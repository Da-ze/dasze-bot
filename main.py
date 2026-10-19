#!/usr/bin/env python3
# -*- coding: utf-8 -*-
from __future__ import annotations

import argparse
import csv
import email.utils
import json
import logging
import os
import re
import sys
import time

from dotenv import load_dotenv
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable
from html.parser import HTMLParser
from urllib.parse import unquote

import requests
import mwparserfromhell


load_dotenv()
Username = os.environ.get("BOT_USERNAME", "HarvFix-ZH")

API = "https://zh.wikipedia.org/w/api.php"
CATEGORY_MISSING = "Category:含有哈佛参考文献格式系列模板链接指向错误的页面"
CATEGORY_MULTIPLE = "Category:含有哈佛参考文献格式系列模板链接指向多个目标错误的页面"

USER_AGENT = (
    "HarvFix-ZH/0.3 "
    "(Wikipedia citation diagnostics; "
    f"contact: https://zh.wikipedia.org/wiki/User:{Username})"
)

EDIT_SUMMARY = "修正哈佛引用模板指向的參考文獻錨點（HarvFix-ZH）"

# 使用 Module:Footnotes 的模板
SFN_TEMPLATES = {
    "harv",
    "harvnb",
    "harvcol",
    "harvcolnb",
    "harvcoltxt",
    "harvtxt",
    "harvp",
    "harvard citation",
    "harvard citation no brackets",
    "harvard citation text",
    "sfn",
    "sfnp",
}

HARVC_TEMPLATES = {"harvc", "citec"}

SFNREF_TEMPLATES = {"sfnref", "harvid"}

YEAR_RE = re.compile(
    r"^(?:\d{3,4}[a-z]?|n\.d\.[a-z]?|nd[a-z]?|c\. \d{3,4}[a-z]?|\d{4}–\d{4}[a-z]?|\d{4}–\d{2}[a-z]?)$"
)
YEAR_ZH_RE = re.compile(r"^(\d{3,4})([a-z]?)年(?:\d{1,2}月(?:\d{1,2}日)?)?([a-z]?)$")

MISSING_RE = re.compile(r"無指向目標\s*[:：]\s*(\S+)")
MULTIPLE_RE = re.compile(r"多個指向目標\s*[（(]\s*(\d+)\s*個\s*[)）]\s*[:：]\s*(\S+)")


@dataclass
class Issue:
    page: str
    pageid: int
    revision_id: int
    scan_categories: str
    template: str
    line: int | None
    raw_template: str
    target: str | None
    issue_type: str
    diagnosis: str
    proposed_change: str
    confidence: str
    status: str = "review_required"


@dataclass
class Fix:
    """對單一模板的修改建議"""

    raw_template: str
    new_template: str
    line: int
    reason: str
    confidence: str  # auto | review


### 年份及錨點
def anchor_year(year: str) -> str | None:
    """Module:Footnotes/year anchor_year() 的 Python 版：2018年3月 -> 2018，2018年a -> 2018a"""
    if not year:
        return None
    if YEAR_RE.match(year):
        return year
    m = YEAR_ZH_RE.match(year)
    if m:
        digits, dab1, dab2 = m.groups()
        if dab1 and dab2:
            return None
        return digits + dab1 + dab2
    return None


def is_year(year: str) -> bool:
    return anchor_year(year) is not None


def anchor_encode(text: str) -> str:
    """mw.uri.anchorEncode()（html5 模式）：去除首尾空白，空白改為底線"""
    return re.sub(r"\s+", "_", text.strip())


def normalize_name(name: str) -> str:
    """正規化模板名稱"""
    name = re.sub(r"[_\s]+", " ", name.strip())
    name = name.lower()

    for prefix in ("template:", "模板:", "样板:", "樣板:", "t:"):
        if name.startswith(prefix):
            name = name[len(prefix) :]
            break

    return name.strip()


def get_template_params(
    template: Any,
) -> tuple[list[str], dict[str, str]]:
    """取得位置參數和命名參數（數字命名參數 |1= 視為位置參數）"""
    positional: dict[int, str] = {}
    named: dict[str, str] = {}
    next_index = 1

    for param in template.params:
        key = str(param.name).strip()
        value = str(param.value).strip()

        if not param.showkey:
            positional[next_index] = value
            next_index += 1
        elif key.isdigit():
            positional[int(key)] = value
        else:
            named[key.lower()] = value

    ordered = [positional.get(i, "") for i in range(1, max(positional, default=0) + 1)]
    return ordered, named


def sfnref_anchor(text: str, normalize: bool = True) -> str | None:
    """{{sfnref|...}} / {{harvid|...}} 的錨點"""
    try:
        code = mwparserfromhell.parse(text)
    except Exception:
        return None
    for template in code.filter_templates(recursive=False):
        if normalize_name(str(template.name)) in SFNREF_TEMPLATES:
            positional, _ = get_template_params(template)
            parts = positional[:5]
            if len(parts) == 5:
                for value in positional[5:]:
                    if is_year(value):
                        parts[4] = value
                        break
            if normalize and len(parts) > 1 and is_year(parts[-1]):
                parts[-1] = anchor_year(parts[-1]) or parts[-1]
            return anchor_encode("CITEREF" + "".join(parts))
    return None


@dataclass
class SfnAnchor:
    anchor: str
    year_index: int | None  # 位置參數索引（0 起算），年份所在位置
    names: list[str] = field(default_factory=list)


def sfn_anchor(
    positional: list[str], named: dict[str, str], normalize: bool = True
) -> SfnAnchor | None:
    """
    Module:Footnotes core() 的錨點推算

    normalize=True 為修正後模組（年份用錨點格式），False 為原模組（年份照寫）
    """
    ref = named.get("ref", named.get("Ref", ""))
    if ref == "none":
        return None
    if ref:
        if "{{" in ref:
            anchor = sfnref_anchor(ref, normalize)
            return SfnAnchor(anchor, None) if anchor else None
        return SfnAnchor(anchor_encode(ref), None)

    p = (positional + [""] * 5)[:5]
    year_source = {i: i for i in range(5)}  # P 位置 -> 原始位置參數索引

    if p[4] and not is_year(p[4]):
        for index, value in enumerate(positional[5:], start=5):
            if is_year(value):
                p[4] = value
                year_source[4] = index
                break

    year_index = None
    if p[4]:
        if is_year(p[4]):
            year_index = 4
        else:
            p[4] = ""
    elif p[3]:
        year_index = 3 if is_year(p[3]) else None
    elif p[2]:
        year_index = 2 if is_year(p[2]) else None
    elif p[1]:
        year_index = 1 if is_year(p[1]) else None

    parts = list(p)
    if normalize and year_index is not None:
        parts[year_index] = anchor_year(parts[year_index]) or parts[year_index]

    names = [x for i, x in enumerate(p) if x and i != year_index]
    return SfnAnchor(
        anchor_encode("CITEREF" + "".join(parts)),
        year_source[year_index] if year_index is not None else None,
        names,
    )


def harvc_link_anchor(named: dict[str, str], normalize: bool = True) -> str | None:
    """{{harvc}} 中 In ... 連結的錨點"""
    ref = named.get("ref", "")
    if ref:
        return anchor_encode(ref)
    year = named.get("year", "")
    if normalize:
        year = anchor_year(year) or year
    names = [named.get("in", named.get("in1", ""))] + [
        named.get(f"in{i}", "") for i in (2, 3, 4)
    ]
    return anchor_encode("CITEREF" + "".join(names) + year)


def template_line(source: str, start: int) -> int:
    """由原始碼字元位置計算行號"""
    return source.count("\n", 0, start) + 1


# ---------------------------------------------------------------- HTML


class RenderedHTMLParser(HTMLParser):
    """收集解析後 HTML 的 id、頁面內連結，以及模組輸出的 harv-error 訊息"""

    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.id_counts: dict[str, int] = {}
        self.fragment_links: list[tuple[str, str]] = []
        self.module_errors: list[str] = []
        self._error_depth = 0
        self._error_text: list[str] = []

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        attr = dict(attrs)
        value = attr.get("id")
        if value:
            self.id_counts[value] = self.id_counts.get(value, 0) + 1

        if tag.lower() == "span":
            if self._error_depth:
                self._error_depth += 1
            elif "harv-error" in (attr.get("class") or "").split():
                self._error_depth = 1
                self._error_text = []

        if tag.lower() != "a":
            return

        href = attr.get("href")
        if not href:
            return

        if href.startswith("#") and len(href) > 1:
            fragment = unquote(href[1:])
            label = attr.get("title") or ""
            self.fragment_links.append((fragment, label))

    def handle_endtag(self, tag: str) -> None:
        if tag.lower() == "span" and self._error_depth:
            self._error_depth -= 1
            if not self._error_depth:
                self.module_errors.append("".join(self._error_text))

    def handle_data(self, data: str) -> None:
        if self._error_depth:
            self._error_text.append(data)


def parse_module_errors(texts: Iterable[str]) -> tuple[dict[str, int], dict[str, int]]:
    """由 harv-error 文字取得模組判定的「無指向目標」及「多個指向目標」錨點"""
    missing: dict[str, int] = {}
    multiple: dict[str, int] = {}
    for text in texts:
        m = MISSING_RE.search(text)
        if m:
            missing[m.group(1)] = missing.get(m.group(1), 0) + 1
            continue
        m = MULTIPLE_RE.search(text)
        if m:
            multiple[m.group(2)] = int(m.group(1))
    return missing, multiple


# ---------------------------------------------------------------- API


class Wiki:
    def __init__(
        self,
        api: str = API,
        delay: float = 1.0,
        max_attempts: int = 6,
    ):
        self.api = api
        self.delay = max(0.0, delay)
        self.max_attempts = max(1, max_attempts)
        self.logged_in_as: str | None = None

        self.session = requests.Session()
        self.session.headers.update(
            {
                "User-Agent": USER_AGENT,
            }
        )

    @staticmethod
    def retry_after_seconds(response: requests.Response) -> float | None:
        """解析 Retry-After 秒數或 HTTP 日期"""
        value = response.headers.get("Retry-After")

        if not value:
            return None

        try:
            return max(0.0, float(value))
        except ValueError:
            pass

        try:
            retry_date = email.utils.parsedate_to_datetime(value)

            if retry_date.tzinfo is None:
                retry_date = retry_date.replace(tzinfo=timezone.utc)

            return max(
                0.0,
                (retry_date - datetime.now(timezone.utc)).total_seconds(),
            )
        except (TypeError, ValueError, OverflowError):
            return None

    def request(self, params: dict[str, Any], post: bool = False) -> dict[str, Any]:
        """發出有退避重試機制的 API 請求"""
        request_params = {
            "format": "json",
            "formatversion": 2,
            "maxlag": 5,
            **params,
        }

        retryable_statuses = {429, 500, 502, 503, 504}

        for attempt in range(self.max_attempts):
            try:
                if post:
                    response = self.session.post(
                        self.api, data=request_params, timeout=45
                    )
                else:
                    response = self.session.get(
                        self.api, params=request_params, timeout=45
                    )

                if response.status_code in retryable_statuses:
                    if attempt == self.max_attempts - 1:
                        response.raise_for_status()

                    wait = self.retry_after_seconds(response)

                    if wait is None:
                        wait = min(5 * (2**attempt), 120)

                    logging.warning(
                        "HTTP %s；等待 %.1f 秒後重試（%d/%d）",
                        response.status_code,
                        wait,
                        attempt + 1,
                        self.max_attempts,
                    )

                    time.sleep(wait)
                    continue

                response.raise_for_status()
                data = response.json()

                if "error" in data:
                    error = data["error"]
                    code = error.get("code", "")

                    if (
                        code in {"ratelimited", "maxlag"}
                        and attempt < self.max_attempts - 1
                    ):
                        wait = self.retry_after_seconds(response) or min(
                            5 * (2**attempt), 120
                        )

                        logging.warning("API 錯誤 %s；等待 %.1f 秒", code, wait)

                        time.sleep(wait)
                        continue

                    raise RuntimeError(f"MediaWiki API error: {error}")

                if self.delay:
                    time.sleep(self.delay)

                return data

            except requests.exceptions.HTTPError:
                raise

            except (
                requests.exceptions.ConnectionError,
                requests.exceptions.Timeout,
                requests.exceptions.ChunkedEncodingError,
                requests.exceptions.JSONDecodeError,
            ) as exc:
                if attempt == self.max_attempts - 1:
                    raise RuntimeError(f"API 請求失敗：{exc}") from exc

                wait = min(5 * (2**attempt), 60)

                logging.warning("暫時性網路錯誤：%s；等待 %.1f 秒", exc, wait)

                time.sleep(wait)

        raise RuntimeError("API 重試次數已用盡")

    def get(self, params: dict[str, Any]) -> dict[str, Any]:
        return self.request(params)

    def category_pages(
        self,
        category: str,
        limit: int,
    ) -> list[dict[str, Any]]:
        """分批讀取分類中的條目頁面"""
        pages: list[dict[str, Any]] = []
        continuation: dict[str, Any] = {}

        while len(pages) < limit:
            data = self.get(
                {
                    "action": "query",
                    "list": "categorymembers",
                    "cmtitle": category,
                    "cmnamespace": 0,
                    "cmtype": "page",
                    "cmlimit": min(500, limit - len(pages)),
                    **continuation,
                }
            )

            members = data.get("query", {}).get("categorymembers", [])

            pages.extend(members)

            continuation = data.get("continue", {})

            if not continuation or not members:
                break

        return pages[:limit]

    def page(self, title: str) -> dict[str, Any] | None:
        """讀取單頁原始碼及修訂版本資訊"""
        data = self.get(
            {
                "action": "query",
                "prop": "revisions|info",
                "rvprop": "ids|timestamp|content",
                "rvslots": "main",
                "titles": title,
                "inprop": "url",
                "curtimestamp": 1,
            }
        )

        pages = data.get("query", {}).get("pages", [])

        if not pages:
            return None

        page = pages[0]

        if page.get("missing"):
            return None

        revisions = page.get("revisions", [])

        if not revisions:
            return None

        revision = revisions[0]
        main_slot = revision.get("slots", {}).get("main", {})

        return {
            "title": page.get("title", title),
            "pageid": page.get("pageid", 0),
            "revision_id": revision.get("revid", 0),
            "timestamp": revision.get("timestamp", ""),
            "curtimestamp": data.get("curtimestamp", ""),
            "text": main_slot.get("content", ""),
            "url": page.get("fullurl", ""),
        }

    def parse_html(self, title: str, revision_id: int | None = None) -> str:
        """取得 MediaWiki 解析後的 HTML（指定版本時解析該版本）"""
        params: dict[str, Any] = {
            "action": "parse",
            "prop": "text",
            "disablelimitreport": 1,
        }
        if revision_id:
            params["oldid"] = revision_id
        else:
            params["page"] = title

        data = self.get(params)

        parsed = data.get("parse", {}).get("text", "")

        if isinstance(parsed, dict):
            return parsed.get("*", "")

        return str(parsed)

    def login(self, username: str, password: str) -> None:
        """以機器人密碼（Special:BotPasswords）登入"""
        token = self.get({"action": "query", "meta": "tokens", "type": "login"})[
            "query"
        ]["tokens"]["logintoken"]
        data = self.request(
            {
                "action": "login",
                "lgname": username,
                "lgpassword": password,
                "lgtoken": token,
            },
            post=True,
        )
        result = data.get("login", {})
        if result.get("result") != "Success":
            raise RuntimeError(f"登入失敗：{result}")
        self.logged_in_as = result.get("lgusername", username)

    def edit(self, page: dict[str, Any], text: str, summary: str) -> dict[str, Any]:
        """以機器人身分提交編輯；版本衝突時由 API 拒絕"""
        token = self.get({"action": "query", "meta": "tokens"})["query"]["tokens"][
            "csrftoken"
        ]
        return self.request(
            {
                "action": "edit",
                "title": page["title"],
                "text": text,
                "summary": summary,
                "baserevid": page["revision_id"],
                "basetimestamp": page["timestamp"],
                "starttimestamp": page["curtimestamp"],
                "nocreate": 1,
                "minor": 1,
                "bot": 1,
                "assert": "bot",
                "token": token,
            },
            post=True,
        )


# ---------------------------------------------------------------- 診斷


def bots_denied(source: str, username: str | None) -> bool:
    """遵守 {{nobots}} 及 {{bots|deny=...}}"""
    code = mwparserfromhell.parse(source)
    for template in code.filter_templates():
        name = normalize_name(str(template.name))
        if name == "nobots":
            return True
        if name == "bots":
            _, named = get_template_params(template)
            deny = [x.strip().lower() for x in named.get("deny", "").split(",")]
            allow = [
                x.strip().lower()
                for x in named.get("allow", "").split(",")
                if x.strip()
            ]
            if "all" in deny or (username and username.lower() in deny):
                return True
            if (
                allow
                and "all" not in allow
                and (not username or username.lower() not in allow)
            ):
                return True
    return False


def find_link_templates(
    source: str,
) -> list[tuple[Any, int, str, SfnAnchor | None, str | None]]:
    """
    列出原始碼中所有會產生 CITEREF 連結的模板

    回傳 (模板, 行號, 模板名稱, 修正後錨點, 原模組錨點)
    """
    found = []
    code = mwparserfromhell.parse(source)
    position = 0
    for template in code.filter_templates(recursive=True):
        name = normalize_name(str(template.name))
        if name not in SFN_TEMPLATES and name not in HARVC_TEMPLATES:
            continue
        raw = str(template)
        start = source.find(raw, position)
        if start < 0:
            start = source.find(raw)
        else:
            position = start + 1
        line = template_line(source, max(start, 0))
        positional, named = get_template_params(template)
        if name in HARVC_TEMPLATES:
            new = harvc_link_anchor(named, True)
            old = harvc_link_anchor(named, False)
            found.append(
                (template, line, name, SfnAnchor(new, None) if new else None, old)
            )
        else:
            new_anchor = sfn_anchor(positional, named, True)
            old_anchor = sfn_anchor(positional, named, False)
            found.append(
                (
                    template,
                    line,
                    name,
                    new_anchor,
                    old_anchor.anchor if old_anchor else None,
                )
            )
    return found


def propose_fix(
    template: Any,
    line: int,
    name: str,
    anchor: SfnAnchor | None,
    ids: dict[str, int],
) -> Fix | None:
    """
    為指向不存在目標的模板尋找唯一的候選目標並產生修改

    自動（auto）修改只限一種：年份缺少消歧義字母，而頁面上只有一個「同作者同年份加字母」的目標
    例如 {{sfn|Smith|2001}} 而參考文獻只有 CITEREFSmith2001a，其餘只產生人工覆核建議
    """
    if anchor is None or anchor.year_index is None or name in HARVC_TEMPLATES:
        return None

    positional, _ = get_template_params(template)
    raw_year = positional[anchor.year_index]
    year = anchor_year(raw_year) or ""
    if not re.fullmatch(r"\d{3,4}", year):
        return None

    candidates = sorted(
        i
        for i in ids
        if i.startswith(anchor.anchor)
        and re.fullmatch(r"[a-z]", i[len(anchor.anchor) :])
    )
    if len(candidates) != 1:
        return None

    letter = candidates[0][-1]
    if raw_year == year:
        new_year = year + letter  # 2001 -> 2001a
        confidence = "auto"
    else:
        new_year = re.sub(
            r"^(\d{3,4})", r"\g<1>" + letter, raw_year, count=1
        )  # 2001年 -> 2001a年
        confidence = "review"  # 需要已部署修正後的 Module:Footnotes

    raw = str(template)
    param_name = str(anchor.year_index + 1)
    clone = mwparserfromhell.parse(raw).filter_templates(recursive=False)[0]
    index = 0
    for param in clone.params:
        if not param.showkey:
            index += 1
            key = str(index)
        else:
            key = str(param.name).strip()
        if key == param_name:
            old_value = str(param.value)
            param.value = old_value.replace(raw_year, new_year, 1)
            break
    else:
        return None

    return Fix(
        raw_template=raw,
        new_template=str(clone),
        line=line,
        reason=f"頁面上只有 {candidates[0]} 一個同作者同年份的目標，年份應加上消歧義字母 {letter}",
        confidence=confidence,
    )


def inspect_page(
    wiki: Wiki,
    page: dict[str, Any],
    scan_categories: str,
) -> tuple[list[Issue], list[Fix]]:
    """檢查頁內 CITEREF 連結，區分模組誤報及條目錯誤；只產生建議，不修改頁面"""
    title = page["title"]

    try:
        html = wiki.parse_html(title, page.get("revision_id"))
    except Exception as exc:
        logging.warning("無法取得頁面 %s 的解析 HTML：%s", title, exc)
        return [], []

    parser = RenderedHTMLParser()

    try:
        parser.feed(html)
        parser.close()
    except Exception as exc:
        logging.warning("無法解析頁面 %s 的 HTML：%s", title, exc)
        return [], []

    return diagnose(page, scan_categories, parser)


def diagnose(
    page: dict[str, Any],
    scan_categories: str,
    parser: RenderedHTMLParser,
) -> tuple[list[Issue], list[Fix]]:
    title = page["title"]
    source = page["text"]
    ids = {k: v for k, v in parser.id_counts.items() if k.startswith("CITEREF")}
    issues: list[Issue] = []
    fixes: list[Fix] = []

    def issue(
        target: str,
        issue_type: str,
        diagnosis: str,
        proposed: str,
        confidence: str,
        template: str = "(rendered HTML)",
        line: int | None = None,
        raw: str = "",
        status: str = "review_required",
    ) -> None:
        issues.append(
            Issue(
                page=title,
                pageid=page["pageid"],
                revision_id=page["revision_id"],
                scan_categories=scan_categories,
                template=template,
                line=line,
                raw_template=raw,
                target=target,
                issue_type=issue_type,
                diagnosis=diagnosis,
                proposed_change=proposed,
                confidence=confidence,
                status=status,
            )
        )

    module_missing, module_multiple = parse_module_errors(parser.module_errors)

    # 1. 模組誤報：模組說找不到，但 HTML 確實有這個 id
    for target in sorted(module_missing):
        if ids.get(target):
            issue(
                target,
                "module_false_missing",
                f"模組回報「無指向目標：{target}」，但解析後 HTML 有 id={target}"
                "目標由模組未辨識的模板產生（例如中文名稱的 cs1 重定向），或年份格式不一致",
                "不需修改條目，修正 Module:Footnotes 系列模組；若目標來自未列出的引用模板重定向，"
                "把該重定向加入 Module:Footnotes/anchor_id_list/data 的 zh_cs12_template_patterns",
                "high",
                status="module_issue",
            )

    # 2. 模組誤報：模組說有多個目標，但 HTML 只有一個（或沒有）
    for target, count in sorted(module_multiple.items()):
        if ids.get(target, 0) <= 1:
            issue(
                target,
                "module_false_multiple",
                f"模組回報 {count} 個「{target}」目標，但解析後 HTML 只有 {ids.get(target, 0)} 個 id"
                "可能是模組把不同日期（例如 2020年a 和 2020年b）算成同一個錨點，"
                "或原始碼中有不會顯示的引用模板（語言轉換 -{}- 區塊等）",
                "不需修改條目；修正模組",
                "high",
                status="module_issue",
            )

    # 3. 條目真正的錯誤：頁內連結指向不存在的 id
    link_templates = find_link_templates(source)
    broken = sorted(
        {
            f
            for f, _ in parser.fragment_links
            if f.startswith("CITEREF") and f not in ids
        }
    )

    for fragment in broken:
        sources = [
            t
            for t in link_templates
            if (t[3] and t[3].anchor == fragment) or t[4] == fragment
        ]

        # 年份寫成 2018年 而目標為 CITEREF…2018：修正後模組會自動連到正確目標
        normalized = [
            t
            for t in sources
            if t[4] == fragment
            and t[3]
            and t[3].anchor != fragment
            and ids.get(t[3].anchor)
        ]
        if normalized:
            for template, line, name, anchor, _old in normalized:
                issue(
                    fragment,
                    "year_form",
                    f"{{{{{name}}}}} 的年份寫法產生 #{fragment}，"
                    f"但參考文獻的錨點是 #{anchor.anchor}",
                    "部署修正後的 Module:Footnotes 即可，不需修改條目",
                    "high",
                    template=name,
                    line=line,
                    raw=str(template),
                    status="module_issue",
                )
            continue

        fixed = False
        for template, line, name, anchor, _old in sources:
            fix = propose_fix(template, line, name, anchor, ids)
            if fix:
                fixes.append(fix)
                issue(
                    fragment,
                    "missing_dab",
                    fix.reason,
                    f"{fix.raw_template} → {fix.new_template}",
                    "high" if fix.confidence == "auto" else "medium",
                    template=name,
                    line=line,
                    raw=fix.raw_template,
                    status=(
                        "auto_fix" if fix.confidence == "auto" else "review_required"
                    ),
                )
                fixed = True
        if fixed:
            continue

        hint = near_targets(fragment, ids)
        issue(
            fragment,
            "missing_target",
            f"頁內連結指向 #{fragment}，但頁面沒有這個 id"
            + (
                f"相近的目標：{', '.join(hint)}" if hint else "頁面上沒有相近的目標"
            ),
            "人工檢查：作者名稱（含繁簡寫法）、年份或 |ref= 是否與參考文獻一致；"
            "參考文獻是否缺少日期，或根本未列出該文獻",
            "medium" if hint else "low",
            template=", ".join(sorted({t[2] for t in sources}))
            or "(rendered HTML link)",
            line=sources[0][1] if sources else None,
            raw=str(sources[0][0]) if sources else "",
        )

    # 4. 條目真正的多個目標：同一 id 出現多次
    for anchor_id, count in sorted(ids.items()):
        if count > 1:
            issue(
                anchor_id,
                "duplicate_target",
                f"HTML 中 id={anchor_id} 出現 {count} 次：同一作者同一年份有多筆參考文獻",
                "人工處理：在各參考文獻的 |date= 或 |year= 加上消歧義字母（2018a、2018b），"
                "並同步修改指向它們的 sfn/harv 模板",
                "medium",
            )

    return issues, fixes


def apply_fixes(
    source: str, fixes: list[Fix], include_review: bool = False
) -> tuple[str, list[Fix]]:
    """把修改套用到原始碼；每個模板文字只替換一次"""
    applied = []
    for fix in fixes:
        if fix.confidence != "auto" and not include_review:
            continue
        if fix.raw_template in source:
            source = source.replace(fix.raw_template, fix.new_template, 1)
            applied.append(fix)
    return source, applied


# ---------------------------------------------------------------- 流程


def collect_pages(
    wiki: Wiki,
    categories: list[str],
    limit: int,
) -> list[tuple[dict[str, Any], list[str]]]:
    """合併分類頁面並去重，保留每頁所屬分類"""
    titles: dict[str, list[str]] = {}

    for category in categories:
        remaining = limit - len(titles)

        if remaining <= 0:
            break

        for item in wiki.category_pages(category, remaining):
            title = item["title"]

            if title not in titles:
                titles[title] = []

            if category not in titles[title]:
                titles[title].append(category)

            if len(titles) >= limit:
                break

    result: list[tuple[dict[str, Any], list[str]]] = []

    for index, (title, page_categories) in enumerate(
        titles.items(),
        start=1,
    ):
        logging.info("[%d/%d] 讀取 %s", index, len(titles), title)

        try:
            page = wiki.page(title)

            if page is not None:
                result.append((page, page_categories))

        except Exception as exc:
            logging.error("讀取頁面 %s 失敗：%s", title, exc)

            if isinstance(exc, RuntimeError) or (
                isinstance(exc, requests.HTTPError)
                and exc.response is not None
                and exc.response.status_code == 429
            ):
                logging.error("停止掃描以避免持續請求 API")
                break

    return result


def write_reports(
    issues: list[Issue],
    pages_scanned: int,
    edits: list[dict[str, Any]],
    applied_live: bool,
    json_path: str,
    csv_path: str,
    diff_path: str,
) -> None:
    """輸出 JSON、CSV 報告及建議修改（diff）"""
    counts: dict[str, int] = {}
    for item in issues:
        counts[item.issue_type] = counts.get(item.issue_type, 0) + 1

    payload = {
        "tool": "HarvFix-ZH",
        "version": "0.3.0",
        "preview_only": not applied_live,
        "edits_submitted": sum(1 for e in edits if e.get("submitted")),
        "pages_scanned": pages_scanned,
        "issues_found": len(issues),
        "issues_by_type": counts,
        "safety_note": (
            "module_false_* 及 year_form 為模組問題，不應修改條目"
            "只有 status=auto_fix 的項目會在 --apply 時提交"
        ),
        "edits": edits,
        "issues": [asdict(issue) for issue in issues],
    }

    for path in (json_path, csv_path, diff_path):
        Path(path).parent.mkdir(parents=True, exist_ok=True)

    Path(json_path).write_text(
        json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8"
    )

    fields = list(Issue.__dataclass_fields__.keys())

    with Path(csv_path).open("w", newline="", encoding="utf-8-sig") as handle:
        writer = csv.DictWriter(handle, fieldnames=fields)
        writer.writeheader()
        for issue in issues:
            writer.writerow(asdict(issue))

    lines = []
    for edit in edits:
        lines.append(f"== {edit['title']} (rev {edit['revision_id']}) ==")
        for change in edit["changes"]:
            lines.append(f"line {change['line']}: {change['reason']}")
            lines.append(f"- {change['old']}")
            lines.append(f"+ {change['new']}")
        lines.append("")
    Path(diff_path).write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="HarvFix-ZH：中文維基百科哈佛引用錯誤診斷及修正工具（預設唯讀）"
    )

    parser.add_argument(
        "--limit", type=int, default=50, help="最多掃描的不重複頁面數，預設 50"
    )
    parser.add_argument(
        "--category",
        choices=["missing", "multiple", "both"],
        default="both",
        help="要掃描的分類",
    )
    parser.add_argument("--title", help="指定單一頁面；不指定時掃描分類")
    parser.add_argument("--api", default=API, help="MediaWiki API endpoint")
    parser.add_argument(
        "--delay", type=float, default=1.0, help="每次成功 API 請求後的等待秒數"
    )
    parser.add_argument(
        "--out", default="reports/harvfix-report.json", help="JSON 報告路徑"
    )
    parser.add_argument(
        "--csv", default="reports/harvfix-report.csv", help="CSV 報告路徑"
    )
    parser.add_argument(
        "--diff", default="reports/harvfix-edits.txt", help="建議修改清單路徑"
    )
    parser.add_argument(
        "--apply",
        action="store_true",
        help="實際提交 status=auto_fix 的修改，需要已核准的機器人帳號及 "
        "HARVFIX_BOT_USER / HARVFIX_BOT_PASSWORD 環境變數（Special:BotPasswords）",
    )
    parser.add_argument(
        "--max-edits", type=int, default=10, help="--apply 時最多編輯頁數，預設 10"
    )
    parser.add_argument(
        "--edit-delay", type=float, default=10.0, help="兩次編輯之間的等待秒數，預設 10"
    )

    args = parser.parse_args()

    if not 1 <= args.limit <= 500:
        parser.error("--limit 必須介於 1 和 500")

    if args.delay < 0:
        parser.error("--delay 不可小於 0")

    logging.basicConfig(level=logging.INFO, format="%(levelname)s: %(message)s")

    wiki = Wiki(api=args.api, delay=args.delay)

    if args.apply:
        user = os.environ.get("HARVFIX_BOT_USER")
        password = os.environ.get("HARVFIX_BOT_PASSWORD")
        if not user or not password:
            parser.error(
                "--apply 需要 HARVFIX_BOT_USER 及 HARVFIX_BOT_PASSWORD 環境變數"
            )
        try:
            wiki.login(user, password)
        except Exception as exc:
            logging.error("%s", exc)
            return 2
        logging.info(
            "以 %s 登入；將提交 auto_fix 修改（最多 %d 頁）",
            wiki.logged_in_as,
            args.max_edits,
        )

    if args.title:
        try:
            page = wiki.page(args.title)

            if page is None:
                logging.error("找不到頁面：%s", args.title)
                return 2

            pages = [(page, ["指定頁面"])]

        except Exception as exc:
            logging.error("讀取指定頁面失敗：%s", exc)
            return 2

    else:
        categories: list[str] = []

        if args.category in {"missing", "both"}:
            categories.append(CATEGORY_MISSING)

        if args.category in {"multiple", "both"}:
            categories.append(CATEGORY_MULTIPLE)

        try:
            pages = collect_pages(wiki, categories, args.limit)
        except Exception as exc:
            logging.error("取得分類頁面失敗：%s", exc)
            return 2

    all_issues: list[Issue] = []
    edits: list[dict[str, Any]] = []
    submitted = 0

    for index, (page, page_categories) in enumerate(pages, start=1):
        logging.info("[%d/%d] 分析 %s", index, len(pages), page["title"])

        try:
            issues, fixes = inspect_page(wiki, page, "; ".join(page_categories))
        except Exception as exc:
            logging.error("分析頁面 %s 失敗：%s", page["title"], exc)
            continue

        all_issues.extend(issues)

        if not fixes:
            continue

        new_text, applied = apply_fixes(page["text"], fixes)
        record = {
            "title": page["title"],
            "revision_id": page["revision_id"],
            "submitted": False,
            "changes": [
                {
                    "line": f.line,
                    "old": f.raw_template,
                    "new": f.new_template,
                    "reason": f.reason,
                    "confidence": f.confidence,
                }
                for f in fixes
            ],
        }
        edits.append(record)

        if not args.apply or not applied or new_text == page["text"]:
            continue

        if submitted >= args.max_edits:
            logging.info("已達 --max-edits；其餘只列入報告")
            continue

        if bots_denied(page["text"], wiki.logged_in_as):
            logging.info("%s 有 {{nobots}}/{{bots}} 排除，略過", page["title"])
            record["skipped"] = "bots_denied"
            continue

        try:
            result = wiki.edit(page, new_text, EDIT_SUMMARY)
            record["submitted"] = result.get("edit", {}).get("result") == "Success"
            record["new_revision_id"] = result.get("edit", {}).get("newrevid")
            submitted += 1
            logging.info("已編輯 %s", page["title"])
            time.sleep(max(0.0, args.edit_delay))
        except Exception as exc:
            logging.error("編輯 %s 失敗：%s；停止編輯", page["title"], exc)
            record["error"] = str(exc)
            break

    write_reports(
        all_issues, len(pages), edits, args.apply, args.out, args.csv, args.diff
    )

    counts: dict[str, int] = {}
    for item in all_issues:
        counts[item.issue_type] = counts.get(item.issue_type, 0) + 1

    print()
    print("HarvFix-ZH 掃描完成")
    print(f"掃描頁面：{len(pages)}")
    print(
        f"診斷：{len(all_issues)}  "
        + "  ".join(f"{k}={v}" for k, v in sorted(counts.items()))
    )
    print(f"建議修改頁面：{len(edits)}")
    print(f"提交編輯：{sum(1 for e in edits if e.get('submitted'))}")
    print("模式：" + ("編輯" if args.apply else "唯讀預覽"))
    print(f"JSON：{args.out}")
    print(f"CSV：{args.csv}")
    print(f"修改清單：{args.diff}")

    return 0


def near_targets(fragment: str, ids: dict[str, int]) -> list[str]:
    """找出與缺失錨點相近的現有錨點（忽略大小寫、空白／底線、年份寫法及消歧義字母）"""

    def key(value: str) -> str:
        value = value.lower().replace("_", "")
        value = re.sub(
            r"(\d{3,4})[a-z]?年(?:\d{1,2}月(?:\d{1,2}日)?)?[a-z]?$", r"\1", value
        )
        return re.sub(r"(\d{3,4})[a-z]$", r"\1", value)

    target = key(fragment)
    prefix = re.sub(r"\d{3,4}.*$", "", target)
    exact = [i for i in ids if key(i) == target]
    if exact:
        return sorted(exact)[:5]
    if len(prefix) > len("citeref"):
        return sorted(i for i in ids if key(i).startswith(prefix))[:5]
    return []


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except KeyboardInterrupt:
        print("\n使用者中止掃描", file=sys.stderr)
        raise SystemExit(130)

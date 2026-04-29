import base64
import json
from urllib.parse import quote, unquote


def format_json_text(raw_text: str) -> str | None:
    text = raw_text.strip()
    if not text:
        return None
    try:
        obj = json.loads(text)
        for _ in range(2):
            if not isinstance(obj, str):
                break
            nested = obj.strip()
            if not nested:
                break
            try:
                obj = json.loads(nested)
            except json.JSONDecodeError:
                break
        return json.dumps(obj, ensure_ascii=False, indent=2)
    except json.JSONDecodeError:
        return None


def base64_encode_text(raw_text: str) -> str | None:
    if not raw_text:
        return None
    return base64.b64encode(raw_text.encode("utf-8")).decode("ascii")


def base64_decode_text(raw_text: str) -> str | None:
    text = raw_text.strip()
    if not text:
        return None
    try:
        decoded_bytes = base64.b64decode(text, validate=True)
        return decoded_bytes.decode("utf-8")
    except Exception:
        return None


def url_encode_text(raw_text: str) -> str | None:
    if raw_text == "":
        return None
    return quote(raw_text, safe="")


def url_decode_text(raw_text: str) -> str | None:
    if raw_text == "":
        return None
    try:
        return unquote(raw_text)
    except Exception:
        return None

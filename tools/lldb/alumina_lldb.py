"""
LLDB data formatters for programs compiled with aluminac.

aluminac describes values in DWARF as they are written in Alumina (`&[u8]`,
`(i32, bool)`, `std::collections::vector::Vector<i32>`); these formatters
show the standard library's types by their contents:

    (&[u8]) name = "hello"
    (&[i32]) xs = len=3 { [0] = 1, [1] = 2, [2] = 3 }
    (std::collections::vector::Vector<i32>) v = len=2 { [0] = 10, [1] = 20 }
    (std::string::StringBuf) s = "abc"
    (std::option::Option<i32>) o = some(7)
    (std::result::Result<i32, Error>) r = err(...)
    (std::collections::hashmap::HashMap<...>) m = len=2 { [0] = (key, value) ... }

Load them with `command script import <path>/alumina_lldb.py` (the
`alumina-lldb` script does), e.g. in `~/.lldbinit`. That also lets `step`
enter the standard library (`std::...`), which lldb skips by default.
"""

import lldb

CATEGORY = "alumina"
# (Past this many elements, a collection shows only its first ones.)
MAX_CHILDREN = 1000


def _unsigned(value, name):
    child = value.GetChildMemberWithName(name)
    return child.GetValueAsUnsigned(0) if child.IsValid() else 0


def _read_bytes(process, address, length, limit=4096):
    if address == 0 or length == 0:
        return b""
    error = lldb.SBError()
    data = process.ReadMemory(address, min(length, limit), error)
    return data if error.Success() else None


def _quote(data, truncated):
    if data is None:
        return "<unreadable>"
    text = data.decode("utf-8", errors="replace")
    escaped = text.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n").replace("\t", "\\t")
    return '"' + escaped + ('"...' if truncated else '"')


def _elements(base_ptr, count, elem_type):
    """Children [0], [1], ... of `count` values of `elem_type` at `base_ptr`."""
    size = elem_type.GetByteSize()
    address = base_ptr.GetValueAsUnsigned(0)
    for i in range(min(count, MAX_CHILDREN)):
        yield base_ptr.CreateValueFromAddress("[%d]" % i, address + i * size, elem_type)


class _ListProvider:
    """A synthetic provider showing a list of values (see `items`)."""

    def __init__(self, valobj, _dict):
        self.valobj = valobj
        self.children = []

    def items(self):
        return []

    def update(self):
        try:
            self.children = list(self.items())
        except Exception:
            self.children = []
        return False

    def num_children(self):
        return len(self.children)

    def get_child_index(self, name):
        try:
            return int(name.lstrip("[").rstrip("]"))
        except ValueError:
            return -1

    def get_child_at_index(self, index):
        return self.children[index] if 0 <= index < len(self.children) else None

    def has_children(self):
        return True


# ---------------------------------------------------------------- slices


def _slice_parts(valobj):
    raw = valobj.GetNonSyntheticValue()
    ptr = raw.GetChildMemberWithName("ptr")
    return ptr, _unsigned(raw, "len")


def _is_bytes(ptr):
    return ptr.GetType().GetPointeeType().GetCanonicalType().GetName() in ("u8", "unsigned char", "uint8_t")


class SliceProvider(_ListProvider):
    def items(self):
        ptr, length = _slice_parts(self.valobj)
        # (`&[u8]` is shown as a string, without its bytes.)
        if _is_bytes(ptr):
            return []
        return _elements(ptr, length, ptr.GetType().GetPointeeType())

    def has_children(self):
        return not _is_bytes(_slice_parts(self.valobj)[0])


def slice_summary(valobj, _dict):
    ptr, length = _slice_parts(valobj)
    if _is_bytes(ptr):
        data = _read_bytes(valobj.GetProcess(), ptr.GetValueAsUnsigned(0), length)
        return _quote(data, data is not None and len(data) < length)
    return "len=%d" % length


# ------------------------------------------------------------ collections


def _vector_parts(valobj):
    raw = valobj.GetNonSyntheticValue()
    data = raw.GetChildMemberWithName("_data").GetNonSyntheticValue()
    return data.GetChildMemberWithName("ptr"), _unsigned(raw, "_length")


class VectorProvider(_ListProvider):
    def items(self):
        ptr, length = _vector_parts(self.valobj)
        return _elements(ptr, length, ptr.GetType().GetPointeeType())


def vector_summary(valobj, _dict):
    return "len=%d" % _vector_parts(valobj)[1]


def stringbuf_summary(valobj, _dict):
    inner = valobj.GetNonSyntheticValue().GetChildMemberWithName("_inner")
    ptr, length = _vector_parts(inner)
    data = _read_bytes(valobj.GetProcess(), ptr.GetValueAsUnsigned(0), length)
    return _quote(data, data is not None and len(data) < length)


class NoChildren(_ListProvider):
    def has_children(self):
        return False


def tuple_summary(valobj, _dict):
    raw = valobj.GetNonSyntheticValue()
    return "(" + ", ".join(_describe(raw.GetChildAtIndex(i)) for i in range(raw.GetNumChildren())) + ")"


def _deque_parts(valobj):
    raw = valobj.GetNonSyntheticValue()
    ptr, capacity = _slice_parts(raw.GetChildMemberWithName("_data"))
    head, tail = _unsigned(raw, "_head"), _unsigned(raw, "_tail")
    length = (tail - head) & (capacity - 1) if capacity else 0
    return ptr, capacity, head, length


class DequeProvider(_ListProvider):
    def items(self):
        ptr, capacity, head, length = _deque_parts(self.valobj)
        elem_type = ptr.GetType().GetPointeeType()
        size = elem_type.GetByteSize()
        base = ptr.GetValueAsUnsigned(0)
        for i in range(min(length, MAX_CHILDREN)):
            index = (head + i) & (capacity - 1)
            yield ptr.CreateValueFromAddress("[%d]" % i, base + index * size, elem_type)


def deque_summary(valobj, _dict):
    return "len=%d" % _deque_parts(valobj)[3]


def _hashmap_items(raw):
    """The occupied buckets' items ((key, value) tuples) of a HashMap."""
    ptr, capacity = _slice_parts(raw.GetChildMemberWithName("_buckets"))
    bucket_type = ptr.GetType().GetPointeeType()
    size = bucket_type.GetByteSize()
    base = ptr.GetValueAsUnsigned(0)
    found = 0
    for i in range(capacity):
        bucket = ptr.CreateValueFromAddress("bucket", base + i * size, bucket_type)
        # (State::Occupied is 1.)
        if bucket.GetChildMemberWithName("state").GetValueAsUnsigned(0) == 1:
            item = bucket.GetChildMemberWithName("item")
            yield item
            found += 1
            if found >= MAX_CHILDREN:
                return


class HashMapProvider(_ListProvider):
    def items(self):
        raw = self.valobj.GetNonSyntheticValue()
        for i, item in enumerate(_hashmap_items(raw)):
            yield item.CreateValueFromData("[%d]" % i, item.GetData(), item.GetType())


def hashmap_summary(valobj, _dict):
    return "len=%d" % _unsigned(valobj.GetNonSyntheticValue(), "_length")


class HashSetProvider(_ListProvider):
    def items(self):
        inner = self.valobj.GetNonSyntheticValue().GetChildMemberWithName("_inner").GetNonSyntheticValue()
        for i, item in enumerate(_hashmap_items(inner)):
            # (The key: the first element of the (key, ()) tuple.)
            key = item.GetChildAtIndex(0)
            yield key.CreateValueFromData("[%d]" % i, key.GetData(), key.GetType())


def hashset_summary(valobj, _dict):
    inner = valobj.GetNonSyntheticValue().GetChildMemberWithName("_inner")
    return "len=%d" % _unsigned(inner.GetNonSyntheticValue(), "_length")


# ------------------------------------------------------- Option and Result


def _describe(value):
    """A value's summary, else its value, else `{...}`."""
    summary = value.GetSummary()
    if summary:
        return summary
    text = value.GetValue()
    if text is not None:
        return text
    return "{...}"


def option_summary(valobj, _dict):
    raw = valobj.GetNonSyntheticValue()
    if raw.GetChildMemberWithName("_is_some").GetValueAsUnsigned(0) == 0:
        return "none"
    inner = raw.GetChildMemberWithName("_inner")
    return "some(%s)" % _describe(inner) if inner.IsValid() else "some"


class OptionProvider(_ListProvider):
    def items(self):
        raw = self.valobj.GetNonSyntheticValue()
        if raw.GetChildMemberWithName("_is_some").GetValueAsUnsigned(0) != 0:
            inner = raw.GetChildMemberWithName("_inner")
            if inner.IsValid():
                yield inner.CreateValueFromData("value", inner.GetData(), inner.GetType())

    def get_child_index(self, name):
        return 0 if name == "value" else -1

    def has_children(self):
        self.update()
        return bool(self.children)


def _result_parts(valobj):
    raw = valobj.GetNonSyntheticValue()
    is_ok = raw.GetChildMemberWithName("_is_ok").GetValueAsUnsigned(0) != 0
    inner = raw.GetChildMemberWithName("_inner")
    return is_ok, inner.GetChildMemberWithName("ok" if is_ok else "err")


def result_summary(valobj, _dict):
    is_ok, value = _result_parts(valobj)
    name = "ok" if is_ok else "err"
    return "%s(%s)" % (name, _describe(value)) if value.IsValid() else name


class ResultProvider(_ListProvider):
    def items(self):
        _is_ok, value = _result_parts(self.valobj)
        if value.IsValid():
            yield value.CreateValueFromData("value", value.GetData(), value.GetType())

    def get_child_index(self, name):
        return 0 if name == "value" else -1

    def has_children(self):
        self.update()
        return bool(self.children)


# ---------------------------------------------------------------- setup

_FORMATTERS = [
    # (type name regex, summary function, synthetic provider class)
    (r"^&(mut )?\[.+\]$", "slice_summary", "SliceProvider"),
    (r"^std::collections::vector::Vector<.+>$", "vector_summary", "VectorProvider"),
    (r"^std::string::StringBuf$", "stringbuf_summary", "NoChildren"),
    (r"^std::collections::deque::Deque<.+>$", "deque_summary", "DequeProvider"),
    (r"^std::collections::hashmap::HashMap<.+>$", "hashmap_summary", "HashMapProvider"),
    (r"^std::collections::hashset::HashSet<.+>$", "hashset_summary", "HashSetProvider"),
    (r"^std::option::Option<.+>$", "option_summary", "OptionProvider"),
    (r"^std::result::Result<.+>$", "result_summary", "ResultProvider"),
]


def __lldb_init_module(debugger, _dict):
    module = __name__
    run = debugger.HandleCommand
    run("type category define %s" % CATEGORY)
    # (8-bit integers are numbers, not characters; arrays of them are
    # arrays, not C strings.)
    run("type format add -w %s -f decimal u8 i8" % CATEGORY)
    run('type summary add -w %s -x "^[iu]8 ?\\[[0-9]+\\]$" -e -s "len=${var%%#}"' % CATEGORY)
    for regex, summary, provider in _FORMATTERS:
        run('type summary add -w %s -x "%s" -e -F %s.%s' % (CATEGORY, regex, module, summary))
        if provider:
            run('type synthetic add -w %s -x "%s" -l %s.%s' % (CATEGORY, regex, module, provider))
    # (Tuples on one line, `(1, "one")`; their elements are still there.)
    run('type summary add -w %s -x "^\\(.+\\)$" -F %s.tuple_summary' % (CATEGORY, module))
    run("type category enable %s" % CATEGORY)
    # (lldb does not step into functions matching `^std::` by default, to
    # skip C++'s standard library: Alumina's is `std::` too, and is stepped
    # into like other code.)
    run("settings set target.process.thread.step-avoid-regexp ''")

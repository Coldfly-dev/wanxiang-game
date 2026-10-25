# -*- coding: utf-8 -*-
"""Minimal AMF0 / AMF3 codec sufficient for Flash Remoting (NetConnection) traffic.

Only what the game client needs: decode AMF0 envelope + AMF0/AMF3 payloads,
encode AMF0 responses (Flash auto-detects markers when decoding).
"""
import struct
import datetime
import calendar

EPOCH = datetime.datetime(1970, 1, 1)


# --------------------------------------------------------------------------- #
# helpers
# --------------------------------------------------------------------------- #
def _ms_to_dt(ms):
    try:
        return EPOCH + datetime.timedelta(milliseconds=float(ms))
    except Exception:
        return datetime.datetime.now()


def _dt_to_ms(dt):
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=datetime.timezone.utc)
    return calendar.timegm(dt.utctimetuple()) * 1000.0 + dt.microsecond / 1000.0


class Reader:
    __slots__ = ("d", "p", "str_refs", "obj_refs", "trait_refs")

    def __init__(self, data):
        self.d = data
        self.p = 0
        # AMF3 reference tables (live for the duration of one message body)
        self.str_refs = []
        self.obj_refs = []
        self.trait_refs = []

    def left(self):
        return len(self.d) - self.p

    def u8(self):
        v = self.d[self.p]
        self.p += 1
        return v

    def peek(self):
        return self.d[self.p]

    def u16(self):
        v = struct.unpack_from(">H", self.d, self.p)[0]
        self.p += 2
        return v

    def i16(self):
        v = struct.unpack_from(">h", self.d, self.p)[0]
        self.p += 2
        return v

    def u32(self):
        v = struct.unpack_from(">I", self.d, self.p)[0]
        self.p += 4
        return v

    def i32(self):
        v = struct.unpack_from(">i", self.d, self.p)[0]
        self.p += 4
        return v

    def f64(self):
        v = struct.unpack_from(">d", self.d, self.p)[0]
        self.p += 8
        return v

    def take(self, n):
        v = self.d[self.p:self.p + n]
        self.p += n
        return v

    def utf8(self, n):
        return self.take(n).decode("utf-8", "replace")

    def str16(self):
        return self.utf8(self.u16())

    def str32(self):
        return self.utf8(self.u32())


# --------------------------------------------------------------------------- #
# AMF0 decoding
# --------------------------------------------------------------------------- #
def read_amf0(r):
    m = r.u8()
    if m == 0x00:                       # number
        return r.f64()
    if m == 0x01:                       # boolean
        return r.u8() != 0
    if m == 0x02:                       # string
        return r.str16()
    if m == 0x03:                       # object
        return _read_amf0_object(r)
    if m == 0x05:
        return None
    if m == 0x06:                       # undefined
        return None
    if m == 0x07:                       # reference (rare in requests)
        return None
    if m == 0x08:                       # ECMA array
        r.u32()                         # approx count
        return _read_amf0_object(r)
    if m == 0x09:                       # object end
        return None
    if m == 0x0A:                       # strict array
        n = r.u32()
        return [read_amf0(r) for _ in range(n)]
    if m == 0x0B:                       # date
        ms = r.f64()
        r.i16()
        return _ms_to_dt(ms)
    if m == 0x0C:                       # long string
        return r.str32()
    if m == 0x0D:                       # unsupported
        return None
    if m == 0x0F:                       # xml doc
        return r.str32()
    if m == 0x10:                       # typed object
        name = r.str16()
        obj = _read_amf0_object(r)
        try:
            obj["__type__"] = name
        except Exception:
            pass
        return obj
    if m == 0x11:                       # avmplus -> switch to AMF3
        return read_amf3(r)
    raise ValueError("unknown AMF0 marker 0x%02x at %d" % (m, r.p - 1))


def _read_amf0_object(r):
    obj = {}
    while True:
        k = r.str16()
        if r.p >= len(r.d):
            break
        if r.d[r.p] == 0x09:
            r.u8()
            break
        obj[k] = read_amf0(r)
    return obj


# --------------------------------------------------------------------------- #
# AMF3 decoding
# --------------------------------------------------------------------------- #
def read_u29(r):
    b = r.u8()
    if b < 0x80:
        return b
    v = (b & 0x7F) << 7
    b = r.u8()
    if b < 0x80:
        return v | b
    v = (v | (b & 0x7F)) << 7
    b = r.u8()
    if b < 0x80:
        return v | b
    v = (v | (b & 0x7F)) << 8
    return v | r.u8()


def read_amf3(r):
    m = r.u8()
    if m == 0x00 or m == 0x01:
        return None
    if m == 0x02:
        return False
    if m == 0x03:
        return True
    if m == 0x04:
        # AMF3 integers are 29-bit two's-complement: values with bit 28 set
        # are negative, so subtract 2**29 (0x20000000), not 2**28.
        v = read_u29(r)
        if v > 0x0FFFFFFF:
            v -= 0x20000000
        return v
    if m == 0x05:
        return r.f64()
    if m == 0x06:
        return _amf3_str(r)
    if m == 0x07:
        return _amf3_str(r)            # xml doc
    if m == 0x08:
        ref = read_u29(r)
        if ref & 1 == 0:
            return r.obj_refs[ref >> 1]
        d = _ms_to_dt(r.f64())
        r.obj_refs.append(d)
        return d
    if m == 0x09:
        return _amf3_array(r)
    if m == 0x0A:
        return _amf3_object(r)
    if m == 0x0B:
        return _amf3_str(r)            # xml
    if m == 0x0C:
        n = read_u29(r) >> 1
        return r.take(n)
    raise ValueError("unknown AMF3 marker 0x%02x at %d" % (m, r.p - 1))


def _amf3_str(r, register=True):
    """Read an AMF3 string.

    The AIR runtime does NOT add the empty string to the reference table (it is
    the special "no more dynamic members" sentinel).  Registering it shifts
    every later reference index, which silently corrupts nested objects.
    Verified by brute force in decode_probe2.py.
    """
    ref = read_u29(r)
    if ref & 1 == 0:
        return r.str_refs[ref >> 1]
    s = r.utf8(ref >> 1)
    if register and s != "":
        r.str_refs.append(s)
    return s


def _amf3_array(r):
    ref = read_u29(r)
    if ref & 1 == 0:
        return r.obj_refs[ref >> 1]
    count = ref >> 1
    # Flash writes 0x01 (the empty-string sentinel) for an empty associative
    # section rather than the 0x00 the spec describes; accept both.
    assoc = read_u29(r)
    if assoc <= 1:
        assoc = 0
    if assoc:
        out = {}
        r.obj_refs.append(out)
        for _ in range(assoc):
            key = _amf3_str(r)
            out[key] = read_amf3(r)
        dense = [read_amf3(r) for _ in range(count)]
        if dense:
            out["__dense__"] = dense
        return out
    out = []
    r.obj_refs.append(out)
    for _ in range(count):
        out.append(read_amf3(r))
    return out


def _amf3_object(r):
    """Decode an AMF3 object the way the AIR runtime actually writes them.

    Empirically (validated against a captured NetConnection.call, see
    decode_probe.py) the trait u29 splits as:
        bit0      : 1 = inline, 0 = object reference
        bit2      : externalizable
        bits3+    : sealed member count
    the class name is present only when there are sealed members, and member
    name/value pairs are interleaved.  Everything this client sends is a plain
    dynamic Object, so "no sealed members" is treated as dynamic.
    """
    ref = read_u29(r)
    if ref & 1 == 0:
        return r.obj_refs[ref >> 1]
    ext = bool(ref & 4)
    sealed_count = ref >> 3
    dyn = bool(ref & 2) or sealed_count == 0
    cls = _amf3_str(r) if sealed_count > 0 else ""

    if ext:
        holder = {"__externalizable__": cls}
        r.obj_refs.append(holder)
        return holder

    obj = {}
    if cls:
        obj["__type__"] = cls
    r.obj_refs.append(obj)
    for _ in range(sealed_count):
        name = _amf3_str(r)          # NB: read the name before the value
        obj[name] = read_amf3(r)
    if dyn:
        while True:
            name = _amf3_str(r)
            if name == "":
                break
            obj[name] = read_amf3(r)
    return obj


# --------------------------------------------------------------------------- #
# AMF0 encoding (responses)
# --------------------------------------------------------------------------- #
def enc_str(s):
    b = s.encode("utf-8")
    if len(b) < 65536:
        return b"\x02" + struct.pack(">H", len(b)) + b
    return b"\x0c" + struct.pack(">I", len(b)) + b


def encode_amf0(v):
    if v is None:
        return b"\x05"
    if v is True:
        return b"\x01\x01"
    if v is False:
        return b"\x01\x00"
    if isinstance(v, (int, float)):
        return b"\x00" + struct.pack(">d", float(v))
    if isinstance(v, str):
        return enc_str(v)
    if isinstance(v, (bytes, bytearray)):
        return enc_str(v.decode("latin-1"))
    if isinstance(v, datetime.datetime):
        return b"\x0b" + struct.pack(">d", _dt_to_ms(v)) + struct.pack(">h", 0)
    if isinstance(v, dict):
        out = bytearray(b"\x03")
        for k, val in v.items():
            if k == "__type__":
                continue
            out += enc_str(str(k))
            out += encode_amf0(val)
        out += b"\x00\x00\x09"
        return bytes(out)
    if isinstance(v, (list, tuple)):
        out = bytearray(b"\x0a" + struct.pack(">I", len(v)))
        for item in v:
            out += encode_amf0(item)
        return bytes(out)
    return enc_str(str(v))


# --------------------------------------------------------------------------- #
# AMF3 encoding (responses)
# --------------------------------------------------------------------------- #
def enc_u29(n):
    n &= 0x1FFFFFFF
    if n < 0x80:
        return bytes([n])
    if n < 0x4000:
        return bytes([0x80 | (n >> 7), n & 0x7F])
    if n < 0x200000:
        return bytes([0x80 | (n >> 14), 0x80 | ((n >> 7) & 0x7F), n & 0x7F])
    return bytes([0x80 | (n >> 22), 0x80 | ((n >> 15) & 0x7F),
                  0x80 | ((n >> 8) & 0x7F), n & 0xFF])


def _enc3_str(s):
    b = s.encode("utf-8")
    return b"\x06" + enc_u29((len(b) << 1) | 1) + b


def encode_amf3(v, state=None):
    """Encode a value the way the AIR runtime itself does.

    Verified against captured traffic: in one AMF3 context the first object is
    written as `0a 0b 01 <name> <value> ... 01` (trait + empty class name) and
    every later object as `0a 01 <name> <value> ... 01`.  Emitting only the
    short form makes Flash fail with Client.Data.UnderFlow.
    """
    if state is None:
        state = {"objs": 0}
    if v is None:
        return b"\x01"
    if v is True:
        return b"\x03"
    if v is False:
        return b"\x02"
    if isinstance(v, int):
        if 0 <= v <= 0x0FFFFFFF:
            return b"\x04" + enc_u29(v)
        return b"\x05" + struct.pack(">d", float(v))
    if isinstance(v, float):
        return b"\x05" + struct.pack(">d", v)
    if isinstance(v, str):
        return _enc3_str(v)
    if isinstance(v, datetime.datetime):
        return b"\x08" + enc_u29(1) + struct.pack(">d", _dt_to_ms(v))
    if isinstance(v, dict):
        out = bytearray(b"\x0a")
        if state["objs"] == 0:
            state["objs"] += 1
            out += enc_u29(0x0B)      # inline | dynamic | 1 sealed slot
            out += enc_u29(1)         # class name ""
        else:
            state["objs"] += 1
            out += enc_u29(0x01)      # inline dynamic, no class name
        for k, val in v.items():
            if k == "__type__":
                continue
            kb = str(k).encode("utf-8")
            out += enc_u29((len(kb) << 1) | 1) + kb
            out += encode_amf3(val, state)
        out += b"\x01"                # member terminator
        return bytes(out)
    if isinstance(v, (list, tuple)):
        out = bytearray(b"\x09")
        out += enc_u29((len(v) << 1) | 1)
        out += enc_u29(1)             # associative count 0
        for item in v:
            out += encode_amf3(item, state)
        return bytes(out)
    return _enc3_str(str(v))

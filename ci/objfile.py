"""Reading the code of compiled Rust crates: `ar` archives (an `.rlib`'s
object files) and little-endian ELF object files (their sections, symbols
and relocations), as `ci/preassemble.py` needs, without any tool but Python.

Only what those need is read: ELF32 and ELF64, little-endian (every target
whose generated code is pre-assembled is), and the GNU and BSD `ar` formats.
"""

import struct

ELF_MAGIC = b"\x7fELF"

# Section types.
SHT_SYMTAB = 2
SHT_RELA = 4
SHT_REL = 9


def ar_members(data):
    """The members of the `ar` archive `data`: `{name: bytes}`."""
    if not data.startswith(b"!<arch>\n"):
        raise ValueError("not an ar archive")
    members, pos, names = {}, 8, b""
    while pos + 60 <= len(data):
        header = data[pos:pos + 60]
        name = header[:16].decode().rstrip()
        size = int(header[48:58].decode().strip())
        body = data[pos + 60:pos + 60 + size]
        pos += 60 + size + (size & 1)
        if name == "//":  # GNU: the table of long names.
            names = body
            continue
        if name in ("/", "/SYM64/", "__.SYMDEF", "__.SYMDEF SORTED"):
            continue
        if name.startswith("#1/"):  # BSD: the name precedes the body.
            n = int(name[3:])
            name, body = body[:n].rstrip(b"\0").decode(), body[n:]
        elif name.startswith("/") and name[1:].isdigit():  # GNU long name.
            off = int(name[1:])
            name = names[off:names.index(b"\n", off)].decode().rstrip("/")
        else:
            name = name.rstrip("/")
        members[name] = body
    return members


class Section:
    def __init__(self, index, name, type_, flags, offset, size, link, info, align, entsize, data):
        self.index, self.name, self.type, self.flags = index, name, type_, flags
        self.offset, self.size, self.link, self.info = offset, size, link, info
        self.align, self.entsize, self.data = align, entsize, data


class Symbol:
    def __init__(self, name, value, size, info, other, shndx):
        self.name, self.value, self.size = name, value, size
        self.info, self.other, self.shndx = info, other, shndx

    @property
    def type(self):
        return self.info & 0xF

    @property
    def bind(self):
        return self.info >> 4


class Reloc:
    def __init__(self, offset, type_, symbol, addend):
        self.offset, self.type, self.symbol, self.addend = offset, type_, symbol, addend


class Elf:
    """A little-endian ELF object file: its sections, its symbols, and the
    relocations of each section (`relocs[section index]`)."""

    def __init__(self, data):
        if not data.startswith(ELF_MAGIC):
            raise ValueError("not an ELF file")
        if data[5] != 1:
            raise ValueError("not little-endian ELF")
        self.is64 = data[4] == 2
        self.machine = struct.unpack_from("<H", data, 18)[0]
        if self.is64:
            shoff, = struct.unpack_from("<Q", data, 40)
            shentsize, shnum, shstrndx = struct.unpack_from("<HHH", data, 58)
        else:
            shoff, = struct.unpack_from("<I", data, 32)
            shentsize, shnum, shstrndx = struct.unpack_from("<HHH", data, 46)
        raw = []
        for i in range(shnum):
            at = shoff + i * shentsize
            if self.is64:
                name, type_, flags, _addr, offset, size, link, info, align, entsize = \
                    struct.unpack_from("<IIQQQQIIQQ", data, at)
            else:
                name, type_, flags, _addr, offset, size, link, info, align, entsize = \
                    struct.unpack_from("<IIIIIIIIII", data, at)
            raw.append((name, type_, flags, offset, size, link, info, align, entsize))
        strtab = raw[shstrndx]
        names = data[strtab[3]:strtab[3] + strtab[4]]
        self.sections = []
        for i, (name, type_, flags, offset, size, link, info, align, entsize) in enumerate(raw):
            body = data[offset:offset + size] if type_ != 8 else b""  # SHT_NOBITS
            self.sections.append(Section(i, cstr(names, name), type_, flags, offset, size,
                                         link, info, align, entsize, body))
        self.symbols = []
        for s in self.sections:
            if s.type == SHT_SYMTAB:
                strs = self.sections[s.link].data
                fmt, n = ("<IBBHQQ", 24) if self.is64 else ("<IIIBBH", 16)
                for at in range(0, len(s.data), n):
                    if self.is64:
                        name, info, other, shndx, value, size = struct.unpack_from(fmt, s.data, at)
                    else:
                        name, value, size, info, other, shndx = struct.unpack_from(fmt, s.data, at)
                    self.symbols.append(Symbol(cstr(strs, name), value, size, info, other, shndx))
        self.relocs = {}
        for s in self.sections:
            if s.type not in (SHT_RELA, SHT_REL):
                continue
            rela = s.type == SHT_RELA
            out = self.relocs.setdefault(s.info, [])
            if self.is64:
                n = 24 if rela else 16
                for at in range(0, len(s.data), n):
                    offset, info = struct.unpack_from("<QQ", s.data, at)
                    addend = struct.unpack_from("<q", s.data, at + 16)[0] if rela else None
                    out.append(Reloc(offset, info & 0xFFFFFFFF, info >> 32, addend))
            else:
                n = 12 if rela else 8
                for at in range(0, len(s.data), n):
                    offset, info = struct.unpack_from("<II", s.data, at)
                    addend = struct.unpack_from("<i", s.data, at + 8)[0] if rela else None
                    out.append(Reloc(offset, info & 0xFF, info >> 8, addend))


def cstr(table, offset):
    return table[offset:table.index(b"\0", offset)].decode()

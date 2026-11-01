"""Pre-assembling the generated code (ci/preassemble.py), checking it
(ci/check_preassembled.py) and reading object files for both (ci/objfile.py),
on objects and archives built here, without a compiler."""

import collections
import contextlib
import io
import pathlib
import struct
import tempfile
import unittest

import check_preassembled
import objfile
import preassemble


def elf(sections, symbols, relocs=(), is64=True):
    """A relocatable little-endian ELF file. `sections`: `[(name, type,
    flags, align, data)]`, after the null section (so the first is 1);
    `symbols`: `[(name, value, size, info, other, shndx)]`, after the null
    symbol; `relocs`: `[(section, offset, type, symbol, addend)]`, in one
    `.rela` section per section (`.rel` without an addend)."""
    strtab, names = b"\0", {}
    for s in symbols:
        names[s[0]] = len(strtab)
        strtab += s[0].encode() + b"\0"
    if is64:
        sym = b"\0" * 24 + b"".join(struct.pack("<IBBHQQ", names[n], info, other, shndx, value, size)
                                     for n, value, size, info, other, shndx in symbols)
    else:
        sym = b"\0" * 16 + b"".join(struct.pack("<IIIBBH", names[n], value, size, info, other, shndx)
                                     for n, value, size, info, other, shndx in symbols)
    by_section = collections.defaultdict(list)
    for r in relocs:
        by_section[r[0]].append(r[1:])
    all_sections = list(sections)
    links = {}
    for target, rs in sorted(by_section.items()):
        rela = rs[0][3] is not None
        if is64:
            data = b"".join(struct.pack("<QQ", off, (symbol << 32) | type_) +
                            (struct.pack("<q", addend) if rela else b"") for off, type_, symbol, addend in rs)
        else:
            data = b"".join(struct.pack("<II", off, (symbol << 8) | type_) +
                            (struct.pack("<i", addend) if rela else b"") for off, type_, symbol, addend in rs)
        links[len(all_sections) + 1] = target
        all_sections.append(((".rela" if rela else ".rel") + sections[target - 1][0],
                             4 if rela else 9, 0, 8, data))
    symtab_index = len(all_sections) + 1
    all_sections += [(".symtab", 2, 0, 8, sym), (".strtab", 3, 0, 1, strtab)]
    shstr, shnames = b"\0", []
    for s in all_sections + [(".shstrtab",)]:
        shnames.append(len(shstr))
        shstr += s[0].encode() + b"\0"
    all_sections.append((".shstrtab", 3, 0, 1, shstr))
    ehsize, shentsize = (64, 64) if is64 else (52, 40)
    body, offsets = b"", []
    for s in all_sections:
        offsets.append(ehsize + len(body))
        body += s[4]
    shoff = ehsize + len(body)
    headers = b"\0" * shentsize
    for i, (name, type_, flags, align, data) in enumerate(all_sections, start=1):
        link = symtab_index + 1 if type_ == 2 else symtab_index if type_ in (4, 9) else 0
        info = links.get(i, 0)
        entsize = {2: 24 if is64 else 16, 4: 24 if is64 else 12, 9: 16 if is64 else 8}.get(type_, 0)
        fmt = "<IIQQQQIIQQ" if is64 else "<IIIIIIIIII"
        headers += struct.pack(fmt, shnames[i - 1], type_, flags, 0, offsets[i - 1], len(data),
                               link, info, align, entsize)
    ident = b"\x7fELF" + bytes([2 if is64 else 1, 1, 1]) + b"\0" * 9
    if is64:
        header = ident + struct.pack("<HHIQQQIHHHHHH", 1, 62, 1, 0, 0, shoff, 0, ehsize, 0, 0,
                                     shentsize, len(all_sections) + 1, len(all_sections))
    else:
        header = ident + struct.pack("<HHIIIIIHHHHHH", 1, 3, 1, 0, 0, shoff, 0, ehsize, 0, 0,
                                     shentsize, len(all_sections) + 1, len(all_sections))
    return header + body + headers


def ar(members, bsd=False):
    """An `ar` archive of `members` (`{name: bytes}`), with GNU's table of
    long names (or BSD's names before the bodies), and a symbol table."""
    out, longnames = b"!<arch>\n", b""
    entries = [("/" if not bsd else "__.SYMDEF", b"\0\0\0\0")]
    for name, body in members.items():
        if bsd:
            n = name.encode()
            entries.append((f"#1/{len(n)}", n + body))
        elif len(name) > 15:
            entries.append((f"/{len(longnames)}", body))
            longnames += name.encode() + b"/\n"
        else:
            entries.append((name + "/", body))
    if longnames:
        entries.insert(1, ("//", longnames))
    for name, body in entries:
        out += f"{name:<16}{0:<12}{0:<6}{0:<6}{644:<8}{len(body):<10}`\n".encode() + body
        if len(body) & 1:
            out += b"\n"
    return out


class ObjFile(unittest.TestCase):
    def test_ar_gnu_and_bsd(self):
        members = {"a.o": b"abc", "a-much-longer-name.rcgu.o": b"de", "lib.rmeta": b""}
        self.assertEqual(objfile.ar_members(ar(members)), members)
        self.assertEqual(objfile.ar_members(ar(members, bsd=True)), members)
        with self.assertRaises(ValueError):
            objfile.ar_members(b"not an archive")

    def test_elf64(self):
        data = elf([(".text.f", 1, 6, 16, b"\x90\xc3"), (".rodata.t", 1, 2, 8, b"\1\2")],
                   [("f", 0, 2, 0x12, 0, 1), ("t", 0, 2, 0x11, 2, 2), ("g", 0, 0, 0x10, 0, 0)],
                   [(1, 1, 4, 3, -4)])
        o = objfile.Elf(data)
        self.assertTrue(o.is64)
        text = o.sections[1]
        self.assertEqual((text.name, text.type, text.flags, text.align, text.data),
                         (".text.f", 1, 6, 16, b"\x90\xc3"))
        f = o.symbols[1]
        self.assertEqual((f.name, f.value, f.size, f.type, f.bind, f.shndx), ("f", 0, 2, 2, 1, 1))
        self.assertEqual(o.symbols[2].other, 2)
        r, = o.relocs[1]
        self.assertEqual((r.offset, r.type, r.symbol, r.addend), (1, 4, 3, -4))

    def test_elf32_rel(self):
        o = objfile.Elf(elf([(".text", 1, 6, 4, b"\xe8\0\0\0\0")], [("g", 0, 0, 0x10, 0, 0)],
                            [(1, 1, 2, 1, None)], is64=False))
        self.assertFalse(o.is64)
        self.assertEqual(o.symbols[1].name, "g")
        r, = o.relocs[1]
        self.assertEqual((r.offset, r.type, r.symbol, r.addend), (1, 2, 1, None))

    def test_not_elf(self):
        with self.assertRaises(ValueError):
            objfile.Elf(b"\0" * 64)
        with self.assertRaises(ValueError):
            objfile.Elf(b"\x7fELF\x02\x02" + b"\0" * 58)


class Parse(unittest.TestCase):
    BODY = '''        "mov rax, rdi",
        r"1:
add rax, 1
jne 1b",
        "call {f}\\n.p2align 4",
        concat!("adrp x0, ", vg_sym_page!("t")),
        f = sym crate::x::f,
        options(),
'''

    def test_parse_args(self):
        lines, operands = preassemble.parse_args(self.BODY)
        self.assertEqual(lines, [("text", "mov rax, rdi"), ("text", "1:"), ("text", "add rax, 1"),
                                 ("text", "jne 1b"), ("text", "call {f}"), ("text", ".p2align 4"),
                                 ("concat", 'concat!("adrp x0, ", vg_sym_page!("t"))')])
        self.assertEqual(operands, ["f = sym crate::x::f", "options()"])
        with self.assertRaises(ValueError):
            preassemble.parse_args("        what,\n")

    def test_unescape_and_literal(self):
        for s in ["plain", 'a "quoted" \\ line\nand\r more', ""]:
            lit = preassemble.literal(s)
            if lit.startswith('r"'):
                self.assertEqual(lit[2:-1], s)
            else:
                self.assertEqual(preassemble.unescape(lit[1:-1]), s)

    def test_kept_lines(self):
        lines = [("text", t) for t in ["1:", "mov x, y", "2:", "call {f}", "b 1b", "lea r, [{t}]",
                                       "j 3f", ".p2align 4", "3:", "cbz 3f, {g}", "3:"]]
        reloc, labels = preassemble.kept_lines(lines)
        self.assertEqual(reloc, {3, 5, 7, 9})
        # `2:` is named by no kept line, `1b` by a line of bytes; `3f` of
        # line 9 is the next `3:`.
        self.assertEqual(labels, {10})
        with self.assertRaises(ValueError):
            preassemble.kept_lines([("text", "call {f}"), ("text", "b.ne {g}, 4f")])


class Encode(unittest.TestCase):
    def test_octa(self):
        b = bytes(range(37))
        out = preassemble.octa(b)
        self.assertEqual(out[0].split(",")[0], ".octa 0x" + bytes(range(16))[::-1].hex().lstrip("0"))
        self.assertEqual(out[-1], ".byte 32,33,34,35,36")
        self.assertEqual(preassemble.octa(b""), [])

    def test_encode(self):
        self.assertEqual(preassemble.encode("x86_64", b""), [])
        self.assertEqual(preassemble.encode("x86_64", b"\xc3"), [".byte 195"])
        with self.assertRaises(ValueError):
            preassemble.encode("arm", b"\0\0\0\0")


class Rewrite(unittest.TestCase):
    TEXT = '''// @generated
pub unsafe extern "C" fn f() {
    core::arch::naked_asm!(
        "push rbx",
        "call {g}",
        "pop rbx\\nret",
        g = sym crate::g,
    )
}
'''

    def test_marked_source(self):
        functions = []
        marked = preassemble.marked_source(self.TEXT, functions)
        self.assertEqual(len(functions), 1)
        self.assertIn('r"vgpre0_s:",\n        r"push rbx",\n        r"vgpre0_1:",\n'
                      '        r"call {g}",\n        r"vgpre0_1e:",', marked)
        self.assertTrue(marked.startswith("// @generated\npub unsafe"))
        self.assertIn("        g = sym crate::g,\n    )\n}\n", marked)

    def test_preassembled(self):
        # The code of `f` as compiled: `push rbx`, `call` (5 bytes), `pop`, `ret`.
        code = b"\x53\xe8\0\0\0\0\x5b\xc3"
        sec = objfile.Section(1, ".text.f", 1, 6, 0, len(code), 0, 0, 16, 0, code)
        found = {"vgpre0_s": (sec, 0), "vgpre0_1": (sec, 1), "vgpre0_1e": (sec, 6)}
        out = preassemble.preassembled("x86_64", {"m.rs": self.TEXT}, found)
        self.assertEqual(out["m.rs"], self.TEXT.replace(
            '"push rbx",\n        "call {g}",\n        "pop rbx\\nret",',
            'r".byte 83",\n        r"call {g}",\n        r".byte 91,195",'))
        # What is outside the code is as it was.
        self.assertEqual(check_preassembled.NAKED.sub("", out["m.rs"]),
                         check_preassembled.NAKED.sub("", self.TEXT))


class Check(unittest.TestCase):
    def test_check_text(self):
        code = "    core::arch::naked_asm!(\n        \"ret\",\n    )\n"
        other = code.replace("ret", ".byte 195")
        errors = []
        check_preassembled.check_text({"a.rs": "x\n" + code, "b.rs": "y", "lib.rs": "z"},
                                      {"a.rs": "x\n" + other, "b.rs": "y!", "c.rs": ""}, "t", errors)
        self.assertEqual(errors, ["t: src/b.rs differs from asm/b.rs outside its code",
                                  "t: c.rs is in src/ only", "t: lib.rs is in asm/ only"])

    def obj(self, code, extra_sections=(), name="_RNvCs1234abcd_3foo1f"):
        return objfile.Elf(elf(
            [(f".text.{name}", 1, 6, 16, code)] + list(extra_sections),
            [("$x", 0, 0, 0, 0, 1), (name, 0, len(code), 0x12, 0, 1), ("ext", 0, 0, 0x10, 0, 0),
             ("", 0, 0, 3, 0, 1), ("cgu.o", 0, 0, 4, 0, 0xFFF1)],
            [(1, 1, 4, 3, -4), (1, 2, 1, 4, 0)]))

    def test_same(self):
        a = check_preassembled.contents([self.obj(b"\xe8\0\0\0\0\xc3")])
        b = check_preassembled.contents([self.obj(b"\xe8\0\0\0\0\xc3", name="_RNvCsZZ_3foo1f")])
        self.assertEqual(check_preassembled.differences("t", a, b), [])
        sections, symbols = a
        self.assertIn(("_RNv3foo1f", 0, 6, 0x12, 0, ".text._RNv3foo1f"), symbols)
        # Neither the section's symbol nor the file's, nor the undefined `ext`.
        self.assertEqual(len(symbols), 2)
        (text,) = [k for k in sections if k[0].startswith(".text")]
        self.assertEqual(text[6], ((1, 4, -4, "ext"), (2, 1, 0, "section .text._RNv3foo1f")))

    def test_different(self):
        a = check_preassembled.contents([self.obj(b"\xe8\0\0\0\0\xc3")])
        for other, what in [
                (self.obj(b"\xe8\0\0\0\0\xc2"), ["section"]),
                # A section no symbol is in: a constructor.
                (self.obj(b"\xe8\0\0\0\0\xc3", [(".init_array", 14, 3, 8, b"\0" * 8)]), ["section"])]:
            diffs = check_preassembled.differences("t", a, check_preassembled.contents([other]))
            self.assertTrue(diffs)
            self.assertTrue(all(any(f"the {w} " in d for w in what) for d in diffs), diffs)
        # A symbol of another size.
        o = self.obj(b"\xe8\0\0\0\0\xc3")
        o.symbols[2].size = 5
        self.assertEqual(check_preassembled.differences("t", a, check_preassembled.contents([o])),
                         ["t: the symbol _RNv3foo1f differs between asm/ and src/"])

    def test_group(self):
        group = (".group", 17, 0, 4, struct.pack("<II", 1, 1))
        def obj(name):
            o = objfile.Elf(elf([(f".text.{name}", 1, 6, 16, b"\xc3"), group],
                                [(name, 0, 1, 0x12, 0, 1)]))
            o.sections[2].info = 1
            return o
        a = check_preassembled.contents([obj("_RNvCsA_1f")])
        b = check_preassembled.contents([obj("_RNvCsB_1f")])
        self.assertEqual(check_preassembled.differences("t", a, b), [])
        (g,) = [k for k in a[0] if k[0] == ".group"]
        self.assertEqual(g[5], (1, "_RNv1f", (".text._RNv1f",)))

    def test_unassembled(self):
        with tempfile.TemporaryDirectory() as d:
            root = pathlib.Path(d)
            for p in ["verified-garbage-asm-x86_64/src", "verified-garbage-asm-x86_64/asm",
                      "verified-garbage-asm-arm/asm", "verified-garbage-asm-riscv64/src",
                      "verified-garbage-asm-mips/asm", "verified-garbage-asm-mips/src",
                      "verified-garbage-cpu/src"]:
                (root / p).mkdir(parents=True)
            self.assertEqual(check_preassembled.unassembled(root), ["verified-garbage-asm-mips"])

    def test_triples(self):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            self.assertEqual(check_preassembled.main(["--triples"]), 0)
        self.assertEqual(out.getvalue().strip().split(","), list(check_preassembled.TRIPLES.values()))

    def test_same_targets(self):
        self.assertEqual(check_preassembled.TRIPLES, preassemble.TRIPLES)


if __name__ == "__main__":
    unittest.main()

module

public import VerifiedGarbage.TCB.PPC64LE.Encode
public import VerifiedGarbage.TCB.Print

/-!
# Printer for the 64-bit little-endian PowerPC model

**Trusted.** Emits the GNU/LLVM assembler syntax used by Rust's
`asm!`/`naked_asm!` on PowerPC, with registers written `%rN` (and `%cr0`)
so that they cannot be read as numbers. The rotates and shifts are printed
as the base instructions (`rlwinm`, `rldicl`, `rldicr`) whose operands the
model's semantics describes, not as extended mnemonics.

Each straight-line instruction, the comparison of each branch and the
return are printed as their machine code (`Encode.lean`), `.long <word>`,
each after a line `// <the instruction's text>`, which the emitter writes in the module's assembly file, not in its code
(`Rust.assembly`): the assembler only copies the words. The
branches (`beq`, `bne`, `b`), the call (`bl`) and the address of a static
(`symLines`) are printed as text, for the assembler and linker to lay out.
-/

@[expose] public section

namespace VG.PPC64LE

/-- `%r<n>`. -/
def Reg.name (r : Reg) : String := s!"%r{r.index}"

def LogicOp.name : LogicOp → String
  | .and => "and" | .or => "or" | .xor => "xor"

/-- A 16-bit immediate, as an unsigned number. -/
def imm16 (v : BitVec 16) : String := toString v.toNat

/-- VMX operands use VR numbers; VSX operands use the aliased VSR number. -/
def VReg.name (r : VReg) : String := s!"%v{r.ctorIdx}"
def VReg.vsx (r : VReg) : String := toString (r.ctorIdx + 32)

def VOp.asm : VOp → String
  | .cipher inv last d n m =>
    let op := if inv then "vncipher" else "vcipher"
    s!"{op}{if last then "last" else ""} {d.name}, {n.name}, {m.name}"
  | .sbox d n => s!"vsbox {d.name}, {n.name}"
  | .sha256 d n st six => s!"vshasigmaw {d.name}, {n.name}, {st.toNat}, {six}"
  | .sha512 d n st six => s!"vshasigmad {d.name}, {n.name}, {st.toNat}, {six}"
  | .pmsumd d n m => s!"vpmsumd {d.name}, {n.name}, {m.name}"
  | .logic op d n m =>
    let op := match op with | .and => "vand" | .or => "vor" | .xor => "vxor"
    s!"{op} {d.name}, {n.name}, {m.name}"
  | .sel d n m mask => s!"vsel {d.name}, {n.name}, {m.name}, {mask.name}"
  | .add dw d n m => s!"{if dw then "vaddudm" else "vadduwm"} {d.name}, {n.name}, {m.name}"
  | .perm d n m c => s!"vperm {d.name}, {n.name}, {m.name}, {c.name}"
  | .sldoi d n m sh => s!"vsldoi {d.name}, {n.name}, {m.name}, {sh}"

def Instr.asm : Instr → List String
  | .vop op => [op.asm]
  | .lxvd2x d a b | .lxvd2xTbl d a b .. => [s!"lxvd2x {d.vsx}, {a.name}, {b.name}"]
  | .stxvd2x n a b => [s!"stxvd2x {n.vsx}, {a.name}, {b.name}"]
  | .mtvsrd d n => [s!"mtvsrd {d.vsx}, {n.name}"]
  | .mfvsrd d n => [s!"mfvsrd {d.name}, {n.vsx}"]
  | .add d n m => [s!"add {d.name}, {n.name}, {m.name}"]
  | .sub d n m => [s!"subf {d.name}, {m.name}, {n.name}"]
  | .mul d n m => [s!"mulld {d.name}, {n.name}, {m.name}"]
  | .mulhu d n m => [s!"mulhdu {d.name}, {n.name}, {m.name}"]
  | .addc d n m => [s!"addc {d.name}, {n.name}, {m.name}"]
  | .adde d n m => [s!"adde {d.name}, {n.name}, {m.name}"]
  | .addze d n => [s!"addze {d.name}, {n.name}"]
  | .subc d n m => [s!"subfc {d.name}, {m.name}, {n.name}"]
  | .sube d n m => [s!"subfe {d.name}, {m.name}, {n.name}"]
  | .addi d n imm => [s!"addi {d.name}, {n.name}, {imm}"]
  | .subi d n imm => [s!"addi {d.name}, {n.name}, -{imm}"]
  | .li d imm => [s!"li {d.name}, {imm}"]
  -- `lis` takes a signed immediate: print the 16 bits as one.
  | .lis d imm => [s!"lis {d.name}, {imm.toInt}"]
  | .ori d n imm => [s!"ori {d.name}, {n.name}, {imm16 imm}"]
  | .oris d n imm => [s!"oris {d.name}, {n.name}, {imm16 imm}"]
  | .logic op d n m => [s!"{op.name} {d.name}, {n.name}, {m.name}"]
  | .rotr .w d n sh => [s!"rlwinm {d.name}, {n.name}, {(32 - sh) % 32}, 0, 31"]
  | .rotr .d d n sh => [s!"rldicl {d.name}, {n.name}, {(64 - sh) % 64}, 0"]
  | .lsr .w d n sh => [s!"rlwinm {d.name}, {n.name}, {(32 - sh) % 32}, {sh}, 31"]
  | .lsr .d d n sh => [s!"rldicl {d.name}, {n.name}, {(64 - sh) % 64}, {sh}"]
  | .lsl d n sh => [s!"rldicr {d.name}, {n.name}, {sh}, {63 - sh}"]
  | .load .w t n off => [s!"lwz {t.name}, {off}({n.name})"]
  | .load .d t n off => [s!"ld {t.name}, {off}({n.name})"]
  | .store .w t n off => [s!"stw {t.name}, {off}({n.name})"]
  | .store .d t n off => [s!"std {t.name}, {off}({n.name})"]
  | .lbz t n off => [s!"lbz {t.name}, {off}({n.name})"]
  | .stb t n off => [s!"stb {t.name}, {off}({n.name})"]
  | .loadRev .w t a b => [s!"lwbrx {t.name}, {a.name}, {b.name}"]
  | .loadRev .d t a b => [s!"ldbrx {t.name}, {a.name}, {b.name}"]
  | .storeRev .w t a b => [s!"stwbrx {t.name}, {a.name}, {b.name}"]
  | .storeRev .d t a b => [s!"stdbrx {t.name}, {a.name}, {b.name}"]
  | .mflr d => [s!"mflr {d.name}"]
  | .mtlr r => [s!"mtlr {r.name}"]
  | .adrSym d name => ["bcl 20, 31, 2f", "2:", s!"mflr {d.name}",
      s!"addis {d.name}, {d.name}, ({name} - 2b)@ha", s!"addi {d.name}, {d.name}, ({name} - 2b)@l"]
  | .push r => ["stdu %r1, -48(%r1)", s!"std {r.name}, 32(%r1)"]
  | .pop r => [s!"ld {r.name}, 32(%r1)", "addi %r1, %r1, 48"]
  | .alloc bytes => [s!"stdu %r1, -{bytes}(%r1)"]
  | .free bytes => [s!"addi %r1, %r1, {bytes}"]
  | .addSp d imm => [s!"addi {d.name}, %r1, {imm}"]

/-- The comparison with zero of a condition. -/
def Cond.cmp : Cond → String
  | .zero .w r | .nonzero .w r => s!"cmplwi %cr0, {r.name}, 0"
  | .zero .d r | .nonzero .d r => s!"cmpldi %cr0, {r.name}, 0"

def Cond.branch : Cond → String
  | .zero .. => "beq"
  | .nonzero .. => "bne"

/-- The lines of an instruction: each of its instructions' text (`asm`) as a
comment, then that instruction's word (`encode`); its text if it has no
encoding (`adrSym`, printed by `symLines`, or an instruction that
`unencodable` reports, which the emitter refuses). -/
def Instr.code (i : Instr) : List String :=
  match i.encode with
  | some ws => (i.asm.zip ws).flatMap fun (t, w) => [s!"// {t}", longLine w]
  | none => i.asm

def printer : Printer isa where
  instr := Instr.code
  branch c l := [s!"// {c.cmp}", longLine c.cmpWord, s!"{c.branch} %cr0, {l}"]
  jump l := s!"b {l}"
  ret := ["// blr", longLine retWord]
  call := "bl"
  -- Label 2 is private to `adrSym`, the `mflr` after its `bcl`: structured
  -- control flow uses 20, 21, …; repeated sequences use the nearest 2b.
  symLines
    | .adrSym d name => some [.text "bcl 20, 31, 2f", .text "2:", .text s!"mflr {d.name}",
        .sym s!"addis {d.name}, {d.name}, (" .ppcHa name, .sym s!"addi {d.name}, {d.name}, (" .ppcLo name]
    | _ => none

  tables
    | .lxvd2xTbl _ _ _ name ws => [(name, ws)]
    | _ => []
  unencodable
    | .adrSym .. => none
    | i => if i.encode.isNone then some "an operand does not fit its field" else none

end VG.PPC64LE

module

public import VerifiedGarbage.Impl.MlKem.X86_64.NttRegs
public import VerifiedGarbage.Proof.Framework.X86_64.Words

/-!
# ML-KEM on x86-64: the NTT on registers, word by word

`nttR` (`Impl/MlKem/X86_64/NttRegs.lean`) moves words between the lanes of
`ymm` registers and memory, and computes butterflies on them. `Sym.run`
follows each of the sixteen words of every register, and of the regions of
memory it reads and writes, as a term (`E`): the word of the polynomial `p`
after `st` layers of `NTT` (`lv st p`), its reduced value (`out p`), a
constant, or an operation on terms. The terms of a butterfly whose words are
`lv st p` and `lv st (p + len)`, with the zetas of their block, become
`lv (st + 1) p` and `lv (st + 1) (p + len)` (`mkAdd`, `mkSub`), and those
of the reduction of `lv 7 p` become `out p`, so that the terms stay small.
A word the machine does not follow is `junk`.

`Sound.lean` proves the machine agrees with the code.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.NttR

/-! ## Terms -/

/-- A word, in terms of the polynomial's words after some layers. -/
inductive E
  /-- Word `p` of the polynomial after `st` layers. -/
  | lv (st p : Nat)
  /-- Word `p` of the polynomial after the seven layers, reduced. -/
  | out (p : Nat)
  /-- The word `v`. -/
  | c (v : Nat)
  | add (a b : E)
  | sub (a b : E)
  /-- The low and the high word of the signed product. -/
  | mlo (a b : E)
  | mhi (a b : E)
  /-- The arithmetic shift right by 15. -/
  | sra (a : E)
  | and (a b : E)
  /-- A word not followed. -/
  | junk
  deriving DecidableEq, Inhabited

/-- Structural equality, which the kernel evaluates directly. -/
def E.beq : E → E → Bool
  | .lv a b, .lv x y => a == x && b == y
  | .out a, .out b => a == b
  | .c a, .c b => a == b
  | .add a b, .add x y | .sub a b, .sub x y | .mlo a b, .mlo x y | .mhi a b, .mhi x y | .and a b, .and x y =>
    E.beq a x && E.beq b y
  | .sra a, .sra b => E.beq a b
  | .junk, .junk => true
  | _, _ => false

def E.isJunk : E → Bool
  | .junk => true
  | _ => false

/-- `q`. -/
def qN : Nat := 3329

/-- `q⁻¹ mod 2¹⁶`. -/
def qinvN : Nat := 62209

/-- The terms `vmont` leaves of `b` and the zetas `z`, `z'` (`ζ` and `ζ q⁻¹`). -/
def mt (b : E) (z z' : Nat) : E := .sub (.mhi b (.c z)) (.mhi (.mlo b (.c z')) (.c qN))

/-- The distance of the butterflies of layer `st` (`len`). -/
def lenOf (st : Nat) : Nat := 128 >>> st

/-- The butterfly of `p` and `p'` in layer `st`, with the zetas `z` and `z'` of their block. -/
def bflyOk (st p p' z z' : Nat) : Bool :=
  st < 7 && p' == p + lenOf st && p % (2 * lenOf st) < lenOf st && p' < 256 &&
    z == zmTab (128 / lenOf st + p / (2 * lenOf st)) && z' == z * qinvN % 65536

/-- `a + b`, a butterfly's sum or the end of a reduction where it is one. -/
def mkAdd (a b : E) : E :=
  if a.isJunk || b.isJunk then .junk else
  match a, b with
  | .lv st p, .sub (.mhi (.lv st₁ p') (.c z)) (.mhi (.mlo (.lv st₂ p'') (.c z')) (.c q)) =>
    if st₁ == st && st₂ == st && p'' == p' && q == qN && bflyOk st p p' z z' then .lv (st + 1) p
    else .add a b
  | .sub (.mhi (.lv st p) (.c z)) (.mhi (.mlo (.lv st₁ p₁) (.c z')) (.c q)),
    .and (.sra r) (.c q') =>
    if st == 7 && st₁ == 7 && p₁ == p && q == qN && q' == qN && z == zmTab 0 && z' == zmTab 0 * qinvN % 65536
      && r.beq a && p < 256 then .out p
    else .add a b
  | _, _ => .add a b

/-- `a - b`, a butterfly's difference where it is one. -/
def mkSub (a b : E) : E :=
  if a.isJunk || b.isJunk then .junk else
  match a, b with
  | .lv st p, .sub (.mhi (.lv st₁ p') (.c z)) (.mhi (.mlo (.lv st₂ p'') (.c z')) (.c q)) =>
    if st₁ == st && st₂ == st && p'' == p' && q == qN && bflyOk st p p' z z' then .lv (st + 1) p'
    else .sub a b
  | _, _ => .sub a b

/-- A binary operation, `junk` if either operand is. -/
def mk2 (f : E → E → E) (a b : E) : E := if a.isJunk || b.isJunk then .junk else f a b

def mkSra (a : E) : E := if a.isJunk then .junk else .sra a

/-- `vpackssdw` of the doubleword of the words `lo` and `hi`: a coefficient
of the input (below `2¹⁵`) and zero. -/
def pk (lo hi : E) : E :=
  match lo, hi with
  | .lv 0 p, .c 0 => if p < 256 then .lv 0 p else .junk
  | _, _ => .junk

/-! ## Registers of terms -/

/-- Sixteen words. -/
abbrev Y := List E

def Y.get (a : Y) (e : Nat) : E := a.getD e .junk

/-- Sixteen words from a function of their index. -/
def Y.ofFn (f : Nat → E) : Y := (List.range 16).map f

/-- The selector of quadword `k` in `vpermq`'s immediate. -/
def sel4 (o k : Nat) : Nat := o / 4 ^ k % 4

/-- The binary vector instructions the machine follows (`vpxor` of a register with itself only). -/
def binOk (op : VBinOp) (same : Bool) : Bool :=
  match op with
  | .vpaddw | .vpsubw | .vpmullw | .vpmulhw | .vpand | .vpackssdw | .vpunpcklwd | .vpunpckhwd
  | .vpunpckldq | .vpunpckhdq | .vpunpcklqdq | .vpunpckhqdq => true
  | .vpxor => same
  | _ => false

/-- Word `e` of a binary vector instruction of `a` and `b`. -/
def binW (op : VBinOp) (a b : Y) (e : Nat) : E :=
  let l := e / 8
  let i := e % 8
  let A := fun j => a.get (8 * l + j)
  let B := fun j => b.get (8 * l + j)
  match op with
  | .vpaddw => mkAdd (A i) (B i)
  | .vpsubw => mkSub (A i) (B i)
  | .vpmullw => mk2 .mlo (A i) (B i)
  | .vpmulhw => mk2 .mhi (A i) (B i)
  | .vpand => mk2 .and (A i) (B i)
  | .vpxor => .c 0
  | .vpackssdw => if i < 4 then pk (A (2 * i)) (A (2 * i + 1)) else pk (B (2 * (i - 4))) (B (2 * (i - 4) + 1))
  | .vpunpcklwd => if i % 2 = 0 then A (i / 2) else B (i / 2)
  | .vpunpckhwd => if i % 2 = 0 then A (4 + i / 2) else B (4 + i / 2)
  | .vpunpckldq => if i / 2 % 2 = 0 then A (2 * (i / 4) + i % 2) else B (2 * (i / 4) + i % 2)
  | .vpunpckhdq => if i / 2 % 2 = 0 then A (4 + 2 * (i / 4) + i % 2) else B (4 + 2 * (i / 4) + i % 2)
  | .vpunpcklqdq => if i < 4 then A i else B (i - 4)
  | .vpunpckhqdq => if i < 4 then A (4 + i) else B i
  | _ => .junk

/-- The shifts the machine follows. -/
def shiftOk (op : XShiftOp) (n : Nat) : Bool :=
  match op with
  | .psllq | .psrlq => n == 32
  | .psraw => n == 15
  | _ => false

/-- Word `e` of a shift of `a`. -/
def shiftW (op : XShiftOp) (a : Y) (e : Nat) : E :=
  match op with
  | .psllq => if e % 4 < 2 then .c 0 else a.get (e - 2)
  | .psrlq => if e % 4 < 2 then a.get (e + 2) else .c 0
  | .psraw => mkSra (a.get e)
  | _ => .junk

/-- Word `e` of `vperm2i128` of `a` and `b` with `sel`. -/
def perm2W (sel : Nat) (a b : Y) (e : Nat) : E :=
  let j := e / 8
  if sel.testBit (4 * j + 3) then .c 0 else
    let k := sel / 16 ^ j % 4
    if k < 2 then a.get (8 * (k % 2) + e % 8) else b.get (8 * (k % 2) + e % 8)

/-- Word `e` of `vpblendd` of `a` and `b` with `sel`. -/
def blendW (sel : Nat) (a b : Y) (e : Nat) : E :=
  if sel.testBit (e / 2) then b.get e else a.get e

/-- Word `e` of quadword `w` of a table. -/
def tblW (ws : List (BitVec 64)) (w e : Nat) : E := .c ((ws.getD w 0).toNat / 2 ^ (16 * e) % 2 ^ 16)

/-! ## The machine -/

/-- A region of memory the code reads or writes: the register holding its
base, its offset from it, its number of words, and whether the code may
write it. -/
abbrev Rg := Reg × Nat × Nat × Bool

structure St where
  /-- The terms of the vector registers, by number. -/
  regs : List Y
  /-- The terms of the words of each region, sixteen at a time. -/
  mem : List (List Y)

/-- The vector register numbered `i`. -/
def xr : Nat → XReg
  | 0 => .xmm0 | 1 => .xmm1 | 2 => .xmm2 | 3 => .xmm3
  | 4 => .xmm4 | 5 => .xmm5 | 6 => .xmm6 | 7 => .xmm7
  | 8 => .xmm8 | 9 => .xmm9 | 10 => .xmm10 | 11 => .xmm11
  | 12 => .xmm12 | 13 => .xmm13 | 14 => .xmm14 | _ => .xmm15

/-- The number of a vector register. -/
def xi : XReg → Nat
  | .xmm0 => 0 | .xmm1 => 1 | .xmm2 => 2 | .xmm3 => 3
  | .xmm4 => 4 | .xmm5 => 5 | .xmm6 => 6 | .xmm7 => 7
  | .xmm8 => 8 | .xmm9 => 9 | .xmm10 => 10 | .xmm11 => 11
  | .xmm12 => 12 | .xmm13 => 13 | .xmm14 => 14 | .xmm15 => 15

def St.reg (σ : St) (r : XReg) : Y := σ.regs.getD (xi r) []

def St.set (σ : St) (d : XReg) (v : Y) : St := { σ with regs := σ.regs.set (xi d) v }

/-- The first region from `k` on holding 32 bytes at `base + d`: its index
and the access's first word. -/
def findAux (base : Reg) (d : Nat) : List Rg → Nat → Option (Nat × Nat)
  | [], _ => none
  | r :: rs, k =>
    if r.1 == base && r.2.1 ≤ d && (d - r.2.1) % 32 == 0 && (d - r.2.1) / 2 + 16 ≤ r.2.2.1 then
      some (k, (d - r.2.1) / 2)
    else findAux base d rs (k + 1)

/-- The region and first word of an aligned 32-byte access at `m`. -/
def find (rs : List Rg) (m : MemOp) : Option (Nat × Nat) :=
  if m.index = none ∧ 0 ≤ m.disp ∧ m.disp < 2 ^ 32 then findAux m.base m.disp.toNat rs 0 else none

def St.vop (σ : St) : VOp → Option St
  | .vbin op .l256 d a b =>
    if binOk op (a == b) then some (σ.set d (Y.ofFn (binW op (σ.reg a) (σ.reg b)))) else none
  | .vshift op .l256 d a n =>
    if shiftOk op n.toNat then some (σ.set d (Y.ofFn (shiftW op (σ.reg a)))) else none
  | .vpblendd .l256 d a b sel => some (σ.set d (Y.ofFn (blendW sel.toNat (σ.reg a) (σ.reg b))))
  | .vpermq d a o =>
    some (σ.set d (Y.ofFn fun e => (σ.reg a).get (4 * sel4 o.toNat (e / 4) + e % 4)))
  | .vperm2i128 d a b sel => some (σ.set d (Y.ofFn (perm2W sel.toNat (σ.reg a) (σ.reg b))))
  | _ => none

/-- One instruction of the vector code, with the regions `rs`. -/
def St.step (rs : List Rg) (σ : St) : Instr → Option St
  | .vop o => σ.vop o
  | .vmovdquTbl d m name ws =>
    if m.base = .r8 ∧ m.index = none ∧ name = tblName ∧ 0 ≤ m.disp ∧ m.disp.toNat % 8 = 0 ∧
        m.disp.toNat / 8 + 4 ≤ ws.length ∧ m.disp.toNat < 2 ^ 32 then
      some (σ.set d (Y.ofFn fun e => tblW ws (m.disp.toNat / 8 + e / 4) (e % 4)))
    else none
  | .vmovdquLoad .l256 d m =>
    (find rs m).map fun (k, j) => σ.set d ((σ.mem.getD k []).getD (j / 16) [])
  | .vmovdquStore .l256 m r =>
    (find rs m).bind fun (k, j) =>
      if (rs.getD k default).2.2.2 ∧ j / 16 < (σ.mem.getD k []).length then
        some { σ with mem := σ.mem.set k ((σ.mem.getD k []).set (j / 16) (σ.reg r)) }
      else none
  | _ => none

def St.run (rs : List Rg) (σ : St) : List Instr → Option St
  | [] => some σ
  | i :: is => (σ.step rs i).bind fun σ' => σ'.run rs is

end VG.Proof.MlKem.X86_64.NttR

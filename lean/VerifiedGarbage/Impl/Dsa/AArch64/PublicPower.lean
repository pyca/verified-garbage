module

public import VerifiedGarbage.Impl.Dsa.AArch64.Arithmetic

/-! # Exponentiation for public DSA subgroup orders

As x86-64's (`Impl/Dsa/X86_64/PublicPower.lean`): only public exponents
may use this path, since table addresses and zero-window branches depend on
their digits. Secret exponents retain RSA's masked path (`Crt.expLoop`).
-/

@[expose] public section

namespace VG.Impl.Dsa.AArch64.PublicPower

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64

/-- Address the table entry of the public digit in `sNib`, and the
destination array. -/
def selectHead : List Instr :=
  [ldh .x12 sW, .addImm .x .x4 .x12 2, ldh .x3 Crt.sNib, .mul .x .x4 .x4 .x3, .lsl .x .x4 .x4 3,
    ldh .x16 Crt.sTab, .add .x .x16 .x16 .x4, ldh .x17 (sArr Crt.aT)]

/-- `[aT] := T_v`, `v` in `sNib`, directly. -/
def select : Prog isa := .seq (.block selectHead) copyWords

/-- Multiplication by the zeroth power is the identity. -/
def applyWindow (mul : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (.block [ldh .x3 Crt.sNib]) (.ite (.zero .x .x3) (.block []) (.seq select (mul aY aY Crt.aT)))

/-- Four squarings, the next public digit, and its optional product; the
window count down into `x3`. -/
def window (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) :=
  [mul aY aY aY, mul aY aY aY, mul aY aY aY, mul aY aY aY,
    .block [ldh .x3 Crt.sV, .lsl .x .x4 .x3 4, sth .x4 Crt.sV, .lsr .x .x3 .x3 4, movi .x4 15,
      .logic .and .x .x3 .x3 .x4, sth .x3 Crt.sNib],
    applyWindow mul,
    .block [ldh .x3 Crt.sBit, .subImm .x .x3 .x3 1, sth .x3 Crt.sBit]]

/-- `Y := Y^d` as `Crt.expLoop`, with public windows. -/
def expLoop (mul : Nat → Nat → Nat → Prog isa) (slotPtr slotLen : Nat) : List (Prog isa) := [
  .block [ldh .x5 Crt.sLink, Crt.ldw .x3 .x5 slotPtr, sth .x3 Crt.sExp, Crt.ldw .x3 .x5 slotLen, sth .x3 Crt.sExpLen,
    movi .x3 0, sth .x3 Crt.sI]] ++
  Crt.tabBuild mul ++ [
  .loop (seqs [
    .block [ldh .x3 Crt.sExp, ldh .x4 Crt.sI, .add .x .x3 .x3 .x4, .ldrb .x3 .x3 0, sth .x3 Crt.sV, movi .x3 2,
      sth .x3 Crt.sBit],
    .loop (seqs (window mul)) (.nonzero .x .x3),
    .block [ldh .x3 Crt.sI, .addImm .x .x3 .x3 1, sth .x3 Crt.sI, ldh .x4 Crt.sExpLen, .sub .x .x3 .x4 .x3]])
    (.nonzero .x .x3)]

def encodedPower (mul : Nat → Nat → Nat → Prog isa) (exp expLen : Nat) : Prog isa :=
  .seq (seqs (expLoop mul exp expLen)) (mul aY aY aOne)

def powerCore (mul : Nat → Nat → Nat → Prog isa) (exp expLen : Nat) : Prog isa :=
  .seq (Arithmetic.encodePower mul) (encodedPower mul exp expLen)

def power (mul : Nat → Nat → Nat → Prog isa) (base baseLen exp expLen : Nat) : Prog isa :=
  .seq (Arithmetic.constants mul) (.seq (Arithmetic.load aX base baseLen) (powerCore mul exp expLen))

end VG.Impl.Dsa.AArch64.PublicPower

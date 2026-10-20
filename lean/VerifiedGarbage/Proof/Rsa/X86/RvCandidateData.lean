module

public import VerifiedGarbage.Proof.Rsa.X86.RvCandidateExp
public import VerifiedGarbage.Proof.Rsa.X86.RvSquareStep
public import VerifiedGarbage.Proof.Rsa.X86.RvWindowLoop
public import VerifiedGarbage.Proof.Bignum.X86.PublicCall

/-! # A recovery candidate's public context and the stages of its search

`CandidateData`: what both runs of the search know of their candidate, and
the stages of its exponentiation and squarings.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (sqStart sqIter)

structure CandidateData (g : Geo) (m eLen dLen : Nat) where
  s0 : State
  A : Nat → Nat
  AW : Nat → Nat
  V : Nat → Nat
  zero : A aZ = 0
  value : A mBase = m
  bound : m < 2 ^ (64 * g.n)
  inverse : (m * V sInv + 1) % 2 ^ 32 = 0
  odd : m % 2 = 1
  large : 101 < m
  one : A aO = 2 ^ (64 * g.n) % m
  neg : A aNg = m - 2 ^ (64 * g.n) % m
  r2 : A mR2 = 2 ^ (128 * g.n) % m
  candidate : V sCand < 100
  baseBound : V sCand + 2 < m
  ae : CallArgument s0 g.B g.Z 7 (BitVec.ofNat 32 eLen)
  ad : CallArgument s0 g.B g.Z 9 (BitVec.ofNat 32 dLen)
  tc : V sTc ≤ 8 * (dLen + eLen)
  rb : AW wR < 2 ^ (8 * (dLen + eLen))
  count : 0 < 8 * (dLen + eLen)
  limit : 8 * (dLen + eLen) ≤ 16384
  wide : 8 * (dLen + eLen) < 32 * g.W

def CandidateData.Start {g : Geo} {m eLen dLen : Nat} (C : CandidateData g m eLen dLen) (s : State) :=
  KS g C.s0 C.A liveM C.AW [wR] C.V slotsExp s

/-- The candidate's power, as the squaring loop takes it. -/
def CandidateData.Exp {g : Geo} {m eLen dLen : Nat} (C : CandidateData g m eLen dLen) (s : State) :=
  KS g C.s0 (upd C.A mY (Spec.Rsa.powMod (C.V sCand + 2) (C.AW wR) m * 2 ^ (64 * g.n) % m)) liveSq
    C.AW [wR] (upd C.V sCnt 0) slotsExp s

section
variable {g : Geo} {m eLen dLen : Nat} (C : CandidateData g m eLen dLen)

/-- The exponent's alignment after `k` shifts. -/
abbrev CandidateData.Align (k : Nat) (s : State) : Prop :=
  AI g C.s0 (candA C.A C.V) (upd C.AW wRc (C.AW wR)) C.V (C.AW wR) (alignShifts g eLen dLen) k s

abbrev CandidateData.Mont (s : State) : Prop :=
  KS g C.s0 (candMontA C.A C.V g.n m) liveExp (upd C.AW wRc (alignedExp g (C.AW wR) eLen dLen))
    [wRc, wR] (upd C.V sCnt 0) slotsExp s

abbrev CandidateData.Table (s : State) : Prop :=
  KS g C.s0 (tableA (candMontA C.A C.V g.n m) g.n m (C.V sCand + 2) 16) (List.range 16 ++ liveExp)
    (upd C.AW wRc (alignedExp g (C.AW wR) eLen dLen)) [wRc, wR] (upd C.V sCnt 0) slotsExp s

abbrev CandidateData.Window (k : Nat) (s : State) : Prop :=
  WI g C.s0 (tableA (candMontA C.A C.V g.n m) g.n m (C.V sCand + 2) 16) C.AW C.V m (C.V sCand + 2)
    (alignedExp g (C.AW wR) eLen dLen) (2 * (dLen + eLen)) k s

end

def CandidateData.SquareStart {g : Geo} {m eLen dLen : Nat}
    (C : CandidateData g m eLen dLen) (y : Nat) (s : State) :=
  KS g C.s0 (upd C.A mY (y * 2 ^ (64 * g.n) % m)) liveSq C.AW [wR]
    (upd C.V sCnt 0) slotsExp s

def CandidateData.SquareEnd {g : Geo} {m eLen dLen : Nat}
    (C : CandidateData g m eLen dLen) (y : Nat) (s : State) :=
  SI g C.s0 C.A C.AW (upd C.V sCnt 0) m (8 * (dLen + eLen)) 0
    (sqIter m (C.V sTc) (8 * (dLen + eLen)) (sqStart m y)) s

abbrev CandidateData.y {g : Geo} {m eLen dLen : Nat} (C : CandidateData g m eLen dLen) : Nat :=
  Spec.Rsa.powMod (C.V sCand + 2) (C.AW wR) m

theorem CandidateData.exp_toSquare {g : Geo} {m eLen dLen : Nat}
    (C : CandidateData g m eLen dLen) {s : State} (h : C.Exp s) : C.SquareStart C.y s := h

end VG.Proof.Rsa.X86.Recover

module

public import VerifiedGarbage.Impl.Dsa.Arm.Generation
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-! # DSA parameter generation on ARMv7: the public parameters and the frame

`mkG s`: the public parameters of a call of `vg_dsa_parameter_search` from
`s`: its arguments, the state's first two words (the seeds left and the
modulus's width) and the tape's bytes, which the contract makes public.
`CIn s`: the contract's precondition (`cin_of_pre`). `GI G σ s`: a state of
the search, for the call from `σ` with the parameters `G`: the frame
allocated (`G.sp`), the regions those of the call and the frame, the
callee-saved registers and the fixed frame words in the frame, the frame
words of `LS` holding `V`, and memory changed only in the frame, `scratch`
and the stack below the frame (`G.chg`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.Generation

/-- The public parameters of a call. -/
structure GP where
  sp0 : BitVec 32
  out : BitVec 32
  outLen : Nat
  usedP : BitVec 32
  /-- `rand`, which holds the seeds, the witnesses and the `h` candidates. -/
  wit : BitVec 32
  witLen : Nat
  scr : BitVec 32
  scrLen : Nat
  stP : BitVec 32
  /-- The seeds left, `state[0]`. -/
  k0 : Nat
  pLen : Nat
  qLen : Nat
  witB : List Byte

/-- The modulus's width, `state[1]`. -/
abbrev pLenOf (s : State) : Nat := (s.mem.readW (State.addr (stackArg s 3) + 8#64) 64).toNat

def mkG (s : State) : GP where
  sp0 := s.sp
  out := s.gpr .r0
  outLen := (s.gpr .r1).toNat
  usedP := s.gpr .r2
  wit := s.gpr .r3
  witLen := (stackArg s 0).toNat
  scr := stackArg s 1
  scrLen := (stackArg s 2).toNat
  stP := stackArg s 3
  k0 := (s.mem.readW (State.addr (stackArg s 3)) 64).toNat
  pLen := pLenOf s
  qLen := Spec.Dsa.generationQLen (pLenOf s)
  witB := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat

namespace GP
variable (G : GP)

/-- The seeds are read from `rand`. -/
abbrev seeds : BitVec 32 := G.wit
abbrev seedsLen : Nat := G.witLen
abbrev seedsB : List Byte := G.witB

/-- The frame's base. -/
abbrev sp : BitVec 32 := G.sp0 - BitVec.ofNat 32 F
abbrev rFrame : Region := ⟨State.addr G.sp, F⟩
/-- The stack of the functions we call. -/
abbrev rBelow : Region := ⟨State.addr G.sp - 176#64, 176⟩
abbrev rScr : Region := ⟨State.addr G.scr, G.scrLen * 8⟩
abbrev rOut : Region := ⟨State.addr G.out, G.outLen⟩
abbrev rUsed : Region := ⟨State.addr G.usedP, 8⟩
abbrev rWit : Region := ⟨State.addr G.wit, G.witLen⟩
abbrev rSeeds : Region := G.rWit
abbrev rSt : Region := ⟨State.addr G.stP, 32⟩
abbrev rArgs : Region := ⟨State.addr (G.sp0 + BitVec.ofNat 32 (4 * 0)), 16⟩

/-- What the search may change. -/
abbrev chg : List Region := [G.rFrame, G.rScr, G.rBelow]

end GP

/-- The contract's precondition. -/
structure CIn (s : State) : Prop where
  spLo : 304 ≤ s.sp.toNat
  spHi : s.sp.toNat + 16 ≤ 2 ^ 32
  rd : s.rd = [(mkG s).rWit, (mkG s).rArgs]
  wr : s.wr = [(mkG s).rOut, (mkG s).rUsed, (mkG s).rScr, (mkG s).rSt]
  oU : (mkG s).rOut.Disjoint (mkG s).rUsed
  oW : (mkG s).rOut.Disjoint (mkG s).rWit
  oC : (mkG s).rOut.Disjoint (mkG s).rScr
  oS : (mkG s).rOut.Disjoint (mkG s).rSt
  oA : (mkG s).rOut.Disjoint (mkG s).rArgs
  uW : (mkG s).rUsed.Disjoint (mkG s).rWit
  uC : (mkG s).rUsed.Disjoint (mkG s).rScr
  uS : (mkG s).rUsed.Disjoint (mkG s).rSt
  uA : (mkG s).rUsed.Disjoint (mkG s).rArgs
  wC : (mkG s).rWit.Disjoint (mkG s).rScr
  wS : (mkG s).rWit.Disjoint (mkG s).rSt
  cS : (mkG s).rScr.Disjoint (mkG s).rSt
  cA : (mkG s).rScr.Disjoint (mkG s).rArgs
  sA : (mkG s).rSt.Disjoint (mkG s).rArgs
  fO : (⟨State.addr s.sp - 304#64, 304⟩ : Region).Disjoint (mkG s).rOut
  fU : (⟨State.addr s.sp - 304#64, 304⟩ : Region).Disjoint (mkG s).rUsed
  fW : (⟨State.addr s.sp - 304#64, 304⟩ : Region).Disjoint (mkG s).rWit
  fC : (⟨State.addr s.sp - 304#64, 304⟩ : Region).Disjoint (mkG s).rScr
  fS : (⟨State.addr s.sp - 304#64, 304⟩ : Region).Disjoint (mkG s).rSt
  fA : (⟨State.addr s.sp - 304#64, 304⟩ : Region).Disjoint (mkG s).rArgs
  nO : (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32
  nU : (s.gpr .r2).toNat + 8 ≤ 2 ^ 32
  nW : (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32
  nC : (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 32
  nS : (stackArg s 3).toNat + 32 ≤ 2 ^ 32
  valid : Spec.Dsa.generationPLenValid (pLenOf s)
  outLen : (s.gpr .r1).toNat = 2 * pLenOf s + Spec.Dsa.generationQLen (pLenOf s)
  scrLen : Spec.Dsa.generationScratchWords (pLenOf s) ≤ (stackArg s 2).toNat
  seeds : (s.mem.readW (State.addr (stackArg s 3)) 64).toNat ≤ Spec.Dsa.parameterSeeds
  budget : s.mem.readW (State.addr (stackArg s 3) + 16#64) 64 = BitVec.ofNat 64 (Spec.Dsa.parameterEntropy (pLenOf s))
  randLen : (stackArg s 0).toNat ≤ Spec.Dsa.parameterEntropy (pLenOf s)

theorem cin_of_pre (s : State) (h : (Spec.Dsa.parameterSearchContract abi 304).pre s) : CIn s := by
  sig_pre [Spec.Dsa.parameterSearchContract, Spec.Dsa.parameterSearchSig, abi, argRegs, reduceClassify,
    Loc.val] at h
  obtain ⟨spLo, spHi, rd, wr, oU, oW, oC, oS, oA, uW, uC, uS, uA, wC, wS, cS, cA, sA, fO, fU, fW, fC, fS, fA, nO, nU, nW, nC, nS, valid, outLen, scrLen, seeds, budget, randLen⟩ := h
  exact ⟨spLo, spHi, rd, wr, oU, oW, oC, oS, oA, uW, uC, uS, uA, wC, wS, cS, cA, sA, fO, fU, fW, fC, fS, fA, nO, nU, nW, nC, nS, valid, outLen, scrLen, seeds, budget, randLen⟩

theorem CIn.lens {s : State} (h : CIn s) :
    ((mkG s).pLen = 128 ∧ (mkG s).qLen = 20) ∨ ((mkG s).pLen = 256 ∧ (mkG s).qLen = 32) ∨
      ((mkG s).pLen = 384 ∧ (mkG s).qLen = 32) := by
  have := h.valid
  simp only [Spec.Dsa.generationPLenValid, Bool.or_eq_true, beq_iff_eq] at this
  simp only [mkG, Spec.Dsa.generationQLen]
  rcases this with (e | e) | e <;> simp [e]

/-- The frame word at `o`. -/
abbrev fw (m : Mem) (G : GP) (o : Nat) : BitVec 32 := m.readW (State.addr G.sp + BitVec.ofNat 64 o) 32

/-- The fixed frame words: `out`, the pointers to `used` and `state`,
`scratch` and `rand`. -/
def fixedWords (G : GP) : List (Nat × BitVec 32) :=
  [(fOut, G.out), (fUsedP, G.usedP), (fStP, G.stP), (fScratch, G.scr), (fWit, G.wit),
    (fWitLen, BitVec.ofNat 32 G.witLen)]

/-- A state of the search. -/
structure GI (G : GP) (σ : State) (V : Nat → BitVec 32) (LS : List Nat) (s : State) : Prop where
  pre : CIn σ
  hG : mkG σ = G
  sp : s.sp = G.sp
  rd : s.rd = σ.rd
  wr : s.wr = G.rFrame :: σ.wr
  saved : Spill.Saved s.mem (State.addr G.sp) σ.gpr saved
  fixed : ∀ p ∈ fixedWords G, fw s.mem G p.1 = p.2
  slots : ∀ o ∈ LS, fw s.mem G o = V o
  /-- The live variable words: past the saved registers, below the frame's end, apart from the fixed words. -/
  ls : ∀ o ∈ LS, 40 ≤ o ∧ o + 4 ≤ F ∧ o % 4 = 0 ∧ ∀ p ∈ fixedWords G, o ≠ p.1
  frame : Frame G.chg σ.mem s.mem

end VG.Proof.Dsa.Arm.Gen

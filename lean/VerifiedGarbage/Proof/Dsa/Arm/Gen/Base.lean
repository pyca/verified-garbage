module

public import VerifiedGarbage.Impl.Dsa.Arm.Generation
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-! # DSA parameter generation on ARMv7: the public parameters and the frame

`mkG s`: the public parameters of a call from `s`, the tapes' bytes among
them, which the contract makes public. `CIn s`: the contract's precondition
(`cin_of_pre`). `GI G σ s`: a state of the search, for the call from `σ`
with the parameters `G`: the frame allocated (`G.sp`), the regions those of
the call and the frame, the callee-saved registers and the fixed frame words
in the frame, the frame words of `LS` holding `V`, and memory changed only in
the frame, `scratch` and the stack below the frame (`G.chg`).
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
  pLen : Nat
  qLen : Nat
  seeds : BitVec 32
  seedsLen : Nat
  hs : BitVec 32
  hsLen : Nat
  wit : BitVec 32
  witLen : Nat
  scr : BitVec 32
  scrLen : Nat
  seedsB : List Byte
  hsB : List Byte
  witB : List Byte

def mkG (s : State) : GP where
  sp0 := s.sp
  out := s.gpr .r0
  outLen := (s.gpr .r1).toNat
  pLen := (s.gpr .r2).toNat
  qLen := (s.gpr .r3).toNat
  seeds := stackArg s 0
  seedsLen := (stackArg s 1).toNat
  hs := stackArg s 2
  hsLen := (stackArg s 3).toNat
  wit := stackArg s 4
  witLen := (stackArg s 5).toNat
  scr := stackArg s 6
  scrLen := (stackArg s 7).toNat
  seedsB := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat
  hsB := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 2)) (stackArg s 3).toNat
  witB := Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 4)) (stackArg s 5).toNat

namespace GP
variable (G : GP)

/-- The frame's base. -/
abbrev sp : BitVec 32 := G.sp0 - BitVec.ofNat 32 F
abbrev rFrame : Region := ⟨State.addr G.sp, F⟩
/-- The stack of the functions we call. -/
abbrev rBelow : Region := ⟨State.addr G.sp - 176#64, 176⟩
abbrev rScr : Region := ⟨State.addr G.scr, G.scrLen * 8⟩
abbrev rOut : Region := ⟨State.addr G.out, G.outLen⟩
abbrev rSeeds : Region := ⟨State.addr G.seeds, G.seedsLen⟩
abbrev rHs : Region := ⟨State.addr G.hs, G.hsLen⟩
abbrev rWit : Region := ⟨State.addr G.wit, G.witLen⟩
abbrev rArgs : Region := ⟨State.addr (G.sp0 + BitVec.ofNat 32 (4 * 0)), 32⟩

/-- What the search may change. -/
abbrev chg : List Region := [G.rFrame, G.rScr, G.rBelow]

end GP

/-- The contract's precondition. -/
structure CIn (s : State) : Prop where
  spLo : 304 ≤ s.sp.toNat
  spHi : s.sp.toNat + 32 ≤ 2 ^ 32
  rd : s.rd = [(mkG s).rSeeds, (mkG s).rHs, (mkG s).rWit, (mkG s).rArgs]
  wr : s.wr = [(mkG s).rOut, (mkG s).rScr]
  oS : (mkG s).rOut.Disjoint (mkG s).rSeeds
  oH : (mkG s).rOut.Disjoint (mkG s).rHs
  oW : (mkG s).rOut.Disjoint (mkG s).rWit
  oC : (mkG s).rOut.Disjoint (mkG s).rScr
  oA : (mkG s).rOut.Disjoint (mkG s).rArgs
  sC : (mkG s).rSeeds.Disjoint (mkG s).rScr
  hC : (mkG s).rHs.Disjoint (mkG s).rScr
  wC : (mkG s).rWit.Disjoint (mkG s).rScr
  cA : (mkG s).rScr.Disjoint (mkG s).rArgs
  fO : (⟨State.addr s.sp - 304#64, 304⟩ : Region).Disjoint (mkG s).rOut
  fS : (⟨State.addr s.sp - 304#64, 304⟩ : Region).Disjoint (mkG s).rSeeds
  fH : (⟨State.addr s.sp - 304#64, 304⟩ : Region).Disjoint (mkG s).rHs
  fW : (⟨State.addr s.sp - 304#64, 304⟩ : Region).Disjoint (mkG s).rWit
  fC : (⟨State.addr s.sp - 304#64, 304⟩ : Region).Disjoint (mkG s).rScr
  fA : (⟨State.addr s.sp - 304#64, 304⟩ : Region).Disjoint (mkG s).rArgs
  nO : (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32
  nS : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32
  nH : (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 32
  nW : (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 32
  nC : (stackArg s 6).toNat + (stackArg s 7).toNat * 8 ≤ 2 ^ 32
  lens : Spec.Dsa.generationLengthsValid (s.gpr .r2).toNat (s.gpr .r3).toNat
  outLen : (s.gpr .r1).toNat = 2 * (s.gpr .r2).toNat + (s.gpr .r3).toNat
  seedsMod : (stackArg s 1).toNat % (s.gpr .r3).toNat = 0
  hsMod : (stackArg s 3).toNat % (s.gpr .r2).toNat = 0
  scrLen : Spec.Dsa.generationScratchWords (s.gpr .r2).toNat ≤ (stackArg s 7).toNat

theorem cin_of_pre (s : State) (h : (Spec.Dsa.generateParametersContract abi 304).pre s) : CIn s := by
  sig_pre [Spec.Dsa.generateParametersContract, Spec.Dsa.generateParametersSig, abi, argRegs, reduceClassify,
    Loc.val] at h
  obtain ⟨spLo, spHi, rd, wr, oS, oH, oW, oC, oA, sC, hC, wC, cA, fO, fS, fH, fW, fC, fA, nO, nS, nH, nW, nC,
    lens, outLen, seedsMod, hsMod, scrLen⟩ := h
  exact ⟨spLo, spHi, rd, wr, oS, oH, oW, oC, oA, sC, hC, wC, cA, fO, fS, fH, fW, fC, fA, nO, nS, nH, nW, nC,
    lens, outLen, seedsMod, hsMod, scrLen⟩

/-- The frame word at `o`. -/
abbrev fw (m : Mem) (G : GP) (o : Nat) : BitVec 32 := m.readW (State.addr G.sp + BitVec.ofNat 64 o) 32

/-- The fixed frame words: `out`, its length, `scratch` and the witnesses. -/
def fixedWords (G : GP) : List (Nat × BitVec 32) :=
  [(fOut, G.out), (fOutLen, BitVec.ofNat 32 G.outLen), (fScratch, G.scr), (fWit, G.wit),
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

module

public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.ExponentState
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops

/-! # The complete exponent loop terminates after the prepared native width -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86.PublicRt (countLoop)

theorem wordLoop_ok {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {s : State}
    (S : Stage g capacity c p A Js V wordFields s) (length : g.L = 8 * capacity)
    (odd : c % 2 = 1) (Ylt : A aY < c) (yKnown : aY ∈ Js)
    (oneKnown : aOne ∈ Js) (minusKnown : aMinusOne ∈ Js) (expKnown : aExponent ∈ Js) (xUnknown : aX ∉ Js)
    (tableKnown : ∀ j < 16, aTable + j ∈ Js) (one : A aTable = A aOne)
    (tableLt : ∀ j < 16, A (aTable + j) < c) (F : Bool)
    (flag : V sFlag = BitVec.ofNat 32 F.toNat) (count : V sWords = BitVec.ofNat 32 g.words) :
    WP isa (.loop (wordStep name code) .ne) s fun t =>
      Stage g capacity c p (exponentValues A c g.w g.words F g.words) Js
        (exponentCounters V A c g.w g.words F g.words) wordFields t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  let I : Nat → State → Prop := fun i t =>
    Stage g capacity c p (exponentValues A c g.w g.words F i) Js
      (exponentCounters V A c g.w g.words F i) wordFields t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t
  have start : I 0 s := by
    refine ⟨?_, WorkspaceFrame.refl _ _ _, Keeps.refl _ _⟩
    rw [exponentValues_initial, exponentCounters_initial V A c g.w g.words F count flag]
    exact S
  have positive : 0 < g.words := by have := v.minWidth; unfold Geometry.words; omega
  apply countLoop positive I ?_ start
  intro i t index H
  obtain ⟨St, Ot, Kt⟩ := H
  have yBound : exponentValues A c g.w g.words F i aY < c := by
    rw [exponentValues, setAt_self]
    exact exponentState_lt A (by omega : 0 < c) g.w g.words F Ylt i
  have sameOne : exponentValues A c g.w g.words F i aTable = exponentValues A c g.w g.words F i aOne := by
    unfold exponentValues
    rw [setAt_other _ _ (by decide : aTable ≠ aY), setAt_other _ _ (by decide : aOne ≠ aY)]
    exact one
  have powersLt : ∀ j < 16, exponentValues A c g.w g.words F i (aTable + j) < c := by
    intro j bound
    rw [exponentValues, setAt_other _ _ (by unfold aTable aY; omega)]
    exact tableLt j bound
  refine WP.mono (wordStep_ok verified noSp stack v St length odd yBound yKnown oneKnown minusKnown expKnown
    xUnknown tableKnown sameOne powersLt (by omega : 0 < g.words - i) (by omega : g.words - i ≤ g.words)
    (exponentState A c g.w g.words F i).2 rfl rfl) fun u ⟨Su, Z, Ou, Ku⟩ => ?_
  have Snext : Stage g capacity c p (exponentValues A c g.w g.words F (i + 1)) Js
      (exponentCounters V A c g.w g.words F (i + 1)) wordFields u := Su.mono
    (fun j mem => ⟨mem, congrFun (exponentValues_next A c g.w g.words F i) j⟩)
    (fun d mem => ⟨mem, exponentCounters_next V A c g.w g.words F i mem⟩)
  refine ⟨⟨Snext, Ot.trans Ou, Kt.trans Ku⟩, ?_⟩
  rw [Z]
  congr 1
  exact decide_eq_decide.mpr (by omega)

end VG.Proof.MillerRabin.X86

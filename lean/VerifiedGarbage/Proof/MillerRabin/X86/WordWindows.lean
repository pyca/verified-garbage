module

public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.WordState
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.MillerRabin.X86.Window
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops

/-! # Eight fixed windows consume a complete native exponent word -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86.PublicRt (countLoop)

theorem wordWindows_ok {code : Prog isa} {name : String}
    (verified : Verified target code (Spec.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {s : State}
    (S : Stage g capacity c p A Js V windowFields s) (length : g.L = 8 * capacity)
    (odd : c % 2 = 1) (Ylt : A aY < c) (yKnown : aY ∈ Js)
    (oneKnown : aOne ∈ Js) (minusKnown : aMinusOne ∈ Js) (xUnknown : aX ∉ Js)
    (tableKnown : ∀ j < 16, aTable + j ∈ Js) (one : A aTable = A aOne)
    (tableLt : ∀ j < 16, A (aTable + j) < c)
    (x : BitVec 32) (F : Bool) (value : V sValue = x)
    (flag : V sFlag = BitVec.ofNat 32 F.toNat) (count : V sWindows = 8#32) :
    WP isa (.loop (window name code) .ne) s fun t =>
      Stage g capacity c p (wordValues A c g.w x F 8) Js
        (wordCounters V A c g.w x F 8) windowFields t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  let I : Nat → State → Prop := fun i t =>
    Stage g capacity c p (wordValues A c g.w x F i) Js
      (wordCounters V A c g.w x F i) windowFields t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t
  have start : I 0 s := by
    refine ⟨?_, WorkspaceFrame.refl _ _ _, Keeps.refl _ _⟩
    rw [wordValues_initial, wordCounters_initial V A c g.w x F value count flag]
    exact S
  apply countLoop (by decide : 0 < 8) I ?_ start
  intro i t index H
  obtain ⟨St, Ot, Kt⟩ := H
  have yBound : wordValues A c g.w x F i aY < c := by
    rw [wordValues, setAt_self]
    exact wordState_lt A (by omega : 0 < c) g.w x F Ylt i
  have sameOne : wordValues A c g.w x F i aTable = wordValues A c g.w x F i aOne := by
    unfold wordValues
    rw [setAt_other _ _ (by decide : aTable ≠ aY), setAt_other _ _ (by decide : aOne ≠ aY)]
    exact one
  have powersLt : ∀ j < 16, wordValues A c g.w x F i (aTable + j) < c := by
    intro j bound
    rw [wordValues, setAt_other _ _ (by unfold aTable aY; omega)]
    exact tableLt j bound
  refine WP.mono (window_ok verified noSp stack v St length odd yBound yKnown oneKnown minusKnown
    xUnknown tableKnown sameOne powersLt (by omega : 0 < 8 - i) (by omega : 8 - i < 2 ^ 32)
    (wordState A c g.w x F i).2 rfl rfl) fun u ⟨Su, Z, Ou, Ku⟩ => ?_
  have Snext : Stage g capacity c p (wordValues A c g.w x F (i + 1)) Js
      (wordCounters V A c g.w x F (i + 1)) windowFields u := Su.mono
    (fun j mem => ⟨mem, congrFun (wordValues_next V A c g.w x F i) j⟩)
    (fun d mem => ⟨mem, wordCounters_next V A c g.w x F i mem⟩)
  refine ⟨⟨Snext, Ot.trans Ou, Kt.trans Ku⟩, ?_⟩
  rw [Z]
  congr 1
  exact decide_eq_decide.mpr (by omega)

end VG.Proof.MillerRabin.X86

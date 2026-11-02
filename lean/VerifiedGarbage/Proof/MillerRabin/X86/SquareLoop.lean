module

public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.SquareState
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.MillerRabin.X86.SquareStep
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops

/-! # A fixed public count of prepared squarings with secret threshold masks -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86.PublicRt (countLoop)

theorem squareLoop_ok {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity c q r : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s) (length : g.L = 8 * capacity)
    (odd : c % 2 = 1) (Ylt : A aY < c) (yKnown : aY ∈ Js) (minusKnown : aMinusOne ∈ Js)
    (positive : 0 < q) (qBound : q < 2 ^ 31) (rBound : r < 2 ^ 31) (F : Bool)
    (known : ∀ d ∈ [sSquares, sThreshold, sFlag], d ∈ Ds) (eqUnknown : sEq2 ∉ Ds)
    (count : V sSquares = BitVec.ofNat 32 q) (threshold : V sThreshold = BitVec.ofNat 32 r)
    (flag : V sFlag = BitVec.ofNat 32 F.toNat) :
    WP isa (squareLoop name code) s fun t =>
      Stage g capacity c p (squareValues A c g.w r q F q) Js
        (squareCounters V A c g.w r q F q) Ds t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  let I : Nat → State → Prop := fun i t =>
    Stage g capacity c p (squareValues A c g.w r q F i) Js
      (squareCounters V A c g.w r q F i) Ds t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t
  have start : I 0 s := by
    refine ⟨?_, WorkspaceFrame.refl _ _ _, Keeps.refl _ _⟩
    rw [squareValues_initial, squareCounters_initial V A c g.w r q F count flag]
    exact S
  unfold squareLoop
  apply countLoop positive I ?_ start
  intro i t index H
  obtain ⟨St, Ot, Kt⟩ := H
  have yBound : squareValues A c g.w r q F i aY < c := by
    rw [squareValues, setAt_self]
    exact squareState_lt A (by omega : 0 < c) g.w r q F Ylt i
  refine WP.mono (squareStep_ok verified noSp stack v St length odd yBound yKnown minusKnown
    (by omega : 0 < q - i) (by omega : q - i < 2 ^ 31) rBound (squareState A c g.w r q F i).2
    known ?_ ?_ ?_) fun u ⟨Su, Z, Ou, Ku⟩ => ?_
  · change setAt (setAt V sSquares (BitVec.ofNat 32 (q - i))) sFlag _ sSquares = _
    rfl
  · change setAt (setAt V sSquares (BitVec.ofNat 32 (q - i))) sFlag _ sThreshold = _
    exact threshold
  · exact setAt_self _ _ _
  · have Snext : Stage g capacity c p (squareValues A c g.w r q F (i + 1)) Js
        (squareCounters V A c g.w r q F (i + 1)) Ds u := Su.mono
      (fun j mem => ⟨mem, congrFun (squareValues_next A c g.w r q F i) j⟩) (by
        intro d mem
        refine ⟨List.mem_append_right _ (List.mem_cons_of_mem _ mem), ?_⟩
        exact squareCounters_next V A c g.w r q F (fun eq => eqUnknown (eq ▸ mem)))
    refine ⟨⟨Snext, Ot.trans Ou, Kt.trans Ku⟩, ?_⟩
    rw [Z]
    congr 1
    exact decide_eq_decide.mpr (by omega)

end VG.Proof.MillerRabin.X86

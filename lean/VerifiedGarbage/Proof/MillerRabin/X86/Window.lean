module

public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.WindowState
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call

import VerifiedGarbage.Proof.MillerRabin.X86.FourSquares
import VerifiedGarbage.Proof.MillerRabin.X86.SquareLoop
import VerifiedGarbage.Proof.MillerRabin.X86.StageScan
import VerifiedGarbage.Proof.MillerRabin.X86.StageMultiply
import VerifiedGarbage.Proof.MillerRabin.X86.StageEqual
import VerifiedGarbage.Proof.MillerRabin.X86.RoundArrayFrame
import VerifiedGarbage.Proof.MillerRabin.X86.RoundScalarFrame
import VerifiedGarbage.Proof.MillerRabin.X86.MaskMath
import VerifiedGarbage.Proof.MillerRabin.X86.DataWindowControl
import VerifiedGarbage.Proof.MillerRabin.X86.StageSlots
/-! # One complete prepared fixed-window Miller–Rabin transition -/

-- Formerly `VerifiedGarbage/Proof/MillerRabin/X86/StageWindowControl.lean`, which only this module imported.
section

/-! # A completed window retains all invariants needed by the next window -/

section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Stage.windowEnd {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s)
    (q : Nat) (positive : 0 < q) (bound : q < 2 ^ 32) (E1 E2 F : Bool)
    (known : ∀ d ∈ [sEq1, sEq2, sFlag, sValue, sWindows], d ∈ Ds)
    (eq1 : V sEq1 = BitVec.ofNat 32 E1.toNat) (eq2 : V sEq2 = BitVec.ofNat 32 E2.toNat)
    (flag : V sFlag = BitVec.ofNat 32 F.toNat) (count : V sWindows = BitVec.ofNat 32 q) :
    WP isa (.block windowEnd) s fun t =>
      Stage g capacity c p A Js (windowSlots V q E1 E2 F) ([sFlag, sValue, sWindows] ++ Ds) t ∧
      t.zf = some (decide (q = 1)) ∧ WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx] s t := by
  have scratch : ∀ d ∈ [sFlag, sValue, sWindows], scratchWord d := by
    intro d mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl
    · unfold scratchWord sFlag; simp
    · unfold scratchWord sValue; simp
    · unfold scratchWord sWindows; simp
  refine WP.mono (S.data.windowEnd v q positive bound E1 E2 F known eq1 eq2 flag count)
    fun t ⟨D, Z, O, K⟩ => ?_
  exact ⟨S.afterSlots v D [sFlag, sValue, sWindows] scratch O K (by decide), Z,
    scalar_roundFrame S.data.context.ws.nowrap scratch O, K⟩

end VG.Proof.MillerRabin.X86
end

end

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem window_ok {code : Prog isa} {name : String}
    (verified : Verified target code (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity c q : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {s : State}
    (S : Stage g capacity c p A Js V windowFields s) (length : g.L = 8 * capacity)
    (odd : c % 2 = 1) (Ylt : A aY < c) (yKnown : aY ∈ Js)
    (oneKnown : aOne ∈ Js) (minusKnown : aMinusOne ∈ Js) (xUnknown : aX ∉ Js)
    (tableKnown : ∀ j < 16, aTable + j ∈ Js) (one : A aTable = A aOne)
    (tableLt : ∀ j < 16, A (aTable + j) < c)
    (positive : 0 < q) (qBound : q < 2 ^ 32) (F : Bool)
    (flag : V sFlag = BitVec.ofNat 32 F.toNat) (count : V sWindows = BitVec.ofNat 32 q) :
    WP isa (window name code) s fun t =>
      Stage g capacity c p (setAt A aY (windowResult V A c g.w F).1) Js
        (windowCounters V A c g.w q F) windowFields t ∧
      t.zf = some (decide (q = 1)) ∧ WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  change WP isa (.seq (.block fourSquares) (.seq (squareLoop name code) (.seq scan
    (.seq (mulY name code aX) (.seq (equal sEq1 aY aOne)
      (.seq (equal sEq2 aY aMinusOne) (.block windowEnd))))))) s _
  refine WP.seq (WP.mono (fourSquares_ok v S) fun a ⟨Sa, Oa, Ka⟩ => ?_)
  refine WP.seq (WP.mono (squareLoop_ok verified noSp stack v Sa length odd Ylt yKnown minusKnown
    (by decide : 0 < 4) (by decide : 4 < 2 ^ 31) (by decide : 0 < 2 ^ 31) F
    (by
      intro d mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl <;> decide)
    (by decide) rfl rfl flag) fun b ⟨Sb, Ob, Kb⟩ => ?_)
  change Stage g capacity c p (squareValues A c g.w 0 4 F 4) Js
    (windowSquaresV V A c g.w F) (sSquares :: sThreshold :: windowFields) b at Sb
  refine WP.seq (WP.mono (Sb.scan v tableKnown (by decide) (by decide)) fun d ⟨Sd, Od, Kd⟩ => ?_)
  change Stage g capacity c p (windowScanA V A c g.w F) (aX :: Js)
    (windowSquaresV V A c g.w F) (sSquares :: sThreshold :: windowFields) d at Sd
  have selectedLt : windowScanA V A c g.w F aX < c := by
    rw [windowScanA, setAt_self, squareValues,
      setAt_other _ _ (by unfold aTable aY; omega : aTable + windowDigit V ≠ aY)]
    exact tableLt _ (digit_lt _)
  refine WP.seq (WP.mono (Sd.multiply verified noSp stack v length aX
    (by change 5 < 8 ∧ 5 ≠ 2 ∧ 5 ≠ 3; decide) odd selectedLt
    (List.mem_cons_self ..) (List.mem_cons_of_mem _ yKnown)) fun e ⟨Se, Oe, Ke⟩ => ?_)
  change Stage g capacity c p (windowProductA V A c g.w F) (aX :: Js)
    (windowSquaresV V A c g.w F) (sSquares :: sThreshold :: windowFields) e at Se
  refine WP.seq (WP.mono (Se.equal v sEq1 aY aOne (by unfold scratchWord sEq1; simp)
    (List.mem_cons_of_mem _ yKnown) (List.mem_cons_of_mem _ oneKnown)) fun f ⟨Sf, Of, Kf⟩ => ?_)
  refine WP.seq (WP.mono (Sf.equal v sEq2 aY aMinusOne (by unfold scratchWord sEq2; simp)
    (List.mem_cons_of_mem _ yKnown) (List.mem_cons_of_mem _ minusKnown)) fun h ⟨Sh, Oh, Kh⟩ => ?_)
  change Stage g capacity c p (windowProductA V A c g.w F) (aX :: Js)
    (windowEqV V A c g.w F) (sEq2 :: sEq1 :: sSquares :: sThreshold :: windowFields) h at Sh
  refine WP.mono (Sh.windowEnd v q positive qBound (windowOne V A c g.w F) (windowMinus V A c g.w F)
    (squareState A c g.w 0 4 F 4).2 (by
      intro d mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl | rfl <;> decide) rfl rfl rfl count)
    fun t ⟨St, Z, Ot, Kt⟩ => ?_
  refine ⟨St.mono ?_ ?_, Z, ?_, ?_⟩
  · intro j mem
    exact ⟨List.mem_cons_of_mem _ mem, windowProduct_value V A c g.w F (fun eq => xUnknown (eq ▸ mem))⟩
  · intro d mem
    exact ⟨List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ mem)))), windowCounters_eq V A c g.w q F one mem⟩
  · have Eq1 := scalar_roundFrame Se.data.context.ws.nowrap (rs := [sEq1])
      (by intro d mem; obtain rfl := List.mem_singleton.mp mem; unfold scratchWord sEq1; simp)
      (Outs.of_outside Of (List.mem_singleton_self _))
    have Eq2 := scalar_roundFrame Sf.data.context.ws.nowrap (rs := [sEq2])
      (by intro d mem; obtain rfl := List.mem_singleton.mp mem; unfold scratchWord sEq2; simp)
      (Outs.of_outside Oh (List.mem_singleton_self _))
    exact ((((((Oa.trans Ob).trans Od).trans (mont_roundFrame Oe)).trans Eq1).trans Eq2).trans Ot)
  · exact (((((((Ka.mono (by decide)).trans Kb).trans Kd).trans (Ke.mono (by decide))).trans Kf).trans Kh).trans
      (Kt.mono (by decide)))

end VG.Proof.MillerRabin.X86

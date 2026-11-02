module
public import VerifiedGarbage.Impl.Bignum.Arm.DoubleLoop
public import VerifiedGarbage.Proof.Bignum.Arm.DoubleFnBodyCT
public import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopState

import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopBody
import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopSteps
import VerifiedGarbage.Proof.Bignum.Arm.DoubleFnRestore
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Bignum.Arm.DoubleLoop
meta import VerifiedGarbage.Proof.Bignum.Arm.DoubleFnBodyCT
meta import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopState
meta import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopBody
meta import VerifiedGarbage.Proof.Bignum.Arm.DoubleLoopSteps
meta import VerifiedGarbage.Proof.Bignum.Arm.DoubleFnRestore
meta import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Repeated doubling leaks only the public count and workspace shape -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt Operand)

theorem doubleIndices_ready (s : State) {base : BitVec 32} {len w c : Nat}
    (h : DoubleLoopReady base len w c s) :
    WP isa (.block doubleIndices) s (DoubleFnReady base len w 4 7 4) := by
  refine WP.mono (doubleIndices_ok s) ?_
  rintro u ⟨out, scalar, operand, mem, rest⟩
  refine ⟨⟨h.workspace.congr rest.wr, ?_, ?_, ?_, out, scalar, operand, ?_, ?_⟩, ?_⟩
  · rw [mem]; exact h.layout
  · rw [mem]; exact h.width
  · exact (rest.gpr .r0 (by simp)).trans h.ptr
  · rw [mem]; exact h.inverse
  · rw [mem]; exact h.operand
  · rw [mem]; exact h.two

theorem doubleLoopMultiply_ct {base : BitVec 32} {len w c : Nat}
    (fit : arrAt w 3 + 32 ≤ 8 * len) (hn : 0 < 2 * w) :
    RelCT isa (fun s t => DoubleLoopReady base len w c s ∧
      DoubleLoopReady base len w c t ∧ s.sp = t.sp) doubleLoopMultiply (fun _ _ => True) := by
  let P := fun (s t : State) => DoubleLoopReady base len w c s ∧
    DoubleLoopReady base len w c t ∧ s.sp = t.sp
  have indices : RelCT isa P (.block doubleIndices) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)
  have setup := (relCT_keep_sp indices (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨doubleIndices_ready s h.1, doubleIndices_ready t h.2.1⟩)
  have op4 : Operand 4 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  have op7 : Operand 7 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  exact (setup.mono (fun _ _ h => h) (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩)).seq
    (doubleFnRestore_ct op4 op7 op4 fit hn)

theorem doubleLoopBody_ct {base : BitVec 32} {len w c : Nat}
    (fit : arrAt w 3 + 32 ≤ 8 * len) (hn : 0 < 2 * w) :
    RelCT isa (fun s t => DoubleLoopReady base len w c s ∧
      DoubleLoopReady base len w c t ∧ s.sp = t.sp) doubleLoopBody (fun _ _ => True) := by
  have multiply := (doubleLoopMultiply_ct (base := base) (c := c) fit hn).wp (fun s t h =>
    ⟨WP.mono (doubleLoopMultiply_ok s h.1) (fun _ h => h.1),
      WP.mono (doubleLoopMultiply_ok t h.2.1) (fun _ h => h.1)⟩)
  refine multiply.seq ?_
  apply RelCT.taint (A := taint) (Taint.ofRegs [.r0]) _ (by taint_decide)
  intro s t h
  apply Taint.agree_ofRegs
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact h.2.1.ptr.trans h.2.2.ptr.symm

theorem doubleLoop_ct {base : BitVec 32} {len w c : Nat} (hc : 0 < c) (hc' : c < 2 ^ 32) :
    RelCT isa (fun s t => DoubleLoopReady base len w c s ∧
      DoubleLoopReady base len w c t ∧ s.sp = t.sp) doubleLoop (fun _ _ => True) := by
  let I := fun k (s t : State) => 0 < k ∧ k < 2 ^ 32 ∧ DoubleLoopReady base len w k s ∧
    DoubleLoopReady base len w k t ∧ s.sp = t.sp
  have step : ∀ k, RelCT isa (I k) doubleLoopBody fun s t => isa.eval .ne s = isa.eval .ne t ∧
      (isa.eval .ne s = some false → True) ∧
      (isa.eval .ne s = some true → ∃ j < k, I j s t) := by
    intro k s t tr1 tr2 u v h e1 e2
    obtain ⟨hk, hk', hs, ht, sp⟩ := h
    have hw : 2 ≤ w := hs.width ▸ hs.layout.1
    have fits : arrAt w 8 ≤ 8 * len := hs.width ▸ hs.layout.2.2.1
    have tmp := Nat.le_trans (array_end_le (w := w) (j := 3) (k := 8) (by decide)) fits
    have ct := doubleLoopBody_ct (base := base) (len := len) (w := w) (c := k) (by omega) (by omega)
    obtain ⟨trace, _⟩ := ct s t tr1 tr2 u v ⟨hs, ht, sp⟩ e1 e2
    obtain ⟨_, u', eu, hu, _, _, zu, _, ru⟩ := doubleLoopBody_ok s hs hk hk'
    obtain ⟨_, v', ev, hv, _, _, zv, _, rv⟩ := doubleLoopBody_ok t ht hk hk'
    obtain ⟨-, rfl⟩ := Exec.det e1 eu
    obtain ⟨-, rfl⟩ := Exec.det e2 ev
    refine ⟨trace, ?_, fun _ => trivial, ?_⟩
    · change some (!u.z) = some (!v.z)
      rw [zu, zv]
    · intro branch
      have ne : k ≠ 1 := by
        intro eq
        change some (!u.z) = some true at branch
        simp only [zu, eq, decide_true, Bool.not_true] at branch
        cases branch
      exact ⟨k - 1, by omega, by omega, by omega, hu, hv, ru.sp.trans (sp.trans rv.sp.symm)⟩
  exact (RelCT.loop I step c).mono (fun _ _ h => ⟨hc, hc', h⟩) (fun _ _ h => h)

end VG.Proof.Bignum.Arm

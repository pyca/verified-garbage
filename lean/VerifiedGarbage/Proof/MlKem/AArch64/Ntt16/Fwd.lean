module

import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Pass2
import VerifiedGarbage.Proof.MlKem.AArch64.NttR.FwdU
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
public import VerifiedGarbage.Proof.MlKem.AArch64.NttCommon
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Pass2
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
meta import VerifiedGarbage.Proof.MlKem.AArch64.NttCommon
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# ML-KEM's 16-bit NTT on AArch64: `vg_mlkem_ntt`

The NTT (`correct`), by the machine of `Proof/MlKem/AArch64/NttR/`
(`NttR.ntt_run`), its constant time (`ct`) and its contract (`ntt_verified`);
lemmas about the constants the inverse shares (`vhalf_setLane`, `wp_movzV`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem
open Impl.MlKem.AArch64.Ntt16

/-! ## Constants -/

theorem vhalf_setLane (x : BitVec 128) {k e : Nat} (hk : k < 8) (he : e < 8) (h : BitVec 16) :
    vhalf (setLane x 16 k h) e = if e = k then h else vhalf x e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [getLsbD_vhalf _ _ hi]
  simp only [setLane, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
    show 16 * e + i < 128 by omega, decide_true, Bool.true_and]
  by_cases h' : e = k
  · subst h'
    simp [hi, show ¬ 16 * e + i < 16 * e by omega, show 16 * e + i - 16 * e = i by omega,
      show i < 128 by omega]
  · rw [ite_eq_right h', getLsbD_vhalf _ _ hi]
    rcases (by omega : e < k ∨ k < e) with c | c
    · simp [show 16 * e + i < 16 * k by omega]
    · have : h.getLsbD (16 * e + i - 16 * k) = false := BitVec.getLsbD_of_ge _ _ (by omega)
      simp [show ¬ 16 * e + i < 16 * k by omega, show ¬ 16 * e + i - 16 * k < 16 by omega, this]

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `movz`, keeping the vector registers. -/
theorem wp_movzV {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Only [d] s s' → s'.v = s.v → s'.gpr d = imm.setWidth 64 → WP isa (.block is) s' Q) :
    WP isa (.block (.movz .x d imm 0 :: is)) s Q :=
  WP.cons (s' := s.write .x d (imm.setWidth 64)) (by simp [exec])
    (k _ (only_write _ _ _ _) rfl (write_x_gpr _ _ _))

end

theorem vhalf_zero (e : Nat) : vhalf 0 e = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [getLsbD_vhalf _ _ hi]

theorem setWidth16_imm (h : BitVec 16) : (h.setWidth 64).setWidth 16 = h := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

/-! ## The NTT -/

theorem correct (s₀ : State) (hs : (inPlaceAArch64 Spec.MlKem.ntt).pre s₀) :
    ∃ t s', Exec isa Impl.MlKem.AArch64.Ntt16.ntt s₀ t s' ∧ abiPreserved s₀ s' ∧
      (inPlaceAArch64 Spec.MlKem.ntt).post s₀ s' := by
  have hp : Pre s₀ := pre_of (Ntt.pre_of hs)
  suffices h : WP isa Impl.MlKem.AArch64.Ntt16.ntt s₀ fun s' => s'.sp = s₀.sp ∧
      (inPlaceAArch64 Spec.MlKem.ntt).post s₀ s' by
    obtain ⟨t, s', he, hsp, hpost⟩ := h
    exact ⟨t, s', he, abi_of rfl (by lit_decide) he (by lit_decide), hpost⟩
  exact NttR.ntt_run s₀ ⟨hp.wr, hp.disj, hp.red⟩

theorem ct : ConstantTime isa (inPlaceAArch64 Spec.MlKem.ntt).pre (inPlaceAArch64 Spec.MlKem.ntt).pub
    Impl.MlKem.AArch64.Ntt16.ntt :=
  VG.Taint.constantTime (A := VG.AArch64.taint) (VG.AArch64.Taint.ofRegs [.x0, .x1])
    (fun _ _ _ _ ⟨h0, h1, hsp⟩ => agree_of hsp (by simp [h0, h1])) (by taint_decide)

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]

theorem ntt_verified :
    Verified AArch64.target Impl.MlKem.AArch64.Ntt16.ntt (Spec.MlKem.nttContract AArch64.abi) :=
  Verified.of_correct correct ct (by
    mlkem_implies [Spec.MlKem.nttContract, Spec.MlKem.inPlaceContract, Spec.MlKem.inPlaceSig,
      inPlaceAArch64, AArch64.abi, AArch64.argRegs] [sat] using sat)

end VG.Proof.MlKem.AArch64.Ntt16

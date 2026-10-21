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

The table of pass 2 (`halves_ok`), the constants (`consts_ok`), pass 1 and
pass 2 (`p1_body`, `p2_body`) as loops, and the NTT (`correct`).
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

/-- What `consts` sets. -/
structure CInv (s₀ : State) (n : Nat) (s : State) : Prop where
  keep : Keep [.x9] s₀ s
  mem : s.mem = s₀.mem
  v : ∀ r, r ∉ [VReg.v31, .v30, .v29, .v18, .v19] → s.v r = s₀.v r
  q : Cst (s.v .v31) fun _ => 3329
  c10 : Cst (s.v .v30) fun _ => 10
  c0 : Cst (s.v .v29) fun _ => 0
  z : ∀ k < n, vhalf (s.v .v18) k = BitVec.ofNat 16 (Impl.MlKem.AArch64.Ntt16.zeta (k + 1)) ∧
    vhalf (s.v .v19) k = BitVec.ofNat 16 (tw (Impl.MlKem.AArch64.Ntt16.zeta (k + 1)))

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

theorem consts_ok (s₀ : State) : WP isa (.block consts) s₀ (CInv s₀ 7) := by
  simp only [consts, List.cons_append, List.nil_append]
  refine wp_movzV fun s₁ h₁ v₁ e₁ => wp_vop rfl fun s₂ h₂ => wp_movzV fun s₃ h₃ v₃ e₃ => wp_vop rfl fun s₄ h₄ =>
    wp_vop rfl fun s₅ h₅ => ?_
  have i₀ : CInv s₀ 0 s₅ := by
    refine ⟨(((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep |>.mono,
      by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem], fun r hr => ?_, fun e he => ?_, fun e he => ?_,
      fun e he => ?_, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [h₅.get r hr.2.2.1, h₄.get r hr.2.1, v₃, h₂.get r hr.1, v₁]
    · rw [h₅.get .v31, h₄.get .v31, v₃, h₂.v, vhalf_ofVHalves _ he, e₁, setWidth16_imm]; rfl
    · rw [h₅.get .v30, h₄.v, vhalf_ofVHalves _ he, e₃, setWidth16_imm]; rfl
    · rw [h₅.v, vhalf_zero]; rfl
  refine wp_range_flatMap (M := isa) (CInv s₀) (fun k w hk h => ?_) 7 (Nat.le_refl _) s₅ i₀
  refine wp_movzV fun w₁ h₁ v₁ e₁ => wp_vop (by simp only [VOp.eval, show k < 8 by omega, ite_true]; rfl)
    fun w₂ h₂ => wp_movzV fun w₃ h₃ v₃ e₃ =>
      wp_vop (by simp only [VOp.eval, show k < 8 by omega, ite_true]; rfl) fun w₄ h₄ => wp_nil ?_
  refine ⟨(h.keep.trans ((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep))).mono,
    by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem, h.mem], fun r hr => ?_, ?_, ?_, ?_, fun k' hk' => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [h₄.get r hr.2.2.2.2, v₃, h₂.get r hr.2.2.2.1, v₁]; exact h.v r (by simp [hr])
  · rw [h₄.get .v31, v₃, h₂.get .v31, v₁]; exact h.q
  · rw [h₄.get .v30, v₃, h₂.get .v30, v₁]; exact h.c10
  · rw [h₄.get .v29, v₃, h₂.get .v29, v₁]; exact h.c0
  · have hk8 : k < 8 := by omega
    have k8 : k' < 8 := by omega
    refine ⟨?_, ?_⟩
    · rw [h₄.get .v18, v₃, h₂.v, vhalf_setLane _ hk8 k8, v₁]
      by_cases e : k' = k
      · subst e; rw [ite_eq_left rfl, e₁, setWidth16_imm]
      · rw [ite_eq_right e]; exact (h.z k' (by omega)).1
    · rw [h₄.v, vhalf_setLane _ hk8 k8, v₃, h₂.get .v19, v₁]
      by_cases e : k' = k
      · subst e; rw [ite_eq_left rfl, e₃, setWidth16_imm]
      · rw [ite_eq_right e]; exact (h.z k' (by omega)).2

/-! ## The NTT -/

theorem length_tableHalves : tableHalves.length = 256 :=
  length_flatMap_range _ length_blockHalves 8

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

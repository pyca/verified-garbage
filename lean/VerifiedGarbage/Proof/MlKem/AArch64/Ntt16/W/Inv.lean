module

import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.W.InvPass2
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.W.Fwd
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Inv
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.W.InvPass1
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Pre
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlKem.Arith

/-!
# ML-KEM's 16-bit inverse NTT on AArch64, of a polynomial stored with 16 bits

`Impl.MlKem.AArch64.Ntt16.Readonly.invW` computes the inverse of the
polynomial at `x0`, stored with 16-bit coefficients, in place, with 512
bytes of working space at `x1` and the table `VG_MLKEM_INTT16_ZETAS`
(`invW_ok`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Ntt16.W

open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem
open VG.Proof.MlKem.AArch64.Ntt16 VG.Proof.MlKem.AArch64.Ntt16.Readonly
open VG.Impl.MlKem.AArch64.Ntt16

theorem invW_ok (s₀ : State) (hi : Input s₀ "VG_MLKEM_INTT16_ZETAS" invTableHalves) :
    WP isa Impl.MlKem.AArch64.Ntt16.Readonly.invW s₀ fun s' =>
      s'.sp = s₀.sp ∧ PolyIsW 16 s'.mem (fP s₀) (Spec.MlKem.nttInv (P₀ s₀)) := by
  have hp := hi.toPre
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono_syms (qConsts_ok s₀) fun s₂ c₂ sy₂ => ?_
  refine WP.mono (WP.keepV (Q := fun s₃ => Keep [.x2, .x3, .x6, .x5] s₂ s₃ ∧ s₃.mem = s₂.mem ∧
      s₃.gpr .x2 = s₂.gpr .x0 ∧ s₃.gpr .x3 = s₂.gpr .x1 ∧
      s₃.gpr .x6 = s₂.syms "VG_MLKEM_INTT16_ZETAS" ∧ (s₃.gpr .x5).toNat = 8)
    (by decide) (wp_movS fun w₁ k₁ e₁ sy₁ => wp_movS fun w₂ k₂ e₂ sy₂' =>
      wp_x (by rfl) fun w₃ k₃ e₃ => wp_movz fun w₄ k₄ e₄ =>
      wp_nil ⟨(((k₁.keep.trans k₂.keep).trans k₃.keep).trans k₄.keep).mono,
        by rw [k₄.mem, k₃.mem, k₂.mem, k₁.mem],
        by rw [k₄.get .x2, k₃.get .x2, k₂.get .x2, e₁],
        by rw [k₄.get .x3, k₃.get .x3, e₂, k₁.get .x1],
        by rw [k₄.get .x6, e₃, sy₂', sy₁], by rw [e₄]; rfl⟩))
    fun s₃ ⟨⟨k₃, m₃, e2, e3, e6, e5⟩, hv₃⟩ => ?_
  have kk := c₂.keep.trans k₃
  have st₃ : St s₀ s₃ := ⟨kk.rd, kk.wr, kk.sp, kk.get .x0, kk.get .x1⟩
  have i₀ : LI1 s₀ 0 s₃ (s₀.syms "VG_MLKEM_INTT16_ZETAS") := by
    refine ⟨st₃, ?_, ?_, ?_, by rw [e5], ?_,
      (fun o ho => hi.read ho), hi.apartScratch, fun j hj => ?_, fun r hr => absurd hr (Nat.not_lt_zero _),
      by rw [hv₃]; exact c₂.q, by rw [hv₃]; exact c₂.c10⟩
    · rw [e2, c₂.keep.get .x0]; exact (BitVec.add_zero _).symm
    · rw [e3, c₂.keep.get .x1]; exact (BitVec.add_zero _).symm
    · rw [e6, sy₂]; exact (BitVec.add_zero _).symm
    · rw [m₃, c₂.mem]; exact Frame.refl _ _
    · rw [m₃, c₂.mem]; exact hi.table j hj
  refine WP.seq (WP.mono (count_loop (n := 8) (by decide)
    (fun b s => LI1 s₀ b s (s₀.syms "VG_MLKEM_INTT16_ZETAS")) (fun b hb w hw => ip1_body hp hb hw) i₀)
    fun s₄ h₄ => ?_)
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (invConsts_ok s₄) fun s₅ c₅ => ?_
  refine WP.mono (WP.keepV (Q := fun s₆ => Keep [.x2, .x3, .x5] s₅ s₆ ∧ s₆.mem = s₅.mem ∧
      s₆.gpr .x2 = s₅.gpr .x1 ∧ s₆.gpr .x3 = s₅.gpr .x0 ∧ (s₆.gpr .x5).toNat = 4)
    (by decide) (wp_movS fun w₁ k₁ e₁ _ => wp_movS fun w₂ k₂ e₂ _ => wp_movz fun w₃ k₃ e₃ =>
      wp_nil ⟨((k₁.keep.trans k₂.keep).trans k₃.keep).mono, by rw [k₃.mem, k₂.mem, k₁.mem],
        by rw [k₃.get .x2, k₂.get .x2, e₁], by rw [k₃.get .x3, e₂, k₁.get .x0], by rw [e₃]; rfl⟩))
    fun s₆ ⟨⟨k₆, m₆, e2', e3', e5'⟩, hv₆⟩ => ?_
  have k₅₆ := c₅.keep.trans k₆
  have vv : ∀ r ∈ [VReg.v30, .v31], s₆.v r = s₄.v r := fun r hr => by
    rw [hv₆, c₅.v r (by simp at hr; rcases hr with rfl | rfl <;> decide)]
  have j₀ : LI2 s₀ s₄.mem 0 s₆ := by
    refine ⟨h₄.st.keep k₅₆, ?_, ?_, by rw [e5'], by rw [m₆, c₅.mem]; exact Frame.refl _ _,
      fun r hr i hi => h₄.scr r hr i hi, fun i _ => ?_, fun k hk => by rw [hv₆]; exact (c₅.z k hk).1,
      fun k hk => by rw [hv₆]; exact (c₅.z k hk).2, by rw [vv .v31 (by decide)]; exact h₄.q,
      by rw [vv .v30 (by decide)]; exact h₄.c10⟩
    · rw [e2', c₅.keep.get .x1, h₄.st.x1]; exact (BitVec.add_zero _).symm
    · rw [e3', c₅.keep.get .x0, h₄.st.x0]; exact (BitVec.add_zero _).symm
    · rw [m₆, c₅.mem, ite_eq_right (Nat.not_lt_zero _)]
  refine WP.mono (count_loop (n := 4) (by decide) (LI2 s₀ s₄.mem) (fun c hc w hw => ip2_body hp hc hw) j₀)
    fun s' h' => ⟨h'.st.sp, h'.out.polyIs (fun i _ => Nat.mod_lt _ (by decide)) fun i hi => ?_⟩
  rw [nttInv_eq_nttInvL, map_mul_get _ (show i < n from hi), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by have := val_lt ((nttInvL 7 (P₀ s₀))[i]! * 3303); omega)]

end VG.Proof.MlKem.AArch64.Ntt16.W

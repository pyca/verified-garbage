module

public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Pre
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.Readonly
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Fwd
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Pass2
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Lit

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Ntt16.Readonly
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Proof.MlKem VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.Ntt16

theorem fwd_ok (s₀ : State) (hi : Input s₀ "VG_MLKEM_NTT16_ZETAS" tableHalves) :
    WP isa Impl.MlKem.AArch64.Ntt16.Readonly.fwd s₀ fun s' =>
      s'.sp=s₀.sp ∧ PolyIs s'.mem (fP s₀) (Spec.MlKem.ntt (P₀ s₀)) := by
  have hp := hi.toPre
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono_syms (consts_ok s₀) fun s₂ c₂ sy₂ => ?_
  refine WP.mono_syms (WP.keepV (Q := fun s₃ => Keep [.x2, .x3, .x5] s₂ s₃ ∧ s₃.mem = s₂.mem ∧
      s₃.gpr .x2 = s₂.gpr .x0 ∧ s₃.gpr .x3 = s₂.gpr .x1 + BitVec.ofNat 64 0 ∧ (s₃.gpr .x5).toNat = 4)
    (by decide) (wp_mov fun w₁ k₁ e₁ => wp_addImm (by decide) fun w₂ k₂ e₂ => wp_movz fun w₃ k₃ e₃ =>
      wp_nil ⟨((k₁.keep.trans k₂.keep).trans k₃.keep).mono, by rw [k₃.mem, k₂.mem, k₁.mem],
        by rw [k₃.get .x2, k₂.get .x2, e₁], by rw [k₃.get .x3, e₂, k₁.get .x1], by rw [e₃]; rfl⟩))
    fun s₃ ⟨⟨k₃, m₃, e2, e3, e5⟩, hv₃⟩ sy₃ => ?_
  have kk := c₂.keep.trans k₃
  have st₃ : St s₀ s₃ := ⟨kk.rd, kk.wr, kk.sp, kk.get .x0, kk.get .x1⟩
  have i₀ : L1 s₀ 0 s₃ false := by
    refine ⟨st₃, ?_, ?_, by rw [e5], ?_, trivial, fun r _ c' hc' => absurd hc' (Nat.not_lt_zero _),
      fun k hk => by rw [hv₃]; exact c₂.z k hk, by rw [hv₃]; exact c₂.q, by rw [hv₃]; exact c₂.c10,
      by rw [hv₃]; exact c₂.c0⟩
    · rw [e2, c₂.keep.get .x0]; exact (BitVec.add_zero _).symm
    · rw [e3, c₂.keep.get .x1]
    · rw [m₃,c₂.mem]; exact Frame.refl _ _
  refine WP.seq (WP.mono_syms (count_loop (n := 4) (by decide) (fun c s => L1 s₀ c s false) (fun c hc w hw => p1_body hp hc hw) i₀)
    fun s₄ h₄ sy₄ => ?_)
  refine WP.seq ?_
  refine WP.mono (WP.keepV (Q := fun s₅ => Keep [.x2, .x6, .x4, .x5] s₄ s₅ ∧ s₅.mem = s₄.mem ∧
      s₅.gpr .x2 = s₄.gpr .x1 ∧ s₅.gpr .x6 = s₄.syms "VG_MLKEM_NTT16_ZETAS" ∧
      s₅.gpr .x4 = s₄.gpr .x0 ∧ (s₅.gpr .x5).toNat = 8)
    (by decide) (wp_movS fun w₁ k₁ e₁ sy₁ => wp_x (by rfl) fun w₂ k₂ e₂ =>
      wp_mov fun w₃ k₃ e₃ => wp_movz fun w₄ k₄ e₄ =>
      wp_nil ⟨(((k₁.keep.trans k₂.keep).trans k₃.keep).trans k₄.keep).mono,
        by rw [k₄.mem, k₃.mem, k₂.mem, k₁.mem],
        by rw [k₄.get .x2, k₃.get .x2, k₂.get .x2, e₁],
        by rw [k₄.get .x6, k₃.get .x6, e₂,sy₁],
        by rw [k₄.get .x4, e₃, k₂.get .x0, k₁.get .x0], by rw [e₄]; rfl⟩))
    fun s₅ ⟨⟨k₅, m₅, e2', e6', e4', e5'⟩, hv₅⟩ => ?_
  have j₀ : L2 s₀ s₄.mem 0 s₅ (s₀.syms "VG_MLKEM_NTT16_ZETAS") := by
    refine ⟨h₄.st.keep k₅, ?_, ?_, ?_, by rw [e5'], by rw [m₅]; exact Frame.refl _ _,
      (fun o ho => hi.read ho), hi.apartOutput, hi.table_frame h₄.frame,
      fun r hr c' hc' => h₄.scr r hr c' hc', ?_, by rw [hv₅]; exact h₄.q, by rw [hv₅]; exact h₄.c10,
      by rw [hv₅]; exact h₄.c0⟩
    · rw [e2',h₄.st.x1]; exact (BitVec.add_zero _).symm
    · rw [e6',sy₄,sy₃,sy₂]; exact (BitVec.add_zero _).symm
    · rw [e4', h₄.st.x0]; exact (BitVec.add_zero _).symm
    · rw [m₅]; exact CoeffsUpTo.zero _
  refine WP.mono (count_loop (n := 8) (by decide) (fun b s => L2 s₀ s₄.mem b s (s₀.syms "VG_MLKEM_NTT16_ZETAS")) (fun b hb w hw => p2_body hp hb hw) j₀)
    fun s' h' => ⟨h'.st.sp, ?_⟩
  show PolyIs s'.mem (fP s₀) (Spec.MlKem.ntt (P₀ s₀))
  rw [ntt_eq_nttL]
  exact h'.out.polyIs fun i _ => rfl

end VG.Proof.MlKem.AArch64.Ntt16.Readonly

import VerifiedGarbage.Proof.AesOcb.AArch64.CTBase
import VerifiedGarbage.Proof.AesOcb.AArch64.Init

/-!
# AES-OCB on AArch64: `vg_aes_ocb_init` is constant time

Untrusted: everything here is checked by Lean. The blocks between the calls
run from public registers (the arguments, then the scratch buffer, the key
context and the rounds), and the calls have the same arguments in both runs.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq rel_taint rel_key ct_of KeyCall key_call)

theorem init_ct (v : BlocksImpl) : ConstantTime isa initAArch64.pre initAArch64.pub (init (callees v)) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨q0, q1, q2, q3, qsp⟩ := hq
  have A₁ := IArgs.of h₁
  have A₂ := IArgs.of h₂
  rw [← q0, ← q1, ← q2, ← q3] at A₂
  have o : ∀ x : BitVec 64, x = BitVec.ofNat 64 x.toNat := fun x => (ofNat_toNat64 x).symm
  have hR' : Spec.Aes.rounds ((σ₁.gpr .x1).toNat / 4) = 10 ∨ Spec.Aes.rounds ((σ₁.gpr .x1).toNat / 4) = 12 ∨
      Spec.Aes.rounds ((σ₁.gpr .x1).toNat / 4) = 14 := by rcases A₁.len with h | h | h <;> rw [h] <;> decide
  unfold init
  refine rel_seq (rel_taint [.x0, .x1, .x2, .x3] qsp (by agree_tac [q0, q1, q2, q3]) ⟨_, by taint_decide⟩)
    (init1_ok A₁ rfl (o _) rfl rfl) (init1_ok A₂ q0.symm (by rw [← q1]; exact o _) q2.symm q3.symm)
    fun s₁ s₂ ⟨a19, a20, a22, kc₁, asp, ard, awr, _, _⟩ ⟨b19, b20, b22, kc₂, bsp, brd, bwr, _, _⟩ => ?_
  refine rel_seq (rel_key (keyImpl v) kc₁ kc₂ (by rw [asp, bsp, qsp])) (key_call (keyImpl v) kc₁)
    (key_call (keyImpl v) kc₂) fun t₁ t₂ g₁ g₂ => ?_
  have c19 : t₁.gpr .x19 = σ₁.gpr .x3 := by rw [g₁.saved .x19 (by decide) (by decide), a19]
  have c20 : t₁.gpr .x20 = σ₁.gpr .x2 := by rw [g₁.saved .x20 (by decide) (by decide), a20]
  have c22 : t₁.gpr .x22 = BitVec.ofNat 64 (Spec.Aes.rounds ((σ₁.gpr .x1).toNat / 4)) := by rw [g₁.saved .x22 (by decide) (by decide), a22]
  have d19 : t₂.gpr .x19 = σ₁.gpr .x3 := by rw [g₂.saved .x19 (by decide) (by decide), b19]
  have d20 : t₂.gpr .x20 = σ₁.gpr .x2 := by rw [g₂.saved .x20 (by decide) (by decide), b20]
  have d22 : t₂.gpr .x22 = BitVec.ofNat 64 (Spec.Aes.rounds ((σ₁.gpr .x1).toNat / 4)) := by rw [g₂.saved .x22 (by decide) (by decide), b22]
  refine rel_seq (rel_taint [.x19, .x20, .x22] (by rw [g₁.sp, g₂.sp, asp, bsp, qsp])
      (by agree_tac [c19, c20, c22, d19, d20, d22]) ⟨_, by taint_decide⟩)
    (init2_ok A₁ hR' c19 c20 c22 (by rw [g₁.rd, ard]) (by rw [g₁.wr, awr]))
    (init2_ok A₂ hR' d19 d20 d22 (by rw [g₂.rd, brd]) (by rw [g₂.wr, bwr]))
    fun u₁ u₂ ⟨bc₁, e₁, esp₁, _, _, _⟩ ⟨bc₂, e₂, esp₂, _, _, _⟩ => ?_
  refine rel_seq (blk_rel v.encOk v.encCt fun a b hab => by
      obtain ⟨rfl, rfl⟩ := hab
      exact ⟨_, _, _, _, _, bc₁, bc₂, by rw [esp₁, esp₂, g₁.sp, g₂.sp, asp, bsp, qsp]⟩)
    (blk_call v.encOk v.encNoFrames bc₁) (blk_call v.encOk v.encNoFrames bc₂) fun w₁ w₂ P₁ P₂ => ?_
  exact rel_taint [.x19] (by rw [P₁.sp, P₂.sp, esp₁, esp₂, g₁.sp, g₂.sp, asp, bsp, qsp])
    (by agree_tac [P₁.saved .x19 (by decide) (by decide), P₂.saved .x19 (by decide) (by decide),
      e₁ .x19 (by decide), e₂ .x19 (by decide), c19, d19]) ⟨_, by taint_decide⟩

end VG.Proof.AesOcb.AArch64

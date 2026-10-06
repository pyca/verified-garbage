import VerifiedGarbage.Proof.AesCcm.AArch64.EntryCT
import VerifiedGarbage.Proof.AesCcm.AArch64.MacCT
import VerifiedGarbage.Proof.AesCcm.AArch64.CtrCT

/-!
# AES-CCM on AArch64: `vg_aes_ccm_seal` is constant time

Untrusted: everything here is checked by Lean. Two runs with the same public
arguments (`args_two`): the entry by `entry_rel`, `Ctr₀` by the taint
analysis, the MAC by `mac_rel`, the tag by `tag_rel` and the encryption by
`ctr_rel`; the load of the address of `tag` from its slot by the taint
analysis, and the copy of the tag there and the restore by the taint
analysis from that address, which correctness says both runs load; between
them, the states the correctness proofs describe
(`Proof.AesGcm.AArch64.rel_seq`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.Taint VG.Impl.AesCcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq ct_of)
open VG.Proof.AesCcm (length_bytesAt)

theorem seal_ct (v : Proof.CmacAes.AArch64.UpdateImpl) :
    ConstantTime isa sealAArch64.pre sealAArch64.pub (Impl.AesCcm.AArch64.seal v.callee v.ctr.callee) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨A₁, A₂⟩ := args_two (args_of_seal h₁).1 (args_of_seal h₂).1 hq
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, -, -⟩ := hq
  have L := A₁.lay
  refine rel_seq (entry_rel A₁ A₂ (by agree_tac [q0, q1, q2, q3, q4, q5, q6, q7])) (entry_ok A₁) (entry_ok A₂)
    fun τ₁ τ₂ En₁ En₂ => ?_
  refine rel_seq (rel_env [.x2, .x3] En₁.env En₂.env (by agree_tac [En₁.x2, En₂.x2, En₁.x3, En₂.x3])
      ⟨_, by taint_decide⟩)
    (ctrs_ok L En₁.env (A₁.nonce.of_eq En₁.rd En₁.wr) En₁.x2 En₁.x3)
    (ctrs_ok L En₂.env (A₂.nonce.of_eq En₂.rd En₂.wr) En₂.x2 En₂.x3)
    fun ρ₁ ρ₂ ⟨E₁, f₁, c₁, _, _⟩ ⟨E₂, f₂, c₂, _, _⟩ => ?_
  have S₁ := En₁.slots.mut L (f₁.sub (frame_ctrs_mut _))
  have S₂ := En₂.slots.mut L (f₂.sub (frame_ctrs_mut _))
  have hn₁ := length_bytesAt τ₁.mem (σ₁.gpr .x2) (cxOf σ₁).nl
  have hn₂ := length_bytesAt τ₂.mem (σ₁.gpr .x2) (cxOf σ₁).nl
  refine rel_seq (mac_rel v L E₁ E₂ (.inl rfl) S₁ S₂ hn₁ hn₂ c₁ c₂) (mac_ok v L E₁ S₁ hn₁ c₁ (.inl rfl))
    (mac_ok v L E₂ S₂ hn₂ c₂ (.inl rfl)) fun κ₁ κ₂ M₁ M₂ => ?_
  have d₁ := (Proof.AesGcm.AArch64.bytesAt_frame M₁.frame (macR_c0 L (.inl rfl)) (by decide)).trans c₁
  have d₂ := (Proof.AesGcm.AArch64.bytesAt_frame M₂.frame (macR_c0 L (.inl rfl)) (by decide)).trans c₂
  refine rel_seq (tag_rel v.ctr L M₁.env M₂.env hn₁ hn₂ d₁ d₂ (.inl rfl)) (tag_ok v.ctr L M₁.env hn₁ d₁ (.inl rfl))
    (tag_ok v.ctr L M₂.env hn₂ d₂ (.inl rfl)) fun ω₁ ω₂ ⟨F₁, _, _, g₁, _⟩ ⟨F₂, _, _, g₂, _⟩ => ?_
  have e₁ := (Proof.AesGcm.AArch64.bytesAt_frame g₁ (tagR_c0 L (.inl rfl)) (by decide)).trans d₁
  have e₂ := (Proof.AesGcm.AArch64.bytesAt_frame g₂ (tagR_c0 L (.inl rfl)) (by decide)).trans d₂
  refine rel_seq (ctr_rel v.ctr L F₁ F₂ hn₁ hn₂ e₁ e₂) (ctr_ok v.ctr L F₁ hn₁ e₁) (ctr_ok v.ctr L F₂ hn₂ e₂)
    fun π₁ π₂ ⟨G₁, _, _, h₁, _⟩ ⟨G₂, _, _, h₂, _⟩ => ?_
  have T₁ := S₁.mut L ((M₁.frame.sub (macR_mut (.inl rfl))).trans ((g₁.sub (tagR_mut _ (.inl rfl))).trans
    (h₁.sub (ctrR_mut _))))
  have T₂ := S₂.mut L ((M₂.frame.sub (macR_mut (.inl rfl))).trans ((g₂.sub (tagR_mut _ (.inl rfl))).trans
    (h₂.sub (ctrR_mut _))))
  refine rel_seq (rel_env [] G₁ G₂ (by simp) ⟨_, by taint_decide⟩) (loadTag_ok G₁ T₁ .x11) (loadTag_ok G₂ T₂ .x11)
    fun ρ₁ ρ₂ ⟨x₁, og₁, _, sp₁, rd₁, wr₁⟩ ⟨x₂, og₂, _, sp₂, rd₂, wr₂⟩ => ?_
  exact rel_env [.x11] (G₁.others og₁ (by decide) sp₁ rd₁ wr₁) (G₂.others og₂ (by decide) sp₂ rd₂ wr₂)
    (by agree_tac [x₁, x₂]) ⟨_, by taint_decide⟩

end VG.Proof.AesCcm.AArch64

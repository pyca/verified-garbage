import VerifiedGarbage.Proof.AesCcm.AArch64.EntryCT
import VerifiedGarbage.Proof.AesCcm.AArch64.MacCT
import VerifiedGarbage.Proof.AesCcm.AArch64.CtrCT

/-!
# AES-CCM on AArch64: `vg_aes_ccm_open` is constant time

Untrusted: everything here is checked by Lean. As `seal_ct`, with the
decryption first; then the load of the address of the received tag from its
slot, and the comparison of the tags, the result and the mask of the data,
whose branches and loops depend only on the tag length and the data's length,
by the taint analysis from that address, which correctness says both runs
load. Whether the function returns 1 or 0
leaks nothing: the comparison has no branch, and the mask writes every byte.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.Taint VG.Impl.AesCcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.AArch64 (imm)
open VG.Proof.AesGcm.AArch64 (Eq2 TT rel_seq ct_of)
open VG.Proof.AesCcm (length_bytesAt)

theorem open_ct (v : Proof.CmacAes.AArch64.UpdateImpl) :
    ConstantTime isa openAArch64.pre openAArch64.pub (Impl.AesCcm.AArch64.open v.callee v.ctr.callee) := by
  refine ct_of fun σ₁ σ₂ h₁ h₂ hq => ?_
  obtain ⟨A₁, A₂⟩ := args_two (args_of_open h₁) (args_of_open h₂) hq.1
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, -, -⟩ := hq.1
  have L := A₁.lay
  refine rel_seq (entry_rel A₁ A₂ (by agree_tac [q0, q1, q2, q3, q4, q5, q6, q7])) (entry_ok A₁) (entry_ok A₂)
    fun τ₁ τ₂ En₁ En₂ => ?_
  refine rel_seq (rel_env [.x2, .x3] En₁.env En₂.env (by agree_tac [En₁.x2, En₂.x2, En₁.x3, En₂.x3])
      ⟨_, by taint_decide⟩)
    (ctrs_ok L En₁.env (A₁.nonce.of_eq En₁.rd En₁.wr) En₁.x2 En₁.x3)
    (ctrs_ok L En₂.env (A₂.nonce.of_eq En₂.rd En₂.wr) En₂.x2 En₂.x3)
    fun ρ₁ ρ₂ ⟨E₁, f₁, c₁, _, _⟩ ⟨E₂, f₂, c₂, _, _⟩ => ?_
  have hn₁ := length_bytesAt τ₁.mem (σ₁.gpr .x2) (cxOf σ₁).nl
  have hn₂ := length_bytesAt τ₂.mem (σ₁.gpr .x2) (cxOf σ₁).nl
  refine rel_seq (ctr_rel v.ctr L E₁ E₂ hn₁ hn₂ c₁ c₂) (ctr_ok v.ctr L E₁ hn₁ c₁) (ctr_ok v.ctr L E₂ hn₂ c₂)
    fun π₁ π₂ ⟨F₁, _, _, g₁, _⟩ ⟨F₂, _, _, g₂, _⟩ => ?_
  have S₁ := En₁.slots.mut L ((f₁.sub (frame_ctrs_mut _)).trans (g₁.sub (ctrR_mut _)))
  have S₂ := En₂.slots.mut L ((f₂.sub (frame_ctrs_mut _)).trans (g₂.sub (ctrR_mut _)))
  have d₁ := (Proof.AesGcm.AArch64.bytesAt_frame g₁ (ctrR_disj L (.inl (by decide))) (by decide)).trans c₁
  have d₂ := (Proof.AesGcm.AArch64.bytesAt_frame g₂ (ctrR_disj L (.inl (by decide))) (by decide)).trans c₂
  refine rel_seq (mac_rel v L F₁ F₂ (.inr rfl) S₁ S₂ hn₁ hn₂ d₁ d₂) (mac_ok v L F₁ S₁ hn₁ d₁ (.inr rfl))
    (mac_ok v L F₂ S₂ hn₂ d₂ (.inr rfl)) fun κ₁ κ₂ M₁ M₂ => ?_
  have e₁ := (Proof.AesGcm.AArch64.bytesAt_frame M₁.frame (macR_c0 L (.inr rfl)) (by decide)).trans d₁
  have e₂ := (Proof.AesGcm.AArch64.bytesAt_frame M₂.frame (macR_c0 L (.inr rfl)) (by decide)).trans d₂
  refine rel_seq (tag_rel v.ctr L M₁.env M₂.env hn₁ hn₂ e₁ e₂ (.inr rfl))
    (tag_ok v.ctr L M₁.env hn₁ e₁ (.inr rfl)) (tag_ok v.ctr L M₂.env hn₂ e₂ (.inr rfl))
    fun ω₁ ω₂ ⟨G₁, _, _, k₁, _⟩ ⟨G₂, _, _, k₂, _⟩ => ?_
  have T₁ := S₁.mut L ((M₁.frame.sub (macR_mut (.inr rfl))).trans (k₁.sub (tagR_mut _ (.inr rfl))))
  have T₂ := S₂.mut L ((M₂.frame.sub (macR_mut (.inr rfl))).trans (k₂.sub (tagR_mut _ (.inr rfl))))
  refine rel_seq (rel_env [] G₁ G₂ (by simp) ⟨_, by taint_decide⟩) (loadTag_ok G₁ T₁ .x12) (loadTag_ok G₂ T₂ .x12)
    fun ρ₁ ρ₂ ⟨x₁, og₁, _, sp₁, rd₁, wr₁⟩ ⟨x₂, og₂, _, sp₂, rd₂, wr₂⟩ => ?_
  exact rel_env [.x12] (G₁.others og₁ (by decide) sp₁ rd₁ wr₁) (G₂.others og₂ (by decide) sp₂ rd₂ wr₂)
    (by agree_tac [x₁, x₂]) ⟨_, by taint_decide⟩

end VG.Proof.AesCcm.AArch64

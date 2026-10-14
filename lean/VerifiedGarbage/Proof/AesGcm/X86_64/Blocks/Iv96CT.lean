module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.Iv96
public import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.CT
import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.FnCT
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
meta import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# AES-GCM on whole blocks, x86-64: constant time given the block index

Untrusted: everything here is checked by Lean. As `Blocks.decrypt_ct`, with
a loop given the block index (`DecCodeI`), checked from the arguments in
their registers and the same index in both runs (the public argument at
`rsp + 16`, kept by the entry).
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64.Blocks

open VG VG.X86_64 VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Blocks
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Spec.Gcm (Block blockAt blocksAt)

theorem scratch_check (aligned : Bool) : ∃ hc, ((taint.check (Taint.ofRegs (.r11 :: args))
    (.block (scratchSetup aligned)) hc).map fun τ' =>
      (RegSet.ofList (.r11 :: args)).subset τ'.regs && (!false || τ'.flags)) = some true := by
  cases aligned
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩

/-- `vg_aes_gcm_decrypt_blocks` with a loop given the block index, for any
contract whose precondition gives `BP` and `IdxArg 16`, and whose public
arguments include those of `blocksPub` and the index. -/
theorem decryptI_ct (v : GcmImpl) {M : CtxMode} {aligned : Bool} (c : DecCodeI M) {k : Contract isa}
    (hpre : ∀ s, k.pre s → BP M s ∧ IdxArg 16 s)
    (hpub : ∀ s s', k.pub s s' → Proof.AesGcm.blocksPub s s' ∧
      s.mem.readW (SP s + BitVec.ofNat 64 16) 32 = s'.mem.readW (SP s' + BitVec.ofNat 64 16) 32) :
    ConstantTime isa k.pre k.pub (decrypt v.callees.ctr v.callees.gh (some c.dec) aligned true) := by
  refine ct_of_rel fun s₀ s₀' h h' hq => ?_
  obtain ⟨hp, hx⟩ := hpre _ h
  obtain ⟨hp', hx'⟩ := hpre _ h'
  have pb := Pub.of (hpub _ _ hq).1
  have hi := (hpub _ _ hq).2
  have tl : ∀ q ys ys', RelCT isa (fun s₁ s₂ => Mid s₀ q q ys s₁ ∧ Mid s₀' q q ys' s₂)
      (tail (ghCall v.callees.gh) (ctrCall v.callees.ctr)) fun _ _ => True := fun _ _ _ =>
    tail_rel hp hp' pb (fun q hq => ghCall_rel hp hp' pb v.gh hq) (fun q hq => ctrCall_rel hp hp' pb v.ctr hq)
  refine RelCT.seq (entry_rel hp hp' pb) ?_
  refine fullBody_relG hp hp' pb aligned c.dec _ _ (ys := fun s q => blocksAt s.mem (D s) q) (fun _ => rfl) ?_
    (tl 0 _ _)
  have a := rel_wp (P := fun s₁ s₂ => (∀ r ∈ .r11 :: args, s₁.gpr r = s₂.gpr r) ∧ EntryPost s₀ s₁ ∧
      EntryPost s₀' s₂ ∧ 16 ≤ n s₀)
    (rel_regs (.r11 :: args) (.r11 :: args) false (fun _ _ h => h.1) (scratch_check aligned))
    (F₁ := fun t => EntryPost s₀ t ∧ 16 ≤ n s₀) (F₂ := fun t => EntryPost s₀' t ∧ 16 ≤ n s₀')
    (fun _ _ h => ⟨⟨h.2.1, h.2.2.2⟩, h.2.2.1, by rw [pb.en]; exact h.2.2.2⟩)
    (fun _ ⟨⟨h11, hg, _, hf, hrd, hwr⟩, h16⟩ => scratchI_ok (M := M) hp hx h16 h11 hg hf hrd hwr)
    (fun _ ⟨⟨h11, hg, _, hf, hrd, hwr⟩, h16⟩ => scratchI_ok (M := M) hp' hx' h16 h11 hg hf hrd hwr)
  refine RelCT.seq a (c.ct.mono (fun s₁ s₂ h => ?_) fun _ _ h => h)
  obtain ⟨⟨hr, -⟩, ⟨p₁, i₁, e₁⟩, ⟨p₂, i₂, e₂⟩⟩ := h
  refine ⟨fun r hr' => hr r (by simpa [args] using hr'), p₁, p₂, i₁, i₂, ?_⟩
  rw [e₁, e₂]; exact hi

end VG.Proof.AesGcm.X86_64.Blocks

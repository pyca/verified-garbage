module
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.RoundBodyCT

import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PolicyLoopCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Rounds
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH parameter generation on x86-64: timing of a complete primality policy -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.MillerRabin.X86_64 VG.Proof.MlKem.X86_64

def RoundsBefore (d : PolicyPublic) (s : State) : Prop :=
  DrawBefore d.toDrawPublic s ∧ RoundRoom d.p d.rp d.bs s ∧ s.gpr .rsp = d.sp ∧
    word s.mem d.p.O (8 * oChecks) = BitVec.ofNat 64 d.checks ∧ 0 < d.checks ∧ d.checks < 2 ^ 31

private theorem init_policy (d : PolicyPublic) (s : State) (h : RoundsBefore d s) :
    WP isa (.block roundInit) s (fun t => PolicyBefore {d with i := 0} t ∧ 0 < d.checks) := by
  obtain ⟨hd, hroom, hsp, hc, hpos, hc32⟩ := h
  refine WP.mono (roundInit_ok hd.1) fun t ⟨hm, k⟩ => ?_
  have hf : Frm d.p.O [(8 * oIndex, 8)] s.mem t.mem := by
    rw [hm]; exact Frm.of_outside (writeW_outside _ _ _ (by decide)) (by simp)
  have ht := hd.1.outer_frame hf (by simp [oIndex]) (by simp [oIndex]) k
    ((k.gpr (by decide)).trans hd.1.ready.good.rdi)
  have hst : t.gpr .rsp = s.gpr .rsp := k.gpr (by decide)
  refine ⟨⟨⟨ht, k.2.2.trans hd.2.1, hd.2.2⟩, hroom.congr hst, hst.trans hsp, ?_, ?_, by change 0 < 2 ^ 31; decide, hc32⟩, hpos⟩
  · rw [hm]; exact word_writeW_self _ _ _ _
  · rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact hc

theorem rounds_ct (M : Mont) (K : Kernel) :
    RelCT isa (Two RoundsBefore) (rounds M.mm K.run) fun _ _ => True := by
  unfold rounds
  refine RelCT.seq (two_post
    (two_map (fun d : PolicyPublic => (⟨d.p.O, d.wr⟩ : LinkPublic)) (fun _ _ h => h.1.link) roundInit_ct)
    init_policy) ?_
  exact two_map (fun d : PolicyPublic => {d with i := 0}) (fun _ _ h => h) (policyLoop_ct M K)

end VG.Proof.Ffdh.X86_64.ParameterCandidate

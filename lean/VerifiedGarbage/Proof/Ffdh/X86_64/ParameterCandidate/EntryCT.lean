module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.EntryCTData
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.EntryCTData
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr

/-! # FFDH parameter generation on x86-64: constant-time ABI entry -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Rsa.X86_64.Crt (stk)
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.MlKem.X86_64

private theorem entry_head (p : CandidateP) (s : State) (h : CR p s) :
    WP isa (.block [.mov .rax (.mem (stk 2)), .mov .r10 (.mem (stk 1))]) s (fun t => t.gpr .rax = p.B) := by
  change WP isa (.block [.mov .rax (.mem { base := .rsp, disp := 16 }),
    .mov .r10 (.mem { base := .rsp, disp := 8 })]) s _
  have ha₀ : InRegions (s.rd ++ s.wr) (s.gpr .rsp + 8#64) 8 := (pcCtx_of h.1).args 0 (by decide)
  have ha₁ : InRegions (s.rd ++ s.wr) (s.gpr .rsp + 16#64) 8 := (pcCtx_of h.1).args 1 (by decide)
  have hb : s.mem.readW (off (s.gpr .rsp) 16) 64 = p.B := congrArg CandidateP.B h.2
  refine WP.mono (WP.keep [.rax, .r10] (Q := fun t => t.gpr .rax = p.B) ?_ rfl) fun _ ⟨ht, _⟩ => ht
  change s.mem.readW (s.gpr .rsp + 16#64) 64 = p.B at hb
  xrun [State.ea, BitVec.ofInt_ofNat, hb, ha₁, ha₀]

theorem entry_ct : RelCT isa (Two CR) (.block VG.Impl.Ffdh.X86_64.ParameterCandidate.entry) (Two Entered) := by
  refine two_post ?_ entry_entered
  unfold VG.Impl.Ffdh.X86_64.ParameterCandidate.entry
  rw [List.append_assoc]
  refine RelCT.block_append (RelCT.seq (two_piece [.rsp]
    (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst r
      exact (congrArg CandidateP.sp h₁.2).trans (congrArg CandidateP.sp h₂.2).symm)
    (by taint_decide) entry_head) ?_)
  exact two_taint [.rax] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst r; exact h₁.trans h₂.symm) (by taint_decide)

end VG.Proof.Ffdh.X86_64.ParameterCandidate

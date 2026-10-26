module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateFrameCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.FrameWord
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Workspace
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateFrameCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.FrameWord
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Workspace
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Dsa.AArch64.Run
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash
import Mathlib.Data.Int.ModEq

/-! # Initialize candidate-reduction scratch while retaining source bytes and frame arguments -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Rsa VG.Proof.Rsa.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.AArch64.Generation VG.Impl.Dsa.Generation.Layout

structure CandidateWorkspacePublic where
  frame : CandidateFramePublic
  base : frame.B = off frame.arena arithmetic
  room : slot frame.w 16 ≤ frame.Z
  lower : 2 ≤ frame.w
  upper : frame.w ≤ 48
  outside : ∀ k < 34, ∀ i < 8, frame.Z ≤ ofs frame.B (off (off frame.F (8 * k)) i)

def CandidateWorkspaceBefore (w pLen qLen : Nat) (c : CandidateWorkspacePublic) (s : State) : Prop :=
  CandidateFrameInputs c.frame s ∧ Scr s c.frame.B c.frame.Z ∧
    c.frame.w = w ∧ c.frame.xb.length = pLen ∧ c.frame.qb.length = qLen

def CandidateWorkspaceBase (w pLen qLen : Nat) (c : CandidateWorkspacePublic) (s : State) : Prop :=
  CandidateWorkspaceBefore w pLen qLen c s ∧ s.gpr .x0 = c.frame.B

theorem candidateWorkspace_base {w pLen qLen : Nat} {c : CandidateWorkspacePublic} {s : State}
    (h : CandidateWorkspaceBefore w pLen qLen c s) :
    WP isa (.block workspaceBase) s (CandidateWorkspaceBase w pLen qLen c) := by
  have ld := h.1.read 5 (by decide)
  have hv : s.mem.readW (off c.frame.F 40) 64 = c.frame.arena := h.1.arena
  have step : WP isa (.block workspaceBase) s fun t => t.gpr .x0 = c.frame.B ∧ t.mem = s.mem := by
    brun [workspaceBase, exec_ldrSp (off := 40) (by decide), h.1.stack, ld, hv]
    change c.frame.arena + (BitVec.ofNat 16 arithmetic).setWidth 64 = _
    rw [show (BitVec.ofNat 16 arithmetic).setWidth 64 = BitVec.ofNat 64 arithmetic by decide]
    exact c.base.symm
  refine WP.mono (WP.keep [.x0, .x3] step rfl rfl rfl) fun t ⟨⟨hb, hm⟩, hk⟩ => ?_
  refine ⟨⟨?_, h.2.1.congr hk.wr, h.2.2⟩, hb⟩
  exact ⟨hk.sp.trans h.1.stack,
    (fun k hk' => by rw [hk.rd, hk.wr]; exact h.1.read k hk'),
    hm ▸ h.1.arena, h.1.x.congrK (fun _ _ => by rw [hm]) hk,
    h.1.q.congrK (fun _ _ => by rw [hm]) hk,
    (fun i hi => by rw [hk.wr]; exact h.1.pWrite i hi),
    (fun i hi => by rw [hk.wr]; exact h.1.eWrite i hi)⟩

theorem candidateWorkspace_ready {w pLen qLen : Nat} {c : CandidateWorkspacePublic} {s : State}
    (h : CandidateWorkspaceBase w pLen qLen c s) :
    WP isa (workspace w) s (CandidateFrameBefore pLen qLen c.frame) := by
  have step := workspace_ok h.1.2.1 h.2 c.room c.lower c.upper
  rw [h.1.2.2.1] at step
  refine WP.mono step fun t ⟨ht, _, ff, hk⟩ => ?_
  have hz : 256 ≤ c.frame.Z := Nat.le_trans (Nat.le_add_right 256 _) c.room
  have bound : ∀ r ∈ workspaceRanges, r.1 + r.2 ≤ c.frame.Z := by
    simp only [workspaceRanges, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only <;> omega
  have ht' : Ws t c.frame.B c.frame.Z c.frame.w := by rw [h.1.2.2.1]; exact ht
  refine ⟨?_, ht', h.1.2.2.2⟩
  refine ⟨hk.sp.trans h.1.1.stack, ?_, ?_,
    h.1.1.x.congrK (InScr.of_frm ff bound) hk, h.1.1.q.congrK (InScr.of_frm ff bound) hk, ?_, ?_⟩
  · intro k hk'; rw [hk.rd, hk.wr]; exact h.1.1.read k hk'
  · exact (frame_word_of_workspace ff bound (c.outside 5 (by decide))).trans h.1.1.arena
  · intro i hi; rw [hk.wr]; exact h.1.1.pWrite i hi
  · intro i hi; rw [hk.wr]; exact h.1.1.eWrite i hi

theorem reduceFromFrame_ct (w pLen qLen : Nat) {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0]) (workspace w) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.x0])
      (.block (headerArguments (candidateArguments pLen qLen))) hc₂).isSome = true) :
    RelCT isa (Two (CandidateWorkspaceBefore w pLen qLen))
      (seqs [.block workspaceBase, workspace w, candidateFromFrame pLen qLen]) (fun _ _ => True) := by
  simp only [seqs]
  refine RelCT.seq (two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide))
    (fun _ _ h => candidateWorkspace_base h))
    (RelCT.seq (two_post (two_taint [.x0] ?_ ht₁)
      (fun _ _ h => candidateWorkspace_ready h)) ?_)
  · intro c s t hs ht r hr
    simp only [List.mem_singleton] at hr; subst r
    exact hs.2.trans ht.2.symm
  · exact two_map CandidateWorkspacePublic.frame (fun _ _ h => h) (candidateFromFrame_ct pLen qLen ht₂)

end VG.Proof.Dsa.AArch64.Generation

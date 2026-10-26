module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorFrameCT
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
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorFrameCT
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

/-! # Initialize generator range-check scratch while retaining source bytes and frame arguments -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Rsa VG.Proof.Rsa.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.AArch64.Generation VG.Impl.Dsa.Generation.Layout

structure GeneratorWorkspacePublic where
  frame : GeneratorFramePublic
  base : frame.B = off frame.arena arithmetic
  room : slot frame.w 16 ≤ frame.Z
  lower : 2 ≤ frame.w
  upper : frame.w ≤ 48
  outside : ∀ k < 34, ∀ i < 8, frame.Z ≤ ofs frame.B (off (off frame.F (8 * k)) i)

def GeneratorWorkspaceBefore (w len : Nat) (result : Bool) (c : GeneratorWorkspacePublic) (s : State) : Prop :=
  GeneratorFrameInputs result c.frame s ∧ Scr s c.frame.B c.frame.Z ∧
    c.frame.w = w ∧ c.frame.pb.length = len

def GeneratorWorkspaceBase (w len : Nat) (result : Bool) (c : GeneratorWorkspacePublic) (s : State) : Prop :=
  GeneratorWorkspaceBefore w len result c s ∧ s.gpr .x0 = c.frame.B

theorem generatorWorkspace_base {w len : Nat} {result : Bool} {c : GeneratorWorkspacePublic} {s : State}
    (h : GeneratorWorkspaceBefore w len result c s) :
    WP isa (.block workspaceBase) s (GeneratorWorkspaceBase w len result c) := by
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
    hm ▸ h.1.arena, hm ▸ h.1.candidate, h.1.modulus.congrK (fun _ _ => by rw [hm]) hk,
    h.1.source.congrK (fun _ _ => by rw [hm]) hk,
    h.1.odd⟩

theorem generatorWorkspace_ready {w len : Nat} {result : Bool} {c : GeneratorWorkspacePublic} {s : State}
    (h : GeneratorWorkspaceBase w len result c s) :
    WP isa (workspace w) s (GeneratorFrameBefore len result c.frame) := by
  have step := workspace_ok h.1.2.1 h.2 c.room c.lower c.upper
  rw [h.1.2.2.1] at step
  refine WP.mono step fun t ⟨ht, _, ff, hk⟩ => ?_
  have hz : 256 ≤ c.frame.Z := Nat.le_trans (Nat.le_add_right 256 _) c.room
  have bound : ∀ r ∈ workspaceRanges, r.1 + r.2 ≤ c.frame.Z := by
    simp only [workspaceRanges, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only <;> omega
  have ht' : Ws t c.frame.B c.frame.Z c.frame.w := by rw [h.1.2.2.1]; exact ht
  refine ⟨?_, ht', h.1.2.2.2⟩
  refine ⟨hk.sp.trans h.1.1.stack, ?_, ?_, ?_,
    h.1.1.modulus.congrK (InScr.of_frm ff bound) hk, h.1.1.source.congrK (InScr.of_frm ff bound) hk, h.1.1.odd⟩
  · intro k hk'; rw [hk.rd, hk.wr]; exact h.1.1.read k hk'
  · exact (frame_word_of_workspace ff bound (c.outside 5 (by decide))).trans h.1.1.arena
  · exact (frame_word_of_workspace ff bound (c.outside 21 (by decide))).trans h.1.1.candidate

theorem generatorRangeFromFrame_ct_of (w len : Nat) (result : Bool) {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0]) (workspace w) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.x0])
      (.block (headerArguments (generatorRangeArguments len result))) hc₂).isSome = true) :
    RelCT isa (Two (GeneratorWorkspaceBefore w len result))
      (seqs [.block workspaceBase, workspace w, (.seq (.block (headerArguments (generatorRangeArguments len result)))
        (if result then generatorResult else generatorRange))]) (fun _ _ => True) := by
  simp only [seqs]
  refine RelCT.seq (two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide))
    (fun _ _ h => generatorWorkspace_base h))
    (RelCT.seq (two_post (two_taint [.x0] ?_ ht₁)
      (fun _ _ h => generatorWorkspace_ready h)) ?_)
  · intro c s t hs ht r hr
    simp only [List.mem_singleton] at hr; subst r
    exact hs.2.trans ht.2.symm
  · exact two_map GeneratorWorkspacePublic.frame (fun _ _ h => h) (generatorFrame_ct len result ht₂)

theorem generatorRangeFromFrame_ct (len : Nat) (result : Bool)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorWorkspaceBefore (len / 8) len result))
      (generatorRangeFromFrame len result) (fun _ _ => True) := by
  unfold generatorRangeFromFrame
  rcases hl with rfl | rfl | rfl <;> cases result
  all_goals
    exact generatorRangeFromFrame_ct_of _ _ _ (by taint_decide) (by taint_decide)

end VG.Proof.Dsa.AArch64.Generation

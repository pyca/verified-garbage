module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFrameCTState
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PrimeFrameCTState
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash

/-! # Recover the arithmetic base from the persistent frame -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.RsaOaep.AArch64
open VG.Impl.Dsa.AArch64.Generation

theorem PrimeFrameInputs.congr {p : PrimeFramePublic} {s t : State}
    (h : PrimeFrameInputs p s) (hm : t.mem = s.mem) (hk : Keep [.x0, .x3] s t) : PrimeFrameInputs p t where
  stack := hk.sp.trans h.stack
  read k hk' := by rw [hk.rd, hk.wr]; exact h.read k hk'
  arena := hm ▸ h.arena
  tapePtr := hm ▸ h.tapePtr
  tapeLength := hm ▸ h.tapeLength
  used := hm ▸ h.used
  tape := h.tape.congrK (fun _ _ => by rw [hm]) hk
  source := h.source.congrK (fun _ _ => by rw [hm]) hk
  writable i hi := by rw [hk.wr]; exact h.writable i hi
  usedBound := h.usedBound

def WorkspaceBefore (p : PrimeFramePublic) (s : State) : Prop :=
  PrimeFrameInputs p s ∧ Scr s p.bytes.call.draw.prime.B p.bytes.call.draw.prime.Z

def WorkspaceReady (p : PrimeFramePublic) (s : State) : Prop :=
  WorkspaceBefore p s ∧ s.gpr .x0 = p.bytes.call.draw.prime.B

theorem workspaceBase_ready {p : PrimeFramePublic} {s : State} (h : WorkspaceBefore p s) :
    WP isa (.block workspaceBase) s (WorkspaceReady p) := by
  have ld := h.1.read 5 (by decide)
  have hv : s.mem.readW (VG.Proof.Bignum.off p.F 40) 64 = p.bytes.call.arena := h.1.arena
  have hw : WP isa (.block workspaceBase) s fun t =>
      t.gpr .x0 = p.bytes.call.draw.prime.B ∧ t.mem = s.mem := by
    brun [workspaceBase, exec_ldrSp (off := 40) (by decide),
      h.1.stack, ld, hv, VG.Proof.Bignum.off, Impl.Dsa.Generation.Layout.arithmetic]
    change p.bytes.call.arena + (BitVec.ofNat 16 Impl.Dsa.Generation.Layout.arithmetic).setWidth 64 = _
    rw [show (BitVec.ofNat 16 Impl.Dsa.Generation.Layout.arithmetic).setWidth 64 =
      BitVec.ofNat 64 Impl.Dsa.Generation.Layout.arithmetic by decide]
    exact p.bytes.call.base.symm
  exact WP.mono (WP.keep [.x0, .x3] hw rfl rfl rfl) fun _ ⟨⟨hb, hm⟩, hk⟩ =>
    ⟨⟨h.1.congr hm hk, h.2.congr hk.wr⟩, hb⟩

theorem workspaceBase_ct : RelCT isa (Two WorkspaceBefore) (.block workspaceBase) (Two WorkspaceReady) := by
  exact two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide))
    (fun _ _ h => workspaceBase_ready h)

end VG.Proof.Dsa.AArch64.Generation

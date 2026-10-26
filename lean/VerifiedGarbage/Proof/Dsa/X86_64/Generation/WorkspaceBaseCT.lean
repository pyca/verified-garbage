module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeFrameCTState
import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeFrameCTState
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import Mathlib.Algebra.Group.Nat.Defs

/-! # Recover the arithmetic base from the persistent frame -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64
open VG.Impl.Dsa.X86_64.Generation

theorem PrimeFrameInputs.congr {p : PrimeFramePublic} {s t : State}
    (h : PrimeFrameInputs p s) (hm : t.mem = s.mem) (hk : Keep [.rdi] s t) : PrimeFrameInputs p t where
  stack := (hk.gpr (by decide)).trans h.stack
  read k hk' := by rw [hk.2.1, hk.2.2]; exact h.read k hk'
  arena := hm ▸ h.arena
  tapePtr := hm ▸ h.tapePtr
  tapeLength := hm ▸ h.tapeLength
  used := hm ▸ h.used
  tape := h.tape.congrK (fun _ _ => by rw [hm]) hk
  source := h.source.congrK (fun _ _ => by rw [hm]) hk
  writable i hi := by rw [hk.2.2]; exact h.writable i hi
  wr := hk.2.2.trans h.wr
  usedBound := h.usedBound

def WorkspaceBefore (p : PrimeFramePublic) (s : State) : Prop :=
  PrimeFrameInputs p s ∧ Scr s p.bytes.call.draw.prime.B p.bytes.call.draw.prime.Z

def WorkspaceReady (p : PrimeFramePublic) (s : State) : Prop :=
  WorkspaceBefore p s ∧ s.gpr .rdi = p.bytes.call.draw.prime.B

theorem workspaceBase_ready {p : PrimeFramePublic} {s : State} (h : WorkspaceBefore p s) :
    WP isa (.block workspaceBase) s (WorkspaceReady p) := by
  have ld := h.1.read 5 (by decide)
  have hv : s.mem.readW (off p.bytes.call.draw.prime.sp 40) 64 = p.bytes.call.arena := h.1.arena
  have hw : WP isa (.block workspaceBase) s fun t =>
      t.gpr .rdi = p.bytes.call.draw.prime.B ∧ t.mem = s.mem := by
    xrun [workspaceBase, VG.Proof.RsaOaep.X86_64.ea_sp, h.1.stack, ld, hv,
      sx_ofNat (by decide : Impl.Dsa.Generation.Layout.arithmetic < 2 ^ 31)]
    exact p.bytes.call.base.symm
  exact WP.mono (WP.keep [.rdi] hw rfl) fun _ ⟨⟨hb, hm⟩, hk⟩ =>
    ⟨⟨h.1.congr hm hk, h.2.congr hk.2.2⟩, hb⟩

theorem workspaceBase_ct : RelCT isa (Two WorkspaceBefore) (.block workspaceBase) (Two WorkspaceReady) := by
  refine two_post (two_taint [.rsp] ?_ (by taint_decide)) (fun _ _ h => workspaceBase_ready h)
  intro p s t hs ht r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact hs.1.stack.trans ht.1.stack.symm

end VG.Proof.Dsa.X86_64.Generation

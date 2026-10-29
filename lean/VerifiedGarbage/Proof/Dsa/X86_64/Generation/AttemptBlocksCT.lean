module

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.AttemptStatus
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ArgumentBlocksCT
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PAttempt
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.AttemptStatus
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ArgumentBlocksCT
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PAttempt
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # Public addressing on p-attempt entry and return to the search controller -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.Dsa.X86_64.Generation

structure AttemptReturnPublic where
  F : Addr
  S : Addr
  arena : Addr

def AttemptReturnBefore (p : AttemptReturnPublic) (s : State) : Prop :=
  Lay s p.F p.S ∧ ∃ V W, Rep s.mem p.F p.S V W ∧ W 5 = p.arena

def AttemptReturnReady (p : AttemptReturnPublic) (s : State) : Prop :=
  s.gpr .rdi = off p.arena Impl.Dsa.Generation.Layout.control ∧ s.gpr .rsp = p.F

theorem controlBase_ready {p : AttemptReturnPublic} {s : State} (h : AttemptReturnBefore p s) :
    WP isa (.block controlBase) s (AttemptReturnReady p) := by
  obtain ⟨V, W, R, hw⟩ := h.2
  exact WP.mono (controlBase_ok h.1 R (by rw [hw])) fun _ ⟨hb, _, hk⟩ =>
    ⟨hb, (hk.gpr (by decide)).trans h.1.rsp⟩

theorem controlBase_ct : RelCT isa (Two AttemptReturnBefore) (.block controlBase) (Two AttemptReturnReady) := by
  refine two_post (two_taint [.rsp] ?_ (by taint_decide)) (fun _ _ h => controlBase_ready h)
  intro p s t hs ht r hr
  simp only [List.mem_singleton] at hr; subst r
  exact hs.1.rsp.trans ht.1.rsp.symm

theorem searchReturn_ct : RelCT isa (Two AttemptReturnBefore) (.block searchReturn) (fun _ _ => True) := by
  apply RelCT.block_append (M := isa) (l₁ := controlBase)
    (l₂ := [.mov .rax (.mem (Impl.Mgf1.X86_64.sp 152)), .store (VG.Impl.Bignum.X86_64.hdr 2) .rax])
  refine RelCT.seq controlBase_ct (two_taint [.rdi, .rsp] ?_ (by taint_decide))
  intro p s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hs.1.trans ht.1.symm
  · exact hs.2.trans ht.2.symm

theorem pAttemptArgs_ct : RelCT isa (Two ArgumentRegisters) (.block pAttemptArgs) (fun _ _ => True) :=
  two_taint [.rdi, .rsp] argumentRegisters_pins (by taint_decide)

end VG.Proof.Dsa.X86_64.Generation

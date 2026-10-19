module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.AttemptStatus
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.AttemptStatus
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs

/-! # Public addressing on p-attempt entry and return to the search controller -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.RsaOaep.AArch64 VG.Impl.Dsa.AArch64.Generation

structure AttemptReturnPublic where
  F : Addr
  S : Addr
  arena : Addr

def AttemptReturnBefore (p : AttemptReturnPublic) (s : State) : Prop :=
  Lay s p.F p.S ∧ ∃ V W, Rep s.mem p.F p.S V W ∧ W 5 = p.arena

def AttemptReturnReady (p : AttemptReturnPublic) (s : State) : Prop :=
  s.gpr .x0 = VG.Proof.Bignum.off p.arena Impl.Dsa.Generation.Layout.control ∧ s.sp = p.F

theorem controlBase_ready {p : AttemptReturnPublic} {s : State} (h : AttemptReturnBefore p s) :
    WP isa (.block controlBase) s (AttemptReturnReady p) := by
  obtain ⟨V, W, R, hw⟩ := h.2
  exact WP.mono (controlBase_ok h.1 R (by rw [hw])) fun _ ⟨hb, _, hk⟩ =>
    ⟨hb, hk.sp.trans h.1.sp⟩

theorem controlBase_ct : RelCT isa (Two AttemptReturnBefore) (.block controlBase) (Two AttemptReturnReady) := by
  exact two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide))
    (fun _ _ h => controlBase_ready h)

theorem searchReturn_ct : RelCT isa (Two AttemptReturnBefore) (.block searchReturn) (fun _ _ => True) := by
  apply RelCT.block_append (M := isa) (l₁ := controlBase)
    (l₂ := [.ldrSp .x3 152, VG.Impl.Bignum.AArch64.sth .x3 2])
  refine RelCT.seq controlBase_ct (two_taint [.x0] ?_ (by taint_decide))
  intro p s t hs ht r hr
  obtain rfl := List.mem_singleton.mp hr
  exact hs.1.trans ht.1.symm

structure AttemptPointers where
  B : Addr
  F : Addr

def AttemptRegisters (p : AttemptPointers) (s : State) : Prop := s.gpr .x0 = p.B ∧ s.sp = p.F

theorem pAttemptArgs_ct : RelCT isa (Two AttemptRegisters) (.block pAttemptArgs) (fun _ _ => True) :=
  two_taint [.x0] (fun _ _ _ hs ht r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact hs.1.trans ht.1.symm) (by taint_decide)

end VG.Proof.Dsa.AArch64.Generation

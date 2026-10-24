module

import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsCT
import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroups
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Ffdh.Arm.VettedGroups
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleEnvironment
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedGroupsState
public import VerifiedGarbage.Proof.Framework.RelCT

/-! Exact recognition needs only the public domain and read-only table. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.VettedGroups
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Impl.Ffdh.Arm.VettedGroups

theorem recognition_ct {p : Inputs} {slots : List Nat}
    (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) :
    RelCT isa (fun s t => (Context p slots s ∧ TableAt (s.syms tableSym) groups s) ∧
      (Context p slots t ∧ TableAt (t.syms tableSym) groups t) ∧ s.sp = t.sp ∧ s.syms tableSym = t.syms tableSym)
      code (fun _ _ => True) := by
  let P := fun s t : State => (Context p slots s ∧ TableAt (s.syms tableSym) groups s) ∧
    (Context p slots t ∧ TableAt (t.syms tableSym) groups t) ∧ s.sp = t.sp ∧ s.syms tableSym = t.syms tableSym
  let Q := fun s t : State => ∃ table, ScanReady table p.domain p.k p.dom groups s ∧
    ScanReady table p.domain p.k p.dom groups t
  have stage : RelCT isa P (.block entry) Q := by
    intro s t tr1 tr2 u v h e1 e2
    have timing := entry_ct s t tr1 tr2 u v h.2.2.1 e1 e2
    obtain ⟨_, u', eu, ⟨cu,_,mu⟩,ru⟩ := entry_ok s h.1.1 h24 h28 h32
    obtain ⟨_, v', ev, ⟨cv,_,mv⟩,rv⟩ := entry_ok t h.2.1.1 h24 h28 h32
    obtain ⟨_,rfl⟩ := Exec.det e1 eu
    obtain ⟨_,rfl⟩ := Exec.det e2 ev
    have source (a b : State) (context : Context p slots a)
        (mem : b.mem = a.mem) (rest : VG.Proof.X25519.Arm.Rest [.r4,.r6,.r7,.r8,.r9,.r10] a b) :
        Source p.domain p.k p.dom b :=
      ⟨by rw [p.domainLength]; split <;> have := p.minLength <;> omega,
        context.domain.fits, by rw [rest.rd,rest.wr]; exact context.domain.readable,
        by rw [mem]; exact context.domain.bytes, by rw [p.domainLength]; split <;> simp⟩
    have tabU := h.1.2.after mu ru
    have tabV := h.2.1.2.after mv rv
    have symbol : s.syms tableSym = t.syms tableSym := h.2.2.2
    rw [← symbol] at tabV cv
    exact ⟨timing.1, s.syms tableSym,
      ⟨source s u h.1.1 mu ru, tabU, cu⟩, ⟨source t v h.2.1.1 mv rv, tabV, cv⟩⟩
  have scanning : RelCT isa Q loop (fun _ _ => True) := by
    apply RelCT.exists_
    intro table
    exact loop_ct (by decide) (by have := p.maxLength; omega) (by decide)
  have restore : RelCT isa (fun _ _ => True) (.block [.mov .r0 (.reg .r8)]) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro _ _ _; exact Taint.agree_ofRegs (by simp)
  exact stage.seq (scanning.seq restore)

end VG.Proof.Ffdh.Arm.VettedGroups

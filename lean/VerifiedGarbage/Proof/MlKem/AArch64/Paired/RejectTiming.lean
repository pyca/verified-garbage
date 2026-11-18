module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Reject
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Continue
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Zero
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.TaintSumGeneric
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Continue
meta import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Reject
meta import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Zero
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.TaintSumGeneric

/-! ### `MlKem.AArch64.Paired.Trace`, which this module and modules that import it used -/

section

/-! # Constant-time scalar wrappers around the public rejection loop -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.MlKem.AArch64

theorem rejectEntry_ct (buf out : Nat) : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [])) (.block (rejectEntry buf out)) := by
  unfold rejectEntry ptrTo
  split <;> exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [])
    (fun _ _ _ _ h => h) (hc := .block []) rfl

theorem continueEntry_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [])) (.block continueEntry) := by
  unfold continueEntry
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [])
    (fun _ _ _ _ h => h) (hc := .block []) rfl

theorem moveFlag_ct (flag : Reg) : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [])) (.block [mov flag .x0]) := by
  cases flag <;> exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [])
    (fun _ _ _ _ h => h) (hc := .block []) rfl

theorem loadCheckpoint_ct (slot : Nat) : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x19]))
    (.block [.ldr .x .x3 .x19 slot,.ldr .x .x4 .x19 (slot+8)]) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x19]) (fun _ _ _ _ h => h) (hc := .block []) rfl

/-- Loading and storing a cursor at `x1`, whose address is public. -/
theorem cursor_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x1])) (.block [.ldr .x .x3 .x1 0,.ldr .x .x4 .x1 8]) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x1]) (fun _ _ _ _ h => h) (hc := .block []) rfl

theorem storeCursor_ct : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x1])) (.block [.str .x .x3 .x1 0,.str .x .x4 .x1 8]) :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x1]) (fun _ _ _ _ h => h) (hc := .block []) rfl

theorem zeroSuffix_ct (w16 : Bool) : ConstantTime isa (fun _ => True)
    (VG.AArch64.Taint.Agree (Taint.ofRegs [.x3,.x4])) (Rej8.zeroSuffix w16) := by
  cases w16 <;> exact VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x3,.x4]) (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.MlKem.AArch64.Paired

end

end

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem

 theorem exec_post {c : Prog isa} {s t : State} {tr : List Leak} {Q : State→Prop}
    (h : WP isa c s Q) (e : Exec isa c s tr t) : Q t := by
  obtain ⟨_,u,eu,hu⟩ := h
  obtain ⟨_,rfl⟩ := Exec.det e eu
  exact hu

theorem segment_entry_relCT {w16 : Bool} (L : List Zq) (N : Nat) (B : Nat→Byte) (bP aP : Addr)
    (hN : 0<N) (hm : N%4=0) :
    RelCT isa (fun s u => Rej8.EntryW w16 L N B bP aP s ∧ Rej8.EntryW w16 L N B bP aP u ∧
      s.sp=u.sp ∧ s.gpr .x16=u.gpr .x16) (Impl.MlKem.AArch64.Rej8.rejLoop w16)
      (fun s u => s.sp=u.sp) := by
  intro s u tr ur s' u' h es eu
  obtain ⟨ht,hs,hu⟩ := Rej8.segment_relCT h.1 h.2.1 h.2.2.1 h.2.2.2 hN hm
    s u tr ur s' u' ⟨rfl,rfl⟩ es eu
  exact ⟨ht,hs.keep.sp.trans (h.2.2.1.trans hu.keep.sp.symm)⟩

theorem reject_relCT {w16 : Bool} {s u : State} {buf out : Nat} (hb : buf<4096) (ho : out<65536)
    {flag : Reg} (hf : flag≠.x3 ∧ flag≠.x4) {B : Nat→Byte}
    (ps : Rej8.EnvW w16 168 B (s.gpr .x19+BitVec.ofNat 64 buf) (s.gpr .x28+BitVec.ofNat 64 out) s)
    (pu : Rej8.EnvW w16 168 B (u.gpr .x19+BitVec.ofNat 64 buf) (u.gpr .x28+BitVec.ofNat 64 out) u)
    (cs : Rej8.Constants s) (cu : Rej8.Constants u)
    (hsp : s.sp=u.sp) (h19 : s.gpr .x19=u.gpr .x19) (h28 : s.gpr .x28=u.gpr .x28)
    (h16 : s.gpr .x16=u.gpr .x16) :
    RelCT isa (fun a b => a=s ∧ b=u) (Impl.MlKem.AArch64.Paired.reject buf out flag w16)
      (fun a b => RejectPostW w16 B (s.gpr .x28+BitVec.ofNat 64 out) flag s a ∧
        RejectPostW w16 B (u.gpr .x28+BitVec.ofNat 64 out) flag u b) := by
  have start : RelCT isa (fun a b => a=s ∧ b=u) (.block (rejectEntry buf out))
      (fun a b => Rej8.EntryW w16 [] 168 B (s.gpr .x19+BitVec.ofNat 64 buf)
        (s.gpr .x28+BitVec.ofNat 64 out) a ∧
        Rej8.EntryW w16 [] 168 B (s.gpr .x19+BitVec.ofNat 64 buf)
        (s.gpr .x28+BitVec.ofNat 64 out) b ∧ a.sp=b.sp ∧ a.gpr .x16=b.gpr .x16) := by
    intro a b tr ur a' b' h ea eb
    rcases h with ⟨ha,hb'⟩
    subst a; subst b
    have ht := rejectEntry_ct buf out s u tr ur a' b' trivial trivial
      (agree_of hsp (by simp)) ea eb
    obtain ⟨ka,ha⟩ := exec_post (rejectEntry_ok s hb ho ps cs) ea
    obtain ⟨kb,hb⟩ := exec_post (rejectEntry_ok u hb ho pu cu) eb
    refine ⟨ht,ha,?_,ka.sp.trans (hsp.trans kb.sp.symm),?_⟩
    · simpa only [h19,h28] using hb
    · rw [ka.get .x16,kb.get .x16,h16]
  have trace : RelCT isa (fun a b => a=s ∧ b=u)
      (Impl.MlKem.AArch64.Paired.reject buf out flag w16) (fun _ _=>True) := by
    refine RelCT.seq start (RelCT.seq (segment_entry_relCT [] 168 B _ _ (by decide) (by decide)) ?_)
    intro a b tr ur a' b' h ea eb
    exact ⟨moveFlag_ct flag a b tr ur a' b' trivial trivial (agree_of h (by simp)) ea eb,trivial⟩
  intro a b tr ur a' b' h ea eb
  rcases h with ⟨ha,hb'⟩
  subst a; subst b
  exact ⟨(trace s u tr ur a' b' ⟨rfl,rfl⟩ ea eb).1,
    exec_post (reject_ok s hb ho hf ps cs) ea,exec_post (reject_ok u hb ho hf pu cu) eb⟩

end VG.Proof.MlKem.AArch64.Paired

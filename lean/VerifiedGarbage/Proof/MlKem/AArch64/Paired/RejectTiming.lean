module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Trace

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

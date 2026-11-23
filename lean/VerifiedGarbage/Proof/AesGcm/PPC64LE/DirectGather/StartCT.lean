module
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.DirectGather.Bind
public import VerifiedGarbage.Proof.Gather.PPC64LE.LoopCT
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CTOne
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Impl.AesGcm.PPC64LE
meta import VerifiedGarbage.Proof.AesGcm.PPC64LE.DirectGather.Bind
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-! # Public accesses of the gather prologue and AAD computation -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.DirectGather
open VG VG.PPC64LE VG.Proof.AesGcm.PPC64LE.Gather
open VG.Impl.AesGcm.PPC64LE (oneEntry oneAad)
open VG.Proof.Gather.PPC64LE (Eq2 TT rel_taint rel_seq)

variable {s d e f t u : State}

theorem entry_rel (pub : gatherPub s d) (p : Args s e) (q : Args d f) :
    RelCT isa (Eq2 e f) (.block (oneEntry 120)) TT := by
  obtain ⟨_,_,_,_,_,_,_,_,sp,_⟩ := pub
  have baseEq : base s=base d := congrArg (· - 1280) sp
  have workEq : work s=work d := congrArg (· + 128) baseEq
  have hsp := p.sp.trans (baseEq.trans q.sp.symm)
  have head {s e : State} (r : Args s e) :
      WP isa (.block [.addSp .r12 0,.load .d .r12 .r12 120]) e fun v =>
        v.gpr .r12=work s ∧ (∀ k,k≠.r12 → v.gpr k=e.gpr k) ∧ Keeps e v := by
    apply oneA_at (by decide) (by decide)
    · rw [r.sp,r.wr]; exact (Covers.right (Covers.refl _)) _ _ (slot_write (j:=3) (by decide))
    · rw [r.sp]; exact r.buf
  rw [oneEntry,List.append_assoc]
  refine RelCT.block_append (rel_seq (rel_taint [] hsp (by simp) (by taint_decide)) (head p) (head q) ?_)
  rintro u v ⟨r,_,ku⟩ ⟨l,_,kv⟩
  exact rel_taint [.r12] (ku.sp.trans (hsp.trans kv.sp.symm)) (by simpa using r.trans (workEq.trans l.symm)) (by taint_decide)

theorem loadArgs_rel (sp : t.sp=u.sp) (work : t.gpr .r31=u.gpr .r31) :
    RelCT isa (Eq2 t u) (.block loadArgs) TT :=
  rel_taint [.r31] sp (by simpa using work) (by taint_decide)

private abbrev AadPublic (s t : State) :=
  OneIP (fun _ st w state D n => DataOk st w state D n) (C s) (work s) (base s) (Rn s)
    (Nn s) (NL s) (Ad s) (s.gpr .r8) (Src s) (s.gpr .r10) t ∧
  t.gpr .r24=Nn s ∧ t.gpr .r25=BitVec.ofNat 64 (NL s)

private theorem aadPublic (h : GatherSplit.Layout s) (p : Args s e) (q : SO1 (work s) (Dst s) e t) :
    AadPublic s t := by
  have hp := bounds h
  have key := p.regs .r3 (by decide) (by decide)
  have round := p.regs .r4 (by decide) (by decide)
  have nonce := p.regs .r5 (by decide) (by decide)
  have nlen := p.regs .r6 (by decide) (by decide)
  have ap := p.regs .r7 (by decide) (by decide)
  have al := p.regs .r8 (by decide) (by decide)
  have dp := p.regs .r9 (by decide) (by decide)
  have dl := p.regs .r10 (by decide) (by decide)
  have en := one_env q (by rw [key]; exact p.read h (r:=cR s) (by simp)) p.workWrite
  rw [p.sp] at en
  have D {r : Region} (mem : r∈[cR s,nR s,aR s,dsR s]++lsR s++[argR s])
      (sep : (stack s).Disjoint r) (fit : r.base.toNat+r.len≤2^64) (lt : r.len<2^64) :
      DataOk (work s+16) (work s) t r.base r.len := by
    have apart := sep.symm.sub_right (work_sub s)
    exact ⟨by rw [q.en.keeps.rd,q.en.keeps.wr]; exact p.read h mem,lt,fit,
      apart.sub_right (Offset.sub_base _ (by decide)),apart.sub_right (Region.sub_prefix (by decide))⟩
  have d := D (r:=dsR s) (by simp) (stack_disjoint h (by simp)) h.base.ods (count_lt h)
  have short : DataOk (work s+16) (work s) t (Src s) (Cnt s) := by
    have le : Cnt s≤Cnt s*16 := by omega
    refine ⟨?_,(s.gpr .r10).isLt,by have fit:=h.base.ods; omega_using [fit,le],
      d.st.sub_left (Region.sub_prefix le),d.w.sub_left (Region.sub_prefix le)⟩
    intro a n ⟨r,hr,cap⟩
    rcases List.mem_singleton.mp hr with rfl
    exact d.rd a n ⟨_,List.mem_singleton_self _,Nat.le_trans cap le⟩
  have b25 : t.gpr .r25=BitVec.ofNat 64 (NL s) := by rw [q.r25,nlen]; simp [NL]
  exact ⟨⟨t.gpr,q.r29.trans key,q.r30,q.r31,by rw [q.r28,round]; simp [Rn],
    by rw [q.r18,nlen]; simp [NL],q.r21.trans ap,q.r22.trans al,q.r27.trans dp,q.r23.trans dl,en,
    D (r:=nR s) (by simp) (stack_disjoint h (by simp)) hp.nonce (s.gpr .r6).isLt,
    D (r:=aR s) (by simp) (stack_disjoint h (by simp)) hp.aad (s.gpr .r8).isLt,short⟩,q.r24.trans nonce,b25⟩

theorem aad_rel [Proof.Gcm.PPC64LE.GhashLaw] (pub : gatherPub s d) (h : GatherSplit.Layout s)
    (g : GatherSplit.Layout d) (p : Args s e) (r : Args d f) (x : SO1 (work s) (Dst s) e t)
    (y : SO1 (work d) (Dst d) f u) : RelCT isa (Eq2 t u) oneAad TT := by
  have left := aadPublic h p x
  have right := aadPublic g r y
  obtain ⟨key,rounds,np,nl,ad,al,dp,dl,sp,_⟩ := pub
  have L := oneLay (bounds h).key (work_fit h) ((stack_disjoint h (r:=cR s) (by simp)).symm.sub_right (work_sub s))
  refine RelCT.mono (oneAad_ctP (sp:=base s) (R:=Rn s) (Np:=Nn s) (n:=NL s) (Ad:=Ad s)
    (A:=s.gpr .r8) (D:=Src s) (Ln:=s.gpr .r10) L dataOk_ok) ?_ (fun _ _ _ => trivial)
  rintro a b ⟨rfl,rfl⟩
  refine ⟨left,?_⟩
  simpa only [AadPublic,C,work,base,Rn,Nn,NL,Ad,Src,sp,key,rounds,np,nl,ad,al,dp,dl] using right

end VG.Proof.AesGcm.PPC64LE.DirectGather

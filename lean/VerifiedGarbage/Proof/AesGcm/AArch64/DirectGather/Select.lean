module

meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Impl.AesGcm.AArch64.DirectGather
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.LeafCT
import VerifiedGarbage.Proof.Framework.EntryBranch
import VerifiedGarbage.Proof.Framework.AArch64.Residue
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Cold
import VerifiedGarbage.Proof.AesGcm.AArch64.Env

/-! The length check reads the second stack argument. It leaves the gather
arguments, ABI and public observations available to either selected path. -/
@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64.DirectGather VG.Proof.AesGcm.AArch64.Gather
open VG.AArch64.Scrub

private abbrev gr := [Reg.x9,.x10,.x11,.x12]

variable {limit : Nat}

private structure View (limit : Nat) (s u : State) : Prop where
  keep : Regs gr s u
  v : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  dit : u.dit = s.dit
  cond : (u.gpr .x10 = 0 ↔ recordWithin limit s)

private theorem guardRead {s : State} (l : Gather.Lay .plain s) :
    InRegions (s.rd ++ s.wr) (s.sp+8#64) 8 := by
  change InRegions _ (stackArgAddr s 1) 8
  rw [l.hA]; exact l.inArg _ (by decide) (by decide) _

private theorem guardView {limit : Nat} (bound : limit=96 ∨ limit=224) (s : State) (l : Gather.Lay .plain s) :
    WP isa (.block (recordGuard limit)) s (View limit s) := by
  obtain ⟨t,u,e,k,r⟩ := recordGuard_ok bound s (guardRead l)
  refine ⟨t,u,e,r,Exec.preservedV e (by rcases bound with rfl | rfl <;> lit_decide),Exec.dit (by rcases bound with rfl | rfl <;> lit_decide) e,?_⟩
  rw [k]
  change s.gpr .x3 = 12 ∧ _ ∧ _ ↔ (s.gpr .x3).toNat = 12 ∧ _ ∧ _
  have h : s.gpr .x3 = 12 ↔ (s.gpr .x3).toNat = 12 :=
    ⟨fun e => by rw [e]; rfl, fun e => BitVec.eq_of_toNat_eq e⟩
  rw [h]; rfl

private theorem View.arg {s u : State} (v : View limit s u) (i : Nat) : stackArg u i = stackArg s i := by
  simp only [stackArg,stackArgAddr,v.keep.mem,v.keep.sp]

private theorem View.abi {s u t : State} (v : View limit s u) (a : abiPreserved u t) : abiPreserved s t :=
  ⟨fun r hr => (a.1 r hr).trans (v.keep.others _ ((by decide : ∀ q ∈ preserved, q ∉ gr) r hr)),
    a.2.1.trans v.keep.sp,fun r hr => (a.2.2 r hr).trans (v.v r hr)⟩

private theorem View.pre {s u : State} (v : View limit s u) (h : gatherPre .plain s) : gatherPre .plain u := by
  simpa only [gatherPre,K,Nn,NL,Ad,AL,Src,Cnt,Dst,L,Tg,gl,kR,nR,aR,dsR,lsR,dR,tgR,argR,stkR,stackArgAddr,
    v.keep.rd,v.keep.wr,v.keep.sp,v.keep.mem,v.arg,v.keep.others _ (by decide : Reg.x0 ∉ gr),
    v.keep.others _ (by decide : Reg.x1 ∉ gr),v.keep.others _ (by decide : Reg.x2 ∉ gr),
    v.keep.others _ (by decide : Reg.x3 ∉ gr),v.keep.others _ (by decide : Reg.x4 ∉ gr),
    v.keep.others _ (by decide : Reg.x5 ∉ gr),v.keep.others _ (by decide : Reg.x6 ∉ gr),
    v.keep.others _ (by decide : Reg.x7 ∉ gr),K,Nn,NL,Ad,AL,Src,Cnt,Dst,L,Tg] using h

private theorem View.post {s u t : State} (v : View limit s u) (h : gatherPost u t) : gatherPost s t := by
  simpa only [gatherPost,pt,K,Nn,NL,Ad,AL,Src,Cnt,Dst,Tg,L,v.keep.mem,v.arg,
    v.keep.others _ (by decide : Reg.x0 ∉ gr),v.keep.others _ (by decide : Reg.x1 ∉ gr),
    v.keep.others _ (by decide : Reg.x2 ∉ gr),v.keep.others _ (by decide : Reg.x3 ∉ gr),
    v.keep.others _ (by decide : Reg.x4 ∉ gr),v.keep.others _ (by decide : Reg.x5 ∉ gr),
    v.keep.others _ (by decide : Reg.x6 ∉ gr),v.keep.others _ (by decide : Reg.x7 ∉ gr)] using h

private theorem View.pub {a b s t : State} (v : View limit a s) (w : View limit b t) (h : gatherPub a b) : gatherPub s t := by
  obtain ⟨q0,q1,q2,q3,q4,q5,q6,q7,qsp,qd,a0,a1,a2,ds⟩ := h
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,v.keep.sp.trans (qsp.trans w.keep.sp.symm),v.dit.trans (qd.trans w.dit.symm),
    (v.arg 0).trans (a0.trans (w.arg 0).symm),(v.arg 1).trans (a1.trans (w.arg 1).symm),
    (v.arg 2).trans (a2.trans (w.arg 2).symm),?_⟩
  · rw [v.keep.others _ (by decide : Reg.x0 ∉ gr),w.keep.others _ (by decide : Reg.x0 ∉ gr),q0]
  · rw [v.keep.others _ (by decide : Reg.x1 ∉ gr),w.keep.others _ (by decide : Reg.x1 ∉ gr),q1]
  · rw [v.keep.others _ (by decide : Reg.x2 ∉ gr),w.keep.others _ (by decide : Reg.x2 ∉ gr),q2]
  · rw [v.keep.others _ (by decide : Reg.x3 ∉ gr),w.keep.others _ (by decide : Reg.x3 ∉ gr),q3]
  · rw [v.keep.others _ (by decide : Reg.x4 ∉ gr),w.keep.others _ (by decide : Reg.x4 ∉ gr),q4]
  · rw [v.keep.others _ (by decide : Reg.x5 ∉ gr),w.keep.others _ (by decide : Reg.x5 ∉ gr),q5]
  · rw [v.keep.others _ (by decide : Reg.x6 ∉ gr),w.keep.others _ (by decide : Reg.x6 ∉ gr),q6]
  · rw [v.keep.others _ (by decide : Reg.x7 ∉ gr),w.keep.others _ (by decide : Reg.x7 ∉ gr),q7]
  · simp only [Cnt,Src,v.keep.others _ (by decide : Reg.x6 ∉ gr),v.keep.others _ (by decide : Reg.x7 ∉ gr),
    v.keep.mem,w.keep.mem]
    exact ds

private theorem View.record {s u : State} (v : View limit s u) (h : recordWithin limit s) : recordWithin limit u := by
  simpa only [recordWithin,NL,AL,L,v.arg,v.keep.others _ (by decide : Reg.x3 ∉ gr),
    v.keep.others _ (by decide : Reg.x5 ∉ gr)] using h

private abbrev afterLoad (limit : Nat) := (recordGuard limit).tail
private abbrev loadState (s : State) := s.write .x .x12 (stackArg s 1)

private theorem guardRun {s u : State} {tr : List Leak} (l : Gather.Lay .plain s)
    (e : execBlock isa (recordGuard limit) s = some (u,tr)) :
    ∃ tt, execBlock isa (afterLoad limit) (loadState s) = some (u,tt) ∧ tr = [.addr (s.sp+8#64)] := by
  change execBlock isa (.ldrSp .x12 8 :: afterLoad limit) s = _ at e
  rw [execBlock_cons_of (exec_ldrSp (by decide) (guardRead l))] at e
  obtain ⟨⟨v,τ⟩,body,h⟩ := Option.map_eq_some_iff.mp e
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj h
  have z := execBlock_trace_nil (M := isa) (b := afterLoad limit) (fun i hi s' => by
    simp only [afterLoad,recordGuard,List.tail_cons,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl) body
  exact ⟨τ,body,by rw [z]; rfl⟩

private theorem View.eval {s u : State} (v : View limit s u) :
    isa.eval (.zero .x .x10) u = some (decide (recordWithin limit s)) := by
  change some ((u.read .x .x10) == 0) = _
  change some (u.gpr .x10 == (0 : Addr)) = _
  congr 1
  by_cases y : recordWithin limit s
  · simp [y,v.cond.mpr y]
  · simp [y]; exact fun e => y (v.cond.mp e)

private theorem guardOutside {limit : Nat} (bound : limit=96 ∨ limit=224) {a b s t : State} {τ υ : List Leak}
    (la : Gather.Lay .plain a) (lb : Gather.Lay .plain b) (outside : Outside 0 a b)
    (pub : gatherPub a b) (unknown : a.unknowns = b.unknowns) (ea : execBlock isa (recordGuard limit) a = some (s,τ))
    (eb : execBlock isa (recordGuard limit) b = some (t,υ)) : Outside 0 s t := by
  obtain ⟨ra,sa,_⟩ := guardRun la ea
  obtain ⟨rb,sb,_⟩ := guardRun lb eb
  have len : stackArg a 1 = stackArg b 1 := pub.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨rd,wr,g,x0,sp,c,n,z,v,d,vec,mem⟩ := outside
  have after : Outside 0 (loadState a) (loadState b) := by
    refine ⟨rd,wr,fun r he => ?_,?_,sp,c,n,z,v,d,vec,mem⟩
    · by_cases same : r = .x12
      · subst r; simp only [loadState,gpr_write_self,len]
      · simpa only [loadState,gpr_write_of_ne _ _ _ same] using g r he
    · simpa only [loadState,gpr_write_of_ne _ _ _ (by decide : Reg.x0 ≠ .x12)] using x0
  exact Residue.noResidue_of_blind (c := (.block (afterLoad limit))) (by rcases bound with rfl | rfl <;> lit_decide)
    (⟨fun _ => True, fun _ _ => True, fun _ _ => True⟩ : Contract isa) 0 _ _ _ _ _ _
    trivial trivial trivial after unknown (.block sa) (.block sb)

private theorem sameRecord {a b : State} (pub : gatherPub a b) : recordWithin limit a ↔ recordWithin limit b := by
  obtain ⟨_,_,_,q3,_,q5,_,_,_,_,_,n,_,_⟩ := pub
  simp only [recordWithin,NL,AL,L,q3,q5,n]

private abbrev fullContract := gatherAArch64 .plain

private theorem branch_correct {limit : Nat} {leaf : Prog isa} (bound : limit=96 ∨ limit=224) (short : VerifiedScrubbed target leaf (boundedRecordContract limit) 0) (other : Prog isa) (h : Verified target other fullContract)
    (s : State) (ps : fullContract.pre s) :
    WP isa (chooseRecord limit leaf other) s fun t => abiPreserved s t ∧ gatherPost s t := by
  refine WP.seq ((guardView bound s (Gather.lay ps.1)).mono ?_)
  intro u v
  apply WP.ite _ v.eval
  · intro r
    exact (show WP isa leaf u _ from short.verified.1 _ ⟨v.pre ps.1,v.record (of_decide_eq_true r)⟩).mono
      fun _ hu => ⟨v.abi hu.1,v.post hu.2⟩
  · intro _
    exact (show WP isa other u _ from h.1 u ⟨v.pre ps.1,trivial⟩).mono fun _ hu => ⟨v.abi hu.1,v.post hu.2⟩

private theorem select_rel {limit : Nat} {leaf : Prog isa} (bound : limit=96 ∨ limit=224) (short : VerifiedScrubbed target leaf (boundedRecordContract limit) 0) {other : Prog isa} (h : Verified target other fullContract) {a b : State}
    (pa : fullContract.pre a) (pb : fullContract.pre b) (pub : gatherPub a b) :
    RelCT isa (Eq2 a b) (chooseRecord limit leaf other) TT := by
  have sp := pub.2.2.2.2.2.2.2.2.1
  refine rel_seq (rel_taint [] sp (by agree_tac []) (by rcases bound with rfl | rfl <;> exact ⟨_,by taint_decide⟩))
    (guardView bound a (Gather.lay pa.1)) (guardView bound b (Gather.lay pb.1)) ?_
  intro u v pu pv
  have eq : decide (recordWithin limit a) = decide (recordWithin limit b) := by simp only [sameRecord pub]
  refine rel_ite pu.eval (eq ▸ pv.eval) ?_ ?_
  · intro take
    have hr := of_decide_eq_true take
    intro x y τ υ x' y' ⟨rfl,rfl⟩ ea eb
    exact ⟨short.verified.2.1 _ _ _ _ _ _ ⟨pu.pre pa.1,pu.record hr⟩
      ⟨pv.pre pb.1,pv.record ((sameRecord pub).mp hr)⟩ (pu.pub pv pub) ea eb,trivial⟩
  · intro _
    intro x y τ υ x' y' ⟨rfl,rfl⟩ ea eb
    exact ⟨h.2.1 _ _ _ _ _ _ ⟨pu.pre pa.1,trivial⟩ ⟨pv.pre pb.1,trivial⟩ (pu.pub pv pub) ea eb,trivial⟩

private theorem branch_noResidue {limit : Nat} {leaf : Prog isa} (bound : limit=96 ∨ limit=224) (short : VerifiedScrubbed target leaf (boundedRecordContract limit) 0) {other : Prog isa} (h : NoResidue other fullContract 0) :
    NoResidue (chooseRecord limit leaf other) fullContract 0 := by
  intro a b τ υ a' b' pa pb pub out unknown ea eb
  cases ea with | seq ga ba =>
   cases eb with | seq gb bb =>
    have la := Gather.lay pa.1
    have lb := Gather.lay pb.1
    obtain ⟨_,_,xa,va⟩ := guardView bound a la
    obtain ⟨_,_,xb,vb⟩ := guardView bound b lb
    obtain ⟨_,rfl⟩ := Exec.det xa ga
    obtain ⟨_,rfl⟩ := Exec.det xb gb
    have ra := Exec.block_eq (T := target) ga
    have rb := Exec.block_eq (T := target) gb
    have ou := guardOutside bound la lb out pub unknown ra rb
    obtain ⟨_,ua,ub⟩ := execBlock_unknowns ra rb
    have un := ua.trans (unknown.trans ub.symm)
    have pu := va.pub vb pub
    have same := sameRecord (limit := limit) pub
    cases ba with
    | iteT yes take =>
      have ok : recordWithin limit a := of_decide_eq_true (Option.some.inj (va.eval.symm.trans yes))
      have y := (same.mp ok)
      cases bb with
      | iteT _ take' =>
        exact short.noResidue _ _ _ _ _ _ ⟨va.pre pa.1,va.record ok⟩
          ⟨vb.pre pb.1,vb.record y⟩ pu ou un take take'
      | iteF no _ => rw [vb.eval,decide_eq_true y] at no; cases no
    | iteF no take =>
      have bad : ¬ recordWithin limit a := of_decide_eq_false (Option.some.inj (va.eval.symm.trans no))
      have n := fun y => bad (same.mpr y)
      cases bb with
      | iteT yes _ => rw [vb.eval,decide_eq_false n] at yes; cases yes
      | iteF _ take' =>
        exact h _ _ _ _ _ _ ⟨va.pre pa.1,trivial⟩ ⟨vb.pre pb.1,trivial⟩ pu ou un take take'

/-- Both branches satisfy the existing gather ABI, CT and residue obligations.
The guard observes only the public record lengths. -/
theorem chooseRecord_scrubbed {limit : Nat} {leaf : Prog isa} (bound : limit=96 ∨ limit=224) (short : VerifiedScrubbed target leaf (boundedRecordContract limit) 0) {other : Prog isa}
    (h : VerifiedScrubbed target other (gatherAArch64 .plain) 0) :
    VerifiedScrubbed target (chooseRecord limit leaf other) (gatherAArch64 .plain) 0 :=
  ⟨⟨branch_correct bound short other h.verified,ct_of (fun _ _ => select_rel bound short h.verified),h.verified.2.2⟩,branch_noResidue bound short h.noResidue⟩

theorem chooseShort_scrubbed {other : Prog isa} (short : VerifiedScrubbed target shortLeaf shortContract 0)
    (h : VerifiedScrubbed target other (gatherAArch64 .plain) 0) :
    VerifiedScrubbed target (chooseShort other) (gatherAArch64 .plain) 0 :=
  chooseRecord_scrubbed (.inl rfl) short h

end VG.Proof.AesGcm.AArch64.DirectGather

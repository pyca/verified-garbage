module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.Guard
import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.Select
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.EntryBranch
import VerifiedGarbage.Proof.Framework.AArch64.Residue
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Proof.AesGcm.AArch64.Contiguous.Guard
import VerifiedGarbage.Proof.AesGcm.ScratchPowers8
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig

/-! The public size tests retain every input to the authenticated-encryption
specification and the two-buffer layout, including the original plaintext. -/

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Guard
open VG VG.AArch64

variable {o t : State} (v : View o t)
include v

theorem View.stackArg (i : Nat) : VG.AArch64.stackArg t i = VG.AArch64.stackArg o i := by
  simp only [VG.AArch64.stackArg,stackArgAddr,v.keep.mem,v.keep.sp]

theorem View.caller (c : Caller o) : Caller t := by
  have key : Gather.kR .plain t = Gather.kR .plain o := by unfold Gather.kR Gather.K; rw [v.keep.others .x0 (by decide)]
  have nonce : Gather.nR t = Gather.nR o := by unfold Gather.nR Gather.Nn Gather.NL; rw [v.keep.others .x2 (by decide),v.keep.others .x3 (by decide)]
  have aad : Gather.aR t = Gather.aR o := by unfold Gather.aR Gather.Ad Gather.AL; rw [v.keep.others .x4 (by decide),v.keep.others .x5 (by decide)]
  have src : srcR t = srcR o := by unfold srcR; rw [v.keep.others .x6 (by decide),v.stackArg]
  have dst : dstR t = dstR o := by unfold dstR; rw [v.keep.others .x7 (by decide),v.stackArg]
  have tag : tagR t = tagR o := by unfold tagR; rw [v.stackArg]
  have args : callerArgs t = callerArgs o := by simp only [callerArgs,stackArgAddr,v.keep.sp]
  have regs : externalRegions t = externalRegions o := by unfold externalRegions; rw [key,nonce,aad,src,dst,tag]
  constructor
  · simpa only [key,nonce,aad,src,args,v.keep.rd,v.keep.wr] using c.read
  · simpa only [dst,tag,v.keep.wr] using c.write
  · simpa only [key,dst] using c.kd
  · simpa only [key,tag] using c.kt
  · simpa only [nonce,dst] using c.nd
  · simpa only [nonce,tag] using c.nt
  · simpa only [aad,dst] using c.ad
  · simpa only [aad,tag] using c.atag
  · simpa only [src,dst,v.keep.others .x6 (by decide),v.keep.others .x7 (by decide)] using c.sd
  · simpa only [src,tag] using c.st
  · simpa only [dst,tag] using c.dt
  · simpa only [dst,args] using c.dstArgs
  · simpa only [regs,v.keep.sp] using c.stack
  · simpa only [regs] using c.nowrap
  · simpa only [v.keep.sp] using c.room
  · simpa only [v.keep.sp] using c.top
  · simpa only [v.keep.others .x1 (by decide)] using c.rounds

theorem View.powers (p : Prepared.Powers o) : Prepared.Powers t := by
  have pow : Prepared.powerR t = Prepared.powerR o := by unfold Prepared.powerR; rw [v.stackArg]
  have dst : dstR t = dstR o := by unfold dstR; rw [v.keep.others .x7 (by decide),v.stackArg]
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [pow,v.keep.rd,v.keep.wr] using p.read
  · simpa only [pow,dst] using p.dst
  · simpa only [pow,v.keep.sp] using p.stack
  · simpa only [v.keep.mem,v.stackArg,v.keep.others .x0 (by decide)] using p.repr

theorem View.post {z : State} (h : result t z) : result o z := by
  simpa only [result,v.keep.mem,v.stackArg,v.keep.others .x0 (by decide),v.keep.others .x1 (by decide),v.keep.others .x2 (by decide),v.keep.others .x3 (by decide),v.keep.others .x4 (by decide),v.keep.others .x5 (by decide),v.keep.others .x6 (by decide),v.keep.others .x7 (by decide)] using h

theorem View.standard_iff : standard t ↔ standard o := by
  simp only [standard,v.keep.others .x3 (by decide),v.keep.others .x5 (by decide)]

theorem View.abi {z : State} (h : abiPreserved t z) : abiPreserved o z :=
  ⟨fun r hr => (h.1 r hr).trans (v.keep.others _ ((by decide : ∀ r ∈ preserved, r ∉ temps) _ hr)),
    h.2.1.trans v.keep.sp,fun r hr => (h.2.2 r hr).trans (v.vec r hr)⟩

theorem View.pub {b u : State} (w : View b u) (pub : onePub 3 o b ∧ o.dit=b.dit) :
    onePub 3 t u ∧ t.dit=u.dit := by
  obtain ⟨⟨g0,g1,g2,g3,g4,g5,g6,g7,sp,stk⟩,dit⟩ := pub
  have eq (r : Reg) (h : r ∉ temps) (p : o.gpr r=b.gpr r) :=
    (v.keep.others _ h).trans (p.trans (w.keep.others _ h).symm)
  exact ⟨⟨eq _ (by decide) g0,eq _ (by decide) g1,eq _ (by decide) g2,eq _ (by decide) g3,eq _ (by decide) g4,eq _ (by decide) g5,eq _ (by decide) g6,eq _ (by decide) g7,
    v.keep.sp.trans (sp.trans w.keep.sp.symm),fun i hi => (v.stackArg i).trans ((stk i hi).trans (w.stackArg i).symm)⟩,
    v.dit.trans (dit.trans w.dit.symm)⟩

end VG.Proof.AesGcm.AArch64.Contiguous.Guard

/-! ## Composition through public branches that preserve the contiguous inputs. -/

namespace VG.Proof.AesGcm.AArch64.Contiguous.Guard
open VG VG.AArch64
open VG.AArch64.Scrub

abbrev Checked (p : State → Prop) (code : Prog isa) :=
  (∃ s, (leafContract p).pre s) → VerifiedScrubbed target code (leafContract p) 0

structure Branch (p l r : State → Prop) (code : List Instr) (cond : Cond) where
  take : State → Bool
  run : ∀ s, (leafContract p).pre s → WP isa (.block code) s fun t =>
    View s t ∧ isa.eval cond t=some (take s) ∧ (take s=true → l t) ∧ (take s=false → r t)
  same : ∀ {s t}, (leafContract p).pre s → (leafContract p).pre t → (leafContract p).pub s t → take s=take t
  trace : ∀ {s t}, (leafContract p).pre s → (leafContract p).pre t → (leafContract p).pub s t →
    RelCT isa (Eq2 s t) (.block code) TT
  residue : NoResidue (.block code) (leafContract p) 0

theorem Branch.checked {p l r : State → Prop} {code : List Instr} {cond : Cond}
    (g : Branch p l r code cond) {yes no : Prog isa} (left : Checked l yes) (right : Checked r no) :
    Checked p (.seq (.block code) (.ite cond yes no)) := by
  intro sat
  refine ⟨⟨?_,ct_of ?_,sat⟩,?_,fun ty _ h => by cases ty <;> cases h⟩
  · intro s ps
    refine WP.seq ((g.run s ps).mono ?_)
    intro t ⟨v,eval,hl,hr⟩
    apply WP.ite _ eval
    · intro ok
      have a : (leafContract l).pre t := ⟨v.caller ps.1,v.powers ps.2.1,hl ok⟩
      exact (show WP isa yes t _ from (left ⟨_,a⟩).verified.1 t a).mono fun _ h => ⟨v.abi h.1,v.post h.2⟩
    · intro ok
      have a : (leafContract r).pre t := ⟨v.caller ps.1,v.powers ps.2.1,hr ok⟩
      exact (show WP isa no t _ from (right ⟨_,a⟩).verified.1 t a).mono fun _ h => ⟨v.abi h.1,v.post h.2⟩
  · intro a b pa pb pub
    refine rel_seq (g.trace pa pb pub) (g.run a pa) (g.run b pb) ?_
    intro t u ⟨v,ev,al,ar⟩ ⟨w,ew,bl,br⟩
    have both := g.same pa pb pub
    refine rel_ite ev (both ▸ ew) ?_ ?_
    · intro ok
      have ha : (leafContract l).pre t := ⟨v.caller pa.1,v.powers pa.2.1,al ok⟩
      have hb : (leafContract l).pre u := ⟨w.caller pb.1,w.powers pb.2.1,bl (both ▸ ok)⟩
      rintro _ _ _ _ _ _ ⟨rfl,rfl⟩ ea eb
      exact ⟨(left ⟨_,ha⟩).verified.2.1 _ _ _ _ _ _ ha hb (v.pub w pub) ea eb,trivial⟩
    · intro ok
      have ha : (leafContract r).pre t := ⟨v.caller pa.1,v.powers pa.2.1,ar ok⟩
      have hb : (leafContract r).pre u := ⟨w.caller pb.1,w.powers pb.2.1,br (both ▸ ok)⟩
      rintro _ _ _ _ _ _ ⟨rfl,rfl⟩ ea eb
      exact ⟨(right ⟨_,ha⟩).verified.2.1 _ _ _ _ _ _ ha hb (v.pub w pub) ea eb,trivial⟩
  · intro a b τ υ x y pa pb pub out unknown ea eb
    cases ea with | seq ga ba =>
     cases eb with | seq gb bb =>
      obtain ⟨_,_,xa,v,ev,al,ar⟩ := g.run a pa
      obtain ⟨_,_,xb,w,ew,bl,br⟩ := g.run b pb
      obtain ⟨_,rfl⟩ := Exec.det xa ga
      obtain ⟨_,rfl⟩ := Exec.det xb gb
      have pu := v.pub w pub
      have ou := g.residue _ _ _ _ _ _ pa pb pub out unknown ga gb
      obtain ⟨_,ua,ub⟩ := execBlock_unknowns (Exec.block_eq (T := target) ga) (Exec.block_eq (T := target) gb)
      have un := ua.trans (unknown.trans ub.symm)
      have same := g.same pa pb pub
      cases ba with
      | iteT hit go =>
        have ok := Option.some.inj (ev.symm.trans hit)
        cases bb with
        | iteT _ go' =>
          have ha : (leafContract l).pre _ := ⟨v.caller pa.1,v.powers pa.2.1,al ok⟩
          have hb : (leafContract l).pre _ := ⟨w.caller pb.1,w.powers pb.2.1,bl (same ▸ ok)⟩
          exact (left ⟨_,ha⟩).noResidue _ _ _ _ _ _ ha hb pu ou un go go'
        | iteF miss _ => rw [ew,← same,ok] at miss; cases miss
      | iteF miss go =>
        have ok := Option.some.inj (ev.symm.trans miss)
        cases bb with
        | iteT hit _ => rw [ew,← same,ok] at hit; cases hit
        | iteF _ go' =>
          have ha : (leafContract r).pre _ := ⟨v.caller pa.1,v.powers pa.2.1,ar ok⟩
          have hb : (leafContract r).pre _ := ⟨w.caller pb.1,w.powers pb.2.1,br (same ▸ ok)⟩
          exact (right ⟨_,ha⟩).noResidue _ _ _ _ _ _ ha hb pu ou un go go'

end VG.Proof.AesGcm.AArch64.Contiguous.Guard

/-! ## A single sealed, scrubbed path for every record length and CPU specialization. -/

namespace VG.Proof.AesGcm.AArch64.Contiguous.Guard
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64.Contiguous
open VG.Impl.Scrub.AArch64 (scrubAll)
open VG.Impl.AesGcm.AArch64.Fn (own)

abbrev any (_ : State) : Prop := True
abbrev intermediate (s : State) : Prop := standard s ∧ s.gpr .x10 = stackArg s 0

instance (s : State) : Decidable (standard s) := inferInstanceAs (Decidable (_ ∧ _))

private def nonceBranch (p : State → Prop) (accept : ∀ {s}, standard s → p s) :
    Branch any p any standardGuard (.zero .x .x10) where
  take s := decide (standard s)
  run s _ := (standard_ok s).mono fun t ⟨v,test⟩ => by
    refine ⟨v,?_,fun h => accept (v.standard_iff.mpr (of_decide_eq_true h)),fun _ => trivial⟩
    change some (t.gpr .x10 == (0 : Addr)) = _
    by_cases yes : standard s
    · simp [yes,test.mpr yes]
    · simp [yes]; exact fun h => yes (test.mp h)
  same := by
    intro a b _ _ pub
    obtain ⟨⟨_,_,_,q3,_,q5,_,_,_,_⟩,_⟩ := pub
    have eq : standard a ↔ standard b := by simp only [standard,q3,q5]
    by_cases h : standard a
    · rw [decide_eq_true h,decide_eq_true (eq.mp h)]
    · rw [decide_eq_false h,decide_eq_false (fun e => h (eq.mpr e))]
  trace := by
    intro a b _ _ pub
    exact rel_taint [] pub.1.2.2.2.2.2.2.2.2.1 (by agree_tac []) ⟨_,by taint_decide⟩
  residue := Residue.noResidue_of_blind (by decide +kernel) _ 0

private theorem limit_eval {n : Nat} {s t : State} (load : s.gpr .x10=stackArg s 0)
    (cond : t.gpr .x11 ≠ 0 ↔ (s.gpr .x10).toNat<n) :
    isa.eval (.nonzero .x .x11) t = some (decide ((stackArg s 0).toNat<n)) := by
  rw [load] at cond
  change some (!(t.gpr .x11 == (0 : Addr))) = _
  by_cases ok : (stackArg s 0).toNat<n
  · simp [ok]; exact cond.mpr ok
  · have z : t.gpr .x11=0 := by by_contra hn; exact ok (cond.mp hn)
    simp [ok,z]

private def mediumBranch (n : Nat) (bound : n=768 ∨ n=4096) :
    Branch intermediate (prepared false) (prepared true) (limitCode n) (.nonzero .x .x11) where
  take s := decide ((stackArg s 0).toNat<n)
  run s h := (limit_ok (.inr bound) s).mono fun t ⟨v,_,test⟩ => by
    refine ⟨v,limit_eval h.2.2.2 test,fun _ => ⟨v.standard_iff.mpr h.2.2.1,fun e => Bool.noConfusion e⟩,?_⟩
    intro miss
    have big := of_decide_eq_false miss
    exact ⟨v.standard_iff.mpr h.2.2.1,fun _ => by rw [v.stackArg]; rcases bound with rfl|rfl <;> omega⟩
  same := by intro a b _ _ p; rw [p.1.2.2.2.2.2.2.2.2.2 0 (by decide)]
  trace := by
    intro a b _ _ pub
    rcases bound with rfl | rfl <;> exact rel_taint [] pub.1.2.2.2.2.2.2.2.2.1 (by agree_tac []) ⟨_,by taint_decide⟩
  residue := Residue.noResidue_of_blind (by rcases bound with rfl|rfl <;> decide +kernel) _ 0

private abbrev firstCode : List Instr := .ldrSp .x10 0 :: limitCode 97
private abbrev loaded (s : State) := s.write .x .x10 (stackArg s 0)

private theorem loadRun {s : State} (c : Caller s) :
    exec (.ldrSp .x10 0) s = some (loaded s) := by
  apply exec_ldrSp (by decide)
  exact c.read _ _ ⟨callerArgs s,by simp,DirectGather.stackArg_contains s 0 (by decide)⟩

private theorem loadView (s : State) : View s (loaded s) := by
  refine ⟨⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩,fun _ _ => rfl,rfl⟩
  exact gpr_write_of_ne _ _ _ (fun h => hr (h ▸ (by decide : Reg.x10 ∈ temps)))

private theorem firstRun {s : State} (c : Caller s) :
    WP isa (.block firstCode) s fun t => View s t ∧ t.gpr .x10=stackArg s 0 ∧
      (t.gpr .x11 ≠ 0 ↔ (stackArg s 0).toNat<97) := by
  obtain ⟨τ,t,exec,vt,x10,hit⟩ := limit_ok (.inl rfl) (loaded s)
  have full : WP isa (.block firstCode) s fun u => u=t := by
    refine ⟨[.addr (s.sp+0)]++τ,t,Exec.block ?_,rfl⟩
    rw [execBlock_cons_of (loadRun c),Exec.block_eq (T := target) exec]; rfl
  refine full.mono fun u e => e ▸ ?_
  have v := loadView s
  have keep : View s t := ⟨v.keep.trans vt.keep,fun r hr => (vt.vec r hr).trans (v.vec r hr),vt.dit.trans v.dit⟩
  exact ⟨keep,x10.trans (gpr_write_self ..),by rwa [show (loaded s).gpr .x10=stackArg s 0 from gpr_write_self ..] at hit⟩

private theorem firstOutside : NoResidue (.block firstCode) (leafContract standard) 0 := by
  intro a b τ υ s t pa pb pub out un ea eb
  have ra := Exec.block_eq (T := target) ea
  have rb := Exec.block_eq (T := target) eb
  rw [execBlock_cons_of (loadRun pa.1)] at ra
  rw [execBlock_cons_of (loadRun pb.1)] at rb
  obtain ⟨⟨_,_⟩,ha,he⟩ := Option.map_eq_some_iff.mp ra
  obtain ⟨⟨_,_⟩,hb,hf⟩ := Option.map_eq_some_iff.mp rb
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj hf
  have len := pub.1.2.2.2.2.2.2.2.2.2 0 (by decide)
  obtain ⟨rd,wr,rg,x0,sp,c,n,z,v,d,vec,mem⟩ := out
  have eq : Outside 0 (loaded a) (loaded b) := by
    refine ⟨rd,wr,fun r h => ?_,?_,sp,c,n,z,v,d,vec,mem⟩
    · by_cases hr : r=.x10
      · subst r; simp only [loaded,gpr_write_self,len]
      · simpa only [loaded,gpr_write_of_ne _ _ _ hr] using rg r h
    · simpa only [loaded,gpr_write_of_ne _ _ _ (by decide : Reg.x0 ≠ .x10)] using x0
  exact Residue.noResidue_of_blind (c := .block (limitCode 97)) (by decide +kernel)
    (⟨fun _ => True,fun _ _ => True,fun _ _ => True,none⟩ : Contract isa) 0 _ _ _ _ _ _ trivial trivial trivial
    eq un (.block ha) (.block hb)

private def shortBranch (p : State → Prop) (accept : ∀ {s}, intermediate s → p s) : Branch standard short p firstCode (.nonzero .x .x11) where
  take s := decide ((stackArg s 0).toNat<97)
  run s h := (firstRun h.1).mono fun t ⟨v,x10,hit⟩ => by
    have test := @limit_eval 97 (loaded s) t (by exact gpr_write_self ..)
      (by simpa only [loaded,gpr_write_self,BitVec.setWidth_eq] using hit)
    refine ⟨v,test,?_,fun _ => accept ⟨v.standard_iff.mpr h.2.2,x10.trans (v.stackArg 0).symm⟩⟩
    intro yes
    have sm := of_decide_eq_true yes
    exact ⟨v.standard_iff.mpr h.2.2,by rw [v.stackArg]; omega⟩
  same := by intro a b _ _ p; rw [p.1.2.2.2.2.2.2.2.2.2 0 (by decide)]
  trace := by
    intro a b _ _ pub
    exact rel_taint [] pub.1.2.2.2.2.2.2.2.2.1 (by agree_tac []) ⟨_,by taint_decide⟩
  residue := firstOutside

theorem selected {v : GcmImpl} {g : GhashWithImpl} (facts : BackendFacts v g) : Checked any (select v.calls g.fn) := by
  by_cases portable : (!v.calls.pmull) = true
  · simp only [select,portable,ite_true]
    exact generalLeaf facts
  · let n := if v.calls.stitch then 768 else 4096
    have hn : n=768 ∨ n=4096 := by cases h : v.calls.stitch <;> simp [n,h]
    simp only [select,portable]
    exact (nonceBranch standard id).checked ((shortBranch intermediate id).checked (shortLeaf facts.hash)
      ((mediumBranch n hn).checked (preparedLeaf facts false) (preparedLeaf facts true))) (generalLeaf facts)


end VG.Proof.AesGcm.AArch64.Contiguous.Guard

/-! ## Nonempty caller states for both layouts. The identical case reads its
plaintext through the writable region alone. -/

namespace VG.Proof.AesGcm.AArch64.Contiguous
open VG VG.AArch64 VG.Impl.AesGcm.AArch64.Contiguous

def exampleState (same : Bool) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 10 | .x2 => 0x2000 | .x3 => 12 | .x4 => 0x3000
    | .x5 => 5 | .x6 => 0x4000 | .x7 => if same then 0x4000 else 0x5000 | _ => 0
  sp := 0x9000
  mem a := if a=0x9000 then 16 else if a=0x9009 then 0x60 else if a=0x9011 then 0x70 else 0
  rd := [⟨0x1000,256⟩,⟨0x2000,12⟩,⟨0x3000,5⟩] ++ (if same then [] else [⟨0x4000,16⟩]) ++
    [⟨0x7000,128⟩,⟨0x9000,24⟩]
  wr := [⟨if same then 0x4000 else 0x5000,16⟩,⟨0x6000,16⟩]

private theorem args (same : Bool) : stackArg (exampleState same) 0=16 ∧
    stackArg (exampleState same) 1=0x6000 ∧ stackArg (exampleState same) 2=0x7000 := by
  cases same <;> decide

private theorem caller (same : Bool) : Caller (exampleState same) := by
  cases same <;> constructor <;> first
    | exact Covers.of_mem (by simp only [List.forall_mem_cons,List.not_mem_nil,forall_false,implies_true,and_true]; decide)
    | exact Covers.refl _
    | exact Or.inr rfl
    | apply Or.inl; exact Region.disjoint_of_sep (by decide)
    | exact Region.disjoint_of_sep (by decide)
    | simp only [externalRegions,List.forall_mem_cons,List.not_mem_nil,forall_false,implies_true,and_true]
      repeat' apply And.intro
      all_goals first | exact Region.disjoint_of_sep (by decide) | decide
    | decide

theorem examplePowers (same : Bool) : Prepared.Powers (exampleState same) := by
  constructor
  · apply Covers.of_mem
    simp only [List.mem_singleton,forall_eq,Prepared.powerR,(args same).2.2]
    cases same <;> decide
  · cases same <;> exact Region.disjoint_of_sep (by decide)
  · cases same <;> exact Region.disjoint_of_sep (by decide)
  · apply Proof.AesGcm.powers8Repr_of_zeroMem (by cases same <;> decide)
    intro i hi
    rw [(args same).2.2]
    change (if 0x7000#64+BitVec.ofNat 64 i=0x9000 then 16 else
      if 0x7000#64+BitVec.ofNat 64 i=0x9009 then 0x60 else if 0x7000#64+BitVec.ofNat 64 i=0x9011 then 0x70 else 0)=0
    have lt : (0x7000#64+BitVec.ofNat 64 i).toNat<0x9000 := by
      simp only [BitVec.toNat_add,BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
      rw [Nat.mod_eq_of_lt (by omega : i<18446744073709551616)]
      change (0x7000+i)%2^64 < 0x9000
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    split <;> rename_i h
    · rw [h] at lt; contradiction
    · split <;> rename_i h'
      · rw [h'] at lt; contradiction
      · split <;> rename_i h''
        · rw [h''] at lt; contradiction
        · rfl

theorem bothLayouts (same : Bool) : ∃ s, (leafContract Guard.any).pre s ∧
    (stackArg s 0).toNat=16 ∧ (s.gpr .x6 == s.gpr .x7)=same := by
  refine ⟨exampleState same,⟨caller same,examplePowers same,trivial⟩,congrArg BitVec.toNat (args same).1,?_⟩
  cases same <;> decide

theorem verified {v : GcmImpl} {g : GhashWithImpl} (facts : BackendFacts v g) :
    VerifiedScrubbed target (select v.calls g.fn) (leafContract Guard.any) 0 := by
  obtain ⟨s,p,_⟩ := bothLayouts true
  exact Guard.selected facts ⟨s,p⟩

end VG.Proof.AesGcm.AArch64.Contiguous

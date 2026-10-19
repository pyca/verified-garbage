module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.BeginTiming
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Finish
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FinishTiming
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlKem.AArch64.Shared

/-! # Paired matrix sampling has public-seed-dependent leakage only -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Impl.MlKem.AArch64

theorem pairCode_relCT {w16 : Bool} {s u : State} {p seed outA outB table : Addr} {sb ss a b k oa ob : Nat}
    (hss : ss<65536) (hsb : sb+32≤32768) (h8 : sb%8=0) (hoa : oa<65536) (hob : ob<65536)
    (ps : BeginInput sb ss oa ob p seed outA outB table s) (pu : BeginInput sb ss oa ob p seed outA outB table u)
    (sp : s.sp=u.sp) (base : s.gpr .x28=u.gpr .x28)
    (seedA : seedState s.mem seed a k=seedState u.mem seed a k)
    (seedB : seedState s.mem seed b k=seedState u.mem seed b k) :
    RelCT isa (fun t v=>t=s ∧ v=u) (.seq (beginCode sb ss a b k oa ob w16) (finishCode w16)) (fun _ _=>True) := by
  let R := fun t v : State=>BeginPostW w16 (seedState s.mem seed a k) (seedState s.mem seed b k) p outA outB table s t ∧
    BeginPostW w16 (seedState u.mem seed a k) (seedState u.mem seed b k) p outA outB table u v ∧
    t.syms=s.syms ∧ v.syms=u.syms
  have start : RelCT isa (fun t v=>t=s ∧ v=u) (beginCode sb ss a b k oa ob w16) R := by
    intro t v tr ur t' v' h et ev
    rcases h with ⟨ht,hv⟩; subst t; subst v
    have hh := begin_relCT hss hsb h8 hoa hob ps pu sp base seedA seedB s u tr ur t' v' ⟨rfl,rfl⟩ et ev
    exact ⟨hh.1,hh.2.1,hh.2.2,Exec.syms et,Exec.syms ev⟩
  refine RelCT.seq start ?_
  intro t v tr ur t' v' h et ev
  exact finish_relCT h.1.progress (by rw [seedA,seedB]; exact h.2.1.progress)
    (by rw [h.2.2.1]; exact ps.symbol) (by rw [h.2.2.2]; exact pu.symbol)
    h.1.flag (by rw [seedA,seedB]; exact h.2.1.flag)
    (h.1.keep.sp.trans (sp.trans h.2.1.keep.sp.symm)) t v tr ur t' v' ⟨rfl,rfl⟩ et ev

theorem block_split {l r : List Instr} {s t : State} {tr : List Leak}
    (h : Exec isa (.block (l++r)) s tr t) : Exec isa (.seq (.block l) (.block r)) s tr t := by
  rw [Exec.block_iff,execBlock_append] at h
  obtain ⟨⟨u,ta⟩,ha,hb⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨v,tb⟩,hr,he⟩ := Option.map_eq_some_iff.mp hb
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl,rfl⟩ := he
  exact .seq (.block ha) (.block hr)

theorem seq_parts {a b : Prog isa} {s t : State} {tr : List Leak}
    (h : Exec isa (.seq a b) s tr t) :
    ∃u ta tb,tr=ta++tb ∧ Exec isa a s ta u ∧ Exec isa b u tb t := by
  cases h with
  | seq ha hb => exact ⟨_,_,_,rfl,ha,hb⟩

theorem pair_exec {w16 : Bool} {L : KemLay} {kg : Bool} {a : Nat} {s t : State} {tr : List Leak}
    (h : Exec isa (Impl.MlKem.AArch64.Paired.pair L kg a w16) s tr t) :
    Exec isa (.seq (beginCode (if kg then KG.SB else KEM.SB) (if kg then KG.SS else KEM.SS)
      a (a+1) L.k ((if kg then KG.AH else KEM.AH)+1024*a)
      ((if kg then KG.AH else KEM.AH)+1024*(a+1)) w16) (finishCode w16)) s tr t := by
  simp only [Impl.MlKem.AArch64.Paired.pair,seqs] at h
  obtain ⟨_,_,_,rfl,ei,h⟩ := seq_parts h
  obtain ⟨_,_,_,rfl,es,h⟩ := seq_parts h
  obtain ⟨_,_,_,rfl,ec,h⟩ := seq_parts h
  obtain ⟨_,_,_,rfl,ea,h⟩ := seq_parts h
  obtain ⟨_,_,_,rfl,eca,h⟩ := seq_parts h
  obtain ⟨_,_,_,rfl,eb,h⟩ := seq_parts h
  obtain ⟨_,_,_,rfl,ecb,h⟩ := seq_parts h
  obtain ⟨_,_,_,rfl,ex,er⟩ := seq_parts h
  have split := block_split (l:=[.str .x .x3 .x19 1696,.str .x .x4 .x19 1704])
    (r:=[.logic .and .x .x6 .x22 .x23]) ecb
  obtain ⟨_,_,_,rfl,ecbb,eand⟩ := seq_parts split
  have ee := Exec.seq (Exec.seq ei (Exec.seq es (Exec.seq ec
    (Exec.seq ea (Exec.seq eca (Exec.seq eb (Exec.seq ecbb eand))))))) (Exec.seq ex er)
  simpa only [beginCode,initialCode,finishCode,seqs,List.append_assoc] using ee

theorem pair_relCT {w16 : Bool} {s u : State} {L : KemLay} {kg : Bool} {a : Nat}
    {p seed outA outB table : Addr}
    (hss : (if kg then KG.SS else KEM.SS)<65536)
    (hsb : (if kg then KG.SB else KEM.SB)+32≤32768)
    (h8 : (if kg then KG.SB else KEM.SB)%8=0)
    (hoa : (if kg then KG.AH else KEM.AH)+1024*a<65536)
    (hob : (if kg then KG.AH else KEM.AH)+1024*(a+1)<65536)
    (ps : BeginInput (if kg then KG.SB else KEM.SB) (if kg then KG.SS else KEM.SS)
      ((if kg then KG.AH else KEM.AH)+1024*a) ((if kg then KG.AH else KEM.AH)+1024*(a+1)) p seed outA outB table s)
    (pu : BeginInput (if kg then KG.SB else KEM.SB) (if kg then KG.SS else KEM.SS)
      ((if kg then KG.AH else KEM.AH)+1024*a) ((if kg then KG.AH else KEM.AH)+1024*(a+1)) p seed outA outB table u)
    (sp : s.sp=u.sp) (base : s.gpr .x28=u.gpr .x28)
    (seedA : seedState s.mem seed a L.k=seedState u.mem seed a L.k)
    (seedB : seedState s.mem seed (a+1) L.k=seedState u.mem seed (a+1) L.k) :
    RelCT isa (fun t v=>t=s ∧ v=u) (Impl.MlKem.AArch64.Paired.pair L kg a w16) (fun _ _=>True) := by
  intro t v tr ur t' v' h et ev
  exact pairCode_relCT hss hsb h8 hoa hob ps pu sp base seedA seedB t v tr ur t' v' h
    (pair_exec et) (pair_exec ev)

end VG.Proof.MlKem.AArch64.Paired

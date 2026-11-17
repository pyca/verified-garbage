module

public import VerifiedGarbage.Proof.Mont.X86_64.Csub
import VerifiedGarbage.Proof.Mont.X86_64.Chain
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Impl.Weierstrass.X86_64.Forward
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-! ### `Weierstrass.X86_64.Forward`, which this module and modules that import it used -/

section

/-! Forwarding changes memory reads to register reads with identical state results. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.Forward
open VG VG.X86_64 VG.Impl.Weierstrass.X86_64.Forward

def Valid (cs : Cache) (s : State) : Prop :=
  ∀ c∈cs,s.load64 (s.gpr .rdi+BitVec.ofInt 64 c.1)=some (s.gpr c.2)

theorem lookup_valid {cs : Cache} {s : State} (h : Valid cs s) {d : Int} {r : Reg}
    (he : lookup d cs=some r) : s.load64 (s.gpr .rdi+BitVec.ofInt 64 d)=some (s.gpr r) := by
  induction cs with
  | nil => cases he
  | cons c cs ih =>
    obtain ⟨o,q⟩ := c
    simp only [lookup] at he
    split at he
    · rename_i hd
      cases he
      subst o
      exact h (d,r) (List.mem_cons_self ..)
    · exact ih (fun c hc => h c (List.mem_cons_of_mem _ hc)) he

private theorem one_frame {i : Instr} {d : Reg} {s t : State}
    (hd : i.dst=some d) (he : exec i s=some t) :
    t.rd=s.rd ∧ t.wr=s.wr ∧ t.mem=s.mem ∧ ∀ r,r≠d → t.gpr r=s.gpr r := by
  have hd' : Taint.dstOf i=some d := by
    cases i <;> simp only [reduceInstrDst,Option.some.injEq,reduceCtorEq] at hd
    all_goals subst d
    all_goals first | rfl | cases he
  exact Taint.exec_nonstore hd' he

theorem writes_frame {i : Instr} {rs : List Reg} {s t : State}
    (hw : writes i=some rs) (he : exec i s=some t) :
    t.rd=s.rd ∧ t.wr=s.wr ∧ t.mem=s.mem ∧ ∀ r,r∉rs → t.gpr r=s.gpr r := by
  cases i <;> simp only [writes,reduceInstrDst,Option.map_some,Option.map_none,
    Option.some.injEq,reduceCtorEq] at hw
  all_goals subst rs
  all_goals first
    | exact ⟨(one_frame rfl he).1,(one_frame rfl he).2.1,(one_frame rfl he).2.2.1,
        fun r hr => (one_frame rfl he).2.2.2 r (by simpa only [List.mem_singleton] using hr)⟩
    | skip
  case mul q =>
    cases he
    refine ⟨rfl,rfl,rfl,fun r hr => ?_⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    exact Taint.execMul_gpr q s hr.1 hr.2
  case mulx hi lo src =>
    simp only [exec,execMulx] at he
    split at he
    · cases he
    · simp only [Option.map_eq_some_iff] at he
      obtain ⟨_,_,rfl⟩ := he
      refine ⟨rfl,rfl,rfl,fun r hr => ?_⟩
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
      simp only [RegUpd.gpr_setReg,hr.1,hr.2,ite_false]

theorem next_valid {cs : Cache} {i : Instr} {s t : State}
    (hc : Valid cs s) (he : exec i s=some t) : Valid (next cs i) t := by
  unfold next
  split
  · intro c hc; cases hc
  · rename_i rs hw
    split
    · intro c hc; cases hc
    · rename_i hrdi
      have hf := writes_frame hw he
      have hb : t.gpr .rdi=s.gpr .rdi := hf.2.2.2 _ (by simpa using hrdi)
      intro c hcs
      have hcs := List.mem_filter.mp hcs
      have hr : t.gpr c.2=s.gpr c.2 := hf.2.2.2 _ (by simpa using hcs.2)
      simp only [State.load64,hb,hf.1,hf.2.1,hf.2.2.1,hr]
      exact hc c hcs.1

theorem instruction_eq {cs : Cache} {i : Instr} {s : State} (hc : Valid cs s) :
    exec (instruction cs i) s=exec i s := by
  cases i <;> simp only [instruction]
  rename_i d src
  cases src <;> simp only
  rename_i m
  split
  · rename_i hm
    split
    · rename_i r hr
      have hv := lookup_valid hc hr
      simp only [exec,readSrc,State.ea,hm.1,hm.2,hv,Option.map_some]
    · rfl
  · rfl

/-- Functional correctness transfers to forwarded code. Its access trace is
shorter, so callers establish constant time separately for the generated code. -/
theorem block_wp {cs : Cache} {is : List Instr} {s : State} {Q : State → Prop}
    (hc : Valid cs s) (h : WP isa (.block is) s Q) : WP isa (.block (block cs is)) s Q := by
  induction is generalizing cs s with
  | nil => exact h
  | cons i is ih =>
    obtain ⟨t,he,ht⟩ := WP.block_cons_iff.mp h
    apply WP.block_cons_iff.mpr
    exact ⟨t,(instruction_eq hc).trans he,ih (next_valid hc he) ht⟩

end VG.Proof.Weierstrass.X86_64.Forward

end

end

/-! Consecutive output stores establish the next field operation's register cache. -/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64.Forward
open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64.Forward
open VG.Proof.Mont VG.Proof.Mont.X86_64

theorem valid_of_words {s : State} {base : Addr} {size o : Nat} {rs : List Reg}
    (hs : Scr s base size) (ho : o+8*rs.length≤size)
    (he : wordsVal s.mem base o rs.length=regsVal s rs) : Valid (ofStores rs o) s := by
  induction rs generalizing o with
  | nil => intro c hc; cases hc
  | cons r rs ih =>
    simp only [List.length_cons,wordsVal,regsVal] at he
    have hm := (word s.mem base o).isLt
    have hr := (s.gpr r).isLt
    have hw : word s.mem base o=s.gpr r := BitVec.eq_of_toNat_eq (by omega_using [he])
    have ht : wordsVal s.mem base (o+8) rs.length=regsVal s rs := by omega_using [he]
    have hl := load_sc hs (d := o) (by simp only [List.length_cons] at ho; omega_using [ho])
    rw [hw] at hl
    intro c hc
    simp only [ofStores,List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact hl
    · exact ih (by simp only [List.length_cons] at ho; omega_using [ho]) ht c hc

theorem stores_valid {s : State} {base : Addr} {size o : Nat} {rs : List Reg}
    (hs : Scr s base size) (ho : o+8*rs.length≤size) (hd : rs.Nodup) :
    WP isa (.block (stores rs o)) s fun t => Valid (ofStores rs o) t ∧ KeepRegs [] s t := by
  apply WP.mono (stores_ok rs hs ho hd)
  intro t ⟨he,hk,_⟩
  refine ⟨valid_of_words (hs.of_keepRegs hk (by simp)) ho ?_,hk⟩
  exact he.trans (regsVal_congr (fun r _ => hk.gpr r (by simp))).symm

private theorem stores_scr_back {rs : List Reg} {o size : Nat} {s : State} {base : Addr}
    (h : WP isa (.block (stores rs o)) s fun t => Scr t base size) : Scr s base size := by
  induction rs generalizing o s with
  | nil => exact WP.block_nil_iff.mp h
  | cons r rs ih =>
    obtain ⟨t,he,ht⟩ := WP.block_cons_iff.mp h
    have hs := ih ht
    simp only [exec,State.store64] at he
    split at he
    · cases he
      exact ⟨hs.rdi,hs.wr,hs.nowrap⟩
    · cases he

/-- A field block's final stores establish a cache without strengthening its
arithmetic proof. Its existing postcondition only needs to retain scratch access. -/
theorem block_stores_valid {is : List Instr} {rs : List Reg} {o size : Nat}
    {s : State} {base : Addr} {Q : State → Prop}
    (h : WP isa (.block (is++stores rs o)) s Q)
    (hs : ∀ t,Q t → Scr t base size) (ho : o+8*rs.length≤size) (hd : rs.Nodup) :
    WP isa (.block (is++stores rs o)) s fun t => Q t ∧ Valid (ofStores rs o) t := by
  apply WP.block_append_iff.mpr
  apply WP.mono (WP.block_append_iff.mp h)
  intro u hu
  have hsu := stores_scr_back (WP.mono hu hs)
  obtain ⟨tr,t,he,hq⟩ := hu
  obtain ⟨tr',t',he',hc,_⟩ := stores_valid hsu ho hd
  have ht := (Exec.det he he').2
  subst t'
  exact ⟨tr,t,he,hq,hc⟩

end VG.Proof.Weierstrass.X86_64.Forward

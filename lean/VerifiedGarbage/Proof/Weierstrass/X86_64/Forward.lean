import VerifiedGarbage.Impl.Weierstrass.X86_64.Forward
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-! Forwarding changes memory reads to register reads with identical state results. -/
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
    cases i <;> simp only [Instr.dst,Option.some.injEq,reduceCtorEq] at hd
    all_goals subst d
    all_goals first | rfl | cases he
  exact Taint.exec_nonstore hd' he

theorem writes_frame {i : Instr} {rs : List Reg} {s t : State}
    (hw : writes i=some rs) (he : exec i s=some t) :
    t.rd=s.rd ∧ t.wr=s.wr ∧ t.mem=s.mem ∧ ∀ r,r∉rs → t.gpr r=s.gpr r := by
  cases i <;> simp only [writes,Instr.dst,Option.map_some,Option.map_none,
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

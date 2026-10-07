import VerifiedGarbage.Proof.Weierstrass.X86_64.Forward
import VerifiedGarbage.Proof.Mont.X86_64.Chain

/-! Consecutive output stores establish the next field operation's register cache. -/
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
    have hw : word s.mem base o=s.gpr r := BitVec.eq_of_toNat_eq (by omega)
    have ht : wordsVal s.mem base (o+8) rs.length=regsVal s rs := by omega
    have hl := load_sc hs (d := o) (by simp only [List.length_cons] at ho; omega)
    rw [hw] at hl
    intro c hc
    simp only [ofStores,List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact hl
    · exact ih (by simp only [List.length_cons] at ho; omega) ht c hc

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

import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8RowCT

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

theorem rowStep_stage {i n : Nat} {lo hi : Reg} {tail : List Reg}
    (hr : Regs (lo::hi::tail)) (hlen : (lo::hi::tail).length=n+2) (hi8 : i+n+2≤8)
    (L : CtLayout) (s : State) (h : Stage (n+1) (lo::hi::tail) L s) :
    WP isa (AdxTri8.rowStep i lo hi tail) s (Stage n (tail++[lo]) L) := by
  obtain ⟨⟨mi,hg,hI⟩,hp,hv⟩ := h
  have he := L.he; have hiL := L.hi; have hZ := L.hZ
  have bound : slot L.w aAcc+16*L.I+(16+8*(2*i+2))+8≤L.Z := by
    unfold slot aAcc at *; omega
  refine WP.mono (rowStep_ok hg.scr hg.rdi hg.hdr L.hZ hI hp (by rw [hlen]; omega)
    bound hr.1 hr.2 (by rw [hlen,show n+2-1=n+1 by omega]; exact hv))
    fun t ⟨_,zt,ot,kt⟩ => ?_
  have dr : t.gpr .rdi=L.B := (kt.gpr (by
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨by decide,⟨(hr.2 lo (by simp)).2.2.2.2.symm,(hr.2 hi (by simp)).2.2.2.2.symm,
      fun h => (hr.2 .rdi (by simp [h])).2.2.2.2 rfl⟩⟩)).trans hg.rdi
  have pr : t.gpr .rbp=off L.B L.e := (kt.gpr (by
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨by decide,⟨(hr.2 lo (by simp)).1.2.1.symm,(hr.2 hi (by simp)).1.2.1.symm,
      fun h => (hr.2 .rbp (by simp [h])).1.2.1 rfl⟩⟩)).trans hp
  have ht := hg.hdr.of_outside ot (by unfold slot; omega)
  have it : word t.mem L.B (8*sFn 12)=BitVec.ofNat 64 L.I := by
    rw [ot.word (by unfold slot hdrBytes sFn; omega) (by decide)]; exact hI
  have len : tail.length=n := by simp only [List.length_cons] at hlen; omega
  refine ⟨⟨mi,⟨hg.scr.congr kt.2.2,dr,ht⟩,it⟩,pr,?_⟩
  have h := value_zero_top (rs := tail) zt
  simpa only [List.length_append,List.length_cons,List.length_nil,len,Nat.zero_add,Nat.add_sub_cancel] using h

/-- Closed hints for each unrolled row; the loop itself is proved relationally. -/
def RowChecks (i : Nat) (lo hi : Reg) (tail : List Reg) : Prop :=
  ∃ ht hm hc : VG.Taint.Hint VG.X86_64.Taint.T,
    (taint.check (Taint.ofRegs [.rsi]) (Stores i lo hi) ht).isSome=true ∧
    (taint.check (Taint.ofRegs []) (.block [.mov32 lo (.imm 0)]) hm).isSome=true ∧
    (taint.check (Taint.ofRegs [.rbp]) (.block (AdxTri8.rowCore i (lo::hi::tail))) hc).isSome=true

def Checks : Nat → Nat → List Reg → Prop
  | 0, _, _ => True
  | n+1, i, rs => RowChecks i rs[0]! rs[1]! (rs.drop 2) ∧ Checks n (i+1) (AdxTri8.rotate rs)

theorem rows_ct (n i : Nat) (rs : List Reg) (hr : Regs rs) (hlen : rs.length=n+1)
    (hi : i+n+1≤8) (hc : Checks n i rs) :
    RelCT isa (Two (Stage n rs)) (AdxTri8.rows n i rs) (fun _ _ => True) := by
  induction n generalizing i rs with
  | zero => exact RelCT.block_nil fun _ _ _ => trivial
  | succ n ih =>
    cases rs with
    | nil => simp only [List.length_nil] at hlen; omega
    | cons lo rs =>
      cases rs with
      | nil => simp only [List.length_cons,List.length_nil] at hlen; omega
      | cons h tail =>
        obtain ⟨⟨ht,hm,hcore,htc,hmc,hcc⟩,next⟩ := hc
        change RelCT isa (Two (Stage (n+1) (lo::h::tail)))
          (.seq (AdxTri8.rowStep i lo h tail) (AdxTri8.rows n (i+1) (tail++[lo]))) _
        refine RelCT.seq (two_post (rowStep_ct hr hlen hi htc hmc hcc) (rowStep_stage hr hlen hi)) ?_
        apply ih (i+1) (tail++[lo]) (rotate_regs hr) _ (by omega) next
        simp only [List.length_cons] at hlen
        simp only [List.length_append,List.length_cons,List.length_nil]; omega

theorem checks_seven : Checks 7 0 AdxTri8.columns := by
  refine ⟨⟨_,_,_,by taint_decide,by taint_decide,by taint_decide⟩,?_⟩
  refine ⟨⟨_,_,_,by taint_decide,by taint_decide,by taint_decide⟩,?_⟩
  refine ⟨⟨_,_,_,by taint_decide,by taint_decide,by taint_decide⟩,?_⟩
  refine ⟨⟨_,_,_,by taint_decide,by taint_decide,by taint_decide⟩,?_⟩
  refine ⟨⟨_,_,_,by taint_decide,by taint_decide,by taint_decide⟩,?_⟩
  refine ⟨⟨_,_,_,by taint_decide,by taint_decide,by taint_decide⟩,?_⟩
  exact ⟨⟨_,_,_,by taint_decide,by taint_decide,by taint_decide⟩,True.intro⟩

end VG.Proof.Bignum.X86_64.AdxTri8

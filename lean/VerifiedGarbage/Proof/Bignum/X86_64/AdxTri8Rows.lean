import VerifiedGarbage.Proof.Bignum.X86_64.AdxTri8Sum

namespace VG.Proof.Bignum.X86_64.AdxTri8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

def output (w I i : Nat) := slot w aAcc+16*I+(16+8*(2*i+1))

private theorem compose_arith {P R T V A S W : Nat}
    (h : P+R*T=V+A) (e : W=T+S) : P+R*W=V+(A+R*S) := by grind

theorem rows_ok (n : Nat) {s : State} {B : Addr} {Z w I i e : Nat} {mi : BitVec 64} {rs : List Reg}
    (hs : Scr s B Z) (hd : s.gpr .rdi=B) (hh : Hdr s.mem B w mi) (hZ : slot w 8≤Z)
    (hI : word s.mem B (8*sFn 12)=BitVec.ofNat 64 I) (hp : s.gpr .rbp=off B e)
    (he : e+8*(i+n+1)≤Z) (hout : output w I i+16*n≤Z)
    (hsep : e+8*(i+n+1)≤output w I i ∨ output w I i+16*n≤e)
    (hr : Regs rs) (hlen : rs.length=n+1) (hv : value s rs<2^(64*n)) :
    WP isa (AdxTri8.rows n i rs) s fun t =>
      wv t.mem B (output w I i) (2*n)=value s rs+rowSum s.mem B e i n ∧
      Outside B (output w I i) (16*n) s.mem t.mem ∧
      Keep (([.rdx,.rcx,.rax,.rbx,.rsi] : List Reg)++rs) s t := by
  have nowrap := hs.nowrap
  induction n generalizing s i rs with
  | zero =>
    change WP isa (.block []) s _
    apply WP.block_nil
    have vz : value s rs=0 := by simpa only [Nat.mul_zero,Nat.pow_zero,Nat.lt_one_iff] using hv
    exact ⟨by simp only [wv,rowSum,vz,Nat.zero_add],Outside.refl _ _ _ _,Keep.refl _ _⟩
  | succ n ih =>
    cases rs with
    | nil => simp only [List.length_nil] at hlen; omega
    | cons lo rs =>
      cases rs with
      | nil => simp only [List.length_cons,List.length_nil] at hlen; omega
      | cons hi tail =>
        have tl : tail.length=n := by simp only [List.length_cons] at hlen; omega
        change WP isa (.seq (AdxTri8.rowStep i lo hi tail) (AdxTri8.rows n (i+1) (tail++[lo]))) s _
        refine WP.seq (WP.mono (rowStep_ok hs hd hh hZ hI hp (by rw [hlen]; omega)
          (by unfold output at hout; omega) hr.1 hr.2 (by rw [hlen]; simpa only [Nat.add_sub_cancel] using hv))
          fun a ⟨va,za,oa,ka⟩ => ?_)
        change Outside B (output w I i) 16 s.mem a.mem at oa
        have sa := hs.congr ka.2.2
        have da : a.gpr .rdi=B := (ka.gpr (by
          simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
          exact ⟨by decide,⟨(hr.2 lo (by simp)).2.2.2.2.symm,(hr.2 hi (by simp)).2.2.2.2.symm,
            fun h => (hr.2 .rdi (by simp [h])).2.2.2.2 rfl⟩⟩)).trans hd
        have pa : a.gpr .rbp=off B e := (ka.gpr (by
          simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or]
          exact ⟨by decide,⟨(hr.2 lo (by simp)).1.2.1.symm,(hr.2 hi (by simp)).1.2.1.symm,
            fun h => (hr.2 .rbp (by simp [h])).1.2.1 rfl⟩⟩)).trans hp
        have head : hdrBytes≤output w I i := by unfold output slot; omega
        have ia : word a.mem B (8*sFn 12)=BitVec.ofNat 64 I := by
          rw [oa.word (by unfold output slot hdrBytes sFn; omega) (by decide)]; exact hI
        have av : value a (tail++[lo])<2^(64*n) := by
          have h := value_zero_top (rs := tail) za
          simpa only [List.length_append,List.length_cons,List.length_nil,tl,Nat.zero_add,Nat.add_sub_cancel] using h
        have outNext : output w I (i+1)=output w I i+16 := by unfold output; omega
        refine WP.mono (ih (i := i+1) sa da (hh.of_outside oa head) ia pa (by omega)
          (by rw [outNext]; omega) (by rw [outNext]; omega) (rotate_regs hr)
          (by simp only [List.length_append,List.length_cons,List.length_nil,tl]) av)
          fun t ⟨vt,ot,kt⟩ => ?_
        have input : rowSum a.mem B e (i+1) n=rowSum s.mem B e (i+1) n :=
          rowSum_congr fun j hj => oa.word (by omega) (by omega)
        rw [input] at vt
        have pre : wv t.mem B (output w I i) 2=wv a.mem B (output w I i) 2 :=
          ot.wv (by rw [outNext]; omega) (by omega)
        have frames : Outside B (output w I i) (16*(n+1)) s.mem t.mem :=
          (oa.mono (by omega) (by omega)).trans (ot.mono (by rw [outNext]; omega) (by rw [outNext]; omega))
        refine ⟨?_,frames,(ka.trans kt).mono ?_⟩
        · rw [show 2*(n+1)=2+2*n by omega,wv_add,pre,
            show output w I i+8*2=output w I (i+1) by rw [outNext],rowSum]
          change wv a.mem B (output w I i) 2+2^128*wv t.mem B (output w I (i+1)) (2*n)=_
          simp only [hlen,Nat.add_sub_cancel] at va
          exact compose_arith va vt
        · intro r hm
          simp only [List.mem_append] at hm ⊢
          rcases hm with old | new
          · exact old
          · rcases new with base | rot
            · exact Or.inl base
            · exact Or.inr (rotate_subset r (List.mem_append.mpr rot))

end VG.Proof.Bignum.X86_64.AdxTri8

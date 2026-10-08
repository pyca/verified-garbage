import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Production
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeFetch
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAdd
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowInvariant

/-! Tree precomputation: even multiples double a previous table entry;
odd multiples add the original public point to the accumulator. -/
namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (Keeps read_x)

theorem jacTreeParity_ok {s : State} {m : Nat} (hm : m < 16)
    (h19 : s.gpr .x19 = BitVec.ofNat 64 (16-m)) :
    WP isa (.block [.movz .x .x5 1 0,.logic .and .x .x2 .x19 .x5]) s fun t =>
      isa.eval (.nonzero .x .x2) t = some (decide (m%2=1)) ∧ Keeps [.x2,.x5] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,exec,read_x,RegUpd.gpr_write,
    BitVec.setWidth_eq,Size.bits,show 16*0<64 from by decide,
    ite_true,ite_false,reduceCtorEq,h19,Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨fun r hr => ?_,rfl,rfl,rfl,rfl⟩⟩
  · change some ((BitVec.ofNat 64 (16-m) &&& 1) != 0) = _
    exact congrArg some ((show ∀ m<16, ((BitVec.ofNat 64 (16-m) &&& 1) != 0) = decide (m%2=1) by decide) m hm)
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [RegUpd.gpr_write,hr.1,hr.2,ite_false]

theorem keeps_prog {M : Mod} {base : Addr} {W : List Nat} {s t : State} {rs : List Reg}
    (h : Keeps rs s t) (hr : ∀ r ∈ rs, r ∈ clob M.n) : ProgKeep M base W s t :=
  ⟨fun r hn => h.gpr r (fun hh => hn (hr r hh)),h.rd,h.wr,h.sp,fun _ _ _ => congrFun h.mem _⟩

/-- The arithmetic portion constructs the next multiple in `D`. -/
theorem jacTreeArithmetic_ok {K : WinCfg} {C : Curve} {base : Addr} {size m : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52)
    (hAl : Aligned K.M (· ∈ jacWinSlots K)) (hm : UnitMod C.p (2^(64*K.M.n)))
    (hC : Law C) (ha : AM3 C) (ht : K.tbl<4096) (hOne : K.one<C.p)
    (hRP : RcbApart K.S K.R K.P K.D) (hm1 : 1≤m) (hm15 : m≤15)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p (· ∈ jacWinSlots K) V E s)
    (hV : ∀ x ∈ rcbR K.S K.R K.P, x ∈ V)
    (hVE : m%2≠1 → ∀ x ∈ [K.E.x,K.E.y,K.E.z], x ∈ V)
    (hT : ∀ x ∈ [(Jacobian.tablePt K ((m+1)/2)).x,(Jacobian.tablePt K ((m+1)/2)).y,
      (Jacobian.tablePt K ((m+1)/2)).z], x ∈ V)
    (h19 : s.gpr .x19=BitVec.ofNat 64 (16-m)) {P : Point C}
    (hP : onCurve C P=true) (hp : InvJ C (E K.P.x) (E K.P.y) (E K.P.z) P)
    (hr : InvJ C (E K.R.x) (E K.R.y) (E K.R.z) (mul m P))
    (hjt : InvJ C (E (Jacobian.tablePt K ((m+1)/2)).x)
      (E (Jacobian.tablePt K ((m+1)/2)).y) (E (Jacobian.tablePt K ((m+1)/2)).z) (mul ((m+1)/2) P)) :
    WP isa (Jacobian.jacTreeArithmetic K 16) s fun t =>
      ∃ E', ProgKeep K.M base (winOther K) s t ∧
      Inv K.M base size C.p (· ∈ jacWinSlots K) ([K.E.x,K.E.y,K.E.z,K.D.x,K.D.y,K.D.z]++V) E' t ∧
      InvJ C (E' K.D.x) (E' K.D.y) (E' K.D.z) (mul (m+1) P) := by
  have old := hL.toWinLay hJ
  have hs (x : Nat) (hx : x ∈ winRo K ++ winOther K) : x ∈ jacWinSlots K :=
    List.mem_append_left _ hx
  have sw : ∀ x ∈ rcbW K.S K.D, x ∈ winOther K := fun _ hx => List.mem_append_right _ hx
  have se : ∀ x ∈ [K.E.x,K.E.y,K.E.z], x ∈ winOther K := by
    intro x hx; simp only [winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; grind
  rw [Jacobian.jacTreeArithmetic]
  refine WP.seq (WP.mono (jacTreeParity_ok (by omega) h19) fun u ⟨he,ke⟩ => ?_)
  have iu := hI.of_keeps ke (by decide)
  have ku : ProgKeep K.M base (winOther K) s u := keeps_prog ke (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> simp [clob])
  refine WP.ite (decide (m%2=1)) he (fun hb => ?_) (fun hb => ?_)
  · have ho := of_decide_eq_true hb
    have hc : u.gpr .x19 = BitVec.ofNat 64 (15-2*((m+1)/2-1)) := by
      rw [ke.gpr _ (by decide),h19]; congr 1; omega
    have es : ∀ x ∈ [K.E.x,K.E.y,K.E.z], x ∈ jacWinSlots K := fun x hx => hs x (List.mem_append_right _ (se x hx))
    have sep : K.E.x+96 ≤ K.tbl+96*((m+1)/2-1) ∨ K.tbl+96*((m+1)/2-1)+96 ≤ K.E.x := by
      have x := hL.tbl K.E.x (List.mem_append_right _ (se _ (by simp)))
      have z := hL.tbl K.E.z (List.mem_append_right _ (se _ (by simp)))
      rw [hL.exz] at z
      omega
    apply WP.seq
    refine WP.mono (jacTreeFetchPoint_ok hL.lay hAl hL.n hL.exy hL.exz iu hc (by omega) (by omega)
      ht es hT sep hjt) fun v ⟨kf,iv,jv⟩ => ?_
    have ds : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.E K.E, x ∈ jacWinSlots K := by
      intro x hx; apply hs x
      simp only [rcbW,rcbR,winRo,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
      grind
    have dv : ∀ x ∈ rcbR K.S K.E K.E, x ∈ [K.E.x,K.E.y,K.E.z]++V := by
      intro x hx
      simp only [rcbR,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact List.mem_append_right _ (hV _ (by simp [rcbR]))
      · exact List.mem_append_right _ (hV _ (by simp [rcbR]))
      all_goals simp
    refine WP.mono (Forward.double_ok Forward.Production.cases hL.lay hAl (callOf_small (Nat.le_of_eq hL.n)) hm hC ha old.rcbApart_jac.2.1 ds iv dv
      (hC.onCurve_mul hP _) jv) fun t ⟨kd,it,jt⟩ => ⟨_,ku.trans ((kf.mono se).trans (kd.mono sw)),it.sub ?_,?_⟩
    · intro x hx
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
      grind
    · rw [hC.add_mul_mul hP,show (m+1)/2+(m+1)/2=m+1 by omega] at jt
      exact jt
  · have ho := of_decide_eq_false hb
    have ds : ∀ x ∈ rcbW K.S K.D ++ rcbR K.S K.R K.P, x ∈ jacWinSlots K := by
      intro x hx; apply hs x
      simp only [rcbW,rcbR,winRo,winOther,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
      grind
    refine WP.mono (jacAdd_ok hL.lay hAl (callOf_small (Nat.le_of_eq hL.n)) hm hC ha hRP ds iu hV hOne (hC.onCurve_mul hP m) hP hr hp)
      fun t ⟨et,kt,it,jt⟩ => ⟨et,ku.trans (kt.mono sw),it.sub ?_,?_⟩
    · intro x hx
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
      have ex := hVE ho K.E.x (by simp)
      have ey := hVE ho K.E.y (by simp)
      have ez := hVE ho K.E.z (by simp)
      grind
    · have jp : InvJ C (et K.D.x) (et K.D.y) (et K.D.z)
          (Spec.Weierstrass.add (mul m P) (mul 1 P)) := by rw [mul_one_pt]; exact jt
      rw [hC.add_mul_mul hP] at jp
      exact jp

end VG.Proof.Weierstrass.AArch64

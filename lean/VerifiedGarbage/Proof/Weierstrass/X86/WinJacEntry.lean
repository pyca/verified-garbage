import VerifiedGarbage.Proof.Weierstrass.X86.WinJacChoose

/-! Cached entries include the all-zero triple selected for magnitude zero. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

def coords (K : JacWinCfg) : List Nat := [K.E.x,K.E.y,K.E.z,K.z2,K.z3]

structure Entry (K : JacWinCfg) (C : Curve) (base : Addr) (Q : Point C) (s : State) : Prop where
  lt : ∀ x∈coords K,wordsVal s.mem base x K.M.n<C.p
  jac : InvJ C (tmv C K.M.n base s K.E.x) (tmv C K.M.n base s K.E.y) (tmv C K.M.n base s K.E.z) Q
  z2 : tmv C K.M.n base s K.z2=tmv C K.M.n base s K.E.z*tmv C K.M.n base s K.E.z
  z3 : tmv C K.M.n base s K.z3=tmv C K.M.n base s K.z2*tmv C K.M.n base s K.E.z

theorem Entry.of_inv {K : JacWinCfg} {C : Curve} {base : Addr} {size : Nat}
    {Sl : Nat → Prop} {V : List Nat} {E : Nat → Fe C} {s : State}
    (hI : Inv K.M base size C.p Sl V E s) (hv : ∀ x∈coords K,x∈V)
    {Q : Point C} (hj : InvJ C (E K.E.x) (E K.E.y) (E K.E.z) Q)
    (h2 : E K.z2=E K.E.z*E K.E.z) (h3 : E K.z3=E K.z2*E K.E.z) : Entry K C base Q s := by
  have ev (x : Nat) (hx : x∈coords K) : tmv C K.M.n base s x=E x := hI.val x (hv x hx)
  refine ⟨fun x hx => hI.lt x (hv x hx),?_,?_,?_⟩
  · rw [ev _ (by simp [coords]),ev _ (by simp [coords]),ev _ (by simp [coords])]; exact hj
  · rw [ev _ (by simp [coords]),ev _ (by simp [coords])]; exact h2
  · rw [ev _ (by simp [coords]),ev _ (by simp [coords]),ev _ (by simp [coords])]; exact h3

theorem coords_work (K : JacWinCfg) : ∀ x∈coords K,x∈work K := by
  intro x hx
  simp only [coords,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl <;> simp [work]

theorem Cached.entry {K : JacWinCfg} {C : Curve} {base : Addr} {s : State} {Q : Point C}
    (hn : K.M.n=4) (h : Cached C base s (fun c => K.T+32*c) Q) : Entry K C base Q s := by
  refine ⟨?_,?_,?_,?_⟩
  · intro x hx
    rw [hn]
    simp only [coords,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl
    · exact h.lt 0 (by decide)
    · exact h.lt 1 (by decide)
    · exact h.lt 2 (by decide)
    · exact h.lt 3 (by decide)
    · exact h.lt 4 (by decide)
  · rw [hn]; exact h.jac
  · rw [hn]; exact h.z2
  · rw [hn]; exact h.z3

theorem selected_keep {K : JacWinCfg} {base : Addr} {wk : Nat} {s t : State} (hn : K.M.n=4)
    (hu : Outside base K.T 160 s.mem t.mem) (hk : KeepRegs [.ecx,.edx] s t) :
    ProgKeep K.M base wk (coords K) s t := by
  refine ⟨fun r hr => hk.gpr r (fun he => hr (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl <;> simp [clob])),hk.rd,hk.wr,?_⟩
  intro x hx
  apply hu
  have hc (o : Nat) (ho : o∈coords K) := hx (o,8*K.M.n)
    (List.mem_append_left _ (List.mem_map.mpr ⟨o,ho,rfl⟩))
  have h0 := hc K.E.x (by simp [coords])
  have h1 := hc K.E.y (by simp [coords])
  have h2 := hc K.E.z (by simp [coords])
  have h3 := hc K.z2 (by simp [coords])
  have h4 := hc K.z3 (by simp [coords])
  simp only [hn,JacWinCfg.E,JacWinCfg.z2,JacWinCfg.z3] at h0 h1 h2 h3 h4
  omega

theorem select_entry_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk a : Nat}
    (hL : Layout K size wk) {s : State} (hs : Scr s base size) (ha : a≤16)
    (hb : s.gpr .ebx=BitVec.ofNat 32 a) {P : Point C} (ht : Table K C base P 16 s) :
    WP isa (.block K.select) s fun t => Entry K C base (mul a P) t ∧
      ProgKeep K.M base wk (coords K) s t := by
  have hT : K.T+160≤K.tbl := by
    have := hL.low K.z3 (by simp [slots,work])
    simp only [JacWinCfg.z3] at this
    omega
  refine WP.mono (select_ok hs ha hb hL.table (by have := hL.table; omega) hT)
    fun t ⟨et,ot,kt⟩ => ⟨?_,selected_keep hL.n ot kt⟩
  by_cases h1 : 1≤a
  · exact ((ht a h1 ha).congr (fun c hc => by simpa only [h1,ite_true] using et c hc)).entry hL.n
  · have az : a=0 := by omega
    subst a
    have ev (c : Nat) (hc : c<5) : wordsVal t.mem base (K.T+32*c) 4=0 := by
      simpa only [show ¬1≤0 by decide,ite_false] using et c hc
    have ez (c : Nat) (hc : c<5) : tmv C 4 base t (K.T+32*c)=0 := by
      unfold tmv; rw [ev c hc]; exact toM_zero _ _
    refine ⟨?_,?_,?_,?_⟩
    · intro x hx
      rw [hL.n]
      simp only [coords,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl
      · exact (ev 0 (by decide)).symm ▸ Nat.pos_of_ne_zero (NeZero.ne C.p)
      · exact (ev 1 (by decide)).symm ▸ Nat.pos_of_ne_zero (NeZero.ne C.p)
      · exact (ev 2 (by decide)).symm ▸ Nat.pos_of_ne_zero (NeZero.ne C.p)
      · exact (ev 3 (by decide)).symm ▸ Nat.pos_of_ne_zero (NeZero.ne C.p)
      · exact (ev 4 (by decide)).symm ▸ Nat.pos_of_ne_zero (NeZero.ne C.p)
    · rw [hL.n,Window5.mul_zero_pt]
      exact Or.inl ⟨rfl,ez 2 (by decide)⟩
    · rw [hL.n,show K.z2=K.T+32*3 from rfl,show K.E.z=K.T+32*2 from rfl,
        ez 3 (by decide),ez 2 (by decide)]
      grind
    · rw [hL.n,show K.z3=K.T+32*4 from rfl,show K.z2=K.T+32*3 from rfl,
        show K.E.z=K.T+32*2 from rfl,ez 4 (by decide),ez 3 (by decide),ez 2 (by decide)]
      grind

end VG.Proof.Weierstrass.X86.JWin

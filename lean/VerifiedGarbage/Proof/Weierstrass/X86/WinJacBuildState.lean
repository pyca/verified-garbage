import VerifiedGarbage.Proof.Weierstrass.X86.WinJacFrame

/-! Invariants shared by the finite-point table construction steps. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

def live (K : JacWinCfg) : List Nat := ro K++[K.E.x,K.E.y,K.E.z,K.z2,K.z3]

theorem live_slots (K : JacWinCfg) : ∀ x∈live K,x∈slots K := by
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · exact List.mem_append_left _ hx
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl <;> simp [slots,work]

/-- The table stores leave every initialized arithmetic slot intact. -/
theorem store_slot {K : JacWinCfg} {base : Addr} {size wk m x : Nat} {s t : State}
    (hL : Layout K size wk) (hs : Scr s base size) (hx : x∈slots K)
    (hu : Unch base (storeW K m) s.mem t.mem) :
    wordsVal t.mem base x K.M.n=wordsVal s.mem base x K.M.n := by
  have hl := hL.low x hx
  have hb := hL.lay.le x hx
  have hn := hs.nowrap
  apply hu.wordsVal (fun w hw => ?_) (by omega)
  simp only [storeW,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl|rfl <;> dsimp only <;> rw [hL.n] <;> omega

theorem Cached.store {K : JacWinCfg} {C : Curve} {base : Addr} {size wk m : Nat} {s t : State}
    (hL : Layout K size wk) (hs : Scr s base size) (hu : Unch base (storeW K m) s.mem t.mem)
    {Q : Point C} (h : Cached C base s (fun c => K.T+32*c) Q) :
    Cached C base t (fun c => K.T+32*c) Q := by
  apply h.congr
  intro c hc
  have hx : K.T+32*c∈slots K := by
    have : c=0 ∨ c=1 ∨ c=2 ∨ c=3 ∨ c=4 := by omega
    rcases this with rfl|rfl|rfl|rfl|rfl <;> simp [slots,work,JacWinCfg.E,JacWinCfg.z2,JacWinCfg.z3]
  simpa only [hL.n] using store_slot hL hs hx hu

/-- Reconstruct only initialized fields; temporary arithmetic slots need no bounds. -/
theorem Frame.inv_cached {K : JacWinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    {s₀ s : State} (h : Frame K C base size wk s₀ s)
    (hro : ∀ x∈JWin.ro K,wordsVal s₀.mem base x K.M.n<C.p) {Q : Point C}
    (hc : Cached C base s (fun c => K.T+32*c) Q) :
    Inv K.M base size C.p (·∈slots K) (live K) (tmv C K.M.n base s) s := by
  refine ⟨h.scr,h.mod,live_slots K,?_,fun _ _ => rfl⟩
  intro x hx
  rcases List.mem_append.mp hx with hx|hx
  · rw [h.ro hL hW hx]; exact hro x hx
  · rw [hL.n]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl
    · exact hc.lt 0 (by decide)
    · exact hc.lt 1 (by decide)
    · exact hc.lt 2 (by decide)
    · exact hc.lt 3 (by decide)
    · exact hc.lt 4 (by decide)

structure BuildInv (K : JacWinCfg) (C : Curve) (base : Addr) (size wk : Nat)
    (P : Point C) (s₀ : State) (m : Nat) (s : State) : Prop where
  frame : Frame K C base size wk s₀ s
  table : Table K C base P m s
  point : Cached C base s (fun c => K.T+32*c) (mul m P)
  counter : s.gpr .esi=BitVec.ofNat 32 m

theorem build_store_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk m : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    {s₀ s : State} (h : Frame K C base size wk s₀ s) (hm : m<16)
    (hb : s.gpr .esi=BitVec.ofNat 32 (m+1)) {P : Point C}
    (ht : Table K C base P m s)
    (hp : Cached C base s (fun c => K.T+32*c) (mul (m+1) P)) :
    WP isa (.block K.storeEntry) s (BuildInv K C base size wk P s₀ (m+1)) := by
  have hT : K.T+160≤K.tbl := by
    have := hL.low K.z3 (by simp [slots,work])
    simp only [JacWinCfg.z3] at this
    omega
  refine WP.mono (store_table_ok h.scr hm hb hL.table hT ht hp)
    fun t ⟨ht,hu,hk⟩ => ⟨h.store hL hW hm hu hk,ht,hp.store hL h.scr hu,
      (hk.gpr _ (by decide)).trans hb⟩

end VG.Proof.Weierstrass.X86.JWin

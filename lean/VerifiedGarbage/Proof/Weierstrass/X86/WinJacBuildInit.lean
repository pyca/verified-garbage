import VerifiedGarbage.Proof.Weierstrass.X86.WinJacBuildState

/-! Initialize the cached table point from an affine input. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

private theorem coord_mem (K : JacWinCfg) {c : Nat} (hc : c<5) : K.T+32*c∈work K := by
  have : c=0 ∨ c=1 ∨ c=2 ∨ c=3 ∨ c=4 := by omega
  rcases this with rfl|rfl|rfl|rfl|rfl <;> simp [work,JacWinCfg.E,JacWinCfg.z2,JacWinCfg.z3]

/-- Copy affine XYZ and use its unit Z for both cached powers. -/
theorem build_copy_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    {s : State} (hI : Inv K.M base size C.p (·∈slots K) (ro K) (tmv C K.M.n base s) s)
    {P : Point C} (hJ : InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y)
      (tmv C K.M.n base s K.P.z) P) (hz : tmv C K.M.n base s K.P.z=1) (hC : Law C) :
    WP isa (.block (copyPt 4 K.E K.P++copy 8 K.z2 K.P.z++copy 8 K.z3 K.P.z)) s fun t =>
      Cached C base t (fun c => K.T+32*c) P ∧ Frame K C base size wk s t := by
  have cs (c : Nat) (hc : c<5) : K.T+32*c∈slots K := List.mem_append_right _ (coord_mem K hc)
  have px : K.P.x∈ro K := by simp [ro]
  have py : K.P.y∈ro K := by simp [ro]
  have pz : K.P.z∈ro K := by simp [ro]
  have sep (x : Nat) (hx : x∈ro K) (c : Nat) (hc : c<5) : x≠K.T+32*c :=
    fun he => hL.readonly x hx (he ▸ coord_mem K hc)
  have spy : K.P.y≠K.T := by simpa using sep K.P.y py 0 (by decide)
  have spz := sep K.P.z pz
  have spz0 : K.P.z≠K.T := by simpa using spz 0 (by decide)
  simp only [copyPt,List.append_assoc]
  rw [WP.block_append_iff]
  have n8 : 2*K.M.n=8 := by rw [hL.n]
  have step := copyField_ok hL.lay hW hI (cs 0 (by decide)) px
  simp only [n8,Nat.reduceMul,Nat.add_zero] at step
  refine WP.mono step
    fun a ⟨ka,ia⟩ => ?_
  rw [WP.block_append_iff]
  have step := copyField_ok hL.lay hW ia (cs 1 (by decide)) (List.mem_cons_of_mem _ py)
  simp only [n8,Nat.reduceMul] at step
  refine WP.mono step fun b ⟨kb,ib⟩ => ?_
  rw [WP.block_append_iff]
  have step := copyField_ok hL.lay hW ib (cs 2 (by decide)) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ pz))
  simp only [n8,Nat.reduceMul] at step
  refine WP.mono step fun c ⟨kc,ic⟩ => ?_
  rw [WP.block_append_iff]
  have step := copyField_ok hL.lay hW ic (cs 3 (by decide)) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ pz)))
  simp only [n8,Nat.reduceMul] at step
  refine WP.mono step fun d ⟨kd,id⟩ => ?_
  have step := copyField_ok hL.lay hW id (cs 4 (by decide)) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ pz))))
  simp only [n8,Nat.reduceMul] at step
  refine WP.mono step
    fun t ⟨kt,it⟩ => ?_
  have hs : ∀ x∈[K.E.x,K.E.y,K.E.z,K.z2,K.z3],x∈work K := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl <;> simp [work]
  have kk : ProgKeep K.M base wk [K.E.x,K.E.y,K.E.z,K.z2,K.z3] s t :=
    (progKeep_of_op ka (by simp [JacWinCfg.E])).trans
      ((progKeep_of_op kb (by simp [JacWinCfg.E])).trans
        ((progKeep_of_op kc (by simp [JacWinCfg.E])).trans
          ((progKeep_of_op kd (by simp [JacWinCfg.z2])).trans (progKeep_of_op kt (by simp [JacWinCfg.z3])))))
  refine ⟨?_,(Frame.refl hI.scr hI.mod).field hL hW kk hs⟩
  apply Cached.of_inv hL.n it
  · intro c hc
    have : c=0 ∨ c=1 ∨ c=2 ∨ c=3 ∨ c=4 := by omega
    rcases this with rfl|rfl|rfl|rfl|rfl <;> simp
  all_goals
    simp only [JacWinCfg.E,JacWinCfg.z2,JacWinCfg.z3,Function.update_apply]
    simp only [spy,spz0,spz 1 (by decide),spz 2 (by decide),spz 3 (by decide),ite_false]
    simp (disch := omega) only [ite_eq_right,ite_true]
  · exact hJ
  · rw [hz]; exact hC.one_ne_zero
  · rw [hz]; grind
  · rw [hz]; grind

/-- The first packed entry is the input point, with no field multiplications. -/
theorem build_init_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    {s : State} (hI : Inv K.M base size C.p (·∈slots K) (ro K) (tmv C K.M.n base s) s)
    {P : Point C} (hJ : InvJ C (tmv C K.M.n base s K.P.x) (tmv C K.M.n base s K.P.y)
      (tmv C K.M.n base s K.P.z) P) (hz : tmv C K.M.n base s K.P.z=1) (hC : Law C) :
    WP isa (.block (copyPt 4 K.E K.P++copy 8 K.z2 K.P.z++copy 8 K.z3 K.P.z++
      ([.mov .esi (.imm 1)] : List Instr)++K.storeEntry)) s (BuildInv K C base size wk P s 1) := by
  rw [WP.block_append_iff,WP.block_append_iff]
  refine WP.mono (build_copy_ok hL hW hI hJ hz hC) fun a ⟨pa,fa⟩ => ?_
  refine WP.mono (mov_counter_ok a 1) fun b ⟨cb,kb⟩ => ?_
  apply build_store_ok hL hW (fa.keeps kb) (m:=0) (by decide) cb
  · intro m h1 hm; omega
  · rw [show 0+1=1 from rfl,mul_one_pt]
    exact pa.congr fun _ _ => by rw [kb.2.1]

end VG.Proof.Weierstrass.X86.JWin

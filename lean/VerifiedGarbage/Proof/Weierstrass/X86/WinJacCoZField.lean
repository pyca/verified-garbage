import VerifiedGarbage.Proof.Weierstrass.X86.WinJacBuildState
import VerifiedGarbage.Proof.Weierstrass.JacCoZ

/-! Co-Z table arithmetic in the existing x86 scratch layout. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

/-- DBLU on numbered slots (`tblσ`). -/
def dbluN : List FOp :=
  [.mul 0 18 18, .mul 1 19 19, .mul 2 1 1, .mul 3 18 1, .add 3 3 3, .add 3 3 3, .sub 4 0 20,
   .add 5 4 4, .add 4 5 4, .mul 12 4 4, .sub 12 12 3, .sub 12 12 3, .sub 5 3 12, .mul 13 4 5,
   .add 2 2 2, .add 2 2 2, .add 2 2 2, .sub 13 13 2, .add 14 19 19, .mul 15 14 14, .mul 16 15 14]

/-- ZADDU on numbered slots (`tblσ`). -/
def zadduN : List FOp :=
  [.sub 0 9 12, .mul 1 0 0, .mul 14 14 0, .mul 9 9 1, .mul 3 12 1, .sub 4 10 13, .mul 5 4 4,
   .sub 2 9 3, .mul 10 10 2, .sub 12 5 9, .sub 12 12 3, .sub 13 9 12, .mul 13 4 13, .sub 13 13 10,
   .mul 15 15 1, .mul 16 15 14]

/-- DBLU from `P = (x, y, 1)`: `T = 2 P` with its powers, and `(t3, t2)` is
`P` scaled by `T`'s `Z`. -/
theorem dbluN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) (h20 : e 20 = 1) :
    (runOps dbluN e 12, runOps dbluN e 13, runOps dbluN e 14) = dblJF (e 18) (e 19) 1 ∧
      runOps dbluN e 15 = runOps dbluN e 14 * runOps dbluN e 14 ∧
      runOps dbluN e 16 = runOps dbluN e 15 * runOps dbluN e 14 ∧
      runOps dbluN e 3 * (1 * 1) = e 18 * (runOps dbluN e 14 * runOps dbluN e 14) ∧
      runOps dbluN e 2 * (1 * 1 * 1) =
        e 19 * (runOps dbluN e 14 * runOps dbluN e 14 * runOps dbluN e 14) := by
  simp only [dbluN, runOps, List.foldl_cons, List.foldl_nil, FOp.run, Function.update_apply]
  simp only [Nat.reduceEqDiff, ite_true, ite_false, h20, dblJF, Prod.mk.injEq]
  refine ⟨⟨?_, ?_, ?_⟩, trivial, trivial, ?_, ?_⟩ <;> grind

/-- ZADDU of `D = (X1, Y1)` and `T = (X2, Y2)` sharing `Z`, with `T`'s powers. -/
theorem zadduN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    ((runOps zadduN e 12, runOps zadduN e 13, runOps zadduN e 14), (runOps zadduN e 9, runOps zadduN e 10)) =
        zadduF (e 9) (e 10) (e 12) (e 13) (e 14) ∧
      (e 15 = e 14 * e 14 → runOps zadduN e 15 = runOps zadduN e 14 * runOps zadduN e 14) ∧
      runOps zadduN e 16 = runOps zadduN e 15 * runOps zadduN e 14 := by
  simp only [zadduN, runOps, List.foldl_cons, List.foldl_nil, FOp.run, Function.update_apply]
  simp only [Nat.reduceEqDiff, ite_true, ite_false, zadduF]
  refine ⟨?_, fun h => ?_, ?_⟩ <;> first | trivial | grind


/-- Co-Z numbered slots use the existing work-list order, then the affine input. -/
def coσ (K : JacWinCfg) (i : Nat) : Nat :=
  (work K ++ [K.P.x,K.P.y,K.P.z]).getD i K.P.x

theorem coP_readonly {K : JacWinCfg} {size wk : Nat} (hL : Layout K size wk) :
    ∀ x∈[K.P.x,K.P.y,K.P.z],x∉work K := by
  intro x hx
  exact hL.readonly x (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl <;> simp [ro])

/-- Run a numbered co-Z formula without making a second scratch layout. -/
theorem coProg_ok {K : JacWinCfg} {C : Curve} {base : Addr} {size wk : Nat}
    (hL : Layout K size wk) (hW : WkOk K.F K.M C.p size wk (·∈slots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) {N : List FOp}
    (hout : ∀ op∈N,op.out<18)
    {V : List Nat} {E : Nat → Fe C} {s : State}
    (hi : Inv K.M base size C.p (·∈slots K) V E s)
    (hr : readsOk (N.map (FOp.rename (coσ K))) V=true) :
    WP isa (fprog K.F (N.map (FOp.rename (coσ K)))) s fun t =>
      ProgKeep K.M base wk (work K) s t ∧
      Inv K.M base size C.p (·∈slots K)
        (validAfter (N.map (FOp.rename (coσ K))) V)
        (runOps (N.map (FOp.rename (coσ K))) E) t ∧
      (∀ i,runOps (N.map (FOp.rename (coσ K))) E (coσ K i)=
        runOps N (fun j => E (coσ K j)) i) := by
  have hp := coP_readonly hL
  have hinj : ∀ op∈N,∀ y,coσ K y=coσ K op.out → y=op.out := fun op ho y =>
    getD_append_inj hL.nd hp (hp _ (List.mem_cons_self ..)) (hout op ho) y
  have hmem : ∀ i,coσ K i∈slots K := by
    intro i
    have hx := getD_append_mem (W:=work K) (List.mem_cons_self (a:=K.P.x) (l:=[K.P.y,K.P.z])) i
    rcases List.mem_append.mp hx with h|h
    · exact List.mem_append_right _ h
    · apply List.mem_append_left
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with h|h|h <;> simp only [coσ,h] <;> simp [ro]
  have hS : ∀ op∈N.map (FOp.rename (coσ K)),∀ x∈op.out::op.ins,x∈slots K := by
    intro op ho
    obtain ⟨op',_,rfl⟩ := List.mem_map.mp ho
    cases op' <;> simp only [FOp.rename,FOp.out,FOp.ins,List.mem_cons,List.not_mem_nil,or_false] <;>
      rintro x (rfl|rfl|rfl) <;> exact hmem _
  refine WP.mono (fprog_ok hL.lay hW hm _ hi hS hr) fun t ⟨kt,it⟩ =>
    ⟨kt.mono ?_,it,?_⟩
  · intro x hx
    obtain ⟨op,ho,rfl⟩ := List.mem_map.mp hx
    obtain ⟨op',ho',rfl⟩ := List.mem_map.mp ho
    rw [FOp.out_rename]
    unfold coσ
    rw [getD_append_left (by simpa only [work,temps,List.length_append,List.length_cons,List.length_nil] using hout op' ho')]
    exact List.getElem_mem _
  · exact fun i => congrFun (runOps_rename (coσ K) N E hinj) i


theorem dblu_eq (K : JacWinCfg) : K.dbluOps=dbluN.map (FOp.rename (coσ K)) := rfl

theorem zaddu_eq (K : JacWinCfg) : K.zadduOps=zadduN.map (FOp.rename (coσ K)) := rfl

theorem dbluN_out : ∀ op∈dbluN,op.out<18 := by decide
theorem zadduN_out : ∀ op∈zadduN,op.out<18 := by decide
theorem dbluN_reads : readsOk dbluN [18,19,20]=true := by decide
theorem zadduN_reads : readsOk zadduN [9,10,12,13,14,15]=true := by decide

end VG.Proof.Weierstrass.X86.JWin

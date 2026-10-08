import VerifiedGarbage.Impl.Weierstrass.X86.WinJac
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import VerifiedGarbage.Proof.Weierstrass.JacAdd

/-! The table's mixed Jacobian addition and cached powers. -/
namespace VG.Proof.Weierstrass.X86.JWin
open VG VG.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Mont
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

/-- The table's step on numbered slots: `t0 … t5` are `0 … 5`, `T`'s five
coordinates `6 … 10`, `P` `11 … 13`. -/
def maddN : List FOp :=
  jacMixedHead ⟨14, 15, 0, 1, 2, 3, 4, 5⟩ ⟨6, 7, 8⟩ ⟨11, 12, 13⟩ ++
    jacMixedTail ⟨14, 15, 0, 1, 2, 3, 4, 5⟩ ⟨6, 7, 8⟩ ⟨11, 12, 13⟩ ⟨6, 7, 8⟩ ++ [.mul 9 8 8, .mul 10 9 8]

/-- The table step's slot `i`. -/
def maddσ (K : JacWinCfg) (i : Nat) : Nat :=
  ([K.S.t0, K.S.t1, K.S.t2, K.S.t3, K.S.t4, K.S.t5, K.E.x, K.E.y, K.E.z, K.z2, K.z3] ++
    [K.P.x, K.P.y, K.P.z]).getD i K.P.x

theorem madd_eq (K : JacWinCfg) : K.maddOps ++ K.cacheOps = maddN.map (FOp.rename (maddσ K)) := rfl

theorem map_out_rename (σ : Nat → Nat) (N : List FOp) :
    (N.map (FOp.rename σ)).map FOp.out = (N.map FOp.out).map σ := by
  simp only [List.map_map]
  exact List.map_congr_left fun op _ => FOp.out_rename σ op

theorem maddN_out : ∀ op ∈ maddN, op.out < 11 := by decide

theorem maddN_reads : readsOk maddN [2, 4, 6, 7, 8, 11, 12] = true := by decide

theorem maddN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) (h2 : e 2 = e 6) (h4 : e 4 = e 7) :
    (runOps maddN e 6, runOps maddN e 7, runOps maddN e 8) = jacAddF (e 6) (e 7) (e 8) (e 11) (e 12) 1 ∧
      runOps maddN e 9 = runOps maddN e 8 * runOps maddN e 8 ∧
      runOps maddN e 10 = runOps maddN e 9 * runOps maddN e 8 := by
  simp only [maddN, jacMixedHead, jacMixedTail, jacTail, List.take, List.cons_append, List.nil_append,
    runOps, List.foldl_cons, List.foldl_nil, FOp.run, Function.update_apply]
  simp only [Nat.reduceEqDiff, ite_true, ite_false, h2, h4, jacAddF, Prod.mk.injEq]
  refine ⟨⟨?_, ?_, ?_⟩, trivial, trivial⟩ <;> grind

theorem maddCache_ok {K : JacWinCfg} {base : Addr} {size wk : Nat} {C : Spec.Weierstrass.Curve}
    {Sl : Nat → Prop} (hL : Lay K.M size Sl) (hW : WkOk K.F K.M C.p size wk Sl)
    (hp : UnitMod C.p (2^(64*K.M.n)))
    (hn : ([K.S.t0,K.S.t1,K.S.t2,K.S.t3,K.S.t4,K.S.t5,K.E.x,K.E.y,K.E.z,K.z2,K.z3] : List Nat).Nodup)
    (hP : ∀ x∈[K.P.x,K.P.y,K.P.z],x∉[K.S.t0,K.S.t1,K.S.t2,K.S.t3,K.S.t4,K.S.t5,K.E.x,K.E.y,K.E.z,K.z2,K.z3])
    (hall : ∀ x∈[K.S.t0,K.S.t1,K.S.t2,K.S.t3,K.S.t4,K.S.t5,K.E.x,K.E.y,K.E.z,K.z2,K.z3]++
      [K.P.x,K.P.y,K.P.z],Sl x)
    {V : List Nat} {E : Nat → Fe C} {s : State} (hI : Inv K.M base size C.p Sl V E s)
    (hV : ∀ x∈[K.S.t2,K.S.t4,K.E.x,K.E.y,K.E.z,K.P.x,K.P.y],x∈V)
    (h2 : E K.S.t2=E K.E.x) (h4 : E K.S.t4=E K.E.y) :
    WP isa (fprog K.F (K.maddOps++K.cacheOps)) s fun t =>
      ProgKeep K.M base wk (rcbW K.S K.E++[K.z2,K.z3]) s t ∧ ∃ E' : Nat → Fe C,
      Inv K.M base size C.p Sl ([K.E.x,K.E.y,K.E.z,K.z2,K.z3]++V) E' t ∧
      (E' K.E.x,E' K.E.y,E' K.E.z)=jacAddF (E K.E.x) (E K.E.y) (E K.E.z) (E K.P.x) (E K.P.y) 1 ∧
      E' K.z2=E' K.E.z*E' K.E.z ∧ E' K.z3=E' K.z2*E' K.E.z := by
  have hinj : ∀ op∈maddN,∀ y,maddσ K y=maddσ K op.out → y=op.out := fun op hop y =>
    getD_append_inj hn hP (hP _ (List.mem_cons_self ..)) (maddN_out op hop) y
  have hmem : ∀ i, Sl (maddσ K i) := fun i =>
    hall _ (getD_append_mem (List.mem_cons_self (a := K.P.x) (l := [K.P.y, K.P.z])) i)
  have hS : ∀ op ∈ maddN.map (FOp.rename (maddσ K)), ∀ x ∈ op.out :: op.ins, Sl x := by
    intro op hop
    obtain ⟨op', _, rfl⟩ := List.mem_map.mp hop
    cases op' <;> simp only [FOp.rename, FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil,
      or_false] <;> rintro x (rfl | rfl | rfl) <;> exact hmem _
  have hR : readsOk (maddN.map (FOp.rename (maddσ K))) V = true :=
    readsOk_mono (readsOk_rename (maddσ K) maddN_reads) fun x hx => hV x (by
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with h | h | h | h | h | h | h <;> rw [h] <;> simp [maddσ])
  rw [madd_eq]
  refine WP.mono (fprog_ok hL hW hp _ hI hS hR) fun t ⟨kt, it⟩ =>
    ⟨kt.mono ?_, runOps (maddN.map (FOp.rename (maddσ K))) E, ?_, ?_⟩
  · intro x hx
    obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hx
    obtain ⟨op', hop', rfl⟩ := List.mem_map.mp hop
    rw [FOp.out_rename]
    have hlt := maddN_out op' hop'
    unfold maddσ
    rw [getD_append_left (by simpa using hlt)]
    have := List.getElem_mem (l := [K.S.t0, K.S.t1, K.S.t2, K.S.t3, K.S.t4, K.S.t5, K.E.x, K.E.y, K.E.z, K.z2,
      K.z3]) (by simpa using hlt)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    simp only [rcbW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rcases this with h | h | h | h | h | h | h | h | h | h | h <;> simp [h]
  · refine it.sub fun x hx => ?_
    rw [mem_validAfter]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (h | h | h | h | h) | h
    all_goals first
      | exact Or.inl h
      | (refine Or.inr ?_; subst h; rw [map_out_rename])
    · exact List.mem_map.mpr ⟨6, by decide, rfl⟩
    · exact List.mem_map.mpr ⟨7, by decide, rfl⟩
    · exact List.mem_map.mpr ⟨8, by decide, rfl⟩
    · exact List.mem_map.mpr ⟨9, by decide, rfl⟩
    · exact List.mem_map.mpr ⟨10, by decide, rfl⟩
  · have hren := runOps_rename (maddσ K) maddN E hinj
    have hv := maddN_run (fun y => E (maddσ K y)) h2 h4
    have e : ∀ i, runOps (maddN.map (FOp.rename (maddσ K))) E (maddσ K i) =
        runOps maddN (fun y => E (maddσ K y)) i := fun i => congrFun hren i
    refine ⟨?_, ?_, ?_⟩
    · exact (congrArg₂ Prod.mk (e 6) (congrArg₂ Prod.mk (e 7) (e 8))).trans hv.1
    · exact (e 9).trans (hv.2.1.trans (by rw [← e 8]; rfl))
    · exact (e 10).trans (hv.2.2.trans (by rw [← e 9, ← e 8]; rfl))

end VG.Proof.Weierstrass.X86.JWin

import VerifiedGarbage.Proof.Weierstrass.X86.Fprog

/-! # The complete a = -3 addition on x86 (32-bit) -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont

/-- A formula on numbered slots, renamed to `p`, `q` and `o`: it writes only
`rcbW S o`, and its result is what the numbered formula computes. -/
theorem ofN_ok {M : Mod} {base : Addr} {size m wk : Nat} [NeZero m] {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hW : WkOk M size wk Sl) (hm : UnitMod m (2 ^ (64 * M.n))) {N : List FOp} (hN : NumOk N) {S : RcbSlots}
    {p q o : Pt} (hA : RcbApart S p q o) (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x) {V : List Nat}
    {E : Nat → Fin m} {s : State} (hI : Inv M base size m Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (fprog M wk (ofN N S p q o)) s fun s' => ProgKeep M base wk (rcbW S o) s s' ∧
      Inv M base size m Sl ([o.x, o.y, o.z] ++ V) (runOps (ofN N S p q o) E) s' ∧
      (runOps (ofN N S p q o) E o.x, runOps (ofN N S p q o) E o.y, runOps (ofN N S p q o) E o.z) =
        (runOps N (fun y => E (rcbσ S p q o y)) 6, runOps N (fun y => E (rcbσ S p q o y)) 7,
          runOps N (fun y => E (rcbσ S p q o y)) 8) := by
  have hR : readsOk (ofN N S p q o) V = true := readsOk_mono (ofN_readsOk hN S p q o) hV
  refine WP.mono (fprog_ok hL hW hm _ hI (fun op hop x hx => hSl x (ofN_slots op hop x hx)) hR)
    fun s' ⟨hk, hI'⟩ => ⟨hk.mono fun w hw => ?_, hI'.sub fun x hx => ?_, ?_⟩
  · obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw
    exact ofN_out hN op hop
  · rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (ofN_out_mem hN hx)
    · exact Or.inl hx
  · exact congrArg₂ Prod.mk (ofN_run hN hA E 6) (congrArg₂ Prod.mk (ofN_run hN hA E 7) (ofN_run hN hA E 8))

/-- `o = p + q` by Algorithm 4 (`a = -3`, with `b` in `S.b3`). -/
theorem rcb3_ok {M : Mod} {base : Addr} {size m wk : Nat} [NeZero m] {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hW : WkOk M size wk Sl) (hm : UnitMod m (2 ^ (64 * M.n))) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o) (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x) {V : List Nat} {E : Nat → Fin m}
    {s : State} (hI : Inv M base size m Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (fprog M wk (rcb3 S p q o)) s fun s' => ProgKeep M base wk (rcbW S o) s s' ∧
      Inv M base size m Sl ([o.x, o.y, o.z] ++ V) (runOps (rcb3 S p q o) E) s' ∧
      (runOps (rcb3 S p q o) E o.x, runOps (rcb3 S p q o) E o.y, runOps (rcb3 S p q o) E o.z) =
        VG.Proof.Weierstrass.rcbAdd3 (E S.b3) (E p.x) (E p.y) (E p.z) (E q.x) (E q.y) (E q.z) := by
  rw [rcb3_eq]
  exact WP.mono (ofN_ok hL hW hm rcb3N_ok hA hSl hI hV) fun s' ⟨k, I, v⟩ =>
    ⟨k, I, v.trans (rcb3N_run _)⟩

end VG.Proof.Weierstrass.X86

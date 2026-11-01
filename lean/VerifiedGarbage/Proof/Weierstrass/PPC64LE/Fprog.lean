module

public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.PointFprog
public import VerifiedGarbage.Proof.Mont.Words

/-!
# Field programs on slots, on PPC64LE

`fprog S ops` (`Impl/Weierstrass/PPC64LE/Call.lean`) runs the field
operations `ops` on slots of the working space, one by one by calls of the
functions of the modulus `S` (`fprog_ok`), as on 32-bit ARM
(`Proof/Weierstrass/Arm/Fprog.lean`): on slots that are apart from each other
and below the functions' own working space (`Proof.Mont.Lay` of
`own M.n` bytes), what the slots stand for (`toM`) follows `runOps ops`, the
program on environments (`Inv`). A slot is read only once it holds a number
below `m`: either it did at the start (`V`) or an earlier operation wrote it
(`Proof.Weierstrass.readsOk`). Only the registers `fnClob`, the slots
written and the functions' own working space change (`KeepR`, with the
slots their own offsets).

The complete addition `rcb` is such a program, and computes `rcbAdd`
(`rcb_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE.Mont
open VG.Proof.Weierstrass.PPC64LE.Point (KeepR)

/-- The state holds the environment `E` in Montgomery's form in the slots
`V` (of `Sl`), below `m`, and the working space is at `r3`. -/
structure Inv (n : Nat) (base : Addr) (m : Nat) [NeZero m] (Sl : Nat → Prop) (V : List Nat)
    (E : Nat → Fin m) (s : State) : Prop where
  ws : WsReg s base
  sl : ∀ x ∈ V, Sl x
  lt : ∀ x ∈ V, wordsVal s.mem base x n < m
  val : ∀ x ∈ V, toM m (2 ^ (64 * n)) (wordsVal s.mem base x n) = E x

theorem Inv.sub {n : Nat} {base : Addr} {m : Nat} [NeZero m] {Sl : Nat → Prop} {V V' : List Nat}
    {E : Nat → Fin m} {s : State} (h : Inv n base m Sl V E s) (hV : ∀ x ∈ V', x ∈ V) :
    Inv n base m Sl V' E s :=
  ⟨h.ws, fun x hx => h.sl x (hV x hx), fun x hx => h.lt x (hV x hx), fun x hx => h.val x (hV x hx)⟩

/-- An operation writing `o`, which then holds `v`, keeps the invariant. -/
theorem Inv.update {M : Mod} {base : Addr} {m : Nat} [NeZero m] {Sl : Nat → Prop}
    (hL : Lay M (own M.n) Sl) {V : List Nat} {E : Nat → Fin m} {s s' : State}
    (hI : Inv M.n base m Sl V E s) {o : Nat} (ho : Sl o) (hk : KeepR M.n (fun x => x) base [o] s s')
    (hr : wordsVal s'.mem base o M.n < m) {v : Fin m}
    (hv : toM m (2 ^ (64 * M.n)) (wordsVal s'.mem base o M.n) = v) :
    Inv M.n base m Sl (o :: V) (Function.update E o v) s' := by
  have hn := hI.ws.nowrap
  have hown : own M.n ≤ 4096 := Nat.sub_le _ _
  have heq : ∀ x ∈ V, x ≠ o → wordsVal s'.mem base x M.n = wordsVal s.mem base x M.n := by
    intro x hx hxo
    have hxS := hI.sl x hx
    have h1 := hL.le x hxS
    have h2 := hL.apart x o hxS ho hxo
    refine outs_wordsVal hk.mem (fun r hr => ?_) (by omega)
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h2
    · exact .inl h1
  refine ⟨hI.ws.of_keep (hk.gpr _ (by decide)) hk.wr, ?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ho
    · exact hI.sl x hx
  · intro x hx
    by_cases hxo : x = o
    · subst hxo; exact hr
    · have hx' := List.mem_of_ne_of_mem hxo hx
      rw [heq x hx' hxo]; exact hI.lt x hx'
  · intro x hx
    by_cases hxo : x = o
    · subst hxo; rw [Function.update_self]; exact hv
    · have hx' := List.mem_of_ne_of_mem hxo hx
      rw [heq x hx' hxo, Function.update_of_ne hxo]
      exact hI.val x hx'

/-- One operation. -/
theorem fop_ok {M : Mod} {base : Addr} {S : Impl.Weierstrass.Mont.Modulus} [NeZero S.m]
    (hM : ModOk S.k S.m) (hk : S.k = M.n) {Sl : Nat → Prop} (hL : Lay M (own M.n) Sl)
    (hm : UnitMod S.m (2 ^ (64 * M.n))) {V : List Nat} {E : Nat → Fin S.m} {s : State}
    (hI : Inv M.n base S.m Sl V E s) {op : FOp} (hS : ∀ x ∈ op.out :: op.ins, Sl x)
    (hR : ∀ x ∈ op.ins, x ∈ V) :
    WP isa (opCode S op) s fun s' =>
      KeepR M.n (fun x => x) base [op.out] s s' ∧ Inv M.n base S.m Sl (op.out :: V) (op.run E) s' := by
  have hle : ∀ x, Sl x → x + 8 * S.k ≤ own S.k := fun x hx => by rw [hk]; exact hL.le x hx
  cases op with
  | mul o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    refine WP.mono (mulCall_ok hM hI.ws (hle o hS.1) (hle a hS.2.1) (hle b hS.2.2)
        (by rw [hk]; exact hI.lt b hR.2))
      fun s' ⟨K, hlt, heq⟩ => ?_
    rw [hk] at K hlt heq
    refine ⟨.of_call K, hI.update hL hS.1 (.of_call K) hlt ?_⟩
    rw [toM_mul hm heq, hI.val a hR.1, hI.val b hR.2]
  | add o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    have hA := hI.lt a hR.1
    have hB := hI.lt b hR.2
    refine WP.mono (addCall_ok hM hI.ws (hle o hS.1) (hle a hS.2.1) (hle b hS.2.2)
        (by rw [hk]; omega))
      fun s' ⟨K, heq⟩ => ?_
    rw [hk] at K heq
    refine ⟨.of_call K, hI.update hL hS.1 (.of_call K) ?_ ?_⟩
    · rw [heq]; exact Nat.mod_lt _ (by omega)
    · rw [heq, toM_add, hI.val a hR.1, hI.val b hR.2]
  | sub o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    have hA := hI.lt a hR.1
    have hB := hI.lt b hR.2
    refine WP.mono (subCall_ok hM hI.ws (hle o hS.1) (hle a hS.2.1) (hle b hS.2.2)
        (by rw [hk]; exact hA) (by rw [hk]; exact hB))
      fun s' ⟨K, heq⟩ => ?_
    rw [hk] at K heq
    refine ⟨.of_call K, hI.update hL hS.1 (.of_call K) ?_ ?_⟩
    · rw [heq]; exact Nat.mod_lt _ (by omega)
    · rw [heq, toM_sub (by omega), hI.val a hR.1, hI.val b hR.2]

/-- A field program. -/
theorem fprog_ok {M : Mod} {base : Addr} {S : Impl.Weierstrass.Mont.Modulus} [NeZero S.m]
    (hM : ModOk S.k S.m) (hk : S.k = M.n) {Sl : Nat → Prop} (hL : Lay M (own M.n) Sl)
    (hm : UnitMod S.m (2 ^ (64 * M.n))) :
    ∀ (ops : List FOp) {V : List Nat} {E : Nat → Fin S.m} {s : State},
      Inv M.n base S.m Sl V E s → (∀ op ∈ ops, ∀ x ∈ op.out :: op.ins, Sl x) →
      readsOk ops V = true →
      WP isa (fprog S ops) s fun s' => KeepR M.n (fun x => x) base (ops.map FOp.out) s s' ∧
        Inv M.n base S.m Sl (validAfter ops V) (runOps ops E) s'
  | [], _, _, s, hI, _, _ => WP.block_nil ⟨KeepR.refl _ _ _ _ s, hI⟩
  | op :: ops, V, E, s, hI, hS, hR => by
    simp only [readsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hR
    refine Point.progs_wp _ _ (WP.mono (fop_ok hM hk hL hm hI (hS op (List.mem_cons_self ..)) hR.1)
      fun s₁ ⟨k₁, I₁⟩ => ?_)
    refine WP.mono (fprog_ok hM hk hL hm ops I₁ (fun op' h => hS op' (List.mem_cons_of_mem _ h)) hR.2)
      fun s₂ ⟨k₂, I₂⟩ => ⟨(k₁.mono fun w hw => ?_).trans (k₂.mono fun w hw => ?_), I₂⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      simp [hw]
    · simp [hw]

/-! ## The complete addition -/

/-- `o = p + q` by `rcb`, on slots of `Sl` that are apart (`RcbApart`; `p` may
be `q`), from a state holding `E`, in particular `p`, `q`, `a` and `3b`
(`rcbR`): `o` holds `rcbAdd` of their values, and the slots but those `rcb`
writes (`rcbW`) keep theirs. -/
theorem rcb_ok {M : Mod} {base : Addr} {S' : Impl.Weierstrass.Mont.Modulus} [NeZero S'.m]
    (hM : ModOk S'.k S'.m) (hk : S'.k = M.n) {Sl : Nat → Prop} (hL : Lay M (own M.n) Sl)
    (hm : UnitMod S'.m (2 ^ (64 * M.n))) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o)
    (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x) {V : List Nat} {E : Nat → Fin S'.m} {s : State}
    (hI : Inv M.n base S'.m Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (fprog S' (rcb S p q o)) s fun s' => KeepR M.n (fun x => x) base (rcbW S o) s s' ∧
      Inv M.n base S'.m Sl (rcbW S o ++ V) (runOps (rcb S p q o) E) s' ∧
      (runOps (rcb S p q o) E o.x, runOps (rcb S p q o) E o.y, runOps (rcb S p q o) E o.z) =
        VG.Proof.Weierstrass.rcbAdd (E S.a) (E S.b3) (E p.x) (E p.y) (E p.z) (E q.x) (E q.y)
          (E q.z) ∧
      ∀ x, x ∉ rcbW S o → runOps (rcb S p q o) E x = E x := by
  have hR : readsOk (rcb S p q o) V = true := by
    rw [rcb_eq_rename]
    exact readsOk_mono (readsOk_rename _ rcbN_reads) hV
  refine WP.mono (fprog_ok hM hk hL hm _ hI (fun op hop x hx => hSl x (rcb_slots op hop x hx)) hR)
    fun s' ⟨hk', hI'⟩ => ⟨hk'.mono fun w hw => ?_, hI'.sub fun x hx => ?_, rcb_run hA E,
      fun x hx => runOps_of_not_out _ _ fun op hop h => hx (h ▸ rcb_out op hop)⟩
  · obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw
    exact rcb_out op hop
  · rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (rcb_out_mem hx)
    · exact Or.inl hx

end VG.Proof.Weierstrass.PPC64LE

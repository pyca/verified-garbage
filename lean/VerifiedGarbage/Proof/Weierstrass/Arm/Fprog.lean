import VerifiedGarbage.Proof.Weierstrass.Env
import VerifiedGarbage.Impl.Weierstrass.Arm
import VerifiedGarbage.Proof.Mont.Arm.Ops
import VerifiedGarbage.Proof.Weierstrass.Arm.MontCall

/-!
# Field programs on 32-bit ARM

`fprog S ops` runs the field operations `ops` on slots of the working
space (`fprog_ok`), one by one by calls of the functions of the modulus `S`
(`mulCall_ok`, `addCall_ok` and `subCall_ok`, which `FnOk` lets compute
modulo `m`): on slots that are apart from each other, from the modulus and
from the temporary area (`Proof.Mont.Lay`), and below the functions' own
working space at `wk` (`WkOk`), what the slots stand for (`toM`) follows
`runOps ops`, the program on environments (`Inv`). A slot is read only once
it holds a number below `m`: either it did at the start (`V`) or an earlier
operation wrote it (`Proof.Weierstrass.readsOk`). Only the registers
`callClob`, the slots written, the temporary area and the functions' own
working space change (`ProgKeep`).

The complete addition `rcb` is such a program, and computes `rcbAdd`
(`rcb_ok`).
-/

namespace VG.Proof.Weierstrass.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass VG.Proof.Mont.Arm
  VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

/-- The functions of `S` compute modulo `m` on numbers of `M.n` words, with
their own working space at `wk`. -/
structure FnOk (M : Mod) (wk : Nat) (S : Spec.Weierstrass.Mont.Modulus) (m : Nat) : Prop where
  k : S.k = M.n
  m : S.m = m
  ok : Mont.ModOk S.k S.m
  wk : wk = Impl.Weierstrass.Arm.Mont.own M.n

/-- The functions' own working space at `wk`, in the working space above the
slots `Sl`, the modulus and the temporary area. -/
structure WkOk (M : Mod) (size wk : Nat) (Sl : Nat → Prop) : Prop where
  le : wk + 64 * M.n ≤ size
  sl : ∀ x, Sl x → x + 8 * M.n ≤ wk
  mo : M.mo + 8 * M.n ≤ wk
  tmp : M.tmp + 8 * M.n ≤ wk

/-- The state holds the environment `E` in Montgomery's form in the slots
`V`, below `m`, with the modulus in place, and the `8192` bytes of the
working space the functions take are writable. -/
structure Inv (M : Mod) (base : Addr) (size m : Nat) [NeZero m] (Sl : Nat → Prop) (V : List Nat)
    (E : Nat → Fin m) (s : State) : Prop where
  scr : Scr s base size
  mod : ModOkW M size m s.mem base
  sl : ∀ x ∈ V, Sl x
  lt : ∀ x ∈ V, wordsVal s.mem base x M.n < m
  val : ∀ x ∈ V, toM m (2 ^ (64 * M.n)) (wordsVal s.mem base x M.n) = E x
  far : Far s base 8192

theorem Inv.sub {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} {V V' : List Nat}
    {E : Nat → Fin m} {s : State} (h : Inv M base size m Sl V E s) (hV : ∀ x ∈ V', x ∈ V) :
    Inv M base size m Sl V' E s :=
  ⟨h.scr, h.mod, fun x hx => h.sl x (hV x hx), fun x hx => h.lt x (hV x hx),
    fun x hx => h.val x (hV x hx), h.far⟩

/-- The ranges a program writing the slots `W` may change: those slots, the
temporary area and the functions' own working space. -/
def progW (M : Mod) (wk : Nat) (W : List Nat) : List (Nat × Nat) :=
  W.map (·, 8 * M.n) ++ [(M.tmp, 8 * M.n), (wk, 64 * M.n)]

/-- What a program writing the slots `W` keeps: the registers but `callClob`,
the regions, and the memory but the slots `W`, the temporary area and the
functions' own working space. -/
structure ProgKeep (M : Mod) (base : Addr) (wk : Nat) (W : List Nat) (s s' : State) : Prop where
  rest : Rest Mont.callClob s s'
  mem : Outs base (progW M wk W) s.mem s'.mem

theorem ProgKeep.refl (M : Mod) (base : Addr) (wk : Nat) (W : List Nat) (s : State) :
    ProgKeep M base wk W s s :=
  ⟨Rest.refl _ _, Outs.refl _ _ _⟩

theorem progW_mono {M : Mod} {wk : Nat} {W W' : List Nat} (hW : ∀ w ∈ W, w ∈ W') :
    ∀ r ∈ progW M wk W, r ∈ progW M wk W' := by
  intro r hr
  simp only [progW, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with ⟨w, hw, rfl⟩ | h
  · exact .inl ⟨w, hW w hw, rfl⟩
  · exact .inr h

theorem ProgKeep.mono {M : Mod} {base : Addr} {wk : Nat} {W W' : List Nat} {s s' : State}
    (h : ProgKeep M base wk W s s') (hW : ∀ w ∈ W, w ∈ W') : ProgKeep M base wk W' s s' :=
  ⟨h.rest, h.mem.mono (progW_mono hW)⟩

theorem ProgKeep.trans {M : Mod} {base : Addr} {wk : Nat} {W : List Nat} {s₁ s₂ s₃ : State}
    (h₁ : ProgKeep M base wk W s₁ s₂) (h₂ : ProgKeep M base wk W s₂ s₃) : ProgKeep M base wk W s₁ s₃ :=
  ⟨h₁.rest.trans h₂.rest, h₁.mem.trans h₂.mem⟩

theorem ProgKeep.scr {M : Mod} {base : Addr} {wk : Nat} {W : List Nat} {s s' : State} {size : Nat}
    (h : ProgKeep M base wk W s s') (hs : Scr s base size) : Scr s' base size :=
  hs.of_rest h.rest (by decide)

theorem ProgKeep.unch {M : Mod} {base : Addr} {wk : Nat} {W : List Nat} {s s' : State}
    (h : ProgKeep M base wk W s s') : VG.Proof.Weierstrass.Unch base (progW M wk W) s.mem s'.mem := h.mem

/-- A call's frame, as a program's. -/
theorem ProgKeep.of_call {M : Mod} {base : Addr} {wk o : Nat} {S : Spec.Weierstrass.Mont.Modulus} {m : Nat}
    (hF : FnOk M wk S m) {s s' : State} (h : Mont.CallKeep S.k base o s s') : ProgKeep M base wk [o] s s' :=
  ⟨h.rest, h.mem.mono (by
    intro r hr
    rw [hF.k, ← hF.wk] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [progW, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rcases hr with rfl | rfl <;> simp)⟩

/-- A slot apart from what a program writes keeps its number. -/
theorem ProgKeep.wordsVal {M : Mod} {base : Addr} {wk : Nat} {W : List Nat} {s s' : State} {size : Nat}
    (h : ProgKeep M base wk W s s') (hn : base.toNat + size ≤ 2 ^ 32) {y : Nat} (hy : y + 8 * M.n ≤ size)
    (hW : ∀ w ∈ W, y + 8 * M.n ≤ w ∨ w + 8 * M.n ≤ y) (ht : y + 8 * M.n ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ y)
    (hk : y + 8 * M.n ≤ wk) :
    VG.Proof.Mont.wordsVal s'.mem base y M.n = VG.Proof.Mont.wordsVal s.mem base y M.n := by
  refine Outs.wordsVal h.mem (fun r hr => ?_) (by omega)
  simp only [progW, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with ⟨w, hw, rfl⟩ | rfl | rfl
  · exact hW w hw
  · exact ht
  · exact .inl hk

/-- An operation writing `o`, which then holds `v`, keeps the invariant. -/
theorem Inv.update {M : Mod} {base : Addr} {size m wk : Nat} [NeZero m] {Sl : Nat → Prop}
    (hL : Lay M size Sl) (hW : WkOk M size wk Sl)
    {V : List Nat} {E : Nat → Fin m} {s s' : State} (hI : Inv M base size m Sl V E s) {o : Nat}
    (ho : Sl o) (hk : ProgKeep M base wk [o] s s') (hr : wordsVal s'.mem base o M.n < m) {v : Fin m}
    (hv : toM m (2 ^ (64 * M.n)) (wordsVal s'.mem base o M.n) = v) :
    Inv M base size m Sl (o :: V) (Function.update E o v) s' := by
  have hn := hI.scr.nowrap
  have hM := hI.mod
  have heq : ∀ x, Sl x → x ≠ o → wordsVal s'.mem base x M.n = wordsVal s.mem base x M.n :=
    fun x hx hxo => hk.wordsVal hn (hL.le x hx)
      (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        subst hw; exact hL.apart x w hx ho hxo)
      (hL.tmp x hx) (hW.sl x hx)
  refine ⟨hk.scr hI.scr, ⟨hM.n0, hM.mo, hM.tmp, hM.sep, ?_, hM.inv, hM.red⟩, ?_, ?_, ?_,
    hI.far.of_rest hk.rest⟩
  · have := hW.mo
    rw [hk.wordsVal hn hM.mo (fun w hw => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        subst hw; have := hL.mo w ho; omega) hM.sep hW.mo]
    exact hM.val
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ho
    · exact hI.sl x hx
  · intro x hx
    by_cases hxo : x = o
    · subst hxo; exact hr
    · rw [heq x (hI.sl x (List.mem_of_ne_of_mem hxo hx)) hxo]
      exact hI.lt x (List.mem_of_ne_of_mem hxo hx)
  · intro x hx
    by_cases hxo : x = o
    · subst hxo; rw [Function.update_self]; exact hv
    · have hx' := List.mem_of_ne_of_mem hxo hx
      rw [heq x (hI.sl x hx') hxo, Function.update_of_ne hxo]
      exact hI.val x hx'

/-- What a program writing one slot changes, as a list. -/
theorem ProgKeep.unchOne {M : Mod} {base : Addr} {wk o : Nat} {s s' : State} (h : ProgKeep M base wk [o] s s') :
    VG.Proof.Weierstrass.Unch base [(o, 8 * M.n), (M.tmp, 8 * M.n), (wk, 64 * M.n)] s.mem s'.mem := h.mem

/-- A number below the functions' own working space, in their terms. -/
theorem FnOk.fits {M : Mod} {wk : Nat} {S : Spec.Weierstrass.Mont.Modulus} {m : Nat} (hF : FnOk M wk S m)
    {x : Nat} (hx : x + 8 * M.n ≤ wk) : x + 8 * S.k ≤ Impl.Weierstrass.Arm.Mont.own S.k := by
  rw [hF.k, ← hF.wk]; exact hx

/-- The slots of an operation, in the functions' terms. -/
theorem fnSl {M : Mod} {size wk : Nat} {Sl : Nat → Prop} (hW : WkOk M size wk Sl)
    {S : Spec.Weierstrass.Mont.Modulus} {m : Nat} (hF : FnOk M wk S m) {x : Nat} (hx : Sl x) :
    x + 8 * S.k ≤ Impl.Weierstrass.Arm.Mont.own S.k :=
  hF.fits (hW.sl x hx)

/-- One operation. -/
theorem fop_ok {M : Mod} {base : Addr} {size m wk : Nat} [NeZero m] {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hW : WkOk M size wk Sl) {S : Spec.Weierstrass.Mont.Modulus} (hF : FnOk M wk S m)
    (hm : UnitMod m (2 ^ (64 * M.n))) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) {op : FOp} (hS : ∀ x ∈ op.out :: op.ins, Sl x)
    (hR : ∀ x ∈ op.ins, x ∈ V) :
    WP isa (opCode S op) s fun s' =>
      ProgKeep M base wk [op.out] s s' ∧ Inv M base size m Sl (op.out :: V) (op.run E) s' := by
  have hk := hF.k
  have hmm := hF.m
  cases op with
  | mul o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    refine WP.mono (Mont.mulCall_ok hF.ok hI.scr hI.far (fnSl hW hF hS.1) (fnSl hW hF hS.2.1) (fnSl hW hF hS.2.2)
        (by rw [hk, hmm]; exact hI.lt b hR.2))
      fun s' ⟨K, hlt, heq⟩ => ?_
    rw [hk, hmm] at hlt heq
    refine ⟨.of_call hF K, hI.update hL hW hS.1 (.of_call hF K) hlt ?_⟩
    rw [toM_mul hm heq, hI.val a hR.1, hI.val b hR.2]
  | add o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    have hA := hI.lt a hR.1
    have hB := hI.lt b hR.2
    refine WP.mono (Mont.addCall_ok hF.ok hI.scr hI.far (fnSl hW hF hS.1) (fnSl hW hF hS.2.1) (fnSl hW hF hS.2.2)
        (by rw [hk, hmm]; omega))
      fun s' ⟨K, heq⟩ => ?_
    rw [hk, hmm] at heq
    refine ⟨.of_call hF K, hI.update hL hW hS.1 (.of_call hF K) ?_ ?_⟩
    · rw [heq]; exact Nat.mod_lt _ (by omega)
    · rw [heq, toM_add, hI.val a hR.1, hI.val b hR.2]
  | sub o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    have hA := hI.lt a hR.1
    have hB := hI.lt b hR.2
    refine WP.mono (Mont.subCall_ok hF.ok hI.scr hI.far (fnSl hW hF hS.1) (fnSl hW hF hS.2.1) (fnSl hW hF hS.2.2)
        (by rw [hk, hmm]; exact hA) (by rw [hk, hmm]; exact hB))
      fun s' ⟨K, heq⟩ => ?_
    rw [hk, hmm] at heq
    refine ⟨.of_call hF K, hI.update hL hW hS.1 (.of_call hF K) ?_ ?_⟩
    · rw [heq]; exact Nat.mod_lt _ (by omega)
    · rw [heq, toM_sub (by omega), hI.val a hR.1, hI.val b hR.2]

theorem progs_wp (p : Prog isa) (ps : List (Prog isa)) {s : State} {Q : State → Prop}
    (h : WP isa p s fun s' => WP isa (progs ps) s' Q) : WP isa (progs (p :: ps)) s Q := by
  cases ps with
  | nil => exact WP.mono h fun _ h' => WP.block_nil_iff.mp h'
  | cons p' ps' => exact WP.seq h

/-- A field program. -/
theorem fprog_ok {M : Mod} {base : Addr} {size m wk : Nat} [NeZero m] {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hW : WkOk M size wk Sl) {S : Spec.Weierstrass.Mont.Modulus} (hF : FnOk M wk S m)
    (hm : UnitMod m (2 ^ (64 * M.n))) :
    ∀ (ops : List FOp) {V : List Nat} {E : Nat → Fin m} {s : State},
      Inv M base size m Sl V E s → (∀ op ∈ ops, ∀ x ∈ op.out :: op.ins, Sl x) →
      readsOk ops V = true →
      WP isa (fprog S ops) s fun s' => ProgKeep M base wk (ops.map FOp.out) s s' ∧
        Inv M base size m Sl (validAfter ops V) (runOps ops E) s'
  | [], _, _, s, hI, _, _ => WP.block_nil ⟨ProgKeep.refl _ _ _ _ s, hI⟩
  | op :: ops, V, E, s, hI, hS, hR => by
    simp only [readsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hR
    refine progs_wp _ _ (WP.mono (fop_ok hL hW hF hm hI (hS op (List.mem_cons_self ..)) hR.1)
      fun s₁ ⟨k₁, I₁⟩ => ?_)
    refine WP.mono (fprog_ok hL hW hF hm ops I₁ (fun op' h => hS op' (List.mem_cons_of_mem _ h)) hR.2)
      fun s₂ ⟨k₂, I₂⟩ => ⟨(k₁.mono fun w hw => ?_).trans (k₂.mono fun w hw => ?_), I₂⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      simp [hw]
    · simp [hw]

/-! ## The complete addition -/

/-- `o = p + q` by `rcb`, on slots of `Sl` that are apart (`RcbApart`; `p` may
be `q`), from a state holding `E`, in particular `p`, `q`, `a` and `3b`
(`rcbR`): `o` holds `rcbAdd` of their values, and the slots but those `rcb`
writes (`rcbW`) keep theirs. -/
theorem rcb_ok {M : Mod} {base : Addr} {size m wk : Nat} [NeZero m] {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hW : WkOk M size wk Sl) {S' : Spec.Weierstrass.Mont.Modulus} (hF : FnOk M wk S' m)
    (hm : UnitMod m (2 ^ (64 * M.n))) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o)
    (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (fprog S' (rcb S p q o)) s fun s' => ProgKeep M base wk (rcbW S o) s s' ∧
      Inv M base size m Sl (rcbW S o ++ V) (runOps (rcb S p q o) E) s' ∧
      (runOps (rcb S p q o) E o.x, runOps (rcb S p q o) E o.y, runOps (rcb S p q o) E o.z) =
        VG.Proof.Weierstrass.rcbAdd (E S.a) (E S.b3) (E p.x) (E p.y) (E p.z) (E q.x) (E q.y)
          (E q.z) ∧
      ∀ x, x ∉ rcbW S o → runOps (rcb S p q o) E x = E x := by
  have hR : readsOk (rcb S p q o) V = true := by
    rw [rcb_eq_rename]
    exact readsOk_mono (readsOk_rename _ rcbN_reads) hV
  refine WP.mono (fprog_ok hL hW hF hm _ hI (fun op hop x hx => hSl x (rcb_slots op hop x hx)) hR)
    fun s' ⟨hk, hI'⟩ => ⟨hk.mono fun w hw => ?_, hI'.sub fun x hx => ?_, rcb_run hA E,
      fun x hx => runOps_of_not_out _ _ fun op hop h => hx (h ▸ rcb_out op hop)⟩
  · obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw
    exact rcb_out op hop
  · rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (rcb_out_mem hx)
    · exact Or.inl hx

end VG.Proof.Weierstrass.Arm

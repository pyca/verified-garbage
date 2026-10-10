import VerifiedGarbage.Proof.Weierstrass.Arm.PointCall
import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
import VerifiedGarbage.Proof.Weierstrass.Arm.Fprog

/-!
# Field programs on slots at offsets known at run time, on 32-bit ARM

`fprogR σ S ops` (`Impl/Weierstrass/Arm/Point.lean`) runs the field
operations `ops`, on slots named by number, each slot `x` at the offset
`σ x`, by calls of the functions of the modulus `S`. As `fprog_ok`
(`Fprog.lean`), what the slots stand for (`toM`) follows `runOps ops`
(`fprogR_ok`), but the offsets may coincide: only the slots the program
writes (`W`) must be apart from every other (`LayR`), so that two slots it
only reads may be one (a point doubled). `rcbR_ok` is the complete
addition.
-/

namespace VG.Proof.Weierstrass.Arm.Point

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass.Arm.Mont
open VG.Impl.Weierstrass VG.Impl.Weierstrass.Arm.Point
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
  VG.Proof.Weierstrass.Arm.Mont
open VG.Proof.X25519.Arm (Rest)

/-- The slots `x < N` at offsets `σ x` of numbers of `k` words: below the
functions' own working space, and each of `W` apart from every other. -/
structure LayR (k N : Nat) (W : List Nat) (σ : Nat → Nat) : Prop where
  le : ∀ x < N, σ x + 8 * k ≤ own k
  apart : ∀ w ∈ W, ∀ x < N, x ≠ w → σ x + 8 * k ≤ σ w ∨ σ w + 8 * k ≤ σ x

/-- The state holds the environment `E` in Montgomery's form in the slots `V`
(below `N`), below `m`, and the working space at `r12` has its `8192` bytes
writable. -/
structure InvR (k N : Nat) (σ : Nat → Nat) (base : Addr) (m : Nat) [NeZero m]
    (V : List Nat) (E : Nat → Fin m) (s : State) : Prop where
  scr : Scr s base 4096
  far : Far s base 8192
  ids : ∀ x ∈ V, x < N
  lt : ∀ x ∈ V, wordsVal s.mem base (σ x) k < m
  val : ∀ x ∈ V, toM m (2 ^ (64 * k)) (wordsVal s.mem base (σ x) k) = E x

/-- What a program writing the slots `W` keeps: the registers but `r0`–`r3`,
`r12` and `lr`, `r12` itself, the regions, and the memory but the slots `W`
and the functions' own working space. -/
structure KeepR (k : Nat) (σ : Nat → Nat) (base : Addr) (W : List Nat) (s s' : State) : Prop where
  rest : Rest [.r0, .r1, .r2, .r3, .r12, .lr] s s'
  r12 : s'.gpr .r12 = s.gpr .r12
  mem : Outs base (W.map (fun w => (σ w, 8 * k)) ++ [(own k, 64 * k)]) s.mem s'.mem

theorem KeepR.refl (k : Nat) (σ : Nat → Nat) (base : Addr) (W : List Nat) (s : State) : KeepR k σ base W s s :=
  ⟨Rest.refl _ _, rfl, Outs.refl _ _ _⟩

theorem KeepR.trans {k : Nat} {σ : Nat → Nat} {base : Addr} {W : List Nat} {s₁ s₂ s₃ : State}
    (h₁ : KeepR k σ base W s₁ s₂) (h₂ : KeepR k σ base W s₂ s₃) : KeepR k σ base W s₁ s₃ :=
  ⟨h₁.rest.trans h₂.rest, h₂.r12.trans h₁.r12, h₁.mem.trans h₂.mem⟩

theorem KeepR.mono {k : Nat} {σ : Nat → Nat} {base : Addr} {W W' : List Nat} {s s' : State}
    (h : KeepR k σ base W s s') (hW : ∀ w ∈ W, w ∈ W') : KeepR k σ base W' s s' :=
  ⟨h.rest, h.r12, h.mem.mono fun r hr => by
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hr ⊢
    rcases hr with ⟨w, hw, rfl⟩ | rfl
    · exact .inl ⟨w, hW w hw, rfl⟩
    · exact .inr rfl⟩

/-- A call's frame, as a program's. -/
theorem KeepR.of_call {k : Nat} {σ : Nat → Nat} {base : Addr} {o : Nat} {s s' : State}
    (h : CallKeepR k base (σ o) s s') : KeepR k σ base [o] s s' :=
  ⟨h.rest, h.r12, h.mem.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rcases hr with rfl | rfl <;> simp)⟩

/-- An operation writing `o`, which then holds `v`, keeps the invariant. -/
theorem InvR.update {k N : Nat} {σ : Nat → Nat} {base : Addr} {m : Nat} [NeZero m]
    {W : List Nat} (hL : LayR k N W σ) {V : List Nat} {E : Nat → Fin m} {s s' : State}
    (hI : InvR k N σ base m V E s) {o : Nat} (hoW : o ∈ W) (hoN : o < N) (hk : KeepR k σ base [o] s s')
    (hr : wordsVal s'.mem base (σ o) k < m) {v : Fin m}
    (hv : toM m (2 ^ (64 * k)) (wordsVal s'.mem base (σ o) k) = v) :
    InvR k N σ base m (o :: V) (Function.update E o v) s' := by
  have hn := hI.scr.nowrap
  have hown : own k ≤ 4096 := Nat.sub_le _ _
  have heq : ∀ x ∈ V, x ≠ o → wordsVal s'.mem base (σ x) k = wordsVal s.mem base (σ x) k := by
    intro x hx hxo
    have hxN := hI.ids x hx
    have h1 := hL.le x hxN
    have h2 := hL.apart o hoW x hxN hxo
    refine Outs.wordsVal hk.mem (fun r hr => ?_) (by have := hI.far.nowrap; omega)
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h2
    · exact .inl h1
  refine ⟨⟨by rw [hk.r12]; exact hI.scr.wb, hk.rest.wr ▸ hI.scr.wr, hI.scr.nowrap, hI.scr.small⟩,
    hI.far.of_rest hk.rest, ?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hoN
    · exact hI.ids x hx
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
theorem fopR_ok {k N : Nat} {σ : Nat → Nat} {base : Addr} {S : Spec.Weierstrass.Mont.Modulus}
    [NeZero S.m] (hM : ModOk S.k S.m) (hk : S.k = k) {W : List Nat} (hL : LayR k N W σ)
    (hm : UnitMod S.m (2 ^ (64 * k))) {V : List Nat} {E : Nat → Fin S.m} {s : State}
    (hI : InvR k N σ base S.m V E s) {op : FOp} (hW : op.out ∈ W) (hN : ∀ x ∈ op.out :: op.ins, x < N)
    (hR : ∀ x ∈ op.ins, x ∈ V) :
    WP isa (opCodeR σ S op) s fun s' =>
      KeepR k σ base [op.out] s s' ∧ InvR k N σ base S.m (op.out :: V) (op.run E) s' := by
  subst hk
  cases op with
  | mul o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hW hN hR
    refine WP.mono (mulCallR_ok (enc := σ) hM hI.scr hI.far (hL.le o hN.1) (hL.le a hN.2.1) (hL.le b hN.2.2)
        (hI.lt b hR.2))
      fun s' ⟨K, hlt, heq⟩ => ?_
    refine ⟨.of_call K, hI.update hL hW hN.1 (.of_call K) hlt ?_⟩
    rw [toM_mul hm heq, hI.val a hR.1, hI.val b hR.2]
  | add o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hW hN hR
    have hA := hI.lt a hR.1
    have hB := hI.lt b hR.2
    refine WP.mono (addCallR_ok (enc := σ) hM hI.scr hI.far (hL.le o hN.1) (hL.le a hN.2.1) (hL.le b hN.2.2)
        (by omega))
      fun s' ⟨K, heq⟩ => ?_
    refine ⟨.of_call K, hI.update hL hW hN.1 (.of_call K) ?_ ?_⟩
    · rw [heq]; exact Nat.mod_lt _ (by omega)
    · rw [heq, toM_add, hI.val a hR.1, hI.val b hR.2]
  | sub o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hW hN hR
    have hA := hI.lt a hR.1
    have hB := hI.lt b hR.2
    refine WP.mono (subCallR_ok (enc := σ) hM hI.scr hI.far (hL.le o hN.1) (hL.le a hN.2.1) (hL.le b hN.2.2)
        hA hB)
      fun s' ⟨K, heq⟩ => ?_
    refine ⟨.of_call K, hI.update hL hW hN.1 (.of_call K) ?_ ?_⟩
    · rw [heq]; exact Nat.mod_lt _ (by omega)
    · rw [heq, toM_sub (by omega), hI.val a hR.1, hI.val b hR.2]

/-- A field program. -/
theorem fprogR_ok {k N : Nat} {σ : Nat → Nat} {base : Addr} {S : Spec.Weierstrass.Mont.Modulus}
    [NeZero S.m] (hM : ModOk S.k S.m) (hk : S.k = k) {W : List Nat} (hL : LayR k N W σ)
    (hm : UnitMod S.m (2 ^ (64 * k))) :
    ∀ (ops : List FOp) {V : List Nat} {E : Nat → Fin S.m} {s : State},
      InvR k N σ base S.m V E s → (∀ op ∈ ops, op.out ∈ W ∧ ∀ x ∈ op.out :: op.ins, x < N) →
      readsOk ops V = true →
      WP isa (fprogR σ S ops) s fun s' => KeepR k σ base (ops.map FOp.out) s s' ∧
        InvR k N σ base S.m (validAfter ops V) (runOps ops E) s'
  | [], _, _, s, hI, _, _ => WP.block_nil ⟨KeepR.refl _ _ _ _ s, hI⟩
  | op :: ops, V, E, s, hI, hS, hR => by
    simp only [readsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hR
    have hop := hS op (List.mem_cons_self ..)
    refine progs_wp _ _ (WP.mono (fopR_ok hM hk hL hm hI hop.1 hop.2 hR.1) fun s₁ ⟨k₁, I₁⟩ => ?_)
    refine WP.mono (fprogR_ok hM hk hL hm ops I₁ (fun op' h => hS op' (List.mem_cons_of_mem _ h)) hR.2)
      fun s₂ ⟨k₂, I₂⟩ => ⟨(k₁.mono fun w hw => ?_).trans (k₂.mono fun w hw => ?_), I₂⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      simp [hw]
    · simp [hw]

/-! ## The complete addition -/

/-- The slots the function's addition writes: the result's and the
temporaries. -/
def wIds : List Nat := [0, 1, 2, 11, 12, 13, 14, 15, 16]

/-- The slots it reads first: `p`, `q`, `a` and `3b`. -/
def rIds : List Nat := [3, 4, 5, 6, 7, 8, 9, 10]

theorem rcbIds_ok : ∀ op ∈ rcb sId pId qId oId, op.out ∈ wIds ∧ ∀ x ∈ op.out :: op.ins, x < 17 := by
  decide

theorem rcbIds_reads : readsOk (rcb sId pId qId oId) rIds = true := by decide

theorem rcbIds_apart : RcbApart sId pId qId oId := ⟨by decide, by decide⟩

/-- `o = p + q` by `rcb` on the slots numbered as the function numbers them,
from a state holding `E` in `p`, `q`, `a` and `3b`: `o` holds `rcbAdd` of
their values. -/
theorem rcbR_ok {k : Nat} {σ : Nat → Nat} {base : Addr} {S : Spec.Weierstrass.Mont.Modulus}
    [NeZero S.m] (hM : ModOk S.k S.m) (hk : S.k = k) (hL : LayR k 17 wIds σ)
    (hm : UnitMod S.m (2 ^ (64 * k))) {E : Nat → Fin S.m} {s : State}
    (hI : InvR k 17 σ base S.m rIds E s) :
    WP isa (fprogR σ S (rcb sId pId qId oId)) s fun s' => KeepR k σ base wIds s s' ∧
      InvR k 17 σ base S.m (validAfter (rcb sId pId qId oId) rIds) (runOps (rcb sId pId qId oId) E) s' ∧
      (runOps (rcb sId pId qId oId) E 0, runOps (rcb sId pId qId oId) E 1, runOps (rcb sId pId qId oId) E 2) =
        VG.Proof.Weierstrass.rcbAdd (E 9) (E 10) (E 3) (E 4) (E 5) (E 6) (E 7) (E 8) := by
  refine WP.mono (fprogR_ok hM hk hL hm _ hI rcbIds_ok rcbIds_reads) fun s' ⟨hk', hI'⟩ =>
    ⟨hk'.mono fun w hw => ?_, hI', rcb_run rcbIds_apart E⟩
  obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw
  exact (rcbIds_ok op hop).1

end VG.Proof.Weierstrass.Arm.Point

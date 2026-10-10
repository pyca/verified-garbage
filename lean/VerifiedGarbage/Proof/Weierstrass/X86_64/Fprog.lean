import VerifiedGarbage.Proof.Weierstrass.Env
import VerifiedGarbage.Impl.Weierstrass.X86_64
import VerifiedGarbage.Proof.Mont.X86_64.Ops
import VerifiedGarbage.Proof.Weierstrass.X86_64.MontCall

/-!
# Field programs on x86-64

`fprog M ops` runs the field operations `ops` on slots of the working space
(`fprog_ok`), one by one with `mul_ok`, `add_ok` and `sub_ok`: on slots that
are apart from each other, from the modulus and from the temporary area
(`Proof.Mont.Lay`), what the slots stand for (`toM`) follows `runOps ops`, the program
on environments (`Inv`). A slot is read only once it holds a number below
`m`: either it did at the start (`V`) or an earlier operation wrote it
(`Proof.Weierstrass.readsOk`). Only the registers `clob n`, the slots written and the temporary
area change (`ProgKeep`).

The complete additions `rcb` and, for `a = -3`, `rcb3` are such programs,
and compute `rcbAdd` and `rcbAdd3` (`rcb_ok`, `rcb3_ok`).
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Proof.Mont.X86_64 VG.Proof.Mont

/-- The state holds the environment `E` in Montgomery's form in the slots
`V`, below `m`, with the modulus in place. -/
structure Inv (M : Mod) (base : Addr) (size m : Nat) [NeZero m] (Sl : Nat → Prop) (V : List Nat)
    (E : Nat → Fin m) (s : State) : Prop where
  scr : Scr s base size
  mod : ModOkW M size m s.mem base
  sl : ∀ x ∈ V, Sl x
  lt : ∀ x ∈ V, wordsVal s.mem base x M.n < m
  val : ∀ x ∈ V, toM m (2 ^ (64 * M.n)) (wordsVal s.mem base x M.n) = E x

theorem Inv.sub {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} {V V' : List Nat}
    {E : Nat → Fin m} {s : State} (h : Inv M base size m Sl V E s) (hV : ∀ x ∈ V', x ∈ V) :
    Inv M base size m Sl V' E s :=
  ⟨h.scr, h.mod, fun x hx => h.sl x (hV x hx), fun x hx => h.lt x (hV x hx),
    fun x hx => h.val x (hV x hx)⟩

/-- What a program writing the slots `W` keeps: the registers but `clob`,
the regions, and the memory but the slots `W` and the temporary area. -/
structure ProgKeep (M : Mod) (base : Addr) (W : List Nat) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ clob M.n → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : ∀ x, (∀ w ∈ W, ofs base x < w ∨ w + 8 * M.n ≤ ofs base x) →
    (ofs base x < M.tmp ∨ M.tmp + 8 * M.n ≤ ofs base x) → s'.mem x = s.mem x

/-- `Inv` and `ProgKeep` do not depend on whether the products are written
out (`Mod.inl`). -/
theorem Inv.inl {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} {V : List Nat}
    {E : Nat → Fin m} {s : State} (b : Bool) (h : Inv M base size m Sl V E s) :
    Inv { M with inl := b } base size m Sl V E s :=
  ⟨h.scr, h.mod.inl b, h.sl, h.lt, h.val⟩

theorem Inv.of_inl {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} {V : List Nat}
    {E : Nat → Fin m} {s : State} {b : Bool} (h : Inv { M with inl := b } base size m Sl V E s) :
    Inv M base size m Sl V E s :=
  ⟨h.scr, h.mod.of_inl, h.sl, h.lt, h.val⟩

theorem ProgKeep.of_inl {M : Mod} {base : Addr} {W : List Nat} {s s' : State} {b : Bool}
    (h : ProgKeep { M with inl := b } base W s s') : ProgKeep M base W s s' :=
  ⟨h.gpr, h.rd, h.wr, h.mem⟩

theorem ProgKeep.refl (M : Mod) (base : Addr) (W : List Nat) (s : State) : ProgKeep M base W s s :=
  ⟨fun _ _ => rfl, rfl, rfl, fun _ _ _ => rfl⟩

theorem ProgKeep.mono {M : Mod} {base : Addr} {W W' : List Nat} {s s' : State}
    (h : ProgKeep M base W s s') (hW : ∀ w ∈ W, w ∈ W') : ProgKeep M base W' s s' :=
  ⟨h.gpr, h.rd, h.wr, fun x hx ht => h.mem x (fun w hw => hx w (hW w hw)) ht⟩

theorem rdi_not_clob (n : Nat) : Reg.rdi ∉ clob n := by
  intro h
  rcases List.mem_append.mp h with h | h
  swap
  · split at h <;> simp at h
  simp only [List.mem_cons] at h
  rcases h with h | h | h | h | h
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · have := List.mem_of_mem_take h
    simp only [List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self] at this

theorem ProgKeep.scr {M : Mod} {base : Addr} {W : List Nat} {s s' : State} {size : Nat}
    (h : ProgKeep M base W s s') (hs : Scr s base size) : Scr s' base size :=
  ⟨(h.gpr _ (rdi_not_clob _)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

/-- A number in memory apart from what an operation writes. -/
theorem opKeep_wordsVal {M : Mod} {base : Addr} {o : Nat} {s s' : State}
    (h : OpKeep M base o s s') : ∀ {k y : Nat}, (y + 8 * k ≤ o ∨ o + 8 * M.n ≤ y) →
      (y + 8 * k ≤ M.tmp ∨ M.tmp + 8 * M.n ≤ y) → y + 8 * k ≤ 2 ^ 64 →
      wordsVal s'.mem base y k = wordsVal s.mem base y k
  | 0, _, _, _, _ => rfl
  | k + 1, y, ho, ht, hy => by
    simp only [wordsVal]
    have hw : word s'.mem base y = word s.mem base y :=
      Mem.readW_congr fun i hi => h.mem _ (by rw [ofs_off base (by omega)]; omega)
        (by rw [ofs_off base (by omega)]; omega)
    rw [opKeep_wordsVal h (k := k) (y := y + 8) (by omega) (by omega) (by omega), hw]

/-- An operation writing `o`, which then holds `v`, keeps the invariant. -/
theorem Inv.update {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} (hL : Lay M size Sl)
    {V : List Nat} {E : Nat → Fin m} {s s' : State} (hI : Inv M base size m Sl V E s) {o : Nat}
    (ho : Sl o) (hk : OpKeep M base o s s') (hr : wordsVal s'.mem base o M.n < m) {v : Fin m}
    (hv : toM m (2 ^ (64 * M.n)) (wordsVal s'.mem base o M.n) = v) :
    Inv M base size m Sl (o :: V) (Function.update E o v) s' := by
  have hn := hI.scr.nowrap
  have hlo := hL.le o ho
  have hmo := hL.mo o ho
  have hto := hL.tmp o ho
  have hM := hI.mod
  have heq : ∀ x, Sl x → x ≠ o → wordsVal s'.mem base x M.n = wordsVal s.mem base x M.n :=
    fun x hx hxo => by
      have := hL.apart x o hx ho hxo
      have := hL.tmp x hx
      have := hL.le x hx
      exact opKeep_wordsVal hk (by omega) (by omega) (by omega)
  refine ⟨⟨(hk.gpr _ (rdi_not_clob _)).trans hI.scr.rdi, hk.wr ▸ hI.scr.wr, hn⟩,
    ⟨hM.n0, hM.mo, hM.tmp, hM.sep, ?_, hM.inv, hM.red⟩, ?_, ?_, ?_⟩
  · have := hM.mo
    have := hM.sep
    rw [opKeep_wordsVal hk (by omega) (by omega) (by omega)]
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

/-- One operation. -/
theorem fop_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hm : UnitMod m (2 ^ (64 * M.n))) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) {op : FOp} (hS : ∀ x ∈ op.out :: op.ins, Sl x)
    (hR : ∀ x ∈ op.ins, x ∈ V) :
    WP isa (.block (opCode M op)) s fun s' =>
      OpKeep M base op.out s s' ∧ Inv M base size m Sl (op.out :: V) (op.run E) s' := by
  cases op with
  | mul o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    refine WP.mono (mul_ok hI.scr hI.mod (hL.le o hS.1) (hL.le a hS.2.1) (hL.le b hS.2.2)
      (hL.tmp o hS.1) (hL.tmp a hS.2.1) (hL.tmp b hS.2.2) (hL.mo o hS.1) (hI.lt b hR.2)) fun s' ⟨hk, hlt, heq⟩ => ⟨hk, hI.update hL hS.1 hk hlt ?_⟩
    rw [toM_mul hm heq, hI.val a hR.1, hI.val b hR.2]
  | add o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    have hA := hI.lt a hR.1
    have hB := hI.lt b hR.2
    refine WP.mono (add_ok hI.scr hI.mod (hL.le o hS.1) (hL.le a hS.2.1) (hL.le b hS.2.2)
      (hL.tmp o hS.1) (hL.tmp a hS.2.1) (hL.tmp b hS.2.2) (hL.mo o hS.1) (by omega)) fun s' ⟨hk, heq⟩ => ⟨hk, hI.update hL hS.1 hk ?_ ?_⟩
    · rw [heq]; exact Nat.mod_lt _ (by omega)
    · rw [heq, toM_add, hI.val a hR.1, hI.val b hR.2]
  | sub o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    have hA := hI.lt a hR.1
    have hB := hI.lt b hR.2
    refine WP.mono (sub_ok hI.scr hI.mod (hL.le o hS.1) (hL.le a hS.2.1) (hL.le b hS.2.2)
      (hL.tmp o hS.1) (hL.tmp a hS.2.1) (hL.tmp b hS.2.2) (hL.mo o hS.1) hA hB)
      fun s' ⟨hk, heq⟩ => ⟨hk, hI.update hL hS.1 hk ?_ ?_⟩
    · rw [heq]; exact Nat.mod_lt _ (by omega)
    · rw [heq, toM_sub (by omega), hI.val a hR.1, hI.val b hR.2]

theorem fprog_cons (M : Mod) (op : FOp) (ops : List FOp) :
    fprog M (op :: ops) = opCode M op ++ fprog M ops := rfl

/-- A field program. -/
theorem fprog_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hm : UnitMod m (2 ^ (64 * M.n))) :
    ∀ (ops : List FOp) {V : List Nat} {E : Nat → Fin m} {s : State},
      Inv M base size m Sl V E s → (∀ op ∈ ops, ∀ x ∈ op.out :: op.ins, Sl x) →
      readsOk ops V = true →
      WP isa (.block (fprog M ops)) s fun s' => ProgKeep M base (ops.map FOp.out) s s' ∧
        Inv M base size m Sl (validAfter ops V) (runOps ops E) s'
  | [], _, _, s, hI, _, _ => WP.block_nil ⟨ProgKeep.refl _ _ _ s, hI⟩
  | op :: ops, V, E, s, hI, hS, hR => by
    simp only [readsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hR
    rw [fprog_cons, WP.block_append_iff]
    refine WP.mono (fop_ok hL hm hI (hS op (List.mem_cons_self ..)) hR.1) fun s₁ ⟨k₁, I₁⟩ => ?_
    refine WP.mono (fprog_ok hL hm ops I₁ (fun op' h => hS op' (List.mem_cons_of_mem _ h)) hR.2)
      fun s₂ ⟨k₂, I₂⟩ => ⟨⟨fun r hr => (k₂.gpr r hr).trans (k₁.gpr r hr), k₂.rd.trans k₁.rd,
        k₂.wr.trans k₁.wr, fun x hx ht => ?_⟩, I₂⟩
    rw [List.map_cons] at hx
    rw [k₂.mem x (fun w hw => hx w (List.mem_cons_of_mem _ hw)) ht,
      k₁.mem x (hx _ (List.mem_cons_self ..)) ht]

/-- One operation, a call for a product modulo P-521's or P-384's `p` with the
functions' temporary area (`opProg`), inlined (`Code.inline`). -/
theorem opProg_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hm : UnitMod m (2 ^ (64 * M.n))) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) {op : FOp} (hS : ∀ x ∈ op.out :: op.ins, Sl x)
    (hR : ∀ x ∈ op.ins, x ∈ V) :
    WP isa (opProg M op).inline s fun s' =>
      OpKeep M base op.out s s' ∧ Inv M base size m Sl (op.out :: V) (op.run E) s' := by
  unfold opProg
  cases hc : opCall? M op with
  | none => exact fop_ok hL hm hI hS hR
  | some p =>
    cases op with
    | add o a b => simp [opCall?] at hc
    | sub o a b => simp [opCall?] at hc
    | mul o a b =>
      simp only [opCall?] at hc
      split at hc
      · rename_i f body hcall
        split at hc
        · rename_i hlow
          cases hc
          simp only [Option.getD_some]
          unfold Mont.callOf at hcall
          simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
            forall_eq_or_imp, forall_eq] at hS hR
          split at hcall
          · rename_i hM
            obtain ⟨hn9, hred, ht⟩ := hM
            have hbody : body = Mont.mulFn ∨ body = Mont.mulFnX := by
              split at hcall <;> (cases hcall; simp)
            refine WP.mono (Mont.mulCall_ok hbody hI.scr hI.mod hred ht (hn9 ▸ hlow) (hI.lt b hR.2))
              fun s' ⟨hk, hlt, heq⟩ => ⟨hk, hI.update hL hS.1 hk hlt ?_⟩
            rw [toM_mul hm heq, hI.val a hR.1, hI.val b hR.2]
          split at hcall
          · rename_i hM
            obtain ⟨hn6, hsp, ht, -⟩ := hM
            have hbody : body = Mont.mulFn6 false ∨ body = Mont.mulFn6 true := by
              split at hcall <;> (cases hcall; simp)
            refine WP.mono (Mont.mulCall6_ok hbody hI.scr hI.mod hsp ht (hn6 ▸ hlow) (hL.le o hS.1)
              (hL.le a hS.2.1) (hL.le b hS.2.2) (hI.lt b hR.2))
              fun s' ⟨hk, hlt, heq⟩ => ⟨hk, hI.update hL hS.1 hk hlt ?_⟩
            rw [toM_mul hm heq, hI.val a hR.1, hI.val b hR.2]
          · cases hcall
        · cases hc
      · cases hc

/-- A field program, its products calls where `opProg` makes them, inlined. -/
theorem fprogB_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hm : UnitMod m (2 ^ (64 * M.n))) :
    ∀ (ops : List FOp) {V : List Nat} {E : Nat → Fin m} {s : State},
      Inv M base size m Sl V E s → (∀ op ∈ ops, ∀ x ∈ op.out :: op.ins, Sl x) →
      readsOk ops V = true →
      WP isa (fprogB M ops).inline s fun s' => ProgKeep M base (ops.map FOp.out) s s' ∧
        Inv M base size m Sl (validAfter ops V) (runOps ops E) s'
  | [], _, _, s, hI, _, _ => WP.block_nil ⟨ProgKeep.refl _ _ _ s, hI⟩
  | [op], V, E, s, hI, hS, hR => by
    simp only [readsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hR
    refine WP.mono (opProg_ok hL hm hI (hS op (List.mem_cons_self ..)) hR.1) fun s₁ ⟨k₁, I₁⟩ =>
      ⟨⟨k₁.gpr, k₁.rd, k₁.wr, fun x hx ht => k₁.mem x (hx _ (List.mem_cons_self ..)) ht⟩, I₁⟩
  | op :: op' :: ops, V, E, s, hI, hS, hR => by
    rw [readsOk, Bool.and_eq_true, List.all_eq_true] at hR
    simp only [decide_eq_true_eq] at hR
    show WP isa (Code.seq (opProg M op).inline (fprogB M (op' :: ops)).inline) s _
    refine WP.seq (WP.mono (opProg_ok hL hm hI (hS op (List.mem_cons_self ..)) hR.1) fun s₁ ⟨k₁, I₁⟩ => ?_)
    refine WP.mono (fprogB_ok hL hm (op' :: ops) I₁ (fun op'' h => hS op'' (List.mem_cons_of_mem _ h)) hR.2)
      fun s₂ ⟨k₂, I₂⟩ => ⟨⟨fun r hr => (k₂.gpr r hr).trans (k₁.gpr r hr), k₂.rd.trans k₁.rd,
        k₂.wr.trans k₁.wr, fun x hx ht => ?_⟩, I₂⟩
    rw [List.map_cons] at hx
    rw [k₂.mem x (fun w hw => hx w (List.mem_cons_of_mem _ hw)) ht,
      k₁.mem x (hx _ (List.mem_cons_self ..)) ht]

/-- Code that calls nothing runs as its inlined form. -/
theorem _root_.VG.X86_64.wp_of_inline {c : Prog isa} (h : c.noCalls = true) {s : State} {Q : State → Prop}
    (hw : WP isa c.inline s Q) : WP isa c s Q :=
  Code.inline_of_noCalls h ▸ hw

/-- `fprogB` of `op :: ops`: the operation, then the rest. -/
theorem fprogB_cons_iff {M : Mod} {op : FOp} {ops : List FOp} {s : State} {Q : State → Prop} :
    WP isa (fprogB M (op :: ops)).inline s Q ↔
      WP isa (opProg M op).inline s fun t => WP isa (fprogB M ops).inline t Q := by
  cases ops with
  | nil => exact ⟨fun h => WP.mono h fun _ h => WP.block_nil h, fun h => WP.mono h fun _ h => WP.block_nil_iff.mp h⟩
  | cons op' ops => exact WP.seq_iff

/-- `fprogB` of `a ++ b`: `a`, then `b`. -/
theorem fprogB_append_iff {M : Mod} :
    ∀ (a b : List FOp) {s : State} {Q : State → Prop}, WP isa (fprogB M (a ++ b)).inline s Q ↔
      WP isa (fprogB M a).inline s fun t => WP isa (fprogB M b).inline t Q
  | [], _, _, _ => ⟨fun h => WP.block_nil h, fun h => WP.block_nil_iff.mp h⟩
  | op :: a, b, _, _ => by
    rw [List.cons_append, fprogB_cons_iff, fprogB_cons_iff]
    exact ⟨fun h => WP.mono h fun _ h => (fprogB_append_iff a b).mp h,
      fun h => WP.mono h fun _ h => (fprogB_append_iff a b).mpr h⟩

/-- The operations of `N` pieces, by an invariant of the pieces done. -/
theorem fprogB_range_ok {M : Mod} {g : Nat → List FOp} {N : Nat} {Inv : Nat → State → Prop}
    (step : ∀ i < N, ∀ s, Inv i s → WP isa (fprogB M (g i)).inline s (Inv (i + 1))) :
    ∀ i ≤ N, ∀ s, Inv 0 s → WP isa (fprogB M ((List.range i).flatMap g)).inline s (Inv i)
  | 0, _, _, h => WP.block_nil h
  | i + 1, hi, s, h => by
    rw [List.range_succ, List.flatMap_append, fprogB_append_iff]
    refine WP.mono (fprogB_range_ok step i (by omega) s h) fun t ht => ?_
    simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using step i (by omega) t ht

/-! ## The complete addition -/

/-- `o = p + q` by `rcb`, on slots of `Sl` that are apart (`RcbApart`; `p` may
be `q`), from a state holding `E`, in particular `p`, `q`, `a` and `3b`
(`rcbR`): `o` holds `rcbAdd` of their values, and the slots but those `rcb`
writes (`rcbW`) keep theirs. -/
theorem rcb_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hm : UnitMod m (2 ^ (64 * M.n))) {S : RcbSlots} {p q o : Pt} (hA : RcbApart S p q o)
    (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (fprogB M (rcb S p q o)).inline s fun s' => ProgKeep M base (rcbW S o) s s' ∧
      Inv M base size m Sl (rcbW S o ++ V) (runOps (rcb S p q o) E) s' ∧
      (runOps (rcb S p q o) E o.x, runOps (rcb S p q o) E o.y, runOps (rcb S p q o) E o.z) =
        VG.Proof.Weierstrass.rcbAdd (E S.a) (E S.b3) (E p.x) (E p.y) (E p.z) (E q.x) (E q.y)
          (E q.z) ∧
      ∀ x, x ∉ rcbW S o → runOps (rcb S p q o) E x = E x := by
  have hR : readsOk (rcb S p q o) V = true := by
    rw [rcb_eq_rename]
    exact readsOk_mono (readsOk_rename _ rcbN_reads) hV
  refine WP.mono (fprogB_ok hL hm _ hI (fun op hop x hx => hSl x (rcb_slots op hop x hx)) hR)
    fun s' ⟨hk, hI'⟩ => ⟨hk.mono fun w hw => ?_, hI'.sub fun x hx => ?_, rcb_run hA E,
      fun x hx => runOps_of_not_out _ _ fun op hop h => hx (h ▸ rcb_out op hop)⟩
  · obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw
    exact rcb_out op hop
  · rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (rcb_out_mem hx)
    · exact Or.inl hx

/-- A formula on numbered slots, renamed to `p`, `q` and `o`: it writes only
`rcbW S o`, and its result is what the numbered formula computes. -/
theorem ofN_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hm : UnitMod m (2 ^ (64 * M.n))) {N : List FOp} (hN : NumOk N) {S : RcbSlots}
    {p q o : Pt} (hA : RcbApart S p q o) (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x) {V : List Nat}
    {E : Nat → Fin m} {s : State} (hI : Inv M base size m Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (fprogB M (ofN N S p q o)).inline s fun s' => ProgKeep M base (rcbW S o) s s' ∧
      Inv M base size m Sl ([o.x, o.y, o.z] ++ V) (runOps (ofN N S p q o) E) s' ∧
      (runOps (ofN N S p q o) E o.x, runOps (ofN N S p q o) E o.y, runOps (ofN N S p q o) E o.z) =
        (runOps N (fun y => E (rcbσ S p q o y)) 6, runOps N (fun y => E (rcbσ S p q o y)) 7,
          runOps N (fun y => E (rcbσ S p q o y)) 8) := by
  have hR : readsOk (ofN N S p q o) V = true := readsOk_mono (ofN_readsOk hN S p q o) hV
  refine WP.mono (fprogB_ok hL hm _ hI (fun op hop x hx => hSl x (ofN_slots op hop x hx)) hR)
    fun s' ⟨hk, hI'⟩ => ⟨hk.mono fun w hw => ?_, hI'.sub fun x hx => ?_, ?_⟩
  · obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw
    exact ofN_out hN op hop
  · rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (ofN_out_mem hN hx)
    · exact Or.inl hx
  · exact congrArg₂ Prod.mk (ofN_run hN hA E 6) (congrArg₂ Prod.mk (ofN_run hN hA E 7) (ofN_run hN hA E 8))

/-- `o = p + q` by Algorithm 4 (`a = -3`, with `b` in `S.b3`). -/
theorem rcb3_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hm : UnitMod m (2 ^ (64 * M.n))) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o) (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x) {V : List Nat} {E : Nat → Fin m}
    {s : State} (hI : Inv M base size m Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (fprogB M (rcb3 S p q o)).inline s fun s' => ProgKeep M base (rcbW S o) s s' ∧
      Inv M base size m Sl ([o.x, o.y, o.z] ++ V) (runOps (rcb3 S p q o) E) s' ∧
      (runOps (rcb3 S p q o) E o.x, runOps (rcb3 S p q o) E o.y, runOps (rcb3 S p q o) E o.z) =
        VG.Proof.Weierstrass.rcbAdd3 (E S.b3) (E p.x) (E p.y) (E p.z) (E q.x) (E q.y) (E q.z) := by
  rw [rcb3_eq]
  exact WP.mono (ofN_ok hL hm rcb3N_ok hA hSl hI hV) fun s' ⟨k, I, v⟩ =>
    ⟨k, I, v.trans (rcb3N_run _)⟩

/-- `o = p + q` by Algorithm 5 (`a = -3`, `q` affine: `q.z` is not read, with
`b` in `S.b3`). -/
theorem rcb3m_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hm : UnitMod m (2 ^ (64 * M.n))) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o) (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x) {V : List Nat} {E : Nat → Fin m}
    {s : State} (hI : Inv M base size m Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (fprogB M (rcb3m S p q o)).inline s fun s' => ProgKeep M base (rcbW S o) s s' ∧
      Inv M base size m Sl ([o.x, o.y, o.z] ++ V) (runOps (rcb3m S p q o) E) s' ∧
      (runOps (rcb3m S p q o) E o.x, runOps (rcb3m S p q o) E o.y, runOps (rcb3m S p q o) E o.z) =
        VG.Proof.Weierstrass.rcbAdd3m (E S.b3) (E p.x) (E p.y) (E p.z) (E q.x) (E q.y) := by
  rw [rcb3m_eq]
  exact WP.mono (ofN_ok hL hm rcb3mN_ok hA hSl hI hV) fun s' ⟨k, I, v⟩ =>
    ⟨k, I, v.trans (rcb3mN_run _)⟩

end VG.Proof.Weierstrass.X86_64

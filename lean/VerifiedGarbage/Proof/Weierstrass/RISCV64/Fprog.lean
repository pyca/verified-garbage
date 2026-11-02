module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Call
public import VerifiedGarbage.Proof.Weierstrass.Env
public import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Field programs on slots, on RISC-V

`fprog F ops` (`Impl/Weierstrass/RISCV64.lean`) runs the field operations
`ops` on slots of the working space, one by one by calls of the functions of
the field `F` (`fprog_ok`), as on PPC64LE
(`Proof/Weierstrass/PPC64LE/Fprog.lean`): on slots that are apart from each
other, below the functions' own working space (`Proof.Mont.Lay` of
`own M.n` bytes) and at offsets `liAt` reaches (below 4095), what the slots
stand for (`toM`) follows `runOps ops`, the program on environments (`Inv`).
A slot is read only once it holds a number below `m`: either it did at the
start (`V`) or an earlier operation wrote it (`readsOk`). Only the slots
written and the functions' own working space change, and the callee-saved
registers, the regions and the stack pointer stay (`KeepR`).

The complete addition `rcb` is such a program, and computes `rcbAdd`
(`rcb_ok`).
-/

-- separate module: its proofs (about 2 s) cost more than its imports, and its importer's
-- changes need not re-check them

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64

open VG VG.RISCV64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Proof.Mont VG.Proof.Weierstrass

/-- What a program writing the slots `W` keeps: `Kp`, and the memory but the
slots `W` and the functions' own working space. -/
structure KeepR (k : Nat) (base : Addr) (W : List Nat) (s s' : State) : Prop where
  kp : Kp s s'
  mem : Outs base (W.map (fun w => (w, 8 * k)) ++ [(own k, 64 * k)]) s.mem s'.mem

theorem KeepR.refl (k : Nat) (base : Addr) (W : List Nat) (s : State) : KeepR k base W s s :=
  ⟨Kp.refl s, Outs.refl _ _ _⟩

theorem KeepR.trans {k : Nat} {base : Addr} {W : List Nat} {s₁ s₂ s₃ : State}
    (h₁ : KeepR k base W s₁ s₂) (h₂ : KeepR k base W s₂ s₃) : KeepR k base W s₁ s₃ :=
  ⟨h₁.kp.trans h₂.kp, h₁.mem.trans h₂.mem⟩

theorem KeepR.mono {k : Nat} {base : Addr} {W W' : List Nat} {s s' : State}
    (h : KeepR k base W s s') (hW : ∀ w ∈ W, w ∈ W') : KeepR k base W' s s' :=
  ⟨h.kp, h.mem.mono fun r hr => by
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hr ⊢
    rcases hr with ⟨w, hw, rfl⟩ | rfl
    · exact .inl ⟨w, hW w hw, rfl⟩
    · exact .inr rfl⟩

/-- A call's frame, as a program's. -/
theorem KeepR.of_call {k : Nat} {base : Addr} {o : Nat} {s s' : State}
    (h : CallKeep k base o s s') : KeepR k base [o] s s' :=
  ⟨h.kp, h.mem.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rcases hr with rfl | rfl <;> simp)⟩

/-- A number apart from every range that changed. -/
theorem outs_wordsVal {base : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs base rs m m')
    {d k : Nat} (hd : ∀ r ∈ rs, d + 8 * k ≤ r.1 ∨ r.1 + r.2 ≤ d) (hd' : d + 8 * k ≤ 2 ^ 64) :
    wordsVal m' base d k = wordsVal m base d k := by
  rw [wordsVal_eq_val32, wordsVal_eq_val32]
  exact h.val32 (fun r hr => by have := hd r hr; omega) (by omega)

/-- Slots `liAt` reaches. -/
abbrev Short (Sl : Nat → Prop) : Prop := ∀ x, Sl x → x < 4095

/-- The state holds the environment `E` in Montgomery's form in the slots
`V` (of `Sl`), below `m`, and the working space is at `s0`. -/
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
    (hI : Inv M.n base m Sl V E s) {o : Nat} (ho : Sl o) (hk : KeepR M.n base [o] s s')
    (hr : wordsVal s'.mem base o M.n < m) {v : Fin m}
    (hv : toM m (2 ^ (64 * M.n)) (wordsVal s'.mem base o M.n) = v) :
    Inv M.n base m Sl (o :: V) (Function.update E o v) s' := by
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
  refine ⟨hI.ws.of_kp hk.kp, ?_, ?_, ?_⟩
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

theorem progs_wp (p : Prog isa) (ps : List (Prog isa)) {s : State} {Q : State → Prop}
    (h : WP isa p s fun s' => WP isa (progs ps) s' Q) : WP isa (progs (p :: ps)) s Q := by
  cases ps with
  | nil => exact WP.mono h fun _ h' => WP.block_nil_iff.mp h'
  | cons p' ps' => exact WP.seq h

/-- One operation. -/
theorem fop_ok {M : Mod} {base : Addr} {F : Field} [NeZero F.S.m] (hF : FieldOk F) (hk : F.S.k = M.n)
    {Sl : Nat → Prop} (hL : Lay M (own M.n) Sl) (hS2 : Short Sl)
    (hm : UnitMod F.S.m (2 ^ (64 * M.n))) {V : List Nat} {E : Nat → Fin F.S.m} {s : State}
    (hI : Inv M.n base F.S.m Sl V E s) {op : FOp} (hS : ∀ x ∈ op.out :: op.ins, Sl x)
    (hR : ∀ x ∈ op.ins, x ∈ V) :
    WP isa (opCode F op) s fun s' =>
      KeepR M.n base [op.out] s s' ∧ Inv M.n base F.S.m Sl (op.out :: V) (op.run E) s' := by
  have hle : ∀ x, Sl x → x + 8 * F.S.k ≤ own F.S.k := fun x hx => by rw [hk]; exact hL.le x hx
  cases op with
  | mul o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    refine WP.mono (mulCall_ok hF hI.ws (hle o hS.1) (hle a hS.2.1) (hle b hS.2.2)
        (hS2 o hS.1) (hS2 a hS.2.1) (hS2 b hS.2.2) (by rw [hk]; exact hI.lt b hR.2))
      fun s' ⟨K, hlt, heq⟩ => ?_
    rw [hk] at K hlt heq
    refine ⟨.of_call K, hI.update hL hS.1 (.of_call K) hlt ?_⟩
    rw [toM_mul hm heq, hI.val a hR.1, hI.val b hR.2]
  | add o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    have hA := hI.lt a hR.1
    have hB := hI.lt b hR.2
    refine WP.mono (addCall_ok hF hI.ws (hle o hS.1) (hle a hS.2.1) (hle b hS.2.2)
        (hS2 o hS.1) (hS2 a hS.2.1) (hS2 b hS.2.2) (by rw [hk]; omega))
      fun s' ⟨K, heq⟩ => ?_
    rw [hk] at K heq
    refine ⟨.of_call K, hI.update hL hS.1 (.of_call K) ?_ ?_⟩
    · rw [heq]; exact Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne _))
    · rw [heq, toM_add, hI.val a hR.1, hI.val b hR.2]
  | sub o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    have hA := hI.lt a hR.1
    have hB := hI.lt b hR.2
    refine WP.mono (subCall_ok hF hI.ws (hle o hS.1) (hle a hS.2.1) (hle b hS.2.2)
        (hS2 o hS.1) (hS2 a hS.2.1) (hS2 b hS.2.2) (by rw [hk]; exact hA) (by rw [hk]; exact hB))
      fun s' ⟨K, heq⟩ => ?_
    rw [hk] at K heq
    refine ⟨.of_call K, hI.update hL hS.1 (.of_call K) ?_ ?_⟩
    · rw [heq]; exact Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne _))
    · rw [heq, toM_sub (by omega), hI.val a hR.1, hI.val b hR.2]

/-- A field program. -/
theorem fprog_ok {M : Mod} {base : Addr} {F : Field} [NeZero F.S.m] (hF : FieldOk F) (hk : F.S.k = M.n)
    {Sl : Nat → Prop} (hL : Lay M (own M.n) Sl) (hS2 : Short Sl)
    (hm : UnitMod F.S.m (2 ^ (64 * M.n))) :
    ∀ (ops : List FOp) {V : List Nat} {E : Nat → Fin F.S.m} {s : State},
      Inv M.n base F.S.m Sl V E s → (∀ op ∈ ops, ∀ x ∈ op.out :: op.ins, Sl x) →
      readsOk ops V = true →
      WP isa (fprog F ops) s fun s' => KeepR M.n base (ops.map FOp.out) s s' ∧
        Inv M.n base F.S.m Sl (validAfter ops V) (runOps ops E) s'
  | [], _, _, s, hI, _, _ => WP.block_nil ⟨KeepR.refl _ _ _ s, hI⟩
  | op :: ops, V, E, s, hI, hS, hR => by
    simp only [readsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hR
    refine progs_wp _ _ (WP.mono (fop_ok hF hk hL hS2 hm hI (hS op (List.mem_cons_self ..)) hR.1)
      fun s₁ ⟨k₁, I₁⟩ => ?_)
    refine WP.mono (fprog_ok hF hk hL hS2 hm ops I₁ (fun op' h => hS op' (List.mem_cons_of_mem _ h)) hR.2)
      fun s₂ ⟨k₂, I₂⟩ => ⟨(k₁.mono fun w hw => ?_).trans (k₂.mono fun w hw => ?_), I₂⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      simp [hw]
    · simp [hw]

/-! ## The complete addition -/

/-- `o = p + q` by `rcb`, on slots of `Sl` that are apart (`RcbApart`; `p` may
be `q`), from a state holding `E`, in particular `p`, `q`, `a` and `3b`
(`rcbR`): `o` holds `rcbAdd` of their values, and the slots but those `rcb`
writes (`rcbW`) keep theirs. -/
theorem rcb_ok {M : Mod} {base : Addr} {F : Field} [NeZero F.S.m] (hF : FieldOk F) (hk : F.S.k = M.n)
    {Sl : Nat → Prop} (hL : Lay M (own M.n) Sl) (hS2 : Short Sl)
    (hm : UnitMod F.S.m (2 ^ (64 * M.n))) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o)
    (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x) {V : List Nat} {E : Nat → Fin F.S.m} {s : State}
    (hI : Inv M.n base F.S.m Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (fprog F (rcb S p q o)) s fun s' => KeepR M.n base (rcbW S o) s s' ∧
      Inv M.n base F.S.m Sl (rcbW S o ++ V) (runOps (rcb S p q o) E) s' ∧
      (runOps (rcb S p q o) E o.x, runOps (rcb S p q o) E o.y, runOps (rcb S p q o) E o.z) =
        VG.Proof.Weierstrass.rcbAdd (E S.a) (E S.b3) (E p.x) (E p.y) (E p.z) (E q.x) (E q.y)
          (E q.z) ∧
      ∀ x, x ∉ rcbW S o → runOps (rcb S p q o) E x = E x := by
  have hR : readsOk (rcb S p q o) V = true := by
    rw [rcb_eq_rename]
    exact readsOk_mono (readsOk_rename _ rcbN_reads) hV
  refine WP.mono (fprog_ok hF hk hL hS2 hm _ hI (fun op hop x hx => hSl x (rcb_slots op hop x hx)) hR)
    fun s' ⟨hk', hI'⟩ => ⟨hk'.mono fun w hw => ?_, hI'.sub fun x hx => ?_, rcb_run hA E,
      fun x hx => runOps_of_not_out _ _ fun op hop h => hx (h ▸ rcb_out op hop)⟩
  · obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw
    exact rcb_out op hop
  · rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (rcb_out_mem hx)
    · exact Or.inl hx

/-! ## Formulas on numbered slots: `a = -3` -/

/-- A formula on numbered slots (`NumOk`), renamed to the slots of a sum. -/
theorem ofN_ok {M : Mod} {base : Addr} {F : Field} [NeZero F.S.m] (hF : FieldOk F) (hk : F.S.k = M.n)
    {Sl : Nat → Prop} (hL : Lay M (own M.n) Sl) (hS2 : Short Sl)
    (hm : UnitMod F.S.m (2 ^ (64 * M.n))) {N : List FOp} (hN : NumOk N) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o) (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x) {V : List Nat}
    {E : Nat → Fin F.S.m} {s : State} (hI : Inv M.n base F.S.m Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (fprog F (ofN N S p q o)) s fun s' => KeepR M.n base (rcbW S o) s s' ∧
      Inv M.n base F.S.m Sl ([o.x, o.y, o.z] ++ V) (runOps (ofN N S p q o) E) s' ∧
      (runOps (ofN N S p q o) E o.x, runOps (ofN N S p q o) E o.y, runOps (ofN N S p q o) E o.z) =
        (runOps N (fun y => E (rcbσ S p q o y)) 6, runOps N (fun y => E (rcbσ S p q o y)) 7,
          runOps N (fun y => E (rcbσ S p q o y)) 8) ∧
      ∀ x, x ∉ rcbW S o → runOps (ofN N S p q o) E x = E x := by
  have hR : readsOk (ofN N S p q o) V = true := readsOk_mono (ofN_readsOk hN S p q o) hV
  refine WP.mono (fprog_ok hF hk hL hS2 hm _ hI (fun op hop x hx => hSl x (ofN_slots op hop x hx)) hR)
    fun s' ⟨hk', hI'⟩ => ⟨hk'.mono fun w hw => ?_, hI'.sub fun x hx => ?_, ?_,
      fun x hx => runOps_of_not_out _ _ fun op hop h => hx (h ▸ ofN_out hN op hop)⟩
  · obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw
    exact ofN_out hN op hop
  · rw [mem_validAfter]
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inr (ofN_out_mem hN hx)
    · exact Or.inl hx
  · exact congrArg₂ Prod.mk (ofN_run hN hA E 6) (congrArg₂ Prod.mk (ofN_run hN hA E 7) (ofN_run hN hA E 8))

/-- `o = p + q` by Algorithm 4 (`a = -3`, with `b` in `S.b3`). -/
theorem rcb3_ok {M : Mod} {base : Addr} {F : Field} [NeZero F.S.m] (hF : FieldOk F) (hk : F.S.k = M.n)
    {Sl : Nat → Prop} (hL : Lay M (own M.n) Sl) (hS2 : Short Sl)
    (hm : UnitMod F.S.m (2 ^ (64 * M.n))) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o) (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x) {V : List Nat}
    {E : Nat → Fin F.S.m} {s : State} (hI : Inv M.n base F.S.m Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V) :
    WP isa (fprog F (rcb3 S p q o)) s fun s' => KeepR M.n base (rcbW S o) s s' ∧
      Inv M.n base F.S.m Sl ([o.x, o.y, o.z] ++ V) (runOps (rcb3 S p q o) E) s' ∧
      (runOps (rcb3 S p q o) E o.x, runOps (rcb3 S p q o) E o.y, runOps (rcb3 S p q o) E o.z) =
        VG.Proof.Weierstrass.rcbAdd3 (E S.b3) (E p.x) (E p.y) (E p.z) (E q.x) (E q.y) (E q.z) := by
  rw [rcb3_eq]
  exact WP.mono (ofN_ok hF hk hL hS2 hm rcb3N_ok hA hSl hI hV) fun s' ⟨k, I, v, _⟩ =>
    ⟨k, I, v.trans (rcb3N_run _)⟩

end VG.Proof.Weierstrass.RISCV64

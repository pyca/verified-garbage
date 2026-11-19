module

public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Pow
public import VerifiedGarbage.Impl.Weierstrass.PPC64LE.LadderP
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Copy
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Weierstrass.Rcb0
public import VerifiedGarbage.Proof.Weierstrass.Layout
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Mont.RangeCover
public import VerifiedGarbage.Proof.Weierstrass.Point0Contract
public import VerifiedGarbage.Impl.Weierstrass.PPC64LE.Point
public import VerifiedGarbage.Proof.Weierstrass.Env

/-! ### `Weierstrass.PPC64LE.Ladder`, which this module and modules that import it used -/

section

/-! ### `Weierstrass.PPC64LE.PointFprog`, which this module and modules that import it used -/

section

/-!
# Field programs on slots named by number, on PPC64LE

`fprogR σ S ops` (`Impl/Weierstrass/PPC64LE/Point.lean`) runs the field
operations `ops`, on slots named by number, each slot `x` at the offset
`σ x`, by calls of the functions of the modulus `S`, as on 32-bit ARM
(`Proof/Weierstrass/Arm/PointFprog.lean`): what the slots stand for (`toM`)
follows `runOps ops` (`fprogR_ok`), and the offsets may coincide: only the
slots the program writes (`W`) must be apart from every other (`LayR`), so
that two slots it only reads may be one (a point doubled). `rcbR_ok` is the
complete addition.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.Point

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Weierstrass.PPC64LE.Point
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE.Mont

/-- The slots `x < N` at offsets `σ x` of numbers of `k` words: below the
functions' own working space, and each of `W` apart from every other. -/
structure LayR (k N : Nat) (W : List Nat) (σ : Nat → Nat) : Prop where
  le : ∀ x < N, σ x + 8 * k ≤ own k
  apart : ∀ w ∈ W, ∀ x < N, x ≠ w → σ x + 8 * k ≤ σ w ∨ σ w + 8 * k ≤ σ x

/-- The state holds the environment `E` in Montgomery's form in the slots `V`
(below `N`), below `m`, and the working space is at `r3`. -/
structure InvR (k N : Nat) (σ : Nat → Nat) (base : Addr) (m : Nat) [NeZero m]
    (V : List Nat) (E : Nat → Fin m) (s : State) : Prop where
  ws : WsReg s base
  ids : ∀ x ∈ V, x < N
  lt : ∀ x ∈ V, wordsVal s.mem base (σ x) k < m
  val : ∀ x ∈ V, toM m (2 ^ (64 * k)) (wordsVal s.mem base (σ x) k) = E x

/-- What a program writing the slots `W` keeps: the registers but `fnClob`,
the regions, the stack pointer, and the memory but the slots `W` and the
functions' own working space. -/
structure KeepR (k : Nat) (σ : Nat → Nat) (base : Addr) (W : List Nat) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ fnClob → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  mem : Outs base (W.map (fun w => (σ w, 8 * k)) ++ [(own k, 64 * k)]) s.mem s'.mem

theorem KeepR.refl (k : Nat) (σ : Nat → Nat) (base : Addr) (W : List Nat) (s : State) : KeepR k σ base W s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, Outs.refl _ _ _⟩

theorem KeepR.trans {k : Nat} {σ : Nat → Nat} {base : Addr} {W : List Nat} {s₁ s₂ s₃ : State}
    (h₁ : KeepR k σ base W s₁ s₂) (h₂ : KeepR k σ base W s₂ s₃) : KeepR k σ base W s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp,
    h₁.mem.trans h₂.mem⟩

theorem KeepR.mono {k : Nat} {σ : Nat → Nat} {base : Addr} {W W' : List Nat} {s s' : State}
    (h : KeepR k σ base W s s') (hW : ∀ w ∈ W, w ∈ W') : KeepR k σ base W' s s' :=
  ⟨h.gpr, h.rd, h.wr, h.sp, h.mem.mono fun r hr => by
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hr ⊢
    rcases hr with ⟨w, hw, rfl⟩ | rfl
    · exact .inl ⟨w, hW w hw, rfl⟩
    · exact .inr rfl⟩

/-- A call's frame, as a program's. -/
theorem KeepR.of_call {k : Nat} {σ : Nat → Nat} {base : Addr} {o : Nat} {s s' : State}
    (h : CallKeep k base (σ o) s s') : KeepR k σ base [o] s s' :=
  ⟨h.gpr, h.rd, h.wr, h.sp, h.mem.mono (by
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
  have hn := hI.ws.nowrap
  have hown : own k ≤ 4096 := Nat.sub_le _ _
  have heq : ∀ x ∈ V, x ≠ o → wordsVal s'.mem base (σ x) k = wordsVal s.mem base (σ x) k := by
    intro x hx hxo
    have hxN := hI.ids x hx
    have h1 := hL.le x hxN
    have h2 := hL.apart o hoW x hxN hxo
    refine outs_wordsVal hk.mem (fun r hr => ?_) (by omega_arith)
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h2
    · exact .inl h1
  refine ⟨hI.ws.of_keep (hk.gpr _ (by decide)) hk.wr, ?_, ?_, ?_⟩
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
theorem fopR_ok {k N : Nat} {σ : Nat → Nat} {base : Addr} {S : Impl.Weierstrass.Mont.Modulus}
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
    refine WP.mono (mulCall_ok hM hI.ws (hL.le o hN.1) (hL.le a hN.2.1) (hL.le b hN.2.2) (hI.lt b hR.2))
      fun s' ⟨K, hlt, heq⟩ => ?_
    refine ⟨.of_call K, hI.update hL hW hN.1 (.of_call K) hlt ?_⟩
    rw [toM_mul hm heq, hI.val a hR.1, hI.val b hR.2]
  | add o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hW hN hR
    have hA := hI.lt a hR.1
    have hB := hI.lt b hR.2
    refine WP.mono (addCall_ok hM hI.ws (hL.le o hN.1) (hL.le a hN.2.1) (hL.le b hN.2.2) (by omega_arith))
      fun s' ⟨K, heq⟩ => ?_
    refine ⟨.of_call K, hI.update hL hW hN.1 (.of_call K) ?_ ?_⟩
    · rw [heq]; exact Nat.mod_lt _ (by omega_arith)
    · rw [heq, toM_add, hI.val a hR.1, hI.val b hR.2]
  | sub o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hW hN hR
    have hA := hI.lt a hR.1
    have hB := hI.lt b hR.2
    refine WP.mono (subCall_ok hM hI.ws (hL.le o hN.1) (hL.le a hN.2.1) (hL.le b hN.2.2) hA hB)
      fun s' ⟨K, heq⟩ => ?_
    refine ⟨.of_call K, hI.update hL hW hN.1 (.of_call K) ?_ ?_⟩
    · rw [heq]; exact Nat.mod_lt _ (by omega_arith)
    · rw [heq, toM_sub (by omega_arith), hI.val a hR.1, hI.val b hR.2]

theorem progs_wp (p : Prog isa) (ps : List (Prog isa)) {s : State} {Q : State → Prop}
    (h : WP isa p s fun s' => WP isa (progs ps) s' Q) : WP isa (progs (p :: ps)) s Q := by
  cases ps with
  | nil => exact WP.mono h fun _ h' => WP.block_nil_iff.mp h'
  | cons p' ps' => exact WP.seq h

/-- A field program. -/
theorem fprogR_ok {k N : Nat} {σ : Nat → Nat} {base : Addr} {S : Impl.Weierstrass.Mont.Modulus}
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

/-- A formula on the function's slots: it writes only `wIds`, names only
slots below 17, reads only `rIds` or what it wrote, and writes the
result's three slots. -/
structure OpsOk (ops : List FOp) : Prop where
  slots : ∀ op ∈ ops, op.out ∈ wIds ∧ ∀ x ∈ op.out :: op.ins, x < 17
  reads : readsOk ops rIds = true
  outs : ∀ j < 3, j ∈ validAfter ops rIds

/-- A formula on the slots numbered as the function numbers them, from a
state holding `E` in the slots it reads. -/
theorem opsR_ok {k : Nat} {σ : Nat → Nat} {base : Addr} {S : Impl.Weierstrass.Mont.Modulus}
    [NeZero S.m] (hM : ModOk S.k S.m) (hk : S.k = k) (hL : LayR k 17 wIds σ)
    (hm : UnitMod S.m (2 ^ (64 * k))) {ops : List FOp} (hO : OpsOk ops)
    {E : Nat → Fin S.m} {s : State} (hI : InvR k 17 σ base S.m rIds E s) :
    WP isa (fprogR σ S ops) s fun s' => KeepR k σ base wIds s s' ∧
      InvR k 17 σ base S.m (validAfter ops rIds) (runOps ops E) s' := by
  refine WP.mono (fprogR_ok hM hk hL hm _ hI hO.slots hO.reads) fun s' ⟨hk', hI'⟩ =>
    ⟨hk'.mono fun w hw => ?_, hI'⟩
  obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw
  exact (hO.slots op hop).1

theorem rcbIds_ok : ∀ op ∈ rcb sId pId qId oId, op.out ∈ wIds ∧ ∀ x ∈ op.out :: op.ins, x < 17 := by
  decide

theorem rcbIds_reads : readsOk (rcb sId pId qId oId) rIds = true := by decide

theorem rcbIds_apart : RcbApart sId pId qId oId := ⟨by decide, by decide⟩

/-- `o = p + q` by `rcb` on the slots numbered as the function numbers them,
from a state holding `E` in `p`, `q`, `a` and `3b`: `o` holds `rcbAdd` of
their values. -/
theorem rcbR_ok {k : Nat} {σ : Nat → Nat} {base : Addr} {S : Impl.Weierstrass.Mont.Modulus}
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

/-! ## The formulas for `a = 0` -/

theorem dbl0_opsOk : OpsOk (dbl0 sId pId oId) := ⟨by decide, by decide, by decide⟩

theorem rcb0m_opsOk : OpsOk (rcb0m sId pId qId oId) := ⟨by decide, by decide, by decide⟩

theorem rcbIds_opsOk : OpsOk (rcb sId pId qId oId) := ⟨rcbIds_ok, rcbIds_reads, by decide⟩

theorem ops0_opsOk (dbl : Bool) : OpsOk (ops0 dbl) := by
  cases dbl
  · exact rcb0m_opsOk
  · exact dbl0_opsOk

/-- What the formulas compute on the slots. -/
theorem ops0_run {m : Nat} [NeZero m] (E : Nat → Fin m) (dbl : Bool) :
    (runOps (ops0 dbl) E 0, runOps (ops0 dbl) E 1, runOps (ops0 dbl) E 2) =
      if dbl then Impl.Weierstrass.Point.rcbDbl0 (E 10) (E 3) (E 4) (E 5)
      else Impl.Weierstrass.Point.rcbAdd0m (E 10) (E 3) (E 4) (E 5) (E 6) (E 7) := by
  cases dbl <;> rfl

end VG.Proof.Weierstrass.PPC64LE.Point

end

end

/-! ### `Weierstrass.PPC64LE.LadderPCall`, which the modules that import this one used -/

section

/-! ### `Weierstrass.PPC64LE.PointFn`, which this module and modules that import it used -/

section

/-!
# Complete point addition and doubling as functions, on PPC64LE: correctness

`fnOps S dbl ops` (`Impl/Weierstrass/PPC64LE/Point.lean`), for field
operations `ops` that write only the result and the temporaries (`OpsOk`),
from a state that its precondition describes (`PrePt`: the working space at `r3`, writable, and
every coordinate it reads below the prime), returns with the callee-saved
registers, `sp` and `lr` kept, the registers but `fnClob` kept, the memory
changed only at `O` and in the own working space, and `O`'s coordinates
below the prime, standing for what `ops` computes from what the constants
and the operands stand for (`fnOps_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.Point

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Weierstrass.PPC64LE.Point
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE.Mont
open VG.Impl.Weierstrass.Point (elemBytes ownAt aAt b3At oAt pAt qAt)

/-- The numbers of the layout, for `omega`. -/
theorem lay_nums {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) :
    ownAt k + 64 + 6 * elemBytes k = own k ∧ own k + 64 * k = 4096 ∧ elemBytes k = 8 * k ∧
    b3At k + elemBytes k = ownAt k ∧ aAt k + elemBytes k = b3At k ∧
    qAt k + 3 * elemBytes k = aAt k ∧ pAt k + 3 * elemBytes k = qAt k ∧
    oAt k + 3 * elemBytes k = pAt k ∧ 1000 ≤ oAt k ∧ ownAt k % 8 = 0 := by
  obtain rfl | rfl | rfl | rfl : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega_using [hk3, hk6]
  all_goals decide +kernel

/-- The slots the function reads first lie below its own working space. -/
theorem enc_rIds {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) (dbl : Bool) :
    ∀ x ∈ rIds, enc k dbl x + 8 * k ≤ ownAt k := by
  obtain rfl | rfl | rfl | rfl : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega_using [hk3, hk6]
  all_goals cases dbl <;> decide +kernel

/-- The slots `enc` gives are laid out as the program needs. -/
theorem enc_lay {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) (dbl : Bool) : LayR k 17 wIds (enc k dbl) := by
  obtain rfl | rfl | rfl | rfl : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega_using [hk3, hk6]
  all_goals cases dbl <;> exact ⟨by decide +kernel, by decide +kernel⟩

/-- Those it writes lie apart from the saved `lr` and within `O` or the own
working space. -/
theorem enc_wIds {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) (dbl : Bool) :
    ∀ w ∈ wIds, (enc k dbl w + 8 * k ≤ ownAt k ∨ ownAt k + 8 ≤ enc k dbl w) ∧
      ((oAt k ≤ enc k dbl w ∧ enc k dbl w + 8 * k ≤ pAt k) ∨
        (ownAt k ≤ enc k dbl w ∧ enc k dbl w + 8 * k ≤ 4096)) := by
  obtain rfl | rfl | rfl | rfl : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega_using [hk3, hk6]
  all_goals cases dbl <;> decide +kernel

/-- The precondition of the function, on the state: the working space at
`r3`, its `8192` bytes writable, and the numbers it reads below `m`. -/
structure PrePt (k m : Nat) (dbl : Bool) (s : State) : Prop where
  wr : s.wr = [⟨s.gpr .r3, 8192⟩]
  fit : (s.gpr .r3).toNat + 8192 ≤ 2 ^ 64
  k3 : 3 ≤ k
  k6 : k ≤ 6
  lt : ∀ x ∈ rIds, wordsVal s.mem (s.gpr .r3) (enc k dbl x) k < m

/-- The environment of the entry: what the numbers of the slots stand for. -/
def E₀ (k m : Nat) [NeZero m] (dbl : Bool) (s : State) (x : Nat) : Fin m :=
  toM m (2 ^ (64 * k)) (wordsVal s.mem (s.gpr .r3) (enc k dbl x) k)

theorem rIds_lt : ∀ x ∈ rIds, x < 17 := by decide

/-- A function of field operations `ops` that write only the result and the
temporaries (`OpsOk`): the registers but `fnClob`, `sp` and `lr` kept, the
memory changed only at `O` and in the own working space, and `O`'s
coordinates below the prime, standing for what `ops` computes from what the
slots stand for. -/
theorem fnOps_ok {S : Impl.Weierstrass.Mont.Modulus} [NeZero S.m] (hM : ModOk S.k S.m) (hodd : S.m % 2 = 1)
    {dbl : Bool} {ops : List FOp} (hO : OpsOk ops) {s : State} (hp : PrePt S.k S.m dbl s) :
    WP isa (Point.fnOps S dbl ops) s fun s' => abiPreserved s s' ∧ (∀ r, r ∉ fnClob → s'.gpr r = s.gpr r) ∧
      Outs (s.gpr .r3) [(oAt S.k, 3 * elemBytes S.k), (ownAt S.k, 4096 - ownAt S.k)] s.mem s'.mem ∧
      (∀ j < 3, wordsVal s'.mem (s.gpr .r3) (enc S.k dbl j) S.k < S.m) ∧
      (toM S.m (2 ^ (64 * S.k)) (wordsVal s'.mem (s.gpr .r3) (enc S.k dbl 0) S.k),
        toM S.m (2 ^ (64 * S.k)) (wordsVal s'.mem (s.gpr .r3) (enc S.k dbl 1) S.k),
        toM S.m (2 ^ (64 * S.k)) (wordsVal s'.mem (s.gpr .r3) (enc S.k dbl 2) S.k)) =
        (runOps ops (E₀ S.k S.m dbl s) 0, runOps ops (E₀ S.k S.m dbl s) 1,
          runOps ops (E₀ S.k S.m dbl s) 2) := by
  have hl := lay_nums hp.k3 hp.k6
  have hR := enc_rIds hp.k3 hp.k6 dbl
  have hW := enc_wIds hp.k3 hp.k6 dbl
  have hfit := hp.fit
  have hs : Ws s (s.gpr .r3) 4096 := ⟨⟨8192, by decide, by rw [hp.wr]; simp, hfit⟩, by decide⟩
  have h3 : At s (s.gpr .r3) .r3 0 := by simp [At, off]
  rw [Point.fnOps]
  -- The entry: `lr` saved.
  have hent : WP isa (.block (entry S.k)) s fun s₁ => Kp fnClob s s₁ ∧
      s₁.mem = s.mem.writeW (off (s.gpr .r3) (saveAt S.k)) s.lr := by
    refine wp_step exec_mflr (wp_step (std_ok (hs.write _ _) (h3.write _) (by decide) (d := saveAt S.k)
      (by simp only [saveAt]; omega_using [hl]) (by simp only [saveAt]; omega_using [hl])) (WP.block_nil ?_))
    simp only [write_gpr, ite_true, Nat.zero_add]
    exact ⟨(Kp.write s _ (by decide)).trans (Kp.store _ _ _), rfl⟩
  refine WP.seq (WP.mono hent fun s₁ ⟨K₁, m₁⟩ => ?_)
  have O₁ := writeW_outside s.mem (s.gpr .r3) (d := saveAt S.k) s.lr (by simp only [saveAt]; omega_using [hl])
  rw [← m₁] at O₁
  have hI : InvR S.k 17 (enc S.k dbl) (s.gpr .r3) S.m rIds (E₀ S.k S.m dbl s) s₁ := by
    have heq : ∀ x ∈ rIds, wordsVal s₁.mem (s.gpr .r3) (enc S.k dbl x) S.k =
        wordsVal s.mem (s.gpr .r3) (enc S.k dbl x) S.k := fun x hx =>
      O₁.wordsVal (by have := hR x hx; simp only [saveAt]; omega_using [this]) (by have := hR x hx; omega_using [hl, this])
    exact ⟨⟨by rw [K₁.g], by rw [K₁.wr, hp.wr]; simp, hfit⟩, rIds_lt,
      fun x hx => by rw [heq x hx]; exact hp.lt x hx, fun x hx => by rw [heq x hx]; rfl⟩
  refine WP.seq (WP.mono (opsR_ok hM rfl (enc_lay hp.k3 hp.k6 dbl) (unitMod_pow_two hodd _) hO hI)
    fun s₂ ⟨K, I₂⟩ => ?_)
  -- The restore.
  have hs₂ : Ws s₂ (s.gpr .r3) 4096 := ⟨⟨8192, by decide, by rw [K.wr, K₁.wr, hp.wr]; simp, hfit⟩, by decide⟩
  have h3₂ : At s₂ (s.gpr .r3) .r3 0 := by rw [At, K.gpr _ (by decide), K₁.g]; exact h3
  have hsv : word s₂.mem (s.gpr .r3) (saveAt S.k) = s.lr := by
    rw [Outs.word K.mem (fun r hr => ?_) (by simp only [saveAt]; omega_using [hl]), m₁, word_writeW_self]
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hr
    rcases hr with ⟨x, hx, rfl⟩ | rfl
    · rcases (hW x hx).1 with h | h <;> [exact .inr (by simp only [saveAt]; omega_using [h]);
        exact .inl (by simp only [saveAt]; omega_using [h])]
    · exact .inl (by simp only [saveAt]; omega_using [hl])
  refine wp_step (ld_ok hs₂ h3₂ (by decide) (by simp only [saveAt]; omega_using [hl]) (d := saveAt S.k)
    (by simp only [saveAt]; omega_using [hl])) (wp_step exec_mtlr (WP.block_nil ?_))
  simp only [write_gpr, ite_true, Nat.zero_add, hsv]
  refine ⟨⟨fun r hr => ?_, ?_, rfl⟩, fun r hr => ?_, ?_, fun j hj => ?_, ?_⟩
  · have hr' : r ∉ fnClob := fun h => absurd h ((by decide : ∀ r ∈ preserved, r ∉ fnClob) r hr)
    have : r ≠ .r0 := fun h => hr' (h ▸ by decide)
    simp only [write_gpr, this, ite_false]
    rw [K.gpr r hr', K₁.gpr r hr']
  · simp only [write_sp]; rw [K.sp, K₁.sp]
  · have : r ≠ .r0 := fun h => hr (h ▸ by decide)
    simp only [this, ite_false]
    rw [K.gpr r hr, K₁.gpr r hr]
  · simp only [write_mem]
    refine (Outs.cover (rs := [(saveAt S.k, 8)]) ?_ fun r hr => ?_).trans (Outs.cover K.mem fun r hr => ?_)
    · rw [m₁]; exact Outs.of_outside (writeW_outside s.mem _ s.lr (by simp only [saveAt]; omega_using [hl]))
        (List.mem_singleton_self _)
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by simp only [saveAt]; omega_using [],
        by simp only [saveAt]; omega_using [hl]⟩
    · simp only [List.mem_append, List.mem_map, List.mem_singleton] at hr
      rcases hr with ⟨x, hx, rfl⟩ | rfl
      · rcases (hW x hx).2 with h | h
        · exact ⟨_, List.mem_cons_self, h.1, by dsimp only; omega_using [hl, h]⟩
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.1, by dsimp only; omega_using [h]⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by dsimp only; omega_using [hl], by dsimp only; omega_using [hl]⟩
  · simp only [write_mem]; exact I₂.lt j (hO.outs j hj)
  · simp only [write_mem]
    rw [I₂.val 0 (hO.outs 0 (by decide)), I₂.val 1 (hO.outs 1 (by decide)),
      I₂.val 2 (hO.outs 2 (by decide))]

end VG.Proof.Weierstrass.PPC64LE.Point

end

end

/-!
# The ladder by calls of the point functions, on PPC64LE: copies and calls

`copyPt n o a` copies the point at `a` to `o` (`copyPt_ok`), and
`ptCall S dbl` calls `vg_<curve>_point_double` or `vg_<curve>_point_add` on
the working space at `r3` (`ptCall_ok`): it changes only `fnClob`, `O` and
the point functions' own working space, and `O` then holds `rcbAdd` of what
`a`, `3b`, `P` and `Q` (or `P`) stood for (`ptVal`). As on 32-bit ARM
(`Proof/Weierstrass/Arm/LadderPCall.lean`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.Point

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Weierstrass.PPC64LE.Point
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont

/-- `o = a`, for points whose slots (`n` 64-bit words, at multiples of 4) are
in the working space, with `o`'s apart from each other and from `a`'s. -/
theorem copyPt_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) (h3 : At s base .r3 0)
    {n : Nat} {o a : Pt}
    (h4 : ∀ d ∈ [o.x, o.y, o.z, a.x, a.y, a.z], d % 4 = 0)
    (hin : ∀ d ∈ [o.x, o.y, o.z, a.x, a.y, a.z], d + 8 * n ≤ size)
    (hoo : (o.x + 8 * n ≤ o.y ∨ o.y + 8 * n ≤ o.x) ∧ (o.x + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.x) ∧
      (o.y + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.y))
    (hoa : ∀ d ∈ [o.x, o.y, o.z], ∀ e ∈ [a.x, a.y, a.z], d + 8 * n ≤ e ∨ e + 8 * n ≤ d) :
    WP isa (.block (copyPt n o a)) s fun s' =>
      wordsVal s'.mem base o.x n = wordsVal s.mem base a.x n ∧
      wordsVal s'.mem base o.y n = wordsVal s.mem base a.y n ∧
      wordsVal s'.mem base o.z n = wordsVal s.mem base a.z n ∧
      Kp [.r4] s s' ∧ Outs base [(o.x, 8 * n), (o.y, 8 * n), (o.z, 8 * n)] s.mem s'.mem := by
  have hn := hs.nowrap
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin hoa h4
  obtain ⟨iox, ioy, ioz, iax, iay, iaz⟩ := hin
  obtain ⟨⟨xax, xay, xaz⟩, ⟨yax, yay, yaz⟩, ⟨zax, zay, zaz⟩⟩ := hoa
  obtain ⟨xy, xz, yz⟩ := hoo
  obtain ⟨fox, foy, foz, fax, fay, faz⟩ := h4
  rw [copyPt, List.append_assoc, WP.block_append_iff]
  refine WP.mono (copy_ok n hs h3 fox fax (by omega_using [iox]) (by omega_using [iax])
    (by omega_using [xax])) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok n (k₁.ws hs) (k₁.at h3) foy fay (by omega_using [ioy]) (by omega_using [iay])
    (by omega_using [yay])) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  refine WP.mono (copy_ok n (k₂.ws (k₁.ws hs)) (k₂.at (k₁.at h3)) foz faz (by omega_using [ioz])
    (by omega_using [iaz]) (by omega_using [zaz])) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  refine ⟨?_, ?_, ?_, (k₁.trans k₂).trans k₃, ?_⟩
  · rw [O₃.wordsVal (d := o.x) (by omega_using [xz]) (by omega_using [iox, hn]),
      O₂.wordsVal (d := o.x) (by omega_using [xy]) (by omega_using [iox, hn]), e₁]
  · rw [O₃.wordsVal (d := o.y) (by omega_using [yz]) (by omega_using [ioy, hn]), e₂,
      O₁.wordsVal (d := a.y) (by omega_using [xay]) (by omega_using [iay, hn])]
  · rw [e₃, O₂.wordsVal (d := a.z) (by omega_using [yaz]) (by omega_using [iaz, hn]),
      O₁.wordsVal (d := a.z) (by omega_using [xaz]) (by omega_using [iaz, hn])]
  · exact ((Outs.of_outside O₁ (by simp)).trans (Outs.of_outside O₂ (by simp))).trans
      (Outs.of_outside O₃ (by simp))

/-- What the slot of number `x` stands for, in the working space at `base`. -/
def Eb (k m : Nat) [NeZero m] (dbl : Bool) (mem : Mem) (base : Addr) (x : Nat) : Fin m :=
  toM m (2 ^ (64 * k)) (wordsVal mem base (enc k dbl x) k)

/-- What the point function `ptName S a0 dbl` computes from the values of
the slots: Algorithm 9 or 8 for `a0`, else Algorithm 1. -/
def ptVal {m : Nat} [NeZero m] (a0 dbl : Bool) (E : Nat → Fin m) : Fin m × Fin m × Fin m :=
  if a0 then
    (if dbl then Impl.Weierstrass.Point.rcbDbl0 (E 10) (E 3) (E 4) (E 5)
    else Impl.Weierstrass.Point.rcbAdd0m (E 10) (E 3) (E 4) (E 5) (E 6) (E 7))
  else VG.Proof.Weierstrass.rcbAdd (E 9) (E 10) (E 3) (E 4) (E 5) (E 6) (E 7) (E 8)

theorem ptOps_opsOk (a0 dbl : Bool) : OpsOk (ptOps a0 dbl) := by
  cases a0
  · exact rcbIds_opsOk
  · exact ops0_opsOk dbl

theorem ptOps_run {m : Nat} [NeZero m] (E : Nat → Fin m) (a0 dbl : Bool) :
    (runOps (ptOps a0 dbl) E 0, runOps (ptOps a0 dbl) E 1, runOps (ptOps a0 dbl) E 2) =
      ptVal a0 dbl E := by
  cases a0
  · exact rcb_run rcbIds_apart E
  · exact ops0_run E dbl

/-- A call of a point function, from the working space at `r3`: only
`fnClob`, `O` and the own working space change, and `O` holds `rcbAdd` of
what the constants and the operands stood for. -/
theorem ptCall_ok {S : Impl.Weierstrass.Mont.Modulus} [NeZero S.m] (hM : ModOk S.k S.m) (hodd : S.m % 2 = 1)
    (hk3 : 3 ≤ S.k) (hk6 : S.k ≤ 6) (dbl : Bool) {a0 : Bool} {s : State} {base : Addr} (hw : WsReg s base)
    (hlt : ∀ x ∈ rIds, wordsVal s.mem base (enc S.k dbl x) S.k < S.m) :
    WP isa (ptCall S dbl a0) s fun s' => Rk fnClob s s' ∧
      Outs base [(Impl.Weierstrass.Point.oAt S.k, 3 * Impl.Weierstrass.Point.elemBytes S.k),
        (Impl.Weierstrass.Point.ownAt S.k, 4096 - Impl.Weierstrass.Point.ownAt S.k)] s.mem s'.mem ∧
      (∀ j < 3, wordsVal s'.mem base (enc S.k dbl j) S.k < S.m) ∧
      (Eb S.k S.m dbl s'.mem base 0, Eb S.k S.m dbl s'.mem base 1, Eb S.k S.m dbl s'.mem base 2) =
        ptVal a0 dbl (Eb S.k S.m dbl s.mem base) := by
  have hcov : Covers [⟨base, 8192⟩] s.wr := Covers.of_mem fun r hr => by
    rw [List.mem_singleton] at hr; subst hr; exact hw.wr
  have g3 : ∀ t : State, (t.callEntry.withRegions [] [⟨base, 8192⟩]).gpr .r3 = t.gpr .r3 := fun t => by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide)]
  rw [ptCall]
  refine WP.call (k := ⟨fun t => PrePt S.k S.m dbl t ∧ t.gpr .r3 = base ∧ t.mem = s.mem,
      fun t t' => (∀ r, r ∉ fnClob → t'.gpr r = t.gpr r) ∧
        Outs (t.gpr .r3) [(Impl.Weierstrass.Point.oAt S.k, 3 * Impl.Weierstrass.Point.elemBytes S.k),
          (Impl.Weierstrass.Point.ownAt S.k, 4096 - Impl.Weierstrass.Point.ownAt S.k)] t.mem t'.mem ∧
        (∀ j < 3, wordsVal t'.mem (t.gpr .r3) (enc S.k dbl j) S.k < S.m) ∧
        (toM S.m (2 ^ (64 * S.k)) (wordsVal t'.mem (t.gpr .r3) (enc S.k dbl 0) S.k),
          toM S.m (2 ^ (64 * S.k)) (wordsVal t'.mem (t.gpr .r3) (enc S.k dbl 1) S.k),
          toM S.m (2 ^ (64 * S.k)) (wordsVal t'.mem (t.gpr .r3) (enc S.k dbl 2) S.k)) =
        ptVal a0 dbl (Eb S.k S.m dbl t.mem (t.gpr .r3)),
      fun _ _ => True⟩)
    (fun t ⟨hp, _, _⟩ => by
      obtain ⟨tr, t', he, A, G, O, L, E⟩ := fnOps_ok hM hodd (ptOps_opsOk a0 dbl) hp
      exact ⟨tr, t', he, A, G, O, L, E.trans (ptOps_run _ a0 dbl)⟩)
    (rd := []) (wr := [⟨base, 8192⟩])
    ⟨⟨by rw [State.withRegions_wr, g3, hw.r3], by rw [g3, hw.r3]; exact hw.nowrap, hk3, hk6,
        fun x hx => by
          rw [g3, hw.r3, State.withRegions_mem, State.callEntry_mem]
          exact hlt x hx⟩,
      by rw [g3, hw.r3],
      by rw [State.withRegions_mem, State.callEntry_mem]⟩
    (Covers.right hcov) hcov ?_ (by cases a0 <;> cases dbl <;> rfl)
  intro s' r' w' p' _ _ _ ⟨G, O, L, E⟩
  simp only [State.withRegions_mem, State.callEntry_mem, g3, hw.r3, State.withRegions_gpr] at G O L E
  refine ⟨⟨fun r hr => ?_, r', w', p'⟩, O, L, E⟩
  have hl : r ∉ linkRegs := not_mem_sub hr
  rw [G r hr, State.callEntry_gpr _ hl]

end VG.Proof.Weierstrass.PPC64LE.Point

end

end

/-! ### `Weierstrass.PPC64LE.Fprog`, which this module and modules that import it used -/

section

/-!
# Field programs on slots, on PPC64LE

`fprog S ops` (`Impl/Weierstrass/PPC64LE/Call.lean`) runs the field
operations `ops` on slots of the working space, one by one by calls of the
functions of the modulus `S` (`fprog_ok`), as on 32-bit ARM
(`Proof/Weierstrass/Arm/Bits.lean`): on slots that are apart from each other
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
    refine outs_wordsVal hk.mem (fun r hr => ?_) (by omega_using [hown, h1])
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
        (by rw [hk]; omega_using [hA, hB]))
      fun s' ⟨K, heq⟩ => ?_
    rw [hk] at K heq
    refine ⟨.of_call K, hI.update hL hS.1 (.of_call K) ?_ ?_⟩
    · rw [heq]; exact Nat.mod_lt _ (by omega_using [hA])
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
    · rw [heq]; exact Nat.mod_lt _ (by omega_using [hA])
    · rw [heq, toM_sub (by omega_using [hB]), hI.val a hR.1, hI.val b hR.2]

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

end

end

/-!
# The ladder, on PPC64LE

An iteration of `ladder L S` (`Impl/Weierstrass/PPC64LE.lean`) computes
`D = R + R` and `T = D + G` with the complete addition (`rcb_ok`), and
selects `T` into `R` if the scalar's bit is set, else `D`
(`ladderBody_ok`), for the scalar `k` whose bits are the table at `L.bits`,
as on 32-bit ARM (`Proof/Weierstrass/Arm/Ladder.lean`). `ladder_ok` takes the
loop's invariant `Q j` on what `R` holds, and that an iteration keeps it
(`Step`): the callers' invariant is that `R` represents `[k >>> j]P`
(`step_rep`, in `Rep.lean`), and only they need the group law. The field
arithmetic is calls of the functions of `S`, whose own working space is
above the ladder's slots (`LadLay` of `own n` bytes) and below its table
(`LadLayI`). This is the ladder of curves whose points do not fit the point
functions' slots (`ladderP`, for coordinates of more than 6 words).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.Point

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont
open VG.Spec.Weierstrass (Curve Fe)

/-- What a slot holding `x` stands for, modulo `C.p`. -/
abbrev tmv (C : Curve) (n : Nat) (base : Addr) (s : State) (x : Nat) : Fe C :=
  toM C.p (2 ^ (64 * n)) (wordsVal s.mem base x n)

/-- That an iteration keeps the invariant `Q`: from `(X : Y : Z)` that
`Q (j + 1)` accepts, `Q j` accepts `T = D + G` if bit `j` of `k` is set, else
`D = (X : Y : Z) + (X : Y : Z)`, by the complete addition with the curve's
`a`, `3b` and `G` as the slots `L.S.a`, `L.S.b3` and `L.G` hold them (for
`a0`, by the formulas for `a = 0`). -/
def Step (L : LadderCfg) (C : Curve) (base : Addr) (s : State) (k : Nat)
    (Q : Nat → Fe C → Fe C → Fe C → Prop) (a0 : Bool := false) : Prop :=
  ∀ j < L.nbits, ∀ X Y Z X2 Y2 Z2 X3 Y3 Z3 : Fe C, Q (j + 1) X Y Z →
    ladDbl a0 (tmv C L.M.n base s L.S.a) (tmv C L.M.n base s L.S.b3) X Y Z = (X2, Y2, Z2) →
    ladAdd a0 (tmv C L.M.n base s L.S.a) (tmv C L.M.n base s L.S.b3) X2 Y2 Z2
      (tmv C L.M.n base s L.G.x) (tmv C L.M.n base s L.G.y) (tmv C L.M.n base s L.G.z) =
      (X3, Y3, Z3) →
    Q j (if k.testBit j then X3 else X2) (if k.testBit j then Y3 else Y2)
      (if k.testBit j then Z3 else Z2)

/-- What the ladder writes: `ladW` and the functions' own working space. -/
def ladWx (L : LadderCfg) : List (Nat × Nat) := ladW L ++ [(own L.M.n, 64 * L.M.n)]

/-- The ladder's slots: `LadLay` below the functions' own working space, at
multiples of 4, with the table of bits above it and its length an
immediate. -/
structure LadLayI (L : LadderCfg) : Prop where
  lay : LadLay L (own L.M.n) 8192
  al : ∀ x ∈ ladSlots L, x % 4 = 0
  bits : 4096 ≤ L.bits
  nbits : L.nbits < 2 ^ 15

theorem own_add (n : Nat) (h : 8 * n ≤ own n) : own n + 64 * n = 4096 := by
  simp only [own, Impl.Weierstrass.Mont.ownAt, Impl.Weierstrass.Mont.ownBytes] at h ⊢; omega_using [h]

/-- A slot the ladder does not write is apart from what it writes. -/
theorem LadLayI.apart_wx {L : LadderCfg} (hL : LadLayI L) {x : Nat} (hx : x ∈ ladSlots L)
    (hxw : x ∉ ladWs L) : ∀ w ∈ ladWx L, x + 8 * L.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := by
  intro w hw
  simp only [ladWx, List.mem_append, List.mem_singleton] at hw
  rcases hw with hw | rfl
  · exact hL.lay.apart_w hx hxw w hw
  · exact .inl (hL.lay.lay.le x hx)

/-- The table of bits is apart from what the ladder writes. -/
theorem LadLayI.bits_wx {L : LadderCfg} (hL : LadLayI L) {t : Nat} (ht : t < L.nbits) :
    ∀ w ∈ ladWx L, L.bits + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ L.bits + t := by
  have hR := hL.lay.lay.le _ (ladPts_slots L L.R.x (by simp))
  have ho := own_add L.M.n (by omega_using [hR])
  have hb := hL.bits
  intro w hw
  simp only [ladWx, List.mem_append, List.mem_singleton] at hw
  rcases hw with hw | rfl
  · have := hL.lay.bits_w w hw; omega_using [ht, this]
  · simp only; omega_using [ho, hb]

/-- The loop's invariant at `r31 = j`: `Q j` accepts what `R` holds. -/
structure LadInv (L : LadderCfg) (C : Curve) (base : Addr) (Q : Nat → Fe C → Fe C → Fe C → Prop)
    (s₀ s : State) (j : Nat) : Prop where
  ws : WsReg s base
  r31 : s.gpr .r31 = BitVec.ofNat 64 j
  keep : Rk powClob s₀ s
  unch : Unch base (ladWx L) s₀.mem s.mem
  lt : ∀ x ∈ [L.R.x, L.R.y, L.R.z], wordsVal s.mem base x L.M.n < C.p
  q : Q j (tmv C L.M.n base s L.R.x) (tmv C L.M.n base s L.R.y) (tmv C L.M.n base s L.R.z)

/-- After both additions: `D` and `T` hold `R + R` and `D + G`. -/
structure AddsPost (L : LadderCfg) (C : Curve) (base : Addr) (E : Nat → Fe C) (s s' : State) : Prop where
  ws : WsReg s' base
  keep : Rk fnClob s s'
  unch : Unch base (ladWx L) s.mem s'.mem
  lt : ∀ x ∈ [L.D.x, L.D.y, L.D.z, L.T.x, L.T.y, L.T.z], wordsVal s'.mem base x L.M.n < C.p
  vals : ∃ X2 Y2 Z2 X3 Y3 Z3 : Fe C,
    VG.Proof.Weierstrass.rcbAdd (E L.S.a) (E L.S.b3) (E L.R.x) (E L.R.y) (E L.R.z) (E L.R.x)
      (E L.R.y) (E L.R.z) = (X2, Y2, Z2) ∧
    VG.Proof.Weierstrass.rcbAdd (E L.S.a) (E L.S.b3) X2 Y2 Z2 (E L.G.x) (E L.G.y) (E L.G.z) =
      (X3, Y3, Z3) ∧
    tmv C L.M.n base s' L.D.x = X2 ∧ tmv C L.M.n base s' L.D.y = Y2 ∧
    tmv C L.M.n base s' L.D.z = Z2 ∧ tmv C L.M.n base s' L.T.x = X3 ∧
    tmv C L.M.n base s' L.T.y = Y3 ∧ tmv C L.M.n base s' L.T.z = Z3

/-- What a program writing the slots `W` of `ladWs`, through the functions,
changes of what the ladder writes. -/
theorem keep_unch {L : LadderCfg} {base : Addr} {W : List Nat} {s s' : State}
    (h : KeepR L.M.n (fun x => x) base W s s') (hW : ∀ w ∈ W, w ∈ ladWs L) :
    Unch base (ladWx L) s.mem s'.mem :=
  fun x hx => h.mem x fun r hr => hx r (by
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hr
    simp only [ladWx, ladW, List.mem_append, List.mem_map, List.mem_singleton]
    rcases hr with ⟨w, hw, rfl⟩ | rfl
    · exact .inl (.inl ⟨w, hW w hw, rfl⟩)
    · exact .inr rfl)

/-- The two additions, from a state holding `E` in the slots `ladR`. -/
theorem ladAdds_ok {L : LadderCfg} {C : Curve} {base : Addr} (hL : LadLayI L)
    {S : Impl.Weierstrass.Mont.Modulus} (hM : ModOk S.k S.m) (hkS : S.k = L.M.n) (hmS : S.m = C.p)
    (hp : UnitMod C.p (2 ^ (64 * L.M.n))) {E : Nat → Fe C} {s : State}
    (hI : Inv L.M.n base C.p (· ∈ ladSlots L) (ladR L) E s) {rest : Prog isa}
    {Q : State → Prop} (h : ∀ s', AddsPost L C base E s s' → WP isa rest s' Q) :
    WP isa (.seq (fprog S (rcb L.S L.R L.R L.D)) (.seq (fprog S (rcb L.S L.D L.G L.T)) rest))
      s Q := by
  obtain ⟨c, w, m', k', d⟩ := S
  dsimp only at hkS hmS hM ⊢
  subst hkS hmS
  have hL' := hL.lay
  refine WP.seq (WP.mono (rcb_ok (S' := ⟨c, w, C.p, L.M.n, d⟩) hM rfl hL'.lay hp hL'.a1 (ladR_S₁ L) hI
    (ladR_V₁ L)) fun s₂ ⟨k₂, I₂, t₂, n₂⟩ => ?_)
  refine WP.seq (WP.mono (rcb_ok (S' := ⟨c, w, C.p, L.M.n, d⟩) hM rfl hL'.lay hp hL'.a2 (ladR_S₂ L) I₂
    (ladR_V₂ L)) fun s₃ ⟨k₃, I₃, t₃, n₃⟩ => h s₃ ?_)
  have hro : ∀ x ∈ ladRo L, x ∉ rcbW L.S L.D := fun x hx h =>
    hL'.ro x hx (by simp only [ladWs, List.mem_append]; exact Or.inl (Or.inr h))
  have hDT : ∀ x ∈ [L.D.x, L.D.y, L.D.z], x ∉ rcbW L.S L.T := fun x hx =>
    hL'.a2.apart x (by revert x; sub_list)
  have hD : ∀ x ∈ [L.D.x, L.D.y, L.D.z], x ∈ rcbW L.S L.T ++ (rcbW L.S L.D ++ ladR L) := by
    sub_list
  have hT : ∀ x ∈ [L.T.x, L.T.y, L.T.z], x ∈ rcbW L.S L.T ++ (rcbW L.S L.D ++ ladR L) := by
    sub_list
  refine ⟨I₃.ws, ⟨fun r hr => (k₃.gpr r hr).trans (k₂.gpr r hr), k₃.rd.trans k₂.rd, k₃.wr.trans k₂.wr,
    k₃.sp.trans k₂.sp⟩, ((keep_unch k₂ fun w hw => ?_).trans (keep_unch k₃ fun w hw => ?_)).mono
      fun w hw => ?_, fun x hx => ?_, ?_⟩
  · simp only [ladWs, List.mem_append]; exact .inl (.inr hw)
  · simp only [ladWs, List.mem_append]; exact .inr hw
  · rcases List.mem_append.mp hw with hw | hw <;> exact hw
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    exact I₃.lt x (by rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> mem_list)
  · refine ⟨_, _, _, _, _, _, t₂.symm, ?_, (I₃.val L.D.x (hD L.D.x (by simp))).trans (n₃ L.D.x (hDT L.D.x (by simp))),
      (I₃.val L.D.y (hD L.D.y (by simp))).trans (n₃ L.D.y (hDT L.D.y (by simp))),
      (I₃.val L.D.z (hD L.D.z (by simp))).trans (n₃ L.D.z (hDT L.D.z (by simp))),
      I₃.val L.T.x (hT L.T.x (by simp)), I₃.val L.T.y (hT L.T.y (by simp)),
      I₃.val L.T.z (hT L.T.z (by simp))⟩
    rw [← n₂ L.S.a (hro L.S.a (by simp [ladRo])), ← n₂ L.S.b3 (hro L.S.b3 (by simp [ladRo])),
      ← n₂ L.G.x (hro L.G.x (by simp [ladRo])), ← n₂ L.G.y (hro L.G.y (by simp [ladRo])),
      ← n₂ L.G.z (hro L.G.z (by simp [ladRo]))]
    exact t₃.symm

/-- The mask of the bit, and `R = D` or `T` by it. -/
theorem ladSel_ok {L : LadderCfg} {base : Addr} (hL : LadLayI L) {s : State} (hw : WsReg s base)
    {t : Nat} (ht : t < L.nbits) (h31 : s.gpr .r31 = BitVec.ofNat 64 t)
    {c : Bool} (hc : s.mem (off base (L.bits + t)) = if c then 1 else 0) :
    WP isa (.block (bitMask L.bits ++ selPt L.M.n L.R L.D L.T)) s
      fun s' => Kp [.r4, .r5, .r10] s s' ∧
        Unch base [(L.R.x, 8 * L.M.n), (L.R.y, 8 * L.M.n), (L.R.z, 8 * L.M.n)] s.mem s'.mem ∧
        wordsVal s'.mem base L.R.x L.M.n =
          (if c then wordsVal s.mem base L.T.x L.M.n else wordsVal s.mem base L.D.x L.M.n) ∧
        wordsVal s'.mem base L.R.y L.M.n =
          (if c then wordsVal s.mem base L.T.y L.M.n else wordsVal s.mem base L.D.y L.M.n) ∧
        wordsVal s'.mem base L.R.z L.M.n =
          (if c then wordsVal s.mem base L.T.z L.M.n else wordsVal s.mem base L.D.z L.M.n) := by
  have hlb := hL.lay.bits
  have hx := hL.lay.lay.le _ (ladPts_slots L L.R.x (by simp))
  have ho := own_add L.M.n (by omega_using [hx])
  refine wp_append (WP.mono (bitMask_bool_ok hw.ws hw.at3 h31 (by omega_using [ht, hlb]) (c := c) hc)
    fun s₄ ⟨c₄, k₄, hm₄⟩ => ?_)
  have hap : ∀ x ∈ [L.R.x, L.R.y, L.R.z, L.D.x, L.D.y, L.D.z, L.T.x, L.T.y, L.T.z],
      ∀ y ∈ [L.R.x, L.R.y, L.R.z, L.D.x, L.D.y, L.D.z, L.T.x, L.T.y, L.T.z], x ≠ y →
      x + 8 * L.M.n ≤ y ∨ y + 8 * L.M.n ≤ x :=
    fun x hx y hy hxy => hL.lay.lay.apart x y (ladPts_slots L x hx) (ladPts_slots L y hy) hxy
  obtain ⟨rxy, rxz, ryz⟩ := hL.lay.rne
  refine WP.mono (selPt_ok (k₄.ws hw.ws) (k₄.at hw.at3) c c₄ (n := L.M.n) (o := L.R) (a := L.D) (b := L.T)
    (fun d hd => hL.al d (ladPts_slots L d hd))
    (fun d hd => by have := hL.lay.lay.le d (ladPts_slots L d hd); omega_using [ho, this])
    ⟨hap L.R.x (by simp) L.R.y (by simp) rxy, hap L.R.x (by simp) L.R.z (by simp) rxz,
      hap L.R.y (by simp) L.R.z (by simp) ryz⟩
    (fun d hd e he => hap d (List.mem_append_left [L.D.x, L.D.y, L.D.z, L.T.x, L.T.y, L.T.z] hd) e
      (List.mem_append_right [L.R.x, L.R.y, L.R.z] he) fun h => hL.lay.rdt d hd (h ▸ he)))
    fun s₅ ⟨ex₅, ey₅, ez₅, k₅, O₅⟩ => ?_
  refine ⟨k₄.trans (k₅.mono (by decide)), by rw [← hm₄]; exact O₅, by rw [ex₅, hm₄], by rw [ey₅, hm₄],
    by rw [ez₅, hm₄]⟩

section body
variable {L : LadderCfg} {C : Curve} {base : Addr}

/-- An iteration. -/
theorem ladderBody_ok {k : Nat} {Q : Nat → Fe C → Fe C → Fe C → Prop} {S : Impl.Weierstrass.Mont.Modulus}
    (hM : ModOk S.k S.m) (hkS : S.k = L.M.n) (hmS : S.m = C.p) (hp : UnitMod C.p (2 ^ (64 * L.M.n)))
    (hL : LadLayI L) {s₀ : State} (hlt₀ : ∀ x ∈ ladRo L, wordsVal s₀.mem base x L.M.n < C.p)
    (hstep : Step L C base s₀ k Q)
    (hbits : ∀ t < L.nbits, s₀.mem (off base (L.bits + t)) = if k.testBit t then 1 else 0)
    {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j ≤ L.nbits) (hI : LadInv L C base Q s₀ s j) :
    WP isa (ladderBody L S) s fun s' => LadInv L C base Q s₀ s' (j - 1) := by
  have hn := hI.ws.nowrap
  have hnb := hL.lay.nbits
  have hlb := hL.lay.bits
  -- The slots read only hold what they held at the start.
  have hro : ∀ x ∈ ladRo L, wordsVal s.mem base x L.M.n = wordsVal s₀.mem base x L.M.n :=
    fun x hx => hI.unch.wordsVal
      (hL.apart_wx (ladR_slots L x (mem_ladRo_ladR hx)) (hL.lay.ro x hx))
      (by have := hL.lay.lay.le x (ladR_slots L x (mem_ladRo_ladR hx)); have := own_lt L.M.n; omega_arith)
  have hE : ∀ x ∈ ladRo L, tmv C L.M.n base s x = tmv C L.M.n base s₀ x := fun x hx => by
    rw [tmv, hro x hx]
  -- `r31 -= 1`.
  rw [ladderBody]
  refine WP.seq (wp_decCounter hj hI.r31 (WP.block_nil ?_))
  generalize hs₁ : s.write .r31 (BitVec.ofNat 64 (j - 1)) = s₁
  have K₁ : Kp [.r31] s s₁ := by rw [← hs₁]; exact Kp.write _ _ (by decide)
  have m₁ : s₁.mem = s.mem := by rw [← hs₁]; rfl
  have c₁ : s₁.gpr .r31 = BitVec.ofNat 64 (j - 1) := by rw [← hs₁]; simp only [write_gpr, ite_true]
  have I₁ : Inv L.M.n base C.p (· ∈ ladSlots L) (ladR L) (tmv C L.M.n base s) s₁ := by
    refine ⟨hI.ws.of_kp K₁, ladR_slots L, fun x hx => ?_, fun x _ => by rw [tmv, m₁]⟩
    rw [m₁]
    simp only [ladR, List.mem_append] at hx
    rcases hx with hx | hx
    · rw [hro x hx]; exact hlt₀ x hx
    · exact hI.lt x hx
  -- The additions.
  refine ladAdds_ok hL hM hkS hmS hp I₁ fun s₃ A => ?_
  obtain ⟨X2, Y2, Z2, X3, Y3, Z3, h2, h3, dx, dy, dz, tx, ty, tz⟩ := A.vals
  have hU₃ : Unch base (ladWx L) s₀.mem s₃.mem :=
    (hI.unch.trans (by rw [← m₁]; exact A.unch)).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw <;> exact hw
  have hbyte : s₃.mem (off base (L.bits + (j - 1))) = if k.testBit (j - 1) then 1 else 0 := by
    rw [hU₃.byte (hL.bits_wx (by omega_using [hj, hjn])) (by omega_using [hjn, hlb]), hbits _ (by omega_using [hj, hjn])]
  have c₃ : s₃.gpr .r31 = BitVec.ofNat 64 (j - 1) := by rw [A.keep.g, c₁]
  have hstep := hstep (j - 1) (by omega_using [hj, hjn]) (tmv C L.M.n base s L.R.x) (tmv C L.M.n base s L.R.y)
    (tmv C L.M.n base s L.R.z) X2 Y2 Z2 X3 Y3 Z3 (by rw [Nat.sub_add_cancel hj]; exact hI.q)
    (by rw [← hE L.S.a (by simp [ladRo]), ← hE L.S.b3 (by simp [ladRo])]; exact h2)
    (by rw [← hE L.S.a (by simp [ladRo]), ← hE L.S.b3 (by simp [ladRo]), ← hE L.G.x (by simp [ladRo]),
        ← hE L.G.y (by simp [ladRo]), ← hE L.G.z (by simp [ladRo])]; exact h3)
  have K₃ : Rk powClob s₀ s₃ :=
    (hI.keep.trans (K₁.rk (rs' := powClob))).trans (A.keep.mono (rs' := powClob))
  refine WP.mono (ladSel_ok hL A.ws (by omega_using [hj, hjn]) c₃ hbyte) fun s' ⟨k', U', ex, ey, ez⟩ => ?_
  refine ⟨A.ws.of_kp k', by rw [k'.g, c₃], K₃.trans (k'.rk (rs' := powClob)), ?_, ?_, ?_⟩
  · exact (hU₃.trans U').mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hw
      · exact List.mem_append_left _ (mem_ladW_R w hw)
  · have hlt := A.lt
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlt ⊢
    refine ⟨?_, ?_, ?_⟩
    · rw [ex]; split
      · exact hlt.2.2.2.1
      · exact hlt.1
    · rw [ey]; split
      · exact hlt.2.2.2.2.1
      · exact hlt.2.1
    · rw [ez]; split
      · exact hlt.2.2.2.2.2
      · exact hlt.2.2.1
  · have hx : tmv C L.M.n base s' L.R.x = if k.testBit (j - 1) then X3 else X2 := by
      show toM _ _ _ = _
      rw [ex]; split
      · exact tx
      · exact dx
    have hy : tmv C L.M.n base s' L.R.y = if k.testBit (j - 1) then Y3 else Y2 := by
      show toM _ _ _ = _
      rw [ey]; split
      · exact ty
      · exact dy
    have hz : tmv C L.M.n base s' L.R.z = if k.testBit (j - 1) then Z3 else Z2 := by
      show toM _ _ _ = _
      rw [ez]; split
      · exact tz
      · exact dz
    rw [hx, hy, hz]
    exact hstep

/-- `Q 0` accepts what `R` holds at the end, if `Q L.nbits` accepts what it
holds at the start and an iteration keeps `Q` (`Step`), for the scalar `k`
whose bits are the table at `L.bits`; only `powClob` and `ladWx` change. -/
theorem ladder_ok {k : Nat} {Q : Nat → Fe C → Fe C → Fe C → Prop} {S : Impl.Weierstrass.Mont.Modulus}
    (hM : ModOk S.k S.m) (hkS : S.k = L.M.n) (hmS : S.m = C.p) (hp : UnitMod C.p (2 ^ (64 * L.M.n)))
    (hL : LadLayI L) {s : State} (hs : WsReg s base)
    (hlt : ∀ x ∈ ladR L, wordsVal s.mem base x L.M.n < C.p) (hstep : Step L C base s k Q)
    (hR : Q L.nbits (tmv C L.M.n base s L.R.x) (tmv C L.M.n base s L.R.y) (tmv C L.M.n base s L.R.z))
    (hbits : ∀ t < L.nbits, s.mem (off base (L.bits + t)) = if k.testBit t then 1 else 0) :
    WP isa (ladder L S) s fun s' => Rk powClob s s' ∧ Unch base (ladWx L) s.mem s'.mem ∧
      (∀ x ∈ [L.R.x, L.R.y, L.R.z], wordsVal s'.mem base x L.M.n < C.p) ∧
      Q 0 (tmv C L.M.n base s' L.R.x) (tmv C L.M.n base s' L.R.y) (tmv C L.M.n base s' L.R.z) := by
  have hnb := hL.lay.nbits
  have hnb' := hL.nbits
  rw [ladder]
  refine WP.seq (wp_step (exec_li hnb') (WP.block_nil ?_))
  have K₁ : Kp [.r31] s (s.write .r31 (BitVec.ofNat 64 L.nbits)) := Kp.write _ _ (by decide)
  refine countLoop_ok (Inv := fun j s' => LadInv L C base Q s s' j) (n := L.nbits)
    (fun j s' hi => hi.r31)
    (fun j s' h1 h2 hi => ladderBody_ok hM hkS hmS hp hL (fun x hx => hlt x (mem_ladRo_ladR hx))
      hstep hbits h1 h2 hi)
    (fun s' hi => ⟨hi.keep, hi.unch, hi.lt, hi.q⟩) hnb.1 (by omega_using [hnb])
    ⟨hs.of_kp K₁, by simp only [write_gpr, ite_true], K₁.rk, Unch.refl _ _ _,
      fun x hx => hlt x (List.mem_append_right _ hx), hR⟩

end body

end VG.Proof.Weierstrass.PPC64LE.Point

end

end

/-!
# The ladder by calls of the point functions, on PPC64LE

`ladderP L S` (`Impl/Weierstrass/PPC64LE/LadderP.lean`), for coordinates of
3 to 6 words, takes the loop's invariant `Q j` on what `R` holds to `Q 0`, if
an iteration keeps it (`Step`), for the scalar `k` whose bits are the table at
`L.bits` (`ladderP_ok`), as on 32-bit ARM
(`Proof/Weierstrass/Arm/LadderP.lean`): the setup copies `G`, `a` and `3b`
to the point functions' `Q`, `a` and `3b` (`ladderSetup_ok`, `CpOk`); an
iteration (`ladderPBody_ok`) copies `R` to `P`, so that the doubling's call
leaves `D = R + R` in `O` (`ptCall_ok`), copies it to `P`, so that the
addition's leaves `T = D + G` in `O`, and selects `R = T` or `D`. The
ladder's slots lie below the point functions' (`LadPtLay`); it writes `R`
and the point functions' slots and own working space (`ladWp`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.PPC64LE.Point

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Weierstrass.PPC64LE.Point
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont
open VG.Spec.Weierstrass (Curve Fe)
open VG.Impl.Weierstrass.Point (elemBytes ownAt aAt b3At oAt pAt qAt)

/-- Apart from each of a few ranges, for numbers of the layout. -/
tactic_template "ppc_apart" : tactic => `(tactic| (simp only [List.mem_cons, List.mem_append, List.not_mem_nil,
  or_false, or_imp, forall_and, forall_eq_or_imp, forall_eq, List.mem_singleton]; omega_arith))

/-- What the ladder by calls of the point functions writes: `R` and the
point functions' slots and own working space. -/
def ladWpt (L : LadderCfg) : List (Nat × Nat) :=
  [(L.R.x, 8 * L.M.n), (L.R.y, 8 * L.M.n), (L.R.z, 8 * L.M.n), (oAt L.M.n, 4096 - oAt L.M.n)]

/-- The point functions' slots and own working space, which the ladder
writes if it calls them. -/
def ptW (n : Nat) : List (Nat × Nat) := if n ≤ 6 then [(oAt n, 4096 - oAt n)] else []

/-- What `ladderP` writes, whether it calls the point functions or not. -/
def ladWp (L : LadderCfg) : List (Nat × Nat) := ladWx L ++ ptW L.M.n

/-- The ladder's slots: `a`, `3b`, `G` and `R` below the point functions'
slots, at multiples of 4, `R`'s apart; and its table of bits above the
functions' own working space. -/
structure LadPtLay (L : LadderCfg) : Prop where
  k3 : 3 ≤ L.M.n
  k6 : L.M.n ≤ 6
  a : L.S.a + 8 * L.M.n ≤ oAt L.M.n
  b3 : L.S.b3 + 8 * L.M.n ≤ oAt L.M.n
  gx : L.G.x + 8 * L.M.n ≤ oAt L.M.n
  gy : L.G.y + 8 * L.M.n ≤ oAt L.M.n
  gz : L.G.z + 8 * L.M.n ≤ oAt L.M.n
  rx : L.R.x + 8 * L.M.n ≤ oAt L.M.n
  ry : L.R.y + 8 * L.M.n ≤ oAt L.M.n
  rz : L.R.z + 8 * L.M.n ≤ oAt L.M.n
  al : L.S.a % 4 = 0 ∧ L.S.b3 % 4 = 0 ∧ L.G.x % 4 = 0 ∧ L.G.y % 4 = 0 ∧ L.G.z % 4 = 0 ∧
    L.R.x % 4 = 0 ∧ L.R.y % 4 = 0 ∧ L.R.z % 4 = 0
  rne : (L.R.x + 8 * L.M.n ≤ L.R.y ∨ L.R.y + 8 * L.M.n ≤ L.R.x) ∧
    (L.R.x + 8 * L.M.n ≤ L.R.z ∨ L.R.z + 8 * L.M.n ≤ L.R.x) ∧
    (L.R.y + 8 * L.M.n ≤ L.R.z ∨ L.R.z + 8 * L.M.n ≤ L.R.y)
  bits : 4096 ≤ L.bits
  bitsE : L.bits + L.nbits ≤ 8192
  nbits : 1 ≤ L.nbits ∧ L.nbits < 2 ^ 15

section enc
variable (k : Nat) (dbl : Bool)

theorem enc_0 : enc k dbl 0 = oAt k := by simp [enc]
theorem enc_1 : enc k dbl 1 = oAt k + elemBytes k := by simp [enc]
theorem enc_2 : enc k dbl 2 = oAt k + 2 * elemBytes k := by simp [enc]; omega_arith
theorem enc_3 : enc k dbl 3 = pAt k := by simp [enc]
theorem enc_4 : enc k dbl 4 = pAt k + elemBytes k := by simp [enc]
theorem enc_5 : enc k dbl 5 = pAt k + 2 * elemBytes k := by simp [enc]; omega_arith
theorem enc_6 : enc k dbl 6 = if dbl then pAt k else qAt k := by simp [enc]
theorem enc_7 : enc k dbl 7 = (if dbl then pAt k else qAt k) + elemBytes k := by simp [enc]
theorem enc_8 : enc k dbl 8 = (if dbl then pAt k else qAt k) + 2 * elemBytes k := by simp [enc]; omega_arith
theorem enc_9 : enc k dbl 9 = aAt k := by simp [enc]
theorem enc_10 : enc k dbl 10 = b3At k := by simp [enc]

end enc

/-- The bounds a call needs, by offset. -/
theorem rIds_lt_of {k m : Nat} (dbl : Bool) {mem : Mem} {base : Addr}
    (h : ∀ x ∈ [pAt k, pAt k + elemBytes k, pAt k + 2 * elemBytes k,
      (if dbl then pAt k else qAt k), (if dbl then pAt k else qAt k) + elemBytes k,
      (if dbl then pAt k else qAt k) + 2 * elemBytes k, aAt k, b3At k],
      wordsVal mem base x k < m) :
    ∀ x ∈ rIds, wordsVal mem base (enc k dbl x) k < m := by
  intro x hx
  simp only [rIds, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [enc_3, enc_4, enc_5, enc_6, enc_7, enc_8, enc_9, enc_10] <;> exact h _ (by simp)

/-- The point functions' `Q`, `a` and `3b` in `m` hold `G`, `a` and `3b` of
`m₀`. -/
def CpOk (L : LadderCfg) (base : Addr) (m m₀ : Mem) : Prop :=
  wordsVal m base (qAt L.M.n) L.M.n = wordsVal m₀ base L.G.x L.M.n ∧
  wordsVal m base (qAt L.M.n + elemBytes L.M.n) L.M.n = wordsVal m₀ base L.G.y L.M.n ∧
  wordsVal m base (qAt L.M.n + 2 * elemBytes L.M.n) L.M.n = wordsVal m₀ base L.G.z L.M.n ∧
  wordsVal m base (aAt L.M.n) L.M.n = wordsVal m₀ base L.S.a L.M.n ∧
  wordsVal m base (b3At L.M.n) L.M.n = wordsVal m₀ base L.S.b3 L.M.n

/-- The copies survive changes apart from them. -/
theorem CpOk.keep {L : LadderCfg} {base : Addr} {m m' m₀ : Mem} (h : CpOk L base m m₀)
    (hk3 : 3 ≤ L.M.n) (hk6 : L.M.n ≤ 6) {W : List (Nat × Nat)} (hU : Unch base W m m')
    (hW : ∀ w ∈ W, w.1 + w.2 ≤ qAt L.M.n ∨ ownAt L.M.n ≤ w.1) :
    CpOk L base m' m₀ := by
  obtain ⟨h1, h2, he, hb3, ha, hq, -, -, -, -⟩ := lay_nums hk3 hk6
  obtain ap : ∀ x, qAt L.M.n ≤ x → x + 8 * L.M.n ≤ ownAt L.M.n →
      ∀ w ∈ W, x + 8 * L.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := fun x h1 h2 w hw =>
    (hW w hw).elim (fun h => .inr (Nat.le_trans h h1)) (fun h => .inl (Nat.le_trans h2 h))
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨by rw [hU.wordsVal (ap _ (by omega_arith) (by omega_arith)) (by omega_arith)]; exact h1,
    by rw [hU.wordsVal (ap _ (by omega_arith) (by omega_arith)) (by omega_arith)]; exact h2,
    by rw [hU.wordsVal (ap _ (by omega_arith) (by omega_arith)) (by omega_arith)]; exact h3,
    by rw [hU.wordsVal (ap _ (by omega_arith) (by omega_arith)) (by omega_arith)]; exact h4,
    by rw [hU.wordsVal (ap _ (by omega_arith) (by omega_arith)) (by omega_arith)]; exact h5⟩

/-- The loop's invariant at `r31 = j`: `Q j` accepts what `R` holds, and the
point functions' `Q`, `a` and `3b` hold `G`, `a` and `3b`. -/
structure LadInvP (L : LadderCfg) (C : Curve) (base : Addr)
    (Q : Nat → Fe C → Fe C → Fe C → Prop) (s₀ s : State) (j : Nat) : Prop where
  ws : WsReg s base
  r31 : s.gpr .r31 = BitVec.ofNat 64 j
  keep : Rk powClob s₀ s
  unch : Unch base (ladWpt L) s₀.mem s.mem
  lt : ∀ x ∈ [L.R.x, L.R.y, L.R.z], wordsVal s.mem base x L.M.n < C.p
  q : Q j (tmv C L.M.n base s L.R.x) (tmv C L.M.n base s L.R.y) (tmv C L.M.n base s L.R.z)
  cp : CpOk L base s.mem s₀.mem

/-- What a copy of three slots `a` below `P` or `Q` into it needs. -/
theorem copyPt_conds {k o : Nat} {a : Pt} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) (ho : o = pAt k ∨ o = qAt k)
    (hax : a.x + 8 * k ≤ o) (hay : a.y + 8 * k ≤ o) (haz : a.z + 8 * k ≤ o)
    (h4 : a.x % 4 = 0 ∧ a.y % 4 = 0 ∧ a.z % 4 = 0) :
    (∀ d ∈ [(ptAt k o).x, (ptAt k o).y, (ptAt k o).z, a.x, a.y, a.z], d % 4 = 0) ∧
    (∀ d ∈ [(ptAt k o).x, (ptAt k o).y, (ptAt k o).z, a.x, a.y, a.z], d + 8 * k ≤ 8192) ∧
    (((ptAt k o).x + 8 * k ≤ (ptAt k o).y ∨ (ptAt k o).y + 8 * k ≤ (ptAt k o).x) ∧
      ((ptAt k o).x + 8 * k ≤ (ptAt k o).z ∨ (ptAt k o).z + 8 * k ≤ (ptAt k o).x) ∧
      ((ptAt k o).y + 8 * k ≤ (ptAt k o).z ∨ (ptAt k o).z + 8 * k ≤ (ptAt k o).y)) ∧
    (∀ d ∈ [(ptAt k o).x, (ptAt k o).y, (ptAt k o).z], ∀ e ∈ [a.x, a.y, a.z],
      d + 8 * k ≤ e ∨ e + 8 * k ≤ d) := by
  obtain ⟨h1, h2, he, hb3, ha, hq, hp, hoo, -, h8⟩ := lay_nums hk3 hk6
  obtain ⟨a1, a2, a3⟩ := h4
  simp only [ptAt, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  rcases ho with rfl | rfl <;> omega_arith

/-- What a selection of `P` or `O` into three slots below `O` needs. -/
theorem selPt_conds {k : Nat} {a : Pt} (hk3 : 3 ≤ k) (hk6 : k ≤ 6)
    (hax : a.x + 8 * k ≤ oAt k) (hay : a.y + 8 * k ≤ oAt k) (haz : a.z + 8 * k ≤ oAt k)
    (h4 : a.x % 4 = 0 ∧ a.y % 4 = 0 ∧ a.z % 4 = 0) :
    (∀ d ∈ [a.x, a.y, a.z, (ptAt k (pAt k)).x, (ptAt k (pAt k)).y, (ptAt k (pAt k)).z,
      (ptAt k (oAt k)).x, (ptAt k (oAt k)).y, (ptAt k (oAt k)).z], d % 4 = 0) ∧
    (∀ d ∈ [a.x, a.y, a.z, (ptAt k (pAt k)).x, (ptAt k (pAt k)).y, (ptAt k (pAt k)).z,
      (ptAt k (oAt k)).x, (ptAt k (oAt k)).y, (ptAt k (oAt k)).z], d + 8 * k ≤ 8192) ∧
    (∀ d ∈ [a.x, a.y, a.z], ∀ e ∈ [(ptAt k (pAt k)).x, (ptAt k (pAt k)).y, (ptAt k (pAt k)).z,
      (ptAt k (oAt k)).x, (ptAt k (oAt k)).y, (ptAt k (oAt k)).z], d + 8 * k ≤ e ∨ e + 8 * k ≤ d) := by
  obtain ⟨h1, h2, he, hb3, ha, hq, hp, hoo, -, h8⟩ := lay_nums hk3 hk6
  obtain ⟨a1, a2, a3⟩ := h4
  simp only [ptAt, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  omega_arith

/-- What a range written within the point functions' slots keeps. -/
theorem pt_cover {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) {W : List (Nat × Nat)}
    (hW : ∀ w ∈ W, oAt k ≤ w.1 ∧ w.1 + w.2 ≤ 4096) :
    ∀ w ∈ W, ∃ w' ∈ [(oAt k, 4096 - oAt k)], w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 := by
  obtain ⟨-, -, -, -, -, -, -, -, ho, -⟩ := lay_nums hk3 hk6
  intro w hw
  have := hW w hw
  exact ⟨_, List.mem_singleton_self _, this.1, by simp only; omega_arith⟩

/-- `G`, `a` and `3b` to the point functions' `Q`, `a` and `3b`. -/
theorem ladderSetup_ok {L : LadderCfg} {base : Addr} {s : State} (hw : WsReg s base) (hL : LadPtLay L) :
    WP isa (.block (ladderSetup L)) s fun t =>
      Kp [.r4] s t ∧ Unch base [(oAt L.M.n, 4096 - oAt L.M.n)] s.mem t.mem ∧ CpOk L base t.mem s.mem := by
  have hk3 := hL.k3
  have hk6 := hL.k6
  obtain ⟨h1, h2, he, hb3, ha, hq, hp, hoo, ho1, h8⟩ := lay_nums hk3 hk6
  have hn := hw.nowrap
  obtain ⟨al, bl, gxl, gyl, gzl, -, -, -⟩ := hL.al
  obtain sa := hL.a; have sb := hL.b3; have sgx := hL.gx; have sgy := hL.gy; have sgz := hL.gz
  obtain cG := copyPt_conds (a := L.G) hk3 hk6 (.inr rfl) (by omega_arith) (by omega_arith) (by omega_arith) ⟨gxl, gyl, gzl⟩
  rw [ladderSetup, List.append_assoc, WP.block_append_iff]
  refine WP.mono (copyPt_ok hw.ws hw.at3 (n := L.M.n) (o := ptAt L.M.n (qAt L.M.n)) (a := L.G)
    cG.1 cG.2.1 cG.2.2.1 cG.2.2.2) fun s₁ ⟨gx₁, gy₁, gz₁, k₁, O₁⟩ => ?_
  simp only [ptAt] at gx₁ gy₁ gz₁ O₁
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok L.M.n (k₁.ws hw.ws) (k₁.at hw.at3) (o := aAt L.M.n) (a := L.S.a) (by omega_arith) al
    (by omega_arith) (by omega_arith) (by omega_arith)) fun s₂ ⟨a₂, k₂, O₂⟩ => ?_
  refine WP.mono (copy_ok L.M.n (k₂.ws (k₁.ws hw.ws)) (k₂.at (k₁.at hw.at3)) (o := b3At L.M.n) (a := L.S.b3)
    (by omega_arith) bl (by omega_arith) (by omega_arith) (by omega_arith)) fun s₃ ⟨b₃, k₃, O₃⟩ => ?_
  have U₁ : Unch base [(qAt L.M.n, 8 * L.M.n), (qAt L.M.n + elemBytes L.M.n, 8 * L.M.n),
      (qAt L.M.n + 2 * elemBytes L.M.n, 8 * L.M.n)] s.mem s₁.mem := O₁
  have U₂ : Unch base [(aAt L.M.n, 8 * L.M.n)] s₁.mem s₂.mem := O₂.unch
  have U₃ : Unch base [(b3At L.M.n, 8 * L.M.n)] s₂.mem s₃.mem := O₃.unch
  refine ⟨(k₁.trans k₂).trans k₃, ((U₁.trans U₂).trans U₃).cover (pt_cover hk3 hk6 fun w hw => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with ((rfl | rfl | rfl) | rfl) | rfl <;> (simp only; omega_arith)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [(U₂.trans U₃).wordsVal (by ppc_apart) (by omega_arith), gx₁]
  · rw [(U₂.trans U₃).wordsVal (by ppc_apart) (by omega_arith), gy₁]
  · rw [(U₂.trans U₃).wordsVal (by ppc_apart) (by omega_arith), gz₁]
  · rw [U₃.wordsVal (by ppc_apart) (by omega_arith), a₂, U₁.wordsVal (by ppc_apart) (by omega_arith)]
  · rw [b₃, U₂.wordsVal (by ppc_apart) (by omega_arith), U₁.wordsVal (by ppc_apart) (by omega_arith)]

section body
variable {L : LadderCfg} {C : Curve} {base : Addr}

/-- A doubling's result as `Step` has it: for `dbl` the second operand's
slots are the first's. -/
theorem ptVal_dbl {m : Nat} [NeZero m] (a0 : Bool) {E : Nat → Fin m} (h6 : E 6 = E 3) (h7 : E 7 = E 4)
    (h8 : E 8 = E 5) : ptVal a0 true E = ladDbl a0 (E 9) (E 10) (E 3) (E 4) (E 5) := by
  cases a0
  · simp only [ptVal, ladDbl, Bool.false_eq_true, ↓reduceIte, h6, h7, h8]
  · rfl

theorem ptVal_add {m : Nat} [NeZero m] (a0 : Bool) (E : Nat → Fin m) :
    ptVal a0 false E = ladAdd a0 (E 9) (E 10) (E 3) (E 4) (E 5) (E 6) (E 7) (E 8) := by
  cases a0 <;> rfl

theorem Eb_dbl {k m : Nat} [NeZero m] (mem : Mem) (base : Addr) :
    Eb k m true mem base 6 = Eb k m true mem base 3 ∧ Eb k m true mem base 7 = Eb k m true mem base 4 ∧
      Eb k m true mem base 8 = Eb k m true mem base 5 := by
  simp only [Eb, enc_3, enc_4, enc_5, enc_6, enc_7, enc_8, ↓reduceIte, and_self]

/-- An iteration. -/
theorem ladderPBody_ok {k : Nat} {Q : Nat → Fe C → Fe C → Fe C → Prop} {S : Impl.Weierstrass.Mont.Modulus}
    (hkS : S.k = L.M.n) (hmS : S.m = C.p) (hM : ModOk L.M.n C.p) (hodd : C.p % 2 = 1) (hL : LadPtLay L)
    {s₀ : State} (hlt₀ : ∀ x ∈ [L.S.a, L.S.b3, L.G.x, L.G.y, L.G.z], wordsVal s₀.mem base x L.M.n < C.p)
    {a0 : Bool} (hstep : Step L C base s₀ k Q a0)
    (hbits : ∀ t < L.nbits, s₀.mem (off base (L.bits + t)) = if k.testBit t then 1 else 0)
    {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j ≤ L.nbits) (hI : LadInvP L C base Q s₀ s j) :
    WP isa (ladderPBody L S a0) s fun s' => LadInvP L C base Q s₀ s' (j - 1) := by
  obtain ⟨c, w, m', k', d⟩ := S
  dsimp only at hkS hmS
  subst hkS hmS
  have hk3 := hL.k3
  have hk6 := hL.k6
  obtain ⟨h1, h2, he, hb3, ha, hq, hp, hoo, ho1, h8⟩ := lay_nums hk3 hk6
  have hn := hI.ws.nowrap
  have hbl := hL.bits
  have hbe := hL.bitsE
  have hnb := hL.nbits
  obtain ⟨-, -, -, -, -, rxl, ryl, rzl⟩ := hL.al
  obtain rx := hL.rx; have ry := hL.ry; have rz := hL.rz
  obtain cR := copyPt_conds (a := L.R) hk3 hk6 (.inl rfl) (by omega_arith) (by omega_arith) (by omega_arith) ⟨rxl, ryl, rzl⟩
  obtain cO := copyPt_conds (a := ptAt L.M.n (oAt L.M.n)) hk3 hk6 (.inl rfl)
    (by simp only [ptAt]; omega_arith) (by simp only [ptAt]; omega_arith) (by simp only [ptAt]; omega_arith)
    (by simp only [ptAt]; omega_arith)
  -- `r31 -= 1`.
  rw [ladderPBody]
  refine WP.seq (wp_decCounter hj hI.r31 ?_)
  generalize hs₁ : s.write .r31 (BitVec.ofNat 64 (j - 1)) = s₁
  obtain K₁ : Kp [.r31] s s₁ := by rw [← hs₁]; exact Kp.write _ _ (by decide)
  obtain w₁ := hI.ws.of_rk (K₁.rk (rs' := powClob))
  obtain m₁ : s₁.mem = s.mem := by rw [← hs₁]; rfl
  obtain c₁ : s₁.gpr .r31 = BitVec.ofNat 64 (j - 1) := by rw [← hs₁]; simp only [write_gpr, ite_true]
  -- `P = R`.
  refine WP.mono (copyPt_ok w₁.ws w₁.at3 (n := L.M.n) (o := ptAt L.M.n (pAt L.M.n)) (a := L.R)
    cR.1 cR.2.1 cR.2.2.1 cR.2.2.2) fun s₂ ⟨px₂, py₂, pz₂, k₂, O₂⟩ => ?_
  simp only [ptAt] at px₂ py₂ pz₂ O₂
  rw [m₁] at px₂ py₂ pz₂ O₂
  obtain w₂ := w₁.of_rk (k₂.rk (rs' := powClob))
  obtain cp₂ : CpOk L base s₂.mem s₀.mem := hI.cp.keep hk3 hk6 (W := [(pAt L.M.n, 8 * L.M.n),
    (pAt L.M.n + elemBytes L.M.n, 8 * L.M.n), (pAt L.M.n + 2 * elemBytes L.M.n, 8 * L.M.n)]) O₂ (by ppc_apart)
  obtain ⟨gx₂, gy₂, gz₂, ga₂, gb₂⟩ := cp₂
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlt₀
  obtain ⟨la, lb, lgx, lgy, lgz⟩ := hlt₀
  obtain lrx : wordsVal s.mem base L.R.x L.M.n < C.p := hI.lt _ (by simp)
  obtain lry : wordsVal s.mem base L.R.y L.M.n < C.p := hI.lt _ (by simp)
  obtain lrz : wordsVal s.mem base L.R.z L.M.n < C.p := hI.lt _ (by simp)
  -- `O = P + P`.
  refine WP.seq (WP.mono (ptCall_ok (S := ⟨c, w, C.p, L.M.n, d⟩) hM hodd hk3 hk6 true w₂
    (rIds_lt_of true fun x hx => by
      simp only [↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [px₂]; exact lrx
      · rw [py₂]; exact lry
      · rw [pz₂]; exact lrz
      · rw [px₂]; exact lrx
      · rw [py₂]; exact lry
      · rw [pz₂]; exact lrz
      · rw [ga₂]; exact la
      · rw [gb₂]; exact lb)) fun s₃ ⟨k₃, O₃, L₃, E₃⟩ => ?_)
  dsimp only at k₃ O₃ L₃ E₃
  obtain ⟨d6, d7, d8⟩ := Eb_dbl (k := L.M.n) (m := C.p) s₂.mem base
  rw [ptVal_dbl a0 d6 d7 d8] at E₃
  simp only [Eb, enc_0, enc_1, enc_2, enc_3, enc_4, enc_5, enc_9, enc_10] at E₃
  rw [ga₂, gb₂, px₂, py₂, pz₂] at E₃
  obtain l3x := L₃ 0 (by decide)
  obtain l3y := L₃ 1 (by decide)
  obtain l3z := L₃ 2 (by decide)
  rw [enc_0] at l3x
  rw [enc_1] at l3y
  rw [enc_2] at l3z
  obtain w₃ := w₂.of_rk (k₃.mono (rs' := powClob))
  -- `P = O`.
  refine WP.seq (WP.mono (copyPt_ok w₃.ws w₃.at3 (n := L.M.n) (o := ptAt L.M.n (pAt L.M.n))
    (a := ptAt L.M.n (oAt L.M.n)) cO.1 cO.2.1 cO.2.2.1 cO.2.2.2)
    fun s₄ ⟨px₄, py₄, pz₄, k₄, O₄⟩ => ?_)
  simp only [ptAt] at px₄ py₄ pz₄ O₄
  obtain w₄ := w₃.of_rk (k₄.rk (rs' := powClob))
  obtain cp₄ : CpOk L base s₄.mem s₀.mem :=
    (CpOk.keep ⟨gx₂, gy₂, gz₂, ga₂, gb₂⟩ hk3 hk6 O₃ (by ppc_apart)).keep
      hk3 hk6 (W := [(pAt L.M.n, 8 * L.M.n), (pAt L.M.n + elemBytes L.M.n, 8 * L.M.n),
        (pAt L.M.n + 2 * elemBytes L.M.n, 8 * L.M.n)]) O₄ (by ppc_apart)
  obtain ⟨gx₄, gy₄, gz₄, ga₄, gb₄⟩ := cp₄
  -- `O = P + Q`.
  refine WP.seq (WP.mono (ptCall_ok (S := ⟨c, w, C.p, L.M.n, d⟩) hM hodd hk3 hk6 false w₄
    (rIds_lt_of false fun x hx => by
      simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [px₄]; exact l3x
      · rw [py₄]; exact l3y
      · rw [pz₄]; exact l3z
      · rw [gx₄]; exact lgx
      · rw [gy₄]; exact lgy
      · rw [gz₄]; exact lgz
      · rw [ga₄]; exact la
      · rw [gb₄]; exact lb)) fun s₅ ⟨k₅, O₅, L₅, E₅⟩ => ?_)
  dsimp only at k₅ O₅ L₅ E₅
  rw [ptVal_add] at E₅
  simp only [Eb, enc_0, enc_1, enc_2, enc_3, enc_4, enc_5, enc_6, enc_7, enc_8, enc_9, enc_10,
    Bool.false_eq_true, ↓reduceIte] at E₅
  rw [ga₄, gb₄, px₄, py₄, pz₄, gx₄, gy₄, gz₄] at E₅
  obtain l5x := L₅ 0 (by decide)
  obtain l5y := L₅ 1 (by decide)
  obtain l5z := L₅ 2 (by decide)
  rw [enc_0] at l5x
  rw [enc_1] at l5y
  rw [enc_2] at l5z
  have U₅ : Unch base [(oAt L.M.n, 3 * elemBytes L.M.n), (ownAt L.M.n, 4096 - ownAt L.M.n)] s₄.mem s₅.mem := O₅
  -- `P` still holds `D`.
  obtain p5x : wordsVal s₅.mem base (pAt L.M.n) L.M.n = wordsVal s₃.mem base (oAt L.M.n) L.M.n := by
    rw [U₅.wordsVal (by ppc_apart)
      (by omega_arith), px₄]
  obtain p5y : wordsVal s₅.mem base (pAt L.M.n + elemBytes L.M.n) L.M.n =
      wordsVal s₃.mem base (oAt L.M.n + elemBytes L.M.n) L.M.n := by
    rw [U₅.wordsVal (by ppc_apart)
      (by omega_arith), py₄]
  obtain p5z : wordsVal s₅.mem base (pAt L.M.n + 2 * elemBytes L.M.n) L.M.n =
      wordsVal s₃.mem base (oAt L.M.n + 2 * elemBytes L.M.n) L.M.n := by
    rw [U₅.wordsVal (by ppc_apart)
      (by omega_arith), pz₄]
  obtain cp₅ : CpOk L base s₅.mem s₀.mem := CpOk.keep ⟨gx₄, gy₄, gz₄, ga₄, gb₄⟩ hk3 hk6 U₅ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; omega_arith)
  -- What changed: the point functions' slots.
  obtain U₁₅ : Unch base [(oAt L.M.n, 4096 - oAt L.M.n)] s.mem s₅.mem :=
    ((((show Unch base _ s.mem s₂.mem from O₂).trans (show Unch base _ s₂.mem s₃.mem from O₃)).trans
      (show Unch base _ s₃.mem s₄.mem from O₄)).trans U₅).cover (pt_cover hk3 hk6 fun w hw => by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with (((rfl | rfl | rfl) | rfl | rfl) | rfl | rfl | rfl) | rfl | rfl <;> (simp only; omega_arith))
  obtain hU₅ : Unch base (ladWpt L) s₀.mem s₅.mem :=
    (hI.unch.trans U₁₅).mono fun w hw => by
      simp only [ladWpt, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
      rcases hw with (h | h | h | h) | h <;> simp [h]
  obtain hbyte : s₅.mem (off base (L.bits + (j - 1))) = if k.testBit (j - 1) then 1 else 0 := by
    rw [hU₅.byte (fun w hw => by
      simp only [ladWpt, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl <;> (simp only; omega_arith)) (by omega_arith), hbits _ (by omega_arith)]
  obtain K₅ : Rk powClob s s₅ :=
    (K₁.rk (rs' := powClob)).trans <| (k₂.rk (rs' := powClob)).trans <| (k₃.mono (rs' := powClob)).trans <|
      (k₄.rk (rs' := powClob)).trans (k₅.mono (rs' := powClob))
  obtain c₅ : s₅.gpr .r31 = BitVec.ofNat 64 (j - 1) := by
    rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), c₁]
  obtain w₅ := w₄.of_rk (k₅.mono (rs' := powClob))
  -- `R = O` or `P`.
  refine wp_append (WP.mono (bitMask_bool_ok w₅.ws w₅.at3 c₅ (by omega_arith) hbyte) fun s₆ ⟨g₆, k₆, m₆⟩ => ?_)
  obtain sR := selPt_conds (a := L.R) hk3 hk6 rx ry rz ⟨rxl, ryl, rzl⟩
  refine WP.mono (selPt_ok (k₆.ws w₅.ws) (k₆.at w₅.at3) _ g₆ (n := L.M.n) (o := L.R)
    (a := ptAt L.M.n (pAt L.M.n)) (b := ptAt L.M.n (oAt L.M.n)) sR.1 sR.2.1 hL.rne sR.2.2)
    fun s₇ ⟨ex, ey, ez, k₇, O₇⟩ => ?_
  simp only [ptAt] at ex ey ez
  rw [m₆] at ex ey ez
  obtain U₅₇ : Unch base [(L.R.x, 8 * L.M.n), (L.R.y, 8 * L.M.n), (L.R.z, 8 * L.M.n)] s₅.mem s₇.mem := by
    rw [← m₆]; exact O₇
  obtain K₇ : Rk powClob s₅ s₇ := (k₆.rk (rs' := powClob)).trans (k₇.rk (rs' := powClob))
  refine ⟨w₅.of_rk K₇, by rw [k₇.g, k₆.g, c₅], (hI.keep.trans K₅).trans K₇, ?_, ?_, ?_, ?_⟩
  · exact (hU₅.trans U₅₇).mono fun w hw => by
      simp only [ladWpt, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
      rcases hw with (h | h | h | h) | (h | h | h) <;> simp [h]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [ex]; split
      · exact l5x
      · rw [p5x]; exact l3x
    · rw [ey]; split
      · exact l5y
      · rw [p5y]; exact l3y
    · rw [ez]; split
      · exact l5z
      · rw [p5z]; exact l3z
  · have hq := hstep (j - 1) (by omega_arith) _ _ _ _ _ _ _ _ _ (by rw [Nat.sub_add_cancel hj]; exact hI.q)
      E₃.symm E₅.symm
    obtain hx : tmv C L.M.n base s₇ L.R.x = if k.testBit (j - 1) then
        toM C.p (2 ^ (64 * L.M.n)) (wordsVal s₅.mem base (oAt L.M.n) L.M.n) else
        toM C.p (2 ^ (64 * L.M.n)) (wordsVal s₃.mem base (oAt L.M.n) L.M.n) := by
      show toM _ _ _ = _
      rw [ex]; split
      · rfl
      · rw [p5x]
    obtain hy : tmv C L.M.n base s₇ L.R.y = if k.testBit (j - 1) then
        toM C.p (2 ^ (64 * L.M.n)) (wordsVal s₅.mem base (oAt L.M.n + elemBytes L.M.n) L.M.n) else
        toM C.p (2 ^ (64 * L.M.n)) (wordsVal s₃.mem base (oAt L.M.n + elemBytes L.M.n) L.M.n) := by
      show toM _ _ _ = _
      rw [ey]; split
      · rfl
      · rw [p5y]
    obtain hz : tmv C L.M.n base s₇ L.R.z = if k.testBit (j - 1) then
        toM C.p (2 ^ (64 * L.M.n)) (wordsVal s₅.mem base (oAt L.M.n + 2 * elemBytes L.M.n) L.M.n) else
        toM C.p (2 ^ (64 * L.M.n)) (wordsVal s₃.mem base (oAt L.M.n + 2 * elemBytes L.M.n) L.M.n) := by
      show toM _ _ _ = _
      rw [ez]; split
      · rfl
      · rw [p5z]
    rw [hx, hy, hz]
    exact hq
  · exact cp₅.keep hk3 hk6 U₅₇ (by ppc_apart)

/-- `Q 0` accepts what `R` holds at the end, if `Q L.nbits` accepts what it
holds at the start and an iteration keeps `Q` (`Step`), for the scalar `k`
whose bits are the table at `L.bits`, by calls of the point functions; only
`powClob` and `ladWpt` change. -/
theorem ladderPt_ok {k : Nat} {Q : Nat → Fe C → Fe C → Fe C → Prop} {S : Impl.Weierstrass.Mont.Modulus}
    (hkS : S.k = L.M.n) (hmS : S.m = C.p) (hM : ModOk L.M.n C.p) (hodd : C.p % 2 = 1) (hL : LadPtLay L)
    {s : State} (hs : WsReg s base)
    (hlt : ∀ x ∈ [L.S.a, L.S.b3, L.G.x, L.G.y, L.G.z, L.R.x, L.R.y, L.R.z],
      wordsVal s.mem base x L.M.n < C.p)
    {a0 : Bool} (hstep : Step L C base s k Q a0)
    (hR : Q L.nbits (tmv C L.M.n base s L.R.x) (tmv C L.M.n base s L.R.y) (tmv C L.M.n base s L.R.z))
    (hbits : ∀ t < L.nbits, s.mem (off base (L.bits + t)) = if k.testBit t then 1 else 0) :
    WP isa (ladderP L S a0) s fun s' => Rk powClob s s' ∧ Unch base (ladWpt L) s.mem s'.mem ∧
      (∀ x ∈ [L.R.x, L.R.y, L.R.z], wordsVal s'.mem base x L.M.n < C.p) ∧
      Q 0 (tmv C L.M.n base s' L.R.x) (tmv C L.M.n base s' L.R.y) (tmv C L.M.n base s' L.R.z) := by
  have hk3 := hL.k3
  have hk6 := hL.k6
  obtain ⟨h1, h2, he, hb3, ha, hq, hp, hoo, ho1, h8⟩ := lay_nums hk3 hk6
  have hn := hs.nowrap
  have hnb := hL.nbits
  obtain rx := hL.rx; have ry := hL.ry; have rz := hL.rz
  unfold ladderP
  simp only [hk6, ↓reduceIte]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (ladderSetup_ok hs hL) fun s₃ ⟨k₃, U₃, cp₃⟩ =>
    wp_step (exec_li hnb.2) (WP.block_nil ?_)
  obtain K₄ : Kp powClob s (s₃.write .r31 (BitVec.ofNat 64 L.nbits)) :=
    (k₃.mono (by decide)).trans (Kp.write _ _ (by decide))
  obtain low : ∀ {x}, x + 8 * L.M.n ≤ oAt L.M.n →
      wordsVal (s₃.write .r31 (BitVec.ofNat 64 L.nbits)).mem base x L.M.n = wordsVal s.mem base x L.M.n :=
    fun hx => by rw [write_mem]; exact U₃.wordsVal (by ppc_apart) (by omega_arith)
  refine countLoop_ok (Inv := fun j s' => LadInvP L C base Q s s' j) (n := L.nbits)
    (fun j s' hi => hi.r31)
    (fun j s' h1 h2 hi => ladderPBody_ok hkS hmS hM hodd hL (fun x hx => hlt x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with h | h | h | h | h <;> simp [h])) hstep hbits h1 h2 hi)
    (fun s' hi => ⟨hi.keep, hi.unch, hi.lt, hi.q⟩) hnb.1 (by omega_arith)
    ⟨hs.of_rk (K₄.rk (rs' := powClob)), by simp only [write_gpr, ite_true], K₄.rk,
      U₃.mono fun w hw => by simp at hw; simp [hw, ladWpt], fun x hx => ?_, ?_, cp₃⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [low rx]; exact hlt _ (by simp)
    · rw [low ry]; exact hlt _ (by simp)
    · rw [low rz]; exact hlt _ (by simp)
  · show Q L.nbits (toM _ _ _) (toM _ _ _) (toM _ _ _)
    rw [low rx, low ry, low rz]
    exact hR

/-- `Q 0` accepts what `R` holds at the end, if `Q L.nbits` accepts what it
holds at the start and an iteration keeps `Q` (`Step`), for the scalar `k`
whose bits are the table at `L.bits`: by calls of the point functions for
coordinates of at most 6 words (`ladderPt_ok`, whose slots `LadPtLay` gives),
else by the complete addition inlined (`ladder_ok`, `LadLayI`); only
`powClob` and `ladWp` change. -/
theorem ladderP_ok {k : Nat} {Q : Nat → Fe C → Fe C → Fe C → Prop} {S : Impl.Weierstrass.Mont.Modulus}
    (hkS : S.k = L.M.n) (hmS : S.m = C.p) (hM : ModOk L.M.n C.p) (hodd : C.p % 2 = 1)
    (hp : UnitMod C.p (2 ^ (64 * L.M.n))) (hP : L.M.n ≤ 6 → LadPtLay L) (hX : 6 < L.M.n → LadLayI L)
    {s : State} (hs : WsReg s base)
    (hlt : ∀ x ∈ [L.S.a, L.S.b3, L.G.x, L.G.y, L.G.z, L.R.x, L.R.y, L.R.z],
      wordsVal s.mem base x L.M.n < C.p)
    {a0 : Bool} (ha0 : a0 = true → L.M.n ≤ 6) (hstep : Step L C base s k Q a0)
    (hR : Q L.nbits (tmv C L.M.n base s L.R.x) (tmv C L.M.n base s L.R.y) (tmv C L.M.n base s L.R.z))
    (hbits : ∀ t < L.nbits, s.mem (off base (L.bits + t)) = if k.testBit t then 1 else 0) :
    WP isa (ladderP L S a0) s fun s' => Rk powClob s s' ∧ Unch base (ladWp L) s.mem s'.mem ∧
      (∀ x ∈ [L.R.x, L.R.y, L.R.z], wordsVal s'.mem base x L.M.n < C.p) ∧
      Q 0 (tmv C L.M.n base s' L.R.x) (tmv C L.M.n base s' L.R.y) (tmv C L.M.n base s' L.R.z) := by
  by_cases hk6 : L.M.n ≤ 6
  · refine WP.mono (ladderPt_ok hkS hmS hM hodd (hP hk6) hs hlt hstep hR hbits)
      fun s' ⟨K, U, l, q⟩ => ⟨K, U.mono fun w hw => ?_, l, q⟩
    simp only [ladWpt, List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [ladWp, ptW, hk6, ↓reduceIte, List.mem_append, List.mem_singleton]
    rcases hw with rfl | rfl | rfl | rfl
    · exact .inl (List.mem_append_left _ (mem_ladW_R _ (by simp)))
    · exact .inl (List.mem_append_left _ (mem_ladW_R _ (by simp)))
    · exact .inl (List.mem_append_left _ (mem_ladW_R _ (by simp)))
    · exact .inr rfl
  · unfold ladderP
    simp only [hk6, ↓reduceIte]
    obtain hM' : ModOk S.k S.m := by rw [hkS, hmS]; exact hM
    cases a0
    swap; · exact absurd (ha0 rfl) hk6
    exact WP.mono (ladder_ok hM' hkS hmS hp (hX (by omega_arith)) hs hlt hstep hR hbits)
      fun s' ⟨K, U, l, q⟩ => ⟨K, U.mono fun w hw => List.mem_append_left _ hw, l, q⟩

end body

end VG.Proof.Weierstrass.PPC64LE.Point

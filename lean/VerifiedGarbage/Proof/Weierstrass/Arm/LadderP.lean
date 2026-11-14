module

public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Impl.Weierstrass.Arm.Point
public import VerifiedGarbage.Proof.Weierstrass.Arm.MontFn
import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Weierstrass.Point0Contract
public import VerifiedGarbage.Proof.Weierstrass.Env
import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
import VerifiedGarbage.Proof.Weierstrass.Arm.Fprog
import VerifiedGarbage.Proof.Weierstrass.Arm.Copy
import VerifiedGarbage.Proof.Framework.Arm.RelCT
public import VerifiedGarbage.Impl.Weierstrass.Arm.LadderP
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Weierstrass.Arm.Ladder
import VerifiedGarbage.Proof.Weierstrass.Arm.Bits
import VerifiedGarbage.Proof.Weierstrass.Arm.Loop
import VerifiedGarbage.Spec.X25519

/-! ### `Weierstrass.Arm.LadderPCall`, which only this module used -/

section

/-! ### `Weierstrass.Arm.PointFn`, which only this module used -/

section

/-! ### `Weierstrass.Arm.PointFprog`, which only this module used -/

section

/-! ### `Weierstrass.Arm.PointCall`, which only this module used -/

section

/-!
# Calls of the Montgomery functions with operands in registers, on 32-bit ARM

`callR enc f body o a b` (`Impl/Weierstrass/Arm/Point.lean`) calls the
function `f`, whose code is `body`, on the working space at `r12` and the
offsets that `enc` gives the slots `o`, `a` and `b`. As `callOp_ok`
(`MontCall.lean`), but `lr` is not kept in `r10`: the point functions save
it in memory, and write no register but `r0`–`r3`, `r12` and `lr`.
`mulCallR_ok`, `addCallR_ok` and `subCallR_ok` are the calls of `mulFn`,
`addFn` and `subFn`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.Arm.Point

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass.Arm.Mont
open VG.Impl.Weierstrass.Arm.Point
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass.Arm.Mont
open VG.Proof.X25519.Arm (Rest Upd wp_mov wp_movw op2_reg)

/-- A 16-bit immediate, as `movw` loads it. -/
theorem movw_toNat {c : Nat} (h : c < 2 ^ 16) : ((BitVec.ofNat 16 c).setWidth 32).toNat = c := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_using [h]

/-- What a call writing `[o]` keeps: the registers but `r0`–`r3`, `r12` and
`lr`, the regions, the stack pointer, `r12` as the working space, and the
memory but `[o]` and the functions' own working space. -/
structure CallKeepR (n : Nat) (base : Addr) (o : Nat) (s s' : State) : Prop where
  rest : Rest [.r0, .r1, .r2, .r3, .r12, .lr] s s'
  r12 : s'.gpr .r12 = s.gpr .r12
  mem : Outs base [(o, 8 * n), (own n, 64 * n)] s.mem s'.mem

/-- A call of `body` on the offsets `enc` gives, which from the working space
at `r12` changes only `[enc o]` and its own working space, preserves the
callee-saved registers, leaves `r12` as the working space, and relates the
memory before and after by `V`. -/
theorem callR_ok {enc : Nat → Nat} {f : String} {body : Prog isa} (hn : body.noCalls = true) {n : Nat}
    {s : State} {base : Addr} (hf : Far s base 8192) {o a b : Nat}
    (ho : enc o < 2 ^ 16) (ha : enc a < 2 ^ 16) (hb : enc b < 2 ^ 16) {V : Mem → Mem → Prop}
    (hbody : ∀ t, t.rd = [] → t.wr = [⟨base, 8192⟩] → t.gpr .r0 = s.gpr .r12 →
      (t.gpr .r1).toNat = enc o → (t.gpr .r2).toNat = enc a → (t.gpr .r3).toNat = enc b → t.mem = s.mem →
      WP isa body t fun t' => abiPreserved t t' ∧ Kept n base (enc o) t.mem t'.mem ∧ V t.mem t'.mem ∧
        t'.gpr .r12 = t.gpr .r0) :
    WP isa (callR enc f body o a b) s fun s' => CallKeepR n base (enc o) s s' ∧ V s.mem s'.mem := by
  rw [callR]
  refine WP.seq (wp_mov (op2_reg _ _) fun s₁ u₁ => wp_movw fun s₂ u₂ => wp_movw fun s₃ u₃ =>
    wp_movw fun s₄ u₄ => WP.block_nil ?_)
  have k₄ : Rest [.r0, .r1, .r2, .r3] s s₄ :=
    (u₁.rest (by simp)).trans <| (u₂.rest (by simp)).trans <| (u₃.rest (by simp)).trans (u₄.rest (by simp))
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have g0 : s₄.gpr .r0 = s.gpr .r12 := by
    rw [u₄.other .r0 (by decide), u₃.other .r0 (by decide), u₂.other .r0 (by decide), u₁.gpr]
  have g1 : (s₄.gpr .r1).toNat = enc o := by
    rw [u₄.other .r1 (by decide), u₃.other .r1 (by decide), u₂.gpr, movw_toNat ho]
  have g2 : (s₄.gpr .r2).toNat = enc a := by rw [u₄.other .r2 (by decide), u₃.gpr, movw_toNat ha]
  have g3 : (s₄.gpr .r3).toNat = enc b := by rw [u₄.gpr, movw_toNat hb]
  have hf₄ : Far s₄ base 8192 := hf.of_rest k₄
  have hcov : Covers [⟨base, 8192⟩] s₄.wr := by
    have h := hf₄.write (d := 0) (n := 8192) (by omega_using [])
    simp only [off, BitVec.add_zero] at h
    exact Covers.one h
  refine WP.call (k := ⟨fun t => t.rd = [] ∧ t.wr = [⟨base, 8192⟩] ∧ t.gpr .r0 = s.gpr .r12 ∧
      (t.gpr .r1).toNat = enc o ∧ (t.gpr .r2).toNat = enc a ∧ (t.gpr .r3).toNat = enc b ∧ t.mem = s.mem,
      fun t t' => Kept n base (enc o) t.mem t'.mem ∧ V t.mem t'.mem ∧ t'.gpr .r12 = t.gpr .r0, fun _ _ => True⟩)
    (fun t ⟨h1, h2, h3, h4, h5, h6, h7⟩ => by
      obtain ⟨tr, t', he, A, K, W, R⟩ := hbody t h1 h2 h3 h4 h5 h6 h7
      exact ⟨tr, t', he, A, K, W, R⟩)
    (rd := []) (wr := [⟨base, 8192⟩])
    ⟨rfl, rfl, by rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), g0],
      by rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), g1],
      by rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), g2],
      by rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), g3],
      by rw [State.withRegions_mem, State.callEntry_mem, m₄]⟩
    (Covers.right hcov) hcov ?_ hn
  intro s₇ r₇ w₇ p₇ _ hp₇ _ ⟨K, W, R⟩
  simp only [State.withRegions_mem, State.callEntry_mem, m₄, State.withRegions_gpr] at K W R
  rw [State.callEntry_gpr _ (by decide), g0] at R
  refine ⟨⟨⟨fun r hr => ?_, by rw [r₇, k₄.rd], by rw [w₇, k₄.wr], by rw [p₇, k₄.sp]⟩, R, K⟩, W⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h0, h1, h2, h3, h12, hlr⟩ := hr
  have hpres : r ∈ preserved := by revert h0 h1 h2 h3 h12 hlr; cases r <;> decide
  rw [hp₇ r hpres hlr, k₄.gpr r (by simp [h0, h1, h2, h3])]

/-- The arguments of a call, as the functions' precondition has them. -/
theorem pre_of_callR {n m : Nat} {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hf : Far s base 8192) {o a b : Nat} (ho : o + 8 * n ≤ own n) (ha : a + 8 * n ≤ own n)
    (hb : b + 8 * n ≤ own n) {t : State} (h1 : t.rd = []) (h2 : t.wr = [⟨base, 8192⟩])
    (h3 : t.gpr .r0 = s.gpr .r12) (h4 : (t.gpr .r1).toNat = o) (h5 : (t.gpr .r2).toNat = a)
    (h6 : (t.gpr .r3).toNat = b) : Pre n m t ∧ State.addr (t.gpr .r0) = base := by
  have hr0 : State.addr (t.gpr .r0) = base := by rw [h3]; exact hs.wb
  refine ⟨⟨h1, by rw [h2, hr0], ?_, by rw [h4]; exact ho, by rw [h5]; exact ha, by rw [h6]; exact hb⟩, hr0⟩
  rw [h3, hs.wb_toNat]; exact hf.nowrap

section
variable {enc : Nat → Nat} {S : Impl.Weierstrass.Mont.Modulus} (hM : ModOk S.k S.m) {s : State} {base : Addr}
  {size : Nat} (hs : Scr s base size) (hf : Far s base 8192) {o a b : Nat}
  (lo : enc o + 8 * S.k ≤ own S.k) (la : enc a + 8 * S.k ≤ own S.k) (lb : enc b + 8 * S.k ≤ own S.k)
include hM hs hf lo la lb

/-- `[o] = [a] [b] R⁻¹ mod m` by a call of `vg_<curve>_mul_mod_<p|n>`. -/
theorem mulCallR_ok (hB : wordsVal s.mem base (enc b) S.k < S.m) {u : Bool} :
    WP isa (callR enc (mulName u S) (mulFnWith u S.k S.m) o a b) s fun s' => CallKeepR S.k base (enc o) s s' ∧
      wordsVal s'.mem base (enc o) S.k < S.m ∧
      wordsVal s'.mem base (enc o) S.k * 2 ^ (64 * S.k) % S.m =
        wordsVal s.mem base (enc a) S.k * wordsVal s.mem base (enc b) S.k % S.m :=
  callR_ok (V := fun m m' => wordsVal m' base (enc o) S.k < S.m ∧
      wordsVal m' base (enc o) S.k * 2 ^ (64 * S.k) % S.m = wordsVal m base (enc a) S.k * wordsVal m base (enc b) S.k % S.m)
    (by unfold mulFnWith mulFnU mulFn; cases u <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> (try split) <;> rfl)
    hf (by have := own_le S.k hM.n9; omega_using [lo, this]) (by have := own_le S.k hM.n9; omega_using [la, this])
    (by have := own_le S.k hM.n9; omega_using [lb, this]) fun t h1 h2 h3 h4 h5 h6 h7 => by
      obtain ⟨hp, e0⟩ := pre_of_callR hs hf lo la lb h1 h2 h3 h4 h5 h6 (m := S.m)
      refine WP.mono (mulFnWith_ok u hM hp (by rw [e0, h6, h7]; exact hB)) fun t' ⟨A, K, ⟨V, C⟩, R⟩ => ?_
      rw [e0, h4, h5, h6] at *
      exact ⟨A, K, ⟨V, C⟩, R⟩

/-- `[o] = [a] + [b] mod m` by a call of `vg_<curve>_add_mod_<p|n>`. -/
theorem addCallR_ok (hAB : wordsVal s.mem base (enc a) S.k + wordsVal s.mem base (enc b) S.k < 2 * S.m) :
    WP isa (callR enc (S.fn "add") (addFn S.k S.m) o a b) s fun s' => CallKeepR S.k base (enc o) s s' ∧
      wordsVal s'.mem base (enc o) S.k = (wordsVal s.mem base (enc a) S.k + wordsVal s.mem base (enc b) S.k) % S.m :=
  callR_ok (V := fun m m' => wordsVal m' base (enc o) S.k = (wordsVal m base (enc a) S.k + wordsVal m base (enc b) S.k) % S.m)
    rfl hf (by have := own_le S.k hM.n9; omega_using [lo, this]) (by have := own_le S.k hM.n9; omega_using [la, this])
    (by have := own_le S.k hM.n9; omega_using [lb, this]) fun t h1 h2 h3 h4 h5 h6 h7 => by
      obtain ⟨hp, e0⟩ := pre_of_callR hs hf lo la lb h1 h2 h3 h4 h5 h6 (m := S.m)
      refine WP.mono (addFn_ok hM hp (by rw [e0, h5, h6, h7]; exact hAB)) fun t' ⟨A, K, V, R⟩ => ?_
      rw [e0, h4, h5, h6] at *
      exact ⟨A, K, V, R⟩

/-- `[o] = [a] - [b] mod m` by a call of `vg_<curve>_sub_mod_<p|n>`. -/
theorem subCallR_ok (hA : wordsVal s.mem base (enc a) S.k < S.m) (hB : wordsVal s.mem base (enc b) S.k < S.m) :
    WP isa (callR enc (S.fn "sub") (subFn S.k S.m) o a b) s fun s' => CallKeepR S.k base (enc o) s s' ∧
      wordsVal s'.mem base (enc o) S.k = (wordsVal s.mem base (enc a) S.k + S.m - wordsVal s.mem base (enc b) S.k) % S.m :=
  callR_ok (V := fun m m' => wordsVal m' base (enc o) S.k = (wordsVal m base (enc a) S.k + S.m - wordsVal m base (enc b) S.k) % S.m)
    rfl hf (by have := own_le S.k hM.n9; omega_using [lo, this]) (by have := own_le S.k hM.n9; omega_using [la, this])
    (by have := own_le S.k hM.n9; omega_using [lb, this]) fun t h1 h2 h3 h4 h5 h6 h7 => by
      obtain ⟨hp, e0⟩ := pre_of_callR hs hf lo la lb h1 h2 h3 h4 h5 h6 (m := S.m)
      refine WP.mono (subFn_ok hM hp (by rw [e0, h5, h7]; exact hA) (by rw [e0, h6, h7]; exact hB))
        fun t' ⟨A, K, V, R⟩ => ?_
      rw [e0, h4, h5, h6] at *
      exact ⟨A, K, V, R⟩

end

end VG.Proof.Weierstrass.Arm.Point

end

end


/-!
# Field programs on slots at offsets known at run time, on 32-bit ARM

`fprogR σ S ops` (`Impl/Weierstrass/Arm/Point.lean`) runs the field
operations `ops`, on slots named by number, each slot `x` at the offset
`σ x`, by calls of the functions of the modulus `S`. As `fprog_ok`
(`Fprog.lean`), what the slots stand for (`toM`) follows `runOps ops`
(`fprogR_ok`), but the offsets may coincide: only the slots the program
writes (`W`) must be apart from every other (`LayR`), so that two slots it
only reads may be one (a point doubled). `opsR_ok` runs a formula on the
function's slots (`OpsOk`), such as the complete addition (`rcbIds_opsOk`).
-/

@[expose] public section

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
    refine Outs.wordsVal hk.mem (fun r hr => ?_) (by have := hI.far.nowrap; omega_using [hown, h1])
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
theorem fopR_ok {k N : Nat} {σ : Nat → Nat} {base : Addr} {S : Impl.Weierstrass.Mont.Modulus}
    [NeZero S.m] (hM : ModOk S.k S.m) (hk : S.k = k) {W : List Nat} (hL : LayR k N W σ)
    (hm : UnitMod S.m (2 ^ (64 * k))) {V : List Nat} {E : Nat → Fin S.m} {s : State}
    (hI : InvR k N σ base S.m V E s) {op : FOp} (hW : op.out ∈ W) (hN : ∀ x ∈ op.out :: op.ins, x < N)
    (hR : ∀ x ∈ op.ins, x ∈ V) {u : Bool} :
    WP isa (opCodeR σ S u op) s fun s' =>
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
        (by omega_using [hA, hB]))
      fun s' ⟨K, heq⟩ => ?_
    refine ⟨.of_call K, hI.update hL hW hN.1 (.of_call K) ?_ ?_⟩
    · rw [heq]; exact Nat.mod_lt _ (by omega_using [hA])
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
    · rw [heq]; exact Nat.mod_lt _ (by omega_using [hA])
    · rw [heq, toM_sub (by omega_using [hB]), hI.val a hR.1, hI.val b hR.2]

/-- A field program. -/
theorem fprogR_ok {k N : Nat} {σ : Nat → Nat} {base : Addr} {S : Impl.Weierstrass.Mont.Modulus}
    [NeZero S.m] (hM : ModOk S.k S.m) (hk : S.k = k) {W : List Nat} (hL : LayR k N W σ)
    (hm : UnitMod S.m (2 ^ (64 * k))) {u : Bool} :
    ∀ (ops : List FOp) {V : List Nat} {E : Nat → Fin S.m} {s : State},
      InvR k N σ base S.m V E s → (∀ op ∈ ops, op.out ∈ W ∧ ∀ x ∈ op.out :: op.ins, x < N) →
      readsOk ops V = true →
      WP isa (fprogR σ S ops u) s fun s' => KeepR k σ base (ops.map FOp.out) s s' ∧
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
    {E : Nat → Fin S.m} {s : State} (hI : InvR k 17 σ base S.m rIds E s) {u : Bool} :
    WP isa (fprogR σ S ops u) s fun s' => KeepR k σ base wIds s s' ∧
      InvR k 17 σ base S.m (validAfter ops rIds) (runOps ops E) s' := by
  refine WP.mono (fprogR_ok hM hk hL hm _ hI hO.slots hO.reads) fun s' ⟨hk', hI'⟩ =>
    ⟨hk'.mono fun w hw => ?_, hI'⟩
  obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw
  exact (hO.slots op hop).1

theorem rcbIds_ok : ∀ op ∈ rcb sId pId qId oId, op.out ∈ wIds ∧ ∀ x ∈ op.out :: op.ins, x < 17 := by
  decide

theorem rcbIds_reads : readsOk (rcb sId pId qId oId) rIds = true := by decide

theorem rcbIds_apart : RcbApart sId pId qId oId := ⟨by decide, by decide⟩

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

end VG.Proof.Weierstrass.Arm.Point

end

end


/-!
# Complete point addition and doubling as functions, on 32-bit ARM: correctness

`fnOps S dbl ops` (`Impl/Weierstrass/Arm/Point.lean`), for field operations
`ops` that write only the result and the temporaries (`OpsOk`), from a state
that its precondition describes (`PrePt`: the working space at `r0`, writable, and
every coordinate it reads below the prime), returns with the callee-saved
registers and `sp` kept, `r12 = ws`, the memory changed only at `O` and in
the own working space, and `O`'s coordinates below the prime, standing for
what `ops` computes from what the constants and the operands stand for
(`fnOps_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.Arm.Point

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass.Arm.Mont
open VG.Impl.Weierstrass VG.Impl.Weierstrass.Arm.Point
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
  VG.Proof.Weierstrass.Arm.Mont
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov op2_reg wp_str wp_ldr)

/-- The numbers of the layout, for `omega_arith`. -/
theorem lay_nums {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) :
    Impl.Weierstrass.Point.ownAt k + 64 + 6 * Impl.Weierstrass.Point.elemBytes k = own k ∧ own k + 64 * k = 4096 ∧ Impl.Weierstrass.Point.elemBytes k = 8 * k ∧
    Impl.Weierstrass.Point.b3At k + Impl.Weierstrass.Point.elemBytes k = Impl.Weierstrass.Point.ownAt k ∧ Impl.Weierstrass.Point.aAt k + Impl.Weierstrass.Point.elemBytes k = Impl.Weierstrass.Point.b3At k ∧
    Impl.Weierstrass.Point.qAt k + 3 * Impl.Weierstrass.Point.elemBytes k = Impl.Weierstrass.Point.aAt k ∧ Impl.Weierstrass.Point.pAt k + 3 * Impl.Weierstrass.Point.elemBytes k = Impl.Weierstrass.Point.qAt k ∧
    Impl.Weierstrass.Point.oAt k + 3 * Impl.Weierstrass.Point.elemBytes k = Impl.Weierstrass.Point.pAt k ∧ 1000 ≤ Impl.Weierstrass.Point.oAt k := by
  obtain rfl | rfl | rfl | rfl : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega_using [hk3, hk6]
  all_goals decide +kernel

/-- The slots the function reads first lie below its own working space. -/
theorem enc_rIds {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) (dbl : Bool) :
    ∀ x ∈ rIds, enc k dbl x + 8 * k ≤ Impl.Weierstrass.Point.ownAt k := by
  obtain rfl | rfl | rfl | rfl : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega_using [hk3, hk6]
  all_goals cases dbl <;> decide +kernel

/-- The slots `enc` gives are laid out as the program needs, and those it
writes lie apart from the saved `lr` and within `O` or the own working
space. -/
theorem enc_lay {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) (dbl : Bool) : LayR k 17 wIds (enc k dbl) := by
  obtain rfl | rfl | rfl | rfl : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega_using [hk3, hk6]
  all_goals cases dbl <;> exact ⟨by decide +kernel, by decide +kernel⟩

theorem enc_wIds {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) (dbl : Bool) :
    ∀ w ∈ wIds, (enc k dbl w + 8 * k ≤ Impl.Weierstrass.Point.ownAt k ∨ Impl.Weierstrass.Point.ownAt k + 4 ≤ enc k dbl w) ∧
      ((Impl.Weierstrass.Point.oAt k ≤ enc k dbl w ∧ enc k dbl w + 8 * k ≤ Impl.Weierstrass.Point.pAt k) ∨
        (Impl.Weierstrass.Point.ownAt k ≤ enc k dbl w ∧ enc k dbl w + 8 * k ≤ 4096)) := by
  obtain rfl | rfl | rfl | rfl : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega_using [hk3, hk6]
  all_goals cases dbl <;> decide +kernel

/-- The precondition of the function, on the state: the working space at
`r0`, its `8192` bytes writable, and the numbers it reads below `m`. -/
structure PrePt (k m : Nat) (dbl : Bool) (s : State) : Prop where
  rd : s.rd = []
  wr : s.wr = [⟨State.addr (s.gpr .r0), 8192⟩]
  fit : (s.gpr .r0).toNat + 8192 ≤ 2 ^ 32
  k3 : 3 ≤ k
  k6 : k ≤ 6
  lt : ∀ x ∈ rIds, wordsVal s.mem (State.addr (s.gpr .r0)) (enc k dbl x) k < m

/-- What the entry leaves: `r12 = ws`, the other registers, `lr` saved, and
the memory but those 4 bytes. -/
structure EnteredPt (k : Nat) (s s₁ : State) : Prop where
  scr : Scr s₁ (State.addr (s.gpr .r0)) 4096
  far : Far s₁ (State.addr (s.gpr .r0)) 8192
  r12 : s₁.gpr .r12 = s.gpr .r0
  keep : ∀ r, r ≠ .r12 → s₁.gpr r = s.gpr r
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr
  sp : s₁.sp = s.sp
  mem : Outs (State.addr (s.gpr .r0)) [(Impl.Weierstrass.Point.ownAt k, 4)] s.mem s₁.mem
  saved : s₁.mem.readW (off (State.addr (s.gpr .r0)) (Impl.Weierstrass.Point.ownAt k)) 32 = s.gpr .lr

theorem entry_ok {k m : Nat} {dbl : Bool} {s : State} (hp : PrePt k m dbl s) :
    WP isa (.block (Impl.Weierstrass.Arm.Point.entry k)) s (EnteredPt k s) := by
  have hl := lay_nums hp.k3 hp.k6
  have hfit := hp.fit
  have hown : own k ≤ 4096 := Nat.sub_le _ _
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => ?_
  have hs₁ : Scr s₁ (State.addr (s.gpr .r0)) 4096 := ⟨by rw [u₁.gpr], ⟨8192, by decide, by decide,
    by rw [u₁.wr, hp.wr]; simp⟩, by rw [VG.Proof.X25519.Arm.addr_toNat]; omega_arith, by decide⟩
  refine VG.Proof.X25519.Arm.WP.append (strs_ok hs₁ [(.lr, Impl.Weierstrass.Point.ownAt k)] (by simp; omega_arith) (by simp))
    fun s₂ ⟨K₂, O₂, V₂⟩ => WP.block_nil ?_
  refine ⟨hs₁.of_rest K₂ (by simp), ⟨by rw [K₂.wr, u₁.wr, hp.wr]; simp,
    by rw [VG.Proof.X25519.Arm.addr_toNat]; exact hp.fit⟩, by rw [K₂.gpr _ (by simp), u₁.gpr],
    fun r hr => by rw [K₂.gpr _ (by simp), u₁.other _ hr], by rw [K₂.rd, u₁.rd], by rw [K₂.wr, u₁.wr],
    by rw [K₂.sp, u₁.sp], by rw [← u₁.mem]; simpa using O₂, ?_⟩
  rw [V₂ (.lr, Impl.Weierstrass.Point.ownAt k) (by simp), u₁.other .lr (by decide)]

/-- The environment of the entry: what the numbers of the slots stand for. -/
def E₀ (k m : Nat) [NeZero m] (dbl : Bool) (s : State) (x : Nat) : Fin m :=
  toM m (2 ^ (64 * k)) (wordsVal s.mem (State.addr (s.gpr .r0)) (enc k dbl x) k)

theorem rIds_lt : ∀ x ∈ rIds, x < 17 := by decide

/-- A function of field operations `ops` that write only the result and the
temporaries (`OpsOk`): the callee-saved registers and `sp` kept, `r12 = ws`,
the memory changed only at `O` and in the own working space, and `O`'s
coordinates below the prime, standing for what `ops` computes from what the
slots stand for. -/
theorem fnOps_ok {S : Impl.Weierstrass.Mont.Modulus} [NeZero S.m] (hM : ModOk S.k S.m) (hodd : S.m % 2 = 1)
    {dbl : Bool} {ops : List FOp} (hO : OpsOk ops) {s : State} (hp : PrePt S.k S.m dbl s) {u : Bool} :
    WP isa (Impl.Weierstrass.Arm.Point.fnOps S dbl ops u) s fun s' => abiPreserved s s' ∧
      Outs (State.addr (s.gpr .r0)) [(Impl.Weierstrass.Point.oAt S.k, 3 * Impl.Weierstrass.Point.elemBytes S.k),
        (Impl.Weierstrass.Point.ownAt S.k, 4096 - Impl.Weierstrass.Point.ownAt S.k)] s.mem s'.mem ∧
      s'.gpr .r12 = s.gpr .r0 ∧
      (∀ j < 3, wordsVal s'.mem (State.addr (s.gpr .r0)) (enc S.k dbl j) S.k < S.m) ∧
      (toM S.m (2 ^ (64 * S.k)) (wordsVal s'.mem (State.addr (s.gpr .r0)) (enc S.k dbl 0) S.k),
        toM S.m (2 ^ (64 * S.k)) (wordsVal s'.mem (State.addr (s.gpr .r0)) (enc S.k dbl 1) S.k),
        toM S.m (2 ^ (64 * S.k)) (wordsVal s'.mem (State.addr (s.gpr .r0)) (enc S.k dbl 2) S.k)) =
        (runOps ops (E₀ S.k S.m dbl s) 0, runOps ops (E₀ S.k S.m dbl s) 1,
          runOps ops (E₀ S.k S.m dbl s) 2) := by
  have hl := lay_nums hp.k3 hp.k6
  have hR := enc_rIds hp.k3 hp.k6 dbl
  have hW := enc_wIds hp.k3 hp.k6 dbl
  rw [Impl.Weierstrass.Arm.Point.fnOps]
  refine WP.seq (WP.mono (entry_ok hp) fun s₁ E => ?_)
  have hI : InvR S.k 17 (enc S.k dbl) (State.addr (s.gpr .r0)) S.m rIds (E₀ S.k S.m dbl s) s₁ := by
    have heq : ∀ x ∈ rIds, wordsVal s₁.mem (State.addr (s.gpr .r0)) (enc S.k dbl x) S.k =
        wordsVal s.mem (State.addr (s.gpr .r0)) (enc S.k dbl x) S.k := fun x hx =>
      Outs.wordsVal E.mem (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact .inl (hR x hx)) (by have := hR x hx; omega_arith)
    exact ⟨E.scr, E.far, rIds_lt, fun x hx => by rw [heq x hx]; exact hp.lt x hx,
      fun x hx => by rw [heq x hx]; rfl⟩
  refine WP.seq (WP.mono (opsR_ok hM rfl (enc_lay hp.k3 hp.k6 dbl) (unitMod_pow_two hodd _) hO hI)
    fun s₂ ⟨K, I₂⟩ => ?_)
  refine WP.mono (ldrs_ok I₂.scr [(.lr, Impl.Weierstrass.Point.ownAt S.k)] (by simp; omega_arith) (by simp) (by simp))
    fun s₃ ⟨M₃, K₃, V₃⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_, ?_, fun j hj => ?_, ?_⟩
  · -- The callee-saved registers.
    by_cases hlr : r = .lr
    · subst hlr
      rw [V₃ (.lr, Impl.Weierstrass.Point.ownAt S.k) (by simp), ← E.saved]
      refine Unch.readW32 (Outs.unch K.mem) (fun w hw => ?_) (by omega_arith)
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at hw
      rcases hw with ⟨x, hx, rfl⟩ | rfl
      · rcases (hW x hx).1 with h | h <;> [exact .inr (by dsimp only; omega_arith); exact .inl (by dsimp only; omega_arith)]
      · exact .inl (by dsimp only; omega_arith)
    · have hr' : r ∉ [Reg.r0, .r1, .r2, .r3, .r12, .lr] := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
      rw [K₃.gpr r (by simp [hlr]), K.rest.gpr r hr', E.keep r (by intro h; simp [h] at hr')]
  · rw [K₃.sp, K.rest.sp, E.sp]
  · -- The memory.
    rw [M₃]
    refine (Outs.sub (rs := [(Impl.Weierstrass.Point.ownAt S.k, 4)]) E.mem fun r hr => ?_).trans
      (Outs.sub K.mem fun r hr => ?_)
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Nat.le_refl _, by dsimp only; omega_arith⟩
    · simp only [List.mem_append, List.mem_map, List.mem_singleton] at hr
      rcases hr with ⟨x, hx, rfl⟩ | rfl
      · rcases (hW x hx).2 with h | h
        · exact ⟨_, List.mem_cons_self, h.1, by dsimp only; omega_arith⟩
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.1, by dsimp only; omega_arith⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by dsimp only; omega_arith, by dsimp only; omega_arith⟩
  · rw [K₃.gpr _ (by simp), K.r12, E.r12]
  · rw [M₃]; exact I₂.lt j (hO.outs j hj)
  · rw [M₃, I₂.val 0 (hO.outs 0 (by decide)), I₂.val 1 (hO.outs 1 (by decide)),
      I₂.val 2 (hO.outs 2 (by decide))]

end VG.Proof.Weierstrass.Arm.Point

end

end


/-!
# The ladder by calls of the point functions, on 32-bit ARM: copies and calls

`copyPt n o a` copies the point at `a` to `o` (`copyPt_ok`), and
`ptCall S dbl` calls `vg_<curve>_point_double` or `vg_<curve>_point_add` on
the working space at `r12` (`ptCall_ok`): it changes only `r0`–`r3` and
`r10`, `O` and the point functions' own working space, and `O` then holds
`rcbAdd` of what `a`, `3b`, `P` and `Q` (or `P`) stood for (`ptVal`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.Arm.Point

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass.Arm.Mont
open VG.Impl.Weierstrass VG.Impl.Weierstrass.Arm.Point
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
  VG.Proof.Weierstrass.Arm.Mont
open VG.Proof.X25519.Arm (Rest Upd wp_mov op2_reg)

/-- `o = a`, for points whose slots (`n` 64-bit words) are in the working
space, with `o`'s apart from each other and from `a`'s. -/
theorem copyPt_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n : Nat} {o a : Pt}
    (hin : ∀ d ∈ [o.x, o.y, o.z, a.x, a.y, a.z], d + 8 * n ≤ size)
    (hoo : (o.x + 8 * n ≤ o.y ∨ o.y + 8 * n ≤ o.x) ∧ (o.x + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.x) ∧
      (o.y + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.y))
    (hoa : ∀ d ∈ [o.x, o.y, o.z], ∀ e ∈ [a.x, a.y, a.z], d + 8 * n ≤ e ∨ e + 8 * n ≤ d) :
    WP isa (.block (copyPt n o a)) s fun s' =>
      wordsVal s'.mem base o.x n = wordsVal s.mem base a.x n ∧
      wordsVal s'.mem base o.y n = wordsVal s.mem base a.y n ∧
      wordsVal s'.mem base o.z n = wordsVal s.mem base a.z n ∧
      Rest [.r4] s s' ∧ Outs base [(o.x, 8 * n), (o.y, 8 * n), (o.z, 8 * n)] s.mem s'.mem := by
  have hn := hs.nowrap
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin hoa
  obtain ⟨iox, ioy, ioz, iax, iay, iaz⟩ := hin
  obtain ⟨⟨xax, xay, xaz⟩, ⟨yax, yay, yaz⟩, ⟨zax, zay, zaz⟩⟩ := hoa
  obtain ⟨xy, xz, yz⟩ := hoo
  simp only [wordsVal_eq_val32]
  rw [copyPt, List.append_assoc, WP.block_append_iff]
  refine WP.mono (copy_ok (2 * n) hs (by omega_using [iox]) (by omega_using [iax]) (by omega_using [xax]))
    fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_rest k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok (2 * n) hs₁ (by omega_using [ioy]) (by omega_using [iay]) (by omega_using [yay]))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_rest k₂ (by decide)
  refine WP.mono (copy_ok (2 * n) hs₂ (by omega_using [ioz]) (by omega_using [iaz]) (by omega_using [zaz]))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  refine ⟨?_, ?_, ?_, (k₁.trans k₂).trans k₃, ?_⟩
  · rw [O₃.val32 (d := o.x) (by omega_using [xz]) (by omega_using [iox, hn]),
      O₂.val32 (d := o.x) (by omega_using [xy]) (by omega_using [iox, hn]), e₁]
  · rw [O₃.val32 (d := o.y) (by omega_using [yz]) (by omega_using [ioy, hn]), e₂,
      O₁.val32 (d := a.y) (by omega_using [xay]) (by omega_using [iay, hn])]
  · rw [e₃, O₂.val32 (d := a.z) (by omega_using [yaz]) (by omega_using [iaz, hn]),
      O₁.val32 (d := a.z) (by omega_using [xaz]) (by omega_using [iaz, hn])]
  · rw [show 4 * (2 * n) = 8 * n by omega_using []] at O₁ O₂ O₃
    exact ((Outs.of_outside O₁ (by simp)).trans (Outs.of_outside O₂ (by simp))).trans
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

theorem fnOps_noFrames (S : Impl.Weierstrass.Mont.Modulus) (dbl : Bool) (ops : List FOp) (u : Bool := false) :
    (fnOps S dbl ops u).noFrames = true := by
  have mul : (Mont.mulFnWith u S.k S.m).noFrames = true := by
    unfold Mont.mulFnWith Mont.mulFnU Mont.mulFn
    cases u <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> (try split) <;> rfl
  have fields (op : FOp) : (opCodeR (enc S.k dbl) S u op).noFrames = true := by
    cases op <;> simp only [opCodeR, callR, Code.noFrames, Bool.true_and, mul] <;> rfl
  have seqs : ∀ ps : List (Prog isa), (∀ p ∈ ps, p.noFrames = true) → (progs ps).noFrames = true := by
    intro ps
    induction ps with
    | nil => intro _; rfl
    | cons p ps ih =>
      intro hp
      cases ps with
      | nil => exact hp p (by simp)
      | cons q qs =>
        change p.noFrames && (progs (q :: qs)).noFrames = true
        rw [hp p (by simp), ih (fun r hr => hp r (by simp [hr]))]
        rfl
  have prog : (fprogR (enc S.k dbl) S ops u).noFrames = true := by
    apply seqs
    intro p hp
    obtain ⟨op, _, rfl⟩ := List.mem_map.mp hp
    exact fields op
  simpa only [Impl.Weierstrass.Arm.Point.fnOps, Code.noFrames, Bool.true_and, Bool.and_true] using prog

/-- A call of a point function, from the working space at `r12`: only
`r0`–`r3`, `r10`, `O` and the own working space change, and `O` holds
`ptVal` of what the constants and the operands stood for. -/
theorem ptCall_ok {S : Impl.Weierstrass.Mont.Modulus} {m k : Nat} [NeZero m] (hm : S.m = m) (hk : S.k = k)
    (hM : ModOk k m) (hodd : m % 2 = 1) (hk6 : k ≤ 6) (dbl : Bool) {a0 : Bool} {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (hf : Far s base 8192)
    (hlt : ∀ x ∈ rIds, wordsVal s.mem base (enc k dbl x) k < m) {u : Bool} :
    WP isa (ptCall S dbl a0 u) s fun s' => Rest [.r10, .r0, .r1, .r2, .r3] s s' ∧
      Outs base [(Impl.Weierstrass.Point.oAt k, 3 * Impl.Weierstrass.Point.elemBytes k),
        (Impl.Weierstrass.Point.ownAt k, 4096 - Impl.Weierstrass.Point.ownAt k)] s.mem s'.mem ∧
      (∀ j < 3, wordsVal s'.mem base (enc k dbl j) k < m) ∧
      (Eb k m dbl s'.mem base 0, Eb k m dbl s'.mem base 1, Eb k m dbl s'.mem base 2) =
        ptVal a0 dbl (Eb k m dbl s.mem base) := by
  obtain ⟨c, w, m', k', d⟩ := S
  dsimp only at hm hk
  subst hm hk
  rw [ptCall]
  refine WP.seq (wp_mov (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_reg _ _) fun s₂ u₂ => WP.block_nil ?_)
  have k₂ : Rest [.r10, .r0] s s₂ := (u₁.rest (by simp)).trans (u₂.rest (by simp))
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have g10 : s₂.gpr .r10 = s.gpr .lr := by rw [u₂.other _ (by decide), u₁.gpr]
  have g0 : s₂.gpr .r0 = s.gpr .r12 := by rw [u₂.gpr, u₁.other _ (by decide)]
  have hf₂ : Far s₂ base 8192 := hf.of_rest k₂
  have hcov : Covers [⟨base, 8192⟩] s₂.wr := by
    have h := hf₂.write (d := 0) (n := 8192) (by omega_using [])
    simp only [off, BitVec.add_zero] at h
    exact Covers.one h
  have e0 : ∀ t : State, t.gpr .r0 = s.gpr .r12 → State.addr (t.gpr .r0) = base := fun t h => by
    rw [h]; exact hs.wb
  refine WP.seq (WP.callCalls (k := ⟨fun t => PrePt k' m' dbl t ∧ t.gpr .r0 = s.gpr .r12 ∧ t.mem = s.mem,
      fun t t' => Outs (State.addr (t.gpr .r0)) [(Impl.Weierstrass.Point.oAt k', 3 * Impl.Weierstrass.Point.elemBytes k'),
          (Impl.Weierstrass.Point.ownAt k', 4096 - Impl.Weierstrass.Point.ownAt k')] t.mem t'.mem ∧
        t'.gpr .r12 = t.gpr .r0 ∧
        (∀ j < 3, wordsVal t'.mem (State.addr (t.gpr .r0)) (enc k' dbl j) k' < m') ∧
        (Eb k' m' dbl t'.mem (State.addr (t.gpr .r0)) 0, Eb k' m' dbl t'.mem (State.addr (t.gpr .r0)) 1,
          Eb k' m' dbl t'.mem (State.addr (t.gpr .r0)) 2) =
        ptVal a0 dbl (Eb k' m' dbl t.mem (State.addr (t.gpr .r0))),
      fun _ _ => True⟩)
    (fun t ⟨hp, _, _⟩ => by
      obtain ⟨tr, t', he, A, O, R, L, E⟩ := fnOps_ok (S := ⟨c, w, m', k', d⟩) hM hodd (ptOps_opsOk a0 dbl) hp
      exact ⟨tr, t', he, A, O, R, L, E.trans (ptOps_run _ a0 dbl)⟩)
    (rd := []) (wr := [⟨base, 8192⟩])
    ⟨⟨rfl, by rw [State.withRegions_wr, State.withRegions_gpr, State.callEntry_gpr _ (by decide),
        e0 _ g0],
      by rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), g0, hs.wb_toNat]; exact hf.nowrap,
      hM.n3, hk6,
      fun x hx => by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), e0 _ g0, State.withRegions_mem,
          State.callEntry_mem, m₂]
        exact hlt x hx⟩,
      by rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), g0],
      by rw [State.withRegions_mem, State.callEntry_mem, m₂]⟩
    (Covers.right hcov) hcov ?_ (fnOps_noFrames _ _ _ u))
  intro s₇ r₇ w₇ p₇ _ hp₇ _ ⟨O, R, L, E⟩
  simp only [State.withRegions_mem, State.callEntry_mem, m₂, State.withRegions_gpr] at O R L E
  rw [State.callEntry_gpr _ (by decide), g0] at R
  rw [State.callEntry_gpr _ (by decide), e0 _ g0] at O L E
  refine wp_mov (op2_reg _ _) fun s₈ u₈ => WP.block_nil ?_
  have hm : s₈.mem = s₇.mem := u₈.mem
  refine ⟨⟨fun r hr => ?_, by rw [u₈.rd, r₇, k₂.rd], by rw [u₈.wr, w₇, k₂.wr],
    by rw [u₈.sp, p₇, k₂.sp]⟩, by rw [hm]; exact O, by rw [hm]; exact L, by rw [hm]; exact E⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h10, h0, h1, h2, h3⟩ := hr
  by_cases hlr : r = .lr
  · subst hlr
    rw [u₈.gpr, hp₇ _ (by decide) (by decide), g10]
  by_cases h12 : r = .r12
  · subst h12
    rw [u₈.other _ (by decide), R]
  have hpres : r ∈ preserved := by revert h10 h0 h1 h2 h3 h12 hlr; cases r <;> decide
  rw [u₈.other _ hlr, hp₇ r hpres hlr, k₂.gpr r (by simp [h10, h0])]

end VG.Proof.Weierstrass.Arm.Point

end

end


/-!
# The ladder by calls of the point functions, on 32-bit ARM

`ladderP L S` (`Impl/Weierstrass/Arm/LadderP.lean`) meets what `ladder_ok`
states of `ladder L S` (`ladderP_ok`), but that it also writes the point
functions' slots and own working space (`ptW`, empty for P-521, whose
ladder is `ladder`): for coordinates of at most 6 words, an iteration
(`ladderPBody_ok`) copies `R` to `P`, so that the doubling's call leaves
`D = R + R` in `O` (`ptCall_ok`), copies it to `P`, so that the addition's
leaves `T = D + G` in `O`, `G` having been copied to `Q` (and `a` and `3b` to
theirs) before the loop, and selects `R = T` or `D`; the ladder's slots lie
below the point functions' (`LadPt`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.Arm.Point

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass.Arm.Mont
open VG.Impl.Weierstrass VG.Impl.Weierstrass.Arm.Point
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass.Arm.Mont
open VG.Proof.X25519.Arm (Rest Upd wp_mov op2_imm)

/-- The point functions' slots and own working space, which the ladder
writes if it calls them. -/
def ptW (n : Nat) : List (Nat × Nat) :=
  if n ≤ 6 then [(Impl.Weierstrass.Point.oAt n, 4096 - Impl.Weierstrass.Point.oAt n)] else []

/-- What `ladderP` writes. -/
def ladWp (L : LadderCfg) (wk : Nat) : List (Nat × Nat) := ladWx L wk ++ ptW L.M.n

/-- The ladder's slots and modulus lie below the point functions' slots. -/
structure LadPt (L : LadderCfg) : Prop where
  sl : ∀ x ∈ ladSlots L, x + 8 * L.M.n ≤ Impl.Weierstrass.Point.oAt L.M.n
  mo : L.M.mo + 8 * L.M.n ≤ Impl.Weierstrass.Point.oAt L.M.n

theorem ModOk.odd {n m : Nat} (h : Mont.ModOk n m) : m % 2 = 1 := by
  have h2 : (m * minv m + 1) % 2 = 0 := by
    rw [← Nat.mod_mod_of_dvd _ (show 2 ∣ 2 ^ 64 by decide), h.inv]
  rcases Nat.mod_two_eq_zero_or_one m with h0 | h1
  · simp [Nat.add_mod, Nat.mul_mod, h0] at h2
  · exact h1

section enc
variable (k : Nat) (dbl : Bool)

theorem enc_0 : enc k dbl 0 = Impl.Weierstrass.Point.oAt k := by simp [enc]
theorem enc_1 : enc k dbl 1 = Impl.Weierstrass.Point.oAt k + Impl.Weierstrass.Point.elemBytes k := by simp [enc]
theorem enc_2 : enc k dbl 2 = Impl.Weierstrass.Point.oAt k + 2 * Impl.Weierstrass.Point.elemBytes k := by simp [enc]; omega_arith
theorem enc_3 : enc k dbl 3 = Impl.Weierstrass.Point.pAt k := by simp [enc]
theorem enc_4 : enc k dbl 4 = Impl.Weierstrass.Point.pAt k + Impl.Weierstrass.Point.elemBytes k := by simp [enc]
theorem enc_5 : enc k dbl 5 = Impl.Weierstrass.Point.pAt k + 2 * Impl.Weierstrass.Point.elemBytes k := by simp [enc]; omega_arith
theorem enc_6 : enc k dbl 6 = if dbl then Impl.Weierstrass.Point.pAt k else Impl.Weierstrass.Point.qAt k := by simp [enc]
theorem enc_7 : enc k dbl 7 = (if dbl then Impl.Weierstrass.Point.pAt k else Impl.Weierstrass.Point.qAt k) + Impl.Weierstrass.Point.elemBytes k := by
  simp [enc]
theorem enc_8 : enc k dbl 8 = (if dbl then Impl.Weierstrass.Point.pAt k else Impl.Weierstrass.Point.qAt k) + 2 * Impl.Weierstrass.Point.elemBytes k := by
  simp [enc]; omega_arith
theorem enc_9 : enc k dbl 9 = Impl.Weierstrass.Point.aAt k := by simp [enc]
theorem enc_10 : enc k dbl 10 = Impl.Weierstrass.Point.b3At k := by simp [enc]

end enc

/-- The bounds a call needs, by offset. -/
theorem rIds_lt_of {k m : Nat} (dbl : Bool) {mem : Mem} {base : Addr}
    (h : ∀ x ∈ [Impl.Weierstrass.Point.pAt k, Impl.Weierstrass.Point.pAt k + Impl.Weierstrass.Point.elemBytes k, Impl.Weierstrass.Point.pAt k + 2 * Impl.Weierstrass.Point.elemBytes k,
      (if dbl then Impl.Weierstrass.Point.pAt k else Impl.Weierstrass.Point.qAt k), (if dbl then Impl.Weierstrass.Point.pAt k else Impl.Weierstrass.Point.qAt k) + Impl.Weierstrass.Point.elemBytes k,
      (if dbl then Impl.Weierstrass.Point.pAt k else Impl.Weierstrass.Point.qAt k) + 2 * Impl.Weierstrass.Point.elemBytes k, Impl.Weierstrass.Point.aAt k, Impl.Weierstrass.Point.b3At k],
      wordsVal mem base x k < m) :
    ∀ x ∈ rIds, wordsVal mem base (enc k dbl x) k < m := by
  intro x hx
  simp only [rIds, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [enc_3, enc_4, enc_5, enc_6, enc_7, enc_8, enc_9, enc_10] <;> exact h _ (by simp)

/-- The point functions' `Q`, `a` and `3b` in `m` hold `G`, `a` and `3b` of
`m₀`. -/
def CpOk (L : LadderCfg) (base : Addr) (m m₀ : Mem) : Prop :=
  wordsVal m base (Impl.Weierstrass.Point.qAt L.M.n) L.M.n = wordsVal m₀ base L.G.x L.M.n ∧
  wordsVal m base (Impl.Weierstrass.Point.qAt L.M.n + Impl.Weierstrass.Point.elemBytes L.M.n) L.M.n =
    wordsVal m₀ base L.G.y L.M.n ∧
  wordsVal m base (Impl.Weierstrass.Point.qAt L.M.n + 2 * Impl.Weierstrass.Point.elemBytes L.M.n) L.M.n =
    wordsVal m₀ base L.G.z L.M.n ∧
  wordsVal m base (Impl.Weierstrass.Point.aAt L.M.n) L.M.n = wordsVal m₀ base L.S.a L.M.n ∧
  wordsVal m base (Impl.Weierstrass.Point.b3At L.M.n) L.M.n = wordsVal m₀ base L.S.b3 L.M.n

/-- A fact about the layout's numbers for `k` words, `3 ≤ k ≤ 6`, from the
fact for each `k`, which `decide` proves more cheaply than `omega` the fact
for any `k`. -/
@[elab_as_elim]
theorem lay_cases {P : Nat → Prop} (k : Nat) (hk3 : 3 ≤ k) (hk6 : k ≤ 6) (h3 : P 3) (h4 : P 4)
    (h5 : P 5) (h6 : P 6) : P k := by
  obtain rfl | rfl | rfl | rfl : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega_using [hk3, hk6]
  exacts [h3, h4, h5, h6]

/-- The copies survive changes apart from them. -/
theorem CpOk.keep {L : LadderCfg} {base : Addr} {m m' m₀ : Mem} (h : CpOk L base m m₀)
    (hk3 : 3 ≤ L.M.n) (hk6 : L.M.n ≤ 6) {W : List (Nat × Nat)} (hU : Unch base W m m')
    (hW : ∀ w ∈ W, w.1 + w.2 ≤ Impl.Weierstrass.Point.qAt L.M.n ∨ Impl.Weierstrass.Point.ownAt L.M.n ≤ w.1) :
    CpOk L base m' m₀ := by
  have ap : ∀ x, Impl.Weierstrass.Point.qAt L.M.n ≤ x ∧ x + 8 * L.M.n ≤ Impl.Weierstrass.Point.ownAt L.M.n →
      ∀ w ∈ W, x + 8 * L.M.n ≤ w.1 ∨ w.1 + w.2 ≤ x := fun x hx w hw =>
    (hW w hw).elim (fun h => .inr (Nat.le_trans h hx.1)) (fun h => .inl (Nat.le_trans hx.2 h))
  have hp : ∀ x ∈ [Impl.Weierstrass.Point.qAt L.M.n,
      Impl.Weierstrass.Point.qAt L.M.n + Impl.Weierstrass.Point.elemBytes L.M.n,
      Impl.Weierstrass.Point.qAt L.M.n + 2 * Impl.Weierstrass.Point.elemBytes L.M.n,
      Impl.Weierstrass.Point.aAt L.M.n, Impl.Weierstrass.Point.b3At L.M.n],
      (Impl.Weierstrass.Point.qAt L.M.n ≤ x ∧ x + 8 * L.M.n ≤ Impl.Weierstrass.Point.ownAt L.M.n) ∧
        x + 8 * L.M.n ≤ 2 ^ 64 :=
    lay_cases L.M.n hk3 hk6 (by decide) (by decide) (by decide) (by decide)
  rw [List.forall_mem_cons, List.forall_mem_cons, List.forall_mem_cons, List.forall_mem_cons,
    List.forall_mem_singleton] at hp
  obtain ⟨p1, p2, p3, p4, p5⟩ := hp
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨by rw [hU.wordsVal (ap _ p1.1) p1.2]; exact h1, by rw [hU.wordsVal (ap _ p2.1) p2.2]; exact h2,
    by rw [hU.wordsVal (ap _ p3.1) p3.2]; exact h3, by rw [hU.wordsVal (ap _ p4.1) p4.2]; exact h4,
    by rw [hU.wordsVal (ap _ p5.1) p5.2]; exact h5⟩

/-- The loop's invariant at `r11 = j`: `Q j` accepts what `R` holds, and the
point functions' `Q`, `a` and `3b` hold `G`, `a` and `3b`. -/
structure LadInvP (L : LadderCfg) (wk : Nat) (C : Spec.Weierstrass.Curve) (base : Addr) (size : Nat)
    (Q : Nat → Spec.Weierstrass.Fe C → Spec.Weierstrass.Fe C → Spec.Weierstrass.Fe C → Prop) (s₀ s : State) (j : Nat) : Prop where
  scr : Scr s base size
  r11 : s.gpr .r11 = BitVec.ofNat 32 j
  keep : Rest powClob s₀ s
  unch : Unch base (ladWx L wk ++ [(Impl.Weierstrass.Point.oAt L.M.n, 4096 - Impl.Weierstrass.Point.oAt L.M.n)]) s₀.mem s.mem
  mod : ModOkW L.M size C.p s.mem base
  lt : ∀ x ∈ [L.R.x, L.R.y, L.R.z], wordsVal s.mem base x L.M.n < C.p
  q : Q j (tmv C L.M.n base s L.R.x) (tmv C L.M.n base s L.R.y) (tmv C L.M.n base s L.R.z)
  cp : CpOk L base s.mem s₀.mem

/-- Apart from each of a few ranges, for numbers of the layout. -/
tactic_template "apart_ranges" : tactic => `(tactic| (simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, or_imp, forall_and, forall_eq_or_imp, forall_eq, List.mem_singleton]; omega_arith))

/-- What `copyPt_ok` asks of a copy into `P` or `Q` (`ptAt k o`) from three
slots below it, for numbers of the layout: proved once rather than by
`omega` at each copy. -/
theorem copyPt_conds {k size o : Nat} {a : Pt} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) (hsz : size = 4096)
    (ho : o = Impl.Weierstrass.Point.pAt k ∨ o = Impl.Weierstrass.Point.qAt k)
    (hax : a.x + 8 * k ≤ o) (hay : a.y + 8 * k ≤ o) (haz : a.z + 8 * k ≤ o) :
    (∀ d ∈ [(ptAt k o).x, (ptAt k o).y, (ptAt k o).z, a.x, a.y, a.z], d + 8 * k ≤ size) ∧
    (((ptAt k o).x + 8 * k ≤ (ptAt k o).y ∨ (ptAt k o).y + 8 * k ≤ (ptAt k o).x) ∧
      ((ptAt k o).x + 8 * k ≤ (ptAt k o).z ∨ (ptAt k o).z + 8 * k ≤ (ptAt k o).x) ∧
      ((ptAt k o).y + 8 * k ≤ (ptAt k o).z ∨ (ptAt k o).z + 8 * k ≤ (ptAt k o).y)) ∧
    (∀ d ∈ [(ptAt k o).x, (ptAt k o).y, (ptAt k o).z], ∀ e ∈ [a.x, a.y, a.z], d + 8 * k ≤ e ∨ e + 8 * k ≤ d) := by
  subst hsz
  have he : ∀ e ∈ [a.x, a.y, a.z], e + 8 * k ≤ o := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hax, hay, haz⟩
  have hd : (∀ d ∈ [(ptAt k o).x, (ptAt k o).y, (ptAt k o).z], o ≤ d ∧ d + 8 * k ≤ 4096) ∧
      (((ptAt k o).x + 8 * k ≤ (ptAt k o).y ∨ (ptAt k o).y + 8 * k ≤ (ptAt k o).x) ∧
        ((ptAt k o).x + 8 * k ≤ (ptAt k o).z ∨ (ptAt k o).z + 8 * k ≤ (ptAt k o).x) ∧
        ((ptAt k o).y + 8 * k ≤ (ptAt k o).z ∨ (ptAt k o).z + 8 * k ≤ (ptAt k o).y)) := by
    rcases ho with rfl | rfl <;> exact lay_cases k hk3 hk6 (by decide) (by decide) (by decide) (by decide)
  refine ⟨fun d hd' => ?_, hd.2, fun d hd' e he' => Or.inr (Nat.le_trans (he e he') (hd.1 d hd').1)⟩
  rcases List.mem_append.mp (show d ∈ [(ptAt k o).x, (ptAt k o).y, (ptAt k o).z] ++ _ from hd') with h | h
  · exact (hd.1 d h).2
  · have h₁ := he d h; have h₂ := (hd.1 _ (List.mem_cons_self ..)).2; simp only [ptAt] at h₂; omega_using [h₁, h₂]

theorem oAt_le_pAt (k : Nat) : Impl.Weierstrass.Point.oAt k ≤ Impl.Weierstrass.Point.pAt k :=
  Nat.sub_le _ _

theorem oAt_le_qAt (k : Nat) : Impl.Weierstrass.Point.oAt k ≤ Impl.Weierstrass.Point.qAt k :=
  Nat.le_trans (oAt_le_pAt k) (Nat.sub_le _ _)

/-- `O`'s slots are below `P`. -/
theorem oPt_below {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) :
    (ptAt k (Impl.Weierstrass.Point.oAt k)).x + 8 * k ≤ Impl.Weierstrass.Point.pAt k ∧
    (ptAt k (Impl.Weierstrass.Point.oAt k)).y + 8 * k ≤ Impl.Weierstrass.Point.pAt k ∧
    (ptAt k (Impl.Weierstrass.Point.oAt k)).z + 8 * k ≤ Impl.Weierstrass.Point.pAt k :=
  lay_cases k hk3 hk6 (by decide) (by decide) (by decide) (by decide)

/-- What `selPt_ok` asks of a selection of `P` or `O` into three slots below
`O`, for numbers of the layout: proved once rather than by `omega` in the
iteration. -/
theorem selPt_conds {k size : Nat} {a : Pt} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) (hsz : size = 4096)
    (hax : a.x + 8 * k ≤ Impl.Weierstrass.Point.oAt k) (hay : a.y + 8 * k ≤ Impl.Weierstrass.Point.oAt k)
    (haz : a.z + 8 * k ≤ Impl.Weierstrass.Point.oAt k) :
    (∀ d ∈ [a.x, a.y, a.z, (ptAt k (Impl.Weierstrass.Point.pAt k)).x, (ptAt k (Impl.Weierstrass.Point.pAt k)).y,
      (ptAt k (Impl.Weierstrass.Point.pAt k)).z, (ptAt k (Impl.Weierstrass.Point.oAt k)).x,
      (ptAt k (Impl.Weierstrass.Point.oAt k)).y, (ptAt k (Impl.Weierstrass.Point.oAt k)).z], d + 8 * k ≤ size) ∧
    (∀ d ∈ [a.x, a.y, a.z], ∀ e ∈ [(ptAt k (Impl.Weierstrass.Point.pAt k)).x,
      (ptAt k (Impl.Weierstrass.Point.pAt k)).y, (ptAt k (Impl.Weierstrass.Point.pAt k)).z,
      (ptAt k (Impl.Weierstrass.Point.oAt k)).x, (ptAt k (Impl.Weierstrass.Point.oAt k)).y,
      (ptAt k (Impl.Weierstrass.Point.oAt k)).z], d + 8 * k ≤ e ∨ e + 8 * k ≤ d) := by
  have hd : ∀ d ∈ [a.x, a.y, a.z], d + 8 * k ≤ Impl.Weierstrass.Point.oAt k := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hax, hay, haz⟩
  have he : ∀ e ∈ [(ptAt k (Impl.Weierstrass.Point.pAt k)).x,
      (ptAt k (Impl.Weierstrass.Point.pAt k)).y, (ptAt k (Impl.Weierstrass.Point.pAt k)).z,
      (ptAt k (Impl.Weierstrass.Point.oAt k)).x, (ptAt k (Impl.Weierstrass.Point.oAt k)).y,
      (ptAt k (Impl.Weierstrass.Point.oAt k)).z], Impl.Weierstrass.Point.oAt k ≤ e ∧ e + 8 * k ≤ size := by
    subst hsz; exact lay_cases k hk3 hk6 (by decide) (by decide) (by decide) (by decide)
  refine ⟨fun d hd' => ?_, fun d hd' e he' => Or.inl (Nat.le_trans (hd d hd') (he e he').1)⟩
  rcases List.mem_append.mp (show d ∈ [a.x, a.y, a.z] ++ _ from hd') with h | h
  · have h₁ := hd d h; have h₂ := (he _ (List.mem_cons_self ..)).1; have h₃ := (he _ (List.mem_cons_self ..)).2
    omega_using [h₁, h₂, h₃]
  · exact (he d h).2

open Spec.Weierstrass.Point Impl.Weierstrass.Point in
/-- An iteration's copies and calls write within the point functions' slots
and own working space: proved once rather than by `omega` in the iteration. -/
theorem iterOuts_cover {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) :
    ∀ w ∈ [(pAt k, 8 * k), (pAt k + elemBytes k, 8 * k), (pAt k + 2 * elemBytes k, 8 * k)] ++
        [(oAt k, 3 * elemBytes k), (ownAt k, 4096 - ownAt k)] ++
        ([(pAt k, 8 * k), (pAt k + elemBytes k, 8 * k), (pAt k + 2 * elemBytes k, 8 * k)] ++
          [(oAt k, 3 * elemBytes k), (ownAt k, 4096 - ownAt k)]),
      ∃ w' ∈ [(oAt k, 4096 - oAt k)], w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 :=
  lay_cases k hk3 hk6 (by decide) (by decide) (by decide) (by decide)

open Spec.Weierstrass.Point Impl.Weierstrass.Point in
/-- The setup's copies write within the point functions' slots. -/
theorem setupOuts_cover {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) :
    ∀ w ∈ [(qAt k, 8 * k), (qAt k + elemBytes k, 8 * k), (qAt k + 2 * elemBytes k, 8 * k)] ++
        ([(aAt k, 4 * (2 * k))] ++ [(b3At k, 4 * (2 * k))]),
      ∃ w' ∈ [(oAt k, 4096 - oAt k)], w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 :=
  lay_cases k hk3 hk6 (by decide) (by decide) (by decide) (by decide)

/-- Copy the input point and curve parameters to the point-call slots.
Shared by the variable-base ladder and fixed-base comb. -/
theorem ladderSetup_ok {L : LadderCfg} {base : Addr} {s : State}
    (hs : Scr s base 4096) (hk3 : 3 ≤ L.M.n) (hk6 : L.M.n ≤ 6)
    (hPt : LadPt L) :
    WP isa (.block (ladderSetup L)) s fun t =>
      Rest [.r4] s t ∧
      Unch base [(Impl.Weierstrass.Point.oAt L.M.n,
        4096 - Impl.Weierstrass.Point.oAt L.M.n)] s.mem t.mem ∧ CpOk L base t.mem s.mem := by
  have hsz : 4096 = 4096 := rfl
  have hl := lay_nums hk3 hk6
  have hn := hs.nowrap
  have gx : L.G.x + 8 * L.M.n ≤ Impl.Weierstrass.Point.oAt L.M.n := hPt.sl _ (ladR_slots L _ (by simp [ladR, ladRo]))
  have gy : L.G.y + 8 * L.M.n ≤ Impl.Weierstrass.Point.oAt L.M.n := hPt.sl _ (ladR_slots L _ (by simp [ladR, ladRo]))
  have gz : L.G.z + 8 * L.M.n ≤ Impl.Weierstrass.Point.oAt L.M.n := hPt.sl _ (ladR_slots L _ (by simp [ladR, ladRo]))
  have ga : L.S.a + 8 * L.M.n ≤ Impl.Weierstrass.Point.oAt L.M.n := hPt.sl _ (ladR_slots L _ (by simp [ladR, ladRo]))
  have gb : L.S.b3 + 8 * L.M.n ≤ Impl.Weierstrass.Point.oAt L.M.n := hPt.sl _ (ladR_slots L _ (by simp [ladR, ladRo]))
  have cG := copyPt_conds (a := L.G) hk3 hk6 hsz (.inr rfl) (Nat.le_trans gx (oAt_le_qAt _))
    (Nat.le_trans gy (oAt_le_qAt _)) (Nat.le_trans gz (oAt_le_qAt _))
  rw [ladderSetup, List.append_assoc, WP.block_append_iff]
  -- `Q = G`, `a`, `3b`.
  refine WP.mono (copyPt_ok hs (n := L.M.n) (o := ptAt L.M.n (Impl.Weierstrass.Point.qAt L.M.n)) (a := L.G) cG.1 cG.2.1 cG.2.2)
    fun s₁ ⟨gx₁, gy₁, gz₁, k₁, O₁⟩ => ?_
  simp only [ptAt] at gx₁ gy₁ gz₁ O₁
  have hs₁ := hs.of_rest k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok (2 * L.M.n) hs₁ (o := Impl.Weierstrass.Point.aAt L.M.n) (a := L.S.a) (by omega_arith) (by omega_arith)
    (by omega_arith)) fun s₂ ⟨a₂, k₂, O₂⟩ => ?_
  rw [← wordsVal_eq_val32, ← wordsVal_eq_val32] at a₂
  have hs₂ := hs₁.of_rest k₂ (by decide)
  refine WP.mono (copy_ok (2 * L.M.n) hs₂ (o := Impl.Weierstrass.Point.b3At L.M.n) (a := L.S.b3) (by omega_arith) (by omega_arith)
    (by omega_arith)) fun s₃ ⟨b₃, k₃, O₃⟩ => ?_
  rw [← wordsVal_eq_val32, ← wordsVal_eq_val32] at b₃
  have hs₃ := hs₂.of_rest k₃ (by decide)
  have U₂ : Unch base [(Impl.Weierstrass.Point.aAt L.M.n, 4 * (2 * L.M.n))] s₁.mem s₂.mem := O₂.unch
  have U₃ : Unch base [(Impl.Weierstrass.Point.b3At L.M.n, 4 * (2 * L.M.n))] s₂.mem s₃.mem := O₃.unch
  refine ⟨k₁.trans (k₂.trans k₃),
    ((Outs.unch O₁).trans (U₂.trans U₃)).cover (setupOuts_cover hk3 hk6), ?_⟩
  have k₂₄ : Unch base [(Impl.Weierstrass.Point.aAt L.M.n, 4 * (2 * L.M.n)),
      (Impl.Weierstrass.Point.b3At L.M.n, 4 * (2 * L.M.n))] s₁.mem s₃.mem := by
    exact U₂.trans U₃
  have k₃₄ : Unch base [(Impl.Weierstrass.Point.b3At L.M.n, 4 * (2 * L.M.n))] s₂.mem s₃.mem := by
    exact U₃
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [k₂₄.wordsVal (by exact lay_cases L.M.n hk3 hk6 (by decide) (by decide) (by decide) (by decide)) (by omega_arith), gx₁]
  · rw [k₂₄.wordsVal (by exact lay_cases L.M.n hk3 hk6 (by decide) (by decide) (by decide) (by decide)) (by omega_arith), gy₁]
  · rw [k₂₄.wordsVal (by exact lay_cases L.M.n hk3 hk6 (by decide) (by decide) (by decide) (by decide)) (by omega_arith), gz₁]
  · rw [k₃₄.wordsVal (by exact lay_cases L.M.n hk3 hk6 (by decide) (by decide) (by decide) (by decide)) (by omega_arith), a₂, (Outs.unch O₁).wordsVal (by apart_ranges) (by omega_arith)]
  · rw [b₃, U₂.wordsVal (by apart_ranges) (by omega_arith), (Outs.unch O₁).wordsVal (by apart_ranges) (by omega_arith)]

section body
variable {L : LadderCfg} {wk : Nat} {C : Spec.Weierstrass.Curve} {base : Addr} {size : Nat}

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
theorem ladderPBody_ok {k : Nat} {Q : Nat → Spec.Weierstrass.Fe C → Spec.Weierstrass.Fe C → Spec.Weierstrass.Fe C → Prop}
    (hL : LadLay L size 8192) (hW : LadWk L size wk) {S : Impl.Weierstrass.Mont.Modulus}
    (hF : FnOk L.M wk S C.p) (hk6 : L.M.n ≤ 6) (hP : LadPt L) (hb8 : L.bits < 8192)
    {s₀ : State} (hf₀ : Far s₀ base 8192) (hlt₀ : ∀ x ∈ ladRo L, wordsVal s₀.mem base x L.M.n < C.p)
    {a0 : Bool} (hstep : Step L C base s₀ k Q a0)
    (hbits : ∀ t < L.nbits, s₀.mem (off base (L.bits + t)) = if k.testBit t then 1 else 0)
    {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j ≤ L.nbits) (hI : LadInvP L wk C base size Q s₀ s j) {u : Bool} :
    WP isa (ladderPBody L S a0 u) s fun s' =>
      LadInvP L wk C base size Q s₀ s' (j - 1) ∧ s'.z = decide (j - 1 = 0) := by
  have hM : Mont.ModOk L.M.n C.p := by have h := hF.ok; rw [hF.k, hF.m] at h; exact h
  have hodd := ModOk.odd hM
  have hk3 := hM.n3
  have hl := lay_nums hk3 hk6
  have hwk := hF.wk
  have hown := own_le L.M.n hM.n9
  have hsz : size = 4096 := by have := hW.le; have := hI.scr.small; omega_arith
  have hbl : 4096 ≤ L.bits := by have := hW.bits; omega_arith
  have hnb := hL.nbits
  have hlb := hL.bits
  have rx : L.R.x + 8 * L.M.n ≤ Impl.Weierstrass.Point.oAt L.M.n := hP.sl _ (ladPts_slots L _ (by simp))
  have ry : L.R.y + 8 * L.M.n ≤ Impl.Weierstrass.Point.oAt L.M.n := hP.sl _ (ladPts_slots L _ (by simp))
  have rz : L.R.z + 8 * L.M.n ≤ Impl.Weierstrass.Point.oAt L.M.n := hP.sl _ (ladPts_slots L _ (by simp))
  have cR := copyPt_conds (a := L.R) hk3 hk6 hsz (.inl rfl) (Nat.le_trans rx (oAt_le_pAt _))
    (Nat.le_trans ry (oAt_le_pAt _)) (Nat.le_trans rz (oAt_le_pAt _))
  have cO := copyPt_conds (a := ptAt L.M.n (Impl.Weierstrass.Point.oAt L.M.n)) hk3 hk6 hsz (.inl rfl)
    (oPt_below hk3 hk6).1 (oPt_below hk3 hk6).2.1 (oPt_below hk3 hk6).2.2
  -- `r11 -= 1`.
  rw [ladderPBody]
  refine WP.seq (wp_decCounter hj hI.r11 fun s₁ u₁ => WP.block_nil ?_)
  have hm₁ : s₁.mem = s.mem := u₁.mem
  have k₁ : Rest [.r11] s s₁ := u₁.rest (by simp)
  have hs₁ := hI.scr.of_rest k₁ (by decide)
  -- `P = R`.
  refine WP.seq (WP.mono (copyPt_ok hs₁ (n := L.M.n) (o := ptAt L.M.n (Impl.Weierstrass.Point.pAt L.M.n))
    (a := L.R) cR.1 cR.2.1 cR.2.2)
    fun s₂ ⟨px₂, py₂, pz₂, k₂, O₂⟩ => ?_)
  simp only [ptAt] at px₂ py₂ pz₂ O₂
  rw [hm₁] at px₂ py₂ pz₂ O₂
  have hs₂ := hs₁.of_rest k₂ (by decide)
  have hf₂ : Far s₂ base 8192 := ((hf₀.of_rest hI.keep).of_rest k₁).of_rest k₂
  have cp₂ : CpOk L base s₂.mem s₀.mem := hI.cp.keep hk3 hk6 (Outs.unch O₂) (lay_cases L.M.n hk3 hk6 (by decide) (by decide) (by decide) (by decide))
  obtain ⟨gx₂, gy₂, gz₂, ga₂, gb₂⟩ := cp₂
  have la : wordsVal s₀.mem base L.S.a L.M.n < C.p := hlt₀ _ (by simp [ladRo])
  have lb : wordsVal s₀.mem base L.S.b3 L.M.n < C.p := hlt₀ _ (by simp [ladRo])
  have lgx : wordsVal s₀.mem base L.G.x L.M.n < C.p := hlt₀ _ (by simp [ladRo])
  have lgy : wordsVal s₀.mem base L.G.y L.M.n < C.p := hlt₀ _ (by simp [ladRo])
  have lgz : wordsVal s₀.mem base L.G.z L.M.n < C.p := hlt₀ _ (by simp [ladRo])
  have lrx : wordsVal s.mem base L.R.x L.M.n < C.p := hI.lt _ (by simp)
  have lry : wordsVal s.mem base L.R.y L.M.n < C.p := hI.lt _ (by simp)
  have lrz : wordsVal s.mem base L.R.z L.M.n < C.p := hI.lt _ (by simp)
  -- `O = P + P`.
  refine WP.seq (WP.mono (ptCall_ok hF.m hF.k hM hodd hk6 true hs₂ hf₂ (rIds_lt_of true fun x hx => by
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
  obtain ⟨d6, d7, d8⟩ := Eb_dbl (k := L.M.n) (m := C.p) s₂.mem base
  rw [ptVal_dbl a0 d6 d7 d8] at E₃
  simp only [Eb, enc_0, enc_1, enc_2, enc_3, enc_4, enc_5, enc_9, enc_10] at E₃
  rw [ga₂, gb₂, px₂, py₂, pz₂] at E₃
  have l3x := L₃ 0 (by decide)
  have l3y := L₃ 1 (by decide)
  have l3z := L₃ 2 (by decide)
  rw [enc_0] at l3x
  rw [enc_1] at l3y
  rw [enc_2] at l3z
  have hs₃ := hs₂.of_rest k₃ (by decide)
  have hf₃ : Far s₃ base 8192 := hf₂.of_rest k₃
  -- `P = O`.
  refine WP.seq (WP.mono (copyPt_ok hs₃ (n := L.M.n) (o := ptAt L.M.n (Impl.Weierstrass.Point.pAt L.M.n))
    (a := ptAt L.M.n (Impl.Weierstrass.Point.oAt L.M.n)) cO.1 cO.2.1 cO.2.2)
    fun s₄ ⟨px₄, py₄, pz₄, k₄, O₄⟩ => ?_)
  simp only [ptAt] at px₄ py₄ pz₄ O₄
  have hs₄ := hs₃.of_rest k₄ (by decide)
  have hf₄ : Far s₄ base 8192 := hf₃.of_rest k₄
  have cp₄ : CpOk L base s₄.mem s₀.mem :=
    (CpOk.keep ⟨gx₂, gy₂, gz₂, ga₂, gb₂⟩ hk3 hk6 (Outs.unch O₃) (lay_cases L.M.n hk3 hk6 (by decide) (by decide) (by decide) (by decide))).keep hk3 hk6 (Outs.unch O₄)
      (lay_cases L.M.n hk3 hk6 (by decide) (by decide) (by decide) (by decide))
  obtain ⟨gx₄, gy₄, gz₄, ga₄, gb₄⟩ := cp₄
  -- `O = P + Q`.
  refine WP.seq (WP.mono (ptCall_ok hF.m hF.k hM hodd hk6 false hs₄ hf₄ (rIds_lt_of false fun x hx => by
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
  rw [ptVal_add] at E₅
  simp only [Eb, enc_0, enc_1, enc_2, enc_3, enc_4, enc_5, enc_6, enc_7, enc_8, enc_9, enc_10,
    Bool.false_eq_true, ↓reduceIte] at E₅
  rw [ga₄, gb₄, px₄, py₄, pz₄, gx₄, gy₄, gz₄] at E₅
  have l5x := L₅ 0 (by decide)
  have l5y := L₅ 1 (by decide)
  have l5z := L₅ 2 (by decide)
  rw [enc_0] at l5x
  rw [enc_1] at l5y
  rw [enc_2] at l5z
  -- `P` still holds `D`.
  have p5x : wordsVal s₅.mem base (Impl.Weierstrass.Point.pAt L.M.n) L.M.n =
      wordsVal s₃.mem base (Impl.Weierstrass.Point.oAt L.M.n) L.M.n := by
    rw [(Outs.unch O₅).wordsVal (by exact lay_cases L.M.n hk3 hk6 (by decide) (by decide) (by decide) (by decide)) (by omega_arith), px₄]
  have p5y : wordsVal s₅.mem base (Impl.Weierstrass.Point.pAt L.M.n + Impl.Weierstrass.Point.elemBytes L.M.n) L.M.n =
      wordsVal s₃.mem base (Impl.Weierstrass.Point.oAt L.M.n + Impl.Weierstrass.Point.elemBytes L.M.n) L.M.n := by
    rw [(Outs.unch O₅).wordsVal (by exact lay_cases L.M.n hk3 hk6 (by decide) (by decide) (by decide) (by decide)) (by omega_arith), py₄]
  have p5z : wordsVal s₅.mem base (Impl.Weierstrass.Point.pAt L.M.n + 2 * Impl.Weierstrass.Point.elemBytes L.M.n) L.M.n =
      wordsVal s₃.mem base (Impl.Weierstrass.Point.oAt L.M.n + 2 * Impl.Weierstrass.Point.elemBytes L.M.n) L.M.n := by
    rw [(Outs.unch O₅).wordsVal (by exact lay_cases L.M.n hk3 hk6 (by decide) (by decide) (by decide) (by decide)) (by omega_arith), pz₄]
  have cp₅ : CpOk L base s₅.mem s₀.mem := CpOk.keep ⟨gx₄, gy₄, gz₄, ga₄, gb₄⟩ hk3 hk6 (Outs.unch O₅) (lay_cases L.M.n hk3 hk6 (by decide) (by decide) (by decide) (by decide))
  -- What changed: the point functions' slots.
  have U₁₅ : Unch base [(Impl.Weierstrass.Point.oAt L.M.n, 4096 - Impl.Weierstrass.Point.oAt L.M.n)] s.mem s₅.mem :=
    (((Outs.unch O₂).trans (Outs.unch O₃)).trans ((Outs.unch O₄).trans (Outs.unch O₅))).cover (iterOuts_cover hk3 hk6)
  have hU₅ : Unch base (ladWx L wk ++ [(Impl.Weierstrass.Point.oAt L.M.n, 4096 - Impl.Weierstrass.Point.oAt L.M.n)])
      s₀.mem s₅.mem :=
    (hI.unch.trans U₁₅).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hw
      · exact List.mem_append_right _ hw
  have hbyte : s₅.mem (off base (L.bits + (j - 1))) = if k.testBit (j - 1) then 1 else 0 := by
    rw [hU₅.byte (fun w hw => by
      simp only [ladWx, List.mem_append, List.mem_singleton] at hw
      rcases hw with (hw | rfl) | rfl
      · have := hL.bits_w w hw; omega_arith
      · dsimp only; omega_arith
      · dsimp only; omega_arith) (by omega_arith), hbits _ (by omega_arith)]
  have K₅ : Rest powClob s s₅ :=
    (k₁.mono (by simp [powClob])).trans <| (k₂.mono (by simp [powClob, clob])).trans <|
      (k₃.mono (by simp [powClob, clob])).trans <| (k₄.mono (by simp [powClob, clob])).trans
        (k₅.mono (by simp [powClob, clob]))
  have r11₅ : s₅.gpr .r11 = BitVec.ofNat 32 (j - 1) := by
    rw [k₅.gpr _ (by decide), k₄.gpr _ (by decide), k₃.gpr _ (by decide), k₂.gpr _ (by decide), u₁.gpr]
  have hs₅ := hs₄.of_rest k₅ (by decide)
  -- `R = O` or `P`.
  rw [List.append_assoc]
  refine VG.Proof.X25519.Arm.WP.append (bitMask_bool_ok hs₅ ((hf₀.of_rest hI.keep).of_rest K₅) r11₅ (by omega_arith)
    hb8 hbyte) fun s₆ ⟨c₆, k₆, hm₆⟩ => ?_
  have hs₆ := hs₅.of_rest k₆ (by decide)
  obtain ⟨rxy, rxz, ryz⟩ := hL.rne
  have hap : ∀ x ∈ [L.R.x, L.R.y, L.R.z], ∀ y ∈ [L.R.x, L.R.y, L.R.z], x ≠ y →
      x + 8 * L.M.n ≤ y ∨ y + 8 * L.M.n ≤ x := fun x hx y hy hxy =>
    hL.lay.apart x y (ladPts_slots L x (by simp only [List.mem_cons] at hx ⊢; rcases hx with h | h | h | h <;> simp [h]))
      (ladPts_slots L y (by simp only [List.mem_cons] at hy ⊢; rcases hy with h | h | h | h <;> simp [h])) hxy
  have sR := selPt_conds (a := L.R) hk3 hk6 hsz rx ry rz
  refine VG.Proof.X25519.Arm.WP.append (selPt_ok hs₆ _ c₆ (n := L.M.n) (o := L.R)
    (a := ptAt L.M.n (Impl.Weierstrass.Point.pAt L.M.n)) (b := ptAt L.M.n (Impl.Weierstrass.Point.oAt L.M.n))
    sR.1
    ⟨hap L.R.x (by simp) L.R.y (by simp) rxy, hap L.R.x (by simp) L.R.z (by simp) rxz,
      hap L.R.y (by simp) L.R.z (by simp) ryz⟩
    sR.2)
    fun s₇ ⟨ex, ey, ez, k₇, O₇⟩ => ?_
  simp only [ptAt] at ex ey ez
  rw [hm₆] at ex ey ez
  have r11₇ : s₇.gpr .r11 = BitVec.ofNat 32 (j - 1) := by rw [k₇.gpr _ (by decide), k₆.gpr _ (by decide), r11₅]
  have U₅₇ : Unch base [(L.R.x, 8 * L.M.n), (L.R.y, 8 * L.M.n), (L.R.z, 8 * L.M.n)] s₅.mem s₇.mem := by
    rw [← hm₆]; exact Outs.unch O₇
  refine wp_testCounter (by omega_arith) r11₇ fun s₈ f₈ z₈ => WP.block_nil ⟨⟨?_, by rw [f₈.gpr, r11₇], ?_, ?_, ?_, ?_, ?_, ?_⟩, z₈⟩
  · exact (hs₆.of_rest k₇ (by decide)).of_rest (f₈.rest []) (by decide)
  · exact (hI.keep.trans K₅).trans ((k₆.mono (by simp [powClob, clob])).trans
      ((k₇.mono (by simp [powClob, clob])).trans (f₈.rest _)))
  · rw [f₈.mem]
    exact (hU₅.trans U₅₇).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hw
      · exact List.mem_append_left _ (List.mem_append_left _ (mem_ladW_R w hw))
  · rw [f₈.mem]
    have hmo := hL.lay.mo
    have mx := hmo L.R.x (ladPts_slots L _ (by simp))
    have my := hmo L.R.y (ladPts_slots L _ (by simp))
    have mz := hmo L.R.z (ladPts_slots L _ (by simp))
    have hpm := hP.mo
    exact hI.mod.unch (U₁₅.trans U₅₇) (by apart_ranges) (by have := hI.scr.nowrap; omega_arith)
  · rw [f₈.mem]
    intro x hx
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
  · have hq := hstep (j - 1) (by omega_arith) _ _ _ _ _ _ _ _ _ (by rw [Nat.sub_add_cancel hj]; exact hI.q) E₃.symm E₅.symm
    have hx : tmv C L.M.n base s₈ L.R.x = if k.testBit (j - 1) then
        toM C.p (2 ^ (64 * L.M.n)) (wordsVal s₅.mem base (Impl.Weierstrass.Point.oAt L.M.n) L.M.n) else
        toM C.p (2 ^ (64 * L.M.n)) (wordsVal s₃.mem base (Impl.Weierstrass.Point.oAt L.M.n) L.M.n) := by
      show toM _ _ _ = _
      rw [f₈.mem, ex]; split
      · rfl
      · rw [p5x]
    have hy : tmv C L.M.n base s₈ L.R.y = if k.testBit (j - 1) then
        toM C.p (2 ^ (64 * L.M.n)) (wordsVal s₅.mem base
          (Impl.Weierstrass.Point.oAt L.M.n + Impl.Weierstrass.Point.elemBytes L.M.n) L.M.n) else
        toM C.p (2 ^ (64 * L.M.n)) (wordsVal s₃.mem base
          (Impl.Weierstrass.Point.oAt L.M.n + Impl.Weierstrass.Point.elemBytes L.M.n) L.M.n) := by
      show toM _ _ _ = _
      rw [f₈.mem, ey]; split
      · rfl
      · rw [p5y]
    have hz : tmv C L.M.n base s₈ L.R.z = if k.testBit (j - 1) then
        toM C.p (2 ^ (64 * L.M.n)) (wordsVal s₅.mem base
          (Impl.Weierstrass.Point.oAt L.M.n + 2 * Impl.Weierstrass.Point.elemBytes L.M.n) L.M.n) else
        toM C.p (2 ^ (64 * L.M.n)) (wordsVal s₃.mem base
          (Impl.Weierstrass.Point.oAt L.M.n + 2 * Impl.Weierstrass.Point.elemBytes L.M.n) L.M.n) := by
      show toM _ _ _ = _
      rw [f₈.mem, ez]; split
      · rfl
      · rw [p5z]
    rw [hx, hy, hz]
    exact hq
  · rw [f₈.mem]
    exact cp₅.keep hk3 hk6 U₅₇ (by apart_ranges)

/-- `Q 0` accepts what `R` holds at the end, if `Q L.nbits` accepts what it
holds at the start and an iteration keeps `Q` (`Step`), for the scalar `k`
whose bits are the table at `L.bits`; only `powClob` and `ladWp` change. As
`ladder_ok`, for the slots below the point functions' (`LadPt`) if it calls
them. -/
theorem ladderP_ok {k : Nat} {Q : Nat → Spec.Weierstrass.Fe C → Spec.Weierstrass.Fe C → Spec.Weierstrass.Fe C → Prop}
    (hL : LadLay L size 8192) (hW : LadWk L size wk) {S : Impl.Weierstrass.Mont.Modulus}
    (hF : FnOk L.M wk S C.p) (hP : L.M.n ≤ 6 → LadPt L) (hp : UnitMod C.p (2 ^ (64 * L.M.n)))
    (hb8 : L.bits < 8192) {s : State} (hs : Scr s base size) (hf : Far s base 8192)
    (hM : ModOkW L.M size C.p s.mem base) (hlt : ∀ x ∈ ladR L, wordsVal s.mem base x L.M.n < C.p)
    {a0 : Bool} (ha0 : a0 = true → L.M.n ≤ 6) (hstep : Step L C base s k Q a0)
    (hR : Q L.nbits (tmv C L.M.n base s L.R.x) (tmv C L.M.n base s L.R.y) (tmv C L.M.n base s L.R.z))
    (hbits : ∀ t < L.nbits, s.mem (off base (L.bits + t)) = if k.testBit t then 1 else 0)
    (henc : encodable (BitVec.ofNat 32 L.nbits) = true) {u : Bool} :
    WP isa (ladderP L S a0 u) s fun s' => Rest powClob s s' ∧ Unch base (ladWp L wk) s.mem s'.mem ∧
      ModOkW L.M size C.p s'.mem base ∧
      (∀ x ∈ [L.R.x, L.R.y, L.R.z], wordsVal s'.mem base x L.M.n < C.p) ∧
      Q 0 (tmv C L.M.n base s' L.R.x) (tmv C L.M.n base s' L.R.y) (tmv C L.M.n base s' L.R.z) := by
  unfold ladderP ladWp ptW
  by_cases hk6 : L.M.n ≤ 6
  swap
  · simp only [hk6, ↓reduceIte, List.append_nil]
    cases a0
    swap; · exact absurd (ha0 rfl) hk6
    exact ladder_ok hL hW hF hp hb8 hs hf hM hlt hstep hR hbits henc
  simp only [hk6, ↓reduceIte]
  have hPt := hP hk6
  have hM' : Mont.ModOk L.M.n C.p := by have h := hF.ok; rw [hF.k, hF.m] at h; exact h
  have hk3 := hM'.n3
  have hl := lay_nums hk3 hk6
  have hwk := hF.wk
  have hown := own_le L.M.n hM'.n9
  have hsz : size = 4096 := by have := hW.le; have := hs.small; omega_arith
  have hn := hs.nowrap
  have rx : L.R.x + 8 * L.M.n ≤ Impl.Weierstrass.Point.oAt L.M.n := hPt.sl _ (ladPts_slots L _ (by simp))
  have ry : L.R.y + 8 * L.M.n ≤ Impl.Weierstrass.Point.oAt L.M.n := hPt.sl _ (ladPts_slots L _ (by simp))
  have rz : L.R.z + 8 * L.M.n ≤ Impl.Weierstrass.Point.oAt L.M.n := hPt.sl _ (ladPts_slots L _ (by simp))
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (ladderSetup_ok (base := base) (by simpa only [hsz] using hs) hk3 hk6 hPt)
    fun s₃ ⟨k₃, U₃, cp₃⟩ => ?_
  refine wp_mov (op2_imm henc) fun s₄ u₄ => WP.block_nil ?_
  have hm₄ : s₄.mem = s₃.mem := u₄.mem
  have U₁₃ : Unch base [(Impl.Weierstrass.Point.oAt L.M.n, 4096 - Impl.Weierstrass.Point.oAt L.M.n)] s.mem s₄.mem := by
    rw [hm₄]; exact U₃
  have K₄ : Rest powClob s s₄ := (k₃.mono (by simp [powClob, clob])).trans (u₄.rest (by simp [powClob]))
  have low : ∀ {x}, x + 8 * L.M.n ≤ Impl.Weierstrass.Point.oAt L.M.n →
      wordsVal s₄.mem base x L.M.n = wordsVal s.mem base x L.M.n := fun hx =>
    U₁₃.wordsVal (by apart_ranges) (by omega_arith)
  refine countLoop_ok (Inv := fun j s' => LadInvP L wk C base size Q s s' j) (n := L.nbits)
    (fun j s' h1 h2 hi => ladderPBody_ok hL hW hF hk6 hPt hb8 hf (fun x hx => hlt x (mem_ladRo_ladR hx))
      hstep hbits h1 h2 hi)
    (fun s' hi => ⟨hi.keep, hi.unch, hi.mod, hi.lt, hi.q⟩) hL.nbits.1
    ⟨hs.of_rest K₄ (by decide), u₄.gpr, K₄, U₁₃.mono fun w hw => List.mem_append_right _ hw,
      hM.unch U₁₃ (by have := hPt.mo; apart_ranges) (by omega_arith), fun x hx => ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [low rx]; exact hlt _ (by simp [ladR])
    · rw [low ry]; exact hlt _ (by simp [ladR])
    · rw [low rz]; exact hlt _ (by simp [ladR])
  · show Q L.nbits (toM _ _ _) (toM _ _ _) (toM _ _ _)
    rw [low rx, low ry, low rz]
    exact hR
  · rw [hm₄]
    exact cp₃

end body

end VG.Proof.Weierstrass.Arm.Point

module

public import VerifiedGarbage.Proof.Weierstrass.Env
public import VerifiedGarbage.Impl.Weierstrass.Arm
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Weierstrass.Arm.MontFn
import VerifiedGarbage.Proof.Framework.Arm.Call

/-! ### `Weierstrass.Arm.MontCall`, which this module and modules that import it used -/

section

/-!
# Calls of the Montgomery arithmetic's functions, on 32-bit ARM

`callOp f body o a b` (`Impl/Weierstrass/Arm/Mont.lean`) calls the function
`f`, whose code is `body`, on the working space at `r12` and the offsets
`o`, `a` and `b`, keeping `lr` in `r10` (`callOp_ok`):
from a working space whose `8192` bytes are writable (`Far`), it changes only
the registers `clob` and `r10`, the number at `o` and the functions' own
working space (`CallKeep`), and does what `body` does. `mulCall_ok`, `addCall_ok` and
`subCall_ok` are the calls of `mulFn`, `addFn` and `subFn` (`MontFn.lean`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.Arm.Mont

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Weierstrass.Arm.Mont
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass.Arm
open VG.Proof.X25519.Arm (Rest Upd wp_mov wp_movw op2_reg)

/-- The registers a call changes: `clob` and `r10`, which keeps `lr`. -/
def callClob : List Reg := .r10 :: clob

/-- What a call writing `[o]` keeps: the registers but `callClob`, the
regions, the stack pointer, and the memory but `[o]` and the functions' own
working space. -/
structure CallKeep (n : Nat) (base : Addr) (o : Nat) (s s' : State) : Prop where
  rest : Rest callClob s s'
  mem : Outs base [(o, 8 * n), (own n, 64 * n)] s.mem s'.mem

/-- A call of `body`, which from the working space at `r12` and the offsets
`o`, `a` and `b` in `r1`–`r3` changes only `[o]` and its own working space,
preserves the callee-saved registers, leaves `r12` as the working space, and
relates the memory before and after by `V`. -/
theorem callOp_ok {f : String} {body : Prog isa} (hn : body.noCalls = true) {n : Nat} {s : State}
    {base : Addr} (hf : Far s base 8192) {o a b : Nat}
    {V : Mem → Mem → Prop}
    (hbody : ∀ t, t.rd = [] → t.wr = [⟨base, 8192⟩] → t.gpr .r0 = s.gpr .r12 →
      t.gpr .r1 = (BitVec.ofNat 16 o).setWidth 32 → t.gpr .r2 = (BitVec.ofNat 16 a).setWidth 32 →
      t.gpr .r3 = (BitVec.ofNat 16 b).setWidth 32 → t.mem = s.mem →
      WP isa body t fun t' => abiPreserved t t' ∧ Kept n base o t.mem t'.mem ∧ V t.mem t'.mem ∧
        t'.gpr .r12 = t.gpr .r0) :
    WP isa (callOp f body o a b) s fun s' => CallKeep n base o s s' ∧ V s.mem s'.mem := by
  rw [callOp]
  refine WP.seq (wp_mov (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_reg _ _) fun s₂ u₂ =>
    wp_movw fun s₃ u₃ => wp_movw fun s₄ u₄ => wp_movw fun s₅ u₅ => WP.block_nil ?_)
  have k₅ : Rest [.r10, .r0, .r1, .r2, .r3] s s₅ :=
    (u₁.rest (by simp)).trans <| (u₂.rest (by simp)).trans <| (u₃.rest (by simp)).trans <|
      (u₄.rest (by simp)).trans (u₅.rest (by simp))
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have g10 : s₅.gpr .r10 = s.gpr .lr := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  have g0 : s₅.gpr .r0 = s.gpr .r12 := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]
  have g1 : s₅.gpr .r1 = (BitVec.ofNat 16 o).setWidth 32 := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  have g2 : s₅.gpr .r2 = (BitVec.ofNat 16 a).setWidth 32 := by rw [u₅.other _ (by decide), u₄.gpr]
  have g3 : s₅.gpr .r3 = (BitVec.ofNat 16 b).setWidth 32 := u₅.gpr
  have hf₅ : Far s₅ base 8192 := hf.of_rest k₅
  have hcov : Covers [⟨base, 8192⟩] s₅.wr := by
    have h := hf₅.write (d := 0) (n := 8192) (by omega_using [])
    simp only [off, BitVec.add_zero] at h
    exact Covers.one h
  refine WP.seq (WP.call (k := ⟨fun t => t.rd = [] ∧ t.wr = [⟨base, 8192⟩] ∧ t.gpr .r0 = s.gpr .r12 ∧
      t.gpr .r1 = (BitVec.ofNat 16 o).setWidth 32 ∧ t.gpr .r2 = (BitVec.ofNat 16 a).setWidth 32 ∧
      t.gpr .r3 = (BitVec.ofNat 16 b).setWidth 32 ∧ t.mem = s.mem,
      fun t t' => Kept n base o t.mem t'.mem ∧ V t.mem t'.mem ∧ t'.gpr .r12 = t.gpr .r0, fun _ _ => True⟩)
    (fun t ⟨h1, h2, h3, h4, h5, h6, h7⟩ => by
      obtain ⟨tr, t', he, A, K, W, R⟩ := hbody t h1 h2 h3 h4 h5 h6 h7
      exact ⟨tr, t', he, A, K, W, R⟩)
    (rd := []) (wr := [⟨base, 8192⟩])
    ⟨rfl, rfl, by rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), g0],
      by rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), g1],
      by rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), g2],
      by rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), g3],
      by rw [State.withRegions_mem, State.callEntry_mem, m₅]⟩
    (Covers.right hcov) hcov ?_ hn)
  intro s₇ r₇ w₇ p₇ _ hp₇ _ ⟨K, W, R⟩
  simp only [State.withRegions_mem, State.callEntry_mem, m₅, State.withRegions_gpr] at K W R
  rw [State.callEntry_gpr _ (by decide), g0] at R
  refine wp_mov (op2_reg _ _) fun s₈ u₈ => WP.block_nil ?_
  have hm : s₈.mem = s₇.mem := u₈.mem
  refine ⟨⟨⟨fun r hr => ?_, by rw [u₈.rd, r₇, k₅.rd], by rw [u₈.wr, w₇, k₅.wr],
    by rw [u₈.sp, p₇, k₅.sp]⟩, by rw [hm]; exact K⟩, by rw [hm]; exact W⟩
  simp only [callClob, clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h10, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hr
  by_cases hlr : r = .lr
  · subst hlr
    rw [u₈.gpr, hp₇ _ (by decide) (by decide), g10]
  by_cases h12 : r = .r12
  · subst h12
    rw [u₈.other _ (by decide), R]
  have h11 : r = .r11 := by cases r <;> first | rfl | contradiction
  subst h11
  rw [u₈.other _ (by decide), hp₇ _ (by decide) (by decide), k₅.gpr _ (by decide)]

/-- The arguments of a call, as the functions' precondition has them. -/
theorem pre_of_call {n m : Nat} (hM : ModOk n m) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hf : Far s base 8192) {o a b : Nat} (ho : o + 8 * n ≤ own n) (ha : a + 8 * n ≤ own n)
    (hb : b + 8 * n ≤ own n) {t : State} (h1 : t.rd = []) (h2 : t.wr = [⟨base, 8192⟩])
    (h3 : t.gpr .r0 = s.gpr .r12) (h4 : t.gpr .r1 = (BitVec.ofNat 16 o).setWidth 32)
    (h5 : t.gpr .r2 = (BitVec.ofNat 16 a).setWidth 32) (h6 : t.gpr .r3 = (BitVec.ofNat 16 b).setWidth 32) :
    Pre n m t ∧ State.addr (t.gpr .r0) = base ∧ (t.gpr .r1).toNat = o ∧ (t.gpr .r2).toNat = a ∧
      (t.gpr .r3).toNat = b := by
  have hown := own_le n hM.n9
  have := hM.n3
  have e : ∀ x, x < 4096 → ((BitVec.ofNat 16 x).setWidth 32).toNat = x := fun x hx => by
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_using [hx]
  have hr0 : State.addr (t.gpr .r0) = base := by rw [h3]; exact hs.wb
  have ho' := e o (by omega_using [ho, hown, this])
  have ha' := e a (by omega_using [ha, hown, this])
  have hb' := e b (by omega_using [hb, hown, this])
  refine ⟨⟨h1, by rw [h2, hr0], ?_, by rw [h4, ho']; exact ho, by rw [h5, ha']; exact ha,
    by rw [h6, hb']; exact hb⟩, hr0, by rw [h4, ho'], by rw [h5, ha'], by rw [h6, hb']⟩
  rw [h3, hs.wb_toNat]; exact hf.nowrap

/-- `[o] = [a] [b] R⁻¹ mod m` by a call of `vg_<curve>_mul_mod_<p|n>`. -/
theorem mulCall_ok {S : Impl.Weierstrass.Mont.Modulus} (hM : ModOk S.k S.m) {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (hf : Far s base 8192) {o a b : Nat} (ho : o + 8 * S.k ≤ own S.k)
    (ha : a + 8 * S.k ≤ own S.k) (hb : b + 8 * S.k ≤ own S.k) (hB : wordsVal s.mem base b S.k < S.m)
    {u : Bool} :
    WP isa (mulCall S o a b u) s fun s' => CallKeep S.k base o s s' ∧
      wordsVal s'.mem base o S.k < S.m ∧
      wordsVal s'.mem base o S.k * 2 ^ (64 * S.k) % S.m =
        wordsVal s.mem base a S.k * wordsVal s.mem base b S.k % S.m :=
  callOp_ok (V := fun m m' => wordsVal m' base o S.k < S.m ∧
      wordsVal m' base o S.k * 2 ^ (64 * S.k) % S.m = wordsVal m base a S.k * wordsVal m base b S.k % S.m)
    (by unfold mulFnWith mulFnU mulFn; cases u <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> (try split) <;> rfl)
    hf fun t h1 h2 h3 h4 h5 h6 h7 => by
      obtain ⟨hp, e0, e1, e2, e3⟩ := pre_of_call hM hs hf ho ha hb h1 h2 h3 h4 h5 h6 (m := S.m)
      refine WP.mono (mulFnWith_ok u hM hp (by rw [e0, e3, h7]; exact hB)) fun t' ⟨A, K, ⟨V, C⟩, R⟩ => ?_
      rw [e0, e1, e2, e3] at *
      exact ⟨A, K, ⟨V, C⟩, R⟩

/-- `[o] = [a] + [b] mod m` by a call of `vg_<curve>_add_mod_<p|n>`. -/
theorem addCall_ok {S : Impl.Weierstrass.Mont.Modulus} (hM : ModOk S.k S.m) {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (hf : Far s base 8192) {o a b : Nat} (ho : o + 8 * S.k ≤ own S.k)
    (ha : a + 8 * S.k ≤ own S.k) (hb : b + 8 * S.k ≤ own S.k)
    (hAB : wordsVal s.mem base a S.k + wordsVal s.mem base b S.k < 2 * S.m) :
    WP isa (addCall S o a b) s fun s' => CallKeep S.k base o s s' ∧
      wordsVal s'.mem base o S.k = (wordsVal s.mem base a S.k + wordsVal s.mem base b S.k) % S.m :=
  callOp_ok (V := fun m m' => wordsVal m' base o S.k = (wordsVal m base a S.k + wordsVal m base b S.k) % S.m)
    rfl hf fun t h1 h2 h3 h4 h5 h6 h7 => by
      obtain ⟨hp, e0, e1, e2, e3⟩ := pre_of_call hM hs hf ho ha hb h1 h2 h3 h4 h5 h6 (m := S.m)
      refine WP.mono (addFn_ok hM hp (by rw [e0, e2, e3, h7]; exact hAB)) fun t' ⟨A, K, V, R⟩ => ?_
      rw [e0, e1, e2, e3] at *
      exact ⟨A, K, V, R⟩

/-- `[o] = [a] - [b] mod m` by a call of `vg_<curve>_sub_mod_<p|n>`. -/
theorem subCall_ok {S : Impl.Weierstrass.Mont.Modulus} (hM : ModOk S.k S.m) {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (hf : Far s base 8192) {o a b : Nat} (ho : o + 8 * S.k ≤ own S.k)
    (ha : a + 8 * S.k ≤ own S.k) (hb : b + 8 * S.k ≤ own S.k)
    (hA : wordsVal s.mem base a S.k < S.m) (hB : wordsVal s.mem base b S.k < S.m) :
    WP isa (subCall S o a b) s fun s' => CallKeep S.k base o s s' ∧
      wordsVal s'.mem base o S.k = (wordsVal s.mem base a S.k + S.m - wordsVal s.mem base b S.k) % S.m :=
  callOp_ok (V := fun m m' => wordsVal m' base o S.k = (wordsVal m base a S.k + S.m - wordsVal m base b S.k) % S.m)
    rfl hf fun t h1 h2 h3 h4 h5 h6 h7 => by
      obtain ⟨hp, e0, e1, e2, e3⟩ := pre_of_call hM hs hf ho ha hb h1 h2 h3 h4 h5 h6 (m := S.m)
      refine WP.mono (subFn_ok hM hp (by rw [e0, e2, h7]; exact hA) (by rw [e0, e3, h7]; exact hB))
        fun t' ⟨A, K, V, R⟩ => ?_
      rw [e0, e1, e2, e3] at *
      exact ⟨A, K, V, R⟩

end VG.Proof.Weierstrass.Arm.Mont

end

end

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

@[expose] public section

namespace VG.Proof.Weierstrass.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass VG.Proof.Mont.Arm
  VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

/-- The functions of `S` compute modulo `m` on numbers of `M.n` words, with
their own working space at `wk`. -/
structure FnOk (M : Mod) (wk : Nat) (S : Impl.Weierstrass.Mont.Modulus) (m : Nat) : Prop where
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
theorem ProgKeep.of_call {M : Mod} {base : Addr} {wk o : Nat} {S : Impl.Weierstrass.Mont.Modulus} {m : Nat}
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
  refine Outs.wordsVal h.mem (fun r hr => ?_) (by omega_using [hn, hy])
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
        subst hw; have := hL.mo w ho; omega_using [this]) hM.sep hW.mo]
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
theorem FnOk.fits {M : Mod} {wk : Nat} {S : Impl.Weierstrass.Mont.Modulus} {m : Nat} (hF : FnOk M wk S m)
    {x : Nat} (hx : x + 8 * M.n ≤ wk) : x + 8 * S.k ≤ Impl.Weierstrass.Arm.Mont.own S.k := by
  rw [hF.k, ← hF.wk]; exact hx

/-- The slots of an operation, in the functions' terms. -/
theorem fnSl {M : Mod} {size wk : Nat} {Sl : Nat → Prop} (hW : WkOk M size wk Sl)
    {S : Impl.Weierstrass.Mont.Modulus} {m : Nat} (hF : FnOk M wk S m) {x : Nat} (hx : Sl x) :
    x + 8 * S.k ≤ Impl.Weierstrass.Arm.Mont.own S.k :=
  hF.fits (hW.sl x hx)

/-- One operation. -/
theorem fop_ok {M : Mod} {base : Addr} {size m wk : Nat} [NeZero m] {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hW : WkOk M size wk Sl) {S : Impl.Weierstrass.Mont.Modulus} (hF : FnOk M wk S m)
    (hm : UnitMod m (2 ^ (64 * M.n))) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) {op : FOp} (hS : ∀ x ∈ op.out :: op.ins, Sl x)
    (hR : ∀ x ∈ op.ins, x ∈ V) {u : Bool} :
    WP isa (opCode S u op) s fun s' =>
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
        (by rw [hk, hmm]; omega_using [hA, hB]))
      fun s' ⟨K, heq⟩ => ?_
    rw [hk, hmm] at heq
    refine ⟨.of_call hF K, hI.update hL hW hS.1 (.of_call hF K) ?_ ?_⟩
    · rw [heq]; exact Nat.mod_lt _ (by omega_using [hA])
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
    · rw [heq]; exact Nat.mod_lt _ (by omega_using [hA])
    · rw [heq, toM_sub (by omega_using [hB]), hI.val a hR.1, hI.val b hR.2]

theorem progs_wp (p : Prog isa) (ps : List (Prog isa)) {s : State} {Q : State → Prop}
    (h : WP isa p s fun s' => WP isa (progs ps) s' Q) : WP isa (progs (p :: ps)) s Q := by
  cases ps with
  | nil => exact WP.mono h fun _ h' => WP.block_nil_iff.mp h'
  | cons p' ps' => exact WP.seq h

/-- A field program. -/
theorem fprog_ok {M : Mod} {base : Addr} {size m wk : Nat} [NeZero m] {Sl : Nat → Prop} (hL : Lay M size Sl)
    (hW : WkOk M size wk Sl) {S : Impl.Weierstrass.Mont.Modulus} (hF : FnOk M wk S m)
    (hm : UnitMod m (2 ^ (64 * M.n))) {u : Bool} :
    ∀ (ops : List FOp) {V : List Nat} {E : Nat → Fin m} {s : State},
      Inv M base size m Sl V E s → (∀ op ∈ ops, ∀ x ∈ op.out :: op.ins, Sl x) →
      readsOk ops V = true →
      WP isa (fprog S ops u) s fun s' => ProgKeep M base wk (ops.map FOp.out) s s' ∧
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
    (hW : WkOk M size wk Sl) {S' : Impl.Weierstrass.Mont.Modulus} (hF : FnOk M wk S' m)
    (hm : UnitMod m (2 ^ (64 * M.n))) {S : RcbSlots} {p q o : Pt}
    (hA : RcbApart S p q o)
    (hSl : ∀ x ∈ rcbW S o ++ rcbR S p q, Sl x) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) (hV : ∀ x ∈ rcbR S p q, x ∈ V) {u : Bool} :
    WP isa (fprog S' (rcb S p q o) u) s fun s' => ProgKeep M base wk (rcbW S o) s s' ∧
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

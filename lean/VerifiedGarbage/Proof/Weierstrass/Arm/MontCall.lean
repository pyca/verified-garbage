import VerifiedGarbage.Proof.Weierstrass.Arm.MontFn
import VerifiedGarbage.Proof.Framework.Arm.Call

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
    have h := hf₅.write (d := 0) (n := 8192) (by omega)
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
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  have hr0 : State.addr (t.gpr .r0) = base := by rw [h3]; exact hs.wb
  have ho' := e o (by omega)
  have ha' := e a (by omega)
  have hb' := e b (by omega)
  refine ⟨⟨h1, by rw [h2, hr0], ?_, by rw [h4, ho']; exact ho, by rw [h5, ha']; exact ha,
    by rw [h6, hb']; exact hb⟩, hr0, by rw [h4, ho'], by rw [h5, ha'], by rw [h6, hb']⟩
  rw [h3, hs.wb_toNat]; exact hf.nowrap

/-- `[o] = [a] [b] R⁻¹ mod m` by a call of `vg_<curve>_mul_mod_<p|n>`. -/
theorem mulCall_ok {S : Spec.Weierstrass.Mont.Modulus} (hM : ModOk S.k S.m) {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (hf : Far s base 8192) {o a b : Nat} (ho : o + 8 * S.k ≤ own S.k)
    (ha : a + 8 * S.k ≤ own S.k) (hb : b + 8 * S.k ≤ own S.k) (hB : wordsVal s.mem base b S.k < S.m) :
    WP isa (mulCall S o a b) s fun s' => CallKeep S.k base o s s' ∧
      wordsVal s'.mem base o S.k < S.m ∧
      wordsVal s'.mem base o S.k * 2 ^ (64 * S.k) % S.m =
        wordsVal s.mem base a S.k * wordsVal s.mem base b S.k % S.m :=
  callOp_ok (V := fun m m' => wordsVal m' base o S.k < S.m ∧
      wordsVal m' base o S.k * 2 ^ (64 * S.k) % S.m = wordsVal m base a S.k * wordsVal m base b S.k % S.m)
    rfl hf fun t h1 h2 h3 h4 h5 h6 h7 => by
      obtain ⟨hp, e0, e1, e2, e3⟩ := pre_of_call hM hs hf ho ha hb h1 h2 h3 h4 h5 h6 (m := S.m)
      refine WP.mono (mulFn_ok hM hp (by rw [e0, e3, h7]; exact hB)) fun t' ⟨A, K, ⟨V, C⟩, R⟩ => ?_
      rw [e0, e1, e2, e3] at *
      exact ⟨A, K, ⟨V, C⟩, R⟩

/-- `[o] = [a] + [b] mod m` by a call of `vg_<curve>_add_mod_<p|n>`. -/
theorem addCall_ok {S : Spec.Weierstrass.Mont.Modulus} (hM : ModOk S.k S.m) {s : State} {base : Addr} {size : Nat}
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
theorem subCall_ok {S : Spec.Weierstrass.Mont.Modulus} (hM : ModOk S.k S.m) {s : State} {base : Addr} {size : Nat}
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

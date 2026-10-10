import VerifiedGarbage.Proof.Weierstrass.Arm.MontCall
import VerifiedGarbage.Impl.Weierstrass.Arm.Point

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

namespace VG.Proof.Weierstrass.Arm.Point

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass.Arm.Mont
open VG.Impl.Weierstrass.Arm.Point
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass.Arm.Mont
open VG.Proof.X25519.Arm (Rest Upd wp_mov wp_movw op2_reg)

/-- A 16-bit immediate, as `movw` loads it. -/
theorem movw_toNat {c : Nat} (h : c < 2 ^ 16) : ((BitVec.ofNat 16 c).setWidth 32).toNat = c := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

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
    have h := hf₄.write (d := 0) (n := 8192) (by omega)
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
variable {enc : Nat → Nat} {S : Spec.Weierstrass.Mont.Modulus} (hM : ModOk S.k S.m) {s : State} {base : Addr}
  {size : Nat} (hs : Scr s base size) (hf : Far s base 8192) {o a b : Nat}
  (lo : enc o + 8 * S.k ≤ own S.k) (la : enc a + 8 * S.k ≤ own S.k) (lb : enc b + 8 * S.k ≤ own S.k)
include hM hs hf lo la lb

/-- `[o] = [a] [b] R⁻¹ mod m` by a call of `vg_<curve>_mul_mod_<p|n>`. -/
theorem mulCallR_ok (hB : wordsVal s.mem base (enc b) S.k < S.m) :
    WP isa (callR enc (S.fn "mul") (mulFn S.k S.m) o a b) s fun s' => CallKeepR S.k base (enc o) s s' ∧
      wordsVal s'.mem base (enc o) S.k < S.m ∧
      wordsVal s'.mem base (enc o) S.k * 2 ^ (64 * S.k) % S.m =
        wordsVal s.mem base (enc a) S.k * wordsVal s.mem base (enc b) S.k % S.m :=
  callR_ok (V := fun m m' => wordsVal m' base (enc o) S.k < S.m ∧
      wordsVal m' base (enc o) S.k * 2 ^ (64 * S.k) % S.m = wordsVal m base (enc a) S.k * wordsVal m base (enc b) S.k % S.m)
    rfl hf (by have := own_le S.k hM.n9; omega) (by have := own_le S.k hM.n9; omega)
    (by have := own_le S.k hM.n9; omega) fun t h1 h2 h3 h4 h5 h6 h7 => by
      obtain ⟨hp, e0⟩ := pre_of_callR hs hf lo la lb h1 h2 h3 h4 h5 h6 (m := S.m)
      refine WP.mono (mulFn_ok hM hp (by rw [e0, h6, h7]; exact hB)) fun t' ⟨A, K, ⟨V, C⟩, R⟩ => ?_
      rw [e0, h4, h5, h6] at *
      exact ⟨A, K, ⟨V, C⟩, R⟩

/-- `[o] = [a] + [b] mod m` by a call of `vg_<curve>_add_mod_<p|n>`. -/
theorem addCallR_ok (hAB : wordsVal s.mem base (enc a) S.k + wordsVal s.mem base (enc b) S.k < 2 * S.m) :
    WP isa (callR enc (S.fn "add") (addFn S.k S.m) o a b) s fun s' => CallKeepR S.k base (enc o) s s' ∧
      wordsVal s'.mem base (enc o) S.k = (wordsVal s.mem base (enc a) S.k + wordsVal s.mem base (enc b) S.k) % S.m :=
  callR_ok (V := fun m m' => wordsVal m' base (enc o) S.k = (wordsVal m base (enc a) S.k + wordsVal m base (enc b) S.k) % S.m)
    rfl hf (by have := own_le S.k hM.n9; omega) (by have := own_le S.k hM.n9; omega)
    (by have := own_le S.k hM.n9; omega) fun t h1 h2 h3 h4 h5 h6 h7 => by
      obtain ⟨hp, e0⟩ := pre_of_callR hs hf lo la lb h1 h2 h3 h4 h5 h6 (m := S.m)
      refine WP.mono (addFn_ok hM hp (by rw [e0, h5, h6, h7]; exact hAB)) fun t' ⟨A, K, V, R⟩ => ?_
      rw [e0, h4, h5, h6] at *
      exact ⟨A, K, V, R⟩

/-- `[o] = [a] - [b] mod m` by a call of `vg_<curve>_sub_mod_<p|n>`. -/
theorem subCallR_ok (hA : wordsVal s.mem base (enc a) S.k < S.m) (hB : wordsVal s.mem base (enc b) S.k < S.m) :
    WP isa (callR enc (S.fn "sub") (subFn S.k S.m) o a b) s fun s' => CallKeepR S.k base (enc o) s s' ∧
      wordsVal s'.mem base (enc o) S.k = (wordsVal s.mem base (enc a) S.k + S.m - wordsVal s.mem base (enc b) S.k) % S.m :=
  callR_ok (V := fun m m' => wordsVal m' base (enc o) S.k = (wordsVal m base (enc a) S.k + S.m - wordsVal m base (enc b) S.k) % S.m)
    rfl hf (by have := own_le S.k hM.n9; omega) (by have := own_le S.k hM.n9; omega)
    (by have := own_le S.k hM.n9; omega) fun t h1 h2 h3 h4 h5 h6 h7 => by
      obtain ⟨hp, e0⟩ := pre_of_callR hs hf lo la lb h1 h2 h3 h4 h5 h6 (m := S.m)
      refine WP.mono (subFn_ok hM hp (by rw [e0, h5, h7]; exact hA) (by rw [e0, h6, h7]; exact hB))
        fun t' ⟨A, K, V, R⟩ => ?_
      rw [e0, h4, h5, h6] at *
      exact ⟨A, K, V, R⟩

end

end VG.Proof.Weierstrass.Arm.Point

module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointMul
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Verify
import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointScalar
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointPowers
import VerifiedGarbage.Proof.X25519.PPC64LE.Instr
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.Scalar
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Encode
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Packed
import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarReduce
import VerifiedGarbage.Proof.Ed25519.Decode
public import VerifiedGarbage.Proof.X25519.PPC64LE.Field
import VerifiedGarbage.Proof.X25519.PPC64LE.Pass
import VerifiedGarbage.Proof.X25519.PPC64LE.Freeze
import VerifiedGarbage.Proof.X25519.Field
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Field
public import VerifiedGarbage.Proof.Ed25519.RecoverResult
import VerifiedGarbage.Proof.X25519.PPC64LE.Bits
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Recover
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Freeze
import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Ed25519.Recover
import VerifiedGarbage.Proof.X25519.Invert

/-! ### `Ed25519.PPC64LE.Decode`, which this module and modules that import it used -/

section

/-! ### `Ed25519.PPC64LE.RecoverCand`, which this module and modules that import it used -/

section

/-!
# Ed25519 on PPC64LE: the candidate `x` of a decoding

`rootPower_ok`: slot 15 is `z^((p - 5) / 8)` for `z` in slot 2, by a call of
`vg_gf25519_r32_pow250`, two squarings and a product. `recoverCandidate_ok`:
from `y` in slot 1, `u = y² - 1` in slot 6, `v = d y² + 1` in slot 7, the
candidate `x = u v³ (u v⁷)^((p - 5) / 8)` (`rootX`) in slot 0, `v x²` in slot
11 and `-u` in slot 12, as `recoverX` computes them.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.X25519 (P)
open VG.Proof.Ed25519 (rootU rootV rootX)

theorem root_exp : (2 ^ 250 - 1) * 2 ^ 2 + 1 = (P - 5) / 8 := by decide

section
variable {b : Addr}

/-- **`z^((p - 5) / 8)`** of slot 2, into slot 15; slots 0–13 kept. -/
theorem rootPower_ok {s : State} (hc : Ctx8 b s) :
    WP isa rootPower s fun t => Keep b s t ∧
      env t.mem b 15 = Spec.X25519.pow (env s.mem b 2) ((P - 5) / 8) ∧
      ∀ i : Slot, i.val < 14 → env t.mem b i = env s.mem b i := by
  unfold Impl.Ed25519.PPC64LE.rootPower
  refine WP.seq (WP.mono (power250_ok hc) fun t1 ⟨k1, e15, _, ek⟩ => ?_)
  have hc1 : Ctx8 b t1 := hc.of_keep k1
  refine WP.seq (WP.mono (sqnLoop_ok hc1.ctx 15 (by decide) (n := 2) (by decide) (by decide))
    fun t2 ⟨r2, f2, e2⟩ => ?_)
  have hc2 : Ctx8 b t2 := hc1.of_rest r2 (by decide)
  refine WP.mono (mulCall_ok hc2.ctx 15 15 2) fun t3 ⟨k3, e3⟩ => ⟨?_, ?_, fun i hi => ?_⟩
  · refine k1.trans (Keep.trans ⟨r2.mono (by decide), f2.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩⟩ k3)
    rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_using []) (by omega_using [])
  · have hz : env t1.mem b 2 = env s.mem b 2 := ek 2 (by decide)
    rw [e3, Function.update_self, e2, Function.update_self, Function.update_of_ne (by decide), e15, hz,
      Proof.X25519.sqn_pw]
    conv => lhs; arg 2; rw [← Proof.X25519.pw_one (env s.mem b 2)]
    rw [Proof.X25519.pw_mul, root_exp, Proof.X25519.pow_pw]
  · have h15 : i ≠ 15 := fun h => by subst h; exact absurd hi (by decide)
    rw [e3, Function.update_of_ne h15, e2, Function.update_of_ne h15, ek i hi]

/-- The slots `recoverInitOps` computes from `y` in slot 1. -/
theorem recoverInit_eval (e : Env) :
    evalOps recoverInitOps e 1 = e 1 ∧ evalOps recoverInitOps e 6 = rootU (e 1) ∧
      evalOps recoverInitOps e 7 = rootV (e 1) ∧
      evalOps recoverInitOps e 9 = Spec.X25519.pow (rootV (e 1)) 3 ∧
      evalOps recoverInitOps e 2 = rootU (e 1) * Spec.X25519.pow (rootV (e 1)) 7 := by
  refine ⟨rfl, rfl, rfl, (Proof.Ed25519.pow_three _ : _ = _), ?_⟩
  rw [← Proof.Ed25519.pow_seven]
  rfl

theorem recoverFinish_eval (e : Env) :
    evalOps recoverFinishOps e 0 = e 6 * e 9 * e 15 ∧ evalOps recoverFinishOps e 6 = e 6 ∧
      evalOps recoverFinishOps e 7 = e 7 ∧ evalOps recoverFinishOps e 1 = e 1 ∧
      evalOps recoverFinishOps e 11 = e 7 * (e 6 * e 9 * e 15) * (e 6 * e 9 * e 15) ∧
      evalOps recoverFinishOps e 12 = 0 - e 6 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The candidate**, for `y` in slot 1. -/
theorem recoverCandidate_ok {s : State} (hc : Ctx8 b s) :
    WP isa recoverCandidate s fun t => Keep b s t ∧
      env t.mem b 0 = rootX (env s.mem b 1) ∧ env t.mem b 1 = env s.mem b 1 ∧
      env t.mem b 6 = rootU (env s.mem b 1) ∧ env t.mem b 7 = rootV (env s.mem b 1) ∧
      env t.mem b 11 = rootV (env s.mem b 1) * rootX (env s.mem b 1) * rootX (env s.mem b 1) ∧
      env t.mem b 12 = 0 - rootU (env s.mem b 1) := by
  unfold recoverCandidate
  refine WP.seq (WP.mono (fieldCode_ok _ hc.ctx) fun s1 ⟨k1, e1⟩ => ?_)
  obtain ⟨a1, au, av, av3, a2⟩ := recoverInit_eval (env s.mem b)
  rw [← e1] at a1 au av av3 a2
  have hc1 : Ctx8 b s1 := hc.of_keep k1
  refine WP.seq (WP.mono (rootPower_ok hc1) fun s2 ⟨k2, e15, ek⟩ => ?_)
  have hc2 : Ctx8 b s2 := hc1.of_keep k2
  refine WP.mono (fieldCode_ok _ hc2.ctx) fun t ⟨k3, e3⟩ => ?_
  obtain ⟨f0, f6, f7, f1, f11, f12⟩ := recoverFinish_eval (env s2.mem b)
  rw [← e3] at f0 f6 f7 f1 f11 f12
  have bx : env s2.mem b 6 * env s2.mem b 9 * env s2.mem b 15 = rootX (env s.mem b 1) := by
    rw [ek 6 (by decide), ek 9 (by decide), e15, a2, au, av3]
    rfl
  refine ⟨k1.trans (k2.trans k3), by rw [f0, bx], by rw [f1, ek 1 (by decide), a1], ?_, ?_, ?_, ?_⟩
  · rw [f6, ek 6 (by decide), au]
  · rw [f7, ek 7 (by decide), av]
  · rw [f11, bx, ek 7 (by decide), av]
  · rw [f12, ek 6 (by decide), au]

end

end VG.Proof.Ed25519.PPC64LE

end

end

/-! ### `Ed25519.PPC64LE.FieldTest`, which this module and modules that import it used -/

section

/-!
# Ed25519 on PPC64LE: testing elements

`wordsZero o` leaves `r5` zero exactly when the eight words at `o` are
(`wordsZero_ok`), and `wordsEqual a b` exactly when those at `a` and `b`
agree (`wordsEqual_ok`). With `freeze`, `fieldZero a` tests the element of
slot `a` (`fieldZero_ok`), and `fieldEqual a c` whether the elements of
slots `a` and `c` are equal (`fieldEqual_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.X25519 (P)

/-- Limbs below `2³²` are all zero exactly when their value is. -/
theorem val32_eq_zero {f : Nat → Nat} {n : Nat} (hf : ∀ k < n, f k < 2 ^ 32) :
    val32 f n = 0 ↔ ∀ k < n, f k = 0 := by
  refine ⟨fun h k hk => ?_, fun h => ?_⟩
  · rw [← val32_div hf hk, h, Nat.zero_div, Nat.zero_mod]
  · rw [val32_congr (g := fun _ => 0) h, val32_zero_fn]

/-- Limbs below `2³²` agree exactly when their values do. -/
theorem val32_eq_iff {f g : Nat → Nat} {n : Nat} (hf : ∀ k < n, f k < 2 ^ 32) (hg : ∀ k < n, g k < 2 ^ 32) :
    val32 f n = val32 g n ↔ ∀ k < n, f k = g k := by
  refine ⟨fun h k hk => ?_, val32_congr⟩
  rw [← val32_div hf hk, h, val32_div hg hk]

/-- The sum of the first `k` values of `f`. -/
def psum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => psum f k + f k

theorem psum_le {f : Nat → Nat} (hf : ∀ k, f k < 2 ^ 32) : ∀ k, psum f k ≤ k * 2 ^ 32
  | 0 => Nat.le_refl _
  | k + 1 => by
    have := psum_le hf k
    have := hf k
    simp only [psum, Nat.succ_mul]
    omega_arith

theorem psum_eq_zero {f : Nat → Nat} : ∀ {k : Nat}, psum f k = 0 ↔ ∀ j < k, f j = 0
  | 0 => by simp [psum]
  | k + 1 => by
    rw [psum, Nat.add_eq_zero_iff, psum_eq_zero]
    exact ⟨fun ⟨h1, h2⟩ j hj => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      exacts [h1 j hj, h2], fun h => ⟨fun j hj => h j (by omega_using [hj]), h k (by omega_using [])⟩⟩

theorem wp_or {s : State} {is : List Instr} {Q : State → Prop} {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ||| s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .or d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

section
variable {b : Addr}

theorem wordsZero_ok {s : State} (hc : Ctx b s) {o : Nat} (ho : o + 32 ≤ 4096) :
    WP isa (.block (wordsZero o)) s fun t =>
      Rest [.r5, .r7] s t ∧ t.mem = s.mem ∧ (t.gpr .r5 = 0 ↔ V s.mem b o = 0) := by
  unfold wordsZero
  simp only [List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s1 u1 => ?_
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8)
    (fun k t => Rest [.r5, .r7] s t ∧ t.mem = s.mem ∧ (t.gpr .r5).toNat = psum (limb s.mem b o) k)
    (fun k t hk ⟨hr, hm, h5⟩ => ?_) 8 (Nat.le_refl _) s1
    ⟨u1.rest (by decide), u1.mem, by rw [u1.gpr]; rfl⟩) fun t ⟨hr, hm, h5⟩ => ⟨hr, hm, ?_⟩
  · have ht : Ctx b t := hc.of_rest hr (by decide)
    unfold sumLimb
    refine lw0_ok ht (d := o + 4 * k) (by omega_using [ho, hk]) fun s2 u2 => wp_add fun s3 u3 => WP.block_nil ⟨?_, ?_, ?_⟩
    · exact hr.trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
    · rw [u3.mem, u2.mem, hm]
    · have hle := psum_le (fun j => limb_lt s.mem b o j) k
      have hl := limb_lt s.mem b o k
      have e7 : (s2.gpr .r7).toNat = limb s.mem b o k := by rw [u2.gpr, toNat_ext32, hm]; rfl
      rw [u3.gpr, u2.other _ (by decide), toNat_add_lt (by rw [h5, e7]; omega_using [hk, hle, hl]), h5, e7]
      rfl
  · have hz : t.gpr .r5 = 0 ↔ (t.gpr .r5).toNat = 0 :=
      ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq (by rw [h]; rfl)⟩
    rw [hz, h5, psum_eq_zero, V, val32_eq_zero fun k _ => limb_lt _ _ _ _]

theorem wordsEqual_ok {s : State} (hc : Ctx b s) {a c : Nat} (ha : a + 32 ≤ 4096) (hc' : c + 32 ≤ 4096) :
    WP isa (.block (wordsEqual a c)) s fun t =>
      Rest [.r5, .r7, .r8] s t ∧ t.mem = s.mem ∧ (t.gpr .r5 = 0 ↔ V s.mem b a = V s.mem b c) := by
  unfold wordsEqual
  simp only [List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s1 u1 => ?_
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8)
    (fun k t => Rest [.r5, .r7, .r8] s t ∧ t.mem = s.mem ∧
      (t.gpr .r5 = 0 ↔ ∀ j < k, limb s.mem b a j = limb s.mem b c j))
    (fun k t hk ⟨hr, hm, h5⟩ => ?_) 8 (Nat.le_refl _) s1
    ⟨u1.rest (by decide), u1.mem, by rw [u1.gpr]; exact ⟨fun _ j hj => absurd hj (by omega_using []), fun _ => rfl⟩⟩)
    fun t ⟨hr, hm, h5⟩ => ⟨hr, hm, ?_⟩
  · have ht : Ctx b t := hc.of_rest hr (by decide)
    unfold equalLimb
    refine lw0_ok ht (d := a + 4 * k) (by omega_using [ha, hk]) fun s2 u2 => ?_
    have hc2 : Ctx b s2 := ht.of_rest (u2.rest (ws := [.r7]) (by decide)) (by decide)
    refine lw0_ok hc2 (d := c + 4 * k) (by omega_using [hc', hk]) fun s3 u3 => wp_xor fun s4 u4 => wp_or fun s5 u5 =>
      WP.block_nil ⟨?_, ?_, ?_⟩
    · exact hr.trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
        ((u4.rest (by decide)).trans (u5.rest (by decide)))))
    · rw [u5.mem, u4.mem, u3.mem, u2.mem, hm]
    · have m2 : s2.mem = s.mem := by rw [u2.mem, hm]
      have or0 : ∀ x y : BitVec 64, x ||| y = 0 ↔ x = 0 ∧ y = 0 := fun _ _ => BitVec.or_eq_zero_iff
      have xor0 : ∀ x y : BitVec 64, x ^^^ y = 0 ↔ x = y := fun _ _ => BitVec.xor_eq_zero_iff
      rw [u5.gpr, u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide), u4.gpr,
        u3.other _ (by decide), u2.gpr, u3.gpr, m2, hm, or0, xor0, h5]
      have e : ∀ x y : BitVec 32, x.setWidth 64 = y.setWidth 64 ↔ x.toNat = y.toNat := fun x y =>
        ⟨fun h => by rw [← toNat_ext32 x, ← toNat_ext32 y, h], fun h => by
          apply BitVec.eq_of_toNat_eq; rw [toNat_ext32, toNat_ext32, h]⟩
      rw [e]
      refine ⟨fun ⟨h1, h2⟩ j hj => ?_, fun h => ⟨fun j hj => h j (by omega_using [hj]), h k (by omega_using [])⟩⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      exacts [h1 j hj, h2]
  · rw [h5, V, V, val32_eq_iff (fun k _ => limb_lt _ _ _ _) (fun k _ => limb_lt _ _ _ _)]

theorem fieldZero_ok {s : State} (hc : Ctx b s) (a : Slot) :
    WP isa (fieldZero a) s fun t =>
      Rest [.r4, .r5, .r7, .r8, .r11] s t ∧ Frame [⟨b + BitVec.ofNat 64 FR, 64⟩] s.mem t.mem ∧
      (t.gpr .r5 = 0 ↔ V s.mem b (offset a) % P = 0) := by
  have hX := FR_eq
  unfold fieldZero
  refine WP.seq (WP.mono (freeze_ok hc a) fun s1 ⟨r1, f1, _, v1⟩ => ?_)
  refine WP.mono (wordsZero_ok (hc.of_rest r1 (by decide)) (o := FR) (by omega_using [hX])) fun t ⟨r2, m2, h2⟩ =>
    ⟨r1.trans (r2.mono (by decide)), (by rw [m2]; exact f1), (by rw [h2, v1])⟩

theorem fe_sub_eq_zero (x y : Spec.X25519.Fe) : x - y = 0 ↔ x = y := by
  rw [Fin.ext_iff, Fin.ext_iff, Fin.sub_def]
  have hx := x.isLt
  have hy := y.isLt
  show (P - y.val + x.val) % P = 0 ↔ _
  by_cases hxy : y.val ≤ x.val
  · rw [show P - y.val + x.val = (x.val - y.val) + P by omega_using [hxy], Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_using [])]
    omega_using [hxy]
  · rw [Nat.mod_eq_of_lt (by omega_using [hxy])]; omega_using [hxy]

theorem fieldEqual_ok {s : State} (hc : Ctx b s) (a c : Slot) :
    WP isa (fieldEqual a c) s fun t =>
      Keep b s t ∧ env t.mem b = evalOps [.sub 21 a c] (env s.mem b) ∧
      (t.gpr .r5 = 0 ↔ env s.mem b a = env s.mem b c) := by
  have hX := FR_eq
  unfold fieldEqual
  refine WP.seq (WP.mono (fieldCode_ok _ hc) fun s1 ⟨k1, e1⟩ => ?_)
  refine WP.mono (fieldZero_ok (k1.ctx hc) 21) fun t ⟨r2, f2, h2⟩ => ⟨⟨k1.rest.trans (r2.mono (by decide)),
    k1.frame.trans (f2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub b (by omega_using [hX]) (by omega_using [hX])⟩)⟩, ?_, ?_⟩
  · have ek : env t.mem b = env s1.mem b := funext fun i => env_keep f2 i fun r hr => by
      have := slot_range i
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_using [hX, this])) (by omega_using [this]) (by omega_using [hX])
    rw [ek, e1]
  · have e21 : env s1.mem b 21 = env s.mem b a - env s.mem b c := by
      rw [e1]; simp only [evalOps, List.foldl, evalOp, Function.update_self]
    rw [h2, ← fe_sub_eq_zero, ← e21, Fin.ext_iff]
    rfl

end

end VG.Proof.Ed25519.PPC64LE

end

end

/-! ### `Ed25519.PPC64LE.RecoverSign`, which this module and modules that import it used -/

section

/-!
# Ed25519 on PPC64LE: the sign and the checks of a decoding

A decoding's result is `r17`, 1 for a point (in slots 0–3) and 0 for none
(`DecodeResult`), and it writes `fclob`, `r17` and the field area (`DKeep`).
The sign it took from the encoding is the doubleword at `SIGN` (`SignAt`).
`recoverSign_ok`: from the candidate `x` in slot 0, `signResult`;
`recoverPoint_ok`: the checks of `v x²`, as `recoverResult`, which is the
spec's `recoverX` (`recoverResult_spec`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.X25519 (P)
open VG.Proof.Ed25519 (rootU rootV rootX recoveredPoint signedX signResult recoverResult)

/-- What a decoding writes. -/
structure DKeep (b : Addr) (s t : State) : Prop where
  rest : Rest (.r17 :: fclob) s t
  frame : Frame [FA b] s.mem t.mem

theorem DKeep.of_keep {b : Addr} {s t : State} (h : Keep b s t) : DKeep b s t :=
  ⟨h.rest.mono (by decide), h.frame⟩

theorem DKeep.trans {b : Addr} {s t u : State} (h : DKeep b s t) (k : DKeep b t u) : DKeep b s u :=
  ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩

/-- The result of a decoding. -/
def DecodeResult (b : Addr) (p : Option Spec.Ed25519.Point) (s : State) : Prop :=
  match p with
  | none => s.gpr .r17 = 0
  | some p => s.gpr .r17 = 1 ∧ point (env s.mem b) 0 1 2 3 = p

/-- The sign of the encoding, at `SIGN`. -/
def SignAt (b : Addr) (sg : Bool) (m : Mem) : Prop :=
  m.readW (b + BitVec.ofNat 64 SIGN) 64 = BitVec.ofNat 64 sg.toNat

theorem SignAt.frame {b : Addr} {sg : Bool} {m m' : Mem} (h : SignAt b sg m) (hf : Frame [FA b] m m') :
    SignAt b sg m' := by
  have hS : SIGN = 24 := rfl
  unfold SignAt
  rw [hf.readW (Region.contains_self _ _) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_using [hS])) (by omega_using [hS]) (by omega_using [])) (by decide)]
  exact h

/-- `ld t, off(n)`. -/
theorem wp_ldd {s : State} {is : List Instr} {Q : State → Prop} {t n : Reg} {off : Nat} {a : Addr}
    (hn : n ≠ .r0) (ho : off < 2 ^ 15 ∧ off % 4 = 0) (ha : s.gpr n + BitVec.ofNat 64 off = a)
    (hin : InRegions (s.rd ++ s.wr) a 8) (k : ∀ s', Upd s s' t (s.mem.readW a 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .d t n off :: is)) s Q := by
  refine WP.cons (s' := s.write t (s.mem.readW a 64)) ?_ (k _ (Upd.write _ _ _))
  rw [exec_load_d hn ho (by rw [ha]; exact hin), ha]

section
variable {b : Addr}

theorem frame_FR {m m' : Mem} (hf : Frame [⟨b + BitVec.ofNat 64 FR, 64⟩] m m') : Frame [FA b] m m' :=
  hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    rw [List.mem_singleton.mp hr]; exact Offset.sub b (by decide) (by decide)⟩

theorem env_FR {m m' : Mem} (hf : Frame [⟨b + BitVec.ofNat 64 FR, 64⟩] m m') : env m' b = env m b :=
  funext fun i => env_keep hf i fun r hr => by
    have := slot_range i
    have hX : FR = 864 := rfl
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_using [this, hX])) (by omega_using [this]) (by omega_using [hX])

theorem recoverInvalid_ok (s : State) :
    WP isa recoverInvalid s fun t => DKeep b s t ∧ t.mem = s.mem ∧ DecodeResult b none t :=
  wp_li (by decide) fun t u => WP.block_nil ⟨⟨u.rest (by decide), by rw [u.mem]; exact Frame.refl _ _⟩, u.mem,
    show t.gpr .r17 = 0 by rw [u.gpr]; rfl⟩

theorem recoverSuccess_ok {s : State} (hc : Ctx8 b s) :
    WP isa recoverSuccess s fun t => DKeep b s t ∧
      DecodeResult b (some (recoveredPoint (env s.mem b 0) (env s.mem b 1))) t := by
  unfold recoverSuccess
  refine WP.seq (WP.mono (fieldCode_ok _ hc.ctx) fun s1 ⟨k1, e1⟩ => ?_)
  refine wp_li (by decide) fun t u => WP.block_nil ⟨(DKeep.of_keep k1).trans
    ⟨u.rest (by decide), by rw [u.mem]; exact Frame.refl _ _⟩, u.gpr, ?_⟩
  rw [u.mem, e1]
  rfl

/-- A residue's parity is its low limb's. -/
theorem V_mod2' (m : Mem) (o : Nat) : V m b o % 2 = limb m b o 0 % 2 := by
  have h := val32_div (r := limb m b o) (n := 8) (fun k _ => limb_lt _ _ _ _) (k := 0) (by decide)
  rw [Nat.mul_zero, Nat.pow_zero, Nat.div_one] at h
  rw [V, ← h, Nat.mod_mod_of_dvd _ (by decide)]

theorem parity_ok {s : State} (hc : Ctx b s) {sg : Bool} (hs : SignAt b sg s.mem) :
    WP isa (.block recoverParity) s fun t =>
      Rest [.r5, .r7, .r8] s t ∧ t.mem = s.mem ∧ (t.gpr .r5 = 0 ↔ limb s.mem b FR 0 % 2 = sg.toNat) := by
  unfold recoverParity
  refine lw0_ok hc (d := FR) (by decide) fun s1 u1 => wp_lsl (by decide) fun s2 u2 => wp_lsr (by decide) fun s3 u3 => ?_
  have hc3 : Ctx b s3 := hc.of_rest ((u1.rest (ws := [.r7]) (by decide)).trans ((u2.rest (by decide)).trans
    (u3.rest (by decide)))) (by decide)
  have m3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  refine wp_ldd (a := b + BitVec.ofNat 64 SIGN) (by decide) (by decide) (by rw [hc3.r6])
    (hc3.inR (by decide)) fun s4 u4 => wp_xor fun s5 u5 => WP.block_nil ⟨?_, ?_, ?_⟩
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans (u5.rest (by decide)))))
  · rw [u5.mem, u4.mem, m3]
  · have e7 : (s4.gpr .r7).toNat = limb s.mem b FR 0 % 2 := by
      have hb := bit_shift (s1.gpr .r7) (j := 0) (by decide)
      rw [Nat.sub_zero, Nat.shiftRight_zero, Nat.and_one_is_mod] at hb
      rw [u4.other _ (by decide), u3.gpr, u2.gpr, hb, u1.gpr, toNat_ext32]
      rfl
    have e8 : s4.gpr .r8 = BitVec.ofNat 64 sg.toNat := by rw [u4.gpr, m3]; exact hs
    have xor0 : ∀ x y : BitVec 64, x ^^^ y = 0 ↔ x = y := fun _ _ => BitVec.xor_eq_zero_iff
    rw [u5.gpr, xor0, ← BitVec.toNat_inj, e7, e8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := sg.toNat) (by cases sg <;> decide)]

theorem sign_iff (v : Nat) (sg : Bool) : (((v % 2 == 1) == sg) = true) ↔ v % 2 = sg.toNat := by
  have := Nat.mod_lt v (show 0 < 2 by decide)
  cases sg <;> simp <;> omega

/-- The reduced `x`'s parity against the sign: `r5` zero exactly when they match. -/
theorem adjParity_ok {s : State} (hc : Ctx8 b s) {sg : Bool} (hs : SignAt b sg s.mem) :
    WP isa (.block (freeze 0 ++ recoverParity)) s fun t => DKeep b s t ∧ env t.mem b = env s.mem b ∧
      (t.gpr .r5 = 0 ↔ (((env s.mem b 0).val % 2 == 1) == sg) = true) := by
  refine WP.append (freeze_ok hc.ctx 0) fun s1 ⟨r1, f1, _, v1⟩ => ?_
  have hc1 : Ctx b s1 := hc.ctx.of_rest r1 (by decide)
  refine WP.mono (parity_ok hc1 (hs.frame (frame_FR f1))) fun s2 ⟨r2, m2, h2⟩ =>
    ⟨⟨r1.trans (r2.mono (by decide)) |>.mono (by decide), by rw [m2]; exact frame_FR f1⟩,
      by rw [m2, env_FR f1], ?_⟩
  have hp : limb s1.mem b FR 0 % 2 = (env s.mem b 0).val % 2 := by
    rw [← V_mod2', v1]; rfl
  rw [hp, ← sign_iff] at h2
  exact h2

/-- **The sign applied**, and the point. -/
theorem recoverAdjust_ok {s : State} (hc : Ctx8 b s) {sg : Bool} (hs : SignAt b sg s.mem) :
    WP isa recoverAdjustSign s fun t => DKeep b s t ∧
      DecodeResult b (some (recoveredPoint (signedX (env s.mem b 0) sg) (env s.mem b 1))) t := by
  unfold recoverAdjustSign
  refine WP.seq (WP.mono (adjParity_ok hc hs) fun s2 ⟨hk2, he2, h2⟩ => ?_)
  have hc2 : Ctx8 b s2 := hc.of_rest hk2.rest (by decide)
  refine WP.seq (WP.ite (s2.gpr .r5 == 0) (eval_zero s2 .r5) (fun h => ?_) (fun h => ?_))
  · refine WP.block_nil (WP.mono (recoverSuccess_ok hc2) fun t ⟨kt, dt⟩ => ⟨hk2.trans kt, ?_⟩)
    have hsg : signedX (env s.mem b 0) sg = env s.mem b 0 := by
      unfold signedX; rw [ite_eq_left (h2.mp (beq_iff_eq.mp h))]
    rw [hsg, ← he2]; exact dt
  · refine WP.mono (fieldCode_ok _ hc2.ctx) fun s3 ⟨k3, e3⟩ => ?_
    refine WP.mono (recoverSuccess_ok (hc2.of_keep k3)) fun t ⟨kt, dt⟩ => ⟨hk2.trans ((DKeep.of_keep k3).trans kt), ?_⟩
    have hsg : signedX (env s.mem b 0) sg = 0 - env s.mem b 0 := by
      unfold signedX
      exact ite_eq_right fun hq => absurd (beq_iff_eq.mpr (h2.mpr hq)) (by simpa using h)
    have hx : env s3.mem b 0 = 0 - env s.mem b 0 := by rw [e3, he2]; rfl
    have hy : env s3.mem b 1 = env s.mem b 1 := by rw [e3, he2]; rfl
    rw [hsg]; rw [hx, hy] at dt; exact dt

/-- **The sign**, for the candidate in slot 0 and `y` in slot 1. -/
theorem recoverSign_ok {s : State} (hc : Ctx8 b s) {sg : Bool} (hs : SignAt b sg s.mem) :
    WP isa recoverSign s fun t => DKeep b s t ∧
      DecodeResult b (signResult (env s.mem b 0) (env s.mem b 1) sg) t := by
  unfold recoverSign
  refine WP.seq (WP.mono (fieldZero_ok hc.ctx 0) fun s1 ⟨r1, f1, h1⟩ => ?_)
  have hc1 : Ctx8 b s1 := hc.of_rest r1 (by decide)
  have he1 : env s1.mem b = env s.mem b := env_FR f1
  have hk1 : DKeep b s s1 := ⟨r1.mono (by decide), frame_FR f1⟩
  have hs1 : SignAt b sg s1.mem := hs.frame (frame_FR f1)
  have hz : (env s.mem b 0 = 0) ↔ V s.mem b (offset 0) % P = 0 := by
    rw [Fin.ext_iff]; exact Iff.rfl
  rw [← hz] at h1
  have adj : WP isa recoverAdjustSign s1 fun t => DKeep b s t ∧
      DecodeResult b (some (recoveredPoint (signedX (env s.mem b 0) sg) (env s.mem b 1))) t :=
    WP.mono (recoverAdjust_ok hc1 hs1) fun t ⟨kt, dt⟩ => ⟨hk1.trans kt, by rw [he1] at dt; exact dt⟩
  refine WP.ite (s1.gpr .r5 == 0) (eval_zero s1 .r5) (fun h => ?_) (fun h => ?_)
  · have hx : env s.mem b 0 = 0 := h1.mp (beq_iff_eq.mp h)
    unfold signTest
    refine WP.seq (wp_ldd (a := b + BitVec.ofNat 64 SIGN) (by decide) (by decide) (by rw [hc1.r6])
      (hc1.ctx.inR (by decide)) fun s2 u2 => WP.block_nil ?_)
    have e5 : s2.gpr .r5 = BitVec.ofNat 64 sg.toNat := by rw [u2.gpr]; exact hs1
    have hc2 : Ctx8 b s2 := hc1.of_rest (u2.rest (ws := [.r5]) (by decide)) (by decide)
    have hk2 : DKeep b s1 s2 := ⟨u2.rest (by decide), by rw [u2.mem]; exact Frame.refl _ _⟩
    refine WP.ite (s2.gpr .r5 != 0) (eval_nonzero s2 .r5) (fun h' => ?_) (fun h' => ?_)
    · have hsg : sg = true := by
        cases sg with
        | false => rw [e5] at h'; exact absurd h' (by decide)
        | true => rfl
      refine WP.mono (recoverInvalid_ok s2) fun t ⟨kt, _, dt⟩ => ⟨hk1.trans (hk2.trans kt), ?_⟩
      unfold signResult; rw [hx, hsg]; exact dt
    · have hsg : sg = false := by
        cases sg with
        | false => rfl
        | true => rw [e5] at h'; exact absurd h' (by decide)
      refine WP.mono (recoverAdjust_ok hc2 (sg := sg) (by rw [u2.mem]; exact hs1)) fun t ⟨kt, dt⟩ =>
        ⟨hk1.trans (hk2.trans kt), ?_⟩
      have e2 : env s2.mem b = env s.mem b := by rw [u2.mem, he1]
      rw [e2] at dt
      subst hsg
      unfold signResult; rw [ite_eq_right (by simp)]; exact dt
  · refine WP.mono adj fun t ⟨kt, dt⟩ => ⟨kt, ?_⟩
    have hx : ¬ env s.mem b 0 = 0 := fun hx => absurd (beq_iff_eq.mpr (h1.mpr hx)) (by simpa using h)
    unfold signResult; rw [ite_eq_right (by simp [hx])]; exact dt

/-- **A candidate checked**, for `y` in slot 1: `recoverResult`. -/
theorem recoverPoint_ok {s : State} (hc : Ctx8 b s) {sg : Bool} (hs : SignAt b sg s.mem) :
    WP isa recoverPoint s fun t => DKeep b s t ∧ DecodeResult b (recoverResult (env s.mem b 1) sg) t := by
  unfold recoverPoint
  refine WP.seq (WP.mono (recoverCandidate_ok hc) fun a ⟨ka, ax, ay, au, _, avx, anu⟩ => ?_)
  have hca : Ctx8 b a := hc.of_keep ka
  refine WP.seq (WP.mono (fieldEqual_ok hca.ctx 11 6) fun c ⟨kc, ec, hc5⟩ => ?_)
  have hcc : Ctx8 b c := hca.of_keep kc
  have hkc : DKeep b s c := DKeep.of_keep (ka.trans kc)
  have hsc : SignAt b sg c.mem := hs.frame (ka.trans kc).frame
  have cx : env c.mem b 0 = rootX (env s.mem b 1) := by rw [ec, ← ax]; rfl
  have cy : env c.mem b 1 = env s.mem b 1 := by rw [ec, ← ay]; rfl
  rw [avx, au] at hc5
  refine WP.ite (c.gpr .r5 == 0) (eval_zero c .r5) (fun h => ?_) (fun h => ?_)
  · refine WP.mono (recoverSign_ok hcc hsc) fun t ⟨kt, dt⟩ => ⟨hkc.trans kt, ?_⟩
    unfold recoverResult; rw [ite_eq_left (hc5.mp (beq_iff_eq.mp h))]
    rw [cx, cy] at dt; exact dt
  · have hne : ¬ rootV (env s.mem b 1) * rootX (env s.mem b 1) * rootX (env s.mem b 1) = rootU (env s.mem b 1) :=
      fun he => absurd (beq_iff_eq.mpr (hc5.mpr he)) (by simpa using h)
    refine WP.seq (WP.mono (fieldEqual_ok hcc.ctx 11 12) fun d ⟨kd, ed, hd5⟩ => ?_)
    have hcd : Ctx8 b d := hcc.of_keep kd
    have hkd : DKeep b s d := hkc.trans (DKeep.of_keep kd)
    have hsd : SignAt b sg d.mem := hsc.frame kd.frame
    have c11 : env c.mem b 11 = env a.mem b 11 := by rw [ec]; rfl
    have c12 : env c.mem b 12 = env a.mem b 12 := by rw [ec]; rfl
    rw [c11, c12, avx, anu] at hd5
    refine WP.ite (d.gpr .r5 == 0) (eval_zero d .r5) (fun h' => ?_) (fun h' => ?_)
    · refine WP.seq (WP.mono (fieldCode_ok _ hcd.ctx) fun f ⟨kf, ef⟩ => ?_)
      refine WP.mono (recoverSign_ok (hcd.of_keep kf) (hsd.frame kf.frame)) fun t ⟨kt, dt⟩ =>
        ⟨hkd.trans ((DKeep.of_keep kf).trans kt), ?_⟩
      have fx : env f.mem b 0 = rootX (env s.mem b 1) * Spec.Ed25519.sqrtM1 := by
        rw [ef, ← cx, show env c.mem b 0 = env d.mem b 0 by rw [ed]; rfl]; rfl
      have fy : env f.mem b 1 = env s.mem b 1 := by
        rw [ef, ← cy, show env c.mem b 1 = env d.mem b 1 by rw [ed]; rfl]; rfl
      unfold recoverResult; rw [ite_eq_right hne, ite_eq_left (hd5.mp (beq_iff_eq.mp h'))]
      rw [fx, fy] at dt; exact dt
    · have hne' : ¬ rootV (env s.mem b 1) * rootX (env s.mem b 1) * rootX (env s.mem b 1) =
          0 - rootU (env s.mem b 1) :=
        fun he => absurd (beq_iff_eq.mpr (hd5.mpr he)) (by simpa using h')
      refine WP.mono (recoverInvalid_ok d) fun t ⟨kt, _, dt⟩ => ⟨hkd.trans kt, ?_⟩
      unfold recoverResult; rw [ite_eq_right hne, ite_eq_right hne']; exact dt

end

end VG.Proof.Ed25519.PPC64LE

end

end

/-!
# Ed25519 on PPC64LE: decoding a point

`pointDecode` with the encoding at `r14`: its words into slot 1, bit 255
split off to `SIGN` (`split_ok`), `y` canonical (`pointDecodeLoad_ok`), and
the recovery of `x` (`recoverPoint_ok`): `decodePoint` of the 32 bytes
(`pointDecode_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.X25519 (P)
open VG.Spec.Ed25519 (decodeLE bytesAt)

/-- What a decoding writes, with its sign. -/
structure DecKeep (b : Addr) (s t : State) : Prop where
  rest : Rest (.r17 :: fclob) s t
  frame : Frame [⟨b + BitVec.ofNat 64 SIGN, 8⟩, FA b] s.mem t.mem

theorem DecKeep.trans {b : Addr} {s t u : State} (h : DecKeep b s t) (k : DecKeep b t u) : DecKeep b s u :=
  ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩

theorem DecKeep.of_dkeep {b : Addr} {s t : State} (h : DKeep b s t) : DecKeep b s t :=
  ⟨h.rest, h.frame.mono (by simp)⟩

/-- `std t, off(n)`. -/
theorem wp_stdd {s : State} {is : List Instr} {Q : State → Prop} {t n : Reg} {off : Nat} {a : Addr}
    (hn : n ≠ .r0) (ho : off < 2 ^ 15 ∧ off % 4 = 0) (ha : s.gpr n + BitVec.ofNat 64 off = a)
    (hout : InRegions s.wr a 8) (k : ∀ s', Mupd s s' (s.mem.writeW a (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .d t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr t) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  rw [exec_store_d hn ho (by rw [ha]; exact hout), ha]

theorem toNat_beq_one {x : Nat} (h : x < 2) : (x == 1).toNat = x := by
  rcases (by omega_arith : x = 0 ∨ x = 1) with rfl | rfl <;> rfl

section
variable {b : Addr}

/-- **Bit 255 of slot 1**, to `SIGN`, and cleared. -/
theorem split_ok {s : State} (hc : Ctx b s) :
    WP isa (.block splitYSign) s fun t =>
      Rest [.r7, .r8] s t ∧
      Frame [⟨b + BitVec.ofNat 64 SIGN, 8⟩, ⟨b + BitVec.ofNat 64 (offset 1 + 28), 4⟩] s.mem t.mem ∧
      SignAt b (limb s.mem b (offset 1) 7 / 2 ^ 31 == 1) t.mem ∧
      limb t.mem b (offset 1) 7 = limb s.mem b (offset 1) 7 % 2 ^ 31 ∧
      ∀ j < 7, limb t.mem b (offset 1) j = limb s.mem b (offset 1) j := by
  have hS : SIGN = 24 := rfl
  have h1 : offset 1 = 96 := rfl
  unfold splitYSign VG.Impl.X25519.PPC64LE.low31
  simp only [List.cons_append, List.nil_append]
  refine lw0_ok hc (d := offset 1 + 28) (by decide) fun s2 u2 => wp_lsr (by decide) fun s3 u3 => ?_
  have hr3 : Rest [.r7, .r8] s s3 := (u2.rest (by decide)).trans (u3.rest (by decide))
  have hc3 : Ctx b s3 := hc.of_rest hr3 (by decide)
  refine wp_stdd (a := b + BitVec.ofNat 64 SIGN) (by decide) (by decide) (by rw [hc3.r6])
    (hc3.inW (by decide)) fun s4 u4 => ?_
  have hc4 : Ctx b s4 := hc3.of_rest (u4.rest []) (by decide)
  refine wp_lsl (by decide) fun s5 u5 => wp_lsr (by decide) fun s6 u6 => ?_
  have hc6 : Ctx b s6 := hc4.of_rest ((u5.rest (ws := [.r7]) (by decide)).trans (u6.rest (by decide))) (by decide)
  refine sw0_ok hc6 (d := offset 1 + 28) (by decide) fun s7 u7 => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hr3.trans ((u4.rest _).trans ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans (u7.rest _))))
  · rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem]
    refine Frame.writeW (Frame.writeW (Frame.refl _ _) List.mem_cons_self _ ?_)
      (List.mem_cons_of_mem _ List.mem_cons_self) _ ?_ <;> exact Region.contains_self _ _
  · have hw : (s2.gpr .r7).toNat = limb s.mem b (offset 1) 7 := by rw [u2.gpr, toNat_ext32]; rfl
    have hx : limb s.mem b (offset 1) 7 / 2 ^ 31 < 2 := by have := limb_lt s.mem b (offset 1) 7; omega_arith
    unfold SignAt
    rw [u7.mem, Mem.readW_writeW_sep (Offset.sep b (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide), u6.mem,
      u5.mem, u4.mem, Mem.readW_writeW_self64, u3.gpr]
    apply BitVec.eq_of_toNat_eq
    rw [toNat_shr, hw, BitVec.toNat_ofNat, toNat_beq_one hx, Nat.mod_eq_of_lt (by omega_arith)]
  · show wd s7.mem b (offset 1 + 28) = _
    rw [u7.mem, wd_write_self, toNat_lo32, u6.gpr, u5.gpr, low31_val, u4.gpr, u3.other _ (by decide), u2.gpr,
      toNat_ext32]
    show (s.mem.readW (b + BitVec.ofNat 64 (offset 1 + 28)) 32).toNat % 2 ^ 31 % 2 ^ 32 = _
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))]
    rfl
  · intro j hj
    show wd s7.mem b (offset 1 + 4 * j) = wd s.mem b (offset 1 + 4 * j)
    rw [u7.mem, wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), u6.mem, u5.mem, u4.mem, wd,
      Mem.readW_writeW_sep (Offset.sep b (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide), u3.mem, u2.mem]
    rfl

/-- **The encoding loaded**: `y` (bit 255 cleared) in slot 1, the sign at `SIGN`, and `r5` zero exactly
when `y < p`. -/
theorem pointDecodeLoad_ok {s : State} (hc : Ctx8 b s) {q : Addr} (h14 : s.gpr .r14 = q)
    (hr : ∀ k < 8, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 (0 + 4 * k)) 4)
    (hd : (⟨q + BitVec.ofNat 64 0, 32⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 (offset 1), 32⟩) :
    WP isa pointDecodeLoad s fun t => DecKeep b s t ∧
      SignAt b (decodeLE (bytesAt s.mem q 32) / 2 ^ 255 == 1) t.mem ∧
      env t.mem b 1 = Proof.X25519.toFe (decodeLE (bytesAt s.mem q 32) % 2 ^ 255) ∧
      (t.gpr .r5 = 0 ↔ decodeLE (bytesAt s.mem q 32) % 2 ^ 255 < P) := by
  have h1 : offset 1 = 96 := rfl
  have hX := FR_eq
  unfold pointDecodeLoad canonicalY
  refine WP.seq (WP.append (unpackField_ok hc.ctx h14 (o := offset 1) (src := 0) (by decide) (by decide) hr hd)
    fun s1 ⟨r1, f1, l1⟩ => ?_)
  have hn : decodeLE (bytesAt s.mem q 32) = V s1.mem b (offset 1) :=
    bytes_of_words fun j hj => by rw [l1 j hj, Nat.zero_add]
  have hc1 : Ctx b s1 := hc.ctx.of_rest r1 (by decide)
  refine WP.mono (split_ok hc1) fun s2 ⟨r2, f2, sg2, l7, lj⟩ => ?_
  -- `y`, and the sign, from the top limb.
  have hv1 := val32_succ (limb s1.mem b (offset 1)) 7
  have hv2 := val32_succ (limb s2.mem b (offset 1)) 7
  have hA := val32_lt (f := limb s1.mem b (offset 1)) (n := 7) fun k _ => limb_lt _ _ _ _
  have hL := limb_lt s1.mem b (offset 1) 7
  rw [val32_congr lj, l7] at hv2
  rw [show (2 : Nat) ^ (32 * 7) = 2 ^ 224 from rfl] at hv1 hv2 hA
  have hy : V s2.mem b (offset 1) = decodeLE (bytesAt s.mem q 32) % 2 ^ 255 := by
    rw [hn, V, V, hv1, hv2]; omega_arith
  have hsg : decodeLE (bytesAt s.mem q 32) / 2 ^ 255 = limb s1.mem b (offset 1) 7 / 2 ^ 31 := by
    rw [hn, V, hv1]; omega_arith
  rw [← hsg] at sg2
  have r12 : Rest [.r7, .r8] s s2 := (r1.mono (by decide)).trans r2
  have hc2 : Ctx8 b s2 := hc.of_rest r12 (by decide)
  have hF2 : Frame [⟨b + BitVec.ofNat 64 SIGN, 8⟩, FA b] s.mem s2.mem := by
    refine (f1.sub fun r hr => ⟨FA b, by simp, ?_⟩).trans (f2.sub fun r hr => ?_)
    · rw [List.mem_singleton.mp hr]; exact Offset.sub b (by omega_arith) (by omega_arith)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨FA b, by simp, Offset.sub b (by omega_arith) (by omega_arith)⟩
  -- `y` canonical.
  refine WP.seq (WP.mono (freeze_ok hc2.ctx 1) fun s3 ⟨r3, f3, _, v3⟩ => ?_)
  have hc3 : Ctx b s3 := hc2.ctx.of_rest r3 (by decide)
  refine WP.mono (wordsEqual_ok hc3 (a := offset 1) (c := FR) (by decide) (by decide)) fun t ⟨r4, m4, h4⟩ => ?_
  have hs3 : V s3.mem b (offset 1) = V s2.mem b (offset 1) := by
    unfold V
    exact val32_congr (limb_frame f3 fun r hr k hk => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith))
  refine ⟨⟨(r12.mono (by decide)).trans ((r3.mono (by decide)).trans (r4.mono (by decide))),
    hF2.trans (by rw [m4]; exact (frame_FR f3).mono (by simp))⟩, ?_, ?_, ?_⟩
  · rw [m4]; exact sg2.frame (frame_FR f3)
  · rw [m4, ← hy, ← hs3]; rfl
  · rw [h4, hs3, v3, hy]
    generalize decodeLE (bytesAt s.mem q 32) % 2 ^ 255 = y
    rw [eq_comm, Nat.mod_eq_iff_lt (by decide)]

/-- **A point decoded**, from the 32 bytes at `r14`. -/
theorem pointDecode_ok {s : State} (hc : Ctx8 b s) {q : Addr} (h14 : s.gpr .r14 = q)
    (hr : ∀ k < 8, InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 (0 + 4 * k)) 4)
    (hd : (⟨q + BitVec.ofNat 64 0, 32⟩ : Region).Disjoint ⟨b + BitVec.ofNat 64 (offset 1), 32⟩) :
    WP isa pointDecode s fun t => DecKeep b s t ∧
      ∃ o, Spec.Ed25519.decodePoint (bytesAt s.mem q 32) = o ∧ DecodeResult b o t := by
  have hl : (bytesAt s.mem q 32).length = 32 := by simp [Spec.Ed25519.bytesAt]
  rw [Proof.Ed25519.decodePoint32 _ hl]
  unfold pointDecode
  refine WP.seq (WP.mono (pointDecodeLoad_ok hc h14 hr hd) fun s1 ⟨k1, sg1, y1, h5⟩ => ?_)
  have hc1 : Ctx8 b s1 := hc.of_rest k1.rest (by decide)
  refine WP.ite (s1.gpr .r5 == 0) (eval_zero s1 .r5) (fun h => ?_) (fun h => ?_)
  · have hy := h5.mp (beq_iff_eq.mp h)
    refine WP.mono (recoverPoint_ok hc1 sg1) fun t ⟨kt, dt⟩ => ⟨k1.trans (DecKeep.of_dkeep kt), _, ?_, dt⟩
    rw [ite_eq_left hy, Proof.Ed25519.recoverResult_spec, y1]; rfl
  · have hy : ¬ decodeLE (bytesAt s.mem q 32) % 2 ^ 255 < P := fun hy =>
      absurd (beq_iff_eq.mpr (h5.mpr hy)) (by simpa using h)
    refine WP.mono (recoverInvalid_ok s1) fun t ⟨kt, _, dt⟩ => ⟨k1.trans (DecKeep.of_dkeep kt), none, ?_, dt⟩
    rw [ite_eq_right hy]

end

end VG.Proof.Ed25519.PPC64LE

end

end

/-!
# Ed25519 on PPC64LE: the two sides of the verification equation

With `pk`, the signature and the challenge in `r29`–`r31` (`VCtx`), `A` and
`R` decoded into the tables at 7776 and 7904, and the static of `-[1]B …
-[15]B` (`BStat`): the comparison of the points in slots 0–3 and 4–7
(`pointEqual_ok`), the challenge's top half (`challengeHigh_ok`), and what
the windows' proof gives (`RhsOk`), the result in `r17`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.Ed25519 (decodeLE bytesAt)

section
variable {b : Addr}

/-- **The comparison** of the points in slots 0–3 and 4–7, into `r17`. -/
theorem pointEqual_ok {s : State} (hc : Ctx8 b s) :
    WP isa Impl.Ed25519.PPC64LE.pointEqual s fun t => DKeep b s t ∧
      t.gpr .r17 = if Spec.Ed25519.pointEqual (point (env s.mem b) 0 1 2 3) (point (env s.mem b) 4 5 6 7)
        then 1 else 0 := by
  unfold Impl.Ed25519.PPC64LE.pointEqual
  refine WP.seq (WP.mono (fieldCode_ok _ hc.ctx) fun s1 ⟨k1, e1⟩ => ?_)
  have hc1 : Ctx8 b s1 := hc.of_keep k1
  refine WP.seq (WP.mono (fieldEqual_ok hc1.ctx 8 9) fun s2 ⟨k2, e2, h2⟩ => ?_)
  have hc2 : Ctx8 b s2 := hc1.of_keep k2
  have x8 : env s1.mem b 8 = env s.mem b 0 * env s.mem b 6 := by rw [e1]; rfl
  have x9 : env s1.mem b 9 = env s.mem b 4 * env s.mem b 2 := by rw [e1]; rfl
  have x10 : env s2.mem b 10 = env s.mem b 1 * env s.mem b 6 := by rw [e2, e1]; rfl
  have x11 : env s2.mem b 11 = env s.mem b 5 * env s.mem b 2 := by rw [e2, e1]; rfl
  rw [x8, x9] at h2
  have hk2 : DKeep b s s2 := DKeep.of_keep (k1.trans k2)
  unfold Spec.Ed25519.pointEqual
  simp only [point]
  refine WP.ite (s2.gpr .r5 == 0) (eval_zero s2 .r5) (fun h => ?_) (fun h => ?_)
  · have ha := h2.mp (beq_iff_eq.mp h)
    refine WP.seq (WP.mono (fieldEqual_ok hc2.ctx 10 11) fun s3 ⟨k3, _, h3⟩ => ?_)
    rw [x10, x11] at h3
    have hk3 : DKeep b s s3 := hk2.trans (DKeep.of_keep k3)
    refine WP.ite (s3.gpr .r5 == 0) (eval_zero s3 .r5) (fun h' => ?_) (fun h' => ?_)
    · refine wp_li (by decide) fun t u => WP.block_nil
        ⟨hk3.trans ⟨u.rest (by decide), by rw [u.mem]; exact Frame.refl _ _⟩, ?_⟩
      rw [u.gpr]
      simp [ha, h3.mp (beq_iff_eq.mp h')]
    · have hb : ¬ env s.mem b 1 * env s.mem b 6 = env s.mem b 5 * env s.mem b 2 :=
        fun he => absurd (beq_iff_eq.mpr (h3.mpr he)) (by simpa using h')
      refine WP.mono (recoverInvalid_ok s3) fun t ⟨kt, _, dt⟩ => ⟨hk3.trans kt, ?_⟩
      rw [show t.gpr .r17 = 0 from dt]
      simp [ha, hb]
  · have hb : ¬ env s.mem b 0 * env s.mem b 6 = env s.mem b 4 * env s.mem b 2 :=
      fun he => absurd (beq_iff_eq.mpr (h2.mpr he)) (by simpa using h)
    refine WP.mono (recoverInvalid_ok s2) fun t ⟨kt, _, dt⟩ => ⟨hk2.trans kt, ?_⟩
    rw [show t.gpr .r17 = 0 from dt]
    simp [hb]

end

/-- The verification's inputs: `pk`, the signature and the challenge, readable at `r29`–`r31`,
outside the working space at `r6`. -/
structure VCtx (b pk sig ch : Addr) (s : State) : Prop where
  ctx : Ctx8 b s
  r29 : s.gpr .r29 = pk
  r30 : s.gpr .r30 = sig
  r31 : s.gpr .r31 = ch
  pkR : (⟨pk, 32⟩ : Region) ∈ s.rd
  sigR : (⟨sig, 64⟩ : Region) ∈ s.rd
  chR : (⟨ch, 64⟩ : Region) ∈ s.rd
  pkD : (⟨pk, 32⟩ : Region).Disjoint ⟨b, 8192⟩
  sigD : (⟨sig, 64⟩ : Region).Disjoint ⟨b, 8192⟩
  chD : (⟨ch, 64⟩ : Region).Disjoint ⟨b, 8192⟩

section
variable {b pk sig ch : Addr}

theorem VCtx.of_rest {s t : State} {R : List Reg} (h : VCtx b pk sig ch s) (hr : Rest R s t)
    (hw : ∀ r ∈ [Reg.r6, .r29, .r30, .r31], r ∉ R) : VCtx b pk sig ch t where
  ctx := h.ctx.of_rest hr (hw _ (by simp))
  r29 := by rw [hr.gpr _ (hw _ (by simp)), h.r29]
  r30 := by rw [hr.gpr _ (hw _ (by simp)), h.r30]
  r31 := by rw [hr.gpr _ (hw _ (by simp)), h.r31]
  pkR := by rw [hr.rd]; exact h.pkR
  sigR := by rw [hr.rd]; exact h.sigR
  chR := by rw [hr.rd]; exact h.chR
  pkD := h.pkD
  sigD := h.sigD
  chD := h.chD

/-- Bytes outside the working space, through a frame within it. -/
theorem bytesAt_ws {m m' : Mem} {rs : List Region} (hf : Frame rs m m') (hs : ∀ r ∈ rs, Region.Sub r ⟨b, 8192⟩)
    {p : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨b, 8192⟩) (hn : n ≤ 64) :
    bytesAt m' p n = bytesAt m p n := by
  simp only [Spec.Ed25519.bytesAt, List.map_inj_left]
  intro i hi
  exact bytes_ws hf hs hd hn (List.mem_range.mp hi)

theorem table_sub {o : Nat} (ho : o + 128 ≤ 8192) : Region.Sub ⟨b + BitVec.ofNat 64 o, 128⟩ ⟨b, 8192⟩ :=
  Offset.sub_base b ho

/-- What `[S] P` writes, with a table entry. -/
abbrev sideW (b : Addr) (o : Nat) : List Region := ⟨b + BitVec.ofNat 64 o, 128⟩ :: mulW b

theorem sideW_sub {o : Nat} (ho : o + 128 ≤ 8192) : ∀ r ∈ sideW b o, Region.Sub r ⟨b, 8192⟩ := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact table_sub ho
  · exact mulW_sub r hr

/-- The registers `[S] P` writes. -/
abbrev sideR : List Reg := .r19 :: .r7 :: batchR

/-- A list of zero bytes is the integer 0. -/
theorem decodeLE_zeros : ∀ (l : List (BitVec 8)), (∀ x ∈ l, x = 0) → decodeLE l = 0
  | [], _ => rfl
  | x :: l, h => by
    rw [Proof.Ed25519.decodeLE_cons, h x List.mem_cons_self,
      decodeLE_zeros l fun y hy => h y (List.mem_cons_of_mem _ hy)]
    rfl

/-- A challenge whose top 32 bytes are zero is its low 32 bytes. -/
theorem decodeLE_low (m : Mem) (p : Addr) (h : ∀ i < 32, m (p + BitVec.ofNat 64 (32 + i)) = 0) :
    decodeLE (bytesAt m p 64) = decodeLE (bytesAt m p 32) := by
  have hs : bytesAt m p (32 + 32) = bytesAt m p 32 ++ bytesAt m (p + BitVec.ofNat 64 32) 32 :=
    Proof.X25519.bytesAt_add m p 32 32
  rw [show 64 = 32 + 32 from rfl, hs, Proof.Ed25519.decodeLE_append,
    decodeLE_zeros (bytesAt m (p + BitVec.ofNat 64 32) 32) ?_, Nat.mul_zero, Nat.add_zero]
  intro x hx
  simp only [bytesAt, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact h i hi

theorem or_eq_zero (x y : BitVec 64) : x ||| y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have h' := congrArg BitVec.toNat h
    rw [BitVec.toNat_or] at h'
    have := Nat.or_eq_zero_iff.mp h'
    exact ⟨BitVec.eq_of_toNat_eq this.1, BitVec.eq_of_toNat_eq this.2⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- The first `n` bytes of the challenge's top half, or-ed into `r8`. -/
theorem challengeOr_ok {ch : Addr} :
    ∀ n ≤ 32, ∀ s : State, s.gpr .r31 = ch →
      (∀ i < 32, InRegions (s.rd ++ s.wr) (ch + BitVec.ofNat 64 (32 + i)) 1) →
      WP isa (.block ((List.range n).flatMap fun i =>
          [.lbz .r9 .r31 (32 + i), .logic .or .r8 .r8 .r9])) s fun t =>
        Rest [.r8, .r9] s t ∧ t.mem = s.mem ∧
        (t.gpr .r8 = 0 ↔ s.gpr .r8 = 0 ∧ ∀ i < n, s.mem (ch + BitVec.ofNat 64 (32 + i)) = 0)
  | 0, _, s, _, _ => WP.block_nil ⟨Rest.refl _ _, rfl, by simp⟩
  | n + 1, hn, s, h31, hin => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.append (challengeOr_ok n (by omega_using [hn]) s h31 hin) fun s1 ⟨r1, m1, e1⟩ => ?_
    refine wp_lbz (a := ch + BitVec.ofNat 64 (32 + n)) (by decide) (by omega_using [hn])
      (by rw [r1.gpr _ (by decide), h31]) (by rw [r1.rd, r1.wr]; exact hin n (by omega_using [hn])) fun s2 u2 => ?_
    refine wp_or fun s3 u3 => WP.block_nil ⟨r1.trans ((u2.rest (by decide)).trans (u3.rest (by decide))),
      by rw [u3.mem, u2.mem, m1], ?_⟩
    rw [u3.gpr, u2.other _ (by decide), u2.gpr, or_eq_zero, e1, m1]
    have hz : BitVec.ofNat 64 (s.mem (ch + BitVec.ofNat 64 (32 + n))).toNat = 0 ↔
        s.mem (ch + BitVec.ofNat 64 (32 + n)) = 0 := by
      constructor
      · intro h
        apply BitVec.eq_of_toNat_eq
        have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide))] at this
        exact this
      · intro h; rw [h]; rfl
    rw [hz]
    constructor
    · rintro ⟨⟨h0, hl⟩, hb⟩
      exact ⟨h0, fun i hi => if e : i = n then e ▸ hb else hl i (by omega_using [hi, e])⟩
    · rintro ⟨h0, hl⟩
      exact ⟨⟨h0, fun i hi => hl i (by omega_using [hi])⟩, hl n (by omega_using [])⟩

/-- **`challengeHigh`**: `r8` zero exactly when the challenge's top 32 bytes are. -/
theorem challengeHigh_ok {ch : Addr} {s : State} (h31 : s.gpr .r31 = ch)
    (hin : ∀ i < 32, InRegions (s.rd ++ s.wr) (ch + BitVec.ofNat 64 (32 + i)) 1) :
    WP isa (.block challengeHigh) s fun t =>
      Rest [.r8, .r9] s t ∧ t.mem = s.mem ∧
      (t.gpr .r8 = 0 ↔ ∀ i < 32, s.mem (ch + BitVec.ofNat 64 (32 + i)) = 0) := by
  unfold challengeHigh
  refine wp_li (by decide) fun s1 u1 => ?_
  refine WP.mono (challengeOr_ok (ch := ch) 32 (Nat.le_refl _) s1 (by rw [u1.other _ (by decide), h31])
    (by rw [u1.rd, u1.wr]; exact hin)) fun t ⟨rt, mt, et⟩ =>
      ⟨(u1.rest (by decide)).trans rt, by rw [mt, u1.mem], ?_⟩
  rw [et, u1.gpr, u1.mem]
  simp

/-- The static of the cached `-[1]B … -[15]B` at `T`: readable, its words, not wrapping around,
apart from the working space. -/
structure BStat (b T : Addr) (s : State) : Prop where
  rd : (⟨T, 1920⟩ : Region) ∈ s.rd
  fit : T.toNat + 1920 ≤ 2 ^ 64
  words : ∀ q < 240, s.mem.readW (T + BitVec.ofNat 64 (8 * q)) 64 = bWord q
  ws : (⟨T, 1920⟩ : Region).Disjoint ⟨b, 8192⟩

/-- The static's facts through a frame within the working space. -/
theorem BStat.of_frame {T : Addr} {s t : State} (h : BStat b T s) (hrd : t.rd = s.rd) {rs : List Region}
    (hf : Frame rs s.mem t.mem) (hs : ∀ r ∈ rs, Region.Sub r ⟨b, 8192⟩) : BStat b T t where
  rd := hrd ▸ h.rd
  fit := h.fit
  words q hq := by
    rw [← h.words q hq]
    exact hf.readW (r := ⟨T, 1920⟩) (Offset.contains_base T (by omega_using [hq]) (by omega_using [hq]))
      (fun r hr x h₁ h₂ => h.ws x h₁ (hs r hr x h₂)) (by decide)
  ws := h.ws

/-- **`[k] A - [S] B` compared with `-R`**, for the decoded `A` and `R` in the tables at 7776 and
7904 and the static at `s.syms bSym`, as the equation `[S] B = R + [k] A`: what the windows'
proof gives (`Proof/Ed25519/PPC64LE/WindowRhs.lean`, `rhs_ok`). -/
def RhsOk : Prop := ∀ {b pk sig ch : Addr} {s : State} {PK RS : List Byte},
  VCtx b pk sig ch s → BStat b (s.syms bSym) s →
  Spec.Ed25519.decodePoint PK = some (tableAt s.mem b 7776) →
  Spec.Ed25519.decodePoint RS = some (tableAt s.mem b 7904) →
  WP isa verifyRhs s fun t => Rest (.r17 :: sideR) s t ∧ Frame (sideW b 8032) s.mem t.mem ∧
    t.gpr .r17 = if Spec.Ed25519.pointEqual
      (Spec.Ed25519.pointMul (decodeLE (bytesAt s.mem (sig + BitVec.ofNat 64 32) 32)) Spec.Ed25519.basePoint)
      (Spec.Ed25519.pointAdd (tableAt s.mem b 7904)
        (Spec.Ed25519.pointMul (decodeLE (bytesAt s.mem ch 64)) (tableAt s.mem b 7776))) then 1 else 0

end

end VG.Proof.Ed25519.PPC64LE

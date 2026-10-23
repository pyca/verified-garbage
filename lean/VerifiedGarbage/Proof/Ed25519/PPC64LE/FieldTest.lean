module

public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Freeze
public import VerifiedGarbage.Proof.X25519.PPC64LE.Field
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.FieldProg
import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointPowers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Freeze
import VerifiedGarbage.Proof.X25519.PPC64LE.Instr
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

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
    omega

theorem psum_eq_zero {f : Nat → Nat} : ∀ {k : Nat}, psum f k = 0 ↔ ∀ j < k, f j = 0
  | 0 => by simp [psum]
  | k + 1 => by
    rw [psum, Nat.add_eq_zero_iff, psum_eq_zero]
    exact ⟨fun ⟨h1, h2⟩ j hj => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      exacts [h1 j hj, h2], fun h => ⟨fun j hj => h j (by omega), h k (by omega)⟩⟩

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
    refine lw0_ok ht (d := o + 4 * k) (by omega) fun s2 u2 => wp_add fun s3 u3 => WP.block_nil ⟨?_, ?_, ?_⟩
    · exact hr.trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
    · rw [u3.mem, u2.mem, hm]
    · have hle := psum_le (fun j => limb_lt s.mem b o j) k
      have hl := limb_lt s.mem b o k
      have e7 : (s2.gpr .r7).toNat = limb s.mem b o k := by rw [u2.gpr, toNat_ext32, hm]; rfl
      rw [u3.gpr, u2.other _ (by decide), toNat_add_lt (by rw [h5, e7]; omega), h5, e7]
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
    ⟨u1.rest (by decide), u1.mem, by rw [u1.gpr]; exact ⟨fun _ j hj => absurd hj (by omega), fun _ => rfl⟩⟩)
    fun t ⟨hr, hm, h5⟩ => ⟨hr, hm, ?_⟩
  · have ht : Ctx b t := hc.of_rest hr (by decide)
    unfold equalLimb
    refine lw0_ok ht (d := a + 4 * k) (by omega) fun s2 u2 => ?_
    have hc2 : Ctx b s2 := ht.of_rest (u2.rest (ws := [.r7]) (by decide)) (by decide)
    refine lw0_ok hc2 (d := c + 4 * k) (by omega) fun s3 u3 => wp_xor fun s4 u4 => wp_or fun s5 u5 =>
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
      refine ⟨fun ⟨h1, h2⟩ j hj => ?_, fun h => ⟨fun j hj => h j (by omega), h k (by omega)⟩⟩
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
  refine WP.mono (wordsZero_ok (hc.of_rest r1 (by decide)) (o := FR) (by omega)) fun t ⟨r2, m2, h2⟩ =>
    ⟨r1.trans (r2.mono (by decide)), (by rw [m2]; exact f1), (by rw [h2, v1])⟩

theorem fe_sub_eq_zero (x y : Spec.X25519.Fe) : x - y = 0 ↔ x = y := by
  rw [Fin.ext_iff, Fin.ext_iff, Fin.sub_def]
  have hx := x.isLt
  have hy := y.isLt
  show (P - y.val + x.val) % P = 0 ↔ _
  by_cases hxy : y.val ≤ x.val
  · rw [show P - y.val + x.val = (x.val - y.val) + P by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem fieldEqual_ok {s : State} (hc : Ctx b s) (a c : Slot) :
    WP isa (fieldEqual a c) s fun t =>
      Keep b s t ∧ env t.mem b = evalOps [.sub 21 a c] (env s.mem b) ∧
      (t.gpr .r5 = 0 ↔ env s.mem b a = env s.mem b c) := by
  have hX := FR_eq
  unfold fieldEqual
  refine WP.seq (WP.mono (fieldCode_ok _ hc) fun s1 ⟨k1, e1⟩ => ?_)
  refine WP.mono (fieldZero_ok (k1.ctx hc) 21) fun t ⟨r2, f2, h2⟩ => ⟨⟨k1.rest.trans (r2.mono (by decide)),
    k1.frame.trans (f2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub b (by omega) (by omega)⟩)⟩, ?_, ?_⟩
  · have ek : env t.mem b = env s1.mem b := funext fun i => env_keep f2 i fun r hr => by
      have := slot_range i
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
    rw [ek, e1]
  · have e21 : env s1.mem b 21 = env s.mem b a - env s.mem b c := by
      rw [e1]; simp only [evalOps, List.foldl, evalOp, Function.update_self]
    rw [h2, ← fe_sub_eq_zero, ← e21, Fin.ext_iff]
    rfl

end

end VG.Proof.Ed25519.PPC64LE

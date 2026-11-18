module

import VerifiedGarbage.Proof.Ed25519.Arm.FieldMemory
public import VerifiedGarbage.Proof.Ed25519.Arm.MulFnFinal
public import VerifiedGarbage.Proof.Framework.Arm.Spill
public import VerifiedGarbage.Proof.Ed25519.Arm.Field
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Call
public import Mathlib.Logic.Function.Basic
public import VerifiedGarbage.Proof.X25519.Arm.Invert
public import VerifiedGarbage.Spec.Ed25519
public import VerifiedGarbage.Proof.Ed25519.DblPoint
public import VerifiedGarbage.Impl.Ed25519.Arm.Field
import VerifiedGarbage.Proof.X25519.Arm.AddSub
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.X25519.Arm.Words.Ladder
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `Ed25519.Arm.MulU`, which this module and modules that import it used -/

section

/-!
# The field's product with `umaal` on ARMv7

Untrusted: everything here is checked by Lean. `mulBodyU`
(`Impl/Ed25519/Arm/MulFn.lean`) meets the contract of the baseline's product
(`mulBody_ok`), on the same sixteen 16-bit limbs (`mulBodyU_ok`), and
changes only `r1`–`r9`: the second operand's limbs packed in pairs into
eight words at `ACC` (`packU_ok`, `mulSetupU_ok`), the rows (`rowStepU_ok`,
`rowU_ok`: a chain of `umaal`s each, `uc` and `uo` of
`Proof/X25519/Arm/Words/Ladder.lean`; the invariant `InvU`: after `i` rows,
the product's first `i + 8` words at `ACC + 64` are the product of the first
`i` packed words of the first operand and the second operand), `lo + 38 hi`
in words (`foldPassU_ok`), its words with 38 times its carry as the result's
limbs (`splitPassU_ok`), and 38 times what that carries out into limb 0
(`mulFinalU_ok`, `foldU_arith`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.Arm

open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm
open VG.Proof.X25519.Arm.Words (val32 val32_succ val32_congr val32_append val32_zero_fn val32_lt uc uo uc_succ
  uc_val umaal_lt wp_umaal Upd2)
open VG.Spec.X25519 (P)

/-! ## Limbs packed in words -/

/-- Limbs `2k` and `2k + 1` as a word. -/
def packW (f : Nat → Nat) (k : Nat) : Nat := f (2 * k) + 65536 * f (2 * k + 1)

theorem packW_lt {f : Nat → Nat} {k : Nat} (h0 : f (2 * k) < 65536) (h1 : f (2 * k + 1) < 65536) :
    packW f k < 2 ^ 32 := by
  unfold packW; omega_using [h0, h1]

/-- The limbs' number in radix `2¹⁶` is their packed words' in radix `2³²`. -/
theorem val16_packW (f : Nat → Nat) : ∀ n, val16 f (2 * n) = val32 (packW f) n
  | 0 => rfl
  | n + 1 => by
    have e1 : 2 ^ (16 * (2 * n)) = 2 ^ (32 * n) := congrArg (2 ^ ·) (by omega_arith)
    have e2 : 2 ^ (16 * (2 * n + 1)) = 2 ^ (32 * n) * 65536 := by
      rw [show 16 * (2 * n + 1) = 32 * n + 16 by omega_arith, Nat.pow_add]
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 from rfl, val16_succ, val16_succ, val16_packW f n, val32_succ, packW, e1, e2,
      Nat.mul_add, Nat.add_assoc, Nat.mul_assoc]

/-- Limb `k` of the number of the words `W`: a half of word `k / 2`. -/
def wordLimb (W : Nat → Nat) (k : Nat) : Nat := if k % 2 = 0 then W (k / 2) % 65536 else W (k / 2) / 65536

theorem wordLimb_lt {W : Nat → Nat} (h : ∀ q, W q < 2 ^ 32) (k : Nat) : wordLimb W k < 65536 := by
  unfold wordLimb
  split
  · exact Nat.mod_lt _ (by decide)
  · exact (Nat.div_lt_iff_lt_mul (by decide)).mpr (h _)

theorem packW_wordLimb (W : Nat → Nat) (k : Nat) : packW (wordLimb W) k = W k := by
  have e0 : 2 * k % 2 = 0 := by omega_arith
  have e1 : ¬ (2 * k + 1) % 2 = 0 := by omega_arith
  have d0 : 2 * k / 2 = k := by omega_arith
  have d1 : (2 * k + 1) / 2 = k := by omega_arith
  rw [packW, wordLimb, wordLimb, ite_eq_left e0, ite_eq_right e1, d0, d1]
  exact Nat.mod_add_div _ _

/-- The words' number in radix `2³²` is their limbs' in radix `2¹⁶`. -/
theorem val16_wordLimb (W : Nat → Nat) (n : Nat) : val16 (wordLimb W) (2 * n) = val32 W n := by
  rw [val16_packW]
  exact val32_congr fun k _ => packW_wordLimb W k

/-- Word `j` of the packed second operand, at `ACC`. -/
abbrev bwU (m : Mem) (B : Addr) (j : Nat) : Nat := wd m B (ACC + 4 * j)

/-- Word `k` of the product, at `ACC + 64`. -/
abbrev pwU (m : Mem) (B : Addr) (k : Nat) : Nat := wd m B (ACC + 64 + 4 * k)

/-- Two limbs, the second shifted, as their word. -/
theorem packed_toNat {x y : BitVec 32} (hx : x.toNat < 65536) (hy : y.toNat < 65536) :
    (x + y <<< 16).toNat = x.toNat + 65536 * y.toNat := by
  have e : (y <<< 16).toNat = 65536 * y.toNat := by
    rw [toNat_shl, Nat.mod_eq_of_lt (by omega_using [hy])]; omega_arith
  rw [toNat_add_lt (by rw [e]; omega_using [hx, hy]), e]

section
variable {e : Nat} {b : BitVec 32}

/-! ## The second operand packed, and the product's low words zeroed -/

theorem packU_ok {y j : Nat} (hy : y + 64 ≤ ACC) (hj : j < 8) {s : State} (hc : CtxN e b s)
    (h9 : s.gpr .r9 = b + BitVec.ofNat 32 y) (hly : Lim s.mem (State.addr b) y) :
    WP isa (.block (packU j)) s fun t =>
      t.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 (ACC + 4 * j))
        (BitVec.ofNat 32 (packW (limb s.mem (State.addr b) y) j)) ∧ Rest [.r2, .r3] s t := by
  have hA := ACC_eq
  obtain hfit : b.toNat + 4096 ≤ 2 ^ 32 := by have := hc.fit; omega_using [this]
  unfold packU
  refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (y + 4 * (2 * j))) (by omega_using [hj])
    (by rw [h9, addB hfit (by omega_using [hy, hA, hj]), show y + 8 * j = y + 4 * (2 * j) by omega_arith])
    (hc.inR (by omega_using [hy, hA, hj])) fun s1 u1 => ?_
  refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (y + 4 * (2 * j + 1))) (by omega_using [hj])
    (by rw [u1.other _ (by decide), h9, addB hfit (by omega_using [hy, hA, hj]),
          show y + (8 * j + 4) = y + 4 * (2 * j + 1) by omega_arith])
    (by rw [u1.rd, u1.wr]; exact hc.inR (by omega_using [hy, hA, hj])) fun s2 u2 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s3 u3 => ?_
  obtain r3 : Rest [.r2, .r3] s s3 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
  refine str0_ok (hc.of_rest r3 (by decide)) (d := ACC + 4 * j) (by omega_using [hA, hj]) fun s4 u4 =>
    WP.block_nil ⟨?_, r3.trans (u4.rest _)⟩
  obtain b2 : limb s.mem (State.addr b) y (2 * j) < 65536 := hly _ (by omega_using [hj])
  obtain b3 : limb s.mem (State.addr b) y (2 * j + 1) < 65536 := hly _ (by omega_using [hj])
  obtain e2 : (s2.gpr .r2).toNat = limb s.mem (State.addr b) y (2 * j) := by
    rw [u2.other _ (by decide), u1.gpr]; rfl
  obtain e3 : (s2.gpr .r3).toNat = limb s.mem (State.addr b) y (2 * j + 1) := by
    rw [u2.gpr, u1.mem]; rfl
  rw [u4.mem, u3.mem, u2.mem, u1.mem]
  refine congrArg (s.mem.writeW _) (BitVec.eq_of_toNat_eq ?_)
  rw [u3.gpr]
  change (s2.gpr .r2 + s2.gpr .r3 <<< 16).toNat = _
  rw [packed_toNat (by rw [e2]; exact b2) (by rw [e3]; exact b3), e2, e3, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (packW_lt b2 b3)]
  rfl

/-- After `i` rows of the product of `[x]` and `[y]` into `[o]`, from `s0`: the second operand's
words at `ACC`, and the product of the first `i` words of the first operand and the second
operand in the first `i + 8` words at `ACC + 64`. -/
structure InvU (e : Nat) (b : BitVec 32) (o x y : Nat) (s0 : State) (i : Nat) (s : State) : Prop where
  ctx : CtxN e b s
  rest : Rest clob s0 s
  r7 : s.gpr .r7 = b + BitVec.ofNat 32 (4 * i)
  r5 : s.gpr .r5 = b + BitVec.ofNat 32 (x + 8 * i)
  r8 : s.gpr .r8 = b + BitVec.ofNat 32 o
  r9 : s.gpr .r9 = BitVec.ofNat 32 (8 - i)
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] s0.mem s.mem
  bw : ∀ j < 8, bwU s.mem (State.addr b) j = packW (limb s0.mem (State.addr b) y) j
  val : val32 (pwU s.mem (State.addr b)) (i + 8) =
    val32 (packW (limb s0.mem (State.addr b) x)) i * val32 (packW (limb s0.mem (State.addr b) y)) 8

theorem mulSetupU_ok {o x y : Nat} (hy : y + 64 ≤ ACC) {s : State} (hc : CtxN e b s)
    (h1 : s.gpr .r1 = BitVec.ofNat 32 o) (h2 : s.gpr .r2 = BitVec.ofNat 32 x)
    (h3 : s.gpr .r3 = BitVec.ofNat 32 y) (hly : Lim s.mem (State.addr b) y) :
    WP isa (.block mulSetupU) s (InvU e b o x y s 0) := by
  have hA := ACC_eq
  have e0 : s.gpr .r0 = b := hc.r0
  simp only [mulSetupU, Impl.X25519.Arm.storeN, List.cons_append, List.nil_append, List.append_assoc]
  refine wp_dp (op2_reg _ _) fun s1 u1 => wp_dp (op2_reg _ _) fun s2 u2 => wp_dp (op2_reg _ _) fun s3 u3 => ?_
  obtain hr3 : Rest [.r5, .r8, .r9] s s3 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
  obtain hc3 : CtxN e b s3 := hc.of_rest hr3 (by decide)
  obtain m3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  obtain e8 : s3.gpr .r8 = b + BitVec.ofNat 32 o := by
    rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr, e0, h1]; rfl
  obtain e5 : s3.gpr .r5 = b + BitVec.ofNat 32 x := by
    rw [u3.other _ (by decide), u2.gpr, u1.other _ (by decide), u1.other _ (by decide), e0, h2]; rfl
  obtain e9 : s3.gpr .r9 = b + BitVec.ofNat 32 y := by
    rw [u3.gpr, u2.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide),
      u1.other _ (by decide), e0, h3]; rfl
  -- The second operand.
  refine WP.append (wp_range_flatMap (M := isa) (N := 8)
    (fun n t => (∀ j < n, bwU t.mem (State.addr b) j = packW (limb s.mem (State.addr b) y) j) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 32⟩] s3.mem t.mem ∧ Rest [.r2, .r3] s3 t)
    (fun n t hn ⟨tb, tf, tr⟩ => ?_) 8 (Nat.le_refl _) s3
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, Rest.refl _ _⟩) fun s4 ⟨b4, f4, r4⟩ => ?_
  · obtain ly : ∀ k < 16, limb t.mem (State.addr b) y k = limb s.mem (State.addr b) y k := fun k hk => by
      rw [← m3]
      exact wd_frame tf fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (.inl (by omega_using [hy, hk])) (by omega_using [hy, hA, hk]) (by omega_using [hA])
    refine WP.mono (packU_ok hy hn (hc3.of_rest tr (by decide)) ((tr.gpr _ (by decide)).trans e9)
      (fun k hk => by rw [ly k hk]; exact hly k hk)) fun u ⟨um, ur⟩ => ⟨fun j hj => ?_, ?_, tr.trans ur⟩
    · rw [bwU, um]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [wd_write_other _ _ _ (by omega_using [hj]) (by omega_using [hA, hj, hn]) (by omega_using [hA, hn])]
        exact tb j hj
      · rw [wd_write_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (packW_lt
          (by rw [ly _ (by omega_using [hn])]; exact hly _ (by omega_using [hn]))
          (by rw [ly _ (by omega_using [hn])]; exact hly _ (by omega_using [hn])))]
        show limb t.mem (State.addr b) y (2 * j) + 65536 * limb t.mem (State.addr b) y (2 * j + 1) = _
        rw [ly _ (by omega_using [hn]), ly _ (by omega_using [hn])]
        rfl
    · rw [um]
      exact tf.writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega_using []) (by omega_using [hn]) (by omega_using [hA]))
  -- The product's low words.
  obtain hc4 := hc3.of_rest r4 (by decide)
  refine wp_mov (op2_imm (by decide)) fun s5 u5 => ?_
  obtain hc5 := hc4.of_rest (u5.rest (ws := [.r3]) (by decide)) (by decide)
  refine WP.append (wp_range_flatMap (M := isa) (N := 8)
    (fun n t => (∀ k < n, pwU t.mem (State.addr b) k = 0) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 (ACC + 64), 32⟩] s5.mem t.mem ∧ Rest [] s5 t ∧ t.gpr .r3 = 0)
    (fun n t hn ⟨z1, z2, z3, z4⟩ => ?_) 8 (Nat.le_refl _) s5
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, Rest.refl _ _, u5.gpr⟩)
    fun s6 ⟨z6, f6, r6, _⟩ => ?_
  · refine str0_ok (hc5.of_rest z3 (by decide)) (d := ACC + 64 + 4 * n) (by omega_using [hA, hn]) fun t' u' =>
      WP.block_nil ⟨fun k hk => ?_, ?_, z3.trans (u'.rest _), by rw [u'.gpr, z4]⟩
    · rw [pwU, u'.mem]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · rw [wd_write_other _ _ _ (by omega_using [hk]) (by omega_using [hA, hk, hn]) (by omega_using [hA, hn])]
        exact z1 k hk
      · rw [wd_write_self, z4]; rfl
    · rw [u'.mem]
      exact z2.writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega_using []) (by omega_using [hn]) (by omega_using [hA]))
  obtain hc6 := hc5.of_rest r6 (by decide)
  refine wp_mov (op2_reg _ _) fun s7 u7 => wp_mov (op2_imm (by decide)) fun s8 u8 => WP.block_nil ?_
  obtain r38 : Rest [.r2, .r3, .r7, .r9] s3 s8 :=
    (r4.mono (by decide)).trans ((u5.rest (by decide)).trans ((r6.mono (by decide)).trans
      ((u7.rest (by decide)).trans (u8.rest (by decide)))))
  obtain r8 : Rest clob s s8 := (hr3.mono (by decide)).trans (r38.mono (by decide))
  obtain m8 : s8.mem = s6.mem := by rw [u8.mem, u7.mem]
  obtain f46 : Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] s.mem s6.mem := by
    rw [← m3]
    refine (f4.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (Frame.sub (by rw [← u5.mem]; exact f6) fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · rw [List.mem_singleton.mp hr]; exact Offset.sub _ (Nat.le_refl _) (by omega_using [])
    · rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_using []) (by omega_using [])
  refine ⟨hc.of_rest r8 (by decide), r8, ?_, ?_, ?_, u8.gpr, m8 ▸ f46, fun j hj => ?_, ?_⟩
  · rw [u8.other _ (by decide), u7.gpr, hc6.r0]; exact (BitVec.add_zero b).symm
  · rw [r38.gpr _ (by decide), e5]; rfl
  · rw [r38.gpr _ (by decide), e8]
  · rw [m8, bwU, wd_frame f6 fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (.inl (by omega_using [hj])) (by omega_using [hA, hj]) (by omega_using [hA]),
      u5.mem]
    exact b4 j hj
  · rw [m8, Nat.zero_add, val32_congr (g := fun _ => 0) (fun k hk => z6 k hk), val32_zero_fn]
    exact (Nat.zero_mul _).symm

/-! ## The rows -/

/-- One product of row `i`. -/
theorem rowStepU_ok {i j : Nat} (hi : i < 8) (hj : j < 8) {s : State} (hc : CtxN e b s)
    (h7 : s.gpr .r7 = b + BitVec.ofNat 32 (4 * i)) :
    WP isa (.block (rowStepU j)) s fun t =>
      (t.gpr .r4).toNat = ((s.gpr .r1).toNat * bwU s.mem (State.addr b) j + (s.gpr .r4).toNat +
        pwU s.mem (State.addr b) (i + j)) / 2 ^ 32 ∧
      (t.gpr .r3).toNat = ((s.gpr .r1).toNat * bwU s.mem (State.addr b) j + (s.gpr .r4).toNat +
        pwU s.mem (State.addr b) (i + j)) % 2 ^ 32 ∧
      t.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 (ACC + 64 + 4 * (i + j))) (t.gpr .r3) ∧
      Rest [.r2, .r3, .r4] s t := by
  have hA := ACC_eq
  obtain hfit : b.toNat + 4096 ≤ 2 ^ 32 := by have := hc.fit; omega_using [this]
  unfold rowStepU
  refine ldr0_ok hc (d := ACC + 4 * j) (by omega_using [hA, hj]) fun s1 u1 => ?_
  refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (ACC + 64 + 4 * (i + j))) (by omega_using [hA, hj])
    (by rw [u1.other _ (by decide), h7, ea7 hfit (by omega_using [hA, hi, hj]),
          show 4 * i + (ACC + 64 + 4 * j) = ACC + 64 + 4 * (i + j) by omega_arith])
    (by rw [u1.rd, u1.wr]; exact hc.inR (by omega_using [hA, hi, hj])) fun s2 u2 => ?_
  obtain e2 : (s2.gpr .r2).toNat = bwU s.mem (State.addr b) j := by rw [u2.other _ (by decide), u1.gpr]; rfl
  obtain e3 : (s2.gpr .r3).toNat = pwU s.mem (State.addr b) (i + j) := by rw [u2.gpr, u1.mem]; rfl
  obtain e1 : s2.gpr .r1 = s.gpr .r1 := by rw [u2.other _ (by decide), u1.other _ (by decide)]
  obtain e4 : s2.gpr .r4 = s.gpr .r4 := by rw [u2.other _ (by decide), u1.other _ (by decide)]
  refine wp_umaal (by decide) (umaal_lt (s2.gpr .r1).isLt (s2.gpr .r2).isLt (s2.gpr .r4).isLt
    (s2.gpr .r3).isLt) fun s3 u3 => ?_
  obtain r3 : Rest [.r2, .r3, .r4] s s3 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide) (by decide)))
  refine wp_str (a := State.addr b + BitVec.ofNat 64 (ACC + 64 + 4 * (i + j))) (by omega_using [hA, hj])
    (by rw [r3.gpr _ (by decide), h7, ea7 hfit (by omega_using [hA, hi, hj]),
          show 4 * i + (ACC + 64 + 4 * j) = ACC + 64 + 4 * (i + j) by omega_arith])
    ((hc.of_rest r3 (by decide)).inW (by omega_using [hA, hi, hj])) fun s4 u4 =>
      WP.block_nil ⟨?_, ?_, ?_, r3.trans (u4.rest _)⟩
  · rw [u4.gpr, u3.ghi, e1, e2, e3, e4]
  · rw [u4.gpr, u3.glo, e1, e2, e3, e4]
  · rw [u4.mem, u3.mem, u2.mem, u1.mem, u4.gpr]

/-- The row's sum. -/
theorem rowU_arith {Pv Pi XV Ai av Bv p : Nat} (h1 : Pv = Pi + p * XV) (h2 : Pv = Ai * Bv) :
    Pi + p * (av * Bv + XV) = (Ai + p * av) * Bv := by
  rw [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
  omega_using [h1, h2]

theorem rowU_ok {o x y : Nat} (hx : x + 64 ≤ ACC) {s0 : State} (hlx : Lim s0.mem (State.addr b) x)
    {i : Nat} (hi : i < 8) {s : State} (h : InvU e b o x y s0 i s) :
    WP isa (.block rowU) s fun t => InvU e b o x y s0 (i + 1) t ∧ t.z = decide (i + 1 = 8) := by
  have hA := ACC_eq
  obtain hfit : b.toNat + 4096 ≤ 2 ^ 32 := by have := h.ctx.fit; omega_using [this]
  obtain fr0 : ∀ d, d + 4 ≤ ACC → wd s.mem (State.addr b) d = wd s0.mem (State.addr b) d := fun d hd =>
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by omega_using [hd])) (by omega_using [hd, hA]) (by omega_using [hA])
  simp only [rowU, List.cons_append, List.nil_append]
  -- The row's word of the first operand.
  refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (x + 4 * (2 * i))) (by decide)
    (by rw [h.r5, addB hfit (by omega_using [hx, hA, hi]), show x + 8 * i + 0 = x + 4 * (2 * i) by omega_arith])
    (h.ctx.inR (by omega_using [hx, hA, hi])) fun s1 u1 => ?_
  refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (x + 4 * (2 * i + 1))) (by decide)
    (by rw [u1.other _ (by decide), h.r5, addB hfit (by omega_using [hx, hA, hi]),
          show x + 8 * i + 4 = x + 4 * (2 * i + 1) by omega_arith])
    (by rw [u1.rd, u1.wr]; exact h.ctx.inR (by omega_using [hx, hA, hi])) fun s2 u2 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s3 u3 => ?_
  refine wp_mov (op2_imm (by decide)) fun s4 u4 => ?_
  obtain r4 : Rest [.r1, .r2, .r3, .r4] s s4 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      (u4.rest (by decide))))
  obtain m4 : s4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
  obtain hc4 : CtxN e b s4 := h.ctx.of_rest r4 (by decide)
  obtain a0 : limb s0.mem (State.addr b) x (2 * i) < 65536 := hlx _ (by omega_using [hi])
  obtain a1 : limb s0.mem (State.addr b) x (2 * i + 1) < 65536 := hlx _ (by omega_using [hi])
  obtain e1 : (s4.gpr .r1).toNat = packW (limb s0.mem (State.addr b) x) i := by
    obtain q1 : (s2.gpr .r1).toNat = limb s0.mem (State.addr b) x (2 * i) := by
      rw [u2.other _ (by decide), u1.gpr]; exact fr0 _ (by omega_using [hx, hi])
    obtain q2 : (s2.gpr .r2).toNat = limb s0.mem (State.addr b) x (2 * i + 1) := by
      rw [u2.gpr, u1.mem]; exact fr0 _ (by omega_using [hx, hi])
    rw [u4.other _ (by decide), u3.gpr]
    change (s2.gpr .r1 + s2.gpr .r2 <<< 16).toNat = _
    rw [packed_toNat (by rw [q1]; exact a0) (by rw [q2]; exact a1), q1, q2]
    rfl
  obtain e7 : s4.gpr .r7 = b + BitVec.ofNat 32 (4 * i) := by rw [r4.gpr _ (by decide), h.r7]
  -- The chain.
  generalize hav : packW (limb s0.mem (State.addr b) x) i = av at e1
  let Bf : Nat → Nat := packW (limb s0.mem (State.addr b) y)
  let X : Nat → Nat := fun k => pwU s.mem (State.addr b) (i + k)
  refine WP.append (wp_range_flatMap (M := isa) (N := 8)
    (fun j t => CtxN e b t ∧ Rest [.r2, .r3, .r4] s4 t ∧ (t.gpr .r4).toNat = uc av Bf X 0 j ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 (ACC + 64 + 4 * i), 4 * j⟩] s4.mem t.mem ∧
      ∀ k < j, pwU t.mem (State.addr b) (i + k) = uo av Bf X 0 k)
    (fun j t hj ⟨tc, tr, t4, tf, to⟩ => ?_) 8 (Nat.le_refl _) s4
    ⟨hc4, Rest.refl _ _, by rw [u4.gpr]; rfl, Frame.refl _ _, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩)
    fun s5 ⟨c5, r5, c4, f5, o5⟩ => ?_
  · obtain eb : bwU t.mem (State.addr b) j = Bf j := by
      rw [bwU, wd_frame tf fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (.inl (by omega_using [hj])) (by omega_using [hA, hj]) (by omega_using [hA, hi, hj]),
        m4]
      exact h.bw j hj
    obtain ex : pwU t.mem (State.addr b) (i + j) = X j := by
      rw [pwU, wd_frame tf fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (.inr (by omega_using [])) (by omega_using [hA, hi, hj]) (by omega_using [hA, hi, hj]),
        m4]
    refine WP.mono (rowStepU_ok hi hj tc ((tr.gpr _ (by decide)).trans e7)) fun t' ⟨g4, g3, gm, gr⟩ => ?_
    rw [tr.gpr .r1 (by decide), e1, eb, t4, ex] at g4 g3
    refine ⟨tc.of_rest gr (by decide), tr.trans gr, by rw [g4, uc_succ], ?_, fun k hk => ?_⟩
    · rw [gm]
      refine (tf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega_using []) (by omega_using []) (by omega_using [hA, hi, hj]))
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (Nat.le_refl _) (by omega_using [])
    · rw [pwU, gm]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · rw [wd_write_other _ _ _ (by omega_using [hk]) (by omega_using [hA, hi, hk, hj]) (by omega_using [hA, hi, hj])]
        exact to k hk
      · rw [wd_write_self, g3, uo]
  -- The carry, and the pointers and the counter.
  obtain e7' : s5.gpr .r7 = b + BitVec.ofNat 32 (4 * i) := by rw [r5.gpr _ (by decide), e7]
  refine wp_str (a := State.addr b + BitVec.ofNat 64 (ACC + 64 + 4 * (i + 8))) (by omega_using [hA])
    (by rw [e7', ea7 hfit (by omega_using [hA, hi]), show 4 * i + (ACC + 96) = ACC + 64 + 4 * (i + 8) by omega_arith])
    (c5.inW (by omega_using [hA, hi])) fun s6 u6 => ?_
  refine wp_dp (op2_imm (by decide)) fun s7 u7 => ?_
  refine wp_dp (op2_imm (by decide)) fun s8 u8 => ?_
  refine wp_subs (op2_imm (by decide)) fun s9 u9 hz => WP.block_nil ?_
  obtain r9 : Rest [.r1, .r2, .r3, .r4, .r5, .r7, .r9] s s9 :=
    (r4.mono (by decide)).trans ((r5.mono (by decide)).trans ((u6.rest _).trans
      ((u7.rest (by decide)).trans ((u8.rest (by decide)).trans (u9.rest (by decide))))))
  obtain m9 : s9.mem = s5.mem.writeW (State.addr b + BitVec.ofNat 64 (ACC + 64 + 4 * (i + 8))) (s5.gpr .r4) := by
    rw [u9.mem, u8.mem, u7.mem, u6.mem]
  obtain f59 : Frame [⟨State.addr b + BitVec.ofNat 64 (ACC + 64 + 4 * i), 36⟩] s.mem s9.mem := by
    rw [m9, ← m4]
    refine (f5.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by omega_using []) (by omega_using []) (by omega_using [hA, hi]))
    rw [List.mem_singleton.mp hr]; exact Offset.sub _ (Nat.le_refl _) (by omega_using [])
  obtain lo : ∀ k < i, pwU s9.mem (State.addr b) k = pwU s.mem (State.addr b) k := fun k hk =>
    wd_frame f59 fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by omega_using [hk])) (by omega_using [hA, hi, hk]) (by omega_using [hA, hi])
  obtain mid : ∀ k < 8, pwU s9.mem (State.addr b) (i + k) = uo av Bf X 0 k := fun k hk => by
    rw [pwU, m9, wd_write_other _ _ _ (by omega_using [hk]) (by omega_using [hA, hi, hk]) (by omega_using [hA, hi])]
    exact o5 k hk
  obtain top : pwU s9.mem (State.addr b) (i + 8) = uc av Bf X 0 8 := by
    rw [pwU, m9, wd_write_self, c4]
  obtain he : s.gpr .r9 - (1 : BitVec 32) = BitVec.ofNat 32 (8 - (i + 1)) := by
    change s.gpr .r9 - BitVec.ofNat 32 1 = _
    rw [h.r9, show 8 - i = 8 - (i + 1) + 1 by omega_using [hi], BitVec.ofNat_add, BitVec.add_sub_cancel]
  obtain g9 : s8.gpr .r9 = s.gpr .r9 := by
    rw [u8.other _ (by decide), u7.other _ (by decide), u6.gpr, r5.gpr _ (by decide), r4.gpr _ (by decide)]
  refine ⟨⟨h.ctx.of_rest r9 (by decide), h.rest.trans (r9.mono (by decide)), ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, ?_⟩,
    ?_⟩
  · rw [u9.other _ (by decide), u8.other _ (by decide), u7.gpr]
    change s6.gpr .r7 + BitVec.ofNat 32 4 = _
    rw [u6.gpr, e7', Offset.add_add, show 4 * i + 4 = 4 * (i + 1) by omega_arith]
  · rw [u9.other _ (by decide), u8.gpr]
    change s7.gpr .r5 + BitVec.ofNat 32 8 = _
    rw [u7.other _ (by decide), u6.gpr, r5.gpr _ (by decide), r4.gpr _ (by decide), h.r5, Offset.add_add,
      show x + 8 * i + 8 = x + 8 * (i + 1) by omega_arith]
  · rw [r9.gpr _ (by decide), h.r8]
  · rw [u9.gpr, g9]; exact he
  · refine h.frame.trans (f59.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_using []) (by omega_using [hi])
  · rw [bwU, wd_frame f59 fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by omega_using [hj])) (by omega_using [hA, hj]) (by omega_using [hA, hi])]
    exact h.bw j hj
  · obtain hv := h.val
    rw [val32_append _ i 8] at hv
    rw [show i + 1 + 8 = i + 9 by omega_arith, val32_append _ i 9, val32_congr lo, val32_succ,
      val32_congr mid, top]
    obtain hc8 := uc_val av Bf X 0 8
    rw [Nat.add_zero] at hc8
    rw [hc8, val32_succ (packW (limb s0.mem (State.addr b) x)) i, hav]
    exact rowU_arith rfl hv
  · rw [hz, g9, he]
    exact (ofNat_beq_zero (by omega_using [hi])).trans (decide_eq_decide.mpr (by omega_using [hi]))

/-! ## The result -/

/-- Word `q` of `lo + 38 hi`. -/
theorem foldStepU_ok {q : Nat} (hq : q < 8) {s : State} (hc : CtxN e b s) (h8 : s.gpr .r8 = 38) :
    WP isa (.block (foldStepU q)) s fun t =>
      (t.gpr .r4).toNat = (38 * pwU s.mem (State.addr b) (8 + q) + (s.gpr .r4).toNat +
        pwU s.mem (State.addr b) q) / 2 ^ 32 ∧
      (t.gpr .r3).toNat = (38 * pwU s.mem (State.addr b) (8 + q) + (s.gpr .r4).toNat +
        pwU s.mem (State.addr b) q) % 2 ^ 32 ∧
      t.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 (ACC + 64 + 4 * q)) (t.gpr .r3) ∧
      Rest [.r2, .r3, .r4] s t := by
  have hA := ACC_eq
  unfold foldStepU
  refine ldr0_ok hc (d := ACC + 64 + 4 * q) (by omega_using [hA, hq]) fun s1 u1 => ?_
  refine ldr0_ok (hc.of_rest (u1.rest (ws := [.r3]) (by decide)) (by decide)) (d := ACC + 96 + 4 * q)
    (by omega_using [hA, hq]) fun s2 u2 => ?_
  obtain e3 : (s2.gpr .r3).toNat = pwU s.mem (State.addr b) q := by rw [u2.other _ (by decide), u1.gpr]; rfl
  obtain e2 : (s2.gpr .r2).toNat = pwU s.mem (State.addr b) (8 + q) := by
    rw [u2.gpr, u1.mem, pwU, show ACC + 64 + 4 * (8 + q) = ACC + 96 + 4 * q by omega_arith]; rfl
  obtain e8 : (s2.gpr .r8).toNat = 38 := by rw [u2.other _ (by decide), u1.other _ (by decide), h8]; rfl
  obtain e4 : s2.gpr .r4 = s.gpr .r4 := by rw [u2.other _ (by decide), u1.other _ (by decide)]
  refine wp_umaal (by decide) (umaal_lt (s2.gpr .r8).isLt (s2.gpr .r2).isLt (s2.gpr .r4).isLt
    (s2.gpr .r3).isLt) fun s3 u3 => ?_
  obtain r3 : Rest [.r2, .r3, .r4] s s3 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide) (by decide)))
  refine str0_ok (hc.of_rest r3 (by decide)) (d := ACC + 64 + 4 * q) (by omega_using [hA, hq]) fun s4 u4 =>
    WP.block_nil ⟨?_, ?_, ?_, r3.trans (u4.rest _)⟩
  · rw [u4.gpr, u3.ghi, e8, e2, e3, e4]
  · rw [u4.gpr, u3.glo, e8, e2, e3, e4]
  · rw [u4.mem, u3.mem, u2.mem, u1.mem, u4.gpr]

/-- `lo + 38 hi` of the product's words, in its low words, and its carry out in `r4`. -/
theorem foldPassU_ok {s : State} (hc : CtxN e b s) (h8 : s.gpr .r8 = 38) (h4 : (s.gpr .r4).toNat = 0) :
    WP isa (.block ((List.range 8).flatMap foldStepU)) s fun t =>
      CtxN e b t ∧ Rest [.r2, .r3, .r4] s t ∧
      (t.gpr .r4).toNat = uc 38 (fun q => pwU s.mem (State.addr b) (8 + q)) (pwU s.mem (State.addr b)) 0 8 ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 (ACC + 64), 4 * 8⟩] s.mem t.mem ∧
      ∀ k < 8, pwU t.mem (State.addr b) k =
        uo 38 (fun q => pwU s.mem (State.addr b) (8 + q)) (pwU s.mem (State.addr b)) 0 k := by
  have hA := ACC_eq
  let Hi : Nat → Nat := fun q => pwU s.mem (State.addr b) (8 + q)
  let Lo : Nat → Nat := pwU s.mem (State.addr b)
  refine wp_range_flatMap (M := isa) (N := 8)
    (fun n t => CtxN e b t ∧ Rest [.r2, .r3, .r4] s t ∧ (t.gpr .r4).toNat = uc 38 Hi Lo 0 n ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 (ACC + 64), 4 * n⟩] s.mem t.mem ∧
      ∀ k < n, pwU t.mem (State.addr b) k = uo 38 Hi Lo 0 k)
    (fun n t hn ⟨tc, tr, t4, tf, to⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨hc, Rest.refl _ _, h4, Frame.refl _ _, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩
  obtain eh : pwU t.mem (State.addr b) (8 + n) = Hi n := wd_frame tf fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inr (by omega_using [hn])) (by omega_using [hA, hn]) (by omega_using [hA, hn])
  obtain el : pwU t.mem (State.addr b) n = Lo n := wd_frame tf fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inr (by omega_using [])) (by omega_using [hA, hn]) (by omega_using [hA, hn])
  refine WP.mono (foldStepU_ok hn tc ((tr.gpr _ (by decide)).trans h8)) fun t' ⟨g4, g3, gm, gr⟩ => ?_
  rw [eh, t4, el] at g4 g3
  refine ⟨tc.of_rest gr (by decide), tr.trans gr, by rw [g4, uc_succ], ?_, fun k hk => ?_⟩
  · rw [gm]
    refine (tf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by omega_using []) (by omega_using []) (by omega_using [hA, hn]))
    rw [List.mem_singleton.mp hr]; exact Offset.sub _ (Nat.le_refl _) (by omega_using [])
  · rw [pwU, gm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [wd_write_other _ _ _ (by omega_using [hk]) (by omega_using [hA, hk, hn]) (by omega_using [hA, hn])]
      exact to k hk
    · rw [wd_write_self, g3, uo]

/-- The carry into word `k + 1` of a sum of words and a carry. -/
theorem uc_zero_succ (x : Nat → Nat) (cin k : Nat) :
    uc 0 (fun _ => 0) x cin (k + 1) = (uc 0 (fun _ => 0) x cin k + x k) / 2 ^ 32 := by
  rw [uc_succ, Nat.zero_mul, Nat.zero_add]

/-- Word `k` of a sum of words and a carry. -/
theorem uo_zero (x : Nat → Nat) (cin k : Nat) :
    uo 0 (fun _ => 0) x cin k = (uc 0 (fun _ => 0) x cin k + x k) % 2 ^ 32 := by
  rw [uo, Nat.zero_mul, Nat.zero_add]

/-- Word `q` of the sum plus the carry `r4`, as two limbs of the result. -/
theorem splitStepU_ok {o q : Nat} (ho : o + 64 ≤ ACC) (hq : q < 8) {s : State} (hc : CtxN e b s)
    (h9 : s.gpr .r9 = b + BitVec.ofNat 32 o) (h6 : s.gpr .r6 = mask16) (h2 : (s.gpr .r2).toNat = 0) :
    WP isa (.block (splitStepU q)) s fun t =>
      (t.gpr .r4).toNat = ((s.gpr .r4).toNat + pwU s.mem (State.addr b) q) / 2 ^ 32 ∧
      t.mem = (s.mem.writeW (State.addr b + BitVec.ofNat 64 (o + 4 * (2 * q)))
          (BitVec.ofNat 32 (((s.gpr .r4).toNat + pwU s.mem (State.addr b) q) % 2 ^ 32 % 65536))).writeW
        (State.addr b + BitVec.ofNat 64 (o + 4 * (2 * q + 1)))
        (BitVec.ofNat 32 (((s.gpr .r4).toNat + pwU s.mem (State.addr b) q) % 2 ^ 32 / 65536)) ∧
      Rest [.r1, .r3, .r4] s t := by
  have hA := ACC_eq
  obtain hfit : b.toNat + 4096 ≤ 2 ^ 32 := by have := hc.fit; omega_using [this]
  unfold splitStepU
  refine ldr0_ok hc (d := ACC + 64 + 4 * q) (by omega_using [hA, hq]) fun s1 u1 => ?_
  obtain e3 : (s1.gpr .r3).toNat = pwU s.mem (State.addr b) q := by rw [u1.gpr]; rfl
  obtain e2 : (s1.gpr .r2).toNat = 0 := by rw [u1.other _ (by decide), h2]
  obtain e4 : s1.gpr .r4 = s.gpr .r4 := u1.other _ (by decide)
  refine wp_umaal (by decide) (umaal_lt (s1.gpr .r2).isLt (s1.gpr .r2).isLt (s1.gpr .r4).isLt
    (s1.gpr .r3).isLt) fun s2 u2 => ?_
  obtain eR : (s1.gpr .r2).toNat * (s1.gpr .r2).toNat + (s1.gpr .r4).toNat + (s1.gpr .r3).toNat =
      (s.gpr .r4).toNat + pwU s.mem (State.addr b) q := by
    rw [e2, e3, e4, Nat.zero_mul, Nat.zero_add]
  obtain g3 : (s2.gpr .r3).toNat = ((s.gpr .r4).toNat + pwU s.mem (State.addr b) q) % 2 ^ 32 := by
    rw [u2.glo, eR]
  obtain g4 : (s2.gpr .r4).toNat = ((s.gpr .r4).toNat + pwU s.mem (State.addr b) q) / 2 ^ 32 := by
    rw [u2.ghi, eR]
  refine wp_dp (op2_reg _ _) fun s3 u3 => ?_
  obtain r3 : Rest [.r1, .r3, .r4] s s3 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide) (by decide)).trans (u3.rest (by decide)))
  refine wp_str (a := State.addr b + BitVec.ofNat 64 (o + 4 * (2 * q))) (by omega_using [hq])
    (by rw [r3.gpr _ (by decide), h9, addB hfit (by omega_using [ho, hA, hq]),
          show o + 8 * q = o + 4 * (2 * q) by omega_arith])
    ((hc.of_rest r3 (by decide)).inW (by omega_using [ho, hA, hq])) fun s4 u4 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s5 u5 => ?_
  obtain r5 : Rest [.r1, .r3, .r4] s s5 := r3.trans ((u4.rest _).trans (u5.rest (by decide)))
  refine wp_str (a := State.addr b + BitVec.ofNat 64 (o + 4 * (2 * q + 1))) (by omega_using [hq])
    (by rw [r5.gpr _ (by decide), h9, addB hfit (by omega_using [ho, hA, hq]),
          show o + (8 * q + 4) = o + 4 * (2 * q + 1) by omega_arith])
    ((hc.of_rest r5 (by decide)).inW (by omega_using [ho, hA, hq])) fun s6 u6 =>
      WP.block_nil ⟨?_, ?_, r5.trans (u6.rest _)⟩
  · rw [u6.gpr, u5.other _ (by decide), u4.gpr, u3.other _ (by decide), g4]
  · obtain lt1 : ((s.gpr .r4).toNat + pwU s.mem (State.addr b) q) % 2 ^ 32 % 65536 < 2 ^ 32 :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
    obtain lt2 : ((s.gpr .r4).toNat + pwU s.mem (State.addr b) q) % 2 ^ 32 / 65536 < 2 ^ 32 :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (by decide))
    obtain v1 : s3.gpr .r1 =
        BitVec.ofNat 32 (((s.gpr .r4).toNat + pwU s.mem (State.addr b) q) % 2 ^ 32 % 65536) := by
      apply BitVec.eq_of_toNat_eq
      rw [u3.gpr]
      change (s2.gpr .r3 &&& s2.gpr .r6).toNat = _
      rw [u2.other .r6 (by decide) (by decide), u1.other .r6 (by decide), h6, toNat_and_mask16, g3,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt lt1]
    obtain v3 : s5.gpr .r3 =
        BitVec.ofNat 32 (((s.gpr .r4).toNat + pwU s.mem (State.addr b) q) % 2 ^ 32 / 65536) := by
      apply BitVec.eq_of_toNat_eq
      rw [u5.gpr, toNat_shr, u4.gpr, u3.other _ (by decide), g3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt lt2]
    rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, v3, v1]

/-- The words of the sum plus a carry `cin`, as the limbs of the result, and the carry out in
`r4`. -/
theorem splitPassU_ok {o : Nat} (ho : o + 64 ≤ ACC) {s : State} (hc : CtxN e b s)
    (h9 : s.gpr .r9 = b + BitVec.ofNat 32 o) (h6 : s.gpr .r6 = mask16) (h2 : (s.gpr .r2).toNat = 0)
    {cin : Nat} (h4 : (s.gpr .r4).toNat = cin) :
    WP isa (.block ((List.range 8).flatMap splitStepU)) s fun t =>
      CtxN e b t ∧ Rest [.r1, .r3, .r4] s t ∧
      (t.gpr .r4).toNat = uc 0 (fun _ => 0) (pwU s.mem (State.addr b)) cin 8 ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 o, 8 * 8⟩] s.mem t.mem ∧
      ∀ k < 16, limb t.mem (State.addr b) o k =
        wordLimb (uo 0 (fun _ => 0) (pwU s.mem (State.addr b)) cin) k := by
  have hA := ACC_eq
  let X : Nat → Nat := pwU s.mem (State.addr b)
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8)
    (fun n t => CtxN e b t ∧ Rest [.r1, .r3, .r4] s t ∧ (t.gpr .r4).toNat = uc 0 (fun _ => 0) X cin n ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 o, 8 * n⟩] s.mem t.mem ∧
      ∀ k < n, limb t.mem (State.addr b) o (2 * k) = uo 0 (fun _ => 0) X cin k % 65536 ∧
        limb t.mem (State.addr b) o (2 * k + 1) = uo 0 (fun _ => 0) X cin k / 65536)
    (fun n t hn ⟨tc, tr, t4, tf, to⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨hc, Rest.refl _ _, h4, Frame.refl _ _, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩)
    fun t ⟨tc, tr, t4, tf, to⟩ => ⟨tc, tr, t4, tf, fun k hk => ?_⟩
  · obtain ex : pwU t.mem (State.addr b) n = X n := wd_frame tf fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inr (by omega_using [ho, hn])) (by omega_using [hA, hn])
        (by omega_using [ho, hA, hn])
    refine WP.mono (splitStepU_ok ho hn tc ((tr.gpr _ (by decide)).trans h9) ((tr.gpr _ (by decide)).trans h6)
      (by rw [tr.gpr _ (by decide), h2])) fun t' ⟨g4, gm, gr⟩ => ?_
    rw [t4, ex, ← uo_zero] at gm
    rw [t4, ex, ← uc_zero_succ] at g4
    obtain lt1 : uo 0 (fun _ => 0) X cin n % 65536 < 2 ^ 32 :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
    obtain lt2 : uo 0 (fun _ => 0) X cin n / 65536 < 2 ^ 32 :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (by decide))
    refine ⟨tc.of_rest gr (by decide), tr.trans gr, g4, ?_, fun k hk => ?_⟩
    · rw [gm]
      refine ((tf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega_using []) (by omega_using []) (by omega_using [ho, hA, hn]))).writeW
        (List.mem_singleton_self _) _
        (Offset.contains _ (by omega_using []) (by omega_using []) (by omega_using [ho, hA, hn]))
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (Nat.le_refl _) (by omega_using [])
    · rw [limb, limb, gm]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · rw [wd_write_other _ _ _ (by omega_using [hk]) (by omega_using [ho, hA, hk, hn]) (by omega_using [ho, hA, hn]),
          wd_write_other _ _ _ (by omega_using [hk]) (by omega_using [ho, hA, hk, hn]) (by omega_using [ho, hA, hn]),
          wd_write_other _ _ _ (by omega_using [hk]) (by omega_using [ho, hA, hk, hn]) (by omega_using [ho, hA, hn]),
          wd_write_other _ _ _ (by omega_using [hk]) (by omega_using [ho, hA, hk, hn]) (by omega_using [ho, hA, hn])]
        exact to k hk
      · rw [wd_write_other _ _ _ (by omega_using []) (by omega_using [ho, hA, hn]) (by omega_using [ho, hA, hn]),
          wd_write_self, wd_write_self, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt lt1,
          Nat.mod_eq_of_lt lt2]
        exact ⟨rfl, rfl⟩
  · obtain ⟨q, rfl | rfl⟩ : ∃ q, k = 2 * q ∨ k = 2 * q + 1 := ⟨k / 2, by omega_arith⟩
    · rw [(to q (by omega_using [hk])).1, wordLimb, ite_eq_left (by omega_arith),
        show 2 * q / 2 = q by omega_arith]
    · rw [(to q (by omega_using [hk])).2, wordLimb, ite_eq_right (by omega_arith),
        show (2 * q + 1) / 2 = q by omega_arith]

/-- The reduction's congruence: `lo + 38 hi = w + 2²⁵⁶ c₁`, then `w + 38 c₁ = out + 2²⁵⁶ c₂`, and
`out + 38 c₂` is the result. -/
theorem foldU_arith {lo hi w c1 out c2 : Nat} (h1 : w + 2 ^ 256 * c1 = 38 * hi + lo)
    (h2 : out + 2 ^ 256 * c2 = w + 38 * c1) : (out + 38 * c2) % P = (lo + 2 ^ 256 * hi) % P := by
  rw [← VG.Proof.X25519.fold256 out c2, h2, ← VG.Proof.X25519.fold256 w c1, h1, VG.Proof.X25519.fold256 lo hi,
    Nat.add_comm]

/-- After the rows: the result at `o`, below `2^16` limb by limb and congruent to the product. -/
theorem mulFinalU_ok {o x y : Nat} (ho : o + 64 ≤ ACC) {s0 s : State} (h : InvU e b o x y s0 8 s) :
    WP isa (.block mulFinalU) s fun t =>
      Rest clob s0 t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩, ⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] s.mem t.mem ∧
      Lim t.mem (State.addr b) o ∧
      V t.mem (State.addr b) o % P = val32 (pwU s.mem (State.addr b)) 16 % P := by
  have hA := ACC_eq
  obtain hfit : b.toNat + 4096 ≤ 2 ^ 32 := by have := h.ctx.fit; omega_using [this]
  obtain B9 : State.addr (b + BitVec.ofNat 32 o) = State.addr b + BitVec.ofNat 64 o :=
    addrO' hfit (by omega_using [ho, hA])
  have t38 : (38 : BitVec 32).toNat = 38 := rfl
  simp only [mulFinalU, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_mov (op2_reg _ _) fun s1 u1 => wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  refine wp_movw fun s2' u2' => wp_mov (op2_imm (by decide)) fun s3 u3 => ?_
  obtain hr3 : Rest [.r4, .r6, .r8, .r9] s s3 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u2'.rest (by decide)).trans
      (u3.rest (by decide))))
  obtain hc3 : CtxN e b s3 := h.ctx.of_rest hr3 (by decide)
  obtain hm3 : s3.mem = s.mem := by rw [u3.mem, u2'.mem, u2.mem, u1.mem]
  obtain e9 : s3.gpr .r9 = b + BitVec.ofNat 32 o := by
    rw [u3.other _ (by decide), u2'.other _ (by decide), u2.other _ (by decide), u1.gpr, h.r8]
  obtain e8 : s3.gpr .r8 = 38 := by rw [u3.other _ (by decide), u2'.other _ (by decide), u2.gpr]
  obtain e6 : s3.gpr .r6 = mask16 := by rw [u3.other _ (by decide), u2'.gpr]
  -- `lo + 38 hi`, in words.
  refine WP.append (foldPassU_ok hc3 e8 (by rw [u3.gpr]; rfl)) fun s4 ⟨c4, r4, g4, f4, o4⟩ => ?_
  rw [hm3] at g4 f4 o4
  let Hi : Nat → Nat := fun q => pwU s.mem (State.addr b) (8 + q)
  let Lo : Nat → Nat := pwU s.mem (State.addr b)
  obtain hv1 := uc_val 38 Hi Lo 0 8
  obtain hHi : val32 Hi 8 < 2 ^ (32 * 8) := val32_lt fun _ _ => wd_lt _ _ _
  obtain hLo : val32 Lo 8 < 2 ^ (32 * 8) := val32_lt fun _ _ => wd_lt _ _ _
  obtain hW : val32 (uo 38 Hi Lo 0) 8 < 2 ^ (32 * 8) := val32_lt fun _ _ => Nat.mod_lt _ (by decide)
  rw [show 32 * 8 = 256 from rfl] at hv1 hHi hLo hW
  rw [Nat.add_zero] at hv1
  generalize uc 38 Hi Lo 0 8 = c1 at g4 hv1
  obtain hc1 : c1 ≤ 38 := by
    have : 2 ^ 256 * c1 < 2 ^ 256 * 39 := by omega_using [hv1, hHi, hLo]
    have := Nat.lt_of_mul_lt_mul_left this
    omega_using [this]
  -- 38 times the carry, and zero.
  refine wp_mul fun s5 u5 => wp_mov (op2_imm (by decide)) fun s6 u6 => ?_
  obtain r46 : Rest [.r2, .r4] s4 s6 := (u5.rest (by decide)).trans (u6.rest (by decide))
  obtain c6 : CtxN e b s6 := c4.of_rest r46 (by decide)
  obtain m6 : s6.mem = s4.mem := by rw [u6.mem, u5.mem]
  obtain g6 : (s6.gpr .r4).toNat = 38 * c1 := by
    rw [u6.other _ (by decide), u5.gpr, r4.gpr .r8 (by decide), e8,
      toNat_mul_lt (by rw [g4, t38]; omega_using [hc1]), g4, t38]
    exact Nat.mul_comm _ _
  obtain e9a : s6.gpr .r9 = b + BitVec.ofNat 32 o := by rw [r46.gpr _ (by decide), r4.gpr _ (by decide), e9]
  obtain e6a : s6.gpr .r6 = mask16 := by rw [r46.gpr _ (by decide), r4.gpr _ (by decide), e6]
  obtain e8a : s6.gpr .r8 = 38 := by rw [r46.gpr _ (by decide), r4.gpr _ (by decide), e8]
  -- The words, with the carry, as limbs.
  refine WP.append (splitPassU_ok ho c6 e9a e6a (by rw [u6.gpr]; rfl) g6) fun s7 ⟨c7, r7, g7, f7, l7⟩ => ?_
  let X2 : Nat → Nat := pwU s6.mem (State.addr b)
  obtain eX : val32 X2 8 = val32 (uo 38 Hi Lo 0) 8 := val32_congr fun k hk => by
    show pwU s6.mem (State.addr b) k = _
    rw [m6]; exact o4 k hk
  obtain hv2 := uc_val 0 (fun _ => 0) X2 (38 * c1) 8
  obtain hOut : val32 (uo 0 (fun _ => 0) X2 (38 * c1)) 8 < 2 ^ (32 * 8) :=
    val32_lt fun _ _ => Nat.mod_lt _ (by decide)
  obtain h0 : uo 0 (fun _ => 0) X2 (38 * c1) 0 ≤ val32 (uo 0 (fun _ => 0) X2 (38 * c1)) 8 := by
    rw [VG.Proof.X25519.Arm.Words.val32_cons]; exact Nat.le_add_right _ _
  rw [show 32 * 8 = 256 from rfl, Nat.zero_mul, Nat.zero_add, eX] at hv2
  rw [show 32 * 8 = 256 from rfl] at hOut
  generalize uc 0 (fun _ => 0) X2 (38 * c1) 8 = c2 at g7 hv2
  obtain hc2 : c2 ≤ 1 := by
    have : 2 ^ 256 * c2 < 2 ^ 256 * 2 := by omega_using [hv2, hW, hc1]
    have := Nat.lt_of_mul_lt_mul_left this
    omega_using [this]
  obtain hl0 : wordLimb (uo 0 (fun _ => 0) X2 (38 * c1)) 0 + 38 * c2 < 65536 := by
    have hw : wordLimb (uo 0 (fun _ => 0) X2 (38 * c1)) 0 = uo 0 (fun _ => 0) X2 (38 * c1) 0 % 65536 := rfl
    have hm := Nat.mod_le (uo 0 (fun _ => 0) X2 (38 * c1) 0) 65536
    have hlt := Nat.mod_lt (uo 0 (fun _ => 0) X2 (38 * c1) 0) (show 0 < 65536 by decide)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc2 with hz | ho1
    · rw [hz]; omega_using [hw, hlt]
    · rw [ho1] at hv2 ⊢; omega_using [hw, hm, h0, hv2, hW, hc1]
  -- 38 times the carry out into limb 0.
  obtain e9b : s7.gpr .r9 = b + BitVec.ofNat 32 o := by rw [r7.gpr _ (by decide), e9a]
  refine wp_mul fun s8 u8 => ?_
  obtain g8 : (s8.gpr .r4).toNat = 38 * c2 := by
    rw [u8.gpr, r7.gpr .r8 (by decide), e8a, toNat_mul_lt (by rw [g7, t38]; omega_using [hc2]), g7, t38]
    exact Nat.mul_comm _ _
  refine wp_ldr (a := State.addr b + BitVec.ofNat 64 o) (by decide)
    (by rw [u8.other _ (by decide), e9b, BitVec.add_zero, B9])
    (by rw [u8.rd, u8.wr]; exact c7.inR (by omega_using [ho, hA])) fun s9 u9 => ?_
  refine wp_dp (op2_reg _ _) fun s10 u10 => ?_
  obtain e9c : s10.gpr .r9 = b + BitVec.ofNat 32 o := by
    rw [u10.other _ (by decide), u9.other _ (by decide), u8.other _ (by decide), e9b]
  refine wp_str (a := State.addr b + BitVec.ofNat 64 o) (by decide)
    (by rw [e9c, BitVec.add_zero, B9])
    (by rw [u10.wr, u9.wr, u8.wr]; exact c7.inW (by omega_using [ho, hA])) fun s11 u11 => WP.block_nil ?_
  obtain l0 := l7 0 (by decide)
  rw [limb, Nat.mul_zero, Nat.add_zero] at l0
  obtain g10 : (s10.gpr .r3).toNat = wordLimb (uo 0 (fun _ => 0) X2 (38 * c1)) 0 + 38 * c2 := by
    rw [u10.gpr]
    show (s9.gpr .r3 + s9.gpr .r4).toNat = _
    obtain q3 : (s9.gpr .r3).toNat = wordLimb (uo 0 (fun _ => 0) X2 (38 * c1)) 0 := by
      rw [u9.gpr, u8.mem]; exact l0
    rw [toNat_add_lt (by rw [q3, u9.other .r4 (by decide), g8]; omega_using [hl0]), q3,
      u9.other .r4 (by decide), g8]
  obtain m11 : s11.mem = s7.mem.writeW (State.addr b + BitVec.ofNat 64 o) (s10.gpr .r3) := by
    rw [u11.mem, u10.mem, u9.mem, u8.mem]
  obtain hlimb : ∀ k < 16, limb s11.mem (State.addr b) o k =
      (fun k => if k = 0 then wordLimb (uo 0 (fun _ => 0) X2 (38 * c1)) 0 + 38 * c2
        else wordLimb (uo 0 (fun _ => 0) X2 (38 * c1)) k) k := by
    intro k hk
    rw [limb, m11]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [Nat.mul_zero, Nat.add_zero, wd_write_self, g10]; rfl
    · rw [wd_write_other _ _ _ (by omega_using [hk0]) (by omega_using [ho, hA, hk]) (by omega_using [ho, hA])]
      exact (l7 k hk).trans (ite_eq_right (Nat.ne_of_gt hk0)).symm
  refine ⟨?_, ?_, fun k hk => ?_, ?_⟩
  · exact h.rest.trans ((hr3.mono (by decide)).trans ((r4.mono (by decide)).trans ((r46.mono (by decide)).trans
      ((r7.mono (by decide)).trans ((u8.rest (by decide)).trans ((u9.rest (by decide)).trans
        ((u10.rest (by decide)).trans (u11.rest _))))))))
  · rw [m11]
    refine Frame.writeW (Frame.trans (f4.sub fun r hr => ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩)
      (Frame.sub (by rw [← m6]; exact f7) fun r hr => ⟨_, List.mem_cons_self, ?_⟩)) List.mem_cons_self _
      (Offset.contains (State.addr b) (d := o) (n := 4) (e := o) (k := 64) (Nat.le_refl _)
        (by omega_using []) (by omega_using [ho, hA]))
    · rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_using []) (by omega_using [])
    · rw [List.mem_singleton.mp hr]; exact Offset.sub _ (Nat.le_refl _) (by omega_using [])
  · rw [hlimb k hk]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact hl0
    · show (if k = 0 then _ else wordLimb _ k) < 65536
      rw [ite_eq_right (Nat.ne_of_gt hk0)]
      exact wordLimb_lt (fun _ => Nat.mod_lt _ (by decide)) k
  · rw [V, val16_congr hlimb, val16_add_head (wordLimb (uo 0 (fun _ => 0) X2 (38 * c1))) (38 * c2) (by decide),
      show (16 : Nat) = 2 * 8 from rfl, val16_wordLimb, show (2 * 8 : Nat) = 8 + 8 from rfl,
      val32_append _ 8 8, show 32 * 8 = 256 from rfl]
    exact foldU_arith hv1 hv2

/-- The product of `[x]` and `[y]` into `[o]` with `umaal`, the offsets in `r1`–`r3`: the
baseline's contract (`mulBody_ok`), and no register changed but `r1`–`r9`. -/
theorem mulBodyU_ok {o x y : Nat} (ho : o + 64 ≤ ACC) (hx : x + 64 ≤ ACC) (hy : y + 64 ≤ ACC)
    {s : State} (hc : CtxN e b s) (h1 : s.gpr .r1 = BitVec.ofNat 32 o) (h2 : s.gpr .r2 = BitVec.ofNat 32 x)
    (h3 : s.gpr .r3 = BitVec.ofNat 32 y) (hlx : Lim s.mem (State.addr b) x)
    (hly : Lim s.mem (State.addr b) y) :
    WP isa mulBodyU s fun t =>
      Rest clob s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩, ⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] s.mem t.mem ∧
      Lim t.mem (State.addr b) o ∧
      V t.mem (State.addr b) o % P = (V s.mem (State.addr b) x * V s.mem (State.addr b) y) % P := by
  unfold mulBodyU
  refine WP.seq (WP.mono (mulSetupU_ok (o := o) (x := x) hy hc h1 h2 h3 hly) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (Q := InvU e b o x y s 8) (WP.loop (M := isa)
    (fun n s' => ∃ i, n = 8 - i ∧ i < 8 ∧ InvU e b o x y s i s') ?_ 8 s1 ⟨0, rfl, by decide, h1⟩)
    fun s2 h2 => ?_)
  · rintro n s' ⟨i, rfl, hi, hr⟩
    refine WP.mono (rowU_ok hx hlx hi hr) fun t ⟨ht, hz⟩ => ?_
    by_cases h8 : i + 1 = 8
    · refine .inl ⟨by rw [eval_ne, hz, decide_eq_true h8]; rfl, ?_⟩
      rw [h8] at ht
      exact ht
    · exact .inr ⟨by rw [eval_ne, hz, decide_eq_false h8]; rfl,
        8 - (i + 1), by omega_using [hi], i + 1, rfl, by omega_using [hi, h8], ht⟩
  · refine WP.mono (mulFinalU_ok ho h2) fun t ⟨hrt, hft, hlt, hvt⟩ => ⟨hrt, ?_, hlt, ?_⟩
    · exact (h2.frame.mono fun r hr => by simp [List.mem_singleton.mp hr]).trans hft
    · rw [hvt, show (16 : Nat) = 8 + 8 from rfl, h2.val, V, V, show (16 : Nat) = 2 * 8 from rfl,
        val16_packW, val16_packW]

/-- The product of a function, with either multiplication: `mulBody_ok`. -/
theorem mulBodyFn_ok {umaal : Bool} {o x y : Nat} (ho : o + 64 ≤ ACC) (hx : x + 64 ≤ ACC) (hy : y + 64 ≤ ACC)
    {s : State} (hc : CtxN e b s) (h1 : s.gpr .r1 = BitVec.ofNat 32 o) (h2 : s.gpr .r2 = BitVec.ofNat 32 x)
    (h3 : s.gpr .r3 = BitVec.ofNat 32 y) (hlx : Lim s.mem (State.addr b) x)
    (hly : Lim s.mem (State.addr b) y) :
    WP isa (if umaal then mulBodyU else mulBody) s fun t =>
      Rest mulClob s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩, ⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] s.mem t.mem ∧
      Lim t.mem (State.addr b) o ∧
      V t.mem (State.addr b) o % P = (V s.mem (State.addr b) x * V s.mem (State.addr b) y) % P := by
  cases umaal
  · exact mulBody_ok ho hx hy hc h1 h2 h3 hlx hly
  · exact WP.mono (mulBodyU_ok ho hx hy hc h1 h2 h3 hlx hly) fun t ⟨hr, h⟩ => ⟨hr.mono (by decide), h⟩

/-- An offset of the working space, as `movw` loads it. -/
theorem movw_ofNat {n : Nat} (h : n < 65536) : ((BitVec.ofNat 16 n).setWidth 32) = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_using [h]

/-- **The inlined product**, with either multiplication: X25519's `mul_ok`. -/
theorem mulIn_ok {umaal : Bool} {o x y : Nat} (ho : o + 64 ≤ ACC) (hx : x + 64 ≤ ACC) (hy : y + 64 ≤ ACC)
    {s : State} (hc : CtxN e b s) (hlx : Lim s.mem (State.addr b) x) (hly : Lim s.mem (State.addr b) y) :
    WP isa (mulIn umaal o x y) s fun s' =>
      Rest clob s s' ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩, ⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] s.mem s'.mem ∧
      Lim s'.mem (State.addr b) o ∧
      V s'.mem (State.addr b) o % P = (V s.mem (State.addr b) x * V s.mem (State.addr b) y) % P := by
  have hA := ACC_eq
  cases umaal
  · exact mul_ok (by decide) ho hx hy hc hlx hly
  · show WP isa (.seq (.block (mulArgs o x y)) mulBodyU) s _
    rw [WP.seq_iff]
    unfold mulArgs
    refine wp_movw fun s1 u1 => wp_movw fun s2 u2 => wp_movw fun s3 u3 => WP.block_nil ?_
    obtain hr3 : Rest [.r1, .r2, .r3] s s3 :=
      (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
    obtain hm3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
    obtain e1 : s3.gpr .r1 = BitVec.ofNat 32 o := by
      rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr, movw_ofNat (by omega_using [ho, hA])]
    obtain e2 : s3.gpr .r2 = BitVec.ofNat 32 x := by
      rw [u3.other _ (by decide), u2.gpr, movw_ofNat (by omega_using [hx, hA])]
    obtain e3 : s3.gpr .r3 = BitVec.ofNat 32 y := by rw [u3.gpr, movw_ofNat (by omega_using [hy, hA])]
    refine WP.mono (mulBodyU_ok ho hx hy (hc.of_rest hr3 (by decide)) e1 e2 e3 (by rw [hm3]; exact hlx)
      (by rw [hm3]; exact hly)) fun t ⟨hr, hf, hl, hv⟩ =>
        ⟨(hr3.mono (by decide)).trans hr, by rw [← hm3]; exact hf, hl, by rw [hv, hm3]⟩

/-- The product's function calls nothing. -/
theorem mulFn_noCalls (umaal : Bool) : (mulFn umaal).noCalls = true := by cases umaal <;> decide +kernel

end

end VG.Proof.Ed25519.Arm

end

end

/-! ### `Ed25519.Arm.MulFnFn`, which only this module used -/

section

/-!
# `vg_gf25519_r16_mul` on ARMv7: the function

Untrusted: everything here is checked by Lean. `mulFn_ok`: `mulBody_ok`
(with `umaal`, `mulBodyU_ok`: `mulBodyFn_ok`, `Proof/Ed25519/Arm/FieldProg.lean`)
between saving the callee-saved registers the body changes (`r4`–`r11`) at
`SAVE` and restoring them (`Spill`): the function changes no register but
`r1`–`r3` and no memory but the result's and its own working space (`ACC`
and `SAVE`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.Arm

open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm
open VG.Spec.X25519 (P)

variable {umaal : Bool}

theorem SAVE_eq : SAVE = 1600 := rfl

theorem mulSaved_ok : Spill.Slots SAVE (SAVE + 32) mulSaved := by decide

theorem mulSaved_restorable : Spill.Restorable .r0 mulSaved := by decide

/-- The registers `vg_gf25519_r16_mul` changes. -/
abbrev mulFnClob : List Reg := [.r1, .r2, .r3]

theorem mulClob_split : ∀ r, r ∉ mulFnClob → r ∉ mulSaved.map Prod.fst → r ∉ mulClob := by
  intro r; cases r <;> decide

/-- **`vg_gf25519_r16_mul`**: the product of `[x]` and `[y]` into `[o]`, the offsets in
`r1`–`r3`, saving and restoring the registers its body changes. -/
theorem mulFn_ok {e : Nat} {b : BitVec 32} {o x y : Nat} (ho : o + 64 ≤ ACC) (hx : x + 64 ≤ ACC)
    (hy : y + 64 ≤ ACC) {s : State} (hc : CtxN e b s) (h1 : s.gpr .r1 = BitVec.ofNat 32 o)
    (h2 : s.gpr .r2 = BitVec.ofNat 32 x) (h3 : s.gpr .r3 = BitVec.ofNat 32 y)
    (hlx : Lim s.mem (State.addr b) x) (hly : Lim s.mem (State.addr b) y) :
    WP isa (mulFn umaal) s fun t =>
      Rest mulFnClob s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩, ⟨State.addr b + BitVec.ofNat 64 ACC, 160⟩] s.mem t.mem ∧
      Lim t.mem (State.addr b) o ∧
      V t.mem (State.addr b) o % P = (V s.mem (State.addr b) x * V s.mem (State.addr b) y) % P := by
  have hfit : b.toNat + 4096 ≤ 2 ^ 32 := by have := hc.fit; omega_using [this]
  have hS := SAVE_eq
  have hA := ACC_eq
  have hB : State.addr (s.gpr .r0) = State.addr b := by rw [hc.r0]
  rw [mulFn, WP.seq_iff]
  rw [← List.append_nil (List.map _ mulSaved)]
  refine Spill.save_slots_ok mulSaved_ok (by rw [hc.r0, hS]; omega_using [hfit])
    (fun d hd hd' => by rw [hB]; exact hc.inW (by rw [hS] at hd'; omega_using [hd'])) (WP.block_nil ?_)
  rw [hB]
  have hf1 : Frame [⟨State.addr b + BitVec.ofNat 64 SAVE, SAVE + 32 - SAVE⟩] s.mem
      (Spill.saveMem s.mem (State.addr b) s.gpr mulSaved) :=
    Spill.saveMem_frame_slots mulSaved_ok s.mem (State.addr b) s.gpr
  have hsv1 : Spill.Saved (Spill.saveMem s.mem (State.addr b) s.gpr mulSaved) (State.addr b) s.gpr
      mulSaved :=
    Spill.saveMem_saved (State.addr b) s.gpr s.mem mulSaved mulSaved_ok
  generalize Spill.saveMem s.mem (State.addr b) s.gpr mulSaved = M1 at hf1 hsv1 ⊢
  have hlimb : ∀ z : Nat, z + 64 ≤ ACC → ∀ k < 16, limb M1 (State.addr b) z k = limb s.mem (State.addr b) z k :=
    fun z hz => limb_frame hf1 fun r hr k hk => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by rw [hS]; omega_using [hA, hz, hk])) (by omega_using [hA, hz, hk]) (by omega_using [hS])
  obtain ⟨s₁, hs₁⟩ : ∃ s₁ : State, s₁ = { s with mem := M1 } := ⟨_, rfl⟩
  rw [← hs₁]
  have hm₁ : s₁.mem = M1 := by rw [hs₁]
  have hg₁ : s₁.gpr = s.gpr := by rw [hs₁]
  have hc₁ : CtxN e b s₁ := by rw [hs₁]; exact ⟨hc.r0, hc.fit, hc.wr⟩
  have hlx₁ : Lim s₁.mem (State.addr b) x := fun k hk => by rw [hm₁, hlimb x hx k hk]; exact hlx k hk
  have hly₁ : Lim s₁.mem (State.addr b) y := fun k hk => by rw [hm₁, hlimb y hy k hk]; exact hly k hk
  have hV : ∀ z : Nat, z + 64 ≤ ACC → V s₁.mem (State.addr b) z = V s.mem (State.addr b) z :=
    fun z hz => by rw [hm₁]; exact val16_congr (hlimb z hz)
  refine WP.seq (WP.mono (mulBodyFn_ok ho hx hy hc₁ (by rw [hg₁, h1]) (by rw [hg₁, h2])
    (by rw [hg₁, h3]) hlx₁ hly₁) fun t ⟨hrt, hf, hlt, hvt⟩ => ?_)
  rw [hm₁] at hf
  have hct : CtxN e b t := hc₁.of_rest hrt (by decide)
  have hsv : Spill.Saved t.mem (State.addr (t.gpr .r0)) s.gpr mulSaved := by
    rw [hct.r0]
    refine hsv1.frame mulSaved_ok hf fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint _ (.inr (by rw [hS]; omega_using [ho, hA])) (by omega_using [hS]) (by omega_using [ho, hA])
    · exact Offset.disjoint _ (.inr (by rw [hS]; omega_using [hA])) (by omega_using [hS]) (by omega_using [hA])
  refine WP.mono (Spill.restore_block_ok mulSaved_ok mulSaved_restorable
    (by rw [hct.r0, hS]; omega_using [hfit]) (fun d _ hd' => by rw [hct.r0]; exact hct.inR (by rw [hS] at hd'; omega_using [hd'])) hsv)
    fun u ⟨hres, hoth, hmu, hrd, hwr, hsp⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [hrd, hrt.rd, hs₁], by rw [hwr, hrt.wr, hs₁], by rw [hsp, hrt.sp, hs₁]⟩,
    ?_, by rw [hmu]; exact hlt, ?_⟩
  · by_cases hm : r ∈ mulSaved.map Prod.fst
    · exact Spill.restored_reg hres hm
    · rw [hoth r hm, hrt.gpr r (mulClob_split r hr hm), hg₁]
  · rw [hmu]
    refine (hf1.sub fun r hr => ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩).trans
      (hf.sub fun r hr => ?_)
    · rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by rw [hS]; omega_using [hA]) (by rw [hS]; omega_using [hA])
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by decide)⟩
  · rw [hmu, hvt, hV x hx, hV y hy]

end VG.Proof.Ed25519.Arm

end

end


/-! Compositional field programs and the extended Edwards formulas. -/

@[expose] public section

namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

variable {umaal : Bool}

abbrev Env := Slot → Spec.X25519.Fe

def env (m : Mem) (b : BitVec 32) : Env := fun i => FS m (State.addr b) (offset i)

def AllLim (m : Mem) (b : BitVec 32) : Prop := ∀ i : Slot, Lim m (State.addr b) (offset i)

def evalOp (op : FieldOp) (e : Env) : Env :=
  match op with
  | .copy o a => Function.update e o (e a)
  | .const o v => Function.update e o v
  | .mul o a b | .mulc o a b => Function.update e o (e a * e b)
  | .add o a b => Function.update e o (e a + e b)
  | .sub o a b => Function.update e o (e a - e b)

def evalOps (ops : List FieldOp) (e : Env) : Env := ops.foldl (fun e op => evalOp op e) e

structure Keep (b : BitVec 32) (s s' : State) : Prop where
  rest : Rest fclob s s'
  frame : Frame [FA b] s.mem s'.mem

theorem Keep.refl (b : BitVec 32) (s : State) : Keep b s s :=
  ⟨Rest.refl _ _, Frame.refl _ _⟩

theorem Keep.trans {b : BitVec 32} {s t u : State} (h : Keep b s t) (k : Keep b t u) :
    Keep b s u := ⟨h.rest.trans k.rest, h.frame.trans k.frame⟩

theorem Keep.ctx {b : BitVec 32} {s t : State} (h : Keep b s t) (hs : Ctx b s) : Ctx b t :=
  hs.of_rest h.rest (by decide)

theorem limb_slot_frame {b : BitVec 32} {m m' : Mem} {o i : Slot} (hne : i ≠ o)
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 (offset o), 64⟩,
      ⟨State.addr b + BitVec.ofNat 64 ACC, 160⟩] m m') :
    ∀ k < 16, limb m' (State.addr b) (offset i) k = limb m (State.addr b) (offset i) k := by
  have hi := slot_range i
  have ho := slot_range o
  have hsep : offset i + 64 ≤ offset o ∨ offset o + 64 ≤ offset i := by
    have hv : i.val ≠ o.val := fun e => hne (Fin.ext e)
    simp only [offset]
    omega_arith
  rw [ACC_eq] at hi ho
  refine limb_frame hf fun r hr k hk => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  · exact Offset.disjoint _ (.inl (by rw [ACC_eq]; omega_arith)) (by omega_arith) (by rw [ACC_eq]; omega_arith)

theorem field_update {b : BitVec 32} {m m' : Mem} (o : Slot) (hl : AllLim m b)
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 (offset o), 64⟩,
      ⟨State.addr b + BitVec.ofNat 64 ACC, 160⟩] m m')
    (ho : Lim m' (State.addr b) (offset o)) :
    AllLim m' b ∧ env m' b = Function.update (env m b) o (FS m' (State.addr b) (offset o)) := by
  constructor
  · intro i
    by_cases hi : i = o
    · subst hi; exact ho
    · intro k hk
      rw [limb_slot_frame hi hf k hk]
      exact hl i k hk
  · funext i
    by_cases hi : i = o
    · subst hi; simp only [Function.update_self, env]
    · rw [Function.update_of_ne hi]
      exact congrArg VG.Proof.X25519.toFe (val16_congr (limb_slot_frame hi hf))

/-- An operation's frame at `o` and in the product's own working space is
within the field area. -/
theorem frame_FA16 {b : BitVec 32} {o : Slot} {m m' : Mem}
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 (offset o), 64⟩,
      ⟨State.addr b + BitVec.ofNat 64 ACC, 160⟩] m m') : Frame [FA b] m m' := by
  have ho := slot_range o
  have hA := ACC_eq
  refine hf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.sub _ (by omega_arith) (by omega_arith)
  · exact Offset.sub _ (by omega_arith) (by omega_arith)

/-- The product's frame, within an operation's. -/
theorem frame_acc16 {b : BitVec 32} {o : Nat} {m m' : Mem}
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩, ⟨State.addr b + BitVec.ofNat 64 ACC, 128⟩] m m') :
    Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩, ⟨State.addr b + BitVec.ofNat 64 ACC, 160⟩] m m' := by
  refine hf.sub fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self, Region.sub_prefix (Nat.le_refl _)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by decide)⟩

/-- A frame at `o` alone, as an operation's. -/
theorem frame_o16 {b : BitVec 32} {o : Nat} {m m' : Mem}
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩] m m') :
    Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩, ⟨State.addr b + BitVec.ofNat 64 ACC, 160⟩] m m' :=
  hf.mono fun r hr => by simp [List.mem_singleton.mp hr]

theorem field_finish {b : BitVec 32} {s t : State} (o : Slot) (hl : AllLim s.mem b)
    (hr : Rest fclob s t)
    (hf : Frame [⟨State.addr b + BitVec.ofNat 64 (offset o), 64⟩,
      ⟨State.addr b + BitVec.ofNat 64 ACC, 160⟩] s.mem t.mem)
    (ho : Lim t.mem (State.addr b) (offset o)) {v : Spec.X25519.Fe}
    (hv : FS t.mem (State.addr b) (offset o) = v) :
    Keep b s t ∧ AllLim t.mem b ∧ env t.mem b = Function.update (env s.mem b) o v := by
  obtain ⟨hlim, he⟩ := field_update o hl hf ho
  rw [hv] at he
  exact ⟨⟨hr, frame_FA16 hf⟩, hlim, he⟩

/-- What a call of `vg_gf25519_r16_mul` asks of the function, as a contract on the working
space: `o`, `a` and `c`'s offsets in `r1`–`r3`. -/
def mulK (b : BitVec 32) (o a c : Slot) : Contract isa where
  pre t := t.rd = [] ∧ t.wr = [⟨State.addr b, 8192⟩] ∧ Ctx b t ∧ AllLim t.mem b ∧
    t.gpr .r1 = BitVec.ofNat 32 (offset o) ∧ t.gpr .r2 = BitVec.ofNat 32 (offset a) ∧
    t.gpr .r3 = BitVec.ofNat 32 (offset c)
  post t t' := Rest mulFnClob t t' ∧ Frame [FA b] t.mem t'.mem ∧ AllLim t'.mem b ∧
    env t'.mem b = Function.update (env t.mem b) o (env t.mem b a * env t.mem b c)
  pub _ _ := True

theorem movw_offset (o : Slot) : ((BitVec.ofNat 16 (offset o)).setWidth 32) = BitVec.ofNat 32 (offset o) := by
  have := slot_range o
  rw [ACC_eq] at this
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_arith

/-- **A call of `vg_gf25519_r16_mul`**, as the inlined product. -/
theorem mulCall_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (hl : AllLim s.mem b) (o a c : Slot) :
    WP isa (mulCall umaal (offset o) (offset a) (offset c)) s fun t => Keep b s t ∧ AllLim t.mem b ∧
      env t.mem b = Function.update (env s.mem b) o (env s.mem b a * env s.mem b c) := by
  have ho := slot_range o
  have ha := slot_range a
  have hc' := slot_range c
  have hA := ACC_eq
  unfold mulCall mulArgs
  rw [WP.seq_iff]
  refine wp_movw fun s1 u1 => wp_movw fun s2 u2 => wp_movw fun s3 u3 => WP.block_nil ?_
  have hr3 : Rest [.r1, .r2, .r3] s s3 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
  have hc3 : Ctx b s3 := hc.of_rest hr3 (by decide)
  have hm3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
  have hl3 : AllLim s3.mem b := by rw [hm3]; exact hl
  have e1 : s3.gpr .r1 = BitVec.ofNat 32 (offset o) := by
    rw [u3.other _ (by decide), u2.other _ (by decide), u1.gpr, movw_offset]
  have e2 : s3.gpr .r2 = BitVec.ofNat 32 (offset a) := by
    rw [u3.other _ (by decide), u2.gpr, movw_offset]
  have e3 : s3.gpr .r3 = BitVec.ofNat 32 (offset c) := by rw [u3.gpr, movw_offset]
  have hv : ∀ t, (mulK b o a c).pre t → ∃ tr t', Exec isa (mulFn umaal) t tr t' ∧ abiPreserved t t' ∧
      (mulK b o a c).post t t' := fun t ⟨_, _, ht, hlt, t1, t2, t3⟩ => by
    obtain ⟨tr, t', he, hR, hF, hL, hV⟩ := mulFn_ok (by omega_arith) (by omega_arith) (by omega_arith) ht t1 t2 t3
      (hlt a) (hlt c)
    obtain ⟨hlim, henv⟩ := field_update o hlt hF hL
    exact ⟨tr, t', he, ⟨fun r hr => hR.gpr r (by revert hr; cases r <;> decide), hR.sp⟩, hR,
      frame_FA16 hF, hlim, henv.trans (congrArg _ (VG.Proof.X25519.toFe_mul hV))⟩
  have g : ∀ q, q ∉ VG.Arm.linkRegs → (s3.callEntry.withRegions [] [⟨State.addr b, 8192⟩]).gpr q = s3.gpr q :=
    fun q hq => by rw [State.withRegions_gpr, State.callEntry_gpr _ hq]
  have hcov : Covers [⟨State.addr b, 8192⟩] s3.wr :=
    Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; exact hc3.wr
  refine WP.call (k := mulK b o a c) hv (rd := []) (wr := [⟨State.addr b, 8192⟩])
    ⟨rfl, rfl, ⟨by rw [g _ (by decide)]; exact hc3.r0, hc3.fit, List.mem_singleton_self _⟩,
      by rw [State.withRegions_mem, State.callEntry_mem]; exact hl3,
      by rw [g _ (by decide)]; exact e1, by rw [g _ (by decide)]; exact e2,
      by rw [g _ (by decide)]; exact e3⟩
    (Covers.right hcov) hcov ?_ (mulFn_noCalls umaal)
  intro t hrd hwr hsp _ _ _ ⟨hR, hF, hL, hV⟩
  simp only [State.withRegions_mem, State.callEntry_mem] at hF hL hV
  rw [hm3] at hF hV
  refine ⟨⟨⟨fun q hq => ?_, hrd.trans hr3.rd, hwr.trans hr3.wr, hsp.trans hr3.sp⟩, hF⟩, hL, hV⟩
  have h3 : q ∉ ([.r1, .r2, .r3] : List Reg) := by revert hq; cases q <;> decide
  have hR' := hR.gpr q h3
  simp only [State.withRegions_gpr] at hR'
  rw [hR', State.callEntry_gpr _ (by revert hq; cases q <;> decide), hr3.gpr q h3]

theorem fieldOp_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (hl : AllLim s.mem b)
    (op : FieldOp) :
    WP isa (op.code umaal) s fun t => Keep b s t ∧ AllLim t.mem b ∧
      env t.mem b = evalOp op (env s.mem b) := by
  cases op with
  | copy o a =>
    refine WP.mono (copyField_op hc o a (hl a)) fun t ⟨hr, hf, ho, hv⟩ => ?_
    exact field_finish o hl (hr.mono (by decide)) (frame_o16 hf) ho hv
  | const o v =>
    refine WP.mono (constField_op hc o v) fun t ⟨hr, hf, ho, hv⟩ => ?_
    exact field_finish o hl (hr.mono (by decide)) (frame_o16 hf) ho hv
  | mul o a c =>
    refine WP.mono (mulIn_ok (slot_range o).2 (slot_range a).2 (slot_range c).2 hc (hl a) (hl c))
      fun t ⟨hr, hf, ho, hv⟩ => ?_
    exact field_finish o hl (hr.mono (by decide)) (frame_acc16 hf) ho (VG.Proof.X25519.toFe_mul hv)
  | mulc o a c => exact mulCall_ok hc hl o a c
  | add o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    rw [ACC_eq] at ho ha hb
    refine WP.mono (add_ok (by omega_arith) (by omega_arith) (by omega_arith) (slot_sep o a) (slot_sep o c)
      hc (hl a) (hl c)) fun t ⟨hr, hf, ho, hv⟩ => ?_
    exact field_finish o hl (hr.mono (by decide)) (frame_o16 hf) ho (VG.Proof.X25519.toFe_add hv)
  | sub o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    rw [ACC_eq] at ho ha hb
    refine WP.mono (sub_ok (by omega_arith) (by omega_arith) (by omega_arith) (slot_sep o a) (slot_sep o c)
      hc (hl a) (hl c)) fun t ⟨hr, hf, ho, hv⟩ => ?_
    exact field_finish o hl (hr.mono (by decide)) (frame_o16 hf) ho (VG.Proof.X25519.toFe_sub hv)

theorem fieldCode_ok (ops : List FieldOp) {s : State} {b : BitVec 32} (hc : Ctx b s)
    (hl : AllLim s.mem b) :
    WP isa (fieldCode umaal ops) s fun t => Keep b s t ∧ AllLim t.mem b ∧
      env t.mem b = evalOps ops (env s.mem b) := by
  induction ops generalizing s with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, hl, rfl⟩
  | cons op ops ih =>
    rw [fieldCode, WP.seq_iff]
    refine WP.mono (fieldOp_ok hc hl op) fun t ⟨ht, hlt, et⟩ => ?_
    refine WP.mono (ih (ht.ctx hc) hlt) fun u ⟨hu, hlu, eu⟩ => ?_
    exact ⟨ht.trans hu, hlu, by rw [eu, et]; rfl⟩

/-- The field area without `SAVE`, `[64, 1600)`: what field code, which calls
nothing, changes. -/
abbrev FA0 (b : BitVec 32) : Region := Proof.X25519.Arm.FA ACC b

/-- `fieldOp_ok`, which also changes no register but X25519's `clob` and no
memory but `FA0`: an operation calls nothing. -/
theorem fieldOpFree_ok {b : BitVec 32} {s : State} (hc : Ctx b s) (hl : AllLim s.mem b)
    (op : FieldOp) (hi : op.inline = true) :
    WP isa (op.code umaal) s fun t => Keep b s t ∧ Rest clob s t ∧ Frame [FA0 b] s.mem t.mem ∧ AllLim t.mem b ∧
      env t.mem b = evalOp op (env s.mem b) := by
  have hs (o : Slot) := slot_range o
  cases op with
  | copy o a =>
    refine WP.mono (copyField_op hc o a (hl a)) fun t ⟨hr, hf, ho, hv⟩ => ?_
    obtain ⟨k, l, e⟩ := field_finish o hl (hr.mono (by decide)) (frame_o16 hf) ho hv
    exact ⟨k, hr.mono (by decide), frame_FA (by decide) (hs o) (frame_o hf), l, e⟩
  | const o v =>
    refine WP.mono (constField_op hc o v) fun t ⟨hr, hf, ho, hv⟩ => ?_
    obtain ⟨k, l, e⟩ := field_finish o hl (hr.mono (by decide)) (frame_o16 hf) ho hv
    exact ⟨k, hr.mono (by decide), frame_FA (by decide) (hs o) (frame_o hf), l, e⟩
  | mul o a c =>
    refine WP.mono (mulIn_ok (slot_range o).2 (slot_range a).2 (slot_range c).2 hc (hl a) (hl c))
      fun t ⟨hr, hf, ho, hv⟩ => ?_
    obtain ⟨k, l, e⟩ := field_finish o hl (hr.mono (by decide)) (frame_acc16 hf) ho (VG.Proof.X25519.toFe_mul hv)
    exact ⟨k, hr, frame_FA (by decide) (hs o) hf, l, e⟩
  | mulc => simp [FieldOp.inline] at hi
  | add o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    rw [ACC_eq] at ho ha hb
    refine WP.mono (add_ok (by omega_arith) (by omega_arith) (by omega_arith) (slot_sep o a) (slot_sep o c)
      hc (hl a) (hl c)) fun t ⟨hr, hf, ho, hv⟩ => ?_
    obtain ⟨k, l, e⟩ := field_finish o hl (hr.mono (by decide)) (frame_o16 hf) ho (VG.Proof.X25519.toFe_add hv)
    exact ⟨k, hr, frame_FA (by decide) (hs o) (frame_o hf), l, e⟩
  | sub o a c =>
    have ho := slot_range o
    have ha := slot_range a
    have hb := slot_range c
    rw [ACC_eq] at ho ha hb
    refine WP.mono (sub_ok (by omega_arith) (by omega_arith) (by omega_arith) (slot_sep o a) (slot_sep o c)
      hc (hl a) (hl c)) fun t ⟨hr, hf, ho, hv⟩ => ?_
    obtain ⟨k, l, e⟩ := field_finish o hl (hr.mono (by decide)) (frame_o16 hf) ho (VG.Proof.X25519.toFe_sub hv)
    exact ⟨k, hr, frame_FA (by decide) (hs o) (frame_o hf), l, e⟩

/-- `fieldCode_ok`, which also changes no register but X25519's `clob` and no
memory but `FA0`. -/
theorem fieldCodeFree_ok (ops : List FieldOp) (hi : ops.all FieldOp.inline = true) {s : State}
    {b : BitVec 32} (hc : Ctx b s) (hl : AllLim s.mem b) :
    WP isa (fieldCode umaal ops) s fun t => Keep b s t ∧ Rest clob s t ∧ Frame [FA0 b] s.mem t.mem ∧
      AllLim t.mem b ∧ env t.mem b = evalOps ops (env s.mem b) := by
  induction ops generalizing s with
  | nil => exact WP.block_nil ⟨Keep.refl _ _, Rest.refl _ _, Frame.refl _ _, hl, rfl⟩
  | cons op ops ih =>
    rw [fieldCode, WP.seq_iff]
    simp only [List.all_cons, Bool.and_eq_true] at hi
    refine WP.mono (fieldOpFree_ok hc hl op hi.1) fun t ⟨ht, hrt, hft, hlt, et⟩ => ?_
    refine WP.mono (ih hi.2 (ht.ctx hc) hlt) fun u ⟨hu, hru, hfu, hlu, eu⟩ => ?_
    exact ⟨ht.trans hu, hrt.trans hru, hft.trans hfu, hlu, by rw [eu, et]; rfl⟩

/-- Coordinates in four consecutive slots. -/
def point (e : Env) (x y z t : Slot) : Spec.Ed25519.Point := ⟨e x, e y, e z, e t⟩

def addResult (e : Env) (q : Nat) (hq : q + 3 < 22) : Spec.Ed25519.Point :=
  let x := e ⟨q, by omega_arith⟩
  let y := e ⟨q + 1, by omega_arith⟩
  let z := e ⟨q + 2, by omega_arith⟩
  let t := e ⟨q + 3, by omega_arith⟩
  let a := (e 1 - e 0) * (y - x)
  let b := (e 1 + e 0) * (y + x)
  let c := (e 3 * e 16 + e 3 * e 16) * t
  let dd := (e 2 + e 2) * z
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem pointAdd_formula (e : Env) :
    point (evalOps pointAddOps e) 0 1 2 3 = addResult e 4 (by decide) := by
  rfl

theorem addResult_eq (e : Env) (q : Nat) (hq : q + 3 < 22) (hd : e 16 = Spec.Ed25519.d) :
    addResult e q hq = Spec.Ed25519.pointAdd (point e 0 1 2 3)
      (point e ⟨q, by omega_arith⟩ ⟨q + 1, by omega_arith⟩ ⟨q + 2, by omega_arith⟩ ⟨q + 3, hq⟩) := by
  simp only [addResult, point, Spec.Ed25519.pointAdd, hd]
  congr 1 <;> grind

theorem pointAdd_eval (e : Env) (hd : e 16 = Spec.Ed25519.d) :
    point (evalOps pointAddOps e) 0 1 2 3 =
      Spec.Ed25519.pointAdd (point e 0 1 2 3) (point e 4 5 6 7) :=
  (pointAdd_formula e).trans (addResult_eq e 4 (by decide) hd)

/-- The dedicated doubling's `X : Y : Z` (`Proof.Ed25519.dblPoint`), with `T` as it was: what
`pointDoubleOps` computes. -/
def dblXYZ (p : Spec.Ed25519.Point) : Spec.Ed25519.Point := { Proof.Ed25519.dblPoint p with T := p.T }

theorem pointDouble_eval (e : Env) :
    point (evalOps pointDoubleOps e) 0 1 2 3 = dblXYZ (point e 0 1 2 3) := rfl

/-- The doubling leaves `E` and `H`, whose product is its `T`, in slots 11 and 14. -/
theorem pointDouble_t (e : Env) :
    evalOps pointDoubleOps e 11 * evalOps pointDoubleOps e 14 =
      (Proof.Ed25519.dblPoint (point e 0 1 2 3)).T := rfl

/-- The doubling with its `T` (`doubleTOps`). -/
theorem dblXYZ_t (p : Spec.Ed25519.Point) :
    (⟨(dblXYZ p).X, (dblXYZ p).Y, (dblXYZ p).Z, (Proof.Ed25519.dblPoint p).T⟩ : Spec.Ed25519.Point) =
      Proof.Ed25519.dblPoint p := rfl

end VG.Proof.Ed25519.Arm

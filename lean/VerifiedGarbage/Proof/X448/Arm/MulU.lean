module

public import VerifiedGarbage.Proof.X448.Arm.RowMem
public import VerifiedGarbage.Proof.X448.Arm.Field
public import VerifiedGarbage.Proof.X25519.Arm.Words.Ladder
import VerifiedGarbage.Proof.X448.Arm.Init
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Lit
-- separate module: the `umaal` rows' proofs, which cost more than their imports, are not
-- re-checked with `Env.lean`'s baseline operations

/-!
# X448 on ARMv7: the product's limbs with `umaal`

`mulU`'s part before the fold (`Impl/X448/Arm.lean`): the second operand's
limbs packed in pairs into fourteen words at `ACC` (`mulPreU_ok`), the rows
(`rowU_ok`, `mulLoopU_ok`: a chain of `umaal`s each, `uc` and `uo` of
`Proof/X25519/Arm/Words/Ladder.lean`, after which the accumulator's words at
`TMP` are the product of the first operand's packed words so far and the
second operand), and the product's words split into the fifty-six limbs at
`ACC` (`unpackAll_ok`), which are below `2¹⁶` and whose value is the product
of the operands' (`ProdU.val`): what the baseline's rows leave, for the same
fold and normalization.
-/

@[expose] public section

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X25519.Arm
open VG.Proof.X25519.Arm.Words (val32 val32_succ val32_congr val32_append uc uo uc_succ uc_val umaal_lt
  wp_umaal Upd2)

variable {b : BitVec 32}

/-! ## Packed words -/

/-- Limbs `2k` and `2k + 1` as a word. -/
def pack (f : Nat → Nat) (k : Nat) : Nat := f (2 * k) + 65536 * f (2 * k + 1)

theorem pack_lt {f : Nat → Nat} {k : Nat} (h0 : f (2 * k) < 65536) (h1 : f (2 * k + 1) < 65536) :
    pack f k < 2 ^ 32 := by
  unfold pack; omega_using [h0, h1]

/-- The limbs' number in radix `2¹⁶` is their packed words' in radix `2³²`. -/
theorem valN_pack (f : Nat → Nat) : ∀ n, Radix16.valN f (2 * n) = val32 (pack f) n
  | 0 => rfl
  | n + 1 => by
    have e1 : Radix16.radix ^ (2 * n) = 2 ^ (32 * n) := by
      rw [Radix16.radix, ← Nat.pow_mul]; exact congrArg (2 ^ ·) (by omega_arith)
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 from rfl, Radix16.valN_succ, Radix16.valN_succ, valN_pack f n,
      val32_succ, pack, Nat.pow_succ, e1, Nat.mul_add, Nat.add_assoc, Nat.mul_assoc]
    rfl

/-- Word `j` of the packed second operand, at `ACC`. -/
abbrev bw (m : Mem) (B : Addr) (j : Nat) : Nat := wd m B (ACC + 4 * j)

/-- Word `k` of the accumulator, at `TMP`. -/
abbrev pw (m : Mem) (B : Addr) (k : Nat) : Nat := wd m B (TMP + 4 * k)

theorem TMP_eq : TMP = 3840 := rfl

/-- Two limbs, the second shifted, as their word. -/
theorem packed_toNat {x y : BitVec 32} (hx : x.toNat < 65536) (hy : y.toNat < 65536) :
    (x + y <<< 16).toNat = x.toNat + 65536 * y.toNat := by
  have e : (y <<< 16).toNat = 65536 * y.toNat := by
    rw [toNat_shl, Nat.mod_eq_of_lt (by omega_using [hy])]; omega_arith
  rw [toNat_add_lt (by rw [e]; omega_using [hx, hy]), e]

/-! ## The second operand packed, and the accumulator zeroed -/

theorem packB_ok {s : State} (hc : RowCtx b s) {y j : Nat} (hy : y + 112 ≤ ACC) (hj : j < 14)
    (h12 : s.gpr .r12 = b + BitVec.ofNat 32 y) (hly : Bounded s.mem (State.addr b) y) :
    WP isa (.block (packB j)) s fun t =>
      t.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 (ACC + 4 * j))
        (BitVec.ofNat 32 (pack (limbs s.mem (State.addr b) y) j)) ∧ Rest [.r2, .r3] s t := by
  have hA := ACC_eq
  have hfit := hc.fit
  unfold packB
  refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (y + 4 * (2 * j))) (by omega_arith)
    (by rw [h12, eaB hfit (by omega_arith)]) (hc.inR (by omega_arith)) fun s1 u1 => ?_
  refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (y + 4 * (2 * j + 1))) (by omega_arith)
    (by rw [u1.other _ (by decide), h12, eaB hfit (by omega_arith)])
    (by rw [u1.rd, u1.wr]; exact hc.inR (by omega_arith)) fun s2 u2 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s3 u3 => ?_
  obtain r3 : Rest [.r2, .r3] s s3 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
  refine rowStore_ok (hc.of_rest r3 (by decide)) (d := ACC + 4 * j) (by omega_arith) fun s4 u4 =>
    WP.block_nil ⟨?_, r3.trans (u4.rest _)⟩
  obtain b2 : limbs s.mem (State.addr b) y (2 * j) < 65536 := hly _ (by omega_arith)
  obtain b3 : limbs s.mem (State.addr b) y (2 * j + 1) < 65536 := hly _ (by omega_arith)
  obtain e2 : (s2.gpr .r2).toNat = limbs s.mem (State.addr b) y (2 * j) := by
    rw [u2.other _ (by decide), u1.gpr]
  obtain e3 : (s2.gpr .r3).toNat = limbs s.mem (State.addr b) y (2 * j + 1) := by
    rw [u2.gpr, u1.mem]
  rw [u4.mem, u3.mem, u2.mem, u1.mem]
  refine congrArg (s.mem.writeW _) (BitVec.eq_of_toNat_eq ?_)
  rw [u3.gpr]
  change (s2.gpr .r2 + s2.gpr .r3 <<< 16).toNat = _
  rw [packed_toNat (by rw [e2]; exact b2) (by rw [e3]; exact b3), e2, e3, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (pack_lt b2 b3)]
  rfl

/-- The state the rows start from: the second operand packed at `ACC`, the accumulator's low
words zero, and the rows' pointers and counter. -/
structure PreU (b : BitVec 32) (x y : Nat) (s t : State) : Prop where
  ctx : RowCtx b t
  rest : Rest [.r2, .r3, .r5, .r7] s t
  r7 : t.gpr .r7 = b
  r5 : t.gpr .r5 = BitVec.ofNat 32 14
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 368⟩] s.mem t.mem
  bw : ∀ j < 14, bw t.mem (State.addr b) j = pack (limbs s.mem (State.addr b) y) j
  zero : ∀ k < 14, pw t.mem (State.addr b) k = 0

theorem mulPreU_ok {x y : Nat} {s : State} (hc : RowCtx b s) (hy : y + 112 ≤ ACC)
    (h12 : s.gpr .r12 = b + BitVec.ofNat 32 y) (hly : Bounded s.mem (State.addr b) y) :
    WP isa (.block mulPreU) s (PreU b x y s) := by
  have hA := ACC_eq
  have hT := TMP_eq
  unfold mulPreU
  rw [List.append_assoc, List.append_assoc, List.singleton_append]
  -- The second operand.
  refine WP.append (wp_range_flatMap (M := isa) (N := 14)
    (fun n t => (∀ j < n, bw t.mem (State.addr b) j = pack (limbs s.mem (State.addr b) y) j) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 56⟩] s.mem t.mem ∧ Rest [.r2, .r3] s t)
    (fun n t hn ⟨tb, tf, tr⟩ => ?_) 14 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, Rest.refl _ _⟩) fun s1 ⟨b1, f1, r1⟩ => ?_
  · obtain ly : ∀ k < 28, limbs t.mem (State.addr b) y k = limbs s.mem (State.addr b) y k := fun k hk =>
      wd_frame tf fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
    refine WP.mono (packB_ok (hc.of_rest tr (by decide)) hy hn ((tr.gpr _ (by decide)).trans h12)
      (fun k hk => by rw [ly k hk]; exact hly k hk)) fun u ⟨um, ur⟩ => ⟨fun j hj => ?_, ?_, tr.trans ur⟩
    · rw [bw, um]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [wd_write_other _ _ _ (by omega_using [hj]) (by omega_arith) (by omega_arith)]; exact tb j hj
      · rw [wd_write_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (pack_lt
          (by rw [ly _ (by omega_arith)]; exact hly _ (by omega_arith))
          (by rw [ly _ (by omega_arith)]; exact hly _ (by omega_arith)))]
        show limbs t.mem (State.addr b) y (2 * j) + 65536 * limbs t.mem (State.addr b) y (2 * j + 1) = _
        rw [ly _ (by omega_arith), ly _ (by omega_arith)]
        rfl
    · rw [um]
      exact tf.writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
  -- The accumulator.
  obtain hc1 := hc.of_rest r1 (by decide)
  refine wp_mov (op2_imm (by decide)) fun s2 u2 => ?_
  obtain hc2 := hc1.of_rest (u2.rest (ws := [.r3]) (by decide)) (by decide)
  refine WP.append (wp_range_flatMap (M := isa) (N := 14)
    (fun n t => (∀ k < n, pw t.mem (State.addr b) k = 0) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 TMP, 56⟩] s2.mem t.mem ∧ Rest [] s2 t ∧ t.gpr .r3 = 0)
    (fun n t hn ⟨h1, h2, h3, h4⟩ => ?_) 14 (Nat.le_refl _) s2
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, Rest.refl _ _, u2.gpr⟩)
    fun s3 ⟨z3, f3, r3, _⟩ => ?_
  · refine rowStore_ok (hc2.of_rest h3 (by decide)) (d := TMP + 4 * n) (by omega_arith) fun t' u' =>
      WP.block_nil ⟨fun k hk => ?_, ?_, h3.trans (u'.rest _), by rw [u'.gpr, h4]⟩
    · rw [pw, u'.mem]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · rw [wd_write_other _ _ _ (by omega_using [hk]) (by omega_arith) (by omega_arith)]; exact h1 k hk
      · rw [wd_write_self, h4]; rfl
    · rw [u'.mem]
      exact h2.writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
  obtain hc3 := hc2.of_rest r3 (by decide)
  refine wp_mov (op2_reg _ _) fun s4 u4 => wp_mov (op2_imm (by decide)) fun s5 u5 => WP.block_nil ?_
  obtain r5 : Rest [.r2, .r3, .r5, .r7] s s5 :=
    (r1.mono (by decide)).trans ((u2.rest (by decide)).trans ((r3.mono (by decide)).trans
      ((u4.rest (by decide)).trans (u5.rest (by decide)))))
  obtain m5 : s5.mem = s3.mem := by rw [u5.mem, u4.mem]
  obtain f13 : Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 368⟩] s.mem s3.mem := by
    refine (f1.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      ((u2.mem ▸ f3).sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    · rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_arith) (by omega_arith)
    · rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_arith) (by omega_arith)
  refine ⟨hc.of_rest r5 (by decide), r5, ?_, u5.gpr, m5 ▸ f13, fun j hj => ?_, fun k hk => m5 ▸ z3 k hk⟩
  · rw [u5.other _ (by decide), u4.gpr, hc3.r0]
  · rw [m5, bw, wd_frame f3 fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith),
      u2.mem]
    exact b1 j hj

/-! ## The rows -/

/-- One product of row `i`. -/
theorem rowStepU_ok {i j : Nat} (hi : i < 14) (hj : j < 14) {s : State} (hc : RowCtx b s)
    (h7 : s.gpr .r7 = b + BitVec.ofNat 32 (4 * i)) :
    WP isa (.block (rowStepU j)) s fun t =>
      (t.gpr .r4).toNat = ((s.gpr .r1).toNat * bw s.mem (State.addr b) j + (s.gpr .r4).toNat +
        pw s.mem (State.addr b) (i + j)) / 2 ^ 32 ∧
      (t.gpr .r3).toNat = ((s.gpr .r1).toNat * bw s.mem (State.addr b) j + (s.gpr .r4).toNat +
        pw s.mem (State.addr b) (i + j)) % 2 ^ 32 ∧
      t.mem = s.mem.writeW (State.addr b + BitVec.ofNat 64 (TMP + 4 * (i + j))) (t.gpr .r3) ∧
      Rest [.r2, .r3, .r4] s t := by
  have hA := ACC_eq
  have hT := TMP_eq
  have hfit := hc.fit
  unfold rowStepU
  refine rowLoad_ok hc (d := ACC + 4 * j) (by omega_arith) fun s1 u1 => ?_
  refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (TMP + 4 * (i + j))) (by omega_arith)
    (by rw [u1.other _ (by decide), h7, ea7 hfit (by omega_arith),
          show 4 * i + (TMP + 4 * j) = TMP + 4 * (i + j) by omega_arith])
    (by rw [u1.rd, u1.wr]; exact hc.inR (by omega_arith)) fun s2 u2 => ?_
  obtain e2 : (s2.gpr .r2).toNat = bw s.mem (State.addr b) j := by rw [u2.other _ (by decide), u1.gpr]; rfl
  obtain e3 : (s2.gpr .r3).toNat = pw s.mem (State.addr b) (i + j) := by rw [u2.gpr, u1.mem]; rfl
  obtain e1 : s2.gpr .r1 = s.gpr .r1 := by rw [u2.other _ (by decide), u1.other _ (by decide)]
  obtain e4 : s2.gpr .r4 = s.gpr .r4 := by rw [u2.other _ (by decide), u1.other _ (by decide)]
  refine wp_umaal (by decide) (umaal_lt (s2.gpr .r1).isLt (s2.gpr .r2).isLt (s2.gpr .r4).isLt
    (s2.gpr .r3).isLt) fun s3 u3 => ?_
  obtain r3 : Rest [.r2, .r3, .r4] s s3 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide) (by decide)))
  refine wp_str (a := State.addr b + BitVec.ofNat 64 (TMP + 4 * (i + j))) (by omega_arith)
    (by rw [r3.gpr _ (by decide), h7, ea7 hfit (by omega_arith),
          show 4 * i + (TMP + 4 * j) = TMP + 4 * (i + j) by omega_arith])
    ((hc.of_rest r3 (by decide)).inW (by omega_arith)) fun s4 u4 => WP.block_nil ⟨?_, ?_, ?_, r3.trans (u4.rest _)⟩
  · rw [u4.gpr, u3.ghi, e1, e2, e3, e4]
  · rw [u4.gpr, u3.glo, e1, e2, e3, e4]
  · rw [u4.mem, u3.mem, u2.mem, u1.mem, u4.gpr]

/-- After `i` rows: the accumulator's first `i + 14` words are the product of the first `i`
packed words of the first operand and the second operand. -/
structure RowInvU (b : BitVec 32) (x : Nat) (s0 : State) (i : Nat) (s : State) : Prop where
  ctx : RowCtx b s
  rest : Rest (.lr :: fclob) s0 s
  r7 : s.gpr .r7 = b + BitVec.ofNat 32 (4 * i)
  lr : s.gpr .lr = b + BitVec.ofNat 32 (x + 8 * i)
  r5 : s.gpr .r5 = BitVec.ofNat 32 (14 - i)
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 TMP, 112⟩] s0.mem s.mem
  val : val32 (pw s.mem (State.addr b)) (i + 14) =
    val32 (pack (limbs s0.mem (State.addr b) x)) i * val32 (bw s0.mem (State.addr b)) 14

/-- The row's sum. -/
theorem row_arith {P Pi XV Ai av Bv p : Nat} (h1 : P = Pi + p * XV) (h2 : P = Ai * Bv) :
    Pi + p * (av * Bv + XV) = (Ai + p * av) * Bv := by
  rw [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
  omega_using [h1, h2]

theorem rowU_ok {x : Nat} (hx : x + 112 ≤ ACC) {s0 : State} (hlx : Bounded s0.mem (State.addr b) x)
    {i : Nat} (hi : i < 14) {s : State} (h : RowInvU b x s0 i s) :
    WP isa (.block rowU) s fun t => RowInvU b x s0 (i + 1) t ∧ t.z = decide (i + 1 = 14) := by
  have hA := ACC_eq
  have hT := TMP_eq
  have hfit := h.ctx.fit
  obtain fr0 : ∀ d, d + 4 ≤ TMP → wd s.mem (State.addr b) d = wd s0.mem (State.addr b) d := fun d hd =>
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  simp only [rowU, List.cons_append, List.nil_append]
  -- The row's word of the first operand.
  refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (x + 4 * (2 * i))) (by decide)
    (by rw [h.lr, eaB hfit (by omega_arith), show x + 8 * i + 0 = x + 4 * (2 * i) by omega_arith])
    (h.ctx.inR (by omega_arith)) fun s1 u1 => ?_
  refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (x + 4 * (2 * i + 1))) (by decide)
    (by rw [u1.other _ (by decide), h.lr, eaB hfit (by omega_arith),
          show x + 8 * i + 4 = x + 4 * (2 * i + 1) by omega_arith])
    (by rw [u1.rd, u1.wr]; exact h.ctx.inR (by omega_arith)) fun s2 u2 => ?_
  refine wp_dp (op2_lsl (by decide)) fun s3 u3 => ?_
  refine wp_mov (op2_imm (by decide)) fun s4 u4 => ?_
  obtain r4 : Rest [.r1, .r2, .r3, .r4] s s4 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      (u4.rest (by decide))))
  obtain m4 : s4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
  obtain hc4 : RowCtx b s4 := h.ctx.of_rest r4 (by decide)
  obtain a0 : limbs s0.mem (State.addr b) x (2 * i) < 65536 := hlx _ (by omega_arith)
  obtain a1 : limbs s0.mem (State.addr b) x (2 * i + 1) < 65536 := hlx _ (by omega_arith)
  obtain e1 : (s4.gpr .r1).toNat = pack (limbs s0.mem (State.addr b) x) i := by
    obtain q1 : (s2.gpr .r1).toNat = limbs s0.mem (State.addr b) x (2 * i) := by
      rw [u2.other _ (by decide), u1.gpr]; exact fr0 _ (by omega_arith)
    obtain q2 : (s2.gpr .r2).toNat = limbs s0.mem (State.addr b) x (2 * i + 1) := by
      rw [u2.gpr, u1.mem]; exact fr0 _ (by omega_arith)
    rw [u4.other _ (by decide), u3.gpr]
    change (s2.gpr .r1 + s2.gpr .r2 <<< 16).toNat = _
    rw [packed_toNat (by rw [q1]; exact a0) (by rw [q2]; exact a1), q1, q2]
    rfl
  obtain e7 : s4.gpr .r7 = b + BitVec.ofNat 32 (4 * i) := by rw [r4.gpr _ (by decide), h.r7]
  -- The chain.
  generalize hav : pack (limbs s0.mem (State.addr b) x) i = av at e1
  let Bf : Nat → Nat := bw s0.mem (State.addr b)
  let X : Nat → Nat := fun k => pw s.mem (State.addr b) (i + k)
  refine WP.append (wp_range_flatMap (M := isa) (N := 14)
    (fun j t => RowCtx b t ∧ Rest [.r2, .r3, .r4] s4 t ∧ (t.gpr .r4).toNat = uc av Bf X 0 j ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 (TMP + 4 * i), 4 * j⟩] s4.mem t.mem ∧
      ∀ k < j, pw t.mem (State.addr b) (i + k) = uo av Bf X 0 k)
    (fun j t hj ⟨tc, tr, t4, tf, to⟩ => ?_) 14 (Nat.le_refl _) s4
    ⟨hc4, Rest.refl _ _, by rw [u4.gpr]; rfl, Frame.refl _ _, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩)
    fun s5 ⟨c5, r5, c4, f5, o5⟩ => ?_
  · obtain eb : bw t.mem (State.addr b) j = Bf j := by
      rw [bw, wd_frame tf fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith), m4]
      exact fr0 _ (by omega_arith)
    obtain ex : pw t.mem (State.addr b) (i + j) = X j := by
      rw [pw, wd_frame tf fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith), m4]
    refine WP.mono (rowStepU_ok hi hj tc ((tr.gpr _ (by decide)).trans e7)) fun t' ⟨g4, g3, gm, gr⟩ => ?_
    rw [tr.gpr .r1 (by decide), e1, eb, t4, ex] at g4 g3
    refine ⟨tc.of_rest gr (by decide), tr.trans gr, by rw [g4, uc_succ], ?_, fun k hk => ?_⟩
    · rw [gm]
      refine (tf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_arith) (by omega_arith)
    · rw [pw, gm]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · rw [wd_write_other _ _ _ (by omega_using [hk]) (by omega_arith) (by omega_arith)]; exact to k hk
      · rw [wd_write_self, g3, uo]
  -- The carry, and the pointers and the counter.
  obtain e7' : s5.gpr .r7 = b + BitVec.ofNat 32 (4 * i) := by rw [r5.gpr _ (by decide), e7]
  refine wp_str (a := State.addr b + BitVec.ofNat 64 (TMP + 4 * (i + 14))) (by omega_arith)
    (by rw [e7', ea7 hfit (by omega_arith), show 4 * i + (TMP + 56) = TMP + 4 * (i + 14) by omega_arith])
    (c5.inW (by omega_arith)) fun s6 u6 => ?_
  refine wp_dp (op2_imm (by decide)) fun s7 u7 => ?_
  refine wp_dp (op2_imm (by decide)) fun s8 u8 => ?_
  refine wp_subs (op2_imm (by decide)) fun s9 u9 hz => WP.block_nil ?_
  obtain r9 : Rest (.lr :: fclob) s s9 :=
    (r4.mono (by decide)).trans ((r5.mono (by decide)).trans ((u6.rest _).trans
      ((u7.rest (by decide)).trans ((u8.rest (by decide)).trans (u9.rest (by decide))))))
  obtain m9 : s9.mem = s5.mem.writeW (State.addr b + BitVec.ofNat 64 (TMP + 4 * (i + 14))) (s5.gpr .r4) := by
    rw [u9.mem, u8.mem, u7.mem, u6.mem]
  obtain f59 : Frame [⟨State.addr b + BitVec.ofNat 64 (TMP + 4 * i), 60⟩] s.mem s9.mem := by
    rw [m9, ← m4]
    refine (f5.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
    rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_arith) (by omega_arith)
  obtain lo : ∀ k < i, pw s9.mem (State.addr b) k = pw s.mem (State.addr b) k := fun k hk =>
    wd_frame f59 fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  obtain mid : ∀ k < 14, pw s9.mem (State.addr b) (i + k) = uo av Bf X 0 k := fun k hk => by
    rw [pw, m9, wd_write_other _ _ _ (by omega_using [hk]) (by omega_arith) (by omega_arith)]
    exact o5 k hk
  obtain top : pw s9.mem (State.addr b) (i + 14) = uc av Bf X 0 14 := by
    rw [pw, m9, wd_write_self, c4]
  obtain he : s.gpr .r5 - (1 : BitVec 32) = BitVec.ofNat 32 (14 - (i + 1)) := by
    change s.gpr .r5 - BitVec.ofNat 32 1 = _
    rw [h.r5, show 14 - i = 14 - (i + 1) + 1 by omega_arith, BitVec.ofNat_add, BitVec.add_sub_cancel]
  obtain g5 : s8.gpr .r5 = s.gpr .r5 := by
    rw [u8.other _ (by decide), u7.other _ (by decide), u6.gpr, r5.gpr _ (by decide), r4.gpr _ (by decide)]
  refine ⟨⟨h.ctx.of_rest r9 (by decide), h.rest.trans r9, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u9.other _ (by decide), u8.other _ (by decide), u7.gpr]
    change s6.gpr .r7 + BitVec.ofNat 32 4 = _
    rw [u6.gpr, e7', Offset.add_add, show 4 * i + 4 = 4 * (i + 1) by omega_arith]
  · rw [u9.other _ (by decide), u8.gpr]
    change s7.gpr .lr + BitVec.ofNat 32 8 = _
    rw [u7.other _ (by decide), u6.gpr, r5.gpr _ (by decide), r4.gpr _ (by decide), h.lr, Offset.add_add,
      show x + 8 * i + 8 = x + 8 * (i + 1) by omega_arith]
  · rw [u9.gpr, g5]; exact he
  · refine h.frame.trans (f59.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_arith) (by omega_arith)
  · obtain hv := h.val
    rw [val32_append _ i 14] at hv
    rw [show i + 1 + 14 = i + 15 by omega_arith, val32_append _ i 15, val32_congr lo, val32_succ,
      val32_congr mid, top]
    obtain hc14 := uc_val av Bf X 0 14
    rw [Nat.add_zero] at hc14
    rw [hc14, val32_succ (pack (limbs s0.mem (State.addr b) x)) i, hav]
    exact row_arith rfl hv
  · rw [hz, g5, he]
    exact (ofNat_beq_zero (by omega_arith)).trans (decide_eq_decide.mpr (by omega_using [hi]))

theorem mulLoopU_ok {x : Nat} (hx : x + 112 ≤ ACC) {s0 s : State} (hlx : Bounded s0.mem (State.addr b) x)
    (hs : RowInvU b x s0 0 s) : WP isa (.loop (.block rowU) .ne) s (RowInvU b x s0 14) := by
  refine WP.loop (M := isa)
    (fun n s' => ∃ i, n = 14 - i ∧ i < 14 ∧ RowInvU b x s0 i s') ?_ 14 s ⟨0, rfl, by decide, hs⟩
  rintro n s' ⟨i, rfl, hi, hr⟩
  refine WP.mono (rowU_ok hx hlx hi hr) fun t ⟨ht, hz⟩ => ?_
  by_cases h14 : i + 1 = 14
  · refine .inl ⟨by rw [eval_ne, hz, decide_eq_true h14]; rfl, ?_⟩
    rw [h14] at ht
    exact ht
  · exact .inr ⟨by rw [eval_ne, hz, decide_eq_false h14]; rfl,
      14 - (i + 1), by omega_using [hi], i + 1, rfl, by omega_using [hi, h14], ht⟩

/-! ## The product's limbs -/

theorem unpack_ok {s : State} (hc : RowCtx b s) (h6 : s.gpr .r6 = mask16) {k : Nat} (hk : k < 28) :
    WP isa (.block (unpack k)) s fun t =>
      t.mem = (s.mem.writeW (State.addr b + BitVec.ofNat 64 (ACC + 4 * (2 * k)))
        (BitVec.ofNat 32 (pw s.mem (State.addr b) k % 65536))).writeW
          (State.addr b + BitVec.ofNat 64 (ACC + 4 * (2 * k + 1)))
          (BitVec.ofNat 32 (pw s.mem (State.addr b) k / 65536)) ∧ Rest [.r2, .r3] s t := by
  have hA := ACC_eq
  have hT := TMP_eq
  unfold unpack
  refine rowLoad_ok hc (d := TMP + 4 * k) (by omega_arith) fun s1 u1 => ?_
  refine wp_dp (op2_reg _ _) fun s2 u2 => ?_
  obtain r2 : Rest [.r2, .r3] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  refine rowStore_ok (hc.of_rest r2 (by decide)) (d := ACC + 4 * (2 * k)) (by omega_arith) fun s3 u3 => ?_
  refine wp_mov (op2_lsr (by decide)) fun s4 u4 => ?_
  obtain r4 : Rest [.r2, .r3] s s4 := r2.trans ((u3.rest _).trans (u4.rest (by decide)))
  refine rowStore_ok (hc.of_rest r4 (by decide)) (d := ACC + 4 * (2 * k + 1)) (by omega_arith) fun s5 u5 =>
    WP.block_nil ⟨?_, r4.trans (u5.rest _)⟩
  obtain e3 : (s1.gpr .r3).toNat = pw s.mem (State.addr b) k := by rw [u1.gpr]; rfl
  obtain v2 : s2.gpr .r2 = BitVec.ofNat 32 (pw s.mem (State.addr b) k % 65536) := by
    apply BitVec.eq_of_toNat_eq
    rw [u2.gpr]
    change (s1.gpr .r3 &&& s1.gpr .r6).toNat = _
    rw [u1.other .r6 (by decide), h6, toNat_and_mask16, e3, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))]
  obtain v3 : s4.gpr .r3 = BitVec.ofNat 32 (pw s.mem (State.addr b) k / 65536) := by
    apply BitVec.eq_of_toNat_eq
    rw [u4.gpr, toNat_shr, u3.gpr, u2.other _ (by decide), e3, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (wd_lt _ _ _))]
  rw [u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, v3, v2]

/-- What the rows and the split leave: the fifty-six limbs of the product at `ACC`. -/
structure ProdU (b : BitVec 32) (v : Nat) (s t : State) : Prop where
  ctx : RowCtx b t
  rest : Rest [.r2, .r3] s t
  frame : Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 224⟩] s.mem t.mem
  lt : ∀ k < 56, accw t.mem (State.addr b) k < 65536
  val : Radix16.valN (accw t.mem (State.addr b)) 56 = v

theorem unpackAll_ok {s : State} (hc : RowCtx b s) (h6 : s.gpr .r6 = mask16) :
    WP isa (.block ((List.range 28).flatMap unpack)) s
      (ProdU b (val32 (pw s.mem (State.addr b)) 28) s) := by
  have hA := ACC_eq
  have hT := TMP_eq
  refine WP.mono (wp_range_flatMap (M := isa) (N := 28)
    (fun n t => (∀ k < n, accw t.mem (State.addr b) (2 * k) = pw s.mem (State.addr b) k % 65536 ∧
        accw t.mem (State.addr b) (2 * k + 1) = pw s.mem (State.addr b) k / 65536) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 ACC, 8 * n⟩] s.mem t.mem ∧ Rest [.r2, .r3] s t)
    (fun n t hn ⟨ta, tf, tr⟩ => ?_) 28 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, Rest.refl _ _⟩) fun t ⟨ta, tf, tr⟩ => ?_
  · obtain ep : pw t.mem (State.addr b) n = pw s.mem (State.addr b) n :=
      wd_frame tf fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
    refine WP.mono (unpack_ok (hc.of_rest tr (by decide)) ((tr.gpr _ (by decide)).trans h6) hn)
      fun u ⟨um, ur⟩ => ⟨fun k hk => ?_, ?_, tr.trans ur⟩
    · rw [ep] at um
      obtain lt1 : pw s.mem (State.addr b) n % 65536 < 2 ^ 32 :=
        Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
      obtain lt2 : pw s.mem (State.addr b) n / 65536 < 2 ^ 32 :=
        Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (wd_lt _ _ _)
      rw [accw, accw, um]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · rw [wd_write_other _ _ _ (by omega_using [hk]) (by omega_arith) (by omega_arith),
          wd_write_other _ _ _ (by omega_using [hk]) (by omega_arith) (by omega_arith),
          wd_write_other _ _ _ (by omega_using [hk]) (by omega_arith) (by omega_arith),
          wd_write_other _ _ _ (by omega_using [hk]) (by omega_arith) (by omega_arith)]
        exact ta k hk
      · rw [wd_write_other _ _ _ (by omega_arith) (by omega_arith) (by omega_arith), wd_write_self,
          wd_write_self, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt lt1, Nat.mod_eq_of_lt lt2]
        exact ⟨rfl, rfl⟩
    · rw [um]
      refine ((tf.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))).writeW
        (List.mem_singleton_self _) _ (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_arith) (by omega_arith)
  · refine ⟨hc.of_rest tr (by decide), tr, tf, fun k hk => ?_, ?_⟩
    · obtain ⟨q, rfl | rfl⟩ : ∃ q, k = 2 * q ∨ k = 2 * q + 1 := ⟨k / 2, by omega_arith⟩
      · rw [(ta q (by omega_using [hk])).1]; exact Nat.mod_lt _ (by decide)
      · rw [(ta q (by omega_using [hk])).2]
        exact (Nat.div_lt_iff_lt_mul (by decide)).mpr (wd_lt _ _ _)
    · rw [show 56 = 2 * 28 from rfl, valN_pack]
      refine val32_congr fun k hk => ?_
      rw [pack, (ta k hk).1, (ta k hk).2]
      exact Nat.mod_add_div _ _

end VG.Proof.X448.Arm

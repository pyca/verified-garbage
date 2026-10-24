module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointAccumulate
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.BatchBits
import VerifiedGarbage.Proof.Ed25519.ScalarBytes
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.X25519.PPC64LE.Invert
import VerifiedGarbage.Proof.X25519.PPC64LE.Bits
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointPowers
public import VerifiedGarbage.Proof.Ed25519.ScalarMul
public import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Field

/-!
# Ed25519 on PPC64LE: scalar multiplication

`pointMulBody_ok`: from the accumulator `after S P (16 (c + 1))`, batch `c`
adds the powers `[2^(16c + i)] P` of its set bits from the top, leaving
`after S P (16 c)` (`accum_after`). `pointMultiply_ok`: from the identity
and the table of `[2^(16 j)] P`, all batches from the top, `[S] P`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Proof.Ed25519 (powerPoint after)

/-- Sixteen bits from the top, by `after_step`. -/
theorem accum_after (S : Nat) (P : Spec.Ed25519.Point) (c : Nat) :
    ∀ m ≤ 16, accum (fun i => powerPoint P (16 * c + i)) (fun i => S / 2 ^ (16 * c + i) % 2) m
      (after S P (16 * c + m)) = after S P (16 * c)
  | 0, _ => rfl
  | m + 1, hm => by
    rw [accum, ← accum_after S P c m (by omega)]
    congr 1
    rw [Proof.Ed25519.after_step S P (16 * c + m)]
    by_cases h : S / 2 ^ (16 * c + m) % 2 = 0
    · rw [iteT h, iteF (by omega)]; rfl
    · rw [iteF h, iteT (by omega)]; rfl

theorem accum_congr {T T' : Nat → Spec.Ed25519.Point} {W W' : Nat → Nat} :
    ∀ m, (∀ i < m, T i = T' i) → (∀ i < m, W i = W' i) → ∀ A, accum T W m A = accum T' W' m A
  | 0, _, _, _ => rfl
  | m + 1, hT, hW, A => by
    rw [accum, accum, hT m (by omega), hW m (by omega)]
    exact accum_congr m (fun i hi => hT i (by omega)) (fun i hi => hW i (by omega)) _

/-- A batch's digit, as the scalar's bits. -/
theorem digit_bit {m : Mem} {p : Addr} {N c k : Nat} (hc : c < N) (hk : k < 16) :
    (digitAt m p c >>> k) &&& 1 = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p (2 * N)) / 2 ^ (16 * c + k) % 2 := by
  obtain ⟨S, hS⟩ : ∃ S, S = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p (2 * N)) := ⟨_, rfl⟩
  rw [← hS]
  have hb : ∀ i < 2 * N, S / 256 ^ i % 256 = (m (p + BitVec.ofNat 64 i)).toNat := fun i hi => by
    rw [hS, Proof.Ed25519.decodeLE_byte]
    exact congrArg BitVec.toNat (getD_bytesAt m p hi)
  have hd : digitAt m p c = S / 2 ^ (16 * c) % 2 ^ 16 := by
    have h1 := hb (2 * c) (by omega)
    have h2 := hb (2 * c + 1) (by omega)
    have hs := Proof.Ed25519.div_split S (2 * c)
    rw [show (2 : Nat) ^ (16 * c) = 256 ^ (2 * c) by rw [Nat.pow_mul, Nat.pow_mul], hs]
    unfold digitAt
    rw [← h1, ← h2]
    omega
  have h2 : 2 ∣ 2 ^ (16 - k) := ⟨2 ^ (16 - k - 1), by rw [← Nat.pow_succ']; congr 1; omega⟩
  rw [hd, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod,
    show (2 : Nat) ^ 16 = 2 ^ k * 2 ^ (16 - k) by rw [← Nat.pow_add]; congr 1; omega,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ h2, Nat.div_div_eq_div_mul, ← Nat.pow_add]

section
variable {b : Addr}

/-- What a batch writes: the field area, the table of its powers and its bits. -/
abbrev batchW (b : Addr) : List Region := [FA b, ⟨b + BitVec.ofNat 64 5728, 2048⟩, ⟨b + BitVec.ofNat 64 BITSB, 16⟩]

/-- The registers a batch writes. -/
abbrev batchR : List Reg := .r8 :: .r14 :: .r15 :: .r16 :: .r26 :: fclob

theorem bytes_ws {m m' : Mem} {rs : List Region} (hf : Frame rs m m') (hs : ∀ r ∈ rs, Region.Sub r ⟨b, 8192⟩)
    {p : Addr} {nb : Nat} (hd : (⟨p, nb⟩ : Region).Disjoint ⟨b, 8192⟩) (hn : nb ≤ 64) {i : Nat} (hi : i < nb) :
    m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
  hf _ fun r hr hc => hd _ (Offset.contains_base _ (by omega) (by omega)) (hs r hr _ hc)

theorem batchW_sub : ∀ r ∈ batchW b, Region.Sub r ⟨b, 8192⟩ := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.sub_base _ (by omega)
  · exact Offset.sub_base _ (by omega)
  · exact Offset.sub_base _ (by simp only [BITSB]; omega)

theorem batch_table1 {m m' : Mem} (hf : Frame (batchW b) m m') {j : Nat} (hj : j < 32) :
    tableAt m' b (1632 + 128 * j) = tableAt m b (1632 + 128 * j) :=
  tableAt_keep hf fun r hr => by
    have hB : BITSB = 32 := rfl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
    · exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)
    · exact Offset.disjoint _ (.inr (by simp only [BITSB]; omega)) (by omega) (by omega)

/-- **Batch `c`**: from `after S P (16 (c + 1))` to `after S P (16 c)`. -/
theorem pointMulBody_ok {s : State} (hc : Ctx8 b s) (hd : env s.mem b 16 = Spec.Ed25519.d) {p : Addr} {N : Nat}
    (hN : N ≤ 32) (h19 : s.gpr .r19 = p) (hin : ∀ i < 2 * N, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 i) 1)
    (hpd : (⟨p, 2 * N⟩ : Region).Disjoint ⟨b, 8192⟩) {c : Nat} (hcl : c < N)
    (h26 : s.gpr .r26 = BitVec.ofNat 64 (c + 1)) {P : Spec.Ed25519.Point}
    (hacc : point (env s.mem b) 0 1 2 3 =
      after (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p (2 * N))) P (16 * (c + 1)))
    (htab : tableAt s.mem b (1632 + 128 * c) = powerPoint P (16 * c)) :
    WP isa pointMulBody s fun t =>
      Rest batchR s t ∧ Frame (batchW b) s.mem t.mem ∧ t.gpr .r26 = BitVec.ofNat 64 c ∧
      point (env t.mem b) 0 1 2 3 = after (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p (2 * N))) P (16 * c) ∧
      env t.mem b 16 = Spec.Ed25519.d := by
  obtain ⟨S, hS⟩ : ∃ S, S = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p (2 * N)) := ⟨_, rfl⟩
  rw [← hS] at hacc ⊢
  unfold pointMulBody batchStart
  refine WP.seq (wp_subi (by decide) (by decide) fun s1 u1 => wp_addi (by decide) (by decide) fun s2 u2 =>
    WP.block_nil ?_)
  have e26 : s2.gpr .r26 = BitVec.ofNat 64 c := by
    rw [u2.other _ (by decide), u1.gpr, h26, ofNat_sub_one (by omega) (by omega), Nat.add_sub_cancel]
  have e16 : s2.gpr .r16 = BitVec.ofNat 64 c := by
    rw [u2.gpr, BitVec.add_zero, u1.gpr, h26, ofNat_sub_one (by omega) (by omega), Nat.add_sub_cancel]
  have hr2 : Rest [.r16, .r26] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  have hc2 : Ctx8 b s2 := hc.of_rest hr2 (by decide)
  -- The checkpoint, and the saved accumulator.
  unfold prepareBatch loadCheckpoint savePoint restorePoint
  refine WP.seq (WP.seq (WP.seq (WP.mono (fieldCode_ok savePointOps hc2.ctx) fun t1 ⟨k1, e1⟩ => ?_)))
  obtain ⟨s17, _, s16⟩ := env_savePoint (env s2.mem b)
  rw [← e1, hm2] at s17 s16
  have hc3 : Ctx8 b t1 := hc2.of_keep k1
  refine tableAddr_ok hc3 (start := 1632) (n := c) (by decide) (by omega) (by rw [k1.rest.gpr _ (by decide), e16])
    fun t2 r2 m2 e14 => ?_
  refine WP.mono (pointFromTable_ok (hc3.of_rest r2 (by decide)) e14 (by omega) (by omega)) fun t3 ⟨r3, f3, p3, k3⟩ => ?_
  rw [m2] at p3 k3 f3
  rw [table_FA k1.frame (by omega) (by omega), hm2, htab] at p3
  have hc4 : Ctx8 b t3 := (hc3.of_rest r2 (by decide)).of_rest r3 (by decide)
  have hd3 : env t3.mem b 16 = Spec.Ed25519.d := by rw [k3 16 (by decide), s16, hd]
  -- The batch's powers, and the accumulator restored.
  refine WP.seq (WP.mono (pointPowers_ok hc4 hd3 false (start := 5728) (count := 16) (by omega) (by omega) (by omega))
    fun t4 ⟨r4, f4, tab4, _, k4⟩ => ?_)
  have hc5 : Ctx8 b t4 := hc4.of_rest r4 (by decide)
  refine WP.mono (fieldCode_ok restorePointOps hc5.ctx) fun t5 ⟨k5, e5⟩ => ?_
  obtain ⟨w0, _, w16, _⟩ := env_restorePoint (env t4.mem b)
  rw [← e5] at w0 w16
  have hc6 : Ctx8 b t5 := hc5.of_keep k5
  have hA5 : point (env t5.mem b) 0 1 2 3 = after S P (16 * (c + 1)) := by
    rw [w0, ← hacc, ← s17]
    simp only [point, k4 17 (by decide), k4 18 (by decide), k4 19 (by decide), k4 20 (by decide),
      k3 17 (by decide), k3 18 (by decide), k3 19 (by decide), k3 20 (by decide)]
  have hd5 : env t5.mem b 16 = Spec.Ed25519.d := by rw [w16, k4 16 (by decide), hd3]
  -- Everything so far writes within the batch's regions.
  have hF5 : Frame (batchW b) s.mem t5.mem := by
    rw [← hm2]
    refine (k1.frame.mono (by simp)).trans ((f3.sub fun r hr => ⟨FA b, by simp, ?_⟩).trans
      ((f4.mono fun r hr => ?_).trans (k5.frame.mono (by simp))))
    · rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega) (by omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl
      · exact .inl rfl
      · exact .inr (.inl (by simp))
  have hR5 : Rest batchR s t5 :=
    (hr2.mono (by decide)).trans ((k1.rest.mono (by decide)).trans ((r2.mono (by decide)).trans
      ((r3.mono (by decide)).trans ((r4.mono (by decide)).trans (k5.rest.mono (by decide))))))
  -- The bits.
  have hR25 : Rest (.r7 :: .r14 :: .r15 :: .r16 :: fclob) s2 t5 :=
    (k1.rest.mono (by decide)).trans ((r2.mono (by decide)).trans
      ((r3.mono (by decide)).trans ((r4.mono (by decide)).trans (k5.rest.mono (by decide)))))
  have e26' : t5.gpr .r26 = BitVec.ofNat 64 c := by rw [hR25.gpr _ (by decide), e26]
  refine WP.seq (WP.mono (batchBits_ok hc6 (by omega) e26' (p := p)
    (by rw [hR5.gpr _ (by decide), h19]) (fun i hi => by rw [hR5.rd, hR5.wr]; exact hin _ (by omega)))
    fun t6 ⟨r6, f6, bits6⟩ => ?_)
  have hB : BITSB = 32 := rfl
  have hc7 : Ctx8 b t6 := hc6.of_rest r6 (by decide)
  have hslot : ∀ j : Slot, env t6.mem b j = env t5.mem b j := fun j => env_keep f6 j fun r hr => by
    rw [List.mem_singleton.mp hr]
    have := slot_range j
    exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
  have hd6 : env t6.mem b 16 = Spec.Ed25519.d := by rw [hslot, hd5]
  have hbit : ∀ k < 16, (t6.mem (b + BitVec.ofNat 64 (BITSB + k))).toNat = S / 2 ^ (16 * c + k) % 2 := fun k hk => by
    rw [bits6 k hk, BitVec.toNat_ofNat]
    have hdig : digitAt t5.mem p c = digitAt s.mem p c := by
      unfold digitAt
      rw [bytes_ws hF5 batchW_sub hpd (by omega) (by omega), bytes_ws hF5 batchW_sub hpd (by omega) (by omega)]
    rw [hdig, digit_bit hcl hk, ← hS]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))
  refine WP.mono (accumulate16_ok hc7 hd6 fun k hk => by rw [hbit k hk]; exact Nat.le_of_lt_succ (Nat.mod_lt _ (by decide)))
    fun t7 ⟨r7, f7, p7, d7⟩ => ⟨?_, ?_, ?_, ?_, d7⟩
  · exact hR5.trans ((r6.mono (by decide)).trans (r7.mono (by decide)))
  · exact hF5.trans ((f6.mono (by simp)).trans (f7.mono (by simp)))
  · rw [r7.gpr _ (by decide), r6.gpr _ (by decide), e26']
  · have hT : ∀ i < 16, tableAt t6.mem b (5728 + 128 * i) = powerPoint P (16 * c + i) := fun i hi => by
      rw [tableAt_keep f6 fun r hr => by
          rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega),
        table_FA k5.frame (by omega) (by omega), tab4 i hi, p3, ← Proof.Ed25519.powerPoint_add,
        show powerStride false = 1 from rfl, Nat.one_mul]
    have hP6 : point (env t6.mem b) 0 1 2 3 = after S P (16 * c + 16) := by
      simp only [point, hslot]; rw [← Nat.mul_succ]; exact hA5
    rw [p7, hP6, accum_congr 16 hT hbit, accum_after S P c 16 (Nat.le_refl _)]

/-- What the multiplication writes: a batch's regions and the table of checkpoints. -/
abbrev mulW (b : Addr) : List Region := ⟨b + BitVec.ofNat 64 1632, 4096⟩ :: batchW b

theorem mulW_sub : ∀ r ∈ mulW b, Region.Sub r ⟨b, 8192⟩ := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact Offset.sub_base _ (by omega)
  · exact batchW_sub r hr

theorem env_constPoint (e : Env) (p : Spec.Ed25519.Point) :
    point (evalOps (constPointOps p) e) 0 1 2 3 = p ∧ evalOps (constPointOps p) e 16 = e 16 := ⟨rfl, rfl⟩

/-- **`[S] P`**, for the point `P` of slots 0–3 and the scalar `S` of the `2 count` bytes at `r19`. -/
theorem pointMultiply_ok {s : State} (hc : Ctx8 b s) (hd : env s.mem b 16 = Spec.Ed25519.d) {p : Addr}
    {count : Nat} (hc1 : 1 ≤ count) (hc32 : count ≤ 32) (h19 : s.gpr .r19 = p)
    (hin : ∀ i < 2 * count, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 i) 1)
    (hpd : (⟨p, 2 * count⟩ : Region).Disjoint ⟨b, 8192⟩) :
    WP isa (pointMultiply count) s fun t =>
      Rest (.r7 :: batchR) s t ∧ Frame (mulW b) s.mem t.mem ∧
      point (env t.mem b) 0 1 2 3 =
        Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p (2 * count)))
          (point (env s.mem b) 0 1 2 3) ∧ env t.mem b 16 = Spec.Ed25519.d := by
  have hS := Proof.Ed25519.decodeLE_lt (Spec.Ed25519.bytesAt s.mem p (2 * count))
  rw [show (Spec.Ed25519.bytesAt s.mem p (2 * count)).length = 2 * count by simp [Spec.Ed25519.bytesAt],
    show (256 : Nat) ^ (2 * count) = 2 ^ (16 * count) by rw [Nat.pow_mul, Nat.pow_mul]] at hS
  obtain ⟨S, hSd⟩ : ∃ S, S = Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem p (2 * count)) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = point (env s.mem b) 0 1 2 3 := ⟨_, rfl⟩
  rw [← hSd, ← hP]
  rw [← hSd] at hS
  unfold pointMultiply
  refine WP.seq (WP.mono (pointPowers_ok hc hd true (start := 1632) (count := count) (by omega) (by omega) hc1)
    fun t1 ⟨r1, f1, tab1, _, k1⟩ => ?_)
  rw [← hP] at tab1
  have hc2 : Ctx8 b t1 := hc.of_rest r1 (by decide)
  unfold constPoint
  refine WP.seq (WP.mono (fieldCode_ok (constPointOps Spec.Ed25519.identity) hc2.ctx) fun t2 ⟨k2, e2⟩ => ?_)
  obtain ⟨c0, c16⟩ := env_constPoint (env t1.mem b) Spec.Ed25519.identity
  rw [← e2] at c0 c16
  have hc3 : Ctx8 b t2 := hc2.of_keep k2
  refine WP.seq (wp_li (by omega) fun t3 u3 => WP.block_nil ?_)
  have hc4 : Ctx8 b t3 := hc3.of_rest (u3.rest (ws := [.r26]) (by decide)) (by decide)
  -- The frames so far.
  have hF3 : Frame (mulW b) s.mem t3.mem := by
    rw [u3.mem]
    refine (f1.sub fun r hr => ?_).trans (k2.frame.mono (by simp))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨FA b, by simp, fun _ h => h⟩
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by omega)⟩
  have hbytes : ∀ {m : Mem}, Frame (mulW b) s.mem m →
      Spec.Ed25519.bytesAt m p (2 * count) = Spec.Ed25519.bytesAt s.mem p (2 * count) :=
    fun hf => by
      simp only [Spec.Ed25519.bytesAt, List.map_inj_left]
      intro i hi
      exact bytes_ws hf mulW_sub hpd (by omega) (List.mem_range.mp hi)
  have hR3 : Rest (.r7 :: batchR) s t3 :=
    (r1.mono (by decide)).trans ((k2.rest.mono (by decide)).trans (u3.rest (by decide)))
  have hT3 : ∀ j < count, tableAt t3.mem b (1632 + 128 * j) = powerPoint P (16 * j) := fun j hj => by
    rw [u3.mem, table_FA k2.frame (by omega) (by omega), tab1 j hj]; rfl
  refine WP.loop (M := isa) (fun n t => 1 ≤ n ∧ n ≤ count ∧ Ctx8 b t ∧ Rest (.r7 :: batchR) s t ∧
      Frame (mulW b) s.mem t.mem ∧ t.gpr .r26 = BitVec.ofNat 64 n ∧
      point (env t.mem b) 0 1 2 3 = after S P (16 * n) ∧ env t.mem b 16 = Spec.Ed25519.d ∧
      ∀ j < count, tableAt t.mem b (1632 + 128 * j) = powerPoint P (16 * j)) ?_ count t3
    ⟨hc1, Nat.le_refl _, hc4, hR3, hF3, u3.gpr, by rw [u3.mem, c0, Proof.Ed25519.after_top S _ P hS],
      by rw [u3.mem, c16, k1 16 (by decide), hd], hT3⟩
  rintro n t ⟨h1, h2, hct, hr, hf, h26, ha, hdt, ht⟩
  obtain ⟨c, rfl⟩ : ∃ c, n = c + 1 := ⟨n - 1, by omega⟩
  refine WP.mono (pointMulBody_ok hct hdt (p := p) hc32 (by rw [hr.gpr _ (by decide), h19])
    (fun i hi => by rw [hr.rd, hr.wr]; exact hin i hi) hpd (by omega) h26 (P := P)
    (by rw [hbytes hf, ← hSd]; exact ha) (ht c (by omega))) fun u ⟨ru, fu, e26, pu, du⟩ => ?_
  rw [hbytes hf, ← hSd] at pu
  have hfu : Frame (mulW b) s.mem u.mem := hf.trans (fu.mono (by simp))
  have hz : (u.gpr .r26 != 0) = decide (c ≠ 0) := by rw [e26, ofNat_ne_zero (by omega)]
  rw [eval_nonzero, hz]
  by_cases hc0 : c = 0
  · subst hc0
    refine .inl ⟨by simp, hr.trans (ru.mono (by decide)), hfu, ?_, du⟩
    rw [pu, Nat.mul_zero, Proof.Ed25519.after_zero]
  · exact .inr ⟨by simp [hc0], c, by omega, by omega, by omega, hct.of_rest ru (by decide),
      hr.trans (ru.mono (by decide)), hfu, e26, pu, du, fun j hj => by rw [batch_table1 fu (by omega), ht j hj]⟩

end

end VG.Proof.Ed25519.PPC64LE

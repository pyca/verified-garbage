import VerifiedGarbage.Proof.AesCcm.Arm.Seal

/-!
# AES-CCM on ARMv7: masking the data (`mask`)

Untrusted: everything here is checked by Lean. `mask` ANDs every byte of
the data with `0 − ok`, for `ok ∈ {0, 1}` in `r7`: the data is kept if
`ok = 1` and zeroed if `ok = 0` (`mask_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesCcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ccm (zeros)
open VG.Impl.AesGcm.Arm (imm addI)
open VG.Proof.AesGcm.Arm (Keeps z_subFlags gpr_subFlags z_cmp eval_eq' eval_ne' addr_i dec32 z_dec in_of_covers
  bytesAt_succ mem_store gpr_store add32_ofNat_assoc in_left add_ofNat_zero mem_subFlags)

theorem mask_byte (b : Byte) (c : Bool) :
    ((b.setWidth 32 &&& ((0 : BitVec 32) - (if c then 1 else 0))).setWidth 8) = if c then b else 0 := by
  cases c
  · simp
  · rw [show (if true = true then (1 : BitVec 32) else 0) = 1 from rfl,
      show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes]
    simp

abbrev maskBody : List Instr :=
  [.ldrb .r12 .r4 0, .dp .and .r12 .r12 (.reg .r1), .strb .r12 .r4 0, addI .r4 .r4 1, .subs .r5 .r5 (imm 1)]

theorem maskStep_ok (s : State) {D : BitVec 32} {i n : Nat} {c : Bool} (h4 : s.gpr .r4 = D + BitVec.ofNat 32 i)
    (h5 : s.gpr .r5 = BitVec.ofNat 32 (n - i)) (h1 : s.gpr .r1 = 0 - (if c then 1 else 0))
    (r : InRegions (s.rd ++ s.wr) (State.addr (D + BitVec.ofNat 32 i)) 1)
    (w : InRegions s.wr (State.addr (D + BitVec.ofNat 32 i)) 1) :
    ∃ s', runBlock isa maskBody s = some s' ∧
      s'.mem = s.mem.writeW (State.addr (D + BitVec.ofNat 32 i))
        ((if c then s.mem (State.addr (D + BitVec.ofNat 32 i)) else 0 : Byte)) ∧
      s'.gpr .r4 = D + BitVec.ofNat 32 (i + 1) ∧ s'.gpr .r5 = BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 ∧
      s'.z = (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨_, by arun [h4, h5, add_ofNat_zero, r, w], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_subFlags, mem_store, gpr_setReg, gpr_store, ite_true, ite_false, reduceCtorEq, h1,
      mask_byte]
  · simp [gpr_setReg, h4, add32_ofNat_assoc]
  · simp [gpr_setReg, h5]
  · simp [z_setReg, h5]
  · intro r a b d; simp [gpr_setReg, a, b, d]
  all_goals rfl

theorem length_mask (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P j else zeros j).length = j := by
  cases c <;> simp [zeros, Proof.AesCcm.length_bytesAt]

theorem mask_succ (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P (j + 1) else zeros (j + 1)) =
      (if c then bytesAt m P j else zeros j) ++ [if c then m (P + BitVec.ofNat 64 j) else 0] := by
  cases c <;> simp [zeros, bytesAt_succ, List.replicate_succ']

/-- Every byte of the data ANDed with `0 − ok`. -/
theorem mask_ok {k w sp : BitVec 32} {R q1 : Nat} {s₀ s : State} (he : Env k w sp R q1 s) (hk : Stk w s₀ s)
    {D : BitVec 32} {n : Nat} (eD : stackArg s₀ 2 = D) (en : stackArg s₀ 3 = BitVec.ofNat 32 n)
    (hD : Dat k w sp s D n) (hn32 : n < 2 ^ 32) {c : Bool} (h7 : s.gpr .r7 = if c then 1 else 0) :
    WP isa mask s fun s' => Env k w sp R q1 s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .r4 → r ≠ .r5 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      s'.mem = writeBytes s.mem (State.addr D) (if c then bytesAt s.mem (State.addr D) n else zeros n) := by
  have hn := hD.buf.fit
  obtain ⟨i2, v2⟩ := hk.at 2 (by decide) (show 4 * 2 = 8 from rfl)
  obtain ⟨i3, v3⟩ := hk.at 3 (by decide) (show 4 * 3 = 12 from rfl)
  obtain ⟨s₁, run₁, h4₁, h5₁, h1₁, hz₁, g₁, k₁⟩ : ∃ s₁, runBlock isa [.ldrSp .r4 8, .ldrSp .r5 12, .mov .r1 (imm 0),
      .dp .sub .r1 .r1 (.reg .r7), .cmp .r5 (imm 0)] s = some s₁ ∧
      s₁.gpr .r4 = D ∧ s₁.gpr .r5 = BitVec.ofNat 32 n ∧ s₁.gpr .r1 = 0 - (if c then 1 else 0) ∧
      s₁.z = decide (n = 0) ∧ (∀ r, r ≠ .r1 → r ≠ .r4 → r ≠ .r5 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
    refine ⟨_, by arun [i2, v2, i3, v3], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, v2, eD]
    · simp [gpr_setReg, v3, en]
    · simp [gpr_setReg, h7, imm]
    · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, v3, en, imm]
      rw [z_cmp hn32 (by decide)]
    · intro r a b d; simp [gpr_setReg, a, b, d]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide) (by decide)) k₁.sp k₁.rd k₁.wr
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n = 0)) (eval_eq' hz₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hn0 : n = 0 := by simpa using hb
    subst hn0
    refine ⟨he₁, k₁.rd, k₁.wr, fun r hr a b _ => g₁ r ?_ a b, ?_⟩
    · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · rw [k₁.mem]; cases c <;> simp [bytesAt, zeros, writeBytes_nil]
  have hn0 : 0 < n := by have : n ≠ 0 := by simpa using hb
                         omega_arith
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = n - j ∧ j < n ∧ t.gpr .r4 = D + BitVec.ofNat 32 j ∧
      t.gpr .r5 = BitVec.ofNat 32 (n - j) ∧
      t.mem = writeBytes s.mem (State.addr D) (if c then bytesAt s.mem (State.addr D) j else zeros j) ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r12 → t.gpr r = s₁.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp) ?_
    (n - 0) _
    ⟨0, rfl, hn0, by rw [h4₁, add_ofNat_zero], by rw [h5₁]; rfl,
      by rw [k₁.mem]; cases c <;> simp [bytesAt, zeros, writeBytes_nil], fun r _ _ _ => rfl, k₁.rd, k₁.wr, k₁.sp⟩
  rintro m t ⟨j, rfl, hj, r4, r5, mem, g, rd, wr, sp⟩
  have aD := addr_i hn hj
  obtain ⟨t', run', mem', r4', r5', z', g', rd', wr', sp'⟩ := maskStep_ok t (c := c) r4 r5
    (by rw [g _ (by decide) (by decide) (by decide), h1₁])
    (by rw [rd, wr, aD]; exact in_of_covers hD.buf.rd hj (by omega_arith))
    (by rw [wr, aD]; exact in_of_covers hD.wr hj (by omega_arith))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have fr : Frame [⟨State.addr D, j⟩] s.mem t.mem := by
    rw [mem]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  have hq : t.mem (State.addr D + BitVec.ofNat 64 j) = s.mem (State.addr D + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Mem.sub_ofNat_toNat (State.addr D) (show j < 2 ^ 64 by omega_arith)] at hcon; omega_arith
  have hmem : t'.mem = writeBytes s.mem (State.addr D)
      (if c then bytesAt s.mem (State.addr D) (j + 1) else zeros (j + 1)) := by
    rw [mem', aD, hq, mem, mask_succ, writeBytes_snoc _ _ _ _ (by rw [length_mask]; omega_arith), length_mask]
  have hz : t'.z = decide (j + 1 = n) := by rw [z', dec32 hj hn32, z_dec hj hn32]
  have gg : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r12 → t'.gpr r = s₁.gpr r := fun r a b d => by
    rw [g' r a b d, g r a b d]
  have ev : isa.eval .ne t' = some !decide (j + 1 = n) := eval_ne' hz
  by_cases hjn : j + 1 = n
  · left
    refine ⟨by rw [ev]; simp [hjn], he₁.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> exact gg _ (by decide) (by decide) (by decide))
      (by rw [sp', sp, ← k₁.sp]) (by rw [rd', rd, k₁.rd]) (by rw [wr', wr, k₁.wr]), by rw [rd', rd],
      by rw [wr', wr], fun r hr a b _ => ?_, by rw [hmem, hjn]⟩
    have hr12 : r ≠ .r12 ∧ r ≠ .r1 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [gg r a b hr12.1, g₁ r hr12.2 a b]
  · right
    refine ⟨by rw [ev]; simp [hjn], n - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, r4',
      by rw [r5', dec32 hj hn32], hmem, gg, by rw [rd', rd], by rw [wr', wr], by rw [sp', sp]⟩

end VG.Proof.AesCcm.Arm

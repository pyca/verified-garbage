import VerifiedGarbage.Proof.AesSiv.Arm.FinishShort
import VerifiedGarbage.Proof.AesSiv.Long
import VerifiedGarbage.Proof.AesCcm.Bytes

/-!
# AES-SIV on ARMv7: finishing S2V with a string of a block or more

Untrusted: everything here is checked by Lean. For a last string `P` of
`L ≥ 16` bytes, `longTail` computes `16 k` (`kBlock_ok`, `kOf`), copies the
last `T = L − 16 k` bytes of `P` to the tail at `W + 32` and XORs `D` into
its last 16 (`tailCopy_ok`, `xorend_mem4`); `longMac out` chains the `k`
blocks of `P`, then the first `j` blocks of the tail, and finalizes the rest
(`longMac_ok`), which is S2V's end (`long_spec`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesSiv.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI copyLoop)
open VG.Impl.CmacAes.Arm (mov xor4)
open VG.Proof.AesGcm.Arm (z_cmp gpr_subFlags z_subFlags mem_subFlags rd_subFlags wr_subFlags sp_subFlags
  bytesAt_frame covers_left covers_off eval_eq' Keeps LoopPre LoopOut copyLoop_ok in_off ofNat_sub32 shr4 addr_toNat
  add32_ofNat_assoc)
open VG.Proof.CmacAes.Arm (xorBlk xorBlk_ok)
open VG.Proof.MdStream.Arm (wp_sub wp_add op2_reg)
open VG.Proof.AesCcm.Arm (blw UArgs UPost upd_call)
open VG.Proof.CmacAes.Stream.Arm (blw16)
open VG.Proof.AesSiv (kOf jOf kOf_lt kOf_ge kOf_tail jOf_rest jOf_le take_bytesAt drop_bytesAt long_spec)

/-- XORing `D` into the last 16 of `T` bytes, a word at a time. -/
theorem xorend_mem4 (m : Mem) {B Q : Addr} {T : Nat} (hT : 16 ≤ T) (hw : B.toNat + T ≤ 2 ^ 64)
    (hd : (⟨B, T⟩ : Region).Disjoint ⟨Q, 16⟩) :
    bytesAt (Proof.Cmac.xor4Mem m (B + BitVec.ofNat 64 (T - 16)) (B + BitVec.ofNat 64 (T - 16)) Q) B T =
      Spec.Siv.xorend (bytesAt m B T) (bytesAt m Q 16) := by
  have hc : Region.Sub ⟨B + BitVec.ofNat 64 (T - 16), 16⟩ ⟨B, T⟩ := Offset.sub_base B (by omega)
  have e : T = (T - 16) + 16 := by omega
  have hs := Proof.Cmac.Stream.bytesAt_append (Proof.Cmac.xor4Mem m (B + BitVec.ofNat 64 (T - 16))
    (B + BitVec.ofNat 64 (T - 16)) Q) B (T - 16) 16
  rw [← e] at hs
  rw [hs, Spec.Siv.xorend, Proof.Cmac.bytesAt_length, Proof.Cmac.bytesAt_length]
  have tk := take_bytesAt m B (a := T - 16) (b := 16)
  have dr := drop_bytesAt m B (a := T - 16) (b := 16)
  rw [← e] at tk dr
  rw [tk, dr, Proof.Cmac.bytesAt_frame (Proof.Cmac.xor4Mem_frame _ _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint B (by omega) (by omega)) (by omega),
    Proof.Cmac.xor4Mem_bytes _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint (hd.sub_left hc)),
    Siv.xor_eq]

theorem shl4' {n : Nat} (hn : 16 * n < 2 ^ 32) : BitVec.ofNat 32 n <<< 4 = BitVec.ofNat 32 (16 * n) := shl4 hn

/-- `kBlock`: `16 k` in `r4`. -/
theorem kBlock_ok {s : State} {n : Nat} (h16 : 16 ≤ n) (hn : n < 2 ^ 32) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) :
    WP isa kBlock s fun s' => s'.gpr .r4 = BitVec.ofNat 32 (16 * kOf n) ∧
      (∀ r, r ≠ .r4 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have e1 : BitVec.ofNat 32 n - 1#32 = BitVec.ofNat 32 (n - 1) := ofNat_sub32 (by omega) hn
  have e2 : BitVec.ofNat 32 (n - 1) >>> 4 = BitVec.ofNat 32 ((n - 1) / 16) := shr4 (by omega)
  obtain ⟨s₁, run₁, h12₁, h4₁, hz₁, g₁, k₁⟩ : ∃ s₁, runBlock isa [.dp .sub .r12 .r5 (imm 1),
      .mov .r12 (.shifted .r12 .lsr 4), .mov .r4 (imm 0), .cmp .r12 (imm 0)] s = some s₁ ∧
      s₁.gpr .r12 = BitVec.ofNat 32 ((n - 1) / 16) ∧ s₁.gpr .r4 = 0 ∧ s₁.z = decide ((n - 1) / 16 = 0) ∧
      (∀ r, r ≠ .r4 → r ≠ .r12 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
    refine ⟨_, by arun [h5], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h5, e1, e2]
    · simp [gpr_setReg]
    · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5, e1, e2]
      exact z_cmp (by omega) (by decide)
    · intro r a b; simp [gpr_setReg, a, b]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  by_cases h0 : (n - 1) / 16 = 0
  · refine WP.ite true (eval_eq' (by rw [hz₁]; simp [h0])) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    refine ⟨by rw [h4₁, kOf_lt (by omega)]; rfl, g₁, k₁⟩
  · refine WP.ite false (eval_eq' (by rw [hz₁]; simp [h0])) (fun h => by cases h) fun _ => ?_
    have e3 : BitVec.ofNat 32 ((n - 1) / 16) - 1#32 = BitVec.ofNat 32 ((n - 1) / 16 - 1) :=
      ofNat_sub32 (by omega) (by omega)
    have e4 : BitVec.ofNat 32 ((n - 1) / 16 - 1) <<< 4 = BitVec.ofNat 32 (16 * ((n - 1) / 16 - 1)) :=
      shl4 (by omega)
    refine WP.of_runBlock ⟨_, by arun [h12₁], ?_, ?_, ?_⟩
    · simp [gpr_setReg, h12₁, e3, e4, kOf_ge (show ¬ n < 17 by omega)]
    · intro r a b; simp [gpr_setReg, a, b, g₁ r a b]
    · exact ⟨k₁.mem, k₁.rd, k₁.wr, k₁.sp⟩

theorem bytesAt_writeBytes_self (m : Mem) (p : Addr) (xs : List Byte) (hn : xs.length < 2 ^ 64) :
    bytesAt (writeBytes m p xs) p xs.length = xs := by
  rw [Proof.AesCcm.bytesAt_writeBytes_base m p xs (Nat.le_refl _) hn,
    List.drop_eq_nil_of_le (by rw [Proof.Cmac.bytesAt_length]), List.append_nil]

section
variable {c w sp : BitVec 32} {R : Nat} (L : Lay c w sp)
include L

/-- `longTail`: `16 k` in `r4`, and the tail `P[16k..] xorend D` at `W + 32`. -/
theorem longTail_ok {s : State} (he : Env c w sp R s) {P : BitVec 32} {n : Nat} (hP : Buf w sp s P n)
    (h16 : 16 ≤ n) (hn : n < 2 ^ 32) (h6 : s.gpr .r6 = P) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) :
    WP isa longTail s fun s' => Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .r4 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      s'.gpr .r4 = BitVec.ofNat 32 (16 * kOf n) ∧ Frame (wR w sp) s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 tailOff) (n - 16 * kOf n) =
        Spec.Siv.xorend ((bytesAt s.mem (State.addr P) n).drop (16 * kOf n))
          (bytesAt s.mem (State.addr w + BitVec.ofNat 64 dOff) 16) := by
  have ww := L.ww
  have hT := kOf_tail h16
  generalize hK : 16 * kOf n = K at hT ⊢
  have eT := L.wA (d := tailOff) (by decide)
  refine WP.seq (WP.mono (kBlock_ok h16 hn h5) fun s₁ ⟨h4₁, g₁, k₁⟩ => ?_)
  rw [hK] at h4₁
  have he₁ : Env c w sp R s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide)) k₁.sp k₁.rd k₁.wr
  have h6₁ : s₁.gpr .r6 = P := by rw [g₁ _ (by decide) (by decide), h6]
  have h5₁ : s₁.gpr .r5 = BitVec.ofNat 32 n := by rw [g₁ _ (by decide) (by decide), h5]
  have hq : Buf w sp s₁ (P + BitVec.ofNat 32 K) (n - K) :=
    (hP.sub (j := K) (k := n - K) (by omega) (by omega)).of_eq k₁.rd k₁.wr
  have eK : BitVec.ofNat 32 n - BitVec.ofNat 32 K = BitVec.ofNat 32 (n - K) := ofNat_sub32 (by omega) hn
  rw [tailCopy]
  refine WP.seq (WP.of_runBlock ⟨_, by simp only [tailOff]; arun [h6₁, h5₁, h4₁, he₁.r11], ?_⟩)
  -- The copy of the last `T` bytes.
  refine WP.seq (WP.mono (copyLoop_ok (S := P + BitVec.ofNat 32 K) (D := w + BitVec.ofNat 32 tailOff)
      (n := n - K) _ ⟨by simp [gpr_setReg, h6₁, h4₁], by simp [gpr_setReg, he₁.r11],
      by simp [gpr_setReg, h5₁, h4₁, eK], by omega, by omega, hq.fit,
      by rw [L.wN (by decide)]; simp only [tailOff]; omega, hq.rd,
      by rw [eT]; exact he₁.perm.wC (by simp only [tailOff]; omega),
      by rw [eT]; exact hq.w.sub_right (Lay.wSub (by simp only [tailOff]; omega))⟩) fun s₃ ⟨m₃, lo⟩ => ?_)
  have h11₃ : s₃.gpr .r11 = w := by
    rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [gpr_setReg, he₁.r11]
  have h5₃ : s₃.gpr .r5 = BitVec.ofNat 32 n := by
    rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [gpr_setReg, h5₁]
  have h4₃ : s₃.gpr .r4 = BitVec.ofNat 32 K := by
    rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [gpr_setReg, h4₁]
  refine wp_sub (op2_reg _ _) fun s₄ u₄ => wp_add (op2_reg _ _) fun s₅ u₅ => ?_
  have h0₅ : s₅.gpr .r0 = w + BitVec.ofNat 32 (n - K) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₄.gpr, h11₃, h5₃, h4₃, eK]
  have h11₅ : s₅.gpr .r11 = w := by rw [u₅.other _ (by decide), u₄.other _ (by decide), h11₃]
  have eA : State.addr (w + BitVec.ofNat 32 (n - K)) + BitVec.ofNat 64 16 =
      State.addr w + BitVec.ofNat 64 tailOff + BitVec.ofNat 64 (n - K - 16) := by
    rw [L.wA (by omega), Offset.add_add, Offset.add_add]; congr 2; simp only [tailOff]; omega
  have hrw : s₅.rd ++ s₅.wr = s.rd ++ s.wr := by
    rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, lo.rd, lo.wr]; simp only [rd_setReg, wr_setReg, k₁.rd, k₁.wr]
  have hw₅ : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, lo.wr]; simp only [wr_setReg, k₁.wr]
  rw [xor4_eq]
  refine xorBlk_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [h0₅, L.wN (by omega)]; omega)
    (by rw [h11₅]; simp only [dOff]; omega) (by rw [h0₅, L.wN (by omega)]; omega)
    (by rw [h0₅, eA, hrw, Offset.add_add]; exact covers_left (he.perm.wC (by simp only [tailOff]; omega)))
    (by rw [h11₅, hrw]; exact covers_left (he.perm.wC (by decide)))
    (by rw [h0₅, eA, hw₅, Offset.add_add]; exact he.perm.wC (by simp only [tailOff]; omega)) fun s₆ g₆ => WP.block_nil ?_
  have gT : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → r ≠ .lr →
      s₆.gpr r = s.gpr r := fun r a0 a1 a2 a3 a4 a12 alr => by
    rw [g₆.gpr r a12 alr, u₅.other r a0, u₄.other r a0, lo.other r a0 a1 a2 a3 a12]
    simp only [gpr_setReg, a1, a2, a3, ite_false, reduceCtorEq]
    rw [g₁ r a4 a12]
  have rd₆ : s₆.rd = s.rd := by
    rw [g₆.rd, u₅.rd, u₄.rd, lo.rd]; simp only [rd_setReg, k₁.rd]
  have wr₆ : s₆.wr = s.wr := by rw [g₆.wr, hw₅]
  have sp₆ : s₆.sp = s.sp := by
    rw [g₆.sp, u₅.sp, u₄.sp, lo.sp]; simp only [sp_setReg, k₁.sp]
  have aP : State.addr (P + BitVec.ofNat 32 K) = State.addr P + BitVec.ofNat 64 K := hP.addr (by omega)
  have m₅ : s₅.mem = writeBytes s.mem (State.addr w + BitVec.ofNat 64 tailOff)
      (bytesAt s.mem (State.addr P + BitVec.ofNat 64 K) (n - K)) := by
    rw [u₅.mem, u₄.mem, m₃, eT, aP]; simp only [mem_setReg, k₁.mem]
  have hlx : (bytesAt s.mem (State.addr P + BitVec.ofNat 64 K) (n - K)).length = n - K :=
    Proof.Cmac.bytesAt_length _ _ _
  have fW : Frame [⟨State.addr w + BitVec.ofNat 64 tailOff, n - K⟩] s.mem s₅.mem := by
    rw [m₅]; exact writeBytes_frame _ _ _ (by rw [hlx]; exact Region.contains_self _ _)
  have m₆ : s₆.mem = Proof.Cmac.xor4Mem s₅.mem
      (State.addr w + BitVec.ofNat 64 tailOff + BitVec.ofNat 64 (n - K - 16))
      (State.addr w + BitVec.ofNat 64 tailOff + BitVec.ofNat 64 (n - K - 16))
      (State.addr w + BitVec.ofNat 64 dOff) := by rw [g₆.mem, h0₅, h11₅, eA]
  have dTD : (⟨State.addr w + BitVec.ofNat 64 tailOff, n - K⟩ : Region).Disjoint
      ⟨State.addr w + BitVec.ofNat 64 dOff, 16⟩ := L.w_w (.inl (by simp only [tailOff, dOff]; omega))
        (by simp only [tailOff]; omega) (by decide)
  refine ⟨he.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact gT _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) sp₆ rd₆ wr₆, rd₆, wr₆, fun r hr h4 hlr => ?_, ?_, ?_, ?_⟩
  · have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact gT r a.1 a.2.1 a.2.2.1 a.2.2.2.1 h4 a.2.2.2.2 hlr
  · rw [g₆.gpr _ (by decide) (by decide), u₅.other _ (by decide), u₄.other _ (by decide), h4₃]
  · rw [m₆]
    refine (fW.sub fun r hr => ?_).trans ((Proof.Cmac.xor4Mem_frame _ _ _ _).sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr w + BitVec.ofNat 64 16, 112⟩, by simp,
        Offset.sub _ (by simp only [tailOff]; omega) (by simp only [tailOff]; omega)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨⟨State.addr w + BitVec.ofNat 64 16, 112⟩, by simp, ?_⟩
      rw [Offset.add_add]; exact Offset.sub _ (by simp only [tailOff]; omega) (by simp only [tailOff]; omega)
  · have hBw : (State.addr w + BitVec.ofNat 64 tailOff).toNat + (n - K) ≤ 2 ^ 64 := by
      rw [← eT, addr_toNat, L.wN (by decide)]; simp only [tailOff]; omega
    rw [m₆, xorend_mem4 _ (by omega) hBw dTD,
      m₅, bytesAt_frame (writeBytes_frame _ _ _ (R := ⟨State.addr w + BitVec.ofNat 64 tailOff, n - K⟩)
        (by rw [hlx]; exact Region.contains_self _ _)) (p := State.addr w + BitVec.ofNat 64 dOff)
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dTD.symm) (by decide)]
    have ws := bytesAt_writeBytes_self s.mem (State.addr w + BitVec.ofNat 64 tailOff)
      (bytesAt s.mem (State.addr P + BitVec.ofNat 64 K) (n - K)) (by omega)
    rw [hlx] at ws
    rw [ws]
    have dr := drop_bytesAt s.mem (State.addr P) (a := K) (b := n - K)
    rw [show K + (n - K) = n by omega] at dr
    rw [dr]

omit L in
/-- `jBlock`: `j` in `r7`. -/
theorem jBlock_ok {s : State} {n : Nat} (h16 : 16 ≤ n) (hn : n < 2 ^ 32) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) :
    WP isa jBlock s fun s' => s'.gpr .r7 = BitVec.ofNat 32 (jOf n) ∧
      (∀ r, r ≠ .r7 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have e1 : BitVec.ofNat 32 n - 1#32 = BitVec.ofNat 32 (n - 1) := ofNat_sub32 (by omega) hn
  have e2 : BitVec.ofNat 32 (n - 1) >>> 4 = BitVec.ofNat 32 ((n - 1) / 16) := shr4 (by omega)
  obtain ⟨s₁, run₁, h7₁, hz₁, g₁, k₁⟩ : ∃ s₁, runBlock isa [.dp .sub .r12 .r5 (imm 1),
      .mov .r12 (.shifted .r12 .lsr 4), .mov .r7 (imm 0), .cmp .r12 (imm 0)] s = some s₁ ∧
      s₁.gpr .r7 = 0 ∧ s₁.z = decide ((n - 1) / 16 = 0) ∧
      (∀ r, r ≠ .r7 → r ≠ .r12 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
    refine ⟨_, by arun [h5], ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5, e1, e2]
      exact z_cmp (by omega) (by decide)
    · intro r a b; simp [gpr_setReg, a, b]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  by_cases h0 : (n - 1) / 16 = 0
  · refine WP.ite true (eval_eq' (by rw [hz₁]; simp [h0])) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    refine ⟨by rw [h7₁]; simp [jOf, show n < 17 by omega], g₁, k₁⟩
  · refine WP.ite false (eval_eq' (by rw [hz₁]; simp [h0])) (fun h => by cases h) fun _ => ?_
    refine WP.of_runBlock ⟨_, by arun [], ?_, ?_, ?_⟩
    · simp [gpr_setReg, jOf, show ¬ n < 17 by omega]
    · intro r a b; simp [gpr_setReg, a, g₁ r a b]
    · exact ⟨k₁.mem, k₁.rd, k₁.wr, k₁.sp⟩

/-- What `longMac out` computes, from the memory `m` before it: the CMAC of
the `k` blocks of `P`, the first `j` blocks of the tail, and the rest of the
tail. -/
def longVal (m : Mem) (C W P : Addr) (R n : Nat) : List Byte :=
  Spec.Siv.schedCiph m C R (Spec.Cmac.xor
    (Spec.Cmac.lastBlock 16 (bytesAt m (C + BitVec.ofNat 64 240) 16) (bytesAt m (C + BitVec.ofNat 64 256) 16)
      ((bytesAt m (W + BitVec.ofNat 64 tailOff) (n - 16 * kOf n)).drop (16 * jOf n)))
    (Spec.Cmac.chain (Spec.Siv.schedCiph m C R)
      (Spec.Cmac.chain (Spec.Siv.schedCiph m C R) (Spec.Cmac.zeros 16)
        (Spec.Cmac.blocks 16 ((bytesAt m P n).take (16 * kOf n))))
      (Spec.Cmac.blocks 16 ((bytesAt m (W + BitVec.ofNat 64 tailOff) (n - 16 * kOf n)).take (16 * jOf n)))))

/-- What the calls of `longMac out` write. -/
abbrev outR (w sp : BitVec 32) (out : Nat) : List Region :=
  [⟨State.addr w + BitVec.ofNat 64 out, 16⟩, scrR w, blw sp]

/-- `longArgs₁ out`: the state at `W + out` zeroed, and the arguments of
`vg_cmac_aes_update` over the `K / 16` blocks of the string. -/
theorem longArgs₁_ok {s : State} (he : Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {P : BitVec 32}
    {n K : Nat} (hP : Buf w sp s P n) (hKn : K ≤ n) (hK16 : 16 * (K / 16) = K) (hn : n < 2 ^ 32)
    (h6 : s.gpr .r6 = P) (h4 : s.gpr .r4 = BitVec.ofNat 32 K) {out : Nat} (hout : out = 0 ∨ out = tOff) :
    WP isa (.block (longArgs₁ out)) s fun s₂ => Env c w sp R s₂ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₂.gpr r = s.gpr r) ∧
      s₂.rd = s.rd ∧ s₂.wr = s.wr ∧ s₂.mem = Proof.Cmac.zero4 s.mem (State.addr w + BitVec.ofNat 64 out) ∧
      UArgs s₂ c (w + BitVec.ofNat 32 out) P (w + BitVec.ofNat 32 256) R (K / 16) := by
  have ww := L.ww
  have ho16 : out + 16 ≤ 128 := by rcases hout with rfl | rfl <;> decide
  have eo : encodable (BitVec.ofNat 32 out) = true := by rcases hout with rfl | rfl <;> decide
  rw [longArgs₁, List.append_assoc]
  refine zero16_ok L he (d := out) (by omega) fun s₁ g₁ m₁ rd₁ wr₁ sp₁ => ?_
  have he₁ : Env c w sp R s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₁ _ (by decide)) sp₁ rd₁ wr₁
  have hq := (hP.take (k := K) hKn).of_eq rd₁ wr₁
  have hsh : BitVec.ofNat 32 K >>> 4 = BitVec.ofNat 32 (K / 16) := shr4 (by omega)
  obtain ⟨s₂, run₂, he₂, g₂, k₂, U₁⟩ : ∃ s₂, runBlock isa (macArgs out ++ [mov .r3 .r6, .mov .r12 (.shifted .r4 .lsr 4)])
      s₁ = some s₂ ∧ Env c w sp R s₂ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ ∧
      UArgs s₂ c (w + BitVec.ofNat 32 out) P (w + BitVec.ofNat 32 256) R (K / 16) := by
    have h6₁ : s₁.gpr .r6 = P := by rw [g₁ _ (by decide), h6]
    have h4₁ : s₁.gpr .r4 = BitVec.ofNat 32 K := by rw [g₁ _ (by decide), h4]
    refine ⟨_, by simp only [macArgs, csOff, mov]; arun [he₁.r9, he₁.r10, he₁.r11, eo], ?_⟩
    refine ⟨he₁.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl,
      fun r a b c' d e f => by simp [gpr_setReg, a, b, c', d, e, f], ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
    refine uargs_of L ?_ hR (st := out) (by omega) (n := K / 16) (by omega)
      (by rw [show 16 * (K / 16) = K by omega]; exact hq.fit) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact he₁.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl
    · rw [show 16 * (K / 16) = K by omega]; exact hq.w.sub_right (Lay.wSub (by omega))
    · rw [show 16 * (K / 16) = K by omega]; exact hq.w.sub_right (Lay.wSub (by decide))
    · rw [show 16 * (K / 16) = K by omega]; exact hq.stk
    · rw [show 16 * (K / 16) = K by omega]; exact hq.rd
    · simp [gpr_setReg, he₁.r10]
    · simp [gpr_setReg, he₁.r9]
    · simp [gpr_setReg, he₁.r11]
    · simp [gpr_setReg, h6₁]
    · simp [gpr_setReg, h4₁, hsh]
    · simp [gpr_setReg, he₁.r11]
  exact WP.of_runBlock ⟨s₂, run₂, he₂, fun r a b c' d e f => by rw [g₂ r a b c' d e f, g₁ r e],
    by rw [k₂.rd, rd₁], by rw [k₂.wr, wr₁], by rw [k₂.mem, m₁], U₁⟩

/-- `longArgs₂ out`: the arguments of `vg_cmac_aes_update` over the first `j`
blocks of the tail. -/
theorem longArgs₂_ok {s₄ : State} (he₄ : Env c w sp R s₄) (hR : R = 10 ∨ R = 12 ∨ R = 14) {out : Nat}
    (hout : out = 0 ∨ out = tOff) {j : Nat} (hj1 : j ≤ 1) (h7₄ : s₄.gpr .r7 = BitVec.ofNat 32 j) :
    ∃ s₅, runBlock isa (longArgs₂ out) s₄ = some s₅ ∧ Env c w sp R s₅ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₅.gpr r = s₄.gpr r) ∧ Keeps s₄ s₅ ∧
      UArgs s₅ c (w + BitVec.ofNat 32 out) (w + BitVec.ofNat 32 tailOff) (w + BitVec.ofNat 32 256) R j := by
  have ww := L.ww
  have ho16 : out + 16 ≤ 128 := by rcases hout with rfl | rfl <;> decide
  have hoT : out + 16 ≤ tailOff ∨ tailOff + 32 ≤ out := by rcases hout with rfl | rfl <;> decide
  have eo : encodable (BitVec.ofNat 32 out) = true := by rcases hout with rfl | rfl <;> decide
  have eT := L.wA (d := tailOff) (by decide)
  refine ⟨_, by simp only [longArgs₂, macArgs, csOff, tailOff, mov]; arun [he₄.r9, he₄.r10, he₄.r11, eo], ?_⟩
  refine ⟨he₄.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl,
    fun r a b c' d e f => by simp [gpr_setReg, a, b, c', d, e, f], ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  refine uargs_of L ?_ hR (st := out) (by omega) (n := j) (by omega)
    (by rw [L.wN (by decide)]; simp only [tailOff]; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact he₄.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl
  · rw [eT]; exact L.w_w (by simp only [tailOff] at hoT ⊢; omega) (by simp only [tailOff]; omega) (by omega)
  · rw [eT]; exact L.w_w (.inl (by simp only [tailOff]; omega)) (by simp only [tailOff]; omega) (by decide)
  · rw [eT]; exact L.stk_w' (by simp only [tailOff]; omega)
  · rw [eT]; exact covers_left (he₄.perm.wC (by simp only [tailOff]; omega))
  · simp [gpr_setReg, he₄.r10]
  · simp [gpr_setReg, he₄.r9]
  · simp [gpr_setReg, he₄.r11]
  · simp [gpr_setReg, he₄.r11]
  · simp [gpr_setReg, h7₄]
  · simp [gpr_setReg, he₄.r11]

/-- `longArgs₃ out`: the arguments of `vg_cmac_aes_finalize` over the rest of
the tail. -/
theorem longArgs₃_ok {s₆ : State} (he₆ : Env c w sp R s₆) (hR : R = 10 ∨ R = 12 ∨ R = 14) {out : Nat}
    (hout : out = 0 ∨ out = tOff) {n K j : Nat} (hn : n < 2 ^ 32) (hT : 16 ≤ n - K ∧ n - K ≤ 32)
    (hJ : 16 * j ≤ n - K ∧ 0 < n - K - 16 * j ∧ n - K - 16 * j ≤ 16) (hj1 : j ≤ 1)
    (h7₆ : s₆.gpr .r7 = BitVec.ofNat 32 j) (h5₆ : s₆.gpr .r5 = BitVec.ofNat 32 n)
    (h4₆ : s₆.gpr .r4 = BitVec.ofNat 32 K) :
    ∃ s₇, runBlock isa (longArgs₃ out) s₆ = some s₇ ∧ Env c w sp R s₇ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₇.gpr r = s₆.gpr r) ∧ Keeps s₆ s₇ ∧
      FArgs s₇ c (w + BitVec.ofNat 32 out) (w + BitVec.ofNat 32 (tailOff + 16 * j)) (w + BitVec.ofNat 32 256)
        (n - K - 16 * j) R := by
  have ww := L.ww
  have ho16 : out + 16 ≤ 128 := by rcases hout with rfl | rfl <;> decide
  have hoT : out + 16 ≤ tailOff ∨ tailOff + 32 ≤ out := by rcases hout with rfl | rfl <;> decide
  have eo : encodable (BitVec.ofNat 32 out) = true := by rcases hout with rfl | rfl <;> decide
  have e7 : BitVec.ofNat 32 j <<< 4 = BitVec.ofNat 32 (16 * j) := shl4 (by omega)
  have eR : BitVec.ofNat 32 n - BitVec.ofNat 32 K - BitVec.ofNat 32 (16 * j) =
      BitVec.ofNat 32 (n - K - 16 * j) := by
    rw [ofNat_sub32 (by omega) hn, ofNat_sub32 (by omega) (by omega)]
  have eA : w + BitVec.ofNat 32 tailOff + BitVec.ofNat 32 (16 * j) = w + BitVec.ofNat 32 (tailOff + 16 * j) :=
    add32_ofNat_assoc _ _ _
  refine ⟨_, by simp only [longArgs₃, macArgs, csOff, mov]; arun [he₆.r9, he₆.r10, he₆.r11, eo], ?_⟩
  refine ⟨he₆.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl,
    fun r a b c' d e f => by simp [gpr_setReg, a, b, c', d, e, f], ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  refine fargs_of L ?_ hR (st := out) (by omega) (n := n - K - 16 * j) (by omega)
    (by rw [L.wN (by simp only [tailOff]; omega)]; simp only [tailOff]; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact he₆.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl
  · rw [L.wA (by simp only [tailOff]; omega)]
    exact L.w_w (by simp only [tailOff] at hoT ⊢; omega) (by simp only [tailOff]; omega) (by omega)
  · rw [L.wA (by simp only [tailOff]; omega)]
    exact L.w_w (.inl (by simp only [tailOff]; omega)) (by simp only [tailOff]; omega) (by decide)
  · rw [L.wA (by simp only [tailOff]; omega)]; exact L.stk_w' (by simp only [tailOff]; omega)
  · rw [L.wA (by simp only [tailOff]; omega)]; exact covers_left (he₆.perm.wC (by simp only [tailOff]; omega))
  · simp [gpr_setReg, he₆.r10]
  · simp [gpr_setReg, he₆.r9]
  · simp [gpr_setReg, he₆.r11]
  · simp [gpr_setReg, he₆.r11, h7₆, e7, eA]
  · simp [gpr_setReg, h5₆, h4₆, h7₆, e7, eR]
  · simp [gpr_setReg, he₆.r11]

/-- `longMac out`: S2V's end for a long string, from its tail, at `W + out`. -/
theorem longMac_ok {s : State} (he : Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {P : BitVec 32} {n : Nat}
    (hP : Buf w sp s P n) (h16 : 16 ≤ n) (hn : n < 2 ^ 32) (h6 : s.gpr .r6 = P)
    (h5 : s.gpr .r5 = BitVec.ofNat 32 n) (h4 : s.gpr .r4 = BitVec.ofNat 32 (16 * kOf n)) {out : Nat}
    (hout : out = 0 ∨ out = tOff) :
    WP isa (longMac out) s fun s' => Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .r7 → r ≠ .lr → s'.gpr r = s.gpr r) ∧ Frame (outR w sp out) s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 out) 16 =
        longVal s.mem (State.addr c) (State.addr w) (State.addr P) R n := by
  have ww := L.ww
  have hT := kOf_tail h16
  have hJ := jOf_rest h16
  have hj1 := jOf_le n
  have ho16 : out + 16 ≤ 128 := by rcases hout with rfl | rfl <;> decide
  have hoT : out + 16 ≤ tailOff ∨ tailOff + 32 ≤ out := by rcases hout with rfl | rfl <;> decide
  have eo : encodable (BitVec.ofNat 32 out) = true := by rcases hout with rfl | rfl <;> decide
  have eT := L.wA (d := tailOff) (by decide)
  have eO := L.wA (d := out) (by omega)
  have eS := L.wA (d := 256) (by decide)
  have hRb := rounds_le hR
  generalize hK : 16 * kOf n = K at hT hJ h4 ⊢
  have hKk : K / 16 = kOf n := by omega
  generalize hj : jOf n = j at hJ hj1 ⊢
  -- The first call's arguments.
  rw [longMac]
  refine WP.seq (WP.mono (longArgs₁_ok L he hR hP (by omega) (by omega) hn h6 h4 hout)
    fun s₂ ⟨he₂, g₂, rd₂, wr₂, m₂, U₁⟩ => ?_)
  refine WP.seq (WP.mono (upd_call U₁) fun s₃ h₃ => ?_)
  have he₃ := he₂.of_saved h₃.saved h₃.sp h₃.rd h₃.wr
  have g₃ : ∀ r ∈ preserved, r ≠ .lr → s₃.gpr r = s.gpr r := fun r hr hlr => by
    have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [h₃.saved r hr hlr, g₂ r a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2 hlr]
  have h5₃ : s₃.gpr .r5 = BitVec.ofNat 32 n := by rw [g₃ _ (by decide) (by decide), h5]
  have h4₃ : s₃.gpr .r4 = BitVec.ofNat 32 K := by rw [g₃ _ (by decide) (by decide), h4]
  -- `j`.
  refine WP.seq (WP.mono (jBlock_ok h16 hn h5₃) fun s₄ ⟨h7₄, g₄, k₄⟩ => ?_)
  rw [hj] at h7₄
  have he₄ : Env c w sp R s₄ := he₃.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₄ _ (by decide) (by decide)) k₄.sp k₄.rd k₄.wr
  have h5₄ : s₄.gpr .r5 = BitVec.ofNat 32 n := by rw [g₄ _ (by decide) (by decide), h5₃]
  have h4₄ : s₄.gpr .r4 = BitVec.ofNat 32 K := by rw [g₄ _ (by decide) (by decide), h4₃]
  -- The second call's arguments: the first `j` blocks of the tail.
  obtain ⟨s₅, run₅, he₅, g₅, k₅, U₂⟩ := longArgs₂_ok L he₄ hR hout hj1 h7₄
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  refine WP.seq (WP.mono (upd_call U₂) fun s₆ h₆ => ?_)
  have he₆ := he₅.of_saved h₆.saved h₆.sp h₆.rd h₆.wr
  have g₆ : ∀ r ∈ preserved, r ≠ .r7 → r ≠ .lr → s₆.gpr r = s₄.gpr r := fun r hr h7 hlr => by
    have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [h₆.saved r hr hlr, g₅ r a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2 hlr]
  have h7₆ : s₆.gpr .r7 = BitVec.ofNat 32 j := by
    rw [h₆.saved _ (by decide) (by decide), g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h7₄]
  have h5₆ : s₆.gpr .r5 = BitVec.ofNat 32 n := by rw [g₆ _ (by decide) (by decide) (by decide), h5₄]
  have h4₆ : s₆.gpr .r4 = BitVec.ofNat 32 K := by rw [g₆ _ (by decide) (by decide) (by decide), h4₄]
  -- The third call's arguments: the rest of the tail.
  obtain ⟨s₇, run₇, he₇, g₇, k₇, F⟩ := longArgs₃_ok L he₆ hR hout hn hT hJ hj1 h7₆ h5₆ h4₆
  refine WP.seq (WP.of_runBlock ⟨s₇, run₇, ?_⟩)
  refine WP.mono (fin_call F) fun s₈ h₈ => ?_
  have hb₂ := blw16_eq (s := s₂) he₂.sp
  have hb₅ := blw16_eq (s := s₅) he₅.sp
  have hb₇ := blw16_eq (s := s₇) he₇.sp
  -- What each step writes.
  have F₃ : Frame (outR w sp out) s₂.mem s₃.mem := by
    have := h₃.frame; rw [eO, eS, hb₂] at this; exact this
  have F₆ : Frame (outR w sp out) s₅.mem s₆.mem := by
    have := h₆.frame; rw [eO, eS, hb₅] at this; exact this
  have F₈ : Frame (outR w sp out) s₇.mem s₈.mem := by
    have := h₈.frame; rw [eO, eS, hb₇] at this; exact this
  have F₀₂ : Frame (outR w sp out) s.mem s₂.mem := by
    rw [m₂]; exact (Proof.Cmac.frame_store4 _ _ _ _ _).mono (by simp)
  have F₀₃ : Frame (outR w sp out) s.mem s₃.mem := F₀₂.trans F₃
  have F₀₅ : Frame (outR w sp out) s.mem s₅.mem := by rw [k₅.mem, k₄.mem]; exact F₀₃
  have F₀₆ : Frame (outR w sp out) s.mem s₆.mem := F₀₅.trans F₆
  have F₀₇ : Frame (outR w sp out) s.mem s₇.mem := by rw [k₇.mem]; exact F₀₆
  refine ⟨he₇.of_saved h₈.saved h₈.sp h₈.rd h₈.wr, by rw [h₈.rd, k₇.rd, h₆.rd, k₅.rd, k₄.rd, h₃.rd, rd₂],
    by rw [h₈.wr, k₇.wr, h₆.wr, k₅.wr, k₄.wr, h₃.wr, wr₂], fun r hr h7 hlr => ?_, F₀₇.trans F₈, ?_⟩
  · have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [h₈.saved r hr hlr, g₇ r a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2 hlr, g₆ r hr h7 hlr, g₄ r h7 a.2.2.2.2,
      g₃ r hr hlr]
  -- What the calls read is as on entry, but the state.
  have dc : ∀ {d k : Nat}, d + k ≤ 512 → ∀ r ∈ outR w sp out, (⟨State.addr c + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k hd r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact L.c_w' hd (by omega)
    · exact L.c_w' hd (by decide)
    · exact (L.stk_c' hd).symm
  have dt : ∀ {d k : Nat}, tailOff + d + k ≤ 64 → ∀ r ∈ outR w sp out,
      (⟨State.addr w + BitVec.ofNat 64 tailOff + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
    intro d k hd r hr
    rw [Offset.add_add]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact L.w_w (by simp only [tailOff] at hoT hd ⊢; omega) (by omega) (by omega)
    · exact L.w_w (.inl (by simp only [tailOff] at hd ⊢; omega)) (by omega) (by decide)
    · exact (L.stk_w' (by omega)).symm
  have dp : ∀ r ∈ outR w sp out, (⟨State.addr P, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hP.w.sub_right (Lay.wSub (by omega))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm
  have cK {m' : Mem} (hf : Frame (outR w sp out) s.mem m') {d k : Nat} (hd : d + k ≤ 512) :
      bytesAt m' (State.addr c + BitVec.ofNat 64 d) k = bytesAt s.mem (State.addr c + BitVec.ofNat 64 d) k :=
    bytesAt_frame hf (dc hd) (by omega)
  have cT {m' : Mem} (hf : Frame (outR w sp out) s.mem m') {d k : Nat} (hd : tailOff + d + k ≤ 64) :
      bytesAt m' (State.addr w + BitVec.ofNat 64 tailOff + BitVec.ofNat 64 d) k =
        bytesAt s.mem (State.addr w + BitVec.ofNat 64 tailOff + BitVec.ofNat 64 d) k :=
    bytesAt_frame hf (dt hd) (by omega)
  have k0 : ∀ a : Addr, a + BitVec.ofNat 64 0 = a := fun a => BitVec.add_zero a
  have sch₂ := cK F₀₂ (d := 0) (k := 16 * (R + 1)) (by omega)
  have sch₅ := cK F₀₅ (d := 0) (k := 16 * (R + 1)) (by omega)
  have sch₇ := cK F₀₇ (d := 0) (k := 16 * (R + 1)) (by omega)
  rw [k0] at sch₂ sch₅ sch₇
  have k1 := cK F₀₇ (d := 240) (k := 16) (by decide)
  have k2 := cK F₀₇ (d := 256) (k := 16) (by decide)
  have pK : bytesAt s₂.mem (State.addr P) K = bytesAt s.mem (State.addr P) K :=
    bytesAt_frame F₀₂ (fun r hr => (dp r hr).sub_left (Region.sub_prefix (by omega))) (by omega)
  have tJ := cT F₀₅ (d := 0) (k := 16 * j) (by simp only [tailOff]; omega)
  have tR := cT F₀₇ (d := 16 * j) (k := n - K - 16 * j) (by simp only [tailOff]; omega)
  rw [k0] at tJ
  have z₂ : bytesAt s₂.mem (State.addr w + BitVec.ofNat 64 out) 16 = Spec.Cmac.zeros 16 := by
    rw [m₂, Proof.Cmac.zero4_bytes]
  have o₃ := h₃.out
  have o₆ := h₆.out
  have o₈ := h₈.out
  rw [eO, sch₂, z₂, Proof.Cmac.Stream.blocksAt_eq, show 16 * (K / 16) = K by omega, pK] at o₃
  rw [eO, eT, sch₅, k₅.mem, k₄.mem, o₃, Proof.Cmac.Stream.blocksAt_eq, ← k₄.mem, ← k₅.mem, tJ] at o₆
  rw [eO, L.wA (by simp only [tailOff]; omega), ← Offset.add_add, sch₇, k1, k2, tR, k₇.mem, o₆] at o₈
  rw [o₈, longVal, Spec.Siv.schedCiph, hK, hj]
  -- The pieces of `P` and of the tail.
  have tk := take_bytesAt s.mem (State.addr P) (a := K) (b := n - K)
  rw [show K + (n - K) = n by omega] at tk
  have tk' := take_bytesAt s.mem (State.addr w + BitVec.ofNat 64 tailOff) (a := 16 * j) (b := n - K - 16 * j)
  rw [show 16 * j + (n - K - 16 * j) = n - K by omega] at tk'
  have dr' := drop_bytesAt s.mem (State.addr w + BitVec.ofNat 64 tailOff) (a := 16 * j) (b := n - K - 16 * j)
  rw [show 16 * j + (n - K - 16 * j) = n - K by omega] at dr'
  rw [tk, tk', dr']

omit L in
theorem outR_oR {out : Nat} : ∀ r ∈ outR w sp out, ∃ r' ∈ oR w sp out, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨⟨State.addr w + BitVec.ofNat 64 176, 2400⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  · exact ⟨blw sp, by simp, fun _ h => h⟩

/-- S2V's end for a string `P` of a block or more, into `W + out`. -/
theorem long_ok {s : State} (he : Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {P : BitVec 32} {n : Nat}
    (hP : Buf w sp s P n) (h16 : 16 ≤ n) (hn : n < 2 ^ 32) (h6 : s.gpr .r6 = P)
    (h5 : s.gpr .r5 = BitVec.ofNat 32 n) {out : Nat} (hout : out = 0 ∨ out = tOff) :
    WP isa (.seq longTail (longMac out)) s fun s' => Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .r4 → r ≠ .r7 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      Frame (oR w sp out) s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 out) 16 =
        Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem (State.addr c) R)
          (bytesAt s.mem (State.addr w + BitVec.ofNat 64 dOff) 16) (bytesAt s.mem (State.addr P) n) := by
  have ho16 : out + 16 ≤ 128 := by rcases hout with rfl | rfl <;> decide
  refine WP.seq (WP.mono (longTail_ok L he hP h16 hn h6 h5) fun s₁ ⟨he₁, rd₁, wr₁, g₁, h4₁, f₁, t₁⟩ => ?_)
  have h6₁ : s₁.gpr .r6 = P := by rw [g₁ _ (by decide) (by decide) (by decide), h6]
  have h5₁ : s₁.gpr .r5 = BitVec.ofNat 32 n := by rw [g₁ _ (by decide) (by decide) (by decide), h5]
  refine WP.mono (longMac_ok L he₁ hR (hP.of_eq rd₁ wr₁) h16 hn h6₁ h5₁ h4₁ hout)
    fun s₂ ⟨he₂, rd₂, wr₂, g₂, f₂, o₂⟩ => ?_
  refine ⟨he₂, by rw [rd₂, rd₁], by rw [wr₂, wr₁], fun r hr h4 h7 hlr => by rw [g₂ r hr h7 hlr, g₁ r hr h4 hlr],
    (frame_oR out f₁).trans (f₂.sub outR_oR), ?_⟩
  have hRb := rounds_le hR
  have dc : ∀ {d k : Nat}, d + k ≤ 512 → ∀ r ∈ wR w sp, (⟨State.addr c + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r :=
    fun hd => dis_wR (L.c_w.sub_left (Lay.cSub hd)) (L.stk_c' hd)
  have cK {d k : Nat} (hd : d + k ≤ 512) :
      bytesAt s₁.mem (State.addr c + BitVec.ofNat 64 d) k = bytesAt s.mem (State.addr c + BitVec.ofNat 64 d) k :=
    bytesAt_frame f₁ (dc hd) (by omega)
  have sch := cK (d := 0) (k := 16 * (R + 1)) (by omega)
  rw [BitVec.add_zero] at sch
  have pP : bytesAt s₁.mem (State.addr P) n = bytesAt s.mem (State.addr P) n :=
    bytesAt_frame f₁ (dis_wR hP.w hP.stk) (by omega)
  rw [o₂, longVal, Spec.Siv.schedCiph, sch, cK (d := 240) (k := 16) (by decide), cK (d := 256) (k := 16) (by decide),
    t₁, pP, Spec.Siv.ctxMac, Spec.Siv.schedCiph, show (240 : Addr) = BitVec.ofNat 64 240 from rfl,
    show (256 : Addr) = BitVec.ofNat 64 256 from rfl]
  have hl : 16 ≤ (bytesAt s.mem (State.addr P) n).length := by rw [Proof.Cmac.bytesAt_length]; exact h16
  have ls := long_spec (Spec.Cmac.aesWith R (bytesAt s.mem (State.addr c) (16 * (R + 1))))
    (bytesAt s.mem (State.addr c + BitVec.ofNat 64 240) 16) (bytesAt s.mem (State.addr c + BitVec.ofNat 64 256) 16)
    (bytesAt s.mem (State.addr w + BitVec.ofNat 64 dOff) 16) (bytesAt s.mem (State.addr P) n)
    (Proof.Cmac.bytesAt_length _ _ _) hl
  rw [Proof.Cmac.bytesAt_length s.mem (State.addr P) n] at ls
  exact ls

omit L in
/-- `finish`'s first block: `Z` set iff the string is shorter than a block. -/
theorem finishPre_ok {s : State} {n : Nat} (hn : n < 2 ^ 32) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) :
    ∃ s₁, runBlock isa [.mov .r12 (.shifted .r5 .lsr 4), .cmp .r12 (imm 0)] s =
      some s₁ ∧ s₁.z = decide (n / 16 = 0) ∧ (∀ r, r ≠ .r12 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
  refine ⟨_, by arun [h5], ?_, ?_, ?_⟩
  · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5, shr4 hn]
    exact z_cmp (by omega) (by decide)
  · intro r a; simp [gpr_setReg, a]
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- `finish out`: S2V's end with the string `P` (`n` bytes, in `r6` and
`r5`) from `D`, into `W + out`. -/
theorem finish_ok {s : State} (he : Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {P : BitVec 32} {n : Nat}
    (hP : Buf w sp s P n) (hn : n < 2 ^ 32) (h6 : s.gpr .r6 = P) (h5 : s.gpr .r5 = BitVec.ofNat 32 n)
    {out : Nat} (hout : out = 0 ∨ out = tOff) :
    WP isa (finish out) s fun s' => Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .r4 → r ≠ .r6 → r ≠ .r7 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      Frame (oR w sp out) s.mem s'.mem ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 out) 16 =
        Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem (State.addr c) R)
          (bytesAt s.mem (State.addr w + BitVec.ofNat 64 dOff) 16) (bytesAt s.mem (State.addr P) n) := by
  obtain ⟨s₁, run₁, hz₁, g₁, k₁⟩ := finishPre_ok hn h5
  have he₁ : Env c w sp R s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₁ _ (by decide)) k₁.sp k₁.rd k₁.wr
  have hP₁ := hP.of_eq k₁.rd k₁.wr
  have h6₁ : s₁.gpr .r6 = P := by rw [g₁ _ (by decide), h6]
  have h5₁ : s₁.gpr .r5 = BitVec.ofNat 32 n := by rw [g₁ _ (by decide), h5]
  have gP : ∀ r ∈ preserved, s₁.gpr r = s.gpr r := fun r hr => g₁ r (by
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  rw [finish]
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  by_cases h0 : n / 16 = 0
  · refine WP.ite true (eval_eq' (by rw [hz₁]; simp [h0])) (fun _ => ?_) (fun h => by cases h)
    refine WP.mono (short_ok L he₁ hR hP₁ (by omega) h6₁ h5₁ hout) fun s₂ ⟨he₂, rd₂, wr₂, g₂, f₂, o₂⟩ => ?_
    refine ⟨he₂, by rw [rd₂, k₁.rd], by rw [wr₂, k₁.wr], fun r hr h4 h6 _ hlr => by rw [g₂ r hr h4 h6 hlr, gP r hr],
      by rw [← k₁.mem]; exact f₂, by rw [o₂, k₁.mem]⟩
  · refine WP.ite false (eval_eq' (by rw [hz₁]; simp [h0])) (fun h => by cases h) fun _ => ?_
    refine WP.mono (long_ok L he₁ hR hP₁ (by omega) hn h6₁ h5₁ hout) fun s₂ ⟨he₂, rd₂, wr₂, g₂, f₂, o₂⟩ => ?_
    refine ⟨he₂, by rw [rd₂, k₁.rd], by rw [wr₂, k₁.wr], fun r hr h4 _ h7 hlr => by rw [g₂ r hr h4 h7 hlr, gP r hr],
      by rw [← k₁.mem]; exact f₂, by rw [o₂, k₁.mem]⟩

end

end VG.Proof.AesSiv.Arm

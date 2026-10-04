import VerifiedGarbage.Proof.AesSiv.Arm.Seal
import VerifiedGarbage.Proof.AesCcm.Arm.Mask

/-!
# AES-SIV on ARMv7: `vg_aes_siv_decrypt`

Untrusted: everything here is checked by Lean. `decrypt` runs S2V over the
associated data (`s2v_ok`), decrypts the data with CTR from the received
IV at `W` (`ctr_ok`), finishes S2V with the plaintext into `W + 112`
(`finish_ok`), sets `r0` to 1 if the two IVs are equal and 0 if not,
without a branch (`compare_ok`), ANDs every byte of the plaintext with
`0 − r0` (`maskData_ok`) and restores the registers (`decrypt_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesSiv.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI)
open VG.Proof.AesCcm.Arm (blw mask_byte length_mask mask_succ)
open VG.Proof.AesGcm.Arm (bytesAt_frame SavedAt savedR restore_ok covers_left covers_prefix in_off)
open VG.Proof.MdStream.Arm (wp_ldrSp)
open VG.Proof.AesGcm.Arm (Keeps z_subFlags gpr_subFlags z_cmp eval_eq' eval_ne' addr_i dec32 z_dec in_of_covers
  bytesAt_succ mem_store gpr_store add32_ofNat_assoc in_left add_ofNat_zero mem_subFlags bytes_words cmp_value
  words_eq_iff runBlock_app_of add_ofNat_assoc)

section
variable {c w sp : BitVec 32} {R : Nat} (L : Lay c w sp)
include L

/-- `compare`: `r0` is 1 iff the 16 bytes at `W` and `W + 112` are equal. -/
theorem compare_ok {s : State} (he : Env c w sp R s) :
    ∃ s', runBlock isa compare s = some s' ∧
      s'.gpr .r0 = (if bytesAt s.mem (State.addr w + BitVec.ofNat 64 0) 16 =
        bytesAt s.mem (State.addr w + BitVec.ofNat 64 tOff) 16 then 1 else 0) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have h11 := he.r11
  have r₀ := he.perm.wR (show 0 + 4 ≤ 2576 by decide)
  have r₁ := he.perm.wR (show 4 + 4 ≤ 2576 by decide)
  have r₂ := he.perm.wR (show 8 + 4 ≤ 2576 by decide)
  have r₃ := he.perm.wR (show 12 + 4 ≤ 2576 by decide)
  have q₀ := he.perm.wR (show 112 + 4 ≤ 2576 by decide)
  have q₁ := he.perm.wR (show 116 + 4 ≤ 2576 by decide)
  have q₂ := he.perm.wR (show 120 + 4 ≤ 2576 by decide)
  have q₃ := he.perm.wR (show 124 + 4 ≤ 2576 by decide)
  let m := s.mem
  let a := fun k : Nat => m.readW (State.addr w + BitVec.ofNat 64 (4 * k)) 32
  let b := fun k : Nat => m.readW (State.addr w + BitVec.ofNat 64 (112 + 4 * k)) 32
  obtain ⟨s₁, run₁, g₁, h0₁, k₁⟩ : ∃ s₁, runBlock isa (xorW .r0 0 ++ xorW .r1 1 ++ [.dp .orr .r0 .r0 (.reg .r1)]) s =
      some s₁ ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → s₁.gpr r = s.gpr r) ∧
      s₁.gpr .r0 = (a 0 ^^^ b 0 ||| a 1 ^^^ b 1) ∧ Keeps s s₁ := by
    refine ⟨_, by simp only [xorW, tOff]; arun [h11, L.wA, r₀, r₁, q₀, q₁], ?_, ?_, ?_⟩
    · intro r x y z; simp [gpr_setReg, x, y, z]
    · simp [gpr_setReg, a, b, m]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have h11₁ : s₁.gpr .r11 = w := by rw [g₁ _ (by decide) (by decide) (by decide), h11]
  have hm₁ := k₁.mem
  obtain ⟨s₂, run₂, g₂, h0₂, k₂⟩ : ∃ s₂, runBlock isa (xorW .r1 2 ++ [.dp .orr .r0 .r0 (.reg .r1)] ++ xorW .r1 3 ++
      [.dp .orr .r0 .r0 (.reg .r1)]) s₁ = some s₂ ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → s₂.gpr r = s₁.gpr r) ∧
      s₂.gpr .r0 = ((a 0 ^^^ b 0 ||| a 1 ^^^ b 1) ||| a 2 ^^^ b 2) ||| a 3 ^^^ b 3 ∧ Keeps s₁ s₂ := by
    rw [← k₁.rd, ← k₁.wr] at r₂ r₃ q₂ q₃
    refine ⟨_, by simp only [xorW, tOff]; arun [h11₁, L.wA, r₂, r₃, q₂, q₃, hm₁], ?_, ?_, ?_⟩
    · intro r x y z; simp [gpr_setReg, x, y, z]
    · simp [gpr_setReg, a, b, m, h0₁, hm₁]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨s₃, run₃, g₃, h0₃, k₃⟩ : ∃ s₃, runBlock isa [.mov .r1 (imm 0), .dp .sub .r1 .r1 (.reg .r0),
      .dp .orr .r0 .r0 (.reg .r1), .mov .r0 (.shifted .r0 .lsr 31), .mov .r1 (imm 1), .dp .sub .r0 .r1 (.reg .r0)] s₂ =
      some s₃ ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → s₃.gpr r = s₂.gpr r) ∧
      s₃.gpr .r0 = BitVec.ofNat 32 1 - ((s₂.gpr .r0 ||| (BitVec.ofNat 32 0 - s₂.gpr .r0)) >>> 31) ∧ Keeps s₂ s₃ := by
    refine ⟨_, by arun [], ?_, ?_, ?_⟩
    · intro r x y; simp [gpr_setReg, x, y]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, Op2.eval]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨s₃, ?_, ?_, ?_, k₁.trans (k₂.trans k₃)⟩
  · rw [show compare = (xorW .r0 0 ++ xorW .r1 1 ++ [.dp .orr .r0 .r0 (.reg .r1)]) ++
      ((xorW .r1 2 ++ [.dp .orr .r0 .r0 (.reg .r1)] ++ xorW .r1 3 ++ [.dp .orr .r0 .r0 (.reg .r1)]) ++
      [.mov .r1 (imm 0), .dp .sub .r1 .r1 (.reg .r0), .dp .orr .r0 .r0 (.reg .r1), .mov .r0 (.shifted .r0 .lsr 31),
        .mov .r1 (imm 1), .dp .sub .r0 .r1 (.reg .r0)]) from rfl]
    exact runBlock_app_of run₁ (runBlock_app_of run₂ run₃)
  · rw [h0₃, h0₂, cmp_value, bytes_words, bytes_words]
    simp only [add_ofNat_assoc]
    congr 1
    simp only [a, b, m, tOff, Nat.mul_zero, Nat.add_zero]
    exact propext (words_eq_iff _ _ _ _ _ _ _ _).symm
  · intro r x y z; rw [g₃ r x y, g₂ r x y z, g₁ r x y z]

omit L in
theorem maskStep_ok (s : State) {D : BitVec 32} {i n : Nat} {ok : Bool} (h6 : s.gpr .r6 = D + BitVec.ofNat 32 i)
    (h5 : s.gpr .r5 = BitVec.ofNat 32 (n - i)) (h1 : s.gpr .r1 = 0 - (if ok then 1 else 0))
    (r : InRegions (s.rd ++ s.wr) (State.addr (D + BitVec.ofNat 32 i)) 1)
    (w : InRegions s.wr (State.addr (D + BitVec.ofNat 32 i)) 1) :
    ∃ s', runBlock isa [.ldrb .r12 .r6 0, .dp .and .r12 .r12 (.reg .r1), .strb .r12 .r6 0, addI .r6 .r6 1,
        .subs .r5 .r5 (imm 1)] s = some s' ∧
      s'.mem = s.mem.writeW (State.addr (D + BitVec.ofNat 32 i))
        ((if ok then s.mem (State.addr (D + BitVec.ofNat 32 i)) else 0 : Byte)) ∧
      s'.gpr .r6 = D + BitVec.ofNat 32 (i + 1) ∧ s'.gpr .r5 = BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 ∧
      s'.z = (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .r5 → r ≠ .r6 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨_, by arun [h6, h5, add_ofNat_zero, r, w], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_subFlags, mem_store, gpr_setReg, gpr_store, ite_true, ite_false, reduceCtorEq, h1,
      mask_byte]
  · simp [gpr_setReg, h6, add32_ofNat_assoc]
  · simp [gpr_setReg, h5]
  · simp [z_setReg, h5]
  · intro r a b d; simp [gpr_setReg, a, b, d]
  all_goals rfl

omit L in
/-- `maskData`: every byte of the data (`n` bytes at `D`, in `r6` and `r5`)
ANDed with `0 − ok`, for `ok ∈ {0, 1}` in `r0`: kept if `ok = 1`, zeroed if
`ok = 0`. -/
theorem maskData_ok {s : State} (he : Env c w sp R s) {D : BitVec 32} {n : Nat} (hD : Dat c w sp s D n)
    (hn32 : n < 2 ^ 32) (h6 : s.gpr .r6 = D) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) {ok : Bool}
    (h0 : s.gpr .r0 = if ok then 1 else 0) :
    WP isa maskData s fun s' => Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r1 → r ≠ .r5 → r ≠ .r6 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.mem = writeBytes s.mem (State.addr D) (if ok then bytesAt s.mem (State.addr D) n else Spec.Ccm.zeros n) := by
  have hn := hD.buf.fit
  obtain ⟨s₁, run₁, h1₁, hz₁, g₁, k₁⟩ : ∃ s₁, runBlock isa [.mov .r1 (imm 0), .dp .sub .r1 .r1 (.reg .r0),
      .cmp .r5 (imm 0)] s = some s₁ ∧ s₁.gpr .r1 = 0 - (if ok then 1 else 0) ∧
      s₁.z = decide (n = 0) ∧ (∀ r, r ≠ .r1 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
    refine ⟨_, by arun [], ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h0, imm]
    · simp only [z_subFlags, gpr_setReg, gpr_subFlags, ite_true, ite_false, reduceCtorEq, h5, imm]
      rw [z_cmp hn32 (by decide)]
    · intro r a; simp [gpr_setReg, a]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₁ _ (by decide)) k₁.sp k₁.rd k₁.wr
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n = 0)) (eval_eq' hz₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hn0 : n = 0 := by simpa using hb
    subst hn0
    refine ⟨he₁, k₁.rd, k₁.wr, fun r a _ _ _ => g₁ r a, ?_⟩
    rw [k₁.mem]; cases ok <;> simp [bytesAt, Spec.Ccm.zeros, writeBytes_nil]
  have hn0 : 0 < n := by have : n ≠ 0 := by simpa using hb
                         omega
  refine WP.loop (M := isa) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = n - j ∧ j < n ∧ t.gpr .r6 = D + BitVec.ofNat 32 j ∧
      t.gpr .r5 = BitVec.ofNat 32 (n - j) ∧
      t.mem = writeBytes s.mem (State.addr D) (if ok then bytesAt s.mem (State.addr D) j else Spec.Ccm.zeros j) ∧
      (∀ r, r ≠ .r5 → r ≠ .r6 → r ≠ .r12 → t.gpr r = s₁.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp) ?_
    (n - 0) _
    ⟨0, rfl, hn0, by rw [g₁ _ (by decide), h6, add_ofNat_zero], by rw [g₁ _ (by decide), h5]; rfl,
      by rw [k₁.mem]; cases ok <;> simp [bytesAt, Spec.Ccm.zeros, writeBytes_nil], fun r _ _ _ => rfl, k₁.rd, k₁.wr,
      k₁.sp⟩
  rintro m t ⟨j, rfl, hj, r6, r5, mem, g, rd, wr, sp⟩
  have aD := addr_i hn hj
  obtain ⟨t', run', mem', r6', r5', z', g', rd', wr', sp'⟩ := maskStep_ok t (ok := ok) r6 r5
    (by rw [g _ (by decide) (by decide) (by decide), h1₁])
    (by rw [rd, wr, aD]; exact in_of_covers hD.buf.rd hj (by omega))
    (by rw [wr, aD]; exact in_of_covers hD.wr hj (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have fr : Frame [⟨State.addr D, j⟩] s.mem t.mem := by
    rw [mem]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  have hq : t.mem (State.addr D + BitVec.ofNat 64 j) = s.mem (State.addr D + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Mem.sub_ofNat_toNat (State.addr D) (show j < 2 ^ 64 by omega)] at hcon; omega
  have hmem : t'.mem = writeBytes s.mem (State.addr D)
      (if ok then bytesAt s.mem (State.addr D) (j + 1) else Spec.Ccm.zeros (j + 1)) := by
    rw [mem', aD, hq, mem, mask_succ, writeBytes_snoc _ _ _ _ (by rw [length_mask]; omega), length_mask]
  have hz : t'.z = decide (j + 1 = n) := by rw [z', dec32 hj hn32, z_dec hj hn32]
  have gg : ∀ r, r ≠ .r5 → r ≠ .r6 → r ≠ .r12 → t'.gpr r = s₁.gpr r := fun r a b d => by
    rw [g' r a b d, g r a b d]
  have ev : isa.eval .ne t' = some !decide (j + 1 = n) := eval_ne' hz
  by_cases hjn : j + 1 = n
  · left
    refine ⟨by rw [ev]; simp [hjn], he₁.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact gg _ (by decide) (by decide) (by decide))
      (by rw [sp', sp, ← k₁.sp]) (by rw [rd', rd, k₁.rd]) (by rw [wr', wr, k₁.wr]), by rw [rd', rd],
      by rw [wr', wr], fun r a b d e => by rw [gg r b d e, g₁ r a], by rw [hmem, hjn]⟩
  · right
    refine ⟨by rw [ev]; simp [hjn], n - (j + 1), by omega, j + 1, rfl, by omega, r6',
      by rw [r5', dec32 hj hn32], hmem, gg, by rw [rd', rd], by rw [wr', wr], by rw [sp', sp]⟩

/-- Decryption before the comparison: the received IV at `W` as it was, the
plaintext `p` at `D` and S2V's result for it at `W + 112`, the saved
registers and the data's address and length where they were. -/
structure OMid (c w sp a D : BitVec 32) (R N n : Nat) (s s' : State) : Prop where
  env : Env c w sp R s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sv : SavedAt s'.mem w s
  a0 : s'.mem.readW (State.addr sp) 32 = D
  a1 : s'.mem.readW (State.addr sp + BitVec.ofNat 64 4) 32 = BitVec.ofNat 32 n
  iv : bytesAt s'.mem (State.addr w + BitVec.ofNat 64 0) 16 = bytesAt s.mem (State.addr w) 16
  pt : bytesAt s'.mem (State.addr D) n = Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem (State.addr c) R)
    (Spec.Siv.counter (bytesAt s.mem (State.addr w) 16)) (bytesAt s.mem (State.addr D) n)
  tag : bytesAt s'.mem (State.addr w + BitVec.ofNat 64 tOff) 16 =
    Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem (State.addr c) R)
      (Spec.Siv.s2vAcc (Spec.Siv.ctxMac s.mem (State.addr c) R) (Spec.Siv.components 32 s.mem (State.addr a) N))
      (bytesAt s'.mem (State.addr D) n)

/-- S2V of the associated data, CTR from the received IV and S2V's end with
the plaintext. -/
theorem front_ok {a D : BitVec 32} {N n : Nat} {s : State} (h : EPre c w sp a D R N n s) {rest : Prog isa}
    {Q : State → Prop} (k : ∀ s', OMid c w sp a D R N n s s' → WP isa rest s' Q) :
    WP isa (.seq encS2v (.seq (ctr 0) (.seq (.block [.ldrSp .r6 0, .ldrSp .r5 4]) (.seq (finish tOff) rest)))) s Q := by
  have hR := h.rounds
  have hRb := rounds_le hR
  have ww := L.ww
  refine WP.seq (WP.mono (s2v_ok L h) fun s₁ ⟨mₛ, O⟩ => ?_)
  have hD₁ : Dat c w sp s₁ D n := h.data.of_eq O.rd O.wr
  have f₀₁ : Frame (savedR w :: wR w sp) s.mem s₁.mem :=
    (O.fs.mono (by simp)).trans (O.frame.mono fun r hr => List.mem_cons_of_mem _ hr)
  have dA : ∀ r ∈ savedR w :: wR w sp, (⟨State.addr sp, 12⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact Offset.base_disjoint_below (State.addr sp) (n := 16) (k := 12) (by decide)
  have dD : ∀ r ∈ savedR w :: wR w sp, (⟨State.addr D, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.data.buf.w.sub_right (Lay.wSub (by decide))
    · exact h.data.buf.w.sub_right (Lay.wSub (by decide))
    · exact h.data.buf.w.sub_right (Lay.wSub (by decide))
    · exact h.data.buf.stk.symm
  have dc : ∀ r ∈ savedR w :: wR w sp, (⟨State.addr c, 512⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.c0_w' (by decide) (by decide)
    · exact L.c0_w' (by decide) (by decide)
    · exact L.c0_w' (by decide) (by decide)
    · exact L.stk_c.symm
  have dW : ∀ r ∈ savedR w :: wR w sp, (⟨State.addr w + BitVec.ofNat 64 0, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm
  have hm0 : s₁.mem.readW (State.addr sp) 32 = D := by
    rw [f₀₁.readW (r := ⟨State.addr sp, 4⟩) (Region.contains_self _ _)
      (fun r hr => (dA r hr).sub_left (Region.sub_prefix (by decide))) (by decide), h.a0]
  have hm1 : s₁.mem.readW (State.addr sp + BitVec.ofNat 64 4) 32 = BitVec.ofNat 32 n := by
    rw [f₀₁.readW (r := ⟨State.addr sp + BitVec.ofNat 64 4, 4⟩) (Region.contains_self _ _)
      (fun r hr => (dA r hr).sub_left (Offset.sub_base _ (by decide))) (by decide), h.a1]
  refine WP.seq (WP.mono (ctr_ok L O.env hR hD₁ h.n32 h.afit (by rw [O.rd, O.wr]; exact h.args) h.args_w
    hm0 hm1) fun s₂ ⟨he₂, rd₂, wr₂, g₂, h6₂, h5₂, f₂, d₂⟩ => ?_)
  -- What CTR writes.
  have eA : ∀ r ∈ ctrR w sp D n, (⟨State.addr sp, 12⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact Offset.base_disjoint_below (State.addr sp) (n := 16) (k := 12) (by decide)
    · exact h.args_d
  have eS : ∀ r ∈ ctrR w sp D n, (savedR w).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm
    · exact (h.data.buf.w.sub_right (Lay.wSub (by decide))).symm
  have eW : ∀ {d : Nat}, d + 16 ≤ 80 ∨ 2432 ≤ d → d + 16 ≤ 2576 →
      ∀ r ∈ ctrR w sp D n, (⟨State.addr w + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := by
    intro d hd hd' r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.w_w (by simp only [ksOff]; omega) hd' (by decide)
    · exact L.w_w (by omega) hd' (by decide)
    · exact (L.stk_w' hd').symm
    · exact (h.data.buf.w.sub_right (Lay.wSub hd')).symm
  have ec : ∀ r ∈ ctrR w sp D n, (⟨State.addr c, 512⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.c0_w' (by decide) (by decide)
    · exact L.c0_w' (by decide) (by decide)
    · exact L.stk_c.symm
    · exact h.data.c
  have hm0₂ : s₂.mem.readW (State.addr sp + BitVec.ofNat 64 0) 32 = D := by
    rw [BitVec.add_zero, f₂.readW (r := ⟨State.addr sp, 4⟩) (Region.contains_self _ _)
      (fun r hr => (eA r hr).sub_left (Region.sub_prefix (by decide))) (by decide), hm0]
  have hm1₂ : s₂.mem.readW (State.addr sp + BitVec.ofNat 64 4) 32 = BitVec.ofNat 32 n := by
    rw [f₂.readW (r := ⟨State.addr sp + BitVec.ofNat 64 4, 4⟩) (Region.contains_self _ _)
      (fun r hr => (eA r hr).sub_left (Offset.sub_base _ (by decide))) (by decide), hm1]
  have hsp₂ : s₂.sp = sp := he₂.sp
  refine WP.seq ?_
  refine wp_ldrSp (a := State.addr sp + BitVec.ofNat 64 0) (by decide)
    (by rw [hsp₂]; exact addr_add (by have := h.afit; omega))
    (by rw [rd₂, wr₂, O.rd, O.wr]; exact in_off h.args (by decide) (by decide)) fun s₃ u₃ => ?_
  refine wp_ldrSp (a := State.addr sp + BitVec.ofNat 64 4) (by decide)
    (by rw [u₃.sp, hsp₂]; exact addr_add (by have := h.afit; omega))
    (by rw [u₃.rd, u₃.wr, rd₂, wr₂, O.rd, O.wr]; exact in_off h.args (by decide) (by decide)) fun s₄ u₄ => WP.block_nil ?_
  have m₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  have he₄ : Env c w sp R s₄ := he₂.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> rw [u₄.other _ (by decide), u₃.other _ (by decide)])
    (by rw [u₄.sp, u₃.sp]) (by rw [u₄.rd, u₃.rd]) (by rw [u₄.wr, u₃.wr])
  have rd₄ : s₄.rd = s.rd := by rw [u₄.rd, u₃.rd, rd₂, O.rd]
  have wr₄ : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, wr₂, O.wr]
  have hD₄ : Dat c w sp s₄ D n := h.data.of_eq rd₄ wr₄
  have h6₄ : s₄.gpr .r6 = D := by rw [u₄.other _ (by decide), u₃.gpr, hm0₂]
  have h5₄ : s₄.gpr .r5 = BitVec.ofNat 32 n := by rw [u₄.gpr, u₃.mem, hm1₂]
  refine WP.seq (WP.mono (finish_ok L he₄ hR hD₄.buf h.n32 h6₄ h5₄ (out := tOff) (.inr rfl))
    fun s₅ ⟨he₅, rd₅, wr₅, _, f₅, o₅⟩ => k s₅ ?_)
  have f₅' : Frame (wR w sp) s₄.mem s₅.mem := frame_oR_tOff f₅
  rw [m₄] at f₅' o₅
  -- The values.
  have ciph₁ : Spec.Siv.ctxCiph s₁.mem (State.addr c) R = Spec.Siv.ctxCiph s.mem (State.addr c) R :=
    ctxCiph_frame f₀₁ dc hRb
  have mac₂ : Spec.Siv.ctxMac s₂.mem (State.addr c) R = Spec.Siv.ctxMac s.mem (State.addr c) R := by
    rw [ctxMac_frame f₂ ec hRb, ctxMac_frame f₀₁ dc hRb]
  have iv₁ : bytesAt s₁.mem (State.addr w) 16 = bytesAt s.mem (State.addr w) 16 := by
    have := bytesAt_frame f₀₁ dW (by decide)
    rwa [BitVec.add_zero] at this
  have p₁ : bytesAt s₁.mem (State.addr D) n = bytesAt s.mem (State.addr D) n :=
    bytesAt_frame f₀₁ dD (by have := h.data.buf.lt; omega)
  have p₅ : bytesAt s₅.mem (State.addr D) n = bytesAt s₂.mem (State.addr D) n :=
    bytesAt_frame f₅' (dis_wR h.data.buf.w h.data.buf.stk) (by have := h.data.buf.lt; omega)
  have acc₂ : bytesAt s₂.mem (State.addr w + BitVec.ofNat 64 dOff) 16 = bytesAt s₁.mem (State.addr w + BitVec.ofNat 64 dOff) 16 :=
    bytesAt_frame f₂ (eW (.inr (by decide)) (by decide)) (by decide)
  have dWw : ∀ r ∈ wR w sp, (⟨State.addr w + BitVec.ofNat 64 0, 16⟩ : Region).Disjoint r :=
    fun r hr => dW r (List.mem_cons_of_mem _ hr)
  have dAw : ∀ r ∈ wR w sp, (⟨State.addr sp, 12⟩ : Region).Disjoint r :=
    fun r hr => dA r (List.mem_cons_of_mem _ hr)
  refine ⟨he₅, by rw [rd₅, rd₄], by rw [wr₅, wr₄], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((O.sv.frame O.frame (saved_wR L)).frame f₂ eS).frame f₅' (saved_wR L)
  · rw [f₅'.readW (r := ⟨State.addr sp, 4⟩) (Region.contains_self _ _)
      (fun r hr => (dAw r hr).sub_left (Region.sub_prefix (by decide))) (by decide), ← hm0₂, BitVec.add_zero]
  · rw [f₅'.readW (r := ⟨State.addr sp + BitVec.ofNat 64 4, 4⟩) (Region.contains_self _ _)
      (fun r hr => (dAw r hr).sub_left (Offset.sub_base _ (by decide))) (by decide), hm1₂]
  · rw [bytesAt_frame f₅' dWw (by decide), bytesAt_frame f₂ (eW (.inl (by decide)) (by decide)) (by decide),
      BitVec.add_zero, iv₁]
  · rw [p₅, d₂, ciph₁, iv₁, p₁]
  · rw [o₅, mac₂, acc₂, O.acc, p₅]

/-- `vg_aes_siv_decrypt`: 1 and the plaintext in place if the received IV at
`W` is S2V's for it, and 0 and zeros if not. -/
theorem decrypt_wp {a D : BitVec 32} {N n : Nat} {s : State} (h : EPre c w sp a D R N n s) :
    WP isa decrypt s fun s' => abiPreserved s s' ∧
      match Spec.Siv.decryptWith (Spec.Siv.ctxMac s.mem (State.addr c) R) (Spec.Siv.ctxCiph s.mem (State.addr c) R)
          (Spec.Siv.components 32 s.mem (State.addr a) N) (bytesAt s.mem (State.addr w) 16)
          (bytesAt s.mem (State.addr D) n) with
      | some pt => s'.gpr .r0 = 1 ∧ bytesAt s'.mem (State.addr D) n = pt
      | none => s'.gpr .r0 = 0 ∧ bytesAt s'.mem (State.addr D) n = Spec.Siv.zeros n := by
  have ww := L.ww
  refine front_ok L h fun s₅ M => ?_
  obtain ⟨s₆, run₆, h0₆, g₆, k₆⟩ := compare_ok L M.env
  have hsp₅ : s₅.sp = sp := M.env.sp
  refine WP.seq (WP.block_append (WP.of_runBlock ⟨s₆, run₆, ?_⟩))
  refine wp_ldrSp (a := State.addr sp + BitVec.ofNat 64 0) (by decide)
    (by rw [k₆.sp, hsp₅]; exact addr_add (by have := h.afit; omega))
    (by rw [k₆.rd, k₆.wr, M.rd, M.wr]; exact in_off h.args (by decide) (by decide)) fun s₇ u₇ => ?_
  refine wp_ldrSp (a := State.addr sp + BitVec.ofNat 64 4) (by decide)
    (by rw [u₇.sp, k₆.sp, hsp₅]; exact addr_add (by have := h.afit; omega))
    (by rw [u₇.rd, u₇.wr, k₆.rd, k₆.wr, M.rd, M.wr]; exact in_off h.args (by decide) (by decide))
    fun s₈ u₈ => WP.block_nil ?_
  have m₈ : s₈.mem = s₅.mem := by rw [u₈.mem, u₇.mem, k₆.mem]
  have he₈ : Env c w sp R s₈ := M.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        rw [u₈.other _ (by decide), u₇.other _ (by decide), g₆ _ (by decide) (by decide) (by decide)])
    (by rw [u₈.sp, u₇.sp, k₆.sp]) (by rw [u₈.rd, u₇.rd, k₆.rd]) (by rw [u₈.wr, u₇.wr, k₆.wr])
  have rd₈ : s₈.rd = s.rd := by rw [u₈.rd, u₇.rd, k₆.rd, M.rd]
  have wr₈ : s₈.wr = s.wr := by rw [u₈.wr, u₇.wr, k₆.wr, M.wr]
  have hD₈ : Dat c w sp s₈ D n := h.data.of_eq rd₈ wr₈
  have h6₈ : s₈.gpr .r6 = D := by
    rw [u₈.other _ (by decide), u₇.gpr, k₆.mem, BitVec.add_zero, M.a0]
  have h5₈ : s₈.gpr .r5 = BitVec.ofNat 32 n := by rw [u₈.gpr, u₇.mem, k₆.mem, M.a1]
  have h0₈ : s₈.gpr .r0 = if (decide (bytesAt s₅.mem (State.addr w + BitVec.ofNat 64 0) 16 =
      bytesAt s₅.mem (State.addr w + BitVec.ofNat 64 tOff) 16)) then 1 else 0 := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), h0₆]; simp only [decide_eq_true_eq]
  obtain ⟨ok, hok⟩ : ∃ ok, ok = decide (bytesAt s₅.mem (State.addr w + BitVec.ofNat 64 0) 16 =
      bytesAt s₅.mem (State.addr w + BitVec.ofNat 64 tOff) 16) := ⟨_, rfl⟩
  rw [← hok] at h0₈
  refine WP.seq (WP.mono (maskData_ok he₈ hD₈ h.n32 h6₈ h5₈ h0₈) fun s₉ ⟨he₉, rd₉, wr₉, g₉, m₉⟩ => ?_)
  have hlen := length_mask s₈.mem (State.addr D) ok n
  have sv₉ : SavedAt s₉.mem w s := by
    rw [m₉]
    refine (m₈ ▸ M.sv).frame (writeBytes_frame _ _ _ (R := ⟨State.addr D, n⟩)
      (by rw [hlen]; exact Region.contains_self _ _)) fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.data.buf.w.sub_right (Lay.wSub (by decide))).symm
  refine WP.mono (restore_ok (s₀ := s) he₉.r11 (by omega)
    (by rw [rd₉, wr₉, rd₈, wr₈]; exact covers_left (covers_prefix h.perm.w (by decide))) sv₉
    (by rw [he₉.sp, h.hsp])) fun s₁₀ ⟨ab, m₁₀, r0₁₀, _, _⟩ => ⟨ab, ?_⟩
  have hr0 : s₁₀.gpr .r0 = if ok then 1 else 0 := by
    rw [r0₁₀, g₉ _ (by decide) (by decide) (by decide) (by decide), h0₈]
  have hb : bytesAt s₁₀.mem (State.addr D) n =
      if ok then bytesAt s₅.mem (State.addr D) n else Spec.Ccm.zeros n := by
    have e := bytesAt_writeBytes_self s₈.mem (State.addr D)
      (if ok then bytesAt s₈.mem (State.addr D) n else Spec.Ccm.zeros n) (by rw [hlen]; have := h.n32; omega)
    rw [hlen] at e
    rw [m₁₀, m₉, e, m₈]
  rw [M.iv, M.tag, M.pt] at hok
  rw [Spec.Siv.decryptWith_eq, Spec.Siv.openWith]
  by_cases e : Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem (State.addr c) R)
      (Spec.Siv.s2vAcc (Spec.Siv.ctxMac s.mem (State.addr c) R) (Spec.Siv.components 32 s.mem (State.addr a) N))
      (Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem (State.addr c) R) (Spec.Siv.counter (bytesAt s.mem (State.addr w) 16))
        (bytesAt s.mem (State.addr D) n)) = bytesAt s.mem (State.addr w) 16
  · have : ok = true := by rw [hok, e]; simp
    simp only [e, ite_true]
    rw [hr0, hb, this, M.pt]; exact ⟨rfl, rfl⟩
  · have : ok = false := by rw [hok]; simpa using Ne.symm e
    simp only [e, ite_false]
    rw [hr0, hb, this]; exact ⟨rfl, rfl⟩

end

end VG.Proof.AesSiv.Arm

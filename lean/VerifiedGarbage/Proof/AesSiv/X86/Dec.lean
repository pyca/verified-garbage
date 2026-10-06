import VerifiedGarbage.Proof.AesSiv.X86.Enc

/-!
# AES-SIV on x86: `vg_aes_siv_decrypt`

Untrusted: everything here is checked by Lean. `decrypt` copies the received
IV from `siv` to `W` (`sivIn_ok`) after S2V of the associated data, decrypts
the data with CTR from it, finishes S2V with the plaintext into `W + 112`,
compares the IVs without a branch and masks the data with the result
(`decrypt_wp`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesSiv.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot restore)
open VG.Proof.AesGcm.X86 (exit_ok ret_below covers_left readW_writeW_off argA argA_sub argA_contains)
open VG.Proof.AesGcm.X86 (w64 slotv bytes16_eq xor4_eq_zero w64_add in_of_covers succ_ofNat32 add_zero32 pred_count
  pred_beq bytesAt_succ length_bytesAt and_self_beq32 CT)

/-- `cmp eax, 1` and `adc` of 0 after the OR of the XORs of two blocks' words:
1 if they are equal, else 0. -/
theorem cmpAdc (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : BitVec 32) :
    0#32 + 0#32 + BitVec.setWidth 32 (BitVec.ofBool (decide
      ((a₀ ^^^ b₀ ||| a₁ ^^^ b₁ ||| a₂ ^^^ b₂ ||| a₃ ^^^ b₃).toNat < (1#32).toNat))) =
      BitVec.ofNat 32 (if a₀ = b₀ ∧ a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃ then 1 else 0) := by
  have e := xor4_eq_zero a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃
  by_cases h : a₀ = b₀ ∧ a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    simp only [and_self, ↓reduceIte, BitVec.xor_self, BitVec.or_self]
    decide
  · have h0 : (a₀ ^^^ b₀) ||| (a₁ ^^^ b₁) ||| (a₂ ^^^ b₂) ||| (a₃ ^^^ b₃) ≠ 0 := fun h' => h (e.mp h')
    have hne : ((a₀ ^^^ b₀) ||| (a₁ ^^^ b₁) ||| (a₂ ^^^ b₂) ||| (a₃ ^^^ b₃)).toNat ≠ 0 := fun h' =>
      h0 (BitVec.eq_of_toNat_eq (by simpa using h'))
    have hlt : ¬ ((a₀ ^^^ b₀) ||| (a₁ ^^^ b₁) ||| (a₂ ^^^ b₂) ||| (a₃ ^^^ b₃)).toNat < (1#32).toNat := by
      rw [BitVec.toNat_ofNat]; omega
    simp only [h, ↓reduceIte, decide_eq_false hlt]
    rfl

/-- Whether the IVs at `W` and `W + 112` are equal, as a word. -/
abbrev okVal (m : Mem) (W : BitVec 32) : BitVec 32 :=
  BitVec.ofNat 32 (if bytesAt m (w64 W) 16 = bytesAt m (w64 W + BitVec.ofNat 64 tOff) 16 then 1 else 0)

theorem compare_ok {C W SP : BitVec 32} (L : Lay C W SP) {s : State} (E : Env C W SP s) :
    ∃ s', runBlock isa compare s = some s' ∧ s'.mem = s.mem.writeW (w64 W + BitVec.ofNat 64 okO) (okVal s.mem W) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [Impl.AesSiv.X86.compare, E.ebp, L.aW, E.perm.wR, E.perm.wW], ?_, fun r h₁ h₂ => ?_, ?_, ?_⟩
  · cmems []
    rw [cmpAdc]
    simp only [okVal, bytes16_eq, BitVec.add_zero, add_ofNat_assoc, Nat.reduceAdd, tOff]
  · cregs []
  all_goals cmems []

/-! ## `mask` -/

theorem mask_byte32 (b : Byte) (c : Bool) :
    ((b.setWidth 32 &&& ((0 : BitVec 32) - (if c then 1 else 0))).setWidth 8) = if c then b else 0 := by
  cases c
  · simp
  · rw [show (if true = true then (1 : BitVec 32) else 0) = 1 from rfl,
      show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes]
    simp

abbrev maskBody : List Instr :=
  [.movzx8 .edx (at_ .edi 0), .alu .and .edx (.reg .ebx), .store8 (at_ .edi 0) .dl, .alu .add .edi (imm 1),
    .alu .sub .ecx (imm 1)]

theorem maskStep_ok (s : State) {P : BitVec 32} {i n : Nat} {c : Bool} (hs : s.gpr .edi = P + BitVec.ofNat 32 i)
    (hc : s.gpr .ecx = BitVec.ofNat 32 (n - i)) (hb : s.gpr .ebx = 0 - (if c then 1 else 0))
    (eP : w64 (P + BitVec.ofNat 32 i) = w64 P + BitVec.ofNat 64 i)
    (r : InRegions (s.rd ++ s.wr) (w64 P + BitVec.ofNat 64 i) 1) (w : InRegions s.wr (w64 P + BitVec.ofNat 64 i) 1) :
    ∃ s', runBlock isa maskBody s = some s' ∧
      s'.mem = s.mem.writeW (w64 P + BitVec.ofNat 64 i) ((if c then s.mem (w64 P + BitVec.ofNat 64 i) else 0 : Byte)) ∧
      s'.gpr .edi = P + BitVec.ofNat 32 (i + 1) ∧ s'.gpr .ecx = BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 ∧
      s'.zf = some (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) ∧
      (∀ r, r ≠ .edx → r ≠ .edi → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [maskBody, add_zero32, hs, eP, r, w], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cmems [hb, mask_byte32]
  · cregs [hs, succ_ofNat32]
  · cregs [hc]
  · cmems [hc]
  · intro r h₁ h₂ h₃; cregs [h₁, h₂, h₃]
  all_goals cmems []

theorem length_mask (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P j else Spec.Siv.zeros j).length = j := by
  cases c <;> simp [Spec.Siv.zeros, length_bytesAt]

theorem mask_succ (m : Mem) (P : Addr) (c : Bool) (j : Nat) :
    (if c then bytesAt m P (j + 1) else Spec.Siv.zeros (j + 1)) =
      (if c then bytesAt m P j else Spec.Siv.zeros j) ++ [if c then m (P + BitVec.ofNat 64 j) else 0] := by
  cases c <;> simp [Spec.Siv.zeros, bytesAt_succ, List.replicate_succ']

/-- Every byte of the data ANDed with `0 − ok`, for `ok` (at `W + okO`) 1 or 0. -/
theorem mask_ok {C W SP : BitVec 32} {s : State} (L : Lay C W SP) (E : Env C W SP s) {D : BitVec 32} {n : Nat}
    (hDp : slotv s.mem W dataO = D) (hlen : slotv s.mem W lenO = BitVec.ofNat 32 n) (hn32 : n < 2 ^ 32)
    (hD : Buf W SP s D n) (hDw : Covers [⟨w64 D, n⟩] s.wr) {c : Bool}
    (hok : slotv s.mem W okO = if c then 1 else 0) :
    WP isa mask s fun s' => Env C W SP s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = writeBytes s.mem (w64 D) (if c then bytesAt s.mem (w64 D) n else Spec.Siv.zeros n) := by
  obtain ⟨s₁, run₁, m₁, cx₁, zf₁, bp₁, sp₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa
      [.mov .ecx (slot lenO), .alu .test .ecx (.reg .ecx)] s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.gpr .ecx = BitVec.ofNat 32 n ∧ s₁.zf = some (decide (n = 0)) ∧ s₁.gpr .ebp = W ∧ s₁.gpr .esp = SP ∧
      s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hlen], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · cregs [hlen]
    · cmems [hlen]; rw [and_self_beq32 hn32]
    · cregs [E.ebp]
    · cregs [E.esp]
    all_goals cmems []
  have E₁ : Env C W SP s₁ := E.keep (by rw [bp₁, E.ebp]) (by rw [sp₁, E.esp]) rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.ite (decide (n = 0)) (eval_e zf₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hn0 : n = 0 := of_decide_eq_true hb
    subst hn0
    refine ⟨E₁, rd₁, wr₁, ?_⟩
    rw [m₁]
    cases c <;> simp [Spec.Aes.bytesAt, Spec.Siv.zeros, writeBytes_nil]
  have hn0 : 0 < n := Nat.pos_of_ne_zero (of_decide_eq_false hb)
  obtain ⟨s₂, run₂, m₂, bx₂, di₂, cx₂, bp₂, sp₂, rd₂, wr₂⟩ : ∃ s₂, runBlock isa
      [.mov .ebx (imm 0), .alu .sub .ebx (slot okO), .mov .edi (slot dataO)] s₁ = some s₂ ∧ s₂.mem = s.mem ∧
      s₂.gpr .ebx = 0 - (if c then 1 else 0) ∧ s₂.gpr .edi = D ∧ s₂.gpr .ecx = BitVec.ofNat 32 n ∧
      s₂.gpr .ebp = W ∧ s₂.gpr .esp = SP ∧ s₂.rd = s.rd ∧ s₂.wr = s.wr := by
    have hok₁ : slotv s₁.mem W okO = if c then 1 else 0 := by rw [m₁]; exact hok
    have hd₁ : slotv s₁.mem W dataO = D := by rw [m₁]; exact hDp
    refine ⟨_, by crun [bp₁, L.aW, E₁.perm.wR, hok₁, hd₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · cmems [m₁]
    · cregs [hok₁]; rfl
    · cregs [hd₁]
    · cregs [cx₁]
    · cregs [bp₁]
    · cregs [sp₁]
    · cmems [rd₁]
    · cmems [wr₁]
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have hfD := hD.wrap
  refine WP.loop (M := isa) (body := .block maskBody) (c := .ne)
    (fun (k : Nat) (t : State) => ∃ j, k = n - j ∧ j < n ∧ t.gpr .edi = D + BitVec.ofNat 32 j ∧
      t.gpr .ecx = BitVec.ofNat 32 (n - j) ∧
      t.mem = writeBytes s.mem (w64 D) (if c then bytesAt s.mem (w64 D) j else Spec.Siv.zeros j) ∧
      (∀ r, r ≠ .edx → r ≠ .edi → r ≠ .ecx → t.gpr r = s₂.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (n - 0) _
    ⟨0, rfl, hn0, by rw [di₂, add_zero32], by rw [cx₂, Nat.sub_zero], by
      rw [m₂]; cases c <;> simp [Spec.Aes.bytesAt, Spec.Siv.zeros, writeBytes_nil], fun r _ _ _ => rfl, rd₂, wr₂⟩
  rintro k t ⟨j, rfl, hj, di, cx, mem, g, rd, wr⟩
  obtain ⟨t', run', mem', di', cx', zf', g', rd', wr'⟩ := maskStep_ok t (P := D) (i := j) (n := n) (c := c) di cx
    (by rw [g _ (by decide) (by decide) (by decide), bx₂]) (w64_add (by omega))
    (by rw [rd, wr]; exact in_of_covers hD.rd hj (by omega))
    (by rw [wr]; exact in_of_covers hDw hj (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have fr : Frame [⟨w64 D, j⟩] s.mem t.mem := by
    rw [mem]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  have hq : t.mem (w64 D + BitVec.ofNat 64 j) = s.mem (w64 D + BitVec.ofNat 64 j) :=
    fr _ fun r hr hcon => by
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains, Mem.sub_ofNat_toNat (w64 D) (show j < 2 ^ 64 by omega)] at hcon; omega
  have hmem : t'.mem = writeBytes s.mem (w64 D) (if c then bytesAt s.mem (w64 D) (j + 1) else Spec.Siv.zeros (j + 1)) := by
    rw [mem', hq, mem, mask_succ, writeBytes_snoc _ _ _ _ (by rw [length_mask]; omega), length_mask]
  have hz : t'.zf = some (decide (j + 1 = n)) := by rw [zf', pred_beq hj hn32]
  have gg : ∀ r, r ≠ .edx → r ≠ .edi → r ≠ .ecx → t'.gpr r = s₂.gpr r := fun r h₁ h₂ h₃ => by
    rw [g' r h₁ h₂ h₃, g r h₁ h₂ h₃]
  have E' : Env C W SP t' := ⟨by rw [gg _ (by decide) (by decide) (by decide), bp₂],
    by rw [gg _ (by decide) (by decide) (by decide), sp₂], E.perm.of_eq (by rw [rd', rd]) (by rw [wr', wr])⟩
  by_cases he : j + 1 = n
  · left
    exact ⟨by simp [eval, hz, he], E', by rw [rd', rd], by rw [wr', wr], by rw [hmem, he]⟩
  · right
    refine ⟨by simp [eval, hz, he], n - (j + 1), by omega, j + 1, rfl, by omega, di',
      by rw [cx', pred_count hj hn32], hmem, gg, by rw [rd', rd], by rw [wr', wr]⟩


/-! ## `vg_aes_siv_decrypt` -/

theorem okVal_eq (m : Mem) (W : BitVec 32) :
    okVal m W = if decide (bytesAt m (w64 W) 16 = bytesAt m (w64 W + BitVec.ofNat 64 tOff) 16) then 1 else 0 := by
  unfold okVal; split <;> simp_all

theorem retEax_ok {C W SP : BitVec 32} (L : Lay C W SP) {s : State} (E : Env C W SP s) :
    ∃ s', runBlock isa [.mov .eax (slot okO)] s = some s' ∧ s'.gpr .eax = slotv s.mem W okO ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR], ?_, fun r h₁ => ?_, ?_, ?_, ?_⟩
  · cregs []
  · cregs []
  all_goals cmems []

/-- `sivIn`: the IV at `T`, the stack argument 6, copied to `W`. -/
theorem sivIn_ok {C W SP : BitVec 32} (L : Lay C W SP) {s : State} (E : Env C W SP s) {T : BitVec 32}
    (hin : InRegions (s.rd ++ s.wr) (argA SP 6) 4) (hv : s.mem.readW (argA SP 6) 32 = T)
    (tR : Covers [⟨w64 T, 16⟩] (s.rd ++ s.wr)) (fT : T.toNat + 16 ≤ 2 ^ 32) :
    WP isa sivIn s fun s' => bytesAt s'.mem (w64 W + BitVec.ofNat 64 0) 16 = bytesAt s.mem (w64 T + BitVec.ofNat 64 0) 16 ∧
      Frame [⟨w64 W + BitVec.ofNat 64 0, 16⟩] s.mem s'.mem ∧ s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have aT : ∀ {k}, k < 16 → w64 (T + BitVec.ofNat 32 k) = w64 T + BitVec.ofNat 64 k := fun hk => w64_add (by omega)
  have tIn : ∀ {k}, k + 4 ≤ 16 → InRegions (s.rd ++ s.wr) (w64 T + BitVec.ofNat 64 k) 4 := fun hk =>
    Proof.AesGcm.X86.in_off tR hk (by decide)
  have hs := Proof.AesGcm.X86.store4_eq s.mem W 0
  simp only [Nat.reduceAdd] at hs
  refine WP.seq (WP.of_runBlock ⟨_, by crun [E.esp, hin, hv], ?_⟩)
  refine WP.of_runBlock ⟨_, by crun [aT, tIn, E.ebp, L.aW, E.perm.wW], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cmems [hs]
    rw [Cmac.bytesAt_store4, Cmac.bytesAt_split4, Cmac.le4_readW, Cmac.le4_readW, Cmac.le4_readW, Cmac.le4_readW,
      add_ofNat_assoc, add_ofNat_assoc, add_ofNat_assoc]
  · cmems [hs]
    exact Cmac.frame_store4 _ _ _ _ _
  · cregs [E.ebp]
  · cregs [E.esp]
  · cmems []
  · cmems []

/-- What a piece writes in `wR` or the data misses the IV at `W`. -/
theorem w16_dis {C W SP D : BitVec 32} {n : Nat} (L : Lay C W SP)
    (hD : (⟨w64 W, 16⟩ : Region).Disjoint ⟨w64 D, n⟩) {rs : List Region}
    (hs : ∀ r ∈ rs, (∃ r' ∈ wR W SP, Region.Sub r r') ∨ ∃ r' ∈ [(⟨w64 D, n⟩ : Region)], Region.Sub r r') :
    ∀ r ∈ rs, (⟨w64 W, 16⟩ : Region).Disjoint r := by
  intro r hr
  rcases hs r hr with ⟨r', hr', hsub⟩ | ⟨r', hr', hsub⟩
  · refine Region.Disjoint.sub_right ?_ hsub
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa using Lay.w_w (W := W) (a := 0) (n := 16) (d := 16) (k := 112) (.inl (by decide)) (by decide) (by decide)
    · simpa using Lay.w_w (W := W) (a := 0) (n := 16) (d := 144) (k := 32) (.inl (by decide)) (by decide) (by decide)
    · simpa using Lay.w_w (W := W) (a := 0) (n := 16) (d := 184) (k := 8) (.inl (by decide)) (by decide) (by decide)
    · simpa using Lay.w_w (W := W) (a := 0) (n := 16) (d := 200) (k := 56) (.inl (by decide)) (by decide) (by decide)
    · simpa using Lay.w_w (W := W) (a := 0) (n := 16) (d := 256) (k := 2320) (.inl (by decide)) (by decide)
        (by decide)
    · exact (L.stk_w.sub_right (Region.sub_prefix (by decide))).symm
  · simp only [List.mem_singleton] at hr'; subst hr'
    exact hD.sub_right hsub

/-- `vg_aes_siv_decrypt`: the plaintext and 1 if the IV at `T` is right,
zeros and 0 if not. -/
theorem decrypt_wp (v : Ctr32Impl) {C W SP A D T : BitVec 32} {R N n : Nat} {s : State}
    (h : EPre C W SP A D T R N n s) :
    WP isa (decrypt v.callee v.suffix) s fun s' => abiPreserved s s' ∧
      match Spec.Siv.decryptWith (Spec.Siv.ctxMac s.mem (w64 C) R) (Spec.Siv.ctxCiph s.mem (w64 C) R)
          (Spec.Siv.components 32 s.mem (w64 A) N) (bytesAt s.mem (w64 T) 16) (bytesAt s.mem (w64 D) n) with
      | some pt => s'.gpr .eax = 1 ∧ bytesAt s'.mem (w64 D) n = pt
      | none => s'.gpr .eax = 0 ∧ bytesAt s'.mem (w64 D) n = Spec.Siv.zeros n := by
  have L := h.ads.lay
  have hR := h.ads.rounds
  have hRb := rounds_le hR
  have hDw : (⟨w64 D, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ :=
    h.data.buf.w.sub_right (Lay.wSub (by decide))
  have hW16 : (⟨w64 W, 16⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ := by
    simpa using Lay.w_w (W := W) (a := 0) (n := 16) (.inl (by decide)) (by decide) (by decide)
  have dDW : (⟨w64 W, 16⟩ : Region).Disjoint ⟨w64 D, n⟩ :=
    (h.data.buf.w.sub_right (Region.sub_prefix (by decide))).symm
  have hext1 : ∀ r ∈ [(⟨w64 W, 16⟩ : Region)], r.Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hW16
  have hext2 : ∀ r ∈ [(⟨w64 W, 16⟩ : Region), ⟨w64 D, n⟩], r.Disjoint ⟨w64 W + BitVec.ofNat 64 128, 2448⟩ :=
    fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hW16
      · exact hDw
  refine WP.seq (WP.mono (encS2v_ok v h) fun s₀ O => ?_)
  have K₀ := O.kept
  -- The received IV copied from `siv`.
  have hs6 := argA_sub (SP := SP) (n := 8) (i := 6) (by decide) h.fa
  have v6 : s₀.mem.readW (argA SP 6) 32 = T := by
    rw [K₀.big.readW (r := ⟨argA SP 6, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl
      · exact (h.aw.sub_left hs6).sub_right (Lay.wSub (by decide))
      · exact h.as.symm.sub_left hs6) (by decide), ← h.a6, arg, argAddr, h.sp]
  have i6 : InRegions (s₀.rd ++ s₀.wr) (argA SP 6) 4 := by
    rw [K₀.rd, K₀.wr]; exact h.rA _ _ ⟨_, List.mem_singleton_self _, argA_contains (by decide) h.fa⟩
  refine WP.seq (WP.mono (sivIn_ok L K₀.env i6 v6 (by rw [K₀.rd, K₀.wr]; exact h.t_rd) h.tfit)
    fun s₁ ⟨iv₁, fIn, bp₁, sp₁, rd₁, wr₁⟩ => ?_)
  have K₁ : Kept s C W SP R D n [⟨w64 W, 16⟩] s₁ := (K₀.widen _).step L hext1
    ⟨bp₁, sp₁, K₀.env.perm.of_eq rd₁ wr₁⟩ rd₁ wr₁ fIn (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact .inr ⟨⟨w64 W, 16⟩, by simp, Offset.sub_base (k := 16) _ (by decide)⟩)
  have ivT : bytesAt s₁.mem (w64 W) 16 = bytesAt s.mem (w64 T) 16 := by
    rw [BitVec.add_zero, BitVec.add_zero] at iv₁
    rw [iv₁]
    exact K₀.bytes h.t_w h.t_stk (by simp) (by decide)
  -- CTR from the IV.
  obtain ⟨s₂, run₂, m₂, bp₂, sp₂, rd₂, wr₂⟩ := counter_ok L K₁.env
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  have E₂ : Env C W SP s₂ := ⟨bp₂, sp₂, K₁.env.perm.of_eq rd₂ wr₂⟩
  have f₂ : Frame [⟨w64 W + BitVec.ofNat 64 cbOff, 16⟩] s₁.mem s₂.mem := by
    rw [m₂]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have K₂ : Kept s C W SP R D n [⟨w64 W, 16⟩] s₂ := K₁.step L hext1 E₂ rd₂ wr₂ f₂ counter_wR
  have hq : bytesAt s₂.mem (w64 W + BitVec.ofNat 64 cbOff) 16 = Spec.Siv.counter (bytesAt s₁.mem (w64 W) 16) := by
    rw [m₂]; exact counter_bytes _ _
  refine WP.seq (WP.mono (ctr_ok v L hR E₂ (h.data.of_eq K₂.rd K₂.wr) h.n32 K₂.slots.ctx K₂.slots.rounds
    K₂.slots.data K₂.slots.len hq (counter_low _)) fun s₃ ⟨E₃, rd₃, wr₃, f₃, d₃⟩ => ?_)
  have K₃ : Kept s C W SP R D n [⟨w64 W, 16⟩, ⟨w64 D, n⟩] s₃ :=
    (K₂.widen _).step L hext2 E₃ rd₃ wr₃ f₃ (ctrR_wR (by simp))
  -- S2V's end with the plaintext into `W + 112`.
  obtain ⟨s₄, run₄, P₄, K₄, f₄⟩ := dataStr_pre L K₃ hext2 (h.data.buf.of_eq K₃.rd K₃.wr) h.n32
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  refine WP.seq (WP.mono (finish_ok v L hR P₄ (out := tOff) (.inr rfl)) fun s₅ F => ?_)
  have K₅ : Kept s C W SP R D n [⟨w64 W, 16⟩, ⟨w64 D, n⟩] s₅ :=
    K₄.step L hext2 F.env F.rd F.wr F.frame (finR_wR (.inr rfl))
  -- The comparison.
  obtain ⟨s₆, run₆, m₆, g₆, rd₆, wr₆⟩ := compare_ok L F.env
  refine WP.seq (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
  have E₆ : Env C W SP s₆ := F.env.keep (g₆ _ (by decide) (by decide)) (g₆ _ (by decide) (by decide)) rd₆ wr₆
  have f₆ : Frame [⟨w64 W + BitVec.ofNat 64 okO, 4⟩] s₅.mem s₆.mem := by
    rw [m₆]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have K₆ : Kept s C W SP R D n [⟨w64 W, 16⟩, ⟨w64 D, n⟩] s₆ := K₅.step L hext2 E₆ rd₆ wr₆ f₆ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact .inl ⟨wS W, by simp, sub_wS (by decide) (by decide)⟩
  have hok : slotv s₆.mem W okO = okVal s₅.mem W := by rw [m₆]; exact Mem.readW_writeW_self32 _ _ _
  rw [okVal_eq] at hok
  -- The mask.
  refine WP.seq (WP.mono (mask_ok L E₆ K₆.slots.data K₆.slots.len h.n32 (h.data.buf.of_eq K₆.rd K₆.wr)
    (by rw [K₆.wr]; exact h.data.wr) hok) fun s₇ ⟨E₇, rd₇, wr₇, m₇⟩ => ?_)
  have f₇ : Frame [⟨w64 D, n⟩] s₆.mem s₇.mem := by
    rw [m₇]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  have K₇ : Kept s C W SP R D n [⟨w64 W, 16⟩, ⟨w64 D, n⟩] s₇ := K₆.step L hext2 E₇ rd₇ wr₇ f₇ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact .inr ⟨_, by simp, fun _ h => h⟩
  -- The result, and the exit.
  rw [WP.block_append_iff]
  obtain ⟨s₈, run₈, ax₈, g₈, m₈, rd₈, wr₈⟩ := retEax_ok L E₇
  refine WP.of_runBlock ⟨s₈, run₈, ?_⟩
  have K₈ : Kept s C W SP R D n [⟨w64 W, 16⟩, ⟨w64 D, n⟩] s₈ :=
    K₇.step L hext2 (E₇.keep (g₈ _ (by decide)) (g₈ _ (by decide)) rd₈ wr₈) rd₈ wr₈ (rs := [])
      (by rw [m₈]; exact Frame.refl _ _) (fun r hr => by simp at hr)
  have hret : s₈.mem.readW (w64 (s.gpr .esp)) 32 = s.mem.readW (w64 (s.gpr .esp)) 32 := by
    rw [h.sp]
    exact K₈.big.readW (r := ⟨w64 SP, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h.ret.sub_right (Lay.wSub (by decide))
      · exact ret_below L.sp
      · exact h.ret.sub_right (Region.sub_prefix (by decide))
      · exact h.retD) (by decide)
  refine WP.mono (exit_ok K₈.env.ebp (by rw [K₈.env.esp, h.sp]) (covers_left (fun a m ⟨r, hr, hc⟩ => by
      simp only [List.mem_singleton] at hr; subst hr
      exact K₈.env.perm.w a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩))
    (by have := L.fw; omega) K₈.saved hret) fun s₉ ⟨ab, m₉, ax₉, _, _⟩ => ⟨ab, ?_⟩
  -- The values.
  have iv₅ : bytesAt s₅.mem (w64 W) 16 = bytesAt s.mem (w64 T) 16 := by
    rw [Proof.AesGcm.X86.bytesAt_frame F.frame (w16_dis L dDW (finR_wR (.inr rfl))) (by decide),
      Proof.AesGcm.X86.bytesAt_frame f₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        simpa using Lay.w_w (W := W) (a := 0) (n := 16) (d := strO) (k := 8) (.inl (by decide)) (by decide)
          (by decide)) (by decide),
      Proof.AesGcm.X86.bytesAt_frame f₃ (w16_dis L dDW (ctrR_wR (by simp))) (by decide),
      Proof.AesGcm.X86.bytesAt_frame f₂ (w16_dis L dDW counter_wR) (by decide), ivT]
  have dc : ∀ r ∈ [(⟨w64 W, 16⟩ : Region), ⟨w64 D, n⟩], (⟨w64 C, 512⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact L.c_w.sub_right (Region.sub_prefix (by decide))
    · exact h.data.c
  have mac₄ : Spec.Siv.ctxMac s₄.mem (w64 C) R = Spec.Siv.ctxMac s.mem (w64 C) R := K₄.mac L hR dc
  have ciph₂ : Spec.Siv.ctxCiph s₂.mem (w64 C) R = Spec.Siv.ctxCiph s.mem (w64 C) R :=
    ctxCiph_frame K₂.big (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.c_w.sub_right (Lay.wSub (by decide))
      · exact L.stk_c.symm
      · exact L.c_w.sub_right (Region.sub_prefix (by decide))) hRb
  have p₂ : bytesAt s₂.mem (w64 D) n = bytesAt s.mem (w64 D) n :=
    K₂.bytes h.data.buf.w h.data.buf.stk (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dDW.symm) (by have := h.data.buf.lt; omega)
  -- `D`, from `encS2v` to `finish`.
  have dD : ∀ {rs : List Region}, (∀ r ∈ rs, (⟨w64 W + BitVec.ofNat 64 dOff, 16⟩ : Region).Disjoint r) →
      ∀ {m m' : Mem}, Frame rs m m' →
      bytesAt m' (w64 W + BitVec.ofNat 64 dOff) 16 = bytesAt m (w64 W + BitVec.ofNat 64 dOff) 16 :=
    fun hd _ _ hf => Proof.AesGcm.X86.bytesAt_frame hf hd (by decide)
  have acc₄ : bytesAt s₄.mem (w64 W + BitVec.ofNat 64 dOff) 16 =
      Spec.Siv.s2vAcc (Spec.Siv.ctxMac s.mem (w64 C) R) (Spec.Siv.components 32 s.mem (w64 A) N) := by
    rw [dD (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)) f₄,
      dD (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
        · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
        · exact (L.stk_w' (by decide)).symm
        · exact (h.data.buf.w.sub_right (Lay.wSub (by decide))).symm) f₃,
      dD (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)) f₂,
      dD (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide))
        fIn, O.acc]
  have pt₄ : bytesAt s₄.mem (w64 D) n = bytesAt s₃.mem (w64 D) n :=
    Proof.AesGcm.X86.bytesAt_frame f₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.data.buf.w.sub_right (Lay.wSub (by decide)))
      (by have := h.data.buf.lt; omega)
  have o₅ := F.out
  rw [mac₄, acc₄, pt₄] at o₅
  have pt₃ := d₃
  rw [ciph₂, p₂, ivT] at pt₃
  -- The plaintext through the comparison.
  have pt₆ : bytesAt s₆.mem (w64 D) n = bytesAt s₃.mem (w64 D) n := by
    rw [Proof.AesGcm.X86.bytesAt_frame f₆ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.data.buf.w.sub_right (Lay.wSub (by decide)))
        (by have := h.data.buf.lt; omega)]
    exact Proof.AesGcm.X86.bytesAt_frame F.frame (fun r hr => (finR_buf h.data.buf (.inr rfl) r hr))
      (by have := h.data.buf.lt; omega) |>.trans pt₄
  have hlm := length_mask s₆.mem (w64 D) (decide (bytesAt s₅.mem (w64 W) 16 =
    bytesAt s₅.mem (w64 W + BitVec.ofNat 64 tOff) 16)) n
  have out₇ : bytesAt s₇.mem (w64 D) n = if decide (bytesAt s₅.mem (w64 W) 16 =
      bytesAt s₅.mem (w64 W + BitVec.ofNat 64 tOff) 16) then bytesAt s₆.mem (w64 D) n else Spec.Siv.zeros n := by
    rw [m₇]
    have := Proof.AesGcm.X86.bytesAt_writeBytes_self s₆.mem (w64 D) _ (by rw [hlm]; have := h.data.buf.lt; omega)
    rw [hlm] at this
    exact this
  have ok₇ : slotv s₇.mem W okO = slotv s₆.mem W okO :=
    f₇.readW (r := ⟨w64 W + BitVec.ofNat 64 okO, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.data.buf.w.sub_right (Lay.wSub (by decide))).symm) (by decide)
  have eax₉ : s₉.gpr .eax = if decide (bytesAt s₅.mem (w64 W) 16 =
      bytesAt s₅.mem (w64 W + BitVec.ofNat 64 tOff) 16) then 1 else 0 := by
    rw [ax₉, ax₈, ok₇, hok]
  rw [Spec.Siv.decryptWith_eq, Spec.Siv.openWith, ← pt₃]
  rw [m₉, m₈, out₇, eax₉, iv₅, o₅, pt₆]
  by_cases hc : Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem (w64 C) R)
      (Spec.Siv.s2vAcc (Spec.Siv.ctxMac s.mem (w64 C) R) (Spec.Siv.components 32 s.mem (w64 A) N))
      (bytesAt s₃.mem (w64 D) n) = bytesAt s.mem (w64 T) 16
  · simp only [hc, ↓reduceIte, decide_true]
    exact ⟨trivial, trivial⟩
  · have hc' : ¬ bytesAt s.mem (w64 T) 16 = Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem (w64 C) R)
        (Spec.Siv.s2vAcc (Spec.Siv.ctxMac s.mem (w64 C) R) (Spec.Siv.components 32 s.mem (w64 A) N))
        (bytesAt s₃.mem (w64 D) n) := fun e => hc e.symm
    simp only [hc, hc', ↓reduceIte, decide_false]
    exact ⟨rfl, rfl⟩

end VG.Proof.AesSiv.X86

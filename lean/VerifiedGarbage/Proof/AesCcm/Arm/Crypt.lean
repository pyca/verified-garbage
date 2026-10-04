import VerifiedGarbage.Proof.AesCcm.Arm.Mac

/-!
# AES-CCM on ARMv7: counter mode (`ctr`)

Untrusted: everything here is checked by Lean. `ctrWhole` XORs the whole
blocks of the data with the keystream from `Ctr₁`, by one call of
`vg_aes_ctr32` from `Ctr₁` at `W + 64`, whose counters do not wrap around
(`ctrWhole_ok`, `Proof.AesCcm.ctr32_ccm`); `ctrTail` the last bytes with the
first bytes of `CIPH_K(Ctrⱼ)` for the block `j` after them, computed by
`vg_aes_ctr32` on a zero block at `W + 80` (`ctrTail_ok`). Together, the
data XORed with CCM's keystream from `Ctr₁` (`ctr_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesCcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI zero16 xorLoop ctrFrame)
open VG.Proof.AesGcm.Arm (LoopOut LoopPre xorLoop_ok xorBytes bytesAt_frame runBlock_app_of and15 shr4 toNat32
  ofNat_sub32 ofNat_add32 z_cmp eval_eq' Keeps z_subFlags gpr_subFlags covers_prefix covers_off covers_left
  ctr_call CtrPost CtrCall add32_ofNat_assoc)
open VG.Proof.AesCcm (ctxCiph_frame length_bytesAt xorFrom ctr32_ccm repeat_inc32_ctrBlock xorFrom_zeros
  xorFrom_tail xorFrom_append BlockCipher bytesAt_prefix bytesAt_writeBytes_base)

/-- The data: `n` bytes at `D` that the code may write, apart from `W`, the
key schedule and the stack below `sp`. -/
structure Dat (k w sp : BitVec 32) (s : State) (D : BitVec 32) (n : Nat) : Prop where
  buf : Buf w sp s D n
  wr : Covers [⟨State.addr D, n⟩] s.wr
  k : (⟨State.addr k, 240⟩ : Region).Disjoint ⟨State.addr D, n⟩

theorem Dat.of_eq {k w sp : BitVec 32} {s s' : State} {D : BitVec 32} {n : Nat} (h : Dat k w sp s D n)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Dat k w sp s' D n :=
  ⟨h.buf.of_eq hrd hwr, by rw [hwr]; exact h.wr, h.k⟩

/-- What `ctr` writes: the counter block and the keystream block at
`W + 64`, the working space of the functions called, the stack below `sp`
and the data. -/
abbrev ctrR (w sp D : BitVec 32) (n : Nat) : List Region :=
  [⟨State.addr w + BitVec.ofNat 64 64, 32⟩, scrR w, blw sp, ⟨State.addr D, n⟩]

theorem pow_q {q : Nat} (h : 2 ≤ q) : 256 ^ q = 256 * 256 ^ (q - 1) := by
  rw [← Nat.pow_succ']; congr 1; omega

section
variable {k w sp : BitVec 32} {R q1 : Nat} (L : Lay k w sp)
include L

/-- `Ctr₁` at `W + 64`, and the arguments of the call in `ctrWhole`, for the
`n / 16` whole blocks of the data at `D`. -/
theorem ctrWholeArgs_ok {s₁ : State} (he₁ : Env k w sp R q1 s₁) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {nonce : List Byte} (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13)
    (hc0₁ : bytesAt s₁.mem (State.addr w + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    {D : BitVec 32} {n : Nat} (hD : Dat k w sp s₁ D n) (h4₁ : s₁.gpr .r4 = D)
    (h12₁ : s₁.gpr .r12 = BitVec.ofNat 32 (n / 16)) :
    ∃ s₄, runBlock isa ([.mov .r0 (imm 1)] ++ ctrAt ++ ctrArgs ++ [.mov .r3 (.reg .r4)]) s₁ = some s₄ ∧
      CtrCall s₄ k (w + BitVec.ofNat 32 64) D (w + BitVec.ofNat 32 384) R (n / 16) ∧ Env k w sp R q1 s₄ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .lr → s₄.gpr r = s₁.gpr r) ∧
      s₄.rd = s₁.rd ∧ s₄.wr = s₁.wr ∧ s₄.sp = s₁.sp ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 64, 16⟩] s₁.mem s₄.mem ∧
      bytesAt s₄.mem (State.addr w + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce 1 := by
  have hq2 : 2 ≤ 15 - nonce.length := by omega
  have hp := pow_q hq2
  obtain ⟨s₂, run₂, h0₂, g₂, k₂⟩ : ∃ s₂, runBlock isa [.mov .r0 (imm 1)] s₁ = some s₂ ∧
      s₂.gpr .r0 = BitVec.ofNat 32 1 ∧ (∀ r, r ≠ .r0 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
    refine ⟨_, by arun [], ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · intro r a; simp [gpr_setReg, a]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have he₂ := he₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide)) k₂.sp k₂.rd k₂.wr
  have hm2 : 1 < 256 ^ min (15 - nonce.length) 4 := Nat.one_lt_pow (by omega) (by decide)
  obtain ⟨s₃, run₃, hc₃, f₃, g₃, rd₃, wr₃, sp₃⟩ := ctrAt_ok L he₂ h7 h13
    (by rw [k₂.mem]; exact hc0₁) h0₂ hm2
  have he₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide) (by decide)) sp₃ rd₃ wr₃
  obtain ⟨s₄, run₄, a0, a1, a2, a3, a12, alr, g₄, k₄⟩ : ∃ s₄, runBlock isa (ctrArgs ++ [.mov .r3 (.reg .r4)]) s₃ =
      some s₄ ∧ s₄.gpr .r0 = k ∧ s₄.gpr .r1 = BitVec.ofNat 32 R ∧ s₄.gpr .r2 = w + BitVec.ofNat 32 64 ∧
      s₄.gpr .r3 = D ∧ s₄.gpr .r12 = BitVec.ofNat 32 (n / 16) ∧ s₄.gpr .lr = w + BitVec.ofNat 32 384 ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .lr → s₄.gpr r = s₃.gpr r) ∧ Keeps s₃ s₄ := by
    have r4₃ : s₃.gpr .r4 = D := by
      rw [g₃ _ (by decide) (by decide), g₂ _ (by decide), h4₁]
    have r12₃ : s₃.gpr .r12 = BitVec.ofNat 32 (n / 16) := by
      rw [g₃ _ (by decide) (by decide), g₂ _ (by decide), h12₁]
    refine ⟨_, by simp only [ctrArgs, c1O, scrO]; arun [he₃.r9, he₃.r8, he₃.r11], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, he₃.r9]
    · simp [gpr_setReg, he₃.r8]
    · simp [gpr_setReg, he₃.r11]
    · simp [gpr_setReg, r4₃]
    · simp [gpr_setReg, r12₃]
    · simp [gpr_setReg, he₃.r11]
    · intro r a b c d e; simp [gpr_setReg, a, b, c, d, e]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have he₄ := he₃.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₄ _ (by decide) (by decide) (by decide) (by decide)
      (by decide)) k₄.sp k₄.rd k₄.wr
  have hb : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have hq := hD.buf.take hb
  have e64 := L.wA (d := 64) (by decide)
  have C₄ := ctrCall_of L he₄ hR (D := D) (n := n / 16) a0 a1 a2 a3 a12 alr hq.fit
    (hD.k.sub_right (Region.sub_prefix hb)) (hq.w.sub_right (Lay.wSub (by decide))).symm
    (hq.w.sub_right (Lay.wSub (by decide))) hq.stk
    (by rw [k₄.wr, wr₃, k₂.wr]; exact covers_prefix hD.wr hb)
  refine ⟨s₄, by
    rw [show [.mov .r0 (imm 1)] ++ ctrAt ++ ctrArgs ++ [.mov .r3 (.reg .r4)] =
      [.mov .r0 (imm 1)] ++ (ctrAt ++ (ctrArgs ++ [.mov .r3 (.reg .r4)])) by simp]
    exact runBlock_app_of run₂ (runBlock_app_of run₃ run₄), C₄, he₄, fun r a b c d e => by rw [g₄ r a b c d e, g₃ r a b, g₂ r a],
    by rw [k₄.rd, rd₃, k₂.rd], by rw [k₄.wr, wr₃, k₂.wr], by rw [k₄.sp, sp₃, k₂.sp],
    by rw [k₄.mem, ← k₂.mem]; exact f₃, by rw [k₄.mem]; exact hc₃⟩

/-- The whole blocks of the data, from `Ctr₁`. -/
theorem ctrWhole_ok {s : State} (he : Env k w sp R q1 s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {nonce : List Byte}
    (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13)
    (hc0 : bytesAt s.mem (State.addr w + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    {D : BitVec 32} {n : Nat} (hD : Dat k w sp s D n) (hn : n < 256 ^ (15 - nonce.length)) (hn4 : n < 2 ^ 32)
    (h4 : s.gpr .r4 = D) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) :
    WP isa ctrWhole s fun s' => Env k w sp R q1 s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 64, 32⟩, scrR w, blw sp, ⟨State.addr D, 16 * (n / 16)⟩] s.mem s'.mem ∧
      bytesAt s'.mem (State.addr D) (16 * (n / 16)) =
        xorFrom (Spec.Ccm.ctxCiph s.mem (State.addr k) R) nonce 1 (bytesAt s.mem (State.addr D) (16 * (n / 16))) := by
  obtain ⟨s₁, run₁, h12₁, hz, g₁, k₁⟩ := split16_ok hn4 h5
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) k₁.sp k₁.rd k₁.wr
  refine WP.ite (decide (n / 16 = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n / 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨he₁, k₁.rd, k₁.wr, fun r hr _ => g₁ r (by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
      by rw [k₁.mem]; exact Frame.refl _ _, ?_⟩
    rw [k₁.mem, h0]; rfl
  · have h0 : n / 16 ≠ 0 := by simpa using hf
    obtain ⟨s₄, run₄, C₄, he₄, g₄, rd₄, wr₄, sp₄, f₀₄', hc₄⟩ := ctrWholeArgs_ok L he₁ hR h7 h13
      (by rw [k₁.mem]; exact hc0) (hD.of_eq k₁.rd k₁.wr) (by rw [g₁ _ (by decide), h4]) h12₁
    have hb : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
    have hq := hD.buf.take hb
    have e64 := L.wA (d := 64) (by decide)
    refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
    refine WP.mono (ctr_call C₄) fun s₅ h => ?_
    have hsp₄ : s₄.sp = sp := he₄.sp
    have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
    -- Memory before the call: only `W + 64` changed.
    have f₀₄ : Frame [⟨State.addr w + BitVec.ofNat 64 64, 16⟩] s.mem s₄.mem := by
      rw [← k₁.mem]; exact f₀₄'
    have hK₄ : Spec.Ccm.ctxCiph s₄.mem (State.addr k) R = Spec.Ccm.ctxCiph s.mem (State.addr k) R :=
      ctxCiph_frame f₀₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.k_w' (by decide)) hRb
    have hD₄ : bytesAt s₄.mem (State.addr D) (16 * (n / 16)) = bytesAt s.mem (State.addr D) (16 * (n / 16)) :=
      bytesAt_frame f₀₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hq.w.sub_right (Lay.wSub (by decide)))
        (by have := hq.lt; omega)
    refine ⟨he₄.of_saved h.saved h.sp h.rd h.wr, by rw [h.rd, rd₄, k₁.rd],
      by rw [h.wr, wr₄, k₁.wr], fun r hr hlr => ?_, ?_, ?_⟩
    · have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [h.saved r hr hlr, g₄ r a.1 a.2.1 a.2.2.1 a.2.2.2.1 hlr, g₁ r a.2.2.2.2]
    · have f₅ := h.frame
      rw [hsp₄, e64, L.wA (d := 384) (by decide)] at f₅
      refine (f₀₄.sub fun r hr => ?_).trans (f₅.sub fun r hr => ?_)
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
        · exact ⟨_, by simp, fun _ h => h⟩
        · exact ⟨scrR w, by simp, Region.sub_prefix (by decide)⟩
        · exact ⟨blw sp, by simp, below_blw sp⟩
    · have hc := ctr32_ccm (m := s₄.mem) (m' := s₅.mem) (K := State.addr k) (C := State.addr (w + BitVec.ofNat 32 64))
        (D := State.addr D) (R := R) (nonce := nonce) (by omega) (j := 1) (k := n / 16)
        (fun i hi => by
          have e : Spec.Gcm.blockAt s₄.mem (State.addr (w + BitVec.ofNat 32 64)) =
              Spec.Gcm.ofBytes (Spec.Ccm.ctrBlock nonce 1) := by
            show Spec.Gcm.ofBytes _ = _
            rw [e64, hc₄]
          rw [e]
          exact repeat_inc32_ctrBlock h7 h13 (j := 1) (k := n / 16) (by omega) (by omega) i hi) h.out
      rw [hc, hK₄, hD₄]

/-- `Ctrⱼ` at `W + 64` for the block `j` after the whole ones, a zero block at
`W + 80`, and the arguments of the call in `ctrTail`. -/
theorem ctrTailArgs_ok {s₁ : State} (he₁ : Env k w sp R q1 s₁) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {nonce : List Byte} (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13)
    (hc0₁ : bytesAt s₁.mem (State.addr w + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    {n : Nat} (hn : n < 256 ^ (15 - nonce.length)) (hn4 : n < 2 ^ 32) (h5₁ : s₁.gpr .r5 = BitVec.ofNat 32 n) :
    ∃ s₅, runBlock isa (zero16 ksO ++ [.mov .r0 (.shifted .r5 .lsr 4), addI .r0 .r0 1] ++ ctrAt ++ ctrArgs ++
        [addI .r3 .r11 ksO, .mov .r12 (imm 1)]) s₁ = some s₅ ∧
      CtrCall s₅ k (w + BitVec.ofNat 32 64) (w + BitVec.ofNat 32 80) (w + BitVec.ofNat 32 384) R 1 ∧
      Env k w sp R q1 s₅ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₅.gpr r = s₁.gpr r) ∧
      s₅.rd = s₁.rd ∧ s₅.wr = s₁.wr ∧ s₅.sp = s₁.sp ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 64, 32⟩] s₁.mem s₅.mem ∧
      bytesAt s₅.mem (State.addr w + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce (n / 16 + 1) ∧
      bytesAt s₅.mem (State.addr w + BitVec.ofNat 64 80) 16 = Spec.Ccm.zeros 16 := by
  have hq2 : 2 ≤ 15 - nonce.length := by omega
  have hp := pow_q hq2
  have hj : n / 16 + 1 < 256 ^ min (15 - nonce.length) 4 := by
    rcases Nat.le_total (15 - nonce.length) 4 with h | h
    · rw [Nat.min_eq_left h]; omega
    · rw [Nat.min_eq_right h]; show n / 16 + 1 < 4294967296; omega
  obtain ⟨s₂, run₂, hm₂, g₂, rd₂, wr₂, sp₂, -⟩ := zero16_ok L he₁ (d := ksO) (by decide) (by decide)
  simp only [ksO] at hm₂
  obtain ⟨s₃, run₃, h0₃, g₃, k₃⟩ : ∃ s₃, runBlock isa [.mov .r0 (.shifted .r5 .lsr 4), addI .r0 .r0 1] s₂ =
      some s₃ ∧ s₃.gpr .r0 = BitVec.ofNat 32 (n / 16 + 1) ∧ (∀ r, r ≠ .r0 → s₃.gpr r = s₂.gpr r) ∧
      Keeps s₂ s₃ := by
    have r5₂ : s₂.gpr .r5 = BitVec.ofNat 32 n := by rw [g₂ _ (by decide), h5₁]
    refine ⟨_, by arun [], ?_, ?_, ?_⟩
    · simp [gpr_setReg, r5₂, shr4 hn4, imm, ofNat_add32]
    · intro r a; simp [gpr_setReg, a]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have he₃ := he₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> rw [g₃ _ (by decide), g₂ _ (by decide)])
    (k₃.sp.trans sp₂) (k₃.rd.trans rd₂) (k₃.wr.trans wr₂)
  have f₂ : Frame [⟨State.addr w + BitVec.ofNat 64 80, 16⟩] s₁.mem s₂.mem := by
    rw [hm₂]; exact Proof.Cmac.frame_store4 _ _ _ _ _
  have hc₃ : bytesAt s₃.mem (State.addr w + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0 := by
    rw [k₃.mem, bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide))
      (by decide)]; exact hc0₁
  obtain ⟨s₄, run₄, hc₄, f₄, g₄, rd₄, wr₄, sp₄⟩ := ctrAt_ok L he₃ h7 h13 hc₃ h0₃ hj
  have he₄ := he₃.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₄ _ (by decide) (by decide)) sp₄ rd₄ wr₄
  obtain ⟨s₅, run₅, a0, a1, a2, a3, a12, alr, g₅, k₅⟩ : ∃ s₅, runBlock isa (ctrArgs ++
      [addI .r3 .r11 ksO, .mov .r12 (imm 1)]) s₄ = some s₅ ∧
      s₅.gpr .r0 = k ∧ s₅.gpr .r1 = BitVec.ofNat 32 R ∧ s₅.gpr .r2 = w + BitVec.ofNat 32 64 ∧
      s₅.gpr .r3 = w + BitVec.ofNat 32 80 ∧ s₅.gpr .r12 = BitVec.ofNat 32 1 ∧
      s₅.gpr .lr = w + BitVec.ofNat 32 384 ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₅.gpr r = s₄.gpr r) ∧
      Keeps s₄ s₅ := by
    refine ⟨_, by simp only [ctrArgs, c1O, scrO, ksO]; arun [he₄.r9, he₄.r8, he₄.r11], ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩
    · simp [gpr_setReg, he₄.r9]
    · simp [gpr_setReg, he₄.r8]
    · simp [gpr_setReg, he₄.r11]
    · simp [gpr_setReg, he₄.r11]
    · simp [gpr_setReg]
    · simp [gpr_setReg, he₄.r11]
    · intro r a b c d e f; simp [gpr_setReg, a, b, c, d, e, f]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have he₅ := he₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₅ _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)) k₅.sp k₅.rd k₅.wr
  have e64 := L.wA (d := 64) (by decide)
  have e80 := L.wA (d := 80) (by decide)
  have C₅ := ctrCall_of L he₅ hR (D := w + BitVec.ofNat 32 80) (n := 1) a0 a1 a2 a3 a12 alr
    (by rw [L.wN (by decide)]; have := L.ww; omega) (by rw [e80]; exact L.k_w' (by decide))
    (by rw [e80]; exact L.w_w (.inl (by decide)) (by decide) (by decide))
    (by rw [e80]; exact L.w_w (.inl (by decide)) (by decide) (by decide))
    (by rw [e80]; exact L.stk_w' (by decide)) (by rw [e80]; exact he₅.perm.wC (by decide))
  refine ⟨s₅, by
    rw [show zero16 ksO ++ [.mov .r0 (.shifted .r5 .lsr 4), addI .r0 .r0 1] ++ ctrAt ++ ctrArgs ++
      [addI .r3 .r11 ksO, .mov .r12 (imm 1)] = zero16 ksO ++ ([.mov .r0 (.shifted .r5 .lsr 4), addI .r0 .r0 1] ++
      (ctrAt ++ (ctrArgs ++ [addI .r3 .r11 ksO, .mov .r12 (imm 1)]))) by simp]
    exact runBlock_app_of run₂ (runBlock_app_of run₃ (runBlock_app_of run₄ run₅)), C₅, he₅, fun r a b c d e f => by rw [g₅ r a b c d e f, g₄ r a b, g₃ r a, g₂ r a],
    by rw [k₅.rd, rd₄, k₃.rd, rd₂], by rw [k₅.wr, wr₄, k₃.wr, wr₂], by rw [k₅.sp, sp₄, k₃.sp, sp₂], ?_,
    by rw [k₅.mem]; exact hc₄, ?_⟩
  · rw [k₅.mem]
    refine (f₂.sub fun r hr => ?_).trans ?_
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub _ (by decide) (by decide)⟩
    · rw [← k₃.mem]
      exact f₄.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
  · rw [k₅.mem, bytesAt_frame f₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide))
      (by decide), k₃.mem, hm₂]
    exact store4_zero_bytes' _ _

/-- The last bytes of the data, with `CIPH_K(Ctrⱼ)` for the block `j` after
the whole ones. -/
theorem ctrTail_ok {t : State} (he : Env k w sp R q1 t) (hR : R = 10 ∨ R = 12 ∨ R = 14) {nonce : List Byte}
    (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13)
    (hc0 : bytesAt t.mem (State.addr w + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    {D : BitVec 32} {n : Nat} (hD : Dat k w sp t D n) (hn : n < 256 ^ (15 - nonce.length)) (hn4 : n < 2 ^ 32)
    (h4 : t.gpr .r4 = D) (h5 : t.gpr .r5 = BitVec.ofNat 32 n) :
    WP isa ctrTail t fun t' => Env k w sp R q1 t' ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
      (∀ r ∈ preserved, r ≠ .r6 → r ≠ .lr → t'.gpr r = t.gpr r) ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 64, 32⟩, scrR w, blw sp,
        ⟨State.addr D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩] t.mem t'.mem ∧
      bytesAt t'.mem (State.addr D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
        xorFrom (Spec.Ccm.ctxCiph t.mem (State.addr k) R) nonce (1 + n / 16)
          (bytesAt t.mem (State.addr D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16)) := by
  obtain ⟨s₁, run₁, h6₁, hz, g₁, k₁⟩ := split15_ok hn4 h5
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide)) k₁.sp k₁.rd k₁.wr
  refine WP.ite (decide (n % 16 = 0)) (eval_eq' hz) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n % 16 = 0 := by simpa using ht
    refine WP.block_nil ⟨he₁, k₁.rd, k₁.wr, fun r hr h6 _ => g₁ r h6, by rw [k₁.mem]; exact Frame.refl _ _, ?_⟩
    rw [k₁.mem, h0]; rfl
  · have h0 : n % 16 ≠ 0 := by simpa using hf
    obtain ⟨s₅, run₅, C₅, he₅, g₅, rd₅, wr₅, sp₅, f₀₅', hc₄, hz₅⟩ := ctrTailArgs_ok L he₁ hR h7 h13
      (by rw [k₁.mem]; exact hc0) hn hn4 (by rw [g₁ _ (by decide), h5])
    have e64 := L.wA (d := 64) (by decide)
    have e80 := L.wA (d := 80) (by decide)
    refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
    refine WP.seq (WP.mono (ctr_call C₅) fun s₆ h => ?_)
    have he₆ := he₅.of_saved h.saved h.sp h.rd h.wr
    have hsp₅ : s₅.sp = sp := he₅.sp
    have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
    have g₆ : ∀ r ∈ preserved, r ≠ .r6 → r ≠ .lr → s₆.gpr r = t.gpr r := fun r hr h6 hlr => by
      have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [h.saved r hr hlr, g₅ r a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2 hlr, g₁ r h6]
    -- Memory before the call: `W + 64` and `W + 80` changed.
    have f₀₅ : Frame [⟨State.addr w + BitVec.ofNat 64 64, 32⟩] t.mem s₅.mem := by
      rw [← k₁.mem]; exact f₀₅'
    have hK₅ : Spec.Ccm.ctxCiph s₅.mem (State.addr k) R = Spec.Ccm.ctxCiph t.mem (State.addr k) R :=
      ctxCiph_frame f₀₅ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.k_w' (by decide)) hRb
    have hBC : BlockCipher (Spec.Ccm.ctxCiph t.mem (State.addr k) R) := fun x => Proof.Cmac.aesWith_length _ _ x
    have hks : bytesAt s₆.mem (State.addr w + BitVec.ofNat 64 80) 16 =
        Spec.Ccm.ctxCiph t.mem (State.addr k) R (Spec.Ccm.ctrBlock nonce (n / 16 + 1)) := by
      have hx := ctr32_ccm (m := s₅.mem) (m' := s₆.mem) (K := State.addr k) (C := State.addr (w + BitVec.ofNat 32 64))
        (D := State.addr (w + BitVec.ofNat 32 80)) (R := R) (nonce := nonce) (by omega) (j := n / 16 + 1) (k := 1)
        (fun i hi => by
          rw [show i = 0 by omega, Nat.add_zero]
          show Spec.Gcm.ofBytes _ = _
          rw [e64, hc₄]) h.out
      rw [Nat.mul_one, e80] at hx
      rw [hx, hz₅, hK₅, xorFrom_zeros hBC]
    -- The arguments of the XOR.
    have h11 := he₆.r11
    have hb : 16 * (n / 16) < n := by omega
    have eD := hD.buf.addr (j := 16 * (n / 16)) hb
    obtain ⟨s₇, run₇, a1₇, a2₇, a3₇, g₇, k₇⟩ : ∃ s₇, runBlock isa [addI .r1 .r11 ksO, .dp .sub .r2 .r5 (.reg .r6),
        .dp .add .r2 .r2 (.reg .r4), .mov .r3 (.reg .r6)] s₆ = some s₇ ∧
        s₇.gpr .r1 = w + BitVec.ofNat 32 80 ∧ s₇.gpr .r2 = D + BitVec.ofNat 32 (16 * (n / 16)) ∧
        s₇.gpr .r3 = BitVec.ofNat 32 (n % 16) ∧
        (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s₇.gpr r = s₆.gpr r) ∧ Keeps s₆ s₇ := by
      have r4₆ : s₆.gpr .r4 = D := by rw [g₆ _ (by decide) (by decide) (by decide), h4]
      have r5₆ : s₆.gpr .r5 = BitVec.ofNat 32 n := by rw [g₆ _ (by decide) (by decide) (by decide), h5]
      have r6₆ : s₆.gpr .r6 = BitVec.ofNat 32 (n % 16) := by
        rw [h.saved _ (by decide) (by decide), g₅ _ (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), h6₁]
      have hsub : BitVec.ofNat 32 n - BitVec.ofNat 32 (n % 16) = BitVec.ofNat 32 (16 * (n / 16)) := by
        rw [ofNat_sub32 (Nat.mod_le _ _) hn4]; congr 1; omega
      refine ⟨_, by simp only [ksO]; arun [h11], ?_, ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, h11]
      · simp [gpr_setReg, r4₆, r5₆, r6₆, hsub, BitVec.add_comm]
      · simp [gpr_setReg, r6₆]
      · intro r a b c; simp [gpr_setReg, a, b, c]
      · exact ⟨rfl, rfl, rfl, rfl⟩
    refine WP.seq (WP.of_runBlock ⟨s₇, run₇, ?_⟩)
    have hT := (hD.buf.sub (j := 16 * (n / 16)) (k := n % 16) (by omega) (by omega))
    have hTw := hT.w
    have hTs := hT.stk
    rw [eD] at hTw hTs
    have wr₇ : s₇.wr = t.wr := by rw [k₇.wr, h.wr, wr₅, k₁.wr]
    have rd₇ : s₇.rd = t.rd := by rw [k₇.rd, h.rd, rd₅, k₁.rd]
    have lp : LoopPre s₇ (w + BitVec.ofNat 32 80) (D + BitVec.ofNat 32 (16 * (n / 16))) (n % 16) := by
      refine ⟨a1₇, a2₇, a3₇, by omega, by omega, by rw [L.wN (by decide)]; have := L.ww; omega, hT.fit, ?_, ?_, ?_⟩
      · rw [e80]; exact covers_left ((he₆.perm.of_eq k₇.rd k₇.wr).wC (by omega))
      · rw [wr₇, eD]; exact covers_off hD.wr (by omega) hD.buf.lt
      · rw [e80, eD]; exact (hTw.sub_right (Lay.wSub (by omega))).symm
    refine WP.mono (xorLoop_ok s₇ lp) fun s₈ ⟨hm₈, lo⟩ => ?_
    rw [e80, eD] at hm₈
    have hxl : (xorBytes s₇.mem (State.addr D + BitVec.ofNat 64 (16 * (n / 16)))
        (State.addr w + BitVec.ofNat 64 80) (n % 16)).length = n % 16 := by
      simp [xorBytes, length_bytesAt]
    -- What was written.
    have fC : Frame [⟨State.addr w + BitVec.ofNat 64 64, 32⟩, scrR w, blw sp] t.mem s₇.mem := by
      have fc := h.frame
      rw [hsp₅, e64, e80, L.wA (d := 384) (by decide)] at fc
      rw [k₇.mem]
      refine (f₀₅.sub fun r hr => ?_).trans (fc.sub fun r hr => ?_)
      · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
        · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
        · exact ⟨scrR w, by simp, Region.sub_prefix (by decide)⟩
        · exact ⟨blw sp, by simp, below_blw sp⟩
    have fw : Frame [⟨State.addr D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩] s₇.mem s₈.mem := by
      rw [hm₈]; exact writeBytes_frame _ _ _ (by rw [hxl]; exact Region.contains_self _ _)
    refine ⟨he₆.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;>
          rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide),
            g₇ _ (by decide) (by decide) (by decide)]) (lo.sp.trans k₇.sp) (lo.rd.trans k₇.rd) (lo.wr.trans k₇.wr),
      by rw [lo.rd, rd₇], by rw [lo.wr, wr₇], fun r hr h6 hlr => ?_, ?_, ?_⟩
    · have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [lo.other r a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2, g₇ r a.2.1 a.2.2.1 a.2.2.2.1, g₆ r hr h6 hlr]
    · refine (fC.sub fun r hr => ?_).trans (fw.sub fun r hr => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · have h₂ : bytesAt s₇.mem (State.addr D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
          bytesAt t.mem (State.addr D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
        bytesAt_frame fC (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact hTw.sub_right (Lay.wSub (by decide))
          · exact hTw.sub_right (Lay.wSub (by decide))
          · exact hTs.symm) (by omega)
      have hk₇ : bytesAt s₇.mem (State.addr w + BitVec.ofNat 64 80) (n % 16) =
          (Spec.Ccm.ctxCiph t.mem (State.addr k) R (Spec.Ccm.ctrBlock nonce (n / 16 + 1))).take (n % 16) := by
        rw [bytesAt_prefix _ _ (show n % 16 ≤ 16 by omega), k₇.mem, hks]
      have ht := xorFrom_tail (ciph := Spec.Ccm.ctxCiph t.mem (State.addr k) R) nonce (n / 16 + 1)
        (d := bytesAt t.mem (State.addr D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16))
        (by rw [length_bytesAt]; omega)
      rw [length_bytesAt, hBC] at ht
      have ht' := ht.resolve_right (by omega)
      rw [hm₈, bytesAt_writeBytes_base _ _ _ (by rw [hxl]) (by omega), hxl, List.drop_eq_nil_of_le
        (by rw [length_bytesAt]), List.append_nil, xorBytes, h₂, hk₇, ht', Nat.add_comm 1]

/-- Counter mode: the data XORed with CCM's keystream from `Ctr₁`. -/
theorem ctr_ok {s₀ s : State} (he : Env k w sp R q1 s) (hk : Stk w s₀ s) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {nonce : List Byte} (h7 : 7 ≤ nonce.length) (h13 : nonce.length ≤ 13)
    (hc0 : bytesAt s.mem (State.addr w + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0)
    {D : BitVec 32} {n : Nat} (eD : stackArg s₀ 2 = D) (en : stackArg s₀ 3 = BitVec.ofNat 32 n)
    (hD : Dat k w sp s D n) (hn : n < 256 ^ (15 - nonce.length)) (hn4 : n < 2 ^ 32) :
    WP isa ctr s fun s' => Env k w sp R q1 s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      Frame (ctrR w sp D n) s.mem s'.mem ∧
      bytesAt s'.mem (State.addr D) n =
        xorFrom (Spec.Ccm.ctxCiph s.mem (State.addr k) R) nonce 1 (bytesAt s.mem (State.addr D) n) := by
  obtain ⟨s₁, run₁, h4₁, h5₁, g₁, k₁⟩ := dataLd_ok hk eD en
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide)) k₁.sp k₁.rd k₁.wr
  have hD₁ := hD.of_eq k₁.rd k₁.wr
  rw [← k₁.mem] at hc0
  have hb : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  refine WP.seq (WP.mono (ctrWhole_ok L he₁ hR h7 h13 hc0 hD₁ hn hn4 h4₁ h5₁) fun s₂ ⟨he₂, rd₂, wr₂, g₂, f₂, o₂⟩ => ?_)
  have hDw := hD.buf.w
  have hDs := hD.buf.stk
  have dP : ∀ {a l : Nat}, a + l ≤ n → ∀ r ∈ [⟨State.addr w + BitVec.ofNat 64 64, 32⟩, scrR w, blw sp],
      (⟨State.addr D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := by
    intro a l hl r hr
    have hs : Region.Sub ⟨State.addr D + BitVec.ofNat 64 a, l⟩ ⟨State.addr D, n⟩ := Offset.sub_base _ hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hDw.sub_left hs).sub_right (Lay.wSub (by decide))
    · exact (hDw.sub_left hs).sub_right (Lay.wSub (by decide))
    · exact (hDs.sub_right hs).symm
  have kD : ∀ r ∈ [⟨State.addr w + BitVec.ofNat 64 64, 32⟩, scrR w, blw sp, ⟨State.addr D, 16 * (n / 16)⟩],
      (⟨State.addr k, 240⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.k_w' (by decide)
    · exact L.k_w' (by decide)
    · exact L.stk_k.symm
    · exact hD.k.sub_right (Region.sub_prefix hb)
  have hc₂ : bytesAt s₂.mem (State.addr w + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0 := by
    rw [bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · exact (L.stk_w' (by decide)).symm
      · exact (hDw.sub_left (Region.sub_prefix hb)).sub_right (Lay.wSub (by decide)) |>.symm) (by decide)]
    exact hc0
  have r4₂ : s₂.gpr .r4 = D := by rw [g₂ _ (by decide) (by decide), h4₁]
  have r5₂ : s₂.gpr .r5 = BitVec.ofNat 32 n := by rw [g₂ _ (by decide) (by decide), h5₁]
  refine WP.mono (ctrTail_ok L he₂ hR h7 h13 hc₂ (hD₁.of_eq rd₂ wr₂) hn hn4 r4₂ r5₂)
    fun s₃ ⟨he₃, rd₃, wr₃, g₃, f₃, o₃⟩ => ?_
  have f₁₂ : Frame (ctrR w sp D n) s.mem s₂.mem := by
    rw [← k₁.mem]
    exact f₂.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨⟨State.addr D, n⟩, by simp, Region.sub_prefix hb⟩
  refine ⟨he₃, by rw [rd₃, rd₂, k₁.rd], by rw [wr₃, wr₂, k₁.wr], fun r hr h4 h5 h6 hlr => ?_,
    f₁₂.trans (f₃.sub fun r hr => ?_), ?_⟩
  · rw [g₃ r hr h6 hlr, g₂ r hr hlr, g₁ r h4 h5]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨State.addr D, n⟩, by simp, Offset.sub_base _ (by omega)⟩
  · have hs : 16 * (n / 16) + n % 16 = n := Nat.div_add_mod n 16
    have hK₂ : Spec.Ccm.ctxCiph s₂.mem (State.addr k) R = Spec.Ccm.ctxCiph s.mem (State.addr k) R := by
      rw [ctxCiph_frame f₂ kD hRb, k₁.mem]
    -- The whole blocks, which the tail keeps.
    have h₁ : bytesAt s₃.mem (State.addr D) (16 * (n / 16)) = bytesAt s₂.mem (State.addr D) (16 * (n / 16)) :=
      bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact (hDw.sub_left (Region.sub_prefix hb)).sub_right (Lay.wSub (by decide))
        · exact (hDw.sub_left (Region.sub_prefix hb)).sub_right (Lay.wSub (by decide))
        · exact (hDs.sub_right (Region.sub_prefix hb)).symm
        · exact Offset.base_disjoint _ (Nat.le_refl _) (by have := hD.buf.lt; omega)) (by have := hD.buf.lt; omega)
    -- The rest, which the whole blocks keep.
    have h₂ : bytesAt s₂.mem (State.addr D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
        bytesAt s.mem (State.addr D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
      rw [bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact dP (by omega) _ (List.mem_cons_self ..)
        · exact dP (by omega) _ (by simp)
        · exact dP (by omega) _ (by simp)
        · exact Offset.disjoint_base _ (Nat.le_refl _) (by have := hD.buf.lt; omega)) (by omega), k₁.mem]
    have split : ∀ m : Mem, bytesAt m (State.addr D) n = bytesAt m (State.addr D) (16 * (n / 16)) ++
        bytesAt m (State.addr D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := fun m => by
      conv => lhs; rw [← hs]
      exact Proof.Cmac.Stream.bytesAt_append _ _ _ _
    rw [split, split, h₁, o₂, o₃, hK₂, h₂, k₁.mem, xorFrom_append _ _ _ (length_bytesAt _ _ _), Nat.add_comm 1]

end

end VG.Proof.AesCcm.Arm

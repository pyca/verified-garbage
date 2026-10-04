import VerifiedGarbage.Proof.AesSiv.Arm.FinishLong
import VerifiedGarbage.Proof.AesGcm.Arm.Compare
import VerifiedGarbage.Proof.AesGcm.Arm.Tag
import VerifiedGarbage.Proof.AesGcm.Arm.Flush

/-!
# AES-SIV on ARMv7: CTR (`ctr`)

Untrusted: everything here is checked by Lean. `counter 0` sets the counter
block at `W + 96` to `Q`, the IV at `W` with bit 7 of its bytes 8 and 12
cleared (`counter_ok`, `Proof.AesSiv.counter_words4`). `ctrWhole` encrypts
the whole blocks of the data by one call of `vg_aes_ctr32` from `Q`, whose
counters do not wrap around (`Proof.AesSiv.counter_low`,
`Proof.AesSiv.repeat_inc32`), and which leaves `Q + nb` in the counter block
(`ctrWhole_ok`); `ctrTail` XORs the last bytes with the first bytes of the
keystream block of that counter, which `vg_aes_ctr32` computes on a zero
block at `W + 80` (`ctrTail_ok`). Together, CTR's output on the data
(`ctr_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesSiv.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI ctrFrame xorLoop)
open VG.Impl.CmacAes.Arm (mov)
open VG.Proof.Cmac (le4 store4)
open VG.Proof.AesGcm.Arm (mem_store store32_eq gpr_store rd_store wr_store sp_store encodable_of_decide sepW
  bytes_words store4_eq add_ofNat_assoc)
open VG.Proof.AesSiv (qm4 orr_eor_80 counter_words4)
open VG.Proof.AesCcm.Arm (blw)
open VG.Proof.AesGcm.Arm (bytesAt_frame)
open VG.Proof.MdStream.Arm (wp_ldrSp)
open VG.Proof.AesSiv (counter_low)

section
variable {c w sp : BitVec 32} {R : Nat} (L : Lay c w sp)
include L

/-- `counter 0`: `Q` at `W + 96`, from the IV at `W`. -/
theorem counter_ok {s : State} (he : Env c w sp R s) :
    ∃ s', runBlock isa (counter 0) s = some s' ∧
      bytesAt s'.mem (State.addr w + BitVec.ofNat 64 cbOff) 16 = Spec.Siv.counter (bytesAt s.mem (State.addr w) 16) ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 cbOff, 16⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have h11 := he.r11
  have r₀ := he.perm.wR (show 0 + 4 ≤ 2576 by decide)
  have r₁ := he.perm.wR (show 4 + 4 ≤ 2576 by decide)
  have r₂ := he.perm.wR (show 8 + 4 ≤ 2576 by decide)
  have r₃ := he.perm.wR (show 12 + 4 ≤ 2576 by decide)
  have w₀ := he.perm.wW (show 96 + 4 ≤ 2576 by decide)
  have w₁ := he.perm.wW (show 100 + 4 ≤ 2576 by decide)
  have w₂ := he.perm.wW (show 104 + 4 ≤ 2576 by decide)
  have w₃ := he.perm.wW (show 108 + 4 ≤ 2576 by decide)
  have q : ∀ a d, a + 4 ≤ d → d + 4 ≤ 2576 →
      (⟨State.addr w + BitVec.ofNat 64 a, 4⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 d, 4⟩ :=
    fun a d h₁ h₂ => L.w_w (.inl h₁) (by omega) h₂
  have p₁ := fun m v => sepW (m := m) (v := v) (q 4 96 (by decide) (by decide))
  have p₂ := fun m v => sepW (m := m) (v := v) (q 8 96 (by decide) (by decide))
  have p₃ := fun m v => sepW (m := m) (v := v) (q 8 100 (by decide) (by decide))
  have p₄ := fun m v => sepW (m := m) (v := v) (q 12 96 (by decide) (by decide))
  have p₅ := fun m v => sepW (m := m) (v := v) (q 12 100 (by decide) (by decide))
  have p₆ := fun m v => sepW (m := m) (v := v) (q 12 104 (by decide) (by decide))
  have e := fun d (hd : d < 2576) => L.wA (d := d) hd
  let m := s.mem
  let W := State.addr w
  have hm : ∃ s', runBlock isa (counter 0) s = some s' ∧
      s'.mem = store4 m (W + BitVec.ofNat 64 96) (m.readW (W + BitVec.ofNat 64 0) 32)
        (m.readW (W + BitVec.ofNat 64 4) 32) ((m.readW (W + BitVec.ofNat 64 8) 32 ||| 0x80#32) ^^^ 0x80#32)
        ((m.readW (W + BitVec.ofNat 64 12) 32 ||| 0x80#32) ^^^ 0x80#32) ∧
      (∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    refine ⟨_, by simp only [counter, cbOff]; arun [h11, e, r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃, p₁, p₂, p₃,
      p₄, p₅, p₆], ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_store, store4_eq, add_ofNat_assoc, m, W]
    · intro r a; simp [gpr_setReg, a]
    all_goals exact ⟨rfl, rfl, rfl⟩
  obtain ⟨s', run, hm', g, rd, wr, sp⟩ := hm
  refine ⟨s', run, ?_, by rw [hm']; exact Proof.Cmac.frame_store4 _ _ _ _ _, g, rd, wr, sp⟩
  rw [hm', Proof.Cmac.bytesAt_store4, orr_eor_80, orr_eor_80, counter_words4, bytes_words]
  simp only [add_ofNat_assoc, BitVec.add_zero, m, W]

omit L in
theorem below_blw (sp : BitVec 32) : Region.Sub (Proof.AesGcm.Arm.below sp) (blw sp) :=
  Offset.sub_below (State.addr sp) (a := 8) (b := 16) (by decide) (by decide)

/-- A call of `vg_aes_ctr32` with `K2`'s schedule, the counter block at
`W + 96`, `n` blocks at `D` and the working space at `W + 256`. -/
theorem ctrCall_of {s : State} (he : Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {D : BitVec 32}
    {n : Nat} (h0 : s.gpr .r0 = c + BitVec.ofNat 32 272) (h1 : s.gpr .r1 = BitVec.ofNat 32 R)
    (h2 : s.gpr .r2 = w + BitVec.ofNat 32 cbOff) (h3 : s.gpr .r3 = D) (h12 : s.gpr .r12 = BitVec.ofNat 32 n)
    (hlr : s.gpr .lr = w + BitVec.ofNat 32 256)
    (fD : D.toNat + 16 * n ≤ 2 ^ 32) (dK : (⟨State.addr c + BitVec.ofNat 64 272, 240⟩ : Region).Disjoint
      ⟨State.addr D, 16 * n⟩)
    (dC : (⟨State.addr w + BitVec.ofNat 64 cbOff, 16⟩ : Region).Disjoint ⟨State.addr D, 16 * n⟩)
    (dS : (⟨State.addr D, 16 * n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 256, 2048⟩)
    (dB : (blw sp).Disjoint ⟨State.addr D, 16 * n⟩) (wD : Covers [⟨State.addr D, 16 * n⟩] s.wr) :
    Proof.AesGcm.Arm.CtrCall s (c + BitVec.ofNat 32 272) (w + BitVec.ofNat 32 cbOff) D (w + BitVec.ofNat 32 256) R n := by
  have eC := L.wA (d := cbOff) (by decide)
  have eS := L.wA (d := 256) (by decide)
  have eK := L.cA (d := 272) (by decide)
  have hsp := he.sp
  refine ⟨h0, h1, h2, h3, h12, hlr, hR, by rw [hsp]; have := L.sp16; omega,
    by rw [L.cN (by decide)]; have := L.cw; omega, by rw [L.wN (by decide)]; have := L.ww; simp only [cbOff]; omega, fD,
    by rw [L.wN (by decide)]; have := L.ww; omega, ?_, by rw [eK]; exact dK, ?_, by rw [eC]; exact dC, ?_,
    by rw [eS]; exact dS, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eK, eC]; exact L.c_w' (by decide) (by decide)
  · rw [eK, eS]; exact L.c_w' (by decide) (by decide)
  · rw [eC, eS]; exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · rw [hsp, eK]; exact (L.stk_c' (by decide)).sub_left (below_blw sp)
  · rw [hsp, eC]; exact (L.stk_w' (by decide)).sub_left (below_blw sp)
  · rw [hsp]; exact dB.sub_left (below_blw sp)
  · rw [hsp, eS]; exact (L.stk_w' (by decide)).sub_left (below_blw sp)
  · rw [eK]; exact he.perm.cC (by decide)
  · rw [eC, eS]
    exact Proof.AesGcm.Arm.covers_cons (he.perm.wC (by decide))
      (Proof.AesGcm.Arm.covers_cons wD (he.perm.wC (by decide)))

/-- The data: `n` bytes at `D` that the code may write. -/
abbrev ctrR (w sp D : BitVec 32) (n : Nat) : List Region :=
  [⟨State.addr w + BitVec.ofNat 64 ksOff, 32⟩, scrR w, blw sp, ⟨State.addr D, n⟩]

omit L in
theorem split16_ok {s : State} {n : Nat} (hn : n < 2 ^ 32) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) :
    ∃ s₁, runBlock isa [.mov .r12 (.shifted .r5 .lsr 4), .cmp .r12 (imm 0)] s = some s₁ ∧
      s₁.gpr .r12 = BitVec.ofNat 32 (n / 16) ∧ s₁.z = decide (n / 16 = 0) ∧
      (∀ r, r ≠ .r12 → s₁.gpr r = s.gpr r) ∧ Proof.AesGcm.Arm.Keeps s s₁ := by
  refine ⟨_, by arun [], ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, h5, Proof.AesGcm.Arm.shr4 hn]
  · simp only [Proof.AesGcm.Arm.z_subFlags, gpr_setReg, Proof.AesGcm.Arm.gpr_subFlags, ite_true, ite_false,
      reduceCtorEq, h5, Proof.AesGcm.Arm.shr4 hn]
    exact Proof.AesGcm.Arm.z_cmp (by omega) (by decide)
  · intro r a; simp [gpr_setReg, a]
  · exact ⟨rfl, rfl, rfl, rfl⟩


/-- The arguments of the call in `ctrWhole`. -/
theorem ctrWholeArgs_ok {s₀ s₁ : State} (he₁ : Env c w sp R s₁) (hR : R = 10 ∨ R = 12 ∨ R = 14) {D : BitVec 32}
    {n : Nat} (hD : Dat c w sp s₀ D n) (h6₁ : s₁.gpr .r6 = D) (hwr : s₁.wr = s₀.wr)
    (h12₁ : s₁.gpr .r12 = BitVec.ofNat 32 (n / 16)) :
    ∃ s₂, runBlock isa (ctrArgs ++ [mov .r3 .r6]) s₁ = some s₂ ∧ Env c w sp R s₂ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .lr → s₂.gpr r = s₁.gpr r) ∧
      Proof.AesGcm.Arm.Keeps s₁ s₂ ∧
      Proof.AesGcm.Arm.CtrCall s₂ (c + BitVec.ofNat 32 272) (w + BitVec.ofNat 32 cbOff) D
        (w + BitVec.ofNat 32 256) R (n / 16) := by
  have hb : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have hdb := hD.buf.take hb
  refine ⟨_, by simp only [ctrArgs, cbOff, csOff, mov]; arun [he₁.r9, he₁.r10, he₁.r11], ?_⟩
  refine ⟨he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl,
    fun r a b c' d e => by simp [gpr_setReg, a, b, c', d, e], ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  refine ctrCall_of L ?_ hR ?_ ?_ ?_ ?_ ?_ ?_ hdb.fit ?_ ?_ ?_ hdb.stk ?_
  · exact he₁.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl
  · simp [gpr_setReg, he₁.r10]
  · simp [gpr_setReg, he₁.r9]
  · simp [gpr_setReg, he₁.r11]
  · simp [gpr_setReg, h6₁]
  · simp [gpr_setReg, h12₁]
  · simp [gpr_setReg, he₁.r11]
  · exact (hD.c.sub_left (Lay.cSub (by decide))).sub_right (Region.sub_prefix hb)
  · exact (hdb.w.sub_right (Lay.wSub (by decide))).symm
  · exact hdb.w.sub_right (Lay.wSub (by decide))
  · simp only [wr_setReg]; rw [hwr]; exact Proof.AesGcm.Arm.covers_prefix hD.wr hb

/-- The whole blocks of the data, from the counter `q` at `W + 96`, whose last
32 bits do not wrap around. -/
theorem ctrWhole_ok {s : State} (he : Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {D : BitVec 32} {n : Nat}
    (hD : Dat c w sp s D n) (hn : n < 2 ^ 32) (h6 : s.gpr .r6 = D) (h5 : s.gpr .r5 = BitVec.ofNat 32 n)
    {q : List Byte} (hq : bytesAt s.mem (State.addr w + BitVec.ofNat 64 cbOff) 16 = q)
    (hlow : Spec.Siv.beNat q % 2 ^ 32 + n / 16 + 1 ≤ 2 ^ 32) :
    WP isa ctrWhole s fun s' => Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) ∧ Frame (ctrR w sp D n) s.mem s'.mem ∧
      bytesAt s'.mem (State.addr D) n =
        ctrPart (Spec.Siv.ctxCiph s.mem (State.addr c) R) q (bytesAt s.mem (State.addr D) n) (16 * (n / 16)) ∧
      Spec.Gcm.blockAt s'.mem (State.addr w + BitVec.ofNat 64 cbOff) =
        Spec.Gcm.ofBytes (Spec.Siv.be128 (Spec.Siv.beNat q + n / 16)) := by
  have hql : q.length = 16 := by rw [← hq, Proof.Cmac.bytesAt_length]
  have hinc := repeat_inc32 hql (k := n / 16 + 1) (by omega)
  have eC := L.wA (d := cbOff) (by decide)
  have hcb : Spec.Gcm.blockAt s.mem (State.addr w + BitVec.ofNat 64 cbOff) = Spec.Gcm.ofBytes q := by
    rw [Spec.Gcm.blockAt, hq]
  obtain ⟨s₁, run₁, h12₁, hz, g₁, k₁⟩ := split16_ok hn h5
  have he₁ : Env c w sp R s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₁ _ (by decide)) k₁.sp k₁.rd k₁.wr
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hlen := Proof.Cmac.bytesAt_length s.mem (State.addr D) n
  by_cases h0 : n / 16 = 0
  · refine WP.ite true (Proof.AesGcm.Arm.eval_eq' (by rw [hz]; simp [h0])) (fun _ => WP.block_nil ?_)
      (fun h => by cases h)
    refine ⟨he₁, k₁.rd, k₁.wr, fun r _ _ => g₁ r (by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at *
        rintro rfl; simp_all), by rw [k₁.mem]; exact Frame.refl _ _, ?_, ?_⟩
    · rw [k₁.mem, h0, Nat.mul_zero, ctrPart_zero]
    · rw [k₁.mem, hcb, h0, Nat.add_zero]
      have := hinc 0 (by omega)
      rw [Nat.add_zero] at this
      exact this
  · refine WP.ite false (Proof.AesGcm.Arm.eval_eq' (by rw [hz]; simp [h0])) (fun h => by cases h) fun _ => ?_
    have hb : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
    have hdb := hD.buf.take hb
    obtain ⟨s₂, run₂, he₂, g₂, k₂, C⟩ := ctrWholeArgs_ok L he₁ hR hD (by rw [g₁ _ (by decide), h6])
      (by rw [k₁.wr]) h12₁
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    refine WP.mono (Proof.AesGcm.Arm.ctr_call C) fun s₃ h₃ => ?_
    have hsp₂ : s₂.sp = sp := he₂.sp
    have hRb := rounds_le hR
    have eK := L.cA (d := 272) (by decide)
    have eS := L.wA (d := 256) (by decide)
    have f₃ := h₃.frame
    rw [eC, eS, hsp₂] at f₃
    have mem₂ : s₂.mem = s.mem := by rw [k₂.mem, k₁.mem]
    have fT : Frame (ctrR w sp D n) s.mem s₃.mem := by
      rw [← mem₂]
      exact f₃.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
        · exact ⟨⟨State.addr D, n⟩, by simp, Region.sub_prefix hb⟩
        · exact ⟨scrR w, by simp, Region.sub_prefix (by decide)⟩
        · exact ⟨blw sp, by simp, below_blw sp⟩
    refine ⟨he₂.of_saved h₃.saved h₃.sp h₃.rd h₃.wr, by rw [h₃.rd, k₂.rd, k₁.rd],
      by rw [h₃.wr, k₂.wr, k₁.wr], fun r hr hlr => ?_, fT, ?_, ?_⟩
    · have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [h₃.saved r hr hlr, g₂ r a.1 a.2.1 a.2.2.1 a.2.2.2.1 hlr, g₁ r a.2.2.2.2]
    · -- The whole blocks, then the rest as it was.
      have hc := ctr32_ctrPart (m := s₂.mem) (m' := s₃.mem) (K := State.addr (c + BitVec.ofNat 32 272))
        (C := State.addr (w + BitVec.ofNat 32 cbOff)) (D := State.addr D) (R := R) (q := q) (k := n / 16)
        (fun i hi => by rw [eC, mem₂, hcb]; exact hinc i (by omega)) h₃.out
      have e := Proof.Cmac.Stream.bytesAt_append s₃.mem (State.addr D) (16 * (n / 16)) (n - 16 * (n / 16))
      rw [show 16 * (n / 16) + (n - 16 * (n / 16)) = n by omega] at e
      have e₀ := Proof.Cmac.Stream.bytesAt_append s.mem (State.addr D) (16 * (n / 16)) (n - 16 * (n / 16))
      rw [show 16 * (n / 16) + (n - 16 * (n / 16)) = n by omega] at e₀
      have rest : bytesAt s₃.mem (State.addr D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) =
          bytesAt s.mem (State.addr D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)) := by
        rw [← mem₂]
        refine bytesAt_frame f₃ (fun r hr => ?_) (by have := hD.buf.lt; omega)
        have hsub : Region.Sub ⟨State.addr D + BitVec.ofNat 64 (16 * (n / 16)), n - 16 * (n / 16)⟩
            ⟨State.addr D, n⟩ := Offset.sub_base _ (by omega)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ((hD.buf.w.sub_left hsub).sub_right (Lay.wSub (by decide)))
        · exact (Offset.base_disjoint (State.addr D) (e := 16 * (n / 16)) (n := n - 16 * (n / 16))
            (k := 16 * (n / 16)) (by omega) (by have := hD.buf.lt; omega)).symm
        · exact ((hD.buf.w.sub_left hsub).sub_right (Lay.wSub (by decide)))
        · exact (hD.buf.stk.sub_right hsub).symm.sub_right (below_blw sp)
      have hpa := ctrPart_append (Spec.Siv.ctxCiph s.mem (State.addr c) R) q
        (bytesAt s.mem (State.addr D) (16 * (n / 16)))
        (bytesAt s.mem (State.addr D + BitVec.ofNat 64 (16 * (n / 16))) (n - 16 * (n / 16)))
      rw [Proof.Cmac.bytesAt_length] at hpa
      rw [e, hc, rest, e₀, hpa, eK, mem₂]
      rfl
    · have := h₃.ctr
      rw [eC, mem₂, hcb] at this
      rw [this]
      exact hinc (n / 16) (by omega)

/-- The keystream block zeroed, and the arguments of the call in `ctrTail`. -/
theorem ctrTailArgs_ok {s₁ : State} (he₁ : Env c w sp R s₁) (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    WP isa (.block (zero16 ksOff ++ ctrArgs ++ [addI .r3 .r11 ksOff, .mov .r12 (imm 1)])) s₁ fun s₂ =>
      Env c w sp R s₂ ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₂.gpr r = s₁.gpr r) ∧
      s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr ∧ s₂.sp = s₁.sp ∧
      s₂.mem = Proof.Cmac.zero4 s₁.mem (State.addr w + BitVec.ofNat 64 ksOff) ∧
      Proof.AesGcm.Arm.CtrCall s₂ (c + BitVec.ofNat 32 272) (w + BitVec.ofNat 32 cbOff) (w + BitVec.ofNat 32 ksOff)
        (w + BitVec.ofNat 32 256) R 1 := by
  rw [List.append_assoc]
  refine zero16_ok L he₁ (d := ksOff) (by decide) fun s₂ g₂ m₂ rd₂ wr₂ sp₂ => ?_
  have he₂ : Env c w sp R s₂ := he₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₂ _ (by decide)) sp₂ rd₂ wr₂
  have eK := L.wA (d := ksOff) (by decide)
  refine WP.of_runBlock ⟨_, by simp only [ctrArgs, cbOff, csOff, ksOff, mov]; arun [he₂.r9, he₂.r10, he₂.r11], ?_⟩
  refine ⟨he₂.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl,
    fun r a b c' d e f => by simp only [gpr_setReg, a, b, c', d, e, f, ite_false, reduceCtorEq]; rw [g₂ r e],
    by simp [rd_setReg, rd₂], by simp [wr_setReg, wr₂], by simp [sp_setReg, sp₂], by simp [mem_setReg, m₂], ?_⟩
  refine ctrCall_of L ?_ hR ?_ ?_ ?_ ?_ ?_ ?_ (by rw [L.wN (by decide)]; have := L.ww; simp only [ksOff]; omega)
    ?_ ?_ ?_ ?_ ?_
  · exact he₂.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl
  · simp [gpr_setReg, he₂.r10]
  · simp [gpr_setReg, he₂.r9]
  · simp [gpr_setReg, he₂.r11]
  · simp [gpr_setReg, he₂.r11]
  · simp [gpr_setReg]
  · simp [gpr_setReg, he₂.r11]
  · rw [eK]; exact L.c_w' (by decide) (by decide)
  · rw [eK]; exact L.w_w (.inr (by decide)) (by decide) (by decide)
  · rw [eK]; exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · rw [eK]; exact L.stk_w' (by decide)
  · rw [eK]; simp only [wr_setReg]; exact he₂.perm.wC (by decide)

omit L in
/-- `ctrTail`'s first block: the number of last bytes in `r4`, and `Z` set
iff there are none. -/
theorem tailPre_ok {s : State} {n : Nat} (hn : n < 2 ^ 32) (h5 : s.gpr .r5 = BitVec.ofNat 32 n) :
    ∃ s₁, runBlock isa [.dp .and .r4 .r5 (imm 15), .cmp .r4 (imm 0)] s =
      some s₁ ∧ s₁.gpr .r4 = BitVec.ofNat 32 (n % 16) ∧ s₁.z = decide (n % 16 = 0) ∧
      (∀ r, r ≠ .r4 → s₁.gpr r = s.gpr r) ∧ Proof.AesGcm.Arm.Keeps s s₁ := by
  have hand := Proof.AesGcm.Arm.and15 (BitVec.ofNat 32 n)
  rw [Proof.AesGcm.Arm.toNat32 hn] at hand
  refine ⟨_, by arun [], ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, h5, imm, hand]
  · simp only [Proof.AesGcm.Arm.z_subFlags, gpr_setReg, Proof.AesGcm.Arm.gpr_subFlags, ite_true, ite_false,
      reduceCtorEq, h5, imm, hand]
    exact Proof.AesGcm.Arm.z_cmp (by omega) (by decide)
  · intro r a; simp [gpr_setReg, a]
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- The last bytes of the data, XORed with the keystream block of the counter
`Q + nb` that `ctrWhole` left. -/
theorem ctrTail_ok {s : State} (he : Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {D : BitVec 32} {n : Nat}
    (hD : Dat c w sp s D n) (hn : n < 2 ^ 32) (h6 : s.gpr .r6 = D) (h5 : s.gpr .r5 = BitVec.ofNat 32 n)
    {q x : List Byte} (hx : x.length = n)
    (hcb : Spec.Gcm.blockAt s.mem (State.addr w + BitVec.ofNat 64 cbOff) =
      Spec.Gcm.ofBytes (Spec.Siv.be128 (Spec.Siv.beNat q + n / 16)))
    (hd : bytesAt s.mem (State.addr D) n = ctrPart (Spec.Siv.ctxCiph s.mem (State.addr c) R) q x (16 * (n / 16))) :
    WP isa ctrTail s fun s' => Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .r4 → r ≠ .lr → s'.gpr r = s.gpr r) ∧ Frame (ctrR w sp D n) s.mem s'.mem ∧
      bytesAt s'.mem (State.addr D) n = ctrPart (Spec.Siv.ctxCiph s.mem (State.addr c) R) q x n := by
  obtain ⟨s₁, run₁, h4₁, hz, g₁, k₁⟩ := tailPre_ok hn h5
  have he₁ : Env c w sp R s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₁ _ (by decide)) k₁.sp k₁.rd k₁.wr
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  by_cases h0 : n % 16 = 0
  · refine WP.ite true (Proof.AesGcm.Arm.eval_eq' (by rw [hz]; simp [h0])) (fun _ => WP.block_nil ?_)
      (fun h => by cases h)
    refine ⟨he₁, k₁.rd, k₁.wr, fun r _ h4 _ => g₁ r h4, by rw [k₁.mem]; exact Frame.refl _ _, ?_⟩
    rw [k₁.mem, hd, show 16 * (n / 16) = n by omega]
  · refine WP.ite false (Proof.AesGcm.Arm.eval_eq' (by rw [hz]; simp [h0])) (fun h => by cases h) fun _ => ?_
    refine WP.seq (WP.mono (ctrTailArgs_ok L he₁ hR) fun s₂ ⟨he₂, g₂, rd₂, wr₂, sp₂, m₂, C⟩ => ?_)
    refine WP.seq (WP.mono (Proof.AesGcm.Arm.ctr_call C) fun s₃ h₃ => ?_)
    have he₃ := he₂.of_saved h₃.saved h₃.sp h₃.rd h₃.wr
    have hsp₂ : s₂.sp = sp := he₂.sp
    have hRb := rounds_le hR
    have hb : 16 * (n / 16) < n := by omega
    have eC := L.wA (d := cbOff) (by decide)
    have eK := L.wA (d := ksOff) (by decide)
    have eS := L.wA (d := 256) (by decide)
    have eCK := L.cA (d := 272) (by decide)
    have g₃ : ∀ r ∈ preserved, r ≠ .lr → s₃.gpr r = s₁.gpr r := fun r hr hlr => by
      have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [h₃.saved r hr hlr, g₂ r a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2 hlr]
    have h4₃ : s₃.gpr .r4 = BitVec.ofNat 32 (n % 16) := by rw [g₃ _ (by decide) (by decide), h4₁]
    have h5₃ : s₃.gpr .r5 = BitVec.ofNat 32 n := by rw [g₃ _ (by decide) (by decide), g₁ _ (by decide), h5]
    have h6₃ : s₃.gpr .r6 = D := by rw [g₃ _ (by decide) (by decide), g₁ _ (by decide), h6]
    -- The keystream block.
    have hdata : (⟨State.addr D, n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 ksOff, 32⟩ :=
      hD.buf.w.sub_right (Lay.wSub (by decide))
    have f₂ : Frame [⟨State.addr w + BitVec.ofNat 64 ksOff, 16⟩] s.mem s₂.mem := by
      rw [m₂, k₁.mem]; exact Proof.Cmac.frame_store4 _ _ _ _ _
    have cb₂ : Spec.Gcm.blockAt s₂.mem (State.addr w + BitVec.ofNat 64 cbOff) =
        Spec.Gcm.ofBytes (Spec.Siv.be128 (Spec.Siv.beNat q + n / 16)) := by
      rw [Spec.Gcm.blockAt, bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide))
        (by decide), ← Spec.Gcm.blockAt, hcb]
    have sch₂ : bytesAt s₂.mem (State.addr c + BitVec.ofNat 64 272) (16 * (R + 1)) =
        bytesAt s.mem (State.addr c + BitVec.ofNat 64 272) (16 * (R + 1)) :=
      bytesAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.c_w' (by omega) (by decide)) (by omega)
    have hks : bytesAt s₃.mem (State.addr w + BitVec.ofNat 64 ksOff) 16 =
        Proof.Siv.ksBlock (Spec.Siv.ctxCiph s.mem (State.addr c) R) q (n / 16) := by
      have hx₃ := Proof.AesCcm.ctr32_bytes (m := s₂.mem) (m' := s₃.mem) (C := State.addr (w + BitVec.ofNat 32 cbOff))
        (D := State.addr (w + BitVec.ofNat 32 ksOff)) (nb := 1) h₃.out
      rw [Nat.mul_one, eK, eC, m₂, Proof.Cmac.zero4_bytes, ← m₂, cb₂, xorKs_zeros, eCK, sch₂,
        Proof.Cmac.aesWith_bytes _ _ (length_be128 _)] at hx₃
      rw [hx₃]; rfl
    -- The arguments of the XOR.
    have eD := hD.buf.addr (j := 16 * (n / 16)) hb
    obtain ⟨s₄, run₄, a1₄, a2₄, a3₄, g₄, k₄⟩ : ∃ s₄, runBlock isa [addI .r1 .r11 ksOff, .dp .sub .r2 .r5 (.reg .r4),
        .dp .add .r2 .r2 (.reg .r6), mov .r3 .r4] s₃ = some s₄ ∧
        s₄.gpr .r1 = w + BitVec.ofNat 32 ksOff ∧ s₄.gpr .r2 = D + BitVec.ofNat 32 (16 * (n / 16)) ∧
        s₄.gpr .r3 = BitVec.ofNat 32 (n % 16) ∧
        (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s₄.gpr r = s₃.gpr r) ∧ Proof.AesGcm.Arm.Keeps s₃ s₄ := by
      have hsub : BitVec.ofNat 32 n - BitVec.ofNat 32 (n % 16) = BitVec.ofNat 32 (16 * (n / 16)) := by
        rw [Proof.AesGcm.Arm.ofNat_sub32 (Nat.mod_le _ _) hn]; congr 1; omega
      refine ⟨_, by simp only [ksOff, mov]; arun [he₃.r11], ?_, ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, he₃.r11]
      · simp [gpr_setReg, h4₃, h5₃, h6₃, hsub, BitVec.add_comm]
      · simp [gpr_setReg, h4₃]
      · intro r a b c'; simp [gpr_setReg, a, b, c']
      · exact ⟨rfl, rfl, rfl, rfl⟩
    refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
    have hT := hD.buf.sub (j := 16 * (n / 16)) (k := n % 16) (by omega) (by omega)
    have wr₄ : s₄.wr = s.wr := by rw [k₄.wr, h₃.wr, wr₂, k₁.wr]
    have rd₄ : s₄.rd = s.rd := by rw [k₄.rd, h₃.rd, rd₂, k₁.rd]
    have lp : Proof.AesGcm.Arm.LoopPre s₄ (w + BitVec.ofNat 32 ksOff) (D + BitVec.ofNat 32 (16 * (n / 16))) (n % 16) := by
      refine ⟨a1₄, a2₄, a3₄, by omega, by omega, by rw [L.wN (by decide)]; have := L.ww; simp only [ksOff]; omega,
        hT.fit, ?_, ?_, ?_⟩
      · rw [eK, rd₄, wr₄]; exact Proof.AesGcm.Arm.covers_left (he.perm.wC (by simp only [ksOff]; omega))
      · rw [wr₄, eD]; exact Proof.AesGcm.Arm.covers_off hD.wr (by omega) hD.buf.lt
      · rw [eK]; exact (hT.w.sub_right (Lay.wSub (by simp only [ksOff]; omega))).symm
    refine WP.mono (Proof.AesGcm.Arm.xorLoop_ok s₄ lp) fun s₅ ⟨hm₅, lo⟩ => ?_
    rw [eK, eD] at hm₅
    have hxl : (Proof.AesGcm.Arm.xorBytes s₄.mem (State.addr D + BitVec.ofNat 64 (16 * (n / 16)))
        (State.addr w + BitVec.ofNat 64 ksOff) (n % 16)).length = n % 16 := Proof.AesGcm.Arm.length_xorBytes _ _ _ _
    -- What was written before the XOR.
    have f₂₃ : Frame [⟨State.addr w + BitVec.ofNat 64 ksOff, 32⟩, scrR w, blw sp] s₂.mem s₃.mem := by
      have fc := h₃.frame
      rw [hsp₂, eC, eK, eS] at fc
      exact fc.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
        · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
        · exact ⟨scrR w, by simp, Region.sub_prefix (by decide)⟩
        · exact ⟨blw sp, by simp, below_blw sp⟩
    have f₀₄ : Frame [⟨State.addr w + BitVec.ofNat 64 ksOff, 32⟩, scrR w, blw sp] s.mem s₄.mem := by
      rw [k₄.mem]
      exact (f₂.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩).trans f₂₃
    have fw : Frame [⟨State.addr D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩] s₄.mem s₅.mem := by
      rw [hm₅]; exact writeBytes_frame _ _ _ (by rw [hxl]; exact Region.contains_self _ _)
    refine ⟨he₃.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;>
          rw [lo.other _ (by decide) (by decide) (by decide) (by decide) (by decide),
            g₄ _ (by decide) (by decide) (by decide)]) (lo.sp.trans k₄.sp) (lo.rd.trans k₄.rd) (lo.wr.trans k₄.wr),
      by rw [lo.rd, rd₄], by rw [lo.wr, wr₄], fun r hr h4 hlr => ?_, ?_, ?_⟩
    · have a : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [lo.other r a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2, g₄ r a.2.1 a.2.2.1 a.2.2.2.1, g₃ r hr hlr, g₁ r h4]
    · refine (f₀₄.sub fun r hr => ?_).trans (fw.sub fun r hr => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        exact ⟨⟨State.addr D, n⟩, by simp, Offset.sub_base _ (by omega)⟩
    · have hc : ∀ y, (Spec.Siv.ctxCiph s.mem (State.addr c) R y).length = 16 :=
        fun y => Proof.Cmac.aesWith_length _ _ y
      have d₄ : bytesAt s₄.mem (State.addr D) x.length = ctrPart (Spec.Siv.ctxCiph s.mem (State.addr c) R) q x
          (16 * (n / 16)) := by
        rw [hx, bytesAt_frame f₀₄ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact hdata
          · exact hD.buf.w.sub_right (Lay.wSub (by decide))
          · exact hD.buf.stk.symm) (by have := hD.buf.lt; omega), hd]
      have st := ctrPart_step (Spec.Siv.ctxCiph s.mem (State.addr c) R) hc q x s₄.mem (State.addr D)
        (i := n / 16) (n := n % 16) (by have := hD.buf.lt; omega) (by omega) (by omega) d₄
      have xb : Proof.AesGcm.Arm.xorBytes s₄.mem (State.addr D + BitVec.ofNat 64 (16 * (n / 16)))
          (State.addr w + BitVec.ofNat 64 ksOff) (n % 16) =
          Spec.Cmac.xor (bytesAt s₄.mem (State.addr D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16))
            ((Proof.Siv.ksBlock (Spec.Siv.ctxCiph s.mem (State.addr c) R) q (n / 16)).take (n % 16)) := by
        rw [Proof.AesGcm.Arm.xorBytes, Proof.AesCcm.bytesAt_prefix s₄.mem (State.addr w + BitVec.ofNat 64 ksOff)
          (show n % 16 ≤ 16 by omega), k₄.mem, hks]
        rfl
      rw [hx] at st
      rw [hm₅, xb, st, show 16 * (n / 16) + n % 16 = n by omega]

/-- CTR's first block: the counter `Q` at `W + 96`, and the data's address
and length in `r6` and `r5`. -/
theorem ctrPre_ok {s : State} (he : Env c w sp R s) {D : BitVec 32} {n : Nat}
    (hD : Dat c w sp s D n) (hfit : sp.toNat + 12 ≤ 2 ^ 32)
    (hA : Covers [⟨State.addr sp, 12⟩] (s.rd ++ s.wr)) (hAw : (⟨State.addr sp, 12⟩ : Region).Disjoint ⟨State.addr w, 2576⟩)
    (hm0 : s.mem.readW (State.addr sp) 32 = D)
    (hm1 : s.mem.readW (State.addr sp + BitVec.ofNat 64 4) 32 = BitVec.ofNat 32 n) :
    WP isa (.block (counter 0 ++ ([.ldrSp .r6 0, .ldrSp .r5 4] : List Instr))) s fun s₃ => Env c w sp R s₃ ∧ Dat c w sp s₃ D n ∧
      s₃.gpr .r6 = D ∧ s₃.gpr .r5 = BitVec.ofNat 32 n ∧
      (∀ r, r ≠ .r0 → r ≠ .r5 → r ≠ .r6 → s₃.gpr r = s.gpr r) ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 cbOff, 16⟩] s.mem s₃.mem ∧
      bytesAt s₃.mem (State.addr w + BitVec.ofNat 64 cbOff) 16 = Spec.Siv.counter (bytesAt s.mem (State.addr w) 16) := by
  obtain ⟨s₁, run₁, hq₁, f₁, g₁, rd₁, wr₁, sp₁⟩ := counter_ok L he
  have he₁ : Env c w sp R s₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₁ _ (by decide)) sp₁ rd₁ wr₁
  have hsp₁ : s₁.sp = sp := he₁.sp
  have dA : ∀ {d : Nat}, d + 4 ≤ 12 → ∀ r ∈ [(⟨State.addr w + BitVec.ofNat 64 cbOff, 16⟩ : Region)],
      (⟨State.addr sp + BitVec.ofNat 64 d, 4⟩ : Region).Disjoint r := fun hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hAw.sub_left (Offset.sub_base _ hd)).sub_right (Lay.wSub (by decide))
  have a0 : State.addr (s₁.sp + BitVec.ofNat 32 0) = State.addr sp + BitVec.ofNat 64 0 := by
    rw [hsp₁]; exact addr_add (by omega)
  have a4 : State.addr (sp + BitVec.ofNat 32 4) = State.addr sp + BitVec.ofNat 64 4 := addr_add (by omega)
  have v0 : s₁.mem.readW (State.addr sp + BitVec.ofNat 64 0) 32 = D := by
    rw [f₁.readW (Region.contains_self _ _) (dA (d := 0) (by decide)) (by decide), BitVec.add_zero, hm0]
  have v4 : s₁.mem.readW (State.addr sp + BitVec.ofNat 64 4) 32 = BitVec.ofNat 32 n := by
    rw [f₁.readW (Region.contains_self _ _) (dA (d := 4) (by decide)) (by decide), hm1]
  have i0 : InRegions (s₁.rd ++ s₁.wr) (State.addr sp + BitVec.ofNat 64 0) 4 := by
    rw [rd₁, wr₁]; exact Proof.AesGcm.Arm.in_off hA (by decide) (by decide)
  have i4 : InRegions (s₁.rd ++ s₁.wr) (State.addr sp + BitVec.ofNat 64 4) 4 := by
    rw [rd₁, wr₁]; exact Proof.AesGcm.Arm.in_off hA (by decide) (by decide)
  refine WP.block_append_iff.mpr (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine wp_ldrSp (by decide) a0 i0 fun s₂ u₂ => ?_
  refine wp_ldrSp (a := State.addr sp + BitVec.ofNat 64 4) (by decide) (by rw [u₂.sp, hsp₁]; exact a4)
    (by rw [u₂.rd, u₂.wr]; exact i4) fun s₃ u₃ =>
    WP.block_nil ?_
  have he₃ : Env c w sp R s₃ := he₁.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> rw [u₃.other _ (by decide), u₂.other _ (by decide)])
    (by rw [u₃.sp, u₂.sp]) (by rw [u₃.rd, u₂.rd]) (by rw [u₃.wr, u₂.wr])
  have h6₃ : s₃.gpr .r6 = D := by rw [u₃.other _ (by decide), u₂.gpr, v0]
  have h5₃ : s₃.gpr .r5 = BitVec.ofNat 32 n := by rw [u₃.gpr, u₂.mem, v4]
  have m₃ : s₃.mem = s₁.mem := by rw [u₃.mem, u₂.mem]
  have hD₃ : Dat c w sp s₃ D n := hD.of_eq (by rw [u₃.rd, u₂.rd, rd₁]) (by rw [u₃.wr, u₂.wr, wr₁])
  exact ⟨he₃, hD₃, h6₃, h5₃, fun r h0 h5 h6 => by rw [u₃.other r h5, u₂.other r h6, g₁ r h0],
    by rw [u₃.rd, u₂.rd, rd₁], by rw [u₃.wr, u₂.wr, wr₁], by rw [m₃]; exact f₁, by rw [m₃]; exact hq₁⟩

/-- `ctr 0`: the data (`n` bytes at `D`, its address and length at `sp` and
`sp + 4`) XORed with CTR's keystream from the IV at `W` with two bits cleared. -/
theorem ctr_ok {s : State} (he : Env c w sp R s) (hR : R = 10 ∨ R = 12 ∨ R = 14) {D : BitVec 32} {n : Nat}
    (hD : Dat c w sp s D n) (hn : n < 2 ^ 32) (hfit : sp.toNat + 12 ≤ 2 ^ 32)
    (hA : Covers [⟨State.addr sp, 12⟩] (s.rd ++ s.wr)) (hAw : (⟨State.addr sp, 12⟩ : Region).Disjoint ⟨State.addr w, 2576⟩)
    (hm0 : s.mem.readW (State.addr sp) 32 = D)
    (hm1 : s.mem.readW (State.addr sp + BitVec.ofNat 64 4) 32 = BitVec.ofNat 32 n) :
    WP isa (ctr 0) s fun s' => Env c w sp R s' ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ preserved, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      s'.gpr .r6 = D ∧ s'.gpr .r5 = BitVec.ofNat 32 n ∧
      Frame (ctrR w sp D n) s.mem s'.mem ∧
      bytesAt s'.mem (State.addr D) n =
        Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem (State.addr c) R) (Spec.Siv.counter (bytesAt s.mem (State.addr w) 16))
          (bytesAt s.mem (State.addr D) n) := by
  rw [ctr]
  refine WP.seq (WP.mono (ctrPre_ok L he hD hfit hA hAw hm0 hm1)
    fun s₃ ⟨he₃, hD₃, h6₃, h5₃, g₃, rd₃, wr₃, f₁, hq₃⟩ => ?_)
  -- The bounds of the counter.
  have hlow := counter_low (bytesAt s.mem (State.addr w) 16)
  refine WP.seq (WP.mono (ctrWhole_ok L he₃ hR hD₃ hn h6₃ h5₃
    (q := Spec.Siv.counter (bytesAt s.mem (State.addr w) 16)) hq₃ (by omega))
    fun s₄ ⟨he₄, rd₄, wr₄, g₄, f₄, d₄, cb₄⟩ => ?_)
  have hRb := rounds_le hR
  have dcR : ∀ r ∈ ctrR w sp D n, (⟨State.addr c, 512⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.c0_w' (by decide) (by decide)
    · exact L.c0_w' (by decide) (by decide)
    · exact L.stk_c.symm
    · exact hD.c
  have k₄ : Spec.Siv.ctxCiph s₄.mem (State.addr c) R = Spec.Siv.ctxCiph s₃.mem (State.addr c) R :=
    ctxCiph_frame f₄ dcR hRb
  have h6₄ : s₄.gpr .r6 = D := by rw [g₄ _ (by decide) (by decide), h6₃]
  have h5₄ : s₄.gpr .r5 = BitVec.ofNat 32 n := by rw [g₄ _ (by decide) (by decide), h5₃]
  refine WP.mono (ctrTail_ok L he₄ hR (hD₃.of_eq rd₄ wr₄) hn h6₄ h5₄ (x := bytesAt s₃.mem (State.addr D) n)
    (Proof.Cmac.bytesAt_length _ _ _) cb₄ (by rw [k₄]; exact d₄)) fun s₅ ⟨he₅, rd₅, wr₅, g₅, f₅, d₅⟩ => ?_
  have f₀₁ : Frame (ctrR w sp D n) s.mem s₃.mem := by
    exact f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self .., Offset.sub _ (by decide) (by decide)⟩
  refine ⟨he₅, by rw [rd₅, rd₄, rd₃], by rw [wr₅, wr₄, wr₃],
    fun r hr h4 h5 h6 hlr => ?_, by rw [g₅ _ (by decide) (by decide) (by decide), h6₄],
    by rw [g₅ _ (by decide) (by decide) (by decide), h5₄], f₀₁.trans (f₄.trans f₅), ?_⟩
  · have h0 : r ≠ .r0 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [g₅ r hr h4 hlr, g₄ r hr hlr, g₃ r h0 h5 h6]
  · have c₃ : Spec.Siv.ctxCiph s₃.mem (State.addr c) R = Spec.Siv.ctxCiph s.mem (State.addr c) R :=
      ctxCiph_frame f₀₁ dcR hRb
    have b₃ : bytesAt s₃.mem (State.addr D) n = bytesAt s.mem (State.addr D) n := by
      exact bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hD.buf.w.sub_right (Lay.wSub (by decide)))
        (by have := hD.buf.lt; omega)
    rw [d₅, k₄, c₃, b₃]
    exact ctrPart_all (Spec.Siv.ctxCiph s.mem (State.addr c) R) (fun y => Proof.Cmac.aesWith_length _ _ y) _ _
      (by rw [Proof.Cmac.bytesAt_length])

end

end VG.Proof.AesSiv.Arm

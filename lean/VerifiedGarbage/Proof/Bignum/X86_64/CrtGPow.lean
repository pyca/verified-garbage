import VerifiedGarbage.Proof.Bignum.X86_64.PubExp
import VerifiedGarbage.Impl.Rsa.X86_64.Crt

/-!
# `vg_rsa_private_crt` on x86-64: `G = 2^E mod n`

`gPow`: `K = ⌈w / w_X⌉` (`kLoop_ok`), `D = 64 ((K + 1) w_X - w)` into
slot `sD` (`gHead_ok`), its top bit into `sCnt`, `Y := R mod n`, then a
squaring and a doubling under each bit of `D` from the top (`gBit_ok`,
`gBits_ok`): `Y ≡ 2^D R = 2^(64 w_X (K + 1))` (`gPow_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64 (Crt.ws Crt.sD Crt.gPow)

/-- `K = ⌈w / w_X⌉`: `w ≤ K w_X < w + w_X`. -/
theorem kBounds {w wx : Nat} (hwx : 1 ≤ wx) :
    w ≤ (w + wx - 1) / wx * wx ∧ (w + wx - 1) / wx * wx < w + wx := by
  have h1 := Nat.div_add_mod (w + wx - 1) wx
  have h2 := Nat.mod_lt (w + wx - 1) (show 0 < wx by omega)
  rw [Nat.mul_comm] at h1
  omega

/-- The loop `rcx += w_X` while `rcx < w`, from `rcx = 0`: `rcx = K w_X`. -/
theorem kLoop_ok {s : State} {w wx : Nat} (hwx : 1 ≤ wx) (hw : 1 ≤ w) (hw' : w + wx < 2 ^ 32)
    (hax : s.gpr .rax = BitVec.ofNat 64 wx) (h12 : s.gpr .r12 = BitVec.ofNat 64 w)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 0) :
    WP isa (.loop (.block [.alu .add .rcx (.reg .rax), .alu .cmp .rcx (.reg .r12)]) .b) s fun t =>
      t.gpr .rcx = BitVec.ofNat 64 ((w + wx - 1) / wx * wx) ∧ t.mem = s.mem ∧ Keep [.rcx] s t := by
  generalize hK : (w + wx - 1) / wx = K
  obtain ⟨hK1, hK2⟩ := kBounds (w := w) hwx
  rw [hK] at hK1 hK2
  have hK0 : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · rw [h, Nat.zero_mul] at hK1; omega
    · exact h
  refine WP.loop (M := isa) (fun n t => ∃ k, n = K - k ∧ k < K ∧ t.gpr .rcx = BitVec.ofNat 64 (k * wx) ∧
      t.mem = s.mem ∧ Keep [.rcx] s t) ?_ _ s ⟨0, rfl, hK0, by rw [hcx, Nat.zero_mul], rfl, Keep.refl _ _⟩
  rintro n t ⟨k, rfl, hk, hcx', hm, k₀⟩
  have hle : (k + 1) * wx ≤ K * wx := Nat.mul_le_mul_right _ hk
  have hle' : k * wx + wx ≤ K * wx := by rw [← Nat.succ_mul]; exact hle
  refine WP.mono (WP.keep [.rcx] (Q := fun t' => t'.gpr .rcx = BitVec.ofNat 64 ((k + 1) * wx) ∧
      t'.cf = some (decide ((k + 1) * wx < w)) ∧ t'.mem = t.mem) (by
    xrun [hcx', (k₀.gpr (by decide)).trans hax, (k₀.gpr (by decide)).trans h12, ← BitVec.ofNat_add]
    rw [Nat.succ_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    exact ⟨rfl, rfl⟩) rfl) fun t' ⟨⟨hcx'', hcf, hm'⟩, k'⟩ => ?_
  by_cases hc : (k + 1) * wx < w
  · refine .inr ⟨by simp [eval, hcf, hc], K - (k + 1), by omega, k + 1, rfl, ?_, hcx'', hm'.trans hm,
      (k₀.trans k').mono (by decide)⟩
    rcases Nat.lt_or_ge (k + 1) K with h | h
    · exact h
    · have := Nat.mul_le_mul_right wx h; omega
  · have hkK : k + 1 = K := by
      rcases Nat.lt_or_ge (k + 1) K with h | h
      · have := Nat.mul_le_mul_right wx (show k + 2 ≤ K by omega)
        rw [Nat.succ_mul (k + 1)] at this; omega
      · omega
    exact .inl ⟨by simp [eval, hcf, hc], by rw [hcx'', hkK], hm'.trans hm, (k₀.trans k').mono (by decide)⟩

/-- `D = 64 ((K + 1) w_X - w)`. -/
def gD (w wx : Nat) : Nat := 64 * ((w + wx - 1) / wx * wx + wx - w)

/-- `gPow`'s first steps: `D` into slot `sD` and `rax`. -/
def gHead (slotWs : Nat) : List (Prog isa) := [
  .block [.mov .rax (.mem (hdr slotWs)), .mov .rax (.mem (Crt.ws .rax sW)), .mov .r12 (.mem (hdr sW)),
    .mov32 .rcx (.imm 0)],
  .loop (.block [.alu .add .rcx (.reg .rax), .alu .cmp .rcx (.reg .r12)]) .b,
  .block [.alu .add .rcx (.reg .rax), .alu .sub .rcx (.reg .r12), .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx),
    .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .rcx),
    .store (hdr Crt.sD) .rcx, .mov .rax (.reg .rcx)]]

/-- The steps of `D`. -/
theorem gHead_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw30 : w < 2 ^ 30) {sl : Nat} (hsl' : sl < 32) {Bx : Addr} {wx : Nat}
    (hX : word s.mem B (8 * sl) = Bx) (hXw : word s.mem Bx (8 * sW) = BitVec.ofNat 64 wx)
    (hXr : InRegions (s.rd ++ s.wr) (off Bx (8 * sW)) 8) (hwx : 1 ≤ wx) (hwx' : wx ≤ w) :
    WP isa (seqs (gHead sl)) s fun t => t.gpr .rax = BitVec.ofNat 64 (gD w wx) ∧
      t.mem = s.mem.writeW (off B (8 * Crt.sD)) (BitVec.ofNat 64 (gD w wx)) ∧ Keep [.rax, .rcx, .r12] s t := by
  have hs := hg.scr
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  refine WP.seq (WP.mono (WP.keep [.rax, .r12, .rcx] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 wx ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .rcx = BitVec.ofNat 64 0 ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, Crt.ws, hg.rdi, hdrOff, hl sl hsl', hX, hXr, hXw, hl sW (by decide), hg.hdr.hw]) rfl)
    fun t₁ ⟨⟨hax₁, h12₁, hcx₁, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (kLoop_ok hwx (by omega) (by omega) hax₁ h12₁ hcx₁) fun t₂ ⟨hcx₂, hm₂, k₂⟩ => ?_)
  obtain ⟨hK1, hK2⟩ := kBounds (w := w) hwx
  have hD : gD w wx = 64 * ((w + wx - 1) / wx * wx + wx - w) := rfl
  generalize (w + wx - 1) / wx * wx = a at hcx₂ hK1 hK2 hD
  have hsub : BitVec.ofNat 64 (a + wx) - BitVec.ofNat 64 w = BitVec.ofNat 64 (a + wx - w) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega),
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  have hdi₂ : t₂.gpr .rdi = B := ((k₁.trans k₂).gpr (by decide)).trans hg.rdi
  have hs₂ := hs.congr (k₁.trans k₂).2.2
  refine WP.mono (WP.keep [.rcx, .rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (gD w wx) ∧
      t.mem = s.mem.writeW (off B (8 * Crt.sD)) (BitVec.ofNat 64 (gD w wx))) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, hs₂.st (show 8 * Crt.sD + 8 ≤ Z by
      have := hdr_lt_slot w 8 (show Crt.sD < 32 by decide); omega), hcx₂, (k₂.gpr (by decide)).trans hax₁,
      (k₂.gpr (by decide)).trans h12₁, hm₂, hm₁, ← BitVec.ofNat_add, hsub]
    rw [hD]
    generalize a + wx - w = c
    refine ⟨congrArg (BitVec.ofNat 64) ?_,
      congrArg (fun v => s.mem.writeW (off B (8 * Crt.sD)) v) (congrArg (BitVec.ofNat 64) ?_)⟩ <;> omega) rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2, ((k₁.trans k₂).trans k).mono (by decide)⟩

/-! ## The bits of `D` -/

theorem and_pow_beq (D k : Nat) (hk : k < 64) :
    (BitVec.ofNat 64 D &&& BitVec.ofNat 64 (2 ^ k) == 0) = decide (D / 2 ^ k % 2 = 0) := by
  have e : BitVec.ofNat 64 (2 ^ k) = BitVec.twoPow 64 k := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, BitVec.toNat_twoPow]
  rw [e, BitVec.and_twoPow, BitVec.getLsbD_ofNat, Nat.testBit_eq_decide_div_mod_eq]
  by_cases h : D / 2 ^ k % 2 = 0
  · simp [h]
  · have h1 : D / 2 ^ k % 2 = 1 := by omega
    have h2 : BitVec.twoPow 64 k ≠ 0#64 := by
      intro h0
      have := congrArg BitVec.toNat h0
      rw [BitVec.toNat_twoPow_of_lt hk] at this
      exact absurd this (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k))
    simp [h1, hk, h2]

theorem div_bit (D k : Nat) : 2 * (D / 2 ^ (k + 1)) + D / 2 ^ k % 2 = D / 2 ^ k := by
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]; omega

/-- The loop's body: `Y := Y² R⁻¹`, doubled if the bit is set, and the
next bit. -/
def gBody (mul : Nat → Nat → Nat → Prog isa) : List (Prog isa) := [
  mul aY aY aY,
  .block [.mov .rax (.mem (hdr Crt.sD)), .alu .and .rax (.mem (hdr sCnt))],
  .ite .ne (double aN aAcc aTmp aY) (.block []),
  .block [.mov .rax (.mem (hdr sCnt)), .shift .shr .rax 1, .store (hdr sCnt) .rax, .alu .test .rax (.reg .rax)]]

theorem gPow_eq (mul : Nat → Nat → Nat → Prog isa) (slotWs : Nat) : Crt.gPow mul slotWs =
    gHead slotWs ++ [topBit, .block [.store (hdr sCnt) .rdx], mul aY aR2 aOne, .loop (seqs (gBody mul)) .ne] :=
  rfl

/-- What `gPow` changes. -/
def gRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2)), (8 * Crt.sD, 8),
    (8 * sCnt, 8)]

/-- After the top `j` of the `L + 1` bits of `D`, from `s₀`: `Y ≡ 2^⌊D / 2^(L + 1 - j)⌋ R`. -/
structure GInv (s₀ : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (N D L : Nat) (j : Nat) (t : State) :
    Prop where
  good : Good t B Z w minv
  n : wv t.mem B (slot w aN) w = N
  inv : ((word t.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0
  ylt : wv t.mem B (slot w aY) w < N
  y : wv t.mem B (slot w aY) w % N = 2 ^ (D / 2 ^ (L + 1 - j)) * 2 ^ (64 * w) % N
  d : word t.mem B (8 * Crt.sD) = BitVec.ofNat 64 D
  c : word t.mem B (8 * sCnt) = BitVec.ofNat 64 (2 ^ (L + 1 - j) / 2)
  frm : Frm B (gRanges w) s₀.mem t.mem
  keep : Keep mmRegs s₀ t

/-- Bit `L - j` of `D`. -/
theorem gBit_ok (M : Mont) {s₀ t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N D L : Nat}
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hR : Nat.Coprime (2 ^ (64 * w)) N) (hN0 : 0 < N)
    (hL : L < 63) {j : Nat} (hj : j < L + 1) (hI : GInv s₀ B Z w minv N D L j t) :
    WP isa (seqs (gBody M.mm)) t fun t' =>
      t'.zf = some (decide (j + 1 = L + 1)) ∧ GInv s₀ B Z w minv N D L (j + 1) t' := by
  have hn := hI.good.scr.nowrap
  have hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega
  have hc2 : 2 ^ (L + 1 - j) / 2 = 2 ^ (L - j) := by
    rw [show L + 1 - j = (L - j) + 1 by omega, Nat.pow_succ, Nat.mul_div_cancel _ (by decide)]
  have hpL : 2 ^ (L - j) < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
  -- `Y := Y²`.
  refine WP.seq (WP.mono (mmN_ok M (o := aY) (a := aY) (b := aY) hI.good hZ hw hw' (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hI.n hI.inv hI.ylt)
    fun t₁ ⟨hg₁, hn₁, hinv₁, hlt₁, hm₁, ha₁, k₁⟩ => ?_)
  have hY₁ : wv t₁.mem B (slot w aY) w % N = 2 ^ (2 * (D / 2 ^ (L + 1 - j))) * 2 ^ (64 * w) % N :=
    VG.Proof.Bignum.mont_sq hR hI.y hm₁
  have hd₁ : word t₁.mem B (8 * Crt.sD) = BitVec.ofNat 64 D := by rw [ha₁.hslot (by decide)]; exact hI.d
  have hc₁ : word t₁.mem B (8 * sCnt) = BitVec.ofNat 64 (2 ^ (L - j)) := by
    rw [ha₁.hslot (by decide), hI.c, hc2]
  have hl₁ : ∀ i < 32, InRegions (t₁.rd ++ t₁.wr) (off B (8 * i)) 8 := fun i hi =>
    hg₁.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  -- The bit, into ZF.
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t₂ => t₂.zf = some (decide (D / 2 ^ (L - j) % 2 = 0)) ∧
      t₂.mem = t₁.mem) (by
    xrun [State.ea, hdr, hg₁.rdi, hdrOff, hl₁ Crt.sD (by decide), hl₁ sCnt (by decide), hd₁, hc₁,
      and_pow_beq D (L - j) (by omega)]) rfl) fun t₂ ⟨⟨hz₂, hm₂⟩, k₂⟩ => ?_)
  have hg₂ : Good t₂ B Z w minv := ⟨hg₁.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hg₁.rdi, hm₂ ▸ hg₁.hdr⟩
  -- Doubled if it is set.
  have hdbl : WP isa (.ite .ne (double aN aAcc aTmp aY) (.block [])) t₂ fun t₃ => Good t₃ B Z w minv ∧
      wv t₃.mem B (slot w aY) w < N ∧
      wv t₃.mem B (slot w aY) w % N =
        2 ^ (2 * (D / 2 ^ (L + 1 - j)) + D / 2 ^ (L - j) % 2) * 2 ^ (64 * w) % N ∧
      Arrays B w [aAcc, aTmp, aY] t₂.mem t₃.mem ∧ Keep mmRegs t₂ t₃ := by
    by_cases hbit : D / 2 ^ (L - j) % 2 = 0
    · refine WP.ite false (by simp [eval, hz₂, hbit]) (by simp) (fun _ => WP.block_nil ⟨hg₂, ?_, ?_,
        fun _ _ => rfl, Keep.refl _ _⟩)
      · rw [hm₂]; exact hlt₁
      · rw [hm₂, hY₁, hbit]; rfl
    · refine WP.ite true (by simp [eval, hz₂, hbit]) (fun _ => ?_) (by simp)
      refine WP.mono (double_ok hg₂.scr hg₂.rdi hg₂.hdr hZ hw hw' (mo := aN) (acc := aAcc) (tmp := aTmp)
        (o := aY) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by rw [hm₂, hn₁]; exact hlt₁)) fun t₃ ⟨hv₃, ha₃, k₃⟩ => ?_
      rw [hm₂, hn₁] at hv₃
      refine ⟨⟨hg₂.scr.congr k₃.2.2, (k₃.gpr (by decide)).trans hg₂.rdi, ha₃.hdr hg₂.hdr⟩,
        by rw [hv₃]; exact Nat.mod_lt _ hN0, ?_, ha₃, k₃⟩
      rw [hv₃, Nat.mod_mod, Nat.mul_mod 2 (wv t₁.mem B (slot w aY) w) N, hY₁, ← Nat.mul_mod,
        show D / 2 ^ (L - j) % 2 = 1 by omega, Nat.pow_succ, Nat.mul_comm _ 2, Nat.mul_assoc]
  refine WP.seq (WP.mono hdbl fun t₃ ⟨hg₃, hlt₃, hY₃, ha₃, k₃⟩ => ?_)
  -- The next bit.
  have hc₃ : word t₃.mem B (8 * sCnt) = BitVec.ofNat 64 (2 ^ (L - j)) := by
    rw [ha₃.hslot (by decide), hm₂]; exact hc₁
  have hl₃ : ∀ i < 32, InRegions (t₃.rd ++ t₃.wr) (off B (8 * i)) 8 := fun i hi =>
    hg₃.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have hs₃ : ∀ i < 32, InRegions t₃.wr (off B (8 * i)) 8 := fun i hi =>
    hg₃.scr.st (by have := hdr_lt_slot w 8 hi; omega)
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t₃.mem.writeW (off B (8 * sCnt))
      (BitVec.ofNat 64 (2 ^ (L - j) / 2)) ∧ t'.zf = some (decide (2 ^ (L - j) / 2 = 0))) (by
    xrun [State.ea, hdr, hg₃.rdi, hdrOff, hl₃ sCnt (by decide), hs₃ sCnt (by decide), hc₃, shr1_ofNat _ hpL,
      BitVec.and_self, ofNat64_beq_zero (show 2 ^ (L - j) / 2 < 2 ^ 64 by omega)]) rfl) fun t' ⟨⟨hm', hz'⟩, k'⟩ => ?_
  have o' : Outside B (8 * sCnt) 8 t₃.mem t'.mem := by
    rw [hm']; exact writeW_outside _ _ _ (by unfold sCnt sFn; omega)
  have hkeep : ∀ i < 8, i ≠ aAcc → i ≠ aTmp → i ≠ aY → wv t'.mem B (slot w i) w = wv t₁.mem B (slot w i) w :=
    fun i hi h1 h2 h3 => by
      rw [hm', hdrStore_wv _ _ _ (by decide) hi hn', ha₃.wv_of_not_mem hi (by simp [h1, h2, h3]) hn', hm₂]
  have hY' : wv t'.mem B (slot w aY) w = wv t₃.mem B (slot w aY) w := by
    rw [hm', hdrStore_wv _ _ _ (by decide) (by decide) hn']
  have hle : L + 1 - (j + 1) = L - j := by omega
  refine ⟨?_, ⟨⟨hg₃.scr.congr k'.2.2, (k'.gpr (by decide)).trans hg₃.rdi, by
      rw [hm']; exact Hdr.store hg₃.hdr (by decide) (by decide) _⟩,
    by rw [hkeep aN (by decide) (by decide) (by decide) (by decide)]; exact hn₁,
    by rw [hm', hdrStore_word _ _ _ (by decide) (by decide) hn',
      ha₃.word0_of_not_mem (by decide) (by decide) hn' (by omega), hm₂]; exact hinv₁,
    by rw [hY']; exact hlt₃,
    by rw [hY', hY₃, hle, show 2 * (D / 2 ^ (L + 1 - j)) + D / 2 ^ (L - j) % 2 = D / 2 ^ (L - j) by
      rw [show L + 1 - j = L - j + 1 by omega]; exact div_bit D (L - j)],
    by rw [hm', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), ha₃.hslot (by decide), hm₂]; exact hd₁,
    by rw [hm', word_writeW_self, hle],
    ?_, (((hI.keep.trans k₁).trans k₂).trans (k₃.trans k')).mono (by decide)⟩⟩
  · rw [hz']; congr 1; refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => ?_⟩
    · rcases Nat.eq_zero_or_pos (L - j) with h0 | h0
      · omega
      · rw [show L - j = (L - j - 1) + 1 by omega, Nat.pow_succ, Nat.mul_div_cancel _ (by decide)] at h
        exact absurd h (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _))
    · rw [show L - j = 0 by omega]; rfl
  · exact (((hI.frm.trans (Frm.of_arrays ha₁ (by simp [gRanges]))).trans
      (by rw [hm₂]; exact Frm.refl _ _ _)).trans (Frm.of_arrays ha₃ (by simp [gRanges]))).trans
      (Frm.of_outside o' (by simp [gRanges]))

/-- The `L + 1` bits of `D`: `Y ≡ 2^D R`. -/
theorem gBits_ok (M : Mont) {s₀ t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N D L : Nat}
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hR : Nat.Coprime (2 ^ (64 * w)) N) (hN0 : 0 < N)
    (hL : L < 63) (h0 : GInv s₀ B Z w minv N D L 0 t) :
    WP isa (.loop (seqs (gBody M.mm)) .ne) t (GInv s₀ B Z w minv N D L (L + 1)) :=
  wp_upto (a := 0) (N := L + 1) (by omega) (GInv s₀ B Z w minv N D L)
    (fun _ _ hj _ hI => gBit_ok M hZ hw hw' hR hN0 hL hj hI) (fun _ h => h) h0

/-! ## `G` -/

theorem gD_bounds {w wx : Nat} (hwx : 1 ≤ wx) (hwx' : wx ≤ w) (hw30 : w < 2 ^ 30) :
    0 < gD w wx ∧ gD w wx < 2 ^ 62 ∧
      gD w wx + 64 * w = 64 * wx * ((w + wx - 1) / wx + 1) := by
  obtain ⟨hK1, hK2⟩ := kBounds (w := w) hwx
  unfold gD
  rw [Nat.mul_succ, Nat.mul_assoc 64 wx, Nat.mul_comm wx]
  omega

/-- `gPow`: `[aY] ≡ 2^(64 w_X (K + 1)) (mod N)` for `K = ⌈w / w_X⌉`, with `w_X` in
the header of the workspace whose base is in slot `sl`. -/
theorem gPow_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw30 : w < 2 ^ 30)
    (hn : wv s.mem B (slot w aN) w = N)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hodd : N % 2 = 1) (hN1 : 1 < N)
    (hr2' : wv s.mem B (slot w aR2) w % N = 2 ^ (64 * w) * 2 ^ (64 * w) % N)
    (hone : wv s.mem B (slot w aOne) w = 1)
    {sl : Nat} (hsl' : sl < 32)
    {Bx : Addr} {wx : Nat} (hX : word s.mem B (8 * sl) = Bx)
    (hXw : word s.mem Bx (8 * sW) = BitVec.ofNat 64 wx)
    (hXr : InRegions (s.rd ++ s.wr) (off Bx (8 * sW)) 8) (hwx : 1 ≤ wx) (hwx' : wx ≤ w) :
    WP isa (seqs (Crt.gPow M.mm sl)) s fun t => Good t B Z w minv ∧
      wv t.mem B (slot w aY) w < N ∧
      wv t.mem B (slot w aY) w % N = 2 ^ (64 * wx * ((w + wx - 1) / wx + 1)) % N ∧
      Frm B [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2)),
        (8 * Crt.sD, 8), (8 * sCnt, 8)] s.mem t.mem ∧ Keep mmRegs s t := by
  have hw' : w < 2 ^ 31 := by omega
  have hs := hg.scr
  have hnw := hs.nowrap
  have hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega
  have hR : Nat.Coprime (2 ^ (64 * w)) N := VG.Proof.Bignum.coprime_pow2 hodd _
  have hN0 : 0 < N := by omega
  obtain ⟨hD0, hD1, hDE⟩ := gD_bounds hwx hwx' hw30
  rw [gPow_eq]
  refine wp_seqs_append (by simp [gHead]) (by simp) (WP.mono (gHead_ok hg hZ hw hw30 hsl' hX hXw hXr hwx hwx')
    fun t₁ ⟨hax₁, hm₁, k₁⟩ => ?_)
  generalize gD w wx = D at hD0 hD1 hDE hax₁ hm₁
  have hs₁ := hs.congr k₁.2.2
  have hdi₁ : t₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hg.rdi
  -- The top bit `L` of `D`.
  refine WP.seq (WP.mono (topBit_ok hax₁ hD0 (by omega)) fun t₂ ⟨hdx₂, _, hm₂, k₂⟩ => ?_)
  have hL : D.log2 < 62 := (Nat.log2_lt (by omega)).mpr hD1
  have hs₂ := hs₁.congr k₂.2.2
  have hdi₂ : t₂.gpr .rdi = B := (k₂.gpr (by decide)).trans hdi₁
  refine WP.seq (WP.mono (WP.keep [] (Q := fun t => t.mem = t₂.mem.writeW (off B (8 * sCnt))
      (BitVec.ofNat 64 (2 ^ D.log2))) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, hs₂.st (show 8 * sCnt + 8 ≤ Z by
      have := hdr_lt_slot w 8 (show sCnt < 32 by decide); omega), hdx₂]) rfl) fun t₃ ⟨hm₃, k₃⟩ => ?_)
  have hm₃' : t₃.mem = (s.mem.writeW (off B (8 * Crt.sD)) (BitVec.ofNat 64 D)).writeW (off B (8 * sCnt))
      (BitVec.ofNat 64 (2 ^ D.log2)) := by rw [hm₃, hm₂, hm₁]
  have hwv₃ : ∀ j < 8, wv t₃.mem B (slot w j) w = wv s.mem B (slot w j) w := fun j hj => by
    rw [hm₃', hdrStore_wv _ _ _ (by decide) hj hn', hdrStore_wv _ _ _ (by decide) hj hn']
  have hg₃ : Good t₃ B Z w minv := ⟨hs₂.congr k₃.2.2, (k₃.gpr (by decide)).trans hdi₂, by
    rw [hm₃']; exact Hdr.store (Hdr.store hg.hdr (by decide) (by decide) _) (by decide) (by decide) _⟩
  -- `Y := R`.
  refine WP.seq (WP.mono (mmN_ok M (N := N) (o := aY) (a := aR2) (b := aOne) hg₃ hZ hw hw' (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((hwv₃ aN (by decide)).trans hn)
    (by rw [hm₃', hdrStore_word _ _ _ (by decide) (by decide) hn', hdrStore_word _ _ _ (by decide) (by decide) hn'];
        exact hinv)
    (by rw [hwv₃ aOne (by decide), hone]; exact hN1))
    fun t₄ ⟨hg₄, hn₄, hinv₄, hlt₄, hm₄, ha₄, k₄⟩ => ?_)
  rw [hwv₃ aR2 (by decide), hwv₃ aOne (by decide), hone, Nat.mul_one] at hm₄
  have hY₄ : wv t₄.mem B (slot w aY) w % N = 2 ^ (D / 2 ^ (D.log2 + 1 - 0)) * 2 ^ (64 * w) % N := by
    rw [Nat.sub_zero, Nat.div_eq_of_lt Nat.lt_log2_self, Nat.pow_zero, Nat.one_mul]
    apply VG.Proof.Bignum.mont_cancel hR
    rw [hm₄, hr2']
  have hfr₄ : Frm B (gRanges w) s.mem t₄.mem := by
    have o1 := writeW_outside s.mem B (BitVec.ofNat 64 D) (d := 8 * Crt.sD) (by unfold Crt.sD sFn; omega)
    have o2 := writeW_outside (s.mem.writeW (off B (8 * Crt.sD)) (BitVec.ofNat 64 D)) B
      (BitVec.ofNat 64 (2 ^ D.log2)) (d := 8 * sCnt) (by unfold sCnt sFn; omega)
    rw [← hm₃'] at o2
    exact ((Frm.of_outside o1 (by simp [gRanges])).trans (Frm.of_outside o2 (by simp [gRanges]))).trans
      (Frm.of_arrays ha₄ (by simp [gRanges]))
  have h0 : GInv s B Z w minv N D D.log2 0 t₄ := ⟨hg₄, hn₄, hinv₄, hlt₄, hY₄,
    by rw [ha₄.hslot (by decide), hm₃', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self],
    by rw [ha₄.hslot (by decide), hm₃', word_writeW_self, Nat.sub_zero, Nat.pow_succ,
      Nat.mul_div_cancel _ (by decide)],
    hfr₄, (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
  -- The bits.
  refine WP.mono (gBits_ok M hZ hw hw' hR hN0 (by omega) h0) fun t hI => ⟨hI.good, hI.ylt, ?_, hI.frm, hI.keep⟩
  rw [hI.y, Nat.sub_self, Nat.pow_zero, Nat.div_one, ← Nat.pow_add, hDE]

end VG.Proof.Bignum.X86_64

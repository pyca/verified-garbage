import VerifiedGarbage.Proof.Rsa.X86_64.KeyReduce
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup

/-!
# `vg_rsa_check_key` on x86-64: the pieces of the checks

In the workspace at `B` (`Good`): `loadNum` loads a number (`loadNum_ok`),
`ltMask` and `eqOne` and their masks into `sMask` (`ltMask_ok`, `eqOne_ok`),
`decM` subtracts 1 from `m` (`decM_ok`), and `mulE` and `mulXR` compute the
products the reductions start from (`mulE_ok`, `mulXR_ok`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aOne sMask)

theorem slot_eq (w j : Nat) : slot w j = 256 + j * (8 * (w + 2)) := by unfold slot hdrBytes; rfl

theorem hdrLd {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (hZ : slot w 8 ≤ Z) {i : Nat} (hi : i < 32) :
    InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 :=
  hs.ld (by have := hdr_lt_slot w 8 hi; omega)

/-- After a change within the arrays `js` and the header slot `sMask`. -/
theorem Good.of_arrays {s t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    {js : List Nat} (ha : Arrays B w js s.mem t.mem) (hk : Keep mmRegs s t) (hwr : t.wr = s.wr) :
    Good t B Z w minv :=
  ⟨hg.scr.congr hwr, (hk.gpr (by decide)).trans hg.rdi, ha.hdr hg.hdr⟩

theorem Good.of_mask {s t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (ho : Outside B (8 * sMask) 8 s.mem t.mem) (hk : Keep mmRegs s t) : Good t B Z w minv :=
  ⟨hg.scr.congr hk.2.2, (hk.gpr (by decide)).trans hg.rdi, by
    have hh : ∀ i < 16, word t.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
      ho.word (Or.inl (by unfold sMask sFn; omega))
        (by have := hg.scr.nowrap; have := hdr_lt_slot w 8 (show 31 < 32 by decide); omega)
    exact ⟨(hh _ (by decide)).trans hg.hdr.hw, (hh _ (by decide)).trans hg.hdr.hminv,
      fun j hj => (hh _ (by unfold sArr; omega)).trans (hg.hdr.harr j hj)⟩⟩

/-! ## Masks -/

/-- `sMask &= ` the mask of `[a] < [b]`. -/
theorem ltMask_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 28) {a b : Nat} (ha : a < 8) (hb : b < 8) :
    WP isa (seqs (ltMask a b)) s fun t =>
      word t.mem B (8 * sMask) = word s.mem B (8 * sMask) &&&
        mask (decide (wv s.mem B (slot w a) w < wv s.mem B (slot w b) w)) ∧
      Outside B (8 * sMask) 8 s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hdrLd hg.scr hZ hi
  have hA := Nat.le_trans (slot_le (w := w) ha) hZ
  have hB := Nat.le_trans (slot_le (w := w) hb) hZ
  have hS : 8 * sMask + 8 ≤ Z := by have := hdr_lt_slot w 8 (show sMask < 32 by decide); omega
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  simp only [ltMask, seqs]
  refine WP.seq (WP.mono (WP.keep [.r12, .rbx, .r10, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rbx = off B (slot w a) ∧ t.gpr .r10 = off B (slot w b) ∧ t.gpr .rbp = mask false ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr a) (by unfold sArr; omega),
      hl (sArr b) (by unfold sArr; omega), hg.hdr.hw, hg.hdr.harr a ha, hg.hdr.harr b hb]) rfl)
    fun s₁ ⟨⟨h12, hbx, h10, hbp, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (cmpLoop_ok (hg.scr.congr k₁.2.2) hbx h10 h12 hbp hw (by omega) (by omega) (by omega))
    fun s₂ ⟨hbp₂, hm₂, k₂⟩ => ?_)
  rw [hm₁] at hbp₂
  have k12 := k₁.trans k₂
  have hdi₂ : s₂.gpr .rdi = B := (k12.gpr (by decide)).trans hg.rdi
  have hs₂ := hg.scr.congr k12.2.2
  refine WP.mono (WP.keep [.rbp] (Q := fun t =>
      t.mem = s₂.mem.writeW (off B (8 * sMask)) (s₂.gpr .rbp &&& word s₂.mem B (8 * sMask)))
    (by xrun [State.ea, hdr, hdi₂, hdrOff, hs₂.ld (show 8 * sMask + 8 ≤ Z by omega),
      hs₂.st (show 8 * sMask + 8 ≤ Z by omega)]) rfl) fun t ⟨hm, k₃⟩ => ?_
  refine ⟨?_, ?_, (k12.trans k₃).mono (by decide)⟩
  · rw [hm, word_writeW_self, hbp₂, hm₂, hm₁, BitVec.and_comm]
  · rw [hm, hm₂, hm₁]; exact writeW_outside _ B _ (by omega)

/-- `sMask &= ` the mask of `[aR] = [aOne]`. -/
theorem eqOne_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 28) :
    WP isa (seqs eqOne) s fun t =>
      word t.mem B (8 * sMask) = word s.mem B (8 * sMask) &&&
        mask (decide (wv s.mem B (slot w aR) w = wv s.mem B (slot w aOne) w)) ∧
      Outside B (8 * sMask) 8 s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hdrLd hg.scr hZ hi
  have hA := Nat.le_trans (slot_le (w := w) (show aR < 8 by decide)) hZ
  have hB := Nat.le_trans (slot_le (w := w) (show aOne < 8 by decide)) hZ
  have hS : 8 * sMask + 8 ≤ Z := by have := hdr_lt_slot w 8 (show sMask < 32 by decide); omega
  have h8 := hdr_lt_slot w 8 (show 31 < 32 by decide)
  simp only [eqOne, seqs]
  refine WP.seq (WP.mono (WP.keep [.r12, .rbx, .r10, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rbx = off B (slot w aR) ∧ t.gpr .r10 = off B (slot w aOne) ∧ t.gpr .rbp = 0 ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr aR) (by decide),
      hl (sArr aOne) (by decide), hg.hdr.hw, hg.hdr.harr aR (by decide), hg.hdr.harr aOne (by decide)]) rfl)
    fun s₁ ⟨⟨h12, hbx, h10, hbp, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.2.2
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₁.mem → Keep [.r14] s₁ t → t.cf = s₁.cf →
      OrInv s₁ B Z (fun j => ∀ i < j, word s₁.mem B (slot w aR + 8 * i) = word s₁.mem B (slot w aOne + 8 * i))
        0 t := fun t h14 hm k _ =>
    ⟨hs₁.congr k.2.2, k.mono (by decide), hm, h14, by
      rw [(k.gpr (by decide) : t.gpr .rbp = s₁.gpr .rbp), hbp]
      exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩⟩
  refine WP.seq (WP.mono (wordLoop_ok (start := 0) (N := w) (by omega) (by omega) _ h0
    (fun j _ hj t hI => xorStep_ok hbx h10 h12 (by omega) (by omega) (by omega) hj hI)) fun s₂ hI => ?_)
  have hdi₂ : s₂.gpr .rdi = B := ((k₁.trans hI.keep).gpr (by decide)).trans hg.rdi
  refine WP.mono (WP.keep [.rbp] (Q := fun t => ∃ b : Bool, b = decide (s₂.gpr .rbp = 0) ∧
      t.mem = s₂.mem.writeW (off B (8 * sMask)) (mask b &&& word s₂.mem B (8 * sMask)))
    (by
      xrun [State.ea, hdr, hdi₂, hdrOff, hI.scr.ld (show 8 * sMask + 8 ≤ Z by omega),
        hI.scr.st (show 8 * sMask + 8 ≤ Z by omega)]
      exact ⟨_, decide_lt_one _, rfl⟩) rfl) fun t ⟨⟨b, hb, hm⟩, k₄⟩ => ?_
  have hm₂ : s₂.mem = s.mem := hI.mem.trans hm₁
  have hR : b = decide (wv s.mem B (slot w aR) w = wv s.mem B (slot w aOne) w) := by
    rw [hb, Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, hI.val, hm₁]
    exact ⟨fun h => wv_congr2 (fun i hi => (h i hi).symm) |>.symm, fun h => wv_inj w h⟩
  refine ⟨?_, ?_, ((k₁.trans hI.keep).trans k₄).mono (by decide)⟩
  · rw [hm, word_writeW_self, hm₂, BitVec.and_comm, hR]
  · rw [hm, ← hm₂]
    exact writeW_outside _ B _ (by omega)

/-! ## `m - 1` -/

/-- After `j` words of `decM`'s loop: `M'_j + 1 = M_j + 2^(64 j) c`. -/
structure DecInv (s₀ : State) (B : Addr) (Z eM : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rbp, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : Outside B eM (8 * j) s₀.mem t.mem
  val : ∃ c : Bool, t.gpr .rbp = mask c ∧
    wv t.mem B eM j + 1 = wv s₀.mem B eM j + 2 ^ (64 * j) * c.toNat

theorem decStep_ok {s₀ : State} {B : Addr} {Z w eM : Nat}
    (hbx : s₀.gpr .rbx = off B eM) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 32) (hM : eM + 8 * w ≤ Z) {j : Nat} (hj : j < w) {t : State}
    (hI : DecInv s₀ B Z eM j t) :
    WP isa (.block ([cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .sbb .rax (.imm 0),
        .store (ix .rbx .r14) .rax, cfToRbp] ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ DecInv s₀ B Z eM (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tbx : t.gpr .rbx = off B eM := (hI.keep.gpr (by decide)).trans hbx
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  obtain ⟨c, hbp, hval⟩ := hI.val
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t₁ =>
      ∃ c' : Bool, t₁.gpr .rbp = mask c' ∧ ∃ r : BitVec 64, t₁.mem = t.mem.writeW (off B (eM + 8 * j)) r ∧
        r.toNat + c.toNat = (word t.mem B (eM + 8 * j)).toNat + 2 ^ 64 * c'.toNat) ?_ rfl)
    fun t₁ ⟨⟨c', h₁, r, hm, hr⟩, k₁⟩ => ?_
  · unfold cfFromRbp cfToRbp
    xrun [State.ea, ix, addr0 tbx hI.r14, hbp, cf_mask, sx0,
      hI.scr.ld (show eM + 8 * j + 8 ≤ Z by omega), hI.scr.st (show eM + 8 * j + 8 ≤ Z by omega)]
    refine ⟨_, rfl, _, rfl, ?_⟩
    have := sbb_toNat (word t.mem B (eM + 8 * j)) 0 c
    simp only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero, Nat.zero_add] at this ⊢
    exact this
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  have hx : word t.mem B (eM + 8 * j) = word s₀.mem B (eM + 8 * j) := hI.out.word (by omega) (by omega)
  rw [hx] at hr
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_,
    ⟨c', (k'.gpr (by decide)).trans h₁, ?_⟩⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B r (by omega) x (by omega)]
    exact hI.out x (by omega)
  · have hlow : wv t.mem B eM j = wv (t.mem.writeW (off B (eM + 8 * j)) r) B eM j :=
      ((writeW_outside t.mem B r (by omega)).wv (Or.inl (by omega)) (by omega)).symm
    rw [hm', hm]
    simp only [wv]
    rw [← hlow, word_writeW_self, pow64_succ]
    grind

/-- `[aM] := [aM] - 1`, when it is not zero. -/
theorem decM_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 28) :
    WP isa (seqs decM) s fun t =>
      (0 < wv s.mem B (slot w aM) w → wv t.mem B (slot w aM) w + 1 = wv s.mem B (slot w aM) w) ∧
      Outside B (slot w aM) (8 * w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hdrLd hg.scr hZ hi
  have hA := Nat.le_trans (slot_le (w := w) (show aM < 8 by decide)) hZ
  simp only [decM, seqs]
  refine WP.seq (WP.mono (WP.keep [.r12, .rbx, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rbx = off B (slot w aM) ∧ t.gpr .rbp = mask true ∧ t.mem = s.mem)
    (by
      xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr aM) (by decide), hg.hdr.hw,
        hg.hdr.harr aM (by decide)]) rfl)
    fun s₁ ⟨⟨h12, hbx, hbp, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.2.2
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₁.mem → Keep [.r14] s₁ t → t.cf = s₁.cf →
      DecInv s₁ B Z (slot w aM) 0 t := fun t h14 hm k _ =>
    ⟨hs₁.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨true, (k.gpr (by decide)).trans hbp, by rw [hm]; simp [wv]⟩⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := w) (by omega) (by omega) (DecInv s₁ B Z (slot w aM)) h0
    (fun j _ hj t hI => decStep_ok hbx h12 (by omega) (by omega) hj hI)) fun t hI => ?_
  obtain ⟨c, -, hval⟩ := hI.val
  rw [hm₁] at hval
  refine ⟨fun h0 => ?_, by rw [← hm₁]; exact hI.out, (k₁.trans hI.keep).mono (by decide)⟩
  have hlt := wv_lt t.mem B (slot w aM) w
  cases c
  · simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hval; exact hval
  · simp only [Bool.toNat_true, Nat.mul_one] at hval; omega

/-! ## Products -/

theorem mul_lt_pow {a b n k : Nat} (ha : a < 2 ^ n) (hb : b < 2 ^ k) : a * b < 2 ^ (n + k) := by
  rw [Nat.pow_add]
  exact Nat.mul_lt_mul_of_lt_of_le ha (Nat.le_of_lt hb) (Nat.two_pow_pos k)

/-- `acc := [aX] e` (`w + 2` words), for `e` in slot `sEv`. -/
theorem mulE_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 28) :
    WP isa (seqs mulE) s fun t =>
      wv t.mem B (slot w aAcc) (w + 2) = (word s.mem B (8 * sEv)).toNat * wv s.mem B (slot w aX) w ∧
      Arrays B w [aAcc] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hdrLd hg.scr hZ hi
  have hA := Nat.le_trans (slot_le (w := w) (show aAcc < 8 by decide)) hZ
  have sl := slot_eq w
  simp only [mulE, seqs]
  refine WP.seq (WP.mono (WP.keep [.r8, .r12] (Q := fun t => t.gpr .r8 = off B (slot w aAcc) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr aAcc) (by decide), hg.hdr.hw,
      hg.hdr.harr aAcc (by decide)]) rfl) fun s₁ ⟨⟨h8, h12, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (zeroAccLoop_ok (hg.scr.congr k₁.2.2) h8 h12 hw (by omega) hA)
    fun s₂ ⟨hz₂, ho₂, k₂⟩ => ?_)
  rw [hm₁] at ho₂
  have k12 := k₁.trans k₂
  have hs₂ := hg.scr.congr k12.2.2
  have hdi₂ : s₂.gpr .rdi = B := (k12.gpr (by decide)).trans hg.rdi
  have a₂ : Arrays B w [aAcc] s.mem s₂.mem := Arrays.of_outside (by simp) ho₂ (Nat.le_refl _) (Nat.le_refl _)
  have hH₂ := a₂.hdr hg.hdr
  have hl₂ : ∀ i < 32, InRegions (s₂.rd ++ s₂.wr) (off B (8 * i)) 8 := fun i hi => hdrLd hs₂ hZ hi
  have hE : word s₂.mem B (8 * sEv) = word s.mem B (8 * sEv) :=
    a₂.word_eq (fun j hj => by
      simp only [List.mem_singleton] at hj; subst hj; exact .inl (hdr_lt_slot w aAcc (by decide))) (by
      have := hdr_lt_slot w 8 (show sEv < 32 by decide); omega)
  have hX : wv s₂.mem B (slot w aX) w = wv s.mem B (slot w aX) w :=
    a₂.wv_eq (fun j hj => by
      simp only [List.mem_singleton] at hj; subst hj; rw [sl, sl]; unfold aX aAcc; omega) (by
      have := Nat.le_trans (slot_le (w := w) (show aX < 8 by decide)) hZ; omega)
  refine WP.seq (WP.mono (WP.keep [.rcx, .r9, .r8] (Q := fun t => t.gpr .rcx = word s.mem B (8 * sEv) ∧
      t.gpr .r9 = off B (slot w aX) ∧ t.gpr .r8 = off B (slot w aAcc) ∧ t.mem = s₂.mem)
    (by xrun [State.ea, hdr, hdi₂, hdrOff, hl₂ sEv (by decide), hl₂ (sArr aX) (by decide),
      hl₂ (sArr aAcc) (by decide), hE, hH₂.harr aX (by decide), hH₂.harr aAcc (by decide)]) rfl)
    fun s₃ ⟨⟨hcx, h9, h8', hm₃⟩, k₃⟩ => ?_)
  have h12₃ : s₃.gpr .r12 = BitVec.ofNat 64 w := ((k₂.trans k₃).gpr (by decide)).trans h12
  have hb : wv s₃.mem B (slot w aAcc) (w + 2) + (s₃.gpr .rcx).toNat * wv s₃.mem B (slot w aX) w <
      2 ^ (64 * (w + 2)) := by
    rw [hm₃, hz₂, hcx, hX, Nat.zero_add]
    have := mul_lt_pow (word s.mem B (8 * sEv)).isLt (wv_lt s.mem B (slot w aX) w)
    have h2 : 2 ^ (64 + 64 * w) ≤ 2 ^ (64 * (w + 2)) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  refine WP.mono (mulAddRow_ok (hs₂.congr k₃.2.2) h8' h9 h12₃ hw (by omega) hA
    (by have := Nat.le_trans (slot_le (w := w) (show aX < 8 by decide)) hZ; omega)
    (by rw [sl, sl]; unfold aX aAcc; omega) hb) fun t ⟨hv, ho, k₄⟩ => ?_
  refine ⟨?_, ?_, (((k12.trans k₃).trans k₄)).mono (by decide)⟩
  · rw [hv, hm₃, hz₂, hcx, hX, Nat.zero_add]
  · rw [hm₃] at ho
    exact a₂.trans (Arrays.of_outside (by simp) ho (Nat.le_refl _) (by omega))

/-- `acc := [aX] [aR]` (`2 w + 2` words). -/
theorem mulXR_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 28) :
    WP isa (seqs mulXR) s fun t =>
      wv t.mem B (slot w aAcc) (2 * w + 2) = wv s.mem B (slot w aX) w * wv s.mem B (slot w aR) w ∧
      Arrays B w [aAcc, aTmp] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi => hdrLd hg.scr hZ hi
  have sl := slot_eq w
  have h8Z : slot w 8 = 256 + 64 * (w + 2) := by rw [sl]; omega
  have hA : slot w aAcc + 8 * (2 * w + 2) ≤ Z := by rw [sl]; simp only [aAcc]; omega
  simp only [mulXR, Impl.Rsa.X86_64.Crt.zeroAccs, List.cons_append, List.nil_append, seqs]
  refine WP.seq (WP.mono (WP.keep [.r8, .rbx] (Q := fun t => t.gpr .r8 = off B (slot w aAcc) ∧
      t.gpr .rbx = BitVec.ofNat 64 w ∧ t.mem = s.mem)
    (by xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr aAcc) (by decide), hg.hdr.hw,
      hg.hdr.harr aAcc (by decide)]) rfl) fun s₁ ⟨⟨h8, hbx, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (zeroWin_ok (hg.scr.congr k₁.2.2) h8 hbx (by omega) hA) fun s₂ ⟨hz₂, ho₂, k₂⟩ => ?_)
  rw [hm₁] at ho₂
  have k12 := k₁.trans k₂
  have hs₂ := hg.scr.congr k12.2.2
  have hdi₂ : s₂.gpr .rdi = B := (k12.gpr (by decide)).trans hg.rdi
  have a₂ : Arrays B w [aAcc, aTmp] s.mem s₂.mem := fun x hx => ho₂ x (by
    have h1 := hx aAcc (by simp); have h2 := hx aTmp (by simp)
    rw [sl] at h1 h2; simp only [aAcc, aTmp] at h1 h2; rw [sl]; simp only [aAcc]; omega)
  have hH₂ := a₂.hdr hg.hdr
  have hl₂ : ∀ i < 32, InRegions (s₂.rd ++ s₂.wr) (off B (8 * i)) 8 := fun i hi => hdrLd hs₂ hZ hi
  have fX : wv s₂.mem B (slot w aX) w = wv s.mem B (slot w aX) w :=
    a₂.wv_eq (fun j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl <;> rw [sl, sl] <;> simp only [aX, aAcc, aTmp] <;> omega) (by rw [sl]; simp only [aX]; omega)
  have fR : wv s₂.mem B (slot w aR) w = wv s.mem B (slot w aR) w :=
    a₂.wv_eq (fun j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl <;> rw [sl, sl] <;> simp only [aR, aAcc, aTmp] <;> omega) (by rw [sl]; simp only [aR]; omega)
  refine WP.seq (WP.mono (WP.keep [.r11, .r10, .r9, .r12, .r8] (Q := fun t => t.gpr .r11 = off B (slot w aX) ∧
      t.gpr .r10 = BitVec.ofNat 64 w ∧ t.gpr .r9 = off B (slot w aR) ∧ t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .r8 = off B (slot w aAcc) ∧ t.mem = s₂.mem)
    (by xrun [State.ea, hdr, hdi₂, hdrOff, hl₂ sW (by decide), hl₂ (sArr aX) (by decide),
      hl₂ (sArr aR) (by decide), hl₂ (sArr aAcc) (by decide), hH₂.hw, hH₂.harr aX (by decide),
      hH₂.harr aR (by decide), hH₂.harr aAcc (by decide)]) rfl)
    fun s₃ ⟨⟨h11, h10, h9, h12, h8', hm₃⟩, k₃⟩ => ?_)
  have hz : wv s₃.mem B (slot w aAcc) (w + w + 2) = 0 := by
    rw [hm₃, wv_eq_zero_iff]; exact fun q hq => hz₂ q (by omega)
  refine WP.mono (mulRows_ok (hs₂.congr k₃.2.2) h11 h9 h10 h12 h8' hw hw (by omega)
    (by rw [show w + w + 2 = 2 * w + 2 by omega]; exact hA) (by rw [sl]; simp only [aX]; omega)
    (by rw [sl]; simp only [aR]; omega) (by rw [sl, sl]; simp only [aX, aAcc]; omega)
    (by rw [sl, sl]; simp only [aR, aAcc]; omega) (by rw [hz]; exact Nat.two_pow_pos _)) fun t ⟨hv, ho, k₄⟩ => ?_
  refine ⟨?_, ?_, ((k12.trans k₃).trans k₄).mono (by decide)⟩
  · rw [show 2 * w + 2 = w + w + 2 by omega, hv, hz, Nat.zero_add, hm₃, fX, fR]
  · rw [hm₃] at ho
    exact a₂.trans fun x hx => ho x (by
      have h1 := hx aAcc (by simp); have h2 := hx aTmp (by simp)
      rw [sl] at h1 h2; simp only [aAcc, aTmp] at h1 h2; rw [sl]; simp only [aAcc]; omega)

/-! ## Loading a number -/

/-- `[j] := ` the bytes `bs` whose pointer and length are in header slots
`sp` and `sl`, over `w` words. -/
theorem loadNum_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 28) {j : Nat} (hj : j < 8) {sp sl : Nat} (hsp : sp < 32)
    (hsl : sl < 32) {p : Addr} {bs : List Byte} (hp : word s.mem B (8 * sp) = p)
    (hl : word s.mem B (8 * sl) = BitVec.ofNat 64 bs.length) (hsrc : Src s B Z p bs) (hk1 : 1 ≤ bs.length)
    (hkw : bs.length ≤ 8 * w) :
    WP isa (seqs (loadNum j sp sl)) s fun t =>
      wv t.mem B (slot w j) w = Spec.Rsa.os2ip bs ∧ Arrays B w [j] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hg.scr.nowrap
  have hJ := Nat.le_trans (slot_le (w := w) hj) hZ
  have hJ0 := hdr_lt_slot w j (show 31 < 32 by decide)
  simp only [loadNum, seqs]
  refine WP.seq (WP.mono (zeroArr_ok hg hZ hw (by omega) hj) fun s₁ ⟨hz₁, ho₁, k₁⟩ => ?_)
  have a₁ : Arrays B w [j] s.mem s₁.mem := Arrays.of_outside (by simp) ho₁ (Nat.le_refl _) (Nat.le_refl _)
  have hs₁ := hg.scr.congr k₁.2.2
  have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hg.rdi
  have hH₁ := a₁.hdr hg.hdr
  have hw₁ : ∀ i < 32, word s₁.mem B (8 * i) = word s.mem B (8 * i) := fun i hi =>
    a₁.word_eq (fun j' hj' => by
      rw [List.mem_singleton.mp hj']; exact .inl (hdr_lt_slot w j hi)) (by
      have := hdr_lt_slot w 8 hi; omega)
  have hl₁ : ∀ i < 32, InRegions (s₁.rd ++ s₁.wr) (off B (8 * i)) 8 := fun i hi => hdrLd hs₁ hZ hi
  refine WP.seq (WP.mono (WP.keep [.rsi, .rcx, .rbx] (Q := fun t => t.gpr .rsi = p ∧
      t.gpr .rcx = BitVec.ofNat 64 bs.length ∧ t.gpr .rbx = off B (slot w j) ∧ t.mem = s₁.mem)
    (by xrun [State.ea, hdr, hdi₁, hdrOff, hl₁ sp hsp, hl₁ sl hsl, hl₁ (sArr j) (by unfold sArr; omega),
      hw₁ sp hsp, hw₁ sl hsl, hp, hl, hH₁.harr j hj]) rfl) fun s₂ ⟨⟨hsi, hcx, hbx, hm₂⟩, k₂⟩ => ?_)
  have hs₂ := hs₁.congr k₂.2.2
  have hsrc₂ : Src s₂ B Z p bs :=
    hsrc.congrK (by rw [hm₂]; exact InScr.of_outside ho₁ (by omega)) (k₁.trans k₂)
  refine WP.mono (loadBE_ok (w := (bs.length + 7) / 8) hs₂ hsi hcx hbx rfl hk1 (by omega) rfl (by omega)
    hsrc₂.rd hsrc₂.val (fun i hi => .inr (by have := hsrc₂.out i hi; omega))) fun t ⟨hv, ho, k₃⟩ => ?_
  refine ⟨?_, a₁.trans (by rw [← hm₂]; exact Arrays.of_outside (by simp) ho (Nat.le_refl _) (by omega)),
    ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  have hsplit := wv_add t.mem B (slot w j) ((bs.length + 7) / 8) (w - (bs.length + 7) / 8)
  rw [show (bs.length + 7) / 8 + (w - (bs.length + 7) / 8) = w by omega] at hsplit
  rw [hsplit, hv]
  have hz : wv t.mem B (slot w j + 8 * ((bs.length + 7) / 8)) (w - (bs.length + 7) / 8) = 0 := by
    rw [ho.wv (Or.inr (Nat.le_refl _)) (by omega), hm₂, wv_eq_zero_iff]
    intro q hq
    rw [wv_eq_zero_iff] at hz₁
    have := hz₁ ((bs.length + 7) / 8 + q) (by omega)
    rwa [show slot w j + 8 * ((bs.length + 7) / 8) + 8 * q = slot w j + 8 * ((bs.length + 7) / 8 + q) by omega]
  rw [hz, Nat.mul_zero, Nat.add_zero]

end VG.Proof.Rsa.X86_64

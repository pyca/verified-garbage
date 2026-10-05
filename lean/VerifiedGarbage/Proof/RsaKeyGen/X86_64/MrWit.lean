import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrLoop
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdE
import VerifiedGarbage.Proof.Bignum.X86_64.Cmp

/-!
# A candidate on x86-64: Miller–Rabin's witness

`witLoad_ok`: the next `8 w` octets of `rand` into `aX`, `kUsed` advanced;
`witLow_ok`: the mask of `x ≥ 2`; `witCmp_ok`: the mask of `(x | 1) < c`;
`witForce_ok`: the witness forced into range unless both hold.
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- The witness's octets into `aX`. -/
theorem witLoad_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 27) {rp : Addr} {u : Nat} {bs : List Byte} (hR : word s.mem B (8 * kRand) = rp)
    (hU : word s.mem B (8 * kUsed) = BitVec.ofNat 64 u) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hsrc : Src s B Z (rp + BitVec.ofNat 64 u) bs) (hbl : bs.length = 8 * w) :
    WP isa (seqs [.block [.mov .rsi (.mem (hdr kRand)), .alu .add .rsi (.mem (hdr kUsed)), .mov .rcx (.mem (hdr kLen)),
        .mov .rbx (.mem (hdr (sArr aX))), .mov .rax (.mem (hdr kUsed)), .alu .add .rax (.reg .rcx),
        .store (hdr kUsed) .rax], loadBE]) s fun t =>
      wv t.mem B (slot w aX) w = Spec.Rsa.os2ip bs ∧ word t.mem B (8 * kUsed) = BitVec.ofNat 64 (u + 8 * w) ∧
      Frm B [(slot w aX, 8 * (w + 2)), (8 * kUsed, 8)] s.mem t.mem ∧ Good t B Z w mi ∧
      Keep [.rax, .rcx, .rdx, .rbx, .rsi, .rbp, .r14] s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have hw8 : (8 * w + 7) / 8 = w := by omega
  have hst : InRegions s.wr (off B (8 * kUsed)) 8 := hg.scr.st (by have := hdr_lt_slot w 8 (show kUsed < 32 by decide); omega)
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.rsi, .rcx, .rbx, .rax] (Q := fun t => t.gpr .rsi = rp + BitVec.ofNat 64 u ∧
      t.gpr .rcx = BitVec.ofNat 64 (8 * w) ∧ t.gpr .rbx = off B (slot w aX) ∧
      t.mem = s.mem.writeW (off B (8 * kUsed)) (BitVec.ofNat 64 (u + 8 * w))) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl kRand (by decide), hl kUsed (by decide), hl kLen (by decide),
      hl (sArr aX) (by decide), hst, hR, hU, hK, hg.hdr.harr aX (by decide), BitVec.ofNat_add]) rfl)
    fun s₁ ⟨⟨hsi, hcx, hbx, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.2.2
  have hin : InScr B Z s.mem s₁.mem := by
    rw [hm₁]; exact InScr.of_outside (writeW_outside _ B _ (d := 8 * kUsed) (by unfold kUsed sFn; omega))
      (by have := hdr_lt_slot w 8 (show kUsed < 32 by decide); omega)
  refine WP.mono (loadArr_ok (j := aX) hs₁ (by decide) (by rw [hw8]; exact hZ) (hsrc.congrK hin k₁) hbl (by omega)
    (by omega) hsi hcx (by rw [hw8]; exact hbx)) fun t ⟨hv, ha, k⟩ => ?_
  rw [hw8] at hv ha
  have hH₁ : Hdr s₁.mem B w mi := by rw [hm₁]; exact hg.hdr.store (by decide) (by decide) _
  refine ⟨hv, ?_, ?_, ⟨hs₁.congr k.2.2, (k.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hg.rdi), ha.hdr hH₁⟩,
    (k₁.trans k).mono (by decide)⟩
  · rw [ha.hslot (by decide), hm₁, word_writeW_self]
  · refine (?_ : Frm B _ s.mem s₁.mem).trans (Frm.of_arrays ha (by simp))
    rw [hm₁]; exact Frm.of_outside (writeW_outside _ B _ (d := 8 * kUsed) (by unfold kUsed sFn; omega)) (by simp)

theorem and_m2_eq_zero (x : BitVec 64) : x &&& (BitVec.allOnes 64 - 1) = 0 ↔ x.toNat ≤ 1 := by
  have hmb : ∀ i < 64, 1 ≤ i → (BitVec.allOnes 64 - 1).getLsbD i = true := by decide
  constructor
  · intro h
    have : x.toNat < 2 ^ 1 := Nat.lt_pow_two_of_testBit _ fun i hi => by
      by_cases hi64 : i < 64
      · have := congrArg (fun y : BitVec 64 => y.getLsbD i) h
        simp only [BitVec.getLsbD_and, hmb i hi64 hi, Bool.and_true] at this
        rw [BitVec.testBit_toNat]; simpa using this
      · exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
    omega
  · intro h
    rcases (by omega : x.toNat = 0 ∨ x.toNat = 1) with h | h
    · rw [show x = 0#64 from BitVec.eq_of_toNat_eq h]; decide
    · rw [show x = 1#64 from BitVec.eq_of_toNat_eq h]; decide

/-- A number of `w ≥ 1` words is at most 1 iff its low word is and the others
are zero. -/
theorem wv_le_one {m : Mem} {p : Addr} {d w : Nat} (hw : 1 ≤ w) :
    wv m p d w ≤ 1 ↔ (word m p d &&& (BitVec.allOnes 64 - 1) = 0 ∧ ∀ i, 1 ≤ i → i < w → word m p (d + 8 * i) = 0) := by
  have e := wv_add m p d 1 (w - 1)
  rw [show 1 + (w - 1) = w by omega] at e
  have h1 : wv m p d 1 = (word m p d).toNat := by simp [wv]
  rw [e, h1, and_m2_eq_zero]
  have hz := wv_eq_zero_iff m p (d + 8 * 1) (w - 1)
  constructor
  · intro h
    have h2 : wv m p (d + 8 * 1) (w - 1) = 0 := by
      rcases Nat.eq_zero_or_pos (wv m p (d + 8 * 1) (w - 1)) with h0 | h0
      · exact h0
      · have := Nat.mul_le_mul_left (2 ^ (64 * 1)) h0; simp at this; omega
    refine ⟨by omega, fun i hi hiw => ?_⟩
    have := hz.mp h2 (i - 1) (by omega)
    rwa [show d + 8 * 1 + 8 * (i - 1) = d + 8 * i by omega] at this
  · rintro ⟨h0, h⟩
    rw [hz.mpr fun q hq => by rw [show d + 8 * 1 + 8 * q = d + 8 * (q + 1) by omega]; exact h (q + 1) (by omega) (by omega)]
    omega

/-- After `j` words of a loop that ORs words `1, 2, …` into `rbp`. -/
structure OrInv1 (s₀ : State) (B : Addr) (Z e : Nat) (A : Prop) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rbp, .r14] s₀ t
  mem : t.mem = s₀.mem
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  val : t.gpr .rbp = 0 ↔ (A ∧ ∀ i, 1 ≤ i → i < j → word s₀.mem B (e + 8 * i) = 0)

theorem orStep1_ok {s₀ : State} {B : Addr} {Z w e : Nat} {A : Prop}
    (hbx : s₀.gpr .rbx = off B e) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 32) (he : e + 8 * w ≤ Z) {j : Nat} (hj1 : 1 ≤ j) (hj : j < w) {t : State} (hI : OrInv1 s₀ B Z e A j t) :
    WP isa (.block (([.mov .rax (.mem (ix .rbx .r14)), .alu .or .rbp (.reg .rax)] : List Instr) ++
        ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ OrInv1 s₀ B Z e A (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tbx : t.gpr .rbx = off B e := (hI.keep.gpr (by decide)).trans hbx
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t₁ => t₁.mem = t.mem ∧
      t₁.gpr .rbp = t.gpr .rbp ||| word t.mem B (e + 8 * j)) ?_ rfl)
    fun t₁ ⟨⟨hm, hbp⟩, k₁⟩ => ?_
  · xrun [State.ea, ix, addr0 tbx hI.r14, hI.scr.ld (show e + 8 * j + 8 ≤ Z by omega)]
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide),
    by rw [hm', hm, hI.mem], h14, ?_⟩
  rw [(k'.gpr (by decide) : t'.gpr .rbp = t₁.gpr .rbp), hbp, or_eq_zero, hI.val, hI.mem]
  constructor
  · rintro ⟨⟨hA, h1⟩, h2⟩
    refine ⟨hA, fun i hi1 hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    exacts [h1 i hi1 hi, h2]
  · rintro ⟨hA, h⟩
    exact ⟨⟨hA, fun i hi1 hi => h i hi1 (by omega)⟩, h j hj1 (by omega)⟩

/-- `rbp` zero iff `x ≤ 1`, for `x` in `aX`. -/
theorem witLow_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 31) :
    WP isa (seqs [.block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aX))), .mov .rbp (.mem (at0 .rbx)),
        .alu .and .rbp (.imm (BitVec.ofInt 32 (-2)))],
      wordLoop 1 [.mov .rax (.mem (ix .rbx .r14)), .alu .or .rbp (.reg .rax)]]) s fun t =>
      (t.gpr .rbp = 0 ↔ wv s.mem B (slot w aX) w ≤ 1) ∧ t.gpr .rbx = off B (slot w aX) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.mem = s.mem ∧ Keep [.rax, .rbx, .rbp, .r12, .r14] s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have sX := Nat.le_trans (slot_le (w := w) (show aX < 8 by decide)) hZ
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.r12, .rbx, .rbp] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .rbx = off B (slot w aX) ∧ t.gpr .rbp = word s.mem B (slot w aX) &&& (BitVec.allOnes 64 - 1) ∧
      t.mem = s.mem) (by
    xrun [State.ea, hdr, at0, hg.rdi, hdrOff, hl sW (by decide), hl (sArr aX) (by decide), hg.hdr.hw,
      hg.hdr.harr aX (by decide), show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      hg.scr.ld (d := slot w aX) (by omega), sx_m2]) rfl) fun s₁ ⟨⟨h12, hbx, hbp, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.2.2
  refine WP.mono (wordLoop_ok (start := 1) (N := w) (by omega) hw'
    (OrInv1 s₁ B Z (slot w aX) (word s₁.mem B (slot w aX) &&& (BitVec.allOnes 64 - 1) = 0))
    (fun t h14 hm k _ => ⟨hs₁.congr k.2.2, k.mono (by decide), hm, h14, by
      rw [(k.gpr (by decide) : t.gpr .rbp = s₁.gpr .rbp), hbp, hm₁]
      exact ⟨fun h => ⟨h, fun i hi1 hi => absurd hi (by omega)⟩, fun h => h.1⟩⟩)
    (fun j hj1 hj t hI => orStep1_ok hbx h12 (by omega) (by omega) hj1 hj hI)) fun t hI => ?_
  refine ⟨?_, (hI.keep.gpr (by decide)).trans hbx, (hI.keep.gpr (by decide)).trans h12, by rw [hI.mem, hm₁],
    (k₁.trans hI.keep).mono (by decide)⟩
  rw [hI.val, hm₁, wv_le_one (by omega)]

/-- After `j` words of the comparison of `X + δ` with `m`. -/
structure CmpInvD (s₀ : State) (B : Addr) (Z eX eN δ : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rbp, .r14] s₀ t
  mem : t.mem = s₀.mem
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  val : ∃ (c : Bool) (d : Nat), t.gpr .rbp = mask c ∧ d < 2 ^ (64 * j) ∧
    d + wv s₀.mem B eN j = wv s₀.mem B eX j + δ + 2 ^ (64 * j) * c.toNat

theorem cmpStepD_ok {s₀ : State} {B : Addr} {Z w eX eN δ : Nat}
    (hbx : s₀.gpr .rbx = off B eX) (h10 : s₀.gpr .r10 = off B eN)
    (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w) (hw : w < 2 ^ 32) (hX : eX + 8 * w ≤ Z) (hN : eN + 8 * w ≤ Z)
    {j : Nat} (hj : j < w) {t : State} (hI : CmpInvD s₀ B Z eX eN δ j t) :
    WP isa (.block (cmpBody ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ CmpInvD s₀ B Z eX eN δ (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tbx : t.gpr .rbx = off B eX := (hI.keep.gpr (by decide)).trans hbx
  have t10 : t.gpr .r10 = off B eN := (hI.keep.gpr (by decide)).trans h10
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  obtain ⟨c, d, hbp, hd, hval⟩ := hI.val
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t₁ => t₁.mem = t.mem ∧
      ∃ c' : Bool, t₁.gpr .rbp = mask c' ∧ ∃ r : BitVec 64,
        r.toNat + (word t.mem B (eN + 8 * j)).toNat + c.toNat =
          (word t.mem B (eX + 8 * j)).toNat + 2 ^ 64 * c'.toNat) ?_ rfl)
    fun t₁ ⟨⟨hm, c', h₁, r, hr⟩, k₁⟩ => ?_
  · unfold cmpBody cfFromRbp cfToRbp
    xrun [State.ea, ix, addr0 tbx hI.r14, addr0 t10 hI.r14, hbp, cf_mask,
      hI.scr.ld (show eX + 8 * j + 8 ≤ Z by omega), hI.scr.ld (show eN + 8 * j + 8 ≤ Z by omega)]
    exact ⟨_, rfl, _, sbb_toNat _ _ _⟩
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  rw [hI.mem] at hr
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide),
    by rw [hm', hm, hI.mem], h14, ⟨c', d + 2 ^ (64 * j) * r.toNat, (k'.gpr (by decide)).trans h₁, ?_, ?_⟩⟩
  · have := Nat.mul_le_mul_left (2 ^ (64 * j)) (show r.toNat + 1 ≤ 2 ^ 64 from r.isLt)
    rw [pow64_succ]; rw [Nat.mul_add, Nat.mul_one] at this; omega
  · simp only [wv]
    rw [pow64_succ]
    grind

theorem sub_toNat' (a b : BitVec 64) :
    (a - b).toNat + b.toNat = a.toNat + 2 ^ 64 * (decide (a.toNat < b.toNat)).toNat := by
  have := sbb_toNat a b false
  simpa using this

theorem sbb_self (x : BitVec 64) (c : Bool) : x - x - (BitVec.ofBool c).setWidth 64 = mask c := by
  rw [BitVec.sub_self]; rfl

theorem or1_toNat (x : BitVec 64) : (x ||| 1).toNat = x.toNat + (1 - x.toNat % 2) := by
  rw [BitVec.toNat_or, show (1 : BitVec 64).toNat = 1 from rfl]
  have h1 : (x.toNat ||| 1) / 2 = x.toNat / 2 := by
    have := Nat.or_div_two_pow (a := x.toNat) (b := 1) (n := 1); simpa using this
  have h2 : (x.toNat ||| 1) % 2 = 1 := Nat.or_mod_two_eq_one.mpr (Or.inr rfl)
  omega

theorem sx1' : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide

theorem mask_not' (b : Bool) : mask b ^^^ BitVec.allOnes 64 = mask (!b) := by cases b <;> decide

/-- The masks of `x ≥ 2` (`r15`) and `(x | 1) < c` (`rbp`). -/
theorem witCmp_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hbx : s.gpr .rbx = off B (slot w aX)) (h12 : s.gpr .r12 = BitVec.ofNat 64 w)
    (hlow : s.gpr .rbp = 0 ↔ wv s.mem B (slot w aX) w ≤ 1) :
    WP isa (seqs [.block [.alu .cmp .rbp (.imm 1), .alu .sbb .r15 (.reg .r15),
        .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1))), .mov .r10 (.mem (hdr (sArr aN))), .mov .rax (.mem (at0 .rbx)),
        .alu .or .rax (.imm 1), .alu .sub .rax (.mem (at0 .r10)), cfToRbp],
      wordLoop 1 cmpBody]) s fun t =>
      t.gpr .r15 = mask (decide (2 ≤ wv s.mem B (slot w aX) w)) ∧
      t.gpr .rbp = mask (decide (wv s.mem B (slot w aX) w + (1 - wv s.mem B (slot w aX) w % 2) <
        wv s.mem B (slot w aN) w)) ∧
      t.mem = s.mem ∧ Keep [.rax, .rbp, .r10, .r14, .r15] s t := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have sX := Nat.le_trans (slot_le (w := w) (show aX < 8 by decide)) hZ
  have sN := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have hx2 : wv s.mem B (slot w aX) w % 2 = (word s.mem B (slot w aX)).toNat % 2 := by
    have := wv_low s.mem B (slot w aX) (w - 1)
    rw [show w - 1 + 1 = w by omega] at this; omega
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.r15, .r10, .rax, .rbp] (Q := fun t =>
      t.gpr .r15 = mask (decide (2 ≤ wv s.mem B (slot w aX) w)) ∧ t.gpr .r10 = off B (slot w aN) ∧
      t.gpr .rbp = mask (decide ((word s.mem B (slot w aX) ||| 1).toNat < (word s.mem B (slot w aN)).toNat)) ∧
      ((word s.mem B (slot w aX) ||| 1) - word s.mem B (slot w aN)).toNat + (word s.mem B (slot w aN)).toNat =
        (word s.mem B (slot w aX) ||| 1).toNat +
          2 ^ 64 * (decide ((word s.mem B (slot w aX) ||| 1).toNat < (word s.mem B (slot w aN)).toNat)).toNat ∧
      t.mem = s.mem) (by
    unfold cfToRbp
    xrun [State.ea, hdr, at0, hg.rdi, hdrOff, hl (sArr aN) (by decide), hg.hdr.harr aN (by decide), hbx,
      show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, hg.scr.ld (d := slot w aX) (by omega),
      hg.scr.ld (d := slot w aN) (by omega), sx1', sbb_self, decide_lt_one, sub_toNat']
    refine ⟨?_, rfl⟩
    show mask (decide (s.gpr .rbp = 0)) ^^^ _ = _
    rw [sxm1', mask_not', decide_eq_decide.mpr hlow]
    congr 1
    rw [← decide_not]; exact decide_eq_decide.mpr (by omega)) rfl) fun s₁ ⟨⟨h15, h10, hbp, hd, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.2.2
  rw [or1_toNat] at hd hbp
  have hv1 : ∀ e, wv s₁.mem B e 1 = (word s.mem B e).toNat := fun e => by rw [hm₁]; simp [wv]
  refine WP.mono (wordLoop_ok (start := 1) (N := w) (by omega) hw'
    (CmpInvD s₁ B Z (slot w aX) (slot w aN) (1 - (word s.mem B (slot w aX)).toNat % 2))
    (fun t h14 hm k _ => ⟨hs₁.congr k.2.2, k.mono (by decide), hm, h14,
      ⟨decide ((word s.mem B (slot w aX)).toNat + (1 - (word s.mem B (slot w aX)).toNat % 2) <
        (word s.mem B (slot w aN)).toNat), ((word s.mem B (slot w aX) ||| 1) - word s.mem B (slot w aN)).toNat,
        by rw [k.gpr (by decide)]; exact hbp,
        by have := ((word s.mem B (slot w aX) ||| 1) - word s.mem B (slot w aN)).isLt; simpa using this,
        by rw [hv1, hv1]; omega⟩⟩)
    (fun j _ hj t hI => cmpStepD_ok ((k₁.gpr (by decide)).trans hbx) h10 ((k₁.gpr (by decide)).trans h12) (by omega)
      (by omega) (by omega) hj hI)) fun t hI => ?_
  obtain ⟨c, d, hc, hdl, hval⟩ := hI.val
  rw [hm₁] at hval
  refine ⟨(hI.keep.gpr (by decide)).trans h15, ?_, by rw [hI.mem, hm₁], (k₁.trans hI.keep).mono (by decide)⟩
  rw [hc, lt_of_borrow hdl hval, hx2]

theorem mask_and2 (a b : Bool) : mask a &&& mask b = mask (a && b) := by cases a <;> cases b <;> decide

theorem force_lo (x : BitVec 64) (u : Bool) : mask (!u) &&& (2 : BitVec 64) ||| x = if u then x else x ||| 2 := by
  cases u
  · simp only [Bool.not_false, mask_true, Bool.false_eq_true, ↓reduceIte, BitVec.allOnes_and]
    exact BitVec.or_comm _ _
  · simp [mask_false]

theorem force_hi (x : BitVec 64) (u : Bool) :
    (BitVec.ofNat 64 (2 ^ 63) &&& mask (!u) ^^^ BitVec.allOnes 64) &&& x =
      if u then x else x &&& ~~~(BitVec.ofNat 64 (2 ^ 63)) := by
  cases u
  · simp only [Bool.not_false, mask_true, Bool.false_eq_true, ↓reduceIte, BitVec.and_allOnes, BitVec.xor_allOnes]
    exact BitVec.and_comm _ _
  · simp only [Bool.not_true, mask_false, ↓reduceIte]
    rw [show BitVec.ofNat 64 (2 ^ 63) &&& (0 : BitVec 64) = 0 from BitVec.and_zero,
      show (0 : BitVec 64) ^^^ BitVec.allOnes 64 = BitVec.allOnes 64 from BitVec.zero_xor, BitVec.allOnes_and]

/-- The witness forced into range unless `u = a ∧ b` (the masks in `r15`
and `rbp`), and the mask of `u` into `kU`. -/
theorem witForce_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hbx : s.gpr .rbx = off B (slot w aX)) (h12 : s.gpr .r12 = BitVec.ofNat 64 w)
    {a b : Bool} (h15 : s.gpr .r15 = mask a) (hbp : s.gpr .rbp = mask b) :
    WP isa (.block [.alu .and .r15 (.reg .rbp), .store (hdr kU) .r15, .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1))),
      .mov .rax (.reg .r15), .alu .and .rax (.imm 2), .alu .or .rax (.mem (at0 .rbx)), .store (at0 .rbx) .rax,
      .movImm64 .rax (BitVec.ofNat 64 (2 ^ 63)), .alu .and .rax (.reg .r15),
      .alu .xor .rax (.imm (BitVec.ofInt 32 (-1))), .alu .and .rax (.mem (ix .rbx .r12 (-8))),
      .store (ix .rbx .r12 (-8)) .rax]) s fun t =>
      t.mem = ((s.mem.writeW (off B (8 * kU)) (mask (a && b))).writeW (off B (slot w aX))
        (if a && b then word s.mem B (slot w aX) else word s.mem B (slot w aX) ||| 2)).writeW
        (off B (slot w aX + 8 * (w - 1)))
        (if a && b then word s.mem B (slot w aX + 8 * (w - 1))
          else word s.mem B (slot w aX + 8 * (w - 1)) &&& ~~~(BitVec.ofNat 64 (2 ^ 63))) ∧
      Keep [.rax, .r15] s t := by
  have hn := hg.scr.nowrap
  have sX := Nat.le_trans (slot_le (w := w) (show aX < 8 by decide)) hZ
  have hsU : InRegions s.wr (off B (8 * kU)) 8 := hg.scr.st (by have := hdr_lt_slot w 8 (show kU < 32 by decide); omega)
  refine WP.mono (WP.keep [.rax, .r15] (Q := fun t => t.mem = ((s.mem.writeW (off B (8 * kU)) (mask (a && b))).writeW
      (off B (slot w aX)) (if a && b then word s.mem B (slot w aX) else word s.mem B (slot w aX) ||| 2)).writeW
      (off B (slot w aX + 8 * (w - 1)))
      (if a && b then word s.mem B (slot w aX + 8 * (w - 1))
        else word s.mem B (slot w aX + 8 * (w - 1)) &&& ~~~(BitVec.ofNat 64 (2 ^ 63)))) (by
    xrun [State.ea, hdr, at0, ix, hg.rdi, hdrOff, hsU, hbx, h12, h15, hbp, mask_and2, sxm1', mask_not',
      show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
      addrm8 (b := off B (slot w aX)) (i := BitVec.ofNat 64 w) rfl rfl (by omega : 1 ≤ w),
      hg.scr.ld (d := slot w aX) (by omega), hg.scr.st (d := slot w aX) (by omega),
      hg.scr.ld (d := slot w aX + 8 * (w - 1)) (by omega), hg.scr.st (d := slot w aX + 8 * (w - 1)) (by omega),
      force_lo, force_hi,
      fun X => (writeW_outside s.mem B X (d := 8 * kU) (by unfold kU sFn; omega)).word (d := slot w aX)
        (Or.inr (by unfold slot kU sFn aX hdrBytes; omega)) (by omega),
      fun X Y => ((writeW_outside _ B Y (d := slot w aX) (by omega)).word (d := slot w aX + 8 * (w - 1))
        (Or.inr (by omega)) (by omega)).trans
        ((writeW_outside s.mem B X (d := 8 * kU) (by unfold kU sFn; omega)).word (d := slot w aX + 8 * (w - 1))
        (Or.inr (by unfold slot kU sFn aX hdrBytes; omega)) (by omega))]) rfl) fun t ⟨hm, k⟩ => ⟨hm, k⟩

/-- Setting bit 1 of the low word and clearing the top bit of the top word
of a number of `w ≥ 2` words. -/
theorem wv_force {m m' : Mem} {p : Addr} {d w : Nat} (hw : 2 ≤ w)
    (h0 : word m' p d = word m p d ||| 2)
    (htop : word m' p (d + 8 * (w - 1)) = word m p (d + 8 * (w - 1)) &&& ~~~(BitVec.ofNat 64 (2 ^ 63)))
    (hmid : ∀ j, 0 < j → j < w - 1 → word m' p (d + 8 * j) = word m p (d + 8 * j)) :
    wv m' p d w = (wv m p d w ||| 2) % 2 ^ (64 * w - 1) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_or]
  have h2 : ∀ j, Nat.testBit 2 j = decide (j = 1) := fun j => by
    rcases j with _ | _ | j
    · rfl
    · rfl
    · rw [show (2 : Nat) = 2 ^ 1 from rfl, Nat.testBit_two_pow]; simp
  by_cases hi : i < 64 * w
  · rw [testBit_wv m' p d w i hi, testBit_wv m p d w i hi]
    by_cases hj0 : i / 64 = 0
    · rw [hj0, Nat.mul_zero, Nat.add_zero, h0, BitVec.toNat_or, Nat.testBit_or, show (2 : BitVec 64).toNat = 2 from rfl,
        h2, h2, show i % 64 = i by omega, decide_eq_true (show i < 64 * w - 1 by omega)]
      simp
    · by_cases hjt : i / 64 = w - 1
      · rw [hjt, htop, BitVec.toNat_and, Nat.testBit_and, BitVec.toNat_not, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show 2 ^ 63 < 2 ^ 64 by decide), h2, decide_eq_false (show ¬ i = 1 by omega)]
        rw [show 2 ^ 64 - 1 - 2 ^ 63 = 2 ^ 63 - 1 by decide, Nat.testBit_two_pow_sub_one]
        by_cases hm : i % 64 < 63
        · simp [hm, show i < 64 * w - 1 by omega]
        · simp [hm, show ¬ i < 64 * w - 1 by omega]
      · rw [hmid (i / 64) (by omega) (by omega), h2, decide_eq_false (show ¬ i = 1 by omega),
          decide_eq_true (show i < 64 * w - 1 by omega)]
        simp
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (wv_lt m' p d w) (Nat.pow_le_pow_right (by decide) (by omega))),
      decide_eq_false (show ¬ i < 64 * w - 1 by omega)]
    simp

/-- The witness from `x < 2^(64 w)` for the odd `c` with `c − 1` of
`64 w` bits. -/
theorem witness_eq {c x w : Nat} (hc : c % 2 = 1) (hb : Spec.RsaKeyGen.bitLength (c - 1) = 64 * w)
    (hx : x < 2 ^ (64 * w)) :
    Spec.RsaKeyGen.witness (c - 1) x =
      (if decide (2 ≤ x) && decide (x + (1 - x % 2) < c) then x else (x ||| 2) % 2 ^ (64 * w - 1),
        decide (2 ≤ x) && decide (x + (1 - x % 2) < c)) := by
  have e : (decide (2 ≤ x) && decide (x + (1 - x % 2) < c)) = decide (2 ≤ x ∧ x < c - 1) := by
    rw [← Bool.decide_and]; exact decide_eq_decide.mpr (by omega)
  rw [e]
  unfold Spec.RsaKeyGen.witness
  simp only [hb, Nat.mod_eq_of_lt hx]
  by_cases h : 2 ≤ x ∧ x < c - 1 <;> simp [h]

end VG.Proof.RsaKeyGen.X86_64

module

public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Base
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.LoadC
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base
import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks

/-!
# An FFDH parameter candidate on AArch64: a modulus's working space

`phase q` (`phase_ok`): for the modulus of `mb` bits (`PP.mb`: `bits − 1`
for `q`, `bits` for `p`), `sK := ⌈mb / 8⌉` and `Keys.head`'s working space
of `w = ⌈mb / 64⌉` words, the witnesses needed (`primeChecks mb`) and the
top word's mask `2^k − 1`, `k = mb − 64 (w − 1)`, by a loop of `k` steps.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-- The modulus's bit length: `bits − 1` for `q`, `bits` for `p`. -/
def PP.mb (p : PP) (q : Bool) : Nat := if q then p.bits - 1 else p.bits

/-- Its length in octets, its words, and the bits of its top word. -/
abbrev mLen (mb : Nat) : Nat := (mb + 7) / 8
abbrev mW (mb : Nat) : Nat := (mb + 63) / 64
abbrev mK (mb : Nat) : Nat := mb + 64 - 64 * mW mb

theorem wk_mLen (mb : Nat) : wk (mLen mb) = mW mb := by simp only [wk, mLen, mW]; omega

theorem PDims.mb {p : PP} (h : PDims p) (q : Bool) :
    511 ≤ p.mb q ∧ p.mb q ≤ 8192 ∧ p.bits ≤ p.mb q + 1 ∧ p.mb q ≤ p.bits := by
  have := h.b1; have := h.b2
  unfold PP.mb; cases q <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- The header words `phase` writes. -/
def phaseRanges : List (Nat × Nat) :=
  [(8 * sK, 8), (8 * fChecks, 8), (8 * sW, 8), (8 * sArr 0, 64), (8 * sStride, 8), (8 * Public.sMask, 8),
    (8 * fTop, 8)]

theorem phaseRanges_mut : ∀ r ∈ phaseRanges, PMut r := by
  simp only [phaseRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only [PMut, sK, fChecks, sW, sArr, sStride, Public.sMask, fTop, sFn] <;> omega

theorem phaseRanges_kmut : ∀ r ∈ phaseRanges, r.1 + r.2 ≤ 8 * 32 := by
  simp only [phaseRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    simp only [sK, fChecks, sW, sArr, sStride, Public.sMask, fTop, sFn] <;> omega

/-- The common part of `phaseHead`, from `mb` in `x3`. -/
def phaseRest : List Instr :=
  [.addImm .x .x4 .x3 7, .lsr .x .x4 .x4 3, sth .x4 sK, .addImm .x .x6 .x3 63, .lsr .x .x6 .x6 6,
    .lsl .x .x6 .x6 6, .addImm .x .x8 .x3 64, .sub .x .x6 .x8 .x6, movi .x5 64, movi .x9 128, movi .x8 2049,
    .subs .x .x8 .x3 .x8, .csel .x .x5 .x9 .x5, sth .x5 fChecks]

theorem phaseHead_eq (q : Bool) :
    phaseHead q = ([ldh .x3 fBits] ++ (if q then [.subImm .x .x3 .x3 1] else [])) ++ phaseRest := by
  simp only [phaseHead, phaseRest, List.append_assoc]

theorem shr_ofNat (a k : Nat) : BitVec.ofNat 64 a >>> k = BitVec.ofNat 64 (a % 2 ^ 64 / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (Nat.two_pow_pos _)))]

theorem imm16 {n : Nat} (hn : n < 65536) : (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- `phaseRest`, from `mb` in `x3`. -/
theorem phaseRest_ok {s : State} {B : Addr} {Z mb : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (hZ : 8 * 32 ≤ Z) (h3 : s.gpr .x3 = BitVec.ofNat 64 mb) (hmb : mb ≤ 8192) :
    WP isa (.block phaseRest) s fun t =>
      (t.gpr .x6 = BitVec.ofNat 64 (mK mb) ∧
        t.mem = (s.mem.writeW (off B (8 * sK)) (BitVec.ofNat 64 (mLen mb))).writeW (off B (8 * fChecks))
          (BitVec.ofNat 64 (Spec.Ffdh.primeChecks mb))) ∧
      Keep [.x4, .x5, .x6, .x8, .x9] s t := by
  have hn := hs.nowrap
  refine WP.keep [.x4, .x5, .x6, .x8, .x9] ?_ (by decide) (by decide) (by decide +kernel)
  have e1 : (BitVec.ofNat 64 mb + BitVec.ofNat 64 7) >>> 3 = BitVec.ofNat 64 (mLen mb) := by
    rw [ofNat_add_ofNat, shr_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp only [mLen, Nat.reducePow]
  have e2 : ((BitVec.ofNat 64 mb + BitVec.ofNat 64 63) >>> 6) <<< 6 = BitVec.ofNat 64 (64 * mW mb) := by
    rw [ofNat_add_ofNat, shr_ofNat, Nat.mod_eq_of_lt (by omega), shl_ofNat (by simp only [Nat.reducePow]; omega)]
    congr 1; simp only [mW, Nat.reducePow]; omega
  have e3 : BitVec.ofNat 64 mb + BitVec.ofNat 64 64 - BitVec.ofNat 64 (64 * mW mb) = BitVec.ofNat 64 (mK mb) := by
    rw [ofNat_add_ofNat]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, mK, mW]
    omega
  have e4 : (if decide (2 ^ 64 ≤ (BitVec.ofNat 64 mb).toNat + (~~~BitVec.ofNat 64 2049).toNat + true.toNat) = true
      then BitVec.ofNat 64 128 else BitVec.ofNat 64 64) = BitVec.ofNat 64 (Spec.Ffdh.primeChecks mb) := by
    rw [subs_ge (show mb < 2 ^ 64 by omega) (show 2049 < 2 ^ 64 by decide)]
    unfold Spec.Ffdh.primeChecks
    by_cases hc : 2049 ≤ mb
    · simp only [decide_eq_true hc, ite_true, show ¬ mb ≤ 2048 by omega, ite_false]
    · simp only [decide_eq_false hc, Bool.false_eq_true, ite_false, show mb ≤ 2048 by omega, ite_true]
  brun [phaseRest, h0, h3, imm16 (show 64 < 65536 by decide), imm16 (show 128 < 65536 by decide),
    imm16 (show 2049 < 65536 by decide), hdr_enc (show sK < 32 by decide), hdr_enc (show fChecks < 32 by decide),
    hs.st (d := 8 * sK) (by simp only [sK, sFn]; omega), hs.st (d := 8 * fChecks) (by simp only [fChecks]; omega),
    e1, e2, e3, e4]


/-- `bits` (less one for `q`) into `x3`. -/
theorem phaseLoad_ok {s : State} {p : PP} (h : PH p s) (q : Bool) :
    WP isa (.block ([ldh .x3 fBits] ++ (if q then [.subImm .x .x3 .x3 1] else []))) s fun t =>
      (t.gpr .x3 = BitVec.ofNat 64 (p.mb q) ∧ t.mem = s.mem) ∧ Keep [.x3] s t := by
  have hs := h.scr
  have hZ := h.dims.z
  have hb1 := h.dims.b1
  refine WP.keep [.x3] ?_ (by cases q <;> decide) (by cases q <;> rfl) (by cases q <;> decide +kernel)
  have hl : InRegions (s.rd ++ s.wr) (off p.B (8 * fBits)) 8 := hs.ld (by simp only [fBits, sFn]; omega)
  cases q
  · brun [h.x0, hdr_enc (show fBits < 32 by decide), hl, h.args.bits, PP.mb]
  · brun [h.x0, hdr_enc (show fBits < 32 by decide), hl, h.args.bits, PP.mb,
      ofNat_sub_one' (show 1 ≤ p.bits by omega) (show p.bits < 2 ^ 64 by have := h.dims.b2; omega)]

/-- One step of the mask's loop. -/
theorem maskStep_ok (t : State) {i : Nat} (h9 : t.gpr .x9 = BitVec.ofNat 64 (2 ^ i - 1)) :
    WP isa (.block (([.add .x .x9 .x9 .x9, .addImm .x .x9 .x9 1] : List Instr) ++ ([.subImm .x .x6 .x6 1] : List Instr))) t fun t' =>
      (t'.gpr .x9 = BitVec.ofNat 64 (2 ^ (i + 1) - 1) ∧ t'.mem = t.mem ∧ Keep [.x9, .x6] t t') ∧
        t'.gpr .x6 = t.gpr .x6 - BitVec.ofNat 64 1 := by
  refine WP.mono (WP.keep [.x9, .x6] (Q := fun t' => t'.gpr .x9 = BitVec.ofNat 64 (2 ^ (i + 1) - 1) ∧
    t'.mem = t.mem ∧ t'.gpr .x6 = t.gpr .x6 - BitVec.ofNat 64 1) ?_ (by decide) (by decide) (by decide +kernel))
    fun t' ⟨⟨a, b, c⟩, k⟩ => ⟨⟨a, b, k⟩, c⟩
  have e : BitVec.ofNat 64 (2 ^ i - 1) + BitVec.ofNat 64 (2 ^ i - 1) + BitVec.ofNat 64 1 =
      BitVec.ofNat 64 (2 ^ (i + 1) - 1) := by
    rw [ofNat_add_ofNat, ofNat_add_ofNat]
    congr 1
    have := Nat.two_pow_pos i
    rw [Nat.pow_succ]; omega
  brun [h9, e]

/-- The mask loop: `x9 := 2^k − 1` from `x9 = 0` and `x6 = k`. -/
theorem maskLoop_ok {s : State} {k : Nat} (hk1 : 1 ≤ k) (hk : k ≤ 64) (h9 : s.gpr .x9 = 0)
    (h6 : s.gpr .x6 = BitVec.ofNat 64 k) :
    WP isa (countLoop .x6 [.add .x .x9 .x9 .x9, .addImm .x .x9 .x9 1]) s fun t =>
      t.gpr .x9 = BitVec.ofNat 64 (2 ^ k - 1) ∧ t.mem = s.mem ∧ Keep [.x9, .x6] s t := by
  unfold countLoop
  exact wp_countdown (N := k) (by omega) (by omega)
    (fun i t => t.gpr .x9 = BitVec.ofNat 64 (2 ^ i - 1) ∧ t.mem = s.mem ∧ Keep [.x9, .x6] s t)
    (fun i _ t ⟨h9', hm, k'⟩ _ => WP.mono (maskStep_ok t h9') fun t' ⟨⟨a, b, c⟩, d⟩ =>
      ⟨⟨a, b.trans hm, (k'.trans c).mono (by decide)⟩, d⟩)
    ⟨by rw [h9]; rfl, rfl, Keep.refl _ _⟩ h6

/-- `phase q`'s first block: the registers its loop and its end use. -/
theorem phaseBlk_ok {s : State} {p : PP} (h : PH p s) (q : Bool) :
    WP isa (.block (phaseHead q ++ Keys.head ++ [movi .x9 0])) s fun t =>
      ∀ r ∈ [Reg.x0, .x6, .x9], t.gpr r = (fun r => match r with
        | .x0 => p.B | .x6 => BitVec.ofNat 64 (mK (p.mb q)) | _ => 0) r := by
  have hs := h.scr
  have hn := hs.nowrap
  have hZ := h.dims.z
  obtain ⟨hm1, hm2, hm3, hm4⟩ := h.dims.mb q
  generalize hmb : p.mb q = mb at hm1 hm2 hm3 hm4
  have hZ' : 8 * 32 ≤ p.Z := by omega
  rw [phaseHead_eq, List.append_assoc, List.append_assoc]
  refine WP.block_append_iff.mpr (WP.mono (phaseLoad_ok h q) fun s₁ ⟨⟨h3₁, hm₁⟩, k₁⟩ => ?_)
  rw [hmb] at h3₁
  rw [WP.block_append_iff]
  refine WP.mono (phaseRest_ok (hs.congr k₁.wr) ((k₁.gpr .x0 (by decide)).trans h.x0) hZ' h3₁ hm2)
    fun s₂ ⟨⟨h6₂, hm₂⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.wr
  have hK₂ : word s₂.mem p.B (8 * sK) = BitVec.ofNat 64 (mLen mb) := by
    rw [hm₂, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  rw [WP.block_append_iff]
  refine WP.mono (kHead_ok hs₂ ((k12.gpr .x0 (by decide)).trans h.x0) (by simp only [mLen]; omega)
    (by simp only [mLen]; omega) (by simp only [mLen, PP.L] at hZ ⊢; omega) hK₂)
    fun s₃ ⟨hws₃, _, _, k₃⟩ => ?_
  have i0 := imm16 (show 0 < 65536 by decide)
  refine WP.mono (WP.keep [.x9] (Q := fun t => t.gpr .x9 = 0 ∧ t.mem = s₃.mem) (by brun [i0])
    (by decide) (by decide) (by decide +kernel)) fun s₄ ⟨⟨h9₄, _⟩, k₄⟩ => ?_
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (k₄.gpr .x0 (by decide)).trans hws₃.x0
  · exact (k₄.gpr .x6 (by decide)).trans ((k₃.gpr .x6 (by decide)).trans h6₂)
  · exact h9₄

/-- After `phase q`. -/
structure PhasePost (p : PP) (q : Bool) (s t : State) : Prop where
  st : PSt p (mW (p.mb q)) t
  len : word t.mem p.B (8 * sK) = BitVec.ofNat 64 (mLen (p.mb q))
  checks : word t.mem p.B (8 * fChecks) = BitVec.ofNat 64 (Spec.Ffdh.primeChecks (p.mb q))
  top : word t.mem p.B (8 * fTop) = BitVec.ofNat 64 (2 ^ mK (p.mb q) - 1)
  mask : word t.mem p.B (8 * Public.sMask) = mask true
  frm : Frm p.B phaseRanges s.mem t.mem
  keep : Keep mmRegs s t

theorem phase_ok {s : State} {p : PP} (h : PH p s) (q : Bool) :
    WP isa (seqs (phase q)) s (PhasePost p q s) := by
  have hs := h.scr
  have hn := hs.nowrap
  have hZ := h.dims.z
  obtain ⟨hm1, hm2, hm3, hm4⟩ := h.dims.mb q
  generalize hmb : p.mb q = mb at hm1 hm2 hm3 hm4
  have hZ' : 8 * 32 ≤ p.Z := by omega
  simp only [phase, seqs]
  rw [phaseHead_eq, List.append_assoc, List.append_assoc]
  refine WP.seq (WP.block_append_iff.mpr (WP.mono (phaseLoad_ok h q) fun s₁ ⟨⟨h3₁, hm₁⟩, k₁⟩ => ?_))
  rw [hmb] at h3₁
  rw [WP.block_append_iff]
  refine WP.mono (phaseRest_ok (hs.congr k₁.wr) ((k₁.gpr .x0 (by decide)).trans h.x0) hZ' h3₁ hm2)
    fun s₂ ⟨⟨h6₂, hm₂⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.wr
  have hK₂ : word s₂.mem p.B (8 * sK) = BitVec.ofNat 64 (mLen mb) := by
    rw [hm₂, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  rw [WP.block_append_iff]
  refine WP.mono (kHead_ok hs₂ ((k12.gpr .x0 (by decide)).trans h.x0) (by simp only [mLen]; omega)
    (by simp only [mLen]; omega) (by simp only [mLen, PP.L] at hZ ⊢; omega) hK₂)
    fun s₃ ⟨hws₃, hmask₃, hf₃, k₃⟩ => ?_
  rw [wk_mLen] at hws₃
  have i0 := imm16 (show 0 < 65536 by decide)
  refine WP.mono (WP.keep [.x9] (Q := fun t => t.gpr .x9 = 0 ∧ t.mem = s₃.mem) (by brun [i0])
    (by decide) (by decide) (by decide +kernel)) fun s₄ ⟨⟨h9₄, hm₄⟩, k₄⟩ => ?_
  have h6₄ : s₄.gpr .x6 = BitVec.ofNat 64 (mK mb) := (k₄.gpr .x6 (by decide)).trans ((k₃.gpr .x6 (by decide)).trans h6₂)
  refine WP.seq (WP.mono (maskLoop_ok (by simp only [mK, mW]; omega) (by simp only [mK, mW]; omega) h9₄ h6₄)
    fun s₅ ⟨h9₅, hm₅, k₅⟩ => ?_)
  have k25 := (k₃.trans k₄).trans k₅
  have hs₅ := hs₂.congr k25.wr
  have h0₅ : s₅.gpr .x0 = p.B := ((k12.trans k25).gpr .x0 (by decide)).trans h.x0
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s₅.mem.writeW (off p.B (8 * fTop)) (BitVec.ofNat 64 (2 ^ mK mb - 1)))
    (by brun [h0₅, hdr_enc (show fTop < 32 by decide), hs₅.st (d := 8 * fTop) (by simp only [fTop]; omega), h9₅])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨hm, k₆⟩ => ?_
  have hm35 : s₅.mem = s₃.mem := hm₅.trans hm₄
  -- The frame.
  have f₂ : Frm p.B phaseRanges s.mem s₂.mem := by
    rw [hm₂, hm₁]
    exact (Frm.of_outside (writeW_outside _ _ _ (by simp only [sK, sFn]; omega)) (by simp [phaseRanges])).trans
      (Frm.of_outside (writeW_outside _ _ _ (by simp only [fChecks]; omega)) (by simp [phaseRanges]))
  have f₃ : Frm p.B phaseRanges s₂.mem s₃.mem := hf₃.mono (by simp [phaseRanges])
  have f₆ : Frm p.B phaseRanges s₅.mem t.mem := by
    rw [hm]; exact Frm.of_outside (writeW_outside _ _ _ (by simp only [fTop]; omega)) (by simp [phaseRanges])
  have hf : Frm p.B phaseRanges s.mem t.mem := (f₂.trans f₃).trans (by rw [hm35] at f₆; exact f₆)
  have k16 := ((k12.trans k25).trans k₆)
  have hws : Ws t p.B p.Z (mW mb) := hws₃.congr' (rs := [(8 * fTop, 8)]) (by
      rw [hm, hm35]; exact Frm.of_outside (writeW_outside _ _ _ (by simp only [fTop]; omega)) (by simp))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact KMut.hdr (by simp only [fTop, sW]; omega))
    (k₄.trans (k₅.trans k₆)) (by decide)
  have hw36 : ∀ i < 32, i ≠ fTop → word t.mem p.B (8 * i) = word s₃.mem p.B (8 * i) := fun i hi hne => by
    rw [hm, hm35]; exact hdrStore_hdr _ _ _ (by decide) hi (Ne.symm hne)
  have hw23 : ∀ i, i = sK ∨ i = fChecks → word s₃.mem p.B (8 * i) = word s₂.mem p.B (8 * i) := fun i hi =>
    hf₃.word_eq (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hi with rfl | rfl <;> rcases hr with rfl | rfl | rfl | rfl <;>
        simp only [sK, sW, sArr, sStride, Public.sMask, fChecks, sFn] <;> omega)
      (by rcases hi with rfl | rfl <;> simp only [sK, fChecks, sFn] <;> omega)
  subst hmb
  refine ⟨⟨hws, h.args.frm hf phaseRanges_mut, h.src.congrK (InScr.of_frm hf fun r hr => by
      have := phaseRanges_kmut r hr; omega) k16, h.ou.congr k16.wr, h.dims⟩, ?_, ?_, ?_, ?_, hf,
    k16.mono (by decide)⟩
  · rw [hw36 _ (by decide) (by decide), hw23 _ (.inl rfl), hK₂]
  · rw [hw36 _ (by decide) (by decide), hw23 _ (.inr rfl), hm₂, word_writeW_self]
  · rw [hm, word_writeW_self]
  · rw [hw36 _ (by decide) (by decide)]; exact hmask₃

end VG.Proof.Ffdh.AArch64.ParameterCandidate

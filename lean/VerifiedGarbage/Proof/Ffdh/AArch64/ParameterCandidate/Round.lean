module

public import VerifiedGarbage.Proof.MillerRabin.AArch64.Kernel
public import VerifiedGarbage.Proof.Ffdh.AArch64.ParameterCandidate.Base
public import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.SharedRound
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Ffdh.MillerRabin

/-!
# An FFDH parameter candidate on AArch64: a round

`round` (`round_ok`): an accepted witness `a` in Montgomery form, the shared
round (`Kernel.ok`, whose result is FFDH's `mrRound`: `rsa_round_eq`), then
`kStat := 2` for a failing witness, else the passing witnesses counted and
`kStat` 4 or, once there are `fChecks` of them, 1.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.ParameterCandidate

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.AArch64.Candidate VG.Impl.Ffdh.AArch64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MillerRabin.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY aOne sK sCnt)

/-- What a round changes. -/
def rdRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2))] ++
    Caller.callRanges w ++ [(8 * fIdx, 8), (8 * kStat, 8)]

theorem mm3_shape (w : Nat) : VG.Proof.RsaKeyGen.RangeShape w [] [(2, 1), (3, 1), (5, 1)]
    [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2))] := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact .inr ⟨(2, 1), by decide, by simp only [slot, hdrBytes, aAcc]; omega, by simp only [slot, hdrBytes, aAcc]; omega⟩
  · exact .inr ⟨(3, 1), by decide, by simp only [slot, hdrBytes, aTmp]; omega, by simp only [slot, hdrBytes, aTmp]; omega⟩
  · exact .inr ⟨(5, 1), by decide, by simp only [slot, hdrBytes, aXm]; omega, by simp only [slot, hdrBytes, aXm]; omega⟩

theorem rdRanges_shape (w : Nat) : VG.Proof.RsaKeyGen.RangeShape w
    ([] ++ [(8, 8), (184, 8), (208, 8), (232, 8), (240, 8)] ++ [(8 * fIdx, 8), (8 * kStat, 8)])
    ([(2, 1), (3, 1), (5, 1)] ++ [(7, 1), (2, 1), (3, 1), (5, 1), (6, 1), (8, 1), (11, 16)] ++ [])
    (rdRanges w) :=
  VG.Proof.RsaKeyGen.shape_append (VG.Proof.RsaKeyGen.shape_append (mm3_shape w) (sharedKernel_shape w))
    (VG.Proof.RsaKeyGen.shape_self w _)

/-- A header word a round keeps. -/
theorem rdRanges_hdr (w : Nat) {k : Nat} (hk : k ∈ [0, 2, 16, 17, 18, 19, 20, 21, 22, 24, 25, 27]) :
    ∀ r ∈ rdRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact VG.Proof.RsaKeyGen.hdr_of_shape (rdRanges_shape w) (by decide) (by decide)

/-- An array a round keeps. -/
theorem rdRanges_arr (w : Nat) {j : Nat} (hj : j ∈ [aN, aR2, aR1, aRm1]) :
    ∀ r ∈ rdRanges w, slot w j + 8 * (w + 2) ≤ r.1 ∨ r.1 + r.2 ≤ slot w j := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl <;>
    exact VG.Proof.RsaKeyGen.arr_of_shape (rdRanges_shape w) (by decide) (by decide) (Nat.le_refl _)

theorem rdRanges_lt (w : Nat) : ∀ r ∈ rdRanges w, r.1 + r.2 ≤ slot w aE := by
  intro r hr
  rcases (rdRanges_shape w) r hr with h | ⟨q, hq, _, h2⟩
  · exact Nat.le_trans ((by decide : ∀ h ∈ ([] ++ [(8, 8), (184, 8), (208, 8), (232, 8), (240, 8)] ++
      [(8 * fIdx, 8), (8 * kStat, 8)] : List (Nat × Nat)), h.1 + h.2 ≤ hdrBytes) r h)
      (show hdrBytes ≤ slot w aE by unfold slot; exact Nat.le_add_right _ _)
  · refine Nat.le_trans h2 (VG.Proof.RsaKeyGen.slot_le_slot ?_)
    exact (by decide : ∀ q ∈ ([(2, 1), (3, 1), (5, 1)] ++ [(7, 1), (2, 1), (3, 1), (5, 1), (6, 1), (8, 1),
      (11, 16)] ++ [] : List (Nat × Nat)), q.1 + q.2 ≤ aE) q hq

theorem rdRanges_pmut (w : Nat) : ∀ r ∈ rdRanges w, PMut r := by
  intro r hr
  rcases (rdRanges_shape w) r hr with h | ⟨q, _, h1, _⟩
  · have := (by decide : ∀ h ∈ ([] ++ [(8, 8), (184, 8), (208, 8), (232, 8), (240, 8)] ++
      [(8 * fIdx, 8), (8 * kStat, 8)] : List (Nat × Nat)), 8 * 26 ≤ h.1 ∨ h.1 + h.2 ≤ 8 * 16 ∨
      (8 * 18 ≤ h.1 ∧ h.1 + h.2 ≤ 8 * 19) ∨ (8 * 22 ≤ h.1 ∧ h.1 + h.2 ≤ 8 * 24)) r h
    exact this
  · exact Or.inl (Nat.le_trans (by unfold slot hdrBytes; omega) h1)

/-- The end of a round. -/
theorem rdTail_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w)
    {f : Bool} {i K : Nat} (hF : word s.mem B (8 * kFlag) = mask f) (hI : word s.mem B (8 * fIdx) = BitVec.ofNat 64 i)
    (hC : word s.mem B (8 * fChecks) = BitVec.ofNat 64 K) (hi : i < 2 ^ 62) (hK : K < 2 ^ 62) :
    WP isa (seqs [.block [ldh .x3 kFlag],
      .ite (.zero .x .x3) (.block [movi .x3 2, sth .x3 kStat])
        (.block [ldh .x3 fIdx, ldh .x4 fChecks, .addImm .x .x3 .x3 1, .subs .x .x5 .x3 .x4, movi .x6 4, movi .x7 1,
          .csel .x .x5 .x7 .x6, sth .x3 fIdx, sth .x5 kStat])]) s fun t =>
      t.mem = (if f then (s.mem.writeW (off B (8 * fIdx)) (BitVec.ofNat 64 (i + 1))).writeW (off B (8 * kStat))
          (BitVec.ofNat 64 (if i + 1 < K then 4 else 1))
        else s.mem.writeW (off B (8 * kStat)) (BitVec.ofNat 64 2)) ∧ Keep mmRegs s t := by
  have hs := h.scr
  have hn := hs.nowrap
  have h256 := h.h256
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = mask f ∧ t.mem = s.mem) (by
    brun [h.x0, hdr_enc (show kFlag < 32 by decide), hs.ld (d := 8 * kFlag) (by simp only [kFlag, kPlen, sFn]; omega),
      hF]) (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨⟨h3₁, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.wr
  have h0₁ : s₁.gpr .x0 = B := (k₁.gpr .x0 (by decide)).trans h.x0
  refine WP.ite (!f) (by rw [eval_zero, h3₁]; cases f <;> decide) (fun hf => ?_) (fun hf => ?_)
  · simp only [Bool.not_eq_true'] at hf
    refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s.mem.writeW (off B (8 * kStat)) (BitVec.ofNat 64 2)) (by
      brun [h0₁, hdr_enc (show kStat < 32 by decide), hs₁.st (d := 8 * kStat) (by simp only [kStat, sFn]; omega), hm₁]
      rfl) (by decide) (by decide) (by decide +kernel))
      fun t ⟨hm, k⟩ => ⟨by rw [hm, hf]; rfl, (k₁.trans k).mono (by decide)⟩
  · simp only [Bool.not_eq_false'] at hf
    have hI' : s₁.mem.readW (B + BitVec.ofNat 64 (8 * fIdx)) 64 = BitVec.ofNat 64 i := by rw [hm₁]; exact hI
    have hC' : s₁.mem.readW (B + BitVec.ofNat 64 (8 * fChecks)) 64 = BitVec.ofNat 64 K := by rw [hm₁]; exact hC
    refine WP.mono (WP.keep [.x3, .x4, .x5, .x6, .x7] (Q := fun t => t.mem =
        (s₁.mem.writeW (off B (8 * fIdx)) (BitVec.ofNat 64 (i + 1))).writeW (off B (8 * kStat))
          (BitVec.ofNat 64 (if i + 1 < K then 4 else 1))) (by
      brun [h0₁, hdr_enc (show fIdx < 32 by decide), hdr_enc (show fChecks < 32 by decide),
        hdr_enc (show kStat < 32 by decide), hs₁.ld (d := 8 * fIdx) (by simp only [fIdx]; omega),
        hs₁.ld (d := 8 * fChecks) (by simp only [fChecks]; omega),
        hs₁.st (d := 8 * fIdx) (by simp only [fIdx]; omega), hs₁.st (d := 8 * kStat) (by simp only [kStat, sFn]; omega),
        hI', hC', subs_carry]
      have e1 : BitVec.ofNat 64 i + 1#64 = BitVec.ofNat 64 (i + 1) := (BitVec.ofNat_add _ _).symm
      rw [e1, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show K < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show i + 1 < 2 ^ 64 by omega)]
      by_cases hc : i + 1 < K
      · rw [decide_eq_false (by omega)]; simp only [hc, Bool.false_eq_true, ↓reduceIte]; rfl
      · rw [decide_eq_true (by omega)]; simp only [hc, ↓reduceIte]; rfl) (by decide) (by decide) (by decide +kernel))
      fun t ⟨hm, k⟩ => ⟨by rw [hm, hm₁, hf]; rfl, (k₁.trans k).mono (by decide)⟩

/-- A round of an accepted witness `a`. -/
theorem round_ok (M : Mont) (R : Kernel) {s : State} {B : Addr} {Z w c bm a i K : Nat} (hw4 : 4 ≤ w)
    (hw128 : w ≤ 128) (hEZ : slot w aE + 8 * (w + 2) ≤ Z) (hc : MrCtx s B Z w c bm) (he : ECtx s.mem B w c)
    (hR2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c) (hodd : c % 2 = 1) (hc3 : 3 ≤ c)
    (hx : wv s.mem B (slot w aX) w = a) (ha : a < c)
    (hI : word s.mem B (8 * fIdx) = BitVec.ofNat 64 i) (hC : word s.mem B (8 * fChecks) = BitVec.ofNat 64 K)
    (hi : i < 2 ^ 62) (hK : K < 2 ^ 62) :
    WP isa (seqs (VG.Impl.Ffdh.AArch64.ParameterCandidate.round M.mm R.run)) s fun t =>
      (∃ bm', MrCtx t B Z w c bm') ∧ ECtx t.mem B w c ∧
      word t.mem B (8 * kStat) = BitVec.ofNat 64
        (if Proof.MillerRabin.Round.round c a then (if i + 1 < K then 4 else 1) else 2) ∧
      word t.mem B (8 * fIdx) = BitVec.ofNat 64 (if Proof.MillerRabin.Round.round c a then i + 1 else i) ∧
      Frm B (rdRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.ws.scr.nowrap
  have hZ := hc.ws.hZ
  have hw' : w < 2 ^ 31 := by omega_using [hw128]
  have hRc : Nat.Coprime (2 ^ (64 * w)) c := VG.Proof.Bignum.coprime_pow2 hodd _
  have hc0 : 0 < c := by omega_using [hc3]
  simp only [VG.Impl.Ffdh.AArch64.ParameterCandidate.round]
  refine wp_seqs_append (by simp) (by simp) ?_
  refine wp_seqs_append (by simp) R.nonempty ?_
  simp only [seqs_one]
  -- `a R mod c` into `aXm`.
  have hg := hc.good
  refine WP.mono (M.mm_ok hg.1 hg.2 hc.ws.w1 hw' (o := aXm) (a := aX) (b := aR2) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
    (by rw [hR2, hc.n]; exact Nat.mod_lt _ hc0)) fun s₁ ⟨_, hlt₁, hy₁, ha₁, k₁⟩ => ?_
  rw [hc.n] at hlt₁ hy₁
  rw [hx, hR2] at hy₁
  have hXm : wv s₁.mem B (slot w aXm) w = a % c * 2 ^ (64 * w) % c := by
    rw [← Nat.mod_eq_of_lt hlt₁, Nat.mod_eq_of_lt ha]
    refine VG.Proof.Bignum.mont_cancel hRc ?_
    rw [hy₁, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]
  have f₁ : Frm B [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2))]
      s.mem s₁.mem := Frm.of_arrays ha₁ (by simp)
  have hc₁ : MrCtx s₁ B Z w c bm := hc.of_frm f₁ (by kmut) k₁ (by decide) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
  have he₁ : ECtx s₁.mem B w c := he.of_frm f₁ (fun r hr => Or.inr (rdRanges_lt w r (by
    simp only [rdRanges]; exact List.mem_append_left _ (List.mem_append_left _ hr)))) (by omega_arith)
  have hI₁ : word s₁.mem B (8 * fIdx) = BitVec.ofNat 64 i := by
    rw [f₁.word_eq (VG.Proof.RsaKeyGen.hdr_of_shape (mm3_shape w) (by decide) (by decide))
      (by simp only [fIdx]; omega_arith)]; exact hI
  have hC₁ : word s₁.mem B (8 * fChecks) = BitVec.ofNat 64 K := by
    rw [f₁.word_eq (VG.Proof.RsaKeyGen.hdr_of_shape (mm3_shape w) (by decide) (by decide))
      (by simp only [fChecks]; omega_arith)]; exact hC
  -- The round.
  refine WP.mono (R.ok hc₁ he₁ hw4 hw128 hEZ hodd hc3 hXm) fun s₂ ⟨⟨bm₂, hc₂⟩, he₂, hf₂, f₂, k₂⟩ => ?_
  have hI₂ : word s₂.mem B (8 * fIdx) = BitVec.ofNat 64 i := by
    rw [f₂.word_eq (VG.Proof.RsaKeyGen.hdr_of_shape (sharedKernel_shape w) (by decide) (by decide))
      (by simp only [fIdx]; omega_arith)]; exact hI₁
  have hC₂ : word s₂.mem B (8 * fChecks) = BitVec.ofNat 64 K := by
    rw [f₂.word_eq (VG.Proof.RsaKeyGen.hdr_of_shape (sharedKernel_shape w) (by decide) (by decide))
      (by simp only [fChecks]; omega_arith)]; exact hC₁
  generalize Proof.MillerRabin.Round.round c a = f at hf₂ ⊢
  refine WP.mono (rdTail_ok hc₂.ws hf₂ hI₂ hC₂ hi hK) fun t ⟨hm, k⟩ => ?_
  have hft : Frm B [(8 * fIdx, 8), (8 * kStat, 8)] s₂.mem t.mem := by
    rw [hm]
    cases f <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact Frm.of_outside (writeW_outside _ B _ (d := 8 * kStat) (by decide)) (by simp)
    · exact (Frm.of_outside (writeW_outside s₂.mem B _ (d := 8 * fIdx) (by decide)) (by simp)).trans
        (Frm.of_outside (writeW_outside _ B _ (d := 8 * kStat) (by decide)) (by simp))
  refine ⟨⟨bm₂, hc₂.of_frm hft (by kmut) k (by decide) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)⟩,
    he₂.of_frm hft (fun r hr => Or.inr (rdRanges_lt w r (by
      simp only [rdRanges]; exact List.mem_append_right _ hr))) (by omega_arith), ?_, ?_, ?_,
    ((k₁.trans k₂).trans k).mono (by decide)⟩
  · rw [hm]; cases f <;> simp only [↓reduceIte, Bool.false_eq_true, word_writeW_self]
  · rw [hm]
    cases f
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact hI₂
    · simp only [↓reduceIte]
      rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · simp only [rdRanges]
    exact ((f₁.mono fun r hr => List.mem_append_left _ (List.mem_append_left _ hr)).trans
      (f₂.mono fun r hr => List.mem_append_left _ (List.mem_append_right _ hr))).trans
      (hft.mono fun r hr => List.mem_append_right _ hr)

end VG.Proof.Ffdh.AArch64.ParameterCandidate

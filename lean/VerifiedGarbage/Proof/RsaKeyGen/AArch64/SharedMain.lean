module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.SharedRound
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrMain
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.Rsa.Ranges
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # RSA witness policy with a shared prepared round -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.Rsa (slot_lt)
open VG.Proof.MlKem.AArch64 (Keep eval_zero eq_zero_iff)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY sCnt sK)

/-- The header words preserved by the shared round and caller. -/
theorem sharedRoundRanges_hdr (w : Nat) {k : Nat}
    (hk : k = kRand ∨ k = kLen ∨ k = kRandLen ∨ k = kChecks ∨ k = kOut ∨ k = kUsedP) :
    ∀ r ∈ sharedRoundRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> hdr_disj

/-- At the head of the loop, after `i − 1` witnesses (`uni` of them uniform)
and `used` octets of `rand`. -/
structure SharedMrSt (B : Addr) (Z w : Nat) (c ch : Nat) (rp : Addr) (r : List Byte) (s₀ : State)
    (res : Option (Bool × List Byte)) (i uni used : Nat) (s : State) : Prop where
  ctx : ∃ bm, MrCtx s B Z w c bm
  ex : ECtx s.mem B w c
  r2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c
  rand : word s.mem B (8 * kRand) = rp
  len : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w)
  rlen : word s.mem B (8 * kRandLen) = BitVec.ofNat 64 r.length
  chk : word s.mem B (8 * kChecks) = BitVec.ofNat 64 ch
  src : Src s B Z rp r
  ki : word s.mem B (8 * kI) = BitVec.ofNat 64 i
  kuni : word s.mem B (8 * kUni) = BitVec.ofNat 64 uni
  kused : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used
  ul : used ≤ r.length
  go : i ≤ Spec.RsaKeyGen.blindedChecks ∨ uni < ch
  iu : 8 * w * i ≤ used
  unii : uni ≤ i
  rest : mrRest c ch r i uni used = res
  frm : Frm B (sharedRoundRanges w) s₀.mem s.mem
  keep : Keep mmRegs s₀ s

/-- How the loop ends. -/
abbrev SharedMrEnd (B : Addr) (Z w : Nat) (c : Nat) (r : List Byte) (s₀ : State)
    (res : Option (Bool × List Byte)) (s : State) : Prop :=
  (∃ bm, MrCtx s B Z w c bm) ∧
  (res = none → word s.mem B (8 * kStat) = BitVec.ofNat 64 0) ∧
  (∀ b rest, res = some (b, rest) → word s.mem B (8 * kStat) = BitVec.ofNat 64 (if b then 1 else 3) ∧
    word s.mem B (8 * kUsed) = BitVec.ofNat 64 (r.length - rest.length)) ∧
  Frm B (sharedRoundRanges w) s₀.mem s.mem ∧ Keep mmRegs s₀ s
/-- One iteration of `millerRabin`'s loop. -/
theorem sharedIter_ok (M : Mont) (R : VG.Proof.MillerRabin.AArch64.Kernel) {B : Addr} {Z w c ch : Nat} {rp : Addr} {r : List Byte}
    {s₀ : State} {res : Option (Bool × List Byte)} (hw4 : 4 ≤ w) (hw128 : w ≤ 128)
    (hEZ : slot w aE + 8 * (w + 2) ≤ Z) (hc1 : 1 < c) (hsh : VG.Proof.RsaKeyGen.PrimeShape (64 * w) c) (hrl : r.length < 2 ^ 64) (hch : ch < 2 ^ 62)
    {i uni used : Nat} (s : State) (hI : SharedMrSt B Z w c ch rp r s₀ res i uni used s) :
    WP isa (seqs [
      .block ([ldh .x3 kRandLen, ldh .x4 kUsed, .sub .x .x3 .x3 .x4, ldh .x4 kLen] ++ geFlag),
      .ite (.zero .x .x5) (.block [movi .x3 0, sth .x3 kStat]) (seqs (mrRoundWith M.mm R.run)),
      .block [ldh .x3 kStat, .subImm .x .x3 .x3 4]]) s fun s' =>
      (isa.eval (.zero .x .x3) s' = some false ∧ SharedMrEnd B Z w c r s₀ res s' ∧
        (res = none → r.length < used + 8 * w) ∧
        (∀ b rest, res = some (b, rest) → rest.length + (used + 8 * w) = r.length)) ∨
      (isa.eval (.zero .x .x3) s' = some true ∧ ∃ uni', SharedMrSt B Z w c ch rp r s₀ res (i + 1) uni' (used + 8 * w) s') := by
  obtain ⟨⟨bm, hc⟩, hE, hr2, hrp, hlen, hrlen, hchk, hsrc, hi, hun, hus, hul, hgo, hiu, huni, hres, hfrm, hkeep⟩ := hI
  have h := hc.ws
  have hZ := h.hZ
  have hnw := h.scr.nowrap
  have h256 := h.h256
  have hEn : B.toNat + slot w aE + 8 * (w + 1) ≤ 2 ^ 64 := by omega_arith
  have hEr : ∀ r ∈ sharedRoundRanges w, slot w aE + 8 * (w + 1) ≤ r.1 ∨ r.1 + r.2 ≤ slot w aE := fun r hr =>
    Or.inr (sharedRoundRanges_lt w r hr)
  obtain ⟨_, _, hwb⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega_arith) hsh
  have hres' := VG.Proof.RsaKeyGen.mrLoop_step c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2
    (8 * w) r i uni used hgo hwb (by omega_arith)
  simp only [seqs]
  refine WP.seq (WP.mono (iterHead_ok h hw128 hrl hul hlen hrlen hus) fun s₁ ⟨hz₁, hm₁, k₁⟩ => ?_)
  refine WP.seq (WP.ite (decide (r.length < used + 8 * w)) hz₁ (fun hb => ?_) (fun hb => ?_))
  · -- Out of octets: `kStat := 0`.
    simp only [decide_eq_true_eq] at hb
    have hs₁ := h.scr.congr k₁.wr
    refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s₁.mem.writeW (off B (8 * kStat)) (BitVec.ofNat 64 0)) (by
      brun [(k₁.gpr .x0 (by decide)).trans h.x0, hdr_enc (show kStat < 32 by decide),
        hs₁.st (d := 8 * kStat) (by simp only [kStat, sFn]; omega_arith)]
      rfl) (by decide) (by decide) (by decide +kernel)) fun s₂ ⟨hm₂, k₂⟩ => ?_
    have hf₂ : Frm B [(8 * kStat, 8)] s.mem s₂.mem := by
      rw [hm₂, hm₁]
      exact Frm.of_outside (writeW_outside _ B _ (d := 8 * kStat) (by simp only [kStat, sFn]; omega_arith)) (by simp)
    have hc₂ : MrCtx s₂ B Z w c bm := hc.of_frm hf₂ (by kmut) (k₁.trans k₂) (by decide) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
      (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
    refine WP.mono (statCmp_ok hc₂.ws (v := 0) (by decide) (by rw [hm₂, word_writeW_self]))
      fun t ⟨hz, hm, k⟩ => Or.inl ⟨hz.trans rfl, ?_⟩
    have hres0 : res = none := hres.symm.trans (hres'.trans (VG.Proof.RsaKeyGen.ite_f (by omega_arith) _ _))
    have hft : Frm B [(8 * kStat, 8)] s.mem t.mem :=
      hf₂.trans (show Frm B [(8 * kStat, 8)] s₂.mem t.mem by rw [hm]; exact Frm.refl _ _ _)
    refine ⟨⟨⟨bm, hc.of_frm hft (by kmut) ((k₁.trans k₂).trans k) (by decide) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
        (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)⟩,
      ?_, ?_, ?_, (((hkeep.trans k₁).trans k₂).trans k).mono (by decide)⟩, fun _ => hb,
      fun b rest h1 => by rw [hres0] at h1; cases h1⟩
    · intro _; rw [hm, hm₂, word_writeW_self]
    · intro b rest h; rw [hres0] at h; cases h
    · exact hfrm.trans (hft.mono (by simp [sharedRoundRanges]))
  · -- A round.
    simp only [decide_eq_false_iff_not, Nat.not_lt] at hb
    have hc₁ : MrCtx s₁ B Z w c bm := hc.of_frm (rs := []) (by rw [hm₁]; exact Frm.refl _ _ _) (by simp) k₁
      (by decide) (by simp) (by simp) (by simp) (by simp) (by simp)
    have hi61 : i < 2 ^ 61 := by
      have : 32 * i ≤ 8 * w * i := Nat.mul_le_mul_right _ (by omega_arith)
      omega_arith
    refine WP.mono (sharedRound_ok (rp := rp) (used := used) (r := r) (i := i) (uni := uni) (ch := ch) M R hw4 hw128 hEZ hc₁
      (by rw [hm₁]; exact hE) (by rw [hm₁]; exact hr2) hc1 hsh (by rw [hm₁]; exact hrp)
      (by rw [hm₁]; exact hus) (by rw [hm₁]; exact hlen) (hsrc.congrK (by rw [hm₁]; exact InScr.refl _ _ _) k₁) hb
      (by rw [hm₁]; exact hi) (by rw [hm₁]; exact hun) (by rw [hm₁]; exact hchk) hi61 (by omega_arith) hch)
      fun s₂ ⟨⟨bm₂, hc₂⟩, hr₂, hus₂, hst₂, hcnt₂, hfr₂, k₂⟩ => ?_
    rw [VG.Proof.RsaKeyGen.ite_t hb] at hres'
    generalize Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w))) = wt
      at hres' hc₂ hst₂ hcnt₂
    generalize Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2 wt.1 = f
      at hres' hst₂ hcnt₂
    have hfr : Frm B (sharedRoundRanges w) s.mem s₂.mem := by rw [← hm₁]; exact hfr₂
    have hdrop : r.length - (r.drop (used + 8 * w)).length = used + 8 * w := by rw [List.length_drop]; omega_arith
    have hk : Keep mmRegs s₀ s₂ := ((hkeep.trans k₁).trans k₂).mono (by decide)
    refine WP.mono (statCmp_ok hc₂.ws (v := if f then (if i + 1 < 17 ∨ uni + wt.2.toNat < ch then 4 else 1) else 3)
      (by split <;> (try split) <;> decide) hst₂) fun t ⟨hz, hm, k⟩ => ?_
    have hct : MrCtx t B Z w c bm₂ := hc₂.of_frm (rs := [])
      (by rw [hm]; exact Frm.refl _ _ _) (by simp) k (by decide) (by simp) (by simp) (by simp) (by simp) (by simp)
    have hkt : Keep mmRegs s₀ t := (hk.trans k).mono (by decide)
    have hft : Frm B (sharedRoundRanges w) s₀.mem t.mem := by rw [hm]; exact hfrm.trans hfr
    cases f
    · -- Composite.
      refine Or.inl ⟨hz.trans rfl, ⟨⟨_, hct⟩, fun h0 => ?_, fun b rest h1 => ?_, hft, hkt⟩, fun h0 => ?_,
        fun b rest h1 => ?_⟩
      · have h0' := hres'.symm.trans (hres.trans h0); simp at h0'
      · have h1' := hres'.symm.trans (hres.trans h1)
        simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h1'
        obtain ⟨h1a, h1b⟩ := h1'
        subst h1a h1b
        rw [hm, hst₂, hus₂, hdrop]; exact ⟨rfl, rfl⟩
      · have h0' := hres'.symm.trans (hres.trans h0); simp at h0'
      · have h1' := hres'.symm.trans (hres.trans h1)
        simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h1'
        obtain ⟨-, h1b⟩ := h1'
        subst h1b
        rw [List.length_drop]; omega_arith
    · obtain ⟨hI₂, hN₂⟩ := hcnt₂ rfl
      have hu : (if wt.2 = true then 1 else 0) = wt.2.toNat := by cases wt.2 <;> rfl
      simp only [↓reduceIte, hu] at hres'
      by_cases hcnd : i + 1 < 17 ∨ uni + wt.2.toNat < ch
      · -- On to the next witness.
        refine Or.inr ⟨hz.trans (by simp [hcnd]), uni + wt.2.toNat, ⟨⟨_, hct⟩,
          by rw [hm]; exact hE.of_frm hfr hEr hEn, ?_, ?_, ?_, ?_, ?_,
          ?_, by rw [hm]; exact hI₂, by rw [hm]; exact hN₂, by rw [hm]; exact hus₂, by omega_arith, ?_, ?_, ?_, ?_, hft,
          hkt⟩⟩
        · rw [hm]; exact hr₂
        · rw [hm, hfr.word_eq (sharedRoundRanges_hdr w (Or.inl rfl)) (by simp only [kRand, sFn]; omega_arith)]; exact hrp
        · rw [hm, hfr.word_eq (sharedRoundRanges_hdr w (Or.inr (Or.inl rfl))) (by simp only [kLen, sK, sFn]; omega_arith)]
          exact hlen
        · rw [hm, hfr.word_eq (sharedRoundRanges_hdr w (Or.inr (Or.inr (Or.inl rfl)))) (by simp only [kRandLen, sFn]; omega_arith)]
          exact hrlen
        · rw [hm, hfr.word_eq (sharedRoundRanges_hdr w (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
            (by simp only [kChecks, kE, sFn]; omega_arith)]
          exact hchk
        · have hle : ∀ r ∈ sharedRoundRanges w, r.1 + r.2 ≤ Z := fun r hr => by
            have := sharedRoundRanges_lt w r hr; omega_arith
          exact hsrc.congrK (by rw [hm]; exact InScr.of_frm hfr hle) ((k₁.trans k₂).trans k)
        · exact hcnd.imp (fun h => show i + 1 ≤ 16 by omega_arith) id
        · rw [Nat.mul_add, Nat.mul_one]; omega_arith
        · cases wt.2 <;> simp <;> omega_arith
        · exact hres'.symm.trans hres
      · -- Probably prime.
        have hdone := VG.Proof.RsaKeyGen.mrLoop_done c ch (Spec.Rsa.splitTwos (c - 1)).1
          (Spec.Rsa.splitTwos (c - 1)).2 (r.drop (used + 8 * w)) (i + 1) (uni + wt.2.toNat)
          (by intro h; exact hcnd (h.imp (fun h => by unfold Spec.RsaKeyGen.blindedChecks at h; omega_arith) id))
        refine Or.inl ⟨hz.trans (by simp [hcnd]), ⟨⟨_, hct⟩, fun h0 => ?_, fun b rest h1 => ?_, hft, hkt⟩,
          fun h0 => ?_, fun b rest h1 => ?_⟩
        · have h0' := (hres'.symm.trans (hres.trans h0)); rw [hdone] at h0'; cases h0'
        · have h1' := (hres'.symm.trans (hres.trans h1))
          rw [hdone] at h1'
          simp only [Option.some.injEq, Prod.mk.injEq] at h1'
          obtain ⟨h1a, h1b⟩ := h1'
          subst h1a h1b
          rw [hm, hst₂, hus₂, hdrop]
          simp [hcnd]
        · have h0' := (hres'.symm.trans (hres.trans h0)); rw [hdone] at h0'; cases h0'
        · have h1' := (hres'.symm.trans (hres.trans h1))
          rw [hdone] at h1'
          simp only [Option.some.injEq, Prod.mk.injEq] at h1'
          obtain ⟨-, h1b⟩ := h1'
          subst h1b
          rw [List.length_drop]; omega_arith

/-- The start of `millerRabin`: `kI := 1`, `kUni := 0`. -/
theorem sharedInit_ok {B : Addr} {Z w c ch bm : Nat} {rp : Addr} {r : List Byte} {s : State} {used : Nat}
    (hc : MrCtx s B Z w c bm) (hE : ECtx s.mem B w c) (hEZ : slot w aE + 8 * (w + 2) ≤ Z) (hr2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c)
    (hrp : word s.mem B (8 * kRand) = rp) (hlen : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hrlen : word s.mem B (8 * kRandLen) = BitVec.ofNat 64 r.length)
    (hchk : word s.mem B (8 * kChecks) = BitVec.ofNat 64 ch) (hsrc : Src s B Z rp r)
    (hus : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used) (hu1 : 8 * w ≤ used) (hu2 : used ≤ r.length) :
    WP isa (.block [movi .x3 1, sth .x3 kI, movi .x3 0, sth .x3 kUni]) s
      (SharedMrSt B Z w c ch rp r s (mrRest c ch r 1 0 used) 1 0 used) := by
  have h := hc.ws
  have hZ := h.hZ
  have hnw := h.scr.nowrap
  have h256 := h.h256
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = (s.mem.writeW (off B (8 * kI)) (BitVec.ofNat 64 1)).writeW
      (off B (8 * kUni)) (BitVec.ofNat 64 0)) (by
    brun [h.x0, hdr_enc (show kI < 32 by decide), hdr_enc (show kUni < 32 by decide),
      h.scr.st (d := 8 * kI) (by simp only [kI, kElen, sFn]; omega_arith),
      h.scr.st (d := 8 * kUni) (by simp only [kUni, kP, sFn]; omega_arith)]
    rfl) (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨hm₁, k₁⟩ => ?_
  have hf₁ : Frm B [(8 * kI, 8), (8 * kUni, 8)] s.mem s₁.mem := by
    rw [hm₁]
    exact (Frm.of_outside (writeW_outside _ B _ (d := 8 * kI) (by simp only [kI, kElen, sFn]; omega_arith)) (by simp)).trans
      (Frm.of_outside (writeW_outside _ B _ (d := 8 * kUni) (by simp only [kUni, kP, sFn]; omega_arith)) (by simp))
  have sR2 : slot w aR2 + 8 * (w + 2) ≤ Z := by have := slot_lt (w := w) (show aR2 < 16 by decide); omega_arith
  refine ⟨⟨bm, hc.of_frm hf₁ (by kmut) k₁ (by decide) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
      (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)⟩, hE.of_frm hf₁ (VG.Proof.RsaKeyGen.SlotShapeC.apartW1 rfl rfl) (by omega_arith), ?_, ?_, ?_, ?_, ?_, hsrc.congrK (InScr.of_frm hf₁ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, kI, kElen, kUni, kP, sFn]
        omega_arith)) k₁,
    by rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self],
    by rw [hm₁, word_writeW_self], ?_, hu2, Or.inl (by decide), by omega_arith, by omega_arith, rfl,
    hf₁.mono (by simp [sharedRoundRanges]), k₁.mono (by decide)⟩
  · rw [hf₁.wv_eq (d := slot w aR2) (k := w) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (by omega_arith)]; exact hr2
  · rw [hf₁.word_eq (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by simp only [kRand, sFn]; omega_arith)]; exact hrp
  · rw [hf₁.word_eq (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by simp only [kLen, sK, sFn]; omega_arith)]; exact hlen
  · rw [hf₁.word_eq (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by simp only [kRandLen, sFn]; omega_arith)]; exact hrlen
  · rw [hf₁.word_eq (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by simp only [kChecks, kE, sFn]; omega_arith)]; exact hchk
  · rw [hf₁.word_eq (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by simp only [kUsed, sFn]; omega_arith)]; exact hus

/-- `millerRabin`: the witnesses from offset `used`, as `primalityTest`'s
loop from `(1, 0)`. -/
theorem sharedMillerRabin_ok (M : Mont) (R : VG.Proof.MillerRabin.AArch64.Kernel) {B : Addr} {Z w c ch bm : Nat} {rp : Addr}
    {r : List Byte} {s : State} {used : Nat} (hw4 : 4 ≤ w) (hw128 : w ≤ 128) (hEZ : slot w aE + 8 * (w + 2) ≤ Z)
    (hc1 : 1 < c) (hsh : VG.Proof.RsaKeyGen.PrimeShape (64 * w) c) (hrl : r.length < 2 ^ 64) (hch : ch < 2 ^ 62)
    (hc : MrCtx s B Z w c bm) (hE : ECtx s.mem B w c) (hr2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c)
    (hrp : word s.mem B (8 * kRand) = rp) (hlen : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hrlen : word s.mem B (8 * kRandLen) = BitVec.ofNat 64 r.length)
    (hchk : word s.mem B (8 * kChecks) = BitVec.ofNat 64 ch) (hsrc : Src s B Z rp r)
    (hus : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used) (hu1 : 8 * w ≤ used) (hu2 : used ≤ r.length) :
    WP isa (seqs (millerRabinWith M.mm R.run)) s (SharedMrEnd B Z w c r s (mrRest c ch r 1 0 used)) := by
  unfold millerRabinWith
  simp only [seqs]
  refine WP.seq (WP.mono (sharedInit_ok hc hE hEZ hr2 hrp hlen hrlen hchk hsrc hus hu1 hu2) fun s₁ h => ?_)
  exact WP.loop (fun n t => ∃ i uni u, n = r.length - u ∧ SharedMrSt B Z w c ch rp r s (mrRest c ch r 1 0 used) i uni u t)
    (fun n t ⟨i, uni, u, hn, hI⟩ => WP.mono (sharedIter_ok M R hw4 hw128 hEZ hc1 hsh hrl hch t hI)
      fun t' h => h.imp (fun h => ⟨h.1, h.2.1⟩)
      fun ⟨he, uni', hI'⟩ => ⟨he, r.length - (u + 8 * w), by have := hI'.ul; omega_arith,
        i + 1, uni', u + 8 * w, rfl, hI'⟩) (r.length - used) s₁ ⟨1, 0, used, rfl, h⟩

end VG.Proof.RsaKeyGen.AArch64

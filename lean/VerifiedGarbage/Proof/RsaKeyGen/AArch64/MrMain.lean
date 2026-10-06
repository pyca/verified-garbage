import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrRound

/-!
# A candidate on AArch64: Miller–Rabin's loop

`MrSt`: at the head of `millerRabin`'s loop, a state `(i, uniform)` that
draws, at the offset `used` of `rand`, whose remaining loop (`mrRest`) is
the whole test's. `mrIter_ok`: one iteration; `millerRabin_ok`: the loop,
with `kStat` 0, 1 or 3 and `kUsed` as `primalityTest` ends.
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero eq_zero_iff)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY sCnt sK)

/-- The witnesses' loop from `(i, uniform)` at offset `used`. -/
abbrev mrRest (c ch : Nat) (r : List Byte) (i uni used : Nat) : Option (Bool × List Byte) :=
  Spec.RsaKeyGen.loop (Spec.RsaKeyGen.mrStep c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2)
    (i, uni) (r.drop used)

/-- At the head of the loop, after `i − 1` witnesses (`uni` of them uniform)
and `used` octets of `rand`. -/
structure MrSt (B : Addr) (Z w : Nat) (c ch : Nat) (rp : Addr) (r : List Byte) (s₀ : State)
    (res : Option (Bool × List Byte)) (i uni used : Nat) (s : State) : Prop where
  ctx : ∃ bm, MrCtx s B Z w c bm
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
  frm : Frm B (roundRanges w) s₀.mem s.mem
  keep : Keep mmRegs s₀ s

/-- How the loop ends. -/
abbrev MrEnd (B : Addr) (Z w : Nat) (c : Nat) (r : List Byte) (s₀ : State)
    (res : Option (Bool × List Byte)) (s : State) : Prop :=
  (∃ bm, MrCtx s B Z w c bm) ∧
  (res = none → word s.mem B (8 * kStat) = BitVec.ofNat 64 0) ∧
  (∀ b rest, res = some (b, rest) → word s.mem B (8 * kStat) = BitVec.ofNat 64 (if b then 1 else 3) ∧
    word s.mem B (8 * kUsed) = BitVec.ofNat 64 (r.length - rest.length)) ∧
  Frm B (roundRanges w) s₀.mem s.mem ∧ Keep mmRegs s₀ s

theorem sub4_beq {v : Nat} (hv : v < 2 ^ 63) :
    (BitVec.ofNat 64 v - BitVec.ofNat 64 4 == 0) = decide (v = 4) := by
  rw [eq_zero_iff, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  exact decide_eq_decide.mpr (by omega)

/-- `kStat` against 4. -/
theorem statCmp_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w)
    {v : Nat} (hv : v < 2 ^ 63) (hS : word s.mem B (8 * kStat) = BitVec.ofNat 64 v) :
    WP isa (.block [ldh .x3 kStat, .subImm .x .x3 .x3 4]) s fun t =>
      isa.eval (.zero .x .x3) t = some (decide (v = 4)) ∧ t.mem = s.mem ∧ Keep [.x3] s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have hS' : s.mem.readW (B + BitVec.ofNat 64 (8 * kStat)) 64 = BitVec.ofNat 64 v := hS
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 v - BitVec.ofNat 64 4 ∧ t.mem = s.mem) (by
    brun [h.x0, hdr_enc (show kStat < 32 by decide), h.scr.ld (d := 8 * kStat) (by simp only [kStat, sFn]; omega),
      hS']) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h3, hm⟩, k⟩ => ?_
  exact ⟨by rw [eval_zero, h3, sub4_beq hv], hm, k⟩

/-- Bounds of the ranges of a round. -/
theorem roundRanges_le (w : Nat) : ∀ r ∈ roundRanges w, r.1 + r.2 ≤ slot w 16 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, roundRanges, preRanges,
    witRanges, expRanges, bitRanges, List.cons_append, List.nil_append, slot, hdrBytes, aX, aAcc, aTmp, aY, aXm,
    aB, kG, kFlag, kPlen, kV, kT0, sCnt, kBits, kT2, kWords, kT1, kUsed, kU, kI, kElen, kUni, kP, kStat, sFn]
  and_intros <;> omega

/-- The header words a round keeps. -/
theorem roundRanges_hdr (w : Nat) {k : Nat} (hk : k = kRand ∨ k = kLen ∨ k = kRandLen ∨ k = kChecks ∨ k = kOut ∨
    k = kUsedP) : ∀ r ∈ roundRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> rd_disj

theorem ofNat_sub_ofNat' {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega)]
  omega

/-- The test of `rand`'s octets left: `x5 = 0` iff fewer than `8 w`. -/
theorem iterHead_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w) {r : List Byte} {used : Nat}
    (hw64 : w ≤ 64) (hrl : r.length < 2 ^ 64) (hul : used ≤ r.length)
    (hlen : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hrlen : word s.mem B (8 * kRandLen) = BitVec.ofNat 64 r.length)
    (hus : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used) :
    WP isa (.block ([ldh .x3 kRandLen, ldh .x4 kUsed, .sub .x .x3 .x3 .x4, ldh .x4 kLen] ++ geFlag)) s fun t =>
      isa.eval (.zero .x .x5) t = some (decide (r.length < used + 8 * w)) ∧ t.mem = s.mem ∧
        Keep [.x3, .x4, .x5, .x7] s t := by
  have hn := h.scr.nowrap
  have h256 := h.h256
  have e1 : BitVec.ofNat 64 r.length - BitVec.ofNat 64 used = BitVec.ofNat 64 (r.length - used) :=
    ofNat_sub_ofNat' hul hrl
  have r1 : s.mem.readW (B + BitVec.ofNat 64 (8 * kRandLen)) 64 = BitVec.ofNat 64 r.length := hrlen
  have r2 : s.mem.readW (B + BitVec.ofNat 64 (8 * kUsed)) 64 = BitVec.ofNat 64 used := hus
  have r3 : s.mem.readW (B + BitVec.ofNat 64 (8 * kLen)) 64 = BitVec.ofNat 64 (8 * w) := hlen
  refine (WP.block_append_iff (M := isa)
    (l₁ := ([ldh .x3 kRandLen, ldh .x4 kUsed, .sub .x .x3 .x3 .x4, ldh .x4 kLen] : List Instr))).mpr ?_
  refine WP.mono (WP.keep [.x3, .x4] (Q := fun t => t.gpr .x3 = BitVec.ofNat 64 (r.length - used) ∧
      t.gpr .x4 = BitVec.ofNat 64 (8 * w) ∧ t.mem = s.mem) (by
    brun [h.x0, hdr_enc (show kRandLen < 32 by decide), hdr_enc (show kUsed < 32 by decide),
      hdr_enc (show kLen < 32 by decide), h.scr.ld (d := 8 * kRandLen) (by simp only [kRandLen, sFn]; omega),
      h.scr.ld (d := 8 * kUsed) (by simp only [kUsed, sFn]; omega),
      h.scr.ld (d := 8 * kLen) (by simp only [kLen, sK, sFn]; omega), r1, r2, r3, e1]) (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨⟨h3, h4, hm₁⟩, k₁⟩ => ?_
  refine WP.mono (geFlag_ok s₁) fun t ⟨⟨h5, hm⟩, k⟩ => ⟨?_, hm.trans hm₁, (k₁.trans k).mono (by decide)⟩
  rw [eval_zero, h5, h3, h4, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 8 * w < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show r.length - used < 2 ^ 64 by omega)]
  rcases Nat.lt_or_ge r.length (used + 8 * w) with hl | hl
  · rw [decide_eq_false (show ¬(8 * w ≤ r.length - used) by omega), decide_eq_true hl]; rfl
  · rw [decide_eq_true (show 8 * w ≤ r.length - used by omega), decide_eq_false (show ¬(r.length < used + 8 * w) by omega)]
    rfl

/-- One iteration of `millerRabin`'s loop. -/
theorem mrIter_ok (M : Mont) {B : Addr} {Z w c ch : Nat} {rp : Addr} {r : List Byte}
    {s₀ : State} {res : Option (Bool × List Byte)} (hw4 : 4 ≤ w) (hw64 : w ≤ 64) (hc1 : 1 < c)
    (hsh : VG.Proof.RsaKeyGen.PrimeShape (64 * w) c) (hrl : r.length < 2 ^ 64) (hch : ch < 2 ^ 62)
    {i uni used : Nat} (s : State) (hI : MrSt B Z w c ch rp r s₀ res i uni used s) :
    WP isa (seqs [
      .block ([ldh .x3 kRandLen, ldh .x4 kUsed, .sub .x .x3 .x3 .x4, ldh .x4 kLen] ++ geFlag),
      .ite (.zero .x .x5) (.block [movi .x3 0, sth .x3 kStat]) (seqs (mrRound M.mm)),
      .block [ldh .x3 kStat, .subImm .x .x3 .x3 4]]) s fun s' =>
      (isa.eval (.zero .x .x3) s' = some false ∧ MrEnd B Z w c r s₀ res s' ∧
        (res = none → r.length < used + 8 * w) ∧
        (∀ b rest, res = some (b, rest) → rest.length + (used + 8 * w) = r.length)) ∨
      (isa.eval (.zero .x .x3) s' = some true ∧ ∃ uni', MrSt B Z w c ch rp r s₀ res (i + 1) uni' (used + 8 * w) s') := by
  obtain ⟨⟨bm, hc⟩, hr2, hrp, hlen, hrlen, hchk, hsrc, hi, hun, hus, hul, hgo, hiu, huni, hres, hfrm, hkeep⟩ := hI
  have h := hc.ws
  have hZ := h.hZ
  have hnw := h.scr.nowrap
  have h256 := h.h256
  obtain ⟨_, _, hwb⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega) hsh
  have hres' := VG.Proof.RsaKeyGen.mrLoop_step c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2
    (8 * w) r i uni used hgo hwb (by omega)
  simp only [seqs]
  refine WP.seq (WP.mono (iterHead_ok h hw64 hrl hul hlen hrlen hus) fun s₁ ⟨hz₁, hm₁, k₁⟩ => ?_)
  refine WP.seq (WP.ite (decide (r.length < used + 8 * w)) hz₁ (fun hb => ?_) (fun hb => ?_))
  · -- Out of octets: `kStat := 0`.
    simp only [decide_eq_true_eq] at hb
    have hs₁ := h.scr.congr k₁.wr
    refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = s₁.mem.writeW (off B (8 * kStat)) (BitVec.ofNat 64 0)) (by
      brun [(k₁.gpr .x0 (by decide)).trans h.x0, hdr_enc (show kStat < 32 by decide),
        hs₁.st (d := 8 * kStat) (by simp only [kStat, sFn]; omega)]
      rfl) (by decide) (by decide) (by decide +kernel)) fun s₂ ⟨hm₂, k₂⟩ => ?_
    have hf₂ : Frm B [(8 * kStat, 8)] s.mem s₂.mem := by
      rw [hm₂, hm₁]
      exact Frm.of_outside (writeW_outside _ B _ (d := 8 * kStat) (by simp only [kStat, sFn]; omega)) (by simp)
    have hc₂ : MrCtx s₂ B Z w c bm := hc.of_frm hf₂ (by kmut) (k₁.trans k₂) (by decide) (by rd_disj) (by rd_disj)
      (by rd_disj) (by rd_disj) (by rd_disj)
    refine WP.mono (statCmp_ok hc₂.ws (v := 0) (by decide) (by rw [hm₂, word_writeW_self]))
      fun t ⟨hz, hm, k⟩ => Or.inl ⟨hz.trans rfl, ?_⟩
    have hres0 : res = none := hres.symm.trans (hres'.trans (VG.Proof.RsaKeyGen.ite_f (by omega) _ _))
    have hft : Frm B [(8 * kStat, 8)] s.mem t.mem :=
      hf₂.trans (show Frm B [(8 * kStat, 8)] s₂.mem t.mem by rw [hm]; exact Frm.refl _ _ _)
    refine ⟨⟨⟨bm, hc.of_frm hft (by kmut) ((k₁.trans k₂).trans k) (by decide) (by rd_disj) (by rd_disj)
        (by rd_disj) (by rd_disj) (by rd_disj)⟩,
      ?_, ?_, ?_, (((hkeep.trans k₁).trans k₂).trans k).mono (by decide)⟩, fun _ => hb,
      fun b rest h1 => by rw [hres0] at h1; cases h1⟩
    · intro _; rw [hm, hm₂, word_writeW_self]
    · intro b rest h; rw [hres0] at h; cases h
    · exact hfrm.trans (hft.mono (by simp [roundRanges]))
  · -- A round.
    simp only [decide_eq_false_iff_not, Nat.not_lt] at hb
    have hc₁ : MrCtx s₁ B Z w c bm := hc.of_frm (rs := []) (by rw [hm₁]; exact Frm.refl _ _ _) (by simp) k₁
      (by decide) (by simp) (by simp) (by simp) (by simp) (by simp)
    have hi61 : i < 2 ^ 61 := by
      have : 32 * i ≤ 8 * w * i := Nat.mul_le_mul_right _ (by omega)
      omega
    refine WP.mono (mrRound_ok (rp := rp) (used := used) (r := r) (i := i) (uni := uni) (ch := ch) M hw4 hw64 hc₁
      (by rw [hm₁]; exact hr2) hc1 hsh (by rw [hm₁]; exact hrp)
      (by rw [hm₁]; exact hus) (by rw [hm₁]; exact hlen) (hsrc.congrK (by rw [hm₁]; exact InScr.refl _ _ _) k₁) hb
      (by rw [hm₁]; exact hi) (by rw [hm₁]; exact hun) (by rw [hm₁]; exact hchk) hi61 (by omega) hch)
      fun s₂ ⟨hc₂, hr₂, hus₂, hst₂, hcnt₂, hfr₂, k₂⟩ => ?_
    rw [VG.Proof.RsaKeyGen.ite_t hb] at hres'
    generalize Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w))) = wt
      at hres' hc₂ hst₂ hcnt₂
    generalize Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2 wt.1 = f
      at hres' hst₂ hcnt₂
    have hfr : Frm B (roundRanges w) s.mem s₂.mem := by rw [← hm₁]; exact hfr₂
    have hdrop : r.length - (r.drop (used + 8 * w)).length = used + 8 * w := by rw [List.length_drop]; omega
    have hk : Keep mmRegs s₀ s₂ := ((hkeep.trans k₁).trans k₂).mono (by decide)
    refine WP.mono (statCmp_ok hc₂.ws (v := if f then (if i + 1 < 17 ∨ uni + wt.2.toNat < ch then 4 else 1) else 3)
      (by split <;> (try split) <;> decide) hst₂) fun t ⟨hz, hm, k⟩ => ?_
    have hct : MrCtx t B Z w c (wt.1 * 2 ^ (64 * w) % c) := hc₂.of_frm (rs := [])
      (by rw [hm]; exact Frm.refl _ _ _) (by simp) k (by decide) (by simp) (by simp) (by simp) (by simp) (by simp)
    have hkt : Keep mmRegs s₀ t := (hk.trans k).mono (by decide)
    have hft : Frm B (roundRanges w) s₀.mem t.mem := by rw [hm]; exact hfrm.trans hfr
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
        rw [List.length_drop]; omega
    · obtain ⟨hI₂, hN₂⟩ := hcnt₂ rfl
      have hu : (if wt.2 = true then 1 else 0) = wt.2.toNat := by cases wt.2 <;> rfl
      simp only [↓reduceIte, hu] at hres'
      by_cases hcnd : i + 1 < 17 ∨ uni + wt.2.toNat < ch
      · -- On to the next witness.
        refine Or.inr ⟨hz.trans (by simp [hcnd]), uni + wt.2.toNat, ⟨⟨_, hct⟩, ?_, ?_, ?_, ?_, ?_,
          ?_, by rw [hm]; exact hI₂, by rw [hm]; exact hN₂, by rw [hm]; exact hus₂, by omega, ?_, ?_, ?_, ?_, hft,
          hkt⟩⟩
        · rw [hm]; exact hr₂
        · rw [hm, hfr.word_eq (roundRanges_hdr w (Or.inl rfl)) (by simp only [kRand, sFn]; omega)]; exact hrp
        · rw [hm, hfr.word_eq (roundRanges_hdr w (Or.inr (Or.inl rfl))) (by simp only [kLen, sK, sFn]; omega)]
          exact hlen
        · rw [hm, hfr.word_eq (roundRanges_hdr w (Or.inr (Or.inr (Or.inl rfl)))) (by simp only [kRandLen, sFn]; omega)]
          exact hrlen
        · rw [hm, hfr.word_eq (roundRanges_hdr w (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
            (by simp only [kChecks, kE, sFn]; omega)]
          exact hchk
        · have hle : ∀ r ∈ roundRanges w, r.1 + r.2 ≤ Z := fun r hr => (roundRanges_le w r hr).trans hZ
          exact hsrc.congrK (by rw [hm]; exact InScr.of_frm hfr hle) ((k₁.trans k₂).trans k)
        · exact hcnd.imp (fun h => show i + 1 ≤ 16 by omega) id
        · rw [Nat.mul_add, Nat.mul_one]; omega
        · cases wt.2 <;> simp <;> omega
        · exact hres'.symm.trans hres
      · -- Probably prime.
        have hdone := VG.Proof.RsaKeyGen.mrLoop_done c ch (Spec.Rsa.splitTwos (c - 1)).1
          (Spec.Rsa.splitTwos (c - 1)).2 (r.drop (used + 8 * w)) (i + 1) (uni + wt.2.toNat)
          (by intro h; exact hcnd (h.imp (fun h => by unfold Spec.RsaKeyGen.blindedChecks at h; omega) id))
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
          rw [List.length_drop]; omega

/-- The start of `millerRabin`: `kI := 1`, `kUni := 0`. -/
theorem mrInit_ok {B : Addr} {Z w c ch bm : Nat} {rp : Addr} {r : List Byte} {s : State} {used : Nat}
    (hc : MrCtx s B Z w c bm) (hr2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c)
    (hrp : word s.mem B (8 * kRand) = rp) (hlen : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hrlen : word s.mem B (8 * kRandLen) = BitVec.ofNat 64 r.length)
    (hchk : word s.mem B (8 * kChecks) = BitVec.ofNat 64 ch) (hsrc : Src s B Z rp r)
    (hus : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used) (hu1 : 8 * w ≤ used) (hu2 : used ≤ r.length) :
    WP isa (.block [movi .x3 1, sth .x3 kI, movi .x3 0, sth .x3 kUni]) s
      (MrSt B Z w c ch rp r s (mrRest c ch r 1 0 used) 1 0 used) := by
  have h := hc.ws
  have hZ := h.hZ
  have hnw := h.scr.nowrap
  have h256 := h.h256
  refine WP.mono (WP.keep [.x3] (Q := fun t => t.mem = (s.mem.writeW (off B (8 * kI)) (BitVec.ofNat 64 1)).writeW
      (off B (8 * kUni)) (BitVec.ofNat 64 0)) (by
    brun [h.x0, hdr_enc (show kI < 32 by decide), hdr_enc (show kUni < 32 by decide),
      h.scr.st (d := 8 * kI) (by simp only [kI, kElen, sFn]; omega),
      h.scr.st (d := 8 * kUni) (by simp only [kUni, kP, sFn]; omega)]
    rfl) (by decide) (by decide) (by decide +kernel)) fun s₁ ⟨hm₁, k₁⟩ => ?_
  have hf₁ : Frm B [(8 * kI, 8), (8 * kUni, 8)] s.mem s₁.mem := by
    rw [hm₁]
    exact (Frm.of_outside (writeW_outside _ B _ (d := 8 * kI) (by simp only [kI, kElen, sFn]; omega)) (by simp)).trans
      (Frm.of_outside (writeW_outside _ B _ (d := 8 * kUni) (by simp only [kUni, kP, sFn]; omega)) (by simp))
  have sR2 : slot w aR2 + 8 * (w + 2) ≤ Z := by have := slot_lt (w := w) (show aR2 < 16 by decide); omega
  refine ⟨⟨bm, hc.of_frm hf₁ (by kmut) k₁ (by decide) (by rd_disj) (by rd_disj) (by rd_disj) (by rd_disj)
      (by rd_disj)⟩, ?_, ?_, ?_, ?_, ?_, hsrc.congrK (InScr.of_frm hf₁ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, kI, kElen, kUni, kP, sFn]
        omega)) k₁,
    by rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self],
    by rw [hm₁, word_writeW_self], ?_, hu2, Or.inl (by decide), by omega, by omega, rfl,
    hf₁.mono (by simp [roundRanges]), k₁.mono (by decide)⟩
  · rw [hf₁.wv_eq (d := slot w aR2) (k := w) (by rd_disj) (by omega)]; exact hr2
  · rw [hf₁.word_eq (by rd_disj) (by simp only [kRand, sFn]; omega)]; exact hrp
  · rw [hf₁.word_eq (by rd_disj) (by simp only [kLen, sK, sFn]; omega)]; exact hlen
  · rw [hf₁.word_eq (by rd_disj) (by simp only [kRandLen, sFn]; omega)]; exact hrlen
  · rw [hf₁.word_eq (by rd_disj) (by simp only [kChecks, kE, sFn]; omega)]; exact hchk
  · rw [hf₁.word_eq (by rd_disj) (by simp only [kUsed, sFn]; omega)]; exact hus

/-- `millerRabin`: the witnesses from offset `used`, as `primalityTest`'s
loop from `(1, 0)`. -/
theorem millerRabin_ok (M : Mont) {B : Addr} {Z w c ch bm : Nat} {rp : Addr}
    {r : List Byte} {s : State} {used : Nat} (hw4 : 4 ≤ w) (hw64 : w ≤ 64) (hc1 : 1 < c)
    (hsh : VG.Proof.RsaKeyGen.PrimeShape (64 * w) c) (hrl : r.length < 2 ^ 64) (hch : ch < 2 ^ 62)
    (hc : MrCtx s B Z w c bm) (hr2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c)
    (hrp : word s.mem B (8 * kRand) = rp) (hlen : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hrlen : word s.mem B (8 * kRandLen) = BitVec.ofNat 64 r.length)
    (hchk : word s.mem B (8 * kChecks) = BitVec.ofNat 64 ch) (hsrc : Src s B Z rp r)
    (hus : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used) (hu1 : 8 * w ≤ used) (hu2 : used ≤ r.length) :
    WP isa (seqs (millerRabin M.mm)) s (MrEnd B Z w c r s (mrRest c ch r 1 0 used)) := by
  unfold millerRabin
  simp only [seqs]
  refine WP.seq (WP.mono (mrInit_ok hc hr2 hrp hlen hrlen hchk hsrc hus hu1 hu2) fun s₁ h => ?_)
  exact WP.loop (fun n t => ∃ i uni u, n = r.length - u ∧ MrSt B Z w c ch rp r s (mrRest c ch r 1 0 used) i uni u t)
    (fun n t ⟨i, uni, u, hn, hI⟩ => WP.mono (mrIter_ok M hw4 hw64 hc1 hsh hrl hch t hI)
      fun t' h => h.imp (fun h => ⟨h.1, h.2.1⟩)
      fun ⟨he, uni', hI'⟩ => ⟨he, r.length - (u + 8 * w), by have := hI'.ul; omega,
        i + 1, uni', u + 8 * w, rfl, hI'⟩) (r.length - used) s₁ ⟨1, 0, used, rfl, h⟩

end VG.Proof.RsaKeyGen.AArch64

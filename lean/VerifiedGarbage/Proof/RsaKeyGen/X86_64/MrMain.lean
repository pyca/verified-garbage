import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrRoundAll

/-!
# A candidate on x86-64: Miller–Rabin's loop

`MrSt`: at the head of `millerRabin`'s loop, a state `(i, uniform)` that
draws, at the offset `used` of `rand`, whose remaining loop (`mrRest`) is
the whole test's. `mrIter_ok`: one iteration; `millerRabin_ok`: the loop,
with `kStat` 0, 1 or 3 and `kUsed` as `primalityTest` ends.
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- The witnesses' loop from `(i, uniform)` at offset `used`. -/
abbrev mrRest (c ch : Nat) (r : List Byte) (i uni used : Nat) : Option (Bool × List Byte) :=
  Spec.RsaKeyGen.loop (Spec.RsaKeyGen.mrStep c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2)
    (i, uni) (r.drop used)

/-- At the head of the loop, with `n` octets of `rand` left. -/
structure MrSt (B : Addr) (Z w : Nat) (mi : BitVec 64) (c ch : Nat) (rp : Addr) (r : List Byte) (s₀ : State)
    (res : Option (Bool × List Byte)) (n : Nat) (s : State) : Prop where
  ctx : ∃ bm, MrCtx s B Z w mi c bm
  r2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c
  rand : word s.mem B (8 * kRand) = rp
  len : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w)
  rlen : word s.mem B (8 * kRandLen) = BitVec.ofNat 64 r.length
  chk : word s.mem B (8 * kChecks) = BitVec.ofNat 64 ch
  src : Src s B Z rp r
  st : ∃ i uni used, word s.mem B (8 * kI) = BitVec.ofNat 64 i ∧ word s.mem B (8 * kUni) = BitVec.ofNat 64 uni ∧
    word s.mem B (8 * kUsed) = BitVec.ofNat 64 used ∧ used ≤ r.length ∧ n = r.length - used ∧
    (i ≤ Spec.RsaKeyGen.blindedChecks ∨ uni < ch) ∧ 8 * w * i ≤ used ∧ uni ≤ i ∧ mrRest c ch r i uni used = res
  frm : Frm B (roundRanges w) s₀.mem s.mem
  keep : Keep mmRegs s₀ s

/-- How the loop ends. -/
abbrev MrEnd (B : Addr) (Z w : Nat) (mi : BitVec 64) (c : Nat) (r : List Byte) (s₀ : State)
    (res : Option (Bool × List Byte)) (s : State) : Prop :=
  (∃ bm, MrCtx s B Z w mi c bm) ∧
  (res = none → word s.mem B (8 * kStat) = BitVec.ofNat 64 0) ∧
  (∀ b rest, res = some (b, rest) → word s.mem B (8 * kStat) = BitVec.ofNat 64 (if b then 1 else 3) ∧
    word s.mem B (8 * kUsed) = BitVec.ofNat 64 (r.length - rest.length)) ∧
  Frm B (roundRanges w) s₀.mem s.mem ∧ Keep mmRegs s₀ s

/-- `kStat` against 4. -/
theorem statCmp_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z)
    {v : Nat} (hv : v < 2 ^ 31) (hS : word s.mem B (8 * kStat) = BitVec.ofNat 64 v) :
    WP isa (.block [.mov .rax (.mem (hdr kStat)), .alu .cmp .rax (.imm 4)]) s fun t =>
      t.zf = some (decide (v = 4)) ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  have hn := hg.scr.nowrap
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * kStat)) 8 :=
    hg.scr.ld (by have := hdr_lt_slot w 8 (show kStat < 32 by decide); omega)
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (decide (v = 4)) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl, hS]
    exact (congrArg (fun x => (BitVec.ofNat 64 v - x == 0)) (show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl)).trans
      (ofNat_sub_beq (by omega) (by decide))) rfl) fun t ⟨⟨hz, hm⟩, k⟩ => ⟨hz, hm, k⟩

/-- Bounds of a list of literal ranges of the scratch space. -/
macro "rng_le" : tactic => `(tactic| (
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, slot, hdrBytes, aN, aX, aAcc,
    aTmp, aR2, aXm, aY, aOne, aB, aR1, aRm1, aTab, kT0, kChecks, kE, sFn, sMinv, sW, sArr, kG, kV, kWords, kBits,
    kFlag, kPlen, kI, kElen, kU, kUni, kP, kStat, kT1, kT2, kUsed]
  and_intros <;> omega))

theorem roundRanges_le (w : Nat) : ∀ r ∈ roundRanges w, r.1 + r.2 ≤ slot w aRm1 + 8 * (w + 2) := by
  simp only [roundRanges, preRanges, witRanges, expRanges, bitRanges, List.cons_append, List.nil_append]
  rng_le

/-- The header words a round keeps. -/
theorem roundRanges_hdr (w : Nat) {k : Nat} (hk : k = kRand ∨ k = kLen ∨ k = kRandLen ∨ k = kChecks ∨ k = kOut ∨
    k = kUsedP) : ∀ r ∈ roundRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  simp only [roundRanges, preRanges, witRanges, expRanges, bitRanges, List.cons_append, List.nil_append]
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals (try simp only [kRand, kLen, kRandLen, kOut, kUsedP])
  all_goals rng_disj

theorem ofNat_sub_ofNat' {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega)]
  omega

/-- One iteration of `millerRabin`'s loop. -/
theorem mrIter_ok (M : Mont) {B : Addr} {Z w : Nat} {mi : BitVec 64} {c ch : Nat} {rp : Addr} {r : List Byte}
    {s₀ : State} {res : Option (Bool × List Byte)} (hd : MrDims B Z w) (hc1 : 1 < c)
    (hsh : VG.Proof.RsaKeyGen.PrimeShape (64 * w) c) (hrl : r.length < 2 ^ 64) (hch : ch < 2 ^ 62)
    (n : Nat) (s : State) (hI : MrSt B Z w mi c ch rp r s₀ res n s) :
    WP isa (seqs [
      .block [.mov .rcx (.mem (hdr kRandLen)), .alu .sub .rcx (.mem (hdr kUsed)), .alu .cmp .rcx (.mem (hdr kLen))],
      .ite .b (.block [.mov32 .rax (.imm 0), .store (hdr kStat) .rax]) (seqs (mrRound M.mm)),
      .block [.mov .rax (.mem (hdr kStat)), .alu .cmp .rax (.imm 4)]]) s fun s' =>
      (isa.eval .e s' = some false ∧ MrEnd B Z w mi c r s₀ res s') ∨
      (isa.eval .e s' = some true ∧ ∃ m < n, MrSt B Z w mi c ch rp r s₀ res m s') := by
  obtain ⟨⟨bm, hc⟩, hr2, hrp, hlen, hrlen, hchk, hsrc, ⟨i, uni, used, hi, hun, hus, hul, hn, hgo, hiu, huni, hres⟩,
    hfrm, hkeep⟩ := hI
  have hg := hc.good
  have hZ := hd.z
  have hw4 := hd.w4
  have hnw := hg.scr.nowrap
  obtain ⟨_, _, hwb⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega) hsh
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have hres' := VG.Proof.RsaKeyGen.mrLoop_step c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2
    (8 * w) r i uni used hgo hwb (by omega)
  simp only [seqs]
  have e1 : BitVec.ofNat 64 r.length - BitVec.ofNat 64 used = BitVec.ofNat 64 (r.length - used) :=
    ofNat_sub_ofNat' hul hrl
  have e2 : r.length - used < 2 ^ 64 := by omega
  have e3 : 8 * w < 2 ^ 64 := by have := hd.w64; omega
  refine WP.seq (WP.mono (WP.keep [.rcx] (Q := fun t => t.cf = some (decide (r.length < used + 8 * w)) ∧
      t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl kUsed (by decide), hl kLen (by decide), hl kRandLen (by decide), hus, hlen,
      hrlen, e1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt e2, Nat.mod_eq_of_lt e3]
    exact decide_eq_decide.mpr (by omega)) rfl) fun s₁ ⟨⟨hcf, hm₁⟩, k₁⟩ => ?_)
  have hg₁ : Good s₁ B Z w mi := ⟨hg.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans hg.rdi, by rw [hm₁]; exact hg.hdr⟩
  refine WP.seq (WP.ite (decide (r.length < used + 8 * w)) (by simp [eval, hcf]) (fun h => ?_) (fun h => ?_))
  · -- Out of octets: `kStat := 0`.
    simp only [decide_eq_true_eq] at h
    have hst : InRegions s₁.wr (off B (8 * kStat)) 8 :=
      hg₁.scr.st (by have := hdr_lt_slot w 8 (show kStat < 32 by decide); omega)
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = s₁.mem.writeW (off B (8 * kStat)) (BitVec.ofNat 64 0)) (by
      xrun [State.ea, hdr, hg₁.rdi, hdrOff, hst]; rfl) rfl) fun s₂ ⟨hm₂, k₂⟩ => ?_
    have hf₂ : Frm B [(8 * kStat, 8)] s.mem s₂.mem := by
      rw [hm₂, hm₁]; exact Frm.of_outside (writeW_outside _ B _ (d := 8 * kStat) (by unfold kStat sFn; omega)) (by simp)
    have hg₂ : Good s₂ B Z w mi := ⟨hg₁.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hg₁.rdi,
      Hdr.of_frm hg.hdr hf₂ (by rng_disj)⟩
    refine WP.mono (statCmp_ok hg₂ hZ (v := 0) (by decide) (by rw [hm₂, word_writeW_self]))
      fun t ⟨hz, hm, k⟩ => Or.inl ⟨by simp [eval, hz], ?_⟩
    have hres0 : res = none := hres.symm.trans (hres'.trans (ite_f (by omega) _ _))
    have hft : Frm B [(8 * kStat, 8)] s.mem t.mem :=
      hf₂.trans (show Frm B [(8 * kStat, 8)] s₂.mem t.mem by rw [hm]; exact Frm.refl _ _ _)
    refine ⟨⟨bm, hc.of_frm hd hft (hg₂.scr.congr k.2.2)
        ((k.gpr (by decide)).trans hg₂.rdi) (by rng_disj) (by rng_disj) (by rng_disj) (by rng_disj) (by rng_disj)⟩,
      ?_, ?_, ?_, (((hkeep.trans k₁).trans k₂).trans k).mono (by decide)⟩
    · intro _; rw [hm, hm₂, word_writeW_self]
    · intro b rest h; rw [hres0] at h; cases h
    · exact hfrm.trans (hft.mono (by simp [roundRanges, preRanges, witRanges, expRanges, bitRanges]))
  · -- A round.
    simp only [decide_eq_false_iff_not, Nat.not_lt] at h
    have hc₁ : MrCtx s₁ B Z w mi c bm := hc.of_frm hd (rs := []) (by rw [hm₁]; exact Frm.refl _ _ _) hg₁.scr
      hg₁.rdi (by simp) (by simp) (by simp) (by simp) (by simp)
    have hi61 : i < 2 ^ 61 := by
      have : 32 * i ≤ 8 * w * i := Nat.mul_le_mul_right _ (by omega)
      omega
    refine WP.mono (mrRound_ok (rp := rp) (used := used) (r := r) (i := i) (uni := uni) (ch := ch) M hd hc₁
      (by rw [hm₁]; exact hr2) hc1 hsh (by rw [hm₁]; exact hrp)
      (by rw [hm₁]; exact hus) (by rw [hm₁]; exact hlen) (hsrc.congrK (by rw [hm₁]; exact InScr.refl _ _ _) k₁) h
      (by rw [hm₁]; exact hi) (by rw [hm₁]; exact hun) (by rw [hm₁]; exact hchk) hi61 (by omega) hch)
      fun s₂ ⟨hc₂, hr₂, hus₂, hst₂, hcnt₂, hfr₂, k₂⟩ => ?_
    rw [ite_t h] at hres'
    generalize hwt : Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w))) = wt
      at hres' hc₂ hst₂ hcnt₂
    generalize hfv : Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2 wt.1 = f
      at hres' hst₂ hcnt₂
    have hfr : Frm B (roundRanges w) s.mem s₂.mem := by rw [← hm₁]; exact hfr₂
    have hdrop : r.length - (r.drop (used + 8 * w)).length = used + 8 * w := by rw [List.length_drop]; omega
    have hk : Keep mmRegs s₀ s₂ := ((hkeep.trans k₁).trans k₂).mono (by decide)
    refine WP.mono (statCmp_ok hc₂.good hZ (v := if f then (if i + 1 < 17 ∨ uni + wt.2.toNat < ch then 4 else 1) else 3)
      (by split <;> (try split) <;> decide) hst₂) fun t ⟨hz, hm, k⟩ => ?_
    have hct : MrCtx t B Z w mi c (wt.1 * 2 ^ (64 * w) % c) := hc₂.of_frm hd (rs := [])
      (by rw [hm]; exact Frm.refl _ _ _) (hc₂.good.scr.congr k.2.2) ((k.gpr (by decide)).trans hc₂.good.rdi)
      (by simp) (by simp) (by simp) (by simp) (by simp)
    have hkt : Keep mmRegs s₀ t := (hk.trans k).mono (by decide)
    have hft : Frm B (roundRanges w) s₀.mem t.mem := by rw [hm]; exact hfrm.trans hfr
    cases f
    · -- Composite.
      refine Or.inl ⟨by simp [eval, hz], ⟨_, hct⟩, fun h0 => ?_, fun b rest h1 => ?_, hft, hkt⟩
      · have h0' := hres'.symm.trans (hres.trans h0); simp at h0'
      · have h1' := hres'.symm.trans (hres.trans h1)
        simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h1'
        obtain ⟨h1a, h1b⟩ := h1'
        subst h1a h1b
        rw [hm, hst₂, hus₂, hdrop]; exact ⟨rfl, rfl⟩
    · obtain ⟨hI₂, hN₂⟩ := hcnt₂ rfl
      have hu : (if wt.2 = true then 1 else 0) = wt.2.toNat := by cases wt.2 <;> rfl
      simp only [↓reduceIte, hu] at hres'
      by_cases hcnd : i + 1 < 17 ∨ uni + wt.2.toNat < ch
      · -- On to the next witness.
        refine Or.inr ⟨by simp [eval, hz, hcnd], r.length - (used + 8 * w), by omega, ⟨⟨_, hct⟩, ?_, ?_, ?_, ?_, ?_,
          ?_, ⟨i + 1, uni + wt.2.toNat, used + 8 * w, by rw [hm]; exact hI₂, by rw [hm]; exact hN₂,
            by rw [hm]; exact hus₂, by omega, rfl, ?_, ?_, ?_, ?_⟩, hft, hkt⟩⟩
        · rw [hm]; exact hr₂
        · rw [hm, hfr.word_eq (roundRanges_hdr w (Or.inl rfl)) (by unfold kRand sFn; omega)]; exact hrp
        · rw [hm, hfr.word_eq (roundRanges_hdr w (Or.inr (Or.inl rfl))) (by unfold kLen sFn; omega)]; exact hlen
        · rw [hm, hfr.word_eq (roundRanges_hdr w (Or.inr (Or.inr (Or.inl rfl)))) (by unfold kRandLen sFn; omega)]
          exact hrlen
        · rw [hm, hfr.word_eq (roundRanges_hdr w (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (by unfold kChecks kE sFn; omega)]
          exact hchk
        · have hle : ∀ r ∈ roundRanges w, r.1 + r.2 ≤ Z := fun r hr => by
            have := roundRanges_le w r hr; have := hd.x; omega
          exact hsrc.congrK (by rw [hm]; exact InScr.of_frm hfr hle) ((k₁.trans k₂).trans k)
        · exact hcnd.imp (fun h => show i + 1 ≤ 16 by omega) id
        · rw [Nat.mul_add, Nat.mul_one]; omega
        · cases wt.2 <;> simp <;> omega
        · exact hres'.symm.trans hres
      · -- Probably prime.
        have hdone := VG.Proof.RsaKeyGen.mrLoop_done c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2
          (r.drop (used + 8 * w)) (i + 1) (uni + wt.2.toNat)
          (by intro h; exact hcnd (h.imp (fun h => by unfold Spec.RsaKeyGen.blindedChecks at h; omega) id))
        refine Or.inl ⟨by simp [eval, hz, hcnd], ⟨_, hct⟩, fun h0 => ?_, fun b rest h1 => ?_, hft, hkt⟩
        · have h0' := (hres'.symm.trans (hres.trans h0)); rw [hdone] at h0'; cases h0'
        · have h1' := (hres'.symm.trans (hres.trans h1))
          rw [hdone] at h1'
          simp only [Option.some.injEq, Prod.mk.injEq] at h1'
          obtain ⟨h1a, h1b⟩ := h1'
          subst h1a h1b
          rw [hm, hst₂, hus₂, hdrop]
          simp [hcnd]

/-- `millerRabin`: the witnesses from offset `used`, as `primalityTest`'s
loop from `(1, 0)`. -/
theorem millerRabin_ok (M : Mont) {B : Addr} {Z w : Nat} {mi : BitVec 64} {c ch bm : Nat} {rp : Addr}
    {r : List Byte} {s : State} {used : Nat} (hd : MrDims B Z w) (hc1 : 1 < c)
    (hsh : VG.Proof.RsaKeyGen.PrimeShape (64 * w) c) (hrl : r.length < 2 ^ 64) (hch : ch < 2 ^ 62)
    (hc : MrCtx s B Z w mi c bm) (hr2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c)
    (hrp : word s.mem B (8 * kRand) = rp) (hlen : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hrlen : word s.mem B (8 * kRandLen) = BitVec.ofNat 64 r.length)
    (hchk : word s.mem B (8 * kChecks) = BitVec.ofNat 64 ch) (hsrc : Src s B Z rp r)
    (hus : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used) (hu1 : 8 * w ≤ used) (hu2 : used ≤ r.length) :
    WP isa (seqs (millerRabin M.mm)) s (MrEnd B Z w mi c r s (mrRest c ch r 1 0 used)) := by
  have hg := hc.good
  have hZ := hd.z
  have hnw := hg.scr.nowrap
  have hs : ∀ i < 32, InRegions s.wr (off B (8 * i)) 8 := fun i hi =>
    hg.scr.st (by have := hdr_lt_slot w 8 hi; omega)
  unfold millerRabin
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t => t.mem = (s.mem.writeW (off B (8 * kI)) (BitVec.ofNat 64 1)).writeW
      (off B (8 * kUni)) (BitVec.ofNat 64 0)) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hs kI (by decide), hs kUni (by decide)]
    rfl) rfl) fun s₁ ⟨hm₁, k₁⟩ => ?_)
  have hf₁ : Frm B [(8 * kI, 8), (8 * kUni, 8)] s.mem s₁.mem := by
    rw [hm₁]
    exact (Frm.of_outside (writeW_outside _ B _ (d := 8 * kI) (by unfold kI kElen sFn; omega)) (by simp)).trans
      (Frm.of_outside (writeW_outside _ B _ (d := 8 * kUni) (by unfold kUni kP sFn; omega)) (by simp))
  have hg₁ : Good s₁ B Z w mi := ⟨hg.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans hg.rdi,
    Hdr.of_frm hg.hdr hf₁ (by rng_disj)⟩
  have hh : ∀ {k}, k = kRand ∨ k = kLen ∨ k = kRandLen ∨ k = kChecks ∨ k = kUsed ∨ k = kOut →
      word s₁.mem B (8 * k) = word s.mem B (8 * k) := fun {k} hk => by
    rw [hm₁]
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]
  refine WP.loop (MrSt B Z w mi c ch rp r s (mrRest c ch r 1 0 used))
    (fun n t hI => mrIter_ok M hd hc1 hsh hrl hch n t hI) (r.length - used) s₁ ?_
  refine ⟨⟨bm, hc.of_frm hd hf₁ hg₁.scr hg₁.rdi (by rng_disj) (by rng_disj) (by rng_disj) (by rng_disj)
      (by rng_disj)⟩, ?_, by rw [hh (Or.inl rfl)]; exact hrp, by rw [hh (Or.inr (Or.inl rfl))]; exact hlen,
    by rw [hh (Or.inr (Or.inr (Or.inl rfl)))]; exact hrlen, by rw [hh (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; exact hchk,
    hsrc.congrK (InScr.of_frm hf₁ (by
      have := hdr_lt_slot w 8 (show 31 < 32 by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, kI, kElen, kUni, kP, sFn]
      omega)) k₁,
    ⟨1, 0, used, by rw [hm₁, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self],
      by rw [hm₁, word_writeW_self], by rw [hh (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))]; exact hus, hu2, rfl,
      Or.inl (by decide), by omega, by omega, rfl⟩,
    hf₁.mono (by simp [roundRanges, preRanges, witRanges, expRanges, bitRanges]), k₁.mono (by decide)⟩
  rw [hf₁.wv_eq (d := slot w aR2) (k := w) (by rng_disj)
    (by have := slot_le (w := w) (show aR2 < 8 by decide); omega)]; exact hr2

end VG.Proof.RsaKeyGen.X86_64

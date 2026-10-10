import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrWit
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrLoop
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrTail

/-!
# A candidate on AArch64: one round of Miller–Rabin

`roundPre_ok`: the witness `b`, `b R mod c` into `aXm` and `aB`, and
`y := 1` (`R mod c` into `aY`). `mrRound_ok`: one witness `b` from the next
`8 w` octets; `kStat := 3` if `mrIteration` says `b` proves `c` composite,
otherwise the counters advance and `kStat` is 4 to go on (fewer than 17
witnesses, or fewer uniform ones than `checks`) or 1.
-/

namespace VG.Proof.RsaKeyGen.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64
open VG.Proof.Rsa (slot_lt)
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Bignum.Public (aN aX aAcc aTmp aR2 aXm aY sCnt sK)

/-- The octets of `rand` from `a`. -/
theorem Src.seg {s : State} {B : Addr} {Z : Nat} {rp : Addr} {r : List Byte} (h : Src s B Z rp r) {a n : Nat}
    (ha : a + n ≤ r.length) : Src s B Z (rp + BitVec.ofNat 64 a) (VG.Proof.RsaKeyGen.seg r a n) := by
  have hl : (VG.Proof.RsaKeyGen.seg r a n).length = n := by
    simp only [VG.Proof.RsaKeyGen.seg, List.length_take, List.length_drop]; omega_using [ha]
  have he : ∀ i, rp + BitVec.ofNat 64 a + BitVec.ofNat 64 i = rp + BitVec.ofNat 64 (a + i) := fun i => by
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [he]; exact h.rd (a + i) (by omega_using [ha, hl, hi])
  · rw [he, h.val (a + i) (by omega_using [ha, hl, hi])]
    simp only [VG.Proof.RsaKeyGen.seg, List.getElem_take, List.getElem_drop]
  · rw [he]; exact h.out (a + i) (by omega_using [ha, hl, hi])

/-- What the start of a round changes. -/
def preRanges (w : Nat) : List (Nat × Nat) :=
  witRanges w ++ [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2)),
    (slot w aB, 8 * (w + 2)), (slot w aY, 8 * (w + 2))]

/-- What a round changes. -/
def roundRanges (w : Nat) : List (Nat × Nat) :=
  preRanges w ++ expRanges w ++ [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)]

/-- Disjointness of a range from each of a list of literal ranges of a round. -/
macro "rd_disj" : tactic => `(tactic| (
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, roundRanges, preRanges,
    witRanges, expRanges, bitRanges, List.cons_append, List.nil_append, slot, hdrBytes, aN, aX, aAcc, aTmp, aR2,
    aY, aXm, aB, aR1, aRm1, kG, kFlag, kPlen, kV, kT0, sCnt, kBits, kT2, kWords, kT1, kUsed, kU, kI, kElen, kUni,
    kP, kStat, kChecks, kE, kRand, kLen, sK, kRandLen, kOut, kUsedP, sFn, sMinv]
  and_intros <;> omega_arith))

/-- The ranges of a list of literal ranges are `KMut`. -/
macro "kmut" : tactic => `(tactic| (
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  and_intros <;> first | exact KMut.ofSlot _ _ _ | exact KMut.hdr (by decide)))

/-- `MrCtx` with a new witness. -/
theorem MrCtx.setB {s t : State} {B : Addr} {Z w c bm bm' : Nat} {rs : List (Nat × Nat)}
    (hc : MrCtx s B Z w c bm) (hf : Frm B rs s.mem t.mem) (hm : ∀ r ∈ rs, KMut r)
    {regs : List Reg} (k : Keep regs s t) (hr : .x0 ∉ regs)
    (dI : ∀ r ∈ rs, 8 * sMinv + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * sMinv)
    (dN : ∀ r ∈ rs, slot w aN + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aN)
    (d1 : ∀ r ∈ rs, slot w aR1 + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aR1)
    (dm : ∀ r ∈ rs, slot w aRm1 + 8 * w ≤ r.1 ∨ r.1 + r.2 ≤ slot w aRm1)
    (hb : wv t.mem B (slot w aB) w = bm') : MrCtx t B Z w c bm' := by
  have hn := hc.ws.scr.nowrap
  have hZ := hc.ws.hZ
  have e : ∀ {j : Nat}, j < 16 → slot w j + 8 * w ≤ Z := fun hj => by
    have := slot_lt (w := w) hj; omega_using [hZ, this]
  have e1 := e (show aR1 < 16 by decide)
  have em := e (show aRm1 < 16 by decide)
  have eN := e (show aN < 16 by decide)
  have hw1 := hc.ws.w1
  refine ⟨hc.ws.congr' hf hm k hr, ?_, ?_, hb, ?_, ?_⟩
  · rw [hf.word_eq (d := slot w aN) (fun r hr => by have := dN r hr; omega_using [hw1, this]) (by omega_using [hn, eN, hw1]),
      hf.word_eq (d := 8 * sMinv) dI (by simp only [sMinv] at *; have := hc.ws.h256; omega_using [])]
    exact hc.inv
  · rw [hf.wv_eq dN (by omega_using [hn, eN])]; exact hc.n
  · rw [hf.wv_eq d1 (by omega_using [hn, e1])]; exact hc.r1
  · rw [hf.wv_eq dm (by omega_using [hn, em])]; exact hc.rm1

/-- The start of a round. -/
theorem roundPre_ok (M : Mont) {s : State} {B : Addr} {Z w c bm : Nat} (hw4 : 4 ≤ w) (hw64 : w ≤ 64)
    (hc : MrCtx s B Z w c bm)
    (hR2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c) (hodd : c % 2 = 1) (hc1 : 1 < c)
    (hb : Spec.RsaKeyGen.bitLength (c - 1) = 64 * w)
    {rp : Addr} {used : Nat} {r : List Byte} (hR : word s.mem B (8 * kRand) = rp)
    (hU : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hsrc : Src s B Z rp r) (hlen : used + 8 * w ≤ r.length) :
    WP isa (seqs (mrWitness ++ [M.mm aXm aX aR2, copyA aB aXm, copyA aY aR1])) s fun t =>
      MrCtx t B Z w c
        ((Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))).1 *
          2 ^ (64 * w) % c) ∧
      wv t.mem B (slot w aY) w = 2 ^ (64 * w) % c ∧
      wv t.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c ∧
      word t.mem B (8 * kU) =
        mask (Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))).2 ∧
      word t.mem B (8 * kUsed) = BitVec.ofNat 64 (used + 8 * w) ∧
      Frm B (preRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.ws.scr.nowrap
  have hZ := hc.ws.hZ
  have hw' : w < 2 ^ 31 := by omega_using [hw64]
  have hRc : Nat.Coprime (2 ^ (64 * w)) c := VG.Proof.Bignum.coprime_pow2 hodd _
  have hc0 : 0 < c := by omega_using [hc1]
  have sl : ∀ {j : Nat}, j < 16 → slot w j + 8 * (w + 2) ≤ Z := fun hj => by
    have := slot_lt (w := w) hj; omega_using [hZ, this]
  have sR2 := sl (show aR2 < 16 by decide)
  have sB := sl (show aB < 16 by decide)
  have sY := sl (show aY < 16 by decide)
  have sXm := sl (show aXm < 16 by decide)
  refine wp_seqs_append (by simp [mrWitness]) (by simp) ?_
  refine WP.mono (mrWitness_ok hc hw4 hw64 hodd hb hR hU hK (Src.seg hsrc hlen) (by
    simp only [VG.Proof.RsaKeyGen.seg, List.length_take, List.length_drop]; omega_using [hlen]))
    fun s₁ ⟨hc₁, hx₁, hu₁, hus₁, hf₁, k₁⟩ => ?_
  generalize Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w))) = wt
    at hx₁ hu₁ ⊢
  have hR2₁ : wv s₁.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c := by
    rw [hf₁.wv_eq (d := slot w aR2) (k := w) (by rd_disj) (by omega_using [hn, sR2])]; exact hR2
  simp only [seqs]
  -- `b R mod c` into `aXm`.
  have hg₁ := hc₁.good
  refine WP.seq (WP.mono (M.mm_ok hg₁.1 hg₁.2 hc₁.ws.w1 hw' (o := aXm) (a := aX) (b := aR2) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc₁.inv
    (by rw [hR2₁, hc₁.n]; exact Nat.mod_lt _ hc0)) fun s₂ ⟨_, hlt₂, hy₂, ha₂, k₂⟩ => ?_)
  rw [hc₁.n] at hlt₂ hy₂
  rw [hx₁, hR2₁] at hy₂
  have hXm : wv s₂.mem B (slot w aXm) w = wt.1 * 2 ^ (64 * w) % c := by
    rw [← Nat.mod_eq_of_lt hlt₂]
    refine VG.Proof.Bignum.mont_cancel hRc ?_
    rw [hy₂, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]
  have f₂ : Frm B [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2))]
      s₁.mem s₂.mem := Frm.of_arrays ha₂ (by simp)
  have hc₂ : MrCtx s₂ B Z w c bm := hc₁.of_frm f₂ (by kmut) k₂ (by decide) (by rd_disj) (by rd_disj) (by rd_disj)
    (by rd_disj) (by rd_disj)
  have hR2₂ : wv s₂.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c := by
    rw [f₂.wv_eq (d := slot w aR2) (k := w) (by rd_disj) (by omega_using [hn, sR2])]; exact hR2₁
  -- `[aB] := b R mod c`.
  refine WP.seq (WP.mono (copyA_ok hc₂.ws (o := aB) (a := aXm) (by decide) (by decide) (by decide))
    fun s₃ ⟨hv₃, o₃, _, _, k₃⟩ => ?_)
  rw [hXm] at hv₃
  have f₃ : Frm B [(slot w aB, 8 * (w + 2))] s₂.mem s₃.mem :=
    Frm.of_outside (o₃.mono (o' := slot w aB) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_using [])) (by simp)
  have hc₃ := hc₂.setB f₃ (by kmut) k₃ (by decide) (by rd_disj) (by rd_disj) (by rd_disj) (by rd_disj) hv₃
  -- `[aY] := R mod c`.
  refine WP.mono (copyA_ok hc₃.ws (o := aY) (a := aR1) (by decide) (by decide) (by decide))
    fun t ⟨hv, o, _, _, k⟩ => ?_
  rw [hc₃.r1] at hv
  have ft : Frm B [(slot w aY, 8 * (w + 2))] s₃.mem t.mem :=
    Frm.of_outside (o.mono (o' := slot w aY) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega_using [])) (by simp)
  have f13 : Frm B [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aXm, 8 * (w + 2)),
      (slot w aB, 8 * (w + 2)), (slot w aY, 8 * (w + 2))] s₁.mem t.mem :=
    ((f₂.mono (by simp)).trans (f₃.mono (by simp))).trans (ft.mono (by simp))
  refine ⟨hc₃.of_frm ft (by kmut) k (by decide) (by rd_disj) (by rd_disj) (by rd_disj) (by rd_disj) (by rd_disj),
    hv, ?_, ?_, ?_, ?_, (((k₁.trans k₂).trans k₃).trans k).mono (by decide)⟩
  · rw [f13.wv_eq (d := slot w aR2) (k := w) (by rd_disj) (by omega_using [hn, sR2])]; exact hR2₁
  · rw [f13.word_eq (d := 8 * kU) (by rd_disj) (by simp only [kU]; omega_using [])]; exact hu₁
  · rw [f13.word_eq (d := 8 * kUsed) (by rd_disj) (by simp only [kUsed, sFn]; omega_using [])]; exact hus₁
  · exact (hf₁.mono fun r hr => List.mem_append_left _ hr).trans (f13.mono (by simp))

theorem mrRound_eq (mul : Nat → Nat → Nat → Prog isa) : mrRound mul =
    (mrWitness ++ [mul aXm aX aR2, copyA aB aXm, copyA aY aR1]) ++ (mrExpLoop mul ++ ([.block [ldh .x3 kFlag],
      .ite (.zero .x .x3) (.block [movi .x3 3, sth .x3 kStat])
        (.block [ldh .x3 kI, .addImm .x .x3 .x3 1, sth .x3 kI, ldh .x4 kU, movi .x5 1, .logic .and .x .x4 .x4 .x5,
          ldh .x5 kUni, .add .x .x4 .x4 .x5, sth .x4 kUni,
          movi .x9 4, movi .x10 1, movi .x5 17, .subs .x .x6 .x3 .x5, .csel .x .x13 .x10 .x9, ldh .x5 kChecks,
          .subs .x .x6 .x4 .x5, .csel .x .x13 .x13 .x9, sth .x13 kStat])] : List (Prog isa))) := by
  simp only [mrRound, List.append_assoc]

/-- The witness of a round, and whether it passes. -/
abbrev wtOf (c w used : Nat) (r : List Byte) : Nat × Bool :=
  Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))

abbrev passOf (c w used : Nat) (r : List Byte) : Bool :=
  Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2 (wtOf c w used r).1

/-- `mrRound` up to its flag: the witness, and the flag of its test. -/
theorem roundMid_ok (M : Mont) {s : State} {B : Addr} {Z w c bm : Nat} (hw4 : 4 ≤ w) (hw64 : w ≤ 64)
    (hc : MrCtx s B Z w c bm)
    (hR2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c) (hc1 : 1 < c)
    (hsh : VG.Proof.RsaKeyGen.PrimeShape (64 * w) c)
    {rp : Addr} {used : Nat} {r : List Byte} (hR : word s.mem B (8 * kRand) = rp)
    (hU : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hsrc : Src s B Z rp r) (hlen : used + 8 * w ≤ r.length)
    {i uni ch : Nat} (hI : word s.mem B (8 * kI) = BitVec.ofNat 64 i)
    (hN : word s.mem B (8 * kUni) = BitVec.ofNat 64 uni) (hC : word s.mem B (8 * kChecks) = BitVec.ofNat 64 ch) :
    WP isa (seqs ((mrWitness ++ [M.mm aXm aX aR2, copyA aB aXm, copyA aY aR1]) ++ mrExpLoop M.mm)) s fun s₂ =>
      MrCtx s₂ B Z w c ((wtOf c w used r).1 * 2 ^ (64 * w) % c) ∧
      word s₂.mem B (8 * kFlag) = mask (passOf c w used r) ∧ word s₂.mem B (8 * kI) = BitVec.ofNat 64 i ∧
      word s₂.mem B (8 * kUni) = BitVec.ofNat 64 uni ∧ word s₂.mem B (8 * kChecks) = BitVec.ofNat 64 ch ∧
      word s₂.mem B (8 * kU) = mask (wtOf c w used r).2 ∧
      word s₂.mem B (8 * kUsed) = BitVec.ofNat 64 (used + 8 * w) ∧
      wv s₂.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c ∧
      Frm B (preRanges w ++ expRanges w) s.mem s₂.mem ∧ Keep mmRegs s s₂ := by
  have hodd : c % 2 = 1 := hsh.1
  obtain ⟨_, hb, _⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega_using [hw4]) hsh
  have hn := hc.ws.scr.nowrap
  have hZ := hc.ws.hZ
  have sR2 : slot w aR2 + 8 * (w + 2) ≤ Z := by have := slot_lt (w := w) (show aR2 < 16 by decide); omega_using [hZ, this]
  refine wp_seqs_append (by simp [mrWitness]) (by simp [mrExpLoop]) ?_
  refine WP.mono (roundPre_ok M hw4 hw64 hc hR2 hodd hc1 hb hR hU hK hsrc hlen)
    fun s₁ ⟨hc₁, hy₁, hr₁, hu₁, hus₁, hf₁, k₁⟩ => ?_
  refine WP.mono (mrExpLoop_ok M hc₁ hw4 hw64 hodd hc1 hy₁) fun s₂ ⟨hc₂, _, hfl₂, hf₂, k₂⟩ => ?_
  have hflag : VG.Proof.RsaKeyGen.mrPre c (wtOf c w used r).1 (64 * w) (64 * w - 1) false = passOf c w used r := by
    rw [← VG.Proof.RsaKeyGen.mrRun_pre]; exact (VG.Proof.RsaKeyGen.mrIteration_cand (by omega_using [hw4]) hsh false).symm
  rw [hflag] at hfl₂
  have hf02 : Frm B (preRanges w ++ expRanges w) s.mem s₂.mem :=
    (hf₁.mono fun r hr => List.mem_append_left _ hr).trans (hf₂.mono fun r hr => List.mem_append_right _ hr)
  refine ⟨hc₂, hfl₂, ?_, ?_, ?_, ?_, ?_, ?_, hf02, (k₁.trans k₂).mono (by decide)⟩
  · rw [hf02.word_eq (d := 8 * kI) (by rd_disj) (by simp only [kI, kElen, sFn]; omega_using [])]; exact hI
  · rw [hf02.word_eq (d := 8 * kUni) (by rd_disj) (by simp only [kUni, kP, sFn]; omega_using [])]; exact hN
  · rw [hf02.word_eq (d := 8 * kChecks) (by rd_disj) (by simp only [kChecks, kE, sFn]; omega_using [])]; exact hC
  · rw [hf₂.word_eq (d := 8 * kU) (by rd_disj) (by simp only [kU]; omega_using [])]; exact hu₁
  · rw [hf₂.word_eq (d := 8 * kUsed) (by rd_disj) (by simp only [kUsed, sFn]; omega_using [])]; exact hus₁
  · rw [hf₂.wv_eq (d := slot w aR2) (k := w) (by rd_disj) (by omega_using [hn, sR2])]; exact hr₁

/-- `mrRound`. -/
theorem mrRound_ok (M : Mont) {s : State} {B : Addr} {Z w c bm : Nat} (hw4 : 4 ≤ w) (hw64 : w ≤ 64)
    (hc : MrCtx s B Z w c bm)
    (hR2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c) (hc1 : 1 < c)
    (hsh : VG.Proof.RsaKeyGen.PrimeShape (64 * w) c)
    {rp : Addr} {used : Nat} {r : List Byte} (hR : word s.mem B (8 * kRand) = rp)
    (hU : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hsrc : Src s B Z rp r) (hlen : used + 8 * w ≤ r.length)
    {i uni ch : Nat} (hI : word s.mem B (8 * kI) = BitVec.ofNat 64 i)
    (hN : word s.mem B (8 * kUni) = BitVec.ofNat 64 uni) (hC : word s.mem B (8 * kChecks) = BitVec.ofNat 64 ch)
    (hi : i < 2 ^ 61) (huni : uni < 2 ^ 61) (hch : ch < 2 ^ 62) :
    WP isa (seqs (mrRound M.mm)) s fun t =>
      MrCtx t B Z w c
        ((Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))).1 *
          2 ^ (64 * w) % c) ∧
      wv t.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c ∧
      word t.mem B (8 * kUsed) = BitVec.ofNat 64 (used + 8 * w) ∧
      word t.mem B (8 * kStat) = BitVec.ofNat 64
        (if Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2
            (Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))).1 then
          (if i + 1 < 17 ∨ uni + (Spec.RsaKeyGen.witness (c - 1)
              (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))).2.toNat < ch then 4 else 1)
        else 3) ∧
      (Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2
          (Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))).1 = true →
        word t.mem B (8 * kI) = BitVec.ofNat 64 (i + 1) ∧
        word t.mem B (8 * kUni) = BitVec.ofNat 64 (uni + (Spec.RsaKeyGen.witness (c - 1)
          (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))).2.toNat)) ∧
      Frm B (roundRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hc.ws.scr.nowrap
  have hZ := hc.ws.hZ
  have sR2 : slot w aR2 + 8 * (w + 2) ≤ Z := by have := slot_lt (w := w) (show aR2 < 16 by decide); omega_using [hZ, this]
  rw [mrRound_eq, ← List.append_assoc]
  refine wp_seqs_append (by simp [mrWitness]) (by simp) ?_
  refine WP.mono (roundMid_ok M hw4 hw64 hc hR2 hc1 hsh hR hU hK hsrc hlen hI hN hC)
    fun s₂ ⟨hc₂, hfl₂, hI₂, hN₂, hC₂, hU₂, hUs₂, hR2₂, hf02, k₁₂⟩ => ?_
  simp only [wtOf, passOf] at hc₂ hU₂ hfl₂
  generalize Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w))) = wt
    at hc₂ hU₂ hfl₂ ⊢
  generalize Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1
    (Spec.Rsa.splitTwos (c - 1)).2 wt.1 = f at hfl₂ ⊢
  refine WP.mono (roundTail_ok hc₂.ws hfl₂ hI₂ hU₂ hN₂ hC₂ (by omega_arith) (by omega_using [huni]) hch) fun t ⟨hm, k⟩ => ?_
  have hft : Frm B [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)] s₂.mem t.mem := by
    rw [hm]
    have wI := Frm.of_outside (rs := [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)])
      (writeW_outside s₂.mem B (BitVec.ofNat 64 (i + 1)) (d := 8 * kI) (by simp only [kI, kElen, sFn]; omega_using []))
      (by simp)
    cases f
    · exact Frm.of_outside (writeW_outside _ B _ (d := 8 * kStat) (by simp only [kStat, sFn]; omega_using [])) (by simp)
    · exact (wI.trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kUni) (by simp only [kUni, kP, sFn]; omega_using []))
        (by simp))).trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kStat) (by simp only [kStat, sFn]; omega_using []))
        (by simp))
  refine ⟨hc₂.of_frm hft (by kmut) k (by decide) (by rd_disj) (by rd_disj) (by rd_disj) (by rd_disj) (by rd_disj),
    ?_, ?_, ?_, ?_, ?_, (k₁₂.trans k).mono (by decide)⟩
  · rw [hft.wv_eq (d := slot w aR2) (k := w) (by rd_disj) (by omega_using [hn, sR2])]; exact hR2₂
  · rw [hft.word_eq (d := 8 * kUsed) (by rd_disj) (by simp only [kUsed, sFn]; omega_using [])]; exact hUs₂
  · rw [hm]; cases f <;> simp only [↓reduceIte, Bool.false_eq_true, word_writeW_self]
  · intro hf
    rw [hm, hf]
    simp only [↓reduceIte]
    refine ⟨?_, ?_⟩
    · rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        word_writeW_self]
    · rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · exact (hf02.mono fun r hr => List.mem_append_left _ hr).trans (hft.mono (by simp))

end VG.Proof.RsaKeyGen.AArch64

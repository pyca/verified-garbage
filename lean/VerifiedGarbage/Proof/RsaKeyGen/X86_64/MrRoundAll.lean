module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrRound
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrLoop
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrExp
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Bignum.CrtExp
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-!
# A candidate on x86-64: `mrRound`

`mrRound_ok`: one witness `b` from the next `8 w` octets; `kStat := 3` if
`mrIteration` says `b` proves `c` composite, otherwise the counters advance
and `kStat` is 4 to go on (fewer than 17 witnesses, or fewer uniform ones
than `checks`) or 1.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- What a round changes. -/
def roundRanges (w : Nat) : List (Nat × Nat) :=
  preRanges w ++ expRanges w ++ [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)]

/-- `roundRanges`'s ranges, in the header and in the arrays. -/
theorem roundRanges_shape (w : Nat) : VG.Proof.RsaKeyGen.RangeShape w [(200, 8), (240, 8), (208, 8), (224, 8), (248, 8), (176, 8), (216, 8), (160, 8), (168, 8), (232, 8)]
    [(1, 1), (2, 1), (3, 1), (5, 1), (8, 16), (6, 1)] (roundRanges w) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, List.cons_append, List.nil_append,
    expRanges, preRanges, roundRanges, tabRanges, winRanges, witRanges, Public.aX, Public.aAcc, Public.aTmp, Public.aXm, Public.aY, aX, aAcc, aTmp, aXm, aY, VG.Proof.Bignum.tabBytes, kT0, sFn, kG, kV, kWords, kBits, kFlag, kPlen, kI, kElen, kU, kUni, kP, kStat, kT1, kT2, kUsed] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inr ⟨(1, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inl (by decide)
  · exact .inl (by decide)
  · exact .inr ⟨(2, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(3, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(5, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(8, 16), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(2, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(3, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(6, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inl (by decide)
  · exact .inl (by decide)
  · exact .inr ⟨(2, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(3, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(6, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inr ⟨(5, 1), by decide, by simp only [slot, hdrBytes]; omega_using [],
      by simp only [slot, hdrBytes]; omega_using []⟩
  · exact .inl (by decide)
  · exact .inl (by decide)
  · exact .inl (by decide)
  · exact .inl (by decide)
  · exact .inl (by decide)
  · exact .inl (by decide)
  · exact .inl (by decide)
  · exact .inl (by decide)

theorem mrRound_eq (mul : Nat → Nat → Nat → Prog isa) : mrRound mul =
    (mrWitness ++ [mul aXm aX aR2] ++ tabBuild mul) ++
    (mrExpLoop mul ++ ([.block [.mov32 .rcx (.imm 3), .mov .rax (.mem (hdr kFlag)), .alu .test .rax (.reg .rax)],
      .ite .e (.block [])
        (.block [.mov .rax (.mem (hdr kI)), .alu .add .rax (.imm 1), .store (hdr kI) .rax,
          .mov .rdx (.mem (hdr kU)), .alu .and .rdx (.imm 1), .alu .add .rdx (.mem (hdr kUni)), .store (hdr kUni) .rdx,
          .alu .cmp .rax (.imm 17), .alu .sbb .rcx (.reg .rcx), .alu .cmp .rdx (.mem (hdr kChecks)),
          .alu .sbb .rax (.reg .rax), .alu .or .rcx (.reg .rax), .alu .and .rcx (.imm 3), .alu .add .rcx (.imm 1)]),
      .block [.store (hdr kStat) .rcx]] : List (Prog isa))) := by
  simp only [mrRound, preparedRound, List.append_assoc]

theorem preRanges_lt (w : Nat) : ∀ r ∈ preRanges w, r.1 + r.2 ≤ slot w aE := by
  intro r hr
  simp only [preRanges, List.mem_append] at hr
  rcases hr with (hr | hr) | hr
  · have := slot_le (w := w) (show aX < 8 by decide)
    have := slot_mono w (show 8 ≤ aE by decide)
    have := hdr_lt_slot w 8 (show 31 < 32 by decide)
    simp only [witRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [kUsed, kU, sFn] at * <;> omega_arith
  · have := slot_le (w := w) (show aAcc < 8 by decide)
    have := slot_le (w := w) (show aTmp < 8 by decide)
    have := slot_le (w := w) (show aXm < 8 by decide)
    have := slot_mono w (show 8 ≤ aE by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith
  · exact tabRanges_lt w r hr

/-- The witness of a round, and whether it passes. -/
abbrev wtOf (c w used : Nat) (r : List Byte) : Nat × Bool :=
  Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))

abbrev passOf (c w used : Nat) (r : List Byte) : Bool :=
  Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2 (wtOf c w used r).1

/-- `mrRound` up to its flag: the witness, and the flag of its test. -/
theorem roundMid_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm : Nat}
    (hd : MrDims B Z w) (hc : MrCtx s B Z w mi c bm) (hE : ECtx s.mem B w c)
    (hR2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c) (hc1 : 1 < c)
    (hsh : VG.Proof.RsaKeyGen.PrimeShape (64 * w) c)
    {rp : Addr} {used : Nat} {r : List Byte} (hR : word s.mem B (8 * kRand) = rp)
    (hU : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hsrc : Src s B Z rp r) (hlen : used + 8 * w ≤ r.length)
    {i uni ch : Nat} (hI : word s.mem B (8 * kI) = BitVec.ofNat 64 i)
    (hN : word s.mem B (8 * kUni) = BitVec.ofNat 64 uni) (hC : word s.mem B (8 * kChecks) = BitVec.ofNat 64 ch) :
    WP isa (seqs ((mrWitness ++ [M.mm aXm aX aR2] ++ tabBuild M.mm) ++ mrExpLoop M.mm)) s fun s₂ =>
      (∃ bm', MrCtx s₂ B Z w mi c bm') ∧
      word s₂.mem B (8 * kFlag) = mask (passOf c w used r) ∧ word s₂.mem B (8 * kI) = BitVec.ofNat 64 i ∧
      word s₂.mem B (8 * kUni) = BitVec.ofNat 64 uni ∧ word s₂.mem B (8 * kChecks) = BitVec.ofNat 64 ch ∧
      word s₂.mem B (8 * kU) = mask (wtOf c w used r).2 ∧
      word s₂.mem B (8 * kUsed) = BitVec.ofNat 64 (used + 8 * w) ∧
      wv s₂.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c ∧
      Frm B (preRanges w ++ expRanges w) s.mem s₂.mem ∧ Keep mmRegs s s₂ := by
  have hw4 := hd.w4
  have hodd : c % 2 = 1 := hsh.1
  obtain ⟨_, hb, _⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega_arith) hsh
  have hn := hc.good.scr.nowrap
  have hEn : B.toNat + slot w aE + 8 * (w + 1) ≤ 2 ^ 64 := by have := aE_fits hd; have := hd.z; omega_arith
  refine wp_seqs_append (by simp [mrWitness]) (by simp [mrExpLoop]) ?_
  refine WP.mono (roundPre_ok M hd hc hR2 hodd hc1 hb hR hU hK hsrc hlen)
    fun s₁ ⟨hc₁, hT₁, hy₁, hr₁, hu₁, hus₁, hf₁, k₁⟩ => ?_
  have hE₁ : ECtx s₁.mem B w c := hE.of_frm hf₁ (fun r hr => Or.inr (preRanges_lt w r hr)) hEn
  refine WP.mono (mrExpLoop_ok M hd hc₁ hT₁ hE₁ hodd hc1 hy₁) fun s₂ ⟨hc₂, _, hfl₂, hf₂, k₂⟩ => ?_
  rw [VG.Proof.RsaKeyGen.wEnd_cand _ (by omega_arith) hsh] at hfl₂
  have hf02 : Frm B (preRanges w ++ expRanges w) s.mem s₂.mem :=
    (hf₁.mono fun r hr => List.mem_append_left _ hr).trans (hf₂.mono fun r hr => List.mem_append_right _ hr)
  have hdh : ∀ k, k = kI ∨ k = kUni ∨ k = kChecks ∨ k = kU ∨ k = kUsed →
      ∀ r ∈ expRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := fun k hk => by
    simp only [expRanges, winRanges, List.cons_append, List.nil_append]
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> rng_disj
  refine ⟨⟨_, hc₂⟩, hfl₂, ?_, ?_, ?_, ?_, ?_, ?_, hf02, (k₁.trans k₂).mono (by decide)⟩
  · rw [hf02.word_eq (d := 8 * kI) (by
        simp only [preRanges, witRanges, tabRanges, expRanges, winRanges, List.cons_append, List.nil_append]
        rng_disj) (by unfold kI kElen sFn; omega_arith)]; exact hI
  · rw [hf02.word_eq (d := 8 * kUni) (by
        simp only [preRanges, witRanges, tabRanges, expRanges, winRanges, List.cons_append, List.nil_append]
        rng_disj) (by unfold kUni kP sFn; omega_arith)]; exact hN
  · rw [hf02.word_eq (d := 8 * kChecks) (by
        simp only [preRanges, witRanges, tabRanges, expRanges, winRanges, List.cons_append, List.nil_append]
        rng_disj) (by unfold kChecks kE sFn; omega_arith)]; exact hC
  · rw [hf₂.word_eq (d := 8 * kU) (hdh kU (by simp)) (by unfold kU sFn; omega_arith)]; exact hu₁
  · rw [hf₂.word_eq (d := 8 * kUsed) (hdh kUsed (by simp)) (by unfold kUsed sFn; omega_arith)]; exact hus₁
  · rw [hf₂.wv_eq (d := slot w aR2) (k := w) (by
        simp only [expRanges, winRanges, List.cons_append, List.nil_append]
        rng_disj) (by have := slot_le (w := w) (show aR2 < 8 by decide); have := hd.z; omega_arith)]
    exact hr₁

/-- `mrRound`. -/
theorem mrRound_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm : Nat}
    (hd : MrDims B Z w) (hc : MrCtx s B Z w mi c bm) (hE : ECtx s.mem B w c)
    (hR2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c) (hc1 : 1 < c)
    (hsh : VG.Proof.RsaKeyGen.PrimeShape (64 * w) c)
    {rp : Addr} {used : Nat} {r : List Byte} (hR : word s.mem B (8 * kRand) = rp)
    (hU : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hsrc : Src s B Z rp r) (hlen : used + 8 * w ≤ r.length)
    {i uni ch : Nat} (hI : word s.mem B (8 * kI) = BitVec.ofNat 64 i)
    (hN : word s.mem B (8 * kUni) = BitVec.ofNat 64 uni) (hC : word s.mem B (8 * kChecks) = BitVec.ofNat 64 ch)
    (hi : i < 2 ^ 61) (huni : uni < 2 ^ 61) (hch : ch < 2 ^ 62) :
    WP isa (seqs (mrRound M.mm)) s fun t =>
      (∃ bm', MrCtx t B Z w mi c bm') ∧
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
  have hn := hc.good.scr.nowrap
  rw [mrRound_eq, ← List.append_assoc]
  refine wp_seqs_append (by simp [mrWitness]) (by simp) ?_
  refine WP.mono (roundMid_ok M hd hc hE hR2 hc1 hsh hR hU hK hsrc hlen hI hN hC)
    fun s₂ ⟨⟨bm₂, hc₂⟩, hfl₂, hI₂, hN₂, hC₂, hU₂, hUs₂, hR2₂, hf02, k₁₂⟩ => ?_
  simp only [wtOf, passOf] at hU₂ hfl₂
  generalize hwt : Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w))) = wt
    at hU₂ hfl₂ ⊢
  generalize hfv : Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1
    (Spec.Rsa.splitTwos (c - 1)).2 wt.1 = f at hfl₂ ⊢
  have hg₂ := hc₂.good
  refine WP.mono (roundTail_ok hg₂ hd.z hfl₂ hI₂ hU₂ hN₂ hC₂ (by omega_arith) (by omega_arith) hch) fun t ⟨hm, k⟩ => ?_
  have hft : Frm B [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)] s₂.mem t.mem := by
    rw [hm]
    have wI := Frm.of_outside (rs := [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)])
      (writeW_outside s₂.mem B (BitVec.ofNat 64 (i + 1)) (d := 8 * kI) (by unfold kI kElen sFn; omega_arith)) (by simp)
    cases f
    · exact Frm.of_outside (writeW_outside _ B _ (d := 8 * kStat) (by unfold kStat sFn; omega_arith)) (by simp)
    · exact (wI.trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kUni) (by unfold kUni kP sFn; omega_arith))
        (by simp))).trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kStat) (by unfold kStat sFn; omega_arith))
        (by simp))
  have hgt : Good t B Z w mi := ⟨hg₂.scr.congr k.2.2, (k.gpr (by decide)).trans hg₂.rdi,
    Hdr.of_frm hg₂.hdr hft (VG.Proof.RsaKeyGen.HdrShapeC.geD rfl rfl)⟩
  refine ⟨⟨bm₂, hc₂.of_frm hd hft hgt.scr hgt.rdi (VG.Proof.RsaKeyGen.HdrShapeC.geD rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)⟩,
    ?_, ?_, ?_, ?_, ?_, ((k₁₂.trans k).mono (by decide))⟩
  · rw [hft.wv_eq (d := slot w aR2) (k := w) (VG.Proof.RsaKeyGen.SlotShapeC.apartW rfl rfl)
      (by have := slot_le (w := w) (show aR2 < 8 by decide); have := hd.z; omega_arith)]; exact hR2₂
  · rw [hft.word_eq (d := 8 * kUsed) (VG.Proof.RsaKeyGen.HdrShapeC.hdrW rfl rfl) (by unfold kUsed sFn; omega_arith)]; exact hUs₂
  · rw [hm]; cases f <;> simp only [↓reduceIte, Bool.false_eq_true, word_writeW_self]
  · intro hf
    rw [hm, hf]
    simp only [↓reduceIte]
    refine ⟨?_, ?_⟩
    · rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        word_writeW_self]
    · rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · exact (hf02.mono fun r hr => by simp only [roundRanges, List.mem_append] at hr ⊢; grind).trans
      (hft.mono (by simp [roundRanges]))

end VG.Proof.RsaKeyGen.X86_64

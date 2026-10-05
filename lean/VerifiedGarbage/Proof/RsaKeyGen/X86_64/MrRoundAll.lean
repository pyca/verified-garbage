import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrRound

/-!
# A candidate on x86-64: `mrRound`

`mrRound_ok`: one witness `b` from the next `8 w` octets; `kStat := 3` if
`mrIteration` says `b` proves `c` composite, otherwise the counters advance
and `kStat` is 4 to go on (fewer than 17 witnesses, or fewer uniform ones
than `checks`) or 1.
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- What a round changes. -/
def roundRanges (w : Nat) : List (Nat × Nat) :=
  preRanges w ++ expRanges w ++ [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)]

theorem mrRound_eq (mul : Nat → Nat → Nat → Prog isa) : mrRound mul =
    (mrWitness ++ [mul aXm aX aR2,
      .block ([.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aXm)))] ++ extBase aB .rbx), copyWords,
      .block ([.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aY)))] ++ extBase aR1 .rsi), copyWords]) ++
    (mrExpLoop mul ++ [.block [.mov32 .rcx (.imm 3), .mov .rax (.mem (hdr kFlag)), .alu .test .rax (.reg .rax)],
      .ite .e (.block [])
        (.block [.mov .rax (.mem (hdr kI)), .alu .add .rax (.imm 1), .store (hdr kI) .rax,
          .mov .rdx (.mem (hdr kU)), .alu .and .rdx (.imm 1), .alu .add .rdx (.mem (hdr kUni)), .store (hdr kUni) .rdx,
          .alu .cmp .rax (.imm 17), .alu .sbb .rcx (.reg .rcx), .alu .cmp .rdx (.mem (hdr kChecks)),
          .alu .sbb .rax (.reg .rax), .alu .or .rcx (.reg .rax), .alu .and .rcx (.imm 3), .alu .add .rcx (.imm 1)]),
      .block [.store (hdr kStat) .rcx]]) := rfl

/-- The witness of a round, and whether it passes. -/
abbrev wtOf (c w used : Nat) (r : List Byte) : Nat × Bool :=
  Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w)))

abbrev passOf (c w used : Nat) (r : List Byte) : Bool :=
  Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2 (wtOf c w used r).1

/-- `mrRound` up to its flag: the witness, and the flag of its test. -/
theorem roundMid_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm : Nat}
    (hd : MrDims B Z w) (hc : MrCtx s B Z w mi c bm)
    (hR2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c) (hc1 : 1 < c)
    (hsh : VG.Proof.RsaKeyGen.PrimeShape (64 * w) c)
    {rp : Addr} {used : Nat} {r : List Byte} (hR : word s.mem B (8 * kRand) = rp)
    (hU : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hsrc : Src s B Z rp r) (hlen : used + 8 * w ≤ r.length)
    {i uni ch : Nat} (hI : word s.mem B (8 * kI) = BitVec.ofNat 64 i)
    (hN : word s.mem B (8 * kUni) = BitVec.ofNat 64 uni) (hC : word s.mem B (8 * kChecks) = BitVec.ofNat 64 ch) :
    WP isa (seqs ((mrWitness ++ [M.mm aXm aX aR2,
      .block ([.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aXm)))] ++ extBase aB .rbx), copyWords,
      .block ([.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aY)))] ++ extBase aR1 .rsi), copyWords]) ++
      mrExpLoop M.mm)) s fun s₂ =>
      MrCtx s₂ B Z w mi c ((wtOf c w used r).1 * 2 ^ (64 * w) % c) ∧
      word s₂.mem B (8 * kFlag) = mask (passOf c w used r) ∧ word s₂.mem B (8 * kI) = BitVec.ofNat 64 i ∧
      word s₂.mem B (8 * kUni) = BitVec.ofNat 64 uni ∧ word s₂.mem B (8 * kChecks) = BitVec.ofNat 64 ch ∧
      word s₂.mem B (8 * kU) = mask (wtOf c w used r).2 ∧
      word s₂.mem B (8 * kUsed) = BitVec.ofNat 64 (used + 8 * w) ∧
      wv s₂.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c ∧
      Frm B (preRanges w ++ expRanges w) s.mem s₂.mem ∧ Keep mmRegs s s₂ := by
  have hw4 := hd.w4
  have hodd : c % 2 = 1 := hsh.1
  obtain ⟨_, hb, _⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega) hsh
  have hn := hc.good.scr.nowrap
  refine wp_seqs_append (by simp [mrWitness]) (by simp [mrExpLoop]) ?_
  refine WP.mono (roundPre_ok M hd hc hR2 hodd hc1 hb hR hU hK hsrc hlen) fun s₁ ⟨hc₁, hy₁, hr₁, hu₁, hus₁, hf₁, k₁⟩ => ?_
  refine WP.mono (mrExpLoop_ok M hd hc₁ hodd hc1 hy₁) fun s₂ ⟨hc₂, _, hfl₂, hf₂, k₂⟩ => ?_
  have hflag : mrPre c (wtOf c w used r).1 (64 * w) (64 * w - 1) false = passOf c w used r := by
    rw [← mrRun_pre]; exact (VG.Proof.RsaKeyGen.mrIteration_cand (by omega) hsh false).symm
  rw [hflag] at hfl₂
  have hf02 : Frm B (preRanges w ++ expRanges w) s.mem s₂.mem :=
    (hf₁.mono fun r hr => List.mem_append_left _ hr).trans (hf₂.mono fun r hr => List.mem_append_right _ hr)
  refine ⟨hc₂, hfl₂, ?_, ?_, ?_, ?_, ?_, ?_, hf02, (k₁.trans k₂).mono (by decide)⟩
  · rw [hf02.word_eq (d := 8 * kI) (by
        simp only [preRanges, witRanges, expRanges, bitRanges, List.cons_append, List.nil_append]
        rng_disj) (by unfold kI kElen sFn; omega)]; exact hI
  · rw [hf02.word_eq (d := 8 * kUni) (by
        simp only [preRanges, witRanges, expRanges, bitRanges, List.cons_append, List.nil_append]
        rng_disj) (by unfold kUni kP sFn; omega)]; exact hN
  · rw [hf02.word_eq (d := 8 * kChecks) (by
        simp only [preRanges, witRanges, expRanges, bitRanges, List.cons_append, List.nil_append]
        rng_disj) (by unfold kChecks kE sFn; omega)]; exact hC
  · rw [hf₂.word_eq (d := 8 * kU) (by simp only [expRanges, bitRanges, List.cons_append, List.nil_append]; rng_disj)
      (by unfold kU sFn; omega)]; exact hu₁
  · rw [hf₂.word_eq (d := 8 * kUsed) (by simp only [expRanges, bitRanges, List.cons_append, List.nil_append]; rng_disj)
      (by unfold kUsed sFn; omega)]; exact hus₁
  · rw [hf₂.wv_eq (d := slot w aR2) (k := w) (by
        simp only [expRanges, bitRanges, List.cons_append, List.nil_append]
        rng_disj) (by have := slot_le (w := w) (show aR2 < 8 by decide); have := hd.z; omega)]
    exact hr₁

/-- `mrRound`. -/
theorem mrRound_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm : Nat}
    (hd : MrDims B Z w) (hc : MrCtx s B Z w mi c bm)
    (hR2 : wv s.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % c) (hc1 : 1 < c)
    (hsh : VG.Proof.RsaKeyGen.PrimeShape (64 * w) c)
    {rp : Addr} {used : Nat} {r : List Byte} (hR : word s.mem B (8 * kRand) = rp)
    (hU : word s.mem B (8 * kUsed) = BitVec.ofNat 64 used) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hsrc : Src s B Z rp r) (hlen : used + 8 * w ≤ r.length)
    {i uni ch : Nat} (hI : word s.mem B (8 * kI) = BitVec.ofNat 64 i)
    (hN : word s.mem B (8 * kUni) = BitVec.ofNat 64 uni) (hC : word s.mem B (8 * kChecks) = BitVec.ofNat 64 ch)
    (hi : i < 2 ^ 61) (huni : uni < 2 ^ 61) (hch : ch < 2 ^ 62) :
    WP isa (seqs (mrRound M.mm)) s fun t =>
      MrCtx t B Z w mi c
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
  have hn := hc.good.scr.nowrap
  rw [mrRound_eq, ← List.append_assoc]
  refine wp_seqs_append (by simp [mrWitness]) (by simp) ?_
  refine WP.mono (roundMid_ok M hd hc hR2 hc1 hsh hR hU hK hsrc hlen hI hN hC)
    fun s₂ ⟨hc₂, hfl₂, hI₂, hN₂, hC₂, hU₂, hUs₂, hR2₂, hf02, k₁₂⟩ => ?_
  simp only [wtOf, passOf] at hc₂ hU₂ hfl₂
  generalize hwt : Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (VG.Proof.RsaKeyGen.seg r used (8 * w))) = wt
    at hc₂ hU₂ hfl₂ ⊢
  generalize hfv : Spec.RsaKeyGen.mrIteration c (Spec.Rsa.splitTwos (c - 1)).1
    (Spec.Rsa.splitTwos (c - 1)).2 wt.1 = f at hfl₂ ⊢
  have hg₂ := hc₂.good
  refine WP.mono (roundTail_ok hg₂ hd.z hfl₂ hI₂ hU₂ hN₂ hC₂ (by omega) (by omega) hch) fun t ⟨hm, k⟩ => ?_
  have hft : Frm B [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)] s₂.mem t.mem := by
    rw [hm]
    have wI := Frm.of_outside (rs := [(8 * kI, 8), (8 * kUni, 8), (8 * kStat, 8)])
      (writeW_outside s₂.mem B (BitVec.ofNat 64 (i + 1)) (d := 8 * kI) (by unfold kI kElen sFn; omega)) (by simp)
    cases f
    · exact Frm.of_outside (writeW_outside _ B _ (d := 8 * kStat) (by unfold kStat sFn; omega)) (by simp)
    · exact (wI.trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kUni) (by unfold kUni kP sFn; omega))
        (by simp))).trans (Frm.of_outside (writeW_outside _ B _ (d := 8 * kStat) (by unfold kStat sFn; omega))
        (by simp))
  have hgt : Good t B Z w mi := ⟨hg₂.scr.congr k.2.2, (k.gpr (by decide)).trans hg₂.rdi,
    Hdr.of_frm hg₂.hdr hft (by rng_disj)⟩
  refine ⟨hc₂.of_frm hd hft hgt.scr hgt.rdi (by rng_disj) (by rng_disj) (by rng_disj) (by rng_disj) (by rng_disj),
    ?_, ?_, ?_, ?_, ?_, ((k₁₂.trans k).mono (by decide))⟩
  · rw [hft.wv_eq (d := slot w aR2) (k := w) (by rng_disj)
      (by have := slot_le (w := w) (show aR2 < 8 by decide); have := hd.z; omega)]; exact hR2₂
  · rw [hft.word_eq (d := 8 * kUsed) (by rng_disj) (by unfold kUsed sFn; omega)]; exact hUs₂
  · rw [hm]; cases f <;> simp only [↓reduceIte, Bool.false_eq_true, word_writeW_self]
  · intro hf
    rw [hm, hf]
    simp only [↓reduceIte]
    refine ⟨?_, ?_⟩
    · rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
        word_writeW_self]
    · rw [hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self]
  · exact (hf02.mono fun r hr => by simp only [roundRanges, List.mem_append] at hr ⊢; tauto).trans
      (hft.mono (by simp [roundRanges]))

end VG.Proof.RsaKeyGen.X86_64

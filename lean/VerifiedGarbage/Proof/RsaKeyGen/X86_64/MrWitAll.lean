import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrWit

/-!
# A candidate on x86-64: `mrWitness`

`mrWitness_ok`: the witness `Spec.RsaKeyGen.witness (c − 1) x` for the next
`8 w` octets `x` of `rand` in `aX`, the mask of its uniformity in `kU`, and
`kUsed` advanced.
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- What `mrWitness` changes. -/
def witRanges (w : Nat) : List (Nat × Nat) := [(slot w aX, 8 * (w + 2)), (8 * kUsed, 8), (8 * kU, 8)]

theorem mrWitness_eq : mrWitness =
    ([.block [.mov .rsi (.mem (hdr kRand)), .mov .rax (.mem (hdr kUsed)), .alu .add .rsi (.reg .rax),
        .mov .rcx (.mem (hdr kLen)), .mov .rbx (.mem (hdr (sArr aX))), .alu .add .rax (.reg .rcx),
        .store (hdr kUsed) .rax], loadBE] : List (Prog isa)) ++
    (([.block [.mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (hdr (sArr aX))), .mov .rbp (.mem (at0 .rbx)),
        .alu .and .rbp (.imm (BitVec.ofInt 32 (-2)))],
      wordLoop 1 [.mov .rax (.mem (ix .rbx .r14)), .alu .or .rbp (.reg .rax)]] : List (Prog isa)) ++
    (([.block [.alu .cmp .rbp (.imm 1), .alu .sbb .r15 (.reg .r15),
        .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1))), .mov .r10 (.mem (hdr (sArr aN))), .mov .rax (.mem (at0 .rbx)),
        .alu .or .rax (.imm 1), .alu .sub .rax (.mem (at0 .r10)), cfToRbp],
      wordLoop 1 cmpBody] : List (Prog isa)) ++
    ([.block [.alu .and .r15 (.reg .rbp), .store (hdr kU) .r15, .alu .xor .r15 (.imm (BitVec.ofInt 32 (-1))),
      .mov .rax (.reg .r15), .alu .and .rax (.imm 2), .alu .or .rax (.mem (at0 .rbx)), .store (at0 .rbx) .rax,
      .movImm64 .rax (BitVec.ofNat 64 (2 ^ 63)), .alu .and .rax (.reg .r15),
      .alu .xor .rax (.imm (BitVec.ofInt 32 (-1))), .alu .and .rax (.mem (ix .rbx .r12 (-8))),
      .store (ix .rbx .r12 (-8)) .rax]] : List (Prog isa)))) := rfl

/-- `mrWitness`. -/
theorem mrWitness_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {c bm : Nat} (hd : MrDims B Z w)
    (hc : MrCtx s B Z w mi c bm) (hodd : c % 2 = 1) (hb : Spec.RsaKeyGen.bitLength (c - 1) = 64 * w)
    {rp : Addr} {u : Nat} {bs : List Byte} (hR : word s.mem B (8 * kRand) = rp)
    (hU : word s.mem B (8 * kUsed) = BitVec.ofNat 64 u) (hK : word s.mem B (8 * kLen) = BitVec.ofNat 64 (8 * w))
    (hsrc : Src s B Z (rp + BitVec.ofNat 64 u) bs) (hbl : bs.length = 8 * w) :
    WP isa (seqs mrWitness) s fun t => MrCtx t B Z w mi c bm ∧
      wv t.mem B (slot w aX) w = (Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip bs)).1 ∧
      word t.mem B (8 * kU) = mask (Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip bs)).2 ∧
      word t.mem B (8 * kUsed) = BitVec.ofNat 64 (u + 8 * w) ∧
      Frm B (witRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hg := hc.good
  have hZ := hd.z
  have hw4 := hd.w4
  have hw' : w < 2 ^ 27 := by have := hd.w64; omega
  have hn := hg.scr.nowrap
  have sX := Nat.le_trans (slot_le (w := w) (show aX < 8 by decide)) hZ
  rw [mrWitness_eq]
  refine wp_seqs_append (by simp) (by simp) ?_
  refine WP.mono (witLoad_ok hg hZ (by omega) hw' hR hU hK hsrc hbl) fun s₁ ⟨hx₁, hu₁, hf₁, hg₁, k₁⟩ => ?_
  have hc₁ : MrCtx s₁ B Z w mi c bm := hc.of_frm hd hf₁ hg₁.scr hg₁.rdi (by rng_disj) (by rng_disj) (by rng_disj)
    (by rng_disj) (by rng_disj)
  have hx : Spec.Rsa.os2ip bs < 2 ^ (64 * w) := by
    have := os2ip_lt bs; rw [hbl, pow256_eq] at this; rwa [show 8 * (8 * w) = 64 * w by omega] at this
  refine wp_seqs_append (by simp) (by simp) ?_
  refine WP.mono (witLow_ok hg₁ hZ (by omega) (by omega)) fun s₂ ⟨hlow, hbx₂, h12₂, hm₂, k₂⟩ => ?_
  have hg₂ : Good s₂ B Z w mi := ⟨hg₁.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hg₁.rdi, by rw [hm₂]; exact hg₁.hdr⟩
  refine wp_seqs_append (by simp) (by simp) ?_
  refine WP.mono (witCmp_ok hg₂ hZ (by omega) (by omega) hbx₂ h12₂ (by rw [hm₂]; exact hlow))
    fun s₃ ⟨h15, hbp, hm₃, k₃⟩ => ?_
  rw [hm₂, hx₁] at h15
  rw [hm₂, hx₁, hc₁.n] at hbp
  have hg₃ : Good s₃ B Z w mi := ⟨hg₂.scr.congr k₃.2.2, (k₃.gpr (by decide)).trans hg₂.rdi, by rw [hm₃]; exact hg₂.hdr⟩
  refine WP.mono (witForce_ok hg₃ hZ (by omega) (by omega) ((k₃.gpr (by decide)).trans hbx₂)
    ((k₃.gpr (by decide)).trans h12₂) h15 hbp) fun t ⟨hm, k⟩ => ?_
  rw [hm₃, hm₂] at hm
  generalize hu : (decide (2 ≤ Spec.Rsa.os2ip bs) && decide (Spec.Rsa.os2ip bs + (1 - Spec.Rsa.os2ip bs % 2) < c)) = uu
    at hm
  have hwit := witness_eq hodd hb hx
  rw [hu] at hwit
  -- The words of `aX` after the stores.
  have hw0 : word t.mem B (slot w aX) = if uu then word s₁.mem B (slot w aX) else word s₁.mem B (slot w aX) ||| 2 := by
    rw [hm, (writeW_outside _ B _ (d := slot w aX + 8 * (w - 1)) (by omega)).word (d := slot w aX) (Or.inl (by omega))
      (by omega), word_writeW_self]
  have hwt : word t.mem B (slot w aX + 8 * (w - 1)) = if uu then word s₁.mem B (slot w aX + 8 * (w - 1))
      else word s₁.mem B (slot w aX + 8 * (w - 1)) &&& ~~~(BitVec.ofNat 64 (2 ^ 63)) := by
    rw [hm, word_writeW_self]
  have hwm : ∀ j, 0 < j → j < w - 1 → word t.mem B (slot w aX + 8 * j) = word s₁.mem B (slot w aX + 8 * j) := by
    intro j hj0 hj
    rw [hm, (writeW_outside _ B _ (d := slot w aX + 8 * (w - 1)) (by omega)).word (Or.inl (by omega)) (by omega),
      (writeW_outside _ B _ (d := slot w aX) (by omega)).word (Or.inr (by omega)) (by omega),
      (writeW_outside _ B _ (d := 8 * kU) (by unfold kU sFn; omega)).word
        (Or.inr (by unfold slot kU sFn aX hdrBytes; omega)) (by omega)]
  have hft : Frm B (witRanges w) s₁.mem t.mem := by
    rw [hm]
    exact ((Frm.of_outside (writeW_outside _ B _ (d := 8 * kU) (by unfold kU sFn; omega)) (by simp [witRanges])).trans
      (Frm.of_outside ((writeW_outside _ B _ (d := slot w aX) (by omega)).mono (o' := slot w aX) (n' := 8 * (w + 2))
        (Nat.le_refl _) (by omega)) (by simp [witRanges]))).trans
      (Frm.of_outside ((writeW_outside _ B _ (d := slot w aX + 8 * (w - 1)) (by omega)).mono (o' := slot w aX)
        (n' := 8 * (w + 2)) (by omega) (by omega)) (by simp [witRanges]))
  have hgt : Good t B Z w mi := ⟨hg₃.scr.congr k.2.2, (k.gpr (by decide)).trans hg₃.rdi,
    Hdr.of_frm (by rw [← hm₂, ← hm₃]; exact hg₃.hdr) hft (by simp only [witRanges]; rng_disj)⟩
  refine ⟨hc₁.of_frm hd hft hgt.scr hgt.rdi (by simp only [witRanges]; rng_disj) (by simp only [witRanges]; rng_disj) (by simp only [witRanges]; rng_disj) (by simp only [witRanges]; rng_disj) (by simp only [witRanges]; rng_disj),
    ?_, ?_, ?_, (Frm.mono hf₁ (by simp [witRanges])).trans hft, ((((k₁.trans k₂).trans k₃).trans k).mono (by decide))⟩
  · rw [hwit, ← hx₁]
    cases uu
    · exact wv_force (by omega) (by rw [hw0]; rfl) (by rw [hwt]; rfl) hwm
    · exact wv_congr2 fun i hi => by
        rcases Nat.eq_zero_or_pos i with rfl | hi0
        · rw [Nat.mul_zero, Nat.add_zero, hw0]; rfl
        · by_cases hit : i = w - 1
          · rw [hit, hwt]; rfl
          · exact hwm i hi0 (by omega)
  · rw [hwit, hm, (writeW_outside _ B _ (d := slot w aX + 8 * (w - 1)) (by omega)).word (d := 8 * kU)
      (Or.inl (by unfold slot kU sFn aX hdrBytes; omega)) (by unfold kU sFn; omega),
      (writeW_outside _ B _ (d := slot w aX) (by omega)).word (d := 8 * kU)
      (Or.inl (by unfold slot kU sFn aX hdrBytes; omega)) (by unfold kU sFn; omega), word_writeW_self]
  · rw [hm, (writeW_outside _ B _ (d := slot w aX + 8 * (w - 1)) (by omega)).word (d := 8 * kUsed)
      (Or.inl (by unfold slot kUsed sFn aX hdrBytes; omega)) (by unfold kUsed sFn; omega),
      (writeW_outside _ B _ (d := slot w aX) (by omega)).word (d := 8 * kUsed)
      (Or.inl (by unfold slot kUsed sFn aX hdrBytes; omega)) (by unfold kUsed sFn; omega),
      hdrStore_hdr _ _ _ (by decide) (by decide) (by decide)]; exact hu₁

end VG.Proof.RsaKeyGen.X86_64

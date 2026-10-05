import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontRest

/-!
# A candidate on x86-64: all of `montSetup`

`montSetup_ok`: `-c⁻¹`, `R² mod c` in `aR2`, `R mod c` in `aR1`,
`c − R mod c` in `aRm1` and `checksW w` in `kChecks`, changing only
`msRanges`.
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- Disjointness of a range from each of a list of literal ranges of the
scratch space (header words and arrays). -/
macro "rng_disj" : tactic => `(tactic| (
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, slot, hdrBytes, aN, aX, aAcc,
    aTmp, aR2, aXm, aY, aOne, aB, aR1, aRm1, aTab, kT0, kChecks, kE, sFn, sMinv, sW, sArr, kG, kV, kWords, kBits,
    kFlag, kPlen, kI, kElen, kU, kUni, kP, kStat, kT1, kT2, kUsed]
  and_intros <;> omega))

/-- What `montSetup` changes. -/
def msRanges (w : Nat) : List (Nat × Nat) :=
  [(8 * sMinv, 8), (slot w aOne, 8 * (w + 2)), (slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)),
    (slot w aR2, 8 * (w + 2)), (8 * kT0, 8), (slot w aY, 8 * (w + 2)), (slot w aR1, 8 * (w + 2)),
    (slot w aRm1, 8 * (w + 2)), (8 * kChecks, 8)]

theorem montSetup_eq (mul : Nat → Nat → Nat → Prog isa) : montSetup mul =
    [.block (([.mov .r10 (.mem (hdr (sArr aN))), .mov .r12 (.mem (hdr sW)), .mov .rbx (.mem (at0 .r10))] :
      List Instr) ++ minv ++ ([.store (hdr sMinv) .r15, .mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)] : List Instr)),
      setWord aOne .rcx] ++ (msR2 mul ++ ([mul aY aR2 aOne] ++
    ([.block ([.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aY)))] ++ extBase aR1 .rbx), copyWords] ++
    ([.block ([.mov .r12 (.mem (hdr sW)), .mov .r8 (.mem (hdr (sArr aN)))] ++ extBase aR1 .r10 ++
        extBase aRm1 .rsi ++ [.mov32 .rbp (.imm 0)]),
      wordLoop 0 [cfFromRbp, .mov .rax (.mem (ix .r8 .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)),
        .store (ix .rsi .r14) .rax, cfToRbp]] ++
    [.block [.mov .rcx (.mem (hdr sW)), .mov32 .rax (.imm 27), .alu .cmp .rcx (.imm 5)],
      .ite .b (.block []) (seqs [
        .block [.mov32 .rax (.imm 8), .alu .cmp .rcx (.imm 6)],
        .ite .b (.block []) (seqs [
          .block [.mov32 .rax (.imm 7), .alu .cmp .rcx (.imm 7)],
          .ite .b (.block []) (seqs [
            .block [.mov32 .rax (.imm 6), .alu .cmp .rcx (.imm 8)],
            .ite .b (.block []) (seqs [
              .block [.mov32 .rax (.imm 5), .alu .cmp .rcx (.imm 22)],
              .ite .b (.block []) (seqs [
                .block [.mov32 .rax (.imm 4), .alu .cmp .rcx (.imm 59)],
                .ite .b (.block []) (.block [.mov32 .rax (.imm 3)])])])])])]),
      .block [.store (hdr kChecks) .rax]])))) := rfl

/-- `montSetup` for the odd candidate `c` of `4 ≤ w ≤ 64` words, its top bit
set. -/
theorem montSetup_ok (M : Mont) {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} {N : Nat}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) (hXZ : slot w aRm1 + 8 * (w + 2) ≤ Z) (hw : 4 ≤ w) (hw64 : w ≤ 64)
    (hn : wv s.mem B (slot w aN) w = N) (hodd : N % 2 = 1) (htop : 2 ^ (64 * w - 1) ≤ N) :
    WP isa (seqs (montSetup M.mm)) s fun t => ∃ mi' : BitVec 64, Good t B Z w mi' ∧
      ((word t.mem B (slot w aN)).toNat * mi'.toNat + 1) % 2 ^ 64 = 0 ∧
      wv t.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % N ∧
      wv t.mem B (slot w aR1) w = 2 ^ (64 * w) % N ∧
      wv t.mem B (slot w aRm1) w = N - 2 ^ (64 * w) % N ∧
      word t.mem B (8 * kChecks) = BitVec.ofNat 64 (Proof.RsaKeyGen.checksW w) ∧
      Frm B (msRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hnw := hg.scr.nowrap
  have hw' : w < 2 ^ 31 := by omega
  have hR : Nat.Coprime (2 ^ (64 * w)) N := VG.Proof.Bignum.coprime_pow2 hodd _
  have hN1 : 1 < N := by
    have : 2 ≤ 2 ^ (64 * w - 1) := by
      rw [show 64 * w - 1 = (64 * w - 2) + 1 by omega, Nat.pow_succ]; have := Nat.two_pow_pos (64 * w - 2); omega
    omega
  have hsN : slot w aN + 8 * w ≤ Z := by have := slot_le (w := w) (show aN < 8 by decide); omega
  have hodd0 : (word s.mem B (slot w aN)).toNat % 2 = 1 := by
    have := wv_low s.mem B (slot w aN) (w - 1)
    rw [show w - 1 + 1 = w by omega, hn] at this; omega
  rw [montSetup_eq]
  refine wp_seqs_append (by simp) (by simp [msR2]) ?_
  simp only [seqs]
  -- `-c⁻¹`, and 1.
  refine WP.seq (WP.mono (msHead_ok hg hZ hodd0) fun s₁ ⟨hg₁, hinv₁, hdx₁, hcx₁, h12₁, hm₁, k₁⟩ => ?_)
  generalize hmi : s₁.gpr .r15 = mi' at hg₁ hinv₁ hm₁
  have hn₁ : wv s₁.mem B (slot w aN) w = N := by
    rw [hm₁, hdrStore_wv _ _ _ (by decide) (by decide) (by omega)]; exact hn
  have hw0₁ : word s₁.mem B (slot w aN) = word s.mem B (slot w aN) := by
    rw [hm₁, hdrStore_word _ _ _ (by decide) (by decide) (by omega)]
  refine WP.mono (setWord_ok hg₁.scr hg₁.rdi hg₁.hdr hZ h12₁ (by omega) hw' (o := aOne) (by decide) (ri := .rcx)
    (by decide) (i := 0) (by omega) hcx₁) fun s₂ ⟨hv₂, ho₂, k₂⟩ => ?_
  rw [hdx₁] at hv₂
  have ha₂ : Arrays B w [aOne] s₁.mem s₂.mem :=
    Arrays.of_outside (List.mem_singleton_self _) ho₂ (Nat.le_refl _) (Nat.le_refl _)
  have hg₂ : Good s₂ B Z w mi' := ⟨hg₁.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hg₁.rdi, ha₂.hdr hg₁.hdr⟩
  have hn₂ : wv s₂.mem B (slot w aN) w = N := by rw [ha₂.wv_of_not_mem (by decide) (by decide) (by omega)]; exact hn₁
  have hw0₂ : word s₂.mem B (slot w aN) = word s.mem B (slot w aN) := by
    rw [ha₂.word0_of_not_mem (by decide) (by decide) (by omega) (by omega)]; exact hw0₁
  -- `R² mod c`.
  refine wp_seqs_append (by simp [msR2]) (by simp) ?_
  refine WP.mono (msR2_ok M hg₂ hZ (by omega) (by omega) hn₂ (by rw [hw0₂]; exact hinv₁)
    ((k₂.gpr (by decide)).trans h12₁) hodd htop) fun s₃ ⟨hg₃, hr₃, hf₃, k₃⟩ => ?_
  have hn₃ : wv s₃.mem B (slot w aN) w = N := by
    rw [hf₃.wv_eq (d := slot w aN) (k := w) (by simp only [msR2Ranges]; rng_disj) (by omega)]; exact hn₂
  have hw0₃ : word s₃.mem B (slot w aN) = word s.mem B (slot w aN) := by
    rw [hf₃.word_eq (d := slot w aN) (by simp only [msR2Ranges]; rng_disj) (by omega)]; exact hw0₂
  have hone₃ : wv s₃.mem B (slot w aOne) w = 1 := by
    rw [hf₃.wv_eq (d := slot w aOne) (k := w) (by simp only [msR2Ranges]; rng_disj)
      (by have := slot_le (w := w) (show aOne < 8 by decide); omega),
      hv₂]; rfl
  -- `R mod c`.
  refine wp_seqs_append (by simp) (by simp) ?_
  refine WP.mono (M.mm_ok hg₃ hZ (by omega) hw' (o := aY) (a := aR2) (b := aOne) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [hw0₃]; exact hinv₁)
    (by rw [hone₃, hn₃]; exact hN1)) fun s₄ ⟨hg₄, hlt₄, hy₄, ha₄, k₄⟩ => ?_
  rw [hn₃, hr₃, hone₃] at hy₄
  rw [hn₃] at hlt₄
  have hY : wv s₄.mem B (slot w aY) w = 2 ^ (64 * w) % N := by
    rw [← Nat.mod_eq_of_lt hlt₄]
    refine VG.Proof.Bignum.mont_cancel hR ?_
    rw [hy₄, Nat.mul_one, Nat.mod_mod]
  have hn₄ : wv s₄.mem B (slot w aN) w = N := by rw [ha₄.wv_of_not_mem (by decide) (by decide) (by omega)]; exact hn₃
  have hw0₄ : word s₄.mem B (slot w aN) = word s.mem B (slot w aN) := by
    rw [ha₄.word0_of_not_mem (by decide) (by decide) (by omega) (by omega)]; exact hw0₃
  have hr₄ : wv s₄.mem B (slot w aR2) w = 2 ^ (64 * w) * 2 ^ (64 * w) % N := by
    rw [ha₄.wv_of_not_mem (by decide) (by decide) (by omega)]; exact hr₃
  -- `[aR1] := R mod c`.
  refine wp_seqs_append (by simp) (by simp) ?_
  refine WP.mono (copyToExt_ok hg₄ hZ (by omega) hw' (a := aY) (d := aR1) (by decide) (by decide)
    (by unfold slot aR1 aRm1 at *; omega)) fun s₅ ⟨hv₅, ho₅, k₅⟩ => ?_
  rw [hY] at hv₅
  have hg₅ : Good s₅ B Z w mi' := ⟨hg₄.scr.congr k₅.2.2, (k₅.gpr (by decide)).trans hg₄.rdi,
    Hdr.outside hg₄.hdr ho₅ (by unfold slot; omega)⟩
  have hout5 : ∀ {j : Nat}, j < 8 → wv s₅.mem B (slot w j) w = wv s₄.mem B (slot w j) w := fun {j} hj =>
    ho₅.wv (Or.inl (by have := slot_le (w := w) hj; have : slot w 8 ≤ slot w aR1 := (by unfold slot aR1; omega); omega))
      (by have := slot_le (w := w) hj; omega)
  have hw0₅ : word s₅.mem B (slot w aN) = word s₄.mem B (slot w aN) :=
    ho₅.word (by unfold slot aR1 aN; omega) (by have := slot_le (w := w) (show aN < 8 by decide); omega)
  -- `[aRm1] := c − R mod c`.
  refine wp_seqs_append (by simp) (by simp) ?_
  refine WP.mono (msRm1_ok hg₅ hZ hXZ (by omega) hw' (by rw [hv₅, hout5 (by decide), hn₄]; exact Nat.mod_lt _ (by omega)))
    fun s₆ ⟨hv₆, ho₆, k₆⟩ => ?_
  rw [hv₅, hout5 (by decide), hn₄] at hv₆
  have hg₆ : Good s₆ B Z w mi' := ⟨hg₅.scr.congr k₆.2.2, (k₆.gpr (by decide)).trans hg₅.rdi,
    Hdr.outside hg₅.hdr ho₆ (by unfold slot; omega)⟩
  -- `checksW w`.
  refine WP.mono (msChecks_ok hg₆ hZ hw') fun t ⟨hm, k⟩ => ⟨mi', ?_, ?_, ?_, ?_, ?_, by rw [hm, word_writeW_self], ?_,
    ((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans k).mono (by decide)⟩
  · exact ⟨hg₆.scr.congr k.2.2, (k.gpr (by decide)).trans hg₆.rdi, by rw [hm]; exact hg₆.hdr.store (by decide) (by decide) _⟩
  · rw [hm, hdrStore_word _ _ _ (by decide) (by decide) (by omega),
      ho₆.word (by unfold slot aRm1 aN; omega) (by omega), hw0₅, hw0₄]; exact hinv₁
  · rw [hm, hdrStore_wv _ _ _ (by decide) (by decide) (by omega),
      ho₆.wv (Or.inl (by unfold slot aRm1 aR2; omega)) (by have := slot_le (w := w) (show aR2 < 8 by decide); omega),
      hout5 (by decide)]; exact hr₄
  · rw [hm, (writeW_outside _ B _ (d := 8 * kChecks) (by unfold kChecks kE sFn; omega)).wv (Or.inr (by unfold slot kChecks kE sFn aR1 hdrBytes; omega))
      (by unfold slot aR1 aRm1 at *; omega),
      ho₆.wv (Or.inl (by unfold slot aRm1 aR1; omega)) (by unfold slot aR1 aRm1 at *; omega)]; exact hv₅
  · rw [hm, (writeW_outside _ B _ (d := 8 * kChecks) (by unfold kChecks kE sFn; omega)).wv (Or.inr (by unfold slot kChecks kE sFn aRm1 hdrBytes; omega))
      (by omega)]; exact hv₆
  · have f₁ : Frm B (msRanges w) s.mem s₁.mem := by
      rw [hm₁]; exact Frm.of_outside (writeW_outside _ B _ (d := 8 * sMinv) (by unfold sMinv; omega)) (by simp [msRanges])
    have f₂ : Frm B (msRanges w) s₁.mem s₂.mem := Frm.of_arrays ha₂ (by simp [msRanges])
    have f₃ : Frm B (msRanges w) s₂.mem s₃.mem := hf₃.mono (by simp [msR2Ranges, msRanges])
    have f₄ : Frm B (msRanges w) s₃.mem s₄.mem := Frm.of_arrays ha₄ (by simp [msRanges])
    have f₅ : Frm B (msRanges w) s₄.mem s₅.mem :=
      Frm.of_outside (ho₅.mono (o' := slot w aR1) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega)) (by simp [msRanges])
    have f₆ : Frm B (msRanges w) s₅.mem s₆.mem :=
      Frm.of_outside (ho₆.mono (o' := slot w aRm1) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega)) (by simp [msRanges])
    have f₇ : Frm B (msRanges w) s₆.mem t.mem := by
      rw [hm]; exact Frm.of_outside (writeW_outside _ B _ (d := 8 * kChecks) (by unfold kChecks kE sFn; omega)) (by simp [msRanges])
    exact (((((f₁.trans f₂).trans f₃).trans f₄).trans f₅).trans f₆).trans f₇

end VG.Proof.RsaKeyGen.X86_64

import VerifiedGarbage.Proof.Bignum.X86_64.IfmaWin

/-!
# RSA with AVX512_IFMA on x86-64: the exponentiations

`expLoop` builds the table, then for each of the 128 bytes of the exponents
(at `oE` of each region, most significant first) puts the byte in the top
8 bits of `V` (`ldV_ok`) and does two windows (`wins_ok`): `Y ≡ x^E R`
becomes `x^(256 E + b) R`. After all of them `Y ≡ x^e R`, `e` the exponent
(`ev`), from `Y ≡ R` (`expLoop_ok`).
-/

namespace VG.Proof.Bignum.X86_64.AmmSym

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum.X86_64 (off word ofs Outside off_off Scr ofs_off writeW_outside)
open VG.Impl.Rsa.X86_64.CrtIfma (D oM oK0 oTab oS oV oX oY oE mask52)

/-- The first `i` bytes of prime `p`'s exponent, big-endian. -/
def ev (m : Mem) (B : Addr) (p : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => ev m B p i * 256 + (m (off B (D * p + oE + i))).toNat

theorem ror8_byte : ∀ b : BitVec 8, (b.setWidth 64).rotateRight 8 = BitVec.ofNat 64 (b.toNat * 2 ^ 56) := by
  decide +kernel

theorem ror60_v : ∀ b < 256, (BitVec.ofNat 64 (b * 2 ^ 56)).rotateRight 60 =
    BitVec.ofNat 64 (b % 16 * 2 ^ 60 + b / 16) := by
  decide +kernel

theorem nib_hi {m : Mem} {B : Addr} {p b : Nat} (hb : b < 256) (h : word m B (D * p + oV) = BitVec.ofNat 64 (b * 2 ^ 56)) :
    nib m B p = b / 16 := by
  unfold nib; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega

theorem nib_lo {m : Mem} {B : Addr} {p b : Nat} (hb : b < 256)
    (h : word m B (D * p + oV) = BitVec.ofNat 64 (b % 16 * 2 ^ 60 + b / 16)) : nib m B p = b % 16 := by
  unfold nib; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega


theorem ea_idx (t : State) (d : Nat) :
    t.ea { base := .rbx, index := some .r13, disp := ((d : Nat) : Int) } =
      t.gpr .rbx + t.gpr .r13 + BitVec.ofNat 64 d := by
  simp only [State.ea, BitVec.mul_one]
  exact congrArg _ (BitVec.ofInt_natCast ..)

/-- The byte `i` of prime `p`'s exponent. -/
abbrev ebyte (m : Mem) (B : Addr) (p i : Nat) : Nat := (m (off B (D * p + oE + i))).toNat

/-- Byte `i` of prime `p`'s exponent into the top 8 bits of `V`. -/
theorem ldV_ok {s : State} {B : Addr} {p i : Nat} (hp : p < 2) (hi : i < 128) (hB : s.gpr .rbx = B)
    (h13 : s.gpr .r13 = BitVec.ofNat 64 i) (hs : Scr s B (2 * D)) :
    WP isa (.block [.movzx8 .rax { base := .rbx, index := some .r13, disp := ((D * p + oE : Nat) : Int) },
        .shift .ror .rax 8, .store (VG.Impl.Rsa.X86_64.CrtIfma.at_ .rbx (D * p + oV)) .rax]) s fun s' =>
      s'.mem = s.mem.writeW (off B (D * p + oV)) (BitVec.ofNat 64 (ebyte s.mem B p i * 2 ^ 56)) ∧
      VG.Proof.MlKem.X86_64.Keep [.rax] s s' ∧ s'.mxcsr = s.mxcsr := by
  have hDp : D * p ≤ 3872 := by rcases D_mul hp with h | h <;> omega
  have e : B + BitVec.ofNat 64 i + BitVec.ofNat 64 (D * p + oE) = off B (D * p + oE + i) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm i]
  have hld : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 i + BitVec.ofNat 64 (D * p + oE)) 1 := by
    rw [e]
    obtain ⟨r, h, c⟩ := hs.region (d := D * p + oE + i) (n := 1) (by simp only [oE, D] at *; omega) (by decide)
    exact ⟨r, List.mem_append_right _ h, c⟩
  have hst : InRegions s.wr (B + BitVec.ofNat 64 (D * p + oV)) 8 :=
    let ⟨_, h, c⟩ := hs.region (d := D * p + oV) (n := 8) (by simp only [oV, D] at *; omega) (by decide); ⟨_, h, c⟩
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax] (Q := fun s' =>
    s'.mem = s.mem.writeW (off B (D * p + oV)) (BitVec.ofNat 64 (ebyte s.mem B p i * 2 ^ 56)) ∧
      s'.mxcsr = s.mxcsr) (by
    xrun [ea_idx, ea_at', hB, h13, hld, hst, ror8_byte]
    rw [e]
    and_intros <;> rfl) rfl)
    fun s' ⟨⟨a, b⟩, k⟩ => ⟨a, k, b⟩


/-- The windows' count down, `ZF` at 0. -/
theorem r14Dec_ok {s : State} {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 2) (h14 : s.gpr .r14 = BitVec.ofNat 64 n) :
    WP isa (.block [.alu .sub .r14 (.imm 1)]) s fun s' =>
      s'.gpr .r14 = BitVec.ofNat 64 (n - 1) ∧ s'.zf = some (decide (n - 1 = 0)) ∧
      VG.Proof.MlKem.X86_64.Keep [.r14] s s' ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr := by
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.r14] (Q := fun s' =>
    s'.gpr .r14 = BitVec.ofNat 64 (n - 1) ∧ s'.zf = some (decide (n - 1 = 0)) ∧ s'.mem = s.mem ∧
      s'.mxcsr = s.mxcsr) (by
    xrun [h14]
    have e : BitVec.ofNat 64 n - 1 = BitVec.ofNat 64 (n - 1) := by
      rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← VG.Offset.ofNat_sub_ofNat hn]
    and_intros
    · exact e
    · rw [e]; congr 1
      by_cases h : n - 1 = 0
      · simp only [h, decide_true]; rfl
      · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
        intro h'
        have := congrArg BitVec.toNat h'
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        exact h this
    all_goals rfl) rfl)
    fun s' ⟨⟨a, b, c, d⟩, k⟩ => ⟨a, b, k, c, d⟩

/-- `V` before window `j` of the byte `b`. -/
def vj (b j : Nat) : Nat := if j = 0 then b * 2 ^ 56 else b % 16 * 2 ^ 60 + b / 16

/-- After `j` windows of the bytes `bs`, from `t₀` where `Y ≡ x^E R`. -/
structure WinInv (t₀ : State) (B : Addr) (M k x : Nat → Nat) (Q : Prop) (E bs : Nat → Nat) (j : Nat) (t : State) :
    Prop where
  r14 : t.gpr .r14 = BitVec.ofNat 64 (2 - j)
  st : ExpSt t.mem B M k x Q (fun p => E p * 16 ^ j + bs p / 16 ^ (2 - j))
  v : j < 2 → ∀ p < 2, word t.mem B (D * p + oV) = BitVec.ofNat 64 (vj (bs p) j)
  frame : OutW B t₀.mem t.mem
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 →
    r ≠ .r14 → r ≠ .r15 → t.gpr r = t₀.gpr r
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  mxcsr : t.mxcsr = t₀.mxcsr

theorem win_exp {E b j : Nat} (hb : b < 256) (hj : j < 2) (n : Nat) (hn : n = if j = 0 then b / 16 else b % 16) :
    (E * 16 ^ j + b / 16 ^ (2 - j)) * 16 + n = E * 16 ^ (j + 1) + b / 16 ^ (2 - (j + 1)) := by
  subst hn
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceAdd,
    ite_true, ite_false, Nat.one_ne_zero] <;> omega

/-- Window `j` of the bytes `bs`. -/
theorem winStep_ok {t₀ t : State} {B : Addr} {M k x : Nat → Nat} {Q : Prop} {E bs : Nat → Nat} {j : Nat}
    (hj : j < 2) (hbs : ∀ p < 2, bs p < 256) (hB : t₀.gpr .rbx = B) (hs : Scr t₀ B (2 * D))
    (hR : ∀ p < 2, Nat.Coprime (2 ^ (52 * 20)) (M p)) (h : WinInv t₀ B M k x Q E bs j t) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (VG.Impl.Rsa.X86_64.CrtIfma.window ++ [.block [.alu .sub .r14 (.imm 1)]])) t
      fun t' => WinInv t₀ B M k x Q E bs (j + 1) t' ∧ t'.zf = some (decide (j + 1 = 2)) := by
  have hBt : t.gpr .rbx = B := by
    rw [h.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]; exact hB
  refine wp_seqs_app (by simp [VG.Impl.Rsa.X86_64.CrtIfma.window]) (by simp)
    (WP.mono (window_ok hBt (hs.congr h.wr) hR h.st) fun t₁ ⟨st₁, v₁, f₁, g₁, rd₁, wr₁, x₁⟩ => ?_)
  have r14₁ : t₁.gpr .r14 = BitVec.ofNat 64 (2 - j) := by
    rw [g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact h.r14
  refine WP.mono (r14Dec_ok (n := 2 - j) (by omega) (by omega) r14₁) fun t₂ ⟨r14₂, z₂, k₂, me₂, x₂⟩ =>
    ⟨⟨by rw [r14₂, show 2 - j - 1 = 2 - (j + 1) by omega], ?_, fun hj' p hp => ?_, by rw [me₂]; exact h.frame.trans f₁,
      fun r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 => ?_, by rw [k₂.2.1, rd₁, h.rd], by rw [k₂.2.2, wr₁, h.wr],
      by rw [x₂, x₁, h.mxcsr]⟩, by rw [z₂]; congr 1; exact decide_eq_decide.mpr (by omega)⟩
  · rw [me₂]
    refine ⟨st₁.ar, st₁.tab, st₁.y, fun hq p hp => ?_⟩
    rw [st₁.yv hq p hp, win_exp (hbs p hp) hj _ ?_]
    have hv := h.v hj p hp
    unfold vj at hv
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · rw [nib_hi (hbs p hp) hv]; rfl
    · rw [nib_lo (hbs p hp) hv]; rfl
  · rw [me₂, v₁ p hp, h.v hj p hp]
    rcases (show j = 0 by omega) with rfl
    unfold vj
    simp only [ite_true]
    exact ror60_v _ (hbs p hp)
  · rw [k₂.gpr (by simp [r10]), g₁ r r1 r2 r3 r4 r5 r6 r7 r8 r9 r11]
    exact h.gpr r r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11

end VG.Proof.Bignum.X86_64.AmmSym

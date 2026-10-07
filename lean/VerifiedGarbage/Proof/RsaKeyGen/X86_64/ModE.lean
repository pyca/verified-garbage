import VerifiedGarbage.Proof.RsaKeyGen.X86_64.GcdStep
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.RsaKeyGen.CandMath

/-!
# A candidate on x86-64: `(c − 1) mod e`

`modLoop` copies `c` to `aX`, clears its low bit (`c` is odd), and reduces
`c − 1` modulo the odd `e > 1` bit by bit, from the top (`modLoop_ok`):
`r := (2 r + bit) mod e` (`modbit_bv`), the bits shifted out of the top of
each word in turn.
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- `modBit` and the count. -/
theorem modBody_ok (s : State) (hre : (s.gpr .rsi).toNat < (s.gpr .rbx).toNat) :
    WP isa (.block (modBit ++ ([.alu .sub .r13 (.imm 1)] : List Instr))) s fun t =>
      (t.gpr .rsi).toNat = (2 * (s.gpr .rsi).toNat +
        (decide (2 ^ 64 ≤ (s.gpr .rdx).toNat + (s.gpr .rdx).toNat)).toNat) % (s.gpr .rbx).toNat ∧
      t.gpr .rdx = s.gpr .rdx + s.gpr .rdx ∧
      t.gpr .r13 = s.gpr .r13 - 1 ∧ t.zf = some (s.gpr .r13 - 1 == 0) ∧ t.mem = s.mem ∧
      Keep [.rax, .rcx, .rdx, .rbp, .rsi, .r13] s t := by
  refine WP.mono (WP.keep [.rax, .rcx, .rdx, .rbp, .rsi, .r13] (Q := fun t =>
    (t.gpr .rsi).toNat = (2 * (s.gpr .rsi).toNat +
        (decide (2 ^ 64 ≤ (s.gpr .rdx).toNat + (s.gpr .rdx).toNat)).toNat) % (s.gpr .rbx).toNat ∧
      t.gpr .rdx = s.gpr .rdx + s.gpr .rdx ∧
      t.gpr .r13 = s.gpr .r13 - 1 ∧ t.zf = some (s.gpr .r13 - 1 == 0) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, k⟩
  unfold modBit
  xrun [sx1, List.cons_append, List.nil_append]
  exact modbit_bv _ _ _ hre

/-- The 64 bits of the word `x` in `rdx` into `r = rsi < e` (`rbx`):
`(r 2^64 + x) mod e`. -/
theorem modBits_ok {s : State} (h13 : s.gpr .r13 = BitVec.ofNat 64 64) (hre : (s.gpr .rsi).toNat < (s.gpr .rbx).toNat) :
    WP isa (.loop (.block (modBit ++ ([.alu .sub .r13 (.imm 1)] : List Instr))) .ne) s fun t =>
      (t.gpr .rsi).toNat = ((s.gpr .rsi).toNat * 2 ^ 64 + (s.gpr .rdx).toNat) % (s.gpr .rbx).toNat ∧
      t.mem = s.mem ∧ Keep [.rax, .rcx, .rdx, .rbp, .rsi, .r13] s t := by
  have he0 : 0 < (s.gpr .rbx).toNat := by omega
  have hX := (s.gpr .rdx).isLt
  refine wp_countdown (cnt := .r13) (N := 64) (by decide) (by decide)
    (fun i t => (t.gpr .rsi).toNat = ((s.gpr .rsi).toNat * 2 ^ i + (s.gpr .rdx).toNat / 2 ^ (64 - i)) %
        (s.gpr .rbx).toNat ∧
      (t.gpr .rdx).toNat = ((s.gpr .rdx).toNat % 2 ^ (64 - i)) * 2 ^ i ∧ t.mem = s.mem ∧
      Keep [.rax, .rcx, .rdx, .rbp, .rsi, .r13] s t) ?_ ?_ ⟨?_, ?_, rfl, Keep.refl _ _⟩ h13
  · intro i hi t ⟨hr, hd, hm, k⟩ _
    have hbx : t.gpr .rbx = s.gpr .rbx := k.gpr (by decide)
    refine WP.mono (modBody_ok t (by rw [hbx, hr]; exact Nat.mod_lt _ he0))
      fun t' ⟨h1, h2, h3, h4, h5, k'⟩ => ⟨⟨?_, ?_, h5.trans hm, (k.trans k').mono (by decide)⟩, h3, h4⟩
    · obtain ⟨_, hbit, _, hdiv⟩ := shift_step (s.gpr .rdx).toNat (63 - i) i (by omega)
      rw [show 63 - i + 1 = 64 - i by omega] at hbit hdiv
      rw [h1, hbx, hd, hbit, hr, show 64 - (i + 1) = 63 - i by omega, ← hdiv, Nat.pow_succ]
      have hm2 : ∀ V b E : Nat, (2 * (V % E) + b) % E = (2 * V + b) % E := fun V b E => by
        rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
      rw [hm2]
      congr 1
      have hb2 : (s.gpr .rdx).toNat / 2 ^ (63 - i) % 2 < 2 := Nat.mod_lt _ (by decide)
      generalize (s.gpr .rsi).toNat = R
      generalize (s.gpr .rdx).toNat / 2 ^ (64 - i) = Q
      generalize (s.gpr .rdx).toNat / 2 ^ (63 - i) % 2 = b at hb2 ⊢
      rw [Nat.mul_add, Nat.mul_comm 2 (R * 2 ^ i), Nat.mul_assoc, Nat.mul_comm 2 Q]
      omega
    · obtain ⟨_, _, hsh, _⟩ := shift_step (s.gpr .rdx).toNat (63 - i) i (by omega)
      rw [show 63 - i + 1 = 64 - i by omega] at hsh
      rw [h2, BitVec.toNat_add, hd, hsh, show 64 - (i + 1) = 63 - i by omega]
  · intro t ⟨hr, _, hm, k⟩
    refine ⟨?_, hm, k⟩
    rw [hr, Nat.sub_self, Nat.pow_zero, Nat.div_one]
  · rw [Nat.pow_zero, Nat.mul_one, Nat.div_eq_of_lt hX, Nat.add_zero, Nat.mod_eq_of_lt hre]
  · rw [Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hX]

/-- The words `m` to `w − 1` of the number at `d`. -/
abbrev hiw (mem : Mem) (B : Addr) (d w m : Nat) : Nat := wv mem B (d + 8 * m) (w - m)

theorem hiw_step (mem : Mem) (B : Addr) (d w m : Nat) (hm : m < w) :
    hiw mem B d w m = (word mem B (d + 8 * m)).toNat + 2 ^ 64 * hiw mem B d w (m + 1) := by
  unfold hiw
  rw [show w - m = 1 + (w - (m + 1)) by omega, wv_add, show d + 8 * m + 8 * 1 = d + 8 * (m + 1) by omega]
  simp [wv]

/-- One word of `modLoop`: word `w − 1 − j` into `r = rsi`. -/
theorem modWord_ok {s : State} {B : Addr} {Z d w j : Nat} (hs : Scr s B Z) (h8 : s.gpr .r8 = off B d)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (h14 : s.gpr .r14 = BitVec.ofNat 64 j) (hj : j < w) (hw : w < 2 ^ 31)
    (hd : d + 8 * w ≤ Z) (hre : (s.gpr .rsi).toNat < (s.gpr .rbx).toNat) :
    WP isa modWord s fun t =>
      (t.gpr .rsi).toNat = ((s.gpr .rsi).toNat * 2 ^ 64 + (word s.mem B (d + 8 * (w - 1 - j))).toNat) %
        (s.gpr .rbx).toNat ∧ t.mem = s.mem ∧ Keep [.rax, .rcx, .rdx, .rbp, .rsi, .r13] s t := by
  have hn := hs.nowrap
  unfold modWord
  refine WP.seq (WP.mono (WP.keep [.rax, .rdx, .r13] (Q := fun t =>
      t.gpr .rdx = word s.mem B (d + 8 * (w - 1 - j)) ∧ t.gpr .r13 = BitVec.ofNat 64 64 ∧ t.mem = s.mem) ?_ rfl)
    fun t₁ ⟨⟨hdx, h13, hm⟩, k₁⟩ => ?_)
  · have hix : s.gpr .r12 - 1 - s.gpr .r14 = BitVec.ofNat 64 (w - 1 - j) := by
      rw [h12, h14]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      have : (1 : BitVec 64).toNat = 1 := rfl
      rw [this]; omega
    xrun [State.ea, ix, addr0 h8 hix, hs.ld (show d + 8 * (w - 1 - j) + 8 ≤ Z by omega), sx_ofNat]
  · refine WP.mono (modBits_ok h13 (by
      rw [show t₁.gpr .rsi = s.gpr .rsi from k₁.gpr (by decide),
        show t₁.gpr .rbx = s.gpr .rbx from k₁.gpr (by decide)]; exact hre))
      fun t ⟨h1, hm', k⟩ => ⟨?_, hm'.trans hm, (k₁.trans k).mono (by decide)⟩
    rw [h1, show t₁.gpr .rsi = s.gpr .rsi from k₁.gpr (by decide),
      show t₁.gpr .rbx = s.gpr .rbx from k₁.gpr (by decide), hdx]

/-- After `j` words of `modLoop`. -/
structure ModInv (s₀ : State) (B : Addr) (d w : Nat) (j : Nat) (t : State) : Prop where
  val : (t.gpr .rsi).toNat = hiw s₀.mem B d w (w - j) % (s₀.gpr .rbx).toNat
  mem : t.mem = s₀.mem
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  keep : Keep [.rax, .rcx, .rdx, .rbp, .rsi, .r13, .r14] s₀ t

/-- The words of the number at `d`, from the top, into `r = rsi = 0` modulo
the `e > 1` in `rbx`. -/
theorem modWords_ok {s : State} {B : Addr} {Z d w : Nat} (hs : Scr s B Z) (h8 : s.gpr .r8 = off B d)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (h14 : s.gpr .r14 = BitVec.ofNat 64 0) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hd : d + 8 * w ≤ Z) (hsi : s.gpr .rsi = 0) (he : 1 < (s.gpr .rbx).toNat) :
    WP isa (.loop (.seq modWord (.block [.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)])) .ne) s fun t =>
      (t.gpr .rsi).toNat = wv s.mem B d w % (s.gpr .rbx).toNat ∧ t.mem = s.mem ∧
      Keep [.rax, .rcx, .rdx, .rbp, .rsi, .r13, .r14] s t := by
  refine wp_upto (a := 0) (N := w) (by omega) (ModInv s B d w) ?_ (fun t hI => ⟨?_, hI.mem, hI.keep⟩)
    ⟨by rw [hsi, Nat.sub_zero]; unfold hiw; rw [Nat.sub_self]; simp [wv], rfl, h14, Keep.refl _ _⟩
  · intro j _ hj t hI
    have tbx : t.gpr .rbx = s.gpr .rbx := hI.keep.gpr (by decide)
    refine WP.seq (WP.mono (modWord_ok (hs.congr hI.keep.2.2) ((hI.keep.gpr (by decide)).trans h8)
      ((hI.keep.gpr (by decide)).trans h12) hI.r14 hj hw' hd (by rw [hI.val, tbx]; exact Nat.mod_lt _ (by omega)))
      fun t₁ ⟨h1, hm₁, k₁⟩ => ?_)
    refine WP.mono (count_ok t₁ ((k₁.gpr (by decide)).trans hI.r14)
      ((k₁.gpr (by decide)).trans ((hI.keep.gpr (by decide)).trans h12)) (by omega) (by omega))
      fun t' ⟨hz, h14', hm', k'⟩ => ⟨hz, ⟨?_, by rw [hm', hm₁, hI.mem], h14', ((hI.keep.trans k₁).trans k').mono (by decide)⟩⟩
    rw [k'.gpr (by decide), h1, tbx, hI.val, hI.mem, hiw_step s.mem B d w (w - (j + 1)) (by omega),
      show w - (j + 1) + 1 = w - j by omega, show w - 1 - j = w - (j + 1) by omega]
    have hm2 : ∀ V x E : Nat, ((V % E) * 2 ^ 64 + x) % E = (x + 2 ^ 64 * V) % E := fun V x E => by
      rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod, Nat.add_comm, Nat.mul_comm]
    exact hm2 _ _ _
  · rw [hI.val, Nat.sub_self]; unfold hiw; simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero]

end VG.Proof.RsaKeyGen.X86_64

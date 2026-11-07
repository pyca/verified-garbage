module

public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Sieve
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.TrialLoop
public import VerifiedGarbage.Spec.Ffdh
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Sieve
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.RsaKeyGen.TrialMath
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Trial
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
public import Mathlib.Data.Nat.Find

/-! # FFDH parameter candidates on x86-64: RSA's trial division, with its proven reductions -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Proof.RsaKeyGen.X86_64
open VG.Proof.MlKem.X86_64 VG.Proof.RsaKeyGen

/-- The table's words the sieve divides by, for the requested width `bits`:
256 above 1024 bits, else 128. -/
def sieveCount (bits : Nat) : Nat := if 1025 ≤ bits then 256 else 128

/-! ## Stopping at the first divisor -/

theorem anyPre_mono {c m n : Nat} (h : m ≤ n) (ha : anyPre c m = true) : anyPre c n = true := by
  unfold anyPre at *
  obtain ⟨i, hi, hd⟩ := List.any_eq_true.mp ha
  exact List.any_eq_true.mpr ⟨i, List.mem_range.mpr (Nat.lt_of_lt_of_le (List.mem_range.mp hi) h), hd⟩


/-- The number of the table's words the sieve divides by before it stops:
the first `k ≥ 1` whose words hold a divisor of `c`, or all `N`. -/
noncomputable def firstHit (c N : Nat) : Nat :=
  Nat.find (p := fun k => N ≤ k ∨ (0 < k ∧ anyPre c (4 * k) = true)) ⟨N, Or.inl (Nat.le_refl _)⟩

theorem firstHit_le (c N : Nat) : firstHit c N ≤ N := by
  unfold firstHit; exact Nat.find_min' _ (Or.inl (Nat.le_refl _))

private theorem firstHit_spec (c N : Nat) :
    N ≤ firstHit c N ∨ (0 < firstHit c N ∧ anyPre c (4 * firstHit c N) = true) := by
  unfold firstHit; exact Nat.find_spec (p := fun k => N ≤ k ∨ (0 < k ∧ anyPre c (4 * k) = true)) _

private theorem firstHit_min {c N k : Nat} (h : k < firstHit c N) :
    ¬ (N ≤ k ∨ (0 < k ∧ anyPre c (4 * k) = true)) := by
  unfold firstHit at h; exact Nat.find_min (p := fun k => N ≤ k ∨ (0 < k ∧ anyPre c (4 * k) = true)) _ h

theorem firstHit_pos {c N : Nat} (hN : 1 ≤ N) : 1 ≤ firstHit c N := by
  by_contra h
  have h0 : firstHit c N = 0 := by omega
  have := firstHit_spec c N
  rw [h0] at this
  omega

/-- The exit test after word `j` of the sieve: done, or a divisor so far. -/
theorem firstHit_exit {c N j : Nat} (hj : j < firstHit c N) :
    (decide (j + 1 = N) || anyPre c (4 * (j + 1))) = decide (j + 1 = firstHit c N) := by
  have hle := firstHit_le c N
  by_cases he : j + 1 = firstHit c N
  · rw [he, show decide (firstHit c N = firstHit c N) = true from decide_eq_true rfl]
    rcases firstHit_spec c N with h | ⟨-, h⟩
    · have : firstHit c N = N := by omega
      simp [this]
    · rw [h, Bool.or_true]
  · have hlt : j + 1 < firstHit c N := by omega
    have hn := firstHit_min hlt
    simp only [not_or, not_le, not_and, Bool.not_eq_true] at hn
    have h1 : ¬ j + 1 = N := by omega
    simp [he, h1, hn.2 (by omega)]

/-- Stopping early decides as the whole table does. -/
theorem firstHit_any (c N : Nat) : anyPre c (4 * firstHit c N) = anyPre c (4 * N) := by
  rcases firstHit_spec c N with h | ⟨-, h⟩
  · rw [show firstHit c N = N by have := firstHit_le c N; omega]
  · rw [h, anyPre_mono (Nat.mul_le_mul_left 4 (firstHit_le c N)) h]

private theorem exit_bv {N k : Nat} (hk : k + 1 ≤ N) (hN : N < 2 ^ 64) (b : Bool) :
    ((BitVec.ofNat 64 N - BitVec.ofNat 64 (k + 1)) &&&
      (mask b ^^^ BitVec.signExtend 64 (BitVec.ofInt 32 (-1))) == 0) = (decide (k + 1 = N) || b) := by
  have hm : BitVec.signExtend 64 (BitVec.ofInt 32 (-1)) = BitVec.allOnes 64 := by decide
  have m0 : mask false = 0#64 := by decide
  have m1 : mask true = BitVec.allOnes 64 := by decide
  rw [hm]
  cases b
  · rw [m0, BitVec.zero_xor, BitVec.and_allOnes, Bool.or_false, sub_beq_zero]
    by_cases h : k + 1 = N
    · simp [h]
    · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro he; apply h
      have := congrArg BitVec.toNat he
      simp only [BitVec.toNat_ofNat] at this
      omega
  · rw [m1, BitVec.xor_self, BitVec.and_zero, Bool.or_true]
    rfl

/-! ## A table word's product

The candidate is reduced once modulo the product `M` of the table word's
four primes (`productReduce`, Montgomery reduction by `2^64` word by word:
`acc 2^(64 w) ≡ c (mod M)`), and each prime's test is RSA's on `acc`
(`accEntry`). -/

/-- Montgomery reduction by `2^64` modulo the odd `M`, with `mv = −M⁻¹ mod
2^64`, of `acc + x`: below `M + 2`, and `(acc + x) 2^(−64) mod M`. -/
theorem redc64_math {M mv acc x : Nat} (hinv : (M * mv + 1) % 2 ^ 64 = 0)
    (hacc : acc < M + 2) (hx : x < 2 ^ 64) :
    ((acc + x) / 2 ^ 64 + (acc + x) % 2 ^ 64 * mv % 2 ^ 64 * M / 2 ^ 64 +
        ((acc + x) % 2 ^ 64 * mv % 2 ^ 64 * M % 2 ^ 64 + (acc + x) % 2 ^ 64) / 2 ^ 64) < M + 2 ∧
    ((acc + x) / 2 ^ 64 + (acc + x) % 2 ^ 64 * mv % 2 ^ 64 * M / 2 ^ 64 +
        ((acc + x) % 2 ^ 64 * mv % 2 ^ 64 * M % 2 ^ 64 + (acc + x) % 2 ^ 64) / 2 ^ 64) * 2 ^ 64 % M =
      (acc + x) % M := by
  generalize hX : acc + x = X
  have hXb : X < M + 2 + 2 ^ 64 := by omega
  generalize hlo : X % 2 ^ 64 = lo
  have hlo' : lo < 2 ^ 64 := hlo ▸ Nat.mod_lt _ (by decide)
  generalize hq : lo * mv % 2 ^ 64 = q
  have hq' : q < 2 ^ 64 := hq ▸ Nat.mod_lt _ (by decide)
  -- q M + lo ≡ 0 (mod 2^64)
  have hz : (q * M + lo) % 2 ^ 64 = 0 := by
    rw [← hq, Nat.add_mod, Nat.mod_mul_mod, Nat.mul_assoc, Nat.mul_comm mv M, ← Nat.add_mod]
    have : lo * (M * mv) + lo = lo * (M * mv + 1) := by rw [Nat.mul_add, Nat.mul_one]
    rw [this, Nat.mul_mod, hinv, Nat.mul_zero, Nat.zero_mod]
  have e1 := Nat.div_add_mod X (2 ^ 64)
  have e2 := Nat.div_add_mod (q * M) (2 ^ 64)
  have e3 := Nat.div_add_mod (q * M % 2 ^ 64 + lo) (2 ^ 64)
  have hz' : (q * M % 2 ^ 64 + lo) % 2 ^ 64 = 0 := by rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]; exact hz
  rw [hz', Nat.add_zero] at e3
  rw [hlo] at e1
  have hexact : (X / 2 ^ 64 + q * M / 2 ^ 64 + (q * M % 2 ^ 64 + lo) / 2 ^ 64) * 2 ^ 64 = X + q * M := by
    rw [Nat.add_mul, Nat.add_mul, Nat.mul_comm (X / 2 ^ 64), Nat.mul_comm (q * M / 2 ^ 64),
      Nat.mul_comm ((q * M % 2 ^ 64 + lo) / 2 ^ 64), e3]
    omega
  refine ⟨?_, ?_⟩
  · have hqM : q * M ≤ (2 ^ 64 - 1) * M := Nat.mul_le_mul_right _ (by omega)
    have : (X / 2 ^ 64 + q * M / 2 ^ 64 + (q * M % 2 ^ 64 + lo) / 2 ^ 64) * 2 ^ 64 < (M + 2) * 2 ^ 64 := by
      rw [hexact]
      have : (2 ^ 64 - 1) * M + M = 2 ^ 64 * M := by
        rw [Nat.sub_mul, Nat.one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ (by decide))]
      omega
    exact Nat.lt_of_mul_lt_mul_right this
  · rw [hexact, Nat.add_mul_mod_self_right]


/-- The carry of a sum below `2^65`. -/
theorem carry_bit {X : Nat} (h : X < 2 ^ 65) :
    (BitVec.setWidth 64 (BitVec.ofBool (decide (2 ^ 64 ≤ X)))).toNat = X / 2 ^ 64 := by
  by_cases hx : 2 ^ 64 ≤ X
  · simp [hx]; omega
  · simp [hx]; omega

/-- `redc64`'s result, from the machine's operations. -/
theorem redc_bits (a b m Mv : BitVec 64) (hM : Mv.toNat < 2 ^ 62) :
    (BitVec.ofNat 64 (((a + b) * m).toNat * Mv.toNat / 2 ^ 64) + BitVec.signExtend 64 (0 : BitVec 32) +
        BitVec.setWidth 64 (BitVec.ofBool (decide (2 ^ 64 ≤
          (BitVec.ofNat 64 (((a + b) * m).toNat * Mv.toNat)).toNat + (a + b).toNat))) -
      (0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (2 ^ 64 ≤ a.toNat + b.toNat))))).toNat =
    (b.toNat + a.toNat) / 2 ^ 64 + (b.toNat + a.toNat) % 2 ^ 64 * m.toNat % 2 ^ 64 * Mv.toNat / 2 ^ 64 +
      ((b.toNat + a.toNat) % 2 ^ 64 * m.toNat % 2 ^ 64 * Mv.toNat % 2 ^ 64 + (b.toNat + a.toNat) % 2 ^ 64) / 2 ^ 64 := by
  rw [show BitVec.signExtend 64 (0 : BitVec 32) = 0#64 from rfl, BitVec.add_zero, BitVec.zero_sub, BitVec.sub_neg]
  have ha := a.isLt
  have hb := b.isLt
  have hab : (a + b).toNat = (b.toNat + a.toNat) % 2 ^ 64 := by rw [BitVec.toNat_add, Nat.add_comm]
  have hq : ((a + b) * m).toNat = (b.toNat + a.toNat) % 2 ^ 64 * m.toNat % 2 ^ 64 := by
    rw [BitVec.toNat_mul, hab]
  rw [hab, hq, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_comm a.toNat b.toNat]
  have hlo : (b.toNat + a.toNat) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
  have hq2 : (b.toNat + a.toNat) % 2 ^ 64 * m.toNat % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
  generalize (b.toNat + a.toNat) % 2 ^ 64 * m.toNat % 2 ^ 64 = q at hq2 ⊢
  have hP : q * Mv.toNat / 2 ^ 64 < 2 ^ 62 := by
    apply Nat.div_lt_of_lt_mul
    calc q * Mv.toNat < 2 ^ 64 * 2 ^ 62 := Nat.mul_lt_mul_of_lt_of_le hq2 (Nat.le_of_lt hM) (by decide)
      _ = 2 ^ 62 * 2 ^ 64 := Nat.mul_comm _ _
  have hPm : q * Mv.toNat % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
  rw [BitVec.toNat_ofNat, carry_bit (by omega), carry_bit (by omega)]
  generalize (b.toNat + a.toNat) % 2 ^ 64 = lo at hlo ⊢
  generalize q * Mv.toNat / 2 ^ 64 = H at hP ⊢
  generalize q * Mv.toNat % 2 ^ 64 = L at hPm ⊢
  have h1 : (b.toNat + a.toNat) / 2 ^ 64 ≤ 1 := by omega
  have h2 : (L + lo) / 2 ^ 64 ≤ 1 := by omega
  rw [Nat.mod_eq_of_lt (b := 2 ^ 64) (by omega : H < 2 ^ 64), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem sieve_imul (a b : BitVec 64) : BitVec.ofInt 64 (a.toInt * b.toInt) = a * b := by
  simp only [BitVec.ofInt_mul, BitVec.ofInt_toInt]

/-- The value `redc64` leaves in `rbp`. -/
def redcVal (acc x mv M : Nat) : Nat :=
  (acc + x) / 2 ^ 64 + (acc + x) % 2 ^ 64 * mv % 2 ^ 64 * M / 2 ^ 64 +
    ((acc + x) % 2 ^ 64 * mv % 2 ^ 64 * M % 2 ^ 64 + (acc + x) % 2 ^ 64) / 2 ^ 64

theorem redc64_ok {t : State} {B : Addr} {Z d : Nat} (hs : Scr t B Z) (h8 : t.gpr .r8 = off B d) {j : Nat}
    (h14 : t.gpr .r14 = BitVec.ofNat 64 j) (hd : d + 8 * j + 8 ≤ Z) (hM : (t.gpr .rbx).toNat < 2 ^ 62) :
    WP isa (.block redc64) t fun t' =>
      (t'.gpr .rbp).toNat = redcVal (t.gpr .rbp).toNat (word t.mem B (d + 8 * j)).toNat (t.gpr .r15).toNat
        (t.gpr .rbx).toNat ∧ t'.mem = t.mem ∧ Keep [.rsi, .rcx, .rax, .rdx, .rbp] t t' := by
  have hn := hs.nowrap
  have hld : InRegions (t.rd ++ t.wr) (off B (d + 8 * j)) 8 := hs.ld (by omega_arith)
  refine WP.mono (WP.keep [.rsi, .rcx, .rax, .rdx, .rbp] (Q := fun t' =>
      (t'.gpr .rbp).toNat = redcVal (t.gpr .rbp).toNat (word t.mem B (d + 8 * j)).toNat (t.gpr .r15).toNat
        (t.gpr .rbx).toNat ∧ t'.mem = t.mem) ?_ rfl) fun t' ⟨⟨h, hm⟩, k⟩ => ⟨h, hm, k⟩
  unfold redc64 redcVal
  xrun [State.ea, ix, addr0 h8 h14, hld, execImul, sieve_imul]
  exact redc_bits _ _ _ _ hM


/-- Another word reduced: `acc 2^(64 j) ≡ c_j` carries on to `j + 1` words. -/
theorem prod_word_math {M acc r x V j : Nat} (h : r * 2 ^ 64 % M = (acc + x) % M)
    (hV : acc * 2 ^ (64 * j) % M = V % M) :
    r * 2 ^ (64 * (j + 1)) % M = (V + 2 ^ (64 * j) * x) % M := by
  calc r * 2 ^ (64 * (j + 1)) % M = r * 2 ^ 64 % M * (2 ^ (64 * j) % M) % M := by
        rw [pow64_succ, Nat.mul_comm (2 ^ (64 * j)) (2 ^ 64), ← Nat.mul_assoc, Nat.mul_mod]
    _ = (acc * 2 ^ (64 * j) + x * 2 ^ (64 * j)) % M := by rw [h, ← Nat.mul_mod, Nat.add_mul]
    _ = (acc * 2 ^ (64 * j) % M + x * 2 ^ (64 * j)) % M := (Nat.mod_add_mod _ _ _).symm
    _ = (V + 2 ^ (64 * j) * x) % M := by rw [hV, Nat.mod_add_mod, Nat.mul_comm x]

/-- After `j` words of the candidate's reduction modulo `M`. -/
structure PInv (s₀ : State) (B : Addr) (d M : Nat) (j : Nat) (t : State) : Prop where
  acc : (t.gpr .rbp).toNat < M + 2
  val : (t.gpr .rbp).toNat * 2 ^ (64 * j) % M = wv s₀.mem B d j % M
  mem : t.mem = s₀.mem
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  keep : Keep [.rax, .rcx, .rdx, .rbp, .rsi, .r14] s₀ t

theorem prStep_ok {s₀ : State} {B : Addr} {Z d w M : Nat} (hs : Scr s₀ B Z) (h8 : s₀.gpr .r8 = off B d)
    (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w) (hbx : (s₀.gpr .rbx).toNat = M)
    (h15 : (M * (s₀.gpr .r15).toNat + 1) % 2 ^ 64 = 0) (hM : M < 2 ^ 62)
    (hw : w < 2 ^ 31) (hd : d + 8 * w ≤ Z) {j : Nat} (hj : j < w) {t : State} (hI : PInv s₀ B d M j t) :
    WP isa (.block (redc64 ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ PInv s₀ B d M (j + 1) t' := by
  have t8 : t.gpr .r8 = off B d := (hI.keep.gpr (by decide)).trans h8
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have tbx : (t.gpr .rbx).toNat = M := by rw [hI.keep.gpr (by decide)]; exact hbx
  have t15 : (M * (t.gpr .r15).toNat + 1) % 2 ^ 64 = 0 := by rw [hI.keep.gpr (by decide)]; exact h15
  have hst : Scr t B Z := hs.congr hI.keep.2.2
  rw [WP.block_append_iff]
  refine WP.mono (redc64_ok hst t8 hI.r14 (by omega_arith) (by rw [tbx]; exact hM)) fun t₁ ⟨hbp, hm₁, k₁⟩ => ?_
  rw [tbx, hI.mem] at hbp
  obtain ⟨hlt, hmod⟩ := redc64_math (acc := (t.gpr .rbp).toNat) (x := (word s₀.mem B (d + 8 * j)).toNat) t15 hI.acc
    (word s₀.mem B (d + 8 * j)).isLt
  refine WP.mono (count_ok t₁ ((k₁.gpr (by decide)).trans hI.r14) ((k₁.gpr (by decide)).trans t12) (by omega_arith) (by omega_arith))
    fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ⟨?_, ?_, by rw [hm', hm₁, hI.mem], h14, ((hI.keep.trans k₁).trans k').mono (by decide)⟩⟩
  · rw [k'.gpr (by decide), hbp]; exact hlt
  · rw [k'.gpr (by decide), hbp, wv]
    exact prod_word_math hmod hI.val

/-- The product of entries `4 i` to `4 i + 3` of the table. -/
def wordProd (i : Nat) : Nat := tabEntry (4 * i) * tabEntry (4 * i + 1) * tabEntry (4 * i + 2) * tabEntry (4 * i + 3)

/-- The four entries of the table word in `kT1` multiplied into `rbx`. -/
theorem prodBlock_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good t B Z w minv) (hZ : slot w 8 ≤ Z)
    {i : Nat} (hi : i < 256) (hT : word t.mem B (8 * kT1) = BitVec.ofNat 64 (tabWord i)) :
    WP isa (.block (([.mov .rax (.mem (hdr kT1)), .mov .rbx (.reg .rax), .alu .and .rbx (.imm 0xFFFF)] : List Instr) ++
      productField 1 ++ productField 2 ++ productField 3)) t fun t' =>
      (t'.gpr .rbx).toNat = wordProd i ∧ t'.mem = t.mem ∧ Keep [.rax, .rbx, .rcx] t t' := by
  have hn := hg.scr.nowrap
  have hl : InRegions (t.rd ++ t.wr) (off B (8 * kT1)) 8 := hg.scr.ld (by have := hdr_lt_slot w 8 (show kT1 < 32 by decide); omega_arith)
  refine WP.mono (WP.keep [.rax, .rbx, .rcx] (Q := fun t' => (t'.gpr .rbx).toNat = wordProd i ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨⟨h1, h2⟩, k⟩ => ⟨h1, h2, k⟩
  unfold productField
  simp only [List.cons_append, List.nil_append, Nat.reduceMul]
  xrun [State.ea, hdr, hg.rdi, hdrOff, hl, hT, sxFFFF, execImul, sieve_imul]
  have e0 := tabWord_entry hi (show 0 < 4 by decide)
  have e1 := tabWord_entry hi (show 1 < 4 by decide)
  have e2 := tabWord_entry hi (show 2 < 4 by decide)
  have e3 := tabWord_entry hi (show 3 < 4 by decide)
  rw [Nat.mul_zero, BitVec.ushiftRight_zero, Nat.add_zero] at e0
  simp only [Nat.reduceMul] at e1 e2 e3
  have b0 := (tabEntry_facts (i := 4 * i) (by omega)).2.2
  have b1 := (tabEntry_facts (i := 4 * i + 1) (by omega)).2.2
  have b2 := (tabEntry_facts (i := 4 * i + 2) (by omega)).2.2
  have b3 := (tabEntry_facts (i := 4 * i + 3) (by omega)).2.2
  rw [BitVec.toNat_mul, BitVec.toNat_mul, BitVec.toNat_mul, e0, e1, e2, e3]
  unfold wordProd
  have h01 : tabEntry (4 * i) * tabEntry (4 * i + 1) < 2 ^ 26 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le b0 (Nat.le_of_lt b1) (by omega)) (by decide)
  have h012 : tabEntry (4 * i) * tabEntry (4 * i + 1) * tabEntry (4 * i + 2) < 2 ^ 39 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le h01 (Nat.le_of_lt b2) (by omega)) (by decide)
  have h0123 : tabEntry (4 * i) * tabEntry (4 * i + 1) * tabEntry (4 * i + 2) * tabEntry (4 * i + 3) < 2 ^ 52 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le h012 (Nat.le_of_lt b3) (by omega)) (by decide)
  rw [Nat.mod_eq_of_lt (by omega : tabEntry (4 * i) * tabEntry (4 * i + 1) < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : tabEntry (4 * i) * tabEntry (4 * i + 1) * tabEntry (4 * i + 2) < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : tabEntry (4 * i) * tabEntry (4 * i + 1) * tabEntry (4 * i + 2) * tabEntry (4 * i + 3) < 2 ^ 64)]

theorem wordProd_facts {i : Nat} (hi : i < 256) : wordProd i % 2 = 1 ∧ wordProd i < 2 ^ 52 := by
  have b0 := tabEntry_facts (i := 4 * i) (by omega)
  have b1 := tabEntry_facts (i := 4 * i + 1) (by omega)
  have b2 := tabEntry_facts (i := 4 * i + 2) (by omega)
  have b3 := tabEntry_facts (i := 4 * i + 3) (by omega)
  unfold wordProd
  refine ⟨by rw [Nat.mul_mod, Nat.mul_mod (_ * _), Nat.mul_mod (tabEntry (4 * i)), b0.1, b1.1, b2.1, b3.1], ?_⟩
  have h01 : tabEntry (4 * i) * tabEntry (4 * i + 1) < 2 ^ 26 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le b0.2.2 (Nat.le_of_lt b1.2.2) (by omega)) (by decide)
  have h012 : tabEntry (4 * i) * tabEntry (4 * i + 1) * tabEntry (4 * i + 2) < 2 ^ 39 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le h01 (Nat.le_of_lt b2.2.2) (by omega)) (by decide)
  exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le h012 (Nat.le_of_lt b3.2.2) (by omega)) (by decide)

theorem dvd_wordProd {i j : Nat} (hj : j < 4) : tabEntry (4 * i + j) ∣ wordProd i := by
  unfold wordProd
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
  · exact Nat.dvd_mul_right_of_dvd (Nat.dvd_mul_right_of_dvd (Nat.dvd_mul_right _ _) _) _
  · exact Nat.dvd_mul_right_of_dvd (Nat.dvd_mul_right_of_dvd (Nat.dvd_mul_left _ _) _) _
  · exact Nat.dvd_mul_right_of_dvd (Nat.dvd_mul_left _ _) _
  · exact Nat.dvd_mul_left _ _

/-- `productHead`: the table word's product `M` in `rbx`, `−M⁻¹` in `r15`, and
the reduction's start. -/
theorem productHead_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good t B Z w minv)
    (hZ : slot w 8 ≤ Z) {i : Nat} (hi : i < 256) (hT : word t.mem B (8 * kT1) = BitVec.ofNat 64 (tabWord i)) :
    WP isa (.block productHead) t fun t' =>
      (t'.gpr .rbx).toNat = wordProd i ∧ (wordProd i * (t'.gpr .r15).toNat + 1) % 2 ^ 64 = 0 ∧
      t'.gpr .r12 = BitVec.ofNat 64 w ∧ t'.gpr .r8 = off B (slot w aN) ∧ t'.gpr .rbp = 0 ∧
      t'.mem = t.mem ∧ Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r12, .r15] t t' := by
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega_arith)
  unfold productHead
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (prodBlock_ok hg hZ hi hT) fun t₁ ⟨hbx₁, hm₁, k₁⟩ => ?_
  refine WP.mono (minv_ok t₁ (by rw [hbx₁]; exact (wordProd_facts hi).1)) fun t₂ ⟨h15, k₂, hm₂⟩ => ?_
  rw [hbx₁] at h15
  have hdi₂ : t₂.gpr .rdi = B := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hg.rdi)
  have hl₂ : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off B (8 * i)) 8 := fun i hi => by
    rw [k₂.2.1, k₂.2.2, k₁.2.1, k₁.2.2]; exact hl i hi
  have hm12 : t₂.mem = t.mem := hm₂.trans hm₁
  refine WP.mono (WP.keep [.r12, .r8, .rbp] (Q := fun t' => t'.gpr .r12 = BitVec.ofNat 64 w ∧
      t'.gpr .r8 = off B (slot w aN) ∧ t'.gpr .rbp = 0 ∧ t'.mem = t₂.mem) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, hl₂ sW (by decide), hl₂ (sArr aN) (by decide), hm12, hg.hdr.hw,
      hg.hdr.harr aN (by decide)]) rfl) fun t' ⟨⟨h12, h8, hbp, hm'⟩, k'⟩ => ?_
  refine ⟨?_, by rw [k'.gpr (by decide)]; exact h15, h12, h8, hbp, by rw [hm', hm12], ((k₁.trans k₂).trans k').mono (by decide)⟩
  rw [k'.gpr (by decide), k₂.gpr (by decide)]; exact hbx₁

/-- The candidate reduced modulo the table word's product, into `r8`. -/
theorem productReduce_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good t B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) {i : Nat} (hi : i < 256)
    (hT : word t.mem B (8 * kT1) = BitVec.ofNat 64 (tabWord i)) :
    WP isa (seqs productReduce) t fun t' =>
      (t'.gpr .r8).toNat < wordProd i + 2 ∧
      (t'.gpr .r8).toNat * 2 ^ (64 * w) % wordProd i = wv t.mem B (slot w aN) w % wordProd i ∧
      t'.mem = t.mem ∧ Good t' B Z w minv ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r12, .r14, .r15] t t' := by
  have sN := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have hP := wordProd_facts hi
  unfold productReduce
  simp only [seqs]
  refine WP.seq (WP.mono (productHead_ok hg hZ hi hT) fun t₁ ⟨hbx, h15, h12, h8, hbp, hm₁, k₁⟩ => ?_)
  have hs₁ := hg.scr.congr k₁.2.2
  refine WP.seq (WP.mono (wordLoop_ok (start := 0) (N := w) (by omega_arith) hw' (PInv t₁ B (slot w aN) (wordProd i))
    (fun t h14 hm k _ => ⟨by rw [k.gpr (by decide), hbp]; show 0 < wordProd i + 2; omega_arith,
      by rw [k.gpr (by decide), hbp]; simp [wv], hm, h14, k.mono (by decide)⟩)
    (fun j' _ hj' t hI => prStep_ok hs₁ h8 h12 hbx h15 (by omega_arith) hw' (by omega_arith) hj' hI)) fun t₂ hI => ?_)
  refine WP.mono (WP.keep [.r8] (Q := fun t' => t'.gpr .r8 = t₂.gpr .rbp ∧ t'.mem = t₂.mem) (by xrun) rfl)
    fun t' ⟨⟨h8', hm'⟩, k'⟩ => ?_
  have kk := (k₁.trans hI.keep).trans k'
  have hm : t'.mem = t.mem := by rw [hm', hI.mem, hm₁]
  refine ⟨by rw [h8']; exact hI.acc, by rw [h8', ← hm₁]; exact hI.val, hm,
    ⟨hg.scr.congr kk.2.2, (kk.gpr (by decide)).trans hg.rdi, by rw [hm]; exact hg.hdr⟩, kk.mono (by decide)⟩

/-- The reduced candidate: `acc 2^(64 (w + 1)) ≡ c (mod s)` from
`acc 2^(64 w) ≡ c (mod M)`, `s ∣ M` and `r 2^64 ≡ acc (mod s)`. -/
theorem acc_entry_math {s M acc r c w : Nat} (hd : s ∣ M) (hval : acc * 2 ^ (64 * w) % M = c % M)
    (hr : r * 2 ^ 64 % s = acc % s) : r * 2 ^ (64 * (w + 1)) % s = c % s := by
  have hv : acc * 2 ^ (64 * w) % s = c % s := by
    rw [← Nat.mod_mod_of_dvd _ hd, hval, Nat.mod_mod_of_dvd _ hd]
  rw [pow64_succ, Nat.mul_comm (2 ^ (64 * w)) (2 ^ 64), ← Nat.mul_assoc, Nat.mul_mod, hr, ← Nat.mul_mod, hv]

/-- `accEntry j`: the mask of `s ∣ c`, for entry `j` of the table word in
`kT1` and the candidate reduced modulo the word's product in `r8`, or'ed
into `kT2`. -/
theorem accEntry_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) {i j : Nat} (hi : i < 256) (hj : j < 4)
    (hT : word s.mem B (8 * kT1) = BitVec.ofNat 64 (tabWord i)) {c : Nat}
    (hacc : (s.gpr .r8).toNat < 2 ^ 54)
    (hval : (s.gpr .r8).toNat * 2 ^ (64 * w) % wordProd i = c % wordProd i) :
    WP isa (.block (accEntry j)) s fun t =>
      word t.mem B (8 * kT2) = mask (decide (c % tabEntry (4 * i + j) = 0)) ||| word s.mem B (8 * kT2) ∧
      Good t B Z w minv ∧ Outside B (8 * kT2) 8 s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r15] s t := by
  have hn := hg.scr.nowrap
  obtain ⟨hodd, hs3, hs13⟩ := tabEntry_facts (i := 4 * i + j) (by omega_arith)
  have hdv := dvd_wordProd (i := i) hj
  generalize hsp : tabEntry (4 * i + j) = sp at hodd hs3 hs13 hdv ⊢
  generalize hA : (s.gpr .r8).toNat = acc at hacc hval
  unfold accEntry
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff]
  refine WP.mono (entryLoad_ok hg hZ hi hj hT) fun s₁ ⟨hbx₁, hm₁, k₁⟩ => ?_
  rw [hsp] at hbx₁
  refine WP.mono (minv_ok s₁ (by rw [hbx₁]; exact hodd)) fun s₂ ⟨h15, k₂, hm₂⟩ => ?_
  rw [hbx₁] at h15
  have h8₂ : (s₂.gpr .r8).toNat = acc := by rw [k₂.gpr (by decide), k₁.gpr (by decide)]; exact hA
  refine WP.mono (WP.keep [.rbp, .rax] (Q := fun t => t.gpr .rbp = 0 ∧ (t.gpr .rax).toNat = acc % 2 ^ 32 ∧
      t.mem = s₂.mem) (by
    xrun
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, h8₂,
      Nat.mod_eq_of_lt (b := 2 ^ 64) (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide))]) rfl)
    fun s₃ ⟨⟨hbp₃, hax₃, hm₃⟩, k₃⟩ => ?_
  have hbx₃ : (s₃.gpr .rbx).toNat = sp := by rw [k₃.gpr (by decide), k₂.gpr (by decide)]; exact hbx₁
  have h15₃ : (sp * (s₃.gpr .r15).toNat + 1) % 2 ^ 64 = 0 := by rw [k₃.gpr (by decide)]; exact h15
  refine WP.mono (redc32_ok (s := sp) (by rw [hax₃]; exact Nat.mod_lt _ (by decide))
    (by rw [hbp₃]; show 0 < 2 * sp; omega_arith) hbx₃ h15₃ hs3 (by omega_arith)) fun s₄ ⟨hacc₄, hval₄, hm₄, k₄⟩ => ?_
  have h8₄ : (s₄.gpr .r8).toNat = acc := by rw [k₄.gpr (by decide), k₃.gpr (by decide)]; exact h8₂
  refine WP.mono (WP.keep [.rax] (Q := fun t => (t.gpr .rax).toNat = acc / 2 ^ 32 ∧ t.mem = s₄.mem) (by
    xrun
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, h8₄]) rfl) fun s₅ ⟨⟨hax₅, hm₅⟩, k₅⟩ => ?_
  have hbx₅ : (s₅.gpr .rbx).toNat = sp := by rw [k₅.gpr (by decide), k₄.gpr (by decide)]; exact hbx₃
  have h15₅ : (sp * (s₅.gpr .r15).toNat + 1) % 2 ^ 64 = 0 := by rw [k₅.gpr (by decide), k₄.gpr (by decide)]; exact h15₃
  refine WP.mono (redc32_ok (s := sp) (by rw [hax₅]; omega_arith) (by rw [k₅.gpr (by decide)]; exact hacc₄) hbx₅ h15₅ hs3
    (by omega_arith)) fun s₆ ⟨hacc₆, hval₆, hm₆, k₆⟩ => ?_
  have kk := ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆
  have hdi₆ : s₆.gpr .rdi = B := (kk.gpr (by decide)).trans hg.rdi
  have hs₆ := hg.scr.congr kk.2.2
  have hm6 : s₆.mem = s.mem := by rw [hm₆, hm₅, hm₄, hm₃, hm₂, hm₁]
  have hl6 : InRegions (s₆.rd ++ s₆.wr) (off B (8 * kT2)) 8 := hs₆.ld (by have := hdr_lt_slot w 8 (show kT2 < 32 by decide); omega_arith)
  have hw6 : InRegions s₆.wr (off B (8 * kT2)) 8 := hs₆.st (by have := hdr_lt_slot w 8 (show kT2 < 32 by decide); omega_arith)
  rw [hax₅, show s₅.gpr .rbp = s₄.gpr .rbp from k₅.gpr (by decide)] at hval₆
  rw [hax₃, hbp₃] at hval₄
  have hr : (s₆.gpr .rbp).toNat * 2 ^ 64 % sp = acc % sp := by
    have := trial_word_math (acc := 0) (V := 0) (j := 0) (by simpa using hval₄) hval₆ (by simp)
    simpa using this
  have hdiv := trial_div (w := w + 1) hodd hacc₆ (acc_entry_math hdv hval hr)
  refine WP.mono (WP.keep [.rax, .rcx, .rdx] (Q := fun t => t.mem = s₆.mem.writeW (off B (8 * kT2))
      (mask (decide ((s₆.gpr .rbp).toNat = 0 ∨ (s₆.gpr .rbp).toNat = (s₆.gpr .rbx).toNat)) |||
        s₆.mem.readW (off B (8 * kT2)) 64)) (by
    xrun [State.ea, hdr, hdi₆, hdrOff, hl6, hw6, sx1]
    rw [flag_eq]) rfl) fun t ⟨hmt, kt⟩ => ⟨?_, ⟨hs₆.congr kt.2.2, (kt.gpr (by decide)).trans hdi₆, ?_⟩, ?_, ?_⟩
  · have hd : decide ((s₆.gpr .rbp).toNat = 0 ∨ (s₆.gpr .rbp).toNat = (s₆.gpr .rbx).toNat) =
        decide (c % sp = 0) := decide_eq_decide.mpr (by
      rw [show (s₆.gpr .rbx).toNat = sp by rw [k₆.gpr (by decide)]; exact hbx₅]; exact hdiv.symm)
    rw [hmt, word_writeW_self, hd, hm6]
  · rw [hmt, hm6]; exact hg.hdr.store (by decide) (by decide) _
  · rw [hmt, hm6]; exact writeW_outside _ _ _ (by have := hdr_lt_slot w 8 (show kT2 < 32 by decide); omega_arith)
  · exact (kk.trans kt).mono (by decide)

/-- Entry `j` of the table word, on the candidate reduced modulo its product
in `r8`, from the loop's invariant. -/
theorem taEntry_ok {s₀ : State} {B : Addr} {Z w T N : Nat} {minv : BitVec 64} (hZ : slot w 8 ≤ Z)
    (hT : 8 * kT2 + 8 ≤ T) (hTZ : T + 2048 ≤ Z) {k j : Nat} (hk : k < 256) (hj : j < 4) {t : State}
    (hI : TLInv s₀ B Z w T N minv k t) (hf : word t.mem B (8 * kT2) = mask (anyPre (wv s₀.mem B (slot w aN) w) (4 * k + j)))
    (hT1 : word t.mem B (8 * kT1) = BitVec.ofNat 64 (tabWord k)) (hacc : (t.gpr .r8).toNat < 2 ^ 54)
    (hval : (t.gpr .r8).toNat * 2 ^ (64 * w) % wordProd k = wv s₀.mem B (slot w aN) w % wordProd k) :
    WP isa (.block (accEntry j)) t fun t' => TLInv s₀ B Z w T N minv k t' ∧
      word t'.mem B (8 * kT2) = mask (anyPre (wv s₀.mem B (slot w aN) w) (4 * k + j + 1)) ∧
      word t'.mem B (8 * kT1) = BitVec.ofNat 64 (tabWord k) ∧ t'.gpr .r8 = t.gpr .r8 := by
  have hn := hI.good.scr.nowrap
  have sN := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have h2 : 8 * kT2 + 8 ≤ slot w aN := hdr_lt_slot w aN (by decide)
  refine WP.mono (accEntry_ok hI.good hZ hk hj hT1 hacc hval) fun t' ⟨hf', hg', ho', k'⟩ =>
    ⟨⟨hg', ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, k'.gpr (by decide)⟩
  · rw [k'.gpr (by decide)]; exact hI.r13
  · rw [ho'.word (Or.inl (by unfold kT0 kT2 sFn; omega_arith)) (by unfold kT0 sFn; omega_arith)]; exact hI.n
  · intro i hi; rw [ho'.word (Or.inr (by omega_arith)) (by omega_arith)]; exact hI.tab i hi
  · rw [ho'.wv (Or.inr h2) (by omega_arith)]; exact hI.c
  · exact hI.frm.trans (Frm.of_outside ho' (by simp))
  · exact (hI.keep.trans k').mono (by decide)
  · rw [hf', hf, mask_or2, anyPre_succ, Bool.or_comm]
    congr 2
  · rw [ho'.word (Or.inl (by unfold kT1 kT2 sFn; omega_arith)) (by unfold kT1 sFn; omega_arith)]; exact hT1

/-- One word of the table, its four entries, and the exit test. -/
theorem eeIter_ok {s₀ : State} {B : Addr} {Z w N : Nat} {minv : BitVec 64} (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hTZ : slot w aTab + 2048 ≤ Z) (hN : N ≤ 256) {k : Nat} (hk : k < N) {t : State}
    (hI : TLInv s₀ B Z w (slot w aTab) N minv k t)
    (hf : word t.mem B (8 * kT2) = mask (anyPre (wv s₀.mem B (slot w aN) w) (4 * k))) :
    WP isa (seqs sieveWord) t fun t' =>
      t'.zf = some (decide (k + 1 = N) || anyPre (wv s₀.mem B (slot w aN) w) (4 * (k + 1))) ∧
      TLInv s₀ B Z w (slot w aTab) N minv (k + 1) t' ∧
      word t'.mem B (8 * kT2) = mask (anyPre (wv s₀.mem B (slot w aN) w) (4 * (k + 1))) := by
  have hT : 8 * kT2 + 8 ≤ slot w aTab := hdr_lt_slot w aTab (by decide)
  unfold sieveWord sieveLoad
  simp only [List.append_assoc, List.cons_append]
  refine WP.seq (WP.mono (tlLoad_ok hZ hw' hTZ (by omega_arith) hI) fun t₁ ⟨hI₁, hT1₁, hf₁⟩ => ?_)
  rw [hf] at hf₁
  refine wp_seqs_append (a := productReduce) (by simp [productReduce]) (by simp)
    (WP.mono (productReduce_ok hI₁.good hZ hw hw' (by omega_arith) hT1₁) fun t₂ ⟨hacc₂, hval₂, hm₂, hg₂, k₂⟩ => ?_)
  have hn := hI₁.good.scr.nowrap
  have hP := (wordProd_facts (i := k) (by omega_arith)).2
  have hI₂ : TLInv s₀ B Z w (slot w aTab) N minv k t₂ :=
    ⟨hg₂, (k₂.gpr (by decide)).trans hI₁.r13, by rw [hm₂]; exact hI₁.n, fun i hi => by rw [hm₂]; exact hI₁.tab i hi,
      by rw [hm₂]; exact hI₁.c, by rw [hm₂]; exact hI₁.frm, (hI₁.keep.trans k₂).mono (by decide)⟩
  rw [← hm₂] at hf₁ hT1₁
  rw [hI₁.c] at hval₂
  have hacc₂' : (t₂.gpr .r8).toNat < 2 ^ 54 := by omega_arith
  have e := fun j (hj : j < 4) t (hI : TLInv s₀ B Z w (slot w aTab) N minv k t) hf hT1 hacc hval =>
    taEntry_ok (j := j) hZ hT hTZ (by omega_arith) hj hI hf hT1 hacc hval
  simp only [seqs]
  refine WP.seq (WP.mono (e 0 (by decide) t₂ hI₂ (by rw [hf₁, Nat.add_zero]) hT1₁ hacc₂' hval₂)
    fun t₃ ⟨hI₃, hf₃, hT1₃, h8₃⟩ => ?_)
  rw [← h8₃] at hacc₂' hval₂
  refine WP.seq (WP.mono (e 1 (by decide) t₃ hI₃ (by rw [hf₃, Nat.add_zero]) hT1₃ hacc₂' hval₂)
    fun t₄ ⟨hI₄, hf₄, hT1₄, h8₄⟩ => ?_)
  rw [← h8₄] at hacc₂' hval₂
  refine WP.seq (WP.mono (e 2 (by decide) t₄ hI₄ (by rw [hf₄]) hT1₄ hacc₂' hval₂)
    fun t₅ ⟨hI₅, hf₅, hT1₅, h8₅⟩ => ?_)
  rw [← h8₅] at hacc₂' hval₂
  refine WP.seq (WP.mono (e 3 (by decide) t₅ hI₅ (by rw [hf₅]) hT1₅ hacc₂' hval₂)
    fun t₆ ⟨hI₆, hf₆, _, _⟩ => ?_)
  have hn := hI₆.good.scr.nowrap
  have hl : InRegions (t₆.rd ++ t₆.wr) (off B (8 * kT0)) 8 :=
    hI₆.good.scr.ld (by have := hdr_lt_slot w 8 (show kT0 < 32 by decide); omega_arith)
  have hl2 : InRegions (t₆.rd ++ t₆.wr) (off B (8 * kT2)) 8 :=
    hI₆.good.scr.ld (by have := hdr_lt_slot w 8 (show kT2 < 32 by decide); omega_arith)
  have hf₆' : word t₆.mem B (8 * kT2) = mask (anyPre (wv s₀.mem B (slot w aN) w) (4 * (k + 1))) := by
    rw [hf₆, show 4 * k + 3 + 1 = 4 * (k + 1) by omega_arith]
  refine WP.mono (WP.keep [.r13, .rax, .rcx] (Q := fun t' =>
      t'.zf = some (decide (k + 1 = N) || anyPre (wv s₀.mem B (slot w aN) w) (4 * (k + 1))) ∧
      t'.gpr .r13 = BitVec.ofNat 64 (k + 1) ∧ t'.mem = t₆.mem) (by
    unfold sieveNext
    xrun [State.ea, hdr, hI₆.good.rdi, hdrOff, hl, hl2, hI₆.n, hI₆.r13, ofNat_add_one, hf₆',
      exit_bv (show k + 1 ≤ N by omega_arith) (show N < 2 ^ 64 by omega_arith)]) rfl) fun t' ⟨⟨hz, h13, hm⟩, k'⟩ =>
    ⟨hz, ⟨⟨hI₆.good.scr.congr k'.2.2, (k'.gpr (by decide)).trans hI₆.good.rdi, by rw [hm]; exact hI₆.good.hdr⟩,
      h13, by rw [hm]; exact hI₆.n, fun i hi => by rw [hm]; exact hI₆.tab i hi, by rw [hm]; exact hI₆.c,
      by rw [hm]; exact hI₆.frm, (hI₆.keep.trans k').mono (by decide)⟩, by rw [hm, hf₆']⟩

/-- Where `sievePrefix` leaves the loop: the table at `aTab`, the count `N`,
the flag clear and `r13 = 0`, the candidate unchanged. -/
structure SieveStart (s : State) (B : Addr) (Z w N : Nat) (minv : BitVec 64) (t : State) : Prop where
  inv : TLInv t B Z w (slot w aTab) N minv 0 t
  flag : word t.mem B (8 * kT2) = mask (anyPre (wv t.mem B (slot w aN) w) (4 * 0))
  c : wv t.mem B (slot w aN) w = wv s.mem B (slot w aN) w
  frm : Frm B [(slot w aTab, 2048), (8 * kT0, 8), (8 * kT2, 8)] s.mem t.mem
  keep : Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r12, .r13, .r14, .r15] s t

/-- `sieveStart`: the count `N` from RAX, the flag cleared, `r13 = 0`. -/
theorem sieveStart_ok {s s₃ t : State} {B : Addr} {Z w N : Nat} {minv : BitVec 64}
    (hTZ : slot w aTab + 2048 ≤ Z) (hg₃ : Good s₃ B Z w minv)
    (hc₃ : wv s₃.mem B (slot w aN) w = wv s.mem B (slot w aN) w)
    (ho₃ : Outside B (slot w aTab) 2048 s.mem s₃.mem)
    (htab₃ : ∀ i < 256, word s₃.mem B (slot w aTab + 8 * i) = BitVec.ofNat 64 (tabWord i))
    (k₀ : Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r12, .r13, .r14, .r15] s s₃)
    (hax : t.gpr .rax = BitVec.ofNat 64 N) (hmt : t.mem = s₃.mem) (kt : Keep [.rax] s₃ t) :
    WP isa (.block sieveStart) t (SieveStart s B Z w N minv) := by
  have hn := hg₃.scr.nowrap
  have hT2 : 8 * kT2 + 8 ≤ slot w aN := hdr_lt_slot w aN (by decide)
  have hTa : slot w aN + 8 * (w + 2) ≤ slot w aTab := by unfold slot aN aTab; omega_arith
  have hTa' : 8 * kT2 + 8 ≤ slot w aTab := hdr_lt_slot w aTab (by decide)
  unfold sieveStart
  have hgt : Good t B Z w minv := ⟨hg₃.scr.congr kt.2.2, (kt.gpr (by decide)).trans hg₃.rdi, by rw [hmt]; exact hg₃.hdr⟩
  have hst : ∀ i < 32, InRegions t.wr (off B (8 * i)) 8 := fun i hi => hgt.scr.st (by have := hdr_lt_slot w 8 hi; omega_arith)
  refine WP.mono (WP.keep [.rax, .r13] (Q := fun t' => t'.mem = (t.mem.writeW (off B (8 * kT0))
      (BitVec.ofNat 64 N)).writeW (off B (8 * kT2)) (0 : BitVec 64) ∧ t'.gpr .r13 = BitVec.ofNat 64 0) (by
    xrun [State.ea, hdr, hgt.rdi, hdrOff, hst kT0 (by decide), hst kT2 (by decide), hax, sx_ofNat]
    rfl) rfl) fun t₄ ⟨⟨hm₄, h13₄⟩, k₄⟩ => ?_
  have hoA : Outside B (8 * kT0) 8 t.mem (t.mem.writeW (off B (8 * kT0)) (BitVec.ofNat 64 N)) :=
    writeW_outside _ _ _ (by unfold kT0 sFn; omega_arith)
  have hoB : ∀ m : Mem, Outside B (8 * kT2) 8 m (m.writeW (off B (8 * kT2)) (0 : BitVec 64)) :=
    fun m => writeW_outside _ _ _ (by unfold kT2 sFn; omega_arith)
  have hg₄ : Good t₄ B Z w minv := ⟨hgt.scr.congr k₄.2.2, (k₄.gpr (by decide)).trans hgt.rdi,
    by rw [hm₄]; exact (hgt.hdr.store (by decide) (by decide) _).store (by decide) (by decide) _⟩
  have hc₄ : wv t₄.mem B (slot w aN) w = wv s.mem B (slot w aN) w := by
    rw [hm₄, (hoB _).wv (Or.inr hT2) (by omega_arith),
      hoA.wv (Or.inr (by unfold kT0 kT2 sFn at *; omega_arith)) (by omega_arith), hmt, hc₃]
  have hN₄ : word t₄.mem B (8 * kT0) = BitVec.ofNat 64 N := by
    rw [hm₄, (hoB _).word (Or.inl (by unfold kT0 kT2 sFn; omega_arith)) (by unfold kT0 sFn; omega_arith),
      word_writeW_self]
  have htab₄ : ∀ i < 256, word t₄.mem B (slot w aTab + 8 * i) = BitVec.ofNat 64 (tabWord i) := fun i hi => by
    rw [hm₄, (hoB _).word (Or.inr (by omega_arith)) (by omega_arith),
      hoA.word (Or.inr (by have := hdr_lt_slot w aTab (show kT0 < 32 by decide); omega_arith)) (by omega_arith),
      hmt]; exact htab₃ i hi
  have hf₄ : word t₄.mem B (8 * kT2) = mask (anyPre (wv t₄.mem B (slot w aN) w) (4 * 0)) := by
    rw [hm₄, word_writeW_self]; unfold anyPre
    rw [Nat.mul_zero, show List.range 0 = [] from rfl, List.any_nil, mask_false]
  refine ⟨⟨hg₄, h13₄, hN₄, htab₄, rfl, Frm.refl _ _ _, Keep.refl _ _⟩, hf₄, hc₄, ?_,
    ((k₀.trans kt).trans k₄).mono (by decide)⟩
  intro x hx
  rw [hm₄, hoB _ x (hx (8 * kT2, 8) (by simp)), hoA x (hx (8 * kT0, 8) (by simp)), hmt,
    ho₃ x (hx (slot w aTab, 2048) (by simp))]

/-- `sievePrefix`: the table, the count for `bits` in RDX, and the flag. -/
theorem sievePrefix_ok {s : State} {B : Addr} {Z w bits : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hTZ : slot w aTab + 2048 ≤ Z) (hw' : w < 2 ^ 31)
    (hb : bits < 2 ^ 32) (hdx : s.gpr .rdx = BitVec.ofNat 64 bits) :
    WP isa sievePrefix s (SieveStart s B Z w (sieveCount bits) minv) := by
  have hn := hg.scr.nowrap
  have hT2 : 8 * kT2 + 8 ≤ slot w aN := hdr_lt_slot w aN (by decide)
  have hTa : slot w aN + 8 * (w + 2) ≤ slot w aTab := by unfold slot aN aTab; omega_arith
  have hTa' : 8 * kT2 + 8 ≤ slot w aTab := hdr_lt_slot w aTab (by decide)
  unfold sievePrefix
  simp only [seqs]
  -- The table, and the number of its words to use.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (extBase_ok hg hZ hw' (j := aTab) (by decide) (r := .rbx) (by decide) rfl rfl)
    fun s₁ ⟨hbx₁, hm₁, k₁⟩ => ?_
  refine WP.mono (tabWrites_ok (hg.scr.congr k₁.2.2) hTZ hbx₁ 256 (Nat.le_refl _)) fun s₂ ⟨htab₂, ho₂, k₂⟩ => ?_
  have hm₂ : ∀ i < 32, word s₂.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
    rw [ho₂.word (Or.inl (by have := hdr_lt_slot w aTab hi; omega_arith)) (by omega_arith), hm₁]
  have hdi₂ : s₂.gpr .rdi = B := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hg.rdi)
  have hdx₂ : s₂.gpr .rdx = BitVec.ofNat 64 bits := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hdx)
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 128 ∧
      t.cf = some (decide (bits < 1025)) ∧ t.mem = s₂.mem) (by
    xrun [hdx₂, sx_ofNat]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
      show (BitVec.signExtend 64 (1025 : BitVec 32)).toNat = 1025 by decide]) rfl)
    fun s₃ ⟨⟨hax₃, hcf₃, hm₃⟩, k₃⟩ => ?_
  have hg₃ : Good s₃ B Z w minv := ⟨hg.scr.congr (k₃.2.2.trans (k₂.2.2.trans k₁.2.2)), (k₃.gpr (by decide)).trans hdi₂,
    ⟨by rw [hm₃, hm₂ sW (by decide)]; exact hg.hdr.hw, by rw [hm₃, hm₂ sMinv (by decide)]; exact hg.hdr.hminv,
      fun j hj => by rw [hm₃, hm₂ (sArr j) (by unfold sArr; omega_arith)]; exact hg.hdr.harr j hj⟩⟩
  have hc₃ : wv s₃.mem B (slot w aN) w = wv s.mem B (slot w aN) w := by
    rw [hm₃, ho₂.wv (k := w) (Or.inl (by omega_arith)) (by omega_arith), hm₁]
  have ho₃ : Outside B (slot w aTab) 2048 s.mem s₃.mem := by rw [hm₃, ← hm₁]; exact ho₂
  generalize hNdef : sieveCount bits = N
  have hN : N ≤ 256 ∧ 1 ≤ N := by rw [← hNdef]; unfold sieveCount; split <;> omega_arith
  have hN128 : bits < 1025 → N = 128 := fun h => by rw [← hNdef]; unfold sieveCount; split <;> omega_arith
  have hN256 : ¬ bits < 1025 → N = 256 := fun h => by rw [← hNdef]; unfold sieveCount; split <;> omega_arith
  have htab₃ : ∀ i < 256, word s₃.mem B (slot w aTab + 8 * i) = BitVec.ofNat 64 (tabWord i) := fun i hi => by
    rw [hm₃]; exact htab₂ i hi
  have k₀ : Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r12, .r13, .r14, .r15] s s₃ :=
    ((k₁.trans k₂).trans k₃).mono (by decide)
  have cont : ∀ t : State, t.gpr .rax = BitVec.ofNat 64 N → t.mem = s₃.mem → Keep [.rax] s₃ t →
      WP isa (.block sieveStart) t (SieveStart s B Z w N minv) := fun t hax hmt kt =>
    sieveStart_ok hTZ hg₃ hc₃ ho₃ htab₃ k₀ hax hmt kt
  refine WP.seq (WP.ite (decide (bits < 1025)) (by simp [eval, hcf₃])
    (fun h => WP.block_nil (cont s₃ ?_ rfl (Keep.refl _ _)))
    (fun h => WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 N ∧ t.mem = s₃.mem) (by
      xrun [sx_ofNat]; rw [hN256 (by simpa using h)]; rfl) rfl) fun t ⟨⟨h1, h2⟩, k⟩ => cont t h1 h2 k))
  rw [hax₃, hN128 (by simpa using h)]

/-- The sieve's loop and its result, from where its prefix leaves it: ZF set
iff none of the table's first `4 N` entries divides the candidate. -/
theorem sieveRest_ok {s t₄ : State} {B : Addr} {Z w N : Nat} {minv : BitVec 64}
    (hZ : slot w 8 ≤ Z) (hTZ : slot w aTab + 2048 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hN : N ≤ 256 ∧ 1 ≤ N) (hS : SieveStart s B Z w N minv t₄) :
    WP isa (.seq (.loop (seqs sieveWord) .ne) (.block sieveTail)) t₄ fun t =>
      t.zf = some (!(anyPre (wv s.mem B (slot w aN) w) (4 * N))) ∧ Good t B Z w minv ∧
      Frm B [(slot w aTab, 2048), (8 * kT0, 8), (8 * kT1, 8), (8 * kT2, 8)] s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r12, .r13, .r14, .r15] s t := by
  obtain ⟨hI₀, hf₄, hc₄, hfrm₄, k₄⟩ := hS
  have hF := firstHit_le (wv t₄.mem B (slot w aN) w) N
  refine WP.seq (WP.mono (wp_upto (a := 0) (N := firstHit (wv t₄.mem B (slot w aN) w) N)
    (by have := firstHit_pos (c := wv t₄.mem B (slot w aN) w) hN.2; omega_arith)
    (fun k t' => TLInv t₄ B Z w (slot w aTab) N minv k t' ∧
      word t'.mem B (8 * kT2) = mask (anyPre (wv t₄.mem B (slot w aN) w) (4 * k)))
    (fun k _ hk t' ⟨hI, hf⟩ => WP.mono (eeIter_ok hZ hw hw' hTZ hN.1 (by omega_arith) hI hf)
      fun t'' ⟨hz, hI', hf'⟩ => ⟨by rw [hz, firstHit_exit hk], hI', hf'⟩) (fun t' h => h)
    ⟨hI₀, hf₄⟩) fun t₅ ⟨hI₅, hf₅⟩ => ?_)
  rw [firstHit_any] at hf₅
  have hl₅ : InRegions (t₅.rd ++ t₅.wr) (off B (8 * kT2)) 8 :=
    hI₅.good.scr.ld (by have := hdr_lt_slot w 8 (show kT2 < 32 by decide); omega_arith)
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.zf = some (!anyPre (wv s.mem B (slot w aN) w) (4 * N)) ∧
      t'.mem = t₅.mem) (by
    unfold sieveTail
    xrun [State.ea, hdr, hI₅.good.rdi, hdrOff, hl₅, hf₅, BitVec.and_self, hc₄]
    cases anyPre (wv s.mem B (slot w aN) w) (4 * N) <;> decide) rfl)
    fun t' ⟨⟨hz, hm'⟩, k'⟩ => ⟨hz, ⟨hI₅.good.scr.congr k'.2.2, (k'.gpr (by decide)).trans hI₅.good.rdi,
      by rw [hm']; exact hI₅.good.hdr⟩, ?_, ((k₄.trans hI₅.keep).trans k').mono (by decide)⟩
  intro x hx
  rw [hm', hI₅.frm x (fun r hr => hx r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h <;> simp [h])),
    hfrm₄ x (fun r hr => hx r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h <;> simp [h]))]

/-- `sieve`: ZF set iff none of the table's first `4 (sieveCount bits)`
entries divides the candidate in `aN`, `bits` in RDX. -/
theorem sieve_ok {s : State} {B : Addr} {Z w bits : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hTZ : slot w aTab + 2048 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hb : bits < 2 ^ 32) (hdx : s.gpr .rdx = BitVec.ofNat 64 bits) :
    WP isa sieve s fun t =>
      t.zf = some (!(anyPre (wv s.mem B (slot w aN) w) (4 * sieveCount bits))) ∧ Good t B Z w minv ∧
      Frm B [(slot w aTab, 2048), (8 * kT0, 8), (8 * kT1, 8), (8 * kT2, 8)] s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r12, .r13, .r14, .r15] s t := by
  have hN : sieveCount bits ≤ 256 ∧ 1 ≤ sieveCount bits := by unfold sieveCount; split <;> omega_arith
  unfold sieve
  exact WP.seq (WP.mono (sievePrefix_ok hg hZ hTZ hw' hb hdx) fun t₄ hS => sieveRest_ok hZ hTZ hw hw' hN hS)

/-- `sievePrefixN n`: the table, the count `n`, and the flag. -/
theorem sievePrefixN_ok {s : State} {B : Addr} {Z w n : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hTZ : slot w aTab + 2048 ≤ Z) (hw' : w < 2 ^ 31) (hn : n < 2 ^ 31) :
    WP isa (sievePrefixN n) s (SieveStart s B Z w n minv) := by
  have hTa : slot w aN + 8 * (w + 2) ≤ slot w aTab := by unfold slot aN aTab; omega_arith
  unfold sievePrefixN
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (extBase_ok hg hZ hw' (j := aTab) (by decide) (r := .rbx) (by decide) rfl rfl)
    fun s₁ ⟨hbx₁, hm₁, k₁⟩ => ?_
  refine WP.mono (tabWrites_ok (hg.scr.congr k₁.2.2) hTZ hbx₁ 256 (Nat.le_refl _)) fun s₂ ⟨htab₂, ho₂, k₂⟩ => ?_
  have hn := hg.scr.nowrap
  have hm₂ : ∀ i < 32, word s₂.mem B (8 * i) = word s.mem B (8 * i) := fun i hi => by
    rw [ho₂.word (Or.inl (by have := hdr_lt_slot w aTab hi; omega_arith)) (by omega_arith), hm₁]
  have hg₂ : Good s₂ B Z w minv := ⟨hg.scr.congr (k₂.2.2.trans k₁.2.2),
    (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hg.rdi),
    ⟨by rw [hm₂ sW (by decide)]; exact hg.hdr.hw, by rw [hm₂ sMinv (by decide)]; exact hg.hdr.hminv,
      fun j hj => by rw [hm₂ (sArr j) (by unfold sArr; omega_arith)]; exact hg.hdr.harr j hj⟩⟩
  have hc₂ : wv s₂.mem B (slot w aN) w = wv s.mem B (slot w aN) w := by
    rw [ho₂.wv (k := w) (Or.inl (by omega_arith)) (by omega_arith), hm₁]
  have ho₂' : Outside B (slot w aTab) 2048 s.mem s₂.mem := by rw [← hm₁]; exact ho₂
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 n ∧ t.mem = s₂.mem)
    (by xrun; apply BitVec.eq_of_toNat_eq; simp; omega) rfl)
    fun t ⟨⟨hax, hmt⟩, kt⟩ => sieveStart_ok hTZ hg₂ hc₂ ho₂' htab₂ ((k₁.trans k₂).mono (by decide)) hax hmt kt

/-- `sieveFirst`: ZF set iff none of the table's first `4 firstWords` entries
divides the candidate in `aN`. -/
theorem sieveFirst_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hTZ : slot w aTab + 2048 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) :
    WP isa sieveFirst s fun t =>
      t.zf = some (!(anyPre (wv s.mem B (slot w aN) w) (4 * firstWords))) ∧ Good t B Z w minv ∧
      Frm B [(slot w aTab, 2048), (8 * kT0, 8), (8 * kT1, 8), (8 * kT2, 8)] s.mem t.mem ∧
      Keep [.rax, .rbx, .rcx, .rdx, .rsi, .rbp, .r8, .r12, .r13, .r14, .r15] s t := by
  unfold sieveFirst
  exact WP.seq (WP.mono (sievePrefixN_ok hg hZ hTZ hw' (by decide)) fun t₄ hS =>
    sieveRest_ok hZ hTZ hw hw' (by decide) hS)

/-- Above the table's largest prime, an odd candidate passes the sieve iff
it has `primeShape` and is not `obviouslyComposite` for the requested width. -/
theorem sieve_shape {c bits : Nat} (hc : 8161 < c) (ho : c % 2 = 1) :
    (!anyPre c (4 * sieveCount bits)) =
      (Spec.Ffdh.primeShape c && !Spec.RsaKeyGen.obviouslyComposite bits c) := by
  have htrial : anyPre c (4 * sieveCount bits) = Spec.RsaKeyGen.obviouslyComposite bits c := by
    have he := VG.Proof.RsaKeyGen.trialAny_eq (w := if 1025 ≤ bits then 17 else 16) hc
    have hw : (if 17 ≤ (if 1025 ≤ bits then 17 else 16) then 256 else 128) = sieveCount bits := by
      unfold sieveCount; split <;> simp
    have hb : Spec.RsaKeyGen.obviouslyComposite (64 * if 1025 ≤ bits then 17 else 16) c =
        Spec.RsaKeyGen.obviouslyComposite bits c := by
      unfold Spec.RsaKeyGen.obviouslyComposite Spec.RsaKeyGen.trialPrimes
      by_cases h : 1025 ≤ bits
      · simp only [h, ↓reduceIte, show 1024 < 64 * 17 by decide, show 1024 < bits by omega]
      · simp only [h, ↓reduceIte, show ¬ 1024 < 64 * 16 by decide, show ¬ 1024 < bits by omega]
    rw [hw, hb] at he
    exact he
  have h53 : 53 ≤ 4 * sieveCount bits := by unfold sieveCount; split <;> omega
  rw [VG.Proof.Ffdh.ParameterCandidate.primeShape_sieve hc ho, ← htrial]
  cases hA : anyPre c (4 * sieveCount bits)
  · have h' : ((List.range 53).any fun i => c % VG.Impl.RsaKeyGen.tabEntry i == 0) = false := by
      cases h5 : ((List.range 53).any fun i => c % VG.Impl.RsaKeyGen.tabEntry i == 0)
      · rfl
      · have := anyPre_mono h53 h5; rw [hA] at this; contradiction
    simp [h']
  · simp

theorem oddTest_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) :
    WP isa (.block oddTest) s fun t =>
      t.zf = some (decide (wv s.mem B (slot w aN) w % 2 = 1)) ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * sArr aN)) 8 :=
    hg.scr.ld (by have := hdr_lt_slot w 8 (show sArr aN < 32 by decide); omega_arith)
  have hn : InRegions (s.rd ++ s.wr) (off B (slot w aN)) 8 :=
    hg.scr.ld (by have := slot_le (w := w) (show aN < 8 by decide); omega_arith)
  have he : ((word s.mem B (slot w aN) &&& 1) == 1) = decide (wv s.mem B (slot w aN) w % 2 = 1) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    rw [← BitVec.toNat_inj, BitVec.toNat_and, show (1 : BitVec 64).toNat = 1 from rfl,
      show (1 : Nat) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    rw [← wv_mod64 s.mem B (slot w aN) hw, Nat.mod_mod_of_dvd _ (show 2 ∣ 2 ^ 64 by decide)]
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.zf = some (decide (wv s.mem B (slot w aN) w % 2 = 1)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨hz, hm⟩, k⟩ => ⟨hz, hm, k⟩
  unfold oddTest
  xrun [State.ea, hdr, at0, hg.rdi, hdrOff, hl, hn, BitVec.ofInt_ofNat, BitVec.add_zero, hg.hdr.harr aN (by decide)]
  simpa only [sub_beq_zero, show BitVec.signExtend 64 (1 : BitVec 32) = 1 from by decide] using he

end VG.Proof.Ffdh.X86_64.ParameterCandidate

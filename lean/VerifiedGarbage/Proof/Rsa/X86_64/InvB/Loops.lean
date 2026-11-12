module
-- separate module: the inverse's proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Impl.Rsa.X86_64.Keys
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.X86_64.Words
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Rsa.X86_64.Loops
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-!
# RSA's inverse by divsteps on x86-64: the loops over the words

The bases of the inverse's arrays from its window (`wa_ok`), and the arithmetic of its
rows: the shift by 59 (`shr59_word`, `shr_top`) and the
signed linear combination (`lin_term`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.InvB

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.Inv
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-- A sequence of two nonempty sequences. -/
theorem seqs_append_iff : ∀ (cs ds : List (Prog isa)), cs ≠ [] → ds ≠ [] → ∀ (s : State) (Q : State → Prop),
    WP isa (seqs (cs ++ ds)) s Q ↔ WP isa (seqs cs) s fun t => WP isa (seqs ds) t Q
  | [], _, h, _, _, _ => absurd rfl h
  | [c], d :: ds, _, _, s, Q => by
    show WP isa (.seq c (seqs (d :: ds))) s Q ↔ _
    rw [WP.seq_iff]; rfl
  | c :: c' :: cs, ds, _, hd, s, Q => by
    show WP isa (.seq c (seqs (c' :: cs ++ ds))) s Q ↔ WP isa (.seq c (seqs (c' :: cs))) s _
    rw [WP.seq_iff, WP.seq_iff]
    exact ⟨fun h => WP.mono h fun t ht => (seqs_append_iff (c' :: cs) ds (by simp) hd t Q).mp ht,
      fun h => WP.mono h fun t ht => (seqs_append_iff (c' :: cs) ds (by simp) hd t Q).mpr ht⟩
  | [_], [], _, hd, _, _ => absurd rfl hd

/-- `wa k r`: `r := rdi + k · r9`, from `rdi` at array `j`'s base: array `j + k`'s. -/
theorem wa_ok {s : State} {B : Addr} {w j : Nat} (k : Nat) {r : Reg} (hr' : r ≠ .r9)
    (hdi : s.gpr .rdi = off B (slot w j)) (h9 : s.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2))) :
    WP isa (.block (wa k r)) s fun t =>
      t.gpr r = off B (slot w (j + k)) ∧ t.mem = s.mem ∧ Keep [r] s t := by
  unfold wa
  rw [WP.block_append_iff]
  have e₀ : WP isa (.block [.mov r (.reg .rdi)]) s
      fun (t₁ : State) => t₁.gpr r = off B (slot w (j + 0)) ∧ t₁.mem = s.mem ∧ Keep [r] s t₁ := by
    xrun [hdi]
    exact ⟨rfl, only_of (fun r' h => by simp [setReg_gpr, h]) rfl rfl⟩
  refine WP.mono e₀ fun t₁ ⟨h₁, m₁, k₁⟩ => ?_
  have h9₁ : t₁.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) := (k₁.gpr (by simp [hr'.symm])).trans h9
  suffices ∀ n, ∀ t, t.gpr r = off B (slot w (j + (k - n))) → t.gpr .r9 = BitVec.ofNat 64 (8 * (w + 2)) →
      n ≤ k → WP isa (.block (List.replicate n (.alu .add r (.reg .r9)))) t fun t' =>
        t'.gpr r = off B (slot w (j + k)) ∧ t'.mem = t.mem ∧ Keep [r] t t' by
    refine WP.mono (this k t₁ (by rw [Nat.sub_self]; exact h₁) h9₁ (Nat.le_refl _))
      fun t ⟨h, m, k'⟩ => ⟨h, m.trans m₁, (k₁.trans k').mono (by simp)⟩
  intro n
  induction n with
  | zero => intro t h _ _; exact WP.block_nil ⟨by rwa [Nat.sub_zero] at h, rfl, Keep.refl _ _⟩
  | succ n ih =>
    intro t h h9t hn
    rw [List.replicate_succ, show (Instr.alu .add r (.reg .r9) :: List.replicate n (.alu .add r (.reg .r9))) =
      [.alu .add r (.reg .r9)] ++ List.replicate n (.alu .add r (.reg .r9)) from rfl, WP.block_append_iff]
    have e₁ : WP isa (.block [.alu .add r (.reg .r9)]) t
        fun (t₁ : State) => t₁.gpr r = off B (slot w (j + (k - n))) ∧ t₁.mem = t.mem ∧ Keep [r] t t₁ := by
      xrun [h, h9t]
      refine ⟨?_, only_of (fun r' h => by simp [setReg_gpr, setFlags_gpr, h]) rfl rfl⟩
      rw [add_r9 _ B w (j + (k - (n + 1))) rfl, show j + (k - (n + 1)) + 1 = j + (k - n) by omega_using [hn]]
    refine WP.mono e₁ fun t₁ ⟨h₁, m₁, k₁⟩ => ?_
    refine WP.mono (ih t₁ h₁ ((k₁.gpr (by simp [hr'.symm])).trans h9t) (by omega_using [hn]))
      fun t' ⟨h', m', k'⟩ => ⟨h', m'.trans m₁, (k₁.trans k').mono (by simp)⟩

/-! ## The shift by 59 -/

theorem shr59_word (x y : BitVec 64) :
    (x >>> 59 + y <<< 5).toNat = x.toNat / 2 ^ 59 + y.toNat % 2 ^ 59 * 32 := by
  have hx := x.isLt
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq]
  have e : y.toNat * 2 ^ 5 % 2 ^ 64 = y.toNat % 2 ^ 59 * 32 := by
    rw [show (2 : Nat) ^ 64 = 2 ^ 59 * 32 from rfl, show (2 : Nat) ^ 5 = 32 from rfl, Nat.mul_mod_mul_right]
  rw [e]
  have : x.toNat / 2 ^ 59 < 32 := by omega
  have : y.toNat % 2 ^ 59 < 2 ^ 59 := Nat.mod_lt _ (by decide)
  omega

/-- After `j` words of `shrBody`: `D_j + 2^(64 j) (T_j / 2^59) = T_{j+1} / 2^59`. -/
theorem pow59 (j : Nat) : 2 ^ (64 * (j + 1)) = 2 ^ 59 * (2 ^ (64 * j) * 32) := by
  rw [pow64_succ, show (2 : Nat) ^ 64 = 2 ^ 59 * 32 from rfl]; grind

def signW (x : BitVec 64) : Nat := if 2 ^ 63 ≤ x.toNat then 2 ^ 64 - 1 else 0

theorem maskOf_toNat (x : BitVec 64) :
    (BitVec.setWidth 64 (0 : BitVec 32) - x >>> 63).toNat = signW x := by
  unfold signW
  have hx := x.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [show (BitVec.setWidth 64 (0 : BitVec 32)).toNat = 0 from rfl]
  by_cases h : 2 ^ 63 ≤ x.toNat
  · simp only [h, ↓reduceIte, show x.toNat / 2 ^ 63 = 1 by omega]
  · simp only [h, ↓reduceIte, show x.toNat / 2 ^ 63 = 0 by omega]

theorem shr_top {V S n : Nat} (hV : V < 2 ^ (64 * (n + 1))) :
    (V + 2 ^ (64 * (n + 1)) * S) / 2 ^ 59 % 2 ^ (64 * (n + 1)) = V / 2 ^ 59 + 2 ^ (64 * n) * (S % 2 ^ 59 * 32) := by
  have e : 2 ^ (64 * (n + 1)) * S = 2 ^ 59 * (2 ^ (64 * n) * 32 * (S % 2 ^ 59)) +
      2 ^ 59 * (2 ^ (64 * (n + 1)) * (S / 2 ^ 59)) := by
    have := Nat.div_add_mod S (2 ^ 59)
    rw [pow59]
    grind
  rw [e, ← Nat.add_assoc, Nat.add_mul_div_left _ _ (show 0 < 2 ^ 59 by decide),
    Nat.add_mul_div_left _ _ (show 0 < 2 ^ 59 by decide), Nat.add_mul_mod_self_left]
  have h1 : V / 2 ^ 59 < 2 ^ (64 * n) * 32 := by
    rw [Nat.div_lt_iff_lt_mul (by decide)]; rw [pow59] at hV; grind
  have h2 : S % 2 ^ 59 < 2 ^ 59 := Nat.mod_lt _ (by decide)
  have h3 : 2 ^ (64 * n) * 32 * (S % 2 ^ 59) ≤ 2 ^ (64 * n) * 32 * (2 ^ 59 - 1) := Nat.mul_le_mul_left _ (by omega)
  rw [Nat.mod_eq_of_lt (by rw [pow64_succ]; grind)]
  grind

/-! ## The signed linear combination -/

theorem offD (p : Addr) (e d : Nat) : off p e + BitVec.ofInt 64 (d : Int) = off p (e + d) := by
  simp only [off]
  rw [BitVec.ofInt_natCast, BitVec.add_assoc, BitVec.ofNat_add]

/-- The `n` words at `d`, each `⊕ k`. -/
def wvM (m : Mem) (p : Addr) (d : Nat) (k : BitVec 64) : Nat → Nat
  | 0 => 0
  | n + 1 => wvM m p d k n + 2 ^ (64 * n) * (word m p (d + 8 * n) ^^^ k).toNat

theorem wvM_congr {m m' : Mem} {p : Addr} {d n : Nat} {k : BitVec 64}
    (h : ∀ i < n, word m' p (d + 8 * i) = word m p (d + 8 * i)) : wvM m' p d k n = wvM m p d k n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [wvM]; rw [ih fun i hi => h i (by omega), h n (by omega)]

/-! ### Absolute values and masks -/

theorem abs_word (x : BitVec 64) :
    (x ^^^ (BitVec.setWidth 64 (0 : BitVec 32) - x >>> 63)) - (BitVec.setWidth 64 (0 : BitVec 32) - x >>> 63) =
      BitVec.ofNat 64 x.toInt.natAbs ∧
    BitVec.setWidth 64 (0 : BitVec 32) - x >>> 63 = mask (decide (x.toInt < 0)) := by
  have hx := x.isLt
  have hm := maskOf_toNat x
  unfold signW at hm
  by_cases h : 2 ^ 63 ≤ x.toNat
  · have e : BitVec.setWidth 64 (0 : BitVec 32) - x >>> 63 = BitVec.allOnes 64 := by
      apply BitVec.eq_of_toNat_eq; rw [hm]; simp only [h, ↓reduceIte]; rfl
    have ht : x.toInt = (x.toNat : Int) - 2 ^ 64 := by
      rw [BitVec.toInt_eq_toNat_cond]; simp only [show ¬ (2 * x.toNat < 2 ^ 64) by omega, ↓reduceIte]; omega
    have hn : x.toInt.natAbs = 2 ^ 64 - x.toNat := by rw [ht]; omega
    rw [e, hn, show decide (x.toInt < 0) = true by rw [ht]; simp; omega, mask_true]
    refine ⟨?_, rfl⟩
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.xor_allOnes, BitVec.toNat_sub, BitVec.toNat_not, BitVec.toNat_allOnes, BitVec.toNat_ofNat]
    omega
  · have e : BitVec.setWidth 64 (0 : BitVec 32) - x >>> 63 = 0 := by
      apply BitVec.eq_of_toNat_eq; rw [hm]; simp only [h, ↓reduceIte]; rfl
    have ht : x.toInt = (x.toNat : Int) := by
      rw [BitVec.toInt_eq_toNat_cond]; simp only [show 2 * x.toNat < 2 ^ 64 by omega, ↓reduceIte]
    rw [e, ht, show decide ((x.toNat : Int) < 0) = false by simp, mask_false]
    refine ⟨?_, rfl⟩
    show (x ^^^ 0#64) - 0#64 = _
    rw [BitVec.xor_zero, BitVec.sub_zero]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Int.natAbs_natCast, Nat.mod_eq_of_lt hx]

/-! ### The combination as signed numbers -/

theorem wvM_mask (m : Mem) (p : Addr) (d : Nat) (c : Bool) :
    ∀ N, wvM m p d (mask c) N = if c then 2 ^ (64 * N) - 1 - wv m p d N else wv m p d N
  | 0 => by cases c <;> rfl
  | N + 1 => by
    have ih := wvM_mask m p d c N
    have hl := wv_lt m p d N
    have hx := (word m p (d + 8 * N)).isLt
    cases c
    · have ih' : wvM m p d (mask false) N = wv m p d N := by rw [ih]; rfl
      show wvM m p d (mask false) N + 2 ^ (64 * N) * (word m p (d + 8 * N) ^^^ mask false).toNat =
        wv m p d N + 2 ^ (64 * N) * (word m p (d + 8 * N)).toNat
      rw [ih', mask_false, show (0 : BitVec 64) = 0#64 from rfl, BitVec.xor_zero]
    · have ih' : wvM m p d (mask true) N = 2 ^ (64 * N) - 1 - wv m p d N := by rw [ih]; rfl
      show wvM m p d (mask true) N + 2 ^ (64 * N) * (word m p (d + 8 * N) ^^^ mask true).toNat =
        2 ^ (64 * (N + 1)) - 1 - (wv m p d N + 2 ^ (64 * N) * (word m p (d + 8 * N)).toNat)
      rw [ih', mask_true, BitVec.xor_allOnes, BitVec.toNat_not, pow64_succ, Nat.mul_sub, Nat.mul_sub,
        Nat.mul_one]
      have h1 : 2 ^ (64 * N) * (word m p (d + 8 * N)).toNat ≤ 2 ^ (64 * N) * (2 ^ 64 - 1) :=
        Nat.mul_le_mul_left _ (by omega)
      have hq : 2 ^ (64 * N) * (2 ^ 64 - 1) = 2 ^ (64 * N) * 2 ^ 64 - 2 ^ (64 * N) := Nat.mul_sub_one _ _
      have h2 : 1 ≤ 2 ^ (64 * N) := Nat.one_le_two_pow
      have := Nat.mul_le_mul_left (2 ^ (64 * N)) (show 1 ≤ 2 ^ 64 by decide)
      omega

/-- `|u| X' + (|u| if u < 0)` for `X'` the words of `X` complemented under the mask of
`u < 0`: `u X` modulo `2^(64 N)`. -/
theorem lin_term (m : Mem) (p : Addr) (d N : Nat) (u : Int) :
    ((u.natAbs * wvM m p d (mask (decide (u < 0))) N + (if u < 0 then u.natAbs else 0) : Nat) : Int) %
        2 ^ (64 * N) = (u * wv m p d N) % 2 ^ (64 * N) := by
  rw [wvM_mask]
  have hl := wv_lt m p d N
  by_cases h : u < 0
  · simp only [h, decide_true, ↓reduceIte]
    have e : u.natAbs * (2 ^ (64 * N) - 1 - wv m p d N) + u.natAbs + u.natAbs * wv m p d N =
        u.natAbs * 2 ^ (64 * N) := by
      rw [← Nat.mul_add_one, ← Nat.mul_add]; congr 1; omega
    have e' := congrArg (fun z : Nat => (z : Int)) e
    simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_pow] at e' ⊢
    have hu : (u.natAbs : Int) = -u := by omega
    rw [hu] at e' ⊢
    rw [show -u * ((2 ^ (64 * N) - 1 - wv m p d N : Nat) : Int) + -u = u * wv m p d N + 2 ^ (64 * N) * (-u) by
      grind, Int.add_mul_emod_self_left]
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Int.natCast_mul]
    rw [show (u.natAbs : Int) = u by omega]

/-! ## The Montgomery reduction by a word -/

/-- `N + 1` words: the lowest and the `N` above it. -/
theorem wv_succ_low (m : Mem) (p : Addr) (e : Nat) :
    ∀ N, wv m p e (N + 1) = (word m p e).toNat + 2 ^ 64 * wv m p (e + 8) N
  | 0 => by simp [wv]
  | N + 1 => by
    rw [wv, wv_succ_low m p e N, wv, show e + 8 * (N + 1) = e + 8 + 8 * N by omega, pow64_succ]
    grind

end VG.Proof.Rsa.X86_64.InvB

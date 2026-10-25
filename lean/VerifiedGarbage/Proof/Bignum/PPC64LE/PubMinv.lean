module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.PublicChecked
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Words

/-!
# The RSA public-key operation on PPC64LE: `-n⁻¹ mod 2³²`

`minv_ok`: Newton's iteration from `n`'s low word, four steps (3, 6, 12, 24
to 48 bits), negated and cut to 32 bits, what `MontMul.lean`'s `tail` takes
in `r12`.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Pub

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum.PPC64LE.PublicChecked
open VG.Proof.Bignum (newton_step emod_pow_weaken odd_sq)

/-- A Newton step computed on words is the step on integers, modulo `2⁶⁴`. -/
theorem newton_val (a x : BitVec 64) :
    (((x * (BitVec.ofNat 64 2 - a * x)).toNat : Int) - x.toNat * (2 - a.toNat * x.toNat)) % 2 ^ 64 = 0 := by
  have hx := x.isLt; have ha := a.isLt
  have hR : (x * (BitVec.ofNat 64 2 - a * x)).toNat = x.toNat * (BitVec.ofNat 64 2 - a * x).toNat % 2 ^ 64 :=
    BitVec.toNat_mul _ _
  have hD : (BitVec.ofNat 64 2 - a * x).toNat = (2 ^ 64 - a.toNat * x.toNat % 2 ^ 64 + 2) % 2 ^ 64 := by
    rw [BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_ofNat]
  generalize (BitVec.ofNat 64 2 - a * x).toNat = D at hR hD
  generalize (x * (BitVec.ofNat 64 2 - a * x)).toNat = R at hR ⊢
  generalize x.toNat = X at *
  generalize a.toNat = A at *
  have hDj : (D : Int) = 2 - (A * X : Nat) + 2 ^ 64 * (((D : Int) - 2 + (A * X : Nat)) / 2 ^ 64) := by
    have : ((A * X : Nat) : Int) % 2 ^ 64 = ((A * X % 2 ^ 64 : Nat) : Int) := by omega_arith
    omega_arith
  generalize (((D : Int) - 2 + (A * X : Nat)) / 2 ^ 64) = j at hDj
  have hXD : ((X * D : Nat) : Int) = 2 * X - (X : Int) * (A * X : Nat) + 2 ^ 64 * (X * j) := by
    rw [Int.natCast_mul, hDj, Int.mul_add, Int.mul_sub, Int.mul_left_comm (X : Int) (2 ^ 64) j]
    omega_arith
  have e : (X : Int) * (2 - (A : Int) * X) = 2 * X - (X : Int) * (A * X : Nat) := by
    rw [Int.mul_sub, Int.natCast_mul, Int.mul_comm (X : Int) 2]
  rw [e]
  have : ((X * D % 2 ^ 64 : Nat) : Int) = ((X * D : Nat) : Int) % 2 ^ 64 := by omega_arith
  rw [hR, this, hXD]
  omega_arith

/-- A step: `a x' ≡ 1 (mod 2^(2j))` from `a x ≡ 1 (mod 2^j)`, `a` in `r0`
and `x` in `r12`. -/
theorem nstep_ok (t : State) {j : Nat} (hj : 2 * j ≤ 64)
    (h : (((t.gpr .r0).toNat : Int) * (t.gpr .r12).toNat - 1) % (2 ^ j : Int) = 0) :
    WP isa (.block [.mul .r3 .r0 .r12, .li .r4 2, .sub .r3 .r4 .r3, .mul .r12 .r12 .r3]) t fun t' =>
      ((((t'.gpr .r0).toNat : Int) * (t'.gpr .r12).toNat - 1) % (2 ^ (2 * j) : Int) = 0 ∧
        t'.gpr .r0 = t.gpr .r0 ∧ t'.mem = t.mem) ∧ Keep [.r3, .r4, .r12] t t' := by
  refine WP.keep _ ?_ (by decide)
  prun
  exact newton_step hj h (newton_val _ _)

/-- `-x mod 2³²` is an inverse of `-a` when `x` is one of `a`. -/
theorem neg_inv32 {a x : Nat} (h : ((a : Int) * x - 1) % (2 ^ 32 : Int) = 0) :
    (a % 2 ^ 32 * ((2 ^ 64 - x % 2 ^ 64) % 2 ^ 64 % 2 ^ 32) + 1) % 2 ^ 32 = 0 := by
  generalize hy : (2 ^ 64 - x % 2 ^ 64) % 2 ^ 64 % 2 ^ 32 = y
  have hxy : (x + y) % 2 ^ 32 = 0 := by omega_arith
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
  have h1 : (2 ^ 32 : Int) ∣ (a : Int) * x - 1 := Int.dvd_of_emod_eq_zero h
  have h2 : (2 ^ 32 : Int) ∣ ((x + y : Nat) : Int) := by
    have := Int.dvd_of_emod_eq_zero (show ((x + y : Nat) : Int) % (2 ^ 32 : Int) = 0 by omega_arith)
    exact this
  have h3 : (2 ^ 32 : Int) ∣ ((a * y + 1 : Nat) : Int) := by
    have e : ((a * y + 1 : Nat) : Int) = (a : Int) * ((x + y : Nat) : Int) - ((a : Int) * x - 1) := by
      push_cast; grind
    rw [e]
    exact Int.dvd_sub (Int.dvd_mul_of_dvd_right h2) h1
  exact Nat.mod_eq_zero_of_dvd (Int.natCast_dvd_natCast.mp (by exact_mod_cast h3))

theorem minv_split : minv = ([.load .d .r0 .r10 0, .load .d .r12 .r10 0] : List Instr) ++
    (([.mul .r3 .r0 .r12, .li .r4 2, .sub .r3 .r4 .r3, .mul .r12 .r12 .r3] : List Instr) ++
    (([.mul .r3 .r0 .r12, .li .r4 2, .sub .r3 .r4 .r3, .mul .r12 .r12 .r3] : List Instr) ++
    (([.mul .r3 .r0 .r12, .li .r4 2, .sub .r3 .r4 .r3, .mul .r12 .r12 .r3] : List Instr) ++
    (([.mul .r3 .r0 .r12, .li .r4 2, .sub .r3 .r4 .r3, .mul .r12 .r12 .r3] : List Instr) ++
    ([.li .r3 0, .sub .r12 .r3 .r12, .lsl .r12 .r12 32, .lsr .d .r12 .r12 32] : List Instr))))) := rfl

/-- `minv`, `n` at `d` of the working space (`r10`), odd: `r12` is
`-n⁻¹ mod 2³²`. -/
theorem minv_ok {s : State} {B : Addr} {Z d : Nat} (hs : Scr s B Z) (h10 : s.gpr .r10 = off B d)
    (hd : d + 8 ≤ Z) (hodd : (word s.mem B d).toNat % 2 = 1) :
    WP isa (.block minv) s fun t =>
      ((t.gpr .r12).toNat < 2 ^ 32 ∧ (w32 s.mem B d * (t.gpr .r12).toNat + 1) % 2 ^ 32 = 0 ∧
        t.mem = s.mem) ∧ Keep [.r0, .r3, .r4, .r12] s t := by
  rw [minv_split, WP.block_append_iff]
  refine WP.mono (WP.keep [.r0, .r12] (Q := fun t => t.gpr .r0 = word s.mem B d ∧
    t.gpr .r12 = word s.mem B d ∧ t.mem = s.mem) (by prun [h10, BitVec.add_zero, hs.ld hd]) (by decide))
    fun t₀ ⟨⟨h0, h12, hm₀⟩, k₀⟩ => ?_
  have e₀ : (((t₀.gpr .r0).toNat : Int) * (t₀.gpr .r12).toNat - 1) % (2 ^ 3 : Int) = 0 := by
    rw [h0, h12]
    have h1 := odd_sq _ hodd
    have h2 : (((word s.mem B d).toNat : Int) * (word s.mem B d).toNat) % 8 = 1 := by
      simpa only [Int.natCast_mul, Int.natCast_emod, show ((8 : Nat) : Int) = 8 from rfl,
        show ((1 : Nat) : Int) = 1 from rfl] using congrArg (fun n : Nat => (n : Int)) h1
    show (((word s.mem B d).toNat : Int) * (word s.mem B d).toNat - 1) % 8 = 0
    omega_arith
  rw [WP.block_append_iff]
  refine WP.mono (nstep_ok t₀ (j := 3) (by decide) e₀) fun t₁ ⟨⟨e₁, hb₁, hm₁⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (nstep_ok t₁ (j := 6) (by decide) e₁) fun t₂ ⟨⟨e₂, hb₂, hm₂⟩, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (nstep_ok t₂ (j := 12) (by decide) e₂) fun t₃ ⟨⟨e₃, hb₃, hm₃⟩, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (nstep_ok t₃ (j := 24) (by decide) e₃) fun t₄ ⟨⟨e₄, hb₄, hm₄⟩, k₄⟩ => ?_
  have hb : t₄.gpr .r0 = word s.mem B d := hb₄.trans (hb₃.trans (hb₂.trans (hb₁.trans h0)))
  have kk := (((k₀.trans k₁).trans k₂).trans k₃).trans k₄
  rw [hb] at e₄
  refine WP.mono (WP.keep [.r3, .r12] (Q := fun t =>
    t.gpr .r12 = ((0 - t₄.gpr .r12) <<< 32) >>> 32 ∧ t.mem = t₄.mem) (by prun; rfl) (by decide))
    fun t ⟨⟨h12', hm⟩, k⟩ => ⟨⟨?_, ?_, by rw [hm, hm₄, hm₃, hm₂, hm₁, hm₀]⟩, (kk.trans k).mono⟩
  · rw [h12', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have := ((0 - t₄.gpr .r12) <<< 32).isLt
    omega_arith
  · have hw : w32 s.mem B d = (word s.mem B d).toNat % 2 ^ 32 := by
      have h2 : w32 s.mem B d < 2 ^ 32 := (s.mem.readW (off B d) 32).isLt
      rw [word_eq_w32, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]
    have hv : (t.gpr .r12).toNat = (2 ^ 64 - (t₄.gpr .r12).toNat % 2 ^ 64) % 2 ^ 64 % 2 ^ 32 := by
      rw [h12', BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow,
        Nat.shiftLeft_eq, show (0 : BitVec 64).toNat = 0 from rfl]
      have := (t₄.gpr .r12).isLt
      omega_arith
    rw [hw, hv]
    exact neg_inv32 (emod_pow_weaken (by decide) e₄)

end VG.Proof.Bignum.PPC64LE.Pub

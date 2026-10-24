module

public import VerifiedGarbage.Impl.MillerRabin.PPC64LE.Search
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Words

/-!
# A prime search on PPC64LE: `−N⁻¹ mod 2⁶⁴`

`minv64_ok`: Newton's iteration from `N`'s low word, five steps (3, 6, 12,
24, 32 to 64 bits), negated into header word 7, and its low half in `r12`
for `montOp` (`r12_inv`).
-/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE.Search

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.Bignum.PPC64LE
open VG.Proof.Bignum (emod_pow_weaken odd_sq)

/-- `-x mod 2⁶⁴` is an inverse of `-a` when `x` is one of `a`. -/
theorem neg_inv64 {a x : Nat} (h : ((a : Int) * x - 1) % (2 ^ 64 : Int) = 0) :
    (a * ((2 ^ 64 - x % 2 ^ 64) % 2 ^ 64) + 1) % 2 ^ 64 = 0 := by
  generalize hy : (2 ^ 64 - x % 2 ^ 64) % 2 ^ 64 = y
  have h1 : (2 ^ 64 : Int) ∣ (a : Int) * x - 1 := Int.dvd_of_emod_eq_zero h
  have h2 : (2 ^ 64 : Int) ∣ ((x + y : Nat) : Int) :=
    Int.dvd_of_emod_eq_zero (show ((x + y : Nat) : Int) % (2 ^ 64 : Int) = 0 by omega)
  have h3 : (2 ^ 64 : Int) ∣ ((a * y + 1 : Nat) : Int) := by
    have e : ((a * y + 1 : Nat) : Int) = (a : Int) * ((x + y : Nat) : Int) - ((a : Int) * x - 1) := by
      push_cast; grind
    rw [e]
    exact Int.dvd_sub (Int.dvd_mul_of_dvd_right h2) h1
  exact Nat.mod_eq_zero_of_dvd (Int.natCast_dvd_natCast.mp (by exact_mod_cast h3))

/-- The low half of `-N⁻¹`, what `montOp` takes in `r12`. -/
theorem r12_inv {a : Nat} {v : BitVec 64} (h : (a * v.toNat + 1) % 2 ^ 64 = 0) :
    ((v <<< 32) >>> 32).toNat < 2 ^ 32 ∧ (a % 2 ^ 32 * ((v <<< 32) >>> 32).toNat + 1) % 2 ^ 32 = 0 := by
  have hv : ((v <<< 32) >>> 32).toNat = v.toNat % 2 ^ 32 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    have := v.isLt
    omega
  refine ⟨by rw [hv]; omega, ?_⟩
  have h32 : (a * v.toNat + 1) % 2 ^ 32 = 0 := by
    rw [← Nat.mod_mod_of_dvd _ (show 2 ^ 32 ∣ 2 ^ 64 by decide), h]
  rw [hv, Nat.add_mod, ← Nat.mul_mod, ← Nat.add_mod]
  exact h32

theorem minv64_split : minv64 = ([.load .d .r0 .r10 0, .load .d .r12 .r10 0] : List Instr) ++
    (([.mul .r3 .r0 .r12, .li .r4 2, .sub .r3 .r4 .r3, .mul .r12 .r12 .r3] : List Instr) ++
    (([.mul .r3 .r0 .r12, .li .r4 2, .sub .r3 .r4 .r3, .mul .r12 .r12 .r3] : List Instr) ++
    (([.mul .r3 .r0 .r12, .li .r4 2, .sub .r3 .r4 .r3, .mul .r12 .r12 .r3] : List Instr) ++
    (([.mul .r3 .r0 .r12, .li .r4 2, .sub .r3 .r4 .r3, .mul .r12 .r12 .r3] : List Instr) ++
    (([.mul .r3 .r0 .r12, .li .r4 2, .sub .r3 .r4 .r3, .mul .r12 .r12 .r3] : List Instr) ++
    ([.li .r3 0, .sub .r3 .r3 .r12, sth .r3 hMinv, .lsl .r12 .r3 32, .lsr .d .r12 .r12 32] : List Instr)))))) :=
  rfl

/-- `minv64`, `N` at `d` of the working space (`r10`), odd: `−N⁻¹ mod 2⁶⁴`
in header word 7, its low half in `r12`. -/
theorem minv64_ok {s : State} {B : Addr} {Z d : Nat} (hs : Scr s B Z) (h10 : s.gpr .r10 = off B d)
    (h31 : s.gpr .r31 = B) (hd : d + 8 ≤ Z) (hZ : 64 ≤ Z) (hodd : (word s.mem B d).toNat % 2 = 1) :
    WP isa (.block minv64) s fun t =>
      (∃ v : BitVec 64, t.mem = s.mem.writeW (B + BitVec.ofNat 64 56) v ∧
        ((word s.mem B d).toNat * v.toNat + 1) % 2 ^ 64 = 0 ∧ t.gpr .r12 = (v <<< 32) >>> 32) ∧
      Keep [.r0, .r3, .r4, .r12] s t := by
  rw [minv64_split, WP.block_append_iff]
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
    omega
  rw [WP.block_append_iff]
  refine WP.mono (Pub.nstep_ok t₀ (j := 3) (by decide) e₀) fun t₁ ⟨⟨e₁, hb₁, hm₁⟩, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.nstep_ok t₁ (j := 6) (by decide) e₁) fun t₂ ⟨⟨e₂, hb₂, hm₂⟩, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.nstep_ok t₂ (j := 12) (by decide) e₂) fun t₃ ⟨⟨e₃, hb₃, hm₃⟩, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.nstep_ok t₃ (j := 24) (by decide) e₃) fun t₄ ⟨⟨e₄, hb₄, hm₄⟩, k₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.nstep_ok t₄ (j := 32) (by decide) (emod_pow_weaken (by decide) e₄))
    fun t₅ ⟨⟨e₅, hb₅, hm₅⟩, k₅⟩ => ?_
  have hb : t₅.gpr .r0 = word s.mem B d := hb₅.trans (hb₄.trans (hb₃.trans (hb₂.trans (hb₁.trans h0))))
  have kk := ((((k₀.trans k₁).trans k₂).trans k₃).trans k₄).trans k₅
  rw [hb] at e₅
  have hm : t₅.mem = s.mem := by rw [hm₅, hm₄, hm₃, hm₂, hm₁, hm₀]
  have st : InRegions t₅.wr (B + BitVec.ofNat 64 56) 8 := by rw [kk.wr]; exact hs.st (d := 56) (by omega)
  refine WP.mono (WP.keep [.r3, .r12] (Q := fun t =>
    t.mem = s.mem.writeW (B + BitVec.ofNat 64 56) (0 - t₅.gpr .r12) ∧
      t.gpr .r12 = ((0 - t₅.gpr .r12) <<< 32) >>> 32) ?_ (by decide))
    fun t ⟨⟨tm, t12⟩, k⟩ => ⟨⟨_, tm, ?_, t12⟩, (kk.trans k).mono (by decide)⟩
  · simp only [sth, hMinv]
    prun [(kk.gpr .r31 (by decide)).trans h31, st, hm]
    exact ⟨rfl, rfl⟩
  · rw [BitVec.toNat_sub, show (0 : BitVec 64).toNat = 0 from rfl, Nat.add_zero]
    have := neg_inv64 e₅
    rwa [Nat.mod_eq_of_lt (BitVec.isLt _)] at this

end VG.Proof.MillerRabin.PPC64LE.Search

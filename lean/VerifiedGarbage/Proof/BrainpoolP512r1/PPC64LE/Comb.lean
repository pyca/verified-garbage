module

public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.TCombI
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.PPC64LEComb
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.LadPow
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP512r1
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Stages
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Lays
import VerifiedGarbage.Proof.BrainpoolP512r1.Comb7
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Weierstrass.Env
import VerifiedGarbage.Proof.Weierstrass.BytesLen
import VerifiedGarbage.Proof.BrainpoolP512r1.Comb7Shape
public import VerifiedGarbage.Proof.Framework.ConstMem

/-!
# brainpoolP512r1's seven-bit comb on PPC64LE

The configuration the proof of the comb with the addition inlined takes
(`ConfigI`, on the signature's layout: the ladder's `R`, `a`, `3b` and table
of bits, of all 512 bits, the entry in its `T`, the sum and `-y` in its `D`,
zero at `ZERO`), and the comb as the generator of the signature's and the
public key's stages (`GeneratorPost`), from the table's words in memory.
-/

@[expose] public section

namespace VG.Proof.BrainpoolP512r1.PPC64LE

open VG VG.PPC64LE VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Impl.BrainpoolP512r1
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE VG.Proof.Weierstrass.PPC64LE.Point
  VG.Proof.Weierstrass.PPC64LE.TComb VG.Proof.Ecdsa.PPC64LE
open Spec.Weierstrass

theorem comb_lad : LadLayI brainpoolp512r1Comb.L :=
  (ladLayI brainpoolp512r1_ok (gx := GX) (gy := GY) (by decide) (by decide) (by decide) (by decide)).with_nbits
    (by decide) (by decide) (by decide) (by decide)

theorem comb_layout : LayoutI brainpoolp512r1Comb where
  lad := comb_lad
  bitsE := by decide
  wx := by decide
  qT := rfl
  qy := rfl
  qz := rfl
  negD := rfl
  zeroLe := by decide
  zero4 := by decide
  zeroW := by decide
  apart := ⟨by decide, by decide⟩

set_option exponentiation.threshold 1024 in
theorem comb_config (hC : Law Spec.BrainpoolP512r1.curve) :
    ConfigI brainpoolp512r1Comb Spec.BrainpoolP512r1.curve comb7 comb7Start where
  layout := comb_layout
  fieldK := rfl
  fieldM := rfl
  modulus := modP brainpoolp512r1_ok
  odd := brainpoolp512r1_ok.p_odd
  unit := unitMod_pow_two brainpoolp512r1_ok.p_odd _
  tables := Proof.BrainpoolP512r1.combOk7 hC
  one_lt := Nat.mod_lt _ (by decide)
  one := toM_one (unitMod_pow_two brainpoolp512r1_ok.p_odd _)
  startX := rfl
  startY := rfl
  w1 := by decide
  w9 := by decide
  J1 := by decide
  J15 := by decide
  startBits := by decide
  coverBits := by decide
  bitsOff := by decide
  row := by decide
  n18 := by decide

set_option exponentiation.threshold 1024 in
theorem comb_words_eq : tableWords brainpoolp512r1Comb Spec.BrainpoolP512r1.curve comb7 = brainpoolp512r1CombWords := by
  unfold brainpoolp512r1CombWords
  rfl

set_option exponentiation.threshold 1024 in
theorem comb_words_length : brainpoolp512r1CombWords.length = 75776 := by
  unfold brainpoolp512r1CombWords
  rw [tcombWords_length (H := 64) Proof.BrainpoolP512r1.comb7_length Proof.BrainpoolP512r1.comb7_rows]

theorem comb_writes_cover : ∀ w ∈ ladWx brainpoolp512r1Comb.L, ∃ v ∈ ladWp (ladderAt brainpoolp512r1 GX GY) ++ genX brainpoolp512r1,
    v.1 ≤ w.1 ∧ w.1 + w.2 ≤ v.1 + v.2 := by decide

set_option exponentiation.threshold 1024 in
/-- The comb as the generator of the stages after the setup and the
tables, from the table's words at `T`, apart from the working space. -/
theorem comb_generator_ok (hC : Law Spec.BrainpoolP512r1.curve) {A : Args} {s₀ : State} {base : Addr} {F : BitVec 64}
    {s : State} (S : St₁ brainpoolp512r1 A s₀ base F s) {T : Addr} (ht : TableMem s T brainpoolp512r1CombWords)
    (sym : s.syms brainpoolp512r1Comb.tsym = T) (hd : Region.Disjoint ⟨T, 8 * brainpoolp512r1CombWords.length⟩ ⟨base, 8192⟩) :
    WP isa mulGeneratorBrainpoolP512r1 s (GeneratorPost brainpoolp512r1 base (kv brainpoolp512r1 A s₀) (G Spec.BrainpoolP512r1.curve) s) := by
  have F' := S.fixed
  have ht' : TableMem s T (tableWords brainpoolp512r1Comb Spec.BrainpoolP512r1.curve comb7) := by
    rw [comb_words_eq]; exact ht
  have hd' : Region.Disjoint ⟨T, 8 * (tableWords brainpoolp512r1Comb Spec.BrainpoolP512r1.curve comb7).length⟩ ⟨base, 8192⟩ := by
    rw [comb_words_eq]; exact hd
  refine WP.mono (combI_ok brainpoolp512r1Comb (comb_config hC) hC brainpoolp512r1_ok.onG S.ws ht' sym hd'
    (Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (ofBytes_bytesAt_lt _ _ _))
      (Nat.pow_le_pow_right (by decide) (by decide))) F'.zero S.t₀ F'.ap F'.b3p)
    fun t ⟨keep, unch, lt, rep⟩ => ⟨keep, unch.cover comb_writes_cover, lt, rep⟩

/-- The memory of the witnesses with the table: the table at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the
table). -/
@[irreducible] def combSatMem : Mem := constMem 0x100000 brainpoolp512r1CombWords

theorem combSatMem_held : ∀ i < brainpoolp512r1CombWords.length,
    combSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = brainpoolp512r1CombWords.getD i 0 := by
  unfold combSatMem
  exact constMem_held _ _ (by rw [comb_words_length]; omega)

end VG.Proof.BrainpoolP512r1.PPC64LE

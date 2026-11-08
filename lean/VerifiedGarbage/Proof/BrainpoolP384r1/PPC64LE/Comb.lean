module

public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.TComb
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.PPC64LEComb
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.LadPow
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.BrainpoolP384r1
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Stages
import VerifiedGarbage.Proof.BrainpoolP384r1.Comb7
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Weierstrass.Env
import VerifiedGarbage.Proof.Weierstrass.BytesLen
import VerifiedGarbage.Proof.BrainpoolP384r1.Comb7Shape
public import VerifiedGarbage.Proof.Framework.ConstMem

/-!
# brainpoolBrainpoolP384r1r1's seven-bit comb on PPC64LE

The configuration the comb's proof takes (on the signature's layout: the
ladder's `R`, `a`, `3b` and table of bits, zero at `ZERO`, `-y` in the
ladder's `T`), and the comb as the generator of the signature's and the
public key's stages (`GeneratorPost`), from the table's words in memory.
-/

@[expose] public section

namespace VG.Proof.BrainpoolP384r1.PPC64LE

open VG VG.PPC64LE VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Impl.BrainpoolP384r1
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE VG.Proof.Weierstrass.PPC64LE.Point
  VG.Proof.Weierstrass.PPC64LE.TComb VG.Proof.Ecdsa.PPC64LE
open Spec.Weierstrass

theorem comb_layout : Layout brainpoolp384r1Comb where
  point := ladPtLay brainpoolp384r1_ok (by decide) (by decide) (gx := GX) (gy := GY) (by decide) (by decide)
  low := by decide
  al := by decide
  negApart := by decide
  zeroApart := by decide

set_option exponentiation.threshold 512 in
theorem comb_config (hC : Law Spec.BrainpoolP384r1.curve) :
    Config brainpoolp384r1Comb Spec.BrainpoolP384r1.curve comb7 comb7Start where
  layout := comb_layout
  fieldK := rfl
  fieldM := rfl
  modulus := modP brainpoolp384r1_ok
  odd := brainpoolp384r1_ok.p_odd
  unit := unitMod_pow_two brainpoolp384r1_ok.p_odd _
  tables := Proof.BrainpoolP384r1.combOk7 hC
  one_lt := Nat.mod_lt _ (by decide)
  one := toM_one (unitMod_pow_two brainpoolp384r1_ok.p_odd _)
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

set_option exponentiation.threshold 512 in
theorem comb_words_eq : tableWords brainpoolp384r1Comb Spec.BrainpoolP384r1.curve comb7 = brainpoolp384r1CombWords := by
  unfold brainpoolp384r1CombWords
  rfl

set_option exponentiation.threshold 512 in
theorem comb_words_length : brainpoolp384r1CombWords.length = 42240 := by
  unfold brainpoolp384r1CombWords
  rw [tcombWords_length (H := 64) Proof.BrainpoolP384r1.comb7_length Proof.BrainpoolP384r1.comb7_rows]

theorem comb_writes_cover : ∀ w ∈ writes brainpoolp384r1Comb, ∃ v ∈ ladWp (ladderAt brainpoolp384r1 GX GY) ++ genX brainpoolp384r1,
    v.1 ≤ w.1 ∧ w.1 + w.2 ≤ v.1 + v.2 := by decide

set_option exponentiation.threshold 512 in
/-- The comb as the generator of the stages after the setup and the
tables, from the table's words at `T`, apart from the working space. -/
theorem comb_generator_ok (hC : Law Spec.BrainpoolP384r1.curve) {A : Args} {s₀ : State} {base : Addr} {F : BitVec 64}
    {s : State} (S : St₁ brainpoolp384r1 A s₀ base F s) {T : Addr} (ht : TableMem s T brainpoolp384r1CombWords)
    (sym : s.syms brainpoolp384r1Comb.tsym = T) (hd : Region.Disjoint ⟨T, 8 * brainpoolp384r1CombWords.length⟩ ⟨base, 8192⟩) :
    WP isa mulGeneratorBrainpoolP384r1 s (GeneratorPost brainpoolp384r1 base (kv brainpoolp384r1 A s₀) (G Spec.BrainpoolP384r1.curve) s) := by
  have F' := S.fixed
  have ht' : TableMem s T (tableWords brainpoolp384r1Comb Spec.BrainpoolP384r1.curve comb7) := by
    rw [comb_words_eq]; exact ht
  have hd' : Region.Disjoint ⟨T, 8 * (tableWords brainpoolp384r1Comb Spec.BrainpoolP384r1.curve comb7).length⟩ ⟨base, 8192⟩ := by
    rw [comb_words_eq]; exact hd
  refine WP.mono (comb_ok brainpoolp384r1Comb (comb_config hC) hC brainpoolp384r1_ok.onG S.ws ht' sym hd'
    (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (ofBytes_bytesAt_lt _ _ _)) F'.zero S.t₀ F'.ap F'.b3p)
    fun t ⟨keep, unch, lt, rep⟩ => ⟨keep, unch.cover comb_writes_cover, lt, rep⟩

/-- The memory of the witnesses with the table: the table at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the
table). -/
@[irreducible] def combSatMem : Mem := constMem 0x100000 brainpoolp384r1CombWords

theorem combSatMem_held : ∀ i < brainpoolp384r1CombWords.length,
    combSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = brainpoolp384r1CombWords.getD i 0 := by
  unfold combSatMem
  exact constMem_held _ _ (by rw [comb_words_length]; omega)

end VG.Proof.BrainpoolP384r1.PPC64LE

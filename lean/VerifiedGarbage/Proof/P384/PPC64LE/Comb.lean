module

public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.TComb
public import VerifiedGarbage.Impl.Ecdsa.P384.PPC64LEComb
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.LadPow
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P384
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Stages
import VerifiedGarbage.Proof.P384.Comb7
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Weierstrass.Env
import VerifiedGarbage.Proof.Weierstrass.BytesLen
import VerifiedGarbage.Proof.P384.Comb7Shape
public import VerifiedGarbage.Proof.Framework.ConstMem

/-!
# P-384's seven-bit comb on PPC64LE

The configuration the comb's proof takes (on the signature's layout: the
ladder's `R`, `a`, `3b` and table of bits, zero at `ZERO`, `-y` in the
ladder's `T`), and the comb as the generator of the signature's and the
public key's stages (`GeneratorPost`), from the table's words in memory.
-/

@[expose] public section

namespace VG.Proof.P384.PPC64LE

open VG VG.PPC64LE VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Impl.P384
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE VG.Proof.Weierstrass.PPC64LE.Point
  VG.Proof.Weierstrass.PPC64LE.TComb VG.Proof.Ecdsa.PPC64LE
open Spec.Weierstrass

theorem comb_layout : Layout p384Comb where
  point := ladPtLay p384_ok (by decide) (by decide) (gx := GX) (gy := GY) (by decide) (by decide)
  low := by decide
  al := by decide
  negApart := by decide
  zeroApart := by decide

set_option exponentiation.threshold 512 in
theorem comb_config (hC : Law Spec.P384.curve) :
    Config p384Comb Spec.P384.curve p384Comb7 p384Comb7Start where
  layout := comb_layout
  fieldK := rfl
  fieldM := rfl
  modulus := modP p384_ok
  odd := p384_ok.p_odd
  unit := unitMod_pow_two p384_ok.p_odd _
  tables := Proof.P384.combOk7 hC
  one_lt := Nat.mod_lt _ (by decide)
  one := toM_one (unitMod_pow_two p384_ok.p_odd _)
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
theorem comb_words_eq : tableWords p384Comb Spec.P384.curve p384Comb7 = p384CombWords := by
  unfold p384CombWords
  rfl

set_option exponentiation.threshold 512 in
theorem comb_words_length : p384CombWords.length = 42240 := by
  unfold p384CombWords
  rw [tcombWords_length (H := 64) Proof.P384.p384Comb7_length Proof.P384.p384Comb7_rows]

theorem comb_writes_cover : ∀ w ∈ writes p384Comb, ∃ v ∈ ladWp (ladderAt p384 GX GY) ++ genX p384,
    v.1 ≤ w.1 ∧ w.1 + w.2 ≤ v.1 + v.2 := by decide

set_option exponentiation.threshold 512 in
/-- The comb as the generator of the stages after the setup and the
tables, from the table's words at `T`, apart from the working space. -/
theorem comb_generator_ok (hC : Law Spec.P384.curve) {A : Args} {s₀ : State} {base : Addr} {F : BitVec 64}
    {s : State} (S : St₁ p384 A s₀ base F s) {T : Addr} (ht : TableMem s T p384CombWords)
    (sym : s.syms p384Comb.tsym = T) (hd : Region.Disjoint ⟨T, 8 * p384CombWords.length⟩ ⟨base, 8192⟩) :
    WP isa mulGeneratorP384 s (GeneratorPost p384 base (kv p384 A s₀) (G Spec.P384.curve) s) := by
  have F' := S.fixed
  have ht' : TableMem s T (tableWords p384Comb Spec.P384.curve p384Comb7) := by
    rw [comb_words_eq]; exact ht
  have hd' : Region.Disjoint ⟨T, 8 * (tableWords p384Comb Spec.P384.curve p384Comb7).length⟩ ⟨base, 8192⟩ := by
    rw [comb_words_eq]; exact hd
  refine WP.mono (comb_ok p384Comb (comb_config hC) hC p384_ok.onG S.ws ht' sym hd'
    (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (ofBytes_bytesAt_lt _ _ _)) F'.zero S.t₀ F'.ap F'.b3p)
    fun t ⟨keep, unch, lt, rep⟩ => ⟨keep, unch.cover comb_writes_cover, lt, rep⟩

/-- The memory of the witnesses with the table: the table at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the
table). -/
@[irreducible] def combSatMem : Mem := constMem 0x100000 p384CombWords

theorem combSatMem_held : ∀ i < p384CombWords.length,
    combSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = p384CombWords.getD i 0 := by
  unfold combSatMem
  exact constMem_held _ _ (by rw [comb_words_length]; omega)

end VG.Proof.P384.PPC64LE

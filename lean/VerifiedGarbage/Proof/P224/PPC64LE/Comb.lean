module

public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.TComb
public import VerifiedGarbage.Impl.Ecdsa.P224.PPC64LEComb
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.LadPow
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P224
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Stages
import VerifiedGarbage.Proof.P224.Comb7
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Weierstrass.Env
import VerifiedGarbage.Proof.Weierstrass.BytesLen
import VerifiedGarbage.Proof.P224.Comb7Shape
public import VerifiedGarbage.Proof.Framework.ConstMem

/-!
# P-224's seven-bit comb on PPC64LE

The configuration the comb's proof takes (on the signature's layout: the
ladder's `R`, `a`, `3b` and table of bits, zero at `ZERO`, `-y` in the
ladder's `T`), and the comb as the generator of the signature's and the
public key's stages (`GeneratorPost`), from the table's words in memory.
-/

@[expose] public section

namespace VG.Proof.P224.PPC64LE

open VG VG.PPC64LE VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Impl.P224
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE VG.Proof.Weierstrass.PPC64LE.Point
  VG.Proof.Weierstrass.PPC64LE.TComb VG.Proof.Ecdsa.PPC64LE
open Spec.Weierstrass

theorem comb_layout : Layout p224Comb where
  point := ladPtLay p224_ok (by decide) (by decide) (gx := GX) (gy := GY) (by decide) (by decide)
  low := by decide
  al := by decide
  negApart := by decide
  zeroApart := by decide

theorem comb_config (hC : Law Spec.P224.curve) :
    Config p224Comb Spec.P224.curve p224Comb7x32 p224Comb7Start32 where
  layout := comb_layout
  fieldK := rfl
  fieldM := rfl
  modulus := modP p224_ok
  odd := p224_ok.p_odd
  unit := unitMod_pow_two p224_ok.p_odd _
  tables := Proof.P224.combOk7x32 hC
  one_lt := Nat.mod_lt _ (by decide)
  one := toM_one (unitMod_pow_two p224_ok.p_odd _)
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

theorem comb_words_eq : tableWords p224Comb Spec.P224.curve p224Comb7x32 = p224CombWords := by
  unfold p224CombWords
  rfl

theorem p224Comb7x32_length : p224Comb7x32.length = 32 := by
  unfold p224Comb7x32; rw [List.length_take, Proof.P224.p224Comb7_length]; rfl

theorem p224Comb7x32_rows : ∀ j < 32, (p224Comb7x32.getD j []).length = 64 := fun j hj => by
  unfold p224Comb7x32
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj, ← List.getD_eq_getElem?_getD]
  exact Proof.P224.p224Comb7_rows j (by omega)

theorem comb_words_length : p224CombWords.length = 16384 := by
  unfold p224CombWords
  rw [tcombWords_length (H := 64) p224Comb7x32_length p224Comb7x32_rows]

theorem comb_writes_cover : ∀ w ∈ writes p224Comb, ∃ v ∈ ladWp (ladderAt p224 GX GY) ++ genX p224,
    v.1 ≤ w.1 ∧ w.1 + w.2 ≤ v.1 + v.2 := by decide

/-- The comb as the generator of the stages after the setup and the
tables, from the table's words at `T`, apart from the working space. -/
theorem comb_generator_ok (hC : Law Spec.P224.curve) {A : Args} {s₀ : State} {base : Addr} {F : BitVec 64}
    {s : State} (S : St₁ p224 A s₀ base F s) {T : Addr} (ht : TableMem s T p224CombWords)
    (sym : s.syms p224Comb.tsym = T) (hd : Region.Disjoint ⟨T, 8 * p224CombWords.length⟩ ⟨base, 8192⟩) :
    WP isa mulGeneratorP224 s (GeneratorPost p224 base (kv p224 A s₀) (G Spec.P224.curve) s) := by
  have F' := S.fixed
  have ht' : TableMem s T (tableWords p224Comb Spec.P224.curve p224Comb7x32) := by
    rw [comb_words_eq]; exact ht
  have hd' : Region.Disjoint ⟨T, 8 * (tableWords p224Comb Spec.P224.curve p224Comb7x32).length⟩ ⟨base, 8192⟩ := by
    rw [comb_words_eq]; exact hd
  refine WP.mono (comb_ok p224Comb (comb_config hC) hC p224_ok.onG S.ws ht' sym hd'
    (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (ofBytes_bytesAt_lt _ _ _)) F'.zero
    (fun i hi => S.t₀ i (Nat.lt_of_lt_of_le hi (by decide))) F'.ap F'.b3p)
    fun t ⟨keep, unch, lt, rep⟩ => ⟨keep, unch.cover comb_writes_cover, lt, rep⟩

/-- The memory of the witnesses with the table: the table at `0x100000`
(irreducible: unfolding it in a definitional check would evaluate the
table). -/
@[irreducible] def combSatMem : Mem := constMem 0x100000 p224CombWords

theorem combSatMem_held : ∀ i < p224CombWords.length,
    combSatMem.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = p224CombWords.getD i 0 := by
  unfold combSatMem
  exact constMem_held _ _ (by rw [comb_words_length]; omega)

end VG.Proof.P224.PPC64LE

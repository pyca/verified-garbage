import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Gh
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Cvt
import VerifiedGarbage.Spec.Gcm.Precomputed

/-!
# AES-GCM's short path on x86-64: the table of powers, without the field

Untrusted: everything here is checked by Lean. The table of powers of the
hash subkey that `powers` writes (`TabOk`), as blocks: `H'ᵏ = Hᵏ · x⁻¹`
(`hInvF`). What the short path's proofs need from the algebra of the field,
`powers`' table and `GHASH` of `G` from it (`ShortFacts`), is proved in the
two modules that import that algebra (`Pow.lean`, `Field.lean`) and passed
to the others, which so need not import it.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short
open VG.Proof.AesGcm.X86_64
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Proof.Gcm.X86_64.Pclmul (reduceB)
open VG.Proof.Gcm.X86_64.StitchZP (hInvF)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom mul hpow ctxH)

/-- The table of powers at `T` for `n` groups of four: lane `l` of group `j`
is `H'^(4 j + 4 - l)`. -/
def TabOk (m : Mem) (T : Addr) (H : Block) (n : Nat) : Prop :=
  ∀ j < n, ∀ l < 4, m.readW (T + BitVec.ofNat 64 (64 * j + 16 * l)) 128 = hInvF (hpow H (4 * j + 4 - l))

theorem TabOk.keep {m m' : Mem} {T : Addr} {H : Block} {g : Nat} (h : TabOk m T H g) (hg : g ≤ 8)
    {rs : List Region} (f : Frame rs m m') (hd : ∀ r ∈ rs, (⟨T, 512⟩ : Region).Disjoint r) : TabOk m' T H g :=
  fun j hj l hl => by
    rw [f.readW (r := ⟨T + BitVec.ofNat 64 (64 * j + 16 * l), 16⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base T (by omega))) (by decide)]
    exact h j hj l hl

/-- `mul`'s fold, for a first factor none of whose bits is set: the product
stays 0. -/
theorem foldl_fst_keep (c : Nat → Bool) (hc : ∀ i, c i = false) (f : Block × Block → Nat → Block)
    (l : List Nat) (z v : Block) :
    (l.foldl (fun zv i => (if c i = true then zv.1 ^^^ zv.2 else zv.1, f zv i)) (z, v)).1 = z := by
  induction l generalizing v with
  | nil => rfl
  | cons i l ih => simp only [List.foldl_cons, hc i, Bool.false_eq_true, ↓reduceIte]; exact ih _

theorem mul_zero_left (h : Block) : mul 0 h = 0 := by
  unfold mul
  generalize List.range 128 = l
  exact foldl_fst_keep (fun i => (0 : Block).getMsbD i) (fun i => by simp [BitVec.getMsbD]) _ l 0 h

/-- Zero blocks first add nothing to `GHASH` from 0. -/
theorem ghashFrom_zeros (H : Block) (k : Nat) (xs : List Block) :
    ghashFrom H 0 (List.replicate k 0 ++ xs) = ghashFrom H 0 xs := by
  rw [Proof.Gcm.ghashFrom_append]
  congr 1
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ', Proof.Gcm.ghashFrom_append, ih]
    simp only [ghashFrom, List.foldl_cons, List.foldl_nil, BitVec.xor_self]
    exact mul_zero_left H

/-- `T` multiplies as `H' = H · x⁻¹`: one product with it, reduced, is a
step of `GHASH`. -/
def IsH1 (H T : Block) : Prop :=
  ∀ Y X : Block, VG.Proof.Gcm.X86_64.Pclmul.reduce (VG.Proof.Gcm.X86_64.Pclmul.Prod.zero.acc (Y ^^^ X) T) =
    ghashFrom H Y [X]

/-- `T₂` multiplies as `H'²` and `T₁` as `H'`: two products, added and
reduced once, are two steps of `GHASH`. -/
def IsH2 (H T₁ T₂ : Block) : Prop :=
  ∀ Y X₁ X₂ : Block, VG.Proof.Gcm.X86_64.Pclmul.reduce
    ((VG.Proof.Gcm.X86_64.Pclmul.Prod.zero.acc (Y ^^^ X₁) T₂).acc X₂ T₁) = ghashFrom H Y [X₁, X₂]

/-- What the short path's proofs need from the algebra of the field: the
table `powers` writes (`powers_ok`), the registers its first block leaves
(`powHead_ok`), `GHASH` of `G` from the table (`gacc_ghash`), and the
powers `H'` and `H'²` that the end of a long `seal` computes (`finPow_facts`). -/
structure ShortFacts : Prop where
  powers : ∀ {Ctx W SP : Addr} {g : Nat} (s : State), Env Ctx (W + BitVec.ofNat 64 16) W SP s →
    s.mem.readW (W + BitVec.ofNat 64 288) 64 = BitVec.ofNat 64 (4 * g) → 1 ≤ g → g ≤ 8 →
    WP isa Impl.AesGcm.X86_64.Short.powers s fun t =>
      TabOk t.mem (W + BitVec.ofNat 64 1536) (ctxH s.mem Ctx) g ∧
      Frame [⟨W + BitVec.ofNat 64 1536, 512⟩] s.mem t.mem ∧
      (∀ l < 4, t.zlane .xmm0 l = revMask) ∧ (∀ l < 4, t.zlane .xmm1 l = poly) ∧
      (∀ r, r ≠ .rax → r ≠ .r11 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr
  powHead : ∀ {Ctx W SP : Addr} {g : Nat} (s : State), Env Ctx (W + BitVec.ofNat 64 16) W SP s →
    s.mem.readW (W + BitVec.ofNat 64 288) 64 = BitVec.ofNat 64 (4 * g) →
    WP isa (.block (powSse ++ ptr .r11 .r15 tbO ++ pow4 ++ [.mov .rax (.mem (at_ .r15 mpO))])) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 (4 * g) ∧ t.gpr .r11 = W + BitVec.ofNat 64 1536
  ghash : ∀ {m : Mem} {G T : Addr} {H : Block} {g : Nat}, TabOk m T H g →
    (reduceB (gacc m G T g 0 g) ^^^ reduceB (gacc m G T g 2 g)) ^^^
      (reduceB (gacc m G T g 1 g) ^^^ reduceB (gacc m G T g 3 g)) = ghashFrom H 0 (blocksAt m G (4 * g))
  finPow : ∀ (s : State), InRegions (s.rd ++ s.wr) (s.gpr .r13 + BitVec.ofInt 64 ((240 : Nat) : Int)) 16 →
    WP isa (.block Impl.AesGcm.X86_64.Short.finPow) s fun t =>
      t.xmm .xmm0 = revMask ∧ t.xmm .xmm1 = poly ∧
      IsH1 (blockAt s.mem (s.gpr .r13 + BitVec.ofInt 64 ((240 : Nat) : Int))) (t.xmm .xmm3) ∧
      IsH2 (blockAt s.mem (s.gpr .r13 + BitVec.ofInt 64 ((240 : Nat) : Int))) (t.xmm .xmm3) (t.xmm .xmm6) ∧
      VG.Proof.Gcm.X86_64.Pclmul.Only
        [.xmm0, .xmm1, .xmm3, .xmm6, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm12, .xmm13, .xmm14] s t

end VG.Proof.AesGcm.X86_64.Short

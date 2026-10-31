module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Ghash
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Ops

/-!
# AES-GCM on AArch64: `vg_ghash_aes`, `vg_ghash_prepared8_aes` and `vg_ghash_with_powers_aes`

Untrusted: everything here is checked by Lean. The `GhashImpl` of
`vg_ghash_aes` and the `GhashPreparedImpl` of `vg_ghash_prepared8_aes`, from
their proofs, apart from `Callee.lean`: only the variants
need it, and its proof imports the algebra of `Proof/Gcm/Poly.lean`, which
the rest of the AES-GCM proofs then need not import. So does `gh8Ok`, which
the interleaved loops' proofs (`Proof/Gcm/AArch64/Stitch/`) take as a
hypothesis: what `ghPart` computes (`gh8V`) is GHASH of its eight blocks, in
the ring `Q` of `Proof/Gcm/Poly.lean`. Karatsuba's products (`kadd`) add
`x · a · s` once `fix`ed (`val_fix_kadd`): `mid` has the two products
`vg_ghash_aes` adds to it, and the other two each twice. The power `H'ᵏ` with
its halves swapped is of the class of `x⁻¹ · Hᵏ` (`x_φ_pp`).
-/

@[expose] public section

local notation "vdword" => VG.Proof.Gcm.Clmul.vdword
local notation "ofVDwords" => VG.Proof.Gcm.Clmul.ofVDwords

namespace VG.Proof.AesGcm.AArch64

open VG VG.AArch64

/-- `vg_ghash_prepared8_aes`, with PMULL. -/
def GhashPreparedImpl.aes : GhashPreparedImpl where
  fn := ⟨"vg_ghash_prepared8_aes", Impl.Gcm.AArch64.Pmull.ghashP⟩
  noFrames := by decide +kernel
  ok := Proof.Gcm.AArch64.Pmull.ghashP_correct
  ct := Proof.Gcm.AArch64.Pmull.ghashP_ct
  keepsV := by decide +kernel

/-- `vg_ghash_with_powers_aes`, with PMULL. -/
def GhashWithImpl.aes : GhashWithImpl where
  fn := ⟨"vg_ghash_with_powers_aes", Impl.Gcm.AArch64.Pmull.ghashW⟩
  noFrames := by decide +kernel
  ok := Proof.Gcm.AArch64.Pmull.ghashW_correct
  ct := Proof.Gcm.AArch64.Pmull.ghashW_ct
  keepsV := by decide +kernel

def GhashStoreImpl.aes : GhashStoreImpl where
  fn := ⟨"vg_ghash_store_powers_aes", Impl.Gcm.AArch64.Pmull.ghashS⟩
  noFrames := by decide +kernel
  ok := Proof.Gcm.AArch64.Pmull.ghashS_correct
  ct := Proof.Gcm.AArch64.Pmull.ghashS_ct
  keepsV := by decide +kernel

namespace GhashImpl

/-- `vg_ghash_aes`, with PMULL (which Rust's `aes` feature stands for, with
the AES instructions). -/
def aes : GhashImpl where
  fn := ⟨"vg_ghash_aes", Impl.Gcm.AArch64.Pmull.ghash⟩
  noFrames := by decide +kernel
  ok := Proof.Gcm.AArch64.Pmull.ghash_correct
  ct := Proof.Gcm.AArch64.Pmull.ghash_ct
  keepsV := by decide +kernel
  suffix := "_aes"
  features := ["aes"]
  pmull := true
  prepared := some .aes
  withPowers := some .aes
  storePowers := some .aes

end GhashImpl

/-- The implementation of `vg_ghash` named `n`. -/
def GhashName.impl : GhashName → GhashImpl
  | .scalar => .scalar
  | .aes => .aes

/-- The implementations a variant calls. -/
def GcmVariant.impl (v : GcmVariant) : GcmImpl := ⟨v.ctr, v.key, v.gh.impl, v.stitch⟩

end VG.Proof.AesGcm.AArch64

namespace VG.Proof.Gcm.AArch64.Stitch

open VG VG.AArch64 VG.Proof.Gcm.Poly VG.Proof.Gcm.AArch64.Pmull
open VG.Impl.Gcm.AArch64.Stitch (pa pb pk pl)

/-- `kadd` adds `x · a · s` (`s` as loaded) to the product. -/
theorem val_fix_kadd (p : Prod) (a s : BitVec 128) :
    (fix (kadd p a s (kkey s))).val = (fix p).val + x * ρ a * ρ s := by
  simp only [fix, kadd, kkey, Prod.val, φ_xor, φ_polyMul, ψ_xor, ρ]
  linear_combination (x ^ 65 * (ψ (vdword a 0) * ψ (vdword s 0) + ψ (vdword a 1) * ψ (vdword s 1))) *
    two_Q

theorem vdword_ofVDwords_0 (a b : BitVec 64) : vdword (ofVDwords a b) 0 = a := vdword_append_0 _ _
theorem vdword_ofVDwords_1 (a b : BitVec 64) : vdword (ofVDwords a b) 1 = b := vdword_append_1 _ _

theorem val_fix_zero : (fix ⟨0#128, 0#128, 0#128⟩).val = 0 := by
  simp only [fix, Prod.val, BitVec.xor_zero, φ_zero', mul_zero, add_zero]

/-- A pair's products, from the keys of the table. -/
theorem val_kpair (pv : Prod) (H : Spec.Gcm.Block) (a₁ a₂ : BitVec 128) (k l : Nat) :
    (fix (kpair pv a₁ (ext8 (pp H k) (pp H k)) a₂ (ext8 (pp H l) (pp H l)) (kpack H k l))).val =
      (fix pv).val + ρ a₁ * φ H ^ k + ρ a₂ * φ H ^ l := by
  rw [kpair, kpack, vdword_ofVDwords_0, vdword_ofVDwords_1, val_fix_kadd, val_fix_kadd, ρ_ext8_self,
    ρ_ext8_self, ← x_φ_pp H k, ← x_φ_pp H l]
  ring

theorem gh8Ok : Gh8Ok := by
  intro H y b
  apply ρ_inj
  simp only [gh8V, pk, pl, pa, pb, show (0 : Nat) = 3 ↔ False by decide, show (1 : Nat) = 3 ↔ False by decide,
    show (2 : Nat) = 3 ↔ False by decide, ite_false, ite_true, BitVec.ofNat_eq_ofNat, BitVec.xor_zero]
  rw [ρ_reduce, val_kpair, val_kpair, val_kpair, val_kpair, val_fix_zero, ρ_ext8_self, ρ_xor]
  simp only [ρ_ext8_self, Spec.Gcm.ghashFrom, List.range_succ, List.range_zero, List.map_append, List.map_cons,
    List.map_nil, List.nil_append, List.foldl_append, List.foldl_cons, List.foldl_nil, φ_mul, φ_xor]
  ring

end VG.Proof.Gcm.AArch64.Stitch

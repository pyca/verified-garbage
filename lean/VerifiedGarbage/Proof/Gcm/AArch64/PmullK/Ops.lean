module

public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.Ops

/-!
# GHASH with PMULL and EOR3: Karatsuba's products, as bits

`Impl.Gcm.AArch64.PmullK` collects, of a block `a` as loaded and a key `s`
(a power with its halves swapped, as `sReg` holds it), `a₀ · s₀` in `hi`,
`a₁ · s₁` in `lo` and `(a₀ + a₁) · (s₀ + s₁)` in `mid` (`kadd`), and reduces
`hi : mid + hi + lo : lo` (`fix`). Their classes are in `Ghash.lean`
(`val_fix_kadd`).
-/

@[expose] public section

namespace VG.Proof.Gcm.AArch64.PmullK

open VG.AArch64
open VG.Proof.Gcm.AArch64.Pmull

/-- The key of Karatsuba's product by `s`: the sum of its halves. -/
def kkey (s : BitVec 128) : BitVec 64 := vdword s 0 ^^^ vdword s 1

/-- The products of the block `a` and the key `s`, with `kv` the key's
`kkey`, added to `p`. -/
def kadd (p : Prod) (a s : BitVec 128) (kv : BitVec 64) : Prod :=
  ⟨p.lo ^^^ polyMul (vdword a 1) (vdword s 1),
   p.mid ^^^ polyMul (vdword a 0 ^^^ vdword a 1) kv,
   p.hi ^^^ polyMul (vdword a 0) (vdword s 0)⟩

/-- The product `p` collects, with `hi` and `lo` added to its `mid`. -/
def fix (p : Prod) : Prod := ⟨p.lo, p.mid ^^^ p.hi ^^^ p.lo, p.hi⟩

theorem fix_zero : fix Prod.zero = Prod.zero := by
  simp only [fix, Prod.zero, BitVec.ofNat_eq_ofNat, BitVec.xor_zero]

end VG.Proof.Gcm.AArch64.PmullK

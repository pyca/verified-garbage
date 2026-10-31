module

public import VerifiedGarbage.Proof.Gcm.AArch64.Pmull.PrepKey
public import VerifiedGarbage.Impl.Gcm.AArch64.Stitch

/-!
# Interleaved counter mode and GHASH on AArch64: GHASH's values

Untrusted: everything here is checked by Lean. What `ghPart`
(`Impl.Gcm.AArch64.Stitch`) computes, as bits (`Pmull/Ops.lean`), and what it
needs of the table of keys, without the algebra
(`Proof/AesGcm/AArch64/GhashImpls.lean` gives the classes):

* of a block `a` as loaded and a key `s` (a power with its halves swapped),
  Karatsuba's products add `a₀ · s₀` to `hi`, `a₁ · s₁` to `lo` and
  `(a₀ + a₁) · (s₀ + s₁)` to `mid` (`kadd`), the last with `s₀ + s₁` (`kkey`)
  read from the table, and the reduction is that of `hi : mid + hi + lo : lo`
  (`fix`);
* the table holds `H'ᵏ = preparedPower(Hᵏ)` with its halves swapped
  (`Pmull.pp`), and, for each pair of `ghPart`, the two keys' `kkey`s
  (`kpack`): `TblOk`;
* `Gh8Ok`: from `Y` and the eight blocks as loaded, `reduce` of the products
  is the next `Y` as loaded, `ghashFrom` of the eight blocks (proven in
  `Proof/AesGcm/AArch64/GhashImpls.lean`).
-/

@[expose] public section

local notation "vdword" => VG.Proof.Gcm.Clmul.vdword
local notation "ofVDwords" => VG.Proof.Gcm.Clmul.ofVDwords

namespace VG.Proof.Gcm.AArch64.Stitch

open VG.AArch64
open VG.Proof.Gcm.AArch64.Pmull (Prod reduce ext8 pp)
open VG.Impl.Gcm.AArch64.Stitch (sOff kOff pa pb pk pl)

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

/-- A pair's products: block `a₁` by the key `s₁` and `a₂` by `s₂`, their
keys' `kkey`s in the lanes of `kp`. -/
def kpair (p : Prod) (a₁ s₁ a₂ s₂ kp : BitVec 128) : Prod :=
  kadd (kadd p a₁ s₁ (vdword kp 0)) a₂ s₂ (vdword kp 1)

/-- The keys' `kkey`s of the pair `(k, l)`, in the low and high lanes. -/
def kpack (H : Spec.Gcm.Block) (k l : Nat) : BitVec 128 :=
  ofVDwords (kkey (ext8 (pp H k) (pp H k))) (kkey (ext8 (pp H l) (pp H l)))


/-- The table of keys of `H` at `W` (`Stitch.tbl`). -/
structure TblOk (m : Mem) (W : Addr) (H : Spec.Gcm.Block) : Prop where
  sw : ∀ k, 1 ≤ k → k ≤ 8 → m.readW (W + BitVec.ofNat 64 (sOff k)) 128 = ext8 (pp H k) (pp H k)
  key : ∀ p < 4, m.readW (W + BitVec.ofNat 64 (kOff p)) 128 = kpack H (pk p) (pl p)

/-- What `ghPart` computes, from `Y` and the eight blocks (as loaded), the
powers `S k` and the keys `KP p`. -/
def gh8V (y : BitVec 128) (b : Nat → BitVec 128) (S KP : Nat → BitVec 128) : BitVec 128 :=
  let pr := fun (pv : Prod) (p : Nat) =>
    kpair pv (b (pa p)) (S (pk p)) (b (pb p) ^^^ (if p = 3 then y else 0)) (S (pl p)) (KP p)
  reduce (fix (pr (pr (pr (pr ⟨0, 0, 0⟩ 0) 1) 2) 3))

/-- `ghPart` is GHASH of the eight blocks, with the table of `H`. -/
def Gh8Ok : Prop :=
  ∀ (H y : Spec.Gcm.Block) (b : Nat → Spec.Gcm.Block),
    gh8V (ext8 y y) (fun j => ext8 (b j) (b j)) (fun k => ext8 (pp H k) (pp H k)) (fun p => kpack H (pk p) (pl p)) =
      ext8 (Spec.Gcm.ghashFrom H y ((List.range 8).map b)) (Spec.Gcm.ghashFrom H y ((List.range 8).map b))

end VG.Proof.Gcm.AArch64.Stitch

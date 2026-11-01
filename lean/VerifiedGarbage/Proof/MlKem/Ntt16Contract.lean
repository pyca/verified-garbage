module

public import VerifiedGarbage.Proof.MlKem.Kpke16Contract

/-!
# ML-KEM with 16-bit coefficients: the NTT and its inverse, on every target

Not trusted: the contracts that the proofs of internal functions (`Rust.Internal`),
which only verified code calls, are of, and that the proofs of their callers
compose. Only the callers' contracts, in `Spec/`, are trusted.

`NTT` (FIPS 203 Algorithm 9) and `NTT⁻¹` (Algorithm 10) of a polynomial
stored as `[u16; 256]`, in place, with 512 bytes of working space: the
16-bit counterparts of `vg_mlkem_ntt` and `vg_mlkem_inv_ntt`
(`PolyContract.lean`), for the functions of `Kpke16Contract.lean`'s storage
to call.
-/

@[expose] public section

namespace VG.Proof.MlKem

open VG.Spec VG.Spec.MlKem

/-- `f: *mut [u16; 256], scratch: *mut [u64; 64]`. -/
def inPlace16Sig : Sig where
  params := [("f", .array true .u16 256), ("scratch", .array true .u64 64)]

/-- If the polynomial stored with 16-bit coefficients at `f` is reduced, it
becomes `t` of it, reduced. -/
def inPlace16Contract {M : ISA} (A : Abi M) (t : Poly → Poly) (stack : Nat := 0) : Contract M :=
  inPlace16Sig.contract A
    (pre := fun f _scratch m => ReducedW 16 m f)
    (post := fun f _scratch m m' _ => PolyIsW 16 m' f (t (polyAtW 16 m f)))
    (writeArgs := true)
    (stack := stack)

/-- `vg_mlkem16_ntt(f: *mut [u16; 256], scratch: *mut [u64; 64])`: `NTT`
(Algorithm 9) in place. -/
def ntt16Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  inPlace16Contract A ntt stack

/-- `vg_mlkem16_inv_ntt(f: *mut [u16; 256], scratch: *mut [u64; 64])`:
`NTT⁻¹` (Algorithm 10) in place. -/
def nttInv16Contract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  inPlace16Contract A nttInv stack

end VG.Proof.MlKem

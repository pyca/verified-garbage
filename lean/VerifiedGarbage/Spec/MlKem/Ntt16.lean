module

public import VerifiedGarbage.Spec.MlKem.Kpke16

/-!
# ML-KEM with 16-bit coefficients: the NTT and its inverse, on every target

**Trusted** (as every file in `Spec/`). `NTT` (FIPS 203 Algorithm 9) and
`NTT⁻¹` (Algorithm 10) of a polynomial stored as `[u16; 256]`, in place,
with 512 bytes of working space: the 16-bit counterparts of `vg_mlkem_ntt`
and `vg_mlkem_inv_ntt` (`Spec/MlKem/Poly.lean`), for the functions of
`Spec/MlKem/Kpke16.lean`'s storage to call.
-/

@[expose] public section

namespace VG.Spec.MlKem

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

/-- `vg_mlkem16_ntt` on every target. -/
def ntt16Api : Api where
  module := "mlkem16"
  name := "vg_mlkem16_ntt"
  sig := inPlace16Sig
  writeArgs := true
  contracts := some fun A stack => ntt16Contract A stack
  summary := "The ML-KEM number-theoretic transform, `NTT` (FIPS 203 Algorithm 9), of the \
    polynomial `*f` (256 `u16` coefficients less than `q` = 3329), in place." ++
    ctDoc "ntt16Contract"
  safety := [reduced16Safety "f" 1, scratchSafety]

/-- `vg_mlkem16_inv_ntt` on every target. (Not `vg_mlkem16_ntt_inv`: a
function named after another with a suffix and the same signature is a
variant of it, to `ci/check_variants.py`.) -/
def nttInv16Api : Api where
  module := "mlkem16"
  name := "vg_mlkem16_inv_ntt"
  sig := inPlace16Sig
  writeArgs := true
  contracts := some fun A stack => nttInv16Contract A stack
  summary := "The inverse of the ML-KEM number-theoretic transform, `NTT⁻¹` (FIPS 203 \
    Algorithm 10), of `*f` (256 `u16` coefficients less than `q` = 3329), in place." ++
    ctDoc "nttInv16Contract"
  safety := [reduced16Safety "f" 1, scratchSafety]

end VG.Spec.MlKem

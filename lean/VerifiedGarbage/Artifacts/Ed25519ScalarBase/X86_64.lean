import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Sound
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedVerified
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.ScalarBase

/-! Complete unsigned scalar multiplication by the Ed25519 base point. -/

namespace VG.Artifacts.Ed25519ScalarBase.X86_64

def artifacts : List Artifact := [
  { Spec.Ed25519.scalarBaseApi with
    target := X86_64.target
    doc := Spec.Ed25519.scalarBaseApi.doc (notes := ["Uses baseline integer instructions and \
      a comb: 26 tables of the multiples [k 1024^j]B (1 ≤ k ≤ 16) of the base point, affine, \
      precomputed as [Y - X, Y + X, 2dT] and checked against the specification in Lean, in the \
      static `VG_ED25519_COMB`. Each of the scalar's 52 chunks n of five bits (the last is bit \
      255 alone) gives the digit n - 16, whose magnitude selects its table entry in constant \
      time (every entry of the table is loaded with SSE2 and kept under a mask; a zero digit \
      selects the identity) and whose sign negates it, or not, under a mask; the odd digits are \
      added first to [G]B (G = 16 Σ 1024^j makes up for the offset), then five doublings and \
      [G]B again, then the even ones. The working values, masks and saved registers reside in \
      `scratch`."])
    consts := Impl.Ed25519.X86_64.combConsts
    code := Impl.Ed25519.X86_64.scalarBase_precomputed Impl.X25519.X86_64.baseline
    contract := Spec.Ed25519.scalarBaseContract (X86_64.abi.withConsts Impl.Ed25519.X86_64.combConsts)
    verified := Proof.Ed25519.X86_64.scalarBase_precomputed_verified
      (fld := Impl.X25519.X86_64.baseline)
    stack := 0
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Ed25519.scalarBaseApi with
    target := X86_64.target
    name := "vg_ed25519_scalar_base_adx"
    doc := Spec.Ed25519.scalarBaseApi.doc (notes := ["The code of \
      `vg_ed25519_scalar_base` but for the field multiplications and squarings, \
      which use BMI2's `mulx` and ADX's `adcx` and `adox` (two carry chains at once), as \
      `vg_x25519_adx` does. Its comb selects each of the scalar's 52 signed digits' table entry \
      in constant time from the static `VG_ED25519_COMB`; the working values, masks and saved \
      registers reside in `scratch`."])
    consts := Impl.Ed25519.X86_64.combConsts
    code := Impl.Ed25519.X86_64.scalarBase_precomputed Impl.X25519.X86_64.adx
    contract := Spec.Ed25519.scalarBaseContract (X86_64.abi.withConsts Impl.Ed25519.X86_64.combConsts)
    verified := Proof.Ed25519.X86_64.scalarBase_precomputed_verified (fld := Impl.X25519.X86_64.adx)
    features := ["bmi2", "adx"]
    stack := 0
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.Ed25519.scalarBaseApi with
    target := X86_64.target
    name := "vg_ed25519_scalar_base_ifma"
    doc := Spec.Ed25519.scalarBaseApi.doc (notes := ["The comb of `vg_ed25519_scalar_base_adx` \
      with two accumulated points, one in each half of `zmm` registers, (X, Y, Z, T) in the four \
      quadwords of the half as five limbs of 51 bits: one sums the entries of the odd digits, \
      the other those of the even digits, so each of the 26 steps adds two tables' entries at \
      once, each addition two products of eight field multiplications at once with \
      AVX512_IFMA's `vpmadd52luq` and `vpmadd52huq`. Each entry is selected from the static \
      `VG_ED25519_COMB` in constant time, 32 bytes at a time into both halves, split into limbs \
      and negated under the mask of its digit's sign. The odd digits' sum is then doubled five \
      times as `vg_ed25519_verify_ifma`'s doublings (on `ymm` registers, with AVX512VL) and the \
      even digits' added. The comb runs with MXCSR `0x1FBF` (Intel's MCDT prologue and \
      epilogue), saved in `scratch` and restored; the rest uses BMI2's and ADX's field \
      multiplications."])
    consts := Impl.Ed25519.X86_64.combConsts
    code := Impl.Ed25519.X86_64.scalarBase_ifma
    contract := Spec.Ed25519.scalarBaseContract (X86_64.abi.withConsts Impl.Ed25519.X86_64.combConsts)
    verified := Proof.Ed25519.X86_64.Ifma.scalarBase_ifma_verified
    features := ["avx", "avx2", "bmi2", "adx", "avx512f", "avx512ifma", "avx512vl"]
    stack := 0
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Ed25519ScalarBase.X86_64

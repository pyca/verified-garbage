import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Impl.X25519.X86_64
import VerifiedGarbage.Proof.X25519.X86_64.Verified
import VerifiedGarbage.Proof.X25519.X86_64.Lit
import VerifiedGarbage.Impl.X25519.X86_64.Adx
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Verified
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Lit
import VerifiedGarbage.Impl.X25519.X86_64.Ifma
import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Verified
import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Lit
import VerifiedGarbage.Proof.X25519.X86_64.Base.Verified
import VerifiedGarbage.Proof.X25519.X86_64.Base.Ifma
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Sound

/-! # X25519 (RFC 7748) on x86-64 -/

namespace VG.Artifacts.X25519.X86_64

def artifacts : List Artifact := [
  { Spec.X25519.x25519Api with
    target := X86_64.target
    doc := Spec.X25519.x25519Api.doc (notes := ["The function saves its caller's callee-saved \
      registers in `scratch`. Field elements are four 64-bit words, multiplied with `mul` \
      (squares computing each cross product once) and reduced with `2^256 = 38` (mod p); the \
      inversion is by Bernstein–Yang divsteps, in ten batches of 59 on 64-bit words, and one \
      multiplication by `2^-590`."])
    code := Impl.X25519.X86_64.x25519
    contract := Spec.X25519.x25519Contract X86_64.abi
    verified := Proof.X25519.X86_64.x25519_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.X25519.x25519Api with
    target := X86_64.target
    name := "vg_x25519_adx"
    doc := Spec.X25519.x25519Api.doc (notes := ["The function saves its caller's callee-saved \
      registers in `scratch`. Field elements are four 64-bit words, multiplied and squared with \
      BMI2's `mulx` and ADX's `adcx` and `adox` (two carry chains at once) and reduced with \
      `2^256 = 38` (mod p); the inversion is `vg_x25519`'s divsteps. The same code as \
      `vg_x25519` but for the field multiplications."])
    code := Impl.X25519.X86_64.x25519Adx
    contract := Spec.X25519.x25519Contract X86_64.abi
    verified := Proof.X25519.X86_64.x25519Adx_verified
    features := ["bmi2", "adx"]
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.X25519.x25519Api with
    target := X86_64.target
    name := "vg_x25519_ifma"
    doc := Spec.X25519.x25519Api.doc (notes := ["The function saves its caller's callee-saved \
      registers in `scratch`. The ladder runs the four field multiplications of each of its \
      three stages at once, one to each 64-bit lane of `ymm` registers, with AVX512_IFMA's \
      `vpmadd52luq` and `vpmadd52huq`: field elements are five 51-bit limbs, reduced with \
      `2^255 = 19` (mod p). It sets MXCSR to `0x1FBF` for the ladder (Intel's mitigation of \
      MXCSR-configuration-dependent timing) and restores the caller's. The inversion is \
      `vg_x25519`'s divsteps, with `vg_x25519_adx`'s field multiplication."])
    code := Impl.X25519.X86_64.x25519Ifma
    contract := Spec.X25519.x25519Contract X86_64.abi
    verified := Proof.X25519.X86_64.x25519Ifma_verified
    features := ["avx", "avx2", "bmi2", "adx", "avx512ifma", "avx512vl"]
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.X25519.x25519BaseApi with
    target := X86_64.target
    doc := Spec.X25519.x25519BaseApi.doc (notes := ["Ed25519's fixed-base comb, from its \
      tables in the static `VG_ED25519_COMB`, with the scalar clamped as RFC 7748 specifies and \
      the point mapped to `(Z + Y) / (Z - Y)`. The table selection is constant time; the \
      callee-saved registers are saved in `scratch`."])
    consts := Impl.Ed25519.X86_64.combConsts
    code := Impl.X25519.X86_64.Base.x25519Base Impl.X25519.X86_64.baseline
    contract := Spec.X25519.x25519BaseContract (X86_64.abi.withConsts Impl.Ed25519.X86_64.combConsts)
    verified := Proof.X25519.X86_64.Base.x25519Base_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.X25519.x25519BaseApi with
    target := X86_64.target
    name := "vg_x25519_base_adx"
    doc := Spec.X25519.x25519BaseApi.doc (notes := ["The same fixed-base comb as \
      `vg_x25519_base`, with BMI2 and ADX field arithmetic."])
    consts := Impl.Ed25519.X86_64.combConsts
    code := Impl.X25519.X86_64.Base.x25519Base Impl.X25519.X86_64.adx
    contract := Spec.X25519.x25519BaseContract (X86_64.abi.withConsts Impl.Ed25519.X86_64.combConsts)
    verified := Proof.X25519.X86_64.Base.x25519Base_verified
    features := ["bmi2", "adx"]
    spSafe := Code.all_of_allInstrs (by lit_decide) },
  { Spec.X25519.x25519BaseApi with
    target := X86_64.target
    name := "vg_x25519_base_ifma"
    doc := Spec.X25519.x25519BaseApi.doc (notes := ["The fixed-base comb of \
      `vg_x25519_base_adx` with the accumulated point in the four quadwords of `ymm` registers: \
      each addition of a table's entry is two products of four field multiplications at once \
      with AVX512_IFMA's `vpmadd52luq` and `vpmadd52huq` (on `ymm` registers, with AVX512VL), as \
      `vg_ed25519_scalar_base_ifma`'s; the selection loads 32 bytes of each entry at a time. The \
      comb runs with MXCSR `0x1FBF` (Intel's MCDT prologue and epilogue), saved in `scratch` and \
      restored."])
    consts := Impl.Ed25519.X86_64.combConsts
    code := Impl.X25519.X86_64.Base.x25519BaseIfma
    contract := Spec.X25519.x25519BaseContract (X86_64.abi.withConsts Impl.Ed25519.X86_64.combConsts)
    verified := Proof.X25519.X86_64.Base.x25519BaseIfma_verified
    features := ["avx", "avx2", "bmi2", "adx", "avx512ifma", "avx512vl"]
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.X25519.X86_64

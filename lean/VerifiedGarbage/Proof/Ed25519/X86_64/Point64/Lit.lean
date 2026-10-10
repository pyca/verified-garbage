import VerifiedGarbage.Proof.X25519.X86_64.Adx.Lit
import VerifiedGarbage.Impl.X25519.X86_64.Adx
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Ed25519.X86_64.Point64

/-! The point functions' code as literals (`materialize_code`), which their checks, and those
of the code that calls them, read rather than build each field multiplication again. -/

namespace VG.Impl.Ed25519.X86_64.Point64

open VG.Impl.X25519.X86_64 (baseline adx)

materialize_code doubleExtLit := doubleFn baseline true
materialize_code doubleProjLit := doubleFn baseline false
materialize_code addExtLit := addFn baseline true
materialize_code addProjLit := addFn baseline false
materialize_code doubleExtAdxLit := doubleFn adx true
materialize_code doubleProjAdxLit := doubleFn adx false
materialize_code addExtAdxLit := addFn adx true
materialize_code addProjAdxLit := addFn adx false
materialize_code addAffineLit := addAffineFn baseline
materialize_code addAffineAdxLit := addAffineFn adx

end VG.Impl.Ed25519.X86_64.Point64

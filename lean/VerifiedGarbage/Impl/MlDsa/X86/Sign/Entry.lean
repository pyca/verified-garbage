module

public import VerifiedGarbage.Impl.MlDsa.X86.Sign.Sign
public import VerifiedGarbage.Impl.MlDsa.X86.KeyGen.Call
public import VerifiedGarbage.Spec.MlDsa.Contract

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa{44,65,87}_sign` and `vg_mldsa{44,65,87}_sign_prepared`

Both are leaves that call the signing code they share, `vg_mldsa*_sign_core`
(`Sign.sign`, named `n`, with the code `f`), with their own arguments
`sk, mu, rnd, sig, scratch`, after setting the word `KEYS` of `scratch`:

* `vg_mldsa*_sign` sets it to 0, so that the core decodes `ŝ₁`, `ŝ₂` and
  `t̂₀` from `sk`;
* `vg_mldsa*_sign_prepared`, whose `sk` is a prepared private key (the
  encoded key, then the `ℓ + 2k` polynomials `ŝ₁`, `ŝ₂`, `t̂₀` as `u32`
  coefficients), sets it to 1 and copies those polynomials to the slots of
  `ŝ₁`, `ŝ₂` and `t̂₀` in `scratch`, so that the core uses them.

Every address and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlDsa.X86.Sign

open VG.X86
open VG.Impl.MlKem.X86 (Buf copyW leaf at_)
open VG.Spec.MlDsa (Params)

/-- The name of `vg_mldsa*_sign_core`, for the module `module`. -/
def coreName (module : String) : String := s!"vg_{module}_sign_core"

/-- The name of `vg_mldsa*_sign_prepared`, for the module `module`. -/
def preparedName (module : String) : String := s!"vg_{module}_sign_prepared"

section
variable (p : Params)

/-- The size of `scratch` in bytes. -/
abbrev scrBytes : Nat := Spec.MlDsa.scratchWords p * 8

/-- The size of the polynomials of a prepared private key, in bytes. -/
abbrev keysBytes : Nat := 1024 * (p.ℓ + 2 * p.k)

/-- The core's arguments: the function's own. -/
def coreArgs : List KeyGen.Arg :=
  [.buf (bSk 0 p.skLen), .buf bMu, .buf bRnd, .buf (bSig 0 p.sigLen), .buf (sc 0 (scrBytes p))]

/-- `esi ← scratch`, `pre`, and the call of the core. -/
def entryBody (pre : Prog isa) (n : String) (f : Prog isa) : Prog isa :=
  .seq (.block [.mov .esi (.mem (at_ .esp (20 + 4 * SC)))])
    (.seq pre (KeyGen.callPR SC n f (coreArgs p)))

/-- `KEYS ← 1`, then the polynomials of the prepared key `sk` to the slots
of `ŝ₁`, `ŝ₂` and `t̂₀`. -/
def copyKeys : Prog isa :=
  .seq (.block (st32 oKEYS 1))
    (copyW SC (bSk p.skLen (keysBytes p)) (sc (oP (5 + 2 * p.k + 2 * p.ℓ)) (keysBytes p)) (256 * (p.ℓ + 2 * p.k)))

/-- `vg_mldsa{44,65,87}_sign`, calling the core `f`, named `n`. -/
def signEntry (n : String) (f : Prog isa) : Prog isa := leaf (entryBody p (.block (st32 oKEYS 0)) n f)

/-- `vg_mldsa{44,65,87}_sign_prepared`, calling the core `f`, named `n`. -/
def signPrepared (n : String) (f : Prog isa) : Prog isa := leaf (entryBody p (copyKeys p) n f)

end

end VG.Impl.MlDsa.X86.Sign

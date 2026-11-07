module

public import VerifiedGarbage.Impl.MlDsa.X86.Verify.Verify
public import VerifiedGarbage.Spec.MlDsa.Contract

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa{44,65,87}_verify` and `vg_mldsa{44,65,87}_verify_prepared`

Both are leaves that call the verification code they share,
`vg_mldsa*_verify_core` (`Verify.verify`, named `n`, with the code `f`), with
their own `pk`, `mu`, `sig` and `scratch`, and `t1`, the `k` polynomials
`t̂₁[r] = NTT(t₁[r] · 2ᵈ)` of the public key:

* `vg_mldsa*_verify` computes them in the last `1024 k` bytes of `scratch`
  (`oT1 p`), which the core does not use: `t₁[r]` unpacked
  (`vg_mldsa_unpack_t1`) and transformed (`vg_mldsa_ntt`, with the first
  1024 bytes of `scratch` as its working space);
* `vg_mldsa*_verify_prepared`, whose `pk` is a prepared public key (the
  encoded key, then the `k` polynomials `t̂₁` as `u32` coefficients), passes
  those that follow the encoded key.

Every address and branch depends only on the pointers.
-/

@[expose] public section

namespace VG.Impl.MlDsa.X86.Verify

open VG.X86
open VG.Impl.MlKem.X86 (Buf leaf at_)
open VG.Impl.MlDsa.X86.KeyGen (Arg callP callPR seqR)
open VG.Spec.MlDsa (Params)

/-- The name of `vg_mldsa*_verify_core`, for the module `module`. -/
def coreName (module : String) : String := s!"vg_{module}_verify_core"

/-- The name of `vg_mldsa*_verify_prepared`, for the module `module`. -/
def preparedName (module : String) : String := s!"vg_{module}_verify_prepared"

section
variable (p : Params)

/-- Where `vg_mldsa*_verify` computes `t̂₁` in `scratch`: its last `1024 k` bytes. -/
abbrev oT1 : Nat := Spec.MlDsa.scratchWords p * 8 - 1024 * p.k

/-- `t̂₁[r]`, in `scratch`. -/
abbrev t1S (r : Nat) : Buf := sb (oT1 p + 1024 * r) 1024

/-- The core's arguments, with `t1` the buffer `t`. -/
def coreArgs (t : Buf) : List Arg :=
  [.buf ⟨0, 0, p.pkLen⟩, .buf ⟨1, 0, 64⟩, .buf ⟨2, 0, p.sigLen⟩, .buf (sb 0 (oT1 p)), .buf t]

/-- `t̂₁[r] = NTT(t₁[r] · 2ᵈ)` to `t1S r`. -/
def t1One (P : Prims) (r : Nat) : Prog isa :=
  .seq (callP vS "vg_mldsa_unpack_t1" P.unpackT1 [.buf ⟨0, 32 + 320 * r, 320⟩, .buf (t1S p r)])
    (callP vS "vg_mldsa_ntt" P.ntt [.buf (t1S p r), .buf (sb 0 1024)])

/-- `vg_mldsa{44,65,87}_verify`, calling the core `f`, named `n`, with the primitives `P`. -/
def verifyEntry (P : Prims) (n : String) (f : Prog isa) : Prog isa :=
  leaf (.seq (.block [.mov .esi (.mem (at_ .esp (20 + 4 * vS)))]) (.seq (seqR (t1One p P) 0 p.k)
    (callPR vS n f (coreArgs p (sb (oT1 p) (1024 * p.k))))))

/-- `vg_mldsa{44,65,87}_verify_prepared`, calling the core `f`, named `n`. -/
def verifyPrepared (n : String) (f : Prog isa) : Prog isa :=
  leaf (.seq (.block [.mov .esi (.mem (at_ .esp (20 + 4 * vS)))])
    (callPR vS n f (coreArgs p ⟨0, p.pkLen, 1024 * p.k⟩)))

end

end VG.Impl.MlDsa.X86.Verify

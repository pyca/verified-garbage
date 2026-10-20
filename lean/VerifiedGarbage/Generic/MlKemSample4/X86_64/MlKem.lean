module

public import VerifiedGarbage.Proof.MlKem.X86_64.Top768
public import VerifiedGarbage.Proof.MlKem1024.X86_64.Top
public import VerifiedGarbage.Proof.MlKem1024.X86_64.Written
public import VerifiedGarbage.Proof.MlKem.X86_64.Instances
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# ML-KEM-768 and ML-KEM-1024 (FIPS 203) on x86-64: key generation, encapsulation (hashing the key, or with `H(ek)` given) and decapsulation

A generic file (see `TCB/Emit.lean`): the artifacts it lists, which sample the
matrix `Â` four entries at a time with an implementation `v` of
`vg_mlkem_sample_ntt4` (and compute the outputs of `PRF` as goes with it), are
emitted once for each implementation (`Variants/MlKemSample4/X86_64/`), named
with its suffix (e.g. `vg_mlkem768_keygen_avx2`), and need its CPU features.
Both parameter sets are the same code and proofs for their layouts
(`Impl/MlKem/X86_64/Kem.lean`).
-/

@[expose] public section

namespace VG.Generic.MlKemSample4.X86_64.MlKem

open VG.Proof.MlKem.X86_64 (Sample4Impl)

/-- What an instance calls, sampling the matrix with `sampler`, and its use of the stack. -/
def callNotes (v : Sample4Impl) (sampler : String) : List String :=
  ["The function saves its caller's callee-saved registers in `scratch`; its calls use the 32 bytes of \
    stack below its return address. It samples the matrix four entries at a time with `" ++
    sampler ++ "`, and computes the outputs of `PRF` " ++ v.prfsDoc ++ "."]

/-- What an instance with polynomials of `u32`s calls. -/
def notes (v : Sample4Impl) : List String := callNotes v v.callee.name

/-- What an instance calls that computes with 16-bit polynomials if `v`
has a 16-bit sampler, calling the K-PKE functions `kpke`. -/
def notes16 (v : Sample4Impl) (kpke : List String) : List String :=
  match v.callee.s16 with
  | none => notes v
  | some (n, _) => callNotes v n ++ ["Its polynomials are 16-bit words: it samples the noise with \
      `vg_mlkem16_cbd2_avx2`, and computes the rest of K-PKE with " ++
      ", ".intercalate (kpke.map (s!"`{·}`")) ++ "."]

/-- How an instance of encapsulation (hashing the key) computes `H(ek)`, sampling the matrix with `sampler`. -/
def hashNote (sampler : String) : String :=
  "It computes `H(ek)` while it samples the matrix: it samples its first entries three at a time with the \
    code of `" ++ sampler ++ "` inlined, whose fourth Keccak state absorbs the padded key, three blocks of \
    136 bytes at a time."

/-- What an instance of encapsulation (hashing the key) calls, calling the
K-PKE function `kpke` with 16-bit polynomials, and how it computes `H(ek)`. -/
def encapsNotes (v : Sample4Impl) (kpke : String) : List String :=
  match v.callee.s16, v.callee.batchH16 with
  | some (n, _), some _ => notes16 v [kpke] ++ [hashNote n]
  | _, _ => notes v ++ ["It computes `H(ek)` with the sponge functions of SHA3-256 first."]

def artifacts (v : Sample4Impl) : List Artifact := [
  Spec.MlKem.keyGenApi.artifact X86_64.target {
    suffix := v.suffix
    notes := notes16 v ["vg_mlkem768_kpke_keygen"]
    code := Impl.MlKem.X86_64.keyGen v.callee
    stack := 32
    verified := Proof.MlKem.X86_64.keyGen_verified v
    spSafe := Proof.MlKem.X86_64.keyGen_spSafe v
    features := v.features },
  Spec.MlKem.encapsHApi.artifact X86_64.target {
    suffix := v.suffix
    notes := notes16 v ["vg_mlkem768_kpke_encrypt"]
    code := Impl.MlKem.X86_64.encapsH v.callee
    stack := 32
    verified := Proof.MlKem.X86_64.encapsH_verified v
    spSafe := Proof.MlKem.X86_64.encapsH_spSafe v
    features := v.features },
  Spec.MlKem.encapsApi.artifact X86_64.target {
    suffix := v.suffix
    notes := encapsNotes v "vg_mlkem768_kpke_encrypt"
    code := Impl.MlKem.X86_64.encaps v.callee
    stack := 32
    verified := Proof.MlKem.X86_64.encaps_verified v
    spSafe := Proof.MlKem.X86_64.encaps_spSafe v
    features := v.features },
  Spec.MlKem.decapsApi.artifact X86_64.target {
    suffix := v.suffix
    notes := notes16 v ["vg_mlkem768_kpke_decrypt", "vg_mlkem768_kpke_encrypt"]
    code := Impl.MlKem.X86_64.decaps v.callee
    stack := 32
    verified := Proof.MlKem.X86_64.decaps_verified v
    spSafe := Proof.MlKem.X86_64.decaps_spSafe v
    features := v.features },
  Spec.MlKem1024.keyGenApi.artifact X86_64.target {
    suffix := v.suffix
    notes := notes16 v ["vg_mlkem1024_kpke_keygen"]
    code := Impl.MlKem1024.X86_64.keyGen1024 v.callee
    stack := 32
    verified := Proof.MlKem1024.X86_64.keyGen1024_verified v
    spSafe := Proof.MlKem.X86_64.keyGen1024_spSafe v
    written := Proof.MlKem1024.X86_64.written v
    writtenOk := Proof.MlKem1024.X86_64.keyGen1024_written v
    features := v.features },
  Spec.MlKem1024.encapsHApi.artifact X86_64.target {
    suffix := v.suffix
    notes := notes16 v ["vg_mlkem1024_kpke_encrypt"]
    code := Impl.MlKem1024.X86_64.encapsH1024 v.callee
    stack := 32
    verified := Proof.MlKem1024.X86_64.encapsH1024_verified v
    spSafe := Proof.MlKem.X86_64.encapsH1024_spSafe v
    written := Proof.MlKem1024.X86_64.written v
    writtenOk := Proof.MlKem1024.X86_64.encapsH1024_written v
    features := v.features },
  Spec.MlKem1024.encapsApi.artifact X86_64.target {
    suffix := v.suffix
    notes := encapsNotes v "vg_mlkem1024_kpke_encrypt"
    code := Impl.MlKem1024.X86_64.encaps1024 v.callee
    stack := 32
    verified := Proof.MlKem1024.X86_64.encaps1024_verified v
    spSafe := Proof.MlKem.X86_64.encaps1024_spSafe v
    written := Proof.MlKem1024.X86_64.writtenEnc v
    writtenOk := Proof.MlKem1024.X86_64.encaps1024_written v
    features := v.features },
  Spec.MlKem1024.decapsApi.artifact X86_64.target {
    suffix := v.suffix
    notes := notes16 v ["vg_mlkem1024_kpke_decrypt", "vg_mlkem1024_kpke_encrypt"]
    code := Impl.MlKem1024.X86_64.decaps1024 v.callee
    stack := 32
    verified := Proof.MlKem1024.X86_64.decaps1024_verified v
    spSafe := Proof.MlKem.X86_64.decaps1024_spSafe v
    written := Proof.MlKem1024.X86_64.writtenEnc v
    writtenOk := Proof.MlKem1024.X86_64.decaps1024_written v
    features := v.features }]

end VG.Generic.MlKemSample4.X86_64.MlKem

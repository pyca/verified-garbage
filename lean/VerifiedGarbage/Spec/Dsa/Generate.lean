module

public import VerifiedGarbage.Spec.Dsa.Random
public import VerifiedGarbage.Spec.Dsa.SignVerify

/-!
# DSA key generation contract and generation helpers (trusted)

Key generation consumes fresh independent random octets, samples x by
FIPS 186-4 B.1.2 rejection sampling, and computes y = g^x mod p. Imported
parameters undergo algebraic consistency checks, not primality certification.
The private scalar and its random tape are secret; only public parameters,
sampling decisions and success/failure may affect timing.

The generated widths, the p||q||g encoding and the scratch size here are also
those of parameter generation over a refillable tape (`ParameterSearch.lean`).

Key generation is bounded by its finite input tape and 128 scalar draws.
Failure zeros output.
-/

@[expose] public section

namespace VG.Spec.Dsa

open VG.Spec.Rsa (bytesAt wordsAt)

/-- Parameters in the same prefix encoding as the signing key: p||q||g. -/
def paramsBytes (pLen qLen : Nat) (params : List Byte) : Params :=
  (publicKeyBytes pLen qLen params).params

def encodeParams (pLen qLen : Nat) (a : Params) : List Byte :=
  encodeBE pLen a.p ++ encodeBE qLen a.q ++ encodeBE pLen a.g

/-- Private key output has exactly the signer's p||q||g||y||x layout. -/
def encodePrivateKey (pLen qLen : Nat) (key : Key) : List Byte :=
  encodeParams pLen qLen key.params ++ encodeBE pLen key.y ++ encodeBE qLen (key.x.getD 0)

structure GenerateKeyResult where
  key : Option (List Byte)
  status : Nat
  used : Nat
  trace : List Nat
  deriving DecidableEq, Repr

/-- Checked domain, sampled scalar, public-key exponentiation, and final
key consistency. Status 0 is invalid input/draw limit, 1 success, 2 exhaustion.
A supplied domain's primality remains the caller's responsibility. -/
def generateKeyBytes (pLen qLen : Nat) (params rand : List Byte) : GenerateKeyResult :=
  if !(lengthsValid pLen qLen) || params.length != 2 * pLen + qLen then
    ⟨none, 0, 0, [4]⟩
  else
    let a := paramsBytes pLen qLen params
    if !parametersValid a then ⟨none, 0, 0, [4]⟩ else
    let draw := Random.sample a.q 128 rand
    match draw.scalar with
    | none => ⟨none, if draw.trace.getLast? == some 2 then 2 else 0, draw.used, draw.trace⟩
    | some x =>
      match generate a [x] with
      | none => ⟨none, 0, draw.used, draw.trace ++ [6]⟩
      | some key =>
        if keyValid key then
          ⟨some (encodePrivateKey pLen qLen key), 1, draw.used, draw.trace ++ [5]⟩
        else ⟨none, 0, draw.used, draw.trace ++ [6]⟩

/-- Complete fixed-width chunks only; callers require divisible lengths.
With width zero there are no chunks. -/
def generationChunks (width : Nat) (bytes : List Byte) : List (List Byte) :=
  (List.range (bytes.length / width)).map fun i => (bytes.drop (i * width)).take width

/-- Generated parameters use (1024,160), (2048,256), or (3072,256).
(2048,160) and (2048,224) remain supported only for imported parameters. -/
def generationLengthsValid (pLen qLen : Nat) : Prop :=
  (pLen = 128 ∧ qLen = 20) ∨ (pLen = 256 ∧ qLen = 32) ∨ (pLen = 384 ∧ qLen = 32)

instance (pLen qLen : Nat) : Decidable (generationLengthsValid pLen qLen) := by
  unfold generationLengthsValid
  infer_instance

/-- Caller-provided working space, including arithmetic and hash workspaces. -/
def generationScratchWords (pLen : Nat) : Nat := 64 * pLen + 1024

def generateKeySig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("used", .array true .u64 1),
    ("params", .slice false .u8 "params_len"), ("p_len", .int .usize true),
    ("q_len", .int .usize true), ("rand", .slice false .u8 "rand_len"),
    ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

def generateKeyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  generateKeySig.contract A
    (pre := fun _out outLen _used _params paramsLen pLen qLen _rand _randLen _scratch scratchLen _ =>
      lengthsValid pLen.toNat qLen.toNat ∧ outLen.toNat = 3 * pLen.toNat + 2 * qLen.toNat ∧
        paramsLen.toNat = 2 * pLen.toNat + qLen.toNat ∧
        generationScratchWords pLen.toNat ≤ scratchLen.toNat)
    (post := fun out outLen used params paramsLen pLen qLen rand randLen _scratch _scratchLen m m' r =>
      let res := generateKeyBytes pLen.toNat qLen.toNat (bytesAt m params paramsLen.toNat)
        (bytesAt m rand randLen.toNat)
      r.toNat = res.status ∧
        bytesAt m' out outLen.toNat = res.key.getD (List.replicate outLen.toNat 0) ∧
        wordsAt m' used 1 = [BitVec.ofNat 64 res.used])
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen _used params paramsLen pLen qLen rand randLen _scratch _scratchLen m =>
      let pb := bytesAt m params paramsLen.toNat
      let res := generateKeyBytes pLen.toNat qLen.toNat pb (bytesAt m rand randLen.toNat)
      pb.map (·.toNat) ++ [res.status, res.used] ++ res.trace)

def generateKeyApi : Api where
  module := "dsa"
  name := "vg_dsa_generate_key"
  sig := generateKeySig
  writeArgs := true
  contracts := some fun A stack => generateKeyContract A stack
  summary := "Generate a DSA private key from p||q||g and fresh independent random bytes. \
    Uses at most 128 rejection-sampling draws, computes y=g^x mod p, and checks algebraic \
    consistency, not primality. Returns 1 with p||q||g||y||x, 0 for invalid input/draw limit, \
    or 2 for insufficient randomness. Failure zeros out; used counts consumed complete \
    draws on every return. Timing may depend on public parameters, sampling decisions, \
    consumption and success, not otherwise on x or randomness. \
    Contract: `VG.Spec.Dsa.generateKeyContract`."
  safety := ["(p_len, q_len) must be (128,20), (256,20), (256,28), (256,32), or (384,32).",
    "params_len must be 2*p_len + q_len; out_len must be 3*p_len + 2*q_len.",
    "scratch_len must be at least 64*p_len + 1024 words; destroy scratch after use.",
    "Caller must assure domain validity and supply fresh independent random bytes."]

end VG.Spec.Dsa

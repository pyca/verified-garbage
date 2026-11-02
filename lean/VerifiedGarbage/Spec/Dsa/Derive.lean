module

public import VerifiedGarbage.Spec.Dsa.Generate

/-!
# DSA domain checks and key derivation: the parts of key generation (trusted)

`generateKeyBytes` checks the domain before it consumes any randomness, then
samples x, then derives and checks the key:

* `checkParametersBytes` accepts exactly the supported widths and domains
  that `generateKeyBytes` accepts. All its inputs are public.
* `vg_dsa_derive_key` derives the key from an explicitly supplied scalar x,
  with `generateKeyBytes`'s checks (`deriveKeyBytes`): the domain, x's range,
  y = g^x mod p and `keyValid`. x is secret: only the domain and success may
  affect timing.

Deriving a key from a supplied x is for a caller that samples x itself: x
must be a fresh uniform scalar. It checks algebraic consistency, not
primality. Scratch may contain secrets on
return and must be destroyed by the caller.
-/

@[expose] public section

namespace VG.Spec.Dsa

open VG.Spec.Rsa (bytesAt)

/-- The domain checks of `generateKeyBytes`: supported widths, a packed
p||q||g of exactly those widths, and `parametersValid`. -/
def checkParametersBytes (pLen qLen : Nat) (params : List Byte) : Bool :=
  decide (lengthsValid pLen qLen) && params.length == 2 * pLen + qLen &&
    decide (parametersValid (paramsBytes pLen qLen params))

/-- Key derivation from a supplied q_len-byte big-endian x, with
`generateKeyBytes`'s checks after sampling: the domain, then `generate`
(which requires 0 < x < q), then `keyValid`. -/
def deriveKeyBytes (pLen qLen : Nat) (params x : List Byte) : Option (List Byte) :=
  if !checkParametersBytes pLen qLen params || x.length != qLen then none else
    match generate (paramsBytes pLen qLen params) [decodeBE x] with
    | none => none
    | some key => if keyValid key then some (encodePrivateKey pLen qLen key) else none

def deriveKeySig : Sig where
  params := [("out", .slice true .u8 "out_len"), ("params", .slice false .u8 "params_len"),
    ("p_len", .int .usize true), ("x", .slice false .u8 "q_len"),
    ("scratch", .slice true .u64 "scratch_len")]
  ret := some .u32

def deriveKeyContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  deriveKeySig.contract A
    (pre := fun _out outLen _params paramsLen pLen _x qLen _scratch scratchLen _ =>
      lengthsValid pLen.toNat qLen.toNat ∧ outLen.toNat = 3 * pLen.toNat + 2 * qLen.toNat ∧
        paramsLen.toNat = 2 * pLen.toNat + qLen.toNat ∧ scratchWords pLen.toNat ≤ scratchLen.toNat)
    (post := fun out outLen params paramsLen pLen x qLen _scratch _scratchLen m m' r =>
      let res := deriveKeyBytes pLen.toNat qLen.toNat (bytesAt m params paramsLen.toNat)
        (bytesAt m x qLen.toNat)
      r.toNat = signStatus res ∧
        bytesAt m' out outLen.toNat = res.getD (List.replicate outLen.toNat 0))
    (writeArgs := true) (stack := stack)
    (leak := some fun _out _outLen params paramsLen pLen x qLen _scratch _scratchLen m =>
      let pb := bytesAt m params paramsLen.toNat
      pb.map (·.toNat) ++
        [signStatus (deriveKeyBytes pLen.toNat qLen.toNat pb (bytesAt m x qLen.toNat))])

def deriveKeyApi : Api where
  module := "dsa"
  name := "vg_dsa_derive_key"
  sig := deriveKeySig
  writeArgs := true
  contracts := some fun A stack => deriveKeyContract A stack
  summary := "Derive a DSA private key from big-endian p||q||g and a supplied q_len-byte \
    scalar x, as key generation does after sampling x: checks the domain and \
    0 < x < q, computes y = g^x mod p and checks the key. Returns 1 with \
    p||q||g||y||x, or 0 and zero output. Checks algebraic consistency, not \
    primality. x must be a fresh uniform scalar the caller sampled. Timing may \
    depend on p, q, g and success, not otherwise on x. \
    Contract: `VG.Spec.Dsa.deriveKeyContract`."
  safety := ["(p_len, q_len) must be (128,20), (256,20), (256,28), (256,32), or (384,32).",
    "params_len must be 2*p_len + q_len; out_len must be 3*p_len + 2*q_len.",
    "scratch_len must be at least 16*p_len words. Scratch may contain secrets on return."]

end VG.Spec.Dsa

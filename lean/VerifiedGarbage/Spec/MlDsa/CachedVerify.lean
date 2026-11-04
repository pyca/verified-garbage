module

public import VerifiedGarbage.Spec.MlDsa.Contract

/-!
# Private cached-digest verification boundary

The additional read-only digest is valid only when it equals the public-key
hash. The ordinary raw-key verification contract is unchanged.
-/

@[expose] public section

namespace VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- Eight machine arguments: the ordinary message verifier's seven followed
by a pointer to the cached 64-byte public-key digest. -/
def verifyMessageCachedSig (p : Params) : Sig where
  params := [("pk", .array false .u8 p.pkLen), ("msg", .slice false .u8 "msg_len"),
    ("ctx", .slice false .u8 "ctx_len"), ("sig", .array false .u8 p.sigLen),
    ("scratch", .array true .u64 (messageScratchWords p)), ("tr", .array false .u8 64)]
  ret := some .u32

/-- Private contract. Its digest invariant must be established by the key
constructor; an arbitrary digest is not a valid input to this entry. -/
def verifyMessageCachedContract (p : Params) {M : ISA} (A : Abi M)
    (stack : Nat := 0) : Contract M :=
  (verifyMessageCachedSig p).contract A
    (pre := fun pk _msg _msgLen _ctx _ctxLen _sig _scratch tr m =>
      bytesAt m tr 64 = pkTr (bytesAt m pk p.pkLen))
    (post := fun pk msg msgLen ctx ctxLen sig _scratch _tr m _m' r =>
      match formatMessage (bytesAt m ctx ctxLen.toNat) (bytesAt m msg msgLen.toNat) with
      | none => r = 2
      | some M' =>
        let v := fun b => verifyInternal p b (bytesAt m pk p.pkLen) M' (bytesAt m sig p.sigLen)
        (r = 1 ∧ ∃ b, v b = some true) ∨ (r = 0 ∧ v minBounds ≠ some true))
    (writeArgs := true)
    (stack := stack)
    (leak := some fun pk msg msgLen ctx ctxLen sig _scratch _tr m =>
      leakBytes (bytesAt m pk p.pkLen ++ bytesAt m msg msgLen.toNat ++
        bytesAt m ctx ctxLen.toNat ++ bytesAt m sig p.sigLen))

/-- Private implementation API: callers must maintain the cached digest invariant. -/
def verifyMessageCachedApi (p : Params) (module name : String) : Api where
  module := module
  name := s!"vg_{module}_verify_message_cached"
  sig := verifyMessageCachedSig p
  writeArgs := true
  contracts := some fun A stack => verifyMessageCachedContract p A stack
  summary := s!"{name} message verification with a cached public-key digest. Returns 1 for a valid \
    signature, 0 for an invalid signature or exhausted sampling bound, and 2 if the context \
    exceeds 255 bytes. It is `ML-DSA.Verify(pk, M, σ, ctx)` (FIPS 204 Algorithm 3) with \
    `H(pk, 64)` read from `*tr`: with the public key `*pk`, the `msg_len` bytes of the message \
    at `msg`, the `ctx_len` bytes of the context string at `ctx` and the signature `*sig`, it \
    formats the message `M′ = 0 ‖ ctx_len ‖ ctx ‖ M` (line 5), computes \
    `μ = H(tr ‖ M′, 64)`, and verifies `*sig` on `μ` with `*pk`, \
    `ML-DSA.Verify_internal(pk, M′, σ)` (Algorithm 8).\n\n\
    Contract: `VG.Spec.MlDsa.verifyMessageCachedContract`. Timing may depend on the public key, \
    message, context string and signature, and on argument addresses and lengths."
  safety := ["`*tr` must equal SHAKE256(`*pk`, 64 bytes).", keyScratchSafety]


end VG.Spec.MlDsa

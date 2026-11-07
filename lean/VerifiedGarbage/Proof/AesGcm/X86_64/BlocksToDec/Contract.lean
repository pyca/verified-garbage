module

public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Contract
public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksTo.Piece
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.SpecToDec

/-!
# AES-GCM decryption of whole blocks out of place, x86-64: the contract

Untrusted: everything here is checked by Lean. `vg_aes_gcm_decrypt_blocks_to`
takes the arguments of `vg_aes_gcm_encrypt_blocks_to`, under the same
precondition (`blocksToPreM`) and with the same public arguments
(`blocksToPub`); it leaves the decryption of the ciphertext at `src` in the
output, the counter advanced, and `Y` continued over the ciphertext
(`blocksToDecPost`). Only verified code calls it, so its contract is here,
with no `Api`. `StitchToDecCode` is an out-of-place decryption loop with its
proof, which it may run on whole groups of 16 blocks.
-/

@[expose] public section

namespace VG.Proof.AesGcm

open VG VG.X86_64
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)

/-- What `vg_aes_gcm_decrypt_blocks_to` leaves: the decryption of the
ciphertext in the output, the counter advanced, and `Y` continued over the
ciphertext. -/
def blocksToDecPost (s s' : State) : Prop :=
  let n := (s.gpr .r9).toNat
  let c := blocksAt s.mem (s.gpr .r8) n
  blocksAt s'.mem (arg s 0) n = ctr32 (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (blockAt s.mem (s.gpr .rdx)) c ∧
    blockAt s'.mem (s.gpr .rdx) = Nat.repeat inc32 n (blockAt s.mem (s.gpr .rdx)) ∧
    blockAt s'.mem (s.gpr .rcx) = ghashFrom (ctxH s.mem (s.gpr .rdi)) (blockAt s.mem (s.gpr .rcx)) c

/-- `vg_aes_gcm_decrypt_blocks_to`, for a key context of kind `M`. -/
def decryptBlocksToX86_64M (M : CtxMode) : Contract isa where
  pre := blocksToPreM M
  post := blocksToDecPost
  pub := blocksToPub

end VG.Proof.AesGcm

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64

open Gcm.X86_64.Stitch (CtxMode StitchToDecOkM) in
/-- An out-of-place interleaved decryption loop for a key context of kind
`M`, on whole groups of 16 blocks, with its proof. -/
structure StitchToDecCode (M : CtxMode) (aligned : Bool := false) where
  dec : Prog isa
  ok : StitchToDecOkM M dec
  P : PieceTo dec aligned false

end VG.Proof.AesGcm.X86_64

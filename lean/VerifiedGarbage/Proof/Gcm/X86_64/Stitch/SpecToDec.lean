module

public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.SpecTo

/-!
# Interleaved counter mode and GHASH out of place: what the decryption loops do

Untrusted: everything here is checked by Lean. Interleaved decryption loops
that read the ciphertext from one buffer and write the plaintext to another
(for `vg_aes_gcm_decrypt_blocks_to`) start from a state meeting `SPreTo`
(`Stitch/SpecTo.lean`), with the ciphertext in `r8` and the output in `r10`.
`DPostTo` is what they do (`StitchToDecOkM`): `EPostTo`, but `Y` continued
over the ciphertext, which nothing writes.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.Stitch

open VG VG.X86_64
open VG.Spec.Gcm (Block blockAt blocksAt inc32 aesWith ghashFrom)

/-- What the decryption leaves: the ciphertext's decryption in the output,
the counter advanced, `Y` continued over the ciphertext, nothing else
written but the working space. -/
structure DPostTo (s₀ s : State) : Prop where
  data : blocksAt s.mem (op s₀) (nb s₀) =
    Spec.Gcm.ctr32 (ciph s₀) (cb s₀) (blocksAt s₀.mem (sp s₀) (nb s₀))
  ctr : blockAt s.mem (cp s₀) = Nat.repeat inc32 (nb s₀) (cb s₀)
  y : blockAt s.mem (yp s₀) = ghashFrom (hk s₀) (y₀ s₀) (blocksAt s₀.mem (sp s₀) (nb s₀))
  frame : Frame [cR s₀, yR s₀, oR s₀, pR s₀] s₀.mem s.mem
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- An out-of-place interleaved decryption loop `dec`, for a key context of
kind `M`, meets these contracts for a number of blocks that is a multiple of
`w`. -/
def StitchToDecOkM (M : CtxMode) (dec : Prog isa) (w : Nat := 16) : Prop :=
  ∀ s₀, SPreTo M s₀ → nb s₀ % w = 0 → WP isa dec s₀ (DPostTo s₀)

end VG.Proof.Gcm.X86_64.Stitch

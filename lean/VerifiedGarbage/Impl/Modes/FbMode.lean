/-!
# The feedback modes

OFB (SP 800-38A §6.4) and CFB with segments of a whole block (§6.3), in
each direction: each block's input block is the previous block's output
block (OFB) or ciphertext block (CFB). Each target's implementation of the
modes (`Impl/Modes/<Target>/Fb.lean`) takes one of these, and their proofs
share the mode's result (`Proof/Modes/Fb.lean`).
-/

namespace VG.Impl.Modes

/-- The feedback modes. -/
inductive FbMode
  /-- OFB, both directions. -/
  | ofb
  /-- CFB encryption, with segments of a whole block. -/
  | cfbEnc
  /-- CFB decryption, with segments of a whole block. -/
  | cfbDec
  deriving DecidableEq, Repr

end VG.Impl.Modes

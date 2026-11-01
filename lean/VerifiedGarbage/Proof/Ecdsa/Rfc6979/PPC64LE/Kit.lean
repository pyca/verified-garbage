module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Calls
public import VerifiedGarbage.Proof.Hmac.Contract
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.InitLong
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Finalize
import VerifiedGarbage.Proof.Hmac.Stream.PPC64LE.Common

/-!
# Deterministic ECDSA on PPC64LE: HMAC's functions over a streaming hash

The `Kit` of a streaming hash function whose HMAC `init` and `finalize`
(the code over any streaming hash, `Impl/Hmac/Stream/PPC64LE.lean`) are
verified against their shared contracts with 96 bytes of stack: their
frames are within those 96 bytes (`fdepth` ≤ 2).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Proof.Hmac.Stream.PPC64LE (HashOK)

/-- The `Kit` of a streaming hash function. -/
def Kit.ofStream (H : Hash) (hH : HashOK H) (I : Spec.Hmac.Instance) (hIS : I.S = hH.SH)
    (hi : Verified PPC64LE.target H.init (Proof.Hmac.Instance.initScratchContract I PPC64LE.abi 96))
    (hf : Verified PPC64LE.target H.finalize (Proof.Hmac.Instance.finalizeScratchContract I PPC64LE.abi 96))
    (hu : ConstantTime isa (Proof.Hmac.Stream.PPC64LE.updK H.S H.W hH.SH.Repr).pre
      (Proof.Hmac.Stream.PPC64LE.updK H.S H.W hH.SH.Repr).pub H.updC)
    (hScr : Impl.Ecdsa.Rfc6979.PPC64LE.sWork + I.scratch * 8 ≤ Impl.Ecdsa.Rfc6979.PPC64LE.sMsg)
    (hW : Impl.Ecdsa.Rfc6979.PPC64LE.sWork + H.W ≤ Impl.Ecdsa.Rfc6979.PPC64LE.sMsg)
    (hS : H.S ≤ 192) : Kit where
  H := H
  hH := hH
  I := I
  hIS := hIS
  initC := H.init
  finC := H.finalize
  kI := 95
  kF := 95
  initV := hi.1
  finV := hf.1
  initCT := hi.2.1
  finCT := hf.2.1
  updCT := hu
  hkI := Nat.le_refl _
  hkF := Nat.le_refl _
  dI := by
    have h₁ := sdepth_le_fdepth _ (Proof.Hmac.Stream.PPC64LE.InitLong.init_pf hH)
    have h₂ := Proof.Hmac.Stream.PPC64LE.InitLong.init_fdepth hH
    omega
  dF := by
    have h₁ := sdepth_le_fdepth H.finalize (by
      simp [Hash.finalize, pushFrames, Instr.isPush, Proof.Hmac.Stream.PPC64LE.Finalize.finalizeMain_pf hH])
    have h₂ : H.finalize.fdepth ≤ 2 := by
      have := Proof.Hmac.Stream.PPC64LE.Finalize.finalizeMain_fdepth hH
      simp only [Hash.finalize, Code.fdepth, Nat.max_le]; omega
    omega
  hScr := hScr
  hW := hW
  hS := hS

end VG.Proof.Ecdsa.Rfc6979.PPC64LE

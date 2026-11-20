module

public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.OptimizedPrims
public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.Prims
public import VerifiedGarbage.Impl.MlDsa.AArch64.PreparedKey.Sign
public import VerifiedGarbage.Impl.MlDsa.AArch64.PreparedKey.Verify
public import VerifiedGarbage.Impl.MlDsa.AArch64.Message
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.CachedVerify
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentMask
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.ResidentRejSelected
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.HighPack
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.KeygenPack
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.BallDispatch
public import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Ntt
public import VerifiedGarbage.Impl.MlDsa.AArch64.Pack.Hint
public import VerifiedGarbage.Impl.MlDsa.AArch64.Pack.Encode
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.ExpandMask
public import VerifiedGarbage.Impl.Residue.AArch64.Scrub

-- separate module: the functions as emitted name code of the modules above, which do not import one another

/-!
# ML-DSA on AArch64: the functions as emitted

Key generation, signing and verification of ML-DSA with the parameters `p`,
over the Keccak-f[1600] implementation `c` they call: each is its code, then
its cleanup (`scrubAll`), which clears every register the calling convention
does not preserve (`Clear.all`) and zeroes its stack, so that it returns
without secret residue. `module` is the name of the parameter set's module
(`mldsa44`), which names the functions; `prepared` is whether the key is a
prepared one.

The functions that take a message (`signMessage`, `verifyMessage`) hash it
and call the function that takes its representative (`sign`, `verify`) as
emitted, cleanup included.
-/

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.Fn

open VG.AArch64
open VG.Impl.Residue.AArch64 (scrubAll Clear)
open VG.Spec.MlDsa (Params)

/-- The primitives signing calls, over `c`. -/
def signPrims (c : Impl.Sha3.AArch64.Callee) : Impl.MlDsa.AArch64.Sign.Prims where
  suffix := c.suffix
  ntt := Impl.MlDsa.AArch64.Arith.Neon.ntt
  rej4 := Impl.MlDsa.AArch64.Optimized.ResidentRej.selected c.pairedSha3
  rejNTT := Impl.MlDsa.AArch64.Sample.rejNTTWith c
  expandMask := Impl.MlDsa.AArch64.Sample.expandMaskWith c
  pairedMask := c.pairedSha3
  expandMaskPair := Impl.MlDsa.AArch64.Optimized.ResidentMask.raw
  ball := Impl.MlDsa.AArch64.Optimized.Ball.selected c
  highPack := Impl.MlDsa.AArch64.Optimized.HighPack.code
  bitPack := Impl.MlDsa.AArch64.Optimized.KeygenPack.signed
  bitUnpack := Impl.MlDsa.AArch64.Pack.bitUnpack
  hintBitPack := Impl.MlDsa.AArch64.Pack.hintBitPack

/-- `vg_mldsa<n>_keygen`. -/
def keyGen (c : Impl.Sha3.AArch64.Callee) (p : Params) : Prog isa :=
  scrubAll 16 32 Clear.all (KeyGen.Optimized.keyGenWith c p)

/-- `vg_<module>_sign`, or `vg_<module>_sign_prepared`: signing a message
representative, with the key's bytes or a prepared key. -/
def sign (c : Impl.Sha3.AArch64.Callee) (p : Params) (module : String) (prepared : Bool) : Prog isa :=
  scrubAll 64 32 Clear.all
    (PreparedKey.Sign.entry (s!"vg_{module}_sign_with_cache" ++ c.suffix)
      (PreparedKey.Sign.withCache c (signPrims c) p) p prepared)

/-- `vg_<module>_sign_message`, or `vg_<module>_sign_message_prepared`. -/
def signMessage (c : Impl.Sha3.AArch64.Callee) (p : Params) (module : String) (prepared : Bool) : Prog isa :=
  scrubAll 64 32 Clear.all
    (Message.signMessage c
      ((if prepared then s!"vg_{module}_sign_prepared" else s!"vg_{module}_sign") ++ c.suffix)
      (sign c p module prepared) p)

/-- `vg_<module>_verify`, or `vg_<module>_verify_prepared`: verifying a
signature of a message representative, with the key's bytes or a prepared
key. -/
def verify (c : Impl.Sha3.AArch64.Callee) (p : Params) (module : String) (prepared : Bool) : Prog isa :=
  scrubAll 64 32 Clear.all
    (PreparedKey.Verify.entry (s!"vg_{module}_verify_with_cache" ++ c.suffix)
      (PreparedKey.Verify.withCache c (KeyGen.primsWith c) p) p prepared)

/-- `vg_<module>_verify_message_cached`, or
`vg_<module>_verify_message_prepared`. -/
def verifyMessage (c : Impl.Sha3.AArch64.Callee) (p : Params) (module : String) (prepared : Bool) :
    Prog isa :=
  scrubAll 64 32 Clear.all
    (Optimized.verifyMessageCached c
      ((if prepared then s!"vg_{module}_verify_prepared" else s!"vg_{module}_verify") ++ c.suffix)
      (verify c p module prepared) p)

end VG.Impl.MlDsa.AArch64.Fn

module

public import VerifiedGarbage.Impl.MlDsa.AArch64.PreparedKey.Copy
public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.Prims
public import VerifiedGarbage.Impl.MlDsa.AArch64.Verify.Optimized
public import VerifiedGarbage.Impl.MlDsa.AArch64.Verify.OptimizedSamples

/-! # Shared verification body for ordinary and prepared ML-DSA keys -/

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.PreparedKey.Verify
open VG VG.AArch64 VG.Spec.MlDsa VG.Impl.MlDsa.AArch64.Call
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify

/-- The public key's row `r`: from the prepared key, or unpacked and transformed. -/
def keyRow (P : Prims) (p : Params) (r : Nat) : Prog isa :=
  .ite (.nonzero .x .x22) (PreparedKey.copy (tmP p) (.x21, 1024 * r) 1024)
    (.seq (unpackT1At P (.x25, 32 + 320 * r) (tmP p)) (Optimized.forward (tmP p)))

/-- Row `r` of `w'₁`, with the positive transform arithmetic, which needs no
CPU feature. -/
def row (P : Prims) (p : Params) (r : Nat) : Prog isa :=
  .seq (Optimized.dot p r) (.seq (keyRow P p r)
    (.seq (Optimized.product p) (.seq (Optimized.subtract p)
      (.seq (Optimized.inverse (wP p)) (Optimized.hintPack p r)))))

def compute (c : Impl.Sha3.AArch64.Callee) (P : Prims) (p : Params) : Prog isa :=
  .seq (seqR (fun i => Optimized.forward (zP p i)) 0 p.ℓ)
    (.seq (Optimized.forward (cP p)) (.seq (seqR (row P p) 0 p.k)
      (.seq (shake256With c [⟨.x26, 0, 64⟩, ⟨.x28, (bP p).2, p.k * w1Len p⟩]
        [⟨.x28, oCT, p.ctildeLen⟩]) (cmpAnd (sc oCT) (.x27, 0) p.ctildeLen))))

/-- The samplers are the permutation's: the paired ones where its kernels
may use the SHA3 instructions. -/
def body (c : Impl.Sha3.AArch64.Callee) (P : Prims) (p : Params) : Prog isa :=
  .seq (hint P p) (ifOk (.seq (seqR (zOne P p) 0 p.ℓ)
    (ifOk (.seq (if c.pairedSha3 then OptimizedSamples.samples P p else samples P p)
      (compute c P p)))))

def core (c : Impl.Sha3.AArch64.Callee) (P : Prims) (p : Params) : Prog isa :=
  .seq (.block pro) (.seq (body c P p) (.block epi))

def withCache (c : Impl.Sha3.AArch64.Callee) (P : Prims) (p : Params) : Prog isa :=
  .frame (.push .x21) (.frame (.push .x22)
    (.seq (.block [.addImm .x .x21 .x4 0, .addImm .x .x22 .x5 0])
      (core c P p)) (.pop .x22)) (.pop .x21)

def entry (name : String) (code : Prog isa) (p : Params) (prepared : Bool) : Prog isa :=
  .frame (.push .x30)
    (.seq (.block (if prepared then lea .x4 .x0 p.pkLen ++ movV .x5 (1024 * p.k)
      else [.addImm .x .x4 .x0 0] ++ movV .x5 0)) (.call name code)) (.pop .x30)

end VG.Impl.MlDsa.AArch64.PreparedKey.Verify

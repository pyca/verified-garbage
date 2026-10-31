module

public import VerifiedGarbage.Impl.MlDsa.AArch64.PreparedKey.Copy
public import VerifiedGarbage.Impl.MlDsa.AArch64.Verify.OptimizedTop
public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.Prims

/-! # Shared verification body for ordinary and prepared ML-DSA keys -/

@[expose] public section

namespace VG.Impl.MlDsa.AArch64.PreparedKey.Verify
open VG VG.AArch64 VG.Spec.MlDsa VG.Impl.MlDsa.AArch64.Call
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify

def forward (c : Impl.Sha3.AArch64.Callee) (P : Prims) (_p : Params) (a : Ptr) : Prog isa :=
  if c.pairedSha3 then Optimized.forward a else nttAt P (sc oSS) a

def keyRow (c : Impl.Sha3.AArch64.Callee) (P : Prims) (p : Params) (r : Nat) : Prog isa :=
  .ite (.nonzero .x .x22) (PreparedKey.copy (tmP p) (.x21, 1024 * r) 1024)
    (.seq (unpackT1At P (.x25, 32 + 320 * r) (tmP p)) (forward c P p (tmP p)))

def row (c : Impl.Sha3.AArch64.Callee) (P : Prims) (p : Params) (r : Nat) : Prog isa :=
  if c.pairedSha3 then
    .seq (Optimized.dot p r) (.seq (keyRow c P p r)
      (.seq (Optimized.product p) (.seq (Optimized.subtract p)
        (.seq (Optimized.inverse (wP p)) (Optimized.hintPack p r)))))
  else
    .seq (VG.Impl.MlDsa.AArch64.Verify.dot P p r) (.seq (keyRow c P p r)
      (.seq (mulAt P (tm2P p) (cP p) (tmP p)) (.seq (subAt P (wP p) (tm2P p))
        (.seq (invNttAt P (sc oSS) (wP p))
          (.seq (useHintAt P (hP p r) (wP p) p.γ₂ (w1P p))
            (simpleBitPackAt P (w1P p) (w1Max p)
              ((bP p).1, (bP p).2 + w1Len p * r) (w1Len p)))))))

def compute (c : Impl.Sha3.AArch64.Callee) (P : Prims) (p : Params) : Prog isa :=
  .seq (seqR (fun i => forward c P p (zP p i)) 0 p.ℓ)
    (.seq (forward c P p (cP p)) (.seq (seqR (row c P p) 0 p.k)
      (.seq (shake256With c [⟨.x26, 0, 64⟩, ⟨.x28, (bP p).2, p.k * w1Len p⟩]
        [⟨.x28, oCT, p.ctildeLen⟩]) (cmpAnd (sc oCT) (.x27, 0) p.ctildeLen))))

def core (c : Impl.Sha3.AArch64.Callee) (P : Prims) (p : Params) : Prog isa :=
  let body := .seq (hint P p) (ifOk (.seq (seqR (zOne P p) 0 p.ℓ)
    (ifOk (.seq (if c.pairedSha3 then OptimizedSamples.samples P p else samples P p)
      (compute c P p)))))
  .seq (.block pro) (.seq body (.block epi))

def withCache (c : Impl.Sha3.AArch64.Callee) (P : Prims) (p : Params) : Prog isa :=
  .frame (.push .x21) (.frame (.push .x22)
    (.seq (.block [.addImm .x .x21 .x4 0, .addImm .x .x22 .x5 0])
      (core c P p)) (.pop .x22)) (.pop .x21)

def entry (name : String) (code : Prog isa) (p : Params) (prepared : Bool) : Prog isa :=
  .frame (.push .x30)
    (.seq (.block (if prepared then lea .x4 .x0 p.pkLen ++ movV .x5 (1024 * p.k)
      else [.addImm .x .x4 .x0 0] ++ movV .x5 0)) (.call name code)) (.pop .x30)

end VG.Impl.MlDsa.AArch64.PreparedKey.Verify

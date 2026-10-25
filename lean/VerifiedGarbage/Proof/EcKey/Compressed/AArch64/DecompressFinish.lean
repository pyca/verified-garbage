module

public import VerifiedGarbage.Impl.EcKey.Compressed.AArch64.Decompress
import VerifiedGarbage.Proof.EcKey.AArch64.Main
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb

/-! # Reuse public-key derivation's verified output encoder -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 Spec.Weierstrass

 theorem decompressFinish_ok {c : Cfg} (hc : BaseCfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) {out : Addr} (hout : s.gpr .x20 = out)
    (hw : (⟨out, 1 + 2 * c.C.len⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨out, 1 + 2 * c.C.len⟩ ⟨base, size⟩)
    (hfit : out.toNat + (1 + 2 * c.C.len) ≤ 2 ^ 64)
    {g : Reg → BitVec 64} (hsv : Spill.Saved base g Cfg.saved s.mem) (b : Bool)
    (hf : word s.mem base (c.sl FLAG) = if b then BitVec.allOnes 64 else 0) :
    WP isa (.block (Impl.EcKey.Compressed.AArch64.decompressFinish c)) s fun t =>
      Spec.Ecdsa.bytesAt t.mem out (1 + 2 * c.C.len) =
        (if b then 4 :: (toBytes c.C.len (sv c base s E) ++
          toBytes c.C.len (sv c base s Impl.Ecdh.AArch64.QY))
          else List.replicate (1 + 2 * c.C.len) 0) ∧
      (t.gpr .x0).setWidth 32 = (if b then 1 else 0) ∧
      (∀ r ∈ Cfg.saved.map Prod.fst, t.gpr r = g r) :=
  VG.Proof.EcKey.AArch64.pointFinish_ok hc (by decide) (by decide) hs hout hfit hw hd hsv b hf

end VG.Proof.EcKey.Compressed.AArch64

module

public import VerifiedGarbage.Impl.EcKey.Compressed.X86.Decompress
import VerifiedGarbage.Proof.EcKey.X86.Finish
public import VerifiedGarbage.Proof.Ecdsa.X86.Layout

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86 Spec.Weierstrass
open VG.Proof.EcKey.X86 (pointFinish_ok)
variable {c : Cfg}

theorem decompressFinish_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size) {o32 : BitVec 32}
    (hout : readSrc s (.mem (Cfg.argOp 0)) = some o32) (hofit : o32.toNat + (1 + 2 * c.C.len) ≤ 2 ^ 32)
    (hw : (⟨o32.setWidth 64, 1 + 2 * c.C.len⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨o32.setWidth 64, 1 + 2 * c.C.len⟩ ⟨base, size⟩)
    {g : Reg → BitVec 32} (hsv : ∀ rd ∈ Cfg.saved, s.mem.readW (off base rd.2) 32 = g rd.1) (b : Bool)
    (hf : flagW c base s = mask32 (b = true)) :
    WP isa (.block (Impl.EcKey.Compressed.X86.decompressFinish c)) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem (o32.setWidth 64) (1 + 2 * c.C.len) =
        (if b then 4 :: (toBytes c.C.len (sv c base s E) ++ toBytes c.C.len (sv c base s Impl.Ecdh.X86.QY))
          else List.replicate (1 + 2 * c.C.len) 0) ∧
      s'.gpr .eax = (if b then 1 else 0) ∧
      (∀ rd ∈ Cfg.saved, s'.gpr rd.1 = g rd.1) ∧
      (∀ r, r ∉ [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] → s'.gpr r = s.gpr r) ∧
      Outside (o32.setWidth 64) 0 (1 + 2 * c.C.len) s.mem s'.mem :=
  pointFinish_ok hc (by decide) (by decide) hs hout hofit hw hd hsv b hf

end VG.Proof.EcKey.Compressed.X86

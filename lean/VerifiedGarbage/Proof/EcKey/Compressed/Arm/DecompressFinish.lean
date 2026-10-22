module

public import VerifiedGarbage.Impl.EcKey.Compressed.Arm.Decompress
public import VerifiedGarbage.Proof.EcKey.Arm.Finish

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm

open VG.Proof.Mont VG.Proof.Mont.Arm
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm Spec.Weierstrass
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.EcKey.Arm (pointFinish_ok)

variable {c : Cfg}

theorem decompressFinish_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size) {o32 : BitVec 32}
    (hlr : s.gpr .lr = o32) (hofit : o32.toNat + (1 + 2 * c.C.len) ≤ 2 ^ 32)
    (hw : (⟨State.addr o32, 1 + 2 * c.C.len⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨State.addr o32, 1 + 2 * c.C.len⟩ ⟨base, size⟩)
    {g : Reg → BitVec 32} (hsv : ∀ rd ∈ Cfg.saved, s.mem.readW (off base rd.2) 32 = g rd.1) (b : Bool)
    (hf : flagW c base s = mask32 (b = true)) :
    WP isa (.block (Impl.EcKey.Compressed.Arm.decompressFinish c)) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem (State.addr o32) (1 + 2 * c.C.len) =
        (if b then 4 :: (toBytes c.C.len (sv c base s E) ++ toBytes c.C.len (sv c base s Impl.Ecdh.Arm.QY))
          else List.replicate (1 + 2 * c.C.len) 0) ∧
      s'.gpr .r0 = (if b then 1 else 0) ∧
      (∀ rd ∈ Cfg.saved, s'.gpr rd.1 = g rd.1) ∧
      Rest [.r0, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr] s s' ∧
      Outside (State.addr o32) 0 (1 + 2 * c.C.len) s.mem s'.mem :=
  pointFinish_ok hc (by decide) (by decide) hs hlr hofit hw hd hsv b hf

end VG.Proof.EcKey.Compressed.Arm

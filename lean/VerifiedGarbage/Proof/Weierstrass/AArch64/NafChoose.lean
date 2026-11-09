module

public import VerifiedGarbage.Impl.Weierstrass.AArch64.NafPrep
public import VerifiedGarbage.Proof.Weierstrass.Naf5
public import VerifiedGarbage.Proof.Ed25519.AArch64.Step
import VerifiedGarbage.Proof.Mont.AArch64.Blocks
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Weierstrass.PointContract

@[expose] public section

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Weierstrass.AArch64 VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono read_x)

def nafRaw (x : BitVec 64) : BitVec 64 :=
  if x &&& 1=0 then 0 else (x &&& 31)-(((x &&& 31) &&& 16) <<< 1)

theorem nafMask (x : BitVec 64) : x &&& 31=BitVec.ofNat 64 (x.toNat%32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and,BitVec.toNat_ofNat]
  change x.toNat &&& (2^5-1) = (x.toNat%32)%2^64
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem nafRaw_eq {x : BitVec 64} {k j : Nat}
    (hx : x.toNat%32=Naf5.residual k j%32) : nafRaw x=BitVec.ofInt 64 (Naf5.digit k j) := by
  have H : ∀ r : Fin 32,
      (if r.val%2=0 then (0 : BitVec 64) else BitVec.ofNat 64 r.val-
        ((BitVec.ofNat 64 r.val &&& 16) <<< 1)) =
      BitVec.ofInt 64 (if r.val%2=0 then 0 else if r.val<16 then (r.val:Int) else (r.val:Int)-32) := by decide
  have he : x &&& 1=0 ↔ x.toNat%2=0 := by
    rw [←BitVec.toNat_inj]
    change x.toNat &&& 1=0 ↔ x.toNat%2=0
    rw [Nat.and_one_is_mod]
  simp only [nafRaw,he,nafMask,hx,Naf5.digit_mod32]
  have hp : x.toNat%2=Naf5.residual k j%32%2 := by omega
  rw [hp]
  change (if Naf5.residual k j%32%2=0 then (0:BitVec 64) else
    (x &&& (31:BitVec 64))-(BitVec.ofNat 64 (Naf5.residual k j%32) &&& 16) <<< 1)=_
  rw [nafMask,hx]
  exact H ⟨Naf5.residual k j%32,Nat.mod_lt _ (by decide)⟩

end VG.Proof.Weierstrass.AArch64

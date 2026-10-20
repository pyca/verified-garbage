module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Squeeze
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SeedSpec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit

/-! # Memory bytes of the initial paired matrix streams -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG
open VG.Proof.Sha3.AArch64.Neon

theorem Rate21.byte {m : Mem} {p : Addr} {A : Spec.Sha3.State} (h : Rate21 m p A)
    {j : Nat} (hj : j<168) : m (p+BitVec.ofNat 64 j)=Proof.Sha3.byteOf A j := by
  have hw := h (j/8) (by omega)
  have he := congrArg (fun v : BitVec 64 => v.extractLsb' (8*(j%8)) 8) hw
  change (m.read (p+BitVec.ofNat 64 (8*(j/8))) 8).extractLsb' (8*(j%8)) 8 = _ at he
  rw [Mem.extractLsb'_read m _ (by omega),BitVec.add_assoc,← BitVec.ofNat_add,
    show 8*(j/8)+j%8=j by omega] at he
  exact he

theorem Blocks.byte {m : Mem} {p : Addr} {k : Nat} {A : Spec.Sha3.State} (h : Blocks m p k A)
    {j : Nat} (hj : j<168*k) :
    m (p+BitVec.ofNat 64 j) = Proof.Sha3.byteOf (Proof.Sha3.iterF (j/168+1) A) (j%168) := by
  have he := (h (j/168) (by omega)).byte (j := j%168) (by omega)
  change m ((p+BitVec.ofNat 64 (168*(j/168)))+BitVec.ofNat 64 (j%168)) = _ at he
  rw [BitVec.add_assoc,← BitVec.ofNat_add,show 168*(j/168)+j%168=j by omega] at he
  exact he

theorem Blocks.xof {m input : Mem} {p seed : Addr} {a k blocks : Nat}
    (hk : 0<k) (hk256 : k≤256) (h : Blocks m p blocks (seedState input seed a k))
    {j : Nat} (hj : j<168*blocks) :
    m (p+BitVec.ofNat 64 j)=Proof.MlKem.xofByte (seedBytes input seed a k) j :=
  (h.byte hj).trans (stream_seedState input seed hk hk256 j)

/-- One continuation block can be passed directly to the incremental rejection loop. -/
theorem Rate21.xof {m input : Mem} {p seed : Addr} {a k block : Nat}
    (hk : 0<k) (hk256 : k≤256)
    (h : Rate21 m p (Proof.Sha3.iterF (block+1) (seedState input seed a k)))
    {j : Nat} (hj : j<168) :
    m (p+BitVec.ofNat 64 j)=Proof.MlKem.xofByte (seedBytes input seed a k) (168*block+j) :=
  (h.byte hj).trans (xofByte_seedState input seed hk hk256 hj).symm

end VG.Proof.MlKem.AArch64.Paired

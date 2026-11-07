module

public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.PairTail
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.InitCall
import VerifiedGarbage.Proof.Framework.Offset

/-! # Complete paired-noise operation -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon

def outOff (L : KemLay) (kg : Bool) (n : Nat) : Nat :=
 if n<L.k then (if kg then KG.sOff L n else KEM.yOff L n) else Impl.MlKem.AArch64.Noise.noiseOff L (n-L.k)
def transformed (L : KemLay) (kg : Bool) (n : Nat) : Bool := kg || n<L.k

theorem TailSetup.regions {s t : State} {p f g w : Addr} (h : TailSetup s p f g w)
    (hr : t.rd=s.rd) (hw : t.wr=s.wr) : TailSetup t p f g w := by
  rcases h with ⟨a,b,c,d,e,f,g,j,k,l,m,n,o,q,r,v⟩
  exact ⟨by simpa only [hr,hw] using a,by simpa only [hw] using b,
    by simpa only [hw] using c,by simpa only [hw] using d,by simpa only [hr,hw] using e,
    by simpa only [hr,hw] using f,by simpa only [hr,hw] using g,
    by simpa only [hw] using j,by simpa only [hw] using k,l,m,n,o,q,r,v⟩

end VG.Proof.MlKem.AArch64.Noise

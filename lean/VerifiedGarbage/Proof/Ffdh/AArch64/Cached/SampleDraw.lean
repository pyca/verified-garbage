module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SampleWidth
public import VerifiedGarbage.Proof.Ffdh.AArch64.GenerateKey.Cut
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Omega

/-! The existing constant-time byte-copy loop realizes the reviewed modular entropy cut. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Ffdh

theorem sampleDraw_bytes {s t : State} {rp xp : Addr} {rb : List Byte} {k ld : Nat} {msk : Addr}
 (inv : VG.Proof.Ffdh.AArch64.GenerateKey.CInv s rp xp rb ld msk k t)
 (length : rb.length=k) (inside : ld<k) :
 Spec.Rsa.bytesAt t.mem xp k=KeyScalar.cut rb ld (msk.setWidth 8) := by
 apply List.ext_getElem
 · simp only [Spec.Rsa.bytesAt,List.length_map,List.length_range,KeyScalar.cut_length _ (length ▸ inside)]
   exact length.symm
 · intro i hi _
   have bound : i<k := by simpa only [Spec.Rsa.bytesAt,List.length_map,List.length_range] using hi
   simp only [Spec.Rsa.bytesAt,List.getElem_map,List.getElem_range]
   rw [inv.bytes i bound,KeyScalar.cut_get _ (length ▸ inside) (by omega : i<rb.length)]
   unfold VG.Proof.Ffdh.AArch64.GenerateKey.cb
   simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by omega : i<rb.length),Option.getD_some]

theorem sampleDraw_ok {s : State} {rp xp : Addr} {rb : List Byte} {k N : Nat}
 (positive : 0<k) (size : k<2^31) (widthPositive : 0<N) (widthFit : N≤8*k) (length : rb.length=k)
 (random : s.gpr .x1=rp) (output : s.gpr .x2=xp) (index : s.gpr .x10=0#64)
 (skip : s.gpr .x11=BitVec.ofNat 64 (k-(N+7)/8)) (mask : s.gpr .x12=sampleMask N)
 (allOnes : s.gpr .x13=255#64) (zero : s.gpr .x7=0#64) (count : s.gpr .x14=BitVec.ofNat 64 k)
 (readable : ∀ i<k,InRegions (s.rd++s.wr) (rp+BitVec.ofNat 64 i) 1)
 (bytes : ∀ i<k,s.mem (rp+BitVec.ofNat 64 i)=rb.getD i 0)
 (writable : ∀ i<k,InRegions s.wr (xp+BitVec.ofNat 64 i) 1)
 (separate : ∀ i<k,∀ j<k,rp+BitVec.ofNat 64 i≠xp+BitVec.ofNat 64 j) :
 WP isa (countLoop .x14 VG.Impl.Ffdh.AArch64.Domain.GenerateKey.cutBody) s fun t =>
 Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem xp k)=Spec.Rsa.os2ip rb%2^N ∧
 VG.Proof.Ffdh.AArch64.GenerateKey.CInv s rp xp rb (k-(N+7)/8) (sampleMask N) k t := by
 have inside : k-(N+7)/8<k := by omega
 refine WP.mono (VG.Proof.Ffdh.AArch64.GenerateKey.cut_ok (by omega) size inside random output
  index skip mask allOnes zero count readable bytes writable separate) ?_
 intro t inv
 refine ⟨?_,inv⟩
 rw [sampleDraw_bytes inv length inside,sample_mask widthPositive]
 have width := sample_width widthPositive
 rw [←width]
 have cut := ScalarWidth.cut_value (bits:=N) (by omega : 0<rb.length) (by omega : N≤8*rb.length)
 rw [length] at cut
 exact cut

end VG.Proof.Ffdh.AArch64.Cached

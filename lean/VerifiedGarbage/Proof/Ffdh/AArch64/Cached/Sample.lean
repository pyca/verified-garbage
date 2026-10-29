module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SourceSlices
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.MemoryState
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.OutputFrame
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SampleMask
public import VerifiedGarbage.Proof.Ffdh.VettedPolicy
public import VerifiedGarbage.Proof.Ffdh.AArch64.GenerateKey.Cut

import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.WorkspaceState
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.GetElem
/-! The full native sampler applies the public policy to the complete entropy draw. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/SampleWidth.lean`, which only this module imported.
section

/-! The native mask and byte count encode exactly the reviewed sampler width. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG
open VG.Proof.Ffdh

theorem sample_width {N : Nat} (positive : 0<N) : ScalarWidth.width N=(N+7)/8 := by
 unfold ScalarWidth.width
 omega

theorem sample_headBits {N : Nat} (positive : 0<N) : ScalarWidth.headBits N=(N-1)%8+1 := by
 unfold ScalarWidth.headBits
 rw [sample_width positive]
 omega

theorem sample_mask {N : Nat} (positive : 0<N) : (sampleMask N).setWidth 8=ScalarWidth.mask N := by
 unfold sampleMask ScalarWidth.mask
 rw [sample_headBits positive]
 apply BitVec.eq_of_toNat_eq
 simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]
 omega

theorem sample_octets {a : Spec.Ffdh.Parameters} {r : List Byte}
 (positive : 0<Spec.Ffdh.generationScalarBits a) :
 KeyScalar.cut r (r.length-(Spec.Ffdh.generationScalarBits a+7)/8)
  ((sampleMask (Spec.Ffdh.generationScalarBits a)).setWidth 8)=VettedPolicy.octets a r := by
 rw [sample_mask positive]
 unfold VettedPolicy.octets
 rw [sample_width positive]

end VG.Proof.Ffdh.AArch64.Cached
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/SampleDraw.lean`, which only this module imported.
section

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
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem sample_ok {s : State} {B xp rp : Addr} {Z w k N : Nat} {mi : BitVec 64} {rb : List Byte}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (positive : 0<k) (size : k<2^31)
 (bitsPositive : 0<N) (bitsBound : N≤8192) (width : N≤8*k) (rbLength : rb.length=k)
 (bits : word s.mem B (8*sBits)=BitVec.ofNat 64 N) (bytes : word s.mem B (8*sBytes)=BitVec.ofNat 64 ((N+7)/8))
 (length : word s.mem B (8*sLen)=BitVec.ofNat 64 k) (x : word s.mem B (8*sX)=xp) (random : word s.mem B (8*sRand)=rp)
 (source : Src s B Z rp rb) (writable : ∀ i<k,InRegions s.wr (xp+BitVec.ofNat 64 i) 1)
 (outside : ∀ i<k,Z≤ofs B (xp+BitVec.ofNat 64 i))
 (separate : ∀ i<k,∀ j<k,rp+BitVec.ofNat 64 i≠xp+BitVec.ofNat 64 j) :
 WP isa Generate.sample s fun t =>
 Good t B Z w mi ∧
 Spec.Rsa.bytesAt t.mem xp k=VG.Proof.Ffdh.KeyScalar.cut rb (k-(N+7)/8) ((sampleMask N).setWidth 8) ∧
 Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem xp k)=Spec.Rsa.os2ip rb%2^N ∧
 (∀ q,ofs B q<Z→t.mem q=(s.mem.writeW (off B (8*sMask)) (sampleMask N)) q) ∧
 Frame [⟨B,Z⟩,⟨xp,k⟩] s.mem t.mem ∧ Keep mmRegs s t := by
 have room256 : 256≤Z := by dsimp only [slot,hdrBytes] at room;omega
 unfold Generate.sample
 rw [WP.seq_iff]
 refine WP.mono (sampleMask_ok good.scr room256 good.x0 bitsPositive bitsBound bits) ?_
 rintro a ⟨maskA,maskHeaderA,memA,frameA,restA⟩
 have goodA := good_after_header good (by decide) (by decide) frameA restA ((restA.gpr .x0 (by decide)).trans good.x0)
 have inscrA : InScr B Z s.mem a.mem := InScr.of_outside frameA (by have := hdr_lt_slot w 8 (show sMask<32 by decide);omega)
 rw [WP.seq_iff]
 have headerA (i : Nat) (hi : i<32) (different : i≠sMask) : word a.mem B (8*i)=word s.mem B (8*i) :=
  header_other frameA (by decide) hi different
 have subtract : BitVec.ofNat 64 k-BitVec.ofNat 64 ((N+7)/8)=BitVec.ofNat 64 (k-(N+7)/8) :=
  BitVec.ofNat_sub_ofNat_of_le k ((N+7)/8) (by omega) (by omega)
 refine WP.mono (WP.keep [.x1,.x2,.x7,.x10,.x11,.x13,.x14] (Q:=fun b =>
  b.gpr .x1=rp ∧ b.gpr .x2=xp ∧ b.gpr .x10=0#64 ∧ b.gpr .x11=BitVec.ofNat 64 (k-(N+7)/8) ∧
  b.gpr .x13=255#64 ∧ b.gpr .x7=0#64 ∧ b.gpr .x14=BitVec.ofNat 64 k ∧ b.mem=a.mem) ?_ rfl rfl rfl) ?_
 · brun [goodA.x0,hdr_enc (show sLen<32 by decide),hdr_enc (show sBytes<32 by decide),hdr_enc (show sX<32 by decide),hdr_enc (show sRand<32 by decide),
    header_read goodA room (show sLen<32 by decide),header_read goodA room (show sBytes<32 by decide),
    header_read goodA room (show sX<32 by decide),header_read goodA room (show sRand<32 by decide),
    (headerA sLen (by decide) (by decide)).trans length,(headerA sBytes (by decide) (by decide)).trans bytes,
    (headerA sX (by decide) (by decide)).trans x,(headerA sRand (by decide) (by decide)).trans random,subtract]
 · rintro b ⟨⟨ptrB,outB,indexB,skipB,onesB,zeroB,countB,memB⟩,restB⟩
   have total := restA.trans restB
   have sourceB := (source.congrK inscrA restA).congrK (fun q _ =>by rw [memB]) restB
   refine WP.mono (sampleDraw_ok positive size bitsPositive width rbLength ptrB outB indexB skipB
    ((restB.gpr .x12 (by decide)).trans maskA) onesB zeroB countB
    (fun i hi =>sourceB.rd i (by omega)) (fun i hi =>(src_source sourceB).bytes i (by omega))
    (fun i hi =>by rw [total.wr];exact writable i hi) separate) ?_
   rintro t ⟨valueT,inv⟩
   have sameScratch (q : Addr) (hq : ofs B q<Z) : t.mem q=a.mem q := by
    rw [inv.frame q ?_,memB]
    intro i hi eq
    have sep : k≤ofs xp q := le_ofs_of_sep outside hq
    rw [eq,show ofs xp (xp+BitVec.ofNat 64 i)=i from Mem.sub_ofNat_toNat _ (by omega)] at sep
    omega
   have rest : Keep mmRegs s t := (total.trans inv.keep).mono (by simp [mmRegs])
   have goodT : Good t B Z w mi :=
    ⟨good.scr.congr rest.wr,(rest.gpr .x0 (by simp [mmRegs])).trans good.x0,
     (workspace_word (by have := good.scr.nowrap;omega) sameScratch (by have := hdr_lt_slot w 8 (show sW<32 by decide);omega)).trans goodA.hdr.hw,
     (workspace_word (by have := good.scr.nowrap;omega) sameScratch (by have := hdr_lt_slot w 8 (show sMinv<32 by decide);omega)).trans goodA.hdr.hminv,
     fun i hi =>(workspace_word (by have := good.scr.nowrap;omega) sameScratch (by have := hdr_lt_slot w 8 (show sArr i<32 by unfold sArr;omega);omega)).trans (goodA.hdr.harr i hi)⟩
   have outsideX : Outside xp 0 k b.mem t.mem := by
    intro q hq
    apply inv.frame q
    intro i hi eq
    subst q
    rw [show ofs xp (xp+BitVec.ofNat 64 i)=i from Mem.sub_ofNat_toNat _ (by omega)] at hq
    omega
   have frameMask : Frame [⟨B,Z⟩,⟨xp,k⟩] s.mem a.mem := outside_frame_member (ptr:=B) (k:=Z)
    (fun q h =>inscrA q (by omega)) (by simp)
   have frameOutput : Frame [⟨B,Z⟩,⟨xp,k⟩] a.mem t.mem := by
    rw [←memB];exact outside_frame_member outsideX (by simp)
   exact ⟨goodT,sampleDraw_bytes inv rbLength (by omega),valueT,
    fun q hq =>(sameScratch q hq).trans (by rw [memA]),frameMask.trans frameOutput,rest⟩

end VG.Proof.Ffdh.AArch64.Cached

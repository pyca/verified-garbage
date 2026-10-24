module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SampleDraw
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SourceSlices
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.WorkspaceState
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.MemoryState
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.OutputFrame
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! The full native sampler applies the public policy to the complete entropy draw. -/
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

module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.MaskX
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.WorkspaceState
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.OutputFrame
public import VerifiedGarbage.Proof.Bignum.AArch64.Store
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! Serialize both outputs with the same success mask and return exactly 1 or 3. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem finish_ok {s : State} {B xp yp : Addr} {Z w k : Nat} {mi : BitVec 64} {c : Bool}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (words : w=(k+7)/8) (positive : 0<k) (size : k<2^31)
 (x : word s.mem B (8*sX)=xp) (y : word s.mem B (8*sY)=yp) (length : word s.mem B (8*sLen)=BitVec.ofNat 64 k)
 (flag : word s.mem B (8*sTmp)=BitVec.ofNat 64 c.toNat)
 (writeX : ∀ i<k,InRegions s.wr (xp+BitVec.ofNat 64 i) 1)
 (writeY : ∀ i<k,InRegions s.wr (yp+BitVec.ofNat 64 i) 1)
 (outsideX : ∀ i<k,Z≤ofs B (xp+BitVec.ofNat 64 i))
 (outsideY : ∀ i<k,Z≤ofs B (yp+BitVec.ofNat 64 i))
 (separate : ∀ i<k,k≤ofs yp (xp+BitVec.ofNat 64 i)) :
 WP isa Generate.finish s fun t =>
 t.gpr .x0=(if c then 1#64 else 3#64) ∧
 Spec.Rsa.bytesAt t.mem xp k=(if c then Spec.Rsa.bytesAt s.mem xp k else List.replicate k 0) ∧
 Spec.Rsa.bytesAt t.mem yp k=Spec.Rsa.i2osp (if c then wv s.mem B (slot w 6) w else 0) k ∧
 Frame [⟨xp,k⟩,⟨yp,k⟩] s.mem t.mem ∧ Keep (.x0::mmRegs) s t := by
 have room256 : 256≤Z := by unfold slot hdrBytes at room;omega
 have yRoom := Nat.le_trans (slot_le (w:=w) (show 6<8 by decide)) room
 have wPositive : 0<w := by rw [words];omega
 unfold Generate.finish
 simp only [seqs]
 rw [WP.seq_iff]
 refine WP.mono (maskX_ok good.scr room256 good.x0 positive size x length flag writeX outsideX) ?_
 rintro a ⟨bytesX,maskA,frameA,sameA,restA⟩
 have headerA (i : Nat) (hi : i<32) : word a.mem B (8*i)=word s.mem B (8*i) :=
  workspace_word (by have := good.scr.nowrap;omega) sameA (by have := hdr_lt_slot w 8 hi;omega)
 have goodA : Good a B Z w mi :=
  ⟨good.scr.congr restA.wr,(restA.gpr .x0 (by decide)).trans good.x0,
   (headerA sW (by decide)).trans good.hdr.hw,(headerA sMinv (by decide)).trans good.hdr.hminv,
   fun i hi =>(headerA (sArr i) (by unfold sArr;omega)).trans (good.hdr.harr i hi)⟩
 have arrayA : wv a.mem B (slot w 6) w=wv s.mem B (slot w 6) w := by
  apply wv_congr
  intro i hi
  exact workspace_word (by have := good.scr.nowrap;omega) sameA (by omega)
 rw [WP.seq_iff]
 refine WP.mono (WP.keep [.x8,.x1,.x9] (Q:=fun b =>b.gpr .x8=off B (slot w 6) ∧
  b.gpr .x1=yp+BitVec.ofNat 64 k ∧ b.gpr .x9=BitVec.ofNat 64 k ∧ b.mem=a.mem) ?_ rfl rfl rfl) ?_
 · brun [goodA.x0,hdr_enc (show sArr 6<32 by decide),hdr_enc (show sY<32 by decide),hdr_enc (show sLen<32 by decide),
    header_read goodA room (show sArr 6<32 by decide),header_read goodA room (show sY<32 by decide),
    header_read goodA room (show sLen<32 by decide),goodA.hdr.harr 6 (by decide),
    (headerA sY (by decide)).trans y,(headerA sLen (by decide)).trans length]
 · rintro b ⟨⟨srcB,dstB,countB,memB⟩,restB⟩
   have before := restA.trans restB
   rw [WP.seq_iff]
   refine WP.mono (storeBE_ok (good.scr.congr before.wr) srcB dstB countB
    ((restB.gpr .x15 (by decide)).trans maskA) (by omega) size words (by omega)
    (fun i hi =>by rw [before.wr];exact writeY i hi) outsideY) ?_
   rintro d ⟨bytesY,storeFrame,_,_,restD⟩
   have frameD : Outside yp 0 k b.mem d.mem := by
    intro q hq
    apply storeFrame q
    intro i hi eq
    subst q
    rw [show ofs yp (yp+BitVec.ofNat 64 i)=i from Mem.sub_ofNat_toNat _ (by omega)] at hq
    omega
   have sameD (q : Addr) (hq : ofs B q<Z) : d.mem q=s.mem q := by
    rw [frameD q (Or.inr (by have sep : k≤ofs yp q :=le_ofs_of_sep outsideY hq;omega)),memB]
    exact sameA q hq
   have flagD : word d.mem B (8*sTmp)=BitVec.ofNat 64 c.toNat :=
    (workspace_word (by have := good.scr.nowrap;omega) sameD
     (by have := hdr_lt_slot w 8 (show sTmp<32 by decide);omega)).trans flag
   have xD : Spec.Rsa.bytesAt d.mem xp k=(if c then Spec.Rsa.bytesAt s.mem xp k else List.replicate k 0) := by
    rw [←bytesX]
    apply List.ext_getElem
    · simp only [Spec.Rsa.bytesAt,List.length_map,List.length_range]
    · intro i hi _
      have bound : i<k := by simpa only [Spec.Rsa.bytesAt,List.length_map,List.length_range] using hi
      simp only [Spec.Rsa.bytesAt,List.getElem_map,List.getElem_range]
      rw [frameD _ (Or.inr (by have := separate i bound;omega)),memB]
   have yD : Spec.Rsa.bytesAt d.mem yp k=Spec.Rsa.i2osp (if c then wv s.mem B (slot w 6) w else 0) k := by
    change (List.range k).map (fun i =>d.mem (yp+BitVec.ofNat 64 i))=_
    rw [bytesY,memB,arrayA]
   have total := before.trans restD
   have ret : (3#64 : Addr)-(BitVec.ofNat 64 c.toNat <<< 1)=(if c then 1#64 else 3#64) := by cases c <;>rfl
   refine WP.mono (WP.keep [.x9,.x0] (Q:=fun t =>t.gpr .x0=(if c then 1#64 else 3#64) ∧ t.mem=d.mem) ?_ rfl rfl rfl) ?_
   · brun [(total.gpr .x0 (by simp)).trans good.x0,hdr_enc (show sTmp<32 by decide),flagD,
      (good.scr.congr total.wr).ld (d:=8*sTmp) (by have := hdr_lt_slot w 8 (show sTmp<32 by decide);omega),ret]
     exact ret
   · rintro t ⟨⟨status,mem⟩,rest⟩
     have lastFrame : Outside yp 0 k a.mem d.mem := by rw [←memB];exact frameD
     exact ⟨status,by rw [mem];exact xD,by rw [mem];exact yD,
      by rw [mem];exact (outside_frame_member frameA (by simp)).trans (outside_frame_member lastFrame (by simp)),
      (total.trans rest).mono (by simp [mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached

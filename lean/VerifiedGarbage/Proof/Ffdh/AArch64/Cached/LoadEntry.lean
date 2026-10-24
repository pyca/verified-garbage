module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.EntryPointer
public import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! Load an immutable canonical table entry into a native Montgomery operand array. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem loadEntry_ok {s : State} {B ctx : Addr} {Z w a j : Nat} {mi : BitVec 64}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (positive : 0<w) (size : w<2^31) (array : a<8)
 (context : word s.mem B (8*sCtx)=ctx) (digit : s.gpr .x3=BitVec.ofNat 64 j)
 (readable : ∀ i<w,InRegions (s.rd++s.wr) (off ctx (entryOffset w j+8*i)) 8)
 (outside : ∀ i<8*w,Z≤ofs B (off ctx (entryOffset w j)+BitVec.ofNat 64 i)) :
 WP isa (loadEntry a) s fun t =>
 Good t B Z w mi ∧ wv t.mem B (slot w a) w=wv s.mem ctx (entryOffset w j) w ∧
 Arrays B w [a] s.mem t.mem ∧ Keep mmRegs s t := by
 have arrHdr : sArr a<32 := by unfold sArr;omega
 have arrayRoom : slot w a+8*(w+2)≤Z := Nat.le_trans (slot_le array) room
 unfold loadEntry
 rw [WP.seq_iff,WP.block_append_iff]
 refine WP.mono (entryPtr_ok good room context digit) ?_
 rintro u ⟨⟨ptrU,countU,memU⟩,restU⟩
 refine WP.mono (WP.keep [.x16,.x17] (Q:=fun v =>v.gpr .x16=off ctx (entryOffset w j) ∧
  v.gpr .x17=off B (slot w a) ∧ v.mem=u.mem) ?_ rfl rfl rfl) ?_
 · brun [restU.rd,restU.wr,(restU.gpr .x0 (by decide)).trans good.x0,hdr_enc arrHdr,
    good.scr.ld (d:=8*sArr a) (by have := hdr_lt_slot w 8 arrHdr;omega),memU,good.hdr.harr a array,ptrU]
 · rintro v ⟨⟨srcV,dstV,memV⟩,restV⟩
   have rest := restU.trans restV
   have mem : v.mem=s.mem := memV.trans memU
   refine WP.mono (copyWords_ok (S:=ctx) (D:=B) (eS:=entryOffset w j) (eD:=slot w a) (w:=w) srcV dstV
    ((restV.gpr .x12 (by decide)).trans countU) (by omega) size (by have := good.scr.nowrap;omega)
    (fun i hi => by rw [rest.rd,rest.wr];exact readable i hi)
    (fun i hi => by rw [rest.wr];exact good.scr.st (by omega))
    (fun i hi b hb => Or.inr (by
     have sep := outside (8*i+b) (by omega)
     have same : off ctx (entryOffset w j+8*i)+BitVec.ofNat 64 b=
       off ctx (entryOffset w j)+BitVec.ofNat 64 (8*i+b) := by simp only [off,BitVec.ofNat_add,BitVec.add_assoc]
     rw [same]
     omega))) ?_
   rintro t ⟨value,_,frame,_,_,restT⟩
   have totalRest : Keep mmRegs s t := (rest.trans restT).mono (by simp [mmRegs])
   have arrays : Arrays B w [a] s.mem t.mem := by
    apply Arrays.of_outside (j:=a) (by simp) (o:=slot w a) (n:=8*w)
    · rw [←mem];exact frame
    · omega
    · omega
   refine ⟨good_after_arrays good arrays totalRest ((totalRest.gpr .x0 (by simp [mmRegs])).trans good.x0),?_,arrays,totalRest⟩
   rw [mem] at value
   exact value

end VG.Proof.Ffdh.AArch64.Cached

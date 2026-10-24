module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Const
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! Reuse native big-endian byte loading for the checked public domain and sampled scalar. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem loadArray_ok {s : State} {B src : Addr} {Z w k a : Nat} {mi : BitVec 64} {bs : List Byte}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (words : w=(k+7)/8) (positive : 0<k)
 (size : k<2^31) (array : a<8) (source : Src s B Z src bs) (length : bs.length=k)
 (pointer : s.gpr .x1=src) (count : s.gpr .x2=BitVec.ofNat 64 k) :
 WP isa (VG.Impl.Ffdh.AArch64.Cached.load a) s fun t =>
 Good t B Z w mi ∧ wv t.mem B (slot w a) w=Spec.Rsa.os2ip bs ∧ Arrays B w [a] s.mem t.mem ∧ Keep mmRegs s t := by
 have arrHdr : sArr a<32 := by unfold sArr;omega
 unfold VG.Impl.Ffdh.AArch64.Cached.load
 rw [WP.seq_iff]
 refine WP.mono (WP.keep [.x8,.x12] (Q:=fun u =>u.gpr .x8=off B (slot w a) ∧ u.mem=s.mem) ?_ rfl rfl rfl) ?_
 · brun [good.x0,hdr_enc arrHdr,hdr_enc (show sW<32 by decide),
    good.scr.ld (d:=8*sArr a) (by have := hdr_lt_slot w 8 arrHdr;omega),
    good.scr.ld (d:=8*sW) (by have := hdr_lt_slot w 8 (show sW<32 by decide);omega),good.hdr.harr a array]
 · rintro u ⟨⟨dest,mem⟩,rest⟩
   have sourceU := source.congrK (fun x _ => by rw [mem]) rest
   have destW : u.gpr .x8=off B (slot ((k+7)/8) a) := by rw [words] at dest;exact dest
   refine WP.mono (loadArr_ok (good.scr.congr rest.wr) array (by rw [←words];exact room) sourceU
    length (by omega) size ((rest.gpr .x1 (by decide)).trans pointer)
    ((rest.gpr .x2 (by decide)).trans count) destW) ?_
   rintro t ⟨value,frame,keep⟩
   rw [←words,mem] at frame
   rw [←words] at value
   have totalRest : Keep mmRegs s t := (rest.trans keep).mono (by simp [mmRegs])
   exact ⟨good_after_arrays good frame totalRest ((totalRest.gpr .x0 (by simp [mmRegs])).trans good.x0),value,frame,totalRest⟩

end VG.Proof.Ffdh.AArch64.Cached

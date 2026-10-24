module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SelectLayout
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Const
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! Complete canonical-context selection into the existing Montgomery operand array. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem select_ok {s : State} {B table : Addr} {Z w v : Nat} {mi : BitVec 64}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (positive : 0<w) (width : w<2^31) (hv : v<32)
 (tablePtr : word s.mem B (8*VG.Impl.Ffdh.AArch64.Cached.sTab)=table)
 (digit : word s.mem B (8*VG.Impl.Ffdh.AArch64.Cached.sD)=BitVec.ofNat 64 v)
 (readSource : ∀ j<32, ∀ i<w, InRegions (s.rd++s.wr) (off table (8*w*j+8*i)) 8)
 (sourceOutside : ∀ j<32, ∀ i<w, ∀ b<8, Z≤ofs B (off table (8*w*j+8*i)+BitVec.ofNat 64 b)) :
 WP isa VG.Impl.Ffdh.AArch64.Cached.Comb.select s fun t =>
 Good t B Z w mi ∧ wv t.mem B (slot w 5) w=wv s.mem table (8*w*v) w ∧
 Arrays B w [5] s.mem t.mem ∧ Keep mmRegs s t := by
 have convert (m : Mem) (i : Nat) : word m (off B (slot w 5)) (8*i)=word m B (slot w 5+8*i) := by
  simp only [word,VG.Proof.Bignum.off_off]
 have nowrap : slot w 5+8*(w+2)≤2^64 := by
  have := good.scr.nowrap
  have := slot_le (w:=w) (by decide : 5<8)
  omega
 unfold VG.Impl.Ffdh.AArch64.Cached.Comb.select
 rw [WP.seq_iff]
 refine WP.mono (const_ok good room positive width (by decide : 5<8) (by decide : 0<2^16)) ?_
 rintro u ⟨goodU,zeroU,frameU,restU⟩
 have arraysU : Arrays B w [5] s.mem u.mem := Arrays.of_outside (j:=5) (by simp) frameU (by omega) (by omega)
 have headerU (i : Nat) (hi : i<32) : word u.mem B (8*i)=word s.mem B (8*i) :=
  frameU.word (Or.inl (hdr_lt_slot w 5 hi)) (by omega)
 rw [WP.seq_iff]
 refine WP.mono (WP.keep [.x9,.x10,.x11] (Q:=fun z =>
  z.gpr .x9=table ∧ z.gpr .x10=BitVec.ofNat 64 v ∧ z.gpr .x11=0#64 ∧ z.mem=u.mem)
  ?_ rfl rfl rfl) ?_
 · brun [goodU.x0,hdr_enc (show VG.Impl.Ffdh.AArch64.Cached.sTab<32 by decide),
   hdr_enc (show VG.Impl.Ffdh.AArch64.Cached.sD<32 by decide),
   goodU.scr.ld (d:=8*VG.Impl.Ffdh.AArch64.Cached.sTab)
    (by have := hdr_lt_slot w 8 (show VG.Impl.Ffdh.AArch64.Cached.sTab<32 by decide);omega),
   goodU.scr.ld (d:=8*VG.Impl.Ffdh.AArch64.Cached.sD)
    (by have := hdr_lt_slot w 8 (show VG.Impl.Ffdh.AArch64.Cached.sD<32 by decide);omega),
   headerU VG.Impl.Ffdh.AArch64.Cached.sTab (by decide),
   headerU VG.Impl.Ffdh.AArch64.Cached.sD (by decide),tablePtr,digit]
 · rintro z ⟨⟨pointerZ,digitZ,candidateZ,memZ⟩,restZ⟩
   have restUZ := restU.trans restZ
   have goodZ : Good z B Z w mi :=
    ⟨goodU.scr.congr restZ.wr,(restZ.gpr .x0 (by decide)).trans goodU.x0,memZ ▸ goodU.hdr⟩
   have envZ : SelectEnv B table (off B (slot w 5)) w z := selectEnv_good goodZ room positive
    (fun j hj i hi => by rw [restUZ.rd,restUZ.wr];exact readSource j hj i hi) sourceOutside
   have zeros : ∀ i<w, word z.mem (off B (slot w 5)) (8*i)=0#64 := by
    intro i hi
    rw [convert,memZ]
    exact (wv_eq_zero_iff _ _ _ _).mp zeroU i hi
   refine WP.mono (selectScan_ok z envZ positive (by omega) hv pointerZ digitZ candidateZ zeros) ?_
   rintro t ⟨_,words,frame,restT⟩
   have frameZ : Outside B (slot w 5) (8*w) z.mem t.mem :=
    outside_to_workspace (by omega) (by omega) frame
   have arraysZ : Arrays B w [5] z.mem t.mem := Arrays.of_outside (j:=5) (by simp) frameZ (by omega) (by omega)
   have totalArrays : Arrays B w [5] s.mem t.mem := by
    rw [memZ] at arraysZ
    exact arraysU.trans arraysZ
   have totalRest : Keep mmRegs s t := (restUZ.trans restT).mono (by simp [selectClobbers,mmRegs])
   refine ⟨good_after_arrays good totalArrays totalRest
    ((totalRest.gpr .x0 (by decide)).trans good.x0),?_,totalArrays,totalRest⟩
   apply wv_congr2
   intro i hi
   rw [←convert,words i hi,memZ]
   exact Mem.readW_congr fun b hb => InScr.of_arrays arraysU room (by simp) _ (sourceOutside v hv i hi b hb)

end VG.Proof.Ffdh.AArch64.Cached

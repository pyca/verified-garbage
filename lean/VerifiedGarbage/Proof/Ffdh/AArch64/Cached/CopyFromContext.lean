module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Const
public import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Framework.Omega

/-! Import a pointer-free canonical limb range into a native arithmetic array. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem copyFromContext_ok {s : State} {B ctx : Addr} {Z w a d : Nat} {mi : BitVec 64}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (positive : 0<w) (size : w<2^31) (array : a<8)
 (source : s.gpr .x16=off ctx d) (output : s.gpr .x17=off B (slot w a)) (count : s.gpr .x12=BitVec.ofNat 64 w)
 (readable : ∀ i<w,InRegions (s.rd++s.wr) (off ctx (d+8*i)) 8)
 (outside : ∀ i<8*w,Z≤ofs B (off ctx d+BitVec.ofNat 64 i)) :
 WP isa copyWords s fun t =>
 Good t B Z w mi ∧ wv t.mem B (slot w a) w=wv s.mem ctx d w ∧ Arrays B w [a] s.mem t.mem ∧
 t.gpr .x16=off ctx (d+8*w) ∧ Keep mmRegs s t := by
 have arrayRoom := Nat.le_trans (slot_le (w:=w) array) room
 have fit : slot w a+8*w≤2^64 := by have := good.scr.nowrap;omega
 refine WP.mono (copyWords_ok source output count (by omega) size fit readable
  (fun i hi =>good.scr.st (by omega)) (fun i hi b hb =>Or.inr (by
   have sep := outside (8*i+b) (by omega)
   have eq : off ctx (d+8*i)+BitVec.ofNat 64 b=off ctx d+BitVec.ofNat 64 (8*i+b) := by
    simp only [off,BitVec.ofNat_add,BitVec.add_assoc]
   rw [eq]
   omega))) ?_
 rintro t ⟨value,_,frame,pointer,_,rest⟩
 have arrays : Arrays B w [a] s.mem t.mem :=
  Arrays.of_outside (j:=a) (by simp) frame (by omega) (by omega)
 have total : Keep mmRegs s t := rest.mono (by simp [mmRegs])
 exact ⟨good_after_arrays good arrays total ((total.gpr .x0 (by simp [mmRegs])).trans good.x0),value,arrays,pointer,total⟩

end VG.Proof.Ffdh.AArch64.Cached

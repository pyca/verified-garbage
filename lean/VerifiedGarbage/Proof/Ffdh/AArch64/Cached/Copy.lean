module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Const
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Framework.Omega

/-! Native array copies reuse the existing verified CRT copy implementation. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem copy_ok {s : State} {B : Addr} {Z w a b : Nat} {mi : BitVec 64}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (positive : 0<w) (size : w<2^31)
 (ha : a<8) (hb : b<8) (different : a≠b) :
 WP isa (VG.Impl.Ffdh.AArch64.Cached.copy a b) s fun t =>
 Good t B Z w mi ∧ wv t.mem B (slot w a) w=wv s.mem B (slot w b) w ∧
 Arrays B w [a] s.mem t.mem ∧ Keep mmRegs s t := by
 have equality : VG.Impl.Ffdh.AArch64.Cached.copy a b=seqs (VG.Impl.Rsa.AArch64.Crt.copyArr a b) := rfl
 rw [equality]
 refine WP.mono (copyArr_ok good room (by omega) size ha hb different) ?_
 rintro t ⟨value,outside,rest⟩
 have frame : Arrays B w [a] s.mem t.mem := Arrays.of_outside (j:=a) (by simp) outside
  (by omega) (by have := good.scr.nowrap;have := slot_le (w:=w) ha;omega)
 exact ⟨good_after_arrays good frame rest ((rest.gpr .x0 (by simp [mmRegs])).trans good.x0),value,frame,rest⟩

end VG.Proof.Ffdh.AArch64.Cached

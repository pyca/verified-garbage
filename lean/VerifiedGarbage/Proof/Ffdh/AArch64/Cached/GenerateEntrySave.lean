module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Generate
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header
import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! Save the cached attempt's register and stack arguments in public scratch controls. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def generationSaveMemory (m : Mem) (B xp yp dp dl k rp ctx : Addr) : Mem :=
 ((((((m.writeW (off B (8*sX)) xp).writeW (off B (8*sY)) yp).writeW (off B (8*sDom)) dp).writeW
 (off B (8*sDL)) dl).writeW (off B (8*sLen)) k).writeW (off B (8*sRand)) rp).writeW (off B (8*sCtx)) ctx

theorem generationSave_headers (m : Mem) (B xp yp dp dl k rp ctx : Addr) :
 let t := generationSaveMemory m B xp yp dp dl k rp ctx
 word t B (8*sX)=xp ∧ word t B (8*sY)=yp ∧ word t B (8*sDom)=dp ∧
 word t B (8*sDL)=dl ∧ word t B (8*sLen)=k ∧ word t B (8*sRand)=rp ∧ word t B (8*sCtx)=ctx := by
 simp (disch:=decide) only [generationSaveMemory,hdrStore_hdr,word_writeW_self]
 decide

theorem generationSave_range (m : Mem) (B xp yp dp dl k rp ctx : Addr) :
 Outside B 128 80 m (generationSaveMemory m B xp yp dp dl k rp ctx) := by
 intro q hq
 have store (m : Mem) (i : Nat) (low : 16≤i) (high : i<26) (v : Addr) :
  (m.writeW (off B (8*i)) v) q=m q := writeW_outside m B v (by omega) q (by omega)
 unfold generationSaveMemory
 rw [store _ sCtx (by decide) (by decide),store _ sRand (by decide) (by decide),store _ sLen (by decide) (by decide),
  store _ sDL (by decide) (by decide),store _ sDom (by decide) (by decide),
  store _ sY (by decide) (by decide),store _ sX (by decide) (by decide)]

theorem generateEntrySave_ok {s : State} {B ctx : Addr} {Z : Nat}
 (scratch : Scr s B Z) (room : 256≤Z)
 (readB : s.mem.readW (s.sp+8#64) 64=B) (readCtx : s.mem.readW (s.sp+24#64) 64=ctx)
 (stackB : InRegions (s.rd++s.wr) (s.sp+8#64) 8) (stackCtx : InRegions (s.rd++s.wr) (s.sp+24#64) 8) :
 WP isa (.block (Generate.entry.take 10)) s fun t =>
 (t.gpr .x0=B ∧ t.gpr .x9=ctx ∧
 t.mem=generationSaveMemory s.mem B (s.gpr .x0) (s.gpr .x2) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) ctx) ∧
 Keep [.x0,.x8,.x9] s t := by
 refine WP.keep [.x0,.x8,.x9] ?_ rfl rfl rfl
 unfold Generate.entry generationSaveMemory
 dsimp only [List.take]
 brun [exec_ldrSp_x' _ (show 8%8=0 ∧ 8<32768 by decide) stackB,
  exec_ldrSp_x' (s.write .x .x8 B) (show 24%8=0 ∧ 24<32768 by decide)
   (by simpa only [RegUpd.rd_write,RegUpd.wr_write,RegUpd.sp_write] using stackCtx),readB,readCtx,st,
  hdr_enc (show sX<32 by decide),hdr_enc (show sY<32 by decide),hdr_enc (show sDom<32 by decide),
  hdr_enc (show sDL<32 by decide),hdr_enc (show sLen<32 by decide),hdr_enc (show sRand<32 by decide),hdr_enc (show sCtx<32 by decide),
  scratch.st (d:=8*sX) (by unfold sX;omega),scratch.st (d:=8*sY) (by unfold sY;omega),
  scratch.st (d:=8*sDom) (by unfold sDom;omega),scratch.st (d:=8*sDL) (by unfold sDL;omega),
  scratch.st (d:=8*sLen) (by unfold sLen;omega),scratch.st (d:=8*sRand) (by unfold sRand;omega),scratch.st (d:=8*sCtx) (by unfold sCtx;omega)]

end VG.Proof.Ffdh.AArch64.Cached

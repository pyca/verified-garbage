module

public import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Generate
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Header

import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
/-! Complete cached-attempt entry with its original argument ordering. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/GenerateEntrySave.lean`, which only this module imported.
section

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
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/AArch64/Cached/GenerateEntryMetadata.lean`, which only this module imported.
section

/-! Copy the three canonical public metadata words into native controls. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def generationMetadataMemory (m : Mem) (B N bytes rows : Addr) : Mem :=
 ((m.writeW (off B (8*sBits)) N).writeW (off B (8*sBytes)) bytes).writeW (off B (8*sRows)) rows

theorem generationMetadata_range (m : Mem) (B N bytes rows : Addr) :
 Outside B 128 80 m (generationMetadataMemory m B N bytes rows) := by
 intro q hq
 have store (m : Mem) (i : Nat) (low : 16≤i) (high : i<26) (v : Addr) :
  (m.writeW (off B (8*i)) v) q=m q := writeW_outside m B v (by omega) q (by omega)
 unfold generationMetadataMemory
 rw [store _ sRows (by decide) (by decide),store _ sBytes (by decide) (by decide),store _ sBits (by decide) (by decide)]

theorem generateEntryMetadata_ok {s : State} {B ctx N bytes rows : Addr} {Z : Nat}
 (scratch : Scr s B Z) (room : 256≤Z) (base : s.gpr .x0=B) (context : s.gpr .x9=ctx)
 (read0 : InRegions (s.rd++s.wr) ctx 8) (read8 : InRegions (s.rd++s.wr) (off ctx 8) 8)
 (read16 : InRegions (s.rd++s.wr) (off ctx 16) 8)
 (value0 : word s.mem ctx 0=N) (value8 : word s.mem ctx 8=bytes) (value16 : word s.mem ctx 16=rows) :
 WP isa (.block (Generate.entry.drop 10)) s fun t =>
 t.mem=generationMetadataMemory s.mem B N bytes rows ∧ Keep [.x10,.x11,.x12] s t := by
 refine WP.keep [.x10,.x11,.x12] ?_ rfl rfl rfl
 unfold Generate.entry generationMetadataMemory
 dsimp only [List.drop]
 have v0 : s.mem.readW ctx 64=N := by simpa only [word,off,BitVec.add_zero] using value0
 brun [base,context,read0,read8,read16,v0,value8,value16,
  hdr_enc (show sBits<32 by decide),hdr_enc (show sBytes<32 by decide),hdr_enc (show sRows<32 by decide),
  scratch.st (d:=8*sBits) (by unfold sBits;omega),scratch.st (d:=8*sBytes) (by unfold sBytes;omega),
  scratch.st (d:=8*sRows) (by unfold sRows;omega)]

end VG.Proof.Ffdh.AArch64.Cached
end

end

@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem generationEntry_headers (m : Mem) (B xp yp dp dl k rp ctx N bytes rows : Addr) :
 let t := generationMetadataMemory (generationSaveMemory m B xp yp dp dl k rp ctx) B N bytes rows
 word t B (8*sCtx)=ctx ∧ word t B (8*sDom)=dp ∧ word t B (8*sLen)=k ∧ word t B (8*sDL)=dl ∧
 word t B (8*sX)=xp ∧ word t B (8*sY)=yp ∧ word t B (8*sRand)=rp ∧
 word t B (8*sBits)=N ∧ word t B (8*sBytes)=bytes ∧ word t B (8*sRows)=rows := by
 simp (disch:=decide) only [generationMetadataMemory,generationSaveMemory,hdrStore_hdr,word_writeW_self]
 decide

theorem generateEntry_ok {s : State} {B ctx N bytes rows : Addr} {Z : Nat}
 (scratch : Scr s B Z) (room : 256≤Z)
 (readB : s.mem.readW (s.sp+8#64) 64=B) (readCtx : s.mem.readW (s.sp+24#64) 64=ctx)
 (stackB : InRegions (s.rd++s.wr) (s.sp+8#64) 8) (stackCtx : InRegions (s.rd++s.wr) (s.sp+24#64) 8)
 (readable : ∀ i<3,InRegions (s.rd++s.wr) (ctx+BitVec.ofNat 64 (8*i)) 8)
 (outside : ∀ i<24,Z≤ofs B (ctx+BitVec.ofNat 64 i))
 (value0 : word s.mem ctx 0=N) (value8 : word s.mem ctx 8=bytes) (value16 : word s.mem ctx 16=rows) :
 WP isa (.block Generate.entry) s fun t =>
 t.gpr .x0=B ∧
 t.mem=generationMetadataMemory (generationSaveMemory s.mem B (s.gpr .x0) (s.gpr .x2) (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) ctx) B N bytes rows ∧
 Outside B 128 80 s.mem t.mem ∧ Keep (.x0::mmRegs) s t := by
 change WP isa (.block ((Generate.entry.take 10)++(Generate.entry.drop 10))) s _
 rw [WP.block_append_iff]
 refine WP.mono (generateEntrySave_ok scratch room readB readCtx stackB stackCtx) ?_
 rintro a ⟨⟨baseA,ctxA,memA⟩,restA⟩
 have frameA : Outside B 128 80 s.mem a.mem := by rw [memA];exact generationSave_range _ _ _ _ _ _ _ _ _
 have inscrA : InScr B Z s.mem a.mem := InScr.of_outside frameA (by omega)
 have same (i : Nat) (hi : i<3) : word a.mem ctx (8*i)=word s.mem ctx (8*i) := by
  apply Mem.readW_congr
  intro j hj
  have sep := outside (8*i+j) (by omega)
  exact inscrA _ (by simpa only [off,BitVec.ofNat_add,BitVec.add_assoc] using sep)
 refine WP.mono (generateEntryMetadata_ok (scratch.congr restA.wr) room baseA ctxA
  (by rw [restA.rd,restA.wr];simpa only [Nat.mul_zero,show BitVec.ofNat 64 0=0#64 from rfl,BitVec.add_zero] using readable 0 (by decide))
  (by rw [restA.rd,restA.wr];exact readable 1 (by decide))
  (by rw [restA.rd,restA.wr];exact readable 2 (by decide))
  ((same 0 (by decide)).trans value0) ((same 1 (by decide)).trans value8) ((same 2 (by decide)).trans value16)) ?_
 rintro t ⟨memT,restT⟩
 have frameT : Outside B 128 80 a.mem t.mem := by rw [memT];exact generationMetadata_range _ _ _ _ _
 exact ⟨(restT.gpr .x0 (by decide)).trans baseA,by rw [memT,memA],frameA.trans frameT,
  (restA.trans restT).mono (by simp [mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached

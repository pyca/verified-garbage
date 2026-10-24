module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.GenerateEntrySave
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.GenerateEntryMetadata
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Complete cached-attempt entry with its original argument ordering. -/
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

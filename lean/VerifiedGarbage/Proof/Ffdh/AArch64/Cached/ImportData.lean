module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.CopyFromContext
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ImportInverse
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PowerState
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Controls
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! Import canonical p and R² and reconstruct the architecture-specific inverse. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def importData : Prog isa := seqs [
 .block [ldh .x16 sCtx,.addImm .x .x16 .x16 24,ldh .x17 (sArr 0),ldh .x12 sW],copyWords,
 .block [ldh .x17 (sArr 4),ldh .x12 sW],copyWords,
 .block ([ldh .x8 (sArr 0),ld .x3 .x8]++minv++[sth .x15 sMinv])]

def importDataRanges (w : Nat) : List (Nat × Nat) :=
 [(slot w 0,8*(w+2)),(slot w 4,8*(w+2)),(8*sMinv,8)]

theorem importData_ok {s : State} {B ctx : Addr} {Z w P : Nat} {old : BitVec 64}
 (good : Good s B Z w old) (room : slot w 8≤Z) (positive : 0<w) (size : w<2^31)
 (context : word s.mem B (8*sCtx)=ctx)
 (readable : ∀ i<2*w,InRegions (s.rd++s.wr) (off ctx (24+8*i)) 8)
 (outside : ∀ i<16*w,Z≤ofs B (off ctx 24+BitVec.ofNat 64 i))
 (modulus : wv s.mem ctx 24 w=P) (r2 : wv s.mem ctx (24+8*w) w=2^(128*w)%P) (odd : P%2=1) :
 WP isa importData s fun t =>
 ∃ mi,Good t B Z w mi ∧ wv t.mem B (slot w 0) w=P ∧
 ((word t.mem B (slot w 0)).toNat*mi.toNat+1)%2^64=0 ∧
 wv t.mem B (slot w 4) w=2^(128*w)%P ∧ Frm B (importDataRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
 have nowrap : B.toNat+slot w 8≤2^64 := by have := good.scr.nowrap;omega
 have keepCtx (m : Mem) (frame : InScr B Z s.mem m) : wv m ctx (24+8*w) w=wv s.mem ctx (24+8*w) w := by
  apply wv_congr
  intro i hi
  apply Mem.readW_congr
  intro b hb
  apply frame
  have sep := outside (8*w+8*i+b) (by omega)
  simpa only [off,BitVec.ofNat_add,BitVec.add_assoc] using sep
 unfold importData
 simp only [seqs]
 rw [WP.seq_iff]
 refine WP.mono (WP.keep [.x16,.x17,.x12] (Q:=fun a =>a.gpr .x16=off ctx 24 ∧
  a.gpr .x17=off B (slot w 0) ∧ a.gpr .x12=BitVec.ofNat 64 w ∧ a.mem=s.mem) ?_ rfl rfl rfl) ?_
 · brun [good.x0,hdr_enc (show sCtx<32 by decide),hdr_enc (show sArr 0<32 by decide),hdr_enc (show sW<32 by decide),
    header_read good room (show sCtx<32 by decide),header_read good room (show sArr 0<32 by decide),
    header_read good room (show sW<32 by decide),context,good.hdr.harr 0 (by decide),good.hdr.hw]
 · rintro a ⟨⟨srcA,dstA,countA,memA⟩,restA⟩
   have goodA : Good a B Z w old := ⟨good.scr.congr restA.wr,(restA.gpr .x0 (by decide)).trans good.x0,memA ▸ good.hdr⟩
   rw [WP.seq_iff]
   refine WP.mono (copyFromContext_ok goodA room positive size (by decide : 0<8) srcA dstA countA
    (fun i hi =>by rw [restA.rd,restA.wr];exact readable i (by omega))
    (fun i hi =>outside i (by omega))) ?_
   rintro b ⟨goodB,valueB,frameB,pointerB,restB⟩
   have modulusB : wv b.mem B (slot w 0) w=P := by rw [valueB,memA];exact modulus
   have inscrB : InScr B Z s.mem b.mem := by
    rw [←memA];exact InScr.of_arrays frameB room (by simp : ∀ i∈[0],i<8)
   rw [WP.seq_iff]
   refine WP.mono (WP.keep [.x17,.x12] (Q:=fun c =>c.gpr .x17=off B (slot w 4) ∧ c.gpr .x12=BitVec.ofNat 64 w ∧ c.mem=b.mem) ?_ rfl rfl rfl) ?_
   · brun [goodB.x0,hdr_enc (show sArr 4<32 by decide),hdr_enc (show sW<32 by decide),
      header_read goodB room (show sArr 4<32 by decide),header_read goodB room (show sW<32 by decide),
      goodB.hdr.harr 4 (by decide),goodB.hdr.hw]
   · rintro c ⟨⟨dstC,countC,memC⟩,restC⟩
     have goodC : Good c B Z w old := ⟨goodB.scr.congr restC.wr,(restC.gpr .x0 (by decide)).trans goodB.x0,memC ▸ goodB.hdr⟩
     have rest := (restA.trans restB).trans restC
     rw [WP.seq_iff]
     refine WP.mono (copyFromContext_ok goodC room positive size (by decide : 4<8)
      ((restC.gpr .x16 (by decide)).trans pointerB) dstC countC
      (fun i hi =>by
       rw [rest.rd,rest.wr]
       simpa only [Nat.mul_add,Nat.add_assoc] using readable (w+i) (by omega))
      (fun i hi =>by
       have sep := outside (8*w+i) (by omega)
       simpa only [off,BitVec.ofNat_add,BitVec.add_assoc] using sep)) ?_
     rintro d ⟨goodD,valueD,frameD,_,restD⟩
     have modulusD : wv d.mem B (slot w 0) w=P := by
      rw [frameD.wv_of_not_mem (by decide) (by decide) nowrap,memC];exact modulusB
     have r2D : wv d.mem B (slot w 4) w=2^(128*w)%P := by rw [valueD,memC,keepCtx b.mem inscrB];exact r2
     refine WP.mono (importInverse_ok goodD room positive (by rw [modulusD];exact odd)) ?_
     rintro t ⟨mi,goodT,inverseT,frameT,restT⟩
     have field0 : wv t.mem B (slot w 0) w=P :=
      (frameT.wv (Or.inr (hdr_lt_slot w 0 (show sMinv<32 by decide))) (by have := slot_le (w:=w) (show 0<8 by decide);omega)).trans modulusD
     have field4 : wv t.mem B (slot w 4) w=2^(128*w)%P :=
      (frameT.wv (Or.inr (hdr_lt_slot w 4 (show sMinv<32 by decide))) (by have := slot_le (w:=w) (show 4<8 by decide);omega)).trans r2D
     have first : Frm B (importDataRanges w) s.mem b.mem := by rw [←memA];exact Frm.of_arrays frameB (by simp [importDataRanges])
     have second : Frm B (importDataRanges w) b.mem d.mem := by rw [←memC];exact Frm.of_arrays frameD (by simp [importDataRanges])
     exact ⟨mi,goodT,field0,inverseT,field4,(first.trans second).trans (Frm.of_outside frameT (by simp [importDataRanges])),
      (((rest.trans restD).trans restT)).mono (by simp [mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached

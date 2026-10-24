module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.MemoryState
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SetLowBit
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Less
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Copy
public import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! Public powers are checked for 1<y<p−1 without repeating their proven subgroup test. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def publicRangeRanges (w : Nat) : List (Nat × Nat) := [(slot w 1,8*(w+2)),(8*sTmp,8)]

theorem publicRange_ok {p : Parameters} {s : State} (state : ModState p s) (odd : p.P%2=1) :
 WP isa Generate.publicRange s fun t =>
 ModState p t ∧ wv t.mem p.B (slot p.w 6) p.w=wv s.mem p.B (slot p.w 6) p.w ∧
 t.gpr .x9=(if 1<wv s.mem p.B (slot p.w 6) p.w ∧ wv s.mem p.B (slot p.w 6) p.w<p.P-1 then 1#64 else 0#64) ∧
 word t.mem p.B (8*sTmp)=t.gpr .x9 ∧ Frm p.B (publicRangeRanges p.w) s.mem t.mem ∧ Keep mmRegs s t := by
 have positive : 0<p.w := by have := p.positive;omega
 have nowrap : p.B.toNat+slot p.w 8≤2^64 := by have := state.good.scr.nowrap;have := p.room;omega
 have yRoom := slot_le (w:=p.w) (show 6<8 by decide)
 unfold Generate.publicRange
 simp only [seqs]
 rw [WP.seq_iff]
 refine WP.mono (less_ok state.good p.room positive p.width (by decide : 7<8) (by decide : 6<8)) ?_
 rintro a ⟨valueA,memA,restA⟩
 rw [state.one] at valueA
 have stateA := state.after_mem memA restA ((restA.gpr .x0 (by simp [mmRegs])).trans state.good.x0)
 rw [WP.seq_iff]
 refine WP.mono (store_control_ok stateA.good p.room (by decide : 16≤sTmp) (by decide : sTmp<32) .x9) ?_
 rintro b ⟨goodB,memB,frameB,restB⟩
 have stateB := stateA.after_header goodB frameB (by decide : sTmp<32)
 have flagB : word b.mem p.B (8*sTmp)=(if 1<wv s.mem p.B (slot p.w 6) p.w then 1#64 else 0#64) := by
  rw [memB,word_writeW_self];exact valueA
 have yB : wv b.mem p.B (slot p.w 6) p.w=wv s.mem p.B (slot p.w 6) p.w := by
  rw [frameB.wv (Or.inr (hdr_lt_slot p.w 6 (show sTmp<32 by decide))) (by omega),memA]
 rw [WP.seq_iff]
 refine WP.mono (copy_ok goodB p.room positive p.width (by decide : 1<8) (by decide : 6<8) (by decide)) ?_
 rintro c ⟨goodC,valueC,frameC,restC⟩
 have stateC := stateB.after_arrays goodC frameC (by decide) (by decide) (by decide)
 rw [WP.seq_iff]
 refine WP.mono (setLowBit_ok goodC p.room positive) ?_
 rintro d ⟨goodD,valueD,frameD,restD⟩
 have stateD := stateC.after_arrays goodD frameD (by decide) (by decide) (by decide)
 have valueD : wv d.mem p.B (slot p.w 1) p.w=2*(wv s.mem p.B (slot p.w 6) p.w/2)+1 := by rw [valueD,valueC,yB]
 have yD : wv d.mem p.B (slot p.w 6) p.w=wv s.mem p.B (slot p.w 6) p.w :=
  (frameD.wv_of_not_mem (by decide) (by decide) nowrap).trans
   ((frameC.wv_of_not_mem (by decide) (by decide) nowrap).trans yB)
 have flagD : word d.mem p.B (8*sTmp)=(if 1<wv s.mem p.B (slot p.w 6) p.w then 1#64 else 0#64) := by
  rw [arrays_header frameD (by decide),arrays_header frameC (by decide)];exact flagB
 rw [WP.seq_iff]
 refine WP.mono (less_ok goodD p.room positive p.width (by decide : 1<8) (by decide : 0<8)) ?_
 rintro e ⟨valueE,memE,restE⟩
 rw [valueD,stateD.modulus] at valueE
 simp only [VG.Proof.Ffdh.lt_pm1 odd] at valueE
 have total := (((restA.trans restB).trans restC).trans restD).trans restE
 have goodE := good_after_mem goodD memE restE ((restE.gpr .x0 (by simp [mmRegs])).trans goodD.x0)
 have flagE : word e.mem p.B (8*sTmp)=(if 1<wv s.mem p.B (slot p.w 6) p.w then 1#64 else 0#64) := by rw [memE];exact flagD
 let flag : Addr := if 1<wv s.mem p.B (slot p.w 6) p.w ∧ wv s.mem p.B (slot p.w 6) p.w<p.P-1 then 1#64 else 0#64
 have combine : (if wv s.mem p.B (slot p.w 6) p.w<p.P-1 then 1#64 else 0#64) &&&
  (if 1<wv s.mem p.B (slot p.w 6) p.w then 1#64 else 0#64)=flag := by
  unfold flag
  split <;> split <;> simp_all
 refine WP.mono (WP.keep [.x3,.x9] (Q:=fun t =>t.gpr .x9=flag ∧ t.mem=e.mem.writeW (off p.B (8*sTmp)) flag) ?_ rfl rfl rfl) ?_
 · brun [goodE.x0,hdr_enc (show sTmp<32 by decide),header_read goodE p.room (show sTmp<32 by decide),
    goodE.scr.st (d:=8*sTmp) (by have := hdr_lt_slot p.w 8 (show sTmp<32 by decide);have := p.room;omega),
    flagE,valueE,combine]
 · rintro t ⟨⟨flagT,memT⟩,restT⟩
   have frameT : Outside p.B (8*sTmp) 8 e.mem t.mem := by rw [memT];exact writeW_outside _ _ _ (by decide)
   have stateE := stateD.after_mem memE restE goodE.x0
   have goodT := good_after_header goodE (by decide) (by decide) frameT restT ((restT.gpr .x0 (by decide)).trans goodE.x0)
   have stateT := stateE.after_header goodT frameT (by decide)
   have yT : wv t.mem p.B (slot p.w 6) p.w=wv s.mem p.B (slot p.w 6) p.w := by
    rw [frameT.wv (Or.inr (hdr_lt_slot p.w 6 (show sTmp<32 by decide))) (by omega),memE];exact yD
   have first : Frm p.B (publicRangeRanges p.w) s.mem b.mem := by
    rw [←memA];exact Frm.of_outside frameB (by simp [publicRangeRanges])
   have middle : Frm p.B (publicRangeRanges p.w) b.mem d.mem :=
    (Frm.of_arrays frameC (by simp [publicRangeRanges])).trans (Frm.of_arrays frameD (by simp [publicRangeRanges]))
   have last : Frm p.B (publicRangeRanges p.w) d.mem t.mem := by
    rw [←memE];exact Frm.of_outside frameT (by simp [publicRangeRanges])
   exact ⟨stateT,yT,flagT,by rw [memT,word_writeW_self,flagT],(first.trans middle).trans last,
    (total.trans restT).mono (by simp [mmRegs])⟩

end VG.Proof.Ffdh.AArch64.Cached

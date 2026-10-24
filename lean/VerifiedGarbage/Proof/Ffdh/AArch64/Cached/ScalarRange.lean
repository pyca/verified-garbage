module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ScalarBound
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Nonzero
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Less
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Controls
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! The complete rejection predicate is 0<x<q, or 0<x<p−1, at a fixed public width. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def scalarRanges (w : Nat) : List (Nat × Nat) :=
 [(slot w 1,8*(w+2)),(slot w 5,8*(w+2)),(8*sTmp,8)]

theorem scalarRange_ok {s : State} {B xp dp : Addr} {Z w k dl : Nat} {mi : BitVec 64} {dom bs : List Byte}
 (good : Good s B Z w mi) (room : slot w 8≤Z) (words : w=(k+7)/8) (positive : 0<k) (size : k<2^31)
 (shape : dl=2*k ∨ dl=3*k) (domLength : dom.length=dl)
 (domainSource : Src s B Z dp dom) (scalarSource : Src s B Z xp bs) (bsLength : bs.length=k)
 (output : word s.mem B (8*sX)=xp) (domain : word s.mem B (8*sDom)=dp)
 (length : word s.mem B (8*sLen)=BitVec.ofNat 64 k) (domainLength : word s.mem B (8*sDL)=BitVec.ofNat 64 dl)
 (modulus : wv s.mem B (slot w 0) w=(Spec.Ffdh.domainOf k dom).p)
 (odd : (Spec.Ffdh.domainOf k dom).p%2=1) :
 WP isa Generate.scalarRange s fun t =>
 Good t B Z w mi ∧ wv t.mem B (slot w 1) w=Spec.Rsa.os2ip bs ∧
 t.gpr .x9=(if 0<Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs<Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) then 1#64 else 0#64) ∧
 Frm B (scalarRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
 have wPositive : 0<w := by rw [words];omega
 have wSize : w<2^31 := by rw [words];omega
 have nowrap : slot w 8≤2^64 := by have := good.scr.nowrap;omega
 have array0 := slot_le (w:=w) (show 0<8 by decide)
 have array1 := slot_le (w:=w) (show 1<8 by decide)
 unfold Generate.scalarRange
 simp only [seqs]
 rw [WP.seq_iff]
 refine WP.mono (WP.keep [.x1,.x2] (Q:=fun a =>a.gpr .x1=xp ∧ a.gpr .x2=BitVec.ofNat 64 k ∧ a.mem=s.mem) ?_ rfl rfl rfl) ?_
 · brun [good.x0,hdr_enc (show sX<32 by decide),hdr_enc (show sLen<32 by decide),
    header_read good room (show sX<32 by decide),header_read good room (show sLen<32 by decide),output,length]
 · rintro a ⟨⟨ptrA,lenA,memA⟩,restA⟩
   have goodA : Good a B Z w mi := ⟨good.scr.congr restA.wr,(restA.gpr .x0 (by decide)).trans good.x0,memA ▸ good.hdr⟩
   have scalarA := scalarSource.congrK (fun x _ =>by rw [memA]) restA
   rw [WP.seq_iff]
   refine WP.mono (loadArray_ok goodA room words positive size (by decide : 1<8) scalarA bsLength ptrA lenA) ?_
   rintro b ⟨goodB,valueB,frameB,restB⟩
   rw [WP.seq_iff]
   refine WP.mono (nonzero_ok goodB room wPositive wSize) ?_
   rintro c ⟨goodC,_,nonzeroC,frameC,restC⟩
   have before := (restA.trans restB).trans restC
   have inscrB := InScr.of_arrays frameB room (by simp : ∀ i∈[1],i<8)
   have inscrC : InScr B Z b.mem c.mem := InScr.of_outside frameC (by have := hdr_lt_slot w 8 (show sTmp<32 by decide);omega)
   have inscrSA : InScr B Z s.mem a.mem := by intro x hx;rw [memA]
   have sourceC := domainSource.congrK ((inscrSA.trans inscrB).trans inscrC) before
   have headerC (i : Nat) (hi : i<32) (different : i≠sTmp) : word c.mem B (8*i)=word s.mem B (8*i) := by
    rw [header_other frameC (by decide) hi different,arrays_header frameB hi,memA]
   have modulusC : wv c.mem B (slot w 0) w=(Spec.Ffdh.domainOf k dom).p := by
    rw [frameC.wv (Or.inr (hdr_lt_slot w 0 (show sTmp<32 by decide))) (by omega),
     frameB.wv_of_not_mem (by decide) (by decide) (by have := good.scr.nowrap;omega),memA]
    exact modulus
   have valueC : wv c.mem B (slot w 1) w=Spec.Rsa.os2ip bs := by
    rw [frameC.wv (Or.inr (hdr_lt_slot w 1 (show sTmp<32 by decide))) (by omega)];exact valueB
   rw [WP.seq_iff]
   refine WP.mono (scalarBound_ok goodC room words positive size shape domLength sourceC
    ((headerC sDom (by decide) (by decide)).trans domain)
    ((headerC sLen (by decide) (by decide)).trans length)
    ((headerC sDL (by decide) (by decide)).trans domainLength) modulusC odd) ?_
   rintro d ⟨goodD,boundD,frameD,restD⟩
   have valueD : wv d.mem B (slot w 1) w=Spec.Rsa.os2ip bs :=
    (frameD.wv_of_not_mem (by decide) (by decide) (by have := good.scr.nowrap;omega)).trans valueC
   have nzD : word d.mem B (8*sTmp)=(if Spec.Rsa.os2ip bs=0 then 0#64 else 1#64) := by
    rw [arrays_header frameD (by decide),nonzeroC,valueB]
   rw [WP.seq_iff]
   refine WP.mono (less_ok goodD room wPositive wSize (by decide : 1<8) (by decide : 5<8)) ?_
   rintro e ⟨lessE,memE,restE⟩
   rw [valueD,boundD] at lessE
   have rest := ((before.trans restD).trans restE)
   have maskE : word e.mem B (8*sTmp)=(if Spec.Rsa.os2ip bs=0 then 0#64 else 1#64) := by rw [memE];exact nzD
   have flag : (if Spec.Rsa.os2ip bs<Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) then 1#64 else 0#64) &&&
    (if Spec.Rsa.os2ip bs=0 then 0#64 else 1#64)=
    (if 0<Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs<Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) then 1#64 else 0#64) := by
    split <;> split <;> simp_all
   refine WP.mono (WP.keep [.x3,.x9] (Q:=fun t =>
    t.gpr .x9=(if 0<Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs<Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) then 1#64 else 0#64) ∧ t.mem=e.mem)
    ?_ rfl rfl rfl) ?_
   · brun [(rest.gpr .x0 (by simp [mmRegs])).trans good.x0,hdr_enc (show sTmp<32 by decide),
      (good.scr.congr rest.wr).ld (d:=8*sTmp) (by have := hdr_lt_slot w 8 (show sTmp<32 by decide);omega),maskE,lessE,flag]
   · rintro t ⟨⟨flagT,memT⟩,restT⟩
     have total : Keep mmRegs s t := (rest.trans restT).mono (by simp [mmRegs])
     have same : t.mem=d.mem := memT.trans memE
     have goodT : Good t B Z w mi :=
      ⟨good.scr.congr total.wr,(total.gpr .x0 (by simp [mmRegs])).trans good.x0,same ▸ goodD.hdr⟩
     have first : Frm B (scalarRanges w) s.mem b.mem := by
      rw [←memA];exact Frm.of_arrays frameB (by simp [scalarRanges])
     have second : Frm B (scalarRanges w) b.mem c.mem := Frm.of_outside frameC (by simp [scalarRanges])
     have third : Frm B (scalarRanges w) c.mem d.mem := Frm.of_arrays frameD (by simp [scalarRanges])
     exact ⟨goodT,by rw [same];exact valueD,flagT,by rw [same];exact (first.trans second).trans third,total⟩

end VG.Proof.Ffdh.AArch64.Cached

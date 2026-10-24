module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Phases
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ScanTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ConstTiming
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Comb
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! Complete selection, including zero initialization and public header loads. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

def SelectionReady (p : Parameters) (s : State) : Prop :=
 ∃ bs E i v, Running p bs E i s ∧ v<32 ∧ word s.mem p.B (8*sD)=BitVec.ofNat 64 v

def scanPublic (p : Parameters) : ScanPublic :=
 ⟨p.B,p.table,off p.B (slot p.w 5),p.w,by have := p.positive;omega,by have := p.width;omega⟩

theorem selection_ct : RelCT isa (Two SelectionReady) Comb.select (fun _ _ => True) := by
 unfold Comb.select
 refine RelCT.seq (two_post (Ψ:=SelectionReady)
  (two_map (fun p : Parameters => (⟨p.B,p.Z,p.w⟩ : Ws))
   (fun p s h => by obtain ⟨bs,E,i,v,h,_,_⟩:=h;exact ⟨p.mi,h.power.good,p.room⟩)
   (const_ct 5 0 (by decide) (by taint_decide) (by taint_decide))) ?_) ?_
 · rintro p s ⟨bs,E,i,v,h,hv,digit⟩
   refine WP.mono (const_ok h.power.good p.room (by have := p.positive;omega) p.width
    (by decide : 5<8) (by decide : 0<2^16)) ?_
   rintro t ⟨good,_,outside,rest⟩
   have frame : Arrays p.B p.w [5] s.mem t.mem := Arrays.of_outside (j:=5) (by simp) outside
    (by have := p.positive;omega) (by have := h.power.good.scr.nowrap;have := p.room;have := slot_le (w:=p.w) (by decide : 5<8);omega)
   have power := h.power.after_arrays good frame (by decide) (by decide) (by decide) (by decide)
   have keep := rest.mono (show ∀ r∈[.x7,.x8,.x9,.x12,.x13,.x14,.x16],r∈mmRegs by decide)
   exact ⟨bs,E,i,v,h.after_arrays power frame keep (by simp),hv,(arrays_header frame (by decide)).trans digit⟩
 · refine RelCT.seq (two_piece (Ψ:=fun p s => ScanReady (scanPublic p) 0 s) [.x0] ?_ (by taint_decide) ?_)
    (two_map scanPublic (fun _ _ h => h) scan_ct)
   · rintro p s t ⟨bs,E,i,v,hs,_,_⟩ ⟨bt,F,j,u,ht,_,_⟩ r hr
     have : r= .x0 := by simpa using hr
     subst r
     exact hs.power.good.x0.trans ht.power.good.x0.symm
   · rintro p s ⟨bs,E,i,v,h,hv,digit⟩
     refine WP.mono (WP.keep [.x9,.x10,.x11] (Q:=fun t =>
      t.gpr .x9=p.table ∧ t.gpr .x10=BitVec.ofNat 64 v ∧ t.gpr .x11=0#64 ∧ t.mem=s.mem) ?_ rfl rfl rfl) ?_
     · have table : word s.mem p.B (8*sTab)=p.table := h.tablePointer
       brun [h.power.good.x0,hdr_enc (show sTab<32 by decide),hdr_enc (show sD<32 by decide),
        header_read h.power.good p.room (show sTab<32 by decide),
        header_read h.power.good p.room (show sD<32 by decide),table,digit]
     · rintro t ⟨⟨pointer,digit,candidate,mem⟩,rest⟩
       have hT := h.after_mem mem (rest.mono (by decide))
       refine ⟨selectEnv_good hT.power.good p.room (by have := p.positive;omega)
        hT.reads.tableRead hT.reads.tableOutside,?_,candidate,v,hv,digit⟩
       simpa [scanPublic,off] using pointer

end VG.Proof.Ffdh.AArch64.Cached

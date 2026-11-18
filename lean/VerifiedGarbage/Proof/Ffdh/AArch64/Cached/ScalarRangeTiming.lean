module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SourceEncoding
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.BoundTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.NonzeroTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SetLowBit
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.LessTiming
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Generate
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! ### `Ffdh.AArch64.Cached.ScalarTimingState`, which only this module used -/

section

/-! The rejection checks preserve all public controls and immutable scalar/context inputs. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

structure ScalarPublic where
 p : Parameters
 dp : Addr
 dl : Nat
 dom : List Byte
 words : p.w=(p.k+7)/8
 positive : 0<p.k
 size : p.k<2^31
 shape : dl=2*p.k ∨ dl=3*p.k
 domLength : dom.length=dl
 modulus : p.P=(Spec.Ffdh.domainOf p.k dom).p
 odd : p.P%2=1

structure ScalarState (q : ScalarPublic) (bs : List Byte) (s : State) : Prop where
 initial : Initial q.p bs s
 length : bs.length=q.p.k
 source : Src s q.p.B q.p.Z q.dp q.dom
 domain : word s.mem q.p.B (8*sDom)=q.dp
 domainLength : word s.mem q.p.B (8*sDL)=BitVec.ofNat 64 q.dl

def ScalarReady (q : ScalarPublic) (s : State) : Prop := ∃ bs,ScalarState q bs s

theorem ScalarState.after {q : ScalarPublic} {bs : List Byte} {s t : State} {rs : List Reg}
 (h : ScalarState q bs s) (good : Good t q.p.B q.p.Z q.p.w q.p.mi)
 (frame : Frm q.p.B (scalarRanges q.p.w) s.mem t.mem) (rest : Keep rs s t) : ScalarState q bs t :=
 ⟨h.initial.after_scalarRange good frame rest,h.length,
  h.source.congrK (InScr.of_frm frame (fun r hr =>Nat.le_trans (scalarRanges_le _ r hr) q.p.room)) rest,
  (scalarFrame_header frame (by decide) (by decide)).trans h.domain,
  (scalarFrame_header frame (by decide) (by decide)).trans h.domainLength⟩

theorem ScalarState.after_mem {q : ScalarPublic} {bs : List Byte} {s t : State} {rs : List Reg}
 (h : ScalarState q bs s) (mem : t.mem=s.mem) (rest : Keep rs s t) (base : t.gpr .x0=q.p.B) : ScalarState q bs t :=
 h.after (good_after_mem h.initial.good mem rest base) (fun a _ =>by rw [mem]) rest

def scalarWs (q : ScalarPublic) : Ws := ⟨q.p.B,q.p.Z,q.p.w⟩

def scalarBoundPublic (q : ScalarPublic) : BoundPublic :=
 ⟨scalarWs q,q.dp,q.p.k,q.dl,by change 0<q.p.w;have :=q.p.positive;omega_using [this],q.p.width,q.size,q.shape⟩

theorem scalarReady_bound {q : ScalarPublic} {s : State} (h : ScalarReady q s) : BoundReady (scalarBoundPublic q) s := by
 obtain ⟨bs,h⟩ :=h
 exact ⟨⟨q.p.mi,h.initial.good,q.p.room⟩,h.domain,(by change word s.mem q.p.B (8*sLen)=BitVec.ofNat 64 q.p.k;rw [←h.length];exact h.initial.controls.length),h.domainLength⟩

theorem scalarReady_nonzero {q : ScalarPublic} {s : State} (h : ScalarReady q s) :
 WP isa Generate.nonzero s (ScalarReady q) := by
 obtain ⟨bs,h⟩ :=h
 refine WP.mono (nonzero_ok h.initial.good q.p.room (by have :=q.p.positive;omega_using [this]) q.p.width) ?_
 rintro t ⟨good,_,_,frame,rest⟩
 exact ⟨bs,h.after good (Frm.of_outside frame (by simp [scalarRanges])) rest⟩

theorem scalarReady_bound_ok {q : ScalarPublic} {s : State} (h : ScalarReady q s) :
 WP isa Generate.bound s (ScalarReady q) := by
 obtain ⟨bs,h⟩ :=h
 refine WP.mono (scalarBound_ok h.initial.good q.p.room q.words q.positive q.size q.shape q.domLength h.source
  h.domain (h.length ▸ h.initial.controls.length) h.domainLength (h.initial.modulus.trans q.modulus)
  (by rw [←q.modulus];exact q.odd)) ?_
 rintro t ⟨good,_,frame,rest⟩
 exact ⟨bs,h.after good (Frm.of_arrays frame (by simp [scalarRanges])) rest⟩

end VG.Proof.Ffdh.AArch64.Cached

end

end


/-! The complete scalar rejection predicate scans a fixed public geometry. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def ScalarLoadReady (q : ScalarPublic) (s : State) : Prop :=
 ScalarReady q s ∧ s.gpr .x1=q.p.src ∧ s.gpr .x2=BitVec.ofNat 64 q.p.k

theorem scalarRange_ct : RelCT isa (Two ScalarReady) Generate.scalarRange (fun _ _ =>True) := by
 unfold Generate.scalarRange
 simp only [seqs]
 refine RelCT.seq (two_piece (Ψ:=ScalarLoadReady) [.x0] ?_ (by taint_decide) ?_) ?_
 · rintro q s t ⟨bs,hs⟩ ⟨bt,ht⟩ r hr
   have eq : r= .x0 := by simpa using hr
   subst r
   exact hs.initial.good.x0.trans ht.initial.good.x0.symm
 · rintro q s ⟨bs,h⟩
   have good := h.initial.good
   have x := h.initial.controls.source
   have len := h.initial.controls.length
   rw [h.length] at len
   refine WP.mono (WP.keep [.x1,.x2] (Q:=fun t =>
    t.gpr .x1=q.p.src ∧ t.gpr .x2=BitVec.ofNat 64 q.p.k ∧ t.mem=s.mem) ?_ rfl rfl rfl) ?_
   · brun [good.x0,hdr_enc (show sX<32 by decide),hdr_enc (show sLen<32 by decide),
      header_read good q.p.room (show sX<32 by decide),header_read good q.p.room (show sLen<32 by decide),x,len]
   · rintro t ⟨⟨ptr,len,mem⟩,rest⟩
     exact ⟨⟨bs,h.after_mem mem rest ((rest.gpr .x0 (by decide)).trans good.x0)⟩,ptr,len⟩
 · refine RelCT.seq (two_post (Ψ:=ScalarReady)
    (two_map (fun q =>(⟨scalarWs q,q.p.src,q.p.k⟩ : LoadPublic))
     (fun q s h =>by obtain ⟨⟨bs,h⟩,ptr,len⟩:=h;exact ⟨⟨q.p.mi,h.initial.good,q.p.room⟩,ptr,len⟩)
     (load_ct (by decide : 1<8) (by taint_decide))) ?_) ?_
   · rintro q s ⟨⟨bs,h⟩,ptr,len⟩
     refine WP.mono (loadArray_ok h.initial.good q.p.room q.words q.positive q.size (by decide : 1<8)
      (source_src h.initial.reads.source h.initial.reads.scalarOutside) h.length ptr len) ?_
     rintro t ⟨good,_,frame,rest⟩
     exact ⟨bs,h.after good (Frm.of_arrays frame (by simp [scalarRanges])) rest⟩
   · refine RelCT.seq (two_post (Ψ:=ScalarReady)
      (two_map scalarWs (fun q s h =>by obtain ⟨bs,h⟩:=h;exact ⟨q.p.mi,h.initial.good,q.p.room⟩) nonzero_ct)
      (fun _ _ h =>scalarReady_nonzero h)) ?_
     refine RelCT.seq (two_post (Ψ:=ScalarReady)
      (two_map scalarBoundPublic (fun _ _ h =>scalarReady_bound h) scalarBound_ct)
      (fun _ _ h =>scalarReady_bound_ok h)) ?_
     refine RelCT.seq (two_post (Ψ:=ScalarReady)
      (two_map scalarWs (fun q s h =>by obtain ⟨bs,h⟩:=h;exact ⟨q.p.mi,h.initial.good,q.p.room⟩)
       (less_ct (by decide : 1<8) (by decide : 5<8) (by taint_decide))) ?_)
      (two_taint [.x0] ?_ (by taint_decide))
     · rintro q s ⟨bs,h⟩
       refine WP.mono (less_ok h.initial.good q.p.room (by have :=q.p.positive;omega_using [this]) q.p.width
        (by decide : 1<8) (by decide : 5<8)) ?_
       rintro t ⟨_,mem,rest⟩
       exact ⟨bs,h.after_mem mem rest ((rest.gpr .x0 (by simp [mmRegs])).trans h.initial.good.x0)⟩
     · rintro q s t ⟨bs,hs⟩ ⟨bt,ht⟩ r hr
       have eq : r= .x0 := by simpa using hr
       subst r
       exact hs.initial.good.x0.trans ht.initial.good.x0.symm

end VG.Proof.Ffdh.AArch64.Cached

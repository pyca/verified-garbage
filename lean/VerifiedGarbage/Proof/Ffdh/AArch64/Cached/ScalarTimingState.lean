module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.RangeFrame
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SourceEncoding
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.BoundTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.NonzeroTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.MemoryState
import VerifiedGarbage.Proof.Framework.Omega

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
 ⟨scalarWs q,q.dp,q.p.k,q.dl,by change 0<q.p.w;have :=q.p.positive;omega,q.p.width,q.size,q.shape⟩

theorem scalarReady_bound {q : ScalarPublic} {s : State} (h : ScalarReady q s) : BoundReady (scalarBoundPublic q) s := by
 obtain ⟨bs,h⟩ :=h
 exact ⟨⟨q.p.mi,h.initial.good,q.p.room⟩,h.domain,(by change word s.mem q.p.B (8*sLen)=BitVec.ofNat 64 q.p.k;rw [←h.length];exact h.initial.controls.length),h.domainLength⟩

theorem scalarReady_nonzero {q : ScalarPublic} {s : State} (h : ScalarReady q s) :
 WP isa Generate.nonzero s (ScalarReady q) := by
 obtain ⟨bs,h⟩ :=h
 refine WP.mono (nonzero_ok h.initial.good q.p.room (by have :=q.p.positive;omega) q.p.width) ?_
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

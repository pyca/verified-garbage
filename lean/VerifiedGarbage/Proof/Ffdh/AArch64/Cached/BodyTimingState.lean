module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ScalarRangeTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.OutputTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PublicRangeTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.CombTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.KeyStatus
import VerifiedGarbage.Proof.Framework.Omega

/-! Attempt timing fixes only the reviewed public status, with independent secret draws. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure BodyPublic where
 scalar : ScalarPublic
 yp : Addr
 status : Nat
 bitsPositive : 0<scalar.p.N
 bitsBound : scalar.p.N≤8192
 width : scalar.p.N≤8*scalar.p.k
 table : scalar.p.table=scalar.p.ctx+BitVec.ofNat 64 (24+16*scalar.p.w)
 valid : Spec.Ffdh.parametersValid (Spec.Ffdh.domainOf scalar.p.k scalar.dom)=true
 outsideX : ∀ i<scalar.p.k,scalar.p.Z≤ofs scalar.p.B (scalar.p.src+BitVec.ofNat 64 i)

structure BodyState (q : BodyPublic) (bs : List Byte) (s : State) : Prop where
 scalar : ScalarState q.scalar bs s
 bound : Spec.Rsa.os2ip bs<2^q.scalar.p.N
 status : Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf q.scalar.p.k q.scalar.dom) (Spec.Rsa.os2ip bs)=q.status
 y : word s.mem q.scalar.p.B (8*sY)=q.yp
 write : ∀ i<q.scalar.p.k,InRegions s.wr (q.scalar.p.src+BitVec.ofNat 64 i) 1

def BodyReady (q : BodyPublic) (s : State) : Prop := ∃ bs,BodyState q bs s

def bodyOutput (q : BodyPublic) : OutputPublic :=
 ⟨q.scalar.p,q.yp,q.scalar.words,q.scalar.positive,q.scalar.size,q.outsideX⟩

def bodyComb (q : BodyPublic) : CombPublic :=
 ⟨⟨q.scalar.p,q.bitsPositive,q.bitsBound,q.scalar.size,q.width⟩,q.table⟩

theorem bodyReady_output {q : BodyPublic} {s : State} (h : BodyReady q s) : OutputReady (bodyOutput q) s := by
 obtain ⟨bs,h⟩:=h
 exact ⟨h.scalar.initial.good,h.scalar.initial.controls.source,h.y,h.scalar.length ▸ h.scalar.initial.controls.length,h.write⟩

def BodyRangeDone (q : BodyPublic) (s : State) : Prop :=
 BodyReady q s ∧ s.gpr .x9=(if q.status=2 then 0#64 else 1#64)

theorem bodyRangeDone_ok {q : BodyPublic} {s : State} (h : BodyReady q s) :
 WP isa Generate.scalarRange s (BodyRangeDone q) := by
 obtain ⟨bs,h⟩:=h
 have init :=h.scalar.initial
 refine WP.mono (scalarRange_ok init.good q.scalar.p.room q.scalar.words q.scalar.positive q.scalar.size q.scalar.shape q.scalar.domLength
  h.scalar.source (source_src init.reads.source init.reads.scalarOutside) h.scalar.length init.controls.source h.scalar.domain
  (h.scalar.length ▸ init.controls.length) h.scalar.domainLength (init.modulus.trans q.scalar.modulus)
  (by rw [←q.scalar.modulus];exact q.scalar.odd)) ?_
 rintro t ⟨good,_,flag,frame,rest⟩
 have state : BodyState q bs t :=
  ⟨h.scalar.after good frame rest,h.bound,h.status,(scalarFrame_header frame (by decide) (by decide)).trans h.y,
   fun i hi =>by rw [rest.wr];exact h.write i hi⟩
 refine ⟨⟨bs,state⟩,?_⟩
 have rejected := keyStatus_scalar_rejected q.valid (Spec.Rsa.os2ip bs)
 rw [h.status] at rejected
 by_cases scalar : 0<Spec.Rsa.os2ip bs ∧ Spec.Rsa.os2ip bs<Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf q.scalar.p.k q.scalar.dom)
 · rw [ite_eq_left scalar] at flag
   rw [ite_eq_right (fun eq =>rejected.mp eq scalar)]
   exact flag
 · rw [ite_eq_right scalar] at flag
   rw [ite_eq_left (rejected.mpr scalar)]
   exact flag

end VG.Proof.Ffdh.AArch64.Cached

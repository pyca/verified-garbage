module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeFieldTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeFieldFrame
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeTailTiming
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.InverseUnique
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Public modulus setup establishes the table builder's field without assuming prior scratch contents. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

structure ArithmeticPublic where
 table : TablePublic
 nb : List Byte
 value : Spec.Rsa.os2ip nb=table.p.P
 odd : table.p.P%2=1

def arithmeticPc (q : ArithmeticPublic) : PcPub :=
 ⟨q.table.p.B,q.table.p.Z,q.table.p.k,q.table.p.ctx,q.table.dom,q.nb⟩

def arithmeticTable (q : ArithmeticPublic) (mi : BitVec 64) : TablePublic :=
 {q.table with p:={q.table.p with mi:=mi}}

structure ArithmeticReady (q : ArithmeticPublic) (s : State) : Prop where
 pc : PcM (arithmeticPc q) s
 space : ContextSpace q.table.p s
 generator : GeneratorSource q.table.p (q.table.dom+BitVec.ofNat 64 q.table.p.k) q.table.bs s
 rows : word s.mem q.table.p.B (8*sRows)=BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows q.table.p.N)

def ArithmeticDone (q : ArithmeticPublic) (s : State) : Prop :=∃ mi,TableReady (arithmeticTable q mi) s

theorem arithmeticField_done (M : Mont) {q : ArithmeticPublic} {s : State} (h : ArithmeticReady q s) :
 WP isa (seqs (VG.Impl.Rsa.AArch64.pcLoadW++VG.Impl.Rsa.AArch64.r2StepsPub M.mm)) s (ArithmeticDone q) := by
 obtain ⟨scratch,base,room,small,large,ctx,len,dom,source,nbLength,valid,_,_,span⟩:=h.pc
 dsimp only [arithmeticPc,PcPub.w,PcPub.N] at *
 have normalized :=(valid_facts valid small).2.2
 refine WP.mono (precomputeField_ok M scratch base room (by change 9≤q.table.p.k;change 64≤q.table.p.k at small;omega)
  q.table.size len dom source span nbLength (by rw [q.value];exact q.odd) normalized) ?_
 rintro t ⟨mi,good,modulus,inverse,r2,frame,rest⟩
 have field : FieldInitial (arithmeticTable q mi).p t :=by
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [arithmeticTable,q.table.words] using good
  · simpa only [arithmeticTable,q.table.words,q.value] using modulus
  · simpa only [arithmeticTable,q.table.words] using inverse
  · simpa only [arithmeticTable,q.table.words,q.value] using r2
 have inscr : InScr q.table.p.B q.table.p.Z s.mem t.mem :=by
  apply precomputeField_inscr (w:=q.table.p.w) _ q.table.p.room
  simpa only [q.table.words] using frame
 have sourceT:=h.generator.after_inscr inscr rest
 have header (i : Nat) (lo : 16≤i) (hi : i<32) (different : i≠Public.sCnt) :=precomputeField_header frame lo hi different
 exact ⟨mi,⟨field,⟨(h.space.after rest).writable,h.space.outside⟩,
  ⟨sourceT.source,sourceT.length,sourceT.value,sourceT.separate⟩,
  (header sCtx (by decide) (by decide) (by decide)).trans ctx,
  (header sDom (by decide) (by decide) (by decide)).trans dom,
  (header sLen (by decide) (by decide) (by decide)).trans len⟩,
  (header sRows (by decide) (by decide) (by decide)).trans h.rows⟩

theorem arithmeticDone_two {s t : State} (h : Two ArithmeticDone s t) : Two TableReady s t := by
 obtain ⟨q,⟨a,hs⟩,⟨b,ht⟩,sp⟩:=h
 have same : a=b := imported_inverse_unique (p:=q.table.p) hs.field ht.field q.odd
 subst b
 exact ⟨arithmeticTable q a,hs,ht,sp⟩

end VG.Proof.Ffdh.AArch64.Cached

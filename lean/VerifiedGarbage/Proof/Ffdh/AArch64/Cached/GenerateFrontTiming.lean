module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.FrontTimingState
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.GeneratePrepared
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Relate independent entropy draws through context import, sampling, and the complete attempt. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

/-- The inverse is reconstructed; no prior scratch value is assumed. -/
def FrontDone (q : FrontPublic) (s : State) : Prop := ∃ mi,BodyReady (frontBody q mi) s

theorem generateFront_ct : RelCT isa (Two FrontReady) (.seq importPrefix Generate.sample) (fun _ _ =>True) :=
 RelCT.seq (two_post (Ψ:=fun q s =>SampleReady (frontSample q) s)
  (two_map frontImport (fun _ _ h =>frontReady_import h) importPrefix_ct)
  (fun _ _ h =>frontImport_sample h)) (two_map frontSample (fun _ _ h =>h) sample_ct)

theorem front_done_ok {q : FrontPublic} {s : State} (h : FrontReady q s) :
 WP isa (.seq importPrefix Generate.sample) s (FrontDone q) := by
 obtain ⟨rb,h⟩:=h
 refine WP.mono (generateFront_ok h.scratch h.base q.body.scalar.words q.body.scalar.positive q.body.scalar.size q.body.scalar.shape
  q.body.scalar.domLength q.checked q.body.scalar.modulus q.generator q.policy q.body.table h.view h.domainSource h.randomSource h.rbLength
  h.controls h.domain h.domainLength h.y h.random h.bytes q.body.bitsPositive q.body.bitsBound q.body.width
  h.write q.body.outsideX q.separateRand q.separateDomain q.separateContext) ?_
 rintro t ⟨mi,initial,value,domainSource,domain,domainLength,y,rest⟩
 let bs:=Spec.Rsa.bytesAt t.mem q.body.scalar.p.src q.body.scalar.p.k
 refine ⟨mi,bs,⟨initial,initial.reads.length,domainSource,domain,domainLength⟩,?_,?_,y,?_⟩
 · change Spec.Rsa.os2ip bs<2^q.body.scalar.p.N
   rw [value]
   exact Nat.mod_lt _ (Nat.two_pow_pos _)
 · have scalar : Spec.Rsa.os2ip bs=Spec.Ffdh.vettedScalarOfOctets (Spec.Ffdh.domainOf q.body.scalar.p.k q.body.scalar.dom) rb := by
    unfold Spec.Ffdh.vettedScalarOfOctets
    rw [←q.policy]
    exact value
   change Spec.Ffdh.keyStatus (Spec.Ffdh.domainOf q.body.scalar.p.k q.body.scalar.dom) (Spec.Rsa.os2ip bs)=q.body.status
   rw [scalar];exact h.status
 · intro i hi;rw [rest.wr];exact h.write i hi

theorem front_done_two {s t : State} (h : Two FrontDone s t) :
 Two BodyReady s t := by
 obtain ⟨q,⟨a,bs,hs⟩,⟨b,bt,ht⟩,sp⟩:=h
 have same : a=b := imported_inverse_unique (p:=q.body.scalar.p)
  hs.scalar.initial.toFieldInitial ht.scalar.initial.toFieldInitial q.body.scalar.odd
 subst b
 exact ⟨frontBody q a,⟨bs,hs⟩,⟨bt,ht⟩,sp⟩

theorem generatePrepared_ct (M : Mont) :
 RelCT isa (Two FrontReady) (generatePrepared M.mm) (fun _ _ =>True) := by
 unfold generatePrepared
 apply RelCT.assoc
 exact RelCT.seq (two_post generateFront_ct (fun _ _ h =>front_done_ok h))
  ((generateBody_ct M).mono (fun _ _ h =>front_done_two h) (fun _ _ h =>h))

end VG.Proof.Ffdh.AArch64.Cached

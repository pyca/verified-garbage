module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeInput
import VerifiedGarbage.Proof.Bignum.AArch64.PcCode
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! The native initializer returns the exact canonical reviewed context. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached

theorem precompute_correct (M : Mont) {s : State} (pre : precomputePre s) :
 WP isa (Precompute.code M.mm) s fun t =>abiPreserved s t ∧ precomputePost s t :=by
 let g:=precompute_geometry pre
 let q:=precomputeInputPublic s g
 have ns:=precompute_input_ready g
 have records : PolicyTableAt q.p.B (s.syms Policy.tableSym) Policy.groups s :=by
  rw [ns.symbol];exact ns.records
 refine WP.mono (precomputeNative_ok M ns.scratch ns.space ns.output ns.source ns.span
  q.words q.small q.large q.shape q.domLength q.checked q.modulus q.generator q.policy
  ns.context ns.domain ns.domainLength ns.length ns.base records) ?_
 rintro t ⟨status,canonical,frame,rest⟩
 refine ⟨abiPreserved_of_keep rest,?_,?_⟩
 · change (t.gpr .x0).setWidth 32=1#32
   rw [status];rfl
 · change Spec.Ffdh.generationPrecompute (s.gpr .x4).toNat (precomputeDomain s)=
    some (Spec.Rsa.wordsAt t.mem (s.gpr .x0) (s.gpr .x1).toNat)
   rw [g.count]
   change Spec.Rsa.wordsAt t.mem (s.gpr .x0) (Spec.Ffdh.generationPrecomputedWords (s.gpr .x4).toNat)=_ at canonical
   have count : Spec.Ffdh.generationPrecomputedWords (s.gpr .x4).toNat=3+34*(((s.gpr .x4).toNat+7)/8) :=by
    simp only [Spec.Ffdh.generationPrecomputedWords,Spec.Rsa.FixedBaseComb.precomputedWords,Spec.Rsa.precomputedWords,
     Spec.Rsa.FixedBaseComb.entries,Spec.Rsa.FixedBaseComb.teeth,Spec.Rsa.modulusWords]
    omega
   rw [count] at canonical
   rw [canonical]
   apply VG.Proof.Ffdh.generationPrecompute_eq
   · have shape :=g.shape
     have length : (precomputeDomain s).length=(s.gpr .x3).toNat :=by simp only [precomputeDomain,Spec.Rsa.bytesAt,List.length_map,List.length_range]
     change (s.gpr .x4).toNat≤(precomputeDomain s).length
     omega
   · exact VG.Proof.Ffdh.domainValid_mod g.checked

end VG.Proof.Ffdh.AArch64.Cached

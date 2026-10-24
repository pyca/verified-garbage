module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeTimingState
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Metadata writes preserve the domain and establish the public arithmetic setup. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem precomputeMetadata_arithmetic {q : PrecomputePublic} {s : State} (h : PrecomputePolicyDone q s) :
 WP isa Policy.metadata s (ArithmeticReady (precomputeArithmetic q)) := by
 have room :=(precomputeDomainPolicy q).room
 have bits:=precomputeBits q
 refine WP.mono (metadata_ok h.scratch room h.output h.base h.context h.bits bits.1 bits.2) ?_
 rintro t ⟨mem,rest⟩
 have frame : PublicFrame q.p s.mem t.mem :=by rw [mem];exact metadataMemory_frame _ q.p _
 have source:=h.source.after frame rest
 have controls:=metadataMemory_controls h.space h.scratch q.p.N
 rw [←mem] at controls
 have header (i : Nat) (hi : i<32) (notBytes : i≠sBytes) (notRows : i≠sRows) :=controls.2.2 i hi notBytes notRows
 have space:=h.space.after rest
 have domSize : q.p.k≤q.dom.length :=by have :=q.shape;have :=q.domLength;omega
 have nbLength : (q.dom.take q.p.k).length=q.p.k :=by simp only [List.length_take];omega
 refine ⟨?_,?_,?_,controls.2.1⟩
 · change PcM (⟨q.p.B,q.p.Z,q.p.k,q.p.ctx,q.domPtr,q.dom.take q.p.k⟩ : PcPub) t
   refine ⟨h.scratch.congr rest.wr,(rest.gpr .x0 (by decide)).trans h.base,
    by change slot ((q.p.k+7)/8) 8≤q.p.Z;rw [←q.words];exact q.p.room,q.small,q.large,
    (header sCtx (by decide) (by decide) (by decide)).trans h.context,
    (header sLen (by decide) (by decide) (by decide)).trans h.length,
    (header sDom (by decide) (by decide) (by decide)).trans h.domain,
    (source.take q.p.k).toSrc,nbLength,VG.Proof.Ffdh.domainValid_mod q.checked,?_,?_,?_⟩
   · intro i hi
     change i<2*((q.p.k+7)/8) at hi
     rw [←q.words] at hi
     exact space.writable i (by omega)
   · intro i hi
     change i<16*((q.p.k+7)/8) at hi
     rw [←q.words] at hi
     exact space.outside i (by omega)
   · rw [rest.rd,rest.wr];exact h.span
 · exact ⟨space.writable,space.outside⟩
 · exact source.generator (by have :=q.shape;have :=q.domLength;omega) q.generator

end VG.Proof.Ffdh.AArch64.Cached

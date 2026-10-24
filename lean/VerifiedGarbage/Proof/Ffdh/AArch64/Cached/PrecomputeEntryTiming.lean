module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PrecomputeTimingState
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.AArch64.Isa
meta import VerifiedGarbage.Impl.Ffdh.AArch64.Cached.Precompute
meta import VerifiedGarbage.Impl.Bignum.AArch64.Core
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

/-! The public initializer's entry and policy phases establish exact metadata inputs. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64

theorem precomputeEntry_ct : RelCT isa (Two PrecomputeReady) (.block Precompute.entry) (fun _ _ =>True) :=
 two_taint [.x5] (fun _ s t hs ht r hr =>by
  have eq : r= .x5 :=by simpa using hr
  subst r;exact hs.base.trans ht.base.symm) (by taint_decide)

theorem precomputeEntry_entered {q : PrecomputePublic} {s : State} (h : PrecomputeReady q s) :
 WP isa (.block Precompute.entry) s (PrecomputeEntered q) := by
 have room : 256≤q.p.Z :=(precomputeDomainPolicy q).room
 refine WP.mono_syms (precomputeEntry_ok h.scratch room h.base) ?_
 rintro t ⟨⟨base,mem⟩,rest⟩ syms
 have entry : t.mem=entryMemory s.mem q.p.B q.p.ctx q.domPtr (BitVec.ofNat 64 q.dl) (BitVec.ofNat 64 q.p.k) :=by
  rw [mem,h.context,h.domain,h.domainLength,h.length]
 have headers :=entryMemory_header s.mem q.p.B q.p.ctx q.domPtr (BitVec.ofNat 64 q.dl) (BitVec.ofNat 64 q.p.k)
 rw [←entry] at headers
 have inscr : InScr q.p.B q.p.Z s.mem t.mem :=by rw [entry];exact entryMemory_frame _ _ _ _ _ _ _ room
 have publicFrame : PublicFrame q.p s.mem t.mem :=PublicFrame.of_inscr inscr
 have range : Outside q.p.B 128 32 s.mem t.mem :=by rw [entry];exact entryMemory_range _ _ _ _ _ _
 exact ⟨⟨h.scratch.congr rest.wr,h.space.after rest,h.output.congr rest.wr,h.source.after publicFrame rest,
  by rw [rest.rd,rest.wr];exact h.span,base,headers.1,headers.2.1,headers.2.2.1,headers.2.2.2⟩,
  h.records.after_belowBits range rest (by decide),(congrFun syms Policy.tableSym).trans h.symbol⟩

theorem precomputePolicy_metadata {q : PrecomputePublic} {s : State} (h : PrecomputeEntered q s) :
 WP isa Policy.recognize s (PrecomputePolicyDone q) := by
 have room : 256≤q.p.Z :=(precomputeDomainPolicy q).room
 have records : PolicyTableAt q.p.B (s.syms Policy.tableSym) Policy.groups s :=by rw [h.symbol];exact h.records
 refine WP.mono (policyDomain_ok h.scratch room h.base (by have :=q.small;omega) q.large q.shape q.domLength q.checked
  h.domain h.length h.domainLength h.source.toSource
  (fun i hi =>Nat.le_trans (by change 8*sBits+8≤q.p.Z;have :=room;unfold sBits;omega) (h.source.scratchOutside i hi)) records) ?_
 rintro t ⟨bits,frame,rest⟩
 have inscr : InScr q.p.B q.p.Z s.mem t.mem :=InScr.of_outside frame (by change 8*sBits+8≤q.p.Z;have :=room;unfold sBits;omega)
 have header (i : Nat) (hi : i<32) (ne : i≠sBits) :=header_other frame (by decide) hi ne
 exact ⟨⟨h.scratch.congr rest.wr,h.space.after rest,h.output.congr rest.wr,h.source.after (PublicFrame.of_inscr inscr) rest,
  by rw [rest.rd,rest.wr];exact h.span,(rest.gpr .x0 (by simp [recordClobbers])).trans h.base,
  (header sCtx (by decide) (by decide)).trans h.context,(header sDom (by decide) (by decide)).trans h.domain,
  (header sDL (by decide) (by decide)).trans h.domainLength,(header sLen (by decide) (by decide)).trans h.length⟩,
  by rw [q.policy];exact bits⟩

end VG.Proof.Ffdh.AArch64.Cached

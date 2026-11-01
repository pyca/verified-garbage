module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.GatherSplit.Invoke
import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Wp

-- separate module: compose the shared entry, gather loop, split seal and return.
/-! # Correctness of the split gather caller -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.GatherSplit
open VG VG.PPC64LE
open VG.Proof.AesGcm.PPC64LE.Gather
open VG.Proof.ChaCha20Poly1305.PPC64LE (wp_ld wp_lsr)

structure Selected (s u : State) : Prop where
  entered : Gather.Entered s u
  count : u.gpr .r10=s.gpr .r10
  choice : u.gpr .r0=stackArg s 1 >>> 9


theorem select_wp {s e : State} (h : Gather.Lay s) (he : Gather.Entered s e)
    (hcount : e.gpr .r10=s.gpr .r10) :
    WP isa (.block Impl.AesGcm.PPC64LE.GatherSplit.select) e (Selected s) := by
  unfold Impl.AesGcm.PPC64LE.GatherSplit.select
  refine wp_ld (a := sa s 1) (by decide) (by decide) (by rw [he.r12]) (h.sa_in (by decide) e he.rd)
    fun a ha => wp_lsr (by decide) fun u hu => WP.block_nil ?_
  have g {r : Reg} (hr : r≠.r0) : u.gpr r=e.gpr r := (hu.other _ hr).trans (ha.other _ hr)
  have pres : ∀ r∈preserved,r≠.r0 := by decide
  refine ⟨⟨hu.mem.trans (ha.mem.trans he.mem),(g (by decide)).trans he.r7,
    (g (by decide)).trans he.r8,(g (by decide)).trans he.r9,(g (by decide)).trans he.r12,
    fun r hr => (g (pres r hr)).trans (he.pres r hr),hu.sp.trans (ha.sp.trans he.sp),
    hu.rd.trans (ha.rd.trans he.rd),hu.wr.trans (ha.wr.trans he.wr)⟩,
    (g (by decide)).trans hcount,?_⟩
  rw [hu.gpr,ha.gpr,he.mem,h.eArg (by decide)]


theorem fast_wp (hv : SplitOk) {s e : State} (h : Layout s) (he : Gather.Entered s e)
    (hcount : e.gpr .r10=s.gpr .r10) (hc : 0<Cnt s) :
    WP isa Impl.AesGcm.PPC64LE.GatherSplit.fast e
      fun y => abiPreserved s (freed 160 y) ∧ gatherPost s (freed 160 y) := by
  unfold Impl.AesGcm.PPC64LE.GatherSplit.fast
  refine WP.seq (WP.mono (tail_ok (gatherPre_of h.base he) hc) fun t ht => ?_)
  refine WP.seq (WP.mono (prepare_ok h.base he hcount hc ht) fun c hp => ?_)
  refine WP.seq (WP.mono (called_wp hv h he hc hp) fun z hz => ?_)
  exact Gather.ret_wp h.base hz


theorem slow_wp (hv : Gather.SealOk) {s e : State} (h : Gather.Lay s) (he : Gather.Entered s e) :
    WP isa Impl.AesGcm.PPC64LE.SealGather.body e
      fun y => abiPreserved s (freed 160 y) ∧ gatherPost s (freed 160 y) := by
  unfold Impl.AesGcm.PPC64LE.SealGather.body
  refine WP.seq (WP.mono (Gather.gathered_wp h he) fun t ht => ?_)
  refine WP.seq (WP.mono (Gather.ready_wp h ht) fun c hp => ?_)
  refine WP.seq (WP.mono (Gather.called_wp hv h hp) fun z hz => ?_)
  exact Gather.ret_wp h hz


theorem nonempty_of_choice {s : State} (h : Gather.Lay s)
    (hn : (stackArg s 1 >>> 9).toNat≠0) : 0<Cnt s := by
  by_contra hc
  have hz : Cnt s=0 := by omega
  have hl : L s=0 := h.hgl.symm.trans (by rw [hz]; rfl)
  have hw : stackArg s 1=0 := BitVec.eq_of_toNat_eq hl
  rw [hw] at hn
  exact hn rfl


theorem body_wp (hv : Gather.SealOk) (hs : SplitOk) {s e : State} (h : Layout s)
    (he : Gather.Entered s e) (hcount : e.gpr .r10=s.gpr .r10) :
    WP isa Impl.AesGcm.PPC64LE.GatherSplit.body e
      fun y => abiPreserved s (freed 160 y) ∧ gatherPost s (freed 160 y) := by
  unfold Impl.AesGcm.PPC64LE.GatherSplit.body
  refine WP.seq (WP.mono (select_wp h.base he hcount) fun u hu => ?_)
  refine WP.ite (decide ((u.gpr .r0).toNat=0))
    (VG.Proof.Gather.PPC64LE.eval_zero (by rw [BitVec.ofNat_toNat,BitVec.setWidth_eq]) (u.gpr .r0).isLt)
    (fun _ => slow_wp hv h.base hu.entered) (fun _ => ?_)
  have hn : (u.gpr .r0).toNat≠0 := of_decide_eq_false ‹decide ((u.gpr .r0).toNat=0)=false›
  rw [hu.choice] at hn
  exact fast_wp hs h hu.entered hu.count (nonempty_of_choice h.base hn)


theorem sealGather_wp (hv : Gather.SealOk) (hs : SplitOk) {s : State} (h : Layout s) :
    WP isa Impl.AesGcm.PPC64LE.GatherSplit.sealGather s
      fun z => abiPreserved s z ∧ gatherPost s z := by
  unfold Impl.AesGcm.PPC64LE.GatherSplit.sealGather Impl.AesGcm.PPC64LE.SealGather.withBody
  refine WP.alloc ⟨by decide,by decide,by decide⟩ (by have := h.space; omega) ?_
  refine WP.seq (WP.mono (entered_wp h.base) fun e he => ?_)
  exact body_wp hv hs h he.1 he.2

end VG.Proof.AesGcm.PPC64LE.GatherSplit

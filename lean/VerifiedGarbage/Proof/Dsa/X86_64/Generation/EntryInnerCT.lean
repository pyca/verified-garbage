module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PublicContextCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryFrame

/-! # The inner ABI frame preserves the proved generator trace and stack pointer -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MillerRabin.X86_64 VG.Impl.Dsa.X86_64.Generation

theorem generation_alloc {s : State} {bytes : Nat}
    (hb : 0 < bytes ∧ bytes < 4096 ∧ bytes % 8 = 0) (hl : bytes ≤ (s.gpr .rsp).toNat) :
    isa.push (.alloc bytes) s = some (allocState bytes s) := by
  simp only [isa, push, allocState]
  exact ite_eq_left ⟨hb.1, hb.2.1, hb.2.2, hl⟩

theorem generation_free_rsp {s u v : State} {bytes : Nat}
    (h : isa.pop (.free bytes) (allocState bytes s) u = some v) : v.gpr .rsp = s.gpr .rsp := by
  simp only [isa, pop] at h
  split at h
  · rename_i hc
    obtain rfl := Option.some.inj h
    exact freeState_rsp hc.2.2.2.1
  · cases h

theorem entryInner_ct (H : GenerationHashes) (M : Mont) (Sq : MontS) (K : Kernel)
    {s t a b u v : State} (hs : GenerationABI s) (ht : GenerationABI t) (hp : GenerationPublicAgree s t)
    (ga : a.gpr = (allocState 48 s).gpr) (ra : a.rd = s.rd) (wa : a.wr = (allocState 48 s).wr)
    (fa : Frame [⟨savedBase s, 48⟩] s.mem a.mem)
    (gb : b.gpr = (allocState 48 t).gpr) (rb : b.rd = t.rd) (wb : b.wr = (allocState 48 t).wr)
    (fb : Frame [⟨savedBase t, 48⟩] t.mem b.mem) {tsa tsb : List Leak}
    (ea : Exec isa (.frame (.alloc 296) (entryBody H.sha1 H.sha256 Sq.mm M.mm K.run) (.free 296)) a tsa u)
    (eb : Exec isa (.frame (.alloc 296) (entryBody H.sha1 H.sha256 Sq.mm M.mm K.run) (.free 296)) b tsb v) :
    tsa = tsb ∧ u.gpr .rsp = v.gpr .rsp := by
  cases ea with
  | frame pa ba qa =>
    cases eb with
    | frame pb bb qb =>
      rw [generation_alloc (by decide) (outer_stack_room hs ga), Option.some.injEq] at pa
      rw [generation_alloc (by decide) (outer_stack_room ht gb), Option.some.injEq] at pb
      subst pa; subst pb
      have ha := entryInitial_ct hs ga ra wa fa
      have hb := entryInitial_ct ht gb rb wb fb
      rw [← hp.parameter (hs := hs) (ht := ht)] at hb
      have traces := (entryBody_ct H M Sq K 3 (Or.inr rfl) _ _ _ _ _ _ ⟨parameterOf hs, ha, hb⟩ ba bb).1
      refine ⟨by simpa only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] using traces, ?_⟩
      rw [generation_free_rsp qa, generation_free_rsp qb, ga, gb]
      change s.gpr .rsp - BitVec.ofNat 64 48 = t.gpr .rsp - BitVec.ofNat 64 48
      rw [hp.sp]

end VG.Proof.Dsa.X86_64.Generation

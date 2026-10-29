module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Entry
public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryAllocated
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Hashes
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PublicCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeTest

import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryFrame
import VerifiedGarbage.Proof.Framework.X86_64.FrameAlloc
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.DispatchCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryState
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryReady
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntrySetupCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ABIContext
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryInitial
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
/-! # The inner ABI frame preserves the proved generator trace and stack pointer -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/EntryBodyCT.lean`, which only this module imported.
section

/-! # Entry initialization composes with dispatch and the complete generator -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Proof.MillerRabin.X86_64 VG.Impl.Dsa.X86_64.Generation


variable {checkName : String}

def EntryBefore (n : Nat) (p : ParameterPublic) (s : State) : Prop :=
  EntryState p.context s ∧ FrV n p.context.geo.F p.ws s ∧ s.wr = p.wr ∧ p.randUsed = 0

theorem entryReady_ct (n : Nat) :
    RelCT isa (Two (EntryBefore n)) (.block (entryHeader ++ entryIncoming ++ entryDerived))
      (Two (DispatchBefore n)) := by
  refine two_post (entrySetup_ct.mono ?_ (fun _ _ _ => True.intro)) ?_
  · rintro s t ⟨p, hs, ht⟩
    exact hs.1.rsp.trans ht.1.rsp.symm
  · intro p s ⟨h, hf, hw, hz⟩
    refine WP.mono (entryReady_ok h) fun t ⟨W, ht, h16, _, hk⟩ => ?_
    exact ⟨⟨W, ht, by rw [hz]; exact h16⟩,
      hf.congr (hk.gpr (by decide)) hk.2.2, hk.2.2.trans hw, rfl, rfl⟩

theorem entryBody_ct (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest)
    (n : Nat) (hn : n = 2 ∨ n = 3) :
    RelCT isa (Two (EntryBefore n)) (entryBody (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run) (fun _ _ => True) :=
  RelCT.seq (entryReady_ct n) (dispatch_ct (checkName := checkName) H M Sq T n hn)

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/EntryLayoutCT.lean`, which only this module imported.
section

/-! # ABI regions establish the public frame and arithmetic-header layouts -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64

def generationTail (s : State) : List Region :=
  [⟨savedBase s, 48⟩, ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨stackArg s 4, (stackArg s 5).toNat * 8⟩]

def generationRegions (s : State) : List Region := ⟨generationBase s, frameBytes⟩ :: generationTail s

theorem generationRegions_pairwise {s : State} (h : GenerationABI s) :
    (generationRegions s).Pairwise Region.Disjoint := by
  have frameSave : (⟨generationBase s, frameBytes⟩ : Region).Disjoint ⟨savedBase s, 48⟩ := by
    have he : generationBase s = savedBase s - BitVec.ofNat 64 296 := by
      simp only [generationBase, savedBase, BitVec.sub_sub]; rfl
    rw [he]
    exact (Offset.base_disjoint_below (savedBase s) (n := 296) (k := 48) (by decide)).symm
  have frameOut := h.stackOut.sub_left (generation_frame_sub s)
  have frameScratch := h.stackScratch.sub_left (generation_frame_sub s)
  have saveOut := h.stackOut.sub_left (saved_frame_sub s)
  have saveScratch := h.stackScratch.sub_left (saved_frame_sub s)
  simp [generationRegions, generationTail, List.pairwise_cons, frameSave, frameOut, frameScratch,
    saveOut, saveScratch, h.outScratch]

theorem generationRegions_lengths {s : State} (h : GenerationABI s) :
    ∀ r ∈ generationRegions s, r.len ≤ 2 ^ 64 := by
  intro r hr
  simp only [generationRegions, generationTail, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · change 296 ≤ 2 ^ 64; decide
  · change 48 ≤ 2 ^ 64; decide
  · exact Nat.le_of_lt (s.gpr .rsi).isLt
  · change (stackArg s 5).toNat * 8 ≤ 2 ^ 64
    have := h.scratchBound; omega

theorem generationRegions_header {s : State} (h : GenerationABI s) :
    PrimeHeaderLayout (stackArg s 4) (generationRegions s) := by
  refine ⟨_, _, _, (stackArg s 5).toNat * 8, rfl, ?_, generationRegions_pairwise h, generationRegions_lengths h⟩
  have hs := generation_scratch_size h
  change 28928 ≤ (stackArg s 5).toNat * 8
  change 40960 + 128 * (s.gpr .rdx).toNat ≤ (stackArg s 5).toNat * 8 at hs
  omega

def parameterOf {s : State} (h : GenerationABI s) : ParameterPublic where
  context := contextOf h
  seedUsed := 0
  seedBound := Nat.zero_le _
  randUsed := 0
  randBound := Nat.zero_le _
  ws := generationTail s
  wr := generationRegions s
  header := generationRegions_header h

theorem entryInitial_ct {s u : State} (h : GenerationABI s)
    (hg : u.gpr = (allocState 48 s).gpr) (hr : u.rd = s.rd)
    (hw : u.wr = (allocState 48 s).wr) (hf : Frame [⟨savedBase s, 48⟩] s.mem u.mem) :
    EntryBefore 3 (parameterOf h) (allocState 296 u) := by
  have wr : (allocState 296 u).wr = generationRegions s := by
    change (⟨u.gpr .rsp - BitVec.ofNat 64 296, 296⟩ :: u.wr) = _
    rw [hw, hg]
    change (⟨(allocState 296 (allocState 48 s)).gpr .rsp, 296⟩ :: ⟨savedBase s, 48⟩ :: s.wr) = _
    rw [allocated_rsp rfl, h.wr]
    rfl
  refine ⟨entryInitial h hg hr hw hf, ?_, wr, rfl⟩
  exact ⟨allocated_rsp hg, wr, rfl, generationRegions_pairwise h,
    fun r hr => generationRegions_lengths h r (List.mem_cons_of_mem _ hr)⟩

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/PublicContextCT.lean`, which only this module imported.
section

/-! # Equal public ABI inputs determine the same complete generation plan -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

theorem GenerationTape.heq_of_data {p q : GenerationGeometry} {a : GenerationTape p} {b : GenerationTape q}
    (hg : p = q) (hp : a.ptr = b.ptr) (hb : a.bytes = b.bytes) : HEq a b := by
  cases hg
  cases a
  cases b
  cases hp
  cases hb
  rfl

theorem GenerationContext.eq_of_data {a b : GenerationContext}
    (hg : a.geo = b.geo) (hs : HEq a.seeds b.seeds) (hh : HEq a.hs b.hs)
    (hr : HEq a.rand b.rand) (hw : a.saved = b.saved) : a = b := by
  cases a
  cases b
  cases hg
  cases hs
  cases hh
  cases hr
  cases hw
  rfl

theorem GenerationPublicAgree.context {s t : State} {hs : GenerationABI s} {ht : GenerationABI t}
    (h : GenerationPublicAgree s t) : contextOf hs = contextOf ht := by
  have di := h.regs .rdi (by decide)
  have si := h.regs .rsi (by decide)
  have dx := h.regs .rdx (by decide)
  have cx := h.regs .rcx (by decide)
  have r8 := h.regs .r8 (by decide)
  have r9 := h.regs .r9 (by decide)
  have a0 := h.args 0 (by decide)
  have a1 := h.args 1 (by decide)
  have a2 := h.args 2 (by decide)
  have a3 := h.args 3 (by decide)
  have a4 := h.args 4 (by decide)
  have geo : geometryOf hs = geometryOf ht := by
    unfold geometryOf
    congr 1
    · exact congrArg (fun x => x - BitVec.ofNat 64 344) h.sp
    · exact congrArg BitVec.toNat dx
    · exact congrArg BitVec.toNat cx
  have words : abiWords s = abiWords t := by
    funext k
    unfold abiWords
    split <;> simp only [di, si, dx, cx, r8, r9, a0, a1, a2, a3, a4]
  exact GenerationContext.eq_of_data geo
    (GenerationTape.heq_of_data geo r8 h.seeds)
    (GenerationTape.heq_of_data geo a0 h.hs)
    (GenerationTape.heq_of_data geo a2 h.rand) words

theorem GenerationPublicAgree.parameter {s t : State} {hs : GenerationABI s} {ht : GenerationABI t}
    (h : GenerationPublicAgree s t) : parameterOf hs = parameterOf ht := by
  have hc := h.context (hs := hs) (ht := ht)
  have tail : generationTail s = generationTail t := by
    simp only [generationTail, savedBase, h.sp, h.regs .rdi (by decide), h.regs .rsi (by decide),
      h.args 4 (by decide), h.args 5 (by decide)]
  have regions : generationRegions s = generationRegions t := by
    simp only [generationRegions, generationBase, h.sp, tail]
  simp only [parameterOf, hc, tail, regions]

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MillerRabin.X86_64 VG.Impl.Dsa.X86_64.Generation


variable {checkName : String}

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

theorem entryInner_ct (H : GenerationHashes) (M : Mont) (Sq : MontS) (T : PrimeTest)
    {s t a b u v : State} (hs : GenerationABI s) (ht : GenerationABI t) (hp : GenerationPublicAgree s t)
    (ga : a.gpr = (allocState 48 s).gpr) (ra : a.rd = s.rd) (wa : a.wr = (allocState 48 s).wr)
    (fa : Frame [⟨savedBase s, 48⟩] s.mem a.mem)
    (gb : b.gpr = (allocState 48 t).gpr) (rb : b.rd = t.rd) (wb : b.wr = (allocState 48 t).wr)
    (fb : Frame [⟨savedBase t, 48⟩] t.mem b.mem) {tsa tsb : List Leak}
    (ea : Exec isa (.frame (.alloc 296) (entryBody (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run) (.free 296)) a tsa u)
    (eb : Exec isa (.frame (.alloc 296) (entryBody (checkName := checkName) H.sha1 H.sha256 Sq.mm M.mm T.run) (.free 296)) b tsb v) :
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
      have traces := (entryBody_ct (checkName := checkName) H M Sq T 3 (Or.inr rfl) _ _ _ _ _ _ ⟨parameterOf hs, ha, hb⟩ ba bb).1
      refine ⟨by simpa only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] using traces, ?_⟩
      rw [generation_free_rsp qa, generation_free_rsp qb, ga, gb]
      change s.gpr .rsp - BitVec.ofNat 64 48 = t.gpr .rsp - BitVec.ofNat 64 48
      rw [hp.sp]

end VG.Proof.Dsa.X86_64.Generation

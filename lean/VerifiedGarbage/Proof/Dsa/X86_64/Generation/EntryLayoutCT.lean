module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryBodyCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ABIContext
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryAllocated
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryInitial
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset

/-! # ABI regions establish the public frame and arithmetic-header layouts -/

@[expose] public section
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

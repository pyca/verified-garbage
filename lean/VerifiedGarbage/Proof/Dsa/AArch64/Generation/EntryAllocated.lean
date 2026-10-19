module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ABIContext
import VerifiedGarbage.Proof.Framework.Omega

/-! The native frame leaves all incoming arguments and input bytes intact. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

def allocState (bytes : Nat) (s : State) : State :=
  { s with sp := s.sp - BitVec.ofNat 64 bytes, wr := ⟨s.sp - BitVec.ofNat 64 bytes, bytes⟩ :: s.wr }

def freeState (bytes : Nat) (s : State) : State :=
  { s with sp := s.sp + BitVec.ofNat 64 bytes, wr := s.wr.tail }

theorem generation_incoming_address (s : State) (j : Nat) :
    off (generationBase s) (448 + 8 * j) = stackArgAddr s j := by
  simp only [generationBase, off, stackArgAddr, BitVec.ofNat_add]
  rw [← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem allocated_incoming_read {s : State} (h : GenerationABI s) (j : Nat) (hj : j < 4) :
    InRegions ((allocState 448 s).rd ++ (allocState 448 s).wr)
      (off (generationBase s) (448 + 8 * j)) 8 := by
  rw [generation_incoming_address]
  refine ⟨⟨stackArgAddr s 0, 32⟩, List.mem_append_left _ ?_, ?_⟩
  · change _ ∈ s.rd
    rw [h.rd]; simp
  · simp only [stackArgAddr]
    exact Offset.contains _ (d := 8 * j) (n := 8) (e := 0) (k := 32)
      (by omega) (by omega) (by decide)

theorem allocated_tape {s : State} (h : GenerationABI s)
    (ptr : Addr) (len : BitVec 64)
    (bound : ptr.toNat + len.toNat ≤ 2 ^ 64)
    (arena : (⟨ptr, len.toNat⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩)
    (stack : (below s.sp 464).Disjoint ⟨ptr, len.toNat⟩)
    (hin : (⟨ptr, len.toNat⟩ : Region) ∈ s.rd) :
    GenerationTapeMemory (tapeOf h ptr len bound arena stack) (allocState 448 s) where
  cover := by
    intro a n ha
    simp only [tapeOf, bytesAt_length, InRegions, List.mem_singleton] at ha
    obtain ⟨r, rfl, ha⟩ := ha
    exact ⟨_, List.mem_append_left _ hin, ha⟩
  bytes := by simp only [allocState, tapeOf, bytesAt_length]

theorem alloc_frame_ok {bytes : Nat} (hb : 0 < bytes ∧ bytes < 4096 ∧ bytes % 16 = 0)
    {s : State} (hl : bytes ≤ s.sp.toNat) {body : Prog isa} {Q : State → Prop}
    (run : WP isa body (allocState bytes s) fun t =>
      t.sp = (allocState bytes s).sp ∧ t.wr = (allocState bytes s).wr ∧ Q (freeState bytes t)) :
    WP isa (.frame (.alloc bytes) body (.free bytes)) s Q := by
  obtain ⟨trace, t, he, hsp, hwr, hq⟩ := run
  have ha : isa.push (.alloc bytes) s = some (allocState bytes s) := by
    simp only [isa, push, allocState]
    exact ite_eq_left ⟨hb.1, hb.2.1, hb.2.2, hl⟩
  have hf : isa.pop (.free bytes) (allocState bytes s) t = some (freeState bytes t) := by
    simp only [isa, pop]
    exact ite_eq_left ⟨hb.1, hb.2.1, hb.2.2, hsp, hwr, rfl⟩
  exact ⟨_, _, Exec.frame ha he hf, hq⟩

end VG.Proof.Dsa.AArch64.Generation

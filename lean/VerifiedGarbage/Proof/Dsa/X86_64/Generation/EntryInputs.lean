module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryAllocated
import VerifiedGarbage.Proof.Framework.Omega

/-! # Incoming stack arguments remain readable after both entry allocations -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.RsaOaep.X86_64

theorem allocated_incoming_read {s u : State} (h : GenerationABI s) (hr : u.rd = s.rd)
    (j : Nat) (hj : j < 6) :
    InRegions ((allocState 296 u).rd ++ (allocState 296 u).wr)
      (off (generationBase s) (352 + 8 * j)) 8 := by
  rw [generation_incoming_address]
  refine ⟨⟨stackArgAddr s 0, 48⟩, List.mem_append_left _ ?_, ?_⟩
  · change _ ∈ u.rd
    rw [hr, h.rd]
    simp
  · simp only [stackArgAddr]
    exact Offset.contains _ (d := 8 * (j + 1)) (n := 8) (e := 8) (k := 48)
      (by omega) (by omega) (by decide)

theorem allocated_incoming_word {s u : State} (h : GenerationABI s)
    (hf : Frame [⟨savedBase s, 48⟩] s.mem u.mem) (j : Nat) (hj : j < 6) :
    word (allocState 296 u).mem (generationBase s) (352 + 8 * j) = stackArg s j := by
  change u.mem.readW (off (generationBase s) (352 + 8 * j)) 64 = _
  rw [generation_incoming_address]
  change u.mem.readW (stackArgAddr s j) 64 = s.mem.readW (stackArgAddr s j) 64
  apply hf.readW (r := ⟨stackArgAddr s 0, 48⟩)
  · simp only [stackArgAddr]
    exact Offset.contains _ (d := 8 * (j + 1)) (n := 8) (e := 8) (k := 48)
      (by omega) (by omega) (by decide)
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact (h.stackArgs.sub_left (saved_frame_sub s)).symm
  · decide

theorem allocated_register {s u : State} (hg : u.gpr = (allocState 48 s).gpr)
    (r : Reg) (hr : r ≠ .rsp) : (allocState 296 u).gpr r = s.gpr r := by
  simp only [allocState, State.setReg]
  simp [hr, hg, allocState, State.setReg]

theorem allocated_frame {s u : State} (hg : u.gpr = (allocState 48 s).gpr) :
    (⟨generationBase s, frameBytes⟩ : Region) ∈ (allocState 296 u).wr := by
  have he := allocated_rsp hg
  change u.gpr .rsp - BitVec.ofNat 64 296 = generationBase s at he
  change _ ∈ ⟨u.gpr .rsp - BitVec.ofNat 64 296, 296⟩ :: u.wr
  rw [he]
  exact List.mem_cons_self ..

end VG.Proof.Dsa.X86_64.Generation

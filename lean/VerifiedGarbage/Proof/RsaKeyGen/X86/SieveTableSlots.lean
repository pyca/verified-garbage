module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveCandidateSlots
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveAdvancedMem

/-! # Initialize the static cursor, public table length and hit word -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.Sieve

theorem tableSlots_ok {g : Geometry} (v : g.Valid) {c : Nat} {s : State} (C : CandidateReady g c s)
    (length : g.limit = tableCount g.w) (pointer : s.gpr .eax = g.table) :
    WP isa (.block (tableSlots stackSlots g.w)) s fun t =>
      StateAt g c 0 g.limit t ∧ Outside (g.sp.setWidth 64) 0 20 s.mem t.mem ∧ Keeps [.eax] s t := by
  change WP isa (.block ([.store (slot 8) .eax] ++ ([.mov .eax (.imm (BitVec.ofNat 32 (tableCount g.w))),
    .store (slot 12) .eax] ++ [.mov .eax (.imm 0), .store (slot 16) .eax]))) s _
  refine WP.block_append (WP.mono (C.context.stack.store 8 (by decide) .eax) fun a ⟨Ma, Oa, Ka, Ca⟩ => ?_)
  refine WP.block_append (WP.mono (Ca.literal 12 (by decide) (BitVec.ofNat 32 (tableCount g.w)))
    fun b ⟨Mb, Ob, Kb, Cb⟩ => ?_)
  refine WP.mono (Cb.literal 16 (by decide) 0#32) fun t ⟨Mt, Ot, Kt, _⟩ => ?_
  have mem : t.mem = ((s.mem.writeW (off (g.sp.setWidth 64) 8) g.table).writeW
      (off (g.sp.setWidth 64) 12) (BitVec.ofNat 32 g.limit)).writeW (off (g.sp.setWidth 64) 16) 0#32 := by
    rw [Mt, Mb, Ma, pointer, ← length]
  have outside : Outside (g.sp.setWidth 64) 0 20 s.mem t.mem :=
    ((Oa.mono (by decide) (by decide)).trans (Ob.mono (by decide) (by decide))).trans (Ot.mono (by decide) (by decide))
  have keep : Keeps [.eax] s t := ((Ka.mono (by decide)).trans Kb).trans Kt
  refine ⟨⟨C.context.keep v keep (by decide) (outsideStack_frame outside), ?_, ?_, ?_, ?_⟩, outside, keep⟩
  · rw [mem, stack_write_ne (by decide) (by decide) (by decide),
      stack_write_ne (by decide) (by decide) (by decide), stack_write_ne (by decide) (by decide) (by decide)]
    exact C.candidate
  · rw [mem, stack_write_ne (by decide) (by decide) (by decide),
      stack_write_ne (by decide) (by decide) (by decide), stack_write_ne (by decide) (by decide) (by decide)]
    exact C.ending
  · rw [mem, stack_write_ne (by decide) (by decide) (by decide),
      stack_write_ne (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
    unfold Geometry.cursor
    rw [Nat.mul_zero, show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.add_zero]
  · rw [mem, stack_write_ne (by decide) (by decide) (by decide), Mem.readW_writeW_self32]

end VG.Proof.RsaKeyGen.X86.Sieve

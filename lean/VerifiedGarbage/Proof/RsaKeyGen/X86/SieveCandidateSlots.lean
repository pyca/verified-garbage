module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveContext
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveAdvancedMem

/-! # Install the candidate's fixed public pointer and end in the sieve frame -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen.X86.Sieve

structure CandidateReady (g : Geometry) (c : Nat) (s : State) : Prop where
  context : Context g c s
  candidate : s.mem.readW (off (g.sp.setWidth 64) 0) 32 = g.candidate
  ending : s.mem.readW (off (g.sp.setWidth 64) 4) 32 = g.ending

theorem candidateSlots_ok {g : Geometry} (v : g.Valid) {c : Nat} {s : State} (C : Context g c s)
    (pointer : s.gpr .edi = g.candidate) :
    WP isa (.block (candidateSlots stackSlots g.w)) s fun t =>
      CandidateReady g c t ∧ Outside (g.sp.setWidth 64) 0 20 s.mem t.mem ∧ Keeps [.eax] s t := by
  change WP isa (.block ([.store (slot 0) .edi] ++ [.mov .eax (.reg .edi),
    .alu .add .eax (.imm (BitVec.ofNat 32 (8 * g.w))), .store (slot 4) .eax])) s _
  refine WP.block_append (WP.mono (C.stack.store 0 (by decide) .edi) fun a ⟨Ma, Oa, Ka, Ca⟩ => ?_)
  refine wp_movS rfl fun b B _ => wp_addS rfl fun d D _ => ?_
  have K : Keeps [.eax] s d := ((Ka.mono (by decide)).widen B.keeps).trans D.keeps
  have Md : d.mem = a.mem := D.mem.trans B.mem
  have value : d.gpr .eax = g.ending := by
    rw [D.gpr, B.gpr, Ka.1 .edi (by decide), pointer]
    rfl
  refine WP.mono ((C.stack.keep K (by decide)).store 4 (by decide) .eax)
    fun t ⟨Mt, Ot, Kt, _⟩ => ?_
  have mem : t.mem = (s.mem.writeW (off (g.sp.setWidth 64) 0) g.candidate).writeW (off (g.sp.setWidth 64) 4) g.ending := by
    rw [Mt, value, Md, Ma, pointer]
  have outside : Outside (g.sp.setWidth 64) 0 20 s.mem t.mem := by
    rw [Md] at Ot
    exact (Oa.mono (by decide) (by decide)).trans (Ot.mono (by decide) (by decide))
  have keep : Keeps [.eax] s t := K.widen Kt
  refine ⟨⟨C.keep v keep (by decide) (outsideStack_frame outside), ?_, ?_⟩, outside, keep⟩
  · rw [mem, stack_write_ne (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  · rw [mem, Mem.readW_writeW_self32]

end VG.Proof.RsaKeyGen.X86.Sieve

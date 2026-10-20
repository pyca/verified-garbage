module

import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.CallEntry
import VerifiedGarbage.Proof.Mont.X86.ArgFar
public import VerifiedGarbage.Impl.MillerRabin.X86.Layout
import VerifiedGarbage.Proof.MillerRabin.X86.Context

/-! # Load the length before pushing Montgomery's cdecl arguments -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Mont.X86.Dynamic (readSrc_upd)

theorem mulSetup_ok {g : Geometry} {s : State} (C : Context g s)
    (capacity b : Nat)
    (readLen : readSrc s (.mem (at_ .esp 24)) = some (BitVec.ofNat 32 capacity)) :
    WP isa (.block [.mov .eax (.imm (BitVec.ofNat 32 b)), .mov .ecx (.imm 6),
      .mov .edx (.mem (at_ .esp 24))]) s fun t =>
      MulArguments g capacity b t ∧ t.mem = s.mem ∧ Keeps [.eax, .ecx, .edx] s t := by
  refine wp_movS rfl fun a A _ => wp_movS rfl fun b₁ B _ => ?_
  have readB : readSrc b₁ (.mem (at_ .esp 24)) = some (BitVec.ofNat 32 capacity) := by
    rw [readSrc_upd B (by decide), readSrc_upd A (by decide)]
    exact readLen
  refine wp_movS readB fun t T _ => WP.block_nil ?_
  have K : Keeps [.eax, .ecx, .edx] s t := ((A.keeps.mono (by decide)).widen B.keeps).widen T.keeps
  refine ⟨⟨?_, T.gpr, by rw [T.other .ecx (by decide)]; exact B.gpr,
    by rw [T.other .eax (by decide), B.other .eax (by decide)]; exact A.gpr⟩,
    T.mem.trans (B.mem.trans A.mem), K⟩
  rw [K.1 .edi (by decide)]
  apply BitVec.eq_of_toNat_eq
  rw [C.base]
  rfl

end VG.Proof.MillerRabin.X86

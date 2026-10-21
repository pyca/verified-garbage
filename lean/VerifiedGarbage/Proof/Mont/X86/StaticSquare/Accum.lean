module

public import VerifiedGarbage.Impl.Mont.X86.StaticSquare
import VerifiedGarbage.Proof.Mont.X86.StaticSquare.CarryMath
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Scalar MUL results enter a 96-bit accumulator -/

@[expose] public section
namespace VG.Proof.Mont.X86.StaticSquare
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont.X86

def value (s : State) : Nat :=
 (s.gpr .esi).toNat+2^32*(s.gpr .ebx).toNat+2^64*(s.gpr .ecx).toNat

theorem accum_ok (s : State)
    (bound : value s+(s.gpr .eax).toNat+2^32*(s.gpr .edx).toNat<2^96) :
    WP isa (.block VG.Impl.Mont.X86.Rt.StaticSquare.accum) s fun z =>
      value z=value s+(s.gpr .eax).toNat+2^32*(s.gpr .edx).toNat ∧
      Keeps [.esi,.ebx,.ecx] s z ∧ z.mem=s.mem := by
  let c := decide (2^32≤(s.gpr .esi).toNat+(s.gpr .eax).toNat)
  let d := decide (2^32≤(s.gpr .ebx).toNat+(s.gpr .edx).toNat+c.toNat)
  unfold VG.Impl.Mont.X86.Rt.StaticSquare.accum
  refine wp_addS rfl fun s₁ U₁ C₁ => ?_
  have C : s₁.cf=some c := C₁
  refine wp_adcS rfl C fun s₂ U₂ C₂ => ?_
  have D : s₂.cf=some d := by
    simpa only [U₁.other .ebx (by decide),U₁.other .edx (by decide)] using C₂
  refine wp_adcS rfl D fun z U₃ _ => WP.block_nil ?_
  have L : (z.gpr .esi).toNat=((s.gpr .esi).toNat+(s.gpr .eax).toNat)%2^32 := by
    rw [U₃.other .esi (by decide),U₂.other .esi (by decide),U₁.gpr,BitVec.toNat_add]
  have M : (z.gpr .ebx).toNat=((s.gpr .ebx).toNat+(s.gpr .edx).toNat+c.toNat)%2^32 := by
    rw [U₃.other .ebx (by decide),U₂.gpr,add3_toNat,U₁.other .ebx (by decide),U₁.other .edx (by decide)]
  have H : (z.gpr .ecx).toNat=((s.gpr .ecx).toNat+d.toNat)%2^32 := by
    rw [U₃.gpr,add3_toNat,U₂.other .ecx (by decide),U₁.other .ecx (by decide)]
    rfl
  refine ⟨?_,?_,U₃.mem.trans (U₂.mem.trans U₁.mem)⟩
  · rw [value,L,M,H]
    exact accum96 (s.gpr .esi).isLt (s.gpr .ebx).isLt (s.gpr .ecx).isLt
      (s.gpr .eax).isLt (s.gpr .edx).isLt bound
  · have K : Keeps [.esi,.ebx,.ecx] s s₁ := U₁.keeps.mono (by decide)
    exact (K.trans (U₂.keeps.mono (by decide))).trans (U₃.keeps.mono (by decide))

end VG.Proof.Mont.X86.StaticSquare

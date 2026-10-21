module

public import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Accum
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.StaticSquare.CarryMath
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

/-! # The preceding column carry enters the accumulator -/

@[expose] public section
namespace VG.Proof.Mont.X86.StaticSquare
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont.X86 VG.Proof.Mont

theorem carryIn_ok {s : State} {W : Addr} {L S : Nat}
    (hw : Rt.Ws s W L) (ptr : Rt.PtrAt s W .edi S) (fits : S+16≤L)
    (bound : value s+w32 s.mem W (S+8)+2^32*w32 s.mem W (S+12)<2^96) :
    WP isa (.block VG.Impl.Mont.X86.Rt.StaticSquare.carryIn) s fun z =>
      value z=value s+w32 s.mem W (S+8)+2^32*w32 s.mem W (S+12) ∧
      Keeps [.esi,.ebx,.ecx] s z ∧ z.mem=s.mem := by
  let c := decide (2^32≤(s.gpr .esi).toNat+w32 s.mem W (S+8))
  let d := decide (2^32≤(s.gpr .ebx).toNat+w32 s.mem W (S+12)+c.toNat)
  unfold VG.Impl.Mont.X86.Rt.StaticSquare.carryIn
  refine wp_addS (Rt.readSrc_ptr hw ptr (by omega)) fun s₁ U₁ C₁ => ?_
  have C : s₁.cf=some c := C₁
  have h₁ := hw.of_keeps U₁.keeps
  have p₁ : Rt.PtrAt s₁ W .edi S := by rw [Rt.PtrAt,U₁.other .edi (by decide)]; exact ptr
  refine wp_adcS (Rt.readSrc_ptr h₁ p₁ (by omega)) C fun s₂ U₂ C₂ => ?_
  have D : s₂.cf=some d := by
    simpa only [U₁.other .ebx (by decide),U₁.mem] using C₂
  refine wp_adcS rfl D fun z U₃ _ => WP.block_nil ?_
  have L : (z.gpr .esi).toNat=((s.gpr .esi).toNat+w32 s.mem W (S+8))%2^32 := by
    rw [U₃.other .esi (by decide),U₂.other .esi (by decide),U₁.gpr,BitVec.toNat_add]
  have M : (z.gpr .ebx).toNat=((s.gpr .ebx).toNat+w32 s.mem W (S+12)+c.toNat)%2^32 := by
    rw [U₃.other .ebx (by decide),U₂.gpr,add3_toNat,U₁.other .ebx (by decide),U₁.mem]
  have H : (z.gpr .ecx).toNat=((s.gpr .ecx).toNat+d.toNat)%2^32 := by
    rw [U₃.gpr,add3_toNat,U₂.other .ecx (by decide),U₁.other .ecx (by decide)]
    rfl
  refine ⟨?_,?_,U₃.mem.trans (U₂.mem.trans U₁.mem)⟩
  · rw [value,L,M,H]
    exact accum96 (s.gpr .esi).isLt (s.gpr .ebx).isLt (s.gpr .ecx).isLt
      (s.mem.readW (off W (S+8)) 32).isLt (s.mem.readW (off W (S+12)) 32).isLt bound
  · have K : Keeps [.esi,.ebx,.ecx] s s₁ := U₁.keeps.mono (by decide)
    exact (K.trans (U₂.keeps.mono (by decide))).trans (U₃.keeps.mono (by decide))

end VG.Proof.Mont.X86.StaticSquare

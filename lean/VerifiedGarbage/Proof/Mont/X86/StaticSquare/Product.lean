module

public import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Accum
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.Words32

/-! # A product from public workspace pointers enters the scalar sum -/

@[expose] public section
namespace VG.Proof.Mont.X86.StaticSquare
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem value_keeps {s t : State} (h : Keeps [.eax,.edx] s t) : value t=value s := by
  simp only [value,h.1 .esi (by decide),h.1 .ebx (by decide),h.1 .ecx (by decide)]

theorem product_ok {s : State} {W : Addr} {L x y d d' : Nat} {r r' : Reg}
    (hw : Ws s W L) (hx : PtrAt s W r x) (hy : PtrAt s W r' y) (hne : r'≠.eax)
    (xl : x+d+4≤L) (yl : y+d'+4≤L)
    (bound : value s+w32 s.mem W (x+d)*w32 s.mem W (y+d')<2^96) :
    WP isa (.block (VG.Impl.Mont.X86.Rt.StaticSquare.product r r' d d')) s fun z =>
      value z=value s+w32 s.mem W (x+d)*w32 s.mem W (y+d') ∧
      Keeps [.eax,.edx,.esi,.ebx,.ecx] s z ∧ z.mem=s.mem := by
  unfold VG.Impl.Mont.X86.Rt.StaticSquare.product
  simp only [List.cons_append,List.nil_append]
  refine wp_movS (readSrc_ptr hw hx xl) fun s₁ U₁ _ => ?_
  have hw₁ := hw.of_keeps U₁.keeps
  have hy₁ : PtrAt s₁ W r' y := by rw [PtrAt,U₁.other r' hne]; exact hy
  refine wp_movS (readSrc_ptr hw₁ hy₁ yl) fun s₂ U₂ _ => ?_
  refine wp_mul fun s₃ U₃ => ?_
  have K₀ : Keeps [.eax,.edx] s s₃ :=
    ((U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans U₃.keeps
  have P : (s₃.gpr .eax).toNat+2^32*(s₃.gpr .edx).toNat=
      w32 s.mem W (x+d)*w32 s.mem W (y+d') := by
    rw [U₃.eax,U₃.edx,U₂.other .eax (by decide),U₁.gpr,U₂.gpr,U₁.mem]
    exact (mul_words _ _).1
  have bound₃ : value s₃+(s₃.gpr .eax).toNat+2^32*(s₃.gpr .edx).toNat<2^96 := by
    rw [value_keeps K₀,Nat.add_assoc,P]
    exact bound
  refine WP.mono (accum_ok s₃ bound₃) fun z ⟨V,K,M⟩ => ⟨?_,?_,?_⟩
  · rw [V,value_keeps K₀,Nat.add_assoc,P]
  · have Kstart : Keeps [.eax,.edx,.esi,.ebx,.ecx] s s₃ := K₀.mono (by decide)
    exact Kstart.trans (K.mono (by decide))
  · exact M.trans (U₃.mem.trans (U₂.mem.trans U₁.mem))

end VG.Proof.Mont.X86.StaticSquare

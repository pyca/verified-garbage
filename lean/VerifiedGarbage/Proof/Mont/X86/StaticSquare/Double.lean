module

public import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Accum
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.StaticSquare.CarryMath

/-! # Doubling a column's off-diagonal sum -/

@[expose] public section
namespace VG.Proof.Mont.X86.StaticSquare
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86

private theorem double96 {l m h : Nat} (hl : l<2^32) (hm : m<2^32) (_hh : h<2^32)
    (bound : 2*(l+2^32*m+2^64*h)<2^96) :
    let c := decide (2^32≤l+l)
    let d := decide (2^32≤m+m+c.toNat)
    (l+l)%2^32+2^32*((m+m+c.toNat)%2^32)+2^64*((h+h+d.toNat)%2^32)=
      2*(l+2^32*m+2^64*h) := by
  intro c d
  have hc := Bool.toNat_le c
  have hd := Bool.toNat_le d
  have E₁ := word_carry (t:=l+l) (by omega)
  have E₂ := word_carry (t:=m+m+c.toNat) (by omega)
  change (l+l)%2^32+2^32*c.toNat=l+l at E₁
  change (m+m+c.toNat)%2^32+2^32*d.toNat=m+m+c.toNat at E₂
  have high : h+h+d.toNat<2^32 := by omega
  rw [Nat.mod_eq_of_lt high]
  omega

 theorem double_ok (s : State) (bound : 2*value s<2^96) :
    WP isa (.block VG.Impl.Mont.X86.Rt.StaticSquare.double) s fun t =>
      value t=2*value s ∧ Keeps [.esi,.ebx,.ecx] s t ∧ t.mem=s.mem := by
  let c := decide (2^32≤(s.gpr .esi).toNat+(s.gpr .esi).toNat)
  let d := decide (2^32≤(s.gpr .ebx).toNat+(s.gpr .ebx).toNat+c.toNat)
  unfold VG.Impl.Mont.X86.Rt.StaticSquare.double
  refine wp_addS rfl fun u U C => ?_
  have cu : u.cf=some c := C
  refine wp_adcS rfl cu fun v V D => ?_
  have dv : v.cf=some d := by simpa only [U.other .ebx (by decide)] using D
  refine wp_adcS rfl dv fun t T _ => WP.block_nil ?_
  have L : (t.gpr .esi).toNat=((s.gpr .esi).toNat+(s.gpr .esi).toNat)%2^32 := by
    rw [T.other .esi (by decide),V.other .esi (by decide),U.gpr,BitVec.toNat_add]
  have M : (t.gpr .ebx).toNat=((s.gpr .ebx).toNat+(s.gpr .ebx).toNat+c.toNat)%2^32 := by
    rw [T.other .ebx (by decide),V.gpr,add3_toNat,U.other .ebx (by decide)]
  have H : (t.gpr .ecx).toNat=((s.gpr .ecx).toNat+(s.gpr .ecx).toNat+d.toNat)%2^32 := by
    rw [T.gpr,add3_toNat,V.other .ecx (by decide),U.other .ecx (by decide)]
  refine ⟨?_,?_,T.mem.trans (V.mem.trans U.mem)⟩
  · rw [value,L,M,H]
    exact double96 (s.gpr .esi).isLt (s.gpr .ebx).isLt (s.gpr .ecx).isLt bound
  · have ku : Keeps [.esi,.ebx,.ecx] s u := U.keeps.mono (by decide)
    exact (ku.trans (V.keeps.mono (by decide))).trans (T.keeps.mono (by decide))

 theorem clear_ok (s : State) :
    WP isa (.block VG.Impl.Mont.X86.Rt.StaticSquare.clear) s fun t =>
      value t=0 ∧ Keeps [.esi,.ebx,.ecx] s t ∧ t.mem=s.mem := by
  unfold VG.Impl.Mont.X86.Rt.StaticSquare.clear
  refine wp_movS rfl fun u U _ => wp_movS rfl fun v V _ => wp_movS rfl fun t T _ => WP.block_nil ?_
  refine ⟨?_,?_,T.mem.trans (V.mem.trans U.mem)⟩
  · simp only [value,T.gpr,T.other .esi (by decide),T.other .ebx (by decide),V.gpr,
      V.other .esi (by decide),U.gpr]
    rfl
  · have ku : Keeps [.esi,.ebx,.ecx] s u := U.keeps.mono (by decide)
    exact (ku.trans (V.keeps.mono (by decide))).trans (T.keeps.mono (by decide))

end VG.Proof.Mont.X86.StaticSquare

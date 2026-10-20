module

public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.MarkerMath
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base

/-! # Native instructions fold the secret exponent marker without branching -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem markerCalc_ok {s : State} {W : Addr} {L d : Nat} (hw : Ws s W L)
    (ptr : PtrAt s W .ebp d) (fit : d + 8 ≤ L) :
    WP isa (.block markerCalc) s fun t =>
      t.gpr .eax = markerFold (s.mem.readW (off W d) 32) (s.mem.readW (off W (d + 4)) 32) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .edx] s t := by
  unfold markerCalc
  refine wp_movS (readSrc_ptr hw ptr (d := 0) (by omega)) fun s1 u1 _ => ?_
  have bp1 : PtrAt s1 W .ebp d := by rw [PtrAt, u1.other .ebp (by decide)]; exact ptr
  refine wp_orS (readSrc_ptr (hw.of_keeps u1.keeps) bp1 (d := 4) fit) fun s2 u2 => ?_
  refine wp_movS rfl fun s3 u3 _ => ?_
  refine wp_shr (by decide) fun s4 u4 _ => ?_
  refine wp_orS rfl fun s5 u5 => ?_
  refine wp_movS rfl fun s6 u6 _ => ?_
  refine wp_shr (by decide) fun s7 u7 _ => ?_
  refine wp_orS rfl fun s8 u8 => ?_
  refine wp_movS rfl fun s9 u9 _ => ?_
  refine wp_shr (by decide) fun s10 u10 _ => ?_
  refine wp_orS rfl fun s11 u11 => ?_
  refine wp_movS rfl fun s12 u12 _ => ?_
  refine wp_shr (by decide) fun s13 u13 _ => ?_
  refine wp_logicS (.inl rfl) rfl fun s14 u14 => ?_
  refine wp_movS rfl fun s15 u15 _ => ?_
  refine wp_shr (by decide) fun s16 u16 _ => ?_
  refine wp_logicS (.inl rfl) rfl fun s17 u17 => ?_
  refine wp_shr (by decide) fun s18 u18 _ => ?_
  refine wp_logicS (.inl rfl) rfl fun s19 u19 => ?_
  refine wp_addS rfl fun s20 u20 _ => ?_
  refine wp_addS rfl fun s21 u21 _ => ?_
  refine wp_addS rfl fun s22 u22 _ => ?_
  refine wp_addS rfl fun s23 u23 _ => ?_
  refine wp_addS rfl fun s24 u24 _ => ?_
  refine WP.block_nil ⟨?_, ?_, ((((((((((((((((((((((((u1.keeps.mono (by decide)).widen u2.keeps).widen u3.keeps).widen u4.keeps).widen u5.keeps).widen u6.keeps).widen u7.keeps).widen u8.keeps).widen u9.keeps).widen u10.keeps).widen u11.keeps).widen u12.keeps).widen u13.keeps).widen u14.keeps).widen u15.keeps).widen u16.keeps).widen u17.keeps).widen u18.keeps).widen u19.keeps).widen u20.keeps).widen u21.keeps).widen u22.keeps).widen u23.keeps).widen u24.keeps)⟩
  · let x1 := s.mem.readW (off W d) 32 ||| s.mem.readW (off W (d + 4)) 32
    let x2 := x1 ||| x1 >>> 16
    let x3 := x2 ||| x2 >>> 8
    let x4 := x3 ||| x3 >>> 4
    have v2 : s2.gpr .eax = x1 := by rw [u2.gpr, u1.gpr, u1.mem, Nat.add_zero]
    have v5 : s5.gpr .eax = x2 := by
      rw [u5.gpr, u4.other .eax (by decide), u3.other .eax (by decide), v2, u4.gpr, u3.gpr, v2]
    have v8 : s8.gpr .eax = x3 := by
      rw [u8.gpr, u7.other .eax (by decide), u6.other .eax (by decide), v5, u7.gpr, u6.gpr, v5]
    have v11 : s11.gpr .eax = x4 := by
      rw [u11.gpr, u10.other .eax (by decide), u9.other .eax (by decide), v8, u10.gpr, u9.gpr, v8]
    have v14 : s14.gpr .edx = x4 >>> 1 &&& 1 := by
      rw [u14.gpr, u13.gpr, u12.gpr, v11]
      rfl
    have v17 : s17.gpr .ebx = x4 >>> 2 &&& 1 := by
      rw [u17.gpr, u16.gpr, u15.gpr, u14.other .eax (by decide), u13.other .eax (by decide),
        u12.other .eax (by decide), v11]
      rfl
    have v19 : s19.gpr .eax = x4 >>> 3 &&& 1 := by
      rw [u19.gpr, u18.gpr, u17.other .eax (by decide), u16.other .eax (by decide),
        u15.other .eax (by decide), u14.other .eax (by decide), u13.other .eax (by decide),
        u12.other .eax (by decide), v11]
      rfl
    have d19 : s19.gpr .edx = x4 >>> 1 &&& 1 := by
      rw [u19.other .edx (by decide), u18.other .edx (by decide), u17.other .edx (by decide),
        u16.other .edx (by decide), u15.other .edx (by decide), v14]
    have b19 : s19.gpr .ebx = x4 >>> 2 &&& 1 := by
      rw [u19.other .ebx (by decide), u18.other .ebx (by decide), v17]
    rw [u24.gpr, u23.gpr, u22.gpr, u21.gpr, u20.gpr, v19,
      u23.other .ebx (by decide), u22.other .ebx (by decide), u21.other .ebx (by decide),
      u20.other .ebx (by decide), b19,
      u21.other .edx (by decide), u20.other .edx (by decide), d19]
    rfl
  · rw [u24.mem, u23.mem, u22.mem, u21.mem, u20.mem, u19.mem, u18.mem, u17.mem, u16.mem, u15.mem, u14.mem, u13.mem, u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]

end VG.Proof.MillerRabin.X86

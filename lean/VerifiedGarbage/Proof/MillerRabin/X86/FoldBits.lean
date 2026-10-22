module

public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.Math
public import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr

/-! # Fold the prepared one-hot word using the shared threshold arithmetic -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86

theorem fold_bits_ok {s : State} {is : List Instr} {Q : State → Prop} {x : BitVec 32}
    (hx : s.gpr .eax = x)
    (k : ∀ t, Keeps [.eax, .ecx, .edx] s t → t.mem = s.mem →
      t.gpr .eax = VG.Proof.MillerRabin.Math.foldR x 0 → WP isa (.block is) t Q) :
    WP isa (.block (foldBits ++ is)) s Q := by
  simp only [foldBits, List.cons_append, List.nil_append]
  refine wp_movS rfl fun s1 U1 _ => ?_
  refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun s2 U2 => ?_
  refine wp_orS rfl fun s3 U3 => ?_
  refine wp_movS rfl fun s4 U4 _ => ?_
  refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun s5 U5 => ?_
  refine wp_orS rfl fun s6 U6 => ?_
  refine wp_movS rfl fun s7 U7 _ => ?_
  refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun s8 U8 => ?_
  refine wp_orS rfl fun s9 U9 => ?_
  refine wp_movS rfl fun s10 U10 _ => ?_
  refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun s11 U11 => ?_
  refine wp_logicS (.inl rfl) rfl fun s12 U12 => ?_
  refine wp_movS rfl fun s13 U13 _ => ?_
  refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun s14 U14 => ?_
  refine wp_logicS (.inl rfl) rfl fun s15 U15 => ?_
  refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun s16 U16 => ?_
  refine wp_logicS (.inl rfl) rfl fun s17 U17 => ?_
  refine wp_addS rfl fun s18 U18 _ => ?_
  refine wp_addS rfl fun s19 U19 _ => ?_
  refine wp_addS rfl fun s20 U20 _ => ?_
  refine wp_addS rfl fun s21 U21 _ => ?_
  refine wp_addS rfl fun t U22 _ => ?_
  have K1 : Keeps [.eax, .ecx, .edx] s s1 := U1.keeps.mono (by decide)
  have K2 : Keeps [.eax, .ecx, .edx] s s2 := K1.trans (U2.keeps.mono (by decide))
  have K3 : Keeps [.eax, .ecx, .edx] s s3 := K2.trans (U3.keeps.mono (by decide))
  have K4 : Keeps [.eax, .ecx, .edx] s s4 := K3.trans (U4.keeps.mono (by decide))
  have K5 : Keeps [.eax, .ecx, .edx] s s5 := K4.trans (U5.keeps.mono (by decide))
  have K6 : Keeps [.eax, .ecx, .edx] s s6 := K5.trans (U6.keeps.mono (by decide))
  have K7 : Keeps [.eax, .ecx, .edx] s s7 := K6.trans (U7.keeps.mono (by decide))
  have K8 : Keeps [.eax, .ecx, .edx] s s8 := K7.trans (U8.keeps.mono (by decide))
  have K9 : Keeps [.eax, .ecx, .edx] s s9 := K8.trans (U9.keeps.mono (by decide))
  have K10 : Keeps [.eax, .ecx, .edx] s s10 := K9.trans (U10.keeps.mono (by decide))
  have K11 : Keeps [.eax, .ecx, .edx] s s11 := K10.trans (U11.keeps.mono (by decide))
  have K12 : Keeps [.eax, .ecx, .edx] s s12 := K11.trans (U12.keeps.mono (by decide))
  have K13 : Keeps [.eax, .ecx, .edx] s s13 := K12.trans (U13.keeps.mono (by decide))
  have K14 : Keeps [.eax, .ecx, .edx] s s14 := K13.trans (U14.keeps.mono (by decide))
  have K15 : Keeps [.eax, .ecx, .edx] s s15 := K14.trans (U15.keeps.mono (by decide))
  have K16 : Keeps [.eax, .ecx, .edx] s s16 := K15.trans (U16.keeps.mono (by decide))
  have K17 : Keeps [.eax, .ecx, .edx] s s17 := K16.trans (U17.keeps.mono (by decide))
  have K18 : Keeps [.eax, .ecx, .edx] s s18 := K17.trans (U18.keeps.mono (by decide))
  have K19 : Keeps [.eax, .ecx, .edx] s s19 := K18.trans (U19.keeps.mono (by decide))
  have K20 : Keeps [.eax, .ecx, .edx] s s20 := K19.trans (U20.keeps.mono (by decide))
  have K21 : Keeps [.eax, .ecx, .edx] s s21 := K20.trans (U21.keeps.mono (by decide))
  have K22 : Keeps [.eax, .ecx, .edx] s t := K21.trans (U22.keeps.mono (by decide))
  have mem : t.mem = s.mem := by rw [U22.mem, U21.mem, U20.mem, U19.mem, U18.mem, U17.mem, U16.mem, U15.mem, U14.mem, U13.mem, U12.mem, U11.mem, U10.mem, U9.mem, U8.mem, U7.mem, U6.mem, U5.mem, U4.mem, U3.mem, U2.mem, U1.mem]
  refine k t K22 mem ?_
  let x2 := x ||| x >>> 16
  let x3 := x2 ||| x2 >>> 8
  let x4 := x3 ||| x3 >>> 4
  have v3 : s3.gpr .eax = x2 := by
    rw [U3.gpr, U2.other .eax (by decide), U1.other .eax (by decide), U2.gpr, U1.gpr, hx]
  have v6 : s6.gpr .eax = x3 := by
    rw [U6.gpr, U5.other .eax (by decide), U4.other .eax (by decide), U5.gpr, U4.gpr, v3]
  have v9 : s9.gpr .eax = x4 := by
    rw [U9.gpr, U8.other .eax (by decide), U7.other .eax (by decide), U8.gpr, U7.gpr, v6]
  have b1 : s12.gpr .edx = x4 >>> 1 &&& 1 := by
    rw [U12.gpr, U11.gpr, U10.gpr, v9]
    rfl
  have b2 : s15.gpr .ecx = x4 >>> 2 &&& 1 := by
    rw [U15.gpr, U14.gpr, U13.gpr, U12.other .eax (by decide), U11.other .eax (by decide),
      U10.other .eax (by decide), v9]
    rfl
  have b3 : s17.gpr .eax = x4 >>> 3 &&& 1 := by
    rw [U17.gpr, U16.gpr, U15.other .eax (by decide), U14.other .eax (by decide),
      U13.other .eax (by decide), U12.other .eax (by decide), U11.other .eax (by decide),
      U10.other .eax (by decide), v9]
    rfl
  have d17 : s17.gpr .edx = x4 >>> 1 &&& 1 := by
    rw [U17.other .edx (by decide), U16.other .edx (by decide), U15.other .edx (by decide),
      U14.other .edx (by decide), U13.other .edx (by decide), b1]
  have c17 : s17.gpr .ecx = x4 >>> 2 &&& 1 := by
    rw [U17.other .ecx (by decide), U16.other .ecx (by decide), b2]
  rw [U22.gpr, U21.other .eax (by decide), U20.gpr, U19.other .eax (by decide), U18.gpr, b3,
    U19.gpr, U18.other .edx (by decide), d17, U21.gpr, U20.other .ecx (by decide),
    U19.other .ecx (by decide), U18.other .ecx (by decide), c17]
  have twice (a : BitVec 32) : a + a = a <<< 1 := by
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    exact BitVec.mul_two.symm
  rw [twice, twice]
  unfold VG.Proof.MillerRabin.Math.foldR
  rw [show x ||| (0 : BitVec 32) = x from BitVec.or_zero]
  rfl

end VG.Proof.MillerRabin.X86

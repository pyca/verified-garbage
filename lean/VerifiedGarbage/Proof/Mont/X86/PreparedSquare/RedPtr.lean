module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Base

public import VerifiedGarbage.TCB.X86.Isa

public import VerifiedGarbage.Proof.Framework.Semantics

import VerifiedGarbage.Proof.Mont.X86.Rt.Step

public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Args
public import VerifiedGarbage.Proof.Mont.X86.Square.Scalar
import VerifiedGarbage.Proof.Mont.X86.Square.CarryIn

@[expose] public section
namespace VG.Proof.Mont.X86.PreparedSquare
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Mont.X86.Square

def redPtr : List Instr :=
  [.mov .ecx (.reg .edi), .alu .add .ecx (.imm 24), .alu .add .ecx (.reg .edx)] ++
  ptr .ebp argM .eax ++
  [.alu .add .ebp (.reg .esi), .alu .sub .ebp (.reg .edx), .alu .cmp .esi (.reg .ebx)]

theorem redPtr_ok {s : State} {W : Addr} {L S m N k l : Nat} {A : Nat → BitVec 32}
    (ha : Args s W L A) (base : A 0 = BitVec.ofNat 32 W.toNat) (argMeq : A 3 = BitVec.ofNat 32 m)
    (edi : PtrAt s W .edi S) (lk : l≤k) (hl32 : 4*l<2^32) (h8 : 8*N<2^32) (hk : k<2*N)
    (dx : s.gpr .edx = BitVec.ofNat 32 (4*l)) (si : s.gpr .esi = BitVec.ofNat 32 (4*k))
    (bx : s.gpr .ebx = BitVec.ofNat 32 (4*N)) :
    WP isa (.block redPtr) s fun t =>
      PtrAt t W .ecx (S+24+4*l) ∧ PtrAt t W .ebp (m+4*(k-l)) ∧
      t.cf = some (decide (k<N)) ∧ t.mem = s.mem ∧ Keeps [.eax, .ecx, .ebp] s t ∧ t.xmm = s.xmm := by
  have body : WP isa (.block redPtr) s fun t =>
      PtrAt t W .ecx (S+24+4*l) ∧ PtrAt t W .ebp (m+4*(k-l)) ∧
      t.cf = some (decide (k<N)) ∧ t.mem = s.mem ∧ Keeps [.eax, .ecx, .ebp] s t := by
    unfold redPtr
    rw [List.append_assoc]
    apply WP.block_append
    refine wp_movS rfl fun t1 u1 _ => wp_addS rfl fun t2 u2 _ => wp_addS rfl fun t3 u3 _ => WP.block_nil ?_
    have K3 : Keeps [.ecx] s t3 := u1.keeps.trans (u2.keeps.trans u3.keeps)
    have ediEq : s.gpr .edi = BitVec.ofNat 32 (W.toNat+S) := by
      apply BitVec.eq_of_toNat_eq
      rw [edi, BitVec.toNat_ofNat]
    have c3 : t3.gpr .ecx = BitVec.ofNat 32 (W.toNat+S+24+4*l) := by
      rw [u3.gpr, u2.gpr, u1.gpr, ediEq, u2.other _ (by decide), u1.other _ (by decide), dx]
      change (BitVec.ofNat 32 (W.toNat+S)+BitVec.ofNat 32 24)+BitVec.ofNat 32 (4*l) = _
      rw [← BitVec.ofNat_add, ← BitVec.ofNat_add]
    have ha3 := ha.of_keeps K3 (by decide) (by rw [u3.mem, u2.mem, u1.mem]; exact Outs.refl _ _ _)
    apply WP.block_append
    refine WP.mono (ptr_ok ha3 (r := .ebp) (t := .eax) (i := 3) (by decide) (by decide) (by decide))
      fun t4 ⟨bp4, _, m4, K4⟩ => ?_
    have K : Keeps [.eax, .ecx, .ebp] s t4 := (K3.mono (by decide)).trans (K4.mono (by decide))
    have p4 : t4.gpr .ebp = BitVec.ofNat 32 (W.toNat+m) := by
      rw [bp4, base, argMeq, ← BitVec.ofNat_add]
    refine wp_addS rfl fun t5 u5 _ => wp_subS rfl fun t6 u6 _ => wp_cmpCF rfl fun t7 F cf => WP.block_nil ?_
    have p6 : t6.gpr .ebp = BitVec.ofNat 32 (W.toNat+m+4*(k-l)) := by
      rw [u6.gpr, u5.gpr, p4, K.1 _ (by decide), si, u5.other _ (by decide), K.1 _ (by decide), dx,
        ← BitVec.ofNat_add, BitVec.ofNat_sub_ofNat_of_le _ _ hl32 (by omega)]
      congr 1
      omega
    refine ⟨?_, ?_, ?_, ?_, K.trans ((u5.keeps.mono (by decide)).trans
      ((u6.keeps.mono (by decide)).trans (F.keeps _)))⟩
    · rw [PtrAt, F.gpr, u6.other _ (by decide), u5.other _ (by decide), K4.1 _ (by decide), c3,
        BitVec.toNat_ofNat]
      congr 1
      omega
    · rw [PtrAt, F.gpr, p6, BitVec.toNat_ofNat]
      congr 1
      omega
    · rw [cf, u6.other _ (by decide), u5.other _ (by decide), K.1 _ (by decide), si,
        u6.other _ (by decide), u5.other _ (by decide), K.1 _ (by decide), bx,
        BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      simp only [Nat.mul_lt_mul_left (by decide : 0 < 4)]
    · rw [F.mem, u6.mem, u5.mem, m4, u3.mem, u2.mem, u1.mem]
  exact WP.mono (scalar_frame (by simp [redPtr, ptr, argM, scalar]) body)
    fun t ⟨⟨cx, bp, flag, mem, keep⟩, xmm⟩ => ⟨cx, bp, flag, mem, keep, xmm⟩

end VG.Proof.Mont.X86.PreparedSquare

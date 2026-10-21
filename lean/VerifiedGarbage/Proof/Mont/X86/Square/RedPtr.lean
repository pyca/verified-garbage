module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Impl.Mont.X86.MulRt
import VerifiedGarbage.Proof.Mont.X86.Square.CarryIn
public import VerifiedGarbage.Proof.Mont.X86.Rt.Args
public import VerifiedGarbage.Proof.Mont.X86.Square.Scalar
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def redPtr : List Instr := [.mov .ecx (.reg .edi), .alu .add .ecx (.imm 52), .alu .add .ecx (.reg .edx),
  .mov .ebp (.mem argWs), .mov .eax (.mem argM), .alu .add .ebp (.reg .eax),
  .alu .add .ebp (.reg .esi), .alu .sub .ebp (.reg .edx), .alu .cmp .esi (.reg .ebx)]

theorem redPtr_ok {s : State} {W : Addr} {L S m N k l : Nat} {A : Nat → BitVec 32}
    (ha : Args s W L A) (base : A 0 = BitVec.ofNat 32 W.toNat) (argMeq : A 3 = BitVec.ofNat 32 m)
    (edi : PtrAt s W .edi S) (lk : l≤k) (hl32 : 4*l<2^32) (h8 : 8*N<2^32) (hk : k<2*N)
    (dx : s.gpr .edx = BitVec.ofNat 32 (4*l)) (si : s.gpr .esi = BitVec.ofNat 32 (4*k))
    (bx : s.gpr .ebx = BitVec.ofNat 32 (4*N)) :
    WP isa (.block redPtr) s fun t =>
      PtrAt t W .ecx (S+52+4*l) ∧ PtrAt t W .ebp (m+4*(k-l)) ∧
      t.cf = some (decide (k<N)) ∧ t.mem = s.mem ∧ Keeps [.eax, .ecx, .ebp] s t ∧ t.xmm = s.xmm := by
  have body : WP isa (.block redPtr) s fun t =>
      PtrAt t W .ecx (S+52+4*l) ∧ PtrAt t W .ebp (m+4*(k-l)) ∧
      t.cf = some (decide (k<N)) ∧ t.mem = s.mem ∧ Keeps [.eax, .ecx, .ebp] s t := by
    unfold redPtr
    refine wp_movS rfl fun t1 u1 _ => wp_addS rfl fun t2 u2 _ => wp_addS rfl fun t3 u3 _ => ?_
    have ha3 := ((ha.of_upd u1 (by decide)).of_upd u2 (by decide)).of_upd u3 (by decide)
    refine wp_movS (ha3.read 0 (by decide)) fun t4 u4 _ => ?_
    have ha4 := ha3.of_upd u4 (by decide)
    refine wp_movS (ha4.read 3 (by decide)) fun t5 u5 _ => wp_addS rfl fun t6 u6 _ =>
      wp_addS rfl fun t7 u7 _ => wp_subS rfl fun t8 u8 _ => wp_cmpCF rfl fun t9 f9 cf => WP.block_nil ?_
    have ediEq : s.gpr .edi = BitVec.ofNat 32 (W.toNat+S) := by
      apply BitVec.eq_of_toNat_eq; rw [edi, BitVec.toNat_ofNat]
    have c3 : t3.gpr .ecx = BitVec.ofNat 32 (W.toNat+S+52+4*l) := by
      rw [u3.gpr, u2.gpr, u1.gpr, ediEq, u2.other _ (by decide), u1.other _ (by decide), dx]
      change (BitVec.ofNat 32 (W.toNat+S)+BitVec.ofNat 32 52)+BitVec.ofNat 32 (4*l) = _
      rw [← BitVec.ofNat_add, ← BitVec.ofNat_add]
    have p8 : t8.gpr .ebp = BitVec.ofNat 32 (W.toNat+m+4*(k-l)) := by
      rw [u8.gpr, u7.gpr, u6.gpr, u5.other _ (by decide), u4.gpr, u5.gpr, base, argMeq]
      have ss : t6.gpr .esi = s.gpr .esi := by
        rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
          u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide)]
      have dd : t7.gpr .edx = s.gpr .edx := by
        rw [u7.other _ (by decide), u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
          u3.other _ (by decide), u2.other _ (by decide), u1.other _ (by decide)]
      rw [ss, si, dd, dx, ← BitVec.ofNat_add, ← BitVec.ofNat_add,
        BitVec.ofNat_sub_ofNat_of_le _ _ hl32 (by omega)]
      congr 1
      omega
    have c8 : t8.gpr .ecx = BitVec.ofNat 32 (W.toNat+S+52+4*l) := by
      rw [u8.other _ (by decide), u7.other _ (by decide), u6.other _ (by decide),
        u5.other _ (by decide), u4.other _ (by decide), c3]
    have K : Keeps [.eax, .ecx, .ebp] s t8 :=
      (u1.keeps.mono (by decide)).trans ((u2.keeps.mono (by decide)).trans ((u3.keeps.mono (by decide)).trans
        ((u4.keeps.mono (by decide)).trans ((u5.keeps.mono (by decide)).trans
          ((u6.keeps.mono (by decide)).trans ((u7.keeps.mono (by decide)).trans (u8.keeps.mono (by decide))))))))
    refine ⟨?_, ?_, ?_, ?_, K.trans (f9.keeps _)⟩
    · rw [PtrAt, f9.gpr, c8, BitVec.toNat_ofNat]; congr 1; omega
    · rw [PtrAt, f9.gpr, p8, BitVec.toNat_ofNat]; congr 1; omega
    · rw [cf, K.1 _ (by decide), K.1 _ (by decide), si, bx, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      simp only [Nat.mul_lt_mul_left (by decide : 0<4)]
    · rw [f9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  exact WP.mono (scalar_frame (by simp [redPtr, scalar]) body)
    fun t ⟨⟨c, p, cf, mem, keep⟩, xmm⟩ => ⟨c, p, cf, mem, keep, xmm⟩

end VG.Proof.Mont.X86.Square

module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Impl.Mont.X86.MulRt
import VerifiedGarbage.Proof.Mont.X86.Square.Double
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Mont.X86.Rt.Args
public import VerifiedGarbage.Proof.Mont.X86.Square.Scalar

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def diagPtr : List Instr := [.mov .eax (.reg .esi), .shift .shr .eax 1,
  .mov .edx (.mem argWs), .alu .add .eax (.reg .edx), .mov .edx (.mem argA), .alu .add .eax (.reg .edx)]

theorem diagPtr_ok {s : State} {W : Addr} {L a k : Nat} {A : Nat → BitVec 32}
    (ha : Args s W L A) (base : A 0 = BitVec.ofNat 32 W.toNat) (argAeq : A 7 = BitVec.ofNat 32 a)
    (count : s.gpr .esi = BitVec.ofNat 32 (4*k)) (h4 : 4*k < 2^32) (even : k%2=0) :
    WP isa (.block diagPtr) s fun t =>
      PtrAt t W .eax (a+4*(k/2)) ∧ t.mem = s.mem ∧ Keeps [.eax, .edx] s t ∧ t.xmm = s.xmm := by
  have body : WP isa (.block diagPtr) s fun t =>
      PtrAt t W .eax (a+4*(k/2)) ∧ t.mem = s.mem ∧ Keeps [.eax, .edx] s t := by
    unfold diagPtr
    refine wp_movS rfl fun t1 u1 _ => VG.X86.Wp.wp_shr (by decide) fun t2 u2 _ => ?_
    have ha1 := ha.of_upd u1 (by decide)
    have ha2 := ha1.of_upd u2 (by decide)
    refine wp_movS (ha2.read 0 (by decide)) fun t3 u3 _ => wp_addS rfl fun t4 u4 _ => ?_
    have ha3 := ha2.of_upd u3 (by decide)
    have ha4 := ha3.of_upd u4 (by decide)
    refine wp_movS (ha4.read 7 (by decide)) fun t5 u5 _ => wp_addS rfl fun t6 u6 _ => WP.block_nil ?_
    have half : t2.gpr .eax = BitVec.ofNat 32 (4*(k/2)) := by
      rw [u2.gpr, u1.gpr, count]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h4,
        Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      simp only [Nat.reducePow]
      omega
    have result : t6.gpr .eax = BitVec.ofNat 32 (W.toNat+a+4*(k/2)) := by
      rw [u6.gpr, u5.other _ (by decide), u4.gpr, u3.other _ (by decide), half,
        u3.gpr, u5.gpr, base, argAeq, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
      congr 1
      omega
    refine ⟨?_, ?_, ?_⟩
    · rw [PtrAt, result, BitVec.toNat_ofNat]
      congr 1
      omega
    · rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    · exact (u1.keeps.mono (by decide)).trans ((u2.keeps.mono (by decide)).trans
        ((u3.keeps.mono (by decide)).trans ((u4.keeps.mono (by decide)).trans
          ((u5.keeps.mono (by decide)).trans (u6.keeps.mono (by decide))))))
  exact WP.mono (scalar_frame (by simp [diagPtr, scalar]) body)
    fun t ⟨⟨p, mem, keep⟩, xmm⟩ => ⟨p, mem, keep, xmm⟩

end VG.Proof.Mont.X86.Square

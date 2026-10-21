module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Base

public import VerifiedGarbage.Proof.Mont.X86.Words

public import VerifiedGarbage.Proof.Framework.Semantics

import VerifiedGarbage.Proof.Mont.X86.Rt.Step

public import VerifiedGarbage.Proof.Mont.X86.PreparedSquare.Args
public import VerifiedGarbage.Proof.Mont.X86.Square.Scalar
import VerifiedGarbage.Proof.Mont.X86.Square.Double

@[expose] public section
namespace VG.Proof.Mont.X86.PreparedSquare
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt
open VG.Proof.Mont.X86.Square

def diagPtr : List Instr := [.mov .ecx (.mem (at_ .esp 8)),
  .mov .eax (.reg .esi), .shift .shr .eax 1, .alu .add .eax (.reg .ecx)]

theorem diagPtr_ok {s : State} {W : Addr} {L a k : Nat} {A : Nat → BitVec 32}
    (ha : Args s W L A) (base : A 0 = BitVec.ofNat 32 W.toNat) (argAeq : A 7 = BitVec.ofNat 32 a)
    (count : s.gpr .esi = BitVec.ofNat 32 (4*k)) (h4 : 4*k < 2^32) (even : k%2=0) :
    WP isa (.block diagPtr) s fun t =>
      PtrAt t W .eax (a+4*(k/2)) ∧ t.mem = s.mem ∧ Keeps [.eax, .ecx] s t ∧ t.xmm = s.xmm := by
  have body : WP isa (.block diagPtr) s fun t =>
      PtrAt t W .eax (a+4*(k/2)) ∧ t.mem = s.mem ∧ Keeps [.eax, .ecx] s t := by
    unfold diagPtr
    refine wp_movS (ha.read 7 (by decide)) fun t0 u0 _ => wp_movS rfl fun t1 u1 _ =>
      VG.X86.Wp.wp_shr (by decide) fun t2 u2 _ => wp_addS rfl fun t3 u3 _ => WP.block_nil ?_
    have half : t2.gpr .eax = BitVec.ofNat 32 (4*(k/2)) := by
      rw [u2.gpr, u1.gpr, u0.other _ (by decide), count]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h4,
        Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      simp only [Nat.reducePow]
      omega
    have pointer : t2.gpr .ecx = BitVec.ofNat 32 (W.toNat+a) := by
      rw [u2.other _ (by decide), u1.other _ (by decide), u0.gpr]
      change A 0 + A 7 = _
      rw [base, argAeq, ← BitVec.ofNat_add]
    refine ⟨?_, u3.mem.trans (u2.mem.trans (u1.mem.trans u0.mem)), ?_⟩
    · rw [PtrAt, u3.gpr, half, pointer, ← BitVec.ofNat_add, BitVec.toNat_ofNat]
      congr 1
      omega
    · exact (u0.keeps.mono (by decide)).trans ((u1.keeps.mono (by decide)).trans
        ((u2.keeps.mono (by decide)).trans (u3.keeps.mono (by decide))))
  exact WP.mono (scalar_frame (by simp [diagPtr, scalar]) body)
    fun t ⟨⟨p, mem, keep⟩, xmm⟩ => ⟨p, mem, keep, xmm⟩

end VG.Proof.Mont.X86.PreparedSquare

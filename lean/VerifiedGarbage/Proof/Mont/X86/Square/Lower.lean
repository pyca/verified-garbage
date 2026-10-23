module

public import VerifiedGarbage.Proof.Mont.X86.Square.Scalar
import VerifiedGarbage.Proof.Mont.X86.Square.Dot
public import VerifiedGarbage.Proof.Mont.X86.Rt.Args
public import VerifiedGarbage.Impl.Mont.X86.MulRt
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def lower (r : Reg) : Prog isa :=
  .seq (.block (lenTimes r 0 ++ [.mov .edx (.reg .esi), .alu .add .edx (.imm 4), .alu .sub .edx (.reg r)]))
    (.ite .b (.block [.mov .edx (.imm 0)]) (.block []))

theorem lower_ok {s : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} {N k : Nat} {r : Reg}
    (ha : Args s W L A) (hr : r = .eax ∨ r = .ebx)
    (hN : N = 2*(A 2).toNat) (h8 : 8*N < 2^32) (hk : k < 2*N)
    (count : s.gpr .esi = BitVec.ofNat 32 (4*k)) :
    WP isa (lower r) s fun t =>
      t.gpr .edx = BitVec.ofNat 32 (4*(k+1-N)) ∧ t.gpr r = BitVec.ofNat 32 (4*N) ∧
      t.mem = s.mem ∧ Keeps [r, .edx] s t ∧ t.xmm = s.xmm := by
  have rdx : r ≠ .edx := by rcases hr with rfl | rfl <;> decide
  have rsi : r ≠ .esi := by rcases hr with rfl | rfl <;> decide
  have first : WP isa (.block (lenTimes r 0 ++
      [.mov .edx (.reg .esi), .alu .add .edx (.imm 4), .alu .sub .edx (.reg r)])) s fun t =>
      t.gpr .edx = BitVec.ofNat 32 (4*(k+1)) - BitVec.ofNat 32 (4*N) ∧
      t.gpr r = BitVec.ofNat 32 (4*N) ∧ t.cf = some (decide (k+1<N)) ∧
      t.mem = s.mem ∧ Keeps [r, .edx] s t := by
    apply WP.block_append
    refine WP.mono (lenTimes_ok ha (r := r) 0) fun t1 ⟨len1, m1, keep1⟩ => ?_
    have er : t1.gpr r = BitVec.ofNat 32 (4*N) := by
      apply BitVec.eq_of_toNat_eq
      rw [len1, hN, BitVec.toNat_ofNat]
      congr 1
      omega_arith
    have si : t1.gpr .esi = BitVec.ofNat 32 (4*k) := (keep1.1 _ (by simp [Ne.symm rsi])).trans count
    refine wp_movS rfl fun t2 u2 _ => wp_addS rfl fun t3 u3 _ => wp_subS rfl fun t4 u4 cf => WP.block_nil ?_
    have e3 : t3.gpr .edx = BitVec.ofNat 32 (4*(k+1)) := by
      rw [u3.gpr, u2.gpr, si]
      change BitVec.ofNat 32 (4*k) + BitVec.ofNat 32 4 = _
      rw [← BitVec.ofNat_add]
      congr 1
    have er3 : t3.gpr r = BitVec.ofNat 32 (4*N) := by
      rw [u3.other _ rdx, u2.other _ rdx, er]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [u4.gpr, e3, er3]
    · rw [u4.other _ rdx, er3]
    · rw [cf, e3, er3, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
      simp only [Nat.mul_lt_mul_left (by decide : 0 < 4)]
    · rw [u4.mem, u3.mem, u2.mem, m1]
    · exact (keep1.mono (by simp)).trans ((u2.keeps.mono (by simp)).trans
        ((u3.keeps.mono (by simp)).trans (u4.keeps.mono (by simp))))
  unfold lower
  refine WP.seq (WP.mono (scalar_frame (by simp [lenTimes, scalar]) first) fun t ⟨⟨ed, er, cf, mem, keep⟩, xmm⟩ => ?_)
  refine WP.ite (decide (k+1<N)) (by change t.cf = _; exact cf) ?_ ?_
  · intro yes
    refine VG.X86.Wp.cons rfl (WP.block_nil ?_)
    have upd := VG.X86.Wp.Upd.setReg t .edx (0 : BitVec 32)
    have lt : k+1<N := of_decide_eq_true yes
    refine ⟨?_, by rw [upd.other _ rdx, er], by rw [upd.mem, mem], ?_, ?_⟩
    · rw [upd.gpr, Nat.sub_eq_zero_of_le (by omega_arith)]; rfl
    · exact keep.trans (upd.keeps.mono (by simp))
    · exact xmm
  · intro no
    apply WP.block_nil
    have ge : N ≤ k+1 := by have := of_decide_eq_false no; omega_arith
    refine ⟨?_, er, mem, keep, xmm⟩
    rw [ed, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_arith) (by omega_arith)]
    congr 1
    omega_arith

end VG.Proof.Mont.X86.Square

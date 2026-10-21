module

public import VerifiedGarbage.Impl.Mont.X86.MulRt
import VerifiedGarbage.Proof.Mont.X86.Square.CarryOut
public import VerifiedGarbage.Proof.Mont.X86.Rt.Args
public import VerifiedGarbage.Proof.Mont.X86.Square.Scalar
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def endCtl : List Instr := [.alu .add .esi (.imm 4)] ++ lenTimes .eax 1 ++ [.alu .cmp .esi (.reg .eax)]

theorem endCtl_ok {s : State} {W : Addr} {L N k : Nat} {A : Nat → BitVec 32}
    (ha : Args s W L A) (hN : N=2*(A 2).toNat) (h8 : 8*N<2^32) (hk : k<2*N)
    (si : s.gpr .esi = BitVec.ofNat 32 (4*k)) :
    WP isa (.block endCtl) s fun t => t.gpr .esi = BitVec.ofNat 32 (4*(k+1)) ∧
      t.zf = some (decide (k+1=2*N)) ∧ t.mem = s.mem ∧ Keeps [.eax, .esi] s t ∧ t.xmm = s.xmm := by
  have body : WP isa (.block endCtl) s fun t => t.gpr .esi = BitVec.ofNat 32 (4*(k+1)) ∧
      t.zf = some (decide (k+1=2*N)) ∧ t.mem = s.mem ∧ Keeps [.eax, .esi] s t := by
    unfold endCtl
    simp only [List.cons_append, List.nil_append]
    refine wp_addS rfl fun t1 u1 _ => ?_
    have ha1 := ha.of_upd u1 (by decide)
    apply WP.block_append
    refine WP.mono (lenTimes_ok ha1 (r := .eax) 1) fun t2 ⟨len, m2, K2⟩ => ?_
    have eax : t2.gpr .eax = BitVec.ofNat 32 (8*N) := by
      apply BitVec.eq_of_toNat_eq
      rw [len, BitVec.toNat_ofNat, hN]
      congr 1
      omega
    have esi : t2.gpr .esi = BitVec.ofNat 32 (4*(k+1)) := by
      rw [K2.1 _ (by decide), u1.gpr, si]
      change BitVec.ofNat 32 (4*k)+BitVec.ofNat 32 4 = _
      rw [← BitVec.ofNat_add]
      congr 1
    refine wp_cmpS rfl fun t3 f3 zf => WP.block_nil ?_
    refine ⟨by rw [f3.gpr, esi], ?_, f3.mem.trans (m2.trans u1.mem),
      (u1.keeps.mono (by decide)).trans ((K2.mono (by decide)).trans (f3.keeps _))⟩
    rw [zf, esi, eax]
    by_cases e : k+1=2*N
    · have same : 4*(k+1)=8*N := by omega
      rw [same]
      simp [e]
    · have ne : BitVec.ofNat 32 (4*(k+1))-BitVec.ofNat 32 (8*N) ≠ (0 : BitVec 32) := by
        intro zero
        have eq := BitVec.sub_eq_iff_eq_add.mp zero
        have v := congrArg BitVec.toNat eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (0 : BitVec 32).toNat = 0 from rfl,
          Nat.zero_add] at v
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h8, Nat.mod_eq_of_lt h8] at v
        omega
      simp only [e, decide_false, Option.some.injEq, beq_eq_false_iff_ne]
      exact ne
  exact WP.mono (scalar_frame (by simp [endCtl, lenTimes, scalar]) body)
    fun t ⟨⟨si, zf, mem, keep⟩, xmm⟩ => ⟨si, zf, mem, keep, xmm⟩

end VG.Proof.Mont.X86.Square

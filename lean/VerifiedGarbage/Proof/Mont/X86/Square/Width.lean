module

public import VerifiedGarbage.Proof.Mont.X86.Square.Store

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

def widthTest : List Instr := lenTimes .eax 0 ++ [.alu .cmp .esi (.reg .eax)]

theorem widthTest_ok {s : State} {W : Addr} {L N k : Nat} {A : Nat → BitVec 32}
    (ha : Args s W L A) (hN : N=2*(A 2).toNat) (h8 : 8*N<2^32) (hk : k<2*N)
    (si : s.gpr .esi = BitVec.ofNat 32 (4*k)) :
    WP isa (.block widthTest) s fun t => t.cf = some (decide (k<N)) ∧
      t.mem = s.mem ∧ Keeps [.eax] s t ∧ t.xmm = s.xmm := by
  have body : WP isa (.block widthTest) s fun t => t.cf = some (decide (k<N)) ∧
      t.mem = s.mem ∧ Keeps [.eax] s t := by
    unfold widthTest
    apply WP.block_append
    refine WP.mono (lenTimes_ok ha (r := .eax) 0) fun t1 ⟨len, mem, keep⟩ => ?_
    have ea : t1.gpr .eax = BitVec.ofNat 32 (4*N) := by
      apply BitVec.eq_of_toNat_eq
      rw [len, BitVec.toNat_ofNat, hN]
      congr 1
      omega
    refine wp_cmpCF rfl fun t2 f2 cf => WP.block_nil ?_
    refine ⟨?_, f2.mem.trans mem, keep.trans (f2.keeps _)⟩
    rw [cf, keep.1 _ (by decide), si, ea, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    simp only [Nat.mul_lt_mul_left (by decide : 0<4)]
  exact WP.mono (scalar_frame (by simp [widthTest, lenTimes, scalar]) body)
    fun t ⟨⟨cf, mem, keep⟩, xmm⟩ => ⟨cf, mem, keep, xmm⟩

end VG.Proof.Mont.X86.Square

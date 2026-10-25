module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontStep
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Omega

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum.PPC64LE

theorem ofNat_sub_one {n : Nat} (hn : 1 ≤ n) (hn' : n < 2 ^ 64) :
    BitVec.ofNat 64 n - 1#64 = BitVec.ofNat 64 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simp only [BitVec.toNat_ofNat]
  omega_arith

/-- `cnt -= 1`. -/
theorem subi_ok (s : State) (r : Reg) (hr : r ≠ .r0) :
    WP isa (.block [.subi r r 1]) s fun s' => s' = s.write r (s.gpr r - BitVec.ofNat 64 1) := by
  apply WP.of_runBlock
  rw [runBlock_cons, exec_subi (imm := 1) hr (by decide), runStep_some, runBlock_nil]
  exact ⟨_, rfl, rfl⟩

/-- A store of digit `j` of a number of `j + 1` digits. -/
theorem val32_write_top (m : Mem) (B : Addr) (d j : Nat) (v : BitVec 32) (h : d + 4 * j + 4 ≤ 2 ^ 64) :
    val32 (m.writeW (off B (d + 4 * j)) v) B d (j + 1) = val32 m B d j + 2 ^ (32 * j) * v.toNat := by
  rw [val32_succ, (writeW32_outside m B v (by omega_arith)).val32 (by omega_arith) (by omega_arith), w32_write_self]

theorem pow32_mul (j : Nat) : 2 ^ 32 * 2 ^ (32 * j) = 2 ^ (32 * (j + 1)) := by
  rw [← Nat.pow_add]; congr 1; omega_arith

end VG.Proof.Bignum.PPC64LE

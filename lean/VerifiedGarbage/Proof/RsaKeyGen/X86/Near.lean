module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.NearScalar
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Near
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.NearFinish
import VerifiedGarbage.Proof.RsaKeyGen.X86.NearValues
import VerifiedGarbage.Proof.RsaKeyGen.X86.OrScan
import VerifiedGarbage.Proof.RsaKeyGen.NearWords32
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Complete constant-shape comparison with the RSA prime separation threshold -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Near
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.Near

theorem code_ok {s : State} {base : Addr} {size n src : Nat}
    (scratch : Scr s base size) (positive : 4 < n) (fit : src + 4 * n ≤ size) :
    WP isa (code n src) s fun t =>
      t.gpr .eax = bit (decide (val32 s.mem base src n ≤ 2 ^ (32 * n - 100))) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  unfold code
  refine WP.seq (WP.mono (OrScan.code_ok scratch (by omega) (by omega)) fun a ⟨Z, Ma, Ka⟩ => ?_)
  refine WP.block_append (WP.mono (top_ok (scratch.of_keeps Ka (by decide)) (by omega) fit)
    fun b ⟨C, L, H, Mb, Kb⟩ => ?_)
  rw [Ma] at C L H
  have bound : (b.gpr .ecx).toNat < 16 := by rw [C]; exact nibble_bound _
  have nibble : (b.gpr .ecx).toNat = w32 s.mem base (src + 4 * (n - 4)) / 2 ^ 28 := by
    rw [C, nibble_value]
    rfl
  have low : (b.gpr .ebx).toNat = 0 ↔ val32 s.mem base src (n - 4) = 0 ∧
      w32 s.mem base (src + 4 * (n - 4)) % 2 ^ 28 = 0 := by
    rw [L, low_zero, Z]
    rfl
  have high : (b.gpr .edx).toNat = 0 ↔ val32 s.mem base (src + 4 * (n - 4) + 4) 3 = 0 := by
    rw [← word_zero, H]
    simpa only [Nat.add_assoc, Nat.reduceAdd] using high_zero s.mem base (src + 4 * (n - 4) + 4)
  refine WP.mono (finish_ok b bound) fun t ⟨value, Mt, Kt⟩ => ?_
  refine ⟨?_, Mt.trans (Mb.trans Ma), ((Ka.mono (by decide)).widen Kb).widen Kt⟩
  rw [value, nibble]
  have lowFlag : decide ((b.gpr .ebx).toNat ≠ 0) =
      decide (val32 s.mem base src (n - 4) ≠ 0 ∨ w32 s.mem base (src + 4 * (n - 4)) % 2 ^ 28 ≠ 0) :=
    decide_eq_decide.mpr (by omega)
  rw [lowFlag, decide_eq_decide.mpr high, Bool.and_comm, ← Bool.decide_and]
  apply congrArg bit
  exact decide_eq_decide.mpr (VG.Proof.RsaKeyGen.near_words32 s.mem base src n (by omega)).symm

end VG.Proof.RsaKeyGen.X86.Near

module

public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.KeyWords
import VerifiedGarbage.Proof.Framework.PPC64LE.Reduce
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: initialization connects the copied bytes to the word-loop invariant.
/-! # POWER8 AES key-schedule initialization -/

@[expose] public section
namespace VG.Proof.Aes.PPC64LE.Crypto
open VG VG.PPC64LE
open VG.Proof.Aes.KeyWords (W Good W_lt)

theorem copied_good {base s : State} {P S : Addr} {nk : Nat}
    (h : CopyInv base P S (4*nk) ((4*nk)/8) s) (hdiv : 8*((4*nk)/8) = 4*nk) :
    Good s.mem S (W base.mem P nk) nk := by
  intro i hi
  rw [W_lt hi]
  apply VG.Proof.Aes.KeyWords.ext32
  intro j hj
  rw [← Mem.readW_byte s.mem (S + BitVec.ofNat 64 (4*i)) hj,
    ← Mem.readW_byte base.mem (P + BitVec.ofNat 64 (4*i)) hj, Offset.add_add, Offset.add_add]
  exact h.copied _ (by omega)

theorem wordSetup_ok {base s : State} {P S : Addr} {nk : Nat} (hc : KeyConfig base P S (4*nk))
    (h : CopyInv base P S (4*nk) ((4*nk)/8) s) (h7 : s.gpr .r7 = BitVec.ofNat 64 (4*nk)) :
    WP isa (.block Impl.Aes.PPC64LE.Crypto.wordSetup) s (WordInv base P S nk nk) := by
  have h3 : nk = 4 ∨ nk = 6 ∨ nk = 8 := by have := hc.length; omega
  have hn : 0 < nk ∧ nk ≤ 8 := by omega
  have hdiv : 8*((4*nk)/8) = 4*nk := by rcases h3 with rfl | rfl | rfl <;> decide
  have hgood := copied_good h hdiv
  have h5 : s.gpr .r5 = S + BitVec.ofNat 64 (4*nk) := by simpa only [hdiv] using h.out
  have hshift : BitVec.ofNat 64 (4*nk) >>> 2 = BitVec.ofNat 64 nk := by
    rcases h3 with rfl | rfl | rfl <;> decide
  have hrc0 : (nk-1)/nk = 0 := Nat.div_eq_of_lt (by omega)
  apply WP.of_runBlock
  simp only [Impl.Aes.PPC64LE.Crypto.wordSetup, runBlock_cons, runStep_some, runBlock_nil, reduceExec,
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, ne_eq, not_false_eq_true,
    State.read, Size.ext, Size.bits, BitVec.setWidth_eq,
    show 4 ≤ 2^15 by decide, show 0 < 2^15 by decide, show 2 < 64 by decide,
    show 28 < 2^15 by decide, show 1 < 2^15 by decide, and_self,
    h7, h5, hshift, Option.some.injEq, exists_eq_left']
  refine ⟨⟨by omega, by omega⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine (h.keep.trans (rs' := [.r4, .r6, .r8, .r10, .r11, .r12]) ⟨fun r hr => ?_, ?_, ?_⟩).mono (by simp [keyGprs])
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]
    · simp only [RegUpd.rd_write]
    · simp only [RegUpd.wr_write]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false,
      BitVec.add_sub_cancel, Nat.sub_self, Nat.mul_zero, BitVec.add_zero]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
    change S + BitVec.ofNat 64 (4*nk) - BitVec.ofNat 64 4 = _
    rw [Offset.add_ofNat_sub _ (by omega)]
    exact congrArg (fun j => S + BitVec.ofNat 64 j) (by omega)
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, Nat.mod_self, Nat.mul_zero]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, h7]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]
    rw [← BitVec.ofNat_add, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    exact congrArg (BitVec.ofNat 64) (by omega)
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false,
      hrc0, Nat.zero_add, Impl.Aes.KeyWords.rc, Nat.sub_self, Nat.repeat]
    rfl
  · simpa only [RegUpd.mem_write] using hgood
  · simpa only [RegUpd.mem_write] using h.frame

end VG.Proof.Aes.PPC64LE.Crypto

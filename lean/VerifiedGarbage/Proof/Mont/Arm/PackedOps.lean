module

public import VerifiedGarbage.Impl.Mont.ArmPacked
import VerifiedGarbage.Proof.Mont.Arm.PackedLoop
import VerifiedGarbage.Proof.Mont.Arm.PackedExpand
public import VerifiedGarbage.Proof.Mont.Arm.Ops
import VerifiedGarbage.Proof.Mont.Arm.Csub
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Packed Montgomery multiplication under the existing curve operation contract. -/

set_option exponentiation.threshold 1024

@[expose] public section
namespace VG.Proof.Mont.Arm.Packed
open VG VG.Arm VG.Proof.Mont VG.Proof.Mont.Arm VG.Impl.Mont VG.Impl.Mont.Arm.Packed
open VG.Proof.X25519.Arm (Rest wp_mov op2_imm)

 theorem pval_extended {mem : Mem} {base : Addr} {acc n : Nat}
    (bound : val32 mem base acc (n + 2) < 2 ^ (32 * n) * 2) :
    pval mem base acc (2 * n + 1) = val32 mem base acc (n + 2) := by
  have whole := val32_append mem base acc n 2
  have top : val32 mem base (acc + 4 * n) 2 < 2 := by
    rw [whole] at bound
    exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt (Nat.le_add_left _ _) bound)
  simp only [val32, Nat.mul_zero, Nat.add_zero] at top
  have hzero : w32 mem base (acc + 4 * n + 4) = 0 := by omega
  have hlo : w32 mem base (acc + 4 * n) < 65536 := by omega
  rw [pval, pval_words, whole]
  simp only [pdig, hdig, show (2 * n) / 2 = n by omega, show (2 * n) % 2 = 0 by omega,
    Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.mod_eq_of_lt hlo,
    show 16 * (2 * n) = 32 * n by omega, val32, hzero, Nat.add_zero]
  rw [Nat.mul_comm]

 theorem val32_zeros {mem : Mem} {base : Addr} {acc : Nat} :
    ∀ k, (∀ j < k, w32 mem base (acc + 4 * j) = 0) → val32 mem base acc k = 0
  | 0, _ => rfl
  | k + 1, h => by
    rw [val32_succ, val32_zeros k (fun j hj => h j (by omega)), h k (by omega), Nat.mul_zero, Nat.add_zero]

/-- Packed rows and the expanded half-word reducer fit inside the original
`32 * n + 8` byte accumulator. The word count must be a baseline immediate. -/
theorem mulR_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {M : Mod} {m n : Nat}
    (hM : ModOkW M size m s.mem base) (hMn : M.n = n) (hn : 0 < n) (hn128 : n < 128)
    {acc o a b : Nat} (hL : OpLay M size acc o a b)
    (pa : s.gpr .r1 = s.gpr .r12 + BitVec.ofNat 32 a)
    (pb : s.gpr .r4 = s.gpr .r12 + BitVec.ofNat 32 b)
    (po : s.gpr .lr = s.gpr .r12 + BitVec.ofNat 32 o)
    (hB : wordsVal s.mem base b M.n < m) :
    WP isa (Impl.Mont.Arm.Packed.mulR M acc) s fun t => OpKeep M base acc o s t ∧
      wordsVal t.mem base o M.n < m ∧
      wordsVal t.mem base o M.n * 2 ^ (64 * M.n) % m =
        wordsVal s.mem base a M.n * wordsVal s.mem base b M.n % m := by
  have nowrap := hs.nowrap
  have hacc : accLen M = 32 * n + 8 := by
    simp only [accLen, Impl.Mont.Arm.digits, hMn]; omega
  have facc := hL.acc_le; have fo := hL.o_le; have fa := hL.a_le; have fb := hL.b_le
  have sa := hL.acc_a; have sb := hL.acc_b; have sm := hL.acc_mo; have st := hL.acc_tmp; have so := hL.acc_o
  have fm := hM.mo; have ftmp := hM.tmp; have smt := hM.sep
  rw [hacc] at facc sa sb sm st so
  rw [hMn] at fo fa fb sa sb so fm ftmp smt
  have modval : val32 s.mem base M.mo (2 * n) = m := by
    have hv := hM.val
    rw [hMn, wordsVal_eq_val32] at hv
    exact hv
  have bval : val32 s.mem base b (2 * n) < m := by simpa only [wordsVal_eq_val32, hMn] using hB
  have mpos : 0 < m := by omega
  unfold Impl.Mont.Arm.Packed.mulR
  simp only [hMn]
  refine WP.seq (zeros_ok hs (k := 2 * n + 2) (by omega) fun s1 out1 zero1 keep1 => ?_)
  refine wp_mov (op2_imm (by
    simpa only [Impl.Mont.Arm.words, hMn] using words_encodable (M := M) (by omega)))
    fun s2 u2 => WP.block_nil ?_
  have keep2 : Rest [.r7, .r9] s s2 := (keep1.mono (by simp)).trans (u2.rest (by simp))
  have mem2 : s2.mem = s1.mem := u2.mem
  have out2 : Outside base acc (8 * n + 8) s.mem s2.mem := by
    rw [mem2]; simpa [Nat.mul_add, ← Nat.mul_assoc] using out1
  have ctx2 := hs.of_rest keep2 (by decide)
  have pa2 : s2.gpr .r1 = s2.gpr .r12 + BitVec.ofNat 32 a := by
    rw [keep2.gpr .r1 (by decide), keep2.gpr .r12 (by decide)]; exact pa
  have pb2 : s2.gpr .r4 = s2.gpr .r12 + BitVec.ofNat 32 b := by
    rw [keep2.gpr .r4 (by decide), keep2.gpr .r12 (by decide)]; exact pb
  have mod2 : val32 s2.mem base M.mo (2 * n) = m := by rw [out2.val32 (by omega) (by omega)]; exact modval
  have b2 : val32 s2.mem base b (2 * n) < m := by rw [out2.val32 (by omega) (by omega)]; exact bval
  have z2 : val32 s2.mem base acc (2 * n + 2) = 0 := by
    rw [mem2]
    exact val32_zeros (2 * n + 2) zero1
  refine WP.seq (WP.mono (loop_ok ctx2 (M := M) (n := 2 * n) (by rw [hMn]) (by omega) (by omega)
    pa2 pb2 u2.gpr (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) mod2 hM.inv b2 z2)
    fun s3 ⟨bound, value, out3, keep3⟩ => ?_)
  have keep : Rest roundClob s s3 := (keep2.mono (by simp)).trans keep3
  have out : Outside base acc (8 * n + 8) s.mem s3.mem :=
    out2.trans (by simpa [Nat.mul_add, ← Nat.mul_assoc] using out3)
  have oldA := out2.val32 (d := a) (k := 2 * n) (by omega) (by omega)
  have oldB := out2.val32 (d := b) (k := 2 * n) (by omega) (by omega)
  rw [oldA, oldB] at value
  have h3 := hs.of_rest keep (by decide)
  have mod3 : val32 s3.mem base M.mo (2 * n) = m := by rw [out.val32 (by omega) (by omega)]; exact modval
  have modBound : m < 2 ^ (32 * (2 * n)) := by rw [← modval]; exact val32_lt _ _ _ _
  have lowDigits : pval s3.mem base acc (4 * n + 1) = val32 s3.mem base acc (2 * n + 2) := by
    simpa [← Nat.mul_assoc] using
      pval_extended (mem := s3.mem) (base := base) (acc := acc) (n := 2 * n) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (expand_ok h3 (n := 4 * n + 1) (dst := acc + (8 * n + 8)) (by omega) (by omega))
    fun s4 ⟨out4, digs, digitsVal, keep4⟩ => ?_
  rw [lowDigits] at digitsVal
  have keep14 : Rest clob s s4 := keep.mono (by simp [clob]) |>.trans (keep4.mono (by simp [clob]))
  have h4 := hs.of_rest keep14 (by decide)
  have pout : s4.gpr .lr = s4.gpr .r12 + BitVec.ofNat 32 o := by
    rw [keep14.gpr .lr (by decide), keep14.gpr .r12 (by decide)]; exact po
  have mod4 : val32 s4.mem base M.mo (2 * n) = m := by rw [out4.val32 (by omega) (by omega)]; exact mod3
  refine WP.mono (csub_ok h4 (K := o) (d := 0) pout (Nat.add_zero _) (by decide)
    (by simp only [Impl.Mont.Arm.words, hMn]) (by simp only [Impl.Mont.Arm.digits, hMn]; omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simpa [hMn, ← Nat.mul_assoc] using hL.o_tmp) mod4 mpos
    (by simpa [Nat.add_assoc, ← Nat.mul_assoc] using digs)
    (by simpa [Nat.add_assoc, ← Nat.mul_assoc] using digitsVal.symm ▸ bound)) fun t ⟨out5, reduced, keep5⟩ => ?_
  simp only [Nat.add_assoc, ← Nat.mul_assoc] at reduced
  rw [digitsVal] at reduced
  have kval : wordsVal t.mem base o n = val32 s3.mem base acc (2 * n + 2) % m := by
    rw [wordsVal_eq_val32]
    exact reduced
  refine ⟨⟨keep14.trans (keep5.mono (by simp [clob])), ?_⟩, ?_, ?_⟩
  · have all : Outside base acc (32 * n + 8) s.mem s4.mem :=
      (out.mono (Nat.le_refl _) (by omega)).trans (out4.mono (by omega) (by omega))
    exact (Outs.of_outside all (by simp [hacc])).trans (out5.mono (by simp [hMn, hacc, ← Nat.mul_assoc]))
  · rw [kval]; exact Nat.mod_lt _ mpos
  · rw [kval, wordsVal_eq_val32, wordsVal_eq_val32]
    rw [Nat.mul_comm, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
    simpa [← Nat.mul_assoc] using value

end VG.Proof.Mont.Arm.Packed

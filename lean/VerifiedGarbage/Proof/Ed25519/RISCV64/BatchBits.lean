module

import VerifiedGarbage.Proof.Ed25519.RISCV64.PointTable
public import VerifiedGarbage.Impl.Ed25519.RISCV64.PointMul
import VerifiedGarbage.Proof.X25519.RISCV64.Bits
import VerifiedGarbage.Proof.X25519.RISCV64.Invert
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ed25519.RISCV64.PointOps
public import VerifiedGarbage.Proof.Framework.Block

/-!
# Ed25519 on RISCV64: a batch's 16 bits, one to a byte

`batchBits` with `r26 = c` and the scalar at `s5`: the scalar's bytes `2c`
and `2c + 1` as a 16-bit digit (`batchDigit_ok`), and bit `k` of it at byte
`BITSB + k` of the working space (`expandBits_ok`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Proof.X25519 (val32_congr)

section
variable {b : Addr}

/-- After `k` bits of the digit `x` from `s1`. -/
structure KInv (b : Addr) (x : Nat) (s1 : State) (k : Nat) (s : State) : Prop where
  rest : Rest [.a5] s1 s
  frame : Frame [⟨b + BitVec.ofNat 64 BITSB, k⟩] s1.mem s.mem
  bits : ∀ j < k, s.mem (b + BitVec.ofNat 64 (BITSB + j)) = BitVec.ofNat 8 ((x >>> j) &&& 1)

theorem expandBits_ok {s1 : State} (hc : Ctx8 b s1) {x : Nat} (h7 : (s1.gpr .a4).toNat = x) :
    WP isa (.block expandBits) s1 (KInv b x s1 16) := by
  have hB : BITSB = 32 := rfl
  refine wp_range_flatMap (M := isa) (KInv b x s1) (fun k s hk h => ?_) 16 (Nat.le_refl _) s1
    ⟨Rest.refl _ _, Frame.refl _ _, fun j hj => by omega⟩
  have e7 : (s.gpr .a4).toNat = x := by rw [h.rest.gpr _ (by decide), h7]
  have hcs : Ctx8 b s := hc.of_rest h.rest (by decide)
  unfold expandBit
  refine wp_sll (by omega) fun s2 u2 => wp_srl (by decide) fun s3 u3 => ?_
  have e8 : (s3.gpr .a5).toNat = (x >>> k) &&& 1 := by
    rw [u3.gpr, u2.gpr, bit_shift _ (by omega), e7]
  refine wp_sb (a := b + BitVec.ofNat 64 (BITSB + k)) (by omega)
    (by rw [u3.other _ (by decide), u2.other _ (by decide), hcs.a3])
    (by rw [u3.wr, u2.wr]; exact hcs.inW (by omega)) fun s4 u4 => WP.block_nil ⟨?_, ?_, fun j hj => ?_⟩
  · exact h.rest.trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans (u4.rest _)))
  · rw [u4.mem, u3.mem, u2.mem]
    exact (h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).writeW
      (List.mem_singleton_self _) _ (by rw [hB]; exact Offset.contains _ (by omega) (by omega) (by omega))
  · rw [u4.mem, VG.WriteBytes.writeW8_apply, u3.mem, u2.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [iteF (Offset.add_ofNat_ne _ (by omega) (by omega) (by omega))]; exact h.bits j hj
    · rw [iteT rfl]; exact stb_byte e8

/-- The digit of batch `c`: bytes `2c` and `2c + 1` of the scalar at `s5`. -/
def digitAt (m : Mem) (p : Addr) (c : Nat) : Nat :=
  (m (p + BitVec.ofNat 64 (2 * c))).toNat + 256 * (m (p + BitVec.ofNat 64 (2 * c + 1))).toNat

theorem batchBits_ok {s : State} (hc : Ctx8 b s) {c : Nat} (hcl : c < 32) (h26 : s.gpr .s6 = BitVec.ofNat 64 c)
    {p : Addr} (h19 : s.gpr .s5 = p) (hin : ∀ i < 2, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (2 * c + i)) 1) :
    WP isa (.block batchBits) s fun t =>
      Rest [.a4, .a5, .s0] s t ∧ Frame [⟨b + BitVec.ofNat 64 BITSB, 16⟩] s.mem t.mem ∧
      ∀ k < 16, t.mem (b + BitVec.ofNat 64 (BITSB + k)) = BitVec.ofNat 8 ((digitAt s.mem p c >>> k) &&& 1) := by
  unfold batchBits batchDigit
  simp only [List.cons_append, List.nil_append]
  refine wp_sll (by decide) fun s1 u1 => wp_add fun s2 u2 => ?_
  have e14 : s2.gpr .s0 = p + BitVec.ofNat 64 (2 * c) := by
    rw [u2.gpr, u1.other .s5 (by decide), h19, u1.gpr, h26]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [toNat_shl, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega
  refine wp_lbz (a := p + BitVec.ofNat 64 (2 * c)) (by decide) (by rw [e14, BitVec.add_zero])
    (by rw [u2.rd, u2.wr, u1.rd, u1.wr]; exact Nat.add_zero (2 * c) ▸ hin 0 (by decide)) fun s3 u3 => ?_
  refine wp_lbz (a := p + BitVec.ofNat 64 (2 * c + 1)) (by decide)
    (by rw [u3.other _ (by decide), e14, Offset.add_add])
    (by rw [u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact hin 1 (by decide)) fun s4 u4 => ?_
  refine wp_sll (by decide) fun s5 u5 => wp_add fun s6 u6 => ?_
  have hm6 : s6.mem = s.mem := by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have hlo := (s.mem (p + BitVec.ofNat 64 (2 * c))).isLt
  have hhi := (s.mem (p + BitVec.ofNat 64 (2 * c + 1))).isLt
  have e7 : (s6.gpr .a4).toNat = digitAt s.mem p c := by
    have m3 : s3.mem = s.mem := by rw [u3.mem, u2.mem, u1.mem]
    rw [u6.gpr, u5.other _ (by decide), u4.other _ (by decide), u3.gpr, u5.gpr, u4.gpr, u2.mem, u1.mem, m3]
    rw [toNat_add_lt, BitVec.toNat_ofNat, toNat_shl, BitVec.toNat_ofNat]
    · simp only [digitAt]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [BitVec.toNat_ofNat, toNat_shl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
      omega
  have hr6 : Rest [.a4, .a5, .s0] s s6 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))))
  refine WP.mono (expandBits_ok (hc.of_rest hr6 (by decide)) e7) fun t ht =>
    ⟨hr6.trans (ht.rest.mono (by decide)), by rw [← hm6]; exact ht.frame, ht.bits⟩

end

end VG.Proof.Ed25519.RISCV64

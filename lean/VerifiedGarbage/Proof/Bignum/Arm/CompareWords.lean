module

public import VerifiedGarbage.Impl.Bignum.Arm.CompareWords
public import VerifiedGarbage.Proof.X25519.Arm.Instr

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PlainSimp
/-! A bounded wordwise comparison visits every word and returns exact equality. -/

-- Formerly `VerifiedGarbage/Proof/Bignum/Arm/CompareWordStep.lean`, which only this module imported.
section

/-! One wordwise XOR/OR comparison step preserves memory. -/

section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp wp_subs op2_imm op2_reg dpVal)

theorem compareWordStep_ok (s : State) (a b : Addr)
    (pa : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = a)
    (pb : State.addr (s.gpr .r1 + BitVec.ofNat 32 0) = b)
    (ra : InRegions (s.rd ++ s.wr) a 4) (rb : InRegions (s.rd ++ s.wr) b 4) :
    WP isa (.block compareWordStep) s fun t => t.mem = s.mem ∧
      t.gpr .r0 = s.gpr .r0 + 4 ∧ t.gpr .r1 = s.gpr .r1 + 4 ∧
      t.gpr .r2 = s.gpr .r2 ||| (s.mem.readW a 32 ^^^ s.mem.readW b 32) ∧
      t.gpr .lr = s.gpr .lr - 1 ∧ t.z = (s.gpr .lr - 1 == 0) ∧
      Rest [.r0, .r1, .r2, .r3, .r12, .lr] s t := by
  unfold compareWordStep
  refine wp_ldr (by decide) pa ra fun s1 u1 => ?_
  refine wp_ldr (a := b) (by decide) (by rw [u1.other .r1 (by decide)]; exact pb)
    (by rw [u1.rd, u1.wr]; exact rb) fun s2 u2 => ?_
  refine wp_dp (op2_reg _ _) fun s3 u3 => ?_
  refine wp_dp (op2_reg _ _) fun s4 u4 => ?_
  refine wp_dp (op2_imm (by decide)) fun s5 u5 => ?_
  refine wp_dp (op2_imm (by decide)) fun s6 u6 => ?_
  refine wp_subs (op2_imm (by decide)) fun t u7 z7 => WP.block_nil ?_
  refine ⟨u7.mem.trans (u6.mem.trans (u5.mem.trans (u4.mem.trans (u3.mem.trans (u2.mem.trans u1.mem))))),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u7.other .r0 (by decide), u6.other .r0 (by decide), u5.gpr, dpVal,
      u4.other .r0 (by decide), u3.other .r0 (by decide), u2.other .r0 (by decide), u1.other .r0 (by decide)]
  · rw [u7.other .r1 (by decide), u6.gpr, dpVal, u5.other .r1 (by decide),
      u4.other .r1 (by decide), u3.other .r1 (by decide), u2.other .r1 (by decide), u1.other .r1 (by decide)]
  · rw [u7.other .r2 (by decide), u6.other .r2 (by decide), u5.other .r2 (by decide), u4.gpr, dpVal,
      u3.other .r2 (by decide), u2.other .r2 (by decide), u1.other .r2 (by decide),
      u3.gpr, dpVal, u2.other .r3 (by decide), u1.gpr, u2.gpr, u1.mem]
  · rw [u7.gpr, u6.other .lr (by decide), u5.other .lr (by decide), u4.other .lr (by decide),
      u3.other .lr (by decide), u2.other .lr (by decide), u1.other .lr (by decide)]
  · rw [z7, u6.other .lr (by decide), u5.other .lr (by decide), u4.other .lr (by decide),
      u3.other .lr (by decide), u2.other .lr (by decide), u1.other .lr (by decide)]
  · exact (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans (u7.rest (by decide)))))))
end VG.Proof.Bignum.Arm
end

end

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)

structure WordCompareCtx (s : State) (a b : BitVec 32) (n : Nat) : Prop where
  countFits : n < 2 ^ 32
  readA : ∀ i < n, InRegions (s.rd ++ s.wr) (State.addr (a + BitVec.ofNat 32 (4 * i))) 4
  readB : ∀ i < n, InRegions (s.rd ++ s.wr) (State.addr (b + BitVec.ofNat 32 (4 * i))) 4

structure WordCompareInv (s0 : State) (a b : BitVec 32) (n i : Nat) (s : State) : Prop where
  index : i ≤ n
  first : s.gpr .r0 = a + BitVec.ofNat 32 (4 * i)
  second : s.gpr .r1 = b + BitVec.ofNat 32 (4 * i)
  count : s.gpr .lr = BitVec.ofNat 32 (n - i)
  equal : s.gpr .r2 = 0 ↔ ∀ j < i,
    s0.mem.readW (State.addr (a + BitVec.ofNat 32 (4 * j))) 32 = s0.mem.readW (State.addr (b + BitVec.ofNat 32 (4 * j))) 32
  mem : s.mem = s0.mem
  rest : Rest [.r0, .r1, .r2, .r3, .r12, .lr] s0 s

private theorem word_xor_zero32 (a b : BitVec 32) : a ^^^ b = 0 ↔ a = b :=
  BitVec.xor_eq_zero_iff

theorem compareWordBody_ok {s0 s : State} {a b : BitVec 32} {n i : Nat}
    (ctx : WordCompareCtx s0 a b n) (inv : WordCompareInv s0 a b n i s) (hi : i < n) :
    WP isa (.block compareWordStep) s fun t => WordCompareInv s0 a b n (i + 1) t ∧ t.z = decide (i + 1 = n) := by
  have ra := ctx.readA i hi
  have rb := ctx.readB i hi
  rw [← inv.rest.rd, ← inv.rest.wr] at ra rb
  refine WP.mono (compareWordStep_ok s _ _ (by rw [inv.first]; simp) (by rw [inv.second]; simp) ra rb) ?_
  rintro t ⟨mem, first, second, acc, count, zero, rest⟩
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, mem.trans inv.mem, inv.rest.trans rest⟩, ?_⟩
  · rw [first, inv.first, BitVec.add_assoc]
    change a + (BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 4) = _
    rw [← BitVec.ofNat_add]
    rw [show 4 * i + 4 = 4 * (i + 1) by omega]
  · rw [second, inv.second, BitVec.add_assoc]
    change b + (BitVec.ofNat 32 (4 * i) + BitVec.ofNat 32 4) = _
    rw [← BitVec.ofNat_add]
    rw [show 4 * i + 4 = 4 * (i + 1) by omega]
  · rw [count, inv.count]
    change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    congr 1
  · rw [acc, show (0 : BitVec 32) = 0#32 from rfl, BitVec.or_eq_zero_iff, ← show (0 : BitVec 32) = 0#32 from rfl,
      word_xor_zero32, inv.equal, inv.mem]
    constructor
    · rintro ⟨before, atI⟩ j hj
      by_cases eq : j = i
      · subst j; exact atI
      · exact before j (by omega)
    · intro all
      exact ⟨fun j hj => all j (by omega), all i (by omega)⟩
  · rw [zero, inv.count]
    change (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), ofNat_beq_zero (by have := ctx.countFits; omega)]
    simp only [show n - i - 1 = 0 ↔ i + 1 = n by omega]

theorem compareWords_ok (s : State) {a b : BitVec 32} {n : Nat}
    (ctx : WordCompareCtx s a b n) (hn : 0 < n)
    (ha : s.gpr .r0 = a) (hb : s.gpr .r1 = b) (hc : s.gpr .lr = BitVec.ofNat 32 n) (hz : s.gpr .r2 = 0) :
    WP isa compareWords s (WordCompareInv s a b n n) := by
  let inv := fun k t => ∃ i, i + k = n ∧ 0 < k ∧ WordCompareInv s a b n i t
  unfold compareWords
  refine WP.loop (M := isa) inv ?_ n s ?_
  · intro k t h
    obtain ⟨i, hik, hk, hi⟩ := h
    refine WP.mono (compareWordBody_ok ctx hi (by omega)) ?_
    rintro u ⟨hu, zero⟩
    by_cases he : i + 1 = n
    · left
      refine ⟨?_, he ▸ hu⟩
      change some (!u.z) = some false
      simp only [zero, he, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega, i + 1, by omega, by omega, hu⟩
      change some (!u.z) = some true
      simp only [zero, he, decide_false, Bool.not_false]
  · refine ⟨0, by omega, hn, ?_⟩
    exact ⟨by omega, by simpa using ha, by simpa using hb, by simpa using hc,
      by simp [hz], rfl, Rest.refl _ _⟩

end VG.Proof.Bignum.Arm

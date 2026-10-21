module

public import VerifiedGarbage.Impl.Bignum.Arm.CompareWords
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Bignum.Arm.CompareWordStep
import VerifiedGarbage.Proof.Framework.Omega

/-! A bounded wordwise comparison visits every word and returns exact equality. -/

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

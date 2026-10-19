module

public import VerifiedGarbage.Proof.Rsa.ZeroTest32
public import VerifiedGarbage.Proof.Rsa.X86.PrivCompareStep
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes

/-! # A full byte comparison terminates without disclosing the first mismatch -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.X86.Wp (ofNat_beq_zero)

structure CompareCtx (s : State) (a b : BitVec 32) (n : Nat) : Prop where
  countFits : n < 2 ^ 32
  readA : ∀ i < n, InRegions (s.rd ++ s.wr) (byteAddr (a + BitVec.ofNat 32 i)) 1
  readB : ∀ i < n, InRegions (s.rd ++ s.wr) (byteAddr (b + BitVec.ofNat 32 i)) 1

structure CompareInv (s0 : State) (a b : BitVec 32) (n i : Nat) (s : State) : Prop where
  index : i ≤ n
  first : s.gpr .esi = a + BitVec.ofNat 32 i
  second : s.gpr .edi = b + BitVec.ofNat 32 i
  count : s.gpr .ecx = BitVec.ofNat 32 (n - i)
  equal : s.gpr .ebp = 0 ↔ ∀ j < i,
    s0.mem (byteAddr (a + BitVec.ofNat 32 j)) = s0.mem (byteAddr (b + BitVec.ofNat 32 j))
  mem : s.mem = s0.mem
  rest : Keeps [.esi, .edi, .ebp, .eax, .edx, .ecx] s0 s

theorem byte_xor_zero32 (a b : Byte) : a.setWidth 32 ^^^ b.setWidth 32 = 0 ↔ a = b :=
  VG.Proof.Rsa.byte_xor_zero32 a b

theorem compareBody_ok {s0 s : State} {a b : BitVec 32} {n i : Nat}
    (ctx : CompareCtx s0 a b n) (inv : CompareInv s0 a b n i s) (hi : i < n) :
    WP isa (.block compareStep) s fun t => CompareInv s0 a b n (i + 1) t ∧ t.zf = some (decide (i + 1 = n)) := by
  have ra := ctx.readA i hi
  have rb := ctx.readB i hi
  rw [← inv.rest.2.1, ← inv.rest.2.2] at ra rb
  refine WP.mono (compareStep_ok s _ _ (by change byteAddr (s.gpr .esi + 0) = _; rw [inv.first]; simp)
    (by change byteAddr (s.gpr .edi + 0) = _; rw [inv.second]; simp) ra rb) ?_
  rintro t ⟨mem, first, second, acc, count, zero, rest⟩
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, mem.trans inv.mem, inv.rest.trans rest⟩, ?_⟩
  · rw [first, inv.first, BitVec.add_assoc]
    change a + (BitVec.ofNat 32 i + BitVec.ofNat 32 1) = _
    rw [← BitVec.ofNat_add]
  · rw [second, inv.second, BitVec.add_assoc]
    change b + (BitVec.ofNat 32 i + BitVec.ofNat 32 1) = _
    rw [← BitVec.ofNat_add]
  · rw [count, inv.count]
    change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    congr 1
  · rw [acc, show (0 : BitVec 32) = 0#32 from rfl, BitVec.or_eq_zero_iff, ← show (0 : BitVec 32) = 0#32 from rfl,
      byte_xor_zero32, inv.equal, inv.mem]
    constructor
    · rintro ⟨before, atI⟩ j hj
      by_cases eq : j = i
      · subst j; exact atI
      · exact before j (by omega)
    · intro all
      exact ⟨fun j hj => all j (by omega), all i (by omega)⟩
  · rw [zero, inv.count]
    change some (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), ofNat_beq_zero (by have := ctx.countFits; omega)]
    simp only [show n - i - 1 = 0 ↔ i + 1 = n by omega]

theorem compareBytes_ok (s : State) {a b : BitVec 32} {n : Nat}
    (ctx : CompareCtx s a b n) (hn : 0 < n)
    (ha : s.gpr .esi = a) (hb : s.gpr .edi = b) (hc : s.gpr .ecx = BitVec.ofNat 32 n) (hz : s.gpr .ebp = 0) :
    WP isa compareBytes s (CompareInv s a b n n) := by
  let inv := fun k t => ∃ i, i + k = n ∧ 0 < k ∧ CompareInv s a b n i t
  unfold compareBytes
  refine WP.loop (M := isa) inv ?_ n s ?_
  · intro k t h
    obtain ⟨i, hik, hk, hi⟩ := h
    refine WP.mono (compareBody_ok ctx hi (by omega)) ?_
    rintro u ⟨hu, zero⟩
    by_cases he : i + 1 = n
    · left
      refine ⟨?_, he ▸ hu⟩
      change u.zf.map not = some false
      simp only [zero, he, decide_true, Option.map_some, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega, i + 1, by omega, by omega, hu⟩
      change u.zf.map not = some true
      simp only [zero, he, decide_false, Option.map_some, Bool.not_false]
  · refine ⟨0, by omega, hn, ?_⟩
    exact ⟨by omega, by simpa using ha, by simpa using hb, by simpa using hc,
      by simp [hz], rfl, Keeps.refl _ _⟩
end VG.Proof.Rsa.X86.PrivChecked

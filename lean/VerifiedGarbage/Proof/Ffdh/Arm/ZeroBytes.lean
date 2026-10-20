module

public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Ffdh.Arm.ZeroByteStep
import VerifiedGarbage.Proof.Bignum.Arm.MaskBuffer
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Bignum.Arm.MaskBytes
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.TCB.Arm.Isa

/-! Native byte clearing for scalar prefixes and rejected key pairs. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)

structure ZeroBytesInv (advance : Bool) (s0 : State) (src dst : BitVec 32) (n i : Nat) (s : State) : Prop where
  index : i ≤ n
  source : s.gpr .r1 = src + BitVec.ofNat 32 (if advance then i else 0)
  dest : s.gpr .r0 = dst + BitVec.ofNat 32 i
  count : s.gpr .lr = BitVec.ofNat 32 (n - i)
  zeroed : ∀ j < i, s.mem (State.addr (dst + BitVec.ofNat 32 j)) = 0
  outside : ∀ a, (∀ j < i, a ≠ State.addr (dst + BitVec.ofNat 32 j)) → s.mem a = s0.mem a
  rest : Rest [.r0, .r1, .lr] s0 s

theorem zeroBytesBody_ok {advance : Bool} {s0 s : State} {src dst : BitVec 32} {n i : Nat}
    (ctx : MaskCtx s0 dst n) (inv : ZeroBytesInv advance s0 src dst n i s) (hi : i < n) (zero : s0.gpr .r2 = 0) :
    WP isa (.block (if advance then VG.Impl.Ffdh.Arm.Domain.GenerateKey.prefixStep
      else VG.Impl.Ffdh.Arm.Domain.GenerateKey.zeroStep)) s fun t =>
        ZeroBytesInv advance s0 src dst n (i + 1) t ∧ t.z = decide (i + 1 = n) := by
  have addr : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) = State.addr (dst + BitVec.ofNat 32 i) := by
    rw [inv.dest]; simp
  have write := ctx.writable i hi
  rw [← inv.rest.wr] at write
  refine WP.mono (zeroByteStep_ok advance s _ addr write ((inv.rest.gpr .r2 (by simp)).trans zero)) ?_
  rintro t ⟨mem, dest, source, count, zeroFlag, rest⟩
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, inv.rest.trans rest⟩, ?_⟩
  · rw [source, inv.source, BitVec.add_assoc]
    cases advance
    · simp
    · change src + (BitVec.ofNat 32 i + BitVec.ofNat 32 1) = _
      rw [← BitVec.ofNat_add] <;> rfl
  · rw [dest, inv.dest, BitVec.add_assoc]
    change dst + (BitVec.ofNat 32 i + BitVec.ofNat 32 1) = _
    rw [← BitVec.ofNat_add]
  · rw [count, inv.count]
    change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    congr 1
  · intro j hj
    rw [mem, VG.WriteBytes.writeW8_apply]
    by_cases same : j = i
    · subst j; simp only [ite_true] <;> rfl
    · have different : State.addr (dst + BitVec.ofNat 32 j) ≠ State.addr (dst + BitVec.ofNat 32 i) :=
        fun h => same (ctx.distinct j (by omega) i hi h)
      rw [ite_eq_right different]
      exact inv.zeroed j (by omega)
  · intro a ha
    rw [mem, VG.WriteBytes.writeW8_apply, ite_eq_right (ha i (by omega))]
    exact inv.outside a fun j hj => ha j (by omega)
  · rw [zeroFlag, inv.count]
    change (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), ofNat_beq_zero (by have := ctx.countFits; omega)]
    simp only [show n - i - 1 = 0 ↔ i + 1 = n by omega]

theorem zeroBytes_ok (advance : Bool) (s : State) {src dst : BitVec 32} {n : Nat}
    (ctx : MaskCtx s dst n) (positive : 0 < n) (zero : s.gpr .r2 = 0)
    (source : s.gpr .r1 = src) (dest : s.gpr .r0 = dst) (count : s.gpr .lr = BitVec.ofNat 32 n) :
    WP isa (.loop (.block (if advance then VG.Impl.Ffdh.Arm.Domain.GenerateKey.prefixStep
      else VG.Impl.Ffdh.Arm.Domain.GenerateKey.zeroStep)) .ne) s (ZeroBytesInv advance s src dst n n) := by
  let inv := fun k t => ∃ i, i + k = n ∧ 0 < k ∧ ZeroBytesInv advance s src dst n i t
  refine WP.loop (M := isa) inv ?_ n s ?_
  · intro k t h
    obtain ⟨i, hik, hk, hi⟩ := h
    refine WP.mono (zeroBytesBody_ok ctx hi (by omega) zero) ?_
    rintro u ⟨hu, hz⟩
    by_cases last : i + 1 = n
    · left
      refine ⟨?_, last ▸ hu⟩
      change some (!u.z) = some false
      simp only [hz, last, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega, i + 1, by omega, by omega, hu⟩
      change some (!u.z) = some true
      simp only [hz, last, decide_false, Bool.not_false]
  · refine ⟨0, by omega, positive, ?_⟩
    exact ⟨by omega, by simpa using source, by simpa using dest, by simpa using count,
      by intro j hj; omega, by intros; rfl, Rest.refl _ _⟩

end VG.Proof.Ffdh.Arm

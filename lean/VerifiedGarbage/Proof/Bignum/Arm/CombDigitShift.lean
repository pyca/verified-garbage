module

public import VerifiedGarbage.Impl.Bignum.Arm.CombDigit
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Framework.Block

/-! Public-count shifts use only modeled immediate shift instructions. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.CombDigit
open VG VG.Arm VG.Proof.X25519.Arm

private theorem step_ok (s : State) {k : Nat} (positive : 0 < k) (fit : k < 2^32)
    (count : s.gpr .r2 = BitVec.ofNat 32 k) :
    WP isa (.block [.mov .r11 (.shifted .r11 .lsr 1), .subs .r2 .r2 (.imm 1)]) s fun t =>
      t.gpr .r11 = s.gpr .r11 >>> 1 ∧ t.gpr .r2 = BitVec.ofNat 32 (k-1) ∧
      t.z = decide (k=1) ∧ t.mem = s.mem ∧ Rest [.r2,.r11] s t := by
  refine wp_mov (by rfl) fun u one => ?_
  refine wp_subs (op2_imm (by decide)) fun t two zero => WP.block_nil ?_
  have mid : u.gpr .r2 = BitVec.ofNat 32 k := (one.other .r2 (by decide)).trans count
  have sub : u.gpr .r2 - 1 = BitVec.ofNat 32 (k-1) := by
    rw [mid]
    change BitVec.ofNat 32 k - BitVec.ofNat 32 1 = BitVec.ofNat 32 (k-1)
    exact BitVec.ofNat_sub_ofNat_of_le k 1 (by decide) (by omega)
  refine ⟨(two.other .r11 (by decide)).trans one.gpr, two.gpr.trans sub, ?_,
    two.mem.trans one.mem, (one.rest (by simp)).trans (two.rest (by simp))⟩
  rw [zero,sub,ofNat_beq_zero (by omega)]
  exact decide_eq_decide.mpr (by omega)

theorem shift_ok (s : State) {n : Nat} (positive : 0 < n) (fit : n < 2^32)
    (count : s.gpr .r2 = BitVec.ofNat 32 n) :
    WP isa VG.Impl.Bignum.Arm.CombDigit.shift s fun t =>
      t.gpr .r11 = s.gpr .r11 >>> n ∧ t.gpr .r2 = 0 ∧ t.mem = s.mem ∧ Rest [.r2,.r11] s t := by
  let I := fun k t => 0 < k ∧ k ≤ n ∧ t.gpr .r2 = BitVec.ofNat 32 k ∧
    t.gpr .r11 = s.gpr .r11 >>> (n-k) ∧ t.mem = s.mem ∧ Rest [.r2,.r11] s t
  unfold VG.Impl.Bignum.Arm.CombDigit.shift
  refine WP.loop (M := isa) I ?_ n s ⟨positive,by omega,count,by simp,rfl,Rest.refl _ _⟩
  intro k t h
  obtain ⟨positiveK,leK,countK,word,mem,rest⟩ := h
  refine WP.mono (step_ok t positiveK (by omega) countK) ?_
  rintro u ⟨wordU,countU,zeroU,memU,restU⟩
  have next : u.gpr .r11 = s.gpr .r11 >>> (n-(k-1)) := by
    rw [wordU,word,←BitVec.shiftRight_add]
    congr 1
    omega
  by_cases last : k=1
  · left
    refine ⟨?_, ?_, ?_, memU.trans mem, rest.trans restU⟩
    · change some (!u.z) = some false
      simp only [zeroU,last,decide_true,Bool.not_true]
    · simpa only [last,Nat.sub_self,Nat.sub_zero] using next
    · change u.gpr .r2 = BitVec.ofNat 32 0
      simpa only [last,Nat.sub_self] using countU
  · right
    refine ⟨?_, k-1,by omega,by omega,by omega,countU,next,memU.trans mem,rest.trans restU⟩
    change some (!u.z) = some true
    simp only [zeroU,decide_eq_false last,Bool.not_false]

end VG.Proof.Bignum.Arm.CombDigit

module

import VerifiedGarbage.Impl.Bignum.Arm.DownRowUmaal
public import VerifiedGarbage.Proof.Bignum.Arm.RowUmaal
import VerifiedGarbage.Proof.Bignum.Arm.RowStep
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
public import VerifiedGarbage.Impl.Bignum.Arm.RowStep

/-! Exact states and traces of the downward row's baseline step. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.DownRowUmaal
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (mask16)

def inW (k : Nat) (s : State) : BitVec 32 := s.mem.readW (State.addr (s.gpr .r12 + BitVec.ofNat 32 k)) 32
def accW (k : Nat) (s : State) : BitVec 32 := s.mem.readW (State.addr (s.gpr .r0 + BitVec.ofNat 32 (k+4))) 32

def stepSum (k : Nat) (x : BitVec 32) (s : State) : Nat :=
  (inW k s).toNat*x.toNat+(s.gpr .r11).toNat+(accW k s).toNat

def stepAt (k : Nat) : Prog isa :=
  .seq (.block [.ldr .r2 .r12 k]) (.seq (.block rowProduct)
    (.seq (.block [.ldr .r5 .r0 (k+4)])
      (.seq (.block (addWord .r5 ++ addCarry)) (.block [.str .r3 .r0 k]))))

def stepOld (k : Nat) (x : BitVec 32) (s : State) : State :=
  { (((((((s.setReg .r2 (inW k s &&& mask16)).setReg .r6 (inW k s >>> 16)).setReg .r7
      ((x &&& mask16) * (inW k s >>> 16))).setReg .r5 (accW k s)).setReg .r4
      (BitVec.ofNat 32 (((inW k s).toNat * x.toNat + (0 : BitVec 32).toNat + (accW k s).toNat) / 2 ^ 32))).setReg
      .r3 (BitVec.ofNat 32 (stepSum k x s))).setReg .r11 (BitVec.ofNat 32 (stepSum k x s / 2 ^ 32))) with
    mem := s.mem.writeW (State.addr (s.gpr .r0 + BitVec.ofNat 32 k)) (BitVec.ofNat 32 (stepSum k x s)) }


theorem step_fwd {k : Nat} (hk : k + 4 < 4096) {x : BitVec 32} {s s' : State} {t : List Leak}
    (h1 : s.gpr .r1 = x &&& mask16) (h10 : s.gpr .r10 = x >>> 16) (h9 : s.gpr .r9 = mask16)
    (h : Exec isa (stepAt k) s t s') :
    t = [.addr (State.addr (s.gpr .r12 + BitVec.ofNat 32 k)), .addr (State.addr (s.gpr .r0 + BitVec.ofNat 32 (k+4))),
      .addr (State.addr (s.gpr .r0 + BitVec.ofNat 32 k))] ∧
    InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12 + BitVec.ofNat 32 k)) 4 ∧
    InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r0 + BitVec.ofNat 32 (k+4))) 4 ∧
    InRegions s.wr (State.addr (s.gpr .r0 + BitVec.ofNat 32 k)) 4 ∧
    NoFlags s' (stepOld k x s) := by
  unfold stepAt at h
  obtain ⟨s₁, t₁, r₁, e₁, h₁, rfl⟩ := seq_inv h
  obtain ⟨s₂, t₂, r₂, e₂, h₂, rfl⟩ := seq_inv h₁
  obtain ⟨s₃, t₃, r₃, e₃, h₃, rfl⟩ := seq_inv h₂
  obtain ⟨s₄, t₄, t₅, e₄, e₅, rfl⟩ := seq_inv h₃
  obtain ⟨hr₁, rfl, rfl⟩ := ldr_block (by omega : k < 4096) e₁
  -- `rowProduct`
  have p1 : (s.setReg .r2 (inW k s)).gpr .r1 = x &&& mask16 := by
    simp only [gpr_setReg, reduceCtorEq, ↓reduceIte]; exact h1
  have p10 : (s.setReg .r2 (inW k s)).gpr .r10 = x >>> 16 := by
    simp only [gpr_setReg, reduceCtorEq, ↓reduceIte]; exact h10
  have p9 : (s.setReg .r2 (inW k s)).gpr .r9 = mask16 := by
    simp only [gpr_setReg, reduceCtorEq, ↓reduceIte]; exact h9
  obtain ⟨_, _, w₂, prod, f₂⟩ := rowProduct_ok _ x p1 p10 p9
  rw [(Exec.det w₂ e₂).2] at prod f₂
  obtain ⟨_, _, w₂', v2, v6, v7⟩ := rowProduct_regs (s.setReg .r2 (inW k s))
  rw [(Exec.det w₂' e₂).2] at v2 v6 v7
  have t₂0 : t₂ = [] := execBlock_noMem (by decide) (Exec.block_iff.mp e₂)
  subst t₂0
  have g0 : s₂.gpr .r0 = s.gpr .r0 := by
    rw [f₂.regs .r0 (by decide)]; simp only [gpr_setReg, reduceCtorEq, ↓reduceIte]
  have m₂ : s₂.mem = s.mem := f₂.mem
  -- the accumulator word
  obtain ⟨hr₃, rfl, rfl⟩ := ldr_block hk e₃
  -- `addWord r5 ++ addCarry`
  let s₃ := s₂.setReg .r5 (s₂.mem.readW (State.addr (s₂.gpr .r0 + BitVec.ofNat 32 (k+4))) 32)
  have a3 : s₃.gpr .r5 = accW k s := by
    simp only [s₃, gpr_setReg, ↓reduceIte, g0, m₂, accW]
  have c3 : s₃.gpr .r11 = s.gpr .r11 := by
    simp only [s₃, gpr_setReg, reduceCtorEq, ↓reduceIte]
    rw [f₂.regs .r11 (by decide)]; simp only [gpr_setReg, reduceCtorEq, ↓reduceIte]
  have p3 : (s₃.gpr .r3).toNat + (s₃.gpr .r4).toNat * 2 ^ 32 = (inW k s).toNat * x.toNat := by
    simp only [s₃, gpr_setReg, reduceCtorEq, ↓reduceIte]
    rw [prod, Nat.mul_comm]; simp only [gpr_setReg, ↓reduceIte]
  have hb := mac_bound (inW k s) x (accW k s) (s.gpr .r11)
  obtain ⟨_, _, w₄, ⟨lo, sumA, sumC⟩, f₄⟩ := rowMac_ok s₃ (by rw [p3, a3, c3]; omega)
  rw [(Exec.det w₄ e₄).2] at sumA sumC f₄
  have t₄0 : t₄ = [] := execBlock_noMem (by decide) (Exec.block_iff.mp e₄)
  subst t₄0
  have g40 : s₄.gpr .r0 = s.gpr .r0 := by
    rw [f₄.regs .r0 (by decide)]; simp only [s₃, gpr_setReg, reduceCtorEq, ↓reduceIte]; exact g0
  obtain ⟨hw₅, rfl, rfl⟩ := str_block (by omega : k < 4096) e₅
  have lo3 : s₄.gpr .r3 = BitVec.ofNat 32 (stepSum k x s) := by
    refine toNat_lo (hi := s₄.gpr .r11) ?_
    rw [sumC, sumA, p3, a3, c3, stepSum]; omega
  have hi11 : s₄.gpr .r11 = BitVec.ofNat 32 (stepSum k x s / 2 ^ 32) := by
    refine toNat_hi (lo := s₄.gpr .r3) ?_
    rw [sumC, sumA, p3, a3, c3, stepSum]; omega
  have hi4 : s₄.gpr .r4 = BitVec.ofNat 32
      (((inW k s).toNat * x.toNat + (0 : BitVec 32).toNat + (accW k s).toNat) / 2 ^ 32) := by
    refine toNat_hi (lo := lo) ?_
    rw [sumA, p3, a3]; simp
  have keep : ∀ r, r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → r ≠ .r11 →
      s₄.gpr r = s.gpr r := by
    intro r h2 h3 h4 h5 h6 h7 h11
    have e4 := f₄.regs r (by simp [h3, h4, h11])
    rw [e4]
    simp only [s₃, gpr_setReg, h5, ↓reduceIte]
    by_cases h8 : r = .r8
    · subst h8
      rw [VG.Arm.Exec.gpr (fun i hi => by revert i hi; decide) e₂]
      simp only [gpr_setReg, reduceCtorEq, ↓reduceIte]
    rw [f₂.regs r (by simp [h2, h3, h4, h5, h6, h7, h8])]
    simp only [gpr_setReg, h2, ↓reduceIte]
  have k5 : s₄.gpr .r5 = accW k s := by rw [f₄.regs _ (by decide)]; exact a3
  have k2 : s₄.gpr .r2 = inW k s &&& mask16 := by
    rw [f₄.regs _ (by decide)]; simp only [s₃, gpr_setReg, reduceCtorEq, ↓reduceIte]
    rw [v2, p9]; simp only [gpr_setReg, ↓reduceIte]
  have k6 : s₄.gpr .r6 = inW k s >>> 16 := by
    rw [f₄.regs _ (by decide)]; simp only [s₃, gpr_setReg, reduceCtorEq, ↓reduceIte]
    rw [v6]; simp only [gpr_setReg, ↓reduceIte]
  have k7 : s₄.gpr .r7 = (x &&& mask16) * (inW k s >>> 16) := by
    rw [f₄.regs _ (by decide)]; simp only [s₃, gpr_setReg, reduceCtorEq, ↓reduceIte]
    rw [v7, p1]; simp only [gpr_setReg, ↓reduceIte]
  have wr₄ : s₄.wr = s.wr := by rw [f₄.wr]; exact f₂.wr
  refine ⟨by simp [g0, g40], hr₁, by rw [g0, f₂.rd, f₂.wr] at hr₃; exact hr₃, by rw [g40, wr₄] at hw₅; exact hw₅, ?_⟩
  refine ⟨funext fun r => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change s₄.gpr r = _
    cases r <;> simp only [stepOld, gpr_setReg, reduceCtorEq, ↓reduceIte]
    all_goals first
      | exact keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      | exact lo3
      | exact hi11
      | exact hi4
      | exact k5
      | exact k2
      | exact k6
      | exact k7
  · change s₄.sp = s.sp; rw [f₄.sp]; exact f₂.sp
  · change s₄.mem.writeW _ (s₄.gpr .r3) = _
    simp only [stepOld]
    rw [lo3, g40, f₄.mem]
    change s₂.mem.writeW _ _ = _
    rw [m₂]
  · change s₄.rd = s.rd; rw [f₄.rd]; exact f₂.rd
  · exact wr₄
  · change s₄.unknowns = s.unknowns; rw [f₄.unknowns]; exact f₂.unknowns
  · change s₄.syms = s.syms; rw [f₄.syms]; exact f₂.syms


end VG.Proof.Bignum.Arm.DownRowUmaal

module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public meta import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
public meta import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
public import VerifiedGarbage.Impl.Bignum.PPC64LE.MontMul
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
public import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Montgomery multiplication on PPC64LE: a multiply-accumulate step

`mcrun`: `prun` with the carrying adds (`State.writeCarry`, read through with
`Proof/Framework/PPC64LE/Carry.lean`). `montMac_ok`: a step of `montMac k`, `x = tⱼ +
r17 · sⱼ + c` with its low word stored and its high word the next carry.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Proof.Mont VG.Impl.Bignum.PPC64LE

theorem mont_ca_mem (s : State) (m : Mem) : ({ s with mem := m } : State).ca = s.ca := rfl

/-- `prun` through carrying writes. -/
tactic_template "mcrun" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
                       prun [exec_mulhu, exec_addc, exec_addze, exec_subc, exec_sube, gpr_writeCarry,
                         ca_writeCarry, ca_write, mont_ca_mem, mem_writeCarry, rd_writeCarry, wr_writeCarry,
                         sp_writeCarry, lr_writeCarry, $ls,*]))

/-- The arithmetic of a step: `t + x b + c`, a 128-bit number, is its low
word (the low word of `x b` plus `c`, plus `t`) and its high word (the high
word of `x b` plus both carries). -/
theorem montMac_arith (t x b c : BitVec 64) :
    (BitVec.ofNat 64 (t.toNat + (BitVec.ofNat 64 ((x * b).toNat + c.toNat)).toNat)).toNat +
      2 ^ 64 * (BitVec.ofNat 64 ((BitVec.ofNat 64 ((BitVec.ofNat 64 (x.toNat * b.toNat / 2 ^ 64)).toNat +
        (decide (2 ^ 64 ≤ (x * b).toNat + c.toNat)).toNat)).toNat +
          (decide (2 ^ 64 ≤ t.toNat + (BitVec.ofNat 64 ((x * b).toNat + c.toNat)).toNat)).toNat)).toNat =
      t.toNat + x.toNat * b.toNat + c.toNat := by
  have hx := x.isLt
  have hb := b.isLt
  have ht := t.isLt
  have hc := c.isLt
  have hP : x.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  simp only [BitVec.toNat_ofNat, BitVec.toNat_mul]
  by_cases h1 : 2 ^ 64 ≤ x.toNat * b.toNat % 2 ^ 64 + c.toNat <;>
    by_cases h2 : 2 ^ 64 ≤ t.toNat + (x.toNat * b.toNat % 2 ^ 64 + c.toNat) % 2 ^ 64 <;>
    simp only [h1, h2, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega

/-- The registers `montMac` writes. -/
def montMacRegs : List Reg := [.r14, .r15, .r18, .r19, .r20, .r22]

/-- A step (`montMac k`), the pointers `r14`, `r15` at offsets `dT`, `dS` of `B`:
the word `v` stored at `dT` and the carry `r18` make up `tⱼ + r17 · sⱼ + c`,
for the words `tⱼ`, `sⱼ` at `dT + k`, `dS + k` and the carry `c`. -/
theorem montMac_ok {s : State} {B : Addr} {Z dT dS k : Nat} (hs : Scr s B Z) (hk : k = 0 ∨ k = 8)
    (h14 : s.gpr .r14 = off B dT) (h15 : s.gpr .r15 = off B dS)
    (hT : dT + k + 8 ≤ Z) (hS : dS + k + 8 ≤ Z) (hT' : dT + 8 ≤ Z) :
    WP isa (.block (montMac k)) s fun s' =>
      (s'.gpr .r14 = off B (dT + 8) ∧ s'.gpr .r15 = off B (dS + 8) ∧
        ∃ v : BitVec 64, s'.mem = s.mem.writeW (off B dT) v ∧
        v.toNat + 2 ^ 64 * (s'.gpr .r18).toNat =
          (word s.mem B (dT + k)).toNat + (s.gpr .r17).toNat * (word s.mem B (dS + k)).toNat +
            (s.gpr .r18).toNat) ∧ Keep montMacRegs s s' := by
  rcases hk with rfl | rfl <;> simp only [Nat.add_zero] at hT hS ⊢ <;>
    refine WP.keep montMacRegs ?_ (by decide) <;> unfold montMac <;>
    mcrun [h14, h15, hs.ld hT, hs.ld hS, hs.st hT'] <;> exact ⟨_, rfl, montMac_arith _ _ _ _⟩

/-- A store of word `j` of a number of `j + 1` words. -/
theorem mont_wordsVal_write_top (m : Mem) (B : Addr) (d j : Nat) (v : BitVec 64) (h : d + 8 * j + 8 ≤ 2 ^ 64) :
    wordsVal (m.writeW (off B (d + 8 * j)) v) B d (j + 1) = wordsVal m B d j + 2 ^ (64 * j) * v.toNat := by
  rw [wordsVal_succ_top, (writeW_outside m B v h).wordsVal (by omega_arith) (by omega_arith), word_writeW_self]

/-- `N` steps (`countLoop .r16 (montMac k)`), from the pointers at offsets `dT`,
`dS`, with `x` in `r17` and the carry `c₀` in `r18`: the `N` words stored
from `dT` on and the last carry make up `T + x S + c₀`, for the `N` words
`T`, `S` from `dT + k`, `dS + k` on. -/
theorem montMacLoop_ok {s₀ : State} {B : Addr} {Z dT dS k N : Nat} (hs : Scr s₀ B Z) (hk : k = 0 ∨ k = 8)
    (h14 : s₀.gpr .r14 = off B dT) (h15 : s₀.gpr .r15 = off B dS) (h16 : s₀.gpr .r16 = BitVec.ofNat 64 N)
    (hN : 1 ≤ N) (hN' : N < 2 ^ 32) (hT : dT + k + 8 * N ≤ Z) (hS : dS + k + 8 * N ≤ Z)
    (hsep : dS + k + 8 * N ≤ dT ∨ dT + 8 * N ≤ dS + k) :
    WP isa (countLoop .r16 (montMac k)) s₀ fun s =>
      s.gpr .r14 = off B (dT + 8 * N) ∧ Outside B dT (8 * N) s₀.mem s.mem ∧
      wordsVal s.mem B dT N + 2 ^ (64 * N) * (s.gpr .r18).toNat =
        wordsVal s₀.mem B (dT + k) N + (s₀.gpr .r17).toNat * wordsVal s₀.mem B (dS + k) N +
          (s₀.gpr .r18).toNat ∧
      Keep (montMacRegs ++ ([.r16] : List Reg)) s₀ s := by
  have hnw := hs.nowrap
  let x := (s₀.gpr .r17).toNat
  let Inv : Nat → State → Prop := fun j s =>
    s.gpr .r14 = off B (dT + 8 * j) ∧ s.gpr .r15 = off B (dS + 8 * j) ∧
    Outside B dT (8 * j) s₀.mem s.mem ∧
    wordsVal s.mem B dT j + 2 ^ (64 * j) * (s.gpr .r18).toNat =
      wordsVal s₀.mem B (dT + k) j + x * wordsVal s₀.mem B (dS + k) j + (s₀.gpr .r18).toNat ∧
    Keep (montMacRegs ++ ([.r16] : List Reg)) s₀ s
  have hinv0 : Inv 0 s₀ :=
    ⟨by rw [h14]; rfl, by rw [h15]; rfl, Outside.refl _ _ _ _, by simp [wordsVal], Keep.refl _ _⟩
  refine WP.mono (wp_countdown (body := .block (montMac k ++ ([.subi .r16 .r16 1] : List Instr)))
    (cnt := .r16) (N := N) (by omega_arith) (by omega_arith) Inv (fun j hj s hI hc => ?_) hinv0 h16)
    fun s ⟨i14, _, iout, ieq, ik⟩ => ⟨i14, iout, ieq, ik⟩
  obtain ⟨i14, i15, iout, ieq, ik⟩ := hI
  have r17 : s.gpr .r17 = s₀.gpr .r17 := ik.gpr _ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (montMac_ok (hs.congr ik.wr) hk i14 i15 (by omega_arith) (by omega_arith) (by omega_arith))
    fun s₁ ⟨⟨j14, j15, v, jm, jv⟩, k₁⟩ => ?_
  refine WP.mono (subi_ok s₁ .r16 (by decide)) fun s₂ e => ?_
  subst e
  -- The words read are those on entry.
  have wt : word s.mem B (dT + 8 * j + k) = word s₀.mem B (dT + 8 * j + k) :=
    iout.word (by omega_arith) (by omega_arith)
  have ws : word s.mem B (dS + 8 * j + k) = word s₀.mem B (dS + 8 * j + k) :=
    iout.word (by omega_arith) (by omega_arith)
  rw [wt, ws, r17] at jv
  have p64 : 2 ^ (64 * (j + 1)) = 2 ^ (64 * j) * 2 ^ 64 := by rw [Nat.mul_succ, Nat.pow_add]
  refine ⟨⟨by gsimp; rw [j14, Nat.mul_succ, Nat.add_assoc], by gsimp; rw [j15, Nat.mul_succ, Nat.add_assoc],
    ?_, ?_, ?_⟩, ?_⟩
  · gsimp; rw [jm]
    exact (iout.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW_outside _ B v (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · gsimp
    rw [jm, mont_wordsVal_write_top _ _ _ _ _ (by omega_arith), wordsVal_succ_top s₀.mem B (dT + k) j,
      wordsVal_succ_top s₀.mem B (dS + k) j, show dT + k + 8 * j = dT + 8 * j + k by omega_arith,
      show dS + k + 8 * j = dS + 8 * j + k by omega_arith, p64]
    have e : 2 ^ (64 * j) * v.toNat + 2 ^ (64 * j) * 2 ^ 64 * (s₁.gpr .r18).toNat =
        2 ^ (64 * j) * ((word s₀.mem B (dT + 8 * j + k)).toNat +
          x * (word s₀.mem B (dS + 8 * j + k)).toNat + (s.gpr .r18).toNat) := by
      rw [← jv, Nat.mul_add, Nat.mul_assoc]
    grind
  · have k₂ : Keep [.r16] s₁ (s₁.write .r16 (s₁.gpr .r16 - BitVec.ofNat 64 1)) := Keep.write _ _ _
    exact ik.trans' ((k₁.mono (by decide)).trans' (k₂.mono (by decide)))
  · gsimp
    rw [k₁.gpr _ (by decide)]

end VG.Proof.Bignum.PPC64LE

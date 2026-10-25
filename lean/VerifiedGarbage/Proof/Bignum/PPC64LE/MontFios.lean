module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public meta import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
public meta import VerifiedGarbage.Proof.Framework.PPC64LE.Carry
public import VerifiedGarbage.Impl.Bignum.PPC64LE.MontMul
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# Montgomery multiplication on PPC64LE: the steps of a round

`mcrun`: `prun` with the carrying adds (`State.writeCarry`, read through with
`Proof/Framework/PPC64LE/Carry.lean`). `fiosStep_ok`: a word of a round, `tⱼ +
aᵢ bⱼ + u mⱼ` plus the two carries, its low word stored and the carries
replaced.
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

/-- The arithmetic of one of a step's two sums: `x + p q + c`, below `2¹²⁸`, is
the low word of `p q` plus the low word of `c + x`, and `2⁶⁴` times the high
word of `p q` plus both carries. -/
theorem fios_chain (x p q c : BitVec 64) :
    (BitVec.ofNat 64 ((p * q).toNat + (BitVec.ofNat 64 (c.toNat + x.toNat)).toNat)).toNat +
      2 ^ 64 * (BitVec.ofNat 64 ((BitVec.ofNat 64 ((BitVec.ofNat 64 (p.toNat * q.toNat / 2 ^ 64)).toNat +
        (decide (2 ^ 64 ≤ c.toNat + x.toNat)).toNat)).toNat +
          (decide (2 ^ 64 ≤ (p * q).toNat + (BitVec.ofNat 64 (c.toNat + x.toNat)).toNat)).toNat)).toNat =
      x.toNat + p.toNat * q.toNat + c.toNat := by
  have hx := x.isLt
  have hp := p.isLt
  have hq := q.isLt
  have hc := c.isLt
  have hP : p.toNat * q.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega_arith) (by omega_arith)
  simp only [BitVec.toNat_ofNat, BitVec.toNat_mul]
  by_cases h1 : 2 ^ 64 ≤ c.toNat + x.toNat <;>
    by_cases h2 : 2 ^ 64 ≤ p.toNat * q.toNat % 2 ^ 64 + (c.toNat + x.toNat) % 2 ^ 64 <;>
    simp only [h1, h2, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_arith

theorem fiosStep_writes (k : Nat) : writesOnly [.r18, .r19, .r20, .r22] (.block (fiosStep k)) = true := rfl

theorem fiosStep_ok {s : State} {B : Addr} {Z dT dB dM k : Nat} (hs : Scr s B Z)
    (h14 : s.gpr .r14 = off B dT) (h15 : s.gpr .r15 = off B dB) (h3 : s.gpr .r3 = off B dM)
    (hk : k + 8 < 32768) (hk4 : k % 4 = 0)
    (hT : dT + k + 16 ≤ Z) (hB : dB + k + 16 ≤ Z) (hM : dM + k + 16 ≤ Z) :
    WP isa (.block (fiosStep k)) s fun s' =>
      (∃ v : BitVec 64, s'.mem = s.mem.writeW (off B (dT + k)) v ∧
        v.toNat + 2 ^ 64 * ((s'.gpr .r18).toNat + (s'.gpr .r22).toNat) =
          (word s.mem B (dT + (k + 8))).toNat + (s.gpr .r17).toNat * (word s.mem B (dB + (k + 8))).toNat +
            (s.gpr .r0).toNat * (word s.mem B (dM + (k + 8))).toNat +
            ((s.gpr .r18).toNat + (s.gpr .r22).toNat)) ∧ Keep [.r18, .r19, .r20, .r22] s s' := by
  have hk1 : k < 32768 := by omega_arith
  have hk2 : (k + 8) % 4 = 0 := by omega_arith
  refine WP.keep _ ?_ (fiosStep_writes k)
  unfold fiosStep
  mcrun [h14, h15, h3, hk, hk1, hk2, hk4, hs.ld (show dT + (k + 8) + 8 ≤ Z by omega_arith),
    hs.ld (show dB + (k + 8) + 8 ≤ Z by omega_arith), hs.ld (show dM + (k + 8) + 8 ≤ Z by omega_arith),
    hs.st (show dT + k + 8 ≤ Z by omega_arith)]
  refine ⟨_, rfl, ?_⟩
  have h1 := fios_chain (word s.mem B (dT + (k + 8))) (s.gpr .r17) (word s.mem B (dB + (k + 8))) (s.gpr .r18)
  have h2 := fios_chain (BitVec.ofNat 64 ((s.gpr .r17 * word s.mem B (dB + (k + 8))).toNat +
    (BitVec.ofNat 64 ((s.gpr .r18).toNat + (word s.mem B (dT + (k + 8))).toNat)).toNat)) (s.gpr .r0) (word s.mem B (dM + (k + 8))) (s.gpr .r22)
  simp only [Nat.reducePow, word] at h1 h2 ⊢
  omega_arith

/-! ## The words of a round -/

/-- A store of word `j` of a number of `j + 1` words. -/
theorem fios_wordsVal_write_top (m : Mem) (B : Addr) (d j : Nat) (v : BitVec 64) (h : d + 8 * j + 8 ≤ 2 ^ 64) :
    wordsVal (m.writeW (off B (d + 8 * j)) v) B d (j + 1) = wordsVal m B d j + 2 ^ (64 * j) * v.toNat := by
  rw [wordsVal_succ_top, (writeW_outside m B v h).wordsVal (by omega_arith) (by omega_arith), word_writeW_self]

theorem fios_wordsVal_append (m : Mem) (B : Addr) (d j k : Nat) :
    wordsVal m B d (j + k) = wordsVal m B d j + 2 ^ (64 * j) * wordsVal m B (d + 8 * j) k := by
  induction j generalizing d with
  | zero => simp only [wordsVal, Nat.zero_add, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.add_zero]
  | succ j ih =>
    rw [Nat.add_right_comm, wordsVal, ih, wordsVal, pow64_succ, show d + 8 + 8 * j = d + 8 * (j + 1) by omega_arith,
      Nat.mul_add, Nat.mul_assoc]
    omega_arith

theorem fiosSteps_succ (K : Nat) :
    (List.range (K + 1)).flatMap (fun k => fiosStep (8 * k)) =
      (List.range K).flatMap (fun k => fiosStep (8 * k)) ++ fiosStep (8 * K) := by
  simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The registers the steps write. -/
def fiosRegs : List Reg := [.r18, .r19, .r20, .r22]

/-- The sum of `K` steps from `T`, `S`, `M` and the carries `c + d`, as the
sum of the first `K` steps and the last. -/
theorem fios_sum_succ {W T S M W' C₀ C₁ C₂ a u v t b m P : Nat}
    (e₁ : W + P * C₁ = T + a * S + u * M + C₀) (e₂ : v + 2 ^ 64 * C₂ = t + a * b + u * m + C₁)
    (hW : W' = W + P * v) :
    W' + P * 2 ^ 64 * C₂ = T + P * t + a * (S + P * b) + u * (M + P * m) + C₀ := by
  subst hW
  have e : P * v + P * 2 ^ 64 * C₂ = P * (t + a * b + u * m + C₁) := by
    rw [← e₂, Nat.mul_add, Nat.mul_assoc]
  grind

/-- `K` steps (`8 K + 8` bytes into the arrays at most `2¹⁵`), the pointers
`r14`, `r15`, `r3` at offsets `dT`, `dB`, `dM`: the `K` words stored from
`dT` on and the carries `r18 + r22` make up `T + aᵢ S + u M` plus the carries
on entry, for the `K` words `T`, `S`, `M` from `dT + 8`, `dB + 8`, `dM + 8`
on, `aᵢ` in `r17` and `u` in `r0`. -/
theorem fiosSteps_ok {B : Addr} {Z dT dB dM : Nat} : ∀ (K : Nat) {s : State}, Scr s B Z →
    s.gpr .r14 = off B dT → s.gpr .r15 = off B dB → s.gpr .r3 = off B dM → 8 * K < 32768 →
    dT + 8 * K + 8 ≤ Z → dB + 8 * K + 8 ≤ Z → dM + 8 * K + 8 ≤ Z →
    (dB + 8 * K + 8 ≤ dT ∨ dT + 8 * K ≤ dB + 8) → (dM + 8 * K + 8 ≤ dT ∨ dT + 8 * K ≤ dM + 8) →
    WP isa (.block ((List.range K).flatMap fun k => fiosStep (8 * k))) s fun s' =>
      (Outside B dT (8 * K) s.mem s'.mem ∧
        wordsVal s'.mem B dT K + 2 ^ (64 * K) * ((s'.gpr .r18).toNat + (s'.gpr .r22).toNat) =
          wordsVal s.mem B (dT + 8) K + (s.gpr .r17).toNat * wordsVal s.mem B (dB + 8) K +
            (s.gpr .r0).toNat * wordsVal s.mem B (dM + 8) K + ((s.gpr .r18).toNat + (s.gpr .r22).toNat)) ∧
      Keep fiosRegs s s'
  | 0, s, _, _, _, _, _, _, _, _, _, _ => by
    simp only [List.range_zero, List.flatMap_nil]
    exact WP.block_nil ⟨⟨Outside.refl _ _ _ _, by simp [wordsVal]⟩, Keep.refl _ _⟩
  | K + 1, s, hs, h14, h15, h3, hK, hT, hB, hM, sB, sM => by
    have hnw := hs.nowrap
    rw [fiosSteps_succ, WP.block_append_iff]
    refine WP.mono (fiosSteps_ok K hs h14 h15 h3 (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      (by omega_arith)) fun s₁ ⟨⟨o₁, e₁⟩, k₁⟩ => ?_
    have g : ∀ r ∈ [Reg.r0, .r3, .r14, .r15, .r17], s₁.gpr r = s.gpr r := fun r hr =>
      k₁.gpr r (by revert r hr; decide)
    refine WP.mono (fiosStep_ok (dT := dT) (dB := dB) (dM := dM) (k := 8 * K) (hs.congr k₁.wr) (by rw [g .r14 (by decide), h14])
      (by rw [g .r15 (by decide), h15]) (by rw [g .r3 (by decide), h3]) (by omega_arith) (by omega_arith) (by omega_arith)
      (by omega_arith) (by omega_arith)) fun s₂ ⟨⟨v, m₂, e₂⟩, k₂⟩ => ⟨⟨?_, ?_⟩, (k₁.trans k₂).mono (by decide)⟩
    · rw [m₂]
      exact (o₁.mono (Nat.le_refl _) (by omega_arith)).trans
        ((writeW_outside _ B v (by omega_arith)).mono (by omega_arith) (by omega_arith))
    · -- The words read are those on entry.
      rw [show dT + (8 * K + 8) = dT + 8 + 8 * K by omega_arith, show dB + (8 * K + 8) = dB + 8 + 8 * K by omega_arith,
        show dM + (8 * K + 8) = dM + 8 + 8 * K by omega_arith, o₁.word (by omega_arith) (by omega_arith),
        o₁.word (by omega_arith) (by omega_arith), o₁.word (by omega_arith) (by omega_arith), g .r0 (by decide),
        g .r17 (by decide)] at e₂
      rw [m₂, fios_wordsVal_write_top _ _ _ _ _ (by omega_arith), wordsVal_succ_top s.mem B (dT + 8) K,
        wordsVal_succ_top s.mem B (dB + 8) K, wordsVal_succ_top s.mem B (dM + 8) K, Nat.mul_succ, Nat.pow_add]
      exact fios_sum_succ e₁ e₂ rfl

/-- The sum of a loop's iterations, as the sum of the first ones and the last. -/
theorem fios_sum_group {W T S M W' C₀ C₁ C₂ a u G T' S' M' P Q : Nat}
    (e₁ : W + P * C₁ = T + a * S + u * M + C₀) (e₂ : G + Q * C₂ = T' + a * S' + u * M' + C₁)
    (hW : W' = W + P * G) :
    W' + P * Q * C₂ = T + P * T' + a * (S + P * S') + u * (M + P * M') + C₀ := by
  subst hW
  have e : P * G + P * Q * C₂ = P * (T' + a * S' + u * M' + C₁) := by
    rw [← e₂, Nat.mul_add, Nat.mul_assoc]
  grind

/-- The registers a loop of steps writes. -/
def fiosLoopRegs : List Reg := [.r3, .r14, .r15, .r16, .r18, .r19, .r20, .r22]

/-- What `N` iterations of `U` steps leave, the pointers at offsets `dT`,
`dB`, `dM` on entry: `fiosSteps_ok` for `U N` words, the pointers advanced
past them. -/
def FiosPost (B : Addr) (dT dB dM K : Nat) (s₀ s : State) : Prop :=
  s.gpr .r14 = off B (dT + 8 * K) ∧ s.gpr .r15 = off B (dB + 8 * K) ∧ s.gpr .r3 = off B (dM + 8 * K) ∧
    Outside B dT (8 * K) s₀.mem s.mem ∧
    wordsVal s.mem B dT K + 2 ^ (64 * K) * ((s.gpr .r18).toNat + (s.gpr .r22).toNat) =
      wordsVal s₀.mem B (dT + 8) K + (s₀.gpr .r17).toNat * wordsVal s₀.mem B (dB + 8) K +
        (s₀.gpr .r0).toNat * wordsVal s₀.mem B (dM + 8) K + ((s₀.gpr .r18).toNat + (s₀.gpr .r22).toNat) ∧
    Keep fiosLoopRegs s₀ s

/-- `N > 0` iterations of `U` steps (`countLoop .r16 (fiosGroup U)`). -/
theorem fiosLoop_ok {B : Addr} {Z dT dB dM U N : Nat} (hU : 8 * U < 32768) {s₀ : State} (hs : Scr s₀ B Z)
    (h14 : s₀.gpr .r14 = off B dT) (h15 : s₀.gpr .r15 = off B dB) (h3 : s₀.gpr .r3 = off B dM)
    (h16 : s₀.gpr .r16 = BitVec.ofNat 64 N) (hN : 1 ≤ N) (hN' : N < 2 ^ 32)
    (hT : dT + 8 * (U * N) + 8 ≤ Z) (hB : dB + 8 * (U * N) + 8 ≤ Z) (hM : dM + 8 * (U * N) + 8 ≤ Z)
    (sB : dB + 8 * (U * N) + 8 ≤ dT ∨ dT + 8 * (U * N) ≤ dB + 8)
    (sM : dM + 8 * (U * N) + 8 ≤ dT ∨ dT + 8 * (U * N) ≤ dM + 8) :
    WP isa (countLoop .r16 (fiosGroup U)) s₀ (FiosPost B dT dB dM (U * N) s₀) := by
  have hnw := hs.nowrap
  refine wp_countdown (body := .block (fiosGroup U ++ ([.subi .r16 .r16 1] : List Instr))) (cnt := .r16)
    (N := N) (by omega_arith) (by omega_arith) (fun i s => FiosPost B dT dB dM (U * i) s₀ s) (fun i hi s hI hc => ?_)
    ⟨by rw [h14]; rfl, by rw [h15]; rfl, by rw [h3]; rfl, Outside.refl _ _ _ _, by simp [wordsVal],
      Keep.refl _ _⟩ h16
  obtain ⟨i14, i15, i3, iout, ieq, ik⟩ := hI
  have hUi : U * i + U ≤ U * N := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  have g : ∀ r ∈ [Reg.r0, .r17], s.gpr r = s₀.gpr r := fun r hr => ik.gpr r (by revert r hr; decide)
  rw [fiosGroup, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fiosSteps_ok U (hs.congr ik.wr) i14 i15 i3 hU (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith)) fun s₁ ⟨⟨o₁, e₁⟩, k₁⟩ => ?_
  have g₁ : ∀ r ∈ [Reg.r3, .r14, .r15, .r16], s₁.gpr r = s.gpr r := fun r hr =>
    k₁.gpr r (by revert r hr; decide)
  have hst : WP isa (.block [.addi .r14 .r14 (8 * U), .addi .r15 .r15 (8 * U), .addi .r3 .r3 (8 * U),
      .subi .r16 .r16 1]) s₁ fun s₂ =>
      s₂ = (((s₁.write .r14 (off B (dT + 8 * (U * i) + 8 * U))).write .r15 (off B (dB + 8 * (U * i) + 8 * U))).write
        .r3 (off B (dM + 8 * (U * i) + 8 * U))).write .r16 (s₁.gpr .r16 - BitVec.ofNat 64 1) := by
    prun [g₁ .r14 (by decide), g₁ .r15 (by decide), g₁ .r3 (by decide), i14, i15, i3, hU]
  refine WP.mono hst fun s₂ e => ?_
  subst e
  have pU : U * (i + 1) = U * i + U := Nat.mul_succ _ _
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, by gsimp; rw [g₁ .r16 (by decide)]⟩
  · gsimp; rw [pU, Nat.mul_add, Nat.add_assoc]
  · gsimp; rw [pU, Nat.mul_add, Nat.add_assoc]
  · gsimp; rw [pU, Nat.mul_add, Nat.add_assoc]
  · gsimp
    exact (iout.mono (Nat.le_refl _) (by omega_arith)).trans (o₁.mono (by omega_arith) (by omega_arith))
  · gsimp
    -- The words read are those on entry.
    have rd : ∀ d, (d + 8 * (U * N) + 8 ≤ dT ∨ dT + 8 * (U * N) ≤ d + 8) → d + 8 * (U * N) + 8 ≤ Z →
        wordsVal s.mem B (d + 8 * (U * i) + 8) U = wordsVal s₀.mem B (d + 8 + 8 * (U * i)) U := by
      intro d hd hdZ
      rw [show d + 8 * (U * i) + 8 = d + 8 + 8 * (U * i) by omega_arith]
      exact iout.wordsVal (by omega_arith) (by omega_arith)
    rw [rd dB sB hB, rd dM sM hM, g .r0 (by decide),
      g .r17 (by decide)] at e₁
    rw [show dT + 8 * (U * i) + 8 = dT + 8 + 8 * (U * i) by omega_arith,
      iout.wordsVal (o := dT) (n := 8 * (U * i)) (by omega_arith) (by omega_arith)] at e₁
    rw [pU, fios_wordsVal_append s₁.mem B dT (U * i) U, fios_wordsVal_append s₀.mem B (dT + 8) (U * i) U,
      fios_wordsVal_append s₀.mem B (dB + 8) (U * i) U, fios_wordsVal_append s₀.mem B (dM + 8) (U * i) U,
      show 64 * (U * i + U) = 64 * (U * i) + 64 * U by omega_arith, Nat.pow_add,
      (o₁.wordsVal (o := dT + 8 * (U * i)) (n := 8 * U) (d := dT) (k := U * i) (by omega_arith) (by omega_arith))]
    exact fios_sum_group ieq e₁ rfl
  · exact ik.trans' ((k₁.mono (by decide)).trans' (Keep.mono (by
      exact (((Keep.write _ _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans (Keep.write _ _ _))
      (by decide)))

/-- `N` iterations of `U` steps if `N ≠ 0` (`countLoop? (fiosGroup U)`). -/
theorem fiosLoop?_ok {B : Addr} {Z dT dB dM U N : Nat} (hU : 8 * U < 32768) {s₀ : State} (hs : Scr s₀ B Z)
    (h14 : s₀.gpr .r14 = off B dT) (h15 : s₀.gpr .r15 = off B dB) (h3 : s₀.gpr .r3 = off B dM)
    (h16 : s₀.gpr .r16 = BitVec.ofNat 64 N) (hN' : N < 2 ^ 32)
    (hT : dT + 8 * (U * N) + 8 ≤ Z) (hB : dB + 8 * (U * N) + 8 ≤ Z) (hM : dM + 8 * (U * N) + 8 ≤ Z)
    (sB : dB + 8 * (U * N) + 8 ≤ dT ∨ dT + 8 * (U * N) ≤ dB + 8)
    (sM : dM + 8 * (U * N) + 8 ≤ dT ∨ dT + 8 * (U * N) ≤ dM + 8) :
    WP isa (countLoop? (fiosGroup U)) s₀ (FiosPost B dT dB dM (U * N) s₀) := by
  refine WP.ite _ (eval_zero_ofNat _ _ (by omega_arith) h16) (fun hz => ?_) (fun hz => ?_)
  · have hN : N = 0 := of_decide_eq_true hz
    subst hN
    exact WP.block_nil ⟨by rw [h14]; rfl, by rw [h15]; rfl, by rw [h3]; rfl, Outside.refl _ _ _ _,
      by simp [wordsVal], Keep.refl _ _⟩
  · exact fiosLoop_ok hU hs h14 h15 h3 h16 (Nat.pos_of_ne_zero (of_decide_eq_false hz)) hN' hT hB hM sB sM

/-! ## The start and the end of a round -/

theorem fios_rem (n : Nat) : BitVec.ofNat 64 n <<< 62 >>> 62 = BitVec.ofNat 64 (n % 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  omega_arith

theorem fios_quot (n : Nat) (h : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 2 = BitVec.ofNat 64 (n / 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_arith

/-- The arithmetic of word 0's product: `t + a b` is the low word of `t +
(a b mod 2⁶⁴)` and `2⁶⁴` times the high word of `a b` plus the carry. -/
theorem fios_head_arith (t a b : BitVec 64) :
    (BitVec.ofNat 64 (t.toNat + (a * b).toNat)).toNat +
      2 ^ 64 * (BitVec.ofNat 64 ((BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64)).toNat +
        (decide (2 ^ 64 ≤ t.toNat + (a * b).toNat)).toNat)).toNat = t.toNat + a.toNat * b.toNat := by
  have ht := t.isLt
  have ha := a.isLt
  have hb := b.isLt
  have hP : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega_arith) (by omega_arith)
  simp only [BitVec.toNat_ofNat, BitVec.toNat_mul]
  by_cases h1 : 2 ^ 64 ≤ t.toNat + a.toNat * b.toNat % 2 ^ 64 <;>
    simp only [h1, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_arith

/-- The arithmetic of word 0's reduction: `u m₀ + s₀`, a multiple of `2⁶⁴`, is
`2⁶⁴` times the high word of `u m₀` plus the carry of its low word plus `s₀`. -/
theorem fios_red_arith (t u m : BitVec 64) (h : ((u * m).toNat + t.toNat) % 2 ^ 64 = 0) :
    2 ^ 64 * (BitVec.ofNat 64 ((BitVec.ofNat 64 (u.toNat * m.toNat / 2 ^ 64)).toNat +
      (decide (2 ^ 64 ≤ (u * m).toNat + t.toNat)).toNat)).toNat = u.toNat * m.toNat + t.toNat := by
  have hu := u.isLt
  have hm := m.isLt
  have ht := t.isLt
  have hP : u.toNat * m.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega_arith) (by omega_arith)
  simp only [BitVec.toNat_ofNat, BitVec.toNat_mul] at h ⊢
  by_cases h1 : 2 ^ 64 ≤ u.toNat * m.toNat % 2 ^ 64 + t.toNat <;>
    simp only [h1, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_arith

/-- The registers the start of a round writes. -/
def fiosHeadRegs : List Reg := [.r0, .r3, .r6, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22]

/-- The start of a round (`fiosHead ++ fiosRem`), for `aᵢ` at `da` (`r6`),
`T` at `dA`, `b` at `dB`, `m` at `dM`, `n = 2 w` in `r11` and `-m⁻¹ mod 2³²`
in `r12`: `aᵢ` in `r17`, `r0` a `u < 2⁶⁴` such that `2⁶⁴ (c + d) = t₀ + aᵢ b₀
+ u m₀` for the carries `c` in `r18` and `d` in `r22`, the pointers at word
0 and `(w - 1) mod 4` in `r16`. -/
theorem fiosHead_ok {s : State} {B : Addr} {Z da dA dB dM w : Nat} (hs : Scr s B Z)
    (h6 : s.gpr .r6 = off B da) (h7 : s.gpr .r7 = off B dB) (h8 : s.gpr .r8 = off B dA)
    (h10 : s.gpr .r10 = off B dM) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hinv : ((word s.mem B dM).toNat % 2 ^ 32 * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (ha : da + 8 ≤ Z) (hA : dA + 8 ≤ Z) (hB : dB + 8 ≤ Z) (hM : dM + 8 ≤ Z) :
    WP isa (.block (fiosHead ++ fiosRem)) s fun s' =>
      (s'.gpr .r17 = word s.mem B da ∧ s'.gpr .r6 = off B (da + 8) ∧ s'.gpr .r14 = off B dA ∧
        s'.gpr .r15 = off B dB ∧ s'.gpr .r3 = off B dM ∧ s'.gpr .r16 = BitVec.ofNat 64 ((w - 1) % 4) ∧
        s'.mem = s.mem ∧
        2 ^ 64 * ((s'.gpr .r18).toNat + (s'.gpr .r22).toNat) = (word s.mem B dA).toNat +
          (word s.mem B da).toNat * (word s.mem B dB).toNat + (s'.gpr .r0).toNat * (word s.mem B dM).toNat) ∧
      Keep fiosHeadRegs s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold fiosHead fiosRem
  mcrun [h6, h7, h8, h10, h11, hs.ld ha, hs.ld hA, hs.ld hB, hs.ld hM, BitVec.add_zero,
    mont_ofNat_shr1 (show w < 2 ^ 63 by omega_arith), ofNat_sub_one hw (by omega_arith), fios_rem (w - 1)]
  have h1 := fios_head_arith (word s.mem B dA) (word s.mem B da) (word s.mem B dB)
  have hm := mont_newton64 (word s.mem B dM) (s.gpr .r12) hinv
  have h2 := fios_red_arith (BitVec.ofNat 64 ((word s.mem B dA).toNat + (word s.mem B da * word s.mem B dB).toNat))
    (BitVec.ofNat 64 ((word s.mem B dA).toNat + (word s.mem B da * word s.mem B dB).toNat) *
      ((word s.mem B dM * s.gpr .r12 + BitVec.ofNat 64 2) * s.gpr .r12)) (word s.mem B dM) (by
    rw [BitVec.toNat_mul, BitVec.toNat_mul, Nat.mod_add_mod, Nat.add_comm]; exact mont_low _ _ _ hm)
  simp only [Nat.reducePow, word] at h1 h2 ⊢
  omega_arith

/-- The arithmetic of the end of a round: `c + t + d` as two words, the high
word the sum of the two carries. -/
theorem fios_top_arith (c t d : BitVec 64) :
    (BitVec.ofNat 64 ((BitVec.ofNat 64 (c.toNat + t.toNat)).toNat + d.toNat)).toNat +
      2 ^ 64 * (BitVec.ofNat 64 ((BitVec.ofNat 64 ((0#64).toNat + (decide (2 ^ 64 ≤ c.toNat + t.toNat)).toNat)).toNat +
        (decide (2 ^ 64 ≤ (BitVec.ofNat 64 (c.toNat + t.toNat)).toNat + d.toNat)).toNat)).toNat =
      c.toNat + t.toNat + d.toNat := by
  have hc := c.isLt
  have ht := t.isLt
  have hd := d.isLt
  simp only [BitVec.toNat_ofNat]
  by_cases h1 : 2 ^ 64 ≤ c.toNat + t.toNat <;>
    by_cases h2 : 2 ^ 64 ≤ (c.toNat + t.toNat) % 2 ^ 64 + d.toNat <;>
    simp only [h1, h2, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_arith

/-- The end of a round (`fiosTop`), `r14` at `dT`: the carries `c` (`r18`)
and `d` (`r22`) plus the word at `dT + 8`, stored as two words at `dT`. -/
theorem fiosTop_ok {s : State} {B : Addr} {Z dT : Nat} (hs : Scr s B Z) (h14 : s.gpr .r14 = off B dT)
    (hT : dT + 16 ≤ Z) :
    WP isa (.block fiosTop) s fun s' =>
      (∃ x y : BitVec 64, s'.mem = (s.mem.writeW (off B dT) x).writeW (off B (dT + 8)) y ∧
        x.toNat + 2 ^ 64 * y.toNat = (s.gpr .r18).toNat + (word s.mem B (dT + 8)).toNat + (s.gpr .r22).toNat) ∧
      Keep fiosRegs s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold fiosTop
  mcrun [h14, hs.ld (show dT + 8 + 8 ≤ Z by omega_arith), hs.st (show dT + 8 ≤ Z by omega_arith),
    hs.st (show dT + 8 + 8 ≤ Z by omega_arith)]
  have h := fios_top_arith (s.gpr .r18) (word s.mem B (dT + 8)) (s.gpr .r22)
  simp only [Nat.reducePow, word] at h ⊢
  exact ⟨_, _, rfl, h⟩

/-- `(w - 1) / 4` into `r16`. -/
theorem fiosQuot_ok {s : State} {w : Nat} (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) :
    WP isa (.block fiosQuot) s fun s' =>
      (s'.gpr .r16 = BitVec.ofNat 64 ((w - 1) / 4) ∧ s'.mem = s.mem) ∧ Keep [.r16] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold fiosQuot
  prun [h11, mont_ofNat_shr1 (show w < 2 ^ 63 by omega_arith), ofNat_sub_one hw (by omega_arith), fios_quot (w - 1) (by omega_arith)]

/-- Two words stored at `d + 8 j`, `d + 8 j + 8`, above `j` words at `d`. -/
theorem fios_wordsVal_write2 (m : Mem) (B : Addr) (d j : Nat) (v v' : BitVec 64) (h : d + 8 * j + 16 ≤ 2 ^ 64) :
    wordsVal ((m.writeW (off B (d + 8 * j)) v).writeW (off B (d + 8 * j + 8)) v') B d (j + 2) =
      wordsVal m B d j + 2 ^ (64 * j) * (v.toNat + 2 ^ 64 * v'.toNat) := by
  rw [show d + 8 * j + 8 = d + 8 * (j + 1) by omega_arith, fios_wordsVal_write_top _ _ _ _ _ (by omega_arith),
    fios_wordsVal_write_top _ _ _ _ _ (by omega_arith), Nat.mul_succ, Nat.pow_add]
  grind

/-- The sum of a round: `2⁶⁴ (W + P (c + t_w + d)) = T + aᵢ b + u m`, from that of
words `1` to `w - 1`, `W + P (c + d) = T' + aᵢ b' + u m' + C₀`, and of word 0,
`2⁶⁴ C₀ = t₀ + aᵢ b₀ + u m₀`. -/
theorem fios_round_sum {W T S M C₀ c d a u t0 b0 m0 tw x P : Nat}
    (e : W + P * (c + d) = T + a * S + u * M + C₀) (h0 : 2 ^ 64 * C₀ = t0 + a * b0 + u * m0)
    (hx : x = c + tw + d) :
    2 ^ 64 * (W + P * x) = t0 + 2 ^ 64 * (T + P * tw) + a * (b0 + 2 ^ 64 * S) + u * (m0 + 2 ^ 64 * M) := by
  subst hx
  grind

theorem fios_wordsVal_pred (m : Mem) (B : Addr) (d : Nat) {w : Nat} (hw : 1 ≤ w) :
    wordsVal m B d w = (word m B d).toNat + 2 ^ 64 * wordsVal m B (d + 8) (w - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega_arith⟩
  rfl

/-- The registers a round writes. -/
def roundRegs : List Reg := [.r0, .r3, .r6, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22]

/-- A round (`round`), for `aᵢ` at `da` (`r6`, advanced), `T` (`w + 1` words)
at `dA`, `b` and `m` (`w` words) at `dB` and `dM`, `n = 2 w` in `r11` and
`-m⁻¹ mod 2³²` in `r12`: `2⁶⁴ T' = T + aᵢ b + u m` for some `u < 2⁶⁴`. -/
theorem round_ok {s : State} {B : Addr} {Z da dA dB dM w : Nat} (hs : Scr s B Z)
    (h6 : s.gpr .r6 = off B da) (h7 : s.gpr .r7 = off B dB) (h8 : s.gpr .r8 = off B dA)
    (h10 : s.gpr .r10 = off B dM) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hinv : ((word s.mem B dM).toNat % 2 ^ 32 * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (ha : da + 8 ≤ Z) (hA : dA + 8 * (w + 1) ≤ Z) (hB : dB + 8 * w ≤ Z) (hM : dM + 8 * w ≤ Z)
    (dBA : dB + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ dB) (dMA : dM + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ dM) :
    WP isa round s fun s' =>
      (s'.gpr .r6 = off B (da + 8) ∧ Outside B dA (8 * (w + 1)) s.mem s'.mem ∧
        ∃ u < 2 ^ 64, 2 ^ 64 * wordsVal s'.mem B dA (w + 1) =
          wordsVal s.mem B dA (w + 1) + (word s.mem B da).toNat * wordsVal s.mem B dB w +
            u * wordsVal s.mem B dM w) ∧
      Keep roundRegs s s' := by
  have hnw := hs.nowrap
  have hK := Nat.mod_add_div (w - 1) 4
  generalize hN₁ : (w - 1) % 4 = N₁ at hK
  generalize hN₂ : (w - 1) / 4 = N₂ at hK
  have hN₁4 : N₁ < 4 := hN₁ ▸ Nat.mod_lt _ (by decide)
  unfold round
  -- Word 0.
  refine WP.seq (WP.mono (fiosHead_ok hs h6 h7 h8 h10 h11 hinv hw hw' ha (by omega_arith) (by omega_arith) (by omega_arith))
    fun s₁ ⟨⟨i17, i6, i14, i15, i3, i16, im, i0⟩, k₁⟩ => ?_)
  rw [hN₁] at i16
  -- Words `1` to `N₁`, one at a time.
  refine WP.seq (WP.mono (fiosLoop?_ok (U := 1) (N := N₁) (by decide) (hs.congr k₁.wr) i14 i15 i3 i16 (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)) fun s₂ ⟨j14, j15, j3, jout, jeq, k₂⟩ => ?_)
  rw [Nat.one_mul] at j14 j15 j3 jout jeq
  have g₂ : ∀ r ∈ [Reg.r6, .r11, .r17, .r0], s₂.gpr r = s₁.gpr r := fun r hr => k₂.gpr r (by revert r hr; decide)
  have g₁ : s₁.gpr .r11 = s.gpr .r11 := k₁.gpr _ (by decide)
  -- The count of groups of four.
  refine WP.seq (WP.mono (fiosQuot_ok (s := s₂) (w := w) (by rw [g₂ .r11 (by decide), g₁, h11]) hw hw')
    fun s₃ ⟨⟨l16, lm⟩, k₃⟩ => ?_)
  rw [hN₂] at l16
  have g₃ : ∀ r ∈ [Reg.r0, .r3, .r6, .r14, .r15, .r17, .r18, .r22], s₃.gpr r = s₂.gpr r := fun r hr =>
    k₃.gpr r (by revert r hr; decide)
  -- Words `N₁ + 1` to `w - 1`, four at a time.
  refine WP.seq (WP.mono (fiosLoop?_ok (U := 4) (N := N₂) (dT := dA + 8 * N₁) (dB := dB + 8 * N₁)
    (dM := dM + 8 * N₁) (by decide) (hs.congr (k₁.trans (k₂.trans k₃)).wr) (by rw [g₃ .r14 (by decide), j14])
    (by rw [g₃ .r15 (by decide), j15]) (by rw [g₃ .r3 (by decide), j3]) l16 (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith)) fun s₄ ⟨n14, _, _, nout, neq, k₄⟩ => ?_)
  -- Word `w` and the carries.
  refine WP.mono (fiosTop_ok (dT := dA + 8 * (w - 1)) (hs.congr (k₁.trans (k₂.trans (k₃.trans k₄))).wr)
    (by rw [n14, Nat.add_assoc, ← Nat.mul_add, show N₁ + 4 * N₂ = w - 1 by omega_arith]) (by omega_arith))
    fun s₅ ⟨⟨x, y, tm, txy⟩, k₅⟩ => ?_
  have k25 := k₂.trans (k₃.trans (k₄.trans k₅))
  have pK : 2 ^ (64 * N₁) * 2 ^ (64 * (4 * N₂)) = 2 ^ (64 * (w - 1)) := by
    rw [← Nat.pow_add, ← Nat.mul_add, hK]
  -- The memory outside `T` is that on entry.
  have o₄ : Outside B dA (8 * (w - 1)) s.mem s₄.mem := by
    rw [← im]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans (by rw [← lm]; exact nout.mono (by omega_arith) (by omega_arith))
  refine ⟨⟨by rw [k25.gpr _ (by decide), i6], ?_, (s₁.gpr .r0).toNat, (s₁.gpr .r0).isLt, ?_⟩,
    (k₁.trans k25).mono (by decide)⟩
  · rw [tm]
    exact (o₄.mono (Nat.le_refl _) (by omega_arith)).trans
      (((writeW_outside _ B _ (by omega_arith)).mono (by omega_arith) (by omega_arith)).trans
        ((writeW_outside _ B _ (by omega_arith)).mono (by omega_arith) (by omega_arith)))
  -- The words read by the second loop and the end are those on entry.
  have rd : ∀ d, (d + 8 * w ≤ dA ∨ dA + 8 * (w + 1) ≤ d ∨ d = dA) → d + 8 * w ≤ Z →
      wordsVal s₃.mem B (d + 8 * N₁ + 8) (4 * N₂) = wordsVal s.mem B (d + 8 + 8 * N₁) (4 * N₂) := by
    intro d hd hdZ
    rw [lm, show d + 8 * N₁ + 8 = d + 8 + 8 * N₁ by omega_arith, jout.wordsVal (by omega_arith) (by omega_arith), im]
  have tw : word s₄.mem B (dA + 8 * (w - 1) + 8) = word s.mem B (dA + 8 + 8 * (w - 1)) := by
    rw [o₄.word (by omega_arith) (by omega_arith), show dA + 8 * (w - 1) + 8 = dA + 8 + 8 * (w - 1) by omega_arith]
  rw [rd dA (.inr (.inr rfl)) (by omega_arith), rd dB (by omega_arith) hB, rd dM (by omega_arith) hM, g₃ .r0 (by decide),
    g₃ .r17 (by decide), g₃ .r18 (by decide), g₃ .r22 (by decide), g₂ .r0 (by decide), g₂ .r17 (by decide)] at neq
  rw [im] at jeq
  rw [tw] at txy
  have e := fios_sum_group jeq neq rfl
  rw [← fios_wordsVal_append, ← fios_wordsVal_append, ← fios_wordsVal_append, hK, pK] at e
  rw [show wordsVal s₂.mem B dA N₁ = wordsVal s₄.mem B dA N₁ by
      rw [← lm]; exact (nout.wordsVal (by omega_arith) (by omega_arith)).symm,
    ← fios_wordsVal_append, hK] at e
  rw [tm, show w + 1 = w - 1 + 2 by omega_arith, fios_wordsVal_write2 _ _ _ _ _ _ (by omega_arith),
    fios_wordsVal_pred s.mem B dA (show 1 ≤ w - 1 + 2 by omega_arith), show w - 1 + 2 - 1 = w - 1 + 1 by omega_arith,
    wordsVal_succ_top s.mem B (dA + 8) (w - 1), fios_wordsVal_pred s.mem B dB hw,
    fios_wordsVal_pred s.mem B dM hw]
  rw [i17] at e
  exact fios_round_sum e i0 txy

end VG.Proof.Bignum.PPC64LE

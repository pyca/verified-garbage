module

public import VerifiedGarbage.Proof.Bignum.RISCV64.MontFios
public import VerifiedGarbage.Proof.Bignum.RISCV64.MontFinish64
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Impl.Bignum.RISCV64.MontSqr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Montgomery squaring on RISC-V: the rows

`macSteps_ok`, `macLoop_ok`, `macRun_ok`: a row of `MontSqr.lean`'s
`sqrMac` steps, `T += x Y + c` over `K` words, unrolled by four with the rest
one at a time.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum.RISCV64

theorem sqrMac_writes (k : Nat) : writesOnly [.s1, .s2, .s3, .s4] (.block (sqrMac k)) = true := by
  rfl

/-- A step of a row: `T[k] + s0 Y[k] + s1`, its low word stored at `T[k]`
and its high word the carry `s1`. -/
theorem sqrMac_ok {s : State} {B : Addr} {Z dT dY k : Nat} (hs : Scr s B Z)
    (h4 : s.gpr .t4 = off B dT) (h0 : s.gpr .a0 = off B dY)
    (hk : k < 2048) (hk8 : k % 8 = 0) (hT8 : dT % 8 = 0) (hY8 : dY % 8 = 0)
    (hT : dT + k + 8 ≤ Z) (hY : dY + k + 8 ≤ Z) :
    WP isa (.block (sqrMac k)) s fun s' =>
      (∃ v : BitVec 64, s'.mem = s.mem.writeW (off B (dT + k)) v ∧
        v.toNat + 2 ^ 64 * (s'.gpr .s1).toNat =
          (word s.mem B (dT + k)).toNat + (s.gpr .s0).toNat * (word s.mem B (dY + k)).toNat +
            (s.gpr .s1).toNat) ∧ Keep [.s1, .s2, .s3, .s4] s s' := by
  refine WP.keep _ ?_ (sqrMac_writes k) (by rfl)
  unfold sqrMac
  brun [h4, h0, hk, hs.ld hT, hs.ld hY, hs.st hT, hs.al8 hT (by omega_arith), hs.al8 hY (by omega_arith)]
  refine ⟨_, rfl, ?_⟩
  have h1 := fios_chain (word s.mem B (dT + k)) (s.gpr .s0) (word s.mem B (dY + k)) (s.gpr .s1)
  simp only [Nat.reducePow, word] at h1 ⊢
  omega_arith

/-- The sum of `K + 1` steps, as the sum of the first `K` and the last. -/
theorem mac_sum_succ {W T S C₀ C₁ C₂ a v t b P : Nat}
    (e₁ : W + P * C₁ = T + a * S + C₀) (e₂ : v + 2 ^ 64 * C₂ = t + a * b + C₁) :
    W + P * v + 2 ^ 64 * P * C₂ = T + P * t + a * (S + P * b) + C₀ := by
  have e : P * v + 2 ^ 64 * P * C₂ = P * (t + a * b + C₁) := by
    rw [← e₂, Nat.mul_add, Nat.mul_comm (2 ^ 64) P, Nat.mul_assoc]
  grind

theorem macSteps_succ (K : Nat) :
    (List.range (K + 1)).flatMap (fun k => sqrMac (8 * k)) =
      (List.range K).flatMap (fun k => sqrMac (8 * k)) ++ sqrMac (8 * K) := by
  simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The registers the steps write. -/
def macRegs : List Reg := [.s1, .s2, .s3, .s4]

/-- `K` steps, the pointers `t4` and `a0` at `dT` and `dY`: the `K` words
stored at `dT` and the carry `s1` make up `T + x Y + c`, for the `K` words
`T`, `Y` at `dT`, `dY`, `x` in `s0` and the carry `c` in `s1` on entry. -/
theorem macSteps_ok {B : Addr} {Z dT dY : Nat} (hT8 : dT % 8 = 0) (hY8 : dY % 8 = 0) :
    ∀ (K : Nat) {s : State}, Scr s B Z →
    s.gpr .t4 = off B dT → s.gpr .a0 = off B dY → 8 * K ≤ 2048 →
    dT + 8 * K ≤ Z → dY + 8 * K ≤ Z → (dY + 8 * K ≤ dT ∨ dT + 8 * K ≤ dY) →
    WP isa (.block ((List.range K).flatMap fun k => sqrMac (8 * k))) s fun s' =>
      (Outside B dT (8 * K) s.mem s'.mem ∧
        wordsVal s'.mem B dT K + 2 ^ (64 * K) * (s'.gpr .s1).toNat =
          wordsVal s.mem B dT K + (s.gpr .s0).toNat * wordsVal s.mem B dY K + (s.gpr .s1).toNat) ∧
      Keep macRegs s s'
  | 0, s, _, _, _, _, _, _, _ => by
    simp only [List.range_zero, List.flatMap_nil]
    exact WP.block_nil ⟨⟨Outside.refl _ _ _ _, by simp [wordsVal]⟩, Keep.refl _ _⟩
  | K + 1, s, hs, h4, h0, hK, hT, hY, sY => by
    have hnw := hs.nowrap
    rw [macSteps_succ, WP.block_append_iff]
    refine WP.mono (macSteps_ok hT8 hY8 K hs h4 h0 (by omega_arith) (by omega_arith) (by omega_arith)
      (by omega_arith)) fun s₁ ⟨⟨o₁, e₁⟩, k₁⟩ => ?_
    have g : ∀ r ∈ [Reg.s0, .a0, .t4], s₁.gpr r = s.gpr r := fun r hr =>
      k₁.gpr (by revert r hr; decide)
    refine WP.mono (sqrMac_ok (dT := dT) (dY := dY) (k := 8 * K) (hs.congr k₁.2.2)
      (by rw [g .t4 (by decide), h4]) (by rw [g .a0 (by decide), h0])
      (by omega_arith) (by omega_arith) hT8 hY8 (by omega_arith) (by omega_arith))
      fun s₂ ⟨⟨v, m₂, e₂⟩, k₂⟩ => ⟨⟨?_, ?_⟩, (k₁.trans k₂).mono (by decide)⟩
    · rw [m₂]
      exact (o₁.mono (Nat.le_refl _) (by omega_arith)).trans
        ((writeW_outside _ B v (by omega_arith)).mono (by omega_arith) (by omega_arith))
    · -- The words read are those on entry.
      rw [o₁.word (by omega_arith) (by omega_arith), o₁.word (by omega_arith) (by omega_arith), g .s0 (by decide)] at e₂
      rw [m₂, fios_wordsVal_write_top _ _ _ _ _ (by omega_arith), wordsVal_succ_top s.mem B dT K,
        wordsVal_succ_top s.mem B dY K, pow64_succ]
      exact mac_sum_succ e₁ e₂

/-- The sum of a loop's iterations, as the sum of the first ones and the last. -/
theorem mac_sum_group {W T S C₀ C₁ C₂ a G T' S' P Q : Nat}
    (e₁ : W + P * C₁ = T + a * S + C₀) (e₂ : G + Q * C₂ = T' + a * S' + C₁) :
    W + P * G + P * Q * C₂ = T + P * T' + a * (S + P * S') + C₀ := by
  have e : P * G + P * Q * C₂ = P * (T' + a * S' + C₁) := by
    rw [← e₂, Nat.mul_add, Nat.mul_assoc]
  grind

/-- The registers a loop of steps counted by `cr` writes. -/
def macLoopRegs (cr : Reg) : List Reg := [.a0, .t4, cr, .s1, .s2, .s3, .s4]

/-- What `N` iterations of `U` steps leave, the pointers at offsets `dT`,
`dY` on entry: `macSteps_ok` for `U N` words, the pointers advanced past
them. -/
def MacPost (cr : Reg) (B : Addr) (dT dY K : Nat) (s₀ s : State) : Prop :=
  s.gpr .t4 = off B (dT + 8 * K) ∧ s.gpr .a0 = off B (dY + 8 * K) ∧
    Outside B dT (8 * K) s₀.mem s.mem ∧
    wordsVal s.mem B dT K + 2 ^ (64 * K) * (s.gpr .s1).toNat =
      wordsVal s₀.mem B dT K + (s₀.gpr .s0).toNat * wordsVal s₀.mem B dY K + (s₀.gpr .s1).toNat ∧
    Keep (macLoopRegs cr) s₀ s

theorem macPost_zero {cr : Reg} {B : Addr} {dT dY : Nat} {s : State} (h4 : s.gpr .t4 = off B dT)
    (h0 : s.gpr .a0 = off B dY) : MacPost cr B dT dY 0 s s :=
  ⟨by rw [h4]; rfl, by rw [h0]; rfl, Outside.refl _ _ _ _, by simp [wordsVal], Keep.refl _ _⟩

/-- `N > 0` iterations of `U` steps (`countLoop cr (macGroup U)`). -/
theorem macLoop_ok {cr : Reg} (hcr : cr ∉ [Reg.t4, .a0, .s0, .s1, .s2, .s3, .s4])
    {B : Addr} {Z dT dY U N : Nat} (hU : 8 * U < 2048) {s₀ : State} (hs : Scr s₀ B Z)
    (hT8 : dT % 8 = 0) (hY8 : dY % 8 = 0)
    (h4 : s₀.gpr .t4 = off B dT) (h0 : s₀.gpr .a0 = off B dY)
    (hc : s₀.gpr cr = BitVec.ofNat 64 N) (hN : 1 ≤ N) (hN' : N < 2 ^ 32)
    (hT : dT + 8 * (U * N) ≤ Z) (hY : dY + 8 * (U * N) ≤ Z)
    (sY : dY + 8 * (U * N) ≤ dT ∨ dT + 8 * (U * N) ≤ dY) :
    WP isa (countLoop cr (macGroup U)) s₀ (MacPost cr B dT dY (U * N) s₀) := by
  have hnw := hs.nowrap
  have hc4 : cr ≠ .t4 := fun h => hcr (by simp [h])
  have hc0 : cr ≠ .a0 := fun h => hcr (by simp [h])
  refine wp_countdown (body := .block (macGroup U ++ ([.addi cr cr (-1)] : List Instr))) (cnt := cr)
    (N := N) (by omega_arith) (by omega_arith) (fun i s => MacPost cr B dT dY (U * i) s₀ s)
    (fun i hi s hI hc => ?_) (macPost_zero h4 h0) hc
  obtain ⟨i4, i0, iout, ieq, ik⟩ := hI
  have hUi : U * i + U ≤ U * N := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  have g : s.gpr .s0 = s₀.gpr .s0 := ik.gpr (by simp [macLoopRegs]; exact fun h => hcr (by simp [h]))
  rw [macGroup, List.append_assoc, WP.block_append_iff]
  refine WP.mono (macSteps_ok (show (dT + 8 * (U * i)) % 8 = 0 by omega_arith)
    (show (dY + 8 * (U * i)) % 8 = 0 by omega_arith)
    U (hs.congr ik.2.2) i4 i0 (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
    fun s₁ ⟨⟨o₁, e₁⟩, k₁⟩ => ?_
  have g₁ : ∀ r ∈ [Reg.a0, .t4, cr], s₁.gpr r = s.gpr r := fun r hr =>
    k₁.gpr (by simp only [macRegs]; simp at hr; rcases hr with rfl | rfl | rfl <;> simp_all)
  have hst : WP isa (.block [.addi .t4 .t4 ((8 * U : Nat) : Int), .addi .a0 .a0 ((8 * U : Nat) : Int),
      .addi cr cr (-1)]) s₁ fun s₂ =>
      s₂ = ((s₁.write .t4 (off B (dT + 8 * (U * i) + 8 * U))).write .a0 (off B (dY + 8 * (U * i) + 8 * U))).write
        cr (s₁.gpr cr - BitVec.ofNat 64 1) := by
    brun [g₁ .t4 (by simp), g₁ .a0 (by simp), i4, i0, hU, hc4, hc0, Ne.symm hc4, Ne.symm hc0]
  refine WP.mono hst fun s₂ e => ?_
  subst e
  have pU : U * (i + 1) = U * i + U := Nat.mul_succ _ _
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, by gsimp; rw [g₁ cr (by simp)]⟩
  · gsimp; simp only [Ne.symm hc4, ite_false]; rw [pU, Nat.mul_add, Nat.add_assoc]
  · gsimp; simp only [Ne.symm hc0, ite_false]; rw [pU, Nat.mul_add, Nat.add_assoc]
  · gsimp
    exact (iout.mono (Nat.le_refl _) (by omega_arith)).trans (o₁.mono (by omega_arith) (by omega_arith))
  · have hs1 : ((((s₁.write .t4 (off B (dT + 8 * (U * i) + 8 * U))).write .a0
        (off B (dY + 8 * (U * i) + 8 * U))).write cr (s₁.gpr cr - BitVec.ofNat 64 1)).gpr .s1) = s₁.gpr .s1 := by
      gsimp; have : ¬ Reg.s1 = cr := fun h => hcr (by simp [← h]); simp only [this, ite_false]
    have hm : ((((s₁.write .t4 (off B (dT + 8 * (U * i) + 8 * U))).write .a0
        (off B (dY + 8 * (U * i) + 8 * U))).write cr (s₁.gpr cr - BitVec.ofNat 64 1)).mem) = s₁.mem := by gsimp
    rw [hs1, hm]
    -- The words read are those on entry.
    have rY : wordsVal s.mem B (dY + 8 * (U * i)) U = wordsVal s₀.mem B (dY + 8 * (U * i)) U :=
      iout.wordsVal (by omega_arith) (by omega_arith)
    rw [rY, g] at e₁
    rw [iout.wordsVal (o := dT) (n := 8 * (U * i)) (by omega_arith) (by omega_arith)] at e₁
    rw [pU, fios_wordsVal_append s₁.mem B dT (U * i) U, fios_wordsVal_append s₀.mem B dT (U * i) U,
      fios_wordsVal_append s₀.mem B dY (U * i) U,
      show 64 * (U * i + U) = 64 * (U * i) + 64 * U by omega_arith, Nat.pow_add,
      (o₁.wordsVal (o := dT + 8 * (U * i)) (n := 8 * U) (d := dT) (k := U * i) (by omega_arith) (by omega_arith))]
    exact mac_sum_group ieq e₁
  · exact Keep.trans' ik (Keep.trans' (k₁.mono (by simp [macRegs, macLoopRegs])) (Keep.mono (by
      exact ((Keep.write _ _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _))
      (by simp [macLoopRegs])))

/-- `N` iterations of `U` steps if `N ≠ 0` (`countLoopR? cr (macGroup U)`). -/
theorem macLoop?_ok {cr : Reg} (hcr : cr ∉ [Reg.t4, .a0, .s0, .s1, .s2, .s3, .s4])
    {B : Addr} {Z dT dY U N : Nat} (hU : 8 * U < 2048) {s₀ : State} (hs : Scr s₀ B Z)
    (hT8 : dT % 8 = 0) (hY8 : dY % 8 = 0)
    (h4 : s₀.gpr .t4 = off B dT) (h0 : s₀.gpr .a0 = off B dY)
    (hc : s₀.gpr cr = BitVec.ofNat 64 N) (hN' : N < 2 ^ 32)
    (hT : dT + 8 * (U * N) ≤ Z) (hY : dY + 8 * (U * N) ≤ Z)
    (sY : dY + 8 * (U * N) ≤ dT ∨ dT + 8 * (U * N) ≤ dY) :
    WP isa (countLoopR? cr (macGroup U)) s₀ (MacPost cr B dT dY (U * N) s₀) := by
  refine WP.ite _ (Steps.eval_zero_ofNat _ _ (by omega_arith) hc) (fun hz => ?_) (fun hz => ?_)
  · have hN : N = 0 := of_decide_eq_true hz
    subst hN
    exact WP.block_nil (macPost_zero h4 h0)
  · exact macLoop_ok hcr hU hs hT8 hY8 h4 h0 hc (Nat.pos_of_ne_zero (of_decide_eq_false hz)) hN' hT hY sY

/-- The registers a row writes. -/
def macRunRegs : List Reg := [.a0, .t4, .t5, .t6, .s1, .s2, .s3, .s4]

/-- A row of `K` steps (`macRun`, `K` in `t5`), the pointers `t4`, `a0` at
`dT`, `dY`: the `K` words at `dT` and the carry `s1` make up `T + x Y + c`,
the pointers advanced past them. -/
theorem macRun_ok {B : Addr} {Z dT dY K : Nat} {s : State} (hs : Scr s B Z)
    (hT8 : dT % 8 = 0) (hY8 : dY % 8 = 0)
    (h4 : s.gpr .t4 = off B dT) (h0 : s.gpr .a0 = off B dY)
    (h5 : s.gpr .t5 = BitVec.ofNat 64 K) (hK : K < 2 ^ 32)
    (hT : dT + 8 * K ≤ Z) (hY : dY + 8 * K ≤ Z) (sY : dY + 8 * K ≤ dT ∨ dT + 8 * K ≤ dY) :
    WP isa macRun s fun t =>
      (t.gpr .t4 = off B (dT + 8 * K) ∧ t.gpr .a0 = off B (dY + 8 * K) ∧
        Outside B dT (8 * K) s.mem t.mem ∧
        wordsVal t.mem B dT K + 2 ^ (64 * K) * (t.gpr .s1).toNat =
          wordsVal s.mem B dT K + (s.gpr .s0).toNat * wordsVal s.mem B dY K + (s.gpr .s1).toNat) ∧
      Keep macRunRegs s t := by
  have hnw := hs.nowrap
  have hKd := Nat.mod_add_div K 4
  generalize hN₁ : K % 4 = N₁ at hKd
  generalize hN₂ : K / 4 = N₂ at hKd
  unfold macRun
  have hpre : WP isa (.block [.logicImm .and .t6 .t5 3, .shift .srl .d .t5 .t5 2]) s fun s₁ =>
      (s₁.gpr .t6 = BitVec.ofNat 64 N₁ ∧ s₁.gpr .t5 = BitVec.ofNat 64 N₂ ∧ s₁.mem = s.mem) ∧
        Keep [.t5, .t6] s s₁ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h5, fios_rem K (by omega_arith), fios_quot K (by omega_arith), hN₁, hN₂]
  refine WP.seq (WP.mono hpre fun s₁ ⟨⟨i6, i5, im⟩, k₁⟩ => ?_)
  have g₁ : ∀ r ∈ [Reg.t4, .a0, .s0, .s1], s₁.gpr r = s.gpr r := fun r hr => k₁.gpr (by revert r hr; decide)
  refine WP.seq (WP.mono (macLoop?_ok (cr := .t5) (by decide) (U := 4) (N := N₂) (by decide) (hs.congr k₁.2.2)
    hT8 hY8 (by rw [g₁ .t4 (by decide), h4]) (by rw [g₁ .a0 (by decide), h0]) i5 (by omega_arith)
    (by omega_arith) (by omega_arith) (by omega_arith)) fun s₂ ⟨j4, j0, jout, jeq, k₂⟩ => ?_)
  have g₂ : s₂.gpr .t6 = s₁.gpr .t6 := k₂.gpr (by decide)
  have g₂' : s₂.gpr .s0 = s₁.gpr .s0 := k₂.gpr (by decide)
  refine WP.mono (macLoop?_ok (cr := .t6) (by decide) (U := 1) (N := N₁) (by decide) (hs.congr (k₁.trans k₂).2.2)
    (dT := dT + 8 * (4 * N₂)) (dY := dY + 8 * (4 * N₂)) (by omega_arith) (by omega_arith) j4 j0
    (by rw [g₂, i6]) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith))
    fun t ⟨n4, n0, nout, neq, k₃⟩ => ⟨⟨?_, ?_, ?_, ?_⟩, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  · rw [n4, Nat.one_mul, Nat.add_assoc, ← Nat.mul_add]; congr 2; omega_arith
  · rw [n0, Nat.one_mul, Nat.add_assoc, ← Nat.mul_add]; congr 2; omega_arith
  · rw [← im]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans (nout.mono (by omega_arith) (by omega_arith))
  · rw [Nat.one_mul] at neq
    rw [im, g₁ .s0 (by decide), g₁ .s1 (by decide)] at jeq
    have rY : wordsVal s₂.mem B (dY + 8 * (4 * N₂)) N₁ = wordsVal s.mem B (dY + 8 * (4 * N₂)) N₁ := by
      rw [← im]; exact jout.wordsVal (by omega_arith) (by omega_arith)
    have rT : wordsVal s₂.mem B (dT + 8 * (4 * N₂)) N₁ = wordsVal s.mem B (dT + 8 * (4 * N₂)) N₁ := by
      rw [← im]; exact jout.wordsVal (by omega_arith) (by omega_arith)
    rw [rY, rT, g₂', k₁.gpr (r := .s0) (by decide)] at neq
    have e := mac_sum_group jeq neq
    rw [← fios_wordsVal_append, ← fios_wordsVal_append, show 4 * N₂ + N₁ = K by omega_arith,
      ← Nat.pow_add, ← Nat.mul_add, show 4 * N₂ + N₁ = K by omega_arith] at e
    rw [show wordsVal s₂.mem B dT (4 * N₂) = wordsVal t.mem B dT (4 * N₂) by
      exact (nout.wordsVal (by omega_arith) (by omega_arith)).symm, ← fios_wordsVal_append,
      show 4 * N₂ + N₁ = K by omega_arith] at e
    exact e

/-! ## The square as cross products and squares of words -/

/-- The first `i` rows of the cross products of the `w` words at `d`: row `r`
is `a_r (a_{r+1} … a_{w-1}) 2^(64 (2 r + 1))`. -/
def crossPart (m : Mem) (B : Addr) (d w : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => crossPart m B d w i +
      2 ^ (64 * (2 * i + 1)) * ((word m B (d + 8 * i)).toNat * wordsVal m B (d + 8 * (i + 1)) (w - 1 - i))

/-- The squares of the first `i` words at `d`: `Σ a_r² 2^(128 r)`. -/
def diagPart (m : Mem) (B : Addr) (d : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => diagPart m B d i + 2 ^ (128 * i) * ((word m B (d + 8 * i)).toNat * (word m B (d + 8 * i)).toNat)

theorem crossPart_shift (m : Mem) (B : Addr) (d w : Nat) : ∀ i, i ≤ w →
    crossPart m B d (w + 1) (i + 1) =
      2 ^ 64 * ((word m B d).toNat * wordsVal m B (d + 8) w) + 2 ^ 128 * crossPart m B (d + 8) w i
  | 0, _ => by simp [crossPart]
  | i + 1, hi => by
    rw [crossPart, crossPart_shift m B d w i (by omega_arith), crossPart,
      show d + 8 * (i + 1) = d + 8 + 8 * i by omega_arith,
      show d + 8 * (i + 1 + 1) = d + 8 + 8 * (i + 1) by omega_arith,
      show w + 1 - 1 - (i + 1) = w - 1 - i by omega_arith,
      show 64 * (2 * (i + 1) + 1) = 128 + 64 * (2 * i + 1) by omega_arith, Nat.pow_add]
    grind

theorem diagPart_shift (m : Mem) (B : Addr) (d : Nat) : ∀ i,
    diagPart m B d (i + 1) =
      (word m B d).toNat * (word m B d).toNat + 2 ^ 128 * diagPart m B (d + 8) i
  | 0 => by simp [diagPart]
  | i + 1 => by
    rw [diagPart, diagPart_shift m B d i, diagPart, show d + 8 * (i + 1) = d + 8 + 8 * i by omega_arith,
      show 128 * (i + 1) = 128 + 128 * i by omega_arith, Nat.pow_add]
    grind

/-- The square of the `w` words at `d`: its squares of words and twice its
cross products. -/
theorem sq_parts (m : Mem) (B : Addr) : ∀ (d w : Nat),
    wordsVal m B d w * wordsVal m B d w = diagPart m B d w + 2 * crossPart m B d w w
  | _, 0 => by simp [wordsVal, diagPart, crossPart]
  | d, w + 1 => by
    rw [diagPart_shift, crossPart_shift m B d w w (Nat.le_refl _)]
    have ih := (sq_parts m B (d + 8) w).symm
    simp only [wordsVal]
    generalize wordsVal m B (d + 8) w = P at ih ⊢
    generalize (word m B d).toNat = a
    generalize diagPart m B (d + 8) w = D at ih ⊢
    generalize crossPart m B (d + 8) w w = C at ih ⊢
    have e : 2 ^ 128 * D + 2 * (2 ^ 128 * C) = 2 ^ 128 * (P * P) := by rw [← ih]; grind
    grind

/-- The last row has no products. -/
theorem crossPart_last (m : Mem) (B : Addr) (d w : Nat) (hw : 1 ≤ w) :
    crossPart m B d w w = crossPart m B d w (w - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega_arith⟩
  simp [crossPart, wordsVal]

/-! ## `T := 0` -/

theorem ofNat_dbl2 (w : Nat) : off (BitVec.ofNat 64 w) (w + 2) = BitVec.ofNat 64 (2 * w + 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega_arith

/-- `zeroT`, with `w` in `t0` and `T` at `dT` (`a5`): its `2 w + 2` words 0. -/
theorem zeroT_ok {s : State} {B : Addr} {Z dT w : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .a5 = off B dT) (h0 : s.gpr .t0 = BitVec.ofNat 64 w) (hT8 : dT % 8 = 0)
    (hw : w < 2 ^ 31) (hT : dT + 8 * (2 * w + 2) ≤ Z) :
    WP isa zeroT s fun s' =>
      wordsVal s'.mem B dT (2 * w + 2) = 0 ∧ Outside B dT (8 * (2 * w + 2)) s.mem s'.mem ∧
        Keep [.t3, .t5, .s0] s s' := by
  have hnw := hs.nowrap
  unfold zeroT
  refine WP.seq ?_
  have hpre : WP isa (.block [.addi .t3 .a5 0, .add .t5 .t0 .t0, .addi .t5 .t5 2, .li .s0 0]) s
      fun s₁ => (s₁.gpr .t3 = off B dT ∧ s₁.gpr .t5 = BitVec.ofNat 64 (2 * w + 2) ∧ s₁.gpr .s0 = 0 ∧
        s₁.mem = s.mem) ∧ Keep [.t3, .t5, .s0] s s₁ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [fin64_exec_li_zero, h5, h0, BitVec.add_zero, ofNat_dbl2]
  refine WP.mono hpre fun s₁ ⟨⟨i3, i5, i0, im⟩, k₁⟩ => ?_
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = off B (dT + 8 * i) ∧ t.gpr .s0 = 0 ∧ Outside B dT (8 * i) s.mem t.mem ∧
      wordsVal t.mem B dT i = 0 ∧ Keep [.t3, .t5] s₁ t
  refine WP.mono (wp_countdown (body := .block ([.store .d .s0 .t3 0, .addi .t3 .t3 8] ++
      ([.addi .t5 .t5 (-1)] : List Instr))) (cnt := .t5) (N := 2 * w + 2) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨j3, j0, jout, jz, jk⟩ hc => ?_)
    ⟨by rw [i3]; rfl, i0, by rw [← im]; exact Outside.refl _ _ _ _, rfl, Keep.refl _ _⟩ i5)
    fun t ⟨_, _, tout, tz, tk⟩ => ⟨tz, tout, (k₁.trans tk).mono (by decide)⟩
  have hs' := hs.congr (k₁.trans jk).2.2
  have hst : WP isa (.block [.store .d .s0 .t3 0, .addi .t3 .t3 8, .addi .t5 .t5 (-1)]) t
      fun t' => t' = ((({ t with mem := t.mem.writeW (off B (dT + 8 * i)) (0 : BitVec 64) } : State).write
        .t3 (off B (dT + 8 * i + 8))).write .t5 (t.gpr .t5 - BitVec.ofNat 64 1)) := by
    brun [j3, j0, hs'.st (show dT + 8 * i + 8 ≤ Z by omega_arith),
      hs'.al8 (show dT + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
  refine WP.mono hst fun t' e => ?_
  subst e
  refine ⟨⟨by gsimp; rw [show dT + 8 * i + 8 = dT + 8 * (i + 1) by omega_arith], by gsimp; exact j0, ?_, ?_, ?_⟩,
    by gsimp⟩
  · gsimp
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW_outside t.mem B (d := dT + 8 * i) 0 (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · gsimp
    rw [fios_wordsVal_write_top _ _ _ _ _ (by omega_arith), jz]
    rfl
  · exact Keep.trans' jk ((((Keep.mem _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono (by decide))

/-! ## The cross products -/

/-- `L + K + 1 + R` words: the low `L`, the middle `K`, a word and the rest. -/
theorem wordsVal_seg (m : Mem) (B : Addr) (d L K R : Nat) :
    wordsVal m B d (L + K + 1 + R) = wordsVal m B d L + 2 ^ (64 * L) * (wordsVal m B (d + 8 * L) K +
      2 ^ (64 * K) * ((word m B (d + 8 * (L + K))).toNat + 2 ^ 64 * wordsVal m B (d + 8 * (L + K + 1)) R)) := by
  rw [show L + K + 1 + R = L + (K + (R + 1)) by omega_arith, fios_wordsVal_append, fios_wordsVal_append,
    show R + 1 = 0 + (R + 1) by omega_arith, Nat.zero_add, wordsVal,
    show d + 8 * L + 8 * K = d + 8 * (L + K) by omega_arith,
    show d + 8 * (L + K) + 8 = d + 8 * (L + K + 1) by omega_arith]

/-- The registers `cross` writes. -/
def crossRegs : List Reg := [.a0, .a1, .t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4]

/-- `cross`, `a` (`w` words) at `dA` (`a3`), `T` (`2 w + 2` words, 0) at `dT`
(`a5`): `T` the cross products of `a`, `crossPart … (w - 1)`. -/
theorem cross_ok {s₀ : State} {B : Addr} {Z dA dT w : Nat} (hs : Scr s₀ B Z)
    (hA8 : dA % 8 = 0) (hT8 : dT % 8 = 0)
    (h3 : s₀.gpr .a3 = off B dA) (h5 : s₀.gpr .a5 = off B dT) (ht0 : s₀.gpr .t0 = BitVec.ofNat 64 w)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hA : dA + 8 * w ≤ Z) (hT : dT + 8 * (2 * w + 2) ≤ Z)
    (dAT : dA + 8 * w ≤ dT ∨ dT + 8 * (2 * w + 2) ≤ dA) (hz : wordsVal s₀.mem B dT (2 * w + 2) = 0) :
    WP isa cross s₀ fun s =>
      (wordsVal s.mem B dT (2 * w + 2) = crossPart s₀.mem B dA w (w - 1) ∧
        Outside B dT (8 * (2 * w + 2)) s₀.mem s.mem) ∧ Keep crossRegs s₀ s := by
  have hnw := hs.nowrap
  unfold cross
  have hpre : WP isa (.block [.addi .t3 .a3 0, .addi .a1 .t0 (-1), .addi .t2 .a5 8]) s₀ fun s₁ =>
      (s₁.gpr .t3 = off B dA ∧ s₁.gpr .a1 = BitVec.ofNat 64 (w - 1) ∧ s₁.gpr .t2 = off B (dT + 8 * (2 * 0 + 1)) ∧
        s₁.mem = s₀.mem) ∧ Keep [.t3, .a1, .t2] s₀ s₁ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [h3, h5, ht0, BitVec.add_zero, ofNat_sub_one (show 1 ≤ w by omega_arith) (by omega_arith)]
  refine WP.seq (WP.mono hpre fun s₁ ⟨⟨i3, i1, i2, im⟩, k₁⟩ => ?_)
  let J : Nat → State → Prop := fun i s =>
    s.gpr .t3 = off B (dA + 8 * i) ∧ s.gpr .t2 = off B (dT + 8 * (2 * i + 1)) ∧
      Outside B dT (8 * (2 * w + 2)) s₀.mem s.mem ∧
      wordsVal s.mem B dT (2 * w + 2) = crossPart s₀.mem B dA w i ∧
      wordsVal s.mem B (dT + 8 * (i + w)) (w + 2 - i) = 0 ∧ Keep crossRegs s₀ s
  have hJ0 : J 0 s₁ := by
    refine ⟨by rw [i3]; rfl, i2, by rw [im]; exact Outside.refl _ _ _ _, by rw [im, hz]; rfl, ?_,
      k₁.mono (by decide)⟩
    have e := fios_wordsVal_append s₀.mem B dT w (w + 2)
    rw [show w + (w + 2) = 2 * w + 2 by omega_arith, hz] at e
    rw [im, Nat.zero_add, Nat.sub_zero]
    have := Nat.two_pow_pos (64 * w)
    rcases Nat.eq_zero_or_pos (wordsVal s₀.mem B (dT + 8 * w) (w + 2)) with h | h
    · exact h
    · exfalso; have := Nat.mul_le_mul_left (2 ^ (64 * w)) h; omega_arith
  refine WP.mono (wp_countdown (body := .seq (.block [.load .d .s0 .t3 0, .li .s1 0, .addi .a0 .t3 8,
      .addi .t4 .t2 0, .addi .t5 .a1 0]) (.seq macRun (.block [.store .d .s1 .t4 0, .addi .t3 .t3 8,
      .addi .t2 .t2 16, .addi .a1 .a1 (-1)]))) (cnt := .a1) (N := w - 1) (by omega_arith) (by omega_arith) J
    (fun i hi s hJ hc => ?_) hJ0 i1) fun s ⟨_, _, jout, jv, _, jk⟩ => ⟨⟨jv, jout⟩, jk⟩
  obtain ⟨j3, j2, jout, jv, jz, jk⟩ := hJ
  have hsJ := hs.congr jk.2.2
  -- The start of row `i`.
  have hrp : WP isa (.block [.load .d .s0 .t3 0, .li .s1 0, .addi .a0 .t3 8, .addi .t4 .t2 0,
      .addi .t5 .a1 0]) s fun s₂ =>
      (s₂.gpr .s0 = word s.mem B (dA + 8 * i) ∧ s₂.gpr .s1 = 0 ∧ s₂.gpr .a0 = off B (dA + 8 * (i + 1)) ∧
        s₂.gpr .t4 = off B (dT + 8 * (2 * i + 1)) ∧ s₂.gpr .t5 = BitVec.ofNat 64 (w - 1 - i) ∧
        s₂.mem = s.mem) ∧ Keep [.s0, .s1, .a0, .t4, .t5] s s₂ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [fin64_exec_li_zero, j3, j2, hc, BitVec.add_zero, hsJ.ld (show dA + 8 * i + 8 ≤ Z by omega_arith),
      hsJ.al8 (show dA + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
      show dA + 8 * i + 8 = dA + 8 * (i + 1) by omega_arith]
  refine WP.seq (WP.mono hrp fun s₂ ⟨⟨l0, l1, la, l4, l5, lm⟩, k₂⟩ => ?_)
  -- The row.
  have hK : w - 1 - i < 2 ^ 32 := by omega_arith
  refine WP.seq (WP.mono (macRun_ok (dT := dT + 8 * (2 * i + 1)) (dY := dA + 8 * (i + 1)) (K := w - 1 - i)
    (hsJ.congr k₂.2.2) (by omega_arith) (by omega_arith) l4 la l5 hK (by omega_arith) (by omega_arith)
    (by omega_arith)) fun s₃ ⟨⟨n4, _, nout, neq⟩, k₃⟩ => ?_)
  -- Its carry, and the pointers.
  have g₃ : ∀ r ∈ [Reg.t3, .t2, .a1], s₃.gpr r = s.gpr r := fun r hr => by
    rw [k₃.gpr (by revert r hr; decide), k₂.gpr (by revert r hr; decide)]
  have hsK := hsJ.congr (k₂.trans k₃).2.2
  have dK : dT + 8 * (2 * i + 1) + 8 * (w - 1 - i) = dT + 8 * (i + w) := by omega_arith
  rw [dK] at n4
  have hst : WP isa (.block [.store .d .s1 .t4 0, .addi .t3 .t3 8, .addi .t2 .t2 16, .addi .a1 .a1 (-1)]) s₃
      fun t => t = ((({ s₃ with mem := s₃.mem.writeW (off B (dT + 8 * (i + w))) (s₃.gpr .s1) } : State).write
        .t3 (off B (dA + 8 * i + 8))).write .t2 (off B (dT + 8 * (2 * i + 1) + 16))).write .a1
          (s.gpr .a1 - BitVec.ofNat 64 1) := by
    brun [n4, g₃ .t3 (by decide), g₃ .t2 (by decide), g₃ .a1 (by decide), j3, j2,
      hsK.st (show dT + 8 * (i + w) + 8 ≤ Z by omega_arith),
      hsK.al8 (show dT + 8 * (i + w) + 8 ≤ Z by omega_arith) (by omega_arith)]
  refine WP.mono hst fun t e => ?_
  subst e
  have hm : ∀ x, ({ s₃ with mem := s₃.mem.writeW (off B (dT + 8 * (i + w))) (s₃.gpr .s1) } : State).mem x =
      (s₃.mem.writeW (off B (dT + 8 * (i + w))) (s₃.gpr .s1)) x := fun _ => rfl
  -- The memory, word by word.
  have outW : Outside B (dT + 8 * (i + w)) 8 s₃.mem (s₃.mem.writeW (off B (dT + 8 * (i + w))) (s₃.gpr .s1)) :=
    writeW_outside _ B _ (by omega_arith)
  have o₃ : Outside B (dT + 8 * (2 * i + 1)) (8 * (w - 1 - i)) s.mem s₃.mem := by rw [← lm]; exact nout
  refine ⟨⟨by gsimp; rw [show dA + 8 * i + 8 = dA + 8 * (i + 1) by omega_arith], by gsimp; rw [show dT + 8 * (2 * i + 1) + 16 = dT + 8 * (2 * (i + 1) + 1) by omega_arith],
    ?_, ?_, ?_, ?_⟩, by gsimp⟩
  · gsimp
    exact (jout.trans ((o₃.mono (by omega_arith) (by omega_arith)).trans (outW.mono (by omega_arith) (by omega_arith))))
  · gsimp
    -- The low words, the row, its carry and the rest.
    have hlen : 2 * w + 2 = (2 * i + 1) + (w - 1 - i) + 1 + (w + 1 - i) := by omega_arith
    rw [hlen, wordsVal_seg]
    rw [hlen, wordsVal_seg] at jv
    have eL : wordsVal (s₃.mem.writeW (off B (dT + 8 * (i + w))) (s₃.gpr .s1)) B dT (2 * i + 1) =
        wordsVal s.mem B dT (2 * i + 1) := by
      rw [outW.wordsVal (by omega_arith) (by omega_arith)]
      exact o₃.wordsVal (by omega_arith) (by omega_arith)
    have eM : wordsVal (s₃.mem.writeW (off B (dT + 8 * (i + w))) (s₃.gpr .s1)) B (dT + 8 * (2 * i + 1)) (w - 1 - i) =
        wordsVal s₃.mem B (dT + 8 * (2 * i + 1)) (w - 1 - i) :=
      outW.wordsVal (by omega_arith) (by omega_arith)
    have eW : word (s₃.mem.writeW (off B (dT + 8 * (i + w))) (s₃.gpr .s1)) B (dT + 8 * (2 * i + 1 + (w - 1 - i))) =
        s₃.gpr .s1 := by
      rw [show dT + 8 * (2 * i + 1 + (w - 1 - i)) = dT + 8 * (i + w) by omega_arith]; exact word_writeW_self _ _ _ _
    have eR : ∀ m' : Mem, Outside B (dT + 8 * (2 * i + 1)) (8 * (w - 1 - i) + 8) s.mem m' →
        wordsVal m' B (dT + 8 * (2 * i + 1 + (w - 1 - i) + 1)) (w + 1 - i) =
          wordsVal s.mem B (dT + 8 * (2 * i + 1 + (w - 1 - i) + 1)) (w + 1 - i) := fun m' h =>
      h.wordsVal (by omega_arith) (by omega_arith)
    have oA : Outside B (dT + 8 * (2 * i + 1)) (8 * (w - 1 - i) + 8) s.mem
        (s₃.mem.writeW (off B (dT + 8 * (i + w))) (s₃.gpr .s1)) :=
      (o₃.mono (Nat.le_refl _) (by omega_arith)).trans (outW.mono (by omega_arith) (by omega_arith))
    rw [eL, eM, eW, eR _ oA]
    -- On entry, word `i + w` and the rest are 0.
    have ez := jz
    rw [show w + 2 - i = 0 + 1 + (w + 1 - i) by omega_arith, show 0 + 1 + (w + 1 - i) = 1 + (w + 1 - i) by omega_arith,
      fios_wordsVal_append, show (1 : Nat) = 0 + 1 from rfl, wordsVal] at ez
    have zw : (word s.mem B (dT + 8 * (2 * i + 1 + (w - 1 - i)))).toNat = 0 := by
      rw [show dT + 8 * (2 * i + 1 + (w - 1 - i)) = dT + 8 * (i + w) by omega_arith]; simp [wordsVal] at ez; omega_arith
    have zr : wordsVal s.mem B (dT + 8 * (2 * i + 1 + (w - 1 - i) + 1)) (w + 1 - i) = 0 := by
      rw [show dT + 8 * (2 * i + 1 + (w - 1 - i) + 1) = dT + 8 * (i + w) + 8 * (0 + 1) by omega_arith]
      simp only [wordsVal, Nat.mul_zero, Nat.add_zero, Nat.zero_add] at ez
      rcases Nat.eq_zero_or_pos (wordsVal s.mem B (dT + 8 * (i + w) + 8 * 1) (w + 1 - i)) with h | h
      · exact h
      · exfalso; have := Nat.mul_le_mul_left (2 ^ 64) h; omega_arith
    rw [zw, zr] at jv
    rw [zr]
    -- The row's sum.
    rw [lm, l0, l1, jout.word (by omega_arith) (by omega_arith),
      jout.wordsVal (d := dA + 8 * (i + 1)) (by omega_arith) (by omega_arith)] at neq
    rw [crossPart, ← jv]
    have h0 : (0 : BitVec 64).toNat = 0 := rfl
    simp only [h0, Nat.mul_zero, Nat.add_zero] at neq ⊢
    generalize 2 ^ (64 * (2 * i + 1)) = P at ⊢
    generalize 2 ^ (64 * (w - 1 - i)) = Q at neq ⊢
    generalize wordsVal s₃.mem B (dT + 8 * (2 * i + 1)) (w - 1 - i) = M' at neq ⊢
    generalize (s₃.gpr Reg.s1).toNat = c at neq ⊢
    rw [Nat.add_assoc, ← Nat.mul_add, ← neq]
  · gsimp
    have oA : Outside B (dT + 8 * (2 * i + 1)) (8 * (w - 1 - i) + 8) s.mem
        (s₃.mem.writeW (off B (dT + 8 * (i + w))) (s₃.gpr .s1)) :=
      (o₃.mono (Nat.le_refl _) (by omega_arith)).trans (outW.mono (by omega_arith) (by omega_arith))
    rw [show dT + 8 * (i + 1 + w) = dT + 8 * (i + w) + 8 * 1 by omega_arith,
      show w + 2 - (i + 1) = w + 1 - i by omega_arith, oA.wordsVal (by omega_arith) (by omega_arith)]
    have ez := jz
    rw [show w + 2 - i = 1 + (w + 1 - i) by omega_arith, fios_wordsVal_append] at ez
    rcases Nat.eq_zero_or_pos (wordsVal s.mem B (dT + 8 * (i + w) + 8 * 1) (w + 1 - i)) with h | h
    · exact h
    · exfalso; have := Nat.mul_le_mul_left (2 ^ (64 * 1)) h; omega_arith
  · exact Keep.trans' jk (Keep.trans' (k₂.mono (by decide)) (Keep.trans' (k₃.mono (by decide))
      ((((Keep.mem _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans (Keep.write _ _ _) |>.mono
        (by decide))))

/-! ## Doubling and the squares of the words -/

/-- A word doubled, with a bit shifted in: the bit shifted out, times `2⁶⁴`. -/
theorem dbl_word (x b : BitVec 64) (hb : b.toNat ≤ 1) :
    (x <<< 1 + b).toNat + 2 ^ 64 * (x >>> 63).toNat = 2 * x.toNat + b.toNat := by
  have hx := x.isLt
  have e1 : (x <<< 1).toNat = 2 * x.toNat % 2 ^ 64 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]
  have e2 : (x >>> 63).toNat = x.toNat / 2 ^ 63 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [BitVec.toNat_add, e1, e2]
  omega_arith

theorem shr63_le (x : BitVec 64) : (x >>> 63).toNat ≤ 1 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega_arith

theorem carry_le (x y : BitVec 64) : (if x + y < y then (1 : BitVec 64) else 0).toNat ≤ 1 := by
  split <;> decide

/-- A step of `diag`: the pair `x₀ + 2⁶⁴ x₁` doubled, the bit `sh` shifted in
and the carry `c` and `a²` added, as two words, the bit shifted out and the
carry out. -/
theorem diag_arith (x0 x1 a sh c : BitVec 64) (hsh : sh.toNat ≤ 1) :
    (a * a + (c + (x0 <<< 1 + sh))).toNat +
      2 ^ 64 * (x1 <<< 1 + x0 >>> 63 + (BitVec.ofNat 64 (a.toNat * a.toNat / 2 ^ 64) +
        (if c + (x0 <<< 1 + sh) < x0 <<< 1 + sh then 1 else 0) +
        (if a * a + (c + (x0 <<< 1 + sh)) < c + (x0 <<< 1 + sh) then 1 else 0))).toNat +
      2 ^ 128 * ((x1 >>> 63).toNat + (if x1 <<< 1 + x0 >>> 63 + (BitVec.ofNat 64 (a.toNat * a.toNat / 2 ^ 64) +
        (if c + (x0 <<< 1 + sh) < x0 <<< 1 + sh then 1 else 0) +
        (if a * a + (c + (x0 <<< 1 + sh)) < c + (x0 <<< 1 + sh) then 1 else 0)) <
          BitVec.ofNat 64 (a.toNat * a.toNat / 2 ^ 64) +
        (if c + (x0 <<< 1 + sh) < x0 <<< 1 + sh then 1 else 0) +
        (if a * a + (c + (x0 <<< 1 + sh)) < c + (x0 <<< 1 + sh) then 1 else 0) then (1 : BitVec 64) else 0).toNat) =
      2 * (x0.toNat + 2 ^ 64 * x1.toNat) + sh.toNat + a.toNat * a.toNat + c.toNat := by
  have h0 := dbl_word x0 sh hsh
  have h1 := dbl_word x1 (x0 >>> 63) (shr63_le x0)
  have hc := fios_chain (x0 <<< 1 + sh) a a c
  generalize BitVec.ofNat 64 (a.toNat * a.toNat / 2 ^ 64) + (if c + (x0 <<< 1 + sh) < x0 <<< 1 + sh then 1 else 0) +
    (if a * a + (c + (x0 <<< 1 + sh)) < c + (x0 <<< 1 + sh) then 1 else 0) = h at hc ⊢
  have hz := carry_toNat (x1 <<< 1 + x0 >>> 63) h
  have hzs : (x1 <<< 1 + x0 >>> 63 + h).toNat + 2 ^ 64 * (decide (2 ^ 64 ≤ (x1 <<< 1 + x0 >>> 63).toNat + h.toNat)).toNat =
      (x1 <<< 1 + x0 >>> 63).toNat + h.toNat := by
    rw [BitVec.toNat_add]
    have := (x1 <<< 1 + x0 >>> 63).isLt
    have := h.isLt
    by_cases hh : 2 ^ 64 ≤ (x1 <<< 1 + x0 >>> 63).toNat + h.toNat <;>
      simp only [hh, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_arith
  rw [hz]
  omega_arith

/-- The registers `diag` writes. -/
def diagRegs : List Reg := [.a0, .t2, .t3, .t5, .s0, .s1, .s2, .s3, .s4]

/-- The sum of `diag`'s first `i + 1` steps, from that of the first `i` and
the last. -/
theorem diag_sum {L W D P z0 z1 x0 x1 sh c sh' c' a : Nat}
    (e₁ : L + P * (sh + c) = 2 * W + D)
    (e₂ : z0 + 2 ^ 64 * z1 + 2 ^ 128 * (sh' + c') = 2 * (x0 + 2 ^ 64 * x1) + sh + a + c) :
    L + P * (z0 + 2 ^ 64 * z1) + P * 2 ^ 128 * (sh' + c') = 2 * (W + P * (x0 + 2 ^ 64 * x1)) + (D + P * a) := by
  have e : P * (z0 + 2 ^ 64 * z1) + P * 2 ^ 128 * (sh' + c') = P * (2 * (x0 + 2 ^ 64 * x1) + sh + a + c) := by
    rw [← e₂]; grind
  grind

/-- `diag`, `a` (`w` words) at `dA` (`a3`), `T` at `dT` (`a5`): its first
`2 w` words doubled, plus the squares of `a`'s words, and the bit and the
carry out of them 0 but for their sum's top. -/
theorem diag_ok {s₀ : State} {B : Addr} {Z dA dT w : Nat} (hs : Scr s₀ B Z)
    (hA8 : dA % 8 = 0) (hT8 : dT % 8 = 0)
    (h3 : s₀.gpr .a3 = off B dA) (h5 : s₀.gpr .a5 = off B dT) (ht0 : s₀.gpr .t0 = BitVec.ofNat 64 w)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hA : dA + 8 * w ≤ Z) (hT : dT + 16 * w ≤ Z)
    (dAT : dA + 8 * w ≤ dT ∨ dT + 16 * w ≤ dA) :
    WP isa diag s₀ fun s =>
      (∃ e, wordsVal s.mem B dT (2 * w) + 2 ^ (128 * w) * e =
          2 * wordsVal s₀.mem B dT (2 * w) + diagPart s₀.mem B dA w) ∧
        Outside B dT (16 * w) s₀.mem s.mem ∧ Keep diagRegs s₀ s := by
  have hnw := hs.nowrap
  unfold diag
  have hpre : WP isa (.block [.addi .t3 .a5 0, .addi .a0 .a3 0, .addi .t5 .t0 0, .li .t2 0, .li .s1 0]) s₀
      fun s₁ => (s₁.gpr .t3 = off B dT ∧ s₁.gpr .a0 = off B dA ∧ s₁.gpr .t5 = BitVec.ofNat 64 w ∧
        s₁.gpr .t2 = 0 ∧ s₁.gpr .s1 = 0 ∧ s₁.mem = s₀.mem) ∧ Keep [.t3, .a0, .t5, .t2, .s1] s₀ s₁ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [fin64_exec_li_zero, h3, h5, ht0, BitVec.add_zero]
  refine WP.seq (WP.mono hpre fun s₁ ⟨⟨i3, i0, i5, i2, i1, im⟩, k₁⟩ => ?_)
  let J : Nat → State → Prop := fun i s =>
    s.gpr .t3 = off B (dT + 16 * i) ∧ s.gpr .a0 = off B (dA + 8 * i) ∧ (s.gpr .t2).toNat ≤ 1 ∧
      Outside B dT (16 * i) s₀.mem s.mem ∧
      wordsVal s.mem B dT (2 * i) + 2 ^ (128 * i) * ((s.gpr .t2).toNat + (s.gpr .s1).toNat) =
        2 * wordsVal s₀.mem B dT (2 * i) + diagPart s₀.mem B dA i ∧ Keep diagRegs s₀ s
  have hJ0 : J 0 s₁ := ⟨by rw [i3]; rfl, by rw [i0]; rfl, by rw [i2]; decide, by rw [im]; exact Outside.refl _ _ _ _,
    by rw [i2, i1]; simp [wordsVal, diagPart], k₁.mono (by decide)⟩
  refine WP.mono (wp_countdown (body := .block (diagStep ++ ([.addi .t5 .t5 (-1)] : List Instr))) (cnt := .t5)
    (N := w) (by omega_arith) (by omega_arith) J (fun i hi s hJ hc => ?_) hJ0 i5)
    fun s ⟨_, _, _, jout, jv, jk⟩ => ⟨⟨_, jv⟩, jout, jk⟩
  obtain ⟨j3, j0, j2, jout, jv, jk⟩ := hJ
  have hsJ := hs.congr jk.2.2
  have hst : WP isa (.block (diagStep ++ ([.addi .t5 .t5 (-1)] : List Instr))) s fun t =>
      (∃ z0 z1 : BitVec 64, t.mem = (s.mem.writeW (off B (dT + 16 * i)) z0).writeW (off B (dT + 16 * i + 8)) z1 ∧
        z0.toNat + 2 ^ 64 * z1.toNat + 2 ^ 128 * ((t.gpr .t2).toNat + (t.gpr .s1).toNat) =
          2 * ((word s.mem B (dT + 16 * i)).toNat + 2 ^ 64 * (word s.mem B (dT + 16 * i + 8)).toNat) +
            (s.gpr .t2).toNat + (word s.mem B (dA + 8 * i)).toNat * (word s.mem B (dA + 8 * i)).toNat +
            (s.gpr .s1).toNat ∧
        (t.gpr .t2).toNat ≤ 1 ∧ t.gpr .t3 = off B (dT + 16 * i + 16) ∧ t.gpr .a0 = off B (dA + 8 * i + 8) ∧
        t.gpr .t5 = s.gpr .t5 - BitVec.ofNat 64 1) ∧ Keep (diagRegs ++ [.t5]) s t := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    unfold diagStep
    brun [j3, j0, hsJ.ld (show dT + 16 * i + 8 ≤ Z by omega_arith),
      hsJ.ld (show dT + 16 * i + 8 + 8 ≤ Z by omega_arith), hsJ.ld (show dA + 8 * i + 8 ≤ Z by omega_arith),
      hsJ.st (show dT + 16 * i + 8 ≤ Z by omega_arith), hsJ.st (show dT + 16 * i + 8 + 8 ≤ Z by omega_arith),
      hsJ.al8 (show dT + 16 * i + 8 ≤ Z by omega_arith) (by omega_arith),
      hsJ.al8 (show dT + 16 * i + 8 + 8 ≤ Z by omega_arith) (by omega_arith),
      hsJ.al8 (show dA + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
    refine ⟨_, _, rfl, ?_, shr63_le _⟩
    have := diag_arith (word s.mem B (dT + 16 * i)) (word s.mem B (dT + 16 * i + 8)) (word s.mem B (dA + 8 * i))
      (s.gpr .t2) (s.gpr .s1) j2
    simp only [word] at this ⊢
    omega_arith
  refine WP.mono hst fun t ⟨⟨z0, z1, tm, teq, t2, t3, ta0, t5⟩, tk⟩ => ⟨⟨?_, ?_, t2, ?_, ?_, ?_⟩, t5⟩
  · rw [t3, show dT + 16 * i + 16 = dT + 16 * (i + 1) by omega_arith]
  · rw [ta0, show dA + 8 * i + 8 = dA + 8 * (i + 1) by omega_arith]
  · rw [tm]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      (((writeW_outside _ B _ (by omega_arith)).mono (by omega_arith) (by omega_arith)).trans
        ((writeW_outside _ B _ (by omega_arith)).mono (by omega_arith) (by omega_arith)))
  · -- The words read are those on entry.
    have w0 : word s.mem B (dT + 16 * i) = word s₀.mem B (dT + 16 * i) := jout.word (by omega_arith) (by omega_arith)
    have w1 : word s.mem B (dT + 16 * i + 8) = word s₀.mem B (dT + 16 * i + 8) :=
      jout.word (by omega_arith) (by omega_arith)
    have wa : word s.mem B (dA + 8 * i) = word s₀.mem B (dA + 8 * i) := jout.word (by omega_arith) (by omega_arith)
    rw [w0, w1, wa] at teq
    have hn : wordsVal t.mem B dT (2 * (i + 1)) = wordsVal s.mem B dT (2 * i) +
        2 ^ (64 * (2 * i)) * (z0.toNat + 2 ^ 64 * z1.toNat) := by
      rw [tm, show 2 * (i + 1) = 2 * i + 2 by omega_arith, show dT + 16 * i = dT + 8 * (2 * i) by omega_arith]
      exact fios_wordsVal_write2 _ _ _ _ _ _ (by omega_arith)
    have ho : wordsVal s₀.mem B dT (2 * (i + 1)) = wordsVal s₀.mem B dT (2 * i) +
        2 ^ (64 * (2 * i)) * ((word s₀.mem B (dT + 16 * i)).toNat + 2 ^ 64 * (word s₀.mem B (dT + 16 * i + 8)).toNat) := by
      rw [show 2 * (i + 1) = 2 * i + 2 by omega_arith, fios_wordsVal_append s₀.mem B dT (2 * i) 2]
      simp only [wordsVal, Nat.mul_zero, Nat.add_zero]
      rw [show dT + 8 * (2 * i) = dT + 16 * i by omega_arith]
    have hd : diagPart s₀.mem B dA (i + 1) = diagPart s₀.mem B dA i +
        2 ^ (64 * (2 * i)) * ((word s₀.mem B (dA + 8 * i)).toNat * (word s₀.mem B (dA + 8 * i)).toNat) := by
      rw [diagPart, show 128 * i = 64 * (2 * i) by omega_arith]
    have hQ : 2 ^ (128 * (i + 1)) = 2 ^ (64 * (2 * i)) * 2 ^ 128 := by
      rw [← Nat.pow_add]; congr 1; omega_arith
    rw [show 128 * i = 64 * (2 * i) by omega_arith] at jv
    rw [hn, ho, hd, hQ]
    exact diag_sum jv teq
  · exact Keep.trans' jk (tk.mono (by decide))

/-! ## The Montgomery reduction -/

/-- The end of a row: `c + x + top` as a word and the carry out. -/
theorem add3_arith (c x top : BitVec 64) :
    (c + x + top).toNat + 2 ^ 64 * ((if c + x < x then (1 : BitVec 64) else 0) +
      (if c + x + top < top then 1 else 0)).toNat = c.toNat + x.toNat + top.toNat := by
  have hc := c.isLt
  have hx := x.isLt
  have ht := top.isLt
  simp only [BitVec.toNat_add (if _ then _ else _), carry_toNat]
  simp only [BitVec.toNat_add]
  by_cases h1 : 2 ^ 64 ≤ c.toNat + x.toNat <;>
    by_cases h2 : 2 ^ 64 ≤ (c.toNat + x.toNat) % 2 ^ 64 + top.toNat <;>
    simp only [h1, h2, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_arith

/-- A row's low word is cleared: `t + u M ≡ 0 (mod 2⁶⁴)` for `u = t m' mod
2⁶⁴`, `M`'s low word `m₀` and `m₀ m' ≡ -1`. -/
theorem red_low {t minv m0 M : Nat} (hM : M % 2 ^ 64 = m0) (h : (m0 * minv + 1) % 2 ^ 64 = 0) :
    (t + t * minv % 2 ^ 64 * M) % 2 ^ 64 = 0 := by
  have hd := Nat.mod_add_div M (2 ^ 64)
  rw [hM] at hd
  have e : t + t * minv % 2 ^ 64 * M =
      (t + t * minv % 2 ^ 64 * m0) + 2 ^ 64 * (t * minv % 2 ^ 64 * (M / 2 ^ 64)) := by
    conv => lhs; rw [← hd]
    rw [Nat.mul_add, Nat.add_assoc, Nat.mul_left_comm]
  rw [e, Nat.add_mul_mod_self_left]
  exact mont_low t minv m0 h

/-- The registers `reduce` writes. -/
def redRegs : List Reg := [.a0, .a1, .t2, .t3, .t4, .t5, .t6, .s0, .s1, .s2, .s3, .s4]

/-- The sum of a row of the reduction. -/
theorem red_sum {L P Q mid mid' c x x' top top' R U uM A : Nat}
    (e₀ : L + P * (mid + Q * (x + 2 ^ 64 * R)) + P * Q * top = A + U)
    (e₁ : mid' + Q * c = mid + uM) (e₂ : x' + 2 ^ 64 * top' = c + x + top) :
    L + P * (mid' + Q * (x' + 2 ^ 64 * R)) + P * Q * 2 ^ 64 * top' = A + (U + P * uM) := by
  have h2 : P * Q * (x' + 2 ^ 64 * top') = P * Q * (c + x + top) := by rw [e₂]
  have h1 : P * (mid' + Q * c) = P * (mid + uM) := by rw [e₁]
  simp only [Nat.mul_add, Nat.mul_assoc] at h1 h2 e₀ ⊢
  omega_arith

/-- `reduce`, `T` (`2 w` words, `T < m²`) at `dT` (`a5`), `m` (`w` words) at
`dM` (`a7`), `-m⁻¹ mod 2⁶⁴` in `t1`: `T + U m = R (X)` for some `U < R`,
with `X` the words `w` to `2 w - 1` and `R` times the carry `a1`. -/
theorem reduce_ok {s₀ : State} {B : Addr} {Z dT dM w : Nat} (hs : Scr s₀ B Z)
    (hT8 : dT % 8 = 0) (hM8 : dM % 8 = 0)
    (h5 : s₀.gpr .a5 = off B dT) (h7 : s₀.gpr .a7 = off B dM) (ht0 : s₀.gpr .t0 = BitVec.ofNat 64 w)
    (hinv : ((word s₀.mem B dM).toNat * (s₀.gpr .t1).toNat + 1) % 2 ^ 64 = 0)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hM : dM + 8 * w ≤ Z) (hT : dT + 16 * w ≤ Z)
    (dMT : dM + 8 * w ≤ dT ∨ dT + 16 * w ≤ dM) :
    WP isa reduce s₀ fun s =>
      (wordsVal s.mem B dT w = 0 ∧
        ∃ U < 2 ^ (64 * w), wordsVal s.mem B dT (2 * w) + 2 ^ (64 * (2 * w)) * (s.gpr .a1).toNat =
          wordsVal s₀.mem B dT (2 * w) + U * wordsVal s₀.mem B dM w) ∧
        Outside B dT (16 * w) s₀.mem s.mem ∧ Keep redRegs s₀ s := by
  have hnw := hs.nowrap
  unfold reduce
  have hpre : WP isa (.block [.addi .t3 .a5 0, .addi .t2 .t0 0, .li .a1 0]) s₀ fun s₁ =>
      (s₁.gpr .t3 = off B dT ∧ s₁.gpr .t2 = BitVec.ofNat 64 w ∧ s₁.gpr .a1 = 0 ∧ s₁.mem = s₀.mem) ∧
        Keep [.t3, .t2, .a1] s₀ s₁ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [fin64_exec_li_zero, h5, ht0, BitVec.add_zero]
  refine WP.seq (WP.mono hpre fun s₁ ⟨⟨i3, i2, i1, im⟩, k₁⟩ => ?_)
  let M := wordsVal s₀.mem B dM w
  let J : Nat → State → Prop := fun i s =>
    s.gpr .t3 = off B (dT + 8 * i) ∧ Outside B dT (16 * w) s₀.mem s.mem ∧ wordsVal s.mem B dT i = 0 ∧
      (∃ U < 2 ^ (64 * i), wordsVal s.mem B dT (2 * w) + 2 ^ (64 * (i + w)) * (s.gpr .a1).toNat =
        wordsVal s₀.mem B dT (2 * w) + U * M) ∧ Keep redRegs s₀ s
  have hJ0 : J 0 s₁ := ⟨by rw [i3]; rfl, by rw [im]; exact Outside.refl _ _ _ _, rfl,
    ⟨0, by decide, by rw [i1, im]; simp⟩, k₁.mono (by decide)⟩
  refine WP.mono (wp_countdown (body := .seq (.block [.load .d .s0 .t3 0, .mul .s0 .s0 .t1, .li .s1 0,
      .addi .a0 .a7 0, .addi .t4 .t3 0, .addi .t5 .t0 0]) (.seq macRun (.block redTop))) (cnt := .t2) (N := w)
    (by omega_arith) (by omega_arith) J (fun i hi s hJ hc => ?_) hJ0 i2)
    fun s ⟨_, jout, jz, ⟨U, hU, jv⟩, jk⟩ => ⟨⟨jz, U, hU, by rw [show 2 * w = w + w by omega_arith] at jv ⊢; exact jv⟩,
      jout, jk⟩
  obtain ⟨j3, jout, jz, ⟨U, hU, jv⟩, jk⟩ := hJ
  have hsJ := hs.congr jk.2.2
  have g : ∀ r ∈ [Reg.a7, .t0, .t1], s.gpr r = s₀.gpr r := fun r hr => jk.gpr (by revert r hr; decide)
  -- The start of row `i`.
  have hrp : WP isa (.block [.load .d .s0 .t3 0, .mul .s0 .s0 .t1, .li .s1 0, .addi .a0 .a7 0, .addi .t4 .t3 0,
      .addi .t5 .t0 0]) s fun s₂ =>
      (s₂.gpr .s0 = word s.mem B (dT + 8 * i) * s₀.gpr .t1 ∧ s₂.gpr .s1 = 0 ∧ s₂.gpr .a0 = off B dM ∧
        s₂.gpr .t4 = off B (dT + 8 * i) ∧ s₂.gpr .t5 = BitVec.ofNat 64 w ∧ s₂.mem = s.mem) ∧
        Keep [.s0, .s1, .a0, .t4, .t5] s s₂ := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [fin64_exec_li_zero, j3, g .a7 (by decide), g .t0 (by decide), g .t1 (by decide), h7, ht0,
      BitVec.add_zero, hsJ.ld (show dT + 8 * i + 8 ≤ Z by omega_arith),
      hsJ.al8 (show dT + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
  refine WP.seq (WP.mono hrp fun s₂ ⟨⟨l0, l1, la, l4, l5, lm⟩, k₂⟩ => ?_)
  -- The row.
  refine WP.seq (WP.mono (macRun_ok (dT := dT + 8 * i) (dY := dM) (K := w) (hsJ.congr k₂.2.2) (by omega_arith) hM8
    l4 la l5 (by omega_arith) (by omega_arith) hM (by omega_arith)) fun s₃ ⟨⟨n4, _, nout, neq⟩, k₃⟩ => ?_)
  have g₃ : ∀ r ∈ [Reg.t3, .t2, .a1], s₃.gpr r = s.gpr r := fun r hr => by
    rw [k₃.gpr (by revert r hr; decide), k₂.gpr (by revert r hr; decide)]
  have hsK := hsJ.congr (k₂.trans k₃).2.2
  rw [show dT + 8 * i + 8 * w = dT + 8 * (i + w) by omega_arith] at n4
  -- Its end.
  have hrt : WP isa (.block redTop) s₃ fun t =>
      (∃ v : BitVec 64, t.mem = s₃.mem.writeW (off B (dT + 8 * (i + w))) v ∧
        v.toNat + 2 ^ 64 * (t.gpr .a1).toNat =
          (s₃.gpr .s1).toNat + (word s₃.mem B (dT + 8 * (i + w))).toNat + (s₃.gpr .a1).toNat) ∧
        t.gpr .t3 = off B (dT + 8 * i + 8) ∧ t.gpr .t2 = s₃.gpr .t2 - BitVec.ofNat 64 1 := by
    unfold redTop
    brun [n4, g₃ .t3 (by decide), j3, hsK.ld (show dT + 8 * (i + w) + 8 ≤ Z by omega_arith),
      hsK.st (show dT + 8 * (i + w) + 8 ≤ Z by omega_arith),
      hsK.al8 (show dT + 8 * (i + w) + 8 ≤ Z by omega_arith) (by omega_arith)]
    have := add3_arith (s₃.gpr .s1) (word s₃.mem B (dT + 8 * (i + w))) (s₃.gpr .a1)
    simp only [word] at this ⊢
    exact ⟨_, rfl, this⟩
  refine WP.mono (WP.keep [.a1, .t2, .t3, .s1, .s2, .s3] hrt (by rfl) (by rfl)) fun t ⟨⟨⟨v, tm, tv⟩, t3, t2⟩, tk⟩ => ?_
  -- The memory: the row's words and word `i + w` changed.
  have o₃ : Outside B (dT + 8 * i) (8 * w) s.mem s₃.mem := by rw [← lm]; exact nout
  have outW : Outside B (dT + 8 * (i + w)) 8 s₃.mem t.mem := by
    rw [tm]; exact writeW_outside _ B _ (by omega_arith)
  have oA : Outside B (dT + 8 * i) (8 * w + 8) s.mem t.mem :=
    (o₃.mono (Nat.le_refl _) (by omega_arith)).trans (outW.mono (by omega_arith) (by omega_arith))
  -- What the row read.
  have rM : wordsVal s.mem B dM w = M := jout.wordsVal (by omega_arith) (by omega_arith)
  have rW : word s₃.mem B (dT + 8 * (i + w)) = word s.mem B (dT + 8 * (i + w)) :=
    o₃.word (by omega_arith) (by omega_arith)
  rw [lm, l0, l1, rM] at neq
  rw [rW, g₃ .a1 (by decide)] at tv
  have hu : (word s.mem B (dT + 8 * i) * s₀.gpr .t1).toNat =
      (word s.mem B (dT + 8 * i)).toNat * (s₀.gpr .t1).toNat % 2 ^ 64 := BitVec.toNat_mul _ _
  rw [hu] at neq
  have hz : (0 : BitVec 64).toNat = 0 := rfl
  rw [hz, Nat.add_zero] at neq
  -- The row's low word is cleared.
  have hm0 : M % 2 ^ 64 = (word s₀.mem B dM).toNat := by
    show wordsVal s₀.mem B dM w % 2 ^ 64 = _
    rw [fios_wordsVal_pred _ _ _ hw, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (word s₀.mem B dM).isLt]
  have hlow : (word t.mem B (dT + 8 * i)).toNat = 0 := by
    rw [outW.word (by omega_arith) (by omega_arith)]
    have e1 := congrArg (· % 2 ^ 64) neq
    rw [show 2 ^ (64 * w) = 2 ^ 64 * 2 ^ (64 * (w - 1)) by rw [← Nat.pow_add]; congr 1; omega_arith,
      Nat.mul_assoc, Nat.add_mul_mod_self_left, fios_wordsVal_pred _ _ _ hw, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (word s₃.mem B (dT + 8 * i)).isLt, fios_wordsVal_pred _ _ _ hw, Nat.add_assoc,
      Nat.add_comm (2 ^ 64 * _), ← Nat.add_assoc, Nat.add_mul_mod_self_left] at e1
    rw [e1]
    exact red_low hm0 hinv
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, by rw [t2, g₃ .t2 (by decide)]⟩
  · rw [t3, show dT + 8 * i + 8 = dT + 8 * (i + 1) by omega_arith]
  · exact jout.trans (oA.mono (by omega_arith) (by omega_arith))
  · rw [wordsVal_succ_top, hlow, Nat.mul_zero, Nat.add_zero, oA.wordsVal (by omega_arith) (by omega_arith)]
    exact jz
  · refine ⟨U + 2 ^ (64 * i) * ((word s.mem B (dT + 8 * i)).toNat * (s₀.gpr .t1).toNat % 2 ^ 64), ?_, ?_⟩
    · have := Nat.mod_lt ((word s.mem B (dT + 8 * i)).toNat * (s₀.gpr .t1).toNat) (show 0 < 2 ^ 64 by decide)
      have := Nat.mul_le_mul_left (2 ^ (64 * i)) (show
        (word s.mem B (dT + 8 * i)).toNat * (s₀.gpr .t1).toNat % 2 ^ 64 ≤ 2 ^ 64 - 1 by omega_arith)
      rw [show 64 * (i + 1) = 64 * i + 64 by omega_arith, Nat.pow_add]
      rw [Nat.mul_sub, Nat.mul_one] at this
      have := Nat.one_le_two_pow (n := 64 * i)
      have : 2 ^ (64 * i) ≤ 2 ^ (64 * i) * 2 ^ 64 := Nat.le_mul_of_pos_right _ (by decide)
      omega_arith
    · have hlen : 2 * w = i + w + 1 + (w - 1 - i) := by omega_arith
      rw [hlen, wordsVal_seg] at jv ⊢
      rw [show 64 * (i + w) = 64 * i + 64 * w by omega_arith, Nat.pow_add] at jv
      rw [show 64 * (i + 1 + w) = 64 * i + 64 * w + 64 by omega_arith, Nat.pow_add, Nat.pow_add]
      have eL : wordsVal t.mem B dT i = wordsVal s.mem B dT i := oA.wordsVal (by omega_arith) (by omega_arith)
      have eM : wordsVal t.mem B (dT + 8 * i) w = wordsVal s₃.mem B (dT + 8 * i) w :=
        outW.wordsVal (by omega_arith) (by omega_arith)
      have eW : word t.mem B (dT + 8 * (i + w)) = v := by rw [tm]; exact word_writeW_self _ _ _ _
      have eR : wordsVal t.mem B (dT + 8 * (i + w + 1)) (w - 1 - i) =
          wordsVal s.mem B (dT + 8 * (i + w + 1)) (w - 1 - i) := oA.wordsVal (by omega_arith) (by omega_arith)
      rw [eL, eM, eW, eR, Nat.add_mul, Nat.mul_assoc (2 ^ (64 * i)) _ M]
      exact red_sum jv neq tv
  · exact Keep.trans' jk (Keep.trans' (k₂.mono (by decide)) (Keep.trans' (k₃.mono (by decide)) (tk.mono (by decide))))

end VG.Proof.Bignum.RISCV64

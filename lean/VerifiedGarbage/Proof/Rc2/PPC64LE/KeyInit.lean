module

import VerifiedGarbage.Proof.Rc2.PPC64LE.KeySteps
public import VerifiedGarbage.Proof.Rc2.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Rc2.PPC64LE.ExpandKey
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.Rc2.Table

/-!
# RC2 on PPC64LE: the setup of key expansion

`piInit_run`: PITABLE's doublewords, from immediates, into the working space.
`maskCode_run`: `TM`, chosen by branches on the public `effective_bits mod 8`.
`reduceSetup_run`: `T8` and the index of the reduction.
-/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE

theorem movImm64_val (v : BitVec 64) :
    (((v.extractLsb' 48 16 ++ (0 : BitVec 16)).signExtend 64 ||| (v.extractLsb' 32 16).setWidth 64) <<< 32 |||
      (v.extractLsb' 16 16).setWidth 64 <<< 16 ||| (v.extractLsb' 0 16).setWidth 64) = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_signExtend, BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
  by_cases h1 : i < 16
  · simp (disch := omega) [h1, show i < 32 by omega]
  · by_cases h2 : i < 32
    · simp (disch := omega) [h1, h2, show i - 16 < 16 by omega, show i - 16 < 64 by omega,
        show 16 + (i - 16) = i by omega]
    · by_cases h3 : i < 48
      · simp (disch := omega) [h1, h2, show i - 32 < 16 by omega, show ¬i - 16 < 16 by omega,
          show i - 32 < 64 by omega, show i - 32 < 32 by omega, show 32 + (i - 32) = i by omega]
      · simp (disch := omega) [h1, h2, show ¬i - 16 < 16 by omega, show i - 32 < 32 by omega,
          show ¬i - 32 < 16 by omega, show i - 32 < 64 by omega, show i - 32 - 16 < 16 by omega,
          show 48 + (i - 32 - 16) = i by omega]

theorem movImm64_run (u : State) (v : BitVec 64) :
    WP isa (.block (movImm64 .r12 v)) u fun t => t.gpr .r12 = v ∧ t.mem = u.mem ∧ Keep [.r12] u t := by
  refine WP.mono (WP.keep [.r12] (c := .block (movImm64 .r12 v)) (Q := fun t => t.gpr .r12 = v ∧ t.mem = u.mem) ?_
    (by rfl) rfl) fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  unfold movImm64
  rrun
  exact movImm64_val v

theorem piInit_steps (u : State) {W : Addr} (hW : u.gpr .r7 = W)
    (hw : ∀ k < 32, InRegions u.wr (W + BitVec.ofNat 64 (8 * k)) 8) :
    ∀ n ≤ 32, WP isa (.block ((List.range n).flatMap fun k =>
        movImm64 .r12 (Impl.Rc2.piQuad k) ++ ([.store .d .r12 .r7 (8 * k)] : List Instr))) u fun t =>
      (∀ i < n, t.mem.readW (W + BitVec.ofNat 64 (8 * i)) 64 = Impl.Rc2.piQuad i) ∧
      Frame [⟨W, 256⟩] u.mem t.mem ∧ Keep [.r12] u t := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, Keep.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨held, F, k⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [WP.block_append_iff]
    refine WP.mono (movImm64_run t _) fun t₁ ⟨a₁, m₁, k₁⟩ => ?_
    have h7 : t₁.gpr .r7 = W := by rw [k₁.gpr (by decide), k.gpr (by decide), hW]
    refine WP.mono (WP.keep [] (c := .block [.store .d .r12 .r7 (8 * n)]) (Q := fun t₂ =>
        t₂.mem = t₁.mem.writeW (W + BitVec.ofNat 64 (8 * n)) (Impl.Rc2.piQuad n)) ?_
      (by rfl) rfl) fun t₂ ⟨m₂, k₂⟩ => ⟨fun i hi => ?_, ?_, ?_⟩
    · rrun [h7, a₁, show 8 * n < 32768 by omega, show 8 * n % 4 = 0 by omega,
        show InRegions t₁.wr (W + BitVec.ofNat 64 (8 * n)) 8 by rw [k₁.2.2, k.2.2]; exact hw n (by omega)]
    · rw [m₂, m₁]
      by_cases e : i = n
      · subst e; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (Offset.sep W (by omega) (by omega) (by omega)) (by decide)]
        exact held i (by omega)
    · rw [m₂, m₁]; exact F.writeW List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))
    · exact ((k.trans k₁).trans k₂).mono (by simp)

theorem piInit_run (u : State) {W : Addr} (hW : u.gpr .r7 = W)
    (hw : ∀ k < 32, InRegions u.wr (W + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block piInit) u fun t =>
      Proof.Rc2.PiHeld t.mem W ∧ Frame [⟨W, 256⟩] u.mem t.mem ∧ Keep [.r12] u t :=
  WP.mono (piInit_steps u hW hw 32 (Nat.le_refl _)) fun _ ⟨held, F, k⟩ =>
    ⟨fun i hi => by rw [Proof.Rc2.piQuads_length] at hi; rw [held i hi, Proof.Rc2.piQuads_getD hi], F, k⟩

/-- `TM` for `c = effective_bits mod 8`. -/
noncomputable def maskVal (c : Nat) : Nat := if c = 0 then 255 else 2 ^ c - 1

theorem sub_beq_zero {c k : Nat} (hc : c < 8) (hk : k < 8) :
    (BitVec.ofNat 64 c - BitVec.ofNat 64 k == 0#64) = decide (c = k) := by
  by_cases h : c = k
  · subst h; simp
  · have : BitVec.ofNat 64 c - BitVec.ofNat 64 k ≠ 0#64 := by
      intro e
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)] at this
      omega
    simp [this, h]

theorem mask_loop {c₀ : Nat} (hc : c₀ < 8) : ∀ n k, k + n = 7 → ∀ u : State, u.gpr .r9 = BitVec.ofNat 64 c₀ →
    u.gpr .r12 = BitVec.ofNat 64 (if 1 ≤ c₀ ∧ c₀ ≤ k then 2 ^ c₀ - 1 else 255) →
    WP isa ((List.range' k n).foldr (fun c rest => .seq (.block [.subi .r10 .r9 (c + 1)])
        (.seq (.ite (.zero .d .r10) (.block [.li .r12 (2 ^ (c + 1) - 1)]) (.block [])) rest)) (.block [])) u
      fun t => t.gpr .r12 = BitVec.ofNat 64 (maskVal c₀) ∧ t.mem = u.mem ∧ Keep [.r10, .r12] u t := by
  intro n
  induction n with
  | zero =>
    intro k hk u _ h12
    refine WP.block_nil ⟨?_, rfl, Keep.refl _ _⟩
    rw [h12]; unfold maskVal
    by_cases h : c₀ = 0
    · rw [ite_eq_right (by omega), ite_eq_left h]
    · rw [ite_eq_left (by omega), ite_eq_right h]
  | succ n ih =>
    intro k hk u h9 h12
    rw [List.range'_succ, List.foldr_cons]
    apply WP.seq
    refine WP.mono (WP.keep [.r10] (c := .block [.subi .r10 .r9 (k + 1)]) (Q := fun t =>
        t.gpr .r10 = u.gpr .r9 - BitVec.ofNat 64 (k + 1) ∧ t.mem = u.mem)
      (by rrun [show k + 1 ≤ 32768 by omega]) (by rfl) rfl)
      fun t₁ ⟨⟨a₁, m₁⟩, k₁⟩ => ?_
    apply WP.seq
    have hb : isa.eval (.zero .d .r10) t₁ = some (decide (c₀ = k + 1)) := by
      rw [eval_zero, a₁, h9, sub_beq_zero hc (by omega)]
    refine WP.ite _ hb (fun ht => ?_) (fun hf => ?_)
    · have e : c₀ = k + 1 := of_decide_eq_true ht
      have hli : 2 ^ (k + 1) - 1 < 2 ^ 15 := by
        have : 2 ^ (k + 1) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
        omega
      refine WP.mono (WP.keep [.r12] (c := .block [.li .r12 (2 ^ (k + 1) - 1)]) (Q := fun t =>
          t.gpr .r12 = BitVec.ofNat 64 (2 ^ (k + 1) - 1) ∧ t.mem = t₁.mem)
        (by rrun [hli])
        (by rfl) rfl) fun t₂ ⟨⟨a₂, m₂⟩, k₂⟩ => ?_
      refine WP.mono (ih (k + 1) (by omega) t₂ (by rw [k₂.gpr (by decide), k₁.gpr (by decide), h9])
        (by rw [a₂, ite_eq_left (by omega), e])) fun t ⟨a, m, kk⟩ =>
          ⟨a, by rw [m, m₂, m₁], ((k₁.trans k₂).trans kk).mono (by simp)⟩
    · have e : c₀ ≠ k + 1 := of_decide_eq_false hf
      refine WP.block_nil ?_
      refine WP.mono (ih (k + 1) (by omega) t₁ (by rw [k₁.gpr (by decide), h9])
        (by
          rw [k₁.gpr (by decide), h12]
          by_cases h : 1 ≤ c₀ ∧ c₀ ≤ k
          · rw [ite_eq_left h, ite_eq_left (by omega)]
          · rw [ite_eq_right h, ite_eq_right (by omega)])) fun t ⟨a, m, kk⟩ =>
          ⟨a, by rw [m, m₁], (k₁.trans kk).mono (by simp)⟩

theorem low3 (bits : Nat) (hb : bits < 2 ^ 64) :
    (BitVec.ofNat 64 bits <<< 61) >>> 61 = BitVec.ofNat 64 (bits % 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (show bits % 8 < 2 ^ 64 by omega)]
  omega

theorem maskCode_run (u : State) {bits : Nat} (hb : bits < 2 ^ 64) (h5 : u.gpr .r5 = BitVec.ofNat 64 bits) :
    WP isa maskCode u fun t => t.gpr .r12 = BitVec.ofNat 64 (maskVal (bits % 8)) ∧ t.mem = u.mem ∧
      Keep [.r9, .r10, .r12] u t := by
  unfold maskCode
  apply WP.seq
  refine WP.mono (WP.keep [.r9, .r12] (c := .block [.lsl .r9 .r5 61, .lsr .d .r9 .r9 61, .li .r12 255])
      (Q := fun t => t.gpr .r9 = BitVec.ofNat 64 (bits % 8) ∧ t.gpr .r12 = BitVec.ofNat 64 255 ∧ t.mem = u.mem)
    (by rrun [h5]; exact low3 bits hb) (by rfl) rfl)
    fun t₁ ⟨⟨a₁, b₁, m₁⟩, k₁⟩ => ?_
  rw [List.range_eq_range']
  refine WP.mono (mask_loop (c₀ := bits % 8) (by omega) 7 0 rfl t₁ a₁ (by rw [b₁, ite_eq_right (by omega)]))
    fun t ⟨a, m, k⟩ => ⟨a, by rw [m, m₁], (k₁.trans k).mono (by simp)⟩

theorem maskVal_eq {bits : Nat} : maskVal (bits % 8) = 255 % 2 ^ (8 + bits - 8 * ((bits + 7) / 8)) := by
  unfold maskVal
  by_cases h : bits % 8 = 0
  · rw [ite_eq_left h, show 8 + bits - 8 * ((bits + 7) / 8) = 8 by omega]
  · rw [ite_eq_right h, show 8 + bits - 8 * ((bits + 7) / 8) = bits % 8 by omega]
    have : ∀ c < 8, c ≠ 0 → 2 ^ c - 1 = 255 % 2 ^ c := by decide
    exact this _ (Nat.mod_lt _ (by decide)) h

theorem reduceSetup_run (u : State) {bits : Nat} (hb : bits ≤ 1024) (h5 : u.gpr .r5 = BitVec.ofNat 64 bits) :
    WP isa (.block reduceSetup) u fun t => t.gpr .r14 = BitVec.ofNat 64 ((bits + 7) / 8) ∧
      t.gpr .r8 = BitVec.ofNat 64 (128 - (bits + 7) / 8) ∧ t.mem = u.mem ∧ Keep [.r8, .r14] u t := by
  refine WP.mono (WP.keep [.r8, .r14] (c := .block reduceSetup) (Q := fun t =>
      t.gpr .r14 = BitVec.ofNat 64 ((bits + 7) / 8) ∧ t.gpr .r8 = BitVec.ofNat 64 (128 - (bits + 7) / 8) ∧
        t.mem = u.mem) ?_ (by rfl) rfl)
    fun t ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩
  have e14 : (BitVec.ofNat 64 bits + BitVec.ofNat 64 7) >>> 3 = BitVec.ofNat 64 ((bits + 7) / 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (show bits < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show (7 : Nat) < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show bits + 7 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show (bits + 7) / 8 < 2 ^ 64 by omega)]
  have e8 : BitVec.ofNat 64 128 - BitVec.ofNat 64 ((bits + 7) / 8) = BitVec.ofNat 64 (128 - (bits + 7) / 8) :=
    Offset.ofNat_sub_ofNat (by omega)
  unfold reduceSetup
  rrun [h5, e14, e8]

end VG.Proof.Rc2.PPC64LE

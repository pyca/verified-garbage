import VerifiedGarbage.Impl.Camellia.X86_64.Layers
import VerifiedGarbage.Proof.Camellia.Bitsliced
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Bitslice.Lanes

/-!
# FL and FLINV on x86-64

The two steps of FL (`flRot`, `flOr`) AND and OR the planes with the
subkey's, so they are not linear, and are run symbolically: one plane's
five instructions for any plane (`flRotStep_ok`, `flOrStep_ok`), composed by
induction over the planes. Each step reads planes as they were before the
step (`flRot` saves plane 7 and updates the planes from 7 down), so the
result is `RotStep` and `OrStep` of `Proof/Camellia/Bitsliced.lean`.
-/

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.Impl.Camellia.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 slotAt rorI andS xorR movR)
open VG.Proof.Camellia (RotStep OrStep oddAt rotPos)

theorem runBlock_append' (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => simp [runBlock]
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

/-- The memory FL reads: the subkey's planes `K i` at words `off + i` of
`kp`, and the masks of the odd and even bytes in their slots. -/
structure FlMem (s : State) (off : Nat) (K : Nat → BitVec 64) : Prop where
  key : ∀ i < 8, InRegions (s.rd ++ s.wr) (s.gpr kp + BitVec.ofInt 64 ((8 * (off + i) : Nat) : Int)) 8 ∧
    s.mem.readW (s.gpr kp + BitVec.ofInt 64 ((8 * (off + i) : Nat) : Int)) 64 = K i
  odd : InRegions (s.rd ++ s.wr) (s.gpr sb + BitVec.ofInt 64 ((8 * oddSlot : Nat) : Int)) 8 ∧
    s.mem.readW (s.gpr sb + BitVec.ofInt 64 ((8 * oddSlot : Nat) : Int)) 64 = 0xFF00FF00FF00FF00
  even : InRegions (s.rd ++ s.wr) (s.gpr sb + BitVec.ofInt 64 ((8 * evenSlot : Nat) : Int)) 8 ∧
    s.mem.readW (s.gpr sb + BitVec.ofInt 64 ((8 * evenSlot : Nat) : Int)) 64 = 0x00FF00FF00FF00FF

/-- `FlMem` survives a run that keeps the memory, the regions, `kp` and `sb`. -/
theorem FlMem.congr {s s' : State} {off : Nat} {K : Nat → BitVec 64} (h : FlMem s off K)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hk : s'.gpr kp = s.gpr kp)
    (hb : s'.gpr sb = s.gpr sb) : FlMem s' off K where
  key i hi := by rw [hm, hrd, hwr, hk]; exact h.key i hi
  odd := by rw [hm, hrd, hwr, hb]; exact h.odd
  even := by rw [hm, hrd, hwr, hb]; exact h.even

theorem kp_ne_t0 : kp ≠ t0 := by decide
theorem sb_ne_t0 : sb ≠ t0 := by decide
theorem q_ne_t0 : ∀ i < 8, q i ≠ t0 := by decide
theorem q_ne_t1 : ∀ i < 8, q i ≠ t1 := by decide
theorem q_ne_kp : ∀ i < 8, q i ≠ kp := by decide
theorem q_ne_sb : ∀ i < 8, q i ≠ sb := by decide
theorem q_inj : ∀ i < 8, ∀ j < 8, q i = q j → i = j := by decide

theorem flRotStep_ok {s : State} {j kw sh : Nat} {src : Reg} {K M : BitVec 64} (hj : q j ≠ t0)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr kp + BitVec.ofInt 64 ((8 * kw : Nat) : Int)) 8)
    (hkv : s.mem.readW (s.gpr kp + BitVec.ofInt 64 ((8 * kw : Nat) : Int)) 64 = K)
    (hm : InRegions (s.rd ++ s.wr) (s.gpr sb + BitVec.ofInt 64 ((8 * oddSlot : Nat) : Int)) 8)
    (hmv : s.mem.readW (s.gpr sb + BitVec.ofInt 64 ((8 * oddSlot : Nat) : Int)) 64 = M)
    (hsh : 1 ≤ sh ∧ sh ≤ 63) :
    ∃ s', runBlock isa (flRotStep j src kw sh) s = some s' ∧
      s'.gpr (q j) = s.gpr (q j) ^^^ ((s.gpr src &&& K).rotateRight sh &&& M) ∧
      (∀ r, r ≠ q j → r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by
    simp only [flRotStep, andK, keyAt, slotAt, movR, rorI, andS, xorR, runBlock_cons, runStep_some,
      runBlock_nil, exec, execAlu, execShift, readSrc, State.load64, State.ea, RegUpd.rd_setReg,
      RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.gpr_setReg_of_ne _ _ kp_ne_t0,
      RegUpd.gpr_setReg_of_ne _ _ sb_ne_t0,
      RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, RegUpd.gpr_arithFlags,
      RegUpd.rd_setFlags, RegUpd.wr_setFlags, RegUpd.mem_setFlags, RegUpd.gpr_setFlags,
      hk, hm, hsh, and_self, ite_true, Option.bind_some, Option.map_some]
    rfl, ?_⟩
  refine ⟨?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_setReg_self, RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne _ _ hj,
      RegUpd.gpr_setFlags, hkv, hmv]
  · simp only [RegUpd.gpr_setReg_of_ne _ _ h1, RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne _ _ h2,
      RegUpd.gpr_setFlags]

theorem flOrStep_ok {s : State} {j kw : Nat} {K M : BitVec 64} (hj : q j ≠ t0)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr kp + BitVec.ofInt 64 ((8 * kw : Nat) : Int)) 8)
    (hkv : s.mem.readW (s.gpr kp + BitVec.ofInt 64 ((8 * kw : Nat) : Int)) 64 = K)
    (hm : InRegions (s.rd ++ s.wr) (s.gpr sb + BitVec.ofInt 64 ((8 * evenSlot : Nat) : Int)) 8)
    (hmv : s.mem.readW (s.gpr sb + BitVec.ofInt 64 ((8 * evenSlot : Nat) : Int)) 64 = M) :
    ∃ s', runBlock isa (flOrStep j kw) s = some s' ∧
      s'.gpr (q j) = s.gpr (q j) ^^^ ((s.gpr (q j) ||| K).rotateRight 8 &&& M) ∧
      (∀ r, r ≠ q j → r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by
    simp only [flOrStep, orK, keyAt, slotAt, movR, rorI, andS, xorR, runBlock_cons, runStep_some,
      runBlock_nil, exec, execAlu, execShift, readSrc, State.load64, State.ea, RegUpd.rd_setReg,
      RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.gpr_setReg_of_ne _ _ kp_ne_t0,
      RegUpd.gpr_setReg_of_ne _ _ sb_ne_t0,
      RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, RegUpd.gpr_arithFlags,
      RegUpd.rd_setFlags, RegUpd.wr_setFlags, RegUpd.mem_setFlags, RegUpd.gpr_setFlags,
      hk, hm, and_self, ite_true, Option.bind_some, Option.map_some, show 1 ≤ 8 ∧ 8 ≤ 63 by decide]
    rfl, ?_⟩
  refine ⟨?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_setReg_self, RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne _ _ hj,
      RegUpd.gpr_setFlags, hkv, hmv]
  · simp only [RegUpd.gpr_setReg_of_ne _ _ h1, RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne _ _ h2,
      RegUpd.gpr_setFlags]

/-- The rotation step's update of plane `j` from the planes `X` and the subkey's `K`. -/
def rotUpd (X K : Nat → BitVec 64) (j : Nat) : BitVec 64 :=
  X j ^^^ ((X ((j + 7) % 8) &&& K ((j + 7) % 8)).rotateRight (if j = 0 then 8 else 56) &&&
    0xFF00FF00FF00FF00)

theorem flRotDesc_ok {off K} : ∀ n ≤ 7, ∀ s : State, FlMem s off K →
    ∃ s', runBlock isa (flRotDesc off n) s = some s' ∧
      (∀ i < 8, s'.gpr (q i) = if 1 ≤ i ∧ i ≤ n then rotUpd (fun i => s.gpr (q i)) K i else s.gpr (q i)) ∧
      (∀ r, (∀ i < 8, r ≠ q i) → r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr
  | 0, _, s, _ => ⟨s, runBlock_nil, fun i _ => by simp only [show ¬ (1 ≤ i ∧ i ≤ 0) by omega, ↓reduceIte],
      fun _ _ _ => rfl, rfl, rfl, rfl⟩
  | n + 1, hn, s, hf => by
    obtain ⟨hk, hkv⟩ := hf.key n (by omega)
    obtain ⟨s₁, h₁, g₁, o₁, m₁, rd₁, wr₁⟩ :=
      flRotStep_ok (j := n + 1) (src := q n) (q_ne_t0 _ (by omega)) hk hkv hf.odd.1 hf.odd.2
        (by decide : 1 ≤ 56 ∧ 56 ≤ 63)
    have hf₁ : FlMem s₁ off K := hf.congr m₁ rd₁ wr₁ (o₁ _ (fun h => q_ne_kp _ (by omega) h.symm)
      (by decide)) (o₁ _ (fun h => q_ne_sb _ (by omega) h.symm) (by decide))
    obtain ⟨s', h', g', o', m', rd', wr'⟩ := flRotDesc_ok n (by omega) s₁ hf₁
    refine ⟨s', by rw [flRotDesc, runBlock_append', h₁]; exact h', fun i hi => ?_,
      fun r h1 h2 => by rw [o' r h1 h2, o₁ r (h1 _ (by omega)) h2], by rw [m', m₁],
      by rw [rd', rd₁], by rw [wr', wr₁]⟩
    have hs₁ : ∀ i' < 8, i' ≠ n + 1 → s₁.gpr (q i') = s.gpr (q i') := fun i' hi' hne =>
      o₁ _ (fun h => hne (q_inj _ hi' _ (by omega) h)) (q_ne_t0 _ hi')
    rw [g' i hi]
    by_cases hin : 1 ≤ i ∧ i ≤ n
    · simp only [hin, show 1 ≤ i ∧ i ≤ n + 1 by omega, and_self, ↓reduceIte]
      simp only [rotUpd]
      rw [hs₁ _ hi (by omega), hs₁ _ (Nat.mod_lt _ (by omega)) (by omega)]
    · simp only [hin, ↓reduceIte]
      by_cases hi1 : i = n + 1
      · subst hi1
        simp only [g₁, show 1 ≤ n + 1 ∧ n + 1 ≤ n + 1 by omega, and_self, ↓reduceIte]
        simp only [rotUpd, show (n + 1 + 7) % 8 = n by omega, show ¬ n + 1 = 0 by omega, ite_false]
      · rw [hs₁ _ hi hi1]; simp only [show ¬ (1 ≤ i ∧ i ≤ n + 1) by omega, ↓reduceIte]

/-- The OR step's update of plane `j`. -/
def orUpd (X K : Nat → BitVec 64) (j : Nat) : BitVec 64 :=
  X j ^^^ ((X j ||| K j).rotateRight 8 &&& 0x00FF00FF00FF00FF)

theorem flOrDesc_ok {off K} : ∀ n ≤ 8, ∀ s : State, FlMem s off K →
    ∃ s', runBlock isa (flOrDesc off n) s = some s' ∧
      (∀ i < 8, s'.gpr (q i) = if i < n then orUpd (fun i => s.gpr (q i)) K i else s.gpr (q i)) ∧
      (∀ r, (∀ i < 8, r ≠ q i) → r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr
  | 0, _, s, _ => ⟨s, runBlock_nil, fun i _ => by simp only [show ¬ i < 0 by omega, ↓reduceIte],
      fun _ _ _ => rfl, rfl, rfl, rfl⟩
  | n + 1, hn, s, hf => by
    obtain ⟨hk, hkv⟩ := hf.key n (by omega)
    obtain ⟨s₁, h₁, g₁, o₁, m₁, rd₁, wr₁⟩ :=
      flOrStep_ok (j := n) (q_ne_t0 _ (by omega)) hk hkv hf.even.1 hf.even.2
    have hf₁ : FlMem s₁ off K := hf.congr m₁ rd₁ wr₁ (o₁ _ (fun h => q_ne_kp _ (by omega) h.symm)
      (by decide)) (o₁ _ (fun h => q_ne_sb _ (by omega) h.symm) (by decide))
    obtain ⟨s', h', g', o', m', rd', wr'⟩ := flOrDesc_ok n (by omega) s₁ hf₁
    refine ⟨s', by rw [flOrDesc, runBlock_append', h₁]; exact h', fun i hi => ?_,
      fun r h1 h2 => by rw [o' r h1 h2, o₁ r (h1 _ (by omega)) h2], by rw [m', m₁],
      by rw [rd', rd₁], by rw [wr', wr₁]⟩
    have hs₁ : ∀ i' < 8, i' ≠ n → s₁.gpr (q i') = s.gpr (q i') := fun i' hi' hne =>
      o₁ _ (fun h => hne (q_inj _ hi' _ (by omega) h)) (q_ne_t0 _ hi')
    rw [g' i hi]
    by_cases hin : i < n
    · simp only [hin, show i < n + 1 by omega, ↓reduceIte, orUpd]
      rw [hs₁ _ hi (by omega)]
    · simp only [hin, ↓reduceIte]
      by_cases hi1 : i = n
      · subst hi1
        simp only [g₁, show i < i + 1 by omega, ↓reduceIte, orUpd]
      · rw [hs₁ _ hi hi1]; simp only [show ¬ i < n + 1 by omega, ↓reduceIte]

theorem flOr_ok {off K} {s : State} (hf : FlMem s off K) :
    ∃ s', runBlock isa (flOr off) s = some s' ∧
      (∀ i < 8, s'.gpr (q i) = orUpd (fun i => s.gpr (q i)) K i) ∧
      (∀ r, (∀ i < 8, r ≠ q i) → r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  obtain ⟨s', h', g', rest⟩ := flOrDesc_ok 8 (by omega) s hf
  exact ⟨s', h', fun i hi => by rw [g' i hi]; simp only [hi, ↓reduceIte], rest⟩

theorem flRot_ok {off K} {s : State} (hf : FlMem s off K) :
    ∃ s', runBlock isa (flRot off) s = some s' ∧
      (∀ i < 8, s'.gpr (q i) = rotUpd (fun i => s.gpr (q i)) K i) ∧
      (∀ r, (∀ i < 8, r ≠ q i) → r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  -- `mov t1, q 7`
  let s₀ := s.setReg t1 (s.gpr (q 7))
  have h₀ : runBlock isa [movR t1 (q 7)] s = some s₀ := by
    simp only [movR, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some]; rfl
  have g₀ : ∀ r, r ≠ t1 → s₀.gpr r = s.gpr r := fun r h => RegUpd.gpr_setReg_of_ne _ _ h
  have hf₀ : FlMem s₀ off K := hf.congr rfl rfl rfl (g₀ _ (by decide)) (g₀ _ (by decide))
  obtain ⟨s₁, h₁, g₁, o₁, m₁, rd₁, wr₁⟩ := flRotDesc_ok 7 (by omega) s₀ hf₀
  have hf₁ : FlMem s₁ off K := hf₀.congr m₁ rd₁ wr₁ (o₁ _ (fun i hi h => q_ne_kp _ hi h.symm)
    (by decide)) (o₁ _ (fun i hi h => q_ne_sb _ hi h.symm) (by decide))
  obtain ⟨hk, hkv⟩ := hf₁.key 7 (by omega)
  obtain ⟨s₂, h₂, g₂, o₂, m₂, rd₂, wr₂⟩ :=
    flRotStep_ok (j := 0) (src := t1) (q_ne_t0 _ (by omega)) hk hkv hf₁.odd.1 hf₁.odd.2
      (by decide : 1 ≤ 8 ∧ 8 ≤ 63)
  have hq₀ : ∀ i < 8, s₀.gpr (q i) = s.gpr (q i) := fun i hi => g₀ _ (q_ne_t1 i hi)
  refine ⟨s₂, by rw [flRot, runBlock_append', runBlock_append', h₀, Option.bind_some, h₁,
      Option.bind_some]; exact h₂, fun i hi => ?_, fun r h1 h2 h3 => ?_,
    by rw [m₂, m₁]; rfl, by rw [rd₂, rd₁]; rfl, by rw [wr₂, wr₁]; rfl⟩
  · have hrot : ∀ j < 8, rotUpd (fun i => s₀.gpr (q i)) K j = rotUpd (fun i => s.gpr (q i)) K j := by
      intro j hj
      simp only [rotUpd]
      rw [hq₀ _ hj, hq₀ _ (Nat.mod_lt _ (by omega))]
    by_cases hi0 : i = 0
    · subst hi0
      have ht1 : s₁.gpr t1 = s.gpr (q 7) := by
        rw [o₁ _ (fun i hi h => q_ne_t1 i hi h.symm) (by decide)]; exact RegUpd.gpr_setReg_self _ _ _
      rw [g₂, g₁ 0 (by omega), ht1, hq₀ 0 (by omega)]
      simp only [show ¬ (1 ≤ 0 ∧ 0 ≤ 7) by omega, ↓reduceIte, rotUpd]
    · rw [o₂ _ (fun h => hi0 (q_inj _ hi _ (by omega) h)) (q_ne_t0 _ hi), g₁ i hi]
      simp only [show 1 ≤ i ∧ i ≤ 7 by omega, and_self, ↓reduceIte]
      exact hrot i hi
  · rw [o₂ r (h1 0 (by omega)) h2, o₁ r h1 h2, g₀ r h3]

theorem odd_mask_bit : ∀ p < 64, (0xFF00FF00FF00FF00 : BitVec 64).getLsbD p = oddAt p := by decide
theorem even_mask_bit : ∀ p < 64, (0x00FF00FF00FF00FF : BitVec 64).getLsbD p = !oddAt p := by decide

theorem rotStep_of {X K Y : Nat → BitVec 64} (h : ∀ i < 8, Y i = rotUpd X K i) : RotStep X K Y := by
  intro j hj p hp
  rw [h j hj, rotUpd, BitVec.getLsbD_xor, BitVec.getLsbD_and, odd_mask_bit p hp,
    VG.Bitslice.getLsbD_rotateRight_lt _ _ _ hp, BitVec.getLsbD_and]
  simp only [rotPos, Bool.and_comm (oddAt p), Bool.and_assoc]

theorem orStep_of {X K Y : Nat → BitVec 64} (h : ∀ i < 8, Y i = orUpd X K i) : OrStep X K Y := by
  intro j hj p hp
  rw [h j hj, orUpd, BitVec.getLsbD_xor, BitVec.getLsbD_and, even_mask_bit p hp,
    VG.Bitslice.getLsbD_rotateRight_lt _ _ _ hp, BitVec.getLsbD_or, Bool.and_comm]

end VG.Proof.Camellia.X86_64

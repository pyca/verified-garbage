import VerifiedGarbage.Impl.Camellia.AArch64.Layers
import VerifiedGarbage.Proof.Camellia.Bitsliced
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Bitslice.Lanes

/-!
# FL and FLINV on AArch64

As on x86-64: the two steps of FL (`flRot`, `flOr`) AND and OR the planes
with the subkey's, so they are not linear, and are run symbolically, one
plane's five instructions for any plane (`flRotStep_ok`, `flOrStep_ok`),
composed by induction over the planes. The mask of the step is loaded into
`t2` first.
-/

namespace VG.Proof.Camellia.AArch64

open VG VG.AArch64 VG.Impl.Camellia.AArch64
open VG.Impl.Aes.AArch64 (q sb t0 t1 t2 u7 kp ldS rorI andR orrR eorR movR)
open VG.Proof.Camellia (RotStep OrStep oddAt rotPos)

theorem runBlock_append' (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

/-- The memory FL reads: the subkey's planes `K i` at words `off + i` of
`kp`, and the masks of the odd and even bytes in their slots. -/
structure FlMem (s : State) (off : Nat) (K : Nat → BitVec 64) : Prop where
  key : ∀ i < 8, InRegions (s.rd ++ s.wr) (s.gpr kp + BitVec.ofNat 64 (8 * (off + i))) 8 ∧
    s.mem.readW (s.gpr kp + BitVec.ofNat 64 (8 * (off + i))) 64 = K i
  keyOff : 8 * (off + 7) < 32768
  odd : InRegions (s.rd ++ s.wr) (s.gpr sb + BitVec.ofNat 64 (8 * oddSlot)) 8 ∧
    s.mem.readW (s.gpr sb + BitVec.ofNat 64 (8 * oddSlot)) 64 = 0xFF00FF00FF00FF00
  even : InRegions (s.rd ++ s.wr) (s.gpr sb + BitVec.ofNat 64 (8 * evenSlot)) 8 ∧
    s.mem.readW (s.gpr sb + BitVec.ofNat 64 (8 * evenSlot)) 64 = 0x00FF00FF00FF00FF

/-- `FlMem` survives a run that keeps the memory, the regions, `kp` and `sb`. -/
theorem FlMem.congr {s s' : State} {off : Nat} {K : Nat → BitVec 64} (h : FlMem s off K)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hk : s'.gpr kp = s.gpr kp)
    (hb : s'.gpr sb = s.gpr sb) : FlMem s' off K where
  key i hi := by rw [hm, hrd, hwr, hk]; exact h.key i hi
  keyOff := h.keyOff
  odd := by rw [hm, hrd, hwr, hb]; exact h.odd
  even := by rw [hm, hrd, hwr, hb]; exact h.even

theorem q_ne_t0 : ∀ i < 8, q i ≠ t0 := by decide
theorem q_ne_t1 : ∀ i < 8, q i ≠ t1 := by decide
theorem q_ne_t2 : ∀ i < 8, q i ≠ t2 := by decide
theorem q_ne_u7 : ∀ i < 8, q i ≠ u7 := by decide
theorem q_ne_kp : ∀ i < 8, q i ≠ kp := by decide
theorem q_ne_sb : ∀ i < 8, q i ≠ sb := by decide
theorem q_inj : ∀ i < 8, ∀ j < 8, q i = q j → i = j := by decide

theorem read_x' (s : State) (r : Reg) : s.read .x r = s.gpr r := by
  simp only [State.read, BitVec.setWidth_eq]

/-- `ldr r, [sb, #8 k]`, a mask. -/
theorem ldMask_ok {s : State} {r : Reg} {k : Nat} {M : BitVec 64} (hk : 8 * k < 32768)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr sb + BitVec.ofNat 64 (8 * k)) 8)
    (hv : s.mem.readW (s.gpr sb + BitVec.ofNat 64 (8 * k)) 64 = M) :
    ∃ s', runBlock isa [ldS r k] s = some s' ∧ s'.gpr r = M ∧ (∀ r', r' ≠ r → s'.gpr r' = s.gpr r') ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨s.write .x r (s.mem.readW (s.gpr sb + BitVec.ofNat 64 (8 * k)) 64), by
    simp only [ldS, runBlock_cons, runStep_some, runBlock_nil, exec_ldr_x ⟨by omega, hk⟩ hin], ?_,
    fun r' h => RegUpd.gpr_write_of_ne _ _ _ h, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_write_self, BitVec.setWidth_eq, hv]

theorem flRotStep_ok {s : State} {j kw sh : Nat} {src : Reg} {K : BitVec 64} (hj : j < 8)
    (hsrc : src ≠ u7) (hko : 8 * kw < 32768)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr kp + BitVec.ofNat 64 (8 * kw)) 8)
    (hkv : s.mem.readW (s.gpr kp + BitVec.ofNat 64 (8 * kw)) 64 = K) (hsh : sh < 64) :
    ∃ s', runBlock isa (flRotStep j src kw sh) s = some s' ∧
      s'.gpr (q j) = s.gpr (q j) ^^^ ((s.gpr src &&& K).rotateRight sh &&& s.gpr t2) ∧
      (∀ r, r ≠ q j → r ≠ t0 → r ≠ u7 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have h1 := q_ne_t0 j hj
  have h2 := q_ne_u7 j hj
  refine ⟨_, by
    simp only [flRotStep, andR, rorI, eorR, runBlock_cons, runStep_some, runBlock_nil,
      exec_ldr_x ⟨by omega, hko⟩ hk, exec_logic, exec_ror_x hsh]
    rfl, ?_⟩
  refine ⟨?_, fun r r1 r2 r3 => ?_, rfl, rfl, rfl⟩
  · simp only [read_x', RegUpd.gpr_write_self, BitVec.setWidth_eq, RegUpd.gpr_write_of_ne _ _ _ h1,
      RegUpd.gpr_write_of_ne _ _ _ h2, RegUpd.gpr_write_of_ne _ _ _ hsrc,
      RegUpd.gpr_write_of_ne _ _ _ (show (t2 : Reg) ≠ t0 by decide),
      RegUpd.gpr_write_of_ne _ _ _ (show (t2 : Reg) ≠ u7 by decide), hkv]
  · simp only [RegUpd.gpr_write_of_ne _ _ _ r1, RegUpd.gpr_write_of_ne _ _ _ r2,
      RegUpd.gpr_write_of_ne _ _ _ r3]

theorem flOrStep_ok {s : State} {j kw : Nat} {K : BitVec 64} (hj : j < 8) (hko : 8 * kw < 32768)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr kp + BitVec.ofNat 64 (8 * kw)) 8)
    (hkv : s.mem.readW (s.gpr kp + BitVec.ofNat 64 (8 * kw)) 64 = K) :
    ∃ s', runBlock isa (flOrStep j kw) s = some s' ∧
      s'.gpr (q j) = s.gpr (q j) ^^^ ((s.gpr (q j) ||| K).rotateRight 8 &&& s.gpr t2) ∧
      (∀ r, r ≠ q j → r ≠ t0 → r ≠ u7 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have h1 := q_ne_t0 j hj
  have h2 := q_ne_u7 j hj
  refine ⟨_, by
    simp only [flOrStep, orrR, rorI, andR, eorR, runBlock_cons, runStep_some, runBlock_nil,
      exec_ldr_x ⟨by omega, hko⟩ hk, exec_logic, exec_ror_x (show 8 < 64 by decide)]
    rfl, ?_⟩
  refine ⟨?_, fun r r1 r2 r3 => ?_, rfl, rfl, rfl⟩
  · simp only [read_x', RegUpd.gpr_write_self, BitVec.setWidth_eq, RegUpd.gpr_write_of_ne _ _ _ h1,
      RegUpd.gpr_write_of_ne _ _ _ h2,
      RegUpd.gpr_write_of_ne _ _ _ (show (t2 : Reg) ≠ t0 by decide),
      RegUpd.gpr_write_of_ne _ _ _ (show (t2 : Reg) ≠ u7 by decide), hkv]
  · simp only [RegUpd.gpr_write_of_ne _ _ _ r1, RegUpd.gpr_write_of_ne _ _ _ r2,
      RegUpd.gpr_write_of_ne _ _ _ r3]

/-- The rotation step's update of plane `j` from the planes `X` and the subkey's `K`. -/
def rotUpd (X K : Nat → BitVec 64) (j : Nat) : BitVec 64 :=
  X j ^^^ ((X ((j + 7) % 8) &&& K ((j + 7) % 8)).rotateRight (if j = 0 then 8 else 56) &&&
    0xFF00FF00FF00FF00)

theorem flRotDesc_ok {off K} : ∀ n ≤ 7, ∀ s : State, FlMem s off K → s.gpr t2 = 0xFF00FF00FF00FF00 →
    ∃ s', runBlock isa (flRotDesc off n) s = some s' ∧
      (∀ i < 8, s'.gpr (q i) = if 1 ≤ i ∧ i ≤ n then rotUpd (fun i => s.gpr (q i)) K i else s.gpr (q i)) ∧
      (∀ r, (∀ i < 8, r ≠ q i) → r ≠ t0 → r ≠ u7 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr
  | 0, _, s, _, _ => ⟨s, runBlock_nil, fun i _ => by simp only [show ¬ (1 ≤ i ∧ i ≤ 0) by omega, ↓reduceIte],
      fun _ _ _ _ => rfl, rfl, rfl, rfl⟩
  | n + 1, hn, s, hf, ht2 => by
    obtain ⟨hk, hkv⟩ := hf.key n (by omega)
    have hko := hf.keyOff
    obtain ⟨s₁, h₁, g₁, o₁, m₁, rd₁, wr₁⟩ :=
      flRotStep_ok (j := n + 1) (src := q n) (by omega) (q_ne_u7 n (by omega)) (by omega) hk hkv
        (by decide : 56 < 64)
    have hf₁ : FlMem s₁ off K := hf.congr m₁ rd₁ wr₁ (o₁ _ (fun h => q_ne_kp _ (by omega) h.symm)
      (by decide) (by decide)) (o₁ _ (fun h => q_ne_sb _ (by omega) h.symm) (by decide) (by decide))
    have ht2₁ : s₁.gpr t2 = 0xFF00FF00FF00FF00 := by
      rw [o₁ _ (fun h => q_ne_t2 _ (by omega) h.symm) (by decide) (by decide), ht2]
    obtain ⟨s', h', g', o', m', rd', wr'⟩ := flRotDesc_ok n (by omega) s₁ hf₁ ht2₁
    refine ⟨s', by rw [flRotDesc, runBlock_append', h₁]; exact h', fun i hi => ?_,
      fun r h1 h2 h3 => by rw [o' r h1 h2 h3, o₁ r (h1 _ (by omega)) h2 h3], by rw [m', m₁],
      by rw [rd', rd₁], by rw [wr', wr₁]⟩
    have hs₁ : ∀ i' < 8, i' ≠ n + 1 → s₁.gpr (q i') = s.gpr (q i') := fun i' hi' hne =>
      o₁ _ (fun h => hne (q_inj _ hi' _ (by omega) h)) (q_ne_t0 _ hi') (q_ne_u7 _ hi')
    rw [g' i hi]
    by_cases hin : 1 ≤ i ∧ i ≤ n
    · simp only [hin, show 1 ≤ i ∧ i ≤ n + 1 by omega, and_self, ↓reduceIte]
      simp only [rotUpd]
      rw [hs₁ _ hi (by omega), hs₁ _ (Nat.mod_lt _ (by omega)) (by omega)]
    · simp only [hin, ↓reduceIte]
      by_cases hi1 : i = n + 1
      · subst hi1
        simp only [g₁, ht2, show 1 ≤ n + 1 ∧ n + 1 ≤ n + 1 by omega, and_self, ↓reduceIte]
        simp only [rotUpd, show (n + 1 + 7) % 8 = n by omega, show ¬ n + 1 = 0 by omega, ite_false]
      · rw [hs₁ _ hi hi1]; simp only [show ¬ (1 ≤ i ∧ i ≤ n + 1) by omega, ↓reduceIte]

/-- The OR step's update of plane `j`. -/
def orUpd (X K : Nat → BitVec 64) (j : Nat) : BitVec 64 :=
  X j ^^^ ((X j ||| K j).rotateRight 8 &&& 0x00FF00FF00FF00FF)

theorem flOrDesc_ok {off K} : ∀ n ≤ 8, ∀ s : State, FlMem s off K → s.gpr t2 = 0x00FF00FF00FF00FF →
    ∃ s', runBlock isa (flOrDesc off n) s = some s' ∧
      (∀ i < 8, s'.gpr (q i) = if i < n then orUpd (fun i => s.gpr (q i)) K i else s.gpr (q i)) ∧
      (∀ r, (∀ i < 8, r ≠ q i) → r ≠ t0 → r ≠ u7 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr
  | 0, _, s, _, _ => ⟨s, runBlock_nil, fun i _ => by simp only [show ¬ i < 0 by omega, ↓reduceIte],
      fun _ _ _ _ => rfl, rfl, rfl, rfl⟩
  | n + 1, hn, s, hf, ht2 => by
    obtain ⟨hk, hkv⟩ := hf.key n (by omega)
    have hko := hf.keyOff
    obtain ⟨s₁, h₁, g₁, o₁, m₁, rd₁, wr₁⟩ := flOrStep_ok (j := n) (by omega) (by omega) hk hkv
    have hf₁ : FlMem s₁ off K := hf.congr m₁ rd₁ wr₁ (o₁ _ (fun h => q_ne_kp _ (by omega) h.symm)
      (by decide) (by decide)) (o₁ _ (fun h => q_ne_sb _ (by omega) h.symm) (by decide) (by decide))
    have ht2₁ : s₁.gpr t2 = 0x00FF00FF00FF00FF := by
      rw [o₁ _ (fun h => q_ne_t2 _ (by omega) h.symm) (by decide) (by decide), ht2]
    obtain ⟨s', h', g', o', m', rd', wr'⟩ := flOrDesc_ok n (by omega) s₁ hf₁ ht2₁
    refine ⟨s', by rw [flOrDesc, runBlock_append', h₁]; exact h', fun i hi => ?_,
      fun r h1 h2 h3 => by rw [o' r h1 h2 h3, o₁ r (h1 _ (by omega)) h2 h3], by rw [m', m₁],
      by rw [rd', rd₁], by rw [wr', wr₁]⟩
    have hs₁ : ∀ i' < 8, i' ≠ n → s₁.gpr (q i') = s.gpr (q i') := fun i' hi' hne =>
      o₁ _ (fun h => hne (q_inj _ hi' _ (by omega) h)) (q_ne_t0 _ hi') (q_ne_u7 _ hi')
    rw [g' i hi]
    by_cases hin : i < n
    · simp only [hin, show i < n + 1 by omega, ↓reduceIte, orUpd]
      rw [hs₁ _ hi (by omega)]
    · simp only [hin, ↓reduceIte]
      by_cases hi1 : i = n
      · subst hi1
        simp only [g₁, ht2, show i < i + 1 by omega, ↓reduceIte, orUpd]
      · rw [hs₁ _ hi hi1]; simp only [show ¬ i < n + 1 by omega, ↓reduceIte]

theorem flOr_ok {off K} {s : State} (hf : FlMem s off K) :
    ∃ s', runBlock isa (flOr off) s = some s' ∧
      (∀ i < 8, s'.gpr (q i) = orUpd (fun i => s.gpr (q i)) K i) ∧
      (∀ r, (∀ i < 8, r ≠ q i) → r ≠ t0 → r ≠ u7 → r ≠ t2 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₀, h₀, v₀, g₀, m₀, rd₀, wr₀⟩ := ldMask_ok (r := t2) (k := evenSlot) (by decide) hf.even.1 hf.even.2
  have hf₀ : FlMem s₀ off K := hf.congr m₀ rd₀ wr₀ (g₀ _ (by decide)) (g₀ _ (by decide))
  obtain ⟨s', h', g', o', m', rd', wr'⟩ := flOrDesc_ok 8 (by omega) s₀ hf₀ v₀
  have hq₀ : ∀ i < 8, s₀.gpr (q i) = s.gpr (q i) := fun i hi => g₀ _ (q_ne_t2 i hi)
  refine ⟨s', by rw [flOr, show ldMask t2 evenSlot :: flOrDesc off 8 = [ldS t2 evenSlot] ++ flOrDesc off 8
      from rfl, runBlock_append', h₀, Option.bind_some]; exact h', fun i hi => ?_,
    fun r h1 h2 h3 h4 => by rw [o' r h1 h2 h3, g₀ r h4], by rw [m', m₀], by rw [rd', rd₀],
    by rw [wr', wr₀]⟩
  rw [g' i hi]
  simp only [hi, ↓reduceIte, orUpd, hq₀ i hi]

theorem flRot_ok {off K} {s : State} (hf : FlMem s off K) :
    ∃ s', runBlock isa (flRot off) s = some s' ∧
      (∀ i < 8, s'.gpr (q i) = rotUpd (fun i => s.gpr (q i)) K i) ∧
      (∀ r, (∀ i < 8, r ≠ q i) → r ≠ t0 → r ≠ u7 → r ≠ t1 → r ≠ t2 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨sa, ha, va, ga, ma, rda, wra⟩ := ldMask_ok (r := t2) (k := oddSlot) (by decide) hf.odd.1 hf.odd.2
  -- `mov t1, q 7`
  let s₀ := sa.write .x t1 (sa.gpr (q 7))
  have h₀ : runBlock isa [movR t1 (q 7)] sa = some s₀ := by
    simp only [movR, runBlock_cons, runStep_some, runBlock_nil, exec_addImm_x (show 0 < 4096 by decide),
      read_x', BitVec.add_zero]; rfl
  have g₀ : ∀ r, r ≠ t1 → s₀.gpr r = sa.gpr r := fun r h => RegUpd.gpr_write_of_ne _ _ _ h
  have hfa : FlMem sa off K := hf.congr ma rda wra (ga _ (by decide)) (ga _ (by decide))
  have hf₀ : FlMem s₀ off K := hfa.congr rfl rfl rfl (g₀ _ (by decide)) (g₀ _ (by decide))
  have ht2₀ : s₀.gpr t2 = 0xFF00FF00FF00FF00 := by rw [g₀ _ (by decide), va]
  obtain ⟨s₁, h₁, g₁, o₁, m₁, rd₁, wr₁⟩ := flRotDesc_ok 7 (by omega) s₀ hf₀ ht2₀
  have hko := hf.keyOff
  have hf₁ : FlMem s₁ off K := hf₀.congr m₁ rd₁ wr₁ (o₁ _ (fun i hi h => q_ne_kp _ hi h.symm)
    (by decide) (by decide)) (o₁ _ (fun i hi h => q_ne_sb _ hi h.symm) (by decide) (by decide))
  obtain ⟨hk, hkv⟩ := hf₁.key 7 (by omega)
  obtain ⟨s₂, h₂, g₂, o₂, m₂, rd₂, wr₂⟩ :=
    flRotStep_ok (j := 0) (src := t1) (by omega) (by decide) (by omega) hk hkv (by decide : 8 < 64)
  have hq₀ : ∀ i < 8, s₀.gpr (q i) = s.gpr (q i) := fun i hi => by
    rw [g₀ _ (q_ne_t1 i hi), ga _ (q_ne_t2 i hi)]
  have ht2₁ : s₁.gpr t2 = 0xFF00FF00FF00FF00 := by
    rw [o₁ _ (fun i hi h => q_ne_t2 i hi h.symm) (by decide) (by decide), ht2₀]
  refine ⟨s₂, by rw [flRot, show [ldMask t2 oddSlot, movR t1 (q 7)] = [ldS t2 oddSlot] ++ [movR t1 (q 7)]
      from rfl, runBlock_append', runBlock_append', runBlock_append', ha, Option.bind_some, h₀,
      Option.bind_some, h₁, Option.bind_some]; exact h₂, fun i hi => ?_, fun r h1 h2 h3 h4 h5 => ?_,
    by rw [m₂, m₁, ← ma]; rfl, by rw [rd₂, rd₁, ← rda]; rfl, by rw [wr₂, wr₁, ← wra]; rfl⟩
  · have hrot : ∀ j < 8, rotUpd (fun i => s₀.gpr (q i)) K j = rotUpd (fun i => s.gpr (q i)) K j := by
      intro j hj
      simp only [rotUpd]
      rw [hq₀ _ hj, hq₀ _ (Nat.mod_lt _ (by omega))]
    by_cases hi0 : i = 0
    · subst hi0
      have ht1 : s₁.gpr t1 = s.gpr (q 7) := by
        rw [o₁ _ (fun i hi h => q_ne_t1 i hi h.symm) (by decide) (by decide)]
        rw [show s₀.gpr t1 = sa.gpr (q 7) from by
          simp only [s₀, RegUpd.gpr_write_self, BitVec.setWidth_eq], ga _ (q_ne_t2 7 (by omega))]
      rw [g₂, g₁ 0 (by omega), ht1, hq₀ 0 (by omega), ht2₁]
      simp only [show ¬ (1 ≤ 0 ∧ 0 ≤ 7) by omega, ↓reduceIte, rotUpd]
    · rw [o₂ _ (fun h => hi0 (q_inj _ hi _ (by omega) h)) (q_ne_t0 _ hi) (q_ne_u7 _ hi), g₁ i hi]
      simp only [show 1 ≤ i ∧ i ≤ 7 by omega, and_self, ↓reduceIte]
      exact hrot i hi
  · rw [o₂ r (h1 0 (by omega)) h2 h3, o₁ r h1 h2 h3, g₀ r h4, ga r h5]

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

end VG.Proof.Camellia.AArch64

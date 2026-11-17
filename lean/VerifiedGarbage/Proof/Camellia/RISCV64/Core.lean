module

public import VerifiedGarbage.Proof.Camellia.RISCV64.Linear
public import VerifiedGarbage.Impl.Camellia.RISCV64.Ecb
public import VerifiedGarbage.Proof.Camellia.Words
import VerifiedGarbage.Proof.Camellia.Common
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Impl.Camellia.RISCV64.Sbox
public import VerifiedGarbage.Proof.Camellia.SboxTable
public import VerifiedGarbage.Proof.Aes.RISCV64.Layers
public import VerifiedGarbage.Impl.Camellia.RISCV64.Layers
public import VerifiedGarbage.Proof.Camellia.Bitsliced
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RISCV64.Straight

/-! ### `Camellia.RISCV64.Round`, which this module and modules that import it used -/

section

/-! ### `Camellia.RISCV64.Fl`, which this module and modules that import it used -/

section

/-!
# FL and FLINV on RISC-V

As on PPC64LE (`Proof/Camellia/PPC64LE/Crypt8.lean`) and x86-64: the two steps of FL (`flRot`, `flOr`) AND and OR the planes
with the subkey's, so they are not linear, and are run symbolically, one
plane's five instructions for any plane (`flRotStep_ok`, `flOrStep_ok`),
composed by induction over the planes. The mask of the step is loaded into
`t2` first. RV64I has no rotate: a plane's step rotates with two shifts and
an XOR through `t4` (`rorI`), which `rot_shifts` turns back into a rotation.
-/

@[expose] public section

namespace VG.Proof.Camellia.RISCV64

open VG VG.RISCV64 VG.Impl.Camellia.RISCV64
open VG.Impl.Aes.RISCV64 (q sb t0 t1 t2 u7 kp rt ldS rorI shlI shrI andR xorR movR)
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
  keyOff : 8 * (off + 7) < 2048
  kpAl : (s.gpr kp).toNat % 8 = 0
  sbAl : (s.gpr sb).toNat % 8 = 0
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
  kpAl := by rw [hk]; exact h.kpAl
  sbAl := by rw [hb]; exact h.sbAl
  odd := by rw [hm, hrd, hwr, hb]; exact h.odd
  even := by rw [hm, hrd, hwr, hb]; exact h.even

theorem q_ne_t0 : ∀ i < 8, q i ≠ t0 := by decide
theorem q_ne_t1 : ∀ i < 8, q i ≠ t1 := by decide
theorem q_ne_t2 : ∀ i < 8, q i ≠ t2 := by decide
theorem q_ne_u7 : ∀ i < 8, q i ≠ u7 := by decide
theorem q_ne_kp : ∀ i < 8, q i ≠ kp := by decide
theorem q_ne_sb : ∀ i < 8, q i ≠ sb := by decide
theorem q_ne_rt : ∀ i < 8, q i ≠ rt := by decide
theorem q_inj : ∀ i < 8, ∀ j < 8, q i = q j → i = j := by decide

/-- The rotation through `rt`, `rorI`'s two shifts and XOR. -/
theorem rot_shifts (x : BitVec 64) {k : Nat} (hk : 0 < k) (hk' : k < 64) :
    x <<< (64 - k) ^^^ x >>> k = x.rotateRight k := by
  rw [BitVec.xor_comm]
  exact Straight.shr_shl x hk hk' (op := .xor) (by decide)

/-- `ld r, 8 k(sb)`, a mask. -/
theorem ldMask_ok {s : State} {r : Reg} {k : Nat} {M : BitVec 64} (hk : 8 * k < 2048)
    (hal : (s.gpr sb).toNat % 8 = 0)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr sb + BitVec.ofNat 64 (8 * k)) 8)
    (hv : s.mem.readW (s.gpr sb + BitVec.ofNat 64 (8 * k)) 64 = M) :
    ∃ s', runBlock isa [ldS r k] s = some s' ∧ s'.gpr r = M ∧ (∀ r', r' ≠ r → s'.gpr r' = s.gpr r') ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨s.write r (s.mem.readW (s.gpr sb + BitVec.ofNat 64 (8 * k)) 64), by
    simp only [ldS, runBlock_cons, runStep_some, runBlock_nil,
      exec_load_d hk (Spill.al8 hal (by omega_using [])) hin], ?_,
    fun r' h => RegUpd.gpr_write_of_ne _ _ h, rfl, rfl, rfl⟩
  simp only [RegUpd.gpr_write_self, hv]

theorem flRotStep_ok {s : State} {j kw sh : Nat} {src : Reg} {K : BitVec 64} (hj : j < 8)
    (hsrc : src ≠ u7) (hko : 8 * kw < 2048) (hal : (s.gpr kp).toNat % 8 = 0)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr kp + BitVec.ofNat 64 (8 * kw)) 8)
    (hkv : s.mem.readW (s.gpr kp + BitVec.ofNat 64 (8 * kw)) 64 = K) (hsh0 : 0 < sh) (hsh : sh < 64) :
    ∃ s', runBlock isa (flRotStep j src kw sh) s = some s' ∧
      s'.gpr (q j) = s.gpr (q j) ^^^ ((s.gpr src &&& K).rotateRight sh &&& s.gpr t2) ∧
      (∀ r, r ≠ q j → r ≠ t0 → r ≠ u7 → r ≠ rt → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have h1 := q_ne_t0 j hj
  have h2 := q_ne_u7 j hj
  have h3 := q_ne_rt j hj
  refine ⟨_, by
    simp only [flRotStep, andR, rorI, shlI, shrI, xorR, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil,
      exec_load_d hko (Spill.al8 hal (by omega_using [])) hk, exec_logic,
      exec_shift_d hsh, exec_shift_d (show 64 - sh < 64 by omega_using [hsh0])]
    rfl, ?_⟩
  refine ⟨?_, fun r r1 r2 r3 r4 => ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne _ _ h1,
      RegUpd.gpr_write_of_ne _ _ h2, RegUpd.gpr_write_of_ne _ _ h3, RegUpd.gpr_write_of_ne _ _ hsrc,
      RegUpd.gpr_write_of_ne _ _ (show (t2 : Reg) ≠ t0 by decide),
      RegUpd.gpr_write_of_ne _ _ (show (t2 : Reg) ≠ u7 by decide),
      RegUpd.gpr_write_of_ne _ _ (show (t2 : Reg) ≠ rt by decide),
      RegUpd.gpr_write_of_ne _ _ (show (t0 : Reg) ≠ rt by decide),
      RegUpd.gpr_write_of_ne _ _ (show (rt : Reg) ≠ t0 by decide), hkv]
    simp only [rot_shifts _ hsh0 hsh]
  · simp only [RegUpd.gpr_write_of_ne _ _ r1, RegUpd.gpr_write_of_ne _ _ r2,
      RegUpd.gpr_write_of_ne _ _ r3, RegUpd.gpr_write_of_ne _ _ r4]

theorem flOrStep_ok {s : State} {j kw : Nat} {K : BitVec 64} (hj : j < 8) (hko : 8 * kw < 2048)
    (hal : (s.gpr kp).toNat % 8 = 0)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr kp + BitVec.ofNat 64 (8 * kw)) 8)
    (hkv : s.mem.readW (s.gpr kp + BitVec.ofNat 64 (8 * kw)) 64 = K) :
    ∃ s', runBlock isa (flOrStep j kw) s = some s' ∧
      s'.gpr (q j) = s.gpr (q j) ^^^ ((s.gpr (q j) ||| K).rotateRight 8 &&& s.gpr t2) ∧
      (∀ r, r ≠ q j → r ≠ t0 → r ≠ u7 → r ≠ rt → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have h1 := q_ne_t0 j hj
  have h2 := q_ne_u7 j hj
  have h3 := q_ne_rt j hj
  refine ⟨_, by
    simp only [flOrStep, orR, rorI, shlI, shrI, andR, xorR, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil,
      exec_load_d hko (Spill.al8 hal (by omega_using [])) hk, exec_logic,
      exec_shift_d (show 8 < 64 by decide), exec_shift_d (show 64 - 8 < 64 by decide)]
    rfl, ?_⟩
  refine ⟨?_, fun r r1 r2 r3 r4 => ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne _ _ h1,
      RegUpd.gpr_write_of_ne _ _ h2, RegUpd.gpr_write_of_ne _ _ h3,
      RegUpd.gpr_write_of_ne _ _ (show (t2 : Reg) ≠ t0 by decide),
      RegUpd.gpr_write_of_ne _ _ (show (t2 : Reg) ≠ u7 by decide),
      RegUpd.gpr_write_of_ne _ _ (show (t2 : Reg) ≠ rt by decide),
      RegUpd.gpr_write_of_ne _ _ (show (t0 : Reg) ≠ rt by decide),
      RegUpd.gpr_write_of_ne _ _ (show (rt : Reg) ≠ t0 by decide), hkv]
    simp only [rot_shifts _ (show 0 < 8 by decide) (show 8 < 64 by decide)]
  · simp only [RegUpd.gpr_write_of_ne _ _ r1, RegUpd.gpr_write_of_ne _ _ r2,
      RegUpd.gpr_write_of_ne _ _ r3, RegUpd.gpr_write_of_ne _ _ r4]

/-- The rotation step's update of plane `j` from the planes `X` and the subkey's `K`. -/
def rotUpd (X K : Nat → BitVec 64) (j : Nat) : BitVec 64 :=
  X j ^^^ ((X ((j + 7) % 8) &&& K ((j + 7) % 8)).rotateRight (if j = 0 then 8 else 56) &&&
    0xFF00FF00FF00FF00)

theorem flRotDesc_ok {off K} : ∀ n ≤ 7, ∀ s : State, FlMem s off K → s.gpr t2 = 0xFF00FF00FF00FF00 →
    ∃ s', runBlock isa (flRotDesc off n) s = some s' ∧
      (∀ i < 8, s'.gpr (q i) = if 1 ≤ i ∧ i ≤ n then rotUpd (fun i => s.gpr (q i)) K i else s.gpr (q i)) ∧
      (∀ r, (∀ i < 8, r ≠ q i) → r ≠ t0 → r ≠ u7 → r ≠ rt → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr
  | 0, _, s, _, _ => ⟨s, runBlock_nil, fun i _ => by simp only [show ¬ (1 ≤ i ∧ i ≤ 0) by omega_arith, ↓reduceIte],
      fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  | n + 1, hn, s, hf, ht2 => by
    obtain ⟨hk, hkv⟩ := hf.key n (by omega_arith)
    have hko := hf.keyOff
    obtain ⟨s₁, h₁, g₁, o₁, m₁, rd₁, wr₁⟩ :=
      flRotStep_ok (j := n + 1) (src := q n) (by omega_arith) (q_ne_u7 n (by omega_arith)) (by omega_arith) hf.kpAl hk hkv
        (by decide) (by decide : 56 < 64)
    have hf₁ : FlMem s₁ off K := hf.congr m₁ rd₁ wr₁ (o₁ _ (fun h => q_ne_kp _ (by omega_arith) h.symm)
      (by decide) (by decide) (by decide)) (o₁ _ (fun h => q_ne_sb _ (by omega_arith) h.symm) (by decide) (by decide) (by decide))
    have ht2₁ : s₁.gpr t2 = 0xFF00FF00FF00FF00 := by
      rw [o₁ _ (fun h => q_ne_t2 _ (by omega_arith) h.symm) (by decide) (by decide) (by decide), ht2]
    obtain ⟨s', h', g', o', m', rd', wr'⟩ := flRotDesc_ok n (by omega_arith) s₁ hf₁ ht2₁
    refine ⟨s', by rw [flRotDesc, runBlock_append', h₁]; exact h', fun i hi => ?_,
      fun r h1 h2 h3 h4 => by rw [o' r h1 h2 h3 h4, o₁ r (h1 _ (by omega_arith)) h2 h3 h4], by rw [m', m₁],
      by rw [rd', rd₁], by rw [wr', wr₁]⟩
    have hs₁ : ∀ i' < 8, i' ≠ n + 1 → s₁.gpr (q i') = s.gpr (q i') := fun i' hi' hne =>
      o₁ _ (fun h => hne (q_inj _ hi' _ (by omega_arith) h)) (q_ne_t0 _ hi') (q_ne_u7 _ hi') (q_ne_rt _ hi')
    rw [g' i hi]
    by_cases hin : 1 ≤ i ∧ i ≤ n
    · simp only [hin, show 1 ≤ i ∧ i ≤ n + 1 by omega_arith, and_self, ↓reduceIte]
      simp only [rotUpd]
      rw [hs₁ _ hi (by omega_arith), hs₁ _ (Nat.mod_lt _ (by omega_arith)) (by omega_arith)]
    · simp only [hin, ↓reduceIte]
      by_cases hi1 : i = n + 1
      · subst hi1
        simp only [g₁, ht2, show 1 ≤ n + 1 ∧ n + 1 ≤ n + 1 by omega_arith, and_self, ↓reduceIte]
        simp only [rotUpd, show (n + 1 + 7) % 8 = n by omega_arith, show ¬ n + 1 = 0 by omega_arith, ite_false]
      · rw [hs₁ _ hi hi1]; simp only [show ¬ (1 ≤ i ∧ i ≤ n + 1) by omega_arith, ↓reduceIte]

/-- The OR step's update of plane `j`. -/
def orUpd (X K : Nat → BitVec 64) (j : Nat) : BitVec 64 :=
  X j ^^^ ((X j ||| K j).rotateRight 8 &&& 0x00FF00FF00FF00FF)

theorem flOrDesc_ok {off K} : ∀ n ≤ 8, ∀ s : State, FlMem s off K → s.gpr t2 = 0x00FF00FF00FF00FF →
    ∃ s', runBlock isa (flOrDesc off n) s = some s' ∧
      (∀ i < 8, s'.gpr (q i) = if i < n then orUpd (fun i => s.gpr (q i)) K i else s.gpr (q i)) ∧
      (∀ r, (∀ i < 8, r ≠ q i) → r ≠ t0 → r ≠ u7 → r ≠ rt → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr
  | 0, _, s, _, _ => ⟨s, runBlock_nil, fun i _ => by simp only [show ¬ i < 0 by omega_arith, ↓reduceIte],
      fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  | n + 1, hn, s, hf, ht2 => by
    obtain ⟨hk, hkv⟩ := hf.key n (by omega_arith)
    have hko := hf.keyOff
    obtain ⟨s₁, h₁, g₁, o₁, m₁, rd₁, wr₁⟩ := flOrStep_ok (j := n) (by omega_arith) (by omega_arith) hf.kpAl hk hkv
    have hf₁ : FlMem s₁ off K := hf.congr m₁ rd₁ wr₁ (o₁ _ (fun h => q_ne_kp _ (by omega_arith) h.symm)
      (by decide) (by decide) (by decide)) (o₁ _ (fun h => q_ne_sb _ (by omega_arith) h.symm) (by decide) (by decide) (by decide))
    have ht2₁ : s₁.gpr t2 = 0x00FF00FF00FF00FF := by
      rw [o₁ _ (fun h => q_ne_t2 _ (by omega_arith) h.symm) (by decide) (by decide) (by decide), ht2]
    obtain ⟨s', h', g', o', m', rd', wr'⟩ := flOrDesc_ok n (by omega_arith) s₁ hf₁ ht2₁
    refine ⟨s', by rw [flOrDesc, runBlock_append', h₁]; exact h', fun i hi => ?_,
      fun r h1 h2 h3 h4 => by rw [o' r h1 h2 h3 h4, o₁ r (h1 _ (by omega_arith)) h2 h3 h4], by rw [m', m₁],
      by rw [rd', rd₁], by rw [wr', wr₁]⟩
    have hs₁ : ∀ i' < 8, i' ≠ n → s₁.gpr (q i') = s.gpr (q i') := fun i' hi' hne =>
      o₁ _ (fun h => hne (q_inj _ hi' _ (by omega_arith) h)) (q_ne_t0 _ hi') (q_ne_u7 _ hi') (q_ne_rt _ hi')
    rw [g' i hi]
    by_cases hin : i < n
    · simp only [hin, show i < n + 1 by omega_arith, ↓reduceIte, orUpd]
      rw [hs₁ _ hi (by omega_arith)]
    · simp only [hin, ↓reduceIte]
      by_cases hi1 : i = n
      · subst hi1
        simp only [g₁, ht2, show i < i + 1 by omega_arith, ↓reduceIte, orUpd]
      · rw [hs₁ _ hi hi1]; simp only [show ¬ i < n + 1 by omega_arith, ↓reduceIte]

theorem flOr_ok {off K} {s : State} (hf : FlMem s off K) :
    ∃ s', runBlock isa (flOr off) s = some s' ∧
      (∀ i < 8, s'.gpr (q i) = orUpd (fun i => s.gpr (q i)) K i) ∧
      (∀ r, (∀ i < 8, r ≠ q i) → r ≠ t0 → r ≠ u7 → r ≠ t2 → r ≠ rt → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₀, h₀, v₀, g₀, m₀, rd₀, wr₀⟩ := ldMask_ok (r := t2) (k := evenSlot) (by decide) hf.sbAl hf.even.1 hf.even.2
  have hf₀ : FlMem s₀ off K := hf.congr m₀ rd₀ wr₀ (g₀ _ (by decide)) (g₀ _ (by decide))
  obtain ⟨s', h', g', o', m', rd', wr'⟩ := flOrDesc_ok 8 (by omega_arith) s₀ hf₀ v₀
  have hq₀ : ∀ i < 8, s₀.gpr (q i) = s.gpr (q i) := fun i hi => g₀ _ (q_ne_t2 i hi)
  refine ⟨s', by rw [flOr, show ldS t2 evenSlot :: flOrDesc off 8 = [ldS t2 evenSlot] ++ flOrDesc off 8
      from rfl, runBlock_append', h₀, Option.bind_some]; exact h', fun i hi => ?_,
    fun r h1 h2 h3 h4 h5 => by rw [o' r h1 h2 h3 h5, g₀ r h4], by rw [m', m₀], by rw [rd', rd₀],
    by rw [wr', wr₀]⟩
  rw [g' i hi]
  simp only [hi, ↓reduceIte, orUpd, hq₀ i hi]

theorem flRot_ok {off K} {s : State} (hf : FlMem s off K) :
    ∃ s', runBlock isa (flRot off) s = some s' ∧
      (∀ i < 8, s'.gpr (q i) = rotUpd (fun i => s.gpr (q i)) K i) ∧
      (∀ r, (∀ i < 8, r ≠ q i) → r ≠ t0 → r ≠ u7 → r ≠ t1 → r ≠ t2 → r ≠ rt → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨sa, ha, va, ga, ma, rda, wra⟩ := ldMask_ok (r := t2) (k := oddSlot) (by decide) hf.sbAl hf.odd.1 hf.odd.2
  -- `mov t1, q 7`
  let s₀ := sa.write t1 (sa.gpr (q 7))
  have h₀ : runBlock isa [movR t1 (q 7)] sa = some s₀ := by
    simp only [movR, runBlock_cons, exec_addi (show imm12 0 by decide), runStep_some, runBlock_nil, s₀]
    rw [show BitVec.ofInt 64 0 = 0 from rfl]; exact congrArg (fun v => some (State.write sa t1 v)) (BitVec.add_zero _)
  have g₀ : ∀ r, r ≠ t1 → s₀.gpr r = sa.gpr r := fun r h => RegUpd.gpr_write_of_ne _ _ h
  have hfa : FlMem sa off K := hf.congr ma rda wra (ga _ (by decide)) (ga _ (by decide))
  have hf₀ : FlMem s₀ off K := hfa.congr rfl rfl rfl (g₀ _ (by decide)) (g₀ _ (by decide))
  have ht2₀ : s₀.gpr t2 = 0xFF00FF00FF00FF00 := by rw [g₀ _ (by decide), va]
  obtain ⟨s₁, h₁, g₁, o₁, m₁, rd₁, wr₁⟩ := flRotDesc_ok 7 (by omega_arith) s₀ hf₀ ht2₀
  have hko := hf.keyOff
  have hf₁ : FlMem s₁ off K := hf₀.congr m₁ rd₁ wr₁ (o₁ _ (fun i hi h => q_ne_kp _ hi h.symm)
    (by decide) (by decide) (by decide)) (o₁ _ (fun i hi h => q_ne_sb _ hi h.symm) (by decide) (by decide) (by decide))
  obtain ⟨hk, hkv⟩ := hf₁.key 7 (by omega_arith)
  obtain ⟨s₂, h₂, g₂, o₂, m₂, rd₂, wr₂⟩ :=
    flRotStep_ok (j := 0) (src := t1) (by omega_arith) (by decide) (by omega_arith) hf₁.kpAl hk hkv (by decide) (by decide : 8 < 64)
  have hq₀ : ∀ i < 8, s₀.gpr (q i) = s.gpr (q i) := fun i hi => by
    rw [g₀ _ (q_ne_t1 i hi), ga _ (q_ne_t2 i hi)]
  have ht2₁ : s₁.gpr t2 = 0xFF00FF00FF00FF00 := by
    rw [o₁ _ (fun i hi h => q_ne_t2 i hi h.symm) (by decide) (by decide) (by decide), ht2₀]
  refine ⟨s₂, by rw [flRot, show [ldS t2 oddSlot, movR t1 (q 7)] = [ldS t2 oddSlot] ++ [movR t1 (q 7)]
      from rfl, runBlock_append', runBlock_append', runBlock_append', ha, Option.bind_some, h₀,
      Option.bind_some, h₁, Option.bind_some]; exact h₂, fun i hi => ?_, fun r h1 h2 h3 h4 h5 h6 => ?_,
    by rw [m₂, m₁, ← ma]; rfl, by rw [rd₂, rd₁, ← rda]; rfl, by rw [wr₂, wr₁, ← wra]; rfl⟩
  · have hrot : ∀ j < 8, rotUpd (fun i => s₀.gpr (q i)) K j = rotUpd (fun i => s.gpr (q i)) K j := by
      intro j hj
      simp only [rotUpd]
      rw [hq₀ _ hj, hq₀ _ (Nat.mod_lt _ (by omega_arith))]
    by_cases hi0 : i = 0
    · subst hi0
      have ht1 : s₁.gpr t1 = s.gpr (q 7) := by
        rw [o₁ _ (fun i hi h => q_ne_t1 i hi h.symm) (by decide) (by decide) (by decide)]
        rw [show s₀.gpr t1 = sa.gpr (q 7) from by
          simp only [s₀, RegUpd.gpr_write_self], ga _ (q_ne_t2 7 (by omega_arith))]
      rw [g₂, g₁ 0 (by omega_arith), ht1, hq₀ 0 (by omega_arith), ht2₁]
      simp only [show ¬ (1 ≤ 0 ∧ 0 ≤ 7) by omega_arith, ↓reduceIte, rotUpd]
    · rw [o₂ _ (fun h => hi0 (q_inj _ hi _ (by omega_arith) h)) (q_ne_t0 _ hi) (q_ne_u7 _ hi) (q_ne_rt _ hi), g₁ i hi]
      simp only [show 1 ≤ i ∧ i ≤ 7 by omega_arith, and_self, ↓reduceIte]
      exact hrot i hi
  · rw [o₂ r (h1 0 (by omega_arith)) h2 h3 h6, o₁ r h1 h2 h3 h6, g₀ r h4, ga r h5]

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

end VG.Proof.Camellia.RISCV64

end

end

/-! ### `Camellia.RISCV64.Sbox`, which only this module used -/

section

/-!
# The bitsliced Camellia S-box on RISC-V

As on PPC64LE (`Proof/Camellia/PPC64LE/Sbox.lean`): `sboxCode` only
combines words bitwise, so it computes the same Boolean function at each of
the 64 bit positions: the kernel evaluates it once on truth tables of the
256 inputs (`Bitslice.table`) and compares the result with the
specification's `SBOX1` on the same inputs. Its run relates each abstract
table to the concrete word at every position at once (AES's `TabAll`),
which makes the relation a function, as the evaluator needs. `sbox_ok` then
gives, at every bit position `p`, the S-box of the byte formed by bit `p`
of the eight words.
-/

@[expose] public section

namespace VG.Proof.Camellia.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Bitslice VG.Impl.Aes.RISCV64
open VG.Proof.Camellia
open VG.Proof.Aes (bsByte getLsbD_bsByte)
open VG.Proof.Aes.RISCV64 (TabAll tabAll_sound tabAll_fun sboxWrites not_sboxWrites restRegs)

/-- The S-box's memory: its spill slots, at `a5`. -/
def sboxCfg : Cfg := { base := sb, slots := 48, ext := sb, exts := 0 }

def sboxEnv : Env Nat :=
  { reg := fun r => ((List.range 8).find? (fun k => q k == r)).map fun k => .v (inT k)
    slot := fun _ => none }

def sboxPost (e : Env Nat) : Bool :=
  (List.range 8).all fun j => word (e.reg (q j)) == some (sbox1T j)

theorem sbox_check :
    check (table 64 256) sboxCfg (fun _ => none) Impl.Camellia.RISCV64.sboxCode sboxEnv sboxPost = true := by
  lit_decide

theorem sbox_writes_rest :
    restRegs.all (fun r => Impl.Camellia.RISCV64.sboxCode.all fun i => dst i != some r) = true := by
  decide +kernel

/-- The S-box, at every bit position of the words in `q 0 … q 7`. -/
theorem sbox_ok {s : State} (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa Impl.Camellia.RISCV64.sboxCode s = some s' ∧
      (∀ j < 8, ∀ p < 64,
        (s'.gpr (q j)).getLsbD p = (Spec.Camellia.sbox1 (bsByte (fun k => s.gpr (q k)) p)).getLsbD j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion sboxCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ sbox_check
  obtain hout : ∀ j < 8, e'.reg (q j) = some (.v (sbox1T j)) := by
    intro j hj
    have := List.all_eq_true.mp hpost j (List.mem_range.mpr hj)
    simp only [beq_iff_eq] at this
    cases h : e'.reg (q j) with
    | none => rw [h] at this; cases this
    | some v => cases v <;> rw [h] at this <;> simp_all [word]
  let cs : Nat → Nat := fun p => (bsByte (fun k => s.gpr (q k)) p).toNat
  obtain hcs : ∀ p < 64, cs p < 256 := fun p _ => (bsByte (fun k => s.gpr (q k)) p).isLt
  obtain hrel : Rel (TabAll cs) sboxCfg (fun _ => none) sboxEnv s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    simp only [sboxEnv, Option.map_eq_some_iff] at h
    obtain ⟨k, hk, rfl⟩ := h
    obtain ⟨hqk, hkr⟩ := List.find?_some hk, List.mem_of_find?_eq_some hk
    obtain hk8 := List.mem_range.mp hkr
    simp only [beq_iff_eq] at hqk
    subst hqk
    intro p hp
    simp only [TableRel, inT, testBit_tableOf, hcs p hp, decide_true, Bool.true_and, cs,
      BitVec.testBit_toNat, getLsbD_bsByte _ _ hk8]
  obtain ⟨s', hs', p₀⟩ := run (tabAll_sound hcs) tabAll_fun hok hrel he
  refine ⟨s', hs', fun j hj p hp => ?_, p₀.rd, p₀.wr, p₀.sp, fun r hr => p₀.other r ?_, p₀.frame⟩
  · have hc := hcs p hp
    have := p₀.rel.reg (q j) _ (hout j hj) p hp
    simp only [TableRel] at this
    rw [← this, testBit_sbox1T hc, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp [List.all_eq_true.mp sbox_writes_rest r (not_sboxWrites r hr)]

end VG.Proof.Camellia.RISCV64

end

end


/-!
# A round of bitsliced Camellia on RISC-V

As on PPC64LE (`Proof/Camellia/PPC64LE/Crypt8.lean`), `round_ok`: with the half `D1` (or `D2`) in the state registers, the other
half in its slots and the subkey's planes at `kp`, `round off d` leaves
`d2 ^ F(d1, k)` in both the state registers and the other half's slots,
keeping the masks and the first half's slots, and writing only the slots
below the table. The layers are composed from their checks
(`Linear.lean`, `Sbox.lean`) and `round_rel`.
-/

@[expose] public section

namespace VG.Proof.Camellia.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Bitslice VG.Impl.Camellia.RISCV64
open VG.Impl.Aes.RISCV64 (q sb t0 t1 kp)
open VG.Proof.Aes.RISCV64 (sboxWrites not_sboxWrites restRegs)
open VG.Proof.Camellia (HalfRel toBsG fromBsG keyInG outPG inSrc outSrc pRow pos cpos rowBits round_rel)
open VG.Proof.Aes (bsByte)

/-- The planes in the state registers. -/
abbrev Qs (s : State) (i : Nat) : BitVec 64 := s.gpr (q i)

/-- Slot `k` of the scratch buffer. -/
abbrev slotW (s : State) (k : Nat) : BitVec 64 := s.mem.readW (wordAddr (s.gpr sb) k) 64

/-- Word `k` of the table entry at `kp`. -/
abbrev keyW (s : State) (k : Nat) : BitVec 64 := s.mem.readW (wordAddr (s.gpr kp) k) 64

/-- The masks are in their slots. -/
def MasksOk (s : State) : Prop := ∀ kv ∈ allMasks, slotW s kv.1 = kv.2

/-- The masks' slots, above the S-box's spills and below the halves'. -/
theorem allMasks_slots : ∀ kv ∈ allMasks, 48 ≤ kv.1 ∧ kv.1 < d1Slot := by decide

theorem ok_sbox {s : State} (h : Ok layerCfg s) : Ok sboxCfg s where
  slotIn k hk := h.slotIn k (by simp [sboxCfg, layerCfg, savedSlot] at hk ⊢; omega_using [hk])
  extIn k hk := by simp [sboxCfg] at hk
  baseAl h0 := h.baseAl (by simp [layerCfg, savedSlot])
  extAl h0 := by simp [sboxCfg] at h0
  slots := by simp [sboxCfg]
  sep k _ j hj := by simp [sboxCfg] at hj

theorem xorBits_map_rows (W : Nat → BitVec 64) (S : Nat → BitVec 64) (hS : ∀ i < 8, W i = S i)
    (j b : Nat) (hb : b < 8) (hj : j < 8) (l : List Nat) (hl : ∀ i ∈ l, i < 8) :
    xorBits W (l.map fun i => 64 * outSrc (cpos i) j + 8 * cpos i + b) = rowBits S j b l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    obtain hi := hl i List.mem_cons_self
    obtain hc : cpos i < 8 := Camellia.cpos_lt hi
    obtain ho : outSrc (cpos i) j < 8 := by simp only [outSrc]; split <;> (try split) <;> omega_arith
    simp only [List.map_cons, xorBits_cons, rowBits, List.foldr_cons] at ih ⊢
    rw [Nat.add_assoc, bitOf_word _ _ _ (by omega_using [hb, hc]), hS _ ho, ih fun i' hi' => hl i' (List.mem_cons_of_mem _ hi')]

/-- The frame of the S-box (its spills) keeps the slots from 48 on. -/
theorem slot_above {m m' : Mem} {b : Addr} {n k : Nat} (hf : Frame [⟨b, 8 * n⟩] m m') (hk : n ≤ k)
    (hk' : k < 2 ^ 58) : m'.readW (wordAddr b k) 64 = m.readW (wordAddr b k) 64 :=
  hf.readW (r := ⟨wordAddr b k, 8⟩) (by simp only [Region.Contains]; simp) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.disjoint_base b (by omega_using [hk]) (by omega_using [hk'])) (by decide)

/-- A round, with the subkey at word `off` of `kp` and the other half at slot `d`. -/
theorem round_ok {off d : Nat}
    (hkc : check (lanes 64 12) layerCfg (linExt 8) (keyXor off ++ inSel) keyInEnv
      (linPostG 12 (qOuts (keyInG off)) [] (maskSlots ++ halvesIns.map (·.1)) keyInEnv) = true)
    (hfc : check (lanes 64 12) layerCfg (linExt 24) (feistel d) bothEnv
      (linPostG 12 (qOuts (feistelG d)) ((List.range 8).map fun j => (d + j, feistelG d j))
        (feistelKeep d) bothEnv) = true)
    (hoff : off = 0 ∨ off = 8) (hd : d = d1Slot ∨ d = d2Slot)
    {s : State} (hok : Ok layerCfg s) (hm : MasksOk s) {d1 d2 : Nat → BitVec 64} {k : BitVec 64}
    (hQ : HalfRel (Qs s) d1) (hK : HalfRel (fun j => keyW s (off + j)) fun _ => k)
    (hR : HalfRel (fun j => slotW s (d + j)) d2) :
    ∃ s', runBlock isa (round off d) s = some s' ∧
      HalfRel (Qs s') (fun b => d2 b ^^^ Spec.Camellia.f (d1 b) k) ∧
      HalfRel (fun j => slotW s' (d + j)) (fun b => d2 b ^^^ Spec.Camellia.f (d1 b) k) ∧
      MasksOk s' ∧ (∀ j < 16, d1Slot + j < d ∨ d + 8 ≤ d1Slot + j →
        slotW s' (d1Slot + j) = slotW s (d1Slot + j)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion layerCfg s] s.mem s'.mem := by
  obtain hcode : round off d = (keyXor off ++ inSel) ++ (Impl.Camellia.RISCV64.sboxCode ++
      ((outSel ++ pLayer) ++ feistel d)) := by simp only [round, List.append_assoc]
  obtain hsb : ∀ is : List Instr, ∀ s₁ s₂ : State,
      (∀ r, (is.all fun i => dst i != some r) = true → s₂.gpr r = s₁.gpr r) →
      (is.all fun i => dst i != some sb) = true → s₂.gpr sb = s₁.gpr sb := fun _ _ _ h h' => h _ h'
  -- The subkey XOR and input selection.
  let W₁ : Nat → BitVec 64 := fun i =>
    if i < 8 then Qs s i else if i < 24 then keyW s (i - 8) else slotW s (d1Slot + (i - 24))
  obtain ⟨s₁, h₁, x₁, -, k₁, rd₁, wr₁, sp₁, o₁, f₁, -, -⟩ := linG_ok hkc hok W₁
    (fun r i hri => by
      simp only [qIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hri
      obtain ⟨i, hi, rfl, rfl⟩ := hri
      exact ⟨by omega_arith, by simp [W₁, hi]⟩)
    (fun j i hji => by
      simp only [halvesIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hji
      obtain ⟨j, hj, rfl, rfl⟩ := hji
      refine ⟨by simp [layerCfg, d1Slot, savedSlot]; omega_arith, by omega_arith, ?_⟩
      simp [W₁, show ¬ 24 + j < 8 by omega_arith, show ¬ 24 + j < 24 by omega_arith]; rfl)
    (fun kv hkv => ⟨by have := allMasks_slots kv hkv; simp only [layerCfg, savedSlot, d1Slot] at this ⊢; omega_using [this],
        hm kv hkv⟩)
    (fun j hj => by
      simp only [layerCfg] at hj
      exact ⟨by omega_arith, by simp [W₁, show ¬ 8 + j < 8 by omega_arith, show 8 + j < 24 by omega_arith]; rfl⟩)
  obtain hX : ∀ j < 8, ∀ p < 64, (Qs s₁ j).getLsbD p =
      ((Qs s (inSrc (p / 8) j)).getLsbD p ^^ (keyW s (off + inSrc (p / 8) j)).getLsbD p) := by
    intro j hj p hp
    obtain hi : inSrc (p / 8) j < 8 := by simp only [inSrc]; split <;> omega_arith
    have := x₁ (q j) (keyInG off j) (by simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩) p hp
    rw [this, keyInG, xorBits_cons, xorBits_cons, xorBits_nil, Bool.xor_false,
      bitOf_word _ _ _ hp, bitOf_word _ _ _ hp]
    simp [W₁, hi, show ¬ 8 + off + inSrc (p / 8) j < 8 by omega_arith,
      show 8 + off + inSrc (p / 8) j < 24 by rcases hoff with h | h <;> subst h <;> omega_arith,
      show 8 + off + inSrc (p / 8) j - 8 = off + inSrc (p / 8) j by omega_arith]
  obtain hok₁ : Ok layerCfg s₁ := hok.congr (o₁ _ (by rcases hoff with rfl | rfl <;> decide +kernel)) (o₁ _ (by rcases hoff with rfl | rfl <;> decide +kernel)) rd₁ wr₁
  obtain hm₁ : MasksOk s₁ := fun kv hkv => by
    obtain hb : s₁.gpr sb = s.gpr sb := o₁ _ (by rcases hoff with rfl | rfl <;> decide +kernel)
    have := k₁ kv.1 (List.mem_append_left _ (List.mem_map_of_mem hkv)) (by
      have := allMasks_slots kv hkv; simp only [layerCfg, savedSlot, d1Slot] at this ⊢; omega_using [this])
    simp only [layerCfg] at this
    rw [slotW, hb, this]; exact hm kv hkv
  obtain hh₁ : ∀ j < 16, slotW s₁ (d1Slot + j) = slotW s (d1Slot + j) := fun j hj => by
    obtain hb : s₁.gpr sb = s.gpr sb := o₁ _ (by rcases hoff with rfl | rfl <;> decide +kernel)
    have := k₁ (d1Slot + j) (List.mem_append_right _ (by
      simp only [halvesIns, List.map_map, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩))
      (by simp [layerCfg, savedSlot, d1Slot]; omega_arith)
    simp only [layerCfg] at this
    rw [slotW, hb, this]
  -- The S-box.
  obtain ⟨s₂, h₂, sx₂, rd₂, wr₂, sp₂, o₂, f₂⟩ := sbox_ok (ok_sbox hok₁)
  obtain b₂ : s₂.gpr sb = s.gpr sb := (o₂ sb (by decide)).trans (o₁ _ (by rcases hoff with rfl | rfl <;> decide +kernel))
  obtain kp₂ : s₂.gpr kp = s.gpr kp := (o₂ kp (by decide)).trans (o₁ _ (by rcases hoff with rfl | rfl <;> decide +kernel))
  obtain hok₂ : Ok layerCfg s₂ := hok₁.congr (o₂ sb (by decide)) (o₂ kp (by decide)) rd₂ wr₂
  obtain above₂ : ∀ k, 48 ≤ k → k < keySlot → slotW s₂ k = slotW s₁ k := fun k h1 h2 => by
    simp only [slotW, o₂ sb (by decide)]
    exact slot_above (n := 48) f₂ h1 (by simp [keySlot] at h2; omega_arith)
  obtain hm₂ : MasksOk s₂ := fun kv hkv => by
    rw [above₂ _ (allMasks_slots kv hkv).1
      (by have := allMasks_slots kv hkv; simp only [keySlot, d1Slot] at this ⊢; omega_using [this])]
    exact hm₁ kv hkv
  obtain hh₂ : ∀ j < 16, slotW s₂ (d1Slot + j) = slotW s (d1Slot + j) := fun j hj => by
    rw [above₂ _ (by simp [d1Slot]; omega_arith) (by simp [d1Slot, keySlot]; omega_arith), hh₁ j hj]
  -- The output selection and the P-function.
  let W₃ : Nat → BitVec 64 := fun i =>
    if i < 8 then Qs s₂ i else if i < 24 then slotW s₂ (d1Slot + (i - 8)) else keyW s₂ (i - 24)
  obtain bothIns_ok : ∀ s' : State, (W : Nat → BitVec 64) →
      (∀ i, 8 ≤ i → i < 24 → W i = slotW s' (d1Slot + (i - 8))) →
      ∀ j i, (j, i) ∈ bothIns → j < layerCfg.slots ∧ 64 * i + 64 ≤ 2 ^ 12 ∧
        W i = s'.mem.readW (wordAddr (s'.gpr layerCfg.base) j) 64 := by
    intro s' W hW j i hji
    simp only [bothIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hji
    obtain ⟨j, hj, rfl, rfl⟩ := hji
    refine ⟨by simp [layerCfg, d1Slot, savedSlot]; omega_arith, by omega_arith, ?_⟩
    rw [hW _ (by omega_arith) (by omega_arith), show 8 + j - 8 = j by omega_arith]; rfl
  obtain masks_ok : ∀ s' : State, MasksOk s' → ∀ kv ∈ allMasks, kv.1 < layerCfg.slots ∧
      s'.mem.readW (wordAddr (s'.gpr layerCfg.base) kv.1) 64 = kv.2 := fun s' hm' kv hkv =>
    ⟨by have := allMasks_slots kv hkv; simp only [layerCfg, savedSlot, d1Slot] at this ⊢; omega_using [this], hm' kv hkv⟩
  obtain ⟨s₃, h₃, y₃, -, k₃, rd₃, wr₃, sp₃, o₃, f₃, -, -⟩ := linG_ok outP_check hok₂ W₃
    (fun r i hri => by
      simp only [qIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hri
      obtain ⟨i, hi, rfl, rfl⟩ := hri
      exact ⟨by omega_arith, by simp [W₃, hi]⟩)
    (bothIns_ok s₂ W₃ fun i h1 h2 => by simp [W₃, show ¬ i < 8 by omega_arith, h2])
    (masks_ok s₂ hm₂)
    (fun j hj => by
      simp only [layerCfg] at hj
      exact ⟨by omega_arith, by simp [W₃, show ¬ 24 + j < 8 by omega_arith, show ¬ 24 + j < 24 by omega_arith]; rfl⟩)
  obtain hY : ∀ j < 8, ∀ p < 64, (Qs s₃ j).getLsbD p = rowBits (Qs s₂) j (p % 8) (pRow (pos (p / 8))) := by
    intro j hj p hp
    rw [y₃ (q j) (outPG j) (by simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩) p hp,
      outPG]
    exact xorBits_map_rows W₃ (Qs s₂) (fun i hi => by simp [W₃, hi]) j (p % 8) (by omega_arith) hj _
      fun i hi => Camellia.pRow_lt hi
  obtain b₃ : s₃.gpr sb = s₂.gpr sb := o₃ _ (by decide +kernel)
  obtain kp₃ : s₃.gpr kp = s₂.gpr kp := o₃ _ (by decide +kernel)
  obtain hok₃ : Ok layerCfg s₃ := hok₂.congr b₃ kp₃ rd₃ wr₃
  obtain hm₃ : MasksOk s₃ := fun kv hkv => by
    have := k₃ kv.1 (List.mem_append_left _ (List.mem_map_of_mem hkv)) (masks_ok s₂ hm₂ kv hkv).1
    simp only [layerCfg] at this
    rw [slotW, b₃, this]; exact hm₂ kv hkv
  obtain hh₃ : ∀ j < 16, slotW s₃ (d1Slot + j) = slotW s (d1Slot + j) := fun j hj => by
    have := k₃ (d1Slot + j) (List.mem_append_right _ (by
      simp only [bothIns, List.map_map, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩))
      (by simp [layerCfg, savedSlot, d1Slot]; omega_arith)
    simp only [layerCfg] at this
    rw [slotW, b₃, this, ← hh₂ j hj]
  -- The Feistel XOR.
  let W₄ : Nat → BitVec 64 := fun i =>
    if i < 8 then Qs s₃ i else if i < 24 then slotW s₃ (d1Slot + (i - 8)) else keyW s₃ (i - 24)
  obtain ⟨s₄, h₄, r₄, sl₄, k₄, rd₄, wr₄, sp₄, o₄, f₄, -, -⟩ := linG_ok hfc hok₃ W₄
    (fun r i hri => by
      simp only [qIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hri
      obtain ⟨i, hi, rfl, rfl⟩ := hri
      exact ⟨by omega_arith, by simp [W₄, hi]⟩)
    (bothIns_ok s₃ W₄ fun i h1 h2 => by simp [W₄, show ¬ i < 8 by omega_arith, h2])
    (masks_ok s₃ hm₃)
    (fun j hj => by
      simp only [layerCfg] at hj
      exact ⟨by omega_arith, by simp [W₄, show ¬ 24 + j < 8 by omega_arith, show ¬ 24 + j < 24 by omega_arith]; rfl⟩)
  obtain hdj : ∀ j < 8, d + j = d1Slot + (d - d1Slot + j) := fun j _ => by
    rcases hd with rfl | rfl <;> simp [d1Slot, d2Slot] <;> omega_arith
  obtain hd8 : d - d1Slot < 16 - 7 := by rcases hd with rfl | rfl <;> simp [d1Slot, d2Slot]
  obtain hfe : ∀ j < 8, ∀ p < 64, xorBits W₄ (feistelG d j p) =
      ((Qs s₃ j).getLsbD p ^^ (slotW s (d + j)).getLsbD p) := by
    intro j hj p hp
    rw [feistelG, xorBits_cons, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hp,
      bitOf_word _ _ _ hp, hdj j hj, ← hh₃ _ (by omega_arith)]
    simp [W₄, hj, show ¬ 8 + (d - d1Slot) + j < 8 by omega_arith, show 8 + (d - d1Slot) + j < 24 by omega_arith,
      show 8 + (d - d1Slot) + j - 8 = d - d1Slot + j by omega_arith]
  obtain b₄ : s₄.gpr sb = s₃.gpr sb := o₄ _ (by rcases hd with rfl | rfl <;> decide +kernel)
  obtain hD : HalfRel (Qs s₄) (fun b => d2 b ^^^ Spec.Camellia.f (d1 b) k) :=
    round_rel hQ hK hR hX sx₂ hY fun j hj p hp => by
      rw [r₄ (q j) (feistelG d j) (by simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
        p hp, hfe j hj p hp, Bool.xor_comm]
  obtain hS : HalfRel (fun j => slotW s₄ (d + j)) (fun b => d2 b ^^^ Spec.Camellia.f (d1 b) k) :=
    round_rel hQ hK hR hX sx₂ hY fun j hj p hp => by
      have := sl₄ (d + j) (feistelG d j) (by simp only [List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
        (by rcases hd with rfl | rfl <;> simp [layerCfg, savedSlot, d1Slot, d2Slot] <;> omega_arith) p hp
      simp only [layerCfg] at this
      rw [slotW, b₄, this, hfe j hj p hp, Bool.xor_comm]
  obtain keep_any : ∀ r, r ∉ sboxWrites → ∀ is : List Instr,
      (restRegs.all fun r => is.all fun i => dst i != some r) = true →
      (is.all fun i => dst i != some r) = true := fun r hr is h =>
    List.all_eq_true.mp h r (not_sboxWrites r hr)
  refine ⟨s₄, ?_, hD, hS, ?_, ?_, by rw [rd₄, rd₃, rd₂, rd₁], by rw [wr₄, wr₃, wr₂, wr₁],
    by rw [sp₄, sp₃, sp₂, sp₁], ?_, ?_⟩
  · rw [hcode, runBlock_append', h₁, Option.bind_some, runBlock_append', h₂, Option.bind_some,
      runBlock_append', h₃, Option.bind_some, h₄]
  · intro kv hkv
    have := k₄ kv.1 (List.mem_append_left _ (List.mem_map_of_mem hkv)) (masks_ok s₃ hm₃ kv hkv).1
    simp only [layerCfg] at this
    rw [slotW, b₄, this]; exact hm₃ kv hkv
  · intro j hj hjd
    obtain hb : s₄.gpr sb = s.gpr sb := by rw [b₄, b₃, b₂]
    obtain hmem : d1Slot + j ∈ feistelKeep d := by
      refine List.mem_append_right _ ?_
      simp only [List.mem_map, List.mem_range]
      rcases hd with rfl | rfl
      · exact ⟨j - 8, by simp [d1Slot] at hjd; omega_arith, by simp [d1Slot, d2Slot]; omega_arith⟩
      · exact ⟨j, by simp [d1Slot, d2Slot] at hjd; omega_arith, by simp [d1Slot, d2Slot]⟩
    have := k₄ _ hmem (by simp [layerCfg, savedSlot, d1Slot]; omega_arith)
    simp only [layerCfg] at this
    rw [slotW, b₄, this, ← hh₃ j hj, slotW, b₃]
  · intro r hr
    rw [o₄ r (keep_any r hr _ (by rcases hd with rfl | rfl <;> decide +kernel)),
      o₃ r (keep_any r hr _ (by decide +kernel)), o₂ r hr,
      o₁ r (keep_any r hr _ (by rcases hoff with rfl | rfl <;> decide +kernel))]
  · have e₁ : slotRegion layerCfg s₁ = slotRegion layerCfg s := by
      simp only [slotRegion, layerCfg]; rw [o₁ _ (by rcases hoff with rfl | rfl <;> decide +kernel)]
    obtain e₂ : slotRegion layerCfg s₂ = slotRegion layerCfg s := by
      simp only [slotRegion, layerCfg]; rw [b₂]
    obtain e₃ : slotRegion layerCfg s₃ = slotRegion layerCfg s := by
      simp only [slotRegion, layerCfg]; rw [b₃, b₂]
    refine f₁.trans ((f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      ((e₂ ▸ f₃).trans (e₃ ▸ f₄)))
    simp only [List.mem_singleton] at hr; subst hr
    simp only [slotRegion, sboxCfg, layerCfg]
    rw [o₁ _ (by rcases hoff with rfl | rfl <;> decide +kernel)]
    exact Region.sub_prefix (by simp [savedSlot])

end VG.Proof.Camellia.RISCV64

end

end

/-! ### `Camellia.RISCV64.Moves`, which only this module used -/

section

/-!
# Moving the halves of bitsliced Camellia on RISC-V, by evaluation

As on PPC64LE and x86-64: the loads and stores of the halves (`loadHalf`,
`storeHalf`), and the subkey XORs outside the rounds (the whitening in
`head` and `tail`), checked over the lane domain as the layers are
(`Linear.lean`).
-/

@[expose] public section

namespace VG.Proof.Camellia.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Bitslice VG.Impl.Camellia.RISCV64
open VG.Impl.Aes.RISCV64 (q sb t0 t1 kp)

/-- Each state register `q b` holds input word `b`. -/
def idG (b p : Nat) : List Nat := [64 * b + p]

/-! ## The halves -/

/-- `loadHalf d`: `q j` is the half's plane `j`, input word `8 + (d - d1Slot) + j`. -/
def loadHalfG (d j p : Nat) : List Nat := [64 * (8 + (d - d1Slot) + j) + p]

theorem loadHalf1_check :
    check (lanes 64 12) layerCfg (linExt 24) (loadHalf d1Slot) bothEnv
      (linPostG 12 (qOuts (loadHalfG d1Slot)) [] (maskSlots ++ bothIns.map (·.1)) bothEnv) = true := by
  decide +kernel

theorem loadHalf2_check :
    check (lanes 64 12) layerCfg (linExt 24) (loadHalf d2Slot) bothEnv
      (linPostG 12 (qOuts (loadHalfG d2Slot)) [] (maskSlots ++ bothIns.map (·.1)) bothEnv) = true := by
  decide +kernel

/-- `storeHalf d`: the half's plane `j` is `q j`. -/
def storeHalfOuts (d : Nat) : List (Nat × (Nat → List Nat)) := (List.range 8).map fun j => (d + j, idG j)

theorem storeHalf1_check :
    check (lanes 64 12) layerCfg (linExt 24) (storeHalf d1Slot) bothEnv
      (linPostG 12 (qOuts idG) (storeHalfOuts d1Slot) (feistelKeep d1Slot) bothEnv) = true := by
  decide +kernel

theorem storeHalf2_check :
    check (lanes 64 12) layerCfg (linExt 24) (storeHalf d2Slot) bothEnv
      (linPostG 12 (qOuts idG) (storeHalfOuts d2Slot) (feistelKeep d2Slot) bothEnv) = true := by
  decide +kernel

/-! ## The whitening -/

/-- `keyXor off`: `q j` XOR the subkey's plane `j`, at word `off + j` of `kp`
(input word `24 + off + j`). -/
def keyXorG (off j p : Nat) : List Nat := [64 * j + p, 64 * (24 + off + j) + p]

theorem keyXor8_check :
    check (lanes 64 12) layerCfg (linExt 24) (keyXor 8) bothEnv
      (linPostG 12 (qOuts (keyXorG 8)) [] (maskSlots ++ bothIns.map (·.1)) bothEnv) = true := by
  decide +kernel

theorem keyXor0_check :
    check (lanes 64 12) layerCfg (linExt 24) (keyXor 0) bothEnv
      (linPostG 12 (qOuts (keyXorG 0)) [] (maskSlots ++ bothIns.map (·.1)) bothEnv) = true := by
  decide +kernel

/-- `D2`'s plane `j` XOR the second subkey's. -/
def whiten2G (j p : Nat) : List Nat := [64 * (16 + j) + p, 64 * (32 + j) + p]

theorem whiten_check :
    check (lanes 64 12) layerCfg (linExt 24) whiten bothEnv
      (linPostG 12 (qOuts (keyXorG 0))
        ((List.range 8).map (fun j => (d1Slot + j, keyXorG 0 j)) ++
          (List.range 8).map (fun j => (d2Slot + j, whiten2G j))) maskSlots bothEnv) = true := by
  decide +kernel

end VG.Proof.Camellia.RISCV64

end

end


/-!
# Eight blocks of bitsliced Camellia on RISC-V

As on PPC64LE (`Proof/Camellia/PPC64LE/Crypt8.lean`) and x86-64: with the table of bitsliced subkeys `E 0 … E (8 g + 1)` in
the scratch buffer (`CorePre`), `crypt8` replaces each of the eight blocks
in the tail buffer with `cryptWords g E` of it. Until its last block
(`tail`) it writes only the rounds' working space, below the table (`Ctx`). The rounds are `round_ok`; the pairs of
rounds, the groups of six and the FL layers are loops and blocks around
them, whose invariants are the specification's `pair`, `group` and
`groups` (`Proof/Camellia/Words.lean`).
-/

@[expose] public section

namespace VG.Proof.Camellia.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Bitslice VG.Impl.Camellia.RISCV64
open VG.Impl.Aes.RISCV64 (q sb t0 t1 t2 u7 kp rt movR ldS stS)
open VG.Proof.Aes.RISCV64 (sboxWrites not_sboxWrites restRegs)
open VG.Proof.Camellia (HalfRel WordRel pair group groups cryptWords)

/-- Word `j` of entry `i` of the table, in the scratch buffer at `b`. -/
def entryW (m : Mem) (b : Addr) (i j : Nat) : BitVec 64 :=
  m.readW (b + BitVec.ofNat 64 (8 * keySlot + 64 * i + 8 * j)) 64

/-- What the rounds need: the scratch buffer, writable, the masks, and a
table of `nk` subkeys. -/
structure KeyCtx (s₀ : State) (nk : Nat) (E : Nat → BitVec 64) : Prop where
  scr : (⟨s₀.gpr sb, 8 * slots⟩ : Region) ∈ s₀.wr
  al : (s₀.gpr sb).toNat % 8 = 0
  fit : (s₀.gpr sb).toNat + 8 * slots ≤ 2 ^ 64
  nk34 : nk ≤ 34
  masks : MasksOk s₀
  keys : ∀ i < nk, HalfRel (entryW s₀.mem (s₀.gpr sb) i) fun _ => E i

/-- What `crypt8` needs: the rounds' context, with the table of `8 g + 2`
subkeys, and the address of its postwhitening entry in `r7`. -/
structure CorePre (s₀ : State) (g : Nat) (E : Nat → BitVec 64) : Prop extends KeyCtx s₀ (8 * g + 2) E where
  hg : g = 3 ∨ g = 4
  bound : s₀.gpr .a4 = s₀.gpr sb + BitVec.ofNat 64 (8 * keySlot + 512 * g)

/-- What `crypt8` may write in the scratch buffer at `b`: the rounds' working
space and the tail buffer. -/
def ctxRegions (b : Addr) : List Region :=
  [⟨b, 8 * savedSlot⟩, ⟨b + BitVec.ofNat 64 (8 * tailSlot), 128⟩]

/-- What stays the same: the regions, the registers but the layers', `kp`
and `r3`, the memory outside the rounds' working space and the tail buffer,
and the masks. -/
structure Ctx (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .a0 → s.gpr r = s₀.gpr r
  frame : Frame (ctxRegions (s₀.gpr sb)) s₀.mem s.mem
  masks : MasksOk s

theorem Ctx.refl {s₀ : State} (hm : MasksOk s₀) : Ctx s₀ s₀ :=
  ⟨rfl, rfl, fun _ _ _ _ => rfl, Frame.refl _ _, hm⟩

theorem Ctx.base {s₀ s : State} (hc : Ctx s₀ s) : s.gpr sb = s₀.gpr sb := hc.keep _ (by decide) (by decide) (by decide)

/-- A step that writes only the state's registers, `kp`, `rdi`, the rounds'
working space, and keeps the masks, keeps `Ctx`. -/
theorem Ctx.step {s₀ s s' : State} (hc : Ctx s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hk : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .a0 → s'.gpr r = s.gpr r)
    (hf : Frame [⟨s₀.gpr sb, 8 * savedSlot⟩] s.mem s'.mem) (hm : MasksOk s') :
    Ctx s₀ s' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, fun r h1 h2 h3 => (hk r h1 h2 h3).trans (hc.keep r h1 h2 h3),
    hc.frame.trans (hf.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [ctxRegions, hr]), hm⟩

/-- `Ctx.step`, for a step that may also write the tail buffer. -/
theorem Ctx.stepT {s₀ s s' : State} (hc : Ctx s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hk : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .a0 → s'.gpr r = s.gpr r)
    (hf : Frame (ctxRegions (s₀.gpr sb)) s.mem s'.mem) (hm : MasksOk s') :
    Ctx s₀ s' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, fun r h1 h2 h3 => (hk r h1 h2 h3).trans (hc.keep r h1 h2 h3),
    hc.frame.trans hf, hm⟩

/-! ## Addresses -/

/-- `kp` at entry `m` of the table. -/
def AtEntry (s : State) (b : Addr) (m : Nat) : Prop := s.gpr kp = b + BitVec.ofNat 64 (8 * keySlot + 64 * m)

theorem keyW_entry {s : State} {b : Addr} {m : Nat} (hk : AtEntry s b m) (e j : Nat) :
    keyW s (8 * e + j) = entryW s.mem b (m + e) j := by
  simp only [keyW, wordAddr, entryW]
  rw [hk, addr_add, show 8 * keySlot + 64 * m + 8 * (8 * e + j) = 8 * keySlot + 64 * (m + e) + 8 * j by omega_arith]

theorem slots_eq : slots = 400 := rfl
theorem tailSlot_eq : tailSlot = 96 := rfl
theorem keySlot_eq : keySlot = 128 := rfl
theorem savedSlot_eq : savedSlot = 80 := rfl

theorem ok_layer {s : State} {b : Addr} {m : Nat} (hscr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr)
    (hal : b.toNat % 8 = 0) (hb : s.gpr sb = b) (hk : AtEntry s b m) (hm : m + 2 ≤ 34) :
    Ok layerCfg s where
  baseAl _ := by simp only [layerCfg]; rw [hb]; exact hal
  extAl _ := by simp only [layerCfg]; rw [show s.gpr kp = _ from hk]; exact Spill.al8 hal (by omega_using [])
  slotIn k hk' := ⟨_, hscr, by
    simp only [layerCfg, savedSlot_eq] at hk'
    simp only [wordAddr, layerCfg, hb]
    exact VG.Offset.contains_base b (by rw [slots_eq]; omega_arith) (by omega_arith)⟩
  extIn j hj := ⟨_, List.mem_append_right _ hscr, by
    simp only [layerCfg] at hj
    simp only [wordAddr, layerCfg]
    rw [show s.gpr kp = _ from hk, addr_add]
    exact VG.Offset.contains_base b (by rw [slots_eq, keySlot_eq]; omega_arith) (by rw [keySlot_eq]; omega_arith)⟩
  slots := by simp only [layerCfg, savedSlot_eq]; omega_arith
  sep k hk' j hj := by
    simp only [layerCfg, savedSlot_eq] at hk' hj
    simp only [wordAddr, layerCfg, hb]
    rw [show s.gpr kp = _ from hk, addr_add]
    exact VG.Offset.sep b (by rw [keySlot_eq]; omega_arith) (by omega_arith) (by rw [keySlot_eq]; omega_arith)

/-! ## Under `Ctx` -/

/-- The table's entries are outside what `Ctx` lets the code write. -/
theorem Ctx.entry {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {i j : Nat} (hi : i < 34) (hj : j < 8) :
    entryW s.mem (s₀.gpr sb) i j = entryW s₀.mem (s₀.gpr sb) i j := by
  have hfit := hp.fit
  rw [slots_eq] at hfit
  simp only [entryW]
  refine hc.frame.readW (r := ⟨s₀.gpr sb + BitVec.ofNat 64 (8 * keySlot + 64 * i + 8 * j), 8⟩)
    (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [ctxRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact VG.Offset.disjoint_base _ (by rw [keySlot_eq, savedSlot_eq]; omega_arith) (by rw [keySlot_eq]; omega_arith)
  · exact VG.Offset.disjoint _ (by rw [keySlot_eq, tailSlot_eq]; omega_arith) (by rw [keySlot_eq]; omega_arith)
      (by rw [tailSlot_eq]; omega_arith)

theorem Ctx.keyRel {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m e : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hme : m + e < nk) :
    HalfRel (fun j => keyW s (8 * e + j)) fun _ => E (m + e) := by
  have hg := hp.nk34
  refine (hp.keys _ hme).congr fun j hj => ?_
  rw [keyW_entry hk, hc.entry hp (by omega_arith) hj]

theorem Ctx.ok {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm : m + 2 ≤ 34) : Ok layerCfg s :=
  ok_layer (by rw [hc.wr]; exact hp.scr) hp.al hc.base hk hm

/-- A round, under `Ctx`: `round off d` with the subkey at entry `m + off / 8`. -/
theorem round_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {off d m : Nat}
    (hkc : check (lanes 64 12) layerCfg (linExt 8) (keyXor off ++ inSel) keyInEnv
      (linPostG 12 (qOuts (Camellia.keyInG off)) [] (maskSlots ++ halvesIns.map (·.1)) keyInEnv) = true)
    (hfc : check (lanes 64 12) layerCfg (linExt 24) (feistel d) bothEnv
      (linPostG 12 (qOuts (feistelG d)) ((List.range 8).map fun j => (d + j, feistelG d j))
        (feistelKeep d) bothEnv) = true)
    (hoff : off = 0 ∨ off = 8) (hd : d = d1Slot ∨ d = d2Slot)
    (hk : AtEntry s (s₀.gpr sb) m) (hme : m + off / 8 < nk) (hm34 : m + 2 ≤ 34)
    {X Y : Nat → BitVec 64} (hQ : HalfRel (Qs s) X) (hR : HalfRel (fun j => slotW s (d + j)) Y) :
    ∃ s', runBlock isa (round off d) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      s'.gpr .a0 = s.gpr .a0 ∧
      HalfRel (Qs s') (fun b => Y b ^^^ Spec.Camellia.f (X b) (E (m + off / 8))) ∧
      HalfRel (fun j => slotW s' (d + j)) (fun b => Y b ^^^ Spec.Camellia.f (X b) (E (m + off / 8))) ∧
      (∀ j < 16, d1Slot + j < d ∨ d + 8 ≤ d1Slot + j → slotW s' (d1Slot + j) = slotW s (d1Slot + j)) ∧
      (∀ k, savedSlot ≤ k → k < 2 ^ 58 → slotW s' k = slotW s k) := by
  have hK : HalfRel (fun j => keyW s (off + j)) fun _ => E (m + off / 8) := by
    have := hc.keyRel hp hk (e := off / 8) hme
    rcases hoff with rfl | rfl <;> exact this
  obtain ⟨s', h', hq', hs', hm', hh', rd', wr', -, o', f'⟩ :=
    round_ok hkc hfc hoff hd (hc.ok hp hk hm34) hc.masks hQ hK hR
  have f'' : Frame [⟨s₀.gpr sb, 8 * savedSlot⟩] s.mem s'.mem := by
    refine f'.mono fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    simp only [slotRegion, layerCfg, hc.base]; simp
  refine ⟨s', h', hc.step rd' wr' (fun r hr _ _ => o' r hr) f'' hm', o' _ (by decide),
    o' _ (by decide), hq', hs', hh', fun k hk hk' => ?_⟩
  simp only [slotW, o' sb (by decide), hc.base]; exact slot_above f'' hk hk'

/-! ## Pairs of rounds -/

/-- The halves of the eight blocks, `(D1, D2)` of block `b` in `S b`: `D1` in
the state and in its slots, `D2` in its slots. -/
def Halves (s : State) (S : Nat → BitVec 64 × BitVec 64) : Prop :=
  HalfRel (Qs s) (fun b => (S b).1) ∧ HalfRel (fun j => slotW s (d1Slot + j)) (fun b => (S b).1) ∧
    HalfRel (fun j => slotW s (d2Slot + j)) (fun b => (S b).2)

/-- `add kp, kp, #n`, keeping all else. -/
theorem addKp_ok (s : State) (n : Nat) (hn : n < 2048) :
    ∃ s', runBlock isa [.addi kp kp (OfNat.ofNat n)] s = some s' ∧
      s'.gpr kp = s.gpr kp + BitVec.ofNat 64 n ∧ (∀ r, r ≠ kp → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.write kp (s.gpr kp + BitVec.ofNat 64 n), by
    simp only [runBlock_cons, exec_addi (show imm12 (OfNat.ofNat n : Int) by
        show imm12 ((n : Nat) : Int); unfold imm12; omega_using [hn]), runStep_some, runBlock_nil]
    rw [show (OfNat.ofNat n : Int) = ((n : Nat) : Int) from rfl, Steps.ofInt_ofNat],
    RegUpd.gpr_write_self _ _ _,
    fun r hr => RegUpd.gpr_write_of_ne _ _ hr, rfl, rfl, rfl⟩

/-- `sub d, n, m`, keeping all else. -/
theorem subR_ok (s : State) (d n m : Reg) :
    ∃ s', runBlock isa [.sub d n m] s = some s' ∧ s'.gpr d = s.gpr n - s.gpr m ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.write d (s.gpr n - s.gpr m), by
    simp only [runBlock_cons]; rfl,
    RegUpd.gpr_write_self _ _ _,
    fun r hr => RegUpd.gpr_write_of_ne _ _ hr, rfl, rfl, rfl⟩

/-- The two rounds of a pair, `kp += 128` and `t0 := kp - r3`. -/
theorem pair_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm : m + 1 < nk) (hm34 : m + 2 ≤ 34)
    {S : Nat → BitVec 64 × BitVec 64} (hS : Halves s S) :
    ∃ s', runBlock isa pairBody s = some s' ∧ Ctx s₀ s' ∧ AtEntry s' (s₀.gpr sb) (m + 2) ∧
      s'.gpr .a0 = s.gpr .a0 ∧ Halves s' (fun b => pair (E m) (E (m + 1)) (S b)) ∧
      s'.gpr t0 = s'.gpr kp - s.gpr .a0 := by
  obtain ⟨hq, h1, h2⟩ := hS
  obtain ⟨s₁, e₁, c₁, k₁, r₁, q₁, d₁, o₁, -⟩ := round_step hp hc (off := 0) (d := d2Slot) keyIn0_check
    feistel2_check (by decide) (by decide) hk (by omega_arith) hm34 hq h2
  have h1' : HalfRel (fun j => slotW s₁ (d1Slot + j)) (fun b => (S b).1) :=
    h1.congr fun j hj => o₁ j (by omega_arith) (Or.inl (by simp [d1Slot, d2Slot]; omega_arith))
  obtain ⟨s₂, e₂, c₂, k₂, r₂, q₂, d₂, o₂, -⟩ := round_step hp c₁ (off := 8) (d := d1Slot) keyIn8_check
    feistel1_check (by decide) (by decide) (by rw [AtEntry, k₁]; exact hk) (by omega_arith) hm34 q₁ h1'
  have d₂' : HalfRel (fun j => slotW s₂ (d2Slot + j))
      (fun b => (S b).2 ^^^ Spec.Camellia.f (S b).1 (E (m + 0 / 8))) :=
    d₁.congr fun j hj => by
      have := o₂ (8 + j) (by omega_arith) (Or.inr (by simp only [d1Slot]; omega_arith))
      rw [show d1Slot + (8 + j) = d2Slot + j by simp [d1Slot, d2Slot]; omega_arith] at this
      exact this
  obtain ⟨s₃, e₃, kp₃, o₃, m₃, rd₃, wr₃⟩ := addKp_ok s₂ 128 (by decide)
  obtain ⟨s₄, e₄, z₄, g₄', m₄, rd₄, wr₄⟩ := subR_ok s₃ t0 kp .a0
  have g₄ : ∀ r, r ≠ t0 → s₄.gpr r = s₃.gpr r := g₄'
  have hrdi : s₂.gpr .a0 = s.gpr .a0 := by rw [r₂, r₁]
  refine ⟨s₄, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pairBody, runBlock_append', runBlock_append', e₁, Option.bind_some, e₂, Option.bind_some,
      show ([.addi kp kp 128, .sub t0 kp .a0] : List Instr) =
        [.addi kp kp 128] ++ [.sub t0 kp .a0] from rfl,
      runBlock_append', e₃, Option.bind_some, e₄]
  · refine c₂.step (by rw [rd₄, rd₃]) (by rw [wr₄, wr₃])
      (fun r h1 h2 _ => by rw [g₄ r (fun h => h1 (by subst h; decide)), o₃ r h2])
      (by rw [m₄, m₃]; exact Frame.refl _ _) ?_
    intro kv hkv
    simp only [slotW, g₄ sb (by decide), m₄, m₃, o₃ sb (by decide)]
    exact c₂.masks kv hkv
  · simp only [AtEntry, g₄ kp (by decide), kp₃, k₂, k₁]
    rw [show s.gpr kp = _ from hk, addr_add,
      show 8 * keySlot + 64 * m + 128 = 8 * keySlot + 64 * (m + 2) by omega_arith]
  · rw [g₄ _ (by decide), o₃ _ (by decide), hrdi]
  · refine ⟨q₂.congr fun j hj => ?_, d₂.congr fun j hj => ?_, d₂'.congr fun j hj => ?_⟩
    · simp only [Qs, g₄ _ (q_ne_t0 j hj), o₃ _ (q_ne_kp j hj)]
    · simp only [slotW, g₄ sb (by decide), m₄, m₃, o₃ sb (by decide)]
    · simp only [slotW, g₄ sb (by decide), m₄, m₃, o₃ sb (by decide)]
  · rw [z₄, g₄ kp (by decide), o₃ .a0 (by decide), hrdi]

/-! ## Moving halves -/

/-- The input words of `bothEnv`: the state, both halves, the subkey's 16 words. -/
def bothW (s : State) (i : Nat) : BitVec 64 :=
  if i < 8 then Qs s i else if i < 24 then slotW s (d1Slot + (i - 8)) else keyW s (i - 24)

/-- A check over `bothEnv`, on the machine. -/
theorem both_ok {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm34 : m + 2 ≤ 34) {is : List Instr}
    {outs : List (Reg × (Nat → List Nat))} {souts : List (Nat × (Nat → List Nat))} {keep : List Nat}
    (hchk : check (lanes 64 12) layerCfg (linExt 24) is bothEnv (linPostG 12 outs souts keep bothEnv) = true) :
    ∃ s', runBlock isa is s = some s' ∧
      (∀ r g, (r, g) ∈ outs → ∀ p < 64, (s'.gpr r).getLsbD p = xorBits (bothW s) (g p)) ∧
      (∀ j g, (j, g) ∈ souts → j < savedSlot →
        ∀ p < 64, (slotW s' j).getLsbD p = xorBits (bothW s) (g p)) ∧
      (∀ j ∈ keep, j < savedSlot → slotW s' j = slotW s j) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, (is.all fun i => dst i != some r) = true → s'.gpr r = s.gpr r) ∧
      Frame [⟨s₀.gpr sb, 8 * savedSlot⟩] s.mem s'.mem := by
  unfold bothEnv at hchk
  obtain ⟨s', h', ho, hso, hkp, rd', wr', -, o', f', hb', -⟩ := linG_ok hchk (hc.ok hp hk hm34) (bothW s)
    (fun r i hri => by
      simp only [qIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hri
      obtain ⟨i, hi, rfl, rfl⟩ := hri
      exact ⟨by omega_arith, by simp [bothW, hi]⟩)
    (fun j i hji => by
      simp only [bothIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hji
      obtain ⟨j, hj, rfl, rfl⟩ := hji
      refine ⟨by simp [layerCfg, d1Slot, savedSlot]; omega_arith, by omega_arith, ?_⟩
      simp [bothW, show ¬ 8 + j < 8 by omega_arith, show 8 + j < 24 by omega_arith]; rfl)
    (fun kv hkv => ⟨by have := allMasks_slots kv hkv; simp only [layerCfg, savedSlot, d1Slot] at this ⊢; omega_using [this],
        hc.masks kv hkv⟩)
    (fun j hj => by
      simp only [layerCfg] at hj
      exact ⟨by omega_arith, by simp [bothW, show ¬ 24 + j < 8 by omega_arith, show ¬ 24 + j < 24 by omega_arith]; rfl⟩)
  simp only [layerCfg] at hb' hso hkp f'
  refine ⟨s', h', ho, fun j g hjg hj p hp => ?_, fun j hj hjk => ?_, rd', wr', o', ?_⟩
  · rw [slotW, hb']; exact hso j g hjg hj p hp
  · rw [slotW, hb']; exact hkp j hj hjk
  · simp only [slotRegion, hc.base] at f'; exact f'

theorem bothW_q (s : State) {j : Nat} (hj : j < 8) : bothW s j = Qs s j := by simp [bothW, hj]

theorem bothW_half (s : State) {d j : Nat} (hd : d = d1Slot ∨ d = d2Slot) (hj : j < 8) :
    bothW s (8 + (d - d1Slot) + j) = slotW s (d + j) := by
  have h1 : ¬ 8 + (d - d1Slot) + j < 8 := by omega_arith
  have h2 : 8 + (d - d1Slot) + j < 24 := by rcases hd with rfl | rfl <;> simp only [d1Slot, d2Slot] <;> omega_arith
  have h3 : d1Slot + (8 + (d - d1Slot) + j - 8) = d + j := by
    rcases hd with rfl | rfl <;> simp only [d1Slot, d2Slot] <;> omega_arith
  simp only [bothW, h1, h2, ↓reduceIte, h3]

/-- `loadHalf d`, under `Ctx`. -/
theorem loadHalf_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m d : Nat} (hd : d = d1Slot ∨ d = d2Slot)
    (hchk : check (lanes 64 12) layerCfg (linExt 24) (loadHalf d) bothEnv
      (linPostG 12 (qOuts (loadHalfG d)) [] (maskSlots ++ bothIns.map (·.1)) bothEnv) = true)
    (hk : AtEntry s (s₀.gpr sb) m) (hm34 : m + 2 ≤ 34) :
    ∃ s', runBlock isa (loadHalf d) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      s'.gpr .a0 = s.gpr .a0 ∧ (∀ j < 8, Qs s' j = slotW s (d + j)) ∧
      (∀ j < 16, slotW s' (d1Slot + j) = slotW s (d1Slot + j)) ∧
      (∀ k, savedSlot ≤ k → k < 2 ^ 58 → slotW s' k = slotW s k) := by
  obtain ⟨s', h', ho, -, hkp, rd', wr', o', f'⟩ := both_ok hp hc hk hm34 hchk
  have hq : ∀ j < 8, Qs s' j = slotW s (d + j) := fun j hj => BitVec.eq_of_getLsbD_eq fun p hp => by
    rw [Qs, ho (q j) (loadHalfG d j) (by simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
      p hp, loadHalfG, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hp, bothW_half s hd hj]
  have hh : ∀ j < 16, slotW s' (d1Slot + j) = slotW s (d1Slot + j) := fun j hj =>
    hkp _ (List.mem_append_right _ (by
      simp only [bothIns, List.map_map, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩))
      (by simp only [d1Slot, savedSlot]; omega_arith)
  have hall : (restRegs.all fun r => (loadHalf d).all fun i => dst i != some r) =
      true := by rcases hd with rfl | rfl <;> decide +kernel
  have hkeep : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r := fun r hr =>
    o' r (List.all_eq_true.mp hall r (not_sboxWrites r hr))
  refine ⟨s', h', hc.step rd' wr' (fun r hr _ _ => hkeep r hr) (f'.mono fun r hr => by simp at hr; simp [hr])
    (fun kv hkv => ?_), hkeep _ (by decide), hkeep _ (by decide), hq, hh, fun k hk hk' => by
      simp only [slotW, hkeep sb (by decide), hc.base]; exact slot_above f' hk hk'⟩
  rw [hkp kv.1 (List.mem_append_left _ (List.mem_map_of_mem hkv)) (by
      have := allMasks_slots kv hkv; simp only [savedSlot, d1Slot] at this ⊢; omega_using [this])]
  exact hc.masks kv hkv

/-- `storeHalf d`, under `Ctx`. -/
theorem storeHalf_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m d : Nat} (hd : d = d1Slot ∨ d = d2Slot)
    (hchk : check (lanes 64 12) layerCfg (linExt 24) (storeHalf d) bothEnv
      (linPostG 12 (qOuts idG) (storeHalfOuts d) (feistelKeep d) bothEnv) = true)
    (hk : AtEntry s (s₀.gpr sb) m) (hm34 : m + 2 ≤ 34) :
    ∃ s', runBlock isa (storeHalf d) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      s'.gpr .a0 = s.gpr .a0 ∧ (∀ j < 8, Qs s' j = Qs s j) ∧ (∀ j < 8, slotW s' (d + j) = Qs s j) ∧
      (∀ j < 16, d1Slot + j < d ∨ d + 8 ≤ d1Slot + j → slotW s' (d1Slot + j) = slotW s (d1Slot + j)) ∧
      (∀ k, savedSlot ≤ k → k < 2 ^ 58 → slotW s' k = slotW s k) := by
  obtain ⟨s', h', ho, hso, hkp, rd', wr', o', f'⟩ := both_ok hp hc hk hm34 hchk
  have hq : ∀ j < 8, Qs s' j = Qs s j := fun j hj => BitVec.eq_of_getLsbD_eq fun p hp => by
    rw [Qs, ho (q j) (idG j) (by simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
      p hp, idG, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hp, bothW_q s hj]
  have hs : ∀ j < 8, slotW s' (d + j) = Qs s j := fun j hj => BitVec.eq_of_getLsbD_eq fun p hp => by
    rw [hso (d + j) (idG j) (by simp only [storeHalfOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
      (by rcases hd with rfl | rfl <;> simp only [d1Slot, d2Slot, savedSlot] <;> omega_arith) p hp,
      idG, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hp, bothW_q s hj]
  have hh : ∀ j < 16, d1Slot + j < d ∨ d + 8 ≤ d1Slot + j → slotW s' (d1Slot + j) = slotW s (d1Slot + j) :=
    fun j hj hjd => hkp _ (List.mem_append_right _ (by
      simp only [List.mem_map, List.mem_range]
      rcases hd with rfl | rfl
      · exact ⟨j - 8, by simp only [d1Slot] at hjd; omega_arith, by simp [d1Slot, d2Slot]; omega_arith⟩
      · exact ⟨j, by simp only [d1Slot, d2Slot] at hjd; omega_arith, by simp [d1Slot, d2Slot]⟩))
      (by simp only [d1Slot, savedSlot]; omega_arith)
  have hall : (restRegs.all fun r => (storeHalf d).all fun i => dst i != some r) =
      true := by rcases hd with rfl | rfl <;> decide +kernel
  have hkeep : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r := fun r hr =>
    o' r (List.all_eq_true.mp hall r (not_sboxWrites r hr))
  refine ⟨s', h', hc.step rd' wr' (fun r hr _ _ => hkeep r hr) (f'.mono fun r hr => by simp at hr; simp [hr])
    (fun kv hkv => ?_), hkeep _ (by decide), hkeep _ (by decide), hq, hs, hh, fun k hk hk' => by
      simp only [slotW, hkeep sb (by decide), hc.base]; exact slot_above f' hk hk'⟩
  rw [hkp kv.1 (List.mem_append_left _ (List.mem_map_of_mem hkv)) (by
      have := allMasks_slots kv hkv; simp only [savedSlot, d1Slot] at this ⊢; omega_using [this])]
  exact hc.masks kv hkv

/-- What FL reads, under `Ctx`. -/
theorem Ctx.flMem {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m off : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hoff : off = 0 ∨ off = 8) (hm34 : m + 2 ≤ 34) :
    FlMem s off (fun i => keyW s (off + i)) := by
  have hok := hc.ok hp hk hm34
  have hm := hc.masks
  refine ⟨fun i hi => ⟨hok.extIn (off + i) (by simp only [layerCfg]; omega_arith), rfl⟩,
    by rcases hoff with rfl | rfl <;> decide, hok.extAl (by simp [layerCfg]),
    hok.baseAl (by simp [layerCfg, savedSlot]), ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · obtain ⟨r, hr, hc'⟩ := hok.slotIn oddSlot (by simp [layerCfg, oddSlot, savedSlot])
    exact ⟨r, List.mem_append_right _ hr, hc'⟩
  · exact hm (oddSlot, _) (by simp [allMasks, layerMasks])
  · obtain ⟨r, hr, hc'⟩ := hok.slotIn evenSlot (by simp [layerCfg, evenSlot, savedSlot])
    exact ⟨r, List.mem_append_right _ hr, hc'⟩
  · exact hm (evenSlot, _) (by simp [allMasks, layerMasks])

/-- The temporaries of FL are among the layers' registers. -/
theorem fl_temps : ∀ r : Reg, (r ∈ sboxWrites ∨ r = kp ∨ r = .a0) ∨
    ((∀ i < 8, r ≠ q i) ∧ r ≠ t0 ∧ r ≠ u7 ∧ r ≠ t1 ∧ r ≠ t2 ∧ r ≠ rt) := by
  intro r; cases r <;> decide

/-- What a run that writes only the state's registers and the temporaries keeps. -/
theorem Ctx.regs {s₀ s s' : State} (hc : Ctx s₀ s) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr)
    (hk : ∀ r, (∀ i < 8, r ≠ q i) → r ≠ t0 → r ≠ u7 → r ≠ t1 → r ≠ t2 → r ≠ rt → s'.gpr r = s.gpr r) :
    Ctx s₀ s' := by
  have hk' : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r := fun r hr => by
    rcases fl_temps r with (h | h | h) | ⟨h1, h2, h3, h4, h5, h6⟩
    · exact absurd h hr
    · subst h; exact hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · subst h; exact hk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact hk r h1 h2 h3 h4 h5 h6
  refine hc.step hrd hwr (fun r hr _ _ => hk' r hr) (by rw [hm]; exact Frame.refl _ _) fun kv hkv => ?_
  simp only [slotW, hm, hk' sb (by decide)]
  exact hc.masks kv hkv

/-- FL (`flCode`) or FLINV (`flinvCode`) on the state, with the subkey at entry `m + off / 8`. -/
theorem flCode_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m off : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hoff : off = 0 ∨ off = 8)
    (hme : m + off / 8 < nk) (hm34 : m + 2 ≤ 34) {X : Nat → BitVec 64} (hQ : HalfRel (Qs s) X) :
    (∃ s', runBlock isa (flCode off) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      s'.gpr .a0 = s.gpr .a0 ∧ s'.mem = s.mem ∧
      HalfRel (Qs s') (fun b => Spec.Camellia.fl (X b) (E (m + off / 8)))) ∧
    (∃ s', runBlock isa (flinvCode off) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      s'.gpr .a0 = s.gpr .a0 ∧ s'.mem = s.mem ∧
      HalfRel (Qs s') (fun b => Spec.Camellia.flinv (X b) (E (m + off / 8)))) := by
  have hK : HalfRel (fun j => keyW s (off + j)) fun _ => E (m + off / 8) := by
    have := hc.keyRel hp hk (e := off / 8) hme
    rcases hoff with rfl | rfl <;> exact this
  have hf := hc.flMem hp hk hoff hm34
  have hqkp : ∀ i < 8, kp ≠ q i := fun i hi h => q_ne_kp i hi h.symm
  have hqrdi : ∀ i < 8, Reg.a0 ≠ q i := fun i hi h => by revert i; decide
  constructor
  · obtain ⟨s₁, e₁, g₁, o₁, m₁, rd₁, wr₁⟩ := flRot_ok hf
    have hf₁ := hf.congr m₁ rd₁ wr₁ (o₁ _ hqkp (by decide) (by decide) (by decide) (by decide) (by decide))
      (o₁ _ (fun i hi h => q_ne_sb i hi h.symm) (by decide) (by decide) (by decide) (by decide) (by decide))
    obtain ⟨s₂, e₂, g₂, o₂, m₂, rd₂, wr₂⟩ := flOr_ok hf₁
    refine ⟨s₂, by rw [flCode, runBlock_append', e₁, Option.bind_some, e₂], ?_, ?_, ?_, by rw [m₂, m₁], ?_⟩
    · exact (hc.regs m₁ rd₁ wr₁ o₁).regs m₂ rd₂ wr₂ fun r h1 h2 h3 _ h5 h6 => o₂ r h1 h2 h3 h5 h6
    · rw [o₂ _ hqkp (by decide) (by decide) (by decide) (by decide),
        o₁ _ hqkp (by decide) (by decide) (by decide) (by decide) (by decide)]
    · rw [o₂ _ hqrdi (by decide) (by decide) (by decide) (by decide),
        o₁ _ hqrdi (by decide) (by decide) (by decide) (by decide) (by decide)]
    · exact Camellia.fl_rel hQ hK (rotStep_of g₁) (orStep_of g₂)
  · obtain ⟨s₁, e₁, g₁, o₁, m₁, rd₁, wr₁⟩ := flOr_ok hf
    have hf₁ := hf.congr m₁ rd₁ wr₁ (o₁ _ hqkp (by decide) (by decide) (by decide) (by decide))
      (o₁ _ (fun i hi h => q_ne_sb i hi h.symm) (by decide) (by decide) (by decide) (by decide))
    obtain ⟨s₂, e₂, g₂, o₂, m₂, rd₂, wr₂⟩ := flRot_ok hf₁
    refine ⟨s₂, by rw [flinvCode, runBlock_append', e₁, Option.bind_some, e₂], ?_, ?_, ?_, by rw [m₂, m₁], ?_⟩
    · exact (hc.regs m₁ rd₁ wr₁ fun r h1 h2 h3 _ h5 h6 => o₁ r h1 h2 h3 h5 h6).regs m₂ rd₂ wr₂ o₂
    · rw [o₂ _ hqkp (by decide) (by decide) (by decide) (by decide) (by decide),
        o₁ _ hqkp (by decide) (by decide) (by decide) (by decide)]
    · rw [o₂ _ hqrdi (by decide) (by decide) (by decide) (by decide) (by decide),
        o₁ _ hqrdi (by decide) (by decide) (by decide) (by decide)]
    · exact Camellia.flinv_rel hQ hK (orStep_of g₁) (rotStep_of g₂)

theorem slotW_congr {s₀ s s' : State} (hc : Ctx s₀ s) (hc' : Ctx s₀ s') (hm : s'.mem = s.mem) (k : Nat) :
    slotW s' k = slotW s k := by simp only [slotW, hm, hc.base, hc'.base]

/-- The FL layer: FLINV on `D2` with entry `m + 1`, FL on `D1` with entry `m`. -/
theorem fl_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm : m + 1 < nk) (hm34 : m + 2 ≤ 34)
    {S : Nat → BitVec 64 × BitVec 64} (hS : Halves s S) :
    ∃ s', runBlock isa flLayer s = some s' ∧ Ctx s₀ s' ∧ AtEntry s' (s₀.gpr sb) (m + 2) ∧
      s'.gpr .a0 = s.gpr .a0 ∧
      Halves s' (fun b => (Spec.Camellia.fl (S b).1 (E m), Spec.Camellia.flinv (S b).2 (E (m + 1)))) := by
  obtain ⟨-, h1, h2⟩ := hS
  -- FLINV on `D2`.
  obtain ⟨s₁, e₁, c₁, k₁, r₁, q₁, hh₁, -⟩ := loadHalf_step hp hc (Or.inr rfl) loadHalf2_check hk hm34
  have hq₁ : HalfRel (Qs s₁) (fun b => (S b).2) := h2.congr fun j hj => q₁ j hj
  have hk₁ : AtEntry s₁ (s₀.gpr sb) m := by rw [AtEntry, k₁]; exact hk
  obtain ⟨s₂, e₂, c₂, k₂, r₂, m₂, hq₂⟩ := (flCode_step hp c₁ hk₁ (off := 8) (Or.inr rfl) (by omega_arith) hm34 hq₁).2
  have hk₂ : AtEntry s₂ (s₀.gpr sb) m := by rw [AtEntry, k₂]; exact hk₁
  obtain ⟨s₃, e₃, c₃, k₃, r₃, q₃, sl₃, hh₃, -⟩ := storeHalf_step hp c₂ (Or.inr rfl) storeHalf2_check hk₂ hm34
  have hk₃ : AtEntry s₃ (s₀.gpr sb) m := by rw [AtEntry, k₃]; exact hk₂
  have d1₃ : ∀ j < 8, slotW s₃ (d1Slot + j) = slotW s (d1Slot + j) := fun j hj => by
    rw [hh₃ j (by omega_arith) (Or.inl (by simp only [d1Slot, d2Slot]; omega_arith)), slotW_congr c₁ c₂ m₂,
      hh₁ j (by omega_arith)]
  have d2₃ : HalfRel (fun j => slotW s₃ (d2Slot + j))
      (fun b => Spec.Camellia.flinv (S b).2 (E (m + 8 / 8))) := hq₂.congr fun j hj => sl₃ j hj
  -- FL on `D1`.
  obtain ⟨s₄, e₄, c₄, k₄, r₄, q₄, hh₄, -⟩ := loadHalf_step hp c₃ (Or.inl rfl) loadHalf1_check hk₃ hm34
  have hq₄ : HalfRel (Qs s₄) (fun b => (S b).1) := h1.congr fun j hj => by rw [q₄ j hj, d1₃ j hj]
  have hk₄ : AtEntry s₄ (s₀.gpr sb) m := by rw [AtEntry, k₄]; exact hk₃
  obtain ⟨s₅, e₅, c₅, k₅, r₅, m₅, hq₅⟩ := (flCode_step hp c₄ hk₄ (off := 0) (Or.inl rfl) (by omega_arith) hm34 hq₄).1
  have hk₅ : AtEntry s₅ (s₀.gpr sb) m := by rw [AtEntry, k₅]; exact hk₄
  obtain ⟨s₆, e₆, c₆, k₆, r₆, q₆, sl₆, hh₆, -⟩ := storeHalf_step hp c₅ (Or.inl rfl) storeHalf1_check hk₅ hm34
  have d2₆ : HalfRel (fun j => slotW s₆ (d2Slot + j))
      (fun b => Spec.Camellia.flinv (S b).2 (E (m + 8 / 8))) := d2₃.congr fun j hj => by
    have := hh₆ (8 + j) (by omega_arith) (Or.inr (by simp only [d1Slot]; omega_arith))
    rw [show d1Slot + (8 + j) = d2Slot + j by simp only [d1Slot, d2Slot]; omega_arith] at this
    have h4 := hh₄ (8 + j) (by omega_arith)
    rw [show d1Slot + (8 + j) = d2Slot + j by simp only [d1Slot, d2Slot]; omega_arith] at h4
    rw [this, slotW_congr c₄ c₅ m₅, h4]
  -- `add kp, 128`.
  obtain ⟨s₇, e₇, kp₇, o₇, m₇, rd₇, wr₇⟩ := addKp_ok s₆ 128 (by decide)
  have hq₇ : ∀ j < 8, Qs s₇ j = Qs s₆ j := fun j hj => o₇ _ (q_ne_kp j hj)
  have hs₇ : ∀ k, slotW s₇ k = slotW s₆ k := fun k => by simp only [slotW, m₇, o₇ sb (by decide)]
  refine ⟨s₇, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩⟩
  · rw [flLayer, runBlock_append', runBlock_append', runBlock_append', runBlock_append', runBlock_append',
      runBlock_append', e₁, Option.bind_some, e₂, Option.bind_some, e₃, Option.bind_some, e₄,
      Option.bind_some, e₅, Option.bind_some, e₆, Option.bind_some]
    exact e₇
  · refine c₆.step rd₇ wr₇ (fun r _ h2 _ => o₇ r h2) (by rw [m₇]; exact Frame.refl _ _) fun kv hkv => ?_
    rw [hs₇]; exact c₆.masks kv hkv
  · simp only [AtEntry, kp₇, k₆, k₅, k₄, k₃, k₂, k₁]
    rw [show s.gpr kp = _ from hk, addr_add,
      show 8 * keySlot + 64 * m + 128 = 8 * keySlot + 64 * (m + 2) by omega_arith]
  · rw [o₇ _ (by decide), r₆, r₅, r₄, r₃, r₂, r₁]
  · exact hq₅.congr fun j hj => by rw [hq₇ j hj, q₆ j hj]
  · exact hq₅.congr fun j hj => by rw [hs₇, sl₆ j hj]
  · exact d2₆.congr fun j hj => hs₇ _

/-! ## Groups of six rounds -/

/-- A step that changes only `t0` keeps `Ctx`. -/
theorem Ctx.t0 {s₀ s s' : State} (hc : Ctx s₀ s) (hg : ∀ r, r ≠ t0 → s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Ctx s₀ s' :=
  hc.step hrd hwr (fun r h1 _ _ => hg r fun h => h1 (by subst h; decide))
    (by rw [hm]; exact Frame.refl _ _) fun kv hkv => by
      simp only [slotW, hm, hg sb (by decide)]; exact hc.masks kv hkv

theorem entry_beq (b : Addr) {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (b + BitVec.ofNat 64 x - (b + BitVec.ofNat 64 y) == 0) = decide (x = y) := by
  rw [VG.Offset.add_sub_add_left, VG.Offset.ofNat_sub_ofNat_beq hx hy]

/-- `bnez r`: whether `r` is not zero. -/
theorem eval_nonzero (s : State) (r : Reg) : isa.eval (.nonzero r) s = some !(s.gpr r == 0) := rfl

/-- `beqz r`: whether `r` is zero. -/
theorem eval_zero (s : State) (r : Reg) : isa.eval (.zero r) s = some (s.gpr r == 0) := rfl

theorem ofNat_beq_zero {v : Nat} (hv : v < 2 ^ 64) : (BitVec.ofNat 64 v == 0) = decide (v = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h; have := congrArg BitVec.toNat h; rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv] at this
  · intro h; rw [h]; rfl

/-- `addi a0, kp, 384`. -/
theorem setBound_ok (s : State) :
    ∃ s', runBlock isa [.addi .a0 kp 384] s = some s' ∧
      s'.gpr .a0 = s.gpr kp + BitVec.ofNat 64 384 ∧ (∀ r, r ≠ .a0 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.write .a0 (s.gpr kp + BitVec.ofNat 64 384), by
    simp only [runBlock_cons, exec_addi (show imm12 384 by decide), runStep_some, runBlock_nil]; rfl,
    RegUpd.gpr_write_self _ _ _,
    fun r hr => RegUpd.gpr_write_of_ne _ _ hr, rfl, rfl, rfl⟩

theorem Halves.congr {s s' : State} {S : Nat → BitVec 64 × BitVec 64} (h : Halves s S)
    (hq : ∀ j < 8, Qs s' j = Qs s j) (hs : ∀ k, slotW s' k = slotW s k) : Halves s' S :=
  ⟨h.1.congr hq, h.2.1.congr fun _ _ => hs _, h.2.2.congr fun _ _ => hs _⟩

/-- A step that changes only `r3` keeps everything. -/
theorem Ctx.flags {s₀ s s' : State} (hc : Ctx s₀ s) (hg : ∀ r, r ≠ .a0 → s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Ctx s₀ s' :=
  hc.step hrd hwr (fun r _ _ h3 => hg r h3) (by rw [hm]; exact Frame.refl _ _) fun kv hkv => by
    simp only [slotW, hm, hg sb (by decide)]; exact hc.masks kv hkv

theorem entry_lt {g i : Nat} (hg : g ≤ 4) (hi : i ≤ 8 * g + 2) : 8 * keySlot + 64 * i < 2 ^ 64 := by
  rw [keySlot_eq]; omega_arith

/-- The postwhitening's address stays in `r7`. -/
theorem Ctx.a4 {s₀ s : State} (hc : Ctx s₀ s) : s.gpr .a4 = s₀.gpr .a4 :=
  hc.keep _ (by decide) (by decide) (by decide)

/-- `sub t0, kp, a4`: whether `kp` is at the postwhitening's entry. -/
theorem endTest_ok {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm : m ≤ 8 * g + 2) :
    ∃ s', runBlock isa [.sub t0 kp .a4] s = some s' ∧ Ctx s₀ s' ∧ AtEntry s' (s₀.gpr sb) m ∧
      (s'.gpr t0 == 0) = decide (m = 8 * g) ∧ (∀ j < 8, Qs s' j = Qs s j) ∧
      (∀ k, slotW s' k = slotW s k) := by
  have hg4 : g ≤ 4 := by rcases hp.hg with h | h <;> omega_arith
  obtain ⟨s', e', z', g', m', rd', wr'⟩ := subR_ok s t0 kp .a4
  have g'' : ∀ r, r ≠ t0 → s'.gpr r = s.gpr r := g'
  refine ⟨s', e', hc.t0 g'' m' rd' wr', by rw [AtEntry, g'' _ (by decide)]; exact hk, ?_,
    fun j hj => g'' _ (q_ne_t0 j hj), fun k => by simp only [slotW, g'' sb (by decide), m']⟩
  rw [z', show s.gpr kp = _ from hk, hc.a4, hp.bound, show 512 * g = 64 * (8 * g) by omega_arith,
    entry_beq _ (entry_lt hg4 hm) (entry_lt hg4 (by omega_arith))]
  simp only [decide_eq_decide]; omega_arith

/-- A group of six rounds, then FL and FLINV unless it is the last. -/
theorem group_wp {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s)
    {i : Nat} (hi : i < g) (hk : AtEntry s (s₀.gpr sb) (2 + 8 * i)) {S : Nat → BitVec 64 × BitVec 64}
    (hS : Halves s S) :
    WP isa groupBody s fun s' => Ctx s₀ s' ∧ Halves s' (fun b => group g E (S b) i) ∧
      AtEntry s' (s₀.gpr sb) (if i + 1 < g then 2 + 8 * (i + 1) else 8 * g) ∧
      (s'.gpr t0 == 0) = decide (i + 1 = g) := by
  have hg4 : g ≤ 4 := by rcases hp.hg with h | h <;> omega_arith
  let b := s₀.gpr sb
  -- The bound of the pairs.
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := setBound_ok s
  have hc₁ : Ctx s₀ s₁ := hc.flags (fun r hr => o₁ r hr) m₁ rd₁ wr₁
  have hk₁ : AtEntry s₁ b (2 + 8 * i) := by rw [AtEntry, o₁ kp (by decide)]; exact hk
  have hrdi₁ : s₁.gpr .a0 = b + BitVec.ofNat 64 (8 * keySlot + 64 * (8 + 8 * i)) := by
    rw [r₁, show s.gpr kp = _ from hk, addr_add,
      show 8 * keySlot + 64 * (2 + 8 * i) + 384 = 8 * keySlot + 64 * (8 + 8 * i) by omega_arith]
  have hS₁ : Halves s₁ S := hS.congr (fun j hj => o₁ _ (fun h => by revert j; decide))
    (fun k => by simp only [slotW, m₁, o₁ sb (by decide)])
  unfold groupBody
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  -- The pairs.
  let Inv : Nat → State → Prop := fun n s' => ∃ p, n = 3 - p ∧ p < 3 ∧ Ctx s₀ s' ∧
    AtEntry s' b (2 + 8 * i + 2 * p) ∧ s'.gpr .a0 = s₁.gpr .a0 ∧
    Halves s' (fun b => pairsN E i p (S b))
  let Mid : State → Prop := fun s' => Ctx s₀ s' ∧ AtEntry s' b (8 + 8 * i) ∧
    Halves s' (fun b => pairsN E i 3 (S b))
  refine WP.seq (WP.mono (Q := Mid) (WP.loop Inv (fun n s' hs' => ?_) 3 s₁
    ⟨0, rfl, by omega_arith, hc₁, by simpa using hk₁, rfl, by simpa [pairsN] using hS₁⟩) fun s₂ h₂ => ?_)
  · obtain ⟨p, rfl, hp3, hc', hk', hr', hS'⟩ := hs'
    obtain ⟨s'', e'', c'', k'', r'', S'', z''⟩ := pair_step hp.toKeyCtx hc' hk' (by omega_arith) (by omega_arith) hS'
    refine WP.of_runBlock ⟨s'', e'', ?_⟩
    have hz : (s''.gpr t0 == 0) = decide (p + 1 = 3) := by
      rw [z'', show s''.gpr kp = _ from k'', hr', hrdi₁, entry_beq b (entry_lt hg4 (by omega_arith))
        (entry_lt hg4 (by omega_arith))]
      simp only [decide_eq_decide]; omega_arith
    have hS'' : Halves s'' (fun b => pairsN E i (p + 1) (S b)) := by
      simpa only [pairsN_succ, show 2 + 8 * i + 2 * p + 1 = 3 + 8 * i + 2 * p by omega_arith] using S''
    by_cases hp2 : p + 1 = 3
    · refine .inl ⟨(eval_nonzero s'' t0).trans (by rw [hz]; simp [hp2]), c'', ?_, by rw [← hp2]; exact hS''⟩
      rw [AtEntry, show s''.gpr kp = _ from k'', show 2 + 8 * i + 2 * p + 2 = 8 + 8 * i by omega_arith]
    · refine .inr ⟨(eval_nonzero s'' t0).trans (by rw [hz]; simp [hp2]), 3 - (p + 1), by omega_arith, p + 1, rfl, by omega_arith, c'',
        by rw [AtEntry, show s''.gpr kp = _ from k'', show 2 + 8 * i + 2 * p + 2 = 2 + 8 * i + 2 * (p + 1) by omega_arith],
        by rw [r'', hr'], hS''⟩
  · obtain ⟨hc₂, hk₂, hS₂⟩ := h₂
    obtain ⟨s₃, e₃, hc₃, hk₃, hz₃, q₃, sl₃⟩ := endTest_ok hp hc₂ hk₂ (by omega_arith)
    have hS₃ : Halves s₃ (fun b => pairsN E i 3 (S b)) := hS₂.congr q₃ sl₃
    refine WP.seq (WP.of_runBlock ⟨s₃, e₃, ?_⟩)
    refine WP.seq (WP.ite (!decide (8 + 8 * i = 8 * g)) ((eval_nonzero s₃ t0).trans (by rw [hz₃])) (fun ht => ?_)
      (fun hf => ?_))
    · have hlt : i + 1 < g := by
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at ht; omega_arith
      obtain ⟨s₄, e₄, c₄, k₄, -, S₄⟩ := fl_step hp.toKeyCtx hc₃ hk₃ (by omega_arith) (by omega_arith) hS₃
      refine WP.of_runBlock ⟨s₄, e₄, ?_⟩
      have hk₄ : AtEntry s₄ b (2 + 8 * (i + 1)) := by
        rw [AtEntry, show s₄.gpr kp = _ from k₄, show 8 + 8 * i + 2 = 2 + 8 * (i + 1) by omega_arith]
      obtain ⟨s₅, e₅, c₅, k₅, z₅, q₅, sl₅⟩ := endTest_ok hp c₄ hk₄ (by omega_arith)
      refine WP.of_runBlock ⟨s₅, e₅, c₅, ?_, ?_, ?_⟩
      · have hG : (fun b => group g E (S b) i) = fun b =>
            (Spec.Camellia.fl (pairsN E i 3 (S b)).1 (E (8 + 8 * i)),
              Spec.Camellia.flinv (pairsN E i 3 (S b)).2 (E (8 + 8 * i + 1))) :=
          funext fun b => by
            rw [group_eq, show 8 + 8 * i + 1 = 9 + 8 * i by omega_arith]; simp only [hlt, ↓reduceIte]
        rw [hG]
        exact S₄.congr q₅ sl₅
      · simp only [hlt, ↓reduceIte]; exact k₅
      · rw [z₅]; simp only [decide_eq_decide]; omega_arith
    · have heq : i + 1 = g := by
        simp only [Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq] at hf; omega_arith
      refine WP.of_runBlock ⟨s₃, rfl, ?_⟩
      obtain ⟨s₅, e₅, c₅, k₅, z₅, q₅, sl₅⟩ := endTest_ok hp hc₃ hk₃ (by omega_arith)
      refine WP.of_runBlock ⟨s₅, e₅, c₅, ?_, ?_, ?_⟩
      · have hG : (fun b => group g E (S b) i) = fun b => pairsN E i 3 (S b) :=
          funext fun b => by rw [group_eq]; simp only [show ¬ i + 1 < g by omega_arith, ↓reduceIte]
        rw [hG]
        exact hS₃.congr q₅ sl₅
      · simp only [show ¬ i + 1 < g by omega_arith, ↓reduceIte]
        rw [show 8 * g = 8 + 8 * i by omega_arith]; exact k₅
      · rw [z₅]; simp only [decide_eq_decide]; omega_arith

end VG.Proof.Camellia.RISCV64

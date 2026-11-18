module

public import VerifiedGarbage.Proof.Sm4.Scratch
public import VerifiedGarbage.Impl.StackScratch.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Impl.StackScratch.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.TCB.PPC64LE.Target
meta import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchWipe
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RegSet
public import VerifiedGarbage.Impl.Sm4.PPC64LE.ExpandKey
public import VerifiedGarbage.Proof.Sm4.PPC64LE.Ecb
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Sm4.Common
import VerifiedGarbage.Proof.Sm4.Layout
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sm4.PPC64LE.LayersLit
import VerifiedGarbage.Proof.Sm4.Planes
public import VerifiedGarbage.Proof.Sm4.PPC64LE.Round
meta import VerifiedGarbage.Impl.Sm4.PPC64LE.ExpandKey
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.Ecb
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Sm4.Common
meta import VerifiedGarbage.Proof.Sm4.Layout
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.LayersLit
meta import VerifiedGarbage.Proof.Sm4.Planes
meta import VerifiedGarbage.Proof.Sm4.PPC64LE.Round

/-! ### `Sm4.PPC64LE.KeyEk`, which this module and modules that import it used -/

section

/-! ### `Sm4.PPC64LE.KeyInit`, which only this module used -/

section

/-!
# The start of the SM4 key schedule on PPC64LE

As on x86-64: the planes of `CK` stored as constants (through
`setSlotsN_ok`), and `MK ⊕ FK` stored to the sixteen blocks of the tail
buffer (`loadHalf_ok`), whose words, bitsliced, are the key schedule's
initial state `keyInit`.
-/

@[expose] public section

namespace VG.Proof.Sm4.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.Sm4.PPC64LE
open VG.Impl.Aes.PPC64LE (q sb t0 t1 movR ldS stS xorR imm64)
open VG.Impl.Sm4 (planeOf fkWord)

/-! ## Stores of a register -/

/-- `std r, 8 k(sb)` for each `k` of `ks`. -/
theorem storeAll_ok (r : Reg) : ∀ (ks : List Nat) {s : State} {b : Addr}, s.gpr sb = b →
    (⟨b, 8 * slots⟩ : Region) ∈ s.wr → (∀ k ∈ ks, k < slots) →
    ∃ s', runBlock isa (ks.map fun k => stS k r) s = some s' ∧ (∀ k ∈ ks, slotW s' k = s.gpr r) ∧
      (∀ k < slots, k ∉ ks → slotW s' k = slotW s k) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨b, 8 * slots⟩] s.mem s'.mem
  | [], s, _, _, _, _ => ⟨s, rfl, by simp, fun _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | k :: ks, s, b, hb, hw, hk => by
    have hk0 : k < slots := hk k List.mem_cons_self
    have e₁ := stS_ok s r (k := k) (by rw [slots_eq] at hk0; omega_using [hk0]) ⟨_, hw, by
      rw [hb]; exact VG.Offset.contains_base b (by omega_using [hk0]) (by rw [slots_eq] at hk0; omega_using [hk0])⟩
    let s₁ : State := { s with mem := s.mem.writeW (wordAddr (s.gpr sb) k) (s.gpr r) }
    obtain ⟨s', e', v', o', g', rd', wr', f'⟩ := storeAll_ok r ks (s := s₁) hb hw
      fun k h => hk k (List.mem_cons_of_mem _ h)
    have hslot : ∀ j < slots, slotW s₁ j = if j = k then s.gpr r else slotW s j := fun j hj => by
      simp only [slotW, s₁]
      exact readW_slot_write _ hj hk0
    refine ⟨s', by rw [List.map_cons, show (stS k r :: ks.map fun k => stS k r) = [stS k r] ++ ks.map fun k => stS k r
        from rfl, runBlock_app, e₁, Option.bind_some]; exact e', fun j hj => ?_, fun j hj hn => ?_,
      by rw [g'], by rw [rd'], by rw [wr'], ?_⟩
    · rcases List.mem_cons.mp hj with rfl | hj'
      · by_cases hin : j ∈ ks
        · rw [v' j hin]
        · rw [o' j hk0 hin, hslot j hk0, ite_eq_left rfl]
      · rw [v' j hj']
    · simp only [List.mem_cons, not_or] at hn
      rw [o' j hj hn.2, hslot j hj, ite_eq_right hn.1]
    · refine Frame.trans (fun x hx => ?_) f'
      simp only [s₁, Mem.writeW, Mem.write, wordAddr, hb]
      exact ite_eq_right fun h => hx _ (List.mem_singleton_self _) (VG.Offset.sub_base b
        (show 8 * k + 8 ≤ 8 * slots by omega_using [hk0]) _ (by simp only [Region.Contains]; omega_using [h]))

/-! ## `MK ⊕ FK` -/

/-- `ld d, n(r)`. -/
theorem loadAt_ok (s : State) (d r : Reg) (n : Nat) (hn : n % 8 = 0 ∧ n < 32768) (hr0 : r ≠ .r0)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr r + BitVec.ofNat 64 n) 8) :
    ∃ s', runBlock isa [.load .d d r n] s = some s' ∧
      s'.gpr d = s.mem.readW (s.gpr r + BitVec.ofNat 64 n) 64 ∧
      (∀ r', r' ≠ d → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  have u := Upd.write s d (s.mem.readW (s.gpr r + BitVec.ofNat 64 n) 64)
  ⟨_, by simp only [runBlock_cons, exec_load_d hr0 ⟨hn.2, by omega_using [hn]⟩ hr, runStep_some, runBlock_nil],
    u.gpr, u.other, u.mem, u.rd, u.wr⟩

/-- `xor d, d, r`. -/
theorem xorReg_ok (s : State) (d r : Reg) :
    ∃ s', runBlock isa [xorR d d r] s = some s' ∧ s'.gpr d = s.gpr d ^^^ s.gpr r ∧
      (∀ r', r' ≠ d → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  have u := Upd.write s d (s.gpr d ^^^ s.gpr r)
  ⟨_, by simp only [xorR, runBlock_cons, exec_logic, runStep_some, runBlock_nil], u.gpr, u.other, u.mem, u.rd, u.wr⟩

/-- `ld t0, 8 h(r3); imm64 t1, FK; xor t0, t0, t1`. -/
theorem keyWord_ok (s : State) (h : Nat) (hh : h < 2)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 (8 * h)) 8) :
    ∃ s', runBlock isa (([.load .d t0 .r3 (8 * h)] : List Instr) ++ imm64 t1 (fkWord h) ++ ([xorR t0 t0 t1] : List Instr)) s = some s' ∧
      s'.gpr t0 = s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 (8 * h)) 64 ^^^ fkWord h ∧
      (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := loadAt_ok s t0 .r3 (8 * h) ⟨by omega_using [], by omega_using [hh]⟩ (by decide) hr
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂⟩ := imm_ok s₁ t1 (fkWord h)
  obtain ⟨s₃, e₃, v₃, o₃, m₃, rd₃, wr₃⟩ := xorReg_ok s₂ t0 t1
  refine ⟨s₃, ?_, ?_, fun r h0 h1 => by rw [o₃ r h0, o₂ r h1, o₁ r h0], by rw [m₃, m₂, m₁],
    by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁]⟩
  · rw [runBlock_app, runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some, e₃]
  · rw [v₃, o₂ _ (by decide), v₁, v₂]

theorem tailAt_lt {b h : Nat} (hb : b < 16) (hh : h < 2) : tailAt b h < slots := by
  simp only [tailAt, tailSlot_eq, slots_eq]; omega_using [hb, hh]

/-- Half `h` of the key, XOR `FK`, to the sixteen blocks. -/
theorem loadHalf_ok {s : State} {b : Addr} (h : Nat) (hh : h < 2) (hb : s.gpr sb = b)
    (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .r3 + BitVec.ofNat 64 (8 * h)) 8) :
    ∃ s', runBlock isa (loadHalf h) s = some s' ∧
      (∀ c < 16, slotW s' (tailAt c h) = s.mem.readW (s.gpr .r3 + BitVec.ofNat 64 (8 * h)) 64 ^^^ fkWord h) ∧
      (∀ k < slots, (∀ c < 16, k ≠ tailAt c h) → slotW s' k = slotW s k) ∧
      (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨b, 8 * slots⟩] s.mem s'.mem := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := keyWord_ok s h hh hr
  obtain ⟨s', e', v', k', g', rd', wr', f'⟩ := storeAll_ok t0 ((List.range 16).map fun c => tailAt c h)
    (s := s₁) (by rw [o₁ _ (by decide) (by decide), hb]) (by rw [wr₁]; exact hw)
    (fun k hk => by simp only [List.mem_map, List.mem_range] at hk; obtain ⟨c, hc, rfl⟩ := hk
                    exact tailAt_lt hc hh)
  refine ⟨s', ?_, fun c hc => ?_, fun k hk hne => ?_, fun r h0 h1 => by rw [g', o₁ r h0 h1], by rw [rd', rd₁],
    by rw [wr', wr₁], by rw [← m₁]; exact f'⟩
  · rw [loadHalf, runBlock_app, e₁, Option.bind_some]
    simpa only [List.map_map, Function.comp_def] using e'
  · rw [v' _ (by simp only [List.mem_map, List.mem_range]; exact ⟨c, hc, rfl⟩), v₁]
  · rw [k' k hk (by simp only [List.mem_map, List.mem_range, not_exists, not_and]; exact fun c hc h' => hne c hc h'.symm)]
    simp only [slotW, m₁, o₁ sb (by decide) (by decide)]

end VG.Proof.Sm4.PPC64LE

end

end

/-! ### `Sm4.PPC64LE.KeyLoop`, which only this module used -/

section

/-!
# The loop of the SM4 key schedule on PPC64LE

Each iteration runs four rounds of the key schedule (`rounds4_ok .key`),
puts the state's words in the tail buffer as a block (`fromBs_step`), and
stores them to the schedule as little-endian words (`extract_ok`): the
first block's 64-bit words, byte-reversed (`rev`).
-/

@[expose] public section

namespace VG.Proof.Sm4.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.Sm4.PPC64LE
open VG.Impl.Aes.PPC64LE (q sb t0 t1 movR ldS stS)
open VG.Impl.Sm4 (planeOf fkWord)
open VG.Proof.Sm4 (WordRel quads ofBlock outBlock keyInit rkOf readW64_bit getLsbD_outBlock' ofInt_nat)

/-! ## Bytes -/

theorem rev64_bit (x : BitVec 64) {t j : Nat} (ht : t < 8) (hj : j < 8) :
    (rev64 x).getLsbD (8 * t + j) = x.getLsbD (8 * (7 - t) + j) := by
  rw [show (rev64 x).getLsbD (8 * t + j) = x.getLsbD (8 * (7 - (8 * t + j) / 8) + (8 * t + j) % 8) from
    VG.byteRev64_getLsbD x (by omega_arith)]
  exact congrArg x.getLsbD (by omega_arith)

/-- A byte of a word written. -/
theorem writeW_byte (m : Mem) (a : Addr) (v : BitVec 64) {t j : Nat} (ht : t < 8) (hj : j < 8) :
    ((m.writeW a v) (a + BitVec.ofNat 64 t)).getLsbD j = v.getLsbD (8 * t + j) := by
  simp only [Mem.writeW, Mem.write, BitVec.setWidth_eq, VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega_arith)]
  simp only [show t < 64 / 8 by omega_arith, ↓reduceIte, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]

/-- A byte outside a word written. -/
theorem writeW_other (m : Mem) (a x : Addr) (v : BitVec 64) (h : ¬ (x - a).toNat < 8) :
    (m.writeW a v) x = m x := by
  simp only [Mem.writeW, Mem.write]
  exact ite_eq_right fun h' => h (by simpa using h')

/-- A word written inside `R`. -/
theorem frame_writeW' {m : Mem} {a : Addr} {R : Region} (v : BitVec 64) (hs : Region.Sub ⟨a, 8⟩ R) :
    Frame [R] m (m.writeW a v) := VG.Proof.Sm4.frame_writeW v hs

/-! ## Single instructions -/

/-- `li r12, n; stdbrx v, r4, r12`. -/
theorem storeRevAt_ok (s : State) (v : Reg) (n : Nat) (hv : v ≠ .r12) (hn : n < 2 ^ 15)
    (hw : InRegions s.wr (s.gpr .r4 + BitVec.ofNat 64 n) 8) :
    ∃ s', runBlock isa [.li .r12 n, .storeRev .d v .r4 .r12] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .r4 + BitVec.ofNat 64 n) (rev64 (s.gpr v)) ∧
      (∀ r, r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain u := Upd.write s .r12 (BitVec.ofNat 64 n)
  let s₁ := s.write .r12 (BitVec.ofNat 64 n)
  obtain h4 : s₁.gpr .r4 = s.gpr .r4 := u.other _ (by decide)
  refine ⟨{ s₁ with mem := s₁.mem.writeW (s₁.gpr .r4 + s₁.gpr .r12) (rev64 (s₁.gpr v)) }, ?_, ?_, u.other,
    u.rd, u.wr⟩
  · have hw' : InRegions s₁.wr (s₁.gpr .r4 + s₁.gpr .r12) 8 := by rw [h4, u.gpr, u.wr]; exact hw
    simp only [runBlock_cons, exec_li hn, runStep_some]
    rw [exec_storeRev_d (show Reg.r4 ≠ .r0 by decide) hw', runStep_some, runBlock_nil]
  · show Mem.writeW _ _ _ = _
    rw [h4, u.gpr, u.other v hv, u.mem]

/-- A byte of the tail buffer's block `0`. -/
theorem tail_byte (s : State) {h t j : Nat} (hh : h < 2) (ht : t < 8) (hj : j < 8) :
    (slotW s (tailAt 0 h)).getLsbD (8 * t + j) = ((tailBlock s 0)[8 * h + t]'(by omega_arith)).getLsbD j := by
  rw [slotW, readW64_bit _ _ ht hj]
  simp only [tailBlock, Spec.Sm4.blockAt, Vector.getElem_ofFn, wordAddr, addr_add, tailAt]
  rw [show 8 * (tailSlot + 2 * 0 + h) + t = 8 * tailSlot + 16 * 0 + (8 * h + t) by omega_arith]

/-! ## The extraction -/

/-- The schedule's bytes `16 m … 16 m + 15`: the words of the tail buffer's
first block, the last first, each little-endian. -/
theorem extract_ok {s : State} {b S : Addr} {m : Nat} (hm : m < 8) (hb : s.gpr sb = b)
    (hr8 : s.gpr .r4 = S + BitVec.ofNat 64 (16 * m))
    (hS : ∀ t < 2, InRegions s.wr (S + BitVec.ofNat 64 (16 * m + 8 * t)) 8)
    (hT : ∀ t < 2, InRegions (s.rd ++ s.wr) (wordAddr b (tailAt 0 t)) 8)
    (hsep : ∀ t < 2, Mem.Sep (wordAddr b (tailAt 0 t)) 8 (S + BitVec.ofNat 64 (16 * m)) 8) :
    ∃ s', runBlock isa extract s = some s' ∧
      (∀ t < 16, ∀ j < 8, (s'.mem (S + BitVec.ofNat 64 (16 * m + t))).getLsbD j =
        ((tailBlock s 0)[15 - t]'(by omega_arith)).getLsbD j) ∧
      Frame [⟨S + BitVec.ofNat 64 (16 * m), 16⟩] s.mem s'.mem ∧
      (∀ r, r ≠ t0 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldMask_ok (r := t0) (k := tailAt 0 1) (by simp only [tailAt, tailSlot_eq]; omega_arith)
    (by rw [hb]; exact hT 1 (by decide)) rfl
  obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃⟩ := storeRevAt_ok s₁ t0 0 (by decide) (by decide)
    (by rw [wr₁, o₁ _ (by decide), hr8, addr_add, Nat.add_zero]
        have := hS 0 (by decide); simpa using this)
  obtain hb₃ : s₃.gpr sb = b := by rw [g₃ _ (by decide), o₁ _ (by decide), hb]
  obtain ⟨s₄, e₄, v₄, o₄, m₄, rd₄, wr₄⟩ := ldMask_ok (s := s₃) (r := t0) (k := tailAt 0 0)
    (by simp only [tailAt, tailSlot_eq]; omega_arith) (by rw [rd₃, wr₃, rd₁, wr₁, hb₃]; exact hT 0 (by decide)) rfl
  obtain ⟨s₆, e₆, m₆, g₆, rd₆, wr₆⟩ := storeRevAt_ok s₄ t0 8 (by decide) (by decide)
    (by rw [wr₄, wr₃, wr₁, o₄ _ (by decide), g₃ _ (by decide), o₁ _ (by decide), hr8, addr_add]
        exact hS 1 (by decide))
  obtain hr8₄ : s₄.gpr .r4 = S + BitVec.ofNat 64 (16 * m) := by
    rw [o₄ _ (by decide), g₃ _ (by decide), o₁ _ (by decide), hr8]
  obtain hr8₁ : s₁.gpr .r4 = S + BitVec.ofNat 64 (16 * m) := by rw [o₁ _ (by decide), hr8]
  obtain q0 : s₄.gpr t0 = slotW s (tailAt 0 0) := by
    rw [v₄]
    simp only [slotW, m₃, m₁, hb₃, hb, hr8₁, addr_add, Nat.add_zero]
    rw [Mem.readW_writeW_sep (hsep 0 (by decide)) (by decide)]
  obtain hm6 : s₆.mem = (s.mem.writeW (S + BitVec.ofNat 64 (16 * m)) (rev64 (slotW s (tailAt 0 1)))).writeW
      (S + BitVec.ofNat 64 (16 * m + 8)) (rev64 (slotW s (tailAt 0 0))) := by
    rw [m₆, m₄, m₃, m₁, hr8₄, q0, hr8₁, v₁, addr_add, addr_add, Nat.add_zero]
  refine ⟨s₆, ?_, fun t ht j hj => ?_, ?_, fun r hr h12 => ?_, by rw [rd₆, rd₄, rd₃, rd₁],
    by rw [wr₆, wr₄, wr₃, wr₁]⟩
  · rw [extract, show ([ldS t0 (tailAt 0 1), .li .r12 0, .storeRev .d t0 .r4 .r12, ldS t0 (tailAt 0 0),
        .li .r12 8, .storeRev .d t0 .r4 .r12] : List Instr) = [ldS t0 (tailAt 0 1)] ++
        ([.li .r12 0, .storeRev .d t0 .r4 .r12] ++ ([ldS t0 (tailAt 0 0)] ++
        [.li .r12 8, .storeRev .d t0 .r4 .r12])) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₃, Option.bind_some,
      runBlock_app, e₄, Option.bind_some, e₆]
  · rw [hm6]
    by_cases h8 : t < 8
    · rw [writeW_other _ _ _ _ (VG.Proof.Sm4.off_sub_not S (Or.inl (by omega_arith)) (by omega_arith) (by decide) (by omega_arith)),
        ← addr_add, writeW_byte _ _ _ h8 hj, rev64_bit _ h8 hj, tail_byte s (by decide) (by omega_arith) hj]
      simp only [show 8 * 1 + (7 - t) = 15 - t by omega_arith]
    · rw [show S + BitVec.ofNat 64 (16 * m + t) = S + BitVec.ofNat 64 (16 * m + 8) + BitVec.ofNat 64 (t - 8) by
          rw [addr_add, show 16 * m + 8 + (t - 8) = 16 * m + t by omega_arith], writeW_byte _ _ _ (by omega_arith) hj,
        rev64_bit _ (by omega_arith) hj, tail_byte s (by decide) (by omega_arith) hj]
      simp only [show 8 * 0 + (7 - (t - 8)) = 15 - t by omega_arith]
  · rw [hm6]
    exact (frame_writeW' _ (VG.Offset.sub S (by omega_arith) (by omega_arith))).trans
      (frame_writeW' _ (VG.Offset.sub S (by omega_arith) (by omega_arith)))
  · rw [g₆ r h12, o₄ r hr, g₃ r h12, o₁ r hr]

/-! ## The loop -/

/-- What the loop keeps, after `m` of its eight iterations: the state holds
the key schedule's words after `4 m` rounds, and the schedule its first
`4 m` round keys. -/
structure EkInv (s₀ : State) (b S : Addr) (key : Spec.Sm4.Block) (m : Nat) (s : State) : Prop where
  base : s.gpr sb = b
  r4 : s.gpr .r4 = S + BitVec.ofNat 64 (16 * m)
  r11 : s.gpr .r11 = b + BitVec.ofNat 64 (8 * tableEnd)
  kr : AtEntry s b (4 * m)
  keys : KeyCtx s Spec.Sm4.ck
  masks : MasksOk s
  st : StRel s (fun _ => quads .key Spec.Sm4.ck m (keyInit key))
  sched : ∀ i < 4 * m, ∀ c < 4, ∀ j < 8,
    (s.mem (S + BitVec.ofNat 64 (4 * i + c))).getLsbD j = (rkOf key i).getLsbD (8 * c + j)
  saved : Saved s₀ b s.mem
  frame : Frame [⟨b, 8 * slots⟩, ⟨S, 128⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The scratch buffer and the schedule, writable and apart. -/
structure EkPre (s₀ : State) (b S : Addr) : Prop where
  scr : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr
  sch : (⟨S, 128⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨S, 128⟩ ⟨b, 8 * slots⟩
  fit : b.toNat + 8 * slots ≤ 2 ^ 64
  fitS : S.toNat + 128 ≤ 2 ^ 64

theorem ekIter_ok {s₀ : State} {b S : Addr} {key : Spec.Sm4.Block} (hp : EkPre s₀ b S) {m : Nat} (hm : m < 8)
    {s : State} (hi : EkInv s₀ b S key m s) :
    ∃ s', runBlock isa keyBody s = some s' ∧ EkInv s₀ b S key (m + 1) s' ∧
      (s'.gpr t0 == 0) = decide (m + 1 = 8) := by
  have hfit := hp.fit
  have hfitS := hp.fitS
  rw [slots_eq] at hfit
  obtain hc0 : Ctx s s := Ctx.refl hi.masks
  -- Four rounds.
  obtain ⟨s₁, e₁, c₁, k₁, X₁⟩ := rounds4_ok .key hi.keys hc0 (by rw [hi.base]; exact hi.kr) hm hi.st
  obtain ⟨s₂, e₂, kr₂, o₂, m₂, rd₂, wr₂⟩ := addKp_ok s₁ 256 (by decide)
  obtain c₂ : Ctx s s₂ := c₁.kr o₂ m₂ rd₂ wr₂
  obtain X₂ : StRel s₂ (fun _ => quads .key Spec.Sm4.ck (m + 1) (keyInit key)) :=
    X₁.congr fun k => by simp only [slotW, m₂, o₂ sb (by decide)]
  -- The words to the tail buffer.
  obtain ⟨s₃, e₃, c₃, kr₃, X₃, T₃⟩ := fromBs_step hi.keys c₂ X₂
  obtain base₃ : s₃.gpr sb = b := by rw [c₃.base, hi.base]
  obtain r8₃ : s₃.gpr .r4 = S + BitVec.ofNat 64 (16 * m) := by rw [c₃.keep _ (by decide) (by decide), hi.r4]
  obtain wr₃ : s₃.wr = s₀.wr := by rw [c₃.wr, hi.wr]
  obtain rd₃ : s₃.rd = s₀.rd := by rw [c₃.rd, hi.rd]
  obtain inS : ∀ t < 2, InRegions s₃.wr (S + BitVec.ofNat 64 (16 * m + 8 * t)) 8 := fun t ht =>
    ⟨_, by rw [wr₃]; exact hp.sch, VG.Offset.contains_base S (by omega_arith) (by omega_arith)⟩
  obtain inT : ∀ t < 2, InRegions (s₃.rd ++ s₃.wr) (wordAddr b (tailAt 0 t)) 8 := fun t ht =>
    ⟨_, List.mem_append_right _ (by rw [wr₃]; exact hp.scr), by
      rw [wordAddr]; exact VG.Offset.contains_base b (by rw [tailAt, tailSlot_eq, slots_eq]; omega_arith)
        (by rw [tailAt, tailSlot_eq]; omega_arith)⟩
  obtain sepTS : ∀ k < slots, Region.Disjoint ⟨wordAddr b k, 8⟩ ⟨S + BitVec.ofNat 64 (16 * m), 16⟩ := fun k hk =>
    (hp.sep.sub_left (VG.Offset.sub_base S (by omega_arith))).sub_right
      (VG.Offset.sub_base b (by rw [slots_eq] at hk ⊢; omega_arith)) |>.symm
  -- To the schedule.
  obtain ⟨s₄, e₄, B₄, f₄, o₄, rd₄, wr₄⟩ := extract_ok hm base₃ r8₃ inS inT
    (fun t ht => fun x h1 h2 => sepTS _ (tailAt_lt (by decide) ht) x h1 (by
      simp only [Region.Contains] at h2 ⊢; omega_arith))
  obtain keep₄ : ∀ k < slots, slotW s₄ k = slotW s₃ k := fun k hk => by
    simp only [slotW, o₄ sb (by decide) (by decide), base₃]
    exact f₄.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sepTS k hk) (by decide)
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := addI_ok s₄ .r4 .r4 (imm := 16) (by decide)
  obtain ⟨s₆, e₆, z₆, g₆, m₆, rd₆, wr₆⟩ := subR_ok s₅ t0 kr .r11
  obtain mem₆ : s₆.mem = s₄.mem := by rw [m₆, m₅]
  obtain g₆' : ∀ r, r ≠ .r4 → r ≠ t0 → r ≠ .r12 → s₆.gpr r = s₃.gpr r := fun r h1 h2 h3 => by rw [g₆ r h2, o₅ r h1, o₄ r h2 h3]
  obtain base₆ : s₆.gpr sb = b := by rw [g₆' _ (by decide) (by decide) (by decide), base₃]
  obtain keep₆ : ∀ k < slots, slotW s₆ k = slotW s₃ k := fun k hk => by
    rw [← keep₄ k hk]; simp only [slotW, mem₆, g₆' sb (by decide) (by decide) (by decide), o₄ sb (by decide) (by decide)]
  obtain kr₆ : AtEntry s₆ b (4 * (m + 1)) := by
    rw [AtEntry, g₆' _ (by decide) (by decide) (by decide), kr₃, kr₂, k₁, show s.gpr kr = _ from hi.kr, addr_add,
      show 8 * tableSlot + 64 * (4 * m) + 256 = 8 * tableSlot + 64 * (4 * (m + 1)) by omega_arith]
  obtain rdi₆ : s₆.gpr .r11 = b + BitVec.ofNat 64 (8 * tableEnd) := by
    rw [g₆' _ (by decide) (by decide) (by decide), c₃.keep _ (by decide) (by decide), hi.r11]
  obtain hent : ∀ (st : State) e j, entryW st.mem (st.gpr sb) e j = slotW st (tableSlot + 8 * e + j) := fun st e j => by
    simp only [entryW, slotW, wordAddr]; rw [show 8 * (tableSlot + 8 * e + j) = 8 * tableSlot + 64 * e + 8 * j by omega_arith]
  obtain key₃ := hi.keys.of_ctx c₃
  -- The schedule's bytes outside this iteration's.
  obtain old₆ : ∀ x, (∀ r ∈ [(⟨b, 8 * tableSlot⟩ : Region), ⟨S + BitVec.ofNat 64 (16 * m), 16⟩], ¬ r.Contains x 1) →
      s₆.mem x = s.mem x := fun x hx => by
    rw [mem₆, f₄ x (fun r hr => hx r (by simp at hr; simp [hr])),
      c₃.frame x (fun r hr => by simp at hr; subst hr; rw [hi.base]; exact hx _ (by simp))]
  refine ⟨s₆, ?_, ⟨base₆, ?_,
    rdi₆, kr₆, ⟨by rw [base₆, wr₆, wr₅, wr₄, wr₃]; exact hp.scr, by rw [base₆]; rw [slots_eq]; exact hfit,
      fun e he => (key₃.keys e he).congr fun j hj => by
        rw [hent s₆, hent s₃, keep₆ _ (by rw [tableSlot_eq, slots_eq]; omega_arith)]⟩,
    fun kv hkv => by rw [keep₆ _ (by have := mask_lt hkv; rw [slots_eq]; omega_arith)]; exact c₃.masks kv hkv,
    fun w hw => (X₃ w hw).congr fun j hj => keep₆ _ (by simp only [stateSlot, slots_eq]; omega_arith),
    fun i hi' c hc j hj => ?_, fun i hi' => ?_, ?_, by rw [rd₆, rd₅, rd₄, rd₃], by rw [wr₆, wr₅, wr₄, wr₃]⟩, ?_⟩
  · rw [keyBody, runBlock_app, runBlock_app, runBlock_app, runBlock_app, e₁, Option.bind_some,
      e₂, Option.bind_some,
      e₃, Option.bind_some, e₄, Option.bind_some,
      show ([.addi .r4 .r4 16, .sub t0 kr .r11] : List Instr) =
        [.addi .r4 .r4 16] ++ [.sub t0 kr .r11] from rfl, runBlock_app, e₅, Option.bind_some, e₆]
  · rw [g₆ _ (by decide), r₅, o₄ _ (by decide) (by decide), r8₃, addr_add, show 16 * m + 16 = 16 * (m + 1) by omega_arith]
  · by_cases hnew : 4 * m ≤ i
    · have ht : 4 * (i - 4 * m) + c < 16 := by omega_arith
      obtain hB := B₄ _ ht j hj
      rw [show 16 * m + (4 * (i - 4 * m) + c) = 4 * i + c by omega_arith] at hB
      rw [mem₆, hB, T₃ 0 (by decide), getLsbD_outBlock' _ _ hj]
      simp only [rkOf]
      rw [show i / 4 + 1 = m + 1 by omega_arith, show 3 - (15 - (4 * (i - 4 * m) + c)) / 4 = i % 4 by omega_arith,
        show 8 * (3 - (15 - (4 * (i - 4 * m) + c)) % 4) + j = 8 * c + j by omega_arith]
    · rw [old₆ _ (fun r hr => ?_)]
      · exact hi.sched i (by omega_arith) c hc j hj
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · intro hc'
          exact hp.sep (S + BitVec.ofNat 64 (4 * i + c)) (VG.Offset.contains_base S (by omega_arith) (by omega_arith))
            (Region.sub_prefix (show 8 * tableSlot ≤ 8 * slots by rw [tableSlot_eq, slots_eq]; omega_arith) _ hc')
        · exact VG.Proof.Sm4.not_contains_off S (Or.inl (by omega_arith)) (by omega_arith) (by decide) (by omega_arith)
  · have hk : savedSlot + i < slots := by rw [savedSlot_eq, slots_eq]; omega_arith
    obtain h1 : s₆.mem.readW (wordAddr b (savedSlot + i)) 64 = s₃.mem.readW (wordAddr b (savedSlot + i)) 64 := by
      have := keep₆ _ hk; simp only [slotW, base₆, base₃] at this; exact this
    obtain h2 : s₃.mem.readW (wordAddr b (savedSlot + i)) 64 = s.mem.readW (wordAddr b (savedSlot + i)) 64 :=
      c₃.frame.readW (r := ⟨wordAddr b (savedSlot + i), 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [hi.base, wordAddr]
        exact VG.Offset.disjoint_base _ (by rw [tableSlot_eq, savedSlot_eq]; omega_arith) (by rw [savedSlot_eq]; omega_arith))
        (by decide)
    rw [h1, h2]; exact hi.saved i hi'
  · rw [mem₆]
    refine hi.frame.trans ((c₃.frame.sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, ?_⟩).trans
      (f₄.sub fun r hr => ⟨⟨S, 128⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩))
    · simp only [List.mem_singleton] at hr; subst hr; rw [hi.base]
      exact Region.sub_prefix (by rw [tableSlot_eq, slots_eq]; omega_arith)
    · simp only [List.mem_singleton] at hr; subst hr; exact VG.Offset.sub_base S (by omega_arith)
  · rw [z₆, o₅ _ (by decide), o₅ _ (by decide), o₄ _ (by decide) (by decide), o₄ _ (by decide) (by decide), kr₃, kr₂, k₁,
      show s.gpr kr = _ from hi.kr, c₃.keep _ (by decide) (by decide), hi.r11, addr_add,
      show 8 * tableSlot + 64 * (4 * m) + 256 = 8 * tableSlot + 64 * (4 * (m + 1)) by omega_arith,
      show 8 * tableEnd = 8 * tableSlot + 64 * 32 by rw [tableSlot_eq, tableEnd_eq],
      entry_beq _ (by rw [tableSlot_eq]; omega_arith) (by rw [tableSlot_eq]; omega_arith)]
    simp only [decide_eq_decide]; omega_arith

end VG.Proof.Sm4.PPC64LE

end

end


/-!
# The SM4 key schedule on PPC64LE: the whole function

`expandKey_wp`: with the working space as an argument (`expandKeyPPC64LE`),
`expandKey` saves the callee-saved registers, sets the masks, stores the
table of `CK`'s planes, bitslices sixteen copies of `MK ⊕ FK`, runs the
loop (`ekIter_ok`) and restores the registers; the schedule is the
specification's `expandKey`.
-/

@[expose] public section

namespace VG.Proof.Sm4

open VG VG.PPC64LE VG.Impl.Sm4.PPC64LE

/-- The key schedule on PPC64LE with its working space at `r5`. -/
def expandKeyPPC64LE : Contract PPC64LE.isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, 16⟩
    let sched : Region := ⟨s.gpr .r4, 128⟩
    let scratch : Region := ⟨s.gpr .r5, 8 * slots⟩
    s.rd = [key] ∧ s.wr = [sched, scratch] ∧ key.Disjoint sched ∧ key.Disjoint scratch ∧
      sched.Disjoint scratch ∧
      (s.gpr .r3).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + 128 ≤ 2 ^ 64 ∧
      (s.gpr .r5).toNat + 8 * slots ≤ 2 ^ 64
  post s s' :=
    Spec.Sm4.scheduleAt s'.mem (s.gpr .r4) = Spec.Sm4.expandKey (Spec.Sm4.blockAt s.mem (s.gpr .r3))
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.sp = s₂.sp

end VG.Proof.Sm4

namespace VG.Proof.Sm4.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.Sm4.PPC64LE
open VG.Impl.Aes.PPC64LE (q sb t0 t1 movR ldS stS)
open VG.Impl.Sm4 (planeOf fkWord)
open VG.Proof.Sm4 (planeOf_rel fkWord_bit WordRel quads ofBlock outBlock keyInit rkOf readW64_bit getLsbD_wordAt ofInt_nat
  expandKeyPPC64LE)

/-! ## `MK ⊕ FK` in the tail buffer -/

theorem keyInit_bit (key : Spec.Sm4.Block) {w i j : Nat} (hi : i < 4) (hj : j < 8) :
    (keyInit key w).getLsbD (8 * (3 - i) + j) =
      ((key.getD (4 * w + i) 0).getLsbD j ^^ (Spec.Sm4.fk.getD w 0).getLsbD (8 * (3 - i) + j)) := by
  rw [keyInit, BitVec.getLsbD_xor, getLsbD_wordAt _ _ hi hj]

/-- Byte `i` of block `c` of the tail buffer, from its words. -/
theorem tailBlock_bit (s : State) {c i j : Nat} (hi : i < 16) (hj : j < 8) :
    ((tailBlock s c).getD i 0).getLsbD j = (slotW s (tailAt c (i / 8))).getLsbD (8 * (i % 8) + j) := by
  rw [slotW, readW64_bit _ _ (by omega_arith) hj, VG.Proof.Sm4.blockAt_getD _ _ hi, wordAddr, addr_add, addr_add, tailAt]
  rw [show 8 * tailSlot + 16 * c + i = 8 * (tailSlot + 2 * c + i / 8) + i % 8 by omega_arith]

/-- The tail buffer's blocks are `MK ⊕ FK`, from the key's 64-bit words `K h`. -/
theorem keyInit_rel {s : State} {key : Spec.Sm4.Block} {K : Nat → BitVec 64}
    (hK : ∀ h < 2, ∀ t < 8, ∀ j < 8, (K h).getLsbD (8 * t + j) = (key.getD (8 * h + t) 0).getLsbD j)
    (hT : ∀ c < 16, ∀ h < 2, slotW s (tailAt c h) = K h ^^^ fkWord h) :
    ∀ c < 16, ∀ w < 4, ofBlock (tailBlock s c) w = keyInit key w := by
  intro c hc w hw
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  obtain hi : 3 - k / 8 < 4 := by omega_arith
  rw [show k = 8 * (3 - (3 - k / 8)) + k % 8 by omega_arith, keyInit_bit key (w := w) hi (by omega_arith)]
  simp only [ofBlock]
  rw [getLsbD_wordAt _ _ hi (by omega_arith), tailBlock_bit s (c := c) (by omega_arith) (by omega_arith), hT c hc _ (by omega_arith),
    BitVec.getLsbD_xor, fkWord_bit (by omega_arith)]
  obtain e1 : 8 * ((4 * w + (3 - k / 8)) % 8) + k % 8 = 8 * (4 * (w % 2) + (3 - k / 8)) + k % 8 := by omega_arith
  rw [e1, hK _ (by omega_arith) _ (by omega_arith) _ (by omega_arith)]
  obtain h1 : 2 * ((4 * w + (3 - k / 8)) / 8) + (8 * (4 * (w % 2) + (3 - k / 8)) + k % 8) / 32 = w := by omega_arith
  obtain h2 : 8 * (3 - (8 * (4 * (w % 2) + (3 - k / 8)) + k % 8) % 32 / 8) +
      (8 * (4 * (w % 2) + (3 - k / 8)) + k % 8) % 8 = 8 * (3 - (3 - k / 8)) + k % 8 := by omega_arith
  obtain h3 : 8 * ((4 * w + (3 - k / 8)) / 8) + (4 * (w % 2) + (3 - k / 8)) = 4 * w + (3 - k / 8) := by omega_arith
  rw [h1, h2, h3]

theorem ckEntries_mem {e j : Nat} (he : e < 32) (hj : j < 8) :
    (tableSlot + 8 * e + j, planeOf (Spec.Sm4.ck e) j) ∈ ckEntries := by
  simp only [ckEntries, List.mem_flatMap, List.mem_range, List.mem_map]
  exact ⟨e, he, j, hj, rfl⟩

theorem ckEntries_lt : ∀ kv ∈ ckEntries, kv.1 < tableEnd := by decide +kernel

theorem ckEntries_ge : ∀ kv ∈ ckEntries, tableSlot ≤ kv.1 := by decide +kernel

theorem ckEntries_nodup : (ckEntries.map (·.1)).Nodup := by
  -- The slots are consecutive: a linear check, not the quadratic `Nodup` search.
  rw [show ckEntries.map (·.1) = List.range' tableSlot 256 by decide +kernel]
  exact List.nodup_range'

theorem entryW_slot (s : State) (e j : Nat) : entryW s.mem (s.gpr sb) e j = slotW s (tableSlot + 8 * e + j) := by
  simp only [entryW, slotW, wordAddr]; rw [show 8 * (tableSlot + 8 * e + j) = 8 * tableSlot + 64 * e + 8 * j by omega_arith]

/-- The code before the loop. -/
def ekHead : List Instr :=
  [movR sb .r5] ++ saveRegs ++ setSlots keyMasks ++ ckTable ++ loadHalf 0 ++
    loadHalf 1 ++ toBs ++ slotAddr .r11 tableEnd ++ slotAddr kr tableSlot

theorem ekHead_ok {s₀ : State} (hp : expandKeyPPC64LE.pre s₀) :
    ∃ s, runBlock isa ekHead s₀ = some s ∧
      EkInv s₀ (s₀.gpr .r5) (s₀.gpr .r4) (Spec.Sm4.blockAt s₀.mem (s₀.gpr .r3)) 0 s := by
  obtain ⟨hrd, hwr, dKS, dKB, dSB, fitK, fitS, fitB⟩ := hp
  let b := s₀.gpr .r5
  let S := s₀.gpr .r4
  let Kp := s₀.gpr .r3
  obtain hwB : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [b]
  have hfitB := fitB
  rw [slots_eq] at hfitB
  -- The registers.
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s₀ sb .r5
  have g₁ : ∀ r, r ≠ sb → s₁.gpr r = s₀.gpr r := o₁
  have hb₁ : s₁.gpr sb = b := r₁
  have mem₁ : s₁.mem = s₀.mem := m₁
  have wr₁' : s₁.wr = s₀.wr := wr₁
  have rd₁' : s₁.rd = s₀.rd := rd₁
  -- Saving, the masks and the table of `CK`.
  obtain ⟨s₂, e₂, sv₂, g₂, rd₂, wr₂, f₂, -⟩ := save_ok (b := b) (by rw [wr₁']; exact hwB) hb₁
  obtain ⟨s₃, e₃, v₃, k₃, g₃, rd₃, wr₃, f₃⟩ := setSlots_ok (b := b) keyMasks (by rw [g₂, hb₁])
    (by rw [wr₂, wr₁']; exact hwB) (fun kv hkv => by have := mask_lt hkv; rw [tableSlot_eq]; omega_arith) (by decide)
  obtain ⟨s₄, e₄, v₄, k₄, g₄, rd₄, wr₄, f₄⟩ := setSlotsN_ok tableEnd (by rw [tableEnd_eq, slots_eq]; omega_arith)
    ckEntries (b := b) (by rw [g₃ _ (by decide), g₂, hb₁]) (by rw [wr₃, wr₂, wr₁']; exact hwB) ckEntries_lt
    ckEntries_nodup
  obtain hb₄ : s₄.gpr sb = b := by rw [g₄ _ (by decide), g₃ _ (by decide), g₂, hb₁]
  obtain f₀₄ : Frame [⟨b, 8 * slots⟩] s₀.mem s₄.mem := by
    rw [← mem₁]
    refine f₂.trans ((f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (f₄.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)) <;>
      (simp only [List.mem_singleton] at hr; subst hr) <;>
      exact Region.sub_prefix (by simp only [tableSlot_eq, tableEnd_eq, slots_eq]; omega_arith)
  -- The key.
  obtain inK : ∀ h < 2, InRegions (s₄.rd ++ s₄.wr) (Kp + BitVec.ofNat 64 (8 * h)) 8 := fun h hh =>
    ⟨_, List.mem_append_left _ (by rw [rd₄, rd₃, rd₂, rd₁', hrd]; exact List.mem_singleton_self _),
      VG.Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  obtain hKw : ∀ (m : Mem), Frame [⟨b, 8 * slots⟩] s₀.mem m → ∀ h < 2,
      m.readW (Kp + BitVec.ofNat 64 (8 * h)) 64 = s₀.mem.readW (Kp + BitVec.ofNat 64 (8 * h)) 64 :=
    fun m hf h hh => hf.readW (r := ⟨Kp, 16⟩) (VG.Offset.contains_base _ (by omega_arith) (by omega_arith))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dKB) (by decide)
  obtain hrdi₄ : s₄.gpr .r3 = Kp := by
    rw [g₄ _ (by decide), g₃ _ (by decide), g₂, g₁ _ (by decide)]
  obtain ⟨s₅, e₅, v₅, k₅, g₅, rd₅, wr₅, f₅⟩ := loadHalf_ok 0 (by decide) hb₄ (by rw [wr₄, wr₃, wr₂, wr₁']; exact hwB)
    (by rw [hrdi₄]; exact inK 0 (by decide))
  obtain hb₅ : s₅.gpr sb = b := by rw [g₅ _ (by decide) (by decide), hb₄]
  obtain ⟨s₆, e₆, v₆, k₆, g₆, rd₆, wr₆, f₆⟩ := loadHalf_ok 1 (by decide) hb₅
    (by rw [wr₅, wr₄, wr₃, wr₂, wr₁']; exact hwB)
    (by rw [rd₅, wr₅, g₅ _ (by decide) (by decide), hrdi₄]; exact inK 1 (by decide))
  obtain hb₆ : s₆.gpr sb = b := by rw [g₆ _ (by decide) (by decide), hb₅]
  obtain f₀₆ : Frame [⟨b, 8 * slots⟩] s₀.mem s₆.mem := (f₀₄.trans f₅).trans f₆
  obtain hk₆ : ∀ k < slots, (∀ c < 16, ∀ h < 2, k ≠ tailAt c h) → slotW s₆ k = slotW s₄ k := fun k hk hn => by
    rw [k₆ k hk (fun c hc => hn c hc 1 (by decide)), k₅ k hk (fun c hc => hn c hc 0 (by decide))]
  obtain notTail : ∀ k, tableSlot ≤ k ∨ k < tailSlot → ∀ c < 16, ∀ h < 2, k ≠ tailAt c h := fun k hk c hc h hh => by
    simp only [tailAt, tailSlot_eq, tableSlot_eq] at hk ⊢; omega_arith
  obtain notCk : ∀ k, k < tableSlot ∨ tableEnd ≤ k → k ∉ ckEntries.map (·.1) := fun k hk hm => by
    simp only [List.mem_map] at hm
    obtain ⟨kv, hkv, rfl⟩ := hm
    have := ckEntries_lt kv hkv; have := ckEntries_ge kv hkv; omega_arith
  obtain notMask : ∀ k, 51 ≤ k → k ∉ keyMasks.map (·.1) := fun k hk hm => by
    simp only [List.mem_map] at hm
    obtain ⟨kv, hkv, rfl⟩ := hm
    have := mask_range hkv; omega_arith
  -- The table and the masks.
  obtain hkey₆ : KeyCtx s₆ Spec.Sm4.ck :=
    { scr := by rw [hb₆, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁']; exact hwB
      fit := by rw [hb₆]; exact fitB
      keys := fun e he => (planeOf_rel (Spec.Sm4.ck e)).congr fun j hj => by
        rw [entryW_slot, hk₆ _ (by rw [tableSlot_eq, slots_eq]; omega_arith) (notTail _ (Or.inl (by omega_arith))),
          v₄ _ (ckEntries_mem he hj)] }
  obtain hm₆ : MasksOk s₆ := fun kv hkv => by
    have := mask_range hkv
    rw [hk₆ _ (by rw [slots_eq]; omega_arith) (notTail _ (Or.inr (by rw [tailSlot_eq]; omega_arith))),
      k₄ _ (by rw [slots_eq]; omega_arith) (notCk _ (Or.inl (by rw [tableSlot_eq]; omega_arith))), v₃ kv hkv]
  -- The key, bitsliced.
  obtain ⟨s₇, e₇, c₇, kr₇, X₇⟩ := toBs_step hkey₆ (Ctx.refl hm₆)
  obtain ⟨s₈, e₈, r₈, o₈, m₈, rd₈, wr₈⟩ := slotAddr_ok s₇ .r11 tableEnd (by decide)
  obtain ⟨s₉, e₉, r₉, o₉, m₉, rd₉, wr₉⟩ := slotAddr_ok s₈ kr tableSlot (by decide)
  obtain hb₇ : s₇.gpr sb = b := by rw [c₇.base, hb₆]
  obtain hb₉ : s₉.gpr sb = b := by rw [o₉ _ (by decide), o₈ _ (by decide), hb₇]
  obtain mem₉ : s₉.mem = s₇.mem := by rw [m₉, m₈]
  obtain g₉ : ∀ r, r ∉ sboxWrites → r ≠ kr → r ≠ .r11 → s₉.gpr r = s₆.gpr r := fun r h1 h2 h3 => by
    rw [o₉ r h2, o₈ r h3, c₇.keep r h1 h2]
  obtain g₆' : ∀ r, r ∉ sboxWrites → r ≠ sb → s₆.gpr r = s₀.gpr r := fun r h1 h2 => by
    obtain ht0 : r ≠ t0 := fun h => h1 (by subst h; decide)
    obtain ht1 : r ≠ t1 := fun h => h1 (by subst h; decide)
    rw [g₆ r ht0 ht1, g₅ r ht0 ht1, g₄ r ht0, g₃ r ht0, g₂, g₁ r h2]
  obtain hK : ∀ h < 2, ∀ t < 8, ∀ j < 8, (s₀.mem.readW (Kp + BitVec.ofNat 64 (8 * h)) 64).getLsbD (8 * t + j) =
      ((Spec.Sm4.blockAt s₀.mem Kp).getD (8 * h + t) 0).getLsbD j := fun h hh t ht j hj => by
    rw [readW64_bit _ _ ht hj, VG.Proof.Sm4.blockAt_getD _ _ (by omega_arith), addr_add]
  obtain hT : ∀ c < 16, ∀ h < 2, slotW s₆ (tailAt c h) = s₀.mem.readW (Kp + BitVec.ofNat 64 (8 * h)) 64 ^^^ fkWord h := by
    intro c hc h hh
    rcases (show h = 0 ∨ h = 1 by omega_arith) with rfl | rfl
    · rw [k₆ _ (tailAt_lt hc (by decide)) (fun c' _ h' => by simp only [tailAt] at h'; omega_arith), v₅ c hc, hrdi₄,
        hKw _ f₀₄ 0 (by decide)]
    · rw [v₆ c hc, g₅ _ (by decide) (by decide), hrdi₄, hKw _ (f₀₄.trans f₅) 1 (by decide)]
  obtain hst : StRel s₉ (fun _ => quads .key Spec.Sm4.ck 0 (keyInit (Spec.Sm4.blockAt s₀.mem Kp))) := fun w hw =>
    ((X₇ w hw).congr fun j _ => by simp only [planes, slotW, mem₉, hb₉, hb₇]).congr_right fun c hc =>
      (keyInit_rel hK hT c hc w hw).symm
  refine ⟨s₉, ?_, ⟨hb₉, ?_, ?_, ?_, ?_, ?_, hst, fun i hi => by omega_arith, fun i hi => ?_, ?_,
    by rw [rd₉, rd₈, c₇.rd, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁'], by rw [wr₉, wr₈, c₇.wr, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁']⟩⟩
  · rw [ekHead, runBlock_app, runBlock_app, runBlock_app, runBlock_app, runBlock_app, runBlock_app,
      runBlock_app, runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some, e₃, Option.bind_some,
      ckTable, e₄, Option.bind_some, e₅, Option.bind_some, e₆, Option.bind_some, e₇, Option.bind_some, e₈,
      Option.bind_some, e₉]
  · rw [g₉ _ (by decide) (by decide) (by decide), g₆' _ (by decide) (by decide)]
    exact (BitVec.add_zero _).symm
  · rw [o₉ _ (by decide), r₈, hb₇]
  · rw [AtEntry, r₉, o₈ _ (by decide), hb₇]; simp; rfl
  · exact (hkey₆.of_ctx c₇) |> fun h => ⟨by rw [wr₉, wr₈, hb₉, ← hb₇]; exact h.scr, by rw [hb₉, ← hb₇]; exact h.fit,
      fun e he => by rw [hb₉, ← hb₇, mem₉]; exact h.keys e he⟩
  · exact fun kv hkv => by simp only [slotW, mem₉, hb₉, ← hb₇]; exact c₇.masks kv hkv
  · have hk : savedSlot + i < slots := by rw [savedSlot_eq, slots_eq]; omega_arith
    obtain h7 : slotW s₇ (savedSlot + i) = slotW s₆ (savedSlot + i) := by
      simp only [slotW, hb₇, hb₆]
      refine c₇.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      rw [hb₆, wordAddr]
      exact VG.Offset.disjoint_base _ (by rw [tableSlot_eq, savedSlot_eq]; omega_arith) (by rw [savedSlot_eq]; omega_arith)
    obtain h6 : slotW s₆ (savedSlot + i) = slotW s₂ (savedSlot + i) := by
      rw [hk₆ _ hk (notTail _ (Or.inl (by rw [tableSlot_eq, savedSlot_eq]; omega_arith))),
        k₄ _ hk (notCk _ (Or.inr (by rw [tableEnd_eq, savedSlot_eq]; omega_arith))),
        k₃ _ hk (notMask _ (by rw [savedSlot_eq]; omega_arith))]
    obtain h2 := sv₂ i hi
    rw [g₁ _ (sreg_ne i hi)] at h2
    show s₉.mem.readW (wordAddr b (savedSlot + i)) 64 = _
    rw [mem₉, ← hb₇, ← h2]
    have := h7.trans h6
    simp only [slotW, hb₇, show s₂.gpr sb = b by rw [g₂, hb₁]] at this
    rw [hb₇]; exact this
  · rw [mem₉]
    refine (f₀₆.trans (c₇.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)).sub
      fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self, fun _ h => h⟩
    simp only [List.mem_singleton] at hr; subst hr
    rw [hb₆]; exact Region.sub_prefix (by rw [tableSlot_eq, slots_eq]; omega_arith)

/-! ## The loop and the whole function -/

theorem ekLoop_wp {s₀ s : State} {b S : Addr} {key : Spec.Sm4.Block} (hp : EkPre s₀ b S)
    (hi : EkInv s₀ b S key 0 s) :
    WP isa (.loop (.block keyBody) (.nonzero .d t0)) s (EkInv s₀ b S key 8) := by
  refine WP.loop (M := isa) (fun n s => ∃ m, n = 8 - m ∧ m < 8 ∧ EkInv s₀ b S key m s)
    (fun n s hs => ?_) 8 s ⟨0, rfl, by omega_arith, hi⟩
  obtain ⟨m, rfl, hm, hi⟩ := hs
  obtain ⟨s', e', hi', z'⟩ := ekIter_ok hp hm hi
  refine WP.of_runBlock ⟨s', e', ?_⟩
  by_cases h8 : m + 1 = 8
  · exact .inl ⟨by rw [eval_nonzero, z', h8]; rfl, by rw [h8] at hi'; exact hi'⟩
  · exact .inr ⟨by rw [eval_nonzero, z']; simp [h8], 8 - (m + 1), by omega_arith, m + 1, rfl, by omega_arith, hi'⟩

theorem expandKey_wp {s₀ : State} (hp : expandKeyPPC64LE.pre s₀) :
    WP isa expandKey s₀ fun s' => (∀ i < 18, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      expandKeyPPC64LE.post s₀ s' := by
  obtain ⟨s₁, e₁, h₁⟩ := ekHead_ok hp
  obtain ⟨hrd, hwr, dKS, dKB, dSB, fitK, fitS, fitB⟩ := hp
  let b := s₀.gpr .r5
  let S := s₀.gpr .r4
  obtain hwB : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [b]
  obtain hwS : (⟨S, 128⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [S]
  obtain pre : EkPre s₀ b S := ⟨hwB, hwS, dSB, fitB, fitS⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, WP.seq (WP.mono (ekLoop_wp pre h₁) fun s₂ h₂ => ?_)⟩)
  obtain ⟨s₃, e₃, rg₃, -, m₃, -, -⟩ := restore_ok (by rw [h₂.wr]; exact hwB) h₂.base h₂.saved
  refine WP.of_runBlock ⟨s₃, e₃, rg₃, ?_⟩
  show Spec.Sm4.scheduleAt s₃.mem S = _
  rw [expandKey_eq]
  apply Vector.ext
  intro i hi
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [show k = 8 * (k / 8) + k % 8 by omega_arith, VG.Proof.Sm4.getLsbD_scheduleAt _ _ hi (by omega_arith) (by omega_arith),
    Vector.getElem_ofFn, m₃]
  exact h₂.sched i (by omega_arith) _ (by omega_arith) _ (by omega_arith)

end VG.Proof.Sm4.PPC64LE

end

end

/-!
# SM4 key expansion on PPC64LE meets its contracts

`expandKey_verified`: `expandKey` is correct (`expandKey_wp`) and constant
time, by the taint analysis with the pointers and the stack pointer public.
`expandKey_framed` runs it with its working space on the stack, zeroed on
return, as `ecb_framed` does.
-/

@[expose] public section

namespace VG.Proof.Sm4.PPC64LE

open VG VG.PPC64LE VG.Impl.Sm4.PPC64LE
open VG.Proof.Sm4 (expandKeyPPC64LE)

theorem expandKeyTaint_agree (s₁ s₂ : State) (_ : expandKeyPPC64LE.pre s₁) (_ : expandKeyPPC64LE.pre s₂)
    (hp : expandKeyPPC64LE.pub s₁ s₂) : taint.Agree (Taint.ofRegs [.r3, .r4, .r5]) s₁ s₂ := by
  obtain ⟨h1, h2, h3, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> with_reducible assumption

theorem expandKey_ct : ConstantTime isa expandKeyPPC64LE.pre expandKeyPPC64LE.pub expandKey :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5]) expandKeyTaint_agree (by taint_decide)

/-- The registers key expansion writes. -/
def expandKeyWrites : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20,
   .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

theorem expandKey_correct (s : State) (hs : expandKeyPPC64LE.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ expandKeyPPC64LE.post s s' := by
  have hn : expandKey.noCalls = true := by lit_decide
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, hk⟩ := WP.keep expandKeyWrites (expandKey_wp hs) (by lit_decide) hn
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, Exec.lr he hn (by lit_decide)⟩, h₂⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact hk.gpr (by decide)
  · exact h₁ 0 (by omega_using [])
  · exact h₁ 1 (by omega_using [])
  · exact h₁ 2 (by omega_using [])
  · exact h₁ 3 (by omega_using [])
  · exact h₁ 4 (by omega_using [])
  · exact h₁ 5 (by omega_using [])
  · exact h₁ 6 (by omega_using [])
  · exact h₁ 7 (by omega_using [])
  · exact h₁ 8 (by omega_using [])
  · exact h₁ 9 (by omega_using [])
  · exact h₁ 10 (by omega_using [])
  · exact h₁ 11 (by omega_using [])
  · exact h₁ 12 (by omega_using [])
  · exact h₁ 13 (by omega_using [])
  · exact h₁ 14 (by omega_using [])
  · exact h₁ 15 (by omega_using [])
  · exact h₁ 16 (by omega_using [])
  · exact h₁ 17 (by omega_using [])

/-- A state satisfying the precondition. -/
def expandKeySat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 8 * 402⟩]

theorem expandKey_verified :
    Verified target expandKey (Proof.Sm4.expandKeyScratchContract abi slots) :=
  Verified.of_correct expandKey_correct expandKey_ct (by
    sig_implies [Proof.Sm4.expandKeyScratchContract, Proof.Sm4.expandKeyScratchSig, Proof.Sm4.expandKeyPost,
      expandKeyPPC64LE, abi, argRegs, slots, savedSlot, tableEnd, tableSlot]
      [expandKeySat] using expandKeySat)

/-- A state satisfying the key schedule's precondition: the key at
`0x1000`, the schedule at `0x2000`. -/
def expandKeyFrameSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | _ => 0
  lr := 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 128⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.Sm4.expandKeyContract abi 3248).pre s := by
  implies_sat [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, abi, argRegs]
    [expandKeyFrameSat] using expandKeyFrameSat

/-- Key expansion, with its working space on the stack. -/
theorem expandKey_framed :
    Verified target (Impl.StackScratch.PPC64LE.withStackScratchWiped 3248 .r5 402 expandKey)
      (Spec.Sm4.expandKeyContract abi 3248) :=
  Verified.stackScratchWiped (sig := Spec.Sm4.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 402) (post := Proof.Sm4.expandKeyPost abi.ptrBits) (wa := false) (stack := 0)
    (bytes := 3248) (words := 402) expandKey_verified (by decide) (by decide) (by decide)
    (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (Proof.Sm4.expandKeyPost_local _)
    (Proof.Sm4.expandKeyPostOut_local _) expandKeyFrameSat_pre

end VG.Proof.Sm4.PPC64LE

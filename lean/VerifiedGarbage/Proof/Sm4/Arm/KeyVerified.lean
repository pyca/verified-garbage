module

public import VerifiedGarbage.Proof.Sm4.Scratch
public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.RegScratchWipe
public import VerifiedGarbage.Impl.StackScratch.Arm
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Sm4.Arm.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sm4.Arm.LayersLit
meta import VerifiedGarbage.Proof.Sm4.Scratch
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.RegScratchWipe
meta import VerifiedGarbage.Impl.StackScratch.Arm
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Sm4.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sm4.Arm.LayersLit
public import VerifiedGarbage.Impl.Sm4.Arm.ExpandKey
public import VerifiedGarbage.Proof.Sm4.Arm.Group
import VerifiedGarbage.Proof.Framework.Arm.Bytes
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Sm4.Layout
import VerifiedGarbage.Proof.Sm4.Planes
meta import VerifiedGarbage.Impl.Sm4.Arm.ExpandKey
meta import VerifiedGarbage.Proof.Sm4.Arm.Group
meta import VerifiedGarbage.Proof.Framework.Arm.Bytes
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Sm4.Layout
meta import VerifiedGarbage.Proof.Sm4.Planes

/-! ### `Sm4.Arm.KeyEk`, which only this module used -/

section

/-! ### `Sm4.Arm.KeyInit`, which only this module used -/

section

/-!
# The start of the SM4 key schedule on ARMv7

As on AArch64: the planes of `CK` stored as constants (`constStores_ok`),
and `MK ⊕ FK` stored to the eight blocks of the tail buffer
(`loadKeyWord_ok`), whose words, bitsliced, are the key schedule's initial
state `keyInit` (`keyInit_rel`).
-/

@[expose] public section

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Sm4.Arm
open VG.Impl.Aes.Arm (q sb t0 t1 kp movR ldS stS eorR imm32)
open VG.Proof.Sm4 (keyInit getLsbD_wordAt fkLE_bit)
open VG.Impl.Sm4 (fkLE)

/-! ## Constants and stores -/

/-- `movw d, #lo; movt d, #hi`. -/
theorem imm32_ok (s : State) (d : Reg) (v : BitVec 32) :
    ∃ s', runBlock isa (imm32 d v) s = some s' ∧ s'.gpr d = v ∧ (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  let s₁ := s.setReg d ((v.extractLsb' 0 16).setWidth 32)
  refine ⟨s₁.setReg d (v.extractLsb' 16 16 ++ (s₁.gpr d).extractLsb' 0 16), ?_, ?_,
    fun r hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setReg_of_ne _ _ hr], rfl, rfl, rfl, rfl⟩
  · rw [imm32, runBlock_cons, show exec (.movw d (v.extractLsb' 0 16)) s = some s₁ from rfl, runStep_some,
      runBlock_cons, show exec (.movt d (v.extractLsb' 16 16)) s₁ =
        some (s₁.setReg d (v.extractLsb' 16 16 ++ (s₁.gpr d).extractLsb' 0 16)) from rfl,
      runStep_some, runBlock_nil]
  · rw [RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_self]; exact movw_movt v

/-- `imm32 t1, v; str t1, [sb, #4 k]` for each `(k, v)` of `L`. -/
theorem constStores_ok {b : BitVec 32} : ∀ (L : List (Nat × BitVec 32)) {s : State}, s.gpr sb = b →
    ScrIn s.wr b → (L.map (·.1)).Nodup → (∀ x ∈ L, x.1 < slots) →
    ∃ s', runBlock isa (L.flatMap fun (k, v) => imm32 t1 v ++ [stS k t1]) s = some s' ∧
      (∀ x ∈ L, s'.mem.readW (wordAddr b x.1) 32 = x.2) ∧
      (∀ k < slots, k ∉ L.map (·.1) → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32) ∧
      (∀ r, r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨State.addr b, 4 * slots⟩] s.mem s'.mem
  | [], s, _, _, _, _ => ⟨s, rfl, by simp, fun _ _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | x :: L, s, hb, hw, hnd, hin => by
    have hx := hin x List.mem_cons_self
    obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := imm32_ok s t1 x.2
    obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂, sp₂, -, f₂⟩ := stSlot_ok s₁ t1 sb (k := x.1)
      (by rw [o₁ _ (by decide), hb]) hx (by rw [wr₁]; exact hw)
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', v', k', g', rd', wr', sp', f'⟩ := constStores_ok L (s := s₂)
      (by rw [g₂, o₁ _ (by decide), hb]) (by rw [wr₂, wr₁]; exact hw) hnd.2
      fun y hy => hin y (List.mem_cons_of_mem _ hy)
    have hfit := hw.fit
    have hslot : ∀ j < slots, s₂.mem.readW (wordAddr b j) 32 = if j = x.1 then x.2 else
        s.mem.readW (wordAddr b j) 32 := fun j hj => by
      rw [m₂, readW_slot_write hfit _ hj hx, v₁, m₁]
    refine ⟨s', ?_, fun y hy => ?_, fun j hj hn => ?_, fun r hr => by rw [g' r hr, g₂, o₁ r hr],
      by rw [rd', rd₂, rd₁], by rw [wr', wr₂, wr₁], by rw [sp', sp₂, sp₁], ?_⟩
    · rw [List.flatMap_cons, runBlock_app, runBlock_app, e₁, Option.bind_some,
        show ([stS x.1 t1] : List Instr) = [.str t1 sb (4 * x.1)] from rfl, e₂, Option.bind_some]
      exact e'
    · rcases List.mem_cons.mp hy with rfl | hy'
      · by_cases hin' : y.1 ∈ L.map (·.1)
        · exact absurd hin' hnd.1
        · rw [k' _ hx hin', hslot _ hx, ite_eq_left rfl]
      · exact v' y hy'
    · simp only [List.map_cons, List.mem_cons, not_or] at hn
      rw [k' j hj hn.2, hslot j hj, ite_eq_right hn.1]
    · rw [← m₁]
      exact (f₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact slot_sub hfit hx⟩).trans f'

/-- `str r, [sb, #4 k]` for each `k` of `ks`. -/
theorem storeAll_ok (r : Reg) {b : BitVec 32} : ∀ (ks : List Nat) {s : State}, s.gpr sb = b →
    ScrIn s.wr b → (∀ k ∈ ks, k < slots) →
    ∃ s', runBlock isa (ks.map fun k => stS k r) s = some s' ∧
      (∀ k ∈ ks, s'.mem.readW (wordAddr b k) 32 = s.gpr r) ∧
      (∀ k < slots, k ∉ ks → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨State.addr b, 4 * slots⟩] s.mem s'.mem
  | [], s, _, _, _ => ⟨s, rfl, by simp, fun _ _ _ => rfl, rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | k :: ks, s, hb, hw, hk => by
    have hk0 : k < slots := hk k List.mem_cons_self
    obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁, sp₁, -, f₁⟩ := stSlot_ok s r sb (k := k) hb hk0 hw
    obtain ⟨s', e', v', o', g', rd', wr', sp', f'⟩ := storeAll_ok r ks (s := s₁) (by rw [g₁, hb])
      (by rw [wr₁]; exact hw) fun k h => hk k (List.mem_cons_of_mem _ h)
    have hfit := hw.fit
    have hslot : ∀ j < slots, s₁.mem.readW (wordAddr b j) 32 = if j = k then s.gpr r else
        s.mem.readW (wordAddr b j) 32 := fun j hj => by rw [m₁, readW_slot_write hfit _ hj hk0]
    refine ⟨s', by rw [List.map_cons, ← List.singleton_append, runBlock_app,
        show ([stS k r] : List Instr) = [.str r sb (4 * k)] from rfl, e₁, Option.bind_some]; exact e',
      fun j hj => ?_, fun j hj hn => ?_, by rw [g', g₁], by rw [rd', rd₁], by rw [wr', wr₁], by rw [sp', sp₁], ?_⟩
    · rcases List.mem_cons.mp hj with rfl | hj'
      · by_cases hin : j ∈ ks
        · rw [v' j hin, g₁]
        · rw [o' j hk0 hin, hslot j hk0, ite_eq_left rfl]
      · rw [v' j hj', g₁]
    · simp only [List.mem_cons, not_or] at hn
      rw [o' j hj hn.2, hslot j hj, ite_eq_right hn.1]
    · exact (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact slot_sub hfit hk0⟩).trans f'

/-! ## `MK ⊕ FK` -/

theorem tailAt_lt {c w : Nat} (hc : c < 8) (hw : w < 4) : tailAt c w < slots := by
  simp only [tailAt, tailSlot_eq, slots_eq]; omega_arith

/-- Word `w` of the key at `K`, XOR `FK`, to the eight blocks. -/
theorem loadKeyWord_ok {s : State} {b K : BitVec 32} (w : Nat) (hw4 : w < 4) (hb : s.gpr sb = b)
    (hw : ScrIn s.wr b) (hK : s.gpr .r0 = K) (hr : InRegions (s.rd ++ s.wr) (wordAddr K w) 4) :
    ∃ s', runBlock isa (loadKeyWord w) s = some s' ∧
      (∀ c < 8, s'.mem.readW (wordAddr b (tailAt c w)) 32 = s.mem.readW (wordAddr K w) 32 ^^^ fkLE w) ∧
      (∀ k < slots, (∀ c < 8, k ≠ tailAt c w) →
        s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32) ∧
      (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨State.addr b, 4 * slots⟩] s.mem s'.mem := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := ldW_ok s t0 .r0 (k := w) hK (by omega_arith) hr
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := imm32_ok s₁ t1 (fkLE w)
  let s₃ := s₂.setReg t0 (s₂.gpr t0 ^^^ s₂.gpr t1)
  have e₃ : runBlock isa [eorR t0 t0 t1] s₂ = some s₃ := by
    rw [runBlock_cons, show exec (eorR t0 t0 t1) s₂ = some s₃ by simp [eorR, exec, Op2.eval, s₃], runStep_some,
      runBlock_nil]
  have v₃ : s₃.gpr t0 = s.mem.readW (wordAddr K w) 32 ^^^ fkLE w := by
    rw [RegUpd.gpr_setReg_self, o₂ _ (by decide), v₁, v₂]
  have o₃ : ∀ r, r ≠ t0 → r ≠ t1 → s₃.gpr r = s.gpr r := fun r h0 h1 => by
    rw [RegUpd.gpr_setReg_of_ne _ _ h0, o₂ r h1, o₁ r h0]
  have hb₃ : s₃.gpr sb = b := by rw [o₃ _ (by decide) (by decide), hb]
  obtain ⟨s', e', v', k', g', rd', wr', sp', f'⟩ := storeAll_ok t0 ((List.range 8).map fun c => tailAt c w)
    (s := s₃) hb₃ (by show ScrIn s₂.wr b; rw [wr₂, wr₁]; exact hw)
    (fun k hk => by simp only [List.mem_map, List.mem_range] at hk; obtain ⟨c, hc, rfl⟩ := hk
                    exact tailAt_lt hc hw4)
  have mem₃ : s₃.mem = s.mem := by show s₂.mem = _; rw [m₂, m₁]
  refine ⟨s', ?_, fun c hc => ?_, fun k hk hne => ?_, fun r h0 h1 => by rw [g', o₃ r h0 h1],
    by rw [rd']; show s₂.rd = _; rw [rd₂, rd₁], by rw [wr']; show s₂.wr = _; rw [wr₂, wr₁],
    by rw [sp']; show s₂.sp = _; rw [sp₂, sp₁], by rw [← mem₃]; exact f'⟩
  · rw [loadKeyWord, runBlock_app, runBlock_app, runBlock_app,
      show ([.ldr t0 .r0 (4 * w)] : List Instr) = [.ldr t0 .r0 (4 * w)] from rfl, e₁, Option.bind_some, e₂,
      Option.bind_some, e₃, Option.bind_some]
    simpa only [List.map_map, Function.comp_def] using e'
  · rw [v' _ (by simp only [List.mem_map, List.mem_range]; exact ⟨c, hc, rfl⟩), v₃]
  · rw [k' k hk (by simp only [List.mem_map, List.mem_range, not_exists, not_and]; exact fun c hc h' => hne c hc h'.symm),
      mem₃]

/-- Byte `i` of block `c` of the tail buffer, from its words. -/
theorem tailBlock_bit (s : State) {b : BitVec 32} (hb : s.gpr sb = b) (hfit : b.toNat + 4 * slots ≤ 2 ^ 32)
    {c i j : Nat} (hc : c < 8) (hi : i < 16) (hj : j < 8) :
    ((tailBlock s c).getD i 0).getLsbD j =
      (s.mem.readW (wordAddr b (tailAt c (i / 4))) 32).getLsbD (8 * (i % 4) + j) := by
  rw [readW_bit _ _ (by omega_arith) hj, VG.Proof.Sm4.blockAt_getD _ _ hi, hb,
    byte_addr b (k := tailAt c (i / 4)) rfl (by simp only [tailAt, tailSlot_eq]; rw [slots_eq] at hfit; omega_arith),
    VG.Offset.add_add, tailAt]
  rw [show 4 * tailSlot + 16 * c + i = 4 * (tailSlot + 4 * c + i / 4) + i % 4 by omega_arith]

/-- The tail buffer's blocks are `MK ⊕ FK`, from the key's words `K w`. -/
theorem keyInit_rel {s : State} {b : BitVec 32} (hb : s.gpr sb = b) (hfit : b.toNat + 4 * slots ≤ 2 ^ 32)
    {key : Spec.Sm4.Block} {K : Nat → BitVec 32}
    (hK : ∀ w < 4, ∀ t < 4, ∀ j < 8, (K w).getLsbD (8 * t + j) = (key.getD (4 * w + t) 0).getLsbD j)
    (hT : ∀ c < 8, ∀ w < 4, s.mem.readW (wordAddr b (tailAt c w)) 32 = K w ^^^ fkLE w) :
    ∀ c < 8, ∀ w < 4, VG.Proof.Sm4.ofBlock (tailBlock s c) w = keyInit key w := by
  intro c hc w hw
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hi : 3 - k / 8 < 4 := by omega_arith
  rw [show k = 8 * (3 - (3 - k / 8)) + k % 8 by omega_arith]
  simp only [VG.Proof.Sm4.ofBlock, keyInit]
  rw [BitVec.getLsbD_xor, getLsbD_wordAt _ _ hi (by omega_arith), getLsbD_wordAt _ _ hi (by omega_arith),
    tailBlock_bit s hb hfit hc (by omega_arith) (by omega_arith), show (4 * w + (3 - k / 8)) / 4 = w by omega_arith,
    hT c hc w hw, BitVec.getLsbD_xor, fkLE_bit (by omega_arith), show (4 * w + (3 - k / 8)) % 4 = 3 - k / 8 by omega_arith,
    hK w hw _ hi _ (by omega_arith)]
  congr 2
  omega_arith

end VG.Proof.Sm4.Arm

end

end

/-! ### `Sm4.Arm.KeyLoop`, which only this module used -/

section

/-!
# The loop of the SM4 key schedule on ARMv7

Each iteration runs four rounds of the key schedule (`rounds4_ok .key`),
puts the state's words in the tail buffer as a block (`fromBs_step`), and
stores them to the schedule as little-endian words (`extract_ok`): the
first block's words, last first, byte-reversed (`rev`). The schedule's
pointer waits in slot `nSlot` (the rounds use every register).
-/

@[expose] public section

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Sm4.Arm
open VG.Impl.Aes.Arm (q sb t0 t1 u7 kp movR ldS stS)
open VG.Proof.Sm4 (quads ofBlock outBlock keyInit rkOf getLsbD_outBlock' writeW32_byte writeW32_other)

/-! ## The extraction -/

/-- The extraction, after its first `k` words: the schedule's bytes at `A`
before `4 k` hold the tail buffer's first block, last byte first. -/
structure ExtInv (s₀ : State) (b P : BitVec 32) (k : Nat) (s : State) : Prop where
  base : s.gpr sb = b
  ptr : s.gpr u7 = P
  bytes : ∀ t < 4 * k, ∀ j < 8, (s.mem (State.addr P + BitVec.ofNat 64 t)).getLsbD j =
    ((tailBlock s₀ 0).getD (15 - t) 0).getLsbD j
  frame : Frame [⟨State.addr P, 4 * k⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ t0 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

/-- The extraction's word `k`. -/
theorem extStep_ok {s₀ s : State} {b P : BitVec 32} {k : Nat} (hk : k < 4)
    (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) (hP : P.toNat + 16 ≤ 2 ^ 32)
    (hw : ScrIn s₀.wr b) (hS : ∀ t < 4, InRegions s₀.wr (State.addr P + BitVec.ofNat 64 (4 * t)) 4)
    (hsep : Region.Disjoint ⟨State.addr P, 16⟩ ⟨State.addr b, 4 * slots⟩) (hb₀ : s₀.gpr sb = b)
    (hi : ExtInv s₀ b P k s) :
    ∃ s', runBlock isa [ldS t0 (tailAt 0 (3 - k)), .rev t0 t0, .str t0 u7 (4 * k)] s = some s' ∧
      ExtInv s₀ b P (k + 1) s' := by
  obtain hb := addr_toNat b
  obtain hPn := addr_toNat P
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := ldSlot_ok s t0 sb (k := tailAt 0 (3 - k)) hi.base
    (tailAt_lt (by decide) (by omega_arith)) (by rw [hi.wr]; exact hw)
  let s₂ := s₁.setReg t0 (rev (s₁.gpr t0))
  obtain e₂ : runBlock isa [.rev t0 t0] s₁ = some s₂ := by
    rw [runBlock_cons, show exec (.rev t0 t0) s₁ = some s₂ from rfl, runStep_some, runBlock_nil]
  obtain u7₂ : s₂.gpr u7 = P := by rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), o₁ _ (by decide), hi.ptr]
  obtain eA : State.addr (s₂.gpr u7 + BitVec.ofNat 32 (4 * k)) = State.addr P + BitVec.ofNat 64 (4 * k) := by
    rw [u7₂, addr_add (by omega_arith)]
  obtain wr₂ : s₂.wr = s₀.wr := by show s₁.wr = _; rw [wr₁, hi.wr]
  obtain hin : InRegions s₂.wr (State.addr (s₂.gpr u7 + BitVec.ofNat 32 (4 * k))) 4 :=
    by rw [wr₂, eA]; exact hS k hk
  -- The slot read is the one on entry.
  obtain hslot : s.mem.readW (wordAddr b (tailAt 0 (3 - k))) 32 = s₀.mem.readW (wordAddr b (tailAt 0 (3 - k))) 32 := by
    obtain hk' := tailAt_lt (c := 0) (w := 3 - k) (by decide) (by omega_arith)
    rw [slot_addr (by omega_arith)]
    refine hi.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact ((hsep.sub_left (Region.sub_prefix (by omega_arith))).sub_right
      (VG.Offset.sub_base _ (by omega_arith))).symm
  obtain v₂ : s₂.gpr t0 = rev (s₀.mem.readW (wordAddr b (tailAt 0 (3 - k))) 32) := by
    rw [RegUpd.gpr_setReg_self, v₁, hslot]
  let s₃ : State := { s₂ with mem := s₂.mem.writeW (State.addr P + BitVec.ofNat 64 (4 * k)) (s₂.gpr t0) }
  obtain e₃ : runBlock isa [.str t0 u7 (4 * k)] s₂ = some s₃ := by
    rw [runBlock_cons, exec_str (by omega_arith) hin, eA, runStep_some, runBlock_nil]
  have mem₂ : s₂.mem = s.mem := m₁
  refine ⟨s₃, ?_, ⟨by show s₂.gpr sb = b; rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), o₁ _ (by decide), hi.base],
    u7₂, fun t ht j hj => ?_, ?_, fun r hr => ?_, by show s₁.rd = _; rw [rd₁, hi.rd], wr₂,
    by show s₁.sp = _; rw [sp₁, hi.sp]⟩⟩
  · rw [show ([ldS t0 (tailAt 0 (3 - k)), .rev t0 t0, .str t0 u7 (4 * k)] : List Instr) =
      [.ldr t0 sb (4 * tailAt 0 (3 - k))] ++ ([.rev t0 t0] ++ [.str t0 u7 (4 * k)]) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, e₃]
  · show (s₂.mem.writeW _ _ _).getLsbD j = _
    by_cases hlt : t < 4 * k
    · rw [writeW32_other _ _ _ _ (VG.Proof.Sm4.off_sub_not _ (Or.inl hlt) (by omega_arith) (by decide) (by omega_arith)),
        mem₂]
      exact hi.bytes t hlt j hj
    · have hc : t - 4 * k < 4 := by omega_arith
      rw [show State.addr P + BitVec.ofNat 64 t =
          State.addr P + BitVec.ofNat 64 (4 * k) + BitVec.ofNat 64 (t - 4 * k) by
        rw [VG.Offset.add_add, show 4 * k + (t - 4 * k) = t by omega_arith],
        writeW32_byte _ _ _ hc hj, v₂, rev_bit _ hc hj,
        tailBlock_bit s₀ (c := 0) (i := 15 - t) hb₀ hfit (by decide) (by omega_arith) hj,
        show (15 - t) / 4 = 3 - k by omega_arith, show (15 - t) % 4 = 3 - (t - 4 * k) by omega_arith]
  · refine (hi.frame.sub fun r hr => ⟨⟨State.addr P, 4 * (k + 1)⟩, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega_arith)⟩).trans ?_
    show Frame _ s.mem (s₂.mem.writeW _ _)
    rw [mem₂]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Offset.contains_base _ (by omega_arith) (by omega_arith))
  · show (s₁.setReg t0 _).gpr r = _
    rw [RegUpd.gpr_setReg_of_ne _ _ hr, o₁ r hr, hi.regs r hr]

/-- The schedule's bytes `16 m … 16 m + 15`: the words of the tail buffer's
first block, the last first, each little-endian; the schedule's pointer
stepped. -/
theorem extract_ok {s : State} {b S : BitVec 32} {m : Nat} (hm : m < 8) (hb : s.gpr sb = b) (hw : ScrIn s.wr b)
    (hSfit : S.toNat + 128 ≤ 2 ^ 32) (hS : (⟨State.addr S, 128⟩ : Region) ∈ s.wr)
    (hsep : Region.Disjoint ⟨State.addr S, 128⟩ ⟨State.addr b, 4 * slots⟩)
    (hn : s.mem.readW (wordAddr b nSlot) 32 = S + BitVec.ofNat 32 (16 * m)) :
    ∃ s', runBlock isa extract s = some s' ∧
      (∀ t < 16, ∀ j < 8, (s'.mem (State.addr S + BitVec.ofNat 64 (16 * m + t))).getLsbD j =
        ((tailBlock s 0).getD (15 - t) 0).getLsbD j) ∧
      s'.mem.readW (wordAddr b nSlot) 32 = S + BitVec.ofNat 32 (16 * (m + 1)) ∧
      Frame [⟨State.addr S + BitVec.ofNat 64 (16 * m), 16⟩, ⟨wordAddr b nSlot, 4⟩] s.mem s'.mem ∧
      (∀ r, r ≠ t0 → r ≠ u7 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have hfit := hw.fit
  obtain hSn := addr_toNat S
  let P := S + BitVec.ofNat 32 (16 * m)
  obtain hPa : State.addr P = State.addr S + BitVec.ofNat 64 (16 * m) := addr_add (by omega_arith)
  obtain hPn : P.toNat + 16 ≤ 2 ^ 32 := by rw [toNat_add32 _ (by omega_arith)]; omega_arith
  obtain subP : Region.Sub ⟨State.addr P, 16⟩ ⟨State.addr S, 128⟩ := by rw [hPa]; exact VG.Offset.sub_base _ (by omega_arith)
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := ldSlot_ok s u7 sb (k := nSlot) hb (by decide) hw
  rw [hn] at v₁
  obtain hb₁ : s₁.gpr sb = b := by rw [o₁ _ (by decide), hb]
  obtain hw₁ : ScrIn s₁.wr b := by rw [wr₁]; exact hw
  obtain hS₁ : ∀ t < 4, InRegions s₁.wr (State.addr P + BitVec.ofNat 64 (4 * t)) 4 := fun t ht =>
    ⟨_, by rw [wr₁]; exact hS, by rw [hPa, VG.Offset.add_add]; exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  obtain hsepP : Region.Disjoint ⟨State.addr P, 16⟩ ⟨State.addr b, 4 * slots⟩ := hsep.sub_left subP
  obtain i0 : ExtInv s₁ b P 0 s₁ := ⟨hb₁, v₁, fun t ht => by omega_arith, Frame.refl _ _, fun _ _ => rfl, rfl, rfl, rfl⟩
  obtain ⟨s₂, e₂, i₂⟩ := extStep_ok (k := 0) (by decide) hfit hPn hw₁ hS₁ hsepP hb₁ i0
  obtain ⟨s₃, e₃, i₃⟩ := extStep_ok (k := 1) (by decide) hfit hPn hw₁ hS₁ hsepP hb₁ i₂
  obtain ⟨s₄, e₄, i₄⟩ := extStep_ok (k := 2) (by decide) hfit hPn hw₁ hS₁ hsepP hb₁ i₃
  obtain ⟨s₅, e₅, i₅⟩ := extStep_ok (k := 3) (by decide) hfit hPn hw₁ hS₁ hsepP hb₁ i₄
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆, sp₆⟩ := addImm_ok s₅ u7 u7 16 (by decide)
  obtain ⟨s₇, e₇, m₇, g₇, rd₇, wr₇, sp₇, -, f₇⟩ := stSlot_ok s₆ u7 sb (k := nSlot)
    (by rw [o₆ _ (by decide), i₅.base]) (by decide) (by rw [wr₆, i₅.wr, wr₁]; exact hw)
  obtain hmem₇ : s₇.mem = s₅.mem.writeW (wordAddr b nSlot) (P + BitVec.ofNat 32 16) := by
    rw [m₇, m₆, r₆, i₅.ptr]; rfl
  obtain hblk : tailBlock s₁ 0 = tailBlock s 0 := by simp only [tailBlock, m₁, hb₁, hb]
  obtain dN : Region.Disjoint ⟨State.addr P, 16⟩ ⟨wordAddr b nSlot, 4⟩ :=
    hsepP.sub_right (slot_sub hfit (by decide))
  refine ⟨s₇, ?_, fun t ht j hj => ?_, ?_, ?_, fun r h0 h7 => ?_, by rw [rd₇, rd₆, i₅.rd, rd₁],
    by rw [wr₇, wr₆, i₅.wr, wr₁], by rw [sp₇, sp₆, i₅.sp, sp₁]⟩
  · rw [extract, show (List.range 4).flatMap (fun k => ([ldS t0 (tailAt 0 (3 - k)), .rev t0 t0,
        .str t0 u7 (4 * k)] : List Instr)) = [ldS t0 (tailAt 0 (3 - 0)), .rev t0 t0, .str t0 u7 (4 * 0)] ++
        ([ldS t0 (tailAt 0 (3 - 1)), .rev t0 t0, .str t0 u7 (4 * 1)] ++
        ([ldS t0 (tailAt 0 (3 - 2)), .rev t0 t0, .str t0 u7 (4 * 2)] ++
        [ldS t0 (tailAt 0 (3 - 3)), .rev t0 t0, .str t0 u7 (4 * 3)])) from rfl,
      show ([.dp .add u7 u7 (.imm 16), stS nSlot u7] : List Instr) =
        [.dp .add u7 u7 (.imm 16)] ++ [.str u7 sb (4 * nSlot)] from rfl,
      runBlock_app, runBlock_app,
      show ([ldS u7 nSlot] : List Instr) = [.ldr u7 sb (4 * nSlot)] from rfl, e₁, Option.bind_some,
      runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some, runBlock_app, e₄, Option.bind_some,
      e₅, Option.bind_some, runBlock_app, e₆, Option.bind_some, e₇]
  · have hx : (⟨State.addr P, 16⟩ : Region).Contains (State.addr P + BitVec.ofNat 64 t) 1 :=
      VG.Offset.contains_base _ (by omega_arith) (by omega_arith)
    rw [show State.addr S + BitVec.ofNat 64 (16 * m + t) = State.addr P + BitVec.ofNat 64 t by
        rw [hPa, VG.Offset.add_add],
      hmem₇, writeW32_other _ _ _ _ (out_of_disj dN hx (Region.contains_self _ _)), i₅.bytes t (by omega_arith) j hj,
      hblk]
  · rw [hmem₇, Mem.readW_writeW_self32]
    simp only [P]
    rw [VG.Offset.add_add, show 16 * m + 16 = 16 * (m + 1) by omega_arith]
  · rw [← m₁]
    refine (i₅.frame.sub fun r hr => ⟨_, List.mem_cons_self, by
      simp only [List.mem_singleton] at hr; subst hr; rw [hPa]; exact fun _ h => h⟩).trans ?_
    rw [← m₆]
    exact f₇.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  · rw [g₇, o₆ r h7, i₅.regs r h0, o₁ r h7]

end VG.Proof.Sm4.Arm

end

end


/-!
# The SM4 key schedule on ARMv7: the whole function

`expandKey_wp`: with the working space as an argument (`expandKeyArm`),
`expandKey` saves the callee-saved registers, keeps the schedule's pointer
in its slot, stores the table of `CK`'s planes, bitslices eight copies of
`MK ⊕ FK`, runs the loop (`ekIter_ok`) and restores the registers; the
schedule is the specification's `expandKey`.
-/

@[expose] public section

namespace VG.Proof.Sm4

open VG VG.Arm VG.Impl.Sm4.Arm

/-- The key schedule on ARMv7 with its working space at `r2`. -/
def expandKeyArm : Contract Arm.isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), 16⟩
    let sched : Region := ⟨State.addr (s.gpr .r1), 128⟩
    let scratch : Region := ⟨State.addr (s.gpr .r2), 4 * slots⟩
    s.rd = [key] ∧ s.wr = [sched, scratch] ∧ key.Disjoint sched ∧ key.Disjoint scratch ∧
      sched.Disjoint scratch ∧
      (s.gpr .r0).toNat + 16 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 128 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 4 * slots ≤ 2 ^ 32
  post s s' :=
    Spec.Sm4.scheduleAt s'.mem (State.addr (s.gpr .r1)) =
      Spec.Sm4.expandKey (Spec.Sm4.blockAt s.mem (State.addr (s.gpr .r0)))
  pub s₁ s₂ :=
    s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.sp = s₂.sp

end VG.Proof.Sm4

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Sm4.Arm
open VG.Impl.Aes.Arm (q sb t0 t1 u7 kp movR ldS stS)
open VG.Proof.Sm4 (quads ofBlock outBlock keyInit rkOf getLsbD_outBlock expandKeyArm expandKey_eq)
open VG.Impl.Sm4 (planeOf32 fkLE)

/-! ## The loop -/

/-- What the loop keeps, after `m` of its eight iterations: the state holds
the key schedule's words after `4 m` rounds, and the schedule its first
`4 m` round keys. -/
structure EkInv (s₀ : State) (b S : BitVec 32) (key : Spec.Sm4.Block) (m : Nat) (s : State) : Prop where
  base : s.gpr sb = b
  ptr : s.mem.readW (wordAddr b nSlot) 32 = S + BitVec.ofNat 32 (16 * m)
  kp : AtEntry s b (4 * m)
  keys : KeyCtx s Spec.Sm4.ck
  st : StRel s (fun _ => quads .key Spec.Sm4.ck m (keyInit key))
  sched : ∀ i < 4 * m, ∀ c < 4, ∀ j < 8,
    (s.mem (State.addr S + BitVec.ofNat 64 (4 * i + c))).getLsbD j = (rkOf key i).getLsbD (8 * c + j)
  saved : Saved s₀ b s.mem
  frame : Frame [⟨State.addr b, 4 * slots⟩, ⟨State.addr S, 128⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

/-- The scratch buffer and the schedule, writable and apart. -/
structure EkPre (s₀ : State) (b S : BitVec 32) : Prop where
  scr : ScrIn s₀.wr b
  sch : (⟨State.addr S, 128⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨State.addr S, 128⟩ ⟨State.addr b, 4 * slots⟩
  fitS : S.toNat + 128 ≤ 2 ^ 32

theorem ekIter_ok {s₀ : State} {b S : BitVec 32} {key : Spec.Sm4.Block} (hp : EkPre s₀ b S) {m : Nat} (hm : m < 8)
    {s : State} (hi : EkInv s₀ b S key m s) :
    ∃ s', runBlock isa keyBody s = some s' ∧ EkInv s₀ b S key (m + 1) s' ∧ s'.z = decide (m + 1 = 8) := by
  have hfit' := hp.scr.fit
  have hfit : b.toNat + 4 * 364 ≤ 2 ^ 32 := hfit'
  have l₁ := tableSlot_eq
  have l₂ := dSlot_eq
  have l₃ := nSlot_eq
  have l₄ := slots_eq
  have l₅ := savedSlot_eq
  have l₆ := tableEnd_eq
  have hfitS := hp.fitS
  obtain hSn := addr_toNat S
  obtain hbn := addr_toNat b
  obtain hc0 : Ctx s s := Ctx.refl s
  obtain hwS : ScrIn s.wr b := by rw [hi.wr]; exact hp.scr
  -- Four rounds.
  obtain ⟨s₁, e₁, c₁, k₁, X₁⟩ := rounds4_ok .key hi.keys hc0 (by rw [hi.base]; exact hi.kp) hm hi.st
  obtain ⟨s₂, e₂, kp₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := addImm_ok s₁ kp kp 128 (by decide)
  obtain c₂ : Ctx s s₂ := c₁.kp o₂ m₂ rd₂ wr₂ sp₂
  obtain X₂ : StRel s₂ (fun _ => quads .key Spec.Sm4.ck (m + 1) (keyInit key)) :=
    X₁.congr fun k => by simp only [slotW, m₂, o₂ sb (by decide)]
  -- The words to the tail buffer.
  obtain ⟨s₃, e₃, c₃, kp₃, X₃, T₃⟩ := fromBs_step hi.keys c₂ X₂
  obtain base₃ : s₃.gpr sb = b := by rw [c₃.base, hi.base]
  obtain hwS₃ : ScrIn s₃.wr b := by rw [c₃.wr]; exact hwS
  -- To the schedule.
  obtain ⟨s₄, e₄, B₄, n₄, f₄, o₄, rd₄, wr₄, sp₄⟩ := extract_ok hm base₃ hwS₃ hfitS
    (by rw [c₃.wr, hi.wr]; exact hp.sch) hp.sep
    (by rw [slot_keep (lo := tableSlot) (hi := slots) hfit' (Nat.le_refl _) c₃.frame (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [hi.base]
          exact VG.Offset.disjoint_base _ (Nat.le_refl _) (by omega_arith))
        (show tableSlot ≤ nSlot by decide) (by decide), hi.ptr])
  obtain ⟨s₅, e₅, z₅, g₅, m₅, rd₅, wr₅, sp₅⟩ := endTest_ok s₄ (BitVec.ofNat 32 (4 * tableEnd)) (by decide)
  have mem₅ : s₅.mem = s₄.mem := m₅
  obtain g₅' : ∀ r, r ≠ t0 → r ≠ u7 → s₅.gpr r = s₃.gpr r := fun r h0 h7 => by rw [g₅ r h0, o₄ r h0 h7]
  obtain base₅ : s₅.gpr sb = b := by rw [g₅' _ (by decide) (by decide), base₃]
  obtain kp₅ : AtEntry s₅ b (4 * (m + 1)) := by
    rw [AtEntry, g₅' _ (by decide) (by decide), kp₃, kp₂, k₁, show s.gpr kp = _ from hi.kp,
      show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl, add_ofNat_ofNat,
      show 4 * tableSlot + 32 * (4 * m) + 128 = 4 * tableSlot + 32 * (4 * (m + 1)) by omega_arith]
  -- What the extraction keeps: everything outside the schedule's new bytes and the pointer's slot.
  obtain dHi : ∀ r ∈ [(⟨State.addr S + BitVec.ofNat 64 (16 * m), 16⟩ : Region), ⟨wordAddr b nSlot, 4⟩],
      (slotsRegion b 0 dSlot).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hp.sep.sub_left (VG.Offset.sub_base _ (by omega_arith))).sub_right
        (VG.Offset.sub_base _ (by omega_arith)) |>.symm
    · rw [slot_addr (by omega_arith)]
      exact VG.Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  obtain keep₄ : ∀ k < dSlot, s₄.mem.readW (wordAddr b k) 32 = s₃.mem.readW (wordAddr b k) 32 := fun k hk =>
    slot_keep (lo := 0) (hi := dSlot) hfit' (by decide) f₄ dHi (Nat.zero_le _) hk
  obtain keepT : ∀ k, tableSlot ≤ k → k < dSlot → s₃.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32 :=
    fun k h1 h2 => slot_keep (lo := tableSlot) (hi := dSlot) hfit' (by decide) c₃.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hi.base]
      exact VG.Offset.disjoint_base _ (Nat.le_refl _) (by omega_arith)) h1 h2
  obtain hent : ∀ e < 32, ∀ j < 8, entryW s₅.mem b e j = entryW s.mem b e j := fun e he j hj => by
    simp only [entryW]
    rw [mem₅, keep₄ _ (by rw [tableSlot_eq, dSlot_eq]; omega_arith), keepT _ (by omega_arith) (by rw [tableSlot_eq, dSlot_eq]; omega_arith)]
  refine ⟨s₅, ?_, ⟨base₅, by rw [mem₅]; exact n₄, kp₅,
    ⟨by rw [base₅, wr₅, wr₄, c₃.wr, hi.wr]; exact hp.scr.mem, by rw [base₅]; exact hfit',
      fun e he => by rw [base₅]; exact (hi.keys.keys e he).congr fun j hj => by rw [hi.base] at *; exact hent e he j hj⟩,
    fun w hw => (X₃ w hw).congr fun j hj => ?_, fun i hi' c hc j hj => ?_, fun i hi' => ?_, ?_,
    by rw [rd₅, rd₄, c₃.rd, hi.rd], by rw [wr₅, wr₄, c₃.wr, hi.wr], by rw [sp₅, sp₄, c₃.sp, hi.sp]⟩, ?_⟩
  · rw [keyBody, runBlock_app, runBlock_app, runBlock_app, runBlock_app, e₁, Option.bind_some,
      e₂, Option.bind_some, e₃, Option.bind_some, e₄, Option.bind_some, e₅]
  · show slotW s₅ (stateSlot w j) = slotW s₃ (stateSlot w j)
    rw [slotW, slotW, base₅, base₃, mem₅, keep₄ _ (by simp only [stateSlot, dSlot_eq]; omega_arith)]
  · by_cases hnew : 4 * m ≤ i
    · have ht : 4 * (i - 4 * m) + c < 16 := by omega_arith
      obtain hB := B₄ _ ht j hj
      rw [show 16 * m + (4 * (i - 4 * m) + c) = 4 * i + c by omega_arith] at hB
      rw [mem₅, hB, T₃ 0 (by decide), getLsbD_outBlock _ (by omega_arith) hj]
      simp only [rkOf]
      rw [show i / 4 + 1 = m + 1 by omega_arith, show 3 - (15 - (4 * (i - 4 * m) + c)) / 4 = i % 4 by omega_arith,
        show 8 * (3 - (15 - (4 * (i - 4 * m) + c)) % 4) + j = 8 * c + j by omega_arith]
    · have hx : (⟨State.addr S, 128⟩ : Region).Contains (State.addr S + BitVec.ofNat 64 (4 * i + c)) 1 :=
        VG.Offset.contains_base _ (by omega_arith) (by omega_arith)
      rw [mem₅, f₄ _ (fun r hr => ?_), c₃.frame _ (fun r hr => ?_)]
      · exact hi.sched i (by omega_arith) c hc j hj
      · simp only [List.mem_singleton] at hr; subst hr; rw [hi.base]
        exact fun h => hp.sep _ hx (Region.sub_prefix (show 4 * tableSlot ≤ 4 * slots by
          rw [tableSlot_eq, slots_eq]; omega_arith) _ h)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact VG.Proof.Sm4.not_contains_off _ (Or.inl (by omega_arith)) (by omega_arith) (by decide) (by omega_arith)
        · exact fun h => hp.sep _ hx (slot_sub hfit' (by decide) _ h)
  · have hk : savedSlot + i < dSlot := by rw [savedSlot_eq, dSlot_eq]; omega_arith
    show s₅.mem.readW _ 32 = _
    rw [mem₅, keep₄ _ hk, keepT _ (by rw [savedSlot_eq, tableSlot_eq]; omega_arith) hk]
    exact hi.saved i hi'
  · rw [mem₅]
    refine hi.frame.trans ((c₃.frame.sub fun r hr => ⟨⟨State.addr b, 4 * slots⟩, List.mem_cons_self, ?_⟩).trans
      (f₄.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr; rw [hi.base]
      exact Region.sub_prefix (by rw [tableSlot_eq, slots_eq]; omega_arith)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨State.addr S, 128⟩, List.mem_cons_of_mem _ List.mem_cons_self, VG.Offset.sub_base _ (by omega_arith)⟩
      · exact ⟨⟨State.addr b, 4 * slots⟩, List.mem_cons_self, slot_sub hfit' (by decide)⟩
  · rw [z₅, o₄ _ (by decide) (by decide), o₄ _ (by decide) (by decide), base₃, kp₃, kp₂, k₁,
      show s.gpr kp = _ from hi.kp, show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl, add_ofNat_ofNat,
      VG.Offset.add_sub_cancel_left, ofNat32_sub_beq (by rw [tableSlot_eq]; omega_arith) (by rw [tableEnd_eq]; omega_arith),
      tableSlot_eq, tableEnd_eq]
    simp only [decide_eq_decide]; omega_arith

theorem ekLoop_wp {s₀ s : State} {b S : BitVec 32} {key : Spec.Sm4.Block} (hp : EkPre s₀ b S)
    (hi : EkInv s₀ b S key 0 s) :
    WP isa (.loop (.block keyBody) .ne) s (EkInv s₀ b S key 8) := by
  refine WP.loop (M := isa) (fun n s => ∃ m, n = 8 - m ∧ m < 8 ∧ EkInv s₀ b S key m s)
    (fun n s hs => ?_) 8 s ⟨0, rfl, by omega_arith, hi⟩
  obtain ⟨m, rfl, hm, hi⟩ := hs
  obtain ⟨s', e', hi', z'⟩ := ekIter_ok hp hm hi
  refine WP.of_runBlock ⟨s', e', ?_⟩
  by_cases h8 : m + 1 = 8
  · exact .inl ⟨by rw [eval_ne, z', h8]; rfl, by rw [h8] at hi'; exact hi'⟩
  · exact .inr ⟨by rw [eval_ne, z']; simp [h8], 8 - (m + 1), by omega_arith, m + 1, rfl, by omega_arith, hi'⟩

/-! ## The start -/

theorem ckEntries_mem {e j : Nat} (he : e < 32) (hj : j < 8) :
    (tableSlot + 8 * e + j, planeOf32 (Spec.Sm4.ck e) j) ∈ ckEntries := by
  simp only [ckEntries, List.mem_flatMap, List.mem_range, List.mem_map]
  exact ⟨e, he, j, hj, rfl⟩

theorem ckEntries_lt : ∀ kv ∈ ckEntries, kv.1 < tableEnd := by decide +kernel

theorem ckEntries_nodup : (ckEntries.map (·.1)).Nodup := by
  -- The slots are consecutive: a linear check, not the quadratic `Nodup` search.
  rw [show ckEntries.map (·.1) = List.range' tableSlot 256 by decide +kernel]
  exact List.nodup_range'

/-- The code before the loop. -/
def ekHead : List Instr :=
  saveRegs .r2 ++ [movR sb .r2, stS nSlot .r1] ++ ckTable ++ loadKey ++ toBs ++ [kpAt tableSlot]

theorem ekHead_ok {s₀ : State} (hp : expandKeyArm.pre s₀) :
    ∃ s, runBlock isa ekHead s₀ = some s ∧
      EkInv s₀ (s₀.gpr .r2) (s₀.gpr .r1) (Spec.Sm4.blockAt s₀.mem (State.addr (s₀.gpr .r0))) 0 s := by
  obtain ⟨hrd, hwr, dKS, dKB, dSB, fitK, fitS, fitB⟩ := hp
  let b := s₀.gpr .r2
  let S := s₀.gpr .r1
  let Kp := s₀.gpr .r0
  obtain hwS : ScrIn s₀.wr b := ⟨by rw [hwr]; simp [b], fitB⟩
  have hfit : b.toNat + 4 * 364 ≤ 2 ^ 32 := fitB
  obtain hbn := addr_toNat b
  obtain hKn := addr_toNat Kp
  have hfK : Kp.toNat + 16 ≤ 2 ^ 32 := fitK
  have l₁ := tableSlot_eq
  have l₂ := dSlot_eq
  have l₃ := nSlot_eq
  have l₄ := slots_eq
  have l₅ := savedSlot_eq
  have l₆ := tableEnd_eq
  have l₇ := tailSlot_eq
  -- Saving, the schedule's pointer, the table of `CK`.
  obtain ⟨s₁, e₁, sv₁, g₁, rd₁, wr₁, sp₁, f₁, -⟩ := save_ok (base := .r2) hwS rfl
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := movR_ok s₁ sb .r2
  obtain b₂ : s₂.gpr sb = b := by rw [r₂, g₁]
  obtain hw₂ : ScrIn s₂.wr b := by rw [wr₂, wr₁]; exact hwS
  obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃, sp₃, -, f₃⟩ := stSlot_ok s₂ .r1 sb (k := nSlot) b₂ (by decide) hw₂
  obtain b₃ : s₃.gpr sb = b := by rw [g₃, b₂]
  obtain hw₃ : ScrIn s₃.wr b := by rw [wr₃]; exact hw₂
  obtain ⟨s₄, e₄, v₄, k₄, g₄, rd₄, wr₄, sp₄, f₄⟩ := constStores_ok ckEntries b₃ hw₃ ckEntries_nodup
    (fun kv hkv => by have := ckEntries_lt kv hkv; omega_arith)
  obtain b₄ : s₄.gpr sb = b := by rw [g₄ _ (by decide), b₃]
  obtain hw₄ : ScrIn s₄.wr b := by rw [wr₄]; exact hw₃
  obtain r0₄ : s₄.gpr .r0 = Kp := by rw [g₄ _ (by decide), g₃, o₂ _ (by decide), g₁]
  -- The key's words, as on entry.
  obtain f₀₄ : Frame [⟨State.addr b, 4 * slots⟩] s₀.mem s₄.mem := by
    refine f₁.trans ?_; rw [← m₂]
    exact (f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact slot_sub fitB (by decide)⟩).trans f₄
  obtain inK : ∀ w < 4, InRegions (s₀.rd ++ s₀.wr) (wordAddr Kp w) 4 := fun w hw =>
    ⟨_, List.mem_append_left _ (by rw [hrd]; exact List.mem_singleton_self _), by
      rw [slot_addr (by omega_arith)]; exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  obtain hKw : ∀ (m : Mem), Frame [⟨State.addr b, 4 * slots⟩] s₀.mem m → ∀ w < 4,
      m.readW (wordAddr Kp w) 32 = s₀.mem.readW (wordAddr Kp w) 32 := fun m hf w hw => by
    rw [slot_addr (by omega_arith)]
    exact hf.readW (r := ⟨State.addr Kp, 16⟩) (VG.Offset.contains_base _ (by omega_arith) (by omega_arith))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dKB) (by decide)
  -- `MK ⊕ FK` to the tail buffer.
  obtain rdwr : ∀ (st : State), st.rd = s₀.rd → st.wr = s₀.wr → ∀ w < 4,
      InRegions (st.rd ++ st.wr) (wordAddr Kp w) 4 := fun st h1 h2 w hw => by rw [h1, h2]; exact inK w hw
  obtain ⟨s₅, e₅, v₅, k₅, g₅, rd₅, wr₅, sp₅, f₅⟩ := loadKeyWord_ok (s := s₄) 0 (by decide) b₄ hw₄ r0₄
    (rdwr s₄ (by rw [rd₄, rd₃, rd₂, rd₁]) (by rw [wr₄, wr₃, wr₂, wr₁]) 0 (by decide))
  obtain ⟨s₆, e₆, v₆, k₆, g₆, rd₆, wr₆, sp₆, f₆⟩ := loadKeyWord_ok (s := s₅) 1 (by decide)
    (by rw [g₅ _ (by decide) (by decide), b₄]) (by rw [wr₅]; exact hw₄) (by rw [g₅ _ (by decide) (by decide), r0₄])
    (rdwr s₅ (by rw [rd₅, rd₄, rd₃, rd₂, rd₁]) (by rw [wr₅, wr₄, wr₃, wr₂, wr₁]) 1 (by decide))
  obtain ⟨s₇, e₇, v₇, k₇, g₇, rd₇, wr₇, sp₇, f₇⟩ := loadKeyWord_ok (s := s₆) 2 (by decide)
    (by rw [g₆ _ (by decide) (by decide), g₅ _ (by decide) (by decide), b₄]) (by rw [wr₆, wr₅]; exact hw₄)
    (by rw [g₆ _ (by decide) (by decide), g₅ _ (by decide) (by decide), r0₄])
    (rdwr s₆ (by rw [rd₆, rd₅, rd₄, rd₃, rd₂, rd₁]) (by rw [wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]) 2 (by decide))
  obtain ⟨s₈, e₈, v₈, k₈, g₈, rd₈, wr₈, sp₈, f₈⟩ := loadKeyWord_ok (s := s₇) 3 (by decide)
    (by rw [g₇ _ (by decide) (by decide), g₆ _ (by decide) (by decide), g₅ _ (by decide) (by decide), b₄])
    (by rw [wr₇, wr₆, wr₅]; exact hw₄)
    (by rw [g₇ _ (by decide) (by decide), g₆ _ (by decide) (by decide), g₅ _ (by decide) (by decide), r0₄])
    (rdwr s₇ (by rw [rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁]) (by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]) 3 (by decide))
  obtain g₈' : ∀ r, r ≠ t0 → r ≠ t1 → s₈.gpr r = s₄.gpr r := fun r h0 h1 => by
    rw [g₈ r h0 h1, g₇ r h0 h1, g₆ r h0 h1, g₅ r h0 h1]
  obtain b₈ : s₈.gpr sb = b := by rw [g₈' _ (by decide) (by decide), b₄]
  obtain f₀₈ : Frame [⟨State.addr b, 4 * slots⟩] s₀.mem s₈.mem := f₀₄.trans (f₅.trans (f₆.trans (f₇.trans f₈)))
  -- The slots outside the tail buffer after `s₄`, and outside the table after `s₃`.
  obtain notTail : ∀ k, tableSlot ≤ k → ∀ c < 8, ∀ w < 4, k ≠ tailAt c w := fun k hk c hc w hw => by
    simp only [tailAt]; omega_arith
  obtain kk₈ : ∀ k < slots, tableSlot ≤ k →
      s₈.mem.readW (wordAddr b k) 32 = s₄.mem.readW (wordAddr b k) 32 := fun k hk ht => by
    rw [k₈ k hk (fun c hc => notTail k ht c hc 3 (by decide)), k₇ k hk (fun c hc => notTail k ht c hc 2 (by decide)),
      k₆ k hk (fun c hc => notTail k ht c hc 1 (by decide)), k₅ k hk (fun c hc => notTail k ht c hc 0 (by decide))]
  obtain notCk : ∀ k, tableEnd ≤ k → k ∉ ckEntries.map (·.1) := fun k hk hm => by
    simp only [List.mem_map] at hm
    obtain ⟨kv, hkv, rfl⟩ := hm
    have := ckEntries_lt kv hkv; omega_arith
  -- The table of `CK`.
  obtain hkey₈ : KeyCtx s₈ Spec.Sm4.ck :=
    { scr := by rw [b₈, wr₈, wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]; exact hwS.mem
      fit := by rw [b₈]; exact fitB
      keys := fun e he => (planeOf32_rel (Spec.Sm4.ck e)).congr fun j hj => by
        rw [b₈, entryW, kk₈ _ (by omega_arith) (by omega_arith), v₄ _ (ckEntries_mem he hj)] }
  -- The key, bitsliced.
  obtain ⟨s₉, e₉, c₉, X₉⟩ := toBs_step hkey₈ (Ctx.refl s₈)
  obtain ⟨s₁₀, e₁₀, k₁₀, o₁₀, m₁₀, rd₁₀, wr₁₀, sp₁₀⟩ := kpAt_ok s₉ tableSlot (by decide)
  obtain b₉ : s₉.gpr sb = b := by rw [c₉.base, b₈]
  obtain b₁₀ : s₁₀.gpr sb = b := by rw [o₁₀ _ (by decide), b₉]
  obtain keep₉ : ∀ k, tableSlot ≤ k → k < slots →
      s₁₀.mem.readW (wordAddr b k) 32 = s₈.mem.readW (wordAddr b k) 32 := fun k h1 h2 => by
    rw [m₁₀]
    exact slot_keep (lo := tableSlot) (hi := slots) fitB (Nat.le_refl _) c₉.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [b₈]
      exact VG.Offset.disjoint_base _ (Nat.le_refl _) (by omega_arith)) h1 h2
  obtain hK : ∀ w < 4, ∀ t < 4, ∀ j < 8, (s₀.mem.readW (wordAddr Kp w) 32).getLsbD (8 * t + j) =
      ((Spec.Sm4.blockAt s₀.mem (State.addr Kp)).getD (4 * w + t) 0).getLsbD j := fun w hw t ht j hj => by
    rw [readW_bit _ _ ht hj, VG.Proof.Sm4.blockAt_getD _ _ (by omega_arith), byte_addr _ rfl (by omega_arith)]
  obtain hT : ∀ c < 8, ∀ w < 4, s₈.mem.readW (wordAddr b (tailAt c w)) 32 =
      s₀.mem.readW (wordAddr Kp w) 32 ^^^ fkLE w := by
    intro c hc w hw
    obtain hne : ∀ w', w' < 4 → w' ≠ w → ∀ c' < 8, tailAt c w ≠ tailAt c' w' := fun w' _ h c' _ h' => by
      simp only [tailAt] at h'; omega_arith
    obtain hl := tailAt_lt hc hw
    rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 by omega_arith) with rfl | rfl | rfl | rfl
    · rw [k₈ _ hl (hne 3 (by decide) (by decide)), k₇ _ hl (hne 2 (by decide) (by decide)),
        k₆ _ hl (hne 1 (by decide) (by decide)), v₅ c hc, hKw _ f₀₄ 0 (by decide)]
    · rw [k₈ _ hl (hne 3 (by decide) (by decide)), k₇ _ hl (hne 2 (by decide) (by decide)), v₆ c hc,
        hKw _ (f₀₄.trans f₅) 1 (by decide)]
    · rw [k₈ _ hl (hne 3 (by decide) (by decide)), v₇ c hc, hKw _ (f₀₄.trans (f₅.trans f₆)) 2 (by decide)]
    · rw [v₈ c hc, hKw _ (f₀₄.trans (f₅.trans (f₆.trans f₇))) 3 (by decide)]
  obtain hst : StRel s₁₀ (fun _ => quads .key Spec.Sm4.ck 0
      (keyInit (Spec.Sm4.blockAt s₀.mem (State.addr Kp)))) := fun w hw =>
    ((X₉ w hw).congr fun j _ => by simp only [planes, slotW, m₁₀, b₁₀, b₉]).congr_right fun c hc =>
      (keyInit_rel b₈ fitB hK hT c hc w hw).symm
  refine ⟨s₁₀, ?_, ⟨b₁₀, ?_, ?_, ?_, hst, fun i hi => by omega_arith, fun i hi => ?_, ?_,
    by rw [rd₁₀, c₉.rd, rd₈, rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁],
    by rw [wr₁₀, c₉.wr, wr₈, wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁],
    by rw [sp₁₀, c₉.sp, sp₈, sp₇, sp₆, sp₅, sp₄, sp₃, sp₂, sp₁]⟩⟩
  · rw [ekHead, runBlock_app, runBlock_app, runBlock_app, runBlock_app, runBlock_app, e₁,
      Option.bind_some,
      show ([movR sb .r2, stS nSlot .r1] : List Instr) = [movR sb .r2] ++ [.str .r1 sb (4 * nSlot)] from rfl,
      runBlock_app, e₂, Option.bind_some, e₃, Option.bind_some, ckTable, e₄, Option.bind_some,
      show loadKey = loadKeyWord 0 ++ (loadKeyWord 1 ++ (loadKeyWord 2 ++ loadKeyWord 3)) from rfl,
      runBlock_app, e₅, Option.bind_some, runBlock_app, e₆, Option.bind_some, runBlock_app, e₇, Option.bind_some,
      e₈, Option.bind_some, e₉, Option.bind_some, e₁₀]
  · rw [keep₉ _ (by decide) (by decide), kk₈ _ (by decide) (by decide), k₄ _ (by decide) (notCk _ (by decide)), m₃,
      readW_slot_write fitB _ (by decide) (by decide), ite_eq_left rfl, o₂ _ (by decide), g₁]
    simp
  · rw [AtEntry, k₁₀, b₉]; simp [b]
  · exact (hkey₈.of_ctx c₉) |> fun h => ⟨by rw [wr₁₀, b₁₀, ← b₉]; exact h.scr, by rw [b₁₀, ← b₉]; exact h.fit,
      fun e he => by rw [b₁₀, ← b₉, m₁₀]; exact h.keys e he⟩
  · have hk : savedSlot + i < slots := by omega_arith
    show s₁₀.mem.readW _ 32 = _
    rw [keep₉ _ (by omega_arith) hk, kk₈ _ hk (by omega_arith), k₄ _ hk (notCk _ (by omega_arith)), m₃,
      readW_slot_write fitB _ hk (by decide), ite_eq_right (by omega_arith), m₂]
    exact sv₁ i hi
  · rw [m₁₀]
    refine (f₀₈.trans (c₉.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)).sub
      fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self, fun _ h => h⟩
    simp only [List.mem_singleton] at hr; subst hr
    rw [b₈]; exact Region.sub_prefix (by omega_arith)

theorem expandKey_wp {s₀ : State} (hp : expandKeyArm.pre s₀) :
    WP isa expandKey s₀ fun s' => (∀ i < 9, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧ expandKeyArm.post s₀ s' := by
  obtain ⟨s₁, e₁, h₁⟩ := ekHead_ok hp
  obtain ⟨hrd, hwr, dKS, dKB, dSB, fitK, fitS, fitB⟩ := hp
  let b := s₀.gpr .r2
  let S := s₀.gpr .r1
  obtain hwB : ScrIn s₀.wr b := ⟨by rw [hwr]; simp [b], fitB⟩
  obtain hwS : (⟨State.addr S, 128⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [S]
  obtain pre : EkPre s₀ b S := ⟨hwB, hwS, dSB, fitS⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, WP.seq (WP.mono (ekLoop_wp pre h₁) fun s₂ h₂ => ?_)⟩)
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃, sp₃⟩ := movR_ok s₂ .r12 sb
  obtain ⟨s₄, e₄, rg₄, -, m₄, -, -, -⟩ := restore_ok (s₀ := s₀) (b := b) (by rw [wr₃, h₂.wr]; exact hwB)
    (by rw [r₃, h₂.base]) (by rw [m₃]; exact h₂.saved)
  refine WP.of_runBlock ⟨s₄, by rw [runBlock_app, e₃, Option.bind_some, e₄], rg₄, ?_⟩
  show Spec.Sm4.scheduleAt s₄.mem (State.addr S) = _
  rw [expandKey_eq]
  apply Vector.ext
  intro i hi
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [show k = 8 * (k / 8) + k % 8 by omega_arith, VG.Proof.Sm4.getLsbD_scheduleAt _ _ hi (by omega_arith) (by omega_arith),
    Vector.getElem_ofFn, m₄, m₃]
  exact h₂.sched i (by omega_arith) _ (by omega_arith) _ (by omega_arith)

end VG.Proof.Sm4.Arm

end

end

/-!
# SM4 key expansion on ARMv7 meets its contracts

`expandKey_verified`: `expandKey` is correct (`expandKey_wp`) and constant
time, by the taint analysis: the pointers are public, and so is the
schedule's pointer the code keeps in a slot of the scratch buffer (stored
through `sb`, the buffer's base, after each extraction). `expandKey_framed`
runs it with its working space on the stack, zeroed on return, as
`ecbAny_framed` does.
-/

@[expose] public section

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Impl.Sm4.Arm
open VG.Proof.Sm4 (expandKeyArm)

/-- The initial taint: the pointers are public; `r1` and `r2` point at the
schedule and the scratch buffer, the writable regions. -/
def expandKeyTaint : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2], flags := false, lens := [128, 4 * slots], bases := [(.r1, 0), (.r2, 1)] }

theorem expandKeyTaint_wf {s : State} (h : expandKeyArm.pre s) : VG.Arm.Taint.Wf expandKeyTaint s := by
  obtain ⟨-, hwr, -, -, dSB, -, fitS, fitB⟩ := h
  refine ⟨fun _ => ⟨by simp [hwr, expandKeyTaint], ?_, ?_⟩, fun p hp => ?_, fun h => by simp [expandKeyTaint] at h,
    fun p hp => by simp [expandKeyTaint] at hp⟩
  · simp only [hwr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil]
    exact ⟨dSB, fun _ h => h.elim, trivial⟩
  · simp only [hwr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [addr_toNat] <;> omega_arith
  · simp only [expandKeyTaint, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [VG.Arm.Taint.region, hwr]

theorem expandKeyTaint_agree (s₁ s₂ : State) (h₁ : expandKeyArm.pre s₁) (h₂ : expandKeyArm.pre s₂)
    (hp : expandKeyArm.pub s₁ s₂) : VG.Arm.Taint.Agree expandKeyTaint s₁ s₂ := by
  obtain ⟨p0, p1, p2, -⟩ := hp
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, expandKeyTaint_wf h₁, expandKeyTaint_wf h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun h => by simp [expandKeyTaint] at h, fun k hk => by simp [expandKeyTaint] at hk⟩
  · simp only [expandKeyTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption
  · rw [h₁.2.1, h₂.2.1, p1, p2]

theorem expandKey_ct : ConstantTime isa expandKeyArm.pre expandKeyArm.pub expandKey :=
  VG.Taint.constantTime (A := VG.Arm.taint) expandKeyTaint expandKeyTaint_agree (by taint_decide)

theorem expandKey_correct (s : State) (hs : expandKeyArm.pre s) :
    ∃ t s', Exec isa expandKey s t s' ∧ abiPreserved s s' ∧ expandKeyArm.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := expandKey_wp hs
  refine ⟨t, s', he, ⟨fun r hr => ?_, VG.Arm.Exec.sp he⟩, h₂⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁ 0 (by omega_using [])
  · exact h₁ 1 (by omega_using [])
  · exact h₁ 2 (by omega_using [])
  · exact h₁ 3 (by omega_using [])
  · exact h₁ 4 (by omega_using [])
  · exact h₁ 5 (by omega_using [])
  · exact h₁ 6 (by omega_using [])
  · exact h₁ 7 (by omega_using [])
  · exact h₁ 8 (by omega_using [])

/-- A state satisfying the precondition. -/
def expandKeySat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 4 * 364⟩]

theorem expandKey_verified :
    Verified Arm.target expandKey (Proof.Sm4.expandKeyScratchContract Arm.abi 182) :=
  Verified.of_correct expandKey_correct expandKey_ct (by
    sig_implies [Proof.Sm4.expandKeyScratchContract, Proof.Sm4.expandKeyScratchSig, Proof.Sm4.expandKeyPost,
      expandKeyArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, State.addr, slots, nSlot, dSlot,
      savedSlot, tableEnd, tableSlot]
      [expandKeySat] using expandKeySat)

/-- A state satisfying the key schedule's precondition: the key at
`0x1000`, the schedule at `0x2000`. -/
def expandKeyFrameSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 16⟩]
  wr := [⟨0x2000, 128⟩]

theorem expandKeyFrameSat_pre : ∃ s, (Spec.Sm4.expandKeyContract Arm.abi 1456).pre s := by
  implies_sat [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [expandKeyFrameSat] using expandKeyFrameSat

/-- Key expansion, with its working space on the stack. -/
theorem expandKey_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withRegScratchWiped 1456 .r2 364 expandKey)
      (Spec.Sm4.expandKeyContract Arm.abi 1456) :=
  Arm.Verified.regScratchWiped (sig := Spec.Sm4.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 182) (post := Proof.Sm4.expandKeyPost Arm.abi.ptrBits) (wa := false) (stack := 0)
    expandKey_verified (by decide) (by decide) (by decide) (by decide)
    (Proof.Sm4.expandKeyPostOut_local _) expandKeyFrameSat_pre

/-- `expandKey_framed`, its working space not wiped: its function's cleanup (`scrubAll`) zeroes it. -/
theorem expandKey_framedU :
    Verified Arm.target (Impl.StackScratch.Arm.withRegScratch 1456 .r2 expandKey)
      (Spec.Sm4.expandKeyContract Arm.abi 1456) :=
  Arm.Verified.regScratch (sig := Spec.Sm4.expandKeySig) (nm := "scratch") (e := .u64)
    (n := 182) (post := Proof.Sm4.expandKeyPost Arm.abi.ptrBits) (wa := false) (stack := 0)
    expandKey_verified (by decide) (by decide) (by decide)
    (fun vs mm m₁ m₂ r hl _ => Proof.Sm4.expandKeyPostOut_local _ vs mm m₁ m₂ r hl) expandKeyFrameSat_pre

end VG.Proof.Sm4.Arm

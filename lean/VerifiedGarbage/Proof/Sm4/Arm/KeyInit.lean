import VerifiedGarbage.Proof.Sm4.Arm.Ecb
import VerifiedGarbage.Proof.Sm4.Planes

/-!
# The start of the SM4 key schedule on ARMv7

As on AArch64: the planes of `CK` stored as constants (`constStores_ok`),
and `MK ⊕ FK` stored to the eight blocks of the tail buffer
(`loadKeyWord_ok`), whose words, bitsliced, are the key schedule's initial
state `keyInit` (`keyInit_rel`).
-/

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
  simp only [tailAt, tailSlot_eq, slots_eq]; omega

/-- Word `w` of the key at `K`, XOR `FK`, to the eight blocks. -/
theorem loadKeyWord_ok {s : State} {b K : BitVec 32} (w : Nat) (hw4 : w < 4) (hb : s.gpr sb = b)
    (hw : ScrIn s.wr b) (hK : s.gpr .r0 = K) (hr : InRegions (s.rd ++ s.wr) (wordAddr K w) 4) :
    ∃ s', runBlock isa (loadKeyWord w) s = some s' ∧
      (∀ c < 8, s'.mem.readW (wordAddr b (tailAt c w)) 32 = s.mem.readW (wordAddr K w) 32 ^^^ fkLE w) ∧
      (∀ k < slots, (∀ c < 8, k ≠ tailAt c w) →
        s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32) ∧
      (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      Frame [⟨State.addr b, 4 * slots⟩] s.mem s'.mem := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := ldW_ok s t0 .r0 (k := w) hK (by omega) hr
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
  rw [readW_bit _ _ (by omega) hj, VG.Proof.Sm4.blockAt_getD _ _ hi, hb,
    byte_addr b (k := tailAt c (i / 4)) rfl (by simp only [tailAt, tailSlot_eq]; rw [slots_eq] at hfit; omega),
    VG.Offset.add_add, tailAt]
  rw [show 4 * tailSlot + 16 * c + i = 4 * (tailSlot + 4 * c + i / 4) + i % 4 by omega]

/-- The tail buffer's blocks are `MK ⊕ FK`, from the key's words `K w`. -/
theorem keyInit_rel {s : State} {b : BitVec 32} (hb : s.gpr sb = b) (hfit : b.toNat + 4 * slots ≤ 2 ^ 32)
    {key : Spec.Sm4.Block} {K : Nat → BitVec 32}
    (hK : ∀ w < 4, ∀ t < 4, ∀ j < 8, (K w).getLsbD (8 * t + j) = (key.getD (4 * w + t) 0).getLsbD j)
    (hT : ∀ c < 8, ∀ w < 4, s.mem.readW (wordAddr b (tailAt c w)) 32 = K w ^^^ fkLE w) :
    ∀ c < 8, ∀ w < 4, VG.Proof.Sm4.ofBlock (tailBlock s c) w = keyInit key w := by
  intro c hc w hw
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hi : 3 - k / 8 < 4 := by omega
  rw [show k = 8 * (3 - (3 - k / 8)) + k % 8 by omega]
  simp only [VG.Proof.Sm4.ofBlock, keyInit]
  rw [BitVec.getLsbD_xor, getLsbD_wordAt _ _ hi (by omega), getLsbD_wordAt _ _ hi (by omega),
    tailBlock_bit s hb hfit hc (by omega) (by omega), show (4 * w + (3 - k / 8)) / 4 = w by omega,
    hT c hc w hw, BitVec.getLsbD_xor, fkLE_bit (by omega), show (4 * w + (3 - k / 8)) % 4 = 3 - k / 8 by omega,
    hK w hw _ hi _ (by omega)]
  congr 2
  omega

end VG.Proof.Sm4.Arm

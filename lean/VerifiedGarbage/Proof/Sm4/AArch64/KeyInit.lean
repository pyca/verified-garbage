import VerifiedGarbage.Proof.Sm4.AArch64.Ecb
import VerifiedGarbage.Proof.Sm4.Planes

/-!
# The start of the SM4 key schedule on AArch64

As on x86-64: the planes of `CK` stored as constants (through
`setSlotsN_ok`), and `MK ⊕ FK` stored to the sixteen blocks of the tail
buffer (`loadHalf_ok`), whose words, bitsliced, are the key schedule's
initial state `keyInit`.
-/

namespace VG.Proof.Sm4.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Sm4.AArch64
open VG.Impl.Aes.AArch64 (q sb t0 t1 movR ldS stS eorR imm)
open VG.Impl.Sm4 (planeOf fkWord)

/-! ## Stores of a register -/

/-- `str r, [sb, #8 k]` for each `k` of `ks`. -/
theorem storeAll_ok (r : Reg) : ∀ (ks : List Nat) {s : State} {b : Addr}, s.gpr sb = b →
    (⟨b, 8 * slots⟩ : Region) ∈ s.wr → (∀ k ∈ ks, k < slots) →
    ∃ s', runBlock isa (ks.map fun k => stS k r) s = some s' ∧ (∀ k ∈ ks, slotW s' k = s.gpr r) ∧
      (∀ k < slots, k ∉ ks → slotW s' k = slotW s k) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨b, 8 * slots⟩] s.mem s'.mem
  | [], s, _, _, _, _ => ⟨s, rfl, by simp, fun _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | k :: ks, s, b, hb, hw, hk => by
    have hk0 : k < slots := hk k List.mem_cons_self
    have e₁ := stS_ok s r (k := k) (by rw [slots_eq] at hk0; omega) ⟨_, hw, by
      rw [hb]; exact VG.Offset.contains_base b (by omega) (by rw [slots_eq] at hk0; omega)⟩
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
        (show 8 * k + 8 ≤ 8 * slots by omega) _ (by simp only [Region.Contains]; omega))

/-! ## `MK ⊕ FK` -/

/-- `ldr d, [r, #n]`. -/
theorem loadAt_ok (s : State) (d r : Reg) (n : Nat) (hn : n % 8 = 0 ∧ n < 32768)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr r + BitVec.ofNat 64 n) 8) :
    ∃ s', runBlock isa [.ldr .x d r n] s = some s' ∧
      s'.gpr d = s.mem.readW (s.gpr r + BitVec.ofNat 64 n) 64 ∧
      (∀ r', r' ≠ d → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.write .x d (s.mem.readW (s.gpr r + BitVec.ofNat 64 n) 64), by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_ldr_x hn hr],
    by simp only [RegUpd.gpr_write_self, BitVec.setWidth_eq], fun r' h => RegUpd.gpr_write_of_ne _ _ _ h,
    rfl, rfl, rfl⟩

/-- `eor d, d, r`. -/
theorem xorReg_ok (s : State) (d r : Reg) :
    ∃ s', runBlock isa [eorR d d r] s = some s' ∧ s'.gpr d = s.gpr d ^^^ s.gpr r ∧
      (∀ r', r' ≠ d → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.write .x d (s.gpr d ^^^ s.gpr r), by simp only [eorR, runBlock_cons]; rfl,
    by simp only [RegUpd.gpr_write_self, BitVec.setWidth_eq], fun r' h => RegUpd.gpr_write_of_ne _ _ _ h,
    rfl, rfl, rfl⟩

/-- `ldr t0, [x0, #8 h]; imm t1, FK; eor t0, t0, t1`. -/
theorem keyWord_ok (s : State) (h : Nat) (hh : h < 2)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (8 * h)) 8) :
    ∃ s', runBlock isa ([.ldr .x t0 .x0 (8 * h)] ++ imm t1 (fkWord h) ++ [eorR t0 t0 t1]) s = some s' ∧
      s'.gpr t0 = s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 (8 * h)) 64 ^^^ fkWord h ∧
      (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := loadAt_ok s t0 .x0 (8 * h) ⟨by omega, by omega⟩ hr
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂⟩ := imm_ok s₁ t1 (fkWord h)
  obtain ⟨s₃, e₃, v₃, o₃, m₃, rd₃, wr₃⟩ := xorReg_ok s₂ t0 t1
  refine ⟨s₃, ?_, ?_, fun r h0 h1 => by rw [o₃ r h0, o₂ r h1, o₁ r h0], by rw [m₃, m₂, m₁],
    by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁]⟩
  · rw [runBlock_app, runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some, e₃]
  · rw [v₃, o₂ _ (by decide), v₁, v₂]

theorem tailAt_lt {b h : Nat} (hb : b < 16) (hh : h < 2) : tailAt b h < slots := by
  simp only [tailAt, tailSlot_eq, slots_eq]; omega

/-- Half `h` of the key, XOR `FK`, to the sixteen blocks. -/
theorem loadHalf_ok {s : State} {b : Addr} (h : Nat) (hh : h < 2) (hb : s.gpr sb = b)
    (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (8 * h)) 8) :
    ∃ s', runBlock isa (loadHalf h) s = some s' ∧
      (∀ c < 16, slotW s' (tailAt c h) = s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 (8 * h)) 64 ^^^ fkWord h) ∧
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

end VG.Proof.Sm4.AArch64

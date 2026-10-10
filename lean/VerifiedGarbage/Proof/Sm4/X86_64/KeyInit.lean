import VerifiedGarbage.Proof.Sm4.X86_64.Ecb

/-!
# The start of the SM4 key schedule on x86-64

The planes of `CK` stored as immediates (`ckTable_ok`, through
`setMasksN_ok`), and `MK ⊕ FK` stored to the sixteen blocks of the tail
buffer (`loadHalf_ok`), whose words, bitsliced, are the key schedule's
initial state `keyInit` (`keyInit_rel`).
-/

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Sm4.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR movS st at_ xorR setMasks)
open VG.Proof.Sm4 (WordRel ofBlock keyInit readW64_bit getLsbD_wordAt blockAt_getD ofInt_nat)

/-! ## Planes of constants -/

theorem planeOf_bit (x : BitVec 32) (j : Nat) {p : Nat} (hp : p < 64) :
    (planeOf x j).getLsbD p = x.getLsbD (8 * (3 - p / 16) + j) := by
  rw [planeOf, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range hp]
  simp [hp]

theorem planeOf_rel (x : BitVec 32) : WordRel (planeOf x) (fun _ => x) := fun b _ i hi j _ => by
  rw [planeOf_bit x j (by omega), show (16 * i + b) / 16 = i by omega]

theorem fkWord_bit {h t : Nat} (ht : t < 64) :
    (fkWord h).getLsbD t = (Spec.Sm4.fk.getD (2 * h + t / 32) 0).getLsbD (8 * (3 - t % 32 / 8) + t % 8) := by
  rw [fkWord, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range ht]
  simp [ht]

/-! ## Stores of a register -/

/-- `mov [sb + 8 k], r` for each `k` of `ks`. -/
theorem storeAll_ok (r : Reg) (hr : r ≠ sb) : ∀ (ks : List Nat) {s : State} {b : Addr}, s.gpr sb = b →
    (⟨b, 8 * slots⟩ : Region) ∈ s.wr → (∀ k ∈ ks, k < slots) →
    ∃ s', runBlock isa (ks.map fun k => st k r) s = some s' ∧ (∀ k ∈ ks, slotW s' k = s.gpr r) ∧
      (∀ k < slots, k ∉ ks → slotW s' k = slotW s k) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨b, 8 * slots⟩] s.mem s'.mem
  | [], s, _, _, _, _ => ⟨s, rfl, by simp, fun _ _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | k :: ks, s, b, hb, hw, hk => by
    have hk0 : k < slots := hk k List.mem_cons_self
    obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁⟩ := stReg_ok (k := k) r hb ⟨_, hw, by
      rw [wordAddr]; exact VG.Offset.contains_base b (by omega) (by rw [slots_eq] at hk0; omega)⟩
    obtain ⟨s', e', v', o', g', rd', wr', f'⟩ := storeAll_ok r hr ks (s := s₁) (by rw [g₁, hb])
      (by rw [wr₁]; exact hw) fun k h => hk k (List.mem_cons_of_mem _ h)
    have hslot : ∀ j < slots, slotW s₁ j = if j = k then s.gpr r else slotW s j := fun j hj => by
      simp only [slotW, g₁, hb, m₁]
      exact readW_slot_write _ hj hk0
    refine ⟨s', by rw [List.map_cons, show (st k r :: ks.map fun k => st k r) = [st k r] ++ ks.map fun k => st k r
        from rfl, runBlock_app, e₁, Option.bind_some, e'], fun j hj => ?_, fun j hj hn => ?_,
      by rw [g', g₁], by rw [rd', rd₁], by rw [wr', wr₁], ?_⟩
    · rcases List.mem_cons.mp hj with rfl | hj'
      · by_cases hin : j ∈ ks
        · rw [v' j hin, g₁]
        · rw [o' j hk0 hin, hslot j hk0, ite_eq_left rfl]
      · rw [v' j hj', g₁]
    · simp only [List.mem_cons, not_or] at hn
      rw [o' j hj hn.2, hslot j hj, ite_eq_right hn.1]
    · refine Frame.trans (fun x hx => ?_) f'
      rw [m₁]
      simp only [Mem.writeW, Mem.write, wordAddr]
      exact ite_eq_right fun h => hx _ (List.mem_singleton_self _) (VG.Offset.sub_base b
        (show 8 * k + 8 ≤ 8 * slots by omega) _ (by simp only [Region.Contains]; omega))

/-! ## `MK ⊕ FK` -/

/-- `mov d, [r + n]`. -/
theorem loadAt_ok (s : State) (d r : Reg) (n : Nat) (hr : InRegions (s.rd ++ s.wr) (s.gpr r + BitVec.ofNat 64 n) 8) :
    ∃ s', runBlock isa [.mov d (.mem (at_ r n))] s = some s' ∧
      s'.gpr d = s.mem.readW (s.gpr r + BitVec.ofNat 64 n) 64 ∧
      (∀ r', r' ≠ d → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨s.setReg d (s.mem.readW (s.gpr r + BitVec.ofNat 64 n) 64), ?_, by simp only [RegUpd.gpr_setReg_self],
    fun r' h => by simp only [RegUpd.gpr_setReg_of_ne _ _ h], rfl, rfl, rfl⟩
  simp only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, State.ea, ofInt_nat,
    hr, ite_true, Option.map_some]

/-- `xor d, r`. -/
theorem xorReg_ok (s : State) (d r : Reg) :
    ∃ s', runBlock isa [xorR d r] s = some s' ∧ s'.gpr d = s.gpr d ^^^ s.gpr r ∧
      (∀ r', r' ≠ d → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨(arithFlags s (s.gpr d ^^^ s.gpr r) false false).setReg d (s.gpr d ^^^ s.gpr r), by
    simp only [xorR, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some], ?_, fun r' h => ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_setReg_self]
  · simp only [RegUpd.gpr_setReg_of_ne _ _ h, RegUpd.gpr_arithFlags]

/-- `mov t0, [rdi + 8 h]; mov t1, FK; xor t0, t1`. -/
theorem keyWord_ok (s : State) (h : Nat) (hr : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (8 * h)) 8) :
    ∃ s', runBlock isa [.mov t0 (.mem (at_ .rdi (8 * h))), .movImm64 t1 (fkWord h), xorR t0 t1] s = some s' ∧
      s'.gpr t0 = s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (8 * h)) 64 ^^^ fkWord h ∧
      (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := loadAt_ok s t0 .rdi (8 * h) hr
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂⟩ := movImm_ok s₁ t1 (fkWord h)
  obtain ⟨s₃, e₃, v₃, o₃, m₃, rd₃, wr₃⟩ := xorReg_ok s₂ t0 t1
  refine ⟨s₃, ?_, ?_, fun r h0 h1 => by rw [o₃ r h0, o₂ r h1, o₁ r h0], by rw [m₃, m₂, m₁],
    by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁]⟩
  · rw [show ([.mov t0 (.mem (at_ .rdi (8 * h))), .movImm64 t1 (fkWord h), xorR t0 t1] : List Instr) =
      [.mov t0 (.mem (at_ .rdi (8 * h)))] ++ ([.movImm64 t1 (fkWord h)] ++ [xorR t0 t1]) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, e₃]
  · rw [v₃, o₂ _ (by decide), v₁, v₂]

theorem tailAt_lt {b h : Nat} (hb : b < 16) (hh : h < 2) : tailAt b h < slots := by
  simp only [tailAt, tailSlot_eq, slots_eq]; omega

/-- Half `h` of the key, XOR `FK`, to the sixteen blocks. -/
theorem loadHalf_ok {s : State} {b : Addr} (h : Nat) (hh : h < 2) (hb : s.gpr sb = b)
    (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (8 * h)) 8) :
    ∃ s', runBlock isa (loadHalf h) s = some s' ∧
      (∀ c < 16, slotW s' (tailAt c h) = s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (8 * h)) 64 ^^^ fkWord h) ∧
      (∀ k < slots, (∀ c < 16, k ≠ tailAt c h) → slotW s' k = slotW s k) ∧
      (∀ r, r ≠ t0 → r ≠ t1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨b, 8 * slots⟩] s.mem s'.mem := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := keyWord_ok s h hr
  obtain ⟨s', e', v', k', g', rd', wr', f'⟩ := storeAll_ok t0 (by decide) ((List.range 16).map fun c => tailAt c h)
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

end VG.Proof.Sm4.X86_64

import VerifiedGarbage.Proof.Camellia.AArch64.Core

/-!
# The head and tail of eight blocks of bitsliced Camellia on AArch64

As on x86-64: `head` loads and bitslices both halves of the eight blocks
in the tail buffer and whitens them, and `tail` whitens, transposes and
stores them back; between them the groups of rounds (`group_wp`) run in a
loop. `crypt8_ok` composes them: each block becomes `cryptWords g E` of it.
The blocks' words are loaded and stored by symbolic execution
(`ldS_list_ok`, `stS_list_ok`), which keeps the rest of the scratch buffer.
-/

namespace VG.Proof.Camellia.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Camellia.AArch64
open VG.Impl.Aes.AArch64 (q sb t0 t1 kp movR ldS stS)
open VG.Proof.Camellia (HalfRel WordRel pair group groups cryptWords toBsG fromBsG pos cpos)

/-! ## Loads and stores of slots -/

/-- Loads of slots into distinct registers other than `sb`. -/
theorem ldS_list_ok : ∀ (L : List (Reg × Nat)) (s : State), (∀ x ∈ L, x.1 ≠ sb) → (L.map (·.1)).Nodup →
    (∀ x ∈ L, 8 * x.2 < 32768 ∧ InRegions (s.rd ++ s.wr) (s.gpr sb + BitVec.ofNat 64 (8 * x.2)) 8) →
    ∃ s', runBlock isa (L.map fun x => ldS x.1 x.2) s = some s' ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ (∀ r, r ∉ L.map (·.1) → s'.gpr r = s.gpr r) ∧ ∀ x ∈ L, s'.gpr x.1 = slotW s x.2
  | [], s, _, _, _ => ⟨s, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ h => absurd h List.not_mem_nil⟩
  | x :: L, s, hsb, hnd, hin => by
    have hx := hin x List.mem_cons_self
    obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldMask_ok (r := x.1) (k := x.2) hx.1 hx.2 rfl
    have hb₁ : s₁.gpr sb = s.gpr sb := o₁ _ (hsb x List.mem_cons_self).symm
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', m', rd', wr', o', v'⟩ := ldS_list_ok L s₁ (fun y hy => hsb y (List.mem_cons_of_mem _ hy))
      hnd.2 (fun y hy => by rw [rd₁, wr₁, hb₁]; exact hin y (List.mem_cons_of_mem _ hy))
    refine ⟨s', ?_, m'.trans m₁, rd'.trans rd₁, wr'.trans wr₁, fun r hr => ?_, fun y hy => ?_⟩
    · rw [List.map_cons, ← List.singleton_append, runBlock_append', e₁, Option.bind_some]; exact e'
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [o' r hr.2, o₁ r hr.1]
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact (o' _ hnd.1).trans v₁
      · rw [v' y hy]; simp only [slotW, m₁, hb₁]

/-- `str t, [sb, #8 k]`. -/
theorem stS_ok (s : State) {k : Nat} (t : Reg) (hk : 8 * k < 32768)
    (hin : InRegions s.wr (s.gpr sb + BitVec.ofNat 64 (8 * k)) 8) :
    runBlock isa [stS k t] s = some { s with mem := s.mem.writeW (wordAddr (s.gpr sb) k) (s.gpr t) } := by
  simp only [stS, runBlock_cons, runStep_some, runBlock_nil, exec_str_x ⟨by omega, hk⟩ hin]

/-- Stores of registers to distinct slots in the region `R`. -/
theorem stS_list_ok (R : Region) : ∀ (L : List (Nat × Reg)) (s : State), (L.map (·.1)).Nodup →
    (∀ x ∈ L, 8 * x.1 < 32768 ∧ InRegions s.wr (s.gpr sb + BitVec.ofNat 64 (8 * x.1)) 8 ∧
      R.Contains (wordAddr (s.gpr sb) x.1) 8) →
    ∃ s', runBlock isa (L.map fun x => stS x.1 x.2) s = some s' ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ Frame [R] s.mem s'.mem ∧
      (∀ k, k ∉ L.map (·.1) → k < 2 ^ 58 → slotW s' k = slotW s k) ∧ ∀ x ∈ L, slotW s' x.1 = s.gpr x.2
  | [], s, _, _ => ⟨s, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ _ _ => rfl,
      fun _ h => absurd h List.not_mem_nil⟩
  | x :: L, s, hnd, hin => by
    have hx := hin x List.mem_cons_self
    let s₁ : State := { s with mem := s.mem.writeW (wordAddr (s.gpr sb) x.1) (s.gpr x.2) }
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', g', rd', wr', f', o', v'⟩ :=
      stS_list_ok R L s₁ hnd.2 fun y hy => hin y (List.mem_cons_of_mem _ hy)
    have hsep : ∀ k, k ≠ x.1 → k < 2 ^ 58 → slotW s₁ k = slotW s k := fun k hk hk58 =>
      Mem.readW_writeW_sep (slot_sep _ (by omega) (by omega) hk) (by decide)
    refine ⟨s', ?_, g', rd', wr', ?_, fun k hk hk58 => ?_, fun y hy => ?_⟩
    · rw [List.map_cons, ← List.singleton_append, runBlock_append', stS_ok s x.2 hx.1 hx.2.1,
        Option.bind_some]
      exact e'
    · exact ((Frame.refl _ _).writeW (List.mem_singleton_self R) _ hx.2.2).trans f'
    · simp only [List.map_cons, List.mem_cons, not_or] at hk
      rw [o' k hk.2 hk58]; exact hsep k hk.1 hk58
    · rcases List.mem_cons.mp hy with rfl | hy
      · rw [o' _ hnd.1 (by omega)]; exact Mem.readW_writeW_self64 _ _ _
      · exact v' y hy

/-! ## The scratch buffer -/

/-- Word `k` of the blocks, in the tail buffer. -/
abbrev dataW (s : State) (k : Nat) : BitVec 64 := slotW s (tailSlot + k)

/-- The tail buffer. -/
def tailRegion (b : Addr) : Region := ⟨b + BitVec.ofNat 64 (8 * tailSlot), 128⟩

theorem Ctx.inWr {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {k : Nat} (hk : k < slots) : InRegions s.wr (s.gpr sb + BitVec.ofNat 64 (8 * k)) 8 := by
  have hfit := hp.fit
  rw [slots_eq] at hfit hk
  refine ⟨_, by rw [hc.wr]; exact hp.scr, ?_⟩
  rw [hc.base, slots_eq]
  exact VG.Offset.contains_base _ (by omega) (by omega)

theorem Ctx.inRd {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {k : Nat} (hk : k < slots) : InRegions (s.rd ++ s.wr) (s.gpr sb + BitVec.ofNat 64 (8 * k)) 8 := by
  obtain ⟨r, hr, hc'⟩ := hc.inWr hp hk
  exact ⟨r, List.mem_append_right _ hr, hc'⟩

theorem tail_contains {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E)
    (hc : Ctx s₀ s) {k : Nat} (hk : k < 16) :
    (tailRegion (s₀.gpr sb)).Contains (wordAddr (s.gpr sb) (tailSlot + k)) 8 := by
  have hfit := hp.fit
  rw [slots_eq] at hfit
  rw [hc.base, tailRegion, wordAddr]
  exact VG.Offset.contains _ (by omega) (by rw [tailSlot_eq]; omega) (by rw [tailSlot_eq]; omega)

/-- A frame of the rounds' working space keeps the slots from the table on. -/
theorem slotW_above {s₀ s s' : State} (hc : Ctx s₀ s) (hb : s'.gpr sb = s.gpr sb)
    (hf : Frame [⟨s₀.gpr sb, 8 * keySlot⟩] s.mem s'.mem) {k : Nat} (hk : keySlot ≤ k) (hk' : k < 2 ^ 58) :
    slotW s' k = slotW s k := by
  simp only [slotW, hb, hc.base]; exact slot_above hf hk hk'

theorem mask_lt {kv : Nat × BitVec 64} (hkv : kv ∈ layerMasks) : kv.1 < keySlot := by
  simp [layerMasks] at hkv; rcases hkv with h | h | h | h | h <;> subst h <;>
    simp [keySlot, evenSlot, oddSlot, m4Slot, m2Slot, m3Slot]

theorem mask_ne_tail {kv : Nat × BitVec 64} (hkv : kv ∈ layerMasks) (k : Nat) : kv.1 ≠ tailSlot + k := by
  have := mask_lt hkv; rw [keySlot_eq] at this; rw [tailSlot_eq]; omega

/-! ## The steps -/

/-- `loadWords h`. -/
theorem loadWords_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E)
    (hc : Ctx s₀ s) {h : Nat} (hh : h = 0 ∨ h = 1) :
    ∃ s', runBlock isa (loadWords h) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      s'.gpr .x0 = s.gpr .x0 ∧ (∀ b < 8, Qs s' b = dataW s (2 * b + h)) ∧ ∀ k, slotW s' k = slotW s k := by
  let L : List (Reg × Nat) := (List.range 8).map fun b => (q b, tailSlot + 2 * b + h)
  have hregs : L.map (·.1) = (List.range 8).map q := by simp only [L, List.map_map]; rfl
  have hL : loadWords h = L.map fun x => ldS x.1 x.2 := by simp only [L, loadWords, List.map_map]; rfl
  have hmem : ∀ {x}, x ∈ L → ∃ b < 8, x = (q b, tailSlot + 2 * b + h) := fun hx => by
    simp only [L, List.mem_map, List.mem_range] at hx
    obtain ⟨b, hb, rfl⟩ := hx; exact ⟨b, hb, rfl⟩
  obtain ⟨s', e', m', rd', wr', o', v'⟩ := ldS_list_ok L s
    (fun x hx => by obtain ⟨b, hb, rfl⟩ := hmem hx; exact q_ne_sb b hb)
    (by rw [hregs]; decide)
    (fun x hx => by
      obtain ⟨b, hb, rfl⟩ := hmem hx
      have : tailSlot + 2 * b + h < slots := by rw [tailSlot_eq, slots_eq]; omega
      exact ⟨by rw [tailSlot_eq] at this ⊢; omega, hc.inRd hp this⟩)
  have hkeep : ∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r := fun r hr => o' r (by
    rw [hregs]; intro hm
    simp only [List.mem_map, List.mem_range] at hm
    obtain ⟨b, hb, rfl⟩ := hm
    exact hr (by revert b; decide))
  have hs : ∀ k, slotW s' k = slotW s k := fun k => by
    simp only [slotW, m', hkeep sb (by decide)]
  refine ⟨s', by rw [hL]; exact e', hc.step rd' wr' (fun r hr _ _ => hkeep r hr)
    (by rw [m']; exact Frame.refl _ _) (fun kv hkv => by rw [hs]; exact hc.masks kv hkv),
    hkeep _ (by decide), hkeep _ (by decide), fun b hb => ?_, hs⟩
  rw [Qs, dataW, ← Nat.add_assoc]
  exact v' (q b, tailSlot + 2 * b + h) (by simp only [L, List.mem_map, List.mem_range]; exact ⟨b, hb, rfl⟩)

/-- `storeWords h`. -/
theorem storeWords_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E)
    (hc : Ctx s₀ s) {h : Nat} (hh : h = 0 ∨ h = 1) :
    ∃ s', runBlock isa (storeWords h) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr = s.gpr ∧
      (∀ b < 8, dataW s' (2 * b + h) = Qs s b) ∧
      (∀ b < 8, dataW s' (2 * b + (1 - h)) = dataW s (2 * b + (1 - h))) ∧
      (∀ k < tailSlot, slotW s' k = slotW s k) := by
  let L : List (Nat × Reg) := (List.range 8).map fun b => (tailSlot + 2 * b + h, q b)
  have hslots : L.map (·.1) = (List.range 8).map fun b => tailSlot + 2 * b + h := by
    simp only [L, List.map_map]; rfl
  have hL : storeWords h = L.map fun x => stS x.1 x.2 := by simp only [L, storeWords, List.map_map]; rfl
  have hmem : ∀ {x}, x ∈ L → ∃ b < 8, x = (tailSlot + 2 * b + h, q b) := fun hx => by
    simp only [L, List.mem_map, List.mem_range] at hx
    obtain ⟨b, hb, rfl⟩ := hx; exact ⟨b, hb, rfl⟩
  have hnot : ∀ k, (k < tailSlot ∨ ∀ b < 8, k ≠ tailSlot + 2 * b + h) → k ∉ L.map (·.1) := by
    intro k hk hm
    rw [hslots] at hm
    simp only [List.mem_map, List.mem_range] at hm
    obtain ⟨b, hb, rfl⟩ := hm
    rcases hk with hk | hk
    · omega
    · exact hk b hb rfl
  obtain ⟨s', e', g', rd', wr', f', o', v'⟩ := stS_list_ok (tailRegion (s₀.gpr sb)) L s
    (by rw [hslots]; rcases hh with rfl | rfl <;> decide)
    (fun x hx => by
      obtain ⟨b, hb, rfl⟩ := hmem hx
      have : tailSlot + 2 * b + h < slots := by rw [tailSlot_eq, slots_eq]; omega
      refine ⟨by rw [tailSlot_eq] at this ⊢; omega, hc.inWr hp this, ?_⟩
      rw [Nat.add_assoc]; exact tail_contains hp hc (by omega))
  have hlow : ∀ k < tailSlot, slotW s' k = slotW s k := fun k hk =>
    o' k (hnot k (.inl hk)) (by rw [tailSlot_eq] at hk; omega)
  have hmask : MasksOk s' := fun kv hkv => by
    have := mask_lt hkv
    rw [hlow _ (by rw [keySlot_eq] at this; rw [tailSlot_eq]; omega)]
    exact hc.masks kv hkv
  have hf : Frame (ctxRegions (s₀.gpr sb)) s.mem s'.mem :=
    f'.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [ctxRegions, tailRegion, hr]
  refine ⟨s', by rw [hL]; exact e', hc.stepT rd' wr' (fun r _ _ _ => by rw [g']) hf hmask,
    g', fun b hb => ?_, fun b hb => ?_, hlow⟩
  · rw [dataW, ← Nat.add_assoc]
    exact v' (tailSlot + 2 * b + h, q b) (by simp only [L, List.mem_map, List.mem_range]; exact ⟨b, hb, rfl⟩)
  · rw [dataW, dataW, ← Nat.add_assoc]
    have hne : ∀ b' < 8, tailSlot + 2 * b + (1 - h) ≠ tailSlot + 2 * b' + h := fun b' _ h' => by omega
    have h1 := hnot (tailSlot + 2 * b + (1 - h)) (.inr hne)
    have h2 : tailSlot + 2 * b + (1 - h) < 2 ^ 58 := by rw [tailSlot_eq]; omega
    exact o' _ h1 h2

/-- A layer on the state registers over `bothEnv`, keeping the masks, both halves and the blocks. -/
theorem lin_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm34 : m + 2 ≤ 34) {is : List Instr} {G : Nat → Nat → List Nat}
    (hchk : check (lanes 64 12) layerCfg (linExt 24) is bothEnv
      (linPostG 12 (qOuts G) [] (maskSlots ++ bothIns.map (·.1)) bothEnv) = true)
    (hall : (layerKeep.all fun r => is.all fun i => dstOf i != some r) = true) :
    ∃ s', runBlock isa is s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      s'.gpr .x0 = s.gpr .x0 ∧ (∀ j < 8, ∀ p < 64, (Qs s' j).getLsbD p = xorBits (bothW s) (G j p)) ∧
      (∀ j < 16, slotW s' (d1Slot + j) = slotW s (d1Slot + j)) ∧ (∀ k < 16, dataW s' k = dataW s k) ∧
      (∀ k, keySlot ≤ k → k < 2 ^ 58 → slotW s' k = slotW s k) := by
  obtain ⟨s', h', ho, -, hkp, rd', wr', o', f'⟩ := both_ok hp hc hk hm34 hchk
  have hkeep : ∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r := fun r hr =>
    o' r (List.all_eq_true.mp hall r (not_layerWrites r hr))
  refine ⟨s', h', hc.step rd' wr' (fun r hr _ _ => hkeep r hr) f' (fun kv hkv => ?_),
    hkeep _ (by decide), hkeep _ (by decide),
    fun j hj p hp => ho (q j) (G j) (by simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩) p hp,
    fun j hj => hkp _ (List.mem_append_right _ (by
      simp only [bothIns, List.map_map, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩))
      (by simp only [d1Slot, keySlot]; omega),
    fun k hk => slotW_above hc (hkeep _ (by decide)) f' (by rw [keySlot_eq, tailSlot_eq]; omega)
      (by rw [tailSlot_eq]; omega), fun k hk hk' => slotW_above hc (hkeep _ (by decide)) f' hk hk'⟩
  rw [hkp kv.1 (List.mem_append_left _ (List.mem_map_of_mem hkv)) (mask_lt hkv)]
  exact hc.masks kv hkv

/-! ## Transposes -/

theorem toBs_rel {s s' : State} {d : Nat → BitVec 64}
    (h : ∀ j < 8, ∀ p < 64, (Qs s' j).getLsbD p = xorBits (bothW s) (toBsG j p)) (hw : WordRel (Qs s) d) :
    HalfRel (Qs s') d :=
  Camellia.half_of_words (fun j hj p hp => by
    have := Camellia.pos_lt (show p / 8 < 8 by omega)
    rw [h j hj p hp, toBsG, xorBits_cons, xorBits_nil, Bool.xor_false, Nat.add_assoc,
      bitOf_word _ _ _ (by omega), bothW_q s (by omega)]) hw

theorem fromBs_rel {s s' : State} {d : Nat → BitVec 64}
    (h : ∀ j < 8, ∀ p < 64, (Qs s' j).getLsbD p = xorBits (bothW s) (fromBsG j p)) (hq : HalfRel (Qs s) d) :
    WordRel (Qs s') d :=
  Camellia.words_of_half (fun b hb t ht => by
    have := Camellia.cpos_lt (show t / 8 < 8 by omega)
    rw [h b hb t ht, fromBsG, xorBits_cons, xorBits_nil, Bool.xor_false, Nat.add_assoc,
      bitOf_word _ _ _ (by omega), bothW_q s (by omega)]) hq

/-- Block `b` in the tail buffer. -/
abbrev blk (s : State) (b : Nat) : Spec.Camellia.Block :=
  Spec.Camellia.blockAt s.mem (s.gpr sb + BitVec.ofNat 64 (8 * tailSlot + 16 * b))

theorem dataW_byte (s : State) {b i j : Nat} (h : Nat) (hi : i < 8) (hj : j < 8) :
    (dataW s (2 * b + h)).getLsbD (8 * i + j) =
      (s.mem (s.gpr sb + BitVec.ofNat 64 (8 * tailSlot + 16 * b) + BitVec.ofNat 64 (8 * h + i))).getLsbD j := by
  rw [dataW, slotW, Camellia.readW64_bit _ _ hi hj, wordAddr, addr_add, addr_add,
    show 8 * (tailSlot + (2 * b + h)) + i = 8 * tailSlot + 16 * b + (8 * h + i) by omega]

theorem data_hi (s : State) : WordRel (fun b => dataW s (2 * b + 0))
    (fun b => (Spec.Camellia.decodeBlock (blk s b) >>> 64).setWidth 64) := fun b _ i hi j hj => by
  rw [dataW_byte s 0 hi hj, Camellia.byteOf_hi _ hi]
  simp [Spec.Camellia.blockAt]

theorem data_lo (s : State) : WordRel (fun b => dataW s (2 * b + 1))
    (fun b => (Spec.Camellia.decodeBlock (blk s b)).setWidth 64) := fun b _ i hi j hj => by
  rw [dataW_byte s 1 hi hj, Camellia.byteOf_lo _ hi]
  simp [Spec.Camellia.blockAt, Nat.add_comm]

theorem bothW_key (s : State) (j : Nat) : bothW s (24 + j) = keyW s j := by
  simp only [bothW, show ¬ 24 + j < 8 by omega, show ¬ 24 + j < 24 by omega, ↓reduceIte,
    show 24 + j - 24 = j by omega]

theorem bothW_d2 (s : State) {j : Nat} (hj : j < 8) : bothW s (16 + j) = slotW s (d2Slot + j) := by
  simp only [bothW, show ¬ 16 + j < 8 by omega, show 16 + j < 24 by omega, ↓reduceIte,
    show d1Slot + (16 + j - 8) = d2Slot + j by simp only [d1Slot, d2Slot]; omega]

/-- `mov kp, sb; add kp, kp, #8 keySlot`. -/
theorem setKp_ok (s : State) :
    ∃ s', runBlock isa tableSetup s = some s' ∧
      s'.gpr kp = s.gpr sb + BitVec.ofNat 64 (8 * keySlot) ∧ (∀ r, r ≠ kp → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := s.write .x kp (s.gpr sb + BitVec.ofNat 64 0)
  refine ⟨s₁.write .x kp (s₁.gpr kp + BitVec.ofNat 64 (8 * keySlot)), ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [tableSetup, movR, runBlock_cons, runStep_some, runBlock_nil, exec_addImm_x (show 0 < 4096 by decide),
      exec_addImm_x (show 8 * keySlot < 4096 by decide), read_x', s₁]
  · simp only [s₁, RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.add_zero]
  · rw [RegUpd.gpr_write_of_ne _ _ _ hr, RegUpd.gpr_write_of_ne _ _ _ hr]

/-- The whitening. -/
theorem whiten_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm34 : m + 2 ≤ 34) :
    ∃ s', runBlock isa whiten s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      (∀ j < 8, ∀ p < 64, (Qs s' j).getLsbD p = ((Qs s j).getLsbD p ^^ (keyW s j).getLsbD p)) ∧
      (∀ j < 8, ∀ p < 64, (slotW s' (d1Slot + j)).getLsbD p = ((Qs s j).getLsbD p ^^ (keyW s j).getLsbD p)) ∧
      (∀ j < 8, ∀ p < 64, (slotW s' (d2Slot + j)).getLsbD p =
        ((slotW s (d2Slot + j)).getLsbD p ^^ (keyW s (8 + j)).getLsbD p)) := by
  obtain ⟨s', h', ho, hso, hkp, rd', wr', o', f'⟩ := both_ok hp hc hk hm34 whiten_check
  have hall : (layerKeep.all fun r => whiten.all fun i => dstOf i != some r) = true := by decide +kernel
  have hkeep : ∀ r, r ∉ layerWrites → s'.gpr r = s.gpr r := fun r hr =>
    o' r (List.all_eq_true.mp hall r (not_layerWrites r hr))
  refine ⟨s', h', hc.step rd' wr' (fun r hr _ _ => hkeep r hr) f' (fun kv hkv => ?_), hkeep _ (by decide),
    fun j hj p hp => ?_, fun j hj p hp => ?_, fun j hj p hp => ?_⟩
  · rw [hkp kv.1 (List.mem_map_of_mem hkv) (mask_lt hkv)]
    exact hc.masks kv hkv
  · rw [Qs, ho (q j) (keyXorG 0 j) (by simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩) p hp,
      keyXorG, xorBits_cons, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hp,
      Nat.add_assoc, bitOf_word _ _ _ hp, bothW_q s hj, Nat.zero_add, bothW_key]
  · rw [hso (d1Slot + j) (keyXorG 0 j) (List.mem_append_left _ (by
        simp only [List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)) (by simp only [d1Slot, keySlot]; omega) p hp,
      keyXorG, xorBits_cons, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hp,
      Nat.add_assoc, bitOf_word _ _ _ hp, bothW_q s hj, Nat.zero_add, bothW_key]
  · rw [hso (d2Slot + j) (whiten2G j) (List.mem_append_right _ (by
        simp only [List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)) (by simp only [d2Slot, keySlot]; omega) p hp,
      whiten2G, xorBits_cons, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hp,
      bitOf_word _ _ _ hp, bothW_d2 s hj, show 32 + j = 24 + (8 + j) by omega, bothW_key]

/-! ## The head -/

/-- The halves of the eight blocks after the prewhitening. -/
def headHalves (s : State) (E : Nat → BitVec 64) (b : Nat) : BitVec 64 × BitVec 64 :=
  ((Spec.Camellia.decodeBlock (blk s b) >>> 64).setWidth 64 ^^^ E 0,
    (Spec.Camellia.decodeBlock (blk s b)).setWidth 64 ^^^ E 1)

theorem head_ok {s₀ : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) :
    ∃ s', runBlock isa head s₀ = some s' ∧ Ctx s₀ s' ∧ AtEntry s' (s₀.gpr sb) 2 ∧
      Halves s' (headHalves s₀ E) := by
  have hg : 8 * g + 2 ≤ 34 := hp.nk34
  have hc₀ : Ctx s₀ s₀ := Ctx.refl hp.masks
  let b := s₀.gpr sb
  obtain ⟨s₁, e₁, k₁, o₁, m₁, rd₁, wr₁⟩ := setKp_ok s₀
  have hs₁ : ∀ k, slotW s₁ k = slotW s₀ k := fun k => by simp only [slotW, m₁, o₁ sb (by decide)]
  have hc₁ : Ctx s₀ s₁ := hc₀.step rd₁ wr₁ (fun r _ h2 _ => o₁ r h2) (by rw [m₁]; exact Frame.refl _ _)
    (fun kv hkv => by rw [hs₁]; exact hp.masks kv hkv)
  have hk₁ : AtEntry s₁ b 0 := by rw [AtEntry, k₁, Nat.mul_zero, Nat.add_zero]
  -- `D2`.
  obtain ⟨s₂, e₂, c₂, k₂, -, q₂, sl₂⟩ := loadWords_step hp.toKeyCtx hc₁ (Or.inr rfl)
  have hk₂ : AtEntry s₂ b 0 := by rw [AtEntry, k₂]; exact hk₁
  obtain ⟨s₃, e₃, c₃, k₃, -, q₃, -, d₃, -⟩ := lin_step hp.toKeyCtx c₂ hk₂ (by omega) toBs_check (by decide +kernel)
  have hk₃ : AtEntry s₃ b 0 := by rw [AtEntry, k₃]; exact hk₂
  have hD2 : HalfRel (Qs s₃) (fun b => (Spec.Camellia.decodeBlock (blk s₀ b)).setWidth 64) :=
    toBs_rel q₃ fun b' hb i hi j hj => by
      rw [q₂ b' hb, dataW, hs₁]; exact data_lo s₀ b' hb i hi j hj
  obtain ⟨s₄, e₄, c₄, k₄, -, -, sl₄, -, ab₄⟩ :=
    storeHalf_step hp.toKeyCtx c₃ (Or.inr rfl) storeHalf2_check hk₃ (by omega)
  have hk₄ : AtEntry s₄ b 0 := by rw [AtEntry, k₄]; exact hk₃
  -- `D1`.
  obtain ⟨s₅, e₅, c₅, k₅, -, q₅, sl₅⟩ := loadWords_step hp.toKeyCtx c₄ (Or.inl rfl)
  have hk₅ : AtEntry s₅ b 0 := by rw [AtEntry, k₅]; exact hk₄
  obtain ⟨s₆, e₆, c₆, k₆, -, q₆, h₆, -, -⟩ := lin_step hp.toKeyCtx c₅ hk₅ (by omega) toBs_check (by decide +kernel)
  have hk₆ : AtEntry s₆ b 0 := by rw [AtEntry, k₆]; exact hk₅
  have hD1 : HalfRel (Qs s₆) (fun b => (Spec.Camellia.decodeBlock (blk s₀ b) >>> 64).setWidth 64) :=
    toBs_rel q₆ fun b' hb i hi j hj => by
      have e : dataW s₄ (2 * b' + 0) = dataW s₀ (2 * b' + 0) := by
        rw [dataW, ab₄ _ (by rw [keySlot_eq, tailSlot_eq]; omega) (by rw [tailSlot_eq]; omega)]
        have := d₃ (2 * b' + 0) (by omega)
        rw [dataW, dataW] at this
        rw [this, sl₂, hs₁]
      rw [q₅ b' hb, e]
      exact data_hi s₀ b' hb i hi j hj
  have hS₆ : HalfRel (fun j => slotW s₆ (d2Slot + j))
      (fun b => (Spec.Camellia.decodeBlock (blk s₀ b)).setWidth 64) :=
    hD2.congr fun j hj => by
      have h1 := h₆ (8 + j) (by omega)
      rw [show d1Slot + (8 + j) = d2Slot + j by simp only [d1Slot, d2Slot]; omega] at h1
      rw [h1, sl₅, sl₄ j hj]
  -- The whitening.
  obtain ⟨s₇, e₇, c₇, k₇, wq, w1, w2⟩ := whiten_step hp.toKeyCtx c₆ hk₆ (by omega)
  have hK0 := c₆.keyRel hp.toKeyCtx hk₆ (e := 0) (by omega)
  have hK1 := c₆.keyRel hp.toKeyCtx hk₆ (e := 1) (by omega)
  simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one] at hK0 hK1
  obtain ⟨s₈, e₈, kp₈, o₈, m₈, rd₈, wr₈⟩ := addKp_ok s₇ 128 (by decide)
  have hs₈ : ∀ k, slotW s₈ k = slotW s₇ k := fun k => by simp only [slotW, m₈, o₈ sb (by decide)]
  refine ⟨s₈, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [head, runBlock_append', runBlock_append', runBlock_append', runBlock_append', runBlock_append',
      runBlock_append', runBlock_append', e₁, Option.bind_some, e₂, Option.bind_some, e₃, Option.bind_some,
      e₄, Option.bind_some, e₅, Option.bind_some, e₆, Option.bind_some, e₇, Option.bind_some]
    exact e₈
  · refine c₇.step rd₈ wr₈ (fun r _ h2 _ => o₈ r h2) (by rw [m₈]; exact Frame.refl _ _) fun kv hkv => ?_
    rw [hs₈]; exact c₇.masks kv hkv
  · rw [AtEntry, kp₈, k₇, show s₆.gpr kp = _ from hk₆, addr_add]
  · exact (HalfRel.xor_key hD1 hK0 wq).congr fun j hj => o₈ _ (q_ne_kp j hj)
  · exact (HalfRel.xor_key hD1 hK0 w1).congr fun j _ => hs₈ _
  · exact (HalfRel.xor_key hS₆ hK1 w2).congr fun j _ => hs₈ _

/-! ## The tail -/

theorem keyXor_bits {s s' : State} {off : Nat}
    (h : ∀ j < 8, ∀ p < 64, (Qs s' j).getLsbD p = xorBits (bothW s) (keyXorG off j p)) :
    ∀ j < 8, ∀ p < 64, (Qs s' j).getLsbD p = ((Qs s j).getLsbD p ^^ (keyW s (off + j)).getLsbD p) :=
  fun j hj p hp => by
    rw [h j hj p hp, keyXorG, xorBits_cons, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hp,
      bitOf_word _ _ _ hp, bothW_q s hj, Nat.add_assoc, bothW_key]

theorem tail_ok {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s)
    (hk : AtEntry s (s₀.gpr sb) (8 * g)) {S : Nat → BitVec 64 × BitVec 64} (hS : Halves s S) :
    ∃ s', runBlock isa tail s = some s' ∧ Ctx s₀ s' ∧
      WordRel (fun b => dataW s' (2 * b + 0)) (fun b => (S b).2 ^^^ E (8 * g)) ∧
      WordRel (fun b => dataW s' (2 * b + 1)) (fun b => (S b).1 ^^^ E (8 * g + 1)) := by
  have hg : 8 * g + 2 ≤ 34 := hp.nk34
  let b := s₀.gpr sb
  obtain ⟨hq, -, h2⟩ := hS
  have hK1 := hc.keyRel hp.toKeyCtx hk (e := 1) (by omega)
  simp only [Nat.mul_one] at hK1
  -- The right halves.
  obtain ⟨s₁, e₁, c₁, k₁, -, q₁, h₁, -, -⟩ := lin_step hp.toKeyCtx hc hk (by omega) keyXor8_check (by decide +kernel)
  have hk₁ : AtEntry s₁ b (8 * g) := by rw [AtEntry, k₁]; exact hk
  obtain ⟨s₂, e₂, c₂, k₂, -, q₂, h₂, -, -⟩ := lin_step hp.toKeyCtx c₁ hk₁ (by omega) fromBs_check (by decide +kernel)
  have hk₂ : AtEntry s₂ b (8 * g) := by rw [AtEntry, k₂]; exact hk₁
  have hW1 : WordRel (Qs s₂) (fun b => (S b).1 ^^^ E (8 * g + 1)) :=
    fromBs_rel q₂ (HalfRel.xor_key hq hK1 (keyXor_bits q₁))
  obtain ⟨s₃, e₃, c₃, g₃, w₃, -, sl₃⟩ := storeWords_step hp.toKeyCtx c₂ (Or.inr rfl)
  have hk₃ : AtEntry s₃ b (8 * g) := by rw [AtEntry, g₃]; exact hk₂
  -- The left halves.
  obtain ⟨s₄, e₄, c₄, k₄, -, q₄, -, d₄, -⟩ := lin_step hp.toKeyCtx c₃ hk₃ (by omega) loadHalf2_check (by decide +kernel)
  have hk₄ : AtEntry s₄ b (8 * g) := by rw [AtEntry, k₄]; exact hk₃
  have hD2 : HalfRel (Qs s₄) (fun b => (S b).2) := h2.congr fun j hj =>
    BitVec.eq_of_getLsbD_eq fun p hp => by
      have e₂ := h₂ (8 + j) (by omega)
      have e₁ := h₁ (8 + j) (by omega)
      rw [show d1Slot + (8 + j) = d2Slot + j by simp only [d1Slot, d2Slot]; omega] at e₁ e₂
      rw [q₄ j hj p hp, loadHalfG, xorBits_cons, xorBits_nil,
        Bool.xor_false, bitOf_word _ _ _ hp, bothW_half s₃ (Or.inr rfl) hj,
        sl₃ _ (by simp only [tailSlot_eq, d2Slot]; omega), e₂, e₁]
  obtain ⟨s₅, e₅, c₅, k₅, -, q₅, -, d₅, -⟩ := lin_step hp.toKeyCtx c₄ hk₄ (by omega) keyXor0_check (by decide +kernel)
  have hk₅ : AtEntry s₅ b (8 * g) := by rw [AtEntry, k₅]; exact hk₄
  have hK0' := c₄.keyRel hp.toKeyCtx hk₄ (e := 0) (by omega)
  simp only [Nat.mul_zero, Nat.add_zero] at hK0'
  obtain ⟨s₆, e₆, c₆, -, -, q₆, -, d₆, -⟩ := lin_step hp.toKeyCtx c₅ hk₅ (by omega) fromBs_check (by decide +kernel)
  have hW0 : WordRel (Qs s₆) (fun b => (S b).2 ^^^ E (8 * g)) :=
    fromBs_rel q₆ (HalfRel.xor_key hD2 hK0' (by simpa only [Nat.zero_add] using keyXor_bits q₅))
  obtain ⟨s₇, e₇, c₇, -, w₇, o₇, -⟩ := storeWords_step hp.toKeyCtx c₆ (Or.inl rfl)
  refine ⟨s₇, ?_, c₇, fun b' hb i hi j hj => ?_, fun b' hb i hi j hj => ?_⟩
  · rw [tail, runBlock_append', runBlock_append', runBlock_append', runBlock_append', runBlock_append',
      runBlock_append', e₁, Option.bind_some, e₂, Option.bind_some, e₃, Option.bind_some, e₄,
      Option.bind_some, e₅, Option.bind_some, e₆, Option.bind_some]
    exact e₇
  · show (dataW s₇ (2 * b' + 0)).getLsbD _ = _
    rw [w₇ b' hb]; exact hW0 b' hb i hi j hj
  · have := o₇ b' hb
    simp only [Nat.sub_zero] at this
    show (dataW s₇ (2 * b' + 1)).getLsbD _ = _
    rw [this, d₆ _ (by omega), d₅ _ (by omega), d₄ _ (by omega), w₃ b' hb]
    exact hW1 b' hb i hi j hj

/-! ## The groups -/

/-- The first `i` groups. -/
def groupsN (g : Nat) (E : Nat → BitVec 64) (i : Nat) (d : BitVec 64 × BitVec 64) : BitVec 64 × BitVec 64 :=
  (List.range i).foldl (group g E) d

theorem groupsN_succ (g : Nat) (E : Nat → BitVec 64) (i : Nat) (d : BitVec 64 × BitVec 64) :
    groupsN g E (i + 1) d = group g E (groupsN g E i d) i := by
  simp [groupsN, List.range_succ, List.foldl_append]

theorem groups_wp {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s)
    (hk : AtEntry s (s₀.gpr sb) 2) {S : Nat → BitVec 64 × BitVec 64} (hS : Halves s S) :
    WP isa (.loop groupBody (.nonzero .x t0)) s fun s' => Ctx s₀ s' ∧ AtEntry s' (s₀.gpr sb) (8 * g) ∧
      Halves s' (fun b => groups g E (S b)) := by
  have hg0 : 0 < g := by rcases hp.hg with h | h <;> omega
  let Inv : Nat → State → Prop := fun n s' => ∃ i, n = g - i ∧ i < g ∧ Ctx s₀ s' ∧
    AtEntry s' (s₀.gpr sb) (2 + 8 * i) ∧ Halves s' (fun b => groupsN g E i (S b))
  refine WP.loop (M := isa) Inv (fun n s' hs' => ?_) g s ⟨0, by omega, hg0, hc, hk, by simpa [groupsN] using hS⟩
  obtain ⟨i, rfl, hi, hc', hk', hS'⟩ := hs'
  refine WP.mono (group_wp hp hc' hi hk' hS') fun s'' ⟨c'', S'', k'', z''⟩ => ?_
  simp only [← groupsN_succ] at S''
  by_cases he : i + 1 = g
  · refine .inl ⟨(eval_nonzero s'' t0).trans (by rw [z'']; simp [he]), c'', ?_, ?_⟩
    · simpa only [show ¬ i + 1 < g by omega, ↓reduceIte] using k''
    · have hG : ∀ d, groupsN g E (i + 1) d = groups g E d := fun d => by rw [he]; rfl
      simpa only [hG] using S''
  · refine .inr ⟨(eval_nonzero s'' t0).trans (by rw [z'']; simp [he]), g - (i + 1), by omega, i + 1, rfl,
      by omega, c'', ?_, S''⟩
    simpa only [show i + 1 < g by omega, ↓reduceIte] using k''

/-! ## Eight blocks -/

theorem blk_of_words {s : State} {b : Nat} {hi lo : BitVec 64}
    (h0 : ∀ i < 8, ∀ j < 8, (dataW s (2 * b + 0)).getLsbD (8 * i + j) = (Camellia.byteOf hi i).getLsbD j)
    (h1 : ∀ i < 8, ∀ j < 8, (dataW s (2 * b + 1)).getLsbD (8 * i + j) = (Camellia.byteOf lo i).getLsbD j) :
    blk s b = Spec.Camellia.encodeBlock (hi ++ lo) := by
  apply Vector.ext
  intro i hi16
  rw [Camellia.encodeBlock_getElem _ _ hi16]
  simp only [blk, Spec.Camellia.blockAt, Vector.getElem_ofFn]
  split
  · rename_i h8
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [← h0 i h8 j hj, dataW_byte s 0 h8 hj, show 8 * 0 + i = i by omega]
  · rename_i h8
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [← h1 (i - 8) (by omega) j hj, dataW_byte s 1 (by omega) hj, show 8 * 1 + (i - 8) = i by omega]

/-- `crypt8`: each of the eight blocks in the tail buffer becomes `cryptWords g E` of it. -/
theorem crypt8_ok {s₀ : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) :
    WP isa crypt8 s₀ fun s' => Ctx s₀ s' ∧
      ∀ b < 8, blk s' b = Spec.Camellia.encodeBlock (cryptWords g E (Spec.Camellia.decodeBlock (blk s₀ b))) := by
  obtain ⟨s₁, e₁, c₁, k₁, S₁⟩ := head_ok hp
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  refine WP.seq (WP.mono (groups_wp hp c₁ k₁ S₁) fun s₂ ⟨c₂, k₂, S₂⟩ => ?_)
  obtain ⟨s₃, e₃, c₃, w0, w1⟩ := tail_ok hp c₂ k₂ S₂
  refine WP.of_runBlock ⟨s₃, e₃, c₃, fun b hb => ?_⟩
  rw [cryptWords]
  refine (blk_of_words (fun i hi j hj => w0 b hb i hi j hj) (fun i hi j hj => w1 b hb i hi j hj)).trans ?_
  rfl

end VG.Proof.Camellia.AArch64

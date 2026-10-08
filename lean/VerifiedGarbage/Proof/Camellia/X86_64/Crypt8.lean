import VerifiedGarbage.Proof.Camellia.X86_64.Core

/-!
# The head and tail of eight blocks of bitsliced Camellia on x86-64

`head` loads and bitslices both halves of the eight blocks at `rdx` and
whitens them, and `tail` whitens, transposes and stores them back; between
them the groups of rounds (`group_wp`) run in a loop. `crypt8_ok` composes
them: each block becomes `cryptWords g E` of it.
-/

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Camellia.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR)
open VG.Proof.Camellia (HalfRel WordRel pair group groups cryptWords toBsG fromBsG pos cpos)

theorem ok_data {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s) :
    Ok dataCfg s where
  slotIn k hk := ⟨_, by rw [hc.wr]; exact hp.dat, by
    simp only [dataCfg] at hk ⊢
    rw [hc.rdx]; exact VG.Offset.contains_base _ (by omega) (by omega)⟩
  extIn k hk := by simp [dataCfg] at hk
  slots := by simp [dataCfg]
  sep k _ j hj := by simp [dataCfg] at hj

/-- A frame of the blocks keeps the scratch buffer. -/
theorem slotW_of_data {s₀ s s' : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E)
    (hc : Ctx s₀ s) (hb : s'.gpr sb = s.gpr sb) (hf : Frame [⟨s.gpr .rdx, 128⟩] s.mem s'.mem)
    {k : Nat} (hk : k < slots) : slotW s' k = slotW s k := by
  have hfit := hp.fit
  rw [slots_eq] at hfit hk
  simp only [slotW, wordAddr, hb, hc.base]
  refine hf.readW (r := ⟨s₀.gpr sb + BitVec.ofNat 64 (8 * k), 8⟩) (Region.contains_self _ _)
    (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  rw [hc.rdx]
  refine (hp.sep.sub_right (VG.Offset.sub_base _ ?_)).symm
  rw [slots_eq]; omega

/-- A step that writes the blocks only. -/
theorem Ctx.data {s₀ s s' : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hg : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r)
    (hf : Frame [⟨s.gpr .rdx, 128⟩] s.mem s'.mem) : Ctx s₀ s' := by
  refine hc.step hrd hwr (fun r h1 _ _ => hg r h1) (hf.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [hc.rdx]) fun kv hkv => ?_
  have hlt : kv.1 < slots := by
    simp [layerMasks] at hkv; rcases hkv with h | h | h | h | h <;> subst h <;> rw [slots_eq] <;>
      simp [evenSlot, oddSlot, m4Slot, m2Slot, m3Slot]
  rw [slotW_of_data hp hc (hg _ (by decide)) hf hlt]
  exact hc.masks kv hkv

theorem Halves.xor_key {Q K Q' : Nat → BitVec 64} {d k : Nat → BitVec 64} (hq : HalfRel Q d)
    (hk : HalfRel K k) (h : ∀ j < 8, ∀ p < 64, (Q' j).getLsbD p = ((Q j).getLsbD p ^^ (K j).getLsbD p)) :
    HalfRel Q' (fun b => d b ^^^ k b) := fun b hb c hc j hj => by
  rw [h j hj _ (by omega), hq b hb c hc j hj, hk b hb c hc j hj, Camellia.byteOf_xor,
    BitVec.getLsbD_xor]

/-- Bit `8 i + j` of a little-endian word is bit `j` of its byte `i`. -/
theorem readW64_bit (m : Mem) (a : Addr) {i j : Nat} (hi : i < 8) (hj : j < 8) :
    (m.readW a 64).getLsbD (8 * i + j) = (m (a + BitVec.ofNat 64 i)).getLsbD j := by
  rw [← Mem.extractLsb'_read m a (n := 8) hi, BitVec.getLsbD_extractLsb']
  simp only [Mem.readW, BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and]
  simp only [show 8 * i + j < 64 by omega, decide_true, Bool.true_and]

/-! ## The steps -/

/-- `loadWords h`. -/
theorem loadWords_step {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E)
    (hc : Ctx s₀ s) {h : Nat} (hh : h = 0 ∨ h = 1)
    (hchk : check (lanes 64 10) dataCfg (linExt 0) (loadWords h) dataEnv
      (linPostG 10 (qOuts (loadG h)) [] (dataIns.map (·.1)) dataEnv) = true) :
    ∃ s', runBlock isa (loadWords h) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      s'.gpr .rdi = s.gpr .rdi ∧ (∀ b < 8, Qs s' b = dataW s (2 * b + h)) ∧
      (∀ k < slots, slotW s' k = slotW s k) ∧ (∀ k < 16, dataW s' k = dataW s k) := by
  unfold dataEnv at hchk
  obtain ⟨s', h', ho, -, hkp, rd', wr', o', f', hb', -⟩ := linG_ok hchk (ok_data hp hc) (dataW s)
    (fun r i hri => by simp at hri)
    (fun j i hji => by
      simp only [dataIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hji
      obtain ⟨j, hj, rfl, rfl⟩ := hji
      exact ⟨by simp only [dataCfg]; omega, by omega, rfl⟩)
    (fun kv hkv => by simp at hkv)
    (fun j hj => by simp [dataCfg] at hj)
  simp only [dataCfg] at hb' hkp f'
  have hall : ([Reg.rdx, .rsp, .rsi, .rdi, .r8, .r9].all fun r => (loadWords h).all fun i => i.dst != some r) =
      true := by rcases hh with rfl | rfl <;> decide +kernel
  have hkeep : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r := fun r hr =>
    o' r (List.all_eq_true.mp hall r (not_sboxWrites r hr))
  have hf : Frame [⟨s.gpr .rdx, 128⟩] s.mem s'.mem := by
    simpa only [slotRegion, dataCfg] using f'
  refine ⟨s', h', hc.data hp rd' wr' hkeep hf, hkeep _ (by decide), hkeep _ (by decide), fun b hb => ?_,
    fun k hk => slotW_of_data hp hc (hkeep _ (by decide)) hf hk, fun k hk => ?_⟩
  · refine BitVec.eq_of_getLsbD_eq fun p hp => ?_
    rw [Qs, ho (q b) (loadG h b) (by simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨b, hb, rfl⟩)
      p hp, loadG, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hp]
  · show s'.mem.readW (wordAddr (s'.gpr .rdx) k) 64 = _
    rw [hkeep .rdx (by decide)]
    exact hkp k (by simp only [dataIns, List.map_map, List.mem_map, List.mem_range]; exact ⟨k, hk, rfl⟩)
      hk

theorem mask_lt {kv : Nat × BitVec 64} (hkv : kv ∈ layerMasks) : kv.1 < keySlot := by
  simp [layerMasks] at hkv; rcases hkv with h | h | h | h | h <;> subst h <;>
    simp [keySlot, evenSlot, oddSlot, m4Slot, m2Slot, m3Slot]

/-- A layer on the state registers over `bothEnv`, keeping the masks and both halves. -/
theorem lin_step {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm34 : m + 2 ≤ 34) {is : List Instr} {G : Nat → Nat → List Nat}
    (hchk : check (lanes 64 12) layerCfg (linExt 24) is bothEnv
      (linPostG 12 (qOuts G) [] (maskSlots ++ bothIns.map (·.1)) bothEnv) = true)
    (hall : ([Reg.rdx, .rsp, .rsi, .rdi, .r8, .r9].all fun r => is.all fun i => i.dst != some r) = true) :
    ∃ s', runBlock isa is s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      s'.gpr .rdi = s.gpr .rdi ∧ (∀ j < 8, ∀ p < 64, (Qs s' j).getLsbD p = xorBits (bothW s) (G j p)) ∧
      (∀ j < 16, slotW s' (d1Slot + j) = slotW s (d1Slot + j)) ∧ (∀ k < 16, dataW s' k = dataW s k) := by
  obtain ⟨s', h', ho, -, hkp, rd', wr', o', f'⟩ := both_ok hp hc hk hm34 hchk
  have hkeep : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r := fun r hr =>
    o' r (List.all_eq_true.mp hall r (not_sboxWrites r hr))
  refine ⟨s', h', hc.step rd' wr' (fun r hr _ _ => hkeep r hr) (f'.mono fun r hr => by simp at hr; simp [hr])
    (fun kv hkv => ?_), hkeep _ (by decide), hkeep _ (by decide),
    fun j hj p hp => ho (q j) (G j) (by simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩) p hp,
    fun j hj => hkp _ (List.mem_append_right _ (by
      simp only [bothIns, List.map_map, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩))
      (by simp only [d1Slot, keySlot]; omega),
    fun k hk => dataW_of_scr hp hc (hkeep _ (by decide)) f' hk⟩
  rw [hkp kv.1 (List.mem_append_left _ (List.mem_map_of_mem hkv)) (mask_lt hkv)]
  exact hc.masks kv hkv

/-- `storeWords h`. -/
theorem storeWords_step {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E)
    (hc : Ctx s₀ s) {h : Nat} (hh : h = 0 ∨ h = 1)
    (hchk : check (lanes 64 11) dataCfg (linExt 0) (storeWords h) storeEnv
      (linPostG 11 [] (storeOuts h) (otherWords h) storeEnv) = true) :
    ∃ s', runBlock isa (storeWords h) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr = s.gpr ∧
      (∀ b < 8, dataW s' (2 * b + h) = Qs s b) ∧ (∀ b < 8, dataW s' (2 * b + (1 - h)) = dataW s (2 * b + (1 - h))) ∧
      (∀ k < slots, slotW s' k = slotW s k) := by
  unfold storeEnv at hchk
  let W : Nat → BitVec 64 := fun i => if i < 8 then Qs s i else dataW s (i - 8)
  obtain ⟨s', h', -, hso, hkp, rd', wr', o', f', hb', -⟩ := linG_ok hchk (ok_data hp hc) W
    (fun r i hri => by
      simp only [qIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hri
      obtain ⟨i, hi, rfl, rfl⟩ := hri
      exact ⟨by omega, by simp [W, hi]⟩)
    (fun j i hji => by
      simp only [storeIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hji
      obtain ⟨j, hj, rfl, rfl⟩ := hji
      exact ⟨by simp only [dataCfg]; omega, by omega, by simp only [W, show ¬ 8 + j < 8 by omega, ↓reduceIte, show 8 + j - 8 = j by omega]; rfl⟩)
    (fun kv hkv => by simp at hkv)
    (fun j hj => by simp [dataCfg] at hj)
  simp only [dataCfg] at hb' hkp hso f'
  have hall : ∀ r, ((storeWords h).all fun i => i.dst != some r) = true := fun r => by
    rcases hh with rfl | rfl <;> simp [storeWords, Instr.dst]
  have hg : s'.gpr = s.gpr := funext fun r => o' r (hall r)
  have hf : Frame [⟨s.gpr .rdx, 128⟩] s.mem s'.mem := by
    simpa only [slotRegion, dataCfg] using f'
  refine ⟨s', h', hc.data hp rd' wr' (fun r _ => by rw [hg]) hf, hg, fun b hb => ?_, fun b hb => ?_,
    fun k hk => slotW_of_data hp hc (by rw [hg]) hf hk⟩
  · refine BitVec.eq_of_getLsbD_eq fun p hp => ?_
    show (s'.mem.readW (wordAddr (s'.gpr .rdx) _) 64).getLsbD p = _
    rw [hg, hso (2 * b + h) (idG b) (by simp only [storeOuts, List.mem_map, List.mem_range]; exact ⟨b, hb, rfl⟩)
      (by omega) p hp, idG, xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hp]
    simp [W, hb]
  · show s'.mem.readW (wordAddr (s'.gpr .rdx) _) 64 = _
    rw [hg]
    exact hkp _ (by simp only [otherWords, List.mem_map, List.mem_range]; exact ⟨b, hb, rfl⟩) (by omega)

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

/-- Block `b` at `rdx`. -/
abbrev blk (s : State) (b : Nat) : Spec.Camellia.Block :=
  Spec.Camellia.blockAt s.mem (s.gpr .rdx + BitVec.ofNat 64 (16 * b))

theorem dataW_byte (s : State) {b i j : Nat} (h : Nat) (hi : i < 8) (hj : j < 8) :
    (dataW s (2 * b + h)).getLsbD (8 * i + j) =
      (s.mem (s.gpr .rdx + BitVec.ofNat 64 (16 * b) + BitVec.ofNat 64 (8 * h + i))).getLsbD j := by
  rw [readW64_bit _ _ hi hj, wordAddr, addr_add, addr_add,
    show 8 * (2 * b + h) + i = 16 * b + (8 * h + i) by omega]

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

/-- `mov kp, sb; add kp, 8 keySlot`. -/
theorem setKp_ok (s : State) :
    ∃ s', runBlock isa [movR kp sb, .alu .add kp (.imm (BitVec.ofNat 32 (8 * keySlot)))] s = some s' ∧
      s'.gpr kp = s.gpr sb + BitVec.ofNat 64 (8 * keySlot) ∧ (∀ r, r ≠ kp → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [movR, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some, Option.map_some]; rfl, ?_, fun r hr => ?_, by rfl, by rfl, by rfl⟩
  · simp only [RegUpd.gpr_setReg_self]; rfl
  · simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

/-- The whitening. -/
theorem whiten_step {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s)
    {m : Nat} (hk : AtEntry s (s₀.gpr sb) m) (hm34 : m + 2 ≤ 34) :
    ∃ s', runBlock isa whiten s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      (∀ j < 8, ∀ p < 64, (Qs s' j).getLsbD p = ((Qs s j).getLsbD p ^^ (keyW s j).getLsbD p)) ∧
      (∀ j < 8, ∀ p < 64, (slotW s' (d1Slot + j)).getLsbD p = ((Qs s j).getLsbD p ^^ (keyW s j).getLsbD p)) ∧
      (∀ j < 8, ∀ p < 64, (slotW s' (d2Slot + j)).getLsbD p =
        ((slotW s (d2Slot + j)).getLsbD p ^^ (keyW s (8 + j)).getLsbD p)) := by
  obtain ⟨s', h', ho, hso, hkp, rd', wr', o', f'⟩ := both_ok hp hc hk hm34 whiten_check
  have hall : ([Reg.rdx, .rsp, .rsi, .rdi, .r8, .r9].all fun r => whiten.all fun i => i.dst != some r) =
      true := by decide +kernel
  have hkeep : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r := fun r hr =>
    o' r (List.all_eq_true.mp hall r (not_sboxWrites r hr))
  refine ⟨s', h', hc.step rd' wr' (fun r hr _ _ => hkeep r hr) (f'.mono fun r hr => by simp at hr; simp [hr])
    (fun kv hkv => ?_), hkeep _ (by decide), fun j hj p hp => ?_, fun j hj p hp => ?_, fun j hj p hp => ?_⟩
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

end VG.Proof.Camellia.X86_64

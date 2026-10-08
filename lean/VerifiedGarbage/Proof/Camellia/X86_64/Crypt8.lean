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

theorem ok_data {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s) :
    Ok dataCfg s where
  slotIn k hk := by
    simp only [dataCfg] at hk ⊢
    rw [hc.rdx, hc.wr]; exact hp.dat k hk
  extIn k hk := by simp [dataCfg] at hk
  slots := by simp [dataCfg]
  sep k _ j hj := by simp [dataCfg] at hj

/-- A frame of the blocks keeps the scratch buffer. -/
theorem slotW_of_data {s₀ s s' : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E)
    (hc : Ctx s₀ s) (hb : s'.gpr sb = s.gpr sb) (hf : Frame [⟨s.gpr .rdx, 128⟩] s.mem s'.mem)
    {k : Nat} (hk : k < tailSlot) : slotW s' k = slotW s k := by
  have hfit := hp.fit
  rw [slots_eq] at hfit
  rw [tailSlot_eq] at hk
  simp only [slotW, wordAddr, hb, hc.base]
  refine hf.readW (r := ⟨s₀.gpr sb + BitVec.ofNat 64 (8 * k), 8⟩) (Region.contains_self _ _)
    (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  rw [hc.rdx]
  refine (hp.sep.sub_right (VG.Offset.sub_base _ ?_)).symm
  rw [tailSlot_eq]; omega

/-- A step that writes the blocks only. -/
theorem Ctx.data {s₀ s s' : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hg : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r)
    (hf : Frame [⟨s.gpr .rdx, 128⟩] s.mem s'.mem) : Ctx s₀ s' := by
  refine hc.step hrd hwr (fun r h1 _ _ => hg r h1) (hf.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [hc.rdx]) fun kv hkv => ?_
  have hlt : kv.1 < tailSlot := by
    simp [layerMasks] at hkv; rcases hkv with h | h | h | h | h <;> subst h <;> rw [tailSlot_eq] <;>
      simp [evenSlot, oddSlot, m4Slot, m2Slot, m3Slot]
  rw [slotW_of_data hp hc (hg _ (by decide)) hf hlt]
  exact hc.masks kv hkv

/-! ## The steps -/

/-- `loadWords h`. -/
theorem loadWords_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E)
    (hc : Ctx s₀ s) {h : Nat} (hh : h = 0 ∨ h = 1)
    (hchk : check (lanes 64 10) dataCfg (linExt 0) (loadWords h) dataEnv
      (linPostG 10 (qOuts (loadG h)) [] (dataIns.map (·.1)) dataEnv) = true) :
    ∃ s', runBlock isa (loadWords h) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      s'.gpr .rdi = s.gpr .rdi ∧ (∀ b < 8, Qs s' b = dataW s (2 * b + h)) ∧
      (∀ k < tailSlot, slotW s' k = slotW s k) ∧ (∀ k < 16, dataW s' k = dataW s k) := by
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
theorem lin_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
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
theorem storeWords_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E)
    (hc : Ctx s₀ s) {h : Nat} (hh : h = 0 ∨ h = 1)
    (hchk : check (lanes 64 11) dataCfg (linExt 0) (storeWords h) storeEnv
      (linPostG 11 [] (storeOuts h) (otherWords h) storeEnv) = true) :
    ∃ s', runBlock isa (storeWords h) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr = s.gpr ∧
      (∀ b < 8, dataW s' (2 * b + h) = Qs s b) ∧ (∀ b < 8, dataW s' (2 * b + (1 - h)) = dataW s (2 * b + (1 - h))) ∧
      (∀ k < tailSlot, slotW s' k = slotW s k) := by
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
theorem whiten_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
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
  have hc₁ : Ctx s₀ s₁ := hc₀.step rd₁ wr₁ (fun r _ h2 _ => o₁ r h2) (by rw [m₁]; exact Frame.refl _ _)
    (fun kv hkv => by simp only [slotW, m₁, o₁ sb (by decide)]; exact hp.masks kv hkv)
  have hk₁ : AtEntry s₁ b 0 := by rw [AtEntry, k₁, Nat.mul_zero, Nat.add_zero]
  have hd₁ : ∀ k, dataW s₁ k = dataW s₀ k := fun k => by
    show s₁.mem.readW (wordAddr (s₁.gpr .rdx) k) 64 = _
    rw [m₁, o₁ .rdx (by decide)]
  -- `D2`.
  obtain ⟨s₂, e₂, c₂, k₂, -, q₂, -, d₂⟩ := loadWords_step hp.toKeyCtx hc₁ (Or.inr rfl) loadWords1_check
  have hk₂ : AtEntry s₂ b 0 := by rw [AtEntry, k₂]; exact hk₁
  obtain ⟨s₃, e₃, c₃, k₃, -, q₃, -, d₃⟩ := lin_step hp.toKeyCtx c₂ hk₂ (by omega) toBs_check (by decide +kernel)
  have hk₃ : AtEntry s₃ b 0 := by rw [AtEntry, k₃]; exact hk₂
  have hD2 : HalfRel (Qs s₃) (fun b => (Spec.Camellia.decodeBlock (blk s₀ b)).setWidth 64) :=
    toBs_rel q₃ fun b' hb i hi j hj => by rw [q₂ b' hb, hd₁]; exact data_lo s₀ b' hb i hi j hj
  obtain ⟨s₄, e₄, c₄, k₄, -, -, sl₄, hh₄, d₄⟩ :=
    storeHalf_step hp.toKeyCtx c₃ (Or.inr rfl) storeHalf2_check hk₃ (by omega)
  have hk₄ : AtEntry s₄ b 0 := by rw [AtEntry, k₄]; exact hk₃
  -- `D1`.
  obtain ⟨s₅, e₅, c₅, k₅, -, q₅, sw₅, -⟩ := loadWords_step hp.toKeyCtx c₄ (Or.inl rfl) loadWords0_check
  have hk₅ : AtEntry s₅ b 0 := by rw [AtEntry, k₅]; exact hk₄
  obtain ⟨s₆, e₆, c₆, k₆, -, q₆, h₆, -⟩ := lin_step hp.toKeyCtx c₅ hk₅ (by omega) toBs_check (by decide +kernel)
  have hk₆ : AtEntry s₆ b 0 := by rw [AtEntry, k₆]; exact hk₅
  have hD1 : HalfRel (Qs s₆) (fun b => (Spec.Camellia.decodeBlock (blk s₀ b) >>> 64).setWidth 64) :=
    toBs_rel q₆ fun b' hb i hi j hj => by
      rw [q₅ b' hb, d₄ _ (by omega), d₃ _ (by omega), d₂ _ (by omega), hd₁]
      exact data_hi s₀ b' hb i hi j hj
  have hS₆ : HalfRel (fun j => slotW s₆ (d2Slot + j)) (fun b => (Spec.Camellia.decodeBlock (blk s₀ b)).setWidth 64) :=
    hD2.congr fun j hj => by
      have h1 := h₆ (8 + j) (by omega)
      rw [show d1Slot + (8 + j) = d2Slot + j by simp only [d1Slot, d2Slot]; omega] at h1
      rw [h1, sw₅ _ (by simp only [tailSlot_eq, d2Slot]; omega), sl₄ j hj]
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
  obtain ⟨s₁, e₁, c₁, k₁, -, q₁, h₁, -⟩ := lin_step hp.toKeyCtx hc hk (by omega) keyXor8_check (by decide +kernel)
  have hk₁ : AtEntry s₁ b (8 * g) := by rw [AtEntry, k₁]; exact hk
  obtain ⟨s₂, e₂, c₂, k₂, -, q₂, h₂, -⟩ := lin_step hp.toKeyCtx c₁ hk₁ (by omega) fromBs_check (by decide +kernel)
  have hk₂ : AtEntry s₂ b (8 * g) := by rw [AtEntry, k₂]; exact hk₁
  have hW1 : WordRel (Qs s₂) (fun b => (S b).1 ^^^ E (8 * g + 1)) :=
    fromBs_rel q₂ (HalfRel.xor_key hq hK1 (keyXor_bits q₁))
  obtain ⟨s₃, e₃, c₃, g₃, w₃, -, sl₃⟩ := storeWords_step hp.toKeyCtx c₂ (Or.inr rfl) storeWords1_check
  have hk₃ : AtEntry s₃ b (8 * g) := by rw [AtEntry, g₃]; exact hk₂
  -- The left halves.
  obtain ⟨s₄, e₄, c₄, k₄, -, q₄, -, d₄⟩ := lin_step hp.toKeyCtx c₃ hk₃ (by omega) loadHalf2_check (by decide +kernel)
  have hk₄ : AtEntry s₄ b (8 * g) := by rw [AtEntry, k₄]; exact hk₃
  have hD2 : HalfRel (Qs s₄) (fun b => (S b).2) := h2.congr fun j hj =>
    BitVec.eq_of_getLsbD_eq fun p hp => by
      have e₂ := h₂ (8 + j) (by omega)
      have e₁ := h₁ (8 + j) (by omega)
      rw [show d1Slot + (8 + j) = d2Slot + j by simp only [d1Slot, d2Slot]; omega] at e₁ e₂
      rw [q₄ j hj p hp, loadHalfG, xorBits_cons, xorBits_nil,
        Bool.xor_false, bitOf_word _ _ _ hp, bothW_half s₃ (Or.inr rfl) hj,
        sl₃ _ (by simp only [tailSlot_eq, d2Slot]; omega), e₂, e₁]
  obtain ⟨s₅, e₅, c₅, k₅, -, q₅, -, d₅⟩ := lin_step hp.toKeyCtx c₄ hk₄ (by omega) keyXor0_check (by decide +kernel)
  have hk₅ : AtEntry s₅ b (8 * g) := by rw [AtEntry, k₅]; exact hk₄
  have hK0' := c₄.keyRel hp.toKeyCtx hk₄ (e := 0) (by omega)
  simp only [Nat.mul_zero, Nat.add_zero] at hK0'
  obtain ⟨s₆, e₆, c₆, -, -, q₆, -, d₆⟩ := lin_step hp.toKeyCtx c₅ hk₅ (by omega) fromBs_check (by decide +kernel)
  have hW0 : WordRel (Qs s₆) (fun b => (S b).2 ^^^ E (8 * g)) :=
    fromBs_rel q₆ (HalfRel.xor_key hD2 hK0' (by simpa only [Nat.zero_add] using keyXor_bits q₅))
  obtain ⟨s₇, e₇, c₇, -, w₇, o₇, -⟩ := storeWords_step hp.toKeyCtx c₆ (Or.inl rfl) storeWords0_check
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

theorem groups_wp {s₀ s : State} {g : Nat} {E : Nat → BitVec 64} (hp : CorePre s₀ g E) (hc : Ctx s₀ s)
    (hk : AtEntry s (s₀.gpr sb) 2) {S : Nat → BitVec 64 × BitVec 64} (hS : Halves s S) :
    WP isa (.loop groupBody .ne) s fun s' => Ctx s₀ s' ∧ AtEntry s' (s₀.gpr sb) (8 * g) ∧
      Halves s' (fun b => groups g E (S b)) := by
  have hg0 : 0 < g := by rcases hp.hg with h | h <;> omega
  let Inv : Nat → State → Prop := fun n s' => ∃ i, n = g - i ∧ i < g ∧ Ctx s₀ s' ∧
    AtEntry s' (s₀.gpr sb) (2 + 8 * i) ∧ Halves s' (fun b => groupsN g E i (S b))
  refine WP.loop (M := isa) Inv (fun n s' hs' => ?_) g s ⟨0, by omega, hg0, hc, hk, by simpa [groupsN] using hS⟩
  obtain ⟨i, rfl, hi, hc', hk', hS'⟩ := hs'
  refine WP.mono (group_wp hp hc' hi hk' hS') fun s'' ⟨c'', S'', k'', z''⟩ => ?_
  simp only [← groupsN_succ] at S''
  by_cases he : i + 1 = g
  · refine .inl ⟨by simp [X86_64.eval, z'', he], c'', ?_, ?_⟩
    · simpa only [show ¬ i + 1 < g by omega, ↓reduceIte] using k''
    · have hG : ∀ d, groupsN g E (i + 1) d = groups g E d := fun d => by rw [he]; rfl
      simpa only [hG] using S''
  · refine .inr ⟨by simp [X86_64.eval, z'', he], g - (i + 1), by omega, i + 1, rfl, by omega, c'', ?_, S''⟩
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

/-- `crypt8`: each of the eight blocks at `rdx` becomes `cryptWords g E` of it. -/
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

end VG.Proof.Camellia.X86_64

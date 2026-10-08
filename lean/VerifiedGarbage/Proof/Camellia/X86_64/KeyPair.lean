import VerifiedGarbage.Proof.Camellia.X86_64.KeyStore
import VerifiedGarbage.Proof.Camellia.X86_64.KeyChecks2

/-!
# A pair of rounds of the key schedule on x86-64

`pairPlain_ok`: with the running value's halves as words at `rdi` (`wSlot`)
and `kp` at entry `m` of a table of the subkeys `E`, `pairPlain` leaves
`pair (E m) (E (m + 1))` of them there, and `kp` at entry `m + 2`. The
rounds are ECB's (`round_step`), on eight copies of the value.
-/

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Camellia.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR movS st at_)
open VG.Proof.Camellia (HalfRel WordRel pair)

/-- `spread d`: the half at `[rdi + d]`, a word of `wSlot`, in every lane. -/
theorem spread_step {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {d : Nat} (hd : d = 0 ∨ d = 8) (hrdi : s.gpr .rdi = s₀.gpr sb + BitVec.ofNat 64 (8 * wSlot))
    {H : BitVec 64} (hw : WordOf (slotW s (wSlot + d / 8)) H) :
    ∃ s', runBlock isa (spread d) s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kp = s.gpr kp ∧
      s'.gpr .rdi = s.gpr .rdi ∧ HalfRel (Qs s') (fun _ => H) ∧
      (∀ j < 16, slotW s' (d1Slot + j) = slotW s (d1Slot + j)) := by
  have hfit := hp.fit
  rw [slots_eq] at hfit
  have hb := hc.base
  have hscr : (⟨s.gpr sb, 8 * slots⟩ : Region) ∈ s.wr := by rw [hc.wr, hb]; exact hp.scr
  have hwS : wSlot = 381 := rfl
  have hrw : ∀ k, wordAddr (s.gpr .rdi) k = wordAddr (s.gpr sb) (wSlot + k) := fun k => by
    rw [hrdi, hb, wordAddr, wordAddr, addr_add, Nat.mul_add]
  have hok : Ok (keyCfg 2) s :=
    { slotIn := fun k hk => ⟨_, hscr, by
        simp only [keyCfg, keySlot_eq] at hk ⊢
        exact VG.Offset.contains_base _ (by rw [slots_eq]; omega) (by omega)⟩
      extIn := fun k hk => ⟨_, List.mem_append_right _ hscr, by
        simp only [keyCfg] at hk ⊢
        rw [hrw]; exact VG.Offset.contains_base _ (by rw [slots_eq]; omega) (by omega)⟩
      slots := by simp [keyCfg, keySlot_eq]
      sep := fun k hk j hj => by
        simp only [keyCfg, keySlot_eq] at hk hj ⊢
        rw [hrw]; exact slot_sep _ (by omega) (by omega) (by omega) }
  have hchk : check (lanes 64 11) (keyCfg 2) (linExt 0) (spread d) kaEnv
      (linPostG 11 (qOuts (keyBsG d)) [] (maskSlots ++ kaIns.map (·.1)) kaEnv) = true := by
    rcases hd with rfl | rfl
    · exact spread0_check
    · exact spread8_check
  unfold kaEnv at hchk
  let W : Nat → BitVec 64 := fun k =>
    if k < 2 then s.mem.readW (wordAddr (s.gpr .rdi) k) 64 else slotW s (d1Slot + (k - 2))
  obtain ⟨s', h', ho, -, hkp, rd', wr', o', f', hb', -⟩ := linG_ok hchk hok W
    (fun r i hri => by simp at hri)
    (fun j i hji => by
      simp only [kaIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hji
      obtain ⟨j, hj, rfl, rfl⟩ := hji
      refine ⟨by simp only [keyCfg, d1Slot, keySlot]; omega, by omega, ?_⟩
      simp only [W, show ¬ 2 + j < 2 by omega, ↓reduceIte, show 2 + j - 2 = j by omega]; rfl)
    (fun kv hkv => ⟨by simp only [keyCfg]; exact mask_lt hkv, by simp only [keyCfg]; exact hc.masks kv hkv⟩)
    (fun j hj => ⟨by simp only [keyCfg] at hj; omega, by
      simp only [keyCfg] at hj ⊢; simp only [W, Nat.zero_add, hj, ↓reduceIte]⟩)
  simp only [keyCfg] at hb' hkp f'
  have hall : ∀ r, r ∉ sboxWrites → ((spread d).all fun i => i.dst != some r) = true := fun r hr => by
    have h := not_sboxWrites r hr
    have : ([Reg.rdx, .rsp, .rsi, .rdi, .r8, .r9].all fun r => (spread d).all fun i => i.dst != some r) =
        true := by rcases hd with rfl | rfl <;> decide +kernel
    exact List.all_eq_true.mp this r h
  have hkeep : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r := fun r hr => o' r (hall r hr)
  refine ⟨s', h', hc.step rd' wr' (fun r hr _ _ => hkeep r hr) (f'.mono fun r hr => by
      simp only [slotRegion, List.mem_singleton] at hr; subst hr; simp [hb])
    (fun kv hkv => ?_), hkeep _ (by decide), hkeep _ (by decide), ?_, fun j hj => ?_⟩
  · show s'.mem.readW (wordAddr (s'.gpr sb) kv.1) 64 = kv.2
    rw [hb', hkp kv.1 (List.mem_append_left _ (List.mem_map_of_mem hkv)) (mask_lt hkv)]
    exact hc.masks kv hkv
  · refine Camellia.half_of_words (W := fun _ => slotW s (wSlot + d / 8)) (fun j hj p hp => ?_)
      (wordOf_iff_rel.mp hw)
    have := Camellia.pos_lt (show p / 8 < 8 by omega)
    rw [Qs, ho (q j) (keyBsG d j) (by simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
      p hp, keyBsG, xorBits_cons, xorBits_nil, Bool.xor_false, Nat.add_assoc, bitOf_word _ _ _ (by omega)]
    simp only [W, show d / 8 < 2 by omega, ↓reduceIte, hrw]
  · show s'.mem.readW (wordAddr (s'.gpr sb) _) 64 = _
    rw [hb']
    exact hkp _ (List.mem_append_right _ (by
      simp only [kaIns, List.map_map, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩))
      (by simp only [d1Slot, keySlot]; omega)

/-! ## Slots of the key schedule -/

/-- A slot at or above the table, which `Ctx` keeps when the blocks are apart from the scratch buffer. -/
theorem Ctx.slotHi {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    (hsx : Region.Disjoint ⟨s₀.gpr .rdx, 128⟩ ⟨s₀.gpr sb, 8 * slots⟩) {k : Nat} (hk1 : keySlot ≤ k)
    (hk2 : k < slots) : slotW s k = slotW s₀ k := by
  have hfit := hp.fit
  rw [slots_eq] at hfit hk2
  rw [keySlot_eq] at hk1
  simp only [slotW, hc.base, wordAddr]
  refine hc.frame.readW (r := ⟨s₀.gpr sb + BitVec.ofNat 64 (8 * k), 8⟩) (Region.contains_self _ _)
    (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact VG.Offset.disjoint_base _ (by rw [keySlot_eq]; omega) (by omega)
  · exact (hsx.sub_right (VG.Offset.sub_base _ (by rw [slots_eq]; omega))).symm

/-- `KeyCtx` moves to a state with the same base, blocks, regions, masks and table. -/
theorem KeyCtx.transfer {s₀ s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E)
    (hsb : s.gpr sb = s₀.gpr sb) (hdx : s.gpr .rdx = s₀.gpr .rdx) (hwr : s.wr = s₀.wr) (hm : MasksOk s)
    (he : ∀ i < nk, ∀ j < 8, entryW s.mem (s₀.gpr sb) i j = entryW s₀.mem (s₀.gpr sb) i j) :
    KeyCtx s nk E where
  scr := by rw [hwr, hsb]; exact hp.scr
  dat := by rw [hwr, hdx]; exact hp.dat
  sep := by rw [hsb, hdx]; exact hp.sep
  fit := by rw [hsb]; exact hp.fit
  fitD := by rw [hdx]; exact hp.fitD
  nk34 := hp.nk34
  masks := hm
  keys i hi := by rw [hsb]; exact (hp.keys i hi).congr fun j hj => he i hi j hj

/-- A store above the table keeps its entries. -/
theorem entryW_write {m : Mem} {b : Addr} {k : Nat} (v : BitVec 64) (hk : endSlot ≤ k) (hk2 : k < slots)
    {i j : Nat} (hi : i < 34) (hj : j < 8) :
    entryW (m.writeW (wordAddr b k) v) b i j = entryW m b i j := by
  have he : ∀ m : Mem, entryW m b i j = m.readW (wordAddr b (keySlot + 8 * i + j)) 64 := fun m => by
    rw [entryW, wordAddr, show 8 * keySlot + 64 * i + 8 * j = 8 * (keySlot + 8 * i + j) by omega]
  rw [he, he, readW_slot_write v (by rw [slots_eq, keySlot_eq]; omega) hk2,
    ite_eq_right (show ¬ keySlot + 8 * i + j = k by rw [endSlot_eq] at hk; rw [keySlot_eq]; omega)]

/-- The slots after a store to slot `k`. -/
theorem slotW_store {s s' : State} {k : Nat} {v : BitVec 64}
    (hm : s'.mem = s.mem.writeW (wordAddr (s.gpr sb) k) v) (hg : s'.gpr = s.gpr) {j : Nat} (hj : j < slots)
    (hk : k < slots) : slotW s' j = if j = k then v else slotW s j := by
  simp only [slotW, hm, hg]; exact readW_slot_write v hj hk

/-- A store above the table keeps the masks and `KeyCtx`. -/
theorem KeyCtx.store {s₀ s s' : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s₀ nk E) (hc : Ctx s₀ s)
    {k : Nat} {v : BitVec 64} (hm : s'.mem = s.mem.writeW (wordAddr (s.gpr sb) k) v) (hg : s'.gpr = s.gpr)
    (hwr : s'.wr = s.wr) (hk : endSlot ≤ k) (hk2 : k < slots) : KeyCtx s' nk E := by
  have h34 := hp.nk34
  refine (hp.transfer (s := s) hc.base hc.rdx hc.wr hc.masks
    (fun i hi j hj => hc.entry hp (by omega) hj)).transfer (by rw [hg]) (by rw [hg]) hwr (fun kv hkv => ?_)
    (fun i hi j hj => by rw [hm]; exact entryW_write v hk hk2 (by omega) hj)
  have := mask_lt hkv
  rw [slotW_store hm hg (by rw [slots_eq]; rw [keySlot_eq] at this; omega) hk2,
    ite_eq_right (show ¬ kv.1 = k by rw [endSlot_eq] at hk; rw [keySlot_eq] at this; omega)]
  exact hc.masks kv hkv

/-! ## A pair of rounds -/

theorem pairPlain_ok {s : State} {nk : Nat} {E : Nat → BitVec 64} (hp : KeyCtx s nk E)
    (hsx : Region.Disjoint ⟨s.gpr .rdx, 128⟩ ⟨s.gpr sb, 8 * slots⟩)
    {m : Nat} (hk : AtEntry s (s.gpr sb) m) (hm : m + 1 < nk)
    (hrdi : s.gpr .rdi = s.gpr sb + BitVec.ofNat 64 (8 * wSlot))
    {H1 H2 : BitVec 64} (hw1 : WordOf (slotW s wSlot) H1) (hw2 : WordOf (slotW s (wSlot + 1)) H2) :
    ∃ s', runBlock isa pairPlain s = some s' ∧ KeyCtx s' nk E ∧ AtEntry s' (s.gpr sb) (m + 2) ∧
      (∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .rdi → s'.gpr r = s.gpr r) ∧ s'.gpr .rdi = s.gpr .rdi ∧
      WordOf (slotW s' wSlot) (pair (E m) (E (m + 1)) (H1, H2)).1 ∧
      WordOf (slotW s' (wSlot + 1)) (pair (E m) (E (m + 1)) (H1, H2)).2 ∧
      (∀ k, keySlot ≤ k → k < slots → k ≠ wSlot → k ≠ wSlot + 1 → slotW s' k = slotW s k) ∧
      Frame [⟨s.gpr sb, 8 * slots⟩, ⟨s.gpr .rdx, 128⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hm34 : m + 2 ≤ 34 := by have := hp.nk34; omega
  have hfit := hp.fit
  rw [slots_eq] at hfit
  have hwS : wSlot = 381 := rfl
  -- The value, bitsliced: `D2` from the second word, `D1` from the first.
  obtain ⟨s₁, e₁, c₁, kp₁, di₁, q₁, -⟩ := spread_step hp (Ctx.refl hp.masks) (d := 8) (Or.inr rfl) hrdi hw2
  have hk₁ : AtEntry s₁ (s.gpr sb) m := by rw [AtEntry, kp₁]; exact hk
  obtain ⟨s₂, e₂, c₂, kp₂, di₂, -, h₂, -, -⟩ := storeHalf_step hp c₁ (Or.inr rfl) storeHalf2_check hk₁ hm34
  have hk₂ : AtEntry s₂ (s.gpr sb) m := by rw [AtEntry, kp₂]; exact hk₁
  have hD2 : HalfRel (fun j => slotW s₂ (d2Slot + j)) (fun _ => H2) := q₁.congr fun j hj => h₂ j hj
  obtain ⟨s₃, e₃, c₃, kp₃, di₃, q₃, o₃⟩ := spread_step hp c₂ (d := 0) (Or.inl rfl)
    (by rw [di₂, di₁, hrdi]) (hw1.congr (c₂.slotHi hp hsx (by decide) (by decide)))
  have hk₃ : AtEntry s₃ (s.gpr sb) m := by rw [AtEntry, kp₃]; exact hk₂
  obtain ⟨s₄, e₄, c₄, kp₄, di₄, q₄, h₄, o₄, -⟩ := storeHalf_step hp c₃ (Or.inl rfl) storeHalf1_check hk₃ hm34
  have hk₄ : AtEntry s₄ (s.gpr sb) m := by rw [AtEntry, kp₄]; exact hk₃
  have hd2 : ∀ j < 8, slotW s₄ (d2Slot + j) = slotW s₂ (d2Slot + j) := fun j hj => by
    have a := o₄ (8 + j) (by omega) (Or.inr (by simp only [d1Slot]; omega))
    have b := o₃ (8 + j) (by omega)
    rw [show d1Slot + (8 + j) = d2Slot + j by simp only [d1Slot, d2Slot]; omega] at a b
    rw [a, b]
  -- The two rounds.
  obtain ⟨s₅, e₅, c₅, k₅, r₅, q₅, d₅, o₅⟩ := round_step hp c₄ (off := 0) (d := d2Slot) keyIn0_check
    feistel2_check (by decide) (by decide) hk₄ (by omega) hm34 (q₃.congr q₄) (hD2.congr hd2)
  have h1' : HalfRel (fun j => slotW s₅ (d1Slot + j)) (fun _ => H1) :=
    (q₃.congr fun j hj => h₄ j hj).congr fun j hj => o₅ j (by omega) (Or.inl (by simp [d1Slot, d2Slot]; omega))
  obtain ⟨s₆, e₆, c₆, k₆, r₆, q₆, d₆, o₆⟩ := round_step hp c₅ (off := 8) (d := d1Slot) keyIn8_check
    feistel1_check (by decide) (by decide) (by rw [AtEntry, k₅]; exact hk₄) (by omega) hm34 q₅ h1'
  have hk₆ : AtEntry s₆ (s.gpr sb) m := by rw [AtEntry, k₆, k₅]; exact hk₄
  have d₅' : HalfRel (fun j => slotW s₆ (d2Slot + j)) (fun _ => (pair (E m) (E (m + 1)) (H1, H2)).2) :=
    d₅.congr fun j hj => by
      have := o₆ (8 + j) (by omega) (Or.inr (by simp only [d1Slot]; omega))
      rw [show d1Slot + (8 + j) = d2Slot + j by simp [d1Slot, d2Slot]; omega] at this
      exact this
  -- The first word.
  obtain ⟨s₇, e₇, c₇, kp₇, di₇, q₇, d₇, -⟩ := lin_step hp c₆ hk₆ hm34 fromBs_check (by decide +kernel)
  have hW1 : WordRel (Qs s₇) (fun _ => (pair (E m) (E (m + 1)) (H1, H2)).1) := fromBs_rel q₇ q₆
  have hin : ∀ {t : State} k, k < slots → t.wr = s.wr → InRegions t.wr (wordAddr (s.gpr sb) k) 8 :=
    fun k hk hw => ⟨_, by rw [hw]; exact hp.scr, by
      rw [wordAddr]; rw [slots_eq] at hk; exact VG.Offset.contains_base _ (by rw [slots_eq]; omega) (by omega)⟩
  obtain ⟨s₈, e₈, m₈, g₈, rd₈, wr₈⟩ := stReg_ok (k := wSlot) (q 0) c₇.base (hin _ (by decide) c₇.wr)
  have m₈' : s₈.mem = s₇.mem.writeW (wordAddr (s₇.gpr sb) wSlot) (s₇.gpr (q 0)) := by rw [m₈, c₇.base]
  have hp₈ : KeyCtx s₈ nk E := hp.store c₇ m₈' g₈ wr₈ (by decide) (by decide)
  have hb₈ : s₈.gpr sb = s.gpr sb := by rw [g₈, c₇.base]
  have hx₈ : s₈.gpr .rdx = s.gpr .rdx := by rw [g₈, c₇.rdx]
  -- The second word.
  have hk₈ : AtEntry s₈ (s₈.gpr sb) m := by rw [AtEntry, hb₈, g₈, kp₇]; exact hk₆
  obtain ⟨s₉, e₉, c₉, kp₉, di₉, q₉, -⟩ := loadHalf_step hp₈ (Ctx.refl hp₈.masks) (Or.inr rfl)
    loadHalf2_check hk₈ hm34
  have hD2' : HalfRel (Qs s₉) (fun _ => (pair (E m) (E (m + 1)) (H1, H2)).2) := d₅'.congr fun j hj => by
    have := d₇ (8 + j) (by omega)
    rw [show d1Slot + (8 + j) = d2Slot + j by simp [d1Slot, d2Slot]; omega] at this
    rw [q₉ j hj, slotW_store m₈' g₈ (by simp only [d2Slot, slots_eq]; omega) (by decide),
      ite_eq_right (show ¬ d2Slot + j = wSlot by simp only [d2Slot, hwS]; omega), this]
  have hk₉ : AtEntry s₉ (s₈.gpr sb) m := by rw [AtEntry, kp₉]; exact hk₈
  obtain ⟨s₁₀, e₁₀, c₁₀, kp₁₀, di₁₀, q₁₀, -, -⟩ := lin_step hp₈ c₉ hk₉ hm34 fromBs_check (by decide +kernel)
  have hW2 : WordRel (Qs s₁₀) (fun _ => (pair (E m) (E (m + 1)) (H1, H2)).2) := fromBs_rel q₁₀ hD2'
  obtain ⟨s₁₁, e₁₁, m₁₁, g₁₁, rd₁₁, wr₁₁⟩ := stReg_ok (k := wSlot + 1) (q 0) (c₁₀.base.trans hb₈)
    (hin _ (by decide) (by rw [c₁₀.wr, wr₈, c₇.wr]))
  have m₁₁' : s₁₁.mem = s₁₀.mem.writeW (wordAddr (s₁₀.gpr sb) (wSlot + 1)) (s₁₀.gpr (q 0)) := by
    rw [m₁₁, c₁₀.base, hb₈]
  obtain ⟨s₁₂, e₁₂, kp₁₂, o₁₂, m₁₂, rd₁₂, wr₁₂⟩ := addKp_ok s₁₁ 128 (by decide)
  have hsl : ∀ k < slots, slotW s₁₂ k = slotW s₁₁ k := fun k _ => by
    simp only [slotW, m₁₂, o₁₂ sb (by decide)]
  have hsx₈ : Region.Disjoint ⟨s₈.gpr .rdx, 128⟩ ⟨s₈.gpr sb, 8 * slots⟩ := by rw [hb₈, hx₈]; exact hsx
  -- The slots above the table.
  have hhi : ∀ k, keySlot ≤ k → k < slots → k ≠ wSlot + 1 → slotW s₁₂ k = slotW s₈ k := fun k h1 h2 h3 => by
    rw [hsl k h2, slotW_store m₁₁' g₁₁ h2 (by decide), ite_eq_right h3, c₁₀.slotHi hp₈ hsx₈ h1 h2]
  refine ⟨s₁₂, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, ?_, ?_, ?_, fun k h1 h2 h3 h4 => ?_, ?_, ?_, ?_⟩
  · unfold pairPlain
    rw [show ([st (wSlot + 1) (q 0), .alu .add kp (.imm 128)] : List Instr) =
        [st (wSlot + 1) (q 0)] ++ [.alu .add kp (.imm (BitVec.ofNat 32 128))] from rfl]
    simp only [List.append_assoc]
    rw [runBlock_append', e₁, Option.bind_some, runBlock_append', e₂, Option.bind_some,
      runBlock_append', e₃, Option.bind_some, runBlock_append', e₄, Option.bind_some,
      runBlock_append', e₅, Option.bind_some, runBlock_append', e₆, Option.bind_some,
      runBlock_append', e₇, Option.bind_some, runBlock_append', e₈, Option.bind_some,
      runBlock_append', e₉, Option.bind_some, runBlock_append', e₁₀, Option.bind_some,
      runBlock_append', e₁₁, Option.bind_some, e₁₂]
  · refine hp₈.transfer (by rw [o₁₂ sb (by decide), g₁₁, c₁₀.base]) (by rw [o₁₂ _ (by decide), g₁₁, c₁₀.rdx])
      (by rw [wr₁₂, wr₁₁, c₁₀.wr]) (fun kv hkv => ?_) (fun i hi j hj => ?_)
    · have := mask_lt hkv
      rw [hsl _ (by rw [slots_eq]; rw [keySlot_eq] at this; omega),
        slotW_store m₁₁' g₁₁ (by rw [slots_eq]; rw [keySlot_eq] at this; omega) (by decide),
        ite_eq_right (show ¬ kv.1 = wSlot + 1 by rw [hwS]; rw [keySlot_eq] at this; omega)]
      exact c₁₀.masks kv hkv
    · have := hp.nk34
      rw [m₁₂, m₁₁', c₁₀.base, entryW_write _ (by decide) (by decide) (by omega) hj, c₁₀.entry hp₈ (by omega) hj]
  · rw [AtEntry, kp₁₂, g₁₁, kp₁₀, kp₉, g₈, kp₇, k₆, k₅, show s₄.gpr kp = _ from hk₄, addr_add,
      show 8 * keySlot + 64 * m + 128 = 8 * keySlot + 64 * (m + 2) by omega]
  · rw [o₁₂ r h2, g₁₁, c₁₀.keep r h1 h2 h3, g₈, c₇.keep r h1 h2 h3]
  · rw [o₁₂ _ (by decide), g₁₁, di₁₀, di₉, g₈, di₇, r₆, r₅, di₄, di₃, di₂, di₁]
  · rw [hhi _ (by decide) (by decide) (by decide), slotW_store m₈' g₈ (by decide) (by decide), ite_eq_left rfl]
    exact fun i hi j hj => hW1 0 (by decide) i hi j hj
  · rw [hsl _ (by decide), slotW_store m₁₁' g₁₁ (by decide) (by decide), ite_eq_left rfl]
    exact fun i hi j hj => hW2 0 (by decide) i hi j hj
  · rw [hhi k h1 h2 h4, slotW_store m₈' g₈ h2 (by decide), ite_eq_right h3, c₇.slotHi hp hsx h1 h2]
  · have hsub : ∀ {t : State}, t.gpr sb = s.gpr sb → t.gpr .rdx = s.gpr .rdx →
        ∀ r ∈ [(⟨t.gpr sb, 8 * keySlot⟩ : Region), ⟨t.gpr .rdx, 128⟩],
          ∃ r' ∈ [(⟨s.gpr sb, 8 * slots⟩ : Region), ⟨s.gpr .rdx, 128⟩], Region.Sub r r' := by
      intro t hb hx r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, by
          rw [hb]; intro x hx; simp only [Region.Contains] at hx ⊢; rw [slots_eq]; rw [keySlot_eq] at hx; omega⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by rw [hx]; exact fun x hx => hx⟩
    have f₈ : Frame [⟨s.gpr sb, 8 * slots⟩, ⟨s.gpr .rdx, 128⟩] s.mem s₈.mem := by
      rw [m₈]; exact (c₇.frame.sub (hsub rfl rfl)).writeW List.mem_cons_self _ (by
        rw [wordAddr]; exact VG.Offset.contains_base _ (by rw [slots_eq]; decide) (by decide))
    rw [m₁₂, m₁₁]
    exact (f₈.trans (c₁₀.frame.sub (hsub hb₈ hx₈))).writeW List.mem_cons_self _ (by
      rw [wordAddr]; exact VG.Offset.contains_base _ (by rw [slots_eq]; decide) (by decide))
  · rw [rd₁₂, rd₁₁, c₁₀.rd, rd₈, c₇.rd]
  · rw [wr₁₂, wr₁₁, c₁₀.wr, wr₈, c₇.wr]

end VG.Proof.Camellia.X86_64

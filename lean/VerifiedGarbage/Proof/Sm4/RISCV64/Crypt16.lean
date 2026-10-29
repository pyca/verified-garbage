module

public import VerifiedGarbage.Proof.Sm4.RISCV64.Core
import VerifiedGarbage.Proof.Sm4.Layout
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Interleave
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Sm4.RISCV64.LayersLit

/-!
# The transposes, and sixteen blocks of bitsliced SM4 on RISCV64

`toBs_step` turns the sixteen blocks of the tail buffer into the state's
planes, and `fromBs_step` turns the state's planes back into the output
blocks (the words in reverse order); `crypt16_wp` composes them with the
32 rounds (`rounds_wp`): each block of the tail buffer becomes the output
of SM4's rounds with the table's round keys. The rounds' S-boxes write
`a0`, `a4` and `ra` too (`sm4Writes`), so `crypt16` saves `ra` in its
slot, beyond the table (`saveAux_ok`), restores it after the rounds
(`restoreAux_ok`) and sets `a0` to the table's end again: to its caller,
`crypt16` keeps what the layers keep but `a4` (`Ctx16`), and writes that
slot too.
-/

@[expose] public section

namespace VG.Proof.Sm4.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Bitslice VG.Impl.Sm4.RISCV64
open VG.Impl.Aes.RISCV64 (q sb t0 t1 movR)
open VG.Proof.Aes.RISCV64 (sboxWrites restRegs not_sboxWrites)
open VG.Proof.Sm4 (WordRel quads ofBlock outBlock readW64_bit getLsbD_wordAt getLsbD_outBlock' blockAt_getD)
open VG.Impl.Sm4 (Lin)

/-- Block `b` of the tail buffer. -/
abbrev tailBlock (s : State) (b : Nat) : Spec.Sm4.Block :=
  Spec.Sm4.blockAt s.mem (s.gpr sb + BitVec.ofNat 64 (8 * tailSlot + 16 * b))

theorem KeyCtx.of_ctx {W : List Reg} {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E)
    (hc : CtxW W s₀ s) (hW : sb ∉ W := by decide) : KeyCtx s E where
  scr := by rw [hc.wr, hc.base hW]; exact hp.scr
  fit := by rw [hc.base hW]; exact hp.fit
  al := by rw [hc.base hW]; exact hp.al
  keys e he := by rw [hc.base hW]; exact (hp.keys e he).congr fun j hj => hc.entry hp he hj

theorem Ctx.trans {s₀ s₁ s₂ : State} (h₁ : Ctx s₀ s₁) (h₂ : Ctx s₁ s₂) : Ctx s₀ s₂ :=
  ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, fun r a b => (h₂.keep r a b).trans (h₁.keep r a b),
    h₁.frame.trans (by rw [← h₁.base]; exact h₂.frame), h₂.masks⟩

/-- `CtxW` after the rounds and `restoreAux`: `a0` and `a4`, which the
S-box writes, are not restored. -/
abbrev XCtx := CtxW (sboxWrites ++ [.a0, .a4])

theorem Ctx.xctx {s₀ s : State} (hc : Ctx s₀ s) : XCtx s₀ s :=
  ⟨hc.rd, hc.wr, fun r h1 h2 => hc.keep r (fun h => h1 (List.mem_append_left _ h)) h2, hc.frame, hc.masks⟩

theorem ok_bs {W : List Reg} {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : CtxW W s₀ s)
    (hW : sb ∉ W := by decide) : Ok bsCfg s where
  slotIn k hk := ⟨_, by rw [hc.wr]; exact hp.scr, by
    have hfit := hp.fit
    simp only [bsCfg, tableSlot_eq] at hk
    simp only [wordAddr, bsCfg, hc.base hW]
    rw [slots_eq] at hfit ⊢
    exact VG.Offset.contains_base _ (by omega) (by omega)⟩
  extIn k hk := by simp [bsCfg] at hk
  baseAl _ := by simp only [bsCfg]; rw [hc.base hW]; exact hp.al
  extAl h := by simp [bsCfg] at h
  slots := by simp only [bsCfg, tableSlot_eq]; omega
  sep k _ j hj := by simp [bsCfg] at hj

/-- What a block of slots below the table that keeps the masks keeps of `Ctx`. -/
theorem CtxW.bs {W : List Reg} {s₀ s s' : State} (hc : CtxW W s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hk : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) (hf : Frame [slotRegion bsCfg s] s.mem s'.mem)
    (hm : MasksOk s') (hW : sb ∉ W := by decide) (hsub : ∀ r ∈ sboxWrites, r ∈ W := by decide) :
    CtxW W s₀ s' :=
  hc.step hrd hwr (fun r h _ => hk r fun h' => h (hsub r h')) (hf.mono fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [slotRegion, bsCfg, hc.base hW]) hm

theorem byte_addr (b : Addr) {k i : Nat} {n : Nat} (hn : 8 * k + i = n) :
    wordAddr b k + BitVec.ofNat 64 i = b + BitVec.ofNat 64 n := by
  rw [wordAddr, addr_add, hn]

/-- The tail buffer's blocks to the state's planes. -/
theorem toBs_step {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : Ctx s₀ s) :
    ∃ s', runBlock isa toBs s = some s' ∧ Ctx s₀ s' ∧ s'.gpr kr = s.gpr kr ∧
      StRel s' (fun b w => ofBlock (tailBlock s b) w) := by
  have hchk := toBs_check
  unfold toBsEnv at hchk
  obtain ⟨s', h', -, hso, hkr, rd', wr', -, o', f', hb', -⟩ := linG_ok hchk (ok_bs hp hc)
    (fun i => slotW s (tailSlot + i))
    (fun r i hri => by simp at hri)
    (fun j i hji => by
      simp only [tailIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hji
      obtain ⟨k, hk, rfl, rfl⟩ := hji
      exact ⟨by simp only [bsCfg, tableSlot_eq, tailSlot_eq]; omega, by omega, rfl⟩)
    (fun kv hkv => ⟨by have := mask_lt hkv; simp only [bsCfg, tableSlot_eq]; omega, hc.masks kv hkv⟩)
    (fun j hj => by simp [bsCfg] at hj)
  simp only [bsCfg] at hb' hso hkr
  have hall : (restRegs.all fun r => toBs.all fun i => dst i != some r) = true := by
    lit_decide
  have hkeep : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r := fun r hr =>
    o' r (List.all_eq_true.mp hall r (not_sboxWrites r hr))
  refine ⟨s', h', hc.bs rd' wr' hkeep f' (fun kv hkv => ?_), hkeep _ (by decide), fun w hw b hb i hi j hj => ?_⟩
  · rw [slotW, hb', hkr kv.1 (List.mem_map_of_mem hkv) (by have := mask_lt hkv; rw [tableSlot_eq]; omega)]
    exact hc.masks kv hkv
  · have hp16 : 16 * i + b < 64 := by omega
    have hmem := hso (64 + (8 * w + j)) (toBsG ((8 * w + j) / 8) ((8 * w + j) % 8)) (by
        simp only [toBsOuts, List.mem_map, List.mem_range]; exact ⟨8 * w + j, by omega, rfl⟩)
        (by rw [tableSlot_eq]; omega) _ hp16
    rw [show (8 * w + j) / 8 = w by omega, show (8 * w + j) % 8 = j by omega] at hmem
    have ht : 8 * (4 * (w % 2) + i) + j < 64 := by omega
    show (slotW s' (stateSlot w j)).getLsbD (16 * i + b) = _
    rw [slotW, hb', show stateSlot w j = 64 + (8 * w + j) by simp only [stateSlot]; omega, hmem, toBsG,
      show (16 * i + b) % 16 = b by omega, show (16 * i + b) / 16 = i by omega, xorBits_cons, xorBits_nil,
      Bool.xor_false, Nat.add_assoc, bitOf_word _ _ _ ht, slotW, readW64_bit _ _ (by omega) hj]
    simp only [ofBlock]
    rw [getLsbD_wordAt _ _ hi hj, blockAt_getD _ _ (by omega), byte_addr _ rfl, addr_add]
    rw [show 8 * (tailSlot + (2 * b + w / 2)) + (4 * (w % 2) + i) = 8 * tailSlot + 16 * b + (4 * w + i) by omega]

/-- The state's planes back to the tail buffer's blocks. -/
theorem fromBs_step {s₀ s : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hc : XCtx s₀ s)
    {X : Nat → Nat → Spec.Sm4.Word} (hX : StRel s X) :
    ∃ s', runBlock isa fromBs s = some s' ∧ XCtx s₀ s' ∧ s'.gpr kr = s.gpr kr ∧ StRel s' X ∧
      ∀ b < 16, tailBlock s' b = outBlock (X b) := by
  have hchk := fromBs_check
  unfold fromBsEnv at hchk
  obtain ⟨s', h', -, hso, hkr, rd', wr', -, o', f', hb', -⟩ := linG_ok hchk (ok_bs hp hc)
    (fun i => slotW s (64 + i))
    (fun r i hri => by simp at hri)
    (fun j i hji => by
      obtain ⟨k, hk, rfl, rfl⟩ := stateIns_mem hji
      exact ⟨by simp only [bsCfg, tableSlot_eq]; omega_arith, by omega_arith, by simp only [Nat.zero_add]; rfl⟩)
    (fun kv hkv => ⟨by have := mask_lt hkv; simp only [bsCfg, tableSlot_eq]; omega_arith, hc.masks kv hkv⟩)
    (fun j hj => by simp [bsCfg] at hj)
  simp only [bsCfg] at hb' hso hkr
  have hall : (restRegs.all fun r => fromBs.all fun i => dst i != some r) = true := by
    lit_decide
  have hkeep : ∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r := fun r hr =>
    o' r (List.all_eq_true.mp hall r (not_sboxWrites r hr))
  have keep : ∀ k ∈ keyMaskSlots ++ stateSlots, slotW s' k = slotW s k := fun k hk => by
    have hk' : k < 128 := (keep_range k hk).2
    rw [slotW, hb', hkr k hk (by rw [tableSlot_eq]; exact hk')]
  refine ⟨s', h', hc.bs rd' wr' hkeep f' (fun kv hkv => ?_), hkeep _ (by decide), ?_, fun b hb => ?_⟩
  · rw [keep kv.1 (List.mem_append_left _ (List.mem_map_of_mem hkv))]; exact hc.masks kv hkv
  · exact fun w hw => (hX w hw).congr fun j hj => by
      show slotW s' (stateSlot w j) = slotW s (stateSlot w j)
      exact keep _ (List.mem_append_right _ (by
        simp only [stateSlots, List.mem_map, List.mem_range]
        exact ⟨8 * w + j, by omega_arith, by simp only [stateSlot]; omega_arith⟩))
  · apply Vector.ext
    intro k hk
    refine BitVec.eq_of_getLsbD_eq fun j hj => ?_
    rw [getLsbD_outBlock' (X b) hk hj]
    have ht : 8 * (k % 8) + j < 64 := by omega_arith
    have hmem := hso (tailSlot + (2 * b + k / 8)) (fromBsG (2 * b + k / 8)) (by
        simp only [fromBsOuts, List.mem_map, List.mem_range]; exact ⟨2 * b + k / 8, by omega_arith, rfl⟩)
        (by rw [tableSlot_eq, tailSlot_eq]; omega_arith) _ ht
    rw [readW64_bit _ _ (by omega_arith) hj, byte_addr _ rfl] at hmem
    have e1 : 8 * (3 - (2 * ((2 * b + k / 8) % 2) + (8 * (k % 8) + j) / 32)) + (8 * (k % 8) + j) % 8 =
        8 * (3 - k / 4) + j := by omega_arith
    have e2 : 16 * ((8 * (k % 8) + j) / 8 % 4) + (2 * b + k / 8) / 2 = 16 * (k % 4) + b := by omega_arith
    have hw : 3 - k / 4 < 4 := by omega_arith
    have hbit := hX (3 - k / 4) hw b hb (k % 4) (by omega_arith) j hj
    rw [fromBsG, xorBits_cons, xorBits_nil, Bool.xor_false, e1, Nat.add_assoc, e2, bitOf_word _ _ _ (by omega_arith)] at hmem
    simp only [Spec.Sm4.blockAt, Vector.getElem_ofFn]
    rw [addr_add, show 8 * tailSlot + 16 * b + k = 8 * (tailSlot + (2 * b + k / 8)) + k % 8 by omega_arith,
      hb', hmem, ← hbit, planes_eq]

/-! ## `ra` around the rounds -/

theorem auxSlot_eq : auxSlot = 396 := rfl

/-- Its slot. -/
def auxR (b : Addr) : Region := ⟨b + BitVec.ofNat 64 (8 * auxSlot), 8⟩

/-- The registers of `auxOffs`. -/
def auxRegs : List Reg := auxOffs.map (·.1)

theorem auxOffs_ho : ∀ p ∈ auxOffs, p.2 % 8 = 0 ∧ p.2 < 2048 := by decide

theorem auxOffs_ne_t0 : ∀ p ∈ auxOffs, p.1 ≠ t0 := by decide

theorem auxOffs_in (b : Addr) :
    ∀ p ∈ auxOffs, (⟨b, 8 * slots⟩ : Region).Contains (b + BitVec.ofNat 64 (8 * auxSlot) + BitVec.ofNat 64 p.2) 8 :=
  fun p hp => by
    have h2 : p.2 + 8 ≤ 8 := by revert p; decide
    rw [addr_add]
    exact VG.Offset.contains_base b (by rw [slots_eq, auxSlot_eq]; omega) (by rw [auxSlot_eq]; omega)

theorem saveAux_ok {s : State} {b : Addr} (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hb : s.gpr sb = b)
    (hal : b.toNat % 8 = 0) :
    ∃ s', runBlock isa saveAux s = some s' ∧ Spill.Saved (b + BitVec.ofNat 64 (8 * auxSlot)) s.gpr auxOffs s'.mem ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [auxR b] s.mem s'.mem := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := slotAddr_ok s t0 auxSlot
  rw [hb] at r₁
  have hal₁ : (s₁.gpr t0).toNat % 8 = 0 := by rw [r₁]; exact Spill.al8 hal (by decide)
  obtain ⟨s', e', st⟩ := Interleave.runBlock_of_WP (Spill.save_wp (b := t0) (l := auxOffs) hal₁
    auxOffs_ho fun p hp => by rw [wr₁, r₁]; exact ⟨_, hw, auxOffs_in b p hp⟩)
  refine ⟨s', by rw [saveAux, Interleave.runBlock_append, e₁, Option.bind_some]; exact e', fun p hp => ?_,
    fun r hr => by rw [st.gpr, o₁ r hr], by rw [st.rd, rd₁], by rw [st.wr, wr₁], ?_⟩
  · have := Spill.saveMem_saved (l := auxOffs) (by decide) s₁.mem (s₁.gpr t0) s₁.gpr p hp
    rw [← st.mem, r₁] at this
    rw [this, o₁ _ (auxOffs_ne_t0 p hp)]
  · rw [st.mem, auxR, ← r₁, m₁]
    exact Spill.saveMem_frame_base (by decide) (by decide) _ _ _

theorem restoreAux_ok {s₀ s : State} {b : Addr} (hw : (⟨b, 8 * slots⟩ : Region) ∈ s.wr) (hb : s.gpr sb = b)
    (hal : b.toNat % 8 = 0)
    (hs : Spill.Saved (b + BitVec.ofNat 64 (8 * auxSlot)) s₀.gpr auxOffs s.mem) :
    ∃ s', runBlock isa restoreAux s = some s' ∧ (∀ r ∈ auxRegs, s'.gpr r = s₀.gpr r) ∧
      (∀ r, r ∉ auxRegs → r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := slotAddr_ok s t0 auxSlot
  rw [hb] at r₁
  obtain ⟨s', e', rs⟩ := Interleave.runBlock_of_WP (Spill.restore_wp (b := t0) (l := auxOffs)
    (g := s₀.gpr) (Spill.al8 hal (by decide)) r₁ auxOffs_ho (by decide)
    (fun p hp => by rw [rd₁, wr₁]; exact ⟨_, List.mem_append_right _ hw, auxOffs_in b p hp⟩)
    (by rw [m₁]; exact hs))
  refine ⟨s', by rw [restoreAux, Interleave.runBlock_append, e₁, Option.bind_some]; exact e',
    fun r hr => ?_, fun r hr h0 => by rw [rs.other r hr, o₁ r h0], by rw [rs.mem, m₁], by rw [rs.rd, rd₁],
    by rw [rs.wr, wr₁]⟩
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
  exact rs.gpr p hp

/-- The slots below the saved registers' are apart from `auxR`. -/
theorem auxR_apart (b : Addr) {k : Nat} (hk : k < auxSlot) : Region.Disjoint ⟨wordAddr b k, 8⟩ (auxR b) := by
  rw [wordAddr, auxR]
  exact VG.Offset.disjoint b (Or.inl (by rw [auxSlot_eq] at hk ⊢; omega)) (by rw [auxSlot_eq] at hk; omega)
    (by rw [auxSlot_eq]; omega)

/-- A slot below `auxSlot`, through a frame of `auxR`. -/
theorem slot_auxR {m m' : Mem} {b : Addr} (hf : Frame [auxR b] m m') {k : Nat} (hk : k < auxSlot) :
    m'.readW (wordAddr b k) 64 = m.readW (wordAddr b k) 64 :=
  hf.readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact auxR_apart b hk) (by decide)

/-- The slots of `auxR`, through a frame of the slots below the table. -/
theorem auxSaved_frame {m m' : Mem} {b : Addr} {g : Reg → BitVec 64}
    (hf : Frame [⟨b, 8 * tableSlot⟩] m m') (hs : Spill.Saved (b + BitVec.ofNat 64 (8 * auxSlot)) g auxOffs m) :
    Spill.Saved (b + BitVec.ofNat 64 (8 * auxSlot)) g auxOffs m' := fun p hp => by
  rw [← hs p hp]
  have h2 : p.2 + 8 ≤ 8 := by revert p; decide
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  rw [addr_add]
  exact VG.Offset.disjoint_base b (by rw [tableSlot_eq, auxSlot_eq]; omega) (by rw [auxSlot_eq]; omega)

/-- Through a frame of `auxR`: the round keys, the masks and the state. -/
theorem KeyCtx.of_auxFrame {s s' : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s E)
    (hb : s'.gpr sb = s.gpr sb) (hwr : s'.wr = s.wr) (hf : Frame [auxR (s.gpr sb)] s.mem s'.mem) :
    KeyCtx s' E where
  scr := by rw [hb, hwr]; exact hp.scr
  fit := by rw [hb]; exact hp.fit
  al := by rw [hb]; exact hp.al
  keys e he := (hp.keys e he).congr fun j hj => by
    rw [hb]
    have hfit := hp.fit
    simp only [entryW]
    refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    rw [auxR]
    rw [slots_eq] at hfit
    exact VG.Offset.disjoint _ (Or.inl (by rw [tableSlot_eq, auxSlot_eq]; omega)) (by rw [tableSlot_eq]; omega)
      (by rw [auxSlot_eq]; omega)

theorem slotW_auxFrame {s s' : State} (hb : s'.gpr sb = s.gpr sb) (hf : Frame [auxR (s.gpr sb)] s.mem s'.mem)
    {k : Nat} (hk : k < auxSlot) : slotW s' k = slotW s k := by
  simp only [slotW, hb]; exact slot_auxR hf hk

theorem MasksOk.of_auxFrame {s s' : State} (hm : MasksOk s) (hb : s'.gpr sb = s.gpr sb)
    (hf : Frame [auxR (s.gpr sb)] s.mem s'.mem) : MasksOk s' := fun kv hkv => by
  rw [slotW_auxFrame hb hf (by have := mask_lt hkv; rw [auxSlot_eq]; omega)]; exact hm kv hkv

theorem StRel.of_auxFrame {s s' : State} {X : Nat → Nat → Spec.Sm4.Word} (hX : StRel s X)
    (hb : s'.gpr sb = s.gpr sb) (hf : Frame [auxR (s.gpr sb)] s.mem s'.mem) : StRel s' X := fun w hw =>
  (hX w hw).congr fun j hj => slotW_auxFrame hb hf (by simp only [stateSlot, auxSlot_eq]; omega)

/-- After the rounds (`RCtx`) and `restoreAux`, which gives back the register
`saveAux` saved from `s` to `sA`: `XCtx`. -/
theorem XCtx.of_restore {s sA s₂ sR : State} (c₂ : RCtx sA s₂) (gA : ∀ r, r ≠ t0 → sA.gpr r = s.gpr r)
    (gR : ∀ r ∈ auxRegs, sR.gpr r = s.gpr r) (oR : ∀ r, r ∉ auxRegs → r ≠ t0 → sR.gpr r = s₂.gpr r)
    (mR : sR.mem = s₂.mem) (rdR : sR.rd = s₂.rd) (wrR : sR.wr = s₂.wr) : XCtx sA sR := by
  have notAux : ∀ r, r ∉ sboxWrites ++ [.a0, .a4] → r ∉ auxRegs → r ∉ sm4Writes := fun r h1 h2 h => by
    have h' : r ∈ sboxWrites ++ [.a0, .a4] ∨ r = .ra := by
      simpa only [sm4Writes, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] using h
    rcases h' with h' | rfl
    · exact h1 h'
    · exact h2 (by decide)
  have kR : ∀ r, r ∉ sboxWrites ++ [.a0, .a4] → r ≠ kr → sR.gpr r = sA.gpr r := fun r h1 h2 => by
    by_cases ha : r ∈ auxRegs
    · rw [gR r ha, gA r (fun h => h1 (by subst h; decide))]
    · rw [oR r ha (fun h => h1 (by subst h; decide)), c₂.keep r (notAux r h1 ha) h2]
  have bR : sR.gpr sb = sA.gpr sb := kR sb (by decide) (by decide)
  exact ⟨by rw [rdR, c₂.rd], by rw [wrR, c₂.wr], kR, by rw [mR]; exact c₂.frame, fun kv hkv => by
    show sR.mem.readW (wordAddr (sR.gpr sb) kv.1) 64 = kv.2
    rw [mR, bR, ← c₂.base]; exact c₂.masks kv hkv⟩

/-- What `crypt16` keeps: what the layers keep but `a4`, but memory changes
in the slots below the table and in `auxR`. -/
structure Ctx16 (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, r ∉ sboxWrites → r ≠ kr → r ≠ .a4 → s.gpr r = s₀.gpr r
  frame : Frame [⟨s₀.gpr sb, 8 * tableSlot⟩, auxR (s₀.gpr sb)] s₀.mem s.mem
  masks : MasksOk s

theorem Ctx16.base {s₀ s : State} (hc : Ctx16 s₀ s) : s.gpr sb = s₀.gpr sb :=
  hc.keep _ (by decide) (by decide) (by decide)

/-- `crypt16`: each block of the tail buffer becomes the output of SM4's 32
rounds with the table's round keys. -/
theorem crypt16_wp {s₀ : State} {E : Nat → Spec.Sm4.Word} (hp : KeyCtx s₀ E) (hm : MasksOk s₀)
    (ha0 : s₀.gpr .a0 = s₀.gpr sb + BitVec.ofNat 64 (8 * tableEnd)) :
    WP isa crypt16 s₀ fun s' => Ctx16 s₀ s' ∧
      ∀ b < 16, tailBlock s' b = outBlock (quads .enc E 8 (ofBlock (tailBlock s₀ b))) := by
  have hfit := hp.fit
  obtain ⟨s₁, e₁, c₁, -, X₁⟩ := toBs_step hp (CtxW.refl hm)
  have b₁ : s₁.gpr sb = s₀.gpr sb := c₁.base
  -- `ra` to its slot.
  obtain ⟨sA, eA, svA, gA, rdA, wrA, fA⟩ := saveAux_ok (s := s₁) (b := s₀.gpr sb) (by rw [c₁.wr]; exact hp.scr)
    b₁ hp.al
  have bA : sA.gpr sb = s₀.gpr sb := by rw [gA _ (by decide), b₁]
  have keepA : ∀ k < auxSlot, slotW sA k = slotW s₁ k := fun k hk => by
    simp only [slotW, bA, b₁]; exact slot_auxR fA hk
  have hmA : MasksOk sA := fun kv hkv => by
    rw [keepA _ (by have := mask_lt hkv; rw [auxSlot_eq]; omega)]; exact c₁.masks kv hkv
  have XA : StRel sA (fun b w => ofBlock (tailBlock s₀ b) w) := fun w hw =>
    (X₁ w hw).congr fun j hj => keepA _ (by simp only [stateSlot, auxSlot_eq]; omega)
  have hpA : KeyCtx sA E :=
    { scr := by rw [bA, wrA, c₁.wr]; exact hp.scr
      fit := by rw [bA]; exact hfit
      al := by rw [bA]; exact hp.al
      keys := fun e he => (hp.keys e he).congr fun j hj => by
        rw [bA, ← c₁.entry hp he hj]
        simp only [entryW]
        refine fA.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
        simp only [List.mem_singleton] at hr; subst hr
        rw [auxR]
        rw [slots_eq] at hfit
        exact VG.Offset.disjoint _ (Or.inl (by rw [tableSlot_eq, auxSlot_eq]; omega)) (by rw [tableSlot_eq]; omega)
          (by rw [auxSlot_eq]; omega) }
  refine WP.seq (WP.of_runBlock ⟨sA, by rw [runBlock_app, e₁, Option.bind_some, eA], ?_⟩)
  -- The rounds.
  refine WP.seq (WP.mono (rounds_wp .enc hpA hmA XA) fun s₂ ⟨c₂, X₂⟩ => ?_)
  have b₂ : s₂.gpr sb = s₀.gpr sb := by rw [c₂.base, bA]
  -- `ra` back.
  obtain ⟨sR, eR, gR, oR, mR, rdR, wrR⟩ := restoreAux_ok (s₀ := s₁) (s := s₂) (b := s₀.gpr sb)
    (by rw [c₂.wr, wrA, c₁.wr]; exact hp.scr) b₂ hp.al (auxSaved_frame (by rw [← bA]; exact c₂.frame) svA)
  have cR : XCtx sA sR := XCtx.of_restore c₂ gA gR oR mR rdR wrR
  have XR : StRel sR (fun b => quads .enc E 8 (ofBlock (tailBlock s₀ b))) :=
    X₂.congr fun k => by simp only [slotW, mR, oR sb (by decide) (by decide)]
  -- Back to blocks, and `a0` to the table's end.
  obtain ⟨s₄, e₄, c₄, -, -, hout⟩ := fromBs_step hpA cR XR
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := slotAddr_ok s₄ .a0 tableEnd
  have b₄ : s₄.gpr sb = s₀.gpr sb := by rw [c₄.base, bA]
  refine WP.of_runBlock ⟨s₅, by rw [runBlock_app, runBlock_app, eR, Option.bind_some, e₄, Option.bind_some, e₅],
    ⟨?_, ?_, fun r h1 h2 h3 => ?_, ?_, fun kv hkv => ?_⟩, fun b hb => ?_⟩
  · rw [rd₅, c₄.rd, rdA, c₁.rd]
  · rw [wr₅, c₄.wr, wrA, c₁.wr]
  · by_cases h0 : r = .a0
    · subst h0; rw [r₅, b₄, ha0]
    · have h4 : r ∉ sboxWrites ++ [.a0, .a4] := by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1, h0, h3⟩
      rw [o₅ r h0, c₄.keep r h4 h2, gA r (fun h => h1 (by subst h; decide)), c₁.keep r h1 h2]
  · have f₁ := c₁.frame
    have f₄ := c₄.frame
    rw [bA] at f₄
    rw [m₅]
    refine (f₁.mono fun r hr => ?_).trans ((fA.mono fun r hr => ?_).trans (f₄.mono fun r hr => ?_)) <;>
      simp_all
  · simp only [slotW, m₅, o₅ sb (by decide)]; exact c₄.masks kv hkv
  · rw [← hout b hb]; simp only [tailBlock, m₅, o₅ sb (by decide)]

end VG.Proof.Sm4.RISCV64

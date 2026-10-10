import VerifiedGarbage.Proof.Camellia.AArch64.Crypt8
import VerifiedGarbage.Proof.Camellia.AArch64.KeyChecks

/-!
# The table of bitsliced subkeys on AArch64

As on x86-64: `keyOne_step`: `keyOne d` bitslices the subkey at `[x0 + d]`
(its eight bytes, the most significant first: `wordAt`) into the table's
entry at `kp`, every block's copy of it alike, and steps `kp` to the next
entry. `encKeys_wp` and `decKeys_wp` build the table in the order the
rounds use the subkeys: for encryption the stored order, for decryption
`decPerm`'s.
-/

namespace VG.Proof.Camellia.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Camellia.AArch64
open VG.Impl.Aes.AArch64 (q sb t0 t1 kp movR)
open VG.Proof.Camellia (HalfRel WordRel pos)

/-! ## Steps of the pointers and the counters -/

theorem addI_ok (s : State) (d n : Reg) {imm : Nat} (h : imm < 4096) :
    ∃ s', runBlock isa [.addImm .x d n imm] s = some s' ∧ s'.gpr d = s.gpr n + BitVec.ofNat 64 imm ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.write .x d (s.gpr n + BitVec.ofNat 64 imm), by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addImm_x h, read_x'],
    (RegUpd.gpr_write_self _ _ _ _).trans (BitVec.setWidth_eq _),
    fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr, rfl, rfl, rfl⟩

theorem subI_ok (s : State) (d n : Reg) {imm : Nat} (h : imm < 4096) :
    ∃ s', runBlock isa [.subImm .x d n imm] s = some s' ∧ s'.gpr d = s.gpr n - BitVec.ofNat 64 imm ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.write .x d (s.gpr n - BitVec.ofNat 64 imm), by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_subImm_x h, read_x'],
    (RegUpd.gpr_write_self _ _ _ _).trans (BitVec.setWidth_eq _),
    fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr, rfl, rfl, rfl⟩

theorem movR_ok (s : State) (d n : Reg) :
    ∃ s', runBlock isa [movR d n] s = some s' ∧ s'.gpr d = s.gpr n ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s', e', v', o', m', rd', wr'⟩ := addI_ok s d n (imm := 0) (by decide)
  exact ⟨s', e', by rw [v', BitVec.add_zero], o', m', rd', wr'⟩

theorem movz_ok (s : State) (d : Reg) {v : Nat} (hv : v < 65536) :
    ∃ s', runBlock isa [.movz .x d (BitVec.ofNat 16 v) 0] s = some s' ∧ s'.gpr d = BitVec.ofNat 64 v ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨s.write .x d ((BitVec.ofNat 16 v).setWidth 64 <<< (16 * 0)), ?_, ?_,
    fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr, rfl, rfl, rfl⟩
  · simp only [runBlock_cons]; rfl
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq]
    apply BitVec.eq_of_toNat_eq
    simp only [Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_arith

/-! ## One subkey -/

/-- The table's entry `e` holds `k` for every block. -/
abbrev EntryOk (m : Mem) (b : Addr) (e : Nat) (k : BitVec 64) : Prop := HalfRel (entryW m b e) fun _ => k

theorem keyOne_step {s : State} {b : Addr} {d e : Nat} (hd : d = 0 ∨ d = 8)
    (hb : s.gpr sb = b) (hscr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr)
    (hkp : s.gpr kp = b + BitVec.ofNat 64 (8 * keySlot + 64 * e)) (he : e < 34)
    (hx0 : ∀ k < d / 8 + 1, InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .x0) k) 8)
    (hsep : ∀ k < keySlot, ∀ j < d / 8 + 1, Mem.Sep (wordAddr b k) 8 (wordAddr (s.gpr .x0) j) 8)
    (hm : MasksOk s) :
    ∃ s', runBlock isa (keyOne d) s = some s' ∧
      s'.gpr kp = s.gpr kp + BitVec.ofNat 64 64 ∧ (∀ r, r ∉ layerWrites → r ≠ kp → s'.gpr r = s.gpr r) ∧
      s'.gpr t1 = s.gpr t1 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ MasksOk s' ∧
      Frame [⟨b, 8 * keySlot⟩, ⟨b + BitVec.ofNat 64 (8 * keySlot + 64 * e), 64⟩] s.mem s'.mem ∧
      EntryOk s'.mem b e (Spec.Camellia.wordAt s.mem (s.gpr .x0 + BitVec.ofNat 64 d)) := by
  rw [slots_eq] at hscr
  have hok : Ok (keyCfg (d / 8 + 1)) s :=
    { slotIn := fun k hk => ⟨_, hscr, by
        simp only [keyCfg, keySlot_eq] at hk ⊢
        rw [hb]; exact VG.Offset.contains_base b (by omega_arith) (by omega_arith)⟩
      extIn := fun k hk => hx0 k (by simpa [keyCfg] using hk)
      slots := by simp [keyCfg, keySlot_eq]
      sep := fun k hk j hj => by
        simp only [keyCfg] at hk hj ⊢; rw [hb]; exact hsep k hk j hj }
  have hchk : check (lanes 64 7) (keyCfg (d / 8 + 1)) (linExt 0) (keyLoad d) keyEnv
      (linPostG 7 (qOuts (keyBsG d)) [] maskSlots keyEnv) = true := by
    rcases hd with rfl | rfl
    · exact keyLoad0_check
    · exact keyLoad8_check
  unfold keyEnv at hchk
  obtain ⟨s₁, e₁, ho₁, -, hkp₁, rd₁, wr₁, -, o₁, f₁, hb₁, -⟩ := linG_ok hchk hok
    (fun k => s.mem.readW (wordAddr (s.gpr .x0) k) 64)
    (fun r i hri => by simp at hri) (fun j i hji => by simp at hji)
    (fun kv hkv => ⟨by simp only [keyCfg]; exact mask_lt hkv, by
      simp only [keyCfg]; exact hm kv hkv⟩)
    (fun j hj => ⟨by simp only [keyCfg] at hj; omega_arith, by simp only [keyCfg, Nat.zero_add]⟩)
  simp only [keyCfg] at hb₁ hkp₁ f₁
  have hall₁ : ∀ r, r ∉ layerWrites → ((keyLoad d).all fun i => dstOf i != some r) = true := fun r hr => by
    have h := not_layerWrites r hr
    have : (layerKeep.all fun r => (keyLoad d).all fun i => dstOf i != some r) = true := by
      rcases hd with rfl | rfl <;> decide +kernel
    exact List.all_eq_true.mp this r h
  have k₁ : ∀ r, r ∉ layerWrites → s₁.gpr r = s.gpr r := fun r hr => o₁ r (hall₁ r hr)
  -- The planes of the subkey.
  have hQ : HalfRel (Qs s₁) (fun _ => Spec.Camellia.wordAt s.mem (s.gpr .x0 + BitVec.ofNat 64 d)) := by
    have hw := wordRel_key s.mem (s.gpr .x0 + BitVec.ofNat 64 d)
    refine Camellia.half_of_words (W := fun _ => s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 d) 64)
      (fun j hj p hp => ?_) hw
    have := Camellia.pos_lt (show p / 8 < 8 by omega_arith)
    rw [Qs, ho₁ (q j) (keyBsG d j) (by simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
      p hp, keyBsG, xorBits_cons, xorBits_nil, Bool.xor_false, Nat.add_assoc, bitOf_word _ _ _ (by omega_arith)]
    rcases hd with rfl | rfl <;> rfl
  -- The stores.
  have hkp₁' : s₁.gpr kp = s.gpr kp := k₁ kp (by decide)
  have hok₂ : Ok entryCfg s₁ :=
    { slotIn := fun k hk => ⟨_, by rw [wr₁]; exact hscr, by
        simp only [entryCfg] at hk ⊢
        rw [hkp₁', hkp, wordAddr, addr_add]
        exact VG.Offset.contains_base b (by rw [keySlot_eq]; omega_arith) (by rw [keySlot_eq]; omega_arith)⟩
      extIn := fun k hk => by simp [entryCfg] at hk
      slots := by simp [entryCfg]
      sep := fun k _ j hj => by simp [entryCfg] at hj }
  have hchk₂ := keyStore_check
  unfold entryEnv at hchk₂
  obtain ⟨s₂, e₂, -, hso₂, -, rd₂, wr₂, -, o₂, f₂, hb₂, -⟩ := linG_ok hchk₂ hok₂ (Qs s₁)
    (fun r i hri => by
      simp only [qIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hri
      obtain ⟨i, hi, rfl, rfl⟩ := hri
      exact ⟨by omega_arith, rfl⟩)
    (fun j i hji => by simp at hji) (fun kv hkv => by simp at hkv)
    (fun j hj => by simp [entryCfg] at hj)
  simp only [entryCfg] at hb₂ hso₂ f₂
  have hall₂ : ∀ r, (keyStore.all fun i => dstOf i != some r) = true := fun r => by
    simp [keyStore, dstOf]
  have k₂ : ∀ r, s₂.gpr r = s₁.gpr r := fun r => o₂ r (hall₂ r)
  obtain ⟨s₃, e₃, kp₃, o₃, m₃, rd₃, wr₃⟩ := addKp_ok s₂ 64 (by decide)
  have he₂ : ∀ j < 8, entryW s₂.mem b e j = Qs s₁ j := fun j hj => BitVec.eq_of_getLsbD_eq fun p hp => by
    have h := hso₂ j (fun p => [64 * j + p]) (by simp only [List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
      hj p hp
    rw [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hp] at h
    rw [← h, entryW, wordAddr, hkp₁', hkp, addr_add]
  have ht1 : s₁.gpr t1 = s.gpr t1 := o₁ t1 (by rcases hd with rfl | rfl <;> decide +kernel)
  refine ⟨s₃, ?_, ?_, fun r h1 h2 => ?_, by rw [o₃ t1 (by decide), k₂, ht1], by rw [rd₃, rd₂, rd₁],
    by rw [wr₃, wr₂, wr₁], fun kv hkv => ?_, ?_, ?_⟩
  · rw [keyOne_eq, runBlock_append', runBlock_append', e₁, Option.bind_some, e₂, Option.bind_some]
    exact e₃
  · rw [kp₃, k₂, hkp₁']
  · rw [o₃ r h2, k₂, k₁ r h1]
  · have hk : kv.1 < keySlot := mask_lt hkv
    show s₃.mem.readW (wordAddr (s₃.gpr sb) kv.1) 64 = kv.2
    have h2 : s₂.mem.readW (wordAddr (s.gpr sb) kv.1) 64 = s₁.mem.readW (wordAddr (s.gpr sb) kv.1) 64 := by
      refine f₂.readW (r := ⟨wordAddr (s.gpr sb) kv.1, 8⟩) (Region.contains_self _ _) (fun r hr => ?_)
        (by decide)
      simp only [slotRegion, List.mem_singleton] at hr; subst hr
      rw [hkp₁', hkp, hb, wordAddr]
      exact VG.Offset.disjoint b (Or.inl (by rw [keySlot_eq] at hk ⊢; omega_arith)) (by rw [keySlot_eq] at hk; omega_arith)
        (by rw [keySlot_eq]; omega_arith)
    rw [m₃, o₃ sb (by decide), k₂, hb₁, h2, hkp₁ kv.1 (List.mem_map_of_mem hkv) hk]
    exact hm kv hkv
  · rw [m₃]
    refine (f₁.mono fun r hr => ?_).trans (f₂.mono fun r hr => ?_)
    · simp only [slotRegion, List.mem_singleton] at hr; subst hr; simp [hb]
    · simp only [slotRegion, List.mem_singleton] at hr; subst hr
      simp [hkp₁', hkp]
  · refine hQ.congr fun j hj => ?_
    show entryW s₃.mem b e j = _
    rw [m₃]; exact he₂ j hj

/-! ## The loops -/

/-- The scratch buffer at `b` and the schedule's 34 words at `sched`, apart. -/
structure KeyPre (s : State) (b sched : Addr) : Prop where
  base : s.gpr sb = b
  scr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr
  fit : b.toNat + 8 * slots ≤ 2 ^ 64
  sch : (⟨sched, 272⟩ : Region) ∈ s.rd ++ s.wr
  schFit : sched.toNat + 272 ≤ 2 ^ 64
  sep : Region.Disjoint ⟨sched, 272⟩ ⟨b, 8 * slots⟩

theorem KeyPre.congr {s s' : State} {b sched : Addr} (h : KeyPre s b sched) (hb : s'.gpr sb = s.gpr sb)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : KeyPre s' b sched :=
  ⟨hb.trans h.base, hwr ▸ h.scr, h.fit, hrd ▸ hwr ▸ h.sch, h.schFit, h.sep⟩

theorem KeyPre.word {s : State} {b sched : Addr} (h : KeyPre s b sched) {w j : Nat} (hw : w + j < 34) :
    InRegions (s.rd ++ s.wr) (wordAddr (sched + BitVec.ofNat 64 (8 * w)) j) 8 :=
  ⟨_, h.sch, by rw [wordAddr, addr_add]; exact VG.Offset.contains_base sched (by omega_arith) (by omega_arith)⟩

theorem KeyPre.wsep {s : State} {b sched : Addr} (h : KeyPre s b sched) {w j : Nat} (hw : w + j < 34)
    {k : Nat} (hk : k < slots) :
    Mem.Sep (wordAddr b k) 8 (wordAddr (sched + BitVec.ofNat 64 (8 * w)) j) 8 := by
  have hf := h.fit
  rw [slots_eq] at hf hk
  refine h.sep.symm.sep (VG.Offset.contains_base b (by rw [slots_eq]; omega_arith) (by omega_arith)) ?_
  rw [wordAddr, addr_add]; exact VG.Offset.contains_base sched (by omega_arith) (by omega_arith)

/-- The schedule is outside the scratch buffer. -/
theorem KeyPre.wordAt_eq {s : State} {b sched : Addr} (h : KeyPre s b sched) {m m' : Mem} {n : Nat}
    (hn : n ≤ slots) (hf : Frame [⟨b, 8 * n⟩] m m') {w : Nat} (hw : w < 34) :
    Spec.Camellia.wordAt m' (sched + BitVec.ofNat 64 (8 * w)) =
      Spec.Camellia.wordAt m (sched + BitVec.ofNat 64 (8 * w)) := by
  refine wordAt_frame hf fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact (h.sep.sub_left (VG.Offset.sub_base _ (by omega_arith))).sub_right (Region.sub_prefix (by omega_arith))

/-- An entry outside a frame keeps its planes. -/
theorem entryW_frame {m m' : Mem} {b : Addr} {e i : Nat}
    (hf : Frame [⟨b, 8 * keySlot⟩, ⟨b + BitVec.ofNat 64 (8 * keySlot + 64 * e), 64⟩] m m')
    (hi : i < 34) (he : e < 34) (hie : i ≠ e) {j : Nat} (hj : j < 8) : entryW m' b i j = entryW m b i j := by
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact VG.Offset.disjoint_base b (by rw [keySlot_eq]; omega_arith) (by rw [keySlot_eq]; omega_arith)
  · exact VG.Offset.disjoint b (by rw [keySlot_eq]; omega_arith) (by rw [keySlot_eq]; omega_arith)
      (by rw [keySlot_eq]; omega_arith)

/-- What the loops keep, after `k` of their `N` iterations: the subkeys `F`
in the entries before `e₀ + k`, `x0` at word `wk k` of the schedule. -/
structure KeyInv (s₀ : State) (b sched : Addr) (e₀ N : Nat) (wk : Nat → Nat) (F : Nat → BitVec 64)
    (k : Nat) (s : State) : Prop where
  pre : KeyPre s b sched
  kpos : s.gpr kp = b + BitVec.ofNat 64 (8 * keySlot + 64 * (e₀ + k))
  x0 : s.gpr .x0 = sched + BitVec.ofNat 64 (8 * wk k)
  cnt : s.gpr t1 = BitVec.ofNat 64 (N - k)
  ent : ∀ i < e₀ + k, EntryOk s.mem b i (F i)
  masks : MasksOk s
  frame : Frame [⟨b, 8 * endSlot⟩] s₀.mem s.mem
  regs : ∀ r, r ∉ layerWrites → r ≠ kp → r ≠ .x0 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The loop of `keyOne 0` and `op x0, x0, #8` (`f` on `x0`), counted down in `t1`. -/
theorem keyLoop_wp {s₀ s : State} {b sched : Addr} {e₀ N : Nat} {wk : Nat → Nat} {F : Nat → BitVec 64}
    {i₁ : Instr} {f : Addr → Addr}
    (hop : ∀ s : State, ∃ s', runBlock isa [i₁] s = some s' ∧
      s'.gpr .x0 = f (s.gpr .x0) ∧ (∀ r, r ≠ .x0 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr)
    (hN : e₀ + N ≤ 34)
    (hwk : ∀ k < N, wk k < 34)
    (hstep : ∀ k < N, f (sched + BitVec.ofNat 64 (8 * wk k)) = sched + BitVec.ofNat 64 (8 * wk (k + 1)))
    (hF : ∀ k < N, F (e₀ + k) = Spec.Camellia.wordAt s₀.mem (sched + BitVec.ofNat 64 (8 * wk k)))
    {k : Nat} (hk : k < N) (hs : KeyInv s₀ b sched e₀ N wk F k s) :
    WP isa (.loop (.block (keyOne 0 ++ ([i₁, .subImm .x t1 t1 1] : List Instr))) (.nonzero .x t1)) s
      (KeyInv s₀ b sched e₀ N wk F N) := by
  refine WP.loop (M := isa) (fun n s => ∃ k, n = N - k ∧ k < N ∧ KeyInv s₀ b sched e₀ N wk F k s)
    (fun n s hs => ?_) (N - k) s ⟨k, rfl, hk, hs⟩
  obtain ⟨k, rfl, hk, hi⟩ := hs
  have hfit := hi.pre.fit
  have hw := hwk k hk
  have hx0 := hi.x0
  obtain ⟨s₁, e₁, kp₁, o₁, t₁, rd₁, wr₁, m₁, f₁, E₁⟩ := keyOne_step (d := 0) (e := e₀ + k) (Or.inl rfl)
    hi.pre.base hi.pre.scr hi.kpos (by omega_arith)
    (fun j hj => by rw [hx0]; exact hi.pre.word (by omega_arith))
    (fun j hj l hl => by rw [hx0]; exact hi.pre.wsep (by omega_arith) (by rw [slots_eq, keySlot_eq] at *; omega_arith))
    hi.masks
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := hop s₁
  obtain ⟨s₃, e₃, c₃, o₃, m₃, rd₃, wr₃⟩ := subI_ok s₂ t1 t1 (imm := 1) (by decide)
  refine WP.of_runBlock ⟨s₃, by
    rw [runBlock_append', e₁, Option.bind_some,
      show ([i₁, .subImm .x t1 t1 1] : List Instr) = [i₁] ++ [.subImm .x t1 t1 1] from rfl,
      runBlock_append', e₂, Option.bind_some, e₃], ?_⟩
  have ht₂ : s₂.gpr t1 = BitVec.ofNat 64 (N - k) := by rw [o₂ _ (by decide), t₁, hi.cnt]
  have hc₃ : s₃.gpr t1 = BitVec.ofNat 64 (N - (k + 1)) := by
    rw [c₃, ht₂, VG.Offset.ofNat_sub_ofNat (by omega_arith), show N - k - 1 = N - (k + 1) by omega_arith]
  -- The new invariant.
  have hf₁₃ : Frame [⟨b, 8 * keySlot⟩, ⟨b + BitVec.ofNat 64 (8 * keySlot + 64 * (e₀ + k)), 64⟩] s.mem s₃.mem := by
    rw [m₃, m₂]; exact f₁
  have hinv : KeyInv s₀ b sched e₀ N wk F (k + 1) s₃ := by
    refine ⟨hi.pre.congr ?_ ?_ ?_, ?_, ?_, hc₃, fun i hi' => ?_, fun kv hkv => ?_, ?_, fun r h1 h2 h3 => ?_,
      by rw [rd₃, rd₂, rd₁, hi.rd], by rw [wr₃, wr₂, wr₁, hi.wr]⟩
    · rw [o₃ _ (by decide), o₂ _ (by decide), o₁ _ (by decide) (by decide)]
    · rw [rd₃, rd₂, rd₁]
    · rw [wr₃, wr₂, wr₁]
    · rw [o₃ _ (by decide), o₂ _ (by decide), kp₁, hi.kpos, addr_add,
        show 8 * keySlot + 64 * (e₀ + k) + 64 = 8 * keySlot + 64 * (e₀ + (k + 1)) by omega_arith]
    · rw [o₃ _ (by decide), r₂, o₁ _ (by decide) (by decide), hx0, hstep k hk]
    · by_cases he : i = e₀ + k
      · subst he
        have hw' : Spec.Camellia.wordAt s.mem (s.gpr .x0 + BitVec.ofNat 64 0) = F (e₀ + k) := by
          rw [hx0, addr_add, Nat.add_zero, hF k hk]
          exact hi.pre.wordAt_eq (by rw [endSlot_eq, slots_eq]; decide) hi.frame hw
        rw [← hw']
        exact E₁.congr fun j _ => by
          show entryW s₃.mem b (e₀ + k) j = entryW s₁.mem b (e₀ + k) j
          rw [m₃, m₂]
      · refine (hi.ent i (by omega_arith)).congr fun j hj => ?_
        exact entryW_frame hf₁₃ (by omega_arith) (by omega_arith) he hj
    · show s₃.mem.readW (wordAddr (s₃.gpr sb) kv.1) 64 = kv.2
      rw [m₃, m₂, o₃ _ (by decide), o₂ _ (by decide)]; exact m₁ kv hkv
    · refine hi.frame.trans ((f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
        (by rw [m₃, m₂]; exact Frame.refl _ _))
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Region.sub_prefix (by rw [keySlot_eq, endSlot_eq]; omega_arith)
      · exact VG.Offset.sub_base b (by rw [keySlot_eq, endSlot_eq]; omega_arith)
    · rw [o₃ r (fun h => h1 (by subst h; decide)), o₂ r h3, o₁ r h1 h2, hi.regs r h1 h2 h3]
  have hz : (s₃.gpr t1 == 0) = decide (N - (k + 1) = 0) := by
    rw [hc₃, show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, Bool.eq_iff_iff, beq_iff_eq,
      decide_eq_true_iff]
    constructor
    · intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega_arith
    · intro h; rw [h]
  by_cases hl : k + 1 = N
  · refine .inl ⟨(eval_nonzero s₃ t1).trans (by rw [hz]; simp; omega_arith),
      by rw [show k + 1 = N from hl] at hinv; exact hinv⟩
  · exact .inr ⟨(eval_nonzero s₃ t1).trans (by rw [hz]; simp; omega_arith), N - (k + 1), by omega_arith, k + 1, rfl,
      by omega_arith, hinv⟩

/-! ## The tables -/

/-- What the table's construction leaves: entry `i` holds word `perm i` of the schedule. -/
structure KeysPost (s₀ : State) (b sched : Addr) (g : Nat) (perm : Nat → Nat) (s : State) : Prop where
  pre : KeyPre s b sched
  ent : ∀ i < 8 * g + 2,
    EntryOk s.mem b i (Spec.Camellia.wordAt s₀.mem (sched + BitVec.ofNat 64 (8 * perm i)))
  masks : MasksOk s
  frame : Frame [⟨b, 8 * endSlot⟩] s₀.mem s.mem
  regs : ∀ r, r ∉ layerWrites → r ≠ kp → r ≠ .x0 → r ≠ .x4 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem add8 (x : Addr) {w : Nat} :
    x + BitVec.ofNat 64 (8 * w) + BitVec.ofNat 64 8 = x + BitVec.ofNat 64 (8 * (w + 1)) := by
  rw [addr_add, show 8 * w + 8 = 8 * (w + 1) by omega_arith]

theorem sub8 (x : Addr) {w : Nat} :
    x + BitVec.ofNat 64 (8 * (w + 1)) - BitVec.ofNat 64 8 = x + BitVec.ofNat 64 (8 * w) := by
  rw [VG.Offset.add_ofNat_sub _ (by omega_arith), show 8 * (w + 1) - 8 = 8 * w by omega_arith]

theorem encKeys_wp {s₀ : State} {b sched : Addr} {g : Nat} (hg : g = 3 ∨ g = 4) (hk : KeyPre s₀ b sched)
    (hx0 : s₀.gpr .x0 = sched) (hm : MasksOk s₀) :
    WP isa (encKeys g) s₀ (KeysPost s₀ b sched g id) := by
  have hg4 : g ≤ 4 := by omega_arith
  obtain ⟨s₁, e₁, k₁, o₁, m₁, rd₁, wr₁⟩ := setKp_ok s₀
  obtain ⟨s₂, e₂, t₂, o₂, m₂, rd₂, wr₂⟩ := movz_ok s₁ t1 (v := 8 * g + 2) (by omega_arith)
  unfold encKeys
  refine WP.seq (WP.of_runBlock ⟨s₂, by rw [runBlock_append', e₁, Option.bind_some, e₂], ?_⟩)
  have hinv : KeyInv s₀ b sched 0 (8 * g + 2) id (fun i => Spec.Camellia.wordAt s₀.mem
      (sched + BitVec.ofNat 64 (8 * i))) 0 s₂ := by
    refine ⟨hk.congr ?_ ?_ ?_, ?_, ?_, ?_, fun i hi => by omega_arith, fun kv hkv => ?_, ?_, fun r h1 h2 _ => ?_,
      by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
    · rw [o₂ _ (by decide), o₁ _ (by decide)]
    · rw [rd₂, rd₁]
    · rw [wr₂, wr₁]
    · rw [o₂ _ (by decide), k₁, hk.base]; simp
    · rw [o₂ _ (by decide), o₁ _ (by decide), hx0]; simp
    · rw [t₂, Nat.sub_zero]
    · show s₂.mem.readW (wordAddr (s₂.gpr sb) kv.1) 64 = kv.2
      rw [m₂, m₁, o₂ _ (by decide), o₁ _ (by decide)]; exact hm kv hkv
    · rw [m₂, m₁]; exact Frame.refl _ _
    · rw [o₂ r (fun h => h1 (by subst h; decide)), o₁ r h2]
  refine WP.mono (keyLoop_wp (e₀ := 0) (N := 8 * g + 2) (wk := id) (f := fun x => x + BitVec.ofNat 64 8)
    (fun s => addI_ok s .x0 .x0 (imm := 8) (by decide)) (by omega_arith) (fun k hk => by simp; omega_arith)
    (fun k _ => add8 sched) (fun k _ => by simp) (by omega_arith) hinv) fun s h => ?_
  exact ⟨h.pre, fun i hi => h.ent i (by omega_arith), h.masks, h.frame, fun r h1 h2 h3 _ => h.regs r h1 h2 h3, h.rd, h.wr⟩

/-- `keyOne_step` within the construction of a table from `s₀`. -/
theorem keyOne_inv {s₀ s : State} {b sched : Addr} {d e w : Nat} (hd : d = 0 ∨ d = 8)
    (hk : KeyPre s b sched) (hkp : s.gpr kp = b + BitVec.ofNat 64 (8 * keySlot + 64 * e)) (he : e < 34)
    (hx0 : s.gpr .x0 = sched + BitVec.ofNat 64 (8 * w)) (hw : w + d / 8 < 34) (hm : MasksOk s)
    (hf : Frame [⟨b, 8 * endSlot⟩] s₀.mem s.mem) :
    ∃ s', runBlock isa (keyOne d) s = some s' ∧ KeyPre s' b sched ∧
      s'.gpr kp = b + BitVec.ofNat 64 (8 * keySlot + 64 * (e + 1)) ∧
      (∀ r, r ∉ layerWrites → r ≠ kp → s'.gpr r = s.gpr r) ∧ s'.gpr t1 = s.gpr t1 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ MasksOk s' ∧ Frame [⟨b, 8 * endSlot⟩] s₀.mem s'.mem ∧
      EntryOk s'.mem b e (Spec.Camellia.wordAt s₀.mem (sched + BitVec.ofNat 64 (8 * (w + d / 8)))) ∧
      (∀ i < 34, i ≠ e → ∀ j < 8, entryW s'.mem b i j = entryW s.mem b i j) := by
  obtain ⟨s', e', k', o', t', rd', wr', m', f', E'⟩ := keyOne_step hd hk.base hk.scr hkp he
    (fun j hj => by rw [hx0]; exact hk.word (by omega_arith))
    (fun l hl j hj => by rw [hx0]; exact hk.wsep (by omega_arith) (by rw [slots_eq, keySlot_eq] at *; omega_arith)) hm
  refine ⟨s', e', hk.congr (o' _ (by decide) (by decide)) rd' wr', ?_, o', t', rd', wr', m', ?_, ?_,
    fun i hi hie j hj => entryW_frame f' hi he hie hj⟩
  · rw [k', hkp, addr_add, show 8 * keySlot + 64 * e + 64 = 8 * keySlot + 64 * (e + 1) by omega_arith]
  · refine hf.trans (f'.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Region.sub_prefix (by rw [keySlot_eq, endSlot_eq]; omega_arith)
    · exact VG.Offset.sub_base b (by rw [keySlot_eq, endSlot_eq]; omega_arith)
  · have hw' : Spec.Camellia.wordAt s.mem (s.gpr .x0 + BitVec.ofNat 64 d) =
        Spec.Camellia.wordAt s₀.mem (sched + BitVec.ofNat 64 (8 * (w + d / 8))) := by
      rw [hx0, addr_add, show 8 * w + d = 8 * (w + d / 8) by omega_arith]
      exact hk.wordAt_eq (by rw [endSlot_eq, slots_eq]; decide) hf hw
    rw [← hw']; exact E'

theorem decKeys_wp {s₀ : State} {b sched : Addr} {g : Nat} (hg : g = 3 ∨ g = 4) (hk : KeyPre s₀ b sched)
    (hx0 : s₀.gpr .x0 = sched) (hm : MasksOk s₀) :
    WP isa (decKeys g) s₀ (KeysPost s₀ b sched g (Camellia.decPerm g)) := by
  have hg4 : g ≤ 4 := by omega_arith
  have hg3 : 3 ≤ g := by omega_arith
  unfold decKeys
  -- `kw3`, `kw4` to entries 0 and 1.
  obtain ⟨s₁, e₁, k₁, o₁, m₁, rd₁, wr₁⟩ := setKp_ok s₀
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := addI_ok s₁ .x0 .x0 (imm := 64 * g) (by omega_arith)
  have hx0₂ : s₂.gpr .x0 = sched + BitVec.ofNat 64 (8 * (8 * g)) := by
    rw [r₂, o₁ _ (by decide), hx0, show 64 * g = 8 * (8 * g) by omega_arith]
  have hk₂ : KeyPre s₂ b sched :=
    hk.congr (by rw [o₂ _ (by decide), o₁ _ (by decide)]) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
  have hm₂ : MasksOk s₂ := fun kv hkv => by
    show s₂.mem.readW (wordAddr (s₂.gpr sb) kv.1) 64 = kv.2
    rw [m₂, m₁, o₂ _ (by decide), o₁ _ (by decide)]; exact hm kv hkv
  have hf₂ : Frame [⟨b, 8 * endSlot⟩] s₀.mem s₂.mem := by rw [m₂, m₁]; exact Frame.refl _ _
  have hkp₂ : s₂.gpr kp = b + BitVec.ofNat 64 (8 * keySlot + 64 * 0) := by
    rw [o₂ _ (by decide), k₁, hk.base]; simp
  obtain ⟨s₃, e₃, hk₃, kp₃, o₃, t₃, rd₃, wr₃, hm₃, hf₃, E₃, -⟩ :=
    keyOne_inv (d := 0) (Or.inl rfl) hk₂ hkp₂ (by omega_arith) hx0₂ (by omega_arith) hm₂ hf₂
  obtain ⟨s₄, e₄, hk₄, kp₄, o₄, t₄, rd₄, wr₄, hm₄, hf₄, E₄, P₄⟩ :=
    keyOne_inv (d := 8) (Or.inr rfl) hk₃ kp₃ (by omega_arith) (by rw [o₃ _ (by decide) (by decide), hx0₂])
      (by omega_arith) hm₃ hf₃
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := subI_ok s₄ .x0 .x0 (imm := 8) (by decide)
  obtain ⟨s₆, e₆, t₆, o₆, m₆, rd₆, wr₆⟩ := movz_ok s₅ t1 (v := 8 * g - 2) (by omega_arith)
  have hx0₆ : s₆.gpr .x0 = sched + BitVec.ofNat 64 (8 * (8 * g - 1)) := by
    rw [o₆ _ (by decide), r₅, o₄ _ (by decide) (by decide), o₃ _ (by decide) (by decide), hx0₂]
    have := sub8 sched (w := 8 * g - 1)
    rwa [show 8 * g - 1 + 1 = 8 * g by omega_arith] at this
  refine WP.seq (WP.of_runBlock ⟨s₆, by
    rw [runBlock_append', runBlock_append', runBlock_append', runBlock_append', e₁, Option.bind_some,
      e₂, Option.bind_some, e₃, Option.bind_some, e₄, Option.bind_some,
      show ([Instr.subImm .x .x0 .x0 8, .movz .x t1 (BitVec.ofNat 16 (8 * g - 2)) 0] : List Instr) =
        [.subImm .x .x0 .x0 8] ++ [.movz .x t1 (BitVec.ofNat 16 (8 * g - 2)) 0] from rfl,
      runBlock_append', e₅, Option.bind_some, e₆], ?_⟩)
  -- The loop: entries 2 to `8 g - 1`.
  let F : Nat → BitVec 64 := fun i =>
    Spec.Camellia.wordAt s₀.mem (sched + BitVec.ofNat 64 (8 * Camellia.decPerm g i))
  have hF0 : F 0 = Spec.Camellia.wordAt s₀.mem (sched + BitVec.ofNat 64 (8 * (8 * g + 0 / 8))) := by
    simp [F, Camellia.decPerm]
  have hF1 : F 1 = Spec.Camellia.wordAt s₀.mem (sched + BitVec.ofNat 64 (8 * (8 * g + 8 / 8))) := by
    simp [F, Camellia.decPerm]
  have hinv : KeyInv s₀ b sched 2 (8 * g - 2) (fun k => 8 * g - 1 - k) F 0 s₆ := by
    refine ⟨hk₄.congr ?_ ?_ ?_, ?_, by rw [hx0₆, Nat.sub_zero], by rw [t₆, Nat.sub_zero], fun i hi => ?_,
      fun kv hkv => ?_, by rw [m₆, m₅]; exact hf₄, fun r h1 h2 h3 => ?_, by rw [rd₆, rd₅, rd₄, rd₃, rd₂, rd₁],
      by rw [wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]⟩
    · rw [o₆ _ (by decide), o₅ _ (by decide)]
    · rw [rd₆, rd₅]
    · rw [wr₆, wr₅]
    · rw [o₆ _ (by decide), o₅ _ (by decide), kp₄]
    · have hmem : s₆.mem = s₄.mem := by rw [m₆, m₅]
      rw [hmem]
      rcases (show i = 0 ∨ i = 1 by omega_arith) with rfl | rfl
      · rw [hF0]; exact E₃.congr fun j hj => P₄ 0 (by omega_arith) (by omega_arith) j hj
      · rw [hF1]; exact E₄
    · show s₆.mem.readW (wordAddr (s₆.gpr sb) kv.1) 64 = kv.2
      rw [m₆, m₅, o₆ _ (by decide), o₅ _ (by decide)]; exact hm₄ kv hkv
    · rw [o₆ r (fun h => h1 (by subst h; decide)), o₅ r h3, o₄ r h1 h2, o₃ r h1 h2, o₂ r h3, o₁ r h2]
  refine WP.seq (WP.mono (keyLoop_wp (e₀ := 2) (N := 8 * g - 2) (wk := fun k => 8 * g - 1 - k)
    (f := fun x => x - BitVec.ofNat 64 8) (fun s => subI_ok s .x0 .x0 (imm := 8) (by decide)) (by omega_arith)
    (fun k hk => by omega_arith) (fun k hk => ?_) (fun k hk => ?_) (by omega_arith) hinv) fun s h => ?_)
  · have := sub8 sched (w := 8 * g - 1 - (k + 1))
    rwa [show 8 * g - 1 - (k + 1) + 1 = 8 * g - 1 - k by omega_arith] at this
  · simp only [F, Camellia.decPerm, show ¬ 2 + k < 2 by omega_arith, show 2 + k < 8 * g by omega_arith, ↓reduceIte,
      show 8 * g + 1 - (2 + k) = 8 * g - 1 - k by omega_arith]
  -- `kw1`, `kw2` to entries `8 g` and `8 g + 1`.
  have hk₇ := h.pre
  obtain ⟨s₇, e₇, r₇, o₇, m₇, rd₇, wr₇⟩ := subI_ok s .x0 .x0 (imm := 8) (by decide)
  have hx0₇ : s₇.gpr .x0 = sched + BitVec.ofNat 64 (8 * 0) := by
    rw [r₇, h.x0, show 8 * g - 1 - (8 * g - 2) = 0 + 1 by omega_arith, sub8]
  have hk₇' : KeyPre s₇ b sched := hk₇.congr (o₇ _ (by decide)) rd₇ wr₇
  have hm₇ : MasksOk s₇ := fun kv hkv => by
    show s₇.mem.readW (wordAddr (s₇.gpr sb) kv.1) 64 = kv.2
    rw [m₇, o₇ _ (by decide)]; exact h.masks kv hkv
  have hkp₇ : s₇.gpr kp = b + BitVec.ofNat 64 (8 * keySlot + 64 * (8 * g)) := by
    rw [o₇ _ (by decide), h.kpos, show 2 + (8 * g - 2) = 8 * g by omega_arith]
  obtain ⟨s₈, e₈, hk₈, kp₈, o₈, -, rd₈, wr₈, hm₈, hf₈, E₈, P₈⟩ :=
    keyOne_inv (s₀ := s₀) (d := 0) (Or.inl rfl) hk₇' hkp₇ (by omega_arith) hx0₇ (by omega_arith) hm₇
      (by rw [m₇]; exact h.frame)
  obtain ⟨s₉, e₉, hk₉, -, o₉, -, rd₉, wr₉, hm₉, hf₉, E₉, P₉⟩ :=
    keyOne_inv (s₀ := s₀) (d := 8) (Or.inr rfl) hk₈ kp₈ (by omega_arith) (by rw [o₈ _ (by decide) (by decide), hx0₇])
      (by omega_arith) hm₈ hf₈
  refine WP.of_runBlock ⟨s₉, by
    rw [runBlock_append', runBlock_append', e₇, Option.bind_some, e₈, Option.bind_some, e₉],
    hk₉, fun i hi => ?_, hm₉, hf₉, fun r h1 h2 h3 _ => ?_, by rw [rd₉, rd₈, rd₇, h.rd],
    by rw [wr₉, wr₈, wr₇, h.wr]⟩
  · rcases (show i < 8 * g ∨ i = 8 * g ∨ i = 8 * g + 1 by omega_arith) with hi' | rfl | rfl
    · refine (h.ent i (by omega_arith)).congr fun j hj => ?_
      rw [P₉ i (by omega_arith) (by omega_arith) j hj, P₈ i (by omega_arith) (by omega_arith) j hj, m₇]
    · have hp : Camellia.decPerm g (8 * g) = 0 + 0 / 8 := by
        unfold Camellia.decPerm
        simp only [show ¬ 8 * g < 2 by omega_arith, show ¬ 8 * g < 8 * g by omega_arith, ↓reduceIte]; omega_arith
      rw [hp]; exact E₈.congr fun j hj => P₉ _ (by omega_arith) (by omega_arith) j hj
    · have hp : Camellia.decPerm g (8 * g + 1) = 0 + 8 / 8 := by
        unfold Camellia.decPerm
        simp only [show ¬ 8 * g + 1 < 2 by omega_arith, show ¬ 8 * g + 1 < 8 * g by omega_arith, ↓reduceIte]; omega_arith
      rw [hp]; exact E₉
  · rw [o₉ r h1 h2, o₈ r h1 h2, o₇ r h3, h.regs r h1 h2 h3]

end VG.Proof.Camellia.AArch64

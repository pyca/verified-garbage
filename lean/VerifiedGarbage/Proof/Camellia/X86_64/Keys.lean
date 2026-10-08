import VerifiedGarbage.Proof.Camellia.X86_64.Crypt8
import VerifiedGarbage.Proof.Camellia.X86_64.KeyChecks

/-!
# The table of bitsliced subkeys on x86-64

`keyOne_step`: `keyOne d` bitslices the subkey at `[rdi + d]` (its eight
bytes, the most significant first: `wordAt`) into the table's entry at
`rsi`, every block's copy of it alike, and steps `rsi` to the next entry.
`encKeys_wp` and `decKeys_wp` build the table in the order the rounds use
the subkeys: for encryption the stored order, for decryption `decPerm`'s.
-/

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Camellia.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR at_ slotAt)
open VG.Proof.Camellia (HalfRel WordRel pos)

/-- Byte `i` of a word read most significant byte first is the byte at `i`. -/
theorem byteOf_wordAt (m : Mem) (a : Addr) {i : Nat} (hi : i < 8) :
    Camellia.byteOf (Spec.Camellia.wordAt m a) i = m (a + BitVec.ofNat 64 i) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [Camellia.getLsbD_byteOf _ hi hj, Spec.Camellia.wordAt,
    Camellia.getLsbD_ofBytes 64 _ (by omega) (by simp [Spec.Camellia.bytesAt])]
  simp only [Spec.Camellia.bytesAt, List.length_map, List.length_range]
  rw [show 8 - 1 - (56 - 8 * i + j) / 8 = i by omega, show (56 - 8 * i + j) % 8 = j by omega]
  simp [hi]

/-- The subkey's word, little-endian, read as the halves are. -/
theorem wordRel_key (m : Mem) (a : Addr) :
    WordRel (fun _ => m.readW a 64) (fun _ => Spec.Camellia.wordAt m a) := fun _ _ i hi j hj => by
  rw [readW64_bit m a hi hj, byteOf_wordAt m a hi]

/-- The table's entry `e` holds `k` for every block. -/
abbrev EntryOk (m : Mem) (b : Addr) (e : Nat) (k : BitVec 64) : Prop := HalfRel (entryW m b e) fun _ => k

theorem keyOne_step {s : State} {b : Addr} {d e : Nat} (hd : d = 0 ∨ d = 8)
    (hb : s.gpr sb = b) (hscr : (⟨b, 8 * slots⟩ : Region) ∈ s.wr)
    (hrsi : s.gpr kp = b + BitVec.ofNat 64 (8 * keySlot + 64 * e)) (he : e < 34)
    (hrdi : ∀ k < d / 8 + 1, InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .rdi) k) 8)
    (hsep : ∀ k < keySlot, ∀ j < d / 8 + 1, Mem.Sep (wordAddr b k) 8 (wordAddr (s.gpr .rdi) j) 8)
    (hm : MasksOk s) :
    ∃ s', runBlock isa (keyOne d) s = some s' ∧
      s'.gpr kp = s.gpr kp + BitVec.ofNat 64 64 ∧ (∀ r, r ∉ sboxWrites → r ≠ kp → s'.gpr r = s.gpr r) ∧
      s'.gpr t1 = s.gpr t1 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ MasksOk s' ∧
      Frame [⟨b, 8 * keySlot⟩, ⟨b + BitVec.ofNat 64 (8 * keySlot + 64 * e), 64⟩] s.mem s'.mem ∧
      EntryOk s'.mem b e (Spec.Camellia.wordAt s.mem (s.gpr .rdi + BitVec.ofNat 64 d)) := by
  rw [slots_eq] at hscr
  have hok : Ok (keyCfg (d / 8 + 1)) s :=
    { slotIn := fun k hk => ⟨_, hscr, by
        simp only [keyCfg, keySlot_eq] at hk ⊢
        rw [hb]; exact VG.Offset.contains_base b (by omega) (by omega)⟩
      extIn := fun k hk => hrdi k (by simpa [keyCfg] using hk)
      slots := by simp [keyCfg, keySlot_eq]
      sep := fun k hk j hj => by
        simp only [keyCfg] at hk hj ⊢; rw [hb]; exact hsep k hk j hj }
  have hchk : check (lanes 64 7) (keyCfg (d / 8 + 1)) (linExt 0) (keyLoad d) keyEnv
      (linPostG 7 (qOuts (keyBsG d)) [] maskSlots keyEnv) = true := by
    rcases hd with rfl | rfl
    · exact keyLoad0_check
    · exact keyLoad8_check
  unfold keyEnv at hchk
  obtain ⟨s₁, e₁, ho₁, -, hkp₁, rd₁, wr₁, o₁, f₁, hb₁, -⟩ := linG_ok hchk hok
    (fun k => s.mem.readW (wordAddr (s.gpr .rdi) k) 64)
    (fun r i hri => by simp at hri) (fun j i hji => by simp at hji)
    (fun kv hkv => ⟨by simp only [keyCfg]; exact mask_lt hkv, by
      simp only [keyCfg]; exact hm kv hkv⟩)
    (fun j hj => ⟨by simp only [keyCfg] at hj; omega, by simp only [keyCfg, Nat.zero_add]⟩)
  simp only [keyCfg] at hb₁ hkp₁ f₁
  have hall₁ : ∀ r, r ∉ sboxWrites → ((keyLoad d).all fun i => i.dst != some r) = true := fun r hr => by
    have h := not_sboxWrites r hr
    have : ([Reg.rdx, .rsp, .rsi, .rdi, .r8, .r9].all fun r => (keyLoad d).all fun i => i.dst != some r) =
        true := by rcases hd with rfl | rfl <;> decide +kernel
    exact List.all_eq_true.mp this r h
  have k₁ : ∀ r, r ∉ sboxWrites → s₁.gpr r = s.gpr r := fun r hr => o₁ r (hall₁ r hr)
  -- The planes of the subkey.
  have hQ : HalfRel (Qs s₁) (fun _ => Spec.Camellia.wordAt s.mem (s.gpr .rdi + BitVec.ofNat 64 d)) := by
    have hw := wordRel_key s.mem (s.gpr .rdi + BitVec.ofNat 64 d)
    refine Camellia.half_of_words (W := fun _ => s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 d) 64)
      (fun j hj p hp => ?_) hw
    have := Camellia.pos_lt (show p / 8 < 8 by omega)
    rw [Qs, ho₁ (q j) (keyBsG d j) (by simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
      p hp, keyBsG, xorBits_cons, xorBits_nil, Bool.xor_false, Nat.add_assoc, bitOf_word _ _ _ (by omega)]
    rcases hd with rfl | rfl <;> rfl
  -- The stores.
  have hrsi₁ : s₁.gpr .rsi = s.gpr .rsi := k₁ .rsi (by decide)
  have hok₂ : Ok entryCfg s₁ :=
    { slotIn := fun k hk => ⟨_, by rw [wr₁]; exact hscr, by
        simp only [entryCfg] at hk ⊢
        rw [hrsi₁, show s.gpr .rsi = _ from hrsi, wordAddr, addr_add]
        exact VG.Offset.contains_base b (by rw [keySlot_eq]; omega) (by rw [keySlot_eq]; omega)⟩
      extIn := fun k hk => by simp [entryCfg] at hk
      slots := by simp [entryCfg]
      sep := fun k _ j hj => by simp [entryCfg] at hj }
  have hchk₂ := keyStore_check
  unfold entryEnv at hchk₂
  obtain ⟨s₂, e₂, -, hso₂, -, rd₂, wr₂, o₂, f₂, hb₂, -⟩ := linG_ok hchk₂ hok₂ (Qs s₁)
    (fun r i hri => by
      simp only [qIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hri
      obtain ⟨i, hi, rfl, rfl⟩ := hri
      exact ⟨by omega, rfl⟩)
    (fun j i hji => by simp at hji) (fun kv hkv => by simp at hkv)
    (fun j hj => by simp [entryCfg] at hj)
  simp only [entryCfg] at hb₂ hso₂ f₂
  have hall₂ : ∀ r, (keyStore.all fun i => i.dst != some r) = true := fun r => by
    simp [keyStore, Instr.dst]
  have k₂ : ∀ r, s₂.gpr r = s₁.gpr r := fun r => o₂ r (hall₂ r)
  obtain ⟨s₃, e₃, kp₃, o₃, m₃, rd₃, wr₃⟩ := addKp_ok s₂ 64 (by decide)
  have he₂ : ∀ j < 8, entryW s₂.mem b e j = Qs s₁ j := fun j hj => BitVec.eq_of_getLsbD_eq fun p hp => by
    have h := hso₂ j (fun p => [64 * j + p]) (by simp only [List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩)
      hj p hp
    rw [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf_word _ _ _ hp] at h
    rw [← h, entryW, wordAddr, hrsi₁, show s.gpr .rsi = _ from hrsi, addr_add]
  have ht1 : s₁.gpr t1 = s.gpr t1 := o₁ t1 (by rcases hd with rfl | rfl <;> decide +kernel)
  refine ⟨s₃, ?_, ?_, fun r h1 h2 => ?_, by rw [o₃ t1 (by decide), k₂, ht1], by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁], fun kv hkv => ?_,
    ?_, ?_⟩
  · rw [keyOne_eq, runBlock_append', runBlock_append', e₁, Option.bind_some, e₂, Option.bind_some]
    exact e₃
  · rw [kp₃, show s₂.gpr kp = s₁.gpr kp from k₂ _, show s₁.gpr kp = s.gpr kp from hrsi₁]
  · rw [o₃ r h2, k₂, k₁ r h1]
  · have hk : kv.1 < keySlot := mask_lt hkv
    show s₃.mem.readW (wordAddr (s₃.gpr sb) kv.1) 64 = kv.2
    have h2 : s₂.mem.readW (wordAddr (s.gpr sb) kv.1) 64 = s₁.mem.readW (wordAddr (s.gpr sb) kv.1) 64 := by
      refine f₂.readW (r := ⟨wordAddr (s.gpr sb) kv.1, 8⟩) (Region.contains_self _ _) (fun r hr => ?_)
        (by decide)
      simp only [slotRegion, List.mem_singleton] at hr; subst hr
      rw [hrsi₁, show s.gpr .rsi = _ from hrsi, hb, wordAddr]
      exact VG.Offset.disjoint b (Or.inl (by rw [keySlot_eq] at hk ⊢; omega)) (by rw [keySlot_eq] at hk; omega)
        (by rw [keySlot_eq]; omega)
    rw [m₃, o₃ sb (by decide), k₂, hb₁, h2, hkp₁ kv.1 (List.mem_map_of_mem hkv) hk]
    exact hm kv hkv
  · rw [m₃]
    refine (f₁.mono fun r hr => ?_).trans (f₂.mono fun r hr => ?_)
    · simp only [slotRegion, List.mem_singleton] at hr; subst hr; simp [hb]
    · simp only [slotRegion, List.mem_singleton] at hr; subst hr
      simp [hrsi₁, show s.gpr .rsi = _ from hrsi]
  · refine hQ.congr fun j hj => ?_
    show entryW s₃.mem b e j = _
    rw [m₃]; exact he₂ j hj

end VG.Proof.Camellia.X86_64

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Camellia.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR)

/-! ## Steps of the pointers and the counter -/

theorem addImm_ok (s : State) (r : Reg) (v : BitVec 32) :
    ∃ s', runBlock isa [.alu .add r (.imm v)] s = some s' ∧
      s'.gpr r = s.gpr r + v.signExtend 64 ∧ (∀ r', r' ≠ r → s'.gpr r' = s.gpr r') ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some]; rfl, ?_, fun r' hr => ?_, by rfl, by rfl, by rfl⟩
  · simp only [RegUpd.gpr_setReg_self]
  · simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

theorem subImm_ok (s : State) (r : Reg) (v : BitVec 32) :
    ∃ s', runBlock isa [.alu .sub r (.imm v)] s = some s' ∧
      s'.gpr r = s.gpr r - v.signExtend 64 ∧ s'.zf = some (s.gpr r - v.signExtend 64 == 0) ∧
      (∀ r', r' ≠ r → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some]; rfl, ?_, by rfl, fun r' hr => ?_, by rfl, by rfl, by rfl⟩
  · simp only [RegUpd.gpr_setReg_self]
  · simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]


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
  ⟨_, h.sch, by rw [wordAddr, addr_add]; exact VG.Offset.contains_base sched (by omega) (by omega)⟩

theorem KeyPre.wsep {s : State} {b sched : Addr} (h : KeyPre s b sched) {w j : Nat} (hw : w + j < 34)
    {k : Nat} (hk : k < slots) :
    Mem.Sep (wordAddr b k) 8 (wordAddr (sched + BitVec.ofNat 64 (8 * w)) j) 8 := by
  have hf := h.fit
  rw [slots_eq] at hf hk
  refine h.sep.symm.sep (VG.Offset.contains_base b (by rw [slots_eq]; omega) (by omega)) ?_
  rw [wordAddr, addr_add]; exact VG.Offset.contains_base sched (by omega) (by omega)

/-- A word of a region the frame keeps. -/
theorem wordAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {a : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨a, 8⟩ r) : Spec.Camellia.wordAt m' a = Spec.Camellia.wordAt m a := by
  simp only [Spec.Camellia.wordAt, Spec.Camellia.bytesAt]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  exact hf.bytes (R := ⟨a, 8⟩) hd (by show (8 : Nat) ≤ 2 ^ 64; decide) (by simpa using hi)

/-- The schedule is outside the scratch buffer. -/
theorem KeyPre.wordAt_eq {s : State} {b sched : Addr} (h : KeyPre s b sched) {m m' : Mem} {n : Nat}
    (hn : n ≤ slots) (hf : Frame [⟨b, 8 * n⟩] m m') {w : Nat} (hw : w < 34) :
    Spec.Camellia.wordAt m' (sched + BitVec.ofNat 64 (8 * w)) =
      Spec.Camellia.wordAt m (sched + BitVec.ofNat 64 (8 * w)) := by
  refine wordAt_frame hf fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact (h.sep.sub_left (VG.Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix (by omega))

/-- An entry outside a frame keeps its planes. -/
theorem entryW_frame {m m' : Mem} {b : Addr} {e i : Nat}
    (hf : Frame [⟨b, 8 * keySlot⟩, ⟨b + BitVec.ofNat 64 (8 * keySlot + 64 * e), 64⟩] m m')
    (hi : i < 34) (he : e < 34) (hie : i ≠ e) {j : Nat} (hj : j < 8) : entryW m' b i j = entryW m b i j := by
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact VG.Offset.disjoint_base b (by rw [keySlot_eq]; omega) (by rw [keySlot_eq]; omega)
  · exact VG.Offset.disjoint b (by rw [keySlot_eq]; omega) (by rw [keySlot_eq]; omega)
      (by rw [keySlot_eq]; omega)

/-- What the loops keep, after `k` of their `N` iterations: the subkeys `F`
in the entries before `e₀ + k`, `rdi` at word `wk k` of the schedule. -/
structure KeyInv (s₀ : State) (b sched : Addr) (e₀ N : Nat) (wk : Nat → Nat) (F : Nat → BitVec 64)
    (k : Nat) (s : State) : Prop where
  pre : KeyPre s b sched
  rsi : s.gpr kp = b + BitVec.ofNat 64 (8 * keySlot + 64 * (e₀ + k))
  rdi : s.gpr .rdi = sched + BitVec.ofNat 64 (8 * wk k)
  cnt : s.gpr t1 = BitVec.ofNat 64 (N - k)
  ent : ∀ i < e₀ + k, EntryOk s.mem b i (F i)
  masks : MasksOk s
  frame : Frame [⟨b, 8 * endSlot⟩] s₀.mem s.mem
  regs : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .rdi → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The loop of `keyOne 0` and `op rdi, 8` (`f` on `rdi`), counted down in `t1`. -/
theorem keyLoop_wp {s₀ s : State} {b sched : Addr} {e₀ N : Nat} {wk : Nat → Nat} {F : Nat → BitVec 64}
    {op : AluOp} {f : Addr → Addr}
    (hop : ∀ s : State, ∃ s', runBlock isa [.alu op .rdi (.imm 8)] s = some s' ∧
      s'.gpr .rdi = f (s.gpr .rdi) ∧ (∀ r, r ≠ .rdi → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr)
    (hN : e₀ + N ≤ 34) (hNw : N < 2 ^ 32)
    (hwk : ∀ k < N, wk k < 34)
    (hstep : ∀ k < N, f (sched + BitVec.ofNat 64 (8 * wk k)) = sched + BitVec.ofNat 64 (8 * wk (k + 1)))
    (hF : ∀ k < N, F (e₀ + k) = Spec.Camellia.wordAt s₀.mem (sched + BitVec.ofNat 64 (8 * wk k)))
    {k : Nat} (hk : k < N) (hs : KeyInv s₀ b sched e₀ N wk F k s) :
    WP isa (.loop (.block (keyOne 0 ++ [.alu op .rdi (.imm 8), .alu .sub t1 (.imm 1)])) .ne) s
      (KeyInv s₀ b sched e₀ N wk F N) := by
  refine WP.loop (M := isa) (fun n s => ∃ k, n = N - k ∧ k < N ∧ KeyInv s₀ b sched e₀ N wk F k s)
    (fun n s hs => ?_) (N - k) s ⟨k, rfl, hk, hs⟩
  obtain ⟨k, rfl, hk, hi⟩ := hs
  have hfit := hi.pre.fit
  have hw := hwk k hk
  have hrdi := hi.rdi
  obtain ⟨s₁, e₁, kp₁, o₁, t₁, rd₁, wr₁, m₁, f₁, E₁⟩ := keyOne_step (d := 0) (e := e₀ + k) (Or.inl rfl)
    hi.pre.base hi.pre.scr hi.rsi (by omega)
    (fun j hj => by rw [hrdi]; exact hi.pre.word (by omega))
    (fun j hj l hl => by rw [hrdi]; exact hi.pre.wsep (by omega) (by rw [slots_eq, keySlot_eq] at *; omega))
    hi.masks
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := hop s₁
  obtain ⟨s₃, e₃, c₃, z₃, o₃, m₃, rd₃, wr₃⟩ := subImm_ok s₂ t1 1
  refine WP.of_runBlock ⟨s₃, by
    rw [runBlock_append', e₁, Option.bind_some,
      show ([Instr.alu op .rdi (.imm 8), .alu .sub t1 (.imm 1)] : List Instr) =
        [.alu op .rdi (.imm 8)] ++ [.alu .sub t1 (.imm 1)] from rfl,
      runBlock_append', e₂, Option.bind_some, e₃], ?_⟩
  have ht₂ : s₂.gpr t1 = BitVec.ofNat 64 (N - k) := by rw [o₂ _ (by decide), t₁, hi.cnt]
  have hc₃ : s₃.gpr t1 = BitVec.ofNat 64 (N - (k + 1)) := by
    rw [c₃, ht₂, show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
      VG.Offset.ofNat_sub_ofNat (by omega), show N - k - 1 = N - (k + 1) by omega]
  -- The new invariant.
  have hf₁₃ : Frame [⟨b, 8 * keySlot⟩, ⟨b + BitVec.ofNat 64 (8 * keySlot + 64 * (e₀ + k)), 64⟩] s.mem s₃.mem := by
    rw [m₃, m₂]; exact f₁
  have hinv : KeyInv s₀ b sched e₀ N wk F (k + 1) s₃ := by
    refine ⟨hi.pre.congr ?_ ?_ ?_, ?_, ?_, hc₃, fun i hi' => ?_, fun kv hkv => ?_, ?_, fun r h1 h2 h3 => ?_,
      by rw [rd₃, rd₂, rd₁, hi.rd], by rw [wr₃, wr₂, wr₁, hi.wr]⟩
    · rw [o₃ _ (by decide), o₂ _ (by decide), o₁ _ (by decide) (by decide)]
    · rw [rd₃, rd₂, rd₁]
    · rw [wr₃, wr₂, wr₁]
    · rw [o₃ _ (by decide), o₂ _ (by decide), kp₁, hi.rsi, addr_add,
        show 8 * keySlot + 64 * (e₀ + k) + 64 = 8 * keySlot + 64 * (e₀ + (k + 1)) by omega]
    · rw [o₃ _ (by decide), r₂, o₁ _ (by decide) (by decide), hrdi, hstep k hk]
    · by_cases he : i = e₀ + k
      · subst he
        have hw' : Spec.Camellia.wordAt s.mem (s.gpr .rdi + BitVec.ofNat 64 0) = F (e₀ + k) := by
          rw [hrdi, addr_add, Nat.add_zero, hF k hk]
          exact hi.pre.wordAt_eq (by rw [endSlot_eq, slots_eq]; decide) hi.frame hw
        rw [← hw']
        exact E₁.congr fun j _ => by
          show entryW s₃.mem b (e₀ + k) j = entryW s₁.mem b (e₀ + k) j
          rw [m₃, m₂]
      · refine (hi.ent i (by omega)).congr fun j hj => ?_
        exact entryW_frame hf₁₃ (by omega) (by omega) he hj
    · show s₃.mem.readW (wordAddr (s₃.gpr sb) kv.1) 64 = kv.2
      rw [m₃, m₂, o₃ _ (by decide), o₂ _ (by decide)]; exact m₁ kv hkv
    · refine hi.frame.trans ((f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
        (by rw [m₃, m₂]; exact Frame.refl _ _))
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Region.sub_prefix (by rw [keySlot_eq, endSlot_eq]; omega)
      · exact VG.Offset.sub_base b (by rw [keySlot_eq, endSlot_eq]; omega)
    · rw [o₃ r (fun h => h1 (by subst h; decide)), o₂ r h3, o₁ r h1 h2, hi.regs r h1 h2 h3]
  have hz : s₃.zf = some (decide (N - (k + 1) = 0)) := by
    rw [z₃, ht₂, show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
      VG.Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]
    simp only [Option.some.injEq, decide_eq_decide]; omega
  by_cases hl : k + 1 = N
  · refine .inl ⟨by simp [X86_64.eval, hz, hl], by rw [show k + 1 = N from hl] at hinv; exact hinv⟩
  · exact .inr ⟨by simp [X86_64.eval, hz]; omega, N - (k + 1), by omega, k + 1, rfl, by omega, hinv⟩

end VG.Proof.Camellia.X86_64

import VerifiedGarbage.Proof.Sm4.AArch64.KeyInit

/-!
# The loop of the SM4 key schedule on AArch64

Each iteration runs four rounds of the key schedule (`rounds4_ok .key`),
puts the state's words in the tail buffer as a block (`fromBs_step`), and
stores them to the schedule as little-endian words (`extract_ok`): the
first block's 64-bit words, byte-reversed (`rev`).
-/

namespace VG.Proof.Sm4.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Sm4.AArch64
open VG.Impl.Aes.AArch64 (q sb t0 t1 movR ldS stS)
open VG.Impl.Sm4 (planeOf fkWord)
open VG.Proof.Sm4 (WordRel quads ofBlock outBlock keyInit rkOf readW64_bit getLsbD_outBlock' ofInt_nat)

/-! ## Bytes -/

theorem rev64_eq (x : BitVec 64) (k : Nat) :
    (rev64 x).getLsbD k = (x.extractLsb' 0 8 ++ x.extractLsb' 8 8 ++ x.extractLsb' 16 8 ++ x.extractLsb' 24 8 ++
      x.extractLsb' 32 8 ++ x.extractLsb' 40 8 ++ x.extractLsb' 48 8 ++ x.extractLsb' 56 8 :
        BitVec (8 + 8 + 8 + 8 + 8 + 8 + 8 + 8)).getLsbD k := rfl

theorem rev64_bit (x : BitVec 64) {t j : Nat} (ht : t < 8) (hj : j < 8) :
    (rev64 x).getLsbD (8 * t + j) = x.getLsbD (8 * (7 - t) + j) := by
  rw [rev64_eq]
  simp only [BitVec.getLsbD_append]
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd, Nat.reduceLT, ↓reduceIte, Nat.lt_irrefl,
    BitVec.getLsbD_extractLsb', decide_true, Bool.true_and]

/-- A byte of a word written. -/
theorem writeW_byte (m : Mem) (a : Addr) (v : BitVec 64) {t j : Nat} (ht : t < 8) (hj : j < 8) :
    ((m.writeW a v) (a + BitVec.ofNat 64 t)).getLsbD j = v.getLsbD (8 * t + j) := by
  simp only [Mem.writeW, Mem.write, BitVec.setWidth_eq, VG.Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  simp only [show t < 64 / 8 by omega, ↓reduceIte, BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]

/-- A byte outside a word written. -/
theorem writeW_other (m : Mem) (a x : Addr) (v : BitVec 64) (h : ¬ (x - a).toNat < 8) :
    (m.writeW a v) x = m x := by
  simp only [Mem.writeW, Mem.write]
  exact ite_eq_right fun h' => h (by simpa using h')

/-- A word written inside `R`. -/
theorem frame_writeW' {m : Mem} {a : Addr} {R : Region} (v : BitVec 64) (hs : Region.Sub ⟨a, 8⟩ R) :
    Frame [R] m (m.writeW a v) := VG.Proof.Sm4.frame_writeW v hs

/-! ## Single instructions -/

theorem bswapR_ok (s : State) (d : Reg) :
    ∃ s', runBlock isa [.rev d d] s = some s' ∧ s'.gpr d = rev64 (s.gpr d) ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.write .x d (rev64 (s.gpr d)), by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x'],
    by simp only [RegUpd.gpr_write_self, BitVec.setWidth_eq], fun r h => RegUpd.gpr_write_of_ne _ _ _ h,
    rfl, rfl, rfl⟩

/-- `str v, [r, #n]`. -/
theorem storeAt_ok (s : State) (r v : Reg) (n : Nat) (hn : n % 8 = 0 ∧ n < 32768)
    (hw : InRegions s.wr (s.gpr r + BitVec.ofNat 64 n) 8) :
    ∃ s', runBlock isa [.str .x v r n] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr r + BitVec.ofNat 64 n) (s.gpr v) ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨{ s with mem := s.mem.writeW (s.gpr r + BitVec.ofNat 64 n) (s.gpr v) }, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_str_x hn hw], rfl, rfl, rfl, rfl⟩

/-- A byte of the tail buffer's block `0`. -/
theorem tail_byte (s : State) {h t j : Nat} (hh : h < 2) (ht : t < 8) (hj : j < 8) :
    (slotW s (tailAt 0 h)).getLsbD (8 * t + j) = ((tailBlock s 0)[8 * h + t]'(by omega)).getLsbD j := by
  rw [slotW, readW64_bit _ _ ht hj]
  simp only [tailBlock, Spec.Sm4.blockAt, Vector.getElem_ofFn, wordAddr, addr_add, tailAt]
  rw [show 8 * (tailSlot + 2 * 0 + h) + t = 8 * tailSlot + 16 * 0 + (8 * h + t) by omega]

/-! ## The extraction -/

/-- The schedule's bytes `16 m … 16 m + 15`: the words of the tail buffer's
first block, the last first, each little-endian. -/
theorem extract_ok {s : State} {b S : Addr} {m : Nat} (hm : m < 8) (hb : s.gpr sb = b)
    (hr8 : s.gpr .x1 = S + BitVec.ofNat 64 (16 * m))
    (hS : ∀ t < 2, InRegions s.wr (S + BitVec.ofNat 64 (16 * m + 8 * t)) 8)
    (hT : ∀ t < 2, InRegions (s.rd ++ s.wr) (wordAddr b (tailAt 0 t)) 8)
    (hsep : ∀ t < 2, Mem.Sep (wordAddr b (tailAt 0 t)) 8 (S + BitVec.ofNat 64 (16 * m)) 8) :
    ∃ s', runBlock isa extract s = some s' ∧
      (∀ t < 16, ∀ j < 8, (s'.mem (S + BitVec.ofNat 64 (16 * m + t))).getLsbD j =
        ((tailBlock s 0)[15 - t]'(by omega)).getLsbD j) ∧
      Frame [⟨S + BitVec.ofNat 64 (16 * m), 16⟩] s.mem s'.mem ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldMask_ok (r := t0) (k := tailAt 0 1) (by simp only [tailAt, tailSlot_eq]; omega)
    (by rw [hb]; exact hT 1 (by decide)) rfl
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂⟩ := bswapR_ok s₁ t0
  obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃⟩ := storeAt_ok s₂ .x1 t0 0 (by decide)
    (by rw [wr₂, wr₁, o₂ _ (by decide), o₁ _ (by decide), hr8, addr_add, Nat.add_zero]
        have := hS 0 (by decide); simpa using this)
  have hb₃ : s₃.gpr sb = b := by rw [g₃, o₂ _ (by decide), o₁ _ (by decide), hb]
  obtain ⟨s₄, e₄, v₄, o₄, m₄, rd₄, wr₄⟩ := ldMask_ok (s := s₃) (r := t0) (k := tailAt 0 0)
    (by simp only [tailAt, tailSlot_eq]; omega) (by rw [rd₃, wr₃, rd₂, wr₂, rd₁, wr₁, hb₃]; exact hT 0 (by decide)) rfl
  obtain ⟨s₅, e₅, v₅, o₅, m₅, rd₅, wr₅⟩ := bswapR_ok s₄ t0
  obtain ⟨s₆, e₆, m₆, g₆, rd₆, wr₆⟩ := storeAt_ok s₅ .x1 t0 8 (by decide)
    (by rw [wr₅, wr₄, wr₃, wr₂, wr₁, o₅ _ (by decide), o₄ _ (by decide), g₃, o₂ _ (by decide), o₁ _ (by decide),
          hr8, addr_add]; exact hS 1 (by decide))
  have hr8₅ : s₅.gpr .x1 = S + BitVec.ofNat 64 (16 * m) := by
    rw [o₅ _ (by decide), o₄ _ (by decide), g₃, o₂ _ (by decide), o₁ _ (by decide), hr8]
  have hr8₂ : s₂.gpr .x1 = S + BitVec.ofNat 64 (16 * m) := by rw [o₂ _ (by decide), o₁ _ (by decide), hr8]
  have q1 : s₂.gpr t0 = rev64 (slotW s (tailAt 0 1)) := by rw [v₂, v₁]
  have q0 : s₅.gpr t0 = rev64 (slotW s (tailAt 0 0)) := by
    rw [v₅, v₄]
    simp only [slotW, m₃, m₂, m₁, hb₃, hb, hr8₂, addr_add, Nat.add_zero]
    rw [Mem.readW_writeW_sep (hsep 0 (by decide)) (by decide)]
  have hm6 : s₆.mem = (s.mem.writeW (S + BitVec.ofNat 64 (16 * m)) (rev64 (slotW s (tailAt 0 1)))).writeW
      (S + BitVec.ofNat 64 (16 * m + 8)) (rev64 (slotW s (tailAt 0 0))) := by
    rw [m₆, m₅, m₄, m₃, m₂, m₁, hr8₅, q0, hr8₂, q1, addr_add, addr_add, Nat.add_zero]
  refine ⟨s₆, ?_, fun t ht j hj => ?_, ?_, fun r hr => ?_, by rw [rd₆, rd₅, rd₄, rd₃, rd₂, rd₁],
    by rw [wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]⟩
  · rw [extract, show ([ldS t0 (tailAt 0 1), .rev t0 t0, .str .x t0 .x1 0, ldS t0 (tailAt 0 0), .rev t0 t0,
        .str .x t0 .x1 8] : List Instr) = [ldS t0 (tailAt 0 1)] ++ ([.rev t0 t0] ++ ([.str .x t0 .x1 0] ++
        ([ldS t0 (tailAt 0 0)] ++ ([.rev t0 t0] ++ [.str .x t0 .x1 8])))) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some,
      runBlock_app, e₄, Option.bind_some, runBlock_app, e₅, Option.bind_some, e₆]
  · rw [hm6]
    by_cases h8 : t < 8
    · rw [writeW_other _ _ _ _ (VG.Proof.Sm4.off_sub_not S (Or.inl (by omega)) (by omega) (by decide) (by omega)),
        ← addr_add, writeW_byte _ _ _ h8 hj, rev64_bit _ h8 hj, tail_byte s (by decide) (by omega) hj]
      simp only [show 8 * 1 + (7 - t) = 15 - t by omega]
    · rw [show S + BitVec.ofNat 64 (16 * m + t) = S + BitVec.ofNat 64 (16 * m + 8) + BitVec.ofNat 64 (t - 8) by
          rw [addr_add, show 16 * m + 8 + (t - 8) = 16 * m + t by omega], writeW_byte _ _ _ (by omega) hj,
        rev64_bit _ (by omega) hj, tail_byte s (by decide) (by omega) hj]
      simp only [show 8 * 0 + (7 - (t - 8)) = 15 - t by omega]
  · rw [hm6]
    exact (frame_writeW' _ (VG.Offset.sub S (by omega) (by omega))).trans
      (frame_writeW' _ (VG.Offset.sub S (by omega) (by omega)))
  · rw [g₆, o₅ r hr, o₄ r hr, g₃, o₂ r hr, o₁ r hr]

/-! ## The loop -/

/-- What the loop keeps, after `m` of its eight iterations: the state holds
the key schedule's words after `4 m` rounds, and the schedule its first
`4 m` round keys. -/
structure EkInv (s₀ : State) (b S : Addr) (key : Spec.Sm4.Block) (m : Nat) (s : State) : Prop where
  base : s.gpr sb = b
  x1 : s.gpr .x1 = S + BitVec.ofNat 64 (16 * m)
  x3 : s.gpr .x3 = b + BitVec.ofNat 64 (8 * tableEnd)
  kp : AtEntry s b (4 * m)
  keys : KeyCtx s Spec.Sm4.ck
  masks : MasksOk s
  st : StRel s (fun _ => quads .key Spec.Sm4.ck m (keyInit key))
  sched : ∀ i < 4 * m, ∀ c < 4, ∀ j < 8,
    (s.mem (S + BitVec.ofNat 64 (4 * i + c))).getLsbD j = (rkOf key i).getLsbD (8 * c + j)
  saved : Saved s₀ b s.mem
  frame : Frame [⟨b, 8 * slots⟩, ⟨S, 128⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The scratch buffer and the schedule, writable and apart. -/
structure EkPre (s₀ : State) (b S : Addr) : Prop where
  scr : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr
  sch : (⟨S, 128⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨S, 128⟩ ⟨b, 8 * slots⟩
  fit : b.toNat + 8 * slots ≤ 2 ^ 64
  fitS : S.toNat + 128 ≤ 2 ^ 64

theorem ekIter_ok {s₀ : State} {b S : Addr} {key : Spec.Sm4.Block} (hp : EkPre s₀ b S) {m : Nat} (hm : m < 8)
    {s : State} (hi : EkInv s₀ b S key m s) :
    ∃ s', runBlock isa keyBody s = some s' ∧ EkInv s₀ b S key (m + 1) s' ∧
      (s'.gpr t0 == 0) = decide (m + 1 = 8) := by
  have hfit := hp.fit
  have hfitS := hp.fitS
  rw [slots_eq] at hfit
  have hc0 : Ctx s s := Ctx.refl hi.masks
  -- Four rounds.
  obtain ⟨s₁, e₁, c₁, k₁, X₁⟩ := rounds4_ok .key hi.keys hc0 (by rw [hi.base]; exact hi.kp) hm hi.st
  obtain ⟨s₂, e₂, kp₂, o₂, m₂, rd₂, wr₂⟩ := addKp_ok s₁ 256 (by decide)
  have c₂ : Ctx s s₂ := c₁.kp o₂ m₂ rd₂ wr₂
  have X₂ : StRel s₂ (fun _ => quads .key Spec.Sm4.ck (m + 1) (keyInit key)) :=
    X₁.congr fun k => by simp only [slotW, m₂, o₂ sb (by decide)]
  -- The words to the tail buffer.
  obtain ⟨s₃, e₃, c₃, kp₃, X₃, T₃⟩ := fromBs_step hi.keys c₂ X₂
  have base₃ : s₃.gpr sb = b := by rw [c₃.base, hi.base]
  have r8₃ : s₃.gpr .x1 = S + BitVec.ofNat 64 (16 * m) := by rw [c₃.keep _ (by decide) (by decide), hi.x1]
  have wr₃ : s₃.wr = s₀.wr := by rw [c₃.wr, hi.wr]
  have rd₃ : s₃.rd = s₀.rd := by rw [c₃.rd, hi.rd]
  have inS : ∀ t < 2, InRegions s₃.wr (S + BitVec.ofNat 64 (16 * m + 8 * t)) 8 := fun t ht =>
    ⟨_, by rw [wr₃]; exact hp.sch, VG.Offset.contains_base S (by omega) (by omega)⟩
  have inT : ∀ t < 2, InRegions (s₃.rd ++ s₃.wr) (wordAddr b (tailAt 0 t)) 8 := fun t ht =>
    ⟨_, List.mem_append_right _ (by rw [wr₃]; exact hp.scr), by
      rw [wordAddr]; exact VG.Offset.contains_base b (by rw [tailAt, tailSlot_eq, slots_eq]; omega)
        (by rw [tailAt, tailSlot_eq]; omega)⟩
  have sepTS : ∀ k < slots, Region.Disjoint ⟨wordAddr b k, 8⟩ ⟨S + BitVec.ofNat 64 (16 * m), 16⟩ := fun k hk =>
    (hp.sep.sub_left (VG.Offset.sub_base S (by omega))).sub_right
      (VG.Offset.sub_base b (by rw [slots_eq] at hk ⊢; omega)) |>.symm
  -- To the schedule.
  obtain ⟨s₄, e₄, B₄, f₄, o₄, rd₄, wr₄⟩ := extract_ok hm base₃ r8₃ inS inT
    (fun t ht => fun x h1 h2 => sepTS _ (tailAt_lt (by decide) ht) x h1 (by
      simp only [Region.Contains] at h2 ⊢; omega))
  have keep₄ : ∀ k < slots, slotW s₄ k = slotW s₃ k := fun k hk => by
    simp only [slotW, o₄ sb (by decide), base₃]
    exact f₄.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact sepTS k hk) (by decide)
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := addI_ok s₄ .x1 .x1 (imm := 16) (by decide)
  obtain ⟨s₆, e₆, z₆, g₆, m₆, rd₆, wr₆⟩ := subR_ok s₅ t0 kp .x3
  have mem₆ : s₆.mem = s₄.mem := by rw [m₆, m₅]
  have g₆' : ∀ r, r ≠ .x1 → r ≠ t0 → s₆.gpr r = s₃.gpr r := fun r h1 h2 => by rw [g₆ r h2, o₅ r h1, o₄ r h2]
  have base₆ : s₆.gpr sb = b := by rw [g₆' _ (by decide) (by decide), base₃]
  have keep₆ : ∀ k < slots, slotW s₆ k = slotW s₃ k := fun k hk => by
    rw [← keep₄ k hk]; simp only [slotW, mem₆, g₆' sb (by decide) (by decide), o₄ sb (by decide)]
  have kp₆ : AtEntry s₆ b (4 * (m + 1)) := by
    rw [AtEntry, g₆' _ (by decide) (by decide), kp₃, kp₂, k₁, show s.gpr kp = _ from hi.kp, addr_add,
      show 8 * tableSlot + 64 * (4 * m) + 256 = 8 * tableSlot + 64 * (4 * (m + 1)) by omega]
  have rdi₆ : s₆.gpr .x3 = b + BitVec.ofNat 64 (8 * tableEnd) := by
    rw [g₆' _ (by decide) (by decide), c₃.keep _ (by decide) (by decide), hi.x3]
  have hent : ∀ (st : State) e j, entryW st.mem (st.gpr sb) e j = slotW st (tableSlot + 8 * e + j) := fun st e j => by
    simp only [entryW, slotW, wordAddr]; rw [show 8 * (tableSlot + 8 * e + j) = 8 * tableSlot + 64 * e + 8 * j by omega]
  have key₃ := hi.keys.of_ctx c₃
  -- The schedule's bytes outside this iteration's.
  have old₆ : ∀ x, (∀ r ∈ [(⟨b, 8 * tableSlot⟩ : Region), ⟨S + BitVec.ofNat 64 (16 * m), 16⟩], ¬ r.Contains x 1) →
      s₆.mem x = s.mem x := fun x hx => by
    rw [mem₆, f₄ x (fun r hr => hx r (by simp at hr; simp [hr])),
      c₃.frame x (fun r hr => by simp at hr; subst hr; rw [hi.base]; exact hx _ (by simp))]
  refine ⟨s₆, ?_, ⟨base₆, ?_,
    rdi₆, kp₆, ⟨by rw [base₆, wr₆, wr₅, wr₄, wr₃]; exact hp.scr, by rw [base₆]; rw [slots_eq]; exact hfit,
      fun e he => (key₃.keys e he).congr fun j hj => by
        rw [hent s₆, hent s₃, keep₆ _ (by rw [tableSlot_eq, slots_eq]; omega)]⟩,
    fun kv hkv => by rw [keep₆ _ (by have := mask_lt hkv; rw [slots_eq]; omega)]; exact c₃.masks kv hkv,
    fun w hw => (X₃ w hw).congr fun j hj => keep₆ _ (by simp only [stateSlot, slots_eq]; omega),
    fun i hi' c hc j hj => ?_, fun i hi' => ?_, ?_, by rw [rd₆, rd₅, rd₄, rd₃], by rw [wr₆, wr₅, wr₄, wr₃]⟩, ?_⟩
  · rw [keyBody, runBlock_app, runBlock_app, runBlock_app, runBlock_app, e₁, Option.bind_some,
      e₂, Option.bind_some,
      e₃, Option.bind_some, e₄, Option.bind_some,
      show ([.addImm .x .x1 .x1 16, .sub .x t0 kp .x3] : List Instr) =
        [.addImm .x .x1 .x1 16] ++ [.sub .x t0 kp .x3] from rfl, runBlock_app, e₅, Option.bind_some, e₆]
  · rw [g₆ _ (by decide), r₅, o₄ _ (by decide), r8₃, addr_add, show 16 * m + 16 = 16 * (m + 1) by omega]
  · by_cases hnew : 4 * m ≤ i
    · have ht : 4 * (i - 4 * m) + c < 16 := by omega
      have hB := B₄ _ ht j hj
      rw [show 16 * m + (4 * (i - 4 * m) + c) = 4 * i + c by omega] at hB
      rw [mem₆, hB, T₃ 0 (by decide), getLsbD_outBlock' _ _ hj]
      simp only [rkOf]
      rw [show i / 4 + 1 = m + 1 by omega, show 3 - (15 - (4 * (i - 4 * m) + c)) / 4 = i % 4 by omega,
        show 8 * (3 - (15 - (4 * (i - 4 * m) + c)) % 4) + j = 8 * c + j by omega]
    · rw [old₆ _ (fun r hr => ?_)]
      · exact hi.sched i (by omega) c hc j hj
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · intro hc'
          exact hp.sep (S + BitVec.ofNat 64 (4 * i + c)) (VG.Offset.contains_base S (by omega) (by omega))
            (Region.sub_prefix (show 8 * tableSlot ≤ 8 * slots by rw [tableSlot_eq, slots_eq]; omega) _ hc')
        · exact VG.Proof.Sm4.not_contains_off S (Or.inl (by omega)) (by omega) (by decide) (by omega)
  · have hk : savedSlot + i < slots := by rw [savedSlot_eq, slots_eq]; omega
    have h1 : s₆.mem.readW (wordAddr b (savedSlot + i)) 64 = s₃.mem.readW (wordAddr b (savedSlot + i)) 64 := by
      have := keep₆ _ hk; simp only [slotW, base₆, base₃] at this; exact this
    have h2 : s₃.mem.readW (wordAddr b (savedSlot + i)) 64 = s.mem.readW (wordAddr b (savedSlot + i)) 64 :=
      c₃.frame.readW (r := ⟨wordAddr b (savedSlot + i), 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [hi.base, wordAddr]
        exact VG.Offset.disjoint_base _ (by rw [tableSlot_eq, savedSlot_eq]; omega) (by rw [savedSlot_eq]; omega))
        (by decide)
    rw [h1, h2]; exact hi.saved i hi'
  · rw [mem₆]
    refine hi.frame.trans ((c₃.frame.sub fun r hr => ⟨⟨b, 8 * slots⟩, List.mem_cons_self, ?_⟩).trans
      (f₄.sub fun r hr => ⟨⟨S, 128⟩, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩))
    · simp only [List.mem_singleton] at hr; subst hr; rw [hi.base]
      exact Region.sub_prefix (by rw [tableSlot_eq, slots_eq]; omega)
    · simp only [List.mem_singleton] at hr; subst hr; exact VG.Offset.sub_base S (by omega)
  · rw [z₆, o₅ _ (by decide), o₅ _ (by decide), o₄ _ (by decide), o₄ _ (by decide), kp₃, kp₂, k₁,
      show s.gpr kp = _ from hi.kp, c₃.keep _ (by decide) (by decide), hi.x3, addr_add,
      show 8 * tableSlot + 64 * (4 * m) + 256 = 8 * tableSlot + 64 * (4 * (m + 1)) by omega,
      show 8 * tableEnd = 8 * tableSlot + 64 * 32 by rw [tableSlot_eq, tableEnd_eq],
      entry_beq _ (by rw [tableSlot_eq]; omega) (by rw [tableSlot_eq]; omega)]
    simp only [decide_eq_decide]; omega

end VG.Proof.Sm4.AArch64

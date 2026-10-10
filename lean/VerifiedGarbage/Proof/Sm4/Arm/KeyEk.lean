import VerifiedGarbage.Proof.Sm4.Arm.KeyLoop

/-!
# The SM4 key schedule on ARMv7: the whole function

`expandKey_wp`: with the working space as an argument (`expandKeyArm`),
`expandKey` saves the callee-saved registers, keeps the schedule's pointer
in its slot, stores the table of `CK`'s planes, bitslices eight copies of
`MK ⊕ FK`, runs the loop (`ekIter_ok`) and restores the registers; the
schedule is the specification's `expandKey`.
-/

namespace VG.Proof.Sm4

open VG VG.Arm VG.Impl.Sm4.Arm

/-- The key schedule on ARMv7 with its working space at `r2`. -/
def expandKeyArm : Contract Arm.isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), 16⟩
    let sched : Region := ⟨State.addr (s.gpr .r1), 128⟩
    let scratch : Region := ⟨State.addr (s.gpr .r2), 4 * slots⟩
    s.rd = [key] ∧ s.wr = [sched, scratch] ∧ key.Disjoint sched ∧ key.Disjoint scratch ∧
      sched.Disjoint scratch ∧
      (s.gpr .r0).toNat + 16 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 128 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 4 * slots ≤ 2 ^ 32
  post s s' :=
    Spec.Sm4.scheduleAt s'.mem (State.addr (s.gpr .r1)) =
      Spec.Sm4.expandKey (Spec.Sm4.blockAt s.mem (State.addr (s.gpr .r0)))
  pub s₁ s₂ :=
    s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.sp = s₂.sp

end VG.Proof.Sm4

namespace VG.Proof.Sm4.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Sm4.Arm
open VG.Impl.Aes.Arm (q sb t0 t1 u7 kp movR ldS stS)
open VG.Proof.Sm4 (quads ofBlock outBlock keyInit rkOf getLsbD_outBlock expandKeyArm expandKey_eq)
open VG.Impl.Sm4 (planeOf32 fkLE)

/-! ## The loop -/

/-- What the loop keeps, after `m` of its eight iterations: the state holds
the key schedule's words after `4 m` rounds, and the schedule its first
`4 m` round keys. -/
structure EkInv (s₀ : State) (b S : BitVec 32) (key : Spec.Sm4.Block) (m : Nat) (s : State) : Prop where
  base : s.gpr sb = b
  ptr : s.mem.readW (wordAddr b nSlot) 32 = S + BitVec.ofNat 32 (16 * m)
  kp : AtEntry s b (4 * m)
  keys : KeyCtx s Spec.Sm4.ck
  st : StRel s (fun _ => quads .key Spec.Sm4.ck m (keyInit key))
  sched : ∀ i < 4 * m, ∀ c < 4, ∀ j < 8,
    (s.mem (State.addr S + BitVec.ofNat 64 (4 * i + c))).getLsbD j = (rkOf key i).getLsbD (8 * c + j)
  saved : Saved s₀ b s.mem
  frame : Frame [⟨State.addr b, 4 * slots⟩, ⟨State.addr S, 128⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

/-- The scratch buffer and the schedule, writable and apart. -/
structure EkPre (s₀ : State) (b S : BitVec 32) : Prop where
  scr : ScrIn s₀.wr b
  sch : (⟨State.addr S, 128⟩ : Region) ∈ s₀.wr
  sep : Region.Disjoint ⟨State.addr S, 128⟩ ⟨State.addr b, 4 * slots⟩
  fitS : S.toNat + 128 ≤ 2 ^ 32

theorem ekIter_ok {s₀ : State} {b S : BitVec 32} {key : Spec.Sm4.Block} (hp : EkPre s₀ b S) {m : Nat} (hm : m < 8)
    {s : State} (hi : EkInv s₀ b S key m s) :
    ∃ s', runBlock isa keyBody s = some s' ∧ EkInv s₀ b S key (m + 1) s' ∧ s'.z = decide (m + 1 = 8) := by
  have hfit' := hp.scr.fit
  have hfit : b.toNat + 4 * 364 ≤ 2 ^ 32 := hfit'
  have l₁ := tableSlot_eq
  have l₂ := dSlot_eq
  have l₃ := nSlot_eq
  have l₄ := slots_eq
  have l₅ := savedSlot_eq
  have l₆ := tableEnd_eq
  have hfitS := hp.fitS
  have hSn := addr_toNat S
  have hbn := addr_toNat b
  have hc0 : Ctx s s := Ctx.refl s
  have hwS : ScrIn s.wr b := by rw [hi.wr]; exact hp.scr
  -- Four rounds.
  obtain ⟨s₁, e₁, c₁, k₁, X₁⟩ := rounds4_ok .key hi.keys hc0 (by rw [hi.base]; exact hi.kp) hm hi.st
  obtain ⟨s₂, e₂, kp₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := addImm_ok s₁ kp kp 128 (by decide)
  have c₂ : Ctx s s₂ := c₁.kp o₂ m₂ rd₂ wr₂ sp₂
  have X₂ : StRel s₂ (fun _ => quads .key Spec.Sm4.ck (m + 1) (keyInit key)) :=
    X₁.congr fun k => by simp only [slotW, m₂, o₂ sb (by decide)]
  -- The words to the tail buffer.
  obtain ⟨s₃, e₃, c₃, kp₃, X₃, T₃⟩ := fromBs_step hi.keys c₂ X₂
  have base₃ : s₃.gpr sb = b := by rw [c₃.base, hi.base]
  have hwS₃ : ScrIn s₃.wr b := by rw [c₃.wr]; exact hwS
  -- To the schedule.
  obtain ⟨s₄, e₄, B₄, n₄, f₄, o₄, rd₄, wr₄, sp₄⟩ := extract_ok hm base₃ hwS₃ hfitS
    (by rw [c₃.wr, hi.wr]; exact hp.sch) hp.sep
    (by rw [slot_keep (lo := tableSlot) (hi := slots) hfit' (Nat.le_refl _) c₃.frame (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; rw [hi.base]
          exact VG.Offset.disjoint_base _ (Nat.le_refl _) (by omega))
        (show tableSlot ≤ nSlot by decide) (by decide), hi.ptr])
  obtain ⟨s₅, e₅, z₅, g₅, m₅, rd₅, wr₅, sp₅⟩ := endTest_ok s₄ (BitVec.ofNat 32 (4 * tableEnd)) (by decide)
  have mem₅ : s₅.mem = s₄.mem := m₅
  have g₅' : ∀ r, r ≠ t0 → r ≠ u7 → s₅.gpr r = s₃.gpr r := fun r h0 h7 => by rw [g₅ r h0, o₄ r h0 h7]
  have base₅ : s₅.gpr sb = b := by rw [g₅' _ (by decide) (by decide), base₃]
  have kp₅ : AtEntry s₅ b (4 * (m + 1)) := by
    rw [AtEntry, g₅' _ (by decide) (by decide), kp₃, kp₂, k₁, show s.gpr kp = _ from hi.kp,
      show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl, add_ofNat_ofNat,
      show 4 * tableSlot + 32 * (4 * m) + 128 = 4 * tableSlot + 32 * (4 * (m + 1)) by omega]
  -- What the extraction keeps: everything outside the schedule's new bytes and the pointer's slot.
  have dHi : ∀ r ∈ [(⟨State.addr S + BitVec.ofNat 64 (16 * m), 16⟩ : Region), ⟨wordAddr b nSlot, 4⟩],
      (slotsRegion b 0 dSlot).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hp.sep.sub_left (VG.Offset.sub_base _ (by omega))).sub_right
        (VG.Offset.sub_base _ (by omega)) |>.symm
    · rw [slot_addr (by omega)]
      exact VG.Offset.disjoint _ (by omega) (by omega) (by omega)
  have keep₄ : ∀ k < dSlot, s₄.mem.readW (wordAddr b k) 32 = s₃.mem.readW (wordAddr b k) 32 := fun k hk =>
    slot_keep (lo := 0) (hi := dSlot) hfit' (by decide) f₄ dHi (Nat.zero_le _) hk
  have keepT : ∀ k, tableSlot ≤ k → k < dSlot → s₃.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32 :=
    fun k h1 h2 => slot_keep (lo := tableSlot) (hi := dSlot) hfit' (by decide) c₃.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [hi.base]
      exact VG.Offset.disjoint_base _ (Nat.le_refl _) (by omega)) h1 h2
  have hent : ∀ e < 32, ∀ j < 8, entryW s₅.mem b e j = entryW s.mem b e j := fun e he j hj => by
    simp only [entryW]
    rw [mem₅, keep₄ _ (by rw [tableSlot_eq, dSlot_eq]; omega), keepT _ (by omega) (by rw [tableSlot_eq, dSlot_eq]; omega)]
  refine ⟨s₅, ?_, ⟨base₅, by rw [mem₅]; exact n₄, kp₅,
    ⟨by rw [base₅, wr₅, wr₄, c₃.wr, hi.wr]; exact hp.scr.mem, by rw [base₅]; exact hfit',
      fun e he => by rw [base₅]; exact (hi.keys.keys e he).congr fun j hj => by rw [hi.base] at *; exact hent e he j hj⟩,
    fun w hw => (X₃ w hw).congr fun j hj => ?_, fun i hi' c hc j hj => ?_, fun i hi' => ?_, ?_,
    by rw [rd₅, rd₄, c₃.rd, hi.rd], by rw [wr₅, wr₄, c₃.wr, hi.wr], by rw [sp₅, sp₄, c₃.sp, hi.sp]⟩, ?_⟩
  · rw [keyBody, runBlock_app, runBlock_app, runBlock_app, runBlock_app, e₁, Option.bind_some,
      e₂, Option.bind_some, e₃, Option.bind_some, e₄, Option.bind_some, e₅]
  · show slotW s₅ (stateSlot w j) = slotW s₃ (stateSlot w j)
    rw [slotW, slotW, base₅, base₃, mem₅, keep₄ _ (by simp only [stateSlot, dSlot_eq]; omega)]
  · by_cases hnew : 4 * m ≤ i
    · have ht : 4 * (i - 4 * m) + c < 16 := by omega
      have hB := B₄ _ ht j hj
      rw [show 16 * m + (4 * (i - 4 * m) + c) = 4 * i + c by omega] at hB
      rw [mem₅, hB, T₃ 0 (by decide), getLsbD_outBlock _ (by omega) hj]
      simp only [rkOf]
      rw [show i / 4 + 1 = m + 1 by omega, show 3 - (15 - (4 * (i - 4 * m) + c)) / 4 = i % 4 by omega,
        show 8 * (3 - (15 - (4 * (i - 4 * m) + c)) % 4) + j = 8 * c + j by omega]
    · have hx : (⟨State.addr S, 128⟩ : Region).Contains (State.addr S + BitVec.ofNat 64 (4 * i + c)) 1 :=
        VG.Offset.contains_base _ (by omega) (by omega)
      rw [mem₅, f₄ _ (fun r hr => ?_), c₃.frame _ (fun r hr => ?_)]
      · exact hi.sched i (by omega) c hc j hj
      · simp only [List.mem_singleton] at hr; subst hr; rw [hi.base]
        exact fun h => hp.sep _ hx (Region.sub_prefix (show 4 * tableSlot ≤ 4 * slots by
          rw [tableSlot_eq, slots_eq]; omega) _ h)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact VG.Proof.Sm4.not_contains_off _ (Or.inl (by omega)) (by omega) (by decide) (by omega)
        · exact fun h => hp.sep _ hx (slot_sub hfit' (by decide) _ h)
  · have hk : savedSlot + i < dSlot := by rw [savedSlot_eq, dSlot_eq]; omega
    show s₅.mem.readW _ 32 = _
    rw [mem₅, keep₄ _ hk, keepT _ (by rw [savedSlot_eq, tableSlot_eq]; omega) hk]
    exact hi.saved i hi'
  · rw [mem₅]
    refine hi.frame.trans ((c₃.frame.sub fun r hr => ⟨⟨State.addr b, 4 * slots⟩, List.mem_cons_self, ?_⟩).trans
      (f₄.sub fun r hr => ?_))
    · simp only [List.mem_singleton] at hr; subst hr; rw [hi.base]
      exact Region.sub_prefix (by rw [tableSlot_eq, slots_eq]; omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨State.addr S, 128⟩, List.mem_cons_of_mem _ List.mem_cons_self, VG.Offset.sub_base _ (by omega)⟩
      · exact ⟨⟨State.addr b, 4 * slots⟩, List.mem_cons_self, slot_sub hfit' (by decide)⟩
  · rw [z₅, o₄ _ (by decide) (by decide), o₄ _ (by decide) (by decide), base₃, kp₃, kp₂, k₁,
      show s.gpr kp = _ from hi.kp, show (128 : BitVec 32) = BitVec.ofNat 32 128 from rfl, add_ofNat_ofNat,
      VG.Offset.add_sub_cancel_left, ofNat32_sub_beq (by rw [tableSlot_eq]; omega) (by rw [tableEnd_eq]; omega),
      tableSlot_eq, tableEnd_eq]
    simp only [decide_eq_decide]; omega

theorem ekLoop_wp {s₀ s : State} {b S : BitVec 32} {key : Spec.Sm4.Block} (hp : EkPre s₀ b S)
    (hi : EkInv s₀ b S key 0 s) :
    WP isa (.loop (.block keyBody) .ne) s (EkInv s₀ b S key 8) := by
  refine WP.loop (M := isa) (fun n s => ∃ m, n = 8 - m ∧ m < 8 ∧ EkInv s₀ b S key m s)
    (fun n s hs => ?_) 8 s ⟨0, rfl, by omega, hi⟩
  obtain ⟨m, rfl, hm, hi⟩ := hs
  obtain ⟨s', e', hi', z'⟩ := ekIter_ok hp hm hi
  refine WP.of_runBlock ⟨s', e', ?_⟩
  by_cases h8 : m + 1 = 8
  · exact .inl ⟨by rw [eval_ne, z', h8]; rfl, by rw [h8] at hi'; exact hi'⟩
  · exact .inr ⟨by rw [eval_ne, z']; simp [h8], 8 - (m + 1), by omega, m + 1, rfl, by omega, hi'⟩

/-! ## The start -/

theorem ckEntries_mem {e j : Nat} (he : e < 32) (hj : j < 8) :
    (tableSlot + 8 * e + j, planeOf32 (Spec.Sm4.ck e) j) ∈ ckEntries := by
  simp only [ckEntries, List.mem_flatMap, List.mem_range, List.mem_map]
  exact ⟨e, he, j, hj, rfl⟩

theorem ckEntries_lt : ∀ kv ∈ ckEntries, kv.1 < tableEnd := by decide +kernel

theorem ckEntries_ge : ∀ kv ∈ ckEntries, tableSlot ≤ kv.1 := by decide +kernel

theorem ckEntries_nodup : (ckEntries.map (·.1)).Nodup := by decide +kernel

/-- The code before the loop. -/
def ekHead : List Instr :=
  saveRegs .r2 ++ [movR sb .r2, stS nSlot .r1] ++ ckTable ++ loadKey ++ toBs ++ [kpAt tableSlot]

theorem ekHead_ok {s₀ : State} (hp : expandKeyArm.pre s₀) :
    ∃ s, runBlock isa ekHead s₀ = some s ∧
      EkInv s₀ (s₀.gpr .r2) (s₀.gpr .r1) (Spec.Sm4.blockAt s₀.mem (State.addr (s₀.gpr .r0))) 0 s := by
  obtain ⟨hrd, hwr, dKS, dKB, dSB, fitK, fitS, fitB⟩ := hp
  let b := s₀.gpr .r2
  let S := s₀.gpr .r1
  let Kp := s₀.gpr .r0
  have hwS : ScrIn s₀.wr b := ⟨by rw [hwr]; simp [b], fitB⟩
  have hfit : b.toNat + 4 * 364 ≤ 2 ^ 32 := fitB
  have hbn := addr_toNat b
  have hKn := addr_toNat Kp
  have hfK : Kp.toNat + 16 ≤ 2 ^ 32 := fitK
  have l₁ := tableSlot_eq
  have l₂ := dSlot_eq
  have l₃ := nSlot_eq
  have l₄ := slots_eq
  have l₅ := savedSlot_eq
  have l₆ := tableEnd_eq
  have l₇ := tailSlot_eq
  -- Saving, the schedule's pointer, the table of `CK`.
  obtain ⟨s₁, e₁, sv₁, g₁, rd₁, wr₁, sp₁, f₁, -⟩ := save_ok (base := .r2) hwS rfl
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂, sp₂⟩ := movR_ok s₁ sb .r2
  have b₂ : s₂.gpr sb = b := by rw [r₂, g₁]
  have hw₂ : ScrIn s₂.wr b := by rw [wr₂, wr₁]; exact hwS
  obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃, sp₃, -, f₃⟩ := stSlot_ok s₂ .r1 sb (k := nSlot) b₂ (by decide) hw₂
  have b₃ : s₃.gpr sb = b := by rw [g₃, b₂]
  have hw₃ : ScrIn s₃.wr b := by rw [wr₃]; exact hw₂
  obtain ⟨s₄, e₄, v₄, k₄, g₄, rd₄, wr₄, sp₄, f₄⟩ := constStores_ok ckEntries b₃ hw₃ ckEntries_nodup
    (fun kv hkv => by have := ckEntries_lt kv hkv; omega)
  have b₄ : s₄.gpr sb = b := by rw [g₄ _ (by decide), b₃]
  have hw₄ : ScrIn s₄.wr b := by rw [wr₄]; exact hw₃
  have r0₄ : s₄.gpr .r0 = Kp := by rw [g₄ _ (by decide), g₃, o₂ _ (by decide), g₁]
  -- The key's words, as on entry.
  have f₀₄ : Frame [⟨State.addr b, 4 * slots⟩] s₀.mem s₄.mem := by
    refine f₁.trans ?_; rw [← m₂]
    exact (f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact slot_sub fitB (by decide)⟩).trans f₄
  have inK : ∀ w < 4, InRegions (s₀.rd ++ s₀.wr) (wordAddr Kp w) 4 := fun w hw =>
    ⟨_, List.mem_append_left _ (by rw [hrd]; exact List.mem_singleton_self _), by
      rw [slot_addr (by omega)]; exact VG.Offset.contains_base _ (by omega) (by omega)⟩
  have hKw : ∀ (m : Mem), Frame [⟨State.addr b, 4 * slots⟩] s₀.mem m → ∀ w < 4,
      m.readW (wordAddr Kp w) 32 = s₀.mem.readW (wordAddr Kp w) 32 := fun m hf w hw => by
    rw [slot_addr (by omega)]
    exact hf.readW (r := ⟨State.addr Kp, 16⟩) (VG.Offset.contains_base _ (by omega) (by omega))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dKB) (by decide)
  -- `MK ⊕ FK` to the tail buffer.
  have rdwr : ∀ (st : State), st.rd = s₀.rd → st.wr = s₀.wr → ∀ w < 4,
      InRegions (st.rd ++ st.wr) (wordAddr Kp w) 4 := fun st h1 h2 w hw => by rw [h1, h2]; exact inK w hw
  obtain ⟨s₅, e₅, v₅, k₅, g₅, rd₅, wr₅, sp₅, f₅⟩ := loadKeyWord_ok (s := s₄) 0 (by decide) b₄ hw₄ r0₄
    (rdwr s₄ (by rw [rd₄, rd₃, rd₂, rd₁]) (by rw [wr₄, wr₃, wr₂, wr₁]) 0 (by decide))
  obtain ⟨s₆, e₆, v₆, k₆, g₆, rd₆, wr₆, sp₆, f₆⟩ := loadKeyWord_ok (s := s₅) 1 (by decide)
    (by rw [g₅ _ (by decide) (by decide), b₄]) (by rw [wr₅]; exact hw₄) (by rw [g₅ _ (by decide) (by decide), r0₄])
    (rdwr s₅ (by rw [rd₅, rd₄, rd₃, rd₂, rd₁]) (by rw [wr₅, wr₄, wr₃, wr₂, wr₁]) 1 (by decide))
  obtain ⟨s₇, e₇, v₇, k₇, g₇, rd₇, wr₇, sp₇, f₇⟩ := loadKeyWord_ok (s := s₆) 2 (by decide)
    (by rw [g₆ _ (by decide) (by decide), g₅ _ (by decide) (by decide), b₄]) (by rw [wr₆, wr₅]; exact hw₄)
    (by rw [g₆ _ (by decide) (by decide), g₅ _ (by decide) (by decide), r0₄])
    (rdwr s₆ (by rw [rd₆, rd₅, rd₄, rd₃, rd₂, rd₁]) (by rw [wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]) 2 (by decide))
  obtain ⟨s₈, e₈, v₈, k₈, g₈, rd₈, wr₈, sp₈, f₈⟩ := loadKeyWord_ok (s := s₇) 3 (by decide)
    (by rw [g₇ _ (by decide) (by decide), g₆ _ (by decide) (by decide), g₅ _ (by decide) (by decide), b₄])
    (by rw [wr₇, wr₆, wr₅]; exact hw₄)
    (by rw [g₇ _ (by decide) (by decide), g₆ _ (by decide) (by decide), g₅ _ (by decide) (by decide), r0₄])
    (rdwr s₇ (by rw [rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁]) (by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]) 3 (by decide))
  have g₈' : ∀ r, r ≠ t0 → r ≠ t1 → s₈.gpr r = s₄.gpr r := fun r h0 h1 => by
    rw [g₈ r h0 h1, g₇ r h0 h1, g₆ r h0 h1, g₅ r h0 h1]
  have b₈ : s₈.gpr sb = b := by rw [g₈' _ (by decide) (by decide), b₄]
  have f₀₈ : Frame [⟨State.addr b, 4 * slots⟩] s₀.mem s₈.mem := f₀₄.trans (f₅.trans (f₆.trans (f₇.trans f₈)))
  -- The slots outside the tail buffer after `s₄`, and outside the table after `s₃`.
  have notTail : ∀ k, tableSlot ≤ k → ∀ c < 8, ∀ w < 4, k ≠ tailAt c w := fun k hk c hc w hw => by
    simp only [tailAt]; omega
  have kk₈ : ∀ k < slots, tableSlot ≤ k →
      s₈.mem.readW (wordAddr b k) 32 = s₄.mem.readW (wordAddr b k) 32 := fun k hk ht => by
    rw [k₈ k hk (fun c hc => notTail k ht c hc 3 (by decide)), k₇ k hk (fun c hc => notTail k ht c hc 2 (by decide)),
      k₆ k hk (fun c hc => notTail k ht c hc 1 (by decide)), k₅ k hk (fun c hc => notTail k ht c hc 0 (by decide))]
  have notCk : ∀ k, tableEnd ≤ k → k ∉ ckEntries.map (·.1) := fun k hk hm => by
    simp only [List.mem_map] at hm
    obtain ⟨kv, hkv, rfl⟩ := hm
    have := ckEntries_lt kv hkv; omega
  -- The table of `CK`.
  have hkey₈ : KeyCtx s₈ Spec.Sm4.ck :=
    { scr := by rw [b₈, wr₈, wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]; exact hwS.mem
      fit := by rw [b₈]; exact fitB
      keys := fun e he => (planeOf32_rel (Spec.Sm4.ck e)).congr fun j hj => by
        rw [b₈, entryW, kk₈ _ (by omega) (by omega), v₄ _ (ckEntries_mem he hj)] }
  -- The key, bitsliced.
  obtain ⟨s₉, e₉, c₉, X₉⟩ := toBs_step hkey₈ (Ctx.refl s₈)
  obtain ⟨s₁₀, e₁₀, k₁₀, o₁₀, m₁₀, rd₁₀, wr₁₀, sp₁₀⟩ := kpAt_ok s₉ tableSlot (by decide)
  have b₉ : s₉.gpr sb = b := by rw [c₉.base, b₈]
  have b₁₀ : s₁₀.gpr sb = b := by rw [o₁₀ _ (by decide), b₉]
  have keep₉ : ∀ k, tableSlot ≤ k → k < slots →
      s₁₀.mem.readW (wordAddr b k) 32 = s₈.mem.readW (wordAddr b k) 32 := fun k h1 h2 => by
    rw [m₁₀]
    exact slot_keep (lo := tableSlot) (hi := slots) fitB (Nat.le_refl _) c₉.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [b₈]
      exact VG.Offset.disjoint_base _ (Nat.le_refl _) (by omega)) h1 h2
  have hK : ∀ w < 4, ∀ t < 4, ∀ j < 8, (s₀.mem.readW (wordAddr Kp w) 32).getLsbD (8 * t + j) =
      ((Spec.Sm4.blockAt s₀.mem (State.addr Kp)).getD (4 * w + t) 0).getLsbD j := fun w hw t ht j hj => by
    rw [readW_bit _ _ ht hj, VG.Proof.Sm4.blockAt_getD _ _ (by omega), byte_addr _ rfl (by omega)]
  have hT : ∀ c < 8, ∀ w < 4, s₈.mem.readW (wordAddr b (tailAt c w)) 32 =
      s₀.mem.readW (wordAddr Kp w) 32 ^^^ fkLE w := by
    intro c hc w hw
    have hne : ∀ w', w' < 4 → w' ≠ w → ∀ c' < 8, tailAt c w ≠ tailAt c' w' := fun w' _ h c' _ h' => by
      simp only [tailAt] at h'; omega
    have hl := tailAt_lt hc hw
    rcases (show w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 by omega) with rfl | rfl | rfl | rfl
    · rw [k₈ _ hl (hne 3 (by decide) (by decide)), k₇ _ hl (hne 2 (by decide) (by decide)),
        k₆ _ hl (hne 1 (by decide) (by decide)), v₅ c hc, hKw _ f₀₄ 0 (by decide)]
    · rw [k₈ _ hl (hne 3 (by decide) (by decide)), k₇ _ hl (hne 2 (by decide) (by decide)), v₆ c hc,
        hKw _ (f₀₄.trans f₅) 1 (by decide)]
    · rw [k₈ _ hl (hne 3 (by decide) (by decide)), v₇ c hc, hKw _ (f₀₄.trans (f₅.trans f₆)) 2 (by decide)]
    · rw [v₈ c hc, hKw _ (f₀₄.trans (f₅.trans (f₆.trans f₇))) 3 (by decide)]
  have hst : StRel s₁₀ (fun _ => quads .key Spec.Sm4.ck 0
      (keyInit (Spec.Sm4.blockAt s₀.mem (State.addr Kp)))) := fun w hw =>
    ((X₉ w hw).congr fun j _ => by simp only [planes, slotW, m₁₀, b₁₀, b₉]).congr_right fun c hc =>
      (keyInit_rel b₈ fitB hK hT c hc w hw).symm
  refine ⟨s₁₀, ?_, ⟨b₁₀, ?_, ?_, ?_, hst, fun i hi => by omega, fun i hi => ?_, ?_,
    by rw [rd₁₀, c₉.rd, rd₈, rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁],
    by rw [wr₁₀, c₉.wr, wr₈, wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁],
    by rw [sp₁₀, c₉.sp, sp₈, sp₇, sp₆, sp₅, sp₄, sp₃, sp₂, sp₁]⟩⟩
  · rw [ekHead, runBlock_app, runBlock_app, runBlock_app, runBlock_app, runBlock_app, e₁,
      Option.bind_some,
      show ([movR sb .r2, stS nSlot .r1] : List Instr) = [movR sb .r2] ++ [.str .r1 sb (4 * nSlot)] from rfl,
      runBlock_app, e₂, Option.bind_some, e₃, Option.bind_some, ckTable, e₄, Option.bind_some,
      show loadKey = loadKeyWord 0 ++ (loadKeyWord 1 ++ (loadKeyWord 2 ++ loadKeyWord 3)) from rfl,
      runBlock_app, e₅, Option.bind_some, runBlock_app, e₆, Option.bind_some, runBlock_app, e₇, Option.bind_some,
      e₈, Option.bind_some, e₉, Option.bind_some, e₁₀]
  · rw [keep₉ _ (by decide) (by decide), kk₈ _ (by decide) (by decide), k₄ _ (by decide) (notCk _ (by decide)), m₃,
      readW_slot_write fitB _ (by decide) (by decide), ite_eq_left rfl, o₂ _ (by decide), g₁]
    simp
  · rw [AtEntry, k₁₀, b₉]; simp [b]
  · exact (hkey₈.of_ctx c₉) |> fun h => ⟨by rw [wr₁₀, b₁₀, ← b₉]; exact h.scr, by rw [b₁₀, ← b₉]; exact h.fit,
      fun e he => by rw [b₁₀, ← b₉, m₁₀]; exact h.keys e he⟩
  · have hk : savedSlot + i < slots := by omega
    show s₁₀.mem.readW _ 32 = _
    rw [keep₉ _ (by omega) hk, kk₈ _ hk (by omega), k₄ _ hk (notCk _ (by omega)), m₃,
      readW_slot_write fitB _ hk (by decide), ite_eq_right (by omega), m₂]
    exact sv₁ i hi
  · rw [m₁₀]
    refine (f₀₈.trans (c₉.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)).sub
      fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self, fun _ h => h⟩
    simp only [List.mem_singleton] at hr; subst hr
    rw [b₈]; exact Region.sub_prefix (by omega)

theorem expandKey_wp {s₀ : State} (hp : expandKeyArm.pre s₀) :
    WP isa expandKey s₀ fun s' => (∀ i < 9, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧ expandKeyArm.post s₀ s' := by
  obtain ⟨s₁, e₁, h₁⟩ := ekHead_ok hp
  obtain ⟨hrd, hwr, dKS, dKB, dSB, fitK, fitS, fitB⟩ := hp
  let b := s₀.gpr .r2
  let S := s₀.gpr .r1
  have hwB : ScrIn s₀.wr b := ⟨by rw [hwr]; simp [b], fitB⟩
  have hwS : (⟨State.addr S, 128⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [S]
  have pre : EkPre s₀ b S := ⟨hwB, hwS, dSB, fitS⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, WP.seq (WP.mono (ekLoop_wp pre h₁) fun s₂ h₂ => ?_)⟩)
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃, sp₃⟩ := movR_ok s₂ .r12 sb
  obtain ⟨s₄, e₄, rg₄, -, m₄, -, -, -⟩ := restore_ok (s₀ := s₀) (b := b) (by rw [wr₃, h₂.wr]; exact hwB)
    (by rw [r₃, h₂.base]) (by rw [m₃]; exact h₂.saved)
  refine WP.of_runBlock ⟨s₄, by rw [runBlock_app, e₃, Option.bind_some, e₄], rg₄, ?_⟩
  show Spec.Sm4.scheduleAt s₄.mem (State.addr S) = _
  rw [expandKey_eq]
  apply Vector.ext
  intro i hi
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [show k = 8 * (k / 8) + k % 8 by omega, VG.Proof.Sm4.getLsbD_scheduleAt _ _ hi (by omega) (by omega),
    Vector.getElem_ofFn, m₄, m₃]
  exact h₂.sched i (by omega) _ (by omega) _ (by omega)

end VG.Proof.Sm4.Arm

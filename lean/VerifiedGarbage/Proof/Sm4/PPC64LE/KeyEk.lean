module

public import VerifiedGarbage.Proof.Sm4.PPC64LE.KeyLoop
import VerifiedGarbage.Proof.Sm4.Planes
import VerifiedGarbage.Proof.Sm4.PPC64LE.KeyInit
import VerifiedGarbage.Proof.Sm4.PPC64LE.Ecb
import VerifiedGarbage.Proof.Sm4.Layout
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Sm4.PPC64LE.LayersLit

/-!
# The SM4 key schedule on PPC64LE: the whole function

`expandKey_wp`: with the working space as an argument (`expandKeyPPC64LE`),
`expandKey` saves the callee-saved registers, sets the masks, stores the
table of `CK`'s planes, bitslices sixteen copies of `MK ⊕ FK`, runs the
loop (`ekIter_ok`) and restores the registers; the schedule is the
specification's `expandKey`.
-/

@[expose] public section

namespace VG.Proof.Sm4

open VG VG.PPC64LE VG.Impl.Sm4.PPC64LE

/-- The key schedule on PPC64LE with its working space at `r5`. -/
def expandKeyPPC64LE : Contract PPC64LE.isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, 16⟩
    let sched : Region := ⟨s.gpr .r4, 128⟩
    let scratch : Region := ⟨s.gpr .r5, 8 * slots⟩
    s.rd = [key] ∧ s.wr = [sched, scratch] ∧ key.Disjoint sched ∧ key.Disjoint scratch ∧
      sched.Disjoint scratch ∧
      (s.gpr .r3).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .r4).toNat + 128 ≤ 2 ^ 64 ∧
      (s.gpr .r5).toNat + 8 * slots ≤ 2 ^ 64
  post s s' :=
    Spec.Sm4.scheduleAt s'.mem (s.gpr .r4) = Spec.Sm4.expandKey (Spec.Sm4.blockAt s.mem (s.gpr .r3))
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.sp = s₂.sp

end VG.Proof.Sm4

namespace VG.Proof.Sm4.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.StraightK VG.Impl.Sm4.PPC64LE
open VG.Impl.Aes.PPC64LE (q sb t0 t1 movR ldS stS)
open VG.Impl.Sm4 (planeOf fkWord)
open VG.Proof.Sm4 (planeOf_rel fkWord_bit WordRel quads ofBlock outBlock keyInit rkOf readW64_bit getLsbD_wordAt ofInt_nat
  expandKeyPPC64LE)

/-! ## `MK ⊕ FK` in the tail buffer -/

theorem keyInit_bit (key : Spec.Sm4.Block) {w i j : Nat} (hi : i < 4) (hj : j < 8) :
    (keyInit key w).getLsbD (8 * (3 - i) + j) =
      ((key.getD (4 * w + i) 0).getLsbD j ^^ (Spec.Sm4.fk.getD w 0).getLsbD (8 * (3 - i) + j)) := by
  rw [keyInit, BitVec.getLsbD_xor, getLsbD_wordAt _ _ hi hj]

/-- Byte `i` of block `c` of the tail buffer, from its words. -/
theorem tailBlock_bit (s : State) {c i j : Nat} (hi : i < 16) (hj : j < 8) :
    ((tailBlock s c).getD i 0).getLsbD j = (slotW s (tailAt c (i / 8))).getLsbD (8 * (i % 8) + j) := by
  rw [slotW, readW64_bit _ _ (by omega_arith) hj, VG.Proof.Sm4.blockAt_getD _ _ hi, wordAddr, addr_add, addr_add, tailAt]
  rw [show 8 * tailSlot + 16 * c + i = 8 * (tailSlot + 2 * c + i / 8) + i % 8 by omega_arith]

/-- The tail buffer's blocks are `MK ⊕ FK`, from the key's 64-bit words `K h`. -/
theorem keyInit_rel {s : State} {key : Spec.Sm4.Block} {K : Nat → BitVec 64}
    (hK : ∀ h < 2, ∀ t < 8, ∀ j < 8, (K h).getLsbD (8 * t + j) = (key.getD (8 * h + t) 0).getLsbD j)
    (hT : ∀ c < 16, ∀ h < 2, slotW s (tailAt c h) = K h ^^^ fkWord h) :
    ∀ c < 16, ∀ w < 4, ofBlock (tailBlock s c) w = keyInit key w := by
  intro c hc w hw
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hi : 3 - k / 8 < 4 := by omega_arith
  rw [show k = 8 * (3 - (3 - k / 8)) + k % 8 by omega_arith, keyInit_bit key (w := w) hi (by omega_arith)]
  simp only [ofBlock]
  rw [getLsbD_wordAt _ _ hi (by omega_arith), tailBlock_bit s (c := c) (by omega_arith) (by omega_arith), hT c hc _ (by omega_arith),
    BitVec.getLsbD_xor, fkWord_bit (by omega_arith)]
  have e1 : 8 * ((4 * w + (3 - k / 8)) % 8) + k % 8 = 8 * (4 * (w % 2) + (3 - k / 8)) + k % 8 := by omega_arith
  rw [e1, hK _ (by omega_arith) _ (by omega_arith) _ (by omega_arith)]
  have h1 : 2 * ((4 * w + (3 - k / 8)) / 8) + (8 * (4 * (w % 2) + (3 - k / 8)) + k % 8) / 32 = w := by omega_arith
  have h2 : 8 * (3 - (8 * (4 * (w % 2) + (3 - k / 8)) + k % 8) % 32 / 8) +
      (8 * (4 * (w % 2) + (3 - k / 8)) + k % 8) % 8 = 8 * (3 - (3 - k / 8)) + k % 8 := by omega_arith
  have h3 : 8 * ((4 * w + (3 - k / 8)) / 8) + (4 * (w % 2) + (3 - k / 8)) = 4 * w + (3 - k / 8) := by omega_arith
  rw [h1, h2, h3]

theorem ckEntries_mem {e j : Nat} (he : e < 32) (hj : j < 8) :
    (tableSlot + 8 * e + j, planeOf (Spec.Sm4.ck e) j) ∈ ckEntries := by
  simp only [ckEntries, List.mem_flatMap, List.mem_range, List.mem_map]
  exact ⟨e, he, j, hj, rfl⟩

theorem ckEntries_lt : ∀ kv ∈ ckEntries, kv.1 < tableEnd := by decide +kernel

theorem ckEntries_ge : ∀ kv ∈ ckEntries, tableSlot ≤ kv.1 := by decide +kernel

theorem ckEntries_nodup : (ckEntries.map (·.1)).Nodup := by
  -- The slots are consecutive: a linear check, not the quadratic `Nodup` search.
  rw [show ckEntries.map (·.1) = List.range' tableSlot 256 by decide +kernel]
  exact List.nodup_range'

theorem entryW_slot (s : State) (e j : Nat) : entryW s.mem (s.gpr sb) e j = slotW s (tableSlot + 8 * e + j) := by
  simp only [entryW, slotW, wordAddr]; rw [show 8 * (tableSlot + 8 * e + j) = 8 * tableSlot + 64 * e + 8 * j by omega_arith]

/-- The code before the loop. -/
def ekHead : List Instr :=
  [movR sb .r5] ++ saveRegs ++ setSlots keyMasks ++ ckTable ++ loadHalf 0 ++
    loadHalf 1 ++ toBs ++ slotAddr .r11 tableEnd ++ slotAddr kr tableSlot

theorem ekHead_ok {s₀ : State} (hp : expandKeyPPC64LE.pre s₀) :
    ∃ s, runBlock isa ekHead s₀ = some s ∧
      EkInv s₀ (s₀.gpr .r5) (s₀.gpr .r4) (Spec.Sm4.blockAt s₀.mem (s₀.gpr .r3)) 0 s := by
  obtain ⟨hrd, hwr, dKS, dKB, dSB, fitK, fitS, fitB⟩ := hp
  let b := s₀.gpr .r5
  let S := s₀.gpr .r4
  let Kp := s₀.gpr .r3
  have hwB : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [b]
  have hfitB := fitB
  rw [slots_eq] at hfitB
  -- The registers.
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s₀ sb .r5
  have g₁ : ∀ r, r ≠ sb → s₁.gpr r = s₀.gpr r := o₁
  have hb₁ : s₁.gpr sb = b := r₁
  have mem₁ : s₁.mem = s₀.mem := m₁
  have wr₁' : s₁.wr = s₀.wr := wr₁
  have rd₁' : s₁.rd = s₀.rd := rd₁
  -- Saving, the masks and the table of `CK`.
  obtain ⟨s₂, e₂, sv₂, g₂, rd₂, wr₂, f₂, -⟩ := save_ok (b := b) (by rw [wr₁']; exact hwB) hb₁
  obtain ⟨s₃, e₃, v₃, k₃, g₃, rd₃, wr₃, f₃⟩ := setSlots_ok (b := b) keyMasks (by rw [g₂, hb₁])
    (by rw [wr₂, wr₁']; exact hwB) (fun kv hkv => by have := mask_lt hkv; rw [tableSlot_eq]; omega_arith) (by decide)
  obtain ⟨s₄, e₄, v₄, k₄, g₄, rd₄, wr₄, f₄⟩ := setSlotsN_ok tableEnd (by rw [tableEnd_eq, slots_eq]; omega_arith)
    ckEntries (b := b) (by rw [g₃ _ (by decide), g₂, hb₁]) (by rw [wr₃, wr₂, wr₁']; exact hwB) ckEntries_lt
    ckEntries_nodup
  have hb₄ : s₄.gpr sb = b := by rw [g₄ _ (by decide), g₃ _ (by decide), g₂, hb₁]
  have f₀₄ : Frame [⟨b, 8 * slots⟩] s₀.mem s₄.mem := by
    rw [← mem₁]
    refine f₂.trans ((f₃.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).trans
      (f₄.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)) <;>
      (simp only [List.mem_singleton] at hr; subst hr) <;>
      exact Region.sub_prefix (by simp only [tableSlot_eq, tableEnd_eq, slots_eq]; omega_arith)
  -- The key.
  have inK : ∀ h < 2, InRegions (s₄.rd ++ s₄.wr) (Kp + BitVec.ofNat 64 (8 * h)) 8 := fun h hh =>
    ⟨_, List.mem_append_left _ (by rw [rd₄, rd₃, rd₂, rd₁', hrd]; exact List.mem_singleton_self _),
      VG.Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have hKw : ∀ (m : Mem), Frame [⟨b, 8 * slots⟩] s₀.mem m → ∀ h < 2,
      m.readW (Kp + BitVec.ofNat 64 (8 * h)) 64 = s₀.mem.readW (Kp + BitVec.ofNat 64 (8 * h)) 64 :=
    fun m hf h hh => hf.readW (r := ⟨Kp, 16⟩) (VG.Offset.contains_base _ (by omega_arith) (by omega_arith))
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dKB) (by decide)
  have hrdi₄ : s₄.gpr .r3 = Kp := by
    rw [g₄ _ (by decide), g₃ _ (by decide), g₂, g₁ _ (by decide)]
  obtain ⟨s₅, e₅, v₅, k₅, g₅, rd₅, wr₅, f₅⟩ := loadHalf_ok 0 (by decide) hb₄ (by rw [wr₄, wr₃, wr₂, wr₁']; exact hwB)
    (by rw [hrdi₄]; exact inK 0 (by decide))
  have hb₅ : s₅.gpr sb = b := by rw [g₅ _ (by decide) (by decide), hb₄]
  obtain ⟨s₆, e₆, v₆, k₆, g₆, rd₆, wr₆, f₆⟩ := loadHalf_ok 1 (by decide) hb₅
    (by rw [wr₅, wr₄, wr₃, wr₂, wr₁']; exact hwB)
    (by rw [rd₅, wr₅, g₅ _ (by decide) (by decide), hrdi₄]; exact inK 1 (by decide))
  have hb₆ : s₆.gpr sb = b := by rw [g₆ _ (by decide) (by decide), hb₅]
  have f₀₆ : Frame [⟨b, 8 * slots⟩] s₀.mem s₆.mem := (f₀₄.trans f₅).trans f₆
  have hk₆ : ∀ k < slots, (∀ c < 16, ∀ h < 2, k ≠ tailAt c h) → slotW s₆ k = slotW s₄ k := fun k hk hn => by
    rw [k₆ k hk (fun c hc => hn c hc 1 (by decide)), k₅ k hk (fun c hc => hn c hc 0 (by decide))]
  have notTail : ∀ k, tableSlot ≤ k ∨ k < tailSlot → ∀ c < 16, ∀ h < 2, k ≠ tailAt c h := fun k hk c hc h hh => by
    simp only [tailAt, tailSlot_eq, tableSlot_eq] at hk ⊢; omega_arith
  have notCk : ∀ k, k < tableSlot ∨ tableEnd ≤ k → k ∉ ckEntries.map (·.1) := fun k hk hm => by
    simp only [List.mem_map] at hm
    obtain ⟨kv, hkv, rfl⟩ := hm
    have := ckEntries_lt kv hkv; have := ckEntries_ge kv hkv; omega_arith
  have notMask : ∀ k, 51 ≤ k → k ∉ keyMasks.map (·.1) := fun k hk hm => by
    simp only [List.mem_map] at hm
    obtain ⟨kv, hkv, rfl⟩ := hm
    have := mask_range hkv; omega_arith
  -- The table and the masks.
  have hkey₆ : KeyCtx s₆ Spec.Sm4.ck :=
    { scr := by rw [hb₆, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁']; exact hwB
      fit := by rw [hb₆]; exact fitB
      keys := fun e he => (planeOf_rel (Spec.Sm4.ck e)).congr fun j hj => by
        rw [entryW_slot, hk₆ _ (by rw [tableSlot_eq, slots_eq]; omega_arith) (notTail _ (Or.inl (by omega_arith))),
          v₄ _ (ckEntries_mem he hj)] }
  have hm₆ : MasksOk s₆ := fun kv hkv => by
    have := mask_range hkv
    rw [hk₆ _ (by rw [slots_eq]; omega_arith) (notTail _ (Or.inr (by rw [tailSlot_eq]; omega_arith))),
      k₄ _ (by rw [slots_eq]; omega_arith) (notCk _ (Or.inl (by rw [tableSlot_eq]; omega_arith))), v₃ kv hkv]
  -- The key, bitsliced.
  obtain ⟨s₇, e₇, c₇, kr₇, X₇⟩ := toBs_step hkey₆ (Ctx.refl hm₆)
  obtain ⟨s₈, e₈, r₈, o₈, m₈, rd₈, wr₈⟩ := slotAddr_ok s₇ .r11 tableEnd (by decide)
  obtain ⟨s₉, e₉, r₉, o₉, m₉, rd₉, wr₉⟩ := slotAddr_ok s₈ kr tableSlot (by decide)
  have hb₇ : s₇.gpr sb = b := by rw [c₇.base, hb₆]
  have hb₉ : s₉.gpr sb = b := by rw [o₉ _ (by decide), o₈ _ (by decide), hb₇]
  have mem₉ : s₉.mem = s₇.mem := by rw [m₉, m₈]
  have g₉ : ∀ r, r ∉ sboxWrites → r ≠ kr → r ≠ .r11 → s₉.gpr r = s₆.gpr r := fun r h1 h2 h3 => by
    rw [o₉ r h2, o₈ r h3, c₇.keep r h1 h2]
  have g₆' : ∀ r, r ∉ sboxWrites → r ≠ sb → s₆.gpr r = s₀.gpr r := fun r h1 h2 => by
    have ht0 : r ≠ t0 := fun h => h1 (by subst h; decide)
    have ht1 : r ≠ t1 := fun h => h1 (by subst h; decide)
    rw [g₆ r ht0 ht1, g₅ r ht0 ht1, g₄ r ht0, g₃ r ht0, g₂, g₁ r h2]
  have hK : ∀ h < 2, ∀ t < 8, ∀ j < 8, (s₀.mem.readW (Kp + BitVec.ofNat 64 (8 * h)) 64).getLsbD (8 * t + j) =
      ((Spec.Sm4.blockAt s₀.mem Kp).getD (8 * h + t) 0).getLsbD j := fun h hh t ht j hj => by
    rw [readW64_bit _ _ ht hj, VG.Proof.Sm4.blockAt_getD _ _ (by omega_arith), addr_add]
  have hT : ∀ c < 16, ∀ h < 2, slotW s₆ (tailAt c h) = s₀.mem.readW (Kp + BitVec.ofNat 64 (8 * h)) 64 ^^^ fkWord h := by
    intro c hc h hh
    rcases (show h = 0 ∨ h = 1 by omega_arith) with rfl | rfl
    · rw [k₆ _ (tailAt_lt hc (by decide)) (fun c' _ h' => by simp only [tailAt] at h'; omega_arith), v₅ c hc, hrdi₄,
        hKw _ f₀₄ 0 (by decide)]
    · rw [v₆ c hc, g₅ _ (by decide) (by decide), hrdi₄, hKw _ (f₀₄.trans f₅) 1 (by decide)]
  have hst : StRel s₉ (fun _ => quads .key Spec.Sm4.ck 0 (keyInit (Spec.Sm4.blockAt s₀.mem Kp))) := fun w hw =>
    ((X₇ w hw).congr fun j _ => by simp only [planes, slotW, mem₉, hb₉, hb₇]).congr_right fun c hc =>
      (keyInit_rel hK hT c hc w hw).symm
  refine ⟨s₉, ?_, ⟨hb₉, ?_, ?_, ?_, ?_, ?_, hst, fun i hi => by omega_arith, fun i hi => ?_, ?_,
    by rw [rd₉, rd₈, c₇.rd, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁'], by rw [wr₉, wr₈, c₇.wr, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁']⟩⟩
  · rw [ekHead, runBlock_app, runBlock_app, runBlock_app, runBlock_app, runBlock_app, runBlock_app,
      runBlock_app, runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some, e₃, Option.bind_some,
      ckTable, e₄, Option.bind_some, e₅, Option.bind_some, e₆, Option.bind_some, e₇, Option.bind_some, e₈,
      Option.bind_some, e₉]
  · rw [g₉ _ (by decide) (by decide) (by decide), g₆' _ (by decide) (by decide)]
    exact (BitVec.add_zero _).symm
  · rw [o₉ _ (by decide), r₈, hb₇]
  · rw [AtEntry, r₉, o₈ _ (by decide), hb₇]; simp; rfl
  · exact (hkey₆.of_ctx c₇) |> fun h => ⟨by rw [wr₉, wr₈, hb₉, ← hb₇]; exact h.scr, by rw [hb₉, ← hb₇]; exact h.fit,
      fun e he => by rw [hb₉, ← hb₇, mem₉]; exact h.keys e he⟩
  · exact fun kv hkv => by simp only [slotW, mem₉, hb₉, ← hb₇]; exact c₇.masks kv hkv
  · have hk : savedSlot + i < slots := by rw [savedSlot_eq, slots_eq]; omega_arith
    have h7 : slotW s₇ (savedSlot + i) = slotW s₆ (savedSlot + i) := by
      simp only [slotW, hb₇, hb₆]
      refine c₇.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      rw [hb₆, wordAddr]
      exact VG.Offset.disjoint_base _ (by rw [tableSlot_eq, savedSlot_eq]; omega_arith) (by rw [savedSlot_eq]; omega_arith)
    have h6 : slotW s₆ (savedSlot + i) = slotW s₂ (savedSlot + i) := by
      rw [hk₆ _ hk (notTail _ (Or.inl (by rw [tableSlot_eq, savedSlot_eq]; omega_arith))),
        k₄ _ hk (notCk _ (Or.inr (by rw [tableEnd_eq, savedSlot_eq]; omega_arith))),
        k₃ _ hk (notMask _ (by rw [savedSlot_eq]; omega_arith))]
    have h2 := sv₂ i hi
    rw [g₁ _ (sreg_ne i hi)] at h2
    show s₉.mem.readW (wordAddr b (savedSlot + i)) 64 = _
    rw [mem₉, ← hb₇, ← h2]
    have := h7.trans h6
    simp only [slotW, hb₇, show s₂.gpr sb = b by rw [g₂, hb₁]] at this
    rw [hb₇]; exact this
  · rw [mem₉]
    refine (f₀₆.trans (c₇.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩)).sub
      fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self, fun _ h => h⟩
    simp only [List.mem_singleton] at hr; subst hr
    rw [hb₆]; exact Region.sub_prefix (by rw [tableSlot_eq, slots_eq]; omega_arith)

/-! ## The loop and the whole function -/

theorem ekLoop_wp {s₀ s : State} {b S : Addr} {key : Spec.Sm4.Block} (hp : EkPre s₀ b S)
    (hi : EkInv s₀ b S key 0 s) :
    WP isa (.loop (.block keyBody) (.nonzero .d t0)) s (EkInv s₀ b S key 8) := by
  refine WP.loop (M := isa) (fun n s => ∃ m, n = 8 - m ∧ m < 8 ∧ EkInv s₀ b S key m s)
    (fun n s hs => ?_) 8 s ⟨0, rfl, by omega_arith, hi⟩
  obtain ⟨m, rfl, hm, hi⟩ := hs
  obtain ⟨s', e', hi', z'⟩ := ekIter_ok hp hm hi
  refine WP.of_runBlock ⟨s', e', ?_⟩
  by_cases h8 : m + 1 = 8
  · exact .inl ⟨by rw [eval_nonzero, z', h8]; rfl, by rw [h8] at hi'; exact hi'⟩
  · exact .inr ⟨by rw [eval_nonzero, z']; simp [h8], 8 - (m + 1), by omega_arith, m + 1, rfl, by omega_arith, hi'⟩

theorem expandKey_wp {s₀ : State} (hp : expandKeyPPC64LE.pre s₀) :
    WP isa expandKey s₀ fun s' => (∀ i < 18, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      expandKeyPPC64LE.post s₀ s' := by
  obtain ⟨s₁, e₁, h₁⟩ := ekHead_ok hp
  obtain ⟨hrd, hwr, dKS, dKB, dSB, fitK, fitS, fitB⟩ := hp
  let b := s₀.gpr .r5
  let S := s₀.gpr .r4
  have hwB : (⟨b, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [b]
  have hwS : (⟨S, 128⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp [S]
  have pre : EkPre s₀ b S := ⟨hwB, hwS, dSB, fitB, fitS⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, WP.seq (WP.mono (ekLoop_wp pre h₁) fun s₂ h₂ => ?_)⟩)
  obtain ⟨s₃, e₃, rg₃, -, m₃, -, -⟩ := restore_ok (by rw [h₂.wr]; exact hwB) h₂.base h₂.saved
  refine WP.of_runBlock ⟨s₃, e₃, rg₃, ?_⟩
  show Spec.Sm4.scheduleAt s₃.mem S = _
  rw [expandKey_eq]
  apply Vector.ext
  intro i hi
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [show k = 8 * (k / 8) + k % 8 by omega_arith, VG.Proof.Sm4.getLsbD_scheduleAt _ _ hi (by omega_arith) (by omega_arith),
    Vector.getElem_ofFn, m₃]
  exact h₂.sched i (by omega_arith) _ (by omega_arith) _ (by omega_arith)

end VG.Proof.Sm4.PPC64LE

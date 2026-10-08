import VerifiedGarbage.Proof.Camellia.AArch64.KeySetup
import VerifiedGarbage.Proof.Camellia.Scratch

/-!
# The Camellia key schedule on AArch64: the whole function

`expandKey_wp`: `expandKey` meets `expandKeyAArch64`. After the prologue
(`ekPrologue_ok`), `loadKey_wp` and `kaKb_wp` leave `KL`, `KR`, `KA` and
`KB` in their slots; `loadValues_ok` byte-swaps them into registers, and
`storeSubkeys_ok` stores the subkeys, which are the specification's
(`scheduleWords_expandKey`, `schedule_of_stores`).
-/

namespace VG.Proof.Camellia.AArch64

open VG.Impl.Camellia (bytePos keyPlane sigmas)
open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Camellia.AArch64
open VG.Impl.Aes.AArch64 (q sb t0 t1 u7 kp movR ldS stS)
open VG.Proof.Camellia (hiW loW)

theorem entryW_slot (s : State) (i j : Nat) : entryW s.mem (s.gpr sb) i j = slotW s (keySlot + 8 * i + j) := by
  simp only [entryW, slotW, wordAddr]
  rw [show 8 * (keySlot + 8 * i + j) = 8 * keySlot + 64 * i + 8 * j by omega]

/-- What the subkeys' stores leave: the schedule's bytes. -/
structure StoresPost (s₈ : State) (S : Addr) (len : Nat) (key : List Byte) (s : State) : Prop where
  bytes : Spec.Camellia.bytesAt s.mem S (8 * Spec.Camellia.scheduleLength (Spec.Camellia.rounds len)) =
    Spec.Camellia.scheduleBytes (Spec.Camellia.expandKey key)
  frame : Frame [⟨S, 272⟩] s₈.mem s.mem
  regs : ∀ r, r ≠ t0 → r ≠ t1 → s.gpr r = s₈.gpr r
  rd : s.rd = s₈.rd
  wr : s.wr = s₈.wr

/-- The stores of one key length's subkeys. -/
theorem stores_wp {s₈ : State} {S : Addr} {len : Nat} {key : List Byte} {ks : List (Nat × Nat × Bool)}
    (hS : s₈.gpr .x2 = S) (hw : (⟨S, 272⟩ : Region) ∈ s₈.wr) (hv : ∀ k ∈ ks, k.1 < 4)
    (hks : ks.length ≤ 34)
    (hg : ∀ v < 4, s₈.gpr (hiReg v) = hiW ([(Spec.Camellia.klkr key).1, (Spec.Camellia.klkr key).2,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).1,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).2].getD v 0) ∧
      s₈.gpr (loReg v) = loW ([(Spec.Camellia.klkr key).1, (Spec.Camellia.klkr key).2,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).1,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).2].getD v 0))
    (hlen : 8 * Spec.Camellia.scheduleLength (Spec.Camellia.rounds len) = 8 * ks.length)
    (hks' : ks = if key.length = 16 then Impl.Camellia.subkeys128 else Impl.Camellia.subkeys256) :
    WP isa (.block (storeSubkeys ks)) s₈ (StoresPost s₈ S len key) := by
  obtain ⟨s₉, e₉, b₉, f₉, g₉, rd₉, wr₉⟩ := storeSubkeys_ok ks hv 0 s₈ (fun i hi => ⟨_, hw, by
    rw [hS]; exact VG.Offset.contains_base _ (by omega) (by omega)⟩) (by omega)
  refine WP.of_runBlock ⟨s₉, e₉, ⟨?_, ?_, g₉, rd₉, wr₉⟩⟩
  · rw [hlen, schedule_of_stores (H := fun v => s₈.gpr (hiReg v)) (L := fun v => s₈.gpr (loReg v)) hv hg (by rw [← hS]; exact b₉), Spec.Camellia.scheduleBytes,
      Proof.Camellia.scheduleWords_expandKey, ← hks']
  · rw [hS] at f₉
    exact f₉.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.sub_base S (by omega)⟩

theorem expandKey_wp {s₀ : State} (hp : expandKeyAArch64.pre s₀) :
    WP isa expandKey s₀ fun s' => (∀ i < 10, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      expandKeyAArch64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKS, dKB, dSB, fitK, fitS, fitB, hlen⟩ := hp
  obtain ⟨hl', hr', hW, hA, hB, hE, hK, hS⟩ := kaKb_slots
  have ht := tailSlot_eq
  have hsv := savedSlot_eq
  have hwB : (⟨s₀.gpr .x3, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  have hwS : (⟨s₀.gpr .x2, 272⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  have hrK : (⟨s₀.gpr .x0, (s₀.gpr .x1).toNat⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  unfold expandKey
  -- The prologue.
  obtain ⟨s₁, e₁, b₁, x3₁, g₁, sv₁, mk₁, ent₁, f₁, rd₁, wr₁⟩ := ekPrologue_ok (b := s₀.gpr .x3) rfl hwB fitB
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have x0₁ : s₁.gpr .x0 = s₀.gpr .x0 := g₁ _ (by decide) (by decide) (by decide) (by decide)
  have x2₁ : s₁.gpr .x2 = s₀.gpr .x2 := g₁ _ (by decide) (by decide) (by decide) (by decide)
  -- The key, unchanged so far.
  have hkey₁ : Spec.Camellia.bytesAt s₁.mem (s₁.gpr .x0) (s₀.gpr .x1).toNat =
      Spec.Camellia.bytesAt s₀.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat := by
    rw [x0₁]
    refine Proof.Camellia.bytesAt_congr fun i hi => f₁.bytes (R := ⟨s₀.gpr .x0, (s₀.gpr .x1).toNat⟩)
      (fun r hr => ?_) (by simp only; omega) hi
    simp only [List.mem_singleton] at hr; subst hr
    exact dKB.sub_right (Region.sub_prefix (by omega))
  -- `KL` and `KR`.
  refine WP.seq (WP.mono (loadKey_wp (len := (s₀.gpr .x1).toNat) (s := s₁) (by rw [b₁, wr₁]; exact hwB)
    (by rw [x0₁, rd₁]; exact hrK) (by rw [x0₁]; exact fitK) (by rw [x0₁, b₁]; exact dKB)
    (by rw [x3₁, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hlen) fun s₂ h₂ => ?_)
  obtain ⟨kl₂, kr₂, sl₂, g₂, f₂, rd₂, wr₂⟩ := h₂
  rw [hkey₁] at kl₂ kr₂
  -- Abbreviations.
  generalize hkey : Spec.Camellia.bytesAt s₀.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat = key at kl₂ kr₂
  have hb₂ : s₂.gpr sb = s₀.gpr .x3 := by rw [g₂ _ (by decide) (by decide) (by decide), b₁]
  -- `kp` at the table.
  obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := setKp_ok s₂
  refine WP.seq (WP.of_runBlock ⟨s₄, e₄, ?_⟩)
  have hg₄ : ∀ r, r ≠ kp → s₄.gpr r = s₂.gpr r := o₄
  have hb₄ : s₄.gpr sb = s₀.gpr .x3 := by rw [hg₄ _ (by decide), hb₂]
  have hs₄ : ∀ k, slotW s₄ k = slotW s₂ k := slotW_eq_of m₄ (hg₄ _ (by decide))
  have x2₄ : s₄.gpr .x2 = s₀.gpr .x2 := by
    rw [hg₄ _ (by decide), g₂ _ (by decide) (by decide) (by decide), x2₁]
  have x3₄ : s₄.gpr .x3 = s₀.gpr .x1 := by
    rw [hg₄ _ (by decide), g₂ _ (by decide) (by decide) (by decide), x3₁]
  have wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wr₂, wr₁]
  have hlow : ∀ k < klSlot, slotW s₄ k = slotW s₁ k := fun k hk => by
    rw [hs₄, sl₂ k (by omega) (Or.inl hk)]
  let KL : BitVec 64 × BitVec 64 := (hiW (Spec.Camellia.klkr key).1, loW (Spec.Camellia.klkr key).1)
  let KR : BitVec 64 × BitVec 64 := (hiW (Spec.Camellia.klkr key).2, loW (Spec.Camellia.klkr key).2)
  have hpre : KaPre s₄ KL KR := by
    refine ⟨⟨?_, ?_, by decide, fun kv hkv => ?_, fun i hi => ?_⟩, ?_,
      kl₂.congr (hs₄ _) (hs₄ _), kr₂.congr (hs₄ _) (hs₄ _)⟩
    · rw [hb₄, wr₄']; exact hwB
    · rw [hb₄]; exact fitB
    · have := mask_lt hkv
      rw [hlow _ (by omega)]; exact mk₁ kv hkv
    · refine sigmas_rel (m := s₄.mem) (b := s₄.gpr sb) (fun i hi j hj => ?_) i hi
      rw [entryW_slot, hlow _ (by omega), ← entryW_slot, b₁]
      exact ent₁ i hi j hj
    · rw [AtEntry, a₄, hb₄, hb₂]; simp
  -- `KA` and `KB`.
  refine WP.seq (WP.mono (kaKb_wp hpre) fun s₅ h₅ => ?_)
  have hb₅ : s₅.gpr sb = s₀.gpr .x3 := h₅.base.trans hb₄
  have wr₅ : s₅.wr = s₀.wr := h₅.wr.trans wr₄'
  have hscr₅ : (⟨s₀.gpr .x3, 8 * slots⟩ : Region) ∈ s₅.wr := by rw [wr₅]; exact hwB
  -- The values, byte-swapped into registers.
  obtain ⟨hKA, hKB⟩ := kaD_eq (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2
  have hKA' : kaD2 KL KR = _ := hKA
  have hKB' : kaD3 KL KR = _ := hKB
  obtain ⟨s₆, e₆, v₆, o₆, m₆, rd₆, wr₆⟩ := loadValues_ok (s := s₅) (by rw [hb₅]; exact hscr₅)
    [(Spec.Camellia.klkr key).1, (Spec.Camellia.klkr key).2,
      (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).1,
      (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).2] (fun v hv => by
      rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega) with rfl | rfl | rfl | rfl
      · exact h₅.kl hpre
      · exact h₅.kr hpre
      · have := h₅.ka (by decide); rw [hKA'] at this; exact this
      · have := h₅.kb (by decide); rw [hKB'] at this; exact this)
  have hnv : ∀ r : Reg, r ∈ [sb, Reg.x2, Reg.x3] → ∀ v < 4, r ≠ hiReg v ∧ r ≠ loReg v := by decide
  have hb₆ : s₆.gpr sb = s₀.gpr .x3 := by rw [o₆ _ (hnv _ (by simp)), hb₅]
  have x3₅ : s₅.gpr .x3 = s₀.gpr .x1 := by
    rw [h₅.regs _ (by decide) (by decide) (by decide) (by decide), x3₄]
  -- The key's length.
  obtain ⟨s₈, e₈, z₈, g₈, m₈, rd₈, wr₈⟩ := subI_ok s₆ t0 .x3 (imm := 16) (by decide)
  have hz₈ : (s₈.gpr t0 == 0) = decide ((s₀.gpr .x1).toNat = 16) := by
    rw [z₈, o₆ _ (hnv _ (by simp)), x3₅]
    conv => lhs; rw [show s₀.gpr .x1 = BitVec.ofNat 64 (s₀.gpr .x1).toNat by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]]
    rw [VG.Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]
  refine WP.seq (WP.of_runBlock ⟨s₈, by rw [runBlock_append', e₆, Option.bind_some, e₈], ?_⟩)
  -- The subkeys.
  have hx2₈ : s₈.gpr .x2 = s₀.gpr .x2 := by
    rw [g₈ _ (by decide), o₆ _ (hnv _ (by simp)), h₅.regs _ (by decide) (by decide) (by decide) (by decide), x2₄]
  have hwS₈ : (⟨s₀.gpr .x2, 272⟩ : Region) ∈ s₈.wr := by rw [wr₈, wr₆, wr₅]; exact hwS
  have hg₈ : ∀ v < 4, s₈.gpr (hiReg v) = hiW ([(Spec.Camellia.klkr key).1, (Spec.Camellia.klkr key).2,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).1,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).2].getD v 0) ∧
      s₈.gpr (loReg v) = loW ([(Spec.Camellia.klkr key).1, (Spec.Camellia.klkr key).2,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).1,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).2].getD v 0) :=
    fun v hv => by
      obtain ⟨n1, -, n3, -⟩ := hiReg_ne v hv
      rw [g₈ _ n1, g₈ _ n3]; exact v₆ v hv
  have hklen : key.length = (s₀.gpr .x1).toNat := by rw [← hkey]; simp [Spec.Camellia.bytesAt]
  refine WP.seq (WP.mono (Q := StoresPost s₈ (s₀.gpr .x2) (s₀.gpr .x1).toNat key)
    (WP.ite (decide ((s₀.gpr .x1).toNat = 16)) ((eval_zero s₈ t0).trans (by rw [hz₈])) (fun h16 => ?_)
      (fun h16 => ?_))
    fun s₉ h₉ => ?_)
  · have h16 : (s₀.gpr .x1).toNat = 16 := by simpa using h16
    exact stores_wp hx2₈ hwS₈ subkeys_lt4.1 (by rw [subkeys_length.1]; omega) hg₈
      (by rw [h16, subkeys_length.1]; rfl) (by rw [hklen, ite_eq_left h16])
  · have h16 : (s₀.gpr .x1).toNat ≠ 16 := by simpa using h16
    exact stores_wp hx2₈ hwS₈ subkeys_lt4.2 (by rw [subkeys_length.2]) hg₈
      (by rw [subkeys_length.2]; simp only [Spec.Camellia.rounds, h16, ↓reduceIte]; rfl)
      (by rw [hklen, ite_eq_right h16])
  -- The epilogue.
  have hb₉ : s₉.gpr sb = s₀.gpr .x3 := by rw [h₉.regs _ (by decide) (by decide), g₈ _ (by decide), hb₆]
  have hSB : ∀ k, savedSlot ≤ k → k < savedSlot + 10 →
      s₉.mem.readW (wordAddr (s₀.gpr .x3) k) 64 = s₁.mem.readW (wordAddr (s₀.gpr .x3) k) 64 := by
    intro k h1 h2
    rw [h₉.frame.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (dSB.sub_right (by rw [wordAddr]; exact VG.Offset.sub_base _ (by omega))).symm) (by decide)]
    have := h₅.keep k (by omega) (by omega) (Or.inl (by omega))
    rw [hs₄, sl₂ k (by omega) (Or.inl (by omega))] at this
    simp only [slotW, hb₅, b₁] at this
    rw [m₈, m₆]
    exact this
  obtain ⟨s₁₀, e₁₀, rg₁₀, -, m₁₀, -, -⟩ := restore_ok (s₀ := s₀) (b := s₀.gpr .x3)
    (by rw [h₉.wr, wr₈, wr₆, wr₅]; exact hwB) hb₉ (fun i hi => by
      rw [hSB _ (by omega) (by omega)]; exact sv₁ i hi)
  refine WP.of_runBlock ⟨s₁₀, e₁₀, rg₁₀, ?_⟩
  show Spec.Camellia.bytesAt s₁₀.mem (s₀.gpr .x2) _ = _
  rw [hkey, m₁₀, ← h₉.bytes]

end VG.Proof.Camellia.AArch64

import VerifiedGarbage.Proof.Camellia.X86_64.KeySetup
import VerifiedGarbage.Proof.Camellia.Scratch

/-!
# The Camellia key schedule on x86-64: the whole function

`expandKey_wp`: `expandKey` meets `expandKeyX86_64`. After the prologue
(`ekPrologue_ok`), `loadKey_wp` and `kaKb_wp` leave `KL`, `KR`, `KA` and
`KB` in their slots; `loadValues_ok` byte-swaps them into registers, and
`storeSubkeys_ok` stores the subkeys, which are the specification's
(`scheduleWords_expandKey`, `schedule_of_stores`).
-/

namespace VG.Proof.Camellia.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Camellia.X86_64
open VG.Impl.Aes.X86_64 (q sb t0 t1 movR movS st)
open VG.Proof.Camellia (hiW loW)

/-- The stored subkeys' bytes are their words'. -/
theorem schedule_of_stores {m : Mem} {S : Addr} {ks : List (Nat × Nat × Bool)} {vs : List (BitVec 128)}
    {g : Reg → BitVec 64} (hv : ∀ k ∈ ks, k.1 < 4)
    (hg : ∀ v < 4, g (hiReg v) = hiW (vs.getD v 0) ∧ g (loReg v) = loW (vs.getD v 0))
    (hm : ∀ i < ks.length, ∀ j < 8, m (S + BitVec.ofNat 64 (8 * (0 + i) + j)) =
      Proof.Camellia.byteOf (Proof.Camellia.rotHalf (g (hiReg (ks.getD i (0, 0, true)).1))
        (g (loReg (ks.getD i (0, 0, true)).1)) (ks.getD i (0, 0, true)).2.1 (ks.getD i (0, 0, true)).2.2) j) :
    Spec.Camellia.bytesAt m S (8 * ks.length) =
      (Proof.Camellia.subkeyWords vs ks).flatMap Spec.Camellia.wordBytes := by
  have hl : (Proof.Camellia.subkeyWords vs ks).length = ks.length := by simp [Proof.Camellia.subkeyWords]
  rw [← hl]
  refine bytesAt_words m _ S fun i hi j hj => ?_
  rw [hl] at hi
  rw [show 8 * i + j = 8 * (0 + i) + j by omega, hm i hi j hj]
  have hk : ks.getD i (0, 0, true) = ks[i] := by simp [List.getD_eq_getElem?_getD, hi]
  have h4 := hg ks[i].1 (hv _ (List.getElem_mem hi))
  rw [hk, h4.1, h4.2]
  simp only [Proof.Camellia.subkeyWords, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]

theorem entryW_slot (s : State) (i j : Nat) : entryW s.mem (s.gpr sb) i j = slotW s (keySlot + 8 * i + j) := by
  simp only [entryW, slotW, wordAddr]
  rw [show 8 * (keySlot + 8 * i + j) = 8 * keySlot + 64 * i + 8 * j by omega]

theorem subkeys_lt4 : (∀ k ∈ Impl.Camellia.subkeys128, k.1 < 4) ∧ (∀ k ∈ Impl.Camellia.subkeys256, k.1 < 4) := by
  decide

theorem subkeys_length : Impl.Camellia.subkeys128.length = 26 ∧ Impl.Camellia.subkeys256.length = 34 := by
  decide

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
    (hS : s₈.gpr .rdx = S) (hw : (⟨S, 272⟩ : Region) ∈ s₈.wr) (hv : ∀ k ∈ ks, k.1 < 4)
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
  · rw [hlen, schedule_of_stores (g := s₈.gpr) hv hg (by rw [← hS]; exact b₉), Spec.Camellia.scheduleBytes,
      Proof.Camellia.scheduleWords_expandKey, ← hks']
  · rw [hS] at f₉
    exact f₉.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.sub_base S (by omega)⟩

theorem expandKey_wp {s₀ : State} (hp : expandKeyX86_64.pre s₀) :
    WP isa expandKey s₀ fun s' => gprPreserved s₀ s' ∧ expandKeyX86_64.post s₀ s' := by
  obtain ⟨hrd, hwr, dKS, dKB, dSB, dRS, dRB, fitK, fitS, fitB, hlen⟩ := hp
  obtain ⟨hl', hr', hW, hA, hB, hE, hK, hS⟩ := kaKb_slots
  have ht := tailSlot_eq
  have hd : dataSlot = 369 := rfl
  have hsv : savedSlot = 371 := rfl
  have hwB : (⟨s₀.gpr .rcx, 8 * slots⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  have hwS : (⟨s₀.gpr .rdx, 272⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  have hrK : (⟨s₀.gpr .rdi, (s₀.gpr .rsi).toNat⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  unfold expandKey
  -- The prologue.
  obtain ⟨s₁, e₁, b₁, rsi₁, g₁, sv₁, mk₁, ds₁, ent₁, f₁, rd₁, wr₁⟩ := ekPrologue_ok (b := s₀.gpr .rcx) rfl hwB fitB
  refine WP.seq (WP.of_runBlock ⟨s₁, e₁, ?_⟩)
  have rdi₁ : s₁.gpr .rdi = s₀.gpr .rdi := g₁ _ (by decide) (by decide) (by decide) (by decide)
  have rdx₁ : s₁.gpr .rdx = s₀.gpr .rdx := g₁ _ (by decide) (by decide) (by decide) (by decide)
  -- The key, unchanged so far.
  have hkey₁ : Spec.Camellia.bytesAt s₁.mem (s₁.gpr .rdi) (s₀.gpr .rsi).toNat =
      Spec.Camellia.bytesAt s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat := by
    rw [rdi₁]
    refine Proof.Camellia.bytesAt_congr fun i hi => f₁.bytes (R := ⟨s₀.gpr .rdi, (s₀.gpr .rsi).toNat⟩)
      (fun r hr => ?_) (by simp only; omega) hi
    simp only [List.mem_singleton] at hr; subst hr
    exact dKB.sub_right (Region.sub_prefix (by omega))
  -- `KL` and `KR`.
  refine WP.seq (WP.mono (loadKey_wp (len := (s₀.gpr .rsi).toNat) (s := s₁) (by rw [b₁, wr₁]; exact hwB)
    (by rw [rdi₁, rd₁]; exact hrK) (by rw [rdi₁]; exact fitK) (by rw [rdi₁, b₁]; exact dKB)
    (by rw [rsi₁, BitVec.ofNat_toNat, BitVec.setWidth_eq]) hlen) fun s₂ h₂ => ?_)
  obtain ⟨kl₂, kr₂, sl₂, g₂, f₂, rd₂, wr₂⟩ := h₂
  rw [hkey₁] at kl₂ kr₂
  -- Abbreviations.
  generalize hkey : Spec.Camellia.bytesAt s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat = key at kl₂ kr₂
  have hb₂ : s₂.gpr sb = s₀.gpr .rcx := by rw [g₂ _ (by decide), b₁]
  -- `kp` at the table.
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := movR_ok s₂ kp sb
  obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := addImm_ok s₃ kp (BitVec.ofNat 32 (8 * keySlot))
  refine WP.seq (WP.of_runBlock ⟨s₄, by
    rw [show ([movR kp sb, .alu .add kp (.imm (BitVec.ofNat 32 (8 * keySlot)))] : List Instr) =
      [movR kp sb] ++ [.alu .add kp (.imm (BitVec.ofNat 32 (8 * keySlot)))] from rfl, runBlock_append', e₃,
      Option.bind_some, e₄], ?_⟩)
  have hg₄ : ∀ r, r ≠ kp → s₄.gpr r = s₂.gpr r := fun r hr => by rw [o₄ r hr, o₃ r hr]
  have hb₄ : s₄.gpr sb = s₀.gpr .rcx := by rw [hg₄ _ (by decide), hb₂]
  have hs₄ : ∀ k, slotW s₄ k = slotW s₂ k := slotW_eq_of (by rw [m₄, m₃]) (hg₄ _ (by decide))
  have rdx₄ : s₄.gpr .rdx = s₀.gpr .rdx := by rw [hg₄ _ (by decide), g₂ _ (by decide), rdx₁]
  have wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wr₃, wr₂, wr₁]
  have hlow : ∀ k < klSlot, slotW s₄ k = slotW s₁ k := fun k hk => by
    rw [hs₄, sl₂ k (by omega) (Or.inl hk)]
  let KL : BitVec 64 × BitVec 64 := (hiW (Spec.Camellia.klkr key).1, loW (Spec.Camellia.klkr key).1)
  let KR : BitVec 64 × BitVec 64 := (hiW (Spec.Camellia.klkr key).2, loW (Spec.Camellia.klkr key).2)
  have hpre : KaPre s₄ KL KR := by
    refine ⟨⟨?_, fun k hk => ?_, ?_, ?_, ?_, by decide, fun kv hkv => ?_, fun i hi => ?_⟩, ?_, ?_,
      kl₂.congr (hs₄ _) (hs₄ _), kr₂.congr (hs₄ _) (hs₄ _)⟩
    · rw [hb₄, wr₄']; exact hwB
    · refine ⟨_, by rw [wr₄']; exact hwS, ?_⟩
      rw [rdx₄, wordAddr]; exact VG.Offset.contains_base _ (by omega) (by omega)
    · rw [rdx₄, hb₄]
      exact (dSB.sub_left (Region.sub_prefix (by omega))).sub_right (Region.sub_prefix (by omega))
    · rw [hb₄]; exact fitB
    · rw [rdx₄]; omega
    · have := mask_lt hkv
      rw [hlow _ (by omega)]; exact mk₁ kv hkv
    · refine sigmas_rel (m := s₄.mem) (b := s₄.gpr sb) (fun i hi j hj => ?_) i hi
      rw [entryW_slot, hlow _ (by omega), ← entryW_slot, b₁]
      exact ent₁ i hi j hj
    · rw [rdx₄, hb₄]; exact dSB.sub_left (Region.sub_prefix (by omega))
    · rw [AtEntry, a₄, r₃, hb₄, hb₂, show (BitVec.ofNat 32 (8 * keySlot)).signExtend 64 =
        BitVec.ofNat 64 (8 * keySlot + 64 * 0) from rfl]
  -- `KA` and `KB`.
  refine WP.seq (WP.mono (kaKb_wp hpre) fun s₅ h₅ => ?_)
  have hb₅ : s₅.gpr sb = s₀.gpr .rcx := h₅.base.trans hb₄
  have wr₅ : s₅.wr = s₀.wr := h₅.wr.trans wr₄'
  have hscr₅ : (⟨s₀.gpr .rcx, 8 * slots⟩ : Region) ∈ s₅.wr := by rw [wr₅]; exact hwB
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
  have hsb₆ : ∀ v < 4, sb ≠ hiReg v ∧ sb ≠ loReg v := fun v hv =>
    ⟨(regs_lt4 hv).1.symm, (regs_lt4 hv).2.1.symm⟩
  have hb₆ : s₆.gpr sb = s₀.gpr .rcx := by rw [o₆ _ hsb₆, hb₅]
  -- The key's length.
  obtain ⟨s₇, e₇, a₇, o₇, m₇, rd₇, wr₇⟩ := movS_ok (k := dataSlot) t0 hb₆
    (inRd (scr_in (by rw [wr₆]; exact hscr₅) (by omega)))
  obtain ⟨s₈, e₈, z₈, g₈, m₈, rd₈, wr₈⟩ := cmpImmZ_ok s₇ t0 16
  have hds : slotW s₆ dataSlot = s₀.gpr .rsi := by
    rw [slotW_eq_of m₆ (o₆ _ hsb₆), h₅.keep _ (by omega) (by omega) (Or.inl (by omega)), hs₄,
      sl₂ _ (by omega) (Or.inl (by omega)), ds₁]
  have hz₈ : s₈.zf = some (decide ((s₀.gpr .rsi).toNat = 16)) := by
    rw [z₈, a₇, hds, show (16 : BitVec 32).signExtend 64 = BitVec.ofNat 64 16 from rfl]
    conv => lhs; rw [show s₀.gpr .rsi = BitVec.ofNat 64 (s₀.gpr .rsi).toNat by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]]
    rw [VG.Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]
  refine WP.seq (WP.of_runBlock ⟨s₈, by
    rw [runBlock_append', e₆, Option.bind_some,
      show ([movS t0 dataSlot, .alu .cmp t0 (.imm 16)] : List Instr) =
        [movS t0 dataSlot] ++ [.alu .cmp t0 (.imm 16)] from rfl,
      runBlock_append', e₇, Option.bind_some, e₈], ?_⟩)
  -- The subkeys.
  have hrdx₈ : s₈.gpr .rdx = s₀.gpr .rdx := by
    rw [g₈, o₇ _ (by decide), o₆ _ (fun v hv => by
      rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega) with rfl | rfl | rfl | rfl <;> decide),
      h₅.rdx, rdx₄]
  have hwS₈ : (⟨s₀.gpr .rdx, 272⟩ : Region) ∈ s₈.wr := by rw [wr₈, wr₇, wr₆, wr₅]; exact hwS
  have hg₈ : ∀ v < 4, s₈.gpr (hiReg v) = hiW ([(Spec.Camellia.klkr key).1, (Spec.Camellia.klkr key).2,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).1,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).2].getD v 0) ∧
      s₈.gpr (loReg v) = loW ([(Spec.Camellia.klkr key).1, (Spec.Camellia.klkr key).2,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).1,
        (Spec.Camellia.kakb (Spec.Camellia.klkr key).1 (Spec.Camellia.klkr key).2).2].getD v 0) :=
    fun v hv => by
      obtain ⟨n1, -, n3, -⟩ := hiReg_ne v hv
      rw [g₈, o₇ _ n1, o₇ _ n3]; exact v₆ v hv
  have hklen : key.length = (s₀.gpr .rsi).toNat := by rw [← hkey]; simp [Spec.Camellia.bytesAt]
  refine WP.seq (WP.mono (Q := StoresPost s₈ (s₀.gpr .rdx) (s₀.gpr .rsi).toNat key)
    (WP.ite (decide ((s₀.gpr .rsi).toNat = 16)) (by simp [X86_64.eval, hz₈]) (fun h16 => ?_) (fun h16 => ?_))
    fun s₉ h₉ => ?_)
  · have h16 : (s₀.gpr .rsi).toNat = 16 := by simpa using h16
    exact stores_wp hrdx₈ hwS₈ subkeys_lt4.1 (by rw [subkeys_length.1]; omega) hg₈
      (by rw [h16, subkeys_length.1]; rfl) (by rw [hklen, ite_eq_left h16])
  · have h16 : (s₀.gpr .rsi).toNat ≠ 16 := by simpa using h16
    exact stores_wp hrdx₈ hwS₈ subkeys_lt4.2 (by rw [subkeys_length.2]) hg₈
      (by rw [subkeys_length.2]; simp only [Spec.Camellia.rounds, h16, ↓reduceIte]; rfl)
      (by rw [hklen, ite_eq_right h16])
  -- The epilogue.
  have hb₉ : s₉.gpr sb = s₀.gpr .rcx := by rw [h₉.regs _ (by decide) (by decide), g₈, o₇ _ (by decide), hb₆]
  have hSB : ∀ k, savedSlot ≤ k → k < savedSlot + 6 →
      s₉.mem.readW (wordAddr (s₀.gpr .rcx) k) 64 = s₁.mem.readW (wordAddr (s₀.gpr .rcx) k) 64 := by
    intro k h1 h2
    rw [h₉.frame.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (dSB.sub_right (by rw [wordAddr]; exact VG.Offset.sub_base _ (by omega))).symm) (by decide)]
    have := h₅.keep k (by omega) (by omega) (Or.inl (by omega))
    rw [hs₄, sl₂ k (by omega) (Or.inl (by omega))] at this
    simp only [slotW, hb₅, b₁] at this
    rw [m₈, m₇, m₆]
    exact this
  obtain ⟨s₁₀, e₁₀, rg₁₀, o₁₀, f₁₀, rd₁₀, wr₁₀⟩ := restore_ok (s₀ := s₀) (b := s₀.gpr .rcx)
    (by rw [h₉.wr, wr₈, wr₇, wr₆, wr₅]; exact hwB) hb₉ (fun i hi => by
      rw [hSB _ (by omega) (by omega)]; exact sv₁ i hi)
  refine WP.of_runBlock ⟨s₁₀, e₁₀, ⟨fun r hr => ?_, ?_⟩, ?_⟩
  · have hsp : s₁₀.gpr .rsp = s₀.gpr .rsp := by
      rw [o₁₀ _ (fun i hi => by unfold sreg; split <;> decide), h₉.regs _ (by decide) (by decide), g₈,
        o₇ _ (by decide), o₆ _ (fun v hv => by
          rcases (show v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 by omega) with rfl | rfl | rfl | rfl <;> decide),
        h₅.regs _ (by decide) (by decide) (by decide) (by decide), hg₄ _ (by decide), g₂ _ (by decide),
        g₁ _ (by decide) (by decide) (by decide) (by decide)]
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rg₁₀ 0 (by omega)
    · exact rg₁₀ 1 (by omega)
    · exact hsp
    · exact rg₁₀ 2 (by omega)
    · exact rg₁₀ 3 (by omega)
    · exact rg₁₀ 4 (by omega)
    · exact rg₁₀ 5 (by omega)
  · -- The return address is untouched.
    have fr : Frame [⟨s₀.gpr .rcx, 8 * slots⟩, ⟨s₀.gpr .rdx, 272⟩] s₀.mem s₁₀.mem := by
      have F₁ : Frame [⟨s₀.gpr .rcx, 8 * slots⟩, ⟨s₀.gpr .rdx, 272⟩] s₀.mem s₁.mem :=
        f₁.sub fun r hr => ⟨_, List.mem_cons_self, by
          simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)⟩
      have F₂ : Frame [⟨s₀.gpr .rcx, 8 * slots⟩, ⟨s₀.gpr .rdx, 272⟩] s₁.mem s₄.mem := by
        rw [m₄, m₃]; rw [b₁] at f₂
        exact f₂.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
      have F₅ : Frame [⟨s₀.gpr .rcx, 8 * slots⟩, ⟨s₀.gpr .rdx, 272⟩] s₄.mem s₅.mem := by
        have := h₅.frame; rw [hb₄, rdx₄] at this
        exact this.sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
          · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by omega)⟩
      have F₉ : Frame [⟨s₀.gpr .rcx, 8 * slots⟩, ⟨s₀.gpr .rdx, 272⟩] s₅.mem s₉.mem := by
        rw [← m₆, ← m₇, ← m₈]
        exact h₉.frame.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
      have F₁₀ : Frame [⟨s₀.gpr .rcx, 8 * slots⟩, ⟨s₀.gpr .rdx, 272⟩] s₉.mem s₁₀.mem :=
        f₁₀.sub fun r hr => ⟨_, List.mem_cons_self, by
          simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)⟩
      exact F₁.trans (F₂.trans (F₅.trans (F₉.trans F₁₀)))
    refine fr.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact dRB
    · exact dRS
  · show Spec.Camellia.bytesAt s₁₀.mem (s₀.gpr .rdx) _ = _
    rw [hkey, ← h₉.bytes]
    have hle := Proof.Camellia.scheduleLength_rounds_le (s₀.gpr .rsi).toNat
    refine Proof.Camellia.bytesAt_congr fun i hi => f₁₀.bytes (R := ⟨s₀.gpr .rdx, 272⟩) (fun r hr => ?_)
      (by simp only; omega) (by simp only; omega)
    simp only [List.mem_singleton] at hr; subst hr
    exact dSB.sub_right (Region.sub_prefix (by omega))

end VG.Proof.Camellia.X86_64

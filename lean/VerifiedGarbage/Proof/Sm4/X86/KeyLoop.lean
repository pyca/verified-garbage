import VerifiedGarbage.Proof.Sm4.X86.KeyInit

/-!
# The loop of the SM4 key schedule on x86 (32-bit)

As on ARMv7 (`Proof/Sm4/Arm/KeyLoop.lean`): each iteration runs four rounds
of the key schedule, puts the state's words in the tail buffer as a block
(`fromBs_step`), and stores them to the schedule as little-endian words
(`extract_ok`): the first block's words, last first, byte-reversed
(`bswap`). The schedule's pointer waits in slot `nSlot` (the rounds use
every register).
-/

namespace VG.Proof.Sm4.X86

open VG VG.X86 VG.X86.Straight VG.Impl.Sm4.X86
open VG.Impl.Aes.X86 (sb slotAt st movS addI at_)
open VG.Proof.Sm4 (writeW32_byte writeW32_other)

theorem out_of_disj {r₁ r₂ : Region} (hd : r₁.Disjoint r₂) {x a : Addr} {n : Nat} (hx : r₁.Contains x 1)
    (ha : r₂.Contains a n) : ¬ (x - a).toNat < n := fun h => hd x hx (ha.byte h)

/-! ## The extraction -/

/-- The extraction, after its first `k` words: the schedule's bytes at `P`
before `4 k` hold the tail buffer's first block, last byte first. -/
structure ExtInv (s₀ : State) (b P : BitVec 32) (k : Nat) (s : State) : Prop where
  base : s.gpr sb = b
  ptr : s.gpr .ecx = P
  bytes : ∀ t < 4 * k, ∀ j < 8, (s.mem (P.setWidth 64 + BitVec.ofNat 64 t)).getLsbD j =
    ((tailBlock s₀ 0).getD (15 - t) 0).getLsbD j
  frame : Frame [⟨P.setWidth 64, 4 * k⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .eax → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The extraction's word `k`. -/
theorem extStep_ok {s₀ s : State} {b P : BitVec 32} {k : Nat} (hk : k < 4)
    (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) (hP : P.toNat + 16 ≤ 2 ^ 32)
    (hw : ScrIn s₀.wr b) (hS : ∀ t < 4, InRegions s₀.wr (P.setWidth 64 + BitVec.ofNat 64 (4 * t)) 4)
    (hsep : Region.Disjoint ⟨P.setWidth 64, 16⟩ ⟨b.setWidth 64, 4 * slots⟩) (hb₀ : s₀.gpr sb = b)
    (hi : ExtInv s₀ b P k s) :
    ∃ s', runBlock isa [movS .eax (tailAt 0 (3 - k)), .bswap .eax, .store (at_ .ecx (4 * k)) .eax] s = some s' ∧
      ExtInv s₀ b P (k + 1) s' := by
  have hb := setWidth_toNat b
  have hPn := setWidth_toNat P
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, -, -⟩ := ldSlot_ok s .eax .edi (k := tailAt 0 (3 - k)) hi.base
    (tailAt_lt (by decide) (by omega_arith)) (by rw [hi.wr]; exact hw)
  let s₂ := s₁.setReg .eax (bswap (s₁.gpr .eax))
  have e₂ : runBlock isa [.bswap .eax] s₁ = some s₂ := by
    rw [runBlock_cons, show exec (.bswap .eax) s₁ = some s₂ from rfl, runStep_some, runBlock_nil]
  have ecx₂ : s₂.gpr .ecx = P := by rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), o₁ _ (by decide), hi.ptr]
  have eA : s₂.ea (at_ .ecx (4 * k)) = P.setWidth 64 + BitVec.ofNat 64 (4 * k) := by
    show (s₂.gpr .ecx + BitVec.ofNat 32 (4 * k)).setWidth 64 = _
    rw [ecx₂]; exact setWidth_add (by omega_arith)
  have wr₂ : s₂.wr = s₀.wr := by show s₁.wr = _; rw [wr₁, hi.wr]
  have hin : InRegions s₂.wr (P.setWidth 64 + BitVec.ofNat 64 (4 * k)) 4 := by rw [wr₂]; exact hS k hk
  -- The slot read is the one on entry.
  have hslot : s.mem.readW (wordAddr b (tailAt 0 (3 - k))) 32 = s₀.mem.readW (wordAddr b (tailAt 0 (3 - k))) 32 := by
    have hk' := tailAt_lt (c := 0) (w := 3 - k) (by decide) (by omega_arith)
    rw [slot_addr (by omega_arith)]
    refine hi.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact ((hsep.sub_left (Region.sub_prefix (by omega_arith))).sub_right
      (VG.Offset.sub_base _ (by omega_arith))).symm
  have v₂ : s₂.gpr .eax = bswap (s₀.mem.readW (wordAddr b (tailAt 0 (3 - k))) 32) := by
    rw [RegUpd.gpr_setReg_self, v₁, hslot]
  let s₃ : State := { s₂ with mem := s₂.mem.writeW (P.setWidth 64 + BitVec.ofNat 64 (4 * k)) (s₂.gpr .eax) }
  have e₃ : runBlock isa [.store (at_ .ecx (4 * k)) .eax] s₂ = some s₃ := by
    rw [runBlock_cons]
    simp only [exec, State.store32, eA, hin, ↓reduceIte, runStep_some, runBlock_nil, s₃]
  have mem₂ : s₂.mem = s.mem := m₁
  refine ⟨s₃, ?_, ⟨by show s₂.gpr sb = b; rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), o₁ _ (by decide), hi.base],
    ecx₂, fun t ht j hj => ?_, ?_, fun r hr => ?_, by show s₁.rd = _; rw [rd₁, hi.rd], wr₂⟩⟩
  · rw [show ([movS .eax (tailAt 0 (3 - k)), .bswap .eax, .store (at_ .ecx (4 * k)) .eax] : List Instr) =
      [.mov .eax (.mem (slotAt .edi (tailAt 0 (3 - k))))] ++ ([.bswap .eax] ++ [.store (at_ .ecx (4 * k)) .eax])
      from rfl, runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, e₃]
  · show (s₂.mem.writeW _ _ _).getLsbD j = _
    by_cases hlt : t < 4 * k
    · rw [writeW32_other _ _ _ _ (VG.Proof.Sm4.off_sub_not _ (Or.inl hlt) (by omega_arith) (by decide) (by omega_arith)),
        mem₂]
      exact hi.bytes t hlt j hj
    · have hc : t - 4 * k < 4 := by omega_arith
      rw [show P.setWidth 64 + BitVec.ofNat 64 t =
          P.setWidth 64 + BitVec.ofNat 64 (4 * k) + BitVec.ofNat 64 (t - 4 * k) by
        rw [VG.Offset.add_add, show 4 * k + (t - 4 * k) = t by omega_arith],
        writeW32_byte _ _ _ hc hj, v₂, bswap_bit _ hc hj,
        tailBlock_bit s₀ (c := 0) (i := 15 - t) hb₀ hfit (by decide) (by omega_arith) hj,
        show (15 - t) / 4 = 3 - k by omega_arith, show (15 - t) % 4 = 3 - (t - 4 * k) by omega_arith]
  · refine (hi.frame.sub fun r hr => ⟨⟨P.setWidth 64, 4 * (k + 1)⟩, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega_arith)⟩).trans ?_
    show Frame _ s.mem (s₂.mem.writeW _ _)
    rw [mem₂]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Offset.contains_base _ (by omega_arith) (by omega_arith))
  · show (s₁.setReg .eax _).gpr r = _
    rw [RegUpd.gpr_setReg_of_ne _ _ hr, o₁ r hr, hi.regs r hr]

/-- The schedule's bytes `16 m … 16 m + 15`: the words of the tail buffer's
first block, the last first, each little-endian; the schedule's pointer
stepped. -/
theorem extract_ok {s : State} {b S : BitVec 32} {m : Nat} (hm : m < 8) (hb : s.gpr sb = b) (hw : ScrIn s.wr b)
    (hSfit : S.toNat + 128 ≤ 2 ^ 32) (hS : (⟨S.setWidth 64, 128⟩ : Region) ∈ s.wr)
    (hsep : Region.Disjoint ⟨S.setWidth 64, 128⟩ ⟨b.setWidth 64, 4 * slots⟩)
    (hn : s.mem.readW (wordAddr b nSlot) 32 = S + BitVec.ofNat 32 (16 * m)) :
    ∃ s', runBlock isa extract s = some s' ∧
      (∀ t < 16, ∀ j < 8, (s'.mem (S.setWidth 64 + BitVec.ofNat 64 (16 * m + t))).getLsbD j =
        ((tailBlock s 0).getD (15 - t) 0).getLsbD j) ∧
      s'.mem.readW (wordAddr b nSlot) 32 = S + BitVec.ofNat 32 (16 * (m + 1)) ∧
      Frame [⟨S.setWidth 64 + BitVec.ofNat 64 (16 * m), 16⟩, ⟨wordAddr b nSlot, 4⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hfit := hw.fit
  have hSn := setWidth_toNat S
  let P := S + BitVec.ofNat 32 (16 * m)
  have hPa : P.setWidth 64 = S.setWidth 64 + BitVec.ofNat 64 (16 * m) := setWidth_add (by omega_arith)
  have hPn : P.toNat + 16 ≤ 2 ^ 32 := by rw [toNat_add32 _ (by omega_arith)]; omega_arith
  have subP : Region.Sub ⟨P.setWidth 64, 16⟩ ⟨S.setWidth 64, 128⟩ := by
    rw [hPa]; exact VG.Offset.sub_base _ (by omega_arith)
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, -, -⟩ := ldSlot_ok s .ecx .edi (k := nSlot) hb (by decide) hw
  rw [hn] at v₁
  have hb₁ : s₁.gpr sb = b := by rw [o₁ _ (by decide)]; exact hb
  have hw₁ : ScrIn s₁.wr b := by rw [wr₁]; exact hw
  have hS₁ : ∀ t < 4, InRegions s₁.wr (P.setWidth 64 + BitVec.ofNat 64 (4 * t)) 4 := fun t ht =>
    ⟨_, by rw [wr₁]; exact hS, by rw [hPa, VG.Offset.add_add]; exact VG.Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have hsepP : Region.Disjoint ⟨P.setWidth 64, 16⟩ ⟨b.setWidth 64, 4 * slots⟩ := hsep.sub_left subP
  have i0 : ExtInv s₁ b P 0 s₁ := ⟨hb₁, v₁, fun t ht => by omega_arith, Frame.refl _ _, fun _ _ => rfl, rfl, rfl⟩
  obtain ⟨s₂, e₂, i₂⟩ := extStep_ok (k := 0) (by decide) hfit hPn hw₁ hS₁ hsepP hb₁ i0
  obtain ⟨s₃, e₃, i₃⟩ := extStep_ok (k := 1) (by decide) hfit hPn hw₁ hS₁ hsepP hb₁ i₂
  obtain ⟨s₄, e₄, i₄⟩ := extStep_ok (k := 2) (by decide) hfit hPn hw₁ hS₁ hsepP hb₁ i₃
  obtain ⟨s₅, e₅, i₅⟩ := extStep_ok (k := 3) (by decide) hfit hPn hw₁ hS₁ hsepP hb₁ i₄
  obtain ⟨s₆, e₆, r₆, -, o₆, m₆, rd₆, wr₆⟩ := addI_ok s₅ .ecx 16
  obtain ⟨s₇, e₇, m₇, g₇, rd₇, wr₇, -, -, f₇⟩ := stSlot_ok s₆ .ecx .edi (b := b) (k := nSlot)
    (by rw [o₆ _ (by decide)]; exact i₅.base) (by decide) (by rw [wr₆, i₅.wr, wr₁]; exact hw)
  have hmem₇ : s₇.mem = s₅.mem.writeW (wordAddr b nSlot) (P + BitVec.ofNat 32 16) := by
    rw [m₇, m₆, r₆, i₅.ptr]; rfl
  have hblk : tailBlock s₁ 0 = tailBlock s 0 := by simp only [tailBlock, m₁, hb₁, hb]
  have dN : Region.Disjoint ⟨P.setWidth 64, 16⟩ ⟨wordAddr b nSlot, 4⟩ :=
    hsepP.sub_right (slot_sub hfit (by decide))
  refine ⟨s₇, ?_, fun t ht j hj => ?_, ?_, ?_, fun r h0 h7 => ?_, by rw [rd₇, rd₆, i₅.rd, rd₁],
    by rw [wr₇, wr₆, i₅.wr, wr₁]⟩
  · rw [extract, show (List.range 4).flatMap (fun k => ([movS .eax (tailAt 0 (3 - k)), .bswap .eax,
        .store (at_ .ecx (4 * k)) .eax] : List Instr)) =
        [movS .eax (tailAt 0 (3 - 0)), .bswap .eax, .store (at_ .ecx (4 * 0)) .eax] ++
        ([movS .eax (tailAt 0 (3 - 1)), .bswap .eax, .store (at_ .ecx (4 * 1)) .eax] ++
        ([movS .eax (tailAt 0 (3 - 2)), .bswap .eax, .store (at_ .ecx (4 * 2)) .eax] ++
        [movS .eax (tailAt 0 (3 - 3)), .bswap .eax, .store (at_ .ecx (4 * 3)) .eax])) from rfl,
      show ([addI .ecx 16, st nSlot .ecx] : List Instr) =
        [addI .ecx 16] ++ [.store (slotAt .edi nSlot) .ecx] from rfl,
      runBlock_app, runBlock_app,
      show ([movS .ecx nSlot] : List Instr) = [.mov .ecx (.mem (slotAt .edi nSlot))] from rfl, e₁,
      Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some, runBlock_app, e₄,
      Option.bind_some, e₅, Option.bind_some, runBlock_app, e₆, Option.bind_some, e₇]
  · have hx : (⟨P.setWidth 64, 16⟩ : Region).Contains (P.setWidth 64 + BitVec.ofNat 64 t) 1 :=
      VG.Offset.contains_base _ (by omega_arith) (by omega_arith)
    rw [show S.setWidth 64 + BitVec.ofNat 64 (16 * m + t) = P.setWidth 64 + BitVec.ofNat 64 t by
        rw [hPa, VG.Offset.add_add],
      hmem₇, writeW32_other _ _ _ _ (out_of_disj dN hx (Region.contains_self _ _)), i₅.bytes t (by omega_arith) j hj,
      hblk]
  · rw [hmem₇, Mem.readW_writeW_self32]
    simp only [P]
    rw [VG.Offset.add_add, show 16 * m + 16 = 16 * (m + 1) by omega_arith]
  · rw [← m₁]
    refine (i₅.frame.sub fun r hr => ⟨_, List.mem_cons_self, by
      simp only [List.mem_singleton] at hr; subst hr; rw [hPa]; exact fun _ h => h⟩).trans ?_
    rw [← m₆]
    exact f₇.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  · rw [g₇, o₆ r h7, i₅.regs r h0, o₁ r h7]

end VG.Proof.Sm4.X86

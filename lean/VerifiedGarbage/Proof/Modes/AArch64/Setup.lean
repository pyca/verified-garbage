import VerifiedGarbage.Proof.Modes.AArch64.Counter

/-!
# CTR on AArch64: entry and exit

`setup_ok`: the entry block of `ctr` moves the scratch buffer to `sb`,
stores the callee-saved registers in the mode's slots, reads the counter
block `T₁` at `r.ctr` (a number `V`, big-endian) into the running counter's
slots, as `hiOf V` and `loOf V`, and writes `T₁ + n` back. `ctrArgs_ok`:
the data's address and `n` to the registers the core keeps.
-/

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Aes.AArch64 (sb movR ldS stS)
open VG.Spec.Aes (bytesAt)

/-- The counter block at `P`, as a number. -/
abbrev ctrVal (m : Mem) (P : Addr) : Nat := Spec.Ctr.toNat (bytesAt m P 16)

/-- Its halves are the byte-reversed words at `P` and `P + 8`. -/
theorem halves (m : Mem) (P : Addr) :
    hiOf (ctrVal m P) = rev64 (m.readW P 64) ∧
      loOf (ctrVal m P) = rev64 (m.readW (P + BitVec.ofNat 64 8) 64) := by
  have h := AesCtr.toNat_append (bytesAt m P 8) (bytesAt m (P + BitVec.ofNat 64 8) 8)
  rw [← AesCtr.bytesAt_append, AesCtr.bytesAt_rv64, AesCtr.bytesAt_rv64, AesCtr.toNat_ofNat, AesCtr.toNat_ofNat,
    AesCtr.length_ofNat] at h
  have a1 := (AesCtr.rv64 (m.readW P 64)).isLt
  have a2 := (AesCtr.rv64 (m.readW (P + BitVec.ofNat 64 8) 64)).isLt
  simp only [Nat.reducePow] at a1 a2 h
  rw [Nat.mod_eq_of_lt a1, Nat.mod_eq_of_lt a2] at h
  constructor
  · apply BitVec.eq_of_toNat_eq
    rw [hiOf, BitVec.toNat_ofNat, ctrVal, h, show rev64 (m.readW P 64) = AesCtr.rv64 (m.readW P 64) from rfl]
    omega
  · apply BitVec.eq_of_toNat_eq
    rw [loOf, BitVec.toNat_ofNat, ctrVal, h,
      show rev64 (m.readW (P + BitVec.ofNat 64 8) 64) = AesCtr.rv64 (m.readW (P + BitVec.ofNat 64 8) 64) from rfl]
    omega

/-- `bytesAt` of the two words written at `P + 8` and then `P`: the
big-endian bytes of `V`. -/
theorem bytes_pair2 (m : Mem) (P : Addr) (V : Nat) :
    bytesAt ((m.writeW (P + BitVec.ofNat 64 8) (rev64 (loOf V))).writeW P (rev64 (hiOf V))) P 16 =
      Spec.Ctr.ofNat V 16 := by
  rw [show (16 : Nat) = 8 + 8 from rfl, AesCtr.bytesAt_append,
    show (rev64 (hiOf V)) = AesCtr.rv64 (hiOf V) from rfl, AesCtr.bytesAt_writeW_rv64,
    AesCtr.bytesAt_writeW_sep _ _ _ (by decide) (by decide),
    show (rev64 (loOf V)) = AesCtr.rv64 (loOf V) from rfl, AesCtr.bytesAt_writeW_rv64, AesCtr.ofNat_add]
  congr 1
  · exact AesCtr.ofNat_congr (by simp only [hiOf, BitVec.toNat_ofNat]; omega)
  · exact AesCtr.ofNat_congr (by simp only [loOf, BitVec.toNat_ofNat]; omega)

/-! ## Words to and from consecutive slots -/

/-- `k` stores of registers to consecutive slots from `base`. -/
theorem stores_ok {B : Addr} (base : Nat) (g : Nat → Reg) : ∀ (k : Nat) (s : State), s.gpr sb = B →
    (∀ i < k, InRegions s.wr (wordAddr B (base + i)) 8) → 8 * (base + k) < 32768 →
    ∃ s', runBlock isa ((List.range k).map fun i => stS (base + i) (g i)) s = some s' ∧
      (∀ i < k, s'.mem.readW (wordAddr B (base + i)) 64 = s.gpr (g i)) ∧
      Frame [⟨wordAddr B base, 8 * k⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | 0, s, _, _, _ => ⟨s, rfl, fun i hi => by omega, Frame.refl _ _, rfl, rfl, rfl⟩
  | k + 1, s, hB, hw, hk => by
    obtain ⟨s₁, e₁, v₁, f₁, g₁, rd₁, wr₁⟩ := stores_ok base g k s hB (fun i hi => hw i (by omega)) (by omega)
    obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := stS_ok (s := s₁) (b := B) (k := base + k) (g k) (by rw [g₁, hB])
      (by omega) (by rw [wr₁]; exact hw k (by omega))
    refine ⟨s₂, ?_, fun i hi => ?_, ?_, by rw [g₂, g₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
    · rw [List.range_succ, List.map_append, runBlock_app, e₁, Option.bind_some, List.map_singleton, e₂]
    · rw [m₂, readW_slot_write _ (by omega) (by omega), g₁]
      split
      · rename_i h; rw [show i = k by omega]
      · exact v₁ i (by omega)
    · rw [m₂]
      refine (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _ ?_
      · simp only [List.mem_singleton] at hr; subst hr
        exact VG.Offset.sub B (by omega) (by omega)
      · exact VG.Offset.contains B (by omega) (by omega) (by omega)

/-- `k` loads of consecutive slots from `base` to distinct registers other
than `sb`. -/
theorem loads_ok {B : Addr} (base : Nat) (g : Nat → Reg) : ∀ (k : Nat) (s : State), s.gpr sb = B →
    (∀ i < k, g i ≠ sb) → (∀ i < k, ∀ j < k, g i = g j → i = j) → 8 * (base + k) < 32768 →
    (∀ i < k, InRegions (s.rd ++ s.wr) (wordAddr B (base + i)) 8) →
    ∃ s', runBlock isa ((List.range k).map fun i => ldS (g i) (base + i)) s = some s' ∧
      (∀ i < k, s'.gpr (g i) = s.mem.readW (wordAddr B (base + i)) 64) ∧
      (∀ r, (∀ i < k, r ≠ g i) → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | 0, s, _, _, _, _, _ => ⟨s, rfl, fun i hi => by omega, fun _ _ => rfl, rfl, rfl, rfl⟩
  | k + 1, s, hB, hsb, hinj, hk, hr => by
    obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := loads_ok base g k s hB (fun i hi => hsb i (by omega))
      (fun i hi j hj => hinj i (by omega) j (by omega)) (by omega) (fun i hi => hr i (by omega))
    have hB₁ : s₁.gpr sb = B := by
      rw [o₁ _ (fun i hi h => hsb i (by omega) h.symm), hB]
    obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂⟩ := ldS_ok (s := s₁) (b := B) (k := base + k) (g k) hB₁ (by omega)
      (by rw [rd₁, wr₁]; exact hr k (by omega))
    refine ⟨s₂, ?_, fun i hi => ?_, fun r hr' => ?_, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
    · rw [List.range_succ, List.map_append, runBlock_app, e₁, Option.bind_some, List.map_singleton, e₂]
    · by_cases h : i = k
      · subst h; rw [v₂, m₁]
      · rw [o₂ _ (fun he => h (hinj i hi k (by omega) he)), v₁ i (by omega)]
    · rw [o₂ r (hr' k (by omega)), o₁ r (fun i hi => hr' i (by omega))]

/-! ## Entry -/

/-- The mode's slots. -/
abbrev modeRegion (c : Core) (B : Addr) : Region := ⟨B + BitVec.ofNat 64 (8 * c.slots), 96⟩

theorem ctrSetup_eq (c : Core) (r : CtrRegs) : c.ctrSetup r =
    ([.ldr .x .x6 r.ctr 0] : List Instr) ++ (([.rev .x6 .x6] : List Instr) ++
      (([.ldr .x .x7 r.ctr 8] : List Instr) ++ (([.rev .x7 .x7] : List Instr) ++
      (([stS c.hiSlot .x6] : List Instr) ++ (([stS c.loSlot .x7] : List Instr) ++
      (([.movz .x .x10 (BitVec.ofNat 16 0) 0] : List Instr) ++
      (([.adds .x .x7 .x7 r.n, .adc .x .x6 .x6 .x10] : List Instr) ++
      (([.rev .x6 .x6] : List Instr) ++ (([.rev .x7 .x7] : List Instr) ++
      (([.str .x .x7 r.ctr 8] : List Instr) ++ ([.str .x .x6 r.ctr 0] : List Instr))))))))))) := rfl

theorem ctrEntry_eq (c : Core) (r : CtrRegs) : c.ctrEntry r =
    ([movR sb r.scr] : List Instr) ++ ((List.range 10).map fun i => stS (c.slots + i) (Core.savedRegs.getD i .x19)) :=
  rfl

/-- The registers of a mode's arguments: none of them `sb`, nor a register
the entry writes (`x6`, `x7`, `x10`). -/
def SetupRegs : List Reg := [sb, .x6, .x7, .x10]

structure RegsOk (r : CtrRegs) : Prop where
  ctr : r.ctr ∉ SetupRegs
  data : r.data ∉ SetupRegs
  n : r.n ∉ SetupRegs

theorem not_setupRegs {r : Reg} (h : r ∉ SetupRegs) : r ≠ sb ∧ r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x10 := by
  simp only [SetupRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  exact h

variable {c : Core}

/-- The entry block. -/
theorem setup_ok (hL : Layout c) {r : CtrRegs} (hr : RegsOk r) (s : State) {B P : Addr}
    (hB : s.gpr r.scr = B) (hs : ScrIn s B c.total) (hP : s.gpr r.ctr = P) (hwP : (⟨P, 16⟩ : Region) ∈ s.wr)
    (hsep : Region.Disjoint ⟨P, 16⟩ ⟨B, 8 * c.total⟩) :
    ∃ s', runBlock isa (c.ctrEntry r ++ c.ctrSetup r) s = some s' ∧ s'.gpr sb = B ∧
      (∀ i < 10, s'.mem.readW (wordAddr B (c.slots + i)) 64 = s.gpr (Core.savedRegs.getD i .x19)) ∧
      s'.mem.readW (wordAddr B c.hiSlot) 64 = hiOf (ctrVal s.mem P) ∧
      s'.mem.readW (wordAddr B c.loSlot) 64 = loOf (ctrVal s.mem P) ∧
      bytesAt s'.mem P 16 = Spec.Ctr.ofNat (ctrVal s.mem P + (s.gpr r.n).toNat) 16 ∧
      Frame [modeRegion c B, ⟨P, 16⟩] s.mem s'.mem ∧
      (∀ x, x ∉ SetupRegs → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hsm := hL.small
  have hroom := hL.room
  have hN : 8 * c.total < 2 ^ 64 := by omega
  have sl : ∀ k, c.slots ≤ k → k < c.total → InRegions s.wr (wordAddr B k) 8 := fun k _ hk =>
    slot_wr hs.wr hN hk
  have p0 : P + BitVec.ofNat 64 0 = P := by simp
  obtain ⟨cs, c6, c7, c10⟩ := not_setupRegs hr.ctr
  obtain ⟨ns, n6, n7, n10⟩ := not_setupRegs hr.n
  -- The scratch buffer to `sb`.
  obtain ⟨s₁, e₁, b₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s sb r.scr
  have b₁' : s₁.gpr sb = B := by rw [b₁, hB]
  -- The callee-saved registers.
  obtain ⟨s₂, e₂, v₂, f₂, g₂, rd₂, wr₂⟩ := stores_ok (B := B) c.slots (fun i => Core.savedRegs.getD i .x19) 10 s₁
    b₁' (fun i hi => by rw [wr₁]; exact sl _ (by omega) (by omega)) (by omega)
  have wr₂' : s₂.wr = s.wr := by rw [wr₂, wr₁]
  have rd₂' : s₂.rd = s.rd := by rw [rd₂, rd₁]
  have keep₂ : ∀ x, x ≠ sb → s₂.gpr x = s.gpr x := fun x hx => by rw [g₂, o₁ x hx]
  have P₂ : s₂.gpr r.ctr = P := by rw [keep₂ _ cs, hP]
  have fe : Frame [modeRegion c B] s.mem s₂.mem := by
    rw [← m₁]
    exact f₂.sub fun x hx => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hx; subst hx
      exact VG.Offset.sub B (by omega) (by omega)⟩
  have dP : ∀ k, c.slots ≤ k → k < c.total → ∀ x ∈ [(⟨P, 16⟩ : Region)],
      Region.Disjoint ⟨wordAddr B k, 8⟩ x := fun k h1 h2 x hx => by
    simp only [List.mem_singleton] at hx; subst hx
    exact (hsep.sub_right (VG.Offset.sub_base B (by omega))).symm
  -- The counter.
  have inP : ∀ d, d + 8 ≤ 16 → InRegions s.wr (P + BitVec.ofNat 64 d) 8 := fun d hd =>
    ⟨_, hwP, VG.Offset.contains_base P hd (by omega)⟩
  obtain ⟨hv, lv⟩ := halves s.mem P
  let V := ctrVal s.mem P
  have mP : ∀ d, d + 8 ≤ 16 →
      s₂.mem.readW (P + BitVec.ofNat 64 d) 64 = s.mem.readW (P + BitVec.ofNat 64 d) 64 := fun d hd =>
    fe.readW (r := ⟨P, 16⟩) (VG.Offset.contains_base P (by omega) (by omega)) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      exact hsep.sub_right (VG.Offset.sub_base B (by omega))) (by decide)
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := ldr_ok s₂ .x6 r.ctr (off := 0) (by decide)
    (by rw [rd₂', wr₂', P₂]; exact inRd (inP 0 (by decide)))
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := rev_ok s₃ .x6 .x6
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := ldr_ok s₄ .x7 r.ctr (off := 8) (by decide)
    (by rw [rd₄, wr₄, rd₃, wr₃, rd₂', wr₂', o₄ _ (Ne.symm c6).symm, o₃ _ c6, P₂]; exact inRd (inP 8 (by decide)))
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆⟩ := rev_ok s₅ .x7 .x7
  have g₆ : ∀ x, x ≠ .x6 → x ≠ .x7 → s₆.gpr x = s₂.gpr x := fun x h1 h2 => by
    rw [o₆ x h2, o₅ x h2, o₄ x h1, o₃ x h1]
  have mP0 := mP 0 (by decide)
  rw [p0] at mP0
  have x6₆ : s₆.gpr .x6 = hiOf V := by
    rw [o₆ _ (by decide), o₅ _ (by decide), r₄, r₃, P₂, p0, mP0, hv]
  have x7₆ : s₆.gpr .x7 = loOf V := by
    rw [r₆, r₅, m₄, m₃, o₄ _ c6, o₃ _ c6, P₂, mP 8 (by decide), lv]
  have wr₆' : s₆.wr = s.wr := by rw [wr₆, wr₅, wr₄, wr₃, wr₂']
  have rd₆' : s₆.rd = s.rd := by rw [rd₆, rd₅, rd₄, rd₃, rd₂']
  have b₆ : s₆.gpr sb = B := by rw [g₆ _ (by decide) (by decide), g₂, b₁']
  have hH : c.hiSlot < c.total := by simp only [Core.hiSlot]; omega
  have hLo : c.loSlot < c.total := by simp only [Core.loSlot]; omega
  obtain ⟨s₇, e₇, m₇, g₇, rd₇, wr₇⟩ := stS_ok (s := s₆) (b := B) (k := c.hiSlot) .x6 b₆ (by omega)
    (by rw [wr₆']; exact sl _ (by simp only [Core.hiSlot]; omega) hH)
  obtain ⟨s₈, e₈, m₈, g₈, rd₈, wr₈⟩ := stS_ok (s := s₇) (b := B) (k := c.loSlot) .x7 (by rw [g₇, b₆]) (by omega)
    (by rw [wr₇, wr₆']; exact sl _ (by simp only [Core.loSlot]; omega) hLo)
  obtain ⟨s₉, e₉, r₉, o₉, m₉, rd₉, wr₉⟩ := movz_ok s₈ .x10 (v := 0) (by decide)
  let N := (s.gpr r.n).toNat
  have n₉ : s₉.gpr r.n = BitVec.ofNat 64 N := by
    rw [o₉ _ n10, g₈, g₇, g₆ _ n6 n7, keep₂ _ ns]; simp [N]
  obtain ⟨s₁₀, e₁₀, h₁₀, l₁₀, o₁₀, m₁₀, rd₁₀, wr₁₀⟩ := addc_ok s₉ r.n (V := V) (N := N) (s.gpr r.n).isLt
    (by rw [o₉ _ (by decide), g₈, g₇, x6₆]) (by rw [o₉ _ (by decide), g₈, g₇, x7₆]) n₉ (by rw [r₉]; rfl)
  obtain ⟨s₁₁, e₁₁, r₁₁, o₁₁, m₁₁, rd₁₁, wr₁₁⟩ := rev_ok s₁₀ .x6 .x6
  obtain ⟨s₁₂, e₁₂, r₁₂, o₁₂, m₁₂, rd₁₂, wr₁₂⟩ := rev_ok s₁₁ .x7 .x7
  have keep₁₂ : ∀ x, x ≠ .x6 → x ≠ .x7 → x ≠ .x10 → s₁₂.gpr x = s₆.gpr x := fun x h1 h2 h3 => by
    rw [o₁₂ x h2, o₁₁ x h1, o₁₀ x h1 h2, o₉ x h3, g₈, g₇]
  have P₁₂ : s₁₂.gpr r.ctr = P := by rw [keep₁₂ _ c6 c7 c10, g₆ _ c6 c7, P₂]
  have wr₁₂' : s₁₂.wr = s.wr := by rw [wr₁₂, wr₁₁, wr₁₀, wr₉, wr₈, wr₇, wr₆']
  obtain ⟨s₁₃, e₁₃, m₁₃, g₁₃, rd₁₃, wr₁₃⟩ := str_ok s₁₂ .x7 r.ctr (off := 8) (by decide)
    (by rw [P₁₂, wr₁₂']; exact inP 8 (by decide))
  obtain ⟨s₁₄, e₁₄, m₁₄, g₁₄, rd₁₄, wr₁₄⟩ := str_ok s₁₃ .x6 r.ctr (off := 0) (by decide)
    (by rw [g₁₃, P₁₂, wr₁₃, wr₁₂']; exact inP 0 (by decide))
  have mem₈ : s₈.mem = (s₂.mem.writeW (wordAddr B c.hiSlot) (hiOf V)).writeW (wordAddr B c.loSlot) (loOf V) := by
    rw [m₈, m₇, g₇, x6₆, x7₆, m₆, m₅, m₄, m₃]
  have mem₁₄ : s₁₄.mem = (s₈.mem.writeW (P + BitVec.ofNat 64 8) (rev64 (loOf (V + N)))).writeW P
      (rev64 (hiOf (V + N))) := by
    rw [m₁₄, g₁₃, P₁₂, p0, m₁₃, P₁₂, m₁₂, m₁₁, m₁₀, m₉, o₁₂ .x6 (by decide), r₁₁, h₁₀, r₁₂, o₁₁ .x7 (by decide),
      l₁₀]
  -- The frames.
  have fS : Frame [modeRegion c B] s₂.mem s₈.mem := by
    rw [mem₈]
    have hm : modeRegion c B ∈ [modeRegion c B] := List.mem_singleton_self _
    exact ((Frame.refl _ _).writeW hm _ (VG.Offset.contains B (by simp only [Core.hiSlot]; omega)
      (by simp only [Core.hiSlot]; omega) (by omega))).writeW hm _
      (VG.Offset.contains B (by simp only [Core.loSlot]; omega) (by simp only [Core.loSlot]; omega) (by omega))
  have fP : Frame [⟨P, 16⟩] s₈.mem s₁₄.mem := by
    rw [mem₁₄]
    have hm : (⟨P, 16⟩ : Region) ∈ [(⟨P, 16⟩ : Region)] := List.mem_singleton_self _
    exact ((Frame.refl _ _).writeW hm _ (VG.Offset.contains_base P (by decide) (by decide))).writeW hm _
      (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide)
  have thruP : ∀ k, c.slots ≤ k → k < c.total →
      s₁₄.mem.readW (wordAddr B k) 64 = s₈.mem.readW (wordAddr B k) 64 := fun k h1 h2 =>
    fP.readW (Region.contains_self _ _) (dP k h1 h2) (by decide)
  have b8 : ∀ k, k < c.total → 8 * k < 2 ^ 64 := fun k hk => by omega
  have mem8 : ∀ k, c.slots ≤ k → k < c.total → k ≠ c.hiSlot → k ≠ c.loSlot →
      s₈.mem.readW (wordAddr B k) 64 = s₂.mem.readW (wordAddr B k) 64 := fun k h1 h2 hh hl => by
    rw [mem₈, readW_slot_write _ (b8 k h2) (b8 _ hLo), ite_eq_right hl, readW_slot_write _ (b8 k h2) (b8 _ hH),
      ite_eq_right hh]
  have hsv : ∀ i < 10, Core.savedRegs.getD i .x19 ≠ sb := by decide
  refine ⟨s₁₄, ?_, ?_, fun i hi => ?_, ?_, ?_, ?_, ?_, fun x hx => ?_,
    by rw [rd₁₄, rd₁₃, rd₁₂, rd₁₁, rd₁₀, rd₉, rd₈, rd₇, rd₆'], by rw [wr₁₄, wr₁₃, wr₁₂']⟩
  · rw [runBlock_app, ctrEntry_eq, runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some, ctrSetup_eq,
      runBlock_app, e₃, Option.bind_some, runBlock_app, e₄, Option.bind_some, runBlock_app, e₅, Option.bind_some,
      runBlock_app, e₆, Option.bind_some, runBlock_app, e₇, Option.bind_some, runBlock_app, e₈, Option.bind_some,
      runBlock_app, e₉, Option.bind_some, runBlock_app, e₁₀, Option.bind_some, runBlock_app, e₁₁,
      Option.bind_some, runBlock_app, e₁₂, Option.bind_some, runBlock_app, e₁₃, Option.bind_some, e₁₄]
  · rw [g₁₄, g₁₃, keep₁₂ _ (by decide) (by decide) (by decide), b₆]
  · have k1 : c.slots ≤ c.slots + i := by omega
    have k2 : c.slots + i < c.total := by omega
    rw [thruP _ k1 k2, mem8 _ k1 k2 (by simp only [Core.hiSlot]; omega) (by simp only [Core.loSlot]; omega),
      v₂ i hi, o₁ _ (hsv i hi)]
  · rw [thruP _ (by simp only [Core.hiSlot]; omega) hH, mem₈,
      readW_slot_write _ (b8 _ hH) (b8 _ hLo), ite_eq_right (by simp only [Core.hiSlot, Core.loSlot]; omega),
      Mem.readW_writeW_self64]
  · rw [thruP _ (by simp only [Core.loSlot]; omega) hLo, mem₈, Mem.readW_writeW_self64]
  · rw [mem₁₄]; exact bytes_pair2 _ _ _
  · exact (fe.trans (fS.sub fun x hx => ⟨x, hx, fun _ h => h⟩) |>.sub fun x hx => ⟨x, by
      simp only [List.mem_singleton] at hx; rw [hx]; exact List.mem_cons_self, fun _ h => h⟩).trans
      (fP.sub fun x hx => ⟨x, by
        simp only [List.mem_singleton] at hx; rw [hx]; exact List.mem_cons_of_mem _ List.mem_cons_self,
        fun _ h => h⟩)
  · obtain ⟨h1, h2, h3, h4⟩ := not_setupRegs hx
    rw [g₁₄, g₁₃, keep₁₂ x h2 h3 h4, g₆ x h2 h3, keep₂ x h1]

/-- The data's address and `n` to `dataReg` and `leftReg`. -/
theorem ctrArgs_ok (s : State) (r : CtrRegs) (hd : c.dataReg ≠ r.n) (hdl : c.dataReg ≠ c.leftReg) :
    ∃ s', runBlock isa (c.ctrArgs r) s = some s' ∧ s'.gpr c.dataReg = s.gpr r.data ∧
      s'.gpr c.leftReg = s.gpr r.n ∧ (∀ x, x ≠ c.dataReg → x ≠ c.leftReg → s'.gpr x = s.gpr x) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s c.dataReg r.data
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := movR_ok s₁ c.leftReg r.n
  refine ⟨s₂, ?_, ?_, by rw [r₂, o₁ _ (Ne.symm hd)], fun x h1 h2 => by rw [o₂ x h2, o₁ x h1], by rw [m₂, m₁],
    by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
  · rw [Core.ctrArgs, show ([movR c.dataReg r.data, movR c.leftReg r.n] : List Instr) =
      [movR c.dataReg r.data] ++ [movR c.leftReg r.n] from rfl, runBlock_app, e₁, Option.bind_some, e₂]
  · rw [o₂ _ hdl, r₁]

end VG.Proof.Modes.AArch64

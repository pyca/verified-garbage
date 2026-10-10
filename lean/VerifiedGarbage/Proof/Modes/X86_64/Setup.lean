import VerifiedGarbage.Proof.Modes.X86_64.Counter

/-!
# CTR on x86-64: entry and exit

`setup_ok`: the entry block of `ctr` moves the scratch buffer to `sb`,
stores the callee-saved registers, the data's address and `n` in the
mode's slots, reads the counter block `T₁` at `r.ctr` (a number `V`,
big-endian) into the running counter's slots, as `hiOf V` and `loOf V`, and
writes `T₁ + n` back. `restore_ok`: the exit block loads the callee-saved
registers back.
-/

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64
open VG.Impl.Aes.X86_64 (sb movR movS st)
open VG.Spec.Aes (bytesAt)

/-- `mov d, [r + off]`. -/
theorem ld_ok (s : State) (d r : Reg) (off : Nat) (hr : InRegions (s.rd ++ s.wr) (s.gpr r + BitVec.ofNat 64 off) 8) :
    ∃ s', runBlock isa [.mov d (.mem (at_ r off))] s = some s' ∧
      s'.gpr d = s.mem.readW (s.gpr r + BitVec.ofNat 64 off) 64 ∧
      (∀ x, x ≠ d → s'.gpr x = s.gpr x) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.setReg d (s.mem.readW (s.gpr r + BitVec.ofNat 64 off) 64), by
    simp only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, State.ea, ofInt_nat, hr,
      ite_true, Option.map_some],
    RegUpd.gpr_setReg_self _ _ _, fun _ hx => RegUpd.gpr_setReg_of_ne _ _ hx, rfl, rfl, rfl⟩

/-- `mov [r + off], v`. -/
theorem stM_ok (s : State) (r v : Reg) (off : Nat) (hw : InRegions s.wr (s.gpr r + BitVec.ofNat 64 off) 8) :
    ∃ s', runBlock isa [.store (at_ r off) v] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr r + BitVec.ofNat 64 off) (s.gpr v) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨{ s with mem := s.mem.writeW (s.gpr r + BitVec.ofNat 64 off) (s.gpr v) }, by
    simp only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, State.ea, ofInt_nat, hw,
      ite_true], rfl, rfl, rfl, rfl⟩

theorem addN_vals (V N : Nat) (hN : N < 2 ^ 64) :
    loOf V + BitVec.ofNat 64 N = loOf (V + N) ∧
    hiOf V + (0 : BitVec 32).signExtend 64 +
        (BitVec.ofBool (decide (2 ^ 64 ≤ (loOf V).toNat + (BitVec.ofNat 64 N).toNat))).setWidth 64 =
      hiOf (V + N) := by
  have e0 : ((0 : BitVec 32).signExtend 64) = BitVec.ofNat 64 0 := rfl
  obtain ⟨h1, h2⟩ := carry_vals V N hN
  refine ⟨h1, ?_⟩
  rw [e0, BitVec.add_zero, ← h2]
  congr 1
  apply BitVec.eq_of_toNat_eq
  cases decide (2 ^ 64 ≤ (loOf V).toNat + (BitVec.ofNat 64 N).toNat) <;> rfl

/-- `add rbx, nr; adc rax, 0`: the running counter stepped by `nr`. -/
theorem addN_ok (s : State) (nr : Reg) {V N : Nat} (hN : N < 2 ^ 64) (hh : s.gpr .rax = hiOf V)
    (hl : s.gpr .rbx = loOf V) (hn : s.gpr nr = BitVec.ofNat 64 N) :
    ∃ s', runBlock isa [.alu .add .rbx (.reg nr), .alu .adc .rax (.imm 0)] s = some s' ∧
      s'.gpr .rax = hiOf (V + N) ∧ s'.gpr .rbx = loOf (V + N) ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨i1, i2⟩ := addN_vals V N hN
  let e1 := s.gpr nr
  let e0 := (0 : BitVec 32).signExtend 64
  let c := decide (2 ^ 64 ≤ (s.gpr .rbx).toNat + e1.toNat)
  let s₁ := (arithFlags s (s.gpr .rbx + e1) c (addOverflow (s.gpr .rbx) e1 (s.gpr .rbx + e1))).setReg .rbx
    (s.gpr .rbx + e1)
  let r := s₁.gpr .rax + e0 + (BitVec.ofBool c).setWidth 64
  let s₂ := (arithFlags s₁ r (decide (2 ^ 64 ≤ (s₁.gpr .rax).toNat + e0.toNat + c.toNat))
    (addOverflow (s₁.gpr .rax) e0 r)).setReg .rax r
  have g₁ : ∀ x, x ≠ .rbx → s₁.gpr x = s.gpr x := fun x hx => by
    simp only [s₁, RegUpd.gpr_setReg_of_ne _ _ hx, RegUpd.gpr_arithFlags]
  refine ⟨s₂, ?_, ?_, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl⟩
  · simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
      RegUpd.cf_setReg, RegUpd.cf_arithFlags, Option.map_some]
    rfl
  · show s₁.gpr .rax + e0 + (BitVec.ofBool c).setWidth 64 = _
    rw [g₁ .rax (by decide), hh]
    simp only [c, e1, hl, hn]
    exact i2
  · show (s₂.gpr .rbx) = _
    simp only [s₂, RegUpd.gpr_setReg_of_ne _ _ (show Reg.rbx ≠ Reg.rax by decide), RegUpd.gpr_arithFlags, s₁,
      RegUpd.gpr_setReg_self, hl, e1, hn]
    exact i1
  · simp only [s₂, RegUpd.gpr_setReg_of_ne _ _ h1, RegUpd.gpr_arithFlags, g₁ _ h2]

/-! ## Words to and from consecutive slots -/

/-- `k` stores of registers to consecutive slots from `base`. -/
theorem stores_ok {B : Addr} (base : Nat) (g : Nat → Reg) : ∀ (k : Nat) (s : State), s.gpr sb = B →
    (∀ i < k, InRegions s.wr (wordAddr B (base + i)) 8) → 8 * (base + k) < 2 ^ 64 →
    ∃ s', runBlock isa ((List.range k).map fun i => st (base + i) (g i)) s = some s' ∧
      (∀ i < k, s'.mem.readW (wordAddr B (base + i)) 64 = s.gpr (g i)) ∧
      Frame [⟨wordAddr B base, 8 * k⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | 0, s, _, _, _ => ⟨s, rfl, fun i hi => by omega, Frame.refl _ _, rfl, rfl, rfl⟩
  | k + 1, s, hB, hw, hk => by
    obtain ⟨s₁, e₁, v₁, f₁, g₁, rd₁, wr₁⟩ := stores_ok base g k s hB (fun i hi => hw i (by omega)) (by omega)
    obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := stReg_ok (s := s₁) (b := B) (k := base + k) (g k) (by rw [g₁, hB])
      (by rw [wr₁]; exact hw k (by omega))
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
    (∀ i < k, g i ≠ sb) → (∀ i < k, ∀ j < k, g i = g j → i = j) →
    (∀ i < k, InRegions (s.rd ++ s.wr) (wordAddr B (base + i)) 8) →
    ∃ s', runBlock isa ((List.range k).map fun i => movS (g i) (base + i)) s = some s' ∧
      (∀ i < k, s'.gpr (g i) = s.mem.readW (wordAddr B (base + i)) 64) ∧
      (∀ r, (∀ i < k, r ≠ g i) → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | 0, s, _, _, _, _ => ⟨s, rfl, fun i hi => by omega, fun _ _ => rfl, rfl, rfl, rfl⟩
  | k + 1, s, hB, hsb, hinj, hr => by
    obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := loads_ok base g k s hB (fun i hi => hsb i (by omega))
      (fun i hi j hj => hinj i (by omega) j (by omega)) (fun i hi => hr i (by omega))
    have hB₁ : s₁.gpr sb = B := by
      rw [o₁ _ (fun i hi h => hsb i (by omega) h.symm), hB]
    obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂⟩ := movS_ok (s := s₁) (b := B) (k := base + k) (g k) hB₁
      (by rw [rd₁, wr₁]; exact hr k (by omega))
    refine ⟨s₂, ?_, fun i hi => ?_, fun r hr' => ?_, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
    · rw [List.range_succ, List.map_append, runBlock_app, e₁, Option.bind_some, List.map_singleton, e₂]
    · by_cases h : i = k
      · subst h; rw [v₂, m₁]
      · rw [o₂ _ (fun he => h (hinj i hi k (by omega) he)), v₁ i (by omega)]
    · rw [o₂ r (hr' k (by omega)), o₁ r (fun i hi => hr' i (by omega))]

/-! ## Entry -/

/-- The mode's slots. -/
abbrev modeRegion (c : Core) (B : Addr) : Region := ⟨B + BitVec.ofNat 64 (8 * c.slots), 64⟩

theorem ctrSetup_eq (c : Core) (r : CtrRegs) : c.ctrSetup r =
    ([.mov .rax (.mem (at_ r.ctr 0))] : List Instr) ++ (([.bswap .rax] : List Instr) ++
      (([.mov .rbx (.mem (at_ r.ctr 8))] : List Instr) ++ (([.bswap .rbx] : List Instr) ++
      (([st c.hiSlot .rax] : List Instr) ++ (([st c.loSlot .rbx] : List Instr) ++
      (([.alu .add .rbx (.reg r.n), .alu .adc .rax (.imm 0)] : List Instr) ++
      (([.bswap .rax] : List Instr) ++ (([.bswap .rbx] : List Instr) ++
      (([.store (at_ r.ctr 8) .rbx] : List Instr) ++ ([.store (at_ r.ctr 0) .rax] : List Instr)))))))))) := rfl

theorem ctrEntry_eq (c : Core) (r : CtrRegs) : c.ctrEntry r =
    ([movR sb r.scr] : List Instr) ++ ((List.range 6).map fun i => st (c.slots + i) (Core.savedRegs.getD i .rbx)) :=
  rfl

/-- The registers of a mode's arguments: none of them `sb`, `rax` or `rbx`. -/
structure RegsOk (r : CtrRegs) : Prop where
  ctr : r.ctr ≠ sb ∧ r.ctr ≠ .rax ∧ r.ctr ≠ .rbx
  data : r.data ≠ sb ∧ r.data ≠ .rax ∧ r.data ≠ .rbx
  n : r.n ≠ sb ∧ r.n ≠ .rax ∧ r.n ≠ .rbx

variable {c : Core}

/-- The entry block. -/
theorem setup_ok (hL : Layout c) {r : CtrRegs} (hr : RegsOk r) (s : State) {B P : Addr}
    (hB : s.gpr r.scr = B) (hs : ScrIn s B c.ctrSlots) (hP : s.gpr r.ctr = P) (hwP : (⟨P, 16⟩ : Region) ∈ s.wr)
    (hsep : Region.Disjoint ⟨P, 16⟩ ⟨B, 8 * c.ctrSlots⟩) :
    ∃ s', runBlock isa (c.ctrEntry r ++ c.ctrSetup r) s = some s' ∧ s'.gpr sb = B ∧
      (∀ i < 6, s'.mem.readW (wordAddr B (c.slots + i)) 64 = s.gpr (Core.savedRegs.getD i .rbx)) ∧
      s'.mem.readW (wordAddr B c.hiSlot) 64 = hiOf (ctrVal s.mem P) ∧
      s'.mem.readW (wordAddr B c.loSlot) 64 = loOf (ctrVal s.mem P) ∧
      bytesAt s'.mem P 16 = Spec.Ctr.ofNat (ctrVal s.mem P + (s.gpr r.n).toNat) 16 ∧
      Frame [modeRegion c B, ⟨P, 16⟩] s.mem s'.mem ∧
      (∀ x, x ≠ sb → x ≠ .rax → x ≠ .rbx → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hsm := hL.small
  have hroom := hL.room
  have hN : 8 * c.ctrSlots < 2 ^ 64 := by simp only [Core.ctrSlots]; omega
  have sl : ∀ k, c.slots ≤ k → k < c.ctrSlots → InRegions s.wr (wordAddr B k) 8 := fun k _ hk =>
    slot_wr hs.wr hN hk
  have p0 : P + BitVec.ofNat 64 0 = P := by simp
  -- The scratch buffer to `sb`.
  obtain ⟨s₁, e₁, b₁, o₁, m₁, rd₁, wr₁⟩ := movR_ok s sb r.scr
  have b₁' : s₁.gpr sb = B := by rw [b₁, hB]
  have keep₁ : ∀ x, x ≠ sb → s₁.gpr x = s.gpr x := o₁
  -- The callee-saved registers.
  obtain ⟨s₂, e₂, v₂, f₂, g₂, rd₂, wr₂⟩ := stores_ok (B := B) c.slots (fun i => Core.savedRegs.getD i .rbx) 6 s₁ b₁'
    (fun i hi => by rw [wr₁]; exact sl _ (by omega) (by simp only [Core.ctrSlots]; omega))
    (by omega)
  let s₄ := s₂
  have m₄e : s₄.mem = s₂.mem := rfl
  have g₄' : s₄.gpr = s₁.gpr := g₂
  have wr₄' : s₄.wr = s.wr := by rw [show s₄.wr = s₂.wr from rfl, wr₂, wr₁]
  have rd₄' : s₄.rd = s.rd := by rw [show s₄.rd = s₂.rd from rfl, rd₂, rd₁]
  have keep₄ : ∀ x, x ≠ sb → s₄.gpr x = s.gpr x := fun x hx => by rw [g₄', keep₁ x hx]
  have P₄ : s₄.gpr r.ctr = P := by rw [keep₄ _ hr.ctr.1, hP]
  have fe : Frame [modeRegion c B] s.mem s₄.mem := by
    rw [← m₁]
    exact f₂.sub fun x hx => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hx; subst hx
      exact VG.Offset.sub B (by omega) (by omega)⟩
  have dP : ∀ k, c.slots ≤ k → k < c.ctrSlots → ∀ x ∈ [(⟨P, 16⟩ : Region)],
      Region.Disjoint ⟨wordAddr B k, 8⟩ x := fun k h1 h2 x hx => by
    simp only [List.mem_singleton] at hx; subst hx
    exact (hsep.sub_right (VG.Offset.sub_base B (by omega))).symm
  have memP : bytesAt s₄.mem P 16 = bytesAt s.mem P 16 :=
    bytesAt_frame fe (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      exact hsep.sub_right (VG.Offset.sub_base B (by simp only [Core.ctrSlots]; omega))) (by decide)
  -- The counter.
  have inP : ∀ d, d + 8 ≤ 16 → InRegions s.wr (P + BitVec.ofNat 64 d) 8 := fun d hd =>
    ⟨_, hwP, VG.Offset.contains_base P hd (by omega)⟩
  obtain ⟨hv, lv⟩ := halves s.mem P
  let V := ctrVal s.mem P
  have mP : ∀ d, d + 8 ≤ 16 →
      s₄.mem.readW (P + BitVec.ofNat 64 d) 64 = s.mem.readW (P + BitVec.ofNat 64 d) 64 := fun d hd =>
    fe.readW (r := ⟨P, 16⟩) (VG.Offset.contains_base P (by omega) (by omega)) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      exact hsep.sub_right (VG.Offset.sub_base B (by simp only [Core.ctrSlots]; omega))) (by decide)
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := ld_ok s₄ .rax r.ctr 0
    (by rw [rd₄', wr₄', P₄]; exact inRd (inP 0 (by decide)))
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆⟩ := bswap_ok s₅ .rax
  obtain ⟨s₇, e₇, r₇, o₇, m₇, rd₇, wr₇⟩ := ld_ok s₆ .rbx r.ctr 8
    (by rw [rd₆, wr₆, rd₅, wr₅, rd₄', wr₄', o₆ _ hr.ctr.2.1, o₅ _ hr.ctr.2.1, P₄]; exact inRd (inP 8 (by decide)))
  obtain ⟨s₈, e₈, r₈, o₈, m₈, rd₈, wr₈⟩ := bswap_ok s₇ .rbx
  have g₈ : ∀ x, x ≠ .rax → x ≠ .rbx → s₈.gpr x = s₄.gpr x := fun x h1 h2 => by
    rw [o₈ x h2, o₇ x h2, o₆ x h1, o₅ x h1]
  have mP0 := mP 0 (by decide)
  rw [p0] at mP0
  have rax₈ : s₈.gpr .rax = hiOf V := by
    rw [o₈ _ (by decide), o₇ _ (by decide), r₆, r₅, P₄, p0, mP0, hv]; rfl
  have rbx₈ : s₈.gpr .rbx = loOf V := by
    rw [r₈, r₇, m₆, m₅, o₆ _ hr.ctr.2.1, o₅ _ hr.ctr.2.1, P₄, mP 8 (by decide), lv]; rfl
  have wr₈' : s₈.wr = s.wr := by rw [wr₈, wr₇, wr₆, wr₅, wr₄']
  have rd₈' : s₈.rd = s.rd := by rw [rd₈, rd₇, rd₆, rd₅, rd₄']
  have b₈ : s₈.gpr sb = B := by rw [g₈ _ (by decide) (by decide), g₄', b₁']
  have hH : c.hiSlot < c.ctrSlots := by simp only [Core.hiSlot, Core.ctrSlots]; omega
  have hLo : c.loSlot < c.ctrSlots := by simp only [Core.loSlot, Core.ctrSlots]; omega
  obtain ⟨s₉, e₉, m₉, g₉, rd₉, wr₉⟩ := stReg_ok (s := s₈) (b := B) (k := c.hiSlot) .rax b₈
    (by rw [wr₈']; exact sl _ (by simp only [Core.hiSlot]; omega) hH)
  obtain ⟨s₁₀, e₁₀, m₁₀, g₁₀, rd₁₀, wr₁₀⟩ := stReg_ok (s := s₉) (b := B) (k := c.loSlot) .rbx (by rw [g₉, b₈])
    (by rw [wr₉, wr₈']; exact sl _ (by simp only [Core.loSlot]; omega) hLo)
  let N := (s.gpr r.n).toNat
  have n₁₀ : s₁₀.gpr r.n = BitVec.ofNat 64 N := by
    rw [g₁₀, g₉, g₈ _ hr.n.2.1 hr.n.2.2, keep₄ _ hr.n.1]; simp [N]
  obtain ⟨s₁₁, e₁₁, h₁₁, l₁₁, o₁₁, m₁₁, rd₁₁, wr₁₁⟩ := addN_ok s₁₀ r.n (V := V) (N := N) (s.gpr r.n).isLt
    (by rw [g₁₀, g₉, rax₈]) (by rw [g₁₀, g₉, rbx₈]) n₁₀
  obtain ⟨s₁₂, e₁₂, r₁₂, o₁₂, m₁₂, rd₁₂, wr₁₂⟩ := bswap_ok s₁₁ .rax
  obtain ⟨s₁₃, e₁₃, r₁₃, o₁₃, m₁₃, rd₁₃, wr₁₃⟩ := bswap_ok s₁₂ .rbx
  have keep₁₃ : ∀ x, x ≠ .rax → x ≠ .rbx → s₁₃.gpr x = s₈.gpr x := fun x h1 h2 => by
    rw [o₁₃ x h2, o₁₂ x h1, o₁₁ x h1 h2, g₁₀, g₉]
  have P₁₃ : s₁₃.gpr r.ctr = P := by rw [keep₁₃ _ hr.ctr.2.1 hr.ctr.2.2, g₈ _ hr.ctr.2.1 hr.ctr.2.2, P₄]
  have wr₁₃' : s₁₃.wr = s.wr := by rw [wr₁₃, wr₁₂, wr₁₁, wr₁₀, wr₉, wr₈']
  obtain ⟨s₁₄, e₁₄, m₁₄, g₁₄, rd₁₄, wr₁₄⟩ := stM_ok s₁₃ r.ctr .rbx 8 (by rw [P₁₃, wr₁₃']; exact inP 8 (by decide))
  obtain ⟨s₁₅, e₁₅, m₁₅, g₁₅, rd₁₅, wr₁₅⟩ := stM_ok s₁₄ r.ctr .rax 0
    (by rw [g₁₄, P₁₃, wr₁₄, wr₁₃']; exact inP 0 (by decide))
  have mem₁₀ : s₁₀.mem = (s₄.mem.writeW (wordAddr B c.hiSlot) (hiOf V)).writeW (wordAddr B c.loSlot) (loOf V) := by
    rw [m₁₀, m₉, g₉, rax₈, rbx₈, m₈, m₇, m₆, m₅]
  have mem₁₅ : s₁₅.mem = (s₁₀.mem.writeW (P + BitVec.ofNat 64 8) (bswap64 (loOf (V + N)))).writeW P
      (bswap64 (hiOf (V + N))) := by
    rw [m₁₅, g₁₄, P₁₃, p0, m₁₄, P₁₃, m₁₃, m₁₂, m₁₁, o₁₃ .rax (by decide), r₁₂, h₁₁, r₁₃, o₁₂ .rbx (by decide), l₁₁]
  -- The frames.
  have fS : Frame [modeRegion c B] s₄.mem s₁₀.mem := by
    rw [mem₁₀]
    have hm : modeRegion c B ∈ [modeRegion c B] := List.mem_singleton_self _
    exact ((Frame.refl _ _).writeW hm _ (VG.Offset.contains B (by simp only [Core.hiSlot]; omega)
      (by simp only [Core.hiSlot]; omega) (by omega))).writeW hm _
      (VG.Offset.contains B (by simp only [Core.loSlot]; omega) (by simp only [Core.loSlot]; omega) (by omega))
  have fP : Frame [⟨P, 16⟩] s₁₀.mem s₁₅.mem := by
    rw [mem₁₅]
    have hm : (⟨P, 16⟩ : Region) ∈ [(⟨P, 16⟩ : Region)] := List.mem_singleton_self _
    exact ((Frame.refl _ _).writeW hm _ (VG.Offset.contains_base P (by decide) (by decide))).writeW hm _
      (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide)
  have thruP : ∀ k, c.slots ≤ k → k < c.ctrSlots →
      s₁₅.mem.readW (wordAddr B k) 64 = s₁₀.mem.readW (wordAddr B k) 64 := fun k h1 h2 =>
    fP.readW (Region.contains_self _ _) (dP k h1 h2) (by decide)
  have b8 : ∀ k, k < c.ctrSlots → 8 * k < 2 ^ 64 := fun k hk => by omega
  have mem10 : ∀ k, c.slots ≤ k → k < c.ctrSlots → k ≠ c.hiSlot → k ≠ c.loSlot →
      s₁₀.mem.readW (wordAddr B k) 64 = s₄.mem.readW (wordAddr B k) 64 := fun k h1 h2 hh hl => by
    rw [mem₁₀, readW_slot_write _ (b8 k h2) (b8 _ hLo), ite_eq_right hl, readW_slot_write _ (b8 k h2) (b8 _ hH), ite_eq_right hh]
  have hsv : ∀ i < 6, Core.savedRegs.getD i .rbx ≠ sb := by decide
  refine ⟨s₁₅, ?_, ?_, fun i hi => ?_, ?_, ?_, ?_, ?_, fun x h1 h2 h3 => ?_,
    by rw [rd₁₅, rd₁₄, rd₁₃, rd₁₂, rd₁₁, rd₁₀, rd₉, rd₈'], by rw [wr₁₅, wr₁₄, wr₁₃']⟩
  · rw [runBlock_app, ctrEntry_eq, runBlock_app, e₁, Option.bind_some, e₂, Option.bind_some, ctrSetup_eq,
      runBlock_app, e₅, Option.bind_some, runBlock_app, e₆, Option.bind_some, runBlock_app, e₇, Option.bind_some,
      runBlock_app, e₈, Option.bind_some, runBlock_app, e₉, Option.bind_some, runBlock_app, e₁₀, Option.bind_some,
      runBlock_app, e₁₁, Option.bind_some, runBlock_app, e₁₂, Option.bind_some, runBlock_app, e₁₃,
      Option.bind_some, runBlock_app, e₁₄, Option.bind_some, e₁₅]
  · rw [g₁₅, g₁₄, keep₁₃ _ (by decide) (by decide), b₈]
  · have k1 : c.slots ≤ c.slots + i := by omega
    have k2 : c.slots + i < c.ctrSlots := by simp only [Core.ctrSlots]; omega
    rw [thruP _ k1 k2, mem10 _ k1 k2 (by simp only [Core.hiSlot]; omega) (by simp only [Core.loSlot]; omega),
      m₄e, v₂ i hi, keep₁ _ (hsv i hi)]
  · rw [thruP _ (by simp only [Core.hiSlot]; omega) hH, mem₁₀,
      readW_slot_write _ (b8 _ hH) (b8 _ hLo), ite_eq_right (by simp only [Core.hiSlot, Core.loSlot]; omega),
      Mem.readW_writeW_self64]
  · rw [thruP _ (by simp only [Core.loSlot]; omega) hLo, mem₁₀, Mem.readW_writeW_self64]
  · rw [mem₁₅]; exact bytes_pair2 _ _ _
  · exact (fe.trans (fS.sub fun x hx => ⟨x, hx, fun _ h => h⟩) |>.sub fun x hx => ⟨x, by
      simp only [List.mem_singleton] at hx; rw [hx]; exact List.mem_cons_self, fun _ h => h⟩).trans
      (fP.sub fun x hx => ⟨x, by
        simp only [List.mem_singleton] at hx; rw [hx]; exact List.mem_cons_of_mem _ List.mem_cons_self,
        fun _ h => h⟩)
  · rw [g₁₅, g₁₄, keep₁₃ x h2 h3, g₈ x h2 h3, keep₄ x h1]

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

end VG.Proof.Modes.X86_64

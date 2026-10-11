import VerifiedGarbage.Proof.Seed.Arm.Crypt8

/-!
# Slots, copies of blocks, and saving registers, on ARMv7

As for SM4 on ARMv7 (`Proof/Sm4/Arm/Copy.lean`, `Prologue.lean`): loads and
stores of the scratch buffer's slots through a base register (`ldW_ok`,
`stW_ok`, and lists of them); `copyBlocks_wp`, the loop copying `c ≥ 1`
blocks of 16 bytes from `r0` to `r12`; the prologue and epilogue's saving
and restoring of the callee-saved registers (`save_ok`, `restore_ok`) in
the slots from `savedSlot`; and the data loop's invariant (`DInv`).
-/

namespace VG.Proof.Seed.Arm

open VG VG.Arm VG.Arm.Straight VG.Impl.Seed.Arm
open VG.Impl.Aes.Arm (sb t0 t1 kp)

theorem savedSlot_eq : savedSlot = 176 := rfl
theorem ptrSlot_eq : ptrSlot = 185 := rfl
theorem cntSlot_eq : cntSlot = 186 := rfl
theorem tableSlot_eq : tableSlot = 144 := rfl
theorem tableEnd_eq : tableEnd = 176 := rfl
theorem tailSlot_eq : tailSlot = 112 := rfl

/-! ## Addresses and memory -/

theorem off_sub_toNat (B : Addr) {t e : Nat} (h : e ≤ t) (ht : t < 2 ^ 64) :
    (B + BitVec.ofNat 64 t - (B + BitVec.ofNat 64 e)).toNat = t - e := by
  rw [Offset.add_sub_add _ h, BitVec.toNat_ofNat]; omega

theorem off_sub_not (B : Addr) {t e n : Nat} (h : t < e ∨ e + n ≤ t) (ht : t < 2 ^ 64) (hn : 0 < n)
    (he : e + n ≤ 2 ^ 64) : ¬ (B + BitVec.ofNat 64 t - (B + BitVec.ofNat 64 e)).toNat < n := by
  rw [Offset.add_sub_add_left]; exact Offset.not_lt_sub_ofNat h ht hn he

theorem not_contains_off (b : Addr) {t e n : Nat} (h : t < e ∨ e + n ≤ t) (ht : t < 2 ^ 64) (hn : 0 < n)
    (he : e + n ≤ 2 ^ 64) : ¬ (⟨b + BitVec.ofNat 64 e, n⟩ : Region).Contains (b + BitVec.ofNat 64 t) 1 := by
  simp only [Region.Contains]; intro hc; exact off_sub_not b h ht hn he (by omega)

/-- A byte of a little-endian 32-bit word stored from a load. -/
theorem writeW_readW32_apply (m m' : Mem) (a c x : Addr) :
    m.writeW a (m'.readW c 32) x =
      if (x - a).toNat < 4 then m' (c + BitVec.ofNat 64 (x - a).toNat) else m x := by
  simp only [Mem.writeW, Mem.write, Mem.readW, BitVec.setWidth_eq]
  split
  · rename_i h
    exact Mem.extractLsb'_read m' c (n := 4) h
  · rfl

/-- Slot `k` is in the scratch buffer. -/
theorem slot_inR {rs : List Region} {b : BitVec 32} {n k : Nat} (hr : (⟨State.addr b, 4 * n⟩ : Region) ∈ rs)
    (hfit : b.toNat + 4 * n ≤ 2 ^ 32) (hk : k < n) : InRegions rs (wordAddr b k) 4 :=
  ⟨_, hr, by
    rw [slot_addr (by omega)]
    have := toNat_addr b
    exact Offset.contains_base _ (by omega) (by omega)⟩

/-- `subs d, n, #1`. -/
theorem subs1_ok (s : State) (d : Reg) :
    ∃ s', runBlock isa [.subs d d (.imm 1)] s = some s' ∧ s'.gpr d = s.gpr d - 1 ∧ s'.z = (s.gpr d - 1 == 0) ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨(subFlags s (s.gpr d) 1).setReg d (s.gpr d - 1), ?_, RegUpd.gpr_setReg_self _ _ _, by rw [RegUpd.z_setReg]; rfl,
    fun r hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr]; rfl, rfl, rfl, rfl, rfl⟩
  rw [runBlock_cons, show exec (.subs d d (.imm 1)) s = some ((subFlags s (s.gpr d) 1).setReg d (s.gpr d - 1)) by
    simp [exec, Op2.eval]; decide, runStep_some, runBlock_nil]

theorem ofNat32_beq_zero {x : Nat} (hx : x < 2 ^ 32) : (BitVec.ofNat 32 x == 0) = decide (x = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  bv_omega

/-- `mov d, #v` (`v` encodable). -/
theorem movImm_ok (s : State) (d : Reg) (v : BitVec 32) (hv : encodable v = true) :
    ∃ s', runBlock isa [.mov d (.imm v)] s = some s' ∧ s'.gpr d = v ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  ⟨s.setReg d v, by
    rw [runBlock_cons, show exec (.mov d (.imm v)) s = some (s.setReg d v) by simp [exec, Op2.eval, hv],
      runStep_some, runBlock_nil],
    RegUpd.gpr_setReg_self _ _ _, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl, rfl⟩

/-! ## Copying blocks -/

/-- What a copy keeps, after its first `k` bytes. -/
structure Copied (A B : Addr) (c : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  copied : ∀ t < k, s.mem (B + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t)
  frame : Frame [⟨B, 16 * c⟩] s₀.mem s.mem

/-- `ldr t0, [r0, #d]; str t0, [r1, #d]`: the copy's next word. -/
theorem copyWord_ok {A B : BitVec 32} {c : Nat} {s₀ s : State} {j d : Nat} (hd : d < 16) (hd4 : d % 4 = 0)
    (hj : j < c) (hfA : A.toNat + 16 * c ≤ 2 ^ 32) (hfB : B.toNat + 16 * c ≤ 2 ^ 32)
    (hsep : Region.Disjoint ⟨State.addr A, 16 * c⟩ ⟨State.addr B, 16 * c⟩)
    (hr : InRegions (s.rd ++ s.wr) (State.addr A + BitVec.ofNat 64 (16 * j + d)) 4)
    (hw : InRegions s.wr (State.addr B + BitVec.ofNat 64 (16 * j + d)) 4)
    (h0 : s.gpr .r0 = A + BitVec.ofNat 32 (16 * j)) (h1 : s.gpr .r12 = B + BitVec.ofNat 32 (16 * j))
    (hi : Copied (State.addr A) (State.addr B) c s₀ (16 * j + d) s) :
    ∃ s', runBlock isa [.ldr t0 .r0 d, .str t0 .r12 d] s = some s' ∧
      Copied (State.addr A) (State.addr B) c s₀ (16 * j + d + 4) s' ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have eA : State.addr (s.gpr .r0 + BitVec.ofNat 32 d) = State.addr A + BitVec.ofNat 64 (16 * j + d) := by
    rw [h0, add_ofNat_ofNat, addr_add (by omega)]
  have eB : State.addr (s.gpr .r12 + BitVec.ofNat 32 d) = State.addr B + BitVec.ofNat 64 (16 * j + d) := by
    rw [h1, add_ofNat_ofNat, addr_add (by omega)]
  have h₁ : (s.setReg t0 (s.mem.readW (State.addr A + BitVec.ofNat 64 (16 * j + d)) 32)).gpr .r12 = s.gpr .r12 :=
    RegUpd.gpr_setReg_of_ne _ _ (by decide)
  refine ⟨{ s.setReg t0 (s.mem.readW (State.addr A + BitVec.ofNat 64 (16 * j + d)) 32) with
      mem := s.mem.writeW (State.addr B + BitVec.ofNat 64 (16 * j + d))
        (s.mem.readW (State.addr A + BitVec.ofNat 64 (16 * j + d)) 32) }, ?_,
    ⟨fun t ht' => ?_, hi.frame.trans fun x hx => ?_⟩, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl⟩
  · rw [runBlock_cons, exec_ldr (by omega) (by rw [eA]; exact hr), eA, runStep_some, runBlock_cons,
      exec_str (by omega) (by rw [h₁, eB]; exact hw), runStep_some, runBlock_nil, h₁, eB,
      RegUpd.gpr_setReg_self]
    rfl
  · have hn : 16 * c < 2 ^ 64 := by omega
    have hAs : ∀ t < 16 * c, s.mem (State.addr A + BitVec.ofNat 64 t) = s₀.mem (State.addr A + BitVec.ofNat 64 t) :=
      fun t ht => hi.frame.bytes (R := ⟨State.addr A, 16 * c⟩)
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep) (by simp only; omega) ht
    show (s.mem.writeW _ _) _ = _
    rw [writeW_readW32_apply]
    by_cases h8 : 16 * j + d ≤ t
    · rw [ite_eq_left (by rw [off_sub_toNat _ h8 (by omega)]; omega), off_sub_toNat _ h8 (by omega),
        Offset.add_add, show 16 * j + d + (t - (16 * j + d)) = t by omega, hAs t (by omega)]
    · rw [ite_eq_right (off_sub_not _ (Or.inl (by omega)) (by omega) (by omega) (by omega))]
      exact hi.copied t (by omega)
  · show (s.mem.writeW _ _) x = s.mem x
    rw [writeW_readW32_apply, ite_eq_right fun h =>
      hx _ (List.mem_singleton_self _) (Offset.sub_base _ (show 16 * j + d + 4 ≤ 16 * c by omega) _
        (by simp only [Region.Contains]; omega))]

/-- Copying, after `j` of `c` blocks. -/
structure CopyInv (A B : BitVec 32) (c : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  src : s.gpr .r0 = A + BitVec.ofNat 32 (16 * j)
  dst : s.gpr .r12 = B + BitVec.ofNat 32 (16 * j)
  cnt : s.gpr .r3 = BitVec.ofNat 32 (c - j)
  cp : Copied (State.addr A) (State.addr B) c s₀ (16 * j) s
  regs : ∀ r, r ≠ .r0 → r ≠ .r12 → r ≠ .r3 → r ≠ t0 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem copyBlocks_wp {A B : BitVec 32} {c : Nat} {s₀ : State} (hc : 0 < c) (hc8 : c ≤ 8)
    (hfA : A.toNat + 16 * c ≤ 2 ^ 32) (hfB : B.toNat + 16 * c ≤ 2 ^ 32)
    (hA : ∀ t < 16 * c, t % 4 = 0 → InRegions (s₀.rd ++ s₀.wr) (State.addr A + BitVec.ofNat 64 t) 4)
    (hB : ∀ t < 16 * c, t % 4 = 0 → InRegions s₀.wr (State.addr B + BitVec.ofNat 64 t) 4)
    (hsep : Region.Disjoint ⟨State.addr A, 16 * c⟩ ⟨State.addr B, 16 * c⟩) (hs : CopyInv A B c s₀ 0 s₀) :
    WP isa copyBlocks s₀ (CopyInv A B c s₀ c) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = c - j ∧ j < c ∧ CopyInv A B c s₀ j s)
    (fun n s hs => ?_) c s₀ ⟨0, by omega, hc, hs⟩
  obtain ⟨j, rfl, hj, hi⟩ := hs
  have rA : ∀ d < 16, d % 4 = 0 → ∀ s : State, s.rd = s₀.rd → s.wr = s₀.wr →
      InRegions (s.rd ++ s.wr) (State.addr A + BitVec.ofNat 64 (16 * j + d)) 4 := fun d hd hd4 s h1 h2 => by
    rw [h1, h2]; exact hA _ (by omega) (by omega)
  have rB : ∀ d < 16, d % 4 = 0 → ∀ s : State, s.wr = s₀.wr →
      InRegions s.wr (State.addr B + BitVec.ofNat 64 (16 * j + d)) 4 := fun d hd hd4 s h2 => by
    rw [h2]; exact hB _ (by omega) (by omega)
  obtain ⟨s₁, e₁, c₁, g₁, rd₁, wr₁, sp₁⟩ := copyWord_ok (d := 0) (by decide) (by decide) hj hfA hfB hsep
    (rA 0 (by decide) (by decide) s hi.rd hi.wr) (rB 0 (by decide) (by decide) s hi.wr) hi.src hi.dst
    (by simpa using hi.cp)
  obtain ⟨s₂, e₂, c₂, g₂, rd₂, wr₂, sp₂⟩ := copyWord_ok (d := 4) (by decide) (by decide) hj hfA hfB hsep
    (rA 4 (by decide) (by decide) s₁ (rd₁.trans hi.rd) (wr₁.trans hi.wr))
    (rB 4 (by decide) (by decide) s₁ (wr₁.trans hi.wr))
    (by rw [g₁ _ (by decide), hi.src]) (by rw [g₁ _ (by decide), hi.dst]) (by simpa using c₁)
  obtain ⟨s₃, e₃, c₃, g₃, rd₃, wr₃, sp₃⟩ := copyWord_ok (d := 8) (by decide) (by decide) hj hfA hfB hsep
    (rA 8 (by decide) (by decide) s₂ (rd₂.trans (rd₁.trans hi.rd)) (wr₂.trans (wr₁.trans hi.wr)))
    (rB 8 (by decide) (by decide) s₂ (wr₂.trans (wr₁.trans hi.wr)))
    (by rw [g₂ _ (by decide), g₁ _ (by decide), hi.src]) (by rw [g₂ _ (by decide), g₁ _ (by decide), hi.dst])
    c₂
  obtain ⟨s₄, e₄, c₄, g₄, rd₄, wr₄, sp₄⟩ := copyWord_ok (d := 12) (by decide) (by decide) hj hfA hfB hsep
    (rA 12 (by decide) (by decide) s₃ (rd₃.trans (rd₂.trans (rd₁.trans hi.rd)))
      (wr₃.trans (wr₂.trans (wr₁.trans hi.wr))))
    (rB 12 (by decide) (by decide) s₃ (wr₃.trans (wr₂.trans (wr₁.trans hi.wr))))
    (by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hi.src])
    (by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hi.dst]) c₃
  have g₄' : ∀ r, r ≠ t0 → s₄.gpr r = s.gpr r := fun r hr => by rw [g₄ r hr, g₃ r hr, g₂ r hr, g₁ r hr]
  obtain ⟨s₅, e₅, a₅, o₅, m₅, rd₅, wr₅, sp₅⟩ := addImm_ok s₄ .r0 .r0 16 (by decide)
  obtain ⟨s₆, e₆, a₆, o₆, m₆, rd₆, wr₆, sp₆⟩ := addImm_ok s₅ .r12 .r12 16 (by decide)
  obtain ⟨s₇, e₇, c₇, z₇, o₇, m₇, rd₇, wr₇, sp₇⟩ := subs1_ok s₆ .r3
  refine WP.of_runBlock ⟨s₇, by
    rw [show ([Instr.ldr t0 .r0 0, .str t0 .r12 0, .ldr t0 .r0 4, .str t0 .r12 4,
      .ldr t0 .r0 8, .str t0 .r12 8, .ldr t0 .r0 12, .str t0 .r12 12,
      .dp .add .r0 .r0 (.imm 16), .dp .add .r12 .r12 (.imm 16), .subs .r3 .r3 (.imm 1)] : List Instr) =
      [.ldr t0 .r0 0, .str t0 .r12 0] ++ ([.ldr t0 .r0 4, .str t0 .r12 4] ++ ([.ldr t0 .r0 8, .str t0 .r12 8] ++
      ([.ldr t0 .r0 12, .str t0 .r12 12] ++ ([.dp .add .r0 .r0 (.imm 16)] ++
      ([.dp .add .r12 .r12 (.imm 16)] ++ [.subs .r3 .r3 (.imm 1)]))))) from rfl,
      runBlock_append, e₁, Option.bind_some, runBlock_append, e₂, Option.bind_some, runBlock_append, e₃,
      Option.bind_some, runBlock_append, e₄, Option.bind_some, runBlock_append, e₅, Option.bind_some,
      runBlock_append, e₆, Option.bind_some, e₇], ?_⟩
  have hc₇ : s₇.gpr .r3 = BitVec.ofNat 32 (c - (j + 1)) := by
    rw [c₇, o₆ _ (by decide), o₅ _ (by decide), g₄' _ (by decide), hi.cnt,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.ofNat_sub_ofNat (by omega),
      show c - j - 1 = c - (j + 1) by omega]
  have hm : s₇.mem = s₄.mem := by rw [m₇, m₆, m₅]
  have hinv : CopyInv A B c s₀ (j + 1) s₇ := by
    refine ⟨?_, ?_, hc₇, ⟨fun t ht => ?_, by rw [hm]; exact c₄.frame⟩, fun r h1 h2 h3 h4 => ?_,
      by rw [rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁, hi.rd], by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁, hi.wr],
      by rw [sp₇, sp₆, sp₅, sp₄, sp₃, sp₂, sp₁, hi.sp]⟩
    · rw [o₇ _ (by decide), o₆ _ (by decide), a₅, g₄' _ (by decide), hi.src,
        show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, add_ofNat_ofNat,
        show 16 * j + 16 = 16 * (j + 1) by omega]
    · rw [o₇ _ (by decide), a₆, o₅ _ (by decide), g₄' _ (by decide), hi.dst,
        show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, add_ofNat_ofNat,
        show 16 * j + 16 = 16 * (j + 1) by omega]
    · rw [hm]; exact c₄.copied t (by omega)
    · rw [o₇ r h3, o₆ r h2, o₅ r h1, g₄' r h4, hi.regs r h1 h2 h3 h4]
  have hz : s₇.z = decide (c - (j + 1) = 0) := by
    rw [z₇, ← c₇, hc₇, ofNat32_beq_zero (by omega)]
  by_cases hl : j + 1 = c
  · refine .inl ⟨(eval_ne s₇).trans (by rw [hz]; simp; omega),
      by rw [show j + 1 = c from hl] at hinv; exact hinv⟩
  · exact .inr ⟨(eval_ne s₇).trans (by rw [hz]; simp; omega), c - (j + 1), by omega, j + 1, rfl,
      by omega, hinv⟩

/-! ## Slots -/

/-- The scratch buffer at `b`, in the writable regions. -/
structure ScrIn (rs : List Region) (b : BitVec 32) : Prop where
  mem : (⟨State.addr b, 4 * slots⟩ : Region) ∈ rs
  fit : b.toNat + 4 * slots ≤ 2 ^ 32

theorem ScrIn.slot {rs : List Region} {b : BitVec 32} (h : ScrIn rs b) {k : Nat} (hk : k < slots) :
    InRegions rs (wordAddr b k) 4 := slot_inR h.mem h.fit hk

theorem inRd {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩

/-- A slot is inside the scratch buffer. -/
theorem slot_sub {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {k : Nat} (hk : k < slots) :
    Region.Sub ⟨wordAddr b k, 4⟩ ⟨State.addr b, 4 * slots⟩ := by
  rw [slot_addr (by omega)]
  exact Offset.sub_base _ (by omega)

/-- A slot after a store to a slot. -/
theorem readW_slot_write {m : Mem} {b : BitVec 32} (hfit : b.toNat + 4 * slots ≤ 2 ^ 32) {j k : Nat}
    (v : BitVec 32) (hj : j < slots) (hk : k < slots) :
    (m.writeW (wordAddr b k) v).readW (wordAddr b j) 32 = if j = k then v else m.readW (wordAddr b j) 32 := by
  split
  · rename_i h; subst h; exact Mem.readW_writeW_self32 _ _ _
  · rename_i h; exact Mem.readW_writeW_sep (slot_sep b (by omega) (by omega) h) (by decide)

/-- `ldr d, [n, #4 k]`, `n` holding `b`. -/
theorem ldW_ok (s : State) (d n : Reg) {b : BitVec 32} {k : Nat} (hn : s.gpr n = b) (hk : 4 * k < 4096)
    (hin : InRegions (s.rd ++ s.wr) (wordAddr b k) 4) :
    ∃ s', runBlock isa [.ldr d n (4 * k)] s = some s' ∧ s'.gpr d = s.mem.readW (wordAddr b k) 32 ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  ⟨s.setReg d (s.mem.readW (wordAddr b k) 32), by
    rw [runBlock_cons, exec_ldr hk (by rw [hn]; exact hin), hn, runStep_some, runBlock_nil],
    RegUpd.gpr_setReg_self _ _ _, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl, rfl⟩

/-- `str t, [n, #4 k]`, `n` holding `b`. -/
theorem stW_ok (s : State) (t n : Reg) {b : BitVec 32} {k : Nat} (hn : s.gpr n = b) (hk : 4 * k < 4096)
    (hin : InRegions s.wr (wordAddr b k) 4) :
    runBlock isa [.str t n (4 * k)] s = some { s with mem := s.mem.writeW (wordAddr b k) (s.gpr t) } := by
  rw [runBlock_cons, exec_str hk (by rw [hn]; exact hin), hn, runStep_some, runBlock_nil]

/-- A store to a slot of the scratch buffer. -/
theorem stSlot_ok (s : State) (t n : Reg) {b : BitVec 32} {k : Nat} (hn : s.gpr n = b) (hk : k < slots)
    (hw : ScrIn s.wr b) :
    ∃ s', runBlock isa [.str t n (4 * k)] s = some s' ∧ s'.mem = s.mem.writeW (wordAddr b k) (s.gpr t) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.z = s.z ∧
      Frame [⟨wordAddr b k, 4⟩] s.mem s'.mem :=
  ⟨_, stW_ok s t n hn (by rw [slots_eq] at hk; omega) (hw.slot hk), rfl, rfl, rfl, rfl, rfl, rfl,
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)⟩

/-- A load of a slot of the scratch buffer. -/
theorem ldSlot_ok (s : State) (d n : Reg) {b : BitVec 32} {k : Nat} (hn : s.gpr n = b) (hk : k < slots)
    (hw : ScrIn s.wr b) :
    ∃ s', runBlock isa [.ldr d n (4 * k)] s = some s' ∧ s'.gpr d = s.mem.readW (wordAddr b k) 32 ∧
      (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp :=
  ldW_ok s d n hn (by rw [slots_eq] at hk; omega) (inRd (hw.slot hk))

/-- Stores of registers to distinct slots, through `n`, which none of them is. -/
theorem stW_list_ok (n : Reg) {b : BitVec 32} : ∀ (L : List (Nat × Reg)) (s : State), s.gpr n = b →
    ScrIn s.wr b → (L.map (·.1)).Nodup → (∀ x ∈ L, x.1 < slots) →
    ∃ s', runBlock isa (L.map fun x => .str x.2 n (4 * x.1)) s = some s' ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [⟨State.addr b, 4 * slots⟩] s.mem s'.mem ∧
      (∀ k, k ∉ L.map (·.1) → k < slots → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32) ∧
      ∀ x ∈ L, s'.mem.readW (wordAddr b x.1) 32 = s.gpr x.2
  | [], s, _, _, _, _ => ⟨s, rfl, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ _ _ => rfl,
      fun _ h => absurd h List.not_mem_nil⟩
  | x :: L, s, hn, hw, hnd, hin => by
    obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁, sp₁, -, f₁⟩ := stSlot_ok s x.2 n hn (hin x List.mem_cons_self) hw
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', g', rd', wr', sp', f', o', v'⟩ :=
      stW_list_ok n L s₁ (by rw [g₁, hn]) (by rw [wr₁]; exact hw) hnd.2
        fun y hy => hin y (List.mem_cons_of_mem _ hy)
    refine ⟨s', ?_, g'.trans g₁, rd'.trans rd₁, wr'.trans wr₁, sp'.trans sp₁,
      (f₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact slot_sub hw.fit (hin x List.mem_cons_self)⟩).trans f',
      fun k hk hks => ?_,
      fun y hy => ?_⟩
    · rw [List.map_cons, ← List.singleton_append, runBlock_append, e₁, Option.bind_some]; exact e'
    · simp only [List.map_cons, List.mem_cons, not_or] at hk
      rw [o' k hk.2 hks, m₁, readW_slot_write hw.fit _ hks (hin x List.mem_cons_self)]
      simp only [hk.1, ite_false]
    · rcases List.mem_cons.mp hy with rfl | hy
      · rw [o' _ hnd.1 (hin _ List.mem_cons_self), m₁, Mem.readW_writeW_self32]
      · rw [v' y hy, g₁]

/-- Loads of distinct slots into distinct registers, through `n`, which none of them is. -/
theorem ldW_list_ok (n : Reg) {b : BitVec 32} : ∀ (L : List (Reg × Nat)) (s : State), s.gpr n = b →
    ScrIn s.wr b → (∀ x ∈ L, x.1 ≠ n) → (L.map (·.1)).Nodup → (∀ x ∈ L, x.2 < slots) →
    ∃ s', runBlock isa (L.map fun x => .ldr x.1 n (4 * x.2)) s = some s' ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ L.map (·.1) → s'.gpr r = s.gpr r) ∧
      ∀ x ∈ L, s'.gpr x.1 = s.mem.readW (wordAddr b x.2) 32
  | [], s, _, _, _, _, _ => ⟨s, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ h => absurd h List.not_mem_nil⟩
  | x :: L, s, hn, hw, hne, hnd, hin => by
    obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁, sp₁⟩ := ldSlot_ok s x.1 n hn (hin x List.mem_cons_self) hw
    have hn₁ : s₁.gpr n = b := by rw [o₁ _ (hne x List.mem_cons_self).symm, hn]
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨s', e', m', rd', wr', sp', o', v'⟩ := ldW_list_ok n L s₁ hn₁ (by rw [wr₁]; exact hw)
      (fun y hy => hne y (List.mem_cons_of_mem _ hy)) hnd.2 fun y hy => hin y (List.mem_cons_of_mem _ hy)
    refine ⟨s', ?_, m'.trans m₁, rd'.trans rd₁, wr'.trans wr₁, sp'.trans sp₁, fun r hr => ?_, fun y hy => ?_⟩
    · rw [List.map_cons, ← List.singleton_append, runBlock_append, e₁, Option.bind_some]; exact e'
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [o' r hr.2, o₁ r hr.1]
    · rcases List.mem_cons.mp hy with rfl | hy
      · rw [o' _ hnd.1, v₁]
      · rw [v' y hy, m₁]

/-! ## Saving and restoring the callee-saved registers -/

/-- The callee-saved registers, in the order of `savedRegs`. -/
def sreg (i : Nat) : Reg := ((savedRegs.map (·.1))[i]?).getD .r4

theorem savedRegs_eq : savedRegs = (List.range 9).map fun i => (sreg i, savedSlot + i) := by decide

/-- The saved registers are in their slots. -/
def Saved (s₀ : State) (b : BitVec 32) (m : Mem) : Prop :=
  ∀ i < 9, m.readW (wordAddr b (savedSlot + i)) 32 = s₀.gpr (sreg i)

theorem save_ok {s : State} {base : Reg} {b : BitVec 32} (hw : ScrIn s.wr b) (hb : s.gpr base = b) :
    ∃ s', runBlock isa (saveRegs base) s = some s' ∧ Saved s b s'.mem ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ Frame [⟨State.addr b, 4 * slots⟩] s.mem s'.mem ∧
      ∀ k, k < savedSlot → s'.mem.readW (wordAddr b k) 32 = s.mem.readW (wordAddr b k) 32 := by
  let L : List (Nat × Reg) := (List.range 9).map fun i => (savedSlot + i, sreg i)
  have hL : saveRegs base = L.map fun x => .str x.2 base (4 * x.1) := by
    rw [saveRegs, savedRegs_eq]; simp only [L, List.map_map]; rfl
  have hslots : L.map (·.1) = (List.range 9).map fun i => savedSlot + i := by
    simp only [L, List.map_map]; rfl
  obtain ⟨s', e', g', rd', wr', sp', f', o', v'⟩ := stW_list_ok base L s hb hw (by rw [hslots]; decide)
    (fun x hx => by
      simp only [L, List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      rw [savedSlot_eq, slots_eq]; omega)
  refine ⟨s', by rw [hL]; exact e', fun i hi => ?_, g', rd', wr', sp', f', fun k hk => o' k ?_ (by
    rw [savedSlot_eq] at hk; rw [slots_eq]; omega)⟩
  · exact v' (savedSlot + i, sreg i) (by simp only [L, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩)
  · rw [hslots]
    simp only [List.mem_map, List.mem_range, not_exists, not_and]
    intro i hi h; omega

theorem sreg_ne_r12 : ∀ i < 9, sreg i ≠ .r12 := by decide

theorem restore_ok {s₀ s : State} {b : BitVec 32} (hw : ScrIn s.wr b) (hb : s.gpr .r12 = b)
    (hs : Saved s₀ b s.mem) :
    ∃ s', runBlock isa (restoreRegs .r12) s = some s' ∧ (∀ i < 9, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      (∀ r, (∀ i < 9, r ≠ sreg i) → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  let L : List (Reg × Nat) := (List.range 9).map fun i => (sreg i, savedSlot + i)
  have hL : restoreRegs .r12 = L.map fun x => .ldr x.1 .r12 (4 * x.2) := by
    rw [restoreRegs, savedRegs_eq]
  have hregs : L.map (·.1) = (List.range 9).map sreg := by simp only [L, List.map_map]; rfl
  obtain ⟨s', e', m', rd', wr', sp', o', v'⟩ := ldW_list_ok .r12 L s hb hw
    (fun x hx => by
      simp only [L, List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx; exact sreg_ne_r12 i hi)
    (by rw [hregs]; decide)
    (fun x hx => by
      simp only [L, List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      rw [savedSlot_eq, slots_eq]; omega)
  refine ⟨s', by rw [hL]; exact e', fun i hi => ?_, fun r hr => o' r ?_, m', rd', wr', sp'⟩
  · rw [v' (sreg i, savedSlot + i) (by simp only [L, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩)]
    exact hs i hi
  · rw [hregs]
    simp only [List.mem_map, List.mem_range, not_exists, not_and]
    exact fun i hi h => hr i hi h.symm

/-! ## The data -/

/-- The first `k` blocks are `F`'s, the others still `m₀`'s. -/
def DInv (m₀ m : Mem) (D : Addr) (n k : Nat) (F : Nat → Spec.Seed.Block) : Prop :=
  ∀ i < 16 * n, m (D + BitVec.ofNat 64 i) =
    if i < 16 * k then (F (i / 16)).getD (i % 16) 0 else m₀ (D + BitVec.ofNat 64 i)

theorem blocksAt_of_dinv {m₀ m : Mem} {D : Addr} {n : Nat} {F : Nat → Spec.Seed.Block}
    (h : DInv m₀ m D n n F) : Spec.Seed.blocksAt m D n = (List.range n).map F := by
  simp only [Spec.Seed.blocksAt]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.mp hj
  apply Vector.ext; intro t ht
  simp only [Spec.Seed.blockAt, Vector.getElem_ofFn]
  rw [Offset.add_add, h _ (by omega), ite_eq_left (by omega), show (16 * j + t) / 16 = j by omega,
    show (16 * j + t) % 16 = t by omega]
  simp [Vector.getD, ht]

end VG.Proof.Seed.Arm

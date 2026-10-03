import VerifiedGarbage.Proof.Argon2.Arm.Derive.Frame
import VerifiedGarbage.Proof.Argon2.Arm.Divide

/-!
# Argon2 on ARMv7: the state of the derivation's body

`Inv s₀ s`: in the body, `sp` and `r11` point to the locals (`E s₀`), the
permissions are those of the body's entry, and memory has changed only in
the memory matrix, `scratch`, the output, the locals and the 40 bytes of
stack below them. The arguments, the inputs and the saved registers are
therefore kept (`Inv.arg`, `Inv.input`, `Inv.done`).

The regions all lie at 32-bit addresses, so whether they are disjoint,
contain an access or lie in one another is a question about the addresses'
values (`disj32`, `contains32`, `sub32`), for `omega`.
-/

namespace VG.Proof.Argon2.Arm.Derive

open VG VG.Arm VG.Arm.FrameStack
open VG.Proof.Argon2.Arm (stkR addr_toNat)
open VG.Proof.MdStream.Arm (Upd Mupd)
open VG.Spec.Blake2 (bytesAt)

/-! ## Regions at 32-bit addresses -/

theorem disj32 {x y : BitVec 32} {n m : Nat} (h : x.toNat + n ≤ y.toNat ∨ y.toNat + m ≤ x.toNat)
    (hn : x.toNat + n ≤ 2 ^ 32) (hm : y.toNat + m ≤ 2 ^ 32) :
    Region.Disjoint ⟨State.addr x, n⟩ ⟨State.addr y, m⟩ := by
  rcases h with h | h
  · exact Offset.disjoint_of_le (by simp only [addr_toNat]; omega) (by simp only [addr_toNat]; omega)
  · exact (Offset.disjoint_of_le (r₁ := ⟨State.addr y, m⟩) (by simp only [addr_toNat]; omega)
      (by simp only [addr_toNat]; omega)).symm

theorem contains32 {x y : BitVec 32} {n m : Nat} (h₁ : y.toNat ≤ x.toNat)
    (h₂ : x.toNat + n ≤ y.toNat + m) :
    Region.Contains ⟨State.addr y, m⟩ (State.addr x) n := by
  simp only [Region.Contains]
  rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, addr_toNat]; exact h₁), addr_toNat, addr_toNat]
  omega

theorem sub32 {x y : BitVec 32} {n m : Nat} (h₁ : y.toNat ≤ x.toNat)
    (h₂ : x.toNat + n ≤ y.toNat + m) :
    Region.Sub ⟨State.addr x, n⟩ ⟨State.addr y, m⟩ := by
  intro a ha
  simp only [Region.Contains] at ha ⊢
  have hx := addr_toNat x
  have hy := addr_toNat y
  have := x.isLt
  bv_omega

/-- `x + k`, as a number. -/
theorem add_nat {x : BitVec 32} {k : Nat} (h : x.toNat + k < 2 ^ 32) :
    (x + BitVec.ofNat 32 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega),
    Nat.mod_eq_of_lt h]

/-! ## The regions of the body -/

section
variable (s₀ : State)

/-- The locals. -/
abbrev locR : Region := ⟨State.addr (E s₀), 144⟩

/-- The stack below the locals: a call of `vg_argon2_hprime` and its frame. -/
abbrev callR : Region := stkR (E s₀) 40

/-- The regions the body may write. -/
abbrev bodyW : List Region := [memR s₀, scrR s₀, outR s₀, locR s₀, callR s₀]

/-- The word at `[r11, #d]`. -/
abbrev lw (s : State) (d : Nat) : BitVec 32 := s.mem.readW (State.addr (E s₀ + BitVec.ofNat 32 d)) 32

end

theorem entry_gpr (s₀ : State) : (entry s₀).gpr = s₀.gpr := rfl
theorem entry_rd (s₀ : State) : (entry s₀).rd = s₀.rd := rfl

theorem entry_sp' (s₀ : State) : (entry s₀).sp = E s₀ := by
  simp only [entry, allocated, pushed_sp, List.length_cons, List.length_nil, BitVec.sub_sub,
    BitVec.ofNat_add_ofNat]

theorem loc_mem (s₀ : State) : locR s₀ ∈ (entry s₀).wr := by
  simp [entry, allocated, pushed, BitVec.sub_sub, BitVec.ofNat_add_ofNat]

theorem wr_mem (s₀ : State) {r : Region} (h : r ∈ s₀.wr) : r ∈ (entry s₀).wr := by
  simp only [entry, allocated, pushed, List.mem_cons]
  exact .inr (.inr (.inr h))

/-! ## The invariant -/

/-- The state of the body. -/
structure Inv (s₀ s : State) : Prop where
  sp : s.sp = E s₀
  r11 : s.gpr .r11 = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = (entry s₀).wr
  frame : Frame (bodyW s₀) (entry s₀).mem s.mem

/-- A step that writes registers other than `r11`, and memory within the body's regions. -/
theorem Inv.step {s₀ s t : State} (h : Inv s₀ s) (hs : t.sp = s.sp)
    (hb : t.gpr .r11 = s.gpr .r11) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hf : Frame (bodyW s₀) s.mem t.mem) : Inv s₀ t :=
  ⟨hs.trans h.sp, hb.trans h.r11, hrd.trans h.rd, hwr.trans h.wr, h.frame.trans hf⟩

theorem Inv.upd {s₀ s t : State} {r : Reg} {v : BitVec 32} (h : Inv s₀ s) (u : Upd s t r v)
    (h₁ : r ≠ .r11) : Inv s₀ t :=
  h.step u.sp (u.other _ h₁.symm) u.rd u.wr (by rw [u.mem]; exact Frame.refl _ _)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem E_nat : (E s₀).toNat = (E0 s₀).toNat - 200 := sub_toNat' (by have := hp.sp_lo; omega)

theorem E_hi : (E s₀).toNat + 256 ≤ 2 ^ 32 := by
  have := hp.sp_hi; have := hp.sp_lo; rw [E_nat hp]; omega

theorem loc_nat {d : Nat} (hd : d < 256) : (E s₀ + BitVec.ofNat 32 d).toNat = (E s₀).toNat + d :=
  add_nat (by have := E_hi hp; omega)

/-- A range above the stack the body's calls use, within the frames and locals. -/
theorem frame_stk {d n : Nat} (h : d + n ≤ 200) :
    Region.Sub ⟨State.addr (E s₀ + BitVec.ofNat 32 d), n⟩ (stkR0 s₀) := by
  have := hp.sp_lo; have := hp.sp_hi
  have h2 : (E0 s₀ - BitVec.ofNat 32 240).toNat = (E0 s₀).toNat - 240 := sub_toNat' (by omega)
  have e := E_nat hp
  have hh : State.addr (E0 s₀) - BitVec.ofNat 64 240 = State.addr (E0 s₀ - BitVec.ofNat 32 240) :=
    (addr_sub' (by omega)).symm
  have tL : (E s₀ + BitVec.ofNat 32 d).toNat = (E s₀).toNat + d := loc_nat hp (by omega)
  show Region.Sub _ ⟨State.addr (E0 s₀) - BitVec.ofNat 64 240, 240⟩
  rw [hh]
  exact sub32 (by rw [tL, h2]; omega) (by rw [tL, h2]; omega)

theorem call_stk : Region.Sub (callR s₀) (stkR0 s₀) := by
  have := hp.sp_lo; have := hp.sp_hi
  have e := E_nat hp
  have h1 : State.addr (E s₀) - BitVec.ofNat 64 40 = State.addr (E s₀ - BitVec.ofNat 32 40) :=
    (addr_sub' (by omega)).symm
  have h2 : State.addr (E0 s₀) - BitVec.ofNat 64 240 = State.addr (E0 s₀ - BitVec.ofNat 32 240) :=
    (addr_sub' (by omega)).symm
  show Region.Sub ⟨State.addr (E s₀) - BitVec.ofNat 64 40, 40⟩ ⟨State.addr (E0 s₀) - BitVec.ofNat 64 240, 240⟩
  have t1 : (E s₀ - BitVec.ofNat 32 40).toNat = (E0 s₀).toNat - 240 := by rw [sub_toNat' (by omega), e]; omega
  have t2 : (E0 s₀ - BitVec.ofNat 32 240).toNat = (E0 s₀).toNat - 240 := sub_toNat' (by omega)
  rw [h1, h2]
  exact sub32 (by rw [t1, t2]) (by rw [t1, t2]; omega)

/-- A word of the locals. -/
theorem loc_in {s : State} (h : Inv s₀ s) {d : Nat} (hd : d + 4 ≤ 144) :
    InRegions s.wr (State.addr (E s₀ + BitVec.ofNat 32 d)) 4 := by
  rw [h.wr]
  exact ⟨locR s₀, loc_mem s₀, contains32 (by rw [loc_nat hp (d := d) (by omega)]; omega)
    (by rw [loc_nat hp (d := d) (by omega)]; omega)⟩

theorem loc_in' {s : State} (h : Inv s₀ s) {d : Nat} (hd : d + 4 ≤ 144) :
    InRegions (s.rd ++ s.wr) (State.addr (E s₀ + BitVec.ofNat 32 d)) 4 :=
  let ⟨r, hr, hc⟩ := loc_in hp h hd
  ⟨r, List.mem_append_right _ hr, hc⟩

/-- What lies above the locals is outside the body's regions. -/
theorem above_disj {a : BitVec 32} {n : Nat} (ha : (E s₀).toNat + 144 ≤ a.toNat)
    (ha' : a.toNat + n ≤ (E0 s₀).toNat + 56)
    (hm : Region.Disjoint ⟨State.addr a, n⟩ (memR s₀)) (hs : Region.Disjoint ⟨State.addr a, n⟩ (scrR s₀))
    (ho : Region.Disjoint ⟨State.addr a, n⟩ (outR s₀)) :
    ∀ r ∈ bodyW s₀, Region.Disjoint ⟨State.addr a, n⟩ r := by
  have := hp.sp_lo; have := hp.sp_hi
  have hE := E_nat hp
  intro r hr
  simp only [bodyW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hm
  · exact hs
  · exact ho
  · exact disj32 (.inr (by omega)) (by omega) (by omega)
  · show Region.Disjoint _ ⟨State.addr (E s₀) - BitVec.ofNat 64 40, 40⟩
    rw [← addr_sub' (by omega)]
    exact disj32 (.inr (by rw [sub_toNat' (by omega)]; omega)) (by omega)
      (by rw [sub_toNat' (by omega)]; omega)

/-! ## The frames' words -/

theorem S1_nat : (pushed argRegs s₀).sp.toNat = (E0 s₀).toNat - 16 := sp1 (by have := hp.sp_lo; omega)

/-- What the first push leaves above `E0 - 16`, and the memory above it. -/
theorem entry_frame : Frame [stkR (E0 s₀) 56] s₀.mem (entry s₀).mem := by
  have := hp.sp_lo
  have e0 : (E0 s₀).toNat = s₀.sp.toNat := rfl
  have s1 := S1_nat hp
  have f₁ := VG.Proof.Argon2.Arm.pushed_stk (rs := argRegs) (s := s₀) (by simp only [List.length_cons, List.length_nil]; omega)
  have f₂ := VG.Proof.Argon2.Arm.pushed_stk (rs := savedRegs) (s := pushed argRegs s₀) (by simp only [List.length_cons, List.length_nil]; omega)
  refine (f₁.sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, VG.Proof.Argon2.Arm.stkR_sub (by simp) (by omega)⟩
  · simp only [List.mem_singleton] at hr; subst hr
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    have := VG.Proof.Argon2.Arm.stkR_inner (sp := E0 s₀) (a := 4 * savedRegs.length) (k := 16) (b := 56)
      (by simp) (by omega)
    simpa [pushed_sp] using this

/-- Word `j` of the second frame: `savedRegs[j]`. -/
theorem entry_saved {j : Nat} (hj : j < 10) :
    (entry s₀).mem.readW (State.addr (E s₀ + BitVec.ofNat 32 (144 + 4 * j))) 32 =
      s₀.gpr (savedRegs[j]?.getD .r0) := by
  have := hp.sp_lo; have := hp.sp_hi
  have s1 := S1_nat hp
  have e := E_nat hp
  have := VG.Proof.Argon2.Arm.storeWords_readW (pushed argRegs s₀).mem
    ((pushed argRegs s₀).sp - BitVec.ofNat 32 (4 * savedRegs.length))
    (savedRegs.map (pushed argRegs s₀).gpr) (by
      simp only [List.length_map, List.length_cons, List.length_nil]
      rw [sub_toNat' (by rw [s1]; omega), s1]; omega) (i := j) (by simpa using hj)
  rw [List.getElem_map] at this
  have ea : (pushed argRegs s₀).sp - BitVec.ofNat 32 (4 * savedRegs.length) + BitVec.ofNat 32 (4 * j) =
      E s₀ + BitVec.ofNat 32 (144 + 4 * j) := by
    apply BitVec.eq_of_toNat_eq
    rw [loc_nat hp (d := 144 + 4 * j) (by omega), BitVec.toNat_add, sub_toNat' (by simp only [List.length_cons, List.length_nil]; rw [s1]; omega), s1, BitVec.toNat_ofNat]
    simp only [List.length_cons, List.length_nil]
    rw [Nat.mod_eq_of_lt (a := 4 * j) (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  rw [ea] at this
  refine this.trans ?_
  simp only [pushed_gpr, List.getElem?_eq_getElem (show j < savedRegs.length by simpa using hj),
    Option.getD_some]

/-- Word `i` of the first frame: register argument `i`. -/
theorem entry_regArg {i : Nat} (hi : i < 4) :
    (entry s₀).mem.readW (State.addr (E s₀ + BitVec.ofNat 32 (184 + 4 * i))) 32 = arg s₀ i := by
  have := hp.sp_lo; have := hp.sp_hi
  have s1 := S1_nat hp
  have e := E_nat hp
  have e0 : (E0 s₀).toNat = s₀.sp.toNat := rfl
  have := VG.Proof.Argon2.Arm.storeWords_readW s₀.mem (s₀.sp - BitVec.ofNat 32 (4 * argRegs.length))
    (argRegs.map s₀.gpr) (by
      simp only [List.length_map, List.length_cons, List.length_nil]
      rw [sub_toNat' (by omega)]; omega) (i := i) (by simpa using hi)
  rw [List.getElem_map] at this
  have ea : s₀.sp - BitVec.ofNat 32 (4 * argRegs.length) + BitVec.ofNat 32 (4 * i) =
      E s₀ + BitVec.ofNat 32 (184 + 4 * i) := by
    apply BitVec.eq_of_toNat_eq
    rw [loc_nat hp (d := 184 + 4 * i) (by omega), BitVec.toNat_add, sub_toNat' (by simp only [List.length_cons, List.length_nil]; omega), BitVec.toNat_ofNat]
    simp only [List.length_cons, List.length_nil]
    rw [Nat.mod_eq_of_lt (a := 4 * i) (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  rw [ea] at this
  -- The second push and the allocation keep the first frame.
  have keep : (entry s₀).mem.readW (State.addr (E s₀ + BitVec.ofNat 32 (184 + 4 * i))) 32 =
      (pushed argRegs s₀).mem.readW (State.addr (E s₀ + BitVec.ofNat 32 (184 + 4 * i))) 32 := by
    refine (VG.Proof.Argon2.Arm.pushed_stk (rs := savedRegs) (s := pushed argRegs s₀) (by simp only [List.length_cons, List.length_nil]; omega)).readW
      (r := ⟨_, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    have tS : ((pushed argRegs s₀).sp - BitVec.ofNat 32 (4 * savedRegs.length)).toNat = (E0 s₀).toNat - 56 := by
      rw [sub_toNat' (by simp only [List.length_cons, List.length_nil]; omega), s1]
      simp only [List.length_cons, List.length_nil]; omega
    have tL : (E s₀ + BitVec.ofNat 32 (184 + 4 * i)).toNat = (E s₀).toNat + (184 + 4 * i) := loc_nat hp (by omega)
    show Region.Disjoint _ ⟨State.addr (pushed argRegs s₀).sp - BitVec.ofNat 64 (4 * savedRegs.length), _⟩
    rw [← addr_sub' (by simp only [List.length_cons, List.length_nil]; omega)]
    have hc : savedRegs.length = 10 := rfl
    exact disj32 (.inr (by rw [tS, tL]; omega)) (by rw [tL]; omega) (by rw [tS]; omega)
  refine keep.trans (this.trans ?_)
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- The stack arguments, above the frames, are as on entry. -/
theorem entry_stackArg {i : Nat} (hi : 4 ≤ i) (hi' : i < 18) :
    (entry s₀).mem.readW (State.addr (E s₀ + BitVec.ofNat 32 (184 + 4 * i))) 32 = arg s₀ i := by
  have := hp.sp_lo; have := hp.sp_hi
  have e := E_nat hp
  have e0 : (E0 s₀).toNat = s₀.sp.toNat := rfl
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 4 := ⟨i - 4, by omega⟩
  have ea : E s₀ + BitVec.ofNat 32 (184 + 4 * (k + 4)) = s₀.sp + BitVec.ofNat 32 (4 * k) := by
    apply BitVec.eq_of_toNat_eq
    rw [loc_nat hp (d := 184 + 4 * (k + 4)) (by omega), add_nat (x := s₀.sp) (k := 4 * k) (by omega)]; omega
  rw [ea, (entry_frame hp).readW (r := ⟨_, 4⟩) (Region.contains_self _ _) ?_ (by decide)]
  · rfl
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  show Region.Disjoint _ ⟨State.addr (E0 s₀) - BitVec.ofNat 64 56, 56⟩
  rw [← addr_sub' (by omega)]
  exact disj32 (.inr (by rw [sub_toNat' (by omega), add_nat (x := s₀.sp) (k := 4 * k) (by omega)]; omega)) (by rw [add_nat (x := s₀.sp) (k := 4 * k) (by omega)]; omega)
    (by rw [sub_toNat' (by omega)]; omega)

/-! ## What the body keeps -/

theorem Inv.done {s : State} (h : Inv s₀ s) : BodyDone s₀ s := by
  have := hp.sp_lo; have := hp.sp_hi
  have hE := E_nat hp
  refine ⟨h.sp, fun j hj => ?_⟩
  have st := frame_stk hp (d := 148 + 4 * j) (n := 4) (by omega)
  rw [h.frame.readW (r := ⟨_, 4⟩) (Region.contains_self _ _) ?_ (by decide)]
  · rw [show 148 + 4 * j = 144 + 4 * (j + 1) by omega, entry_saved hp (by omega)]
  refine above_disj hp (by rw [loc_nat hp (d := 148 + 4 * j) (by omega)]; omega) (by rw [loc_nat hp (d := 148 + 4 * j) (by omega)]; omega) ?_ ?_ ?_
  · exact ((hp.stk_all _ (by simp)).sub_left st)
  · exact ((hp.stk_all _ (by simp)).sub_left st)
  · exact ((hp.stk_all _ (by simp)).sub_left st)

/-- The word of argument `i`, above the locals. -/
theorem arg_disj {i : Nat} (hi : i < 18) :
    ∀ r ∈ bodyW s₀, Region.Disjoint
      ⟨State.addr (E s₀ + BitVec.ofNat 32 (Impl.Argon2.Arm.Derive.argOff i)), 4⟩ r := by
  have := hp.sp_lo; have := hp.sp_hi
  have hE := E_nat hp
  have e0 : (E0 s₀).toNat = s₀.sp.toNat := rfl
  simp only [Impl.Argon2.Arm.Derive.argOff, Impl.Argon2.Arm.Derive.locals]
  refine above_disj hp (by rw [loc_nat hp (d := 144 + 40 + 4 * i) (by omega)]; omega) (by rw [loc_nat hp (d := 144 + 40 + 4 * i) (by omega)]; omega) ?_ ?_ ?_
    <;> by_cases h4 : i < 4
  all_goals first
    | (have st := frame_stk hp (d := 184 + 4 * i) (n := 4) (by omega)
       exact (hp.stk_all _ (by simp)).sub_left st)
    | (have sa : Region.Sub ⟨State.addr (E s₀ + BitVec.ofNat 32 (144 + 40 + 4 * i)), 4⟩ (argR s₀) := by
         show Region.Sub _ ⟨State.addr (s₀.sp + BitVec.ofNat 32 (4 * 0)), 56⟩
         exact sub32 (by rw [loc_nat hp (d := 144 + 40 + 4 * i) (by omega), add_nat (x := s₀.sp) (k := 4 * 0) (by omega)]; omega)
           (by rw [loc_nat hp (d := 144 + 40 + 4 * i) (by omega), add_nat (x := s₀.sp) (k := 4 * 0) (by omega)]; omega)
       exact (hp.ro_w _ (by simp) _ (by simp)).sub_left sa)

theorem Inv.arg {s : State} (h : Inv s₀ s) {i : Nat} (hi : i < 18) :
    lw s₀ s (Impl.Argon2.Arm.Derive.argOff i) = arg s₀ i := by
  rw [lw, h.frame.readW (r := ⟨_, 4⟩) (Region.contains_self _ _) (arg_disj hp hi) (by decide)]
  simp only [Impl.Argon2.Arm.Derive.argOff, Impl.Argon2.Arm.Derive.locals]
  rw [show 144 + 40 + 4 * i = 184 + 4 * i by omega]
  by_cases h4 : i < 4
  · exact entry_regArg hp h4
  · exact entry_stackArg hp (by omega) hi

theorem Inv.arg_in {s : State} (h : Inv s₀ s) {i : Nat} (hi : i < 18) :
    InRegions (s.rd ++ s.wr) (State.addr (E s₀ + BitVec.ofNat 32 (Impl.Argon2.Arm.Derive.argOff i))) 4 := by
  have := hp.sp_lo; have := hp.sp_hi
  have hE := E_nat hp
  have e0 : (E0 s₀).toNat = s₀.sp.toNat := rfl
  have s1 := S1_nat hp
  simp only [Impl.Argon2.Arm.Derive.argOff, Impl.Argon2.Arm.Derive.locals]
  rw [h.rd, h.wr]
  by_cases h4 : i < 4
  · -- The first frame, writable.
    refine ⟨⟨State.addr (s₀.sp - BitVec.ofNat 32 (4 * argRegs.length)), 4 * argRegs.length⟩,
      List.mem_append_right _ (by simp [entry, allocated, pushed]), ?_⟩
    have tA : (s₀.sp - BitVec.ofNat 32 (4 * argRegs.length)).toNat = (E0 s₀).toNat - 16 := by
      rw [sub_toNat' (by simp only [List.length_cons, List.length_nil]; omega)]
      simp only [List.length_cons, List.length_nil]
    have tL : (E s₀ + BitVec.ofNat 32 (144 + 40 + 4 * i)).toNat = (E s₀).toNat + (144 + 40 + 4 * i) :=
      loc_nat hp (by omega)
    exact contains32 (by rw [tL, tA]; omega) (by rw [tL, tA]; simp only [List.length_cons, List.length_nil]; omega)
  · refine ⟨argR s₀, List.mem_append_left _ (by rw [hp.rd]; simp), ?_⟩
    show Region.Contains ⟨State.addr (s₀.sp + BitVec.ofNat 32 (4 * 0)), 56⟩ _ _
    exact contains32 (by rw [loc_nat hp (d := 144 + 40 + 4 * i) (by omega), add_nat (x := s₀.sp) (k := 4 * 0) (by omega)]; omega)
      (by rw [loc_nat hp (d := 144 + 40 + 4 * i) (by omega), add_nat (x := s₀.sp) (k := 4 * 0) (by omega)]; omega)

/-- The inputs are kept. -/
theorem Inv.input {s : State} (h : Inv s₀ s) {R : Region}
    (hR : R ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀]) :
    bytesAt s.mem R.base R.len = bytesAt s₀.mem R.base R.len := by
  have hR' : R ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀, argR s₀] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl <;> simp
  have hS : R ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀, memR s₀, scrR s₀, outR s₀] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl <;> simp
  have stk := (hp.stk_all R hS).symm
  have hl : R.len ≤ 2 ^ 64 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl | rfl <;> exact Nat.le_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide))
  have hlo := hp.sp_lo
  apply Proof.Blake2.bytesAt_congr
  intro i hi
  rw [h.frame.bytes (R := R) (fun r hr => ?_) hl hi]
  · exact (entry_frame hp).bytes (R := R) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact stk.sub_right (VG.Proof.Argon2.Arm.stkR_sub (by decide) (by omega))) hl hi
  simp only [bodyW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hp.ro_w _ hR' _ (by simp)
  · exact hp.ro_w _ hR' _ (by simp)
  · exact hp.ro_w _ hR' _ (by simp)
  · exact stk.sub_right (by simpa using frame_stk hp (d := 0) (n := 144) (by decide))
  · exact stk.sub_right (call_stk hp)

end

end VG.Proof.Argon2.Arm.Derive

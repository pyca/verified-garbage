module

public import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Contract
public import VerifiedGarbage.Impl.Argon2.PPC64LE.Derive
import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.MdStream.PPC64LE.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Blake2.Stream
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch

/-!
# Argon2 on PPC64LE: the state of the derivation's body

The derivation's stack lies at offsets of `B s₀`, 384 bytes below the stack
pointer on entry (`at' s₀ d`): the 48 bytes of its calls' frames, its own
frame from `E s₀ = at' s₀ 48` (`Impl/Argon2/PPC64LE/Layout.lean`), and,
above the stack pointer on entry, the caller's Parameter Save Area, whose
arguments the derivation reads at `at' s₀ (432 + 8 i)`.

`Inv s₀ s`: in the body, `sp` and `r30` point to the frame, `r31` to
`scratch`, the registers the body never writes are the caller's, the
permissions are those of the body's entry, and memory has changed since the
setup (`setupMem`) only in the memory matrix, `scratch`, the output, H′'s
input and the loop variables in the frame, and the calls' frames below it.
The return address, the caller's registers and the arguments are therefore
kept (`Inv.arg`, `Inv.input`, `Inv.saved`).
-/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.Derive

open VG VG.PPC64LE
open VG.Proof.MdStream.PPC64LE (Upd Mupd)
open VG.Spec.Blake2 (bytesAt)
open VG.Impl.Argon2.PPC64LE.Derive (locals argOff savedSlots argSlots)

/-! ## The stack -/

section
variable (s₀ : State)

/-- The bottom of the stack the derivation uses. -/
abbrev B : Addr := s₀.sp - BitVec.ofNat 64 384

/-- `d` bytes above `B s₀`. -/
abbrev at' (d : Nat) : Addr := B s₀ + BitVec.ofNat 64 d

/-- The frame's stack pointer: the body's. -/
abbrev E : Addr := s₀.sp - BitVec.ofNat 64 336

/-- The state the body starts in. -/
def entry : State := allocated 336 s₀

/-- H′'s input in the frame: H₀, LE32(column), LE32(lane). -/
abbrev inR : Region := ⟨at' s₀ 80, 72⟩

/-- The loop variables and temporaries in the frame. -/
abbrev varR : Region := ⟨at' s₀ 256, 128⟩

/-- The frames of the functions the body calls. -/
abbrev callR : Region := ⟨B s₀, 48⟩

/-- The regions the body writes. -/
abbrev bodyW : List Region := [memR s₀, scrR s₀, outR s₀, inR s₀, varR s₀, callR s₀]

/-- The registers the body never writes. -/
abbrev untouched : List Reg :=
  [.r2, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27]

/-- What the body stores in its frame first: the return address, the
caller's `r28`–`r31` and the register arguments. -/
def setupMem : Mem :=
  Spill.saveMem ((entry s₀).mem.writeW (E s₀ + BitVec.ofNat 64 104) s₀.lr) (E s₀) s₀.gpr
    (savedSlots ++ argSlots)

/-- The doubleword at `r30 + d`. -/
abbrev lw (s : State) (d : Nat) : BitVec 64 := s.mem.readW (E s₀ + BitVec.ofNat 64 d) 64

end

theorem E_eq (s₀ : State) : E s₀ = at' s₀ 48 :=
  Offset.sub_ofNat_eq s₀.sp (by decide)

theorem E_add (s₀ : State) (d : Nat) : E s₀ + BitVec.ofNat 64 d = at' s₀ (48 + d) := by
  show _ = B s₀ + BitVec.ofNat 64 (48 + d)
  rw [E_eq, BitVec.add_assoc, BitVec.ofNat_add]

theorem entry_sp (s₀ : State) : (entry s₀).sp = E s₀ := rfl
theorem entry_gpr (s₀ : State) : (entry s₀).gpr = s₀.gpr := rfl
theorem entry_rd (s₀ : State) : (entry s₀).rd = s₀.rd := rfl
theorem entry_lr (s₀ : State) : (entry s₀).lr = s₀.lr := rfl
theorem entry_wr (s₀ : State) : (entry s₀).wr = ⟨at' s₀ 80, 304⟩ :: s₀.wr := by
  show (⟨E s₀ + BitVec.ofNat 64 32, 304⟩ : Region) :: s₀.wr = _
  rw [E_add]

/-! ## The invariant -/

/-- The state of the body. -/
structure Inv (s₀ s : State) : Prop where
  sp : s.sp = E s₀
  r30 : s.gpr .r30 = E s₀
  r31 : s.gpr .r31 = scrP s₀
  keep : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = (entry s₀).wr
  frame : Frame (bodyW s₀) (setupMem s₀) s.mem

/-- A step that writes registers the invariant does not name, and memory
within the body's regions. -/
theorem Inv.step {s₀ s t : State} (h : Inv s₀ s) (hs : t.sp = s.sp)
    (h30 : t.gpr .r30 = s.gpr .r30) (h31 : t.gpr .r31 = s.gpr .r31)
    (hk : ∀ r ∈ untouched, t.gpr r = s.gpr r) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hf : Frame (bodyW s₀) s.mem t.mem) : Inv s₀ t :=
  ⟨hs.trans h.sp, h30.trans h.r30, h31.trans h.r31, fun r hr => (hk r hr).trans (h.keep r hr),
    hrd.trans h.rd, hwr.trans h.wr, h.frame.trans hf⟩

/-- A register the invariant does not name. -/
abbrev Free (r : Reg) : Prop := r ≠ .r30 ∧ r ≠ .r31 ∧ r ∉ untouched

theorem Inv.upd {s₀ s t : State} {r : Reg} {v : BitVec 64} (h : Inv s₀ s) (u : Upd s t r v)
    (hr : Free r := by decide) : Inv s₀ t :=
  h.step u.sp (u.other _ (Ne.symm hr.1)) (u.other _ (Ne.symm hr.2.1))
    (fun q hq => u.other _ fun e => hr.2.2 (e ▸ hq)) u.rd u.wr (by rw [u.mem]; exact Frame.refl _ _)

theorem Inv.mupd {s₀ s t : State} {m : Mem} (h : Inv s₀ s) (u : Mupd s t m)
    (hf : Frame (bodyW s₀) s.mem m) : Inv s₀ t :=
  h.step u.sp (by rw [u.gpr]) (by rw [u.gpr]) (fun _ _ => by rw [u.gpr]) u.rd u.wr (u.mem ▸ hf)

/-! ## Facts of the precondition about the stack -/

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem B_toNat : (B s₀).toNat = s₀.sp.toNat - 384 :=
  toNat_sub_ofNat' (by have := hp.sp_lo; omega)

theorem B_hi : (B s₀).toNat + 560 ≤ 2 ^ 64 := by
  have := hp.sp_hi; have := hp.sp_lo; rw [B_toNat hp]; omega

omit hp in
/-- The stack the derivation uses, at offsets of `B`. -/
theorem stk_eq : stkR0 s₀ = ⟨B s₀, 384⟩ := rfl

omit hp in
theorem stk_sub {d n : Nat} (h : d + n ≤ 384) : Region.Sub ⟨at' s₀ d, n⟩ (stkR0 s₀) :=
  Offset.sub_base _ h

end

/-- `x` bytes above the stack pointer on entry. -/
theorem sp_add (s₀ : State) (x : Nat) : s₀.sp + BitVec.ofNat 64 x = at' s₀ (384 + x) := by
  show _ = s₀.sp - BitVec.ofNat 64 384 + BitVec.ofNat 64 (384 + x)
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

/-- The arguments in the Parameter Save Area. -/
theorem stackArg_eq (s₀ : State) (i : Nat) : stackArgAddr s₀ i = at' s₀ (416 + 8 * (8 + i)) := by
  rw [stackArgAddr, sp_add, show 384 + (32 + 8 * (8 + i)) = 416 + 8 * (8 + i) by omega]

theorem callR_eq (s₀ : State) : below (E s₀) 48 = callR s₀ := by
  show (⟨s₀.sp - BitVec.ofNat 64 336 - BitVec.ofNat 64 48, 48⟩ : Region) = ⟨s₀.sp - BitVec.ofNat 64 384, 48⟩
  rw [BitVec.sub_sub]
  rfl

/-! ## The frame's slots -/

theorem slots_fits : Spill.Fits (savedSlots ++ argSlots) := by decide

theorem slots_in : ∀ p ∈ savedSlots ++ argSlots, 112 ≤ p.2 ∧ p.2 + 8 ≤ 112 + 96 := by decide

/-- The slots the setup writes, and the back chain the frame's push stored. -/
abbrev setupR (s₀ : State) : Region := ⟨at' s₀ 48, 208⟩

theorem setupMem_frame (s₀ : State) : Frame [setupR s₀] s₀.mem (setupMem s₀) := by
  have h₁ : Frame [setupR s₀] s₀.mem (entry s₀).mem := by
    show Frame _ s₀.mem (s₀.mem.write (E s₀) 8 s₀.sp)
    refine (Frame.refl _ _).write (List.mem_singleton_self _) _ ?_
    rw [E_eq]
    exact Offset.contains _ (by decide) (by decide) (by decide)
  have h₂ := (h₁.writeW (List.mem_singleton_self _) (b := E s₀ + BitVec.ofNat 64 104) s₀.lr (by
    rw [E_add]; exact Offset.contains _ (by decide) (by decide) (by decide)))
  have h₃ := Spill.saveMem_frame slots_in (by decide)
    ((entry s₀).mem.writeW (E s₀ + BitVec.ofNat 64 104) s₀.lr) (E s₀) s₀.gpr
  refine h₂.trans (h₃.sub fun r hr => ?_)
  simp only [List.mem_singleton] at hr; subst hr
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  rw [E_add]
  exact Offset.sub _ (by decide) (by decide)

theorem setupMem_slot (s₀ : State) {r : Reg} {d : Nat} (h : (r, d) ∈ savedSlots ++ argSlots) :
    (setupMem s₀).readW (E s₀ + BitVec.ofNat 64 d) 64 = s₀.gpr r :=
  Spill.saveMem_saved slots_fits _ _ _ (r, d) h

theorem setupMem_lr (s₀ : State) :
    (setupMem s₀).readW (E s₀ + BitVec.ofNat 64 104) 64 = s₀.lr := by
  unfold setupMem
  rw [(Spill.saveMem_frame slots_in (by decide) _ _ _).readW (r := ⟨E s₀ + BitVec.ofNat 64 104, 8⟩)
    (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self64]

/-! ## What the body's writes keep -/

/-- The slots of the setup, and the return address. -/
abbrev slotR (s₀ : State) : Region := ⟨at' s₀ 152, 104⟩

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- A region of the stack the derivation uses is outside the buffers. -/
theorem stk_disj {d n : Nat} (h : d + n ≤ 384) :
    ∀ r ∈ [memR s₀, scrR s₀, outR s₀], Region.Disjoint ⟨at' s₀ d, n⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact (hp.stk_all _ (by simp)).sub_left (stk_sub h)

/-- A region of the stack outside the body's own: neither H′'s input, nor
the loop variables, nor the calls' frames. -/
theorem frame_disj {d n : Nat} (h₁ : 48 ≤ d ∧ d + n ≤ 80 ∨ 152 ≤ d ∧ d + n ≤ 256) :
    ∀ r ∈ bodyW s₀, Region.Disjoint ⟨at' s₀ d, n⟩ r := by
  intro r hr
  simp only [bodyW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact stk_disj hp (by omega) _ (by simp)
  · exact stk_disj hp (by omega) _ (by simp)
  · exact stk_disj hp (by omega) _ (by simp)
  · exact Offset.disjoint _ (by omega) (by omega) (by omega)
  · exact Offset.disjoint _ (by omega) (by omega) (by omega)
  · have e : B s₀ = B s₀ + BitVec.ofNat 64 0 := (BitVec.add_zero _).symm
    show Region.Disjoint _ ⟨B s₀, 48⟩
    rw [e]
    exact Offset.disjoint _ (by omega) (by omega) (by omega)

omit hp in
theorem argR_eq : argR s₀ = ⟨at' s₀ 480, 80⟩ := by
  show (⟨stackArgAddr s₀ 0, 80⟩ : Region) = _
  rw [stackArg_eq]

/-- The arguments in the Parameter Save Area are outside the body's regions. -/
theorem arg_disj {d n : Nat} (h₁ : 480 ≤ d) (h₂ : d + n ≤ 560) :
    ∀ r ∈ bodyW s₀, Region.Disjoint ⟨at' s₀ d, n⟩ r := by
  have sub : Region.Sub ⟨at' s₀ d, n⟩ (argR s₀) := by
    rw [argR_eq]; exact Offset.sub _ h₁ (by omega)
  intro r hr
  simp only [bodyW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hp.ro_w _ (by simp) _ (by simp)).sub_left sub
  · exact (hp.ro_w _ (by simp) _ (by simp)).sub_left sub
  · exact (hp.ro_w _ (by simp) _ (by simp)).sub_left sub
  · exact Offset.disjoint _ (by omega) (by omega) (by omega)
  · exact Offset.disjoint _ (by omega) (by omega) (by omega)
  · have e : B s₀ = B s₀ + BitVec.ofNat 64 0 := (BitVec.add_zero _).symm
    show Region.Disjoint _ ⟨B s₀, 48⟩
    rw [e]
    exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem Inv.slot {s : State} (h : Inv s₀ s) {d : Nat} (h₁ : 152 ≤ d) (h₂ : d + 8 ≤ 256) :
    s.mem.readW (at' s₀ d) 64 = (setupMem s₀).readW (at' s₀ d) 64 :=
  h.frame.readW (Region.contains_self _ _) (frame_disj hp (.inr ⟨h₁, h₂⟩)) (by decide)

/-- The doubleword `d` bytes above the frame's stack pointer, among the setup's
slots. -/
theorem Inv.saved {s : State} (h : Inv s₀ s) {r : Reg} {d : Nat}
    (hr : (r, d) ∈ savedSlots ++ argSlots) : lw s₀ s d = s₀.gpr r := by
  have := slots_in _ hr
  rw [lw, E_add, h.slot hp (by simp only at this; omega) (by simp only at this; omega), ← E_add,
    setupMem_slot s₀ hr]

theorem Inv.lr {s : State} (h : Inv s₀ s) : lw s₀ s 104 = s₀.lr := by
  rw [lw, E_add, h.slot hp (by decide) (by decide), ← E_add, setupMem_lr]

/-- The arguments, from the frame or the Parameter Save Area. -/
theorem Inv.arg {s : State} (h : Inv s₀ s) {i : Nat} (hi : i < 18) :
    s.mem.readW (E s₀ + BitVec.ofNat 64 (argOff i)) 64 = arg s₀ i := by
  by_cases h8 : i < 8
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h.saved hp (r := .r3) (d := 144) (by decide)
    · exact h.saved hp (r := .r4) (d := 152) (by decide)
    · exact h.saved hp (r := .r5) (d := 160) (by decide)
    · exact h.saved hp (r := .r6) (d := 168) (by decide)
    · exact h.saved hp (r := .r7) (d := 176) (by decide)
    · exact h.saved hp (r := .r8) (d := 184) (by decide)
    · exact h.saved hp (r := .r9) (d := 192) (by decide)
    · exact h.saved hp (r := .r10) (d := 200) (by decide)
  · obtain ⟨k, rfl⟩ : ∃ k, i = 8 + k := ⟨i - 8, by omega⟩
    have ea : E s₀ + BitVec.ofNat 64 (argOff (8 + k)) = at' s₀ (416 + 8 * (8 + k)) := by
      have e : argOff (8 + k) = 368 + 8 * (8 + k) := by
        simp only [argOff, locals]; rw [ite_eq_right_iff.mpr (by omega)]
      rw [E_add, e, show 48 + (368 + 8 * (8 + k)) = 416 + 8 * (8 + k) by omega]
    rw [ea, h.frame.readW (Region.contains_self _ _) (arg_disj hp (by omega) (by omega)) (by decide),
      (setupMem_frame s₀).readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide),
      ← stackArg_eq, show 8 + k = k + 8 by omega]
    rfl

theorem Inv.arg32 {s : State} (h : Inv s₀ s) {i : Nat} (hi : i < 18) :
    s.mem.readW (E s₀ + BitVec.ofNat 64 (argOff i)) 32 = arg32 s₀ i :=
  Mem.readW_lo32 (h.arg hp hi)

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
    rcases hR with rfl | rfl | rfl | rfl <;> exact Nat.le_of_lt (BitVec.isLt _)
  apply Proof.Blake2.bytesAt_congr
  intro i hi
  rw [h.frame.bytes (R := R) (fun r hr => ?_) hl hi]
  · exact (setupMem_frame s₀).bytes (R := R) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact stk.sub_right (stk_sub (by decide))) hl hi
  simp only [bodyW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hp.ro_w _ hR' _ (by simp)
  · exact hp.ro_w _ hR' _ (by simp)
  · exact hp.ro_w _ hR' _ (by simp)
  · exact stk.sub_right (stk_sub (by decide))
  · exact stk.sub_right (stk_sub (by decide))
  · exact stk.sub_right (by
      have e : B s₀ = B s₀ + BitVec.ofNat 64 0 := (BitVec.add_zero _).symm
      show Region.Sub ⟨B s₀, 48⟩ _
      rw [e]; exact stk_sub (by decide))

end

end VG.Proof.Argon2.PPC64LE.Derive

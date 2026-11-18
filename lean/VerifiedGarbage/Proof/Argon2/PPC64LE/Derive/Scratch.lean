module

public import VerifiedGarbage.Proof.Argon2.PPC64LE.HPrime.Frame
import VerifiedGarbage.Proof.Blake2.Scratch
import VerifiedGarbage.Proof.Argon2.HPrime
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Argon2.PPC64LE.Divide
import VerifiedGarbage.Proof.Argon2.Divide
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.MdStream.PPC64LE.Basic
public import VerifiedGarbage.Proof.MdStream.Spec
import VerifiedGarbage.Proof.MdStream.PPC64LE.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Impl.Argon2.PPC64LE.Derive
import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.Blake2.Stream
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Spec.Argon2.Contract
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Argon2.Dimensions

/-! ### `Argon2.PPC64LE.Derive.Parameters`, which this module and modules that import it used -/

section

/-! ### `Argon2.PPC64LE.Derive.Locals`, which this module and modules that import it used -/

section

/-! ### `Argon2.PPC64LE.Derive.Body`, which this module and modules that import it used -/

section

/-! ### `Argon2.PPC64LE.Derive.Contract`, which this module and modules that import it used -/

section

/-!
# Argon2 on PPC64LE: the contract of the derivation's proof

`derivePPC`: `vg_argon2`'s contract, with its precondition a structure
(`DPre`; `Derive/Verified.lean` reaches the shared contract). The
derivation uses the 384 bytes of stack below the stack pointer: its frame of
336 bytes, and 48 for the frames of the functions it calls.
-/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.Derive

open VG VG.PPC64LE VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

/-- Argument `i`: `r3`–`r10`, then those in the Parameter Save Area. -/
def arg (s : State) : Nat → BitVec 64
  | 0 => s.gpr .r3
  | 1 => s.gpr .r4
  | 2 => s.gpr .r5
  | 3 => s.gpr .r6
  | 4 => s.gpr .r7
  | 5 => s.gpr .r8
  | 6 => s.gpr .r9
  | 7 => s.gpr .r10
  | i + 8 => stackArg s i

/-- The 32-bit argument `i`. -/
abbrev arg32 (s : State) (i : Nat) : BitVec 32 := (arg s i).setWidth 32

/-- The 32-bit arguments: `kind`, `iterations`, `memory_cost`, `lanes` and
`threads`. -/
def intArgs : List Nat := [0, 5, 6, 7, 8]

/-- What is public of argument `i`: its low 32 bits if it is a 32-bit one. -/
def argPub (s : State) (i : Nat) : BitVec 64 :=
  if i ∈ intArgs then (arg32 s i).setWidth 64 else arg s i

section
variable (s₀ : State)

abbrev kindV : BitVec 32 := arg32 s₀ 0
abbrev pwP : Addr := arg s₀ 1
abbrev pwL : Nat := (arg s₀ 2).toNat
abbrev saltP : Addr := arg s₀ 3
abbrev saltL : Nat := (arg s₀ 4).toNat
abbrev itersN : Nat := (arg32 s₀ 5).toNat
abbrev mcostN : Nat := (arg32 s₀ 6).toNat
abbrev lanesN : Nat := (arg32 s₀ 7).toNat
abbrev threadsN : Nat := (arg32 s₀ 8).toNat
abbrev secP : Addr := arg s₀ 9
abbrev secL : Nat := (arg s₀ 10).toNat
abbrev adP : Addr := arg s₀ 11
abbrev adL : Nat := (arg s₀ 12).toNat
abbrev memP : Addr := arg s₀ 13
abbrev blocksN : Nat := (arg s₀ 14).toNat
abbrev scrP : Addr := arg s₀ 15
abbrev outP : Addr := arg s₀ 16
abbrev outL : Nat := (arg s₀ 17).toNat

/-- The parameters. -/
abbrev prm : Params := params (kindV s₀).toNat (itersN s₀) (mcostN s₀) (lanesN s₀) (outL s₀)

abbrev pwR : Region := ⟨pwP s₀, pwL s₀⟩
abbrev saltR : Region := ⟨saltP s₀, saltL s₀⟩
abbrev secR : Region := ⟨secP s₀, secL s₀⟩
abbrev adR : Region := ⟨adP s₀, adL s₀⟩
abbrev memR : Region := ⟨memP s₀, blocksN s₀ * 1024⟩
abbrev scrR : Region := ⟨scrP s₀, 16384⟩
abbrev outR : Region := ⟨outP s₀, outL s₀⟩
/-- The ten arguments in the Parameter Save Area. -/
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 80⟩
/-- The stack the derivation uses. -/
abbrev stkR0 : Region := below s₀.sp 384

/-- The inputs, on entry. -/
abbrev pwB : List Byte := bytesAt s₀.mem (pwR s₀).base (pwL s₀)
abbrev saltB : List Byte := bytesAt s₀.mem (saltR s₀).base (saltL s₀)
abbrev secB : List Byte := bytesAt s₀.mem (secR s₀).base (secL s₀)
abbrev adB : List Byte := bytesAt s₀.mem (adR s₀).base (adL s₀)

end

/-- The facts of `derivePPC`'s precondition. -/
structure DPre (s₀ : State) : Prop where
  rd : s₀.rd = [pwR s₀, saltR s₀, secR s₀, adR s₀, argR s₀]
  wr : s₀.wr = [memR s₀, scrR s₀, outR s₀]
  ro_w : ∀ r ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀, argR s₀], ∀ w ∈ [memR s₀, scrR s₀, outR s₀],
    r.Disjoint w
  mem_scr : (memR s₀).Disjoint (scrR s₀)
  mem_out : (memR s₀).Disjoint (outR s₀)
  scr_out : (scrR s₀).Disjoint (outR s₀)
  stk_all : ∀ r ∈ [pwR s₀, saltR s₀, secR s₀, adR s₀, memR s₀, scrR s₀, outR s₀], (stkR0 s₀).Disjoint r
  pw_fits : (pwP s₀).toNat + pwL s₀ ≤ 2 ^ 64
  salt_fits : (saltP s₀).toNat + saltL s₀ ≤ 2 ^ 64
  sec_fits : (secP s₀).toNat + secL s₀ ≤ 2 ^ 64
  ad_fits : (adP s₀).toNat + adL s₀ ≤ 2 ^ 64
  mem_fits : (memP s₀).toNat + blocksN s₀ * 1024 ≤ 2 ^ 64
  scr_fits : (scrP s₀).toNat + 16384 ≤ 2 ^ 64
  out_fits : (outP s₀).toNat + outL s₀ ≤ 2 ^ 64
  sp_lo : 384 ≤ s₀.sp.toNat
  sp_hi : s₀.sp.toNat + 32 + 8 * 18 ≤ 2 ^ 64
  kind_le : (kindV s₀).toNat ≤ 2
  valid : valid (prm s₀) (pwL s₀) (saltL s₀) (secL s₀) (adL s₀)
  threads : 1 ≤ threadsN s₀ ∧ threadsN s₀ < 2 ^ 24
  blocks : blocksN s₀ = (prm s₀).blocks

/-- `vg_argon2`. -/
def derivePPC : Contract isa where
  pre := DPre
  post s s' := bytesAt s'.mem (outP s) (outL s) =
    derive (prm s) (pwB s) (saltB s) (secB s) (adB s)
  pub s₁ s₂ := (s₁.sp = s₂.sp ∧ ∀ i < 18, argPub s₁ i = argPub s₂ i) ∧
    references (prm s₁) (pwB s₁) (saltB s₁) (secB s₁) (adB s₁) =
      references (prm s₂) (pwB s₂) (saltB s₂) (secB s₂) (adB s₂)

namespace DPre
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem lanes_pos : 1 ≤ lanesN s₀ := hp.valid.1
theorem lanes_lt : lanesN s₀ < 2 ^ 24 := hp.valid.2.1
theorem passes_pos : 1 ≤ itersN s₀ := hp.valid.2.2.1
theorem memory_ge : 8 * lanesN s₀ ≤ mcostN s₀ := hp.valid.2.2.2.2.1
theorem tag_ge : 4 ≤ outL s₀ := hp.valid.2.2.2.2.2.2.1
theorem tag_lt : outL s₀ < 2 ^ 32 := hp.valid.2.2.2.2.2.2.2.1

theorem segLen_two : 2 ≤ (prm s₀).segmentLen :=
  Proof.Argon2.segmentLen_ge_two _ hp.lanes_pos hp.memory_ge

theorem segLen_eq : (prm s₀).segmentLen = mcostN s₀ / (4 * lanesN s₀) :=
  Proof.Argon2.segmentLen_eq _ hp.lanes_pos

theorem laneLen_eq : (prm s₀).laneLen = 4 * (prm s₀).segmentLen :=
  Proof.Argon2.laneLen_segments _ hp.lanes_pos

theorem blocks_eq : blocksN s₀ = lanesN s₀ * (prm s₀).laneLen := by
  rw [hp.blocks]; exact Proof.Argon2.blocks_lanes _ hp.lanes_pos

theorem blocks_le : blocksN s₀ ≤ mcostN s₀ := by
  rw [hp.blocks]; exact Proof.Argon2.blocks_le_memory _

end DPre

theorem mcost_lt (s₀ : State) : mcostN s₀ < 2 ^ 32 := (arg32 s₀ 6).isLt

end VG.Proof.Argon2.PPC64LE.Derive

end

end

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
  rw [stackArgAddr, sp_add, show 384 + (32 + 8 * (8 + i)) = 416 + 8 * (8 + i) by omega_using []]

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
  · exact stk_disj hp (by omega_using [h₁]) _ (by simp)
  · exact stk_disj hp (by omega_using [h₁]) _ (by simp)
  · exact stk_disj hp (by omega_using [h₁]) _ (by simp)
  · exact Offset.disjoint _ (by omega_using [h₁]) (by omega_using [h₁]) (by omega_using [])
  · exact Offset.disjoint _ (by omega_using [h₁]) (by omega_using [h₁]) (by omega_using [])
  · have e : B s₀ = B s₀ + BitVec.ofNat 64 0 := (BitVec.add_zero _).symm
    show Region.Disjoint _ ⟨B s₀, 48⟩
    rw [e]
    exact Offset.disjoint _ (by omega_using [h₁]) (by omega_using [h₁]) (by omega_using [])

omit hp in
theorem argR_eq : argR s₀ = ⟨at' s₀ 480, 80⟩ := by
  show (⟨stackArgAddr s₀ 0, 80⟩ : Region) = _
  rw [stackArg_eq]

/-- The arguments in the Parameter Save Area are outside the body's regions. -/
theorem arg_disj {d n : Nat} (h₁ : 480 ≤ d) (h₂ : d + n ≤ 560) :
    ∀ r ∈ bodyW s₀, Region.Disjoint ⟨at' s₀ d, n⟩ r := by
  have sub : Region.Sub ⟨at' s₀ d, n⟩ (argR s₀) := by
    rw [argR_eq]; exact Offset.sub _ h₁ (by omega_using [h₂])
  intro r hr
  simp only [bodyW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hp.ro_w _ (by simp) _ (by simp)).sub_left sub
  · exact (hp.ro_w _ (by simp) _ (by simp)).sub_left sub
  · exact (hp.ro_w _ (by simp) _ (by simp)).sub_left sub
  · exact Offset.disjoint _ (by omega_using [h₁]) (by omega_using [h₂]) (by omega_using [])
  · exact Offset.disjoint _ (by omega_using [h₁]) (by omega_using [h₂]) (by omega_using [])
  · have e : B s₀ = B s₀ + BitVec.ofNat 64 0 := (BitVec.add_zero _).symm
    show Region.Disjoint _ ⟨B s₀, 48⟩
    rw [e]
    exact Offset.disjoint _ (by omega_using [h₁]) (by omega_using [h₂]) (by omega_using [])

theorem Inv.slot {s : State} (h : Inv s₀ s) {d : Nat} (h₁ : 152 ≤ d) (h₂ : d + 8 ≤ 256) :
    s.mem.readW (at' s₀ d) 64 = (setupMem s₀).readW (at' s₀ d) 64 :=
  h.frame.readW (Region.contains_self _ _) (frame_disj hp (.inr ⟨h₁, h₂⟩)) (by decide)

/-- The doubleword `d` bytes above the frame's stack pointer, among the setup's
slots. -/
theorem Inv.saved {s : State} (h : Inv s₀ s) {r : Reg} {d : Nat}
    (hr : (r, d) ∈ savedSlots ++ argSlots) : lw s₀ s d = s₀.gpr r := by
  have := slots_in _ hr
  rw [lw, E_add, h.slot hp (by simp only at this; omega_using [this]) (by simp only at this; omega_using [this]), ← E_add,
    setupMem_slot s₀ hr]

theorem Inv.lr {s : State} (h : Inv s₀ s) : lw s₀ s 104 = s₀.lr := by
  rw [lw, E_add, h.slot hp (by decide) (by decide), ← E_add, setupMem_lr]

/-- The arguments, from the frame or the Parameter Save Area. -/
theorem Inv.arg {s : State} (h : Inv s₀ s) {i : Nat} (hi : i < 18) :
    s.mem.readW (E s₀ + BitVec.ofNat 64 (argOff i)) 64 = arg s₀ i := by
  by_cases h8 : i < 8
  · rcases (by omega_using [h8] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h.saved hp (r := .r3) (d := 144) (by decide)
    · exact h.saved hp (r := .r4) (d := 152) (by decide)
    · exact h.saved hp (r := .r5) (d := 160) (by decide)
    · exact h.saved hp (r := .r6) (d := 168) (by decide)
    · exact h.saved hp (r := .r7) (d := 176) (by decide)
    · exact h.saved hp (r := .r8) (d := 184) (by decide)
    · exact h.saved hp (r := .r9) (d := 192) (by decide)
    · exact h.saved hp (r := .r10) (d := 200) (by decide)
  · obtain ⟨k, rfl⟩ : ∃ k, i = 8 + k := ⟨i - 8, by omega_using [h8]⟩
    have ea : E s₀ + BitVec.ofNat 64 (argOff (8 + k)) = at' s₀ (416 + 8 * (8 + k)) := by
      have e : argOff (8 + k) = 368 + 8 * (8 + k) := by
        simp only [argOff, locals]; rw [ite_eq_right_iff.mpr (by omega_using [])]
      rw [E_add, e, show 48 + (368 + 8 * (8 + k)) = 416 + 8 * (8 + k) by omega_using []]
    rw [ea, h.frame.readW (Region.contains_self _ _) (arg_disj hp (by omega_using []) (by omega_using [hi])) (by decide),
      (setupMem_frame s₀).readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega_using []) (by omega_using [hi]) (by omega_using [])) (by decide),
      ← stackArg_eq, show 8 + k = k + 8 by omega_using []]
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

end

end

/-!
# Argon2 on PPC64LE: the derivation's locals

`lw s₀ s d`: the doubleword at `r30 + d` in the body. A store to the frame's
variables keeps the invariant and every other doubleword (`wp_stloc`);
writes to the memory matrix, `scratch`, the output or the calls' frames keep
all of them (`lw_keep`). `wp_lda` and `wp_ldw` load an argument, of 64 or 32
bits.
-/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.Derive

open VG VG.PPC64LE
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_ld wp_std wp_lwz wp_mov)
open VG.Impl.Argon2.PPC64LE.Derive (ld st lda ldw argOff locals savedSlots argSlots)

/-- An offset of a doubleword in the frame's local variable space. -/
abbrev LocOff (d : Nat) : Prop := 32 ≤ d ∧ d + 8 ≤ 336 ∧ d % 8 = 0

/-- An offset of a doubleword the body may write: H′'s input or the loop
variables. -/
abbrev VarOff (d : Nat) : Prop := (32 ≤ d ∧ d + 8 ≤ 104 ∨ 208 ≤ d ∧ d + 8 ≤ 336) ∧ d % 8 = 0

section
variable {s₀ : State}

theorem loc_in {s : State} (h : Inv s₀ s) {d n : Nat} (h₁ : 32 ≤ d) (h₂ : d + n ≤ 336) :
    InRegions s.wr (E s₀ + BitVec.ofNat 64 d) n := by
  rw [h.wr, entry_wr, E_add]
  exact ⟨_, List.mem_cons_self .., Offset.contains _ (by omega_using [h₁]) (by omega_using [h₂]) (by omega_using [])⟩

theorem loc_in' {s : State} (h : Inv s₀ s) {d n : Nat} (h₁ : 32 ≤ d) (h₂ : d + n ≤ 336) :
    InRegions (s.rd ++ s.wr) (E s₀ + BitVec.ofNat 64 d) n :=
  let ⟨r, hr, hc⟩ := loc_in h h₁ h₂
  ⟨r, List.mem_append_right _ hr, hc⟩

/-- A store's doubleword is within the body's regions. -/
theorem var_in {d : Nat} (hd : VarOff d) :
    ∃ r ∈ bodyW s₀, r.Contains (E s₀ + BitVec.ofNat 64 d) 8 := by
  rw [E_add]
  rcases hd.1 with h | h
  · exact ⟨inR s₀, by simp, Offset.contains _ (by omega_using [h]) (by omega_using [h]) (by omega_using [])⟩
  · exact ⟨varR s₀, by simp, Offset.contains _ (by omega_using [h]) (by omega_using [h]) (by omega_using [])⟩

/-- `std r, d(r30)` -/
theorem wp_stloc {s : State} (h : Inv s₀ s) {d : Nat} (hd : VarOff d) {r : Reg} {is : List Instr}
    {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → lw s₀ t d = s.gpr r →
      (∀ e, e + 8 ≤ 336 → d + 8 ≤ e ∨ e + 8 ≤ d → lw s₀ t e = lw s₀ s e) → t.gpr = s.gpr →
      t.mem = s.mem.writeW (E s₀ + BitVec.ofNat 64 d) (s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (st d r :: is)) s Q := by
  obtain ⟨R, hR, hc⟩ := var_in hd
  refine wp_std (a := E s₀ + BitVec.ofNat 64 d) ⟨by omega, by omega⟩ (by rw [h.r30])
    (loc_in h (by omega) (by omega)) fun t u => k t (h.mupd u ((Frame.refl _ _).writeW hR _ hc))
    (by rw [lw, u.mem, Mem.readW_writeW_self64]) (fun e he he' => ?_) u.gpr u.mem
  rw [lw, lw, u.mem, Mem.readW_writeW_sep (by
    rw [E_add, E_add]
    exact Offset.sep _ (by omega_using [he']) (by omega_using [he]) (by omega)) (by decide)]

/-- `ld r, d(r30)` -/
theorem wp_ldloc {s : State} (h : Inv s₀ s) {d : Nat} (hd : LocOff d) {r : Reg} {is : List Instr}
    {Q : State → Prop} (k : ∀ t, Upd s t r (lw s₀ s d) → WP isa (.block is) t Q) :
    WP isa (.block (ld r d :: is)) s Q :=
  wp_ld ⟨by omega, by omega⟩ (by rw [h.r30]) (loc_in' h hd.1 (by omega)) k

theorem argOff_lt {i : Nat} (hi : i < 18) : argOff i < 2 ^ 15 ∧ argOff i % 4 = 0 := by
  revert hi; revert i; decide

variable (hp : DPre s₀)
include hp

/-- Argument `i` is readable. -/
theorem Inv.arg_in {s : State} (h : Inv s₀ s) {i : Nat} (hi : i < 18) {n : Nat} (hn : n ≤ 8) :
    InRegions (s.rd ++ s.wr) (E s₀ + BitVec.ofNat 64 (argOff i)) n := by
  by_cases h8 : i < 8
  · refine loc_in' h ?_ ?_ <;> simp only [argOff, locals, h8, ite_true] <;> first | omega_arith | skip
  · have e : argOff i = 368 + 8 * i := by
      simp only [argOff, locals]; rw [ite_eq_right_iff.mpr (by omega_using [h8])]
    rw [h.rd, e, E_add, hp.rd]
    refine ⟨argR s₀, List.mem_append_left _ (by simp), ?_⟩
    rw [argR_eq]
    exact Offset.contains _ (by omega_using [h8]) (by omega_using [hi, hn]) (by omega_using [])

/-- `ld r, (argOff i)(r30)`: a 64-bit argument. -/
theorem wp_lda {s : State} (h : Inv s₀ s) {i : Nat} (hi : i < 18) {r : Reg} {is : List Instr}
    {Q : State → Prop} (k : ∀ t, Upd s t r (arg s₀ i) → WP isa (.block is) t Q) :
    WP isa (.block (lda r i :: is)) s Q :=
  wp_ld (argOff_lt hi) (by rw [h.r30]) (h.arg_in hp hi (by decide)) fun t u =>
    k t (by rw [h.arg hp hi] at u; exact u)

/-- `lwz r, (argOff i)(r30)`: a 32-bit argument, zero-extended. -/
theorem wp_ldw {s : State} (h : Inv s₀ s) {i : Nat} (hi : i < 18) {r : Reg} {is : List Instr}
    {Q : State → Prop} (k : ∀ t, Upd s t r ((arg32 s₀ i).setWidth 64) → WP isa (.block is) t Q) :
    WP isa (.block (ldw r i :: is)) s Q :=
  wp_lwz (argOff_lt hi).1 (by rw [h.r30]) (h.arg_in hp hi (by decide)) fun t u =>
    k t (by rw [h.arg32 hp hi] at u; exact u)

/-- The frame's doublewords are outside the buffers and the calls' frames. -/
theorem loc_disj {d : Nat} (h₁ : 32 ≤ d) (h₂ : d + 8 ≤ 336) :
    ∀ r ∈ [memR s₀, scrR s₀, outR s₀, callR s₀],
      Region.Disjoint ⟨E s₀ + BitVec.ofNat 64 d, 8⟩ r := by
  rw [E_add]
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact stk_disj hp (by omega) _ (by simp)
  · exact stk_disj hp (by omega_using [h₂]) _ (by simp)
  · exact stk_disj hp (by omega_using [h₂]) _ (by simp)
  · have e : B s₀ = B s₀ + BitVec.ofNat 64 0 := (BitVec.add_zero _).symm
    show Region.Disjoint _ ⟨B s₀, 48⟩
    rw [e]
    exact Offset.disjoint _ (by omega_using []) (by omega_using [h₂]) (by omega_using [])

/-- The frame is kept by writes outside it. -/
theorem lw_keep {s t : State} {rs : List Region} (f : Frame rs s.mem t.mem)
    (hs : ∀ r ∈ rs, ∃ r' ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Sub r r') {d : Nat}
    (h₁ : 32 ≤ d) (h₂ : d + 8 ≤ 336) : lw s₀ t d = lw s₀ s d :=
  (f.sub hs).readW (Region.contains_self _ _) (loc_disj hp h₁ h₂) (by decide)

end

theorem saveMem_congr {m : Mem} {b : Addr} {g g' : Reg → BitVec 64} :
    ∀ {l : List (Reg × Nat)}, (∀ p ∈ l, g p.1 = g' p.1) →
      Spill.saveMem m b g l = Spill.saveMem m b g' l
  | [], _ => rfl
  | (r, d) :: l, h => by
    simp only [Spill.saveMem]
    rw [h (r, d) List.mem_cons_self]
    exact saveMem_congr fun p hp => h p (List.mem_cons_of_mem _ hp)

/-- `scratch`, from the Parameter Save Area, after the setup. -/
theorem setupMem_arg (s₀ : State) {i : Nat} (h₁ : 8 ≤ i) (h₂ : i < 18) :
    (setupMem s₀).readW (E s₀ + BitVec.ofNat 64 (argOff i)) 64 = arg s₀ i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = 8 + k := ⟨i - 8, by omega_using [h₁]⟩
  have e : argOff (8 + k) = 368 + 8 * (8 + k) := by
    simp only [argOff, locals]; rw [ite_eq_right_iff.mpr (by omega_using [])]
  rw [E_add, e, show 48 + (368 + 8 * (8 + k)) = 416 + 8 * (8 + k) by omega_using [],
    (setupMem_frame s₀).readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega_using []) (by omega_using [h₂]) (by omega_using [])) (by decide),
    ← stackArg_eq, show 8 + k = k + 8 by omega_using []]
  rfl

/-- The body's first instructions: the return address, the caller's
registers and the register arguments to the frame, `r30` to the frame and
`r31` to `scratch`. -/
theorem setup_ok {s₀ : State} (hp : DPre s₀) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → t.mem = setupMem s₀ → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.PPC64LE.Derive.setup ++ is)) (entry s₀) Q := by
  have h0 : E s₀ + BitVec.ofNat 64 0 = E s₀ := BitVec.add_zero _
  have hl : ∀ p ∈ savedSlots ++ argSlots, p.1 ≠ .r0 ∧ p.1 ≠ .r12 := by decide
  simp only [Impl.Argon2.PPC64LE.Derive.setup, List.cons_append, List.append_assoc]
  refine MdStream.PPC64LE.WP.cons (s' := (entry s₀).write .r12 (E s₀))
    (by simp only [exec, show (0 : Nat) < 2 ^ 15 by decide, ite_true, entry_sp, h0]) ?_
  have u₁ := Upd.write (entry s₀) .r12 (E s₀)
  refine MdStream.PPC64LE.WP.cons exec_mflr ?_
  have u₂ := Upd.write ((entry s₀).write .r12 (E s₀)) .r0 ((entry s₀).write .r12 (E s₀)).lr
  have lr : ((entry s₀).write .r12 (E s₀)).lr = s₀.lr := rfl
  generalize ((entry s₀).write .r12 (E s₀)).write .r0 ((entry s₀).write .r12 (E s₀)).lr = c at u₂
  rw [lr] at u₂
  have c12 : c.gpr .r12 = E s₀ := by rw [u₂.other _ (by decide), u₁.gpr]
  have cg : ∀ r, r ≠ .r0 → r ≠ .r12 → c.gpr r = s₀.gpr r := fun r h₁ h₂ => by
    rw [u₂.other _ h₁, u₁.other _ h₂]; rfl
  have cwr : c.wr = (entry s₀).wr := by rw [u₂.wr, u₁.wr]
  have inE : ∀ d n, 32 ≤ d → d + n ≤ 336 → InRegions c.wr (E s₀ + BitVec.ofNat 64 d) n :=
    fun d n h₁ h₂ => by
      rw [cwr, entry_wr, E_add]
      exact ⟨_, List.mem_cons_self .., Offset.contains _ (by omega_using [h₁]) (by omega_using [h₂]) (by omega_using [])⟩
  refine wp_std (a := E s₀ + BitVec.ofNat 64 104) (by decide) (by rw [c12]; rfl)
    (inE 104 8 (by decide) (by decide)) fun d ud => ?_
  rw [show (savedSlots ++ argSlots).map (fun (r, d) => Instr.store .d r .r12 d) =
    Spill.saveCode .r12 (savedSlots ++ argSlots) from rfl]
  refine Spill.save_ok (by decide) (fun p hp => slots_fits.1 p hp) (fun p hp => by
    rw [ud.wr, ud.gpr, c12]
    have := slots_in p hp
    exact inE _ _ (by omega_using [this]) (by omega_using [this])) ?_
  refine wp_mov fun f uf => ?_
  have f30 : f.gpr .r30 = E s₀ := by rw [uf.gpr]; show d.gpr .r12 = _; rw [ud.gpr, c12]
  have fmem : f.mem = setupMem s₀ := by
    rw [uf.mem]
    show Spill.saveMem d.mem (d.gpr .r12) d.gpr _ = _
    rw [ud.mem, ud.gpr, c12, u₂.mem, u₁.mem, u₂.gpr]
    exact saveMem_congr fun p hp => by
      rw [cg _ (hl p hp).1 (hl p hp).2]
  have frd : f.rd = s₀.rd := by
    rw [uf.rd]; show d.rd = _; rw [ud.rd, u₂.rd, u₁.rd]; rfl
  have fin : InRegions (f.rd ++ f.wr) (E s₀ + BitVec.ofNat 64 (argOff 15)) 8 := by
    refine ⟨argR s₀, List.mem_append_left _ (by rw [frd, hp.rd]; simp), ?_⟩
    rw [argR_eq, show argOff 15 = 488 by decide, E_add]
    exact Offset.contains _ (by decide) (by decide) (by decide)
  refine wp_ld (a := E s₀ + BitVec.ofNat 64 (argOff 15)) (by decide) (by rw [f30]; rfl) fin
    fun t ut => ?_
  rw [fmem, setupMem_arg s₀ (by decide) (by decide)] at ut
  refine k t ⟨?_, ?_, ut.gpr, fun r hr => ?_, ?_, ?_, ?_⟩ (by rw [ut.mem, fmem])
  · rw [ut.sp, uf.sp]; show d.sp = _; rw [ud.sp, u₂.sp, u₁.sp]; rfl
  · rw [ut.other _ (by decide), f30]
  · have h0 : r ≠ .r0 := fun e => by subst e; exact absurd hr (by decide)
    have h12 : r ≠ .r12 := fun e => by subst e; exact absurd hr (by decide)
    have h30 : r ≠ .r30 := fun e => by subst e; exact absurd hr (by decide)
    have h31 : r ≠ .r31 := fun e => by subst e; exact absurd hr (by decide)
    rw [ut.other _ h31, uf.other _ h30]; show d.gpr r = _; rw [ud.gpr, cg r h0 h12]
  · rw [ut.rd, frd]
  · rw [ut.wr, uf.wr]; show d.wr = _; rw [ud.wr, cwr]
  · rw [ut.mem, fmem]; exact Frame.refl _ _

end VG.Proof.Argon2.PPC64LE.Derive

end

end

/-! ### `Argon2.PPC64LE.Derive.Divide`, which this module and modules that import it used -/

section

/-! ### `Argon2.PPC64LE.Derive.Ops`, which this module and modules that import it used -/

section

/-! # Argon2 on PPC64LE: the derivation's arithmetic and logical instructions -/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.Derive

open VG VG.PPC64LE
open VG.Proof.MdStream.PPC64LE (Upd WP.cons)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mul {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n * s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.mul d n m :: is)) s Q :=
  WP.cons exec_mul (k _ (Upd.write _ _ _))

theorem wp_xor {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .xor d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

theorem wp_or {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ||| s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .or d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

theorem wp_lsrw {d n : Reg} {sh : Nat} (h : sh < 32)
    (k : ∀ s', Upd s s' d (((s.gpr n).setWidth 32 >>> sh).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsr .w d n sh :: is)) s Q :=
  WP.cons (exec_lsr_w h) (k _ (Upd.write _ _ _))

end

/-- `s'` is `s` with (at most) the registers `ds` changed. -/
structure Only (ds : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ ds → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Only.of_upd {s s' : State} {d : Reg} {v : BitVec 64} (u : Upd s s' d v) : Only [d] s s' :=
  ⟨fun r h => u.other r (by simpa using h), u.mem, u.rd, u.wr, u.sp⟩

theorem Only.trans {ds es : List Reg} {s₁ s₂ s₃ : State} (h₁ : Only ds s₁ s₂) (h₂ : Only es s₂ s₃) :
    Only (ds ++ es) s₁ s₃ :=
  ⟨fun r h => by
    simp only [List.mem_append, not_or] at h
    rw [h₂.gpr r h.2, h₁.gpr r h.1], h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    h₂.sp.trans h₁.sp⟩

theorem Only.mono {ds es : List Reg} {s s' : State} (h : Only ds s s') (he : ∀ r ∈ ds, r ∈ es) :
    Only es s s' :=
  ⟨fun r hr => h.gpr r fun hd => hr (he r hd), h.mem, h.rd, h.wr, h.sp⟩

end VG.Proof.Argon2.PPC64LE.Derive

end

end

/-!
# Fixed-time division on PPC64LE

`code_ok`: `Impl.Argon2.PPC64LE.Divide.code` leaves `n / D` in `r6` and
`n mod D` in `r7`, for the numerator `n` in the low 32 bits of `r4` and the
divisor `D` in `r5`, `0 < D < 2³¹`. After `k` bits (`bits_ok`) the low 32
bits of `r4` hold the `32 - k` bits of `n` not yet consumed, shifted up by
`k`, and `r6`, `r7` the quotient and remainder of the `k` consumed ones: each
bit is one step of binary long division (`Proof.Argon2.divide_step`).
-/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.Derive.Divide

open VG VG.PPC64LE
open VG.Impl.Argon2.PPC64LE.Divide (bit bits code)
open VG.Proof.MdStream.PPC64LE (Upd wp_add wp_sub wp_lsr wp_lsl wp_li)
open VG.Proof.Argon2.PPC64LE.Derive (wp_mul wp_lsrw)

/-- Only `r4`, `r6`, `r7` and `r8` change. -/
structure Keep (s t : State) : Prop where
  other : ∀ r, r ≠ .r4 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem Keep.refl (s : State) : Keep s s := ⟨fun _ _ _ _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem Keep.trans {s t u : State} (h : Keep s t) (h' : Keep t u) : Keep s u :=
  ⟨fun r a b c d => (h'.other r a b c d).trans (h.other r a b c d), h'.mem.trans h.mem,
    h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp⟩

theorem Keep.of_upd {s t : State} {d : Reg} {v : BitVec 64} (u : Upd s t d v)
    (hd : d = .r4 ∨ d = .r6 ∨ d = .r7 ∨ d = .r8) : Keep s t :=
  ⟨fun r a b c e => u.other r (by
    rcases hd with rfl | rfl | rfl | rfl <;> with_reducible assumption), u.mem, u.rd, u.wr, u.sp⟩

/-- The numbers after `k` bits of `n`. -/
def Stage (n D k : Nat) (s : State) : Prop :=
  ((s.gpr .r4).setWidth 32).toNat = (n % 2 ^ (32 - k)) * 2 ^ k ∧
    (s.gpr .r6).toNat = n / 2 ^ (32 - k) / D ∧
    (s.gpr .r7).toNat = n / 2 ^ (32 - k) % D

theorem toNat_lsl1 (x : BitVec 64) : (x <<< 1).toNat = x.toNat * 2 % 2 ^ 64 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one]

theorem toNat_lsr (x : BitVec 64) (k : Nat) : (x >>> k).toNat = x.toNat / 2 ^ k := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- One bit. -/
theorem bit_ok {s : State} {D : Nat} (hD : 0 < D) (hD2 : D < 2 ^ 31)
    (hb : (s.gpr .r5).toNat = D) (h9 : (s.gpr .r9).toNat = 1) {n k : Nat} (hn : n < 2 ^ 32)
    (hk : k < 32) (h : Stage n D k s) {is : List Instr} {Q : State → Prop}
    (hq : ∀ t, Stage n D (k + 1) t → Keep s t → WP isa (.block is) t Q) :
    WP isa (.block (bit ++ is)) s Q := by
  obtain ⟨hc, hq6, ha⟩ := h
  obtain hm : k + (31 - k) = 31 := by omega_arith
  obtain pos : ∀ j, 0 < 2 ^ j := fun j => Nat.two_pow_pos j
  obtain e32 : 32 - k = 31 - k + 1 := by omega_arith
  obtain p31 : 2 ^ (31 - k) * 2 ^ k = 2 ^ 31 := by rw [← Nat.pow_add, Nat.add_comm, hm]
  obtain hRlt : n % 2 ^ (32 - k) < 2 ^ (32 - k) := Nat.mod_lt _ (pos _)
  obtain hRb := (Nat.div_add_mod' (n % 2 ^ (32 - k)) (2 ^ (31 - k))).symm
  obtain hb1 : n % 2 ^ (32 - k) / 2 ^ (31 - k) ≤ 1 := by
    obtain h' : 2 ^ (32 - k) = 2 ^ (31 - k) * 2 := by rw [e32, Nat.pow_succ]
    exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega_using [h', hRlt]))
  obtain hR'lt : n % 2 ^ (32 - k) % 2 ^ (31 - k) < 2 ^ (31 - k) := Nat.mod_lt _ (pos _)
  obtain hqlt : n / 2 ^ (32 - k) / D < 2 ^ 32 := by
    refine Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn)
  obtain hrlt : n / 2 ^ (32 - k) % D < D := Nat.mod_lt _ hD
  generalize hN : n / 2 ^ (32 - k) = N at hq6 ha hqlt hrlt
  generalize hRR : n % 2 ^ (32 - k) = R at hc hRlt hRb hb1 hR'lt
  generalize hbb : R / 2 ^ (31 - k) = b at hRb hb1
  generalize hR' : R % 2 ^ (31 - k) = R' at hRb hR'lt
  obtain N' : n / 2 ^ (32 - (k + 1)) = 2 * N + b := by
    rw [← hN, ← hbb, ← hRR, show 32 - (k + 1) = 31 - k by omega_arith, e32, Nat.pow_succ,
      Nat.mod_mul_right_div_self, ← Nat.div_div_eq_div_mul]
    have := Nat.div_add_mod (n / 2 ^ (31 - k)) 2
    omega_using [this]
  obtain R'' : n % 2 ^ (32 - (k + 1)) = R' := by
    rw [← hR', ← hRR, show 32 - (k + 1) = 31 - k by omega_arith, e32, Nat.pow_succ, Nat.mod_mul_right_mod]
  obtain step := Proof.Argon2.divide_step (n := N) (d := D) (q := N / D) (r := N % D)
    (bit := b) (Nat.div_add_mod' N _).symm hrlt hb1
  dsimp only at step
  obtain ⟨st₁, st₂⟩ := step
  obtain res := Proof.Argon2.divide_result hD st₁ st₂
  obtain pk : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
  obtain hPb : R' * 2 ^ k + 2 ^ k ≤ 2 ^ 31 := by
    have := Nat.mul_le_mul_right (2 ^ k) (show R' + 1 ≤ 2 ^ (31 - k) by omega_arith)
    rw [Nat.add_mul, Nat.one_mul, p31] at this
    exact this
  obtain hL : ((s.gpr .r4).setWidth 32).toNat = b * 2 ^ 31 + R' * 2 ^ k := by
    rw [hc, hRb, Nat.add_mul, Nat.mul_assoc, p31]
  obtain hP : R' * 2 ^ (k + 1) = 2 * (R' * 2 ^ k) := by rw [pk, Nat.mul_left_comm]
  generalize hPP : R' * 2 ^ k = P at hP hPb hL
  generalize hKK : 2 ^ k = K at hPb pk
  obtain hK : 0 < K := hKK ▸ pos k
  simp only [bit, List.cons_append, List.nil_append]
  refine wp_lsrw (by decide) fun s₁ u₁ => ?_
  obtain v₁ : (s₁.gpr .r8).toNat = b := by
    rw [u₁.gpr, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hL,
      Nat.mod_eq_of_lt (by
        rcases (by omega_arith : b = 0 ∨ b = 1) with rfl | rfl <;>
          exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega_arith))]
    rcases (by omega_arith : b = 0 ∨ b = 1) with rfl | rfl <;> omega_arith
  refine wp_lsl (by decide) fun s₂ u₂ => ?_
  obtain v₂ : ((s₂.gpr .r4).setWidth 32).toNat = 2 * P := by
    rw [u₂.gpr, u₁.other _ (by decide), BitVec.toNat_setWidth, toNat_lsl1]
    obtain hx : (s.gpr .r4).toNat % 2 ^ 32 = b * 2 ^ 31 + P := by
      rw [← BitVec.toNat_setWidth, hL]
    rw [Nat.mod_mod_of_dvd _ (by decide), Nat.mul_mod, hx]
    rcases (by omega_arith : b = 0 ∨ b = 1) with rfl | rfl <;> omega_arith
  refine wp_lsl (by decide) fun s₃ u₃ => ?_
  refine wp_add fun s₄ u₄ => ?_
  obtain v₄ : (s₄.gpr .r7).toNat = 2 * (N % D) + b := by
    rw [u₄.gpr, u₃.gpr, u₃.other _ (by decide), BitVec.toNat_add, toNat_lsl1,
      u₂.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), ha, v₁]
    omega_arith
  refine wp_sub fun s₅ u₅ => ?_
  obtain d₄ : (s₄.gpr .r5).toNat = D := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hb]
  refine wp_lsr (by decide) fun s₆ u₆ => ?_
  generalize ht : (if 2 * (N % D) + b < D then 0 else 1) = t
  obtain ht1 : t ≤ 1 := by rw [← ht]; split <;> omega_arith
  obtain v₆ : (s₆.gpr .r8).toNat = 1 - t := by
    rw [u₆.gpr, toNat_lsr, u₅.gpr, BitVec.toNat_sub, v₄, d₄, ← ht]
    split
    · rw [show 2 ^ 64 - D + (2 * (N % D) + b) = 2 ^ 64 - (D - (2 * (N % D) + b)) by omega_arith,
        Nat.mod_eq_of_lt (by omega_arith)]
      omega_arith
    · rw [show 2 ^ 64 - D + (2 * (N % D) + b) = (2 * (N % D) + b - D) + 2 ^ 64 by omega_arith,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_arith)]
      omega_arith
  refine wp_sub fun s₇ u₇ => ?_
  obtain v₇ : (s₇.gpr .r8).toNat = t := by
    obtain e9 : (s₆.gpr .r9).toNat = 1 := by
      rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h9]
    rw [u₇.gpr, BitVec.toNat_sub, v₆, e9]
    rcases (by omega_arith : t = 0 ∨ t = 1) with rfl | rfl <;> decide
  refine wp_lsl (by decide) fun s₈ u₈ => ?_
  refine wp_add fun s₉ u₉ => ?_
  refine wp_mul fun s₁₀ u₁₀ => ?_
  refine wp_sub fun s₁₁ u₁₁ => hq s₁₁ ⟨?_, ?_, ?_⟩ ?_
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
      u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), v₂, R'', hP]
  · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr, BitVec.toNat_add,
      u₈.gpr, u₈.other _ (by decide), toNat_lsl1, v₇, u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hq6, N', ← res.1, ← ht]
    omega_arith
  · have d₉ : (s₉.gpr .r5).toNat = D := by
      rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.other _ (by decide), u₅.other _ (by decide), d₄]
    obtain r₉ : (s₉.gpr .r7).toNat = 2 * (N % D) + b := by
      rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.other _ (by decide), u₅.other _ (by decide), v₄]
    obtain e₉ : (s₉.gpr .r8).toNat = t := by rw [u₉.other _ (by decide), u₈.other _ (by decide), v₇]
    rw [u₁₁.gpr, u₁₀.other _ (by decide), u₁₀.gpr, BitVec.toNat_sub, BitVec.toNat_mul, e₉, d₉, r₉,
      N', ← res.2, ← ht]
    obtain sub : ∀ x v : Nat, x ≤ v → v < 2 ^ 64 → (2 ^ 64 - x % 2 ^ 64 + v) % 2 ^ 64 = v - x :=
      fun x v h₁ h₂ => by
        rw [Nat.mod_eq_of_lt (a := x) (by omega_arith), show 2 ^ 64 - x + v = (v - x) + 2 ^ 64 by omega_arith,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_arith)]
    split
    · rw [Nat.zero_mul, sub 0 _ (by omega_arith) (by omega_arith)]; rfl
    · rw [Nat.one_mul, sub D _ (by omega_arith) (by omega_arith)]
  · exact (((((((((((Keep.of_upd u₁ (by simp)).trans (Keep.of_upd u₂ (by simp))).trans (Keep.of_upd u₃ (by simp))).trans (Keep.of_upd u₄ (by simp))).trans (Keep.of_upd u₅ (by simp))).trans (Keep.of_upd u₆ (by simp))).trans (Keep.of_upd u₇ (by simp))).trans (Keep.of_upd u₈ (by simp))).trans (Keep.of_upd u₉ (by simp))).trans (Keep.of_upd u₁₀ (by simp))).trans (Keep.of_upd u₁₁ (by simp)))

theorem bits_ok {D : Nat} (hD : 0 < D) (hD2 : D < 2 ^ 31) {n : Nat}
    (hn : n < 2 ^ 32) {is : List Instr} {Q : State → Prop} :
    ∀ k ≤ 32, ∀ s : State, (s.gpr .r5).toNat = D → (s.gpr .r9).toNat = 1 → Stage n D 0 s →
      (∀ t, Stage n D k t → Keep s t → WP isa (.block is) t Q) →
      WP isa (.block (bits k ++ is)) s Q
  | 0, _, s, _, _, h, hq => hq s h (Keep.refl s)
  | k + 1, hk, s, hb, h9, h, hq => by
    simp only [bits, List.append_assoc]
    refine bits_ok hD hD2 hn k (by omega_arith) s hb h9 h fun t ht kt => ?_
    refine bit_ok hD hD2 (by rw [kt.other _ (by decide) (by decide) (by decide) (by decide), hb])
      (by rw [kt.other _ (by decide) (by decide) (by decide) (by decide), h9]) hn (by omega_arith) ht
      fun u hu ku => hq u hu (kt.trans ku)

/-- Only `r4` and `r6`–`r9` change. -/
structure KeepD (s t : State) : Prop where
  other : ∀ r, r ≠ .r4 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → r ≠ .r9 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

/-- The division: `r6 := n / D`, `r7 := n mod D`, for `n` the low 32 bits of
`r4`. -/
theorem code_ok {s : State} {D : Nat} (hD : 0 < D) (hD2 : D < 2 ^ 31)
    (hb : (s.gpr .r5).toNat = D) {is : List Instr} {Q : State → Prop}
    (hq : ∀ t, (t.gpr .r6).toNat = ((s.gpr .r4).setWidth 32).toNat / D →
      (t.gpr .r7).toNat = ((s.gpr .r4).setWidth 32).toNat % D → KeepD s t →
      WP isa (.block is) t Q) :
    WP isa (.block (code ++ is)) s Q := by
  obtain hn := ((s.gpr .r4).setWidth 32).isLt
  simp only [code, List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s₁ u₁ => wp_li (by decide) fun s₂ u₂ => wp_li (by decide) fun s₃ u₃ => ?_
  obtain e4 : s₃.gpr .r4 = s.gpr .r4 := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  refine bits_ok hD hD2 hn 32 (Nat.le_refl _) s₃
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hb])
    (by rw [u₃.gpr]; rfl) ⟨?_, ?_, ?_⟩ fun t ⟨hc, h6, h7⟩ kt => ?_
  · rw [e4, Nat.mod_eq_of_lt hn]; simp
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, show 32 - 0 = 32 from rfl,
      Nat.div_eq_of_lt hn, Nat.zero_div]; rfl
  · rw [u₃.other _ (by decide), u₂.gpr, show 32 - 0 = 32 from rfl, Nat.div_eq_of_lt hn,
      Nat.zero_mod]; rfl
  · refine hq t (by rw [h6]; simp) (by rw [h7]; simp) ⟨fun r a b c d e => ?_, ?_, ?_, ?_, ?_⟩
    · rw [kt.other r a b c d, u₃.other _ e, u₂.other _ c, u₁.other _ b]
    · rw [kt.mem, u₃.mem, u₂.mem, u₁.mem]
    · rw [kt.rd, u₃.rd, u₂.rd, u₁.rd]
    · rw [kt.wr, u₃.wr, u₂.wr, u₁.wr]
    · rw [kt.sp, u₃.sp, u₂.sp, u₁.sp]

end VG.Proof.Argon2.PPC64LE.Derive.Divide

end

end

/-!
# Argon2 on PPC64LE: the parameters

`parameters_ok`: the body's first computation stores the segment length (by
the fixed-time division of the memory cost by `4 · lanes`), the lane length
and its size in bytes in the frame (`Prm`).
-/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.Derive

open VG VG.PPC64LE
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_lsl)
open VG.Impl.Argon2.PPC64LE.Derive (parameters segLenOff laneLenOff strideOff)

/-- The parameters in the frame. -/
structure Prm (s₀ s : State) : Prop where
  segLen : lw s₀ s segLenOff = BitVec.ofNat 64 (prm s₀).segmentLen
  laneLen : lw s₀ s laneLenOff = BitVec.ofNat 64 (prm s₀).laneLen
  stride : lw s₀ s strideOff = BitVec.ofNat 64 ((prm s₀).laneLen * 1024)

theorem lw_mem {s₀ s t : State} (h : t.mem = s.mem) (d : Nat) : lw s₀ t d = lw s₀ s d := by
  simp only [lw, h]

theorem Inv.divide {s₀ s t : State} (h : Inv s₀ s) (k : Divide.KeepD s t) : Inv s₀ t :=
  h.step k.sp (k.other _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (k.other _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (fun r hr => k.other _ (by rintro rfl; exact absurd hr (by decide))
      (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide))
      (by rintro rfl; exact absurd hr (by decide)) (by rintro rfl; exact absurd hr (by decide)))
    k.rd k.wr (by rw [k.mem]; exact Frame.refl _ _)

theorem Prm.of_mem {s₀ s t : State} (pr : Prm s₀ s) (h : t.mem = s.mem) : Prm s₀ t :=
  ⟨by rw [lw_mem h]; exact pr.segLen, by rw [lw_mem h]; exact pr.laneLen,
    by rw [lw_mem h]; exact pr.stride⟩

/-- `x << n`, as a number, when it does not overflow. -/
theorem shl_nat {x : BitVec 64} {n : Nat} (h : x.toNat * 2 ^ n < 2 ^ 64) :
    (x <<< n).toNat = x.toNat * 2 ^ n := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

theorem toNat_ext32 (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

theorem ofNat_toNat {x : BitVec 64} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 64 n := by
  subst h; simp

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem parameters_ok {s : State} (h : Inv s₀ s) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → Prm s₀ t → WP isa (.block is) t Q) :
    WP isa (.block (parameters ++ is)) s Q := by
  have hL := hp.lanes_lt
  have hL1 := hp.lanes_pos
  have hb := hp.blocks_eq
  have hbl := hp.blocks_le
  have hm := mcost_lt s₀
  have hseg := hp.segLen_eq
  have hlane := hp.laneLen_eq
  simp only [parameters, List.cons_append, List.append_assoc]
  refine wp_ldw hp h (i := Impl.Argon2.PPC64LE.Derive.lanesArg) (by decide) fun s₂ u₂ => ?_
  have i₂ := h.upd u₂
  refine wp_lsl (by decide) fun s₃ u₃ => ?_
  have i₃ := i₂.upd u₃
  have e₃ : (s₃.gpr .r5).toNat = 4 * lanesN s₀ := by
    rw [u₃.gpr, u₂.gpr, shl_nat (by rw [toNat_ext32]; show lanesN s₀ * 4 < _; omega_using [hL]), toNat_ext32]
    show lanesN s₀ * 4 = _
    omega_using []
  refine wp_ldw hp i₃ (i := Impl.Argon2.PPC64LE.Derive.memoryCostArg) (by decide) fun s₅ u₅ => ?_
  have i₅ := i₃.upd u₅
  refine Divide.code_ok (D := 4 * lanesN s₀) (by omega_using [hL1]) (by omega_using [hL])
    (by rw [u₅.other _ (by decide), e₃]) fun s₆ c₆ _ k₆ => ?_
  have i₆ := i₅.divide k₆
  have c₆' : (s₆.gpr .r6).toNat = (prm s₀).segmentLen := by
    rw [c₆, u₅.gpr, hseg, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
    rfl
  refine wp_stloc i₆ (d := segLenOff) (by decide) fun s₇ i₇ v₇ o₇ g₇ _ => ?_
  have hll : (prm s₀).laneLen ≤ mcostN s₀ :=
    Nat.le_trans (Nat.le_trans (Nat.le_mul_of_pos_left _ hL1) (Nat.le_of_eq hb.symm)) hbl
  refine wp_lsl (by decide) fun s₈ u₈ => ?_
  have i₈ := i₇.upd u₈
  have e₈ : (s₈.gpr .r6).toNat = (prm s₀).laneLen := by
    rw [u₈.gpr, g₇, shl_nat (by rw [c₆']; omega_using [hm, hlane, hll]), c₆', hlane]; omega_using []
  refine wp_stloc i₈ (d := laneLenOff) (by decide) fun s₉ i₉ v₉ o₉ g₉ _ => ?_
  refine wp_lsl (by decide) fun s₁₀ u₁₀ => ?_
  have i₁₀ := i₉.upd u₁₀
  have e₁₀ : (s₁₀.gpr .r6).toNat = (prm s₀).laneLen * 1024 := by
    rw [u₁₀.gpr, g₉, shl_nat (by rw [e₈]; omega_using [hm, hll]), e₈]
  refine wp_stloc i₁₀ (d := strideOff) (by decide) fun s₁₁ i₁₁ v₁₁ o₁₁ _ _ =>
    k s₁₁ i₁₁ ⟨?_, ?_, ?_⟩
  · rw [o₁₁ _ (by decide) (by decide), lw_mem u₁₀.mem, o₉ _ (by decide) (by decide),
      lw_mem u₈.mem, v₇]
    exact ofNat_toNat c₆'
  · rw [o₁₁ _ (by decide) (by decide), lw_mem u₁₀.mem, v₉]
    exact ofNat_toNat e₈
  · rw [v₁₁]
    exact ofNat_toNat e₁₀

end

end VG.Proof.Argon2.PPC64LE.Derive

end

end

/-!
# Argon2 on PPC64LE: `scratch` in the derivation

`r31` points to `scratch` throughout the body. `wp_stscrw` and `wp_stscrd`
store a word or a doubleword there; `Inv.keeps` keeps the invariant and the
frame's variables through a call that writes only the first 832 bytes of
`scratch` and the calls' frames (`HPrime.Keeps`), and `repr_frame` a BLAKE2b
streaming state through writes outside it.
-/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.Derive

open VG VG.PPC64LE
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_std wp_stw)
open VG.Spec.Blake2 (Repr b bytesAt)

/-- A BLAKE2b streaming state at `p` is kept by writes outside its 192 bytes. -/
theorem repr_frame {m m' : Mem} {rs : List Region} (f : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 192⟩ r) {h0 : Spec.Blake2.HashValue 64} {d : List Byte}
    (h : Repr b h0 m p d) : Repr b h0 m' p d :=
  Proof.Blake2.repr_congr' (by decide) (fun i hi => by
    have hi' : i < 192 := by simpa [Proof.Blake2.bufOff, Spec.Blake2.blockBytes] using hi
    exact f _ fun r hr hc => hd r hr _ (Offset.contains_base p (show i + 1 ≤ 192 by omega_using [hi'])
      (by omega_using [hi'])) hc) h

theorem finalHash_length (h0 : Spec.Blake2.HashValue 64) (d : List Byte) :
    (Spec.Blake2.finalHash b h0 d).length = 64 := by
  simp only [Spec.Blake2.finalHash, Proof.Argon2.wordList_length, Vector.length_toList]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem scr_mem : scrR s₀ ∈ (entry s₀).wr := by
  rw [entry_wr, hp.wr]; simp

theorem mem_mem : memR s₀ ∈ (entry s₀).wr := by rw [entry_wr, hp.wr]; simp

theorem Inv.scr_in {s : State} (h : Inv s₀ s) : (⟨s.gpr .r31, 16384⟩ : Region) ∈ s.wr := by
  rw [h.r31, h.wr]; exact scr_mem hp

/-- `scratch` is outside the calls' frames. -/
theorem Inv.stk_scr {s : State} (h : Inv s₀ s) :
    (below s.sp 48).Disjoint ⟨s.gpr .r31, 16384⟩ := by
  rw [h.sp, h.r31, callR_eq]
  refine (hp.stk_all (scrR s₀) (by simp)).sub_left ?_
  have e : B s₀ = B s₀ + BitVec.ofNat 64 0 := (BitVec.add_zero _).symm
  show Region.Sub ⟨B s₀, 48⟩ _
  rw [e]; exact stk_sub (by decide)

omit hp in
/-- A part of `scratch`. -/
theorem scr_sub {o n : Nat} (h : o + n ≤ 16384) : Region.Sub ⟨scrP s₀ + BitVec.ofNat 64 o, n⟩ (scrR s₀) :=
  Offset.sub_base _ h

/-- A call that keeps the caller's registers and writes only `scratch` and
its frames keeps the invariant and the frame's variables. -/
theorem Inv.keeps {s t : State} (h : Inv s₀ s) (k : HPrime.Keeps s t) :
    Inv s₀ t ∧ ∀ d, 32 ≤ d → d + 8 ≤ 336 → lw s₀ t d = lw s₀ s d := by
  have hs : ∀ r ∈ [⟨s.gpr .r31, 832⟩, below s.sp 48],
      ∃ r' ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨scrR s₀, by simp, ?_⟩
      rw [h.r31]; exact Region.sub_prefix (by decide)
    · exact ⟨callR s₀, by simp, by rw [h.sp, callR_eq]; exact fun _ h => h⟩
  refine ⟨h.step k.sp (k.regs _ (by decide)) (k.regs _ (by decide))
    (fun r hr => k.regs r (by revert hr; revert r; decide)) k.rd k.wr ?_,
    fun d h₁ h₂ => lw_keep hp k.frame hs h₁ h₂⟩
  refine k.frame.sub fun r hr => ?_
  obtain ⟨r', hr', hs'⟩ := hs r hr
  refine ⟨r', ?_, hs'⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl <;> simp

/-- `stw r, o(r31)`, to `scratch`. -/
theorem wp_stscrw {s : State} (h : Inv s₀ s) {o : Nat} (ho : o + 4 ≤ 16384) (ho' : o < 2 ^ 15)
    {r : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → t.mem = s.mem.writeW (scrP s₀ + BitVec.ofNat 64 o) ((s.gpr r).setWidth 32) →
      t.gpr = s.gpr → (∀ d, 32 ≤ d → d + 8 ≤ 336 → lw s₀ t d = lw s₀ s d) →
      Frame [⟨scrP s₀ + BitVec.ofNat 64 o, 4⟩] s.mem t.mem → WP isa (.block is) t Q) :
    WP isa (.block (.store .w r .r31 o :: is)) s Q := by
  have hc : (scrR s₀).Contains (scrP s₀ + BitVec.ofNat 64 o) 4 :=
    Offset.contains_base _ (by omega_using [ho]) (by omega_using [ho])
  refine wp_stw (a := scrP s₀ + BitVec.ofNat 64 o) ho' (by rw [h.r31])
    (by rw [h.wr]; exact ⟨scrR s₀, scr_mem hp, hc⟩) fun t u => ?_
  have f : Frame [⟨scrP s₀ + BitVec.ofNat 64 o, 4⟩] s.mem t.mem := by
    rw [u.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine k t (h.mupd u ((Frame.refl _ _).writeW (r := scrR s₀) (by simp) _ hc)) u.mem u.gpr
    (fun d h₁ h₂ => lw_keep hp f (fun r hr => ?_) h₁ h₂) f
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨scrR s₀, by simp, scr_sub (by omega_using [ho])⟩

/-- `std r, o(r31)`, to `scratch`. -/
theorem wp_stscrd {s : State} (h : Inv s₀ s) {o : Nat} (ho : o + 8 ≤ 16384) (ho' : o < 2 ^ 15)
    (ho4 : o % 4 = 0) {r : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → t.mem = s.mem.writeW (scrP s₀ + BitVec.ofNat 64 o) (s.gpr r) →
      t.gpr = s.gpr → (∀ d, 32 ≤ d → d + 8 ≤ 336 → lw s₀ t d = lw s₀ s d) →
      Frame [⟨scrP s₀ + BitVec.ofNat 64 o, 8⟩] s.mem t.mem → WP isa (.block is) t Q) :
    WP isa (.block (.store .d r .r31 o :: is)) s Q := by
  have hc : (scrR s₀).Contains (scrP s₀ + BitVec.ofNat 64 o) 8 :=
    Offset.contains_base _ (by omega_using [ho]) (by omega_using [ho])
  refine wp_std (a := scrP s₀ + BitVec.ofNat 64 o) ⟨ho', ho4⟩ (by rw [h.r31])
    (by rw [h.wr]; exact ⟨scrR s₀, scr_mem hp, hc⟩) fun t u => ?_
  have f : Frame [⟨scrP s₀ + BitVec.ofNat 64 o, 8⟩] s.mem t.mem := by
    rw [u.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine k t (h.mupd u ((Frame.refl _ _).writeW (r := scrR s₀) (by simp) _ hc)) u.mem u.gpr
    (fun d h₁ h₂ => lw_keep hp f (fun r hr => ?_) h₁ h₂) f
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨scrR s₀, by simp, scr_sub (by omega_using [ho])⟩

/-- A store to the frame is outside `scratch`. -/
theorem loc_scr {d : Nat} (h₁ : 32 ≤ d) (h₂ : d + 8 ≤ 336) {o n : Nat} (ho : o + n ≤ 16384) :
    Region.Disjoint ⟨E s₀ + BitVec.ofNat 64 d, 8⟩ ⟨scrP s₀ + BitVec.ofNat 64 o, n⟩ :=
  (loc_disj hp h₁ h₂ (scrR s₀) (by simp)).sub_right (scr_sub ho)

omit hp in
/-- A store to the frame keeps what lies in `scratch`. -/
theorem frame_loc {m : Mem} {d : Nat} (v : BitVec 64) :
    Frame [⟨E s₀ + BitVec.ofNat 64 d, 8⟩] m (m.writeW (E s₀ + BitVec.ofNat 64 d) v) :=
  (Frame.refl _ m).writeW (List.mem_singleton_self _) v (Region.contains_self _ _)

/-- A store to the frame keeps a streaming state in `scratch`. -/
theorem repr_loc {m : Mem} {d : Nat} (h₁ : 32 ≤ d) (h₂ : d + 8 ≤ 336) (v : BitVec 64)
    {h0 : Spec.Blake2.HashValue 64} {data : List Byte} (h : Repr b h0 m (scrP s₀) data) :
    Repr b h0 (m.writeW (E s₀ + BitVec.ofNat 64 d) v) (scrP s₀) data :=
  repr_frame (frame_loc v) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    have := (loc_scr hp h₁ h₂ (o := 0) (n := 192) (by decide)).symm
    simpa using this) h

end

end VG.Proof.Argon2.PPC64LE.Derive

module

import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Argon2.RISCV64.Ops
public import VerifiedGarbage.Impl.Argon2.RISCV64.Derive
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.RISCV64.Wp
public import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Blake2.Stream
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Spec.Argon2.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Argon2.Dimensions

/-! ### `Argon2.RISCV64.Derive.Body`, which this module and modules that import it used -/

section

/-! ### `Argon2.RISCV64.Derive.Contract`, which this module and modules that import it used -/

section

/-!
# Argon2 on RISC-V: the contract of the derivation's proof

`deriveRV`: `vg_argon2`'s contract, with its precondition a structure
(`DPre`; `Derive/Verified.lean` reaches the shared contract). The
derivation uses the 320 bytes of stack below the stack pointer, its frame:
the functions it calls use none. `memory` and `scratch` are 8-byte aligned,
as RISC-V's contracts require of arrays of `u64` (`Abi.alignsBufs`).
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64 VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

/-- Argument `i`: `a0`–`a7`, then those on the stack. -/
def arg (s : State) : Nat → BitVec 64
  | 0 => s.gpr .a0
  | 1 => s.gpr .a1
  | 2 => s.gpr .a2
  | 3 => s.gpr .a3
  | 4 => s.gpr .a4
  | 5 => s.gpr .a5
  | 6 => s.gpr .a6
  | 7 => s.gpr .a7
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
/-- The ten arguments on the stack. -/
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 80⟩
/-- The stack the derivation uses. -/
abbrev stkR0 : Region := below s₀.sp 320

/-- The inputs, on entry. -/
abbrev pwB : List Byte := bytesAt s₀.mem (pwR s₀).base (pwL s₀)
abbrev saltB : List Byte := bytesAt s₀.mem (saltR s₀).base (saltL s₀)
abbrev secB : List Byte := bytesAt s₀.mem (secR s₀).base (secL s₀)
abbrev adB : List Byte := bytesAt s₀.mem (adR s₀).base (adL s₀)

end

/-- The facts of `deriveRV`'s precondition. -/
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
  sp_lo : 320 ≤ s₀.sp.toNat
  sp_hi : s₀.sp.toNat + 80 ≤ 2 ^ 64
  sp_al : s₀.sp.toNat % 16 = 0
  mem_al : (memP s₀).toNat % 8 = 0
  scr_al : (scrP s₀).toNat % 8 = 0
  kind_le : (kindV s₀).toNat ≤ 2
  valid : valid (prm s₀) (pwL s₀) (saltL s₀) (secL s₀) (adL s₀)
  threads : 1 ≤ threadsN s₀ ∧ threadsN s₀ < 2 ^ 24
  blocks : blocksN s₀ = (prm s₀).blocks

/-- `vg_argon2`. -/
def deriveRV : Contract isa where
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

end VG.Proof.Argon2.RISCV64.Derive

end

end

/-!
# Argon2 on RISC-V: the state of the derivation's body

The derivation's frame is the 320 bytes below the stack pointer on entry,
from `E s₀` (`Impl/Argon2/RISCV64/Layout.lean`, at offsets `at' s₀ d`), and
the caller's ten stack arguments are above it, at `at' s₀ (320 + 8 i)`.

`Inv s₀ s`: in the body, `sp` and `s3` point to the frame, `s4` to
`scratch` and `s0` 2048 bytes above it, the registers the body never writes
are the caller's, the permissions are those of the body's entry, and memory
has changed since the setup (`setupMem`) only in the memory matrix,
`scratch`, the output, H′'s input and the loop variables in the frame. The
return address, the caller's registers and the arguments are therefore kept
(`Inv.arg`, `Inv.input`, `Inv.saved`).
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd)
open VG.Spec.Blake2 (bytesAt)
open VG.Impl.Argon2.RISCV64.Derive (locals argOff savedSlots argSlots)

/-! ## The stack -/

section
variable (s₀ : State)

/-- The frame's stack pointer: the body's. -/
abbrev E : Addr := s₀.sp - BitVec.ofNat 64 320

/-- `d` bytes above `E s₀`. -/
abbrev at' (d : Nat) : Addr := E s₀ + BitVec.ofNat 64 d

/-- The state the body starts in. -/
def entry : State := allocd 320 s₀

/-- H′'s input in the frame: H₀, LE32(column), LE32(lane). -/
abbrev inR : Region := ⟨at' s₀ 0, 72⟩

/-- The loop variables and temporaries in the frame. -/
abbrev varR : Region := ⟨at' s₀ 184, 128⟩

/-- The regions the body writes. -/
abbrev bodyW : List Region := [memR s₀, scrR s₀, outR s₀, inR s₀, varR s₀]

/-- The registers the body never writes. -/
abbrev untouched : List Reg := [.s5, .s6, .s7, .s8, .s9, .s10, .s11]

/-- What the body stores in its frame first: the return address, the
caller's `s0`–`s4` and the register arguments. -/
def setupMem : Mem := Spill.saveMem s₀.mem (E s₀) s₀.gpr (savedSlots ++ argSlots)

/-- The doubleword at `s3 + d`. -/
abbrev lw (s : State) (d : Nat) : BitVec 64 := s.mem.readW (E s₀ + BitVec.ofNat 64 d) 64

/-- The pointer 2048 bytes into `scratch`. -/
abbrev hiP : Addr := scrP s₀ + BitVec.ofNat 64 2048

end

theorem entry_sp (s₀ : State) : (entry s₀).sp = E s₀ := rfl
theorem entry_wr (s₀ : State) : (entry s₀).wr = ⟨at' s₀ 0, 320⟩ :: s₀.wr := by
  rw [show at' s₀ 0 = E s₀ from BitVec.add_zero _]; rfl

/-! ## The invariant -/

/-- The state of the body. -/
structure Inv (s₀ s : State) : Prop where
  sp : s.sp = E s₀
  s3 : s.gpr .s3 = E s₀
  s4 : s.gpr .s4 = scrP s₀
  s0 : s.gpr .s0 = hiP s₀
  eal : (E s₀).toNat % 16 = 0
  sal : (scrP s₀).toNat % 8 = 0
  keep : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = (entry s₀).wr
  frame : Frame (bodyW s₀) (setupMem s₀) s.mem

/-- A step that writes registers the invariant does not name, and memory
within the body's regions. -/
theorem Inv.step {s₀ s t : State} (h : Inv s₀ s) (hs : t.sp = s.sp)
    (h3 : t.gpr .s3 = s.gpr .s3) (h4 : t.gpr .s4 = s.gpr .s4) (h0 : t.gpr .s0 = s.gpr .s0)
    (hk : ∀ r ∈ untouched, t.gpr r = s.gpr r) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hf : Frame (bodyW s₀) s.mem t.mem) : Inv s₀ t :=
  ⟨hs.trans h.sp, h3.trans h.s3, h4.trans h.s4, h0.trans h.s0, h.eal, h.sal,
    fun r hr => (hk r hr).trans (h.keep r hr), hrd.trans h.rd, hwr.trans h.wr, h.frame.trans hf⟩

/-- A register the invariant does not name. -/
abbrev Free (r : Reg) : Prop := r ≠ .s3 ∧ r ≠ .s4 ∧ r ≠ .s0 ∧ r ∉ untouched

theorem Inv.upd {s₀ s t : State} {r : Reg} {v : BitVec 64} (h : Inv s₀ s) (u : Upd s t r v)
    (hr : Free r := by decide) : Inv s₀ t :=
  h.step u.sp (u.other _ (Ne.symm hr.1)) (u.other _ (Ne.symm hr.2.1)) (u.other _ (Ne.symm hr.2.2.1))
    (fun q hq => u.other _ fun e => hr.2.2.2 (e ▸ hq)) u.rd u.wr (by rw [u.mem]; exact Frame.refl _ _)

theorem Inv.mupd {s₀ s t : State} {m : Mem} (h : Inv s₀ s) (u : Mupd s t m)
    (hf : Frame (bodyW s₀) s.mem m) : Inv s₀ t :=
  h.step u.sp (by rw [u.gpr]) (by rw [u.gpr]) (by rw [u.gpr]) (fun _ _ => by rw [u.gpr]) u.rd u.wr
    (u.mem ▸ hf)

/-! ## Facts of the precondition about the stack -/

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem E_toNat : (E s₀).toNat = s₀.sp.toNat - 320 :=
  toNat_sub_ofNat' (by have := hp.sp_lo; omega_using [this])

theorem E_hi : (E s₀).toNat + 400 ≤ 2 ^ 64 := by
  have := hp.sp_hi; have := hp.sp_lo; rw [E_toNat hp]; omega_arith

theorem E_al : (E s₀).toNat % 16 = 0 := by
  rw [E_toNat hp]; have := hp.sp_al; have := hp.sp_lo; omega_arith

omit hp in
theorem stk_sub {d n : Nat} (h : d + n ≤ 320) : Region.Sub ⟨at' s₀ d, n⟩ (stkR0 s₀) :=
  Offset.sub_base _ h

end

/-- `x` bytes above the stack pointer on entry. -/
theorem sp_add (s₀ : State) (x : Nat) : s₀.sp + BitVec.ofNat 64 x = at' s₀ (320 + x) := by
  show _ = s₀.sp - BitVec.ofNat 64 320 + BitVec.ofNat 64 (320 + x)
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

/-- The arguments on the stack. -/
theorem stackArg_eq (s₀ : State) (i : Nat) : stackArgAddr s₀ i = at' s₀ (320 + 8 * i) := by
  rw [stackArgAddr, sp_add]

/-! ## The frame's slots -/

theorem slots_fits : Spill.Fits (savedSlots ++ argSlots) := by decide

theorem slots_in : ∀ p ∈ savedSlots ++ argSlots, 72 ≤ p.2 ∧ p.2 + 8 ≤ 72 + 112 := by decide

/-- The slots the setup writes. -/
abbrev setupR (s₀ : State) : Region := ⟨at' s₀ 72, 112⟩

theorem setupMem_frame (s₀ : State) : Frame [setupR s₀] s₀.mem (setupMem s₀) :=
  Spill.saveMem_frame slots_in (by decide) s₀.mem (E s₀) s₀.gpr

theorem setupMem_slot (s₀ : State) {r : Reg} {d : Nat} (h : (r, d) ∈ savedSlots ++ argSlots) :
    (setupMem s₀).readW (E s₀ + BitVec.ofNat 64 d) 64 = s₀.gpr r :=
  Spill.saveMem_saved slots_fits _ _ _ (r, d) h

/-! ## What the body's writes keep -/

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- A region of the stack the derivation uses is outside the buffers. -/
theorem stk_disj {d n : Nat} (h : d + n ≤ 320) :
    ∀ r ∈ [memR s₀, scrR s₀, outR s₀], Region.Disjoint ⟨at' s₀ d, n⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact (hp.stk_all _ (by simp)).sub_left (stk_sub h)

/-- A region of the frame outside the body's own: neither H′'s input nor the
loop variables. -/
theorem frame_disj {d n : Nat} (h₁ : 72 ≤ d ∧ d + n ≤ 184) :
    ∀ r ∈ bodyW s₀, Region.Disjoint ⟨at' s₀ d, n⟩ r := by
  intro r hr
  simp only [bodyW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact stk_disj hp (by omega_using [h₁]) _ (by simp)
  · exact stk_disj hp (by omega_using [h₁]) _ (by simp)
  · exact stk_disj hp (by omega_using [h₁]) _ (by simp)
  · exact Offset.disjoint _ (by omega_using [h₁]) (by omega_using [h₁]) (by omega_using [])
  · exact Offset.disjoint _ (by omega_using [h₁]) (by omega_using [h₁]) (by omega_using [])

omit hp in
theorem argR_eq : argR s₀ = ⟨at' s₀ 320, 80⟩ := by
  show (⟨stackArgAddr s₀ 0, 80⟩ : Region) = _
  rw [stackArg_eq]

/-- The arguments on the stack are outside the body's regions. -/
theorem arg_disj {d n : Nat} (h₁ : 320 ≤ d) (h₂ : d + n ≤ 400) :
    ∀ r ∈ bodyW s₀, Region.Disjoint ⟨at' s₀ d, n⟩ r := by
  have sub : Region.Sub ⟨at' s₀ d, n⟩ (argR s₀) := by
    rw [argR_eq]; exact Offset.sub _ h₁ (by omega_using [h₂])
  have hi := E_hi hp
  intro r hr
  simp only [bodyW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (hp.ro_w _ (by simp) _ (by simp)).sub_left sub
  · exact (hp.ro_w _ (by simp) _ (by simp)).sub_left sub
  · exact (hp.ro_w _ (by simp) _ (by simp)).sub_left sub
  · exact Offset.disjoint _ (by omega_using [h₁]) (by omega_using [h₂]) (by omega_using [])
  · exact Offset.disjoint _ (by omega_using [h₁]) (by omega_using [h₂]) (by omega_using [])

theorem Inv.slot {s : State} (h : Inv s₀ s) {d : Nat} (h₁ : 72 ≤ d) (h₂ : d + 8 ≤ 184) :
    s.mem.readW (at' s₀ d) 64 = (setupMem s₀).readW (at' s₀ d) 64 :=
  h.frame.readW (Region.contains_self _ _) (frame_disj hp ⟨h₁, h₂⟩) (by decide)

/-- The doubleword `d` bytes above the frame's stack pointer, among the setup's
slots. -/
theorem Inv.saved {s : State} (h : Inv s₀ s) {r : Reg} {d : Nat}
    (hr : (r, d) ∈ savedSlots ++ argSlots) : lw s₀ s d = s₀.gpr r := by
  have := slots_in _ hr
  rw [lw, h.slot hp (by simp only at this; omega_using [this]) (by simp only at this; omega_using [this]), setupMem_slot s₀ hr]

/-- The arguments, from the frame or the stack. -/
theorem Inv.arg {s : State} (h : Inv s₀ s) {i : Nat} (hi : i < 18) :
    s.mem.readW (E s₀ + BitVec.ofNat 64 (argOff i)) 64 = arg s₀ i := by
  by_cases h8 : i < 8
  · rcases (by omega_using [h8] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h.saved hp (r := .a0) (d := 120) (by decide)
    · exact h.saved hp (r := .a1) (d := 128) (by decide)
    · exact h.saved hp (r := .a2) (d := 136) (by decide)
    · exact h.saved hp (r := .a3) (d := 144) (by decide)
    · exact h.saved hp (r := .a4) (d := 152) (by decide)
    · exact h.saved hp (r := .a5) (d := 160) (by decide)
    · exact h.saved hp (r := .a6) (d := 168) (by decide)
    · exact h.saved hp (r := .a7) (d := 176) (by decide)
  · obtain ⟨k, rfl⟩ : ∃ k, i = 8 + k := ⟨i - 8, by omega_using [h8]⟩
    have ea : E s₀ + BitVec.ofNat 64 (argOff (8 + k)) = at' s₀ (320 + 8 * k) := by
      have e : argOff (8 + k) = 320 + 8 * k := by
        simp only [argOff, locals]; rw [ite_eq_right_iff.mpr (by omega_using [])]; omega_using []
      rw [e]
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
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hp.ro_w _ hR' _ (by simp)
  · exact hp.ro_w _ hR' _ (by simp)
  · exact hp.ro_w _ hR' _ (by simp)
  · exact stk.sub_right (stk_sub (by decide))
  · exact stk.sub_right (stk_sub (by decide))

end

end VG.Proof.Argon2.RISCV64.Derive

end

end

/-!
# Argon2 on RISC-V: the derivation's locals

`lw s₀ s d`: the doubleword at `s3 + d` in the body. A store to the frame's
variables keeps the invariant and every other doubleword (`wp_stloc`);
writes to the memory matrix, `scratch` or the output keep all of them
(`lw_keep`). `wp_lda` and `wp_ldw` load an argument, of 64 or 32 bits.
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd wp_ld wp_sd wp_mv wp_addSp wp_addi)
open VG.Proof.Argon2.RISCV64 (wp_lwu)
open VG.Impl.Argon2.RISCV64.Derive (ld st lda ldw argOff locals savedSlots argSlots)

/-- An offset of a doubleword in the frame. -/
abbrev LocOff (d : Nat) : Prop := d + 8 ≤ 320 ∧ d % 8 = 0

/-- An offset of a doubleword the body may write: H′'s input or the loop
variables. -/
abbrev VarOff (d : Nat) : Prop := (d + 8 ≤ 72 ∨ 184 ≤ d ∧ d + 8 ≤ 312) ∧ d % 8 = 0

section
variable {s₀ : State}

theorem loc_in {s : State} (h : Inv s₀ s) {d n : Nat} (h₂ : d + n ≤ 320) :
    InRegions s.wr (E s₀ + BitVec.ofNat 64 d) n := by
  rw [h.wr, entry_wr]
  exact ⟨_, List.mem_cons_self .., Offset.contains _ (by omega_using []) (by omega_using [h₂]) (by omega_using [])⟩

theorem loc_in' {s : State} (h : Inv s₀ s) {d n : Nat} (h₂ : d + n ≤ 320) :
    InRegions (s.rd ++ s.wr) (E s₀ + BitVec.ofNat 64 d) n :=
  let ⟨r, hr, hc⟩ := loc_in h h₂
  ⟨r, List.mem_append_right _ hr, hc⟩

theorem Inv.loc_al {s : State} (h : Inv s₀ s) {d k : Nat} (hk : k ∣ 16) (hd : d % k = 0) :
    (E s₀ + BitVec.ofNat 64 d).toNat % k = 0 := by
  have := h.eal
  have hE := (E s₀).isLt
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h64 : k ∣ 2 ^ 64 := Nat.dvd_trans hk (by decide)
  rw [Nat.mod_mod_of_dvd _ h64, Nat.add_mod, Nat.mod_mod_of_dvd _ h64, hd,
    Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hk (Nat.dvd_of_mod_eq_zero this)), Nat.add_zero,
    Nat.zero_mod]

/-- A store's doubleword is within the body's regions. -/
theorem var_in {d : Nat} (hd : VarOff d) :
    ∃ r ∈ bodyW s₀, r.Contains (E s₀ + BitVec.ofNat 64 d) 8 := by
  rcases hd.1 with h | h
  · exact ⟨inR s₀, by simp, Offset.contains _ (by omega_using []) (by omega_using [h]) (by omega_using [])⟩
  · exact ⟨varR s₀, by simp, Offset.contains _ (by omega_using [h]) (by omega_using [h]) (by omega_using [])⟩

/-- `sd r, d(s3)` -/
theorem wp_stloc {s : State} (h : Inv s₀ s) {d : Nat} (hd : VarOff d) {r : Reg} {is : List Instr}
    {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → lw s₀ t d = s.gpr r →
      (∀ e, e + 8 ≤ 320 → d + 8 ≤ e ∨ e + 8 ≤ d → lw s₀ t e = lw s₀ s e) → t.gpr = s.gpr →
      t.mem = s.mem.writeW (E s₀ + BitVec.ofNat 64 d) (s.gpr r) → WP isa (.block is) t Q) :
    WP isa (.block (st d r :: is)) s Q := by
  obtain ⟨R, hR, hc⟩ := var_in hd
  refine wp_sd (a := E s₀ + BitVec.ofNat 64 d) (by omega) (by rw [h.s3])
    (h.loc_al (by decide) hd.2) (loc_in h (by omega))
    fun t u => k t (h.mupd u ((Frame.refl _ _).writeW hR _ hc))
    (by rw [lw, u.mem, Mem.readW_writeW_self64]) (fun e he he' => ?_) u.gpr u.mem
  rw [lw, lw, u.mem, Mem.readW_writeW_sep (Offset.sep _ (by omega_using [he']) (by omega_using [he]) (by omega)) (by decide)]

/-- `ld r, d(s3)` -/
theorem wp_ldloc {s : State} (h : Inv s₀ s) {d : Nat} (hd : LocOff d) {r : Reg} {is : List Instr}
    {Q : State → Prop} (k : ∀ t, Upd s t r (lw s₀ s d) → WP isa (.block is) t Q) :
    WP isa (.block (ld r d :: is)) s Q :=
  wp_ld (by omega) (by rw [h.s3]) (h.loc_al (by decide) hd.2) (loc_in' h hd.1) k

theorem argOff_lt {i : Nat} (hi : i < 18) : argOff i < 2048 ∧ argOff i % 8 = 0 := by
  revert hi; revert i; decide

variable (hp : DPre s₀)
include hp

/-- Argument `i` is readable. -/
theorem Inv.arg_in {s : State} (h : Inv s₀ s) {i : Nat} (hi : i < 18) {n : Nat} (hn : n ≤ 8) :
    InRegions (s.rd ++ s.wr) (E s₀ + BitVec.ofNat 64 (argOff i)) n := by
  by_cases h8 : i < 8
  · refine loc_in' h ?_; simp only [argOff, locals, h8, ite_true]; omega_using [hi, hn]
  · have e : argOff i = 320 + 8 * (i - 8) := by
      simp only [argOff, locals]; rw [ite_eq_right_iff.mpr (by omega_using [h8])]
    have hE := E_hi hp
    rw [h.rd, e, hp.rd]
    refine ⟨argR s₀, List.mem_append_left _ (by simp), ?_⟩
    rw [argR_eq]
    exact Offset.contains _ (by omega_using []) (by omega_using [hi, hn]) (by omega_using [])

/-- `ld r, (argOff i)(s3)`: a 64-bit argument. -/
theorem wp_lda {s : State} (h : Inv s₀ s) {i : Nat} (hi : i < 18) {r : Reg} {is : List Instr}
    {Q : State → Prop} (k : ∀ t, Upd s t r (arg s₀ i) → WP isa (.block is) t Q) :
    WP isa (.block (lda r i :: is)) s Q :=
  wp_ld (argOff_lt hi).1 (by rw [h.s3]) (h.loc_al (by decide) (argOff_lt hi).2)
    (h.arg_in hp hi (by decide)) fun t u => k t (by rw [h.arg hp hi] at u; exact u)

/-- `lwu r, (argOff i)(s3)`: a 32-bit argument, zero-extended. -/
theorem wp_ldw {s : State} (h : Inv s₀ s) {i : Nat} (hi : i < 18) {r : Reg} {is : List Instr}
    {Q : State → Prop} (k : ∀ t, Upd s t r ((arg32 s₀ i).setWidth 64) → WP isa (.block is) t Q) :
    WP isa (.block (ldw r i :: is)) s Q :=
  wp_lwu (argOff_lt hi).1 (by rw [h.s3])
    (h.loc_al (by decide) (by have := (argOff_lt hi).2; omega_using [this])) (h.arg_in hp hi (by decide))
    fun t u => k t (by rw [h.arg32 hp hi] at u; exact u)

/-- The frame's doublewords are outside the buffers. -/
theorem loc_disj {d : Nat} (h₂ : d + 8 ≤ 320) :
    ∀ r ∈ [memR s₀, scrR s₀, outR s₀], Region.Disjoint ⟨E s₀ + BitVec.ofNat 64 d, 8⟩ r :=
  stk_disj hp h₂

/-- The frame is kept by writes outside it. -/
theorem lw_keep {s t : State} {rs : List Region} (f : Frame rs s.mem t.mem)
    (hs : ∀ r ∈ rs, ∃ r' ∈ [memR s₀, scrR s₀, outR s₀], Region.Sub r r') {d : Nat}
    (h₂ : d + 8 ≤ 320) : lw s₀ t d = lw s₀ s d :=
  (f.sub hs).readW (Region.contains_self _ _) (loc_disj hp h₂) (by decide)

end

theorem saveMem_congr {m : Mem} {b : Addr} {g g' : Reg → BitVec 64} :
    ∀ {l : List (Reg × Nat)}, (∀ p ∈ l, g p.1 = g' p.1) →
      Spill.saveMem m b g l = Spill.saveMem m b g' l
  | [], _ => rfl
  | (r, d) :: l, h => by
    simp only [Spill.saveMem]
    rw [h (r, d) List.mem_cons_self]
    exact saveMem_congr fun p hp => h p (List.mem_cons_of_mem _ hp)

/-- `scratch`, from the stack, after the setup. -/
theorem setupMem_arg (s₀ : State) {i : Nat} (h₁ : 8 ≤ i) (h₂ : i < 18) :
    (setupMem s₀).readW (E s₀ + BitVec.ofNat 64 (argOff i)) 64 = arg s₀ i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = 8 + k := ⟨i - 8, by omega_using [h₁]⟩
  have e : argOff (8 + k) = 320 + 8 * k := by
    simp only [argOff, locals]; rw [ite_eq_right_iff.mpr (by omega_using [])]; omega_using []
  rw [e, (setupMem_frame s₀).readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega_using []) (by omega_using [h₂]) (by omega_using [])) (by decide),
    show E s₀ + BitVec.ofNat 64 (320 + 8 * k) = stackArgAddr s₀ k from (stackArg_eq s₀ k).symm,
    show 8 + k = k + 8 by omega_using []]
  rfl

/-- The body's first instructions: the return address, the caller's
registers and the register arguments to the frame, `s3` to the frame, `s4`
to `scratch` and `s0` 2048 bytes above it. -/
theorem setup_ok {s₀ : State} (hp : DPre s₀) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → t.mem = setupMem s₀ → WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.RISCV64.Derive.setup ++ is)) (entry s₀) Q := by
  have hl : ∀ p ∈ savedSlots ++ argSlots, p.1 ≠ .t0 := by decide
  have eal := E_al hp
  simp only [Impl.Argon2.RISCV64.Derive.setup, List.cons_append, List.append_assoc]
  refine wp_addSp (imm := 0) (by decide) fun c u₁ => ?_
  have c0 : c.gpr .t0 = E s₀ := by rw [u₁.gpr, entry_sp, BitVec.add_zero]
  have cg : ∀ r, r ≠ .t0 → c.gpr r = s₀.gpr r := fun r h₁ => by rw [u₁.other _ h₁]; rfl
  have cwr : c.wr = (entry s₀).wr := u₁.wr
  have inE : ∀ d n, d + n ≤ 320 → InRegions c.wr (E s₀ + BitVec.ofNat 64 d) n :=
    fun d n h₂ => by
      rw [cwr, entry_wr]
      exact ⟨_, List.mem_cons_self .., Offset.contains _ (by omega_using []) (by omega_using [h₂]) (by omega_using [])⟩
  rw [show (savedSlots ++ argSlots).map (fun (r, d) => Instr.store .d r .t0 d) =
    Spill.saveCode .t0 (savedSlots ++ argSlots) from rfl]
  refine Spill.save_ok (by rw [c0]; omega_using [eal]) (fun p hp => slots_fits.1 p hp) (fun p hp => by
    rw [c0]
    have := slots_in p hp
    exact inE _ _ (by omega_using [this])) ?_
  refine wp_mv fun f uf => ?_
  have f3 : f.gpr .s3 = E s₀ := by rw [uf.gpr]; exact c0
  have fmem : f.mem = setupMem s₀ := by
    rw [uf.mem]
    show Spill.saveMem c.mem (c.gpr .t0) c.gpr _ = _
    rw [u₁.mem, c0]
    exact saveMem_congr fun p hp => by rw [cg _ (hl p hp)]
  have frd : f.rd = s₀.rd := by rw [uf.rd]; show c.rd = _; rw [u₁.rd]; rfl
  have fin : InRegions (f.rd ++ f.wr) (E s₀ + BitVec.ofNat 64 (argOff 15)) 8 := by
    have hE := E_hi hp
    refine ⟨argR s₀, List.mem_append_left _ (by rw [frd, hp.rd]; simp), ?_⟩
    rw [argR_eq, show argOff 15 = 376 by decide]
    exact Offset.contains _ (by decide) (by decide) (by omega_using [])
  refine wp_ld (a := E s₀ + BitVec.ofNat 64 (argOff 15)) (by decide) (by rw [f3]; rfl)
    (by rw [show argOff 15 = 376 by decide]; exact Spill.al8 (by omega_using [eal]) (by decide)) fin
    fun g ug => ?_
  rw [fmem, setupMem_arg s₀ (by decide) (by decide)] at ug
  refine wp_addi (imm := 1024) (by decide) fun h₁ uh => wp_addi (imm := 1024) (by decide) fun t ut => ?_
  have nt : ∀ r, r ≠ .s0 → r ≠ .s4 → r ≠ .s3 → r ≠ .t0 → t.gpr r = s₀.gpr r := fun r a b c' d => by
    rw [ut.other _ a, uh.other _ a, ug.other _ b, uf.other _ c']; exact cg r d
  have gs4 : g.gpr .s4 = scrP s₀ := ug.gpr
  refine k t ⟨?_, ?_, ?_, ?_, eal, hp.scr_al, fun r hr => ?_, ?_, ?_, ?_⟩ ?_
  · rw [ut.sp, uh.sp, ug.sp, uf.sp]; show c.sp = _; rw [u₁.sp]; rfl
  · rw [ut.other _ (by decide), uh.other _ (by decide), ug.other _ (by decide), f3]
  · rw [ut.other _ (by decide), uh.other _ (by decide), gs4]
  · rw [ut.gpr, uh.gpr, gs4, BitVec.add_assoc, ← BitVec.ofNat_add]
  · exact nt r (fun e => by subst e; exact absurd hr (by decide))
      (fun e => by subst e; exact absurd hr (by decide))
      (fun e => by subst e; exact absurd hr (by decide))
      (fun e => by subst e; exact absurd hr (by decide))
  · rw [ut.rd, uh.rd, ug.rd, frd]
  · rw [ut.wr, uh.wr, ug.wr, uf.wr]; show c.wr = _; exact cwr
  · rw [ut.mem, uh.mem, ug.mem, fmem]; exact Frame.refl _ _
  · rw [ut.mem, uh.mem, ug.mem, fmem]

end VG.Proof.Argon2.RISCV64.Derive

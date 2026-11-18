module

public import VerifiedGarbage.Impl.CmacTripleDes.Stream.Arm
public import VerifiedGarbage.Impl.StackScratch.Arm
import VerifiedGarbage.Proof.Framework.Arm.RegScratch
import VerifiedGarbage.Proof.Framework.Arm.StackScratch
import VerifiedGarbage.Proof.CmacTripleDes.Arm.RoundLit
import VerifiedGarbage.Proof.TripleDes.SboxTables
public import VerifiedGarbage.Proof.CmacTripleDes.StreamScratch
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.CmacTripleDes.StreamScratch
meta import VerifiedGarbage.Proof.Framework.Arm.ArgTaint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.Arm.Contract
import VerifiedGarbage.Proof.CmacTripleDes.Arm.Lit
public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.CmacTripleDes.Words
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.Arm.Inline
import VerifiedGarbage.Proof.CmacTripleDes.Arm.Update
public import VerifiedGarbage.Proof.CmacTripleDes.Stream
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.Arm.Contract
meta import VerifiedGarbage.Proof.CmacTripleDes.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.CmacTripleDes.Stream.Arm
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.CmacTripleDes.Words
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.Arm.Inline
meta import VerifiedGarbage.Proof.CmacTripleDes.Arm.Update
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.CmacTripleDes.Stream.Arm.Common
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.Arm.Common
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Stream
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.CmacTripleDes.Arm.Init
import VerifiedGarbage.Proof.MdStream.Arm.Common
public import VerifiedGarbage.Proof.Framework.Arm.Spill
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Cmac.Stream
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Cmac.Block
meta import VerifiedGarbage.Proof.CmacTripleDes.Arm.Init
meta import VerifiedGarbage.Proof.MdStream.Arm.Common
meta import VerifiedGarbage.Proof.CmacTripleDes.Arm.RoundLit
meta import VerifiedGarbage.Proof.TripleDes.SboxTables
meta import VerifiedGarbage.Proof.Framework.Arm.Spill
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-! ### `CmacTripleDes.Stream.Arm.Verified`, which only this module used -/

section

/-! ### `CmacTripleDes.Stream.Arm.Implies`, which this module and modules that import it used -/

section

/-!
# Streaming TDEA-CMAC on ARMv7: the shared contracts imply ours

The shared contracts with the working space as an argument
(`Proof/CmacTripleDes/StreamScratch.lean`), which `Frame.lean` moves to the
shared contracts of `Spec/Cmac/TripleDesContract.lean`: with no stack for
`stream_init`, and 4 bytes for `absorb` and `finish` (the stack argument
they push).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.Arm

open VG VG.Arm

/-- A state satisfying `vg_cmac_triple_des_stream_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x3000 | .r2 => 16 | .r3 => 0x4000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x3000, 16⟩]
  wr := [⟨0x1000, 416⟩, ⟨0x4000, 640⟩]

theorem init_implies : initArm.Implies (streamInitScratchContract Arm.abi 0) := by
  sig_implies [streamInitScratchContract, streamInitScratchSig, Spec.Cmac.tdesStreamInitPre,
    Spec.Cmac.tdesStreamInitPost, initArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [initSat] using initSat

/-- A state satisfying `vg_cmac_triple_des_absorb`'s precondition (with no
data): `state` at `0x1000`, `data` at `0x3000`, `scratch` at `0x4000`, the
stack arguments at `0x8000`. -/
def absorbSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x30 else if a = 0x8009 then 0x40 else 0
  rd := [⟨0x3000, 0⟩, ⟨0x8000, 12⟩]
  wr := [⟨0x1000, 416⟩, ⟨0x4000, 688⟩]

theorem absorb_implies : absorbArm.Implies (absorbScratchContract Arm.abi 4) := by
  sig_implies [absorbScratchContract, absorbScratchSig, Spec.Cmac.tdesAbsorbPost, absorbArm, countArm,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [absorbSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using absorbSat

/-- A state satisfying `vg_cmac_triple_des_finish`'s precondition: `state` at
`0x1000`, `out` at `0x2000`, `scratch` at `0x4000`, the stack arguments at
`0x8000`. -/
def finishSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x20 else if a = 0x8005 then 0x40 else 0
  rd := [⟨0x8000, 8⟩]
  wr := [⟨0x1000, 416⟩, ⟨0x2000, 8⟩, ⟨0x4000, 640⟩]

theorem finish_implies : finishArm.Implies (finishScratchContract Arm.abi 4) := by
  sig_implies [finishScratchContract, finishScratchSig, Spec.Cmac.tdesFinishPost, finishArm, countArm,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finishSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using finishSat

end VG.Proof.CmacTripleDes.Stream.Arm

end

end

/-! ### `CmacTripleDes.Stream.Arm.AbsorbCorrect`, which only this module used -/

section

/-! ### `CmacTripleDes.Stream.Arm.Absorb`, which this module and modules that import it used -/

section

/-! ### `CmacTripleDes.Stream.Arm.AbsorbBlocks`, which only this module used -/

section

@[expose] public section

section

/-!
# Streaming TDEA-CMAC on ARMv7: copying bytes

`copy` copies the `r1` bytes at `r6` to `r2`, a byte at a time (none if `r1`
is 0), advancing `r6` past them and taking them off `r7`, and changing only
`r1`, `r2`, `r6`, `r7`, `r12` and the flags.
-/

namespace VG.Proof.CmacTripleDes.Stream.Arm

open VG VG.Arm VG.Impl.CmacTripleDes.Stream.Arm VG.WriteBytes
open VG.Proof.MdStream.Arm (Upd op2_imm op2_reg wp_add wp_sub wp_subs wp_cmp wp_ldrb wp_strb eval_ne
  ofNat_beq_zero sub_ofNat)
open VG.Proof.CmacTripleDes.Arm (byte_rt32)

/-- What `copy` leaves. -/
structure Copied (s : State) (p c : BitVec 32) (L x : Nat) (s' : State) : Prop where
  mem : s'.mem = writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) L)
  r6 : s'.gpr .r6 = p + BitVec.ofNat 32 L
  r7 : s'.gpr .r7 = BitVec.ofNat 32 (x - L)
  other : ∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r6 → r ≠ .r7 → r ≠ .r12 → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- The loop, for `L > 0` bytes. -/
theorem copyLoop_wp {s : State} {p c : BitVec 32} {L : Nat} (hL₀ : 0 < L)
    (h6 : s.gpr .r6 = p) (h2 : s.gpr .r2 = c) (h1 : s.gpr .r1 = BitVec.ofNat 32 L)
    (fp : p.toNat + L ≤ 2 ^ 32) (fc : c.toNat + L ≤ 2 ^ 32)
    (hr : Covers [⟨State.addr p, L⟩] (s.rd ++ s.wr)) (hw : Covers [⟨State.addr c, L⟩] s.wr)
    (hd : (⟨State.addr p, L⟩ : Region).Disjoint ⟨State.addr c, L⟩) :
    WP isa (.loop (.block copyBody) .ne) s fun s' =>
      s'.mem = writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) L) ∧
      s'.gpr .r6 = p + BitVec.ofNat 32 L ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r6 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block copyBody) (c := .ne)
    (fun (n : Nat) (t : State) => ∃ i, n = L - i ∧ i < L ∧ t.gpr .r6 = p + BitVec.ofNat 32 i ∧
      t.gpr .r2 = c + BitVec.ofNat 32 i ∧ t.gpr .r1 = BitVec.ofNat 32 (L - i) ∧
      t.mem = writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) i) ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r6 → r ≠ .r12 → t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (L - 0) _
    ⟨0, rfl, hL₀, by rw [h6]; exact (BitVec.add_zero p).symm, by rw [h2]; exact (BitVec.add_zero c).symm,
      by rw [h1, Nat.sub_zero], by simp [Spec.Aes.bytesAt, writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  rintro n t ⟨i, rfl, hi, x6, x2, x1, mem, g, sp, rd, wr⟩
  obtain aP : State.addr (p + BitVec.ofNat 32 i) = State.addr p + BitVec.ofNat 64 i := addr_add (by omega_arith)
  obtain aC : State.addr (c + BitVec.ofNat 32 i) = State.addr c + BitVec.ofNat 64 i := addr_add (by omega_arith)
  refine wp_ldrb (a := State.addr p + BitVec.ofNat 64 i) (by decide) (by rw [x6, BitVec.add_zero, aP])
    (by rw [rd, wr]; exact hr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    fun t₁ u₁ => ?_
  refine wp_strb (a := State.addr c + BitVec.ofNat 64 i) (by decide)
    (by rw [u₁.other _ (by decide), x2, BitVec.add_zero, aC])
    (by rw [u₁.wr, wr]; exact hw _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    fun t₂ v₂ => ?_
  refine wp_add (op2_imm (by decide)) fun t₃ u₃ => wp_add (op2_imm (by decide)) fun t₄ u₄ =>
    wp_subs (op2_imm (by decide)) fun t₅ u₅ z₅ => WP.block_nil ?_
  obtain hlen : (Spec.Aes.bytesAt s.mem (State.addr p) i).length = i := Proof.Cmac.bytesAt_length _ _ _
  obtain hx : writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) i) (State.addr p + BitVec.ofNat 64 i) =
      s.mem (State.addr p + BitVec.ofNat 64 i) :=
    (writeBytes_frame s.mem (State.addr c) _ (R := ⟨State.addr c, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hd _ (Offset.contains_base _ (by omega_arith) (by omega_arith)) (Region.sub_prefix (by omega_arith) _ hcon)
  obtain hmem : t₅.mem = writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) (i + 1)) := by
    rw [u₅.mem, u₄.mem, u₃.mem, v₂.mem, u₁.gpr, u₁.mem, mem, byte_rt32, hx, Proof.Cmac.bytesAt_succ,
      writeBytes_snoc s.mem _ _ _ (by rw [hlen]; omega_arith), hlen]
  obtain x1' : t₅.gpr .r1 = BitVec.ofNat 32 (L - (i + 1)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), x1,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega_arith)]; rfl
  obtain ev : isa.eval .ne t₅ = some !decide (L - (i + 1) = 0) := by
    show VG.Arm.eval .ne t₅ = _
    rw [eval_ne, z₅, u₄.other _ (by decide), u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), x1,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega_arith), Nat.sub_sub,
      ofNat_beq_zero (by omega_arith)]
  obtain gg : ∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r6 → r ≠ .r12 → t₅.gpr r = s.gpr r := fun r h₁ h₂ h₆ h₁₂ => by
    rw [u₅.other _ h₁, u₄.other _ h₂, u₃.other _ h₆, v₂.gpr, u₁.other _ h₁₂, g r h₁ h₂ h₆ h₁₂]
  obtain x2' : t₅.gpr .r2 = c + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), x2,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  obtain x6' : t₅.gpr .r6 = p + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, v₂.gpr, u₁.other _ (by decide), x6,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  obtain sp' : t₅.sp = s.sp := by rw [u₅.sp, u₄.sp, u₃.sp, v₂.sp, u₁.sp, sp]
  obtain rd' : t₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, v₂.rd, u₁.rd, rd]
  obtain wr' : t₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, v₂.wr, u₁.wr, wr]
  by_cases he : i + 1 = L
  · left
    exact ⟨by rw [ev]; simp [he], by rw [hmem, he], by rw [x6', he], gg, sp', rd', wr'⟩
  · right
    exact ⟨by rw [ev]; simp; omega_arith, L - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, x6', x2', x1', hmem, gg,
      sp', rd', wr'⟩

/-- What copying `L > 0` bytes from `p` to `c` needs. -/
structure CopyOk (s : State) (p c : BitVec 32) (L : Nat) : Prop where
  fp : p.toNat + L ≤ 2 ^ 32
  fc : c.toNat + L ≤ 2 ^ 32
  hr : Covers [⟨State.addr p, L⟩] (s.rd ++ s.wr)
  hw : Covers [⟨State.addr c, L⟩] s.wr
  hd : (⟨State.addr p, L⟩ : Region).Disjoint ⟨State.addr c, L⟩

theorem copy_wp {s : State} {p c : BitVec 32} {L x : Nat} (hLx : L ≤ x) (hx : x < 2 ^ 32)
    (h6 : s.gpr .r6 = p) (h2 : s.gpr .r2 = c) (h1 : s.gpr .r1 = BitVec.ofNat 32 L)
    (h7 : s.gpr .r7 = BitVec.ofNat 32 x) (ok : 0 < L → CopyOk s p c L) :
    WP isa copy s (Copied s p c L x) := by
  refine WP.seq (wp_sub (op2_reg _ _) fun s₁ u₁ => wp_cmp (op2_imm (by decide)) fun s₂ f₂ z₂ => WP.block_nil ?_)
  obtain g₂ : ∀ r, r ≠ .r7 → s₂.gpr r = s.gpr r := fun r hr => by rw [f₂.gpr, u₁.other _ hr]
  obtain r7₂ : s₂.gpr .r7 = BitVec.ofNat 32 (x - L) := by rw [f₂.gpr, u₁.gpr, h7, h1, sub_ofNat hLx]
  rw [show s₁.gpr .r1 = BitVec.ofNat 32 L by rw [u₁.other _ (by decide), h1]] at z₂
  obtain ev := eq_iff s₂ z₂ (by omega_arith)
  obtain sp₂ : s₂.sp = s.sp := by rw [f₂.sp, u₁.sp]
  obtain rd₂ : s₂.rd = s.rd := by rw [f₂.rd, u₁.rd]
  obtain wr₂ : s₂.wr = s.wr := by rw [f₂.wr, u₁.wr]
  obtain m₂ : s₂.mem = s.mem := by rw [f₂.mem, u₁.mem]
  by_cases hL : L = 0
  · subst hL
    refine WP.ite true (by rw [ev]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    exact ⟨by rw [m₂]; simp [Spec.Aes.bytesAt, writeBytes_nil],
      (by rw [g₂ _ (by decide), h6]; exact (BitVec.add_zero p).symm), r7₂, fun r _ _ _ h₇ _ => g₂ r h₇, sp₂, rd₂,
      wr₂⟩
  · obtain ⟨fp, fc, hr, hw, hd⟩ := ok (by omega_arith)
    refine WP.ite false (by rw [ev]; simp [hL]) (fun h => by cases h) fun _ => ?_
    refine WP.mono (copyLoop_wp (by omega_arith) (by rw [g₂ _ (by decide), h6]) (by rw [g₂ _ (by decide), h2])
      (by rw [g₂ _ (by decide), h1]) fp fc (by rw [rd₂, wr₂]; exact hr) (by rw [wr₂]; exact hw) hd)
      fun s' ⟨mm, r6, g, sp, rd, wr⟩ => ⟨by rw [mm, m₂], r6, by rw [g _ (by decide) (by decide) (by decide)
        (by decide), r7₂], fun r h₁ h₂ h₆ h₇ h₁₂ => by rw [g r h₁ h₂ h₆ h₁₂, g₂ r h₇], by rw [sp, sp₂],
        by rw [rd, rd₂], by rw [wr, wr₂]⟩

end VG.Proof.CmacTripleDes.Stream.Arm

end

/-!
# Streaming TDEA-CMAC on ARMv7: `vg_cmac_triple_des_absorb`'s straight-line code

What each piece of code between the copies and calls computes, in terms of
`count` (`c`) and `len` (`L`): the bytes held back `h = held c`, the bytes
copied after them `f = min L (8 - h)`, the data left `L - f`, whether to
chain the block held back (`b1`), the blocks chained after it (`nb`), and the
rest (`rest`).
-/

namespace VG.Proof.CmacTripleDes.Stream.Arm

open VG VG.Arm VG.Impl.CmacTripleDes.Stream.Arm
open VG.Impl.CmacTripleDes.Arm (mov)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsr op2_lsl wp_mov wp_add wp_sub wp_and wp_orr
  wp_cmp cmp0 sub_ofNat ofNat_shr)
open VG.Proof.CmacTripleDes.Stream (held held_le held_zero)

/-! ## The numbers -/

/-- The bytes copied after the `held c` held back. -/
def fOf (c L : Nat) : Nat := min L (8 - held c)

/-- The data left after them. -/
def leftOf (c L : Nat) : Nat := L - fOf c L

/-- The number of blocks the first run of `update` chains: the block held back, if data is left. -/
def b1Of (c L : Nat) : Nat := if leftOf c L = 0 then 0 else 1

/-- The number of whole blocks of `x` bytes but its last 1 to 8 (none for none). -/
def nbx (x : Nat) : Nat := if x = 0 then 0 else (x - 1) / 8

/-- The number of blocks the second run chains: those of the data left but its
last 1 to 8 bytes. -/
def nbOf (c L : Nat) : Nat := nbx (leftOf c L)

/-- The bytes copied to the start of the bytes held back at the end. -/
def restOf (c L : Nat) : Nat := leftOf c L - 8 * nbOf c L

theorem f_le (c L : Nat) : fOf c L ≤ L ∧ fOf c L + held c ≤ 8 := by
  have := held_le c; unfold fOf; omega_arith

theorem nb_le (c L : Nat) : fOf c L + 8 * nbOf c L + restOf c L = L := by
  have := f_le c L; unfold restOf nbOf nbx leftOf; split <;> omega_arith

theorem rest_le (c L : Nat) : restOf c L ≤ 8 := by
  unfold restOf nbOf nbx leftOf; split <;> omega_arith

/-! ## Arithmetic on registers -/

theorem ite_neg' {α : Type} {p : Prop} [Decidable p] {a b : α} (h : ¬p) : (if p then a else b) = b := by
  simp [h]

theorem ite_pos' {α : Type} {p : Prop} [Decidable p] {a b : α} (h : p) : (if p then a else b) = a := by
  simp [h]

theorem shl3 (n : Nat) : BitVec.ofNat 32 n <<< 3 = BitVec.ofNat 32 (8 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

theorem shr3 {a : Nat} (h : a < 2 ^ 32) : BitVec.ofNat 32 a >>> 3 = BitVec.ofNat 32 (a / 8) := ofNat_shr h

/-! ## `held`: the bytes held back -/

theorem held_wp {s : State} {c : Nat} (hc : c < 2 ^ 64)
    (hcnt : (s.gpr .r3 ++ s.gpr .r2 : BitVec 64) = BitVec.ofNat 64 c) :
    WP isa Impl.CmacTripleDes.Stream.Arm.held s fun s' => s'.gpr .r0 = BitVec.ofNat 32 (held c) ∧
      (∀ r, r ≠ .r0 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine WP.seq (wp_sub (op2_imm (by decide)) fun s₁ u₁ => wp_and (op2_imm (by decide)) fun s₂ u₂ =>
    wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_orr (op2_reg _ _) fun s₄ u₄ =>
    wp_cmp (op2_imm (by decide)) fun s₅ f₅ z₅ => WP.block_nil ?_)
  obtain g : ∀ r, r ≠ .r0 → r ≠ .r12 → s₅.gpr r = s.gpr r := fun r a b => by
    rw [f₅.gpr, u₄.other _ b, u₃.other _ a, u₂.other _ a, u₁.other _ a]
  obtain ev : isa.eval .eq s₅ = some (decide (c = 0)) := by
    show VG.Arm.eval .eq s₅ = _
    rw [VG.Proof.MdStream.Arm.eval_eq, z₅, u₄.gpr]
    simp (disch := decide) only [u₃.other, u₂.other, u₁.other]
    exact congrArg some (or_beq_zero hcnt hc)
  obtain r0 : s₅.gpr .r0 = ((s.gpr .r2 - 1) &&& 7) + 1 := by
    rw [f₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.gpr]
  obtain m : s₅.mem = s.mem := by rw [f₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain sp : s₅.sp = s.sp := by rw [f₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  obtain rd : s₅.rd = s.rd := by rw [f₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  obtain wr : s₅.wr = s.wr := by rw [f₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  by_cases h0 : c = 0
  · subst h0
    refine WP.ite true (by rw [ev]; rfl) (fun _ => wp_mov (op2_imm (by decide)) fun t u => WP.block_nil ?_)
      (fun h => by cases h)
    exact ⟨by rw [u.gpr, held_zero]; rfl, fun r a b => by rw [u.other _ a, g r a b], by rw [u.mem, m],
      by rw [u.sp, sp], by rw [u.rd, rd], by rw [u.wr, wr]⟩
  · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => WP.block_nil ?_
    exact ⟨by rw [r0]; exact held_lo hcnt hc h0, g, m, sp, rd, wr⟩

/-! ## `fill`: how many bytes to copy, and where -/

theorem fill_wp {s : State} {St : BitVec 32} {h L : Nat} (hh : h ≤ 8) (hL : L < 2 ^ 32)
    (h0 : s.gpr .r0 = BitVec.ofNat 32 h) (h7 : s.gpr .r7 = BitVec.ofNat 32 L) (h4 : s.gpr .r4 = St) :
    WP isa fill s fun s' => s'.gpr .r1 = BitVec.ofNat 32 (min L (8 - h)) ∧
      s'.gpr .r2 = St + BitVec.ofNat 32 (408 + h) ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_sub (op2_reg _ _) fun s₂ u₂ =>
    wp_mov (op2_lsr (by decide)) fun s₃ u₃ => wp_cmp (op2_imm (by decide)) fun s₄ f₄ z₄ => WP.block_nil ?_)
  obtain g₄ : ∀ r, r ≠ .r1 → r ≠ .r12 → s₄.gpr r = s.gpr r := fun r a b => by
    rw [f₄.gpr, u₃.other _ b, u₂.other _ a, u₁.other _ a]
  obtain r1₄ : s₄.gpr .r1 = BitVec.ofNat 32 (8 - h) := by
    rw [f₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), h0]; exact sub_ofNat hh
  obtain z : s₄.z = (BitVec.ofNat 32 (L / 8) - 0 == 0) := by
    rw [z₄, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h7, shr3 hL]
  obtain ev := eq_iff s₄ z (by omega_arith)
  refine WP.seq (WP.mono (Q := fun (s₅ : State) => s₅.gpr .r1 = BitVec.ofNat 32 (min L (8 - h)) ∧
    (∀ r, r ≠ .r1 → r ≠ .r12 → s₅.gpr r = s.gpr r) ∧ s₅.mem = s.mem ∧ s₅.sp = s.sp ∧ s₅.rd = s.rd ∧
      s₅.wr = s.wr) ?_ ?_)
  · refine WP.mono (Q := fun (s₅ : State) => s₅.gpr .r1 = BitVec.ofNat 32 (min L (8 - h)) ∧
      (∀ r, r ≠ .r1 → r ≠ .r12 → s₅.gpr r = s₄.gpr r) ∧ s₅.mem = s₄.mem ∧ s₅.sp = s₄.sp ∧ s₅.rd = s₄.rd ∧
        s₅.wr = s₄.wr) ?_ fun s₅ ⟨r1, g, m, sp, rd, wr⟩ => ⟨r1, fun r a b => by rw [g r a b, g₄ r a b],
          by rw [m, f₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [sp, f₄.sp, u₃.sp, u₂.sp, u₁.sp],
          by rw [rd, f₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [wr, f₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
    by_cases hl : L / 8 = 0
    · refine WP.ite true (by rw [ev]; simp [hl]) (fun _ => ?_) (fun h => by cases h)
      refine WP.seq (wp_add (op2_reg _ _) fun t₁ v₁ => wp_mov (op2_lsr (by decide)) fun t₂ v₂ =>
        wp_cmp (op2_imm (by decide)) fun t₃ e₃ y₃ => WP.block_nil ?_)
      obtain zz : t₃.z = (BitVec.ofNat 32 ((L + h) / 8) - 0 == 0) := by
        rw [y₃, v₂.gpr, v₁.gpr, g₄ .r7 (by decide) (by decide), g₄ .r0 (by decide) (by decide), h7, h0,
          ← BitVec.ofNat_add, shr3 (by omega_arith)]
      obtain ev' := eq_iff t₃ zz (by omega_arith)
      obtain gt : ∀ r, r ≠ .r12 → t₃.gpr r = s₄.gpr r := fun r a => by rw [e₃.gpr, v₂.other _ a, v₁.other _ a]
      obtain mt : t₃.mem = s₄.mem := by rw [e₃.mem, v₂.mem, v₁.mem]
      obtain spt : t₃.sp = s₄.sp := by rw [e₃.sp, v₂.sp, v₁.sp]
      obtain rdt : t₃.rd = s₄.rd := by rw [e₃.rd, v₂.rd, v₁.rd]
      obtain wrt : t₃.wr = s₄.wr := by rw [e₃.wr, v₂.wr, v₁.wr]
      by_cases hl' : (L + h) / 8 = 0
      · refine WP.ite true (by rw [ev']; simp [hl']) (fun _ => wp_mov (op2_reg _ _) fun t₄ v₄ =>
          WP.block_nil ?_) (fun h => by cases h)
        refine ⟨by rw [v₄.gpr, gt _ (by decide), g₄ _ (by decide) (by decide), h7, Nat.min_eq_left (by omega_arith)],
          fun r a b => by rw [v₄.other _ a, gt _ b], by rw [v₄.mem, mt], by rw [v₄.sp, spt], by rw [v₄.rd, rdt],
          by rw [v₄.wr, wrt]⟩
      · refine WP.ite false (by rw [ev']; simp [hl']) (fun h => by cases h) fun _ => WP.block_nil ?_
        exact ⟨by rw [gt _ (by decide), r1₄, Nat.min_eq_right (by omega_arith)], fun r _ b => gt r b, mt, spt, rdt,
          wrt⟩
    · refine WP.ite false (by rw [ev]; simp [hl]) (fun h => by cases h) fun _ => WP.block_nil ?_
      exact ⟨by rw [r1₄, Nat.min_eq_right (by omega_arith)], fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
  · intro s₅ ⟨r1, g, m, sp, rd, wr⟩
    refine wp_add (op2_reg _ _) fun t₁ v₁ => wp_add (op2_imm (by decide)) fun t₂ v₂ => WP.block_nil ?_
    refine ⟨by rw [v₂.other _ (by decide), v₁.other _ (by decide), r1], ?_,
      fun r a b c => by rw [v₂.other _ b, v₁.other _ b, g r a c], by rw [v₂.mem, v₁.mem, m],
      by rw [v₂.sp, v₁.sp, sp], by rw [v₂.rd, v₁.rd, rd], by rw [v₂.wr, v₁.wr, wr]⟩
    rw [v₂.gpr, v₁.gpr, g _ (by decide) (by decide), g _ (by decide) (by decide), h4, h0, BitVec.add_assoc,
      show (408 : BitVec 32) = BitVec.ofNat 32 408 from rfl, ← BitVec.ofNat_add, Nat.add_comm]

/-! ## `chain1`: the arguments of the first run -/

theorem chain1_wp {s : State} {St : BitVec 32} {x : Nat} (hx : x < 2 ^ 32) (h7 : s.gpr .r7 = BitVec.ofNat 32 x)
    (h4 : s.gpr .r4 = St) :
    WP isa chain1 s fun s' => s'.gpr .r3 = BitVec.ofNat 32 (if x = 0 then 0 else 1) ∧ s'.gpr .r0 = St ∧
      s'.gpr .r1 = St + BitVec.ofNat 32 400 ∧ s'.gpr .r2 = St + BitVec.ofNat 32 408 ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_cmp (op2_imm (by decide)) fun s₂ f₂ z₂ =>
    WP.block_nil ?_)
  obtain ev := eq_iff s₂ (k := x) (by rw [z₂, u₁.other _ (by decide), h7]) hx
  refine WP.seq (WP.mono (Q := fun (s₃ : State) => s₃.gpr .r3 = BitVec.ofNat 32 (if x = 0 then 0 else 1) ∧
    (∀ r, r ≠ .r3 → s₃.gpr r = s.gpr r) ∧ s₃.mem = s.mem ∧ s₃.sp = s.sp ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr) ?_ ?_)
  · have g₂ : ∀ r, r ≠ .r3 → s₂.gpr r = s.gpr r := fun r a => by rw [f₂.gpr, u₁.other _ a]
    by_cases h0 : x = 0
    · refine WP.ite true (by rw [ev]; simp [h0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨by rw [f₂.gpr, u₁.gpr, h0]; rfl, g₂, by rw [f₂.mem, u₁.mem], by rw [f₂.sp, u₁.sp],
        by rw [f₂.rd, u₁.rd], by rw [f₂.wr, u₁.wr]⟩
    · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ =>
        wp_mov (op2_imm (by decide)) fun t u => WP.block_nil ?_
      exact ⟨by rw [u.gpr, ite_neg' h0]; rfl, fun r a => by rw [u.other _ a, g₂ r a],
        by rw [u.mem, f₂.mem, u₁.mem], by rw [u.sp, f₂.sp, u₁.sp], by rw [u.rd, f₂.rd, u₁.rd],
        by rw [u.wr, f₂.wr, u₁.wr]⟩
  · intro s₃ ⟨r3, g, m, sp, rd, wr⟩
    refine wp_mov (op2_reg _ _) fun t₁ v₁ => wp_add (op2_imm (by decide)) fun t₂ v₂ =>
      wp_add (op2_imm (by decide)) fun t₃ v₃ => WP.block_nil ?_
    refine ⟨by simp (disch := decide) only [v₃.other, v₂.other, v₁.other, r3],
      by simp (disch := decide) only [v₃.other, v₂.other, v₁.gpr, g, h4],
      by simp (disch := decide) only [v₃.other, v₂.gpr, v₁.other, g, h4]; rfl,
      by simp (disch := decide) only [v₃.gpr, v₂.other, v₁.other, g, h4]; rfl,
      fun r a b c d => by rw [v₃.other _ c, v₂.other _ b, v₁.other _ a, g r d],
      by rw [v₃.mem, v₂.mem, v₁.mem, m], by rw [v₃.sp, v₂.sp, v₁.sp, sp],
      by rw [v₃.rd, v₂.rd, v₁.rd, rd], by rw [v₃.wr, v₂.wr, v₁.wr, wr]⟩

/-! ## `chain2`: the arguments of the second run -/

theorem chain2_wp {s : State} {St Dd : BitVec 32} {x : Nat} (hx : x < 2 ^ 32) (h7 : s.gpr .r7 = BitVec.ofNat 32 x)
    (h4 : s.gpr .r4 = St) (h6 : s.gpr .r6 = Dd) :
    WP isa chain2 s fun s' => s'.gpr .r3 = BitVec.ofNat 32 (nbx x) ∧
      s'.gpr .r8 = BitVec.ofNat 32 (8 * nbx x) ∧ s'.gpr .r2 = (if x = 0 then St else Dd) ∧
      s'.gpr .r0 = St ∧ s'.gpr .r1 = St + BitVec.ofNat 32 400 ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r8 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.seq (wp_cmp (op2_imm (by decide)) fun s₁ f₁ z₁ => WP.block_nil ?_)
  obtain ev := eq_iff s₁ (k := x) (by rw [z₁, h7]) hx
  refine WP.seq (WP.mono (Q := fun (s₂ : State) => s₂.gpr .r3 = BitVec.ofNat 32 (nbx x) ∧
    s₂.gpr .r8 = BitVec.ofNat 32 (8 * nbx x) ∧ s₂.gpr .r2 = (if x = 0 then St else Dd) ∧
    (∀ r, r ≠ .r2 → r ≠ .r3 → r ≠ .r8 → s₂.gpr r = s.gpr r) ∧ s₂.mem = s.mem ∧ s₂.sp = s.sp ∧ s₂.rd = s.rd ∧
      s₂.wr = s.wr) ?_ ?_)
  · by_cases h0 : x = 0
    · refine WP.ite true (by rw [ev]; simp [h0]) (fun _ => wp_mov (op2_imm (by decide)) fun t₁ v₁ =>
        wp_mov (op2_imm (by decide)) fun t₂ v₂ => wp_mov (op2_reg _ _) fun t₃ v₃ => WP.block_nil ?_)
        (fun h => by cases h)
      refine ⟨by rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr, nbx, ite_pos' h0]; rfl,
        by rw [v₃.other _ (by decide), v₂.gpr, nbx, ite_pos' h0]; rfl,
        by rw [v₃.gpr, v₂.other _ (by decide), v₁.other _ (by decide), f₁.gpr, h4, ite_pos' h0],
        fun r a b c => by rw [v₃.other _ a, v₂.other _ c, v₁.other _ b, f₁.gpr],
        by rw [v₃.mem, v₂.mem, v₁.mem, f₁.mem], by rw [v₃.sp, v₂.sp, v₁.sp, f₁.sp],
        by rw [v₃.rd, v₂.rd, v₁.rd, f₁.rd], by rw [v₃.wr, v₂.wr, v₁.wr, f₁.wr]⟩
    · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ =>
        wp_sub (op2_imm (by decide)) fun t₁ v₁ => wp_mov (op2_lsr (by decide)) fun t₂ v₂ =>
        wp_mov (op2_lsl (by decide)) fun t₃ v₃ => wp_mov (op2_reg _ _) fun t₄ v₄ => WP.block_nil ?_
      obtain e3 : t₂.gpr .r3 = BitVec.ofNat 32 ((x - 1) / 8) := by
        rw [v₂.gpr, v₁.gpr, f₁.gpr, h7, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega_arith),
          shr3 (by omega_arith)]
      refine ⟨by rw [v₄.other _ (by decide), v₃.other _ (by decide), e3, nbx, ite_neg' h0],
        by rw [v₄.other _ (by decide), v₃.gpr, e3, shl3, nbx, ite_neg' h0],
        by rw [v₄.gpr, v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), f₁.gpr, h6,
          ite_neg' h0],
        fun r a b c => by rw [v₄.other _ a, v₃.other _ c, v₂.other _ b, v₁.other _ b, f₁.gpr],
        by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem, f₁.mem], by rw [v₄.sp, v₃.sp, v₂.sp, v₁.sp, f₁.sp],
        by rw [v₄.rd, v₃.rd, v₂.rd, v₁.rd, f₁.rd], by rw [v₄.wr, v₃.wr, v₂.wr, v₁.wr, f₁.wr]⟩
  · intro s₂ ⟨r3, r8, r2, g, m, sp, rd, wr⟩
    refine wp_mov (op2_reg _ _) fun t₁ v₁ => wp_add (op2_imm (by decide)) fun t₂ v₂ => WP.block_nil ?_
    refine ⟨by simp (disch := decide) only [v₂.other, v₁.other, r3],
      by simp (disch := decide) only [v₂.other, v₁.other, r8],
      by simp (disch := decide) only [v₂.other, v₁.other, r2],
      by simp (disch := decide) only [v₂.other, v₁.gpr, g, h4],
      by simp (disch := decide) only [v₂.gpr, v₁.other, g, h4]; rfl,
      fun r a b c d e => by rw [v₂.other _ b, v₁.other _ a, g r c d e],
      by rw [v₂.mem, v₁.mem, m], by rw [v₂.sp, v₁.sp, sp],
      by rw [v₂.rd, v₁.rd, rd], by rw [v₂.wr, v₁.wr, wr]⟩

/-! ## `rest`: the arguments of the last copy -/

theorem rest_wp {s : State} {St P : BitVec 32} {x n : Nat} (hn : 8 * n ≤ x)
    (h6 : s.gpr .r6 = P) (h7 : s.gpr .r7 = BitVec.ofNat 32 x) (h8 : s.gpr .r8 = BitVec.ofNat 32 (8 * n))
    (h4 : s.gpr .r4 = St) :
    WP isa (.block rest) s fun s' => s'.gpr .r6 = P + BitVec.ofNat 32 (8 * n) ∧
      s'.gpr .r7 = BitVec.ofNat 32 (x - 8 * n) ∧ s'.gpr .r1 = BitVec.ofNat 32 (x - 8 * n) ∧
      s'.gpr .r2 = St + BitVec.ofNat 32 408 ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r6 → r ≠ .r7 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine wp_add (op2_reg _ _) fun t₁ v₁ => wp_sub (op2_reg _ _) fun t₂ v₂ => wp_mov (op2_reg _ _) fun t₃ v₃ =>
    wp_add (op2_imm (by decide)) fun t₄ v₄ => WP.block_nil ?_
  obtain r7 : t₂.gpr .r7 = BitVec.ofNat 32 (x - 8 * n) := by
    rw [v₂.gpr, v₁.other _ (by decide), v₁.other _ (by decide), h7, h8, sub_ofNat hn]
  refine ⟨by rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr, h6, h8],
    by rw [v₄.other _ (by decide), v₃.other _ (by decide), r7], by rw [v₄.other _ (by decide), v₃.gpr, r7],
    by rw [v₄.gpr, v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide), h4]; rfl,
    fun r a b c d => by rw [v₄.other _ b, v₃.other _ a, v₂.other _ d, v₁.other _ c],
    by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem], by rw [v₄.sp, v₃.sp, v₂.sp, v₁.sp],
    by rw [v₄.rd, v₃.rd, v₂.rd, v₁.rd], by rw [v₄.wr, v₃.wr, v₂.wr, v₁.wr]⟩

end VG.Proof.CmacTripleDes.Stream.Arm

end

end


/-!
# Streaming TDEA-CMAC on ARMv7: `vg_cmac_triple_des_absorb` up to the first run of `update`

The code saves the registers, computes the bytes held back `h`, copies `f =
min(len, 8 - h)` bytes after them, and sets up the first run of `update`,
which chains the block held back if data is left (`AMid₁`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.Arm

open VG VG.Arm VG.Impl.CmacTripleDes.Stream.Arm VG.WriteBytes
open VG.Impl.CmacTripleDes.Arm (mov)
open VG.Proof.MdStream.Arm (Upd Mupd op2_reg wp_mov wp_ldrSp saveMem saveList_ok saveMem_frame
  readW_writeW_save)
open VG.Arm.Spill (saveMem_congr)
open VG.Proof.CmacTripleDes.Stream (held held_le)

/-- The precondition, by name: the state `St`, the `L` bytes of data at `D`
and the scratch buffer `S`. -/
structure APre (s₀ : State) (St D S : BitVec 32) (L : Nat) : Prop where
  r0 : s₀.gpr .r0 = St
  a0 : stackArg s₀ 0 = D
  a1 : (stackArg s₀ 1).toNat = L
  a2 : stackArg s₀ 2 = S
  rd : s₀.rd = [⟨State.addr D, L⟩, ⟨stackArgAddr s₀ 0, 12⟩]
  wr : s₀.wr = [⟨State.addr St, 416⟩, ⟨State.addr S, 688⟩]
  st_d : (⟨State.addr St, 416⟩ : Region).Disjoint ⟨State.addr D, L⟩
  st_s : (⟨State.addr St, 416⟩ : Region).Disjoint ⟨State.addr S, 688⟩
  d_s : (⟨State.addr D, L⟩ : Region).Disjoint ⟨State.addr S, 688⟩
  a_st : (⟨stackArgAddr s₀ 0, 12⟩ : Region).Disjoint ⟨State.addr St, 416⟩
  a_s : (⟨stackArgAddr s₀ 0, 12⟩ : Region).Disjoint ⟨State.addr S, 688⟩
  b_st : (blw4 s₀).Disjoint ⟨State.addr St, 416⟩
  b_d : (blw4 s₀).Disjoint ⟨State.addr D, L⟩
  b_s : (blw4 s₀).Disjoint ⟨State.addr S, 688⟩
  fSt : St.toNat + 416 ≤ 2 ^ 32
  fD : D.toNat + L ≤ 2 ^ 32
  fS : S.toNat + 688 ≤ 2 ^ 32
  sp : 4 ≤ s₀.sp.toNat
  spf : s₀.sp.toNat + 12 ≤ 2 ^ 32

theorem APre.of {s₀ : State} (h : absorbArm.pre s₀) :
    APre s₀ (s₀.gpr .r0) (stackArg s₀ 0) (stackArg s₀ 2) (stackArg s₀ 1).toNat :=
  let ⟨a, b, c, d, e, f, g, i, j, k, l, m, n, o, p⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, i, j, k, l, m, n, o, p⟩

section
variable {s₀ : State} {St D S : BitVec 32} {L : Nat} (hp : APre s₀ St D S L)
include hp

theorem APre.lt : L < 2 ^ 32 := by rw [← hp.a1]; exact BitVec.isLt _

theorem APre.a1' : stackArg s₀ 1 = BitVec.ofNat 32 L :=
  BitVec.eq_of_toNat_eq (by rw [hp.a1, toNat_ofNat32 hp.lt])

theorem APre.argAddr {k : Nat} (hk : k < 3) : stackArgAddr s₀ k = stackArgAddr s₀ 0 + BitVec.ofNat 64 (4 * k) := by
  have := hp.spf
  simp only [stackArgAddr]
  rw [addr_add (by omega_arith), addr_add (by omega_arith)]
  simp

theorem APre.arg_sub {k : Nat} (hk : k < 3) : Region.Sub ⟨stackArgAddr s₀ k, 4⟩ ⟨stackArgAddr s₀ 0, 12⟩ := by
  rw [hp.argAddr hk]; exact Offset.sub_base _ (by omega_arith)

theorem APre.arg_in {k : Nat} (hk : k < 3) : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ k) 4 := by
  refine ⟨⟨stackArgAddr s₀ 0, 12⟩, by rw [hp.rd]; simp, ?_⟩
  rw [hp.argAddr hk]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)

/-- Offsets in the state. -/
theorem APre.aS {k : Nat} (hk : k < 416) : State.addr (St + BitVec.ofNat 32 k) = State.addr St + BitVec.ofNat 64 k :=
  addr_add (by have := hp.fSt; omega_arith)

theorem APre.inSt {d n : Nat} (h : d + n ≤ 416) :
    Covers [⟨State.addr St + BitVec.ofNat 64 d, n⟩] s₀.wr := by
  rw [hp.wr]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr St, 416⟩, by simp, d, rfl, h⟩

theorem APre.inS {d n : Nat} (h : d + n ≤ 688) :
    Covers [⟨State.addr S + BitVec.ofNat 64 d, n⟩] s₀.wr := by
  rw [hp.wr]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr S, 688⟩, by simp, d, rfl, h⟩

theorem APre.inD {d n : Nat} (h : d + n ≤ L) :
    Covers [⟨State.addr D + BitVec.ofNat 64 d, n⟩] (s₀.rd ++ s₀.wr) := by
  rw [hp.rd, hp.wr]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨State.addr D, L⟩, by simp, d, rfl, h⟩

/-- The arguments of a run of `update` on `n` blocks at `Dd`, from a state
with the permissions and stack of `s₀`. -/
theorem APre.uargs {s : State} {Dd : BitVec 32} {n : Nat} (hr0 : s.gpr .r0 = St)
    (hr1 : s.gpr .r1 = St + BitVec.ofNat 32 400) (hr2 : s.gpr .r2 = Dd) (hr3 : s.gpr .r3 = BitVec.ofNat 32 n)
    (hr10 : s.gpr .r10 = S) (hsp : s.sp = s₀.sp) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hn : 8 * n < 2 ^ 32)
    (hdc : (⟨State.addr Dd, 8 * n⟩ : Region).Disjoint ⟨State.addr St + BitVec.ofNat 64 400, 8⟩)
    (hds : (⟨State.addr Dd, 8 * n⟩ : Region).Disjoint ⟨State.addr S, 688⟩)
    (hbd : (blw4 s₀).Disjoint ⟨State.addr Dd, 8 * n⟩) (hfD : Dd.toNat + 8 * n ≤ 2 ^ 32)
    (hcov : Covers [⟨State.addr Dd, 8 * n⟩] (s₀.rd ++ s₀.wr)) :
    UArgs s St (St + BitVec.ofNat 32 400) Dd S n := by
  have hw := hp.fSt
  obtain a400 := hp.aS (k := 400) (by decide)
  obtain c400 : Region.Sub ⟨State.addr St + BitVec.ofNat 64 400, 8⟩ ⟨State.addr St, 416⟩ :=
    Offset.sub_base _ (by decide)
  obtain hb : blw4 s = blw4 s₀ := by rw [blw4, hsp]
  exact
  { r0 := hr0, r1 := hr1, r2 := hr2, r3 := hr3, r10 := hr10, hn := hn
    hsp := by rw [hsp]; exact hp.sp
    wc := by rw [a400]; exact Offset.base_disjoint _ (by decide) (by omega_arith)
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    dc := by rw [a400]; exact hdc
    ds := hds.sub_right (Region.sub_prefix (by decide))
    cs := by rw [a400]; exact (hp.st_s.sub_left c400).sub_right (Region.sub_prefix (by decide))
    bw := by rw [hb]; exact hp.b_st.sub_right (Region.sub_prefix (by decide))
    bd := by rw [hb]; exact hbd
    bc := by rw [hb, a400]; exact hp.b_st.sub_right c400
    bs := by rw [hb]; exact hp.b_s.sub_right (Region.sub_prefix (by decide))
    fW := by omega_arith
    fC := by rw [toNat_add_ofNat (by omega_arith)]; omega_arith
    fD := hfD
    fS := by have := hp.fS; omega_arith
    reads := by
      rw [hrd, hwr]
      intro a k hi
      obtain ⟨r, hr, hc⟩ := hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Covers.right (hp.inSt (d := 0) (n := 384) (by decide)) a k
          ⟨_, List.mem_singleton_self _, by rw [BitVec.add_zero]; exact hc⟩
      · exact hcov a k ⟨_, List.mem_singleton_self _, hc⟩
    writes := by
      rw [hwr]
      intro a k hi
      obtain ⟨r, hr, hc⟩ := hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [a400] at hc; exact hp.inSt (d := 400) (n := 8) (by decide) a k ⟨_, List.mem_singleton_self _, hc⟩
      · exact hp.inS (d := 0) (n := 640) (by decide) a k
          ⟨_, List.mem_singleton_self _, by rw [BitVec.add_zero]; exact hc⟩ }

end

/-! ## Saving the registers -/

theorem saved_bound : ∀ p ∈ saved, 640 ≤ p.2 ∧ p.2 + 4 ≤ 660 := by decide

theorem saved_ne_r12 : ∀ p ∈ saved, p.1 ≠ .r12 := by decide

theorem save_eq : save = .ldrSp .r12 8 :: (saved.map (fun p => Instr.str p.1 .r12 p.2) ++
    [mov .r4 .r0, .ldrSp .r6 0, .ldrSp .r7 4, mov .r10 .r12]) := rfl

/-- The memory after saving the registers. -/
def aMem (s₀ : State) (S : BitVec 32) : Mem := saveMem s₀.mem (State.addr S) s₀.gpr saved

theorem saved_slots : Spill.Slots 640 660 saved := by decide

theorem aMem_slot (s₀ : State) (S : BitVec 32) {r : Reg} {d : Nat} (h : (r, d) ∈ saved) :
    (aMem s₀ S).readW (State.addr S + BitVec.ofNat 64 d) 32 = s₀.gpr r :=
  Spill.saveMem_saved (State.addr S) s₀.gpr s₀.mem saved saved_slots (r, d) h

theorem aMem_frame (s₀ : State) (S : BitVec 32) : Frame [⟨State.addr S, 688⟩] s₀.mem (aMem s₀ S) :=
  Spill.saveMem_frame _ _ _ (by decide) saved (by decide)

/-- What the saves leave. -/
structure ASave (s₀ : State) (St D S : BitVec 32) (L : Nat) (s : State) : Prop where
  r2 : s.gpr .r2 = s₀.gpr .r2
  r3 : s.gpr .r3 = s₀.gpr .r3
  r4 : s.gpr .r4 = St
  r6 : s.gpr .r6 = D
  r7 : s.gpr .r7 = BitVec.ofNat 32 L
  r10 : s.gpr .r10 = S
  keep : ∀ r ∈ preserved, r ≠ .r4 → r ≠ .r6 → r ≠ .r7 → r ≠ .r10 → s.gpr r = s₀.gpr r
  mem : s.mem = aMem s₀ S
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem save_wp {s₀ : State} {St D S : BitVec 32} {L : Nat} (hp : APre s₀ St D S L) :
    WP isa (.block save) s₀ (ASave s₀ St D S L) := by
  have hS := hp.fS
  rw [save_eq]
  refine wp_ldrSp (a := stackArgAddr s₀ 2) (by decide) rfl (hp.arg_in (by decide)) fun s₁ u₁ => ?_
  obtain h12 : s₁.gpr .r12 = S := by rw [u₁.gpr]; exact hp.a2
  refine saveList_ok saved s₁ _ (fun p hp' => ?_) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  · have := saved_bound p hp'
    rw [h12, u₁.wr, hp.wr]
    exact ⟨by omega_arith, by omega_arith, ⟨⟨State.addr S, 688⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩⟩
  obtain hm₂ : s₂.mem = aMem s₀ S := by
    rw [m₂, u₁.mem, h12, aMem]
    exact saveMem_congr _ _ _ fun p hp' => u₁.other _ (saved_ne_r12 p hp')
  have arg (k : Nat) (hk : k < 3) : (aMem s₀ S).readW (stackArgAddr s₀ k) 32 = stackArg s₀ k :=
    (aMem_frame s₀ S).readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.a_s.sub_left (hp.arg_sub hk)) (by decide)
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) (by rw [u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]; exact hp.arg_in (by decide)) fun s₅ u₅ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) (by rw [u₅.sp, u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₅.rd, u₅.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]; exact hp.arg_in (by decide))
    fun s₆ u₆ => wp_mov (op2_reg _ _) fun s₇ u₇ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr a b c d => ?_, ?_, ?_, ?_, ?_⟩
  · simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₃.other, g₂, u₁.other]
  · simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₃.other, g₂, u₁.other]
  · simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₃.gpr, g₂, u₁.other, hp.r0]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₃.mem, hm₂, arg 0 (by decide), hp.a0]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, u₃.mem, hm₂, arg 1 (by decide), hp.a1']
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₃.other _ (by decide), g₂, h12]
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl a
    | exact absurd rfl b
    | exact absurd rfl c
    | exact absurd rfl d
    | simp (disch := decide) only [u₇.other, u₆.other, u₅.other, u₃.other, g₂, u₁.other]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₃.mem, hm₂]
  · rw [u₇.sp, u₆.sp, u₅.sp, u₃.sp, sp₂, u₁.sp]
  · rw [u₇.rd, u₆.rd, u₅.rd, u₃.rd, rd₂, u₁.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, u₃.wr, wr₂, u₁.wr]

/-! ## Up to the first run of `update` -/

/-- The memory after the saves and the first copy. -/
def m4 (s₀ : State) (St D S : BitVec 32) (c L : Nat) : Mem :=
  writeBytes (aMem s₀ S) (State.addr (St + BitVec.ofNat 32 (408 + held c)))
    (Spec.Aes.bytesAt (aMem s₀ S) (State.addr D) (fOf c L))

/-- What the code before the first run of `update` leaves. -/
structure AMid₁ (s₀ : State) (St D S : BitVec 32) (L : Nat) (s : State) : Prop where
  args : UArgs s St (St + BitVec.ofNat 32 400) (St + BitVec.ofNat 32 408) S (b1Of (countArm s₀).toNat L)
  r4 : s.gpr .r4 = St
  r6 : s.gpr .r6 = D + BitVec.ofNat 32 (fOf (countArm s₀).toNat L)
  r7 : s.gpr .r7 = BitVec.ofNat 32 (leftOf (countArm s₀).toNat L)
  r10 : s.gpr .r10 = S
  sp : s.sp = s₀.sp
  keep : ∀ r ∈ preserved, r ≠ .r4 → r ≠ .r6 → r ≠ .r7 → r ≠ .r10 → s.gpr r = s₀.gpr r
  mem : s.mem = m4 s₀ St D S (countArm s₀).toNat L
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem absorbPre_wp {s₀ : State} {St D S : BitVec 32} {L : Nat} (hp : APre s₀ St D S L) :
    WP isa absorbPre s₀ (AMid₁ s₀ St D S L) := by
  generalize hc : (countArm s₀).toNat = c
  obtain hcl : c < 2 ^ 64 := by rw [← hc]; exact BitVec.isLt _
  have hL := hp.lt
  have hw := hp.fSt
  have hD := hp.fD
  have ⟨hfL, hfh⟩ := f_le c L
  obtain hh := held_le c
  refine WP.seq (WP.mono (save_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (held_wp (c := c) hcl (by rw [h₁.r3, h₁.r2, count_eq, hc]))
    fun s₂ ⟨r0₂, g₂, m₂, sp₂, rd₂, wr₂⟩ => ?_)
  refine WP.seq (WP.mono (fill_wp (St := St) (held_le c) hL r0₂ (by rw [g₂ _ (by decide) (by decide), h₁.r7])
    (by rw [g₂ _ (by decide) (by decide), h₁.r4])) fun s₃ ⟨r1₃, r2₃, g₃, m₃, sp₃, rd₃, wr₃⟩ => ?_)
  have g (r : Reg) (a : r ≠ .r0) (b : r ≠ .r1) (c : r ≠ .r2) (d : r ≠ .r12) : s₃.gpr r = s₁.gpr r := by
    rw [g₃ r b c d, g₂ r a d]
  obtain rd₃' : s₃.rd = s₀.rd := by rw [rd₃, rd₂, h₁.rd]
  obtain wr₃' : s₃.wr = s₀.wr := by rw [wr₃, wr₂, h₁.wr]
  refine WP.seq (WP.mono (copy_wp (p := D) (c := St + BitVec.ofNat 32 (408 + held c)) (L := fOf c L) (x := L)
    hfL hL (by rw [g _ (by decide) (by decide) (by decide) (by decide), h₁.r6]) r2₃ (by rw [r1₃]; rfl)
    (by rw [g _ (by decide) (by decide) (by decide) (by decide), h₁.r7]) fun hpos => ?_) fun s₄ h₄ => ?_)
  · have hlt : 408 + held c < 416 := by unfold fOf at hpos; omega_arith
    obtain aDst' : State.addr (St + BitVec.ofNat 32 (408 + held c)) = State.addr St + BitVec.ofNat 64 (408 + held c) :=
      hp.aS hlt
    exact
    { fp := by omega_arith
      fc := by rw [toNat_add_ofNat (by omega_arith)]; omega_arith
      hr := by
        rw [rd₃', wr₃']
        have := hp.inD (d := 0) (n := fOf c L) (by omega_arith)
        rwa [BitVec.add_zero] at this
      hw := by rw [wr₃', aDst']; exact hp.inSt (by omega_arith)
      hd := by
        rw [aDst']
        exact (hp.st_d.sub_left (Offset.sub_base _ (by omega_arith))).symm.sub_left (Region.sub_prefix hfL) }
  have g' (r : Reg) (a : r ≠ .r0) (b : r ≠ .r1) (c : r ≠ .r2) (d : r ≠ .r12) (e : r ≠ .r6) (f : r ≠ .r7) :
      s₄.gpr r = s₁.gpr r := by rw [h₄.other r b c e f d, g r a b c d]
  refine WP.mono (chain1_wp (x := leftOf c L) (by unfold leftOf; omega_arith) (by rw [h₄.r7]; rfl)
    (by rw [g' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₁.r4])) fun s₅ h₅ => ?_
  obtain ⟨r3₅, r0₅, r1₅, r2₅, g₅, m₅, sp₅, rd₅, wr₅⟩ := h₅
  have k (r : Reg) (a : r ≠ .r0) (b : r ≠ .r1) (c : r ≠ .r2) (d : r ≠ .r3) (f : r ≠ .r12) (i : r ≠ .r6)
      (j : r ≠ .r7) : s₅.gpr r = s₁.gpr r := by rw [g₅ r a b c d, g' r a b c f i j]
  obtain hrd : s₅.rd = s₀.rd := by rw [rd₅, h₄.rd, rd₃']
  obtain hwr : s₅.wr = s₀.wr := by rw [wr₅, h₄.wr, wr₃']
  obtain hsp : s₅.sp = s₀.sp := by rw [sp₅, h₄.sp, sp₃, sp₂, h₁.sp]
  obtain hb1 : 8 * b1Of c L ≤ 8 := by unfold b1Of; split <;> omega_arith
  obtain a408 := hp.aS (k := 408) (by decide)
  obtain c408 : Region.Sub ⟨State.addr (St + BitVec.ofNat 32 408), 8 * b1Of c L⟩ ⟨State.addr St, 416⟩ := by
    rw [a408]; exact Offset.sub_base _ (by omega_arith)
  subst hc
  refine ⟨hp.uargs (Dd := St + BitVec.ofNat 32 408) r0₅ r1₅ r2₅
      (by rw [r3₅, b1Of, leftOf]) (by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), h₁.r10]) hsp hrd hwr (by omega_arith)
      (by rw [a408]; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))
      ((hp.st_s.sub_left c408))
      (hp.b_st.sub_right c408) (by rw [toNat_add_ofNat (by omega_arith)]; omega_arith)
      (Covers.right (by rw [a408]; exact hp.inSt (by omega_arith))), ?_, ?_, ?_, ?_, hsp, ?_, ?_, hrd, hwr⟩
  · rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₁.r4]
  · rw [g₅ _ (by decide) (by decide) (by decide) (by decide), h₄.r6]
  · rw [g₅ _ (by decide) (by decide) (by decide) (by decide), h₄.r7]; rfl
  · rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h₁.r10]
  · intro r hr a b c d
    have : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [k r this.1 this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2 b c, h₁.keep r hr a b c d]
  · rw [m₅, h₄.mem, m₃, m₂, h₁.mem, m4]

end VG.Proof.CmacTripleDes.Stream.Arm

end

end

/-!
# Streaming TDEA-CMAC on ARMv7: `vg_cmac_triple_des_absorb` is correct

After `absorbPre`, the first run of `update` chains the block held back if
data is left (`b1`), the second the whole blocks of the data left but its
last 1 to 8 bytes (`nb`), and the last copy holds those back. If no data is
left (`len ≤ 8 - h`), the runs chain nothing and the copy copies nothing,
and the data is appended to the bytes held back (`repr_fill`); otherwise
`repr_chain`.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.Arm

open VG VG.Arm VG.Impl.CmacTripleDes.Stream.Arm VG.WriteBytes
open VG.Proof.CmacTripleDes.Stream (held held_le)
open VG.Proof.CmacTripleDes.Arm (scheduleAt_frame)

theorem disjoint_zero (p : Addr) (r : Region) : (⟨p, 0⟩ : Region).Disjoint r := fun a h _ => by
  simp only [Region.Contains] at h; omega_using [h]

theorem blocksAt_zero (m : Mem) (p : Addr) : Spec.Cmac.blocksAt m p 8 0 = [] := rfl

theorem blocksAt_one (m : Mem) (p : Addr) :
    Spec.Cmac.blocksAt m p 8 1 = [Spec.Aes.bytesAt m p 8] := by
  simp [Spec.Cmac.blocksAt]

/-- The data of the second run of `update`: the state if no data is left. -/
abbrev d2Of (St D : BitVec 32) (c L : Nat) : BitVec 32 :=
  if leftOf c L = 0 then St else D + BitVec.ofNat 32 (fOf c L)

/-- What the first run of `update` leaves, for `chain2`. -/
structure AAfter₁ (s₀ : State) (St D S : BitVec 32) (L : Nat) (s : State) : Prop where
  r4 : s.gpr .r4 = St
  r6 : s.gpr .r6 = D + BitVec.ofNat 32 (fOf (countArm s₀).toNat L)
  r7 : s.gpr .r7 = BitVec.ofNat 32 (leftOf (countArm s₀).toNat L)
  r10 : s.gpr .r10 = S
  keep : ∀ r ∈ preserved, r ≠ .r4 → r ≠ .r6 → r ≠ .r7 → r ≠ .r10 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem AMid₁.after {s₀ s s' : State} {St D S : BitVec 32} {L : Nat} (h : AMid₁ s₀ St D S L s)
    (h₆ : UPost s St (St + BitVec.ofNat 32 400) (St + BitVec.ofNat 32 408) S (b1Of (countArm s₀).toNat L) s') :
    AAfter₁ s₀ St D S L s' :=
  ⟨by rw [h₆.saved _ (by simp [preserved]), h.r4], by rw [h₆.saved _ (by simp [preserved]), h.r6],
    by rw [h₆.saved _ (by simp [preserved]), h.r7], by rw [h₆.saved _ (by simp [preserved]), h.r10],
    fun r hr a b c d => by rw [h₆.saved r hr, h.keep r hr a b c d], by rw [h₆.sp, h.sp], by rw [h₆.rd, h.rd],
    by rw [h₆.wr, h.wr]⟩

theorem upd1_after {s₀ s : State} {St D S : BitVec 32} {L : Nat} (h : AMid₁ s₀ St D S L s) :
    WP isa updFrame s (AAfter₁ s₀ St D S L) :=
  WP.mono (upd_wp h.args) fun _ h₆ => h.after h₆

/-- What `chain2` leaves, for the second run of `update`. -/
structure AMid₂ (s₀ : State) (St D S : BitVec 32) (L : Nat) (m : Mem) (s : State) : Prop where
  mem : s.mem = m
  args : UArgs s St (St + BitVec.ofNat 32 400) (d2Of St D (countArm s₀).toNat L) S (nbOf (countArm s₀).toNat L)
  r4 : s.gpr .r4 = St
  r6 : s.gpr .r6 = D + BitVec.ofNat 32 (fOf (countArm s₀).toNat L)
  r7 : s.gpr .r7 = BitVec.ofNat 32 (leftOf (countArm s₀).toNat L)
  r8 : s.gpr .r8 = BitVec.ofNat 32 (8 * nbOf (countArm s₀).toNat L)
  r10 : s.gpr .r10 = S
  keep : ∀ r ∈ preserved, r ≠ .r4 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → r ≠ .r10 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem chain2_mid {s₀ s : State} {St D S : BitVec 32} {L : Nat} (hp : APre s₀ St D S L)
    (h : AAfter₁ s₀ St D S L s) : WP isa chain2 s (AMid₂ s₀ St D S L s.mem) := by
  have hL := hp.lt
  have hD := hp.fD
  have hw := hp.fSt
  have ⟨hfL, _⟩ := f_le (countArm s₀).toNat L
  obtain hsum := nb_le (countArm s₀).toNat L
  refine WP.mono (chain2_wp (x := leftOf (countArm s₀).toNat L) (by unfold leftOf; omega_using [hL]) h.r7 h.r4
    h.r6) fun s₇ h₇ => ?_
  obtain ⟨r3₇, r8₇, r2₇, r0₇, r1₇, g₇, m₇, sp₇, rd₇, wr₇⟩ := h₇
  have k (r : Reg) (a : r ≠ .r0) (b : r ≠ .r1) (c : r ≠ .r2) (d : r ≠ .r3) (e : r ≠ .r8) :
      s₇.gpr r = s.gpr r := g₇ r a b c d e
  obtain hsp : s₇.sp = s₀.sp := by rw [sp₇, h.sp]
  obtain hrd : s₇.rd = s₀.rd := by rw [rd₇, h.rd]
  obtain hwr : s₇.wr = s₀.wr := by rw [wr₇, h.wr]
  refine ⟨m₇, ?_, by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r4],
    by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r6],
    by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r7], r8₇,
    by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r10],
    fun r hr a b c d e => ?_, hsp, hrd, hwr⟩
  rotate_left
  · have : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [k r this.1 this.2.1 this.2.2.1 this.2.2.2 d, h.keep r hr a b c e]
  obtain common := @APre.uargs _ _ _ _ _ hp s₇ (d2Of St D (countArm s₀).toNat L) (nbOf (countArm s₀).toNat L) r0₇
    r1₇ r2₇ r3₇ (by rw [k _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r10]) hsp hrd hwr
  by_cases h0 : leftOf (countArm s₀).toNat L = 0
  · have hn : nbOf (countArm s₀).toNat L = 0 := by simp [nbOf, nbx, h0]
    simp only [d2Of, h0, ↓reduceIte, hn, Nat.mul_zero] at common ⊢
    refine common (by decide) (disjoint_zero _ _) (disjoint_zero _ _) ((disjoint_zero _ _).symm) (by omega_using [])
      (Covers.right (by have := hp.inSt (d := 0) (n := 0) (by decide); rwa [BitVec.add_zero] at this))
  · simp only [d2Of, h0, ↓reduceIte] at common ⊢
    obtain hn : 8 * nbOf (countArm s₀).toNat L < leftOf (countArm s₀).toNat L := by
      simp only [nbOf, nbx, h0, ↓reduceIte]; omega_using [h0]
    obtain aD : State.addr (D + BitVec.ofNat 32 (fOf (countArm s₀).toNat L)) =
        State.addr D + BitVec.ofNat 64 (fOf (countArm s₀).toNat L) :=
      addr_add (by unfold leftOf at h0; omega_using [hD, h0])
    obtain dD : Region.Sub ⟨State.addr D + BitVec.ofNat 64 (fOf (countArm s₀).toNat L),
        8 * nbOf (countArm s₀).toNat L⟩ ⟨State.addr D, L⟩ :=
      Offset.sub_base _ (by unfold leftOf at hn; omega_using [hn])
    rw [aD] at common
    refine common (by omega_using [hL, hsum]) ((hp.st_d.sub_left (Offset.sub_base _ (by decide))).symm.sub_left dD)
      (hp.d_s.sub_left dD) (hp.b_d.sub_right dD)
      (by rw [toNat_add_ofNat (by unfold leftOf at h0; omega_using [hD, h0])]; unfold leftOf at hn
          omega_using [hD, hn])
      (hp.inD (by unfold leftOf at hn; omega_using [hn]))

/-- What the second run of `update` leaves, for `absorbPost`. -/
structure AAfter₂ (s₀ : State) (St D S : BitVec 32) (L : Nat) (s : State) : Prop where
  r4 : s.gpr .r4 = St
  r6 : s.gpr .r6 = D + BitVec.ofNat 32 (fOf (countArm s₀).toNat L)
  r7 : s.gpr .r7 = BitVec.ofNat 32 (leftOf (countArm s₀).toNat L)
  r8 : s.gpr .r8 = BitVec.ofNat 32 (8 * nbOf (countArm s₀).toNat L)
  r10 : s.gpr .r10 = S
  keep : ∀ r ∈ preserved, r ≠ .r4 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → r ≠ .r10 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem AMid₂.after {s₀ s s' : State} {St D S : BitVec 32} {L : Nat} {m : Mem} (h : AMid₂ s₀ St D S L m s)
    (h₈ : UPost s St (St + BitVec.ofNat 32 400) (d2Of St D (countArm s₀).toNat L) S (nbOf (countArm s₀).toNat L) s') :
    AAfter₂ s₀ St D S L s' :=
  ⟨by rw [h₈.saved _ (by simp [preserved]), h.r4], by rw [h₈.saved _ (by simp [preserved]), h.r6],
    by rw [h₈.saved _ (by simp [preserved]), h.r7], by rw [h₈.saved _ (by simp [preserved]), h.r8],
    by rw [h₈.saved _ (by simp [preserved]), h.r10],
    fun r hr a b c d e => by rw [h₈.saved r hr, h.keep r hr a b c d e], by rw [h₈.sp, h.sp],
    by rw [h₈.rd, h.rd], by rw [h₈.wr, h.wr]⟩

theorem upd2_after {s₀ s : State} {St D S : BitVec 32} {L : Nat} {m : Mem} (h : AMid₂ s₀ St D S L m s) :
    WP isa updFrame s (AAfter₂ s₀ St D S L) :=
  WP.mono (upd_wp h.args) fun _ h₈ => h.after h₈

theorem saved_eq : saved = saved.take 4 ++ [(.r10, 656)] := rfl

theorem absorb_wp {s₀ : State} (h0 : absorbArm.pre s₀) :
    WP isa absorb s₀ fun s' => abiPreserved s₀ s' ∧ absorbArm.post s₀ s' := by
  obtain hp := APre.of h0
  generalize s₀.gpr .r0 = St at hp
  generalize stackArg s₀ 0 = D at hp
  generalize stackArg s₀ 2 = S at hp
  generalize (stackArg s₀ 1).toNat = L at hp
  have hL := hp.lt
  have hw := hp.fSt
  have hsw := hp.fS
  have hD := hp.fD
  refine WP.seq (WP.mono (absorbPre_wp hp) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (upd_wp h₅.args) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (chain2_mid hp (h₅.after h₆)) fun s₇ h₇ => ?_)
  refine WP.seq (WP.mono (upd_wp h₇.args) fun s₈ h₈ => ?_)
  obtain ⟨c, hc⟩ : ∃ c, (countArm s₀).toNat = c := ⟨_, rfl⟩
  have ⟨hfL, hfh⟩ := f_le c L
  obtain hsum := nb_le c L
  obtain hrr := rest_le c L
  obtain hh := held_le c
  obtain ⟨r4₈, r6₈, r7₈, r8₈, r10₈, keep₈, sp₈, rd₈, wr₈⟩ := h₇.after h₈
  rw [hc] at r6₈ r7₈ r8₈
  refine WP.seq (WP.mono (rest_wp (St := St) (x := leftOf c L) (n := nbOf c L) (by unfold leftOf; omega_using [hsum])
    r6₈ r7₈ r8₈ r4₈) fun s₉ h₉ => ?_)
  obtain ⟨r6₉, r7₉, r1₉, r2₉, g₉, m₉, sp₉, rd₉, wr₉⟩ := h₉
  have restEq : leftOf c L - 8 * nbOf c L = restOf c L := rfl
  rw [restEq] at r7₉ r1₉
  obtain rd₉' : s₉.rd = s₀.rd := by rw [rd₉, rd₈]
  obtain wr₉' : s₉.wr = s₀.wr := by rw [wr₉, wr₈]
  obtain a408 := hp.aS (k := 408) (by decide)
  refine WP.seq (WP.mono (copy_wp (p := D + BitVec.ofNat 32 (fOf c L) + BitVec.ofNat 32 (8 * nbOf c L))
    (c := St + BitVec.ofNat 32 408) (L := restOf c L) (x := restOf c L) (Nat.le_refl _) (by omega_using [hrr])
    r6₉ r2₉ r1₉ r7₉ fun hpos => ?_) fun s₁₀ h₁₀ => ?_)
  · have aP : State.addr (D + BitVec.ofNat 32 (fOf c L) + BitVec.ofNat 32 (8 * nbOf c L)) =
        State.addr D + BitVec.ofNat 64 (fOf c L + 8 * nbOf c L) := by
      rw [add_ofNat32]; exact addr_add (by omega_using [hD, hsum, hpos])
    exact
    { fp := by rw [add_ofNat32, toNat_add_ofNat (by omega_using [hD, hsum, hpos])]; omega_using [hD, hsum]
      fc := by rw [toNat_add_ofNat (by omega_using [hw])]; omega_using [hw, hrr]
      hr := by rw [rd₉', wr₉', aP]; exact hp.inD (by omega_using [hsum])
      hw := by rw [wr₉', a408]; exact hp.inSt (by omega_using [hrr])
      hd := by
        rw [aP, a408]
        exact (hp.st_d.sub_left (Offset.sub_base _ (by omega_using [hrr]))).symm.sub_left
          (Offset.sub_base _ (by omega_using [hsum])) }
  obtain r10₁₀ : s₁₀.gpr .r10 = S := by
    rw [h₁₀.other _ (by decide) (by decide) (by decide) (by decide) (by decide),
      g₉ _ (by decide) (by decide) (by decide) (by decide), r10₈]
  obtain inS : ∀ d, d + 4 ≤ 688 → InRegions (s₁₀.rd ++ s₁₀.wr) (State.addr S + BitVec.ofNat 64 d) 4 :=
    fun d hd => by
      rw [h₁₀.rd, h₁₀.wr, rd₉', wr₉']
      exact Covers.right (hp.inS hd) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  rw [restore, saved_eq, ← List.append_nil (List.map _ _)]
  refine Spill.restoreBase_ok (by decide) (fun p hp' => ?_) fun s₁₂ ld₁₂ ho₁₂ m₁₂ _ _ sp₁₂ => WP.block_nil ?_
  · have hb := saved_bound p (by rw [saved_eq]; exact hp')
    exact ⟨by omega_using [hb], by rw [r10₁₀]; omega_using [hsw, hb], by rw [r10₁₀]; exact inS _ (by omega_using [hb])⟩
  -- The frames.
  obtain hm5 : s₅.mem = m4 s₀ St D S c L := by rw [h₅.mem, hc]
  obtain hlr : (Spec.Aes.bytesAt s₉.mem (State.addr (D + BitVec.ofNat 32 (fOf c L) + BitVec.ofNat 32 (8 * nbOf c L)))
      (restOf c L)).length = restOf c L := Proof.Cmac.bytesAt_length _ _ _
  obtain fS : Frame [⟨State.addr S, 688⟩] s₀.mem (aMem s₀ S) := aMem_frame _ _
  obtain fC1 : Frame [⟨State.addr St + BitVec.ofNat 64 408, 8⟩] (aMem s₀ S) s₅.mem := by
    rw [hm5, m4]
    by_cases hf0 : fOf c L = 0
    · rw [hf0, show Spec.Aes.bytesAt (aMem s₀ S) (State.addr D) 0 = [] from rfl, writeBytes_nil]
      exact Frame.refl _ _
    · have hlt : 408 + held c < 416 := by unfold fOf at hf0; omega_using [hf0]
      refine writeBytes_frame _ _ _ ?_
      rw [Proof.Cmac.bytesAt_length, hp.aS hlt]
      exact Offset.contains (State.addr St) (d := 408 + held c) (n := fOf c L) (e := 408) (k := 8) (by omega_using [])
        (by omega_using [hfh]) (by omega_using [])
  obtain hb5 : blw4 s₅ = blw4 s₀ := by rw [blw4, h₅.sp]
  obtain hb7 : blw4 s₇ = blw4 s₀ := by rw [blw4, h₇.sp]
  obtain f6 : Frame [⟨State.addr (St + BitVec.ofNat 32 400), 8⟩, ⟨State.addr S, 640⟩, blw4 s₀] s₅.mem s₆.mem := by
    have := h₆.frame; rwa [hb5] at this
  obtain f8 : Frame [⟨State.addr (St + BitVec.ofNat 32 400), 8⟩, ⟨State.addr S, 640⟩, blw4 s₀] s₆.mem s₈.mem := by
    have := h₈.frame; rwa [hb7, h₇.mem] at this
  obtain fC2 : Frame [⟨State.addr St + BitVec.ofNat 64 408, 8⟩] s₈.mem s₁₀.mem := by
    rw [h₁₀.mem, m₉]
    refine writeBytes_frame _ _ _ ?_
    rw [← m₉, hlr, a408]
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using [hrr]
  let K : List Region := [⟨State.addr S, 688⟩, ⟨State.addr St + BitVec.ofNat 64 408, 8⟩,
    ⟨State.addr (St + BitVec.ofNat 32 400), 8⟩, ⟨State.addr S, 640⟩, blw4 s₀]
  obtain F5 : Frame K s₀.mem s₅.mem := (fS.mono (by simp [K])).trans (fC1.mono (by simp [K]))
  obtain F6 : Frame K s₀.mem s₆.mem := F5.trans (f6.mono (by simp [K]))
  obtain F8 : Frame K s₀.mem s₈.mem := F6.trans (f8.mono (by simp [K]))
  obtain F10 : Frame K s₀.mem s₁₀.mem := F8.trans (fC2.mono (by simp [K]))
  obtain a400 := hp.aS (k := 400) (by decide)
  refine ⟨⟨fun r hr => ?_, by rw [sp₁₂, h₁₀.sp, sp₉, sp₈]⟩, ?_⟩
  · -- The registers, restored from their slots.
    obtain Fp : Frame K.tail (aMem s₀ S) s₁₀.mem :=
      ((fC1.mono (by simp [K])).trans (f6.mono (by simp [K]))).trans
        ((f8.mono (by simp [K])).trans (fC2.mono (by simp [K])))
    have slot (d : Nat) (h₁ : 640 ≤ d) (h₂ : d + 4 ≤ 660) :
        s₁₀.mem.readW (State.addr S + BitVec.ofNat 64 d) 32 =
          (aMem s₀ S).readW (State.addr S + BitVec.ofNat 64 d) 32 := by
      obtain sub : Region.Sub ⟨State.addr S + BitVec.ofNat 64 d, 4⟩ ⟨State.addr S, 688⟩ :=
        Offset.sub_base _ (by omega_using [h₂])
      refine Fp.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [K, List.tail_cons, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (hp.st_s.sub_left (Offset.sub_base _ (by decide))).symm.sub_left sub
      · rw [a400]; exact (hp.st_s.sub_left (Offset.sub_base _ (by decide))).symm.sub_left sub
      · exact Offset.disjoint_base _ (by omega_using [h₁]) (by omega_using [h₂])
      · exact hp.b_s.symm.sub_left sub
    by_cases hs : r ∈ saved.map Prod.fst
    · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hs
      obtain hb := saved_bound _ hp'
      rw [ld₁₂ p (by rw [← saved_eq]; exact hp'), r10₁₀, slot p.2 hb.1 hb.2, aMem_slot s₀ S hp']
    · have hk : ∀ r ∈ preserved, r ∉ saved.map Prod.fst →
          r ≠ .r4 ∧ r ≠ .r6 ∧ r ≠ .r7 ∧ r ≠ .r8 ∧ r ≠ .r10 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r12 := by decide
      obtain ⟨a, b, c, d, e, f, g, i⟩ := hk r hr hs
      rw [ho₁₂ _ hs, h₁₀.other _ f g b c i, g₉ _ f g b c, keep₈ r hr a b c d e]
  · intro key msg hr hcnt hlen
    rw [hp.r0] at hr ⊢
    rw [hp.a0, hp.a1, m₁₂]
    rw [hp.a1] at hlen
    obtain hcm : c = msg.length := by rw [← hc, hcnt, toNat_ofNat64 (by omega_using [hlen])]
    subst hcm
    obtain hsch := ((Proof.CmacTripleDes.Stream.repr_iff _ _ _ _).mp hr).1.2.1
    -- The key and the data are in none of the regions written.
    obtain dK : ∀ r ∈ K, (⟨State.addr St, 400⟩ : Region).Disjoint r := by
      intro r hr
      simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact hp.st_s.sub_left (Region.sub_prefix (by decide))
      · exact Offset.base_disjoint _ (by decide) (by decide)
      · rw [a400]; exact Offset.base_disjoint _ (by decide) (by decide)
      · exact (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
      · exact (hp.b_st.sub_right (Region.sub_prefix (by decide))).symm
    obtain dDat : ∀ r ∈ K, (⟨State.addr D, L⟩ : Region).Disjoint r := by
      intro r hr
      simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact hp.d_s
      · exact hp.st_d.symm.sub_right (Offset.sub_base _ (by decide))
      · rw [a400]; exact hp.st_d.symm.sub_right (Offset.sub_base _ (by decide))
      · exact hp.d_s.sub_right (Region.sub_prefix (by decide))
      · exact hp.b_d.symm
    obtain ciph : ∀ m : Mem, Frame K s₀.mem m →
        Proof.CmacTripleDes.Arm.ciphAt m (State.addr St) = Spec.Cmac.tdes key := fun m hf => by
      simp only [Proof.CmacTripleDes.Arm.ciphAt, Spec.Cmac.tdes]
      rw [scheduleAt_frame hf fun r hr => (dK r hr).sub_left (Region.sub_prefix (by decide)), hsch]
    obtain dat : ∀ m : Mem, Frame K s₀.mem m → ∀ a b : Nat, a + b ≤ L →
        Spec.Aes.bytesAt m (State.addr D + BitVec.ofNat 64 a) b =
          ((Spec.Aes.bytesAt s₀.mem (State.addr D) L).drop a).take b := fun m hf a b hab => by
      rw [Proof.Cmac.Stream.bytesAt_offset m (State.addr D) hab,
        Proof.Cmac.bytesAt_frame hf dDat (by omega_using [hlen])]
    obtain fS' : Frame K s₀.mem (aMem s₀ S) := fS.mono (by simp [K])
    obtain k0 : ∀ p : Addr, p + BitVec.ofNat 64 0 = p := fun p => BitVec.add_zero p
    -- The chaining value.
    obtain cv5 : Spec.Aes.bytesAt s₅.mem (State.addr St + BitVec.ofNat 64 400) 8 =
        Spec.Aes.bytesAt s₀.mem (State.addr St + BitVec.ofNat 64 400) 8 := by
      rw [Proof.Cmac.bytesAt_frame fC1 (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint (State.addr St) (d := 400) (n := 8) (e := 408) (k := 8) (by decide) (by decide)
            (by decide)) (by decide),
        Proof.Cmac.bytesAt_frame fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hp.st_s.sub_left (Offset.sub_base _ (by decide))) (by decide)]
    obtain cv10 : Spec.Aes.bytesAt s₁₀.mem (State.addr St + BitVec.ofNat 64 400) 8 =
        Spec.Aes.bytesAt s₈.mem (State.addr St + BitVec.ofNat 64 400) 8 :=
      Proof.Cmac.bytesAt_frame fC2 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint (State.addr St) (d := 400) (n := 8) (e := 408) (k := 8) (by decide) (by decide)
          (by decide)) (by decide)
    have out6 := h₆.out
    rw [a400, a408, ciph _ F5, hc] at out6
    have out8 := h₈.out
    rw [a400, h₇.mem, ciph _ F6, hc] at out8
    obtain hk : ∀ i < 400, s₁₀.mem (State.addr St + BitVec.ofNat 64 i) = s₀.mem (State.addr St + BitVec.ofNat 64 i) :=
      fun i hi => F10.bytes (R := ⟨State.addr St, 400⟩) dK (by show 400 ≤ 2 ^ 64; decide) hi
    obtain hdl : (Spec.Aes.bytesAt s₀.mem (State.addr D) L).length = L := Proof.Cmac.bytesAt_length _ _ _
    -- The bytes held back so far, and the first `f` bytes of data after them.
    obtain hb5 : Spec.Aes.bytesAt s₅.mem (State.addr St + BitVec.ofNat 64 408) (held msg.length + fOf msg.length L) =
        Spec.Aes.bytesAt s₀.mem (State.addr St + BitVec.ofNat 64 408) (held msg.length) ++
          (Spec.Aes.bytesAt s₀.mem (State.addr D) L).take (fOf msg.length L) := by
      obtain e₀ : Spec.Aes.bytesAt (aMem s₀ S) (State.addr St + BitVec.ofNat 64 408) (held msg.length) =
          Spec.Aes.bytesAt s₀.mem (State.addr St + BitVec.ofNat 64 408) (held msg.length) :=
        Proof.Cmac.bytesAt_frame fS (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hp.st_s.sub_left (Offset.sub_base _ (by omega_using [hh]))) (by omega_using [hh])
      rw [hm5, m4]
      by_cases hf0 : fOf msg.length L = 0
      · rw [hf0, show Spec.Aes.bytesAt (aMem s₀ S) (State.addr D) 0 = [] from rfl, writeBytes_nil, Nat.add_zero, e₀,
          List.take_zero, List.append_nil]
      · have hlt : 408 + held msg.length < 416 := by unfold fOf at hf0; omega_using [hf0]
        obtain hlf : (Spec.Aes.bytesAt (aMem s₀ S) (State.addr D) (fOf msg.length L)).length = fOf msg.length L :=
          Proof.Cmac.bytesAt_length _ _ _
        obtain e := bytesAt_writeBytes (aMem s₀ S) (State.addr St + BitVec.ofNat 64 408) (held msg.length)
          (Spec.Aes.bytesAt (aMem s₀ S) (State.addr D) (fOf msg.length L)) (by rw [hlf]; omega_using [hfh])
        rw [hlf] at e
        rw [hp.aS hlt, ← Offset.add_add, e, e₀]
        refine congrArg (_ ++ ·) ?_
        have := dat _ fS' 0 (fOf msg.length L) (by omega_using [hsum])
        rwa [k0, List.drop_zero] at this
    generalize hd : Spec.Aes.bytesAt s₀.mem (State.addr D) L = d at hdl hb5 dat ⊢
    by_cases hx : leftOf msg.length L = 0
    · -- Everything fits in the block held back.
      obtain hfL' : fOf msg.length L = L := by unfold leftOf at hx; omega_using [hsum, hx]
      obtain hb : b1Of msg.length L = 0 := by simp [b1Of, hx]
      obtain hn : nbOf msg.length L = 0 := by simp [nbOf, nbx, hx]
      obtain hr0 : restOf msg.length L = 0 := by simp [restOf, hn, hx]
      obtain m108 : s₁₀.mem = s₈.mem := by
        rw [h₁₀.mem, m₉, hr0, show Spec.Aes.bytesAt s₈.mem _ 0 = [] from rfl, writeBytes_nil]
      refine Proof.CmacTripleDes.Stream.repr_fill hr hk
        (by rw [hdl]; have := (f_le msg.length L).2; omega_using [hfL', this]) ?_ ?_
      · show Spec.Aes.bytesAt _ (State.addr St + BitVec.ofNat 64 400) _ =
          Spec.Aes.bytesAt _ (State.addr St + BitVec.ofNat 64 400) _
        rw [cv10, out8, hn, blocksAt_zero, out6, hb, blocksAt_zero]
        exact cv5
      · show Spec.Aes.bytesAt _ (State.addr St + BitVec.ofNat 64 408) _ =
          Spec.Aes.bytesAt _ (State.addr St + BitVec.ofNat 64 408) _ ++ _
        obtain sub : Region.Sub ⟨State.addr St + BitVec.ofNat 64 408, held msg.length + L⟩ ⟨State.addr St, 416⟩ :=
          Offset.sub_base _ (by omega_using [hfh, hfL'])
        obtain dj : ∀ r ∈ [⟨State.addr (St + BitVec.ofNat 32 400), 8⟩, ⟨State.addr S, 640⟩, blw4 s₀],
            (⟨State.addr St + BitVec.ofNat 64 408, held msg.length + L⟩ : Region).Disjoint r := by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · rw [a400]; exact Offset.disjoint _ (by omega_using []) (by omega_using [hfh, hfL']) (by omega_using [])
          · exact (hp.st_s.sub_left sub).sub_right (Region.sub_prefix (by decide))
          · exact (hp.b_st.sub_right sub).symm
        have hb5' := hb5
        rw [hfL', List.take_of_length_le (by rw [hdl])] at hb5'
        rw [m108, hdl, Proof.Cmac.bytesAt_frame f8 dj (by omega_using [hfh, hfL']),
          Proof.Cmac.bytesAt_frame f6 dj (by omega_using [hfh, hfL']), hb5']
    · -- The block held back is complete, and more blocks may follow.
      obtain hlt : 8 - held msg.length < L := by unfold leftOf fOf at hx; omega_using [hx]
      obtain hf' : fOf msg.length L = 8 - held msg.length := by unfold fOf; omega_using [hlt]
      obtain hb : b1Of msg.length L = 1 := by simp [b1Of, hx]
      obtain hn : nbOf msg.length L = Proof.CmacTripleDes.Stream.nblocks msg.length L := by
        simp only [nbOf, nbx, hx, ↓reduceIte]
        unfold leftOf Proof.CmacTripleDes.Stream.nblocks
        rw [hf']
      obtain aD2 : State.addr (d2Of St D msg.length L) = State.addr D + BitVec.ofNat 64 (fOf msg.length L) := by
        simp only [d2Of, hx, ↓reduceIte]; exact addr_add (by unfold leftOf at hx; omega_using [hD, hlt, hf'])
      have hb5' := hb5
      rw [hf', Nat.add_sub_cancel' (held_le _)] at hb5'
      refine Proof.CmacTripleDes.Stream.repr_chain hr hk (by rw [hdl]; exact hlt) ?_ ?_
      · show Spec.Aes.bytesAt _ (State.addr St + BitVec.ofNat 64 400) _ =
          Spec.Cmac.chain _ (Spec.Aes.bytesAt _ (State.addr St + BitVec.ofNat 64 400) _)
            ([Spec.Aes.bytesAt _ (State.addr St + BitVec.ofNat 64 408) _ ++ _] ++ _)
        rw [cv10, out8, out6, hb, blocksAt_one, cv5, Proof.Cmac.chain_append, aD2,
          Proof.CmacTripleDes.Stream.blocksAt_eq, dat _ F6 _ _ (by omega_using [hsum]), hb5', hdl, hf', hn]
      · have hr' : d.length - (8 - held msg.length) - 8 * Proof.CmacTripleDes.Stream.nblocks msg.length d.length =
            restOf msg.length L := by
          rw [hdl, ← hn, ← hf']; rfl
        obtain aP : State.addr (D + BitVec.ofNat 32 (fOf msg.length L) + BitVec.ofNat 32 (8 * nbOf msg.length L)) =
            State.addr D + BitVec.ofNat 64 (fOf msg.length L + 8 * nbOf msg.length L) := by
          obtain hpos : 0 < restOf msg.length L := by
            unfold restOf nbOf nbx; simp only [hx, ↓reduceIte]; omega_using [hx]
          rw [add_ofNat32]; exact addr_add (by omega_using [hD, hsum, hpos])
        obtain e := bytesAt_writeBytes_self s₈.mem (State.addr (St + BitVec.ofNat 32 408))
          (xs := Spec.Aes.bytesAt s₈.mem (State.addr (D + BitVec.ofNat 32 (fOf msg.length L) +
            BitVec.ofNat 32 (8 * nbOf msg.length L))) (restOf msg.length L))
          (by rw [Proof.Cmac.bytesAt_length]; omega_using [hrr])
        rw [Proof.Cmac.bytesAt_length] at e
        show Spec.Aes.bytesAt _ (State.addr St + BitVec.ofNat 64 408) _ = _
        rw [hr', h₁₀.mem, m₉, ← a408, e, aP, dat _ F8 _ _ (by omega_using [hsum]),
          List.take_of_length_le (by simp only [List.length_drop, hdl]; unfold restOf leftOf; omega_using []),
          List.drop_drop, hdl, ← hn, hf']

end VG.Proof.CmacTripleDes.Stream.Arm

end

end

/-! ### `CmacTripleDes.Stream.Arm.Finish`, which only this module used -/

section

/-!
# Streaming TDEA-CMAC on ARMv7: `vg_cmac_triple_des_finish`

The code copies the chaining value to `out`, computes the number of bytes
held back, and runs `finalize` with the state as its key and `out` as its
state: its result is the MAC of the message the state represents
(`repr_finish`). The code before `finalize` is constant time by the taint
analysis, and `finalize` by its own proof (`fin_rel`), its arguments pinned
by `HMid`.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.Arm

open VG VG.Arm VG.Impl.CmacTripleDes.Stream.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_mov wp_add wp_sub wp_and wp_orr wp_cmp wp_ldr
  wp_str wp_ldrSp)
open VG.Proof.CmacTripleDes.Stream (held held_le held_zero)

/-- The precondition, by name: the state `St`, `out` (`O`) and the scratch
buffer `S`. -/
structure HPre (s₀ : State) (St O S : BitVec 32) : Prop where
  r0 : s₀.gpr .r0 = St
  a0 : stackArg s₀ 0 = O
  a1 : stackArg s₀ 1 = S
  rd : s₀.rd = [⟨stackArgAddr s₀ 0, 8⟩]
  wr : s₀.wr = [⟨State.addr St, 416⟩, ⟨State.addr O, 8⟩, ⟨State.addr S, 640⟩]
  st_o : (⟨State.addr St, 416⟩ : Region).Disjoint ⟨State.addr O, 8⟩
  st_s : (⟨State.addr St, 416⟩ : Region).Disjoint ⟨State.addr S, 640⟩
  o_s : (⟨State.addr O, 8⟩ : Region).Disjoint ⟨State.addr S, 640⟩
  a_st : (⟨stackArgAddr s₀ 0, 8⟩ : Region).Disjoint ⟨State.addr St, 416⟩
  a_o : (⟨stackArgAddr s₀ 0, 8⟩ : Region).Disjoint ⟨State.addr O, 8⟩
  a_s : (⟨stackArgAddr s₀ 0, 8⟩ : Region).Disjoint ⟨State.addr S, 640⟩
  b_st : (blw4 s₀).Disjoint ⟨State.addr St, 416⟩
  b_o : (blw4 s₀).Disjoint ⟨State.addr O, 8⟩
  b_s : (blw4 s₀).Disjoint ⟨State.addr S, 640⟩
  fSt : St.toNat + 416 ≤ 2 ^ 32
  fO : O.toNat + 8 ≤ 2 ^ 32
  fS : S.toNat + 640 ≤ 2 ^ 32
  sp : 4 ≤ s₀.sp.toNat
  spf : s₀.sp.toNat + 8 ≤ 2 ^ 32

theorem HPre.of {s₀ : State} (h : finishArm.pre s₀) :
    HPre s₀ (s₀.gpr .r0) (stackArg s₀ 0) (stackArg s₀ 1) :=
  let ⟨a, b, c, d, e, f, g, i, j, k, l, m, n, o, p, q⟩ := h
  ⟨rfl, rfl, rfl, a, b, c, d, e, f, g, i, j, k, l, m, n, o, p, q⟩

/-! ## Arguments on the stack -/

theorem arg1_eq {s : State} (h : s.sp.toNat + 8 ≤ 2 ^ 32) :
    stackArgAddr s 1 = stackArgAddr s 0 + BitVec.ofNat 64 4 := by
  simp only [stackArgAddr]
  rw [addr_add (by omega_arith), addr_add (by omega_arith)]
  simp

theorem arg_in {s : State} (h : s.sp.toNat + 8 ≤ 2 ^ 32) {rs : List Region} (hr : ⟨stackArgAddr s 0, 8⟩ ∈ rs)
    {k : Nat} (hk : k < 2) : InRegions rs (stackArgAddr s k) 4 := by
  refine ⟨_, hr, ?_⟩
  rcases (by omega_arith : k = 0 ∨ k = 1) with rfl | rfl
  · simpa using Offset.contains_base (stackArgAddr s 0) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
  · rw [arg1_eq h]; exact Offset.contains_base _ (by decide) (by decide)

/-! ## The chaining value, copied to `out` -/

/-- The memory after copying the block at `p` to `o`, a word at a time. -/
def cvMem (m : Mem) (o p : Addr) : Mem :=
  (m.writeW o (m.readW p 32)).writeW (o + BitVec.ofNat 64 4) (m.readW (p + BitVec.ofNat 64 4) 32)

theorem cvMem_bytes (m : Mem) (o p : Addr) : Spec.Aes.bytesAt (cvMem m o p) o 8 = Spec.Aes.bytesAt m p 8 := by
  rw [cvMem, ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW, Proof.CmacTripleDes.readW64_split,
    Mem.readW_writeW_self32, Proof.CmacTripleDes.Arm.readW_lo_of_hi, ← Proof.CmacTripleDes.readW64_split]

theorem cvMem_frame (m : Mem) (o p : Addr) : Frame [⟨o, 8⟩] m (cvMem m o p) :=
  ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
    simpa using Offset.contains_base o (d := 0) (n := 4) (k := 8) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base o (d := 4) (n := 4) (k := 8) (by decide) (by decide))

/-! ## Before `finalize` -/

/-- What the block before `lastLen` leaves. -/
structure HBlk (s₀ : State) (St O S : BitVec 32) (s : State) : Prop where
  r0 : s.gpr .r0 = St
  r1 : s.gpr .r1 = O
  r2 : s.gpr .r2 = St + BitVec.ofNat 32 408
  r3 : s.gpr .r3 = ((s₀.gpr .r2 - 1) &&& 7) + 1
  z : s.z = ((s₀.gpr .r2 ||| s₀.gpr .r3) - 0 == 0)
  mem : s.mem = cvMem s₀.mem (State.addr O) (State.addr St + BitVec.ofNat 64 400)
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r ∈ preserved, s.gpr r = s₀.gpr r

theorem finishPre_wp {s₀ : State} {St O S : BitVec 32} (hp : HPre s₀ St O S) :
    WP isa (.block finishPre) s₀ (HBlk s₀ St O S) := by
  have hSt := hp.fSt
  have hO := hp.fO
  have aO : State.addr (O + BitVec.ofNat 32 0) = State.addr O := by rw [BitVec.add_zero]
  have aO4 : State.addr (O + BitVec.ofNat 32 4) = State.addr O + BitVec.ofNat 64 4 := addr_add (by omega_arith)
  have a400 : State.addr (St + BitVec.ofNat 32 400) = State.addr St + BitVec.ofNat 64 400 := addr_add (by omega_arith)
  have a404 : State.addr (St + BitVec.ofNat 32 404) = State.addr St + BitVec.ofNat 64 400 + BitVec.ofNat 64 4 := by
    rw [Offset.add_add]; exact addr_add (by omega_arith)
  have inSt (d : Nat) (hd : d + 4 ≤ 416) :
      InRegions (s₀.rd ++ s₀.wr) (State.addr St + BitVec.ofNat 64 d) 4 := by
    rw [hp.rd, hp.wr]; exact ⟨⟨State.addr St, 416⟩, by simp, Offset.contains_base _ hd (by omega_arith)⟩
  have inO (d : Nat) (hd : d + 4 ≤ 8) : InRegions s₀.wr (State.addr O + BitVec.ofNat 64 d) 4 := by
    rw [hp.wr]; exact ⟨⟨State.addr O, 8⟩, by simp, Offset.contains_base _ hd (by omega_arith)⟩
  have dW : (⟨State.addr O, 4⟩ : Region).Disjoint ⟨State.addr St + BitVec.ofNat 64 400 + BitVec.ofNat 64 4, 4⟩ := by
    rw [Offset.add_add]
    exact (hp.st_o.sub_left (Offset.sub_base _ (by decide))).symm.sub_left (Region.sub_prefix (by decide))
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) rfl
    (arg_in hp.spf (by rw [hp.rd]; simp) (by decide)) fun s₁ u₁ => ?_
  have h1 : s₁.gpr .r1 = O := by rw [u₁.gpr]; exact hp.a0
  refine wp_ldr (a := State.addr St + BitVec.ofNat 64 400) (by decide)
    (by rw [u₁.other _ (by decide), hp.r0, a400]) (by rw [u₁.rd, u₁.wr]; exact inSt 400 (by decide))
    fun s₂ u₂ => ?_
  refine wp_str (a := State.addr O) (by decide) (by rw [u₂.other _ (by decide), h1, aO])
    (by rw [u₂.wr, u₁.wr]; simpa using inO 0 (by decide)) fun s₃ v₃ => ?_
  refine wp_ldr (a := State.addr St + BitVec.ofNat 64 400 + BitVec.ofNat 64 4) (by decide)
    (by rw [v₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hp.r0, a404])
    (by rw [v₃.rd, v₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, Offset.add_add]; exact inSt 404 (by decide)) fun s₄ u₄ => ?_
  refine wp_str (a := State.addr O + BitVec.ofNat 64 4) (by decide)
    (by rw [u₄.other _ (by decide), v₃.gpr, u₂.other _ (by decide), h1, aO4])
    (by rw [u₄.wr, v₃.wr, u₂.wr, u₁.wr]; exact inO 4 (by decide)) fun s₅ v₅ => ?_
  refine wp_orr (op2_reg _ _) fun s₆ u₆ => wp_sub (op2_imm (by decide)) fun s₇ u₇ =>
    wp_and (op2_imm (by decide)) fun s₈ u₈ => wp_add (op2_imm (by decide)) fun s₉ u₉ =>
    wp_add (op2_imm (by decide)) fun s₁₀ u₁₀ => wp_cmp (op2_imm (by decide)) fun s₁₁ f₁₁ z₁₁ => WP.block_nil ?_
  have g : ∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s₁₁.gpr r = s₀.gpr r := fun r a b c d => by
    rw [f₁₁.gpr, u₁₀.other _ b, u₉.other _ c, u₈.other _ c, u₇.other _ c, u₆.other _ d, v₅.gpr,
      u₄.other _ d, v₃.gpr, u₂.other _ d, u₁.other _ a]
  have m₁₁ : s₁₁.mem = cvMem s₀.mem (State.addr O) (State.addr St + BitVec.ofNat 64 400) := by
    rw [f₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, v₅.mem, u₄.gpr, u₄.mem, v₃.mem, u₂.gpr,
      u₂.mem, u₁.mem, cvMem,
      Mem.readW_writeW_sep (dW.symm.sep (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)]
  refine ⟨by rw [g .r0 (by decide) (by decide) (by decide) (by decide)]; exact hp.r0, ?_, ?_, ?_, ?_, m₁₁,
    ?_, ?_, ?_, fun r hr => ?_⟩
  · rw [f₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.other _ (by decide), v₅.gpr, u₄.other _ (by decide), v₃.gpr, u₂.other _ (by decide),
      h1]
  · rw [f₁₁.gpr, u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.other _ (by decide), v₅.gpr, u₄.other _ (by decide), v₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), hp.r0]; rfl
  · rw [f₁₁.gpr, u₁₀.other _ (by decide), u₉.gpr, u₈.gpr, u₇.gpr, u₆.other _ (by decide),
      v₅.gpr, u₄.other _ (by decide), v₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [z₁₁]
    simp (disch := decide) only [u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.gpr, v₅.gpr, u₄.other, v₃.gpr,
      u₂.other, u₁.other]
  · rw [f₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, v₅.sp, u₄.sp, v₃.sp, u₂.sp, u₁.sp]
  · rw [f₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, v₅.rd, u₄.rd, v₃.rd, u₂.rd, u₁.rd]
  · rw [f₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, v₅.wr, u₄.wr, v₃.wr, u₂.wr, u₁.wr]
  · have : r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact g r this.1 this.2.1 this.2.2.1 this.2.2.2

/-- What the code before `finalize` leaves. -/
structure HMid (s₀ : State) (St O S : BitVec 32) (s : State) : Prop where
  args : FArgs s St O (St + BitVec.ofNat 32 408) S (held (countArm s₀).toNat)
  mem : s.mem = cvMem s₀.mem (State.addr O) (State.addr St + BitVec.ofNat 64 400)
  keep : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem HPre.aL {s₀ : State} {St O S : BitVec 32} (hp : HPre s₀ St O S) :
    State.addr (St + BitVec.ofNat 32 408) = State.addr St + BitVec.ofNat 64 408 := addr_add (by have := hp.fSt; omega_arith)

theorem HPre.fargs {s₀ s : State} {St O S : BitVec 32} {L : Nat} (hp : HPre s₀ St O S) (hL : L ≤ 8)
    (r0 : s.gpr .r0 = St) (r1 : s.gpr .r1 = O) (r2 : s.gpr .r2 = St + BitVec.ofNat 32 408)
    (r3 : s.gpr .r3 = BitVec.ofNat 32 L) (r12 : s.gpr .r12 = S)
    (sp : s.sp = s₀.sp) (rd : s.rd = s₀.rd) (wr : s.wr = s₀.wr) :
    FArgs s St O (St + BitVec.ofNat 32 408) S L := by
  have hw := hp.fSt
  have pSt : Region.Sub ⟨State.addr (St + BitVec.ofNat 32 408), L⟩ ⟨State.addr St, 416⟩ := by
    rw [hp.aL]; exact Offset.sub_base _ (by omega_arith)
  have hb : blw4 s = blw4 s₀ := by rw [blw4, sp]
  exact
  { r0 := r0, r1 := r1, r2 := r2, r3 := r3, r12 := r12, len := hL
    hsp := by rw [sp]; exact hp.sp
    kst := hp.st_o.sub_left (Region.sub_prefix (by decide))
    ks := hp.st_s.sub_left (Region.sub_prefix (by decide))
    pst := hp.st_o.sub_left pSt
    ps := hp.st_s.sub_left pSt
    sts := hp.o_s
    bk := by rw [hb]; exact hp.b_st.sub_right (Region.sub_prefix (by decide))
    bp := by rw [hb]; exact hp.b_st.sub_right pSt
    bst := by rw [hb]; exact hp.b_o
    bs := by rw [hb]; exact hp.b_s
    fK := by omega_arith
    fSt := hp.fO
    fP := by rw [toNat_add_ofNat (by omega_arith)]; omega_arith
    fS := hp.fS
    reads := by
      rw [rd, wr, hp.rd, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨State.addr St, 416⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
      · exact ⟨⟨State.addr St, 416⟩, by simp, 408, hp.aL, by simp; omega_arith⟩
    writes := by
      rw [wr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨State.addr O, 8⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩
      · exact ⟨⟨State.addr S, 640⟩, by simp, 0, (BitVec.add_zero _).symm, by simp⟩ }

theorem finPre_wp {s₀ : State} {St O S : BitVec 32} (hp : HPre s₀ St O S) :
    WP isa finPre s₀ (HMid s₀ St O S) := by
  refine WP.seq (WP.mono (finishPre_wp hp) fun s₁ h₁ => ?_)
  have hc := (countArm s₀).isLt
  have ev : isa.eval .eq s₁ = some (decide ((countArm s₀).toNat = 0)) := by
    show VG.Arm.eval .eq s₁ = _
    rw [VG.Proof.MdStream.Arm.eval_eq, h₁.z, or_beq_zero (count_eq s₀) hc]
  have tail : ∀ {t : State} {L : Nat}, L ≤ 8 → t.gpr .r3 = BitVec.ofNat 32 L → L = held (countArm s₀).toNat →
      (∀ r, r ≠ .r3 → t.gpr r = s₁.gpr r) → t.mem = s₁.mem → t.sp = s₁.sp → t.rd = s₁.rd → t.wr = s₁.wr →
      WP isa (.block finArgs) t (HMid s₀ St O S) := fun {t L} hL h3 hLe g m sp rd wr => by
    refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) (by rw [sp, h₁.sp]; rfl)
      (by rw [rd, wr, h₁.rd, h₁.wr]; exact arg_in hp.spf (by rw [hp.rd]; simp) (by decide))
      fun t₁ u₁ => WP.block_nil ?_
    have hS : t₁.gpr .r12 = S := by
      rw [u₁.gpr, m, h₁.mem, ← hp.a1]
      exact (cvMem_frame _ _ _).readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.a_o.sub_left (by rw [arg1_eq hp.spf]; exact Offset.sub_base _ (by decide))) (by decide)
    refine ⟨hLe ▸ hp.fargs hL (by rw [u₁.other _ (by decide), g _ (by decide), h₁.r0])
      (by rw [u₁.other _ (by decide), g _ (by decide), h₁.r1]) (by rw [u₁.other _ (by decide), g _ (by decide), h₁.r2])
      (by rw [u₁.other _ (by decide), h3]) hS (by rw [u₁.sp, sp, h₁.sp]) (by rw [u₁.rd, rd, h₁.rd])
      (by rw [u₁.wr, wr, h₁.wr]), by rw [u₁.mem, m, h₁.mem], fun r hr => ?_, by rw [u₁.sp, sp, h₁.sp],
      by rw [u₁.rd, rd, h₁.rd], by rw [u₁.wr, wr, h₁.wr]⟩
    have : r ≠ .r3 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [u₁.other _ this.2, g _ this.1, h₁.keep r hr]
  refine WP.seq ?_
  by_cases h0 : (countArm s₀).toNat = 0
  · refine WP.ite true (by rw [ev, h0]; rfl) (fun _ => ?_) (fun h => by cases h)
    refine wp_mov (op2_imm (by decide)) fun t u => WP.block_nil ?_
    exact tail (L := 0) (by decide) u.gpr (by rw [h0]; rfl) (fun r h => u.other r h) u.mem u.sp u.rd u.wr
  · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => WP.block_nil ?_
    refine tail (held_le _) ?_ rfl (fun _ _ => rfl) rfl rfl rfl rfl
    rw [h₁.r3]
    exact held_lo (count_eq s₀) hc h0

/-! ## The whole function -/

theorem finish_wp {s₀ : State} (h0 : finishArm.pre s₀) :
    WP isa finish s₀ fun s' => abiPreserved s₀ s' ∧ finishArm.post s₀ s' := by
  have hp := HPre.of h0
  generalize s₀.gpr .r0 = St at hp
  generalize stackArg s₀ 0 = O at hp
  generalize stackArg s₀ 1 = S at hp
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.mono (fin_wp h₁.args) fun s₂ h₂ => ?_
  have f₁ : Frame [⟨State.addr O, 8⟩] s₀.mem s₁.mem := by rw [h₁.mem]; exact cvMem_frame _ _ _
  refine ⟨⟨fun r hr => by rw [h₂.saved r hr, h₁.keep r hr], by rw [h₂.sp, h₁.sp]⟩, ?_⟩
  intro key msg hr hc hlen
  rw [hp.r0] at hr
  rw [hp.a0]
  have hr₁ : Spec.Cmac.tdesRepr s₁.mem (State.addr St) key msg :=
    Proof.CmacTripleDes.Stream.repr_congr_416 (fun i hi => f₁.bytes (R := ⟨State.addr St, 416⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.st_o) (by show 416 ≤ 2 ^ 64; decide) hi) hr
  obtain ⟨hm, hne, hst, happ⟩ := Proof.CmacTripleDes.Stream.repr_finish hr₁
  rw [Proof.CmacTripleDes.Stream.repr_iff] at hr₁
  obtain ⟨⟨_, hks, hsk⟩, -, -⟩ := hr₁
  have hn : (countArm s₀).toNat = msg.length := by rw [hc, toNat_ofNat64 hlen]
  have hciph : Proof.CmacTripleDes.Arm.ciphAt s₁.mem (State.addr St) = Spec.Cmac.tdes key := by
    simp only [Proof.CmacTripleDes.Arm.ciphAt, hks, Spec.Cmac.tdes]
  have e₂ : Spec.Aes.bytesAt s₁.mem (State.addr O) 8 = Spec.Aes.bytesAt s₁.mem (State.addr St + 400) 8 := by
    rw [h₁.mem, cvMem_bytes, show State.addr St + 400 = State.addr St + BitVec.ofNat 64 400 from rfl]
    exact (Proof.Cmac.bytesAt_frame (cvMem_frame _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_o.sub_left (Offset.sub_base _ (d := 400) (n := 8) (by decide))) (by decide)).symm
  have out := h₂.out (by rw [hciph]; exact hsk) _ hm (by rw [hn]; exact hne)
    (by rw [hciph, e₂]; exact hst)
  rw [out, hciph, hn, hp.aL, show State.addr St + BitVec.ofNat 64 408 = State.addr St + 408 from rfl, happ,
    Proof.CmacTripleDes.Stream.tdesCmac_eq]

/-! ## Constant time -/

/-- The stack arguments of a state satisfying the precondition, for the
taint analysis. -/
theorem HPre.wfA {s₀ : State} {St O S : BitVec 32} (hp : HPre s₀ St O S) :
    s₀.sp.toNat + 8 ≤ 2 ^ 32 ∧ ∀ r ∈ s₀.wr, Region.Disjoint ⟨State.addr s₀.sp, 8⟩ r := by
  have e : (⟨State.addr s₀.sp, 8⟩ : Region) = ⟨stackArgAddr s₀ 0, 8⟩ := by simp [stackArgAddr]
  refine ⟨hp.spf, ?_⟩
  rw [e, hp.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hp.a_st
  · exact hp.a_o
  · exact hp.a_s

theorem finish_rel {s₀ s₀' : State} (h0 : finishArm.pre s₀) (h0' : finishArm.pre s₀')
    (hq : finishArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') finish fun _ _ => True := by
  obtain ⟨q1, q2, q4, q5, q6, q7⟩ := hq
  have hp := HPre.of h0
  have hp' : HPre s₀' (s₀.gpr .r0) (stackArg s₀ 0) (stackArg s₀ 1) := by
    rw [q2, q6, q7]; exact HPre.of h0'
  have hc : (countArm s₀').toNat = (countArm s₀).toNat := by simp only [countArm, q4, q5]
  have wf := hp.wfA
  have wf' := hp'.wfA
  generalize s₀.gpr .r0 = St at hp hp'
  generalize stackArg s₀ 0 = O at hp hp'
  generalize stackArg s₀ 1 = S at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (argTaint [.r0, .r2, .r3] 8) finPre h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := HMid s₀ St O S)
    (G' := HMid s₀' St O S) (argTaint [.r0, .r2, .r3] 8)
    (fun s s' e e' => by
      subst e e'
      refine agree_argTaint (fun r hr => ?_) q1 wf wf' (argMem_of (j := 2) q1 hp.spf fun i hi => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        exacts [q2, q4, q5]
      · rcases (by omega_arith : i = 0 ∨ i = 1) with rfl | rfl
        · exact q6
        · exact q7) ⟨_, hA⟩
    (fun s e => by rw [e]; exact finPre_wp hp) (fun s e => by rw [e]; exact finPre_wp hp')
  have c := fin_rel (sp₀ := s₀.sp) (Pr := fun s s' => HMid s₀ St O S s ∧ HMid s₀' St O S s')
    fun _ _ h => ⟨h.1.args, by rw [← hc]; exact h.2.args, h.1.sp, h.2.sp.trans q1.symm⟩
  exact a.seq c

theorem finish_ct : ConstantTime isa finishArm.pre finishArm.pub finish :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (finish_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacTripleDes.Stream.Arm

end

end

/-! ### `CmacTripleDes.Stream.Arm.Init`, which only this module used -/

section

/-!
# Streaming TDEA-CMAC on ARMv7: `vg_cmac_triple_des_stream_init`

The code zeroes the chaining value and runs `init` with the state as its
`out`, which writes the key schedule and the subkeys before it: the state
then represents the empty message. The taint analysis checks it whole, the
code of `init` too, from the public arguments, with `r0` pointing at the
state and `r3` at the scratch buffer (where `init` keeps its pointers).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.Arm

open VG VG.Arm VG.Impl.CmacTripleDes.Stream.Arm
open VG.Impl.CmacTripleDes.Arm (mov)
open VG.Proof.MdStream.Arm (Upd Mupd op2_imm op2_reg wp_mov wp_str addr_toNat)

/-- The precondition, by name: the state `St`, the key `Kp` of `KL` bytes
and the scratch buffer `S`. -/
structure IPre (s₀ : State) (St Kp S : BitVec 32) (KL : Nat) : Prop where
  r0 : s₀.gpr .r0 = St
  r1 : s₀.gpr .r1 = Kp
  r2 : (s₀.gpr .r2).toNat = KL
  r3 : s₀.gpr .r3 = S
  rd : s₀.rd = [⟨State.addr Kp, KL⟩]
  wr : s₀.wr = [⟨State.addr St, 416⟩, ⟨State.addr S, 640⟩]
  st_k : (⟨State.addr St, 416⟩ : Region).Disjoint ⟨State.addr Kp, KL⟩
  st_s : (⟨State.addr St, 416⟩ : Region).Disjoint ⟨State.addr S, 640⟩
  k_s : (⟨State.addr Kp, KL⟩ : Region).Disjoint ⟨State.addr S, 640⟩
  fSt : St.toNat + 416 ≤ 2 ^ 32
  fK : Kp.toNat + KL ≤ 2 ^ 32
  fS : S.toNat + 640 ≤ 2 ^ 32
  klen : Spec.TripleDes.validKey KL

theorem IPre.of {s₀ : State} (h : initArm.pre s₀) :
    IPre s₀ (s₀.gpr .r0) (s₀.gpr .r1) (s₀.gpr .r3) (s₀.gpr .r2).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i⟩ := h
  ⟨rfl, rfl, rfl, rfl, a, b, c, d, e, f, g, h, i⟩

/-- The memory after zeroing the chaining value at `p`, a word at a time. -/
def zeroCv (m : Mem) (p : Addr) : Mem :=
  (m.writeW p (0 : BitVec 32)).writeW (p + BitVec.ofNat 64 4) (0 : BitVec 32)

theorem zeroCv_bytes (m : Mem) (p : Addr) : Spec.Aes.bytesAt (zeroCv m p) p 8 = Spec.Cmac.zeros 8 := by
  rw [zeroCv, ← Proof.Cmac.le8_readW, Proof.CmacTripleDes.readW64_split, Mem.readW_writeW_self32,
    Proof.CmacTripleDes.Arm.readW_lo_of_hi]
  decide

theorem zeroCv_frame (m : Mem) (p : Addr) : Frame [⟨p, 8⟩] m (zeroCv m p) :=
  ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by
    simpa using Offset.contains_base p (d := 0) (n := 4) (k := 8) (by decide) (by decide))).writeW
    (List.mem_singleton_self _) _ (Offset.contains_base p (d := 4) (n := 4) (k := 8) (by decide) (by decide))

theorem initPre_wp {s₀ : State} {St Kp S : BitVec 32} {KL : Nat} (hp : IPre s₀ St Kp S KL) :
    WP isa (.block initPre) s₀ fun s₁ => s₁.gpr .r0 = Kp ∧ s₁.gpr .r1 = BitVec.ofNat 32 KL ∧
      s₁.gpr .r2 = St ∧ s₁.gpr .r3 = S ∧ (∀ r ∈ preserved, s₁.gpr r = s₀.gpr r) ∧ s₁.sp = s₀.sp ∧
      s₁.mem = zeroCv s₀.mem (State.addr St + BitVec.ofNat 64 400) ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr := by
  have hSt := hp.fSt
  have hKL : s₀.gpr .r2 = BitVec.ofNat 32 KL :=
    BitVec.eq_of_toNat_eq (by rw [hp.r2, toNat_ofNat32 (by rcases hp.klen with h | h <;> omega_using [h])])
  have inSt (d : Nat) (hd : d + 4 ≤ 416) : InRegions s₀.wr (State.addr St + BitVec.ofNat 64 d) 4 := by
    rw [hp.wr]; exact ⟨⟨State.addr St, 416⟩, by simp, Offset.contains_base _ hd (by omega_using [hd])⟩
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => ?_
  refine wp_str (a := State.addr St + BitVec.ofNat 64 400) (by decide)
    (by rw [u₁.other _ (by decide), hp.r0]; exact addr_add (by omega_using [hSt])) (by rw [u₁.wr]; exact inSt 400 (by decide))
    fun s₂ v₂ => ?_
  refine wp_str (a := State.addr St + BitVec.ofNat 64 400 + BitVec.ofNat 64 4) (by decide)
    (by rw [v₂.gpr, u₁.other _ (by decide), hp.r0, Offset.add_add]; exact addr_add (by omega_using [hSt]))
    (by rw [v₂.wr, u₁.wr, Offset.add_add]; exact inSt 404 (by decide)) fun s₃ v₃ => ?_
  refine wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ => wp_mov (op2_reg _ _) fun s₆ u₆ =>
    wp_mov (op2_reg _ _) fun s₇ u₇ => WP.block_nil ?_
  have g (r : Reg) (a : r ≠ .r0) (b : r ≠ .r1) (c : r ≠ .r2) (d : r ≠ .r12) : s₇.gpr r = s₀.gpr r := by
    rw [u₇.other _ c, u₆.other _ b, u₅.other _ a, u₄.other _ d, v₃.gpr, v₂.gpr, u₁.other _ d]
  refine ⟨?_, ?_, ?_, g _ (by decide) (by decide) (by decide) (by decide) |>.trans hp.r3,
    fun r hr => ?_, by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, v₃.sp, v₂.sp, u₁.sp], ?_,
    by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, v₃.rd, v₂.rd, u₁.rd], by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, v₃.wr, v₂.wr, u₁.wr]⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), v₃.gpr, v₂.gpr,
      u₁.other _ (by decide), hp.r1]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), v₃.gpr, v₂.gpr,
      u₁.other _ (by decide), hKL]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, v₃.gpr, v₂.gpr, u₁.other _ (by decide),
      hp.r0]
  · have : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r12 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact g r this.1 this.2.1 this.2.2.1 this.2.2.2
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, v₃.mem, v₂.mem, v₂.gpr, u₁.gpr, u₁.mem, zeroCv]

theorem init_wp {s₀ : State} (h0 : initArm.pre s₀) :
    WP isa streamInit s₀ fun s' => abiPreserved s₀ s' ∧ initArm.post s₀ s' := by
  have hp := IPre.of h0
  generalize s₀.gpr .r0 = St at hp
  generalize s₀.gpr .r1 = Kp at hp
  generalize s₀.gpr .r3 = S at hp
  generalize (s₀.gpr .r2).toNat = KL at hp
  have hw := hp.fSt
  refine WP.seq (WP.mono (initPre_wp hp) fun s₁ ⟨r0₁, r1₁, r2₁, r3₁, sv₁, sp₁, m₁, rd₁, wr₁⟩ => ?_)
  have oSt : Region.Sub ⟨State.addr St, 400⟩ ⟨State.addr St, 416⟩ := Region.sub_prefix (by decide)
  have args : IArgs s₁ Kp St S KL :=
    { r0 := r0₁, r1 := r1₁, r2 := r2₁, r3 := r3₁, klen := hp.klen
      ko := (hp.st_k.sub_left oSt).symm
      ks := hp.k_s
      os := hp.st_s.sub_left oSt
      fK := hp.fK
      fO := by omega_using [hw]
      fS := hp.fS
      reads := by
        rw [rd₁, wr₁, hp.rd, hp.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨⟨State.addr Kp, KL⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨State.addr St, 416⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨State.addr S, 640⟩, by simp, 0, by simp, by simp⟩
      writes := by
        rw [wr₁, hp.wr]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨⟨State.addr St, 416⟩, by simp, 0, by simp, by simp⟩
        · exact ⟨⟨State.addr S, 640⟩, by simp, 0, by simp, by simp⟩ }
  refine WP.mono (init_inline_wp args) fun s₂ h₂ => ?_
  have f₁ : Frame [⟨State.addr St + BitVec.ofNat 64 400, 8⟩] s₀.mem s₁.mem := by rw [m₁]; exact zeroCv_frame _ _
  refine ⟨⟨fun r hr => by rw [h₂.saved r hr, sv₁ r hr], by rw [h₂.sp, sp₁]⟩, ?_⟩
  show Spec.Cmac.tdesRepr s₂.mem (State.addr (s₀.gpr .r0))
    (Spec.TripleDes.bytesAt s₀.mem (State.addr (s₀.gpr .r1)) (s₀.gpr .r2).toNat) []
  rw [hp.r0, hp.r1, hp.r2, Proof.CmacTripleDes.Stream.repr_iff]
  have hkey : Spec.TripleDes.bytesAt s₁.mem (State.addr Kp) KL = Spec.TripleDes.bytesAt s₀.mem (State.addr Kp) KL := by
    simp only [Spec.TripleDes.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact f₁.bytes (R := ⟨State.addr Kp, KL⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_k.symm.sub_right (Offset.sub_base _ (by decide)))
      (by show KL ≤ 2 ^ 64; have := hp.fK; omega_using [this]) (List.mem_range.mp hi)
  have hlen : (Spec.TripleDes.bytesAt s₀.mem (State.addr Kp) KL).length = KL := by simp [Spec.TripleDes.bytesAt]
  obtain ⟨hs, hk⟩ := h₂.out
  rw [hkey] at hs hk
  refine ⟨⟨by rw [hlen]; exact hp.klen, hs, hk⟩, ?_, by
    simp [Proof.CmacTripleDes.Stream.held_zero, Spec.Aes.bytesAt]⟩
  rw [show State.addr St + 400 = State.addr St + BitVec.ofNat 64 400 from rfl,
    Proof.Cmac.bytesAt_frame h₂.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint_base _ (d := 400) (by decide) (by decide)
      · exact (hp.st_s.sub_left (Offset.sub_base _ (by decide)))) (by decide), m₁, zeroCv_bytes]
  rfl

/-! ## Constant time -/

/-- `stream_init`'s initial taint: the arguments are public; `r0` and `r3`
point at the state and the scratch buffer. -/
def initTaint : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, lens := [416, 640], bases := [(.r0, 0), (.r3, 1)] }

theorem initTaint_wf {s : State} (h : initArm.pre s) : VG.Arm.Taint.Wf initTaint s := by
  have hp := IPre.of h
  refine ⟨fun _ => ⟨by simp [hp.wr, initTaint], ?_, ?_⟩, fun p hp' => ?_, fun h => absurd h (by decide),
    fun _ h => (List.not_mem_nil h).elim⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, false_implies, implies_true, and_true]
    exact hp.st_s
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    have := hp.fSt; have := hp.fS
    rintro r (rfl | rfl) <;> simp only [addr_toNat] <;> omega_arith
  · simp only [initTaint, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> simp [VG.Arm.Taint.region, hp.wr]

theorem init_ct : ConstantTime isa initArm.pre initArm.pub streamInit := by
  refine VG.Taint.constantTime (A := taint) initTaint ?_ (by taint_decide)
  intro s t hs ht ⟨hsp, h0, h1, h2, h3⟩
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, initTaint_wf hs, initTaint_wf ht,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun h => absurd h (by decide), fun k hk => absurd hk (by simp [initTaint])⟩
  · simp only [initTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [h0, h1, h2, h3]
  · rw [(IPre.of hs).wr, (IPre.of ht).wr, h0, h3]

end VG.Proof.CmacTripleDes.Stream.Arm

end

end

/-!
# Streaming TDEA-CMAC on ARMv7: `Verified`

Correctness, constant time and satisfiability under this target's contracts
(`Contract.lean`), and the shared contracts with the working space as an
argument (`Proof/CmacTripleDes/StreamScratch.lean`), which imply them: with
no stack for `stream_init`, and 4 bytes for `absorb` and `finish` (the stack
argument of the code they run inline, which they push).

The taint analysis does not analyse frames, so two runs of `absorb` from
states that agree on the public arguments are related piece by piece
(`RelCT`): the taint analysis covers the code between the runs of `update`,
from the public arguments for `absorbPre` and from the registers the
correctness proof pins to values of the public arguments afterwards
(`AAfter₁`, `AAfter₂`), and each run of `update`, in its frame, is constant
time by its own proof (`upd_rel`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.Arm

open VG VG.Arm VG.Impl.CmacTripleDes.Stream.Arm

/-- The stack arguments of a state satisfying the precondition, for the
taint analysis. -/
theorem APre.wfA {s₀ : State} {St D S : BitVec 32} {L : Nat} (hp : APre s₀ St D S L) :
    s₀.sp.toNat + 12 ≤ 2 ^ 32 ∧ ∀ r ∈ s₀.wr, Region.Disjoint ⟨State.addr s₀.sp, 12⟩ r := by
  have e : (⟨State.addr s₀.sp, 12⟩ : Region) = ⟨stackArgAddr s₀ 0, 12⟩ := by simp [stackArgAddr]
  refine ⟨hp.spf, ?_⟩
  rw [e, hp.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact hp.a_st
  · exact hp.a_s

theorem absorb_rel {s₀ s₀' : State} (h0 : absorbArm.pre s₀) (h0' : absorbArm.pre s₀')
    (hq : absorbArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') absorb fun _ _ => True := by
  obtain ⟨q1, q2, q4, q5, q6, q7, q8⟩ := hq
  have hp := APre.of h0
  have hp' : APre s₀' (s₀.gpr .r0) (stackArg s₀ 0) (stackArg s₀ 2) (stackArg s₀ 1).toNat := by
    rw [q2, q6, q7, q8]; exact APre.of h0'
  have hc : (countArm s₀').toNat = (countArm s₀).toNat := by simp only [countArm, q4, q5]
  have wf := hp.wfA
  have wf' := hp'.wfA
  generalize s₀.gpr .r0 = St at hp hp'
  generalize stackArg s₀ 0 = D at hp hp'
  generalize stackArg s₀ 2 = S at hp hp'
  generalize (stackArg s₀ 1).toNat = L at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (argTaint [.r0, .r2, .r3] 12) absorbPre h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r4, .r6, .r7, .r10]) chain2 h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.r4, .r6, .r7, .r8, .r10]) absorbPost h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := AMid₁ s₀ St D S L)
    (G' := AMid₁ s₀' St D S L) (argTaint [.r0, .r2, .r3] 12)
    (fun s s' e e' => by
      subst e e'
      refine agree_argTaint (fun r hr => ?_) q1 wf wf' (argMem_of (j := 3) q1 hp.spf fun i hi => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        exacts [q2, q4, q5]
      · rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
        · exact q6
        · exact q7
        · exact q8) ⟨_, hA⟩
    (fun s e => by rw [e]; exact absorbPre_wp hp) (fun s e => by rw [e]; exact absorbPre_wp hp')
  have c₁ := rel_wp (F := AMid₁ s₀ St D S L) (F' := AMid₁ s₀' St D S L) (G := AAfter₁ s₀ St D S L)
    (G' := AAfter₁ s₀' St D S L)
    (upd_rel (sp₀ := s₀.sp) fun _ _ h => ⟨h.1.args, by rw [← hc]; exact h.2.args, h.1.sp, h.2.sp.trans q1.symm⟩)
    (fun _ h => upd1_after h) (fun _ h => upd1_after h)
  have m := rel_agree (F := AAfter₁ s₀ St D S L) (F' := AAfter₁ s₀' St D S L)
    (G := fun s => ∃ m, AMid₂ s₀ St D S L m s) (G' := fun s => ∃ m, AMid₂ s₀' St D S L m s)
    (Taint.ofRegs [.r4, .r6, .r7, .r10])
    (fun s s' h h' => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.r4, h'.r4]
      · rw [h.r6, h'.r6, hc]
      · rw [h.r7, h'.r7, hc]
      · rw [h.r10, h'.r10]) ⟨_, hB⟩
    (fun s h => WP.mono (chain2_mid hp h) fun _ h => ⟨_, h⟩)
    (fun s h => WP.mono (chain2_mid hp' h) fun _ h => ⟨_, h⟩)
  have c₂ := rel_wp (F := fun s => ∃ m, AMid₂ s₀ St D S L m s) (F' := fun s => ∃ m, AMid₂ s₀' St D S L m s)
    (G := AAfter₂ s₀ St D S L) (G' := AAfter₂ s₀' St D S L)
    (upd_rel (sp₀ := s₀.sp) fun _ _ ⟨⟨_, h₁⟩, ⟨_, h₂⟩⟩ =>
      ⟨h₁.args, by rw [← hc]; exact h₂.args, h₁.sp, h₂.sp.trans q1.symm⟩)
    (fun _ ⟨_, h⟩ => upd2_after h) (fun _ ⟨_, h⟩ => upd2_after h)
  have p := RelCT.taint (A := taint) (P := fun a b => AAfter₂ s₀ St D S L a ∧ AAfter₂ s₀' St D S L b)
    (Taint.ofRegs [.r4, .r6, .r7, .r8, .r10]) (fun a b h => by
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [h.1.r4, h.2.r4]
      · rw [h.1.r6, h.2.r6, hc]
      · rw [h.1.r7, h.2.r7, hc]
      · rw [h.1.r8, h.2.r8, hc]
      · rw [h.1.r10, h.2.r10]) hC
  exact a.seq (c₁.seq (m.seq (c₂.seq p)))

theorem absorb_ct : ConstantTime isa absorbArm.pre absorbArm.pub absorb :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (absorb_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `Verified` -/

theorem init_verified : Verified Arm.target streamInit (streamInitScratchContract Arm.abi 0) :=
  Verified.of_correct (fun _ hs => init_wp hs) init_ct init_implies

theorem absorb_verified : Verified Arm.target absorb (absorbScratchContract Arm.abi 4) :=
  Verified.of_correct (fun _ hs => absorb_wp hs) absorb_ct absorb_implies

theorem finish_verified : Verified Arm.target finish (finishScratchContract Arm.abi 4) :=
  Verified.of_correct (fun _ hs => finish_wp hs) finish_ct finish_implies

end VG.Proof.CmacTripleDes.Stream.Arm

end

end

/-!
# Streaming TDEA-CMAC on ARMv7, with its working space on the stack

The streaming functions run their code, proved with the working space as an
argument (`Verified.lean`), in a frame that allocates it. `stream_init`'s
working space is its fourth argument, in `r3`: its frame is the 640 bytes
of working space (`Verified.regScratch`). That of `absorb` and `finish` is
their last, on the stack: their frames hold the copies of their stack
arguments and `lr` too (`Verified.stackScratch`), 704 bytes for `absorb`
(688 of working space) and 656 for `finish`, below which their code pushes
the working space's address. The copies are read only where the pre- and
postconditions read the buffers (`Proof/CmacTripleDes/StreamScratch.lean`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.Arm

open VG VG.Arm VG.Impl.CmacTripleDes.Stream.Arm

/-- A state satisfying `vg_cmac_triple_des_stream_init`'s precondition,
without the working space. -/
def initFrameSat : State := { initSat with wr := [⟨0x1000, 416⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Cmac.tdesStreamInitContract Arm.abi 640).pre s := by
  implies_sat [Spec.Cmac.tdesStreamInitContract, Spec.Cmac.tdesStreamInitSig, Spec.Cmac.tdesStreamInitPre,
    Spec.Cmac.tdesStreamInitPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [initFrameSat, initSat] using initFrameSat

/-- A state satisfying `vg_cmac_triple_des_absorb`'s precondition, without
the working space: as `absorbSat`. -/
def absorbFrameSat : State :=
  { absorbSat with rd := [⟨0x3000, 0⟩, ⟨0x8000, 8⟩], wr := [⟨0x1000, 416⟩] }

theorem absorbFrameSat_pre : ∃ s, (Spec.Cmac.tdesAbsorbContract Arm.abi 708).pre s := by
  implies_sat [Spec.Cmac.tdesAbsorbContract, Spec.Cmac.tdesAbsorbSig, Spec.Cmac.tdesAbsorbPost, countArm,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [absorbFrameSat, absorbSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using absorbFrameSat

/-- A state satisfying `vg_cmac_triple_des_finish`'s precondition, without
the working space: as `finishSat`. -/
def finishFrameSat : State :=
  { finishSat with rd := [⟨0x8000, 4⟩], wr := [⟨0x1000, 416⟩, ⟨0x2000, 8⟩] }

theorem finishFrameSat_pre : ∃ s, (Spec.Cmac.tdesFinishContract Arm.abi 660).pre s := by
  implies_sat [Spec.Cmac.tdesFinishContract, Spec.Cmac.tdesFinishSig, Spec.Cmac.tdesFinishPost, countArm,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [finishFrameSat, finishSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using finishFrameSat

theorem init_framed : Verified Arm.target (Impl.StackScratch.Arm.withRegScratch 640 .r3 streamInit)
    (Spec.Cmac.tdesStreamInitContract Arm.abi 640) :=
  Arm.Verified.regScratch (sig := Spec.Cmac.tdesStreamInitSig) (nm := "scratch") (e := .u64) (n := 80)
    (pre := Spec.Cmac.tdesStreamInitPre Arm.abi.ptrBits) (post := Spec.Cmac.tdesStreamInitPost Arm.abi.ptrBits)
    (wa := false) (stack := 0) init_verified (by decide) (by decide) (by decide)
    (fun vs mm m₁ m₂ r hl _ => streamInitPostOut_local _ vs mm m₁ m₂ r hl) initFrameSat_pre

theorem absorb_framed : Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 704 2 absorb)
    (Spec.Cmac.tdesAbsorbContract Arm.abi 708) :=
  Arm.Verified.stackScratch (sig := Spec.Cmac.tdesAbsorbSig) (nm := "scratch") (e := .u64) (n := 86)
    (post := Spec.Cmac.tdesAbsorbPost Arm.abi.ptrBits)
    (wa := false) (stack := 4) (m := 2) absorb_verified (by decide) (by decide) (by decide)
    (by decide) (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (absorbPost_local _)
    (fun vs mm m₁ m₂ r hl _ => absorbPostOut_local _ vs mm m₁ m₂ r hl)
    absorbFrameSat_pre

theorem finish_framed : Verified Arm.target (Impl.StackScratch.Arm.withStackScratch 656 1 finish)
    (Spec.Cmac.tdesFinishContract Arm.abi 660) :=
  Arm.Verified.stackScratch (sig := Spec.Cmac.tdesFinishSig) (nm := "scratch") (e := .u64) (n := 80)
    (post := Spec.Cmac.tdesFinishPost Arm.abi.ptrBits)
    (wa := false) (stack := 4) (m := 1) finish_verified (by decide) (by decide) (by decide)
    (by decide) (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (finishPost_local _)
    (fun vs mm m₁ m₂ r hl _ => finishPostOut_local _ vs mm m₁ m₂ r hl)
    finishFrameSat_pre

end VG.Proof.CmacTripleDes.Stream.Arm

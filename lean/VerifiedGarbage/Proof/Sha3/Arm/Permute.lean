module

public import VerifiedGarbage.Proof.Sha3.Arm.Round
public import VerifiedGarbage.Proof.Sha3.Lanes
public import VerifiedGarbage.Proof.Sha512.Arm.Rounds
public import VerifiedGarbage.Spec.Sha3.Contract
import VerifiedGarbage.Proof.Framework.Arm.Call
public import VerifiedGarbage.Impl.Sha3.Arm.Stream
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sha3.Arm.Round
meta import VerifiedGarbage.Proof.Sha3.Lanes
meta import VerifiedGarbage.Proof.Sha512.Arm.Rounds
meta import VerifiedGarbage.Spec.Sha3.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Call
meta import VerifiedGarbage.Impl.Sha3.Arm.Stream
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

@[expose] public section

section

/-!
# SHA-3: the 32-bit ARM contracts

The contracts the proofs are written against; the artifacts are emitted with
the shared contracts of `Spec/`, which imply these (`Contract.Implies`), with
the arguments where AAPCS passes them.

The return address is in `lr`, which the target's calling convention
requires to be preserved (`VG.Arm.abiPreserved`); the streaming functions
save it in their scratch space around their calls of the permutation, so
they use no stack.
-/

namespace VG.Proof.Sha3

open Spec.Sha3

open VG.Arm in
/-- 32-bit ARM contract for
`vg_keccak_f1600(state: *mut [u64; 25], scratch: *mut [u64; 64])`: applies
Keccak-f[1600] to the state at `state`.

The code may read and write `state` (200 bytes) and `scratch` (512 bytes,
whose contents on exit are unspecified), which may not overlap or wrap
around the end of the (32-bit) address space. The pointers are public; the
state is secret. -/
def permuteArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 200⟩
    let scratch : Region := ⟨State.addr (s.gpr .r1), 512⟩
    s.rd = [] ∧ s.wr = [state, scratch] ∧ state.Disjoint scratch ∧
    (s.gpr .r0).toNat + 200 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 512 ≤ 2 ^ 32
  post s s' :=
    stateAt s'.mem (State.addr (s.gpr .r0)) = keccakF (stateAt s.mem (State.addr (s.gpr .r0)))
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1

open VG.Arm in
/-- 32-bit ARM contract for `vg_keccak_absorb(state = r0, rate = r1,
pos = r2, data = r3, len = [sp], scratch = [sp, #4]) -> r0`: absorbs `data`
into the streaming state (`Repr`) and returns the new position in the
block.

The code may read the arguments on the stack (8 bytes at `sp`) and `data`,
and read and write `state` (200 bytes) and `scratch` (640 bytes). The
writable buffers may not overlap each other, the data or the arguments, and
nothing may wrap around the end of the (32-bit) address space. `rate` is one
of `rates`, and `pos < rate`. -/
def absorbArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 200⟩
    let data : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 1), 640⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    s.rd = [data, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 200 ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32 ∧
    (stackArg s 1).toNat + 640 ≤ 2 ^ 32 ∧ s.sp.toNat + 8 ≤ 2 ^ 32 ∧
    (s.gpr .r1).toNat ∈ rates ∧ (s.gpr .r2).toNat < (s.gpr .r1).toNat
  post s s' :=
    (∀ msg, Repr s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat msg →
      (s.gpr .r2).toNat = msg.length % (s.gpr .r1).toNat →
      Repr s'.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat
        (msg ++ bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat)) ∧
    (s'.gpr .r0).toNat = ((s.gpr .r2).toNat + (stackArg s 0).toNat) % (s.gpr .r1).toNat
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

open VG.Arm in
/-- 32-bit ARM contract for `vg_keccak_pad(state = r0, rate = r1, pos = r2,
suffix = r3, scratch = [sp])`: absorbs the padding (with the low byte of
`suffix`) into the streaming state.

The code may read the argument on the stack (4 bytes at `sp`), and read and
write `state` (200 bytes) and `scratch` (640 bytes), which may not overlap
each other or the argument, or wrap around the end of the (32-bit) address
space. `rate` is one of `rates`, and `pos < rate`. -/
def padArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 200⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 640⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    s.rd = [args] ∧ s.wr = [state, scratch] ∧ state.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 200 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 640 ≤ 2 ^ 32 ∧
    s.sp.toNat + 4 ≤ 2 ^ 32 ∧
    (s.gpr .r1).toNat ∈ rates ∧ (s.gpr .r2).toNat < (s.gpr .r1).toNat
  post s s' := ∀ msg, Repr s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat msg →
    (s.gpr .r2).toNat = msg.length % (s.gpr .r1).toNat →
    stateAt s'.mem (State.addr (s.gpr .r0)) =
      absorb (s.gpr .r1).toNat (pad (s.gpr .r1).toNat ((s.gpr .r3).setWidth 8) msg)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

open VG.Arm in
/-- 32-bit ARM contract for `vg_keccak_squeeze(state = r0, rate = r1,
pos = r2, out = r3, outlen = [sp], scratch = [sp, #4]) -> r0`: writes
`outlen` bytes of output from byte `pos` on to `out`, and returns the
position after them, leaving a state from which the output continues.

The code may read the arguments on the stack (8 bytes at `sp`), and read
and write `state` (200 bytes), `out` (`outlen` bytes) and `scratch` (640
bytes), which may not overlap each other or the arguments, or wrap around
the end of the (32-bit) address space. `rate` is one of `rates`, and
`pos ≤ rate`. -/
def squeezeArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 200⟩
    let out : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 1), 640⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + 200 ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32 ∧
    (stackArg s 1).toNat + 640 ≤ 2 ^ 32 ∧ s.sp.toNat + 8 ≤ 2 ^ 32 ∧
    (s.gpr .r1).toNat ∈ rates ∧ (s.gpr .r2).toNat ≤ (s.gpr .r1).toNat
  post s s' :=
    bytesAt s'.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat =
      squeezeFrom (s.gpr .r1).toNat (stateAt s.mem (State.addr (s.gpr .r0))) (s.gpr .r2).toNat
        (stackArg s 0).toNat ∧
    (s'.gpr .r0).toNat ≤ (s.gpr .r1).toNat ∧
    ∀ d, squeezeFrom (s.gpr .r1).toNat (stateAt s'.mem (State.addr (s.gpr .r0))) (s'.gpr .r0).toNat d =
      squeezeFrom (s.gpr .r1).toNat (stateAt s.mem (State.addr (s.gpr .r0)))
        ((s.gpr .r2).toNat + (stackArg s 0).toNat) d
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

end VG.Proof.Sha3

end

section

/-!
# Keccak-f[1600] on ARMv7: one round

One round (`round src dst`) from the interleaved state at `src` to the one
at `dst`: θ, ρ, π and χ by evaluation (`core_ok`,
`Proof/Sha3/Arm/Round.lean`), then ι on the two words of lane 0, proved
once for both of the rounds of an iteration (`src`, `dst` being `r1`, `r0`
or `r0`, `r1`).
-/

namespace VG.Proof.Sha3.Arm

open VG VG.Arm VG.Impl.Sha3.Arm
open VG.Arm.Straight (wordAddr Ok checkN slot_sep slot_contains)
open VG.Bitslice.Anf (anf32)
open VG.Proof.Sha512.Arm (A contains_A mem_rd wp_eor)
open VG.Proof.MdStream.Arm (Upd Mupd wp_ldr wp_str wp_add op2_reg op2_imm)
open VG.Proof.Sha3 (out outState)

/-- The 32-bit region of `n` bytes at `b`. -/
abbrev regR (b : BitVec 32) (n : Nat) : Region := ⟨State.addr b, n⟩

/-- Where ι reads and writes: the pointer at `Sc + rcPtr` to the round
constant and the round constant at `P`, neither in the state at `Dd`. -/
structure Env (wr : List Region) (Dd Sc P : BitVec 32) : Prop where
  fitD : Dd.toNat + 200 ≤ 2 ^ 32
  in_dst : ∀ o, o + 4 ≤ 200 → InRegions wr (A Dd o) 4
  ptr_in : InRegions wr (A Sc rcPtr) 4
  rc_in : ∀ o, o = 0 ∨ o = 4 → InRegions wr (A P o) 4
  ptr_dst : Region.Disjoint ⟨A Sc rcPtr, 4⟩ (regR Dd 200)
  rc_dst : ∀ o, o = 0 ∨ o = 4 → Region.Disjoint ⟨A P o, 4⟩ (regR Dd 200)

/-- The words of the state at `Dd` after ι's three stores. -/
theorem Env.readW_iota {wr : List Region} {Dd Sc P : BitVec 32} (E : Env wr Dd Sc P) (m : Mem)
    (v₀ v₁ vp : BitVec 32) :
    (((m.writeW (A Dd 0) v₀).writeW (A Dd 4) v₁).writeW (A Sc rcPtr) vp).readW (A Dd 0) 32 = v₀ ∧
    (((m.writeW (A Dd 0) v₀).writeW (A Dd 4) v₁).writeW (A Sc rcPtr) vp).readW (A Dd 4) 32 = v₁ ∧
    ∀ k, 2 ≤ k → k < 50 →
      (((m.writeW (A Dd 0) v₀).writeW (A Dd 4) v₁).writeW (A Sc rcPtr) vp).readW (wordAddr Dd k) 32 =
        m.readW (wordAddr Dd k) 32 := by
  have fD := E.fitD
  have sp : ∀ {k : Nat}, k < 50 → Mem.Sep (wordAddr Dd k) (32 / 8) (A Sc rcPtr) (32 / 8) := fun hk =>
    E.ptr_dst.symm.sep (slot_contains Dd (n := 50) hk (by omega_using [fD])) (Region.contains_self _ _)
  have s0 : ∀ {k : Nat}, k < 50 → k ≠ 0 → Mem.Sep (wordAddr Dd k) (32 / 8) (A Dd 0) (32 / 8) :=
    fun hk h => slot_sep Dd (k := 0) (by omega_using [fD, hk]) (by omega_using [fD]) h
  have s1 : ∀ {k : Nat}, k < 50 → k ≠ 1 → Mem.Sep (wordAddr Dd k) (32 / 8) (A Dd 4) (32 / 8) :=
    fun hk h => slot_sep Dd (k := 1) (by omega_using [fD, hk]) (by omega_using [fD]) h
  refine ⟨?_, ?_, fun k h2 hk => ?_⟩
  · rw [Mem.readW_writeW_sep (a := A Dd 0) (sp (k := 0) (by decide)) (by decide),
      Mem.readW_writeW_sep (a := A Dd 0) (s1 (k := 0) (by decide) (by decide)) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · rw [Mem.readW_writeW_sep (a := A Dd 4) (sp (k := 1) (by decide)) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  · rw [Mem.readW_writeW_sep (sp hk) (by decide),
      Mem.readW_writeW_sep (s1 hk (by omega_using [h2])) (by decide),
      Mem.readW_writeW_sep (s0 hk (by omega_using [h2])) (by decide)]

/-- ι on the two words of lane 0 of the state at `dst`, and the pointer to
the round constant advanced. -/
theorem iota_ok {dst : Reg} (hdst : dst = .r0 ∨ dst = .r1) {Dd Sc P : BitVec 32} (s : State)
    (E : Env s.wr Dd Sc P) (hd : s.gpr dst = Dd) (h1 : s.gpr .r1 = Sc)
    (hP : s.mem.readW (A Sc rcPtr) 32 = P) :
    WP isa (.block (iota dst)) s fun s' =>
      s'.mem = ((s.mem.writeW (A Dd 0) (s.mem.readW (A Dd 0) 32 ^^^ s.mem.readW (A P 0) 32)).writeW
        (A Dd 4) (s.mem.readW (A Dd 4) 32 ^^^ s.mem.readW (A P 4) 32)).writeW (A Sc rcPtr) (P + 8) ∧
      (∀ q ∈ [Reg.r0, .r1], s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have fD := E.fitD
  have dT : dst ≠ T ∧ dst ≠ U ∧ dst ≠ breg 0 := by rcases hdst with rfl | rfl <;> decide
  obtain ⟨dT, dU, dB⟩ := dT
  unfold iota
  refine wp_ldr (a := A Sc rcPtr) (by decide) (by rw [h1]) (mem_rd E.ptr_in) fun s₁ u₁ => ?_
  refine wp_ldr (a := A Dd 0) (by decide) (by rw [u₁.other dst dT, hd])
    (by rw [u₁.rd, u₁.wr]; exact mem_rd (E.in_dst _ (by decide))) fun s₂ u₂ => ?_
  refine wp_ldr (a := A P 0) (by decide) (by rw [u₂.other T (by decide), u₁.gpr, hP])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact mem_rd (E.rc_in 0 (.inl rfl))) fun s₃ u₃ => ?_
  refine wp_eor (op2_reg _ _) fun s₄ u₄ => ?_
  have w₄ : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have r₄ : s₄.rd = s.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have g₄ : ∀ q, q ≠ T → q ≠ U → q ≠ breg 0 → s₄.gpr q = s.gpr q := fun q a b c => by
    rw [u₄.other q b, u₃.other q c, u₂.other q b, u₁.other q a]
  have t₄ : s₄.gpr T = P := by
    rw [u₄.other T (by decide), u₃.other T (by decide), u₂.other T (by decide), u₁.gpr, hP]
  have v₄ : s₄.gpr U = s.mem.readW (A Dd 0) 32 ^^^ s.mem.readW (A P 0) 32 := by
    rw [u₄.gpr, u₃.other U (by decide), u₃.gpr, u₂.gpr, u₂.mem, u₁.mem]
  refine wp_str (a := A Dd 0) (by decide) (by rw [g₄ dst dT dU dB, hd])
    (by rw [w₄]; exact E.in_dst _ (by decide)) fun s₅ u₅ => ?_
  rw [m₄, v₄] at u₅
  generalize s.mem.readW (A Dd 0) 32 ^^^ s.mem.readW (A P 0) 32 = v₀ at u₅ ⊢
  refine wp_ldr (a := A Dd 4) (by decide) (by rw [u₅.gpr, g₄ dst dT dU dB, hd])
    (by rw [u₅.rd, u₅.wr, r₄, w₄]; exact mem_rd (E.in_dst _ (by decide))) fun s₆ u₆ => ?_
  refine wp_ldr (a := A P 4) (by decide) (by rw [u₆.other T (by decide), u₅.gpr, t₄])
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, r₄, w₄]; exact mem_rd (E.rc_in 4 (.inr rfl))) fun s₇ u₇ => ?_
  refine wp_eor (op2_reg _ _) fun s₈ u₈ => ?_
  have v₈ : s₈.gpr U = s.mem.readW (A Dd 4) 32 ^^^ s.mem.readW (A P 4) 32 := by
    have s10 : Mem.Sep (A Dd 4) (32 / 8) (A Dd 0) (32 / 8) :=
      slot_sep Dd (j := 1) (k := 0) (by omega_using [fD]) (by omega_using [fD]) (by decide)
    rw [u₈.gpr, u₇.other U (by decide), u₇.gpr, u₆.gpr, u₆.mem, u₅.mem, Mem.readW_writeW_sep s10 (by decide),
      Mem.readW_writeW_sep ((E.rc_dst 4 (.inr rfl)).sep (Region.contains_self _ _)
        (contains_A fD (by decide))) (by decide)]
  have g₈ : ∀ q, q ≠ T → q ≠ U → q ≠ breg 0 → s₈.gpr q = s.gpr q := fun q a b c => by
    rw [u₈.other q b, u₇.other q c, u₆.other q b, u₅.gpr, g₄ q a b c]
  refine wp_str (a := A Dd 4) (by decide) (by rw [g₈ dst dT dU dB, hd])
    (by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, w₄]; exact E.in_dst _ (by decide)) fun s₉ u₉ => ?_
  rw [v₈, u₈.mem, u₇.mem, u₆.mem, u₅.mem] at u₉
  refine wp_add (op2_imm (by decide)) fun s₁₀ u₁₀ => ?_
  refine wp_str (a := A Sc rcPtr) (by decide)
    (by rw [u₁₀.other .r1 (by decide), u₉.gpr, g₈ .r1 (by decide) (by decide) (by decide), h1])
    (by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, w₄]; exact E.ptr_in) fun s₁₁ u₁₁ =>
      WP.block_nil ⟨?_, fun q hq => ?_, ?_, ?_, ?_⟩
  · rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₁₀.gpr, u₉.gpr, u₈.other T (by decide), u₇.other T (by decide),
      u₆.other T (by decide), u₅.gpr, t₄]
  · have hq' : q ≠ T ∧ q ≠ U ∧ q ≠ breg 0 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;> decide
    rw [u₁₁.gpr, u₁₀.other q hq'.1, u₉.gpr, g₈ q hq'.1 hq'.2.1 hq'.2.2]
  · rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, r₄]
  · rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, w₄]
  · rw [u₁₁.sp, u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]

/-- ι is on lane 0 alone. -/
theorem out_iota (K : KState) (rc : Lane) (x y : Nat) :
    out K rc x y = if x = 0 ∧ y = 0 then out K 0 x y ^^^ rc else out K 0 x y := by
  unfold out; split <;> simp

/-- Lane 0 of the round's output, from its output without ι. -/
theorem outState_zero (K : KState) (rc : Lane) : (outState K rc)[0]! = out K 0 0 0 ^^^ rc := by
  rw [show (outState K rc)[0]! = out K rc 0 0 by simp [outState], out_iota]
  rfl

theorem outState_pos (K : KState) (rc : Lane) {j : Nat} (h0 : j ≠ 0) (hj : j < 25) :
    (outState K rc)[j]! = out K 0 (j % 5) (j / 5) := by
  rw [show (outState K rc)[j]! = out K rc (j % 5) (j / 5) by simp [outState, hj], out_iota,
    ite_eq_right_of_eq_false _ _ (eq_false (by omega_using [h0]))]

theorem round_ok {src dst : Reg} (hc : checkN anf32 (cfg src dst) atoms (roundCore src dst) env₀ post = true)
    (hsd : (src = .r0 ∧ dst = .r1) ∨ (src = .r1 ∧ dst = .r0)) {Dd Sc P : BitVec 32} {K : KState}
    {rc : Lane} (s : State) (hok : Ok (cfg src dst) s) (E : Env s.wr Dd Sc P) (hd : s.gpr dst = Dd)
    (h1 : s.gpr .r1 = Sc) (hK : Stored s.mem (s.gpr src) K) (hP : s.mem.readW (A Sc rcPtr) 32 = P)
    (hrc : s.mem.readW (A P 0) 32 = half 0 rc ∧ s.mem.readW (A P 4) 32 = half 1 rc) :
    WP isa (.block (round src dst)) s fun s' =>
      Stored s'.mem Dd (outState K rc) ∧ Frame [regR Dd 200, ⟨A Sc rcPtr, 4⟩] s.mem s'.mem ∧
      s'.mem.readW (A Sc rcPtr) 32 = P + 8 ∧ (∀ q ∈ [Reg.r0, .r1], s'.gpr q = s.gpr q) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have fD := E.fitD
  obtain ⟨s₁, hs₁, hw, hrd, hwr, hsp, hsrc, hdst, hf⟩ := core_ok hc hok hK
  rw [hd] at hw hf
  have g₁ : ∀ q ∈ [Reg.r0, .r1], s₁.gpr q = s.gpr q := fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hsd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hq with rfl | rfl <;> with_reducible assumption
  have keep : ∀ {a : Addr}, Region.Disjoint ⟨a, 4⟩ (regR Dd 200) → s₁.mem.readW a 32 = s.mem.readW a 32 :=
    fun h => hf.readW (Region.contains_self _ _) (by simpa using h) (by decide)
  have w₀ : s₁.mem.readW (A Dd 0) 32 = half 0 (out K 0 0 0) := (hw 0 (by decide)).trans (stw_zero _ _)
  have w₁ : s₁.mem.readW (A Dd 4) 32 = half 1 (out K 0 0 0) := (hw 1 (by decide)).trans (stw_zero _ _)
  unfold round
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, hs₁, ?_⟩
  refine WP.mono (iota_ok (hsd.elim (fun h => .inr h.2) (fun h => .inl h.2)) s₁ (hwr ▸ E)
    (by rw [hdst, hd]) (by rw [g₁ .r1 (by simp), h1]) (by rw [keep E.ptr_dst, hP]))
    fun s₂ ⟨hm, hq, hrd₂, hwr₂, hsp₂⟩ => ⟨fun j hj h hh => ?_, ?_, ?_, fun q hq' => ?_, hrd₂.trans hrd,
      hwr₂.trans hwr, hsp₂.trans hsp⟩
  · rw [w₀, w₁, keep (E.rc_dst 0 (.inl rfl)), keep (E.rc_dst 4 (.inr rfl)), hrc.1, hrc.2, ← half_xor,
      ← half_xor] at hm
    obtain ⟨r₀, r₁, r₂⟩ := E.readW_iota s₁.mem (half 0 (out K 0 0 0 ^^^ rc)) (half 1 (out K 0 0 0 ^^^ rc))
      (P + 8)
    rw [← hm] at r₀ r₁ r₂
    by_cases hj0 : j = 0
    · subst hj0
      rw [outState_zero, stw_zero]
      have e : h = 0 ∨ h = 1 := by omega_using [hh]
      rcases e with rfl | rfl
      · exact r₀
      · exact r₁
    · rw [r₂ _ (by omega_using [hj0]) (by omega_using [hj, hh]), hw _ (by omega_using [hj, hh]),
        outState_pos K rc hj0 hj, show (2 * j + h) / 2 = j by omega_using [hh],
        show (2 * j + h) % 2 = h by omega_using [hh]]
  · rw [hm]
    exact (((hf.mono (by simp)).writeW (r := regR Dd 200) (by simp) _ (contains_A fD (by decide))).writeW
      (r := regR Dd 200) (by simp) _ (contains_A fD (by decide))).writeW (r := ⟨A Sc rcPtr, 4⟩) (by simp) _
      (Region.contains_self _ _)
  · rw [hm, Mem.readW_writeW_self32]
  · rw [hq q hq', g₁ q hq']

end VG.Proof.Sha3.Arm

end

/-!
# Keccak-f[1600] on ARMv7: the whole function

The prologue saves the callee-saved registers, interleaves the lanes of the
state into the scratch space (`enter_ok`) and stores the round constants
there; each iteration of the loop runs two rounds (`round_ok`), from the
state in the scratch space to the one at `state` and back; the epilogue
brings the lanes back to `state` (`leave_ok`) and restores the registers.
-/

namespace VG.Proof.Sha3.Arm

open VG VG.Arm VG.Impl.Sha3.Arm
open VG.Arm.Straight (wordAddr Ok Cfg)
open VG.Spec.Sha3 (stateAt keccakF rnd RC)
open VG.Proof.Sha512.Arm (rd64 A A_eq contains_A readW64 mem_rd rd64_frame)
open VG.Proof.MdStream.Arm (Upd Mupd wp_add wp_sub wp_ldr wp_str wp_cmp op2_reg op2_imm eval_ne
  sub_beq readW_writeW_save)
open VG.Proof.Sha3 (outState_eq foldl_succ off_disjoint sub_offset add_zero')

/-! ## Addresses -/

section
variable (s₀ : State)

abbrev stp : BitVec 32 := s₀.gpr .r0
abbrev scp : BitVec 32 := s₀.gpr .r1
abbrev A₀ : KState := stateAt s₀.mem (State.addr (stp s₀))

/-- The state the rounds read from before round `r`, and the one they write. -/
def cur (r : Nat) : BitVec 32 := if r % 2 = 0 then scp s₀ else stp s₀
def oth (r : Nat) : BitVec 32 := if r % 2 = 0 then stp s₀ else scp s₀

/-- The address of the constant of round `r`. -/
abbrev rcp (r : Nat) : BitVec 32 := scp s₀ + BitVec.ofNat 32 (200 + 8 * r)

end

theorem cur_succ (s₀ : State) (r : Nat) : cur s₀ (r + 1) = oth s₀ r := by
  simp only [cur, oth]; split <;> split <;> first | rfl | omega_arith

theorem cur_even (s₀ : State) (t : Nat) : cur s₀ (2 * t) = scp s₀ ∧ oth s₀ (2 * t) = stp s₀ := by
  simp only [cur, oth]; split
  · exact ⟨rfl, rfl⟩
  · omega_arith

theorem cur_odd (s₀ : State) (t : Nat) : cur s₀ (2 * t + 1) = stp s₀ ∧ oth s₀ (2 * t + 1) = scp s₀ := by
  simp only [cur, oth]; split
  · omega_arith
  · exact ⟨rfl, rfl⟩

theorem A_add (b : BitVec 32) (a o : Nat) : A (b + BitVec.ofNat 32 a) o = A b (a + o) := by
  simp only [A]; rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem rcp_succ (s₀ : State) (r : Nat) : rcp s₀ r + 8 = rcp s₀ (r + 1) := by
  simp only [rcp]
  bv_omega

/-- Word `k` from `b`, as an offset. -/
theorem wordAddr_eq (b : BitVec 32) (k : Nat) : wordAddr b k = A b (4 * k) := rfl

/-- Half `h` of the constant of round `r` is a word of the scratch space. -/
theorem rc_addr (s₀ : State) (r h : Nat) : A (rcp s₀ r) (4 * h) = wordAddr (scp s₀) (50 + (2 * r + h)) := by
  rw [A_add, wordAddr_eq, show 4 * (50 + (2 * r + h)) = 200 + 8 * r + 4 * h by omega_arith]

/-- A lane, from its two words. -/
theorem lane_words (m : Mem) (b : BitVec 32) (j : Nat) :
    (m.readW (wordAddr b (2 * j + 1)) 32 ++ m.readW (wordAddr b (2 * j)) 32 : BitVec 64) = rd64 m b (8 * j) := by
  rw [wordAddr_eq, wordAddr_eq, show 4 * (2 * j + 1) = 8 * j + 4 by omega_arith,
    show 4 * (2 * j) = 8 * j by omega_arith]
  rfl

theorem addr_toNat (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := a.isLt; omega_arith)

/-! ## The precondition -/

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [regR (stp s₀) 200, regR (scp s₀) 512]
  disj : (regR (stp s₀) 200).Disjoint (regR (scp s₀) 512)
  fitS : (stp s₀).toNat + 200 ≤ 2 ^ 32
  fitC : (scp s₀).toNat + 512 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : Proof.Sha3.permuteArm.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem scA {d : Nat} (hd : d < 512) : A (scp s₀) d = State.addr (scp s₀) + BitVec.ofNat 64 d :=
  A_eq (by have := h.fitC; omega_arith)

theorem scr_in {d : Nat} (hd : d + 4 ≤ 512) : InRegions s₀.wr (A (scp s₀) d) 4 :=
  ⟨_, by rw [h.wr]; simp, contains_A h.fitC hd⟩

theorem scr_disj {a n b k : Nat} (ha : a + n ≤ 512) (hb : b + k ≤ 512) (hs : a + n ≤ b ∨ b + k ≤ a)
    (hn : 0 < n) (hk : 0 < k) : Region.Disjoint ⟨A (scp s₀) a, n⟩ ⟨A (scp s₀) b, k⟩ := by
  rw [h.scA (by omega_arith), h.scA (by omega_arith)]
  exact off_disjoint _ (by omega_arith) (by omega_arith) hs

theorem off_st {d n : Nat} (hd : d + n ≤ 512) (hn : 0 < n) :
    Region.Disjoint ⟨A (scp s₀) d, n⟩ (regR (stp s₀) 200) := by
  have hs : Region.Sub ⟨A (scp s₀) d, n⟩ (regR (scp s₀) 512) := by
    rw [h.scA (by omega_arith)]; exact sub_offset hd (by omega_arith)
  exact h.disj.symm.sub_left hs

/-- A part of the scratch space after its first `k` bytes. -/
theorem off_scr {d n k : Nat} (hd₀ : k ≤ d) (hd : d + n ≤ 512) (hn : 0 < n) :
    Region.Disjoint ⟨A (scp s₀) d, n⟩ (regR (scp s₀) k) := by
  have := off_disjoint (State.addr (scp s₀)) (a := d) (n := n) (b := 0) (k := k) (by omega_arith)
    (by omega_arith) (.inr (by omega_arith))
  rw [add_zero'] at this
  rw [h.scA (by omega_arith)]; exact this

theorem off_dst {Dd : BitVec 32} (hD : Dd = stp s₀ ∨ Dd = scp s₀) {d n : Nat} (hd₀ : 200 ≤ d)
    (hd : d + n ≤ 512) (hn : 0 < n) : Region.Disjoint ⟨A (scp s₀) d, n⟩ (regR Dd 200) := by
  rcases hD with rfl | rfl
  · exact h.off_st hd hn
  · exact h.off_scr hd₀ hd hn

/-- The state at `state` as the slots, the scratch space as the external words. -/
theorem ok_st {s : State} (hwr : s.wr = s₀.wr) (h0 : s.gpr .r0 = stp s₀) (h1 : s.gpr .r1 = scp s₀) :
    Ok (cfg .r1 .r0) s :=
  ok_of (lb := 200) (le := 512) h0 h1 (by rw [hwr, h.wr]; simp) (by rw [hwr, h.wr]; simp) h.fitS h.fitC
    (by decide) (by decide) h.disj

/-- The scratch space as the slots, the state at `state` as the external words. -/
theorem ok_sc {s : State} (hwr : s.wr = s₀.wr) (h0 : s.gpr .r0 = stp s₀) (h1 : s.gpr .r1 = scp s₀)
    {c : Cfg} (hb : c.base = .r1) (he : c.ext = .r0) (hs : 4 * c.slots ≤ 512) (hx : 4 * c.exts ≤ 200) :
    Ok c s :=
  ok_of (lb := 512) (le := 200) (by rw [hb, h1]) (by rw [he, h0]) (by rw [hwr, h.wr]; simp)
    (by rw [hwr, h.wr]; simp) h.fitC h.fitS hs hx h.disj.symm

theorem env_of {Dd : BitVec 32} (hD : Dd = stp s₀ ∨ Dd = scp s₀) {r : Nat} (hr : r < 24) :
    Env s₀.wr Dd (scp s₀) (rcp s₀ r) := by
  have fS := h.fitS
  have fC := h.fitC
  refine ⟨?_, fun o ho => ?_, h.scr_in (d := rcPtr) (by decide), fun o ho => ?_,
    h.off_dst hD (d := rcPtr) (by decide) (by decide) (by decide), fun o ho => ?_⟩
  · rcases hD with rfl | rfl <;> omega_arith
  · rcases hD with rfl | rfl
    · exact ⟨_, by rw [h.wr]; simp, contains_A fS ho⟩
    · exact h.scr_in (by omega_arith)
  · rw [A_add]; exact h.scr_in (by rcases ho with rfl | rfl <;> omega_arith)
  · rw [A_add]; exact h.off_dst hD (by omega_arith) (by rcases ho with rfl | rfl <;> omega_arith) (by decide)

end Pre

/-! ## What the scratch space holds -/

/-- The round constants, interleaved. -/
def Aux (s₀ : State) (m : Mem) : Prop :=
  ∀ i < 48, m.readW (wordAddr (scp s₀) (50 + i)) 32 = half (i % 2) (RC (i / 2))

/-- The saved registers. -/
def Saved (s₀ : State) (m : Mem) : Prop := ∀ p ∈ saved, m.readW (A (scp s₀) p.2) 32 = s₀.gpr p.1

theorem saved_ok : ∀ p ∈ saved, p.1 ≠ .r1 ∧ p.2 < 4096 ∧ 396 ≤ p.2 ∧ p.2 + 4 ≤ 432 := by decide

theorem Aux.keep {s₀ : State} {m m' : Mem} (ha : Aux s₀ m)
    (hk : ∀ d, 200 ≤ d → d + 4 ≤ 392 → m'.readW (A (scp s₀) d) 32 = m.readW (A (scp s₀) d) 32) :
    Aux s₀ m' := fun i hi =>
  (hk (4 * (50 + i)) (by omega_arith) (by omega_arith)).trans (ha i hi)

/-- The constant of round `r`. -/
theorem Aux.rc {s₀ : State} {m : Mem} (ha : Aux s₀ m) {r : Nat} (hr : r < 24) :
    m.readW (A (rcp s₀ r) 0) 32 = half 0 (RC r) ∧ m.readW (A (rcp s₀ r) 4) 32 = half 1 (RC r) := by
  have h0 := ha (2 * r + 0) (by omega_arith)
  have h1 := ha (2 * r + 1) (by omega_arith)
  rw [← rc_addr, show (2 * r + 0) % 2 = 0 by omega_arith, show (2 * r + 0) / 2 = r by omega_arith] at h0
  rw [← rc_addr, show (2 * r + 1) % 2 = 1 by omega_arith, show (2 * r + 1) / 2 = r by omega_arith] at h1
  exact ⟨h0, h1⟩

theorem Saved.keep {s₀ : State} {m m' : Mem} (hs : Saved s₀ m)
    (hk : ∀ d, 396 ≤ d → d + 4 ≤ 432 → m'.readW (A (scp s₀) d) 32 = m.readW (A (scp s₀) d) 32) :
    Saved s₀ m' := fun p hp => by
  obtain ⟨-, -, h1, h2⟩ := saved_ok p hp
  rw [hk _ h1 h2]; exact hs p hp

theorem readW_writeW_A (m : Mem) {b : BitVec 32} {N : Nat} (hfit : b.toNat + N ≤ 2 ^ 32) (v : BitVec 32)
    {d e : Nat} (hd : d + 4 ≤ N) (he : e + 4 ≤ N) (hs : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (A b e) v).readW (A b d) 32 = m.readW (A b d) 32 := by
  rw [A_eq (by omega_arith), A_eq (by omega_arith)]; exact readW_writeW_save m _ v (by omega_arith) (by omega_arith) hs

/-- Words the rounds do not write. -/
theorem Pre.keep_round {s₀ : State} (hp : Pre s₀) {Dd : BitVec 32} (hD : Dd = stp s₀ ∨ Dd = scp s₀)
    {m m' : Mem} (hf : Frame [regR Dd 200, ⟨A (scp s₀) rcPtr, 4⟩] m m') {d : Nat} (hd : 200 ≤ d)
    (hd' : d + 4 ≤ 512) (hne : d + 4 ≤ 392 ∨ 396 ≤ d) :
    m'.readW (A (scp s₀) d) 32 = m.readW (A (scp s₀) d) 32 := by
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.off_dst hD hd hd' (by decide)
  · exact hp.scr_disj hd' (by decide) (by simp only [rcPtr]; omega_arith) (by decide) (by decide)

/-! ## The state in memory -/

theorem stateAt_get {b : BitVec 32} (hfit : b.toNat + 200 ≤ 2 ^ 32) (m : Mem) {i : Nat} (hi : i < 25) :
    (stateAt m (State.addr b))[i] = rd64 m b (8 * i) := by
  simp only [stateAt, Vector.getElem_ofFn, rd64]
  rw [readW64, A_eq (by omega_arith), A_eq (by omega_arith),
    show State.addr b + BitVec.ofNat 64 (8 * i) + 4 = State.addr b + BitVec.ofNat 64 (8 * i + 4) by
      bv_omega]

/-- The state at `b`, from its lanes. -/
theorem stateAt_eq {b : BitVec 32} (hfit : b.toNat + 200 ≤ 2 ^ 32) {m : Mem} {K : KState}
    (h : ∀ j < 25, rd64 m b (8 * j) = K[j]!) : stateAt m (State.addr b) = K := by
  apply Vector.ext
  intro i hi
  rw [stateAt_get hfit m hi, h i hi]
  exact getElem!_pos K i hi

/-! ## The rounds -/

/-- The loop's invariant, before round `r`. -/
structure LInv (s₀ : State) (r : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = stp s₀
  r1 : s.gpr .r1 = scp s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  ptr : s.mem.readW (A (scp s₀) rcPtr) 32 = rcp s₀ r
  state : Stored s.mem (cur s₀ r) ((List.range r).foldl rnd (A₀ s₀))
  aux : Aux s₀ s.mem
  saved : Saved s₀ s.mem
  frame : Frame [regR (stp s₀) 200, regR (scp s₀) 512] s₀.mem s.mem

theorem round_step {s₀ : State} (hp : Pre s₀) {r : Nat} (hr : r < 24) {src dst : Reg}
    (hc : Straight.checkN Bitslice.Anf.anf32 (cfg src dst) atoms (roundCore src dst) env₀ post = true)
    (hsd : (src = .r0 ∧ dst = .r1) ∨ (src = .r1 ∧ dst = .r0)) {s : State} (hL : LInv s₀ r s)
    (h0 : s.gpr src = cur s₀ r) (hd : s.gpr dst = oth s₀ r) :
    WP isa (.block (round src dst)) s (LInv s₀ (r + 1)) := by
  have hD : oth s₀ r = stp s₀ ∨ oth s₀ r = scp s₀ := by
    rcases hsd with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact .inr (hd.symm.trans hL.r1)
    · exact .inl (hd.symm.trans hL.r0)
  have hok : Ok (cfg src dst) s := by
    rcases hsd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hp.ok_sc hL.wr hL.r0 hL.r1 rfl rfl (by decide) (by decide)
    · exact hp.ok_st hL.wr hL.r0 hL.r1
  have E : Env s.wr (oth s₀ r) (scp s₀) (rcp s₀ r) := hL.wr ▸ hp.env_of hD hr
  refine WP.mono (round_ok hc hsd (K := (List.range r).foldl rnd (A₀ s₀)) (rc := RC r) s hok E hd hL.r1
    (by rw [h0]; exact hL.state) hL.ptr
    (hL.aux.rc hr)) fun s' ⟨hl, hf, hptr, hq, hrd, hwr, hsp⟩ => ?_
  refine ⟨by rw [hq .r0 (by simp), hL.r0], by rw [hq .r1 (by simp), hL.r1], hrd.trans hL.rd,
    hwr.trans hL.wr, hsp.trans hL.sp, by rw [hptr, rcp_succ], ?_,
    hL.aux.keep fun d hd hd' => hp.keep_round hD hf hd (by omega_arith) (.inl hd'),
    hL.saved.keep fun d hd hd' => hp.keep_round hD hf (by omega_arith) (by omega_arith) (.inr hd), ?_⟩
  · rw [cur_succ, foldl_succ, ← outState_eq]; exact hl
  · refine hL.frame.trans (hf.sub fun R hR => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    · rcases hD with e | e <;> rw [e]
      · exact ⟨regR (stp s₀) 200, by simp, fun _ h => h⟩
      · exact ⟨regR (scp s₀) 512, by simp, Region.sub_prefix (by omega_arith)⟩
    · refine ⟨regR (scp s₀) 512, by simp, ?_⟩
      rw [hp.scA (by decide)]; exact sub_offset (by decide) (by decide)

theorem body_ok {s₀ : State} (hp : Pre s₀) {t : Nat} (ht : t < 12) {s : State} (hL : LInv s₀ (2 * t) s) :
    WP isa (.block body) s fun s' =>
      (eval .ne s' = some false ∧ LInv s₀ 24 s') ∨
      (eval .ne s' = some true ∧ t + 1 < 12 ∧ LInv s₀ (2 * (t + 1)) s') := by
  unfold body
  rw [WP.block_append_iff]
  refine WP.mono (round_step hp (r := 2 * t) (by omega_arith) coreA_ok (.inr ⟨rfl, rfl⟩) hL
    (by rw [hL.r1, (cur_even s₀ t).1]) (by rw [hL.r0, (cur_even s₀ t).2])) fun s₁ h₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (round_step hp (r := 2 * t + 1) (by omega_arith) coreB_ok (.inl ⟨rfl, rfl⟩) h₁
    (by rw [h₁.r0, (cur_odd s₀ t).1]) (by rw [h₁.r1, (cur_odd s₀ t).2])) fun s₂ h₂ => ?_
  have h₂' : LInv s₀ (2 * (t + 1)) s₂ := by rw [show 2 * (t + 1) = 2 * t + 1 + 1 by omega_arith]; exact h₂
  refine wp_ldr (a := A (scp s₀) rcPtr) (by decide) (by rw [h₂.r1])
    (by rw [h₂.rd, h₂.wr]; exact mem_rd (hp.scr_in (by decide))) fun s₃ u₃ => ?_
  refine wp_sub (op2_reg _ _) fun s₄ u₄ => wp_cmp (op2_imm (by decide)) fun s₅ u₅ hz => WP.block_nil ?_
  have hT : s₄.gpr T = BitVec.ofNat 32 (216 + 16 * t) := by
    rw [u₄.gpr, u₃.gpr, u₃.other .r1 (by decide), h₂'.ptr, h₂.r1]
    show scp s₀ + _ - scp s₀ = _
    rw [BitVec.add_comm, BitVec.add_sub_cancel, show 200 + 8 * (2 * (t + 1)) = 216 + 16 * t by omega_arith]
  rw [hT, show (392 : BitVec 32) = BitVec.ofNat 32 392 from rfl,
    VG.Proof.MdStream.Arm.sub_beq (by omega_arith) (by omega_arith)] at hz
  have hs₅ : LInv s₀ (2 * (t + 1)) s₅ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₅.gpr, u₄.other .r0 (by decide), u₃.other .r0 (by decide), h₂'.r0]
    · rw [u₅.gpr, u₄.other .r1 (by decide), u₃.other .r1 (by decide), h₂'.r1]
    · rw [u₅.rd, u₄.rd, u₃.rd, h₂'.rd]
    · rw [u₅.wr, u₄.wr, u₃.wr, h₂'.wr]
    · rw [u₅.sp, u₄.sp, u₃.sp, h₂'.sp]
    · rw [u₅.mem, u₄.mem, u₃.mem, h₂'.ptr]
    · rw [u₅.mem, u₄.mem, u₃.mem]; exact h₂'.state
    · rw [u₅.mem, u₄.mem, u₃.mem]; exact h₂'.aux
    · rw [u₅.mem, u₄.mem, u₃.mem]; exact h₂'.saved
    · rw [u₅.mem, u₄.mem, u₃.mem]; exact h₂'.frame
  by_cases hlast : t + 1 = 12
  · refine .inl ⟨by rw [eval_ne, hz, decide_eq_true (by omega_arith)]; rfl, ?_⟩
    rw [show 24 = 2 * (t + 1) by omega_arith]; exact hs₅
  · exact .inr ⟨by rw [eval_ne, hz, decide_eq_false (by omega_arith)]; rfl, by omega_arith, hs₅⟩

/-! ## The prologue -/

/-- The memory after storing the registers `l` (values `g`) at `b + offset`. -/
def saveMemA (m : Mem) (b : BitVec 32) (g : Reg → BitVec 32) : List (Reg × Nat) → Mem
  | [] => m
  | p :: l => saveMemA (m.writeW (A b p.2) (g p.1)) b g l

theorem saveA_ok {bR : Reg} {rest : List Instr} (l : List (Reg × Nat)) :
    ∀ (s : State) (Q : State → Prop),
    (∀ p ∈ l, p.2 < 4096 ∧ InRegions s.wr (A (s.gpr bR) p.2) 4) →
    (∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = saveMemA s.mem (s.gpr bR) s.gpr l → WP isa (.block rest) s' Q) →
    WP isa (.block (l.map (fun p => Instr.str p.1 bR p.2) ++ rest)) s Q := by
  induction l with
  | nil => intro s Q _ k; exact k s rfl rfl rfl rfl rfl
  | cons p l ih =>
    intro s Q hl k
    obtain ⟨h1, h3⟩ := hl p (by simp)
    refine wp_str h1 rfl h3 fun s₁ u₁ => ?_
    refine ih s₁ Q (fun q hq => ?_) fun s' g rd wr sp m => k s' (g.trans u₁.gpr) (rd.trans u₁.rd)
      (wr.trans u₁.wr) (sp.trans u₁.sp) ?_
    · rw [u₁.gpr, u₁.wr]; exact hl q (List.mem_cons_of_mem _ hq)
    · rw [m, u₁.mem, u₁.gpr]; rfl

theorem saveMemA_frame {b : BitVec 32} {N : Nat} (hfit : b.toNat + N ≤ 2 ^ 32) (g : Reg → BitVec 32) :
    ∀ (l : List (Reg × Nat)) (m : Mem), (∀ p ∈ l, p.2 + 4 ≤ N) →
      Frame [regR b N] m (saveMemA m b g l) := by
  intro l
  induction l with
  | nil => intro m _; exact Frame.refl _ _
  | cons p l ih =>
    intro m hl
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_A hfit (hl p (by simp)))).trans
      (ih _ fun q hq => hl q (List.mem_cons_of_mem _ hq))

set_option simprocs false in
theorem saveMemA_saved (m : Mem) {b : BitVec 32} (hfit : b.toNat + 512 ≤ 2 ^ 32) (g : Reg → BitVec 32) :
    ∀ p ∈ saved, (saveMemA m b g saved).readW (A b p.2) 32 = g p.1 := by
  intro p hp
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := omega_arith) only [saved, saveMemA, Mem.readW_writeW_self32, readW_writeW_A (hfit := hfit)]

theorem prologue_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block prologue) s₀ (LInv s₀ 0) := by
  have fC := hp.fitC
  have fS := hp.fitS
  rw [show prologue = saved.map (fun p => Instr.str p.1 .r1 p.2) ++
    (enter ++ [.dp .add T .r1 (.imm 200), .str T .r1 rcPtr]) from rfl]
  refine saveA_ok saved s₀ _ (fun p hp' => ⟨(saved_ok p hp').2.1, hp.scr_in (by have := saved_ok p hp'; omega)⟩)
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
  have f₁ : Frame [regR (scp s₀) 512] s₀.mem s₁.mem := by
    rw [m₁]; exact saveMemA_frame fC _ _ _ (fun p hp' => by have := saved_ok p hp'; omega)
  obtain ⟨s₂, hs₂, hst, hrc, rd₂, wr₂, sp₂, g0, g1, f₂⟩ :=
    enter_ok (hp.ok_sc (c := cfgIn) wr₁ (by rw [g₁]) (by rw [g₁]) rfl rfl (by decide) (by decide))
  rw [g₁] at hst hrc f₂ g0 g1
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₂, hs₂, ?_⟩
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => ?_
  refine wp_str (a := A (scp s₀) rcPtr) (by decide) (by rw [u₃.other .r1 (by decide), g1])
    (by rw [u₃.wr, wr₂, wr₁]; exact hp.scr_in (by decide)) fun s₄ u₄ => WP.block_nil ?_
  have hm : s₄.mem = s₂.mem.writeW (A (scp s₀) rcPtr) (rcp s₀ 0) := by
    rw [u₄.mem, u₃.mem, u₃.gpr, g1]; rfl
  have keep : ∀ d, d + 4 ≤ 512 → d + 4 ≤ 392 ∨ 396 ≤ d →
      s₄.mem.readW (A (scp s₀) d) 32 = s₂.mem.readW (A (scp s₀) d) 32 := fun d hd' hne => by
    rw [hm]; exact readW_writeW_A _ fC _ hd' (by decide) (by simp only [rcPtr]; omega_arith)
  have keep₂ : ∀ d, 396 ≤ d → d + 4 ≤ 512 →
      s₂.mem.readW (A (scp s₀) d) 32 = s₁.mem.readW (A (scp s₀) d) 32 := fun d hd hd' =>
    f₂.readW (Region.contains_self _ _) (by simpa using hp.off_scr (by omega_arith) hd' (by decide)) (by decide)
  refine ⟨by rw [u₄.gpr, u₃.other .r0 (by decide), g0], by rw [u₄.gpr, u₃.other .r1 (by decide), g1],
    by rw [u₄.rd, u₃.rd, rd₂, rd₁], by rw [u₄.wr, u₃.wr, wr₂, wr₁], by rw [u₄.sp, u₃.sp, sp₂, sp₁],
    by rw [hm, Mem.readW_writeW_self32], fun j hj h hh => ?_, fun i hi => ?_, ?_, ?_⟩
  · have hc : cur s₀ 0 = scp s₀ := by simp [cur]
    rw [hc, wordAddr_eq, keep _ (by omega_arith) (.inl (by omega_arith)), ← wordAddr_eq, hst j hj h hh, lane_words,
      rd64_frame f₁ (fun r hr => by simp at hr; subst hr; exact hp.disj) fS (by omega_arith),
      ← stateAt_get fS _ hj]
    simp only [List.range_zero, List.foldl_nil]
    exact congrArg (stw · j h) (getElem!_pos _ j hj).symm
  · rw [wordAddr_eq, keep _ (by omega_arith) (.inl (by omega_arith)), ← wordAddr_eq, hrc i hi]
  · intro p hp'
    obtain ⟨-, -, a, b⟩ := saved_ok p hp'
    rw [keep _ (by omega_arith) (.inr a), keep₂ _ a (by omega_arith), m₁]
    exact saveMemA_saved _ fC _ p hp'
  · rw [hm]
    refine ((f₁.trans (f₂.sub fun R hR => ?_)).mono (by simp)).writeW (r := regR (scp s₀) 512) (by simp) _
      (contains_A fC (by decide))
    simp only [List.mem_singleton] at hR
    subst hR
    exact ⟨regR (scp s₀) 512, by simp, Region.sub_prefix (by decide)⟩

/-! ## The epilogue -/

theorem restoreA_ok {bR : Reg} {rest : List Instr} (l : List (Reg × Nat)) :
    ∀ (s : State) (Q : State → Prop), (l.map Prod.fst).Nodup →
    (∀ p ∈ l, p.1 ≠ bR ∧ p.2 < 4096 ∧ InRegions (s.rd ++ s.wr) (A (s.gpr bR) p.2) 4) →
    (∀ s', (∀ p ∈ l, s'.gpr p.1 = s.mem.readW (A (s.gpr bR) p.2) 32) →
      (∀ r, r ∉ l.map Prod.fst → s'.gpr r = s.gpr r) → s'.mem = s.mem → WP isa (.block rest) s' Q) →
    WP isa (.block (l.map (fun p => Instr.ldr p.1 bR p.2) ++ rest)) s Q := by
  induction l with
  | nil => intro s Q _ _ k; exact k s (fun _ h => by cases h) (fun _ _ => rfl) rfl
  | cons p l ih =>
    intro s Q hnd hl k
    obtain ⟨h0, h1, h3⟩ := hl p (by simp)
    simp only [List.map_cons, List.nodup_cons] at hnd
    refine wp_ldr h1 rfl h3 fun s₁ u₁ => ?_
    have e : s₁.gpr bR = s.gpr bR := u₁.other _ (Ne.symm h0)
    refine ih s₁ Q hnd.2 (fun q hq => ?_) fun s' hl' ho hm => k s' (fun q hq => ?_) (fun r hr => ?_)
      (hm.trans u₁.mem)
    · rw [e, u₁.rd, u₁.wr]; exact hl q (List.mem_cons_of_mem _ hq)
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [ho _ hnd.1, u₁.gpr]
      · rw [hl' q hq, u₁.mem, e]
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [ho r hr.2, u₁.other r hr.1]

theorem preserved_saved : ∀ r ∈ preserved, ∃ p ∈ saved, p.1 = r := by decide

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {s : State} (hL : LInv s₀ 24 s) :
    WP isa (.block epilogue) s fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha3.permuteArm.post s₀ s' := by
  have hc : cur s₀ 24 = scp s₀ := by simp [cur]
  obtain ⟨s₁, hs₁, hl, rd₁, wr₁, sp₁, g0, g1, f₁⟩ :=
    leave_ok (hp.ok_st hL.wr hL.r0 hL.r1) (by rw [hL.r1, ← hc]; exact hL.state)
  rw [hL.r0] at hl f₁ g0
  rw [hL.r1] at g1
  rw [show epilogue = leave ++ (saved.map (fun p => Instr.ldr p.1 .r1 p.2) ++ []) by
    rw [List.append_nil]; rfl, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, hs₁, ?_⟩
  refine restoreA_ok saved s₁ _ (by decide) (fun p hp' => ⟨(saved_ok p hp').1, (saved_ok p hp').2.1, ?_⟩)
    fun s' ho _ hm => WP.block_nil ⟨fun r hr => ?_, ?_⟩
  · rw [rd₁, wr₁, hL.rd, hL.wr, g1]; exact mem_rd (hp.scr_in (by have := saved_ok p hp'; omega))
  · obtain ⟨p, hp', rfl⟩ := preserved_saved r hr
    obtain ⟨-, -, a, b⟩ := saved_ok p hp'
    rw [ho p hp', g1, f₁.readW (Region.contains_self _ _)
      (by simpa using hp.off_st (d := p.2) (n := 4) (by omega_arith) (by decide)) (by decide)]
    exact hL.saved p hp'
  · show stateAt s'.mem (State.addr (stp s₀)) = keccakF (A₀ s₀)
    rw [hm]
    exact stateAt_eq hp.fitS fun j hj => by rw [← lane_words, hl j hj]; rfl

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa permute s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha3.permuteArm.post s₀ s' := by
  unfold permute
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (Q := LInv s₀ 24) ?_ fun s₂ h₂ => epilogue_ok hp h₂)
  let Inv : Nat → State → Prop := fun n s => ∃ t, n = 12 - t ∧ t < 12 ∧ LInv s₀ (2 * t) s
  refine WP.loop (M := isa) Inv (fun n s ⟨t, hn, ht, hL⟩ => ?_) 12 s₁ ⟨0, rfl, by omega_arith, h₁⟩
  refine WP.mono (body_ok hp ht hL) fun s' h => ?_
  rcases h with ⟨he, hL'⟩ | ⟨he, ht', hL'⟩
  · exact .inl ⟨he, hL'⟩
  · exact .inr ⟨he, 12 - (t + 1), by omega_arith, t + 1, rfl, ht', hL'⟩

/-! ## Constant time -/

/-- The constant-time analysis's taint without the round constants that the
prologue stores at `[200, 392)` of the scratch space: public, but no
address or branch depends on them, and the kernel checks the analysis much
faster without them (`taint_decide_weak`). -/
def dropRC (τ : VG.Arm.Taint.T) : VG.Arm.Taint.T :=
  { τ with slots := VG.Arm.Taint.cutSlots 1 200 192 τ.slots }

/-- The initial taint: the pointers are public, and point at the writable regions. -/
def τ₀ : VG.Arm.Taint.T :=
  { regs := .ofList [.r0, .r1], flags := false, lens := [200, 512], bases := [(.r0, 0), (.r1, 1)] }

theorem wf₀ {s : State} (h : Proof.Sha3.permuteArm.pre s) : VG.Arm.Taint.Wf τ₀ s := by
  have hp := pre_of s h
  have hst := hp.fitS; have hsc := hp.fitC
  refine ⟨fun _ => ⟨by simp [hp.wr, τ₀], by simpa [hp.wr] using hp.disj, ?_⟩, ?_,
    fun h => absurd h (by decide), fun _ h => by simp [τ₀] at h⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [addr_toNat] <;> omega_arith
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> simp [VG.Arm.Taint.region, hp.wr]

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Sha3.permuteArm.pre s₁) (h₂ : Proof.Sha3.permuteArm.pre s₂)
    (hpub : Proof.Sha3.permuteArm.pub s₁ s₂) : VG.Arm.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨p0, p1⟩ := hpub
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ h₁, wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun h => absurd h (Nat.lt_irrefl 0), fun _ hk => absurd hk (Nat.not_lt_zero _)⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> with_reducible assumption
  · rw [(pre_of s₁ h₁).wr, (pre_of s₂ h₂).wr, stp, scp, stp, scp, p0, p1]

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 200⟩, ⟨0x2000, 512⟩]

theorem permute_verified : Verified Arm.target Impl.Sha3.Arm.permute Proof.Sha3.permuteArm := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he⟩, h₂⟩
  · exact VG.Taint.constantTime (A := VG.Arm.taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp)
      (by taint_decide_weak dropRC)
  · refine ⟨satState, rfl, rfl, ?_, by decide, by decide⟩
    exact Region.disjoint_of_sep (by decide)

end VG.Proof.Sha3.Arm

section

/-!
# SHA-3 on ARMv7: calling the permutation, and saving registers

What the streaming functions (`VG.Impl.Sha3.Arm.Stream`) share: the call of
the permutation, the saving and restoring of our caller's registers in the
scratch space, and arithmetic on 32-bit values.
-/

namespace VG.Proof.Sha3.Arm

open VG VG.Arm VG.Impl.Sha3.Arm
open VG.Spec.Sha3 (stateAt keccakF)
open VG.Proof.Sha512.Arm (A A_eq contains_A)
open VG.Proof.Sha3 (off_disjoint sub_offset add_zero')

/-! ## The permutation -/

theorem permute_noCalls : permute.noCalls = true := by lit_decide

theorem permute_r0 : ∀ i ∈ instrs permute, clobbers i .r0 = false := by
  have : ((instrs permute).all fun i => !clobbers i .r0) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  intro i hi
  simpa using List.all_eq_true.mp this i hi

theorem permute_r1 : ∀ i ∈ instrs permute, clobbers i .r1 = false := by
  have : ((instrs permute).all fun i => !clobbers i .r1) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  intro i hi
  simpa using List.all_eq_true.mp this i hi

/-- The state and the permutation's part of a scratch space of `N` bytes. -/
theorem covers_of {wr : List Region} {st scr : BitVec 32} {N : Nat} (hN : 512 ≤ N)
    (hS : regR st 200 ∈ wr) (hC : regR scr N ∈ wr) : Covers [regR st 200, regR scr 512] wr := by
  apply Covers.of_sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, hS, 0, by simp, by simp⟩
  · exact ⟨_, hC, 0, by simp, by simpa using hN⟩

/-- Calling `vg_keccak_f1600` on the state at `r0`, with scratch space at
`r1`: the callee-saved registers other than `lr`, and `r0` and `r1`, are
kept. -/
theorem call_ok {s : State} {st scr : BitVec 32} (h0 : s.gpr .r0 = st) (h1 : s.gpr .r1 = scr)
    (fS : st.toNat + 200 ≤ 2 ^ 32) (fC : scr.toNat + 512 ≤ 2 ^ 32)
    (d₁ : Region.Disjoint (regR st 200) (regR scr 512))
    (hw : Covers [regR st 200, regR scr 512] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) → s'.gpr .r0 = st → s'.gpr .r1 = scr →
      Frame [regR st 200, regR scr 512] s.mem s'.mem →
      stateAt s'.mem (State.addr st) = keccakF (stateAt s.mem (State.addr st)) → Q s') :
    WP isa Impl.Sha3.Arm.Stream.permuteCall s Q := by
  have c0 : s.callEntry.gpr .r0 = st := (State.callEntry_gpr _ (by decide)).trans h0
  have c1 : s.callEntry.gpr .r1 = scr := (State.callEntry_gpr _ (by decide)).trans h1
  refine WP.call (k := Proof.Sha3.permuteArm) permute_verified.1
    (rd := []) (wr := [regR st 200, regR scr 512]) ?_ ?_ hw ?_ permute_noCalls
  · simp only [Proof.Sha3.permuteArm, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1]
    exact ⟨trivial, trivial, d₁, fS, fC⟩
  · intro a n h
    obtain ⟨r, hr, hc⟩ := hw a n (by simpa using h)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · intro s' hrd hwr hsp hf hcs hg hpost
    simp only [Proof.Sha3.permuteArm, State.withRegions_gpr, State.withRegions_mem, c0] at hpost
    exact hQ s' hrd hwr hsp hcs (by rw [hg _ permute_r0 (by decide), h0])
      (by rw [hg _ permute_r1 (by decide), h1]) hf (by rw [hpost]; rfl)

/-! ## Saving the caller's registers -/

/-- The caller's registers `g` saved at `scr`. -/
def SSaved (scr : BitVec 32) (g : Reg → BitVec 32) (m : Mem) : Prop :=
  ∀ p ∈ Impl.Sha3.Arm.Stream.saved, m.readW (A scr p.2) 32 = g p.1

theorem ssaved_ok : ∀ p ∈ Impl.Sha3.Arm.Stream.saved,
    p.1 ≠ .r1 ∧ p.1 ≠ .r12 ∧ p.2 < 4096 ∧ 512 ≤ p.2 ∧ p.2 + 4 ≤ 532 := by decide

set_option simprocs false in
theorem saveMemA_ssaved (m : Mem) {b : BitVec 32} (hfit : b.toNat + 640 ≤ 2 ^ 32) (g : Reg → BitVec 32) :
    SSaved b g (saveMemA m b g Impl.Sha3.Arm.Stream.saved) := by
  intro p hp
  simp only [Impl.Sha3.Arm.Stream.saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := omega_arith) only [Impl.Sha3.Arm.Stream.saved, saveMemA, Mem.readW_writeW_self32,
    readW_writeW_A (hfit := hfit)]

theorem SSaved.keep {scr : BitVec 32} {g : Reg → BitVec 32} {m m' : Mem} (h : SSaved scr g m)
    (hk : ∀ d, 512 ≤ d → d + 4 ≤ 532 → m'.readW (A scr d) 32 = m.readW (A scr d) 32) :
    SSaved scr g m' := fun p hp => by
  obtain ⟨-, -, -, h1, h2⟩ := ssaved_ok p hp
  rw [hk _ h1 h2]; exact h p hp

theorem SSaved.of_gpr {scr : BitVec 32} {g g' : Reg → BitVec 32} {m : Mem} (h : SSaved scr g m)
    (hg : ∀ r, r ≠ .r12 → g r = g' r) : SSaved scr g' m := fun p hp => by
  rw [h p hp, hg _ (ssaved_ok p hp).2.1]

/-- Writes to the state and to the permutation's scratch space keep the
words of the scratch space after the permutation's part. -/
theorem readW_hi {st scr : BitVec 32} (fC : scr.toNat + 640 ≤ 2 ^ 32)
    (hd : Region.Disjoint (regR st 200) (regR scr 640)) {m m' : Mem} {rs : List Region}
    (hf : Frame rs m m') (hrs : ∀ r ∈ rs, r = regR st 200 ∨ r = regR scr 512) {d : Nat}
    (hd₁ : 512 ≤ d) (hd₂ : d + 4 ≤ 640) : m'.readW (A scr d) 32 = m.readW (A scr d) 32 := by
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rcases hrs r hr with rfl | rfl
  · refine hd.symm.sub_left ?_
    rw [A_eq (by omega_arith)]; exact sub_offset (by omega_arith) (by omega_arith)
  · have := off_disjoint (State.addr scr) (a := d) (n := 4) (b := 0) (k := 512) (by omega_arith)
      (by omega_arith) (.inr hd₁)
    rw [add_zero'] at this
    rw [A_eq (by omega_arith)]; exact this

/-- Writes to the state and to the permutation's scratch space keep the
saved registers. -/
theorem SSaved.frame {st scr : BitVec 32} (fC : scr.toNat + 640 ≤ 2 ^ 32)
    (hd : Region.Disjoint (regR st 200) (regR scr 640)) {g : Reg → BitVec 32} {m m' : Mem}
    (h : SSaved scr g m) {rs : List Region} (hf : Frame rs m m')
    (hrs : ∀ r ∈ rs, r = regR st 200 ∨ r = regR scr 512) : SSaved scr g m' :=
  h.keep fun _ hd₁ hd₂ => readW_hi fC hd hf hrs hd₁ (by omega_arith)

theorem restore_eq :
    Impl.Sha3.Arm.Stream.restore = Impl.Sha3.Arm.Stream.saved.map (fun p => Instr.ldr p.1 .r1 p.2) := rfl

/-- Every callee-saved register is saved, or one of `r8`–`r11`. -/
theorem preserved_cases : ∀ r ∈ preserved,
    (∃ p ∈ Impl.Sha3.Arm.Stream.saved, p.1 = r) ∨ r ∈ [Reg.r8, .r9, .r10, .r11] := by decide

/-! ## Arithmetic on 32-bit values -/

theorem ofNat32_succ (k : Nat) : BitVec.ofNat 32 k + 1 = BitVec.ofNat 32 (k + 1) := by
  rw [BitVec.ofNat_add]; rfl

theorem sub_ofNat32 {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) :=
  VG.Proof.MdStream.Arm.sub_ofNat h

theorem ofNat32_beq_zero {k : Nat} (h : k < 2 ^ 32) : (BitVec.ofNat 32 k == 0) = decide (k = 0) :=
  VG.Proof.MdStream.Arm.ofNat_beq_zero h

theorem sub_beq_zero32 {a : Nat} (ha : a < 2 ^ 32) (y : BitVec 32) :
    (BitVec.ofNat 32 a - y == 0) = decide (a = y.toNat) := by
  by_cases h : a = y.toNat
  · subst h; simp
  · have : BitVec.ofNat 32 a - y ≠ 0 := by intro e; apply h; bv_omega
    rw [beq_eq_false_iff_ne.mpr this]; simp [h]

theorem beq_zero32 (x : BitVec 32) : (x == 0) = decide (x.toNat = 0) := by
  by_cases h : x = 0
  · subst h; rfl
  · have : x.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq e)
    rw [beq_eq_false_iff_ne.mpr h]; simp [this]

theorem xor_setWidth32 (x y : Byte) : (x.setWidth 32 ^^^ y.setWidth 32).setWidth 8 = x ^^^ y := by
  ext i hi
  simp

theorem xor_setWidth32' (x : Byte) (y : BitVec 32) :
    (x.setWidth 32 ^^^ y).setWidth 8 = x ^^^ y.setWidth 8 := by
  ext i hi
  simp

theorem ofNat_toNat32 (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by simp

theorem sub_imm0 (a : BitVec 32) : a - 0 = a := by simp

/-! ## The arguments on the stack -/

theorem arg_in {s : State} {n : Nat} (hsp : s.sp.toNat + 4 * n ≤ 2 ^ 32) {k : Nat} (hk : k < n) :
    (⟨stackArgAddr s 0, 4 * n⟩ : Region).Contains (stackArgAddr s k) 4 := by
  simp only [stackArgAddr, Region.Contains]
  rw [addr_add (a := s.sp) (k := 4 * k) (by omega_arith), addr_add (a := s.sp) (k := 4 * 0) (by omega_arith)]
  bv_omega

theorem argByte_eq {s : State} {n : Nat} (hsp : s.sp.toNat + n ≤ 2 ^ 32) {k : Nat} (hk : k < n) :
    VG.Arm.Taint.argByte s k = stackArgAddr s (k / 4) + BitVec.ofNat 64 (k % 4) := by
  simp only [VG.Arm.Taint.argByte, stackArgAddr]
  rw [addr_add (a := s.sp) (k := 4 * (k / 4)) (by omega_arith), BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2; omega_arith

end VG.Proof.Sha3.Arm

end

module

public import VerifiedGarbage.Proof.Sha3.Arm.Round
public import VerifiedGarbage.Proof.Sha3.Lanes
public import VerifiedGarbage.Proof.Sha512.Arm.Rounds
public import VerifiedGarbage.Spec.Sha3.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.Arm.RelCT
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
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
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
/-- 32-bit ARM contract for `vg_keccak_update(state = r0, rate = r1,
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

The function saves the callee-saved registers, and calls three functions
of its own: `enter` interleaves the lanes of the state into the scratch
space (`enter_ok`) and stores the round constants there; each iteration of
the loop of `rounds` runs two rounds (`round_ok`), from the state in the
scratch space to the one at `state` and back; `leave` brings the lanes back
to `state` (`leave_ok`). Then it restores the registers.

The three keep `r0`, `r1` and `lr`, but not the callee-saved registers, so
they are not called through a contract of the calling convention
(`WP.call`): `call_kept` runs a call from what the called code does from
the state it is entered in, with its permissions narrowed to the state and
the scratch space (`enter_correct`, `rounds_correct`, `leave_correct`). The
sponge's functions call them too (`enter_call`, `rounds_call`,
`leave_call`), to run several permutations on the interleaved state.
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

/-- The round constants, interleaved, at `scr`. -/
def RCs (scr : BitVec 32) (m : Mem) : Prop :=
  ∀ i < 48, m.readW (wordAddr scr (50 + i)) 32 = half (i % 2) (RC (i / 2))

/-- The round constants, in the scratch space. -/
def Aux (s₀ : State) (m : Mem) : Prop := RCs (scp s₀) m

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

/-- The loop's invariant, before round `r`, from the state `K`: `M` is the
memory when the loop is entered, whose words after the pointer to the round
constants are kept. -/
structure LInv (s₀ : State) (K : KState) (M : Mem) (r : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = stp s₀
  r1 : s.gpr .r1 = scp s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  ptr : s.mem.readW (A (scp s₀) rcPtr) 32 = rcp s₀ r
  state : Stored s.mem (cur s₀ r) ((List.range r).foldl rnd K)
  aux : Aux s₀ s.mem
  kept : ∀ d, 396 ≤ d → d + 4 ≤ 512 → s.mem.readW (A (scp s₀) d) 32 = M.readW (A (scp s₀) d) 32

theorem round_step {s₀ : State} (hp : Pre s₀) {K : KState} {M : Mem} {r : Nat} (hr : r < 24)
    {src dst : Reg}
    (hc : Straight.checkN Bitslice.Anf.anf32 (cfg src dst) atoms (roundCore src dst) env₀ post = true)
    (hsd : (src = .r0 ∧ dst = .r1) ∨ (src = .r1 ∧ dst = .r0)) {s : State} (hL : LInv s₀ K M r s)
    (h0 : s.gpr src = cur s₀ r) (hd : s.gpr dst = oth s₀ r) :
    WP isa (.block (round src dst)) s (LInv s₀ K M (r + 1)) := by
  have hD : oth s₀ r = stp s₀ ∨ oth s₀ r = scp s₀ := by
    rcases hsd with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact .inr (hd.symm.trans hL.r1)
    · exact .inl (hd.symm.trans hL.r0)
  have hok : Ok (cfg src dst) s := by
    rcases hsd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hp.ok_sc hL.wr hL.r0 hL.r1 rfl rfl (by decide) (by decide)
    · exact hp.ok_st hL.wr hL.r0 hL.r1
  have E : Env s.wr (oth s₀ r) (scp s₀) (rcp s₀ r) := hL.wr ▸ hp.env_of hD hr
  refine WP.mono (round_ok hc hsd (K := (List.range r).foldl rnd K) (rc := RC r) s hok E hd hL.r1
    (by rw [h0]; exact hL.state) hL.ptr
    (hL.aux.rc hr)) fun s' ⟨hl, hf, hptr, hq, hrd, hwr, hsp⟩ => ?_
  refine ⟨by rw [hq .r0 (by simp), hL.r0], by rw [hq .r1 (by simp), hL.r1], hrd.trans hL.rd,
    hwr.trans hL.wr, hsp.trans hL.sp, by rw [hptr, rcp_succ], ?_,
    hL.aux.keep fun d hd hd' => hp.keep_round hD hf hd (by omega_arith) (.inl hd'),
    fun d hd hd' => (hp.keep_round hD hf (by omega_arith) hd' (.inr hd)).trans (hL.kept d hd hd')⟩
  rw [cur_succ, foldl_succ, ← outState_eq]; exact hl

theorem body_ok {s₀ : State} (hp : Pre s₀) {K : KState} {M : Mem} {t : Nat} (ht : t < 12) {s : State}
    (hL : LInv s₀ K M (2 * t) s) :
    WP isa (.block body) s fun s' =>
      (eval .ne s' = some false ∧ LInv s₀ K M 24 s') ∨
      (eval .ne s' = some true ∧ t + 1 < 12 ∧ LInv s₀ K M (2 * (t + 1)) s') := by
  unfold body
  rw [WP.block_append_iff]
  refine WP.mono (round_step hp (r := 2 * t) (by omega_arith) coreA_ok (.inr ⟨rfl, rfl⟩) hL
    (by rw [hL.r1, (cur_even s₀ t).1]) (by rw [hL.r0, (cur_even s₀ t).2])) fun s₁ h₁ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (round_step hp (r := 2 * t + 1) (by omega_arith) coreB_ok (.inl ⟨rfl, rfl⟩) h₁
    (by rw [h₁.r0, (cur_odd s₀ t).1]) (by rw [h₁.r1, (cur_odd s₀ t).2])) fun s₂ h₂ => ?_
  have h₂' : LInv s₀ K M (2 * (t + 1)) s₂ := by
    rw [show 2 * (t + 1) = 2 * t + 1 + 1 by omega_arith]; exact h₂
  refine wp_ldr (a := A (scp s₀) rcPtr) (by decide) (by rw [h₂.r1])
    (by rw [h₂.rd, h₂.wr]; exact mem_rd (hp.scr_in (by decide))) fun s₃ u₃ => ?_
  refine wp_sub (op2_reg _ _) fun s₄ u₄ => wp_cmp (op2_imm (by decide)) fun s₅ u₅ hz => WP.block_nil ?_
  have hT : s₄.gpr T = BitVec.ofNat 32 (216 + 16 * t) := by
    rw [u₄.gpr, u₃.gpr, u₃.other .r1 (by decide), h₂'.ptr, h₂.r1]
    show scp s₀ + _ - scp s₀ = _
    rw [BitVec.add_comm, BitVec.add_sub_cancel, show 200 + 8 * (2 * (t + 1)) = 216 + 16 * t by omega_arith]
  rw [hT, show (392 : BitVec 32) = BitVec.ofNat 32 392 from rfl,
    VG.Proof.MdStream.Arm.sub_beq (by omega_arith) (by omega_arith)] at hz
  have hs₅ : LInv s₀ K M (2 * (t + 1)) s₅ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₅.gpr, u₄.other .r0 (by decide), u₃.other .r0 (by decide), h₂'.r0]
    · rw [u₅.gpr, u₄.other .r1 (by decide), u₃.other .r1 (by decide), h₂'.r1]
    · rw [u₅.rd, u₄.rd, u₃.rd, h₂'.rd]
    · rw [u₅.wr, u₄.wr, u₃.wr, h₂'.wr]
    · rw [u₅.sp, u₄.sp, u₃.sp, h₂'.sp]
    · rw [u₅.mem, u₄.mem, u₃.mem, h₂'.ptr]
    · rw [u₅.mem, u₄.mem, u₃.mem]; exact h₂'.state
    · rw [u₅.mem, u₄.mem, u₃.mem]; exact h₂'.aux
    · rw [u₅.mem, u₄.mem, u₃.mem]; exact h₂'.kept
  by_cases hlast : t + 1 = 12
  · refine .inl ⟨by rw [eval_ne, hz, decide_eq_true (by omega_arith)]; rfl, ?_⟩
    rw [show 24 = 2 * (t + 1) by omega_arith]; exact hs₅
  · exact .inr ⟨by rw [eval_ne, hz, decide_eq_false (by omega_arith)]; rfl, by omega_arith, hs₅⟩

/-- The rounds, as a function: from the state `K`, interleaved in the
scratch space with the round constants, to `keccakF K`. They keep `lr`, and
the words of the scratch space after the pointer to the round constants but
the one where they save `lr`. -/
theorem rounds_correct {s₀ : State} (hp : Pre s₀) {K : KState} (hK : Stored s₀.mem (scp s₀) K)
    (ha : Aux s₀ s₀.mem) :
    WP isa rounds s₀ fun s' => s'.gpr .lr = s₀.gpr .lr ∧ Stored s'.mem (scp s₀) (keccakF K) ∧
      Aux s₀ s'.mem ∧
      ∀ d, 396 ≤ d → d + 4 ≤ 432 → s'.mem.readW (A (scp s₀) d) 32 = s₀.mem.readW (A (scp s₀) d) 32 := by
  have fC := hp.fitC
  unfold rounds
  refine WP.seq ?_
  refine wp_str (a := A (scp s₀) lrSave) (by decide) rfl (hp.scr_in (by decide)) fun s₁ u₁ => ?_
  refine wp_add (op2_imm (by decide)) fun s₂ u₂ => ?_
  refine wp_str (a := A (scp s₀) rcPtr) (by decide) (by rw [u₂.other .r1 (by decide), u₁.gpr])
    (by rw [u₂.wr, u₁.wr]; exact hp.scr_in (by decide)) fun s₃ u₃ => WP.block_nil ?_
  have hm : s₃.mem = (s₀.mem.writeW (A (scp s₀) lrSave) (s₀.gpr .lr)).writeW (A (scp s₀) rcPtr) (rcp s₀ 0) := by
    rw [u₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr]; rfl
  have keep : ∀ d, d + 4 ≤ 512 → d + 4 ≤ 392 ∨ 396 ≤ d → d + 4 ≤ 432 ∨ 436 ≤ d →
      s₃.mem.readW (A (scp s₀) d) 32 = s₀.mem.readW (A (scp s₀) d) 32 := fun d hd' h₁ h₂ => by
    rw [hm, readW_writeW_A _ fC _ hd' (by decide) (by simp only [rcPtr]; omega_arith),
      readW_writeW_A _ fC _ hd' (by decide) (by simp only [lrSave]; omega_arith)]
  have hlr : s₃.mem.readW (A (scp s₀) lrSave) 32 = s₀.gpr .lr := by
    rw [hm, readW_writeW_A _ fC _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  have h₀ : LInv s₀ K s₃.mem 0 s₃ := by
    refine ⟨by rw [u₃.gpr, u₂.other .r0 (by decide), u₁.gpr], by rw [u₃.gpr, u₂.other .r1 (by decide), u₁.gpr],
      by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr], by rw [u₃.sp, u₂.sp, u₁.sp],
      by rw [hm, Mem.readW_writeW_self32], fun j hj h hh => ?_, fun i hi => ?_, fun _ _ _ => rfl⟩
    · have hc : cur s₀ 0 = scp s₀ := by simp [cur]
      rw [hc, wordAddr_eq, keep _ (by omega_arith) (.inl (by omega_arith)) (.inl (by omega_arith)), ← wordAddr_eq]
      simp only [List.range_zero, List.foldl_nil]
      exact hK j hj h hh
    · rw [wordAddr_eq, keep _ (by omega_arith) (.inl (by omega_arith)) (.inl (by omega_arith)), ← wordAddr_eq]
      exact ha i hi
  refine WP.seq (WP.mono (Q := LInv s₀ K s₃.mem 24) ?_ fun s₄ h₄ => ?_)
  · let Inv : Nat → State → Prop := fun n s => ∃ t, n = 12 - t ∧ t < 12 ∧ LInv s₀ K s₃.mem (2 * t) s
    refine WP.loop (M := isa) Inv (fun n s ⟨t, hn, ht, hL⟩ => ?_) 12 s₃ ⟨0, rfl, by omega_arith, h₀⟩
    refine WP.mono (body_ok hp ht hL) fun s' h => ?_
    rcases h with ⟨he, hL'⟩ | ⟨he, ht', hL'⟩
    · exact .inl ⟨he, hL'⟩
    · exact .inr ⟨he, 12 - (t + 1), by omega_arith, t + 1, rfl, ht', hL'⟩
  have hc : cur s₀ 24 = scp s₀ := by simp [cur]
  refine wp_ldr (a := A (scp s₀) lrSave) (by decide) (by rw [h₄.r1])
    (by rw [h₄.rd, h₄.wr]; exact mem_rd (hp.scr_in (by decide))) fun s₅ u₅ => WP.block_nil ?_
  refine ⟨by rw [u₅.gpr, h₄.kept _ (by decide) (by decide), hlr], ?_, by rw [u₅.mem]; exact h₄.aux,
    fun d hd hd' => by
      rw [u₅.mem, h₄.kept d hd (by omega_arith), keep d (by omega_arith) (.inr hd) (.inl hd')]⟩
  rw [u₅.mem, ← hc]; exact h₄.state

/-! ## To and from the interleaved lanes -/

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

theorem enter_lr : ∀ i ∈ instrs (.block enter : Prog isa), clobbers i .lr = false := by
  have : ((instrs enterCode.lit).all fun i => !clobbers i .lr) = true := by lit_decide
  rw [enter_code] at this
  intro i hi
  simpa using List.all_eq_true.mp this i hi

theorem leave_lr : ∀ i ∈ instrs (.block leave : Prog isa), clobbers i .lr = false := by
  have : ((instrs leaveCode.lit).all fun i => !clobbers i .lr) = true := by lit_decide
  rw [leave_code] at this
  intro i hi
  simpa using List.all_eq_true.mp this i hi

/-- Code keeps a register that none of its instructions writes. -/
theorem wp_keeps {c : Prog isa} {r : Reg} (hc : ∀ i ∈ instrs c, clobbers i r = false)
    (hn : c.noCalls = true) {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => s'.gpr r = s.gpr r ∧ Q s' := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, Exec.gpr hc he (.inl hn), hq⟩

/-- `enter`, as a function: the state, interleaved in the scratch space,
and the round constants. -/
theorem enter_correct {s₀ : State} (hp : Pre s₀) :
    WP isa (.block enter) s₀ fun s' => s'.gpr .lr = s₀.gpr .lr ∧ Stored s'.mem (scp s₀) (A₀ s₀) ∧
      Aux s₀ s'.mem ∧ Frame [regR (scp s₀) 392] s₀.mem s'.mem := by
  refine wp_keeps enter_lr rfl ?_
  obtain ⟨s₂, hs₂, hst, hrc, -, -, -, -, -, f₂⟩ :=
    enter_ok (hp.ok_sc (c := cfgIn) rfl rfl rfl rfl rfl (by decide) (by decide))
  refine WP.of_runBlock ⟨s₂, hs₂, fun j hj h hh => ?_, hrc, f₂⟩
  rw [hst j hj h hh, lane_words, ← stateAt_get hp.fitS _ hj]
  exact congrArg (stw · j h) (getElem!_pos _ j hj).symm

/-- `leave`, as a function: the state that is interleaved in the scratch
space, at `state`. -/
theorem leave_correct {s₀ : State} (hp : Pre s₀) {K : KState} (hK : Stored s₀.mem (scp s₀) K) :
    WP isa (.block leave) s₀ fun s' => s'.gpr .lr = s₀.gpr .lr ∧
      stateAt s'.mem (State.addr (stp s₀)) = K ∧ Frame [regR (stp s₀) 200] s₀.mem s'.mem := by
  refine wp_keeps leave_lr rfl ?_
  obtain ⟨s₁, hs₁, hl, -, -, -, -, -, f₁⟩ := leave_ok (hp.ok_st rfl rfl rfl) hK
  exact WP.of_runBlock ⟨s₁, hs₁, stateAt_eq hp.fitS fun j hj => by rw [← lane_words, hl j hj], f₁⟩

/-! ## Calling them -/

/-- A call of code that keeps `lr`: from a state `s` in which `pre` holds
on entry, with the permissions narrowed to `rd` and `wr`, the call returns
in a state that has the permissions and stack pointer of `s`, and every
register other than `lr` and `r12` that the code's instructions never
write; that differs from `s` in memory only within `wr`; and that satisfies
`post` (on the narrowed states). Unlike `WP.call`, it asks nothing of the
callee-saved registers. -/
theorem call_kept {n : String} {c : Prog isa} {pre : State → Prop} {post : State → State → Prop}
    (hv : ∀ s, pre s → WP isa c s fun s' => s'.gpr .lr = s.gpr .lr ∧ post s s')
    {s : State} {rd wr : List Region} (hpre : pre (s.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Frame wr s.mem s'.mem →
      (∀ r, (∀ i ∈ instrs c, clobbers i r = false) → r ∉ linkRegs → s'.gpr r = s.gpr r) →
      post (s.callEntry.withRegions rd wr) (s'.withRegions rd wr) → Q s')
    (hn : c.noFrames = true) : WP isa (.call n c) s Q := by
  obtain ⟨t, s₁, he, hlr, hpost⟩ := hv _ hpre
  obtain ⟨hr, hwr, hsp, hf⟩ := Exec.regions he hn
  simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    State.callEntry_mem] at hr hwr hf
  have he' := Exec.widen he (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  simp only [State.withRegions_withRegions] at he'
  rw [show s.callEntry.withRegions s.rd s.wr = s.callEntry from rfl] at he'
  have hret : isa.ret s.callEntry (s₁.withRegions s.rd s.wr) = some (s₁.withRegions s.rd s.wr) := by
    simp only [State.withRegions_gpr] at hlr
    simp only [isa, ret, State.withRegions_gpr, hlr, ite_true]
  refine ⟨_, _, .call (call_callEntry s) he' hret, hQ _ rfl rfl hsp hf (fun r hr' hl => ?_) ?_⟩
  · rw [Exec.gpr hr' he' (.inr hl), State.callEntry_gpr s hl]
  · have : (s₁.withRegions s.rd s.wr).withRegions rd wr = s₁ := by
      rw [State.withRegions_withRegions, ← hr, ← hwr]; rfl
    rw [this]; exact hpost

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

theorem mem_enter {i : Instr} (h : i ∈ instrs (.block enter : Prog isa)) : i ∈ instrs Impl.Sha3.Arm.permute := by
  simp only [Impl.Sha3.Arm.permute, enterCall, instrs, List.mem_append]
  exact .inr (.inl h)

theorem mem_rounds {i : Instr} (h : i ∈ instrs rounds) : i ∈ instrs Impl.Sha3.Arm.permute := by
  simp only [Impl.Sha3.Arm.permute, roundsCall, instrs, List.mem_append]
  exact .inr (.inr (.inl h))

theorem mem_leave {i : Instr} (h : i ∈ instrs (.block leave : Prog isa)) : i ∈ instrs Impl.Sha3.Arm.permute := by
  simp only [Impl.Sha3.Arm.permute, leaveCall, instrs, List.mem_append]
  exact .inr (.inr (.inr (.inl h)))

/-- The state and the permutation's part of a scratch space of `N` bytes. -/
theorem covers_of {wr : List Region} {st scr : BitVec 32} {N : Nat} (hN : 512 ≤ N)
    (hS : regR st 200 ∈ wr) (hC : regR scr N ∈ wr) : Covers [regR st 200, regR scr 512] wr := by
  apply Covers.of_sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, hS, 0, by simp, by simp⟩
  · exact ⟨_, hC, 0, by simp, by simpa using hN⟩

theorem covers_all {s : State} {wr : List Region} (hw : Covers wr s.wr) :
    Covers ([] ++ wr) (s.rd ++ s.wr) := by
  intro a n h
  obtain ⟨r, hr, hc⟩ := hw a n (by simpa using h)
  exact ⟨r, List.mem_append_right _ hr, hc⟩

section
variable {s : State} {st scr : BitVec 32} (h0 : s.gpr .r0 = st) (h1 : s.gpr .r1 = scr)
  (fS : st.toNat + 200 ≤ 2 ^ 32) (fC : scr.toNat + 512 ≤ 2 ^ 32)
  (d₁ : Region.Disjoint (regR st 200) (regR scr 512))
include h0 h1 fS fC d₁

/-- The state a call enters `enter`, the rounds or `leave` in, with its
permissions narrowed to the state and the scratch space. -/
theorem pre_entry : Pre (s.callEntry.withRegions [] [regR st 200, regR scr 512]) := by
  have c0 : s.callEntry.gpr .r0 = st := (State.callEntry_gpr _ (by decide)).trans h0
  have c1 : s.callEntry.gpr .r1 = scr := (State.callEntry_gpr _ (by decide)).trans h1
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · show [regR st 200, regR scr 512] = [regR (s.callEntry.gpr .r0) 200, regR (s.callEntry.gpr .r1) 512]
    rw [c0, c1]
  · show (regR (s.callEntry.gpr .r0) 200).Disjoint (regR (s.callEntry.gpr .r1) 512)
    rw [c0, c1]; exact d₁
  · show (s.callEntry.gpr .r0).toNat + 200 ≤ 2 ^ 32
    rw [c0]; exact fS
  · show (s.callEntry.gpr .r1).toNat + 512 ≤ 2 ^ 32
    rw [c1]; exact fC

variable (hw : Covers [regR st 200, regR scr 512] s.wr) {Q : State → Prop}
include hw

/-- Calling `enter` on the state at `r0`, with scratch space at `r1`. -/
theorem enter_call
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → s'.gpr .r0 = st → s'.gpr .r1 = scr →
      Frame [regR scr 392] s.mem s'.mem → Stored s'.mem scr (stateAt s.mem (State.addr st)) →
      RCs scr s'.mem → Q s') : WP isa enterCall s Q := by
  have c0 : s.callEntry.gpr .r0 = st := (State.callEntry_gpr _ (by decide)).trans h0
  have c1 : s.callEntry.gpr .r1 = scr := (State.callEntry_gpr _ (by decide)).trans h1
  refine call_kept (pre := Pre) (post := fun t t' => Stored t'.mem (scp t) (A₀ t) ∧ Aux t t'.mem ∧
    Frame [regR (scp t) 392] t.mem t'.mem) (fun t ht => enter_correct ht) (pre_entry h0 h1 fS fC d₁)
    (covers_all hw) hw (fun s' hrd hwr hsp _ hg hpost => ?_) rfl
  have hpost' : Stored s'.mem (s.callEntry.gpr .r1) (stateAt s.mem (State.addr (s.callEntry.gpr .r0))) ∧
      RCs (s.callEntry.gpr .r1) s'.mem ∧ Frame [regR (s.callEntry.gpr .r1) 392] s.mem s'.mem := hpost
  rw [c0, c1] at hpost'
  exact hQ s' hrd hwr hsp (by rw [hg _ (fun i hi => permute_r0 i (mem_enter hi)) (by decide), h0])
    (by rw [hg _ (fun i hi => permute_r1 i (mem_enter hi)) (by decide), h1]) hpost'.2.2 hpost'.1 hpost'.2.1

/-- Calling the rounds on the state `K`, interleaved in the scratch space
at `r1`, with the round constants. -/
theorem rounds_call {K : KState} (hK : Stored s.mem scr K) (hrc : RCs scr s.mem)
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → s'.gpr .r0 = st → s'.gpr .r1 = scr →
      Frame [regR st 200, regR scr 512] s.mem s'.mem → Stored s'.mem scr (keccakF K) → RCs scr s'.mem →
      (∀ d, 396 ≤ d → d + 4 ≤ 432 → s'.mem.readW (A scr d) 32 = s.mem.readW (A scr d) 32) → Q s') :
    WP isa roundsCall s Q := by
  have c0 : s.callEntry.gpr .r0 = st := (State.callEntry_gpr _ (by decide)).trans h0
  have c1 : s.callEntry.gpr .r1 = scr := (State.callEntry_gpr _ (by decide)).trans h1
  refine call_kept (pre := fun t => Pre t ∧ Stored t.mem (scp t) K ∧ Aux t t.mem)
    (post := fun t t' => Stored t'.mem (scp t) (keccakF K) ∧ Aux t t'.mem ∧
      ∀ d, 396 ≤ d → d + 4 ≤ 432 → t'.mem.readW (A (scp t) d) 32 = t.mem.readW (A (scp t) d) 32)
    (fun t ht => rounds_correct ht.1 ht.2.1 ht.2.2) ⟨pre_entry h0 h1 fS fC d₁, ?_, ?_⟩
    (covers_all hw) hw (fun s' hrd hwr hsp hf hg hpost => ?_) rfl
  · show Stored s.mem (s.callEntry.gpr .r1) K
    rw [c1]; exact hK
  · show RCs (s.callEntry.gpr .r1) s.mem
    rw [c1]; exact hrc
  have hpost' : Stored s'.mem (s.callEntry.gpr .r1) (keccakF K) ∧ RCs (s.callEntry.gpr .r1) s'.mem ∧
      ∀ d, 396 ≤ d → d + 4 ≤ 432 →
        s'.mem.readW (A (s.callEntry.gpr .r1) d) 32 = s.mem.readW (A (s.callEntry.gpr .r1) d) 32 := hpost
  rw [c1] at hpost'
  exact hQ s' hrd hwr hsp (by rw [hg _ (fun i hi => permute_r0 i (mem_rounds hi)) (by decide), h0])
    (by rw [hg _ (fun i hi => permute_r1 i (mem_rounds hi)) (by decide), h1]) hf hpost'.1 hpost'.2.1
    hpost'.2.2

/-- Calling `leave` for the state `K`, interleaved in the scratch space at
`r1`. -/
theorem leave_call {K : KState} (hK : Stored s.mem scr K)
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → s'.gpr .r0 = st → s'.gpr .r1 = scr →
      Frame [regR st 200] s.mem s'.mem → stateAt s'.mem (State.addr st) = K → Q s') :
    WP isa leaveCall s Q := by
  have c0 : s.callEntry.gpr .r0 = st := (State.callEntry_gpr _ (by decide)).trans h0
  have c1 : s.callEntry.gpr .r1 = scr := (State.callEntry_gpr _ (by decide)).trans h1
  refine call_kept (pre := fun t => Pre t ∧ Stored t.mem (scp t) K)
    (post := fun t t' => stateAt t'.mem (State.addr (stp t)) = K ∧ Frame [regR (stp t) 200] t.mem t'.mem)
    (fun t ht => leave_correct ht.1 ht.2) ⟨pre_entry h0 h1 fS fC d₁, ?_⟩
    (covers_all hw) hw (fun s' hrd hwr hsp _ hg hpost => ?_) rfl
  · show Stored s.mem (s.callEntry.gpr .r1) K
    rw [c1]; exact hK
  have hpost' : stateAt s'.mem (State.addr (s.callEntry.gpr .r0)) = K ∧
      Frame [regR (s.callEntry.gpr .r0) 200] s.mem s'.mem := hpost
  rw [c0] at hpost'
  exact hQ s' hrd hwr hsp (by rw [hg _ (fun i hi => permute_r0 i (mem_leave hi)) (by decide), h0])
    (by rw [hg _ (fun i hi => permute_r1 i (mem_leave hi)) (by decide), h1]) hpost'.2 hpost'.1

end

/-! ## The whole function -/

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

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa permute s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha3.permuteArm.post s₀ s' := by
  have fC := hp.fitC
  have fS := hp.fitS
  unfold permute
  refine WP.seq ?_
  rw [← List.append_nil (saved.map _)]
  refine saveA_ok saved s₀ _ (fun p hp' => ⟨(saved_ok p hp').2.1, hp.scr_in (by have := saved_ok p hp'; omega)⟩)
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => WP.block_nil ?_
  have f₁ : Frame [regR (scp s₀) 512] s₀.mem s₁.mem := by
    rw [m₁]; exact saveMemA_frame fC _ _ _ (fun p hp' => by have := saved_ok p hp'; omega)
  have hw : ∀ s : State, s.wr = s₀.wr → Covers [regR (stp s₀) 200, regR (scp s₀) 512] s.wr := fun s h => by
    rw [h, hp.wr]; exact covers_of (N := 512) (Nat.le_refl _) (by simp) (by simp)
  have hA : stateAt s₁.mem (State.addr (stp s₀)) = A₀ s₀ :=
    stateAt_eq fS fun j hj => by
      rw [rd64_frame f₁ (fun r hr => by simp at hr; subst hr; exact hp.disj) fS (by omega_arith),
        ← stateAt_get fS _ hj]
      exact (getElem!_pos _ j hj).symm
  -- The saved registers are kept by `enter`, the rounds and `leave`.
  refine WP.seq (enter_call (by rw [g₁]) (by rw [g₁]) fS fC hp.disj (hw s₁ wr₁)
    fun s₂ rd₂ wr₂ sp₂ r0₂ r1₂ f₂ hst₂ hrc₂ => ?_)
  rw [hA] at hst₂
  refine WP.seq (rounds_call r0₂ r1₂ fS fC hp.disj (hw s₂ (wr₂.trans wr₁)) hst₂ hrc₂
    fun s₃ rd₃ wr₃ sp₃ r0₃ r1₃ _ hst₃ _ k₃ => ?_)
  refine WP.seq (leave_call r0₃ r1₃ fS fC hp.disj (hw s₃ (wr₃.trans (wr₂.trans wr₁))) hst₃
    fun s₄ rd₄ wr₄ sp₄ r0₄ r1₄ f₄ hst₄ => ?_)
  rw [show restore = saved.map (fun p => Instr.ldr p.1 .r1 p.2) ++ [] by rw [List.append_nil]; rfl]
  refine restoreA_ok saved s₄ _ (by decide) (fun p hp' => ⟨(saved_ok p hp').1, (saved_ok p hp').2.1, ?_⟩)
    fun s' ho _ hm => WP.block_nil ⟨fun r hr => ?_, ?_⟩
  · rw [rd₄, wr₄, rd₃, wr₃, rd₂, wr₂, rd₁, wr₁, r1₄]
    exact mem_rd (hp.scr_in (by have := saved_ok p hp'; omega))
  · obtain ⟨p, hp', rfl⟩ := preserved_saved r hr
    obtain ⟨-, -, a, b⟩ := saved_ok p hp'
    rw [ho p hp', r1₄, f₄.readW (Region.contains_self _ _)
      (by simpa using hp.off_st (d := p.2) (n := 4) (by omega_arith) (by decide)) (by decide), k₃ _ a b,
      f₂.readW (Region.contains_self _ _)
        (by simpa using hp.off_scr (d := p.2) (n := 4) (k := 392) (by omega_arith) (by omega_arith) (by decide))
        (by decide), m₁]
    exact saveMemA_saved _ fC _ p hp'
  · show stateAt s'.mem (State.addr (stp s₀)) = keccakF (A₀ s₀)
    rw [hm]; exact hst₄

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
scratch space, arithmetic on 32-bit values, and what `absorb` and `squeeze`
do alike between one `enter` and one `leave`: the variables and saved
registers in the scratch space (`Hi`, `bulkLoad_ok`, `bulkStore_ok`,
`bulkRestore_ok`), the tests of the bytes left (`wp_geq`), and the runs of
lanes of a block of each rate (`ladder_ok`).
-/

namespace VG.Proof.Sha3.Arm

open VG VG.Arm VG.Impl.Sha3.Arm
open VG.Spec.Sha3 (stateAt keccakF)
open VG.Proof.Sha512.Arm (A A_eq contains_A)
open VG.Proof.Sha3 (off_disjoint sub_offset add_zero')

/-! ## The permutation -/

theorem permute_noFrames : permute.noFrames = true := by lit_decide

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
  refine WP.callCalls (k := Proof.Sha3.permuteArm) permute_verified.1
    (rd := []) (wr := [regR st 200, regR scr 512]) ?_ ?_ hw ?_ permute_noFrames
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

theorem shl2_ofNat32 (k : Nat) : BitVec.ofNat 32 k <<< 2 = BitVec.ofNat 32 (4 * k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_using []

/-- A byte of a word stored. -/
theorem writeW32_apply (m : Mem) (a : Addr) (v : BitVec 32) (x : Addr) :
    m.writeW a v x = if (x - a).toNat < 4 then v.extractLsb' (8 * (x - a).toNat) 8 else m x := by
  change (if (x - a).toNat < 4 then (v.setWidth 32).extractLsb' (8 * (x - a).toNat) 8 else m x) = _
  rw [BitVec.setWidth_eq]

/-! ## The words left of the data and of the block -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mvn {d : Reg} {o : Op2} {v : BitVec 32} (ho : o.eval s = some v)
    (k : ∀ s', VG.Proof.MdStream.Arm.Upd s s' d (~~~v) → WP isa (.block is) s' Q) :
    WP isa (.block (.mvn d o :: is)) s Q :=
  VG.Proof.MdStream.Arm.WP.cons (s' := s.setReg d (~~~v)) (by simp [exec, ho])
    (k _ (VG.Proof.MdStream.Arm.Upd.setReg _ _ _))

/-- `subs`, with its carry: set when the subtraction does not borrow. -/
theorem wp_subsC {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', VG.Proof.MdStream.Arm.Upd s s' d (s.gpr n - y) →
      s'.c = decide (y.toNat ≤ (s.gpr n).toNat) → WP isa (.block is) s' Q) :
    WP isa (.block (.subs d n o :: is)) s Q :=
  VG.Proof.MdStream.Arm.WP.cons (s' := (subFlags s (s.gpr n) y).setReg d (s.gpr n - y)) (by simp [exec, ho])
    (k _ (VG.Proof.MdStream.Arm.Upd.subs _ _ _ _ _) rfl)

end

/-- `words`, from `r7 = l` bytes left of the data or the output, the position
`r5 = j` and the rate `r4 = rt`: `lr` is the number of whole words among the
bytes left of both, and Z is set if there is none. It changes only `r2`,
`r3`, `r12`, `lr` and the flags. -/
theorem words_ok {s : State} {l j rt : Nat} (h7 : s.gpr .r7 = BitVec.ofNat 32 l)
    (h5 : s.gpr .r5 = BitVec.ofNat 32 j) (h4 : s.gpr .r4 = BitVec.ofNat 32 rt) (hl : l < 2 ^ 32)
    (hj : j ≤ rt) (hrt : rt < 2 ^ 32) :
    WP isa (.block Impl.Sha3.Arm.Stream.words) s fun s' =>
      (∀ r, r ∉ [Reg.r2, .r3, .r12, .lr] → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.gpr .lr = BitVec.ofNat 32 (min l (rt - j) / 4) ∧
      s'.z = decide (min l (rt - j) / 4 = 0) := by
  open VG.Proof.MdStream.Arm in
  unfold Impl.Sha3.Arm.Stream.words
  refine wp_sub (op2_reg _ _) fun s₁ u₁ => wp_mvn (op2_imm (by decide)) fun s₂ u₂ =>
    wp_subsC (op2_reg _ _) fun s₃ u₃ hc => VG.Proof.Sha512.Arm.wp_adc (op2_imm (by decide)) fun s₄ u₄ =>
    wp_and (op2_reg _ _) fun s₅ u₅ => wp_add (op2_reg _ _) fun s₆ u₆ =>
    wp_mov (op2_lsr (by decide)) fun s₇ u₇ => wp_cmp (op2_imm (by decide)) fun s₈ u₈ hz => WP.block_nil ?_
  have e12 : s₁.gpr .r12 = BitVec.ofNat 32 (rt - j) := by rw [u₁.gpr, h4, h5, sub_ofNat32 hj]
  have e7 : s₂.gpr .r7 = BitVec.ofNat 32 l := by rw [u₂.other _ (by decide), u₁.other _ (by decide), h7]
  have e12' : s₂.gpr .r12 = BitVec.ofNat 32 (rt - j) := by rw [u₂.other _ (by decide), e12]
  have hc' : s₃.c = decide (rt - j ≤ l) := by
    rw [hc, e7, e12', BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl,
      Nat.mod_eq_of_lt (by omega_using [hrt])]
  have e2 : s₆.gpr .r2 = BitVec.ofNat 32 (min l (rt - j)) := by
    have a12 : s₅.gpr .r12 = BitVec.ofNat 32 (rt - j) := by
      rw [u₅.other .r12 (by decide), u₄.other .r12 (by decide), u₃.other .r12 (by decide), e12']
    have a2 : s₄.gpr .r2 = BitVec.ofNat 32 l - BitVec.ofNat 32 (rt - j) := by
      rw [u₄.other .r2 (by decide), u₃.gpr, e7, e12']
    have a3 : s₄.gpr .r3 = ~~~0 + 0 + (if s₃.c then 1 else 0) := by
      rw [u₄.gpr, u₃.other .r3 (by decide), u₂.gpr]
    rw [u₆.gpr, a12, u₅.gpr, a2, a3, hc']
    by_cases h : rt - j ≤ l
    · rw [decide_eq_true h, Nat.min_eq_right h, ite_eq_left rfl,
        show (~~~(0 : BitVec 32)) + 0 + 1 = 0#32 by decide, BitVec.and_zero, BitVec.add_zero]
    · rw [decide_eq_false h, Nat.min_eq_left (by omega_using [h]), ite_eq_right (by decide),
        show (~~~(0 : BitVec 32)) + 0 + 0 = BitVec.allOnes 32 by decide, BitVec.and_allOnes,
        BitVec.add_comm, BitVec.sub_add_cancel]
  have elr : s₇.gpr .lr = BitVec.ofNat 32 (min l (rt - j) / 4) := by
    rw [u₇.gpr, e2, ofNat_shr (by omega_using [hl])]
  refine ⟨fun r hr => ?_, by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem],
    by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd],
    by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr],
    by rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp], by rw [u₈.gpr, elr], ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨a, b, c, d⟩ := hr
    rw [u₈.gpr, u₇.other r d, u₆.other r a, u₅.other r a, u₄.other r b, u₃.other r a, u₂.other r b,
      u₁.other r c]
  · rw [hz, elr, sub_imm0, ofNat32_beq_zero (by omega_using [hl])]

/-! ## Several blocks between one `enter` and one `leave` -/

section
open VG.Impl.Sha3.Arm.Stream (vRate vPtr vLeft savedHi bulkSave bulkLoad bulkStore bulkRestore rung ladder)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd wp_ldr wp_str wp_sub wp_add wp_mov wp_cmp op2_reg op2_imm eval_eq
  sub_beq)
open VG.Proof.Sha512.Arm (mem_rd wp_adc)
open VG.Arm.Straight (wordAddr)
open VG.Spec.Sha3 (rates)

theorem Stored.keep {scr : BitVec 32} {K : KState} {m m' : Mem} (h : Stored m scr K)
    (hk : ∀ d, d + 4 ≤ 200 → m'.readW (A scr d) 32 = m.readW (A scr d) 32) : Stored m' scr K :=
  fun j hj h' hh => by
    rw [wordAddr_eq, hk _ (by omega_using [hj, hh]), ← wordAddr_eq]; exact h j hj h' hh

theorem RCs.keep {scr : BitVec 32} {m m' : Mem} (h : RCs scr m)
    (hk : ∀ d, 200 ≤ d → d + 4 ≤ 392 → m'.readW (A scr d) 32 = m.readW (A scr d) 32) : RCs scr m' :=
  fun i hi => by
    rw [wordAddr_eq, hk _ (by omega_using [hi]) (by omega_using [hi]), ← wordAddr_eq]; exact h i hi

theorem savedHi_ok : ∀ p ∈ savedHi, p.1 ≠ .r1 ∧ p.2 < 4096 ∧ 544 ≤ p.2 ∧ p.2 + 4 ≤ 560 := by decide

theorem savedHi_regs : ∀ p ∈ savedHi, p.1 ∈ [Reg.r8, .r9, .r10, .r11] := by decide

/-- Writes to the first `k` bytes of the scratch space keep its words after
them. -/
theorem readW_above {scr : BitVec 32} (fC : scr.toNat + 640 ≤ 2 ^ 32) {m m' : Mem} {k : Nat}
    (hf : Frame [regR scr k] m m') {d : Nat} (hd₁ : k ≤ d) (hd₂ : d + 4 ≤ 640) :
    m'.readW (A scr d) 32 = m.readW (A scr d) 32 := by
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rw [List.mem_singleton.mp hr]
  have := off_disjoint (State.addr scr) (a := d) (n := 4) (b := 0) (k := k) (by omega_using [hd₂])
    (by omega_using [hd₁, hd₂]) (.inr (by omega_using [hd₁]))
  rw [add_zero'] at this
  rw [A_eq (by omega_using [fC, hd₂])]; exact this

/-- The words of the scratch space after the permutation's part, between
`enter` and `leave`: our caller's registers `g`, and the variables. -/
structure Hi (scr : BitVec 32) (g : Reg → BitVec 32) (rate ptr left : BitVec 32) (m : Mem) : Prop where
  saved : SSaved scr g m
  hi : ∀ p ∈ savedHi, m.readW (A scr p.2) 32 = g p.1
  rate : m.readW (A scr vRate) 32 = rate
  ptr : m.readW (A scr vPtr) 32 = ptr
  left : m.readW (A scr vLeft) 32 = left

theorem Hi.keep {scr : BitVec 32} {g : Reg → BitVec 32} {r p l : BitVec 32} {m m' : Mem}
    (h : Hi scr g r p l m)
    (hk : ∀ d, 512 ≤ d → d + 4 ≤ 640 → m'.readW (A scr d) 32 = m.readW (A scr d) 32) :
    Hi scr g r p l m' where
  saved := h.saved.keep fun d h₁ h₂ => hk d h₁ (by omega_using [h₂])
  hi q hq := by obtain ⟨-, -, a, b⟩ := savedHi_ok q hq; rw [hk _ (by omega_using [a]) (by omega_using [b])]; exact h.hi q hq
  rate := by rw [hk _ (by decide) (by decide)]; exact h.rate
  ptr := by rw [hk _ (by decide) (by decide)]; exact h.ptr
  left := by rw [hk _ (by decide) (by decide)]; exact h.left

/-- Writes to the state and to the permutation's scratch space keep them. -/
theorem Hi.frame {st scr : BitVec 32} (fC : scr.toNat + 640 ≤ 2 ^ 32)
    (hd : Region.Disjoint (regR st 200) (regR scr 640)) {g : Reg → BitVec 32} {r p l : BitVec 32}
    {m m' : Mem} (h : Hi scr g r p l m) {rs : List Region} (hf : Frame rs m m')
    (hrs : ∀ r ∈ rs, r = regR st 200 ∨ r = regR scr 512) : Hi scr g r p l m' :=
  h.keep fun _ hd₁ hd₂ => readW_hi fC hd hf hrs hd₁ hd₂

/-- The memory after storing the variables. -/
def storeVars (m : Mem) (scr r p l : BitVec 32) : Mem :=
  ((m.writeW (A scr vPtr) p).writeW (A scr vRate) r).writeW (A scr vLeft) l

/-- The other words of the scratch space are kept. -/
theorem storeVars_keep (m : Mem) {scr : BitVec 32} (fC : scr.toNat + 640 ≤ 2 ^ 32) (r p l : BitVec 32)
    {d : Nat} (hd : d + 4 ≤ 640) (hne : d + 4 ≤ 532 ∨ 544 ≤ d) :
    (storeVars m scr r p l).readW (A scr d) 32 = m.readW (A scr d) 32 := by
  simp only [storeVars, vRate, vPtr, vLeft]
  rw [readW_writeW_A _ fC _ hd (by decide) (by omega_using [hne]),
    readW_writeW_A _ fC _ hd (by decide) (by omega_using [hne]),
    readW_writeW_A _ fC _ hd (by decide) (by omega_using [hne])]

theorem storeVars_frame (m : Mem) {scr : BitVec 32} (fC : scr.toNat + 640 ≤ 2 ^ 32) (r p l : BitVec 32) :
    Frame [regR scr 640] m (storeVars m scr r p l) :=
  (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_A fC (by decide))).writeW
    (List.mem_singleton_self _) _ (contains_A fC (by decide))).writeW (List.mem_singleton_self _) _
    (contains_A fC (by decide))

theorem Hi.store {scr : BitVec 32} (fC : scr.toNat + 640 ≤ 2 ^ 32) {g : Reg → BitVec 32}
    {r p l : BitVec 32} {m : Mem} (h : Hi scr g r p l m) (r' p' l' : BitVec 32) :
    Hi scr g r' p' l' (storeVars m scr r' p' l') where
  saved := h.saved.keep fun d _ h₂ => storeVars_keep m fC _ _ _ (by omega_using [h₂]) (.inl h₂)
  hi q hq := by
    obtain ⟨-, -, a, b⟩ := savedHi_ok q hq
    rw [storeVars_keep m fC _ _ _ (by omega_using [b]) (.inr a)]; exact h.hi q hq
  rate := by
    simp only [storeVars, vRate, vPtr, vLeft]
    rw [readW_writeW_A _ fC _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  ptr := by
    simp only [storeVars, vRate, vPtr, vLeft]
    rw [readW_writeW_A _ fC _ (by decide) (by decide) (by decide),
      readW_writeW_A _ fC _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
  left := by
    simp only [storeVars, vRate, vPtr, vLeft]
    rw [Mem.readW_writeW_self32]

/-- The registers that `bulkSave` stores, and where. -/
def saveL : List (Reg × Nat) := savedHi ++ [(.r4, vRate), (.r6, vPtr), (.r7, vLeft)]

theorem bulkSave_eq : bulkSave = saveL.map (fun p => Instr.str p.1 .r1 p.2) ++ [] := rfl

theorem saveL_ok : ∀ p ∈ saveL, p.2 < 4096 ∧ 532 ≤ p.2 ∧ p.2 + 4 ≤ 560 := by decide

set_option simprocs false in
/-- `bulkSave`: our caller's `r8`–`r11` and the variables, after the saved
registers `g₀`. -/
theorem saveMemA_hi {m : Mem} {b : BitVec 32} (hfit : b.toNat + 640 ≤ 2 ^ 32) {g₀ : Reg → BitVec 32}
    (h : SSaved b g₀ m) (g : Reg → BitVec 32) (hg : ∀ p ∈ savedHi, g p.1 = g₀ p.1) :
    Hi b g₀ (g .r4) (g .r6) (g .r7) (saveMemA m b g saveL) := by
  have lo : ∀ d, d + 4 ≤ 532 → (saveMemA m b g saveL).readW (A b d) 32 = m.readW (A b d) 32 := fun d hd => by
    simp (disch := omega_using [hd]) only [saveL, savedHi, vRate, vPtr, vLeft, List.cons_append,
      List.nil_append, saveMemA, readW_writeW_A (hfit := hfit)]
  refine ⟨h.keep fun d _ h₂ => lo d h₂, fun p hp => ?_, ?_, ?_, ?_⟩
  · rw [← hg p hp]
    simp only [savedHi, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;>
    simp (disch := omega_arith) only [saveL, savedHi, vRate, vPtr, vLeft, List.cons_append,
      List.nil_append, saveMemA, Mem.readW_writeW_self32, readW_writeW_A (hfit := hfit)]
  all_goals
    simp (disch := omega_arith) only [saveL, savedHi, vRate, vPtr, vLeft, List.cons_append,
      List.nil_append, saveMemA, Mem.readW_writeW_self32, readW_writeW_A (hfit := hfit)]

section
variable {s : State} {scr : BitVec 32} (h1 : s.gpr .r1 = scr)
  (hin : ∀ d, d + 4 ≤ 640 → InRegions s.wr (A scr d) 4) {rest : List Instr} {Q : State → Prop}
include h1 hin

/-- `bulkLoad`: the masks, and the variables in `r9`, `r10` and `r11`. -/
theorem bulkLoad_ok
    (k : ∀ s', Masks s' → s'.gpr .r9 = s.mem.readW (A scr vPtr) 32 →
      s'.gpr .r10 = s.mem.readW (A scr vRate) 32 → s'.gpr .r11 = s.mem.readW (A scr vLeft) 32 →
      s'.gpr .r0 = s.gpr .r0 → s'.gpr .r1 = scr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → WP isa (.block rest) s' Q) :
    WP isa (.block (bulkLoad ++ rest)) s Q := by
  unfold bulkLoad
  rw [List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, hs₁, hm, m₁, rd₁, wr₁, sp₁, g₁⟩ := masks_ok s
  refine WP.of_runBlock ⟨s₁, hs₁, ?_⟩
  have e1 : s₁.gpr .r1 = scr := (g₁ .r1 (by decide)).trans h1
  refine wp_ldr (a := A scr vPtr) (by decide) (by rw [e1])
    (by rw [rd₁, wr₁]; exact mem_rd (hin _ (by decide))) fun s₂ u₂ => ?_
  refine wp_ldr (a := A scr vRate) (by decide) (by rw [u₂.other .r1 (by decide), e1])
    (by rw [u₂.rd, u₂.wr, rd₁, wr₁]; exact mem_rd (hin _ (by decide))) fun s₃ u₃ => ?_
  refine wp_ldr (a := A scr vLeft) (by decide)
    (by rw [u₃.other .r1 (by decide), u₂.other .r1 (by decide), e1])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, rd₁, wr₁]; exact mem_rd (hin _ (by decide))) fun s₄ u₄ => ?_
  obtain ⟨m4, m5, m6, m7, m8⟩ := hm
  refine k s₄ ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), m4]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), m5]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), m6]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), m7]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), m8]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, m₁]
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.mem, m₁]
  · rw [u₄.gpr, u₃.mem, u₂.mem, m₁]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁ .r0 (by decide)]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), e1]
  · rw [u₄.mem, u₃.mem, u₂.mem, m₁]
  · rw [u₄.rd, u₃.rd, u₂.rd, rd₁]
  · rw [u₄.wr, u₃.wr, u₂.wr, wr₁]
  · rw [u₄.sp, u₃.sp, u₂.sp, sp₁]

/-- `bulkStore`: a block taken off the bytes left, and the variables stored. -/
theorem bulkStore_ok
    (k : ∀ s', s'.gpr .r11 = s.gpr .r11 - s.gpr .r10 → (∀ r, r ≠ .r11 → s'.gpr r = s.gpr r) →
      s'.mem = storeVars s.mem scr (s.gpr .r10) (s.gpr .r9) (s.gpr .r11 - s.gpr .r10) →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → WP isa (.block rest) s' Q) :
    WP isa (.block (bulkStore ++ rest)) s Q := by
  unfold bulkStore
  simp only [List.cons_append, List.nil_append]
  refine wp_sub (op2_reg _ _) fun s₁ u₁ => ?_
  have e1 : s₁.gpr .r1 = scr := (u₁.other .r1 (by decide)).trans h1
  refine wp_str (a := A scr vPtr) (by decide) (by rw [e1]) (by rw [u₁.wr]; exact hin _ (by decide))
    fun s₂ u₂ => ?_
  refine wp_str (a := A scr vRate) (by decide) (by rw [u₂.gpr, e1])
    (by rw [u₂.wr, u₁.wr]; exact hin _ (by decide)) fun s₃ u₃ => ?_
  refine wp_str (a := A scr vLeft) (by decide) (by rw [u₃.gpr, u₂.gpr, e1])
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hin _ (by decide)) fun s₄ u₄ => ?_
  refine k s₄ (by rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr])
    (fun r hr => by rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.other r hr]) ?_ (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]) (by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp])
  rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₃.gpr, u₂.gpr, u₁.gpr, u₁.other .r9 (by decide),
    u₁.other .r10 (by decide)]
  rfl

end

theorem bulkRestore_eq : bulkRestore = [.ldr .r4 .r1 vRate, .ldr .r6 .r1 vPtr, .ldr .r7 .r1 vLeft,
    .mov .r5 (.imm 0), .ldr .r8 .r1 544, .ldr .r9 .r1 548, .ldr .r10 .r1 552, .ldr .r11 .r1 556] := rfl

/-- `bulkRestore`: the variables in their registers, the position 0, and
our caller's `r8`–`r11`. -/
theorem bulkRestore_ok {s : State} {scr : BitVec 32} {g : Reg → BitVec 32} {r p l : BitVec 32}
    (h1 : s.gpr .r1 = scr) (hin : ∀ d, d + 4 ≤ 640 → InRegions s.wr (A scr d) 4)
    (hH : Hi scr g r p l s.mem) {Q : State → Prop}
    (k : ∀ s', s'.gpr .r4 = r → s'.gpr .r5 = 0 → s'.gpr .r6 = p → s'.gpr .r7 = l →
      (∀ q ∈ [Reg.r8, .r9, .r10, .r11], s'.gpr q = g q) → s'.gpr .r0 = s.gpr .r0 → s'.gpr .r1 = scr →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Q s') :
    WP isa (.block bulkRestore) s Q := by
  rw [bulkRestore_eq]
  refine wp_ldr (a := A scr vRate) (by decide) (by rw [h1]) (mem_rd (hin _ (by decide))) fun s₁ u₁ => ?_
  refine wp_ldr (a := A scr vPtr) (by decide) (by rw [u₁.other .r1 (by decide), h1])
    (by rw [u₁.rd, u₁.wr]; exact mem_rd (hin _ (by decide))) fun s₂ u₂ => ?_
  refine wp_ldr (a := A scr vLeft) (by decide)
    (by rw [u₂.other .r1 (by decide), u₁.other .r1 (by decide), h1])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact mem_rd (hin _ (by decide))) fun s₃ u₃ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₄ u₄ => ?_
  have e1 : s₄.gpr .r1 = scr := by
    rw [u₄.other .r1 (by decide), u₃.other .r1 (by decide), u₂.other .r1 (by decide),
      u₁.other .r1 (by decide), h1]
  have em : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have erd : s₄.rd = s.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have ewr : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  refine wp_ldr (a := A scr 544) (by decide) (by rw [e1])
    (by rw [erd, ewr]; exact mem_rd (hin _ (by decide))) fun s₅ u₅ => ?_
  refine wp_ldr (a := A scr 548) (by decide) (by rw [u₅.other .r1 (by decide), e1])
    (by rw [u₅.rd, u₅.wr, erd, ewr]; exact mem_rd (hin _ (by decide))) fun s₆ u₆ => ?_
  refine wp_ldr (a := A scr 552) (by decide)
    (by rw [u₆.other .r1 (by decide), u₅.other .r1 (by decide), e1])
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, erd, ewr]; exact mem_rd (hin _ (by decide))) fun s₇ u₇ => ?_
  refine wp_ldr (a := A scr 556) (by decide)
    (by rw [u₇.other .r1 (by decide), u₆.other .r1 (by decide), u₅.other .r1 (by decide), e1])
    (by rw [u₇.rd, u₇.wr, u₆.rd, u₆.wr, u₅.rd, u₅.wr, erd, ewr]; exact mem_rd (hin _ (by decide)))
    fun s₈ u₈ => WP.block_nil ?_
  have lo : ∀ q, q ∉ [Reg.r8, .r9, .r10, .r11] → s₈.gpr q = s₄.gpr q := fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    rw [u₈.other q hq.2.2.2, u₇.other q hq.2.2.1, u₆.other q hq.2.1, u₅.other q hq.1]
  refine k s₈ ?_ ?_ ?_ ?_ (fun q hq => ?_) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [lo _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.gpr, hH.rate]
  · rw [lo _ (by decide), u₄.gpr]
  · rw [lo _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem, hH.ptr]
  · rw [lo _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem, hH.left]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, em]
      exact hH.hi (.r8, 544) (by decide)
    · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.mem, em]
      exact hH.hi (.r9, 548) (by decide)
    · rw [u₈.other _ (by decide), u₇.gpr, u₆.mem, u₅.mem, em]
      exact hH.hi (.r10, 552) (by decide)
    · rw [u₈.gpr, u₇.mem, u₆.mem, u₅.mem, em]
      exact hH.hi (.r11, 556) (by decide)
  · rw [lo _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide)]
  · rw [lo _ (by decide), e1]
  · rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, em]
  · rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, erd]
  · rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, ewr]
  · rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]

/-! ### Lanes in memory -/

theorem rd64_add (m : Mem) (b : BitVec 32) (a o : Nat) :
    VG.Proof.Sha512.Arm.rd64 m (b + BitVec.ofNat 32 a) o = VG.Proof.Sha512.Arm.rd64 m b (a + o) := by
  simp only [VG.Proof.Sha512.Arm.rd64]; rw [A_add, A_add, Nat.add_assoc]

/-- A lane in memory, from its two words. -/
theorem rd64_eq (m : Mem) {b : BitVec 32} {o : Nat} (h : b.toNat + o + 8 ≤ 2 ^ 32) :
    VG.Proof.Sha512.Arm.rd64 m b o = m.readW (State.addr b + BitVec.ofNat 64 o) 64 := by
  rw [VG.Proof.Sha512.Arm.rd64, VG.Proof.Sha512.Arm.readW64, A_eq (by omega_using [h]),
    A_eq (by omega_using [h])]
  rw [show State.addr b + BitVec.ofNat 64 o + 4 = State.addr b + BitVec.ofNat 64 (o + 4) by bv_omega]

/-! ### The tests -/

/-- `d` is zero if `y ≤ x`, and all ones otherwise: `x - y` does not borrow,
and its carry is set, when `y ≤ x`. -/
theorem wp_geq {d n : Reg} {o : Op2} {x y : BitVec 32} {s : State} (hd : d ≠ .r2) (hnd : n ≠ d)
    (hn : s.gpr n = x) (ho : ∀ s', (∀ r, r ≠ d → s'.gpr r = s.gpr r) → o.eval s' = some y)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr d = (if y.toNat ≤ x.toNat then 0#32 else BitVec.allOnes 32) →
      (∀ r, r ≠ d → r ≠ .r2 → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → WP isa (.block rest) s' Q) :
    WP isa (.block (.mvn d (.imm 0) :: .subs .r2 n o :: .adc d d (.imm 0) :: rest)) s Q := by
  refine wp_mvn (op2_imm (by decide)) fun s₁ u₁ => wp_subsC (ho s₁ u₁.other) fun s₂ u₂ hc =>
    wp_adc (op2_imm (by decide)) fun s₃ u₃ => ?_
  refine k s₃ ?_ (fun r h₁ h₂ => by rw [u₃.other r h₁, u₂.other r h₂, u₁.other r h₁])
    (by rw [u₃.mem, u₂.mem, u₁.mem]) (by rw [u₃.rd, u₂.rd, u₁.rd]) (by rw [u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₃.sp, u₂.sp, u₁.sp])
  rw [u₃.gpr, u₂.other d hd, u₁.gpr, hc, u₁.other n hnd, hn]
  by_cases h : y.toNat ≤ x.toNat
  · rw [decide_eq_true h, ite_eq_left rfl, ite_eq_left h]; decide
  · rw [decide_eq_false h, ite_eq_right (by decide), ite_eq_right h]; decide

/-- Whether a register that is zero or all ones is zero. -/
theorem geq_beq {c : Prop} [Decidable c] :
    ((if c then 0#32 else BitVec.allOnes 32) - 0 == 0) = decide c := by
  by_cases h : c
  · rw [ite_eq_left h, decide_eq_true h]; decide
  · rw [ite_eq_right h, decide_eq_false h]; decide

/-! ### The lanes of a block -/

/-- A run of lanes that a rate reaches is within its block. -/
theorem segs_rate {rt : Nat} (hrt : rt ∈ rates) : ∀ p ∈ segs, p.1 = 0 ∨ rt ≠ 8 * p.1 → 8 * p.1 ≤ rt →
    8 * p.2 ≤ rt := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at hrt
  intro p hp
  simp only [segs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl <;> intro h₁ h₂ <;> omega_using [hrt, h₁, h₂]

theorem segs_imm : ∀ p ∈ segs, encodable (BitVec.ofNat 32 (8 * (p.2 - p.1))) = true ∧
    encodable (BitVec.ofNat 32 (8 * p.2)) = true := by decide

section
variable {seg : Nat → Nat → List Instr} {P : Nat → State → Prop} {rt : Nat}
  (h10 : ∀ a s, P a s → s.gpr .r10 = BitVec.ofNat 32 rt) (hF : ∀ a s s', P a s → Fupd s s' → P a s')
  (hseg : ∀ p ∈ segs, p.1 = 0 ∨ rt ≠ 8 * p.1 → ∀ s, P p.1 s → ∀ (rest : List Instr) (Q : State → Prop),
    (∀ s', P p.2 s' → WP isa (.block rest) s' Q) →
    WP isa (.block (seg p.1 p.2 ++
      .dp .add .r9 .r9 (.imm (BitVec.ofNat 32 (8 * (p.2 - p.1)))) :: rest)) s Q)
include h10 hF hseg

/-- A rung of the ladder: the lanes `a ≤ j < b`, and the rest unless the
rate is `8 b`. -/
theorem rung_ok {a b : Nat} (hp : (a, b) ∈ segs) (ha : a = 0 ∨ rt ≠ 8 * a) (hrt : rt < 2 ^ 32)
    {rest : Prog isa} {s : State} (h : P a s) {Q : State → Prop} (hb : rt = 8 * b → ∀ s', P b s' → Q s')
    (hrest : rt ≠ 8 * b → ∀ s', P b s' → WP isa rest s' Q) : WP isa (rung seg a b rest) s Q := by
  obtain ⟨-, hb21, -⟩ := segs_ok _ hp
  unfold rung
  refine WP.seq (hseg _ hp ha s h _ _ fun s₁ h₁ => ?_)
  refine wp_cmp (op2_imm (segs_imm _ hp).2) fun s₂ u₂ hz => WP.block_nil ?_
  rw [h10 _ _ h₁, sub_beq hrt (by have : b ≤ 21 := hb21; omega_using [this])] at hz
  refine WP.ite (decide (rt = 8 * b)) (by show VG.Arm.eval .eq s₂ = _; rw [eval_eq, hz])
    (fun hd => ?_) (fun hd => ?_)
  · exact WP.block_nil (hb (of_decide_eq_true hd) s₂ (hF _ _ _ h₁ u₂))
  · exact hrest (of_decide_eq_false hd) s₂ (hF _ _ _ h₁ u₂)

/-- The ladder: the lanes of a block of `rt` bytes. -/
theorem ladder_ok (hrt : rt ∈ rates) {s : State} (h : P 0 s) : WP isa (ladder seg) s (P (rt / 8)) := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at hrt
  have hlt : rt < 2 ^ 32 := by omega_using [hrt]
  unfold ladder
  refine rung_ok h10 hF hseg (by decide) (.inl rfl) hlt h (fun e s' h' => by rw [e]; exact h')
    fun n₁ s₁ h₁ => ?_
  refine rung_ok h10 hF hseg (by decide) (.inr n₁) hlt h₁ (fun e s' h' => by rw [e]; exact h')
    fun n₂ s₂ h₂ => ?_
  refine rung_ok h10 hF hseg (by decide) (.inr n₂) hlt h₂ (fun e s' h' => by rw [e]; exact h')
    fun n₃ s₃ h₃ => ?_
  refine rung_ok h10 hF hseg (by decide) (.inr n₃) hlt h₃ (fun e s' h' => by rw [e]; exact h')
    fun n₄ s₄ h₄ => ?_
  have e : rt = 8 * 21 := by omega_using [hrt, n₁, n₂, n₃, n₄]
  refine hseg (18, 21) (by decide) (.inr n₄) s₄ h₄ [] _ fun s' h' => WP.block_nil ?_
  rw [e]; exact h'

end

end

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

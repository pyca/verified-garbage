module

import VerifiedGarbage.Proof.Blake2.Spec
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.MdStream.Arm.Common
public import VerifiedGarbage.Proof.Blake2.Arm.Contract
public import VerifiedGarbage.Proof.Blake2.Stream
public import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.OmegaLit
public import VerifiedGarbage.Impl.Blake2.Arm.Stream
public import VerifiedGarbage.Proof.Framework.Arm.Call

/-! ### `Blake2.Arm.Stream.Common`, which this module and modules that import it used -/

section

@[expose] public section

section

/-!
# Streaming BLAKE2 on ARMv7: the calls of the compression function

The streaming functions call any compression function verified against
`compressArm P` that makes no calls (`CalleeOk`), in a frame that pushes its
stack arguments (`t` in `r3:r11`, `last` in `r12`, `scratch` in `lr`).
`call_ok` runs such a frame from the state before its push (`WP.frame`,
`WP.call`), and `call_rel` relates two runs of it (`RelCT.frame`,
`RelCT.call`), as for HMAC's calls of `update`
(`Proof/Pbkdf2/Stream/Arm/Hash.lean`). The frame writes the 16 bytes below the
stack pointer (`below`), which `After` lets change.
-/

namespace VG.Proof.Blake2.Arm.Stream

open VG.Arm VG.Spec.Blake2
open VG.Impl.Blake2.Arm.Stream (call)

/-- The 16 bytes below the stack pointer. -/
abbrev below (s : State) : Region := ⟨State.addr s.sp - 16, 16⟩

/-- What the streaming functions need of the compression function they call:
that it is verified against `compressArm P` and makes no calls. -/
structure CalleeOk {w : Nat} (P : Params w) (code : Prog isa) : Prop where
  verified : Verified Arm.target code (compressArm P)
  noCalls : code.noCalls = true

/-- What a call leaves: the regions, the stack pointer, the callee-saved
registers but `lr`, and memory outside what it may write and the 16 bytes
below the stack pointer. -/
structure After (s : State) (ws : List Region) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  cs : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame (ws ++ [below s]) s.mem s'.mem

theorem frame_app {ws ws' : List Region} {m m' : Mem} (h : Frame ws m m') : Frame (ws ++ ws') m m' :=
  h.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩

/-! The argument registers are not changed by the call instruction. -/

@[simp] theorem ce0 (s : State) : s.callEntry.gpr .r0 = s.gpr .r0 := State.callEntry_gpr s (by decide)
@[simp] theorem ce1 (s : State) : s.callEntry.gpr .r1 = s.gpr .r1 := State.callEntry_gpr s (by decide)
@[simp] theorem ce2 (s : State) : s.callEntry.gpr .r2 = s.gpr .r2 := State.callEntry_gpr s (by decide)

/-- `x - k + i` (for `i ≤ k ≤ x`) widened to 64 bits. -/
theorem addr_sub_add {x : BitVec 32} {k i : Nat} (hk : k ≤ x.toNat) (hi : i ≤ k) :
    State.addr (x - BitVec.ofNat 32 k + BitVec.ofNat 32 i) =
      State.addr x - BitVec.ofNat 64 k + BitVec.ofNat 64 i := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [State.addr, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := k) (by omega_nat), Nat.mod_eq_of_lt (a := i) (by omega_nat),
    Nat.mod_eq_of_lt (a := k) (by omega_nat), Nat.mod_eq_of_lt (a := i) (by omega_nat),
    Nat.mod_eq_of_lt (a := x.toNat) (by omega_nat),
    show 2 ^ 32 - k + x.toNat = 2 ^ 32 + (x.toNat - k) by omega_nat, Nat.add_mod_left,
    show 2 ^ 64 - k + x.toNat = 2 ^ 64 + (x.toNat - k) by omega_nat, Nat.add_mod_left]
  omega_nat

/-- `x - k` (for `k ≤ x`) widened to 64 bits. -/
theorem addr_sub {x : BitVec 32} {k : Nat} (hk : k ≤ x.toNat) :
    State.addr (x - BitVec.ofNat 32 k) = State.addr x - BitVec.ofNat 64 k := by
  have := addr_sub_add (i := 0) hk (Nat.zero_le _)
  simpa using this

/-- Bytes at two offsets from a base that do not overlap. -/
theorem sep_off (b : Addr) {d e n k : Nat} (h : d + n ≤ e ∨ e + k ≤ d) (hd : d + n < 2 ^ 32)
    (he : e + k < 2 ^ 32) : Mem.Sep (b + BitVec.ofNat 64 d) n (b + BitVec.ofNat 64 e) k :=
  Offset.sep b h (by omega_nat) (by omega_nat)

/-- Bytes at an offset from a region's base, in it. -/
theorem contains_off (b : Addr) {len d n : Nat} (h : d + n ≤ len) (hl : len < 2 ^ 64) :
    Region.Contains ⟨b, len⟩ (b + BitVec.ofNat 64 d) n := Offset.contains_base b h (by omega_nat)

section
variable {w : Nat}

/-- What a call needs of the state before its push: the hash value at `st`
in `r0`, the `n` blocks at `blk` in `r1` and `r2`, the counter `t` in
`r11:r3` (low word in `r3`), `last` in `r12` and the scratch space at `scr` in
`lr`; the regions the callee may read and write, disjoint as it needs, and
from the 16 bytes below the stack pointer; and that none of them wraps
around. -/
structure CallArgs (s : State) (st scr blk : BitVec 32) (n : Nat) (t : BitVec 64) (last : BitVec 32) :
    Prop where
  r0 : s.gpr .r0 = st
  r1 : s.gpr .r1 = blk
  r2 : s.gpr .r2 = BitVec.ofNat 32 n
  t : s.gpr .r11 ++ s.gpr .r3 = t
  r12 : s.gpr .r12 = last
  lr : s.gpr .lr = scr
  hn : n < 2 ^ 32
  sp16 : 16 ≤ s.sp.toNat
  cb : Covers [⟨State.addr blk, blockBytes w * n⟩] (s.rd ++ s.wr)
  cw : Covers [⟨State.addr st, bufOff w⟩, ⟨State.addr scr, 512⟩] s.wr
  st_sc : Region.Disjoint ⟨State.addr st, bufOff w⟩ ⟨State.addr scr, 512⟩
  b_st : Region.Disjoint ⟨State.addr blk, blockBytes w * n⟩ ⟨State.addr st, bufOff w⟩
  b_sc : Region.Disjoint ⟨State.addr blk, blockBytes w * n⟩ ⟨State.addr scr, 512⟩
  w_st : (below s).Disjoint ⟨State.addr st, bufOff w⟩
  w_b : (below s).Disjoint ⟨State.addr blk, blockBytes w * n⟩
  w_sc : (below s).Disjoint ⟨State.addr scr, 512⟩
  nst : st.toNat + bufOff w ≤ 2 ^ 32
  nb : blk.toNat + blockBytes w * n ≤ 2 ^ 32
  nsc : scr.toNat + 512 ≤ 2 ^ 32

/-- The four words the frame pushes. -/
abbrev args4 : List Reg := [.r3, .r11, .r12, .lr]

theorem e16 : BitVec.ofNat 32 (4 * args4.length) = 16 := rfl

/-- The regions the callee is given: the blocks and its stack arguments, the
state and the scratch space. -/
abbrev CallArgs.rd (w : Nat) (sp blk : BitVec 32) (n : Nat) : List Region :=
  [⟨State.addr blk, blockBytes w * n⟩, ⟨State.addr sp - 16, 16⟩]
abbrev CallArgs.wr (w : Nat) (st scr : BitVec 32) : List Region :=
  [⟨State.addr st, bufOff w⟩, ⟨State.addr scr, 512⟩]

variable {P : Params w}

namespace CallArgs
variable {s : State} {st scr blk : BitVec 32} {n : Nat} {t : BitVec 64} {last : BitVec 32}
  (h : CallArgs (w := w) s st scr blk n t last)
include h

theorem a0 : State.addr (s.sp - 16) = State.addr s.sp - 16 := addr_sub h.sp16
theorem a4 : State.addr (s.sp - 16 + 4) = State.addr s.sp - 16 + BitVec.ofNat 64 4 :=
  addr_sub_add h.sp16 (by decide)
theorem a8 : State.addr (s.sp - 16 + 4 + 4) = State.addr s.sp - 16 + BitVec.ofNat 64 8 := by
  rw [BitVec.add_assoc]; exact addr_sub_add (k := 16) (i := 8) h.sp16 (by decide)
theorem a12 : State.addr (s.sp - 16 + 4 + 4 + 4) = State.addr s.sp - 16 + BitVec.ofNat 64 12 := by
  rw [BitVec.add_assoc, BitVec.add_assoc]; exact addr_sub_add (k := 16) (i := 12) h.sp16 (by decide)

/-- The memory after the push. -/
theorem pmem : (pushed args4 s).mem =
    (((s.mem.writeW (State.addr s.sp - 16) (s.gpr .r3)).writeW (State.addr s.sp - 16 + BitVec.ofNat 64 4)
      (s.gpr .r11)).writeW (State.addr s.sp - 16 + BitVec.ofNat 64 8) last).writeW
      (State.addr s.sp - 16 + BitVec.ofNat 64 12) scr := by
  show storeWords s.mem (s.sp - BitVec.ofNat 32 (4 * args4.length))
    [s.gpr .r3, s.gpr .r11, s.gpr .r12, s.gpr .lr] = _
  rw [e16]
  show (((s.mem.writeW (State.addr (s.sp - 16)) _).writeW (State.addr (s.sp - 16 + 4)) _).writeW
    (State.addr (s.sp - 16 + 4 + 4)) _).writeW (State.addr (s.sp - 16 + 4 + 4 + 4)) _ = _
  rw [h.a0, h.a4, h.a8, h.a12, h.r12, h.lr]

omit h in
theorem psp : (pushed args4 s).sp = s.sp - 16 := by rw [pushed_sp, e16]

/-- The stack arguments, in a state whose stack pointer is that after the push. -/
theorem sa (T : State) (ht : T.sp = s.sp - 16) (i : Nat) (hi : i < 4) :
    stackArgAddr T i = State.addr s.sp - 16 + BitVec.ofNat 64 (4 * i) := by
  simp only [stackArgAddr, ht]
  exact addr_sub_add (k := 16) h.sp16 (by omega_nat)

theorem sa0 (T : State) (ht : T.sp = s.sp - 16) : stackArgAddr T 0 = State.addr s.sp - 16 := by
  rw [h.sa T ht 0 (by decide)]; exact BitVec.add_zero _

theorem arg0 (T : State) (ht : T.sp = s.sp - 16) (hm : T.mem = (pushed args4 s).mem) :
    stackArg T 0 = s.gpr .r3 := by
  rw [stackArg, h.sa T ht 0 (by decide), hm, h.pmem,
    Mem.readW_writeW_sep (sep_off _ (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_sep (sep_off _ (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_sep (sep_off _ (by decide) (by decide) (by decide)) (by decide),
    show 4 * 0 = 0 from rfl, BitVec.add_zero, Mem.readW_writeW_self32]

theorem arg1 (T : State) (ht : T.sp = s.sp - 16) (hm : T.mem = (pushed args4 s).mem) :
    stackArg T 1 = s.gpr .r11 := by
  rw [stackArg, h.sa T ht 1 (by decide), hm, h.pmem,
    Mem.readW_writeW_sep (sep_off _ (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_sep (sep_off _ (by decide) (by decide) (by decide)) (by decide),
    show 4 * 1 = 4 from rfl, Mem.readW_writeW_self32]

theorem arg2 (T : State) (ht : T.sp = s.sp - 16) (hm : T.mem = (pushed args4 s).mem) :
    stackArg T 2 = last := by
  rw [stackArg, h.sa T ht 2 (by decide), hm, h.pmem,
    Mem.readW_writeW_sep (sep_off _ (by decide) (by decide) (by decide)) (by decide),
    show 4 * 2 = 8 from rfl, Mem.readW_writeW_self32]

theorem arg3 (T : State) (ht : T.sp = s.sp - 16) (hm : T.mem = (pushed args4 s).mem) :
    stackArg T 3 = scr := by
  rw [stackArg, h.sa T ht 3 (by decide), hm, h.pmem, show 4 * 3 = 12 from rfl, Mem.readW_writeW_self32]

/-- The push writes only below the stack pointer. -/
theorem fP : Frame [below s] s.mem (pushed args4 s).mem := by
  rw [h.pmem]
  have hc : ∀ k, k + 4 ≤ 16 → (below s).Contains (State.addr s.sp - 16 + BitVec.ofNat 64 k) (32 / 8) := by
    intro k hk; exact contains_off _ (by omega_nat) (by decide)
  refine ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _
    ?_).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
  · simpa using hc 0 (by decide)
  · exact hc 4 (by decide)
  · exact hc 8 (by decide)
  · exact hc 12 (by decide)

omit h in
theorem vsp : ((pushed args4 s).callEntry.withRegions (rd w s.sp blk n) (wr w st scr)).sp = s.sp - 16 :=
  psp
omit h in
theorem vmem : ((pushed args4 s).callEntry.withRegions (rd w s.sp blk n) (wr w st scr)).mem =
    (pushed args4 s).mem := rfl

theorem hn' : (BitVec.ofNat 32 n).toNat = n := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h.hn

theorem pre : (compressArm P).pre ((pushed args4 s).callEntry.withRegions (rd w s.sp blk n) (wr w st scr)) := by
  simp only [compressArm, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, ce0, ce1, ce2,
    pushed_gpr, h.arg3 _ vsp vmem, h.sa0 _ vsp, h.r0, h.r1, h.r2, h.hn']
  refine ⟨trivial, trivial, h.st_sc, h.b_st, h.b_sc, h.w_st, h.w_sc, h.nst, h.nb, h.nsc, ?_⟩
  rw [vsp, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, Offset.toNat_sub_ofNat]
  have := h.sp16; have := s.sp.isLt; omega_nat

theorem cov : Covers (rd w s.sp blk n ++ wr w st scr) ((pushed args4 s).rd ++ (pushed args4 s).wr) := by
  intro x n' ⟨r, hr, hcn⟩
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rw [pushed_rd, pushed_wr, e16]
  rcases hr with (rfl | rfl) | (rfl | rfl)
  · obtain ⟨r', hr', hc'⟩ := h.cb x n' ⟨_, List.mem_singleton_self _, hcn⟩
    rcases List.mem_append.mp hr' with hr' | hr'
    · exact ⟨r', List.mem_append_left _ hr', hc'⟩
    · exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr'), hc'⟩
  · refine ⟨_, List.mem_append_right _ (List.mem_cons_self ..), ?_⟩
    rw [h.a0]; exact hcn
  all_goals
    obtain ⟨r', hr', hc'⟩ := h.cw x n' ⟨_, by simp, hcn⟩
    exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr'), hc'⟩

theorem covW : Covers (wr w st scr) (pushed args4 s).wr := by
  intro x n' hi
  obtain ⟨r', hr', hc'⟩ := h.cw x n' hi
  exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩

end CallArgs

/-- The `n ≤ 16` bytes a pop releases lie in `below s`. -/
theorem lost_sub {s : State} {n : Nat} (hn : n ≤ 16) (h16 : 16 ≤ s.sp.toNat) :
    Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 n), n⟩ (below s) := by
  intro a ha
  have := s.sp.isLt
  simp only [Region.Contains, State.addr] at ha ⊢
  bv_omega_arith

/-- After a frame of `rs` around a call that keeps the regions and the stack
pointer, whatever memory `m` that differs from the call's only in the
released frame, and whatever unknowns `u`, the pop leaves. -/
theorem after_frame {s s₂ : State} {rs : List Reg} {ws : List Region}
    (fP : Frame [below s] s.mem (pushed rs s).mem)
    (hrd : s₂.rd = (pushed rs s).rd) (hwr : s₂.wr = (pushed rs s).wr) (hsp : s₂.sp = (pushed rs s).sp)
    (hf : Frame ws (pushed rs s).mem s₂.mem)
    (hcs : ∀ r ∈ preserved, r ≠ .lr → s₂.gpr r = (pushed rs s).gpr r)
    (hn : 4 * rs.length ≤ 16) (h16 : 16 ≤ s.sp.toNat) {m : Mem} {u : Nat → BitVec 32}
    (hfl : Frame [⟨State.addr (s.sp - BitVec.ofNat 32 (4 * rs.length)), 4 * rs.length⟩] s₂.mem m) :
    After s ws { popped .r3 (4 * rs.length) s₂ with mem := m, unknowns := u } := by
  refine ⟨?_, ?_, ?_, fun r hr hl => ?_, ?_⟩
  · dsimp only; rw [popped_rd, hrd, pushed_rd]
  · dsimp only; rw [popped_wr, hwr, pushed_wr]; rfl
  · dsimp only; rw [popped_sp, hsp, pushed_sp]; exact BitVec.sub_add_cancel _ _
  · have hr3 : r ≠ .r3 := by rintro rfl; simp [preserved] at hr
    dsimp only; rw [popped_gpr hr3, hcs r hr hl, pushed_gpr]
  · dsimp only
    exact ((frame_app (ws' := ws) fP |>.mono fun r hr => by
        simp only [List.mem_append, List.mem_singleton] at hr ⊢; grind).trans (frame_app (ws' := [below s]) hf)).trans
      (hfl.sub fun r hr => ⟨below s, List.mem_append_right _ (List.mem_singleton_self _), by
        rw [List.mem_singleton.mp hr]; exact lost_sub hn h16⟩)

variable {P : Params w}

/-- A call of the compression function, in its frame: the hash value at `st`
is updated with the `n` blocks at `blk`, the first with the counter `t`, as
the last ones if `last ≠ 0`. -/
theorem call_ok {name : String} {code : Prog isa} (hf : CalleeOk P code) {s : State}
    {st scr blk : BitVec 32} {n : Nat} {t : BitVec 64} {last : BitVec 32}
    (h : CallArgs (w := w) s st scr blk n t last) {Q : State → Prop}
    (hQ : ∀ s', After s [⟨State.addr st, bufOff w⟩, ⟨State.addr scr, 512⟩] s' →
      stateAt w s'.mem (State.addr st) =
        compressBlocks P (stateAt w s.mem (State.addr st)) s.mem (State.addr blk) n t.toNat
          (last != 0) → Q s') :
    WP isa (call name code) s Q := by
  have h16 := h.sp16
  refine WP.frame (rs := args4) (r := .r3) rfl (by show 16 ≤ s.sp.toNat; exact h16) (by decide) ?_
  refine WP.call (k := compressArm P) hf.verified.1 h.pre h.cov h.covW ?_ hf.noCalls
  intro s₂ hrd hwr hsp hfr hcs _ hpost mL uL hfl
  simp only [compressArm, tArm, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, ce0, ce1,
    ce2, pushed_gpr, h.r0, h.r1, h.r2, h.hn', h.arg0 _ CallArgs.vsp CallArgs.vmem,
    h.arg1 _ CallArgs.vsp CallArgs.vmem, h.arg2 _ CallArgs.vsp CallArgs.vmem, h.t] at hpost
  refine hQ _ (after_frame h.fP hrd hwr hsp hfr hcs (by decide) h16 hfl) ?_
  have hstL : stateAt w mL (State.addr st) = stateAt w s₂.mem (State.addr st) :=
    stateAt_congr fun i hi => hfl.bytes (R := ⟨State.addr st, bufOff w⟩)
      (by simp only [List.mem_singleton]; rintro r rfl; exact h.w_st.symm.sub_right (lost_sub (by decide) h16))
      (by show bufOff w ≤ 2 ^ 64; have := h.nst; omega_nat) hi
  have hst : stateAt w (pushed args4 s).mem (State.addr st) = stateAt w s.mem (State.addr st) :=
    stateAt_congr fun i hi => h.fP.bytes (R := ⟨State.addr st, bufOff w⟩)
      (by simp only [List.mem_singleton]; rintro r rfl; exact h.w_st.symm)
      (by show bufOff w ≤ 2 ^ 64; have := h.nst; omega_nat) hi
  have hbl : compressBlocks P (stateAt w s.mem (State.addr st)) (pushed args4 s).mem (State.addr blk) n
      t.toNat (last != 0) =
      compressBlocks P (stateAt w s.mem (State.addr st)) s.mem (State.addr blk) n t.toNat
        (last != 0) :=
    compressBlocks_congr P fun j hj => h.fP.bytes (R := ⟨State.addr blk, blockBytes w * n⟩)
      (by simp only [List.mem_singleton]; rintro r rfl; exact h.w_b.symm)
      (by show blockBytes w * n ≤ 2 ^ 64; have := h.nb; omega_nat) hj
  dsimp only
  rw [hstL, hpost, hst, hbl]

end

end VG.Proof.Blake2.Arm.Stream

end

/-!
# Streaming BLAKE2 on ARMv7: common lemmas

The contracts the proofs of `init`, `update` and `finalize` are written
against (for any word size, as on AArch64:
`Proof/Blake2/AArch64/Stream/Common.lean`), weakest-precondition rules for the
instructions the MD streaming proofs do not cover, 64-bit counts in register
pairs, the number of buffered bytes, the loops copying bytes into the buffer
and zeroing it, and saving and restoring the caller's registers.
-/

namespace VG.Proof.Blake2

open VG.Arm VG.Spec.Blake2

/-- The 64-bit `count` argument of `update`/`finalize`, in `r2:r3` (AAPCS: the
low word in `r2`). -/
def countArm (s : State) : BitVec 64 := s.gpr .r3 ++ s.gpr .r2

section
variable {w : Nat} (P : Params w)

/-- ARMv7 contract for `init(state = r0, outlen = r1, key = r2, keylen =
r3)`. -/
def initArm : Contract isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), bufOff w + blockBytes w⟩
    let key : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
    s.rd = [key] ∧ s.wr = [state] ∧ key.Disjoint state ∧
    (s.gpr .r0).toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32 ∧
    (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
    1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ P.maxBytes ∧ (s.gpr .r3).toNat ≤ P.maxBytes
  post s s' := Spec.Blake2.Repr P (Spec.Blake2.init P (s.gpr .r1).toNat (s.gpr .r3).toNat) s'.mem
    (State.addr (s.gpr .r0)) (keyBlock w (bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat))
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3

/-- ARMv7 contract for `update(state = r0, count = r2:r3, data = [sp],
len = [sp, #4], scratch = [sp, #8])`, which pushes 16 bytes of stack. -/
def updateArm : Contract isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), bufOff w + blockBytes w⟩
    let data : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 2), 576⟩
    let args : Region := ⟨stackArgAddr s 0, 12⟩
    s.rd = [data, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧
    (Arm.Stream.below s).Disjoint state ∧ (Arm.Stream.below s).Disjoint data ∧
    (Arm.Stream.below s).Disjoint scratch ∧
    (s.gpr .r0).toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32 ∧
    (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32 ∧ (stackArg s 2).toNat + 576 ≤ 2 ^ 32 ∧
    16 ≤ s.sp.toNat ∧ s.sp.toNat + 12 ≤ 2 ^ 32
  post s s' := ∀ h0 d, Spec.Blake2.Repr P h0 s.mem (State.addr (s.gpr .r0)) d →
    countArm s = BitVec.ofNat 64 d.length → d.length + (stackArg s 1).toNat < 2 ^ 64 →
    Spec.Blake2.Repr P h0 s'.mem (State.addr (s.gpr .r0))
      (d ++ bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2

/-- ARMv7 contract for `finalize(state = r0, count = r2:r3, out = [sp],
scratch = [sp, #4])`, which pushes 16 bytes of stack. -/
def finalizeArm : Contract isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), bufOff w + blockBytes w⟩
    let out : Region := ⟨State.addr (stackArg s 0), bufOff w⟩
    let scratch : Region := ⟨State.addr (stackArg s 1), 576⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    (Arm.Stream.below s).Disjoint state ∧ (Arm.Stream.below s).Disjoint out ∧
    (Arm.Stream.below s).Disjoint scratch ∧
    (s.gpr .r0).toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + bufOff w ≤ 2 ^ 32 ∧
    (stackArg s 1).toNat + 576 ≤ 2 ^ 32 ∧ 16 ≤ s.sp.toNat ∧ s.sp.toNat + 8 ≤ 2 ^ 32
  post s s' := ∀ h0 d, Spec.Blake2.Repr P h0 s.mem (State.addr (s.gpr .r0)) d → d.length < 2 ^ 64 →
    countArm s = BitVec.ofNat 64 d.length →
    bytesAt s'.mem (State.addr (stackArg s 0)) (bufOff w) = finalHash P h0 d
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

end

namespace Arm.Stream

open VG.Impl.Blake2.Arm.Stream (N B lbb saved save restore)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd WP.cons op2_imm op2_reg op2_lsr op2_lsl wp_mov wp_add wp_sub
  wp_and wp_orr wp_subs wp_cmp wp_ldr wp_str wp_ldrb wp_strb wp_ldrSp ofNat_beq_zero sub_ofNat cmp0 eval_eq
  eval_ne)
open VG.WriteBytes (writeBytes writeBytes_snoc writeBytes_frame writeBytes_nil)

variable {w : Nat} {P : Params w}

/-! ## Sizes -/

/-- The word sizes, and keys fitting a block. -/
structure Ok (P : Params w) : Prop where
  /-- A key fits in a block. -/
  max : P.maxBytes ≤ blockBytes w
  w : w = 64 ∨ w = 32

theorem Ok.bb (h : Ok P) : blockBytes w = 64 ∨ blockBytes w = 128 := by
  rcases h.w with rfl | rfl <;> decide

theorem Ok.pos (h : Ok P) : 0 < blockBytes w := by rcases h.bb with h | h <;> omega_arith

/-- The sizes, all small. -/
theorem Ok.len (h : Ok P) : bufOff w + blockBytes w ≤ 192 ∧ bufOff w ≤ 64 ∧ 32 ≤ bufOff w ∧
    bufOff w % 4 = 0 ∧ 64 ≤ blockBytes w := by
  rcases h.w with rfl | rfl <;> decide

theorem Ok.lbb (h : Ok P) : 1 ≤ lbb w ∧ lbb w ≤ 31 ∧ 2 ^ lbb w = blockBytes w := by
  rcases h.w with rfl | rfl <;> decide

theorem N_eq : N w = bufOff w := rfl
theorem B_eq : B w = blockBytes w := rfl

theorem Ok.encB (h : Ok P) : encodable (BitVec.ofNat 32 (B w)) = true := by
  rcases h.w with rfl | rfl <;> decide
theorem Ok.encB1 (h : Ok P) : encodable (BitVec.ofNat 32 (B w - 1)) = true := by
  rcases h.w with rfl | rfl <;> decide
theorem Ok.encN (h : Ok P) : encodable (BitVec.ofNat 32 (N w)) = true := by
  rcases h.w with rfl | rfl <;> decide

/-! ## Instructions the MD streaming proofs do not cover -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem Upd.adds (s : State) (d : Reg) (x y v : BitVec 32) : Upd s ((addFlags s x y).setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, addFlags, h], rfl, rfl, rfl, rfl⟩

theorem wp_adds {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n + y) → s'.c = decide (2 ^ 32 ≤ (s.gpr n).toNat + y.toNat) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.adds d n o :: is)) s Q :=
  WP.cons (s' := (addFlags s (s.gpr n) y).setReg d (s.gpr n + y)) (by simp [exec, ho])
    (k _ (Upd.adds _ _ _ _ _) rfl)

theorem wp_adc {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n + y + (if s.c then 1 else 0)) → s'.c = s.c → WP isa (.block is) s' Q) :
    WP isa (.block (.adc d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n + y + (if s.c then 1 else 0))) (by simp [exec, ho])
    (k _ (MdStream.Arm.Upd.setReg _ _ _) rfl)

theorem wp_eor {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ y) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .eor d n o :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n ^^^ y)) (by simp [exec, ho]) (k _ (MdStream.Arm.Upd.setReg _ _ _))

theorem wp_movw {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm.setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movw d imm :: is)) s Q :=
  WP.cons (s' := s.setReg d (imm.setWidth 32)) rfl (k _ (MdStream.Arm.Upd.setReg _ _ _))

theorem wp_movt {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movt d imm :: is)) s Q :=
  WP.cons (s' := s.setReg d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32)) rfl
    (k _ (MdStream.Arm.Upd.setReg _ _ _))

end

/-! ## 64-bit counts in register pairs -/

theorem toNat_append32 (hi lo : BitVec 32) : (hi ++ lo : BitVec 64).toNat = hi.toNat * 2 ^ 32 + lo.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt, Nat.shiftLeft_eq]

/-- `adds lo, lo, y` then `adc hi, hi, #0` adds `y` to `hi:lo`. -/
theorem add64 (lo hi y : BitVec 32) :
    ((hi + 0 + (if decide (2 ^ 32 ≤ lo.toNat + y.toNat) = true then 1 else 0)) ++ (lo + y) : BitVec 64) =
      (hi ++ lo) + y.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  have hl := lo.isLt; have hh := hi.isLt; have hy := y.isLt
  rw [show hi + 0 = hi from BitVec.add_zero _]
  have e1 : (1 : BitVec 32).toNat = 1 := rfl
  have e0 : (0 : BitVec 32).toNat = 0 := rfl
  by_cases hc : 2 ^ 32 ≤ lo.toNat + y.toNat
  · simp only [hc, decide_true, ite_true, toNat_append32, BitVec.toNat_add, BitVec.toNat_setWidth, e1]
    omega_arith
  · simp only [hc, decide_false, Bool.false_eq_true, ite_false, toNat_append32, BitVec.toNat_add,
      BitVec.toNat_setWidth, e0]
    omega_arith

/-- Adding `y < 2³²` to a count `x` (modulo 2⁶⁴) in a register pair. -/
theorem add64_ofNat {lo hi : BitVec 32} {x y : Nat} (h : (hi ++ lo : BitVec 64) = BitVec.ofNat 64 x)
    (hy : y < 2 ^ 32) :
    ((hi + 0 + (if decide (2 ^ 32 ≤ lo.toNat + (BitVec.ofNat 32 y).toNat) = true then 1 else 0)) ++
      (lo + BitVec.ofNat 32 y) : BitVec 64) = BitVec.ofNat 64 (x + y) := by
  rw [add64, h, BitVec.ofNat_add]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_arith

/-- The low word of a count in a register pair. -/
theorem lo_of_pair {lo hi : BitVec 32} {x : Nat} (h : (hi ++ lo : BitVec 64) = BitVec.ofNat 64 x) :
    lo = BitVec.ofNat 32 x := by
  apply BitVec.eq_of_toNat_eq
  have e := congrArg BitVec.toNat h
  rw [toNat_append32, BitVec.toNat_ofNat] at e
  rw [BitVec.toNat_ofNat]
  have := lo.isLt; have := hi.isLt
  omega_arith

/-- A count in a register pair is zero iff the OR of its words is. -/
theorem or_beq_zero {lo hi : BitVec 32} {x : Nat} (h : (hi ++ lo : BitVec 64) = BitVec.ofNat 64 x)
    (hx : x < 2 ^ 64) : ((lo ||| hi) - 0 == 0) = decide (x = 0) := by
  have e := congrArg BitVec.toNat h
  rw [toNat_append32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at e
  rw [show (lo ||| hi) - 0 = lo ||| hi from BitVec.sub_zero _]
  by_cases hx0 : x = 0
  · have h1 : lo = 0 := BitVec.eq_of_toNat_eq (by show lo.toNat = 0; omega_arith)
    have h2 : hi = 0 := BitVec.eq_of_toNat_eq (by show hi.toNat = 0; omega_arith)
    simp [h1, h2, hx0]
  · rw [decide_eq_false hx0, beq_eq_false_iff_ne]
    intro h0
    obtain ⟨h1, h2⟩ := BitVec.or_eq_zero_iff.mp h0
    rw [h1, h2] at e
    rw [BitVec.toNat_zero] at e
    omega_arith

/-! ## The number of bytes in the buffer -/

/-- `x & (B - 1)`: the remainder modulo the block size. -/
theorem mask_mod (hP : Ok P) (x : BitVec 32) :
    x &&& BitVec.ofNat 32 (B w - 1) = BitVec.ofNat 32 (x.toNat % blockBytes w) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  rcases hP.w with rfl | rfl
  · rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (B 64 - 1) % 2 ^ 32 = 2 ^ 7 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, show blockBytes 64 = 2 ^ 7 from rfl]
    omega_arith
  · rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (B 32 - 1) % 2 ^ 32 = 2 ^ 6 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, show blockBytes 32 = 2 ^ 6 from rfl]
    omega_arith

/-- `x >>> lbb`: division by the block size. -/
theorem shr_ofNat (hP : Ok P) {m : Nat} (h : m < 2 ^ 32) :
    BitVec.ofNat 32 m >>> lbb w = BitVec.ofNat 32 (m / blockBytes w) := by
  rw [MdStream.Arm.ofNat_shr h, hP.lbb.2.2]

/-- `((count - 1) mod B) + 1`, from the low word of the count. -/
theorem bufLen_lo (hP : Ok P) {x : Nat} (hx : x ≠ 0) :
    ((BitVec.ofNat 32 x - 1) &&& BitVec.ofNat 32 (B w - 1)) + 1 = BitVec.ofNat 32 (bufLen w x) := by
  have hd : blockBytes w ∣ 2 ^ 32 := by rcases hP.w with rfl | rfl <;> decide
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega_arith), mask_mod hP,
    BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ hd, ← BitVec.ofNat_add]
  simp only [bufLen, hx, ite_false]

/-- A pointer plus an offset that does not wrap. -/
theorem toNat_add_ofNat {p : BitVec 32} {k : Nat} (h : p.toNat + k < 2 ^ 32) :
    (p + BitVec.ofNat 32 k).toNat = p.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega_arith), Nat.mod_eq_of_lt h]

/-! ## Copying bytes into the buffer -/

/-- The copy loop's state after `j` of `k` bytes, from `s₀`: the bytes go from
`src` to `dst`. -/
structure CopyI (s₀ : State) (dst : Addr) (src : BitVec 32) (r k j : Nat) (s : State) : Prop where
  j_le : j ≤ k
  r6 : s.gpr .r6 = src + BitVec.ofNat 32 j
  r8 : s.gpr .r8 = BitVec.ofNat 32 (r + j)
  r11 : s.gpr .r11 = BitVec.ofNat 32 (k - j)
  other : ∀ x, x ≠ .r12 → x ≠ .r1 → x ≠ .r6 → x ≠ .r8 → x ≠ .r11 → s.gpr x = s₀.gpr x
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = writeBytes s₀.mem dst ((bytesAt s₀.mem (State.addr src) k).take j)

theorem setWidth_byte (b : BitVec 8) : (b.setWidth 32).setWidth 8 = b := by
  ext i hi; simp

theorem ne_iff (s : State) {k : Nat} (h : s.z = (BitVec.ofNat 32 k == 0)) (hk : k < 2 ^ 32) :
    isa.eval .ne s = some (decide (k ≠ 0)) := by
  show VG.Arm.eval .ne s = _
  rw [eval_ne, h, ofNat_beq_zero hk]
  simp

theorem contains_prefix (q : Addr) {j k : Nat} (h : j ≤ k) : (⟨q, k⟩ : Region).Contains q j := by
  simp [Region.Contains, h]

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by simp [bytesAt]

/-- The loop copying `k ≥ 1` bytes from `src` (at `r6`) to the buffer of the
state at `st` (in `r4`), from byte `r` on (in `r8`). -/
theorem copyLoop_ok {s₀ : State} {st src : BitVec 32} {r k : Nat} (hN : bufOff w ≤ 64) (hk : 1 ≤ k)
    (hfit : st.toNat + bufOff w + r + k ≤ 2 ^ 32) (hsfit : src.toNat + k ≤ 2 ^ 32)
    (hr4 : s₀.gpr .r4 = st) (hr6 : s₀.gpr .r6 = src) (hr8 : s₀.gpr .r8 = BitVec.ofNat 32 r)
    (hr11 : s₀.gpr .r11 = BitVec.ofNat 32 k)
    (hsrc : ∀ i < k, InRegions (s₀.rd ++ s₀.wr) (State.addr src + BitVec.ofNat 64 i) 1)
    (hdst : ∀ i < k, InRegions s₀.wr (State.addr st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 i) 1)
    (hd : Region.Disjoint ⟨State.addr src, k⟩ ⟨State.addr st + BitVec.ofNat 64 (bufOff w + r), k⟩)
    {Q : State → Prop}
    (hQ : ∀ s, CopyI s₀ (State.addr st + BitVec.ofNat 64 (bufOff w + r)) src r k k s → Q s) :
    WP isa (Impl.Blake2.Arm.Stream.copyLoop (w := w)) s₀ Q := by
  refine WP.loop (M := isa) (fun n (s : State) => ∃ j, n = k - j ∧ j < k ∧
      CopyI s₀ (State.addr st + BitVec.ofNat 64 (bufOff w + r)) src r k j s) ?_ k s₀
    ⟨0, by omega_arith, by omega_arith, by omega_arith, by simp [hr6], by rw [hr8, Nat.add_zero], by rw [hr11, Nat.sub_zero],
      fun _ _ _ _ _ _ => rfl, rfl, rfl, rfl, by rw [List.take_zero, writeBytes_nil]⟩
  rintro n s ⟨j, rfl, hj, h⟩
  -- The byte read.
  have hin : InRegions (s.rd ++ s.wr) (State.addr src + BitVec.ofNat 64 j) 1 := by
    rw [h.rd, h.wr]; exact hsrc j hj
  have hbyte : s.mem (State.addr src + BitVec.ofNat 64 j) = s₀.mem (State.addr src + BitVec.ofNat 64 j) := by
    rw [h.mem]
    exact (writeBytes_frame s₀.mem _ _ (contains_prefix (k := k) _ (by simp; omega_arith))).bytes
      (R := ⟨State.addr src, k⟩) (by simpa using hd) (by show k ≤ 2 ^ 64; omega_arith) hj
  -- The byte written.
  have hout : InRegions s.wr (State.addr st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 j) 1 := by
    rw [h.wr]; exact hdst j hj
  have hr4' : s.gpr .r4 = st := by
    rw [h.other .r4 (by decide) (by decide) (by decide) (by decide) (by decide), hr4]
  refine wp_ldrb (a := State.addr src + BitVec.ofNat 64 j) (by decide)
    (by rw [h.r6, BitVec.add_zero, addr_add (by omega_arith)]) hin fun s₁ u₁ => ?_
  refine wp_add (op2_reg _ _) fun s₂ u₂ =>
    wp_strb (a := State.addr st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 j)
    (by simp only [N_eq]; omega_arith) ?_ (by rw [u₂.wr, u₁.wr]; exact hout) fun s₃ g₃ => ?_
  · rw [u₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), hr4', h.r8, N_eq, BitVec.add_assoc,
      ← BitVec.ofNat_add, addr_add (by omega_arith), Offset.add_add]
    congr 2; omega_arith
  refine wp_add (op2_imm (by decide)) fun s₄ u₄ => wp_add (op2_imm (by decide)) fun s₅ u₅ =>
    wp_subs (op2_imm (by decide)) fun s₆ u₆ z₆ => WP.block_nil ?_
  have hr11' : s₆.gpr .r11 = BitVec.ofNat 32 (k - (j + 1)) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.r11, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega_arith),
      Nat.sub_sub]
  have hI : CopyI s₀ (State.addr st + BitVec.ofNat 64 (bufOff w + r)) src r k (j + 1) s₆ := by
    refine ⟨by omega_arith, ?_, ?_, hr11', fun x h1 h2 h3 h4 h5 => ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃.gpr, u₂.other _ (by decide),
        u₁.other _ (by decide), h.r6, BitVec.add_assoc, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
        ← BitVec.ofNat_add]
    · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
        u₁.other _ (by decide), h.r8, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add,
        Nat.add_assoc]
    · rw [u₆.other x h5, u₅.other x h4, u₄.other x h3, g₃.gpr, u₂.other x h2, u₁.other x h1,
        h.other x h1 h2 h3 h4 h5]
    · rw [u₆.rd, u₅.rd, u₄.rd, g₃.rd, u₂.rd, u₁.rd, h.rd]
    · rw [u₆.wr, u₅.wr, u₄.wr, g₃.wr, u₂.wr, u₁.wr, h.wr]
    · rw [u₆.sp, u₅.sp, u₄.sp, g₃.sp, u₂.sp, u₁.sp, h.sp]
    · have hj' : j < (bytesAt s₀.mem (State.addr src) k).length := by rw [bytesAt_length]; omega_arith
      have hl : (List.take j (bytesAt s₀.mem (State.addr src) k)).length = j := by
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
      rw [u₆.mem, u₅.mem, u₄.mem, g₃.mem, u₂.mem, u₁.mem, u₂.other _ (by decide), u₁.gpr, hbyte, h.mem,
        List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some,
        writeBytes_snoc _ _ _ _ (by rw [hl]; omega_arith), hl, setWidth_byte]
      congr 1
      simp [bytesAt]
  have hz : isa.eval .ne s₆ = some (decide (k - (j + 1) ≠ 0)) :=
    ne_iff s₆ (by rw [z₆, ← u₆.gpr, hr11']) (by omega_arith)
  by_cases hjk : j + 1 = k
  · exact .inl ⟨by rw [hz]; simp; omega_arith, hQ _ (hjk ▸ hI)⟩
  · exact .inr ⟨by rw [hz]; simp; omega_arith, k - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, hI⟩

/-! ## Zeroing the buffer -/

/-- The zeroing loop's state after `j` of `k` bytes, from `s₀`. -/
structure ZI (s₀ : State) (q : Addr) (r k j : Nat) (s : State) : Prop where
  j_le : j ≤ k
  r8 : s.gpr .r8 = BitVec.ofNat 32 (r + j)
  r11 : s.gpr .r11 = BitVec.ofNat 32 (k - j)
  other : ∀ x, x ≠ .r1 → x ≠ .r8 → x ≠ .r11 → s.gpr x = s₀.gpr x
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = writeBytes s₀.mem q (List.replicate j 0)

/-- The loop zeroing `k ≥ 1` bytes of the buffer of the state at `st` (in
`r4`), from byte `r` on (in `r8`), with `r12 = 0`. -/
theorem zeroLoop_ok {s₀ : State} {st : BitVec 32} {r k : Nat} (hN : bufOff w ≤ 64) (hk : 1 ≤ k)
    (hfit : st.toNat + bufOff w + r + k ≤ 2 ^ 32)
    (hr4 : s₀.gpr .r4 = st) (hr8 : s₀.gpr .r8 = BitVec.ofNat 32 r) (hr11 : s₀.gpr .r11 = BitVec.ofNat 32 k)
    (hr12 : s₀.gpr .r12 = 0)
    (hdst : ∀ i < k, InRegions s₀.wr (State.addr st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 i) 1)
    {Q : State → Prop}
    (hQ : ∀ s, ZI s₀ (State.addr st + BitVec.ofNat 64 (bufOff w + r)) r k k s → Q s) :
    WP isa (Impl.Blake2.Arm.Stream.zeroLoop (w := w)) s₀ Q := by
  refine WP.loop (M := isa) (fun n (s : State) => ∃ j, n = k - j ∧ j < k ∧
      ZI s₀ (State.addr st + BitVec.ofNat 64 (bufOff w + r)) r k j s) ?_ k s₀
    ⟨0, by omega_arith, by omega_arith, by omega_arith, by rw [hr8, Nat.add_zero], by rw [hr11, Nat.sub_zero],
      fun _ _ _ _ => rfl, rfl, rfl, rfl, by rw [List.replicate_zero, writeBytes_nil]⟩
  rintro n s ⟨j, rfl, hj, h⟩
  have hr4' : s.gpr .r4 = st := by rw [h.other .r4 (by decide) (by decide) (by decide), hr4]
  refine wp_add (op2_reg _ _) fun s₁ u₁ =>
    wp_strb (a := State.addr st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 j)
    (by simp only [N_eq]; omega_arith) ?_ (by rw [u₁.wr, h.wr]; exact hdst j hj) fun s₂ g₂ => ?_
  · rw [u₁.gpr, hr4', h.r8, N_eq, BitVec.add_assoc, ← BitVec.ofNat_add, addr_add (by omega_arith), Offset.add_add]
    congr 2; omega_arith
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_subs (op2_imm (by decide)) fun s₄ u₄ z₄ =>
    WP.block_nil ?_
  have hr11' : s₄.gpr .r11 = BitVec.ofNat 32 (k - (j + 1)) := by
    rw [u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.r11,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega_arith), Nat.sub_sub]
  have hI : ZI s₀ (State.addr st + BitVec.ofNat 64 (bufOff w + r)) r k (j + 1) s₄ := by
    refine ⟨by omega_arith, ?_, hr11', fun x h1 h2 h3 => ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.r8,
        show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add, Nat.add_assoc]
    · rw [u₄.other x h3, u₃.other x h2, g₂.gpr, u₁.other x h1, h.other x h1 h2 h3]
    · rw [u₄.rd, u₃.rd, g₂.rd, u₁.rd, h.rd]
    · rw [u₄.wr, u₃.wr, g₂.wr, u₁.wr, h.wr]
    · rw [u₄.sp, u₃.sp, g₂.sp, u₁.sp, h.sp]
    · rw [u₄.mem, u₃.mem, g₂.mem, u₁.mem, u₁.other _ (by decide),
        h.other .r12 (by decide) (by decide) (by decide), hr12, h.mem,
        List.replicate_succ', writeBytes_snoc _ _ _ _ (by simp; omega_arith), List.length_replicate]
      rfl
  have hz : isa.eval .ne s₄ = some (decide (k - (j + 1) ≠ 0)) :=
    ne_iff s₄ (by rw [z₄, ← u₄.gpr, hr11']) (by omega_arith)
  by_cases hjk : j + 1 = k
  · exact .inl ⟨by rw [hz]; simp; omega_arith, hQ _ (hjk ▸ hI)⟩
  · exact .inr ⟨by rw [hz]; simp; omega_arith, k - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, hI⟩

/-! ## Saving and restoring the caller's registers -/

/-- The caller's registers `g` are saved in the scratch space at `b`. -/
abbrev Saved (b : Addr) (g : Reg → BitVec 32) (m : Mem) : Prop := Spill.Saved m b g saved

theorem saved_slots : Spill.Slots 512 548 saved := by decide

theorem saved_bound : ∀ p ∈ saved, 512 ≤ p.2 ∧ p.2 + 4 ≤ 548 := by decide

theorem saveMem_saved (m : Mem) (b : Addr) (g : Reg → BitVec 32) :
    Saved b g (MdStream.Arm.saveMem m b g saved) :=
  Spill.saveMem_saved b g m saved saved_slots

theorem saveMem_frame (m : Mem) (b : Addr) (g : Reg → BitVec 32) :
    Frame [⟨b, 576⟩] m (MdStream.Arm.saveMem m b g saved) :=
  Spill.saveMem_frame m b g (by decide) saved (by decide)

/-- Saving `r4`–`r11` and `lr` with the scratch pointer in `b`. -/
theorem save_ok {b : Reg} {rest : List Instr} {s : State} {Q : State → Prop}
    (hfit : (s.gpr b).toNat + 576 ≤ 2 ^ 32)
    (hin : ∀ d, 512 ≤ d → d + 4 ≤ 548 → InRegions s.wr (State.addr (s.gpr b) + BitVec.ofNat 64 d) 4)
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = MdStream.Arm.saveMem s.mem (State.addr (s.gpr b)) s.gpr saved → WP isa (.block rest) s' Q) :
    WP isa (.block (save b ++ rest)) s Q :=
  Spill.save_slots_ok saved_slots (by omega_arith) hin (k _ rfl rfl rfl rfl rfl)

/-- Restoring `r4`–`r11` and `lr` from the save area at `scratch` (in `r5`). -/
theorem restore_ok {s : State} {scr : BitVec 32} (h5 : s.gpr .r5 = scr) (hfit : scr.toNat + 576 ≤ 2 ^ 32)
    (hin : ∀ d, 512 ≤ d → d + 4 ≤ 548 → InRegions (s.rd ++ s.wr) (State.addr scr + BitVec.ofNat 64 d) 4)
    (g : Reg → BitVec 32) (hsv : Saved (State.addr scr) g s.mem) {Q : State → Prop}
    (k : ∀ s', (∀ p ∈ saved, s'.gpr p.1 = g p.1) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → Q s') :
    WP isa (.block restore) s Q := by
  unfold restore
  rw [← List.append_nil (saved.map _)]
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => ?_
  have h3 : s₁.gpr .r3 = scr := by rw [u₁.gpr, h5]
  refine Spill.restore_slots_ok saved_slots (by decide) (g := g) (by rw [h3]; omega_arith)
    (fun d h₁ h₂ => by rw [h3, u₁.rd, u₁.wr]; exact hin d h₁ h₂) (by rw [h3, u₁.mem]; exact hsv)
    fun s' ho _ hm hrd hwr hsp => WP.block_nil (k s' ho (hm.trans u₁.mem) (hrd.trans u₁.rd)
      (hwr.trans u₁.wr) (hsp.trans u₁.sp))

/-- The callee-saved registers are the caller's again once `restore` has run. -/
theorem preserved_of {s₀ s' : State} (hsv : ∀ p ∈ saved, s'.gpr p.1 = s₀.gpr p.1) :
    ∀ r ∈ preserved, s'.gpr r = s₀.gpr r :=
  Spill.restored_of hsv (by decide)

/-! ## The streaming state -/

/-- `Repr` depends only on the bytes of the streaming state. -/
theorem repr_congr (hP : Ok P) {h0 : HashValue w} {mem mem' : Mem} {p : Addr} {d : List Byte}
    (hm : ∀ i < bufOff w + blockBytes w, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i))
    (h : Spec.Blake2.Repr P h0 mem p d) : Spec.Blake2.Repr P h0 mem' p d := by
  rw [repr_iff P hP.pos] at h ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, by rw [← h4]; exact stateAt_congr fun i hi => hm i (by omega_arith), ?_⟩
  rw [← h5]
  refine bytesAt_congr fun i hi => ?_
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact hm _ (by omega_arith)

/-- `ReprR` depends only on the bytes of the streaming state. -/
theorem reprR_congr {h0 : HashValue w} {mem mem' : Mem} {p : Addr} {d : List Byte} {r : Nat}
    (hs : stateAt w mem' p = stateAt w mem p)
    (hb : ∀ i < r, mem' (p + BitVec.ofNat 64 (bufOff w) + BitVec.ofNat 64 i) =
      mem (p + BitVec.ofNat 64 (bufOff w) + BitVec.ofNat 64 i))
    (h : ReprR P h0 mem p d r) : ReprR P h0 mem' p d r := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, by rw [hs, h4], by rw [← h5]; exact bytesAt_congr hb⟩

/-- Bytes `[0, r)` from `p` stay, and the bytes `xs` follow them. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (r : Nat) (xs : List Byte) (h : r + xs.length < 2 ^ 64) :
    bytesAt (writeBytes m (p + BitVec.ofNat 64 r) xs) p (r + xs.length) = bytesAt m p r ++ xs := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro i hi
    have hi := List.mem_range.mp hi
    exact WriteBytes.writeBytes_before m p xs hi (by omega_arith)
  · apply List.ext_getElem (by simp)
    intro j h₁ h₂
    simp only [List.getElem_map, List.getElem_range, Function.comp, writeBytes]
    have hj : j < xs.length := by simpa using h₁
    rw [show p + BitVec.ofNat 64 (r + j) - (p + BitVec.ofNat 64 r) = BitVec.ofNat 64 j from
      Offset.add_ofNat_add_sub p r j, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]
    simp [hj, List.getD_eq_getElem?_getD]

end Arm.Stream

end VG.Proof.Blake2

end

end

/-!
# Streaming BLAKE2 on ARMv7: `update`

The functional correctness of `update`, for either word size and any correct
compression function (`CalleeOk`), piece by piece: the prologue, up to the
first call (`pro_ok`), the first call (`call₁_ok`), the code between the calls
(`mid_ok`), the second call (`call₂_ok`) and the end (`end_ok`). Each piece's
postcondition gives the registers the next one starts from as functions of the
arguments, which the constant-time proof (`CT.lean`) uses too.
-/

@[expose] public section

namespace VG.Proof.Blake2.Arm.Stream.Update

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Blake2.Arm.Stream (N B lbb saved save restore call copyLoop copy fill args updatePro
  updateMid updateEnd update)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsr wp_mov wp_add wp_sub wp_and wp_orr
  wp_subs wp_cmp wp_ldrSp ofNat_beq_zero sub_ofNat cmp0 eval_eq eval_ne)
open VG.WriteBytes (writeBytes writeBytes_before writeBytes_frame)
open VG.Proof.Blake2 (ReprR bufLen bufLen_le bufLen_le_self bufLen_pos repr_iff reprR_append reprR_flush
  reprR_blocks repr_of_reprR stateAt_congr bytesAt_congr bytesAt_add updateArm countArm compressBlocks_zero)

variable {w : Nat} {P : Params w}

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : BitVec 32 := s₀.gpr .r0
abbrev stA : Addr := State.addr (st s₀)
abbrev dp : BitVec 32 := stackArg s₀ 0
abbrev dA : Addr := State.addr (dp s₀)
abbrev len : Nat := (stackArg s₀ 1).toNat
abbrev scr : BitVec 32 := stackArg s₀ 2
abbrev scA : Addr := State.addr (scr s₀)
abbrev cnt : Nat := (countArm s₀).toNat
abbrev stR (w : Nat) : Region := ⟨stA s₀, bufOff w + blockBytes w⟩
abbrev dR : Region := ⟨dA s₀, len s₀⟩
abbrev scR : Region := ⟨scA s₀, 576⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 12⟩
/-- The first `c` bytes of data. -/
abbrev D (c : Nat) : List Byte := bytesAt s₀.mem (dA s₀) c

end

structure Pre (w : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀, argR s₀]
  wr : s₀.wr = [stR s₀ w, scR s₀]
  st_scr : (stR s₀ w).Disjoint (scR s₀)
  d_st : (dR s₀).Disjoint (stR s₀ w)
  d_scr : (dR s₀).Disjoint (scR s₀)
  a_st : (argR s₀).Disjoint (stR s₀ w)
  a_scr : (argR s₀).Disjoint (scR s₀)
  w_st : (below s₀).Disjoint (stR s₀ w)
  w_d : (below s₀).Disjoint (dR s₀)
  w_scr : (below s₀).Disjoint (scR s₀)
  st_fit : (st s₀).toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32
  d_fit : (dp s₀).toNat + len s₀ ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + 576 ≤ 2 ^ 32
  sp16 : 16 ≤ s₀.sp.toNat
  sp_fit : s₀.sp.toNat + 12 ≤ 2 ^ 32

theorem pre_of {s₀ : State} (h : (updateArm P).pre s₀) : Pre w s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

theorem len_lt (s₀ : State) : len s₀ < 2 ^ 32 := (stackArg s₀ 1).isLt
theorem cnt_lt (s₀ : State) : cnt s₀ < 2 ^ 64 := (countArm s₀).isLt

/-- The data the initial state represents, from `h0`. -/
def R₀ (P : Params w) (s₀ : State) (h0 : HashValue w) (d : List Byte) : Prop :=
  Spec.Blake2.Repr P h0 s₀.mem (stA s₀) d ∧ countArm s₀ = BitVec.ofNat 64 d.length ∧
    d.length + len s₀ < 2 ^ 64

theorem R₀.cnt_eq {s₀ : State} {h0 : HashValue w} {d : List Byte} (h : R₀ P s₀ h0 d) :
    cnt s₀ = d.length := by
  rw [cnt, h.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.2.2; omega_using [this])]

theorem R₀.length {s₀ : State} {h0 : HashValue w} {d : List Byte} (h : R₀ P s₀ h0 d) (c : Nat) :
    (d ++ D s₀ c).length = cnt s₀ + c := by
  rw [List.length_append, Arm.Stream.bytesAt_length, h.cnt_eq]

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (w : Nat) (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r4 : s.gpr .r4 = st s₀
  r5 : s.gpr .r5 = scr s₀
  r6 : s.gpr .r6 = dp s₀ + BitVec.ofNat 32 c
  r7 : s.gpr .r7 = BitVec.ofNat 32 (len s₀ - c)
  cn : s.gpr .r10 ++ s.gpr .r9 = BitVec.ofNat 64 (cnt s₀ + c)
  frame : Frame [stR s₀ w, scR s₀, below s₀] s₀.mem s.mem
  saved : Saved (scA s₀) s₀.gpr s.mem

/-- The state represents the data followed by the first `c` bytes of data,
the last `r` of them in the buffer. -/
structure Inv (P : Params w) (s₀ : State) (c r : Nat) (s : State) : Prop extends Common w s₀ c s where
  r8 : s.gpr .r8 = BitVec.ofNat 32 r
  repr : ∀ h0 d, R₀ P s₀ h0 d → ReprR P h0 s.mem (stA s₀) (d ++ D s₀ c) r

/-- The registers `Common` is about. -/
abbrev commonRegs : List Reg := [.r4, .r5, .r6, .r7, .r9, .r10]

theorem notC {r : Reg} (hr : r ∈ commonRegs) (x : Reg) (hx : x ∉ commonRegs := by decide) : r ≠ x :=
  fun h => hx (h ▸ hr)

theorem Common.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Common w s₀ c s)
    (hg : ∀ r ∈ commonRegs, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Common w s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  sp := hsp.trans h.sp
  r4 := by rw [hg _ (by simp)]; exact h.r4
  r5 := by rw [hg _ (by simp)]; exact h.r5
  r6 := by rw [hg _ (by simp)]; exact h.r6
  r7 := by rw [hg _ (by simp)]; exact h.r7
  cn := by rw [hg .r9 (by simp), hg .r10 (by simp)]; exact h.cn
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

theorem Inv.of_gpr {s₀ : State} {c r : Nat} {s s' : State} (h : Inv P s₀ c r s)
    (hg : ∀ r ∈ .r8 :: commonRegs, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    Inv P s₀ c r s' :=
  { h.toCommon.of_gpr (fun r hr => hg r (List.mem_cons_of_mem _ hr)) hm hrd hwr hsp with
    r8 := by rw [hg _ (by simp)]; exact h.r8
    repr := by rw [hm]; exact h.repr }

/-- `Inv` after an instruction writing a register it is not about. -/
theorem Inv.of_upd {s₀ : State} {c r : Nat} {s s' : State} (h : Inv P s₀ c r s) {d : Reg} {v : BitVec 32}
    (u : Upd s s' d v) (hd : d ∉ .r8 :: commonRegs := by decide) : Inv P s₀ c r s' :=
  h.of_gpr (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem u.rd u.wr u.sp

theorem Inv.of_flags {s₀ : State} {c r : Nat} {s s' : State} (h : Inv P s₀ c r s) (u : Fupd s s') :
    Inv P s₀ c r s' :=
  h.of_gpr (fun r _ => by rw [u.gpr]) u.mem u.rd u.wr u.sp

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : Pre w s₀) {c : Nat} {s : State} (h : Common w s₀ c s) {i : Nat}
    (hi : i < len s₀) : s.mem (dA s₀ + BitVec.ofNat 64 i) = s₀.mem (dA s₀ + BitVec.ofNat 64 i) :=
  h.frame.bytes (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr, hp.w_d.symm⟩)
    (by show len s₀ ≤ 2 ^ 64; have := len_lt s₀; omega_using [this]) hi

/-- Writes to the state, the compression function's scratch space and the
16 bytes below the stack pointer keep the saved registers. -/
theorem saved_frame {s₀ : State} (hp : Pre w s₀) {m m' : Mem} (h : Saved (scA s₀) s₀.gpr m)
    (hf : Frame [stR s₀ w, ⟨scA s₀, 512⟩, below s₀] m m') : Saved (scA s₀) s₀.gpr m' := by
  have := hp.scr_fit
  refine h.frame saved_slots hf fun r' hr' => ?_
  obtain e : Region.Sub ⟨scA s₀ + BitVec.ofNat 64 512, 548 - 512⟩ (scR s₀) := Offset.sub_base _ (by omega_using [])
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl
  · exact hp.st_scr.symm.sub_left e
  · exact Offset.disjoint_base _ (by omega_using []) (by omega_using [])
  · exact hp.w_scr.symm.sub_left e

/-! ## The prologue -/

/-- The prologue, but for `bufLen` and what follows it. -/
abbrev prologue : List Instr :=
  [.ldrSp .r12 8] ++ save .r12 ++ [.mov .r4 (.reg .r0), .mov .r5 (.reg .r12), .ldrSp .r6 0, .ldrSp .r7 4,
    .mov .r9 (.reg .r2), .mov .r10 (.reg .r3)]

/-- The stack arguments, word by word. -/
theorem argAddr_eq {s₀ : State} (hp : Pre w s₀) {k : Nat} (hk : k < 3) :
    stackArgAddr s₀ k = stackArgAddr s₀ 0 + BitVec.ofNat 64 (4 * k) := by
  have := hp.sp_fit
  simp only [stackArgAddr]
  rw [addr_add (by omega_using [hk, this])]
  simp

theorem arg_in {s₀ : State} (hp : Pre w s₀) {k : Nat} (hk : k < 3) :
    InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ k) 4 :=
  ⟨argR s₀, by simp [hp.rd], by rw [argAddr_eq hp hk]; exact contains_off _ (by omega_using [hk]) (by omega_using [])⟩

theorem arg_sub {s₀ : State} (hp : Pre w s₀) {k : Nat} (hk : k < 3) :
    Region.Sub ⟨stackArgAddr s₀ k, 4⟩ (argR s₀) := by
  rw [argAddr_eq hp hk]; exact Offset.sub_base _ (by omega_using [hk])

theorem prologue_ok {s₀ : State} (hp : Pre w s₀) :
    WP isa (.block prologue) s₀ fun s => Common w s₀ 0 s ∧
      ∀ i < bufOff w + blockBytes w, s.mem (stA s₀ + BitVec.ofNat 64 i) = s₀.mem (stA s₀ + BitVec.ofNat 64 i) := by
  have hsc := hp.scr_fit
  simp only [prologue, List.cons_append, List.nil_append]
  refine wp_ldrSp (a := stackArgAddr s₀ 2) (by decide) rfl (arg_in hp (by decide)) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = scr s₀ := u₁.gpr
  refine save_ok (by rw [h12]; omega_using [hsc]) (fun d hd₁ hd₂ => ⟨scR s₀, by simp [u₁.wr, hp.wr],
    by rw [h12]; exact contains_off _ (by omega_using [hd₂]) (by omega_using [])⟩) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  -- The save writes only the scratch space.
  obtain hframe : Frame [scR s₀] s₀.mem s₂.mem := by
    rw [m₂, u₁.mem, h12]; exact saveMem_frame _ _ _
  obtain harg : ∀ k, k < 3 → s₂.mem.readW (stackArgAddr s₀ k) 32 = stackArg s₀ k := fun k hk =>
    hframe.readW (Region.contains_self _ _) (by simpa using (hp.a_scr.sub_left (arg_sub hp hk))) (by decide)
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide)
    (by rw [u₄.sp, u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]; exact arg_in hp (by decide)) fun s₅ u₅ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide)
    (by rw [u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]; exact arg_in hp (by decide))
    fun s₆ u₆ => wp_mov (op2_reg _ _) fun s₇ u₇ => wp_mov (op2_reg _ _) fun s₈ u₈ => WP.block_nil ?_
  obtain mm : s₈.mem = s₂.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  refine ⟨⟨Nat.zero_le _, by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd],
    by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr],
    by rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, g₂, u₁.other _ (by decide)]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.gpr, u₃.other _ (by decide), g₂, h12]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem,
      harg 0 (by decide)]
    simp
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.mem, u₄.mem, u₃.mem, harg 1 (by decide)]
    simp
  · have h9 : s₈.gpr .r9 = s₀.gpr .r2 := by
      rw [u₈.other .r9 (by decide), u₇.gpr, u₆.other .r2 (by decide), u₅.other .r2 (by decide),
        u₄.other .r2 (by decide), u₃.other .r2 (by decide), g₂, u₁.other .r2 (by decide)]
    obtain h10 : s₈.gpr .r10 = s₀.gpr .r3 := by
      rw [u₈.gpr, u₇.other .r3 (by decide), u₆.other .r3 (by decide), u₅.other .r3 (by decide),
        u₄.other .r3 (by decide), u₃.other .r3 (by decide), g₂, u₁.other .r3 (by decide)]
    rw [h9, h10, Nat.add_zero (cnt s₀), cnt, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rfl
  · rw [mm]; exact hframe.mono (by simp)
  · intro p hp'
    rw [mm, m₂, u₁.mem, h12, saveMem_saved _ _ _ p hp', u₁.other _ (Ne.symm ?_)]
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
  · intro i hi
    rw [mm]
    exact hframe.bytes (R := stR s₀ w) (by simpa using hp.st_scr)
      (by show bufOff w + blockBytes w ≤ 2 ^ 64; have := hp.st_fit; omega_using [this]) hi

/-! ## The number of bytes in the buffer -/

theorem bufLen_ok (hP : Ok P) {s : State} {x : Nat} (hx : x < 2 ^ 64)
    (hc : s.gpr .r10 ++ s.gpr .r9 = BitVec.ofNat 64 x) :
    WP isa (Impl.Blake2.Arm.Stream.bufLen (w := w)) s fun s' =>
      s'.gpr .r8 = BitVec.ofNat 32 (bufLen w x) ∧
      (∀ r, r ≠ .r8 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold Impl.Blake2.Arm.Stream.bufLen
  obtain h9 : s.gpr .r9 = BitVec.ofNat 32 x := lo_of_pair hc
  refine WP.seq (wp_sub (op2_imm (by decide)) fun s₁ u₁ => wp_and (op2_imm hP.encB1) fun s₂ u₂ =>
    wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_orr (op2_reg _ _) fun s₄ u₄ =>
    wp_cmp (op2_imm (by decide)) fun s₅ f₅ z₅ => WP.block_nil ?_)
  obtain g : ∀ r, r ≠ .r8 → r ≠ .r12 → s₅.gpr r = s.gpr r := fun r h1 h2 => by
    rw [f₅.gpr, u₄.other r h2, u₃.other r h1, u₂.other r h1, u₁.other r h1]
  obtain hm : s₅.mem = s.mem := by rw [f₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain hrd : s₅.rd = s.rd := by rw [f₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  obtain hwr : s₅.wr = s.wr := by rw [f₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  obtain hsp : s₅.sp = s.sp := by rw [f₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  obtain hz : s₅.z = decide (x = 0) := by
    rw [z₅, u₄.gpr, u₃.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), u₁.other _ (by decide)]
    exact or_beq_zero hc hx
  refine WP.ite (decide (x = 0)) (by show VG.Arm.eval .eq s₅ = _; rw [eval_eq, hz]) (fun hb => ?_)
    (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine wp_mov (op2_imm (by decide)) fun s₆ u₆ => WP.block_nil ⟨?_, fun r h1 h2 => by
      rw [u₆.other r h1, g r h1 h2], by rw [u₆.mem, hm], by rw [u₆.rd, hrd], by rw [u₆.wr, hwr],
      by rw [u₆.sp, hsp]⟩
    rw [u₆.gpr, hb]; rfl
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.block_nil ⟨?_, g, hm, hrd, hwr, hsp⟩
    rw [f₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.gpr, h9]
    exact bufLen_lo hP hb

theorem bufLen_inv (hP : Ok P) {s₀ : State} {s : State} (hC : Common w s₀ 0 s)
    (hst : ∀ i < bufOff w + blockBytes w, s.mem (stA s₀ + BitVec.ofNat 64 i) = s₀.mem (stA s₀ + BitVec.ofNat 64 i)) :
    WP isa (Impl.Blake2.Arm.Stream.bufLen (w := w)) s (Inv P s₀ 0 (bufLen w (cnt s₀))) := by
  obtain hrepr : ∀ h0 d, R₀ P s₀ h0 d →
      ReprR P h0 s.mem (stA s₀) (d ++ D s₀ 0) (bufLen w (cnt s₀)) := by
    intro h0 d hd
    obtain e : D s₀ 0 = [] := by simp [bytesAt]
    rw [e, List.append_nil, hd.cnt_eq, ← repr_iff P hP.pos]
    exact repr_congr hP hst hd.1
  refine WP.mono (bufLen_ok hP (cnt_lt s₀) hC.cn) fun s' ⟨h8, g, m, rd, wr, sp⟩ => ?_
  exact { hC.of_gpr (fun r hr => g r (notC hr .r8) (notC hr .r12)) m rd wr sp with
    r8 := h8, repr := by rw [m]; exact hrepr }

/-! ## Copying data into the buffer -/

/-- `copy`: copying `k` bytes of data (none if `k = 0`), from byte `c` on,
into the buffer, from byte `r` on. -/
theorem copy_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {c r k : Nat} (hrk : r + k ≤ blockBytes w)
    (hck : c + k ≤ len s₀) {s : State} (hI : Inv P s₀ c r s) (h11 : s.gpr .r11 = BitVec.ofNat 32 k) :
    WP isa (copy (w := w)) s (Inv P s₀ (c + k) (r + k)) := by
  have hl := hP.len
  obtain hL := len_lt s₀
  obtain hst := hp.st_fit; have hdf := hp.d_fit
  unfold copy
  refine WP.seq (wp_sub (op2_reg _ _) fun s₁ u₁ => wp_adds (op2_reg _ _) fun s₂ u₂ c₂ =>
    wp_adc (op2_imm (by decide)) fun s₃ u₃ _ => wp_cmp (op2_imm (by decide)) fun s₄ f₄ z₄ =>
    WP.block_nil ?_)
  obtain g₄ : ∀ x, x ≠ .r7 → x ≠ .r9 → x ≠ .r10 → s₄.gpr x = s.gpr x := fun x h1 h2 h3 => by
    rw [f₄.gpr, u₃.other x h3, u₂.other x h2, u₁.other x h1]
  obtain h7 : s₄.gpr .r7 = BitVec.ofNat 32 (len s₀ - (c + k)) := by
    rw [f₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hI.r7, h11, sub_ofNat (by omega_using [hck]),
      Nat.sub_sub]
  obtain hcn : s₄.gpr .r10 ++ s₄.gpr .r9 = BitVec.ofNat 64 (cnt s₀ + (c + k)) := by
    rw [f₄.gpr, u₃.gpr, u₃.other .r9 (by decide), u₂.gpr, u₂.other .r10 (by decide), c₂,
      u₁.other .r9 (by decide), u₁.other .r10 (by decide), u₁.other .r11 (by decide), h11,
      add64_ofNat hI.cn (by omega_using [hck, hL]), Nat.add_assoc]
  obtain hm₄ : s₄.mem = s.mem := by rw [f₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain hrd₄ : s₄.rd = s.rd := by rw [f₄.rd, u₃.rd, u₂.rd, u₁.rd]
  obtain hwr₄ : s₄.wr = s.wr := by rw [f₄.wr, u₃.wr, u₂.wr, u₁.wr]
  obtain hsp₄ : s₄.sp = s.sp := by rw [f₄.sp, u₃.sp, u₂.sp, u₁.sp]
  obtain h4 : s₄.gpr .r4 = st s₀ := by rw [g₄ _ (by decide) (by decide) (by decide), hI.r4]
  obtain h5 : s₄.gpr .r5 = scr s₀ := by rw [g₄ _ (by decide) (by decide) (by decide), hI.r5]
  obtain h6 : s₄.gpr .r6 = dp s₀ + BitVec.ofNat 32 c := by rw [g₄ _ (by decide) (by decide) (by decide), hI.r6]
  obtain h8 : s₄.gpr .r8 = BitVec.ofNat 32 r := by rw [g₄ _ (by decide) (by decide) (by decide), hI.r8]
  obtain h11' : s₄.gpr .r11 = BitVec.ofNat 32 k := by rw [g₄ _ (by decide) (by decide) (by decide), h11]
  obtain hz : isa.eval .eq s₄ = some (decide (k = 0)) := by
    show VG.Arm.eval .eq s₄ = _
    rw [eval_eq, z₄, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h11,
      cmp0 (by omega_using [hck, hL])]
  refine WP.ite (decide (k = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    simp only [Nat.add_zero] at hcn h7 ⊢
    exact WP.block_nil
      { c_le := hI.c_le
        rd := hrd₄.trans hI.rd
        wr := hwr₄.trans hI.wr
        sp := hsp₄.trans hI.sp
        r4 := h4
        r5 := h5
        r6 := h6
        r7 := h7
        cn := hcn
        frame := hm₄ ▸ hI.frame
        saved := hm₄ ▸ hI.saved
        r8 := h8
        repr := hm₄ ▸ hI.repr }
  · simp only [decide_eq_false_iff_not] at hb
    obtain hcl : c < len s₀ := by omega_using [hck, hb]
    obtain hsrc : ∀ i < k, InRegions (s₄.rd ++ s₄.wr)
        (State.addr (dp s₀ + BitVec.ofNat 32 c) + BitVec.ofNat 64 i) 1 := fun i hi =>
      ⟨dR s₀, by simp [hrd₄, hI.rd, hp.rd], by
        rw [addr_add (by omega_using [hdf, hcl]), Offset.add_add]; exact contains_off _ (by omega_using [hck, hi]) (by omega_using [hdf])⟩
    obtain hdst : ∀ i < k, InRegions s₄.wr (stA s₀ + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 i) 1 :=
      fun i hi => ⟨stR s₀ w, by simp [hwr₄, hI.wr, hp.wr], by
        rw [Offset.add_add]; exact contains_off _ (by omega_using [hrk, hi]) (by omega_using [hst])⟩
    obtain hd : Region.Disjoint ⟨State.addr (dp s₀ + BitVec.ofNat 32 c), k⟩
        ⟨stA s₀ + BitVec.ofNat 64 (bufOff w + r), k⟩ := by
      rw [addr_add (by omega_using [hdf, hcl])]
      exact (hp.d_st.sub_left (Offset.sub_base _ (by omega_using [hck]))).sub_right (Offset.sub_base _ (by omega_using [hrk]))
    refine copyLoop_ok (st := st s₀) hl.2.1 (by omega_using [hb]) (by omega_using [hrk, hst])
      (by rw [toNat_add_ofNat (by omega_using [hdf, hcl])]; omega_using [hck, hdf]) h4 h6 h8 h11' hsrc hdst hd fun s' h => ?_
    obtain hx : bytesAt s₄.mem (State.addr (dp s₀ + BitVec.ofNat 32 c)) k =
        bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 c) k := by
      rw [addr_add (by omega_using [hdf, hcl]), hm₄]
      exact bytesAt_congr fun i hi => by rw [Offset.add_add]; exact hI.data hp (by omega_using [hck, hi])
    obtain hmem : s'.mem = writeBytes s.mem (stA s₀ + BitVec.ofNat 64 (bufOff w + r))
        (bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 c) k) := by
      rw [h.mem, List.take_of_length_le (by rw [bytesAt_length]), hx, hm₄]
    obtain hfw : Frame [stR s₀ w] s.mem s'.mem := by
      rw [hmem]
      exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact contains_off _ (by omega_using [hrk]) (by omega_using [hst]))
    obtain g' : ∀ x, x ≠ .r12 → x ≠ .r1 → x ≠ .r6 → x ≠ .r8 → x ≠ .r11 → x ≠ .r7 → x ≠ .r9 → x ≠ .r10 →
        s'.gpr x = s.gpr x := fun x h1 h2 h3 h4 h5 h6 h7 h8 => by
      rw [h.other x h1 h2 h3 h4 h5, g₄ x h6 h7 h8]
    refine
      { c_le := by omega_using [hck]
        rd := h.rd.trans (hrd₄.trans hI.rd)
        wr := h.wr.trans (hwr₄.trans hI.wr)
        sp := h.sp.trans (hsp₄.trans hI.sp)
        r4 := by rw [g' .r4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide), hI.r4]
        r5 := by rw [g' .r5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide), hI.r5]
        r6 := by rw [h.r6, BitVec.add_assoc, ← BitVec.ofNat_add]
        r7 := by rw [h.other .r7 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h7
        cn := by
          rw [h.other .r9 (by decide) (by decide) (by decide) (by decide) (by decide),
            h.other .r10 (by decide) (by decide) (by decide) (by decide) (by decide)]
          exact hcn
        frame := hI.frame.trans (hfw.mono (by simp))
        saved := saved_frame hp hI.saved (hfw.mono (by simp))
        r8 := h.r8
        repr := fun h0 d hd => ?_ }
    obtain e : d ++ D s₀ (c + k) = d ++ D s₀ c ++ bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 c) k := by
      rw [D, bytesAt_add, List.append_assoc]
    rw [e]
    have := reprR_append P (hI.repr h0 d hd) (x := bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 c) k)
      (mem' := s'.mem) (by rw [bytesAt_length]; exact hrk) ?_ ?_
    · rwa [bytesAt_length] at this
    · rw [hmem]
      exact stateAt_congr fun i hi => writeBytes_before _ _ _ (by omega_using [hi]) (by rw [bytesAt_length]; omega_using [hrk, hst])
    · rw [hmem, ← Offset.add_add, bytesAt_writeBytes _ _ _ _ (by rw [bytesAt_length]; omega_using [hrk, hst])]

/-- `fill`: copying `min(B - r, len - c)` bytes of data into the buffer. -/
theorem fill_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {c r : Nat} (hr : r ≤ blockBytes w) {s : State}
    (hI : Inv P s₀ c r s) :
    WP isa (fill (w := w)) s (Inv P s₀ (c + min (blockBytes w - r) (len s₀ - c))
      (r + min (blockBytes w - r) (len s₀ - c))) := by
  obtain hL := len_lt s₀
  have hc := hI.c_le
  have hpos := hP.pos
  have hl := hP.len
  obtain hbb : blockBytes w ≤ 128 := by rcases hP.bb with h | h <;> omega_using [h]
  obtain ⟨a, ha⟩ : ∃ a, a = min (blockBytes w - r) (len s₀ - c) := ⟨_, rfl⟩
  rw [← ha]
  obtain hlbb : 1 ≤ lbb w ∧ lbb w ≤ 31 := ⟨hP.lbb.1, hP.lbb.2.1⟩
  unfold fill
  refine WP.seq (wp_mov (op2_imm hP.encB) fun s₁ u₁ => wp_sub (op2_reg _ _) fun s₂ u₂ =>
    wp_mov (op2_lsr hlbb) fun s₃ u₃ => wp_cmp (op2_imm (by decide)) fun s₄ f₄ z₄ => WP.block_nil ?_)
  obtain hI₄ : Inv P s₀ c r s₄ := (((hI.of_upd u₁).of_upd u₂).of_upd u₃).of_flags f₄
  obtain h11 : s₄.gpr .r11 = BitVec.ofNat 32 (blockBytes w - r) := by
    rw [f₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), hI.r8, B_eq,
      sub_ofNat hr]
  obtain hz : isa.eval .eq s₄ = some (decide ((len s₀ - c) / blockBytes w = 0)) := by
    show VG.Arm.eval .eq s₄ = _
    rw [eval_eq, z₄, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hI.r7,
      shr_ofNat hP (by omega_using [hL]), cmp0 (by have := Nat.div_le_self (len s₀ - c) (blockBytes w); omega_using [hL, this])]
  refine WP.seq (WP.mono (Q := fun (t : State) => Inv P s₀ c r t ∧ t.gpr .r11 = BitVec.ofNat 32 a) ?_
    fun (t : State) (ht : Inv P s₀ c r t ∧ t.gpr .r11 = BitVec.ofNat 32 a) =>
      copy_ok hP hp (by omega_using [hr, ha]) (by omega_using [hc, ha]) ht.1 ht.2)
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    obtain hlt : len s₀ - c < blockBytes w := by
      refine Nat.lt_of_not_le fun h' => ?_
      have := Nat.div_pos h' hpos
      omega_using [hb, this]
    refine WP.seq (wp_add (op2_reg _ _) fun s₅ u₅ => wp_mov (op2_lsr hlbb) fun s₆ u₆ =>
      wp_cmp (op2_imm (by decide)) fun s₇ f₇ z₇ => WP.block_nil ?_)
    obtain hI₇ : Inv P s₀ c r s₇ := ((hI₄.of_upd u₅).of_upd u₆).of_flags f₇
    obtain hz₇ : isa.eval .eq s₇ = some (decide ((len s₀ - c + r) / blockBytes w = 0)) := by
      show VG.Arm.eval .eq s₇ = _
      rw [eval_eq, z₇, u₆.gpr, u₅.gpr, hI₄.r7, hI₄.r8, ← BitVec.ofNat_add, shr_ofNat hP (by omega_using [hr, hbb, hlt]),
        cmp0 (by have := Nat.div_le_self (len s₀ - c + r) (blockBytes w); omega_using [hr, hbb, hlt, this])]
    refine WP.ite _ hz₇ (fun hb' => ?_) (fun hb' => ?_)
    · simp only [decide_eq_true_eq] at hb'
      obtain hlt' : len s₀ - c + r < blockBytes w := by
        refine Nat.lt_of_not_le fun h' => ?_
        have := Nat.div_pos h' hpos
        omega_using [hb', this]
      refine wp_mov (op2_reg _ _) fun s₈ u₈ => WP.block_nil ⟨hI₇.of_upd u₈, ?_⟩
      rw [u₈.gpr, hI₇.r7, ha]
      congr 1; omega_using [hlt']
    · simp only [decide_eq_false_iff_not] at hb'
      obtain hge : blockBytes w ≤ len s₀ - c + r := by
        refine Nat.le_of_not_lt fun h' => hb' (Nat.div_eq_of_lt h')
      refine WP.block_nil ⟨hI₇, ?_⟩
      rw [f₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), h11, ha]
      congr 1; omega_using [hge]
  · simp only [decide_eq_false_iff_not] at hb
    obtain hge : blockBytes w ≤ len s₀ - c := by
      refine Nat.le_of_not_lt fun h' => hb (Nat.div_eq_of_lt h')
    refine WP.block_nil ⟨hI₄, ?_⟩
    rw [h11, ha]
    congr 1; omega_using [hge]

/-! ## Up to the first call -/

section
variable (w : Nat) (s₀ : State)

/-- The bytes in the buffer on entry. -/
abbrev r₀ : Nat := bufLen w (cnt s₀)
/-- The bytes of data copied into a non-empty buffer. -/
def a₁ : Nat := if r₀ w s₀ = 0 then 0 else min (blockBytes w - r₀ w s₀) (len s₀)
/-- The blocks the first call compresses: the buffer, if it is not empty and
more data follows (it is then full). -/
def n₁ : Nat := if len s₀ - a₁ w s₀ ≠ 0 ∧ r₀ w s₀ + a₁ w s₀ ≠ 0 then 1 else 0

end

theorem a₁_le (s₀ : State) : a₁ w s₀ ≤ len s₀ := by
  unfold a₁; split <;> omega_using []

theorem a₁_eq (s₀ : State) (h : r₀ w s₀ ≠ 0) : a₁ w s₀ = min (blockBytes w - r₀ w s₀) (len s₀) := by
  simp only [a₁, h, ite_false]

theorem a₁_zero (s₀ : State) (h : r₀ w s₀ = 0) : a₁ w s₀ = 0 := by
  simp only [a₁, h, ite_true]

theorem r₁_le (hP : Ok P) (s₀ : State) : r₀ w s₀ + a₁ w s₀ ≤ blockBytes w := by
  obtain hr : r₀ w s₀ ≤ blockBytes w := bufLen_le hP.pos _
  by_cases h0 : r₀ w s₀ = 0
  · rw [a₁_zero s₀ h0]; omega_using [h0]
  · rw [a₁_eq s₀ h0]; omega_using [hr]

/-- The first call compresses the buffer only when it is full. -/
theorem n₁_full (hP : Ok P) (s₀ : State) (h : n₁ w s₀ = 1) : r₀ w s₀ + a₁ w s₀ = blockBytes w := by
  obtain hr : r₀ w s₀ ≤ blockBytes w := bufLen_le hP.pos _
  simp only [n₁] at h
  split at h
  · rename_i hc
    by_cases h0 : r₀ w s₀ = 0
    · rw [a₁_zero s₀ h0] at hc; omega_using [hc, h0]
    · rw [a₁_eq s₀ h0] at hc ⊢; omega_using [hr, hc]
  · cases h

theorem n₁_le (s₀ : State) : n₁ w s₀ ≤ 1 := by unfold n₁; split <;> omega_using []

theorem head_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {s : State} (hI : Inv P s₀ 0 (r₀ w s₀) s)
    {rest : Prog isa} {Q : State → Prop}
    (k : ∀ t, Inv P s₀ (a₁ w s₀) (r₀ w s₀ + a₁ w s₀) t → WP isa rest t Q) :
    WP isa (.seq (.block [.cmp .r8 (.imm 0)]) (.seq (.ite .eq (.block []) (fill (w := w))) rest)) s Q := by
  obtain hr : r₀ w s₀ ≤ blockBytes w := bufLen_le hP.pos _
  obtain hB : blockBytes w ≤ 128 := by rcases hP.bb with h | h <;> omega_using [h]
  refine WP.seq (wp_cmp (op2_imm (by decide)) fun s₁ f₁ z₁ => WP.block_nil ?_)
  obtain hI₁ := hI.of_flags f₁
  obtain hz : isa.eval .eq s₁ = some (decide (r₀ w s₀ = 0)) := by
    show VG.Arm.eval .eq s₁ = _
    rw [eval_eq, z₁, hI.r8, cmp0 (by omega_using [hr, hB])]
  refine WP.seq (WP.mono (WP.ite _ hz (fun hb => ?_) (fun hb => ?_)) k)
  · simp only [decide_eq_true_eq] at hb
    rw [a₁_zero s₀ hb, Nat.add_zero]
    exact WP.block_nil hI₁
  · simp only [decide_eq_false_iff_not] at hb
    obtain h := fill_ok hP hp hr hI₁
    simp only [Nat.zero_add, Nat.sub_zero] at h
    rw [a₁_eq s₀ hb]
    exact h

/-! ## The arguments of a call -/

theorem common_sp {s₀ : State} {c : Nat} {s : State} (h : Common w s₀ c s) : below s = below s₀ := by
  rw [below, below, h.sp]

theorem cov_of {s₀ : State} (hp : Pre w s₀) {c : Nat} {s : State} (h : Common w s₀ c s) {R : Region}
    (hR : (∃ off, R.base = stA s₀ + BitVec.ofNat 64 off ∧ off + R.len ≤ bufOff w + blockBytes w) ∨
      (∃ off, R.base = dA s₀ + BitVec.ofNat 64 off ∧ off + R.len ≤ len s₀)) :
    Covers [R] (s.rd ++ s.wr) := by
  rw [h.rd, h.wr, hp.rd, hp.wr]
  apply Covers.of_sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  rcases hR with ⟨off, h1, h2⟩ | ⟨off, h1, h2⟩
  · exact ⟨stR s₀ w, by simp, off, h1, h2⟩
  · exact ⟨dR s₀, by simp, off, h1, h2⟩

/-- The arguments of a call, from the registers. -/
theorem callArgs_of (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {c : Nat} {s : State} (h : Common w s₀ c s)
    {blk : BitVec 32} {n : Nat} {t : BitVec 64} {last : BitVec 32}
    (hblk : (blk = st s₀ + BitVec.ofNat 32 (bufOff w) ∧ n ≤ 1) ∨
      (∃ c₀, blk = dp s₀ + BitVec.ofNat 32 c₀ ∧ c₀ < len s₀ ∧ c₀ + blockBytes w * n ≤ len s₀) ∨
      (blk = st s₀ ∧ n = 0))
    (h0 : s.gpr .r0 = st s₀) (h1 : s.gpr .r1 = blk) (h2 : s.gpr .r2 = BitVec.ofNat 32 n)
    (ht : s.gpr .r11 ++ s.gpr .r3 = t) (h12 : s.gpr .r12 = last) (hlr : s.gpr .lr = scr s₀) :
    CallArgs (w := w) s (st s₀) (scr s₀) blk n t last := by
  have hl := hP.len
  obtain hst := hp.st_fit; have hsc := hp.scr_fit; have hdf := hp.d_fit
  obtain hL := len_lt s₀
  obtain eN : Region.Sub ⟨stA s₀, bufOff w⟩ (stR s₀ w) := Region.sub_prefix (by omega_using [])
  obtain eS : Region.Sub ⟨scA s₀, 512⟩ (scR s₀) := Region.sub_prefix (by omega_using [])
  -- Where the blocks are.
  obtain hB : (State.addr blk = stA s₀ + BitVec.ofNat 64 (bufOff w) ∧ blockBytes w * n ≤ blockBytes w) ∨
      (∃ c₀, State.addr blk = dA s₀ + BitVec.ofNat 64 c₀ ∧ c₀ + blockBytes w * n ≤ len s₀) ∨
      (State.addr blk = stA s₀ ∧ n = 0) := by
    rcases hblk with ⟨rfl, hn⟩ | ⟨c₀, rfl, hc₀, hc₁⟩ | ⟨rfl, hn⟩
    · refine .inl ⟨addr_add (by omega_using [hl, hst]), ?_⟩
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl <;> omega_using []
    · exact .inr (.inl ⟨c₀, addr_add (by omega_using [hdf, hc₀]), hc₁⟩)
    · exact .inr (.inr ⟨rfl, hn⟩)
  obtain hBn : blockBytes w * n ≤ 2 ^ 32 := by
    rcases hB with ⟨-, h⟩ | ⟨c₀, -, h⟩ | ⟨-, rfl⟩ <;> omega_arith
  obtain hsub : Region.Sub ⟨State.addr blk, blockBytes w * n⟩ (stR s₀ w) ∨
      Region.Sub ⟨State.addr blk, blockBytes w * n⟩ (dR s₀) := by
    rcases hB with ⟨e, h⟩ | ⟨c₀, e, h⟩ | ⟨e, rfl⟩
    · exact .inl (e ▸ Offset.sub_base _ (by omega_arith))
    · exact .inr (e ▸ Offset.sub_base _ (by omega_arith))
    · exact .inl (by rw [e, Nat.mul_zero]; exact Region.sub_prefix (by omega_using []))
  obtain hblkN : blk.toNat + blockBytes w * n ≤ 2 ^ 32 := by
    rcases hblk with ⟨rfl, hn⟩ | ⟨c₀, rfl, hc₀, hc₁⟩ | ⟨rfl, rfl⟩
    · rw [toNat_add_ofNat (by omega_using [hl, hst])]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl <;> omega_using [hst]
    · rw [toNat_add_ofNat (by omega_using [hdf, hc₀])]; omega_using [hdf, hc₁]
    · omega_using []
  obtain hn : n < 2 ^ 32 := by
    have := hP.pos
    rcases Nat.lt_or_ge n (2 ^ 32) with h | h
    · exact h
    · exfalso; have := Nat.mul_le_mul_left (blockBytes w) h; omega_arith
  refine ⟨h0, h1, h2, ht, h12, hlr, hn, by rw [h.sp]; exact hp.sp16, ?_, ?_, (hp.st_scr.sub_left eN).sub_right eS, ?_, ?_, ?_, ?_, ?_,
    by omega_using [hst], hblkN, by omega_using [hsc]⟩
  · refine cov_of hp h ?_
    rcases hB with ⟨e, h'⟩ | ⟨c₀, e, h'⟩ | ⟨e, rfl⟩
    · exact .inl ⟨bufOff w, e, by dsimp only; omega_using [h']⟩
    · exact .inr ⟨c₀, e, h'⟩
    · exact .inl ⟨0, by rw [e]; simp, by dsimp only; omega_using []⟩
  · rw [h.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
  · rcases hB with ⟨e, h'⟩ | ⟨c₀, e, h'⟩ | ⟨e, rfl⟩
    · rw [e]; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega_using [hst, h'])
    · exact (hp.d_st.sub_left (e ▸ Offset.sub_base _ (by omega_using [h']))).sub_right eN
    · intro a h₁ _; simp [Region.Contains] at h₁
  · rcases hsub with e | e
    · exact (hp.st_scr.sub_left e).sub_right eS
    · exact (hp.d_scr.sub_left e).sub_right eS
  · rw [common_sp h]; exact hp.w_st.sub_right eN
  · rw [common_sp h]
    rcases hsub with e | e
    · exact hp.w_st.sub_right e
    · exact hp.w_d.sub_right e
  · rw [common_sp h]; exact hp.w_scr.sub_right eS

/-- What a call leaves of `Common`. -/
theorem Common.after_call {s₀ : State} (hp : Pre w s₀) {c : Nat} {s s' : State} (h : Common w s₀ c s)
    (ha : After s [⟨stA s₀, bufOff w⟩, ⟨scA s₀, 512⟩] s') (hl : bufOff w ≤ bufOff w + blockBytes w) :
    Common w s₀ c s' := by
  obtain hf : Frame [stR s₀ w, ⟨scA s₀, 512⟩, below s₀] s.mem s'.mem := by
    have := ha.frame
    rw [common_sp h] at this
    exact this.sub fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨stR s₀ w, by simp, Region.sub_prefix hl⟩
      · exact ⟨⟨scA s₀, 512⟩, by simp, fun _ h => h⟩
      · exact ⟨below s₀, by simp, fun _ h => h⟩
  obtain hcp : ∀ r ∈ commonRegs, r ∈ preserved ∧ r ≠ .lr := by decide
  obtain hg : ∀ r ∈ commonRegs, s'.gpr r = s.gpr r := fun r hr => ha.cs r (hcp r hr).1 (hcp r hr).2
  refine ⟨h.c_le, ha.rd.trans h.rd, ha.wr.trans h.wr, ha.sp.trans h.sp, by rw [hg _ (by simp)]; exact h.r4,
    by rw [hg _ (by simp)]; exact h.r5, by rw [hg _ (by simp)]; exact h.r6, by rw [hg _ (by simp)]; exact h.r7,
    by rw [hg .r9 (by simp), hg .r10 (by simp)]; exact h.cn,
    h.frame.trans (hf.sub fun r hr => ?_), saved_frame hp h.saved hf⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨stR s₀ w, by simp, fun _ h => h⟩
  · exact ⟨scR s₀, by simp, Region.sub_prefix (by omega_using [])⟩
  · exact ⟨below s₀, by simp, fun _ h => h⟩

theorem r8_after {s s' : State} {ws : List Region} (ha : After s ws s') : s'.gpr .r8 = s.gpr .r8 :=
  ha.cs .r8 (by simp [preserved]) (by decide)

/-! ## The prologue, up to the first call -/

/-- What holds before the first call. -/
def PostPro (P : Params w) (s₀ : State) (s : State) : Prop :=
  Inv P s₀ (a₁ w s₀) (r₀ w s₀ + a₁ w s₀) s ∧
    CallArgs (w := w) s (st s₀) (scr s₀) (st s₀ + BitVec.ofNat 32 (bufOff w)) (n₁ w s₀)
      (BitVec.ofNat 64 (cnt s₀ + a₁ w s₀)) 0

theorem args₁_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {s : State}
    (hI : Inv P s₀ (a₁ w s₀) (r₀ w s₀ + a₁ w s₀) s) :
    WP isa (.seq (.block [.mov .r2 (.imm 0), .cmp .r7 (.imm 0)])
      (.seq (.ite .eq (.block []) (.seq (.block [.cmp .r8 (.imm 0)])
        (.ite .eq (.block []) (.block [.mov .r2 (.imm 1)]))))
      (.block (args ++ ([.dp .add .r1 .r4 (.imm (BitVec.ofNat 32 (N w))), .mov .r3 (.reg .r9),
        .mov .r11 (.reg .r10)] : List Instr))))) s (PostPro P s₀) := by
  obtain hL := len_lt s₀
  obtain hr := r₁_le hP s₀
  have hl := hP.len
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_cmp (op2_imm (by decide)) fun s₂ f₂ z₂ =>
    WP.block_nil ?_)
  obtain hI₂ := (hI.of_upd u₁).of_flags f₂
  obtain hz : isa.eval .eq s₂ = some (decide (len s₀ - a₁ w s₀ = 0)) := by
    show VG.Arm.eval .eq s₂ = _
    rw [eval_eq, z₂, u₁.other _ (by decide), hI.r7, cmp0 (by omega_using [hL])]
  -- `r2` := `n₁`.
  refine WP.seq (WP.mono (Q := fun (t : State) => Inv P s₀ (a₁ w s₀) (r₀ w s₀ + a₁ w s₀) t ∧
      t.gpr .r2 = BitVec.ofNat 32 (n₁ w s₀)) ?_ fun t ⟨hIt, h2t⟩ => ?_)
  · refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      refine WP.block_nil ⟨hI₂, ?_⟩
      rw [f₂.gpr, u₁.gpr]; simp [n₁, hb]
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.seq (wp_cmp (op2_imm (by decide)) fun s₃ f₃ z₃ => WP.block_nil ?_)
      obtain hI₃ := hI₂.of_flags f₃
      obtain hz₃ : isa.eval .eq s₃ = some (decide (r₀ w s₀ + a₁ w s₀ = 0)) := by
        show VG.Arm.eval .eq s₃ = _
        rw [eval_eq, z₃, hI₂.r8, cmp0 (by omega_using [hr, hl])]
      refine WP.ite _ hz₃ (fun hb' => ?_) (fun hb' => ?_)
      · simp only [decide_eq_true_eq] at hb'
        refine WP.block_nil ⟨hI₃, ?_⟩
        rw [f₃.gpr, f₂.gpr, u₁.gpr]; simp [n₁, hb']
      · simp only [decide_eq_false_iff_not] at hb'
        refine wp_mov (op2_imm (by decide)) fun s₄ u₄ => WP.block_nil ⟨hI₃.of_upd u₄, ?_⟩
        rw [u₄.gpr]; simp only [n₁, ne_eq, hb, hb', not_false_eq_true, and_self, ite_true]; rfl
  · simp only [args, List.cons_append, List.nil_append]
    refine wp_mov (op2_reg _ _) fun s₅ u₅ => wp_mov (op2_imm (by decide)) fun s₆ u₆ =>
      wp_mov (op2_reg _ _) fun s₇ u₇ => wp_add (op2_imm hP.encN) fun s₈ u₈ =>
      wp_mov (op2_reg _ _) fun s₉ u₉ => wp_mov (op2_reg _ _) fun s₁₀ u₁₀ => WP.block_nil ?_
    obtain hI' : Inv P s₀ (a₁ w s₀) (r₀ w s₀ + a₁ w s₀) s₁₀ :=
      (((((hIt.of_upd u₅).of_upd u₆).of_upd u₇).of_upd u₈).of_upd u₉).of_upd u₁₀
    refine ⟨hI', callArgs_of hP hp hI'.toCommon (.inl ⟨rfl, n₁_le s₀⟩) ?_ ?_ ?_ ?_ ?_ ?_⟩ <;>
      simp only [u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other,
        u₅.gpr, u₅.other, ne_eq, reduceCtorEq, not_false_eq_true, hIt.r4, hIt.r5, h2t, N_eq]
    exact hIt.cn

theorem pro_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) :
    WP isa (updatePro (w := w)) s₀ (PostPro P s₀) := by
  unfold updatePro
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨hC, hst⟩ => ?_)
  refine WP.seq (WP.mono (bufLen_inv hP hC hst) fun s₂ hI₂ => ?_)
  exact head_ok hP hp hI₂ fun s₃ hI₃ => args₁_ok hP hp hI₃

/-! ## The first call -/

/-- What holds after the first call. -/
def Mid (P : Params w) (s₀ s : State) : Prop :=
  Common w s₀ (a₁ w s₀) s ∧ s.gpr .r8 = BitVec.ofNat 32 (r₀ w s₀ + a₁ w s₀) ∧
    ∀ h0 d, R₀ P s₀ h0 d → ReprR P h0 s.mem (stA s₀) (d ++ D s₀ (a₁ w s₀))
      (if n₁ w s₀ = 1 then 0 else r₀ w s₀ + a₁ w s₀)

theorem compressBlocks_one (h : HashValue w) (m : Mem) (p : Addr) (t : Nat) (f : Bool) :
    compressBlocks P h m p 1 t f = F P h (blockAt w m p) t f := by
  rw [compressBlocks_succ, compressBlocks_zero]; simp

/-- The buffer's bytes are not among those a call may write. -/
theorem buf_after {s₀ : State} (hp : Pre w s₀) {c : Nat} {s s' : State} (h : Common w s₀ c s)
    (ha : After s [⟨stA s₀, bufOff w⟩, ⟨scA s₀, 512⟩] s') {i : Nat} (hi : i < blockBytes w) :
    s'.mem (stA s₀ + BitVec.ofNat 64 (bufOff w) + BitVec.ofNat 64 i) =
      s.mem (stA s₀ + BitVec.ofNat 64 (bufOff w) + BitVec.ofNat 64 i) := by
  have hst := hp.st_fit
  obtain eB : Region.Sub ⟨stA s₀ + BitVec.ofNat 64 (bufOff w), blockBytes w⟩ (stR s₀ w) :=
    Offset.sub_base _ (by omega_using [])
  refine ha.frame.bytes (R := ⟨stA s₀ + BitVec.ofNat 64 (bufOff w), blockBytes w⟩) (fun r hr => ?_)
    (by show blockBytes w ≤ 2 ^ 64; omega_using [hst]) hi
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint_base _ (Nat.le_refl _) (by omega_using [hst])
  · exact (hp.st_scr.sub_left eB).sub_right (Region.sub_prefix (by omega_using []))
  · rw [common_sp h]; exact (hp.w_st.sub_right eB).symm

theorem call₁_ok (hP : Ok P) {name : String} {code : Prog isa} (hf : CalleeOk P code) {s₀ : State}
    (hp : Pre w s₀) {s : State} (h : PostPro P s₀ s) : WP isa (call name code) s (Mid P s₀) := by
  have hl := hP.len
  have hI := h.1
  refine call_ok hf h.2 fun s' ha hst => ⟨hI.toCommon.after_call hp ha (by omega_using []),
    by rw [r8_after ha]; exact hI.r8, fun h0 d hd => ?_⟩
  obtain hr := hI.repr h0 d hd
  split
  · rename_i hn
    rw [n₁_full hP s₀ hn] at hr
    refine reprR_flush P hP.pos hr ?_
    have hlen := hd.2.2
    obtain ha₁ := a₁_le (w := w) s₀
    rw [hst, hn, compressBlocks_one, R₀.length hd _, addr_add (by have := hp.st_fit; omega_using [hl, this]),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [← hd.cnt_eq] at hlen; omega_using [hlen, ha₁])]
    rfl
  · rename_i hn
    obtain hn0 : n₁ w s₀ = 0 := by have := n₁_le (w := w) s₀; omega_using [hn, this]
    rw [hn0, compressBlocks_zero] at hst
    exact reprR_congr hst (fun i hi => buf_after hp hI.toCommon ha (by have := r₁_le hP s₀; omega_using [hi, this])) hr

/-! ## Between the calls -/

section
variable (w : Nat) (s₀ : State)

/-- The bytes in the buffer before the second call. -/
def r₂ : Nat := if (len s₀ - a₁ w s₀) = 0 then r₀ w s₀ + a₁ w s₀ else 0
/-- The blocks the second call compresses. -/
def k₂ : Nat := if (len s₀ - a₁ w s₀) = 0 then 0 else ((len s₀ - a₁ w s₀) - 1) / blockBytes w
/-- Where they are. -/
def blk₂ : BitVec 32 := if (len s₀ - a₁ w s₀) = 0 then st s₀ else dp s₀ + BitVec.ofNat 32 (a₁ w s₀)

end

/-- What holds before the second call. -/
def PostMid (P : Params w) (s₀ s : State) : Prop :=
  Inv P s₀ (a₁ w s₀) (r₂ w s₀) s ∧
    CallArgs (w := w) s (st s₀) (scr s₀) (blk₂ w s₀) (k₂ w s₀)
      (BitVec.ofNat 64 (cnt s₀ + a₁ w s₀ + blockBytes w)) 0

theorem k₂_le (s₀ : State) : a₁ w s₀ + blockBytes w * k₂ w s₀ ≤ len s₀ := by
  have := a₁_le (w := w) s₀
  unfold k₂; split
  · rw [Nat.mul_zero, Nat.add_zero]; exact this
  · have := Nat.mul_div_le ((len s₀ - a₁ w s₀) - 1) (blockBytes w); omega_arith

theorem mid_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {s : State} (h : Mid P s₀ s) :
    WP isa (updateMid (w := w)) s (PostMid P s₀) := by
  obtain ⟨hC, h8, hrep⟩ := h
  obtain hL := len_lt s₀
  obtain ha₁ := a₁_le (w := w) s₀
  obtain hlbb : 1 ≤ lbb w ∧ lbb w ≤ 31 := ⟨hP.lbb.1, hP.lbb.2.1⟩
  unfold updateMid
  refine WP.seq (wp_cmp (op2_imm (by decide)) fun s₁ f₁ z₁ => WP.block_nil ?_)
  obtain hz : isa.eval .eq s₁ = some (decide ((len s₀ - a₁ w s₀) = 0)) := by
    show VG.Arm.eval .eq s₁ = _
    rw [eval_eq, z₁, hC.r7, cmp0 (by omega_using [hL])]
  obtain hC₁ := hC.of_gpr (fun r _ => by rw [f₁.gpr]) f₁.mem f₁.rd f₁.wr f₁.sp
  refine WP.seq (WP.mono (Q := fun (t : State) => Inv P s₀ (a₁ w s₀) (r₂ w s₀) t ∧
      t.gpr .r2 = BitVec.ofNat 32 (k₂ w s₀) ∧ t.gpr .r1 = blk₂ w s₀) ?_ fun t ⟨hIt, h2, h1⟩ => ?_)
  · refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      obtain hn : n₁ w s₀ = 0 := by simp [n₁, hb]
      refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ => WP.block_nil ?_
      obtain hg : ∀ r ∈ .r8 :: commonRegs, s₃.gpr r = s₁.gpr r := fun r hr => by
        rw [u₃.other r (fun e => by subst e; simp at hr), u₂.other r (fun e => by subst e; simp at hr)]
      refine ⟨{ hC₁.of_gpr (fun r hr => hg r (List.mem_cons_of_mem _ hr)) (by rw [u₃.mem, u₂.mem])
          (by rw [u₃.rd, u₂.rd]) (by rw [u₃.wr, u₂.wr]) (by rw [u₃.sp, u₂.sp]) with
        r8 := by rw [hg _ (by simp), f₁.gpr, h8]; simp [r₂, hb]
        repr := fun h0 d hd => by
          rw [u₃.mem, u₂.mem, f₁.mem]
          have := hrep h0 d hd
          simp only [hn] at this
          simpa [r₂, hb] using this }, ?_, ?_⟩
      · rw [u₃.other _ (by decide), u₂.gpr]; simp [k₂, hb]
      · rw [u₃.gpr, u₂.other _ (by decide), f₁.gpr, hC.r4]; simp [blk₂, hb]
    · simp only [decide_eq_false_iff_not] at hb
      refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => wp_sub (op2_imm (by decide)) fun s₃ u₃ =>
        wp_mov (op2_lsr hlbb) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ => WP.block_nil ?_
      obtain hg : ∀ r ∈ commonRegs, s₅.gpr r = s₁.gpr r := fun r hr => by
        rw [u₅.other r (notC hr .r1), u₄.other r (notC hr .r2), u₃.other r (notC hr .r2),
          u₂.other r (notC hr .r8)]
      obtain hr0 : (if n₁ w s₀ = 1 then 0 else r₀ w s₀ + a₁ w s₀) = 0 := by
        simp only [n₁]; split
        · rfl
        · rename_i hc
          simp only [ne_eq, not_and, Decidable.not_not] at hc
          exact hc hb
      refine ⟨{ hC₁.of_gpr hg (by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]) (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd])
          (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr]) (by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp]) with
        r8 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
                 simp [r₂, hb]
        repr := fun h0 d hd => by
          rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, f₁.mem]
          have := hrep h0 d hd
          rw [hr0] at this
          simpa [r₂, hb] using this }, ?_, ?_⟩
      · rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide), f₁.gpr, hC.r7,
          show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega_using [hb]), shr_ofNat hP (by omega_using [hL])]
        simp [k₂, hb]
      · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), f₁.gpr, hC.r6]
        simp [blk₂, hb]
  · simp only [args, List.cons_append, List.nil_append]
    refine wp_mov (op2_reg _ _) fun s₆ u₆ => wp_mov (op2_imm (by decide)) fun s₇ u₇ =>
      wp_mov (op2_reg _ _) fun s₈ u₈ => wp_adds (op2_imm hP.encB) fun s₉ u₉ c₉ =>
      wp_adc (op2_imm (by decide)) fun s₁₀ u₁₀ _ => WP.block_nil ?_
    obtain hI' : Inv P s₀ (a₁ w s₀) (r₂ w s₀) s₁₀ :=
      ((((hIt.of_upd u₆).of_upd u₇).of_upd u₈).of_upd u₉).of_upd u₁₀
    obtain hB : blockBytes w < 2 ^ 32 := by rcases hP.bb with h | h <;> omega_using [h]
    refine ⟨hI', callArgs_of hP hp hI'.toCommon ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
    · by_cases hb : (len s₀ - a₁ w s₀) = 0
      · exact .inr (.inr ⟨by simp [blk₂, hb], by simp [k₂, hb]⟩)
      · refine .inr (.inl ⟨a₁ w s₀, by simp [blk₂, hb], by omega_using [hb], k₂_le (w := w) s₀⟩)
    · simp only [u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.gpr, ne_eq, reduceCtorEq, not_false_eq_true,
        hIt.r4]
    · simp only [u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.other, ne_eq, reduceCtorEq, not_false_eq_true, h1]
    · simp only [u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.other, ne_eq, reduceCtorEq, not_false_eq_true, h2]
    · simp only [u₁₀.gpr, u₁₀.other .r3 (by decide), u₉.gpr, u₉.other .r10 (by decide), c₉,
        u₈.other .r9 (by decide), u₈.other .r10 (by decide), u₇.other .r9 (by decide), u₇.other .r10 (by decide),
        u₆.other .r9 (by decide), u₆.other .r10 (by decide), B_eq]
      exact add64_ofNat hIt.cn hB
    · simp only [u₁₀.other, u₉.other, u₈.other, u₇.gpr, ne_eq, reduceCtorEq, not_false_eq_true]
    · simp only [u₁₀.other, u₉.other, u₈.gpr, u₇.other, u₆.other, ne_eq, reduceCtorEq, not_false_eq_true,
        hIt.r5]

/-! ## The second call -/

/-- What holds after the second call. -/
def End (P : Params w) (s₀ s : State) : Prop :=
  Common w s₀ (a₁ w s₀) s ∧ s.gpr .r8 = BitVec.ofNat 32 (r₂ w s₀) ∧
    ∀ h0 d, R₀ P s₀ h0 d →
      ReprR P h0 s.mem (stA s₀) (d ++ D s₀ (a₁ w s₀ + blockBytes w * k₂ w s₀)) (r₂ w s₀)

theorem call₂_ok (hP : Ok P) {name : String} {code : Prog isa} (hf : CalleeOk P code) {s₀ : State}
    (hp : Pre w s₀) {s : State} (h : PostMid P s₀ s) : WP isa (call name code) s (End P s₀) := by
  have hl := hP.len
  have hI := h.1
  obtain hL := len_lt s₀
  obtain ha₁ := a₁_le (w := w) s₀
  refine call_ok hf h.2 fun s' ha hst => ⟨hI.toCommon.after_call hp ha (by omega_using []),
    by rw [r8_after ha]; exact hI.r8, fun h0 d hd => ?_⟩
  obtain hr := hI.repr h0 d hd
  by_cases hk : k₂ w s₀ = 0
  · rw [hk, compressBlocks_zero] at hst
    rw [hk, Nat.mul_zero, Nat.add_zero]
    exact reprR_congr hst (fun i hi => buf_after hp hI.toCommon ha (by
      have := bufLen_le (w := w) hP.pos (cnt s₀); have := r₁_le hP s₀
      unfold r₂ at hi; split at hi <;> omega_arith)) hr
  · have hb : (len s₀ - a₁ w s₀) ≠ 0 := fun hb => hk (by simp [k₂, hb])
    obtain e2 : r₂ w s₀ = 0 := by simp [r₂, hb]
    rw [e2] at hr ⊢
    obtain hkl := k₂_le (w := w) s₀
    have hpos := hP.pos
    obtain hkB : blockBytes w ≤ blockBytes w * k₂ w s₀ := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hk)
    obtain hlt : a₁ w s₀ + blockBytes w * k₂ w s₀ < len s₀ := by
      have := Nat.div_mul_le_self ((len s₀ - a₁ w s₀) - 1) (blockBytes w)
      simp only [k₂, hb, ite_false] at hkB ⊢; rw [Nat.mul_comm]; omega_using [hb, this]
    have hlen := hd.2.2
    obtain ecn : (BitVec.ofNat 64 (cnt s₀ + a₁ w s₀ + blockBytes w)).toNat =
        (d ++ D s₀ (a₁ w s₀)).length + blockBytes w := by
      rw [R₀.length hd _, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [← hd.cnt_eq] at hlen; omega_using [hkB, hlt, hlen])]
    obtain eblk : State.addr (blk₂ w s₀) = dA s₀ + BitVec.ofNat 64 (a₁ w s₀) := by
      simp only [blk₂, hb, ite_false]; exact addr_add (by have := hp.d_fit; omega_using [hlt, this])
    rw [ecn, eblk] at hst
    have := reprR_blocks P hP.pos hr (mem' := s'.mem) (q := dA s₀ + BitVec.ofNat 64 (a₁ w s₀))
      (k := k₂ w s₀) (by rw [hst]; rfl)
    obtain e : bytesAt s.mem (dA s₀ + BitVec.ofNat 64 (a₁ w s₀)) (blockBytes w * k₂ w s₀) =
        bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 (a₁ w s₀)) (blockBytes w * k₂ w s₀) :=
      bytesAt_congr fun i hi => by rw [Offset.add_add]; exact hI.data hp (by omega_using [hlt, hi])
    rw [e, List.append_assoc, ← bytesAt_add] at this
    exact this

/-! ## The end -/

theorem rem_eq (x : Nat) :
    x - ((x - 1) % blockBytes w + 1) = blockBytes w * ((x - 1) / blockBytes w) := by
  have := Nat.div_add_mod (x - 1) (blockBytes w); omega_using [this]

/-- The final state of `Inv` is the streaming state of the data. -/
theorem final_repr (hP : Ok P) {s₀ : State} {h0 : HashValue w} {d : List Byte} (hd : R₀ P s₀ h0 d)
    {m : Mem} {rf : Nat} (hrf : rf = 0 → cnt s₀ + len s₀ = 0)
    (h : ReprR P h0 m (stA s₀) (d ++ D s₀ (len s₀)) rf) :
    Spec.Blake2.Repr P h0 m (stA s₀) (d ++ D s₀ (len s₀)) := by
  rcases Nat.eq_zero_or_pos rf with h0' | h0'
  · subst h0'
    have := hrf rfl
    obtain hl : (d ++ D s₀ (len s₀)).length = 0 := by rw [R₀.length hd _]; omega_using [this]
    rw [repr_iff P hP.pos, hl]
    exact h
  · exact repr_of_reprR P hP.pos h h0'

theorem end_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {s : State} (h : End P s₀ s) :
    WP isa (updateEnd (w := w)) s fun s' => abiPreserved s₀ s' ∧ (updateArm P).post s₀ s' := by
  obtain ⟨hC, h8, hrep⟩ := h
  obtain hL := len_lt s₀
  obtain ha₁ := a₁_le (w := w) s₀
  have hpos := hP.pos
  have hl := hP.len
  obtain hB : blockBytes w ≤ 128 := by rcases hP.bb with h | h <;> omega_using [h]
  unfold updateEnd
  refine WP.seq (wp_cmp (op2_imm (by decide)) fun s₁ f₁ z₁ => WP.block_nil ?_)
  obtain hz : isa.eval .eq s₁ = some (decide ((len s₀ - a₁ w s₀) = 0)) := by
    show VG.Arm.eval .eq s₁ = _
    rw [eval_eq, z₁, hC.r7, cmp0 (by omega_using [hL])]
  obtain hC₁ := hC.of_gpr (fun r _ => by rw [f₁.gpr]) f₁.mem f₁.rd f₁.wr f₁.sp
  -- Every byte of data is consumed.
  refine WP.seq (WP.mono (Q := fun (t : State) => ∃ rf, (rf = 0 → cnt s₀ + len s₀ = 0) ∧ Inv P s₀ (len s₀) rf t)
    ?_ fun t ⟨rf, hrf, hIt⟩ => ?_)
  · refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      obtain hk : k₂ w s₀ = 0 := by simp [k₂, hb]
      obtain e2 : r₂ w s₀ = r₀ w s₀ + a₁ w s₀ := by simp [r₂, hb]
      obtain ea : a₁ w s₀ = len s₀ := by omega_using [ha₁, hb]
      refine WP.block_nil ⟨r₂ w s₀, fun h0 => ?_, ?_⟩
      · rw [e2] at h0
        obtain hr0 : r₀ w s₀ = 0 := by omega_using [h0]
        have : cnt s₀ = 0 := by
          by_contra hc; have := bufLen_pos (w := w) hc; simp only [r₀] at hr0; omega_using [hr0, this]
        omega_using [ea, h0, this]
      · rw [← ea]
        exact
          { hC₁ with
            r8 := by rw [f₁.gpr]; exact h8
            repr := fun h0 d hd => by
              rw [f₁.mem]; have := hrep h0 d hd; rwa [hk, Nat.mul_zero, Nat.add_zero] at this }
    · simp only [decide_eq_false_iff_not] at hb
      obtain e2 : r₂ w s₀ = 0 := by simp [r₂, hb]
      obtain ek : blockBytes w * k₂ w s₀ = (len s₀ - a₁ w s₀) - (((len s₀ - a₁ w s₀) - 1) % blockBytes w + 1) := by
        rw [rem_eq _]; simp [k₂, hb]
      obtain hrem : ((len s₀ - a₁ w s₀) - 1) % blockBytes w < blockBytes w := Nat.mod_lt _ hpos
      refine WP.seq (wp_sub (op2_imm (by decide)) fun s₂ u₂ => wp_and (op2_imm hP.encB1) fun s₃ u₃ =>
        wp_add (op2_imm (by decide)) fun s₄ u₄ => wp_sub (op2_reg _ _) fun s₅ u₅ =>
        wp_add (op2_reg _ _) fun s₆ u₆ => wp_sub (op2_reg _ _) fun s₇ u₇ =>
        wp_adds (op2_reg _ _) fun s₈ u₈ c₈ => wp_adc (op2_imm (by decide)) fun s₉ u₉ _ => WP.block_nil ?_)
      obtain h4 : s₄.gpr .r11 = BitVec.ofNat 32 (((len s₀ - a₁ w s₀) - 1) % blockBytes w + 1) := by
        rw [u₄.gpr, u₃.gpr, u₂.gpr, f₁.gpr, hC.r7, bufLen_lo hP hb]
        simp only [bufLen, hb, ite_false]
      obtain h11 : s₉.gpr .r11 = BitVec.ofNat 32 (((len s₀ - a₁ w s₀) - 1) % blockBytes w + 1) := by
        rw [u₉.other .r11 (by decide), u₈.other .r11 (by decide), u₇.other .r11 (by decide),
          u₆.other .r11 (by decide), u₅.other .r11 (by decide), h4]
      obtain hrem' : a₁ w s₀ + blockBytes w * k₂ w s₀ + (((len s₀ - a₁ w s₀) - 1) % blockBytes w + 1) =
          len s₀ := by
        have := Nat.mod_le ((len s₀ - a₁ w s₀) - 1) (blockBytes w)
        rw [ek]; omega_using [hb, this]
      obtain h12 : s₅.gpr .r12 = BitVec.ofNat 32 (blockBytes w * k₂ w s₀) := by
        rw [u₅.gpr, h4, u₄.other .r7 (by decide), u₃.other .r7 (by decide), u₂.other .r7 (by decide), f₁.gpr,
          hC.r7, sub_ofNat (by have := Nat.mod_le ((len s₀ - a₁ w s₀) - 1) (blockBytes w); omega_using [hrem']), ek]
      obtain hk := k₂_le (w := w) s₀
      obtain hBk : blockBytes w * k₂ w s₀ < 2 ^ 32 := by omega_using [hL, hk]
      obtain g₉ : ∀ x, x ≠ .r11 → x ≠ .r12 → x ≠ .r6 → x ≠ .r7 → x ≠ .r9 → x ≠ .r10 → s₉.gpr x = s.gpr x :=
        fun x h1 h2 h3 h4 h5 h6 => by
          rw [u₉.other x h6, u₈.other x h5, u₇.other x h4, u₆.other x h3, u₅.other x h2, u₄.other x h1,
            u₃.other x h1, u₂.other x h1, f₁.gpr]
      obtain h6 : s₉.gpr .r6 = dp s₀ + BitVec.ofNat 32 (a₁ w s₀ + blockBytes w * k₂ w s₀) := by
        rw [u₉.other .r6 (by decide), u₈.other .r6 (by decide), u₇.other .r6 (by decide), u₆.gpr, h12,
          u₅.other .r6 (by decide), u₄.other .r6 (by decide), u₃.other .r6 (by decide),
          u₂.other .r6 (by decide), f₁.gpr, hC.r6, BitVec.add_assoc, ← BitVec.ofNat_add]
      obtain h7 : s₉.gpr .r7 = BitVec.ofNat 32 (len s₀ - (a₁ w s₀ + blockBytes w * k₂ w s₀)) := by
        rw [u₉.other .r7 (by decide), u₈.other .r7 (by decide), u₇.gpr, u₆.other .r7 (by decide),
          u₆.other .r12 (by decide), h12, u₅.other .r7 (by decide), u₄.other .r7 (by decide),
          u₃.other .r7 (by decide), u₂.other .r7 (by decide), f₁.gpr, hC.r7, sub_ofNat (by omega_using [hk]), Nat.sub_sub]
      obtain hcn : s₉.gpr .r10 ++ s₉.gpr .r9 = BitVec.ofNat 64 (cnt s₀ + (a₁ w s₀ + blockBytes w * k₂ w s₀)) := by
        rw [u₉.gpr, u₉.other .r9 (by decide), u₈.gpr, u₈.other .r10 (by decide), c₈, u₇.other .r9 (by decide),
          u₇.other .r10 (by decide), u₇.other .r12 (by decide), u₆.other .r9 (by decide),
          u₆.other .r10 (by decide), u₆.other .r12 (by decide), h12, u₅.other .r9 (by decide),
          u₅.other .r10 (by decide), u₄.other .r9 (by decide), u₄.other .r10 (by decide),
          u₃.other .r9 (by decide), u₃.other .r10 (by decide), u₂.other .r9 (by decide),
          u₂.other .r10 (by decide), f₁.gpr, add64_ofNat hC.cn hBk, Nat.add_assoc]
      obtain hm₉ : s₉.mem = s.mem := by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, f₁.mem]
      obtain hI₉ : Inv P s₀ (a₁ w s₀ + blockBytes w * k₂ w s₀) 0 s₉ :=
        { c_le := hk
          rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, f₁.rd, hC.rd]
          wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, f₁.wr, hC.wr]
          sp := by rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, f₁.sp, hC.sp]
          r4 := by rw [g₉ .r4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hC.r4]
          r5 := by rw [g₉ .r5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hC.r5]
          r6 := h6
          r7 := h7
          cn := hcn
          frame := hm₉ ▸ hC.frame
          saved := hm₉ ▸ hC.saved
          r8 := by rw [g₉ .r8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h8, e2]
          repr := fun h0 d hd => by
            rw [hm₉]
            have := hrep h0 d hd
            rwa [e2] at this }
      refine WP.mono (copy_ok hP hp (by omega_using [hrem]) (by omega_using [hrem']) hI₉ h11)
        fun t ht => ⟨((len s₀ - a₁ w s₀) - 1) % blockBytes w + 1, fun h => by omega_using [h], ?_⟩
      rw [Nat.zero_add, hrem'] at ht
      exact ht
  · have := hp.scr_fit
    refine restore_ok hIt.r5 hp.scr_fit
      (fun d hd₁ hd₂ => ⟨scR s₀, by simp [hIt.rd, hIt.wr, hp.wr], contains_off _ (by omega_using [hd₂]) (by omega_using [])⟩) s₀.gpr
      hIt.saved fun s' hs hmem _ _ hsp => ⟨⟨preserved_of hs, by rw [hsp, hIt.sp]⟩, fun h0 d hr hc hlt => ?_⟩
    obtain hd : R₀ P s₀ h0 d := ⟨hr, hc, hlt⟩
    rw [hmem]
    exact final_repr hP hd hrf (hIt.repr h0 d hd)

/-! ## `update` -/

theorem correct (hP : Ok P) {name : String} {code : Prog isa} (hf : CalleeOk P code) {s₀ : State}
    (hp : Pre w s₀) :
    WP isa (update (w := w) name code) s₀ fun s' => abiPreserved s₀ s' ∧ (updateArm P).post s₀ s' :=
  WP.seq (WP.mono (pro_ok hP hp) fun _ h₁ => WP.seq (WP.mono (call₁_ok hP hf hp h₁) fun _ h₂ =>
    WP.seq (WP.mono (mid_ok hP hp h₂) fun _ h₃ => WP.seq (WP.mono (call₂_ok hP hf hp h₃) fun _ h₄ =>
      end_ok hP hp h₄))))

end VG.Proof.Blake2.Arm.Stream.Update

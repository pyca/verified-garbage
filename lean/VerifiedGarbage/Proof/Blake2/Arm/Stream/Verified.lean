import VerifiedGarbage.Proof.MdStream.Arm.Words
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Blake2.Arm.Contract
import VerifiedGarbage.Proof.Blake2.Scratch
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Impl.Blake2.Arm.Stream
import VerifiedGarbage.Proof.Rc2.Stream
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Spec.Blake2.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.Arm.Stream.Common`. -/
section

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
abbrev below (s : VG.Arm.State) : Region := ⟨State.addr s.sp - 16, 16⟩

/-- What the streaming functions need of the compression function they call:
that it is verified against `compressArm P` and makes no calls. -/
structure CalleeOk {w : Nat} (P : VG.Spec.Blake2.Params w) (code : Prog isa) : Prop where
  verified : Verified Arm.target code (compressArm P)
  noCalls : code.noCalls = true

/-- What a call leaves: the regions, the stack pointer, the callee-saved
registers but `lr`, and memory outside what it may write and the 16 bytes
below the stack pointer. -/
structure After (s : VG.Arm.State) (ws : List Region) (s' : VG.Arm.State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  cs : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame (ws ++ [VG.Proof.Blake2.Arm.Stream.below s]) s.mem s'.mem

theorem frame_app {ws ws' : List Region} {m m' : Mem} (h : Frame ws m m') : Frame (ws ++ ws') m m' :=
  h.sub fun r hr => ⟨r, List.mem_append_left _ hr, fun _ h => h⟩

/-! The argument registers are not changed by the call instruction. -/

@[simp] theorem ce0 (s : VG.Arm.State) : s.callEntry.gpr .r0 = s.gpr .r0 := State.callEntry_gpr s (by decide)
@[simp] theorem ce1 (s : VG.Arm.State) : s.callEntry.gpr .r1 = s.gpr .r1 := State.callEntry_gpr s (by decide)
@[simp] theorem ce2 (s : VG.Arm.State) : s.callEntry.gpr .r2 = s.gpr .r2 := State.callEntry_gpr s (by decide)

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
  have := VG.Proof.Blake2.Arm.Stream.addr_sub_add (i := 0) hk (Nat.zero_le _)
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
structure CallArgs (s : VG.Arm.State) (st scr blk : BitVec 32) (n : Nat) (t : BitVec 64) (last : BitVec 32) :
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
  w_st : (VG.Proof.Blake2.Arm.Stream.below s).Disjoint ⟨State.addr st, bufOff w⟩
  w_b : (VG.Proof.Blake2.Arm.Stream.below s).Disjoint ⟨State.addr blk, blockBytes w * n⟩
  w_sc : (VG.Proof.Blake2.Arm.Stream.below s).Disjoint ⟨State.addr scr, 512⟩
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

variable {P : VG.Spec.Blake2.Params w}

namespace CallArgs
variable {s : VG.Arm.State} {st scr blk : BitVec 32} {n : Nat} {t : BitVec 64} {last : BitVec 32}
  (h : VG.Proof.Blake2.Arm.Stream.CallArgs (w := w) s st scr blk n t last)
include h

theorem a0 : State.addr (s.sp - 16) = State.addr s.sp - 16 := VG.Proof.Blake2.Arm.Stream.addr_sub h.sp16
theorem a4 : State.addr (s.sp - 16 + 4) = State.addr s.sp - 16 + BitVec.ofNat 64 4 :=
  VG.Proof.Blake2.Arm.Stream.addr_sub_add h.sp16 (by decide)
theorem a8 : State.addr (s.sp - 16 + 4 + 4) = State.addr s.sp - 16 + BitVec.ofNat 64 8 := by
  rw [BitVec.add_assoc]; exact VG.Proof.Blake2.Arm.Stream.addr_sub_add (k := 16) (i := 8) h.sp16 (by decide)
theorem a12 : State.addr (s.sp - 16 + 4 + 4 + 4) = State.addr s.sp - 16 + BitVec.ofNat 64 12 := by
  rw [BitVec.add_assoc, BitVec.add_assoc]; exact VG.Proof.Blake2.Arm.Stream.addr_sub_add (k := 16) (i := 12) h.sp16 (by decide)

/-- The memory after the push. -/
theorem pmem : (pushed VG.Proof.Blake2.Arm.Stream.args4 s).mem =
    (((s.mem.writeW (State.addr s.sp - 16) (s.gpr .r3)).writeW (State.addr s.sp - 16 + BitVec.ofNat 64 4)
      (s.gpr .r11)).writeW (State.addr s.sp - 16 + BitVec.ofNat 64 8) last).writeW
      (State.addr s.sp - 16 + BitVec.ofNat 64 12) scr := by
  show storeWords s.mem (s.sp - BitVec.ofNat 32 (4 * args4.length))
    [s.gpr .r3, s.gpr .r11, s.gpr .r12, s.gpr .lr] = _
  rw [VG.Proof.Blake2.Arm.Stream.e16]
  show (((s.mem.writeW (State.addr (s.sp - 16)) _).writeW (State.addr (s.sp - 16 + 4)) _).writeW
    (State.addr (s.sp - 16 + 4 + 4)) _).writeW (State.addr (s.sp - 16 + 4 + 4 + 4)) _ = _
  rw [h.a0, h.a4, h.a8, h.a12, h.r12, h.lr]

omit h in
theorem psp : (pushed VG.Proof.Blake2.Arm.Stream.args4 s).sp = s.sp - 16 := by rw [pushed_sp, VG.Proof.Blake2.Arm.Stream.e16]

/-- The stack arguments, in a state whose stack pointer is that after the push. -/
theorem sa (T : VG.Arm.State) (ht : T.sp = s.sp - 16) (i : Nat) (hi : i < 4) :
    stackArgAddr T i = State.addr s.sp - 16 + BitVec.ofNat 64 (4 * i) := by
  simp only [stackArgAddr, ht]
  exact VG.Proof.Blake2.Arm.Stream.addr_sub_add (k := 16) h.sp16 (by omega_nat)

theorem sa0 (T : VG.Arm.State) (ht : T.sp = s.sp - 16) : stackArgAddr T 0 = State.addr s.sp - 16 := by
  rw [h.sa T ht 0 (by decide)]; exact BitVec.add_zero _

theorem arg0 (T : VG.Arm.State) (ht : T.sp = s.sp - 16) (hm : T.mem = (pushed VG.Proof.Blake2.Arm.Stream.args4 s).mem) :
    stackArg T 0 = s.gpr .r3 := by
  rw [stackArg, h.sa T ht 0 (by decide), hm, h.pmem,
    Mem.readW_writeW_sep (VG.Proof.Blake2.Arm.Stream.sep_off _ (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_sep (VG.Proof.Blake2.Arm.Stream.sep_off _ (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_sep (VG.Proof.Blake2.Arm.Stream.sep_off _ (by decide) (by decide) (by decide)) (by decide),
    show 4 * 0 = 0 from rfl, BitVec.add_zero, Mem.readW_writeW_self32]

theorem arg1 (T : VG.Arm.State) (ht : T.sp = s.sp - 16) (hm : T.mem = (pushed VG.Proof.Blake2.Arm.Stream.args4 s).mem) :
    stackArg T 1 = s.gpr .r11 := by
  rw [stackArg, h.sa T ht 1 (by decide), hm, h.pmem,
    Mem.readW_writeW_sep (VG.Proof.Blake2.Arm.Stream.sep_off _ (by decide) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_sep (VG.Proof.Blake2.Arm.Stream.sep_off _ (by decide) (by decide) (by decide)) (by decide),
    show 4 * 1 = 4 from rfl, Mem.readW_writeW_self32]

theorem arg2 (T : VG.Arm.State) (ht : T.sp = s.sp - 16) (hm : T.mem = (pushed VG.Proof.Blake2.Arm.Stream.args4 s).mem) :
    stackArg T 2 = last := by
  rw [stackArg, h.sa T ht 2 (by decide), hm, h.pmem,
    Mem.readW_writeW_sep (VG.Proof.Blake2.Arm.Stream.sep_off _ (by decide) (by decide) (by decide)) (by decide),
    show 4 * 2 = 8 from rfl, Mem.readW_writeW_self32]

theorem arg3 (T : VG.Arm.State) (ht : T.sp = s.sp - 16) (hm : T.mem = (pushed VG.Proof.Blake2.Arm.Stream.args4 s).mem) :
    stackArg T 3 = scr := by
  rw [stackArg, h.sa T ht 3 (by decide), hm, h.pmem, show 4 * 3 = 12 from rfl, Mem.readW_writeW_self32]

/-- The push writes only below the stack pointer. -/
theorem fP : Frame [VG.Proof.Blake2.Arm.Stream.below s] s.mem (pushed VG.Proof.Blake2.Arm.Stream.args4 s).mem := by
  rw [h.pmem]
  have hc : ∀ k, k + 4 ≤ 16 → (VG.Proof.Blake2.Arm.Stream.below s).Contains (State.addr s.sp - 16 + BitVec.ofNat 64 k) (32 / 8) := by
    intro k hk; exact VG.Proof.Blake2.Arm.Stream.contains_off _ (by omega_nat) (by decide)
  refine ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _
    ?_).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
  · simpa using hc 0 (by decide)
  · exact hc 4 (by decide)
  · exact hc 8 (by decide)
  · exact hc 12 (by decide)

omit h in
theorem vsp : ((pushed VG.Proof.Blake2.Arm.Stream.args4 s).callEntry.withRegions (VG.Proof.Blake2.Arm.Stream.CallArgs.rd w s.sp blk n) (VG.Proof.Blake2.Arm.Stream.CallArgs.wr w st scr)).sp = s.sp - 16 :=
  VG.Proof.Blake2.Arm.Stream.CallArgs.psp
omit h in
theorem vmem : ((pushed VG.Proof.Blake2.Arm.Stream.args4 s).callEntry.withRegions (VG.Proof.Blake2.Arm.Stream.CallArgs.rd w s.sp blk n) (VG.Proof.Blake2.Arm.Stream.CallArgs.wr w st scr)).mem =
    (pushed VG.Proof.Blake2.Arm.Stream.args4 s).mem := rfl

theorem hn' : (BitVec.ofNat 32 n).toNat = n := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h.hn

omit h in
theorem argsSub : Region.Sub ⟨State.addr s.sp - 16, 16⟩ (VG.Proof.Blake2.Arm.Stream.below s) := fun _ h => h

theorem pre : (compressArm P).pre ((pushed VG.Proof.Blake2.Arm.Stream.args4 s).callEntry.withRegions (VG.Proof.Blake2.Arm.Stream.CallArgs.rd w s.sp blk n) (VG.Proof.Blake2.Arm.Stream.CallArgs.wr w st scr)) := by
  simp only [compressArm, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, VG.Proof.Blake2.Arm.Stream.ce0, VG.Proof.Blake2.Arm.Stream.ce1, VG.Proof.Blake2.Arm.Stream.ce2,
    pushed_gpr, h.arg3 _ VG.Proof.Blake2.Arm.Stream.CallArgs.vsp VG.Proof.Blake2.Arm.Stream.CallArgs.vmem, h.sa0 _ VG.Proof.Blake2.Arm.Stream.CallArgs.vsp, h.r0, h.r1, h.r2, h.hn']
  refine ⟨trivial, trivial, h.st_sc, h.b_st, h.b_sc, h.w_st, h.w_sc, h.nst, h.nb, h.nsc, ?_⟩
  rw [VG.Proof.Blake2.Arm.Stream.CallArgs.vsp, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, Offset.toNat_sub_ofNat]
  have := h.sp16; have := s.sp.isLt; omega_nat

theorem cov : Covers (VG.Proof.Blake2.Arm.Stream.CallArgs.rd w s.sp blk n ++ VG.Proof.Blake2.Arm.Stream.CallArgs.wr w st scr) ((pushed VG.Proof.Blake2.Arm.Stream.args4 s).rd ++ (pushed VG.Proof.Blake2.Arm.Stream.args4 s).wr) := by
  intro x n' ⟨r, hr, hcn⟩
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rw [pushed_rd, pushed_wr, VG.Proof.Blake2.Arm.Stream.e16]
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

theorem covW : Covers (VG.Proof.Blake2.Arm.Stream.CallArgs.wr w st scr) (pushed VG.Proof.Blake2.Arm.Stream.args4 s).wr := by
  intro x n' hi
  obtain ⟨r', hr', hc'⟩ := h.cw x n' hi
  exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩

end CallArgs

/-- After a frame of `rs` around a call that keeps the regions and the stack
pointer. -/
theorem after_frame {s s₂ : VG.Arm.State} {rs : List Reg} {ws : List Region}
    (fP : Frame [VG.Proof.Blake2.Arm.Stream.below s] s.mem (pushed rs s).mem)
    (hrd : s₂.rd = (pushed rs s).rd) (hwr : s₂.wr = (pushed rs s).wr) (hsp : s₂.sp = (pushed rs s).sp)
    (hf : Frame ws (pushed rs s).mem s₂.mem)
    (hcs : ∀ r ∈ preserved, r ≠ .lr → s₂.gpr r = (pushed rs s).gpr r) :
    VG.Proof.Blake2.Arm.Stream.After s ws (popped .r3 (4 * rs.length) s₂) := by
  refine ⟨?_, ?_, ?_, fun r hr hl => ?_, ?_⟩
  · rw [popped_rd, hrd, pushed_rd]
  · rw [popped_wr, hwr, pushed_wr]; rfl
  · rw [popped_sp, hsp, pushed_sp]; exact BitVec.sub_add_cancel _ _
  · have hr3 : r ≠ .r3 := by rintro rfl; simp [preserved] at hr
    rw [popped_gpr hr3, hcs r hr hl, pushed_gpr]
  · rw [popped_mem]
    exact (VG.Proof.Blake2.Arm.Stream.frame_app (ws' := ws) fP |>.mono fun r hr => by
        simp only [List.mem_append, List.mem_singleton] at hr ⊢; grind).trans (VG.Proof.Blake2.Arm.Stream.frame_app (ws' := [VG.Proof.Blake2.Arm.Stream.below s]) hf)

variable {P : VG.Spec.Blake2.Params w}

/-- A call of the compression function, in its frame: the hash value at `st`
is updated with the `n` blocks at `blk`, the first with the counter `t`, as
the last ones if `last ≠ 0`. -/
theorem call_ok {name : String} {code : Prog isa} (hf : VG.Proof.Blake2.Arm.Stream.CalleeOk P code) {s : VG.Arm.State}
    {st scr blk : BitVec 32} {n : Nat} {t : BitVec 64} {last : BitVec 32}
    (h : VG.Proof.Blake2.Arm.Stream.CallArgs (w := w) s st scr blk n t last) {Q : VG.Arm.State → Prop}
    (hQ : ∀ s', VG.Proof.Blake2.Arm.Stream.After s [⟨State.addr st, bufOff w⟩, ⟨State.addr scr, 512⟩] s' →
      stateAt w s'.mem (State.addr st) =
        compressBlocks P (stateAt w s.mem (State.addr st)) s.mem (State.addr blk) n t.toNat
          (last != 0) → Q s') :
    WP isa (call name code) s Q := by
  have h16 := h.sp16
  refine WP.frame (rs := VG.Proof.Blake2.Arm.Stream.args4) (r := .r3) rfl (by show 16 ≤ s.sp.toNat; exact h16) (by decide) ?_
  refine WP.call (k := compressArm P) hf.verified.1 h.pre h.cov h.covW ?_ hf.noCalls
  intro s₂ hrd hwr hsp hfr hcs _ hpost
  simp only [compressArm, tArm, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, VG.Proof.Blake2.Arm.Stream.ce0, VG.Proof.Blake2.Arm.Stream.ce1,
    VG.Proof.Blake2.Arm.Stream.ce2, pushed_gpr, h.r0, h.r1, h.r2, h.hn', h.arg0 _ CallArgs.vsp CallArgs.vmem,
    h.arg1 _ CallArgs.vsp CallArgs.vmem, h.arg2 _ CallArgs.vsp CallArgs.vmem, h.t] at hpost
  refine hQ _ (VG.Proof.Blake2.Arm.Stream.after_frame h.fP hrd hwr hsp hfr hcs) ?_
  have hst : stateAt w (pushed VG.Proof.Blake2.Arm.Stream.args4 s).mem (State.addr st) = stateAt w s.mem (State.addr st) :=
    stateAt_congr fun i hi => h.fP.bytes (R := ⟨State.addr st, bufOff w⟩)
      (by simp only [List.mem_singleton]; rintro r rfl; exact h.w_st.symm)
      (by show bufOff w ≤ 2 ^ 64; have := h.nst; omega_nat) hi
  have hbl : compressBlocks P (stateAt w s.mem (State.addr st)) (pushed VG.Proof.Blake2.Arm.Stream.args4 s).mem (State.addr blk) n
      t.toNat (last != 0) =
      compressBlocks P (stateAt w s.mem (State.addr st)) s.mem (State.addr blk) n t.toNat
        (last != 0) :=
    compressBlocks_congr P fun j hj => h.fP.bytes (R := ⟨State.addr blk, blockBytes w * n⟩)
      (by simp only [List.mem_singleton]; rintro r rfl; exact h.w_b.symm)
      (by show blockBytes w * n ≤ 2 ^ 64; have := h.nb; omega_nat) hj
  rw [popped_mem, hpost, hst, hbl]

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
def countArm (s : VG.Arm.State) : BitVec 64 := s.gpr .r3 ++ s.gpr .r2

section
variable {w : Nat} (P : VG.Spec.Blake2.Params w)

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
    (State.addr (s.gpr .r0)) (keyBlock w (VG.Spec.Blake2.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat))
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
    VG.Proof.Blake2.countArm s = BitVec.ofNat 64 d.length → d.length + (stackArg s 1).toNat < 2 ^ 64 →
    Spec.Blake2.Repr P h0 s'.mem (State.addr (s.gpr .r0))
      (d ++ VG.Spec.Blake2.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
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
    VG.Proof.Blake2.countArm s = BitVec.ofNat 64 d.length →
    VG.Spec.Blake2.bytesAt s'.mem (State.addr (stackArg s 0)) (bufOff w) = finalHash P h0 d
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

variable {w : Nat} {P : VG.Spec.Blake2.Params w}

/-! ## Sizes -/

/-- The word sizes, and keys fitting a block. -/
structure Ok (P : VG.Spec.Blake2.Params w) : Prop where
  /-- A key fits in a block. -/
  max : P.maxBytes ≤ blockBytes w
  w : w = 64 ∨ w = 32

theorem Ok.bb (h : VG.Proof.Blake2.Arm.Stream.Ok P) : blockBytes w = 64 ∨ blockBytes w = 128 := by
  rcases h.w with rfl | rfl <;> decide

theorem Ok.pos (h : VG.Proof.Blake2.Arm.Stream.Ok P) : 0 < blockBytes w := by rcases h.bb with h | h <;> omega

/-- The sizes, all small. -/
theorem Ok.len (h : VG.Proof.Blake2.Arm.Stream.Ok P) : bufOff w + blockBytes w ≤ 192 ∧ bufOff w ≤ 64 ∧ 32 ≤ bufOff w ∧
    bufOff w % 4 = 0 ∧ 64 ≤ blockBytes w := by
  rcases h.w with rfl | rfl <;> decide

theorem Ok.lbb (h : VG.Proof.Blake2.Arm.Stream.Ok P) : 1 ≤ VG.Impl.Blake2.Arm.Stream.lbb w ∧ VG.Impl.Blake2.Arm.Stream.lbb w ≤ 31 ∧ 2 ^ VG.Impl.Blake2.Arm.Stream.lbb w = blockBytes w := by
  rcases h.w with rfl | rfl <;> decide

theorem N_eq : N w = bufOff w := rfl
theorem B_eq : B w = blockBytes w := rfl

theorem Ok.encB (h : VG.Proof.Blake2.Arm.Stream.Ok P) : encodable (BitVec.ofNat 32 (B w)) = true := by
  rcases h.w with rfl | rfl <;> decide
theorem Ok.encB1 (h : VG.Proof.Blake2.Arm.Stream.Ok P) : encodable (BitVec.ofNat 32 (B w - 1)) = true := by
  rcases h.w with rfl | rfl <;> decide
theorem Ok.encN (h : VG.Proof.Blake2.Arm.Stream.Ok P) : encodable (BitVec.ofNat 32 (N w)) = true := by
  rcases h.w with rfl | rfl <;> decide

/-! ## Instructions the MD streaming proofs do not cover -/

section
variable {is : List Instr} {s : VG.Arm.State} {Q : VG.Arm.State → Prop}

theorem Upd.adds (s : VG.Arm.State) (d : Reg) (x y v : BitVec 32) : Upd s ((addFlags s x y).setReg d v) d v :=
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

theorem op2_ror {s : VG.Arm.State} {r : Reg} {n : Nat} (h : 1 ≤ n ∧ n ≤ 31) :
    (Op2.shifted r .ror n).eval s = some ((s.gpr r).rotateRight n) := by
  simp [Op2.eval, h]

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
  · simp only [hc, decide_true, ite_true, VG.Proof.Blake2.Arm.Stream.toNat_append32, BitVec.toNat_add, BitVec.toNat_setWidth, e1]
    omega
  · simp only [hc, decide_false, Bool.false_eq_true, ite_false, VG.Proof.Blake2.Arm.Stream.toNat_append32, BitVec.toNat_add,
      BitVec.toNat_setWidth, e0]
    omega

/-- The low word of a 64-bit number. -/
def lo32 (x : Nat) : BitVec 32 := BitVec.ofNat 32 x
/-- The high word of a 64-bit number (below 2⁶⁴). -/
def hi32 (x : Nat) : BitVec 32 := BitVec.ofNat 32 (x / 2 ^ 32)

/-- Adding `y < 2³²` to a count `x` (modulo 2⁶⁴) in a register pair. -/
theorem add64_ofNat {lo hi : BitVec 32} {x y : Nat} (h : (hi ++ lo : BitVec 64) = BitVec.ofNat 64 x)
    (hy : y < 2 ^ 32) :
    ((hi + 0 + (if decide (2 ^ 32 ≤ lo.toNat + (BitVec.ofNat 32 y).toNat) = true then 1 else 0)) ++
      (lo + BitVec.ofNat 32 y) : BitVec 64) = BitVec.ofNat 64 (x + y) := by
  rw [VG.Proof.Blake2.Arm.Stream.add64, h, BitVec.ofNat_add]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- The low word of a count in a register pair. -/
theorem lo_of_pair {lo hi : BitVec 32} {x : Nat} (h : (hi ++ lo : BitVec 64) = BitVec.ofNat 64 x) :
    lo = BitVec.ofNat 32 x := by
  apply BitVec.eq_of_toNat_eq
  have e := congrArg BitVec.toNat h
  rw [VG.Proof.Blake2.Arm.Stream.toNat_append32, BitVec.toNat_ofNat] at e
  rw [BitVec.toNat_ofNat]
  have := lo.isLt; have := hi.isLt
  omega

/-- A count in a register pair is zero iff the OR of its words is. -/
theorem or_beq_zero {lo hi : BitVec 32} {x : Nat} (h : (hi ++ lo : BitVec 64) = BitVec.ofNat 64 x)
    (hx : x < 2 ^ 64) : ((lo ||| hi) - 0 == 0) = decide (x = 0) := by
  have e := congrArg BitVec.toNat h
  rw [VG.Proof.Blake2.Arm.Stream.toNat_append32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at e
  rw [show (lo ||| hi) - 0 = lo ||| hi from BitVec.sub_zero _]
  by_cases hx0 : x = 0
  · have h1 : lo = 0 := BitVec.eq_of_toNat_eq (by show lo.toNat = 0; omega)
    have h2 : hi = 0 := BitVec.eq_of_toNat_eq (by show hi.toNat = 0; omega)
    simp [h1, h2, hx0]
  · rw [decide_eq_false hx0, beq_eq_false_iff_ne]
    intro h0
    obtain ⟨h1, h2⟩ := BitVec.or_eq_zero_iff.mp h0
    rw [h1, h2] at e
    rw [BitVec.toNat_zero] at e
    omega

/-! ## The number of bytes in the buffer -/

/-- `x & (B - 1)`: the remainder modulo the block size. -/
theorem mask_mod (hP : VG.Proof.Blake2.Arm.Stream.Ok P) (x : BitVec 32) :
    x &&& BitVec.ofNat 32 (B w - 1) = BitVec.ofNat 32 (x.toNat % blockBytes w) := by
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  rcases hP.w with rfl | rfl
  · rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (B 64 - 1) % 2 ^ 32 = 2 ^ 7 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, show blockBytes 64 = 2 ^ 7 from rfl]
    omega
  · rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (B 32 - 1) % 2 ^ 32 = 2 ^ 6 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, show blockBytes 32 = 2 ^ 6 from rfl]
    omega

/-- `x >>> lbb`: division by the block size. -/
theorem shr_ofNat (hP : VG.Proof.Blake2.Arm.Stream.Ok P) {m : Nat} (h : m < 2 ^ 32) :
    BitVec.ofNat 32 m >>> VG.Impl.Blake2.Arm.Stream.lbb w = BitVec.ofNat 32 (m / blockBytes w) := by
  rw [MdStream.Arm.ofNat_shr h, hP.lbb.2.2]

/-- `((count - 1) mod B) + 1`, from the low word of the count. -/
theorem bufLen_lo (hP : VG.Proof.Blake2.Arm.Stream.Ok P) {x : Nat} (hx : x ≠ 0) :
    ((BitVec.ofNat 32 x - 1) &&& BitVec.ofNat 32 (B w - 1)) + 1 = BitVec.ofNat 32 (bufLen w x) := by
  have hd : blockBytes w ∣ 2 ^ 32 := by rcases hP.w with rfl | rfl <;> decide
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), VG.Proof.Blake2.Arm.Stream.mask_mod hP,
    BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ hd, ← BitVec.ofNat_add]
  simp only [bufLen, hx, ite_false]

/-- A pointer plus an offset that does not wrap. -/
theorem toNat_add_ofNat {p : BitVec 32} {k : Nat} (h : p.toNat + k < 2 ^ 32) :
    (p + BitVec.ofNat 32 k).toNat = p.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt h]

/-! ## Copying bytes into the buffer -/

/-- The copy loop's state after `j` of `k` bytes, from `s₀`: the bytes go from
`src` to `dst`. -/
structure CopyI (s₀ : VG.Arm.State) (dst : Addr) (src : BitVec 32) (r k j : Nat) (s : VG.Arm.State) : Prop where
  j_le : j ≤ k
  r6 : s.gpr .r6 = src + BitVec.ofNat 32 j
  r8 : s.gpr .r8 = BitVec.ofNat 32 (r + j)
  r11 : s.gpr .r11 = BitVec.ofNat 32 (k - j)
  other : ∀ x, x ≠ .r12 → x ≠ .r1 → x ≠ .r6 → x ≠ .r8 → x ≠ .r11 → s.gpr x = s₀.gpr x
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = VG.WriteBytes.writeBytes s₀.mem dst ((VG.Spec.Blake2.bytesAt s₀.mem (State.addr src) k).take j)

theorem setWidth_byte (b : BitVec 8) : (b.setWidth 32).setWidth 8 = b := by
  ext i hi; simp

theorem ne_iff (s : VG.Arm.State) {k : Nat} (h : s.z = (BitVec.ofNat 32 k == 0)) (hk : k < 2 ^ 32) :
    isa.eval .ne s = some (decide (k ≠ 0)) := by
  show VG.Arm.eval .ne s = _
  rw [eval_ne, h, ofNat_beq_zero hk]
  simp

theorem eq_iff (s : VG.Arm.State) {k : Nat} (h : s.z = (BitVec.ofNat 32 k == 0)) (hk : k < 2 ^ 32) :
    isa.eval .eq s = some (decide (k = 0)) := by
  show VG.Arm.eval .eq s = _
  rw [eval_eq, h, ofNat_beq_zero hk]

theorem contains_prefix (q : Addr) {j k : Nat} (h : j ≤ k) : (⟨q, k⟩ : Region).Contains q j := by
  simp [Region.Contains, h]

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (VG.Spec.Blake2.bytesAt m p n).length = n := by simp [VG.Spec.Blake2.bytesAt]

/-- The loop copying `k ≥ 1` bytes from `src` (at `r6`) to the buffer of the
state at `st` (in `r4`), from byte `r` on (in `r8`). -/
theorem copyLoop_ok {s₀ : VG.Arm.State} {st src : BitVec 32} {r k : Nat} (hN : bufOff w ≤ 64) (hk : 1 ≤ k)
    (hfit : st.toNat + bufOff w + r + k ≤ 2 ^ 32) (hsfit : src.toNat + k ≤ 2 ^ 32)
    (hr4 : s₀.gpr .r4 = st) (hr6 : s₀.gpr .r6 = src) (hr8 : s₀.gpr .r8 = BitVec.ofNat 32 r)
    (hr11 : s₀.gpr .r11 = BitVec.ofNat 32 k)
    (hsrc : ∀ i < k, InRegions (s₀.rd ++ s₀.wr) (State.addr src + BitVec.ofNat 64 i) 1)
    (hdst : ∀ i < k, InRegions s₀.wr (State.addr st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 i) 1)
    (hd : Region.Disjoint ⟨State.addr src, k⟩ ⟨State.addr st + BitVec.ofNat 64 (bufOff w + r), k⟩)
    {Q : VG.Arm.State → Prop}
    (hQ : ∀ s, VG.Proof.Blake2.Arm.Stream.CopyI s₀ (State.addr st + BitVec.ofNat 64 (bufOff w + r)) src r k k s → Q s) :
    WP isa (Impl.Blake2.Arm.Stream.copyLoop (w := w)) s₀ Q := by
  refine WP.loop (M := isa) (fun n (s : VG.Arm.State) => ∃ j, n = k - j ∧ j < k ∧
      VG.Proof.Blake2.Arm.Stream.CopyI s₀ (State.addr st + BitVec.ofNat 64 (bufOff w + r)) src r k j s) ?_ k s₀
    ⟨0, by omega, by omega, by omega, by simp [hr6], by rw [hr8, Nat.add_zero], by rw [hr11, Nat.sub_zero],
      fun _ _ _ _ _ _ => rfl, rfl, rfl, rfl, by rw [List.take_zero, VG.WriteBytes.writeBytes_nil]⟩
  rintro n s ⟨j, rfl, hj, h⟩
  -- The byte read.
  have hin : InRegions (s.rd ++ s.wr) (State.addr src + BitVec.ofNat 64 j) 1 := by
    rw [h.rd, h.wr]; exact hsrc j hj
  have hbyte : s.mem (State.addr src + BitVec.ofNat 64 j) = s₀.mem (State.addr src + BitVec.ofNat 64 j) := by
    rw [h.mem]
    exact (VG.WriteBytes.writeBytes_frame s₀.mem _ _ (VG.Proof.Blake2.Arm.Stream.contains_prefix (k := k) _ (by simp; omega))).bytes
      (R := ⟨State.addr src, k⟩) (by simpa using hd) (by show k ≤ 2 ^ 64; omega) hj
  -- The byte written.
  have hout : InRegions s.wr (State.addr st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 j) 1 := by
    rw [h.wr]; exact hdst j hj
  have hr4' : s.gpr .r4 = st := by
    rw [h.other .r4 (by decide) (by decide) (by decide) (by decide) (by decide), hr4]
  refine wp_ldrb (a := State.addr src + BitVec.ofNat 64 j) (by decide)
    (by rw [h.r6, BitVec.add_zero, addr_add (by omega)]) hin fun s₁ u₁ => ?_
  refine wp_add (op2_reg _ _) fun s₂ u₂ =>
    wp_strb (a := State.addr st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 j)
    (by simp only [VG.Proof.Blake2.Arm.Stream.N_eq]; omega) ?_ (by rw [u₂.wr, u₁.wr]; exact hout) fun s₃ g₃ => ?_
  · rw [u₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), hr4', h.r8, VG.Proof.Blake2.Arm.Stream.N_eq, BitVec.add_assoc,
      ← BitVec.ofNat_add, addr_add (by omega), Offset.add_add]
    congr 2; omega
  refine wp_add (op2_imm (by decide)) fun s₄ u₄ => wp_add (op2_imm (by decide)) fun s₅ u₅ =>
    wp_subs (op2_imm (by decide)) fun s₆ u₆ z₆ => WP.block_nil ?_
  have hr11' : s₆.gpr .r11 = BitVec.ofNat 32 (k - (j + 1)) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.r11, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega),
      Nat.sub_sub]
  have hI : VG.Proof.Blake2.Arm.Stream.CopyI s₀ (State.addr st + BitVec.ofNat 64 (bufOff w + r)) src r k (j + 1) s₆ := by
    refine ⟨by omega, ?_, ?_, hr11', fun x h1 h2 h3 h4 h5 => ?_, ?_, ?_, ?_, ?_⟩
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
    · have hj' : j < (VG.Spec.Blake2.bytesAt s₀.mem (State.addr src) k).length := by rw [VG.Proof.Blake2.Arm.Stream.bytesAt_length]; omega
      have hl : (List.take j (VG.Spec.Blake2.bytesAt s₀.mem (State.addr src) k)).length = j := by
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
      rw [u₆.mem, u₅.mem, u₄.mem, g₃.mem, u₂.mem, u₁.mem, u₂.other _ (by decide), u₁.gpr, hbyte, h.mem,
        List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some,
        VG.WriteBytes.writeBytes_snoc _ _ _ _ (by rw [hl]; omega), hl, VG.Proof.Blake2.Arm.Stream.setWidth_byte]
      congr 1
      simp [VG.Spec.Blake2.bytesAt]
  have hz : isa.eval .ne s₆ = some (decide (k - (j + 1) ≠ 0)) :=
    VG.Proof.Blake2.Arm.Stream.ne_iff s₆ (by rw [z₆, ← u₆.gpr, hr11']) (by omega)
  by_cases hjk : j + 1 = k
  · exact .inl ⟨by rw [hz]; simp; omega, hQ _ (hjk ▸ hI)⟩
  · exact .inr ⟨by rw [hz]; simp; omega, k - (j + 1), by omega, j + 1, rfl, by omega, hI⟩

/-! ## Zeroing the buffer -/

/-- The zeroing loop's state after `j` of `k` bytes, from `s₀`. -/
structure ZI (s₀ : VG.Arm.State) (q : Addr) (r k j : Nat) (s : VG.Arm.State) : Prop where
  j_le : j ≤ k
  r8 : s.gpr .r8 = BitVec.ofNat 32 (r + j)
  r11 : s.gpr .r11 = BitVec.ofNat 32 (k - j)
  other : ∀ x, x ≠ .r1 → x ≠ .r8 → x ≠ .r11 → s.gpr x = s₀.gpr x
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = VG.WriteBytes.writeBytes s₀.mem q (List.replicate j 0)

/-- The loop zeroing `k ≥ 1` bytes of the buffer of the state at `st` (in
`r4`), from byte `r` on (in `r8`), with `r12 = 0`. -/
theorem zeroLoop_ok {s₀ : VG.Arm.State} {st : BitVec 32} {r k : Nat} (hN : bufOff w ≤ 64) (hk : 1 ≤ k)
    (hfit : st.toNat + bufOff w + r + k ≤ 2 ^ 32)
    (hr4 : s₀.gpr .r4 = st) (hr8 : s₀.gpr .r8 = BitVec.ofNat 32 r) (hr11 : s₀.gpr .r11 = BitVec.ofNat 32 k)
    (hr12 : s₀.gpr .r12 = 0)
    (hdst : ∀ i < k, InRegions s₀.wr (State.addr st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 i) 1)
    {Q : VG.Arm.State → Prop}
    (hQ : ∀ s, VG.Proof.Blake2.Arm.Stream.ZI s₀ (State.addr st + BitVec.ofNat 64 (bufOff w + r)) r k k s → Q s) :
    WP isa (Impl.Blake2.Arm.Stream.zeroLoop (w := w)) s₀ Q := by
  refine WP.loop (M := isa) (fun n (s : VG.Arm.State) => ∃ j, n = k - j ∧ j < k ∧
      VG.Proof.Blake2.Arm.Stream.ZI s₀ (State.addr st + BitVec.ofNat 64 (bufOff w + r)) r k j s) ?_ k s₀
    ⟨0, by omega, by omega, by omega, by rw [hr8, Nat.add_zero], by rw [hr11, Nat.sub_zero],
      fun _ _ _ _ => rfl, rfl, rfl, rfl, by rw [List.replicate_zero, VG.WriteBytes.writeBytes_nil]⟩
  rintro n s ⟨j, rfl, hj, h⟩
  have hr4' : s.gpr .r4 = st := by rw [h.other .r4 (by decide) (by decide) (by decide), hr4]
  refine wp_add (op2_reg _ _) fun s₁ u₁ =>
    wp_strb (a := State.addr st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 j)
    (by simp only [VG.Proof.Blake2.Arm.Stream.N_eq]; omega) ?_ (by rw [u₁.wr, h.wr]; exact hdst j hj) fun s₂ g₂ => ?_
  · rw [u₁.gpr, hr4', h.r8, VG.Proof.Blake2.Arm.Stream.N_eq, BitVec.add_assoc, ← BitVec.ofNat_add, addr_add (by omega), Offset.add_add]
    congr 2; omega
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_subs (op2_imm (by decide)) fun s₄ u₄ z₄ =>
    WP.block_nil ?_
  have hr11' : s₄.gpr .r11 = BitVec.ofNat 32 (k - (j + 1)) := by
    rw [u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.r11,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), Nat.sub_sub]
  have hI : VG.Proof.Blake2.Arm.Stream.ZI s₀ (State.addr st + BitVec.ofNat 64 (bufOff w + r)) r k (j + 1) s₄ := by
    refine ⟨by omega, ?_, hr11', fun x h1 h2 h3 => ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.r8,
        show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add, Nat.add_assoc]
    · rw [u₄.other x h3, u₃.other x h2, g₂.gpr, u₁.other x h1, h.other x h1 h2 h3]
    · rw [u₄.rd, u₃.rd, g₂.rd, u₁.rd, h.rd]
    · rw [u₄.wr, u₃.wr, g₂.wr, u₁.wr, h.wr]
    · rw [u₄.sp, u₃.sp, g₂.sp, u₁.sp, h.sp]
    · rw [u₄.mem, u₃.mem, g₂.mem, u₁.mem, u₁.other _ (by decide),
        h.other .r12 (by decide) (by decide) (by decide), hr12, h.mem,
        List.replicate_succ', VG.WriteBytes.writeBytes_snoc _ _ _ _ (by simp; omega), List.length_replicate]
      rfl
  have hz : isa.eval .ne s₄ = some (decide (k - (j + 1) ≠ 0)) :=
    VG.Proof.Blake2.Arm.Stream.ne_iff s₄ (by rw [z₄, ← u₄.gpr, hr11']) (by omega)
  by_cases hjk : j + 1 = k
  · exact .inl ⟨by rw [hz]; simp; omega, hQ _ (hjk ▸ hI)⟩
  · exact .inr ⟨by rw [hz]; simp; omega, k - (j + 1), by omega, j + 1, rfl, by omega, hI⟩

/-! ## Saving and restoring the caller's registers -/

/-- The caller's registers `g` are saved in the scratch space at `b`. -/
abbrev Saved (b : Addr) (g : Reg → BitVec 32) (m : Mem) : Prop := Spill.Saved m b g saved

theorem saved_slots : Spill.Slots 512 548 saved := by decide

theorem saved_bound : ∀ p ∈ saved, 512 ≤ p.2 ∧ p.2 + 4 ≤ 548 := by decide

theorem saveMem_saved (m : Mem) (b : Addr) (g : Reg → BitVec 32) :
    VG.Proof.Blake2.Arm.Stream.Saved b g (MdStream.Arm.saveMem m b g saved) :=
  Spill.saveMem_saved b g m saved VG.Proof.Blake2.Arm.Stream.saved_slots

theorem saveMem_frame (m : Mem) (b : Addr) (g : Reg → BitVec 32) :
    Frame [⟨b, 576⟩] m (MdStream.Arm.saveMem m b g saved) :=
  Spill.saveMem_frame m b g (by decide) saved (by decide)

/-- Saving `r4`–`r11` and `lr` with the scratch pointer in `b`. -/
theorem save_ok {b : Reg} {rest : List Instr} {s : VG.Arm.State} {Q : VG.Arm.State → Prop}
    (hfit : (s.gpr b).toNat + 576 ≤ 2 ^ 32)
    (hin : ∀ d, 512 ≤ d → d + 4 ≤ 548 → InRegions s.wr (State.addr (s.gpr b) + BitVec.ofNat 64 d) 4)
    (k : ∀ s', s'.gpr = s.gpr → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = MdStream.Arm.saveMem s.mem (State.addr (s.gpr b)) s.gpr saved → WP isa (.block rest) s' Q) :
    WP isa (.block (save b ++ rest)) s Q :=
  Spill.save_slots_ok VG.Proof.Blake2.Arm.Stream.saved_slots (by omega) hin (k _ rfl rfl rfl rfl rfl)

/-- Restoring `r4`–`r11` and `lr` from the save area at `scratch` (in `r5`). -/
theorem restore_ok {s : VG.Arm.State} {scr : BitVec 32} (h5 : s.gpr .r5 = scr) (hfit : scr.toNat + 576 ≤ 2 ^ 32)
    (hin : ∀ d, 512 ≤ d → d + 4 ≤ 548 → InRegions (s.rd ++ s.wr) (State.addr scr + BitVec.ofNat 64 d) 4)
    (g : Reg → BitVec 32) (hsv : VG.Proof.Blake2.Arm.Stream.Saved (State.addr scr) g s.mem) {Q : VG.Arm.State → Prop}
    (k : ∀ s', (∀ p ∈ saved, s'.gpr p.1 = g p.1) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp → Q s') :
    WP isa (.block restore) s Q := by
  unfold restore
  rw [← List.append_nil (saved.map _)]
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => ?_
  have h3 : s₁.gpr .r3 = scr := by rw [u₁.gpr, h5]
  refine Spill.restore_slots_ok VG.Proof.Blake2.Arm.Stream.saved_slots (by decide) (g := g) (by rw [h3]; omega)
    (fun d h₁ h₂ => by rw [h3, u₁.rd, u₁.wr]; exact hin d h₁ h₂) (by rw [h3, u₁.mem]; exact hsv)
    fun s' ho _ hm hrd hwr hsp => WP.block_nil (k s' ho (hm.trans u₁.mem) (hrd.trans u₁.rd)
      (hwr.trans u₁.wr) (hsp.trans u₁.sp))

/-- The callee-saved registers are the caller's again once `restore` has run. -/
theorem preserved_of {s₀ s' : VG.Arm.State} (hsv : ∀ p ∈ saved, s'.gpr p.1 = s₀.gpr p.1) :
    ∀ r ∈ preserved, s'.gpr r = s₀.gpr r :=
  Spill.restored_of hsv (by decide)

/-! ## The streaming state -/

/-- `Repr` depends only on the bytes of the streaming state. -/
theorem repr_congr (hP : VG.Proof.Blake2.Arm.Stream.Ok P) {h0 : HashValue w} {mem mem' : Mem} {p : Addr} {d : List Byte}
    (hm : ∀ i < bufOff w + blockBytes w, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i))
    (h : Spec.Blake2.Repr P h0 mem p d) : Spec.Blake2.Repr P h0 mem' p d := by
  rw [repr_iff P hP.pos] at h ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, by rw [← h4]; exact stateAt_congr fun i hi => hm i (by omega), ?_⟩
  rw [← h5]
  refine bytesAt_congr fun i hi => ?_
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact hm _ (by omega)

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
    VG.Spec.Blake2.bytesAt (VG.WriteBytes.writeBytes m (p + BitVec.ofNat 64 r) xs) p (r + xs.length) = VG.Spec.Blake2.bytesAt m p r ++ xs := by
  simp only [VG.Spec.Blake2.bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro i hi
    have hi := List.mem_range.mp hi
    exact WriteBytes.writeBytes_before m p xs hi (by omega)
  · apply List.ext_getElem (by simp)
    intro j h₁ h₂
    simp only [List.getElem_map, List.getElem_range, Function.comp, VG.WriteBytes.writeBytes]
    have hj : j < xs.length := by simpa using h₁
    rw [show p + BitVec.ofNat 64 (r + j) - (p + BitVec.ofNat 64 r) = BitVec.ofNat 64 j from
      Offset.add_ofNat_add_sub p r j, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp [hj, List.getD_eq_getElem?_getD]

end Arm.Stream

end VG.Proof.Blake2

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.Arm.Stream.Update`. -/
section

/-!
# Streaming BLAKE2 on ARMv7: `update`

The functional correctness of `update`, for either word size and any correct
compression function (`CalleeOk`), piece by piece: the prologue, up to the
first call (`pro_ok`), the first call (`call₁_ok`), the code between the calls
(`mid_ok`), the second call (`call₂_ok`) and the end (`end_ok`). Each piece's
postcondition gives the registers the next one starts from as functions of the
arguments, which the constant-time proof (`CT.lean`) uses too.
-/

namespace VG.Proof.Blake2.Arm.Stream.Update

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Blake2.Arm.Stream (N B lbb saved save restore call copyLoop copy fill args updatePro
  updateMid updateEnd update)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsr wp_mov wp_add wp_sub wp_and wp_orr
  wp_subs wp_cmp wp_ldrSp ofNat_beq_zero sub_ofNat cmp0 eval_eq eval_ne)
open VG.WriteBytes (writeBytes writeBytes_before writeBytes_frame)
open VG.Proof.Blake2 (ReprR bufLen bufLen_le bufLen_le_self bufLen_pos repr_iff reprR_append reprR_flush
  reprR_blocks repr_of_reprR stateAt_congr bytesAt_congr bytesAt_add updateArm countArm compressBlocks_zero)

variable {w : Nat} {P : VG.Spec.Blake2.Params w}

/-! ## The precondition -/

section
variable (s₀ : VG.Arm.State)

abbrev st : BitVec 32 := s₀.gpr .r0
abbrev stA : Addr := State.addr (VG.Proof.Blake2.Arm.Stream.Update.st s₀)
abbrev dp : BitVec 32 := stackArg s₀ 0
abbrev dA : Addr := State.addr (VG.Proof.Blake2.Arm.Stream.Update.dp s₀)
abbrev len : Nat := (stackArg s₀ 1).toNat
abbrev scr : BitVec 32 := stackArg s₀ 2
abbrev scA : Addr := State.addr (VG.Proof.Blake2.Arm.Stream.Update.scr s₀)
abbrev cnt : Nat := (VG.Proof.Blake2.countArm s₀).toNat
abbrev stR (w : Nat) : Region := ⟨VG.Proof.Blake2.Arm.Stream.Update.stA s₀, bufOff w + blockBytes w⟩
abbrev dR : Region := ⟨VG.Proof.Blake2.Arm.Stream.Update.dA s₀, VG.Proof.Blake2.Arm.Stream.Update.len s₀⟩
abbrev scR : Region := ⟨VG.Proof.Blake2.Arm.Stream.Update.scA s₀, 576⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 12⟩
/-- The first `c` bytes of data. -/
abbrev D (c : Nat) : List Byte := VG.Spec.Blake2.bytesAt s₀.mem (VG.Proof.Blake2.Arm.Stream.Update.dA s₀) c

end

structure Pre (w : Nat) (s₀ : VG.Arm.State) : Prop where
  rd : s₀.rd = [VG.Proof.Blake2.Arm.Stream.Update.dR s₀, VG.Proof.Blake2.Arm.Stream.Update.argR s₀]
  wr : s₀.wr = [VG.Proof.Blake2.Arm.Stream.Update.stR s₀ w, VG.Proof.Blake2.Arm.Stream.Update.scR s₀]
  st_scr : (VG.Proof.Blake2.Arm.Stream.Update.stR s₀ w).Disjoint (VG.Proof.Blake2.Arm.Stream.Update.scR s₀)
  d_st : (VG.Proof.Blake2.Arm.Stream.Update.dR s₀).Disjoint (VG.Proof.Blake2.Arm.Stream.Update.stR s₀ w)
  d_scr : (VG.Proof.Blake2.Arm.Stream.Update.dR s₀).Disjoint (VG.Proof.Blake2.Arm.Stream.Update.scR s₀)
  a_st : (VG.Proof.Blake2.Arm.Stream.Update.argR s₀).Disjoint (VG.Proof.Blake2.Arm.Stream.Update.stR s₀ w)
  a_scr : (VG.Proof.Blake2.Arm.Stream.Update.argR s₀).Disjoint (VG.Proof.Blake2.Arm.Stream.Update.scR s₀)
  w_st : (VG.Proof.Blake2.Arm.Stream.below s₀).Disjoint (VG.Proof.Blake2.Arm.Stream.Update.stR s₀ w)
  w_d : (VG.Proof.Blake2.Arm.Stream.below s₀).Disjoint (VG.Proof.Blake2.Arm.Stream.Update.dR s₀)
  w_scr : (VG.Proof.Blake2.Arm.Stream.below s₀).Disjoint (VG.Proof.Blake2.Arm.Stream.Update.scR s₀)
  st_fit : (VG.Proof.Blake2.Arm.Stream.Update.st s₀).toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32
  d_fit : (VG.Proof.Blake2.Arm.Stream.Update.dp s₀).toNat + VG.Proof.Blake2.Arm.Stream.Update.len s₀ ≤ 2 ^ 32
  scr_fit : (VG.Proof.Blake2.Arm.Stream.Update.scr s₀).toNat + 576 ≤ 2 ^ 32
  sp16 : 16 ≤ s₀.sp.toNat
  sp_fit : s₀.sp.toNat + 12 ≤ 2 ^ 32

theorem pre_of {s₀ : VG.Arm.State} (h : (VG.Proof.Blake2.updateArm P).pre s₀) : VG.Proof.Blake2.Arm.Stream.Update.Pre w s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

theorem len_lt (s₀ : VG.Arm.State) : VG.Proof.Blake2.Arm.Stream.Update.len s₀ < 2 ^ 32 := (stackArg s₀ 1).isLt
theorem cnt_lt (s₀ : VG.Arm.State) : VG.Proof.Blake2.Arm.Stream.Update.cnt s₀ < 2 ^ 64 := (VG.Proof.Blake2.countArm s₀).isLt

/-- The data the initial state represents, from `h0`. -/
def R₀ (P : VG.Spec.Blake2.Params w) (s₀ : VG.Arm.State) (h0 : HashValue w) (d : List Byte) : Prop :=
  Spec.Blake2.Repr P h0 s₀.mem (VG.Proof.Blake2.Arm.Stream.Update.stA s₀) d ∧ VG.Proof.Blake2.countArm s₀ = BitVec.ofNat 64 d.length ∧
    d.length + VG.Proof.Blake2.Arm.Stream.Update.len s₀ < 2 ^ 64

theorem R₀.cnt_eq {s₀ : VG.Arm.State} {h0 : HashValue w} {d : List Byte} (h : VG.Proof.Blake2.Arm.Stream.Update.R₀ P s₀ h0 d) :
    VG.Proof.Blake2.Arm.Stream.Update.cnt s₀ = d.length := by
  rw [VG.Proof.Blake2.Arm.Stream.Update.cnt, h.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.2.2; omega)]

theorem R₀.length {s₀ : VG.Arm.State} {h0 : HashValue w} {d : List Byte} (h : VG.Proof.Blake2.Arm.Stream.Update.R₀ P s₀ h0 d) (c : Nat) :
    (d ++ VG.Proof.Blake2.Arm.Stream.Update.D s₀ c).length = VG.Proof.Blake2.Arm.Stream.Update.cnt s₀ + c := by
  rw [List.length_append, Arm.Stream.bytesAt_length, h.cnt_eq]

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (w : Nat) (s₀ : VG.Arm.State) (c : Nat) (s : VG.Arm.State) : Prop where
  c_le : c ≤ VG.Proof.Blake2.Arm.Stream.Update.len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r4 : s.gpr .r4 = VG.Proof.Blake2.Arm.Stream.Update.st s₀
  r5 : s.gpr .r5 = VG.Proof.Blake2.Arm.Stream.Update.scr s₀
  r6 : s.gpr .r6 = VG.Proof.Blake2.Arm.Stream.Update.dp s₀ + BitVec.ofNat 32 c
  r7 : s.gpr .r7 = BitVec.ofNat 32 (VG.Proof.Blake2.Arm.Stream.Update.len s₀ - c)
  cn : s.gpr .r10 ++ s.gpr .r9 = BitVec.ofNat 64 (VG.Proof.Blake2.Arm.Stream.Update.cnt s₀ + c)
  frame : Frame [VG.Proof.Blake2.Arm.Stream.Update.stR s₀ w, VG.Proof.Blake2.Arm.Stream.Update.scR s₀, VG.Proof.Blake2.Arm.Stream.below s₀] s₀.mem s.mem
  saved : VG.Proof.Blake2.Arm.Stream.Saved (VG.Proof.Blake2.Arm.Stream.Update.scA s₀) s₀.gpr s.mem

/-- The state represents the data followed by the first `c` bytes of data,
the last `r` of them in the buffer. -/
structure Inv (P : VG.Spec.Blake2.Params w) (s₀ : VG.Arm.State) (c r : Nat) (s : VG.Arm.State) : Prop extends VG.Proof.Blake2.Arm.Stream.Update.Common w s₀ c s where
  r8 : s.gpr .r8 = BitVec.ofNat 32 r
  repr : ∀ h0 d, VG.Proof.Blake2.Arm.Stream.Update.R₀ P s₀ h0 d → ReprR P h0 s.mem (VG.Proof.Blake2.Arm.Stream.Update.stA s₀) (d ++ VG.Proof.Blake2.Arm.Stream.Update.D s₀ c) r

/-- The registers `Common` is about. -/
abbrev commonRegs : List Reg := [.r4, .r5, .r6, .r7, .r9, .r10]

theorem notC {r : Reg} (hr : r ∈ VG.Proof.Blake2.Arm.Stream.Update.commonRegs) (x : Reg) (hx : x ∉ VG.Proof.Blake2.Arm.Stream.Update.commonRegs := by decide) : r ≠ x :=
  fun h => hx (h ▸ hr)

theorem Common.of_gpr {s₀ : VG.Arm.State} {c : Nat} {s s' : VG.Arm.State} (h : VG.Proof.Blake2.Arm.Stream.Update.Common w s₀ c s)
    (hg : ∀ r ∈ VG.Proof.Blake2.Arm.Stream.Update.commonRegs, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    VG.Proof.Blake2.Arm.Stream.Update.Common w s₀ c s' where
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

theorem Inv.of_gpr {s₀ : VG.Arm.State} {c r : Nat} {s s' : VG.Arm.State} (h : VG.Proof.Blake2.Arm.Stream.Update.Inv P s₀ c r s)
    (hg : ∀ r ∈ .r8 :: VG.Proof.Blake2.Arm.Stream.Update.commonRegs, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    VG.Proof.Blake2.Arm.Stream.Update.Inv P s₀ c r s' :=
  { h.toCommon.of_gpr (fun r hr => hg r (List.mem_cons_of_mem _ hr)) hm hrd hwr hsp with
    r8 := by rw [hg _ (by simp)]; exact h.r8
    repr := by rw [hm]; exact h.repr }

/-- `Inv` after an instruction writing a register it is not about. -/
theorem Inv.of_upd {s₀ : VG.Arm.State} {c r : Nat} {s s' : VG.Arm.State} (h : VG.Proof.Blake2.Arm.Stream.Update.Inv P s₀ c r s) {d : Reg} {v : BitVec 32}
    (u : Upd s s' d v) (hd : d ∉ .r8 :: VG.Proof.Blake2.Arm.Stream.Update.commonRegs := by decide) : VG.Proof.Blake2.Arm.Stream.Update.Inv P s₀ c r s' :=
  h.of_gpr (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem u.rd u.wr u.sp

theorem Inv.of_flags {s₀ : VG.Arm.State} {c r : Nat} {s s' : VG.Arm.State} (h : VG.Proof.Blake2.Arm.Stream.Update.Inv P s₀ c r s) (u : Fupd s s') :
    VG.Proof.Blake2.Arm.Stream.Update.Inv P s₀ c r s' :=
  h.of_gpr (fun r _ => by rw [u.gpr]) u.mem u.rd u.wr u.sp

/-- The data is unchanged. -/
theorem Common.data {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.Arm.Stream.Update.Pre w s₀) {c : Nat} {s : VG.Arm.State} (h : VG.Proof.Blake2.Arm.Stream.Update.Common w s₀ c s) {i : Nat}
    (hi : i < VG.Proof.Blake2.Arm.Stream.Update.len s₀) : s.mem (VG.Proof.Blake2.Arm.Stream.Update.dA s₀ + BitVec.ofNat 64 i) = s₀.mem (VG.Proof.Blake2.Arm.Stream.Update.dA s₀ + BitVec.ofNat 64 i) :=
  h.frame.bytes (R := VG.Proof.Blake2.Arm.Stream.Update.dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr, hp.w_d.symm⟩)
    (by show VG.Proof.Blake2.Arm.Stream.Update.len s₀ ≤ 2 ^ 64; have := VG.Proof.Blake2.Arm.Stream.Update.len_lt s₀; omega) hi

/-- Writes to the state, the compression function's scratch space and the
16 bytes below the stack pointer keep the saved registers. -/
theorem saved_frame {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.Arm.Stream.Update.Pre w s₀) {m m' : Mem} (h : VG.Proof.Blake2.Arm.Stream.Saved (VG.Proof.Blake2.Arm.Stream.Update.scA s₀) s₀.gpr m)
    (hf : Frame [VG.Proof.Blake2.Arm.Stream.Update.stR s₀ w, ⟨VG.Proof.Blake2.Arm.Stream.Update.scA s₀, 512⟩, VG.Proof.Blake2.Arm.Stream.below s₀] m m') : VG.Proof.Blake2.Arm.Stream.Saved (VG.Proof.Blake2.Arm.Stream.Update.scA s₀) s₀.gpr m' := by
  have := hp.scr_fit
  refine h.frame VG.Proof.Blake2.Arm.Stream.saved_slots hf fun r' hr' => ?_
  have e : Region.Sub ⟨VG.Proof.Blake2.Arm.Stream.Update.scA s₀ + BitVec.ofNat 64 512, 548 - 512⟩ (VG.Proof.Blake2.Arm.Stream.Update.scR s₀) := Offset.sub_base _ (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl
  · exact hp.st_scr.symm.sub_left e
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · exact hp.w_scr.symm.sub_left e

/-! ## The prologue -/

/-- The prologue, but for `bufLen` and what follows it. -/
abbrev prologue : List Instr :=
  [.ldrSp .r12 8] ++ save .r12 ++ [.mov .r4 (.reg .r0), .mov .r5 (.reg .r12), .ldrSp .r6 0, .ldrSp .r7 4,
    .mov .r9 (.reg .r2), .mov .r10 (.reg .r3)]

/-- The stack arguments, word by word. -/
theorem argAddr_eq {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.Arm.Stream.Update.Pre w s₀) {k : Nat} (hk : k < 3) :
    stackArgAddr s₀ k = stackArgAddr s₀ 0 + BitVec.ofNat 64 (4 * k) := by
  have := hp.sp_fit
  simp only [stackArgAddr]
  rw [addr_add (by omega)]
  simp

theorem arg_in {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.Arm.Stream.Update.Pre w s₀) {k : Nat} (hk : k < 3) :
    InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ k) 4 :=
  ⟨VG.Proof.Blake2.Arm.Stream.Update.argR s₀, by simp [hp.rd], by rw [VG.Proof.Blake2.Arm.Stream.Update.argAddr_eq hp hk]; exact VG.Proof.Blake2.Arm.Stream.contains_off _ (by omega) (by omega)⟩

theorem arg_sub {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.Arm.Stream.Update.Pre w s₀) {k : Nat} (hk : k < 3) :
    Region.Sub ⟨stackArgAddr s₀ k, 4⟩ (VG.Proof.Blake2.Arm.Stream.Update.argR s₀) := by
  rw [VG.Proof.Blake2.Arm.Stream.Update.argAddr_eq hp hk]; exact Offset.sub_base _ (by omega)

theorem prologue_ok {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.Arm.Stream.Update.Pre w s₀) :
    WP isa (.block VG.Proof.Blake2.Arm.Stream.Update.prologue) s₀ fun s => VG.Proof.Blake2.Arm.Stream.Update.Common w s₀ 0 s ∧
      ∀ i < bufOff w + blockBytes w, s.mem (VG.Proof.Blake2.Arm.Stream.Update.stA s₀ + BitVec.ofNat 64 i) = s₀.mem (VG.Proof.Blake2.Arm.Stream.Update.stA s₀ + BitVec.ofNat 64 i) := by
  have hsc := hp.scr_fit
  simp only [VG.Proof.Blake2.Arm.Stream.Update.prologue, List.cons_append, List.nil_append]
  refine wp_ldrSp (a := stackArgAddr s₀ 2) (by decide) rfl (VG.Proof.Blake2.Arm.Stream.Update.arg_in hp (by decide)) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = VG.Proof.Blake2.Arm.Stream.Update.scr s₀ := u₁.gpr
  refine VG.Proof.Blake2.Arm.Stream.save_ok (by rw [h12]; omega) (fun d hd₁ hd₂ => ⟨VG.Proof.Blake2.Arm.Stream.Update.scR s₀, by simp [u₁.wr, hp.wr],
    by rw [h12]; exact VG.Proof.Blake2.Arm.Stream.contains_off _ (by omega) (by omega)⟩) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  -- The save writes only the scratch space.
  have hframe : Frame [VG.Proof.Blake2.Arm.Stream.Update.scR s₀] s₀.mem s₂.mem := by
    rw [m₂, u₁.mem, h12]; exact VG.Proof.Blake2.Arm.Stream.saveMem_frame _ _ _
  have harg : ∀ k, k < 3 → s₂.mem.readW (stackArgAddr s₀ k) 32 = stackArg s₀ k := fun k hk =>
    hframe.readW (Region.contains_self _ _) (by simpa using (hp.a_scr.sub_left (VG.Proof.Blake2.Arm.Stream.Update.arg_sub hp hk))) (by decide)
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide)
    (by rw [u₄.sp, u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]; exact VG.Proof.Blake2.Arm.Stream.Update.arg_in hp (by decide)) fun s₅ u₅ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide)
    (by rw [u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]; exact VG.Proof.Blake2.Arm.Stream.Update.arg_in hp (by decide))
    fun s₆ u₆ => wp_mov (op2_reg _ _) fun s₇ u₇ => wp_mov (op2_reg _ _) fun s₈ u₈ => WP.block_nil ?_
  have mm : s₈.mem = s₂.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
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
    have h10 : s₈.gpr .r10 = s₀.gpr .r3 := by
      rw [u₈.gpr, u₇.other .r3 (by decide), u₆.other .r3 (by decide), u₅.other .r3 (by decide),
        u₄.other .r3 (by decide), u₃.other .r3 (by decide), g₂, u₁.other .r3 (by decide)]
    rw [h9, h10, Nat.add_zero (VG.Proof.Blake2.Arm.Stream.Update.cnt s₀), VG.Proof.Blake2.Arm.Stream.Update.cnt, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rfl
  · rw [mm]; exact hframe.mono (by simp)
  · intro p hp'
    rw [mm, m₂, u₁.mem, h12, VG.Proof.Blake2.Arm.Stream.saveMem_saved _ _ _ p hp', u₁.other _ (Ne.symm ?_)]
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
  · intro i hi
    rw [mm]
    exact hframe.bytes (R := VG.Proof.Blake2.Arm.Stream.Update.stR s₀ w) (by simpa using hp.st_scr)
      (by show bufOff w + blockBytes w ≤ 2 ^ 64; have := hp.st_fit; omega) hi

/-! ## The number of bytes in the buffer -/

theorem bufLen_ok (hP : VG.Proof.Blake2.Arm.Stream.Ok P) {s : VG.Arm.State} {x : Nat} (hx : x < 2 ^ 64)
    (hc : s.gpr .r10 ++ s.gpr .r9 = BitVec.ofNat 64 x) :
    WP isa (Impl.Blake2.Arm.Stream.bufLen (w := w)) s fun s' =>
      s'.gpr .r8 = BitVec.ofNat 32 (bufLen w x) ∧
      (∀ r, r ≠ .r8 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold Impl.Blake2.Arm.Stream.bufLen
  have h9 : s.gpr .r9 = BitVec.ofNat 32 x := VG.Proof.Blake2.Arm.Stream.lo_of_pair hc
  refine WP.seq (wp_sub (op2_imm (by decide)) fun s₁ u₁ => wp_and (op2_imm hP.encB1) fun s₂ u₂ =>
    wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_orr (op2_reg _ _) fun s₄ u₄ =>
    wp_cmp (op2_imm (by decide)) fun s₅ f₅ z₅ => WP.block_nil ?_)
  have g : ∀ r, r ≠ .r8 → r ≠ .r12 → s₅.gpr r = s.gpr r := fun r h1 h2 => by
    rw [f₅.gpr, u₄.other r h2, u₃.other r h1, u₂.other r h1, u₁.other r h1]
  have hm : s₅.mem = s.mem := by rw [f₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hrd : s₅.rd = s.rd := by rw [f₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have hwr : s₅.wr = s.wr := by rw [f₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have hsp : s₅.sp = s.sp := by rw [f₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  have hz : s₅.z = decide (x = 0) := by
    rw [z₅, u₄.gpr, u₃.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), u₁.other _ (by decide)]
    exact VG.Proof.Blake2.Arm.Stream.or_beq_zero hc hx
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
    exact VG.Proof.Blake2.Arm.Stream.bufLen_lo hP hb

theorem bufLen_inv (hP : VG.Proof.Blake2.Arm.Stream.Ok P) {s₀ : VG.Arm.State} {s : VG.Arm.State} (hC : VG.Proof.Blake2.Arm.Stream.Update.Common w s₀ 0 s)
    (hst : ∀ i < bufOff w + blockBytes w, s.mem (VG.Proof.Blake2.Arm.Stream.Update.stA s₀ + BitVec.ofNat 64 i) = s₀.mem (VG.Proof.Blake2.Arm.Stream.Update.stA s₀ + BitVec.ofNat 64 i)) :
    WP isa (Impl.Blake2.Arm.Stream.bufLen (w := w)) s (VG.Proof.Blake2.Arm.Stream.Update.Inv P s₀ 0 (bufLen w (VG.Proof.Blake2.Arm.Stream.Update.cnt s₀))) := by
  have hrepr : ∀ h0 d, VG.Proof.Blake2.Arm.Stream.Update.R₀ P s₀ h0 d →
      ReprR P h0 s.mem (VG.Proof.Blake2.Arm.Stream.Update.stA s₀) (d ++ VG.Proof.Blake2.Arm.Stream.Update.D s₀ 0) (bufLen w (VG.Proof.Blake2.Arm.Stream.Update.cnt s₀)) := by
    intro h0 d hd
    have e : VG.Proof.Blake2.Arm.Stream.Update.D s₀ 0 = [] := by simp [VG.Spec.Blake2.bytesAt]
    rw [e, List.append_nil, hd.cnt_eq, ← repr_iff P hP.pos]
    exact VG.Proof.Blake2.Arm.Stream.repr_congr hP hst hd.1
  refine WP.mono (VG.Proof.Blake2.Arm.Stream.Update.bufLen_ok hP (VG.Proof.Blake2.Arm.Stream.Update.cnt_lt s₀) hC.cn) fun s' ⟨h8, g, m, rd, wr, sp⟩ => ?_
  exact { hC.of_gpr (fun r hr => g r (VG.Proof.Blake2.Arm.Stream.Update.notC hr .r8) (VG.Proof.Blake2.Arm.Stream.Update.notC hr .r12)) m rd wr sp with
    r8 := h8, repr := by rw [m]; exact hrepr }

/-! ## Copying data into the buffer -/

/-- `copy`: copying `k` bytes of data (none if `k = 0`), from byte `c` on,
into the buffer, from byte `r` on. -/
theorem copy_ok (hP : VG.Proof.Blake2.Arm.Stream.Ok P) {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.Arm.Stream.Update.Pre w s₀) {c r k : Nat} (hrk : r + k ≤ blockBytes w)
    (hck : c + k ≤ VG.Proof.Blake2.Arm.Stream.Update.len s₀) {s : VG.Arm.State} (hI : VG.Proof.Blake2.Arm.Stream.Update.Inv P s₀ c r s) (h11 : s.gpr .r11 = BitVec.ofNat 32 k) :
    WP isa (copy (w := w)) s (VG.Proof.Blake2.Arm.Stream.Update.Inv P s₀ (c + k) (r + k)) := by
  have hl := hP.len
  have hL := VG.Proof.Blake2.Arm.Stream.Update.len_lt s₀
  have hst := hp.st_fit; have hdf := hp.d_fit
  unfold copy
  refine WP.seq (wp_sub (op2_reg _ _) fun s₁ u₁ => VG.Proof.Blake2.Arm.Stream.wp_adds (op2_reg _ _) fun s₂ u₂ c₂ =>
    VG.Proof.Blake2.Arm.Stream.wp_adc (op2_imm (by decide)) fun s₃ u₃ _ => wp_cmp (op2_imm (by decide)) fun s₄ f₄ z₄ =>
    WP.block_nil ?_)
  have g₄ : ∀ x, x ≠ .r7 → x ≠ .r9 → x ≠ .r10 → s₄.gpr x = s.gpr x := fun x h1 h2 h3 => by
    rw [f₄.gpr, u₃.other x h3, u₂.other x h2, u₁.other x h1]
  have h7 : s₄.gpr .r7 = BitVec.ofNat 32 (VG.Proof.Blake2.Arm.Stream.Update.len s₀ - (c + k)) := by
    rw [f₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hI.r7, h11, sub_ofNat (by omega),
      Nat.sub_sub]
  have hcn : s₄.gpr .r10 ++ s₄.gpr .r9 = BitVec.ofNat 64 (VG.Proof.Blake2.Arm.Stream.Update.cnt s₀ + (c + k)) := by
    rw [f₄.gpr, u₃.gpr, u₃.other .r9 (by decide), u₂.gpr, u₂.other .r10 (by decide), c₂,
      u₁.other .r9 (by decide), u₁.other .r10 (by decide), u₁.other .r11 (by decide), h11,
      VG.Proof.Blake2.Arm.Stream.add64_ofNat hI.cn (by omega), Nat.add_assoc]
  have hm₄ : s₄.mem = s.mem := by rw [f₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hrd₄ : s₄.rd = s.rd := by rw [f₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have hwr₄ : s₄.wr = s.wr := by rw [f₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have hsp₄ : s₄.sp = s.sp := by rw [f₄.sp, u₃.sp, u₂.sp, u₁.sp]
  have h4 : s₄.gpr .r4 = VG.Proof.Blake2.Arm.Stream.Update.st s₀ := by rw [g₄ _ (by decide) (by decide) (by decide), hI.r4]
  have h5 : s₄.gpr .r5 = VG.Proof.Blake2.Arm.Stream.Update.scr s₀ := by rw [g₄ _ (by decide) (by decide) (by decide), hI.r5]
  have h6 : s₄.gpr .r6 = VG.Proof.Blake2.Arm.Stream.Update.dp s₀ + BitVec.ofNat 32 c := by rw [g₄ _ (by decide) (by decide) (by decide), hI.r6]
  have h8 : s₄.gpr .r8 = BitVec.ofNat 32 r := by rw [g₄ _ (by decide) (by decide) (by decide), hI.r8]
  have h11' : s₄.gpr .r11 = BitVec.ofNat 32 k := by rw [g₄ _ (by decide) (by decide) (by decide), h11]
  have hz : isa.eval .eq s₄ = some (decide (k = 0)) := by
    show VG.Arm.eval .eq s₄ = _
    rw [eval_eq, z₄, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h11,
      cmp0 (by omega)]
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
    have hcl : c < VG.Proof.Blake2.Arm.Stream.Update.len s₀ := by omega
    have hsrc : ∀ i < k, InRegions (s₄.rd ++ s₄.wr)
        (State.addr (VG.Proof.Blake2.Arm.Stream.Update.dp s₀ + BitVec.ofNat 32 c) + BitVec.ofNat 64 i) 1 := fun i hi =>
      ⟨VG.Proof.Blake2.Arm.Stream.Update.dR s₀, by simp [hrd₄, hI.rd, hp.rd], by
        rw [addr_add (by omega), Offset.add_add]; exact VG.Proof.Blake2.Arm.Stream.contains_off _ (by omega) (by omega)⟩
    have hdst : ∀ i < k, InRegions s₄.wr (VG.Proof.Blake2.Arm.Stream.Update.stA s₀ + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 i) 1 :=
      fun i hi => ⟨VG.Proof.Blake2.Arm.Stream.Update.stR s₀ w, by simp [hwr₄, hI.wr, hp.wr], by
        rw [Offset.add_add]; exact VG.Proof.Blake2.Arm.Stream.contains_off _ (by omega) (by omega)⟩
    have hd : Region.Disjoint ⟨State.addr (VG.Proof.Blake2.Arm.Stream.Update.dp s₀ + BitVec.ofNat 32 c), k⟩
        ⟨VG.Proof.Blake2.Arm.Stream.Update.stA s₀ + BitVec.ofNat 64 (bufOff w + r), k⟩ := by
      rw [addr_add (by omega)]
      exact (hp.d_st.sub_left (Offset.sub_base _ (by omega))).sub_right (Offset.sub_base _ (by omega))
    refine VG.Proof.Blake2.Arm.Stream.copyLoop_ok (st := VG.Proof.Blake2.Arm.Stream.Update.st s₀) hl.2.1 (by omega) (by omega)
      (by rw [VG.Proof.Blake2.Arm.Stream.toNat_add_ofNat (by omega)]; omega) h4 h6 h8 h11' hsrc hdst hd fun s' h => ?_
    have hx : VG.Spec.Blake2.bytesAt s₄.mem (State.addr (VG.Proof.Blake2.Arm.Stream.Update.dp s₀ + BitVec.ofNat 32 c)) k =
        VG.Spec.Blake2.bytesAt s₀.mem (VG.Proof.Blake2.Arm.Stream.Update.dA s₀ + BitVec.ofNat 64 c) k := by
      rw [addr_add (by omega), hm₄]
      exact bytesAt_congr fun i hi => by rw [Offset.add_add]; exact hI.data hp (by omega)
    have hmem : s'.mem = VG.WriteBytes.writeBytes s.mem (VG.Proof.Blake2.Arm.Stream.Update.stA s₀ + BitVec.ofNat 64 (bufOff w + r))
        (VG.Spec.Blake2.bytesAt s₀.mem (VG.Proof.Blake2.Arm.Stream.Update.dA s₀ + BitVec.ofNat 64 c) k) := by
      rw [h.mem, List.take_of_length_le (by rw [VG.Proof.Blake2.Arm.Stream.bytesAt_length]), hx, hm₄]
    have hfw : Frame [VG.Proof.Blake2.Arm.Stream.Update.stR s₀ w] s.mem s'.mem := by
      rw [hmem]
      exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [VG.Proof.Blake2.Arm.Stream.bytesAt_length]; exact VG.Proof.Blake2.Arm.Stream.contains_off _ (by omega) (by omega))
    have g' : ∀ x, x ≠ .r12 → x ≠ .r1 → x ≠ .r6 → x ≠ .r8 → x ≠ .r11 → x ≠ .r7 → x ≠ .r9 → x ≠ .r10 →
        s'.gpr x = s.gpr x := fun x h1 h2 h3 h4 h5 h6 h7 h8 => by
      rw [h.other x h1 h2 h3 h4 h5, g₄ x h6 h7 h8]
    refine
      { c_le := by omega
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
        saved := VG.Proof.Blake2.Arm.Stream.Update.saved_frame hp hI.saved (hfw.mono (by simp))
        r8 := h.r8
        repr := fun h0 d hd => ?_ }
    have e : d ++ VG.Proof.Blake2.Arm.Stream.Update.D s₀ (c + k) = d ++ VG.Proof.Blake2.Arm.Stream.Update.D s₀ c ++ VG.Spec.Blake2.bytesAt s₀.mem (VG.Proof.Blake2.Arm.Stream.Update.dA s₀ + BitVec.ofNat 64 c) k := by
      rw [VG.Proof.Blake2.Arm.Stream.Update.D, VG.Proof.Blake2.bytesAt_add, List.append_assoc]
    rw [e]
    have := reprR_append P (hI.repr h0 d hd) (x := VG.Spec.Blake2.bytesAt s₀.mem (VG.Proof.Blake2.Arm.Stream.Update.dA s₀ + BitVec.ofNat 64 c) k)
      (mem' := s'.mem) (by rw [VG.Proof.Blake2.Arm.Stream.bytesAt_length]; exact hrk) ?_ ?_
    · rwa [VG.Proof.Blake2.Arm.Stream.bytesAt_length] at this
    · rw [hmem]
      exact stateAt_congr fun i hi => VG.WriteBytes.writeBytes_before _ _ _ (by omega) (by rw [VG.Proof.Blake2.Arm.Stream.bytesAt_length]; omega)
    · rw [hmem, ← Offset.add_add, VG.Proof.Blake2.Arm.Stream.bytesAt_writeBytes _ _ _ _ (by rw [VG.Proof.Blake2.Arm.Stream.bytesAt_length]; omega)]

/-- `fill`: copying `min(B - r, len - c)` bytes of data into the buffer. -/
theorem fill_ok (hP : VG.Proof.Blake2.Arm.Stream.Ok P) {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.Arm.Stream.Update.Pre w s₀) {c r : Nat} (hr : r ≤ blockBytes w) {s : VG.Arm.State}
    (hI : VG.Proof.Blake2.Arm.Stream.Update.Inv P s₀ c r s) :
    WP isa (VG.Impl.Blake2.Arm.Stream.fill (w := w)) s (VG.Proof.Blake2.Arm.Stream.Update.Inv P s₀ (c + min (blockBytes w - r) (VG.Proof.Blake2.Arm.Stream.Update.len s₀ - c))
      (r + min (blockBytes w - r) (VG.Proof.Blake2.Arm.Stream.Update.len s₀ - c))) := by
  have hL := VG.Proof.Blake2.Arm.Stream.Update.len_lt s₀
  have hc := hI.c_le
  have hpos := hP.pos
  have hl := hP.len
  have hbb : blockBytes w ≤ 128 := by rcases hP.bb with h | h <;> omega
  obtain ⟨a, ha⟩ : ∃ a, a = min (blockBytes w - r) (VG.Proof.Blake2.Arm.Stream.Update.len s₀ - c) := ⟨_, rfl⟩
  rw [← ha]
  have hlbb : 1 ≤ VG.Impl.Blake2.Arm.Stream.lbb w ∧ VG.Impl.Blake2.Arm.Stream.lbb w ≤ 31 := ⟨hP.lbb.1, hP.lbb.2.1⟩
  unfold VG.Impl.Blake2.Arm.Stream.fill
  refine WP.seq (wp_mov (op2_imm hP.encB) fun s₁ u₁ => wp_sub (op2_reg _ _) fun s₂ u₂ =>
    wp_mov (op2_lsr hlbb) fun s₃ u₃ => wp_cmp (op2_imm (by decide)) fun s₄ f₄ z₄ => WP.block_nil ?_)
  have hI₄ : VG.Proof.Blake2.Arm.Stream.Update.Inv P s₀ c r s₄ := (((hI.of_upd u₁).of_upd u₂).of_upd u₃).of_flags f₄
  have h11 : s₄.gpr .r11 = BitVec.ofNat 32 (blockBytes w - r) := by
    rw [f₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.gpr, u₁.other _ (by decide), hI.r8, VG.Proof.Blake2.Arm.Stream.B_eq,
      sub_ofNat hr]
  have hz : isa.eval .eq s₄ = some (decide ((VG.Proof.Blake2.Arm.Stream.Update.len s₀ - c) / blockBytes w = 0)) := by
    show VG.Arm.eval .eq s₄ = _
    rw [eval_eq, z₄, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hI.r7,
      VG.Proof.Blake2.Arm.Stream.shr_ofNat hP (by omega), cmp0 (by have := Nat.div_le_self (VG.Proof.Blake2.Arm.Stream.Update.len s₀ - c) (blockBytes w); omega)]
  refine WP.seq (WP.mono (Q := fun (t : VG.Arm.State) => VG.Proof.Blake2.Arm.Stream.Update.Inv P s₀ c r t ∧ t.gpr .r11 = BitVec.ofNat 32 a) ?_
    fun (t : VG.Arm.State) (ht : VG.Proof.Blake2.Arm.Stream.Update.Inv P s₀ c r t ∧ t.gpr .r11 = BitVec.ofNat 32 a) =>
      VG.Proof.Blake2.Arm.Stream.Update.copy_ok hP hp (by omega) (by omega) ht.1 ht.2)
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    have hlt : VG.Proof.Blake2.Arm.Stream.Update.len s₀ - c < blockBytes w := by
      refine Nat.lt_of_not_le fun h' => ?_
      have := Nat.div_pos h' hpos
      omega
    refine WP.seq (wp_add (op2_reg _ _) fun s₅ u₅ => wp_mov (op2_lsr hlbb) fun s₆ u₆ =>
      wp_cmp (op2_imm (by decide)) fun s₇ f₇ z₇ => WP.block_nil ?_)
    have hI₇ : VG.Proof.Blake2.Arm.Stream.Update.Inv P s₀ c r s₇ := ((hI₄.of_upd u₅).of_upd u₆).of_flags f₇
    have hz₇ : isa.eval .eq s₇ = some (decide ((VG.Proof.Blake2.Arm.Stream.Update.len s₀ - c + r) / blockBytes w = 0)) := by
      show VG.Arm.eval .eq s₇ = _
      rw [eval_eq, z₇, u₆.gpr, u₅.gpr, hI₄.r7, hI₄.r8, ← BitVec.ofNat_add, VG.Proof.Blake2.Arm.Stream.shr_ofNat hP (by omega),
        cmp0 (by have := Nat.div_le_self (VG.Proof.Blake2.Arm.Stream.Update.len s₀ - c + r) (blockBytes w); omega)]
    refine WP.ite _ hz₇ (fun hb' => ?_) (fun hb' => ?_)
    · simp only [decide_eq_true_eq] at hb'
      have hlt' : VG.Proof.Blake2.Arm.Stream.Update.len s₀ - c + r < blockBytes w := by
        refine Nat.lt_of_not_le fun h' => ?_
        have := Nat.div_pos h' hpos
        omega
      refine wp_mov (op2_reg _ _) fun s₈ u₈ => WP.block_nil ⟨hI₇.of_upd u₈, ?_⟩
      rw [u₈.gpr, hI₇.r7, ha]
      congr 1; omega
    · simp only [decide_eq_false_iff_not] at hb'
      have hge : blockBytes w ≤ VG.Proof.Blake2.Arm.Stream.Update.len s₀ - c + r := by
        refine Nat.le_of_not_lt fun h' => hb' (Nat.div_eq_of_lt h')
      refine WP.block_nil ⟨hI₇, ?_⟩
      rw [f₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), h11, ha]
      congr 1; omega
  · simp only [decide_eq_false_iff_not] at hb
    have hge : blockBytes w ≤ VG.Proof.Blake2.Arm.Stream.Update.len s₀ - c := by
      refine Nat.le_of_not_lt fun h' => hb (Nat.div_eq_of_lt h')
    refine WP.block_nil ⟨hI₄, ?_⟩
    rw [h11, ha]
    congr 1; omega

/-! ## Up to the first call -/

section
variable (w : Nat) (s₀ : VG.Arm.State)

/-- The bytes in the buffer on entry. -/
abbrev r₀ : Nat := bufLen w (VG.Proof.Blake2.Arm.Stream.Update.cnt s₀)
/-- The bytes of data copied into a non-empty buffer. -/
def a₁ : Nat := if VG.Proof.Blake2.Arm.Stream.Update.r₀ w s₀ = 0 then 0 else min (blockBytes w - VG.Proof.Blake2.Arm.Stream.Update.r₀ w s₀) (VG.Proof.Blake2.Arm.Stream.Update.len s₀)
/-- The blocks the first call compresses: the buffer, if it is not empty and
more data follows (it is then full). -/
def n₁ : Nat := if VG.Proof.Blake2.Arm.Stream.Update.len s₀ - VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀ ≠ 0 ∧ VG.Proof.Blake2.Arm.Stream.Update.r₀ w s₀ + VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀ ≠ 0 then 1 else 0

end

theorem a₁_le (s₀ : VG.Arm.State) : VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀ ≤ VG.Proof.Blake2.Arm.Stream.Update.len s₀ := by
  unfold VG.Proof.Blake2.Arm.Stream.Update.a₁; split <;> omega

theorem a₁_eq (s₀ : VG.Arm.State) (h : VG.Proof.Blake2.Arm.Stream.Update.r₀ w s₀ ≠ 0) : VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀ = min (blockBytes w - VG.Proof.Blake2.Arm.Stream.Update.r₀ w s₀) (VG.Proof.Blake2.Arm.Stream.Update.len s₀) := by
  simp only [VG.Proof.Blake2.Arm.Stream.Update.a₁, h, ite_false]

theorem a₁_zero (s₀ : VG.Arm.State) (h : VG.Proof.Blake2.Arm.Stream.Update.r₀ w s₀ = 0) : VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀ = 0 := by
  simp only [VG.Proof.Blake2.Arm.Stream.Update.a₁, h, ite_true]

theorem r₁_le (hP : VG.Proof.Blake2.Arm.Stream.Ok P) (s₀ : VG.Arm.State) : VG.Proof.Blake2.Arm.Stream.Update.r₀ w s₀ + VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀ ≤ blockBytes w := by
  have hr : VG.Proof.Blake2.Arm.Stream.Update.r₀ w s₀ ≤ blockBytes w := bufLen_le hP.pos _
  by_cases h0 : VG.Proof.Blake2.Arm.Stream.Update.r₀ w s₀ = 0
  · rw [VG.Proof.Blake2.Arm.Stream.Update.a₁_zero s₀ h0]; omega
  · rw [VG.Proof.Blake2.Arm.Stream.Update.a₁_eq s₀ h0]; omega

/-- The first call compresses the buffer only when it is full. -/
theorem n₁_full (hP : VG.Proof.Blake2.Arm.Stream.Ok P) (s₀ : VG.Arm.State) (h : VG.Proof.Blake2.Arm.Stream.Update.n₁ w s₀ = 1) : VG.Proof.Blake2.Arm.Stream.Update.r₀ w s₀ + VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀ = blockBytes w := by
  have hr : VG.Proof.Blake2.Arm.Stream.Update.r₀ w s₀ ≤ blockBytes w := bufLen_le hP.pos _
  simp only [VG.Proof.Blake2.Arm.Stream.Update.n₁] at h
  split at h
  · rename_i hc
    by_cases h0 : VG.Proof.Blake2.Arm.Stream.Update.r₀ w s₀ = 0
    · rw [VG.Proof.Blake2.Arm.Stream.Update.a₁_zero s₀ h0] at hc; omega
    · rw [VG.Proof.Blake2.Arm.Stream.Update.a₁_eq s₀ h0] at hc ⊢; omega
  · cases h

theorem n₁_le (s₀ : VG.Arm.State) : VG.Proof.Blake2.Arm.Stream.Update.n₁ w s₀ ≤ 1 := by unfold VG.Proof.Blake2.Arm.Stream.Update.n₁; split <;> omega

theorem head_ok (hP : VG.Proof.Blake2.Arm.Stream.Ok P) {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.Arm.Stream.Update.Pre w s₀) {s : VG.Arm.State} (hI : VG.Proof.Blake2.Arm.Stream.Update.Inv P s₀ 0 (VG.Proof.Blake2.Arm.Stream.Update.r₀ w s₀) s)
    {rest : Prog isa} {Q : VG.Arm.State → Prop}
    (k : ∀ t, VG.Proof.Blake2.Arm.Stream.Update.Inv P s₀ (VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) (VG.Proof.Blake2.Arm.Stream.Update.r₀ w s₀ + VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) t → WP isa rest t Q) :
    WP isa (.seq (.block [.cmp .r8 (.imm 0)]) (.seq (.ite .eq (.block []) (VG.Impl.Blake2.Arm.Stream.fill (w := w))) rest)) s Q := by
  have hr : VG.Proof.Blake2.Arm.Stream.Update.r₀ w s₀ ≤ blockBytes w := bufLen_le hP.pos _
  have hB : blockBytes w ≤ 128 := by rcases hP.bb with h | h <;> omega
  refine WP.seq (wp_cmp (op2_imm (by decide)) fun s₁ f₁ z₁ => WP.block_nil ?_)
  have hI₁ := hI.of_flags f₁
  have hz : isa.eval .eq s₁ = some (decide (VG.Proof.Blake2.Arm.Stream.Update.r₀ w s₀ = 0)) := by
    show VG.Arm.eval .eq s₁ = _
    rw [eval_eq, z₁, hI.r8, cmp0 (by omega)]
  refine WP.seq (WP.mono (WP.ite _ hz (fun hb => ?_) (fun hb => ?_)) k)
  · simp only [decide_eq_true_eq] at hb
    rw [VG.Proof.Blake2.Arm.Stream.Update.a₁_zero s₀ hb, Nat.add_zero]
    exact WP.block_nil hI₁
  · simp only [decide_eq_false_iff_not] at hb
    have h := VG.Proof.Blake2.Arm.Stream.Update.fill_ok hP hp hr hI₁
    simp only [Nat.zero_add, Nat.sub_zero] at h
    rw [VG.Proof.Blake2.Arm.Stream.Update.a₁_eq s₀ hb]
    exact h

/-! ## The arguments of a call -/

theorem common_sp {s₀ : VG.Arm.State} {c : Nat} {s : VG.Arm.State} (h : VG.Proof.Blake2.Arm.Stream.Update.Common w s₀ c s) : VG.Proof.Blake2.Arm.Stream.below s = VG.Proof.Blake2.Arm.Stream.below s₀ := by
  rw [VG.Proof.Blake2.Arm.Stream.below, VG.Proof.Blake2.Arm.Stream.below, h.sp]

theorem cov_of {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.Arm.Stream.Update.Pre w s₀) {c : Nat} {s : VG.Arm.State} (h : VG.Proof.Blake2.Arm.Stream.Update.Common w s₀ c s) {R : Region}
    (hR : (∃ off, R.base = VG.Proof.Blake2.Arm.Stream.Update.stA s₀ + BitVec.ofNat 64 off ∧ off + R.len ≤ bufOff w + blockBytes w) ∨
      (∃ off, R.base = VG.Proof.Blake2.Arm.Stream.Update.dA s₀ + BitVec.ofNat 64 off ∧ off + R.len ≤ VG.Proof.Blake2.Arm.Stream.Update.len s₀)) :
    Covers [R] (s.rd ++ s.wr) := by
  rw [h.rd, h.wr, hp.rd, hp.wr]
  apply Covers.of_sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  rcases hR with ⟨off, h1, h2⟩ | ⟨off, h1, h2⟩
  · exact ⟨VG.Proof.Blake2.Arm.Stream.Update.stR s₀ w, by simp, off, h1, h2⟩
  · exact ⟨VG.Proof.Blake2.Arm.Stream.Update.dR s₀, by simp, off, h1, h2⟩

/-- The arguments of a call, from the registers. -/
theorem callArgs_of (hP : VG.Proof.Blake2.Arm.Stream.Ok P) {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.Arm.Stream.Update.Pre w s₀) {c : Nat} {s : VG.Arm.State} (h : VG.Proof.Blake2.Arm.Stream.Update.Common w s₀ c s)
    {blk : BitVec 32} {n : Nat} {t : BitVec 64} {last : BitVec 32}
    (hblk : (blk = VG.Proof.Blake2.Arm.Stream.Update.st s₀ + BitVec.ofNat 32 (bufOff w) ∧ n ≤ 1) ∨
      (∃ c₀, blk = VG.Proof.Blake2.Arm.Stream.Update.dp s₀ + BitVec.ofNat 32 c₀ ∧ c₀ < VG.Proof.Blake2.Arm.Stream.Update.len s₀ ∧ c₀ + blockBytes w * n ≤ VG.Proof.Blake2.Arm.Stream.Update.len s₀) ∨
      (blk = VG.Proof.Blake2.Arm.Stream.Update.st s₀ ∧ n = 0))
    (h0 : s.gpr .r0 = VG.Proof.Blake2.Arm.Stream.Update.st s₀) (h1 : s.gpr .r1 = blk) (h2 : s.gpr .r2 = BitVec.ofNat 32 n)
    (ht : s.gpr .r11 ++ s.gpr .r3 = t) (h12 : s.gpr .r12 = last) (hlr : s.gpr .lr = VG.Proof.Blake2.Arm.Stream.Update.scr s₀) :
    VG.Proof.Blake2.Arm.Stream.CallArgs (w := w) s (VG.Proof.Blake2.Arm.Stream.Update.st s₀) (VG.Proof.Blake2.Arm.Stream.Update.scr s₀) blk n t last := by
  have hl := hP.len
  have hst := hp.st_fit; have hsc := hp.scr_fit; have hdf := hp.d_fit
  have hL := VG.Proof.Blake2.Arm.Stream.Update.len_lt s₀
  have eN : Region.Sub ⟨VG.Proof.Blake2.Arm.Stream.Update.stA s₀, bufOff w⟩ (VG.Proof.Blake2.Arm.Stream.Update.stR s₀ w) := Region.sub_prefix (by omega)
  have eS : Region.Sub ⟨VG.Proof.Blake2.Arm.Stream.Update.scA s₀, 512⟩ (VG.Proof.Blake2.Arm.Stream.Update.scR s₀) := Region.sub_prefix (by omega)
  -- Where the blocks are.
  have hB : (State.addr blk = VG.Proof.Blake2.Arm.Stream.Update.stA s₀ + BitVec.ofNat 64 (bufOff w) ∧ blockBytes w * n ≤ blockBytes w) ∨
      (∃ c₀, State.addr blk = VG.Proof.Blake2.Arm.Stream.Update.dA s₀ + BitVec.ofNat 64 c₀ ∧ c₀ + blockBytes w * n ≤ VG.Proof.Blake2.Arm.Stream.Update.len s₀) ∨
      (State.addr blk = VG.Proof.Blake2.Arm.Stream.Update.stA s₀ ∧ n = 0) := by
    rcases hblk with ⟨rfl, hn⟩ | ⟨c₀, rfl, hc₀, hc₁⟩ | ⟨rfl, hn⟩
    · refine .inl ⟨addr_add (by omega), ?_⟩
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl <;> omega
    · exact .inr (.inl ⟨c₀, addr_add (by omega), hc₁⟩)
    · exact .inr (.inr ⟨rfl, hn⟩)
  have hBn : blockBytes w * n ≤ 2 ^ 32 := by
    rcases hB with ⟨-, h⟩ | ⟨c₀, -, h⟩ | ⟨-, rfl⟩ <;> omega
  have hsub : Region.Sub ⟨State.addr blk, blockBytes w * n⟩ (VG.Proof.Blake2.Arm.Stream.Update.stR s₀ w) ∨
      Region.Sub ⟨State.addr blk, blockBytes w * n⟩ (VG.Proof.Blake2.Arm.Stream.Update.dR s₀) := by
    rcases hB with ⟨e, h⟩ | ⟨c₀, e, h⟩ | ⟨e, rfl⟩
    · exact .inl (e ▸ Offset.sub_base _ (by omega))
    · exact .inr (e ▸ Offset.sub_base _ (by omega))
    · exact .inl (by rw [e, Nat.mul_zero]; exact Region.sub_prefix (by omega))
  have hblkN : blk.toNat + blockBytes w * n ≤ 2 ^ 32 := by
    rcases hblk with ⟨rfl, hn⟩ | ⟨c₀, rfl, hc₀, hc₁⟩ | ⟨rfl, rfl⟩
    · rw [VG.Proof.Blake2.Arm.Stream.toNat_add_ofNat (by omega)]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl <;> omega
    · rw [VG.Proof.Blake2.Arm.Stream.toNat_add_ofNat (by omega)]; omega
    · omega
  have hn : n < 2 ^ 32 := by
    have := hP.pos
    rcases Nat.lt_or_ge n (2 ^ 32) with h | h
    · exact h
    · exfalso; have := Nat.mul_le_mul_left (blockBytes w) h; omega
  refine ⟨h0, h1, h2, ht, h12, hlr, hn, by rw [h.sp]; exact hp.sp16, ?_, ?_, (hp.st_scr.sub_left eN).sub_right eS, ?_, ?_, ?_, ?_, ?_,
    by omega, hblkN, by omega⟩
  · refine VG.Proof.Blake2.Arm.Stream.Update.cov_of hp h ?_
    rcases hB with ⟨e, h'⟩ | ⟨c₀, e, h'⟩ | ⟨e, rfl⟩
    · exact .inl ⟨bufOff w, e, by dsimp only; omega⟩
    · exact .inr ⟨c₀, e, h'⟩
    · exact .inl ⟨0, by rw [e]; simp, by dsimp only; omega⟩
  · rw [h.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.Blake2.Arm.Stream.Update.stR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨VG.Proof.Blake2.Arm.Stream.Update.scR s₀, by simp, 0, by simp, by simp⟩
  · rcases hB with ⟨e, h'⟩ | ⟨c₀, e, h'⟩ | ⟨e, rfl⟩
    · rw [e]; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega)
    · exact (hp.d_st.sub_left (e ▸ Offset.sub_base _ (by omega))).sub_right eN
    · intro a h₁ _; simp [Region.Contains] at h₁
  · rcases hsub with e | e
    · exact (hp.st_scr.sub_left e).sub_right eS
    · exact (hp.d_scr.sub_left e).sub_right eS
  · rw [VG.Proof.Blake2.Arm.Stream.Update.common_sp h]; exact hp.w_st.sub_right eN
  · rw [VG.Proof.Blake2.Arm.Stream.Update.common_sp h]
    rcases hsub with e | e
    · exact hp.w_st.sub_right e
    · exact hp.w_d.sub_right e
  · rw [VG.Proof.Blake2.Arm.Stream.Update.common_sp h]; exact hp.w_scr.sub_right eS

/-- What a call leaves of `Common`. -/
theorem Common.after_call {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.Arm.Stream.Update.Pre w s₀) {c : Nat} {s s' : VG.Arm.State} (h : VG.Proof.Blake2.Arm.Stream.Update.Common w s₀ c s)
    (ha : VG.Proof.Blake2.Arm.Stream.After s [⟨VG.Proof.Blake2.Arm.Stream.Update.stA s₀, bufOff w⟩, ⟨VG.Proof.Blake2.Arm.Stream.Update.scA s₀, 512⟩] s') (hl : bufOff w ≤ bufOff w + blockBytes w) :
    VG.Proof.Blake2.Arm.Stream.Update.Common w s₀ c s' := by
  have hf : Frame [VG.Proof.Blake2.Arm.Stream.Update.stR s₀ w, ⟨VG.Proof.Blake2.Arm.Stream.Update.scA s₀, 512⟩, VG.Proof.Blake2.Arm.Stream.below s₀] s.mem s'.mem := by
    have := ha.frame
    rw [VG.Proof.Blake2.Arm.Stream.Update.common_sp h] at this
    exact this.sub fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨VG.Proof.Blake2.Arm.Stream.Update.stR s₀ w, by simp, Region.sub_prefix hl⟩
      · exact ⟨⟨VG.Proof.Blake2.Arm.Stream.Update.scA s₀, 512⟩, by simp, fun _ h => h⟩
      · exact ⟨VG.Proof.Blake2.Arm.Stream.below s₀, by simp, fun _ h => h⟩
  have hcp : ∀ r ∈ VG.Proof.Blake2.Arm.Stream.Update.commonRegs, r ∈ preserved ∧ r ≠ .lr := by decide
  have hg : ∀ r ∈ VG.Proof.Blake2.Arm.Stream.Update.commonRegs, s'.gpr r = s.gpr r := fun r hr => ha.cs r (hcp r hr).1 (hcp r hr).2
  refine ⟨h.c_le, ha.rd.trans h.rd, ha.wr.trans h.wr, ha.sp.trans h.sp, by rw [hg _ (by simp)]; exact h.r4,
    by rw [hg _ (by simp)]; exact h.r5, by rw [hg _ (by simp)]; exact h.r6, by rw [hg _ (by simp)]; exact h.r7,
    by rw [hg .r9 (by simp), hg .r10 (by simp)]; exact h.cn,
    h.frame.trans (hf.sub fun r hr => ?_), VG.Proof.Blake2.Arm.Stream.Update.saved_frame hp h.saved hf⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨VG.Proof.Blake2.Arm.Stream.Update.stR s₀ w, by simp, fun _ h => h⟩
  · exact ⟨VG.Proof.Blake2.Arm.Stream.Update.scR s₀, by simp, Region.sub_prefix (by omega)⟩
  · exact ⟨VG.Proof.Blake2.Arm.Stream.below s₀, by simp, fun _ h => h⟩

theorem r8_after {s s' : VG.Arm.State} {ws : List Region} (ha : VG.Proof.Blake2.Arm.Stream.After s ws s') : s'.gpr .r8 = s.gpr .r8 :=
  ha.cs .r8 (by simp [preserved]) (by decide)

/-! ## The prologue, up to the first call -/

/-- What holds before the first call. -/
def PostPro (P : VG.Spec.Blake2.Params w) (s₀ : VG.Arm.State) (s : VG.Arm.State) : Prop :=
  VG.Proof.Blake2.Arm.Stream.Update.Inv P s₀ (VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) (VG.Proof.Blake2.Arm.Stream.Update.r₀ w s₀ + VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) s ∧
    VG.Proof.Blake2.Arm.Stream.CallArgs (w := w) s (VG.Proof.Blake2.Arm.Stream.Update.st s₀) (VG.Proof.Blake2.Arm.Stream.Update.scr s₀) (VG.Proof.Blake2.Arm.Stream.Update.st s₀ + BitVec.ofNat 32 (bufOff w)) (VG.Proof.Blake2.Arm.Stream.Update.n₁ w s₀)
      (BitVec.ofNat 64 (VG.Proof.Blake2.Arm.Stream.Update.cnt s₀ + VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀)) 0

theorem args₁_ok (hP : VG.Proof.Blake2.Arm.Stream.Ok P) {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.Arm.Stream.Update.Pre w s₀) {s : VG.Arm.State}
    (hI : VG.Proof.Blake2.Arm.Stream.Update.Inv P s₀ (VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) (VG.Proof.Blake2.Arm.Stream.Update.r₀ w s₀ + VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) s) :
    WP isa (.seq (.block [.mov .r2 (.imm 0), .cmp .r7 (.imm 0)])
      (.seq (.ite .eq (.block []) (.seq (.block [.cmp .r8 (.imm 0)])
        (.ite .eq (.block []) (.block [.mov .r2 (.imm 1)]))))
      (.block (args ++ ([.dp .add .r1 .r4 (.imm (BitVec.ofNat 32 (N w))), .mov .r3 (.reg .r9),
        .mov .r11 (.reg .r10)] : List Instr))))) s (VG.Proof.Blake2.Arm.Stream.Update.PostPro P s₀) := by
  have hL := VG.Proof.Blake2.Arm.Stream.Update.len_lt s₀
  have hr := VG.Proof.Blake2.Arm.Stream.Update.r₁_le hP s₀
  have hl := hP.len
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_cmp (op2_imm (by decide)) fun s₂ f₂ z₂ =>
    WP.block_nil ?_)
  have hI₂ := (hI.of_upd u₁).of_flags f₂
  have hz : isa.eval .eq s₂ = some (decide (VG.Proof.Blake2.Arm.Stream.Update.len s₀ - VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀ = 0)) := by
    show VG.Arm.eval .eq s₂ = _
    rw [eval_eq, z₂, u₁.other _ (by decide), hI.r7, cmp0 (by omega)]
  -- `r2` := `n₁`.
  refine WP.seq (WP.mono (Q := fun (t : VG.Arm.State) => VG.Proof.Blake2.Arm.Stream.Update.Inv P s₀ (VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) (VG.Proof.Blake2.Arm.Stream.Update.r₀ w s₀ + VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) t ∧
      t.gpr .r2 = BitVec.ofNat 32 (VG.Proof.Blake2.Arm.Stream.Update.n₁ w s₀)) ?_ fun t ⟨hIt, h2t⟩ => ?_)
  · refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      refine WP.block_nil ⟨hI₂, ?_⟩
      rw [f₂.gpr, u₁.gpr]; simp [VG.Proof.Blake2.Arm.Stream.Update.n₁, hb]
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.seq (wp_cmp (op2_imm (by decide)) fun s₃ f₃ z₃ => WP.block_nil ?_)
      have hI₃ := hI₂.of_flags f₃
      have hz₃ : isa.eval .eq s₃ = some (decide (VG.Proof.Blake2.Arm.Stream.Update.r₀ w s₀ + VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀ = 0)) := by
        show VG.Arm.eval .eq s₃ = _
        rw [eval_eq, z₃, hI₂.r8, cmp0 (by omega)]
      refine WP.ite _ hz₃ (fun hb' => ?_) (fun hb' => ?_)
      · simp only [decide_eq_true_eq] at hb'
        refine WP.block_nil ⟨hI₃, ?_⟩
        rw [f₃.gpr, f₂.gpr, u₁.gpr]; simp [VG.Proof.Blake2.Arm.Stream.Update.n₁, hb']
      · simp only [decide_eq_false_iff_not] at hb'
        refine wp_mov (op2_imm (by decide)) fun s₄ u₄ => WP.block_nil ⟨hI₃.of_upd u₄, ?_⟩
        rw [u₄.gpr]; simp only [VG.Proof.Blake2.Arm.Stream.Update.n₁, ne_eq, hb, hb', not_false_eq_true, and_self, ite_true]; rfl
  · simp only [args, List.cons_append, List.nil_append]
    refine wp_mov (op2_reg _ _) fun s₅ u₅ => wp_mov (op2_imm (by decide)) fun s₆ u₆ =>
      wp_mov (op2_reg _ _) fun s₇ u₇ => wp_add (op2_imm hP.encN) fun s₈ u₈ =>
      wp_mov (op2_reg _ _) fun s₉ u₉ => wp_mov (op2_reg _ _) fun s₁₀ u₁₀ => WP.block_nil ?_
    have hI' : VG.Proof.Blake2.Arm.Stream.Update.Inv P s₀ (VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) (VG.Proof.Blake2.Arm.Stream.Update.r₀ w s₀ + VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) s₁₀ :=
      (((((hIt.of_upd u₅).of_upd u₆).of_upd u₇).of_upd u₈).of_upd u₉).of_upd u₁₀
    refine ⟨hI', VG.Proof.Blake2.Arm.Stream.Update.callArgs_of hP hp hI'.toCommon (.inl ⟨rfl, VG.Proof.Blake2.Arm.Stream.Update.n₁_le s₀⟩) ?_ ?_ ?_ ?_ ?_ ?_⟩ <;>
      simp only [u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr, u₆.other,
        u₅.gpr, u₅.other, ne_eq, reduceCtorEq, not_false_eq_true, hIt.r4, hIt.r5, h2t, VG.Proof.Blake2.Arm.Stream.N_eq]
    exact hIt.cn

theorem pro_ok (hP : VG.Proof.Blake2.Arm.Stream.Ok P) {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.Arm.Stream.Update.Pre w s₀) :
    WP isa (updatePro (w := w)) s₀ (VG.Proof.Blake2.Arm.Stream.Update.PostPro P s₀) := by
  unfold updatePro
  refine WP.seq (WP.mono (VG.Proof.Blake2.Arm.Stream.Update.prologue_ok hp) fun s₁ ⟨hC, hst⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Blake2.Arm.Stream.Update.bufLen_inv hP hC hst) fun s₂ hI₂ => ?_)
  exact VG.Proof.Blake2.Arm.Stream.Update.head_ok hP hp hI₂ fun s₃ hI₃ => VG.Proof.Blake2.Arm.Stream.Update.args₁_ok hP hp hI₃

/-! ## The first call -/

/-- What holds after the first call. -/
def Mid (P : VG.Spec.Blake2.Params w) (s₀ s : VG.Arm.State) : Prop :=
  VG.Proof.Blake2.Arm.Stream.Update.Common w s₀ (VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) s ∧ s.gpr .r8 = BitVec.ofNat 32 (VG.Proof.Blake2.Arm.Stream.Update.r₀ w s₀ + VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) ∧
    ∀ h0 d, VG.Proof.Blake2.Arm.Stream.Update.R₀ P s₀ h0 d → ReprR P h0 s.mem (VG.Proof.Blake2.Arm.Stream.Update.stA s₀) (d ++ VG.Proof.Blake2.Arm.Stream.Update.D s₀ (VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀))
      (if VG.Proof.Blake2.Arm.Stream.Update.n₁ w s₀ = 1 then 0 else VG.Proof.Blake2.Arm.Stream.Update.r₀ w s₀ + VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀)

theorem compressBlocks_one (h : HashValue w) (m : Mem) (p : Addr) (t : Nat) (f : Bool) :
    compressBlocks P h m p 1 t f = F P h (VG.Spec.Blake2.blockAt w m p) t f := by
  rw [compressBlocks_succ, compressBlocks_zero]; simp

/-- The buffer's bytes are not among those a call may write. -/
theorem buf_after {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.Arm.Stream.Update.Pre w s₀) {c : Nat} {s s' : VG.Arm.State} (h : VG.Proof.Blake2.Arm.Stream.Update.Common w s₀ c s)
    (ha : VG.Proof.Blake2.Arm.Stream.After s [⟨VG.Proof.Blake2.Arm.Stream.Update.stA s₀, bufOff w⟩, ⟨VG.Proof.Blake2.Arm.Stream.Update.scA s₀, 512⟩] s') {i : Nat} (hi : i < blockBytes w) :
    s'.mem (VG.Proof.Blake2.Arm.Stream.Update.stA s₀ + BitVec.ofNat 64 (bufOff w) + BitVec.ofNat 64 i) =
      s.mem (VG.Proof.Blake2.Arm.Stream.Update.stA s₀ + BitVec.ofNat 64 (bufOff w) + BitVec.ofNat 64 i) := by
  have hst := hp.st_fit
  have eB : Region.Sub ⟨VG.Proof.Blake2.Arm.Stream.Update.stA s₀ + BitVec.ofNat 64 (bufOff w), blockBytes w⟩ (VG.Proof.Blake2.Arm.Stream.Update.stR s₀ w) :=
    Offset.sub_base _ (by omega)
  refine ha.frame.bytes (R := ⟨VG.Proof.Blake2.Arm.Stream.Update.stA s₀ + BitVec.ofNat 64 (bufOff w), blockBytes w⟩) (fun r hr => ?_)
    (by show blockBytes w ≤ 2 ^ 64; omega) hi
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint_base _ (Nat.le_refl _) (by omega)
  · exact (hp.st_scr.sub_left eB).sub_right (Region.sub_prefix (by omega))
  · rw [VG.Proof.Blake2.Arm.Stream.Update.common_sp h]; exact (hp.w_st.sub_right eB).symm

theorem call₁_ok (hP : VG.Proof.Blake2.Arm.Stream.Ok P) {name : String} {code : Prog isa} (hf : VG.Proof.Blake2.Arm.Stream.CalleeOk P code) {s₀ : VG.Arm.State}
    (hp : VG.Proof.Blake2.Arm.Stream.Update.Pre w s₀) {s : VG.Arm.State} (h : VG.Proof.Blake2.Arm.Stream.Update.PostPro P s₀ s) : WP isa (call name code) s (VG.Proof.Blake2.Arm.Stream.Update.Mid P s₀) := by
  have hl := hP.len
  have hI := h.1
  refine VG.Proof.Blake2.Arm.Stream.call_ok hf h.2 fun s' ha hst => ⟨hI.toCommon.after_call hp ha (by omega),
    by rw [VG.Proof.Blake2.Arm.Stream.Update.r8_after ha]; exact hI.r8, fun h0 d hd => ?_⟩
  have hr := hI.repr h0 d hd
  split
  · rename_i hn
    rw [VG.Proof.Blake2.Arm.Stream.Update.n₁_full hP s₀ hn] at hr
    refine reprR_flush P hP.pos hr ?_
    have hlen := hd.2.2
    have ha₁ := VG.Proof.Blake2.Arm.Stream.Update.a₁_le (w := w) s₀
    rw [hst, hn, VG.Proof.Blake2.Arm.Stream.Update.compressBlocks_one, R₀.length hd _, addr_add (by have := hp.st_fit; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [← hd.cnt_eq] at hlen; omega)]
    rfl
  · rename_i hn
    have hn0 : VG.Proof.Blake2.Arm.Stream.Update.n₁ w s₀ = 0 := by have := VG.Proof.Blake2.Arm.Stream.Update.n₁_le (w := w) s₀; omega
    rw [hn0, compressBlocks_zero] at hst
    exact VG.Proof.Blake2.Arm.Stream.reprR_congr hst (fun i hi => VG.Proof.Blake2.Arm.Stream.Update.buf_after hp hI.toCommon ha (by have := VG.Proof.Blake2.Arm.Stream.Update.r₁_le hP s₀; omega)) hr

/-! ## Between the calls -/

section
variable (w : Nat) (s₀ : VG.Arm.State)

/-- The bytes in the buffer before the second call. -/
def r₂ : Nat := if (VG.Proof.Blake2.Arm.Stream.Update.len s₀ - VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) = 0 then VG.Proof.Blake2.Arm.Stream.Update.r₀ w s₀ + VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀ else 0
/-- The blocks the second call compresses. -/
def k₂ : Nat := if (VG.Proof.Blake2.Arm.Stream.Update.len s₀ - VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) = 0 then 0 else ((VG.Proof.Blake2.Arm.Stream.Update.len s₀ - VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) - 1) / blockBytes w
/-- Where they are. -/
def blk₂ : BitVec 32 := if (VG.Proof.Blake2.Arm.Stream.Update.len s₀ - VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) = 0 then VG.Proof.Blake2.Arm.Stream.Update.st s₀ else VG.Proof.Blake2.Arm.Stream.Update.dp s₀ + BitVec.ofNat 32 (VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀)

end

/-- What holds before the second call. -/
def PostMid (P : VG.Spec.Blake2.Params w) (s₀ s : VG.Arm.State) : Prop :=
  VG.Proof.Blake2.Arm.Stream.Update.Inv P s₀ (VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) (VG.Proof.Blake2.Arm.Stream.Update.r₂ w s₀) s ∧
    VG.Proof.Blake2.Arm.Stream.CallArgs (w := w) s (VG.Proof.Blake2.Arm.Stream.Update.st s₀) (VG.Proof.Blake2.Arm.Stream.Update.scr s₀) (VG.Proof.Blake2.Arm.Stream.Update.blk₂ w s₀) (VG.Proof.Blake2.Arm.Stream.Update.k₂ w s₀)
      (BitVec.ofNat 64 (VG.Proof.Blake2.Arm.Stream.Update.cnt s₀ + VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀ + blockBytes w)) 0

theorem k₂_le (s₀ : VG.Arm.State) : VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀ + blockBytes w * VG.Proof.Blake2.Arm.Stream.Update.k₂ w s₀ ≤ VG.Proof.Blake2.Arm.Stream.Update.len s₀ := by
  have := VG.Proof.Blake2.Arm.Stream.Update.a₁_le (w := w) s₀
  unfold VG.Proof.Blake2.Arm.Stream.Update.k₂; split
  · rw [Nat.mul_zero, Nat.add_zero]; exact this
  · have := Nat.mul_div_le ((VG.Proof.Blake2.Arm.Stream.Update.len s₀ - VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) - 1) (blockBytes w); omega

theorem mid_ok (hP : VG.Proof.Blake2.Arm.Stream.Ok P) {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.Arm.Stream.Update.Pre w s₀) {s : VG.Arm.State} (h : VG.Proof.Blake2.Arm.Stream.Update.Mid P s₀ s) :
    WP isa (updateMid (w := w)) s (VG.Proof.Blake2.Arm.Stream.Update.PostMid P s₀) := by
  obtain ⟨hC, h8, hrep⟩ := h
  have hL := VG.Proof.Blake2.Arm.Stream.Update.len_lt s₀
  have ha₁ := VG.Proof.Blake2.Arm.Stream.Update.a₁_le (w := w) s₀
  have hlbb : 1 ≤ VG.Impl.Blake2.Arm.Stream.lbb w ∧ VG.Impl.Blake2.Arm.Stream.lbb w ≤ 31 := ⟨hP.lbb.1, hP.lbb.2.1⟩
  unfold updateMid
  refine WP.seq (wp_cmp (op2_imm (by decide)) fun s₁ f₁ z₁ => WP.block_nil ?_)
  have hz : isa.eval .eq s₁ = some (decide ((VG.Proof.Blake2.Arm.Stream.Update.len s₀ - VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) = 0)) := by
    show VG.Arm.eval .eq s₁ = _
    rw [eval_eq, z₁, hC.r7, cmp0 (by omega)]
  have hC₁ := hC.of_gpr (fun r _ => by rw [f₁.gpr]) f₁.mem f₁.rd f₁.wr f₁.sp
  refine WP.seq (WP.mono (Q := fun (t : VG.Arm.State) => VG.Proof.Blake2.Arm.Stream.Update.Inv P s₀ (VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) (VG.Proof.Blake2.Arm.Stream.Update.r₂ w s₀) t ∧
      t.gpr .r2 = BitVec.ofNat 32 (VG.Proof.Blake2.Arm.Stream.Update.k₂ w s₀) ∧ t.gpr .r1 = VG.Proof.Blake2.Arm.Stream.Update.blk₂ w s₀) ?_ fun t ⟨hIt, h2, h1⟩ => ?_)
  · refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      have hn : VG.Proof.Blake2.Arm.Stream.Update.n₁ w s₀ = 0 := by simp [VG.Proof.Blake2.Arm.Stream.Update.n₁, hb]
      refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ => WP.block_nil ?_
      have hg : ∀ r ∈ .r8 :: VG.Proof.Blake2.Arm.Stream.Update.commonRegs, s₃.gpr r = s₁.gpr r := fun r hr => by
        rw [u₃.other r (fun e => by subst e; simp at hr), u₂.other r (fun e => by subst e; simp at hr)]
      refine ⟨{ hC₁.of_gpr (fun r hr => hg r (List.mem_cons_of_mem _ hr)) (by rw [u₃.mem, u₂.mem])
          (by rw [u₃.rd, u₂.rd]) (by rw [u₃.wr, u₂.wr]) (by rw [u₃.sp, u₂.sp]) with
        r8 := by rw [hg _ (by simp), f₁.gpr, h8]; simp [VG.Proof.Blake2.Arm.Stream.Update.r₂, hb]
        repr := fun h0 d hd => by
          rw [u₃.mem, u₂.mem, f₁.mem]
          have := hrep h0 d hd
          simp only [hn] at this
          simpa [VG.Proof.Blake2.Arm.Stream.Update.r₂, hb] using this }, ?_, ?_⟩
      · rw [u₃.other _ (by decide), u₂.gpr]; simp [VG.Proof.Blake2.Arm.Stream.Update.k₂, hb]
      · rw [u₃.gpr, u₂.other _ (by decide), f₁.gpr, hC.r4]; simp [VG.Proof.Blake2.Arm.Stream.Update.blk₂, hb]
    · simp only [decide_eq_false_iff_not] at hb
      refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => wp_sub (op2_imm (by decide)) fun s₃ u₃ =>
        wp_mov (op2_lsr hlbb) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ => WP.block_nil ?_
      have hg : ∀ r ∈ VG.Proof.Blake2.Arm.Stream.Update.commonRegs, s₅.gpr r = s₁.gpr r := fun r hr => by
        rw [u₅.other r (VG.Proof.Blake2.Arm.Stream.Update.notC hr .r1), u₄.other r (VG.Proof.Blake2.Arm.Stream.Update.notC hr .r2), u₃.other r (VG.Proof.Blake2.Arm.Stream.Update.notC hr .r2),
          u₂.other r (VG.Proof.Blake2.Arm.Stream.Update.notC hr .r8)]
      have hr0 : (if VG.Proof.Blake2.Arm.Stream.Update.n₁ w s₀ = 1 then 0 else VG.Proof.Blake2.Arm.Stream.Update.r₀ w s₀ + VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) = 0 := by
        simp only [VG.Proof.Blake2.Arm.Stream.Update.n₁]; split
        · rfl
        · rename_i hc
          simp only [ne_eq, not_and, Decidable.not_not] at hc
          exact hc hb
      refine ⟨{ hC₁.of_gpr hg (by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]) (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd])
          (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr]) (by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp]) with
        r8 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
                 simp [VG.Proof.Blake2.Arm.Stream.Update.r₂, hb]
        repr := fun h0 d hd => by
          rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, f₁.mem]
          have := hrep h0 d hd
          rw [hr0] at this
          simpa [VG.Proof.Blake2.Arm.Stream.Update.r₂, hb] using this }, ?_, ?_⟩
      · rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.other _ (by decide), f₁.gpr, hC.r7,
          show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), VG.Proof.Blake2.Arm.Stream.shr_ofNat hP (by omega)]
        simp [VG.Proof.Blake2.Arm.Stream.Update.k₂, hb]
      · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), f₁.gpr, hC.r6]
        simp [VG.Proof.Blake2.Arm.Stream.Update.blk₂, hb]
  · simp only [args, List.cons_append, List.nil_append]
    refine wp_mov (op2_reg _ _) fun s₆ u₆ => wp_mov (op2_imm (by decide)) fun s₇ u₇ =>
      wp_mov (op2_reg _ _) fun s₈ u₈ => VG.Proof.Blake2.Arm.Stream.wp_adds (op2_imm hP.encB) fun s₉ u₉ c₉ =>
      VG.Proof.Blake2.Arm.Stream.wp_adc (op2_imm (by decide)) fun s₁₀ u₁₀ _ => WP.block_nil ?_
    have hI' : VG.Proof.Blake2.Arm.Stream.Update.Inv P s₀ (VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) (VG.Proof.Blake2.Arm.Stream.Update.r₂ w s₀) s₁₀ :=
      ((((hIt.of_upd u₆).of_upd u₇).of_upd u₈).of_upd u₉).of_upd u₁₀
    have hB : blockBytes w < 2 ^ 32 := by rcases hP.bb with h | h <;> omega
    refine ⟨hI', VG.Proof.Blake2.Arm.Stream.Update.callArgs_of hP hp hI'.toCommon ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
    · by_cases hb : (VG.Proof.Blake2.Arm.Stream.Update.len s₀ - VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) = 0
      · exact .inr (.inr ⟨by simp [VG.Proof.Blake2.Arm.Stream.Update.blk₂, hb], by simp [VG.Proof.Blake2.Arm.Stream.Update.k₂, hb]⟩)
      · refine .inr (.inl ⟨VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀, by simp [VG.Proof.Blake2.Arm.Stream.Update.blk₂, hb], by omega, VG.Proof.Blake2.Arm.Stream.Update.k₂_le (w := w) s₀⟩)
    · simp only [u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.gpr, ne_eq, reduceCtorEq, not_false_eq_true,
        hIt.r4]
    · simp only [u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.other, ne_eq, reduceCtorEq, not_false_eq_true, h1]
    · simp only [u₁₀.other, u₉.other, u₈.other, u₇.other, u₆.other, ne_eq, reduceCtorEq, not_false_eq_true, h2]
    · simp only [u₁₀.gpr, u₁₀.other .r3 (by decide), u₉.gpr, u₉.other .r10 (by decide), c₉,
        u₈.other .r9 (by decide), u₈.other .r10 (by decide), u₇.other .r9 (by decide), u₇.other .r10 (by decide),
        u₆.other .r9 (by decide), u₆.other .r10 (by decide), VG.Proof.Blake2.Arm.Stream.B_eq]
      exact VG.Proof.Blake2.Arm.Stream.add64_ofNat hIt.cn hB
    · simp only [u₁₀.other, u₉.other, u₈.other, u₇.gpr, ne_eq, reduceCtorEq, not_false_eq_true]
    · simp only [u₁₀.other, u₉.other, u₈.gpr, u₇.other, u₆.other, ne_eq, reduceCtorEq, not_false_eq_true,
        hIt.r5]

/-! ## The second call -/

/-- What holds after the second call. -/
def End (P : VG.Spec.Blake2.Params w) (s₀ s : VG.Arm.State) : Prop :=
  VG.Proof.Blake2.Arm.Stream.Update.Common w s₀ (VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) s ∧ s.gpr .r8 = BitVec.ofNat 32 (VG.Proof.Blake2.Arm.Stream.Update.r₂ w s₀) ∧
    ∀ h0 d, VG.Proof.Blake2.Arm.Stream.Update.R₀ P s₀ h0 d →
      ReprR P h0 s.mem (VG.Proof.Blake2.Arm.Stream.Update.stA s₀) (d ++ VG.Proof.Blake2.Arm.Stream.Update.D s₀ (VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀ + blockBytes w * VG.Proof.Blake2.Arm.Stream.Update.k₂ w s₀)) (VG.Proof.Blake2.Arm.Stream.Update.r₂ w s₀)

theorem call₂_ok (hP : VG.Proof.Blake2.Arm.Stream.Ok P) {name : String} {code : Prog isa} (hf : VG.Proof.Blake2.Arm.Stream.CalleeOk P code) {s₀ : VG.Arm.State}
    (hp : VG.Proof.Blake2.Arm.Stream.Update.Pre w s₀) {s : VG.Arm.State} (h : VG.Proof.Blake2.Arm.Stream.Update.PostMid P s₀ s) : WP isa (call name code) s (VG.Proof.Blake2.Arm.Stream.Update.End P s₀) := by
  have hl := hP.len
  have hI := h.1
  have hL := VG.Proof.Blake2.Arm.Stream.Update.len_lt s₀
  have ha₁ := VG.Proof.Blake2.Arm.Stream.Update.a₁_le (w := w) s₀
  refine VG.Proof.Blake2.Arm.Stream.call_ok hf h.2 fun s' ha hst => ⟨hI.toCommon.after_call hp ha (by omega),
    by rw [VG.Proof.Blake2.Arm.Stream.Update.r8_after ha]; exact hI.r8, fun h0 d hd => ?_⟩
  have hr := hI.repr h0 d hd
  by_cases hk : VG.Proof.Blake2.Arm.Stream.Update.k₂ w s₀ = 0
  · rw [hk, compressBlocks_zero] at hst
    rw [hk, Nat.mul_zero, Nat.add_zero]
    exact VG.Proof.Blake2.Arm.Stream.reprR_congr hst (fun i hi => VG.Proof.Blake2.Arm.Stream.Update.buf_after hp hI.toCommon ha (by
      have := bufLen_le (w := w) hP.pos (VG.Proof.Blake2.Arm.Stream.Update.cnt s₀); have := VG.Proof.Blake2.Arm.Stream.Update.r₁_le hP s₀
      unfold VG.Proof.Blake2.Arm.Stream.Update.r₂ at hi; split at hi <;> omega)) hr
  · have hb : (VG.Proof.Blake2.Arm.Stream.Update.len s₀ - VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) ≠ 0 := fun hb => hk (by simp [VG.Proof.Blake2.Arm.Stream.Update.k₂, hb])
    have e2 : VG.Proof.Blake2.Arm.Stream.Update.r₂ w s₀ = 0 := by simp [VG.Proof.Blake2.Arm.Stream.Update.r₂, hb]
    rw [e2] at hr ⊢
    have hkl := VG.Proof.Blake2.Arm.Stream.Update.k₂_le (w := w) s₀
    have hpos := hP.pos
    have hkB : blockBytes w ≤ blockBytes w * VG.Proof.Blake2.Arm.Stream.Update.k₂ w s₀ := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hk)
    have hlt : VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀ + blockBytes w * VG.Proof.Blake2.Arm.Stream.Update.k₂ w s₀ < VG.Proof.Blake2.Arm.Stream.Update.len s₀ := by
      have := Nat.div_mul_le_self ((VG.Proof.Blake2.Arm.Stream.Update.len s₀ - VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) - 1) (blockBytes w)
      simp only [VG.Proof.Blake2.Arm.Stream.Update.k₂, hb, ite_false] at hkB ⊢; rw [Nat.mul_comm]; omega
    have hlen := hd.2.2
    have ecn : (BitVec.ofNat 64 (VG.Proof.Blake2.Arm.Stream.Update.cnt s₀ + VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀ + blockBytes w)).toNat =
        (d ++ VG.Proof.Blake2.Arm.Stream.Update.D s₀ (VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀)).length + blockBytes w := by
      rw [R₀.length hd _, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [← hd.cnt_eq] at hlen; omega)]
    have eblk : State.addr (VG.Proof.Blake2.Arm.Stream.Update.blk₂ w s₀) = VG.Proof.Blake2.Arm.Stream.Update.dA s₀ + BitVec.ofNat 64 (VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) := by
      simp only [VG.Proof.Blake2.Arm.Stream.Update.blk₂, hb, ite_false]; exact addr_add (by have := hp.d_fit; omega)
    rw [ecn, eblk] at hst
    have := reprR_blocks P hP.pos hr (mem' := s'.mem) (q := VG.Proof.Blake2.Arm.Stream.Update.dA s₀ + BitVec.ofNat 64 (VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀))
      (k := VG.Proof.Blake2.Arm.Stream.Update.k₂ w s₀) (by rw [hst]; rfl)
    have e : VG.Spec.Blake2.bytesAt s.mem (VG.Proof.Blake2.Arm.Stream.Update.dA s₀ + BitVec.ofNat 64 (VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀)) (blockBytes w * VG.Proof.Blake2.Arm.Stream.Update.k₂ w s₀) =
        VG.Spec.Blake2.bytesAt s₀.mem (VG.Proof.Blake2.Arm.Stream.Update.dA s₀ + BitVec.ofNat 64 (VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀)) (blockBytes w * VG.Proof.Blake2.Arm.Stream.Update.k₂ w s₀) :=
      bytesAt_congr fun i hi => by rw [Offset.add_add]; exact hI.data hp (by omega)
    rw [e, List.append_assoc, ← VG.Proof.Blake2.bytesAt_add] at this
    exact this

/-! ## The end -/

theorem rem_eq (x : Nat) :
    x - ((x - 1) % blockBytes w + 1) = blockBytes w * ((x - 1) / blockBytes w) := by
  have := Nat.div_add_mod (x - 1) (blockBytes w); omega

/-- The final state of `Inv` is the streaming state of the data. -/
theorem final_repr (hP : VG.Proof.Blake2.Arm.Stream.Ok P) {s₀ : VG.Arm.State} {h0 : HashValue w} {d : List Byte} (hd : VG.Proof.Blake2.Arm.Stream.Update.R₀ P s₀ h0 d)
    {m : Mem} {rf : Nat} (hrf : rf = 0 → VG.Proof.Blake2.Arm.Stream.Update.cnt s₀ + VG.Proof.Blake2.Arm.Stream.Update.len s₀ = 0)
    (h : ReprR P h0 m (VG.Proof.Blake2.Arm.Stream.Update.stA s₀) (d ++ VG.Proof.Blake2.Arm.Stream.Update.D s₀ (VG.Proof.Blake2.Arm.Stream.Update.len s₀)) rf) :
    Spec.Blake2.Repr P h0 m (VG.Proof.Blake2.Arm.Stream.Update.stA s₀) (d ++ VG.Proof.Blake2.Arm.Stream.Update.D s₀ (VG.Proof.Blake2.Arm.Stream.Update.len s₀)) := by
  rcases Nat.eq_zero_or_pos rf with h0' | h0'
  · subst h0'
    have := hrf rfl
    have hl : (d ++ VG.Proof.Blake2.Arm.Stream.Update.D s₀ (VG.Proof.Blake2.Arm.Stream.Update.len s₀)).length = 0 := by rw [R₀.length hd _]; omega
    rw [repr_iff P hP.pos, hl]
    exact h
  · exact repr_of_reprR P hP.pos h h0'

theorem end_ok (hP : VG.Proof.Blake2.Arm.Stream.Ok P) {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.Arm.Stream.Update.Pre w s₀) {s : VG.Arm.State} (h : VG.Proof.Blake2.Arm.Stream.Update.End P s₀ s) :
    WP isa (updateEnd (w := w)) s fun s' => abiPreserved s₀ s' ∧ (VG.Proof.Blake2.updateArm P).post s₀ s' := by
  obtain ⟨hC, h8, hrep⟩ := h
  have hL := VG.Proof.Blake2.Arm.Stream.Update.len_lt s₀
  have ha₁ := VG.Proof.Blake2.Arm.Stream.Update.a₁_le (w := w) s₀
  have hpos := hP.pos
  have hl := hP.len
  have hB : blockBytes w ≤ 128 := by rcases hP.bb with h | h <;> omega
  unfold updateEnd
  refine WP.seq (wp_cmp (op2_imm (by decide)) fun s₁ f₁ z₁ => WP.block_nil ?_)
  have hz : isa.eval .eq s₁ = some (decide ((VG.Proof.Blake2.Arm.Stream.Update.len s₀ - VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) = 0)) := by
    show VG.Arm.eval .eq s₁ = _
    rw [eval_eq, z₁, hC.r7, cmp0 (by omega)]
  have hC₁ := hC.of_gpr (fun r _ => by rw [f₁.gpr]) f₁.mem f₁.rd f₁.wr f₁.sp
  -- Every byte of data is consumed.
  refine WP.seq (WP.mono (Q := fun (t : VG.Arm.State) => ∃ rf, (rf = 0 → VG.Proof.Blake2.Arm.Stream.Update.cnt s₀ + VG.Proof.Blake2.Arm.Stream.Update.len s₀ = 0) ∧ VG.Proof.Blake2.Arm.Stream.Update.Inv P s₀ (VG.Proof.Blake2.Arm.Stream.Update.len s₀) rf t)
    ?_ fun t ⟨rf, hrf, hIt⟩ => ?_)
  · refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      have hk : VG.Proof.Blake2.Arm.Stream.Update.k₂ w s₀ = 0 := by simp [VG.Proof.Blake2.Arm.Stream.Update.k₂, hb]
      have e2 : VG.Proof.Blake2.Arm.Stream.Update.r₂ w s₀ = VG.Proof.Blake2.Arm.Stream.Update.r₀ w s₀ + VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀ := by simp [VG.Proof.Blake2.Arm.Stream.Update.r₂, hb]
      have ea : VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀ = VG.Proof.Blake2.Arm.Stream.Update.len s₀ := by omega
      refine WP.block_nil ⟨VG.Proof.Blake2.Arm.Stream.Update.r₂ w s₀, fun h0 => ?_, ?_⟩
      · rw [e2] at h0
        have hr0 : VG.Proof.Blake2.Arm.Stream.Update.r₀ w s₀ = 0 := by omega
        have : VG.Proof.Blake2.Arm.Stream.Update.cnt s₀ = 0 := by
          by_contra hc; have := bufLen_pos (w := w) hc; simp only [VG.Proof.Blake2.Arm.Stream.Update.r₀] at hr0; omega
        omega
      · rw [← ea]
        exact
          { hC₁ with
            r8 := by rw [f₁.gpr]; exact h8
            repr := fun h0 d hd => by
              rw [f₁.mem]; have := hrep h0 d hd; rwa [hk, Nat.mul_zero, Nat.add_zero] at this }
    · simp only [decide_eq_false_iff_not] at hb
      have e2 : VG.Proof.Blake2.Arm.Stream.Update.r₂ w s₀ = 0 := by simp [VG.Proof.Blake2.Arm.Stream.Update.r₂, hb]
      have ek : blockBytes w * VG.Proof.Blake2.Arm.Stream.Update.k₂ w s₀ = (VG.Proof.Blake2.Arm.Stream.Update.len s₀ - VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) - (((VG.Proof.Blake2.Arm.Stream.Update.len s₀ - VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) - 1) % blockBytes w + 1) := by
        rw [VG.Proof.Blake2.Arm.Stream.Update.rem_eq _]; simp [VG.Proof.Blake2.Arm.Stream.Update.k₂, hb]
      have hrem : ((VG.Proof.Blake2.Arm.Stream.Update.len s₀ - VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) - 1) % blockBytes w < blockBytes w := Nat.mod_lt _ hpos
      refine WP.seq (wp_sub (op2_imm (by decide)) fun s₂ u₂ => wp_and (op2_imm hP.encB1) fun s₃ u₃ =>
        wp_add (op2_imm (by decide)) fun s₄ u₄ => wp_sub (op2_reg _ _) fun s₅ u₅ =>
        wp_add (op2_reg _ _) fun s₆ u₆ => wp_sub (op2_reg _ _) fun s₇ u₇ =>
        VG.Proof.Blake2.Arm.Stream.wp_adds (op2_reg _ _) fun s₈ u₈ c₈ => VG.Proof.Blake2.Arm.Stream.wp_adc (op2_imm (by decide)) fun s₉ u₉ _ => WP.block_nil ?_)
      have h4 : s₄.gpr .r11 = BitVec.ofNat 32 (((VG.Proof.Blake2.Arm.Stream.Update.len s₀ - VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) - 1) % blockBytes w + 1) := by
        rw [u₄.gpr, u₃.gpr, u₂.gpr, f₁.gpr, hC.r7, VG.Proof.Blake2.Arm.Stream.bufLen_lo hP hb]
        simp only [bufLen, hb, ite_false]
      have h11 : s₉.gpr .r11 = BitVec.ofNat 32 (((VG.Proof.Blake2.Arm.Stream.Update.len s₀ - VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) - 1) % blockBytes w + 1) := by
        rw [u₉.other .r11 (by decide), u₈.other .r11 (by decide), u₇.other .r11 (by decide),
          u₆.other .r11 (by decide), u₅.other .r11 (by decide), h4]
      have hrem' : VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀ + blockBytes w * VG.Proof.Blake2.Arm.Stream.Update.k₂ w s₀ + (((VG.Proof.Blake2.Arm.Stream.Update.len s₀ - VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) - 1) % blockBytes w + 1) =
          VG.Proof.Blake2.Arm.Stream.Update.len s₀ := by
        have := Nat.mod_le ((VG.Proof.Blake2.Arm.Stream.Update.len s₀ - VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) - 1) (blockBytes w)
        rw [ek]; omega
      have h12 : s₅.gpr .r12 = BitVec.ofNat 32 (blockBytes w * VG.Proof.Blake2.Arm.Stream.Update.k₂ w s₀) := by
        rw [u₅.gpr, h4, u₄.other .r7 (by decide), u₃.other .r7 (by decide), u₂.other .r7 (by decide), f₁.gpr,
          hC.r7, sub_ofNat (by have := Nat.mod_le ((VG.Proof.Blake2.Arm.Stream.Update.len s₀ - VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) - 1) (blockBytes w); omega), ek]
      have hk := VG.Proof.Blake2.Arm.Stream.Update.k₂_le (w := w) s₀
      have hBk : blockBytes w * VG.Proof.Blake2.Arm.Stream.Update.k₂ w s₀ < 2 ^ 32 := by omega
      have g₉ : ∀ x, x ≠ .r11 → x ≠ .r12 → x ≠ .r6 → x ≠ .r7 → x ≠ .r9 → x ≠ .r10 → s₉.gpr x = s.gpr x :=
        fun x h1 h2 h3 h4 h5 h6 => by
          rw [u₉.other x h6, u₈.other x h5, u₇.other x h4, u₆.other x h3, u₅.other x h2, u₄.other x h1,
            u₃.other x h1, u₂.other x h1, f₁.gpr]
      have h6 : s₉.gpr .r6 = VG.Proof.Blake2.Arm.Stream.Update.dp s₀ + BitVec.ofNat 32 (VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀ + blockBytes w * VG.Proof.Blake2.Arm.Stream.Update.k₂ w s₀) := by
        rw [u₉.other .r6 (by decide), u₈.other .r6 (by decide), u₇.other .r6 (by decide), u₆.gpr, h12,
          u₅.other .r6 (by decide), u₄.other .r6 (by decide), u₃.other .r6 (by decide),
          u₂.other .r6 (by decide), f₁.gpr, hC.r6, BitVec.add_assoc, ← BitVec.ofNat_add]
      have h7 : s₉.gpr .r7 = BitVec.ofNat 32 (VG.Proof.Blake2.Arm.Stream.Update.len s₀ - (VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀ + blockBytes w * VG.Proof.Blake2.Arm.Stream.Update.k₂ w s₀)) := by
        rw [u₉.other .r7 (by decide), u₈.other .r7 (by decide), u₇.gpr, u₆.other .r7 (by decide),
          u₆.other .r12 (by decide), h12, u₅.other .r7 (by decide), u₄.other .r7 (by decide),
          u₃.other .r7 (by decide), u₂.other .r7 (by decide), f₁.gpr, hC.r7, sub_ofNat (by omega), Nat.sub_sub]
      have hcn : s₉.gpr .r10 ++ s₉.gpr .r9 = BitVec.ofNat 64 (VG.Proof.Blake2.Arm.Stream.Update.cnt s₀ + (VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀ + blockBytes w * VG.Proof.Blake2.Arm.Stream.Update.k₂ w s₀)) := by
        rw [u₉.gpr, u₉.other .r9 (by decide), u₈.gpr, u₈.other .r10 (by decide), c₈, u₇.other .r9 (by decide),
          u₇.other .r10 (by decide), u₇.other .r12 (by decide), u₆.other .r9 (by decide),
          u₆.other .r10 (by decide), u₆.other .r12 (by decide), h12, u₅.other .r9 (by decide),
          u₅.other .r10 (by decide), u₄.other .r9 (by decide), u₄.other .r10 (by decide),
          u₃.other .r9 (by decide), u₃.other .r10 (by decide), u₂.other .r9 (by decide),
          u₂.other .r10 (by decide), f₁.gpr, VG.Proof.Blake2.Arm.Stream.add64_ofNat hC.cn hBk, Nat.add_assoc]
      have hm₉ : s₉.mem = s.mem := by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, f₁.mem]
      have hI₉ : VG.Proof.Blake2.Arm.Stream.Update.Inv P s₀ (VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀ + blockBytes w * VG.Proof.Blake2.Arm.Stream.Update.k₂ w s₀) 0 s₉ :=
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
      refine WP.mono (VG.Proof.Blake2.Arm.Stream.Update.copy_ok hP hp (by omega) (by omega) hI₉ h11)
        fun t ht => ⟨((VG.Proof.Blake2.Arm.Stream.Update.len s₀ - VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀) - 1) % blockBytes w + 1, fun h => by omega, ?_⟩
      rw [Nat.zero_add, hrem'] at ht
      exact ht
  · have := hp.scr_fit
    refine VG.Proof.Blake2.Arm.Stream.restore_ok hIt.r5 hp.scr_fit
      (fun d hd₁ hd₂ => ⟨VG.Proof.Blake2.Arm.Stream.Update.scR s₀, by simp [hIt.rd, hIt.wr, hp.wr], VG.Proof.Blake2.Arm.Stream.contains_off _ (by omega) (by omega)⟩) s₀.gpr
      hIt.saved fun s' hs hmem _ _ hsp => ⟨⟨VG.Proof.Blake2.Arm.Stream.preserved_of hs, by rw [hsp, hIt.sp]⟩, fun h0 d hr hc hlt => ?_⟩
    have hd : VG.Proof.Blake2.Arm.Stream.Update.R₀ P s₀ h0 d := ⟨hr, hc, hlt⟩
    rw [hmem]
    exact VG.Proof.Blake2.Arm.Stream.Update.final_repr hP hd hrf (hIt.repr h0 d hd)

/-! ## `update` -/

theorem correct (hP : VG.Proof.Blake2.Arm.Stream.Ok P) {name : String} {code : Prog isa} (hf : VG.Proof.Blake2.Arm.Stream.CalleeOk P code) {s₀ : VG.Arm.State}
    (hp : VG.Proof.Blake2.Arm.Stream.Update.Pre w s₀) :
    WP isa (VG.Impl.Blake2.Arm.Stream.update (w := w) name code) s₀ fun s' => abiPreserved s₀ s' ∧ (VG.Proof.Blake2.updateArm P).post s₀ s' :=
  WP.seq (WP.mono (VG.Proof.Blake2.Arm.Stream.Update.pro_ok hP hp) fun _ h₁ => WP.seq (WP.mono (VG.Proof.Blake2.Arm.Stream.Update.call₁_ok hP hf hp h₁) fun _ h₂ =>
    WP.seq (WP.mono (VG.Proof.Blake2.Arm.Stream.Update.mid_ok hP hp h₂) fun _ h₃ => WP.seq (WP.mono (VG.Proof.Blake2.Arm.Stream.Update.call₂_ok hP hf hp h₃) fun _ h₄ =>
      VG.Proof.Blake2.Arm.Stream.Update.end_ok hP hp h₄))))

end VG.Proof.Blake2.Arm.Stream.Update

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.Arm.Stream.Finalize`. -/
section

/-!
# Streaming BLAKE2 on ARMv7: `finalize`

The functional correctness of `finalize`, for either word size and any correct
compression function (`CalleeOk`), piece by piece, as for `update`: the
prologue, which zeroes the rest of the buffer and sets up the call (`pro_ok`),
the call (`call_ok'`) and the end, which copies the hash value to `out`
(`end_ok`).
-/

namespace VG.Proof.Blake2.Arm.Stream.Finalize

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Blake2.Arm.Stream (N B lbb saved save restore call zeroLoop finalizePro finalizeEnd finalize)
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_mov wp_add wp_sub wp_subs wp_cmp wp_ldr wp_str
  wp_ldrSp sub_ofNat cmp0 eval_eq eval_ne)
open VG.WriteBytes (writeBytes writeBytes_before writeBytes_frame)
open VG.Proof.Blake2 (bufLen bufLen_le bufLen_le_self final_eq stateAt_congr bytesAt_congr bytesAt_add
  bytesAt_state bytesAt_words wordBytes_readW finalizeArm countArm)
open VG.Proof.Blake2.Arm.Stream.Update (bufLen_ok)

variable {w : Nat} {P : VG.Spec.Blake2.Params w}

/-! ## The precondition -/

section
variable (s₀ : VG.Arm.State)

abbrev st : BitVec 32 := s₀.gpr .r0
abbrev stA : Addr := State.addr (VG.Proof.Blake2.Arm.Stream.Finalize.st s₀)
abbrev out : BitVec 32 := stackArg s₀ 0
abbrev outA : Addr := State.addr (VG.Proof.Blake2.Arm.Stream.Finalize.out s₀)
abbrev scr : BitVec 32 := stackArg s₀ 1
abbrev scA : Addr := State.addr (VG.Proof.Blake2.Arm.Stream.Finalize.scr s₀)
abbrev cnt : Nat := (VG.Proof.Blake2.countArm s₀).toNat
abbrev stR (w : Nat) : Region := ⟨VG.Proof.Blake2.Arm.Stream.Finalize.stA s₀, bufOff w + blockBytes w⟩
abbrev outR (w : Nat) : Region := ⟨VG.Proof.Blake2.Arm.Stream.Finalize.outA s₀, bufOff w⟩
abbrev scR : Region := ⟨VG.Proof.Blake2.Arm.Stream.Finalize.scA s₀, 576⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 8⟩
/-- The buffer. -/
abbrev buf (w : Nat) : Addr := VG.Proof.Blake2.Arm.Stream.Finalize.stA s₀ + BitVec.ofNat 64 (bufOff w)

end

structure Pre (w : Nat) (s₀ : VG.Arm.State) : Prop where
  rd : s₀.rd = [VG.Proof.Blake2.Arm.Stream.Finalize.argR s₀]
  wr : s₀.wr = [VG.Proof.Blake2.Arm.Stream.Finalize.stR s₀ w, VG.Proof.Blake2.Arm.Stream.Finalize.outR s₀ w, VG.Proof.Blake2.Arm.Stream.Finalize.scR s₀]
  st_out : (VG.Proof.Blake2.Arm.Stream.Finalize.stR s₀ w).Disjoint (VG.Proof.Blake2.Arm.Stream.Finalize.outR s₀ w)
  st_scr : (VG.Proof.Blake2.Arm.Stream.Finalize.stR s₀ w).Disjoint (VG.Proof.Blake2.Arm.Stream.Finalize.scR s₀)
  out_scr : (VG.Proof.Blake2.Arm.Stream.Finalize.outR s₀ w).Disjoint (VG.Proof.Blake2.Arm.Stream.Finalize.scR s₀)
  a_st : (VG.Proof.Blake2.Arm.Stream.Finalize.argR s₀).Disjoint (VG.Proof.Blake2.Arm.Stream.Finalize.stR s₀ w)
  a_out : (VG.Proof.Blake2.Arm.Stream.Finalize.argR s₀).Disjoint (VG.Proof.Blake2.Arm.Stream.Finalize.outR s₀ w)
  a_scr : (VG.Proof.Blake2.Arm.Stream.Finalize.argR s₀).Disjoint (VG.Proof.Blake2.Arm.Stream.Finalize.scR s₀)
  w_st : (VG.Proof.Blake2.Arm.Stream.below s₀).Disjoint (VG.Proof.Blake2.Arm.Stream.Finalize.stR s₀ w)
  w_out : (VG.Proof.Blake2.Arm.Stream.below s₀).Disjoint (VG.Proof.Blake2.Arm.Stream.Finalize.outR s₀ w)
  w_scr : (VG.Proof.Blake2.Arm.Stream.below s₀).Disjoint (VG.Proof.Blake2.Arm.Stream.Finalize.scR s₀)
  st_fit : (VG.Proof.Blake2.Arm.Stream.Finalize.st s₀).toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32
  out_fit : (VG.Proof.Blake2.Arm.Stream.Finalize.out s₀).toNat + bufOff w ≤ 2 ^ 32
  scr_fit : (VG.Proof.Blake2.Arm.Stream.Finalize.scr s₀).toNat + 576 ≤ 2 ^ 32
  sp16 : 16 ≤ s₀.sp.toNat
  sp_fit : s₀.sp.toNat + 8 ≤ 2 ^ 32

theorem pre_of {s₀ : VG.Arm.State} (h : (VG.Proof.Blake2.finalizeArm P).pre s₀) : VG.Proof.Blake2.Arm.Stream.Finalize.Pre w s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

theorem cnt_lt (s₀ : VG.Arm.State) : VG.Proof.Blake2.Arm.Stream.Finalize.cnt s₀ < 2 ^ 64 := (VG.Proof.Blake2.countArm s₀).isLt

/-- What holds throughout. -/
structure Common (w : Nat) (s₀ : VG.Arm.State) (s : VG.Arm.State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r4 : s.gpr .r4 = VG.Proof.Blake2.Arm.Stream.Finalize.st s₀
  r5 : s.gpr .r5 = VG.Proof.Blake2.Arm.Stream.Finalize.scr s₀
  r6 : s.gpr .r6 = VG.Proof.Blake2.Arm.Stream.Finalize.out s₀
  cn : s.gpr .r10 ++ s.gpr .r9 = BitVec.ofNat 64 (VG.Proof.Blake2.Arm.Stream.Finalize.cnt s₀)
  frame : Frame [VG.Proof.Blake2.Arm.Stream.Finalize.stR s₀ w, VG.Proof.Blake2.Arm.Stream.Finalize.scR s₀, VG.Proof.Blake2.Arm.Stream.below s₀] s₀.mem s.mem
  saved : VG.Proof.Blake2.Arm.Stream.Saved (VG.Proof.Blake2.Arm.Stream.Finalize.scA s₀) s₀.gpr s.mem

/-- The registers `Common` is about. -/
abbrev commonRegs : List Reg := [.r4, .r5, .r6, .r9, .r10]

theorem Common.of_gpr {s₀ : VG.Arm.State} {s s' : VG.Arm.State} (h : VG.Proof.Blake2.Arm.Stream.Finalize.Common w s₀ s)
    (hg : ∀ r ∈ VG.Proof.Blake2.Arm.Stream.Finalize.commonRegs, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) :
    VG.Proof.Blake2.Arm.Stream.Finalize.Common w s₀ s' where
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  sp := hsp.trans h.sp
  r4 := by rw [hg _ (by simp)]; exact h.r4
  r5 := by rw [hg _ (by simp)]; exact h.r5
  r6 := by rw [hg _ (by simp)]; exact h.r6
  cn := by rw [hg .r9 (by simp), hg .r10 (by simp)]; exact h.cn
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

theorem Common.of_upd {s₀ : VG.Arm.State} {s s' : VG.Arm.State} (h : VG.Proof.Blake2.Arm.Stream.Finalize.Common w s₀ s) {d : Reg} {v : BitVec 32}
    (u : Upd s s' d v) (hd : d ∉ VG.Proof.Blake2.Arm.Stream.Finalize.commonRegs := by decide) : VG.Proof.Blake2.Arm.Stream.Finalize.Common w s₀ s' :=
  h.of_gpr (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem u.rd u.wr u.sp

theorem saved_frame {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.Arm.Stream.Finalize.Pre w s₀) {m m' : Mem} (h : VG.Proof.Blake2.Arm.Stream.Saved (VG.Proof.Blake2.Arm.Stream.Finalize.scA s₀) s₀.gpr m)
    (hf : Frame [VG.Proof.Blake2.Arm.Stream.Finalize.stR s₀ w, ⟨VG.Proof.Blake2.Arm.Stream.Finalize.scA s₀, 512⟩, VG.Proof.Blake2.Arm.Stream.below s₀] m m') : VG.Proof.Blake2.Arm.Stream.Saved (VG.Proof.Blake2.Arm.Stream.Finalize.scA s₀) s₀.gpr m' := by
  have := hp.scr_fit
  refine h.frame VG.Proof.Blake2.Arm.Stream.saved_slots hf fun r' hr' => ?_
  have e : Region.Sub ⟨VG.Proof.Blake2.Arm.Stream.Finalize.scA s₀ + BitVec.ofNat 64 512, 548 - 512⟩ (VG.Proof.Blake2.Arm.Stream.Finalize.scR s₀) := Offset.sub_base _ (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl
  · exact hp.st_scr.symm.sub_left e
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · exact hp.w_scr.symm.sub_left e

/-! ## The prologue -/

abbrev prologue : List Instr :=
  [.ldrSp .r12 4] ++ save .r12 ++ [.mov .r4 (.reg .r0), .mov .r5 (.reg .r12), .ldrSp .r6 0,
    .mov .r9 (.reg .r2), .mov .r10 (.reg .r3)]

theorem argAddr_eq {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.Arm.Stream.Finalize.Pre w s₀) {k : Nat} (hk : k < 2) :
    stackArgAddr s₀ k = stackArgAddr s₀ 0 + BitVec.ofNat 64 (4 * k) := by
  have := hp.sp_fit
  simp only [stackArgAddr]
  rw [addr_add (by omega)]
  simp

theorem arg_in {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.Arm.Stream.Finalize.Pre w s₀) {k : Nat} (hk : k < 2) :
    InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ k) 4 :=
  ⟨VG.Proof.Blake2.Arm.Stream.Finalize.argR s₀, by simp [hp.rd], by rw [VG.Proof.Blake2.Arm.Stream.Finalize.argAddr_eq hp hk]; exact VG.Proof.Blake2.Arm.Stream.contains_off _ (by omega) (by omega)⟩

theorem arg_sub {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.Arm.Stream.Finalize.Pre w s₀) {k : Nat} (hk : k < 2) :
    Region.Sub ⟨stackArgAddr s₀ k, 4⟩ (VG.Proof.Blake2.Arm.Stream.Finalize.argR s₀) := by
  rw [VG.Proof.Blake2.Arm.Stream.Finalize.argAddr_eq hp hk]; exact Offset.sub_base _ (by omega)

theorem prologue_ok {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.Arm.Stream.Finalize.Pre w s₀) :
    WP isa (.block VG.Proof.Blake2.Arm.Stream.Finalize.prologue) s₀ fun s => VG.Proof.Blake2.Arm.Stream.Finalize.Common w s₀ s ∧
      ∀ i < bufOff w + blockBytes w, s.mem (VG.Proof.Blake2.Arm.Stream.Finalize.stA s₀ + BitVec.ofNat 64 i) = s₀.mem (VG.Proof.Blake2.Arm.Stream.Finalize.stA s₀ + BitVec.ofNat 64 i) := by
  have hsc := hp.scr_fit
  simp only [VG.Proof.Blake2.Arm.Stream.Finalize.prologue, List.cons_append, List.nil_append]
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) rfl (VG.Proof.Blake2.Arm.Stream.Finalize.arg_in hp (by decide)) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = VG.Proof.Blake2.Arm.Stream.Finalize.scr s₀ := u₁.gpr
  refine VG.Proof.Blake2.Arm.Stream.save_ok (by rw [h12]; omega) (fun d hd₁ hd₂ => ⟨VG.Proof.Blake2.Arm.Stream.Finalize.scR s₀, by simp [u₁.wr, hp.wr],
    by rw [h12]; exact VG.Proof.Blake2.Arm.Stream.contains_off _ (by omega) (by omega)⟩) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  have hframe : Frame [VG.Proof.Blake2.Arm.Stream.Finalize.scR s₀] s₀.mem s₂.mem := by
    rw [m₂, u₁.mem, h12]; exact VG.Proof.Blake2.Arm.Stream.saveMem_frame _ _ _
  have harg : ∀ k, k < 2 → s₂.mem.readW (stackArgAddr s₀ k) 32 = stackArg s₀ k := fun k hk =>
    hframe.readW (Region.contains_self _ _) (by simpa using (hp.a_scr.sub_left (VG.Proof.Blake2.Arm.Stream.Finalize.arg_sub hp hk))) (by decide)
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide)
    (by rw [u₄.sp, u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]; exact VG.Proof.Blake2.Arm.Stream.Finalize.arg_in hp (by decide)) fun s₅ u₅ => ?_
  refine wp_mov (op2_reg _ _) fun s₆ u₆ => wp_mov (op2_reg _ _) fun s₇ u₇ => WP.block_nil ?_
  have mm : s₇.mem = s₂.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  refine ⟨⟨by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd],
    by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr],
    by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp], ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, g₂, u₁.other _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), g₂, h12]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, harg 0 (by decide)]
  · have h9 : s₇.gpr .r9 = s₀.gpr .r2 := by
      rw [u₇.other .r9 (by decide), u₆.gpr, u₅.other .r2 (by decide), u₄.other .r2 (by decide),
        u₃.other .r2 (by decide), g₂, u₁.other .r2 (by decide)]
    have h10 : s₇.gpr .r10 = s₀.gpr .r3 := by
      rw [u₇.gpr, u₆.other .r3 (by decide), u₅.other .r3 (by decide), u₄.other .r3 (by decide),
        u₃.other .r3 (by decide), g₂, u₁.other .r3 (by decide)]
    rw [h9, h10, VG.Proof.Blake2.Arm.Stream.Finalize.cnt, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rfl
  · rw [mm]; exact hframe.mono (by simp)
  · intro p hp'
    rw [mm, m₂, u₁.mem, h12, VG.Proof.Blake2.Arm.Stream.saveMem_saved _ _ _ p hp', u₁.other _ (Ne.symm ?_)]
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
  · intro i hi
    rw [mm]
    exact hframe.bytes (R := VG.Proof.Blake2.Arm.Stream.Finalize.stR s₀ w) (by simpa using hp.st_scr)
      (by show bufOff w + blockBytes w ≤ 2 ^ 64; have := hp.st_fit; omega) hi

/-! ## Padding the buffer with zeros -/

/-- The state, with its buffer padded: the hash value and the first `r`
bytes of the buffer as on entry, then zeros. -/
structure Padded (w : Nat) (s₀ : VG.Arm.State) (s : VG.Arm.State) : Prop extends VG.Proof.Blake2.Arm.Stream.Finalize.Common w s₀ s where
  st : stateAt w s.mem (VG.Proof.Blake2.Arm.Stream.Finalize.stA s₀) = stateAt w s₀.mem (VG.Proof.Blake2.Arm.Stream.Finalize.stA s₀)
  buf : VG.Spec.Blake2.bytesAt s.mem (VG.Proof.Blake2.Arm.Stream.Finalize.buf s₀ w) (blockBytes w) =
    VG.Spec.Blake2.bytesAt s₀.mem (VG.Proof.Blake2.Arm.Stream.Finalize.buf s₀ w) (bufLen w (VG.Proof.Blake2.Arm.Stream.Finalize.cnt s₀)) ++ List.replicate (blockBytes w - bufLen w (VG.Proof.Blake2.Arm.Stream.Finalize.cnt s₀)) 0

theorem pad_ok (hP : VG.Proof.Blake2.Arm.Stream.Ok P) {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.Arm.Stream.Finalize.Pre w s₀) {s : VG.Arm.State} (hC : VG.Proof.Blake2.Arm.Stream.Finalize.Common w s₀ s)
    (hst : ∀ i < bufOff w + blockBytes w, s.mem (VG.Proof.Blake2.Arm.Stream.Finalize.stA s₀ + BitVec.ofNat 64 i) = s₀.mem (VG.Proof.Blake2.Arm.Stream.Finalize.stA s₀ + BitVec.ofNat 64 i))
    (h8 : s.gpr .r8 = BitVec.ofNat 32 (bufLen w (VG.Proof.Blake2.Arm.Stream.Finalize.cnt s₀))) {rest : Prog isa} {Q : VG.Arm.State → Prop}
    (k : ∀ t, VG.Proof.Blake2.Arm.Stream.Finalize.Padded w s₀ t → WP isa rest t Q) :
    WP isa (.seq (.block [.mov .r12 (.imm 0), .mov .r11 (.imm (BitVec.ofNat 32 (B w))), .subs .r11 .r11 (.reg .r8)])
      (.seq (.ite .eq (.block []) (zeroLoop (w := w))) rest)) s Q := by
  have hl := hP.len
  have hst' := hp.st_fit
  have hr := bufLen_le (w := w) hP.pos (VG.Proof.Blake2.Arm.Stream.Finalize.cnt s₀)
  obtain ⟨r, hrr⟩ : ∃ r, r = bufLen w (VG.Proof.Blake2.Arm.Stream.Finalize.cnt s₀) := ⟨_, rfl⟩
  rw [← hrr] at h8 hr
  refine WP.seq (wp_mov (op2_imm (by decide)) fun s₁ u₁ => wp_mov (op2_imm hP.encB) fun s₂ u₂ =>
    wp_subs (op2_reg _ _) fun s₃ u₃ z₃ => WP.block_nil ?_)
  have hC₃ : VG.Proof.Blake2.Arm.Stream.Finalize.Common w s₀ s₃ := ((hC.of_upd u₁).of_upd u₂).of_upd u₃
  have hm₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have h11 : s₃.gpr .r11 = BitVec.ofNat 32 (blockBytes w - r) := by
    rw [u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h8, VG.Proof.Blake2.Arm.Stream.B_eq, sub_ofNat hr]
  have hz : isa.eval .eq s₃ = some (decide (blockBytes w - r = 0)) := by
    show VG.Arm.eval .eq s₃ = _
    rw [eval_eq, z₃, ← u₃.gpr, h11, MdStream.Arm.ofNat_beq_zero (by omega)]
  -- The facts about the bytes, from the memory after zeroing `k` bytes.
  have hpad : ∀ m : Mem, m = VG.WriteBytes.writeBytes s.mem (VG.Proof.Blake2.Arm.Stream.Finalize.buf s₀ w + BitVec.ofNat 64 r) (List.replicate (blockBytes w - r) 0) →
      Frame [VG.Proof.Blake2.Arm.Stream.Finalize.stR s₀ w] s.mem m ∧ stateAt w m (VG.Proof.Blake2.Arm.Stream.Finalize.stA s₀) = stateAt w s₀.mem (VG.Proof.Blake2.Arm.Stream.Finalize.stA s₀) ∧
      VG.Spec.Blake2.bytesAt m (VG.Proof.Blake2.Arm.Stream.Finalize.buf s₀ w) (blockBytes w) =
        VG.Spec.Blake2.bytesAt s₀.mem (VG.Proof.Blake2.Arm.Stream.Finalize.buf s₀ w) r ++ List.replicate (blockBytes w - r) 0 := by
    intro m hm
    have hwf : Frame [VG.Proof.Blake2.Arm.Stream.Finalize.stR s₀ w] s.mem m := by
      rw [hm, Offset.add_add]
      exact VG.WriteBytes.writeBytes_frame _ _ _ (by simp only [List.length_replicate]; exact VG.Proof.Blake2.Arm.Stream.contains_off _ (by omega) (by omega))
    refine ⟨hwf, ?_, ?_⟩
    · rw [hm, Offset.add_add]
      refine (stateAt_congr fun i hi => ?_).trans (stateAt_congr fun i hi => hst i (by omega))
      exact VG.WriteBytes.writeBytes_before _ _ _ (by omega) (by simp; omega)
    · have := Arm.Stream.bytesAt_writeBytes s.mem (VG.Proof.Blake2.Arm.Stream.Finalize.buf s₀ w) r (List.replicate (blockBytes w - r) 0)
        (by simp; omega)
      simp only [List.length_replicate, show r + (blockBytes w - r) = blockBytes w by omega] at this
      rw [hm, this]
      refine congrArg (· ++ _) (bytesAt_congr fun i hi => ?_)
      rw [Offset.add_add]; exact hst _ (by omega)
  refine WP.seq (WP.mono (Q := VG.Proof.Blake2.Arm.Stream.Finalize.Padded w s₀) (WP.ite _ hz (fun hb => ?_) (fun hb => ?_)) k)
  · simp only [decide_eq_true_eq] at hb
    obtain ⟨hwf, h1, h2⟩ := hpad s₃.mem (by rw [hm₃, hb, List.replicate_zero, WriteBytes.writeBytes_nil])
    exact WP.block_nil ⟨hC₃, h1, by rw [← hrr]; exact h2⟩
  · simp only [decide_eq_false_iff_not] at hb
    refine VG.Proof.Blake2.Arm.Stream.zeroLoop_ok (st := VG.Proof.Blake2.Arm.Stream.Finalize.st s₀) (r := r) (k := blockBytes w - r) hl.2.1 (by omega) (by omega) (hC₃.r4) (by
      rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h8]) h11
      (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr])
      (fun i hi => ⟨VG.Proof.Blake2.Arm.Stream.Finalize.stR s₀ w, by simp [hC₃.wr, hp.wr], by
        rw [Offset.add_add]; exact VG.Proof.Blake2.Arm.Stream.contains_off _ (by omega) (by omega)⟩) fun s' h => ?_
    have hm' : s'.mem = VG.WriteBytes.writeBytes s.mem (VG.Proof.Blake2.Arm.Stream.Finalize.buf s₀ w + BitVec.ofNat 64 r) (List.replicate (blockBytes w - r) 0) := by
      rw [h.mem, hm₃, Offset.add_add]
    obtain ⟨hwf, h1, h2⟩ := hpad s'.mem hm'
    have hg : ∀ x ∈ VG.Proof.Blake2.Arm.Stream.Finalize.commonRegs, s'.gpr x = s₃.gpr x := fun x hx => h.other x
      (fun e => by subst e; simp at hx) (fun e => by subst e; simp at hx) (fun e => by subst e; simp at hx)
    refine ⟨⟨h.rd.trans hC₃.rd, h.wr.trans hC₃.wr, h.sp.trans hC₃.sp, by rw [hg _ (by simp)]; exact hC₃.r4,
      by rw [hg _ (by simp)]; exact hC₃.r5, by rw [hg _ (by simp)]; exact hC₃.r6,
      by rw [hg .r9 (by simp), hg .r10 (by simp)]; exact hC₃.cn,
      hC.frame.trans (hwf.mono (by simp)), VG.Proof.Blake2.Arm.Stream.Finalize.saved_frame hp hC.saved (hwf.mono (by simp))⟩, h1,
      by rw [← hrr]; exact h2⟩

/-! ## Up to the call -/

/-- What holds before the call. -/
def PostPro (w : Nat) (s₀ s : VG.Arm.State) : Prop :=
  VG.Proof.Blake2.Arm.Stream.Finalize.Padded w s₀ s ∧
    VG.Proof.Blake2.Arm.Stream.CallArgs (w := w) s (VG.Proof.Blake2.Arm.Stream.Finalize.st s₀) (VG.Proof.Blake2.Arm.Stream.Finalize.scr s₀) (VG.Proof.Blake2.Arm.Stream.Finalize.st s₀ + BitVec.ofNat 32 (bufOff w)) 1 (BitVec.ofNat 64 (VG.Proof.Blake2.Arm.Stream.Finalize.cnt s₀)) 1

theorem pro_ok (hP : VG.Proof.Blake2.Arm.Stream.Ok P) {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.Arm.Stream.Finalize.Pre w s₀) :
    WP isa (finalizePro (w := w)) s₀ (VG.Proof.Blake2.Arm.Stream.Finalize.PostPro w s₀) := by
  have hl := hP.len
  have hst := hp.st_fit; have hsc := hp.scr_fit
  unfold finalizePro
  refine WP.seq (WP.mono (VG.Proof.Blake2.Arm.Stream.Finalize.prologue_ok hp) fun s₁ ⟨hC, hstb⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Blake2.Arm.Stream.Update.bufLen_ok hP (VG.Proof.Blake2.Arm.Stream.Finalize.cnt_lt s₀) hC.cn) fun s₂ ⟨h8, g, m, rd, wr, sp⟩ => ?_)
  have hC₂ := hC.of_gpr (fun r hr => g r (fun e => by subst e; simp at hr) (fun e => by subst e; simp at hr))
    m rd wr sp
  refine VG.Proof.Blake2.Arm.Stream.Finalize.pad_ok hP hp hC₂ (fun i hi => by rw [m]; exact hstb i hi) h8 fun s₃ hP₃ => ?_
  refine wp_mov (op2_reg _ _) fun s₄ u₄ => wp_add (op2_imm hP.encN) fun s₅ u₅ =>
    wp_mov (op2_imm (by decide)) fun s₆ u₆ => wp_mov (op2_reg _ _) fun s₇ u₇ =>
    wp_mov (op2_reg _ _) fun s₈ u₈ => wp_mov (op2_imm (by decide)) fun s₉ u₉ =>
    wp_mov (op2_reg _ _) fun s₁₀ u₁₀ => WP.block_nil ?_
  have hC' : VG.Proof.Blake2.Arm.Stream.Finalize.Common w s₀ s₁₀ :=
    ((((((hP₃.toCommon.of_upd u₄).of_upd u₅).of_upd u₆).of_upd u₇).of_upd u₈).of_upd u₉).of_upd u₁₀
  have hm : s₁₀.mem = s₃.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  refine ⟨⟨hC', by rw [hm]; exact hP₃.st, by rw [hm]; exact hP₃.buf⟩, ?_⟩
  have eN : Region.Sub ⟨VG.Proof.Blake2.Arm.Stream.Finalize.stA s₀, bufOff w⟩ (VG.Proof.Blake2.Arm.Stream.Finalize.stR s₀ w) := Region.sub_prefix (by omega)
  have eS : Region.Sub ⟨VG.Proof.Blake2.Arm.Stream.Finalize.scA s₀, 512⟩ (VG.Proof.Blake2.Arm.Stream.Finalize.scR s₀) := Region.sub_prefix (by omega)
  have eB : Region.Sub ⟨State.addr (VG.Proof.Blake2.Arm.Stream.Finalize.st s₀ + BitVec.ofNat 32 (bufOff w)), blockBytes w * 1⟩ (VG.Proof.Blake2.Arm.Stream.Finalize.stR s₀ w) := by
    rw [addr_add (by omega), Nat.mul_one]; exact Offset.sub_base _ (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by decide, by rw [hC'.sp]; exact hp.sp16, ?_, ?_,
    (hp.st_scr.sub_left eN).sub_right eS, ?_, (hp.st_scr.sub_left eB).sub_right eS, ?_, ?_, ?_, by omega,
    by rw [VG.Proof.Blake2.Arm.Stream.toNat_add_ofNat (by omega)]; omega, by omega⟩
  all_goals try simp only [u₁₀.gpr, u₁₀.other, u₉.gpr, u₉.other, u₈.gpr, u₈.other, u₇.gpr, u₇.other, u₆.gpr,
    u₆.other, u₅.gpr, u₅.other, u₄.gpr, u₄.other, ne_eq, reduceCtorEq, not_false_eq_true, hP₃.r4, hP₃.r5, VG.Proof.Blake2.Arm.Stream.N_eq]
  all_goals first | rfl | exact hP₃.cn | skip
  · rw [hC'.rd, hC'.wr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨VG.Proof.Blake2.Arm.Stream.Finalize.stR s₀ w, by simp, bufOff w, addr_add (by omega), by dsimp only; omega⟩
  · rw [hC'.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.Blake2.Arm.Stream.Finalize.stR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨VG.Proof.Blake2.Arm.Stream.Finalize.scR s₀, by simp, 0, by simp, by simp⟩
  · rw [addr_add (by omega), Nat.mul_one]; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega)
  · rw [VG.Proof.Blake2.Arm.Stream.below, hC'.sp]; exact hp.w_st.sub_right eN
  · rw [VG.Proof.Blake2.Arm.Stream.below, hC'.sp]; exact hp.w_st.sub_right eB
  · rw [VG.Proof.Blake2.Arm.Stream.below, hC'.sp]; exact hp.w_scr.sub_right eS

/-! ## The call -/

/-- What holds after the call. -/
def Mid (P : VG.Spec.Blake2.Params w) (s₀ s : VG.Arm.State) : Prop :=
  VG.Proof.Blake2.Arm.Stream.Finalize.Common w s₀ s ∧ ∀ h0 d, Spec.Blake2.Repr P h0 s₀.mem (VG.Proof.Blake2.Arm.Stream.Finalize.stA s₀) d → d.length < 2 ^ 64 →
    VG.Proof.Blake2.countArm s₀ = BitVec.ofNat 64 d.length →
    (stateAt w s.mem (VG.Proof.Blake2.Arm.Stream.Finalize.stA s₀)).toList.flatMap wordBytes = finalHash P h0 d

theorem call_ok' (hP : VG.Proof.Blake2.Arm.Stream.Ok P) {name : String} {code : Prog isa} (hf : VG.Proof.Blake2.Arm.Stream.CalleeOk P code) {s₀ : VG.Arm.State}
    (hp : VG.Proof.Blake2.Arm.Stream.Finalize.Pre w s₀) {s : VG.Arm.State} (h : VG.Proof.Blake2.Arm.Stream.Finalize.PostPro w s₀ s) : WP isa (call name code) s (VG.Proof.Blake2.Arm.Stream.Finalize.Mid P s₀) := by
  have hl := hP.len
  have hst := hp.st_fit; have hsc := hp.scr_fit
  obtain ⟨hpd, hca⟩ := h
  refine VG.Proof.Blake2.Arm.Stream.call_ok hf hca fun s' ha hstate => ⟨?_, fun h0 d hr hl' hc => ?_⟩
  · have hf' : Frame [VG.Proof.Blake2.Arm.Stream.Finalize.stR s₀ w, ⟨VG.Proof.Blake2.Arm.Stream.Finalize.scA s₀, 512⟩, VG.Proof.Blake2.Arm.Stream.below s₀] s.mem s'.mem := by
      have := ha.frame
      rw [VG.Proof.Blake2.Arm.Stream.below, hpd.sp] at this
      exact this.sub fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨VG.Proof.Blake2.Arm.Stream.Finalize.stR s₀ w, by simp, Region.sub_prefix (by omega)⟩
        · exact ⟨⟨VG.Proof.Blake2.Arm.Stream.Finalize.scA s₀, 512⟩, by simp, fun _ h => h⟩
        · exact ⟨VG.Proof.Blake2.Arm.Stream.below s₀, by simp, fun _ h => h⟩
    have hcp : ∀ r ∈ VG.Proof.Blake2.Arm.Stream.Finalize.commonRegs, r ∈ preserved ∧ r ≠ .lr := by decide
    have hg : ∀ r ∈ VG.Proof.Blake2.Arm.Stream.Finalize.commonRegs, s'.gpr r = s.gpr r := fun r hr => ha.cs r (hcp r hr).1 (hcp r hr).2
    exact ⟨ha.rd.trans hpd.rd, ha.wr.trans hpd.wr, ha.sp.trans hpd.sp, by rw [hg _ (by simp)]; exact hpd.r4,
      by rw [hg _ (by simp)]; exact hpd.r5, by rw [hg _ (by simp)]; exact hpd.r6,
      by rw [hg .r9 (by simp), hg .r10 (by simp)]; exact hpd.cn,
      hpd.frame.trans (hf'.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨VG.Proof.Blake2.Arm.Stream.Finalize.stR s₀ w, by simp, fun _ h => h⟩
        · exact ⟨VG.Proof.Blake2.Arm.Stream.Finalize.scR s₀, by simp, Region.sub_prefix (by omega)⟩
        · exact ⟨VG.Proof.Blake2.Arm.Stream.below s₀, by simp, fun _ h => h⟩),
      VG.Proof.Blake2.Arm.Stream.Finalize.saved_frame hp hpd.saved hf'⟩
  · have ecnt : VG.Proof.Blake2.Arm.Stream.Finalize.cnt s₀ = d.length := by
      rw [VG.Proof.Blake2.Arm.Stream.Finalize.cnt, hc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl']
    rw [hstate, Update.compressBlocks_one, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (VG.Proof.Blake2.Arm.Stream.Finalize.cnt_lt s₀), ecnt,
      addr_add (by omega)]
    refine final_eq P hP.pos hr hpd.st ?_
    rw [← ecnt]; exact hpd.buf

/-! ## The end -/

/-- Copying the first `n` words of the hash value to `out`. -/
structure CopyW (s₀ s : VG.Arm.State) (n : Nat) (s' : VG.Arm.State) : Prop where
  other : ∀ r, r ≠ .r12 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  frame : Frame [VG.Proof.Blake2.Arm.Stream.Finalize.outR s₀ w] s.mem s'.mem
  words : ∀ j < n, s'.mem.readW (VG.Proof.Blake2.Arm.Stream.Finalize.outA s₀ + BitVec.ofNat 64 (4 * j)) 32 =
    s.mem.readW (VG.Proof.Blake2.Arm.Stream.Finalize.stA s₀ + BitVec.ofNat 64 (4 * j)) 32

theorem copyW_all (hP : VG.Proof.Blake2.Arm.Stream.Ok P) {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.Arm.Stream.Finalize.Pre w s₀) {s : VG.Arm.State} (hC : VG.Proof.Blake2.Arm.Stream.Finalize.Common w s₀ s) :
    ∀ n ≤ bufOff w / 4, WP isa (.block ((List.range n).flatMap
      (fun k => [.ldr .r12 .r4 (4 * k), .str .r12 .r6 (4 * k)]))) s (VG.Proof.Blake2.Arm.Stream.Finalize.CopyW (w := w) s₀ s n) := by
  have hl := hP.len
  have hst := hp.st_fit; have hof := hp.out_fit
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t h => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have h4 : t.gpr .r4 = VG.Proof.Blake2.Arm.Stream.Finalize.st s₀ := by rw [h.other _ (by decide), hC.r4]
    have h6 : t.gpr .r6 = VG.Proof.Blake2.Arm.Stream.Finalize.out s₀ := by rw [h.other _ (by decide), hC.r6]
    refine wp_ldr (a := VG.Proof.Blake2.Arm.Stream.Finalize.stA s₀ + BitVec.ofNat 64 (4 * n)) (by omega) (by rw [h4, addr_add (by omega)])
      ⟨VG.Proof.Blake2.Arm.Stream.Finalize.stR s₀ w, by simp [h.rd, h.wr, hC.rd, hC.wr, hp.wr], VG.Proof.Blake2.Arm.Stream.contains_off _ (by omega) (by omega)⟩
      fun t₁ u₁ => ?_
    refine wp_str (a := VG.Proof.Blake2.Arm.Stream.Finalize.outA s₀ + BitVec.ofNat 64 (4 * n)) (by omega)
      (by rw [u₁.other _ (by decide), h6, addr_add (by omega)])
      ⟨VG.Proof.Blake2.Arm.Stream.Finalize.outR s₀ w, by simp [u₁.wr, h.wr, hC.wr, hp.wr], VG.Proof.Blake2.Arm.Stream.contains_off _ (by omega) (by omega)⟩
      fun t₂ u₂ => WP.block_nil ?_
    have hfw : Frame [VG.Proof.Blake2.Arm.Stream.Finalize.outR s₀ w] t.mem t₂.mem := by
      rw [u₂.mem, u₁.mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Proof.Blake2.Arm.Stream.contains_off _ (by omega) (by omega))
    -- The state is not in `out`.
    have hsb : ∀ j < bufOff w / 4, t.mem.readW (VG.Proof.Blake2.Arm.Stream.Finalize.stA s₀ + BitVec.ofNat 64 (4 * j)) 32 =
        s.mem.readW (VG.Proof.Blake2.Arm.Stream.Finalize.stA s₀ + BitVec.ofNat 64 (4 * j)) 32 := fun j hj =>
      h.frame.readW (r := ⟨VG.Proof.Blake2.Arm.Stream.Finalize.stA s₀ + BitVec.ofNat 64 (4 * j), 4⟩) (Region.contains_self _ _)
        (by simp only [List.mem_singleton]; rintro r rfl
            exact hp.st_out.sub_left (Offset.sub_base _ (by omega))) (by decide)
    refine ⟨fun r hr => by rw [u₂.gpr, u₁.other r hr, h.other r hr], by rw [u₂.rd, u₁.rd, h.rd],
      by rw [u₂.wr, u₁.wr, h.wr], by rw [u₂.sp, u₁.sp, h.sp], h.frame.trans hfw, fun j hj => ?_⟩
    rw [u₂.mem, u₁.mem, u₁.gpr]
    by_cases e : j = n
    · subst e; rw [Mem.readW_writeW_self32, hsb j (by omega)]
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact h.words j (by omega)

theorem end_ok (hP : VG.Proof.Blake2.Arm.Stream.Ok P) {s₀ : VG.Arm.State} (hp : VG.Proof.Blake2.Arm.Stream.Finalize.Pre w s₀) {s : VG.Arm.State} (h : VG.Proof.Blake2.Arm.Stream.Finalize.Mid P s₀ s) :
    WP isa (.block (finalizeEnd (w := w))) s fun s' => abiPreserved s₀ s' ∧ (VG.Proof.Blake2.finalizeArm P).post s₀ s' := by
  have hl := hP.len
  have hst := hp.st_fit; have hof := hp.out_fit; have hsc := hp.scr_fit
  obtain ⟨hC, hfin⟩ := h
  unfold finalizeEnd
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Blake2.Arm.Stream.Finalize.copyW_all hP hp hC _ (Nat.le_refl _)) fun t ht => ?_
  have h5 : t.gpr .r5 = VG.Proof.Blake2.Arm.Stream.Finalize.scr s₀ := by rw [ht.other _ (by decide), hC.r5]
  have hsv : VG.Proof.Blake2.Arm.Stream.Saved (VG.Proof.Blake2.Arm.Stream.Finalize.scA s₀) s₀.gpr t.mem := by
    intro p hp'
    have hoff := VG.Proof.Blake2.Arm.Stream.saved_bound p hp'
    rw [← hC.saved p hp']
    refine ht.frame.readW (r := ⟨VG.Proof.Blake2.Arm.Stream.Finalize.scA s₀ + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_singleton]; rintro r rfl
    exact hp.out_scr.symm.sub_left (Offset.sub_base _ (by omega))
  refine VG.Proof.Blake2.Arm.Stream.restore_ok h5 hsc (fun d hd₁ hd₂ => ⟨VG.Proof.Blake2.Arm.Stream.Finalize.scR s₀, by simp [ht.rd, ht.wr, hC.rd, hC.wr, hp.wr],
      VG.Proof.Blake2.Arm.Stream.contains_off _ (by omega) (by omega)⟩) s₀.gpr hsv
    fun s' hs hmem _ _ hsp => ⟨⟨VG.Proof.Blake2.Arm.Stream.preserved_of hs, by rw [hsp, ht.sp, hC.sp]⟩, fun h0 d hr hl' hc => ?_⟩
  rw [← hfin h0 d hr hl' hc, ← bytesAt_state _ _ (by rcases hP.w with h | h <;> simp [h]), hmem]
  -- The words of `out` are those of the hash value.
  have e4 : bufOff w = 4 * (bufOff w / 4) := by omega
  rw [e4, show (4 : Nat) = 32 / 8 from rfl, bytesAt_words, bytesAt_words]
  rw [List.flatMap, List.flatMap]
  refine congrArg _ (List.map_congr_left fun j hj => ?_)
  have hj := List.mem_range.mp hj
  rw [← wordBytes_readW _ _ (.inl rfl), ← wordBytes_readW _ _ (.inl rfl)]
  exact congrArg _ (ht.words j hj)

/-! ## `finalize` -/

theorem correct (hP : VG.Proof.Blake2.Arm.Stream.Ok P) {name : String} {code : Prog isa} (hf : VG.Proof.Blake2.Arm.Stream.CalleeOk P code) {s₀ : VG.Arm.State}
    (hp : VG.Proof.Blake2.Arm.Stream.Finalize.Pre w s₀) :
    WP isa (VG.Impl.Blake2.Arm.Stream.finalize (w := w) name code) s₀ fun s' => abiPreserved s₀ s' ∧ (VG.Proof.Blake2.finalizeArm P).post s₀ s' :=
  WP.seq (WP.mono (VG.Proof.Blake2.Arm.Stream.Finalize.pro_ok hP hp) fun _ h₁ => WP.seq (WP.mono (VG.Proof.Blake2.Arm.Stream.Finalize.call_ok' hP hf hp h₁) fun _ h₂ =>
    VG.Proof.Blake2.Arm.Stream.Finalize.end_ok hP hp h₂))

end VG.Proof.Blake2.Arm.Stream.Finalize

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.Arm.Stream.Init`. -/
section

/-!
# Streaming BLAKE2 on ARMv7: `init`

`initState` stores the initial hash value as 32-bit words (`word32`, two per
word of BLAKE2b), the first with the parameter block XORed in; for a key,
`keyBlock` zeroes the buffer and copies the key into it. `init` is a leaf
function writing only `r1`–`r3` and `r12`.
-/

namespace VG.Proof.Blake2.Arm.Stream.Init

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Blake2.Arm.Stream (N B ws ivWord movImm initState keyBlock init)
open VG.Proof.MdStream.Arm (Upd Mupd op2_imm op2_reg op2_lsl wp_mov wp_add wp_subs wp_cmp wp_str wp_ldrb wp_strb
  sub_ofNat cmp0 eval_eq eval_ne)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc writeBytes_frame writeBytes_before)
open VG.Proof.Blake2 (initArm repr_keyBlock stateAt_congr)

/-! ## 32-bit words of the hash value -/

theorem split64 (x : BitVec 64) : x = (x >>> 32).setWidth 32 ++ x.setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_append]
  split
  · simp [*]
  · simp [show i - 32 < 32 by omega]; congr 1; omega

theorem readW64_split (m : Mem) (a : Addr) :
    m.readW a 64 = m.readW (a + BitVec.ofNat 64 4) 32 ++ m.readW a 32 := by
  rw [← VG.Proof.Rc2.Word32.readW64_hi, ← VG.Proof.Rc2.Word32.readW64_lo]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_append]
  split
  · simp [*]
  · simp [show i - 32 < 32 by omega]; congr 1; omega

def word32 {w : Nat} (h : HashValue w) (j : Nat) : BitVec 32 :=
  ((h.toList.getD (j / (ws w / 4)) 0) >>> (32 * (j % (ws w / 4)))).setWidth 32

theorem ivWord_eq {w : Nat} (P : VG.Spec.Blake2.Params w) (j : Nat) : ivWord P j = VG.Proof.Blake2.Arm.Stream.Init.word32 P.IV j := rfl

theorem word32_32 (h : HashValue 32) {k : Nat} (hk : k < 8) : VG.Proof.Blake2.Arm.Stream.Init.word32 h k = h[k] := by
  simp [VG.Proof.Blake2.Arm.Stream.Init.word32, ws, List.getD_eq_getElem?_getD, hk, Nat.mod_one]

theorem word32_64 (h : HashValue 64) {k : Nat} (hk : k < 8) :
    VG.Proof.Blake2.Arm.Stream.Init.word32 h (2 * k + 1) ++ VG.Proof.Blake2.Arm.Stream.Init.word32 h (2 * k) = h[k] := by
  simp only [VG.Proof.Blake2.Arm.Stream.Init.word32, ws, show 64 / 8 / 4 = 2 from rfl, show (2 * k + 1) / 2 = k by omega,
    show (2 * k + 1) % 2 = 1 by omega, show 2 * k / 2 = k by omega, show 2 * k % 2 = 0 by omega]
  simp [List.getD_eq_getElem?_getD, hk]
  exact (VG.Proof.Blake2.Arm.Stream.Init.split64 _).symm

theorem c_lt {nn kk : Nat} (hn : nn < 256) (hk : kk < 256) :
    ((16842752#64) ^^^ (BitVec.ofNat 64 kk <<< 8) ^^^ BitVec.ofNat 64 nn).toNat < 2 ^ 32 := by
  simp only [BitVec.toNat_xor, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  refine Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (by decide) ?_) (by omega)
  rw [Nat.shiftLeft_eq]; omega

theorem word32_init {w : Nat} (hw : w = 32 ∨ w = 64) (P : VG.Spec.Blake2.Params w) {nn kk : Nat} (hn : nn < 256)
    (hk : kk < 256) {j : Nat} (hj : j < 8 * (ws w / 4)) :
    VG.Proof.Blake2.Arm.Stream.Init.word32 (Spec.Blake2.init P nn kk) j = if j = 0 then
      VG.Proof.Blake2.Arm.Stream.Init.word32 P.IV 0 ^^^ 0x01010000 ^^^ (BitVec.ofNat 32 kk <<< 8) ^^^ BitVec.ofNat 32 nn else VG.Proof.Blake2.Arm.Stream.Init.word32 P.IV j := by
  rcases hw with rfl | rfl
  · have hj' : j < 8 := hj
    rw [VG.Proof.Blake2.Arm.Stream.Init.word32_32 _ hj', Spec.Blake2.init, Vector.getElem_set]
    split
    · subst_vars; simp [VG.Proof.Blake2.Arm.Stream.Init.word32_32 _ (show 0 < 8 by decide)]
    · rename_i h; simp [Ne.symm h, VG.Proof.Blake2.Arm.Stream.Init.word32_32 _ hj']
  · have hj' : j < 16 := hj
    simp only [VG.Proof.Blake2.Arm.Stream.Init.word32, ws, show 64 / 8 / 4 = 2 from rfl, Spec.Blake2.init, Vector.toList_set]
    have hl : P.IV.toList.length = 8 := by simp
    rcases (by omega : j = 0 ∨ j = 1 ∨ 2 ≤ j) with rfl | rfl | h2
    · simp [List.getD_eq_getElem?_getD, BitVec.setWidth_xor]
    · simp [List.getD_eq_getElem?_getD]
      have hc : ((16842752#64) ^^^ (BitVec.ofNat 64 kk <<< 8) ^^^ BitVec.ofNat 64 nn) >>> 32 = 0 := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (VG.Proof.Blake2.Arm.Stream.Init.c_lt hn hk)]
        rfl
      rw [BitVec.xor_assoc, BitVec.xor_assoc, ← BitVec.xor_assoc (16842752#64), BitVec.ushiftRight_xor_distrib, hc]
      simp
    · have hne : j / 2 ≠ 0 := by omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hne), show j ≠ 0 by omega]

theorem stateAt_of_words {w : Nat} (hw : w = 32 ∨ w = 64) {m : Mem} {p : Addr} {h : HashValue w}
    (H : ∀ j < 8 * (ws w / 4), m.readW (p + BitVec.ofNat 64 (4 * j)) 32 = VG.Proof.Blake2.Arm.Stream.Init.word32 h j) :
    stateAt w m p = h := by
  rcases hw with rfl | rfl
  · apply Vector.ext; intro k hk
    simp only [stateAt, Vector.getElem_ofFn]
    rw [show 32 / 8 * k = 4 * k by omega, H k (by simp [ws]; omega), VG.Proof.Blake2.Arm.Stream.Init.word32_32 _ hk]
  · apply Vector.ext; intro k hk
    simp only [stateAt, Vector.getElem_ofFn]
    rw [VG.Proof.Blake2.Arm.Stream.Init.readW64_split, Offset.add_add, show 64 / 8 * k = 4 * (2 * k) by omega,
      show 4 * (2 * k) + 4 = 4 * (2 * k + 1) by omega, H _ (by simp [ws]; omega), H _ (by simp [ws]; omega),
      VG.Proof.Blake2.Arm.Stream.Init.word32_64 _ hk]

/-! ## The initial hash value -/

section
variable {w : Nat} (P : VG.Spec.Blake2.Params w)

/-- The store of IV word `j + 1`. -/
def ivStep (j : Nat) : List Instr := movImm (ivWord P (j + 1)) ++ [.str .r12 .r0 (4 * (j + 1))]

theorem initState_eq : initState P = (List.range (N w / 4 - 1)).flatMap (VG.Proof.Blake2.Arm.Stream.Init.ivStep P) ++
    (movImm (ivWord P 0 ^^^ 0x01010000) ++ ([.dp .eor .r12 .r12 (.shifted .r3 .lsl 8),
      .dp .eor .r12 .r12 (.reg .r1), .str .r12 .r0 0] : List Instr)) := by
  rw [initState, List.append_assoc]
  rfl

/-- After storing IV words `1 … n`. -/
structure IvInv (s₀ : State) (n : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ .r12 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨State.addr (s₀.gpr .r0), bufOff w⟩] s₀.mem s.mem
  words : ∀ j < n, s.mem.readW (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * (j + 1))) 32 = ivWord P (j + 1)

variable {P}

theorem wp_movImm {s : State} {v : BitVec 32} {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' .r12 v → WP isa (.block rest) s' Q) :
    WP isa (.block (movImm v ++ rest)) s Q := by
  simp only [movImm, List.cons_append, List.nil_append]
  refine VG.Proof.Blake2.Arm.Stream.wp_movw fun s₁ u₁ => VG.Proof.Blake2.Arm.Stream.wp_movt fun s₂ u₂ => k s₂ ⟨?_, fun r h => ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₂.gpr, u₁.gpr, movw_movt]
  · rw [u₂.other r h, u₁.other r h]
  · rw [u₂.mem, u₁.mem]
  · rw [u₂.rd, u₁.rd]
  · rw [u₂.wr, u₁.wr]
  · rw [u₂.sp, u₁.sp]

theorem iv_step (hw : w = 32 ∨ w = 64) {s₀ : State} (hfit : (s₀.gpr .r0).toNat + bufOff w ≤ 2 ^ 32)
    (hwr : ∀ a n, InRegions [⟨State.addr (s₀.gpr .r0), bufOff w⟩] a n → InRegions s₀.wr a n)
    (k : Nat) (s : State) (hk : k < bufOff w / 4 - 1) (h : VG.Proof.Blake2.Arm.Stream.Init.IvInv P s₀ k s) :
    WP isa (.block (VG.Proof.Blake2.Arm.Stream.Init.ivStep P k)) s (VG.Proof.Blake2.Arm.Stream.Init.IvInv P s₀ (k + 1)) := by
  have hN : bufOff w ≤ 64 := by rcases hw with rfl | rfl <;> decide
  have hin : (⟨State.addr (s₀.gpr .r0), bufOff w⟩ : Region).Contains
      (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * (k + 1))) 4 :=
    VG.Proof.Blake2.Arm.Stream.contains_off _ (by omega) (by omega)
  unfold VG.Proof.Blake2.Arm.Stream.Init.ivStep
  refine VG.Proof.Blake2.Arm.Stream.Init.wp_movImm fun s₁ u₁ => wp_str (a := State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * (k + 1)))
    (by omega) (by rw [u₁.other _ (by decide), h.gpr _ (by decide), addr_add (by omega)])
    (by rw [u₁.wr, h.wr]; exact hwr _ _ ⟨_, List.mem_singleton_self _, hin⟩) fun s₂ g₂ => WP.block_nil ?_
  refine ⟨fun r hr => by rw [g₂.gpr, u₁.other r hr, h.gpr r hr], by rw [g₂.rd, u₁.rd, h.rd],
    by rw [g₂.wr, u₁.wr, h.wr], by rw [g₂.sp, u₁.sp, h.sp], ?_, fun j hj => ?_⟩
  · rw [g₂.mem, u₁.mem]; exact h.frame.writeW (List.mem_singleton_self _) _ hin
  · rw [g₂.mem, u₁.gpr, u₁.mem]
    by_cases e : j = k
    · subst e; exact Mem.readW_writeW_self32 _ _ _
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact h.words j (by omega)

/-- The state after `initState`. -/
structure StateOk (s₀ : State) (s : State) : Prop where
  gpr : ∀ r, r ≠ .r12 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨State.addr (s₀.gpr .r0), bufOff w⟩] s₀.mem s.mem
  state : stateAt w s.mem (State.addr (s₀.gpr .r0)) =
    Spec.Blake2.init P (s₀.gpr .r1).toNat (s₀.gpr .r3).toNat

theorem initState_ok (hw : w = 32 ∨ w = 64) {s₀ : State} (hfit : (s₀.gpr .r0).toNat + bufOff w ≤ 2 ^ 32)
    (hwr : ∀ a n, InRegions [⟨State.addr (s₀.gpr .r0), bufOff w⟩] a n → InRegions s₀.wr a n)
    (hn : (s₀.gpr .r1).toNat < 256) (hk : (s₀.gpr .r3).toNat < 256) :
    WP isa (.block (initState P)) s₀ (VG.Proof.Blake2.Arm.Stream.Init.StateOk (P := P) s₀) := by
  have hN : bufOff w ≤ 64 ∧ 8 ≤ bufOff w / 4 ∧ N w / 4 = bufOff w / 4 := by
    rcases hw with rfl | rfl <;> decide
  rw [VG.Proof.Blake2.Arm.Stream.Init.initState_eq, WP.block_append_iff, hN.2.2]
  refine WP.mono (wp_range_flatMap (M := isa) (VG.Proof.Blake2.Arm.Stream.Init.IvInv P s₀) (fun k s hk h => VG.Proof.Blake2.Arm.Stream.Init.iv_step hw hfit hwr k s hk h)
    (bufOff w / 4 - 1) (Nat.le_refl _) s₀
    ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩) fun s₇ h₇ => ?_
  have hin : (⟨State.addr (s₀.gpr .r0), bufOff w⟩ : Region).Contains (State.addr (s₀.gpr .r0)) 4 :=
    by simp [Region.Contains]; omega
  refine VG.Proof.Blake2.Arm.Stream.Init.wp_movImm fun s₁ u₁ => VG.Proof.Blake2.Arm.Stream.wp_eor (op2_lsl (by decide)) fun s₂ u₂ => VG.Proof.Blake2.Arm.Stream.wp_eor (op2_reg _ _) fun s₃ u₃ =>
    wp_str (a := State.addr (s₀.gpr .r0)) (by decide) ?_ ?_ fun s₄ g₄ => WP.block_nil ?_
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h₇.gpr _ (by decide),
      BitVec.add_zero]
  · rw [u₃.wr, u₂.wr, u₁.wr, h₇.wr]; exact hwr _ _ ⟨_, List.mem_singleton_self _, hin⟩
  have g : ∀ r, r ≠ .r12 → s₄.gpr r = s₀.gpr r := fun r h1 => by
    rw [g₄.gpr, u₃.other r h1, u₂.other r h1, u₁.other r h1, h₇.gpr r h1]
  have hv : s₃.gpr .r12 = VG.Proof.Blake2.Arm.Stream.Init.word32 (Spec.Blake2.init P (s₀.gpr .r1).toNat (s₀.gpr .r3).toNat) 0 := by
    rw [VG.Proof.Blake2.Arm.Stream.Init.word32_init hw P hn hk (by rcases hw with rfl | rfl <;> decide)]
    simp only [↓reduceIte]
    rw [u₃.gpr, u₂.gpr,
      u₁.gpr, u₂.other .r1 (by decide), u₁.other .r1 (by decide), u₁.other .r3 (by decide),
      h₇.gpr .r1 (by decide), h₇.gpr .r3 (by decide), BitVec.ofNat_toNat, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, BitVec.setWidth_eq, VG.Proof.Blake2.Arm.Stream.Init.ivWord_eq]
    rfl
  have hm : s₄.mem = s₇.mem.writeW (State.addr (s₀.gpr .r0)) (s₃.gpr .r12) := by
    rw [g₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨g, by rw [g₄.rd, u₃.rd, u₂.rd, u₁.rd, h₇.rd], by rw [g₄.wr, u₃.wr, u₂.wr, u₁.wr, h₇.wr],
    by rw [g₄.sp, u₃.sp, u₂.sp, u₁.sp, h₇.sp], ?_, ?_⟩
  · rw [hm]; exact h₇.frame.writeW (List.mem_singleton_self _) _ hin
  · refine VG.Proof.Blake2.Arm.Stream.Init.stateAt_of_words hw fun j hj => ?_
    rw [hm]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [Nat.mul_zero, BitVec.add_zero, Mem.readW_writeW_self32, hv]
    · obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hj' : j + 1 < 8 * (ws w / 4) := hj
      have e8 : 8 * (ws w / 4) = bufOff w / 4 := by rcases hw with rfl | rfl <;> decide
      have hs : Mem.Sep (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 (4 * (j + 1))) (32 / 8)
          (State.addr (s₀.gpr .r0)) (32 / 8) := fun x h1 h2 =>
        Offset.sep_base (State.addr (s₀.gpr .r0)) (n := 4) (e := 4 * (j + 1)) (k := 4) (by omega) (by omega)
          x h2 h1
      rw [Mem.readW_writeW_sep hs (by decide), h₇.words j (by omega), VG.Proof.Blake2.Arm.Stream.Init.word32_init hw P hn hk hj']
      simp only [Nat.add_one_ne_zero, ite_false, VG.Proof.Blake2.Arm.Stream.Init.ivWord_eq]

end

/-! ## The key block -/

section
variable {w : Nat}

/-- After zeroing the first `n` words of the buffer, from `s₁`. -/
structure ZInv (s₁ : State) (n : Nat) (s : State) : Prop where
  gpr : s.gpr = s₁.gpr
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  sp : s.sp = s₁.sp
  frame : Frame [⟨State.addr (s₁.gpr .r0) + BitVec.ofNat 64 (bufOff w), blockBytes w⟩] s₁.mem s.mem
  words : ∀ j < n, s.mem.readW (State.addr (s₁.gpr .r0) + BitVec.ofNat 64 (bufOff w) + BitVec.ofNat 64 (4 * j)) 32 = 0

theorem zero_all (hw : w = 32 ∨ w = 64) {s₁ : State}
    (hfit : (s₁.gpr .r0).toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32) (h12 : s₁.gpr .r12 = 0)
    (hwr : ∀ a n, InRegions [⟨State.addr (s₁.gpr .r0) + BitVec.ofNat 64 (bufOff w), blockBytes w⟩] a n →
      InRegions s₁.wr a n) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s, VG.Proof.Blake2.Arm.Stream.Init.ZInv (w := w) s₁ (blockBytes w / 4) s → WP isa (.block rest) s Q) :
    WP isa (.block ((List.range (B w / 4)).map (fun j => Instr.str .r12 .r0 (N w + 4 * j)) ++ rest)) s₁ Q := by
  have hs : bufOff w ≤ 64 ∧ blockBytes w ≤ 128 ∧ blockBytes w % 4 = 0 := by rcases hw with rfl | rfl <;> decide
  rw [WP.block_append_iff]
  refine WP.mono ?_ k
  rw [VG.Proof.Blake2.Arm.Stream.B_eq]
  suffices h : ∀ n ≤ blockBytes w / 4, WP isa (.block ((List.range n).map
      (fun j => Instr.str .r12 .r0 (N w + 4 * j)))) s₁ (VG.Proof.Blake2.Arm.Stream.Init.ZInv (w := w) s₁ n) from h _ (Nat.le_refl _)
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega)⟩
  | succ n ih =>
    rw [List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t h => ?_
    simp only [List.map_cons, List.map_nil]
    have hin : (⟨State.addr (s₁.gpr .r0) + BitVec.ofNat 64 (bufOff w), blockBytes w⟩ : Region).Contains
        (State.addr (s₁.gpr .r0) + BitVec.ofNat 64 (bufOff w) + BitVec.ofNat 64 (4 * n)) 4 :=
      VG.Proof.Blake2.Arm.Stream.contains_off _ (by omega) (by omega)
    refine wp_str (a := State.addr (s₁.gpr .r0) + BitVec.ofNat 64 (bufOff w) + BitVec.ofNat 64 (4 * n))
      (by rw [VG.Proof.Blake2.Arm.Stream.N_eq]; omega) (by rw [h.gpr, addr_add (by rw [VG.Proof.Blake2.Arm.Stream.N_eq]; omega), VG.Proof.Blake2.Arm.Stream.N_eq, Offset.add_add])
      (by rw [h.wr]; exact hwr _ _ ⟨_, List.mem_singleton_self _, hin⟩) fun t₁ g₁ => WP.block_nil ?_
    refine ⟨by rw [g₁.gpr, h.gpr], by rw [g₁.rd, h.rd], by rw [g₁.wr, h.wr], by rw [g₁.sp, h.sp], ?_,
      fun j hj => ?_⟩
    · rw [g₁.mem]; exact h.frame.writeW (List.mem_singleton_self _) _ hin
    · rw [g₁.mem, h.gpr, h12]
      by_cases e : j = n
      · subst e; exact Mem.readW_writeW_self32 _ _ _
      · rw [Offset.add_add, Offset.add_add,
          Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), ← Offset.add_add]
        exact h.words j (by omega)

/-- The key loop's state after `j` of `k` bytes, from `s₂`. -/
structure KI (s₂ : State) (st key : BitVec 32) (k j : Nat) (s : State) : Prop where
  j_le : j ≤ k
  r1 : s.gpr .r1 = st + BitVec.ofNat 32 (bufOff w) + BitVec.ofNat 32 j
  r2 : s.gpr .r2 = key + BitVec.ofNat 32 j
  r3 : s.gpr .r3 = BitVec.ofNat 32 (k - j)
  other : ∀ x, x ≠ .r1 → x ≠ .r2 → x ≠ .r3 → x ≠ .r12 → s.gpr x = s₂.gpr x
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  sp : s.sp = s₂.sp
  mem : s.mem = VG.WriteBytes.writeBytes s₂.mem (State.addr st + BitVec.ofNat 64 (bufOff w))
    ((bytesAt s₂.mem (State.addr key) k).take j)

theorem keyLoop_ok {s₂ : State} {st key : BitVec 32} {k : Nat} (hk : 1 ≤ k) (hkb : k ≤ blockBytes w)
    (hfit : st.toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32) (hkf : key.toNat + k ≤ 2 ^ 32)
    (h : VG.Proof.Blake2.Arm.Stream.Init.KI (w := w) s₂ st key k 0 s₂)
    (hsrc : ∀ i < k, InRegions (s₂.rd ++ s₂.wr) (State.addr key + BitVec.ofNat 64 i) 1)
    (hdst : ∀ i < k, InRegions s₂.wr (State.addr st + BitVec.ofNat 64 (bufOff w) + BitVec.ofNat 64 i) 1)
    (hd : Region.Disjoint ⟨State.addr key, k⟩ ⟨State.addr st + BitVec.ofNat 64 (bufOff w), k⟩) :
    WP isa (.loop (.block [.ldrb .r12 .r2 0, .strb .r12 .r1 0, .dp .add .r2 .r2 (.imm 1),
      .dp .add .r1 .r1 (.imm 1), .subs .r3 .r3 (.imm 1)]) .ne) s₂ (VG.Proof.Blake2.Arm.Stream.Init.KI (w := w) s₂ st key k k) := by
  refine WP.loop (M := isa) (fun n (s : State) => ∃ j, n = k - j ∧ j < k ∧ VG.Proof.Blake2.Arm.Stream.Init.KI (w := w) s₂ st key k j s) ?_ k s₂
    ⟨0, by omega, by omega, h⟩
  rintro n s ⟨j, rfl, hj, h⟩
  have hbyte : s.mem (State.addr key + BitVec.ofNat 64 j) = s₂.mem (State.addr key + BitVec.ofNat 64 j) := by
    rw [h.mem]
    exact (VG.WriteBytes.writeBytes_frame s₂.mem _ _ (VG.Proof.Blake2.Arm.Stream.contains_prefix (k := k) _ (by simp; omega))).bytes
      (R := ⟨State.addr key, k⟩) (by simpa using hd) (by show k ≤ 2 ^ 64; omega) hj
  refine wp_ldrb (a := State.addr key + BitVec.ofNat 64 j) (by decide)
    (by rw [h.r2, BitVec.add_zero, addr_add (by omega)]) (by rw [h.rd, h.wr]; exact hsrc j hj) fun s₁ u₁ => ?_
  have ht : (st + BitVec.ofNat 32 (bufOff w)).toNat = st.toNat + bufOff w := VG.Proof.Blake2.Arm.Stream.toNat_add_ofNat (by omega)
  refine wp_strb (a := State.addr st + BitVec.ofNat 64 (bufOff w) + BitVec.ofNat 64 j) (by decide)
    (by rw [u₁.other _ (by decide), h.r1, BitVec.add_zero, addr_add (by omega), addr_add (by omega)])
    (by rw [u₁.wr, h.wr]; exact hdst j hj) fun s₃ g₃ => ?_
  refine wp_add (op2_imm (by decide)) fun s₄ u₄ => wp_add (op2_imm (by decide)) fun s₅ u₅ =>
    wp_subs (op2_imm (by decide)) fun s₆ u₆ z₆ => WP.block_nil ?_
  have hr3 : s₆.gpr .r3 = BitVec.ofNat 32 (k - (j + 1)) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃.gpr, u₁.other _ (by decide), h.r3,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), Nat.sub_sub]
  have hI : VG.Proof.Blake2.Arm.Stream.Init.KI (w := w) s₂ st key k (j + 1) s₆ := by
    refine ⟨by omega, ?_, ?_, hr3, fun x h1 h2 h3 h4 => ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃.gpr, u₁.other _ (by decide), h.r1,
        BitVec.add_assoc (st + _), show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add]
    · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃.gpr, u₁.other _ (by decide), h.r2,
        BitVec.add_assoc, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add]
    · rw [u₆.other x h3, u₅.other x h1, u₄.other x h2, g₃.gpr, u₁.other x h4, h.other x h1 h2 h3 h4]
    · rw [u₆.rd, u₅.rd, u₄.rd, g₃.rd, u₁.rd, h.rd]
    · rw [u₆.wr, u₅.wr, u₄.wr, g₃.wr, u₁.wr, h.wr]
    · rw [u₆.sp, u₅.sp, u₄.sp, g₃.sp, u₁.sp, h.sp]
    · have hj' : j < (bytesAt s₂.mem (State.addr key) k).length := by rw [VG.Proof.Blake2.Arm.Stream.bytesAt_length]; omega
      have hl : (List.take j (bytesAt s₂.mem (State.addr key) k)).length = j := by
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
      rw [u₆.mem, u₅.mem, u₄.mem, g₃.mem, u₁.mem, u₁.gpr, hbyte, h.mem, List.take_add_one,
        List.getElem?_eq_getElem hj', Option.toList_some, VG.WriteBytes.writeBytes_snoc _ _ _ _ (by rw [hl]; omega), hl,
        VG.Proof.Blake2.Arm.Stream.setWidth_byte]
      congr 1
      simp [bytesAt]
  have hz : isa.eval .ne s₆ = some (decide (k - (j + 1) ≠ 0)) :=
    VG.Proof.Blake2.Arm.Stream.ne_iff s₆ (by rw [z₆, ← u₆.gpr, hr3]) (by omega)
  by_cases hjk : j + 1 = k
  · exact .inl ⟨by rw [hz]; simp; omega, hjk ▸ hI⟩
  · exact .inr ⟨by rw [hz]; simp; omega, k - (j + 1), by omega, j + 1, rfl, by omega, hI⟩

theorem zero_byte {m : Mem} {a : Addr} (h : m.readW a 32 = 0) {j : Nat} (hj : j < 4) :
    m (a + BitVec.ofNat 64 j) = 0 := by
  rw [← Mem.extractLsb'_read m a hj]
  have : m.read a 4 = 0 := by simpa [Mem.readW] using h
  rw [this]; simp

theorem ZInv.byte {s₁ s : State} (h : VG.Proof.Blake2.Arm.Stream.Init.ZInv (w := w) s₁ (blockBytes w / 4) s) (hb : blockBytes w % 4 = 0)
    {i : Nat} (hi : i < blockBytes w) :
    s.mem (State.addr (s₁.gpr .r0) + BitVec.ofNat 64 (bufOff w) + BitVec.ofNat 64 i) = 0 := by
  have e : i = 4 * (i / 4) + i % 4 := (Nat.div_add_mod i 4).symm
  rw [e, ← Offset.add_add (State.addr (s₁.gpr .r0) + BitVec.ofNat 64 (bufOff w)) (4 * (i / 4)) (i % 4)]
  exact VG.Proof.Blake2.Arm.Stream.Init.zero_byte (h.words _ (by omega)) (Nat.mod_lt _ (by decide))

theorem bytesAt_writeBytes_pad {m : Mem} {q : Addr} {xs : List Byte} {n : Nat} (hl : xs.length ≤ n)
    (hn : n < 2 ^ 64) (hz : ∀ i < n, xs.length ≤ i → m (q + BitVec.ofNat 64 i) = 0) :
    bytesAt (VG.WriteBytes.writeBytes m q xs) q n = xs ++ List.replicate (n - xs.length) 0 := by
  apply List.ext_getElem (by simp only [VG.Proof.Blake2.Arm.Stream.bytesAt_length, List.length_append, List.length_replicate]; omega)
  intro i h1 _
  rw [VG.Proof.Blake2.Arm.Stream.bytesAt_length] at h1
  simp only [bytesAt, List.getElem_map, List.getElem_range, VG.WriteBytes.writeBytes, Offset.add_sub_cancel_left,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega)]
  by_cases hi : i < xs.length
  · simp only [hi, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some,
      List.getElem_append_left hi]
  · simp only [hi, ↓reduceIte, hz i h1 (by omega), List.getElem_append_right (Nat.le_of_not_lt hi),
      List.getElem_replicate]

theorem contains_widen {p a : Addr} {d k n : Nat} (hd : d < 2 ^ 64)
    (h : (⟨p + BitVec.ofNat 64 d, k⟩ : Region).Contains a n) : (⟨p, d + k⟩ : Region).Contains a n := by
  unfold Region.Contains at *
  have : (a - p).toNat ≤ (a - (p + BitVec.ofNat 64 d)).toNat + d := by
    rw [← Offset.sub_add_sub_cancel a (p + BitVec.ofNat 64 d) p, BitVec.toNat_add, Offset.add_sub_cancel_left,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]
    exact Nat.mod_le _ _
  simp only at *
  omega

theorem keyBlock_ok (hw : w = 32 ∨ w = 64) {s : State}
    (hfit : (s.gpr .r0).toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32)
    (hkf : (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32)
    (hk1 : (s.gpr .r3).toNat ≠ 0) (hkb : (s.gpr .r3).toNat ≤ blockBytes w)
    (hrd : s.rd = [⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩])
    (hwr : s.wr = [⟨State.addr (s.gpr .r0), bufOff w + blockBytes w⟩])
    (hd : Region.Disjoint ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
      ⟨State.addr (s.gpr .r0), bufOff w + blockBytes w⟩) :
    WP isa (Impl.Blake2.Arm.Stream.keyBlock (w := w)) s fun s' =>
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      (∀ i < bufOff w, s'.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 i) =
        s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 i)) ∧
      bytesAt s'.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 (bufOff w)) (blockBytes w) =
        bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat ++
          List.replicate (blockBytes w - (s.gpr .r3).toNat) 0 := by
  have hs : bufOff w ≤ 64 ∧ blockBytes w ≤ 128 ∧ blockBytes w % 4 = 0 ∧
      encodable (BitVec.ofNat 32 (N w)) = true := by
    rcases hw with rfl | rfl <;> decide
  have hsub : Region.Sub ⟨State.addr (s.gpr .r0) + BitVec.ofNat 64 (bufOff w), blockBytes w⟩
      ⟨State.addr (s.gpr .r0), bufOff w + blockBytes w⟩ := Offset.sub_base _ (by omega)
  have hdb := hd.sub_right hsub
  unfold Impl.Blake2.Arm.Stream.keyBlock
  refine WP.seq ?_
  rw [List.cons_append]
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => ?_
  have e0 : s₁.gpr .r0 = s.gpr .r0 := u₁.other _ (by decide)
  refine VG.Proof.Blake2.Arm.Stream.Init.zero_all hw (by rw [e0]; omega) u₁.gpr (fun a n h => ?_) fun s₂ z₂ => ?_
  · obtain ⟨R, hR, hc⟩ := h
    simp only [List.mem_singleton] at hR; subst hR
    rw [u₁.wr, hwr]
    exact ⟨_, List.mem_singleton_self _, VG.Proof.Blake2.Arm.Stream.Init.contains_widen (by omega) (by rw [e0] at hc; exact hc)⟩
  refine wp_add (op2_imm hs.2.2.2) fun s₃ u₃ => WP.block_nil ?_
  have g : ∀ r, r ≠ .r1 → r ≠ .r12 → s₃.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₃.other r h1, z₂.gpr, u₁.other r h2]
  have hm₃ : s₃.mem = s₂.mem := u₃.mem
  have hrd₃ : s₃.rd = s.rd := by rw [u₃.rd, z₂.rd, u₁.rd]
  have hwr₃ : s₃.wr = s.wr := by rw [u₃.wr, z₂.wr, u₁.wr]
  have hk : (s.gpr .r2) + BitVec.ofNat 32 0 = s.gpr .r2 := BitVec.add_zero _
  have hI : VG.Proof.Blake2.Arm.Stream.Init.KI (w := w) s₃ (s.gpr .r0) (s.gpr .r2) (s.gpr .r3).toNat 0 s₃ :=
    ⟨Nat.zero_le _, by rw [u₃.gpr, z₂.gpr, e0, VG.Proof.Blake2.Arm.Stream.N_eq]; exact (BitVec.add_zero _).symm,
      by rw [g _ (by decide) (by decide), hk],
      by rw [g _ (by decide) (by decide), Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq],
      fun _ _ _ _ _ => rfl, rfl, rfl, rfl, by rw [List.take_zero, VG.WriteBytes.writeBytes_nil]⟩
  have hdk : Region.Disjoint ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
      ⟨State.addr (s.gpr .r0) + BitVec.ofNat 64 (bufOff w), (s.gpr .r3).toNat⟩ :=
    hdb.sub_right (Offset.sub (e := bufOff w) (d := bufOff w) _ (Nat.le_refl _) (by omega)) |>.sub_right
      (fun _ h => h)
  refine WP.mono (VG.Proof.Blake2.Arm.Stream.Init.keyLoop_ok (Nat.one_le_iff_ne_zero.mpr hk1) hkb hfit (by omega) hI
    (fun i hi => ⟨_, by rw [hrd₃, hrd]; exact List.mem_append_left _ (List.mem_singleton_self _),
      Offset.contains_base _ (by omega) (by omega)⟩)
    (fun i hi => ⟨_, by rw [hwr₃, hwr]; exact List.mem_singleton_self _,
      by rw [Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)⟩) hdk) fun s' h => ?_
  have hfr : Frame [⟨State.addr (s.gpr .r0) + BitVec.ofNat 64 (bufOff w), blockBytes w⟩] s.mem s₂.mem := by
    rw [← u₁.mem, ← e0]; exact z₂.frame
  have hkey : bytesAt s₃.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat =
      bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat := by
    rw [hm₃]
    exact bytesAt_congr fun i hi => hfr.bytes (R := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hdb) (by dsimp only; omega) hi
  have hlen : (bytesAt s₃.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat).length = (s.gpr .r3).toNat :=
    VG.Proof.Blake2.Arm.Stream.bytesAt_length _ _ _
  have hmem := h.mem
  rw [List.take_of_length_le (Nat.le_of_eq hlen)] at hmem
  refine ⟨fun r h1 h2 h3 h4 => by rw [h.other r h1 h2 h3 h4, g r h1 h4], by rw [h.sp, u₃.sp, z₂.sp, u₁.sp],
    fun i hi => ?_, ?_⟩
  · rw [hmem, VG.WriteBytes.writeBytes_before _ _ _ hi (by rw [hlen]; omega), hm₃]
    exact hfr.bytes (R := ⟨State.addr (s.gpr .r0), bufOff w⟩)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (Offset.disjoint_base _ (Nat.le_refl _) (by omega)).symm) (by dsimp only; omega) hi
  · rw [hmem, VG.Proof.Blake2.Arm.Stream.Init.bytesAt_writeBytes_pad (by omega) (by omega) fun i hi _ => ?_, hlen, hkey]
    rw [hm₃, ← e0]; exact z₂.byte hs.2.2.1 hi

end

/-! ## `init` -/

section
variable {w : Nat} {P : VG.Spec.Blake2.Params w}

theorem correct (hP : VG.Proof.Blake2.Arm.Stream.Ok P) {s₀ : State} (hp : (VG.Proof.Blake2.initArm P).pre s₀) :
    WP isa (Impl.Blake2.Arm.Stream.init P) s₀ fun s' => abiPreserved s₀ s' ∧ (VG.Proof.Blake2.initArm P).post s₀ s' := by
  obtain ⟨hrd, hwr, hd, hfit, hkf, -, hn2, hkm⟩ := hp
  have hw : w = 32 ∨ w = 64 := hP.w.symm
  have hmax : P.maxBytes ≤ blockBytes w := hP.max
  have hbb : blockBytes w ≤ 128 := by rcases hw with rfl | rfl <;> decide
  have hsubSt : Region.Sub ⟨State.addr (s₀.gpr .r0), bufOff w⟩
      ⟨State.addr (s₀.gpr .r0), bufOff w + blockBytes w⟩ := fun a h => by
    unfold Region.Contains at h ⊢; dsimp only at h ⊢; omega
  have hpres : ∀ r ∈ preserved, r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by decide
  unfold Impl.Blake2.Arm.Stream.init
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Blake2.Arm.Stream.Init.initState_ok hw (by omega) (fun a n h => ?_) (by omega) (by omega)) fun s₁ h₁ => ?_
  · obtain ⟨R, hR, hc⟩ := h
    simp only [List.mem_singleton] at hR; subst hR
    rw [hwr]
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    unfold Region.Contains at hc ⊢; dsimp only at hc ⊢; omega
  refine wp_cmp (op2_imm (by decide)) fun s₂ f₂ z₂ => WP.block_nil ?_
  have g₂ : ∀ r, r ≠ .r12 → s₂.gpr r = s₀.gpr r := fun r hr => by rw [f₂.gpr, h₁.gpr r hr]
  have hm₂ : s₂.mem = s₁.mem := f₂.mem
  have hkey : bytesAt s₂.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat =
      bytesAt s₀.mem (State.addr (s₀.gpr .r2)) (s₀.gpr .r3).toNat := by
    rw [hm₂]
    exact bytesAt_congr fun i hi => h₁.frame.bytes (R := ⟨State.addr (s₀.gpr .r2), (s₀.gpr .r3).toNat⟩)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd.sub_right hsubSt)
      (by dsimp only; omega) hi
  have e3 : s₀.gpr .r3 = BitVec.ofNat 32 (s₀.gpr .r3).toNat := by simp
  have hz : isa.eval .eq s₂ = some (decide ((s₀.gpr .r3).toNat = 0)) := by
    show VG.Arm.eval .eq s₂ = _
    rw [eval_eq, z₂, h₁.gpr _ (by decide), e3, cmp0 (BitVec.isLt _), ← e3]
  refine WP.ite _ hz (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine ⟨⟨fun r hr => g₂ r (hpres r hr).2.2.2, by rw [f₂.sp, h₁.sp]⟩, ?_⟩
    refine repr_keyBlock P hP.pos (by rw [VG.Proof.Blake2.Arm.Stream.bytesAt_length]; omega) (by rw [hm₂]; exact h₁.state) fun h => ?_
    rw [VG.Proof.Blake2.Arm.Stream.bytesAt_length] at h; exact absurd hb h
  · simp only [decide_eq_false_iff_not] at hb
    have e0 := g₂ .r0 (by decide)
    have e2 := g₂ .r2 (by decide)
    have e3' := g₂ .r3 (by decide)
    refine WP.mono (VG.Proof.Blake2.Arm.Stream.Init.keyBlock_ok hw (by rw [e0]; omega) (by rw [e2, e3']; omega) (by rw [e3']; exact hb)
      (by rw [e3']; omega) (by rw [f₂.rd, h₁.rd, hrd, e2, e3']) (by rw [f₂.wr, h₁.wr, hwr, e0])
      (by rw [e0, e2, e3']; exact hd)) fun s' ⟨hg, hsp, hst, hbytes⟩ => ?_
    refine ⟨⟨fun r hr => by
        obtain ⟨h1, h2, h3, h4⟩ := hpres r hr
        rw [hg r h1 h2 h3 h4, g₂ r h4], by rw [hsp, f₂.sp, h₁.sp]⟩, ?_⟩
    rw [e0, e2, e3', hkey] at hbytes
    rw [e0] at hst
    refine repr_keyBlock P hP.pos (by rw [VG.Proof.Blake2.Arm.Stream.bytesAt_length]; omega) ?_ fun _ => by rw [VG.Proof.Blake2.Arm.Stream.bytesAt_length]; exact hbytes
    rw [stateAt_congr hst, hm₂]; exact h₁.state

end

end VG.Proof.Blake2.Arm.Stream.Init

end

/- Proofs formerly in `VerifiedGarbage.Proof.Blake2.Arm.Stream.Verified`. -/
section

section

/-!
# Streaming BLAKE2 on ARMv7: the shared contracts

The ARMv7 contracts of the streaming functions (`initArm`, `updateArm`,
`finalizeArm`) imply the shared ones (`Spec/Blake2/Contract.lean`) on
`Arm.abi`, for BLAKE2b and BLAKE2s, with states satisfying their
preconditions.
-/

namespace VG.Proof.Blake2.Arm.Stream

open VG VG.Arm VG.Spec.Blake2
open VG.Proof.Blake2 (initArm updateArm finalizeArm)

/-! ## States satisfying the preconditions -/

/-- `init` for `w`-bit words, with no key: `state` at `0x1000`. -/
def initSat (w : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 1 | .r2 => 0x2000 | _ => 0
  sp := 0x5000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, bufOff w + blockBytes w⟩]

/-- `update`, with no data, for `w`-bit words: `state` at `0x1000`, `data` at
`0x2000`, `scratch` at `0x3000`, the stack arguments at `0x5000`. -/
def updateSat (w : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | _ => 0
  sp := 0x5000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x5001 then 0x20 else if a = 0x5009 then 0x30 else 0
  rd := [⟨0x2000, 0⟩, ⟨0x5000, 12⟩]
  wr := [⟨0x1000, bufOff w + blockBytes w⟩, ⟨0x3000, 576⟩]

/-- `finalize`, for `w`-bit words: `state` at `0x1000`, `out` at `0x2000`,
`scratch` at `0x3000`, the stack arguments at `0x5000`. -/
def finalizeSat (w : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | _ => 0
  sp := 0x5000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x5001 then 0x20 else if a = 0x5005 then 0x30 else 0
  rd := [⟨0x5000, 8⟩]
  wr := [⟨0x1000, bufOff w + blockBytes w⟩, ⟨0x2000, bufOff w⟩, ⟨0x3000, 576⟩]

/-! ## BLAKE2b -/

theorem initB_implies : (VG.Proof.Blake2.initArm b).Implies (Spec.Blake2.initBContract Arm.abi) := by
  contract_implies [Spec.Blake2.initBContract, Spec.Blake2.initBSig, Proof.Blake2.initArm,
    Proof.Blake2.bufOff, Spec.Blake2.blockBytes, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [initSat] using VG.Proof.Blake2.Arm.Stream.initSat 64

theorem updateB_implies : (VG.Proof.Blake2.updateArm b).Implies (Spec.Blake2.updateBScratchContract Arm.abi 16) := by
  sig_implies [Spec.Blake2.updateBScratchContract, Spec.Blake2.updateBScratchSig, Proof.Blake2.updateArm,
    Proof.Blake2.bufOff, Spec.Blake2.blockBytes, Arm.Stream.below, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr]
    [updateSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using VG.Proof.Blake2.Arm.Stream.updateSat 64

theorem finalizeB_implies : (VG.Proof.Blake2.finalizeArm b).Implies (Spec.Blake2.finalizeBScratchContract Arm.abi 16) := by
  sig_implies [Spec.Blake2.finalizeBScratchContract, Spec.Blake2.finalizeBScratchSig, Proof.Blake2.finalizeArm,
    Proof.Blake2.bufOff, Spec.Blake2.blockBytes, Arm.Stream.below, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr]
    [finalizeSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using VG.Proof.Blake2.Arm.Stream.finalizeSat 64

/-! ## BLAKE2s -/

theorem initS_implies : (VG.Proof.Blake2.initArm s).Implies (Spec.Blake2.initSContract Arm.abi) := by
  contract_implies [Spec.Blake2.initSContract, Spec.Blake2.initSSig, Proof.Blake2.initArm,
    Proof.Blake2.bufOff, Spec.Blake2.blockBytes, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr] [initSat] using VG.Proof.Blake2.Arm.Stream.initSat 32

theorem updateS_implies : (VG.Proof.Blake2.updateArm s).Implies (Spec.Blake2.updateSScratchContract Arm.abi 16) := by
  sig_implies [Spec.Blake2.updateSScratchContract, Spec.Blake2.updateSScratchSig, Proof.Blake2.updateArm,
    Proof.Blake2.bufOff, Spec.Blake2.blockBytes, Arm.Stream.below, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr]
    [updateSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using VG.Proof.Blake2.Arm.Stream.updateSat 32

theorem finalizeS_implies : (VG.Proof.Blake2.finalizeArm s).Implies (Spec.Blake2.finalizeSScratchContract Arm.abi 16) := by
  sig_implies [Spec.Blake2.finalizeSScratchContract, Spec.Blake2.finalizeSScratchSig, Proof.Blake2.finalizeArm,
    Proof.Blake2.bufOff, Spec.Blake2.blockBytes, Arm.Stream.below, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr]
    [finalizeSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using VG.Proof.Blake2.Arm.Stream.finalizeSat 32

end VG.Proof.Blake2.Arm.Stream

end

section

/-!
# Streaming BLAKE2 on ARMv7: constant time

The taint analysis does not analyse frames, so `update` and `finalize`, whose
calls are in frames, are proven constant time by relating two runs (`RelCT`),
piece by piece: the code between the calls by the taint analysis, from the
public arguments for the prologue and from the registers holding our variables
afterwards (which the correctness proofs determine from the public arguments),
and each call by the compression function's contract (`call_rel`:
`RelCT.frame`, `RelCT.call`). The pieces do not depend on the compression
function, so the taint analysis checks them here, for both word sizes.
-/

namespace VG.Proof.Blake2.Arm.Stream

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Blake2.Arm.Stream (call updatePro updateMid updateEnd update finalizePro finalizeEnd finalize)

/-! ## The taint on entry -/

/-- The taint in which the registers `rs` and the first `n` bytes of stack
arguments are public. -/
def argTaint (rs : List Reg) (n : Nat) : VG.Arm.Taint.T :=
  { regs := RegSet.ofList rs, flags := false, argLen := n }

/-- The first `4 j` bytes of stack arguments agree when their first `j` words do. -/
theorem argMem_of {s₁ s₂ : State} {j : Nat} (hsp : s₁.sp = s₂.sp) (hf : s₁.sp.toNat + 4 * j ≤ 2 ^ 32)
    (h : ∀ i < j, stackArg s₁ i = stackArg s₂ i) :
    ∀ k < 4 * j, s₁.mem (VG.Arm.Taint.argByte s₁ k) = s₂.mem (VG.Arm.Taint.argByte s₂ k) := by
  intro k hk
  have e : ∀ s : State, s.sp.toNat + 4 * j ≤ 2 ^ 32 →
      VG.Arm.Taint.argByte s k = stackArgAddr s (k / 4) + BitVec.ofNat 64 (k % 4) := fun s hs => by
    simp only [VG.Arm.Taint.argByte, stackArgAddr]
    rw [addr_add (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  rw [e s₁ hf, e s₂ (hsp ▸ hf), Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)),
    Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
  exact congrArg _ (h _ (by omega))

theorem agree_argTaint {rs : List Reg} {n : Nat} {s₁ s₂ : State} (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hsp : s₁.sp = s₂.sp)
    (hw₁ : s₁.sp.toNat + n ≤ 2 ^ 32 ∧ ∀ r ∈ s₁.wr, Region.Disjoint ⟨State.addr s₁.sp, n⟩ r)
    (hw₂ : s₂.sp.toNat + n ≤ 2 ^ 32 ∧ ∀ r ∈ s₂.wr, Region.Disjoint ⟨State.addr s₂.sp, n⟩ r)
    (hm : ∀ k < n, s₁.mem (VG.Arm.Taint.argByte s₁ k) = s₂.mem (VG.Arm.Taint.argByte s₂ k)) :
    VG.Arm.Taint.Agree (VG.Proof.Blake2.Arm.Stream.argTaint rs n) s₁ s₂ where
  rf := ⟨fun r hr => h r (RegSet.mem_ofList.mp hr), fun h => by cases h⟩
  wr h := absurd rfl h
  wf₁ := ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim, fun _ => hw₁,
    fun _ h => (List.not_mem_nil h).elim⟩
  wf₂ := ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim, fun _ => hw₂,
    fun _ h => (List.not_mem_nil h).elim⟩
  ok _ h := (List.not_mem_nil h).elim
  slots _ h := (List.not_mem_nil h).elim
  sp _ := hsp
  argMem := hm

/-- Code the taint analysis checks from `τ`, in two runs whose single-run
facts `F` and `F'` make them agree on it. -/
theorem rel_agree {F F' G G' : State → Prop} {c : Prog isa} (τ : VG.Arm.Taint.T)
    (hag : ∀ s s', F s → F' s' → VG.Arm.Taint.Agree τ s s')
    (hc : ∃ hc, (VG.Taint.check taint τ c hc).isSome = true)
    (hw : ∀ s, F s → WP isa c s G) (hw' : ∀ s, F' s → WP isa c s G') :
    RelCT isa (fun s s' => F s ∧ F' s') c fun s s' => G s ∧ G' s' := by
  obtain ⟨_, hc⟩ := hc
  exact ((RelCT.taint (A := taint) τ (fun s s' h => hag s s' h.1 h.2) hc).wp
    fun s s' h => ⟨hw s h.1, hw' s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-! ## The calls in two runs -/

theorem push_eq {rs : List Reg} {s a : State} (hrs : regList rs = true) (h : isa.push (.push rs) s = some a) :
    a = pushed rs s := by
  rw [push_pushed hrs (by
    simp only [isa, push] at h; split at h <;> [skip; cases h]
    rename_i hc; exact hc.2)] at h
  exact (Option.some.inj h).symm

/-- A call of the compression function, in its frame, leaks the same in two
runs whose arguments are the same, and whose stack pointers are. -/
theorem call_rel {w : Nat} {P : VG.Spec.Blake2.Params w} {name : String} {code : Prog isa} (hf : VG.Proof.Blake2.Arm.Stream.CalleeOk P code)
    {Rel : State → State → Prop} {sp st scr blk : BitVec 32} {n : Nat} {t : BitVec 64} {last : BitVec 32}
    (h : ∀ s s', Rel s s' → VG.Proof.Blake2.Arm.Stream.CallArgs (w := w) s st scr blk n t last ∧ VG.Proof.Blake2.Arm.Stream.CallArgs (w := w) s' st scr blk n t last ∧
      s.sp = sp ∧ s'.sp = sp) :
    RelCT isa Rel (call name code) fun _ _ => True := by
  refine RelCT.frame (fun s s' hp => by obtain ⟨-, -, e, e'⟩ := h s s' hp; rw [e, e']) ?_
  refine RelCT.call hf.verified.1 hf.verified.2.1 (CallArgs.rd w sp blk n) (CallArgs.wr w st scr)
    fun a b ⟨s, s', hp, pa, pb⟩ => ?_
  obtain ⟨u, u', e, e'⟩ := h s s' hp
  rw [VG.Proof.Blake2.Arm.Stream.push_eq rfl pa, VG.Proof.Blake2.Arm.Stream.push_eq rfl pb]
  subst e
  have v : s'.sp = s.sp := e'
  have hv' : CallArgs.rd w s.sp blk n = CallArgs.rd w s'.sp blk n := by rw [v]
  have t1 : ((pushed VG.Proof.Blake2.Arm.Stream.args4 s).callEntry.withRegions (CallArgs.rd w s.sp blk n) (CallArgs.wr w st scr)).sp =
    s.sp - 16 := CallArgs.psp
  have t2 : ((pushed VG.Proof.Blake2.Arm.Stream.args4 s').callEntry.withRegions (CallArgs.rd w s.sp blk n) (CallArgs.wr w st scr)).sp =
    s'.sp - 16 := CallArgs.psp
  refine ⟨u.pre, hv' ▸ u'.pre, ?_, u.cov, u.covW, hv' ▸ u'.cov, u'.covW⟩
  obtain ⟨c11, c3⟩ := BitVec.append_32_inj (u.t.trans u'.t.symm)
  simp only [compressArm]
  refine ⟨by rw [t1, t2, v], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [State.withRegions_gpr, VG.Proof.Blake2.Arm.Stream.ce0, pushed_gpr, u.r0, u'.r0]
  · simp only [State.withRegions_gpr, VG.Proof.Blake2.Arm.Stream.ce1, pushed_gpr, u.r1, u'.r1]
  · simp only [State.withRegions_gpr, VG.Proof.Blake2.Arm.Stream.ce2, pushed_gpr, u.r2, u'.r2]
  · rw [u.arg0 _ t1 rfl, u'.arg0 _ t2 rfl, c3]
  · rw [u.arg1 _ t1 rfl, u'.arg1 _ t2 rfl, c11]
  · rw [u.arg2 _ t1 rfl, u'.arg2 _ t2 rfl]
  · rw [u.arg3 _ t1 rfl, u'.arg3 _ t2 rfl]

end VG.Proof.Blake2.Arm.Stream

/-! ## `update` -/

namespace VG.Proof.Blake2.Arm.Stream.Update

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Blake2.Arm.Stream (call updatePro updateMid updateEnd update)
open VG.Proof.Blake2 (updateArm countArm)

/-- The registers holding our variables. -/
abbrev vars : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10]

/-- The pieces of `update` between its calls pass the taint analysis. -/
theorem checks {w : Nat} {P : VG.Spec.Blake2.Params w} (hP : VG.Proof.Blake2.Arm.Stream.Ok P) :
    (∃ hc, (VG.Taint.check taint (VG.Proof.Blake2.Arm.Stream.argTaint [.r0, .r2, .r3] 12) (updatePro (w := w)) hc).isSome = true) ∧
    (∃ hc, (VG.Taint.check taint (VG.Arm.Taint.ofRegs VG.Proof.Blake2.Arm.Stream.Update.vars) (updateMid (w := w)) hc).isSome = true) ∧
    (∃ hc, (VG.Taint.check taint (VG.Arm.Taint.ofRegs VG.Proof.Blake2.Arm.Stream.Update.vars) (updateEnd (w := w)) hc).isSome = true) := by
  rcases hP.w with rfl | rfl <;> exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

section CT
variable {w : Nat} {P : VG.Spec.Blake2.Params w} {s₀ s₀' : State} (hpub : (VG.Proof.Blake2.updateArm P).pub s₀ s₀')
include hpub

theorem st_eq : VG.Proof.Blake2.Arm.Stream.Update.st s₀' = VG.Proof.Blake2.Arm.Stream.Update.st s₀ := hpub.2.1.symm
theorem dp_eq : VG.Proof.Blake2.Arm.Stream.Update.dp s₀' = VG.Proof.Blake2.Arm.Stream.Update.dp s₀ := hpub.2.2.2.2.1.symm
theorem len_eq : VG.Proof.Blake2.Arm.Stream.Update.len s₀' = VG.Proof.Blake2.Arm.Stream.Update.len s₀ := by simp only [VG.Proof.Blake2.Arm.Stream.Update.len, hpub.2.2.2.2.2.1]
theorem scr_eq : VG.Proof.Blake2.Arm.Stream.Update.scr s₀' = VG.Proof.Blake2.Arm.Stream.Update.scr s₀ := hpub.2.2.2.2.2.2.symm
theorem cnt_eq : VG.Proof.Blake2.Arm.Stream.Update.cnt s₀' = VG.Proof.Blake2.Arm.Stream.Update.cnt s₀ := by simp only [VG.Proof.Blake2.Arm.Stream.Update.cnt, VG.Proof.Blake2.countArm, hpub.2.2.1, hpub.2.2.2.1]
theorem a₁_eq' : VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀' = VG.Proof.Blake2.Arm.Stream.Update.a₁ w s₀ := by simp only [VG.Proof.Blake2.Arm.Stream.Update.a₁, VG.Proof.Blake2.Arm.Stream.Update.r₀, VG.Proof.Blake2.Arm.Stream.Update.len_eq hpub, VG.Proof.Blake2.Arm.Stream.Update.cnt_eq hpub]
theorem n₁_eq : VG.Proof.Blake2.Arm.Stream.Update.n₁ w s₀' = VG.Proof.Blake2.Arm.Stream.Update.n₁ w s₀ := by simp only [VG.Proof.Blake2.Arm.Stream.Update.n₁, VG.Proof.Blake2.Arm.Stream.Update.r₀, VG.Proof.Blake2.Arm.Stream.Update.a₁_eq' hpub, VG.Proof.Blake2.Arm.Stream.Update.len_eq hpub, VG.Proof.Blake2.Arm.Stream.Update.cnt_eq hpub]
theorem r₂_eq : VG.Proof.Blake2.Arm.Stream.Update.r₂ w s₀' = VG.Proof.Blake2.Arm.Stream.Update.r₂ w s₀ := by simp only [VG.Proof.Blake2.Arm.Stream.Update.r₂, VG.Proof.Blake2.Arm.Stream.Update.r₀, VG.Proof.Blake2.Arm.Stream.Update.a₁_eq' hpub, VG.Proof.Blake2.Arm.Stream.Update.len_eq hpub, VG.Proof.Blake2.Arm.Stream.Update.cnt_eq hpub]
theorem k₂_eq : VG.Proof.Blake2.Arm.Stream.Update.k₂ w s₀' = VG.Proof.Blake2.Arm.Stream.Update.k₂ w s₀ := by simp only [VG.Proof.Blake2.Arm.Stream.Update.k₂, VG.Proof.Blake2.Arm.Stream.Update.a₁_eq' hpub, VG.Proof.Blake2.Arm.Stream.Update.len_eq hpub]
theorem blk₂_eq : VG.Proof.Blake2.Arm.Stream.Update.blk₂ w s₀' = VG.Proof.Blake2.Arm.Stream.Update.blk₂ w s₀ := by
  simp only [VG.Proof.Blake2.Arm.Stream.Update.blk₂, VG.Proof.Blake2.Arm.Stream.Update.a₁_eq' hpub, VG.Proof.Blake2.Arm.Stream.Update.len_eq hpub, VG.Proof.Blake2.Arm.Stream.Update.st_eq hpub, VG.Proof.Blake2.Arm.Stream.Update.dp_eq hpub]

/-- The variables agree in two runs whose states are `Common` at the same
point, with the same number of buffered bytes. -/
theorem vars_agree {c r : Nat} {s s' : State} (h : VG.Proof.Blake2.Arm.Stream.Update.Common w s₀ c s) (h' : VG.Proof.Blake2.Arm.Stream.Update.Common w s₀' c s')
    (h8 : s.gpr .r8 = BitVec.ofNat 32 r) (h8' : s'.gpr .r8 = BitVec.ofNat 32 r) :
    ∀ x ∈ VG.Proof.Blake2.Arm.Stream.Update.vars, s.gpr x = s'.gpr x := by
  have hc := (h.cn.trans (by rw [VG.Proof.Blake2.Arm.Stream.Update.cnt_eq hpub])).trans h'.cn.symm
  obtain ⟨c10, c9⟩ := BitVec.append_32_inj hc
  intro x hx
  simp only [VG.Proof.Blake2.Arm.Stream.Update.vars, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.r4, h'.r4, VG.Proof.Blake2.Arm.Stream.Update.st_eq hpub]
  · rw [h.r5, h'.r5, VG.Proof.Blake2.Arm.Stream.Update.scr_eq hpub]
  · rw [h.r6, h'.r6, VG.Proof.Blake2.Arm.Stream.Update.dp_eq hpub]
  · rw [h.r7, h'.r7, VG.Proof.Blake2.Arm.Stream.Update.len_eq hpub]
  · rw [h8, h8']
  · exact c9
  · exact c10

theorem update_rel (hP : VG.Proof.Blake2.Arm.Stream.Ok P) {name : String} {code : Prog isa} (hf : VG.Proof.Blake2.Arm.Stream.CalleeOk P code)
    (hp : VG.Proof.Blake2.Arm.Stream.Update.Pre w s₀) (hp' : VG.Proof.Blake2.Arm.Stream.Update.Pre w s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (update (w := w) name code) fun _ _ => True := by
  obtain ⟨c₁, c₂, c₃⟩ := VG.Proof.Blake2.Arm.Stream.Update.checks hP
  have hsp : s₀.sp = s₀'.sp := hpub.1
  have wfA : ∀ {s : State}, VG.Proof.Blake2.Arm.Stream.Update.Pre w s →
      s.sp.toNat + 12 ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, 12⟩ r := fun {s} h => by
    have e : (⟨State.addr s.sp, 12⟩ : Region) = VG.Proof.Blake2.Arm.Stream.Update.argR s := by simp [stackArgAddr]
    refine ⟨h.sp_fit, ?_⟩
    rw [e, h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact h.a_st
    · exact h.a_scr
  have pro := VG.Proof.Blake2.Arm.Stream.rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := VG.Proof.Blake2.Arm.Stream.Update.PostPro P s₀)
    (G' := VG.Proof.Blake2.Arm.Stream.Update.PostPro P s₀') (VG.Proof.Blake2.Arm.Stream.argTaint [.r0, .r2, .r3] 12)
    (fun s s' e e' => by
      subst e e'
      refine VG.Proof.Blake2.Arm.Stream.agree_argTaint (fun r hr => ?_) hsp (wfA hp) (wfA hp')
        (VG.Proof.Blake2.Arm.Stream.argMem_of (j := 3) hsp hp.sp_fit fun i hi => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hpub.2.1
        · exact hpub.2.2.1
        · exact hpub.2.2.2.1
      · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
        · exact hpub.2.2.2.2.1
        · exact hpub.2.2.2.2.2.1
        · exact hpub.2.2.2.2.2.2) c₁
    (fun s e => by rw [e]; exact VG.Proof.Blake2.Arm.Stream.Update.pro_ok hP hp) (fun s e => by rw [e]; exact VG.Proof.Blake2.Arm.Stream.Update.pro_ok hP hp')
  have call₁ : RelCT isa (fun s₁ s₂ => VG.Proof.Blake2.Arm.Stream.Update.PostPro P s₀ s₁ ∧ VG.Proof.Blake2.Arm.Stream.Update.PostPro P s₀' s₂) (call name code)
      fun s₁ s₂ => VG.Proof.Blake2.Arm.Stream.Update.Mid P s₀ s₁ ∧ VG.Proof.Blake2.Arm.Stream.Update.Mid P s₀' s₂ :=
    ((VG.Proof.Blake2.Arm.Stream.call_rel hf (sp := s₀.sp) fun s s' ⟨h, h'⟩ => by
      have a := h'.2
      rw [VG.Proof.Blake2.Arm.Stream.Update.st_eq hpub, VG.Proof.Blake2.Arm.Stream.Update.scr_eq hpub, VG.Proof.Blake2.Arm.Stream.Update.n₁_eq hpub, VG.Proof.Blake2.Arm.Stream.Update.cnt_eq hpub, VG.Proof.Blake2.Arm.Stream.Update.a₁_eq' hpub] at a
      exact ⟨h.2, a, h.1.sp, h'.1.sp.trans hsp.symm⟩).wp
      fun s s' h => ⟨VG.Proof.Blake2.Arm.Stream.Update.call₁_ok hP hf hp h.1, VG.Proof.Blake2.Arm.Stream.Update.call₁_ok hP hf hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have mid := VG.Proof.Blake2.Arm.Stream.rel_agree (F := VG.Proof.Blake2.Arm.Stream.Update.Mid P s₀) (F' := VG.Proof.Blake2.Arm.Stream.Update.Mid P s₀') (VG.Arm.Taint.ofRegs VG.Proof.Blake2.Arm.Stream.Update.vars)
    (fun s s' h h' => VG.Arm.Taint.agree_ofRegs (VG.Proof.Blake2.Arm.Stream.Update.vars_agree hpub h.1
      (by have := h'.1; rwa [VG.Proof.Blake2.Arm.Stream.Update.a₁_eq' hpub] at this) h.2.1
      (by have := h'.2.1; simp only [VG.Proof.Blake2.Arm.Stream.Update.r₀, VG.Proof.Blake2.Arm.Stream.Update.cnt_eq hpub, VG.Proof.Blake2.Arm.Stream.Update.a₁_eq' hpub] at this; exact this))) c₂
    (fun s h => VG.Proof.Blake2.Arm.Stream.Update.mid_ok hP hp h) (fun s h => VG.Proof.Blake2.Arm.Stream.Update.mid_ok hP hp' h)
  have call₂ : RelCT isa (fun s₁ s₂ => VG.Proof.Blake2.Arm.Stream.Update.PostMid P s₀ s₁ ∧ VG.Proof.Blake2.Arm.Stream.Update.PostMid P s₀' s₂) (call name code)
      fun s₁ s₂ => VG.Proof.Blake2.Arm.Stream.Update.End P s₀ s₁ ∧ VG.Proof.Blake2.Arm.Stream.Update.End P s₀' s₂ :=
    ((VG.Proof.Blake2.Arm.Stream.call_rel hf (sp := s₀.sp) fun s s' ⟨h, h'⟩ => by
      have a := h'.2
      rw [VG.Proof.Blake2.Arm.Stream.Update.st_eq hpub, VG.Proof.Blake2.Arm.Stream.Update.scr_eq hpub, VG.Proof.Blake2.Arm.Stream.Update.blk₂_eq hpub, VG.Proof.Blake2.Arm.Stream.Update.k₂_eq hpub, VG.Proof.Blake2.Arm.Stream.Update.cnt_eq hpub, VG.Proof.Blake2.Arm.Stream.Update.a₁_eq' hpub] at a
      exact ⟨h.2, a, h.1.sp, h'.1.sp.trans hsp.symm⟩).wp
      fun s s' h => ⟨VG.Proof.Blake2.Arm.Stream.Update.call₂_ok hP hf hp h.1, VG.Proof.Blake2.Arm.Stream.Update.call₂_ok hP hf hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have fin := VG.Proof.Blake2.Arm.Stream.rel_agree (F := VG.Proof.Blake2.Arm.Stream.Update.End P s₀) (F' := VG.Proof.Blake2.Arm.Stream.Update.End P s₀') (G := fun _ => True) (G' := fun _ => True)
    (VG.Arm.Taint.ofRegs VG.Proof.Blake2.Arm.Stream.Update.vars)
    (fun s s' h h' => VG.Arm.Taint.agree_ofRegs (VG.Proof.Blake2.Arm.Stream.Update.vars_agree hpub h.1
      (by have := h'.1; rwa [VG.Proof.Blake2.Arm.Stream.Update.a₁_eq' hpub] at this) h.2.1
      (by have := h'.2.1; rwa [VG.Proof.Blake2.Arm.Stream.Update.r₂_eq hpub] at this))) c₃
    (fun s h => WP.mono (VG.Proof.Blake2.Arm.Stream.Update.end_ok hP hp h) fun _ _ => trivial)
    (fun s h => WP.mono (VG.Proof.Blake2.Arm.Stream.Update.end_ok hP hp' h) fun _ _ => trivial)
  exact pro.seq (call₁.seq (mid.seq (call₂.seq (fin.mono (fun _ _ h => h) fun _ _ _ => trivial))))

end CT

theorem update_ct {w : Nat} {P : VG.Spec.Blake2.Params w} (hP : VG.Proof.Blake2.Arm.Stream.Ok P) {name : String} {code : Prog isa}
    (hf : VG.Proof.Blake2.Arm.Stream.CalleeOk P code) :
    ConstantTime isa (VG.Proof.Blake2.updateArm P).pre (VG.Proof.Blake2.updateArm P).pub (update (w := w) name code) :=
  fun _ _ _ _ _ _ h₁ h₂ hpub e₁ e₂ =>
    (VG.Proof.Blake2.Arm.Stream.Update.update_rel hpub hP hf (VG.Proof.Blake2.Arm.Stream.Update.pre_of h₁) (VG.Proof.Blake2.Arm.Stream.Update.pre_of h₂) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Blake2.Arm.Stream.Update

/-! ## `finalize` -/

namespace VG.Proof.Blake2.Arm.Stream.Finalize

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Blake2.Arm.Stream (call finalizePro finalizeEnd finalize)
open VG.Proof.Blake2 (finalizeArm countArm)

/-- The pieces of `finalize` around its call pass the taint analysis. -/
theorem checks {w : Nat} {P : VG.Spec.Blake2.Params w} (hP : VG.Proof.Blake2.Arm.Stream.Ok P) :
    (∃ hc, (VG.Taint.check taint (VG.Proof.Blake2.Arm.Stream.argTaint [.r0, .r2, .r3] 8) (finalizePro (w := w)) hc).isSome = true) ∧
    (∃ hc, (VG.Taint.check taint (VG.Arm.Taint.ofRegs [.r4, .r5, .r6]) (.block (finalizeEnd (w := w))) hc).isSome =
      true) := by
  rcases hP.w with rfl | rfl <;> exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

section CT
variable {w : Nat} {P : VG.Spec.Blake2.Params w} {s₀ s₀' : State} (hpub : (VG.Proof.Blake2.finalizeArm P).pub s₀ s₀')
include hpub

theorem finalize_rel (hP : VG.Proof.Blake2.Arm.Stream.Ok P) {name : String} {code : Prog isa} (hf : VG.Proof.Blake2.Arm.Stream.CalleeOk P code)
    (hp : VG.Proof.Blake2.Arm.Stream.Finalize.Pre w s₀) (hp' : VG.Proof.Blake2.Arm.Stream.Finalize.Pre w s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (finalize (w := w) name code) fun _ _ => True := by
  obtain ⟨c₁, c₂⟩ := VG.Proof.Blake2.Arm.Stream.Finalize.checks hP
  have hsp : s₀.sp = s₀'.sp := hpub.1
  have hst : VG.Proof.Blake2.Arm.Stream.Finalize.st s₀' = VG.Proof.Blake2.Arm.Stream.Finalize.st s₀ := hpub.2.1.symm
  have hout : VG.Proof.Blake2.Arm.Stream.Finalize.out s₀' = VG.Proof.Blake2.Arm.Stream.Finalize.out s₀ := hpub.2.2.2.2.1.symm
  have hscr : VG.Proof.Blake2.Arm.Stream.Finalize.scr s₀' = VG.Proof.Blake2.Arm.Stream.Finalize.scr s₀ := hpub.2.2.2.2.2.symm
  have hcnt : VG.Proof.Blake2.Arm.Stream.Finalize.cnt s₀' = VG.Proof.Blake2.Arm.Stream.Finalize.cnt s₀ := by simp only [VG.Proof.Blake2.Arm.Stream.Finalize.cnt, VG.Proof.Blake2.countArm, hpub.2.2.1, hpub.2.2.2.1]
  have wfA : ∀ {s : State}, VG.Proof.Blake2.Arm.Stream.Finalize.Pre w s →
      s.sp.toNat + 8 ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, 8⟩ r := fun {s} h => by
    have e : (⟨State.addr s.sp, 8⟩ : Region) = VG.Proof.Blake2.Arm.Stream.Finalize.argR s := by simp [stackArgAddr]
    refine ⟨h.sp_fit, ?_⟩
    rw [e, h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact h.a_st
    · exact h.a_out
    · exact h.a_scr
  have pro := VG.Proof.Blake2.Arm.Stream.rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀') (G := VG.Proof.Blake2.Arm.Stream.Finalize.PostPro w s₀)
    (G' := VG.Proof.Blake2.Arm.Stream.Finalize.PostPro w s₀') (VG.Proof.Blake2.Arm.Stream.argTaint [.r0, .r2, .r3] 8)
    (fun s s' e e' => by
      subst e e'
      refine VG.Proof.Blake2.Arm.Stream.agree_argTaint (fun r hr => ?_) hsp (wfA hp) (wfA hp')
        (VG.Proof.Blake2.Arm.Stream.argMem_of (j := 2) hsp hp.sp_fit fun i hi => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hpub.2.1
        · exact hpub.2.2.1
        · exact hpub.2.2.2.1
      · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · exact hpub.2.2.2.2.1
        · exact hpub.2.2.2.2.2) c₁
    (fun s e => by rw [e]; exact VG.Proof.Blake2.Arm.Stream.Finalize.pro_ok hP hp) (fun s e => by rw [e]; exact VG.Proof.Blake2.Arm.Stream.Finalize.pro_ok hP hp')
  have call₁ : RelCT isa (fun s₁ s₂ => VG.Proof.Blake2.Arm.Stream.Finalize.PostPro w s₀ s₁ ∧ VG.Proof.Blake2.Arm.Stream.Finalize.PostPro w s₀' s₂) (call name code)
      fun s₁ s₂ => VG.Proof.Blake2.Arm.Stream.Finalize.Mid P s₀ s₁ ∧ VG.Proof.Blake2.Arm.Stream.Finalize.Mid P s₀' s₂ :=
    ((VG.Proof.Blake2.Arm.Stream.call_rel hf (sp := s₀.sp) fun s s' ⟨h, h'⟩ => by
      have a := h'.2
      rw [hst, hscr, hcnt] at a
      exact ⟨h.2, a, h.1.sp, h'.1.sp.trans hsp.symm⟩).wp
      fun s s' h => ⟨VG.Proof.Blake2.Arm.Stream.Finalize.call_ok' hP hf hp h.1, VG.Proof.Blake2.Arm.Stream.Finalize.call_ok' hP hf hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have fin := VG.Proof.Blake2.Arm.Stream.rel_agree (F := VG.Proof.Blake2.Arm.Stream.Finalize.Mid P s₀) (F' := VG.Proof.Blake2.Arm.Stream.Finalize.Mid P s₀') (G := fun _ => True) (G' := fun _ => True)
    (VG.Arm.Taint.ofRegs [.r4, .r5, .r6])
    (fun s s' h h' => VG.Arm.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.1.r4, h'.1.r4, hst]
      · rw [h.1.r5, h'.1.r5, hscr]
      · rw [h.1.r6, h'.1.r6, hout]) c₂
    (fun s h => WP.mono (VG.Proof.Blake2.Arm.Stream.Finalize.end_ok hP hp h) fun _ _ => trivial)
    (fun s h => WP.mono (VG.Proof.Blake2.Arm.Stream.Finalize.end_ok hP hp' h) fun _ _ => trivial)
  exact pro.seq (call₁.seq (fin.mono (fun _ _ h => h) fun _ _ _ => trivial))

end CT

theorem finalize_ct {w : Nat} {P : VG.Spec.Blake2.Params w} (hP : VG.Proof.Blake2.Arm.Stream.Ok P) {name : String} {code : Prog isa}
    (hf : VG.Proof.Blake2.Arm.Stream.CalleeOk P code) :
    ConstantTime isa (VG.Proof.Blake2.finalizeArm P).pre (VG.Proof.Blake2.finalizeArm P).pub (finalize (w := w) name code) :=
  fun _ _ _ _ _ _ h₁ h₂ hpub e₁ e₂ =>
    (VG.Proof.Blake2.Arm.Stream.Finalize.finalize_rel hpub hP hf (VG.Proof.Blake2.Arm.Stream.Finalize.pre_of h₁) (VG.Proof.Blake2.Arm.Stream.Finalize.pre_of h₂) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Blake2.Arm.Stream.Finalize

end

/-!
# Streaming BLAKE2 on ARMv7: `Verified`

The streaming functions are `Verified` against any contract their ARMv7
contracts (`initArm`, `updateArm`, `finalizeArm`) imply, for any parameter set
`P` with `Ok P` and, for `update` and `finalize`, any compression function
verified against `compressArm P` (`CalleeOk`). `init`'s code holds the initial
hash value as immediates, so its taint check is made for each parameter set:
`init_check_s` and `init_check_b`. The implications of the shared contracts
are in `Implies.lean` (`updateS_implies`, …).
-/

namespace VG.Proof.Blake2.Arm.Stream

open VG VG.Arm VG.Spec.Blake2
open VG.Impl.Blake2.Arm.Stream (update finalize)
open VG.Proof.Blake2 (initArm updateArm finalizeArm)

theorem okS : VG.Proof.Blake2.Arm.Stream.Ok Spec.Blake2.s := ⟨by decide, .inr rfl⟩
theorem okB : VG.Proof.Blake2.Arm.Stream.Ok Spec.Blake2.b := ⟨by decide, .inl rfl⟩

variable {w : Nat} {P : VG.Spec.Blake2.Params w}

theorem update_verified (hP : VG.Proof.Blake2.Arm.Stream.Ok P) {name : String} {code : Prog isa} (hf : VG.Proof.Blake2.Arm.Stream.CalleeOk P code)
    {k : Contract isa} (hk : (VG.Proof.Blake2.updateArm P).Implies k) :
    Verified Arm.target (update (w := w) name code) k :=
  Verified.of_correct (fun _ hs => Update.correct hP hf (Update.pre_of hs)) (Update.update_ct hP hf) hk

theorem finalize_verified (hP : VG.Proof.Blake2.Arm.Stream.Ok P) {name : String} {code : Prog isa} (hf : VG.Proof.Blake2.Arm.Stream.CalleeOk P code)
    {k : Contract isa} (hk : (VG.Proof.Blake2.finalizeArm P).Implies k) :
    Verified Arm.target (finalize (w := w) name code) k :=
  Verified.of_correct (fun _ hs => Finalize.correct hP hf (Finalize.pre_of hs)) (Finalize.finalize_ct hP hf) hk

/-- `init`'s taint check, from its arguments. -/
def InitCheck (P : VG.Spec.Blake2.Params w) : Prop :=
  ∃ hc, (VG.Taint.check taint (VG.Arm.Taint.ofRegs [.r0, .r1, .r2, .r3])
    (Impl.Blake2.Arm.Stream.init P) hc).isSome = true

theorem init_check_s : VG.Proof.Blake2.Arm.Stream.InitCheck Spec.Blake2.s := ⟨_, by taint_decide⟩
theorem init_check_b : VG.Proof.Blake2.Arm.Stream.InitCheck Spec.Blake2.b := ⟨_, by taint_decide⟩

theorem init_verified (hP : VG.Proof.Blake2.Arm.Stream.Ok P) (hc : VG.Proof.Blake2.Arm.Stream.InitCheck P) {k : Contract isa} (hk : (VG.Proof.Blake2.initArm P).Implies k) :
    Verified Arm.target (Impl.Blake2.Arm.Stream.init P) k := by
  obtain ⟨_, hc⟩ := hc
  refine Verified.of_correct (fun _ hs => Init.correct hP hs) ?_ hk
  refine VG.Taint.constantTime (A := taint) (VG.Arm.Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun s₁ s₂ _ _ ⟨h0, h1, h2, h3⟩ => VG.Arm.Taint.agree_ofRegs fun r hr => ?_) hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> assumption

end VG.Proof.Blake2.Arm.Stream

end

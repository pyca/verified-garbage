import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Blake2.Arm.Contract
import VerifiedGarbage.Proof.Blake2.Stream
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Impl.Blake2.Arm.Stream

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

omit h in
theorem argsSub : Region.Sub ⟨State.addr s.sp - 16, 16⟩ (below s) := fun _ h => h

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

/-- After a frame of `rs` around a call that keeps the regions and the stack
pointer. -/
theorem after_frame {s s₂ : State} {rs : List Reg} {ws : List Region}
    (fP : Frame [below s] s.mem (pushed rs s).mem)
    (hrd : s₂.rd = (pushed rs s).rd) (hwr : s₂.wr = (pushed rs s).wr) (hsp : s₂.sp = (pushed rs s).sp)
    (hf : Frame ws (pushed rs s).mem s₂.mem)
    (hcs : ∀ r ∈ preserved, r ≠ .lr → s₂.gpr r = (pushed rs s).gpr r) :
    After s ws (popped .r3 (4 * rs.length) s₂) := by
  refine ⟨?_, ?_, ?_, fun r hr hl => ?_, ?_⟩
  · rw [popped_rd, hrd, pushed_rd]
  · rw [popped_wr, hwr, pushed_wr]; rfl
  · rw [popped_sp, hsp, pushed_sp]; exact BitVec.sub_add_cancel _ _
  · have hr3 : r ≠ .r3 := by rintro rfl; simp [preserved] at hr
    rw [popped_gpr hr3, hcs r hr hl, pushed_gpr]
  · rw [popped_mem]
    exact (frame_app (ws' := ws) fP |>.mono fun r hr => by
        simp only [List.mem_append, List.mem_singleton] at hr ⊢; grind).trans (frame_app (ws' := [below s]) hf)

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
  intro s₂ hrd hwr hsp hfr hcs _ hpost
  simp only [compressArm, tArm, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, ce0, ce1,
    ce2, pushed_gpr, h.r0, h.r1, h.r2, h.hn', h.arg0 _ CallArgs.vsp CallArgs.vmem,
    h.arg1 _ CallArgs.vsp CallArgs.vmem, h.arg2 _ CallArgs.vsp CallArgs.vmem, h.t] at hpost
  refine hQ _ (after_frame h.fP hrd hwr hsp hfr hcs) ?_
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

theorem Ok.pos (h : Ok P) : 0 < blockBytes w := by rcases h.bb with h | h <;> omega

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

theorem op2_ror {s : State} {r : Reg} {n : Nat} (h : 1 ≤ n ∧ n ≤ 31) :
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
  · simp only [hc, decide_true, ite_true, toNat_append32, BitVec.toNat_add, BitVec.toNat_setWidth, e1]
    omega
  · simp only [hc, decide_false, Bool.false_eq_true, ite_false, toNat_append32, BitVec.toNat_add,
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
  rw [add64, h, BitVec.ofNat_add]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- The low word of a count in a register pair. -/
theorem lo_of_pair {lo hi : BitVec 32} {x : Nat} (h : (hi ++ lo : BitVec 64) = BitVec.ofNat 64 x) :
    lo = BitVec.ofNat 32 x := by
  apply BitVec.eq_of_toNat_eq
  have e := congrArg BitVec.toNat h
  rw [toNat_append32, BitVec.toNat_ofNat] at e
  rw [BitVec.toNat_ofNat]
  have := lo.isLt; have := hi.isLt
  omega

/-- A count in a register pair is zero iff the OR of its words is. -/
theorem or_beq_zero {lo hi : BitVec 32} {x : Nat} (h : (hi ++ lo : BitVec 64) = BitVec.ofNat 64 x)
    (hx : x < 2 ^ 64) : ((lo ||| hi) - 0 == 0) = decide (x = 0) := by
  have e := congrArg BitVec.toNat h
  rw [toNat_append32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] at e
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
theorem mask_mod (hP : Ok P) (x : BitVec 32) :
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
theorem shr_ofNat (hP : Ok P) {m : Nat} (h : m < 2 ^ 32) :
    BitVec.ofNat 32 m >>> lbb w = BitVec.ofNat 32 (m / blockBytes w) := by
  rw [MdStream.Arm.ofNat_shr h, hP.lbb.2.2]

/-- `((count - 1) mod B) + 1`, from the low word of the count. -/
theorem bufLen_lo (hP : Ok P) {x : Nat} (hx : x ≠ 0) :
    ((BitVec.ofNat 32 x - 1) &&& BitVec.ofNat 32 (B w - 1)) + 1 = BitVec.ofNat 32 (bufLen w x) := by
  have hd : blockBytes w ∣ 2 ^ 32 := by rcases hP.w with rfl | rfl <;> decide
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), mask_mod hP,
    BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ hd, ← BitVec.ofNat_add]
  simp only [bufLen, hx, ite_false]

/-- A pointer plus an offset that does not wrap. -/
theorem toNat_add_ofNat {p : BitVec 32} {k : Nat} (h : p.toNat + k < 2 ^ 32) :
    (p + BitVec.ofNat 32 k).toNat = p.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt h]

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

theorem eq_iff (s : State) {k : Nat} (h : s.z = (BitVec.ofNat 32 k == 0)) (hk : k < 2 ^ 32) :
    isa.eval .eq s = some (decide (k = 0)) := by
  show VG.Arm.eval .eq s = _
  rw [eval_eq, h, ofNat_beq_zero hk]

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
    ⟨0, by omega, by omega, by omega, by simp [hr6], by rw [hr8, Nat.add_zero], by rw [hr11, Nat.sub_zero],
      fun _ _ _ _ _ _ => rfl, rfl, rfl, rfl, by rw [List.take_zero, writeBytes_nil]⟩
  rintro n s ⟨j, rfl, hj, h⟩
  -- The byte read.
  have hin : InRegions (s.rd ++ s.wr) (State.addr src + BitVec.ofNat 64 j) 1 := by
    rw [h.rd, h.wr]; exact hsrc j hj
  have hbyte : s.mem (State.addr src + BitVec.ofNat 64 j) = s₀.mem (State.addr src + BitVec.ofNat 64 j) := by
    rw [h.mem]
    exact (writeBytes_frame s₀.mem _ _ (contains_prefix (k := k) _ (by simp; omega))).bytes
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
    (by simp only [N_eq]; omega) ?_ (by rw [u₂.wr, u₁.wr]; exact hout) fun s₃ g₃ => ?_
  · rw [u₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), hr4', h.r8, N_eq, BitVec.add_assoc,
      ← BitVec.ofNat_add, addr_add (by omega), Offset.add_add]
    congr 2; omega
  refine wp_add (op2_imm (by decide)) fun s₄ u₄ => wp_add (op2_imm (by decide)) fun s₅ u₅ =>
    wp_subs (op2_imm (by decide)) fun s₆ u₆ z₆ => WP.block_nil ?_
  have hr11' : s₆.gpr .r11 = BitVec.ofNat 32 (k - (j + 1)) := by
    rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.r11, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega),
      Nat.sub_sub]
  have hI : CopyI s₀ (State.addr st + BitVec.ofNat 64 (bufOff w + r)) src r k (j + 1) s₆ := by
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
    · have hj' : j < (bytesAt s₀.mem (State.addr src) k).length := by rw [bytesAt_length]; omega
      have hl : (List.take j (bytesAt s₀.mem (State.addr src) k)).length = j := by
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
      rw [u₆.mem, u₅.mem, u₄.mem, g₃.mem, u₂.mem, u₁.mem, u₂.other _ (by decide), u₁.gpr, hbyte, h.mem,
        List.take_add_one, List.getElem?_eq_getElem hj', Option.toList_some,
        writeBytes_snoc _ _ _ _ (by rw [hl]; omega), hl, setWidth_byte]
      congr 1
      simp [bytesAt]
  have hz : isa.eval .ne s₆ = some (decide (k - (j + 1) ≠ 0)) :=
    ne_iff s₆ (by rw [z₆, ← u₆.gpr, hr11']) (by omega)
  by_cases hjk : j + 1 = k
  · exact .inl ⟨by rw [hz]; simp; omega, hQ _ (hjk ▸ hI)⟩
  · exact .inr ⟨by rw [hz]; simp; omega, k - (j + 1), by omega, j + 1, rfl, by omega, hI⟩

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
    ⟨0, by omega, by omega, by omega, by rw [hr8, Nat.add_zero], by rw [hr11, Nat.sub_zero],
      fun _ _ _ _ => rfl, rfl, rfl, rfl, by rw [List.replicate_zero, writeBytes_nil]⟩
  rintro n s ⟨j, rfl, hj, h⟩
  have hr4' : s.gpr .r4 = st := by rw [h.other .r4 (by decide) (by decide) (by decide), hr4]
  refine wp_add (op2_reg _ _) fun s₁ u₁ =>
    wp_strb (a := State.addr st + BitVec.ofNat 64 (bufOff w + r) + BitVec.ofNat 64 j)
    (by simp only [N_eq]; omega) ?_ (by rw [u₁.wr, h.wr]; exact hdst j hj) fun s₂ g₂ => ?_
  · rw [u₁.gpr, hr4', h.r8, N_eq, BitVec.add_assoc, ← BitVec.ofNat_add, addr_add (by omega), Offset.add_add]
    congr 2; omega
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_subs (op2_imm (by decide)) fun s₄ u₄ z₄ =>
    WP.block_nil ?_
  have hr11' : s₄.gpr .r11 = BitVec.ofNat 32 (k - (j + 1)) := by
    rw [u₄.gpr, u₃.other _ (by decide), g₂.gpr, u₁.other _ (by decide), h.r11,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), Nat.sub_sub]
  have hI : ZI s₀ (State.addr st + BitVec.ofNat 64 (bufOff w + r)) r k (j + 1) s₄ := by
    refine ⟨by omega, ?_, hr11', fun x h1 h2 h3 => ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₄.other _ (by decide), u₃.gpr, g₂.gpr, u₁.other _ (by decide), h.r8,
        show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, ← BitVec.ofNat_add, Nat.add_assoc]
    · rw [u₄.other x h3, u₃.other x h2, g₂.gpr, u₁.other x h1, h.other x h1 h2 h3]
    · rw [u₄.rd, u₃.rd, g₂.rd, u₁.rd, h.rd]
    · rw [u₄.wr, u₃.wr, g₂.wr, u₁.wr, h.wr]
    · rw [u₄.sp, u₃.sp, g₂.sp, u₁.sp, h.sp]
    · rw [u₄.mem, u₃.mem, g₂.mem, u₁.mem, u₁.other _ (by decide),
        h.other .r12 (by decide) (by decide) (by decide), hr12, h.mem,
        List.replicate_succ', writeBytes_snoc _ _ _ _ (by simp; omega), List.length_replicate]
      rfl
  have hz : isa.eval .ne s₄ = some (decide (k - (j + 1) ≠ 0)) :=
    ne_iff s₄ (by rw [z₄, ← u₄.gpr, hr11']) (by omega)
  by_cases hjk : j + 1 = k
  · exact .inl ⟨by rw [hz]; simp; omega, hQ _ (hjk ▸ hI)⟩
  · exact .inr ⟨by rw [hz]; simp; omega, k - (j + 1), by omega, j + 1, rfl, by omega, hI⟩

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
  Spill.save_slots_ok saved_slots (by omega) hin (k _ rfl rfl rfl rfl rfl)

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
  refine Spill.restore_slots_ok saved_slots (by decide) (g := g) (by rw [h3]; omega)
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
    bytesAt (writeBytes m (p + BitVec.ofNat 64 r) xs) p (r + xs.length) = bytesAt m p r ++ xs := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro i hi
    have hi := List.mem_range.mp hi
    exact WriteBytes.writeBytes_before m p xs hi (by omega)
  · apply List.ext_getElem (by simp)
    intro j h₁ h₂
    simp only [List.getElem_map, List.getElem_range, Function.comp, writeBytes]
    have hj : j < xs.length := by simpa using h₁
    rw [show p + BitVec.ofNat 64 (r + j) - (p + BitVec.ofNat 64 r) = BitVec.ofNat 64 j from
      Offset.add_ofNat_add_sub p r j, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp [hj, List.getD_eq_getElem?_getD]

end Arm.Stream

end VG.Proof.Blake2

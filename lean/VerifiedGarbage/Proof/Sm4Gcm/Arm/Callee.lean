module

import VerifiedGarbage.Proof.Sm4.Arm.Batch32Verified
import VerifiedGarbage.Proof.Sm4.Arm.KeyVerified
public import VerifiedGarbage.Proof.Framework.Arm.CallF
public import VerifiedGarbage.Proof.Gcm.Arm.Ghash
public import VerifiedGarbage.Spec.Sm4.Gcm.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Frame
public import VerifiedGarbage.Impl.Sm4Gcm.Arm
public import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Gcm.Stream
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Sm4.Arm.BatchCtr32
public import VerifiedGarbage.Impl.Sm4.Arm.ExpandKey
public import VerifiedGarbage.Impl.StackScratch.Arm
public import VerifiedGarbage.Proof.Framework.Arm.Inline
public import VerifiedGarbage.Proof.Framework.Arm.Linear
public import VerifiedGarbage.Proof.Framework.Bitslice.Atoms
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Sm4.Arm.Batch32Body
public import VerifiedGarbage.Proof.Sm4.SboxTable
public import VerifiedGarbage.Spec.Aes
public import VerifiedGarbage.Spec.Sm4.Contract
public import VerifiedGarbage.Proof.Sm4.Contract
public import VerifiedGarbage.Spec.Sm4.Gcm
public import VerifiedGarbage.TCB.Arm.Target

/-!
# SM4-GCM on ARMv7: the functions called

Untrusted: everything here is checked by Lean. Each call, from its callee's
contract (with `WP.call`, or `WP.callF` for the callees that keep their
working space on the stack), with the regions it is given: what it needs
(`CtrCall`, `GhCall`, `KeyCall`) and what it leaves (`CtrPost`, `GhPost`,
`KeyPost`); and that it is constant time (`ctr_rel`, `gh_rel`, `key_rel`).
`vg_ghash` is called in a frame that pushes its stack argument
(`push {r12, lr}`) in the 8 bytes below the stack pointer;
`vg_sm4_ctr32` uses the 1520 bytes below it, and `vg_sm4_expand_key` 1456
(`below`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.Arm

open VG VG.Arm VG.Impl.Sm4Gcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom ctr32)

/-! ## Memory -/

theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    bytesAt m' p n = bytesAt m p n := Proof.Cmac.bytesAt_frame hf hd hn

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) : blockAt m' p = blockAt m p := by
  rw [blockAt, blockAt, bytesAt_frame hf hd (by decide)]

theorem blocksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, 16 * n⟩ : Region).Disjoint r) (hn : 16 * n ≤ 2 ^ 64) :
    blocksAt m' p n = blocksAt m p n := by
  rw [Proof.Gcm.blocksAt_eq, Proof.Gcm.blocksAt_eq, bytesAt_frame hf hd hn]

theorem toNat_ofNat32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- Addresses below a pointer do not wrap. -/
theorem addr_sub {a : BitVec 32} {k : Nat} (h : k ≤ a.toNat) :
    State.addr (a - BitVec.ofNat 32 k) = State.addr a - BitVec.ofNat 64 k := by
  simp only [State.addr]
  apply BitVec.eq_of_toNat_eq
  have := a.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (a := k) (by omega),
    Nat.mod_eq_of_lt (a := a.toNat) (by omega)]
  omega

theorem addr_toNat (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := a.isLt; omega)

/-- The 1520 bytes below the stack pointer `sp`, which the calls use: all of
them `vg_sm4_ctr32`, and the frame of `vg_ghash` the 8 bytes `push8 sp`. -/
abbrev below (sp : BitVec 32) : Region := ⟨State.addr sp - BitVec.ofNat 64 1520, 1520⟩

/-- The 8 bytes below the stack pointer `sp`, where the frames push the stack
arguments. -/
abbrev push8 (sp : BitVec 32) : Region := ⟨State.addr sp - 8, 8⟩

/-- The `n` bytes below `sp` are among the 1520 of `below sp`. -/
theorem below_sub (sp : BitVec 32) {n : Nat} (hn : n ≤ 1520) :
    Region.Sub ⟨State.addr sp - BitVec.ofNat 64 n, n⟩ (below sp) := by
  have e : State.addr sp - BitVec.ofNat 64 n =
      State.addr sp - BitVec.ofNat 64 1520 + BitVec.ofNat 64 (1520 - n) := by
    have := sp.isLt
    apply BitVec.eq_of_toNat_eq
    simp only [State.addr, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  rw [e]
  exact Offset.sub_base _ (by omega)

theorem push8_sub (sp : BitVec 32) : Region.Sub (push8 sp) (below sp) :=
  below_sub sp (n := 8) (by decide)

/-- `armStack`'s bytes below `sp`, as a region of `below sp`. -/
theorem belowA_sub {sp : BitVec 32} {n : Nat} (hn : n ≤ 1520) (hsp : 1520 ≤ sp.toNat) :
    Region.Sub (FrameStack.belowA sp n) (below sp) := by
  simp only [FrameStack.belowA]
  rw [FrameStack.addr_sub' (by omega)]
  exact below_sub sp hn

theorem storeWords_two (m : Mem) (a : BitVec 32) (x y : BitVec 32) :
    storeWords m a [x, y] = (m.writeW (State.addr a) x).writeW (State.addr (a + 4)) y := rfl

theorem e8 : BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length) = 8 := rfl

section Push
variable {s : State} (hsp : 8 ≤ s.sp.toNat)
include hsp

theorem hA : State.addr (s.sp - 8) = State.addr s.sp - 8 := addr_sub hsp

theorem hspA : (s.sp - 8).toNat = s.sp.toNat - 8 :=
  BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hsp)

theorem hA4 : State.addr (s.sp - 8 + BitVec.ofNat 32 4) = State.addr s.sp - 8 + 4 := by
  have := s.sp.isLt
  rw [addr_add (by rw [hspA hsp]; omega), hA hsp]; rfl

/-- The memory after `push {r12, lr}`. -/
theorem amem : (pushed [.r12, .lr] s).mem =
    (s.mem.writeW (State.addr s.sp - 8) (s.gpr .r12)).writeW (State.addr s.sp - 8 + 4) (s.gpr .lr) := by
  show storeWords s.mem (s.sp - BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length)) [s.gpr .r12, s.gpr .lr] = _
  rw [e8, storeWords_two, hA hsp, show (s.sp - 8 + 4 : BitVec 32) = s.sp - 8 + BitVec.ofNat 32 4 from rfl,
    hA4 hsp]

/-- The push writes only the 8 bytes below the stack pointer. -/
theorem fA : Frame [push8 s.sp] s.mem (pushed [.r12, .lr] s).mem := by
  rw [amem hsp]
  refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _ ?_
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  · simp only [Region.Contains]
    rw [Offset.add_sub_cancel_left]; decide

omit hsp in
theorem pushed_sp8 : (pushed [.r12, .lr] s).sp = s.sp - 8 := by simp only [pushed_sp, e8]

/-- The stack arguments the push leaves. -/
theorem arg0 : stackArg (pushed [.r12, .lr] s) 0 = s.gpr .r12 := by
  rw [stackArg, show stackArgAddr (pushed [.r12, .lr] s) 0 = State.addr s.sp - 8 by
      unfold stackArgAddr; rw [pushed_sp8, show s.sp - 8 + BitVec.ofNat 32 (4 * 0) = s.sp - 8 from
        BitVec.add_zero _, hA hsp],
    amem hsp, Mem.readW_writeW_sep
    (Offset.sep_base (State.addr s.sp - 8) (n := 4) (e := 4) (k := 4) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self32]

theorem arg1 : stackArg (pushed [.r12, .lr] s) 1 = s.gpr .lr := by
  rw [stackArg, show stackArgAddr (pushed [.r12, .lr] s) 1 = State.addr s.sp - 8 + 4 by
      unfold stackArgAddr; rw [pushed_sp8]; exact hA4 hsp,
    amem hsp, Mem.readW_writeW_self32]

theorem argAddr0 : stackArgAddr (pushed [.r12, .lr] s) 0 = State.addr s.sp - 8 := by
  unfold stackArgAddr; rw [pushed_sp8, show s.sp - 8 + BitVec.ofNat 32 (4 * 0) = s.sp - 8 from
    BitVec.add_zero _, hA hsp]

/-- The register the pop loads is `r12`, as pushed, if the frame's body
changes nothing outside `rs`, which are apart from the 4 bytes below
the stack pointer's frame. -/
theorem popSlot {s₂ : State} {rs : List Region} (hf : Frame rs (pushed [.r12, .lr] s).mem s₂.mem)
    (hd : ∀ r ∈ rs, (⟨State.addr s.sp - 8, 4⟩ : Region).Disjoint r) :
    s₂.mem.readW (State.addr (pushed [.r12, .lr] s).sp) 32 = s.gpr .r12 := by
  rw [pushed_sp8, hA hsp, hf.readW (r := ⟨State.addr s.sp - 8, 4⟩) (a := State.addr s.sp - 8) (w := 32)
    (Region.contains_self _ _) hd (by decide), amem hsp, Mem.readW_writeW_sep
    (Offset.sep_base (State.addr s.sp - 8) (n := 4) (e := 4) (k := 4) (by decide) (by decide)) (by decide),
    Mem.readW_writeW_self32]

end Push

@[simp] theorem stackArg_callEntry (s : State) (i : Nat) : stackArg s.callEntry i = stackArg s i := rfl
@[simp] theorem stackArgAddr_callEntry (s : State) (i : Nat) : stackArgAddr s.callEntry i = stackArgAddr s i := rfl

theorem view_gpr (s : State) (rd wr : List Region) (r : Reg) (hr : r ∉ linkRegs) :
    ((pushed [.r12, .lr] s).callEntry.withRegions rd wr).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr]

theorem view_sp (s : State) (rd wr : List Region) :
    ((pushed [.r12, .lr] s).callEntry.withRegions rd wr).sp = s.sp - 8 := by
  simp only [State.withRegions_sp, State.callEntry_sp, pushed_sp8]

theorem view_mem (s : State) (rd wr : List Region) :
    ((pushed [.r12, .lr] s).callEntry.withRegions rd wr).mem = (pushed [.r12, .lr] s).mem := by
  simp only [State.withRegions_mem, State.callEntry_mem]

theorem cover_pushed {s : State} {rs : List Region} (h : Covers rs s.wr) : Covers rs (pushed [.r12, .lr] s).wr := by
  intro x n' hi
  obtain ⟨r', hr', hc'⟩ := h x n' hi
  exact ⟨r', by rw [pushed_wr]; exact List.mem_cons_of_mem _ hr', hc'⟩

theorem cover_pushed' {s : State} {rs : List Region} (h : Covers rs (s.rd ++ s.wr)) :
    Covers rs ((pushed [.r12, .lr] s).rd ++ (pushed [.r12, .lr] s).wr) := by
  intro x n' hi
  obtain ⟨r', hr', hc'⟩ := h x n' hi
  refine ⟨r', ?_, hc'⟩
  rcases List.mem_append.mp hr' with h' | h'
  · exact List.mem_append_left _ h'
  · exact List.mem_append_right _ (by rw [pushed_wr]; exact List.mem_cons_of_mem _ h')

theorem pushed_wr8 {s : State} (hsp : 8 ≤ s.sp.toNat) :
    (pushed [.r12, .lr] s).wr = ⟨State.addr s.sp - 8, 8⟩ :: s.wr := by
  rw [pushed_wr, show 4 * [Reg.r12, Reg.lr].length = 8 from rfl, show BitVec.ofNat 32 8 = 8 from rfl, hA hsp]

theorem cover_frame {s : State} (hsp : 8 ≤ s.sp.toNat) {n : Nat} (hn : n ≤ 8) :
    Covers [⟨State.addr s.sp - 8, n⟩] ((pushed [.r12, .lr] s).rd ++ (pushed [.r12, .lr] s).wr) := by
  intro x n' ⟨r, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst hr
  refine ⟨_, List.mem_append_right _ (by rw [pushed_wr8 hsp]; exact List.mem_cons_self ..), ?_⟩
  simp only [Region.Contains] at hc ⊢; omega

theorem covers_append' {xs ys ts : List Region} (h₁ : Covers xs ts) (h₂ : Covers ys ts) :
    Covers (xs ++ ys) ts := by
  intro a n ⟨x, hx, hc⟩
  rcases List.mem_append.mp hx with hx | hx
  · exact h₁ a n ⟨x, hx, hc⟩
  · exact h₂ a n ⟨x, hx, hc⟩

theorem gh_noCalls : Impl.Gcm.Arm.ghash.noCalls = true := by decide +kernel

/-- The 4 bytes `push {r12, lr}` stores `r12` to, among `below sp`. -/
theorem slot_sub (sp : BitVec 32) : Region.Sub ⟨State.addr sp - 8, 4⟩ (below sp) :=
  fun x hx => push8_sub sp x (Region.sub_prefix (by decide) x hx)

/-! ## `vg_sm4_ctr32` -/

theorem ctr_stack : FrameStack.armStack Impl.Sm4.Arm.BatchCtr32.ctr32Framed ≤ 1520 := by decide +kernel

/-- What a call of `vg_sm4_ctr32` needs: the key schedule at `K`, the counter
block at `C` and `n` blocks at `D`, in `r0`, `r2`, `r3` and `r12` (which
`ctrCall` moves to its argument registers), and the 1520 bytes below the
stack pointer. -/
structure CtrCall (s : State) (K C D : BitVec 32) (n : Nat) : Prop where
  r0 : s.gpr .r0 = K
  r2 : s.gpr .r2 = C
  r3 : s.gpr .r3 = D
  r12 : s.gpr .r12 = BitVec.ofNat 32 n
  hsp : 1520 ≤ s.sp.toNat
  fitK : K.toNat + 128 ≤ 2 ^ 32
  fitC : C.toNat + 16 ≤ 2 ^ 32
  fitD : D.toNat + 16 * n ≤ 2 ^ 32
  kc : (⟨State.addr K, 128⟩ : Region).Disjoint ⟨State.addr C, 16⟩
  kd : (⟨State.addr K, 128⟩ : Region).Disjoint ⟨State.addr D, 16 * n⟩
  cd : (⟨State.addr C, 16⟩ : Region).Disjoint ⟨State.addr D, 16 * n⟩
  bk : (below s.sp).Disjoint ⟨State.addr K, 128⟩
  bc : (below s.sp).Disjoint ⟨State.addr C, 16⟩
  bd : (below s.sp).Disjoint ⟨State.addr D, 16 * n⟩
  reads : Covers [⟨State.addr K, 128⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr C, 16⟩, ⟨State.addr D, 16 * n⟩] s.wr

/-- What a call of `vg_sm4_ctr32` leaves. -/
structure CtrPost (s : State) (K C D : BitVec 32) (n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr C, 16⟩, ⟨State.addr D, 16 * n⟩, below s.sp] s.mem s'.mem
  out : blocksAt s'.mem (State.addr D) n =
    ctr32 (Spec.Sm4.Gcm.ctxCiph s.mem (State.addr K)) (blockAt s.mem (State.addr C))
      (blocksAt s.mem (State.addr D) n)
  ctr : blockAt s'.mem (State.addr C) = Nat.repeat Spec.Gcm.inc32 n (blockAt s.mem (State.addr C))

/-- The state `ctrCall`'s moves leave. -/
def ctrArgs (s : State) : State :=
  ((s.setReg .r1 (s.gpr .r2)).setReg .r2 (s.gpr .r3)).setReg .r3 (s.gpr .r12)

theorem ctrArgs_exec (s : State) :
    execBlock isa [.mov .r1 (.reg .r2), .mov .r2 (.reg .r3), .mov .r3 (.reg .r12)] s = some (ctrArgs s, []) := rfl

abbrev ctrRd (K : BitVec 32) : List Region := [⟨State.addr K, 128⟩]
abbrev ctrWr (C D : BitVec 32) (n : Nat) : List Region :=
  [⟨State.addr C, 16⟩, ⟨State.addr D, n * 16⟩]

namespace CtrCall
variable {s : State} {K C D : BitVec 32} {n : Nat} (h : CtrCall s K C D n)
include h

theorem n_lt : n < 2 ^ 32 := by have := h.fitD; omega

theorem g0 : (ctrArgs s).gpr .r0 = K := by
  simp only [ctrArgs, VG.Arm.RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte]; exact h.r0
theorem g1 : (ctrArgs s).gpr .r1 = C := by
  simp only [ctrArgs, VG.Arm.RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte]; exact h.r2
theorem g2 : (ctrArgs s).gpr .r2 = D := by
  simp only [ctrArgs, VG.Arm.RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte]; exact h.r3
theorem g3 : (ctrArgs s).gpr .r3 = BitVec.ofNat 32 n := by
  simp only [ctrArgs, VG.Arm.RegUpd.gpr_setReg, reduceCtorEq, ↓reduceIte]; exact h.r12

omit h in
theorem a_sp : (ctrArgs s).sp = s.sp := rfl
omit h in
theorem a_mem : (ctrArgs s).mem = s.mem := rfl
omit h in
theorem a_rd : (ctrArgs s).rd = s.rd := rfl
omit h in
theorem a_wr : (ctrArgs s).wr = s.wr := rfl

theorem pre : (Proof.Sm4.ctr32Contract Arm.abi 1520).pre
    ((ctrArgs s).callEntry.withRegions (ctrRd K) (ctrWr C D n)) := by
  have hn := toNat_ofNat32 h.n_lt
  sig_pre [Proof.Sm4.ctr32Contract, Proof.Sm4.ctr32Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  rw [h.r0, h.r2, h.r3, h.r12, hn, Nat.mul_comm n 16]
  exact ⟨h.hsp, by have := s.sp.isLt; omega, rfl, by unfold ctrWr; rw [Nat.mul_comm n 16]; rfl, h.kc, h.kd, h.cd,
    h.bk, h.bc, h.bd, h.fitK, h.fitC, h.fitD⟩

theorem cov : Covers (ctrRd K ++ ctrWr C D n) ((ctrArgs s).rd ++ (ctrArgs s).wr) := by
  rw [a_rd, a_wr, show ctrWr C D n = [⟨State.addr C, 16⟩, ⟨State.addr D, 16 * n⟩] by rw [Nat.mul_comm]]
  refine covers_append' h.reads (fun x n' hi => ?_)
  obtain ⟨r', hr', hc'⟩ := h.writes x n' hi
  exact ⟨r', List.mem_append_right _ hr', hc'⟩

theorem covW : Covers (ctrWr C D n) (ctrArgs s).wr := by
  rw [a_wr, show ctrWr C D n = [⟨State.addr C, 16⟩, ⟨State.addr D, 16 * n⟩] by rw [Nat.mul_comm]]
  exact h.writes

end CtrCall

theorem ctr_call {s : State} {K C D : BitVec 32} {n : Nat} (h : CtrCall s K C D n) :
    WP isa ctrCall s (CtrPost s K C D n) := by
  refine WP.seq (WP.of_runBlock ⟨ctrArgs s, rfl, ?_⟩)
  refine FrameStack.WP.callF (k := Proof.Sm4.ctr32Contract Arm.abi 1520) Proof.Sm4.Arm.Batch32Verified.framed.1
    (rd := ctrRd K) (wr := ctrWr C D n) h.pre h.cov h.covW
    (by rw [CtrCall.a_sp]; exact Nat.le_trans ctr_stack h.hsp) ?_
  intro s' hrd hwr hsp hf hcs hpost
  have hn := toNat_ofNat32 h.n_lt
  sig_post [Proof.Sm4.ctr32Contract, Proof.Sm4.ctr32Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hpost
  rw [h.r0, h.r2, h.r3, h.r12, hn] at hpost
  obtain ⟨hdata, hctr⟩ := hpost
  refine ⟨hrd, hwr, hsp, fun r hr hlr => ?_, ?_, hdata, hctr⟩
  · rw [hcs r hr hlr]
    have h1 : r ≠ .r1 := by rintro rfl; revert hr; decide
    have h2 : r ≠ .r2 := by rintro rfl; revert hr; decide
    have h3 : r ≠ .r3 := by rintro rfl; revert hr; decide
    simp only [ctrArgs, VG.Arm.RegUpd.gpr_setReg_of_ne _ _ h1, VG.Arm.RegUpd.gpr_setReg_of_ne _ _ h2,
      VG.Arm.RegUpd.gpr_setReg_of_ne _ _ h3]
  · rw [CtrCall.a_mem] at hf
    rw [CtrCall.a_sp] at hf
    refine hf.sub fun r hr => ?_
    simp only [ctrWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨⟨State.addr D, 16 * n⟩, by simp, fun _ hx => by rwa [Nat.mul_comm] at hx⟩
    · exact ⟨below s.sp, by simp, belowA_sub ctr_stack h.hsp⟩

/-- Calls of `vg_sm4_ctr32` with the same arguments and stack pointer in both
runs are constant time. -/
theorem ctr_rel {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K C D : BitVec 32, ∃ n : Nat,
      CtrCall s₁ K C D n ∧ CtrCall s₂ K C D n ∧ s₁.sp = s₂.sp) :
    RelCT isa P ctrCall fun _ _ => True := by
  intro a b t₁ t₂ a' b' hp e₁ e₂
  obtain ⟨K, C, D, n, h₁, h₂, hsp⟩ := h _ _ hp
  cases e₁ with | seq x₁ y₁ =>
  cases e₂ with | seq x₂ y₂ =>
  cases x₁ with | block x₁ =>
  cases x₂ with | block x₂ =>
  rw [ctrArgs_exec, Option.some.injEq, Prod.mk.injEq] at x₁ x₂
  obtain ⟨rfl, rfl⟩ := x₁
  obtain ⟨rfl, rfl⟩ := x₂
  have hn := toNat_ofNat32 h₁.n_lt
  have r := RelCT.call (k := Proof.Sm4.ctr32Contract Arm.abi 1520) Proof.Sm4.Arm.Batch32Verified.framed.1
    Proof.Sm4.Arm.Batch32Verified.framed.2.1 (ctrRd K) (ctrWr C D n)
    (P := fun x y => x = ctrArgs a ∧ y = ctrArgs b) (fun x y ⟨ex, ey⟩ => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ y₁ y₂
  · exact ⟨by rw [r.1], trivial⟩
  subst ex ey
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.cov, h₁.covW, h₂.cov, h₂.covW⟩
  sig_pub [Proof.Sm4.ctr32Contract, Proof.Sm4.ctr32Sig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  rw [h₁.r0, h₁.r2, h₁.r3, h₁.r12, h₂.r0, h₂.r2, h₂.r3, h₂.r12, hsp]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## `vg_ghash` -/

/-- What a call of `vg_ghash` needs: the hash subkey at `H`, the accumulator
at `Y`, `n` blocks at `D` and working space at `S`, in `r12` to push. -/
structure GhCall (s : State) (H Y D S : BitVec 32) (n : Nat) : Prop where
  r0 : s.gpr .r0 = H
  r1 : s.gpr .r1 = Y
  r2 : s.gpr .r2 = D
  r3 : s.gpr .r3 = BitVec.ofNat 32 n
  r12 : s.gpr .r12 = S
  big : 1520 ≤ s.sp.toNat
  fitH : H.toNat + 16 ≤ 2 ^ 32
  fitY : Y.toNat + 16 ≤ 2 ^ 32
  fitD : D.toNat + 16 * n ≤ 2 ^ 32
  fitS : S.toNat + 256 ≤ 2 ^ 32
  hy : (⟨State.addr H, 16⟩ : Region).Disjoint ⟨State.addr Y, 16⟩
  hs : (⟨State.addr H, 16⟩ : Region).Disjoint ⟨State.addr S, 256⟩
  yd : (⟨State.addr Y, 16⟩ : Region).Disjoint ⟨State.addr D, 16 * n⟩
  ys : (⟨State.addr Y, 16⟩ : Region).Disjoint ⟨State.addr S, 256⟩
  ds : (⟨State.addr D, 16 * n⟩ : Region).Disjoint ⟨State.addr S, 256⟩
  bh : (below s.sp).Disjoint ⟨State.addr H, 16⟩
  by' : (below s.sp).Disjoint ⟨State.addr Y, 16⟩
  bd : (below s.sp).Disjoint ⟨State.addr D, 16 * n⟩
  bs : (below s.sp).Disjoint ⟨State.addr S, 256⟩
  reads : Covers [⟨State.addr H, 16⟩, ⟨State.addr D, 16 * n⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr Y, 16⟩, ⟨State.addr S, 256⟩] s.wr

/-- What a call of `vg_ghash` leaves. -/
structure GhPost (s : State) (H Y D S : BitVec 32) (n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr Y, 16⟩, ⟨State.addr S, 256⟩, below s.sp] s.mem s'.mem
  out : blockAt s'.mem (State.addr Y) =
    ghashFrom (blockAt s.mem (State.addr H)) (blockAt s.mem (State.addr Y)) (blocksAt s.mem (State.addr D) n)

abbrev ghRd (sp H D : BitVec 32) (n : Nat) : List Region :=
  [⟨State.addr H, 16⟩, ⟨State.addr D, 16 * n⟩, ⟨State.addr sp - 8, 4⟩]
abbrev ghWr (Y S : BitVec 32) : List Region := [⟨State.addr Y, 16⟩, ⟨State.addr S, 256⟩]

namespace GhCall
variable {s : State} {H Y D S : BitVec 32} {n : Nat} (h : GhCall s H Y D S n)
include h

theorem hsp : 8 ≤ s.sp.toNat := by have := h.big; omega

theorem n_lt : n < 2 ^ 32 := by have := h.fitD; omega

theorem pre : Proof.Gcm.ghashArm.pre
    ((pushed [.r12, .lr] s).callEntry.withRegions (ghRd s.sp H D n) (ghWr Y S)) := by
  have hn := toNat_ofNat32 h.n_lt
  have b4 : ∀ x : Region, (below s.sp).Disjoint x → (⟨State.addr s.sp - 8, 4⟩ : Region).Disjoint x :=
    fun x hx => hx.sub_left (slot_sub s.sp)
  simp only [Proof.Gcm.ghashArm, arg0 h.hsp, argAddr0 h.hsp, view_gpr _ _ _ .r0 (by decide),
    view_gpr _ _ _ .r1 (by decide), view_gpr _ _ _ .r2 (by decide), view_gpr _ _ _ .r3 (by decide), h.r0, h.r1,
    h.r2, h.r3, h.r12, hn, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem,
    State.callEntry_mem, view_sp, hspA h.hsp, stackArgAddr_withRegions, stackArg_withRegions, stackArg_callEntry,
    stackArgAddr_callEntry, arg0 h.hsp, arg1 h.hsp, argAddr0 h.hsp, h.r12, hn]
  refine ⟨trivial, trivial, h.hy, h.hs, h.yd, h.ys, h.ds, (b4 _ h.by').symm, (b4 _ h.bs).symm, h.fitH, h.fitY,
    h.fitD, h.fitS, ?_⟩
  have := s.sp.isLt; omega

theorem cov : Covers (ghRd s.sp H D n ++ ghWr Y S)
    ((pushed [.r12, .lr] s).rd ++ (pushed [.r12, .lr] s).wr) := by
  have e : ghRd s.sp H D n = [⟨State.addr H, 16⟩, ⟨State.addr D, 16 * n⟩] ++ [⟨State.addr s.sp - 8, 4⟩] := rfl
  rw [e]
  refine covers_append' (covers_append' (cover_pushed' h.reads) (cover_frame h.hsp (by decide)))
    (cover_pushed' (fun x n' hi => ?_))
  obtain ⟨r', hr', hc'⟩ := h.writes x n' hi
  exact ⟨r', List.mem_append_right _ hr', hc'⟩

theorem covW : Covers (ghWr Y S) (pushed [.r12, .lr] s).wr := cover_pushed h.writes

end GhCall

theorem gh_call {s : State} {H Y D S : BitVec 32} {n : Nat} (h : GhCall s H Y D S n) :
    WP isa ghFrame s (GhPost s H Y D S n) := by
  refine WP.frame (rs := [.r12, .lr]) (r := .r12) rfl (by simpa using h.hsp) (by simp) ?_
  refine WP.call (k := Proof.Gcm.ghashArm) Proof.Gcm.Arm.ghash_correct
    (rd := ghRd s.sp H D n) (wr := ghWr Y S) h.pre h.cov h.covW ?_ gh_noCalls
  intro s₂ hrd₂ hwr₂ hsp₂ hf hcs _ hpost
  have hn := toNat_ofNat32 h.n_lt
  have fA' := fA (s := s) h.hsp
  have blockH : blockAt (pushed [.r12, .lr] s).mem (State.addr H) = blockAt s.mem (State.addr H) :=
    blockAt_frame fA' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (h.bh.sub_left (push8_sub s.sp)).symm)
  have blockY : blockAt (pushed [.r12, .lr] s).mem (State.addr Y) = blockAt s.mem (State.addr Y) :=
    blockAt_frame fA' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (h.by'.sub_left (push8_sub s.sp)).symm)
  have blocksD : blocksAt (pushed [.r12, .lr] s).mem (State.addr D) n = blocksAt s.mem (State.addr D) n :=
    blocksAt_frame fA' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (h.bd.sub_left (push8_sub s.sp)).symm) (by have := h.fitD; omega)
  simp only [Proof.Gcm.ghashArm, State.withRegions_mem, State.callEntry_mem, view_gpr _ _ _ .r0 (by decide),
    view_gpr _ _ _ .r1 (by decide), view_gpr _ _ _ .r2 (by decide), view_gpr _ _ _ .r3 (by decide), h.r0, h.r1,
    h.r2, h.r3, hn, blockH, blockY, blocksD] at hpost
  have fB : Frame (ghWr Y S) (pushed [.r12, .lr] s).mem s₂.mem := hf
  have slot : s₂.mem.readW (State.addr (pushed [.r12, .lr] s).sp) 32 = s.gpr .r12 :=
    popSlot h.hsp fB (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.by'.sub_left (slot_sub s.sp)
      · exact h.bs.sub_left (slot_sub s.sp))
  refine ⟨?_, ?_, ?_, fun r hr hlr => ?_, ?_, ?_⟩
  · rw [popped_rd, hrd₂, pushed_rd]
  · rw [popped_wr, hwr₂, pushed_wr]; rfl
  · rw [popped_sp, hsp₂, pushed_sp8]; exact BitVec.sub_add_cancel _ _
  · by_cases h12 : r = .r12
    · subst h12
      show (s₂.setReg .r12 (s₂.mem.readW (State.addr s₂.sp) 32)).gpr .r12 = _
      rw [VG.Arm.RegUpd.gpr_setReg_self, hsp₂, slot]
    · rw [popped_gpr h12, hcs r hr hlr, pushed_gpr]
  · rw [popped_mem]
    refine (fA'.sub fun r hr => ⟨below s.sp, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact push8_sub s.sp⟩).trans
      (fB.sub fun r hr => ⟨r, by simp at hr; rcases hr with rfl | rfl <;> simp, fun _ h => h⟩)
  · rw [popped_mem]; exact hpost

theorem gh_rel {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ H Y D S : BitVec 32, ∃ n : Nat,
      GhCall s₁ H Y D S n ∧ GhCall s₂ H Y D S n ∧ s₁.sp = s₂.sp) :
    RelCT isa P ghFrame fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ hp => by obtain ⟨_, _, _, _, _, _, _, e⟩ := h _ _ hp; exact e) ?_
  intro a b t₁ t₂ a' b' ⟨s₁, s₂, hp, pa, pb⟩ e₁ e₂
  obtain ⟨H, Y, D, S, n, h₁, h₂, hsp⟩ := h _ _ hp
  rw [push_pushed (rs := [.r12, .lr]) rfl (by simpa using h₁.hsp), Option.some.injEq] at pa
  rw [push_pushed (rs := [.r12, .lr]) rfl (by simpa using h₂.hsp), Option.some.injEq] at pb
  subst pa pb
  refine RelCT.call (k := Proof.Gcm.ghashArm) Proof.Gcm.Arm.ghash_correct Proof.Gcm.Arm.ghash_ct
    (ghRd s₁.sp H D n) (ghWr Y S) (P := fun x y => x = pushed [.r12, .lr] s₁ ∧ y = pushed [.r12, .lr] s₂)
    (fun x y ⟨ex, ey⟩ => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  subst ex ey
  have p₁ := h₁.pre
  have p₂ := h₂.pre
  rw [← hsp] at p₂
  refine ⟨p₁, p₂, ?_, h₁.cov, h₁.covW, hsp ▸ h₂.cov, h₂.covW⟩
  simp only [Proof.Gcm.ghashArm, stackArg_withRegions, stackArg_callEntry, arg0 h₁.hsp, arg0 h₂.hsp,
    view_gpr _ _ _ .r0 (by decide), view_gpr _ _ _ .r1 (by decide), view_gpr _ _ _ .r2 (by decide),
    view_gpr _ _ _ .r3 (by decide), view_sp, h₁.r0, h₁.r1, h₁.r2, h₁.r3, h₁.r12, h₂.r0, h₂.r1, h₂.r2,
    h₂.r3, h₂.r12, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `vg_sm4_expand_key` -/

theorem key_stack : FrameStack.armStack
    (Impl.StackScratch.Arm.withRegScratchWiped 1456 .r2 364 Impl.Sm4.Arm.expandKey) ≤ 1456 := by decide +kernel

/-- What a call of `vg_sm4_expand_key` needs: the 16-byte key at `K` and the
key schedule at `C`, and the 1456 bytes below the stack pointer. -/
structure KeyCall (s : State) (K C : BitVec 32) : Prop where
  r0 : s.gpr .r0 = K
  r1 : s.gpr .r1 = C
  hsp : 1520 ≤ s.sp.toNat
  fitK : K.toNat + 16 ≤ 2 ^ 32
  fitC : C.toNat + 128 ≤ 2 ^ 32
  kc : (⟨State.addr K, 16⟩ : Region).Disjoint ⟨State.addr C, 128⟩
  bk : (below s.sp).Disjoint ⟨State.addr K, 16⟩
  bc : (below s.sp).Disjoint ⟨State.addr C, 128⟩
  reads : Covers [⟨State.addr K, 16⟩] (s.rd ++ s.wr)
  writes : Covers [⟨State.addr C, 128⟩] s.wr

/-- What a call of `vg_sm4_expand_key` leaves. -/
structure KeyPost (s : State) (K C : BitVec 32) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  saved : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r
  frame : Frame [⟨State.addr C, 128⟩, below s.sp] s.mem s'.mem
  out : Spec.Sm4.scheduleAt s'.mem (State.addr C) = Spec.Sm4.expandKey (Spec.Sm4.blockAt s.mem (State.addr K))

namespace KeyCall
variable {s : State} {K C : BitVec 32} (h : KeyCall s K C)
include h

theorem pre : (Spec.Sm4.expandKeyContract Arm.abi 1456).pre
    (s.callEntry.withRegions [⟨State.addr K, 16⟩] [⟨State.addr C, 128⟩]) := by
  sig_pre [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  rw [h.r0, h.r1]
  have s1 := below_sub s.sp (n := 1456) (by decide)
  exact ⟨by have := h.hsp; omega, by have := s.sp.isLt; omega, rfl, rfl, h.kc, h.bk.sub_left s1,
    h.bc.sub_left s1, h.fitK, h.fitC⟩

theorem cov : Covers ([⟨State.addr K, 16⟩] ++ [⟨State.addr C, 128⟩]) (s.rd ++ s.wr) :=
  covers_append' h.reads (fun x n' hi => by
    obtain ⟨r', hr', hc'⟩ := h.writes x n' hi
    exact ⟨r', List.mem_append_right _ hr', hc'⟩)

end KeyCall

theorem key_call {s : State} {K C : BitVec 32} (h : KeyCall s K C) : WP isa keyCall s (KeyPost s K C) := by
  refine FrameStack.WP.callF (k := Spec.Sm4.expandKeyContract Arm.abi 1456) Proof.Sm4.Arm.expandKey_framed.1
    (rd := [⟨State.addr K, 16⟩]) (wr := [⟨State.addr C, 128⟩]) h.pre h.cov h.writes
    (Nat.le_trans key_stack (by have := h.hsp; omega)) ?_
  intro s' hrd hwr hsp hf hcs hpost
  sig_post [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, Proof.Sm4.expandKeyPost, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val] at hpost
  rw [h.r0, h.r1] at hpost
  refine ⟨hrd, hwr, hsp, hcs, hf.sub fun r hr => ?_, hpost⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  · exact ⟨below s.sp, by simp, belowA_sub (Nat.le_trans key_stack (by decide)) h.hsp⟩

theorem key_rel {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ K C : BitVec 32, KeyCall s₁ K C ∧ KeyCall s₂ K C ∧ s₁.sp = s₂.sp) :
    RelCT isa P keyCall fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨K, C, h₁, h₂, hsp⟩ := h _ _ hp
  refine RelCT.call (k := Spec.Sm4.expandKeyContract Arm.abi 1456) Proof.Sm4.Arm.expandKey_framed.1
    Proof.Sm4.Arm.expandKey_framed.2.1 [⟨State.addr K, 16⟩] [⟨State.addr C, 128⟩]
    (P := fun x y => x = s₁ ∧ y = s₂) (fun x y ⟨ex, ey⟩ => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  subst ex ey
  refine ⟨h₁.pre, h₂.pre, ?_, h₁.cov, h₁.writes, h₂.cov, h₂.writes⟩
  sig_pub [Spec.Sm4.expandKeyContract, Spec.Sm4.expandKeySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  rw [h₁.r0, h₁.r1, h₂.r0, h₂.r1, hsp]
  exact ⟨rfl, rfl, rfl⟩

end VG.Proof.Sm4Gcm.Arm

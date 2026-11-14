module

public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.AArch64.Target
import VerifiedGarbage.Proof.Rsa.AArch64.PrivCallees
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Impl.Rsa.AArch64.PrivChecked
import VerifiedGarbage.Proof.Framework.AddrArith
meta import Lean.Elab.Tactic.Omega.Frontend
import VerifiedGarbage.Proof.Framework.InstancePriority

/-! ### `Rsa.AArch64.PrivCtx`, which only this module used -/

section

/-!
# `vg_rsa_private_checked` on AArch64: the contract on the registers

`chkA` states the shared contract (with the stack the frames use,
`stackBytes`) on the registers and the stack (`private_checked_implies`).
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64

/-- The stack below the stack pointer the function uses: a frame of 16 bytes
saving `x30` and one of 3232 bytes; its callees use none. -/
def stackBytes : Nat := 3248

theorem stackArgs_twelve (s : State) :
    List.map (stackArg s) (List.range 12) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11] := rfl

/-- `vg_rsa_private_checked(out = x0, out_len = x1, n = x2, n_len = x3,
e = x4, e_len = x5, input = x6, input_len = x7, p, p_len, q, q_len, dp,
dp_len, dq, dq_len, qinv, qinv_len, scratch, scratch_len)`, the last twelve
on the stack, using `stackBytes` bytes of stack. -/
def chkA : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let n : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let e : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat⟩
    let inp : Region := ⟨s.gpr .x6, (s.gpr .x7).toNat⟩
    let p : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let q : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
    let dp : Region := ⟨stackArg s 4, (stackArg s 5).toNat⟩
    let dq : Region := ⟨stackArg s 6, (stackArg s 7).toNat⟩
    let qi : Region := ⟨stackArg s 8, (stackArg s 9).toNat⟩
    let scr : Region := ⟨stackArg s 10, (stackArg s 11).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 96⟩
    let stk : Region := ⟨s.sp - BitVec.ofNat 64 stackBytes, stackBytes⟩
    stackBytes ≤ s.sp.toNat ∧ s.sp.toNat + 96 ≤ 2 ^ 64 ∧
      s.rd = [n, e, inp, p, q, dp, dq, qi, args] ∧ s.wr = [out, scr] ∧
      out.Disjoint n ∧ out.Disjoint e ∧ out.Disjoint inp ∧ out.Disjoint p ∧ out.Disjoint q ∧
      out.Disjoint dp ∧ out.Disjoint dq ∧ out.Disjoint qi ∧ out.Disjoint scr ∧ out.Disjoint args ∧
      n.Disjoint scr ∧ e.Disjoint scr ∧ inp.Disjoint scr ∧ p.Disjoint scr ∧ q.Disjoint scr ∧
      dp.Disjoint scr ∧ dq.Disjoint scr ∧ qi.Disjoint scr ∧ scr.Disjoint args ∧
      stk.Disjoint out ∧ stk.Disjoint n ∧ stk.Disjoint e ∧ stk.Disjoint inp ∧ stk.Disjoint p ∧
      stk.Disjoint q ∧ stk.Disjoint dp ∧ stk.Disjoint dq ∧ stk.Disjoint qi ∧ stk.Disjoint scr ∧
      stk.Disjoint args ∧
      (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x4).toNat + (s.gpr .x5).toNat ≤ 2 ^ 64 ∧ (s.gpr .x6).toNat + (s.gpr .x7).toNat ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
      (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64 ∧
      (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64 ∧
      (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64 ∧
      (stackArg s 8).toNat + (stackArg s 9).toNat ≤ 2 ^ 64 ∧
      (stackArg s 10).toNat + (stackArg s 11).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .x3).toNat ∧ (s.gpr .x1).toNat = (s.gpr .x3).toNat ∧
      (s.gpr .x7).toNat = (s.gpr .x3).toNat ∧ 1 ≤ (s.gpr .x5).toNat ∧ (s.gpr .x5).toNat ≤ (s.gpr .x3).toNat ∧
      1 ≤ (stackArg s 1).toNat ∧ (stackArg s 1).toNat < (s.gpr .x3).toNat ∧ 1 ≤ (stackArg s 3).toNat ∧
      (stackArg s 3).toNat < (s.gpr .x3).toNat ∧ (stackArg s 5).toNat = (stackArg s 1).toNat ∧
      (stackArg s 9).toNat = (stackArg s 1).toNat ∧ (stackArg s 7).toNat = (stackArg s 3).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .x3).toNat ≤ (stackArg s 11).toNat
  post s s' :=
    Spec.Rsa.writtenOutcome s'.mem (s.gpr .x0) (s.gpr .x3).toNat ((s'.gpr .x0).setWidth 32)
      (Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x3).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
        (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat))
  pub s₁ s₂ :=
    (∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r) ∧ s₁.sp = s₂.sp ∧
      (List.range 12).map (stackArg s₁) = (List.range 12).map (stackArg s₂) ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x2) (s₁.gpr .x3).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .x2) (s₂.gpr .x3).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .x4) (s₁.gpr .x5).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .x4) (s₂.gpr .x5).toNat

/-- A state meeting `chkA.pre`: a 64-byte modulus and input, a one-byte
`e`, one-byte primes, exponents and `qInv`, and the stack arguments at
`0x10000`. -/
def chkSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 64 | .x2 => 0x2000 | .x3 => 64 | .x4 => 0x3000 | .x5 => 1
    | .x6 => 0x4000 | .x7 => 64 | _ => 0
  sp := 0x10000
  mem a := bif Nat.beq a.toNat 0x10058 then 0x20
    else bif Nat.beq a.toNat 0x10001 then 0x41 else bif Nat.beq a.toNat 0x10008 then 1
    else bif Nat.beq a.toNat 0x10011 then 0x42 else bif Nat.beq a.toNat 0x10018 then 1
    else bif Nat.beq a.toNat 0x10021 then 0x43 else bif Nat.beq a.toNat 0x10028 then 1
    else bif Nat.beq a.toNat 0x10031 then 0x44 else bif Nat.beq a.toNat 0x10038 then 1
    else bif Nat.beq a.toNat 0x10041 then 0x45 else bif Nat.beq a.toNat 0x10048 then 1
    else bif Nat.beq a.toNat 0x10052 then 0x02 else bif Nat.beq a.toNat 0x10059 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 64⟩, ⟨0x4100, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩, ⟨0x4400, 1⟩,
    ⟨0x4500, 1⟩, ⟨0x10000, 96⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x20000, 8448⟩]

theorem private_checked_implies : chkA.Implies (Proof.Rsa.privateCheckedContract abi stackBytes) where
  pre := by
    intro s h
    sig_pre [Proof.Rsa.privateCheckedContract, Proof.Rsa.privateCheckedSig, abi, argRegs, chkA, stackBytes,
      stackArgs_twelve, List.append_eq, List.range, List.range.loop] at h
    sig_pre [Proof.Rsa.privateCheckedContract, Proof.Rsa.privateCheckedSig, abi, argRegs, chkA, stackBytes,
      stackArgs_twelve, List.append_eq, List.range, List.range.loop] at h
    sig_split h
    sig_reduce [Proof.Rsa.privateCheckedContract, Proof.Rsa.privateCheckedSig, abi, argRegs, chkA, stackBytes,
      stackArgs_twelve, List.append_eq, List.range, List.range.loop]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by
    sig_implies_post [Proof.Rsa.privateCheckedContract, Proof.Rsa.privateCheckedSig, abi, argRegs, chkA,
      stackBytes, stackArgs_twelve, List.append_eq, List.range, List.range.loop]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Proof.Rsa.privateCheckedContract, Proof.Rsa.privateCheckedSig, abi, argRegs, chkA, stackBytes,
      stackArgs_twelve, List.append_eq, List.range, List.range.loop] at h
    obtain ⟨hsp, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, h3]) hl
    refine ⟨?_, hsp, by simp only [stackArgs_twelve, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11],
      hn, he⟩
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  sat := by
    sig_implies_sat [Proof.Rsa.privateCheckedContract, Proof.Rsa.privateCheckedSig, abi, argRegs, chkA,
      stackBytes, stackArgs_twelve, List.append_eq] [chkSatState, stackArg, stackArgAddr, Mem.readW,
      Mem.read] using chkSatState

end VG.Proof.Rsa.AArch64

end

end


/-!
# `vg_rsa_private_checked` on AArch64: where everything is

The function's buffers and the `stackBytes` bytes of stack below the stack
pointer, from `B` up (`Lay`): the inner frame (`FR`, from `B`: the stack
arguments of the calls, the slots, `M` at `oM` and `n`'s values at `oPre`),
then the frame holding our return address (`LR`, at `B + frameBytes`). Our
stack arguments are at `B + stackBytes` (`ARGS`). `Lay.Ok` is what the
contract says of them; `Ctx` is what holds between the frames' pushes and
pops.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64.PrivChecked

/-- The arguments, and the lowest byte of the stack used (`sp - stackBytes`
on entry). -/
structure Lay where
  out : Addr
  ol : BitVec 64
  n : Addr
  k : BitVec 64
  e : Addr
  el : BitVec 64
  inp : Addr
  il : BitVec 64
  p : Addr
  pl : BitVec 64
  q : Addr
  ql : BitVec 64
  dp : Addr
  dpl : BitVec 64
  dq : Addr
  dql : BitVec 64
  qi : Addr
  qil : BitVec 64
  scr : Addr
  sl : BitVec 64
  B : Addr
  /-- Further regions the function may read: none for
  `vg_rsa_private_checked`; for `vg_rsa_private_checked_precomputed`, its
  last stack arguments and `pre`. -/
  X : List Region

namespace Lay

variable (L : Lay)

abbrev OUT : Region := ⟨L.out, L.ol.toNat⟩
abbrev N : Region := ⟨L.n, L.k.toNat⟩
abbrev E : Region := ⟨L.e, L.el.toNat⟩
abbrev IN : Region := ⟨L.inp, L.il.toNat⟩
abbrev P : Region := ⟨L.p, L.pl.toNat⟩
abbrev Q : Region := ⟨L.q, L.ql.toNat⟩
abbrev DP : Region := ⟨L.dp, L.dpl.toNat⟩
abbrev DQ : Region := ⟨L.dq, L.dql.toNat⟩
abbrev QI : Region := ⟨L.qi, L.qil.toNat⟩
abbrev SC : Region := ⟨L.scr, L.sl.toNat * 8⟩
/-- Our stack arguments. -/
abbrev ARGS : Region := ⟨L.B + BitVec.ofNat 64 stackBytes, 96⟩
/-- The stack used. -/
abbrev STK : Region := ⟨L.B, stackBytes⟩
/-- The frames: the inner one, and our return address. -/
abbrev FR : Region := ⟨L.B, frameBytes⟩
abbrev LR : Region := ⟨L.B + BitVec.ofNat 64 frameBytes, 16⟩

/-- `w = ⌈k / 8⌉`, and the bytes of `n`'s values. -/
abbrev pw : Nat := 2 * ((L.k.toNat + 7) / 8)

/-- `M` and `n`'s values, in the inner frame. -/
abbrev M : Region := ⟨L.B + BitVec.ofNat 64 oM, L.k.toNat⟩
abbrev PRE : Region := ⟨L.B + BitVec.ofNat 64 oPre, L.pw * 8⟩

/-- What the contract says of where the buffers and the stack are, and of
the lengths. -/
structure Ok : Prop where
  on : L.OUT.Disjoint L.N
  oe : L.OUT.Disjoint L.E
  oi : L.OUT.Disjoint L.IN
  op : L.OUT.Disjoint L.P
  oq : L.OUT.Disjoint L.Q
  odp : L.OUT.Disjoint L.DP
  odq : L.OUT.Disjoint L.DQ
  oqi : L.OUT.Disjoint L.QI
  osc : L.OUT.Disjoint L.SC
  oa : L.OUT.Disjoint L.ARGS
  nsc : L.N.Disjoint L.SC
  esc : L.E.Disjoint L.SC
  isc : L.IN.Disjoint L.SC
  psc : L.P.Disjoint L.SC
  qsc : L.Q.Disjoint L.SC
  dpsc : L.DP.Disjoint L.SC
  dqsc : L.DQ.Disjoint L.SC
  qisc : L.QI.Disjoint L.SC
  sca : L.SC.Disjoint L.ARGS
  ko : L.STK.Disjoint L.OUT
  kn : L.STK.Disjoint L.N
  ke : L.STK.Disjoint L.E
  ki : L.STK.Disjoint L.IN
  kp : L.STK.Disjoint L.P
  kq : L.STK.Disjoint L.Q
  kdp : L.STK.Disjoint L.DP
  kdq : L.STK.Disjoint L.DQ
  kqi : L.STK.Disjoint L.QI
  ksc : L.STK.Disjoint L.SC
  bo : L.out.toNat + L.ol.toNat ≤ 2 ^ 64
  bn : L.n.toNat + L.k.toNat ≤ 2 ^ 64
  be : L.e.toNat + L.el.toNat ≤ 2 ^ 64
  bi : L.inp.toNat + L.il.toNat ≤ 2 ^ 64
  bp : L.p.toNat + L.pl.toNat ≤ 2 ^ 64
  bq : L.q.toNat + L.ql.toNat ≤ 2 ^ 64
  bdp : L.dp.toNat + L.dpl.toNat ≤ 2 ^ 64
  bdq : L.dq.toNat + L.dql.toNat ≤ 2 ^ 64
  bqi : L.qi.toNat + L.qil.toNat ≤ 2 ^ 64
  bsc : L.scr.toNat + L.sl.toNat * 8 ≤ 2 ^ 64
  nB : L.B.toNat + 3344 ≤ 2 ^ 64
  klo : 64 ≤ L.k.toNat
  khi : L.k.toNat ≤ 1024
  olk : L.ol.toNat = L.k.toNat
  ilk : L.il.toNat = L.k.toNat
  el1 : 1 ≤ L.el.toNat
  elk : L.el.toNat ≤ L.k.toNat
  pl1 : 1 ≤ L.pl.toNat
  plk : L.pl.toNat < L.k.toNat
  ql1 : 1 ≤ L.ql.toNat
  qlk : L.ql.toNat < L.k.toNat
  dpl : L.dpl.toNat = L.pl.toNat
  qil : L.qil.toNat = L.pl.toNat
  dql : L.dql.toNat = L.ql.toNat
  slk : 16 * L.k.toNat + 32 ≤ L.sl.toNat

end Lay

/-! ## The layout of a call -/

/-- The layout of a call from `s`. -/
def lay (s : State) : Lay :=
  ⟨s.gpr .x0, s.gpr .x1, s.gpr .x2, s.gpr .x3, s.gpr .x4, s.gpr .x5, s.gpr .x6, s.gpr .x7,
    stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6,
    stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10, stackArg s 11,
    s.sp - BitVec.ofNat 64 stackBytes, []⟩

theorem lay_top (s : State) : (lay s).B + BitVec.ofNat 64 stackBytes = s.sp := BitVec.sub_add_cancel _ _

theorem lay_args (s : State) : (lay s).B + BitVec.ofNat 64 stackBytes = stackArgAddr s 0 := by
  simp only [lay, stackArgAddr]; bv_omega

theorem lay_ok {s : State} (h : chkA.pre s) : (lay s).Ok := by
  sig_split h
  rename_i hst h96 _ _ on oe oi op oq odp odq oqi osc oa nsc esc isc psc qsc dpsc dqsc qisc sca ko
    kn ke ki kp kq kdp kdq kqi ksc _ bo bn be bi bp bq bdp bdq bqi bsc _ob1 olk ilk el1 elk pl1 plk
    ql1 qlk dpl qil dql
  obtain ⟨klo, khi⟩ := _ob1
  have slk := h
  have ea : (lay s).ARGS = ⟨stackArgAddr s 0, 96⟩ := by simp only [Lay.ARGS, lay_args]
  have nB : (lay s).B.toNat + 3344 ≤ 2 ^ 64 := by
    simp only [lay]
    rw [Offset.toNat_sub_ofNat s.sp stackBytes]
    unfold stackBytes at hst ⊢
    omega_using [hst, h96]
  exact ⟨on, oe, oi, op, oq, odp, odq, oqi, osc, ea ▸ oa, nsc, esc, isc, psc, qsc, dpsc, dqsc, qisc,
    ea ▸ sca, ko, kn, ke, ki, kp, kq, kdp, kdq, kqi, ksc, bo, bn, be, bi, bp, bq, bdp, bdq, bqi, bsc, nB,
    klo, khi, olk, ilk, el1, elk, pl1, plk, ql1, qlk, dpl, qil, dql, slk⟩

end VG.Proof.Rsa.AArch64

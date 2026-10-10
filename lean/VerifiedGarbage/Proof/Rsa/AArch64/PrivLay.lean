import VerifiedGarbage.Proof.Rsa.AArch64.PrivCtx
import VerifiedGarbage.Impl.Rsa.AArch64.PrivChecked
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset

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
  slk : 16 * L.k.toNat ≤ L.sl.toNat

end Lay

/-! ## The layout of a call -/

/-- The layout of a call from `s`. -/
def lay (s : State) : Lay :=
  ⟨s.gpr .x0, s.gpr .x1, s.gpr .x2, s.gpr .x3, s.gpr .x4, s.gpr .x5, s.gpr .x6, s.gpr .x7,
    stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3, stackArg s 4, stackArg s 5, stackArg s 6,
    stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10, stackArg s 11,
    s.sp - BitVec.ofNat 64 stackBytes⟩

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
    omega
  exact ⟨on, oe, oi, op, oq, odp, odq, oqi, osc, ea ▸ oa, nsc, esc, isc, psc, qsc, dpsc, dqsc, qisc,
    ea ▸ sca, ko, kn, ke, ki, kp, kq, kdp, kdq, kqi, ksc, bo, bn, be, bi, bp, bq, bdp, bdq, bqi, bsc, nB,
    klo, khi, olk, ilk, el1, elk, pl1, plk, ql1, qlk, dpl, qil, dql, slk⟩

end VG.Proof.Rsa.AArch64

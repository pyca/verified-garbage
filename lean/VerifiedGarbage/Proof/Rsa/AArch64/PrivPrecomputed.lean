module

public import VerifiedGarbage.Proof.Rsa.AArch64.PrivCorrect
public import VerifiedGarbage.Proof.Rsa.AArch64.PrivCT
public import VerifiedGarbage.Proof.Rsa.AArch64.PrivVerified
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Rsa.AArch64.PrivCheckOk
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Rsa.AArch64.PrivCorrect
meta import VerifiedGarbage.Proof.Rsa.AArch64.PrivCT
meta import VerifiedGarbage.Proof.Rsa.Contract
meta import VerifiedGarbage.Proof.Bignum.Words
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Rsa.PreKey
meta import VerifiedGarbage.Proof.Rsa.AArch64.PrivCheckOk
meta import VerifiedGarbage.Proof.Bignum.AArch64.Copy
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rsa.PreWords
meta import VerifiedGarbage.Proof.Rsa.PreWords

/-!
# `vg_rsa_private_checked_precomputed` on AArch64

`vg_rsa_private_checked`'s frames, CRT and check, with `n`'s values copied
from the key's precomputed values `pre` (`pcCopy`) in place of calling
`vg_rsa_public_precompute`.

`chkPA` states the shared contract on the registers and the stack
(`private_checked_precomputed_implies`): `chkA` of the call reading only
`vg_rsa_private_checked`'s buffers and stack arguments (`rd0`), and what it
says of `pre`.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Rsa.AArch64.PrivChecked

theorem stackArgs_fourteen (s : State) :
    List.map (stackArg s) (List.range 14) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11, stackArg s 12, stackArg s 13] := rfl

@[simp] theorem stackArg_withRegions (s : State) (rd wr : List Region) (i : Nat) :
    stackArg (s.withRegions rd wr) i = stackArg s i := rfl
@[simp] theorem stackArgAddr_withRegions (s : State) (rd wr : List Region) (i : Nat) :
    stackArgAddr (s.withRegions rd wr) i = stackArgAddr s i := rfl

/-- The buffers `vg_rsa_private_checked` reads, and its stack arguments. -/
def rd0 (s : State) : List Region :=
  [⟨s.gpr .x2, (s.gpr .x3).toNat⟩, ⟨s.gpr .x4, (s.gpr .x5).toNat⟩, ⟨s.gpr .x6, (s.gpr .x7).toNat⟩,
    ⟨stackArg s 0, (stackArg s 1).toNat⟩, ⟨stackArg s 2, (stackArg s 3).toNat⟩,
    ⟨stackArg s 4, (stackArg s 5).toNat⟩, ⟨stackArg s 6, (stackArg s 7).toNat⟩,
    ⟨stackArg s 8, (stackArg s 9).toNat⟩, ⟨stackArgAddr s 0, 96⟩]

/-- `pre`. -/
abbrev preR (s : State) : Region := ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩

/-- `vg_rsa_private_checked_precomputed(…, pre, pre_len)`: `pre` and
`pre_len` our stack arguments 12 and 13. -/
def chkPA : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let scr : Region := ⟨stackArg s 10, (stackArg s 11).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 112⟩
    let stk : Region := ⟨s.sp - BitVec.ofNat 64 stackBytes, stackBytes⟩
    chkA.pre (s.withRegions (rd0 s) s.wr) ∧ s.sp.toNat + 112 ≤ 2 ^ 64 ∧
      s.rd = (rd0 s).take 8 ++ [preR s, args] ∧
      out.Disjoint (preR s) ∧ out.Disjoint args ∧ scr.Disjoint (preR s) ∧ scr.Disjoint args ∧
      stk.Disjoint (preR s) ∧ stk.Disjoint args ∧
      (stackArg s 12).toNat + (stackArg s 13).toNat * 8 ≤ 2 ^ 64 ∧
      (stackArg s 13).toNat =
        Spec.Rsa.privatePrecomputedWords (s.gpr .x3).toNat (stackArg s 1).toNat (stackArg s 3).toNat ∧
      Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat) =
        some (Spec.Rsa.wordsAt s.mem (stackArg s 12) (stackArg s 13).toNat)
  post := chkA.post
  pub s₁ s₂ := chkA.pub s₁ s₂ ∧ stackArg s₁ 12 = stackArg s₂ 12 ∧ stackArg s₁ 13 = stackArg s₂ 13

theorem sub96 (p : Addr) : Region.Sub ⟨p, 96⟩ ⟨p, 112⟩ := by
  simpa using Offset.sub_base p (d := 0) (n := 96) (k := 112) (by decide)

/-! ## A state that meets the contract -/

/-- The stack arguments of `preState`; the key (`keyMem`) has `n` at
`0x2000`, `p` at `0x4200`, `q` at `0x4300` and `pre` at `0x4800`. -/
def preArgs : List Nat :=
  [0x4200, 32, 0x4300, 32, 0x4400, 32, 0x4500, 32, 0x4600, 32, 0x10000, 0x420, 0x4800, 24]

/-- The memory of `preState`: the stack arguments from `2^40`, and the key. -/
def preMem (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.ble 0x10000000000 i && Nat.blt i 0x10000000070 then
    BitVec.ofNat 8 (preArgs.getD ((i - 0x10000000000) / 8) 0 / 256 ^ ((i - 0x10000000000) % 8))
  else bif Proof.Rsa.PreKey.keyIn i then Proof.Rsa.PreKey.keyMem a else 0

def preState : State where
  gpr r := match r with
    | .x0 => 0x5000 | .x1 => 64 | .x2 => 0x2000 | .x3 => 64 | .x4 => 0x2100 | .x5 => 1 | .x6 => 0x3000
    | .x7 => 64 | _ => 0
  sp := 0x10000000000
  mem := preMem
  rd := [⟨0x2000, 64⟩, ⟨0x2100, 1⟩, ⟨0x3000, 64⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩, ⟨0x4500, 32⟩,
    ⟨0x4600, 32⟩, ⟨0x4800, 192⟩, ⟨0x10000000000, 112⟩]
  wr := [⟨0x5000, 64⟩, ⟨0x10000, 8448⟩]

theorem preState_key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt preState.mem 0x2000 64)
    (Spec.Rsa.bytesAt preState.mem 0x4200 32) (Spec.Rsa.bytesAt preState.mem 0x4300 32) =
      some (Spec.Rsa.wordsAt preState.mem 0x4800 24) :=
  Proof.Rsa.PreKey.key_pre_of fun a ha => by
    have hs : (Nat.ble 0x10000000000 a.toNat && Nat.blt a.toNat 0x10000000070) = false := by
      simp only [Proof.Rsa.PreKey.keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha
      refine Bool.eq_false_iff.mpr fun h => ?_
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
      omega
    show (bif _ then _ else _) = _
    rw [hs, Bool.cond_false, ha, Bool.cond_true]

theorem pre_args : stackArg preState 0 = 0x4200 ∧ stackArg preState 1 = 32 ∧ stackArg preState 2 = 0x4300 ∧
    stackArg preState 3 = 32 ∧ stackArg preState 4 = 0x4400 ∧ stackArg preState 5 = 32 ∧
    stackArg preState 6 = 0x4500 ∧ stackArg preState 7 = 32 ∧ stackArg preState 8 = 0x4600 ∧
    stackArg preState 9 = 32 ∧ stackArg preState 10 = 0x10000 ∧ stackArg preState 11 = 0x420 ∧
    stackArg preState 12 = 0x4800 ∧ stackArg preState 13 = 24 := by
  decide

theorem satisfiablePre : ∃ s, (Proof.Rsa.privateCheckedPrecomputedContract abi stackBytes).pre s := by
  refine ⟨preState, ?_⟩
  sig_pre [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
    Proof.Rsa.privateCheckedSig, abi, argRegs, stackArgs_fourteen, List.append_eq, List.range, List.range.loop]
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := pre_args
  have hsp : (0x10000000000 : BitVec 64).toNat = 2 ^ 40 := by decide
  have hkb : ((0x10000000000 : BitVec 64) - BitVec.ofNat 64 stackBytes).toNat = 2 ^ 40 - stackBytes := by
    rw [BitVec.toNat_sub, hsp, BitVec.toNat_ofNat]; simp only [stackBytes]
  have ha : stackArgAddr preState 0 = 0x10000000000 := by decide
  simp only [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, ha]
  have kd : ∀ (b : BitVec 64) (n : Nat), b.toNat + n ≤ 2 ^ 20 →
      Region.Disjoint ⟨0x10000000000 - BitVec.ofNat 64 stackBytes, stackBytes⟩ ⟨b, n⟩ := fun b n h =>
    Region.disjoint_of_le (.inr (by dsimp only; rw [hkb]; simp only [stackBytes]; omega))
      (by dsimp only; rw [hkb]; simp only [stackBytes]; omega) (by dsimp only; omega)
  have kt : Region.Disjoint ⟨0x10000000000 - BitVec.ofNat 64 stackBytes, stackBytes⟩ ⟨0x10000000000, 112⟩ :=
    Region.disjoint_of_le (.inl (by dsimp only; rw [hkb, hsp]; simp only [stackBytes]; omega))
      (by dsimp only; rw [hkb]; simp only [stackBytes]; omega) (by dsimp only; rw [hsp]; omega)
  sig_and_intros
  rotate_right
  · exact preState_key
  all_goals first
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact kd _ _ (by decide)
    | exact kt
    | (rw [hsp]; simp only [stackBytes]; omega)
    | (simp only [Spec.Rsa.lenValid]; decide)

theorem private_checked_precomputed_implies : chkPA.Implies (Proof.Rsa.privateCheckedPrecomputedContract abi stackBytes) where
  pre := by
    intro s h
    sig_pre [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
      Proof.Rsa.privateCheckedSig, abi, argRegs, stackBytes,
      stackArgs_fourteen, List.append_eq, List.range, List.range.loop] at h
    sig_pre [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
      Proof.Rsa.privateCheckedSig, abi, argRegs, stackBytes,
      stackArgs_fourteen, List.append_eq, List.range, List.range.loop] at h
    sig_split h
    simp only [chkPA, chkA, rd0, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      State.withRegions_sp, stackArg_withRegions, stackArgAddr_withRegions, stackBytes]
    rename_i spl sph rd wr on oe oi op oq odp odq oqi osc opr oa nsc esc isc psc qsc dpsc dqsc qisc
      scpr sca ko kn ke ki kp kq kdp kdq kqi ksc kpr ka bo bn be bi bp bq bdp bdq bqi bsc bpr lv olk ilk
      el1 elk pl1 plk ql1 qlk dpl qil dql slk prl
    have s96 := sub96 (stackArgAddr s 0)
    exact ⟨⟨spl, by omega, trivial, wr, on, oe, oi, op, oq, odp, odq, oqi, osc, oa.sub_right s96, nsc, esc,
      isc, psc, qsc, dpsc, dqsc, qisc, sca.sub_right s96, ko, kn, ke, ki, kp, kq, kdp, kdq, kqi, ksc,
      ka.sub_right s96, bo, bn, be, bi, bp, bq, bdp, bdq, bqi, bsc, lv, olk, ilk, el1, elk, pl1, plk, ql1,
      qlk, dpl, qil, dql, slk⟩, sph, rd, opr, oa, scpr, sca, kpr, ka, bpr, prl, h⟩
  post := by
    sig_implies_post [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
      Proof.Rsa.privateCheckedSig, abi, argRegs, chkPA, chkA, stackBytes, stackArgs_fourteen, List.append_eq,
      List.range, List.range.loop]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
      Proof.Rsa.privateCheckedSig, abi, argRegs, stackBytes, stackArgs_fourteen, List.append_eq, List.range,
      List.range.loop] at h
    obtain ⟨hsp, hl, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12,
      a13⟩ := h
    have hl' := (List.append_inj hl (by simp [Spec.Rsa.bytesAt, h3, h5])).1
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, h3]) hl'
    refine ⟨⟨?_, hsp, by simp only [stackArgs_twelve, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11],
      hn, he⟩, a12, a13⟩
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  sat := satisfiablePre

/-! ## The copy of `n`'s values -/

/-- Where `pre` is: the second region of `X`. -/
def Lay.preA (L : Lay) : Addr := (L.X.getD 1 ⟨0, 0⟩).base

/-- What the copy needs of `pre` and our stack argument 12, on entry. -/
structure PreIn (L : Lay) (m₀ : Mem) : Prop where
  x : L.X = [⟨L.B + BitVec.ofNat 64 (arg 12), 8⟩, ⟨L.preA, L.pw * 8⟩]
  a12 : m₀.readW (L.B + BitVec.ofNat 64 (arg 12)) 64 = L.preA
  ao : L.OUT.Disjoint ⟨L.B + BitVec.ofNat 64 (arg 12), 8⟩
  asc : L.SC.Disjoint ⟨L.B + BitVec.ofNat 64 (arg 12), 8⟩
  bnd : L.preA.toNat + L.pw * 8 ≤ 2 ^ 64
  po : L.OUT.Disjoint ⟨L.preA, L.pw * 8⟩
  psc : L.SC.Disjoint ⟨L.preA, L.pw * 8⟩
  pk : L.STK.Disjoint ⟨L.preA, L.pw * 8⟩
  pc : Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt m₀ L.n L.k.toNat) = some (Spec.Rsa.wordsAt m₀ L.preA L.pw)
  /-- The key's factors' product is its modulus, which `pre` implies. -/
  pq : Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ L.p L.pl.toNat) * Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ L.q L.ql.toNat) =
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt m₀ L.n L.k.toNat)

section
variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}

/-- `Ctx.store`, keeping only the low halves of the callee-saved vector
registers. -/
theorem Ctx.storeV (hL : L.Ok) {t t' : State} (hc : Ctx L g vv m₀ t) (hrd : t'.rd = t.rd)
    (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hv : ∀ r ∈ preservedV, (t'.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64)
    (hg : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r) (hf : Frame [L.FR] t.mem t'.mem) :
    Ctx L g vv m₀ t' :=
  have h := hc.store (t' := { t' with v := t.v }) hL hrd hwr hsp rfl hg hf
  ⟨h.rd, h.wr, h.sp, h.cs, fun r hr => (hv r hr).trans (hc.vs r hr), h.lr, h.frame⟩

/-- Changes only within `PRE`, from `Outside`. -/
theorem pre_frame (hL : L.Ok) {m m' : Mem}
    (h : VG.Proof.Bignum.Outside L.B oPre (8 * L.pw) m m') : Frame [L.PRE] m m' := by
  have hk := hL.khi
  intro x hx
  apply h
  have := hx L.PRE (List.mem_singleton_self _)
  simp only [Region.Contains] at this
  have e := Offset.lt_iff x L.B (d := oPre) (n := L.pw * 8) (by simp only [oPre, Lay.pw]; omega_arith)
  simp only [VG.Proof.Bignum.ofs]
  omega_arith

/-- The head of the copy: `pre`, `n`'s values' place and their length. -/
abbrev pcHead : List Instr := [.addImm .x .x17 .x0 0, .ldrSp .x16 (arg 12), .addImm .x .x12 .x1 0]

/-- The copy, and the status 1. -/
abbrev pcBody : Prog isa := .seq VG.Impl.Bignum.AArch64.copyWords (.block [.movz .x .x0 1 0])

theorem pcCopy_eq : pcCopy = .seq (.block pcHead) pcBody := rfl

theorem pcHead_ok (hL : L.Ok) (hP : PreIn L m₀) {t : State} (hc : Ctx L g vv m₀ t) (pa : PcArgs L t) :
    WP isa (.block pcHead) t fun t' => Ctx L g vv m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .x17 = L.B + BitVec.ofNat 64 oPre ∧ t'.gpr .x16 = L.preA ∧ t'.gpr .x12 = BitVec.ofNat 64 L.pw := by
  have hnB := hL.nB
  have in12 : InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 (arg 12)) 8 :=
    ⟨_, by rw [hc.rd, hc.wr, hP.x]; simp, Region.contains_self _ _⟩
  have v12 : t.mem.readW (L.B + BitVec.ofNat 64 (arg 12)) 64 = L.preA := by
    rw [hc.frame.readW (r := ⟨L.B + BitVec.ofNat 64 (arg 12), 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      · exact hP.ao.symm
      · exact hP.asc.symm
      · exact Offset.disjoint_base _ (by simp only [arg, frameBytes, stackBytes]; omega_arith)
          (by simp only [arg, frameBytes]; omega_arith)) (by decide)]
    exact hP.a12
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.load, State.read, Size.bits,
    BitVec.setWidth_eq, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, RegUpd.gpr_write,
    BitVec.add_zero, Option.map_some, reduceCtorEq, ite_false, ite_true,
    hc.sp, in12, read8, Option.some.injEq, exists_eq_left', and_self, v12,
    show arg 12 % 8 = 0 by decide, show arg 12 < 32768 by decide, show (0 : Nat) < 4096 by decide]
  exact ⟨hc.regs rfl rfl rfl rfl rfl (by priv_cs_tac), trivial, pa.x0, trivial, pa.x1⟩

theorem pcBody_ok (hL : L.Ok) (hP : PreIn L m₀) {t₁ : State} (hc₁ : Ctx L g vv m₀ t₁) (hs₁ : Slots L t₁.mem)
    (h17 : t₁.gpr .x17 = L.B + BitVec.ofNat 64 oPre) (h16 : t₁.gpr .x16 = L.preA)
    (h12 : t₁.gpr .x12 = BitVec.ofNat 64 L.pw) :
    WP isa pcBody t₁ fun t' => Ctx L g vv m₀ t' ∧ Slots L t'.mem ∧ Frame [L.PRE] t₁.mem t'.mem ∧
      t'.gpr .x0 = 1 ∧ Spec.Rsa.wordsAt t'.mem (L.B + BitVec.ofNat 64 oPre) L.pw = Spec.Rsa.wordsAt m₀ L.preA L.pw := by
  have hnB := hL.nB
  have hk := hL.khi
  have hk1 := hL.klo
  have hw1 : 1 ≤ L.pw := by unfold Lay.pw; omega_arith
  have hw2 : L.pw ≤ 256 := by unfold Lay.pw; omega_arith
  have hb := hP.bnd
  refine WP.seq (WP.mono (VG.Proof.Bignum.AArch64.copyWords_ok (S := L.preA) (eS := 0) (D := L.B) (eD := oPre)
    (w := L.pw) (by rw [h16]; exact (BitVec.add_zero _).symm) h17 h12 hw1 (by omega_arith)
    (by simp only [oPre]; omega_arith)
    (fun j hj => ⟨⟨L.preA, L.pw * 8⟩, by rw [hc₁.rd, hc₁.wr, hP.x]; simp,
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    (fun j hj => hc₁.inFrW hL (by simp only [oPre, frameBytes]; omega_arith))
    (fun j hj b hb' => Or.inr (by
      have hx : (⟨L.preA, L.pw * 8⟩ : Region).Contains
          (VG.Proof.Bignum.off L.preA (0 + 8 * j) + BitVec.ofNat 64 b) 1 := by
        rw [VG.Proof.Bignum.off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
        exact Offset.contains_base _ (by omega_arith) (by omega_arith)
      have hn : ¬ L.STK.Contains (VG.Proof.Bignum.off L.preA (0 + 8 * j) + BitVec.ofNat 64 b) 1 :=
        fun h => hP.pk _ h hx
      simp only [Region.Contains, stackBytes] at hn
      simp only [VG.Proof.Bignum.ofs, oPre]
      omega_arith)))
    fun t₂ ⟨_, hwd, ho, _, _, k⟩ => ?_)
  have hf₂ : Frame [L.PRE] t₁.mem t₂.mem := pre_frame hL ho
  have hPF : Region.Sub L.PRE L.FR :=
    Offset.sub_base _ (by simp only [oPre, frameBytes, Lay.pw]; omega_arith)
  have hc₂ : Ctx L g vv m₀ t₂ := hc₁.storeV hL k.rd k.wr k.sp k.vcs
    (fun r hr _ => k.gpr r fun h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> simp [preserved] at hr)
    (Frame.sub hf₂ fun r hr => ⟨L.FR, by simp, by rw [List.mem_singleton.mp hr]; exact hPF⟩)
  have hs₂ : Slots L t₂.mem := hs₁.frame hf₂ (fun R hR => by
    rw [List.mem_singleton.mp hR]
    exact Offset.disjoint L.B (d := oOut) (n := 48) (e := oPre) (k := L.pw * 8)
      (.inl (by decide)) (by simp only [oOut]; omega_arith) (by simp only [oPre]; omega_arith)) (by omega_arith)
  have hwt : Spec.Rsa.wordsAt t₂.mem (L.B + BitVec.ofNat 64 oPre) L.pw = Spec.Rsa.wordsAt m₀ L.preA L.pw := by
    rw [← frame_wordsAt hc₁.frame (p := L.preA) (n := L.pw) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [Nat.mul_comm]
      rcases hr with rfl | rfl | rfl
      exacts [hP.po.symm, hP.psc.symm, hP.pk.symm]) (by omega_arith)]
    simp only [Spec.Rsa.wordsAt]
    refine List.map_congr_left fun i hi => ?_
    have hi := List.mem_range.mp hi
    have := hwd i hi
    simp only [VG.Proof.Bignum.word, VG.Proof.Bignum.off, Nat.zero_add] at this
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, this]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits, Nat.mul_zero,
    show (0 : Nat) < 64 by decide, ite_true, BitVec.shiftLeft_zero, Option.some.injEq, exists_eq_left',
    RegUpd.mem_write, RegUpd.gpr_write]
  exact ⟨hc₂.regs rfl rfl rfl rfl rfl (by priv_cs_tac), hs₂, hf₂, by simp, hwt⟩

theorem pcCopy_ok (hL : L.Ok) (hP : PreIn L m₀) : StageOk L g vv m₀ pcCopy := by
  intro t hc hs pa
  rw [pcCopy_eq]
  refine WP.seq (WP.mono (pcHead_ok hL hP hc pa) fun t₁ ⟨hc₁, hm₁, h17, h16, h12⟩ => ?_)
  refine WP.mono (pcBody_ok hL hP hc₁ (hm₁ ▸ hs) h17 h16 h12) fun t' ⟨hc', hs', hf, h0, hw⟩ => ?_
  refine ⟨hc', hs', Frame.mono (rs' := pcWr L) (hm₁ ▸ hf) (by simp), ?_⟩
  simp only [PcOut, hc.n_bytes hL, hP.pc, h0]
  exact ⟨by decide, hw⟩

end

/-! ## The call, narrowed to what the proofs read -/

/-- Our stack argument 12, and `n`'s values at the start of `pre`. -/
def XP (s : State) : List Region := [⟨stackArgAddr s 12, 8⟩, ⟨stackArg s 12, (lay s).pw * 8⟩]

/-- The call, reading only `vg_rsa_private_checked`'s buffers and stack
arguments, and `XP`. -/
def narrowP (s : State) : State := s.withRegions (rd0 s ++ XP s) s.wr

theorem arg_slot12 (s : State) : stackArgAddr s 12 = (lay s).B + BitVec.ofNat 64 (arg 12) := by
  simp only [stackArgAddr, lay, arg, frameBytes, stackBytes]
  bv_omega

theorem sub_prefix (p : Addr) {a b : Nat} (h : a ≤ b) : Region.Sub ⟨p, a⟩ ⟨p, b⟩ := by
  simpa using Offset.sub_base p (d := 0) (n := a) (k := b) (by omega)

theorem sub_arg12 (s : State) : Region.Sub ⟨stackArgAddr s 12, 8⟩ ⟨stackArgAddr s 0, 112⟩ :=
  Offset.sub s.sp (d := 96) (n := 8) (e := 0) (k := 112) (by decide) (by decide)

/-- The public values of `privatePrecompute`'s, its first `2 w` words. -/
theorem publicPrecompute_of_private {nB pB qB : List Byte} {W : List (BitVec 64)}
    (h : Spec.Rsa.privatePrecompute nB pB qB = some W) :
    Spec.Rsa.publicPrecompute nB = some (W.take (2 * Spec.Rsa.modulusWords nB.length)) := by
  unfold Spec.Rsa.privatePrecompute at h
  split at h
  · cases hp : Spec.Rsa.publicPrecompute nB with
    | none => simp [hp] at h
    | some ws =>
      simp only [hp, Option.map_some, Option.some.injEq] at h
      subst h
      have hl : ws.length = 2 * Spec.Rsa.modulusWords nB.length := by
        unfold Spec.Rsa.publicPrecompute at hp
        dsimp only at hp
        split at hp
        · simp only [Option.some.injEq] at hp
          subst hp
          simp only [List.length_append, Spec.Rsa.toWords, List.length_map, List.length_range]
          omega
        · cases hp
      rw [List.append_assoc, List.take_left' hl]
  · cases h

theorem wordsAt_take (m : Mem) (p : Addr) {a n : Nat} (h : a ≤ n) :
    (Spec.Rsa.wordsAt m p n).take a = Spec.Rsa.wordsAt m p a := by
  simp only [Spec.Rsa.wordsAt, ← List.map_take, List.take_range, Nat.min_eq_left h]

/-- What the copy needs, from the contract. -/
theorem preIn {s : State} (h : chkPA.pre s) : PreIn (layW s (XP s)) s.mem := by
  obtain ⟨hA, -, -, opr, oa, scpr, sca, kpr, -, bpr, prl, hk⟩ := h
  have hL := lay_ok hA
  have hk1 := hL.klo
  have hpw : (lay s).pw ≤ (stackArg s 13).toNat := by
    rw [prl]
    simp only [Lay.pw, lay, Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords]
    omega
  have hpw' : (layW s (XP s)).pw ≤ (stackArg s 13).toNat := hpw
  have hpw2 : 2 * Spec.Rsa.modulusWords (s.gpr .x3).toNat ≤ (stackArg s 13).toNat := hpw
  have e12 := arg_slot12 s
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show XP s = [⟨(lay s).B + BitVec.ofNat 64 (arg 12), 8⟩, ⟨stackArg s 12, (lay s).pw * 8⟩]
    rw [← e12]; rfl
  · show s.mem.readW ((lay s).B + BitVec.ofNat 64 (arg 12)) 64 = stackArg s 12
    rw [← e12]; rfl
  · show Region.Disjoint ⟨s.gpr .x0, (s.gpr .x1).toNat⟩ ⟨(lay s).B + BitVec.ofNat 64 (arg 12), 8⟩
    rw [← e12]; exact oa.sub_right (sub_arg12 s)
  · show Region.Disjoint ⟨stackArg s 10, (stackArg s 11).toNat * 8⟩ ⟨(lay s).B + BitVec.ofNat 64 (arg 12), 8⟩
    rw [← e12]; exact sca.sub_right (sub_arg12 s)
  · show (stackArg s 12).toNat + (lay s).pw * 8 ≤ 2 ^ 64
    omega
  · exact opr.sub_right (sub_prefix _ (by omega))
  · exact scpr.sub_right (sub_prefix _ (by omega))
  · exact kpr.sub_right (sub_prefix _ (by omega))
  · show Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) =
      some (Spec.Rsa.wordsAt s.mem (stackArg s 12) (lay s).pw)
    rw [publicPrecompute_of_private hk, Proof.Rsa.bytesAt_length', wordsAt_take _ _ hpw2]
    rfl
  · exact Proof.Rsa.privatePrecompute_mul hk

/-- At the CRT's call, the key's factors' product is its modulus. -/
theorem keyProduct_call {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} (hL : L.Ok)
    {t : State} (hc : Ctx L g vv m₀ t) (ha : CrtArgs L t) (hP : PreIn L m₀) :
    KeyProduct (t.callEntry.withRegions (crtRd L) (crtWr L)) := by
  have sa : ∀ i < 10, stackArg (t.callEntry.withRegions (crtRd L) (crtWr L)) i = L.argv (i + 2) := by
    intro i hi
    simp only [stackArg, stackArgAddr, State.withRegions_mem, State.callEntry_mem, State.withRegions_sp,
      State.callEntry_sp, hc.sp]
    exact ha.stk i hi
  obtain ⟨kp, kq, -, -, -⟩ := hc.key_bytes hL
  simp only [KeyProduct, State.withRegions_mem, State.callEntry_mem,
    gpr_ce _ _ _ (by decide : Reg.x2 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x3 ∉ linkRegs),
    gpr_ce _ _ _ (by decide : Reg.x6 ∉ linkRegs), gpr_ce _ _ _ (by decide : Reg.x7 ∉ linkRegs),
    ha.x2, ha.x3, ha.x6, ha.x7, sa 0 (by decide), sa 1 (by decide), Lay.argv]
  rw [kp, kq, hc.n_bytes hL]
  exact hP.pq

theorem narrowP_widen (s : State) : (narrowP s).withRegions s.rd s.wr = s := by
  simp only [narrowP, State.withRegions_withRegions, State.withRegions_self]

theorem narrowP_covers {s : State} (h : chkPA.pre s) :
    Covers ((narrowP s).rd ++ (narrowP s).wr) (s.rd ++ s.wr) := by
  obtain ⟨hA, -, rd, -, -, -, -, -, -, -, prl, -⟩ := h
  have hpw : (lay s).pw ≤ (stackArg s 13).toNat := by
    rw [prl]
    simp only [Lay.pw, lay, Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords]
    omega
  refine Covers.of_sub fun r hr => ?_
  have self : ∀ r ∈ s.rd ++ s.wr, ∃ r' ∈ s.rd ++ s.wr, ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧
      off + r.len ≤ r'.len := fun r hr => ⟨r, hr, 0, (BitVec.add_zero _).symm, by omega⟩
  have m8 : ∀ r ∈ (rd0 s).take 8, ∃ r' ∈ s.rd ++ s.wr, ∃ off, r.base = r'.base + BitVec.ofNat 64 off ∧
      off + r.len ≤ r'.len := fun r hr => self r (by rw [rd]; exact List.mem_append_left _ (List.mem_append_left _ hr))
  have ma : (⟨stackArgAddr s 0, 112⟩ : Region) ∈ s.rd ++ s.wr := by rw [rd]; simp
  have mp : preR s ∈ s.rd ++ s.wr := by rw [rd]; simp
  simp only [narrowP, State.withRegions_rd, State.withRegions_wr, rd0, XP, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)) | hw
  iterate 8 exact m8 _ (by simp [rd0])
  · exact ⟨_, ma, 0, (BitVec.add_zero _).symm, by dsimp only; omega⟩
  · exact ⟨_, ma, 96, by simp only [stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat], by dsimp only; omega⟩
  · exact ⟨_, mp, 0, (BitVec.add_zero _).symm, by dsimp only; omega⟩
  · exact self _ (List.mem_append_right _ hw)

/-- The code, from the narrowed call. -/
theorem codeP_wp (v : CrtImpl) {s : State} (h : chkPA.pre s) :
    WP isa (codeWith v.calleeP v pcCopy) (narrowP s) fun s' => abiPreserved s s' ∧ chkA.post s s' :=
  codeWith_correct v.calleeP v pcCopy (s := narrowP s) (R₀ := rd0 s) (X := XP s) h.1 rfl
    (pcCopy_ok ((lay_ok h.1).withX _) (preIn (s := s) h))
    fun _ hc ha => keyProduct_call ((lay_ok h.1).withX _) hc ha (preIn (s := s) h)

theorem codeP_correct (v : CrtImpl) (s : State) (h : chkPA.pre s) :
    ∃ t s', Exec isa (codeWith v.calleeP v pcCopy) s t s' ∧ abiPreserved s s' ∧ chkPA.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := codeP_wp v h
  have hw := Exec.widen he (narrowP_covers h) (Covers.refl _)
  rw [narrowP_widen] at hw
  exact ⟨t, _, hw, ha, hp⟩

/-! ## Constant time -/

/-- Constant time from the runs of narrowed calls. -/
theorem ct_of_narrow {c : Prog isa} {pre : State → Prop} {pub : State → State → Prop} (n : State → State)
    (hn : ∀ s, pre s → (∃ t s', Exec isa c (n s) t s') ∧ Covers ((n s).rd ++ (n s).wr) (s.rd ++ s.wr) ∧
      Covers (n s).wr s.wr ∧ (n s).withRegions s.rd s.wr = s)
    (hct : ConstantTime isa (fun a => ∃ s, pre s ∧ a = n s)
      (fun a b => ∃ s₁ s₂, pre s₁ ∧ pre s₂ ∧ pub s₁ s₂ ∧ a = n s₁ ∧ b = n s₂) c) :
    ConstantTime isa pre pub c := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨⟨u₁, v₁, x₁⟩, c₁, w₁, r₁⟩ := hn s₁ h₁
  obtain ⟨⟨u₂, v₂, x₂⟩, c₂, w₂, r₂⟩ := hn s₂ h₂
  have y₁ := Exec.widen x₁ c₁ w₁
  have y₂ := Exec.widen x₂ c₂ w₂
  rw [r₁] at y₁
  rw [r₂] at y₂
  obtain ⟨rfl, -⟩ := Exec.det e₁ y₁
  obtain ⟨rfl, -⟩ := Exec.det e₂ y₂
  exact hct _ _ _ _ _ _ ⟨s₁, h₁, rfl⟩ ⟨s₂, h₂, rfl⟩ ⟨s₁, s₂, h₁, h₂, hp, rfl, rfl⟩ x₁ x₂

/-- Both runs' `pre` meet `PreIn`. -/
def GP (e : Env) : Prop := PreIn e.L e.m₁ ∧ PreIn e.L e.m₂

theorem two_addG {G : Env → Prop} {Φ : Lay → Mem → State → Prop} {Ψ : Lay → Mem → Prop}
    (hG : ∀ e, G e → Ψ e.L e.m₁ ∧ Ψ e.L e.m₂) {a b : State} (h : Two G Φ a b) :
    Two G (fun L m t => Φ L m t ∧ Ψ L m) a b := by
  obtain ⟨e, g, hL, a₁, a₂, pe, c₁, c₂, f₁, f₂⟩ := h
  exact ⟨e, g, hL, a₁, a₂, pe, c₁, c₂, ⟨f₁, (hG e g).1⟩, ⟨f₂, (hG e g).2⟩⟩

theorem pcHead_ct :
    RelCT isa (Two GP fun L m₀ t => (Slots L t.mem ∧ PcArgs L t) ∧ PreIn L m₀) (.block pcHead)
      (Two GP fun L m₀ t => Slots L t.mem ∧ t.gpr .x17 = L.B + BitVec.ofNat 64 oPre ∧ t.gpr .x16 = L.preA ∧
        t.gpr .x12 = BitVec.ofNat 64 L.pw ∧ PreIn L m₀) :=
  two_blk [] (fun _ _ => 0) (fun _ _ _ _ _ h => absurd h (by simp)) (by taint_decide)
    fun _ _ _ _ _ hL _ hc ⟨⟨hs, pa⟩, hP⟩ => WP.mono (pcHead_ok hL hP hc pa)
      fun _ ⟨hc', hm, a, b, c⟩ => ⟨hc', by rw [hm]; exact hs, a, b, c, hP⟩

/-- The registers the copy's addresses and count depend on. -/
def fixC (L : Lay) : Reg → BitVec 64
  | .x16 => L.preA | .x17 => L.B + BitVec.ofNat 64 oPre | .x12 => BitVec.ofNat 64 L.pw | _ => 0

theorem pcBody_ct :
    RelCT isa (Two GP fun L m₀ t => Slots L t.mem ∧ t.gpr .x17 = L.B + BitVec.ofNat 64 oPre ∧
        t.gpr .x16 = L.preA ∧ t.gpr .x12 = BitVec.ofNat 64 L.pw ∧ PreIn L m₀) pcBody
      (Two GP fun L m₀ t => Slots L t.mem ∧ PreW L m₀ t) :=
  two_blk [.x16, .x17, .x12] fixC (fun _ _ _ ⟨_, h17, h16, h12, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [fixC] <;> with_reducible assumption) (by taint_decide)
    fun _ _ _ _ _ hL _ hc ⟨hs, h17, h16, h12, hP⟩ => WP.mono (pcBody_ok hL hP hc hs h17 h16 h12)
      fun _ ⟨hc', hs', _, _, hw⟩ => ⟨hc', hs', by simp only [PreW, preVal, hP.pc]; exact hw⟩

theorem pcCopy_ct :
    RelCT isa (Two GP fun L _ t => Slots L t.mem ∧ PcArgs L t) pcCopy
      (Two GP fun L m₀ t => Slots L t.mem ∧ PreW L m₀ t) := by
  rw [pcCopy_eq]
  exact (pcHead_ct.seq pcBody_ct).mono (fun _ _ h => two_addG (Ψ := PreIn) (fun _ g => g) h) fun _ _ h => h

theorem codeP_constantTime (v : CrtImpl) :
    ConstantTime isa chkPA.pre chkPA.pub (codeWith v.calleeP v pcCopy) := by
  refine ct_of_narrow narrowP (fun s h => ⟨?_, narrowP_covers h, Covers.refl _, narrowP_widen s⟩) ?_
  · obtain ⟨t, s', he, -⟩ := codeP_wp v h
    exact ⟨t, s', he⟩
  refine codeWith_constantTime (G := GP) v.calleeP v pcCopy (H := PreIn) (fun _ g => g)
    (fun _ _ _ _ _ hL _ hc ha hP => keyProduct_call hL hc ha hP) pcCopy_ct ?_ ?_
  · rintro _ _ - - ⟨s₁, s₂, -, -, hp, rfl, rfl⟩
    exact hp.1.2.1
  · rintro _ _ - - ⟨s₁, s₂, h₁, h₂, hp, rfl, rfl⟩
    have e := lay_eq hp.1
    have eX : XP s₂ = XP s₁ := by
      simp only [XP, e, stackArgAddr, hp.1.2.1, hp.2.1]
    have eL : layW s₂ (XP s₂) = layW s₁ (XP s₁) := by simp only [layW, e, eX]
    have p₂ := preIn h₂
    rw [eL] at p₂
    exact ⟨narrowP s₁, narrowP s₂, rd0 s₁, rd0 s₂, XP s₁, h₁.1, h₂.1, rfl, by rw [← eX]; rfl, hp.1,
      ⟨preIn (s := s₁) h₁, p₂⟩, rfl, rfl⟩

/-! ## The function -/

/-- The name of `vg_rsa_private_checked_precomputed` calling `v`. -/
def privPName (v : CrtImpl) : String := "vg_rsa_private_checked_precomputed" ++ v.suffix

/-- Its code. -/
abbrev privPCode (v : CrtImpl) : Prog isa := codeP v.crtPName v.crtP v.pdName v.pd

theorem privPCode_eq (v : CrtImpl) : privPCode v = codeWith v.calleeP v pcCopy := rfl

theorem codeP_verified (v : CrtImpl) :
    Verified AArch64.target (privPCode v)
      (Proof.Rsa.privateCheckedPrecomputedContract AArch64.abi stackBytes) :=
  Verified.of_correct (fun s h => codeP_correct v s h) (codeP_constantTime v)
    private_checked_precomputed_implies

/-- Its frames, as `vg_rsa_private_checked`'s. -/
theorem privPCode_depth (v : CrtImpl) : (privPCode v).aarch64Depth = stackBytes / 16 := by
  simp only [privPCode, codeP, bodyP, checkWith, pcCopy, tail, seqs, List.cons_append, List.nil_append,
    Code.aarch64Depth, aarch64Depth_of_noFrames v.crtPNoFrames, aarch64Depth_of_noFrames v.pdNoFrames,
    VG.Impl.Bignum.AArch64.copyWords, VG.Impl.Bignum.AArch64.countLoop, cmpLoop, releaseLoop,
    Instr.frameUnits, frameBytes, stackBytes]
  decide

end VG.Proof.Rsa.AArch64

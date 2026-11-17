module

public import VerifiedGarbage.Proof.Dsa.Arm.Prime.Top5
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.Lost
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Dsa.Arm.Prime.Loads
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Rsa.Arm.PrivSetupCT
import VerifiedGarbage.Proof.Rsa.Arm.PrivAllocCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.Base
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
meta import VerifiedGarbage.TCB.Arm.Target

/-! ### `Dsa.Arm.Prime.Top6`, which only this module used -/

section

/-! # DSA's probable-prime test on ARMv7: a call's result (`prime_ok`) -/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

section
variable {bits : Nat} {s : State}

/-- A call's result. -/
theorem prime_ok (v : RoundImpl) (h : CIn bits s) :
    WP isa (Impl.Dsa.Arm.ProbablePrime.code v.name v.code) s fun t => abiPreserved s t ∧ CPost bits s t := by
  have hb := h.sized
  have spLo := h.spLo; have spHi := h.spHi
  unfold Impl.Dsa.Arm.ProbablePrime.code
  refine WP.allocLost (by decide) (by omega_using [spLo]) ?_
  rw [WP.seq_iff]
  refine WP.mono (pre_ok hb spLo spHi h.argsIn h.arg) fun t ⟨rest, fr, vals, r1, r2⟩ => ?_
  have o : PreOut bits s t := ⟨rest, fr, vals, r1, r2⟩
  have tspN : t.sp.toNat = s.sp.toNat - 32 := by
    rw [rest.sp]; exact sub_toNat' (by omega_using [spLo])
  refine WP.frameLost (by decide) (by simp only [List.length_cons, List.length_nil]; omega_using [spLo, tspN]) (by decide) ?_
  rw [WP.seq_iff]
  obtain ⟨tr, w, -, run', ⟨-, bk, r0, used⟩⟩ := body_wide v hb h o
  refine WP.mono (Q := fun x => x = w.withRegions s.rd (pcPushed t).wr) ⟨tr, _, run', rfl⟩ ?_
  rintro _ rfl
  have pre := bk.pre
  have wsp : w.sp = (mkP bits s).sp := bk.sp.trans pre.sp
  have spN : (mkP bits s).sp.toNat = s.sp.toNat - 88 := sub_toNat' (by omega_using [spLo])
  have sv := pc_push_callee_saved t (by omega_using [spLo, tspN])
  rw [show (t.sp - 56 : BitVec 32) = (mkP bits s).sp from pushed_sp o] at sv
  have saved : Spill.Saved w.mem (State.addr (mkP bits s).sp) t.gpr pcCalleeSaved := fun p hp => by
    have ho : FwOk p.2 := by revert hp; revert p; decide
    exact (bk.frame.readW (r := ⟨State.addr (mkP bits s).sp + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _)
      (pre.fwSep ho) (by decide)).trans (sv p hp)
  have fit : (w.withRegions s.rd (pcPushed t).wr).sp.toNat + 56 ≤ 2 ^ 32 := by
    show w.sp.toNat + 56 ≤ _; rw [wsp, spN]; omega_using []
  have read : InRegions ((w.withRegions s.rd (pcPushed t).wr).rd ++ (w.withRegions s.rd (pcPushed t).wr).wr)
      (State.addr (w.withRegions s.rd (pcPushed t).wr).sp) 56 := by
    refine ⟨⟨State.addr (mkP bits s).sp, 56⟩, List.mem_append_right _ ?_, ?_⟩
    · show _ ∈ ⟨State.addr (t.sp - BitVec.ofNat 32 56), 56⟩ :: t.wr
      rw [show t.sp - BitVec.ofNat 32 56 = (mkP bits s).sp from pushed_sp o]; exact List.mem_cons_self
    · rw [State.withRegions_sp, wsp]; exact Region.contains_self _ _
  refine WP.mono (pc_restore_ok _ t.gpr fit read (by rw [State.withRegions_sp, wsp]; exact saved)) ?_
  rintro t' ⟨restored, memT, restT⟩ m₁ u₁ h₁ m₂ u₂ h₂
  have rc := res_c pre
  have m' : t'.mem = w.mem := memT
  change Frame [⟨State.addr (t.sp - BitVec.ofNat 32 56), 56⟩] t'.mem m₁ at h₁
  rw [show t.sp - BitVec.ofNat 32 56 = (mkP bits s).sp from pushed_sp o, spP h] at h₁
  change Frame [⟨aA s, 32⟩] m₁ m₂ at h₂
  rw [aA_eq h] at h₂
  have lostF : Frame [cF s] t'.mem m₂ :=
    (h₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, cF_sub (by decide)⟩).trans
    (h₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, cF_sub (by decide)⟩)
  have keepsL : Proof.Dsa.ModPow.Keeps (State.addr (s.gpr .r0)) (s.gpr .r1).toNat [(keyOff, 8 * keyWords bits)]
      s.mem m₂ := by
    have k := keeps h o bk
    rw [← m'] at k
    intro i hi hr
    exact (lost_byte lostF (R := cW s) h.FW.symm (by change i < (s.gpr .r1).toNat * 8; omega_using [hi])).trans
      (k i hi hr)
  have usedL : Spec.Rsa.wordsAt m₂ (State.addr (stackArg s 0)) 1 = Spec.Rsa.wordsAt t'.mem (State.addr (stackArg s 0)) 1 :=
    Proof.Rsa.wordsAt_frame lostF (by decide) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.FU.symm
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_, keepsL, fun b rst hr => ?_⟩
  · have ne : r ≠ .r12 := by intro he; subst r; simp [preserved] at hr
    show (popped .r12 56 t').gpr r = _
    rw [popped_gpr ne]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (restored (.r4, 16) (by simp [pcCalleeSaved])).trans (rest.gpr _ (by decide))
    · exact (restored (.r5, 20) (by simp [pcCalleeSaved])).trans (rest.gpr _ (by decide))
    · exact (restored (.r6, 24) (by simp [pcCalleeSaved])).trans (rest.gpr _ (by decide))
    · exact (restored (.r7, 28) (by simp [pcCalleeSaved])).trans (rest.gpr _ (by decide))
    · exact (restored (.r8, 32) (by simp [pcCalleeSaved])).trans (rest.gpr _ (by decide))
    · exact (restored (.r9, 36) (by simp [pcCalleeSaved])).trans (rest.gpr _ (by decide))
    · exact (restored (.r10, 40) (by simp [pcCalleeSaved])).trans (rest.gpr _ (by decide))
    · exact (restored (.r11, 44) (by simp [pcCalleeSaved])).trans (rest.gpr _ (by decide))
    · exact (restored (.lr, 52) (by simp [pcCalleeSaved])).trans (rest.gpr _ (by decide))
  · show t'.sp + BitVec.ofNat 32 56 + BitVec.ofNat 32 32 = s.sp
    rw [restT.sp, State.withRegions_sp, wsp]
    show s.sp - BitVec.ofNat 32 88 + BitVec.ofNat 32 56 + BitVec.ofNat 32 32 = s.sp
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.sub_add_cancel]
  · show ((popped .r12 56 t').gpr .r0).toNat = _
    rw [popped_gpr (by decide), restT.gpr .r0 (by simp [pcCalleeSaved]), State.withRegions_gpr, r0]
    unfold statD; rw [rc]
  · show Spec.Rsa.wordsAt m₂ _ 1 = _
    rw [usedL, m']
    refine used.trans ?_
    unfold usedD; rw [rc, hr]; rfl

end

end VG.Proof.Dsa.Arm.Prime

end

end

/-! ### `Dsa.Arm.Prime.Top7`, which only this module used -/

section

/-! # DSA's probable-prime test on ARMv7: constant time (`prime_ct`)

Two calls with the same public parameters `mkP` leak the same: the
allocation and `pre`'s addresses are on the stack, the push's and the pop's
too, the body's are the stage's (`body_vp`), and the restore's on the stack.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

section
variable {bits : Nat}

/-- `pre`'s addresses are `r12`'s offsets, which it keeps. -/
theorem pre_ct :
    RelCT isa (fun s t => s.sp = t.sp) (.block Impl.Dsa.Arm.ProbablePrime.pre) (fun s t => s.sp = t.sp) := by
  unfold Impl.Dsa.Arm.ProbablePrime.pre Impl.Dsa.Arm.ProbablePrime.wordsOf Impl.Dsa.Arm.ProbablePrime.bitsOf
  simp only [List.cons_append, List.nil_append]
  apply VG.Proof.Rsa.Arm.setupBlock_ct
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro i hi s t h
    obtain ⟨h1, h2⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [addrs, h2]

theorem alloc_push {s : State} (h : 32 ≤ s.sp.toNat) : isa.push (.alloc 32) s = some (allocated 32 s) := by
  simp only [isa, push, show (0 : Nat) < 32 ∧ 32 < 4096 ∧ 32 % 8 = 0 ∧ encodable (BitVec.ofNat 32 32) = true from
    by decide, h, and_self, ite_true]
  rfl

/-- The states after `pre`, for two calls. -/
def AfterPre (bits : Nat) (a b : State) : Prop :=
  ∃ s t, (CIn bits s ∧ CIn bits t ∧ s.sp = t.sp ∧ mkP bits s = mkP bits t) ∧ PreOut bits s a ∧ PreOut bits t b

theorem pre_out {s u : State} {tr : List Leak} (h : CIn bits s)
    (e : Exec isa (.block Impl.Dsa.Arm.ProbablePrime.pre) (allocated 32 s) tr u) : PreOut bits s u := by
  obtain ⟨tr', u', e', rest, fr, vals, r1, r2⟩ := pre_ok h.sized h.spLo h.spHi h.argsIn h.arg
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact ⟨rest, fr, vals, r1, r2⟩

/-- The frame's body, for two calls. -/
theorem inner_ct (v : RoundImpl) :
    RelCT isa (fun a' b' => ∃ a b, AfterPre bits a b ∧
        isa.push (.push [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) a = some a' ∧
        isa.push (.push [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) b = some b')
      (.seq (Impl.Dsa.Arm.ProbablePrime.body v.name v.code) (.block VG.Impl.Bignum.Arm.PcFn.restore)) (fun _ _ => True) := by
  intro a' b' tr1 tr2 u w hp e1 e2
  obtain ⟨a, b, ⟨s, t, ⟨hs, ht, sp, hP⟩, o1, o2⟩, pa, pb⟩ := hp
  have f1 : 56 ≤ a.sp.toNat := by rw [o1.rest.sp]; show 56 ≤ (s.sp - BitVec.ofNat 32 32).toNat
                                  rw [sub_toNat' (by have := hs.spLo; omega_using [this])]; have := hs.spLo; omega_using [this]
  have f2 : 56 ≤ b.sp.toNat := by rw [o2.rest.sp]; show 56 ≤ (t.sp - BitVec.ofNat 32 32).toNat
                                  rw [sub_toNat' (by have := ht.spLo; omega_using [this])]; have := ht.spLo; omega_using [this]
  have ea : pcPushed a = a' := Option.some.inj ((push_pushed (by decide) (by simpa using f1)).symm.trans pa)
  have eb : pcPushed b = b' := Option.some.inj ((push_pushed (by decide) (by simpa using f2)).symm.trans pb)
  subst a'; subst b'
  cases e1 with
  | seq body1 rest1 =>
    cases e2 with
    | seq body2 rest2 =>
      obtain ⟨n1, w1, en1, run1, ⟨-, bk1, -⟩⟩ := body_wide v hs.sized hs o1
      obtain ⟨n2, w2, en2, run2, ⟨-, bk2, -⟩⟩ := body_wide v hs.sized ht o2
      obtain ⟨rfl, rfl⟩ := Exec.det body1 run1
      obtain ⟨rfl, rfl⟩ := Exec.det body2 run2
      have pre1 := in_c hs.sized hs o1
      have pre2 := in_c hs.sized ht o2
      have bx1 : Bk (mkP bits s) (sx bits s a) (sx bits s a) := ⟨pre1, rfl, rfl, rfl, Frame.refl _ _⟩
      have bx2 : Bk (mkP bits t) (sx bits t b) (sx bits t b) := ⟨pre2, rfl, rfl, rfl, Frame.refl _ _⟩
      have sp1 := bk1.sp.trans pre1.sp
      have sp2 := bk2.sp.trans pre2.sp
      rw [← hP] at pre2 bx2 sp2
      have trB := ((body_vp v (P := mkP bits s) (E := In (mkP bits s)) fun _ e => e).ct _ _ _ _ _ _
        ⟨_, _, ⟨pre1, bx1⟩, ⟨pre2, bx2⟩⟩ en1 en2).1
      have trR := ((stackLoads_ct pcCalleeSaved : RelCT isa (fun s t => s.sp = t.sp)
        (.block VG.Impl.Bignum.Arm.PcFn.restore) (fun s t => s.sp = t.sp)) _ _ _ _ _ _
        (by show w1.sp = w2.sp; rw [sp1, sp2]) rest1 rest2).1
      exact ⟨by rw [trB, trR], trivial⟩

/-- Two calls with the same public parameters. -/
theorem prime_ct (v : RoundImpl) :
    RelCT isa (fun s t => CIn bits s ∧ CIn bits t ∧ s.sp = t.sp ∧ mkP bits s = mkP bits t)
      (Impl.Dsa.Arm.ProbablePrime.code v.name v.code) (fun _ _ => True) := by
  unfold Impl.Dsa.Arm.ProbablePrime.code
  apply VG.Proof.Rsa.Arm.allocation_ct
  intro a b tr1 tr2 u w hp e1 e2
  obtain ⟨s, t, ⟨hs, ht, sp, hP⟩, pa, pb⟩ := hp
  have ea : allocated 32 s = a := Option.some.inj ((alloc_push (by have := hs.spLo; omega_using [this])).symm.trans pa)
  have eb : allocated 32 t = b := Option.some.inj ((alloc_push (by have := ht.spLo; omega_using [this])).symm.trans pb)
  subst a; subst b
  cases e1 with
  | seq pre1 fr1 =>
    cases e2 with
    | seq pre2 fr2 =>
      have trP := (pre_ct _ _ _ _ _ _ (show (allocated 32 s).sp = (allocated 32 t).sp by
        show s.sp - _ = t.sp - _; rw [sp]) pre1 pre2).1
      have o1 := pre_out hs pre1
      have o2 := pre_out ht pre2
      have trF := (RelCT.frame (P := AfterPre bits) (fun x y ⟨s, t, ⟨_, _, sp, _⟩, o1, o2⟩ => by
          rw [o1.rest.sp, o2.rest.sp]; show s.sp - _ = t.sp - _; rw [sp])
        (fun a' b' tr1 tr2 u w ⟨x, y, hxy, px, py⟩ e1 e2 => inner_ct v a' b' tr1 tr2 u w ⟨x, y, hxy, px, py⟩ e1 e2)
        _ _ _ _ u w ⟨s, t, ⟨hs, ht, sp, hP⟩, o1, o2⟩ fr1 fr2).1
      exact ⟨by rw [trP, trF], trivial⟩

end

end VG.Proof.Dsa.Arm.Prime

end

end


/-! # `vg_dsa_probable_prime` on ARMv7 is verified against the shared contract

For every size of `sizes` (`Bits`), the second stack argument, and any
implementation of the Miller–Rabin round it calls (`RoundImpl`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Prime
open VG VG.Arm
open VG.Impl.Dsa.Arm.ProbablePrime (code layout keyOff keyWords)
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem prime_contract_correct (v : RoundImpl) (s : State) (h : primeK.pre s) :
    ∃ tr t, Exec isa (code v.name v.code) s tr t ∧ abiPreserved s t ∧ primeK.post s t := by
  have hc := cin_of_pre s h
  obtain ⟨tr, t, run, preserved, r0, keeps, used⟩ := prime_ok v hc
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Proof.Dsa.ProbablePrime.sizedContract, Proof.Dsa.ProbablePrime.sizedSig, abi, argRegs, reduceClassify,
    Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  exact ⟨r0, keeps, used⟩

section
variable {bits : Nat}

/-- Calls with the same public arguments and leak have the same public parameters. -/
theorem mkP_eq {s t : State} (sp : s.sp = t.sp) (p0 : s.gpr .r0 = t.gpr .r0) (p2 : s.gpr .r2 = t.gpr .r2)
    (p3 : s.gpr .r3 = t.gpr .r3) (a0 : stackArg s 0 = stackArg t 0)
    (hc : Proof.Dsa.ProbablePrime.candidateAt (layout bits) s.mem (State.addr (s.gpr .r0)) =
      Proof.Dsa.ProbablePrime.candidateAt (layout bits) t.mem (State.addr (t.gpr .r0)))
    (hr : Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat =
      Spec.Rsa.bytesAt t.mem (State.addr (t.gpr .r2)) (t.gpr .r3).toNat) :
    mkP bits s = mkP bits t := by
  unfold mkP; rw [hc, hr, sp, p0, p2, p3, a0]

end

theorem prime_contract_ct (v : RoundImpl) : ConstantTime isa primeK.pre primeK.pub (code v.name v.code) := by
  intro s t tr1 tr2 u w hs ht hp e1 e2
  have is := cin_of_pre s hs
  have it := cin_of_pre t ht
  sig_pub [Proof.Dsa.ProbablePrime.sizedContract, Proof.Dsa.ProbablePrime.sizedSig, abi, argRegs, reduceClassify,
    Loc.val, State.addr] at hp
  obtain ⟨sp, leak, p0, -, p2, p3, a0, a1⟩ := hp
  rw [← a1] at leak
  obtain ⟨-, leak⟩ := List.cons.inj leak
  obtain ⟨hc, hl⟩ := List.cons.inj leak
  have hr := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hl
  rw [← a1] at it
  exact (prime_ct v s t tr1 tr2 u w ⟨is, it, sp, mkP_eq sp p0 p2 p3 a0 hc hr⟩ e1 e2).1

/-- A state satisfying the contract: the candidate of 160 ones at `0x1000`, in a working space of
6224 words, no `rand`, `used` at 0, and the stack at `0x80000`, its second word the size 160. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 6224 | .r2 => 0x20000 | .r3 => 0 | _ => 0
  sp := 0x80000
  n := false
  z := false
  c := false
  v := false
  mem a := if a.toNat < 0x10000 ∧ 0x1000 ≤ a.toNat then 0xFF else if a = 0x80004 then 160 else 0
  rd := [⟨0x20000, 0⟩, ⟨0x80000, 8⟩]
  wr := [⟨0x1000, 49792⟩, ⟨0, 8⟩]

theorem prime_contract_sat : ∃ s, primeK.pre s := by
  refine ⟨satState, ?_⟩
  have ha : stackArg satState 1 = 160 := by decide
  sig_pre [Proof.Dsa.ProbablePrime.sizedContract, Proof.Dsa.ProbablePrime.sizedSig, abi, argRegs, reduceClassify,
    Loc.val]
  rw [ha]
  sig_and_intros
  all_goals first
    | exact Region.disjoint_of_sep (by decide)
    | decide

theorem prime_verified (v : RoundImpl) : Verified target (code v.name v.code) primeK :=
  ⟨prime_contract_correct v, prime_contract_ct v, prime_contract_sat⟩

end VG.Proof.Dsa.Arm.Prime

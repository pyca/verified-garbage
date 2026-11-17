module

import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Proof.Bignum.Arm.PcPush
public import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Rsa.Arm.CvFail
import VerifiedGarbage.Proof.Framework.AddrArith
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Tactic.Finiteness.Attr
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Base
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Sig
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.RsaKeyGen.CandidateContract

/-! ### `RsaKeyGen.Arm.Cand.Top2`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.Arm.Cand.Top1`, which this module and modules that import it used -/

section

/-! # A candidate on ARMv7: the contract's arguments

`mkP s`: the public parameters of a call from `s` (the branches only when
`rand` holds the candidate's octets, as the leak determines them then);
`CIn s`: the contract's precondition, as the proof uses it (`cin_of_pre`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm

/-- The public parameters of a call: the frame, the pointers, the lengths,
`e` and the branches. -/
def mkP (s : State) : CP where
  sp := s.sp - BitVec.ofNat 32 56
  oP := s.gpr .r0
  uP := s.gpr .r2
  eP := s.gpr .r3
  pP := stackArg s 1
  nP := stackArg s 3
  B := stackArg s 5
  L := (s.gpr .r1).toNat
  el := (stackArg s 0).toNat
  pl := (stackArg s 2).toNat
  rl := (stackArg s 4).toNat
  SL := (stackArg s 6).toNat
  eB := Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat
  sch := if (s.gpr .r1).toNat ≤ (stackArg s 4).toNat then
      VG.Proof.RsaKeyGen.schedOf (s.gpr .r1).toNat
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat))
        (Spec.RsaKeyGen.otherPrime (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 1)) (stackArg s 2).toNat))
        (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 3)) (stackArg s 4).toNat)
    else ⟨false, false, false, none⟩

/-- The regions the body runs with: the frame, `out`, `used`, the working
space, and Montgomery multiplication's part of it. -/
def xRegs (s : State) : List Region := [(mkP s).rFr, (mkP s).rO, (mkP s).rU, (mkP s).rS, (mkP s).rM]

/-- The arguments' regions. -/
abbrev cO (s : State) : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
abbrev cU (s : State) : Region := ⟨State.addr (s.gpr .r2), 8⟩
abbrev cE (s : State) : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
abbrev cP (s : State) : Region := ⟨State.addr (stackArg s 1), (stackArg s 2).toNat⟩
abbrev cR (s : State) : Region := ⟨State.addr (stackArg s 3), (stackArg s 4).toNat⟩
abbrev cS (s : State) : Region := ⟨State.addr (stackArg s 5), (stackArg s 6).toNat * 8⟩
abbrev cA (s : State) : Region := ⟨stackArgAddr s 0, 28⟩
abbrev cF (s : State) : Region := ⟨State.addr s.sp - 112#64, 112⟩

/-- The contract's precondition. -/
structure CIn (s : State) : Prop where
  spLo : 112 ≤ s.sp.toNat
  spHi : s.sp.toNat + 28 ≤ 2 ^ 32
  rd : s.rd = [cE s, cP s, cR s, cA s]
  wr : s.wr = [cO s, cU s, cS s]
  oU : (cO s).Disjoint (cU s)
  oE : (cO s).Disjoint (cE s)
  oP : (cO s).Disjoint (cP s)
  oR : (cO s).Disjoint (cR s)
  oS : (cO s).Disjoint (cS s)
  oA : (cO s).Disjoint (cA s)
  uE : (cU s).Disjoint (cE s)
  uP : (cU s).Disjoint (cP s)
  uR : (cU s).Disjoint (cR s)
  uS : (cU s).Disjoint (cS s)
  uA : (cU s).Disjoint (cA s)
  eS : (cE s).Disjoint (cS s)
  pS : (cP s).Disjoint (cS s)
  rS : (cR s).Disjoint (cS s)
  SA : (cS s).Disjoint (cA s)
  Fo : (cF s).Disjoint (cO s)
  Fu : (cF s).Disjoint (cU s)
  Fe : (cF s).Disjoint (cE s)
  Fp : (cF s).Disjoint (cP s)
  Fr : (cF s).Disjoint (cR s)
  FS : (cF s).Disjoint (cS s)
  FA : (cF s).Disjoint (cA s)
  fo : (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32
  fu : (s.gpr .r2).toNat + 8 ≤ 2 ^ 32
  fe : (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32
  fp : (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 32
  fr : (stackArg s 3).toNat + (stackArg s 4).toNat ≤ 2 ^ 32
  fS : (stackArg s 5).toNat + (stackArg s 6).toNat * 8 ≤ 2 ^ 32
  valid : Spec.RsaKeyGen.primeLenValid (s.gpr .r1).toNat
  el1 : 1 ≤ (stackArg s 0).toNat
  el2 : (stackArg s 0).toNat ≤ 8
  plv : (stackArg s 2).toNat = 0 ∨ (stackArg s 2).toNat = (s.gpr .r1).toNat
  scr : Spec.Rsa.scratchWords (s.gpr .r1).toNat ≤ (stackArg s 6).toNat

theorem cin_of_pre (s : State) (h : (Proof.RsaKeyGen.candidateContract abi 112).pre s) : CIn s := by
  sig_pre [Proof.RsaKeyGen.candidateContract, Proof.RsaKeyGen.candidateSig, abi, argRegs, reduceClassify, Loc.val] at h
  obtain ⟨spLo, spHi, rd, wr, oU, oE, oP, oR, oS, oA, uE, uP, uR, uS, uA, eS, pS, rS, SA, Fo, Fu, Fe, Fp, Fr, FS, FA,
    fo, fu, fe, fp, fr, fS, valid, el1, el2, plv, scr⟩ := h
  exact ⟨spLo, spHi, rd, wr, oU, oE, oP, oR, oS, oA, uE, uP, uR, uS, uA, eS, pS, rS, SA, Fo, Fu, Fe, Fp, Fr, FS, FA,
    fo, fu, fe, fp, fr, fS, valid, el1, el2, plv, scr⟩

end VG.Proof.RsaKeyGen.Arm.Cand

end

end

/-! # A candidate on ARMv7: the body's start (`entry_ok`)

After the push, with the regions `xRegs`, the entry: the start `In` of the
body. The frame and the round's frame below it are the 112 bytes below the
caller's stack pointer (`cF`), at offsets of `cF`'s base (`fB`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm

/-- The state the entry runs from. -/
abbrev sx (s : State) : State := (pcPushed s).withRegions s.rd (xRegs s)

/-- `cF`'s base. -/
abbrev fB (s : State) : Addr := State.addr s.sp - 112#64

section
variable {s t : State}

theorem CIn.spP (h : CIn s) : State.addr (mkP s).sp = fB s + BitVec.ofNat 64 56 := by
  show State.addr (s.sp - BitVec.ofNat 32 56) = _
  rw [FrameStack.addr_sub' (by have := h.spLo; omega_using [this]), Offset.sub_ofNat_eq _ (show 56 ≤ 112 by decide)]

theorem spA_eq (s : State) : stackArgAddr s 0 = fB s + BitVec.ofNat 64 112 := by
  rw [show fB s = State.addr s.sp - BitVec.ofNat 64 112 from rfl, BitVec.sub_add_cancel]
  simp [stackArgAddr]

theorem CIn.argAddr (h : CIn s) {i : Nat} (hi : i < 7) :
    off (State.addr (mkP s).sp) (56 + 4 * i) = stackArgAddr s i := by
  have := h.spLo; have := h.spHi
  show off (State.addr (s.sp - BitVec.ofNat 32 56)) (56 + 4 * i) = _
  simp only [stackArgAddr, off]
  rw [FrameStack.addr_sub' (by omega_arith), addr_add (by omega_using [hi, this]), ← Offset.add_add, BitVec.sub_add_cancel]

theorem CIn.frSub (h : CIn s) : Region.Sub (mkP s).rFr (cF s) := by
  show Region.Sub ⟨State.addr (mkP s).sp, 56⟩ ⟨fB s, 112⟩
  rw [h.spP]; exact Offset.sub_base _ (by decide)

theorem CIn.rcSub (h : CIn s) : Region.Sub (mkP s).rC (cF s) := by
  have := h.spLo
  show Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 56 - BitVec.ofNat 32 56), 56⟩ ⟨fB s, 112⟩
  rw [BitVec.sub_sub, ← BitVec.ofNat_add, FrameStack.addr_sub' (by omega_using [this])]
  simpa using Offset.sub_base (fB s) (d := 0) (n := 56) (k := 112) (by decide)

theorem CIn.disjF (h : CIn s) {r : Region} (h1 : r.Disjoint (cF s)) (h2 : r.Disjoint (cA s)) :
    r.Disjoint (mkP s).rF := by
  show r.Disjoint ⟨State.addr (mkP s).sp, 84⟩
  rw [h.spP]
  intro x hx hc
  have e1 := (Offset.lt_iff x (fB s) (d := 56) (n := 84) (by decide)).mp (by simp only [Region.Contains] at hc; omega_using [hc])
  by_cases hlt : (x - fB s).toNat < 112
  · exact h1 x hx (by show (x - fB s).toNat + 1 ≤ 112; omega_using [hlt])
  · refine h2 x hx ?_
    simp only [Region.Contains]
    rw [spA_eq s]
    have := (Offset.lt_iff x (fB s) (d := 112) (n := 28) (by decide)).mpr ⟨by omega_using [hlt], by omega_using [e1]⟩
    omega_using [this]

/-- Memory after the push and the entry: changed only in the frames. -/
theorem CIn.tFrame (h : CIn s) (mem : t.mem = (pcPushed s).mem.writeW (off (State.addr (mkP s).sp) 48) (s.gpr .r0)) :
    Frame [cF s] s.mem t.mem := by
  have f := FrameStack.pushed_frameA (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr])
    (s := s) (by have := h.spLo; simp only [List.length_cons, List.length_nil]; omega_using [this])
  have e : FrameStack.belowA s.sp (4 * 14) = (mkP s).rFr := rfl
  rw [show [Reg.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr].length = 14 from rfl, e] at f
  have w : Frame [(mkP s).rFr] (pcPushed s).mem t.mem := by
    rw [mem]
    refine (Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_
    show (⟨State.addr (mkP s).sp, 56⟩ : Region).Contains (State.addr (mkP s).sp + BitVec.ofNat 64 48) (32 / 8)
    exact Offset.contains_base _ (by decide) (by decide)
  have sub : ∀ r ∈ [(mkP s).rFr], ∃ r' ∈ [cF s], Region.Sub r r' := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, h.frSub⟩
  exact (f.sub sub).trans (w.sub sub)

theorem CIn.bytesT (h : CIn s) (mem : t.mem = (pcPushed s).mem.writeW (off (State.addr (mkP s).sp) 48) (s.gpr .r0))
    {R : Region} (hR : (cF s).Disjoint R) (hl : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt t.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len :=
  VG.Proof.Rsa.Arm.CrtValues.bytes_frame (h.tFrame mem) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hR.symm) hl

end

end VG.Proof.RsaKeyGen.Arm.Cand

end

end

/-! # A candidate on ARMv7: the entry (`entry_ok`, `in_c`)

The entry moves `out` to frame word 12; then the body starts (`In`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.RsaKeyGen (ite_t ite_f)

section
variable {s t : State}

theorem CIn.argSub (h : CIn s) {i : Nat} (hi : i < 7) : Region.Sub ⟨stackArgAddr s i, 4⟩ (cA s) := by
  have := h.spHi
  have e : stackArgAddr s i = stackArgAddr s 0 + BitVec.ofNat 64 (4 * i) := by
    simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]; exact addr_add (by omega_using [hi, this])
  rw [e]; exact Offset.sub_base _ (by omega_using [hi])

/-- The body's start, after the push and the entry. -/
theorem in_c (h : CIn s) (sp : t.sp = (mkP s).sp) (rd : t.rd = s.rd) (wr : t.wr = xRegs s)
    (mem : t.mem = (pcPushed s).mem.writeW (off (State.addr (mkP s).sp) 48) (s.gpr .r0)) : In (mkP s) t := by
  have spLo := h.spLo; have spHi := h.spHi
  have spN : (mkP s).sp.toNat = s.sp.toNat - 56 := FrameStack.sub_toNat' (by omega_using [spLo])
  have hk := h.valid
  simp only [Spec.RsaKeyGen.primeLenValid] at hk
  have rdm : ∀ r ∈ [cE s, cP s, cR s, cA s], r ∈ t.rd ++ t.wr := fun r hr =>
    List.mem_append_left _ (by rw [rd, h.rd]; exact hr)
  have fr := h.tFrame mem
  have fwArg : ∀ i < 7, fw t.mem (mkP s) (56 + 4 * i) = stackArg s i := fun i hi => by
    simp only [fw]
    rw [h.argAddr hi]
    refine fr.readW (r := ⟨stackArgAddr s i, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact h.FA.symm.sub_left (h.argSub hi)
  have w48 : Frame [⟨off (State.addr (mkP s).sp) 48, 4⟩] (pcPushed s).mem t.mem := by
    rw [mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have fwSaved : ∀ p ∈ [(Reg.r1, 4), (Reg.r2, 8), (Reg.r3, 12)], fw t.mem (mkP s) p.2 = s.gpr p.1 := fun p hp => by
    have hs := pc_push_saved s (by omega_using [spLo]) p (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> simp [pcAllSaved])
    rw [← hs]
    refine w48.readW (r := ⟨off (State.addr (mkP s).sp) p.2, 4⟩) (Region.contains_self _ _) (fun r hr => ?_)
      (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    have : p.2 + 4 ≤ 48 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl <;> decide
    exact Offset.disjoint _ (.inl this) (by omega_using [this]) (by decide)
  have bE := h.bytesT mem (R := cE s) h.Fe (by have := h.fe; show (stackArg s 0).toNat ≤ _; omega_using [])
  have bP := h.bytesT mem (R := cP s) h.Fp (by have := h.fp; show (stackArg s 2).toNat ≤ _; omega_using [])
  have bR := h.bytesT mem (R := cR s) h.Fr (by have := h.fr; show (stackArg s 4).toNat ≤ _; omega_using [])
  have a0 := h.argAddr (i := 0) (by decide)
  simp only [Nat.mul_zero, Nat.add_zero] at a0
  refine ⟨sp, by omega_using [spLo, spN], by omega_using [spHi, spN], wr, ⟨cE s, rdm _ (by simp), Region.contains_self _ _⟩,
    ⟨cP s, rdm _ (by simp), Region.contains_self _ _⟩, ⟨cR s, rdm _ (by simp), Region.contains_self _ _⟩,
    ⟨cA s, rdm _ (by simp), by rw [a0]; exact Region.contains_self _ _⟩, hk.1, hk.2.1, hk.2.2, h.el1, h.el2, h.plv,
    h.scr, h.fo, h.fu, h.fe, h.fp, h.fr, BitVec.isLt _, h.fS,
    h.oS.symm, h.uS.symm, h.eS.symm, h.pS.symm, h.rS.symm, h.disjF h.FS.symm h.SA, h.FS.symm.sub_right h.rcSub,
    h.oU, h.oE, h.oP, h.oR, h.disjF h.Fo.symm h.oA, h.Fo.symm.sub_right h.rcSub,
    h.uE, h.uP, h.uR, h.disjF h.Fu.symm h.uA, h.Fu.symm.sub_right h.rcSub,
    h.Fe.symm.sub_right h.frSub, h.Fe.symm.sub_right h.rcSub, h.Fp.symm.sub_right h.frSub,
    h.Fp.symm.sub_right h.rcSub, h.Fr.symm.sub_right h.frSub, h.Fr.symm.sub_right h.rcSub,
    ?_, ?_, fwSaved (.r2, 8) (by simp), fwSaved (.r3, 12) (by simp), ?_, fwArg 1 (by decide), ?_,
    fwArg 3 (by decide), ?_, fwArg 5 (by decide), ?_, bE, fun hL => ?_⟩
  · show t.mem.readW (off (State.addr (mkP s).sp) 48) 32 = s.gpr .r0
    rw [mem]; exact Mem.readW_writeW_self32 _ _ _
  · rw [show fw t.mem (mkP s) foL = s.gpr .r1 from fwSaved (.r1, 4) (by simp)]; simp [mkP]
  · show fw _ _ (56 + 4 * 0) = _; rw [fwArg 0 (by decide)]; simp [mkP]
  · show fw _ _ (56 + 4 * 2) = _; rw [fwArg 2 (by decide)]; simp [mkP]
  · show fw _ _ (56 + 4 * 4) = _; rw [fwArg 4 (by decide)]; simp [mkP]
  · show fw _ _ (56 + 4 * 6) = _; rw [fwArg 6 (by decide)]; simp [mkP]
  · show VG.Proof.RsaKeyGen.schedOf (s.gpr .r1).toNat (Spec.Rsa.os2ip (mkP s).eB)
      (Spec.RsaKeyGen.otherPrime (Spec.Rsa.bytesAt t.mem (cP s).base (cP s).len))
      (Spec.Rsa.bytesAt t.mem (cR s).base (cR s).len) = (mkP s).sch
    rw [bP, bR]
    exact (ite_t hL _ _).symm

/-- The entry: `out` to frame word 12, and the body's start. -/
theorem entry_ok (h : CIn s) :
    WP isa (.block entry) (sx s) fun t => In (mkP s) t ∧ t.sp = (mkP s).sp ∧ t.rd = s.rd ∧ t.wr = xRegs s ∧
      t.mem = (pcPushed s).mem.writeW (off (State.addr (mkP s).sp) 48) (s.gpr .r0) := by
  have spLo := h.spLo; have spHi := h.spHi
  have spN : (mkP s).sp.toNat = s.sp.toNat - 56 := FrameStack.sub_toNat' (by omega_using [spLo])
  unfold entry
  refine wp_stackAddr (r := .r12) (d := 0) (by decide) fun u1 h1 => ?_
  refine wp_str (a := off (State.addr (mkP s).sp) 48) (by decide) ?_ ⟨(mkP s).rFr, by rw [h1.wr]; simp [xRegs],
    Offset.contains_base _ (by decide) (by decide)⟩ fun t m => WP.block_nil ?_
  · rw [h1.gpr, BitVec.add_zero]
    exact addr_add (by show (mkP s).sp.toNat + 48 < 2 ^ 32; omega_using [spN])
  · have e0 : u1.gpr .r0 = s.gpr .r0 := by rw [h1.other _ (by decide)]; rfl
    have mt : t.mem = (pcPushed s).mem.writeW (off (State.addr (mkP s).sp) 48) (s.gpr .r0) := by
      rw [m.mem, h1.mem, e0]; rfl
    have st : t.sp = (mkP s).sp := by rw [m.sp, h1.sp]; rfl
    have rt : t.rd = s.rd := by rw [m.rd, h1.rd]; rfl
    have wt : t.wr = xRegs s := by rw [m.wr, h1.wr]; rfl
    exact ⟨in_c h st rt wt mt, st, rt, wt, mt⟩

end

end VG.Proof.RsaKeyGen.Arm.Cand

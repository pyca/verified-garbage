module

public import VerifiedGarbage.Impl.Rsa.Arm.CrtValues
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.Arm.KeyWs
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Sig
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Push
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-! # `vg_rsa_crt_values` on ARMv7: the arguments

`CvPre s`: what the contract says of the arguments in the initial state `s`
(`cv_pre`), in the names used here: the working space `cvB s` of `cvZ s`
bytes, the modulus' length `cvK s` and `cvW s = ⌈cvK s / 4⌉`.
-/

@[expose] public section

namespace VG.Proof.Rsa.Arm.CrtValues
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.CrtValues
open VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm

abbrev reg (a : BitVec 32) (n : Nat) : Region := ⟨State.addr a, n⟩

abbrev cvB (s : State) : BitVec 32 := stackArg s 10
abbrev cvZ (s : State) : Nat := (stackArg s 11).toNat * 8
abbrev cvK (s : State) : Nat := (stackArg s 3).toNat
abbrev cvW (s : State) : Nat := (cvK s + 3) / 4
abbrev cvPl (s : State) : Nat := (stackArg s 5).toNat
abbrev cvQl (s : State) : Nat := (stackArg s 7).toNat
abbrev cvDl (s : State) : Nat := (stackArg s 9).toNat

/-- The regions. -/
abbrev rDp (s : State) : Region := reg (s.gpr .r0) (s.gpr .r1).toNat
abbrev rDq (s : State) : Region := reg (s.gpr .r2) (s.gpr .r3).toNat
abbrev rQi (s : State) : Region := reg (stackArg s 0) (stackArg s 1).toNat
abbrev rN (s : State) : Region := reg (stackArg s 2) (stackArg s 3).toNat
abbrev rP (s : State) : Region := reg (stackArg s 4) (stackArg s 5).toNat
abbrev rQ (s : State) : Region := reg (stackArg s 6) (stackArg s 7).toNat
abbrev rD (s : State) : Region := reg (stackArg s 8) (stackArg s 9).toNat
abbrev rS (s : State) : Region := reg (stackArg s 10) ((stackArg s 11).toNat * 8)
abbrev rA (s : State) : Region := ⟨stackArgAddr s 0, 48⟩

structure CvPre (s : State) : Prop where
  sp48 : s.sp.toNat + 48 ≤ 2 ^ 32
  rd : s.rd = [rN s, rP s, rQ s, rD s, rA s]
  wr : s.wr = [rDp s, rDq s, rQi s, rS s]
  dpDq : (rDp s).Disjoint (rDq s)
  dpQi : (rDp s).Disjoint (rQi s)
  dpN : (rDp s).Disjoint (rN s)
  dpP : (rDp s).Disjoint (rP s)
  dpQ : (rDp s).Disjoint (rQ s)
  dpD : (rDp s).Disjoint (rD s)
  dpS : (rDp s).Disjoint (rS s)
  dpA : (rDp s).Disjoint (rA s)
  dqQi : (rDq s).Disjoint (rQi s)
  dqN : (rDq s).Disjoint (rN s)
  dqP : (rDq s).Disjoint (rP s)
  dqQ : (rDq s).Disjoint (rQ s)
  dqD : (rDq s).Disjoint (rD s)
  dqS : (rDq s).Disjoint (rS s)
  dqA : (rDq s).Disjoint (rA s)
  qiN : (rQi s).Disjoint (rN s)
  qiP : (rQi s).Disjoint (rP s)
  qiQ : (rQi s).Disjoint (rQ s)
  qiD : (rQi s).Disjoint (rD s)
  qiS : (rQi s).Disjoint (rS s)
  qiA : (rQi s).Disjoint (rA s)
  nS : (rN s).Disjoint (rS s)
  pS : (rP s).Disjoint (rS s)
  qS : (rQ s).Disjoint (rS s)
  dS : (rD s).Disjoint (rS s)
  sA : (rS s).Disjoint (rA s)
  fDp : (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32
  fDq : (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32
  fQi : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32
  fN : (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 32
  fP : (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 32
  fQ : (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 32
  fD : (stackArg s 8).toNat + (stackArg s 9).toNat ≤ 2 ^ 32
  fS : (stackArg s 10).toNat + (stackArg s 11).toNat * 8 ≤ 2 ^ 32
  valid : Spec.Rsa.lenValid (cvK s)
  pl1 : 1 ≤ cvPl s
  pl2 : cvPl s < cvK s
  ql1 : 1 ≤ cvQl s
  ql2 : cvQl s < cvK s
  dpLen : (s.gpr .r1).toNat = cvPl s
  qiLen : (stackArg s 1).toNat = cvPl s
  dqLen : (s.gpr .r3).toNat = cvQl s
  dl1 : 1 ≤ cvDl s
  dl2 : cvDl s ≤ cvK s
  scr : Spec.Rsa.scratchWords (cvK s) ≤ (stackArg s 11).toNat

theorem cv_pre (s : State) (h : (Spec.Rsa.crtValuesContract abi 0).pre s) : CvPre s := by
  sig_pre [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at h
  obtain ⟨sp48, rd, wr, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
    a20, a21, a22, a23, a24, a25, a26, f1, f2, f3, f4, f5, f6, f7, f8, v, l1, l2, l3, l4, l5, l6, l7, l8, l9,
    l10⟩ := h
  exact ⟨sp48, rd, wr, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
    a20, a21, a22, a23, a24, a25, a26, f1, f2, f3, f4, f5, f6, f7, f8, v, l1, l2, l3, l4, l5, l6, l7, l8, l9,
    l10⟩

theorem CvPre.kb {s : State} (h : CvPre s) : 64 ≤ cvK s ∧ cvK s ≤ 1024 := h.valid

theorem CvPre.w16 {s : State} (h : CvPre s) : 16 ≤ cvW s ∧ cvW s ≤ 256 := by
  have := h.valid; simp only [Spec.Rsa.lenValid] at this
  have e : cvW s = (cvK s + 3) / 4 := rfl
  omega

/-- The working space is large enough for the 25 arrays. -/
theorem CvPre.fits {s : State} (h : CvPre s) : arr (cvW s) nArr ≤ cvZ s := by
  have := h.valid; have := h.scr
  simp only [Spec.Rsa.lenValid, Spec.Rsa.scratchWords] at *
  simp only [arr, S, hdr, nArr, cvZ, cvW]
  omega

/-! ## Loads of stack arguments -/

/-- `ldr t, [sp, #4i]` of a stack argument. -/
theorem wp_ldrSp {s : State} (hrd : rA s ∈ s.rd) (sp48 : s.sp.toNat + 48 ≤ 2 ^ 32) {i : Nat} (hi : i < 12)
    {t : Reg} {rest : List Instr} {Q : State → Prop} (k : ∀ s', Upd s s' t (stackArg s i) → WP isa (.block rest) s' Q) :
    WP isa (.block (.ldrSp t (4 * i) :: rest)) s Q := by
  refine WP.cons (s' := s.setReg t (stackArg s i)) ?_ (k _ (Upd.setReg _ _ _))
  have hin : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 (4 * i))) 4 := by
    refine ⟨rA s, List.mem_append_left _ hrd, ?_⟩
    simp only [Region.Contains, stackArgAddr]
    rw [addr_add (by omega), addr_add (by omega), Nat.mul_zero, BitVec.add_zero,
      Offset.add_sub_cancel_left, BitVec.toNat_ofNat]
    omega
  simp only [exec, show 4 * i < 4096 by omega, ↓reduceIte, State.load32, hin, Option.map_some]
  rfl

end VG.Proof.Rsa.Arm.CrtValues

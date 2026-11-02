module
-- separate module: the ABI, the failure path and the timing base build in parallel with the stages' proofs, which `Timing` also waits for

public import VerifiedGarbage.Proof.Bignum.X86.PublicArgumentTiming
public import VerifiedGarbage.Proof.Rsa.X86.Rd.Inputs
public import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
public import VerifiedGarbage.Proof.Mont.X86.OutsZ
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.TCB.X86.Isa
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
public import Init.Data.List.Basic
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw
public import VerifiedGarbage.TCB.X86.State
public import Init.Prelude
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Impl.Bignum.X86.PublicFn
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Bignum.X86.PublicSave
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Proof.Rsa.X86.Rd.Frame
public import VerifiedGarbage.Proof.Rsa.BoolNat
public import VerifiedGarbage.Proof.Rsa.Sub32
public import Init.Data.Fin.Basic
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Rsa.X86.CvClear
import VerifiedGarbage.Proof.Rsa.X86.InvParts
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Rsa.X86.CvInputs
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
import VerifiedGarbage.Proof.Bignum.X86.ModulusCheck
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
public import VerifiedGarbage.Impl.Bignum.X86.ModulusCheck
import VerifiedGarbage.Proof.Rsa.MontMulContract
import VerifiedGarbage.Proof.Mont.X86.Sse2.AtVerified
public import VerifiedGarbage.Proof.Rsa.X86.Rd.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeMul
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
public import Mathlib.Algebra.Group.Nat.Defs

/-!
# `vg_rsa_recover_primes_det` on i686: the calling convention, the failure path and the timing base

Two runs' public arguments; the ABI of the function and its frame; zeros
written out on a refused key, and its timing; the entry's and the check of
the modulus' timing; the timing base the stages build on.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86 VG.Proof.Dsa.X86

structure Pair (g : CallGeometry) (s t : State) : Prop where
  left : Inputs g s
  right : Inputs g t
  sp : s.gpr .esp = t.gpr .esp

theorem Pair.agree {g : CallGeometry} {s t : State} (h : Pair g s t) :
    VG.X86.Taint.Agree argumentTaint s t := by
  apply agree_regs (rs := [.edi, .esp])
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact BitVec.eq_of_toNat_eq (h.left.ws.workspace.edi_toNat.trans h.right.ws.workspace.edi_toNat.symm)
  · exact h.sp

theorem Pair.workspace {g : CallGeometry} {s t : State} (h : Pair g s t) :
    VG.X86.Taint.Agree (VG.Proof.Mont.X86.Dynamic.workspaceTaint false) s t := by
  apply agree_regs
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact h.agree.rf.1 _ (by decide)

theorem Pair.after {g : CallGeometry} {s t u v : State} {regs : List Reg} (h : Pair g s t)
    (hu : Inputs g u) (hv : Inputs g v) (ku : Keeps regs s u) (kv : Keeps regs t v)
    (sp : .esp ∉ regs) : Pair g u v :=
  ⟨hu, hv, (ku.1 _ sp).trans (h.sp.trans (kv.1 _ sp).symm)⟩

theorem Pair.keepMem {g : CallGeometry} {s t u v : State} {regs : List Reg} (h : Pair g s t)
    (ks : Keeps regs s u) (kt : Keeps regs t v) (di : .edi ∉ regs) (sp : .esp ∉ regs)
    (ms : u.mem = s.mem) (mt : v.mem = t.mem) : Pair g u v :=
  h.after (h.left.after ks di sp (by rw [ms]; exact Frame.refl _ _))
    (h.right.after kt di sp (by rw [mt]; exact Frame.refl _ _)) ks kt sp

end VG.Proof.Rsa.X86.Recover

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86

def caller (s : State) : CallGeometry :=
  ⟨⟨argumentPointer s 10, (arg s 11).toNat * 8, Spec.Rsa.modulusWords (arg s 5).toNat, s.gpr .esp, arg s, s.wr⟩⟩

/-- What the call writes but the stack below `esp`: the working space and the outputs. -/
abbrev bodyRegions (s : State) : List Region :=
  [⟨(caller s).B, (caller s).Z⟩, (caller s).buffer 0, (caller s).buffer 2]

/-- The 40 bytes below `esp` the calls' frames use, as the contract states them. -/
abbrev lowR (s : State) : Region := ⟨(s.gpr .esp).setWidth 64 - 96#64, 96⟩

structure ABI (s : State) : Prop where
  stackLow : 96 ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 52 ≤ 2 ^ 32
  rd : s.rd = [(caller s).buffer 4, (caller s).buffer 6, (caller s).buffer 8]
  wr : s.wr = [(caller s).buffer 0, (caller s).buffer 2,
    ⟨(caller s).B, (caller s).Z⟩, ⟨argAddr s 0, 48⟩]
  scratchBound : (arg s 10).toNat + (caller s).Z ≤ 2 ^ 32
  belowScratch : (lowR s).Disjoint ⟨(caller s).B, (caller s).Z⟩
  belowIn : ∀ r ∈ s.rd, r.Disjoint (lowR s)
  belowOut : ∀ r ∈ [(caller s).buffer 0, (caller s).buffer 2], r.Disjoint (lowR s)
  argsApart : ∀ r ∈ bodyRegions s, (⟨argAddr s 0, 48⟩ : Region).Disjoint r
  retApart : ∀ r ∈ bodyRegions s, (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r
  inApart : ∀ r ∈ s.rd, ∀ w ∈ bodyRegions s, r.Disjoint w
  outScratch : ∀ r ∈ [(caller s).buffer 0, (caller s).buffer 2],
    r.Disjoint ⟨(caller s).B, (caller s).Z⟩
  outSeparate : ((caller s).buffer 0).Disjoint ((caller s).buffer 2)
  bounds : ∀ i ∈ [0, 2, 4, 6, 8], (arg s i).toNat + (arg s (i + 1)).toNat ≤ 2 ^ 32
  lengths : Spec.Rsa.lenValid (arg s 5).toNat
  pLen : (arg s 1).toNat = (arg s 5).toNat
  qLen : (arg s 3).toNat = (arg s 5).toNat
  ePositive : 1 ≤ (arg s 7).toNat
  eBound : (arg s 7).toNat ≤ (arg s 5).toNat
  dPositive : 1 ≤ (arg s 9).toNat
  dBound : (arg s 9).toNat ≤ (arg s 5).toNat
  scratchLength : Spec.Rsa.scratchWords (arg s 5).toNat ≤ (arg s 11).toNat

/-- The stack below `esp`, in the contract's form. -/
theorem below_eq {sp : BitVec 32} (h : 96 ≤ sp.toNat) :
    below sp 96 = ⟨sp.setWidth 64 - 96#64, 96⟩ := by
  simp only [below]
  rw [VG.X86.Taint.sub_setWidth h]

theorem ABI.room {s : State} (a : ABI s) : CallRoom (s.gpr .esp) (caller s).B (caller s).Z :=
  ⟨a.stackLow, by rw [below_eq a.stackLow]; exact a.belowScratch⟩

theorem ABI.argsApartW {s : State} (a : ABI s) :
    ∀ r ∈ (caller s).writes, (⟨argAddr s 0, 48⟩ : Region).Disjoint r := by
  intro r hr
  simp only [CallGeometry.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact a.argsApart _ (by simp)
  · exact a.argsApart _ (by simp)
  · exact a.argsApart _ (by simp)
  · have z : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 :=
      addr_eq (by have := a.stackBound; omega)
    rw [show (caller s).sp = s.gpr .esp from rfl, below_eq a.stackLow, z]
    exact Offset.disjoint_below _ (by decide)

theorem ABI.retApartW {s : State} (a : ABI s) :
    ∀ r ∈ (caller s).writes, (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r := by
  intro r hr
  simp only [CallGeometry.writes, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact a.retApart _ (by simp)
  · exact a.retApart _ (by simp)
  · exact a.retApart _ (by simp)
  · rw [show (caller s).sp = s.gpr .esp from rfl, below_eq a.stackLow]
    exact Offset.base_disjoint_below _ (by decide)

theorem ABI.inApartW {s : State} (a : ABI s) : ∀ r ∈ s.rd, ∀ w ∈ (caller s).writes, r.Disjoint w := by
  intro r hr w hw
  simp only [CallGeometry.writes, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact a.inApart _ hr _ (by simp)
  · exact a.inApart _ hr _ (by simp)
  · exact a.inApart _ hr _ (by simp)
  · rw [show (caller s).sp = s.gpr .esp from rfl, below_eq a.stackLow]
    exact a.belowIn _ hr

end VG.Proof.Rsa.X86.Recover

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Recover

theorem ABI.space {s : State} (a : ABI s) : arr (2 * (caller s).n + 2) nArr ≤ (caller s).Z := by
  have h := a.scratchLength
  have lo := a.lengths.1
  simp only [Spec.Rsa.scratchWords] at h
  simp only [caller, Spec.Rsa.modulusWords, arr, S, VG.Impl.Rsa.X86.Keys.hdr, nArr]
  omega

theorem ABI.used {s : State} (a : ABI s) : 160 ≤ (caller s).Z :=
  Nat.le_trans (Nat.le_add_right _ _) a.space

theorem ABI.width {s : State} (a : ABI s) : 8 ≤ (caller s).n ∧ (caller s).n ≤ 128 ∧
    (arg s 5).toNat ≤ 8 * (caller s).n := by
  have lo := a.lengths.1; have hi := a.lengths.2
  simp only [caller, Spec.Rsa.modulusWords]
  omega

theorem ABI.stackArgument {s : State} (a : ABI s) {i : Nat} (hi : i < 12) :
    StackArgument s (caller s).B (caller s).Z i := by
  apply stackArgument_of (count := 12) (by have := a.stackBound; omega) hi
  · rw [a.rd, a.wr]; simp
  · exact a.argsApart _ (by simp)

theorem ABI.stack {s : State} (a : ABI s) : StkOk (s.gpr .esp) (caller s).B (caller s).Z := by
  apply VG.Proof.Weierstrass.X86.stkOk_of (by decide : 20 ≤ 96) a.stackLow
  · have h := a.scratchBound
    simpa only [caller, argumentPointer, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_trans (arg s 10).isLt (by decide : 2 ^ 32 < 2 ^ 64))] using h
  · have := a.used; omega
  · exact a.belowScratch

theorem ABI.stackApart {s : State} (a : ABI s) {i : Nat} (hi : i < 12)
    {r : Region} (hr : r ∈ (caller s).writes) : (⟨stackAddress s i, 4⟩ : Region).Disjoint r := by
  apply (a.argsApartW r hr).sub_left
  have p : stackAddress s i = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) :=
    addr_eq (by have := a.stackBound; omega)
  have z : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 :=
    addr_eq (by have := a.stackBound; omega)
  rw [p, z]
  exact Offset.sub _ (by omega) (by omega)

theorem ABI.lengths_ok {s : State} (a : ABI s) : Lengths (caller s) :=
  ⟨a.lengths.1, a.lengths.2, rfl,
    BitVec.eq_of_toNat_eq (by
      simp only [caller, argumentPointer, BitVec.toNat_ofNat, BitVec.toNat_setWidth]
      have := (arg s 10).isLt
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]), rfl,
    BitVec.eq_of_toNat_eq a.pLen, BitVec.eq_of_toNat_eq a.qLen⟩

end VG.Proof.Rsa.X86.Recover

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86

theorem ABI.inputLength {s : State} (a : ABI s) (i : Fin 3) :
    0 < ((caller s).buffer (4 + 2 * i.val)).len ∧
      ((caller s).buffer (4 + 2 * i.val)).len ≤ 8 * (caller s).n := by
  have w := a.width.2.2
  change (arg s 5).toNat ≤ 8 * Spec.Rsa.modulusWords (arg s 5).toNat at w
  have lo := a.lengths.1
  have ep := a.ePositive; have dp := a.dPositive
  have eb := a.eBound; have db := a.dBound
  have cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  rcases cases with e | e | e <;> rw [e]
  · change 0 < (arg s 5).toNat ∧ (arg s 5).toNat ≤ 8 * Spec.Rsa.modulusWords (arg s 5).toNat
    omega
  · change 0 < (arg s 7).toNat ∧ (arg s 7).toNat ≤ 8 * Spec.Rsa.modulusWords (arg s 5).toNat
    omega
  · change 0 < (arg s 9).toNat ∧ (arg s 9).toNat ≤ 8 * Spec.Rsa.modulusWords (arg s 5).toNat
    omega

theorem ABI.outputLength {s : State} (a : ABI s) (i : Fin 2) :
    0 < ((caller s).buffer (2 * i.val)).len ∧
      ((caller s).buffer (2 * i.val)).len ≤ 8 * (caller s).n := by
  have w := a.width.2.2
  change (arg s 5).toNat ≤ 8 * Spec.Rsa.modulusWords (arg s 5).toNat at w
  have lo := a.lengths.1
  have p := a.pLen; have q := a.qLen
  have cases : i.val = 0 ∨ i.val = 1 := by omega
  rcases cases with e | e <;> rw [e]
  · change 0 < (arg s 1).toNat ∧ (arg s 1).toNat ≤ 8 * Spec.Rsa.modulusWords (arg s 5).toNat
    omega
  · change 0 < (arg s 3).toNat ∧ (arg s 3).toNat ≤ 8 * Spec.Rsa.modulusWords (arg s 5).toNat
    omega

theorem ABI.inputMember {s : State} (a : ABI s) (i : Fin 3) :
    (caller s).buffer (4 + 2 * i.val) ∈ s.rd := by
  rw [a.rd]
  have cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  rcases cases with e | e | e <;> simp [e]

theorem ABI.outputMember {s : State} (i : Fin 2) :
    (caller s).buffer (2 * i.val) ∈ [(caller s).buffer 0, (caller s).buffer 2] := by
  have cases : i.val = 0 ∨ i.val = 1 := by omega
  rcases cases with e | e <;> simp [e]

theorem ABI.inputFit {s : State} (a : ABI s) (i : Fin 3) :
    (arg s (4 + 2 * i.val)).toNat + ((caller s).buffer (4 + 2 * i.val)).len ≤ 2 ^ 32 := by
  change (arg s _).toNat + (arg s _).toNat ≤ 2 ^ 32
  apply a.bounds
  have cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  rcases cases with e | e | e <;> simp [e]

theorem ABI.outputFit {s : State} (a : ABI s) (i : Fin 2) :
    (arg s (2 * i.val)).toNat + ((caller s).buffer (2 * i.val)).len ≤ 2 ^ 32 := by
  change (arg s _).toNat + (arg s _).toNat ≤ 2 ^ 32
  apply a.bounds
  have cases : i.val = 0 ∨ i.val = 1 := by omega
  rcases cases with e | e <;> simp [e]

theorem ABI.outputSeparate {s : State} (a : ABI s) (i j : Fin 2) (ne : i ≠ j) :
    ((caller s).buffer (2 * i.val)).Disjoint ((caller s).buffer (2 * j.val)) := by
  have neq : i.val ≠ j.val := fun h => ne (Fin.ext h)
  have casesI : i.val = 0 ∨ i.val = 1 := by omega
  have casesJ : j.val = 0 ∨ j.val = 1 := by omega
  rcases casesI with e | e <;> rcases casesJ with f | f
  all_goals try omega
  all_goals simp only [e, f, Nat.mul_zero, Nat.mul_one]
  · exact a.outSeparate
  · exact a.outSeparate.symm

end VG.Proof.Rsa.X86.Recover

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Bignum.X86

theorem Inputs.argsEq {g : CallGeometry} {s : State} {args : Nat → BitVec 32} (h : Inputs g s)
    (eq : ∀ i < 12, args i = g.args i) : Inputs {g with args := args} s := by
  have buffers (i : Nat) (hi : i + 1 < 12) :
      ({g with args := args} : CallGeometry).buffer i = g.buffer i := by
    simp only [CallGeometry.buffer, eq i (by omega), eq (i + 1) hi]
  have writes : ({g with args := args} : CallGeometry).writes = g.writes := by
    unfold CallGeometry.writes
    rw [buffers 0 (by decide), buffers 2 (by decide)]
  refine ⟨h.ws, h.lower, h.upper, h.esp, h.room, h.top, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.wrEq⟩
  · intro i hi
    change CallArgument s g.B g.Z i (args i)
    rw [eq i hi]
    exact h.arguments i hi
  · intro i hi r hr
    rw [writes] at hr
    exact h.stackApart i hi r hr
  · intro i; rw [buffers _ (by omega)]; exact h.inputPositive i
  · intro i; rw [buffers _ (by omega)]; exact h.inputBound i
  · intro i
    rw [buffers _ (by omega)]
    change (args (4 + 2 * i.val)).toNat + _ ≤ _
    rw [eq (4 + 2 * i.val) (by omega)]
    exact h.inputFit i
  · intro i; rw [buffers _ (by omega)]; exact h.inputRead i
  · intro i r hr; rw [writes] at hr; rw [buffers _ (by omega)]; exact h.inputApart i r hr
  · intro i; rw [buffers _ (by omega)]; exact h.outputPositive i
  · intro i; rw [buffers _ (by omega)]; exact h.outputBound i
  · intro i
    rw [buffers _ (by omega)]
    change (args (2 * i.val)).toNat + _ ≤ _
    rw [eq (2 * i.val) (by omega)]
    exact h.outputFit i
  · intro i; rw [buffers _ (by omega)]; exact h.outputWrite i
  · intro i; rw [buffers _ (by omega)]; exact h.outputScratch i
  · intro i j ne; rw [buffers _ (by omega), buffers _ (by omega)]; exact h.outputSeparate i j ne

/-- The inputs over a geometry that agrees on the arguments' values and the rest. -/
theorem Inputs.geoEq {g g' : CallGeometry} {s : State} (h : Inputs g s) (hB : g'.B = g.B) (hZ : g'.Z = g.Z)
    (hn : g'.n = g.n) (hsp : g'.sp = g.sp) (hwr : g'.wr = g.wr) (eq : ∀ i < 12, g'.args i = g.args i) :
    Inputs g' s := by
  obtain ⟨⟨B, Z, n, sp, a, wr⟩⟩ := g'
  dsimp only at hB hZ hn hsp hwr eq
  subst hB hZ hn hsp hwr
  exact h.argsEq eq

end VG.Proof.Rsa.X86.Recover

section

/-! # Establishing the arithmetic workspace while preserving the caller ABI -/

section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Bignum.X86 VG.Proof.Bignum.X86

theorem entry_ok {s : State} {base : Addr} {size : Nat} {ptr : BitVec 32}
    (read : readSrc s (.mem (PublicFn.argument 10)) = some ptr)
    (hb : ptr.setWidth 64 = base) (hf : ptr.toNat + size ≤ 2 ^ 32) (hz : 16 ≤ size)
    (hw : (⟨base, size⟩ : Region) ∈ s.wr) (stk : StkOk (s.gpr .esp) base size) :
    WP isa (.block VG.Impl.Rsa.X86.Recover.entry) s fun t =>
      Scr t base size ∧ Saved t.mem (off base) s.gpr PublicFn.savedRegisters ∧
      Keeps [.eax, .edi] s t ∧ Outside base 0 size s.mem t.mem := by
  unfold VG.Impl.Rsa.X86.Recover.entry
  simp only [List.singleton_append]
  refine wp_movS read fun u U _ => ?_
  refine WP.block_append (WP.mono (entrySave_ok (base := base) (size := size) (by rw [U.gpr]; exact hb)
    (by rw [U.gpr]; exact hf) hz (by rw [U.wr]; exact hw)) fun v ⟨G, Rd, Wr, S, F⟩ => ?_)
  refine wp_movS rfl fun t T _ => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [T.gpr, G, U.gpr]; exact hb
    · rw [T.wr, Wr, U.wr]; exact hw
    · rw [← hb, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans ptr.isLt (by decide))]
      exact hf
    · rw [T.other _ (by decide), G, U.other _ (by decide)]
      exact stk
  · intro p hp
    rw [T.mem, S p hp]
    have H : p.1 ≠ .eax := by
      simp only [PublicFn.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> decide
    exact U.other _ H
  · refine ⟨?_, ?_, ?_⟩
    · intro reg hr
      rw [T.other reg (by intro H; subst reg; exact hr (by simp)), G]
      exact U.other reg (by intro H; subst reg; exact hr (by simp))
    · rw [T.rd, Rd, U.rd]
    · rw [T.wr, Wr, U.wr]
  · intro a ha
    rw [T.mem]
    have H : ¬ InRegions [⟨base, size⟩] a 1 := by
      simp only [InRegions, List.mem_singleton, exists_eq_left, Region.Contains]
      change ¬ (ofs base a + 1 ≤ size)
      omega
    exact (F a (by intro reg hreg hcontains; exact H ⟨reg, hreg, hcontains⟩)).trans (congrFun U.mem a)

end VG.Proof.Rsa.X86.Recover
end

end

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Bignum.X86 VG.Impl.Rsa.X86.Recover

theorem installed_ok {s : State} (a : ABI s) :
    WP isa (.block entry) s fun t => Inputs (caller s) t ∧
      Spill.Saved t.mem (off (caller s).B) s.gpr PublicFn.savedRegisters ∧
      Keeps [.eax, .edi] s t ∧ Outside (caller s).B 0 (caller s).Z s.mem t.mem := by
  refine WP.mono (entry_ok (base := (caller s).B) (ptr := arg s 10) (a.stackArgument (by decide : 10 < 12)).readSrc
    rfl a.scratchBound (by have := a.used; omega) (by rw [a.wr]; simp) a.stack)
    fun t ⟨sc, saved, k, o⟩ => ?_
  refine ⟨?_, saved, k, o⟩
  have w := a.width
  refine ⟨⟨sc, a.space, by change 0 < 2 * (caller s).n + 2; omega,
    by change 2 * (caller s).n + 2 ≤ 1024; omega⟩, w.1, w.2.1, k.1 _ (by decide), a.room,
    a.stackBound, ?_, ?_,
    (fun i => (a.inputLength i).1), (fun i => (a.inputLength i).2), a.inputFit, ?_, ?_,
    (fun i => (a.outputLength i).1), (fun i => (a.outputLength i).2), a.outputFit, ?_, ?_, a.outputSeparate,
    k.2.2⟩
  · intro i hi
    exact (CallArgument.mk (a.stackArgument hi) rfl).keep k (by decide) o
  · intro i hi r hr
    rw [show stackAddress t i = stackAddress s i by simp only [stackAddress, k.1 .esp (by decide)]]
    exact a.stackApart hi hr
  · intro i
    rw [k.2.1, k.2.2]
    exact ⟨_, List.mem_append_left _ (a.inputMember i), Region.contains_self _ _⟩
  · exact fun i r hr => a.inApartW _ (a.inputMember i) r hr
  · intro i
    rw [k.2.2, a.wr]
    refine ⟨_, ?_, Region.contains_self _ _⟩
    exact List.mem_append_left [⟨(caller s).B, (caller s).Z⟩, ⟨argAddr s 0, 48⟩]
      (ABI.outputMember (s := s) i)
  · exact fun i => a.outScratch _ (ABI.outputMember i)

end VG.Proof.Rsa.X86.Recover

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum hiding off Outside
open VG.Proof.Bignum.X86 VG.Impl.Bignum.X86

theorem bodyFrame_full {g : CallGeometry} {m m' : Mem} (low : 16 ≤ g.Z)
    (f : Frame (bodyWrites g) m m') : Frame g.writes m m' := by
  apply f.sub
  intro r hr
  simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨⟨g.B, g.Z⟩, by simp [CallGeometry.writes], Offset.sub_base _ (by omega)⟩
  all_goals exact ⟨_, by simp [CallGeometry.writes], fun _ h => h⟩

theorem bodyFrame_saved {g : CallGeometry} {s : State} {m m' : Mem} {regs : Reg → BitVec 32}
    (h : Inputs g s) (f : Frame (bodyWrites g) m m')
    (saved : Saved m (off g.B) regs PublicFn.savedRegisters) :
    Saved m' (off g.B) regs PublicFn.savedRegisters := by
  have low : 16 ≤ g.Z := by have := h.ws.hdr_le; unfold VG.Impl.Rsa.X86.Keys.hdr at this; omega
  have high : g.Z ≤ 2 ^ 64 := by have := h.ws.workspace.nowrap; omega
  intro p hp
  have bound : p.2 + 4 ≤ 16 := by
    simp only [PublicFn.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  refine (f.readW (r := ⟨g.B, 16⟩) (Offset.contains_base _ bound (by omega)) ?_ (by decide)).trans (saved p hp)
  intro r hr
  simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.base_disjoint g.B (Nat.le_refl 16) (by omega)
  · exact (h.outputScratch 0).symm.sub_left (Region.sub_prefix low)
  · exact (h.outputScratch 1).symm.sub_left (Region.sub_prefix low)
  · exact h.room.apart.symm.sub_left (Region.sub_prefix low)

end VG.Proof.Rsa.X86.Recover

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86

def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 16
    else if a = 0x20008 then 64
    else if a = 0x2000d then 32
    else if a = 0x20010 then 64
    else if a = 0x20015 then 64
    else if a = 0x20018 then 64
    else if a = 0x2001d then 80
    else if a = 0x20020 then 1
    else if a = 0x20025 then 96
    else if a = 0x20028 then 1
    else if a = 0x2002e then 1
    else if a = 0x20030 then 32
    else if a = 0x20031 then 4 else 0
  rd := [⟨0x4000, 64⟩, ⟨0x5000, 1⟩, ⟨0x6000, 1⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 64⟩, ⟨0x10000, 8448⟩, ⟨0x20004, 48⟩]

end VG.Proof.Rsa.X86.Recover

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/CvStores.lean`, which only this module imported.
section

/-! # Release all three CRT values under their common acceptance mask -/

section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.CrtValues
open VG.Proof.Rsa.X86.Keys

end VG.Proof.Rsa.X86.CrtValues
end

end

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum VG.Proof.Bignum.X86
open VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys VG.Impl.Rsa.X86.Recover
open VG.Impl.Rsa.X86.CrtValues (clear)
open VG.Proof.Rsa.X86.CrtValues (clear_ok)

theorem outputFrame_body {g : CallGeometry} {m m' : Mem} (i : Fin 2)
    (f : Frame [g.buffer (2 * i.val)] m m') : Frame (bodyWrites g) m m' := by
  apply f.mono
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  have cases : i.val = 0 ∨ i.val = 1 := by omega
  rcases cases with e | e <;> simp [bodyWrites, e]

theorem clear_input_ok {g : CallGeometry} {s : State} (h : Inputs g s) (i : Fin 2) :
    WP isa (clear (2 * i.val)) s fun t => Inputs g t ∧
      Spec.Rsa.bytesAt t.mem (g.buffer (2 * i.val)).base (g.buffer (2 * i.val)).len =
        List.replicate (g.buffer (2 * i.val)).len 0 ∧
      t.gpr .eax = 0 ∧ Frame [g.buffer (2 * i.val)] s.mem t.mem ∧
      Keeps [.esi, .ecx, .eax] s t := by
  have arg := h.arguments (2 * i.val) (by omega)
  have len := h.arguments (2 * i.val + 1) (by omega)
  have bound : (g.buffer (2 * i.val)).len < 2 ^ 32 := by
    have := h.outputBound i; have := h.upper; omega
  refine WP.mono (clear_ok (2 * i.val) (h.outputPositive i) bound (h.outputFit i)
    arg.readSrc (by simpa only [CallGeometry.buffer, BitVec.ofNat_toNat, BitVec.setWidth_eq] using len.readSrc)
    (h.outputWrite i)) fun t ⟨v, z, o, k⟩ => ?_
  have f : Frame [g.buffer (2 * i.val)] s.mem t.mem := by
    simpa only [CallGeometry.buffer, byteAddr, Bignum.off, BitVec.add_zero] using outside_frame o (by omega)
  refine ⟨h.after k (by decide) (by decide) ?_, v, z, f, k⟩
  apply f.mono
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  have cases : i.val = 0 ∨ i.val = 1 := by omega
  rcases cases with e | e <;> simp [CallGeometry.writes, e]

theorem clear_other {g : CallGeometry} {s : State} {m m' : Mem} (h : Inputs g s)
    (i k : Fin 2) (ne : k ≠ i) (f : Frame [g.buffer (2 * i.val)] m m') :
    Spec.Rsa.bytesAt m' (g.buffer (2 * k.val)).base (g.buffer (2 * k.val)).len =
      Spec.Rsa.bytesAt m (g.buffer (2 * k.val)).base (g.buffer (2 * k.val)).len := by
  apply VG.Proof.Rsa.rsa_bytes_frame f (by have := h.outputBound k; have := h.upper; omega)
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact h.outputSeparate k i ne

theorem failure_ok {g : CallGeometry} {s : State} (h : Inputs g s) :
    WP isa failure s fun t => Inputs g t ∧
      Spec.Rsa.bytesAt t.mem (g.buffer 0).base (g.buffer 0).len = List.replicate (g.buffer 0).len 0 ∧
      Spec.Rsa.bytesAt t.mem (g.buffer 2).base (g.buffer 2).len = List.replicate (g.buffer 2).len 0 ∧
      t.gpr .eax = 0 ∧ Frame (bodyWrites g) s.mem t.mem ∧ Keeps [.esi, .ecx, .eax] s t := by
  unfold VG.Impl.Rsa.X86.Recover.failure
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (clear_input_ok h 0) fun u ⟨hu, vu, _, fu, ku⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (clear_input_ok hu 1) fun v ⟨hv, vv, _, fv, kv⟩ => ?_
  refine wp_movS rfl fun t T _ => WP.block_nil ?_
  refine ⟨hv.after T.keeps (by decide) (by decide) (by rw [T.mem]; exact Frame.refl _ _),
    ?_, ?_, T.gpr, ?_, ku.trans (kv.trans (T.keeps.mono (by decide)))⟩
  · rw [T.mem]
    exact (clear_other hu 1 0 (by decide) fv).trans vu
  · rw [T.mem]
    exact vv
  · rw [T.mem]
    exact (outputFrame_body 0 fu).trans (outputFrame_body 1 fv)

end VG.Proof.Rsa.X86.Recover

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Bignum.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Recover
open VG.Impl.Rsa.X86.CrtValues (clear)

theorem clear_trace (g : CallGeometry) (i : Fin 2) :
    RelCT isa (Pair g) (clear (2 * i.val)) (fun _ _ => True) := by
  have zero : RelCT isa (VG.X86.Taint.Agree loadTaint) (.block [.mov .eax (.imm 0)])
      (VG.X86.Taint.Agree loadTaint) := checkedProgramChange (hint := .block []) rfl rfl
  have head := VG.RelCT.block_append (VG.RelCT.seq
    (loadArguments_relCT (2 * i.val) (2 * i.val + 1) (g.args (2 * i.val)) (g.args (2 * i.val + 1))) zero)
  have loop : RelCT isa (VG.X86.Taint.Agree loadTaint) (.loop (.block PublicFn.clearStep) .ne)
      (fun _ _ => True) := by
    apply RelCT.taint (A := taint) loadTaint (fun _ _ h => h)
      (hc := VG.Taint.hintOf taint loadTaint (.loop (.block PublicFn.clearStep) .ne))
    rfl
  apply (VG.RelCT.seq head loop).mono
  · intro s t h
    exact ⟨h.agree, (h.left.arguments _ (by omega)).readSrc, (h.right.arguments _ (by omega)).readSrc,
      (h.left.arguments _ (by omega)).readSrc, (h.right.arguments _ (by omega)).readSrc⟩
  · exact fun _ _ h => h

theorem clear_relCT (g : CallGeometry) (i : Fin 2) : RelCT isa (Pair g) (clear (2 * i.val)) (Pair g) := by
  intro s t tr ur sf tf h es et
  have eq := (clear_trace g i _ _ _ _ _ _ h es et).1
  obtain ⟨hs, _, _, _, ks⟩ := wp_result (clear_input_ok h.left i) es
  obtain ⟨ht, _, _, _, kt⟩ := wp_result (clear_input_ok h.right i) et
  exact ⟨eq, h.after hs ht ks kt (by decide)⟩

theorem failure_relCT (g : CallGeometry) :
    RelCT isa (Pair g) VG.Impl.Rsa.X86.Recover.failure (fun _ _ => True) :=
  VG.RelCT.seq (clear_relCT g 0) (VG.RelCT.seq (clear_relCT g 1) (by
    apply VG.RelCT.taint (A := taint) (VG.Proof.Mont.X86.Dynamic.workspaceTaint false)
      (fun _ _ h => h.workspace) (hc := .block [])
    rfl))

end VG.Proof.Rsa.X86.Recover

namespace VG.Proof.Rsa.X86.Recover
open VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Dsa.X86 VG.Proof.Mont.X86.Dynamic

theorem entry_relCT :
    RelCT isa (fun s t => s.gpr .esp = t.gpr .esp ∧ stackValue s 10 = stackValue t 10 ∧
      readSrc s (.mem (PublicFn.argument 10)) = some (stackValue s 10) ∧
      readSrc t (.mem (PublicFn.argument 10)) = some (stackValue t 10))
      (.block VG.Impl.Rsa.X86.Recover.entry) (VG.X86.Taint.Agree argumentTaint) := by
  unfold VG.Impl.Rsa.X86.Recover.entry
  rw [List.append_assoc]
  apply VG.RelCT.block_append
  exact VG.RelCT.seq (scratchArgument_relCT 10)
    (checkedProgramChange (τ' := { argumentTaint with regs := .ofList [.esp, .edi, .eax] })
      (hint := .block []) rfl rfl)

end VG.Proof.Rsa.X86.Recover

namespace VG.Proof.Rsa.X86.Recover
open VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86

theorem modulus_ok {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g) :
    WP isa (.seq (.block (VG.Impl.Rsa.X86.CrtValues.inputArgs 4)) (.block modulusCheck)) s fun t =>
      t.zf = some (Spec.Rsa.modulusValid (Spec.Rsa.os2ip (inputBytes g s.mem 0)) (g.args 5).toNat) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  refine WP.seq (WP.mono (argumentPair_ok (d := .esi) (by decide) (by decide)
    (h.arguments 4 (by decide)).readSrc (h.arguments 5 (by decide)).readSrc)
    fun u ⟨p, c, m, k⟩ => ?_)
  refine WP.mono (modulusCheck_ok u len.lower len.upper (by rw [p]; exact h.inputFit 0)
    (by rw [p, k.2.1, k.2.2]; exact h.inputRead 0)
    (by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using c)) fun t ⟨z, mt, kt⟩ => ?_
  rw [p, m] at z
  exact ⟨z, mt.trans m, (k.mono (by decide)).trans (kt.mono (by decide))⟩

theorem modulus_relCT (g : CallGeometry) :
    RelCT isa (Pair g) (.seq (.block (VG.Impl.Rsa.X86.CrtValues.inputArgs 4)) (.block modulusCheck))
      (fun _ _ => True) := by
  have check : RelCT isa (VG.X86.Taint.Agree loadTaint) (.block modulusCheck) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) loadTaint (fun _ _ h => h) (hc := .block [])
    rfl
  apply (VG.RelCT.seq (loadArguments_relCT 4 5 (g.args 4) (g.args 5)) check).mono
  · intro s t h
    exact ⟨h.agree, (h.left.arguments 4 (by decide)).readSrc, (h.right.arguments 4 (by decide)).readSrc,
      (h.left.arguments 5 (by decide)).readSrc, (h.right.arguments 5 (by decide)).readSrc⟩
  · exact fun _ _ h => h

end VG.Proof.Rsa.X86.Recover

namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.RtCall
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover

open VG.Proof.Rsa.X86.Keys
open VG.Proof.Bignum.X86.PublicRt (calleeOf argByte_alloc calleeOf_eq rtPub_of)

/-- The return address and the arguments lie apart from every writable region. -/
def ArgsOk (s : State) : Prop :=
  (s.gpr .esp).toNat + 52 ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 52⟩ r

/-- The geometry's writable regions lie apart from the return address and the arguments. -/
def PubG (g : Geo) : Prop :=
  g.sp.toNat + 52 ≤ 2 ^ 32 ∧ ∀ r ∈ g.wr, Region.Disjoint ⟨g.sp.setWidth 64, 52⟩ r

theorem τA_wf {s : State} (A : ArgsOk s) : VG.X86.Taint.Wf τA s :=
  VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => A, fun _ h => (List.not_mem_nil h).elim⟩

section
variable {g : Geo} {s0 t0 s t : State} {A B AW BW V W : Nat → Nat} {al bl aw bw sl tl : List Nat}

theorem KS.argsOk (pg : PubG g) (h : KS g s0 A al AW aw V sl s) : ArgsOk s := by
  unfold ArgsOk
  rw [h.sp, h.rest.2.2, h.start.1]
  exact pg

/-- Two runs of stages over the same geometry agree on what `τA` makes public. -/
theorem ks_agree (pg : PubG g) (h : KS g s0 A al AW aw V sl s) (j : KS g t0 B bl BW bw W tl t) :
    VG.X86.Taint.Agree τA s t := by
  have f₁ := (h.argsOk pg).1
  have f₂ := (j.argsOk pg).1
  have sp : s.gpr .esp = t.gpr .esp := h.sp.trans j.sp.symm
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, τA_wf (h.argsOk pg), τA_wf (j.argsOk pg),
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => sp, fun k h4 hk => ?_⟩
  · simp only [τA, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact BitVec.eq_of_toNat_eq (h.ws.workspace.edi_toNat.trans j.ws.workspace.edi_toNat.symm)
    · exact sp
  · simp only [τA] at hk
    have C₁ := h.arg (h.start.2 ((k - 4) / 4) (by omega)).1 (by omega)
    have C₂ := j.arg (j.start.2 ((k - 4) / 4) (by omega)).1 (by omega)
    rw [show VG.X86.Taint.depth τA.stk = 0 from rfl, Nat.zero_add,
      VG.X86.Taint.argByte_eq f₁ h4 hk, VG.X86.Taint.argByte_eq f₂ h4 hk,
      Mem.readW_byte s.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte t.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (show arg s _ = arg t _ from C₁.value.trans C₂.value.symm)

end

/-- A loop of `c` rounds, each related by `body`, its flag from each run's invariant. -/
theorem fixedLoop_relCT {body : Prog isa} {c : Nat}
    (I J : Nat → State → Prop) (positive : 0 < c)
    (rel : ∀ k, k < c → RelCT isa (fun s t => I k s ∧ J k t) body (fun _ _ => True))
    (left : ∀ k s, k < c → I k s → WP isa body s fun t =>
      I (k + 1) t ∧ t.zf = some (decide (c - (k + 1) = 0)))
    (right : ∀ k s, k < c → J k s → WP isa body s fun t =>
      J (k + 1) t ∧ t.zf = some (decide (c - (k + 1) = 0))) :
    RelCT isa (fun s t => I 0 s ∧ J 0 t) (.loop body .ne)
      (fun s t => I c s ∧ J c t) := by
  have loop := VG.RelCT.loop (M := isa) (body := body) (c := .ne)
    (Q := fun s t => I c s ∧ J c t)
    (fun remaining s t => ∃ k, k + remaining = c ∧ 0 < remaining ∧ I k s ∧ J k t)
    (fun remaining s t tr ur sf tf ⟨k, sum, pos, hs, ht⟩ es et => by
      have trace := (rel k (by omega) _ _ _ _ _ _ ⟨hs, ht⟩ es et).1
      obtain ⟨is, zs⟩ := VG.Proof.Dsa.X86.wp_result (left k s (by omega) hs) es
      obtain ⟨it, zt⟩ := VG.Proof.Dsa.X86.wp_result (right k t (by omega) ht) et
      refine ⟨trace, ?_, ?_, ?_⟩
      · change sf.zf.map (!·) = tf.zf.map (!·)
        rw [zs, zt]
      · intro done
        have last : k + 1 = c := by
          change sf.zf.map (!·) = some false at done
          rw [zs] at done
          simp only [Option.map_some, Option.some.injEq, Bool.not_eq_false', decide_eq_true_eq] at done
          omega
        exact ⟨last ▸ is, last ▸ it⟩
      · intro more
        have next : k + 1 < c := by
          change sf.zf.map (!·) = some true at more
          rw [zs] at more
          simp only [Option.map_some, Option.some.injEq, Bool.not_eq_true', decide_eq_false_iff_not] at more
          omega
        exact ⟨remaining - 1, by omega, k + 1, by omega, by omega, is, it⟩) c
  apply loop.mono
  · intro s t ⟨hs, ht⟩
    exact ⟨0, by omega, positive, hs, ht⟩
  · intro s t h; exact h

/-- What each run of the call leaves: a stage. -/
def MulPost (g : Geo) (u : State) : Prop := ∃ s0 A live AW liveW V ls, KS g s0 A live AW liveW V ls u

theorem KS.stage {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {live liveW ls : List Nat}
    (h : KS g s0 A live AW liveW V ls s) : MulPost g s := ⟨_, _, _, _, _, _, _, h⟩

end VG.Proof.Rsa.X86.Recover

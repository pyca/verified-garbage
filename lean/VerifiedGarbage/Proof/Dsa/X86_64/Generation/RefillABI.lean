module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillContract
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Dsa.Generation.Layout
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Output
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Out
public import Mathlib.Algebra.Group.Nat.Defs
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ArenaSource
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryWork
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CopyDigest
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf

/-! ### `Dsa.X86_64.Generation.OutputPlan`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.Generation.OutputArgs`, which this module and modules that import it used -/

section

/-! # Prepare output copying and the existing verified zero-output loop -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem outputArgs_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) {len : Nat} (hlen : W 7 = BitVec.ofNat 64 len) :
    WP isa (.block Impl.Dsa.X86_64.Generation.outputArgs) s fun t =>
      t.gpr .rsi = off (W 5) packed ∧ t.gpr .rdi = W 6 ∧
      t.gpr .rcx = BitVec.ofNat 64 len ∧ t.gpr .rdx = BitVec.ofNat 64 (8 * len) ∧
      t.mem = s.mem ∧ Keep [.rsi, .rdi, .rcx, .rdx] s t := by
  refine WP.mono (WP.keep [.rsi, .rdi, .rcx, .rdx] (Q := fun t =>
      t.gpr .rsi = off (W 5) packed ∧ t.gpr .rdi = W 6 ∧
      t.gpr .rcx = BitVec.ofNat 64 len ∧ t.gpr .rdx = BitVec.ofNat 64 (8 * len) ∧ t.mem = s.mem) (by
    xrun [Impl.Dsa.X86_64.Generation.outputArgs, ea_sp, L.rsp,
      L.ld (d := 40) (by decide), R.slot (d := 40) (k := 5) rfl (by decide) rfl,
      L.ld (d := 48) (by decide), R.slot (d := 48) (k := 6) rfl (by decide) rfl,
      L.ld (d := 56) (by decide), R.slot (d := 56) (k := 7) rfl (by decide) hlen,
      sx_ofNat (by decide : packed < 2 ^ 31)]
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 len * BitVec.ofNat 64 8 = BitVec.ofNat 64 (8 * len)
    rw [← BitVec.ofNat_mul, Nat.mul_comm]) rfl)
    fun _ ⟨⟨a, b, c, d, e⟩, hk⟩ => ⟨a, b, c, d, e, hk⟩

theorem zeroArgs_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) :
    WP isa (.block Impl.Dsa.X86_64.Generation.zeroArgs) s fun t =>
      Lay t F S ∧ Rep t.mem F S V (upd (upd W 21 (W 6)) 23 (W 7)) ∧
      Frame [⟨F, frameBytes⟩] s.mem t.mem ∧ Keep [.rax] s t := by
  have read : (s.mem.writeW (off F 168) (W 6)).readW (off F 56) 64 = W 7 :=
    (R.wf L.geo (by decide : 21 < nW) _).slot (d := 56) (k := 7) rfl (by decide) (by simp [upd])
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
      t.mem = (s.mem.writeW (off F 168) (W 6)).writeW (off F 184) (W 7)) (by
    xrun [Impl.Dsa.X86_64.Generation.zeroArgs, ea_sp, L.rsp,
      L.ld (d := 48) (by decide), R.slot (d := 48) (k := 6) rfl (by decide) rfl,
      L.ld (d := 56) (by decide), L.st (d := 168) (by decide), L.st (d := 184) (by decide), read]) rfl)
    fun t ⟨hm, kt⟩ => ?_
  have Rt : Rep t.mem F S V (upd (upd W 21 (W 6)) 23 (W 7)) := by
    rw [hm]
    exact (R.wf L.geo (by decide : 21 < nW) _).wf L.geo (by decide : 23 < nW) _
  refine ⟨lay_of_rep L R Rt (by simp [upd]) (kt.gpr (by decide)) kt.2.2, Rt, ?_, kt⟩
  rw [hm]
  exact ((Frame.refl [⟨F, frameBytes⟩] s.mem).writeW (r := ⟨F, frameBytes⟩) (by simp) _ (Offset.contains_base _ (by decide) (by decide))).writeW (r := ⟨F, frameBytes⟩)
    (by simp) _ (Offset.contains_base _ (by decide) (by decide))

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # The caller's output is disjoint from every parameter-search workspace -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/OutputCopy.lean`, which only this module imported.
section

/-! # Copy accepted packed parameters to the caller and return success -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

theorem outputCopy_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} {bs : List Byte}
    (L : Lay s F S) (R : Rep s.mem F S V W) (hlen : W 7 = BitVec.ofNat 64 bs.length)
    (hl : 2 ≤ bs.length ∧ bs.length ≤ 1024)
    (hrd : ∀ i < bs.length, InRegions (s.rd ++ s.wr) (off (off (W 5) packed) i) 1)
    (hwr : ∀ i < bs.length, InRegions s.wr (off (W 6) i) 1)
    (hb : ∀ i < bs.length, s.mem (off (off (W 5) packed) i) = bs.getD i 0)
    (sep : ∀ i < bs.length, ∀ j < bs.length, off (off (W 5) packed) i ≠ off (W 6) j) :
    WP isa Impl.Dsa.X86_64.Generation.outputCopy s fun t =>
      t.gpr .rax = 1 ∧ Spec.Rsa.bytesAt t.mem (W 6) bs.length = bs ∧
      Frame [⟨W 6, bs.length⟩] s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t := by
  unfold Impl.Dsa.X86_64.Generation.outputCopy
  refine WP.seq (WP.mono (outputArgs_ok L R hlen) fun u ⟨hsi, hdi, hcx, hdx, hm, ku⟩ => ?_)
  refine WP.seq (WP.mono (copyBytes_ok hl hsi hdi hcx hdx
    (fun i hi => by rw [ku.2.1, ku.2.2]; exact hrd i hi)
    (fun i hi => by rw [ku.2.2]; exact hwr i hi)
    (fun i hi => by rw [hm]; exact hb i hi) sep) fun v ⟨bytes, fv, kv⟩ => ?_)
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = 1 ∧ t.mem = v.mem)
    (by xrun) rfl) fun t ⟨⟨hr, hmem⟩, kt⟩ => ?_
  refine ⟨hr, hmem ▸ bytes, ?_, ((ku.trans kv).trans kt).mono (by decide)⟩
  intro a ha
  rw [hmem, fv a (by
    intro i hi he
    apply ha ⟨W 6, bs.length⟩ (by simp)
    rw [he]
    exact Offset.contains_base _ (by omega) (by omega)), hm]

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

structure OutputPlan (p : GenerationContext) : Prop where
  lengthSlot : p.saved 7 = BitVec.ofNat 64 (2 * p.geo.pLen + p.geo.qLen)
  bound : (p.saved 6).toNat + (2 * p.geo.pLen + p.geo.qLen) ≤ 2 ^ 64
  separate : ∀ r ∈ p.changed, (⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩ : Region).Disjoint r

theorem OutputPlan.apart {p : GenerationContext} (o : OutputPlan p) :
    Apart p.geo.F p.geo.hash ⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩ := by
  have hh := p.geo.small_bound (d := VG.Impl.Dsa.Generation.Layout.hash) (n := oRsa) (by decide) (by decide)
  refine ⟨(o.separate _ (by simp [GenerationContext.changed])).symm, ?_, ?_⟩
  · exact ((o.separate _ (by simp [GenerationContext.changed])).sub_right (p.geo.part_sub hh)).symm
  · exact ((o.separate (below p.geo.F 192) (by simp [GenerationContext.changed])).sub_right (below_sub (a := 16) (by decide) (by decide))).symm

theorem OutputPlan.packed {p : GenerationContext} (o : OutputPlan p) :
    (p.geo.part packed (2 * p.geo.pLen + p.geo.qLen)).Disjoint ⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩ := by
  have pn : p.geo.pLen ≤ 384 := by rcases p.geo.width with h | h | h <;> omega_using [h]
  have qn : p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with h | h <;> omega_using [h]
  exact ((o.separate _ (by simp [GenerationContext.changed])).sub_right
    (p.geo.part_sub (p.geo.small_bound (by decide) (by unfold arithmeticBytes; omega_using [pn, qn])))).symm

theorem output_copy_context {p : GenerationContext} {W : Nat → BitVec 64} {s : State}
    (h : GenerationMemory p W s) (o : OutputPlan p)
    (hw : (⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩ : Region) ∈ s.wr)
    (bs : List Byte) (hlen : bs.length = 2 * p.geo.pLen + p.geo.qLen)
    (bytes : Spec.Rsa.bytesAt s.mem (off p.geo.B packed) (2 * p.geo.pLen + p.geo.qLen) = bs) :
    WP isa Impl.Dsa.X86_64.Generation.outputCopy s fun t =>
      t.gpr .rax = 1 ∧ Spec.Rsa.bytesAt t.mem (p.saved 6) (2 * p.geo.pLen + p.geo.qLen) = bs ∧
      Frame [⟨p.saved 6, 2 * p.geo.pLen + p.geo.qLen⟩] s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t := by
  have pn : 2 ≤ p.geo.pLen ∧ p.geo.pLen ≤ 384 := by rcases p.geo.width with hh | hh | hh <;> omega_using [hh]
  have qn : p.geo.qLen ≤ 32 := by rcases p.geo.qWidth with hh | hh <;> omega_using [hh]
  have bound := p.geo.small_bound (d := packed) (n := 2 * p.geo.pLen + p.geo.qLen)
    (by decide) (by unfold arithmeticBytes; omega_using [pn, qn])
  have source : Src s (p.saved 6) (2 * p.geo.pLen + p.geo.qLen) (off p.geo.B packed) bs := by
    apply arena_source h.scratch
    · simpa only [hlen] using bound
    · rw [hlen]; omega_using [pn, qn]
    · simpa only [hlen] using bytes
    · simpa only [hlen, GenerationGeometry.part] using o.packed
  have h5 := (h.slots 5 (by simp [generationSlots])).trans p.baseSlot
  have h6 := h.slots 6 (by simp [generationSlots])
  have h7 := (h.slots 7 (by simp [generationSlots])).trans o.lengthSlot
  obtain ⟨V, R⟩ := h.rep
  have call := outputCopy_ok h.layout R (by simpa only [hlen] using h7)
    (show 2 ≤ bs.length ∧ bs.length ≤ 1024 by rw [hlen]; omega_using [pn, qn])
  rw [h5, h6, hlen] at call
  apply call
  · intro i hi; exact source.rd i (hlen ▸ hi)
  · intro i hi; exact ⟨_, hw, Offset.contains_base _ (by omega_using [hi]) (by omega_using [pn, qn, hi])⟩
  · intro i hi
    simpa only [off, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlen ▸ hi), Option.getD_some] using source.val i (hlen ▸ hi)
  · intro i hi j hj he
    apply o.packed (off (off p.geo.B packed) i)
      (Offset.contains_base _ (by omega_using [hi]) (by omega_using [pn, qn, hi]))
    rw [he]
    exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [pn, qn, hj])

end VG.Proof.Dsa.X86_64.Generation

end

end

-- separate module: the precondition's facts and the frames, apart from the entry's symbolic execution

/-! # The refillable-tape search's precondition, as facts about the machine

`vg_dsa_parameter_search(out, out_len, used, rand, rand_len, scratch,
scratch_len, state)` for one width: six arguments in registers and two on
the stack. Its stack is 568 octets: the saved registers' 48, the
controller's 32, the attempts' 296 and the 192 below them that the attempts'
calls use. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64.Generation.Refill

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- The stack the search uses below its return address. -/
abbrev refillStack : Nat := 568

def inOut (s : State) : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
def inUsed (s : State) : Region := ⟨s.gpr .rdx, 8⟩
def inRand (s : State) : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
def inScr (s : State) : Region := ⟨s.gpr .r9, (stackArg s 0).toNat * 8⟩
def inState (s : State) : Region := ⟨stackArg s 1, 32⟩
def inArgs (s : State) : Region := ⟨stackArgAddr s 0, 16⟩

/-- The modulus's width, `state[1]`. -/
abbrev refillPLen (s : State) : Nat := (s.mem.readW (stackArg s 1 + 8) 64).toNat

structure RefillABI (pBytes : Nat) (s : State) : Prop where
  stackLower : refillStack ≤ (s.gpr .rsp).toNat
  stackUpper : (s.gpr .rsp).toNat + 24 ≤ 2 ^ 64
  rd : s.rd = [inRand s, inArgs s]
  wr : s.wr = [inOut s, inUsed s, inScr s, inState s]
  outUsed : (inOut s).Disjoint (inUsed s)
  outRand : (inOut s).Disjoint (inRand s)
  outScr : (inOut s).Disjoint (inScr s)
  outState : (inOut s).Disjoint (inState s)
  outArgs : (inOut s).Disjoint (inArgs s)
  usedRand : (inUsed s).Disjoint (inRand s)
  usedScr : (inUsed s).Disjoint (inScr s)
  usedState : (inUsed s).Disjoint (inState s)
  usedArgs : (inUsed s).Disjoint (inArgs s)
  randScr : (inRand s).Disjoint (inScr s)
  randState : (inRand s).Disjoint (inState s)
  scrState : (inScr s).Disjoint (inState s)
  scrArgs : (inScr s).Disjoint (inArgs s)
  stateArgs : (inState s).Disjoint (inArgs s)
  retOut : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (inOut s)
  retUsed : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (inUsed s)
  retRand : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (inRand s)
  retScr : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (inScr s)
  retState : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (inState s)
  retArgs : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (inArgs s)
  stackOut : (below (s.gpr .rsp) refillStack).Disjoint (inOut s)
  stackUsed : (below (s.gpr .rsp) refillStack).Disjoint (inUsed s)
  stackRand : (below (s.gpr .rsp) refillStack).Disjoint (inRand s)
  stackScr : (below (s.gpr .rsp) refillStack).Disjoint (inScr s)
  stackState : (below (s.gpr .rsp) refillStack).Disjoint (inState s)
  stackArgs : (below (s.gpr .rsp) refillStack).Disjoint (inArgs s)
  outBound : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  usedBound : (s.gpr .rdx).toNat + 8 ≤ 2 ^ 64
  randBound : (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64
  scrBound : (s.gpr .r9).toNat + (stackArg s 0).toNat * 8 ≤ 2 ^ 64
  stateBound : (stackArg s 1).toNat + 32 ≤ 2 ^ 64
  width : refillPLen s = pBytes
  valid : Spec.Dsa.generationPLenValid (refillPLen s)
  outLength : (s.gpr .rsi).toNat = 2 * refillPLen s + Spec.Dsa.generationQLen (refillPLen s)
  scratchLength : Spec.Dsa.generationScratchWords (refillPLen s) ≤ (stackArg s 0).toNat
  seeds : (s.mem.readW (stackArg s 1) 64).toNat ≤ Spec.Dsa.parameterSeeds
  budget : s.mem.readW (stackArg s 1 + 16) 64 = BitVec.ofNat 64 (Spec.Dsa.parameterEntropy (refillPLen s))
  randLength : (s.gpr .r8).toNat ≤ Spec.Dsa.parameterEntropy (refillPLen s)

theorem stackArgs_two (s : State) : List.map (stackArg s) (List.range 2) = [stackArg s 0, stackArg s 1] := rfl

theorem refillABI_of {pBytes : Nat} {s : State} (h : (contract pBytes abi refillStack).pre s) :
    RefillABI pBytes s := by
  sig_pre [contract, Spec.Dsa.parameterSearchSig, abi, argRegs, stackArgs_two, stackBelow, List.range, List.range.loop,
    inOut, inUsed, inRand, inScr, inState, inArgs] at h
  sig_pre [contract, Spec.Dsa.parameterSearchSig, abi, argRegs, stackArgs_two, stackBelow, List.range, List.range.loop,
    inOut, inUsed, inRand, inScr, inState, inArgs] at h
  sig_split h
  constructor
  all_goals try simp only [inOut, inUsed, inRand, inScr, inState, inArgs]
  all_goals with_reducible assumption

/-! ## The frames

The stack below the return address, from `low = rsp - 568` up: the 192
octets the attempts' calls use, the attempts' frame of 296 (`refillBase`),
the controller's 32 and the saved registers' 48. -/

def low (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 refillStack

/-- The attempts' frame. -/
def refillBase (s : State) : Addr := off (low s) 192

/-- The controller's words. -/
def ctlRegion (F : Addr) : Region := ⟨off F 296, 32⟩

/-- The controller's `k`-th word. -/
def ctlWord (m : Mem) (F : Addr) (k : Nat) : BitVec 64 := m.readW (off F (296 + 8 * k)) 64

theorem low_toNat {pBytes : Nat} {s : State} (h : RefillABI pBytes s) :
    (low s).toNat = (s.gpr .rsp).toNat - refillStack := by
  have hl := h.stackLower
  simp only [low, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := (s.gpr .rsp).isLt
  omega_using [hl]

theorem refillBase_toNat {pBytes : Nat} {s : State} (h : RefillABI pBytes s) :
    (refillBase s).toNat = (s.gpr .rsp).toNat - 376 := by
  have hl : 568 ≤ (s.gpr .rsp).toNat := h.stackLower
  have hb := low_toNat h
  have := (s.gpr .rsp).isLt
  simp only [refillBase, off, BitVec.toNat_add, BitVec.toNat_ofNat, hb, refillStack, Nat.reducePow, Nat.reduceMod]
  omega_using [hl]

theorem low_sub {d n : Nat} (s : State) (h : d + n ≤ refillStack) :
    Region.Sub ⟨off (low s) d, n⟩ (below (s.gpr .rsp) refillStack) :=
  Offset.sub_base _ h

theorem refillBase_below (s : State) : below (refillBase s) 192 = ⟨low s, 192⟩ := by
  simp only [below, refillBase, off, BitVec.add_sub_cancel]

theorem ctlRegion_eq (s : State) : ctlRegion (refillBase s) = ⟨off (low s) 488, 32⟩ := by
  simp only [ctlRegion, refillBase, off_off]

/-- Regions of the stack below the return address are disjoint from the buffers. -/
theorem RefillABI.stack_disjoint {pBytes : Nat} {s : State} (h : RefillABI pBytes s) {d n : Nat}
    (hd : d + n ≤ refillStack) {r : Region}
    (hr : r = inOut s ∨ r = inUsed s ∨ r = inRand s ∨ r = inScr s ∨ r = inState s ∨ r = inArgs s) :
    (⟨off (low s) d, n⟩ : Region).Disjoint r := by
  have sub := low_sub s hd
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.stackOut.sub_left sub
  · exact h.stackUsed.sub_left sub
  · exact h.stackRand.sub_left sub
  · exact h.stackScr.sub_left sub
  · exact h.stackState.sub_left sub
  · exact h.stackArgs.sub_left sub

/-! ## The search's context -/

theorem RefillABI.lengths {pBytes : Nat} {s : State} (h : RefillABI pBytes s) :
    Spec.Dsa.generationLengthsValid pBytes (Spec.Dsa.generationQLen pBytes) := by
  have hv := h.valid
  rw [h.width] at hv
  simp only [Spec.Dsa.generationPLenValid, Bool.or_eq_true, beq_iff_eq] at hv
  rcases hv with (rfl | rfl) | rfl <;> decide

theorem RefillABI.scratchSize {pBytes : Nat} {s : State} (h : RefillABI pBytes s) :
    VG.Impl.Dsa.Generation.Layout.usedBytes pBytes ≤ (stackArg s 0).toNat * 8 := by
  have hl := VG.Proof.Dsa.Generation.generation_layout_fits h.lengths
  have hs := h.scratchLength
  rw [h.width] at hs
  omega_using [hl, hs]

theorem RefillABI.arena_sub {pBytes : Nat} {s : State} (h : RefillABI pBytes s) :
    Region.Sub ⟨s.gpr .r9, VG.Impl.Dsa.Generation.Layout.usedBytes pBytes⟩ (inScr s) := by
  simpa [inScr] using (Offset.sub_base (s.gpr .r9) (d := 0) (by simpa using h.scratchSize))

def refillGeometry {pBytes : Nat} {s : State} (h : RefillABI pBytes s) : GenerationGeometry where
  B := s.gpr .r9
  F := refillBase s
  pLen := pBytes
  qLen := Spec.Dsa.generationQLen pBytes
  lengths := h.lengths
  arenaBound := by have hb := h.scrBound; have hn := h.scratchSize; omega_using [hb, hn]
  frameBound := by
    rw [refillBase_toNat h]; have hb := (s.gpr .rsp).isLt
    unfold VG.Impl.RsaOaep.X86_64.frameBytes; omega_using []
  stackSize := by rw [refillBase_toNat h]; have hl : 568 ≤ (s.gpr .rsp).toNat := h.stackLower; omega_using [hl]
  frameArena := (h.stack_disjoint (d := 192) (n := 296) (by decide) (by simp)).sub_right h.arena_sub
  stackArena := by
    rw [refillBase_below]
    simpa only [off, BitVec.add_zero] using
      (h.stack_disjoint (d := 0) (n := 192) (by decide) (by simp)).sub_right h.arena_sub

/-- The random tape. -/
def randTape {pBytes : Nat} {s : State} (h : RefillABI pBytes s) : GenerationTape (refillGeometry h) where
  ptr := s.gpr .rcx
  bytes := Spec.Rsa.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat
  bound := by rw [bytesAt_length]; exact h.randBound
  size := by rw [bytesAt_length]; exact (s.gpr .r8).isLt
  arena := by rw [bytesAt_length]; exact h.randScr.sub_right h.arena_sub
  frame := by
    rw [bytesAt_length]
    exact (h.stack_disjoint (r := inRand s) (d := 192) (n := 296) (by decide) (by simp)).symm
  stack := by
    rw [bytesAt_length]
    change (inRand s).Disjoint (below (refillBase s) 192)
    rw [refillBase_below]
    simpa only [off, BitVec.add_zero] using (h.stack_disjoint (d := 0) (n := 192) (by decide) (by simp)).symm

/-- The frame words the entry sets. -/
def refillWords (pBytes : Nat) (s : State) : Nat → BitVec 64
  | 3 => off (s.gpr .r9) VG.Impl.Dsa.Generation.Layout.wrappedSeed
  | 4 => off (s.gpr .r9) VG.Impl.Dsa.Generation.Layout.hashes
  | 5 => s.gpr .r9
  | 6 => s.gpr .rdi
  | 7 => s.gpr .rsi
  | 8 => s.gpr .rcx
  | 9 => s.gpr .r8
  | 11 => off (s.gpr .rcx) 0
  | 12 => 0
  | 13 => s.gpr .rcx
  | 15 => s.gpr .r8
  | 17 => BitVec.ofNat 64 pBytes
  | 18 => BitVec.ofNat 64 (Spec.Dsa.generationQLen pBytes)
  | 28 => BitVec.ofNat 64 (Spec.Dsa.generationQLen pBytes)
  | _ => 0

def refillContext {pBytes : Nat} {s : State} (h : RefillABI pBytes s) : GenerationContext where
  geo := refillGeometry h
  seeds := randTape h
  hs := (randTape h).slice 0 0 (Nat.zero_le _)
  rand := randTape h
  saved := refillWords pBytes s
  wrappedSlot := rfl
  hashesSlot := rfl
  baseSlot := rfl
  seedsSlot := rfl
  seedsLengthSlot := by simp [refillWords, randTape, bytesAt_length]
  hSlot := rfl
  hLengthSlot := by simp [refillWords, GenerationTape.slice]
  randSlot := rfl
  randLengthSlot := by simp [refillWords, randTape, bytesAt_length]
  pLenSlot := rfl
  qLenSlot := rfl
  hashLenSlot := rfl

theorem refillOutputPlan {pBytes : Nat} {s : State} (h : RefillABI pBytes s) : OutputPlan (refillContext h) where
  lengthSlot := by
    change s.gpr .rsi = BitVec.ofNat 64 (2 * pBytes + Spec.Dsa.generationQLen pBytes)
    rw [← h.width, ← h.outLength]; simp
  bound := by
    change (s.gpr .rdi).toNat + (2 * pBytes + Spec.Dsa.generationQLen pBytes) ≤ 2 ^ 64
    rw [← h.width, ← h.outLength]; exact h.outBound
  separate := by
    intro r hr
    simp only [GenerationContext.changed, List.mem_cons, List.not_mem_nil, or_false] at hr
    change (⟨s.gpr .rdi, 2 * pBytes + Spec.Dsa.generationQLen pBytes⟩ : Region).Disjoint r
    rw [← h.width, ← h.outLength]
    change (inOut s).Disjoint r
    rcases hr with rfl | rfl | rfl
    · exact h.outScr.sub_right h.arena_sub
    · exact (h.stack_disjoint (d := 192) (n := 296) (by decide) (by simp)).symm
    · change (inOut s).Disjoint (below (refillBase s) 192)
      rw [refillBase_below]
      simpa only [off, BitVec.add_zero] using (h.stack_disjoint (d := 0) (n := 192) (by decide) (by simp)).symm

end VG.Proof.Dsa.X86_64.Generation.Refill

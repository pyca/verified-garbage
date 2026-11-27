module

public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Impl.Bignum.X86.PublicFn
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Bignum.X86.PublicSave
import VerifiedGarbage.Impl.Rsa.X86.CrtValues
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Spec.Weierstrass
public import Init.Data.List.Basic
public import VerifiedGarbage.TCB.X86.State
public import VerifiedGarbage.Proof.Rsa.X86.CvRt.Load
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Proof.Rsa.X86.CvInputs
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
public import VerifiedGarbage.Proof.Weierstrass.PointContract

/-! ### `Rsa.X86.CvBuffers`, which this module and modules that import it used -/

section

/-! ### `Rsa.X86.CvResources`, which this module and modules that import it used -/

section

/-! ### `Rsa.X86.CvABI`, which this module and modules that import it used -/

section

/-! # Resources supplied by the shared CRT-values cdecl contract -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86

def caller (s : State) : CallGeometry :=
  ⟨argumentPointer s 14, (arg s 15).toNat * 8, Spec.Rsa.modulusWords (arg s 7).toNat, arg s⟩

structure ABI (s : State) : Prop where
  stackLow : 52 ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 68 ≤ 2 ^ 32
  rd : s.rd = [(caller s).buffer 6, (caller s).buffer 8, (caller s).buffer 10, (caller s).buffer 12]
  wr : s.wr = [(caller s).buffer 0, (caller s).buffer 2, (caller s).buffer 4,
    ⟨(caller s).base, (caller s).size⟩, ⟨argAddr s 0, 64⟩]
  scratchBound : (arg s 14).toNat + (caller s).size ≤ 2 ^ 32
  belowScratch : (⟨(s.gpr .esp).setWidth 64 - 52#64, 52⟩ : Region).Disjoint
    ⟨(caller s).base, (caller s).size⟩
  argsApart : ∀ r ∈ (caller s).writes, (⟨argAddr s 0, 64⟩ : Region).Disjoint r
  retApart : ∀ r ∈ (caller s).writes, (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r
  inApart : ∀ r ∈ s.rd, ∀ w ∈ (caller s).writes, r.Disjoint w
  outScratch : ∀ r ∈ [(caller s).buffer 0, (caller s).buffer 2, (caller s).buffer 4],
    r.Disjoint ⟨(caller s).base, (caller s).size⟩
  outSeparate : ((caller s).buffer 0).Disjoint ((caller s).buffer 2) ∧
    ((caller s).buffer 0).Disjoint ((caller s).buffer 4) ∧
    ((caller s).buffer 2).Disjoint ((caller s).buffer 4)
  bounds : ∀ i ∈ [0, 2, 4, 6, 8, 10, 12], (arg s i).toNat + (arg s (i + 1)).toNat ≤ 2 ^ 32
  lengths : Spec.Rsa.lenValid (arg s 7).toNat
  pPositive : 1 ≤ (arg s 9).toNat
  pSmall : (arg s 9).toNat < (arg s 7).toNat
  qPositive : 1 ≤ (arg s 11).toNat
  qSmall : (arg s 11).toNat < (arg s 7).toNat
  dpLen : (arg s 1).toNat = (arg s 9).toNat
  qiLen : (arg s 5).toNat = (arg s 9).toNat
  dqLen : (arg s 3).toNat = (arg s 11).toNat
  dPositive : 1 ≤ (arg s 13).toNat
  dBound : (arg s 13).toNat ≤ (arg s 7).toNat
  scratchLength : Spec.Rsa.scratchWords (arg s 7).toNat ≤ (arg s 15).toNat

theorem abi_of {s : State} (h : (Spec.Rsa.crtValuesContract abi 52).pre s) : ABI s := by
  sig_pre [Spec.Rsa.crtValuesContract, Spec.Rsa.crtValuesSig, abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  have rd : s.rd = [(caller s).buffer 6, (caller s).buffer 8, (caller s).buffer 10, (caller s).buffer 12] := by
    dsimp only [caller, CallGeometry.buffer, byteAddr]
    with_reducible assumption
  have lengths : Spec.Rsa.lenValid (arg s 7).toNat := by with_reducible assumption
  have lo := lengths.1
  have hi := lengths.2
  constructor
  all_goals try simp only [rd, CallGeometry.writes, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq]
  all_goals try dsimp only [caller, CallGeometry.buffer, byteAddr]
  all_goals repeat' apply And.intro
  all_goals first | with_reducible assumption | omega |
    exact Region.Disjoint.symm (by with_reducible assumption)

end VG.Proof.Rsa.X86.CrtValues

end

end

/-! # The shared scratch allowance covers the native-word CRT arrays -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.CrtValues

theorem ABI.space {s : State} (a : ABI s) : arr (2 * (caller s).n) nArr ≤ (caller s).size := by
  have h := a.scratchLength
  have lo := a.lengths.1
  simp only [Spec.Rsa.scratchWords] at h
  simp only [caller, Spec.Rsa.modulusWords, arr, S, VG.Impl.Rsa.X86.Keys.hdr, nArr]
  omega_using [h, lo]

theorem ABI.used {s : State} (a : ABI s) : 160 ≤ (caller s).size :=
  Nat.le_trans (Nat.le_add_right _ _) a.space

theorem ABI.width {s : State} (a : ABI s) : 8 ≤ (caller s).n ∧ (caller s).n ≤ 128 ∧
    (arg s 7).toNat ≤ 8 * (caller s).n := by
  have lo := a.lengths.1; have hi := a.lengths.2
  simp only [caller, Spec.Rsa.modulusWords]
  omega_using [lo, hi]

/-- Room below `esp` for the general inverse's call. -/
theorem ABI.room {s : State} (a : ABI s) :
    VG.Proof.Rsa.X86.CrtValuesRt.Room (s.gpr .esp) (caller s).base (caller s).size := by
  refine ⟨a.stackLow, a.stackBound, ?_⟩
  have e : below (s.gpr .esp) 52 = ⟨(s.gpr .esp).setWidth 64 - 52#64, 52⟩ := by
    unfold below
    rw [VG.X86.Taint.sub_setWidth a.stackLow]
  rw [e]
  exact a.belowScratch.symm

/-- The return address lies above the stack the general inverse's call uses. -/
theorem ABI.retAbove {s : State} (a : ABI s) :
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ (below (s.gpr .esp) 52) := by
  have low := a.stackLow
  have high := a.stackBound
  have b : (below (s.gpr .esp) 52).base.toNat = (s.gpr .esp).toNat - 52 := by
    change ((s.gpr .esp - 52#32).setWidth 64).toNat = _
    rw [BitVec.toNat_setWidth, sub_toNat low]
    exact Nat.mod_eq_of_lt (by have := (s.gpr .esp).isLt; omega_using [])
  have e : ((s.gpr .esp).setWidth 64).toNat = (s.gpr .esp).toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := (s.gpr .esp).isLt; omega_using [])
  intro x hx hb
  simp only [Region.Contains, BitVec.toNat_sub] at hx hb
  rw [b] at hb
  rw [e] at hx
  have := x.isLt
  omega_using [low, hx, hb]

theorem ABI.stackArgument {s : State} (a : ABI s) {i : Nat} (hi : i < 16) :
    StackArgument s (caller s).base (caller s).size i := by
  apply stackArgument_of (count := 16) (by have := a.stackBound; omega_using [this]) hi
  · rw [a.rd, a.wr]; simp
  · exact a.argsApart _ (by simp [CallGeometry.writes])

theorem ABI.stack {s : State} (a : ABI s) : StkOk (s.gpr .esp) (caller s).base (caller s).size := by
  apply VG.Proof.Weierstrass.X86.stkOk_of (by decide : 20 ≤ 52) a.stackLow
  · have h := a.scratchBound
    simpa only [caller, argumentPointer, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (Nat.lt_trans (arg s 14).isLt (by decide : 2 ^ 32 < 2 ^ 64))] using h
  · have := a.used; omega_using [this]
  · exact a.belowScratch

theorem ABI.stackApart {s : State} (a : ABI s) {i : Nat} (hi : i < 16)
    {r : Region} (hr : r ∈ (caller s).writes) : (⟨stackAddress s i, 4⟩ : Region).Disjoint r := by
  apply (a.argsApart r hr).sub_left
  have p : stackAddress s i = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) :=
    addr_eq (by have := a.stackBound; omega_using [hi, this])
  have z : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 :=
    addr_eq (by have := a.stackBound; omega_using [this])
  rw [p, z]
  exact Offset.sub _ (by omega_using []) (by omega_using [hi])

theorem ABI.lengths_ok {s : State} (a : ABI s) : VG.Proof.Rsa.X86.CrtValuesRt.Lengths (caller s) :=
  ⟨a.lengths.1, a.lengths.2, rfl, a.pSmall, a.qSmall,
    BitVec.eq_of_toNat_eq a.dpLen, BitVec.eq_of_toNat_eq a.dqLen, BitVec.eq_of_toNat_eq a.qiLen, by
      apply BitVec.eq_of_toNat_eq
      simp only [caller, argumentPointer, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (Nat.lt_trans (arg s 14).isLt (by decide)), Nat.mod_eq_of_lt (arg s 14).isLt]⟩

end VG.Proof.Rsa.X86.CrtValues

end

end

/-! # Public buffer bounds and separation for CRT inputs and outputs -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86

theorem ABI.inputLength {s : State} (a : ABI s) (i : Fin 4) :
    0 < ((caller s).buffer (6 + 2 * i.val)).len ∧
      ((caller s).buffer (6 + 2 * i.val)).len ≤ 8 * (caller s).n := by
  have w := a.width.2.2
  change (arg s 7).toNat ≤ 8 * Spec.Rsa.modulusWords (arg s 7).toNat at w
  have lo := a.lengths.1
  have p := a.pPositive; have q := a.qPositive; have d := a.dPositive
  have ps := a.pSmall; have qs := a.qSmall; have ds := a.dBound
  have cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega_using []
  rcases cases with e | e | e | e <;> rw [e]
  · change 0 < (arg s 7).toNat ∧ (arg s 7).toNat ≤ 8 * Spec.Rsa.modulusWords (arg s 7).toNat
    omega_using [w, lo]
  · change 0 < (arg s 9).toNat ∧ (arg s 9).toNat ≤ 8 * Spec.Rsa.modulusWords (arg s 7).toNat
    omega_using [w, p, ps]
  · change 0 < (arg s 11).toNat ∧ (arg s 11).toNat ≤ 8 * Spec.Rsa.modulusWords (arg s 7).toNat
    omega_using [w, q, qs]
  · change 0 < (arg s 13).toNat ∧ (arg s 13).toNat ≤ 8 * Spec.Rsa.modulusWords (arg s 7).toNat
    omega_using [w, d, ds]

theorem ABI.outputLength {s : State} (a : ABI s) (i : Fin 3) :
    0 < ((caller s).buffer (2 * i.val)).len ∧
      ((caller s).buffer (2 * i.val)).len ≤ 8 * (caller s).n := by
  have w := a.width.2.2
  change (arg s 7).toNat ≤ 8 * Spec.Rsa.modulusWords (arg s 7).toNat at w
  have p := a.pPositive; have q := a.qPositive
  have ps := a.pSmall; have qs := a.qSmall
  have dp := a.dpLen; have dq := a.dqLen; have qi := a.qiLen
  have cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega_using []
  rcases cases with e | e | e <;> rw [e]
  · change 0 < (arg s 1).toNat ∧ (arg s 1).toNat ≤ 8 * Spec.Rsa.modulusWords (arg s 7).toNat
    omega_using [w, p, ps, dp]
  · change 0 < (arg s 3).toNat ∧ (arg s 3).toNat ≤ 8 * Spec.Rsa.modulusWords (arg s 7).toNat
    omega_using [w, q, qs, dq]
  · change 0 < (arg s 5).toNat ∧ (arg s 5).toNat ≤ 8 * Spec.Rsa.modulusWords (arg s 7).toNat
    omega_using [w, p, ps, qi]

theorem ABI.inputMember {s : State} (a : ABI s) (i : Fin 4) :
    (caller s).buffer (6 + 2 * i.val) ∈ s.rd := by
  rw [a.rd]
  have cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega_using []
  rcases cases with e | e | e | e <;> simp [e]

theorem ABI.outputMember {s : State} (i : Fin 3) :
    (caller s).buffer (2 * i.val) ∈ [(caller s).buffer 0, (caller s).buffer 2, (caller s).buffer 4] := by
  have cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega_using []
  rcases cases with e | e | e <;> simp [e]

theorem ABI.inputFit {s : State} (a : ABI s) (i : Fin 4) :
    (arg s (6 + 2 * i.val)).toNat + ((caller s).buffer (6 + 2 * i.val)).len ≤ 2 ^ 32 := by
  change (arg s _).toNat + (arg s _).toNat ≤ 2 ^ 32
  apply a.bounds
  have cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega_using []
  rcases cases with e | e | e | e <;> simp [e]

theorem ABI.outputFit {s : State} (a : ABI s) (i : Fin 3) :
    (arg s (2 * i.val)).toNat + ((caller s).buffer (2 * i.val)).len ≤ 2 ^ 32 := by
  change (arg s _).toNat + (arg s _).toNat ≤ 2 ^ 32
  apply a.bounds
  have cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega_using []
  rcases cases with e | e | e <;> simp [e]

theorem three_outputs {r : Nat → Region}
    (h : (r 0).Disjoint (r 2) ∧ (r 0).Disjoint (r 4) ∧ (r 2).Disjoint (r 4))
    (i j : Fin 3) (ne : i ≠ j) : (r (2 * i.val)).Disjoint (r (2 * j.val)) := by
  have neq : i.val ≠ j.val := fun h => ne (Fin.ext h)
  have casesI : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega_using []
  have casesJ : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega_using []
  rcases casesI with e | e | e <;> rcases casesJ with f | f | f
  all_goals try omega
  all_goals simp only [e, f, Nat.mul_zero, Nat.mul_one, show 2 * 2 = 4 from rfl]
  all_goals first | exact h.1 | exact h.2.1 | exact h.2.2 |
    exact h.1.symm | exact h.2.1.symm | exact h.2.2.symm

theorem ABI.outputSeparate {s : State} (a : ABI s) (i j : Fin 3) (ne : i ≠ j) :
    ((caller s).buffer (2 * i.val)).Disjoint ((caller s).buffer (2 * j.val)) :=
  three_outputs a.outSeparate i j ne

end VG.Proof.Rsa.X86.CrtValues

end

end

/-! # Install CRT caller resources while saving the callee-saved registers -/

-- Formerly `VerifiedGarbage/Proof/Rsa/X86/CvEntry.lean`, which only this module imported.
section

/-! # Establishing the arithmetic workspace while preserving the caller ABI -/

section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.X86.Wp VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Bignum.X86 VG.Proof.Bignum.X86

theorem entry_ok {s : State} {base : Addr} {size : Nat} {ptr : BitVec 32}
    (read : readSrc s (.mem (PublicFn.argument 14)) = some ptr)
    (hb : ptr.setWidth 64 = base) (hf : ptr.toNat + size ≤ 2 ^ 32) (hz : 16 ≤ size)
    (hw : (⟨base, size⟩ : Region) ∈ s.wr) (stk : StkOk (s.gpr .esp) base size) :
    WP isa (.block VG.Impl.Rsa.X86.CrtValues.entry) s fun t =>
      Scr t base size ∧ Saved t.mem (off base) s.gpr PublicFn.savedRegisters ∧
      Keeps [.eax, .edi] s t ∧ Outside base 0 size s.mem t.mem := by
  unfold VG.Impl.Rsa.X86.CrtValues.entry
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

end VG.Proof.Rsa.X86.CrtValues
end

end

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValues
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Bignum.X86 VG.Impl.Rsa.X86.CrtValues

theorem installed_ok {s : State} (a : ABI s) :
    WP isa (.block entry) s fun t => Inputs (caller s) t ∧
      Spill.Saved t.mem (off (caller s).base) s.gpr PublicFn.savedRegisters ∧
      Keeps [.eax, .edi] s t ∧ Outside (caller s).base 0 (caller s).size s.mem t.mem := by
  refine WP.mono (entry_ok (base := (caller s).base) (ptr := arg s 14) (a.stackArgument (by decide : 14 < 16)).readSrc
    rfl a.scratchBound (by have := a.used; omega_using [this]) (by rw [a.wr]; simp) a.stack)
    fun t ⟨sc, saved, k, o⟩ => ?_
  refine ⟨?_, saved, k, o⟩
  have w := a.width
  refine ⟨⟨sc, a.space, by omega_using [w], by omega_using [w]⟩, w.1, w.2.1, ?_, ?_,
    (fun i => (a.inputLength i).1), (fun i => (a.inputLength i).2), a.inputFit, ?_, ?_,
    (fun i => (a.outputLength i).1), (fun i => (a.outputLength i).2), a.outputFit, ?_, ?_, a.outputSeparate,
    by rw [k.1 .esp (by decide)]; exact a.room⟩
  · intro i hi
    exact (CallArgument.mk (a.stackArgument hi) rfl).keep k (by decide) o
  · intro i hi r hr
    rw [show stackAddress t i = stackAddress s i by simp only [stackAddress, k.1 .esp (by decide)]]
    exact a.stackApart hi hr
  · intro i
    rw [k.2.1, k.2.2]
    exact ⟨_, List.mem_append_left _ (a.inputMember i), Region.contains_self _ _⟩
  · exact fun i r hr => a.inApart _ (a.inputMember i) r hr
  · intro i
    rw [k.2.2, a.wr]
    refine ⟨_, ?_, Region.contains_self _ _⟩
    exact List.mem_append_left [⟨(caller s).base, (caller s).size⟩, ⟨argAddr s 0, 64⟩]
      (ABI.outputMember (s := s) i)
  · exact fun i => a.outScratch _ (ABI.outputMember i)

end VG.Proof.Rsa.X86.CrtValues

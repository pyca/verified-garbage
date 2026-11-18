module

public import VerifiedGarbage.Impl.Bignum.X86.PrecomputeFn
public import VerifiedGarbage.Proof.Weierstrass.PointContract
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeInstalled
import VerifiedGarbage.Proof.Bignum.X86.PublicEntryTiming
import VerifiedGarbage.Proof.Bignum.X86.PrecomputeOperation
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.X86.ModulusCheck
import VerifiedGarbage.Proof.Bignum.X86.PublicArgs
import VerifiedGarbage.Proof.Bignum.X86.PrecomputeRt.TimeCompute
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeValid
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeMul
public import VerifiedGarbage.Proof.Bignum.X86.PublicArgumentTiming
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeInputs
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeRt.In
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeExp
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Bignum.X86.PublicReturn
import VerifiedGarbage.Proof.Bignum.X86.PublicSave
import VerifiedGarbage.Proof.Dsa.X86.EntrySave
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Correct
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `Bignum.X86.PrecomputePair`, which only this module used -/

section

/-! # Relate two calls with the same public lengths and pointers -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

structure PrecomputePair (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (s t : State) : Prop where
  left : PrecomputeInputs base bytes len args s
  right : PrecomputeInputs base bytes len args t
  sp : s.gpr .esp = t.gpr .esp

theorem PrecomputePair.agree {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s t : State}
    (H : PrecomputePair base bytes len args s t) : VG.X86.Taint.Agree argumentTaint s t := by
  apply agree_regs (rs := [.edi, .esp])
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · apply BitVec.eq_of_toNat_eq
    exact H.left.scratch.edi_toNat.trans H.right.scratch.edi_toNat.symm
  · exact H.sp

theorem PrecomputePair.keep {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {s t u v : State}
    (H : PrecomputePair base bytes len args s t) {regs : List Reg}
    (Ks : Keeps regs s u) (Kt : Keeps regs t v) (di : .edi ∉ regs) (sp : .esp ∉ regs)
    (Os : Outside base 0 bytes s.mem u.mem) (Ot : Outside base 0 bytes t.mem v.mem) :
    PrecomputePair base bytes len args u v :=
  ⟨H.left.keep Ks di sp Os, H.right.keep Kt di sp Ot, (Ks.1 _ sp).trans (H.sp.trans (Kt.1 _ sp).symm)⟩

end VG.Proof.Bignum.X86

end

end

/-! ### `Bignum.X86.PrecomputeCorrect`, which this module and modules that import it used -/

section

/-! # Functional correctness and cdecl preservation of RSA precomputation -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Bignum.X86 PublicContext

theorem precomputeOperation_ok {s : State} (A : PrecomputeABI s) :
    WP isa PrecomputeFn.code s fun t =>
      (match Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat) with
      | some ws => t.gpr .eax = 1 ∧ Spec.Rsa.wordsAt t.mem (argumentPointer s 0) (arg s 1).toNat = ws
      | none => t.gpr .eax = 0 ∧ Spec.Rsa.wordsAt t.mem (argumentPointer s 0) (arg s 1).toNat =
          List.replicate (arg s 1).toNat 0) ∧ abiPreserved s t := by
  have low : 16 ≤ (arg s 5).toNat * 8 := by have := A.used; omega_using [this]
  have high : (arg s 5).toNat * 8 ≤ 2 ^ 64 := by have := A.scratchBound; omega_using []
  unfold PrecomputeFn.code
  refine WP.seq (WP.mono (precomputeInstalled_ok A) fun u ⟨I, S, K, O⟩ => ?_)
  refine WP.seq (WP.mono (precomputeBody_ok I) fun v ⟨⟨V, F⟩, Kv⟩ => ?_)
  have espu : u.gpr .esp = s.gpr .esp := K.1 _ (by decide)
  have slot : (⟨addr (u.gpr .esp) 8, 4⟩ : Region).Disjoint
      ⟨argumentPointer s 4, (arg s 5).toNat * 8⟩ := (I.stack 1 (by decide)).stack.apart
  rw [espu] at F slot
  have Saved : VG.X86.Spill.Saved v.mem (off (argumentPointer s 4)) s.gpr PublicFn.savedRegisters := by
    intro p hp
    have B : p.2 + 4 ≤ 16 := by
      simp only [PublicFn.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> decide
    refine (F.readW (r := ⟨argumentPointer s 4, 16⟩) (Offset.contains_base _ B (by omega_using [B])) ?_ (by decide)).trans
      (S p hp)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.base_disjoint _ (Nat.le_refl 16) (by omega_using [])
    · exact I.outApart.sub_left (Region.sub_prefix (by omega_using [low]))
    · have := I.room.apart; rw [espu] at this; exact (this.sub_right (Region.sub_prefix (by omega_using [low]))).symm
    · exact (slot.sub_right (Region.sub_prefix (by omega_using [low]))).symm
  have Ret : v.mem.readW ((s.gpr .esp).setWidth 64) 32 =
      s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
    have Start := outside_frame O (by omega_using [])
    simp only [BitVec.add_zero] at Start
    have hlow := A.stackLow
    have hb := A.stackBound
    rw [F.readW (Region.contains_self _ 4) ?_ (by decide)]
    · refine Start.readW (Region.contains_self _ 4) ?_ (by decide)
      intro r hr
      rw [List.mem_singleton.mp hr]
      exact A.retScratch
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact A.retScratch.sub_right (Offset.sub_base _ (by omega_using [low]))
    · rw [← A.outputBytes]; exact A.retOut
    · exact VG.Proof.Bignum.X86.PublicRt.ret_below hlow
    · have e : addr (s.gpr .esp) 8 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 8 := addr_eq (by omega_using [hb])
      rw [e]
      exact Offset.base_disjoint _ (by decide) (by omega_using [])
  refine WP.mono (entryRestore_ok (I.scratch.of_keeps Kv (by decide) (by decide)) low Saved) fun t R => ?_
  refine ⟨?_, publicRestored_abi R ((Kv.1 _ (by decide)).trans (K.1 _ (by decide))) Ret⟩
  rw [R.mem, R.other .eax (by decide), A.preLength]
  have N := scratch_bytes O (by have := A.lengths.2; omega_using []) A.nScratch
  change (match Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt u.mem (argumentPointer s 2) (arg s 3).toNat) with
    | some ws => v.gpr .eax = 1 ∧ Spec.Rsa.wordsAt v.mem (argumentPointer s 0) (2 * Spec.Rsa.modulusWords (arg s 3).toNat) = ws
    | none => v.gpr .eax = 0 ∧ Spec.Rsa.wordsAt v.mem (argumentPointer s 0) (2 * Spec.Rsa.modulusWords (arg s 3).toNat) =
        List.replicate (2 * Spec.Rsa.modulusWords (arg s 3).toNat) 0) at V
  rw [N] at V
  exact V

theorem precomputeCorrect (s : State) (h : (Spec.Rsa.publicPrecomputeContract abi 96).pre s) :
    ∃ trace t, Exec isa PrecomputeFn.code s trace t ∧ abiPreserved s t ∧
      (Spec.Rsa.publicPrecomputeContract abi 96).post s t := by
  obtain ⟨trace, t, E, V, A⟩ := precomputeOperation_ok (precomputeABI_of h)
  refine ⟨trace, t, E, A, ?_⟩
  sig_post [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right]
  exact V

end VG.Proof.Bignum.X86

end

end

/-! ### `Bignum.X86.PrecomputeObservations`, which this module and modules that import it used -/

section

/-! # The shared contract exposes only call geometry and the public modulus -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86
open VG.Proof.Dsa.X86 (argumentPointer)

theorem precomputeArguments {s t : State} (H : (Spec.Rsa.publicPrecomputeContract abi 96).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < 6, arg s i = arg t i := by
  sig_pub [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  constructor
  · assumption
  · intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega_using [hi]
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem precomputeModulusLeak {s t : State} (H : (Spec.Rsa.publicPrecomputeContract abi 96).pub s t) :
    (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat).map (·.toNat) =
      (Spec.Rsa.bytesAt t.mem (argumentPointer t 2) (arg t 3).toNat).map (·.toNat) := by
  sig_pub [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argSlots, argVal, argBytes] at H
  exact H.2.1

theorem precomputeModulusBytes {s t : State} (H : (Spec.Rsa.publicPrecomputeContract abi 96).pub s t) :
    Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat =
      Spec.Rsa.bytesAt t.mem (argumentPointer t 2) (arg t 3).toNat :=
  (List.map_inj_right (fun _ _ h => BitVec.eq_of_toNat_eq h)).mp (precomputeModulusLeak H)

end VG.Proof.Bignum.X86

end

end

/-! ### `Bignum.X86.PrecomputeOperationTiming`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86.PrecomputeArgumentsEq`, which this module and modules that import it used -/

section

/-! # Only six signature arguments determine precomputation resources -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86

theorem PrecomputeInputs.argsEq {base : Addr} {bytes len : Nat} {args other : Nat → BitVec 32} {s : State}
    (H : PrecomputeInputs base bytes len args s) (eq : ∀ i < 6, args i = other i) :
    PrecomputeInputs base bytes len other s := by
  have H0 := eq 0 (by decide)
  have H1 := eq 1 (by decide)
  have H2 := eq 2 (by decide)
  have H3 := eq 3 (by decide)
  have H4 := eq 4 (by decide)
  have H5 := eq 5 (by decide)
  refine ⟨H.scratch, H.lower, H.upper, H.space, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, H.room, H.top,
    by rw [← H4]; exact H.hbase, by rw [← H5]; exact H.hbytes, H.argWrite, by rw [← H2]; exact H.nArg, by rw [← H0]; exact H.outArgs, H.spScratch,
    by rw [← H0]; exact H.spOut⟩
  · intro i hi; rw [← eq i hi]; exact H.stack i hi
  · rw [← H1]; exact H.preLen
  · rw [← H3]; exact H.nLen
  · rw [← H0]; exact H.outFit
  · rw [← H2]; exact H.nFit
  · rw [← H0]; exact H.outWrite
  · rw [← H2]; exact H.nRead
  · rw [← H0]; exact H.outApart
  · rw [← H2]; exact H.nApart

end VG.Proof.Bignum.X86

end

end

/-! ### `Bignum.X86.PrecomputeEntryTiming`, which this module and modules that import it used -/

section

/-! # Saving and restoring registers has a trace fixed by public addresses -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Dsa.X86 VG.Proof.Mont.X86.Dynamic

theorem precomputeEntry_relCT :
    RelCT isa (fun s t => s.gpr .esp = t.gpr .esp ∧ stackValue s 4 = stackValue t 4 ∧
      readSrc s (.mem (PublicFn.argument 4)) = some (stackValue s 4) ∧
      readSrc t (.mem (PublicFn.argument 4)) = some (stackValue t 4))
      (.block PrecomputeFn.entry) (VG.X86.Taint.Agree argumentTaint) := by
  unfold PrecomputeFn.entry
  rw [List.append_assoc]
  apply VG.RelCT.block_append
  exact VG.RelCT.seq (scratchArgument_relCT 4)
    (checkedProgramChange (τ' := { argumentTaint with regs := .ofList [.esp, .edi, .eax] })
      (hint := .block []) (by kernel_rfl) (by kernel_rfl))

end VG.Proof.Bignum.X86

end

end

/-! ### `Bignum.X86.PrecomputeBodyTiming`, which this module and modules that import it used -/

section

/-! ### `Bignum.X86.PrecomputeFailureTiming`, which this module and modules that import it used -/

section

/-! # Invalid public keys clear a public-length output with a fixed trace -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Dsa.X86

theorem precomputeFailure_relCT (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) :
    RelCT isa (PrecomputePair base bytes len args) PrecomputeFn.failure (fun _ _ => True) := by
  have Zero : RelCT isa (VG.X86.Taint.Agree loadTaint) (.block [.alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx),
        .alu .add .ecx (.reg .ecx), .mov .eax (.imm 0)])
      (VG.X86.Taint.Agree loadTaint) := checkedProgramChange (hint := .block []) rfl rfl
  have Head := VG.RelCT.block_append (VG.RelCT.seq (loadArguments_relCT 0 1 (args 0) (args 1)) Zero)
  have Loop : RelCT isa (VG.X86.Taint.Agree loadTaint) (.loop (.block PublicFn.clearStep) .ne)
      (fun _ _ => True) := by
    apply RelCT.taint (A := taint) loadTaint (fun _ _ h => h)
      (hc := VG.Taint.hintOf taint loadTaint (.loop (.block PublicFn.clearStep) .ne))
    rfl
  apply (VG.RelCT.seq Head Loop).mono
  · intro s t H
    exact ⟨H.agree, (H.left.stack 0 (by decide)).readSrc, (H.right.stack 0 (by decide)).readSrc,
      (H.left.stack 1 (by decide)).readSrc, (H.right.stack 1 (by decide)).readSrc⟩
  · exact fun _ _ h => h

end VG.Proof.Bignum.X86

end

end

/-! ### `Bignum.X86.PrecomputeValidTiming`, which this module and modules that import it used -/

section

/-! # The precomputation of a valid modulus leaks only the public lengths and pointers

Argument 1's overwrite is checked by the taint analysis; the computation
after it is related on states whose permissions are narrowed to `pre` and
the working space (`compute_relCT`), and the runs from the states
themselves leak the same traces (`relCT_narrow`).
-/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Proof.Bignum.X86.PrecomputeRt
open VG.Proof.Bignum.X86.PublicRt (wb Both)
open VG.Proof.Bignum.X86.PublicContext (pcArgs pcSetWidth_ok pcCompute_ok pcBytesAt_frame)

def PrecomputeValidPair (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (s t : State) : Prop :=
  PrecomputePair base bytes len args s t ∧
    Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len = true ∧
    Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (byteAddr (args 2)) len)) len = true ∧
    Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len = Spec.Rsa.bytesAt t.mem (byteAddr (args 2)) len

section
variable {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- The permissions of `compute`'s narrowed runs: everything readable, `pre` and the working space
writable. -/
abbrev pcNarrowW (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) : List Region :=
  [⟨byteAddr (args 0), 2 * wb len⟩, ⟨base, bytes⟩]

theorem narrow_pcIn {s : State} (h : PcIn base bytes len args s) :
    PcIn base bytes len args (s.withRegions (s.rd ++ s.wr) (pcNarrowW base bytes len args)) := by
  refine ⟨⟨h.scratch.edi, by simp, h.scratch.nowrap, h.scratch.stk⟩, h.lower, h.upper, h.space,
    fun i hi => ⟨⟨?_, (h.stack i hi).stack.apart⟩, (h.stack i hi).value⟩, h.wLen, h.nLen, h.hbase, h.hbytes,
    h.outFit, h.nFit, ⟨_, List.mem_cons_self .., Region.contains_self _ _⟩, ?_, h.outApart, h.nApart, h.outArgs⟩
  · obtain ⟨r, hr, hc⟩ := (h.stack i hi).stack.read
    exact ⟨r, List.mem_append_left _ hr, hc⟩
  · obtain ⟨r, hr, hc⟩ := h.nRead; exact ⟨r, List.mem_append_left _ hr, hc⟩

/-- What the runs of `compute` from the states themselves need. -/
def PcAt (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (s : State) : Prop :=
  PcIn base bytes len args s ∧ CallRoom (s.gpr .esp) base bytes ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
    s.gpr .esp = sp ∧
    Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len = true ∧
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 28⟩ ⟨byteAddr (args 0), 2 * wb len⟩ ∧
    Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 28⟩ ⟨base, bytes⟩

theorem compute_narrow_relCT (sp : BitVec 32) :
    RelCT isa (Both (PcAt base bytes len args sp)) PrecomputeFn.compute fun _ _ => True := by
  have narrow : ∀ {s : State}, PcAt base bytes len args sp s →
      CIn base bytes len args sp (s.withRegions (s.rd ++ s.wr) (pcNarrowW base bytes len args)) := by
    intro s ⟨h, R, top, e, V, Do, Ds⟩
    refine ⟨narrow_pcIn h, R, top, ⟨top, fun r hr => ?_⟩, e, V⟩
    simp only [State.withRegions, pcNarrowW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Do
    · exact Ds
  refine VG.Proof.Bignum.X86.PublicRt.relCT_narrow (Pn := Both (CIn base bytes len args sp))
    (fun s => s.rd ++ s.wr) (fun _ => pcNarrowW base bytes len args) (fun s₁ s₂ ⟨S₁, S₂⟩ => ?_) (compute_relCT sp)
  have cov : ∀ {s : State}, PcAt base bytes len args sp s → Covers (pcNarrowW base bytes len args) s.wr := by
    intro s S
    rintro a n ⟨r, hr, hc⟩
    simp only [pcNarrowW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Covers.one S.1.outWrite a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact ⟨_, S.1.scratch.wr, hc⟩
  have wp : ∀ {s : State}, PcAt base bytes len args sp s →
      ∃ F, WP isa PrecomputeFn.compute (s.withRegions (s.rd ++ s.wr) (pcNarrowW base bytes len args)) F := by
    intro s S
    obtain ⟨h, R, top, _, _, V⟩ := narrow S
    exact ⟨_, pcCompute_ok h R top V⟩
  exact ⟨Covers.append_left (Covers.refl _) (Covers.right (cov S₁)), cov S₁,
    Covers.append_left (Covers.refl _) (Covers.right (cov S₂)), cov S₂, wp S₁, wp S₂, narrow S₁, narrow S₂⟩

theorem pcAt_of {s u : State} (h : PrecomputeInputs base bytes len args s)
    (valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len = true)
    (P : PcIn base bytes len (pcArgs len args) u) (F : Frame [⟨addr (s.gpr .esp) 8, 4⟩] s.mem u.mem)
    (K : Keeps [.eax] s u) : PcAt base bytes len (pcArgs len args) (s.gpr .esp) u := by
  have esp : u.gpr .esp = s.gpr .esp := K.1 _ (by decide)
  have a0 : pcArgs len args 0 = args 0 := by simp [pcArgs]
  have a2 : pcArgs len args 2 = args 2 := by simp [pcArgs]
  have W : 2 * wb len = 16 * Spec.Rsa.modulusWords len := by simp only [wb]; omega_using []
  have N : Spec.Rsa.bytesAt u.mem (byteAddr (args 2)) len = Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len := by
    refine pcBytesAt_frame F (fun r hr => ?_) (by have := h.upper; omega_using [this])
    rw [List.mem_singleton.mp hr]
    have := h.nArg
    simpa only [stackAddress] using this
  refine ⟨P, by rw [esp]; exact h.room, by rw [esp]; exact h.top, esp, by rw [a2, N]; exact valid,
    by rw [esp, a0, W]; exact h.spOut, by rw [esp]; exact h.spScratch⟩

end

theorem precomputeValid_relCT (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) :
    RelCT isa (PrecomputeValidPair base bytes len args) PrecomputeFn.valid (fun _ _ => True) := by
  intro s t tr ur sf tf H E F
  unfold PrecomputeFn.valid at E F
  cases E with
  | @seq _ _ _ u _ _ _ E1 E2 =>
    cases F with
    | @seq _ _ _ v _ _ _ F1 F2 =>
      have CT : RelCT isa (VG.X86.Taint.Agree argumentTaint) (.block PrecomputeFn.setWidth)
          (VG.X86.Taint.Agree argumentTaint) := checkedProgramChange (hint := .block []) rfl rfl
      have T1 := (CT _ _ _ _ _ _ H.1.agree E1 F1).1
      obtain ⟨Pu, Fu, Ku⟩ := wp_result (pcSetWidth_ok H.1.left) E1
      obtain ⟨Pv, Fv, Kv⟩ := wp_result (pcSetWidth_ok H.1.right) F1
      have Cu := pcAt_of H.1.left H.2.1 Pu Fu Ku
      have Cv := pcAt_of H.1.right H.2.2.1 Pv Fv Kv
      rw [← H.1.sp] at Cv
      have T2 := (compute_narrow_relCT (s.gpr .esp) _ _ _ _ _ _ ⟨Cu, Cv⟩ E2 F2).1
      exact ⟨by rw [T1, T2], trivial⟩

end VG.Proof.Bignum.X86

end

end

/-! ### `Bignum.X86.PrecomputeModulusTiming`, which this module and modules that import it used -/

section

/-! # Loading and validating the public modulus preserves all call inputs -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86

theorem precomputeModulus_ok {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
    (H : PrecomputeInputs base bytes len args s) :
    WP isa (.seq (.block PublicFn.modulusArgs) (.block modulusCheck)) s fun t =>
      t.zf = some (Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len) ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  refine WP.seq (WP.mono (argumentPair_ok (c := BitVec.ofNat 32 len) (by decide) (by decide)
    (H.stack 2 (by decide)).readSrc (by rw [← H.nLen]; exact (H.stack 3 (by decide)).readSrc))
    fun u ⟨P, C, M, K⟩ => ?_)
  refine WP.mono (modulusCheck_ok u H.lower H.upper (by rw [P]; exact H.nFit)
    (by rw [P, K.2.1, K.2.2]; exact H.nRead) C) fun t ⟨Z, Mt, Kt⟩ => ?_
  rw [P, M] at Z
  exact ⟨Z, Mt.trans M, (K.mono (by decide)).trans (Kt.mono (by decide))⟩

theorem precomputeModulus_relCT (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) :
    RelCT isa (PrecomputePair base bytes len args) (.seq (.block PublicFn.modulusArgs) (.block modulusCheck))
      (fun _ _ => True) := by
  have Check : RelCT isa (VG.X86.Taint.Agree loadTaint) (.block modulusCheck) (fun _ _ => True) := by
    apply RelCT.taint (A := taint) loadTaint (fun _ _ h => h) (hc := .block [])
    rfl
  apply (VG.RelCT.seq (loadArguments_relCT 2 3 (args 2) (args 3)) Check).mono
  · intro s t H
    exact ⟨H.agree, (H.left.stack 2 (by decide)).readSrc, (H.right.stack 2 (by decide)).readSrc,
      (H.left.stack 3 (by decide)).readSrc, (H.right.stack 3 (by decide)).readSrc⟩
  · exact fun _ _ h => h

end VG.Proof.Bignum.X86

end

end

/-! # Checked public RSA branches only on public key validation -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86

theorem precomputeBody_relCT (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) :
    RelCT isa (fun s t => PrecomputePair base bytes len args s t ∧
      Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len = Spec.Rsa.bytesAt t.mem (byteAddr (args 2)) len)
      PrecomputeFn.body (fun _ _ => True) := by
  let R := fun s t => PrecomputePair base bytes len args s t ∧
    ∃ b : Bool, s.zf = some b ∧ t.zf = some b ∧ (b = true → PrecomputeValidPair base bytes len args s t)
  have Branch : RelCT isa R (.ite .e PrecomputeFn.valid PrecomputeFn.failure) (fun _ _ => True) := by
    apply VG.RelCT.ite (M := isa) (c := .e) (P := R)
    · intro s t ⟨_, b, Zs, Zt, _⟩
      exact Zs.trans Zt.symm
    · intro s t tr ur sf tf ⟨H, Z⟩ E F
      obtain ⟨b, Zs, _, Valid⟩ := H.2
      have B : b = true := by
        change s.zf = some true at Z
        exact Option.some.inj (Zs.symm.trans Z)
      exact ⟨(precomputeValid_relCT base bytes len args _ _ _ _ _ _ (Valid B) E F).1, trivial⟩
    · exact (precomputeFailure_relCT base bytes len args).mono (fun _ _ H => H.1.1) (fun _ _ h => h)
  apply VG.RelCT.assoc
  intro s t tr ur sf tf ⟨H, N⟩ E F
  cases E with
  | @seq _ _ _ u _ _ _ E1 E2 =>
    cases F with
    | @seq _ _ _ v _ _ _ F1 F2 =>
      have T1 := (precomputeModulus_relCT base bytes len args _ _ _ _ _ _ H E1 F1).1
      obtain ⟨Zs, Ms, Ks⟩ := wp_result (precomputeModulus_ok H.left) E1
      obtain ⟨Zt, Mt, Kt⟩ := wp_result (precomputeModulus_ok H.right) F1
      have Next := H.keep Ks Kt (by decide) (by decide)
        (by rw [Ms]; exact Outside.refl _ _ _ _) (by rw [Mt]; exact Outside.refl _ _ _ _)
      have Relation : R u v := by
        refine ⟨Next, _, Zs, ?_, ?_⟩
        · rw [N]; exact Zt
        · intro V
          refine ⟨Next, ?_, ?_, ?_⟩
          · rw [Ms]; exact V
          · rw [Mt, ← N]; exact V
          · rw [Ms,Mt];exact N
      have T2 := (Branch _ _ _ _ _ _ Relation E2 F2).1
      exact ⟨by rw [T1, T2], trivial⟩

end VG.Proof.Bignum.X86

end

end

/-! # The cdecl checked-public operation leaks only its public key and geometry -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Dsa.X86 (argumentPointer wp_result)

theorem precomputeOperation_trace {s t : State} (A : PrecomputeABI s) (B : PrecomputeABI t)
    (args : ∀ i < 6, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp)
    (N : Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat =
      Spec.Rsa.bytesAt t.mem (argumentPointer t 2) (arg t 3).toNat)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa PrecomputeFn.code s tr sf) (F : Exec isa PrecomputeFn.code t ur tf) : tr = ur := by
  have A2 := args 2 (by decide)
  have A3 := args 3 (by decide)
  have A4 := args 4 (by decide)
  have A5 := args 5 (by decide)
  cases E with
  | @seq _ _ _ u _ _ _ E1 Erest =>
    cases F with
    | @seq _ _ _ v _ _ _ F1 Frest =>
      have T1 := (precomputeEntry_relCT _ _ _ _ _ _
        ⟨SP, A4, (A.stackArgument (by decide : 4 < 6)).readSrc,
          (B.stackArgument (by decide : 4 < 6)).readSrc⟩ E1 F1).1
      obtain ⟨Is, _, Ks, Os⟩ := wp_result (precomputeInstalled_ok A) E1
      obtain ⟨It, _, Kt, Ot⟩ := wp_result (precomputeInstalled_ok B) F1
      have Iv : PrecomputeInputs (argumentPointer s 4) ((arg s 5).toNat * 8) (arg s 3).toNat (arg s) v := by
        have J := It.argsEq (fun i hi => (args i hi).symm)
        simpa only [argumentPointer, ← A4, ← A5, ← A3] using J
      have Ov : VG.Proof.Mont.Outside (argumentPointer s 4) 0 ((arg s 5).toNat * 8) t.mem v.mem := by
        simpa only [argumentPointer, ← A4, ← A5] using Ot
      have Pair : PrecomputePair (argumentPointer s 4) ((arg s 5).toNat * 8) (arg s 3).toNat (arg s) u v :=
        ⟨Is, Iv, (Ks.1 _ (by decide)).trans (SP.trans (Kt.1 _ (by decide)).symm)⟩
      have Ns := scratch_bytes Os (by have := A.lengths.2; omega_using []) Is.nApart
      have Nt := scratch_bytes Ov (by have := A.lengths.2; omega_using []) Iv.nApart
      have NN : Spec.Rsa.bytesAt u.mem (byteAddr (arg s 2)) (arg s 3).toNat =
          Spec.Rsa.bytesAt v.mem (byteAddr (arg s 2)) (arg s 3).toNat := by
        rw [Ns, Nt]
        simpa only [argumentPointer, byteAddr, ← A2, ← A3] using N
      cases Erest with
      | @seq _ _ _ w _ _ _ E2 E3 =>
        cases Frest with
        | @seq _ _ _ z _ _ _ F2 F3 =>
          have T2 := (precomputeBody_relCT _ _ _ _ _ _ _ _ _ _ ⟨Pair, NN⟩ E2 F2).1
          obtain ⟨_, Ksu⟩ := wp_result (PublicContext.precomputeBody_ok Is) E2
          obtain ⟨_, Ktv⟩ := wp_result (PublicContext.precomputeBody_ok Iv) F2
          have Agree : VG.X86.Taint.Agree (VG.Proof.Mont.X86.Dynamic.workspaceTaint false) w z :=
            agree_regs (by
              intro r hr
              obtain rfl := List.mem_singleton.mp hr
              rw [Ksu.1 _ (by decide), Ktv.1 _ (by decide)]
              exact Pair.agree.rf.1 _ (by decide))
          have T3 := (publicRestore_relCT _ _ _ _ _ _ Agree E3 F3).1
          rw [T1, T2, T3]

end VG.Proof.Bignum.X86

end

end

/-! # Complete i686 certificate for public RSA precomputation -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86

theorem precomputeConstantTime : ConstantTime isa (Spec.Rsa.publicPrecomputeContract abi 96).pre
    (Spec.Rsa.publicPrecomputeContract abi 96).pub PrecomputeFn.code := by
  intro s t tr ur sf tf S T H E F
  have Args := precomputeArguments H
  exact precomputeOperation_trace (precomputeABI_of S) (precomputeABI_of T) Args.2 Args.1
    (precomputeModulusBytes H) E F

/-- Disjoint buffers for a 512-bit modulus, rejected because its bytes are zero. -/
def precomputeSatState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 16 else if a = 0x20008 then 16 else if a = 0x2000d then 32
    else if a = 0x20010 then 64 else if a = 0x20015 then 128 else if a = 0x20018 then 128 else 0
  rd := [⟨0x2000, 64⟩]
  wr := [⟨0x1000, 128⟩, ⟨0x8000, 1024⟩, ⟨0x20004, 24⟩]

theorem precomputeSatisfiable : ∃ s, (Spec.Rsa.publicPrecomputeContract abi 96).pre s := by
  have a0 : arg precomputeSatState 0 = 4096 := by decide
  have a1 : arg precomputeSatState 1 = 16 := by decide
  have a2 : arg precomputeSatState 2 = 8192 := by decide
  have a3 : arg precomputeSatState 3 = 64 := by decide
  have a4 : arg precomputeSatState 4 = 32768 := by decide
  have a5 : arg precomputeSatState 5 = 128 := by decide
  have e : argAddr precomputeSatState 0 = 0x20004 := by decide
  have esp : precomputeSatState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, e, esp, precomputeSatState, Spec.Rsa.lenValid,
      Spec.Rsa.publicScratchWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords] using precomputeSatState

theorem precompute_verified : Verified target PrecomputeFn.code (Spec.Rsa.publicPrecomputeContract abi 96) :=
  ⟨precomputeCorrect, precomputeConstantTime, precomputeSatisfiable⟩

end VG.Proof.Bignum.X86

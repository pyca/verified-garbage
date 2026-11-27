module

import VerifiedGarbage.Proof.Dsa.X86.RandomSignCorrect
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyPublicCall
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverStackWord
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverRegions
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Recover
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.X86.RandomContext
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `RsaPkcs1Sig.X86.RecoverFnInput`, which the modules that import this one used -/

section

/-! # Entry state and preserved saved-register words for checked private RSA -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Proof.Rsa.X86.PrivChecked VG.Impl.RsaPkcs1Sig.X86.Verify VG.Proof.Bignum.X86
open VG.Proof.Dsa.X86 (allocated freed allocated_esp freed_esp)

def savedRegisters : List Reg := [.ebx, .ebp, .esi, .edi]
def entered (s : State) : State := allocated VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes (pushed savedRegisters s)

structure FnInput (g : Geometry) (bs : Fin 4 → List Byte) (s : State) : Prop where
  stackFit : recoverStack ≤ (s.gpr .esp).toNat
  context : Context g bs (entered s)
  returnSeparate : ∀ r ∈ bodyWrites g, (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r

theorem FnInput.savedSp {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : FnInput g bs s) :
    (pushed savedRegisters s).gpr .esp = g.stack + BitVec.ofNat 32 VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes := by
  rw [← h.context.sp]
  exact (BitVec.sub_add_cancel _ _).symm

/-- The frame reserved below the saved registers is `innerRegion`. -/
theorem FnInput.innerBelow {g : Geometry} {bs : Fin 4 → List Byte} {s : State} (h : FnInput g bs s) :
    below ((pushed savedRegisters s).gpr .esp) VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes = g.innerRegion := by
  show (⟨((pushed savedRegisters s).gpr .esp - BitVec.ofNat 32 VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes).setWidth 64, VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes⟩ : Region) =
    ⟨byteAddr g.stack, VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes⟩
  rw [← allocated_esp, show (allocated VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes (pushed savedRegisters s)).gpr .esp = g.stack from h.context.sp]
  rfl

/-- The saved registers' words are `savedRegion`. -/
theorem FnInput.savedBelow {g : Geometry} {bs : Fin 4 → List Byte} {s : State} (h : FnInput g bs s) :
    below (s.gpr .esp) (4 * savedRegisters.length) = g.savedRegion := by
  show (⟨(s.gpr .esp - BitVec.ofNat 32 (4 * savedRegisters.length)).setWidth 64, 4 * savedRegisters.length⟩ :
    Region) = ⟨byteAddr g.stack + BitVec.ofNat 64 VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes, 16⟩
  rw [← pushed_esp, h.savedSp]
  exact congrArg (fun a => Region.mk a 16) (h.context.valid.offsetAddr (by decide))

theorem savedRegion_separate {g : Geometry} (h : g.Valid) :
    ∀ r ∈ bodyWrites g, g.savedRegion.Disjoint r := by
  intro r hr
  simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h.innerSaved.symm
  · unfold Geometry.savedRegion Geometry.calleeRegion VG.X86.below
    rw [h.stackBase, Offset.add_add]
    exact Offset.disjoint_base _ (by decide : 100 ≤ 100 + VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes)
      (by decide : 100 + VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 16 ≤ 2 ^ 64)
  · exact h.stackOutput.sub_left h.savedSub
  · exact h.stackWorkspace.sub_left h.savedSub

theorem FnInput.savedWord {g : Geometry} {bs : Fin 4 → List Byte} {s t : State}
    (h : FnInput g bs s) (frame : Frame (bodyWrites g) (entered s).mem t.mem)
    (i : Nat) (hi : i < 4) :
    t.mem.readW (((pushed savedRegisters s).gpr .esp + BitVec.ofNat 32 (4 * i)).setWidth 64) 32 =
      s.gpr (savedRegisters[3 - i]'(by simp only [savedRegisters, List.length_cons, List.length_nil]; omega_using [])) := by
  have initial := pushed_word (s := s) (rs := savedRegisters) (by decide)
    (by have := h.stackFit; change 16 ≤ _; unfold recoverStack at this; omega_using [this]) hi
  have address : ((pushed savedRegisters s).gpr .esp + BitVec.ofNat 32 (4 * i)).setWidth 64 =
      g.savedRegion.base + BitVec.ofNat 64 (4 * i) := by
    rw [h.savedSp, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    change byteAddr (g.stack + BitVec.ofNat 32 (VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 4 * i)) = _
    rw [h.context.valid.offsetAddr (by unfold VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes; omega_using [hi])]
    exact (Offset.add_add _ _ _).symm
  rw [address] at initial ⊢
  exact (frame.readW (r := g.savedRegion)
    (Offset.contains_base _ (by omega_using [hi] : 4 * i + 32 / 8 ≤ 16) (by omega_using [hi]))
    (savedRegion_separate h.context.valid) (by decide)).trans initial
end VG.Proof.RsaPkcs1Sig.X86.Rcv

end

end

/-! ### `RsaPkcs1Sig.X86.RecoverPublicCall`, which this module and modules that import it used -/

section

/-! ### `RsaPkcs1Sig.X86.RecoverPublicPre`, which this module and modules that import it used -/

section

/-! ### `RsaPkcs1Sig.X86.RecoverLocalArgument`, which only this module used -/

section

/-! # Passing a pointer into the wrapper's local frame as a cdecl argument -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.X86.Wp VG.Impl.RsaPkcs1Sig.X86.Verify VG.Proof.Bignum.X86 VG.Proof.Mont.X86

theorem localArgument_ok (s : State) {g : Geometry} {bs : Fin 4 → List Byte}
    (h : Context g bs s) (d : Nat) {j : Nat} (hj : j < 10) :
    WP isa (.block (localArgument d j)) s fun t =>
      Context g bs t ∧
      t.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 (4 * j)) (g.stack + BitVec.ofNat 32 d) ∧
      Frame [⟨byteAddr g.stack + BitVec.ofNat 64 (4 * j), 4⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold localArgument stackAt
  refine wp_movS rfl fun a A _ => ?_
  refine wp_addS rfl fun b B _ => ?_
  refine wp_stm (B := s.gpr .esp)
    (by rw [B.other .esp (by decide), A.other .esp (by decide)])
    (by rw [B.wr, A.wr, h.address (by omega_using [hj])]; exact h.inner.write (by simp only [VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes]; omega_using [hj]))
    fun t T => WP.block_nil ?_
  have M : t.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 (4 * j)) (g.stack + BitVec.ofNat 32 d) := by
    rw [T.mem, B.gpr, A.gpr, B.mem, A.mem, h.address (by omega_using [hj]), h.sp]
  have K : Keeps [.eax] s t := A.keeps.trans (B.keeps.trans (T.keeps _))
  have F : Frame [⟨byteAddr g.stack + BitVec.ofNat 64 (4 * j), 4⟩] s.mem t.mem := by
    rw [M]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨h.after (F.sub ?_) K (K.1 .esp (by decide)), M, F, K⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨g.innerRegion, by simp [bodyWrites], Offset.sub_base _ (by simp only [VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes]; omega_using [hj])⟩

theorem outgoing_word_preserved {g : Geometry} {m m' : Mem} {i j : Nat}
    (hi : i < 10) (hj : j < 10) (hne : i ≠ j)
    (f : Frame [⟨byteAddr g.stack + BitVec.ofNat 64 (4 * j), 4⟩] m m') :
    m'.readW (byteAddr g.stack + BitVec.ofNat 64 (4 * i)) 32 =
      m.readW (byteAddr g.stack + BitVec.ofNat 64 (4 * i)) 32 := by
  apply f.readW (r := ⟨byteAddr g.stack + BitVec.ofNat 64 (4 * i), 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact Offset.disjoint _ (by omega_using [hne]) (by omega_using [hi]) (by omega_using [hj])

end VG.Proof.RsaPkcs1Sig.X86.Rcv

end

end

/-! # The precomputed public call is safe after the signature-length check -/

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/RecoverArguments.lean`, which only this module imported.
section

/-! # Installing successive cdecl arguments preserves every earlier word -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86

def Arguments (g : Geometry) (values : Nat → BitVec 32) (n : Nat) (s : State) : Prop :=
  ∀ j < n, s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 (4 * j)) 32 = values j

theorem Arguments.append {g : Geometry} {values : Nat → BitVec 32} {n : Nat} {s t : State}
    (h : Arguments g values n s) (hn : n < 10)
    (M : t.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 (4 * n)) (values n))
    (F : Frame [⟨byteAddr g.stack + BitVec.ofNat 64 (4 * n), 4⟩] s.mem t.mem) :
    Arguments g values (n + 1) t := by
  intro j hj
  by_cases same : j = n
  · subst j; rw [M, Mem.readW_writeW_self32]
  · rw [outgoing_word_preserved (by omega_using [hn, hj]) hn same F]
    exact h j (by omega_using [hj, same])

theorem slotFrame_outgoing {g : Geometry} {s t : State} {j : Nat} (hj : j < 10)
    (F : Frame [⟨byteAddr g.stack + BitVec.ofNat 64 (4 * j), 4⟩] s.mem t.mem) :
    Frame [⟨byteAddr g.stack, 40⟩] s.mem t.mem := F.sub (by
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by omega_using [hj])⟩)

theorem prepareArgument_ok {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    {values : Nat → BitVec 32} {n : Nat} {code : List Instr}
    (a : Arguments g values n s) (hn : n < 10)
    (w : WP isa (.block code) s fun t => Context g bs t ∧
      t.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 (4 * n)) (values n) ∧
      Frame [⟨byteAddr g.stack + BitVec.ofNat 64 (4 * n), 4⟩] s.mem t.mem ∧ Keeps [.eax] s t) :
    WP isa (.block code) s fun t => Context g bs t ∧ Arguments g values (n + 1) t ∧
      Frame [⟨byteAddr g.stack, 40⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  refine WP.mono w ?_
  rintro t ⟨h, M, F, K⟩
  exact ⟨h, a.append hn M F, slotFrame_outgoing hn F, K⟩

end VG.Proof.RsaPkcs1Sig.X86.Rcv
end

end

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/RecoverCallArgs.lean`, which only this module imported.
section

/-! # All ten arguments of precomputed public RSA verification -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Sig.X86.Verify (em1Offset copyArgument localArgument)
open VG.Impl.RsaPkcs1Sig.X86.Recover (pubArgs)

def publicArgument (g : Geometry) (j : Nat) : BitVec 32 :=
  match j with
  | 0 => g.em1 | 1 => BitVec.ofNat 32 g.length
  | 2 => g.sources 3 | 3 => BitVec.ofNat 32 g.preLength
  | 4 => g.sources 1 | 5 => BitVec.ofNat 32 g.exponentLength
  | 6 => g.sources 2 | 7 => BitVec.ofNat 32 g.length
  | 8 => g.workspace | _ => BitVec.ofNat 32 g.scratchLength

private def inputSlot (j : Nat) : Nat :=
  match j with
  | 1 => 3 | 2 => 11 | 3 => 12 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 3 | 8 => 9 | _ => 10

theorem pubArgs_ok {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) :
    WP isa (.block pubArgs) s fun t => Context g bs t ∧ Arguments g (publicArgument g) 10 t ∧
      Frame [⟨byteAddr g.stack, 40⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  have first : WP isa (.block (localArgument em1Offset 0)) s fun t =>
      Context g bs t ∧ Arguments g (publicArgument g) 1 t ∧
      Frame [⟨byteAddr g.stack, 40⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
    apply prepareArgument_ok (bs := bs) (n := 0) (by intro j hj; omega) (by decide)
    exact localArgument_ok s h em1Offset (by decide)
  have next {u : State} (hu : Context g bs u) {j : Nat} (hj : 1 ≤ j) (hj' : j < 10)
      (a : Arguments g (publicArgument g) j u) :
      WP isa (.block (copyArgument (inputSlot j) j)) u fun t =>
        Context g bs t ∧ Arguments g (publicArgument g) (j + 1) t ∧
        Frame [⟨byteAddr g.stack, 40⟩] u.mem t.mem ∧ Keeps [.eax] u t := by
    have inputBound : inputSlot j < 13 := by
      rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 by omega_using [hj, hj']) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have value : g.argument (inputSlot j) = publicArgument g j := by
      rcases (show j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 by omega_using [hj, hj']) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    apply prepareArgument_ok (bs := bs) a hj'
    refine WP.mono (copyArgument_ok u hu inputBound hj') ?_
    rintro t ⟨ht, M, F, K⟩
    exact ⟨ht, by rw [value] at M; exact M, F, K⟩
  have copyMany (n : Nat) (hn : n ≤ 9) {u : State} (hu : Context g bs u)
      (a : Arguments g (publicArgument g) 1 u) :
      WP isa (.block ((List.range n).flatMap fun j => copyArgument (inputSlot (j + 1)) (j + 1))) u
        fun t => Context g bs t ∧ Arguments g (publicArgument g) (n + 1) t ∧
          Frame [⟨byteAddr g.stack, 40⟩] u.mem t.mem ∧ Keeps [.eax] u t := by
    induction n generalizing u with
    | zero => exact WP.block_nil ⟨hu, a, Frame.refl _ _, Keeps.refl _ _⟩
    | succ n ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
      refine WP.mono (ih (by omega_using [hn]) hu a) ?_
      rintro v ⟨hv, av, F, K⟩
      refine WP.mono (next hv (by omega_using []) (by omega_using [hn]) av) ?_
      rintro t ⟨ht, args, Ft, Kt⟩
      exact ⟨ht, args, F.trans Ft, K.trans Kt⟩
  have code : pubArgs = localArgument em1Offset 0 ++
      (List.range 9).flatMap (fun j => copyArgument (inputSlot (j + 1)) (j + 1)) := rfl
  rw [code, WP.block_append_iff]
  refine WP.mono first ?_
  rintro u ⟨hu, args, F, K⟩
  refine WP.mono (copyMany 9 (by decide) hu args) ?_
  rintro t ⟨ht, argsT, Ft, Kt⟩
  exact ⟨ht, argsT, F.trans Ft, K.trans Kt⟩

end VG.Proof.RsaPkcs1Sig.X86.Rcv
end

end

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Proof.Bignum.X86

def publicRd (g : Geometry) : List Region := [g.sourceRegion 3, g.sourceRegion 1, g.sourceRegion 2]
def publicWr (g : Geometry) : List Region :=
  [⟨byteAddr g.em1, g.length⟩, g.workspaceRegion, ⟨byteAddr g.stack, 40⟩]

theorem publicArgs_values {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) (a : Arguments g (publicArgument g) 10 s) {j : Nat} (hj : j < 10) :
    arg (s.callEntry.withRegions (publicRd g) (publicWr g)) j = publicArgument g j := by
  rw [arg_withRegions, arg_callEntry (by rw [h.sp]; have := h.valid.stackLow; omega_using [this])
    (by rw [h.sp]; have := h.valid.stackHigh; omega_using [hj, this])]
  change s.mem.readW (addr (s.gpr .esp) (4 * j)) 32 = _
  rw [h.address (by omega_using [hj])]
  exact a j hj

theorem publicCall_pre {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) (a : Arguments g (publicArgument g) 10 s) (siglen : g.signatureLength = g.length) :
    (Proof.Rsa.publicPrecomputedCheckedContract abi 96).pre (s.callEntry.withRegions (publicRd g) (publicWr g)) := by
  have sa := fun {j} (hj : j < 10) => publicArgs_values h a hj
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega_using [this]
  have efit : g.exponentLength < 2 ^ 32 := by have := h.valid.exponentFits; omega_using [kfit, this]
  have wfit : g.scratchLength < 2 ^ 32 := by have := h.valid.workspaceFit; omega_using [this]
  have pfit : g.preLength < 2 ^ 32 := by have := h.valid.sourceFits 3; change (g.sources 3).toNat + 8 * g.preLength ≤ 2 ^ 32 at this; omega_using [this]
  sig_pre [Proof.Rsa.publicPrecomputedCheckedContract, Proof.Rsa.publicPrecomputedSig, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [sa (by decide : 0 < 10), sa (by decide : 1 < 10), sa (by decide : 2 < 10),
    sa (by decide : 3 < 10), sa (by decide : 4 < 10), sa (by decide : 5 < 10),
    sa (by decide : 6 < 10), sa (by decide : 7 < 10), sa (by decide : 8 < 10), sa (by decide : 9 < 10),
    publicArgument, BitVec.toNat_ofNat, Nat.mod_eq_of_lt kfit, Nat.mod_eq_of_lt efit,
    Nat.mod_eq_of_lt wfit, Nat.mod_eq_of_lt pfit,
    argAddr_withRegions, argAddr_callEntry, h.sp, Nat.mul_zero, BitVec.add_zero]
  rw [show g.preLength * 8 = 8 * g.preLength from Nat.mul_comm _ _,
    show g.scratchLength * 8 = 8 * g.scratchLength from Nat.mul_comm _ _]
  have tempStack := fun x hx => h.valid.innerSub x (h.em1Sub x hx)
  have argsSub : (⟨byteAddr g.stack, 40⟩ : Region).Sub g.innerRegion := Region.sub_prefix (by decide)
  have argsStack := fun x hx => h.valid.innerSub x (argsSub x hx)
  have tempSource := fun i => (h.valid.stackSources i).sub_left tempStack
  have sourceArgs := fun i => ((h.valid.stackSources i).sub_left argsStack).symm
  have cSource := fun i => (h.valid.stackSources i).sub_left h.valid.calleeSub
  have cTemp := h.valid.calleeInner.sub_right h.em1Sub
  have cWork := h.valid.stackWorkspace.sub_left h.valid.calleeSub
  have cArgs := h.valid.calleeInner.sub_right argsSub
  have low : (g.stack - 4).toNat = g.stack.toNat - 4 := sub_toNat (k := 4) (by have := h.valid.stackLow; omega_using [this])
  have retSub : (⟨(g.stack - 4).setWidth 64, 4⟩ : Region).Sub g.calleeRegion :=
    VG.X86.below_sub (by decide : 4 ≤ 100) h.valid.stackLow
  have belowSub : (⟨(g.stack - 4).setWidth 64 - 96#64, 96⟩ : Region).Sub g.calleeRegion := by
    rw [← VG.X86.Taint.sub_setWidth (by rw [low]; have := h.valid.stackLow; omega_using [this] : 96 ≤ (g.stack - 4).toNat)]
    exact VG.X86.below_inner (by decide : 96 + 4 ≤ 100) h.valid.stackLow
  rw [low]
  have sourceSig : g.sourceRegion 2 = ⟨(g.sources 2).setWidth 64, g.length⟩ := by
    change (⟨byteAddr (g.sources 2), g.signatureLength⟩ : Region) = _
    rw [siglen]
    rfl
  have sourcePre : g.sourceRegion 3 = ⟨(g.sources 3).setWidth 64, 8 * g.preLength⟩ := rfl
  have sfSig : (g.sources 2).toNat + g.length ≤ 2 ^ 32 := by
    have fit := h.valid.sourceFits 2
    change (g.sources 2).toNat + g.signatureLength ≤ 2 ^ 32 at fit
    rw [siglen] at fit
    exact fit
  have emFit := h.valid.encodingFit (d := VG.Impl.RsaPkcs1Sig.X86.Verify.em1Offset)
    (by have := h.valid.maxLength; simp only [VG.Impl.RsaPkcs1Sig.X86.Verify.em1Offset, VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes]; omega_using [this])
  exact ⟨by have := h.valid.stackLow; omega_using [this], by have := h.valid.stackHigh; omega_using [this],
    by unfold publicRd; rw [sourcePre, sourceSig]; rfl, rfl,
    tempSource 3, tempSource 1, by rw [← sourceSig]; exact tempSource 2,
    h.valid.stackWorkspace.sub_left tempStack, h.em1Args,
    h.valid.sourcesWorkspace 3, sourceArgs 3,
    h.valid.sourcesWorkspace 1, sourceArgs 1,
    by rw [← sourceSig]; exact h.valid.sourcesWorkspace 2,
    by rw [← sourceSig]; exact sourceArgs 2,
    (h.valid.stackWorkspace.sub_left argsStack).symm,
    cTemp.sub_left retSub, (cSource 3).sub_left retSub, (cSource 1).sub_left retSub,
    by rw [← sourceSig]; exact (cSource 2).sub_left retSub,
    cWork.sub_left retSub, cArgs.sub_left retSub,
    cTemp.sub_left belowSub, (cSource 3).sub_left belowSub, (cSource 1).sub_left belowSub,
    by rw [← sourceSig]; exact (cSource 2).sub_left belowSub,
    cWork.sub_left belowSub, cArgs.sub_left belowSub,
    emFit, h.valid.sourceFits 3, h.valid.sourceFits 1, sfSig, h.valid.workspaceFit,
    ⟨h.valid.minLength, h.valid.maxLength⟩, h.valid.precomputed, trivial,
    h.valid.exponentPositive, h.valid.exponentFits, h.valid.space⟩

end VG.Proof.RsaPkcs1Sig.X86.Rcv

end

end

/-! # Calling checked public RSA retains every immutable verification input -/

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/RecoverCall.lean`, which only this module imported.
section

/-! # A verified nested call preserves the private wrapper's immutable inputs -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Proof.Mont.X86

def callClobbers : List Reg := [.eax, .ecx, .edx]

theorem call_keeps {s t : State} (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r) : Keeps callClobbers s t := by
  refine ⟨?_, rd, wr⟩
  intro r hr
  apply regs r
  cases r <;> simp_all [callClobbers, calleeSaved]

theorem private_call_ok {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s)
    {name : String} {code : Prog isa} {contract : Contract isa}
    (verified : Verified target code contract) (stack : stackUse code ≤ 96) (noSp : NoSp code)
    {rd wr : List Region} (pre : contract.pre (s.callEntry.withRegions rd wr))
    (read : Covers (rd ++ wr) (s.rd ++ s.wr)) (write : Covers wr s.wr)
    (sub : ∀ r ∈ wr, ∃ R ∈ bodyWrites g, r.Sub R) :
    WP isa (.call name code) s fun t => Context g bs t ∧
      Frame (wr ++ [g.calleeRegion]) s.mem t.mem ∧ Keeps callClobbers s t ∧
      ∃ u : State, u.mem = t.mem ∧ (∀ r, r ≠ .esp → u.gpr r = t.gpr r) ∧
        contract.post (s.callEntry.withRegions rd wr) u := by
  refine VG.X86.WP.call verified.1 noSp
    (by rw [h.sp]; have := h.valid.stackLow; omega_using [stack, this]) pre read write ?_
  intro t rdT wrT regs frame _ post
  have K := call_keeps rdT wrT regs
  have SP := K.1 .esp (by decide)
  have F : Frame (wr ++ [g.calleeRegion]) s.mem t.mem := by
    apply frame.sub
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ hx => hx⟩
    · obtain rfl := List.mem_singleton.mp hr
      refine ⟨g.calleeRegion, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      rw [h.sp]
      exact VG.X86.below_sub (by omega_using [stack] : stackUse code + 4 ≤ 100) h.valid.stackLow
  have Fbody : Frame (bodyWrites g) s.mem t.mem := F.sub (by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact sub r hr
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨g.calleeRegion, by simp [bodyWrites], fun _ hx => hx⟩)
  exact ⟨h.after Fbody K SP, F, K, post⟩

end VG.Proof.RsaPkcs1Sig.X86.Rcv
end

end

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86

abbrev PublicImpl := VG.Proof.RsaPkcs1Sig.X86.Ver.PublicImpl

theorem publicCovers {g : Geometry} {bs : Fin 4 → List Byte} {s : State} (h : Context g bs s) :
    Covers (publicRd g ++ publicWr g) (s.rd ++ s.wr) ∧ Covers (publicWr g) s.wr := by
  have outgoing : InRegions s.wr (byteAddr g.stack) 40 := by
    have W := h.inner.write (d := 0) (n := 40) (by decide)
    simpa only [BitVec.add_zero] using W
  have wr : Covers (publicWr g) s.wr := (Covers.one h.em1Write).cons
    ((Covers.one h.workspaceWrite).pair (Covers.one outgoing))
  exact ⟨Covers.append_left ((Covers.one (h.sources 3).read).cons
    ((Covers.one (h.sources 1).read).pair (Covers.one (h.sources 2).read))) wr.right, wr⟩

theorem publicWrites_sub {g : Geometry} {bs : Fin 4 → List Byte} {s : State} (h : Context g bs s) :
    ∀ r ∈ publicWr g, ∃ R ∈ bodyWrites g, r.Sub R := by
  intro r hr
  simp only [publicWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, by simp [bodyWrites], h.em1Sub⟩
  · exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩
  · exact ⟨g.innerRegion, by simp [bodyWrites], Region.sub_prefix (by decide)⟩

theorem Context.callFrame {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) : Frame [g.calleeRegion] s.mem s.callEntry.mem := by
  rw [State.callEntry_mem, h.sp]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (VG.X86.below_top (by decide : 4 ≤ 100) h.valid.stackLow (by decide : 4 ≤ 4))

theorem Context.callBytes {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) (i : Fin 4) :
    Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources i)) (g.sourceLength i) = bs i :=
  (VG.Proof.Rsa.rsa_bytes_frame h.callFrame (by have := (h.sources i).fits; omega_using [this])
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr
        exact ((h.valid.stackSources i).sub_left h.valid.calleeSub).symm)).trans (h.sources i).bytes

theorem Context.callWords {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) :
    Spec.Rsa.wordsAt s.callEntry.mem (byteAddr (g.sources 3)) g.preLength =
      Spec.Rsa.wordsAt s.mem (byteAddr (g.sources 3)) g.preLength :=
  VG.Proof.Rsa.wordsAt_frame h.callFrame (by
      have fit := h.valid.sourceFits 3
      change (g.sources 3).toNat + 8 * g.preLength ≤ 2 ^ 32 at fit
      omega_using [fit])
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr
        exact ((h.valid.stackSources 3).sub_left h.valid.calleeSub).symm)

def PublicOut (g : Geometry) (bs : Fin 4 → List Byte) (s t : State) : Prop :=
  Spec.Rsa.publicPrecompute (bs 0) = some (Spec.Rsa.wordsAt s.mem (byteAddr (g.sources 3)) g.preLength) →
    Spec.Rsa.written t.mem (byteAddr g.em1) g.length (t.gpr .eax)
      (Spec.Rsa.publicOpChecked (bs 0) (bs 1) (bs 2))

theorem public_call (v : PublicImpl) {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) (a : Arguments g (publicArgument g) 10 s) (siglen : g.signatureLength = g.length) :
    WP isa (.call v.name v.code) s fun t => Context g bs t ∧
      Frame (publicWr g ++ [g.calleeRegion]) s.mem t.mem ∧ Keeps callClobbers s t ∧ PublicOut g bs s t := by
  refine WP.mono (private_call_ok h v.verified v.stack v.noSp (publicCall_pre h a siglen)
    (publicCovers h).1 (publicCovers h).2 (publicWrites_sub h)) ?_
  rintro t ⟨ht, F, K, u, M, G, post⟩
  refine ⟨ht, F, K, ?_⟩
  sig_post [Proof.Rsa.publicPrecomputedCheckedContract, Proof.Rsa.publicPrecomputedSig, abi, argSlots, argVal, argBytes] at post
  have sa := fun {j} (hj : j < 10) => publicArgs_values h a hj
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega_using [this]
  have efit : g.exponentLength < 2 ^ 32 := by have := h.valid.exponentFits; omega_using [kfit, this]
  have pfit : g.preLength < 2 ^ 32 := by
    have fit := h.valid.sourceFits 3
    change (g.sources 3).toNat + 8 * g.preLength ≤ 2 ^ 32 at fit
    omega_using [fit]
  simp only [sa (by decide : 0 < 10), sa (by decide : 1 < 10), sa (by decide : 2 < 10),
    sa (by decide : 3 < 10), sa (by decide : 4 < 10), sa (by decide : 5 < 10), sa (by decide : 6 < 10),
    publicArgument, BitVec.toNat_ofNat, Nat.mod_eq_of_lt kfit, Nat.mod_eq_of_lt efit, Nat.mod_eq_of_lt pfit] at post
  rw [BitVec.setWidth_append_eq_right, M, G .eax (by decide)] at post
  change ∀ nb : List Byte, nb.length = g.length →
    Spec.Rsa.publicPrecompute nb = some (Spec.Rsa.wordsAt s.callEntry.mem (byteAddr (g.sources 3)) g.preLength) →
      Spec.Rsa.written t.mem (byteAddr g.em1) g.length (t.gpr .eax)
        (Spec.Rsa.publicOpChecked nb
          (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 1)) (g.sourceLength 1))
          (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 2)) g.length)) at post
  have sigBytes : Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 2)) g.length = bs 2 := by
    rw [← siglen]
    exact h.callBytes 2
  rw [h.callWords, h.callBytes 1, sigBytes] at post
  exact post (bs 0) (h.sources 0).length

end VG.Proof.RsaPkcs1Sig.X86.Rcv

end

end

/-! # Verification uses its two stack frames without changing their pointers -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Recover
open VG.Impl.RsaPkcs1Sig.X86.Verify (frameBytes)

theorem body_noSp (v : PublicImpl) : NoSp (body v.name v.code) := by
  unfold body
  exact .seq' (.of_all (by decide +kernel)) (.ite' (.of_all (by decide +kernel))
    (.seq' (.of_all (by decide +kernel)) (.seq' (.call' v.noSp) (.of_all (by decide +kernel)))))

theorem allocation_noSp (v : PublicImpl) :
    NoSp (.frame (.alloc frameBytes) (body v.name v.code) (.free frameBytes)) := by
  intro i hi
  simp only [instrs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | hi) | rfl
  · rfl
  · exact body_noSp v i hi
  · rfl

theorem inner_noSp (v : PublicImpl) :
    NoSp (.seq (.frame (.alloc frameBytes) (body v.name v.code) (.free frameBytes))
      (.block VG.Impl.RsaPkcs1Sig.X86.Sign.restore)) :=
  .seq' (allocation_noSp v) (.of_all (by decide +kernel))

end VG.Proof.RsaPkcs1Sig.X86.Rcv

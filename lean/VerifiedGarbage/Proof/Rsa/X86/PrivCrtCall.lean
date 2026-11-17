module

import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Rsa.X86.PrivRegions
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.X86.PrivContext
public import VerifiedGarbage.Proof.Rsa.X86.PrivCrtArgs
import VerifiedGarbage.Proof.Rsa.X86.PrivStackWord

/-! ### `Rsa.X86.PrivCrtPre`, which this module and modules that import it used -/

section

/-! # The CRT call's narrowed regions satisfy the shared cdecl signature -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86

def crtRd (g : PrivGeometry) : List Region :=
  [g.sourceRegion 0, g.sourceRegion 2, g.sourceRegion 3, g.sourceRegion 4,
    g.sourceRegion 5, g.sourceRegion 6, g.sourceRegion 7]
def crtWr (g : PrivGeometry) : List Region :=
  [⟨byteAddr g.temporary, g.length⟩, g.workspaceRegion, ⟨byteAddr g.stack, 72⟩]

theorem crtArgs_values {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) (a : CrtArgs g s) {j : Nat} (hj : j < 18) :
    arg (s.callEntry.withRegions (crtRd g) (crtWr g)) j = crtArgument g j := by
  rw [arg_withRegions, arg_callEntry (by rw [h.sp]; have := h.valid.stackLow; omega_using [this])
    (by rw [h.sp]; have := h.valid.stackHigh; omega_using [hj, this])]
  change s.mem.readW (addr (s.gpr .esp) (4 * j)) 32 = _
  rw [h.address (by omega_using [hj])]
  exact a j hj

theorem crtCall_pre {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) (a : CrtArgs g s) :
    (Proof.Rsa.privateCrtContract abi 96).pre (s.callEntry.withRegions (crtRd g) (crtWr g)) := by
  have sa := fun {j} (hj : j < 18) => crtArgs_values h a hj
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega_using [this]
  have pfit : g.pLength < 2 ^ 32 := by have := h.valid.pFits; omega_using [kfit, this]
  have qfit : g.qLength < 2 ^ 32 := by have := h.valid.qFits; omega_using [kfit, this]
  have wfit : g.scratchLength < 2 ^ 32 := by have := h.valid.workspaceFit; omega_using [this]
  sig_pre [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [sa (by decide : 0 < 18), sa (by decide : 1 < 18), sa (by decide : 2 < 18),
    sa (by decide : 3 < 18), sa (by decide : 4 < 18), sa (by decide : 5 < 18),
    sa (by decide : 6 < 18), sa (by decide : 7 < 18), sa (by decide : 8 < 18),
    sa (by decide : 9 < 18), sa (by decide : 10 < 18), sa (by decide : 11 < 18),
    sa (by decide : 12 < 18), sa (by decide : 13 < 18), sa (by decide : 14 < 18),
    sa (by decide : 15 < 18), sa (by decide : 16 < 18), sa (by decide : 17 < 18),
    crtArgument, PrivGeometry.argument, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff,
    ite_true, ite_false, BitVec.toNat_ofNat, Nat.mod_eq_of_lt kfit, Nat.mod_eq_of_lt pfit,
    Nat.mod_eq_of_lt qfit, Nat.mod_eq_of_lt wfit,
    argAddr_withRegions, argAddr_callEntry, h.sp, Nat.mul_zero, BitVec.add_zero]
  have temporarySub : (⟨byteAddr g.temporary, g.length⟩ : Region).Sub g.innerRegion := by
    rw [PrivGeometry.temporary, h.valid.offsetAddr (by decide)]
    exact Offset.sub_base _ (by have := h.valid.maxLength; simp only [candidateOffset, VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega_using [this])
  have outgoingSub : (⟨byteAddr g.stack, 72⟩ : Region).Sub g.innerRegion :=
    Region.sub_prefix (by decide : 72 ≤ VG.Impl.Rsa.X86.PrivChecked.frameBytes)
  have tempSources := fun i => (h.valid.stackSources i).sub_left (fun x hx => h.valid.innerSub x (temporarySub x hx))
  have tempWorkspace := h.valid.stackWorkspace.sub_left (fun x hx => h.valid.innerSub x (temporarySub x hx))
  have tempArgs : (⟨byteAddr g.temporary, g.length⟩ : Region).Disjoint ⟨byteAddr g.stack, 72⟩ := by
    rw [PrivGeometry.temporary, h.valid.offsetAddr (by decide)]
    exact Offset.disjoint_base _ (by decide : 72 ≤ candidateOffset) (by have := h.valid.maxLength; simp only [candidateOffset]; omega_using [kfit])
  have calleeSources := fun i => (h.valid.stackSources i).sub_left h.valid.calleeSub
  have calleeWorkspace := h.valid.stackWorkspace.sub_left h.valid.calleeSub
  have argsWorkspace := (h.valid.stackWorkspace.sub_left (fun x hx => h.valid.innerSub x (outgoingSub x hx))).symm
  have low : (g.stack - 4).toNat = g.stack.toNat - 4 := sub_toNat (k := 4) (by have := h.valid.stackLow; omega_using [this])
  rw [low]
  have retSub : (⟨(g.stack - 4).setWidth 64, 4⟩ : Region).Sub g.calleeRegion :=
    VG.X86.below_sub (by decide : 4 ≤ 100) h.valid.stackLow
  have belowSub : (⟨(g.stack - 4).setWidth 64 - 96#64, 96⟩ : Region).Sub g.calleeRegion := by
    rw [← VG.X86.Taint.sub_setWidth (by rw [low]; have := h.valid.stackLow; omega_using [this] : 96 ≤ (g.stack - 4).toNat)]
    exact VG.X86.below_inner (by decide : 96 + 4 ≤ 100) h.valid.stackLow
  have retTemp := (h.valid.calleeInner.sub_right temporarySub).sub_left retSub
  have belowTemp := (h.valid.calleeInner.sub_right temporarySub).sub_left belowSub
  have retSources := fun i => (calleeSources i).sub_left retSub
  have belowSources := fun i => (calleeSources i).sub_left belowSub
  have retWorkspace := calleeWorkspace.sub_left retSub
  have belowWorkspace := calleeWorkspace.sub_left belowSub
  have retArgs := (h.valid.calleeInner.sub_right outgoingSub).sub_left retSub
  have belowArgs := (h.valid.calleeInner.sub_right outgoingSub).sub_left belowSub
  have sourceArgs := fun i => ((h.valid.stackSources i).sub_left
    (fun x hx => h.valid.innerSub x (outgoingSub x hx))).symm
  simp only [Nat.mul_comm g.scratchLength 8]
  exact ⟨by have := h.valid.stackLow; omega_using [this],
    by have := h.valid.stackHigh; omega_using [this],
    rfl,
    rfl,
    tempSources 0,
    tempSources 2,
    tempSources 3,
    tempSources 4,
    tempSources 5,
    tempSources 6,
    tempSources 7,
    tempWorkspace,
    tempArgs,
    h.valid.sourcesWorkspace 0,
    sourceArgs 0,
    h.valid.sourcesWorkspace 2,
    sourceArgs 2,
    h.valid.sourcesWorkspace 3,
    sourceArgs 3,
    h.valid.sourcesWorkspace 4,
    sourceArgs 4,
    h.valid.sourcesWorkspace 5,
    sourceArgs 5,
    h.valid.sourcesWorkspace 6,
    sourceArgs 6,
    h.valid.sourcesWorkspace 7,
    sourceArgs 7,
    argsWorkspace,
    retTemp,
    retSources 0,
    retSources 2,
    retSources 3,
    retSources 4,
    retSources 5,
    retSources 6,
    retSources 7,
    retWorkspace,
    retArgs,
    belowTemp,
    belowSources 0,
    belowSources 2,
    belowSources 3,
    belowSources 4,
    belowSources 5,
    belowSources 6,
    belowSources 7,
    belowWorkspace,
    belowArgs,
    h.valid.temporaryFit,
    h.valid.sourceFits 0,
    h.valid.sourceFits 2,
    h.valid.sourceFits 3,
    h.valid.sourceFits 4,
    h.valid.sourceFits 5,
    h.valid.sourceFits 6,
    h.valid.sourceFits 7,
    h.valid.workspaceFit,
    ⟨h.valid.minLength, h.valid.maxLength⟩,
    trivial,
    trivial,
    h.valid.pPositive,
    h.valid.pFits,
    h.valid.qPositive,
    h.valid.qFits,
    trivial,
    trivial,
    trivial,
    h.valid.space⟩

end VG.Proof.Rsa.X86.PrivChecked

end

end

/-! ### `Rsa.X86.PrivCall`, which this module and modules that import it used -/

section

/-! # A verified nested call preserves the private wrapper's immutable inputs -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Proof.Mont.X86

def callClobbers : List Reg := [.eax, .ecx, .edx]

theorem call_keeps {s t : State} (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r) : Keeps callClobbers s t := by
  refine ⟨?_, rd, wr⟩
  intro r hr
  apply regs r
  cases r <;> simp_all [callClobbers, calleeSaved]

theorem private_call_ok {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s)
    {name : String} {code : Prog isa} {contract : Contract isa}
    (verified : Verified target code contract) (stack : stackUse code ≤ 96) (noSp : NoSp code)
    {rd wr : List Region} (pre : contract.pre (s.callEntry.withRegions rd wr))
    (read : Covers (rd ++ wr) (s.rd ++ s.wr)) (write : Covers wr s.wr)
    (sub : ∀ r ∈ wr, ∃ R ∈ bodyWrites g, r.Sub R) :
    WP isa (.call name code) s fun t => PrivContext g bs t ∧
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

end VG.Proof.Rsa.X86.PrivChecked

end

end

/-! # Calling the verified CRT writes its result into the private stack candidate -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86 VG.Proof.Mont.X86

theorem PrivContext.temporaryWrite {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) : InRegions s.wr (byteAddr g.temporary) g.length := by
  rw [PrivGeometry.temporary, h.valid.offsetAddr (by decide)]
  exact h.inner.write (by have := h.valid.maxLength; simp only [candidateOffset, VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega_using [this])

theorem PrivContext.outgoingWrite {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) {n : Nat} (hn : n ≤ 72) : InRegions s.wr (byteAddr g.stack) n := by
  have W := h.inner.write (d := 0) (n := n) (by simp only [VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega_using [hn])
  simpa only [BitVec.add_zero] using W

theorem crtCovers {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State} (h : PrivContext g bs s) :
    Covers (crtRd g ++ crtWr g) (s.rd ++ s.wr) ∧ Covers (crtWr g) s.wr := by
  have wr : Covers (crtWr g) s.wr := (Covers.one h.temporaryWrite).cons
    ((Covers.one h.workspaceWrite).pair (Covers.one (h.outgoingWrite (Nat.le_refl 72))))
  refine ⟨Covers.append_left ?_ wr.right, wr⟩
  exact (Covers.one (h.sources 0).read).cons ((Covers.one (h.sources 2).read).cons
    ((Covers.one (h.sources 3).read).cons ((Covers.one (h.sources 4).read).cons
    ((Covers.one (h.sources 5).read).cons ((Covers.one (h.sources 6).read).pair
    (Covers.one (h.sources 7).read))))))

theorem crtWrites_sub {g : PrivGeometry} (h : g.Valid) :
    ∀ r ∈ crtWr g, ∃ R ∈ bodyWrites g, r.Sub R := by
  intro r hr
  simp only [crtWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · refine ⟨g.innerRegion, by simp [bodyWrites], ?_⟩
    rw [PrivGeometry.temporary, h.offsetAddr (by decide)]
    exact Offset.sub_base _ (by have := h.maxLength; simp only [candidateOffset, VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega_using [this])
  · exact ⟨g.workspaceRegion, by simp [bodyWrites], fun _ hx => hx⟩
  · exact ⟨g.innerRegion, by simp [bodyWrites], Region.sub_prefix (by decide : 72 ≤ VG.Impl.Rsa.X86.PrivChecked.frameBytes)⟩

theorem PrivContext.callBytes {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) (i : Fin 8) :
    Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources i)) (g.sourceLength i) = bs i := by
  have F : Frame [g.calleeRegion] s.mem s.callEntry.mem := by
    rw [State.callEntry_mem, h.sp]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (VG.X86.below_top (by decide : 4 ≤ 100) h.valid.stackLow (by decide : 4 ≤ 4))
  have E := rsa_bytes_frame F (by have := (h.sources i).fits; omega_using [this] : g.sourceLength i < 2 ^ 64)
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr
        exact ((h.valid.stackSources i).sub_left h.valid.calleeSub).symm)
  exact E.trans (h.sources i).bytes

def CrtOut (g : PrivGeometry) (bs : Fin 8 → List Byte) (s : State) : Prop :=
  Spec.Rsa.written s.mem (byteAddr g.temporary) g.length (s.gpr .eax)
    (Spec.Rsa.privateCrt (bs 0) (bs 2) (bs 3) (bs 4) (bs 5) (bs 6) (bs 7))

theorem crt_call (v : CrtImpl) {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) (args : CrtArgs g s) :
    WP isa (.call v.name v.code) s fun t => PrivContext g bs t ∧
      Frame (crtWr g ++ [g.calleeRegion]) s.mem t.mem ∧ Keeps callClobbers s t ∧ CrtOut g bs t := by
  refine WP.mono (private_call_ok h v.verified v.stack v.noSp (crtCall_pre h args)
    (crtCovers h).1 (crtCovers h).2 (crtWrites_sub h.valid)) ?_
  rintro t ⟨ht, F, K, u, M, G, post⟩
  refine ⟨ht, F, K, ?_⟩
  sig_post [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argSlots, argVal, argBytes] at post
  have sa := fun {j} (hj : j < 18) => crtArgs_values h args hj
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega_using [this]
  have pfit : g.pLength < 2 ^ 32 := by have := h.valid.pFits; omega_using [kfit, this]
  have qfit : g.qLength < 2 ^ 32 := by have := h.valid.qFits; omega_using [kfit, this]
  simp only [sa (by decide : 0 < 18), sa (by decide : 2 < 18), sa (by decide : 3 < 18),
    sa (by decide : 4 < 18), sa (by decide : 6 < 18), sa (by decide : 7 < 18),
    sa (by decide : 8 < 18), sa (by decide : 9 < 18), sa (by decide : 10 < 18),
    sa (by decide : 12 < 18), sa (by decide : 14 < 18), crtArgument, PrivGeometry.argument,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, ite_true, ite_false,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt kfit, Nat.mod_eq_of_lt pfit, Nat.mod_eq_of_lt qfit] at post
  rw [BitVec.setWidth_append_eq_right, M, G .eax (by decide)] at post
  change Spec.Rsa.written t.mem (byteAddr g.temporary) g.length (t.gpr .eax)
    (Spec.Rsa.privateCrt
      (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 0)) (g.sourceLength 0))
      (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 2)) (g.sourceLength 2))
      (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 3)) (g.sourceLength 3))
      (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 4)) (g.sourceLength 4))
      (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 5)) (g.sourceLength 5))
      (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 6)) (g.sourceLength 6))
      (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 7)) (g.sourceLength 7))) at post
  rw [h.callBytes 0, h.callBytes 2, h.callBytes 3, h.callBytes 4, h.callBytes 5, h.callBytes 6, h.callBytes 7] at post
  exact post

end VG.Proof.Rsa.X86.PrivChecked

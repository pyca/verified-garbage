module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignContext
import VerifiedGarbage.Proof.Rsa.X86.PrivVerified
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignPrivateRegions
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignEncoding
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignRegions
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Rsa.X86.PrivCrtCall
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.X86.PrivImpl
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignStackWord
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignLocalArgument
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Weierstrass

/-! ### `RsaPkcs1Sig.X86.SignPrivatePre`, which this module and modules that import it used -/

section

/-! # The signing call satisfies the checked RSA contract -/

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/SignArguments.lean`, which only this module imported.
section

/-! # Installing successive cdecl arguments preserves every earlier word -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86

def Arguments (g : Geometry) (values : Nat → BitVec 32) (n : Nat) (s : State) : Prop :=
  ∀ j < n, s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 (4 * j)) 32 = values j

theorem Arguments.append {g : Geometry} {values : Nat → BitVec 32} {n : Nat} {s t : State}
    (h : Arguments g values n s) (hn : n < 20)
    (M : t.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 (4 * n)) (values n))
    (F : Frame [⟨byteAddr g.stack + BitVec.ofNat 64 (4 * n), 4⟩] s.mem t.mem) :
    Arguments g values (n + 1) t := by
  intro j hj
  by_cases same : j = n
  · subst j; rw [M, Mem.readW_writeW_self32]
  · rw [outgoing_word_preserved (by omega_using [hn, hj]) hn same F]
    exact h j (by omega_using [hj, same])

theorem slotFrame_outgoing {g : Geometry} {s t : State} {j : Nat} (hj : j < 20)
    (F : Frame [⟨byteAddr g.stack + BitVec.ofNat 64 (4 * j), 4⟩] s.mem t.mem) :
    Frame [⟨byteAddr g.stack, 80⟩] s.mem t.mem := F.sub (by
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by omega_using [hj])⟩)

theorem prepareArgument_ok {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    {values : Nat → BitVec 32} {n : Nat} {code : List Instr}
    (a : Arguments g values n s) (hn : n < 20)
    (w : WP isa (.block code) s fun t => Context g bs t ∧
      t.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 (4 * n)) (values n) ∧
      Frame [⟨byteAddr g.stack + BitVec.ofNat 64 (4 * n), 4⟩] s.mem t.mem ∧ Keeps [.eax] s t) :
    WP isa (.block code) s fun t => Context g bs t ∧ Arguments g values (n + 1) t ∧
      Frame [⟨byteAddr g.stack, 80⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  refine WP.mono w ?_
  rintro t ⟨h, M, F, K⟩
  exact ⟨h, a.append hn M F, slotFrame_outgoing hn F, K⟩

end VG.Proof.RsaPkcs1Sig.X86.Sgn
end

end

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/SignCallArgs.lean`, which only this module imported.
section

/-! # Install all twenty cdecl arguments for checked RSA signing -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Sign VG.Proof.Bignum.X86 VG.Proof.Mont.X86

def privateArgument (g : Geometry) (j : Nat) : BitVec 32 :=
  if j < 6 then g.argument j else if j = 6 then g.temporary else if j = 7 then g.argument 3 else g.argument (j + 1)

def PrivateArgs (g : Geometry) (s : State) : Prop := Arguments g (privateArgument g) 20 s

theorem copyPrefix_ok {g : Geometry} (values : Nat → BitVec 32) (input : Nat → Nat) (start n : Nat)
    (bound : start + n ≤ 20) (inputs : ∀ j < n, input j < 21)
    (valuesEq : ∀ j < n, g.argument (input j) = values (start + j))
    {bs : Fin 8 → List Byte} {s : State}
    (h : Context g bs s) (a : Arguments g values start s) :
    WP isa (.block ((List.range n).flatMap fun j => copyArgument (input j) (start + j))) s
      fun t => Context g bs t ∧ Arguments g values (start + n) t ∧
        Frame [⟨byteAddr g.stack, 80⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  induction n generalizing s with
  | zero => exact WP.block_nil ⟨h, a, Frame.refl _ _, Keeps.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ih (by omega_using [bound]) (fun j hj => inputs j (by omega_using [hj]))
      (fun j hj => valuesEq j (by omega_using [hj])) h a) ?_
    rintro u ⟨hu, au, F, K⟩
    refine WP.mono (prepareArgument_ok (bs := bs) au (by omega_using [bound])
      (WP.mono (copyArgument_ok u hu (inputs n (by omega_using [])) (by omega_using [bound])) ?_)) ?_
    · rintro t ⟨ht, M, F', K'⟩
      exact ⟨ht, by rw [valuesEq n (by omega_using [])] at M; exact M, F', K'⟩
    · rintro t ⟨ht, argsT, F', K'⟩
      exact ⟨ht, by simpa only [Nat.add_assoc] using argsT, F.trans F', K.trans K'⟩

theorem callArgs_ok {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : Context g bs s) :
    WP isa (.block callArgs) s fun t => Context g bs t ∧ PrivateArgs g t ∧
      Frame [⟨byteAddr g.stack, 80⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold callArgs
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copyPrefix_ok (g := g) (privateArgument g) id 0 6 (by decide)
    (by intro j hj; exact Nat.lt_trans hj (by decide))
    (by intro j hj; simp only [id_eq, Nat.zero_add, privateArgument, hj, ite_true]) h
    (by intro j hj; omega)) ?_
  rintro a ⟨ha, aa, F, K⟩
  refine WP.mono (prepareArgument_ok (bs := bs) aa (by decide : 6 < 20)
    (WP.mono (localArgument_ok a ha emOffset (by decide : 6 < 20)) ?_)) ?_
  · rintro t ⟨ht, M, F', K'⟩
    exact ⟨ht, by simpa only [privateArgument, Geometry.temporary, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, ite_false, ite_true] using M, F', K'⟩
  rintro b ⟨hb, ab, Fb, Kb⟩
  refine WP.mono (prepareArgument_ok (bs := bs) ab (by decide : 7 < 20)
    (WP.mono (copyArgument_ok b hb (by decide : 3 < 21) (by decide : 7 < 20)) ?_)) ?_
  · rintro t ⟨ht, M, F', K'⟩
    exact ⟨ht, by simpa only [privateArgument, Geometry.temporary, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, ite_false, ite_true] using M, F', K'⟩
  rintro c ⟨hc, ac, Fc, Kc⟩
  simp only [show (fun j : Nat => copyArgument (j + 9) (j + 8)) = (fun j => copyArgument (j + 9) (8 + j)) by funext j; rw [Nat.add_comm j 8]]
  refine WP.mono (copyPrefix_ok (g := g) (privateArgument g) (fun j => j + 9) 8 12 (by decide)
    (by intro j hj; omega_using [hj]) (by intro j hj; simp only [privateArgument, show ¬8 + j < 6 by omega_using [],
      show ¬8 + j = 6 by omega_using [], show ¬8 + j = 7 by omega_using [], ite_false]; congr 1; omega_using []) hc ac) ?_
  rintro t ⟨ht, argsT, Ft, Kt⟩
  exact ⟨ht, argsT, F.trans (Fb.trans (Fc.trans Ft)), K.trans (Kb.trans (Kc.trans Kt))⟩

end VG.Proof.RsaPkcs1Sig.X86.Sgn
end

end

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Rsa.X86.PrivChecked

def privateRd (g : Geometry) : List Region :=
  [g.sourceRegion 0, g.sourceRegion 1, ⟨byteAddr g.temporary, g.length⟩,
    g.sourceRegion 3, g.sourceRegion 4, g.sourceRegion 5, g.sourceRegion 6, g.sourceRegion 7]
def privateWr (g : Geometry) : List Region :=
  [g.outputRegion, g.workspaceRegion, ⟨byteAddr g.stack, 80⟩]

theorem privateArgs_values {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : Context g bs s) (a : PrivateArgs g s) {j : Nat} (hj : j < 20) :
    arg (s.callEntry.withRegions (privateRd g) (privateWr g)) j = privateArgument g j := by
  rw [arg_withRegions, arg_callEntry (by rw [h.sp]; have := h.valid.stackLow; simp only [calleeBytes] at this; omega_using [this])
    (by rw [h.sp]; have := h.valid.stackHigh; omega_using [hj, this])]
  change s.mem.readW (addr (s.gpr .esp) (4 * j)) 32 = _
  rw [h.address (by omega_using [hj])]
  exact a j hj

theorem privateCall_pre {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : Context g bs s) (a : PrivateArgs g s) :
    (Proof.Rsa.privateCheckedContract abi stackBytes).pre (s.callEntry.withRegions (privateRd g) (privateWr g)) := by
  have sa := fun {j} (hj : j < 20) => privateArgs_values h a hj
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega_arith
  have efit : g.exponentLength < 2 ^ 32 := by have := h.valid.exponentFits; omega_arith
  have pfit : g.pLength < 2 ^ 32 := by have := h.valid.pFits; omega_arith
  have qfit : g.qLength < 2 ^ 32 := by have := h.valid.qFits; omega_arith
  have wfit : g.scratchLength < 2 ^ 32 := by have := h.valid.workspaceFit; omega_arith
  sig_pre [Proof.Rsa.privateCheckedContract, Proof.Rsa.privateCheckedSig, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [sa (by decide : 0 < 20), sa (by decide : 1 < 20), sa (by decide : 2 < 20),
    sa (by decide : 3 < 20), sa (by decide : 4 < 20), sa (by decide : 5 < 20),
    sa (by decide : 6 < 20), sa (by decide : 7 < 20), sa (by decide : 8 < 20),
    sa (by decide : 9 < 20), sa (by decide : 10 < 20), sa (by decide : 11 < 20),
    sa (by decide : 12 < 20), sa (by decide : 13 < 20), sa (by decide : 14 < 20),
    sa (by decide : 15 < 20), sa (by decide : 16 < 20), sa (by decide : 17 < 20),
    sa (by decide : 18 < 20), sa (by decide : 19 < 20),
    privateArgument, Geometry.argument, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, ite_true, ite_false,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt kfit, Nat.mod_eq_of_lt efit, Nat.mod_eq_of_lt pfit,
    Nat.mod_eq_of_lt qfit, Nat.mod_eq_of_lt wfit,
    argAddr_withRegions, argAddr_callEntry, h.sp,
    Nat.mul_zero, BitVec.add_zero]

  rw [show g.scratchLength * 8 = 8 * g.scratchLength from Nat.mul_comm _ _]
  have tempStack := fun x hx => h.valid.innerSub x (h.temporarySub x hx)
  have argStack := fun x hx => h.valid.innerSub x (h.outgoingSub x hx)
  have cOut := h.valid.stackOutput.sub_left h.valid.calleeSub
  have cSource := fun i => (h.valid.stackSources i).sub_left h.valid.calleeSub
  have cTemp := h.valid.calleeInner.sub_right h.temporarySub
  have cWork := h.valid.stackWorkspace.sub_left h.valid.calleeSub
  have cArgs := h.valid.calleeInner.sub_right h.outgoingSub
  have sourceArgs := fun i => ((h.valid.stackSources i).sub_left argStack).symm
  have low : (g.stack - 4).toNat = g.stack.toNat - 4 :=
    sub_toNat (k := 4) (by have := h.valid.stackLow; simp only [calleeBytes] at this; omega_arith)
  rw [low]
  exact ⟨by have := h.valid.stackLow; simp only [calleeBytes, stackBytes] at *; omega_arith,
    by have := h.valid.stackHigh; omega_arith,
    rfl,
    rfl,
    h.valid.outputSources 0,
    h.valid.outputSources 1,
    (h.valid.stackOutput.sub_left tempStack).symm,
    h.valid.outputSources 3,
    h.valid.outputSources 4,
    h.valid.outputSources 5,
    h.valid.outputSources 6,
    h.valid.outputSources 7,
    h.valid.outputWorkspace,
    (h.valid.stackOutput.sub_left argStack).symm,
    h.valid.sourcesWorkspace 0,
    sourceArgs 0,
    h.valid.sourcesWorkspace 1,
    sourceArgs 1,
    h.valid.stackWorkspace.sub_left tempStack,
    h.temporaryArgs,
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
    (h.valid.stackWorkspace.sub_left argStack).symm,
    cOut.sub_left h.retSub,
    (cSource 0).sub_left h.retSub,
    (cSource 1).sub_left h.retSub,
    cTemp.sub_left h.retSub,
    (cSource 3).sub_left h.retSub,
    (cSource 4).sub_left h.retSub,
    (cSource 5).sub_left h.retSub,
    (cSource 6).sub_left h.retSub,
    (cSource 7).sub_left h.retSub,
    cWork.sub_left h.retSub,
    cArgs.sub_left h.retSub,
    cOut.sub_left h.belowSub,
    (cSource 0).sub_left h.belowSub,
    (cSource 1).sub_left h.belowSub,
    cTemp.sub_left h.belowSub,
    (cSource 3).sub_left h.belowSub,
    (cSource 4).sub_left h.belowSub,
    (cSource 5).sub_left h.belowSub,
    (cSource 6).sub_left h.belowSub,
    (cSource 7).sub_left h.belowSub,
    cWork.sub_left h.belowSub,
    cArgs.sub_left h.belowSub,
    h.valid.outputFit,
    h.valid.sourceFits 0,
    h.valid.sourceFits 1,
    h.valid.temporaryFit,
    h.valid.sourceFits 3,
    h.valid.sourceFits 4,
    h.valid.sourceFits 5,
    h.valid.sourceFits 6,
    h.valid.sourceFits 7,
    h.valid.workspaceFit,
    ⟨h.valid.minLength, h.valid.maxLength⟩,
    trivial,
    trivial,
    h.valid.exponentPositive,
    h.valid.exponentFits,
    h.valid.pPositive,
    h.valid.pFits,
    h.valid.qPositive,
    h.valid.qFits,
    trivial,
    trivial,
    trivial,
    h.valid.space⟩

end VG.Proof.RsaPkcs1Sig.X86.Sgn

end

end

/-! # Checked private RSA returns the signature of the exact local encoding -/

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/SignCall.lean`, which only this module imported.
section

/-! # A verified nested call preserves the private wrapper's immutable inputs -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.Proof.Mont.X86

def callClobbers : List Reg := [.eax, .ecx, .edx]

theorem call_keeps {s t : State} (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r) : Keeps callClobbers s t := by
  refine ⟨?_, rd, wr⟩
  intro r hr
  apply regs r
  cases r <;> simp_all [callClobbers, calleeSaved]

theorem private_call_ok {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : Context g bs s)
    {name : String} {code : Prog isa} {contract : Contract isa}
    (verified : Verified target code contract) (stack : stackUse code ≤ 3444) (noSp : NoSp code)
    {rd wr : List Region} (pre : contract.pre (s.callEntry.withRegions rd wr))
    (read : Covers (rd ++ wr) (s.rd ++ s.wr)) (write : Covers wr s.wr)
    (sub : ∀ r ∈ wr, ∃ R ∈ bodyWrites g, r.Sub R) :
    WP isa (.call name code) s fun t => Context g bs t ∧
      Frame (wr ++ [g.calleeRegion]) s.mem t.mem ∧ Keeps callClobbers s t ∧
      ∃ u : State, u.mem = t.mem ∧ (∀ r, r ≠ .esp → u.gpr r = t.gpr r) ∧
        contract.post (s.callEntry.withRegions rd wr) u := by
  refine VG.X86.WP.call verified.1 noSp
    (by rw [h.sp]; have := h.valid.stackLow; simp only [calleeBytes] at this; omega_using [stack, this]) pre read write ?_
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
      exact VG.X86.below_sub (by simp only [calleeBytes]; omega_using [stack] : stackUse code + 4 ≤ calleeBytes) h.valid.stackLow
  have Fbody : Frame (bodyWrites g) s.mem t.mem := F.sub (by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact sub r hr
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨g.calleeRegion, by simp [bodyWrites], fun _ hx => hx⟩)
  exact ⟨h.after Fbody K SP, F, K, post⟩

end VG.Proof.RsaPkcs1Sig.X86.Sgn
end

end

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl privCode stackBytes)

def privName (v : CrtImpl) : String := "vg_rsa_private_checked" ++ v.suffix

theorem privateCovers {g : Geometry} {bs : Fin 8 → List Byte} {s : State} (h : Context g bs s) :
    Covers (privateRd g ++ privateWr g) (s.rd ++ s.wr) ∧ Covers (privateWr g) s.wr := by
  have wr : Covers (privateWr g) s.wr := (Covers.one h.outputWrite).cons
    ((Covers.one h.workspaceWrite).pair (Covers.one h.outgoingWrite))
  have tmp : InRegions (s.rd ++ s.wr) (byteAddr g.temporary) g.length := by
    obtain ⟨r, hr, hc⟩ := h.temporaryWrite
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine ⟨Covers.append_left ?_ wr.right, wr⟩
  exact (Covers.one (h.sources 0).read).cons ((Covers.one (h.sources 1).read).cons
    ((Covers.one tmp).cons ((Covers.one (h.sources 3).read).cons ((Covers.one (h.sources 4).read).cons
    ((Covers.one (h.sources 5).read).cons ((Covers.one (h.sources 6).read).pair (Covers.one (h.sources 7).read)))))))

theorem privateWrites_sub {g : Geometry} {bs : Fin 8 → List Byte} {s : State} (h : Context g bs s) :
    ∀ r ∈ privateWr g, ∃ R ∈ bodyWrites g, r.Sub R := by
  intro r hr
  simp only [privateWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩
  · exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩
  · exact ⟨_, by simp [bodyWrites], h.outgoingSub⟩

theorem Context.callFrame {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : Context g bs s) : Frame [g.calleeRegion] s.mem s.callEntry.mem := by
  rw [State.callEntry_mem, h.sp]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (VG.X86.below_top (by decide : 4 ≤ calleeBytes) h.valid.stackLow (by decide : 4 ≤ 4))

theorem Context.callBytes {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : Context g bs s) (i : Fin 8) :
    Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources i)) (g.sourceLength i) = bs i := by
  exact (VG.Proof.Rsa.rsa_bytes_frame h.callFrame (by have := (h.sources i).fits; omega_using [this])
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr
        exact ((h.valid.stackSources i).sub_left h.valid.calleeSub).symm)).trans (h.sources i).bytes

theorem Context.callTemporary {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : Context g bs s) :
    Spec.Rsa.bytesAt s.callEntry.mem (byteAddr g.temporary) g.length =
      Spec.Rsa.bytesAt s.mem (byteAddr g.temporary) g.length := by
  exact VG.Proof.Rsa.rsa_bytes_frame h.callFrame (by have := h.valid.maxLength; omega_using [this])
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr
        exact (h.valid.calleeInner.sub_right h.temporarySub).symm)

def PrivateOut (g : Geometry) (bs : Fin 8 → List Byte) (em : List Byte) (s : State) : Prop :=
  Spec.Rsa.writtenOutcome s.mem (byteAddr g.output) g.length (s.gpr .eax)
    (Spec.Rsa.privateChecked (bs 0) (bs 1) em (bs 3) (bs 4) (bs 5) (bs 6) (bs 7))

theorem private_call (v : CrtImpl) {g : Geometry} {bs : Fin 8 → List Byte} {s : State} {em : List Byte}
    (h : Context g bs s) (a : PrivateArgs g s)
    (bytes : Spec.Rsa.bytesAt s.mem (byteAddr g.temporary) g.length = em) :
    WP isa (.call (privName v) (privCode v)) s fun t => Context g bs t ∧
      Frame (privateWr g ++ [g.calleeRegion]) s.mem t.mem ∧ Keeps callClobbers s t ∧ PrivateOut g bs em t := by
  refine WP.mono (private_call_ok h (VG.Proof.Rsa.X86.PrivChecked.code_verified v)
    (VG.Proof.Rsa.X86.PrivChecked.code_stack v) (VG.Proof.Rsa.X86.PrivChecked.privateCode_noSp v)
    (privateCall_pre h a) (privateCovers h).1 (privateCovers h).2 (privateWrites_sub h)) ?_
  rintro t ⟨ht, F, K, u, M, G, post⟩
  refine ⟨ht, F, K, ?_⟩
  sig_post [Proof.Rsa.privateCheckedContract, Proof.Rsa.privateCheckedSig, abi, argSlots, argVal, argBytes] at post
  have sa := fun {j} (hj : j < 20) => privateArgs_values h a hj
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega_using [this]
  have efit : g.exponentLength < 2 ^ 32 := by have := h.valid.exponentFits; omega_using [kfit, this]
  have pfit : g.pLength < 2 ^ 32 := by have := h.valid.pFits; omega_using [kfit, this]
  have qfit : g.qLength < 2 ^ 32 := by have := h.valid.qFits; omega_using [kfit, this]
  simp only [sa (by decide : 0 < 20), sa (by decide : 2 < 20), sa (by decide : 3 < 20),
    sa (by decide : 4 < 20), sa (by decide : 5 < 20), sa (by decide : 6 < 20),
    sa (by decide : 8 < 20), sa (by decide : 9 < 20), sa (by decide : 10 < 20), sa (by decide : 11 < 20),
    sa (by decide : 12 < 20), sa (by decide : 14 < 20),
    sa (by decide : 16 < 20), privateArgument, Geometry.argument,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, ite_true, ite_false, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt kfit, Nat.mod_eq_of_lt efit, Nat.mod_eq_of_lt pfit, Nat.mod_eq_of_lt qfit] at post
  rw [BitVec.setWidth_append_eq_right, M, G .eax (by decide)] at post
  change Spec.Rsa.writtenOutcome t.mem (byteAddr g.output) g.length (t.gpr .eax)
    (Spec.Rsa.privateChecked
      (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 0)) (g.sourceLength 0))
      (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 1)) (g.sourceLength 1))
      (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr g.temporary) g.length)
      (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 3)) (g.sourceLength 3))
      (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 4)) (g.sourceLength 4))
      (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 5)) (g.sourceLength 5))
      (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 6)) (g.sourceLength 6))
      (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 7)) (g.sourceLength 7))) at post
  rw [h.callBytes 0, h.callBytes 1, h.callTemporary, bytes, h.callBytes 3, h.callBytes 4,
    h.callBytes 5, h.callBytes 6, h.callBytes 7] at post
  exact post

end VG.Proof.RsaPkcs1Sig.X86.Sgn

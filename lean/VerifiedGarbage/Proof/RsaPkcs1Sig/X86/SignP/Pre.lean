module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignPrivateCall
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
public import VerifiedGarbage.Proof.Rsa.X86.PrivP.Verified
public import VerifiedGarbage.Proof.Rsa.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignPrivateRegions
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignStackWord
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignRegions
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignLocalArgument
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignEncoding
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-! # `vg_rsa_pkcs1_sign_precomputed` on i686: `pre` and the call's arguments 20 and 21

What the wrapper keeps of `pre` (its arguments 21 and 22) from its entry on
(`SPreCtx`), and `vg_rsa_private_checked_precomputed`'s arguments:
`callArgs`' twenty, then `pre` and `pre_len` (`callArgsP_ok`).
-/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.X86.Wp VG.Impl.RsaPkcs1Sig.X86.Sign VG.Proof.Bignum.X86 VG.Proof.Mont.X86

/-- `pre` (argument 21, `L` words in argument 22) through the body: the arguments and `pre`
readable and apart from what the body writes, and `pre` the key's precomputed values. -/
structure SPreCtx (g : Geometry) (bs : Fin 8 → List Byte) (P : BitVec 32) (L : Nat) (s : State) : Prop where
  high : g.stack.toNat + VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes + 20 + 92 ≤ 2 ^ 32
  ptr : s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes + 20 + 84)) 32 = P
  len : s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes + 20 + 88)) 32 =
    BitVec.ofNat 32 L
  argsRead : InRegions (s.rd ++ s.wr)
    (byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes + 20 + 84)) 8
  argsSep : ∀ r ∈ bodyWrites g, Region.Disjoint
    ⟨byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes + 20 + 84), 8⟩ r
  preRead : InRegions (s.rd ++ s.wr) (byteAddr P) (8 * L)
  preFit : P.toNat + 8 * L ≤ 2 ^ 32
  preSep : ∀ r ∈ bodyWrites g, Region.Disjoint ⟨byteAddr P, 8 * L⟩ r
  lenEq : L = Spec.Rsa.privatePrecomputedWords g.length g.pLength g.qLength
  key : Spec.Rsa.privatePrecompute (bs 0) (bs 3) (bs 4) = some (Spec.Rsa.wordsAt s.mem (byteAddr P) L)

section
variable {g : Geometry} {bs : Fin 8 → List Byte} {P : BitVec 32} {L : Nat}

theorem SPreCtx.after {s t : State} {rs : List Reg} (H : SPreCtx g bs P L s)
    (frame : Frame (bodyWrites g) s.mem t.mem) (rest : Keeps rs s t) : SPreCtx g bs P L t := by
  have word : ∀ d, d + 4 ≤ 8 → t.mem.readW (byteAddr g.stack +
      BitVec.ofNat 64 (VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes + 20 + 84) + BitVec.ofNat 64 d) 32 =
      s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes + 20 + 84) +
        BitVec.ofNat 64 d) 32 := fun d hd =>
    frame.readW (Offset.contains_base _ (by omega : d + 32 / 8 ≤ 8) (by omega)) H.argsSep (by decide)
  refine ⟨H.high, ?_, ?_, by rw [rest.2.1, rest.2.2]; exact H.argsRead, H.argsSep,
    by rw [rest.2.1, rest.2.2]; exact H.preRead, H.preFit, H.preSep, H.lenEq, ?_⟩
  · have w := word 0 (by decide)
    simp only [BitVec.add_zero] at w
    rw [w]; exact H.ptr
  · have w := word 4 (by decide)
    rw [Offset.add_add] at w
    rw [w]; exact H.len
  · rw [VG.Proof.Rsa.wordsAt_frame frame (by have := H.preFit; omega) H.preSep]; exact H.key

/-- An address in the wrapper's frame and arguments, from `esp`. -/
theorem SPreCtx.address {s : State} (h : Context g bs s) (H : SPreCtx g bs P L s) {d : Nat}
    (hd : d < VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes + 20 + 92) :
    addr (s.gpr .esp) d = byteAddr g.stack + BitVec.ofNat 64 d := by
  rw [h.sp]
  exact addr_eq (by have := H.high; omega)

/-- Copying an incoming word to the outgoing argument `j`. -/
theorem copyWord_ok {s : State} (h : Context g bs s) (H : SPreCtx g bs P L s) {i j : Nat} (hi : i < 23)
    (hj : j < 22) {v : BitVec 32}
    (rd : InRegions (s.rd ++ s.wr) (byteAddr g.stack +
      BitVec.ofNat 64 (VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes + 20 + 4 * i)) 4)
    (val : s.mem.readW (byteAddr g.stack +
      BitVec.ofNat 64 (VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes + 20 + 4 * i)) 32 = v) :
    WP isa (.block (copyArgument i j)) s fun t =>
      Context g bs t ∧
      t.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 (4 * j)) v ∧
      Frame [⟨byteAddr g.stack + BitVec.ofNat 64 (4 * j), 4⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold copyArgument incoming stackAt
  refine wp_ldm rfl (by rw [H.address h (by omega)]; exact rd) fun u U => ?_
  refine wp_stm (B := s.gpr .esp) (U.other .esp (by decide))
    (by rw [U.wr, h.address (by omega)]; exact h.inner.write (by simp only [VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes]; omega))
    fun t T => WP.block_nil ?_
  have M : t.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 (4 * j)) v := by
    rw [T.mem, U.gpr, U.mem, H.address h (d := VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes + 20 + 4 * i) (by omega),
      val, h.address (by omega)]
  have K : Keeps [.eax] s t := U.keeps.trans (T.keeps _)
  have F : Frame [⟨byteAddr g.stack + BitVec.ofNat 64 (4 * j), 4⟩] s.mem t.mem := by
    rw [M]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨h.after (F.sub ?_) K (K.1 .esp (by decide)), M, F, K⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨g.innerRegion, by simp [bodyWrites], Offset.sub_base _ (by simp only [VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes]; omega)⟩

theorem outgoing_word_preservedP {m m' : Mem} {i j : Nat}
    (hi : i < 22) (hj : j < 22) (hne : i ≠ j)
    (f : Frame [⟨byteAddr g.stack + BitVec.ofNat 64 (4 * j), 4⟩] m m') :
    m'.readW (byteAddr g.stack + BitVec.ofNat 64 (4 * i)) 32 =
      m.readW (byteAddr g.stack + BitVec.ofNat 64 (4 * i)) 32 := by
  apply f.readW (r := ⟨byteAddr g.stack + BitVec.ofNat 64 (4 * i), 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem Arguments.appendP {values : Nat → BitVec 32} {n : Nat} {s t : State}
    (h : Arguments g values n s) (hn : n < 22)
    (M : t.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 (4 * n)) (values n))
    (F : Frame [⟨byteAddr g.stack + BitVec.ofNat 64 (4 * n), 4⟩] s.mem t.mem) :
    Arguments g values (n + 1) t := by
  intro j hj
  by_cases same : j = n
  · subst j; rw [M, Mem.readW_writeW_self32]
  · rw [outgoing_word_preservedP (by omega) hn same F]
    exact h j (by omega)

/-- `vg_rsa_private_checked_precomputed`'s arguments: `privateArgument`'s twenty, then `pre`
and `pre_len`. -/
def privateArgumentP (g : Geometry) (P : BitVec 32) (L : Nat) (j : Nat) : BitVec 32 :=
  if j < 20 then privateArgument g j else if j = 20 then P else BitVec.ofNat 32 L

def PrivateArgsP (g : Geometry) (P : BitVec 32) (L : Nat) (s : State) : Prop :=
  Arguments g (privateArgumentP g P L) 22 s

theorem callArgsP_ok {s : State} (h : Context g bs s) (H : SPreCtx g bs P L s) :
    WP isa (.block callArgsP) s fun t => Context g bs t ∧ SPreCtx g bs P L t ∧ PrivateArgsP g P L t ∧
      Frame [⟨byteAddr g.stack, 88⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold callArgsP
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (callArgs_ok h) ?_
  rintro a ⟨ha, aa, F, K⟩
  have frameA : Frame (bodyWrites g) s.mem a.mem := F.sub (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, by simp [bodyWrites], h.outgoingSub⟩)
  have Ha := H.after frameA K
  have aa' : Arguments g (privateArgumentP g P L) 20 a := fun j hj => by
    rw [aa j hj]; simp only [privateArgumentP, hj, ite_true]
  have readP : ∀ {u : State}, SPreCtx g bs P L u → ∀ k, k < 2 → InRegions (u.rd ++ u.wr) (byteAddr g.stack +
      BitVec.ofNat 64 (VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes + 20 + 4 * (21 + k))) 4 := by
    intro u Hu k hk
    have read := CallLay.inRegions_sub (off := 4 * k) Hu.argsRead (l := 4) (by omega) (by decide)
    rw [Offset.add_add, show VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes + 20 + 84 + 4 * k =
      VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes + 20 + 4 * (21 + k) by omega] at read
    exact read
  refine WP.mono (copyWord_ok ha Ha (by decide : 21 < 23) (by decide : 20 < 22) (readP Ha 0 (by decide))
    (v := P) Ha.ptr) ?_
  rintro b ⟨hb, Mb, Fb, Kb⟩
  have frameB : Frame (bodyWrites g) a.mem b.mem := Fb.sub (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨g.innerRegion, by simp [bodyWrites], Offset.sub_base _ (by decide)⟩)
  have Hb := Ha.after frameB Kb
  have ab := aa'.appendP (by decide) (by simpa [privateArgumentP] using Mb) Fb
  refine WP.mono (copyWord_ok hb Hb (by decide : 22 < 23) (by decide : 21 < 22) (readP Hb 1 (by decide))
    (v := BitVec.ofNat 32 L) Hb.len) ?_
  rintro t ⟨ht, Mt, Ft, Kt⟩
  have frameT : Frame (bodyWrites g) b.mem t.mem := Ft.sub (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨g.innerRegion, by simp [bodyWrites], Offset.sub_base _ (by decide)⟩)
  have at' := ab.appendP (by decide) (by simpa [privateArgumentP] using Mt) Ft
  have wide : ∀ {m m' : Mem} {j : Nat}, j < 22 →
      Frame [⟨byteAddr g.stack + BitVec.ofNat 64 (4 * j), 4⟩] m m' → Frame [⟨byteAddr g.stack, 88⟩] m m' :=
    fun hj Fj => Fj.sub (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by omega)⟩)
  refine ⟨ht, Hb.after frameT Kt, at', ?_, K.trans (Kb.trans Kt)⟩
  exact (F.sub (by
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩)).trans
    ((wide (by decide : 20 < 22) Fb).trans (wide (by decide : 21 < 22) Ft))
end
end VG.Proof.RsaPkcs1Sig.X86.Sgn

/-! ## The call of `vg_rsa_private_checked_precomputed` -/

namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86

section
variable {g : Geometry} {bs : Fin 8 → List Byte} {P : BitVec 32} {L : Nat}
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl CrtPImpl privCodeP stackBytes)

def privateRdP (g : Geometry) (P : BitVec 32) (L : Nat) : List Region := privateRd g ++ [⟨byteAddr P, 8 * L⟩]
def privateWrP (g : Geometry) : List Region := [g.outputRegion, g.workspaceRegion, ⟨byteAddr g.stack, 88⟩]

theorem SPreCtx.L32 {s : State} (H : SPreCtx g bs P L s) : L < 2 ^ 32 := by have := H.preFit; omega

theorem Context.outgoingSubP {s : State} (_h : Context g bs s) :
    (⟨byteAddr g.stack, 88⟩ : Region).Sub g.innerRegion := Region.sub_prefix (by decide)

theorem Context.outgoingWriteP {s : State} (h : Context g bs s) : InRegions s.wr (byteAddr g.stack) 88 := by
  have W := h.inner.write (d := 0) (n := 88) (by decide)
  simpa only [BitVec.add_zero] using W

theorem Context.temporaryArgsP {s : State} (h : Context g bs s) :
    (⟨byteAddr g.temporary, g.length⟩ : Region).Disjoint ⟨byteAddr g.stack, 88⟩ := by
  rw [Geometry.temporary, h.valid.offsetAddr (by decide)]
  exact Offset.disjoint_base _ (by decide : 88 ≤ VG.Impl.RsaPkcs1Sig.X86.Sign.emOffset)
    (by have := h.valid.maxLength; simp only [VG.Impl.RsaPkcs1Sig.X86.Sign.emOffset]; omega)

theorem privateArgsP_values {s : State} (h : Context g bs s) (a : PrivateArgsP g P L s) {j : Nat} (hj : j < 22) :
    arg (s.callEntry.withRegions (privateRdP g P L) (privateWrP g)) j = privateArgumentP g P L j := by
  rw [arg_withRegions, arg_callEntry (by rw [h.sp]; have := h.valid.stackLow; simp only [calleeBytes] at this; omega)
    (by rw [h.sp]; have := h.valid.stackHigh; omega)]
  change s.mem.readW (addr (s.gpr .esp) (4 * j)) 32 = _
  rw [h.address (by omega)]
  exact a j hj

theorem SPreCtx.callWords {s : State} (h : Context g bs s) (H : SPreCtx g bs P L s) :
    Spec.Rsa.wordsAt s.callEntry.mem (byteAddr P) L = Spec.Rsa.wordsAt s.mem (byteAddr P) L :=
  VG.Proof.Rsa.wordsAt_frame h.callFrame (by have := H.preFit; omega) (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact H.preSep _ (by simp [bodyWrites]))

theorem privateCallP_pre {s : State} (h : Context g bs s) (H : SPreCtx g bs P L s) (a : PrivateArgsP g P L s) :
    (Proof.Rsa.privateCheckedPrecomputedContract abi stackBytes).pre
      (s.callEntry.withRegions (privateRdP g P L) (privateWrP g)) := by
  have sa := fun {j} (hj : j < 22) => privateArgsP_values h a hj
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega_arith
  have efit : g.exponentLength < 2 ^ 32 := by have := h.valid.exponentFits; omega_arith
  have pfit : g.pLength < 2 ^ 32 := by have := h.valid.pFits; omega_arith
  have qfit : g.qLength < 2 ^ 32 := by have := h.valid.qFits; omega_arith
  have wfit : g.scratchLength < 2 ^ 32 := by have := h.valid.workspaceFit; omega_arith
  have lfit := H.L32
  sig_pre [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
    Proof.Rsa.privateCheckedSig, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [sa (by decide : 0 < 22),
    sa (by decide : 1 < 22),
    sa (by decide : 2 < 22),
    sa (by decide : 3 < 22),
    sa (by decide : 4 < 22),
    sa (by decide : 5 < 22),
    sa (by decide : 6 < 22),
    sa (by decide : 7 < 22),
    sa (by decide : 8 < 22),
    sa (by decide : 9 < 22),
    sa (by decide : 10 < 22),
    sa (by decide : 11 < 22),
    sa (by decide : 12 < 22),
    sa (by decide : 13 < 22),
    sa (by decide : 14 < 22),
    sa (by decide : 15 < 22),
    sa (by decide : 16 < 22),
    sa (by decide : 17 < 22),
    sa (by decide : 18 < 22),
    sa (by decide : 19 < 22),
    sa (by decide : 20 < 22),
    sa (by decide : 21 < 22),
    privateArgumentP, privateArgument, Geometry.argument, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, ite_true,
    ite_false, BitVec.toNat_ofNat, Nat.mod_eq_of_lt kfit, Nat.mod_eq_of_lt efit, Nat.mod_eq_of_lt pfit,
    Nat.mod_eq_of_lt qfit, Nat.mod_eq_of_lt wfit, Nat.mod_eq_of_lt lfit,
    argAddr_withRegions, argAddr_callEntry, h.sp, Nat.mul_zero, BitVec.add_zero]
  rw [show g.scratchLength * 8 = 8 * g.scratchLength from Nat.mul_comm _ _, show L * 8 = 8 * L from Nat.mul_comm _ _]
  have args88 : (⟨byteAddr g.stack, 88⟩ : Region).Sub g.innerRegion := h.outgoingSubP
  have tempStack := fun x hx => h.valid.innerSub x (h.temporarySub x hx)
  have argStack := fun x hx => h.valid.innerSub x (args88 x hx)
  have cOut := h.valid.stackOutput.sub_left h.valid.calleeSub
  have cSource := fun i => (h.valid.stackSources i).sub_left h.valid.calleeSub
  have cTemp := h.valid.calleeInner.sub_right h.temporarySub
  have cWork := h.valid.stackWorkspace.sub_left h.valid.calleeSub
  have cArgs := h.valid.calleeInner.sub_right args88
  have cPre := (H.preSep g.calleeRegion (by simp [bodyWrites])).symm
  have sourceArgs := fun i => ((h.valid.stackSources i).sub_left argStack).symm
  have low : (g.stack - 4).toNat = g.stack.toNat - 4 :=
    sub_toNat (k := 4) (by have := h.valid.stackLow; simp only [calleeBytes] at this; omega_arith)
  rw [low]
  have key := H.key
  rw [← h.callBytes 0, ← h.callBytes 3, ← h.callBytes 4, ← H.callWords h] at key
  have lenEq := H.lenEq
  refine ⟨by have := h.valid.stackLow; simp only [calleeBytes, stackBytes] at *; omega_arith,
    by have := H.high; simp only [VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes] at this; omega_arith,
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
    (H.preSep g.outputRegion (by simp [bodyWrites])).symm,
    (h.valid.stackOutput.sub_left argStack).symm,
    h.valid.sourcesWorkspace 0,
    sourceArgs 0,
    h.valid.sourcesWorkspace 1,
    sourceArgs 1,
    h.valid.stackWorkspace.sub_left tempStack,
    h.temporaryArgsP,
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
    (H.preSep g.workspaceRegion (by simp [bodyWrites])).symm,
    (h.valid.stackWorkspace.sub_left argStack).symm,
    (H.preSep g.innerRegion (by simp [bodyWrites])).sub_right args88,
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
    cPre.sub_left h.retSub,
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
    cPre.sub_left h.belowSub,
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
    H.preFit,
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
    h.valid.space,
    lenEq,
    ?_⟩
  rw [State.callEntry_mem, h.sp] at key
  exact key

theorem privateCoversP {s : State} (h : Context g bs s) (H : SPreCtx g bs P L s) :
    Covers (privateRdP g P L ++ privateWrP g) (s.rd ++ s.wr) ∧ Covers (privateWrP g) s.wr := by
  have wr : Covers (privateWrP g) s.wr := (Covers.one h.outputWrite).cons
    ((Covers.one h.workspaceWrite).pair (Covers.one h.outgoingWriteP))
  have tmp : InRegions (s.rd ++ s.wr) (byteAddr g.temporary) g.length := by
    obtain ⟨r, hr, hc⟩ := h.temporaryWrite
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine ⟨Covers.append_left ?_ wr.right, wr⟩
  exact (Covers.one (h.sources 0).read).cons ((Covers.one (h.sources 1).read).cons
    ((Covers.one tmp).cons ((Covers.one (h.sources 3).read).cons ((Covers.one (h.sources 4).read).cons
    ((Covers.one (h.sources 5).read).cons ((Covers.one (h.sources 6).read).cons
    ((Covers.one (h.sources 7).read).pair (Covers.one H.preRead))))))))

theorem privateWritesP_sub {s : State} (h : Context g bs s) :
    ∀ r ∈ privateWrP g, ∃ R ∈ bodyWrites g, r.Sub R := by
  intro r hr
  simp only [privateWrP, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩
  · exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩
  · exact ⟨_, by simp [bodyWrites], h.outgoingSubP⟩

/-- `vg_rsa_private_checked_precomputed`'s name with the variant's suffix. -/
def privNameP (v : CrtImpl) : String := "vg_rsa_private_checked_precomputed" ++ v.suffix

theorem private_callP (v : CrtImpl) (w : CrtPImpl) {s : State} {em : List Byte}
    (h : Context g bs s) (H : SPreCtx g bs P L s) (a : PrivateArgsP g P L s)
    (bytes : Spec.Rsa.bytesAt s.mem (byteAddr g.temporary) g.length = em) :
    WP isa (.call (privNameP v) (privCodeP v w)) s fun t => Context g bs t ∧ SPreCtx g bs P L t ∧
      Frame (privateWrP g ++ [g.calleeRegion]) s.mem t.mem ∧ Keeps callClobbers s t ∧ PrivateOut g bs em t := by
  refine WP.mono (private_call_ok h (VG.Proof.Rsa.X86.PrivChecked.code_verifiedP v w)
    (VG.Proof.Rsa.X86.PrivChecked.code_stackP v w) (VG.Proof.Rsa.X86.PrivChecked.privateCodeP_noSp v w)
    (privateCallP_pre h H a) (privateCoversP h H).1 (privateCoversP h H).2 (privateWritesP_sub h)) ?_
  rintro t ⟨ht, F, K, u, M, G, post⟩
  have Fb : Frame (bodyWrites g) s.mem t.mem := F.sub (by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact privateWritesP_sub h r hr
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨g.calleeRegion, by simp [bodyWrites], fun _ hx => hx⟩)
  refine ⟨ht, H.after Fb K, F, K, ?_⟩
  sig_post [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
    Proof.Rsa.privateCheckedSig, abi, argSlots, argVal, argBytes] at post
  have sa := fun {j} (hj : j < 22) => privateArgsP_values h a hj
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega
  have efit : g.exponentLength < 2 ^ 32 := by have := h.valid.exponentFits; omega
  have pfit : g.pLength < 2 ^ 32 := by have := h.valid.pFits; omega
  have qfit : g.qLength < 2 ^ 32 := by have := h.valid.qFits; omega
  simp only [sa (by decide : 0 < 22), sa (by decide : 2 < 22), sa (by decide : 3 < 22),
    sa (by decide : 4 < 22), sa (by decide : 5 < 22), sa (by decide : 6 < 22),
    sa (by decide : 8 < 22), sa (by decide : 9 < 22), sa (by decide : 10 < 22), sa (by decide : 11 < 22),
    sa (by decide : 12 < 22), sa (by decide : 14 < 22),
    sa (by decide : 16 < 22), privateArgumentP, privateArgument, Geometry.argument,
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

theorem wordsAt_take' (m : Mem) (p : Addr) {n L : Nat} (h : n ≤ L) :
    Spec.Rsa.wordsAt m p n = (Spec.Rsa.wordsAt m p L).take n := by
  simp only [Spec.Rsa.wordsAt, ← List.map_take, List.take_range, Nat.min_eq_left h]

/-- `pre`'s first words, which the call may leak: the modulus' values. -/
theorem pre_modulus {nB pB qB : List Byte} {m : Mem} {p : Addr} {n : Nat}
    (h : Spec.Rsa.privatePrecompute nB pB qB = some (Spec.Rsa.wordsAt m p n)) :
    some (Spec.Rsa.wordsAt m p (Spec.Rsa.precomputedWords nB.length)) = Spec.Rsa.publicPrecompute nB := by
  unfold Spec.Rsa.privatePrecompute at h
  split at h
  · cases hw : Spec.Rsa.publicPrecompute nB with
    | none => rw [hw] at h; cases h
    | some w =>
      rw [hw] at h
      simp only [Option.map_some, Option.some.injEq] at h
      have hl : w.length = Spec.Rsa.precomputedWords nB.length := by
        unfold Spec.Rsa.publicPrecompute at hw
        dsimp only at hw
        split at hw
        · cases hw
          simp only [List.length_append, Spec.Rsa.toWords, List.length_map, List.length_range,
            Spec.Rsa.precomputedWords]; omega
        · cases hw
      have len : Spec.Rsa.precomputedWords nB.length ≤ n := by
        have := congrArg List.length h
        simp only [List.length_append, Spec.Rsa.wordsAt, List.length_map, List.length_range] at this
        omega
      rw [wordsAt_take' m p len, ← h, List.append_assoc, List.take_left' hl]
  · cases h

theorem privateCallP_pub {bs1 bs2 : Fin 8 → List Byte} {s t : State}
    (hs : Context g bs1 s) (ht : Context g bs2 t) (Hs : SPreCtx g bs1 P L s) (Ht : SPreCtx g bs2 P L t)
    (argsS : PrivateArgsP g P L s) (argsT : PrivateArgsP g P L t)
    (nb : bs1 0 = bs2 0) (eb : bs1 1 = bs2 1) :
    (Proof.Rsa.privateCheckedPrecomputedContract abi stackBytes).pub
      (s.callEntry.withRegions (privateRdP g P L) (privateWrP g))
      (t.callEntry.withRegions (privateRdP g P L) (privateWrP g)) := by
  sig_pub [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
    Proof.Rsa.privateCheckedSig, abi, argSlots, argVal, argBytes]
  have sa := fun {j} (hj : j < 22) => privateArgsP_values hs argsS hj
  have ta := fun {j} (hj : j < 22) => privateArgsP_values ht argsT hj
  simp only [hs.sp, ht.sp, sa (by decide : 0 < 22), ta (by decide : 0 < 22),
    sa (by decide : 1 < 22), ta (by decide : 1 < 22),
    sa (by decide : 2 < 22), ta (by decide : 2 < 22),
    sa (by decide : 3 < 22), ta (by decide : 3 < 22),
    sa (by decide : 4 < 22), ta (by decide : 4 < 22),
    sa (by decide : 5 < 22), ta (by decide : 5 < 22),
    sa (by decide : 6 < 22), ta (by decide : 6 < 22),
    sa (by decide : 7 < 22), ta (by decide : 7 < 22),
    sa (by decide : 8 < 22), ta (by decide : 8 < 22),
    sa (by decide : 9 < 22), ta (by decide : 9 < 22),
    sa (by decide : 10 < 22), ta (by decide : 10 < 22),
    sa (by decide : 11 < 22), ta (by decide : 11 < 22),
    sa (by decide : 12 < 22), ta (by decide : 12 < 22),
    sa (by decide : 13 < 22), ta (by decide : 13 < 22),
    sa (by decide : 14 < 22), ta (by decide : 14 < 22),
    sa (by decide : 15 < 22), ta (by decide : 15 < 22),
    sa (by decide : 16 < 22), ta (by decide : 16 < 22),
    sa (by decide : 17 < 22), ta (by decide : 17 < 22),
    sa (by decide : 18 < 22), ta (by decide : 18 < 22),
    sa (by decide : 19 < 22), ta (by decide : 19 < 22),
    sa (by decide : 20 < 22), ta (by decide : 20 < 22),
    sa (by decide : 21 < 22), ta (by decide : 21 < 22),
    privateArgumentP, privateArgument, Geometry.argument, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, ite_true,
    ite_false, true_and, and_true]
  have kf : g.length < 2 ^ 32 := by have := hs.valid.maxLength; omega
  have ef : g.exponentLength < 2 ^ 32 := by have := hs.valid.exponentFits; have := hs.valid.maxLength; omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt kf, Nat.mod_eq_of_lt ef]
  have bytesN := (hs.callBytes 0).trans (nb.trans (ht.callBytes 0).symm)
  have bytesE := (hs.callBytes 1).trans (eb.trans (ht.callBytes 1).symm)
  change Spec.Rsa.bytesAt s.callEntry.mem ((g.sources 0).setWidth 64) g.length = _ at bytesN
  change Spec.Rsa.bytesAt s.callEntry.mem ((g.sources 1).setWidth 64) g.exponentLength = _ at bytesE
  have preS := Hs.key
  rw [← hs.callBytes 0, ← hs.callBytes 3, ← hs.callBytes 4, ← Hs.callWords hs] at preS
  have preT := Ht.key
  rw [← ht.callBytes 0, ← ht.callBytes 3, ← ht.callBytes 4, ← Ht.callWords ht] at preT
  have ms := pre_modulus preS
  have mt := pre_modulus preT
  have lenS : (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 0)) (g.sourceLength 0)).length = g.length := by
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]; rfl
  have lenT : (Spec.Rsa.bytesAt t.callEntry.mem (byteAddr (g.sources 0)) (g.sourceLength 0)).length = g.length := by
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]; rfl
  rw [lenS] at ms
  rw [lenT] at mt
  change some (Spec.Rsa.wordsAt s.callEntry.mem (byteAddr P) _) =
    Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.callEntry.mem ((g.sources 0).setWidth 64) g.length) at ms
  change some (Spec.Rsa.wordsAt t.callEntry.mem (byteAddr P) _) =
    Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt t.callEntry.mem ((g.sources 0).setWidth 64) g.length) at mt
  rw [bytesN] at ms
  have words := Option.some.inj (ms.trans mt.symm)
  simp only [State.callEntry_mem, hs.sp, ht.sp] at bytesN bytesE words
  simp only [Spec.Rsa.privatePrecomputedLeak]
  rw [bytesN, bytesE]
  change _ ++ List.map (·.toNat) (Spec.Rsa.wordsAt _ (byteAddr P) _) = _ ++ List.map (·.toNat) (Spec.Rsa.wordsAt _ (byteAddr P) _)
  rw [words]
  rfl
end
end VG.Proof.RsaPkcs1Sig.X86.Sgn

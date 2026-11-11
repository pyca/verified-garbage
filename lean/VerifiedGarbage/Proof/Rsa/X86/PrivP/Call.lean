module

public import VerifiedGarbage.Proof.Rsa.X86.PrivP.Pre
public import VerifiedGarbage.Proof.Rsa.X86.PrivCrtCall
public import VerifiedGarbage.Proof.Bignum.X86.CrtABI
import VerifiedGarbage.Proof.Rsa.X86.PrivCrtPre
import VerifiedGarbage.Proof.Rsa.X86.PrivRetained
import VerifiedGarbage.Proof.Rsa.X86.PrivStackWord
import VerifiedGarbage.Proof.Rsa.X86.PrivRegions
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TopP

/-! # `vg_rsa_private_checked_precomputed` on x86: the call of `vg_rsa_private_crt_precomputed`

Its precondition from the wrapper's (`crtCallP_pre`), with the primes' values
in `pre` after `n`'s, and `p q = n` from `privatePrecompute`; its result, the
same as `vg_rsa_private_crt`'s (`crtP_call`).
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86 VG.Proof.Mont.X86

/-- `privatePrecompute`'s values: `p q = n`, `n`'s `2 w` words, and the primes'. -/
theorem privatePrecompute_parts {nB pB qB : List Byte} {ws : List (BitVec 64)}
    (h : Spec.Rsa.privatePrecompute nB pB qB = some ws) :
    Spec.Rsa.os2ip pB * Spec.Rsa.os2ip qB = Spec.Rsa.os2ip nB ∧ ∃ wn : List (BitVec 64),
      wn.length = 2 * Spec.Rsa.modulusWords nB.length ∧ ws = wn ++ (Spec.Rsa.primeR2 pB ++ Spec.Rsa.primeR2 qB) := by
  unfold Spec.Rsa.privatePrecompute at h
  split at h
  · refine ⟨by assumption, ?_⟩
    unfold Spec.Rsa.publicPrecompute at h
    dsimp only at h
    split at h
    · simp only [Option.map_some, Option.some.injEq] at h
      refine ⟨_, ?_, by rw [← h, List.append_assoc]⟩
      simp only [List.length_append, Spec.Rsa.toWords, List.length_map, List.length_range]
      omega
    · cases h
  · cases h

section
variable {g : PrivGeometry} {bs : Fin 8 → List Byte} {P : BitVec 32} {L : Nat}

/-- The primes' values in `pre`, after `n`'s `2 w` words. -/
def primesRegion (g : PrivGeometry) (P : BitVec 32) (L : Nat) : Region :=
  ⟨byteAddr P + BitVec.ofNat 64 (16 * Spec.Rsa.modulusWords g.length), (L - 2 * Spec.Rsa.modulusWords g.length) * 8⟩

def crtRdP (g : PrivGeometry) (P : BitVec 32) (L : Nat) : List Region := crtRd g ++ [primesRegion g P L]
def crtWrP (g : PrivGeometry) : List Region :=
  [⟨byteAddr g.temporary, g.length⟩, g.workspaceRegion, ⟨byteAddr g.stack, 80⟩]

theorem crtArgsP_values {s : State} (h : PrivContext g bs s) (a : CrtArgsP g P L s) {j : Nat} (hj : j < 20) :
    arg (s.callEntry.withRegions (crtRdP g P L) (crtWrP g)) j = crtArgumentP g P L j := by
  rw [arg_withRegions, arg_callEntry (by rw [h.sp]; have := h.valid.stackLow; omega)
    (by rw [h.sp]; have := h.valid.stackHigh; omega)]
  change s.mem.readW (addr (s.gpr .esp) (4 * j)) 32 = _
  rw [h.address (by omega)]
  exact a j hj

theorem crtCallP_pre {s : State} (h : PrivContext g bs s) (H : PreCtx g bs P L s) (a : CrtArgsP g P L s) :
    (privateCrtPrecomputedContract abi 96).pre (s.callEntry.withRegions (crtRdP g P L) (crtWrP g)) := by
  have sa := fun {j} (hj : j < 20) => crtArgsP_values h a hj
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega
  have pfit : g.pLength < 2 ^ 32 := by have := h.valid.pFits; omega
  have qfit : g.qLength < 2 ^ 32 := by have := h.valid.qFits; omega
  have wfit : g.scratchLength < 2 ^ 32 := by have := h.valid.workspaceFit; omega
  sig_pre [privateCrtPrecomputedContract, privateCrtPrecomputedSig, Proof.Rsa.privateCrtSig, abi, argSlots, argVal,
    argBytes, stackBelow]
  simp only [sa (by decide : 0 < 20), sa (by decide : 1 < 20), sa (by decide : 2 < 20),
    sa (by decide : 3 < 20), sa (by decide : 4 < 20), sa (by decide : 5 < 20),
    sa (by decide : 6 < 20), sa (by decide : 7 < 20), sa (by decide : 8 < 20),
    sa (by decide : 9 < 20), sa (by decide : 10 < 20), sa (by decide : 11 < 20),
    sa (by decide : 12 < 20), sa (by decide : 13 < 20), sa (by decide : 14 < 20),
    sa (by decide : 15 < 20), sa (by decide : 16 < 20), sa (by decide : 17 < 20),
    sa (by decide : 18 < 20), sa (by decide : 19 < 20),
    crtArgumentP, crtArgument, PrivGeometry.argument, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff,
    ite_true, ite_false, BitVec.toNat_ofNat, Nat.mod_eq_of_lt kfit, Nat.mod_eq_of_lt pfit,
    Nat.mod_eq_of_lt qfit, Nat.mod_eq_of_lt wfit,
    argAddr_withRegions, argAddr_callEntry, h.sp, Nat.mul_zero, BitVec.add_zero]
  have temporarySub : (⟨byteAddr g.temporary, g.length⟩ : Region).Sub g.innerRegion := by
    rw [PrivGeometry.temporary, h.valid.offsetAddr (by decide)]
    exact Offset.sub_base _ (by have := h.valid.maxLength; simp only [candidateOffset, VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega)
  have outgoingSub : (⟨byteAddr g.stack, 80⟩ : Region).Sub g.innerRegion :=
    Region.sub_prefix (by decide : 80 ≤ VG.Impl.Rsa.X86.PrivChecked.frameBytes)
  have tempSources := fun i => (h.valid.stackSources i).sub_left (fun x hx => h.valid.innerSub x (temporarySub x hx))
  have tempWorkspace := h.valid.stackWorkspace.sub_left (fun x hx => h.valid.innerSub x (temporarySub x hx))
  have tempArgs : (⟨byteAddr g.temporary, g.length⟩ : Region).Disjoint ⟨byteAddr g.stack, 80⟩ := by
    rw [PrivGeometry.temporary, h.valid.offsetAddr (by decide)]
    exact Offset.disjoint_base _ (by decide : 80 ≤ candidateOffset) (by have := h.valid.maxLength; simp only [candidateOffset]; omega)
  have calleeSources := fun i => (h.valid.stackSources i).sub_left h.valid.calleeSub
  have calleeWorkspace := h.valid.stackWorkspace.sub_left h.valid.calleeSub
  have argsWorkspace := (h.valid.stackWorkspace.sub_left (fun x hx => h.valid.innerSub x (outgoingSub x hx))).symm
  have low : (g.stack - 4).toNat = g.stack.toNat - 4 := sub_toNat (k := 4) (by have := h.valid.stackLow; omega)
  have retSub : (⟨(g.stack - 4).setWidth 64, 4⟩ : Region).Sub g.calleeRegion :=
    VG.X86.below_sub (by decide : 4 ≤ 100) h.valid.stackLow
  have belowSub : (⟨(g.stack - 4).setWidth 64 - 96#64, 96⟩ : Region).Sub g.calleeRegion := by
    rw [← VG.X86.Taint.sub_setWidth (by rw [low]; have := h.valid.stackLow; omega : 96 ≤ (g.stack - 4).toNat)]
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
  -- The primes' values.
  have hlen := H.lenEq
  have pfit := H.preFit
  have w4 : 2 * Spec.Rsa.modulusWords g.length + 4 ≤ L := by
    rw [hlen]; simp only [Spec.Rsa.primeWords]; omega
  have w2 : 2 * Spec.Rsa.modulusWords g.length ≤ L := by omega
  have Lm : (L - 2 * Spec.Rsa.modulusWords g.length) % 2 ^ 32 = L - 2 * Spec.Rsa.modulusWords g.length :=
    Nat.mod_eq_of_lt (by omega)
  have pa : (P + BitVec.ofNat 32 (16 * Spec.Rsa.modulusWords g.length)).setWidth 64 =
      byteAddr P + BitVec.ofNat 64 (16 * Spec.Rsa.modulusWords g.length) := byteAddr_add (by omega)
  have pn : (P + BitVec.ofNat 32 (16 * Spec.Rsa.modulusWords g.length)).toNat =
      P.toNat + 16 * Spec.Rsa.modulusWords g.length := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  rw [Lm, pa]
  have primesSub : (⟨byteAddr P + BitVec.ofNat 64 (16 * Spec.Rsa.modulusWords g.length),
      (L - 2 * Spec.Rsa.modulusWords g.length) * 8⟩ : Region).Sub ⟨byteAddr P, 8 * L⟩ :=
    Offset.sub_base _ (by omega)
  have preIn : ∀ r ∈ bodyWrites g, Region.Disjoint ⟨byteAddr P + BitVec.ofNat 64 (16 * Spec.Rsa.modulusWords g.length),
      (L - 2 * Spec.Rsa.modulusWords g.length) * 8⟩ r := fun r hr => (H.preSep r hr).sub_left primesSub
  have pInner := preIn g.innerRegion (by simp [bodyWrites])
  have pCallee := preIn g.calleeRegion (by simp [bodyWrites])
  have pWork := preIn g.workspaceRegion (by simp [bodyWrites])
  have tempPrimes := (pInner.sub_right temporarySub).symm
  have workPrimes := pWork.symm
  have primesArgs := pInner.sub_right outgoingSub
  have retPrimes := (pCallee.sub_right retSub).symm
  have belowPrimes := (pCallee.sub_right belowSub).symm
  -- The values in `pre`, at the call.
  obtain ⟨pq, wn, hwn, hws⟩ := privatePrecompute_parts H.key
  have nl : (bs 0).length = g.length := (h.sources 0).length
  have W := hws
  rw [show L = 2 * Spec.Rsa.modulusWords g.length + (L - 2 * Spec.Rsa.modulusWords g.length) by omega,
    VG.Proof.Bignum.X86.CrtRt.wordsAt_append'] at W
  obtain ⟨-, W2⟩ := List.append_inj W (by rw [VG.Proof.Bignum.X86.CrtRt.wordsAt_length', hwn, nl])
  have Fc : Frame [⟨(g.stack - 4).setWidth 64, 4⟩] s.mem s.callEntry.mem := by
    rw [State.callEntry_mem, h.sp]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have words : Spec.Rsa.wordsAt s.callEntry.mem (byteAddr P + BitVec.ofNat 64 (16 * Spec.Rsa.modulusWords g.length))
      (L - 2 * Spec.Rsa.modulusWords g.length) = Spec.Rsa.primeR2 (bs 3) ++ Spec.Rsa.primeR2 (bs 4) := by
    rw [VG.Proof.Rsa.wordsAt_frame Fc (by omega) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      have := retPrimes.symm; rw [Nat.mul_comm (L - 2 * Spec.Rsa.modulusWords g.length) 8] at this; exact this), ← W2, show 8 * (2 * Spec.Rsa.modulusWords g.length) =
        16 * Spec.Rsa.modulusWords g.length by omega]
  have cb := fun i => h.callBytes i
  simp only [State.callEntry_mem] at cb words
  have cb0 : Spec.Rsa.bytesAt (s.mem.writeW ((s.gpr .esp - 4).setWidth 64) (s.unknowns 0)) (BitVec.setWidth 64 (g.sources 0))
      g.length = bs 0 := cb 0
  have cb3 : Spec.Rsa.bytesAt (s.mem.writeW ((s.gpr .esp - 4).setWidth 64) (s.unknowns 0)) (BitVec.setWidth 64 (g.sources 3))
      g.pLength = bs 3 := cb 3
  have cb4 : Spec.Rsa.bytesAt (s.mem.writeW ((s.gpr .esp - 4).setWidth 64) (s.unknowns 0)) (BitVec.setWidth 64 (g.sources 4))
      g.qLength = bs 4 := cb 4
  rw [h.sp] at cb0 cb3 cb4 words
  rw [low]
  simp only [Nat.mul_comm g.scratchLength 8]
  exact ⟨by have := h.valid.stackLow; omega,
    by have := h.valid.stackHigh; have := H.high; omega,
    rfl, rfl,
    tempSources 0, tempSources 2, tempSources 3, tempSources 4, tempSources 5, tempSources 6, tempSources 7,
    tempWorkspace, tempPrimes, tempArgs,
    h.valid.sourcesWorkspace 0, sourceArgs 0, h.valid.sourcesWorkspace 2, sourceArgs 2,
    h.valid.sourcesWorkspace 3, sourceArgs 3, h.valid.sourcesWorkspace 4, sourceArgs 4,
    h.valid.sourcesWorkspace 5, sourceArgs 5, h.valid.sourcesWorkspace 6, sourceArgs 6,
    h.valid.sourcesWorkspace 7, sourceArgs 7,
    workPrimes, argsWorkspace, primesArgs,
    retTemp, retSources 0, retSources 2, retSources 3, retSources 4, retSources 5, retSources 6, retSources 7,
    retWorkspace, retPrimes, retArgs,
    belowTemp, belowSources 0, belowSources 2, belowSources 3, belowSources 4, belowSources 5, belowSources 6,
    belowSources 7, belowWorkspace, belowPrimes, belowArgs,
    h.valid.temporaryFit, h.valid.sourceFits 0, h.valid.sourceFits 2, h.valid.sourceFits 3, h.valid.sourceFits 4,
    h.valid.sourceFits 5, h.valid.sourceFits 6, h.valid.sourceFits 7, h.valid.workspaceFit,
    by rw [pn]; omega,
    ⟨h.valid.minLength, h.valid.maxLength⟩, trivial, trivial,
    h.valid.pPositive, h.valid.pFits, h.valid.qPositive, h.valid.qFits, trivial, trivial, trivial, h.valid.space,
    by rw [hlen]; omega,
    by rw [cb3, cb4]; exact words,
    by rw [cb3, cb4, cb0]; exact pq⟩

end

section
variable {g : PrivGeometry} {bs : Fin 8 → List Byte} {P : BitVec 32} {L : Nat}

theorem PrivContext.outgoingWrite80 {s : State} (h : PrivContext g bs s) : InRegions s.wr (byteAddr g.stack) 80 := by
  have W := h.inner.write (d := 0) (n := 80) (by simp only [VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega)
  simpa only [BitVec.add_zero] using W

theorem PreCtx.primesRead {s : State} (H : PreCtx g bs P L s) :
    InRegions (s.rd ++ s.wr) (primesRegion g P L).base (primesRegion g P L).len := by
  have hlen := H.lenEq
  have w4 : 2 * Spec.Rsa.modulusWords g.length + 4 ≤ L := by rw [hlen]; simp only [Spec.Rsa.primeWords]; omega
  show InRegions _ (byteAddr P + BitVec.ofNat 64 (16 * Spec.Rsa.modulusWords g.length))
    ((L - 2 * Spec.Rsa.modulusWords g.length) * 8)
  exact CallLay.inRegions_sub (off := 16 * Spec.Rsa.modulusWords g.length) H.preRead (by omega)
    (by have := H.preFit; omega)

theorem crtCoversP {s : State} (h : PrivContext g bs s) (H : PreCtx g bs P L s) :
    Covers (crtRdP g P L ++ crtWrP g) (s.rd ++ s.wr) ∧ Covers (crtWrP g) s.wr := by
  have wr : Covers (crtWrP g) s.wr := (Covers.one h.temporaryWrite).cons
    ((Covers.one h.workspaceWrite).pair (Covers.one h.outgoingWrite80))
  refine ⟨Covers.append_left ?_ wr.right, wr⟩
  exact (Covers.one (h.sources 0).read).cons ((Covers.one (h.sources 2).read).cons
    ((Covers.one (h.sources 3).read).cons ((Covers.one (h.sources 4).read).cons
    ((Covers.one (h.sources 5).read).cons ((Covers.one (h.sources 6).read).cons
    ((Covers.one (h.sources 7).read).pair (Covers.one H.primesRead)))))))

theorem crtWritesP_sub (h : g.Valid) : ∀ r ∈ crtWrP g, ∃ R ∈ bodyWrites g, r.Sub R := by
  intro r hr
  simp only [crtWrP, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · refine ⟨g.innerRegion, by simp [bodyWrites], ?_⟩
    rw [PrivGeometry.temporary, h.offsetAddr (by decide)]
    exact Offset.sub_base _ (by have := h.maxLength; simp only [candidateOffset, VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega)
  · exact ⟨g.workspaceRegion, by simp [bodyWrites], fun _ hx => hx⟩
  · exact ⟨g.innerRegion, by simp [bodyWrites], Region.sub_prefix (by decide : 80 ≤ VG.Impl.Rsa.X86.PrivChecked.frameBytes)⟩

/-- The verified `vg_rsa_private_crt_precomputed` implementation the wrapper calls. -/
structure CrtPImpl where
  name : String
  code : Prog isa
  verified : Verified target code (privateCrtPrecomputedContract abi 96)
  stack : stackUse code ≤ 96
  noSp : NoSp code

theorem crtP_call (v : CrtPImpl) {s : State} (h : PrivContext g bs s) (H : PreCtx g bs P L s) (args : CrtArgsP g P L s) :
    WP isa (.call v.name v.code) s fun t => PrivContext g bs t ∧ PreCtx g bs P L t ∧
      Frame (crtWrP g ++ [g.calleeRegion]) s.mem t.mem ∧ Keeps callClobbers s t ∧ CrtOut g bs t := by
  refine WP.mono (private_call_ok h v.verified v.stack v.noSp (crtCallP_pre h H args)
    (crtCoversP h H).1 (crtCoversP h H).2 (crtWritesP_sub h.valid)) ?_
  rintro t ⟨ht, F, K, u, M, G, post⟩
  have Fb : Frame (bodyWrites g) s.mem t.mem := F.sub (calleeWrites_sub (crtWritesP_sub h.valid))
  refine ⟨ht, H.after Fb K, F, K, ?_⟩
  sig_post [privateCrtPrecomputedContract, privateCrtPrecomputedSig, Proof.Rsa.privateCrtSig, abi, argSlots, argVal,
    argBytes] at post
  have sa := fun {j} (hj : j < 20) => crtArgsP_values h args hj
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega
  have pfit : g.pLength < 2 ^ 32 := by have := h.valid.pFits; omega
  have qfit : g.qLength < 2 ^ 32 := by have := h.valid.qFits; omega
  simp only [sa (by decide : 0 < 20), sa (by decide : 2 < 20), sa (by decide : 3 < 20),
    sa (by decide : 4 < 20), sa (by decide : 6 < 20), sa (by decide : 7 < 20),
    sa (by decide : 8 < 20), sa (by decide : 9 < 20), sa (by decide : 10 < 20),
    sa (by decide : 12 < 20), sa (by decide : 14 < 20), crtArgumentP, crtArgument, PrivGeometry.argument,
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

end

end VG.Proof.Rsa.X86.PrivChecked

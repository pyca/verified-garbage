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
public import VerifiedGarbage.Proof.Rsa.X86.PrivImpl
import VerifiedGarbage.Proof.Rsa.X86.PrivCheck
public import VerifiedGarbage.Proof.Rsa.X86.PrivFnInput
import VerifiedGarbage.Proof.Rsa.X86.PrivReturn
import VerifiedGarbage.Proof.Rsa.X86.PrivRestore
import VerifiedGarbage.Proof.Rsa.X86.PrivNoSp
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Dsa.X86.RandomSignCorrect
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Rsa.PrivCheck

/-! # `vg_rsa_private_checked_precomputed` on x86: the call, the body and the function

## The call of `vg_rsa_private_crt_precomputed`

Its precondition from the wrapper's (`crtCallP_pre`), with the primes' values
in `pre` after `n`'s, and `p q = n` from `privatePrecompute`; its result, the
same as `vg_rsa_private_crt`'s (`crtP_call`).
-/

-- separate module: the body's proof builds in parallel with the precondition (`PrivP.Contract`) and the callee's constant time (`CrtRt.TimeTopP`).

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
      omega_using []
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
  rw [arg_withRegions, arg_callEntry (by rw [h.sp]; have := h.valid.stackLow; omega_using [this])
    (by rw [h.sp]; have := h.valid.stackHigh; omega_using [hj, this])]
  change s.mem.readW (addr (s.gpr .esp) (4 * j)) 32 = _
  rw [h.address (by omega_using [hj])]
  exact a j hj

theorem crtCallP_pre {s : State} (h : PrivContext g bs s) (H : PreCtx g bs P L s) (a : CrtArgsP g P L s) :
    (privateCrtPrecomputedContract abi 96).pre (s.callEntry.withRegions (crtRdP g P L) (crtWrP g)) := by
  have sa := fun {j} (hj : j < 20) => crtArgsP_values h a hj
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega_using [this]
  have pfit : g.pLength < 2 ^ 32 := by have := h.valid.pFits; omega_using [kfit, this]
  have qfit : g.qLength < 2 ^ 32 := by have := h.valid.qFits; omega_using [kfit, this]
  have wfit : g.scratchLength < 2 ^ 32 := by have := h.valid.workspaceFit; omega_using [this]
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
    exact Offset.sub_base _ (by have := h.valid.maxLength; simp only [candidateOffset, VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega_using [this])
  have outgoingSub : (⟨byteAddr g.stack, 80⟩ : Region).Sub g.innerRegion :=
    Region.sub_prefix (by decide : 80 ≤ VG.Impl.Rsa.X86.PrivChecked.frameBytes)
  have tempSources := fun i => (h.valid.stackSources i).sub_left (fun x hx => h.valid.innerSub x (temporarySub x hx))
  have tempWorkspace := h.valid.stackWorkspace.sub_left (fun x hx => h.valid.innerSub x (temporarySub x hx))
  have tempArgs : (⟨byteAddr g.temporary, g.length⟩ : Region).Disjoint ⟨byteAddr g.stack, 80⟩ := by
    rw [PrivGeometry.temporary, h.valid.offsetAddr (by decide)]
    exact Offset.disjoint_base _ (by decide : 80 ≤ candidateOffset) (by have := h.valid.maxLength; simp only [candidateOffset]; omega_using [kfit])
  have calleeSources := fun i => (h.valid.stackSources i).sub_left h.valid.calleeSub
  have calleeWorkspace := h.valid.stackWorkspace.sub_left h.valid.calleeSub
  have argsWorkspace := (h.valid.stackWorkspace.sub_left (fun x hx => h.valid.innerSub x (outgoingSub x hx))).symm
  have low : (g.stack - 4).toNat = g.stack.toNat - 4 := sub_toNat (k := 4) (by have := h.valid.stackLow; omega_using [this])
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
  -- The primes' values.
  have hlen := H.lenEq
  have pfit := H.preFit
  have w4 : 2 * Spec.Rsa.modulusWords g.length + 4 ≤ L := by
    rw [hlen]; simp only [Spec.Rsa.primeWords]; omega_using []
  have w2 : 2 * Spec.Rsa.modulusWords g.length ≤ L := by omega_using [hlen]
  have Lm : (L - 2 * Spec.Rsa.modulusWords g.length) % 2 ^ 32 = L - 2 * Spec.Rsa.modulusWords g.length :=
    Nat.mod_eq_of_lt (by omega_using [pfit])
  have pa : (P + BitVec.ofNat 32 (16 * Spec.Rsa.modulusWords g.length)).setWidth 64 =
      byteAddr P + BitVec.ofNat 64 (16 * Spec.Rsa.modulusWords g.length) := byteAddr_add (by omega_using [pfit, w4])
  have pn : (P + BitVec.ofNat 32 (16 * Spec.Rsa.modulusWords g.length)).toNat =
      P.toNat + 16 * Spec.Rsa.modulusWords g.length := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [pfit, w4]
  rw [Lm, pa]
  have primesSub : (⟨byteAddr P + BitVec.ofNat 64 (16 * Spec.Rsa.modulusWords g.length),
      (L - 2 * Spec.Rsa.modulusWords g.length) * 8⟩ : Region).Sub ⟨byteAddr P, 8 * L⟩ :=
    Offset.sub_base _ (by omega_using [hlen])
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
  rw [show L = 2 * Spec.Rsa.modulusWords g.length + (L - 2 * Spec.Rsa.modulusWords g.length) by omega_using [hlen],
    VG.Proof.Bignum.X86.CrtRt.wordsAt_append'] at W
  obtain ⟨-, W2⟩ := List.append_inj W (by rw [VG.Proof.Bignum.X86.CrtRt.wordsAt_length', hwn, nl])
  have Fc : Frame [⟨(g.stack - 4).setWidth 64, 4⟩] s.mem s.callEntry.mem := by
    rw [State.callEntry_mem, h.sp]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have words : Spec.Rsa.wordsAt s.callEntry.mem (byteAddr P + BitVec.ofNat 64 (16 * Spec.Rsa.modulusWords g.length))
      (L - 2 * Spec.Rsa.modulusWords g.length) = Spec.Rsa.primeR2 (bs 3) ++ Spec.Rsa.primeR2 (bs 4) := by
    rw [VG.Proof.Rsa.wordsAt_frame Fc (by omega_using [pfit]) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      have := retPrimes.symm; rw [Nat.mul_comm (L - 2 * Spec.Rsa.modulusWords g.length) 8] at this; exact this), ← W2, show 8 * (2 * Spec.Rsa.modulusWords g.length) =
        16 * Spec.Rsa.modulusWords g.length by omega_using []]
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
  exact ⟨by have := h.valid.stackLow; omega_using [this],
    by have := h.valid.stackHigh; have := H.high; omega_arith,
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
    by rw [pn]; omega_using [hlen, pfit],
    ⟨h.valid.minLength, h.valid.maxLength⟩, trivial, trivial,
    h.valid.pPositive, h.valid.pFits, h.valid.qPositive, h.valid.qFits, trivial, trivial, trivial, h.valid.space,
    by rw [hlen]; omega_using [],
    by rw [cb3, cb4]; exact words,
    by rw [cb3, cb4, cb0]; exact pq⟩

end

section
variable {g : PrivGeometry} {bs : Fin 8 → List Byte} {P : BitVec 32} {L : Nat}

theorem PrivContext.outgoingWrite80 {s : State} (h : PrivContext g bs s) : InRegions s.wr (byteAddr g.stack) 80 := by
  have W := h.inner.write (d := 0) (n := 80) (by simp only [VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega_using [])
  simpa only [BitVec.add_zero] using W

theorem PreCtx.primesRead {s : State} (H : PreCtx g bs P L s) :
    InRegions (s.rd ++ s.wr) (primesRegion g P L).base (primesRegion g P L).len := by
  have hlen := H.lenEq
  have w4 : 2 * Spec.Rsa.modulusWords g.length + 4 ≤ L := by rw [hlen]; simp only [Spec.Rsa.primeWords]; omega_using []
  show InRegions _ (byteAddr P + BitVec.ofNat 64 (16 * Spec.Rsa.modulusWords g.length))
    ((L - 2 * Spec.Rsa.modulusWords g.length) * 8)
  exact CallLay.inRegions_sub (off := 16 * Spec.Rsa.modulusWords g.length) H.preRead (by omega_using [hlen])
    (by have := H.preFit; omega_using [this])

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
    exact Offset.sub_base _ (by have := h.maxLength; simp only [candidateOffset, VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega_using [this])
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
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega_using [this]
  have pfit : g.pLength < 2 ^ 32 := by have := h.valid.pFits; omega_using [kfit, this]
  have qfit : g.qLength < 2 ^ 32 := by have := h.valid.qFits; omega_using [kfit, this]
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

/-! ## the body

`vg_rsa_private_checked`'s, with `vg_rsa_private_crt_precomputed` called in
place of `vg_rsa_private_crt` (`privateBodyP_ok`).
-/

namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86 VG.Proof.Mont.X86

theorem privateBodyP_ok (v : CrtImpl) (w : CrtPImpl) {g : PrivGeometry} {bs : Fin 8 → List Byte} {P : BitVec 32}
    {L : Nat} (s : State) (h : PrivContext g bs s) (H : PreCtx g bs P L s) :
    WP isa (bodyP w.name w.code v.pcName v.pc v.pdName v.pd) s fun t =>
      Spec.Rsa.writtenOutcome t.mem (byteAddr g.output) g.length (t.gpr .eax)
        (Spec.Rsa.privateChecked (bs 0) (bs 1) (bs 2) (bs 3) (bs 4) (bs 5) (bs 6) (bs 7)) ∧
      Spec.Rsa.bytesAt t.mem (byteAddr g.temporary) g.length = List.replicate g.length 0 ∧
      Frame (bodyWrites g) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s t := by
  unfold bodyP
  refine WP.seq (WP.mono (crtArgsP_ok s h H) ?_)
  rintro u ⟨hu, Hu, argsU, frameU, restU⟩
  refine WP.seq (WP.mono (crtP_call w hu Hu argsU) ?_)
  rintro z ⟨hz, _, frameZ, restZ, crt⟩
  refine WP.mono (check_ok v z hz) ?_
  rintro t ⟨_, status, bytes, cleared, frameT, restT⟩
  refine ⟨?_, cleared, (frameU.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨g.innerRegion, by simp [bodyWrites], Region.sub_prefix (by decide : 80 ≤ VG.Impl.Rsa.X86.PrivChecked.frameBytes)⟩)).trans
    ((frameZ.sub (calleeWrites_sub (crtWritesP_sub h.valid))).trans frameT),
    (restU.mono (by simp)).trans ((restZ.mono (by simp [callClobbers])).trans restT)⟩
  have narrow : ((z.gpr .eax).setWidth 64).setWidth 32 = z.gpr .eax := by
    rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  have outcome := Rsa.outcome_eq (rc := (z.gpr .eax).setWidth 64)
    (r := Rsa.checkResult ((z.gpr .eax).setWidth 64) (bs 0) (bs 1) (bs 2)
      (Spec.Rsa.bytesAt z.mem (byteAddr g.temporary) g.length))
    (h.sources 0).length (h.sources 2).length (by rw [narrow]; exact crt) rfl bytes
  rw [status]
  exact outcome

end VG.Proof.Rsa.X86.PrivChecked

/-! ## the function

`vg_rsa_private_checked`'s frame around `bodyP` (`privateFnP_ok`).
-/

namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Proof.Dsa.X86 (allocated)

def privCodeP (v : CrtImpl) (w : CrtPImpl) : Prog isa := codeP w.name w.code v.pcName v.pc v.pdName v.pd

theorem privateBodyP_noSp (v : CrtImpl) (w : CrtPImpl) :
    NoSp (bodyP w.name w.code v.pcName v.pc v.pdName v.pd) := by
  unfold bodyP check
  exact .seq' (.of_all (by decide +kernel)) (.seq' (.call' w.noSp)
    (.seq' (.of_all (by decide +kernel)) (.seq' (.call' v.pcNoSp)
      (.seq' (.of_all (by decide +kernel)) (.seq' (.call' v.pdNoSp)
        (.of_all (by decide +kernel)))))))

theorem privateAllocationP_noSp (v : CrtImpl) (w : CrtPImpl) :
    NoSp (.frame (.alloc frameBytes)
      (bodyP w.name w.code v.pcName v.pc v.pdName v.pd) (.free frameBytes)) := by
  intro i hi
  simp only [instrs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | hi) | rfl
  · rfl
  · exact privateBodyP_noSp v w i hi
  · rfl

theorem privateInnerP_noSp (v : CrtImpl) (w : CrtPImpl) :
    NoSp (.seq (.frame (.alloc frameBytes)
      (bodyP w.name w.code v.pcName v.pc v.pdName v.pd) (.free frameBytes)) (.block restore)) :=
  .seq' (privateAllocationP_noSp v w) (.of_all (by decide +kernel))

theorem privateFnP_ok (v : CrtImpl) (w : CrtPImpl) (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    {P : BitVec 32} {L : Nat} (h : PrivFnInput g bs s) (H : PreCtx g bs P L (entered s)) :
    WP isa (privCodeP v w) s fun t => abiPreserved s t ∧
      Spec.Rsa.writtenOutcome t.mem (byteAddr g.output) g.length (t.gpr .eax)
        (Spec.Rsa.privateChecked (bs 0) (bs 1) (bs 2) (bs 3) (bs 4) (bs 5) (bs 6) (bs 7)) := by
  have stackFit : 16 ≤ (s.gpr .esp).toNat := by
    have := h.stackFit; unfold stackBytes at this; omega_using [this]
  have allocation : VG.Impl.Rsa.X86.PrivChecked.frameBytes ≤ ((pushed savedRegisters s).gpr .esp).toNat := by
    rw [pushed_esp, show 4 * savedRegisters.length = 16 from rfl, sub_toNat stackFit]
    have := h.stackFit
    simp only [stackBytes, VG.Impl.Rsa.X86.PrivChecked.frameBytes] at *
    omega_using [this]
  unfold privCodeP codeP
  refine WP.frame (rs := savedRegisters) (by decide) (by decide) (by decide) stackFit
    (privateInnerP_noSp v w) ?_
  refine WP.seq ?_
  refine VG.Proof.Dsa.X86.WP.alloc (by decide) allocation (privateBodyP_noSp v w) ?_
  refine WP.mono (privateBodyP_ok v w (entered s) h.context H) ?_
  rintro u ⟨result, _, frame, rest⟩
  have spU : (VG.Proof.Dsa.X86.freed VG.Impl.Rsa.X86.PrivChecked.frameBytes u).gpr .esp =
      (pushed savedRegisters s).gpr .esp := by
    rw [VG.Proof.Dsa.X86.freed_esp, rest.1 .esp (by decide)]
    exact BitVec.sub_add_cancel _ _
  have wrU : (VG.Proof.Dsa.X86.freed VG.Impl.Rsa.X86.PrivChecked.frameBytes u).wr = (pushed savedRegisters s).wr := by
    change u.wr.tail = _
    rw [rest.2.2]; rfl
  have fit : ((pushed savedRegisters s).gpr .esp).toNat + 16 ≤ 2 ^ 32 := by
    rw [pushed_esp, show 4 * savedRegisters.length = 16 from rfl, sub_toNat stackFit]
    have := (s.gpr .esp).isLt
    omega_using []
  have read (d : Nat) (hd : d + 4 ≤ 16) :
      InRegions ((VG.Proof.Dsa.X86.freed VG.Impl.Rsa.X86.PrivChecked.frameBytes u).rd ++
        (VG.Proof.Dsa.X86.freed VG.Impl.Rsa.X86.PrivChecked.frameBytes u).wr)
        (addr ((VG.Proof.Dsa.X86.freed VG.Impl.Rsa.X86.PrivChecked.frameBytes u).gpr .esp) d) 4 := by
    rw [spU, wrU, pushed_wr]
    refine ⟨below (s.gpr .esp) 16, List.mem_append_right _ (List.mem_cons_self), ?_⟩
    change (⟨((s.gpr .esp - 16).setWidth 64), 16⟩ : Region).Contains
      (((pushed savedRegisters s).gpr .esp + BitVec.ofNat 32 d).setWidth 64) 4
    rw [show (s.gpr .esp - 16) = (pushed savedRegisters s).gpr .esp from (pushed_esp savedRegisters s).symm]
    change (⟨byteAddr ((pushed savedRegisters s).gpr .esp), 16⟩ : Region).Contains
      (byteAddr ((pushed savedRegisters s).gpr .esp + BitVec.ofNat 32 d)) 4
    rw [byteAddr_add (by omega_using [fit, hd] : ((pushed savedRegisters s).gpr .esp).toNat + d < 2 ^ 32)]
    exact Offset.contains_base _ hd (by omega_using [hd])
  refine WP.mono (restore_ok (VG.Proof.Dsa.X86.freed VG.Impl.Rsa.X86.PrivChecked.frameBytes u)
    (read 4 (by decide)) (read 8 (by decide)) (read 0 (by decide))) ?_
  rintro t ⟨edi, ebp, esi, memT, restT⟩
  have spT : t.gpr .esp = (pushed savedRegisters s).gpr .esp :=
    (restT.1 .esp (by decide)).trans spU
  have words (i : Nat) (hi : i < 4) := h.savedWord frame i hi
  have mem : t.mem = u.mem := memT
  have savedEdi : t.gpr .edi = s.gpr .edi := by
    rw [edi, spU]; exact words 0 (by decide)
  have savedEbp : t.gpr .ebp = s.gpr .ebp := by
    rw [ebp, spU]; exact words 2 (by decide)
  have savedEsi : t.gpr .esi = s.gpr .esi := by
    rw [esi, spU]; exact words 1 (by decide)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [show savedRegisters.length = 4 from rfl, popped_four_value, spT, mem]
      exact words 3 (by decide)
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact savedEsi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact savedEdi
    · rw [popped_gpr _ _ _ (by decide) (by decide)]; exact savedEbp
    · rw [popped_esp, spT, pushed_esp]; exact BitVec.sub_add_cancel _ _
  · rw [popped_mem, mem]; exact h.returnWord frame
  · rw [popped_mem, popped_gpr _ _ _ (by decide) (by decide), mem,
      restT.1 .eax (by decide), VG.Proof.Dsa.X86.freed_gpr _ _ (by decide)]
    exact result
end VG.Proof.Rsa.X86.PrivChecked

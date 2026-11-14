module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyPublicCall
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyFnInput
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifySpec
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyLength
import VerifiedGarbage.Proof.Rsa.BytesFrame
public import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyRegions
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignRestore
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyNoSp
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Dsa.X86.RandomSignCorrect
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeTiming
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyEncoding
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyCmpArgs
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyEncArgs
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Verify
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.EntryTiming
import VerifiedGarbage.Proof.Rsa.X86.PrivSetupTiming
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyStatus
import VerifiedGarbage.Proof.Rsa.X86.PrivReleaseTiming
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyPublicPre
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyContractGeometry
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyPublicBytes
import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyGeometry

/-! ### `RsaPkcs1Sig.X86.VerifyBody`, which only this module used -/

section

/-! # Verification calls RSA, checks the padding, and returns the specified bit -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Sig.X86.Verify

def Precomputed (g : Geometry) (bs : Fin 5 → List Byte) (s : State) : Prop :=
  Spec.Rsa.publicPrecompute (bs 0) = some (Spec.Rsa.wordsAt s.mem (byteAddr (g.sources 4)) g.preLength)

theorem calleeFrame {g : Geometry} {bs : Fin 5 → List Byte} {s : State} {m m' : Mem}
    (h : Context g bs s) (F : Frame (publicWr g ++ [g.calleeRegion]) m m') :
    Frame (bodyWrites g) m m' := F.sub (by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact publicWrites_sub h r hr
  · obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩)

theorem body_ok (v : PublicImpl) {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) : WP isa (body v.name v.code) s fun t =>
      Context g bs t ∧ Frame (bodyWrites g) s.mem t.mem ∧ Keeps clobbers s t ∧
      (Precomputed g bs s → t.gpr .eax = verifiedResult g bs) := by
  unfold body
  refine WP.seq (WP.mono (lengthCheck_ok h) ?_)
  rintro c ⟨hc, Mc, Kc, Z⟩
  by_cases length : g.signatureLength = g.length
  · refine WP.ite false (by simp [eval, Z, length]) (by simp) (fun _ => ?_)
    refine WP.seq (WP.mono (pubArgs_ok hc) ?_)
    rintro a ⟨ha, args, Fa, Ka⟩
    refine WP.seq (WP.mono (public_call v ha args length) ?_)
    rintro b ⟨hb, Fb, Kb, out⟩
    refine WP.mono (afterPub_ok hb) ?_
    rintro t ⟨ht, value, Ft, Kt⟩
    have Fargs : Frame (bodyWrites g) s.mem a.mem := by
      rw [Mc] at Fa
      apply Fa.sub
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨g.innerRegion, by simp [bodyWrites], Region.sub_prefix (by decide)⟩
    refine ⟨ht, Fargs.trans ((calleeFrame h Fb).trans (Ft.sub ?_)),
      (Kc.mono (by decide)).trans ((Ka.mono (by decide)).trans
        ((Kb.mono (by decide)).trans Kt)), ?_⟩
    · intro r hr; obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩
    · intro cache
      have words : Spec.Rsa.wordsAt a.mem (byteAddr (g.sources 4)) g.preLength =
          Spec.Rsa.wordsAt s.mem (byteAddr (g.sources 4)) g.preLength :=
        VG.Proof.Rsa.wordsAt_frame Fargs (by
          have fit := h.valid.sourceFits 4
          change (g.sources 4).toNat + 8 * g.preLength ≤ 2 ^ 32 at fit
          omega_using [fit]) (h.sourceSeparate 4)
      have pre : Precomputed g bs a := by unfold Precomputed at cache ⊢; rw [words]; exact cache
      have result := checkedResult_eq (h.sources 0).length
        (by rw [(h.sources 3).length]; exact length) (out pre)
      exact value.trans result
  · refine WP.ite true (by simp [eval, Z, length]) (fun _ => ?_) (by simp)
    refine WP.mono (ret0_ok c) ?_
    rintro t ⟨ax, M, K⟩
    have mt := M.trans Mc
    have kt := (Kc.mono (by decide : ∀ r ∈ [.eax], r ∈ clobbers)).trans (K.mono (by decide))
    refine ⟨h.after (by rw [mt]; exact Frame.refl _ _) kt (kt.1 .esp (by decide)),
      by rw [mt]; exact Frame.refl _ _, kt, ?_⟩
    intro _
    rw [verifiedResult_bad h length]
    exact ax

end VG.Proof.RsaPkcs1Sig.X86.Ver

end

end

/-! ### `RsaPkcs1Sig.X86.VerifyStages`, which only this module used -/

section

/-! # Intermediate verifier states used to compose independent executions -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Verify

structure EncodeReady (g : Geometry) (bs : Fin 5 → List Byte) (s : State) : Prop where
  context : Context g bs s
  dst : s.gpr .edi = g.em2
  len : s.gpr .ecx = BitVec.ofNat 32 g.length
  hash : s.gpr .edx = g.hash
  src : s.gpr .esi = g.sources 2
  count : s.gpr .ebp = BitVec.ofNat 32 g.digestLength

structure EncodeDone (g : Geometry) (bs : Fin 5 → List Byte) (s : State) : Prop where
  context : Context g bs s
  encoded : Encoded g bs s

structure CompareReady (g : Geometry) (bs : Fin 5 → List Byte) (s : State) : Prop where
  context : Context g bs s
  src : s.gpr .esi = g.em1
  dst : s.gpr .edi = g.em2
  count : s.gpr .ecx = BitVec.ofNat 32 g.length

structure CallReady (g : Geometry) (bs : Fin 5 → List Byte) (s : State) : Prop where
  context : Context g bs s
  args : Arguments g (publicArgument g) 10 s

theorem encArgs_ready {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) : WP isa (.block encArgs) s (EncodeReady g bs) := by
  refine WP.mono (encArgs_ok h) ?_
  rintro t ⟨ht, _, _, dst, len, hash, src, count⟩
  exact ⟨ht, dst, len, hash, src, count⟩

theorem encode_done {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : EncodeReady g bs s) : WP isa VG.Impl.RsaPkcs1Sig.X86.encode s (EncodeDone g bs) := by
  refine WP.mono (encoding_ok h.context h.dst h.len h.hash h.src h.count) ?_
  rintro t ⟨ht, _, _, enc⟩
  exact ⟨ht, enc⟩

theorem cmpArgs_ready {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) : WP isa (.block cmpArgs) s (CompareReady g bs) := by
  refine WP.mono (cmpArgs_ok h) ?_
  rintro t ⟨ht, _, _, src, dst, cnt⟩
  exact ⟨ht, src, dst, cnt⟩

theorem compare_done {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : CompareReady g bs s) : WP isa VG.Impl.RsaPkcs1Sig.X86.compare s (Context g bs) := by
  refine WP.mono (compare_ok h.context h.src h.dst h.count) ?_
  rintro t ⟨ht, _, _, _⟩
  exact ht

theorem callArgs_ready {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) : WP isa (.block pubArgs) s (CallReady g bs) := by
  refine WP.mono (pubArgs_ok h) ?_
  rintro t ⟨ht, args, _, _⟩
  exact ⟨ht, args⟩

theorem publicCall_ready (v : PublicImpl) {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : CallReady g bs s) (len : g.signatureLength = g.length) :
    WP isa (.call v.name v.code) s (Context g bs) := by
  refine WP.mono (public_call v h.context h.args len) ?_
  rintro t ⟨ht, _, _, _⟩
  exact ht

theorem encoded_status {g : Geometry} {bs : Fin 5 → List Byte} {s t : State}
    (hs : EncodeDone g bs s) (ht : EncodeDone g bs t) : s.gpr .eax = t.gpr .eax := by
  have left := hs.encoded
  have right := ht.encoded
  unfold Encoded at left right
  cases e : encodeId g.hash (bs 2) g.length with
  | none =>
    rw [e] at left right
    exact left.trans right.symm
  | some em =>
    rw [e] at left right
    exact left.1.trans right.1.symm

end VG.Proof.RsaPkcs1Sig.X86.Ver

end

end

/-! ### `RsaPkcs1Sig.X86.VerifyBlocksTiming`, which only this module used -/

section

/-! # Public stack addresses suffice for every verifier straight-line fragment -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Verify VG.Proof.Dsa.X86

theorem encArgs_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block encArgs)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem pubArgs_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block pubArgs)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem cmpArgs_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block cmpArgs)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem restore_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block VG.Impl.RsaPkcs1Sig.X86.Sign.restore)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem save_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block [.store (stackAt statusOffset) .eax])
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem result_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block result)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem length_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block lenCheck)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem ret0_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) ret0
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem cmp_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .eax])) (.block test0)
    (VG.X86.Taint.Agree (τr [.esp, .eax])) := checkedBlockInvariant rfl rfl

end VG.Proof.RsaPkcs1Sig.X86.Ver

end

end

/-! ### `RsaPkcs1Sig.X86.VerifyCallPublic`, which only this module used -/

section

/-! # The nested public operation observes only the shared exponent and key words -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.Proof.Bignum.X86

theorem Context.words_equal {g : Geometry} {bs : Fin 5 → List Byte} {s t : State}
    (hs : Context g bs s) (ht : Context g bs t) :
    Spec.Rsa.wordsAt s.mem (byteAddr (g.sources 4)) g.preLength =
      Spec.Rsa.wordsAt t.mem (byteAddr (g.sources 4)) g.preLength := by
  unfold Spec.Rsa.wordsAt
  refine List.map_congr_left ?_
  intro i hi
  have hi := List.mem_range.mp hi
  apply Mem.readW_congr
  intro j hj
  rw [Offset.add_add]
  have bound : 8 * i + j < (bs 4).length := by
    rw [(hs.sources 4).length]
    change 8 * i + j < 8 * g.preLength
    omega_using [hi, hj]
  rw [(hs.sources 4).byte _ bound, (ht.sources 4).byte _ bound]

theorem publicCall_pub {g : Geometry} {bs : Fin 5 → List Byte} {s t : State}
    (hs : Context g bs s) (ht : Context g bs t)
    (argsS : Arguments g (publicArgument g) 10 s) (argsT : Arguments g (publicArgument g) 10 t) :
    (Proof.Rsa.publicPrecomputedCheckedContract abi 96).pub
      (s.callEntry.withRegions (publicRd g) (publicWr g)) (t.callEntry.withRegions (publicRd g) (publicWr g)) := by
  sig_pub [Proof.Rsa.publicPrecomputedCheckedContract, Proof.Rsa.publicPrecomputedSig, abi, argSlots, argVal, argBytes]
  have sa := fun {j} (hj : j < 10) => publicArgs_values hs argsS hj
  have ta := fun {j} (hj : j < 10) => publicArgs_values ht argsT hj
  simp only [hs.sp, ht.sp, sa (by decide : 0 < 10), ta (by decide : 0 < 10),
    sa (by decide : 1 < 10), ta (by decide : 1 < 10), sa (by decide : 2 < 10), ta (by decide : 2 < 10),
    sa (by decide : 3 < 10), ta (by decide : 3 < 10), sa (by decide : 4 < 10), ta (by decide : 4 < 10),
    sa (by decide : 5 < 10), ta (by decide : 5 < 10), sa (by decide : 6 < 10), ta (by decide : 6 < 10),
    sa (by decide : 7 < 10), ta (by decide : 7 < 10), sa (by decide : 8 < 10), ta (by decide : 8 < 10),
    sa (by decide : 9 < 10), ta (by decide : 9 < 10), publicArgument, true_and, and_true]
  have ef : g.exponentLength < 2 ^ 32 := by have := hs.valid.exponentFits; have := hs.valid.maxLength; omega_arith
  have pf : g.preLength < 2 ^ 32 := by
    have fit := hs.valid.sourceFits 4
    change (g.sources 4).toNat + 8 * g.preLength ≤ 2 ^ 32 at fit
    omega_using [fit]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ef, Nat.mod_eq_of_lt pf]
  have bytes := (hs.callBytes 1).trans (ht.callBytes 1).symm
  have words := hs.callWords.trans ((hs.words_equal ht).trans ht.callWords.symm)
  change Spec.Rsa.bytesAt s.callEntry.mem ((g.sources 1).setWidth 64) g.exponentLength = _ at bytes
  simp only [State.callEntry_mem, hs.sp, ht.sp] at bytes words
  simp only [byteAddr] at words
  rw [bytes, words]
  rfl

end VG.Proof.RsaPkcs1Sig.X86.Ver

end

end

/-! ### `RsaPkcs1Sig.X86.VerifyObservations`, which only this module used -/

section

/-! # The shared verifier leakage fixes every immutable input byte -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.Proof.Bignum.X86

theorem arguments {s t : State} (H : (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi verifyStack).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < 13, arg s i = arg t i := by
  sig_pub [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  constructor
  · with_reducible assumption
  · intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 by omega_using [hi]) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem publicGeometry {s t : State} (H : (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi verifyStack).pub s t) :
    verifyGeometry s = verifyGeometry t := by
  obtain ⟨sp, args⟩ := arguments H
  have sources : (verifyGeometry s).sources = (verifyGeometry t).sources := by
    funext i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega_using []) with rfl | rfl | rfl | rfl | rfl
    exacts [args 0 (by decide), args 2 (by decide), args 5 (by decide), args 7 (by decide), args 11 (by decide)]
  simp only [verifyGeometry, sp, args 9 (by decide), args 1 (by decide), args 4 (by decide),
    args 3 (by decide), args 6 (by decide), args 8 (by decide), args 12 (by decide), args 10 (by decide)]
  exact congrArg (fun ps => Geometry.mk _ _ ps _ _ _ _ _ _ _) sources

theorem publicBytes {s t : State} (H : (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi verifyStack).pub s t) :
    verifyBytes s = verifyBytes t := by
  have args := (arguments H).2
  have geometry := publicGeometry H
  have Leak : (verifyBytes s 0 ++ verifyBytes s 1 ++ verifyBytes s 2 ++ verifyBytes s 3).map (·.toNat) ++
      (Spec.Rsa.wordsAt s.mem (byteAddr ((verifyGeometry s).sources 4)) (verifyGeometry s).preLength).map (·.toNat) =
      (verifyBytes t 0 ++ verifyBytes t 1 ++ verifyBytes t 2 ++ verifyBytes t 3).map (·.toNat) ++
      (Spec.Rsa.wordsAt t.mem (byteAddr ((verifyGeometry t).sources 4)) (verifyGeometry t).preLength).map (·.toNat) := by
    sig_pub [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig, abi, argSlots, argVal, argBytes] at H
    exact H.2.1
  have wordLength : ((Spec.Rsa.wordsAt s.mem (byteAddr ((verifyGeometry s).sources 4)) (verifyGeometry s).preLength).map (·.toNat)).length =
      ((Spec.Rsa.wordsAt t.mem (byteAddr ((verifyGeometry t).sources 4)) (verifyGeometry t).preLength).map (·.toNat)).length := by
    simp only [List.length_map, Spec.Rsa.wordsAt, List.length_range, geometry]
  have both := List.append_inj' Leak wordLength
  have bytes := (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp both.1
  have words := (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp both.2
  have lengths (i : Fin 5) : (verifyBytes s i).length = (verifyBytes t i).length := by
    simp only [verifyBytes, Spec.Rsa.bytesAt, List.length_map, List.length_range, geometry]
  simp only [List.append_assoc] at bytes
  have first := List.append_inj_left bytes (lengths 0)
  have rest := List.append_inj_right bytes (lengths 0)
  have second := List.append_inj_left rest (lengths 1)
  have tail := List.append_inj_right rest (lengths 1)
  have third := List.append_inj_left tail (lengths 2)
  have fourth := List.append_inj_right tail (lengths 2)
  have fifth : verifyBytes s 4 = verifyBytes t 4 := by
    rw [geometry] at words
    unfold verifyBytes
    rw [geometry]
    exact bytesAt_of_words words
  funext i
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega_using []) with rfl | rfl | rfl | rfl | rfl
  exacts [first, second, third, fourth, fifth]

end VG.Proof.RsaPkcs1Sig.X86.Ver

end

end

/-! ### `RsaPkcs1Sig.X86.VerifyContractInput`, which only this module used -/

section

/-! # Decode the shared verifier precondition into its frame and input geometry -/

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/VerifyABI.lean`, which only this module imported.
section

/-! # Resources supplied by the shared precomputed-verification signature -/

section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86
open VG.Proof.Dsa.X86 (argumentPointer)

structure VerifyABI (s : State) : Prop where
  stackLow : verifyStack ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 56 ≤ 2 ^ 32
  rd : s.rd = [⟨argumentPointer s 0, (arg s 1).toNat⟩, ⟨argumentPointer s 2, (arg s 3).toNat⟩, ⟨argumentPointer s 5, (arg s 6).toNat⟩, ⟨argumentPointer s 7, (arg s 8).toNat⟩, ⟨argumentPointer s 11, 8 * (arg s 12).toNat⟩]
  wr : s.wr = [⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩, ⟨argAddr s 0, 52⟩]
  sourceWorkspace0 : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩
  sourceWorkspace1 : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩
  sourceWorkspace2 : (⟨argumentPointer s 5, (arg s 6).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩
  sourceWorkspace3 : (⟨argumentPointer s 7, (arg s 8).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩
  sourceWorkspace4 : (⟨argumentPointer s 11, 8 * (arg s 12).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩
  workspaceArguments : (⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 52⟩
  stackSource0 : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat⟩
  stackSource1 : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  stackSource2 : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨argumentPointer s 5, (arg s 6).toNat⟩
  stackSource3 : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨argumentPointer s 7, (arg s 8).toNat⟩
  stackSource4 : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨argumentPointer s 11, 8 * (arg s 12).toNat⟩
  stackWorkspace : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩
  stackArguments : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 verifyStack, verifyStack⟩ : Region).Disjoint ⟨argAddr s 0, 52⟩
  returnWorkspace : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩
  sourceFit0 : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  sourceFit1 : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  sourceFit2 : (arg s 5).toNat + (arg s 6).toNat ≤ 2 ^ 32
  sourceFit3 : (arg s 7).toNat + (arg s 8).toNat ≤ 2 ^ 32
  sourceFit4 : (arg s 11).toNat + 8 * (arg s 12).toNat ≤ 2 ^ 32
  workspaceFit : (arg s 9).toNat + 8 * (arg s 10).toNat ≤ 2 ^ 32
  valid : Spec.Rsa.lenValid (arg s 1).toNat
  ePositive : 1 ≤ (arg s 3).toNat
  eFits : (arg s 3).toNat ≤ (arg s 1).toNat
  space : Spec.Rsa.publicScratchWords (arg s 1).toNat ≤ (arg s 10).toNat
  preLength : (arg s 12).toNat = Spec.Rsa.precomputedWords (arg s 1).toNat

theorem verifyABI_of {s : State} (h : (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi verifyStack).pre s) : VerifyABI s := by
  sig_pre [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig,
    abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> simp only [verifyStack, Nat.mul_comm 8] at *
  all_goals first
    | with_reducible assumption
    | exact Region.Disjoint.symm (by with_reducible assumption)

end VG.Proof.RsaPkcs1Sig.X86.Ver
end

end

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/VerifyEntryInput.lean`, which only this module imported.
section

/-! # Native cdecl inputs before reserving the two wrapper frames -/

section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.Proof.Rsa.X86.PrivChecked VG.Impl.RsaPkcs1Sig.X86.Verify VG.Proof.Bignum.X86
open VG.Proof.Dsa.X86 (allocated)

structure EntryInput (g : Geometry) (bs : Fin 5 → List Byte) (s : State) : Prop where
  valid : g.Valid
  stackFit : verifyStack ≤ (s.gpr .esp).toNat
  base : g.stack = s.gpr .esp - 16 - BitVec.ofNat 32 VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes
  source : ∀ i, PublicBytes (g.sources i) (g.sourceLength i) (bs i) s
  workspaceWrite : InRegions s.wr (byteAddr g.workspace) (8 * g.scratchLength)
  argumentsRead : InRegions (s.rd ++ s.wr) g.argumentsRegion.base 52
  arguments : ∀ j < 13, s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 20 + 4 * j)) 32 = g.argument j
  returnSeparate : ∀ r ∈ bodyWrites g, (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r

theorem EntryInput.enteredSp {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : EntryInput g bs s) : (entered s).gpr .esp = g.stack := by
  rw [entered, VG.Proof.Dsa.X86.allocated_esp, pushed_esp]
  exact h.base.symm

theorem EntryInput.savedAddr {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : EntryInput g bs s) : ((pushed savedRegisters s).gpr .esp).setWidth 64 = g.savedRegion.base := by
  have eq : (pushed savedRegisters s).gpr .esp = g.stack + BitVec.ofNat 32 VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes := by
    rw [← h.enteredSp]
    exact (BitVec.sub_add_cancel _ _).symm
  rw [eq]
  exact h.valid.offsetAddr (by decide)

theorem EntryInput.enteredFrame {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : EntryInput g bs s) : Frame [g.savedRegion] s.mem (entered s).mem := by
  have f := pushed_frame (rs := savedRegisters) (s := s) (by decide)
    (by change 16 ≤ _; have := h.stackFit; unfold verifyStack at this; omega)
  unfold below at f
  rw [← pushed_esp] at f
  change Frame [⟨((pushed savedRegisters s).gpr .esp).setWidth 64, 16⟩] s.mem (entered s).mem at f
  rw [h.savedAddr] at f
  exact f

theorem entered_read {s : State} {p : Addr} {n : Nat} (read : InRegions (s.rd ++ s.wr) p n) :
    InRegions ((entered s).rd ++ (entered s).wr) p n := by
  obtain ⟨r, hr, hc⟩ := read
  refine ⟨r, ?_, hc⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact List.mem_append_left _ hr
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))

theorem entered_write {s : State} {p : Addr} {n : Nat} (write : InRegions s.wr p n) :
    InRegions (entered s).wr p n := by
  obtain ⟨r, hr, hc⟩ := write
  exact ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), hc⟩
end VG.Proof.RsaPkcs1Sig.X86.Ver
end

end

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/VerifyEntryReady.lean`, which only this module imported.
section

/-! # Entering the wrapper preserves all sources and incoming arguments -/

section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.Proof.Rsa.X86.PrivChecked VG.Proof.Bignum.X86

theorem EntryInput.enteredSource {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : EntryInput g bs s) (i : Fin 5) :
    PublicBytes (g.sources i) (g.sourceLength i) (bs i) (entered s) := by
  refine ⟨(h.source i).fits, entered_read (h.source i).read, ?_⟩
  have sep : ∀ r ∈ [g.savedRegion], (g.sourceRegion i).Disjoint r := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ((h.valid.stackSources i).sub_left h.valid.savedSub).symm
  exact (Rsa.rsa_bytes_frame h.enteredFrame (by have := (h.source i).fits; omega) sep).trans (h.source i).bytes

theorem EntryInput.enteredArguments {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : EntryInput g bs s) (j : Nat) (hj : j < 13) :
    (entered s).mem.readW (byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 20 + 4 * j)) 32 = g.argument j := by
  have sep : ∀ r ∈ [g.savedRegion], g.argumentsRegion.Disjoint r := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact (h.valid.stackArguments.sub_left h.valid.savedSub).symm
  have eq := h.enteredFrame.readW (r := g.argumentsRegion)
    (Offset.contains_base _ (by omega : 4 * j + 32 / 8 ≤ 52) (by omega)) sep (by decide : 32 / 8 < 2 ^ 64)
  have address : g.argumentsRegion.base + BitVec.ofNat 64 (4 * j) =
      byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 20 + 4 * j) :=
    Offset.add_add _ _ _
  change (entered s).mem.readW (g.argumentsRegion.base + BitVec.ofNat 64 (4 * j)) 32 =
    s.mem.readW (g.argumentsRegion.base + BitVec.ofNat 64 (4 * j)) 32 at eq
  rw [address] at eq
  exact eq.trans (h.arguments j hj)

theorem EntryInput.ready {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : EntryInput g bs s) : FnInput g bs s := by
  refine ⟨h.stackFit, ⟨h.valid, h.enteredSp, ?_, h.enteredSource,
    entered_write h.workspaceWrite,
    entered_read h.argumentsRead, h.enteredArguments⟩, h.returnSeparate⟩
  refine ⟨by have := h.valid.stackHigh; omega, ?_⟩
  change (⟨byteAddr g.stack, VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes⟩ : Region) ∈
    ⟨byteAddr ((entered s).gpr .esp), VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes⟩ :: (pushed savedRegisters s).wr
  rw [h.enteredSp]
  exact List.mem_cons_self
end VG.Proof.RsaPkcs1Sig.X86.Ver
end

end

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.Proof.Bignum.X86
open VG.Proof.Dsa.X86 (argumentPointer)

theorem verify_contract_pre (s : State) (pre : (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi verifyStack).pre s) :
    FnInput (verifyGeometry s) (verifyBytes s) s := by
  have h := verifyABI_of pre
  have fits : ∀ i, ((verifyGeometry s).sources i).toNat + (verifyGeometry s).sourceLength i ≤ 2 ^ 32 := by
    intro i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega_using []) with rfl | rfl | rfl | rfl | rfl
    exacts [h.sourceFit0, h.sourceFit1, h.sourceFit2, h.sourceFit3, h.sourceFit4]
  have geometry : (verifyGeometry s).Valid := by
    refine ⟨h.valid.1, h.valid.2, h.ePositive, h.eFits, (arg s 6).isLt, (arg s 8).isLt,
      h.preLength, h.space, ?_, ?_, fits, h.workspaceFit, ?_, ?_, ?_, ?_, ?_⟩
    · rw [verifyGeometry_stackNat s h.stackLow]
      have := h.stackLow
      simp only [verifyStack] at this
      omega_using [this]
    · rw [verifyGeometry_stackNat s h.stackLow]
      have := h.stackBound
      simp only [VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes]
      omega_using [this]
    · intro i
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega_using []) with rfl | rfl | rfl | rfl | rfl
      exacts [h.sourceWorkspace0, h.sourceWorkspace1, h.sourceWorkspace2, h.sourceWorkspace3, h.sourceWorkspace4]
    · rw [verifyGeometry_arguments s h.stackLow h.stackBound]; exact h.workspaceArguments
    · intro i
      rw [verifyGeometry_wholeStack s h.stackLow]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega_using []) with rfl | rfl | rfl | rfl | rfl
      exacts [h.stackSource0, h.stackSource1, h.stackSource2, h.stackSource3, h.stackSource4]
    · rw [verifyGeometry_wholeStack s h.stackLow]; exact h.stackWorkspace
    · rw [verifyGeometry_wholeStack s h.stackLow, verifyGeometry_arguments s h.stackLow h.stackBound]
      exact h.stackArguments
  apply EntryInput.ready
  refine ⟨geometry, h.stackLow, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨fits i, ?_, rfl⟩
    refine ⟨(verifyGeometry s).sourceRegion i, List.mem_append_left _ ?_, Region.contains_self _ _⟩
    rw [h.rd]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega_using []) with rfl | rfl | rfl | rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  · rw [h.wr]
    exact ⟨_, by simp [verifyGeometry, byteAddr, argumentPointer], Region.contains_self _ _⟩
  · rw [verifyGeometry_arguments s h.stackLow h.stackBound]
    exact ⟨_, List.mem_append_right _ (by rw [h.wr]; simp), Region.contains_self _ _⟩
  · intro j hj
    have address : byteAddr (verifyGeometry s).stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 20 + 4 * j) = argAddr s j := by
      rw [← Offset.add_add]
      change (verifyGeometry s).argumentsRegion.base + BitVec.ofNat 64 (4 * j) = _
      rw [verifyGeometry_arguments s h.stackLow h.stackBound]
      simp only [argAddr, Nat.mul_zero, Nat.add_zero]
      have bound := h.stackBound
      have first := byteAddr_add (by omega_using [bound] : (s.gpr .esp).toNat + 4 < 2 ^ 32)
      have last := byteAddr_add (by omega_using [hj, bound] : (s.gpr .esp).toNat + (4 + 4 * j) < 2 ^ 32)
      change byteAddr (s.gpr .esp + BitVec.ofNat 32 4) + BitVec.ofNat 64 (4 * j) = byteAddr (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * j))
      rw [first, last, Offset.add_add]
    rw [address]
    change arg s j = _
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 by omega_using [hj]) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [verifyGeometry, Geometry.argument, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    all_goals rfl
  · intro r hr
    have belowRet : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (verifyGeometry s).wholeStack := by
      rw [verifyGeometry_wholeStack s h.stackLow]
      have sep := Offset.disjoint_base ((s.gpr .esp).setWidth 64 - BitVec.ofNat 64 verifyStack)
        (Nat.le_refl verifyStack) (by decide : verifyStack + 4 ≤ 2 ^ 64)
      rw [BitVec.sub_add_cancel] at sep
      exact sep
    simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact belowRet.sub_right geometry.innerSub
    · exact belowRet.sub_right geometry.calleeSub
    · exact h.returnWorkspace

end VG.Proof.RsaPkcs1Sig.X86.Ver

end

end

/-! # Complete i686 certificate for precomputed PKCS #1 verification -/

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/VerifyReturn.lean`, which only this module imported.
section

/-! # The wrapper preserves its caller's return address -/

section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.Proof.Rsa.X86.PrivChecked VG.Impl.RsaPkcs1Sig.X86.Verify VG.Proof.Bignum.X86

theorem popped_four_value (s : State) :
    (popped .ebx 4 s).gpr .ebx = s.mem.readW ((s.gpr .esp + 12).setWidth 64) 32 := by
  change s.mem.readW ((((s.gpr .esp + 4) + 4) + 4).setWidth 64) 32 = _
  simp only [BitVec.add_assoc]
  rfl

theorem FnInput.returnWord {g : Geometry} {bs : Fin 5 → List Byte} {s t : State}
    (h : FnInput g bs s) (frame : Frame (bodyWrites g) (entered s).mem t.mem) :
    t.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
  have low : 16 ≤ (s.gpr .esp).toNat := by have := h.stackFit; unfold verifyStack at this; omega
  have savedFrame := pushed_frame (rs := savedRegisters) (s := s) (by decide) low
  have contains : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Contains ((s.gpr .esp).setWidth 64) (32 / 8) :=
    Region.contains_self _ _
  have savedSeparate : ∀ r ∈ [below (s.gpr .esp) 16],
      (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    unfold below
    rw [Taint.sub_setWidth low]
    have eq : (s.gpr .esp).setWidth 64 =
        (s.gpr .esp).setWidth 64 - 16 + BitVec.ofNat 64 16 := (BitVec.sub_add_cancel _ _).symm
    have sep := Offset.disjoint_base ((s.gpr .esp).setWidth 64 - 16)
      (by decide : 16 ≤ 16) (by decide : 16 + 4 ≤ 2 ^ 64)
    rw [← eq] at sep
    exact sep
  exact (frame.readW contains h.returnSeparate (by decide)).trans
    (savedFrame.readW contains savedSeparate (by decide))
end VG.Proof.RsaPkcs1Sig.X86.Ver
end

end

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/VerifyEntryCache.lean`, which only this module imported.
section

/-! # Saving caller registers leaves the precomputed public key unchanged -/

section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.Proof.Bignum.X86

theorem FnInput.enteredCache {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : FnInput g bs s) : Precomputed g bs (entered s) ↔ Precomputed g bs s := by
  have low : 16 ≤ (s.gpr .esp).toNat := by have := h.stackFit; unfold verifyStack at this; omega
  have F := pushed_frame (rs := savedRegisters) (s := s) (by decide) low
  have saved : ((pushed savedRegisters s).gpr .esp).setWidth 64 = g.savedRegion.base := by
    rw [h.savedSp]
    exact h.context.valid.offsetAddr (by decide)
  unfold below at F
  rw [← pushed_esp] at F
  change Frame [⟨((pushed savedRegisters s).gpr .esp).setWidth 64, 16⟩] s.mem (entered s).mem at F
  rw [saved] at F
  have words : Spec.Rsa.wordsAt (entered s).mem (byteAddr (g.sources 4)) g.preLength =
      Spec.Rsa.wordsAt s.mem (byteAddr (g.sources 4)) g.preLength :=
    VG.Proof.Rsa.wordsAt_frame F (by
      have fit := h.context.valid.sourceFits 4
      change (g.sources 4).toNat + 8 * g.preLength ≤ 2 ^ 32 at fit
      omega) (by
        intro r hr; obtain rfl := List.mem_singleton.mp hr
        exact ((h.context.valid.stackSources 4).sub_left h.context.valid.savedSub).symm)
  unfold Precomputed
  rw [words]

end VG.Proof.RsaPkcs1Sig.X86.Ver
end

end

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/VerifyFn.lean`, which only this module imported.
section

/-! # Callable PKCS #1 signing restores the i686 calling convention -/

section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Verify VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Proof.Dsa.X86 (allocated freed freed_esp freed_gpr)

theorem verifyFn_ok (v : PublicImpl) (s : State) {g : Geometry} {bs : Fin 5 → List Byte}
    (h : FnInput g bs s) :
    WP isa (code v.name v.code) s fun t => abiPreserved s t ∧
      (Precomputed g bs s → t.gpr .eax = verifiedResult g bs) := by
  have stackFit : 16 ≤ (s.gpr .esp).toNat := by
    have := h.stackFit; unfold verifyStack at this; omega
  have allocation : VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes ≤ ((pushed savedRegisters s).gpr .esp).toNat := by
    rw [pushed_esp, show 4 * savedRegisters.length = 16 from rfl, sub_toNat stackFit]
    have := h.stackFit
    simp only [verifyStack, VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes] at *
    omega
  unfold code
  refine WP.frame (rs := savedRegisters) (by decide) (by decide) (by decide) stackFit
    (inner_noSp v) ?_
  refine WP.seq ?_
  refine VG.Proof.Dsa.X86.WP.alloc (by decide) allocation (body_noSp v) ?_
  refine WP.mono (body_ok v (s := entered s) h.context) ?_
  rintro u ⟨_, frame, rest, result⟩
  have spU : (freed VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes u).gpr .esp =
      (pushed savedRegisters s).gpr .esp := by
    rw [freed_esp, rest.1 .esp (by decide)]
    exact BitVec.sub_add_cancel _ _
  have wrU : (freed VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes u).wr = (pushed savedRegisters s).wr := by
    change u.wr.tail = _
    rw [rest.2.2]; rfl
  have fit : ((pushed savedRegisters s).gpr .esp).toNat + 16 ≤ 2 ^ 32 := by
    rw [pushed_esp, show 4 * savedRegisters.length = 16 from rfl, sub_toNat stackFit]
    have := (s.gpr .esp).isLt
    omega
  have read (d : Nat) (hd : d + 4 ≤ 16) :
      InRegions ((freed VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes u).rd ++
        (freed VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes u).wr)
        (addr ((freed VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes u).gpr .esp) d) 4 := by
    rw [spU, wrU, pushed_wr]
    refine ⟨below (s.gpr .esp) 16, List.mem_append_right _ (List.mem_cons_self), ?_⟩
    change (⟨((s.gpr .esp - 16).setWidth 64), 16⟩ : Region).Contains
      (((pushed savedRegisters s).gpr .esp + BitVec.ofNat 32 d).setWidth 64) 4
    rw [show (s.gpr .esp - 16) = (pushed savedRegisters s).gpr .esp from (pushed_esp savedRegisters s).symm]
    change (⟨byteAddr ((pushed savedRegisters s).gpr .esp), 16⟩ : Region).Contains
      (byteAddr ((pushed savedRegisters s).gpr .esp + BitVec.ofNat 32 d)) 4
    rw [byteAddr_add (by omega : ((pushed savedRegisters s).gpr .esp).toNat + d < 2 ^ 32)]
    exact Offset.contains_base _ hd (by omega)
  refine WP.mono (VG.Proof.RsaPkcs1Sig.X86.Sgn.restore_ok (freed VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes u)
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
  · rw [popped_gpr _ _ _ (by decide) (by decide),
      restT.1 .eax (by decide), freed_gpr _ _ (by decide)]
    intro pre
    exact result (h.enteredCache.mpr pre)
end VG.Proof.RsaPkcs1Sig.X86.Ver
end

end

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/VerifyTailTiming.lean`, which only this module imported.
section

/-! # The padding check never branches on the precomputed RSA call's status -/

section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Sig.X86.Verify VG.Proof.Dsa.X86
open VG.Proof.Rsa.X86.PrivChecked (sp_agree pair_seq_ct)

theorem compareReady_agree {g : Geometry} {bs : Fin 5 → List Byte} {s t : State}
    (hs : CompareReady g bs s) (ht : CompareReady g bs t) : VG.X86.Taint.Agree compareTaint s t := by
  apply agree_regs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hs.dst.trans ht.dst.symm
  · exact hs.src.trans ht.src.symm
  · exact hs.count.trans ht.count.symm

theorem compareThenResult_relCT {g : Geometry} {bs : Fin 5 → List Byte} :
    RelCT isa (fun s t => Context g bs s ∧ Context g bs t)
      (.seq (.block cmpArgs) (.seq VG.Impl.RsaPkcs1Sig.X86.compare (.block result))) (fun _ _ => True) := by
  apply pair_seq_ct (cmpArgs_relCT.mono
    (fun _ _ h => sp_agree (h.1.sp.trans h.2.sp.symm)) (fun _ _ _ => trivial))
    (fun _ h => cmpArgs_ready h) (fun _ h => cmpArgs_ready h)
  apply pair_seq_ct (compare_relCT.mono (fun _ _ h => compareReady_agree h.1 h.2) (fun _ _ _ => trivial))
    (fun _ h => compare_done h) (fun _ h => compare_done h)
  exact result_relCT.mono (fun _ _ h => sp_agree (h.1.sp.trans h.2.sp.symm)) (fun _ _ _ => trivial)

structure Compared (g : Geometry) (bs : Fin 5 → List Byte) (s : State) : Prop extends EncodeDone g bs s where
  flag : s.zf = some (s.gpr .eax == 0)

theorem compare_ready {g : Geometry} {bs : Fin 5 → List Byte} {s : State} (h : EncodeDone g bs s) :
    WP isa (.block test0) s (Compared g bs) := by
  unfold test0
  refine wp_cmpS rfl fun t F Z => WP.block_nil ?_
  refine ⟨⟨h.context.after (by rw [F.mem]; exact Frame.refl _ _) (F.keeps []) (congrFun F.gpr .esp), ?_⟩, ?_⟩
  · simpa only [Encoded, F.gpr, F.mem] using h.encoded
  · rw [Z, F.gpr]
    exact congrArg some (by change (s.gpr .eax - 0#32 == 0#32) = _; rw [BitVec.sub_zero]; rfl)

theorem tail_relCT {g : Geometry} {bs : Fin 5 → List Byte} :
    RelCT isa (fun s t => EncodeDone g bs s ∧ EncodeDone g bs t) tail (fun _ _ => True) := by
  unfold tail
  apply pair_seq_ct (cmp_relCT.mono (fun s t h => agree_regs (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.context.sp.trans h.2.context.sp.symm
    · exact encoded_status h.1 h.2)) (fun _ _ _ => trivial))
    (fun _ h => compare_ready h) (fun _ h => compare_ready h)
  apply RelCT.ite
  · intro s t h
    change s.zf = t.zf
    rw [h.1.flag, h.2.flag, encoded_status h.1.toEncodeDone h.2.toEncodeDone]
  · exact ret0_relCT.mono
      (fun _ _ h => sp_agree (h.1.1.context.sp.trans h.1.2.context.sp.symm)) (fun _ _ _ => trivial)
  · exact compareThenResult_relCT.mono (fun _ _ h => ⟨h.1.1.context, h.1.2.context⟩) (fun _ _ _ => trivial)

theorem encodeReady_agree {g : Geometry} {bs : Fin 5 → List Byte} {s t : State}
    (hs : EncodeReady g bs s) (ht : EncodeReady g bs t) : VG.X86.Taint.Agree encodeTaint s t := by
  apply agree_regs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hs.dst.trans ht.dst.symm
  · exact hs.len.trans ht.len.symm
  · exact hs.hash.trans ht.hash.symm
  · exact hs.src.trans ht.src.symm
  · exact hs.count.trans ht.count.symm

theorem afterPub_relCT {g : Geometry} {bs : Fin 5 → List Byte} :
    RelCT isa (fun s t => Context g bs s ∧ Context g bs t) afterPub (fun _ _ => True) := by
  unfold afterPub
  apply pair_seq_ct (save_relCT.mono
    (fun _ _ h => sp_agree (h.1.sp.trans h.2.sp.symm)) (fun _ _ _ => trivial))
    (fun _ h => WP.mono (save_ok h) (fun _ x => x.1))
    (fun _ h => WP.mono (save_ok h) (fun _ x => x.1))
  apply pair_seq_ct (encArgs_relCT.mono
    (fun _ _ h => sp_agree (h.1.sp.trans h.2.sp.symm)) (fun _ _ _ => trivial))
    (fun _ h => encArgs_ready h) (fun _ h => encArgs_ready h)
  exact pair_seq_ct (encode_relCT.mono (fun _ _ h => encodeReady_agree h.1 h.2) (fun _ _ _ => trivial))
    (fun _ h => encode_done h) (fun _ h => encode_done h) tail_relCT

end VG.Proof.RsaPkcs1Sig.X86.Ver
end

end

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/VerifyBodyTiming.lean`, which only this module imported.
section

/-! # The verifier body relates even calls with inconsistent precomputed moduli -/

section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Verify
open VG.Proof.Rsa.X86.PrivChecked (sp_agree pair_seq_ct)

theorem publicCall_relCT (v : PublicImpl) {g : Geometry} {bs : Fin 5 → List Byte}
    (len : g.signatureLength = g.length) :
    RelCT isa (fun s t => CallReady g bs s ∧ CallReady g bs t)
      (.call v.name v.code) (fun _ _ => True) := by
  apply RelCT.call v.verified.1 v.verified.2.1 (publicRd g) (publicWr g)
  intro s t h
  exact ⟨publicCall_pre h.1.context h.1.args len, publicCall_pre h.2.context h.2.args len,
    publicCall_pub h.1.context h.2.context h.1.args h.2.args,
    (publicCovers h.1.context).1, (publicCovers h.1.context).2,
    (publicCovers h.2.context).1, (publicCovers h.2.context).2, h.1.context.sp.trans h.2.context.sp.symm⟩

theorem callThenCheck_relCT (v : PublicImpl) {g : Geometry} {bs : Fin 5 → List Byte}
    (len : g.signatureLength = g.length) :
    RelCT isa (fun s t => Context g bs s ∧ Context g bs t)
      (.seq (.block pubArgs) (.seq (.call v.name v.code) afterPub)) (fun _ _ => True) := by
  apply pair_seq_ct (pubArgs_relCT.mono
    (fun _ _ h => sp_agree (h.1.sp.trans h.2.sp.symm)) (fun _ _ _ => trivial))
    (fun _ h => callArgs_ready h) (fun _ h => callArgs_ready h)
  exact pair_seq_ct (publicCall_relCT v len) (fun _ h => publicCall_ready v h len)
    (fun _ h => publicCall_ready v h len) afterPub_relCT

structure LengthDone (g : Geometry) (bs : Fin 5 → List Byte) (s : State) : Prop where
  context : Context g bs s
  flag : s.zf = some (decide (g.signatureLength = g.length))

theorem length_done {g : Geometry} {bs : Fin 5 → List Byte} {s : State} (h : Context g bs s) :
    WP isa (.block lenCheck) s (LengthDone g bs) := by
  refine WP.mono (lengthCheck_ok h) ?_
  rintro t ⟨ht, _, _, flag⟩
  exact ⟨ht, flag⟩

theorem body_relCT (v : PublicImpl) {g : Geometry} {bs : Fin 5 → List Byte} :
    RelCT isa (fun s t => Context g bs s ∧ Context g bs t) (body v.name v.code) (fun _ _ => True) := by
  unfold body
  apply pair_seq_ct (length_relCT.mono
    (fun _ _ h => sp_agree (h.1.sp.trans h.2.sp.symm)) (fun _ _ _ => trivial))
    (fun _ h => length_done h) (fun _ h => length_done h)
  apply RelCT.ite
  · intro s t h
    change s.zf.map (! ·) = t.zf.map (! ·)
    rw [h.1.flag, h.2.flag]
  · exact ret0_relCT.mono (fun _ _ h => sp_agree (h.1.1.context.sp.trans h.1.2.context.sp.symm)) (fun _ _ _ => trivial)
  · intro s t tr ur sf tf h E F
    have len : g.signatureLength = g.length := by
      have flag := h.2
      simpa only [eval, h.1.1.flag, Option.map_some, Option.some.injEq,
        Bool.not_eq_false', decide_eq_true_eq] using flag
    exact callThenCheck_relCT v len s t tr ur sf tf ⟨h.1.1.context, h.1.2.context⟩ E F

end VG.Proof.RsaPkcs1Sig.X86.Ver
end

end

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/VerifyFnTiming.lean`, which only this module imported.
section

/-! # Stack allocation and saved-register restoration reveal only public addresses -/

section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Verify
open VG.Proof.Rsa.X86.PrivChecked (sp_agree)
open VG.Proof.Dsa.X86 (allocated)

theorem allocation_state {n : Nat} {s a : State} (h : isa.push (.alloc n) s = some a) :
    a = allocated n s := by
  simp only [isa, push] at h
  split at h <;> cases h
  rfl

theorem allocation_relCT (v : PublicImpl) {g : Geometry} {bs : Fin 5 → List Byte}
    :
    RelCT isa (fun a b => ∃ s t, FnInput g bs s ∧ FnInput g bs t ∧
      a = pushed savedRegisters s ∧ b = pushed savedRegisters t)
      (.frame (.alloc VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes)
        (body v.name v.code) (.free VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes))
      (fun a b => a.gpr .esp = b.gpr .esp) := by
  intro a b ta tb a' b' hp ea eb'
  obtain ⟨s, t, hs, ht, rfl, rfl⟩ := hp
  have sp : (pushed savedRegisters s).gpr .esp = (pushed savedRegisters t).gpr .esp := by
    rw [hs.savedSp, ht.savedSp]
  have post : a'.gpr .esp = b'.gpr .esp := by
    rw [Exec.gpr (allocation_noSp v) ea, Exec.gpr (allocation_noSp v) eb', sp]
  cases ea with
  | frame pa ba _ =>
    cases eb' with
    | frame pb bb _ =>
      have ha := allocation_state pa
      have hb := allocation_state pb
      subst ha hb
      have eq := (body_relCT v) _ _ _ _ _ _ ⟨hs.context, ht.context⟩ ba bb
      refine ⟨?_, post⟩
      rw [eq.1]
      rfl

theorem verifyFn_relCT (v : PublicImpl) {g : Geometry} {bs : Fin 5 → List Byte}
    :
    RelCT isa (fun s t => FnInput g bs s ∧ FnInput g bs t)
      (code v.name v.code) (fun _ _ => True) := by
  unfold code
  refine RelCT.frame (R := fun _ _ => True) ?_ ?_
  · intro s t h
    have eq := h.1.savedSp.trans h.2.savedSp.symm
    rw [pushed_esp, pushed_esp] at eq
    have same := congrArg (fun x => x + BitVec.ofNat 32 (4 * savedRegisters.length)) eq
    simpa only [BitVec.sub_add_cancel] using same
  · refine VG.RelCT.seq ((allocation_relCT v (g := g) (bs := bs)).mono ?_ (fun _ _ h => h))
      (restore_relCT.mono (fun _ _ h => sp_agree h) (fun _ _ _ => trivial))
    rintro a b ⟨s, t, h, rfl, rfl⟩
    exact ⟨s, t, h.1, h.2, rfl, rfl⟩
end VG.Proof.RsaPkcs1Sig.X86.Ver
end

end

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/VerifyContract.lean`, which only this module imported.
section

/-! # The complete precomputed verifier satisfies its shared correctness and timing contract -/

section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86

theorem verify_contract_correct (v : PublicImpl) (s : State)
    (h : (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi verifyStack).pre s) :
    ∃ tr t, Exec isa (VG.Impl.RsaPkcs1Sig.X86.Verify.code v.name v.code) s tr t ∧ abiPreserved s t ∧
      (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi verifyStack).post s t := by
  obtain ⟨tr, t, run, preserved, post⟩ := verifyFn_ok v s (verify_contract_pre s h)
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig,
    abi, argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right]
  exact post

theorem verify_contract_ct (v : PublicImpl) : ConstantTime isa
    (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi verifyStack).pre
    (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi verifyStack).pub
    (VG.Impl.RsaPkcs1Sig.X86.Verify.code v.name v.code) := by
  intro s t tr1 tr2 u w hs ht hp e1 e2
  have is := verify_contract_pre s hs
  have it := verify_contract_pre t ht
  rw [← publicGeometry hp, ← publicBytes hp] at it
  exact (verifyFn_relCT v s t tr1 tr2 u w ⟨is, it⟩ e1 e2).1

end VG.Proof.RsaPkcs1Sig.X86.Ver
end

end

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86

def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 131077 then 32
    else if a = 131080 then 64
    else if a = 131085 then 48
    else if a = 131088 then 1
    else if a = 131097 then 64
    else if a = 131100 then 16
    else if a = 131105 then 80
    else if a = 131108 then 64
    else if a = 131113 then 160
    else if a = 131116 then 112
    else if a = 131121 then 96
    else if a = 131124 then 16 else 0
  rd := [⟨8192, 64⟩, ⟨12288, 1⟩, ⟨16384, 16⟩, ⟨20480, 64⟩, ⟨24576, 128⟩]
  wr := [⟨40960, 896⟩, ⟨0x20004, 52⟩]

theorem satisfiable : ∃ s, (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi verifyStack).pre s := by
  have a0 : arg satState 0 = 8192 := by decide
  have a1 : arg satState 1 = 64 := by decide
  have a2 : arg satState 2 = 12288 := by decide
  have a3 : arg satState 3 = 1 := by decide
  have a4 : arg satState 4 = 0 := by decide
  have a5 : arg satState 5 = 16384 := by decide
  have a6 : arg satState 6 = 16 := by decide
  have a7 : arg satState 7 = 20480 := by decide
  have a8 : arg satState 8 = 64 := by decide
  have a9 : arg satState 9 = 40960 := by decide
  have a10 : arg satState 10 = 112 := by decide
  have a11 : arg satState 11 = 24576 := by decide
  have a12 : arg satState 12 = 16 := by decide
  have e : argAddr satState 0 = 0x20004 := by decide
  have esp : satState.gpr .esp = 0x20000 := rfl
  sig_implies_sat [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig,
    abi, argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, e, esp, satState, verifyStack,
      Spec.Rsa.lenValid, Spec.Rsa.publicScratchWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords] using satState

theorem verify_verified (v : PublicImpl) :
    Verified target (VG.Impl.RsaPkcs1Sig.X86.Verify.code v.name v.code)
      (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi verifyStack) :=
  ⟨verify_contract_correct v, verify_contract_ct v, satisfiable⟩

end VG.Proof.RsaPkcs1Sig.X86.Ver

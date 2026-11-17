module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverNoSp
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverSpec
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverZero
import VerifiedGarbage.Proof.Rsa.BytesFrame
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverFnInput
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverRegions
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignRestore
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Dsa.X86.RandomSignCorrect
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeTiming
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverEncoding
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverCmpArgs
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverReleaseArgs
public import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Rsa.X86.PrivSetupTiming
public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Recover
public import VerifiedGarbage.Proof.Rsa.X86.PrivReleaseTiming
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverContext
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverDigest
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignBlocksTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.RandomFinish
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignZero
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Rsa.X86.PrivFnTiming
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyPublicBytes
import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Proof.Dsa.X86.VerifyingABI
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverGeometry
public import VerifiedGarbage.Proof.Rsa.Contract
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverStackWord
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeDispatch
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Dsa.X86.EntryTiming

/-! ### `RsaPkcs1Sig.X86.RecoverContractGeometry`, which only this module used -/

section

/-! # Decode checked RSA's cdecl arguments into its public buffer geometry -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Proof.Bignum.X86

def recoverGeometry (s : State) : Geometry where
  stack := s.gpr .esp - 16 - BitVec.ofNat 32 VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes
  output := arg s 0
  outputLength := (arg s 1).toNat
  workspace := arg s 9
  sources := fun i => arg s (match i.val with | 0 => 2 | 1 => 4 | 2 => 7 | _ => 11)
  length := (arg s 3).toNat
  hash := arg s 6
  exponentLength := (arg s 5).toNat
  signatureLength := (arg s 8).toNat
  preLength := (arg s 12).toNat
  scratchLength := (arg s 10).toNat

def recoverBytes (s : State) (i : Fin 4) : List Byte :=
  Spec.Rsa.bytesAt s.mem (byteAddr ((recoverGeometry s).sources i)) ((recoverGeometry s).sourceLength i)

theorem recoverGeometry_stack (s : State) :
    (recoverGeometry s).stack = s.gpr .esp - BitVec.ofNat 32 2128 := by
  change s.gpr .esp - 16 - 2112 = _
  rw [BitVec.sub_sub]
  rfl

theorem recoverGeometry_stackNat (s : State) (fit : recoverStack ≤ (s.gpr .esp).toNat) :
    (recoverGeometry s).stack.toNat = (s.gpr .esp).toNat - 2128 := by
  rw [recoverGeometry_stack, sub_toNat (by unfold recoverStack at fit; omega_using [fit])]

theorem recoverGeometry_wholeStack (s : State) (fit : recoverStack ≤ (s.gpr .esp).toNat) :
    (recoverGeometry s).wholeStack = ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 recoverStack, recoverStack⟩ := by
  unfold Geometry.wholeStack
  rw [recoverGeometry_stack, BitVec.sub_sub]
  change (⟨(s.gpr .esp - BitVec.ofNat 32 recoverStack).setWidth 64, recoverStack⟩ : Region) = _
  rw [Taint.sub_setWidth fit]

theorem recoverGeometry_arguments (s : State) (fit : recoverStack ≤ (s.gpr .esp).toNat)
    (high : (s.gpr .esp).toNat + 56 ≤ 2 ^ 32) :
    (recoverGeometry s).argumentsRegion = ⟨argAddr s 0, 52⟩ := by
  unfold Geometry.argumentsRegion
  rw [recoverGeometry_stack]
  change (⟨(s.gpr .esp - BitVec.ofNat 32 2128).setWidth 64 + BitVec.ofNat 64 2132, 52⟩ : Region) = _
  rw [Taint.sub_setWidth (by unfold recoverStack at fit; omega_using [fit] : 2128 ≤ (s.gpr .esp).toNat)]
  have aa : argAddr s 0 = (s.gpr .esp).setWidth 64 + 4 :=
    byteAddr_add (by omega_using [high] : (s.gpr .esp).toNat + 4 < 2 ^ 32)
  rw [aa, show BitVec.ofNat 64 2132 = BitVec.ofNat 64 2128 + 4 from rfl, ← BitVec.add_assoc, BitVec.sub_add_cancel]
end VG.Proof.RsaPkcs1Sig.X86.Rcv

end

end

/-! ### `RsaPkcs1Sig.X86.RecoverBlocksTiming`, which only this module used -/

section

/-! # Public stack addresses suffice for every verifier straight-line fragment -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Recover VG.Proof.Dsa.X86
open VG.Impl.RsaPkcs1Sig.X86.Verify (test0 stackAt statusOffset)

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

theorem releaseArgs_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block releaseArgs)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem return_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block [.mov .eax (.reg .ebx)])
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem length_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block lenCheck)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem zeroArgs_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp]))
    (.block [.mov .esi (.mem (VG.Impl.RsaPkcs1Sig.X86.Verify.incoming 0)),
      .mov .ecx (.mem (VG.Impl.RsaPkcs1Sig.X86.Verify.incoming 1)), .mov .eax (.imm 0)])
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem cmp_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .eax])) (.block test0)
    (VG.X86.Taint.Agree (τr [.esp, .eax])) := checkedBlockInvariant rfl rfl

end VG.Proof.RsaPkcs1Sig.X86.Rcv

end

end

/-! ### `RsaPkcs1Sig.X86.RecoverLength`, which only this module used -/

section

/-! # Reject signatures whose public byte count differs from the modulus width -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Sig.X86.Verify (incoming stackAt)
open VG.Impl.RsaPkcs1Sig.X86.Recover (lenCheck)

theorem lengthCheck_ok {g : Geometry} {bs : Fin 4 → List Byte} {s : State} (h : Context g bs s) :
    WP isa (.block lenCheck) s fun t => Context g bs t ∧ t.mem = s.mem ∧ Keeps [.eax] s t ∧
      t.zf = some (decide (g.signatureLength = g.length)) := by
  unfold lenCheck incoming stackAt
  refine wp_ldm rfl (h.readArg (by decide : 8 < 13)) fun a A => ?_
  have ha := h.after (by rw [A.mem]; exact Frame.refl _ _) A.keeps (A.other .esp (by decide))
  have load : readSrc a (.mem ⟨.esp, VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 20 + 4 * 3⟩) = some (g.argument 3) := by
    change a.load32 (addr (a.gpr .esp) (VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 20 + 4 * 3)) = _
    rw [State.load32, ite_eq_left (ha.readArg (by decide : 3 < 13)), ha.argumentValue (by decide : 3 < 13)]
  refine wp_cmpS load fun t T Z => WP.block_nil ?_
  have K : Keeps [.eax] s t := A.keeps.trans (T.keeps _)
  have M := T.mem.trans A.mem
  refine ⟨h.after (by rw [M]; exact Frame.refl _ _) K (K.1 .esp (by decide)), M, K, ?_⟩
  rw [Z, A.gpr, h.argumentValue (by decide : 8 < 13)]
  change some (BitVec.ofNat 32 g.signatureLength - BitVec.ofNat 32 g.length == 0) = _
  rw [sub_beq32]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro eq
    have := congrArg BitVec.toNat eq
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h.valid.signatureBound,
      Nat.mod_eq_of_lt (by have := h.valid.maxLength; omega_using [this] : g.length < 2 ^ 32)] using this
  · intro eq; rw [eq]

theorem recovered_bad {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) (different : g.signatureLength ≠ g.length) : recovered g bs = none := by
  have diff : (bs 2).length ≠ (bs 0).length := by
    rw [(h.sources 0).length, (h.sources 2).length]
    exact different
  unfold recovered
  cases Spec.RsaPkcs1Sig.Hash.ofId g.hash.toNat with
  | none => rfl
  | some hv => simp only [Option.bind_some, Spec.RsaPkcs1Sig.recover, diff, ite_false]

end VG.Proof.RsaPkcs1Sig.X86.Rcv

end

end

/-! ### `RsaPkcs1Sig.X86.RecoverBody`, which only this module used -/

section

/-! # The recovery body releases precisely the digest accepted by the shared spec -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Sig.X86.Recover

def Precomputed (g : Geometry) (bs : Fin 4 → List Byte) (s : State) : Prop :=
  Spec.Rsa.publicPrecompute (bs 0) = some (Spec.Rsa.wordsAt s.mem (byteAddr (g.sources 3)) g.preLength)

theorem calleeFrame {g : Geometry} {bs : Fin 4 → List Byte} {s : State} {m m' : Mem}
    (h : Context g bs s) (F : Frame (publicWr g ++ [g.calleeRegion]) m m') :
    Frame (bodyWrites g) m m' := F.sub (by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact publicWrites_sub h r hr
  · obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩)

theorem body_ok (v : PublicImpl) {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) : WP isa (body v.name v.code) s fun t =>
      Context g bs t ∧ Frame (bodyWrites g) s.mem t.mem ∧ Keeps clobbers s t ∧
      (Precomputed g bs s → Spec.Rsa.written t.mem (byteAddr g.output) g.outputLength (t.gpr .eax) (recovered g bs)) := by
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
    rintro t ⟨ht, Ft, Kt, value⟩
    have Fargs : Frame (bodyWrites g) s.mem a.mem := by
      rw [Mc] at Fa
      apply Fa.sub
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      exact ⟨g.innerRegion, by simp [bodyWrites], Region.sub_prefix (by decide)⟩
    refine ⟨ht, Fargs.trans ((calleeFrame h Fb).trans Ft),
      (Kc.mono (by decide)).trans ((Ka.mono (by decide)).trans
        ((Kb.mono (by decide)).trans Kt)), ?_⟩
    intro cache
    have words : Spec.Rsa.wordsAt a.mem (byteAddr (g.sources 3)) g.preLength =
        Spec.Rsa.wordsAt s.mem (byteAddr (g.sources 3)) g.preLength :=
      VG.Proof.Rsa.wordsAt_frame Fargs (by
        have fit := h.valid.sourceFits 3
        change (g.sources 3).toNat + 8 * g.preLength ≤ 2 ^ 32 at fit
        omega_using [fit]) (h.sourceSeparate 3)
    have pre : Precomputed g bs a := by unfold Precomputed at cache ⊢; rw [words]; exact cache
    rw [checkedPublicRecovery_eq hb length (out pre)] at value
    exact value
  · refine WP.ite true (by simp [eval, Z, length]) (fun _ => ?_) (by simp)
    refine WP.mono (zeroOut_ok hc) ?_
    rintro t ⟨ht, bytes, ax, F, K⟩
    refine ⟨ht, ?_, (Kc.mono (by decide)).trans (K.mono (by decide)), ?_⟩
    · rw [Mc] at F
      apply F.sub
      intro r hr; obtain rfl := List.mem_singleton.mp hr
      exact ⟨g.outputRegion, by simp [bodyWrites], fun _ hx => hx⟩
    · intro _
      rw [recovered_bad h length]
      exact ⟨ax, bytes⟩

end VG.Proof.RsaPkcs1Sig.X86.Rcv

end

end

/-! ### `RsaPkcs1Sig.X86.RecoverStages`, which only this module used -/

section

/-! # Intermediate verifier states used to compose independent executions -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Recover
open VG.Impl.RsaPkcs1Sig.X86.Verify (test0)

structure EncodeReady (g : Geometry) (bs : Fin 4 → List Byte) (s : State) : Prop where
  context : Context g bs s
  dst : s.gpr .edi = g.em2
  len : s.gpr .ecx = BitVec.ofNat 32 g.length
  hash : s.gpr .edx = g.hash
  src : s.gpr .esi = g.digest
  count : s.gpr .ebp = BitVec.ofNat 32 g.outputLength

structure EncodeDone (g : Geometry) (bs : Fin 4 → List Byte) (s : State) : Prop where
  context : Context g bs s
  encoded : Encoded g s

structure CompareReady (g : Geometry) (bs : Fin 4 → List Byte) (s : State) : Prop where
  context : Context g bs s
  src : s.gpr .esi = g.em1
  dst : s.gpr .edi = g.em2
  count : s.gpr .ecx = BitVec.ofNat 32 g.length

structure CallReady (g : Geometry) (bs : Fin 4 → List Byte) (s : State) : Prop where
  context : Context g bs s
  args : Arguments g (publicArgument g) 10 s

theorem encArgs_ready {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) : WP isa (.block encArgs) s (EncodeReady g bs) := by
  refine WP.mono (encArgs_ok h) ?_
  rintro t ⟨ht, _, _, dst, len, hash, count, src⟩
  exact ⟨ht, dst, len, hash, src, count⟩

theorem encode_done {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : EncodeReady g bs s) : WP isa VG.Impl.RsaPkcs1Sig.X86.encode s (EncodeDone g bs) := by
  refine WP.mono (encoding_ok h.context h.dst h.len h.hash h.src h.count) ?_
  rintro t ⟨ht, _, _, enc⟩
  exact ⟨ht, enc⟩

theorem cmpArgs_ready {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) : WP isa (.block cmpArgs) s (CompareReady g bs) := by
  refine WP.mono (cmpArgs_ok h) ?_
  rintro t ⟨ht, _, _, src, dst, cnt⟩
  exact ⟨ht, src, dst, cnt⟩

theorem compare_done {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : CompareReady g bs s) : WP isa VG.Impl.RsaPkcs1Sig.X86.compare s (Context g bs) := by
  refine WP.mono (compare_ok h.context h.src h.dst h.count) ?_
  rintro t ⟨ht, _, _, _⟩
  exact ht

theorem callArgs_ready {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) : WP isa (.block pubArgs) s (CallReady g bs) := by
  refine WP.mono (pubArgs_ok h) ?_
  rintro t ⟨ht, args, _, _⟩
  exact ⟨ht, args⟩

theorem publicCall_ready (v : PublicImpl) {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : CallReady g bs s) (len : g.signatureLength = g.length) :
    WP isa (.call v.name v.code) s (Context g bs) := by
  refine WP.mono (public_call v h.context h.args len) ?_
  rintro t ⟨ht, _, _, _⟩
  exact ht

theorem encoded_status {g : Geometry} {bs : Fin 4 → List Byte} {s t : State}
    (hs : EncodeDone g bs s) (ht : EncodeDone g bs t) : s.gpr .eax = t.gpr .eax := by
  have option : (encodeId g.hash (digestBytes g s) g.length).isSome =
      (encodeId g.hash (digestBytes g t) g.length).isSome := by
    unfold encodeId
    cases id : Spec.RsaPkcs1Sig.Hash.ofId g.hash.toNat with
    | none => rfl
    | some hv =>
      simp only [Option.bind_some, Spec.RsaPkcs1Sig.encode, Spec.RsaPkcs1Sig.digestInfo,
        List.length_append, digestBytes, Spec.Rsa.bytesAt, List.length_map, List.length_range]
      split <;> rfl
  have left := hs.encoded
  have right := ht.encoded
  unfold Encoded at left right
  cases e1 : encodeId g.hash (digestBytes g s) g.length <;>
    cases e2 : encodeId g.hash (digestBytes g t) g.length <;>
    simp only [e1, e2, Option.isSome_none, Option.isSome_some, Bool.false_eq_true, Bool.true_eq_false] at option left right
  · exact left.trans right.symm
  · exact left.1.trans right.1.symm

end VG.Proof.RsaPkcs1Sig.X86.Rcv

end

end

/-! ### `RsaPkcs1Sig.X86.RecoverReleaseTiming`, which only this module used -/

section

/-! # Digest copying and zero output use only public pointers and counters -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Recover VG.Proof.Dsa.X86
open VG.Proof.Rsa.X86.PrivChecked (sp_agree pair_seq_ct loopTaint releaseLoop_relCT)
open VG.Proof.RsaPkcs1Sig.X86.Sgn (clearTaint clear_relCT)

structure ReleaseReady (g : Geometry) (bs : Fin 4 → List Byte) (s : State) : Prop where
  context : Context g bs s
  dst : s.gpr .edi = g.output
  src : s.gpr .esi = g.digest
  count : s.gpr .ecx = BitVec.ofNat 32 g.outputLength

theorem releaseArgs_ready {g : Geometry} {bs : Fin 4 → List Byte} {s : State} (h : Context g bs s) :
    WP isa (.block releaseArgs) s (ReleaseReady g bs) := by
  refine WP.mono (releaseArgs_ok h) ?_
  rintro t ⟨ht, _, _, _, _, dst, cnt, src⟩
  exact ⟨ht, dst, src, cnt⟩

theorem releaseReady_agree {g : Geometry} {bs : Fin 4 → List Byte} {s t : State}
    (hs : ReleaseReady g bs s) (ht : ReleaseReady g bs t) : VG.X86.Taint.Agree loopTaint s t := by
  apply agree_regs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hs.context.sp.trans ht.context.sp.symm
  · exact hs.src.trans ht.src.symm
  · exact hs.dst.trans ht.dst.symm
  · exact hs.count.trans ht.count.symm

theorem release_relCT {g : Geometry} {bs : Fin 4 → List Byte} :
    RelCT isa (fun s t => Context g bs s ∧ Context g bs t) release (fun _ _ => True) := by
  unfold release
  apply pair_seq_ct (releaseArgs_relCT.mono
    (fun _ _ h => sp_agree (h.1.sp.trans h.2.sp.symm)) (fun _ _ _ => trivial))
    (fun _ h => releaseArgs_ready h) (fun _ h => releaseArgs_ready h)
  apply VG.RelCT.seq (releaseLoop_relCT.mono (fun _ _ h => releaseReady_agree h.1 h.2)
    (fun _ _ h => sp_agree (h.rf.1 .esp (by decide))))
  exact return_relCT.mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem zeroOut_relCT {g : Geometry} {bs : Fin 4 → List Byte} :
    RelCT isa (fun s t => Context g bs s ∧ Context g bs t) zeroOut (fun _ _ => True) := by
  intro s t tr ur sf tf H E F
  obtain ⟨hs, ht⟩ := H
  cases E with
  | seq E1 E2 =>
    cases F with
    | seq F1 F2 =>
      have T1 := (zeroArgs_relCT _ _ _ _ _ _ (sp_agree (hs.sp.trans ht.sp.symm)) E1 F1).1
      obtain ⟨_, _, _, Ss, Cs, _⟩ := wp_result (zeroArgs_ok hs) E1
      obtain ⟨_, _, _, St, Ct, _⟩ := wp_result (zeroArgs_ok ht) F1
      have agree : VG.X86.Taint.Agree clearTaint _ _ := agree_regs (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Ss.trans St.symm
        · exact Cs.trans Ct.symm)
      have T2 := (clear_relCT _ _ _ _ _ _ agree E2 F2).1
      exact ⟨by rw [T1, T2], trivial⟩

end VG.Proof.RsaPkcs1Sig.X86.Rcv

end

end

/-! ### `RsaPkcs1Sig.X86.RecoverObservations`, which only this module used -/

section

/-! # The shared verifier leakage fixes every immutable input byte -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Proof.Bignum.X86

theorem arguments {s t : State} (H : (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi recoverStack).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < 13, arg s i = arg t i := by
  sig_pub [Spec.RsaPkcs1Sig.recoverPrecomputedContract, Spec.RsaPkcs1Sig.recoverPrecomputedSig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  constructor
  · with_reducible assumption
  · intro i hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 by omega_using [hi]) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem publicGeometry {s t : State} (H : (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi recoverStack).pub s t) :
    recoverGeometry s = recoverGeometry t := by
  obtain ⟨sp, args⟩ := arguments H
  have sources : (recoverGeometry s).sources = (recoverGeometry t).sources := by
    funext i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_using []) with rfl | rfl | rfl | rfl
    exacts [args 2 (by decide), args 4 (by decide), args 7 (by decide), args 11 (by decide)]
  simp only [recoverGeometry, sp, args 0 (by decide), args 1 (by decide), args 9 (by decide),
    args 3 (by decide), args 6 (by decide), args 5 (by decide), args 8 (by decide), args 12 (by decide), args 10 (by decide)]
  exact congrArg (fun ps => Geometry.mk _ _ _ _ ps _ _ _ _ _ _) sources

theorem publicBytes {s t : State} (H : (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi recoverStack).pub s t) :
    recoverBytes s = recoverBytes t := by
  have args := (arguments H).2
  have geometry := publicGeometry H
  have Leak : (recoverBytes s 0 ++ recoverBytes s 1 ++ recoverBytes s 2).map (·.toNat) ++
      (Spec.Rsa.wordsAt s.mem (byteAddr ((recoverGeometry s).sources 3)) (recoverGeometry s).preLength).map (·.toNat) =
      (recoverBytes t 0 ++ recoverBytes t 1 ++ recoverBytes t 2).map (·.toNat) ++
      (Spec.Rsa.wordsAt t.mem (byteAddr ((recoverGeometry t).sources 3)) (recoverGeometry t).preLength).map (·.toNat) := by
    sig_pub [Spec.RsaPkcs1Sig.recoverPrecomputedContract, Spec.RsaPkcs1Sig.recoverPrecomputedSig, abi, argSlots, argVal, argBytes] at H
    exact H.2.1
  have wordLength : ((Spec.Rsa.wordsAt s.mem (byteAddr ((recoverGeometry s).sources 3)) (recoverGeometry s).preLength).map (·.toNat)).length =
      ((Spec.Rsa.wordsAt t.mem (byteAddr ((recoverGeometry t).sources 3)) (recoverGeometry t).preLength).map (·.toNat)).length := by
    simp only [List.length_map, Spec.Rsa.wordsAt, List.length_range, geometry]
  have both := List.append_inj' Leak wordLength
  have bytes := (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp both.1
  have words := (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp both.2
  have lengths (i : Fin 4) : (recoverBytes s i).length = (recoverBytes t i).length := by
    simp only [recoverBytes, Spec.Rsa.bytesAt, List.length_map, List.length_range, geometry]
  simp only [List.append_assoc] at bytes
  have first := List.append_inj_left bytes (lengths 0)
  have rest := List.append_inj_right bytes (lengths 0)
  have second := List.append_inj_left rest (lengths 1)
  have tail := List.append_inj_right rest (lengths 1)
  have third := tail
  have fourth : recoverBytes s 3 = recoverBytes t 3 := by
    rw [geometry] at words
    unfold recoverBytes
    rw [geometry]
    exact VG.Proof.RsaPkcs1Sig.X86.Ver.bytesAt_of_words words
  funext i
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_using []) with rfl | rfl | rfl | rfl
  exacts [first, second, third, fourth]

end VG.Proof.RsaPkcs1Sig.X86.Rcv

end

end

/-! ### `RsaPkcs1Sig.X86.RecoverContractInput`, which only this module used -/

section

/-! ### `RsaPkcs1Sig.X86.RecoverABI`, which only this module used -/

section

/-! # Resources supplied by the shared precomputed recovery signature -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86
open VG.Proof.Dsa.X86 (argumentPointer)

structure RecoverABI (s : State) : Prop where
  stackLow : recoverStack ≤ (s.gpr .esp).toNat
  stackBound : (s.gpr .esp).toNat + 56 ≤ 2 ^ 32
  rd : s.rd = [⟨argumentPointer s 2, (arg s 3).toNat⟩, ⟨argumentPointer s 4, (arg s 5).toNat⟩, ⟨argumentPointer s 7, (arg s 8).toNat⟩, ⟨argumentPointer s 11, 8 * (arg s 12).toNat⟩]
  wr : s.wr = [⟨argumentPointer s 0, (arg s 1).toNat⟩, ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩, ⟨argAddr s 0, 52⟩]
  outputSource0 : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  outputSource1 : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 4, (arg s 5).toNat⟩
  outputSource2 : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 7, (arg s 8).toNat⟩
  outputSource3 : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 11, 8 * (arg s 12).toNat⟩
  outputWorkspace : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩
  outputArguments : (⟨argumentPointer s 0, (arg s 1).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 52⟩
  sourceWorkspace0 : (⟨argumentPointer s 2, (arg s 3).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩
  sourceWorkspace1 : (⟨argumentPointer s 4, (arg s 5).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩
  sourceWorkspace2 : (⟨argumentPointer s 7, (arg s 8).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩
  sourceWorkspace3 : (⟨argumentPointer s 11, 8 * (arg s 12).toNat⟩ : Region).Disjoint ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩
  workspaceArguments : (⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩ : Region).Disjoint ⟨argAddr s 0, 52⟩
  stackOutput : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 recoverStack, recoverStack⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat⟩
  stackSource0 : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 recoverStack, recoverStack⟩ : Region).Disjoint ⟨argumentPointer s 2, (arg s 3).toNat⟩
  stackSource1 : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 recoverStack, recoverStack⟩ : Region).Disjoint ⟨argumentPointer s 4, (arg s 5).toNat⟩
  stackSource2 : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 recoverStack, recoverStack⟩ : Region).Disjoint ⟨argumentPointer s 7, (arg s 8).toNat⟩
  stackSource3 : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 recoverStack, recoverStack⟩ : Region).Disjoint ⟨argumentPointer s 11, 8 * (arg s 12).toNat⟩
  stackWorkspace : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 recoverStack, recoverStack⟩ : Region).Disjoint ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩
  stackArguments : (⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 recoverStack, recoverStack⟩ : Region).Disjoint ⟨argAddr s 0, 52⟩
  returnOutput : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 0, (arg s 1).toNat⟩
  returnWorkspace : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint ⟨argumentPointer s 9, 8 * (arg s 10).toNat⟩
  outputFit : (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32
  sourceFit0 : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32
  sourceFit1 : (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32
  sourceFit2 : (arg s 7).toNat + (arg s 8).toNat ≤ 2 ^ 32
  sourceFit3 : (arg s 11).toNat + 8 * (arg s 12).toNat ≤ 2 ^ 32
  workspaceFit : (arg s 9).toNat + 8 * (arg s 10).toNat ≤ 2 ^ 32
  valid : Spec.Rsa.lenValid (arg s 3).toNat
  ePositive : 1 ≤ (arg s 5).toNat
  eFits : (arg s 5).toNat ≤ (arg s 3).toNat
  hash : ∃ h, Spec.RsaPkcs1Sig.Hash.ofId (arg s 6).toNat = some h ∧ (arg s 1).toNat = h.len
  space : Spec.Rsa.publicScratchWords (arg s 3).toNat ≤ (arg s 10).toNat
  preLength : (arg s 12).toNat = Spec.Rsa.precomputedWords (arg s 3).toNat

theorem recoverABI_of {s : State} (h : (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi recoverStack).pre s) : RecoverABI s := by
  sig_pre [Spec.RsaPkcs1Sig.recoverPrecomputedContract, Spec.RsaPkcs1Sig.recoverPrecomputedSig,
    abi, argSlots, argVal, argBytes, stackBelow] at h
  sig_split h
  constructor <;> simp only [recoverStack, Nat.mul_comm 8] at *
  all_goals first
    | with_reducible assumption
    | exact Region.Disjoint.symm (by with_reducible assumption)

end VG.Proof.RsaPkcs1Sig.X86.Rcv

end

end

/-! # Decode the shared verifier precondition into its frame and input geometry -/

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/RecoverEntryInput.lean`, which only this module imported.
section

/-! # Native cdecl inputs before reserving the two wrapper frames -/

section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Proof.Rsa.X86.PrivChecked VG.Impl.RsaPkcs1Sig.X86.Verify VG.Proof.Bignum.X86
open VG.Proof.Dsa.X86 (allocated)

structure EntryInput (g : Geometry) (bs : Fin 4 → List Byte) (s : State) : Prop where
  valid : g.Valid
  stackFit : recoverStack ≤ (s.gpr .esp).toNat
  base : g.stack = s.gpr .esp - 16 - BitVec.ofNat 32 VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes
  source : ∀ i, PublicBytes (g.sources i) (g.sourceLength i) (bs i) s
  outputWrite : InRegions s.wr (byteAddr g.output) g.outputLength
  workspaceWrite : InRegions s.wr (byteAddr g.workspace) (8 * g.scratchLength)
  argumentsRead : InRegions (s.rd ++ s.wr) g.argumentsRegion.base 52
  arguments : ∀ j < 13, s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 20 + 4 * j)) 32 = g.argument j
  returnSeparate : ∀ r ∈ bodyWrites g, (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint r

theorem EntryInput.enteredSp {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : EntryInput g bs s) : (entered s).gpr .esp = g.stack := by
  rw [entered, VG.Proof.Dsa.X86.allocated_esp, pushed_esp]
  exact h.base.symm

theorem EntryInput.savedAddr {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : EntryInput g bs s) : ((pushed savedRegisters s).gpr .esp).setWidth 64 = g.savedRegion.base := by
  have eq : (pushed savedRegisters s).gpr .esp = g.stack + BitVec.ofNat 32 VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes := by
    rw [← h.enteredSp]
    exact (BitVec.sub_add_cancel _ _).symm
  rw [eq]
  exact h.valid.offsetAddr (by decide)

theorem EntryInput.enteredFrame {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : EntryInput g bs s) : Frame [g.savedRegion] s.mem (entered s).mem := by
  have f := pushed_frame (rs := savedRegisters) (s := s) (by decide)
    (by change 16 ≤ _; have := h.stackFit; unfold recoverStack at this; omega)
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
end VG.Proof.RsaPkcs1Sig.X86.Rcv
end

end

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/RecoverEntryReady.lean`, which only this module imported.
section

/-! # Entering the wrapper preserves all sources and incoming arguments -/

section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Proof.Rsa.X86.PrivChecked VG.Proof.Bignum.X86

theorem EntryInput.enteredSource {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : EntryInput g bs s) (i : Fin 4) :
    PublicBytes (g.sources i) (g.sourceLength i) (bs i) (entered s) := by
  refine ⟨(h.source i).fits, entered_read (h.source i).read, ?_⟩
  have sep : ∀ r ∈ [g.savedRegion], (g.sourceRegion i).Disjoint r := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ((h.valid.stackSources i).sub_left h.valid.savedSub).symm
  exact (Rsa.rsa_bytes_frame h.enteredFrame (by have := (h.source i).fits; omega) sep).trans (h.source i).bytes

theorem EntryInput.enteredArguments {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
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

theorem EntryInput.ready {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : EntryInput g bs s) : FnInput g bs s := by
  refine ⟨h.stackFit, ⟨h.valid, h.enteredSp, ?_, h.enteredSource,
    entered_write h.outputWrite, entered_write h.workspaceWrite,
    entered_read h.argumentsRead, h.enteredArguments⟩, h.returnSeparate⟩
  refine ⟨by have := h.valid.stackHigh; omega, ?_⟩
  change (⟨byteAddr g.stack, VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes⟩ : Region) ∈
    ⟨byteAddr ((entered s).gpr .esp), VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes⟩ :: (pushed savedRegisters s).wr
  rw [h.enteredSp]
  exact List.mem_cons_self
end VG.Proof.RsaPkcs1Sig.X86.Rcv
end

end

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Proof.Bignum.X86
open VG.Proof.Dsa.X86 (argumentPointer)

theorem recover_contract_pre (s : State) (pre : (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi recoverStack).pre s) :
    FnInput (recoverGeometry s) (recoverBytes s) s := by
  have h := recoverABI_of pre
  have fits : ∀ i, ((recoverGeometry s).sources i).toNat + (recoverGeometry s).sourceLength i ≤ 2 ^ 32 := by
    intro i
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_using []) with rfl | rfl | rfl | rfl
    exacts [h.sourceFit0, h.sourceFit1, h.sourceFit2, h.sourceFit3]
  have geometry : (recoverGeometry s).Valid := by
    refine ⟨h.valid.1, h.valid.2, h.ePositive, h.eFits, h.hash, (arg s 8).isLt,
      h.preLength, h.space, ?_, ?_, h.outputFit, ?_, h.outputWorkspace, ?_, ?_, fits,
      h.workspaceFit, ?_, ?_, ?_, ?_, ?_⟩
    · rw [recoverGeometry_stackNat s h.stackLow]
      have := h.stackLow
      simp only [recoverStack] at this
      omega_using [this]
    · rw [recoverGeometry_stackNat s h.stackLow]
      have := h.stackBound
      simp only [VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes]
      omega_using [this]
    · intro i
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_using []) with rfl | rfl | rfl | rfl
      exacts [h.outputSource0, h.outputSource1, h.outputSource2, h.outputSource3]
    · rw [recoverGeometry_arguments s h.stackLow h.stackBound]; exact h.outputArguments
    · rw [recoverGeometry_wholeStack s h.stackLow]; exact h.stackOutput
    · intro i
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_using []) with rfl | rfl | rfl | rfl
      exacts [h.sourceWorkspace0, h.sourceWorkspace1, h.sourceWorkspace2, h.sourceWorkspace3]
    · rw [recoverGeometry_arguments s h.stackLow h.stackBound]; exact h.workspaceArguments
    · intro i
      rw [recoverGeometry_wholeStack s h.stackLow]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_using []) with rfl | rfl | rfl | rfl
      exacts [h.stackSource0, h.stackSource1, h.stackSource2, h.stackSource3]
    · rw [recoverGeometry_wholeStack s h.stackLow]; exact h.stackWorkspace
    · rw [recoverGeometry_wholeStack s h.stackLow, recoverGeometry_arguments s h.stackLow h.stackBound]
      exact h.stackArguments
  apply EntryInput.ready
  refine ⟨geometry, h.stackLow, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨fits i, ?_, rfl⟩
    refine ⟨(recoverGeometry s).sourceRegion i, List.mem_append_left _ ?_, Region.contains_self _ _⟩
    rw [h.rd]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega_using []) with rfl | rfl | rfl | rfl
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  · rw [h.wr]
    exact ⟨_, by simp [recoverGeometry, byteAddr, argumentPointer], Region.contains_self _ _⟩
  · rw [h.wr]
    exact ⟨_, by simp [recoverGeometry, byteAddr, argumentPointer], Region.contains_self _ _⟩
  · rw [recoverGeometry_arguments s h.stackLow h.stackBound]
    exact ⟨_, List.mem_append_right _ (by rw [h.wr]; simp), Region.contains_self _ _⟩
  · intro j hj
    have address : byteAddr (recoverGeometry s).stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 20 + 4 * j) = argAddr s j := by
      rw [← Offset.add_add]
      change (recoverGeometry s).argumentsRegion.base + BitVec.ofNat 64 (4 * j) = _
      rw [recoverGeometry_arguments s h.stackLow h.stackBound]
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
    all_goals simp only [recoverGeometry, Geometry.argument, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    all_goals rfl
  · intro r hr
    have belowRet : (⟨(s.gpr .esp).setWidth 64, 4⟩ : Region).Disjoint (recoverGeometry s).wholeStack := by
      rw [recoverGeometry_wholeStack s h.stackLow]
      have sep := Offset.disjoint_base ((s.gpr .esp).setWidth 64 - BitVec.ofNat 64 recoverStack)
        (Nat.le_refl recoverStack) (by decide : recoverStack + 4 ≤ 2 ^ 64)
      rw [BitVec.sub_add_cancel] at sep
      exact sep
    simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact belowRet.sub_right geometry.innerSub
    · exact belowRet.sub_right geometry.calleeSub
    · exact h.returnOutput
    · exact h.returnWorkspace

end VG.Proof.RsaPkcs1Sig.X86.Rcv

end

end

/-! # Complete i686 certificate for precomputed PKCS #1 recovery -/

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/RecoverReturn.lean`, which only this module imported.
section

/-! # The wrapper preserves its caller's return address -/

section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Proof.Rsa.X86.PrivChecked VG.Impl.RsaPkcs1Sig.X86.Verify VG.Proof.Bignum.X86

theorem popped_four_value (s : State) :
    (popped .ebx 4 s).gpr .ebx = s.mem.readW ((s.gpr .esp + 12).setWidth 64) 32 := by
  change s.mem.readW ((((s.gpr .esp + 4) + 4) + 4).setWidth 64) 32 = _
  simp only [BitVec.add_assoc]
  rfl

theorem FnInput.returnWord {g : Geometry} {bs : Fin 4 → List Byte} {s t : State}
    (h : FnInput g bs s) (frame : Frame (bodyWrites g) (entered s).mem t.mem) :
    t.mem.readW ((s.gpr .esp).setWidth 64) 32 = s.mem.readW ((s.gpr .esp).setWidth 64) 32 := by
  have low : 16 ≤ (s.gpr .esp).toNat := by have := h.stackFit; unfold recoverStack at this; omega
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
end VG.Proof.RsaPkcs1Sig.X86.Rcv
end

end

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/RecoverEntryCache.lean`, which only this module imported.
section

/-! # Saving caller registers leaves the precomputed public key unchanged -/

section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Proof.Bignum.X86

theorem FnInput.enteredCache {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : FnInput g bs s) : Precomputed g bs (entered s) ↔ Precomputed g bs s := by
  have low : 16 ≤ (s.gpr .esp).toNat := by have := h.stackFit; unfold recoverStack at this; omega
  have F := pushed_frame (rs := savedRegisters) (s := s) (by decide) low
  have saved : ((pushed savedRegisters s).gpr .esp).setWidth 64 = g.savedRegion.base := by
    rw [h.savedSp]
    exact h.context.valid.offsetAddr (by decide)
  unfold below at F
  rw [← pushed_esp] at F
  change Frame [⟨((pushed savedRegisters s).gpr .esp).setWidth 64, 16⟩] s.mem (entered s).mem at F
  rw [saved] at F
  have words : Spec.Rsa.wordsAt (entered s).mem (byteAddr (g.sources 3)) g.preLength =
      Spec.Rsa.wordsAt s.mem (byteAddr (g.sources 3)) g.preLength :=
    VG.Proof.Rsa.wordsAt_frame F (by
      have fit := h.context.valid.sourceFits 3
      change (g.sources 3).toNat + 8 * g.preLength ≤ 2 ^ 32 at fit
      omega) (by
        intro r hr; obtain rfl := List.mem_singleton.mp hr
        exact ((h.context.valid.stackSources 3).sub_left h.context.valid.savedSub).symm)
  unfold Precomputed
  rw [words]

end VG.Proof.RsaPkcs1Sig.X86.Rcv
end

end

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/RecoverFn.lean`, which only this module imported.
section

/-! # Callable PKCS #1 signing restores the i686 calling convention -/

section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Recover VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Proof.Dsa.X86 (allocated freed freed_esp freed_gpr)

theorem recoverFn_ok (v : PublicImpl) (s : State) {g : Geometry} {bs : Fin 4 → List Byte}
    (h : FnInput g bs s) :
    WP isa (code v.name v.code) s fun t => abiPreserved s t ∧
      (Precomputed g bs s → Spec.Rsa.written t.mem (byteAddr g.output) g.outputLength (t.gpr .eax)
        (recovered g bs)) := by
  have stackFit : 16 ≤ (s.gpr .esp).toNat := by
    have := h.stackFit; unfold recoverStack at this; omega
  have allocation : VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes ≤ ((pushed savedRegisters s).gpr .esp).toNat := by
    rw [pushed_esp, show 4 * savedRegisters.length = 16 from rfl, sub_toNat stackFit]
    have := h.stackFit
    simp only [recoverStack, VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes] at *
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
  · rw [popped_mem, popped_gpr _ _ _ (by decide) (by decide), mem,
      restT.1 .eax (by decide), freed_gpr _ _ (by decide)]
    intro cache
    exact result (h.enteredCache.mpr cache)
end VG.Proof.RsaPkcs1Sig.X86.Rcv
end

end

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/RecoverTailTiming.lean`, which only this module imported.
section

/-! # The padding check never branches on the precomputed RSA call's status -/

section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Sig.X86.Recover VG.Proof.Dsa.X86
open VG.Impl.RsaPkcs1Sig.X86.Verify (test0)
open VG.Proof.Rsa.X86.PrivChecked (sp_agree pair_seq_ct)

theorem compareReady_agree {g : Geometry} {bs : Fin 4 → List Byte} {s t : State}
    (hs : CompareReady g bs s) (ht : CompareReady g bs t) : VG.X86.Taint.Agree compareTaint s t := by
  apply agree_regs
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hs.dst.trans ht.dst.symm
  · exact hs.src.trans ht.src.symm
  · exact hs.count.trans ht.count.symm

theorem compareThenRelease_relCT {g : Geometry} {bs : Fin 4 → List Byte} :
    RelCT isa (fun s t => Context g bs s ∧ Context g bs t)
      (.seq (.block cmpArgs) (.seq VG.Impl.RsaPkcs1Sig.X86.compare release)) (fun _ _ => True) := by
  apply pair_seq_ct (cmpArgs_relCT.mono
    (fun _ _ h => sp_agree (h.1.sp.trans h.2.sp.symm)) (fun _ _ _ => trivial))
    (fun _ h => cmpArgs_ready h) (fun _ h => cmpArgs_ready h)
  apply pair_seq_ct (compare_relCT.mono (fun _ _ h => compareReady_agree h.1 h.2) (fun _ _ _ => trivial))
    (fun _ h => compare_done h) (fun _ h => compare_done h)
  exact release_relCT

structure Compared (g : Geometry) (bs : Fin 4 → List Byte) (s : State) : Prop extends EncodeDone g bs s where
  flag : s.zf = some (s.gpr .eax == 0)

theorem compare_ready {g : Geometry} {bs : Fin 4 → List Byte} {s : State} (h : EncodeDone g bs s) :
    WP isa (.block test0) s (Compared g bs) := by
  unfold test0
  refine wp_cmpS rfl fun t F Z => WP.block_nil ?_
  refine ⟨⟨h.context.after (by rw [F.mem]; exact Frame.refl _ _) (F.keeps []) (congrFun F.gpr .esp), ?_⟩, ?_⟩
  · simpa only [Encoded, digestBytes, F.gpr, F.mem] using h.encoded
  · rw [Z, F.gpr]
    exact congrArg some (by change (s.gpr .eax - 0#32 == 0#32) = _; rw [BitVec.sub_zero]; rfl)

theorem tail_relCT {g : Geometry} {bs : Fin 4 → List Byte} :
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
  · exact zeroOut_relCT.mono
      (fun _ _ h => ⟨h.1.1.context, h.1.2.context⟩) (fun _ _ _ => trivial)
  · exact compareThenRelease_relCT.mono (fun _ _ h => ⟨h.1.1.context, h.1.2.context⟩) (fun _ _ _ => trivial)

theorem encodeReady_agree {g : Geometry} {bs : Fin 4 → List Byte} {s t : State}
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

theorem afterPub_relCT {g : Geometry} {bs : Fin 4 → List Byte} :
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

end VG.Proof.RsaPkcs1Sig.X86.Rcv
end

end

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/RecoverCallPublic.lean`, which only this module imported.
section

/-! # The nested public operation observes only the shared exponent and key words -/

section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Proof.Bignum.X86

theorem Context.words_equal {g : Geometry} {bs : Fin 4 → List Byte} {s t : State}
    (hs : Context g bs s) (ht : Context g bs t) :
    Spec.Rsa.wordsAt s.mem (byteAddr (g.sources 3)) g.preLength =
      Spec.Rsa.wordsAt t.mem (byteAddr (g.sources 3)) g.preLength := by
  unfold Spec.Rsa.wordsAt
  refine List.map_congr_left ?_
  intro i hi
  have hi := List.mem_range.mp hi
  apply Mem.readW_congr
  intro j hj
  rw [Offset.add_add]
  have bound : 8 * i + j < (bs 3).length := by
    rw [(hs.sources 3).length]
    change 8 * i + j < 8 * g.preLength
    omega
  rw [(hs.sources 3).byte _ bound, (ht.sources 3).byte _ bound]

theorem publicCall_pub {g : Geometry} {bs : Fin 4 → List Byte} {s t : State}
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
  have ef : g.exponentLength < 2 ^ 32 := by have := hs.valid.exponentFits; have := hs.valid.maxLength; omega
  have pf : g.preLength < 2 ^ 32 := by
    have fit := hs.valid.sourceFits 3
    change (g.sources 3).toNat + 8 * g.preLength ≤ 2 ^ 32 at fit
    omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ef, Nat.mod_eq_of_lt pf]
  have bytes := (hs.callBytes 1).trans (ht.callBytes 1).symm
  have words := hs.callWords.trans ((hs.words_equal ht).trans ht.callWords.symm)
  change Spec.Rsa.bytesAt s.callEntry.mem ((g.sources 1).setWidth 64) g.exponentLength = _ at bytes
  simp only [State.callEntry_mem, hs.sp, ht.sp] at bytes words
  simp only [byteAddr] at words
  rw [bytes, words]
  rfl

end VG.Proof.RsaPkcs1Sig.X86.Rcv
end

end

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/RecoverBodyTiming.lean`, which only this module imported.
section

/-! # The verifier body relates even calls with inconsistent precomputed moduli -/

section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Recover
open VG.Proof.Rsa.X86.PrivChecked (sp_agree pair_seq_ct)

theorem publicCall_relCT (v : PublicImpl) {g : Geometry} {bs : Fin 4 → List Byte}
    (len : g.signatureLength = g.length) :
    RelCT isa (fun s t => CallReady g bs s ∧ CallReady g bs t)
      (.call v.name v.code) (fun _ _ => True) := by
  apply RelCT.call v.verified.1 v.verified.2.1 (publicRd g) (publicWr g)
  intro s t h
  exact ⟨publicCall_pre h.1.context h.1.args len, publicCall_pre h.2.context h.2.args len,
    publicCall_pub h.1.context h.2.context h.1.args h.2.args,
    (publicCovers h.1.context).1, (publicCovers h.1.context).2,
    (publicCovers h.2.context).1, (publicCovers h.2.context).2, h.1.context.sp.trans h.2.context.sp.symm⟩

theorem callThenCheck_relCT (v : PublicImpl) {g : Geometry} {bs : Fin 4 → List Byte}
    (len : g.signatureLength = g.length) :
    RelCT isa (fun s t => Context g bs s ∧ Context g bs t)
      (.seq (.block pubArgs) (.seq (.call v.name v.code) afterPub)) (fun _ _ => True) := by
  apply pair_seq_ct (pubArgs_relCT.mono
    (fun _ _ h => sp_agree (h.1.sp.trans h.2.sp.symm)) (fun _ _ _ => trivial))
    (fun _ h => callArgs_ready h) (fun _ h => callArgs_ready h)
  exact pair_seq_ct (publicCall_relCT v len) (fun _ h => publicCall_ready v h len)
    (fun _ h => publicCall_ready v h len) afterPub_relCT

structure LengthDone (g : Geometry) (bs : Fin 4 → List Byte) (s : State) : Prop where
  context : Context g bs s
  flag : s.zf = some (decide (g.signatureLength = g.length))

theorem length_done {g : Geometry} {bs : Fin 4 → List Byte} {s : State} (h : Context g bs s) :
    WP isa (.block lenCheck) s (LengthDone g bs) := by
  refine WP.mono (lengthCheck_ok h) ?_
  rintro t ⟨ht, _, _, flag⟩
  exact ⟨ht, flag⟩

theorem body_relCT (v : PublicImpl) {g : Geometry} {bs : Fin 4 → List Byte} :
    RelCT isa (fun s t => Context g bs s ∧ Context g bs t) (body v.name v.code) (fun _ _ => True) := by
  unfold body
  apply pair_seq_ct (length_relCT.mono
    (fun _ _ h => sp_agree (h.1.sp.trans h.2.sp.symm)) (fun _ _ _ => trivial))
    (fun _ h => length_done h) (fun _ h => length_done h)
  apply RelCT.ite
  · intro s t h
    change s.zf.map (! ·) = t.zf.map (! ·)
    rw [h.1.flag, h.2.flag]
  · exact zeroOut_relCT.mono (fun _ _ h => ⟨h.1.1.context, h.1.2.context⟩) (fun _ _ _ => trivial)
  · intro s t tr ur sf tf h E F
    have len : g.signatureLength = g.length := by
      have flag := h.2
      simpa only [eval, h.1.1.flag, Option.map_some, Option.some.injEq,
        Bool.not_eq_false', decide_eq_true_eq] using flag
    exact callThenCheck_relCT v len s t tr ur sf tf ⟨h.1.1.context, h.1.2.context⟩ E F

end VG.Proof.RsaPkcs1Sig.X86.Rcv
end

end

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/RecoverFnTiming.lean`, which only this module imported.
section

/-! # Stack allocation and saved-register restoration reveal only public addresses -/

section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Recover
open VG.Proof.Rsa.X86.PrivChecked (sp_agree)
open VG.Proof.Dsa.X86 (allocated)

theorem allocation_state {n : Nat} {s a : State} (h : isa.push (.alloc n) s = some a) :
    a = allocated n s := by
  simp only [isa, push] at h
  split at h <;> cases h
  rfl

theorem allocation_relCT (v : PublicImpl) {g : Geometry} {bs : Fin 4 → List Byte}
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

theorem recoverFn_relCT (v : PublicImpl) {g : Geometry} {bs : Fin 4 → List Byte}
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
end VG.Proof.RsaPkcs1Sig.X86.Rcv
end

end

-- Formerly `VerifiedGarbage/Proof/RsaPkcs1Sig/X86/RecoverContract.lean`, which only this module imported.
section

/-! # Precomputed recovery satisfies the shared correctness and timing contract -/

section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86

theorem recover_contract_correct (v : PublicImpl) (s : State)
    (h : (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi recoverStack).pre s) :
    ∃ tr t, Exec isa (VG.Impl.RsaPkcs1Sig.X86.Recover.code v.name v.code) s tr t ∧ abiPreserved s t ∧
      (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi recoverStack).post s t := by
  obtain ⟨tr, t, run, preserved, post⟩ := recoverFn_ok v s (recover_contract_pre s h)
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Spec.RsaPkcs1Sig.recoverPrecomputedContract, Spec.RsaPkcs1Sig.recoverPrecomputedSig,
    abi, argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right]
  intro cache hash id
  have out := post cache
  unfold recovered at out
  change Spec.RsaPkcs1Sig.Hash.ofId (arg s 6).toNat = some hash at id
  change Spec.Rsa.written t.mem _ _ _
    ((Spec.RsaPkcs1Sig.Hash.ofId (arg s 6).toNat).bind _) at out
  rw [id, Option.bind_some] at out
  exact out

theorem recover_contract_ct (v : PublicImpl) : ConstantTime isa
    (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi recoverStack).pre
    (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi recoverStack).pub
    (VG.Impl.RsaPkcs1Sig.X86.Recover.code v.name v.code) := by
  intro s t tr1 tr2 u w hs ht hp e1 e2
  have is := recover_contract_pre s hs
  have it := recover_contract_pre t ht
  rw [← publicGeometry hp, ← publicBytes hp] at it
  exact (recoverFn_relCT v s t tr1 tr2 u w ⟨is, it⟩ e1 e2).1

end VG.Proof.RsaPkcs1Sig.X86.Rcv
end

end

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86

def satState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 131077 then 16
    else if a = 131080 then 16
    else if a = 131085 then 32
    else if a = 131088 then 64
    else if a = 131093 then 48
    else if a = 131096 then 1
    else if a = 131105 then 64
    else if a = 131108 then 64
    else if a = 131113 then 160
    else if a = 131116 then 112
    else if a = 131121 then 80
    else if a = 131124 then 16 else 0
  rd := [⟨8192, 64⟩, ⟨12288, 1⟩, ⟨16384, 64⟩, ⟨20480, 128⟩]
  wr := [⟨4096, 16⟩, ⟨40960, 896⟩, ⟨0x20004, 52⟩]

theorem satisfiable : ∃ s, (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi recoverStack).pre s := by
  have a0 : arg satState 0 = 4096 := by decide
  have a1 : arg satState 1 = 16 := by decide
  have a2 : arg satState 2 = 8192 := by decide
  have a3 : arg satState 3 = 64 := by decide
  have a4 : arg satState 4 = 12288 := by decide
  have a5 : arg satState 5 = 1 := by decide
  have a6 : arg satState 6 = 0 := by decide
  have a7 : arg satState 7 = 16384 := by decide
  have a8 : arg satState 8 = 64 := by decide
  have a9 : arg satState 9 = 40960 := by decide
  have a10 : arg satState 10 = 112 := by decide
  have a11 : arg satState 11 = 20480 := by decide
  have a12 : arg satState 12 = 16 := by decide
  have e : argAddr satState 0 = 0x20004 := by decide
  have esp : satState.gpr .esp = 0x20000 := rfl
  have hash : ∃ h, Spec.RsaPkcs1Sig.Hash.ofId 0 = some h ∧ 16 = h.len := ⟨.md5, rfl, rfl⟩
  sig_implies_sat [Spec.RsaPkcs1Sig.recoverPrecomputedContract, Spec.RsaPkcs1Sig.recoverPrecomputedSig,
    abi, argSlots, argVal, argBytes, stackBelow]
    [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, e, esp, satState, recoverStack, hash,
      Spec.Rsa.lenValid, Spec.Rsa.publicScratchWords, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords] using satState

theorem recover_verified (v : PublicImpl) :
    Verified target (VG.Impl.RsaPkcs1Sig.X86.Recover.code v.name v.code)
      (Spec.RsaPkcs1Sig.recoverPrecomputedContract abi recoverStack) :=
  ⟨recover_contract_correct v, recover_contract_ct v, satisfiable⟩

end VG.Proof.RsaPkcs1Sig.X86.Rcv

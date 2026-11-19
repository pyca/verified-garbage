module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Recover
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverStackWord
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverDigest
import VerifiedGarbage.Proof.Dsa.X86.FailureLoop
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeHash
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.RsaPkcs1Sig.Verify
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Encode
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Compare
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverRegions
import VerifiedGarbage.Proof.Rsa.X86.PrivZeroTest

/-! ### `RsaPkcs1Sig.X86.RecoverCmpArgs`, which the modules that import this one used -/

section

/-! ### `RsaPkcs1Sig.X86.RecoverReleaseArgs`, which the modules that import this one used -/

section

/-! ### `RsaPkcs1Sig.X86.RecoverDigestArgs`, which this module and modules that import it used -/

section

/-! # Address the recovered digest and load its public encoding parameters -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Sig.X86.Verify (incoming stackAt lea em1Offset em2Offset)
open VG.Impl.RsaPkcs1Sig.X86.Recover

theorem Context.loadArgument {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) {j : Nat} (hj : j < 13) :
    readSrc s (.mem (incoming j)) = some (g.argument j) := by
  change s.load32 (addr (s.gpr .esp) (VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 20 + 4 * j)) = _
  rw [State.load32, ite_eq_left (h.readArg hj), h.argumentValue hj]

theorem digestPtr_ok {g : Geometry} {bs : Fin 4 → List Byte} {s : State} (h : Context g bs s) :
    WP isa (.block digestPtr) s fun t => Context g bs t ∧ t.mem = s.mem ∧
      Keeps [.esi] s t ∧ t.gpr .esi = g.digest := by
  unfold digestPtr lea
  refine wp_movS rfl fun a A _ => ?_
  refine wp_addS rfl fun b B _ => ?_
  have K : Keeps [.esi] s b := A.keeps.trans B.keeps
  have M := B.mem.trans A.mem
  have hb := h.after (by rw [M]; exact Frame.refl _ _) K (K.1 .esp (by decide))
  refine wp_addS (hb.loadArgument (by decide : 3 < 13)) fun c C _ => ?_
  have hc := hb.after (by rw [C.mem]; exact Frame.refl _ _) C.keeps (C.other .esp (by decide))
  refine wp_subS (hc.loadArgument (by decide : 1 < 13)) fun t T _ => WP.block_nil ?_
  have kt := K.trans (C.keeps.trans T.keeps)
  have mt := T.mem.trans (C.mem.trans M)
  refine ⟨h.after (by rw [mt]; exact Frame.refl _ _) kt (kt.1 .esp (by decide)), mt, kt, ?_⟩
  rw [T.gpr, C.gpr, B.gpr, A.gpr, h.sp]
  exact h.valid.digestPointer

theorem encArgs_ok {g : Geometry} {bs : Fin 4 → List Byte} {s : State} (h : Context g bs s) :
    WP isa (.block encArgs) s fun t => Context g bs t ∧ t.mem = s.mem ∧
      Keeps [.edi, .ecx, .edx, .ebp, .esi] s t ∧ t.gpr .edi = g.em2 ∧
      t.gpr .ecx = BitVec.ofNat 32 g.length ∧ t.gpr .edx = g.hash ∧
      t.gpr .ebp = BitVec.ofNat 32 g.outputLength ∧ t.gpr .esi = g.digest := by
  unfold encArgs lea
  rw [WP.block_append_iff, WP.block_append_iff]
  refine wp_movS rfl fun a A _ => ?_
  refine wp_addS rfl fun b B _ => WP.block_nil ?_
  have K : Keeps [.edi] s b := A.keeps.trans B.keeps
  have M := B.mem.trans A.mem
  have hb := h.after (by rw [M]; exact Frame.refl _ _) K (K.1 .esp (by decide))
  unfold incoming stackAt
  refine wp_ldm rfl (hb.readArg (by decide : 3 < 13)) fun c C => ?_
  have hc := hb.after (by rw [C.mem]; exact Frame.refl _ _) C.keeps (C.other .esp (by decide))
  refine wp_ldm rfl (hc.readArg (by decide : 6 < 13)) fun d D => ?_
  have hd := hc.after (by rw [D.mem]; exact Frame.refl _ _) D.keeps (D.other .esp (by decide))
  refine wp_ldm rfl (hd.readArg (by decide : 1 < 13)) fun e E => WP.block_nil ?_
  have ke : Keeps [.edi, .ecx, .edx, .ebp, .esi] s e := (K.mono (by decide)).trans
    ((C.keeps.mono (by decide)).trans ((D.keeps.mono (by decide)).trans (E.keeps.mono (by decide))))
  have me := E.mem.trans (D.mem.trans (C.mem.trans M))
  have he := h.after (by rw [me]; exact Frame.refl _ _) ke (ke.1 .esp (by decide))
  refine WP.mono (digestPtr_ok he) ?_
  rintro t ⟨ht, Mt, Kt, ptr⟩
  refine ⟨ht, Mt.trans me, ke.trans (Kt.mono (by decide)), ?_, ?_, ?_, ?_, ptr⟩
  · rw [Kt.1 .edi (by decide), E.other .edi (by decide), D.other .edi (by decide), C.other .edi (by decide), B.gpr, A.gpr, h.sp]
    rfl
  · rw [Kt.1 .ecx (by decide), E.other .ecx (by decide), D.other .ecx (by decide), C.gpr, hb.argumentValue (by decide : 3 < 13)]
    rfl
  · rw [Kt.1 .edx (by decide), E.other .edx (by decide), D.gpr, hc.argumentValue (by decide : 6 < 13)]
    rfl
  · rw [Kt.1 .ebp (by decide), E.gpr, hd.argumentValue (by decide : 1 < 13)]
    rfl

end VG.Proof.RsaPkcs1Sig.X86.Rcv

end

end

/-! ### `RsaPkcs1Sig.X86.RecoverStatus`, which this module and modules that import it used -/

section

/-! # Save and mask the public operation's status without branching on it -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Sig.X86.Verify

def savedStatus (g : Geometry) (s : State) : BitVec 32 :=
  s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 statusOffset) 32

theorem save_ok {g : Geometry} {bs : Fin 4 → List Byte} {s : State} (h : Context g bs s) :
    WP isa (.block [.store (stackAt statusOffset) .eax]) s fun t => Context g bs t ∧
      savedStatus g t = s.gpr .eax ∧ Frame [localRegion g statusOffset 4] s.mem t.mem ∧ Keeps [] s t := by
  unfold stackAt
  refine wp_stm rfl (by rw [h.address (by decide)]; exact h.inner.write (by decide)) fun t T => WP.block_nil ?_
  have M : t.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 statusOffset) (s.gpr .eax) := by
    rw [T.mem, h.address (by decide)]
  have F : Frame [localRegion g statusOffset 4] s.mem t.mem := by
    rw [M]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨h.after (F.sub ?_) (T.keeps []) (congrFun T.gpr .esp), ?_, F, T.keeps []⟩
  · intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨g.innerRegion, by simp [bodyWrites], localSub (by decide)⟩
  · unfold savedStatus
    rw [M, Mem.readW_writeW_self32]

theorem result_ok {g : Geometry} {bs : Fin 4 → List Byte} {s : State} (h : Context g bs s) :
    WP isa (.block result) s fun t => Context g bs t ∧ t.mem = s.mem ∧ Keeps [.eax, .ecx] s t ∧
      t.gpr .eax = BitVec.ofNat 32 (decide (s.gpr .ebp = 0)).toNat &&& savedStatus g s := by
  unfold result
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Rsa.X86.PrivChecked.zeroTest_ok s) ?_
  rintro a ⟨value, M, K⟩
  have ha := h.after (by rw [M]; exact Frame.refl _ _) K (K.1 .esp (by decide))
  unfold stackAt
  refine wp_ldm rfl (by rw [ha.address (by decide)]; exact ha.inner.read (by decide)) fun b B => ?_
  refine wp_logicS (.inl rfl) rfl fun t T => WP.block_nil ?_
  have kt : Keeps [.eax, .ecx] s t := (K.mono (by decide)).trans
    ((B.keeps.mono (by decide)).trans (T.keeps.mono (by decide)))
  have mt := T.mem.trans (B.mem.trans M)
  refine ⟨h.after (by rw [mt]; exact Frame.refl _ _) kt (kt.1 .esp (by decide)), mt, kt, ?_⟩
  rw [T.gpr, B.other .eax (by decide), value, B.gpr, ha.address (by decide), M]
  rfl

end VG.Proof.RsaPkcs1Sig.X86.Rcv

end

end

/-! # Preserve the acceptance bit and prepare a masked trailing-digest copy -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Sig.X86.Verify (incoming stackAt)
open VG.Impl.RsaPkcs1Sig.X86.Recover

def accepted (g : Geometry) (s : State) : Bool :=
  decide (s.gpr .ebp = 0) && (savedStatus g s).getLsbD 0

theorem acceptance_bit (x y : BitVec 32) :
    BitVec.ofNat 32 (decide (x = 0)).toNat &&& y =
      BitVec.ofNat 32 (decide (x = 0) && y.getLsbD 0).toNat := by
  cases eq : decide (x = 0) with
  | false => change 0#32 &&& y = 0#32; exact BitVec.zero_and
  | true =>
    change 1#32 &&& y = BitVec.ofNat 32 (y.getLsbD 0).toNat
    rw [BitVec.and_comm, BitVec.and_one_eq_setWidth_ofBool_getLsbD]
    cases y.getLsbD 0 <;> rfl

def releaseSetup : List Instr :=
  [.mov .ebx (.reg .eax), .mov .edx (.imm 0), .alu .sub .edx (.reg .eax),
    .mov .edi (.mem (incoming 0)), .mov .ecx (.mem (incoming 1))] ++ digestPtr

theorem releaseSetup_ok {g : Geometry} {bs : Fin 4 → List Byte} {s : State} {good : Bool}
    (h : Context g bs s) (status : s.gpr .eax = BitVec.ofNat 32 good.toNat) :
    WP isa (.block releaseSetup) s fun t => Context g bs t ∧ t.mem = s.mem ∧
      Keeps [.ebx, .edx, .edi, .ecx, .esi] s t ∧ t.gpr .ebx = BitVec.ofNat 32 good.toNat ∧
      t.gpr .edx = -BitVec.ofNat 32 good.toNat ∧ t.gpr .edi = g.output ∧
      t.gpr .ecx = BitVec.ofNat 32 g.outputLength ∧ t.gpr .esi = g.digest := by
  unfold releaseSetup
  rw [WP.block_append_iff]
  refine wp_movS rfl fun a A _ => ?_
  refine wp_movS rfl fun b B _ => ?_
  refine wp_subS rfl fun c C _ => ?_
  have K : Keeps [.ebx, .edx, .edi, .ecx, .esi] s c :=
    (A.keeps.mono (by decide)).trans ((B.keeps.mono (by decide)).trans (C.keeps.mono (by decide)))
  have M := C.mem.trans (B.mem.trans A.mem)
  have hc := h.after (by rw [M]; exact Frame.refl _ _) K (K.1 .esp (by decide))
  unfold incoming stackAt
  refine wp_ldm rfl (hc.readArg (by decide : 0 < 13)) fun d D => ?_
  have hd := hc.after (by rw [D.mem]; exact Frame.refl _ _) D.keeps (D.other .esp (by decide))
  refine wp_ldm rfl (hd.readArg (by decide : 1 < 13)) fun e E => WP.block_nil ?_
  have ke := K.trans ((D.keeps.mono (by decide)).trans (E.keeps.mono (by decide)))
  have me := E.mem.trans (D.mem.trans M)
  have he := h.after (by rw [me]; exact Frame.refl _ _) ke (ke.1 .esp (by decide))
  refine WP.mono (digestPtr_ok he) ?_
  rintro t ⟨ht, Mt, Kt, ptr⟩
  refine ⟨ht, Mt.trans me, ke.trans (Kt.mono (by decide)), ?_, ?_, ?_, ?_, ptr⟩
  · rw [Kt.1 .ebx (by decide), E.other .ebx (by decide), D.other .ebx (by decide), C.other .ebx (by decide), B.other .ebx (by decide), A.gpr, status]
  · rw [Kt.1 .edx (by decide), E.other .edx (by decide), D.other .edx (by decide), C.gpr, B.gpr,
      B.other .eax (by decide), A.other .eax (by decide), status]
    change 0#32 - BitVec.ofNat 32 good.toNat = _
    rw [BitVec.zero_sub]
  · rw [Kt.1 .edi (by decide), E.other .edi (by decide), D.gpr, hc.argumentValue (by decide : 0 < 13)]
    rfl
  · rw [Kt.1 .ecx (by decide), E.gpr, hd.argumentValue (by decide : 1 < 13)]
    rfl

theorem releaseArgs_ok {g : Geometry} {bs : Fin 4 → List Byte} {s : State} (h : Context g bs s) :
    WP isa (.block releaseArgs) s fun t => Context g bs t ∧ t.mem = s.mem ∧
      Keeps [.eax, .ebx, .edx, .edi, .ecx, .esi] s t ∧
      t.gpr .ebx = BitVec.ofNat 32 (accepted g s).toNat ∧
      t.gpr .edx = -BitVec.ofNat 32 (accepted g s).toNat ∧ t.gpr .edi = g.output ∧
      t.gpr .ecx = BitVec.ofNat 32 g.outputLength ∧ t.gpr .esi = g.digest := by
  change WP isa (.block (VG.Impl.RsaPkcs1Sig.X86.Verify.result ++ releaseSetup)) s _
  rw [WP.block_append_iff]
  refine WP.mono (result_ok h) ?_
  rintro a ⟨ha, M, K, value⟩
  have ax : a.gpr .eax = BitVec.ofNat 32 (accepted g s).toNat := value.trans (acceptance_bit _ _)
  refine WP.mono (releaseSetup_ok ha ax) ?_
  rintro t ⟨ht, Mt, Kt, good, mask, dst, cnt, src⟩
  exact ⟨ht, Mt.trans M, (K.mono (by decide)).trans (Kt.mono (by decide)), good, mask, dst, cnt, src⟩

end VG.Proof.RsaPkcs1Sig.X86.Rcv

end

end

/-! # Compare the public RSA result against the separately encoded digest -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Sig.X86.Verify (lea em1Offset em2Offset incoming stackAt)
open VG.Impl.RsaPkcs1Sig.X86.Recover (cmpArgs)

theorem cmpArgs_ok {g : Geometry} {bs : Fin 4 → List Byte} {s : State} (h : Context g bs s) :
    WP isa (.block cmpArgs) s fun t => Context g bs t ∧ t.mem = s.mem ∧
      Keeps [.esi, .edi, .ecx] s t ∧ t.gpr .esi = g.em1 ∧ t.gpr .edi = g.em2 ∧
      t.gpr .ecx = BitVec.ofNat 32 g.length := by
  unfold cmpArgs lea incoming stackAt
  refine wp_movS rfl fun a A _ => ?_
  refine wp_addS rfl fun b B _ => ?_
  refine wp_movS rfl fun c C _ => ?_
  refine wp_addS rfl fun d D _ => ?_
  have K : Keeps [.esi, .edi, .ecx] s d := (A.keeps.mono (by decide)).trans
    ((B.keeps.mono (by decide)).trans ((C.keeps.mono (by decide)).trans (D.keeps.mono (by decide))))
  have M : d.mem = s.mem := D.mem.trans (C.mem.trans (B.mem.trans A.mem))
  have hd := h.after (by rw [M]; exact Frame.refl _ _) K (K.1 .esp (by decide))
  refine wp_ldm rfl (hd.readArg (by decide : 3 < 13)) fun t T => WP.block_nil ?_
  have kt := K.trans (T.keeps.mono (by decide))
  have mt := T.mem.trans M
  refine ⟨h.after (by rw [mt]; exact Frame.refl _ _) kt (kt.1 .esp (by decide)), mt, kt, ?_, ?_, ?_⟩
  · rw [T.other .esi (by decide), D.other .esi (by decide), C.other .esi (by decide), B.gpr, A.gpr, h.sp]
    rfl
  · rw [T.other .edi (by decide), D.gpr, C.gpr, B.other .esp (by decide), A.other .esp (by decide), h.sp]
    rfl
  · rw [T.gpr, hd.argumentValue (by decide : 3 < 13)]
    rfl

theorem compare_ok {g : Geometry} {bs : Fin 4 → List Byte} {s : State} (h : Context g bs s)
    (src : s.gpr .esi = g.em1) (dst : s.gpr .edi = g.em2) (cnt : s.gpr .ecx = BitVec.ofNat 32 g.length) :
    WP isa VG.Impl.RsaPkcs1Sig.X86.compare s fun t => Context g bs t ∧ t.mem = s.mem ∧
      Keeps [.esi, .edi, .ebp, .eax, .edx, .ecx] s t ∧
      (t.gpr .ebp = 0 ↔ Spec.Rsa.bytesAt s.mem (byteAddr g.em1) g.length =
        Spec.Rsa.bytesAt s.mem (byteAddr g.em2) g.length) := by
  have em1Fit := h.valid.encodingFit (d := em1Offset)
    (by have := h.valid.maxLength; simp only [em1Offset, VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes]; omega_using [this])
  have read1 : InRegions (s.rd ++ s.wr) (byteAddr g.em1) g.length := by
    obtain ⟨r, hr, hc⟩ := h.em1Write
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have read2 : InRegions (s.rd ++ s.wr) (byteAddr g.em2) g.length := by
    obtain ⟨r, hr, hc⟩ := h.em2Write
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (VG.Proof.RsaPkcs1Sig.X86.compare_ok s
    (by have := h.valid.minLength; omega_using [this]) (by have := h.valid.maxLength; omega_using [this])
    em1Fit h.em2Fit read1 read2 src dst cnt) ?_
  rintro t ⟨eq, M, K⟩
  exact ⟨h.after (by rw [M]; exact Frame.refl _ _) K (K.1 .esp (by decide)), M, K, eq⟩

end VG.Proof.RsaPkcs1Sig.X86.Rcv

end

end

/-! ### `RsaPkcs1Sig.X86.RecoverEncoding`, which the modules that import this one used -/

section

/-! # Re-encode the trailing digest in a separate buffer -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86 VG.WriteBytes

def digestBytes (g : Geometry) (s : State) : List Byte :=
  Spec.Rsa.bytesAt s.mem (byteAddr g.digest) g.outputLength

theorem Context.digestRead {g : Geometry} {bs : Fin 4 → List Byte} {s : State} (h : Context g bs s) :
    InRegions (s.rd ++ s.wr) (byteAddr g.digest) g.outputLength := by
  have read : InRegions (s.rd ++ s.wr) (byteAddr g.em1) g.length := by
    obtain ⟨r, hr, hc⟩ := h.em1Write
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  rw [h.valid.digestAddr]
  exact CallLay.inRegions_sub (off := g.length - g.outputLength) read
    (by have := h.valid.outputFits; omega_using [this]) (by have := h.valid.maxLength; omega_using [this])

theorem encoding_pre {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) (dst : s.gpr .edi = g.em2)
    (len : s.gpr .ecx = BitVec.ofNat 32 g.length) (hash : s.gpr .edx = g.hash)
    (src : s.gpr .esi = g.digest) (count : s.gpr .ebp = BitVec.ofNat 32 g.outputLength) :
    EPre s g.hash g.length := by
  have out32 : g.outputLength < 2 ^ 32 := by have := h.valid.outputBound; omega_using [this]
  refine ⟨hash, len, h.valid.maxLength, ⟨by rw [dst]; exact h.em2Fit, ?_⟩, ?_⟩
  · intro i hi
    rw [dst, byteAddr_add (by have := h.em2Fit; omega_using [hi, this])]
    exact CallLay.inRegions_sub (off := i) h.em2Write (by omega_using [hi]) (by have := h.valid.maxLength; omega_using [this])
  · rw [count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt out32]
    refine ⟨by rw [src]; exact h.valid.digestFit, ?_, ?_⟩
    · intro i hi
      rw [src, byteAddr_add (by have := h.valid.digestFit; omega_using [hi, this])]
      exact CallLay.inRegions_sub (off := i) h.digestRead (by omega_using [hi]) (by have := h.valid.outputBound; omega_using [out32])
    · intro i hi j hj
      rw [src, byteAddr_add (by have := h.valid.digestFit; omega_using [hi, this]), dst, byteAddr_add (by have := h.em2Fit; omega_using [hj, this])]
      exact VG.Proof.RsaPkcs1Sig.ne_of_disjoint
        (h.encodingsSeparate.sub_left h.valid.digestSub)
        (by have := h.valid.outputBound; omega_using [out32]) (by have := h.valid.maxLength; omega_using [this]) hi hj

def Encoded (g : Geometry) (s : State) : Prop :=
  match encodeId g.hash (digestBytes g s) g.length with
  | none => s.gpr .eax = 0
  | some em => s.gpr .eax = 1 ∧ Spec.Rsa.bytesAt s.mem (byteAddr g.em2) g.length = em

theorem encoding_ok {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) (dst : s.gpr .edi = g.em2)
    (len : s.gpr .ecx = BitVec.ofNat 32 g.length) (hash : s.gpr .edx = g.hash)
    (src : s.gpr .esi = g.digest) (count : s.gpr .ebp = BitVec.ofNat 32 g.outputLength) :
    WP isa VG.Impl.RsaPkcs1Sig.X86.encode s fun t => Context g bs t ∧
      Frame [⟨byteAddr g.em2, g.length⟩] s.mem t.mem ∧ Keeps clob s t ∧ Encoded g t := by
  refine WP.mono (encode_ok (encoding_pre h dst len hash src count)) ?_
  rintro t ⟨K, out⟩
  have out32 : g.outputLength < 2 ^ 32 := by have := h.valid.outputBound; omega_using [this]
  rw [src, count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt out32] at out
  change EOut s t (encodeId g.hash (digestBytes g s) g.length) at out
  have frame : Frame [⟨byteAddr g.em2, g.length⟩] s.mem t.mem := by
    cases e : encodeId g.hash (digestBytes g s) g.length with
    | none => rw [e] at out; rw [out.2]; exact Frame.refl _ _
    | some em =>
      rw [e] at out
      have length : em.length = g.length := by
        unfold encodeId at e
        cases id : Spec.RsaPkcs1Sig.Hash.ofId g.hash.toNat with
        | none => simp [id] at e
        | some hv => simp only [id, Option.bind_some] at e; exact encode_length e
      rw [out.2, dst]
      exact writeBytes_frame _ _ _ (by rw [length]; exact Region.contains_self _ _)
  have bytes : digestBytes g t = digestBytes g s :=
    VG.Proof.Rsa.rsa_bytes_frame frame (by have := h.valid.outputBound; omega_using [out32])
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr
          exact h.encodingsSeparate.sub_left h.valid.digestSub)
  refine ⟨h.after (frame.sub ?_) K (K.1 .esp (by decide)), frame, K, ?_⟩
  · intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨g.innerRegion, by simp [bodyWrites], h.em2Sub⟩
  · unfold Encoded
    rw [bytes]
    cases e : encodeId g.hash (digestBytes g s) g.length with
    | none => rw [e] at out; exact out.1
    | some em =>
      rw [e] at out
      refine ⟨out.1, ?_⟩
      rw [out.2, dst]
      have length : em.length = g.length := by
        unfold encodeId at e
        cases id : Spec.RsaPkcs1Sig.Hash.ofId g.hash.toNat with
        | none => simp [id] at e
        | some hv => simp only [id, Option.bind_some] at e; exact encode_length e
      rw [← length]
      exact bytesAt_writeBytes _ _ _ (by rw [length]; have := h.valid.maxLength; omega_using [this])

end VG.Proof.RsaPkcs1Sig.X86.Rcv

end

end

/-! # Invalid encodings clear every output byte -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Sig.X86.Verify (incoming stackAt)
open VG.Impl.RsaPkcs1Sig.X86.Recover

theorem zeroArgs_ok {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) :
    WP isa (.block [.mov .esi (.mem (incoming 0)), .mov .ecx (.mem (incoming 1)), .mov .eax (.imm 0)]) s
      fun t => Context g bs t ∧ t.mem = s.mem ∧ Keeps [.esi, .ecx, .eax] s t ∧
        t.gpr .esi = g.output ∧ t.gpr .ecx = BitVec.ofNat 32 g.outputLength ∧ t.gpr .eax = 0 := by
  unfold incoming stackAt
  refine wp_ldm rfl (h.readArg (by decide : 0 < 13)) fun a A => ?_
  have ha : Context g bs a := h.after (by rw [A.mem]; exact Frame.refl _ _) A.keeps (A.other .esp (by decide))
  refine wp_ldm rfl (ha.readArg (by decide : 1 < 13)) fun b B => ?_
  refine wp_movS rfl fun c C _ => WP.block_nil ?_
  have K : Keeps [.esi, .ecx, .eax] s c :=
    (A.keeps.mono (by decide)).trans ((B.keeps.mono (by decide)).trans (C.keeps.mono (by decide)))
  have M : c.mem = s.mem := C.mem.trans (B.mem.trans A.mem)
  refine ⟨h.after (by rw [M]; exact Frame.refl _ _) K (K.1 .esp (by decide)), M, K, ?_, ?_, C.gpr⟩
  · rw [C.other .esi (by decide), B.other .esi (by decide), A.gpr, h.argumentValue (by decide : 0 < 13)]; rfl
  · rw [C.other .ecx (by decide), B.gpr, ha.argumentValue (by decide : 1 < 13)]; rfl

theorem zeroOut_ok {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) : WP isa zeroOut s fun t => Context g bs t ∧
      Spec.Rsa.bytesAt t.mem (byteAddr g.output) g.outputLength = List.replicate g.outputLength 0 ∧
      t.gpr .eax = 0 ∧ Frame [g.outputRegion] s.mem t.mem ∧ Keeps [.esi, .ecx, .eax] s t := by
  unfold zeroOut incoming stackAt
  refine WP.seq (wp_ldm rfl (h.readArg (by decide : 0 < 13)) fun a A => ?_)
  have ha : Context g bs a := h.after (by rw [A.mem]; exact Frame.refl _ _) A.keeps (A.other .esp (by decide))
  refine wp_ldm rfl (ha.readArg (by decide : 1 < 13)) fun b B => ?_
  refine wp_movS rfl fun c C _ => WP.block_nil ?_
  have K : Keeps [.esi, .ecx, .eax] s c :=
    (A.keeps.mono (by decide)).trans ((B.keeps.mono (by decide)).trans (C.keeps.mono (by decide)))
  have M : c.mem = s.mem := C.mem.trans (B.mem.trans A.mem)
  have k32 : g.outputLength < 2 ^ 32 := by have := h.valid.outputBound; omega_using [this]
  refine WP.mono (VG.Proof.Dsa.X86.failureLoop_ok
    (by have := h.valid.outputPositive; omega_using [this]) k32 h.valid.outputFit
    (by rw [C.other .esi (by decide), B.other .esi (by decide), A.gpr, h.argumentValue (by decide : 0 < 13)]; rfl)
    (by rw [C.other .ecx (by decide), B.gpr, ha.argumentValue (by decide : 1 < 13)]; rfl) C.gpr ?_) ?_
  · intro i hi
    rw [K.2.2]
    exact CallLay.inRegions_sub (off := i) h.outputWrite (by omega_using [hi]) (by omega_using [k32])
  · rintro t ⟨V, Z, O, T⟩
    have F : Frame [g.outputRegion] s.mem t.mem := by
      rw [M] at O
      simpa only [VG.Proof.Mont.off, BitVec.add_zero, Geometry.outputRegion, byteAddr] using outside_frame O (by omega_using [k32])
    have keep := K.trans (T.mono (by decide))
    refine ⟨h.after (F.sub ?_) keep (keep.1 .esp (by decide)), V, Z, F, keep⟩
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩

end VG.Proof.RsaPkcs1Sig.X86.Rcv

module

public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
public import VerifiedGarbage.Proof.Pbkdf2.Contract
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.Proof.Sha256.X86_64.Shared
public import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Md
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
meta import VerifiedGarbage.Proof.Sha256.X86_64.Shared
meta import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Md
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Hmac.Generic.Implies
meta import VerifiedGarbage.Proof.Framework.TaintBatch
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Proof.MdStream.X86_64.OneShotCT
public import VerifiedGarbage.Spec.Sha256.Contract
public import VerifiedGarbage.Proof.Sha256.Md
public import VerifiedGarbage.Impl.Sha256.X86_64.Stream
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MdStream.X86_64.OneShotCT
meta import VerifiedGarbage.Spec.Sha256.Contract
meta import VerifiedGarbage.Proof.Sha256.Md
meta import VerifiedGarbage.Impl.Sha256.X86_64.Stream
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Common
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MdStream.DigestScratch
meta import VerifiedGarbage.Proof.MdStream.DigestScratch

/-! ### `Sha256.X86_64.OneShot`, which this module and modules that import it used -/

section

/-!
# The one-shot SHA-256 and SHA-224 digests on x86-64

`vg_sha256_digest` and `vg_sha224_digest` are the generic one-shot digest
(`Impl/MdStream/X86_64/OneShot.lean`) for SHA-256's streaming parameters with
the member's digest `o`, its initial hash value's code `initWith iv` and an
implementation `f` of the compression function, as SHA-512's are
(`Proof/Sha512/X86_64/OneShot.lean`). Its body is verified by the generic
proofs (`OneShot.verified`) against `OneShot.oneK`, which implies the
contract of `digest` with a scratch buffer as its last argument
(`digestScratchContract`); in a frame of its own, it is
`Spec.Sha256.digestContract`.
-/

@[expose] public section

namespace VG.Proof.Sha256.X86_64.OneShot

open VG.X86_64 VG.Proof.MdStream.X86_64
open VG.Impl.Sha256.X86_64.Stream (Callee params initWith)

/-- The streaming parameters, with the digest `o`. -/
abbrev Po (o : List Instr) : Impl.MdStream.X86_64.Params := { params with out := o }

/-- The scratch buffer's 8-byte words, and the frame holding it. -/
abbrev words : Nat := 88
abbrev frame : Nat := 728

theorem scratchBytes_eq (o : List Instr) : Impl.MdStream.X86_64.OneShot.scratchBytes (Po o) = 8 * words :=
  show Impl.MdStream.X86_64.OneShot.scratchBytes params = 8 * words by decide

theorem frameBytes_eq (o : List Instr) : Impl.MdStream.X86_64.OneShot.frameBytes (Po o) = frame :=
  show Impl.MdStream.X86_64.OneShot.frameBytes params = frame by decide

/-- The one-shot digest's body, with `initWith iv`, given its scratch buffer. -/
abbrev body (o : List Instr) (iv : Spec.Sha256.HashValue) (f : Callee) : Prog isa :=
  Impl.MdStream.X86_64.OneShot.body (Po o) (initWith iv) f.name f.code

/-- The one-shot digest. -/
abbrev digest (o : List Instr) (iv : Spec.Sha256.HashValue) (f : Callee) : Prog isa :=
  Impl.MdStream.X86_64.OneShot.digest (Po o) (initWith iv) f.name f.code

theorem fits (o : List Instr) : OneShot.Fits (Po o) :=
  ⟨by rw [scratchBytes_eq]; decide⟩

theorem dims (o : List Instr) : Dims (Po o) :=
  ⟨Stream.dims.B, Stream.dims.N, Stream.dims.L, Stream.dims.so⟩

/-! ## The initial hash value's code -/

theorem init_mxcsr (iv : Spec.Sha256.HashValue) :
    (initWith iv).allInstrs (fun i => !loadsMxcsr i) = true := by
  rw [Code.allInstrs_eq]
  simp only [initWith, instrs, List.all_eq_true, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro _ ⟨_, _, rfl | rfl | rfl | rfl | rfl | rfl⟩ <;> rfl

theorem init_sp (iv : Spec.Sha256.HashValue) : (initWith iv).all (fun i => !isa.writesSp i) = true := by
  simp only [initWith, Code.all, List.all_eq_true, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro _ ⟨_, _, rfl | rfl | rfl | rfl | rfl | rfl⟩ <;> rfl

theorem init_writes (iv : Spec.Sha256.HashValue) :
    ∀ r, r ≠ .rax → ∀ i ∈ instrs (initWith iv), Taint.clobbers i r = false := by
  intro r hr i hi
  simp only [initWith, instrs, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hi
  obtain ⟨_, _, rfl | rfl | rfl | rfl | rfl | rfl⟩ := hi <;> simp [Taint.clobbers, Taint.dstOf, Ne.symm hr]

theorem init_hi (o : List Instr) (iv : Spec.Sha256.HashValue) :
    ∀ s, (OneShot.initK (P := Po o) md iv).pre s → ∃ t s', Exec isa (initWith iv) s t s' ∧ abiPreserved s s' ∧
      (OneShot.initK (P := Po o) md iv).post s s' := fun s hs => by
  obtain ⟨t, s', he, h⟩ := Stream.init_correct iv hs
  exact ⟨t, s', he, abiPreserved_of_exec (init_mxcsr iv) he h.1, h.2⟩

theorem init_check256 : ∃ hc, (taint.check (Taint.ofRegs [.rdi]) (initWith Spec.Sha256.H0) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem init_check224 :
    ∃ hc, (taint.check (Taint.ofRegs [.rdi]) (initWith Spec.Sha256.H0_224) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-! ## The precondition -/

/-- A state satisfying the precondition. -/
def sat (o : List Instr) (D : Nat) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rdx => 0x2000 | .rcx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 0⟩]
  wr := [⟨0x2000, D⟩, ⟨0x3000, Impl.MdStream.X86_64.OneShot.scratchBytes (Po o)⟩]

theorem sat_pre (o : List Instr) {D : Nat} (hD : D ≤ 64) : OneShot.Pre (Po o) D (sat o D) := by
  have e := scratchBytes_eq o
  have d : ∀ {a b : Addr} {n m : Nat}, a.toNat + n ≤ b.toNat → b.toNat + m ≤ 2 ^ 64 →
      Region.Disjoint ⟨a, n⟩ ⟨b, m⟩ := fun h h' => Offset.disjoint_of_le h h'
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [OneShot.dR, OneShot.oR, OneShot.wR, OneShot.retR, OneShot.stkR, OneShot.dp, OneShot.len,
    OneShot.out, OneShot.sb, sat, e, VG.X86_64.below]
  · exact d (by decide) (by simp; omega_using [hD])
  · exact d (by decide) (by decide)
  · exact d (by simp; omega_using [hD]) (by decide)
  · exact (d (by simp; omega_using [hD]) (by decide)).symm
  · exact (d (by decide) (by decide)).symm
  · exact (d (by decide) (by decide)).symm
  · exact (d (by simp; omega_using [hD]) (by decide)).symm
  · exact (d (by decide) (by decide)).symm

/-! ## The contracts -/

/-- `vg_<alg>_digest`'s signature with its scratch buffer as its last
argument. -/
def digestScratchSig (D : Nat) : Sig where
  params := [("data", .slice false .u8 "len"), ("out", .array true .u8 D), ("scratch", .array true .u64 words)]

/-- `Spec.Sha256.digestPost`, whatever `scratch` is. -/
def digestScratchContract (A : Abi isa) (D : Nat) (digest : List Byte → List Byte) (stack : Nat) : Contract isa :=
  (digestScratchSig D).contract A (post := fun data len out _scratch =>
    Spec.Sha256.digestPost D digest A.ptrBits data len out) (stack := stack)

theorem implies (o : List Instr) {iv : Spec.Sha256.HashValue} {D : Nat} {digest : List Byte → List Byte}
    (hD : D ≤ 64) (hdg : ∀ m, (md.hash iv m).take D = digest m) :
    (OneShot.oneK (P := Po o) md iv D).Implies (digestScratchContract X86_64.abi D digest 8) := by
  refine
    { pre := fun s h => ?_
      post := fun s s' _ h => ?_
      pub := by implies_pub [digestScratchContract, digestScratchSig, Spec.Sha256.digestPost,
        OneShot.oneK, X86_64.abi, X86_64.argRegs]
      sat := ⟨sat o D, ?_⟩ }
  · sig_pre [digestScratchContract, digestScratchSig, Spec.Sha256.digestPost, X86_64.abi, X86_64.argRegs] at h
    obtain ⟨-, hrd, hwr, hdo, hdw, how, -, hro, hrw, hsd, hso, hsw, -⟩ := h
    have e : Impl.MdStream.X86_64.OneShot.scratchBytes (Po o) = words * 8 := by
      rw [scratchBytes_eq, Nat.mul_comm]
    refine ⟨hrd, ?_, hdo, ?_, ?_, hro, ?_, hsd, hso, ?_⟩ <;> simp only [OneShot.wR, OneShot.sb, e]
    exacts [hwr, hdw, how, hrw, hsw]
  · sig_post [digestScratchContract, digestScratchSig, Spec.Sha256.digestPost, X86_64.abi, X86_64.argRegs]
    rw [← hdg]
    exact h trivial
  · have hp := sat_pre o hD
    sig_pre [digestScratchContract, digestScratchSig, Spec.Sha256.digestPost, X86_64.abi, X86_64.argRegs]
    have e : Impl.MdStream.X86_64.OneShot.scratchBytes (Po o) = words * 8 := by
      rw [scratchBytes_eq, Nat.mul_comm]
    have d₁ := hp.d_o; have d₂ := hp.d_w; have d₃ := hp.o_w; have d₄ := hp.ret_o; have d₅ := hp.ret_w
    have d₆ := hp.stk_d; have d₇ := hp.stk_o; have d₈ := hp.stk_w
    simp only [OneShot.dR, OneShot.oR, OneShot.wR, OneShot.retR, OneShot.stkR, OneShot.dp, OneShot.len,
      OneShot.out, OneShot.sb, sat, e, VG.X86_64.below] at d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈
    refine ⟨by decide, rfl, by rw [e], d₁, d₂, d₃, (Offset.disjoint_of_le (by decide) (by decide)).symm,
      d₄, d₅, d₆, d₇, d₈, by decide, by simp; omega_using [hD], by decide⟩

/-- SHA-256's digest is all of the final hash value. -/
theorem hash_take (m : List Byte) : (md.hash Spec.Sha256.H0 m).take 32 = Spec.Sha256.hash m := by
  rw [Proof.Sha256.hash_eq]
  exact List.take_of_length_le (Nat.le_of_eq (Proof.Sha256.md.digest_length _))

/-- SHA-224's digest is the first 28 bytes of the final hash value. -/
theorem sha224_take (m : List Byte) : (md.hash Spec.Sha256.H0_224 m).take 28 = Spec.Sha256.sha224 m := rfl

/-! ## Each member's code -/

/-- What the generic proofs need of a member's one-shot digest, whose `o`
writes the first `D` bytes of the final hash value, from one check of each. -/
structure Member (o : List Instr) (D : Nat) : Prop where
  shape : ShapeD (P := Po o) md D
  taints : OneShot.Taints (Po o)
  hD : D = 32 ∨ D = 28
  mxcsr : ∀ f : Callee, f.code.allInstrs (fun i => !loadsMxcsr i) = true →
    (Impl.MdStream.X86_64.OneShot.body (Po o) (.block []) f.name f.code).allInstrs (fun i => !loadsMxcsr i) = true
  spSafe : ∀ f : Callee, f.code.all (fun i => !isa.writesSp i) = true →
    (Impl.MdStream.X86_64.OneShot.body (Po o) (.block []) f.name f.code).all (fun i => !isa.writesSp i) = true
  depth : ∀ f : Callee, f.code.x86_64Depth = 0 →
    (Impl.MdStream.X86_64.OneShot.body (Po o) (.block []) f.name f.code).x86_64Depth ≤ 8

theorem Member.le {o : List Instr} {D : Nat} (c : Member o D) : D ≤ 64 := by
  rcases c.hD with rfl | rfl <;> decide

/-- The body, against its contract with the scratch buffer. -/
theorem scratch_verified {o : List Instr} {D : Nat} (c : Member o D) {iv : Spec.Sha256.HashValue}
    (hict : ∃ hc, (taint.check (Taint.ofRegs [.rdi]) (initWith iv) hc).isSome = true)
    {digest : List Byte → List Byte} (hdg : ∀ m, (md.hash iv m).take D = digest m) {f : Callee}
    (hf : f.Ok) (hm : f.code.allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (body o iv f) (digestScratchContract X86_64.abi D digest 8) :=
  (OneShot.verified (fits o) (dims o) c.shape c.taints (init_hi o iv) (init_writes iv) rfl hict
    ((Stream.callee hf).withOut o) (by rw [OneShot.body_allInstrs, c.mxcsr f hm, init_mxcsr]; rfl)
    ⟨_, sat_pre o c.le⟩).of_implies (implies o c.le hdg)

/-- The one-shot digest, with its scratch buffer in a frame of its own. -/
theorem verified {o : List Instr} {D : Nat} (c : Member o D) {iv : Spec.Sha256.HashValue}
    (hict : ∃ hc, (taint.check (Taint.ofRegs [.rdi]) (initWith iv) hc).isSome = true)
    {dg : List Byte → List Byte} (hdg : ∀ m, (md.hash iv m).take D = dg m) {f : Callee}
    (hf : f.Ok) (hm : f.code.allInstrs (fun i => !loadsMxcsr i) = true)
    (hs : f.code.all (fun i => !isa.writesSp i) = true) (hd : f.code.x86_64Depth = 0) :
    Verified X86_64.target (digest o iv f) (Spec.Sha256.digestContract X86_64.abi D dg (8 + frame)) := by
  have h := scratch_verified c hict hdg hf hm
  have hsp : (body o iv f).all (fun i => !isa.writesSp i) = true := by
    rw [OneShot.body_all, c.spSafe f hs, init_sp]; rfl
  have hdp : (body o iv f).x86_64Depth ≤ 8 := by
    rw [OneShot.body_depth _ (rfl : (initWith iv).x86_64Depth = 0)]; exact c.depth f hd
  show Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch
    (Impl.MdStream.X86_64.OneShot.frameBytes (Po o)) .rcx (body o iv f)) _
  rw [frameBytes_eq]
  rcases c.hD with rfl | rfl <;>
  exact X86_64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := words) (stack := 8) (bytes := frame)
    h (by decide) (by decide) (by decide) hsp hdp
    (fun vs m m₁ m₂ r hl hb h => Proof.MdStream.Digest.digestPostOut_local _ _ _ vs m m₁ m₂ r hl hb h)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem spSafe {o : List Instr} {D : Nat} (c : Member o D) (iv : Spec.Sha256.HashValue) {f : Callee}
    (hs : f.code.all (fun i => !isa.writesSp i) = true) :
    (digest o iv f).all (fun i => !isa.writesSp i) = true :=
  X86_64.withStackScratch_spSafe (by decide) (by rw [OneShot.body_all, c.spSafe f hs, init_sp]; rfl)

section
open Impl.MdStream.X86_64 (out32 compressN compressAt compressWith)

theorem code256 : Member (out32 8 true) 32 where
  shape := Stream.shape.toD
  taints := ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩
  hD := .inl rfl
  mxcsr f hm := by
    simp only [Impl.MdStream.X86_64.OneShot.body, Impl.MdStream.X86_64.OneShot.whole, Impl.MdStream.X86_64.OneShot.tail, Impl.MdStream.X86_64.OneShot.copyTail, compressN, compressAt, compressWith, Code.allInstrs, hm,
      Bool.true_and, Bool.and_true]
    decide +kernel
  spSafe f h := by
    simp only [Impl.MdStream.X86_64.OneShot.body, Impl.MdStream.X86_64.OneShot.whole, Impl.MdStream.X86_64.OneShot.tail, Impl.MdStream.X86_64.OneShot.copyTail, compressN, compressAt, compressWith, Code.all, h,
      Bool.true_and]
    decide +kernel
  depth f h := by
    simp only [Impl.MdStream.X86_64.OneShot.body, Impl.MdStream.X86_64.OneShot.whole, Impl.MdStream.X86_64.OneShot.tail, Impl.MdStream.X86_64.OneShot.copyTail, compressN, compressAt, compressWith, Code.x86_64Depth, h]
    decide +kernel

theorem code224 : Member (out32 7 true) 28 where
  shape := Stream.shape224
  taints := ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩
  hD := .inr rfl
  mxcsr f hm := by
    simp only [Impl.MdStream.X86_64.OneShot.body, Impl.MdStream.X86_64.OneShot.whole, Impl.MdStream.X86_64.OneShot.tail, Impl.MdStream.X86_64.OneShot.copyTail, compressN, compressAt, compressWith, Code.allInstrs, hm,
      Bool.true_and, Bool.and_true]
    decide +kernel
  spSafe f h := by
    simp only [Impl.MdStream.X86_64.OneShot.body, Impl.MdStream.X86_64.OneShot.whole, Impl.MdStream.X86_64.OneShot.tail, Impl.MdStream.X86_64.OneShot.copyTail, compressN, compressAt, compressWith, Code.all, h,
      Bool.true_and]
    decide +kernel
  depth f h := by
    simp only [Impl.MdStream.X86_64.OneShot.body, Impl.MdStream.X86_64.OneShot.whole, Impl.MdStream.X86_64.OneShot.tail, Impl.MdStream.X86_64.OneShot.copyTail, compressN, compressAt, compressWith, Code.x86_64Depth, h]
    decide +kernel

end

/-! ## With the working space the compression function uses

The one-shot digest made with `so` bytes of working space for the
compression function (`Stream.paramsS`), for an implementation that uses no
more than that: its buffer and frame shrink with it. -/

/-- The streaming parameters with `so` bytes for the compression function,
with the digest `o`. -/
abbrev PoS (so : Nat) (o : List Instr) : Impl.MdStream.X86_64.Params := { Stream.paramsS so with out := o }

/-- The scratch buffer's 8-byte words, and the frame holding it. -/
abbrev wordsS (so : Nat) : Nat := so / 8 + 18
abbrev frameS (so : Nat) : Nat := Impl.MdStream.X86_64.OneShot.frameBytes (Stream.paramsS so)

theorem scratchBytesS_eq {so : Nat} (h : so = 0 ∨ so = 112) (o : List Instr) :
    Impl.MdStream.X86_64.OneShot.scratchBytes (PoS so o) = 8 * wordsS so := by
  show Impl.MdStream.X86_64.OneShot.scratchBytes (Stream.paramsS so) = 8 * wordsS so
  rcases h with rfl | rfl <;> decide

theorem fitsS {so : Nat} (h : so = 0 ∨ so = 112) (o : List Instr) : OneShot.Fits (PoS so o) :=
  ⟨by rw [scratchBytesS_eq h]; rcases h with rfl | rfl <;> decide⟩

theorem dimsS {so : Nat} (h : so = 0 ∨ so = 112) (o : List Instr) : Dims (PoS so o) :=
  ⟨Stream.dims.B, Stream.dims.N, Stream.dims.L, show so ≤ 2048 by omega_using [h]⟩

/-- The one-shot digest's body, with `initWith iv`, given its scratch buffer. -/
abbrev bodyS (so : Nat) (o : List Instr) (iv : Spec.Sha256.HashValue) (f : Callee) : Prog isa :=
  Impl.MdStream.X86_64.OneShot.body (PoS so o) (initWith iv) f.name f.code

/-- The one-shot digest. -/
abbrev digestS (so : Nat) (o : List Instr) (iv : Spec.Sha256.HashValue) (f : Callee) : Prog isa :=
  Impl.MdStream.X86_64.OneShot.digest (PoS so o) (initWith iv) f.name f.code

/-- A state satisfying the precondition. -/
def satS (so : Nat) (o : List Instr) (D : Nat) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rdx => 0x2000 | .rcx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 0⟩]
  wr := [⟨0x2000, D⟩, ⟨0x3000, Impl.MdStream.X86_64.OneShot.scratchBytes (PoS so o)⟩]

theorem sat_preS {so : Nat} (h : so = 0 ∨ so = 112) (o : List Instr) {D : Nat} (hD : D ≤ 64) :
    OneShot.Pre (PoS so o) D (satS so o D) := by
  have e := scratchBytesS_eq h o
  have hw : wordsS so ≤ 32 := by rcases h with rfl | rfl <;> decide
  have d : ∀ {a b : Addr} {n m : Nat}, a.toNat + n ≤ b.toNat → b.toNat + m ≤ 2 ^ 64 →
      Region.Disjoint ⟨a, n⟩ ⟨b, m⟩ := fun h h' => Offset.disjoint_of_le h h'
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [OneShot.dR, OneShot.oR, OneShot.wR, OneShot.retR, OneShot.stkR, OneShot.dp, OneShot.len,
    OneShot.out, OneShot.sb, satS, e, VG.X86_64.below]
  · exact d (by decide) (by simp; omega_using [hD])
  · exact d (by decide) (by simp; omega_using [hw])
  · exact d (by simp; omega_using [hD]) (by simp; omega_using [hw])
  · exact (d (by simp; omega_using [hD]) (by decide)).symm
  · exact (d (by simp; omega_using [hw]) (by decide)).symm
  · exact (d (by decide) (by decide)).symm
  · exact (d (by simp; omega_using [hD]) (by decide)).symm
  · exact (d (by simp; omega_using [hw]) (by decide)).symm

/-- `vg_<alg>_digest`'s signature with its scratch buffer of `w` words as its
last argument. -/
def digestScratchSigW (w D : Nat) : Sig where
  params := [("data", .slice false .u8 "len"), ("out", .array true .u8 D), ("scratch", .array true .u64 w)]

/-- `Spec.Sha256.digestPost`, whatever `scratch` is. -/
def digestScratchContractW (w : Nat) (A : Abi isa) (D : Nat) (digest : List Byte → List Byte) (stack : Nat) :
    Contract isa :=
  (digestScratchSigW w D).contract A (post := fun data len out _scratch =>
    Spec.Sha256.digestPost D digest A.ptrBits data len out) (stack := stack)

theorem impliesS {so : Nat} (h : so = 0 ∨ so = 112) (o : List Instr) {iv : Spec.Sha256.HashValue} {D : Nat}
    {digest : List Byte → List Byte} (hD : D ≤ 64) (hdg : ∀ m, (md.hash iv m).take D = digest m) :
    (OneShot.oneK (P := PoS so o) md iv D).Implies (digestScratchContractW (wordsS so) X86_64.abi D digest 8) := by
  have e : Impl.MdStream.X86_64.OneShot.scratchBytes (PoS so o) = wordsS so * 8 := by
    rw [scratchBytesS_eq h, Nat.mul_comm]
  have hw : wordsS so ≤ 32 := by rcases h with rfl | rfl <;> decide
  refine
    { pre := fun s h => ?_
      post := fun s s' _ h => ?_
      pub := by implies_pub [digestScratchContractW, digestScratchSigW, Spec.Sha256.digestPost,
        OneShot.oneK, X86_64.abi, X86_64.argRegs]
      sat := ⟨satS so o D, ?_⟩ }
  · sig_pre [digestScratchContractW, digestScratchSigW, Spec.Sha256.digestPost, X86_64.abi, X86_64.argRegs] at h
    obtain ⟨-, hrd, hwr, hdo, hdw, how, -, hro, hrw, hsd, hso, hsw, -⟩ := h
    refine ⟨hrd, ?_, hdo, ?_, ?_, hro, ?_, hsd, hso, ?_⟩ <;> simp only [OneShot.wR, OneShot.sb, e]
    exacts [hwr, hdw, how, hrw, hsw]
  · sig_post [digestScratchContractW, digestScratchSigW, Spec.Sha256.digestPost, X86_64.abi, X86_64.argRegs]
    rw [← hdg]
    exact h trivial
  · have hp := sat_preS h o hD
    sig_pre [digestScratchContractW, digestScratchSigW, Spec.Sha256.digestPost, X86_64.abi, X86_64.argRegs]
    have d₁ := hp.d_o; have d₂ := hp.d_w; have d₃ := hp.o_w; have d₄ := hp.ret_o; have d₅ := hp.ret_w
    have d₆ := hp.stk_d; have d₇ := hp.stk_o; have d₈ := hp.stk_w
    simp only [OneShot.dR, OneShot.oR, OneShot.wR, OneShot.retR, OneShot.stkR, OneShot.dp, OneShot.len,
      OneShot.out, OneShot.sb, satS, e, VG.X86_64.below] at d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈
    refine ⟨by first | decide | (simp; omega), rfl, by rw [e], d₁, d₂, d₃, (Offset.disjoint_of_le (by decide) (by decide)).symm,
      d₄, d₅, d₆, d₇, d₈, by first | decide | (simp; omega), by simp; omega_using [hD], by first | decide | (simp; omega_using [hw])⟩

/-- What the generic proofs need of a member's one-shot digest made with `so`
bytes for the compression function (`Member`). -/
structure MemberS (so : Nat) (o : List Instr) (D : Nat) : Prop where
  shape : ShapeD (P := PoS so o) md D
  taints : OneShot.Taints (PoS so o)
  hso : so = 0 ∨ so = 112
  hD : D = 32 ∨ D = 28
  mxcsr : ∀ f : Callee, f.code.allInstrs (fun i => !loadsMxcsr i) = true →
    (Impl.MdStream.X86_64.OneShot.body (PoS so o) (.block []) f.name f.code).allInstrs (fun i => !loadsMxcsr i) = true
  spSafe : ∀ f : Callee, f.code.all (fun i => !isa.writesSp i) = true →
    (Impl.MdStream.X86_64.OneShot.body (PoS so o) (.block []) f.name f.code).all (fun i => !isa.writesSp i) = true
  depth : ∀ f : Callee, f.code.x86_64Depth = 0 →
    (Impl.MdStream.X86_64.OneShot.body (PoS so o) (.block []) f.name f.code).x86_64Depth ≤ 8

theorem MemberS.le {so : Nat} {o : List Instr} {D : Nat} (c : MemberS so o D) : D ≤ 64 := by
  rcases c.hD with rfl | rfl <;> decide

/-- The body, against its contract with the scratch buffer. -/
theorem scratch_verifiedS {so : Nat} {o : List Instr} {D : Nat} (c : MemberS so o D) {iv : Spec.Sha256.HashValue}
    (hict : ∃ hc, (taint.check (Taint.ofRegs [.rdi]) (initWith iv) hc).isSome = true)
    {digest : List Byte → List Byte} (hdg : ∀ m, (md.hash iv m).take D = digest m) {f : Callee}
    (hf : f.Ok) (hv : Verified X86_64.target f.code (Proof.Sha256.compressX86_64S so))
    (hm : f.code.allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (bodyS so o iv f) (digestScratchContractW (wordsS so) X86_64.abi D digest 8) :=
  (Proof.MdStream.X86_64.OneShot.verified (fitsS c.hso o) (dimsS c.hso o) c.shape c.taints (init_hi' o iv) (init_writes iv) rfl hict
    ((Stream.calleeS hf hv).withOut o) (by rw [OneShot.body_allInstrs, c.mxcsr f hm, init_mxcsr]; rfl)
    ⟨_, sat_preS c.hso o c.le⟩).of_implies (impliesS c.hso o c.le hdg)
where
  init_hi' (o : List Instr) (iv : Spec.Sha256.HashValue) :
      ∀ s, (OneShot.initK (P := PoS so o) md iv).pre s → ∃ t s', Exec isa (initWith iv) s t s' ∧
        abiPreserved s s' ∧ (OneShot.initK (P := PoS so o) md iv).post s s' := fun s hs => by
    obtain ⟨t, s', he, h⟩ := Stream.init_correct iv hs
    exact ⟨t, s', he, abiPreserved_of_exec (init_mxcsr iv) he h.1, h.2⟩

/-- The one-shot digest made with `so` bytes for the compression function,
with its scratch buffer in a frame of its own. -/
theorem verifiedS {so : Nat} {o : List Instr} {D : Nat} (c : MemberS so o D) {iv : Spec.Sha256.HashValue}
    (hict : ∃ hc, (taint.check (Taint.ofRegs [.rdi]) (initWith iv) hc).isSome = true)
    {dg : List Byte → List Byte} (hdg : ∀ m, (md.hash iv m).take D = dg m) {f : Callee}
    (hf : f.Ok) (hv : Verified X86_64.target f.code (Proof.Sha256.compressX86_64S so))
    (hm : f.code.allInstrs (fun i => !loadsMxcsr i) = true)
    (hs : f.code.all (fun i => !isa.writesSp i) = true) (hd : f.code.x86_64Depth = 0) :
    Verified X86_64.target (digestS so o iv f) (Spec.Sha256.digestContract X86_64.abi D dg (8 + frameS so)) := by
  have h := scratch_verifiedS c hict hdg hf hv hm
  have hsp : (bodyS so o iv f).all (fun i => !isa.writesSp i) = true := by
    rw [OneShot.body_all, c.spSafe f hs, init_sp]; rfl
  have hdp : (bodyS so o iv f).x86_64Depth ≤ 8 := by
    rw [OneShot.body_depth _ (rfl : (initWith iv).x86_64Depth = 0)]; exact c.depth f hd
  show Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch
    (Impl.MdStream.X86_64.OneShot.frameBytes (Stream.paramsS so)) .rcx (bodyS so o iv f)) _
  rcases c.hso with rfl | rfl <;> rcases c.hD with rfl | rfl <;>
  exact X86_64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := wordsS _) (stack := 8) (bytes := _)
    h (by decide) (by decide) (by decide) hsp hdp
    (fun vs m m₁ m₂ r hl hb h => Proof.MdStream.Digest.digestPostOut_local _ _ _ vs m m₁ m₂ r hl hb h)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem spSafeS {so : Nat} {o : List Instr} {D : Nat} (c : MemberS so o D) (iv : Spec.Sha256.HashValue) {f : Callee}
    (hs : f.code.all (fun i => !isa.writesSp i) = true) :
    (digestS so o iv f).all (fun i => !isa.writesSp i) = true :=
  X86_64.withStackScratch_spSafe (by rcases c.hso with rfl | rfl <;> decide)
    (by rw [OneShot.body_all, c.spSafe f hs, init_sp]; rfl)

section
open Impl.MdStream.X86_64 (out32 compressN compressAt compressWith)

theorem code256S {so : Nat} (h : so = 0 ∨ so = 112) : MemberS so (out32 8 true) 32 where
  shape := ⟨code256.shape.le, code256.shape.len, code256.shape.lenV, code256.shape.out⟩
  taints := ⟨by rcases h with rfl | rfl <;> exact ⟨_, by taint_decide⟩, code256.taints.wholeHead,
    code256.taints.wholeEnd, code256.taints.zeroBuf, code256.taints.copyTail, code256.taints.cmpLen,
    code256.taints.blkArg, code256.taints.lenArg, by rcases h with rfl | rfl <;> exact ⟨_, by taint_decide⟩⟩
  hso := h
  hD := .inl rfl
  mxcsr f hm := by
    simp only [Impl.MdStream.X86_64.OneShot.body, Impl.MdStream.X86_64.OneShot.whole, Impl.MdStream.X86_64.OneShot.tail, Impl.MdStream.X86_64.OneShot.copyTail, compressN, compressAt, compressWith, Code.allInstrs, hm,
      Bool.true_and, Bool.and_true]
    rcases h with rfl | rfl <;> decide +kernel
  spSafe f hs := by
    simp only [Impl.MdStream.X86_64.OneShot.body, Impl.MdStream.X86_64.OneShot.whole, Impl.MdStream.X86_64.OneShot.tail, Impl.MdStream.X86_64.OneShot.copyTail, compressN, compressAt, compressWith, Code.all, hs,
      Bool.true_and]
    rcases h with rfl | rfl <;> decide +kernel
  depth f hd := by
    simp only [Impl.MdStream.X86_64.OneShot.body, Impl.MdStream.X86_64.OneShot.whole, Impl.MdStream.X86_64.OneShot.tail, Impl.MdStream.X86_64.OneShot.copyTail, compressN, compressAt, compressWith, Code.x86_64Depth, hd]
    rcases h with rfl | rfl <;> decide +kernel

theorem code224S {so : Nat} (h : so = 0 ∨ so = 112) : MemberS so (out32 7 true) 28 where
  shape := ⟨code224.shape.le, code224.shape.len, code224.shape.lenV, code224.shape.out⟩
  taints := ⟨by rcases h with rfl | rfl <;> exact ⟨_, by taint_decide⟩, code224.taints.wholeHead,
    code224.taints.wholeEnd, code224.taints.zeroBuf, code224.taints.copyTail, code224.taints.cmpLen,
    code224.taints.blkArg, code224.taints.lenArg, by rcases h with rfl | rfl <;> exact ⟨_, by taint_decide⟩⟩
  hso := h
  hD := .inr rfl
  mxcsr f hm := by
    simp only [Impl.MdStream.X86_64.OneShot.body, Impl.MdStream.X86_64.OneShot.whole, Impl.MdStream.X86_64.OneShot.tail, Impl.MdStream.X86_64.OneShot.copyTail, compressN, compressAt, compressWith, Code.allInstrs, hm,
      Bool.true_and, Bool.and_true]
    rcases h with rfl | rfl <;> decide +kernel
  spSafe f hs := by
    simp only [Impl.MdStream.X86_64.OneShot.body, Impl.MdStream.X86_64.OneShot.whole, Impl.MdStream.X86_64.OneShot.tail, Impl.MdStream.X86_64.OneShot.copyTail, compressN, compressAt, compressWith, Code.all, hs,
      Bool.true_and]
    rcases h with rfl | rfl <;> decide +kernel
  depth f hd := by
    simp only [Impl.MdStream.X86_64.OneShot.body, Impl.MdStream.X86_64.OneShot.whole, Impl.MdStream.X86_64.OneShot.tail, Impl.MdStream.X86_64.OneShot.copyTail, compressN, compressAt, compressWith, Code.x86_64Depth, hd]
    rcases h with rfl | rfl <;> decide +kernel

end

end VG.Proof.Sha256.X86_64.OneShot

end

end

/-!
# SHA-256 on x86-64, as a Merkle–Damgård hash function

SHA-256 with an implementation `v` of its compression function
(`Proof/Sha256/X86_64/Variant.lean`), as a variant of `MdHash` (`variant v`),
from which HMAC and PBKDF2 are emitted (`Generic/MdHash/X86_64/`): its streaming
code is the generic Merkle–Damgård code (`Stream.params`), its specification
`Spec.Hmac.sha256S`. The facts about the code HMAC and PBKDF2 add, which depend on `v` only
through the scratch space it uses, are checked once for each (`coreOKS`).

`stream v` are the streaming `update` and `finalize` made with `v`, and the
one-shot `digest` (`Proof/Pbkdf2/Md/X86_64/Hashes/Sha256.lean`), which
`Generic/MdHash/X86_64/Stream.lean` emits from their `Api`s, named with
its suffix.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Md.X86_64.Sha256

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Sha256.X86_64 (Compress)

/-- SHA-256's functions, calling the implementation `v` of the compression
function, named with its suffix, giving it the scratch space it uses
(`Callee.so`) and taking the working space they use (`Hash.wOf`). They call
`vg_sha256_init`'s code as the internal `vg_sha256_init_core`: the function
exported as `vg_sha256_init` also clears what it leaves
(`Proof.Sha256.X86_64.initReg`), which its callers, which clear their own,
do not need. -/
def hash (v : Compress) : Hash where
  P := Proof.Sha256.X86_64.Stream.paramsS v.callee.so
  D := 32
  W := Hash.wOf (Proof.Sha256.X86_64.Stream.paramsS v.callee.so)
  compN := v.callee.name
  compC := v.callee.code
  initN := "vg_sha256_init_core"
  initC := Impl.Sha256.X86_64.Stream.init
  updN := "vg_sha256_update_scratch" ++ v.suffix
  finN := "vg_sha256_finalize_scratch" ++ v.suffix
  hmacInitN := "vg_hmac_sha256_init_scratch" ++ v.suffix
  hmacFinN := "vg_hmac_sha256_finalize_scratch" ++ v.suffix
  iterN := "vg_pbkdf2_hmac_sha256_iterate" ++ v.suffix

/-- `hash v` without the functions it calls, for an implementation that uses
`so` bytes of scratch space. -/
def coreHS (so : Nat) : Hash :=
  ⟨Proof.Sha256.X86_64.Stream.paramsS so, 32, Hash.wOf (Proof.Sha256.X86_64.Stream.paramsS so), "", .block [],
    "", .block [], "", "", "", "", "", Proof.Pbkdf2.Md.X86_64.coreBoth⟩

/-- The scratch space the implementations use. -/
abbrev SoOk (so : Nat) : Prop := so = 0 ∨ so = 112 ∨ so = 560

theorem coreOKS (so : Nat) (h : SoOk so) : CoreOK (coreHS so) := by
  rcases h with rfl | rfl | rfl <;>
  refine {
    pbk := ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
      ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
      ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
      ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    iter := ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
      ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    hinit := {
      pro := ⟨?_, ?_⟩
      argI := List.forall_mem_cons.mpr ⟨⟨?_, ?_⟩, List.forall_mem_cons.mpr ⟨⟨?_, ?_⟩, List.forall_mem_nil _⟩⟩
      keys := ⟨?_, ?_⟩
      mid := ⟨?_, ?_⟩
      restore := ⟨?_, ?_⟩ }
    hfin := ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    pbkMx := ?_
    pbkSp := ?_
    hinitMx := ?_
    hinitSp := ?_
    hinitNs := ?_
    hinitD := ?_
    hfinMx := ?_
    hfinSp := ?_
    hfinNs := ?_
    hfinD := ?_
    hinitXD := ?_
    hfinXD := ?_
    pbkXD := ?_
    iterMx := ?_
    iterSp := ?_
    iterNs := ?_
    iterD := ?_
    updMx := ?_
    updNs := ?_
    updD := ?_
    finMx := ?_
    finNs := ?_
    finD := ?_
    fitI := ?_
    fitF := ?_ }
  taint_decide_all

theorem anyOKS (so : Nat) (h : SoOk so) : Any.AnyOK (coreHS so) := by
  rcases h with rfl | rfl | rfl <;> refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  taint_decide_all

variable (v : Compress)

theorem coreOK : CoreOK (core (hash v)) := coreOKS v.callee.so v.hso

theorem anyOK : Any.AnyOK (core (hash v)) := anyOKS v.callee.so v.hso

theorem callees : Callees (hash v) :=
  .ofTwice rfl
    (cMx := v.mxcsr)
    (cSp := allInstrs_of_all v.spSafe)
    (cNs := by
      show v.callee.code.allInstrs _ = true
      rw [Code.allInstrs_eq]; exact List.all_eq_true.mpr fun i hi => by simp [v.ok.nosp i hi])
    (cD := v.ok.depth)
    (iMx := by simp only [hash] <;> decide +kernel)
    (iSp := by simp only [hash] <;> decide +kernel)
    (iNs := by simp only [hash] <;> decide +kernel)
    (iD := by simp only [hash] <;> decide +kernel)
    (cXD := v.noStack)
    (iXD := by simp only [hash] <;> decide +kernel)

/-- The words of working space of `hash v`'s functions. -/
theorem hashW : (hash v).W = 18 ∨ (hash v).W = 32 ∨ (hash v).W = 88 := by
  rcases v.hso with h | h | h <;> simp only [hash, Hash.wOf, Proof.Sha256.X86_64.Stream.paramsS, h] <;> decide

/-- The words of working space of `hash v`'s HMAC `init` for a key of at
most a block. -/
theorem hashIW : initWords (hash v) = 12 ∨ initWords (hash v) = 26 ∨ initWords (hash v) = 82 := by
  rcases v.hso with h | h | h <;> simp only [initWords_eq, hash, Proof.Sha256.X86_64.Stream.paramsS, h] <;> decide

def ok : HashOK (hash v) where
  md := Proof.Sha256.md
  dims := Proof.Sha256.X86_64.Stream.dimsS _ (by rcases v.hso with h | h | h <;> omega_using [h])
  shape := Proof.Sha256.X86_64.Stream.shapeS _
  taints := Proof.Sha256.X86_64.Stream.taintsS3 _ v.hso
  comp := v.okS
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha256.md, Spec.Sha256.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 32) h (by omega_using [hj])
  lenOk _ _ := trivial
  SH := Spec.Hmac.sha256S
  iv := Spec.Sha256.H0
  repr _ _ _ := Iff.rfl
  hash m := by
    show Spec.Sha256.hash m = _
    rw [Proof.Sha256.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Sha256.md.digest_length _))).symm
  hB := rfl
  hS := rfl
  hD := rfl
  hD0 := by simp only [hash] <;> decide
  hDN := by simp only [hash] <;> decide
  hD4 := by simp only [hash] <;> decide
  hN4 := by simp only [hash] <;> decide
  hDL := by simp only [hash] <;> decide
  hL4 := by simp only [hash] <;> decide
  hNL := by simp only [hash] <;> decide
  hPad := by simp only [hash] <;> decide
  hso := by
    show v.callee.so % 8 = 0 ∧ v.callee.so + 48 ≤ 8 * 256
    rcases v.hso with h | h | h <;> rw [h] <;> decide
  fits := by
    show v.callee.so + 48 + 32 + 64 ≤ 8 * ((v.callee.so + 48 + 32 + 64 + 7) / 8)
    omega_using []
  hW := by rcases hashW v with h | h | h <;> rw [h] <;> decide
  init := Proof.Sha256.X86_64.Stream.init_verified
  initDepth := by simp only [hash] <;> decide +kernel
  initSp := nosp_of (callees v).iNs
  updMx := Callees.updMx (callees v) (coreOK v)
  finMx := Callees.finMx (callees v) (coreOK v)
  updSp := Callees.updSp (callees v) (coreOK v)
  finSp := Callees.finSp (callees v) (coreOK v)
  updDepth := Callees.updD (callees v) (coreOK v)
  finDepth := Callees.finD (callees v) (coreOK v)

/-- `hash v` made with the working space of the slowest implementation,
AVX2's (`MdHash.okU`). -/
def okU : HashOK ((hash v).withWs 560 (Hash.wOf { (hash v).P with so := 560 })) :=
  (ok v).withWs 560 _ (by decide) Proof.Sha256.X86_64.Stream.taints (Proof.Sha256.X86_64.Stream.callee v.ok)
    (by show 560 + 48 + 32 + 64 ≤ 8 * ((560 + 48 + 32 + 64 + 7) / 8); decide)
    (by show (560 + 48 + 32 + 64 + 7) / 8 ≤ 256; decide) rfl (callees v) (coreOKS 560 (.inr (.inr rfl)))

/-! ### The shared contracts are satisfiable

With each implementation's working space (`hashW`, `hashIW`). -/

variable {w : Nat}

theorem satI (hw : w = 18 ∨ w = 32 ∨ w = 88) :
    ∃ s, (Proof.Hmac.initScratchContract Spec.Hmac.sha256I.S w X86_64.abi 16).pre s := by
  refine ⟨initSat 96 w, ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.sha256I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, Spec.Hmac.sha256S, Spec.Hmac.sha256, X86_64.abi, X86_64.argRegs]
    | (sig_pre [Spec.Hmac.sha256I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, Spec.Hmac.sha256S, Spec.Hmac.sha256, X86_64.abi, X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem satW (hw : w = 12 ∨ w = 26 ∨ w = 82) :
    ∃ s, (Proof.Hmac.initScratchContract Spec.Hmac.sha256I.S w X86_64.abi 16).pre s := by
  refine ⟨initSat 96 w, ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.sha256I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, Spec.Hmac.sha256S, Spec.Hmac.sha256, X86_64.abi, X86_64.argRegs]
    | (sig_pre [Spec.Hmac.sha256I, Proof.Hmac.initScratchContract, Proof.Hmac.initScratchSig, Spec.Hmac.initPre,
      Spec.Hmac.initPost, Spec.Hmac.sha256S, Spec.Hmac.sha256, X86_64.abi, X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem satF (hw : w = 18 ∨ w = 32 ∨ w = 88) :
    ∃ s, (Proof.Hmac.finalizeScratchContract Spec.Hmac.sha256I.S w X86_64.abi 16).pre s := by
  refine ⟨finSat 96 32 w, ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.sha256I, Proof.Hmac.finalizeScratchContract, Proof.Hmac.finalizeScratchSig,
    Spec.Hmac.finalizePost, Spec.Hmac.sha256S, Spec.Hmac.sha256, X86_64.abi, X86_64.argRegs]
    | (sig_pre [Spec.Hmac.sha256I, Proof.Hmac.finalizeScratchContract, Proof.Hmac.finalizeScratchSig,
    Spec.Hmac.finalizePost, Spec.Hmac.sha256S, Spec.Hmac.sha256, X86_64.abi, X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem satT (hw : w = 18 ∨ w = 32 ∨ w = 88) :
    ∃ s, (Proof.Pbkdf2.iterateContract Spec.Hmac.sha256I.S w X86_64.abi 8).pre s := by
  refine ⟨Pbkdf2.X86_64.iterSat 96 32 w, ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.sha256I, Proof.Pbkdf2.iterateContract, Proof.Pbkdf2.iterateSig, Spec.Hmac.sha256S,
    Spec.Hmac.sha256, X86_64.abi, X86_64.argRegs]
    | (sig_pre [Spec.Hmac.sha256I, Proof.Pbkdf2.iterateContract, Proof.Pbkdf2.iterateSig, Spec.Hmac.sha256S,
    Spec.Hmac.sha256, X86_64.abi, X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem satA (hw : w = 18 ∨ w = 32 ∨ w = 88) :
    ∃ s, (Any.anyScratchContract Spec.Hmac.sha256I.S (w + 96)).pre s := by
  refine ⟨initSat 96 (w + 96), ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Any.anyScratchContract, Spec.Hmac.sha256I, Proof.Hmac.initScratchSig, Spec.Hmac.initPost,
    Spec.Hmac.sha256S, Spec.Hmac.sha256, X86_64.abi, X86_64.argRegs]
    | (sig_pre [Any.anyScratchContract, Spec.Hmac.sha256I, Proof.Hmac.initScratchSig, Spec.Hmac.initPost,
    Spec.Hmac.sha256S, Spec.Hmac.sha256, X86_64.abi, X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem satP (hw : w = 18 ∨ w = 32 ∨ w = 88) :
    ∃ s, (Proof.Pbkdf2.pbkdf2ScratchContract Spec.Hmac.sha256I.S (w + 96) X86_64.abi 24).pre s := by
  refine ⟨pbkSat (w + 96), ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.sha256I, Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig,
    Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha256S, Spec.Hmac.sha256, X86_64.abi,
    X86_64.argRegs]
    | (sig_pre [Spec.Hmac.sha256I, Proof.Pbkdf2.pbkdf2ScratchContract, Proof.Pbkdf2.pbkdf2ScratchSig,
    Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post, Spec.Hmac.sha256S, Spec.Hmac.sha256, X86_64.abi,
    X86_64.argRegs]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem satPF (hw : w = 18 ∨ w = 32 ∨ w = 88) :
    ∃ s, (Spec.Hmac.sha256I.pbkdf2Contract X86_64.abi (24 + (24 + 8 * (w + 96)))).pre s := by
  refine ⟨pbkFrameSat, ?_⟩
  rcases hw with rfl | rfl | rfl <;>
  first
    | sig_sat_check [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.sha256I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post,
    Spec.Hmac.sha256S, Spec.Hmac.sha256, X86_64.abi, X86_64.argRegs, pbkFrameSat, pbkSat]
    | (sig_pre [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.sha256I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Pbkdf2.pbkdf2Pre, Spec.Pbkdf2.pbkdf2Post,
    Spec.Hmac.sha256S, Spec.Hmac.sha256, X86_64.abi, X86_64.argRegs, pbkFrameSat, pbkSat]
       sig_and_intros
       all_goals first
         | exact Region.disjoint_of_sep (by decide)
         | decide
         | rfl)

theorem satIF (hw : w = 12 ∨ w = 26 ∨ w = 82) :
    ∃ s, (Spec.Hmac.sha256I.initContract X86_64.abi (16 + (8 + 8 * w))).pre s := by
  unfold Spec.Hmac.Instance.initContract Spec.Hmac.initContract
  rcases hw with rfl | rfl | rfl <;>
  exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (Nat.le_of_ble_eq_true rfl)

theorem satAF (hw : w = 18 ∨ w = 32 ∨ w = 88) :
    ∃ s, (Spec.Hmac.sha256I.initAnyKeyContract X86_64.abi (24 + (8 + 8 * (w + 96)))).pre s := by
  unfold Spec.Hmac.Instance.initAnyKeyContract Spec.Hmac.initAnyKeyContract
  rcases hw with rfl | rfl | rfl <;>
  exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial)

theorem satFF (hw : w = 18 ∨ w = 32 ∨ w = 88) :
    ∃ s, (Spec.Hmac.sha256I.finalizeContract X86_64.abi (16 + (8 + 8 * w))).pre s := by
  unfold Spec.Hmac.Instance.finalizeContract Spec.Hmac.finalizeContract
  rcases hw with rfl | rfl | rfl <;>
  exact X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial)

/-- The streaming `update` made with `v`, which keeps its working space in a
frame of its own. -/
def updFn : StreamFn :=
  { api := Spec.Sha256.updateApi
    code := Impl.StackScratch.X86_64.withStackScratch 616 .r8 (Impl.Sha256.X86_64.Stream.update v.callee)
    contract := Spec.Sha256.updateContract X86_64.abi (8 + 616)
    stack := 8 + 616
    verified := Proof.Sha256.X86_64.Shared.update v.ok v.mxcsr v.spSafe v.noStack
    spSafe := X86_64.withStackScratch_spSafe (by decide)
      (Proof.Sha256.X86_64.Shared.update_spSafe v.spSafe) }

/-- The streaming `finalize` made with `v`, likewise. -/
def finFn : StreamFn :=
  { api := Spec.Sha256.finalizeApi
    code := Impl.StackScratch.X86_64.withStackScratch 616 .rcx (Impl.Sha256.X86_64.Stream.finalize v.callee)
    contract := Spec.Sha256.finalizeContract X86_64.abi (8 + 616)
    stack := 8 + 616
    verified := Proof.Sha256.X86_64.Shared.finalize v.ok v.mxcsr v.spSafe v.noStack
    spSafe := X86_64.withStackScratch_spSafe (by decide)
      (Proof.Sha256.X86_64.Shared.finalize_spSafe v.spSafe) }

/-- The one-shot `digest` made with `v`. -/
def digFn : StreamFn :=
  { api := Spec.Sha256.digest256Api
    code := Proof.Sha256.X86_64.OneShot.digest (Impl.MdStream.X86_64.out32 8 true) Spec.Sha256.H0 v.callee
    contract := Spec.Sha256.digestContract X86_64.abi 32 Spec.Sha256.hash (8 + Proof.Sha256.X86_64.OneShot.frame)
    stack := 8 + Proof.Sha256.X86_64.OneShot.frame
    verified := Proof.Sha256.X86_64.OneShot.verified Proof.Sha256.X86_64.OneShot.code256
      Proof.Sha256.X86_64.OneShot.init_check256 Proof.Sha256.X86_64.OneShot.hash_take v.ok v.mxcsr v.spSafe
      v.noStack
    spSafe := Proof.Sha256.X86_64.OneShot.spSafe Proof.Sha256.X86_64.OneShot.code256 Spec.Sha256.H0 v.spSafe }

/-- The streaming `update` and `finalize` made with `v`, and the one-shot
`digest`. -/
def stream : List StreamFn := [updFn v, finFn v, digFn v]

/-! ### With the working space the compression function uses

The same functions made for an implementation `v` of the compression
function verified with `so` bytes of scratch space (`hv`), which give it
only that much (`Stream.paramsS`): their frames shrink with it. -/

section S

variable {so : Nat} (h : so = 0 ∨ so = 112)
  (hv : Verified X86_64.target v.callee.code (Proof.Sha256.compressX86_64S so))

/-- The streaming `update` made with `v`, in a frame of `so + 56` bytes. -/
def updFnS : StreamFn :=
  { api := Spec.Sha256.updateApi
    code := Impl.StackScratch.X86_64.withStackScratch (so + 56) .r8
      (Impl.MdStream.X86_64.update (Proof.Sha256.X86_64.Stream.paramsS so) v.callee.name v.callee.code)
    contract := Spec.Sha256.updateContract X86_64.abi (8 + (so + 56))
    stack := 8 + (so + 56)
    verified := Proof.Sha256.X86_64.Shared.updateS h v.ok hv v.mxcsr v.spSafe v.noStack
    spSafe := X86_64.withStackScratch_spSafe (by rcases h with rfl | rfl <;> decide)
      (Proof.Sha256.X86_64.Shared.updateS_spSafe h v.spSafe) }

/-- The streaming `finalize` made with `v`, likewise. -/
def finFnS : StreamFn :=
  { api := Spec.Sha256.finalizeApi
    code := Impl.StackScratch.X86_64.withStackScratch (so + 56) .rcx
      (Impl.MdStream.X86_64.finalize (Proof.Sha256.X86_64.Stream.paramsS so) v.callee.name v.callee.code)
    contract := Spec.Sha256.finalizeContract X86_64.abi (8 + (so + 56))
    stack := 8 + (so + 56)
    verified := Proof.Sha256.X86_64.Shared.finalizeS h v.ok hv v.mxcsr v.spSafe v.noStack
    spSafe := X86_64.withStackScratch_spSafe (by rcases h with rfl | rfl <;> decide)
      (Proof.Sha256.X86_64.Shared.finalizeS_spSafe h v.spSafe) }

/-- The one-shot `digest` made with `v`, in a frame holding a buffer of
`Proof.Sha256.X86_64.OneShot.wordsS so` words. -/
def digFnS : StreamFn :=
  { api := Spec.Sha256.digest256Api
    code := Proof.Sha256.X86_64.OneShot.digestS so (Impl.MdStream.X86_64.out32 8 true) Spec.Sha256.H0 v.callee
    contract := Spec.Sha256.digestContract X86_64.abi 32 Spec.Sha256.hash (8 + Proof.Sha256.X86_64.OneShot.frameS so)
    stack := 8 + Proof.Sha256.X86_64.OneShot.frameS so
    verified := Proof.Sha256.X86_64.OneShot.verifiedS (Proof.Sha256.X86_64.OneShot.code256S h)
      Proof.Sha256.X86_64.OneShot.init_check256 Proof.Sha256.X86_64.OneShot.hash_take v.ok hv v.mxcsr v.spSafe
      v.noStack
    spSafe := Proof.Sha256.X86_64.OneShot.spSafeS (Proof.Sha256.X86_64.OneShot.code256S h) Spec.Sha256.H0
      v.spSafe }

/-- `stream`, made for `so` bytes of scratch space. -/
def streamS : List StreamFn := [updFnS v h hv, finFnS v h hv, digFnS v h hv]

end S

/-- SHA-256 with the implementation `v` of its compression function. -/
def variant (stream : List StreamFnS := []) : MdHash :=
  MdHash.of (I := Spec.Hmac.sha256I) (ok v) (coreOK v) (callees v)
    ⟨Spec.Mgf1.sha256, by simp [mdHashes], fun _ => rfl, rfl⟩ rfl 560 (okU v) rfl
    (satI (hashW v)) (satF (hashW v)) (satT (hashW v)) (satP (hashW v))
    (by rcases hashW v with h | h | h <;> omega_using [h])
    (anyOK v) (satA (hashW v)) (by show (hash v).W + 96 < 511; rcases hashW v with h | h | h <;> omega_using [h])
    Proof.Hmac.sha256_local (satAF (hashW v)) (satW (hashIW v)) (satIF (hashIW v))
    (by decide) (satFF (hashW v))
    (by show (hash v).W + 96 < 509; rcases hashW v with h | h | h <;> omega_using [h]) (satPF (hashW v))
    v.suffix v.features stream

end VG.Proof.Pbkdf2.Md.X86_64.Sha256

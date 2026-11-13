module

public import VerifiedGarbage.Proof.MdStream.X86_64.OneShotCT
public import VerifiedGarbage.Spec.Sha512.Contract
public import VerifiedGarbage.Proof.Sha512.Md
public import VerifiedGarbage.Impl.Sha512.X86_64.Stream
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha512.X86_64.Stream.Init
public import VerifiedGarbage.Proof.Sha512.X86_64.Stream.Digest
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MdStream.X86_64.OneShotCT
meta import VerifiedGarbage.Spec.Sha512.Contract
meta import VerifiedGarbage.Proof.Sha512.Md
meta import VerifiedGarbage.Impl.Sha512.X86_64.Stream
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sha512.X86_64.Stream.Init
meta import VerifiedGarbage.Proof.Sha512.X86_64.Stream.Digest
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# The one-shot SHA-512 family digests on x86-64

`vg_<alg>_digest` is the generic one-shot digest
(`Impl/MdStream/X86_64/OneShot.lean`) for the SHA-512 family's streaming
parameters with the member's digest `o`, its `init` and an implementation
`f` of the compression function. Its body is verified by the generic proofs
(`OneShot.verified`) against `OneShot.oneK`, which implies the contract of
`digest` with a scratch buffer as its last argument (`digestScratchContract`);
in a frame of its own, it is `Spec.Sha512.digestContract`.
-/

@[expose] public section

namespace VG.Proof.Sha512.X86_64.OneShot

open VG.X86_64 VG.Proof.MdStream.X86_64
open VG.Impl.Sha512.X86_64.Stream (Callee params init)
open VG.Spec.Sha256 (bytesAt)

/-- The streaming parameters, with the digest `o`. -/
abbrev Po (o : List Instr) : Impl.MdStream.X86_64.Params := { params with out := o }

/-- The scratch buffer's 8-byte words, and the frame holding it. -/
abbrev words : Nat := 196
abbrev frame : Nat := 1592

theorem scratchBytes_eq (o : List Instr) : Impl.MdStream.X86_64.OneShot.scratchBytes (Po o) = 8 * words :=
  show Impl.MdStream.X86_64.OneShot.scratchBytes params = 8 * words by decide

theorem frameBytes_eq (o : List Instr) : Impl.MdStream.X86_64.OneShot.frameBytes (Po o) = frame :=
  show Impl.MdStream.X86_64.OneShot.frameBytes params = frame by decide

/-- The one-shot digest's body, with `init iv`, given its scratch buffer. -/
abbrev body (o : List Instr) (iv : Spec.Sha512.HashValue) (f : Callee) : Prog isa :=
  Impl.MdStream.X86_64.OneShot.body (Po o) (init iv) f.name f.code

/-- The one-shot digest. -/
abbrev digest (o : List Instr) (iv : Spec.Sha512.HashValue) (f : Callee) : Prog isa :=
  Impl.MdStream.X86_64.OneShot.digest (Po o) (init iv) f.name f.code

theorem fits (o : List Instr) : OneShot.Fits (Po o) :=
  ⟨by rw [scratchBytes_eq]; decide⟩

theorem dims (o : List Instr) : Dims (Po o) :=
  ⟨Stream.dims.B, Stream.dims.N, Stream.dims.L, Stream.dims.so⟩

/-! ## `init` -/

theorem init_hi (o : List Instr) (iv : Spec.Sha512.HashValue) :
    ∀ s, (OneShot.initK (P := Po o) md iv).pre s → ∃ t s', Exec isa (init iv) s t s' ∧ abiPreserved s s' ∧
      (OneShot.initK (P := Po o) md iv).post s s' :=
  (Stream.init_verified iv).1

theorem init_writes (iv : Spec.Sha512.HashValue) :
    ∀ r, r ≠ .rax → ∀ i ∈ instrs (init iv), Taint.clobbers i r = false := by
  intro r hr i hi
  simp only [init, instrs, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hi
  obtain ⟨_, _, rfl | rfl⟩ := hi <;> simp [Taint.clobbers, Taint.dstOf, Ne.symm hr]

theorem init_check (iv : Spec.Sha512.HashValue) :
    ∃ hc, (taint.check (Taint.ofRegs [.rdi]) (init iv) hc).isSome = true :=
  ⟨_, Stream.init_check iv⟩

theorem init_mxcsr (iv : Spec.Sha512.HashValue) : (init iv).allInstrs (fun i => !loadsMxcsr i) = true := by
  rw [Code.allInstrs_eq]
  simp only [init, instrs, List.all_eq_true, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro _ ⟨_, _, rfl | rfl⟩ <;> rfl

theorem init_sp (iv : Spec.Sha512.HashValue) : (init iv).all (fun i => !isa.writesSp i) = true := by
  simp only [init, Code.all, List.all_eq_true, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro _ ⟨_, _, rfl | rfl⟩ <;> rfl

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
  · exact d (by decide) (by simp; omega)
  · exact d (by decide) (by decide)
  · exact d (by simp; omega) (by decide)
  · exact (d (by simp; omega) (by decide)).symm
  · exact (d (by decide) (by decide)).symm
  · exact (d (by decide) (by decide)).symm
  · exact (d (by simp; omega) (by decide)).symm
  · exact (d (by decide) (by decide)).symm

/-! ## The contracts -/

/-- `vg_<alg>_digest`'s signature with its scratch buffer as its last
argument. -/
def digestScratchSig (D : Nat) : Sig where
  params := [("data", .slice false .u8 "len"), ("out", .array true .u8 D), ("scratch", .array true .u64 words)]

/-- `Spec.Sha512.digestPost`, whatever `scratch` is. -/
def digestScratchContract (A : Abi isa) (D : Nat) (digest : List Byte → List Byte) (stack : Nat) : Contract isa :=
  (digestScratchSig D).contract A (post := fun data len out _scratch =>
    Spec.Sha512.digestPost D digest A.ptrBits data len out) (stack := stack)

theorem implies (o : List Instr) {iv : Spec.Sha512.HashValue} {D : Nat} {digest : List Byte → List Byte}
    (hD : D ≤ 64) (hdg : ∀ m, (md.hash iv m).take D = digest m) :
    (OneShot.oneK (P := Po o) md iv D).Implies (digestScratchContract X86_64.abi D digest 8) := by
  refine
    { pre := fun s h => ?_
      post := fun s s' _ h => ?_
      pub := by implies_pub [digestScratchContract, digestScratchSig, Spec.Sha512.digestPost,
        OneShot.oneK, X86_64.abi, X86_64.argRegs]
      sat := ⟨sat o D, ?_⟩ }
  · sig_pre [digestScratchContract, digestScratchSig, Spec.Sha512.digestPost, X86_64.abi, X86_64.argRegs] at h
    obtain ⟨-, hrd, hwr, hdo, hdw, how, -, hro, hrw, hsd, hso, hsw, -⟩ := h
    have e : Impl.MdStream.X86_64.OneShot.scratchBytes (Po o) = words * 8 := by
      rw [scratchBytes_eq, Nat.mul_comm]
    refine ⟨hrd, ?_, hdo, ?_, ?_, hro, ?_, hsd, hso, ?_⟩ <;> simp only [OneShot.wR, OneShot.sb, e]
    exacts [hwr, hdw, how, hrw, hsw]
  · sig_post [digestScratchContract, digestScratchSig, Spec.Sha512.digestPost, X86_64.abi, X86_64.argRegs]
    rw [← hdg]
    exact h (s.gpr .rsi).isLt
  · have hp := sat_pre o hD
    sig_pre [digestScratchContract, digestScratchSig, Spec.Sha512.digestPost, X86_64.abi, X86_64.argRegs]
    have e : Impl.MdStream.X86_64.OneShot.scratchBytes (Po o) = words * 8 := by
      rw [scratchBytes_eq, Nat.mul_comm]
    have d₁ := hp.d_o; have d₂ := hp.d_w; have d₃ := hp.o_w; have d₄ := hp.ret_o; have d₅ := hp.ret_w
    have d₆ := hp.stk_d; have d₇ := hp.stk_o; have d₈ := hp.stk_w
    simp only [OneShot.dR, OneShot.oR, OneShot.wR, OneShot.retR, OneShot.stkR, OneShot.dp, OneShot.len,
      OneShot.out, OneShot.sb, sat, e, VG.X86_64.below] at d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈
    refine ⟨by decide, rfl, by rw [e], d₁, d₂, d₃, (Offset.disjoint_of_le (by decide) (by decide)).symm,
      d₄, d₅, d₆, d₇, d₈, by decide, by simp; omega, by decide⟩

/-! ## Each member's code -/

/-- What the generic proofs need of a member's one-shot digest, whose `o`
writes the first `D` bytes of the final hash value, from one check of each. -/
structure Member (o : List Instr) (D : Nat) : Prop where
  shape : ShapeD (P := Po o) md D
  taints : OneShot.Taints (Po o)
  hD : D = 64 ∨ D = 48 ∨ D = 32 ∨ D = 28
  mxcsr : ∀ f : Callee, f.code.allInstrs (fun i => !loadsMxcsr i) = true →
    (Impl.MdStream.X86_64.OneShot.body (Po o) (.block []) f.name f.code).allInstrs (fun i => !loadsMxcsr i) = true
  spSafe : ∀ f : Callee, f.code.all (fun i => !isa.writesSp i) = true →
    (Impl.MdStream.X86_64.OneShot.body (Po o) (.block []) f.name f.code).all (fun i => !isa.writesSp i) = true
  depth : ∀ f : Callee, f.code.x86_64Depth = 0 →
    (Impl.MdStream.X86_64.OneShot.body (Po o) (.block []) f.name f.code).x86_64Depth ≤ 8

/-- The body, against its contract with the scratch buffer. -/
theorem Member.le {o : List Instr} {D : Nat} (c : Member o D) : D ≤ 64 := by
  rcases c.hD with rfl | rfl | rfl | rfl <;> decide

theorem scratch_verified {o : List Instr} {D : Nat} (c : Member o D) {iv : Spec.Sha512.HashValue}
    {digest : List Byte → List Byte} (hdg : ∀ m, (md.hash iv m).take D = digest m) {f : Callee}
    (hf : CalleeOk (P := params) md f.code) (hm : f.code.allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (body o iv f) (digestScratchContract X86_64.abi D digest 8) :=
  (OneShot.verified (fits o) (dims o) c.shape c.taints (init_hi o iv) (init_writes iv) rfl (init_check iv)
    (hf.withOut o) (by rw [OneShot.body_allInstrs, c.mxcsr f hm, init_mxcsr]; rfl)
    ⟨_, sat_pre o c.le⟩).of_implies (implies o c.le hdg)

/-- The one-shot digest, with its scratch buffer in a frame of its own. -/
theorem verified {o : List Instr} {D : Nat} (c : Member o D) {iv : Spec.Sha512.HashValue}
    {dg : List Byte → List Byte} (hdg : ∀ m, (md.hash iv m).take D = dg m) {f : Callee}
    (hf : CalleeOk (P := params) md f.code) (hm : f.code.allInstrs (fun i => !loadsMxcsr i) = true)
    (hs : f.code.all (fun i => !isa.writesSp i) = true) (hd : f.code.x86_64Depth = 0) :
    Verified X86_64.target (digest o iv f) (Spec.Sha512.digestContract X86_64.abi D dg (8 + frame)) := by
  have h := scratch_verified c hdg hf hm
  have hsp : (body o iv f).all (fun i => !isa.writesSp i) = true := by
    rw [OneShot.body_all, c.spSafe f hs, init_sp]; rfl
  have hdp : (body o iv f).x86_64Depth ≤ 8 := by
    rw [OneShot.body_depth _ (rfl : (init iv).x86_64Depth = 0)]; exact c.depth f hd
  show Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch
    (Impl.MdStream.X86_64.OneShot.frameBytes (Po o)) .rcx (body o iv f)) _
  rw [frameBytes_eq]
  rcases c.hD with rfl | rfl | rfl | rfl <;>
  exact X86_64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := words) (stack := 8) (bytes := frame)
    h (by decide) (by decide) (by decide) hsp hdp
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem spSafe {o : List Instr} {D : Nat} (c : Member o D) (iv : Spec.Sha512.HashValue) {f : Callee}
    (hs : f.code.all (fun i => !isa.writesSp i) = true) :
    (digest o iv f).all (fun i => !isa.writesSp i) = true :=
  X86_64.withStackScratch_spSafe (by decide) (by rw [OneShot.body_all, c.spSafe f hs, init_sp]; rfl)

section
open Impl.MdStream.X86_64 (out64 compressN compressAt compressWith)

theorem code512 : Member (out64 8) 64 where
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

theorem code384 : Member (out64 6) 48 where
  shape := Stream.shape384
  taints := ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩
  hD := .inr (.inl rfl)
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

theorem code512_256 : Member (out64 4) 32 where
  shape := Stream.shape512_256
  taints := ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩
  hD := .inr (.inr (.inl rfl))
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

theorem code512_224 : Member (out64 3 ++ Impl.Sha512.X86_64.Stream.outHi 3) 28 where
  shape := Stream.shape512_224
  taints := ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩
  hD := .inr (.inr (.inr rfl))
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
abbrev wordsS (so : Nat) : Nat := so / 8 + 30
abbrev frameS (so : Nat) : Nat := Impl.MdStream.X86_64.OneShot.frameBytes (Stream.paramsS so)

theorem scratchBytesS_eq {so : Nat} (h : so = 0 ∨ so = 192) (o : List Instr) :
    Impl.MdStream.X86_64.OneShot.scratchBytes (PoS so o) = 8 * wordsS so := by
  show Impl.MdStream.X86_64.OneShot.scratchBytes (Stream.paramsS so) = 8 * wordsS so
  rcases h with rfl | rfl <;> decide

theorem fitsS {so : Nat} (h : so = 0 ∨ so = 192) (o : List Instr) : OneShot.Fits (PoS so o) :=
  ⟨by rw [scratchBytesS_eq h]; rcases h with rfl | rfl <;> decide⟩

theorem dimsS {so : Nat} (h : so = 0 ∨ so = 192) (o : List Instr) : Dims (PoS so o) :=
  ⟨Stream.dims.B, Stream.dims.N, Stream.dims.L, show so ≤ 2048 by omega⟩

/-- The one-shot digest's body, with `init iv`, given its scratch buffer. -/
abbrev bodyS (so : Nat) (o : List Instr) (iv : Spec.Sha512.HashValue) (f : Callee) : Prog isa :=
  Impl.MdStream.X86_64.OneShot.body (PoS so o) (init iv) f.name f.code

/-- The one-shot digest. -/
abbrev digestS (so : Nat) (o : List Instr) (iv : Spec.Sha512.HashValue) (f : Callee) : Prog isa :=
  Impl.MdStream.X86_64.OneShot.digest (PoS so o) (init iv) f.name f.code

theorem init_hiS (so : Nat) (o : List Instr) (iv : Spec.Sha512.HashValue) :
    ∀ s, (OneShot.initK (P := PoS so o) md iv).pre s → ∃ t s', Exec isa (init iv) s t s' ∧ abiPreserved s s' ∧
      (OneShot.initK (P := PoS so o) md iv).post s s' :=
  (Stream.init_verified iv).1

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

theorem sat_preS {so : Nat} (h : so = 0 ∨ so = 192) (o : List Instr) {D : Nat} (hD : D ≤ 64) :
    OneShot.Pre (PoS so o) D (satS so o D) := by
  have e := scratchBytesS_eq h o
  have hw : wordsS so ≤ 60 := by rcases h with rfl | rfl <;> decide
  have d : ∀ {a b : Addr} {n m : Nat}, a.toNat + n ≤ b.toNat → b.toNat + m ≤ 2 ^ 64 →
      Region.Disjoint ⟨a, n⟩ ⟨b, m⟩ := fun h h' => Offset.disjoint_of_le h h'
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [OneShot.dR, OneShot.oR, OneShot.wR, OneShot.retR, OneShot.stkR, OneShot.dp, OneShot.len,
    OneShot.out, OneShot.sb, satS, e, VG.X86_64.below]
  · exact d (by decide) (by simp; omega)
  · exact d (by decide) (by simp; omega)
  · exact d (by simp; omega) (by simp; omega)
  · exact (d (by simp; omega) (by decide)).symm
  · exact (d (by simp; omega) (by decide)).symm
  · exact (d (by decide) (by decide)).symm
  · exact (d (by simp; omega) (by decide)).symm
  · exact (d (by simp; omega) (by decide)).symm

/-- `vg_<alg>_digest`'s signature with its scratch buffer of `w` words as its
last argument. -/
def digestScratchSigW (w D : Nat) : Sig where
  params := [("data", .slice false .u8 "len"), ("out", .array true .u8 D), ("scratch", .array true .u64 w)]

/-- `Spec.Sha512.digestPost`, whatever `scratch` is. -/
def digestScratchContractW (w : Nat) (A : Abi isa) (D : Nat) (digest : List Byte → List Byte) (stack : Nat) :
    Contract isa :=
  (digestScratchSigW w D).contract A (post := fun data len out _scratch =>
    Spec.Sha512.digestPost D digest A.ptrBits data len out) (stack := stack)

theorem impliesS {so : Nat} (h : so = 0 ∨ so = 192) (o : List Instr) {iv : Spec.Sha512.HashValue} {D : Nat}
    {digest : List Byte → List Byte} (hD : D ≤ 64) (hdg : ∀ m, (md.hash iv m).take D = digest m) :
    (OneShot.oneK (P := PoS so o) md iv D).Implies (digestScratchContractW (wordsS so) X86_64.abi D digest 8) := by
  have e : Impl.MdStream.X86_64.OneShot.scratchBytes (PoS so o) = wordsS so * 8 := by
    rw [scratchBytesS_eq h, Nat.mul_comm]
  have hw : wordsS so ≤ 60 := by rcases h with rfl | rfl <;> decide
  refine
    { pre := fun s h => ?_
      post := fun s s' _ h => ?_
      pub := by implies_pub [digestScratchContractW, digestScratchSigW, Spec.Sha512.digestPost,
        OneShot.oneK, X86_64.abi, X86_64.argRegs]
      sat := ⟨satS so o D, ?_⟩ }
  · sig_pre [digestScratchContractW, digestScratchSigW, Spec.Sha512.digestPost, X86_64.abi, X86_64.argRegs] at h
    obtain ⟨-, hrd, hwr, hdo, hdw, how, -, hro, hrw, hsd, hso, hsw, -⟩ := h
    refine ⟨hrd, ?_, hdo, ?_, ?_, hro, ?_, hsd, hso, ?_⟩ <;> simp only [OneShot.wR, OneShot.sb, e]
    exacts [hwr, hdw, how, hrw, hsw]
  · sig_post [digestScratchContractW, digestScratchSigW, Spec.Sha512.digestPost, X86_64.abi, X86_64.argRegs]
    rw [← hdg]
    exact h (s.gpr .rsi).isLt
  · have hp := sat_preS h o hD
    sig_pre [digestScratchContractW, digestScratchSigW, Spec.Sha512.digestPost, X86_64.abi, X86_64.argRegs]
    have d₁ := hp.d_o; have d₂ := hp.d_w; have d₃ := hp.o_w; have d₄ := hp.ret_o; have d₅ := hp.ret_w
    have d₆ := hp.stk_d; have d₇ := hp.stk_o; have d₈ := hp.stk_w
    simp only [OneShot.dR, OneShot.oR, OneShot.wR, OneShot.retR, OneShot.stkR, OneShot.dp, OneShot.len,
      OneShot.out, OneShot.sb, satS, e, VG.X86_64.below] at d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈
    refine ⟨by first | decide | (simp; omega), rfl, by rw [e], d₁, d₂, d₃,
      (Offset.disjoint_of_le (by decide) (by decide)).symm, d₄, d₅, d₆, d₇, d₈,
      by first | decide | (simp; omega), by simp; omega, by first | decide | (simp; omega)⟩

/-- What the generic proofs need of a member's one-shot digest made with `so`
bytes for the compression function (`Member`). -/
structure MemberS (so : Nat) (o : List Instr) (D : Nat) : Prop where
  shape : ShapeD (P := PoS so o) md D
  taints : OneShot.Taints (PoS so o)
  hso : so = 0 ∨ so = 192
  hD : D = 64 ∨ D = 48 ∨ D = 32 ∨ D = 28
  mxcsr : ∀ f : Callee, f.code.allInstrs (fun i => !loadsMxcsr i) = true →
    (Impl.MdStream.X86_64.OneShot.body (PoS so o) (.block []) f.name f.code).allInstrs (fun i => !loadsMxcsr i) = true
  spSafe : ∀ f : Callee, f.code.all (fun i => !isa.writesSp i) = true →
    (Impl.MdStream.X86_64.OneShot.body (PoS so o) (.block []) f.name f.code).all (fun i => !isa.writesSp i) = true
  depth : ∀ f : Callee, f.code.x86_64Depth = 0 →
    (Impl.MdStream.X86_64.OneShot.body (PoS so o) (.block []) f.name f.code).x86_64Depth ≤ 8

theorem MemberS.le {so : Nat} {o : List Instr} {D : Nat} (c : MemberS so o D) : D ≤ 64 := by
  rcases c.hD with rfl | rfl | rfl | rfl <;> decide

/-- The one-shot digest made with `so` bytes for the compression function,
with its scratch buffer in a frame of its own. -/
theorem verifiedS {so : Nat} {o : List Instr} {D : Nat} (c : MemberS so o D) {iv : Spec.Sha512.HashValue}
    {dg : List Byte → List Byte} (hdg : ∀ m, (md.hash iv m).take D = dg m) {f : Callee}
    (hf : CalleeOk (P := params) md f.code) (hv : Verified X86_64.target f.code (Proof.Sha512.compressWideX86_64S so))
    (hm : f.code.allInstrs (fun i => !loadsMxcsr i) = true)
    (hs : f.code.all (fun i => !isa.writesSp i) = true) (hd : f.code.x86_64Depth = 0) :
    Verified X86_64.target (digestS so o iv f) (Spec.Sha512.digestContract X86_64.abi D dg (8 + frameS so)) := by
  have h : Verified X86_64.target (bodyS so o iv f) (digestScratchContractW (wordsS so) X86_64.abi D dg 8) :=
    (Proof.MdStream.X86_64.OneShot.verified (fitsS c.hso o) (dimsS c.hso o) c.shape c.taints (init_hiS so o iv)
      (init_writes iv) rfl (init_check iv) ((Stream.calleeS hf hv).withOut o)
      (by rw [OneShot.body_allInstrs, c.mxcsr f hm, init_mxcsr]; rfl)
      ⟨_, sat_preS c.hso o c.le⟩).of_implies (impliesS c.hso o c.le hdg)
  have hsp : (bodyS so o iv f).all (fun i => !isa.writesSp i) = true := by
    rw [OneShot.body_all, c.spSafe f hs, init_sp]; rfl
  have hdp : (bodyS so o iv f).x86_64Depth ≤ 8 := by
    rw [OneShot.body_depth _ (rfl : (init iv).x86_64Depth = 0)]; exact c.depth f hd
  show Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch
    (Impl.MdStream.X86_64.OneShot.frameBytes (Stream.paramsS so)) .rcx (bodyS so o iv f)) _
  rcases c.hso with rfl | rfl <;> rcases c.hD with rfl | rfl | rfl | rfl <;>
  exact X86_64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := wordsS _) (stack := 8) (bytes := _)
    h (by decide) (by decide) (by decide) hsp hdp
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem spSafeS {so : Nat} {o : List Instr} {D : Nat} (c : MemberS so o D) (iv : Spec.Sha512.HashValue)
    {f : Callee} (hs : f.code.all (fun i => !isa.writesSp i) = true) :
    (digestS so o iv f).all (fun i => !isa.writesSp i) = true :=
  X86_64.withStackScratch_spSafe (by rcases c.hso with rfl | rfl <;> decide)
    (by rw [OneShot.body_all, c.spSafe f hs, init_sp]; rfl)

section
open Impl.MdStream.X86_64 (out64 compressN compressAt compressWith)

theorem code512S {so : Nat} (h : so = 0 ∨ so = 192) : MemberS so (out64 8) 64 where
  shape := ⟨Stream.shape.toD.le, Stream.shape.toD.len, Stream.shape.toD.lenV, Stream.shape.toD.out⟩
  taints := ⟨by rcases h with rfl | rfl <;> exact ⟨_, by taint_decide⟩, code512.taints.wholeHead,
    code512.taints.wholeEnd, code512.taints.zeroBuf, code512.taints.copyTail, code512.taints.cmpLen,
    code512.taints.blkArg, code512.taints.lenArg, by rcases h with rfl | rfl <;> exact ⟨_, by taint_decide⟩⟩
  hso := h
  hD := .inl rfl
  mxcsr f hm := by
    simp only [Impl.MdStream.X86_64.OneShot.body, Impl.MdStream.X86_64.OneShot.whole,
      Impl.MdStream.X86_64.OneShot.tail, Impl.MdStream.X86_64.OneShot.copyTail, compressN, compressAt,
      compressWith, Code.allInstrs, hm, Bool.true_and, Bool.and_true]
    rcases h with rfl | rfl <;> decide +kernel
  spSafe f hs := by
    simp only [Impl.MdStream.X86_64.OneShot.body, Impl.MdStream.X86_64.OneShot.whole,
      Impl.MdStream.X86_64.OneShot.tail, Impl.MdStream.X86_64.OneShot.copyTail, compressN, compressAt,
      compressWith, Code.all, hs, Bool.true_and]
    rcases h with rfl | rfl <;> decide +kernel
  depth f hd := by
    simp only [Impl.MdStream.X86_64.OneShot.body, Impl.MdStream.X86_64.OneShot.whole,
      Impl.MdStream.X86_64.OneShot.tail, Impl.MdStream.X86_64.OneShot.copyTail, compressN, compressAt,
      compressWith, Code.x86_64Depth, hd]
    rcases h with rfl | rfl <;> decide +kernel

theorem code384S {so : Nat} (h : so = 0 ∨ so = 192) : MemberS so (out64 6) 48 where
  shape := ⟨Stream.shape384.le, Stream.shape384.len, Stream.shape384.lenV, Stream.shape384.out⟩
  taints := ⟨by rcases h with rfl | rfl <;> exact ⟨_, by taint_decide⟩, code384.taints.wholeHead,
    code384.taints.wholeEnd, code384.taints.zeroBuf, code384.taints.copyTail, code384.taints.cmpLen,
    code384.taints.blkArg, code384.taints.lenArg, by rcases h with rfl | rfl <;> exact ⟨_, by taint_decide⟩⟩
  hso := h
  hD := .inr (.inl rfl)
  mxcsr f hm := by
    simp only [Impl.MdStream.X86_64.OneShot.body, Impl.MdStream.X86_64.OneShot.whole,
      Impl.MdStream.X86_64.OneShot.tail, Impl.MdStream.X86_64.OneShot.copyTail, compressN, compressAt,
      compressWith, Code.allInstrs, hm, Bool.true_and, Bool.and_true]
    rcases h with rfl | rfl <;> decide +kernel
  spSafe f hs := by
    simp only [Impl.MdStream.X86_64.OneShot.body, Impl.MdStream.X86_64.OneShot.whole,
      Impl.MdStream.X86_64.OneShot.tail, Impl.MdStream.X86_64.OneShot.copyTail, compressN, compressAt,
      compressWith, Code.all, hs, Bool.true_and]
    rcases h with rfl | rfl <;> decide +kernel
  depth f hd := by
    simp only [Impl.MdStream.X86_64.OneShot.body, Impl.MdStream.X86_64.OneShot.whole,
      Impl.MdStream.X86_64.OneShot.tail, Impl.MdStream.X86_64.OneShot.copyTail, compressN, compressAt,
      compressWith, Code.x86_64Depth, hd]
    rcases h with rfl | rfl <;> decide +kernel

theorem code512_256S {so : Nat} (h : so = 0 ∨ so = 192) : MemberS so (out64 4) 32 where
  shape := ⟨Stream.shape512_256.le, Stream.shape512_256.len, Stream.shape512_256.lenV, Stream.shape512_256.out⟩
  taints := ⟨by rcases h with rfl | rfl <;> exact ⟨_, by taint_decide⟩, code512_256.taints.wholeHead,
    code512_256.taints.wholeEnd, code512_256.taints.zeroBuf, code512_256.taints.copyTail, code512_256.taints.cmpLen,
    code512_256.taints.blkArg, code512_256.taints.lenArg, by rcases h with rfl | rfl <;> exact ⟨_, by taint_decide⟩⟩
  hso := h
  hD := .inr (.inr (.inl rfl))
  mxcsr f hm := by
    simp only [Impl.MdStream.X86_64.OneShot.body, Impl.MdStream.X86_64.OneShot.whole,
      Impl.MdStream.X86_64.OneShot.tail, Impl.MdStream.X86_64.OneShot.copyTail, compressN, compressAt,
      compressWith, Code.allInstrs, hm, Bool.true_and, Bool.and_true]
    rcases h with rfl | rfl <;> decide +kernel
  spSafe f hs := by
    simp only [Impl.MdStream.X86_64.OneShot.body, Impl.MdStream.X86_64.OneShot.whole,
      Impl.MdStream.X86_64.OneShot.tail, Impl.MdStream.X86_64.OneShot.copyTail, compressN, compressAt,
      compressWith, Code.all, hs, Bool.true_and]
    rcases h with rfl | rfl <;> decide +kernel
  depth f hd := by
    simp only [Impl.MdStream.X86_64.OneShot.body, Impl.MdStream.X86_64.OneShot.whole,
      Impl.MdStream.X86_64.OneShot.tail, Impl.MdStream.X86_64.OneShot.copyTail, compressN, compressAt,
      compressWith, Code.x86_64Depth, hd]
    rcases h with rfl | rfl <;> decide +kernel

theorem code512_224S {so : Nat} (h : so = 0 ∨ so = 192) : MemberS so (out64 3 ++ Impl.Sha512.X86_64.Stream.outHi 3) 28 where
  shape := ⟨Stream.shape512_224.le, Stream.shape512_224.len, Stream.shape512_224.lenV, Stream.shape512_224.out⟩
  taints := ⟨by rcases h with rfl | rfl <;> exact ⟨_, by taint_decide⟩, code512_224.taints.wholeHead,
    code512_224.taints.wholeEnd, code512_224.taints.zeroBuf, code512_224.taints.copyTail, code512_224.taints.cmpLen,
    code512_224.taints.blkArg, code512_224.taints.lenArg, by rcases h with rfl | rfl <;> exact ⟨_, by taint_decide⟩⟩
  hso := h
  hD := .inr (.inr (.inr rfl))
  mxcsr f hm := by
    simp only [Impl.MdStream.X86_64.OneShot.body, Impl.MdStream.X86_64.OneShot.whole,
      Impl.MdStream.X86_64.OneShot.tail, Impl.MdStream.X86_64.OneShot.copyTail, compressN, compressAt,
      compressWith, Code.allInstrs, hm, Bool.true_and, Bool.and_true]
    rcases h with rfl | rfl <;> decide +kernel
  spSafe f hs := by
    simp only [Impl.MdStream.X86_64.OneShot.body, Impl.MdStream.X86_64.OneShot.whole,
      Impl.MdStream.X86_64.OneShot.tail, Impl.MdStream.X86_64.OneShot.copyTail, compressN, compressAt,
      compressWith, Code.all, hs, Bool.true_and]
    rcases h with rfl | rfl <;> decide +kernel
  depth f hd := by
    simp only [Impl.MdStream.X86_64.OneShot.body, Impl.MdStream.X86_64.OneShot.whole,
      Impl.MdStream.X86_64.OneShot.tail, Impl.MdStream.X86_64.OneShot.copyTail, compressN, compressAt,
      compressWith, Code.x86_64Depth, hd]
    rcases h with rfl | rfl <;> decide +kernel

end

end VG.Proof.Sha512.X86_64.OneShot

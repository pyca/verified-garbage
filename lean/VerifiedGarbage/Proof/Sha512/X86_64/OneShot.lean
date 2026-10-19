module

public import VerifiedGarbage.Proof.MdStream.X86_64.OneShotCT
public import VerifiedGarbage.Spec.Sha512.Contract
public import VerifiedGarbage.Proof.Sha512.Md
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Sha512.X86_64.Stream
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.MdStream.X86_64.OneShotCT
import VerifiedGarbage.Proof.Sha512.X86_64.Stream.Init
meta import VerifiedGarbage.Proof.Sha512.X86_64.Stream.Init
import VerifiedGarbage.Proof.Sha512.X86_64.Stream.Digest
meta import VerifiedGarbage.Proof.Sha512.X86_64.Stream.Digest
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.MdStream.OneShot
import VerifiedGarbage.Proof.MdStream.X86_64.Words
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Sha512.Word64
import VerifiedGarbage.Proof.Sha512.X86_64.Shared
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Frame
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.MdStream.OneShot
meta import VerifiedGarbage.Proof.MdStream.X86_64.Words
meta import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Sha512.Word64
meta import VerifiedGarbage.Proof.Sha512.X86_64.Shared

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

end VG.Proof.Sha512.X86_64.OneShot

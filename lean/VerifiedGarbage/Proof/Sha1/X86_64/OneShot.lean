module

public import VerifiedGarbage.Proof.MdStream.X86_64.OneShotCT
public import VerifiedGarbage.Spec.Sha1.Contract
public import VerifiedGarbage.Proof.Sha1.Md
public import VerifiedGarbage.Impl.Sha1.X86_64.Stream
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha1.X86_64.Stream.Md
import VerifiedGarbage.Proof.Sha1.X86_64.Stream.Init
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MdStream.X86_64.OneShotCT
meta import VerifiedGarbage.Spec.Sha1.Contract
meta import VerifiedGarbage.Proof.Sha1.Md
meta import VerifiedGarbage.Impl.Sha1.X86_64.Stream
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sha1.X86_64.Stream.Md
meta import VerifiedGarbage.Proof.Sha1.X86_64.Stream.Init
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# The one-shot SHA-1 digest on x86-64

`vg_sha1_digest` is the generic one-shot digest
(`Impl/MdStream/X86_64/OneShot.lean`) for SHA-1's streaming parameters, its
initial hash value's code `init` and an implementation `f` of the compression
function, as SHA-256's is (`Proof/Sha256/X86_64/OneShot.lean`). Its body is
verified by the generic proofs (`OneShot.verified`) against `OneShot.oneK`,
which implies the contract of `digest` with a scratch buffer as its last
argument (`digestScratchContract`); in a frame of its own, it is
`Spec.Sha1.digestContract`.
-/

@[expose] public section

namespace VG.Proof.Sha1.X86_64.OneShot

open VG.X86_64 VG.Proof.MdStream.X86_64
open VG.Impl.Sha1.X86_64.Stream (Callee params init)
open Impl.MdStream.X86_64 (compressN compressAt compressWith)

/-- The scratch buffer's 8-byte words, and the frame holding it. -/
abbrev words : Nat := 32
abbrev frame : Nat := 280

theorem scratchBytes_eq : Impl.MdStream.X86_64.OneShot.scratchBytes params = 8 * words := by decide

theorem frameBytes_eq : Impl.MdStream.X86_64.OneShot.frameBytes params = frame := by decide

/-- The one-shot digest's body, given its scratch buffer. -/
abbrev body (f : Callee) : Prog isa := Impl.MdStream.X86_64.OneShot.body params init f.name f.code

/-- The one-shot digest. -/
abbrev digest (f : Callee) : Prog isa := Impl.MdStream.X86_64.OneShot.digest params init f.name f.code

theorem fits : OneShot.Fits params := ⟨by rw [scratchBytes_eq]; decide⟩

/-! ## The initial hash value's code -/

theorem init_mxcsr : init.allInstrs (fun i => !loadsMxcsr i) = true := by
  rw [Code.allInstrs_eq]
  simp only [init, instrs, List.all_eq_true, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro _ ⟨_, _, rfl | rfl⟩ <;> rfl

theorem init_sp : init.all (fun i => !isa.writesSp i) = true := by
  simp only [init, Code.all, List.all_eq_true, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false]
  rintro _ ⟨_, _, rfl | rfl⟩ <;> rfl

theorem init_writes : ∀ r, r ≠ .rax → ∀ i ∈ instrs init, Taint.clobbers i r = false := by
  intro r hr i hi
  simp only [init, instrs, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hi
  obtain ⟨_, _, rfl | rfl⟩ := hi <;> simp [Taint.clobbers, Taint.dstOf, Ne.symm hr]

theorem init_hi :
    ∀ s, (OneShot.initK (P := params) md Spec.Sha1.H0).pre s → ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧
      (OneShot.initK (P := params) md Spec.Sha1.H0).post s s' := fun s hs => by
  obtain ⟨t, s', he, h⟩ := Stream.init_correct hs
  exact ⟨t, s', he, abiPreserved_of_exec init_mxcsr he h.1, h.2⟩

theorem init_check : ∃ hc, (taint.check (Taint.ofRegs [.rdi]) init hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-! ## The precondition -/

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rdx => 0x2000 | .rcx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 0⟩]
  wr := [⟨0x2000, 20⟩, ⟨0x3000, Impl.MdStream.X86_64.OneShot.scratchBytes params⟩]

theorem sat_pre : OneShot.Pre params 20 sat := by
  have e := scratchBytes_eq
  have d : ∀ {a b : Addr} {n m : Nat}, a.toNat + n ≤ b.toNat → b.toNat + m ≤ 2 ^ 64 →
      Region.Disjoint ⟨a, n⟩ ⟨b, m⟩ := fun h h' => Offset.disjoint_of_le h h'
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [OneShot.dR, OneShot.oR, OneShot.wR, OneShot.retR, OneShot.stkR, OneShot.dp, OneShot.len,
    OneShot.out, OneShot.sb, sat, e, VG.X86_64.below]
  · exact d (by decide) (by simp)
  · exact d (by decide) (by decide)
  · exact d (by simp) (by decide)
  · exact (d (by simp) (by decide)).symm
  · exact (d (by decide) (by decide)).symm
  · exact (d (by decide) (by decide)).symm
  · exact (d (by simp) (by decide)).symm
  · exact (d (by decide) (by decide)).symm

/-! ## The contracts -/

/-- `vg_sha1_digest`'s signature with its scratch buffer as its last
argument. -/
def digestScratchSig : Sig where
  params := [("data", .slice false .u8 "len"), ("out", .array true .u8 20), ("scratch", .array true .u64 words)]

/-- `Spec.Sha1.digestPost`, whatever `scratch` is. -/
def digestScratchContract (A : Abi isa) (stack : Nat) : Contract isa :=
  digestScratchSig.contract A (post := fun data len out _scratch =>
    Spec.Sha1.digestPost A.ptrBits data len out) (stack := stack)

/-- SHA-1's digest is all of the final hash value. -/
theorem hash_take (m : List Byte) : (md.hash Spec.Sha1.H0 m).take 20 = Spec.Sha1.hash m := by
  rw [Proof.Sha1.hash_eq]
  exact List.take_of_length_le (Nat.le_of_eq (Proof.Sha1.md.digest_length _))

theorem implies : (OneShot.oneK (P := params) md Spec.Sha1.H0 20).Implies (digestScratchContract X86_64.abi 8) := by
  refine
    { pre := fun s h => ?_
      post := fun s s' _ h => ?_
      pub := by implies_pub [digestScratchContract, digestScratchSig, Spec.Sha1.digestPost,
        OneShot.oneK, X86_64.abi, X86_64.argRegs]
      sat := ⟨sat, ?_⟩ }
  · sig_pre [digestScratchContract, digestScratchSig, Spec.Sha1.digestPost, X86_64.abi, X86_64.argRegs] at h
    obtain ⟨-, hrd, hwr, hdo, hdw, how, -, hro, hrw, hsd, hso, hsw, -⟩ := h
    have e : Impl.MdStream.X86_64.OneShot.scratchBytes params = words * 8 := by
      rw [scratchBytes_eq, Nat.mul_comm]
    refine ⟨hrd, ?_, hdo, ?_, ?_, hro, ?_, hsd, hso, ?_⟩ <;> simp only [OneShot.wR, OneShot.sb, e]
    exacts [hwr, hdw, how, hrw, hsw]
  · sig_post [digestScratchContract, digestScratchSig, Spec.Sha1.digestPost, X86_64.abi, X86_64.argRegs]
    rw [← hash_take]
    exact h trivial
  · have hp := sat_pre
    sig_pre [digestScratchContract, digestScratchSig, Spec.Sha1.digestPost, X86_64.abi, X86_64.argRegs]
    have e : Impl.MdStream.X86_64.OneShot.scratchBytes params = words * 8 := by
      rw [scratchBytes_eq, Nat.mul_comm]
    have d₁ := hp.d_o; have d₂ := hp.d_w; have d₃ := hp.o_w; have d₄ := hp.ret_o; have d₅ := hp.ret_w
    have d₆ := hp.stk_d; have d₇ := hp.stk_o; have d₈ := hp.stk_w
    simp only [OneShot.dR, OneShot.oR, OneShot.wR, OneShot.retR, OneShot.stkR, OneShot.dp, OneShot.len,
      OneShot.out, OneShot.sb, sat, e, VG.X86_64.below] at d₁ d₂ d₃ d₄ d₅ d₆ d₇ d₈
    refine ⟨by decide, rfl, by rw [e], d₁, d₂, d₃, (Offset.disjoint_of_le (by decide) (by decide)).symm,
      d₄, d₅, d₆, d₇, d₈, by decide, by simp, by decide⟩

/-! ## The code -/

theorem taints : OneShot.Taints params :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem code_mxcsr (f : Callee) (hm : f.code.allInstrs (fun i => !loadsMxcsr i) = true) :
    (Impl.MdStream.X86_64.OneShot.body params (.block []) f.name f.code).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [Impl.MdStream.X86_64.OneShot.body, Impl.MdStream.X86_64.OneShot.whole,
    Impl.MdStream.X86_64.OneShot.tail, Impl.MdStream.X86_64.OneShot.copyTail, compressN, compressAt,
    compressWith, Code.allInstrs, hm, Bool.true_and, Bool.and_true]
  decide +kernel

theorem code_sp (f : Callee) (h : f.code.all (fun i => !isa.writesSp i) = true) :
    (Impl.MdStream.X86_64.OneShot.body params (.block []) f.name f.code).all (fun i => !isa.writesSp i) = true := by
  simp only [Impl.MdStream.X86_64.OneShot.body, Impl.MdStream.X86_64.OneShot.whole,
    Impl.MdStream.X86_64.OneShot.tail, Impl.MdStream.X86_64.OneShot.copyTail, compressN, compressAt,
    compressWith, Code.all, h, Bool.true_and]
  decide +kernel

theorem code_depth (f : Callee) (h : f.code.x86_64Depth = 0) :
    (Impl.MdStream.X86_64.OneShot.body params (.block []) f.name f.code).x86_64Depth ≤ 8 := by
  simp only [Impl.MdStream.X86_64.OneShot.body, Impl.MdStream.X86_64.OneShot.whole,
    Impl.MdStream.X86_64.OneShot.tail, Impl.MdStream.X86_64.OneShot.copyTail, compressN, compressAt,
    compressWith, Code.x86_64Depth, h]
  decide +kernel

/-- The body, against its contract with the scratch buffer. -/
theorem scratch_verified {f : Callee} (hf : CalleeOk (P := params) md f.code)
    (hm : f.code.allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (body f) (digestScratchContract X86_64.abi 8) :=
  (OneShot.verified fits Stream.dims Stream.shape.toD taints init_hi init_writes rfl init_check
    (hf.withOut _) (by rw [OneShot.body_allInstrs, code_mxcsr f hm, init_mxcsr]; rfl)
    ⟨_, sat_pre⟩).of_implies implies

/-- The one-shot digest, with its scratch buffer in a frame of its own. -/
theorem verified {f : Callee} (hf : CalleeOk (P := params) md f.code)
    (hm : f.code.allInstrs (fun i => !loadsMxcsr i) = true)
    (hs : f.code.all (fun i => !isa.writesSp i) = true) (hd : f.code.x86_64Depth = 0) :
    Verified X86_64.target (digest f) (Spec.Sha1.digestContract X86_64.abi (8 + frame)) := by
  have h := scratch_verified hf hm
  have hsp : (body f).all (fun i => !isa.writesSp i) = true := by
    rw [OneShot.body_all, code_sp f hs, init_sp]; rfl
  have hdp : (body f).x86_64Depth ≤ 8 := by
    rw [OneShot.body_depth _ (rfl : init.x86_64Depth = 0)]; exact code_depth f hd
  show Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratch
    (Impl.MdStream.X86_64.OneShot.frameBytes params) .rcx (body f)) _
  rw [frameBytes_eq]
  exact X86_64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := words) (stack := 8) (bytes := frame)
    h (by decide) (by decide) (by decide) hsp hdp
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

theorem spSafe {f : Callee} (hs : f.code.all (fun i => !isa.writesSp i) = true) :
    (digest f).all (fun i => !isa.writesSp i) = true :=
  X86_64.withStackScratch_spSafe (by decide) (by rw [OneShot.body_all, code_sp f hs, init_sp]; rfl)

end VG.Proof.Sha1.X86_64.OneShot

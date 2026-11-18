module

public import VerifiedGarbage.Proof.Sha256.Contract
public import VerifiedGarbage.Proof.Sha256.X86_64.Compress
import VerifiedGarbage.Proof.Sha256.X86_64.ShaNi.Compress
import VerifiedGarbage.Proof.Sha256.X86_64.Avx2.Compress
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Common
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Sha256.Digest
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
import VerifiedGarbage.Proof.MdStream.X86_64.Words
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sha256.X86_64.Compress
meta import VerifiedGarbage.Proof.Sha256.X86_64.ShaNi.Compress
meta import VerifiedGarbage.Proof.Sha256.X86_64.Avx2.Compress
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Common
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Sha256.Digest
meta import VerifiedGarbage.Impl.StackScratch.X86_64
meta import VerifiedGarbage.Proof.Framework.X86_64.Depth
meta import VerifiedGarbage.Proof.MdStream.X86_64.Words
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha256.Scratch
public import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Md
import VerifiedGarbage.Proof.MdStream.Prefix
meta import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Md
meta import VerifiedGarbage.Proof.MdStream.Prefix

/-! ### `Sha256.X86_64.Stream.Digest`, which this module and modules that import it used -/

section

/-!
# Streaming SHA-224 on x86-64: `finalize224`

`finalize224` is the generic `finalize` (`Impl/MdStream/X86_64.lean`) with a
digest of the first 28 bytes of the final hash value (`params224`), so it is
verified by the generic proof of a `finalize` writing a prefix of the final
hash value (`Finalize.verifiedD`), for any implementation of the compression
function, given what writing that prefix does (`ShapeD`).
-/

@[expose] public section

namespace VG.Proof.Sha256.X86_64.Stream

open VG VG.X86_64 VG.Proof.MdStream VG.Proof.MdStream.X86_64
open VG.Impl.MdStream.X86_64 (out32)
open VG.Impl.Sha256.X86_64.Stream (Callee params224 finalize224)

theorem shape224 : ShapeD (P := params224) md 28 where
  le := by decide
  len := shape.len
  lenV := shape.lenV
  out s hin hout hd := by
    refine (out32_ok (n := 7) true (by decide) (inRegions_prefix hin (by decide)) hout
      (hd.sub_left (Region.sub_prefix (by decide)))).mono fun s' ⟨g, rd, wr, m⟩ => ⟨g, rd, wr, ?_⟩
    rw [m, digest_take _ _ (n := 7) (by decide)]

theorem taints224 : Taints params224 :=
  ⟨taints.updStart, taints.updHead, taints.updEnd, taints.finStart, taints.finPad, ⟨_, by taint_decide⟩,
    taints.lenSec, ⟨_, by taint_decide⟩, taints.lenSafe, by decide⟩

/-- `finalize224`'s contract: `finalizeX86_64`, for a state hashed from
SHA-224's initial hash value and its 28-byte digest. -/
def finalize224X86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 96⟩
    let out : Region := ⟨s.gpr .rdx, 28⟩
    let scratch : Region := ⟨s.gpr .rcx, 608⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch
  post s s' := ∀ m, Spec.Sha256.ReprFrom Spec.Sha256.H0_224 s.mem (s.gpr .rdi) m → s.gpr .rsi = BitVec.ofNat 64 m.length →
    Spec.Sha256.bytesAt s'.mem (s.gpr .rdx) 28 = Spec.Sha256.sha224 m
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

namespace Finalize

variable {f : Callee} (hf : f.Ok)
include hf

/-- `finalize224` is verified if it never loads MXCSR. -/
theorem verified224_of (hm : (finalize224 f).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (finalize224 f) finalize224X86_64 :=
  have h := MdStream.X86_64.Finalize.verifiedD (P := params224) ⟨dims.B, dims.N, dims.L, dims.so⟩
    shape224 taints224 ((callee hf).withOut _) hm
  h.of_implies ⟨fun _ h => h, fun _ _ _ h m hr hc => (h _ m hr trivial hc).trans (sha224_eq m),
    fun _ _ _ _ h => h, h.2.2⟩

omit hf

/-- A state satisfying `finalize224X86_64`'s precondition. -/
abbrev sat224 : State := MdStream.X86_64.Finalize.satD params 28

end Finalize

/-- `params224` with `so` bytes of working space for the compression function
(`paramsS`). -/
abbrev params224S (so : Nat) : Impl.MdStream.X86_64.Params := { paramsS so with out := out32 7 true }

theorem taints224S (so : Nat) (h : so = 0 ∨ so = 112) : Taints (params224S so) :=
  have t := taintsS so h
  ⟨t.updStart, t.updHead, t.updEnd, t.finStart, t.finPad,
    by rcases h with rfl | rfl <;> exact ⟨_, by taint_decide⟩, t.lenSec, taints224.outPub, t.lenSafe,
    taints224.outSafe⟩

theorem shape224S (so : Nat) : ShapeD (P := params224S so) md 28 :=
  ⟨shape224.le, shape224.len, shape224.lenV, shape224.out⟩

/-- `finalize224X86_64` with `n` bytes of scratch space. -/
def finalize224X86_64S (n : Nat) : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 96⟩
    let out : Region := ⟨s.gpr .rdx, 28⟩
    let scratch : Region := ⟨s.gpr .rcx, n⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch
  post s s' := ∀ m, Spec.Sha256.ReprFrom Spec.Sha256.H0_224 s.mem (s.gpr .rdi) m → s.gpr .rsi = BitVec.ofNat 64 m.length →
    Spec.Sha256.bytesAt s'.mem (s.gpr .rdx) 28 = Spec.Sha256.sha224 m
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

namespace Finalize

/-- `finalize224` made with `so` bytes of working space for the compression
function, for an implementation verified with that much (`hv`). -/
theorem verified224S {so : Nat} (h : so = 0 ∨ so = 112) {f : Callee} (hf : f.Ok)
    (hv : Verified X86_64.target f.code (Proof.Sha256.compressX86_64S so))
    (hm : (Impl.MdStream.X86_64.finalize (params224S so) f.name f.code).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (Impl.MdStream.X86_64.finalize (params224S so) f.name f.code)
      (finalize224X86_64S (so + 48)) :=
  have h := MdStream.X86_64.Finalize.verifiedD (P := params224S so)
    ⟨dims.B, dims.N, dims.L, show so ≤ 2048 by omega_using [h]⟩
    (shape224S so) (taints224S so h) ((calleeS hf hv).withOut _) hm
  h.of_implies ⟨fun _ h => h, fun _ _ _ h m hr hc => (h _ m hr trivial hc).trans (sha224_eq m),
    fun _ _ _ _ h => h, h.2.2⟩

end Finalize

end VG.Proof.Sha256.X86_64.Stream

end

end

/-!
# Streaming SHA-256 on x86-64: `init`
-/

@[expose] public section

namespace VG.Proof.Sha256.X86_64.Stream

open VG VG.X86_64 VG.Impl.Sha256.X86_64.Stream
open VG.Impl.Sha256.X86_64 (at_)
open VG.Proof.Sha256.X86_64 (ea_at contains_offset' writeState stateAt_writeState)

/-! ## `init` -/

variable (iv : Spec.Sha256.HashValue)

theorem initWith_eq : initWith iv = .block [
    .movImm64 .rax (iv[1] ++ iv[0]), .xop (.movq .xmm0 .rax), .movImm64 .rax (iv[3] ++ iv[2]),
    .xop (.movq .xmm1 .rax), .xop (.bin .punpcklqdq .xmm0 .xmm1), .movdquStore (at_ .rdi (16 * 0)) .xmm0,
    .movImm64 .rax (iv[5] ++ iv[4]), .xop (.movq .xmm0 .rax), .movImm64 .rax (iv[7] ++ iv[6]),
    .xop (.movq .xmm1 .rax), .xop (.bin .punpcklqdq .xmm0 .xmm1), .movdquStore (at_ .rdi (16 * 1)) .xmm0] := rfl

theorem init_post {s₀ s' : State}
    (hret : Region.Disjoint ⟨s₀.gpr .rsp, 8⟩ ⟨s₀.gpr .rdi, 96⟩) (hg : ∀ r, r ≠ .rax → s'.gpr r = s₀.gpr r)
    (hm : s'.mem = writeState s₀.mem (s₀.gpr .rdi) iv) :
    gprPreserved s₀ s' ∧ (Proof.Sha256.initX86_64 iv).post s₀ s' := by
  have hf : Frame [⟨s₀.gpr .rdi, 96⟩] s₀.mem (writeState s₀.mem (s₀.gpr .rdi) iv) := by
    have c : ∀ k, k < 8 → (⟨s₀.gpr .rdi, 96⟩ : Region).Contains
        (s₀.gpr .rdi + BitVec.ofInt 64 ((4 * k : Nat) : Int)) (32 / 8) :=
      fun k hk => contains_offset' (by omega_using [hk]) (by omega_using [hk])
    simp only [writeState]
    refine (((((((((Frame.refl _ _).writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 1 ?_)).writeW ?_ _
      (c 2 ?_)).writeW ?_ _ (c 3 ?_)).writeW ?_ _ (c 4 ?_)).writeW ?_ _ (c 5 ?_)).writeW ?_ _
      (c 6 ?_)).writeW ?_ _ (c 7 ?_)) <;> simp
  refine ⟨⟨fun r hr => hg r ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [hm]; exact hf.readW (Region.contains_self _ _) (by simpa using hret) (by decide)
  · have h := Stream.reprFrom_nil (stateAt_writeState s₀.mem (s₀.gpr .rdi) iv)
    rw [← hm] at h
    exact h

/-- Two 16-byte stores of `iv` are `writeState`. -/
theorem init_mem (m : Mem) (p : Addr) :
    (m.writeW (p + BitVec.ofInt 64 ((16 * 0 : Nat) : Int))
        (XBinOp.eval .punpcklqdq ((0 : BitVec 64) ++ (iv[1] ++ iv[0])) ((0 : BitVec 64) ++ (iv[3] ++ iv[2])))).writeW
      (p + BitVec.ofInt 64 ((16 * 1 : Nat) : Int))
        (XBinOp.eval .punpcklqdq ((0 : BitVec 64) ++ (iv[5] ++ iv[4])) ((0 : BitVec 64) ++ (iv[7] ++ iv[6]))) =
      writeState m p iv := by
  simp only [punpcklqdq_eq, (MdStream.X86_64.dword_zero_append _ _).1, (MdStream.X86_64.dword_zero_append _ _).2,
    MdStream.X86_64.writeW_ofDwords, writeState, Proof.Sha256.X86_64.ofInt_natCast, MdStream.X86_64.add_ofNat,
    Nat.reduceMul, Nat.reduceAdd]

set_option simprocs false in
theorem init_correct {s₀ : State} (hp : (Proof.Sha256.initX86_64 iv).pre s₀) :
    WP isa (initWith iv) s₀ fun s' => gprPreserved s₀ s' ∧ (Proof.Sha256.initX86_64 iv).post s₀ s' := by
  obtain ⟨hrd, hwr, hret⟩ := hp
  have o : ∀ q, q < 2 → InRegions s₀.wr (s₀.gpr .rdi + BitVec.ofInt 64 ((16 * q : Nat) : Int)) 16 :=
    fun q hq => ⟨⟨s₀.gpr .rdi, 96⟩, by simp [hwr], contains_offset' (by omega_using [hq]) (by omega_using [hq])⟩
  rw [initWith_eq]
  refine MdStream.X86_64.wp_movImm64' (MdStream.X86_64.wp_movqx (MdStream.X86_64.wp_movImm64'
    (MdStream.X86_64.wp_movqx (MdStream.X86_64.wp_xbin ?_))))
  refine MdStream.X86_64.wp_movdquStore (a := s₀.gpr .rdi + BitVec.ofInt 64 ((16 * 0 : Nat) : Int)) rfl
    (o 0 (by decide)) fun s₁ g₁ m₁ rd₁ wr₁ => ?_
  refine MdStream.X86_64.wp_movImm64' (MdStream.X86_64.wp_movqx (MdStream.X86_64.wp_movImm64'
    (MdStream.X86_64.wp_movqx (MdStream.X86_64.wp_xbin ?_))))
  refine MdStream.X86_64.wp_movdquStore (a := s₀.gpr .rdi + BitVec.ofInt 64 ((16 * 1 : Nat) : Int))
    (by simp only [ea_at, RegUpd.gpr_setXmm, RegUpd.gpr_setReg, g₁]; rfl)
    (by simp only [RegUpd.wr_setXmm, RegUpd.wr_setReg, wr₁]; exact o 1 (by decide))
    fun s₂ g₂ m₂ rd₂ wr₂ => WP.block_nil (init_post iv hret (fun r hr => ?_) ?_)
  · simp only [g₂, RegUpd.gpr_setXmm, RegUpd.gpr_setReg, hr, ite_false, g₁]
  · simp only [m₂, RegUpd.mem_setXmm, RegUpd.mem_setReg, m₁, RegUpd.xmm_setXmm_self, RegUpd.xmm_setReg,
      RegUpd.xmm_setXmm_of_ne _ _ (show ¬ XReg.xmm0 = .xmm1 by decide), RegUpd.gpr_setReg, RegUpd.gpr_setXmm,
      ite_true]
    exact init_mem iv s₀.mem (s₀.gpr .rdi)

/-- A state satisfying the precondition. -/
def initSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 96⟩]

/-- `initWith iv` is verified, given the checks that evaluate its code
(which the kernel can only run on a literal `iv`): it never loads MXCSR, and
the taint analysis accepts it. -/
theorem initWith_verified (hm : (initWith iv).allInstrs (fun i => !loadsMxcsr i) = true)
    {hc} (hct : (taint.check (Taint.ofRegs [.rdi]) (initWith iv) hc).isSome = true) :
    Verified X86_64.target (initWith iv) (Proof.Sha256.initX86_64 iv) := by
  refine ⟨fun s hs => ?_, ?_, ⟨initSat, rfl, rfl, ?_⟩⟩
  · obtain ⟨t, s', he, h⟩ := init_correct iv hs
    exact ⟨t, s', he, abiPreserved_of_exec hm he h.1, h.2⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi]) ?_ hct
    intro s₁ s₂ _ _ h
    exact Taint.agree_ofRegs fun r hr => by simp at hr; subst hr; exact h
  · exact Region.Disjoint.symm (Offset.disjoint_of_le (by decide) (by decide))

theorem init_verified : Verified X86_64.target init (Proof.Sha256.initX86_64 Spec.Sha256.H0) :=
  initWith_verified _ (by decide +kernel) (hct := by taint_decide)

theorem init224_verified : Verified X86_64.target init224 (Proof.Sha256.initX86_64 Spec.Sha256.H0_224) :=
  initWith_verified _ (by decide +kernel) (hct := by taint_decide)

end VG.Proof.Sha256.X86_64.Stream

/-!
# Sha256 on X86_64: the shared contracts

The proofs are written against per-target contracts
(`Proof/Sha256/X86_64/Contract.lean`); these theorems move them to the shared
contracts of `Spec/Sha256/Contract.lean`, which the artifacts are emitted with.
`update` and `finalize` hold for any implementation `f` of the compression
function.

`update` and `finalize` keep their working space in a frame of their own:
they are `updateScratch` and `finalizeScratch` (the shared contracts with
the working space as an argument, which HMAC's, PBKDF2's and ECDSA's code
calls) run in a frame that allocates it (`Verified.stackScratch`), for an
`f` that uses no stack.
-/

namespace VG.Proof.Sha256.X86_64.Shared

theorem init :
    Verified X86_64.target Impl.Sha256.X86_64.Stream.init (Spec.Sha256.initContract X86_64.abi) :=
  Proof.Sha256.X86_64.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sha256.initContract, Spec.Sha256.initSig, Proof.Sha256.initX86_64,
      X86_64.abi, X86_64.argRegs]
      [Proof.Sha256.X86_64.Stream.initSat] using Proof.Sha256.X86_64.Stream.initSat)

theorem init224 :
    Verified X86_64.target Impl.Sha256.X86_64.Stream.init224 (Spec.Sha256.init224Contract X86_64.abi) :=
  Proof.Sha256.X86_64.Stream.init224_verified.of_implies (by
    contract_implies [Spec.Sha256.init224Contract, Spec.Sha256.initSig, Proof.Sha256.initX86_64,
      X86_64.abi, X86_64.argRegs]
      [Proof.Sha256.X86_64.Stream.initSat] using Proof.Sha256.X86_64.Stream.initSat)

open VG.Impl.Sha256.X86_64.Stream (Callee) in
/-- `updateScratch`, for any compression function `f` (see `Variant.lean`). -/
theorem updateScratch {f : Callee} (hf : f.Ok)
    (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true) :
    Verified X86_64.target (Impl.Sha256.X86_64.Stream.update f)
      (Proof.Sha256.updateScratchContract X86_64.abi 8) :=
  (Proof.Sha256.X86_64.Stream.Update.verified_of hf (by
    simp only [Impl.Sha256.X86_64.Stream.update, Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody,
      Impl.MdStream.X86_64.updateTail, Impl.MdStream.X86_64.compressN, Impl.MdStream.X86_64.compressWith,
      Code.allInstrs, hm,
      Bool.true_and]
    decide +kernel)).of_implies (by
    contract_implies [Proof.Sha256.updateScratchContract, Proof.Sha256.updateScratchSig, Proof.Sha256.updateX86_64,
      X86_64.abi, X86_64.argRegs]
      [Proof.Sha256.X86_64.Stream.Update.sat,
        MdStream.X86_64.Update.sat, Impl.Sha256.X86_64.Stream.params] using Proof.Sha256.X86_64.Stream.Update.sat)

open VG.Impl.Sha256.X86_64.Stream (Callee) in
theorem update_spSafe {f : Callee} (h : f.code.all (fun i => !X86_64.isa.writesSp i) = true) :
    (Impl.Sha256.X86_64.Stream.update f).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [Impl.Sha256.X86_64.Stream.update, Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody,
    Impl.MdStream.X86_64.updateTail, Impl.MdStream.X86_64.compressN, Impl.MdStream.X86_64.compressWith, Code.all, h,
    Bool.true_and]
  decide +kernel

open VG.Impl.Sha256.X86_64.Stream (Callee) in
/-- `finalizeScratch`, for any compression function `f` (see `Variant.lean`). -/
theorem finalizeScratch {f : Callee} (hf : f.Ok)
    (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true) :
    Verified X86_64.target (Impl.Sha256.X86_64.Stream.finalize f)
      (Proof.Sha256.finalizeScratchContract X86_64.abi 8) :=
  (Proof.Sha256.X86_64.Stream.Finalize.verified_of hf (by
    simp only [Impl.Sha256.X86_64.Stream.finalize, Impl.MdStream.X86_64.finalize,
      Impl.MdStream.X86_64.finalizeBody, Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
      Code.allInstrs, hm, Bool.true_and]
    decide +kernel)).of_implies (by
    contract_implies [Proof.Sha256.finalizeScratchContract, Proof.Sha256.finalizeScratchSig,
      Proof.Sha256.finalizeX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Sha256.X86_64.Stream.Finalize.sat,
        MdStream.X86_64.Finalize.sat, Impl.Sha256.X86_64.Stream.params] using Proof.Sha256.X86_64.Stream.Finalize.sat)

open VG.Impl.Sha256.X86_64.Stream (Callee) in
theorem finalize_spSafe {f : Callee} (h : f.code.all (fun i => !X86_64.isa.writesSp i) = true) :
    (Impl.Sha256.X86_64.Stream.finalize f).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [Impl.Sha256.X86_64.Stream.finalize, Impl.MdStream.X86_64.finalize,
    Impl.MdStream.X86_64.finalizeBody, Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    Code.all, h, Bool.true_and]
  decide +kernel

open VG.Impl.Sha256.X86_64.Stream (Callee) in
theorem update_depth {f : Callee} (h : f.code.x86_64Depth = 0) :
    (Impl.Sha256.X86_64.Stream.update f).x86_64Depth ≤ 8 := by
  simp only [Impl.Sha256.X86_64.Stream.update, Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody,
    Impl.MdStream.X86_64.updateTail, Impl.MdStream.X86_64.compressN, Impl.MdStream.X86_64.compressWith,
    Code.x86_64Depth, h]
  decide +kernel

open VG.Impl.Sha256.X86_64.Stream (Callee) in
theorem finalize_depth {f : Callee} (h : f.code.x86_64Depth = 0) :
    (Impl.Sha256.X86_64.Stream.finalize f).x86_64Depth ≤ 8 := by
  simp only [Impl.Sha256.X86_64.Stream.finalize, Impl.MdStream.X86_64.finalize,
    Impl.MdStream.X86_64.finalizeBody, Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    Code.x86_64Depth, h]
  decide +kernel

open VG.Impl.Sha256.X86_64.Stream (Callee) in
/-- `update`: `updateScratch` with its working space in a frame of its own. -/
theorem update {f : Callee} (hf : f.Ok)
    (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true)
    (hs : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (hd : f.code.x86_64Depth = 0) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 616 .r8 (Impl.Sha256.X86_64.Stream.update f))
      (Spec.Sha256.updateContract X86_64.abi (8 + 616)) :=
  X86_64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 76) (stack := 8) (bytes := 616)
    (updateScratch hf hm) (by decide) (by decide) (by decide) (update_spSafe hs) (update_depth hd)
    (Proof.Sha256.updatePostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

open VG.Impl.Sha256.X86_64.Stream (Callee) in
/-- `finalize`: `finalizeScratch` with its working space in a frame of its own. -/
theorem finalize {f : Callee} (hf : f.Ok)
    (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true)
    (hs : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (hd : f.code.x86_64Depth = 0) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 616 .rcx (Impl.Sha256.X86_64.Stream.finalize f))
      (Spec.Sha256.finalizeContract X86_64.abi (8 + 616)) :=
  X86_64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 76) (stack := 8) (bytes := 616)
    (finalizeScratch hf hm) (by decide) (by decide) (by decide) (finalize_spSafe hs) (finalize_depth hd)
    (Proof.Sha256.finalizePostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-! ## SHA-224's digest

`finalize224` writes SHA-224's digest, the first 28 bytes of the final hash
value: `finalize224Scratch` with its working space in a frame of its own. -/

open VG.Impl.Sha256.X86_64.Stream (Callee finalize224) in
theorem finalize224_mxcsr {f : Callee} (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true) :
    (finalize224 f).allInstrs (fun i => !X86_64.loadsMxcsr i) = true := by
  simp only [finalize224, Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
    Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith, Code.allInstrs, hm, Bool.true_and]
  decide +kernel

open VG.Impl.Sha256.X86_64.Stream (Callee finalize224) in
theorem finalize224_spSafe {f : Callee} (h : f.code.all (fun i => !X86_64.isa.writesSp i) = true) :
    (finalize224 f).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [finalize224, Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
    Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith, Code.all, h, Bool.true_and]
  decide +kernel

open VG.Impl.Sha256.X86_64.Stream (Callee finalize224) in
theorem finalize224_depth {f : Callee} (h : f.code.x86_64Depth = 0) : (finalize224 f).x86_64Depth ≤ 8 := by
  simp only [finalize224, Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
    Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith, Code.x86_64Depth, h]
  decide +kernel

open VG.Impl.Sha256.X86_64.Stream (Callee finalize224) in
/-- `finalize224` with its working space in `scratch`, for any compression
function `f`. -/
theorem finalize224Scratch {f : Callee} (hf : f.Ok)
    (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true) :
    Verified X86_64.target (finalize224 f) (Proof.Sha256.finalize224ScratchContract X86_64.abi 8) :=
  (Proof.Sha256.X86_64.Stream.Finalize.verified224_of hf (finalize224_mxcsr hm)).of_implies (by
    contract_implies [Proof.Sha256.finalize224ScratchContract, Proof.Sha256.finalize224ScratchSig,
      Spec.Sha256.finalize224Post, Proof.Sha256.X86_64.Stream.finalize224X86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Sha256.X86_64.Stream.Finalize.sat224,
        MdStream.X86_64.Finalize.satD, Impl.Sha256.X86_64.Stream.params]
      using Proof.Sha256.X86_64.Stream.Finalize.sat224)

open VG.Impl.Sha256.X86_64.Stream (Callee finalize224) in
/-- `finalize224`: `finalize224Scratch` with its working space in a frame of its own. -/
theorem finalize224Stack {f : Callee} (hf : f.Ok)
    (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true)
    (hs : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (hd : f.code.x86_64Depth = 0) :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch 616 .rcx (finalize224 f))
      (Spec.Sha256.finalize224Contract X86_64.abi (8 + 616)) :=
  X86_64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := 76) (stack := 8) (bytes := 616)
    (finalize224Scratch hf hm) (by decide) (by decide) (by decide) (finalize224_spSafe hs) (finalize224_depth hd)
    (Proof.Sha256.finalize224PostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-! ## With the working space the compression function uses

`update`, `finalize` and `finalize224` made with `so` bytes of working space
for the compression function (`Stream.paramsS`), for an implementation that
uses no more than that (`Proof.Sha256.compressX86_64S so`): in a frame of
`so + 56` bytes, where the code made for every implementation
(`Stream.params`) takes 616. -/

section S

open VG.Impl.Sha256.X86_64.Stream (Callee)
open VG.Proof.Sha256.X86_64.Stream (paramsS params224S)
open Impl.MdStream.X86_64 (updateBody updateTail compressN compressAt compressWith finalizeBody)

variable {so : Nat} (h : so = 0 ∨ so = 112) {f : Callee}
include h

theorem updateS_mxcsr (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true) :
    (Impl.MdStream.X86_64.update (paramsS so) f.name f.code).allInstrs (fun i => !X86_64.loadsMxcsr i) = true := by
  simp only [Impl.MdStream.X86_64.update, updateBody, updateTail, compressN, compressWith, Code.allInstrs, hm, Bool.true_and]
  rcases h with rfl | rfl <;> decide +kernel

theorem updateS_spSafe (hs : f.code.all (fun i => !X86_64.isa.writesSp i) = true) :
    (Impl.MdStream.X86_64.update (paramsS so) f.name f.code).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [Impl.MdStream.X86_64.update, updateBody, updateTail, compressN, compressWith, Code.all, hs, Bool.true_and]
  rcases h with rfl | rfl <;> decide +kernel

theorem updateS_depth (hd : f.code.x86_64Depth = 0) : (Impl.MdStream.X86_64.update (paramsS so) f.name f.code).x86_64Depth ≤ 8 := by
  simp only [Impl.MdStream.X86_64.update, updateBody, updateTail, compressN, compressWith, Code.x86_64Depth, hd]
  rcases h with rfl | rfl <;> decide +kernel

theorem finalizeS_mxcsr (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true) :
    (Impl.MdStream.X86_64.finalize (paramsS so) f.name f.code).allInstrs (fun i => !X86_64.loadsMxcsr i) = true := by
  simp only [Impl.MdStream.X86_64.finalize, finalizeBody, compressAt, compressWith, Code.allInstrs, hm, Bool.true_and]
  rcases h with rfl | rfl <;> decide +kernel

theorem finalizeS_spSafe (hs : f.code.all (fun i => !X86_64.isa.writesSp i) = true) :
    (Impl.MdStream.X86_64.finalize (paramsS so) f.name f.code).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [Impl.MdStream.X86_64.finalize, finalizeBody, compressAt, compressWith, Code.all, hs, Bool.true_and]
  rcases h with rfl | rfl <;> decide +kernel

theorem finalizeS_depth (hd : f.code.x86_64Depth = 0) :
    (Impl.MdStream.X86_64.finalize (paramsS so) f.name f.code).x86_64Depth ≤ 8 := by
  simp only [Impl.MdStream.X86_64.finalize, finalizeBody, compressAt, compressWith, Code.x86_64Depth, hd]
  rcases h with rfl | rfl <;> decide +kernel

theorem finalize224S_mxcsr (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true) :
    (Impl.MdStream.X86_64.finalize (params224S so) f.name f.code).allInstrs (fun i => !X86_64.loadsMxcsr i) = true := by
  simp only [Impl.MdStream.X86_64.finalize, finalizeBody, compressAt, compressWith, Code.allInstrs, hm, Bool.true_and]
  rcases h with rfl | rfl <;> decide +kernel

theorem finalize224S_spSafe (hs : f.code.all (fun i => !X86_64.isa.writesSp i) = true) :
    (Impl.MdStream.X86_64.finalize (params224S so) f.name f.code).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [Impl.MdStream.X86_64.finalize, finalizeBody, compressAt, compressWith, Code.all, hs, Bool.true_and]
  rcases h with rfl | rfl <;> decide +kernel

theorem finalize224S_depth (hd : f.code.x86_64Depth = 0) :
    (Impl.MdStream.X86_64.finalize (params224S so) f.name f.code).x86_64Depth ≤ 8 := by
  simp only [Impl.MdStream.X86_64.finalize, finalizeBody, compressAt, compressWith, Code.x86_64Depth, hd]
  rcases h with rfl | rfl <;> decide +kernel

variable (hf : f.Ok) (hv : Verified X86_64.target f.code (Proof.Sha256.compressX86_64S so))
  (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true)
include hf hv hm

/-- `update` made with `so` bytes for the compression function, against the
shared contract with the `so / 8 + 6` words of working space it uses. -/
theorem updateScratchS :
    Verified X86_64.target (Impl.MdStream.X86_64.update (paramsS so) f.name f.code)
      (Proof.Sha256.updateScratchContractW (so / 8 + 6) X86_64.abi 8) := by
  have v := Proof.Sha256.X86_64.Stream.Update.verifiedS h hf hv (updateS_mxcsr h hm)
  rcases h with rfl | rfl
  · exact v.of_implies (by
      sig_implies [Proof.Sha256.updateScratchContractW, Proof.Sha256.updateScratchSigW,
        Proof.Sha256.updateX86_64S, X86_64.abi, X86_64.argRegs]
        [MdStream.X86_64.Update.sat, Impl.Sha256.X86_64.Stream.params] using MdStream.X86_64.Update.sat (paramsS 0))
  · exact v.of_implies (by
      sig_implies [Proof.Sha256.updateScratchContractW, Proof.Sha256.updateScratchSigW,
        Proof.Sha256.updateX86_64S, X86_64.abi, X86_64.argRegs]
        [MdStream.X86_64.Update.sat, Impl.Sha256.X86_64.Stream.params] using MdStream.X86_64.Update.sat (paramsS 112))

/-- `finalize` made with `so` bytes for the compression function, likewise. -/
theorem finalizeScratchS :
    Verified X86_64.target (Impl.MdStream.X86_64.finalize (paramsS so) f.name f.code)
      (Proof.Sha256.finalizeScratchContractW (so / 8 + 6) X86_64.abi 8) := by
  have v := Proof.Sha256.X86_64.Stream.Finalize.verifiedS h hf hv (finalizeS_mxcsr h hm)
  rcases h with rfl | rfl
  · exact v.of_implies (by
      sig_implies [Proof.Sha256.finalizeScratchContractW, Proof.Sha256.finalizeScratchSigW,
        Proof.Sha256.finalizeX86_64S, X86_64.abi, X86_64.argRegs]
        [MdStream.X86_64.Finalize.sat, Impl.Sha256.X86_64.Stream.params]
        using MdStream.X86_64.Finalize.sat (paramsS 0))
  · exact v.of_implies (by
      sig_implies [Proof.Sha256.finalizeScratchContractW, Proof.Sha256.finalizeScratchSigW,
        Proof.Sha256.finalizeX86_64S, X86_64.abi, X86_64.argRegs]
        [MdStream.X86_64.Finalize.sat, Impl.Sha256.X86_64.Stream.params]
        using MdStream.X86_64.Finalize.sat (paramsS 112))

/-- `finalize224` made with `so` bytes for the compression function, likewise. -/
theorem finalize224ScratchS :
    Verified X86_64.target (Impl.MdStream.X86_64.finalize (params224S so) f.name f.code)
      (Proof.Sha256.finalize224ScratchContractW (so / 8 + 6) X86_64.abi 8) := by
  have v := Proof.Sha256.X86_64.Stream.Finalize.verified224S h hf hv (finalize224S_mxcsr h hm)
  rcases h with rfl | rfl
  · exact v.of_implies (by
      contract_implies [Proof.Sha256.finalize224ScratchContractW, Proof.Sha256.finalize224ScratchSigW,
        Spec.Sha256.finalize224Post, Proof.Sha256.X86_64.Stream.finalize224X86_64S, X86_64.abi, X86_64.argRegs]
        [MdStream.X86_64.Finalize.satD, Impl.Sha256.X86_64.Stream.params]
        using MdStream.X86_64.Finalize.satD (paramsS 0) 28)
  · exact v.of_implies (by
      contract_implies [Proof.Sha256.finalize224ScratchContractW, Proof.Sha256.finalize224ScratchSigW,
        Spec.Sha256.finalize224Post, Proof.Sha256.X86_64.Stream.finalize224X86_64S, X86_64.abi, X86_64.argRegs]
        [MdStream.X86_64.Finalize.satD, Impl.Sha256.X86_64.Stream.params]
        using MdStream.X86_64.Finalize.satD (paramsS 112) 28)

variable (hs : f.code.all (fun i => !X86_64.isa.writesSp i) = true) (hd : f.code.x86_64Depth = 0)
include hs hd

/-- `update` made with `so` bytes for the compression function, with its
working space in a frame of its own. -/
theorem updateS :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch (so + 56) .r8 (Impl.MdStream.X86_64.update (paramsS so) f.name f.code))
      (Spec.Sha256.updateContract X86_64.abi (8 + (so + 56))) := by
  have v := updateScratchS h hf hv hm
  have sp := updateS_spSafe h hs
  have dp := updateS_depth h hd
  rcases h with rfl | rfl <;>
  exact X86_64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := _) (stack := 8) (bytes := _)
    v (by decide) (by decide) (by decide) sp dp
    (Proof.Sha256.updatePostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- `finalize` made with `so` bytes for the compression function, likewise. -/
theorem finalizeS :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch (so + 56) .rcx (Impl.MdStream.X86_64.finalize (paramsS so) f.name f.code))
      (Spec.Sha256.finalizeContract X86_64.abi (8 + (so + 56))) := by
  have v := finalizeScratchS h hf hv hm
  have sp := finalizeS_spSafe h hs
  have dp := finalizeS_depth h hd
  rcases h with rfl | rfl <;>
  exact X86_64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := _) (stack := 8) (bytes := _)
    v (by decide) (by decide) (by decide) sp dp
    (Proof.Sha256.finalizePostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- `finalize224` made with `so` bytes for the compression function, likewise. -/
theorem finalize224S :
    Verified X86_64.target
      (Impl.StackScratch.X86_64.withStackScratch (so + 56) .rcx (Impl.MdStream.X86_64.finalize (params224S so) f.name f.code))
      (Spec.Sha256.finalize224Contract X86_64.abi (8 + (so + 56))) := by
  have v := finalize224ScratchS h hf hv hm
  have sp := finalize224S_spSafe h hs
  have dp := finalize224S_depth h hd
  rcases h with rfl | rfl <;>
  exact X86_64.Verified.stackScratch (nm := "scratch") (e := .u64) (n := _) (stack := 8) (bytes := _)
    v (by decide) (by decide) (by decide) sp dp
    (Proof.Sha256.finalize224PostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end S

end VG.Proof.Sha256.X86_64.Shared

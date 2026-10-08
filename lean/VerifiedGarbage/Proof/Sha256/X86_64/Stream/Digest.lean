import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Md
import VerifiedGarbage.Proof.Sha256.Digest

/-!
# Streaming SHA-224 on x86-64: `finalize224`

`finalize224` is the generic `finalize` (`Impl/MdStream/X86_64.lean`) with a
digest of the first 28 bytes of the final hash value (`params224`), so it is
verified by the generic proof of a `finalize` writing a prefix of the final
hash value (`Finalize.verifiedD`), for any implementation of the compression
function, given what writing that prefix does (`ShapeD`).
-/

namespace VG.Proof.Sha256.X86_64.Stream

open VG VG.X86_64 VG.Proof.MdStream VG.Proof.MdStream.X86_64
open VG.Impl.MdStream.X86_64 (out32)
open VG.Impl.Sha256.X86_64.Stream (Callee params224 finalize224)

theorem shape224 : ShapeD (P := params224) md 28 where
  le := by decide
  len := shape.len
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

end VG.Proof.Sha256.X86_64.Stream

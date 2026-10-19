module

import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignRegions
public import VerifiedGarbage.Proof.Rsa.X86.PrivBytes
public import VerifiedGarbage.Proof.Rsa.X86.PrivWorkspace
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignGeometry
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Rsa.X86.PrivContext
import VerifiedGarbage.Proof.Rsa.X86.PrivObservations

/-! # Immutable sources and incoming arguments survive calls and local frame writes -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Sign VG.Proof.Bignum.X86 VG.Proof.Mont.X86 VG.Proof.Rsa.X86.PrivChecked

/-- Includes the nested callee's frame, but excludes the wrapper's saved registers. -/
def bodyWrites (g : Geometry) : List Region :=
  [g.innerRegion, g.calleeRegion, g.outputRegion, g.workspaceRegion]

structure Context (g : Geometry) (bs : Fin 8 → List Byte) (s : State) : Prop where
  valid : g.Valid
  sp : s.gpr .esp = g.stack
  inner : Workspace s g.stack VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes
  sources : ∀ i, PublicBytes (g.sources i) (g.sourceLength i) (bs i) s
  outputWrite : InRegions s.wr (byteAddr g.output) g.length
  workspaceWrite : InRegions s.wr (byteAddr g.workspace) (8 * g.scratchLength)
  argumentsRead : InRegions (s.rd ++ s.wr) g.argumentsRegion.base 84
  arguments : ∀ j < 21, s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes + 20 + 4 * j)) 32 = g.argument j

theorem Context.sourceSeparate {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : Context g bs s) (i : Fin 8) : ∀ r ∈ bodyWrites g, (g.sourceRegion i).Disjoint r := by
  intro r hr
  simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ((h.valid.stackSources i).sub_left h.valid.innerSub).symm
  · exact ((h.valid.stackSources i).sub_left h.valid.calleeSub).symm
  · exact (h.valid.outputSources i).symm
  · exact h.valid.sourcesWorkspace i

theorem Context.argumentsSeparate {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : Context g bs s) : ∀ r ∈ bodyWrites g, g.argumentsRegion.Disjoint r := by
  intro r hr
  simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (h.valid.stackArguments.sub_left h.valid.innerSub).symm
  · exact (h.valid.stackArguments.sub_left h.valid.calleeSub).symm
  · exact h.valid.outputArguments.symm
  · exact h.valid.workspaceArguments.symm

theorem Context.after {g : Geometry} {bs : Fin 8 → List Byte} {s t : State} {rs : List Reg}
    (h : Context g bs s) (frame : Frame (bodyWrites g) s.mem t.mem) (rest : Keeps rs s t) (sp : t.gpr .esp = s.gpr .esp) : Context g bs t := by
  refine ⟨h.valid, sp.trans h.sp, h.inner.congr rest.2.2,
    fun i => (h.sources i).after_frame frame rest (h.sourceSeparate i),
    by rw [rest.2.2]; exact h.outputWrite, by rw [rest.2.2]; exact h.workspaceWrite,
    by rw [rest.2.1, rest.2.2]; exact h.argumentsRead, ?_⟩
  intro j hj
  have word := frame.readW (r := g.argumentsRegion)
    (Offset.contains_base _ (by omega : 4 * j + 32 / 8 ≤ 84) (by omega : 4 * j < 2 ^ 64))
    h.argumentsSeparate (by decide : 32 / 8 < 2 ^ 64)
  have address : g.argumentsRegion.base + BitVec.ofNat 64 (4 * j) =
      byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes + 20 + 4 * j) :=
    Offset.add_add _ (VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes + 20) (4 * j)
  change t.mem.readW (g.argumentsRegion.base + BitVec.ofNat 64 (4 * j)) 32 =
    s.mem.readW (g.argumentsRegion.base + BitVec.ofNat 64 (4 * j)) 32 at word
  rw [address] at word
  exact word.trans (h.arguments j hj)

end VG.Proof.RsaPkcs1Sig.X86.Sgn

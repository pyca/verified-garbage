module
public import VerifiedGarbage.Proof.Bignum.Arm.PublicBuffers
public import VerifiedGarbage.Proof.Rsa.Arm.PrivGeometry

import VerifiedGarbage.Proof.Rsa.Arm.PrivRegions
import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Immutable sources and incoming arguments survive calls and local frame writes -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

/-- Includes the nested callee's frame, but excludes the wrapper's saved registers. -/
def bodyWrites (g : PrivGeometry) : List Region :=
  [g.innerRegion, g.calleeRegion, g.outputRegion, g.workspaceRegion]

structure PrivContext (g : PrivGeometry) (bs : Fin 8 → List Byte) (s : State) : Prop where
  valid : g.Valid
  sp : s.sp = g.stack
  inner : Workspace s g.stack frameBytes
  sources : ∀ i, PublicBytes (g.sources i) (g.sourceLength i) (bs i) s
  outputWrite : InRegions s.wr (State.addr g.output) g.length
  workspaceWrite : InRegions s.wr (State.addr g.workspace) (8 * g.scratchLength)
  argumentsRead : InRegions (s.rd ++ s.wr) g.argumentsRegion.base 64
  arguments : ∀ j < 16, s.mem.readW (off (State.addr g.stack) (arg j)) 32 = g.argument j

theorem PrivContext.sourceSeparate {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) (i : Fin 8) : ∀ r ∈ bodyWrites g, (g.sourceRegion i).Disjoint r := by
  intro r hr
  simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ((h.valid.stackSources i).sub_left h.valid.innerSub).symm
  · exact ((h.valid.stackSources i).sub_left h.valid.calleeSub).symm
  · exact (h.valid.outputSources i).symm
  · exact h.valid.sourcesWorkspace i

theorem PrivContext.argumentsSeparate {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) : ∀ r ∈ bodyWrites g, g.argumentsRegion.Disjoint r := by
  intro r hr
  simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (h.valid.stackArguments.sub_left h.valid.innerSub).symm
  · exact (h.valid.stackArguments.sub_left h.valid.calleeSub).symm
  · exact h.valid.outputArguments.symm
  · exact h.valid.workspaceArguments.symm

theorem PrivContext.after {g : PrivGeometry} {bs : Fin 8 → List Byte} {s t : State} {rs : List Reg}
    (h : PrivContext g bs s) (frame : Frame (bodyWrites g) s.mem t.mem) (rest : Rest rs s t) : PrivContext g bs t := by
  refine ⟨h.valid, rest.sp.trans h.sp, h.inner.congr rest.wr,
    fun i => (h.sources i).after_frame frame rest (h.sourceSeparate i),
    by rw [rest.wr]; exact h.outputWrite, by rw [rest.wr]; exact h.workspaceWrite,
    by rw [rest.rd, rest.wr]; exact h.argumentsRead, ?_⟩
  intro j hj
  have eq : WorkspaceEq g.argumentsRegion.base 64 s.mem t.mem :=
    WorkspaceEq.of_frame (by decide) frame h.argumentsSeparate
  have word := eq.word (d := 4 * j) (bits := 32) (by omega)
  have address : off g.argumentsRegion.base (4 * j) = off (State.addr g.stack) (arg j) :=
    Offset.add_add _ (frameBytes + 56) (4 * j)
  rw [address] at word
  exact word.trans (h.arguments j hj)
end VG.Proof.Rsa.Arm

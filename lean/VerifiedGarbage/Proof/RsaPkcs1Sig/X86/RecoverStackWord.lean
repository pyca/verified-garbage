module

import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.RecoverRegions
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.X86.PrivWorkspace

/-! ### `RsaPkcs1Sig.X86.RecoverContext`, which this module and modules that import it used -/

section

/-! # Immutable sources and incoming arguments survive calls and local frame writes -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Impl.RsaPkcs1Sig.X86.Verify VG.Proof.Bignum.X86 VG.Proof.Mont.X86 VG.Proof.Rsa.X86.PrivChecked

/-- Includes the nested callee's frame, but excludes the wrapper's saved registers. -/
def bodyWrites (g : Geometry) : List Region :=
  [g.innerRegion, g.calleeRegion, g.outputRegion, g.workspaceRegion]

structure Context (g : Geometry) (bs : Fin 4 → List Byte) (s : State) : Prop where
  valid : g.Valid
  sp : s.gpr .esp = g.stack
  inner : Workspace s g.stack VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes
  sources : ∀ i, PublicBytes (g.sources i) (g.sourceLength i) (bs i) s
  outputWrite : InRegions s.wr (byteAddr g.output) g.outputLength
  workspaceWrite : InRegions s.wr (byteAddr g.workspace) (8 * g.scratchLength)
  argumentsRead : InRegions (s.rd ++ s.wr) g.argumentsRegion.base 52
  arguments : ∀ j < 13, s.mem.readW (byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 20 + 4 * j)) 32 = g.argument j

theorem Context.sourceSeparate {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) (i : Fin 4) : ∀ r ∈ bodyWrites g, (g.sourceRegion i).Disjoint r := by
  intro r hr
  simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ((h.valid.stackSources i).sub_left h.valid.innerSub).symm
  · exact ((h.valid.stackSources i).sub_left h.valid.calleeSub).symm
  · exact (h.valid.outputSources i).symm
  · exact h.valid.sourcesWorkspace i

theorem Context.argumentsSeparate {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) : ∀ r ∈ bodyWrites g, g.argumentsRegion.Disjoint r := by
  intro r hr
  simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (h.valid.stackArguments.sub_left h.valid.innerSub).symm
  · exact (h.valid.stackArguments.sub_left h.valid.calleeSub).symm
  · exact h.valid.outputArguments.symm
  · exact h.valid.workspaceArguments.symm

theorem Context.after {g : Geometry} {bs : Fin 4 → List Byte} {s t : State} {rs : List Reg}
    (h : Context g bs s) (frame : Frame (bodyWrites g) s.mem t.mem) (rest : Keeps rs s t) (sp : t.gpr .esp = s.gpr .esp) : Context g bs t := by
  refine ⟨h.valid, sp.trans h.sp, h.inner.congr rest.2.2,
    fun i => (h.sources i).after_frame frame rest (h.sourceSeparate i),
    by rw [rest.2.2]; exact h.outputWrite, by rw [rest.2.2]; exact h.workspaceWrite,
    by rw [rest.2.1, rest.2.2]; exact h.argumentsRead, ?_⟩
  intro j hj
  have word := frame.readW (r := g.argumentsRegion)
    (Offset.contains_base _ (by omega_using [hj] : 4 * j + 32 / 8 ≤ 52) (by omega_using [hj] : 4 * j < 2 ^ 64))
    h.argumentsSeparate (by decide : 32 / 8 < 2 ^ 64)
  have address : g.argumentsRegion.base + BitVec.ofNat 64 (4 * j) =
      byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 20 + 4 * j) :=
    Offset.add_add _ (VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 20) (4 * j)
  change t.mem.readW (g.argumentsRegion.base + BitVec.ofNat 64 (4 * j)) 32 =
    s.mem.readW (g.argumentsRegion.base + BitVec.ofNat 64 (4 * j)) 32 at word
  rw [address] at word
  exact word.trans (h.arguments j hj)

end VG.Proof.RsaPkcs1Sig.X86.Rcv

end

end

/-! ### `RsaPkcs1Sig.X86.RecoverLocal`, which the modules that import this one used -/

section

/-! # The two local encodings and the outgoing arguments are separate -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.Proof.Bignum.X86 VG.Impl.RsaPkcs1Sig.X86.Verify

def localRegion (g : Geometry) (d n : Nat) : Region := ⟨byteAddr g.stack + BitVec.ofNat 64 d, n⟩

theorem localSub {g : Geometry} {d n : Nat} (fit : d + n ≤ VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes) :
    (localRegion g d n).Sub g.innerRegion := Offset.sub_base _ fit

theorem Context.em2Fit {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) : g.em2.toNat + g.length ≤ 2 ^ 32 :=
  h.valid.encodingFit (by have := h.valid.maxLength; simp only [em2Offset, VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes]; omega_using [this])

theorem Context.em1Sub {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) : (⟨byteAddr g.em1, g.length⟩ : Region).Sub g.innerRegion := by
  rw [Geometry.em1, h.valid.offsetAddr (by decide)]
  exact localSub (by have := h.valid.maxLength; simp only [em1Offset, VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes]; omega_using [this])

theorem Context.em2Sub {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) : (⟨byteAddr g.em2, g.length⟩ : Region).Sub g.innerRegion := by
  rw [Geometry.em2, h.valid.offsetAddr (by decide)]
  exact localSub (by have := h.valid.maxLength; simp only [em2Offset, VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes]; omega_using [this])

theorem Context.em1Write {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) : InRegions s.wr (byteAddr g.em1) g.length := by
  rw [Geometry.em1, h.valid.offsetAddr (by decide)]
  exact h.inner.write (by have := h.valid.maxLength; simp only [em1Offset, VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes]; omega_using [this])

theorem Context.em2Write {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) : InRegions s.wr (byteAddr g.em2) g.length := by
  rw [Geometry.em2, h.valid.offsetAddr (by decide)]
  exact h.inner.write (by have := h.valid.maxLength; simp only [em2Offset, VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes]; omega_using [this])

theorem Context.em1Args {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) : (⟨byteAddr g.em1, g.length⟩ : Region).Disjoint ⟨byteAddr g.stack, 40⟩ := by
  rw [Geometry.em1, h.valid.offsetAddr (by decide)]
  exact Offset.disjoint_base _ (by decide : 40 ≤ em1Offset)
    (by have := h.valid.maxLength; simp only [em1Offset]; omega_using [this])

theorem Context.encodingsSeparate {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) : (⟨byteAddr g.em1, g.length⟩ : Region).Disjoint ⟨byteAddr g.em2, g.length⟩ := by
  rw [Geometry.em1, h.valid.offsetAddr (by decide), Geometry.em2, h.valid.offsetAddr (by decide)]
  exact Offset.disjoint _ (Or.inl (by have := h.valid.maxLength; simp only [em1Offset, em2Offset]; omega_using [this]))
    (by have := h.valid.maxLength; simp only [em1Offset]; omega_using [this])
    (by have := h.valid.maxLength; simp only [em2Offset]; omega_using [this])

end VG.Proof.RsaPkcs1Sig.X86.Rcv

end

end

/-! # Copying cdecl arguments into the local outgoing call area -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Rcv
open VG VG.X86 VG.X86.Wp VG.Impl.RsaPkcs1Sig.X86.Verify VG.Proof.Bignum.X86 VG.Proof.Mont.X86

theorem Context.address {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) {d : Nat} (hd : d < VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 20 + 52) :
    addr (s.gpr .esp) d = byteAddr g.stack + BitVec.ofNat 64 d := by
  rw [h.sp]
  exact h.valid.offsetAddr hd

theorem Context.readArg {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) {j : Nat} (hj : j < 13) :
    InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) (VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 20 + 4 * j)) 4 := by
  rw [h.address (by omega_using [hj])]
  have read := CallLay.inRegions_sub (off := 4 * j) h.argumentsRead (l := 4) (by omega_using [hj]) (by decide)
  change InRegions (s.rd ++ s.wr)
    (byteAddr g.stack + BitVec.ofNat 64 (VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 20) + BitVec.ofNat 64 (4 * j)) 4 at read
  rw [Offset.add_add] at read
  exact read

theorem Context.argumentValue {g : Geometry} {bs : Fin 4 → List Byte} {s : State}
    (h : Context g bs s) {j : Nat} (hj : j < 13) :
    s.mem.readW (addr (s.gpr .esp) (VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 20 + 4 * j)) 32 = g.argument j := by
  rw [h.address (by omega_using [hj])]
  exact h.arguments j hj

theorem copyArgument_ok (s : State) {g : Geometry} {bs : Fin 4 → List Byte}
    (h : Context g bs s) {i j : Nat} (hi : i < 13) (hj : j < 10) :
    WP isa (.block (copyArgument i j)) s fun t =>
      Context g bs t ∧
      t.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 (4 * j)) (g.argument i) ∧
      Frame [⟨byteAddr g.stack + BitVec.ofNat 64 (4 * j), 4⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold copyArgument incoming stackAt
  refine wp_ldm rfl (h.readArg hi) fun u U => ?_
  refine wp_stm (B := s.gpr .esp) (U.other .esp (by decide))
    (by rw [U.wr, h.address (by omega_using [hj])]; exact h.inner.write (by simp only [VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes]; omega_using [hj]))
    fun t T => WP.block_nil ?_
  have M : t.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 (4 * j)) (g.argument i) := by
    rw [T.mem, U.gpr, U.mem, h.argumentValue hi, h.address (by omega_using [hj])]
  have K : Keeps [.eax] s t := U.keeps.trans (T.keeps _)
  have F : Frame [⟨byteAddr g.stack + BitVec.ofNat 64 (4 * j), 4⟩] s.mem t.mem := by
    rw [M]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨h.after (F.sub ?_) K (K.1 .esp (by decide)), M, F, K⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨g.innerRegion, by simp [bodyWrites], Offset.sub_base _ (by simp only [VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes]; omega_using [hj])⟩

end VG.Proof.RsaPkcs1Sig.X86.Rcv

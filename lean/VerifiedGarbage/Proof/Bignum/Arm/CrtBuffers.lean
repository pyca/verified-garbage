module

public import VerifiedGarbage.Proof.Bignum.Arm.PublicBuffers
public import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Public geometry and immutable source buffers of a private CRT call

Source indices are n, input, p, q, dP, dQ and qInv. The geometry is public;
the byte lists remain independent in the two executions of the leakage proof.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt
open VG.Proof.X25519.Arm (Rest)

structure CrtGeometry where
  base : BitVec 32
  output : BitVec 32
  modulus : BitVec 32
  input : BitVec 32
  p : BitVec 32
  q : BitVec 32
  dp : BitVec 32
  dq : BitVec 32
  qi : BitVec 32
  size : Nat
  length : Nat
  pLength : Nat
  qLength : Nat

def CrtGeometry.source (g : CrtGeometry) (i : Fin 7) : BitVec 32 :=
  match i.val with
  | 0 => g.modulus | 1 => g.input | 2 => g.p | 3 => g.q | 4 => g.dp | 5 => g.dq | _ => g.qi

def CrtGeometry.sourceLength (g : CrtGeometry) (i : Fin 7) : Nat :=
  match i.val with
  | 0 | 1 => g.length | 3 | 5 => g.qLength | _ => g.pLength

def CrtGeometry.words (g : CrtGeometry) : Nat := Spec.Rsa.modulusWords g.length

structure CrtBuffers (g : CrtGeometry) (bs : Fin 7 → List Byte) (s : State) : Prop where
  workspace : Workspace s g.base g.size
  context : CrtSetupContext g.base (workspaceWords g.words) g.words s
  lengthValid : Spec.Rsa.lenValid g.length
  storageFits : totalBytes g.words ≤ g.size
  pPositive : 0 < g.pLength
  pShort : g.pLength < g.length
  qPositive : 0 < g.qLength
  qShort : g.qLength < g.length
  source : ∀ i, PublicBytes (g.source i) (g.sourceLength i) (bs i) s
  sourceSeparate : ∀ i, Region.Disjoint ⟨State.addr (g.source i), g.sourceLength i⟩ ⟨State.addr g.base, g.size⟩
  sourceStack : ∀ i, Region.Disjoint ⟨State.addr (g.source i), g.sourceLength i⟩ ⟨State.addr s.sp, 56⟩
  outputFits : g.output.toNat + g.length ≤ 2 ^ 32
  write : InRegions s.wr (State.addr g.output) g.length
  outputSeparate : Region.Disjoint ⟨State.addr g.base, g.size⟩ ⟨State.addr g.output, g.length⟩
  outputStack : Region.Disjoint ⟨State.addr g.output, g.length⟩ ⟨State.addr s.sp, 56⟩

theorem CrtBuffers.after_frame {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    {regions : List Region} {rs : List Reg} (h : CrtBuffers g bs s)
    (frame : Frame regions s.mem t.mem) (rest : Rest rs s t)
    (separate : ∀ i r, r ∈ regions → (⟨State.addr (g.source i), g.sourceLength i⟩ : Region).Disjoint r) :
    CrtBuffers g bs t := by
  refine ⟨h.workspace.congr rest.wr, h.context.congr rest.wr, h.lengthValid, h.storageFits,
    h.pPositive, h.pShort, h.qPositive, h.qShort,
    fun i => (h.source i).after_frame frame rest (separate i), h.sourceSeparate,
    ?_, h.outputFits, ?_, h.outputSeparate, ?_⟩
  · intro i; rw [rest.sp]; exact h.sourceStack i
  · rw [rest.wr]; exact h.write
  · rw [rest.sp]; exact h.outputStack

theorem CrtBuffers.after_scratch {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {rs : List Reg}
    (h : CrtBuffers g bs s) (frame : Frame [⟨State.addr g.base, g.size⟩] s.mem t.mem) (rest : Rest rs s t) :
    CrtBuffers g bs t :=
  h.after_frame frame rest (by intro i r hr; simp only [List.mem_singleton] at hr; subst r; exact h.sourceSeparate i)

theorem CrtBuffers.after_stack {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {rs : List Reg}
    (h : CrtBuffers g bs s) (frame : Frame [⟨State.addr s.sp, 56⟩] s.mem t.mem) (rest : Rest rs s t) :
    CrtBuffers g bs t :=
  h.after_frame frame rest (by intro i r hr; simp only [List.mem_singleton] at hr; subst r; exact h.sourceStack i)

end VG.Proof.Bignum.Arm

module

public import VerifiedGarbage.Proof.Bignum.Arm.PublicBuffers
public import VerifiedGarbage.Proof.Bignum.Arm.CrtSetupContext
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Rsa.BytesFrame
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Public geometry and immutable source buffers of a private CRT call

Source indices are n, input, p, q, dP, dQ and qInv. The geometry is public;
the byte lists remain independent in the two executions of the leakage proof.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Mont (off)

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
  /-- For `vg_rsa_private_crt_precomputed`, the address of the factors'
  `R² mod p` and `R² mod q` (`Spec.Rsa.primeR2`), which its frame slot 112
  holds. -/
  r2 : Option (BitVec 32) := none

def CrtGeometry.source (g : CrtGeometry) (i : Fin 7) : BitVec 32 :=
  match i.val with
  | 0 => g.modulus | 1 => g.input | 2 => g.p | 3 => g.q | 4 => g.dp | 5 => g.dq | _ => g.qi

def CrtGeometry.sourceLength (g : CrtGeometry) (i : Fin 7) : Nat :=
  match i.val with
  | 0 | 1 => g.length | 3 | 5 => g.qLength | _ => g.pLength

def CrtGeometry.words (g : CrtGeometry) : Nat := Spec.Rsa.modulusWords g.length

/-- The words of `R² mod p` and `R² mod q`. -/
def CrtGeometry.r2Words (g : CrtGeometry) : Nat := Spec.Rsa.primeWords g.pLength + Spec.Rsa.primeWords g.qLength

/-- `R² mod p` and `R² mod q` at `a`, which frame slot 112 holds. -/
structure CrtR2 (g : CrtGeometry) (bs : Fin 7 → List Byte) (a : BitVec 32) (s : State) : Prop where
  slotFit : s.sp.toNat + 116 ≤ 2 ^ 32
  slotRead : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 112) 4
  slot : s.mem.readW (off (State.addr s.sp) 112) 32 = a
  slotSeparate : Region.Disjoint ⟨off (State.addr s.sp) 112, 4⟩ ⟨State.addr g.base, g.size⟩
  slotOutput : Region.Disjoint ⟨off (State.addr s.sp) 112, 4⟩ ⟨State.addr g.output, g.length⟩
  fit : a.toNat + 8 * g.r2Words ≤ 2 ^ 32
  read : InRegions (s.rd ++ s.wr) (State.addr a) (8 * g.r2Words)
  separate : Region.Disjoint ⟨State.addr a, 8 * g.r2Words⟩ ⟨State.addr g.base, g.size⟩
  stack : Region.Disjoint ⟨State.addr a, 8 * g.r2Words⟩ ⟨State.addr s.sp, 56⟩
  output : Region.Disjoint ⟨State.addr a, 8 * g.r2Words⟩ ⟨State.addr g.output, g.length⟩
  words : Spec.Rsa.wordsAt s.mem (State.addr a) g.r2Words = Spec.Rsa.primeR2 (bs 2) ++ Spec.Rsa.primeR2 (bs 3)

/-- The regions of `R² mod p` and `R² mod q` and of frame slot 112. -/
def CrtR2Separate (g : CrtGeometry) (sp : BitVec 32) (regions : List Region) : Prop :=
  ∀ a, g.r2 = some a → ∀ r ∈ regions,
    Region.Disjoint ⟨State.addr a, 8 * g.r2Words⟩ r ∧ Region.Disjoint ⟨off (State.addr sp) 112, 4⟩ r

theorem crtR2Separate_none {g : CrtGeometry} (h : g.r2 = none) (sp : BitVec 32) (regions : List Region) :
    CrtR2Separate g sp regions := by
  intro a ha; rw [h] at ha; cases ha

theorem CrtR2.after_frame {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte} {a : BitVec 32}
    {regions : List Region} {rs : List Reg} (h : CrtR2 g bs a s)
    (frame : Frame regions s.mem t.mem) (rest : Rest rs s t)
    (separate : ∀ r ∈ regions,
      Region.Disjoint ⟨State.addr a, 8 * g.r2Words⟩ r ∧ Region.Disjoint ⟨off (State.addr s.sp) 112, 4⟩ r) :
    CrtR2 g bs a t := by
  have sp := rest.sp
  refine ⟨by rw [sp]; exact h.slotFit, by rw [rest.rd, rest.wr, sp]; exact h.slotRead, ?_,
    by rw [sp]; exact h.slotSeparate, by rw [sp]; exact h.slotOutput, h.fit,
    by rw [rest.rd, rest.wr]; exact h.read, h.separate, by rw [sp]; exact h.stack, h.output, ?_⟩
  · rw [sp, frame.readW (r := ⟨off (State.addr s.sp) 112, 4⟩) (Region.contains_self _ _)
      (fun r hr => (separate r hr).2) (by decide)]
    exact h.slot
  · rw [Rsa.wordsAt_frame frame (by have := h.fit; omega_using [this]) (fun r hr => (separate r hr).1)]
    exact h.words

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
  r2 : ∀ a, g.r2 = some a → CrtR2 g bs a s

theorem CrtBuffers.after_frame {s t : State} {g : CrtGeometry} {bs : Fin 7 → List Byte}
    {regions : List Region} {rs : List Reg} (h : CrtBuffers g bs s)
    (frame : Frame regions s.mem t.mem) (rest : Rest rs s t)
    (separate : ∀ i r, r ∈ regions → (⟨State.addr (g.source i), g.sourceLength i⟩ : Region).Disjoint r)
    (r2 : CrtR2Separate g s.sp regions) :
    CrtBuffers g bs t := by
  refine ⟨h.workspace.congr rest.wr, h.context.congr rest.wr, h.lengthValid, h.storageFits,
    h.pPositive, h.pShort, h.qPositive, h.qShort,
    fun i => (h.source i).after_frame frame rest (separate i), h.sourceSeparate,
    ?_, h.outputFits, ?_, h.outputSeparate, ?_,
    fun a ha => (h.r2 a ha).after_frame frame rest (r2 a ha)⟩
  · intro i; rw [rest.sp]; exact h.sourceStack i
  · rw [rest.wr]; exact h.write
  · rw [rest.sp]; exact h.outputStack

end VG.Proof.Bignum.Arm

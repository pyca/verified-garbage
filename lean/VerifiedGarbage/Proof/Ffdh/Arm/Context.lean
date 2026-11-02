module

import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
public import VerifiedGarbage.Proof.Ffdh.KeyScalar
public import VerifiedGarbage.Proof.Ffdh.Arm.Locals
public import VerifiedGarbage.Proof.Ffdh.Arm.Octets
import VerifiedGarbage.Proof.Ffdh.Arm.Prepare
import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Bignum.Arm.LayoutPreserved
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.MontContract

/-! Common argument and memory invariants of the native FFDH operations. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure Inputs where
  base : BitVec 32
  domain : BitVec 32
  publicValue : BitVec 32
  privateValue : BitVec 32
  output : BitVec 32
  entropy : BitVec 32
  len : Nat
  k : Nat
  privateLength : Nat
  hasQ : Bool
  dom : List Byte
  minLength : 64 ≤ k
  maxLength : k ≤ 1024
  space : Spec.Rsa.scratchWords k ≤ len
  domainLength : dom.length = if hasQ then 3 * k else 2 * k
  cachedContext : BitVec 32 := 0
  cachedWords : Nat := 0

namespace Inputs

def g (p : Inputs) : BitVec 32 := p.domain + BitVec.ofNat 32 p.k
def q (p : Inputs) : BitVec 32 := p.domain + BitVec.ofNat 32 (2 * p.k)
def P (p : Inputs) : Nat := Spec.Rsa.os2ip (p.dom.take p.k)
def G (p : Inputs) : Nat := Spec.Rsa.os2ip ((p.dom.drop p.k).take p.k)
def Q (p : Inputs) : Nat := Spec.Rsa.os2ip ((p.dom.drop (2 * p.k)).take p.k)
def w (p : Inputs) : Nat := Spec.Rsa.modulusWords p.k

def boundSource (p : Inputs) : BitVec 32 := if p.hasQ = true then p.q else p.domain
def boundOctets (p : Inputs) : List Byte := VG.Proof.Ffdh.KeyScalar.bnd p.k p.dom
def scalarLead (p : Inputs) : Nat := VG.Proof.Ffdh.lead p.boundOctets
def scalarWidth (p : Inputs) : Nat := p.k - p.scalarLead
def scalarStart (p : Inputs) : BitVec 32 := p.privateValue + BitVec.ofNat 32 p.scalarLead
def scalarMask (p : Inputs) : BitVec 32 :=
  BitVec.ofNat 32 (VG.Proof.Ffdh.KeyScalar.smearN (p.boundOctets.getD p.scalarLead 0).toNat)

def slotValue (p : Inputs) : Nat → BitVec 32
  | 0 => p.base
  | 4 => p.output
  | 16 => p.scalarStart
  | 20 => BitVec.ofNat 32 p.scalarWidth
  | 24 => p.domain
  | 28 => BitVec.ofNat 32 p.dom.length
  | 32 => BitVec.ofNat 32 p.k
  | 36 => p.publicValue
  | 40 => p.privateValue
  | 44 => BitVec.ofNat 32 p.privateLength
  | 48 => p.entropy
  | 52 => p.cachedContext
  | 56 => p.g
  | 60 => p.q
  | 68 => p.scalarMask
  | _ => 0

theorem publicSpace (p : Inputs) : Spec.Rsa.publicScratchWords p.k ≤ p.len := by
  have := p.space
  have := p.minLength
  simp only [Spec.Rsa.scratchWords, Spec.Rsa.publicScratchWords, Spec.Rsa.modulusWords] at *
  omega

theorem width (p : Inputs) : 2 ≤ p.w ∧ p.w < 2 ^ 31 ∧
    Proof.Rsa.Mont.arrAt p.w 16 ≤ 8 * p.len ∧ p.k ≤ 8 * p.w ∧ 128 * p.w < 2 ^ 32 := by
  have dims := pc_dimensions (k := p.k) (len := p.len) p.minLength p.maxLength (by
    have := p.space
    have := p.minLength
    simp only [Spec.Rsa.scratchWords, Spec.Rsa.publicScratchWords,
      Spec.Rsa.modulusWords] at *
    omega)
  refine ⟨dims.1, dims.2.1, ?_, dims.2.2.2.1, dims.2.2.2.2⟩
  have := p.space
  have := p.minLength
  simp only [Spec.Rsa.scratchWords, Proof.Rsa.Mont.arrAt, w,
    Spec.Rsa.modulusWords, Proof.Rsa.Mont.hdrBytes] at *
  omega

theorem pLength (p : Inputs) : (p.dom.take p.k).length = p.k := by
  simp only [List.length_take, p.domainLength]
  split <;> omega

theorem gLength (p : Inputs) : ((p.dom.drop p.k).take p.k).length = p.k := by
  simp only [List.length_take, List.length_drop, p.domainLength]
  split <;> omega

theorem qLength (p : Inputs) (hasQ : p.hasQ = true) : ((p.dom.drop (2 * p.k)).take p.k).length = p.k := by
  simp only [List.length_take, List.length_drop, p.domainLength, hasQ, ite_true]
  omega

end Inputs

structure ArgumentMemory (p : Inputs) (slots : List Nat) (s : State) : Prop where
  workspace : Workspace s p.base (8 * p.len)
  locals : Locals p.base p.len s
  domain : Octets p.base p.domain p.len p.dom s
  domainStack : Region.Disjoint ⟨State.addr p.domain, p.dom.length⟩ ⟨State.addr s.sp, 72⟩
  saved : ∀ d ∈ slots, s.mem.readW (off (State.addr s.sp) d) 32 = p.slotValue d

theorem ArgumentMemory.domainSliceStack {p : Inputs} {slots : List Nat} {s : State}
    (h : ArgumentMemory p slots s) {d k : Nat} (positive : 0 < k) (fit : d + k ≤ p.dom.length) :
    Region.Disjoint ⟨State.addr (p.domain + BitVec.ofNat 32 d), k⟩ ⟨State.addr s.sp, 72⟩ := by
  rw [VG.Arm.addr_add (by have := h.domain.fits; omega)]
  exact h.domainStack.sub_left (Offset.sub_base _ fit)

theorem ArgumentMemory.after_frame {p : Inputs} {slots : List Nat} {s t : State} {rs : List Reg}
    {regions : List Region} (h : ArgumentMemory p slots s) (frame : Frame regions s.mem t.mem)
    (rest : Rest rs s t)
    (domainSep : ∀ r ∈ regions, (⟨State.addr p.domain, p.dom.length⟩ : Region).Disjoint r)
    (savedSep : ∀ d ∈ slots, ∀ r ∈ regions, (⟨off (State.addr s.sp) d, 4⟩ : Region).Disjoint r) :
    ArgumentMemory p slots t := by
  refine ⟨h.workspace.congr rest.wr, h.locals.after rest, h.domain.after_frame frame rest domainSep,
    by rw [rest.sp]; exact h.domainStack, ?_⟩
  intro d hd
  rw [rest.sp, frame.readW (r := ⟨off (State.addr s.sp) d, 4⟩) (Region.contains_self _ _)
    (savedSep d hd) (by decide)]
  exact h.saved d hd

theorem ArgumentMemory.after_workspace {p : Inputs} {slots : List Nat} {s t : State} {rs : List Reg}
    (h : ArgumentMemory p slots s) (frame : Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem)
    (rest : Rest rs s t) (fit : ∀ d ∈ slots, d + 4 ≤ 72) :
    ArgumentMemory p slots t := by
  have stack := WorkspaceEq.of_frame (by decide : 72 < 2 ^ 64) frame
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h.locals.separate)
  refine ⟨h.workspace.congr rest.wr, h.locals.after rest, h.domain.after_workspace frame rest,
    by rw [rest.sp]; exact h.domainStack, ?_⟩
  intro d hd
  rw [rest.sp, stack.word (bits := 32) (fit d hd)]
  exact h.saved d hd

structure Context (p : Inputs) (slots : List Nat) (s : State) : Prop extends ArgumentMemory p slots s where
  ptr : s.gpr .r0 = p.base

theorem Context.after_frame {p : Inputs} {slots : List Nat} {s t : State} {rs : List Reg}
    {regions : List Region} (h : Context p slots s) (frame : Frame regions s.mem t.mem)
    (rest : Rest rs s t) (ptr : t.gpr .r0 = p.base)
    (domainSep : ∀ r ∈ regions, (⟨State.addr p.domain, p.dom.length⟩ : Region).Disjoint r)
    (savedSep : ∀ d ∈ slots, ∀ r ∈ regions, (⟨off (State.addr s.sp) d, 4⟩ : Region).Disjoint r) :
    Context p slots t := ⟨h.toArgumentMemory.after_frame frame rest domainSep savedSep, ptr⟩

theorem Context.after_local {p : Inputs} {slots : List Nat} {s t : State} {rs : List Reg} {d : Nat}
    (h : Context p slots s) (fit : d + 4 ≤ 72)
    (frame : Frame [⟨off (State.addr s.sp) d, 4⟩] s.mem t.mem) (rest : Rest rs s t)
    (ptr : t.gpr .r0 = p.base) (bounds : ∀ e ∈ slots, e + 4 ≤ 72)
    (saved : ∀ e ∈ slots, e + 4 ≤ d ∨ d + 4 ≤ e) :
    Context p slots t := by
  refine h.after_frame frame rest ptr ?_ ?_
  · intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact h.domainStack.sub_right (Offset.sub_base _ fit)
  · intro e he r hr
    rw [List.mem_singleton] at hr
    subst r
    have := bounds e he
    exact Offset.disjoint _ (saved e he) (by have := h.locals.space.nowrap; omega)
      (by have := h.locals.space.nowrap; omega)

theorem Context.of_mem {p : Inputs} {slots : List Nat} {s t : State} {rs : List Reg}
    (h : Context p slots s) (mem : t.mem = s.mem) (rest : Rest rs s t) (ptr : t.gpr .r0 = p.base) :
    Context p slots t := by
  have frame : Frame [] s.mem t.mem := by rw [mem]; exact Frame.refl _ _
  exact h.after_frame frame rest ptr (by simp) (by simp)

theorem Context.after_workspace {p : Inputs} {slots : List Nat} {s t : State} {rs : List Reg}
    (h : Context p slots s) (frame : Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem)
    (rest : Rest rs s t) (ptr : t.gpr .r0 = p.base) (fit : ∀ d ∈ slots, d + 4 ≤ 72) :
    Context p slots t := ⟨h.toArgumentMemory.after_workspace frame rest fit, ptr⟩

theorem Context.pBytes {p : Inputs} {slots : List Nat} {s : State} (h : Context p slots s) :
    Octets p.base p.domain p.len (p.dom.take p.k) s := by
  have fit : 0 + p.k ≤ p.dom.length := by rw [p.domainLength]; split <;> have := p.minLength <;> omega
  simpa only [List.drop_zero, BitVec.add_zero] using h.domain.slice (by have := p.minLength; omega) fit

theorem Context.gBytes {p : Inputs} {slots : List Nat} {s : State} (h : Context p slots s) :
    Octets p.base p.g p.len ((p.dom.drop p.k).take p.k) s :=
  h.domain.slice (by have := p.minLength; omega) (by rw [p.domainLength]; split <;> omega)

theorem Context.qBytes {p : Inputs} {slots : List Nat} {s : State} (h : Context p slots s)
    (hasQ : p.hasQ = true) : Octets p.base p.q p.len ((p.dom.drop (2 * p.k)).take p.k) s :=
  h.domain.slice (by have := p.minLength; omega) (by rw [p.domainLength, hasQ]; simp only [ite_true]; omega)

end VG.Proof.Ffdh.Arm

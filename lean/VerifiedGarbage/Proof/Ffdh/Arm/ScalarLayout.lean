module

public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Proof.Ffdh.Arm.VettedScalarSpec
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyGeometry

/-! Public scalar geometry independent of the domain's full-width bound. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont

/-- Common argument slots avoid the three words owned by the scalar layout. -/
def sampleSlots (slots : List Nat) : Prop :=
  ∀ d ∈ slots, d + 4 ≤ 16 ∨ 24 ≤ d ∧ d + 4 ≤ 68

structure ScalarLayout (p : Inputs) where
  lead : Nat
  mask : BitVec 32
  lead_lt : lead < p.k

namespace ScalarLayout

def width {p : Inputs} (l : ScalarLayout p) : Nat := p.k - l.lead
def start {p : Inputs} (l : ScalarLayout p) : BitVec 32 :=
  p.privateValue + BitVec.ofNat 32 l.lead
def encode {p : Inputs} (l : ScalarLayout p) (rb : List Byte) : List Byte :=
  VG.Proof.Ffdh.KeyScalar.cut rb l.lead (l.mask.setWidth 8)

theorem width_bounds {p : Inputs} (l : ScalarLayout p) : 0 < l.width ∧ l.width ≤ p.k := by
  have := l.lead_lt
  unfold width
  omega

theorem encode_length {p : Inputs} (l : ScalarLayout p) {rb : List Byte}
    (size : rb.length = p.k) : (l.encode rb).length = p.k := by
  rw [encode, VG.Proof.Ffdh.KeyScalar.cut_length _ (by have := l.lead_lt; omega), size]

theorem encode_significant {p : Inputs} (l : ScalarLayout p) (rb : List Byte) :
    Spec.Rsa.os2ip ((l.encode rb).drop l.lead) = Spec.Rsa.os2ip (l.encode rb) :=
  VG.Proof.Ffdh.KeyScalar.os2ip_cut_drop _ _ _

def standard (p : Inputs) : ScalarLayout p :=
  ⟨p.scalarLead, p.scalarMask, p.scalarLeadBound⟩

def vetted (p : Inputs) : ScalarLayout p :=
  let bits := Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom)
  let count := VG.Proof.Ffdh.ScalarWidth.width bits
  ⟨p.k - count, (VG.Proof.Ffdh.ScalarWidth.mask bits).zeroExtend 32, by
    have positive := VG.Proof.Ffdh.ScalarWidth.width_pos bits
    have fits : count ≤ p.k := VG.Proof.Ffdh.ScalarWidth.width_le (by have := p.minLength; omega)
      (Nat.le_trans (VG.Proof.Ffdh.VettedPolicy.bits_le_bound _) p.scalarBound_bits_fit)
    change p.k - count < p.k
    omega⟩

theorem vetted_encode {p : Inputs} {rb : List Byte} (size : rb.length = p.k) :
    (vetted p).encode rb = vettedScalarOctets p rb := by
  unfold encode vetted vettedScalarOctets VG.Proof.Ffdh.VettedPolicy.octets
  rw [size]
  congr 1
  simp

theorem vetted_value {p : Inputs} {rb : List Byte} (size : rb.length = p.k) :
    Spec.Rsa.os2ip ((vetted p).encode rb) =
      Spec.Ffdh.vettedScalarOfOctets (Spec.Ffdh.domainOf p.k p.dom) rb := by
  rw [vetted_encode size]
  exact vettedScalarOctets_value size

end ScalarLayout

/-- Ordinary saved arguments keep their existing meaning. Only the three
scalar-layout slots use the selected public sampling policy. -/
structure SampleContext (p : Inputs) (l : ScalarLayout p) (slots : List Nat) (s : State)
    extends Context p slots s where
  scalarStart : s.mem.readW (off (State.addr s.sp) 16) 32 = l.start
  scalarWidth : s.mem.readW (off (State.addr s.sp) 20) 32 = BitVec.ofNat 32 l.width
  scalarMask : s.mem.readW (off (State.addr s.sp) 68) 32 = l.mask

theorem SampleContext.of_standard {p : Inputs} {slots : List Nat} {s : State}
    (h : Context p slots s) (h16 : 16 ∈ slots) (h20 : 20 ∈ slots) (h68 : 68 ∈ slots) :
    SampleContext p (ScalarLayout.standard p) slots s :=
  ⟨h, h.saved 16 h16, h.saved 20 h20, h.saved 68 h68⟩

theorem SampleContext.after_kept {p : Inputs} {l : ScalarLayout p} {slots : List Nat}
    {s t : State} (h : SampleContext p l slots s) (context : Context p slots t)
    (sp : t.sp = s.sp)
    (kept : ∀ d ∈ [16, 20, 68], t.mem.readW (off (State.addr s.sp) d) 32 =
      s.mem.readW (off (State.addr s.sp) d) 32) : SampleContext p l slots t := by
  refine ⟨context, ?_, ?_, ?_⟩
  · rw [sp, kept 16 (by simp)]; exact h.scalarStart
  · rw [sp, kept 20 (by simp)]; exact h.scalarWidth
  · rw [sp, kept 68 (by simp)]; exact h.scalarMask

end VG.Proof.Ffdh.Arm

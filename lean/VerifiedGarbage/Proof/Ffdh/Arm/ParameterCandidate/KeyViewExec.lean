module

public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.Framework.Arm.Inline
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! RSA's native key helpers use a header view beginning 96 bytes into the
same scratch allocation. Narrowing permissions makes their existing proofs
callable without granting access to a single byte outside that allocation. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

def keyViewRegion (base : BitVec 32) (capacity : Nat) : Region :=
  ⟨State.addr (base + 96#32), 8 * capacity - 96⟩

theorem keyView_covers {s : State} {base : BitVec 32} {capacity : Nat}
    (h : Workspace s base (8 * capacity)) (large : 96 < 8 * capacity) :
    Covers [keyViewRegion base capacity] s.wr := by
  apply Covers.of_sub
  intro r member
  rw [List.mem_singleton] at member
  subst r
  refine ⟨⟨State.addr base, 8 * capacity⟩, h.writable, 96, ?_, by simp only [keyViewRegion]; omega⟩
  exact VG.Arm.addr_add (by have := h.nowrap; omega)

theorem keyView_dimensions {k capacity : Nat} (minLength : 64 ≤ k) (maxLength : k ≤ 1024)
    (space : Spec.Rsa.scratchWords k ≤ capacity) :
    0 < 2 * ((k + 7) / 8) + 2 ∧ 2 * ((k + 7) / 8) + 2 ≤ 1024 ∧
      160 + 30 * (4 * (2 * ((k + 7) / 8) + 4)) ≤ 8 * capacity - 96 := by
  simp only [Spec.Rsa.scratchWords] at space
  omega

theorem keyView_inline {c : Prog isa} {s : State} {base : BitVec 32} {capacity : Nat}
    {P Q : State → Prop} (workspace : Workspace s base (8 * capacity)) (large : 96 < 8 * capacity)
    (proof : WP isa c (s.withRegions s.rd [keyViewRegion base capacity]) P)
    (noCalls : c.noCalls = true)
    (done : ∀ t, t.rd = s.rd → t.wr = s.wr →
      Frame [keyViewRegion base capacity] s.mem t.mem →
      P (t.withRegions s.rd [keyViewRegion base capacity]) → Q t) : WP isa c s Q := by
  have writes := keyView_covers workspace large
  exact regionModel.wp_narrow proof ((Covers.refl s.rd).append writes) writes
    (Code.noFrames_of_noCalls noCalls) (.inl noCalls) (fun _ t _ rd wr frame post => done t rd wr frame post)

theorem rest_of_keyView {s t : State} {rs : List Reg} {base : BitVec 32} {capacity : Nat}
    (h : Rest rs (s.withRegions s.rd [keyViewRegion base capacity])
      (t.withRegions s.rd [keyViewRegion base capacity]))
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) : Rest rs s t := ⟨h.gpr, rd, wr, h.sp⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate

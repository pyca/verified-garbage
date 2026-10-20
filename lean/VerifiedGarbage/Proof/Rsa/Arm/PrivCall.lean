module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivSlots
public import VerifiedGarbage.Proof.Rsa.Arm.PrivContext
import VerifiedGarbage.Proof.Rsa.Arm.PrivRegions
import VerifiedGarbage.Proof.Framework.Offset

/-! # Calls with their own frames preserve retained private-wrapper state -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

def callClobbers : List Reg := [.r0, .r1, .r2, .r3, .r12, .lr]

theorem call_rest {s t : State} (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sp : t.sp = s.sp)
    (regs : ∀ r ∈ preserved, r ≠ .lr → t.gpr r = s.gpr r) : Rest callClobbers s t := by
  refine ⟨?_, rd, wr, sp⟩
  intro r hr
  apply regs r
  · cases r <;> simp_all [callClobbers, preserved]
  · intro eq; subst r; exact hr (by simp [callClobbers])

theorem private_call_ok {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) (slots : PrivSlots g s.mem)
    {name : String} {code : Prog isa} {contract : Contract isa}
    (verified : Verified target code contract) (stack : FrameStack.armStack code ≤ 56)
    {rd wr : List Region} (pre : contract.pre (s.callEntry.withRegions rd wr))
    (read : Covers (rd ++ wr) (s.rd ++ s.wr)) (write : Covers wr s.wr)
    (sub : ∀ r ∈ wr, ∃ R ∈ bodyWrites g, r.Sub R)
    (separate : ∀ r ∈ wr, (⟨off (State.addr g.stack) 64, 24⟩ : Region).Disjoint r) :
    WP isa (.call name code) s fun t => PrivContext g bs t ∧ PrivSlots g t.mem ∧
      Frame (wr ++ [g.calleeRegion]) s.mem t.mem ∧ Rest callClobbers s t ∧
      contract.post (s.callEntry.withRegions rd wr) (t.withRegions rd wr) := by
  refine FrameStack.WP.callF verified.1 pre read write
    (by rw [h.sp]; exact Nat.le_trans stack h.valid.stackLow) ?_
  intro t rdT wrT spT frame regs post
  have frame56 := FrameStack.Frame.belowA_mono frame stack (by rw [h.sp]; exact h.valid.stackLow)
  rw [h.sp] at frame56
  have rest := call_rest rdT wrT spT regs
  have frameBody : Frame (bodyWrites g) s.mem t.mem := frame56.sub (by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact sub r hr
    · simp only [List.mem_singleton] at hr
      subst r
      exact ⟨g.calleeRegion, by simp [bodyWrites], fun _ hx => hx⟩)
  refine ⟨h.after frameBody rest, slots.after frame56 ?_, frame56, rest, post⟩
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact separate r hr
  · simp only [List.mem_singleton] at hr
    subst r
    exact (h.valid.calleeInner.sub_right (Offset.sub_base _ (by decide : 64 + 24 ≤ frameBytes))).symm
end VG.Proof.Rsa.Arm

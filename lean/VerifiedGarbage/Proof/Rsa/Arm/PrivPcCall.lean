module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivPcPre
public import VerifiedGarbage.Proof.Rsa.Arm.PrivCall
import VerifiedGarbage.Proof.Rsa.Arm.PrivRegions
import VerifiedGarbage.Proof.Framework.Offset

/-! # Call the verified public precomputation without changing the private intermediate -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem PrivContext.precomputationWrite {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) : InRegions s.wr (State.addr g.precomputation) (16 * Spec.Rsa.modulusWords g.length) := by
  rw [PrivGeometry.precomputation, h.valid.offsetAddr (by decide)]
  exact ⟨_, h.inner.writable, Offset.contains_base _
    (by have := h.valid.maxLength; simp only [oPre, frameBytes, Spec.Rsa.modulusWords]; omega) (by decide : oPre < 2 ^ 64)⟩

theorem pcCovers {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State} (h : PrivContext g bs s) :
    Covers (pcRd g ++ pcWr g) (s.rd ++ s.wr) ∧ Covers (pcWr g) s.wr := by
  have wr : Covers (pcWr g) s.wr := (Covers.one h.precomputationWrite).pair (Covers.one h.workspaceWrite)
  refine ⟨Covers.append_left ?_ wr.right, wr⟩
  refine (Covers.one (h.sources 0).read).cons ?_
  exact (Covers.one (show InRegions s.wr (State.addr g.stack) 8 from
    ⟨_, h.inner.writable, by simp [Region.Contains, frameBytes]⟩)).right

theorem pcWrites_sub {g : PrivGeometry} (h : g.Valid) :
    ∀ r ∈ pcWr g, ∃ R ∈ bodyWrites g, r.Sub R := by
  intro r hr
  simp only [pcWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine ⟨g.innerRegion, by simp [bodyWrites], ?_⟩
    rw [PrivGeometry.precomputation, h.offsetAddr (by decide)]
    exact Offset.sub_base _ (by have := h.maxLength; simp only [oPre, frameBytes, Spec.Rsa.modulusWords]; omega)
  · exact ⟨g.workspaceRegion, by simp [bodyWrites], fun _ hx => hx⟩

theorem pcWrites_slots {g : PrivGeometry} (h : g.Valid) :
    ∀ r ∈ pcWr g, (⟨off (State.addr g.stack) 64, 24⟩ : Region).Disjoint r := by
  intro r hr
  simp only [pcWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [PrivGeometry.precomputation, h.offsetAddr (by decide)]
    exact Offset.disjoint _ (Or.inl (by decide : 64 + 24 ≤ oPre)) (by decide)
      (by have := h.maxLength; simp only [oPre, Spec.Rsa.modulusWords]; omega)
  · exact h.stackWorkspace.sub_left (fun x hx => h.innerSub x
      (Offset.sub_base _ (by decide : 64 + 24 ≤ frameBytes) x hx))

def PcOut (g : PrivGeometry) (bs : Fin 8 → List Byte) (s : State) : Prop :=
  match Spec.Rsa.publicPrecompute (bs 0) with
  | some ws => s.gpr .r0 = 1 ∧ Spec.Rsa.wordsAt s.mem (State.addr g.precomputation) (2 * Spec.Rsa.modulusWords g.length) = ws
  | none => s.gpr .r0 = 0 ∧ Spec.Rsa.wordsAt s.mem (State.addr g.precomputation) (2 * Spec.Rsa.modulusWords g.length) =
      List.replicate (2 * Spec.Rsa.modulusWords g.length) 0

theorem pc_call (v : CrtImpl) {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) (slots : PrivSlots g s.mem) (args : PcArgs g s) :
    WP isa (.call v.pcName v.pc) s fun t => PrivContext g bs t ∧ PrivSlots g t.mem ∧
      Frame (pcWr g ++ [g.calleeRegion]) s.mem t.mem ∧ Rest callClobbers s t ∧
      PcOut g bs t := by
  refine WP.mono (private_call_ok h slots v.pcVerified v.pcStack (pcCall_pre h args)
    (pcCovers h).1 (pcCovers h).2 (pcWrites_sub h.valid) (pcWrites_slots h.valid)) ?_
  rintro t ⟨ht, slotsT, frame, rest, post⟩
  refine ⟨ht, slotsT, frame, rest, ?_⟩
  sig_post [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at post
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega
  have pfit : 2 * Spec.Rsa.modulusWords g.length < 2 ^ 32 := by
    have := h.valid.maxLength; simp only [Spec.Rsa.modulusWords]; omega
  simp only [args.output, args.outputLength, args.modulus, args.length, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt kfit, Nat.mod_eq_of_lt pfit] at post
  rw [BitVec.setWidth_append_eq_right] at post
  have nb : Spec.Rsa.bytesAt s.mem ((g.sources 0).setWidth 64) g.length = bs 0 := (h.sources 0).bytes
  rw [nb] at post
  exact post
end VG.Proof.Rsa.Arm

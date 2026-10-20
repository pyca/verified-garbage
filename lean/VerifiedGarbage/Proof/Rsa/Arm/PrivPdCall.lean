module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivPdPre
public import VerifiedGarbage.Proof.Rsa.Arm.PrivCall
import VerifiedGarbage.Proof.Rsa.Arm.PrivPcCall
import VerifiedGarbage.Proof.Rsa.Arm.PrivCrtCall
import VerifiedGarbage.Proof.Rsa.Arm.PrivRegions
import VerifiedGarbage.Proof.Framework.Offset

/-! # Call verified public re-exponentiation while retaining the private intermediate -/

@[expose] public section
namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem pdCovers {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State} (h : PrivContext g bs s) :
    Covers (pdRd g ++ pdWr g) (s.rd ++ s.wr) ∧ Covers (pdWr g) s.wr := by
  have wr : Covers (pdWr g) s.wr := (Covers.one h.outputWrite).pair (Covers.one h.workspaceWrite)
  refine ⟨Covers.append_left ?_ wr.right, wr⟩
  refine (Covers.one h.precomputationWrite).right.cons ((Covers.one (h.sources 1).read).cons
    ((Covers.one h.temporaryWrite).right.cons ?_))
  exact (Covers.one (show InRegions s.wr (State.addr g.stack) 24 from
    ⟨_, h.inner.writable, by simp [Region.Contains, frameBytes]⟩)).right

theorem pdWrites_sub {g : PrivGeometry} :
    ∀ r ∈ pdWr g, ∃ R ∈ bodyWrites g, r.Sub R := by
  intro r hr
  exact ⟨r, by simpa only [pdWr, bodyWrites, List.mem_cons, List.not_mem_nil, or_false] using
    (Or.inr (Or.inr hr) : r = g.innerRegion ∨ r = g.calleeRegion ∨ r ∈ pdWr g), fun _ hx => hx⟩

theorem pdWrites_slots {g : PrivGeometry} (h : g.Valid) :
    ∀ r ∈ pdWr g, (⟨off (State.addr g.stack) 64, 24⟩ : Region).Disjoint r := by
  have sub : (⟨off (State.addr g.stack) 64, 24⟩ : Region).Sub g.wholeStack :=
    fun x hx => h.innerSub x (Offset.sub_base _ (by decide : 64 + 24 ≤ frameBytes) x hx)
  intro r hr
  simp only [pdWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.stackOutput.sub_left sub
  · exact h.stackWorkspace.sub_left sub

def PdOut (g : PrivGeometry) (bs : Fin 8 → List Byte) (s t : State) : Prop :=
  ∀ nb : List Byte, nb.length = g.length →
    Spec.Rsa.publicPrecompute nb = some (Spec.Rsa.wordsAt s.mem (State.addr g.precomputation)
      (2 * Spec.Rsa.modulusWords g.length)) →
    Spec.Rsa.written t.mem (State.addr g.output) g.length (t.gpr .r0)
      (Spec.Rsa.publicOpChecked nb (bs 1) (Spec.Rsa.bytesAt s.mem (State.addr g.temporary) g.length))

theorem pd_call (v : CrtImpl) {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) (slots : PrivSlots g s.mem) (args : PdArgs g s) :
    WP isa (.call v.pdName v.pd) s fun t => PrivContext g bs t ∧ PrivSlots g t.mem ∧
      Frame (pdWr g ++ [g.calleeRegion]) s.mem t.mem ∧ Rest callClobbers s t ∧
      PdOut g bs s t := by
  refine WP.mono (private_call_ok h slots v.pdVerified v.pdStack (pdCall_pre h args)
    (pdCovers h).1 (pdCovers h).2 pdWrites_sub (pdWrites_slots h.valid)) ?_
  rintro t ⟨ht, slotsT, frame, rest, post⟩
  refine ⟨ht, slotsT, frame, rest, ?_⟩
  sig_post [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs, reduceClassify, Loc.val, State.addr] at post
  have sa := fun {j} (hj : j < 6) => pdArgs_stack h args hj
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega
  have efit : g.exponentLength < 2 ^ 32 := by have := h.valid.exponentFits; omega
  have pfit : 2 * Spec.Rsa.modulusWords g.length < 2 ^ 32 := by
    have := h.valid.maxLength; simp only [Spec.Rsa.modulusWords]; omega
  simp only [args.output, args.outputLength, args.precomputation, args.precomputationLength,
    sa (by decide : 0 < 6), sa (by decide : 1 < 6), sa (by decide : 2 < 6), pdArgument,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt kfit, Nat.mod_eq_of_lt efit, Nat.mod_eq_of_lt pfit] at post
  rw [BitVec.setWidth_append_eq_right] at post
  have eb : Spec.Rsa.bytesAt s.mem ((g.sources 1).setWidth 64) g.exponentLength = bs 1 := (h.sources 1).bytes
  rw [eb] at post
  exact post
end VG.Proof.Rsa.Arm

module

public import VerifiedGarbage.Proof.Rsa.X86.PrivPublicPre
public import VerifiedGarbage.Proof.Rsa.X86.PrivPrecomputeCall
public import VerifiedGarbage.Proof.Rsa.X86.PrivCallInput

/-! # Call verified public re-exponentiation while retaining the private intermediate -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86 VG.Proof.Mont.X86

theorem pdCovers {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State} (h : PrivContext g bs s) :
    Covers (pdRd g ++ pdWr g) (s.rd ++ s.wr) ∧ Covers (pdWr g) s.wr := by
  have wr : Covers (pdWr g) s.wr := (Covers.one h.outputWrite).cons
    ((Covers.one h.workspaceWrite).pair (Covers.one (h.outgoingWrite (by decide : 40 ≤ 72))))
  exact ⟨Covers.append_left ((Covers.one h.precomputationWrite).right.cons
    ((Covers.one (h.sources 1).read).pair (Covers.one h.temporaryWrite).right)) wr.right, wr⟩

theorem pdWrites_sub {g : PrivGeometry} :
    ∀ r ∈ pdWr g, ∃ R ∈ bodyWrites g, r.Sub R := by
  intro r hr
  simp only [pdWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨g.outputRegion, by simp [bodyWrites], fun _ hx => hx⟩
  · exact ⟨g.workspaceRegion, by simp [bodyWrites], fun _ hx => hx⟩
  · exact ⟨g.innerRegion, by simp [bodyWrites], Region.sub_prefix (by decide : 40 ≤ VG.Impl.Rsa.X86.PrivChecked.frameBytes)⟩

def PdOut (g : PrivGeometry) (bs : Fin 8 → List Byte) (s t : State) : Prop :=
  ∀ nb : List Byte, nb.length = g.length →
    Spec.Rsa.publicPrecompute nb = some (Spec.Rsa.wordsAt s.mem (byteAddr g.precomputation)
      (2 * Spec.Rsa.modulusWords g.length)) →
    Spec.Rsa.written t.mem (byteAddr g.output) g.length (t.gpr .eax)
      (Spec.Rsa.publicOpChecked nb (bs 1) (Spec.Rsa.bytesAt s.mem (byteAddr g.temporary) g.length))

theorem pd_call (v : CrtImpl) {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) (args : Arguments g (pdArgument g) 10 s) :
    WP isa (.call v.pdName v.pd) s fun t => PrivContext g bs t ∧
      Frame (pdWr g ++ [g.calleeRegion]) s.mem t.mem ∧ Keeps callClobbers s t ∧
      PdOut g bs s t := by
  refine WP.mono (private_call_ok h v.pdVerified v.pdStack v.pdNoSp (pdCall_pre h args)
    (pdCovers h).1 (pdCovers h).2 pdWrites_sub) ?_
  rintro t ⟨ht, frame, rest, u, M, G, post⟩
  refine ⟨ht, frame, rest, ?_⟩
  sig_post [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argSlots, argVal, argBytes] at post
  have sa := fun {j} (hj : j < 10) => pdArgs_values h args hj
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega
  have efit : g.exponentLength < 2 ^ 32 := by have := h.valid.exponentFits; omega
  have pfit : 2 * Spec.Rsa.modulusWords g.length < 2 ^ 32 := by
    have := h.valid.maxLength; simp only [Spec.Rsa.modulusWords]; omega
  simp only [sa (by decide : 0 < 10), sa (by decide : 1 < 10), sa (by decide : 2 < 10),
    sa (by decide : 3 < 10), sa (by decide : 4 < 10), sa (by decide : 5 < 10),
    sa (by decide : 6 < 10), pdArgument,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt kfit, Nat.mod_eq_of_lt efit, Nat.mod_eq_of_lt pfit] at post
  rw [BitVec.setWidth_append_eq_right, M, G .eax (by decide)] at post
  change ∀ nb : List Byte, nb.length = g.length →
    Spec.Rsa.publicPrecompute nb = some (Spec.Rsa.wordsAt s.callEntry.mem (byteAddr g.precomputation)
      (2 * Spec.Rsa.modulusWords g.length)) →
    Spec.Rsa.written t.mem (byteAddr g.output) g.length (t.gpr .eax)
      (Spec.Rsa.publicOpChecked nb
        (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 1)) g.exponentLength)
        (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr g.temporary) g.length)) at post
  have EB : Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 1)) g.exponentLength = bs 1 := h.callBytes 1
  rw [h.callPrecomputation, h.callTemporary, EB] at post
  exact post

end VG.Proof.Rsa.X86.PrivChecked

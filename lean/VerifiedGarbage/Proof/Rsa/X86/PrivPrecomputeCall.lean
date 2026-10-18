module

public import VerifiedGarbage.Proof.Rsa.X86.PrivPrecomputePre
public import VerifiedGarbage.Proof.Rsa.X86.PrivCrtCall

/-! # Call the verified public precomputation without changing the private intermediate -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86 VG.Proof.Mont.X86

theorem PrivContext.precomputationWrite {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) : InRegions s.wr (byteAddr g.precomputation) (16 * Spec.Rsa.modulusWords g.length) := by
  rw [PrivGeometry.precomputation, h.valid.offsetAddr (by decide)]
  exact ⟨_, h.inner.writable, Offset.contains_base _
    (by have := h.valid.maxLength; simp only [precomputeOffset, VG.Impl.Rsa.X86.PrivChecked.frameBytes, Spec.Rsa.modulusWords]; omega) (by decide : precomputeOffset < 2 ^ 64)⟩

theorem pcCovers {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State} (h : PrivContext g bs s) :
    Covers (pcRd g ++ pcWr g) (s.rd ++ s.wr) ∧ Covers (pcWr g) s.wr := by
  have wr : Covers (pcWr g) s.wr := (Covers.one h.precomputationWrite).cons
    ((Covers.one h.workspaceWrite).pair (Covers.one (h.outgoingWrite (by decide : 24 ≤ 72))))
  exact ⟨Covers.append_left (Covers.one (h.sources 0).read) wr.right, wr⟩

theorem pcWrites_sub {g : PrivGeometry} (h : g.Valid) :
    ∀ r ∈ pcWr g, ∃ R ∈ bodyWrites g, r.Sub R := by
  intro r hr
  simp only [pcWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · refine ⟨g.innerRegion, by simp [bodyWrites], ?_⟩
    rw [PrivGeometry.precomputation, h.offsetAddr (by decide)]
    exact Offset.sub_base _ (by have := h.maxLength; simp only [precomputeOffset, VG.Impl.Rsa.X86.PrivChecked.frameBytes, Spec.Rsa.modulusWords]; omega)
  · exact ⟨g.workspaceRegion, by simp [bodyWrites], fun _ hx => hx⟩
  · exact ⟨g.innerRegion, by simp [bodyWrites], Region.sub_prefix (by decide : 24 ≤ VG.Impl.Rsa.X86.PrivChecked.frameBytes)⟩

def PcOut (g : PrivGeometry) (bs : Fin 8 → List Byte) (s : State) : Prop :=
  match Spec.Rsa.publicPrecompute (bs 0) with
  | some ws => s.gpr .eax = 1 ∧ Spec.Rsa.wordsAt s.mem (byteAddr g.precomputation) (2 * Spec.Rsa.modulusWords g.length) = ws
  | none => s.gpr .eax = 0 ∧ Spec.Rsa.wordsAt s.mem (byteAddr g.precomputation) (2 * Spec.Rsa.modulusWords g.length) =
      List.replicate (2 * Spec.Rsa.modulusWords g.length) 0

theorem pc_call (v : CrtImpl) {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) (args : Arguments g (pcArgument g) 6 s) :
    WP isa (.call v.pcName v.pc) s fun t => PrivContext g bs t ∧
      Frame (pcWr g ++ [g.calleeRegion]) s.mem t.mem ∧ Keeps callClobbers s t ∧
      PcOut g bs t := by
  refine WP.mono (private_call_ok h v.pcVerified v.pcStack v.pcNoSp (pcCall_pre h args)
    (pcCovers h).1 (pcCovers h).2 (pcWrites_sub h.valid)) ?_
  rintro t ⟨ht, frame, rest, u, M, G, post⟩
  refine ⟨ht, frame, rest, ?_⟩
  sig_post [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argSlots, argVal, argBytes] at post
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega
  have pfit : 2 * Spec.Rsa.modulusWords g.length < 2 ^ 32 := by
    have := h.valid.maxLength; simp only [Spec.Rsa.modulusWords]; omega
  have sa := fun {j} (hj : j < 6) => pcArgs_values h args hj
  simp only [sa (by decide : 0 < 6), sa (by decide : 1 < 6), sa (by decide : 2 < 6),
    sa (by decide : 3 < 6), pcArgument, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt kfit, Nat.mod_eq_of_lt pfit] at post
  rw [BitVec.setWidth_append_eq_right, M, G .eax (by decide)] at post
  have nb : Spec.Rsa.bytesAt s.callEntry.mem ((g.sources 0).setWidth 64) g.length = bs 0 := h.callBytes 0
  simp only [State.callEntry_mem] at nb
  rw [nb] at post
  exact post
end VG.Proof.Rsa.X86.PrivChecked

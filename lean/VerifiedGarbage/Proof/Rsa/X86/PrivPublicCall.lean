module

public import VerifiedGarbage.Proof.Rsa.X86.PrivPublicPre
public import VerifiedGarbage.Proof.Rsa.X86.PrivCrtCall
import VerifiedGarbage.Proof.Rsa.X86.PrivCallInput
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.X86.PrivPrecomputePre
import VerifiedGarbage.Proof.Rsa.X86.PrivRegions
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `Rsa.X86.PrivPrecomputeCall`, which this module and modules that import it used -/

section

/-! # Call the verified public precomputation without changing the private intermediate -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86 VG.Proof.Mont.X86

theorem PrivContext.precomputationWrite {g : PrivGeometry} {bs : Fin 8 → List Byte} {s : State}
    (h : PrivContext g bs s) : InRegions s.wr (byteAddr g.precomputation) (16 * Spec.Rsa.modulusWords g.length) := by
  rw [PrivGeometry.precomputation, h.valid.offsetAddr (by decide)]
  exact ⟨_, h.inner.writable, Offset.contains_base _
    (by have := h.valid.maxLength; simp only [precomputeOffset, VG.Impl.Rsa.X86.PrivChecked.frameBytes, Spec.Rsa.modulusWords]; omega_using [this]) (by decide : precomputeOffset < 2 ^ 64)⟩

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
    exact Offset.sub_base _ (by have := h.maxLength; simp only [precomputeOffset, VG.Impl.Rsa.X86.PrivChecked.frameBytes, Spec.Rsa.modulusWords]; omega_using [this])
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
  refine WP.mono (private_call_ok h v.pcVerified (Nat.le_trans v.pcStack (by decide)) v.pcNoSp (pcCall_pre h args)
    (pcCovers h).1 (pcCovers h).2 (pcWrites_sub h.valid)) ?_
  rintro t ⟨ht, frame, rest, u, M, G, post⟩
  refine ⟨ht, frame, rest, ?_⟩
  sig_post [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argSlots, argVal, argBytes] at post
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega_using [this]
  have pfit : 2 * Spec.Rsa.modulusWords g.length < 2 ^ 32 := by
    have := h.valid.maxLength; simp only [Spec.Rsa.modulusWords]; omega_using [kfit]
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

end

end

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
  refine WP.mono (private_call_ok h v.pdVerified (Nat.le_trans v.pdStack (by decide)) v.pdNoSp (pdCall_pre h args)
    (pdCovers h).1 (pdCovers h).2 pdWrites_sub) ?_
  rintro t ⟨ht, frame, rest, u, M, G, post⟩
  refine ⟨ht, frame, rest, ?_⟩
  sig_post [Proof.Rsa.publicPrecomputedCheckedContract, Proof.Rsa.publicPrecomputedSig, abi, argSlots, argVal, argBytes] at post
  have sa := fun {j} (hj : j < 10) => pdArgs_values h args hj
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega_using [this]
  have efit : g.exponentLength < 2 ^ 32 := by have := h.valid.exponentFits; omega_using [kfit, this]
  have pfit : 2 * Spec.Rsa.modulusWords g.length < 2 ^ 32 := by
    have := h.valid.maxLength; simp only [Spec.Rsa.modulusWords]; omega_using [kfit]
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

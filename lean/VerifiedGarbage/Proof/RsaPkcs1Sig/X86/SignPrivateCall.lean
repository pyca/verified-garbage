module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignPrivatePre
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignCall
public import VerifiedGarbage.Proof.Rsa.X86.PrivVerified

/-! # Checked private RSA returns the signature of the exact local encoding -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl privCode stackBytes)

def privName (v : CrtImpl) : String := Spec.Rsa.privateCheckedApi.name ++ v.suffix

theorem privateCovers {g : Geometry} {bs : Fin 8 → List Byte} {s : State} (h : Context g bs s) :
    Covers (privateRd g ++ privateWr g) (s.rd ++ s.wr) ∧ Covers (privateWr g) s.wr := by
  have wr : Covers (privateWr g) s.wr := (Covers.one h.outputWrite).cons
    ((Covers.one h.workspaceWrite).pair (Covers.one h.outgoingWrite))
  have tmp : InRegions (s.rd ++ s.wr) (byteAddr g.temporary) g.length := by
    obtain ⟨r, hr, hc⟩ := h.temporaryWrite
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine ⟨Covers.append_left ?_ wr.right, wr⟩
  exact (Covers.one (h.sources 0).read).cons ((Covers.one (h.sources 1).read).cons
    ((Covers.one tmp).cons ((Covers.one (h.sources 3).read).cons ((Covers.one (h.sources 4).read).cons
    ((Covers.one (h.sources 5).read).cons ((Covers.one (h.sources 6).read).pair (Covers.one (h.sources 7).read)))))))

theorem privateWrites_sub {g : Geometry} {bs : Fin 8 → List Byte} {s : State} (h : Context g bs s) :
    ∀ r ∈ privateWr g, ∃ R ∈ bodyWrites g, r.Sub R := by
  intro r hr
  simp only [privateWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩
  · exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩
  · exact ⟨_, by simp [bodyWrites], h.outgoingSub⟩

theorem Context.callFrame {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : Context g bs s) : Frame [g.calleeRegion] s.mem s.callEntry.mem := by
  rw [State.callEntry_mem, h.sp]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (VG.X86.below_top (by decide : 4 ≤ calleeBytes) h.valid.stackLow (by decide : 4 ≤ 4))

theorem Context.callBytes {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : Context g bs s) (i : Fin 8) :
    Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources i)) (g.sourceLength i) = bs i := by
  exact (VG.Proof.Rsa.rsa_bytes_frame h.callFrame (by have := (h.sources i).fits; omega)
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr
        exact ((h.valid.stackSources i).sub_left h.valid.calleeSub).symm)).trans (h.sources i).bytes

theorem Context.callTemporary {g : Geometry} {bs : Fin 8 → List Byte} {s : State}
    (h : Context g bs s) :
    Spec.Rsa.bytesAt s.callEntry.mem (byteAddr g.temporary) g.length =
      Spec.Rsa.bytesAt s.mem (byteAddr g.temporary) g.length := by
  exact VG.Proof.Rsa.rsa_bytes_frame h.callFrame (by have := h.valid.maxLength; omega)
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr
        exact (h.valid.calleeInner.sub_right h.temporarySub).symm)

def PrivateOut (g : Geometry) (bs : Fin 8 → List Byte) (em : List Byte) (s : State) : Prop :=
  Spec.Rsa.writtenOutcome s.mem (byteAddr g.output) g.length (s.gpr .eax)
    (Spec.Rsa.privateChecked (bs 0) (bs 1) em (bs 3) (bs 4) (bs 5) (bs 6) (bs 7))

theorem private_call (v : CrtImpl) {g : Geometry} {bs : Fin 8 → List Byte} {s : State} {em : List Byte}
    (h : Context g bs s) (a : PrivateArgs g s)
    (bytes : Spec.Rsa.bytesAt s.mem (byteAddr g.temporary) g.length = em) :
    WP isa (.call (privName v) (privCode v)) s fun t => Context g bs t ∧
      Frame (privateWr g ++ [g.calleeRegion]) s.mem t.mem ∧ Keeps callClobbers s t ∧ PrivateOut g bs em t := by
  refine WP.mono (private_call_ok h (VG.Proof.Rsa.X86.PrivChecked.code_verified v)
    (VG.Proof.Rsa.X86.PrivChecked.code_stack v) (VG.Proof.Rsa.X86.PrivChecked.privateCode_noSp v)
    (privateCall_pre h a) (privateCovers h).1 (privateCovers h).2 (privateWrites_sub h)) ?_
  rintro t ⟨ht, F, K, u, M, G, post⟩
  refine ⟨ht, F, K, ?_⟩
  sig_post [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, abi, argSlots, argVal, argBytes] at post
  have sa := fun {j} (hj : j < 20) => privateArgs_values h a hj
  have kfit : g.length < 2 ^ 32 := by have := h.valid.maxLength; omega
  have efit : g.exponentLength < 2 ^ 32 := by have := h.valid.exponentFits; omega
  have pfit : g.pLength < 2 ^ 32 := by have := h.valid.pFits; omega
  have qfit : g.qLength < 2 ^ 32 := by have := h.valid.qFits; omega
  simp only [sa (by decide : 0 < 20), sa (by decide : 2 < 20), sa (by decide : 3 < 20),
    sa (by decide : 4 < 20), sa (by decide : 5 < 20), sa (by decide : 6 < 20),
    sa (by decide : 8 < 20), sa (by decide : 9 < 20), sa (by decide : 10 < 20), sa (by decide : 11 < 20),
    sa (by decide : 12 < 20), sa (by decide : 14 < 20),
    sa (by decide : 16 < 20), privateArgument, Geometry.argument,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, ite_true, ite_false, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt kfit, Nat.mod_eq_of_lt efit, Nat.mod_eq_of_lt pfit, Nat.mod_eq_of_lt qfit] at post
  rw [BitVec.setWidth_append_eq_right, M, G .eax (by decide)] at post
  change Spec.Rsa.writtenOutcome t.mem (byteAddr g.output) g.length (t.gpr .eax)
    (Spec.Rsa.privateChecked
      (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 0)) (g.sourceLength 0))
      (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 1)) (g.sourceLength 1))
      (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr g.temporary) g.length)
      (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 3)) (g.sourceLength 3))
      (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 4)) (g.sourceLength 4))
      (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 5)) (g.sourceLength 5))
      (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 6)) (g.sourceLength 6))
      (Spec.Rsa.bytesAt s.callEntry.mem (byteAddr (g.sources 7)) (g.sourceLength 7))) at post
  rw [h.callBytes 0, h.callBytes 1, h.callTemporary, bytes, h.callBytes 3, h.callBytes 4,
    h.callBytes 5, h.callBytes 6, h.callBytes 7] at post
  exact post

end VG.Proof.RsaPkcs1Sig.X86.Sgn

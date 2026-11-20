module

public import VerifiedGarbage.Proof.Framework.X86.Scrub
public import VerifiedGarbage.Impl.Scrub.X86
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem

/-!
# What RSA's postconditions read of the memory on return (x86, 32-bit)

The lemmas from which RSA's functions on x86 prove that their
postconditions read the memory on return only within their buffers
(`X86.Scrub.PostOut`): `postOut_of_local_pre`, for a postcondition that does
so where the precondition holds, and the octets and words at an address,
which read only the bytes there (`bytesAt_of`, `wordsAt_of`); and that a
function followed by its cleanup writes `esp` only by its frames, as the
function does (`scrubF_all`), which a registration generic over a variant
states of its code.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.Scrub

open VG.X86 VG.X86.Scrub

/-! ## Reading memory only within the buffers -/

/-- `postOut_of_local`, for a postcondition that reads the memory on return
only within the buffers when the precondition holds. -/
theorem postOut_of_local_pre {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}
    (hl : ∀ vs m m₁ m₂ r, vs.length = (sig.words A.ptrBits).length →
      Curry.apply (sig.words A.ptrBits) pre vs m →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words A.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words A.ptrBits) post vs m m₂ r) :
    PostOut (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits) := by
  intro s u u' hs hp hm hr
  simp only [Sig.contract] at hs hp ⊢
  revert hs hp
  cases hargs : A.args ((sig.words A.ptrBits).map (·.bits A.ptrBits)) with
  | none => intro hs; exact hs.elim
  | some vals =>
    intro hs hp
    simp only at hs hp ⊢
    obtain ⟨-, hrd, hwr, -, -, -, hpre⟩ := hs
    have hpre' : Curry.apply (sig.words A.ptrBits) pre (vals s) (A.mem s) := by
      cases hal : A.alignsBufs
      · rw [hal] at hpre; exact hpre
      · rw [hal] at hpre; exact hpre.1
    rw [hA.ret, hA.mem, hA.mem] at hp ⊢
    rw [hA.mem] at hpre'
    rw [hr]
    refine hl (vals s) _ _ _ _ (by rw [hA.argsLen _ _ hargs s, List.length_map]) hpre' (fun b hb a ha => ?_) hp
    have hin : b.1 ∈ s.rd ++ s.wr := by
      cases hw : b.2
      · apply List.mem_append_left; apply hA.rdSub; rw [hrd]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          by simp [hw]⟩, rfl⟩
      · apply List.mem_append_right; rw [← hA.wr, hwr]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          hw⟩, rfl⟩
    exact (hm a ⟨b.1, hin, ha⟩).symm

/-- The byte `k` of a region of more than `k` bytes at `o`. -/
theorem contains_of {o : Addr} {k N : Nat} (hk : k < N) : Region.Contains ⟨o, N⟩ (o + BitVec.ofNat 64 k) 1 := by
  simp only [Region.Contains]
  rw [BitVec.add_comm o, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
  have := Nat.mod_le k (2 ^ 64)
  omega_using [hk]

/-- The `n` octets at `o` read the memory only within `⟨o, N * 1⟩`, `n ≤ N`. -/
theorem bytesAt_of {m₁ m₂ : Mem} {o : Addr} {n N : Nat}
    (h : ∀ a, Region.Contains ⟨o, N * 1⟩ a 1 → m₁ a = m₂ a) (hn : n ≤ N) :
    Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  exact (h _ (contains_of (by omega_using [this, hn]))).symm

/-- The `n` words at `o` read the memory only within `⟨o, N⟩`, `n * 8 ≤ N`. -/
theorem wordsAt_of {m₁ m₂ : Mem} {o : Addr} {n N : Nat}
    (h : ∀ a, Region.Contains ⟨o, N⟩ a 1 → m₁ a = m₂ a) (hN : n * 8 ≤ N := by omega) :
    Spec.Rsa.wordsAt m₂ o n = Spec.Rsa.wordsAt m₁ o n :=
  List.map_congr_left fun i hi => Mem.readW_congr fun t ht => by
    have := List.mem_range.mp hi
    rw [Offset.add_add]
    exact (h _ (contains_of (by simp only [Nat.reduceDiv] at ht; omega_using [hN, ht, this]))).symm

theorem written_of {m₁ m₂ : Mem} {o : Addr} {n : Nat} {r : BitVec 32} {v : Option (List Byte)}
    (e : Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n) (h : Spec.Rsa.written m₁ o n r v) :
    Spec.Rsa.written m₂ o n r v := by
  cases v <;> simpa only [Spec.Rsa.written, e] using h

/-- An argument word, as the function reads it (its low 32 bits), is at most
the word. -/
theorem toNat_sw_le (A : Abi isa) (hA : ScrubAbi A) (x : BitVec 64) : (x.setWidth A.ptrBits).toNat ≤ x.toNat := by
  rw [BitVec.toNat_setWidth, hA.ptrBits]
  exact Nat.mod_le _ _

theorem writtenOutcome_of {m₁ m₂ : Mem} {o : Addr} {n : Nat} {r : BitVec 32} {v : Spec.Rsa.Outcome}
    (e : Spec.Rsa.bytesAt m₂ o n = Spec.Rsa.bytesAt m₁ o n) (h : Spec.Rsa.writtenOutcome m₁ o n r v) :
    Spec.Rsa.writtenOutcome m₂ o n r v := by
  cases v <;> simpa only [Spec.Rsa.writtenOutcome, e] using h

/-! ## The cleanup keeps `esp` -/

/-- Code followed by its cleanup (`Impl.Scrub.X86.scrubF`) writes `esp` only
by its frames if the code does. -/
theorem scrubF_all {rb n : Nat} {c : Prog isa} (h : c.all (fun i => !isa.writesSp i) = true) :
    (Impl.Scrub.X86.scrubF rb n c).all (fun i => !isa.writesSp i) = true := by
  simp only [Impl.Scrub.X86.scrubF, Impl.Scrub.X86.wipeBelow, Code.all, h, zeroRegs_all, tail_all,
    Bool.true_and, Bool.and_true]
  exact wipe_all _

end VG.Proof.Rsa.X86.Scrub

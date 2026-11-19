module

public import VerifiedGarbage.Proof.Framework.PPC64LE.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Init
public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Frame
import VerifiedGarbage.Proof.AesOcb.Scratch
import VerifiedGarbage.Proof.Aes.ScrubLocal
import VerifiedGarbage.Proof.Framework.Lit

/-!
# AES-OCB on PPC64LE, without secret residue

`vg_aes_ocb_init`, `vg_aes_ocb_seal` and `vg_aes_ocb_open`, each followed by
`Impl.Scrub.PPC64LE.scrubTail` (`PPC64LE.Scrub.scrubOf`), which clears the
volatile registers they may write and the whole frame that holds their
working space, which they do not wipe themselves: 2592 bytes for `init`
(`withStackScratch`), the key schedule and its callees' working space among
it, and 2688 for `seal` and `open` (`withStackScratchArgs`), the offsets and
the working space of the block functions among it. Their postconditions
read the memory on return only within the key context, the data and the
tag, as on AArch64 (`Proof/AesOcb/AArch64/Frame.lean`): `init`'s for a key
of a length its precondition allows (`initPostOut_of_local_pre`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.PPC64LE.Scrub

open VG.PPC64LE VG.PPC64LE.Scrub VG.Proof.Aes.ScrubLocal

/-! ## Postconditions -/

/-- `postOut_of_local`, for a postcondition that reads the memory on return
only within the buffers when the precondition holds, as for RSA
(`Rsa.PPC64LE.Scrub.postOut_of_local_pre`, whose module this one does not
import). -/
theorem initPostOut_of_local_pre {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
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

theorem initOut (stack : Nat) :
    PostOut (Spec.Ocb.initContract PPC64LE.abi stack) (Spec.Ocb.initSig.retBits 64) :=
  initPostOut_of_local_pre (leak := none) ScrubAbi.plain (Proof.AesOcb.initPostOut_local _)

theorem sealOut (stack : Nat) :
    PostOut (Spec.Ocb.sealContract PPC64LE.abi stack) (Spec.Ocb.sealSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [cp, rd, np, nl, ap, al, dp, dl, tp, tl], _ =>
      simp only [Spec.Ocb.sealSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ocb.sealPost 64) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ocb.sealPost 64) _ m m₂ r
      dsimp only [Curry.apply, Spec.Ocb.sealPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hk
      rw [h key hk, bytesAt_of0 hb.2.2.2.1 (by simp), bytesAt_of0 hb.2.2.2.2 (by simp)]

theorem openOut (stack : Nat) :
    PostOut (Spec.Ocb.openContract PPC64LE.abi stack) (Spec.Ocb.openSig.retBits 64) :=
  postOut_of_local ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [cp, rd, np, nl, ap, al, dp, dl, tp, tl], _ =>
      simp only [Spec.Ocb.openSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq, Elem.size, Nat.mul_one] at hb
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ocb.openPost 64) _ m m₁ r at h
      change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr,
        ArgWord.int 64, ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int 64]
        (Spec.Ocb.openPost 64) _ m m₂ r
      dsimp only [Curry.apply, Spec.Ocb.openPost, ArgWord.ofRaw, IntTy.bits] at h ⊢
      intro key hk
      rw [bytesAt_of0 hb.2.2.2.1 (by simp)]
      exact h key hk

/-! ## The registrations -/

/-- `Spec.Ocb.initApi`. -/
def initReg : Registration Spec.Ocb.initApi PPC64LE.target :=
  scrubOf {
      code := Impl.StackScratch.PPC64LE.withStackScratch 2592 .r6 Impl.AesGcm.PPC64LE.init
      verified := Proof.AesOcb.PPC64LE.init_framed }
    2592 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v9, .v10, .v11, .v19]⟩
    (initOut _)
    (by dsimp only; lit_decide)

/-- `Spec.Ocb.sealApi`. -/
def sealReg : Registration Spec.Ocb.sealApi PPC64LE.target :=
  scrubOf {
      code := Impl.StackScratch.PPC64LE.withStackScratchArgs 2688 2 Impl.AesOcb.PPC64LE.«seal»
      verified := Proof.AesOcb.seal_keyed Proof.AesOcb.PPC64LE.seal_framed }
    2688 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v19]⟩
    (sealOut _)
    (by dsimp only; lit_decide)

/-- `Spec.Ocb.openApi`. -/
def openReg : Registration Spec.Ocb.openApi PPC64LE.target :=
  scrubOf {
      code := Impl.StackScratch.PPC64LE.withStackScratchArgs 2688 2 Impl.AesOcb.PPC64LE.«open»
      verified := Proof.AesOcb.open_keyed Proof.AesOcb.PPC64LE.open_framed }
    2688 ⟨true, true, [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12], false,
      [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v8, .v19]⟩
    (openOut _)
    (by dsimp only; lit_decide)

end VG.Proof.AesOcb.PPC64LE.Scrub

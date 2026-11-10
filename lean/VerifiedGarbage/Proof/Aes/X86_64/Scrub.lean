module

public import VerifiedGarbage.Spec.Aes.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
public import VerifiedGarbage.Proof.Aes.X86_64.Frame
import VerifiedGarbage.Proof.Aes.Scratch
import VerifiedGarbage.Proof.Aes.X86_64.Lit
meta import VerifiedGarbage.Spec.Aes.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.Scrub
meta import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
meta import VerifiedGarbage.Proof.Aes.X86_64.Frame
meta import VerifiedGarbage.Proof.Aes.Scratch
meta import VerifiedGarbage.Proof.Aes.X86_64.Lit

/-!
# The AES key expansion on x86-64, without secret residue

`vg_aes_expand_key` and `vg_aes_expand_key_aesni`, each followed by
`Impl.Scrub.X86_64.scrubTail` (`X86_64.Scrub.withScrub`), which clears the
registers and the granules of its stack that the residue analysis
(`X86_64.RTaint`) finds may hold secrets. Their postcondition reads the
memory on return only within the schedule (`Proof.Aes.expandKeyPostOut_local`).
-/

@[expose] public section

namespace VG.Proof.Aes.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub

/-- `postOut_of_local`, for a postcondition that reads the memory on return
only within the buffers when the precondition holds (as a key's length
bounds the key schedule it states). -/
theorem postOut_of_local_pre {sig : Sig}
    {pre : Curry (sig.words abi.ptrBits) (Mem → Prop)}
    {post : sig.Post abi.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words abi.ptrBits) (Mem → List Nat))}
    (hl : ∀ vs m m₁ m₂ r, vs.length = (sig.words abi.ptrBits).length →
      Curry.apply (sig.words abi.ptrBits) pre vs m →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words abi.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words abi.ptrBits) post vs m m₂ r) :
    PostOut (sig.contract abi pre post wa stack leak) (sig.retBits abi.ptrBits) := by
  intro s u u' hs hp hm hr
  simp only [Sig.contract] at hs hp ⊢
  revert hs hp
  cases hargs : abi.args ((sig.words abi.ptrBits).map (·.bits abi.ptrBits)) with
  | none => intro hs; exact hs.elim
  | some vals =>
    intro hs hp
    simp only at hs hp ⊢
    obtain ⟨-, hrd, hwr, -, -, -, hpre⟩ := hs
    rw [ScrubAbi.plain.ret, ScrubAbi.plain.mem, ScrubAbi.plain.mem] at hp ⊢
    rw [hr]
    refine hl (vals s) _ _ _ _ (by rw [ScrubAbi.plain.argsLen _ _ hargs s, List.length_map])
      (by rw [← ScrubAbi.plain.mem s]; exact hpre) (fun b hb a ha => ?_) hp
    have hin : b.1 ∈ s.rd ++ s.wr := by
      cases hw : b.2
      · apply List.mem_append_left; apply ScrubAbi.plain.rdSub; rw [hrd]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          by simp [hw]⟩, rfl⟩
      · apply List.mem_append_right; rw [← ScrubAbi.plain.wr, hwr]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          hw⟩, rfl⟩
    exact (hm a ⟨b.1, hin, ha⟩).symm

theorem expandKeyOut (stack : Nat) :
    PostOut (Spec.Aes.expandKeyContract X86_64.abi stack) (Spec.Aes.expandKeySig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain (Proof.Aes.expandKeyPostOut_local _)

/-- `vg_aes_expand_key`'s code. -/
abbrev expandKeyCode : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratchWiped 520 .rcx 64 Impl.Aes.X86_64.expandKey

def expandKeyKs : List Nat := keep_for% Spec.Aes.expandKeyApi.sig 520 expandKeyCode []

theorem expandKeyOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Aes.expandKeyApi.sig 520 []) expandKeyCode
      h).any (RScrub.resOkB · 520 expandKeyKs (Impl.Scrub.X86_64.chunks 520)) = true :=
  RScrub.Analysed.ok_of expandKeyKs (by taint_decide)

def expandKeyAesniKs : List Nat :=
  keep_for% Spec.Aes.expandKeyApi.sig 0 Impl.Aes.X86_64.AesNi.expandKey []

theorem expandKeyAesniOk : ∃ h : VG.Taint.Hint RTaint.FT,
    (VG.Taint.check RTaint.rtaint (RScrub.init Spec.Aes.expandKeyApi.sig 0 [])
      Impl.Aes.X86_64.AesNi.expandKey h).any
      (RScrub.resOkB · 0 expandKeyAesniKs (Impl.Scrub.X86_64.chunks 0)) = true :=
  RScrub.Analysed.ok_of expandKeyAesniKs (by taint_decide)

open VG.X86_64.RScrub in
/-- `vg_aes_expand_key`. -/
def expandKeyReg : Registration Spec.Aes.expandKeyApi X86_64.target :=
  withScrub {
    code := expandKeyCode
    stack := 520
    verified := Proof.Aes.X86_64.scalar_expandKey_framed }
    (expandKeyOut _) [] (pubOk_nil _) (some ⟨expandKeyKs, expandKeyOk⟩)

open VG.X86_64.RScrub in
/-- `vg_aes_expand_key_aesni`. -/
def expandKeyAesniReg : Registration Spec.Aes.expandKeyApi X86_64.target :=
  withScrub {
    suffix := "_aesni"
    code := Impl.Aes.X86_64.AesNi.expandKey
    verified := Proof.Aes.X86_64.AesNi.Key.expandKey3_verified }
    (expandKeyOut _) [] (pubOk_nil _) (some ⟨expandKeyAesniKs, expandKeyAesniOk⟩)

end VG.Proof.Aes.X86_64.Scrub

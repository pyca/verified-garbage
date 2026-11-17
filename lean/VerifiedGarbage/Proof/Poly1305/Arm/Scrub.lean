module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Poly1305.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Poly1305.Arm.Lit
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.Poly1305.Arm.Frame
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Poly1305.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# Streaming Poly1305 on ARMv7, without secret residue

`vg_poly1305_update` and `vg_poly1305_finalize`, with either arithmetic
(`update umaal`, `finalize umaal`), keep their working space in a frame.
Their postconditions read the memory on return only within the state and
`out` (`Arm.Scrub.PostOut`), so each is registered followed by a wipe of the
stack its contract reserves (`Arm.Scrub.scrubRegF`), and by instructions
that set the registers a callee may change and the flags to constants.
-/

@[expose] public section

namespace VG.Proof.Poly1305.Arm.Scrub

open VG VG.Arm VG.Arm.Scrub VG.Arm.FrameStack
open VG.Spec.Poly1305

private theorem agree_of {m₁ m₂ : Mem} {p : Addr} {n : Nat}
    (h : ∀ a, Region.Contains ⟨p, n⟩ a 1 → m₁ a = m₂ a) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact Offset.contains_base _ (by omega_using [hi]) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega_using [hi, hw]

/-- `update`'s postcondition reads the memory on return only within the state. -/
theorem updatePost_out (pb : Nat) : ∀ vs m m₁ m₂ r, vs.length = (updateSig.words pb).length →
    (∀ b ∈ Sig.bufs updateSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (updateSig.words pb) (updatePost pb) vs m m₁ r →
      Curry.apply (updateSig.words pb) (updatePost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 3) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨data, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨len, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [updateSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have hs := agree_of hb.1
  change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int pb]
    (updatePost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr, ArgWord.int pb]
    (updatePost pb) _ m m₂ r
  dsimp only [Curry.apply, updatePost, ArgWord.ofRaw] at h ⊢
  intro key msg hbuf hc
  exact Proof.Poly1305.buffered_congr (fun i hi => hs i (by omega_using [hi])) (h key msg hbuf hc)

/-- `finalize`'s postcondition reads the memory on return only within `out`. -/
theorem finalizePost_out (pb : Nat) : ∀ vs m m₁ m₂ r, vs.length = (finalizeSig.words pb).length →
    (∀ b ∈ Sig.bufs finalizeSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (finalizeSig.words pb) (finalizePost pb) vs m m₁ r →
      Curry.apply (finalizeSig.words pb) (finalizePost pb) vs m m₂ r := by
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨_, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨out, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain rfl := List.eq_nil_of_length_eq_zero hlen
  simp only [finalizeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, Elem.size, Nat.mul_one] at hb
  have ho := agree_of hb.2
  change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr] (finalizePost pb) _ m m₁ r at h
  change Curry.apply [ArgWord.addr, ArgWord.int 64, ArgWord.addr] (finalizePost pb) _ m m₂ r
  dsimp only [Curry.apply, finalizePost, ArgWord.ofRaw] at h ⊢
  intro key msg hbuf hc
  rw [← h key msg hbuf hc]
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => ho i (List.mem_range.mp hi)

theorem updateOut (stack : Nat) :
    PostOut (Spec.Poly1305.updateContract abi stack) (Spec.Poly1305.updateSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (updatePost_out _)

theorem finalizeOut (stack : Nat) :
    PostOut (Spec.Poly1305.finalizeContract abi stack) (Spec.Poly1305.finalizeSig.retBits 32) :=
  postOut_of_local (leak := none) ScrubAbi.plain (finalizePost_out _)

theorem frameOk_144 : FrameOk 144 := by decide

theorem update_armStack (umaal : Bool) :
    armStack (Impl.StackScratch.Arm.withStackScratch 144 2 (Impl.Poly1305.Arm.update umaal)) ≤ 144 := by
  cases umaal <;> lit_decide

theorem finalize_armStack (umaal : Bool) :
    armStack (Impl.StackScratch.Arm.withStackScratch 144 1 (Impl.Poly1305.Arm.finalize umaal)) ≤ 144 := by
  cases umaal <;> lit_decide

def updateReg (umaal : Bool) (suffix : String) : Registration Spec.Poly1305.updateApi target :=
  Arm.Scrub.scrubRegF {
      suffix := suffix
      code := Impl.StackScratch.Arm.withStackScratch 144 2 (Impl.Poly1305.Arm.update umaal)
      verified := update_framed }
    (update_armStack umaal) frameOk_144 (updateOut _) rfl

def finalizeReg (umaal : Bool) (suffix : String) : Registration Spec.Poly1305.finalizeApi target :=
  Arm.Scrub.scrubRegF {
      suffix := suffix
      code := Impl.StackScratch.Arm.withStackScratch 144 1 (Impl.Poly1305.Arm.finalize umaal)
      verified := finalize_framed }
    (finalize_armStack umaal) frameOk_144 (finalizeOut _) rfl

end VG.Proof.Poly1305.Arm.Scrub

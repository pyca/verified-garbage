module

public import VerifiedGarbage.Spec.Cmac.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# Streaming AES-CMAC on x86-64, without secret residue

`vg_cmac_aes_finish` over an implementation of `vg_aes_ctr32` that needs no
working space (`Aes.X86_64.Ctr32Impl.free`), in a frame of only the 16
bytes of `vg_cmac_aes_finalize`'s counter block (`finishF_framed`), followed
by `Impl.Scrub.X86_64.scrubTail` (`X86_64.Scrub.withScrub`) where the
implementation gives the residue analysis of the instance
(`Aes.X86_64.Ctr32Impl.cmacFinishRes`). Over the others, as before, in a
frame of 2.3 KB, of which the analysis cannot tell what may hold secrets.
Its postcondition reads the memory on return only within the MAC
(`X86_64.Scrub.PostOut`).
-/

@[expose] public section

namespace VG.Proof.CmacAes.Stream.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub

/-! ## Locality -/

section

variable {m₁ m₂ : Mem} {p : Addr} {L : Nat}

theorem agree_le (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {n : Nat} (hn : n ≤ L) :
    ∀ i < n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i) := by
  intro i hi
  refine (h _ ?_).symm
  by_cases hw : i < 2 ^ 64
  · exact VG.Offset.contains_base _ (by omega) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega

theorem bytesAt_of (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {d n : Nat} (hn : d + n ≤ L) :
    Spec.Aes.bytesAt m₂ (p + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt m₁ (p + BitVec.ofNat 64 d) n := by
  simp only [Spec.Aes.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  rw [VG.Offset.add_add]
  exact agree_le h hn _ (by omega)

theorem bytesAt_of0 (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {n : Nat} (hn : n ≤ L) :
    Spec.Aes.bytesAt m₂ p n = Spec.Aes.bytesAt m₁ p n := by
  have := bytesAt_of h (d := 0) (n := n) (by omega)
  simpa using this

end

/-! ## Postconditions -/

theorem finishOut (stack : Nat) :
    PostOut (Spec.Cmac.aesFinishContract X86_64.abi stack) (Spec.Cmac.aesFinishSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [st, rd, ct, out], _ =>
      simp only [Spec.Cmac.aesFinishSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      intro key msg hr hro hc hlt
      show Spec.Aes.bytesAt m₂ out 16 = _
      rw [bytesAt_of0 hb.2 (by decide)]
      exact h key msg hr hro hc hlt

/-! ## The registration -/

open VG.X86_64.RScrub
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- `vg_cmac_aes_finish` over `v`: with no working space for an
implementation that needs none, and then without secret residue where the
analysis handles it. -/
def finishReg (v : Ctr32Impl) : Registration Spec.Cmac.aesFinishApi X86_64.target :=
  match v.free with
  | some f =>
    withScrub {
      suffix := v.suffix
      code := Impl.StackScratch.X86_64.withStackScratch 24 .r8 (Impl.CmacAes.Stream.X86_64.finishF v.callee v.suffix)
      stack := 40
      verified := Proof.CmacAes.Stream.X86_64.finishF_framed v f
      spSafe := VG.X86_64.withStackScratch_spSafe_of (Proof.CmacAes.Stream.X86_64.finishF_spSafe v) }
      (finishOut _) [] (pubOk_nil _) v.cmacFinishRes
  | none => {
      suffix := v.suffix
      code := Impl.StackScratch.X86_64.withStackScratch 2312 .r8 (Impl.CmacAes.Stream.X86_64.finish v.callee v.suffix)
      stack := 2328
      verified := Proof.CmacAes.Stream.X86_64.finish_framed v
      spSafe := VG.X86_64.withStackScratch_spSafe_of (Proof.CmacAes.Stream.X86_64.finish_spSafe v) }

end VG.Proof.CmacAes.Stream.X86_64.Scrub

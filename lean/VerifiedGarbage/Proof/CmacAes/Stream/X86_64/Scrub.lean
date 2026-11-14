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
(`Aes.X86_64.Ctr32Impl.cmacFinishRes`). Over the bitsliced AES, its frame of
2.3 KB, the working space it writes, is not wiped: that costs too much at
small inputs. Its postcondition reads the memory on return
only within the MAC (`X86_64.Scrub.PostOut`).

`vg_cmac_aes_init` over such an implementation, in a frame of only the 152
bytes it and its calls write (`initF_framed`), which `X86_64.Scrub.withScrubAll`
wipes whole on return; over the bitsliced AES, its frame of 2.3 KB is not
wiped. Its postcondition reads the memory on return only within the state
(`initOut`).

`vg_cmac_aes_absorb` over an implementation of `vg_cmac_aes_update` that
needs no working space (`UpdateFree`), in a frame of only the 48 bytes of
the registers it saves (`absorbF_framed`), which `X86_64.Scrub.withScrubAll`
wipes whole on return; over the bitsliced AES, its frame of 2.3 KB is not
wiped. Its postcondition reads the memory on return only within the state
(`absorbOut`).
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
  · exact VG.Offset.contains_base _ (by omega_using [hn, hi]) hw
  · simp only [Region.Contains]
    have := (p + BitVec.ofNat 64 i - p).isLt
    omega_using [hn, hi, hw]

theorem bytesAt_of (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {d n : Nat} (hn : d + n ≤ L) :
    Spec.Aes.bytesAt m₂ (p + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt m₁ (p + BitVec.ofNat 64 d) n := by
  simp only [Spec.Aes.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have := List.mem_range.mp hi
  rw [VG.Offset.add_add]
  exact agree_le h hn _ (by omega_using [this])

theorem bytesAt_of0 (h : ∀ a, Region.Contains ⟨p, L⟩ a 1 → m₁ a = m₂ a) {n : Nat} (hn : n ≤ L) :
    Spec.Aes.bytesAt m₂ p n = Spec.Aes.bytesAt m₁ p n := by
  have := bytesAt_of h (d := 0) (n := n) (by omega_using [hn])
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

theorem initOut (stack : Nat) :
    PostOut (Spec.Cmac.aesInitContract X86_64.abi stack) (Spec.Cmac.aesInitSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [st, key, kl], _ =>
      simp only [Spec.Cmac.aesInitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      exact Proof.CmacAes.Stream.repr_congr_304 (agree_le hb.1 (by decide)) h

theorem absorbOut (stack : Nat) :
    PostOut (Spec.Cmac.aesAbsorbContract X86_64.abi stack) (Spec.Cmac.aesAbsorbSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [st, rd, ct, dt, ln], _ =>
      simp only [Spec.Cmac.aesAbsorbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      intro key msg hr hro hc hlt
      exact Proof.CmacAes.Stream.repr_congr_304 (agree_le hb.1 (by decide)) (h key msg hr hro hc hlt)

/-! ## The registration -/

open VG.X86_64.RScrub
open VG.Proof.Aes.X86_64 (Ctr32Impl)
open VG.Proof.CmacAes.Stream.X86_64 (ekF)
open VG.Proof.CmacAes.X86_64 (UpdateImpl)

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

/-- `vg_cmac_aes_init` over `v`: with no working space for an implementation
that needs none, then without secret residue, its frame of 184 bytes wiped
whole (`withScrubAll`). -/
def initReg (v : Ctr32Impl) : Registration Spec.Cmac.aesInitApi X86_64.target :=
  match v.free with
  | some f =>
    withScrubAll {
      suffix := v.suffix
      code := Impl.StackScratch.X86_64.withStackScratch 168 .rcx
        (Impl.CmacAes.Stream.X86_64.initF ekF v.callee v.suffix)
      stack := 184
      verified := Proof.CmacAes.Stream.X86_64.initF_framed v f
      spSafe := VG.X86_64.withStackScratch_spSafe_of (Proof.CmacAes.Stream.X86_64.initF_spSafe v) }
      (initOut _)
  | none => {
      suffix := v.suffix
      code := Impl.StackScratch.X86_64.withStackScratch 2312 .rcx
        (Impl.CmacAes.Stream.X86_64.init v.expand v.callee v.suffix)
      stack := 2328
      verified := Proof.CmacAes.Stream.X86_64.init_framed v
      spSafe := VG.X86_64.withStackScratch_spSafe_of (Proof.CmacAes.Stream.X86_64.init_spSafe v) }

/-- `vg_cmac_aes_absorb` over `v`. Over an implementation that needs no
working space (`v.free`), in a frame of only the 48 bytes of the registers
it saves (`absorbF_framed`), wiped whole on return (`withScrubAll`, 72
bytes). Over the others, in its frame of 2.3 KB, as before: wiping that
much on every call costs too much at small inputs. -/
def absorbReg (v : UpdateImpl) : Registration Spec.Cmac.aesAbsorbApi X86_64.target :=
  match v.free with
  | some f =>
    withScrubAll {
      suffix := v.suffix
      code := Impl.StackScratch.X86_64.withStackScratch 56 .r9 (Impl.CmacAes.Stream.X86_64.absorbF v.callee)
      stack := 72
      verified := Proof.CmacAes.Stream.X86_64.absorbF_framed v f
      spSafe := VG.X86_64.withStackScratch_spSafe_of (Proof.CmacAes.Stream.X86_64.absorbF_spSafe v) }
      (absorbOut _)
  | none => {
      suffix := v.suffix
      code := Impl.StackScratch.X86_64.withStackScratch 2312 .r9 (Impl.CmacAes.Stream.X86_64.absorb v.callee)
      stack := 2328
      verified := Proof.CmacAes.Stream.X86_64.absorb_framed v
      spSafe := VG.X86_64.withStackScratch_spSafe_of (Proof.CmacAes.Stream.X86_64.absorb_spSafe v) }

end VG.Proof.CmacAes.Stream.X86_64.Scrub

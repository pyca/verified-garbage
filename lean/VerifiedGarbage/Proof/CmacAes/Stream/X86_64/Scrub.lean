module

public import VerifiedGarbage.Impl.CmacAes.Stream.X86_64.Fn
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall

public import VerifiedGarbage.Spec.Cmac.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubChunks
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
(`Aes.X86_64.Ctr32Impl.cmacFinishRes`). Over an implementation that needs
working space, its frame, the working space it writes, is wiped whole on
return, in chunks whose 16-byte stores are aligned
(`X86_64.RScrub.withScrubAllC`): over the bitsliced AES, which uses 1480
bytes of working space and is given them 512 bytes into the scratch buffer
(`Aes.X86_64.Ctr32Impl.small`), a frame of 1800 bytes for the working space
without its first 512 bytes (`finishS_framed`), wiped in the chunks
`[8, 1808]`; over any other, the frame of 2312 bytes for all of it
(`finish_framed`), wiped in the chunks `[8, 2320]`. Its postcondition reads
the memory on return only within the MAC (`X86_64.Scrub.PostOut`).

`vg_cmac_aes_init` over an implementation that needs no working space, in a
frame of only the 152 bytes it and its calls write (`initF_framed`), which
`X86_64.Scrub.withScrubAll` wipes whole on return; over the others, its
frame of 1800 bytes (`initS_framed`) or 2312 (`init_framed`), wiped whole as
`finish`'s. Its postcondition reads the memory on return only within the
state (`initOut`).

`vg_cmac_aes_absorb` over an implementation of `vg_cmac_aes_update` that
needs no working space (`UpdateFree`), in a frame of only the 48 bytes of
the registers it saves (`absorbF_framed`), which `X86_64.Scrub.withScrubAll`
wipes whole on return; over one that never touches the first 512 bytes of
its scratch buffer (`UpdateSmall`: the chaining by calls of the bitsliced
AES), its frame of 1800 bytes (`absorbS_framed`), and over any other, of
2312 (`absorb_framed`), wiped whole as `finish`'s. Its postcondition reads
the memory on return only within the state (`absorbOut`).
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

/-- `Spec.Cmac.aesFinishApi`'s function as emitted over `v`
(`Impl.CmacAes.Stream.X86_64.Fn.finish`), in the frame the working space of
`v` needs (`Ctr32Impl.space`), meets its contract in constant time and
returns without secret residue: its code is its code over a stub, with
`v`'s where it calls it (`Fill`), and its cleanup wipes its whole frame. -/
theorem finish_scrubbed (v : Ctr32Impl) :
    VerifiedScrubbed target (Impl.CmacAes.Stream.X86_64.Fn.finish v.level v.space v.callee v.suffix)
      (Spec.Cmac.aesFinishApi.contract X86_64.abi (Impl.CmacAes.Stream.X86_64.Fn.stack 40 v.space)) 0 := by
  have := v.side
  unfold Ctr32Impl.space
  rcases hf : v.free with _ | f
  · rcases hs : v.small with _ | g
    · exact verifiedScrubbedAllFill (api := Spec.Cmac.aesFinishApi) (ks := 0) (n := fun _ => 0)
        (a := Impl.StackScratch.X86_64.withStackScratch 2312 .r8
          (Impl.CmacAes.Stream.X86_64.finish ⟨"", .block [], v.callee.scrOff⟩ ""))
        { suffix := v.suffix
          code := Impl.StackScratch.X86_64.withStackScratch 2312 .r8 (Impl.CmacAes.Stream.X86_64.finish v.callee v.suffix)
          stack := 2328
          verified := Proof.CmacAes.Stream.X86_64.finish_framed v
          spSafe := VG.X86_64.withStackScratch_spSafe_of (Proof.CmacAes.Stream.X86_64.finish_spSafe v) }
        v.level (finishOut _) (by fill_calls) (Nat.zero_le _) (Nat.le_refl _)
        (ha := by rcases v.scrOk with h | h <;> rw [h] <;> lit_decide)
    · exact verifiedScrubbedAllFill (api := Spec.Cmac.aesFinishApi) (ks := 0) (n := fun _ => 0)
        (a := Impl.StackScratch.X86_64.withStackScratch 1800 .r8
          (Impl.CmacAes.Stream.X86_64.finishS ⟨"", .block [], v.callee.scrOff⟩ ""))
        { suffix := v.suffix
          code := Impl.StackScratch.X86_64.withStackScratch 1800 .r8 (Impl.CmacAes.Stream.X86_64.finishS v.callee v.suffix)
          stack := 1816
          verified := Proof.CmacAes.Stream.X86_64.finishS_framed v g
          spSafe := VG.X86_64.withStackScratch_spSafe_of (Proof.CmacAes.Stream.X86_64.finishS_spSafe v) }
        v.level (finishOut _) (by fill_calls) (Nat.zero_le _) (Nat.le_refl _)
        (ha := by rcases v.scrOk with h | h <;> rw [h] <;> lit_decide)
  · exact verifiedScrubbedAllFill (api := Spec.Cmac.aesFinishApi) (ks := 0) (n := fun _ => 0)
      (a := Impl.StackScratch.X86_64.withStackScratch 24 .r8
        (Impl.CmacAes.Stream.X86_64.finishF ⟨"", .block [], v.callee.scrOff⟩ ""))
      { suffix := v.suffix
        code := Impl.StackScratch.X86_64.withStackScratch 24 .r8 (Impl.CmacAes.Stream.X86_64.finishF v.callee v.suffix)
        stack := 40
        verified := Proof.CmacAes.Stream.X86_64.finishF_framed v f
        spSafe := VG.X86_64.withStackScratch_spSafe_of (Proof.CmacAes.Stream.X86_64.finishF_spSafe v) }
      v.level (finishOut _) (by fill_calls) (Nat.zero_le _) (Nat.le_refl _)
      (ha := by rcases v.scrOk with h | h <;> rw [h] <;> lit_decide)

theorem finish_spSafeFn (v : Ctr32Impl) :
    (Impl.CmacAes.Stream.X86_64.Fn.finish v.level v.space v.callee v.suffix).all
      (fun i => !VG.X86_64.isa.writesSp i) = true := by
  unfold Impl.CmacAes.Stream.X86_64.Fn.finish
  split
  · exact scrubKs_spSafe (VG.X86_64.withStackScratch_spSafe_of (Proof.CmacAes.Stream.X86_64.finishF_spSafe v))
  · exact scrubKs_spSafe (VG.X86_64.withStackScratch_spSafe_of (Proof.CmacAes.Stream.X86_64.finishS_spSafe v))
  · exact scrubKs_spSafe (VG.X86_64.withStackScratch_spSafe_of (Proof.CmacAes.Stream.X86_64.finish_spSafe v))

/-- `Spec.Cmac.aesInitApi`'s function as emitted over `v`
(`Impl.CmacAes.Stream.X86_64.Fn.init`), as `finish_scrubbed`. -/
theorem init_scrubbed (v : Ctr32Impl) :
    VerifiedScrubbed target (Impl.CmacAes.Stream.X86_64.Fn.init v.level v.space v.expand v.callee v.suffix)
      (Spec.Cmac.aesInitApi.contract X86_64.abi (Impl.CmacAes.Stream.X86_64.Fn.stack 184 v.space)) 0 := by
  have := v.side
  have := v.expandSide
  unfold Ctr32Impl.space
  rcases hf : v.free with _ | f
  · rcases hs : v.small with _ | g
    exact verifiedScrubbedAllFill (api := Spec.Cmac.aesInitApi) (ks := 0) (n := fun _ => 0)
        (a := Impl.StackScratch.X86_64.withStackScratch 2312 .rcx (Impl.CmacAes.Stream.X86_64.init ⟨"", .block []⟩ ⟨"", .block [], v.callee.scrOff⟩ ""))
        { suffix := v.suffix
          code := Impl.StackScratch.X86_64.withStackScratch 2312 .rcx (Impl.CmacAes.Stream.X86_64.init v.expand v.callee v.suffix)
          stack := 2328
          verified := Proof.CmacAes.Stream.X86_64.init_framed v
          spSafe := VG.X86_64.withStackScratch_spSafe_of (Proof.CmacAes.Stream.X86_64.init_spSafe v) }
        v.level (initOut _) (by fill_calls) (Nat.zero_le _) (Nat.le_refl _)
        (ha := by rcases v.scrOk with h | h <;> rw [h] <;> lit_decide)
    · exact verifiedScrubbedAllFill (api := Spec.Cmac.aesInitApi) (ks := 0) (n := fun _ => 0)
          (a := Impl.StackScratch.X86_64.withStackScratch 1800 .rcx (Impl.CmacAes.Stream.X86_64.initS ⟨"", .block []⟩ ⟨"", .block [], v.callee.scrOff⟩ ""))
          { suffix := v.suffix
            code := Impl.StackScratch.X86_64.withStackScratch 1800 .rcx (Impl.CmacAes.Stream.X86_64.initS v.expand v.callee v.suffix)
            stack := 1816
            verified := Proof.CmacAes.Stream.X86_64.initS_framed v g
            spSafe := VG.X86_64.withStackScratch_spSafe_of (Proof.CmacAes.Stream.X86_64.initS_spSafe v) }
          v.level (initOut _) (by fill_calls) (Nat.zero_le _) (Nat.le_refl _)
          (ha := by rcases v.scrOk with h | h <;> rw [h] <;> lit_decide)
  · exact verifiedScrubbedAllFill (api := Spec.Cmac.aesInitApi) (ks := 0) (n := fun _ => 0)
        (a := Impl.StackScratch.X86_64.withStackScratch 168 .rcx (Impl.CmacAes.Stream.X86_64.initF .aesni ⟨"", .block [], v.callee.scrOff⟩ ""))
        { suffix := v.suffix
          code := Impl.StackScratch.X86_64.withStackScratch 168 .rcx (Impl.CmacAes.Stream.X86_64.initF ekF v.callee v.suffix)
          stack := 184
          verified := Proof.CmacAes.Stream.X86_64.initF_framed v f
          spSafe := VG.X86_64.withStackScratch_spSafe_of (Proof.CmacAes.Stream.X86_64.initF_spSafe v) }
        v.level (initOut _) (by fill_calls) (Nat.zero_le _) (Nat.le_refl _)
        (ha := by rcases v.scrOk with h | h <;> rw [h] <;> lit_decide)

theorem init_spSafeFn (v : Ctr32Impl) :
    (Impl.CmacAes.Stream.X86_64.Fn.init v.level v.space v.expand v.callee v.suffix).all
      (fun i => !VG.X86_64.isa.writesSp i) = true := by
  unfold Impl.CmacAes.Stream.X86_64.Fn.init
  split
  · exact scrubKs_spSafe (VG.X86_64.withStackScratch_spSafe_of (Proof.CmacAes.Stream.X86_64.initF_spSafe v))
  · exact scrubKs_spSafe (VG.X86_64.withStackScratch_spSafe_of (Proof.CmacAes.Stream.X86_64.initS_spSafe v))
  · exact scrubKs_spSafe (VG.X86_64.withStackScratch_spSafe_of (Proof.CmacAes.Stream.X86_64.init_spSafe v))

/-- `Spec.Cmac.aesAbsorbApi`'s function as emitted over `v`
(`Impl.CmacAes.Stream.X86_64.Fn.absorb`), as `finish_scrubbed`. -/
theorem absorb_scrubbed (v : UpdateImpl) :
    VerifiedScrubbed target (Impl.CmacAes.Stream.X86_64.Fn.absorb v.level v.space v.callee)
      (Spec.Cmac.aesAbsorbApi.contract X86_64.abi (Impl.CmacAes.Stream.X86_64.Fn.stack 72 v.space)) 0 := by
  have := v.side
  unfold UpdateImpl.space
  rcases hf : v.free with _ | f
  · rcases hs : v.small with _ | g
    exact verifiedScrubbedAllFill (api := Spec.Cmac.aesAbsorbApi) (ks := 0) (n := fun _ => 8)
        (a := Impl.StackScratch.X86_64.withStackScratch 2312 .r9 (Impl.CmacAes.Stream.X86_64.absorb ⟨"", .block []⟩))
        { suffix := v.suffix
          code := Impl.StackScratch.X86_64.withStackScratch 2312 .r9 (Impl.CmacAes.Stream.X86_64.absorb v.callee)
          stack := 2328
          verified := Proof.CmacAes.Stream.X86_64.absorb_framed v
          spSafe := VG.X86_64.withStackScratch_spSafe_of (Proof.CmacAes.Stream.X86_64.absorb_spSafe v) }
        v.level (absorbOut _) (by fill_calls) (Nat.zero_le _) (Nat.le_refl _)
        (ha := by lit_decide)
    · exact verifiedScrubbedAllFill (api := Spec.Cmac.aesAbsorbApi) (ks := 0) (n := fun _ => 8)
          (a := Impl.StackScratch.X86_64.withStackScratch 1800 .r9 (Impl.CmacAes.Stream.X86_64.absorbS ⟨"", .block []⟩))
          { suffix := v.suffix
            code := Impl.StackScratch.X86_64.withStackScratch 1800 .r9 (Impl.CmacAes.Stream.X86_64.absorbS v.callee)
            stack := 1816
            verified := Proof.CmacAes.Stream.X86_64.absorbS_framed v g
            spSafe := VG.X86_64.withStackScratch_spSafe_of (Proof.CmacAes.Stream.X86_64.absorbS_spSafe v) }
          v.level (absorbOut _) (by fill_calls) (Nat.zero_le _) (Nat.le_refl _)
          (ha := by lit_decide)
  · exact verifiedScrubbedAllFill (api := Spec.Cmac.aesAbsorbApi) (ks := 0) (n := fun _ => 8)
        (a := Impl.StackScratch.X86_64.withStackScratch 56 .r9 (Impl.CmacAes.Stream.X86_64.absorbF ⟨"", .block []⟩))
        { suffix := v.suffix
          code := Impl.StackScratch.X86_64.withStackScratch 56 .r9 (Impl.CmacAes.Stream.X86_64.absorbF v.callee)
          stack := 72
          verified := Proof.CmacAes.Stream.X86_64.absorbF_framed v f
          spSafe := VG.X86_64.withStackScratch_spSafe_of (Proof.CmacAes.Stream.X86_64.absorbF_spSafe v) }
        v.level (absorbOut _) (by fill_calls) (Nat.zero_le _) (Nat.le_refl _)
        (ha := by lit_decide)

theorem absorb_spSafeFn (v : UpdateImpl) :
    (Impl.CmacAes.Stream.X86_64.Fn.absorb v.level v.space v.callee).all
      (fun i => !VG.X86_64.isa.writesSp i) = true := by
  unfold Impl.CmacAes.Stream.X86_64.Fn.absorb
  split
  · exact scrubKs_spSafe (VG.X86_64.withStackScratch_spSafe_of (Proof.CmacAes.Stream.X86_64.absorbF_spSafe v))
  · exact scrubKs_spSafe (VG.X86_64.withStackScratch_spSafe_of (Proof.CmacAes.Stream.X86_64.absorbS_spSafe v))
  · exact scrubKs_spSafe (VG.X86_64.withStackScratch_spSafe_of (Proof.CmacAes.Stream.X86_64.absorb_spSafe v))

end VG.Proof.CmacAes.Stream.X86_64.Scrub

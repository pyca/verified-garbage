import VerifiedGarbage.Spec.Sm3.Contract
import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.Sm3.Stream
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Streaming SM3 with its working space as an argument

`vg_sm3_update` and `vg_sm3_finalize` keep their working space in a frame of
their own (`Verified.stackScratch`), around code proved with the working
space as a last argument: `updateScratchContract n` and
`finalizeScratchContract n` are the shared contracts with a `scratch` buffer
of `n` words appended, whatever it holds (each target lays out its own).

On x86 and ARMv7, where the frame also holds a copy of the arguments passed
on the stack, that needs their postconditions to read the memory on entry
only within the function's buffers: the streaming state
(`Stream.repr_congr`) and the data (`Stream.bytesAt_congr`).
-/

namespace VG.Proof.Sm3

open VG.Spec.Sm3

/-- `vg_sm3_update` with `scratch: *mut [u64; n]`. -/
def updateScratchSig (n : Nat) : Sig where
  params := updateSig.params ++ [("scratch", .array true .u64 n)]

/-- `updatePost`, whatever `scratch` is. -/
def updateScratchContract {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  (updateScratchSig n).contract A
    (post := fun state count data len _scratch => updatePost A.ptrBits state count data len)
    (writeArgs := true) (stack := stack)

theorem updateScratchContract_eq {M : ISA} (A : Abi M) (n stack : Nat) :
    updateScratchContract A n stack = Sig.scratchContract A updateSig "scratch" .u64 n
      (Curry.const (fun _ => True) _) (updatePost A.ptrBits) true stack := rfl

/-- `vg_sm3_finalize` with `scratch: *mut [u64; n]`. -/
def finalizeScratchSig (n : Nat) : Sig where
  params := finalizeSig.params ++ [("scratch", .array true .u64 n)]

/-- `finalizePost`, whatever `scratch` is. -/
def finalizeScratchContract {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  (finalizeScratchSig n).contract A
    (post := fun state count out _scratch => finalizePost A.ptrBits state count out)
    (writeArgs := true) (stack := stack)

theorem finalizeScratchContract_eq {M : ISA} (A : Abi M) (n stack : Nat) :
    finalizeScratchContract A n stack = Sig.scratchContract A finalizeSig "scratch" .u64 n
      (Curry.const (fun _ => True) _) (finalizePost A.ptrBits) true stack := rfl

theorem updatePost_local (pb : Nat) : ∀ vs m₁ m₂ m' r, vs.length = (updateSig.words pb).length →
    (∀ b ∈ Sig.bufs updateSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (updateSig.words pb) (updatePost pb) vs m₁ m' r →
      Curry.apply (updateSig.words pb) (updatePost pb) vs m₂ m' r
  | [st, ct, dt, ln], m₁, m₂, m', r, _, hb, h => by
    simp only [updateSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    have hs : ∀ i < 96, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
      (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
    have hd : ∀ i < (ln.setWidth pb).toNat, m₂ (dt + BitVec.ofNat 64 i) = m₁ (dt + BitVec.ofNat 64 i) :=
      fun i hi => by
        have := Nat.mod_le ln.toNat (2 ^ pb)
        have := ln.isLt
        rw [BitVec.toNat_setWidth] at hi
        exact (hb.2 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
    intro msg hr hc
    rw [show bytesAt m₂ (ArgWord.addr.ofRaw dt) ((ArgWord.int pb).ofRaw ln).toNat =
      bytesAt m₁ dt (ln.setWidth pb).toNat from Stream.bytesAt_congr hd]
    exact h msg (Stream.repr_congr (fun i hi => (hs i hi).symm) hr) hc

theorem finalizePost_local (pb : Nat) :
    ∀ vs m₁ m₂ m' r, vs.length = (finalizeSig.words pb).length →
      (∀ b ∈ Sig.bufs finalizeSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (finalizeSig.words pb) (finalizePost pb) vs m₁ m' r →
        Curry.apply (finalizeSig.words pb) (finalizePost pb) vs m₂ m' r
  | [st, ct, ot], m₁, m₂, m', r, _, hb, h => by
    simp only [finalizeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hb
    have hs : ∀ i < 96, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
      (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega) (by omega))).symm
    intro msg hr hc
    exact h msg (Stream.repr_congr (fun i hi => (hs i hi).symm) hr) hc

end VG.Proof.Sm3

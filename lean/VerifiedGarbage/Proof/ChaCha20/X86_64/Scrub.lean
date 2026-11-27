module

public import VerifiedGarbage.Proof.ChaCha20.X86_64.Stream.ApplyCT
public import VerifiedGarbage.Proof.ChaCha20.Stream
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall
public import VerifiedGarbage.Impl.ChaCha20.X86_64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.ChaCha20.ScrubLocal

/-!
# ChaCha20's `apply` without secret residue (x86-64)

`vg_chacha20_apply`, for each implementation of `vg_chacha20_xor`, followed
by the clearing of every register it may write and of its whole stack
(`Impl.ChaCha20.X86_64.Fn.apply`), whose postcondition reads the memory on
return only within the state and the data (`applyOut`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64 VG.X86_64.RScrub VG.Spec.ChaCha20
open VG.Proof.ChaCha20.ScrubLocal
open VG.X86_64.Taint (byteAddr region)


theorem applyOut (stack : Nat) : PostOut (applyContract X86_64.abi stack) (applySig.retBits 64) := by
  unfold applyContract
  refine postOut_of_local ScrubAbi.plain ?_
  intro vs m m₁ m₂ r hlen hb h
  obtain ⟨st, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 2) hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨dt, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  replace hlen := Nat.succ.inj hlen
  obtain ⟨ln, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
  obtain rfl := List.eq_nil_of_length_eq_zero (Nat.succ.inj hlen)
  simp only [applySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hb
  have hs : ∀ i < 136, m₂ (st + BitVec.ofNat 64 i) = m₁ (st + BitVec.ofNat 64 i) := fun i hi =>
    (hb.1 _ (Offset.contains_base _ (by simp only [Elem.size]; omega_using [hi]) (by omega_using [hi]))).symm
  have hd : Spec.ChaCha20.bytesAt m₂ dt ln.toNat = Spec.ChaCha20.bytesAt m₁ dt ln.toNat := by
    simp only [Spec.ChaCha20.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have := List.mem_range.mp hi
    exact (hb.2 _ (Offset.contains_base _ (by simp only [Elem.size]; omega_using [this]) (by omega_using [this]))).symm
  obtain ⟨k, rs, -⟩ := stream_congr hs
  show keyAt m₂ st = _ ∧ _
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [k]; exact h1, ?_⟩
  have e64 : (ArgWord.int X86_64.abi.ptrBits).ofRaw ln = ln := BitVec.setWidth_eq ln
  rw [e64] at h2 ⊢
  split at h2 <;> split <;> rename_i h₁ h₂
  · obtain ⟨a, b, c⟩ := h2; exact ⟨a, hd.trans b, rs.trans c⟩
  · exact absurd h₁ h₂
  · exact absurd h₂ h₁
  · obtain ⟨a, b, c⟩ := h2; exact ⟨a, hd.trans b, rs.trans c⟩

/-- `Spec.ChaCha20.applyApi`'s function as emitted over `v`
(`Impl.ChaCha20.X86_64.Fn.apply`) meets its contract in constant time and
returns without secret residue: its code is its code over a stub, with
`v`'s where it calls it (`Fill`). -/
theorem apply_scrubbed (v : XorImpl) :
    VerifiedScrubbed target (Impl.ChaCha20.X86_64.Fn.apply v.level v.callee)
      (Spec.ChaCha20.applyApi.contract X86_64.abi 24) 32 :=
  verifiedScrubbedAllFill (api := Spec.ChaCha20.applyApi) (ks := 0) (n := fun _ => 16)
    (a := Impl.ChaCha20.X86_64.Stream.apply ⟨"", .block [], 0, 0, 0, false⟩)
    { suffix := v.suffix
      code := Impl.ChaCha20.X86_64.Stream.apply v.callee
      stack := 24
      verified := Proof.ChaCha20.X86_64.Stream.apply_verified v
      spSafe := Proof.ChaCha20.X86_64.Stream.apply_spSafe v }
    v.level (applyOut _) (by have := v.side; fill_calls) (Nat.zero_le _) (Nat.le_refl _)

theorem apply_spSafeFn (v : XorImpl) :
    (Impl.ChaCha20.X86_64.Fn.apply v.level v.callee).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (Proof.ChaCha20.X86_64.Stream.apply_spSafe v)

end VG.Proof.ChaCha20.X86_64.Scrub

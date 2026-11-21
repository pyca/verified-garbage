module

public import VerifiedGarbage.Proof.ChaCha20.X86.Stream.ApplyCT
public import VerifiedGarbage.Proof.ChaCha20.X86.Stream.Init
public import VerifiedGarbage.Proof.Framework.X86.ScrubCall
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Impl.ChaCha20.X86.Stream
import VerifiedGarbage.Proof.ChaCha20.ScrubLocal
import VerifiedGarbage.Proof.ChaCha20.X86.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.ChaCha20.X86.Stream.ApplyCT
meta import VerifiedGarbage.Proof.ChaCha20.X86.Stream.Init
meta import VerifiedGarbage.Proof.Framework.X86.ScrubCall
meta import VerifiedGarbage.Proof.Framework.X86.ScrubFn
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Impl.ChaCha20.X86.Stream
meta import VerifiedGarbage.Proof.ChaCha20.ScrubLocal
meta import VerifiedGarbage.Proof.ChaCha20.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# ChaCha20 on x86 (32-bit), without secret residue

`vg_chacha20_init` and `vg_chacha20_set_nonce` call nothing and have no
frame: as emitted (`Impl.ChaCha20.X86.Fn`) they clear the registers a callee
may change (`X86.Scrub.verifiedScrubbed`). `vg_chacha20_apply` calls
`vg_chacha20_block` and an implementation of `vg_chacha20_xor` (`XorImpl`):
as emitted it also zeroes the 32 bytes of stack that it and they use
(`X86.Scrub.verifiedScrubbedAll`), given that its postcondition reads the
memory on return only within the streaming state and the data (`applyOut`).

What the cleanup needs of `apply`'s code holds of every implementation
(`apply_scrub`): from its code with a stub for the implementation, a frame
of the implementation's 12 bytes around nothing (`holeStub 12`), which the
kernel evaluates here (`apply_side`), the implementation's own facts
(`XorImpl.scrub`, `XorImpl.stack`), and `FillB`, which `fillB_calls` proves
by walking only `apply`'s code.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86.Scrub

open VG.X86 VG.X86.Scrub VG.Spec.ChaCha20 VG.Proof.ChaCha20.ScrubLocal

/-! ## The postcondition -/

/-- `vg_chacha20_apply`'s postcondition reads the memory on return only
within the streaming state and the data. -/
theorem applyOut (stack : Nat) : PostOut (applyContract X86.abi stack) (applySig.retBits 32) := by
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
  have hle : ((ArgWord.int 32).ofRaw ln).toNat ≤ ln.toNat := by
    simp only [ArgWord.ofRaw, BitVec.toNat_setWidth]; exact Nat.mod_le _ _
  have hd : Spec.ChaCha20.bytesAt m₂ dt ((ArgWord.int 32).ofRaw ln).toNat =
      Spec.ChaCha20.bytesAt m₁ dt ((ArgWord.int 32).ofRaw ln).toNat := by
    simp only [Spec.ChaCha20.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    have hi : i < ln.toNat := Nat.lt_of_lt_of_le (List.mem_range.mp hi) hle
    exact (hb.2 _ (Offset.contains_base _ (by simp only [Elem.size]; omega_using [hi])
      (by omega_using [hi, ln.isLt]))).symm
  obtain ⟨k, rs, -⟩ := stream_congr hs
  show keyAt m₂ st = _ ∧ _
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [k]; exact h1, ?_⟩
  split at h2 <;> split <;> rename_i h₁ h₂
  · obtain ⟨a, b, c⟩ := h2; exact ⟨a, hd.trans b, rs.trans c⟩
  · exact absurd h₁ h₂
  · exact absurd h₂ h₁
  · obtain ⟨a, b, c⟩ := h2; exact ⟨a, hd.trans b, rs.trans c⟩

/-! ## What the cleanup needs of `apply`'s code -/

/-- An implementation of `vg_chacha20_xor` with no code: a frame of its 12
bytes of stack around nothing. -/
def stub : Impl.ChaCha20.X86.Callee := ⟨"", holeStub 12⟩

-- `apply`'s code, with the stub, as a literal for the kernel's evaluation.
materialize_code applyStub := Impl.ChaCha20.X86.Stream.apply stub

theorem apply_side : scrubFSide (Impl.ChaCha20.X86.Stream.apply stub) [] 32 = true := by lit_decide

/-- `scrubFSide` of `vg_chacha20_apply`, whatever the implementation. -/
theorem apply_scrub (v : XorImpl) : scrubFSide (Impl.ChaCha20.X86.Stream.apply v.callee) [] 32 = true := by
  have hc : calleeSide v.callee.code 12 = true := calleeSide_of_eq v.stack v.scrub
  exact scrubFSide_of_fillB (by fillB_calls) apply_side

/-! ## The functions as emitted -/

/-- `vg_chacha20_init`, as emitted. -/
theorem init_scrubbed : VerifiedScrubbed target Impl.ChaCha20.X86.Fn.init (initContract X86.abi) 0 :=
  verifiedScrubbed (api := initApi)
    { code := Impl.ChaCha20.X86.Stream.init
      verified := Proof.ChaCha20.X86.Stream.init_verified }

/-- `vg_chacha20_set_nonce`, as emitted. -/
theorem setNonce_scrubbed :
    VerifiedScrubbed target Impl.ChaCha20.X86.Fn.setNonce (setNonceContract X86.abi) 0 :=
  verifiedScrubbed (api := setNonceApi)
    { code := Impl.ChaCha20.X86.Stream.setNonce
      verified := Proof.ChaCha20.X86.Stream.setNonce_verified }

/-- `vg_chacha20_apply`, calling the implementation `v` of `vg_chacha20_xor`, as emitted. -/
theorem apply_scrubbed (v : XorImpl) :
    VerifiedScrubbed target (Impl.ChaCha20.X86.Fn.apply v.callee) (applyContract X86.abi 32) 32 :=
  verifiedScrubbedAll (api := applyApi)
    { suffix := v.suffix
      code := Impl.ChaCha20.X86.Stream.apply v.callee
      stack := 32
      verified := Proof.ChaCha20.X86.Stream.apply_verified v
      spSafe := Proof.ChaCha20.X86.Stream.apply_spSafe v }
    (applyOut _) (hs := apply_scrub v)

/-- `vg_chacha20_apply` as emitted never writes `esp` but by its frames. -/
theorem apply_spSafe (v : XorImpl) :
    (Impl.ChaCha20.X86.Fn.apply v.callee).all (fun i => !X86.isa.writesSp i) = true :=
  scrubAll_spSafe (Proof.ChaCha20.X86.Stream.apply_spSafe v)

end VG.Proof.ChaCha20.X86.Scrub

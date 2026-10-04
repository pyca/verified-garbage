import VerifiedGarbage.Proof.AesCcm.X86.TopCT

/-!
# AES-CCM on x86: `vg_aes_ccm_seal` is constant time

Untrusted: everything here is checked by Lean. From the public values (the
arguments and `esp`), the start, the MAC, the tag, counter mode and the exit
are each constant time (`seal_top_ct`); so is `seal` (`seal_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.Impl.AesCcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (restore)
open VG.Proof.AesGcm.X86 (CT w64 length_bytesAt)

theorem seal_top_ct (v : Ctr32Impl) {K W SP N A D : BitVec 32} {R nl al n tl : Nat} (z : State)
    (Tz : Top K W SP N A D R nl al n tl z) :
    CT (Top K W SP N A D R nl al n tl) («seal» v.callee v.suffix) := by
  have Ar := Tz.args
  have L := Ar.lay
  have h7' : ∀ m : Mem, 7 ≤ (bytesAt m (w64 N) nl).length := fun m => by rw [length_bytesAt]; exact Ar.h7
  have h13' : ∀ m : Mem, (bytesAt m (w64 N) nl).length ≤ 13 := fun m => by rw [length_bytesAt]; exact Ar.h13
  refine RelCT.assoc (CT.seq (J := fun s => ∃ s₀, Top K W SP N A D R nl al n tl s₀ ∧ Run s₀ K W SP N A D R nl al n tl s)
    (start_ct L Ar.h13) (fun s hs => WP.mono (start_ok hs.args hs.sp hs.a0 hs.a1 hs.a2 hs.a3 hs.a4 hs.a5 hs.a6 hs.a7
      hs.a8 hs.a9) fun _ St => ⟨s, hs, Run.of_started St⟩) ?_)
  -- The MAC.
  refine CT.seq (J := fun s => ∃ s₀, Top K W SP N A D R nl al n tl s₀ ∧ Run s₀ K W SP N A D R nl al n tl s)
    ((mac_ct v L Ar.rounds Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te Ar.al32 Ar.hn Ar.n32 (.inl rfl)).mono
      fun s ⟨_, T, h⟩ => h.mac_pre T.args)
    (fun s ⟨s₀, T, h⟩ => WP.mono (mac_ok v L h.env Ar.rounds (h.slots T.args) (length_bytesAt _ _ _) Ar.h7 Ar.h13
      Ar.t4 Ar.t16 Ar.te Ar.al32 Ar.hn Ar.n32 h.c0 (.inl rfl) (T.args.aad.of_eq h.rd h.wr)
      (T.args.data.of_eq h.rd h.wr)) fun _ A' => ⟨s₀, T, h.mac T.args (.inl rfl) A'⟩) ?_
  -- The tag.
  refine CT.seq (J := fun s => ∃ s₀, Top K W SP N A D R nl al n tl s₀ ∧ Run s₀ K W SP N A D R nl al n tl s)
    ((tag_ct v L Ar.rounds (.inl rfl)).mono fun s ⟨_, T, h⟩ => h.tag_pre T.args)
    (fun s ⟨s₀, T, h⟩ => WP.mono (tag_ok v L h.env Ar.rounds (h.slots T.args).ctx (h.slots T.args).rounds (h7' _)
      (h13' _) h.c0 (.inl rfl)) fun _ ⟨E, rd, wr, f, _⟩ => ⟨s₀, T, h.tag T.args (.inl rfl) E rd wr f⟩) ?_
  -- Counter mode.
  refine CT.seq (J := fun s => ∃ s₀, Top K W SP N A D R nl al n tl s₀ ∧ Run s₀ K W SP N A D R nl al n tl s)
    ((ctr_ct v L Ar.rounds Ar.n32).mono fun s ⟨_, T, h⟩ => h.ctr_pre T.args)
    (fun s ⟨s₀, T, h⟩ => by
      obtain ⟨E, hK, hRo, hDp, hlen, nonce, C⟩ := h.ctr_pre T.args
      exact WP.mono (ctr_ok v C E hK hRo hDp hlen) fun _ ⟨E', rd, wr, f, _⟩ => ⟨s₀, T, h.ctr T.args E' rd wr f⟩) ?_
  -- The exit.
  exact CT.taint [.ebp] (pin_ebp fun _ ⟨_, _, h⟩ => h.env.ebp) (by taint_decide)

theorem seal_ct (v : Ctr32Impl) : ConstantTime isa sealX86.pre sealX86.pub («seal» v.callee v.suffix) :=
  CT.constantTime pubOf (fun _ _ _ _ h => pubOf_eq h) fun p => by
    by_cases hex : ∃ s, sealX86.pre s ∧ pubOf s = p
    · obtain ⟨z, hz, hp⟩ := hex
      exact (seal_top_ct v z (top_of hz hp)).mono fun s hs => top_of hs.1 hs.2
    · intro s₁ _ _ _ _ _ h
      exact (hex ⟨s₁, h.1⟩).elim

end VG.Proof.AesCcm.X86

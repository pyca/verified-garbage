import VerifiedGarbage.Proof.AesCcm.X86.TopCT
import VerifiedGarbage.Proof.AesCcm.X86.Mask

/-!
# AES-CCM on x86: `vg_aes_ccm_seal` is constant time

Untrusted: everything here is checked by Lean. From the public values (the
arguments and `esp`), the start, the MAC, the tag, counter mode, the tag
copied out and the exit are each constant time (`seal_top_ct`); so is `seal`
(`seal_ct`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.Impl.AesCcm.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (restore)
open VG.Proof.AesGcm.X86 (CT w64 length_bytesAt)

/-- `seal` from its arguments: `Top`, with the tag writable. -/
structure SealTop (K W SP N A D T : BitVec 32) (R nl al n tl : Nat) (s : State) : Prop
    extends Top K W SP N A D T R nl al n tl s where
  tw : Covers [⟨w64 T, tl⟩] s.wr

theorem seal_top_of {s : State} (h : sealPre s) {p : BitVec 32 × (Nat → BitVec 32)} (hp : pubOf s = p) :
    SealTop (p.2 0) (p.2 10) p.1 (p.2 2) (p.2 4) (p.2 6) (p.2 8) (p.2 1).toNat (p.2 3).toNat (p.2 5).toNat
      (p.2 7).toNat (p.2 9).toNat s := by
  refine ⟨top_of (args_of_seal h) hp, ?_⟩
  subst hp
  simp only [pubOf, show (8 : Nat) < 11 from by decide, show (9 : Nat) < 11 from by decide, ↓reduceIte]
  exact tag_wr h

theorem seal_top_ct (v : Ctr32Impl) {K W SP N A D T : BitVec 32} {R nl al n tl : Nat} (z : State)
    (Tz : SealTop K W SP N A D T R nl al n tl z) :
    CT (SealTop K W SP N A D T R nl al n tl) («seal» v.callee v.suffix) := by
  have Ar := Tz.args
  have L := Ar.lay
  have h7' : ∀ m : Mem, 7 ≤ (bytesAt m (w64 N) nl).length := fun m => by rw [length_bytesAt]; exact Ar.h7
  have h13' : ∀ m : Mem, (bytesAt m (w64 N) nl).length ≤ 13 := fun m => by rw [length_bytesAt]; exact Ar.h13
  refine RelCT.assoc (CT.seq (J := fun s => ∃ s₀, SealTop K W SP N A D T R nl al n tl s₀ ∧ Run s₀ K W SP N A D T R nl al n tl s)
    ((start_ct L Ar.h13).mono fun s hs => hs.toTop) (fun s hs => WP.mono (start_ok hs.args hs.sp hs.a0 hs.a1 hs.a2 hs.a3 hs.a4 hs.a5 hs.a6 hs.a7
      hs.a8 hs.a9 hs.a10) fun _ St => ⟨s, hs, Run.of_started St⟩) ?_)
  -- The MAC.
  refine CT.seq (J := fun s => ∃ s₀, SealTop K W SP N A D T R nl al n tl s₀ ∧ Run s₀ K W SP N A D T R nl al n tl s)
    ((mac_ct v L Ar.rounds Ar.h7 Ar.h13 Ar.t4 Ar.t16 Ar.te Ar.al32 Ar.hn Ar.n32 (.inl rfl)).mono
      fun s ⟨_, Tp, h⟩ => h.mac_pre Tp.args)
    (fun s ⟨s₀, Tp, h⟩ => WP.mono (mac_ok v L h.env Ar.rounds (h.slots Tp.args) (length_bytesAt _ _ _) Ar.h7 Ar.h13
      Ar.t4 Ar.t16 Ar.te Ar.al32 Ar.hn Ar.n32 h.c0 (.inl rfl) (Tp.args.aad.of_eq h.rd h.wr)
      (Tp.args.data.of_eq h.rd h.wr)) fun _ A' => ⟨s₀, Tp, h.mac Tp.args (.inl rfl) A'⟩) ?_
  -- The tag.
  refine CT.seq (J := fun s => ∃ s₀, SealTop K W SP N A D T R nl al n tl s₀ ∧ Run s₀ K W SP N A D T R nl al n tl s)
    ((tag_ct v L Ar.rounds (.inl rfl)).mono fun s ⟨_, Tp, h⟩ => h.tag_pre Tp.args)
    (fun s ⟨s₀, Tp, h⟩ => WP.mono (tag_ok v L h.env Ar.rounds (h.slots Tp.args).ctx (h.slots Tp.args).rounds (h7' _)
      (h13' _) h.c0 (.inl rfl)) fun _ ⟨E, rd, wr, f, _⟩ => ⟨s₀, Tp, h.tag Tp.args (.inl rfl) E rd wr f⟩) ?_
  -- Counter mode.
  refine CT.seq (J := fun s => ∃ s₀, SealTop K W SP N A D T R nl al n tl s₀ ∧ Run s₀ K W SP N A D T R nl al n tl s)
    ((ctr_ct v L Ar.rounds Ar.n32).mono fun s ⟨_, Tp, h⟩ => h.ctr_pre Tp.args)
    (fun s ⟨s₀, Tp, h⟩ => by
      obtain ⟨E, hK, hRo, hDp, hlen, nonce, C⟩ := h.ctr_pre Tp.args
      exact WP.mono (ctr_ok v C E hK hRo hDp hlen) fun _ ⟨E', rd, wr, f, _⟩ => ⟨s₀, Tp, h.ctr Tp.args E' rd wr f⟩) ?_
  -- The tag copied out.
  refine CT.seq (J := fun s => s.gpr .ebp = W)
    (tagOut_ct L fun s ⟨_, Tp, h⟩ => ⟨h.env, (h.slots Tp.args).tl, (h.slots Tp.args).tp⟩)
    (fun s ⟨s₀, Tp, h⟩ => WP.mono (tagOut_ok L h.env (h.slots Tp.args).tl (h.slots Tp.args).tp
      (by have := Ar.t4; omega) Ar.t16 (Tp.args.tag.of_eq h.rd h.wr) (by rw [h.wr]; exact Tp.tw))
      fun _ ⟨_, E, _, _⟩ => E.ebp) ?_
  -- The exit.
  exact CT.taint [.ebp] (pin_ebp fun _ h => h) (by taint_decide)

theorem seal_ct (v : Ctr32Impl) : ConstantTime isa sealX86.pre sealX86.pub («seal» v.callee v.suffix) :=
  CT.constantTime pubOf (fun _ _ _ _ h => pubOf_eq h) fun p => by
    by_cases hex : ∃ s, sealX86.pre s ∧ pubOf s = p
    · obtain ⟨z, hz, hp⟩ := hex
      exact (seal_top_ct v z (seal_top_of hz hp)).mono fun s hs => seal_top_of hs.1 hs.2
    · intro s₁ _ _ _ _ _ h
      exact (hex ⟨s₁, h.1⟩).elim

end VG.Proof.AesCcm.X86

import VerifiedGarbage.Proof.Gcm.X86_64.Cached.PreparedTo
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Prepared
import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.OutOfPlace
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.LoopP
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Ok
import VerifiedGarbage.Proof.Gcm.Powers
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZTo.LoopP
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Ok

/-!
# The AVX-512 loops with the powers in the key context: both meet their contracts

Untrusted: everything here is checked by Lean. `stitchP_ok`: `StitchZP.enc`
and `StitchZP.dec` meet `StitchOkP`: the setup leaves the state of
`StitchZ.setup_ok` from the powers of the key context (`setupP_ok`): in the
field, `x · (Hⁿ · x⁻¹) = Hⁿ` (`x_φ_hInvF`, `φ_hpow`), so that their products,
and those of the tables loaded (`bigP_ok`, `bigDP_ok`), add up to `GHASH`
(`StitchZ.finZ`, `finZ48`); the rest is `StitchZ`'s (`encTailG_ok`,
`decTailG_ok`).
-/

namespace VG.Proof.Gcm.X86_64.StitchZP

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Stitch (SPreP StitchOkP EPost DPost hk)
open VG.Proof.Gcm.X86_64.StitchZ (finZ finZ48 FinOk48 encTailG_ok decTailG_ok)
open VG.Spec.Gcm (Block hpow)

/-- `Hⁿ · x⁻¹`, times `x`, is `Hⁿ`. -/
theorem x_φ_hInvF (H : Block) (n : Nat) : x * φ (hInvF (hpow H n)) = φ H ^ n := by
  rw [hInvF, Pclmul.x_φ_hInv, φ_hpow]

theorem finP {H : Block} {P : Nat → Nat → Block}
    (hP : ∀ k < 4, ∀ l < 4, P k l = hInvF (hpow H (16 - 4 * k - l))) :
    ∀ k < 4, ∀ l < 4, x * φ (P k l) = φ H ^ (16 - 4 * k - l) := fun k hk l hl => by
  rw [hP k hk l hl, x_φ_hInvF]

theorem fin48P (H : Block) (T : Nat → Nat → Nat → Block)
    (hT : ∀ g < 3, ∀ k < 4, ∀ l < 4, T g k l = hInvF (hpow H (48 - 16 * g - 4 * k - l))) : FinOk48 H T :=
  finZ48 fun g hg k hk l hl => by rw [hT g hg k hk l hl, x_φ_hInvF]

/-- The encryption of `n` blocks (a multiple of 16, at least 16). -/
theorem enc_ok {s₀ : State} (hp : SPreP s₀) : WP isa Impl.Gcm.X86_64.StitchZP.enc s₀ (EPost s₀) :=
  WP.seq (WP.mono (setupP_ok hp) fun _ ⟨_, hR, hpw⟩ =>
    encTailG_ok hp.base (finZ (finP hpw))
      (fun _ h256 hI => bigP_ok hp (finZ (finP hpw)) hpw (fin48P (hk s₀)) h256 hI) hR)

/-- The decryption of `n` blocks (a multiple of 16, at least 16). -/
theorem dec_ok {s₀ : State} (hp : SPreP s₀) : WP isa Impl.Gcm.X86_64.StitchZP.dec s₀ (DPost s₀) :=
  WP.seq (WP.mono (setupP_ok hp) fun _ ⟨_, hR, hpw⟩ =>
    decTailG_ok hp.base (finZ (finP hpw)) (fun _ h256 hI => bigDP_ok hp hpw (fin48P (hk s₀)) h256 hI) hR)

/-- Both loops meet their contracts. -/
theorem stitchP_ok : StitchOkP Impl.Gcm.X86_64.StitchZP.enc Impl.Gcm.X86_64.StitchZP.dec :=
  ⟨fun _ hp => enc_ok hp, fun _ hp => dec_ok hp⟩

end VG.Proof.Gcm.X86_64.StitchZP

/-! ## The out-of-place AVX-512 loops (`StitchZTo`): they meet their contract

Untrusted: everything here is checked by Lean. `stitchTo_ok`:
`StitchZTo.enc` meets `StitchToOkM` for a key context of either kind (it
computes the powers itself, from the hash subkey in the first 256 bytes):
the powers `H'`–`H'¹⁶` as `Stitch.setupG_ok` computes them (`setupGTo_ok`),
stored, and the rest of the setup (`setupTTo_ok`, `setupZTo_ok`); with them
the products of a group, and of 48 blocks, add up to `GHASH`
(`StitchZ.finZ`, `StitchZ.powers48`, `StitchZ.finZ48`), and the loops do the
rest (`encTailGTo_ok`, `bigTo_ok`).

`stitchToP_ok`: `StitchZTo.encP` meets `StitchToOkM` for a key context with
the powers: its setup loads them as `StitchZP.setupGP_ok` (`setupGPTo_ok`,
from the conversions of `StitchZP.cvtRun_ok` for the in-place view
`dst s₀`), then stores them and makes the rest of the setup as
`StitchZTo.enc`; with them and the tables of `bigPTo` the products add up to
`GHASH` (`StitchZP.finP`, `StitchZP.fin48P`).

They are proven here, with the loops they build on, rather than in
`Proof/Gcm/X86_64/StitchZTo/`, which does not compute in the field
(`Proof/Gcm/Poly.lean`), so that no more modules import its algebra.
-/

namespace VG.Proof.Gcm.X86_64.StitchZTo

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Stitch (SPreTo StitchToOkM CtxMode hk in_sub_int)
open VG.Proof.Gcm.X86_64.Pclmul (pows_ok const_ok ldrev_ok hInv_ok rev_eq)
open VG.Proof.Gcm.X86_64.Vpclmul (powersP_ok powers16P_ok)
open VG.Proof.Gcm.X86_64.StitchZ (finZ finZ48 powers48)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.Stitch (setupG)
open VG.Impl.Gcm.X86_64.Vpclmul (preg16)
open VG.Impl.Gcm.X86_64.StitchZTo (setup enc encWith)

/-- `Stitch.setupG_ok`, from `SPreTo`. -/
theorem setupGTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) :
    WP isa (.block setupG) s₀ fun s =>
      (∀ l < 2, s.lane .xmm0 l = revMask) ∧ (∀ l < 2, s.lane .xmm1 l = poly) ∧
      (∀ k < 8, ∀ l < 2, x * φ (s.lane (preg16 k) l) = φ (hk s₀) ^ (16 - 2 * k - l)) ∧
      (∀ r, r ≠ .rax → s.gpr r = s₀.gpr r) ∧ s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  have hge := M.ge
  simp only [setupG, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 _ s₀ (by decide)) fun s₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 _ s₁ (by decide)) fun s₂ ⟨c₂, o₂⟩ => ?_
  have o₁₂ := o₁.trans o₂
  rw [WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm7 .rdi 240 s₂ (by decide)
    (by rw [o₂.xmm _ (by decide), c₁, rev_eq])
    (by rw [o₁₂.rd, o₁₂.wr, o₁₂.gpr _ (by decide)]; exact in_sub_int hp.k_in (by omega))) fun s₃ ⟨l₃, o₃⟩ => ?_
  have o₁₃ := o₁₂.trans o₃
  rw [WP.block_append_iff]
  refine WP.mono (hInv_ok s₃) fun s₄ ⟨t₄, o₄⟩ => ?_
  have hH : x * φ (s₄.xmm .xmm3) = φ (hk s₀) := by
    rw [t₄, l₃, o₁₂.mem, o₁₂.gpr _ (by decide), BitVec.ofInt_natCast]; rfl
  rw [WP.block_append_iff]
  refine WP.mono (pows_ok s₄ (by rw [o₄.xmm _ (by decide), o₃.xmm _ (by decide), c₂]) hH)
    fun s₇ ⟨hH2, hH3, hH4, o₇⟩ => ?_
  have o₁₇ := o₁₃.trans (o₄.trans o₇)
  rw [WP.block_append_iff]
  refine WP.mono (powersP_ok (H := hk s₀)
    (by rw [(o₂.trans (o₃.trans (o₄.trans o₇))).xmm _ (by decide), c₁, rev_eq])
    (by rw [(o₃.trans (o₄.trans o₇)).xmm _ (by decide), c₂])
    (by rw [o₇.xmm _ (by decide), hH]) hH2 hH3 hH4)
    fun s₈ ⟨l0, l1, _, pw8, _, g₈, m₈, rd₈, wr₈⟩ => ?_
  refine WP.mono (powers16P_ok l1 pw8) fun s₉ ⟨pw, F⟩ => ⟨fun l hl => ?_, fun l hl => ?_, pw,
    fun r hr => by rw [F.gpr, g₈ r hr, o₁₇.gpr r hr], by rw [F.mem, m₈, o₁₇.mem],
    by rw [F.rd, rd₈, o₁₇.rd], by rw [F.wr, wr₈, o₁₇.wr]⟩
  · rw [F.lane _ (by decide) l hl]; exact l0 l hl
  · rw [F.lane _ (by decide) l hl]; exact l1 l hl

/-- The setup: the state the loop starts from, with the powers
`x · Pₖₗ = H¹⁶⁻⁴ᵏ⁻ˡ` in the working space. -/
theorem setupTo_ok {M : CtxMode} {s₀ : State} (hp : SPreTo M s₀) :
    WP isa (.block setup) s₀ fun s => ∃ P, ReadyTo s₀ P s ∧
      ∀ k < 4, ∀ l < 4, x * φ (P k l) = φ (hk s₀) ^ (16 - 4 * k - l) := by
  rw [setup, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (setupGTo_ok hp) fun s₁ ⟨l0, l1, pw, g₁, m₁, rd₁, wr₁⟩ => ?_
  rw [← List.append_assoc, WP.block_append_iff]
  exact WP.mono (setupTTo_ok hp l0 l1 g₁ m₁ rd₁ wr₁) fun _ hR => WP.mono (setupZTo_ok hR) fun _ hR' =>
    ⟨_, hR', fun k hk l hl => by
      rw [show 16 - 4 * k - l = 16 - 2 * (2 * k + l / 2) - l % 2 by omega]
      exact pw _ (by omega) _ (by omega)⟩

/-- The out-of-place loop meets its contract, for a key context of either
kind. -/
theorem stitchTo_ok (M : CtxMode) : StitchToOkM M Impl.Gcm.X86_64.StitchZTo.enc := fun _ hp =>
  WP.seq (WP.mono (setupTo_ok hp) fun _ ⟨_, hR, hpw⟩ =>
    encTailGTo_ok hp (finZ hpw) (fun _ h256 hI => bigTo_ok hp (finZ hpw) (finZ48 (powers48 hpw)) h256 hI) hR)


open VG.Proof.Gcm.X86_64.StitchZP (vinsSelf_ok consts_ok cvtRun_ok hInvF finP fin48P)
open VG.Impl.Gcm.X86_64.StitchZP (setupGP)
open VG.Impl.Gcm.X86_64.StitchZTo (setupP)

/-- `StitchZP.setupGP_ok`, from `SPreTo`. -/
theorem setupGPTo_ok {s₀ : State} (hp : SPreTo CtxMode.powers s₀) :
    WP isa (.block setupGP) s₀ fun s =>
      (∀ l < 2, s.lane .xmm0 l = revMask) ∧ (∀ l < 2, s.lane .xmm1 l = poly) ∧
      (∀ k < 8, ∀ l < 2, s.lane (preg16 k) l = hInvF (Spec.Gcm.hpow (hk s₀) (16 - 2 * k - l))) ∧
      (∀ r, r ≠ .rax → s.gpr r = s₀.gpr r) ∧ s.mem = s₀.mem ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  simp only [setupGP, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 _ s₀ (by decide)) fun s₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 _ s₁ (by decide)) fun s₂ ⟨c₂, o₂⟩ => ?_
  have o₁₂ := o₁.trans o₂
  rw [WP.block_append_iff, show ([.vop (.vinserti128 .xmm0 .xmm0 .xmm0 1), .vop (.vinserti128 .xmm1 .xmm1 .xmm1 1)] :
    List Instr) = [.vop (.vinserti128 .xmm0 .xmm0 .xmm0 1)] ++ [.vop (.vinserti128 .xmm1 .xmm1 .xmm1 1)] from rfl,
    WP.block_append_iff]
  refine WP.mono (vinsSelf_ok .xmm0 s₂) fun s₃ ⟨v₃, f₃⟩ => ?_
  refine WP.mono (vinsSelf_ok .xmm1 s₃) fun s₄ ⟨v₄, f₄⟩ => ?_
  have m0 : ∀ l < 2, s₄.lane .xmm0 l = revMask := fun l hl => by
    rw [f₄.lane _ (by decide) l hl, v₃ l hl]; show s₂.xmm .xmm0 = _; rw [o₂.xmm _ (by decide), c₁]; rfl
  have m1 : ∀ l < 2, s₄.lane .xmm1 l = poly := fun l hl => by
    rw [v₄ l hl, f₃.lane _ (by decide) 0 (by decide)]; exact c₂
  rw [WP.block_append_iff]
  refine WP.mono (consts_ok s₄ m1) fun s₅ ⟨c8, c9, f₅⟩ => ?_
  have g₅ : ∀ r, r ≠ .rax → s₅.gpr r = s₀.gpr r := fun r hr => by rw [f₅.gpr, f₄.gpr, f₃.gpr, o₁₂.gpr r hr]
  have mm₅ : s₅.mem = s₀.mem := by rw [f₅.mem, f₄.mem, f₃.mem, o₁₂.mem]
  have rd₅ : s₅.rd = s₀.rd := by rw [f₅.rd, f₄.rd, f₃.rd, o₁₂.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [f₅.wr, f₄.wr, f₃.wr, o₁₂.wr]
  refine WP.mono (cvtRun_ok hp.toP 8 (Nat.le_refl _) s₅ (g₅ _ (by decide)) mm₅ rd₅ wr₅
    (fun l hl => by rw [f₅.lane _ (by decide) l hl]; exact m0 l hl) c8 c9) fun s' ⟨pw, F⟩ =>
    ⟨fun l hl => by rw [F.lane _ (by decide) l hl, f₅.lane _ (by decide) l hl]; exact m0 l hl,
      fun l hl => by rw [F.lane _ (by decide) l hl, f₅.lane _ (by decide) l hl]; exact m1 l hl, pw,
      fun r hr => by rw [F.gpr, g₅ r hr], by rw [F.mem, mm₅], by rw [F.rd, rd₅], by rw [F.wr, wr₅]⟩

/-- The setup: the state the loop starts from, with the powers
`Pₖₗ = H¹⁶⁻⁴ᵏ⁻ˡ · x⁻¹` in the working space. -/
theorem setupPTo_ok {s₀ : State} (hp : SPreTo CtxMode.powers s₀) :
    WP isa (.block setupP) s₀ fun s => ∃ P, ReadyTo s₀ P s ∧
      ∀ k < 4, ∀ l < 4, P k l = hInvF (Spec.Gcm.hpow (hk s₀) (16 - 4 * k - l)) := by
  rw [setupP, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (setupGPTo_ok hp) fun s₁ ⟨l0, l1, pw, g₁, m₁, rd₁, wr₁⟩ => ?_
  rw [← List.append_assoc, WP.block_append_iff]
  exact WP.mono (setupTTo_ok hp l0 l1 g₁ m₁ rd₁ wr₁) fun _ hR => WP.mono (setupZTo_ok hR) fun _ hR' =>
    ⟨_, hR', fun k hk l hl => by
      rw [show 16 - 4 * k - l = 16 - 2 * (2 * k + l / 2) - l % 2 by omega]
      exact pw _ (by omega) _ (by omega)⟩

/-- The out-of-place loop with the powers loaded meets its contract. -/
theorem stitchToP_ok : StitchToOkM CtxMode.powers Impl.Gcm.X86_64.StitchZTo.encP := fun s₀ hp =>
  WP.seq (WP.mono (setupPTo_ok hp) fun _ ⟨_, hR, hpw⟩ =>
    encTailGTo_ok hp (finZ (finP hpw))
      (fun _ h256 hI => bigPTo_ok hp (finZ (finP hpw)) hpw (fin48P (hk s₀)) h256 hI) hR)

end VG.Proof.Gcm.X86_64.StitchZTo

/-!
# Prepared-context loops satisfy the unchanged GCM postconditions

The setup loads the same field elements as the old per-record conversion.
The existing loop and field proofs therefore apply unchanged.
-/

namespace VG.Proof.Gcm.X86_64.StitchZR
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPrePrepared StitchOkM CtxMode EPost DPost hk)
open VG.Proof.Gcm.X86_64.StitchZ (finZ encTailG_ok decTailG_ok)
open VG.Proof.Gcm.X86_64.StitchZP (finP fin48P)

/-- Encryption with prepared powers. -/
theorem enc_ok {s₀ : State} (hp : SPrePrepared s₀) : WP isa Impl.Gcm.X86_64.StitchZR.enc s₀ (EPost s₀) :=
  WP.seq (WP.mono (setupP_ok hp) fun _ ⟨_, hR, hpw⟩ =>
    encTailG_ok hp.base (finZ (finP hpw))
      (fun _ h256 hI => bigP_ok hp (finZ (finP hpw)) hpw (fin48P (hk s₀)) h256 hI) hR)

/-- Decryption with prepared powers. -/
theorem dec_ok {s₀ : State} (hp : SPrePrepared s₀) : WP isa Impl.Gcm.X86_64.StitchZR.dec s₀ (DPost s₀) :=
  WP.seq (WP.mono (setupP_ok hp) fun _ ⟨_, hR, hpw⟩ =>
    decTailG_ok hp.base (finZ (finP hpw)) (fun _ h256 hI => bigDP_ok hp hpw (fin48P (hk s₀)) h256 hI) hR)

/-- Both in-place loops implement the prepared context mode. -/
theorem stitch_ok : StitchOkM CtxMode.prepared Impl.Gcm.X86_64.StitchZR.enc Impl.Gcm.X86_64.StitchZR.dec :=
  ⟨fun _ hp => enc_ok hp.toPrepared, fun _ hp => dec_ok hp.toPrepared⟩
end VG.Proof.Gcm.X86_64.StitchZR

namespace VG.Proof.Gcm.X86_64.StitchZRTo
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (StitchToOkM CtxMode hk)
open VG.Proof.Gcm.X86_64.StitchZ (finZ)
open VG.Proof.Gcm.X86_64.StitchZP (finP fin48P)
open VG.Proof.Gcm.X86_64.StitchZTo (encTailGTo_ok)

/-- Out-of-place encryption implements the same prepared context mode. -/
theorem stitchTo_ok : StitchToOkM CtxMode.prepared Impl.Gcm.X86_64.StitchZRTo.encP := fun s₀ hp =>
  WP.seq (WP.mono (setupPTo_ok hp) fun _ ⟨_, hR, hpw⟩ =>
    encTailGTo_ok hp (finZ (finP hpw))
      (fun _ h256 hI => bigPTo_ok hp (finZ (finP hpw)) hpw (fin48P (hk s₀)) h256 hI) hR)
end VG.Proof.Gcm.X86_64.StitchZRTo

/-! ## Prepared powers and cached AES keys -/

namespace VG.Proof.Gcm.X86_64.StitchZH
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPrePrepared StitchOkM CtxMode EPost DPost hk)
open VG.Proof.Gcm.X86_64.StitchZ (finZ)
open VG.Proof.Gcm.X86_64.StitchZP (finP fin48P)

theorem enc_ok {s₀ : State} (hp : SPrePrepared s₀) :
    WP isa Impl.Gcm.X86_64.StitchZH.enc s₀ (EPost s₀) :=
  WP.seq (WP.mono (setup_ok hp) fun _ ⟨_, hR, hpw, hK⟩ =>
    encTailG_ok hp.base (finZ (finP hpw))
      (fun _ h256 hI hC => bigP_ok hp (finZ (finP hpw)) hpw (fin48P (hk s₀)) h256 hI hC) hR hK)

theorem dec_ok {s₀ : State} (hp : SPrePrepared s₀) :
    WP isa Impl.Gcm.X86_64.StitchZH.dec s₀ (DPost s₀) :=
  WP.seq (WP.mono (setup_ok hp) fun _ ⟨_, hR, hpw, hK⟩ =>
    decTailG_ok hp.base (finZ (finP hpw))
      (fun _ h256 hI hC => bigDP_ok hp hpw (fin48P (hk s₀)) h256 hI hC) hR hK)

theorem stitch_ok : StitchOkM CtxMode.prepared Impl.Gcm.X86_64.StitchZH.enc Impl.Gcm.X86_64.StitchZH.dec :=
  ⟨fun _ hp => enc_ok hp.toPrepared, fun _ hp => dec_ok hp.toPrepared⟩

end VG.Proof.Gcm.X86_64.StitchZH

namespace VG.Proof.Gcm.X86_64.StitchZHTo
open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (StitchToOkM CtxMode hk)
open VG.Proof.Gcm.X86_64.StitchZ (finZ)
open VG.Proof.Gcm.X86_64.StitchZP (finP fin48P)

/-- Prepared powers and cached AES keys, with separate input and output buffers. -/
theorem stitchTo_ok : StitchToOkM CtxMode.prepared Impl.Gcm.X86_64.StitchZHTo.encP := fun s₀ hp =>
  WP.seq (WP.mono (setup_ok hp) fun _ ⟨_, hR, hpw, hK⟩ =>
    encTailGTo_ok hp (finZ (finP hpw))
      (fun _ h256 hI hC => bigPTo_ok hp (finZ (finP hpw)) hpw (fin48P (hk s₀)) h256 hI hC) hR hK)

end VG.Proof.Gcm.X86_64.StitchZHTo

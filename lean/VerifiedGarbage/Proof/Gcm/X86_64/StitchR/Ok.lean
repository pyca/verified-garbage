module

import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Ok
import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Setup
import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.OutOfPlace
import VerifiedGarbage.Proof.Gcm.Powers
import VerifiedGarbage.Proof.Gcm.X86_64.StitchR.RemETo
import VerifiedGarbage.Proof.Gcm.X86_64.StitchR.Zero
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchR.SetupFin
public import VerifiedGarbage.Proof.Gcm.Poly
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Cvt
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Ghash
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchR.Rem
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchTo.Loop
import VerifiedGarbage.Proof.Gcm.X86_64.StitchR.RemE

/-!
# The 256-bit interleaved loops with prepared powers meet their contracts

Untrusted: everything here is checked by Lean. `StitchR.setup` loads the
pairs of powers as `StitchZR.setupGP_ok` says, which `Stitch.setupG_ok`'s
postcondition is, with `x · H'ⁿ = Hⁿ` for `H'ⁿ = Hⁿ · x⁻¹` (`x_φ_hInvF`);
the rest of the setup and the loops are `Stitch`'s (`setupT_ok`,
`encTail_ok`, `decTail_ok`), and out of place `StitchTo`'s.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchR

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86_64.Stitch (nb SPre SPreM SPreTo SPrePrepared StitchOkM StitchToOkM CtxMode EPost DPost
  EPostTo hk Ready setupT_ok finE finD)
open VG.Proof.Gcm.X86_64.StitchTo (ReadyTo)
open VG.Proof.Gcm.X86_64.StitchZP (hInvF)
open VG.Spec.Gcm (Block hpow ghashFrom)
open VG.Proof.Gcm.X86_64.Pclmul (Prod φ_reduceB)
open VG.Proof.Gcm.X86_64.StitchZH (accR)

/-- `Hⁿ · x⁻¹`, times `x`, is `Hⁿ`. -/
theorem x_φ_hInvF (H : Block) (n : Nat) : x * φ (hInvF (hpow H n)) = φ H ^ n := by
  rw [hInvF, Pclmul.x_φ_hInv, φ_hpow]

/-- The setup: the state the loops start from, as `Stitch.setup_ok`. -/
theorem setup_ok {s₀ : State} {lo : Nat} (hp : SPrePrepared s₀ lo) :
    WP isa (.block Impl.Gcm.X86_64.StitchR.setup) s₀ fun s => ∃ P, Ready s₀ P s ∧
      ∀ k < 8, ∀ l < 2, x * φ (P k l) = φ (hk s₀) ^ (16 - 2 * k - l) := by
  simp only [Impl.Gcm.X86_64.StitchR.setup, List.append_assoc]
  rw [WP.block_append_iff]
  exact WP.mono (StitchZR.setupGP_ok hp) fun s₁ ⟨l0, l1, pw, g₁, m₁, rd₁, wr₁⟩ =>
    WP.mono (setupT_ok hp.base l0 l1 g₁ m₁ rd₁ wr₁) fun _ hR =>
      ⟨_, hR, fun k hk l hl => by rw [pw k hk l hl]; exact x_φ_hInvF _ _⟩

/-- The prepared powers, `H'¹⁶⁻ᵐ` at `16 m`: the products of the last `r`
blocks with `H'ʳ` … `H'`, reduced, add up to `GHASH` over them. -/
theorem remLaw {H : Block} {P : Nat → Nat → Block}
    (hP : ∀ k < 8, ∀ l < 2, x * φ (P k l) = φ H ^ (16 - 2 * k - l)) : RemLaw H P := by
  intro r hr1 hr15 X y
  let T : Nat → BitVec 128 := fun j => P ((16 - r + j) / 2) ((16 - r + j) % 2)
  have hT : ∀ j < r, x * φ (T j) = φ H ^ (r - j) := fun j hj => by
    have := hP ((16 - r + j) / 2) (by omega) ((16 - r + j) % 2) (by omega)
    rwa [show 16 - 2 * ((16 - r + j) / 2) - (16 - r + j) % 2 = r - j by omega] at this
  have key : ∀ n, 1 ≤ n → n ≤ r →
      (accR X T y n).val = φ H ^ (r - n) * φ (ghashFrom H y ((List.range n).map X)) := by
    intro n
    induction n with
    | zero => intro h; omega
    | succ n ih =>
      intro _ hn
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · have h0 := hT 0 (by omega)
        simp only [accR, ↓reduceIte, Prod.val_acc, Prod.val_zero, zero_add, List.range_one, List.map_cons,
          List.map_nil, ghashFrom, List.foldl_cons, List.foldl_nil, φ_mul, Nat.sub_zero] at h0 ⊢
        rw [show r = (r - (0 + 1)) + 1 by omega, pow_succ] at h0
        linear_combination φ (y ^^^ X 0) * h0
      · have hn' := hT n (by omega)
        rw [show r - n = (r - (n + 1)) + 1 by omega, pow_succ] at hn'
        simp only [accR, show n ≠ 0 by omega, ↓reduceIte, Prod.val_acc, ih hpos (by omega), List.range_succ,
          List.map_append, List.map_cons, List.map_nil, ghashFrom, List.foldl_append, List.foldl_cons,
          List.foldl_nil, φ_mul, φ_xor, φ_zero, zero_add]
        rw [show r - n = (r - (n + 1)) + 1 by omega, pow_succ]
        linear_combination φ (X n) * hn'
  apply φ_inj
  rw [φ_reduceB, key r hr1 (Nat.le_refl _), Nat.sub_self, pow_zero, one_mul]

/-- `decR`: the decryption of any number of blocks from 1 on. -/
theorem decR_ok {s₀ : State} (hp : SPrePrepared s₀ 1) :
    WP isa Impl.Gcm.X86_64.StitchR.decR s₀ (DPost s₀) :=
  WP.seq (WP.mono (setup_ok hp) fun _ ⟨_, hR, hpw⟩ =>
    zeroTail_ok (Rdy := Ready s₀ _) (fun _ _ h g l m rd wr => Ready.keep h g l m rd wr)
      (fun _ h => h.gpr _ (by decide) (by decide) (by decide))
      (fun hlt _ h => decSmall_ok hp.base (remLaw hpw) hp.base.nb16 hlt h)
      (fun h16 _ h => decTailR_ok (hp.base.ofLe h16) (finD hpw) (remLaw hpw) h) hR)

/-- `encR`: the encryption of any number of blocks from 1 on. -/
theorem encR_ok {s₀ : State} (hp : SPrePrepared s₀ 1) :
    WP isa Impl.Gcm.X86_64.StitchR.encR s₀ (EPost s₀) :=
  WP.seq (WP.mono (setup_ok hp) fun _ ⟨_, hR, hpw⟩ =>
    zeroTail_ok (Rdy := Ready s₀ _) (fun _ _ h g l m rd wr => Ready.keep h g l m rd wr)
      (fun _ h => h.gpr _ (by decide) (by decide) (by decide))
      (fun hlt _ h => encSmall_ok hp.base (remLaw hpw) hp.base.nb16 hlt h)
      (fun h16 _ h => encTailR_ok (hp.base.ofLe h16) (finE hpw) (remLaw hpw) h) hR)

/-- Both in-place loops, for a prepared key context, for any number of
blocks from 1 on. -/
theorem stitchR_ok :
    StitchOkM CtxMode.prepared Impl.Gcm.X86_64.StitchR.encR Impl.Gcm.X86_64.StitchR.decR 1 1 1 1 :=
  ⟨fun _ hp _ => encR_ok hp.toPrepared, fun _ hp _ => decR_ok hp.toPrepared⟩

/-- The out-of-place setup, as `StitchTo.setupTo_ok`. -/
theorem setupTo_ok {s₀ : State} (hp : SPreTo CtxMode.prepared s₀) :
    WP isa (.block Impl.Gcm.X86_64.StitchR.setupTo) s₀ fun s => ∃ P, ReadyTo s₀ P s ∧
      ∀ k < 8, ∀ l < 2, x * φ (P k l) = φ (hk s₀) ^ (16 - 2 * k - l) := by
  rw [Impl.Gcm.X86_64.StitchR.setupTo, List.append_assoc, WP.block_append_iff]
  refine WP.mono (StitchZRTo.setupGPTo_ok hp) fun s₁ ⟨l0, l1, pw, g₁, m₁, rd₁, wr₁⟩ => ?_
  exact WP.mono (StitchZTo.setupTTo_ok hp l0 l1 g₁ m₁ rd₁ wr₁) fun _ hR =>
    ⟨_, ReadyTo.ofReady2 hR, fun k hk l hl => by rw [pw k hk l hl]; exact x_φ_hInvF _ _⟩

/-- The out-of-place loop, for a prepared key context, for any number of
blocks from 16 on. -/
theorem stitchTo_ok : StitchToOkM CtxMode.prepared Impl.Gcm.X86_64.StitchR.encToR 1 := fun _ hp _ =>
  WP.seq (WP.mono (setupTo_ok hp) fun _ ⟨_, hR, hpw⟩ => encTailRTo_ok hp (finE hpw) (remLaw hpw) hR)

/-- The setup's powers give the products of an encryption body. -/
theorem setupFin : SetupFin := fun hp =>
  WP.mono (setupTo_ok hp) fun _ ⟨P, hR, hpw⟩ => ⟨P, hR, finE hpw⟩

end VG.Proof.Gcm.X86_64.StitchR

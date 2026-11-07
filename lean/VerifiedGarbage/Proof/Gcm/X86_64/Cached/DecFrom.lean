module

-- separate module: the out-of-place loop's proof, which only the instances (`AesGcm/X86_64/Instances.lean`) use, so that a change to them does not rebuild it

public import VerifiedGarbage.Impl.Gcm.X86_64.StitchZH
public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.SpecFrom
public import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Context
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Cvt
public import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Gh48
public import VerifiedGarbage.Proof.Aes.X86_64.VaesZH.Rounds
import VerifiedGarbage.Proof.Gcm.X86_64.StitchFrom.Loop
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Loop48
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.Prepared
import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemD
import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.OutOfPlace
import VerifiedGarbage.Proof.Aes.X86_64.VaesZH.Load
import VerifiedGarbage.Proof.Framework.X86_64.HighKeep
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-!
# The AVX-512 decryption loop with cached round keys, out of place

`StitchZH.decFromR` is `StitchZH.decR`'s loops out of place
(`Impl.Gcm.X86_64.StitchFrom`'s arguments), for a multiple of 16 blocks, and
so is its proof: `setupFrom_ok`, the setup (`StitchFrom.setupFrom_ok`, then
the four lanes, `StitchZ.setupZ_run`, and the round keys), then the loops of
three groups (`bigDPM_ok`) and of one (`loopDRM_ok`), and the stores
(`StitchZ.dfinalM_ok`), all with the output at `r10`.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (SPreTo CtxMode DPostTo nb nr kp pp cp yp dp hk y₀ sch blk)
open VG.Proof.Gcm.X86_64.StitchZ (AInvM DInvM FinOk cmp_ok)
open VG.Proof.Gcm.X86_64.Pclmul (toNat_ofNat_lt)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Impl.Gcm.X86_64.StitchZ (setupZ)
open VG.Impl.Gcm.X86_64.StitchZH (setupPFrom decFromR bigDP dbody)
open VG.Proof.Gcm.X86_64.StitchZP (hInvF)
open VG.Spec.Gcm (Block ghashFrom)

/-- The state the loops start from, with the round keys cached. -/
theorem setupFrom_ok {s₀ : State} (hp : SPreTo CtxMode.prepared s₀) :
    WP isa (.seq (.block setupPFrom) Impl.Aes.X86_64.VaesZH.loadKeys) s₀ fun s =>
      ∃ P : Nat → Nat → Block, DInvM true s₀ P 0 s ∧
        (∀ k < 4, ∀ l < 4, P k l = hInvF (Spec.Gcm.hpow (hk s₀) (16 - 4 * k - l))) ∧
        VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s := by
  have hm := hp.toM
  rw [show setupPFrom = Impl.Gcm.X86_64.StitchFrom.setup ++ setupZ by
    simp only [setupPFrom, Impl.Gcm.X86_64.StitchFrom.setup, List.append_assoc]]
  have h₁ : WP isa (.block (Impl.Gcm.X86_64.StitchFrom.setup ++ setupZ)) s₀ fun s =>
      ∃ P : Nat → Nat → Block, DInvM true s₀ P 0 s ∧
        ∀ k < 4, ∀ l < 4, P k l = hInvF (Spec.Gcm.hpow (hk s₀) (16 - 4 * k - l)) := by
    rw [WP.block_append_iff]
    refine WP.mono (StitchFrom.setupFrom_ok hp (by decide)) fun s hR => ?_
    refine WP.mono (StitchZ.setupZ_run hR.a.ctr hR.a.msk hR.a.inc hR.m1)
      fun s' ⟨⟨c14, m0, i15, p1, y0, y1⟩, f⟩ => ?_
    have hA := hR.a
    refine ⟨fun k l => hInvF (Spec.Gcm.hpow (hk s₀) (16 - 2 * (2 * k + l / 2) - l % 2)), ⟨⟨Nat.zero_le _, fun l hl => by rw [c14 l hl, Nat.mul_zero, Nat.zero_add], m0, i15,
        by rw [f.gpr]; exact hA.rdi, by rw [f.gpr]; exact hA.rsi, by rw [f.gpr]; exact hA.r10,
        fun hi => by rw [f.gpr]; exact hA.r8 hi, by rw [f.mem]; exact hA.frame,
        fun k hk => absurd hk (by omega), fun k hk _ => by rw [f.mem]; exact hA.src k hk (Nat.zero_le _),
        by rw [f.rd]; exact hA.rd, by rw [f.wr]; exact hA.wr⟩,
      by rw [f.gpr, hR.rdx]; simp, by rw [f.gpr, hR.gpr _ (by decide) (by decide) (by decide) (by decide)]; simp,
      by rw [f.gpr]; exact hR.rax, fun r h1 h2 h3 _ h5 => by rw [f.gpr]; exact hR.gpr r h1 h2 (h3 rfl) h5,
      fun k hk l hl => ?_, p1, by rw [y0, hR.y]; simp [ghashFrom], y1⟩, fun k _ l _ => ?_⟩
    · rw [f.mem, show 64 * k + 16 * l = 32 * (2 * k + l / 2) + 16 * (l % 2) by omega]
      exact hR.pw _ (by omega) _ (by omega)
    · show hInvF (Spec.Gcm.hpow (hk s₀) (16 - 2 * (2 * k + l / 2) - l % 2)) = _
      rw [show 16 - 2 * (2 * k + l / 2) - l % 2 = 16 - 4 * k - l by omega]
  refine WP.seq (WP.mono h₁ fun s ⟨P, hI, hpw⟩ => ?_)
  refine WP.mono (VG.Proof.Aes.X86_64.VaesZH.loadKeys_ok s (hI.a.keys hm) hm.rounds
      (by rw [hI.a.rsi]; simp) (by rw [hI.a.r10, hI.a.rdi])) fun t ⟨hK, f⟩ => ?_
  refine ⟨P, ⟨⟨hI.a.le, fun l hl => by rw [f.zlane _ (by simp) l hl]; exact hI.a.ctr l hl,
      fun l hl => by rw [f.zlane _ (by simp) l hl]; exact hI.a.msk l hl,
      fun l hl => by rw [f.zlane _ (by simp) l hl]; exact hI.a.inc l hl,
      by rw [f.gpr]; exact hI.a.rdi, by rw [f.gpr]; exact hI.a.rsi, by rw [f.gpr]; exact hI.a.r10,
      fun hi => by rw [f.gpr]; exact hI.a.r8 hi, by rw [f.mem]; exact hI.a.frame,
      fun k hk => by rw [f.mem]; exact hI.a.out k hk, fun k hk hc => by rw [f.mem]; exact hI.a.src k hk hc,
      by rw [f.rd]; exact hI.a.rd, by rw [f.wr]; exact hI.a.wr⟩,
    by rw [f.gpr]; exact hI.rdx, by rw [f.gpr]; exact hI.r9, by rw [f.gpr]; exact hI.rax,
    fun r h1 h2 h3 h4 h5 => by rw [f.gpr]; exact hI.gpr r h1 h2 h3 h4 h5,
    fun k hk l hl => by rw [f.mem]; exact hI.pw k hk l hl,
    fun l hl => by rw [f.zlane _ (by simp) l hl]; exact hI.m1 l hl,
    by rw [f.zlane _ (by simp) 0 (by decide)]; exact hI.y,
    fun l h1 h4 => by rw [f.zlane _ (by simp) l h4]; exact hI.y1 l h1 h4⟩, hpw, hK⟩

/-- The prepared powers the setup loads, and the tables of 48 blocks computed
from them, give the products of the loops' bodies (`StitchZ.finZ`,
`StitchZP.fin48P`), which `AesGcm/X86_64/Instances.lean` proves where the
field is imported. -/
def PowFinZ : Prop :=
  (∀ (H : Block) (P : Nat → Nat → Block),
      (∀ k < 4, ∀ l < 4, P k l = hInvF (Spec.Gcm.hpow H (16 - 4 * k - l))) → FinOk H P) ∧
    ∀ (H : Block) (T : Nat → Nat → Nat → Block),
      (∀ g < 3, ∀ k < 4, ∀ l < 4, T g k l = hInvF (Spec.Gcm.hpow H (48 - 16 * g - 4 * k - l))) →
        StitchZ.FinOk48 H T

/-- The out-of-place decryption loop, for a prepared key context, for any
number of blocks from 16 on that is a multiple of 16. -/
theorem decFromR_ok (hz : PowFinZ) : Stitch.StitchFromOkM CtxMode.prepared decFromR := by
  intro s₀ hp hm16
  have hm := hp.toM
  have hn : nb s₀ < 2 ^ 64 := (s₀.gpr .r9).isLt
  refine WP.seq (WP.mono (setupFrom_ok hp) fun s ⟨P, hI₁, hpw, hCache⟩ => ?_)
  have hf : FinOk (hk s₀) P := hz.1 _ _ hpw
  refine WP.seq (WP.mono (WP.hkeep rfl (cmp_ok s Impl.Gcm.X86_64.StitchZ.bigMinP 96 (by decide)))
    fun s₂ ⟨⟨hcf, g, l, m, rd, wr⟩, hh⟩ => ?_)
  have hI₂ := hI₁.of_eq g l m rd wr
  have hCache₂ := hCache.keep hh (hI₂.a.keys hm)
  rw [hI₁.r9, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by decide)] at hcf
  refine WP.seq (WP.mono (WP.ite (Q := fun s' => ∃ e, DInvM true s₀ P e s' ∧
      VG.Proof.Aes.X86_64.VaesZH.Keys (nr s₀) (sch s₀) s') (decide (nb s₀ - 16 * 0 < 96))
    (by simp only [eval, hcf]) (fun _ => WP.block_nil ⟨0, hI₂, hCache₂⟩)
    (fun h => bigDPM_ok hm hp.toPrepared hpw (hz.2 (hk s₀)) (by simp at h; omega) hI₂ hCache₂))
    fun s₃ ⟨e, hI₃, hCache₃⟩ => ?_)
  refine WP.seq (WP.mono (WP.hkeep (by decide) (cmp_ok s₃ 16 16 (by decide)))
    fun s₄ ⟨⟨hcf₄, g₄, l₄, m₄, rd₄, wr₄⟩, hh₄⟩ => ?_)
  have hI₄ := hI₃.of_eq g₄ l₄ m₄ rd₄ wr₄
  have hle := hI₃.a.le
  rw [hI₃.r9, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by decide)] at hcf₄
  refine WP.seq (WP.mono (loopDRM_ok hm hf hI₄ hcf₄ (hCache₃.keep hh₄ (hI₄.a.keys hm)))
    fun s₅ ⟨e, hlt, hI₅, _⟩ => ?_)
  have hle₅ := hI₅.a.le
  exact WP.mono (StitchZ.dfinalM_ok hm (by omega) hI₅) fun _ h => h.toDPostTo

end VG.Proof.Gcm.X86_64.StitchZH

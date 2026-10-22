module

public import VerifiedGarbage.Impl.Gcm.X86_64.Prepare16
public import VerifiedGarbage.Spec.Gcm.Prepared16
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Ok
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Setup
import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
import VerifiedGarbage.Proof.Gcm.X86_64.PrepareCT
import VerifiedGarbage.Proof.Gcm.Poly
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Gcm.X86_64.Prepare16
meta import VerifiedGarbage.Spec.Gcm.Prepared16
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Ok
meta import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Setup
meta import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Base
meta import VerifiedGarbage.Proof.Gcm.X86_64.PrepareCT
meta import VerifiedGarbage.Proof.Gcm.Poly
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# `vg_aes_gcm_prepare16` on 256-bit registers

`prepare16_ok`: `setupG` computes `H'`–`H'¹⁶`, which are stored as pairs 0–7
of the context, as in `Prepare.prepare_ok`'s first pass, and nothing else is
written. `prepare16_ct`: only the context's address affects timing.
`prepare16_verified`: `Spec.Gcm.prepare16Contract`.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.Prepare16

open VG VG.X86_64 VG.Proof.Gcm.Poly
open VG.Impl.Gcm.X86_64.Prepare16 (prepare16)
open VG.Impl.Gcm.X86_64.Vpclmul (preg16)
open VG.Impl.Gcm.X86_64.Stitch (setupG storesK pregs)
open VG.Proof.Gcm.X86_64.Stitch (setupG_ok' storesK_ok in_sub_int)
open VG.Proof.Gcm.X86_64.Prepare (stored vzu_ok pregs_rev_length bytesAt_frame satState)

/-- `vg_aes_gcm_prepare16`'s contract, on the registers. -/
def prepare16X86_64 : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .rdi, 1024⟩] ∧ (s.gpr .rdi).toNat + 1024 ≤ 2 ^ 64 ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 1024⟩
  post s s' := Spec.Aes.bytesAt s'.mem (s.gpr .rdi) 256 = Spec.Aes.bytesAt s.mem (s.gpr .rdi) 256 ∧
    Spec.Gcm.PreparedPowers16Repr s'.mem (s.gpr .rdi)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi

theorem prepare16_ct : ConstantTime isa prepare16X86_64.pre prepare16X86_64.pub prepare16 := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; exact h

/-- What `vg_aes_gcm_prepare16` does from `s₀`: the 16 prepared powers of the
hash subkey at `C + 240` into pairs 0–7 of the context at `C`, nothing else
written, and the registers but `rax` kept. -/
def PrepOk16 (s₀ s : State) : Prop :=
  (∀ k < 8, ∀ l < 2, s.mem.readW (s₀.gpr .rdi + BitVec.ofNat 64 (256 + 32 * k + 16 * l)) 128 =
    Spec.Gcm.preparedPower (Spec.Gcm.hpow (Spec.Gcm.ctxH s₀.mem (s₀.gpr .rdi)) (2 * k + 2 - l))) ∧
  Frame [⟨s₀.gpr .rdi + BitVec.ofNat 64 256, 256⟩] s₀.mem s.mem ∧
  (∀ r, r ≠ .rax → s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr

/-- `prepare16`: the 16 prepared powers of the hash subkey at `C + 240` into
pairs 0–7 of the context at `C`, nothing else written. -/
theorem prepare16_ok {s₀ : State} (hw : InRegions s₀.wr (s₀.gpr .rdi) 1024)
    (hwrap : (s₀.gpr .rdi).toNat + 1024 ≤ 2 ^ 64) :
    WP isa prepare16 s₀ (PrepOk16 s₀) := by
  set C := s₀.gpr .rdi with hC
  set H := Spec.Gcm.ctxH s₀.mem C with hH
  have hk : InRegions (s₀.rd ++ s₀.wr) C 256 := by
    obtain ⟨r, hr, hc⟩ := hw
    exact ⟨r, List.mem_append_right _ hr, by simp only [Region.Contains] at hc ⊢; omega⟩
  simp only [prepare16, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (setupG_ok' hk) fun s₁ ⟨_, _, pw, g₁, m₁, rd₁, wr₁⟩ => ?_
  have r₁ : s₁.gpr .rdi = C := g₁ _ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (storesK_ok .rdi pregs.reverse 8 s₁
    (fun k hk' => by rw [wr₁, r₁]; exact in_sub_int hw (by rw [pregs_rev_length] at hk'; omega))
    (by rw [r₁, pregs_rev_length]; exact Nat.le_trans (by omega) hwrap))
    fun s₂ ⟨sv₂, fr₂, g₂, rd₂, wr₂, ln₂⟩ => ?_
  rw [r₁] at sv₂ fr₂
  have P0 := stored (H := H) (j := 8) (d := 0) rfl (by decide) sv₂ (fun k hk l hl => by
    rw [pw k hk l hl, Nat.add_zero]; rfl)
  refine WP.mono (vzu_ok s₂) fun s ⟨g, m, rd, wr⟩ => ⟨fun k hk l hl => ?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · rw [m]
    have := P0 k hk l hl
    rw [show 8 - 8 + k = k by omega] at this
    exact this
  · rw [m, ← m₁]; exact fr₂
  · rw [g, g₂, g₁ r hr]
  · rw [rd, rd₂, rd₁]
  · rw [wr, wr₂, wr₁]

theorem correct16 {s₀ : State} (hp : prepare16X86_64.pre s₀) :
    WP isa prepare16 s₀ fun s => gprPreserved s₀ s ∧ prepare16X86_64.post s₀ s := by
  obtain ⟨_, hwr, hwrap, hret⟩ := hp
  have hw : InRegions s₀.wr (s₀.gpr .rdi) 1024 := by
    rw [hwr]; exact ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  refine WP.mono (prepare16_ok hw hwrap) fun s ⟨pw, fr, g, _, _⟩ => ?_
  have keep : Spec.Aes.bytesAt s.mem (s₀.gpr .rdi) 256 = Spec.Aes.bytesAt s₀.mem (s₀.gpr .rdi) 256 :=
    bytesAt_frame fr (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact Offset.base_disjoint _ (by decide) (by omega)) (by decide)
  have hH : Spec.Gcm.ctxH s.mem (s₀.gpr .rdi) = Spec.Gcm.ctxH s₀.mem (s₀.gpr .rdi) := by
    simp only [Spec.Gcm.ctxH, Spec.Gcm.blockAt]
    rw [bytesAt_frame fr (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact (Offset.disjoint (s₀.gpr .rdi) (d := 240) (n := 16) (e := 256) (k := 256) (.inl (by decide)) (by decide)
        (by omega)).sub_left (Region.sub_prefix (Nat.le_refl _))) (by decide)]
  refine ⟨⟨fun r hr => g r (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), ?_⟩, keep, fun k hk => ?_⟩
  · exact fr.readW (Region.contains_self _ _) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact hret.sub_right (Offset.sub_base (s₀.gpr .rdi) (by decide))) (by decide)
  · rw [hH]
    have p0 := pw k hk 0 (by decide)
    have p1 := pw k hk 1 (by decide)
    rw [Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at p0
    rw [show 256 + 32 * k + 16 * 1 = 272 + 32 * k by omega, show 2 * k + 2 - 1 = 2 * k + 1 by omega] at p1
    exact ⟨p0, p1⟩

theorem prepare16_correct (s : State) (hs : prepare16X86_64.pre s) :
    ∃ t s', Exec isa prepare16 s t s' ∧ abiPreserved s s' ∧ prepare16X86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct16 hs
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem prepare16_verified :
    Verified X86_64.target prepare16 (Spec.Gcm.prepare16Contract X86_64.abi) :=
  Verified.of_correct prepare16_correct prepare16_ct (by
    sig_implies [Spec.Gcm.prepare16Contract, Spec.Gcm.prepareSig, Spec.Gcm.prepare16Post, prepare16X86_64,
      X86_64.abi, X86_64.argRegs] [satState] using satState)

end VG.Proof.Gcm.X86_64.Prepare16

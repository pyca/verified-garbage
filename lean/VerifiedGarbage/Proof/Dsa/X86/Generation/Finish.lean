module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Search
import VerifiedGarbage.Proof.Dsa.X86.Generation.Copy
import VerifiedGarbage.Proof.Dsa.X86.FailureLoop
import VerifiedGarbage.Proof.Bignum.X86.CopyRead
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Dsa.X86.Generation.Flags
import VerifiedGarbage.Proof.Dsa.X86.Generation.Words

/-! # The result: p||q||g to `out` and 1, or zeros and 0 -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)

/-- What `out` holds for the search's result. -/
def outBytes (g : Geo) : Option Spec.Dsa.Params → List Byte
  | none => List.replicate (2 * g.pLen + g.qLen) 0
  | some a => Spec.Dsa.encodeParams g.pLen g.qLen a

/-- The return value for the search's result. -/
def outStatus : Option Spec.Dsa.Params → Nat
  | none => 0
  | some _ => 1

/-- After the result. -/
structure FPost (E : Env) (g : Geo) (R : Option Spec.Dsa.Params) (s t : State) : Prop where
  out : Spec.Rsa.bytesAt t.mem E.out (2 * g.pLen + g.qLen) = outBytes g R
  eax : t.gpr .eax = BitVec.ofNat 32 (outStatus R)
  frame : Frame [E.outRegion] s.mem t.mem
  edi : t.gpr .edi = s.gpr .edi
  esp : t.gpr .esp = s.gpr .esp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  syms : t.syms = s.syms

theorem finish_ok {g : Geo} (G : GeoOk g) {E : Env} (v : E.Valid) (hp : E.pLen = g.pLen) (hq : E.qLen = g.qLen)
    {s : State} (B : Base E s) {R : Option Spec.Dsa.Params} (hR : SRes E g s.mem R) :
    WP isa g.finish s (FPost E g R s) := by
  have sz := v.size_ge
  have bd := G.bounds
  have nw := v.scratchFit
  have of := v.outFit
  have op := v.ptrs.1
  have oL : E.outLen = 2 * g.pLen + g.qLen := by simp only [Env.outLen, hp, hq]
  have outW : (E.out.setWidth 32).setWidth 64 = E.out := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt op, Nat.mod_eq_of_lt (by omega)]
  have outN : (E.out.setWidth 32).toNat = E.out.toNat := by rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt op]
  have lenN : 2 * g.pLen + g.qLen < 2 ^ 32 := by omega
  obtain ⟨F, hF, hFv⟩ : ∃ F, s.mem.readW (off E.base fStatus) 32 = BitVec.ofNat 32 F ∧
      (F = 1 ↔ R.isSome) ∧ F < 2 ^ 32 := by
    rcases R with _ | a
    · exact ⟨2, hR, by simp, by decide⟩
    · exact ⟨1, hR.1, by simp, by decide⟩
  unfold Geo.finish
  simp only [seqs]
  refine WP.seq (cmpF_end B.scr (o := fStatus) (v := 1) (by simp only [fStatus, hdr]; omega) hF hFv.2 (by decide)
    fun t₁ g₁ m₁ rd₁ wr₁ sy₁ z₁ => ?_)
  have hs₁ : Scr t₁ E.base E.size := Scr.of_eq B.scr (g₁ _ (by decide)) (g₁ _ (by decide)) wr₁
  refine WP.ite _ z₁ (fun h1 => ?_) (fun h1 => ?_)
  · -- p||q||g out.
    obtain ⟨a, rfl⟩ : ∃ a, R = some a := Option.isSome_iff_exists.mp (hFv.1.mp (of_decide_eq_true h1))
    simp only [List.cons_append, List.nil_append]
    refine WP.seq (ld_ok hs₁ (r := .ebx) (d := fOut) (by simp only [fOut, hdr]; omega) fun t₂ u₂ =>
      scr_ok fun t₃ e₃ g₃ m₃ rd₃ wr₃ sy₃ => wp_movi fun t₄ u₄ => WP.block_nil ?_)
    have ebx₄ : t₄.gpr .ebx = E.out.setWidth 32 := by
      rw [u₄.other _ (by decide), g₃ _ (by decide), u₂.gpr, m₁, B.outW]
    have esi₄ : t₄.gpr .esi = s.gpr .edi + BitVec.ofNat 32 sPk := by
      rw [u₄.other _ (by decide), e₃, u₂.other _ (by decide), g₁ _ (by decide)]
    have m₄ : t₄.mem = s.mem := by rw [u₄.mem, m₃, u₂.mem, m₁]
    have rd₄ : t₄.rd = s.rd := by rw [u₄.rd, rd₃, u₂.rd, rd₁]
    have wr₄ : t₄.wr = s.wr := by rw [u₄.wr, wr₃, u₂.wr, wr₁]
    have hs := B.scr
    have pW := Scr.wide hs (d := sPk) (by simp only [sPk]; omega)
    have pN := Scr.toNat_add hs (d := sPk) (by simp only [sPk]; omega)
    refine WP.seq (VG.X86.WP.mono_syms (VG.Proof.Bignum.X86.copyBuffers_ok (src := s.gpr .edi + BitVec.ofNat 32 sPk)
      (dst := E.out.setWidth 32) (n := 2 * g.pLen + g.qLen) (by omega) lenN (by rw [pN]; simp only [sPk]; omega)
      (by rw [outN]; simp only [Env.outLen, hp, hq] at of; omega)
      (by rw [VG.Proof.Bignum.X86.byteAddr, pW, rd₄, wr₄]; exact hs.read (by simp only [sPk]; omega))
      (by rw [VG.Proof.Bignum.X86.byteAddr, outW, wr₄]
          exact ⟨_, B.out, by simp only [Env.outRegion, oL]; exact contains_start _ (Nat.le_refl _)⟩)
      (by rw [VG.Proof.Bignum.X86.byteAddr, pW, VG.Proof.Bignum.X86.byteAddr, outW]
          exact (v.outScratch.symm.sub_left (Offset.sub_base _ (by simp only [sPk]; omega))).sub_right
            (by intro x hx; simp only [Env.outRegion, oL]; exact hx))
      esi₄ ebx₄ u₄.gpr) fun t₅ ⟨R₅, _, _, F₅, K₅⟩ sy₅ => ?_)
    refine wp_movi fun t₆ u₆ => WP.block_nil ⟨?_, u₆.gpr, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [VG.Proof.Bignum.X86.byteAddr, outW, pW, m₄] at R₅
      rw [u₆.mem, bytesAt_of_read R₅]; exact hR.2
    · rw [u₆.mem]
      simp only [VG.Proof.Bignum.X86.byteAddr, outW, m₄] at F₅
      intro x hx; exact F₅ x fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hx E.outRegion (List.mem_singleton_self _) |> fun h => by simpa [Env.outRegion, oL] using h
    · rw [u₆.other _ (by decide), K₅.1 _ (by decide), u₄.other _ (by decide), g₃ _ (by decide),
        u₂.other _ (by decide), g₁ _ (by decide)]
    · rw [u₆.other _ (by decide), K₅.1 _ (by decide), u₄.other _ (by decide), g₃ _ (by decide),
        u₂.other _ (by decide), g₁ _ (by decide)]
    · rw [u₆.rd, K₅.2.1, rd₄]
    · rw [u₆.wr, K₅.2.2, wr₄]
    · rw [u₆.syms, sy₅, u₄.syms, sy₃, u₂.syms, sy₁]
  · -- Zeros out.
    have hn : R = none := by
      rcases R with _ | a
      · rfl
      · exact absurd (hFv.1.mpr rfl) (of_decide_eq_false h1)
    subst hn
    refine WP.seq (ld_ok hs₁ (r := .esi) (d := fOut) (by simp only [fOut, hdr]; omega) fun t₂ u₂ =>
      wp_movi fun t₃ u₃ => wp_movi fun t₄ u₄ => WP.block_nil ?_)
    refine WP.seq (VG.X86.WP.mono_syms (VG.Proof.Dsa.X86.failureLoop_ok (out := E.out.setWidth 32)
      (len := 2 * g.pLen + g.qLen) (by omega) lenN (by rw [outN]; simp only [Env.outLen, hp, hq] at of; omega)
      (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, m₁, B.outW])
      (by rw [u₄.other _ (by decide), u₃.gpr]) u₄.gpr (fun i hi => by
        rw [u₄.wr, u₃.wr, u₂.wr, wr₁, outW]
        exact ⟨_, B.out, by simp only [Env.outRegion, oL]; exact Offset.contains_base _ (by omega) (by omega)⟩))
      fun t₅ ⟨V₅, _, O₅, K₅⟩ sy₅ => ?_)
    refine wp_movi fun t₆ u₆ => WP.block_nil ⟨?_, u₆.gpr, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₆.mem]; rw [outW] at V₅; exact V₅
    · rw [u₆.mem]
      rw [outW] at O₅
      intro x hx
      have hc := hx E.outRegion (List.mem_singleton_self _)
      have := O₅ x (.inr (by
        simp only [Region.Contains, Env.outRegion, oL] at hc
        show 0 + (2 * g.pLen + g.qLen) ≤ (x - E.out).toNat
        omega))
      rw [this, u₄.mem, u₃.mem, u₂.mem, m₁]
    · rw [u₆.other _ (by decide), K₅.1 _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), g₁ _ (by decide)]
    · rw [u₆.other _ (by decide), K₅.1 _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), g₁ _ (by decide)]
    · rw [u₆.rd, K₅.2.1, u₄.rd, u₃.rd, u₂.rd, rd₁]
    · rw [u₆.wr, K₅.2.2, u₄.wr, u₃.wr, u₂.wr, wr₁]
    · rw [u₆.syms, sy₅, u₄.syms, u₃.syms, u₂.syms, sy₁]

end VG.Proof.Dsa.X86.Generation

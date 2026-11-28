module

-- separate module: the whole function's correctness, which the constant-time proof does not change

public import VerifiedGarbage.Proof.SlhDsa.AArch64.VerifyXmssPk
import VerifiedGarbage.Proof.SlhDsa.AArch64.TopLanes
import VerifiedGarbage.Proof.SlhDsa.AArch64.TopIdx
import VerifiedGarbage.Proof.SlhDsa.Lemmas
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64, `xmssPk`

The whole function from `xmssPkContract`'s precondition: the prologue and
the digits (`entry_ok`), the chains (`chains_ok`), the WOTS⁺ public key
(`wotsPk_ok`), the path (`path_ok`), and the root to `oMsg`
(`xmssPk_wp`), which is `xmssPkFromSig` (`xmssPkFromSig_eq`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.XmssPk

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt shake256)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Proof.MlKem.AArch64 (Only Keep)
open VG.Proof.SlhDsa (adrsOf)
open VG.Proof.SlhDsa.AArch64.TreeBase (Up in_scr in_scr' wp_mov wp_movz)

variable {p : Params}

theorem restore_eq : Impl.SlhDsa.AArch64.restoreRegs 1 Impl.SlhDsa.AArch64.Verify.xsaved =
    Impl.SlhDsa.AArch64.restoreRegsAt 1152 [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x30] := rfl

/-- The WOTS⁺ public key the code computes is the specification's. -/
theorem node0_eq (hz : Sz p) {σ : State} {sig : Addr} {pk a M : List Byte} (ha : a.length = 16)
    (hidx : (σ.gpr .x1).toNat < 2 ^ 32) :
    shake256 (pk ++ adrsOf a 1 (σ.gpr .x1).toNat 0 0 ++
        (List.range p.len).flatMap (chainEnd p σ sig pk a (wotsDigits p M))) p.n =
      wotsPkFromSig p ((bytesAt σ.mem sig p.xmssSigLen).take (p.len * p.n)) M pk
        (adrsOf a 0 (σ.gpr .x1).toNat 0 0) := by
  have hsl : p.len * p.n ≤ p.xmssSigLen := by rw [xmssSigLen_eq']; omega
  rw [wotsPkFromSig_eq p ha hidx, bytesAt_take' _ _ hsl]
  simp only [T, hz.shake, shakeAdrs]
  refine congrArg (fun x => shake256 (pk ++ adrsOf a 1 (σ.gpr .x1).toNat 0 0 ++ x) p.n) ?_
  refine flatMap_range_congr fun c hc => ?_
  have hw : p.w - 1 = 15 := by simp only [Params.w, hz.lgw]
  have hcn : p.n * c + p.n ≤ p.len * p.n := by
    rw [Nat.mul_comm p.n c, ← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
  simp only [chainEnd, Xc, chunk, hw]
  rw [bytesAt_drop_take _ _ hcn, Nat.mul_comm p.n c]

/-- `xmssPk`, from its precondition: its postcondition and the calling convention. -/
theorem xmssPk_wp (hz : Sz p) (T : Thash4Impl p.n) {f : Impl.SlhDsa.AArch64.Shake.Fns} (ht : f.t4 = T.code)
    (hh1 : 1 ≤ p.hp) (hh : p.hp ≤ 9) {s : State} (hpre : (xmssPkContract p).pre s) :
    WP isa (Impl.SlhDsa.AArch64.Verify.xmssPk p f) s fun s' =>
      abiPreserved s s' ∧ (xmssPkContract p).post s s' := by
  have hn32 := hz.n32
  have hn8 := hz.n8
  have eA : Layout.laneA 0 = 3136 := rfl
  have eM : Layout.oMsg = 1984 := rfl
  have h8n : 8 * (p.n / 8) = p.n := by omega
  obtain ⟨hR, ⟨pk, a, hE⟩, hidx⟩ := hpre
  generalize hS : s.gpr .x0 = S at hR hE
  have hidx32 : (s.gpr .x1).toNat < 2 ^ 32 :=
    Nat.lt_of_lt_of_le hidx (Nat.pow_le_pow_right (by decide) (by omega))
  have ha := TreeBase.env_a16 hE
  have hwS := TreeBase.regions_scr hR
  obtain ⟨M, eM'⟩ : ∃ M, bytesAt s.mem (at' S Layout.oMsg) p.n = M := ⟨_, rfl⟩
  have hD : ∀ i < p.len, (wotsDigits p M).getD i 0 < 16 := fun i _ => by
    have := wotsDigits_getD_lt (p := p) M i
    simp only [Params.w, hz.lgw] at this; exact this
  unfold Impl.SlhDsa.AArch64.Verify.xmssPk
  refine WP.seq (WP.mono (entry_ok hz hS hR hE) fun u ⟨hu, h22⟩ => ?_)
  rw [eM'] at hu
  refine WP.seq (WP.mono (chains_ok hz T ht hR hidx32 ha hD hu h22) fun u₁ ⟨X₁, hE₁⟩ => ?_)
  refine WP.seq (WP.mono (wotsPk_ok hz T ht hR hidx32 X₁ hE₁) fun u₂ ⟨X₂, hW⟩ => ?_)
  refine WP.seq (wp_movz fun u₃ v₃ => wp_mov fun u₄ v₄ => MlKem.AArch64.wp_nil ?_)
  have K4 : Keep [.x25, .x26] u₂ u₄ := (upOnly v₃).keep.trans (upOnly v₄).keep
  have m4 : u₄.mem = u₂.mem := by rw [v₄.mem, v₃.mem]
  have P₀ : PI p s S (s.gpr .x2) pk a (wotsDigits p M) (shake256 (pk ++ adrsOf a 1 (s.gpr .x1).toNat 0 0 ++
      (List.range p.len).flatMap (chainEnd p s (s.gpr .x2) pk a (wotsDigits p M))) p.n) 0 u₄ :=
    ⟨XK.step hz X₂ (by decide) K4 (by rw [m4]; exact Frame.refl _ _) (fun r hr => absurd hr List.not_mem_nil),
      by rw [v₄.other _ (by decide), v₃.gpr]; rfl,
      by rw [v₄.gpr, v₃.other _ (by decide), X₂.x20, Nat.pow_zero, Nat.div_one]; exact ofNat_of_toNat rfl,
      by rw [m4, hW, path]⟩
  refine WP.seq (WP.mono (path_ok hz T ht hR hidx32 hh1 hh P₀) fun w hw => ?_)
  have hw' : (⟨S, 65536⟩ : Region) ∈ w.wr := by rw [hw.xk.wr]; exact hwS
  rw [restore_eq]
  refine copyWords_ok (t := .x19) (sr := .x19) (d₂ := Layout.oMsg) (d₁ := Layout.laneA 0 + (p.n + 32)) (w := p.n / 8)
    ⟨by decide, by decide, ⟨by rw [eA]; omega, by rw [eA]; omega⟩, ⟨by decide, by rw [eM]; omega⟩,
      by rw [hw.xk.x19, h8n]; exact in_scr' hw' (by rw [eA]; omega),
      by rw [hw.xk.x19, h8n]; exact in_scr hw' (by rw [eM]; omega),
      by rw [hw.xk.x19, h8n]; exact Offset.disjoint S (by rw [eA, eM]; omega) (by rw [eM]; omega) (by rw [eA]; omega)⟩
    fun w₁ k₁ f₁ c₁ => ?_
  rw [hw.xk.x19, h8n] at f₁ c₁
  have X₅ : XK p s S (s.gpr .x2) pk a (wotsDigits p M) w₁ := XK.step hz hw.xk (by decide) k₁ f₁ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨_, _, rfl, .inr (.inl ⟨Nat.le_refl _, by omega⟩)⟩)
  rw [← List.append_nil (Impl.SlhDsa.AArch64.restoreRegsAt _ _)]
  refine restoreRegsAt_ok (by decide) (by decide)
    (by rw [X₅.x19, X₅.rd, X₅.wr, ← hw.xk.wr]; exact in_scr' hw' (by simp only [List.length_cons, List.length_nil]; omega))
    fun t' o' g' => MlKem.AArch64.wp_nil ?_
  have hg : ∀ (i : Nat) (h : i < 9), t'.gpr ([Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x30][i]) =
      s.gpr ([Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x30][i]) := fun i h => by
    rw [g' i h, X₅.x19]
    have := X₅.saved ([Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x30][i], 1152 + 8 * i) (by
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [slotsX])
    exact this
  refine ⟨⟨fun r hr => ?_, by rw [o'.sp, X₅.sp], fun r hr => by rw [o'.vcs r hr, X₅.vcs r hr]⟩,
    fun pk' a' hE' => ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg 0 (by decide)
    · exact hg 1 (by decide)
    · exact hg 2 (by decide)
    · exact hg 3 (by decide)
    · exact hg 4 (by decide)
    · exact hg 5 (by decide)
    · exact hg 6 (by decide)
    · exact hg 7 (by decide)
    · rw [o'.gpr _ (by decide)]; exact X₅.kept _ (by decide)
    · rw [o'.gpr _ (by decide)]; exact X₅.kept _ (by decide)
    · exact hg 8 (by decide)
  simp only [hS] at hE' ⊢
  obtain ⟨rfl, rfl⟩ := TreeBase.env_unique hE hE'
  refine ⟨by rw [o'.mem]; exact X₅.env, ?_, by rw [o'.mem]; exact X₅.frame⟩
  rw [o'.mem, c₁, show Layout.laneA 0 + (p.n + 32) = Layout.laneA 0 + p.n + 32 by omega, hw.node, eM',
    xmssPkFromSig_eq p ha hidx32, node0_eq hz ha hidx32]

end VG.Proof.SlhDsa.AArch64.XmssPk

module

import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Search
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Finish
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Entry
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.SLoop
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # DSA parameter generation on PPC64LE: the body

`body_vp`: from the call's entry, the header written (`entry_vp`), the
search and the exit of the geometry the modulus's width selects
(`dispatch_vp`, each geometry given by a `GeoOk`), and our caller's
registers restored (`restore_vp`): `Done`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

/-- A geometry's proofs, for every call with its `p_len` (and so its `q_len`). -/
structure GeoOk (g : Geo) (pL qL : Nat) where
  HO : HashOk g.G
  Lq : Impl.Dsa.ProbablePrime.Layout
  Lp : Impl.Dsa.ProbablePrime.Layout
  ok : ∀ G : GP, (∃ σ, CIn 176 σ ∧ mkG σ = G) → G.pLen = pL → G.qLen = qL → GenOk G g HO Lq Lp
  hlb : HO.md.lenBytes qL =
    [0, 0, 0, 0, 0, 0, BitVec.ofNat 8 (8 * qL / 256), BitVec.ofNat 8 (8 * qL % 256)]

/-- How the search ends. -/
abbrev oOf (G : GP) : COut := cOut G (sCount G G.k0 0 0)

section
variable {G : GP}

/-- The call's entry, for the public parameters `G`. -/
abbrev AE (G : GP) (σ u : State) : Prop := u = σ ∧ CIn 176 σ ∧ mkG σ = G

/-- After the entry. -/
abbrev E1 (G : GP) (σ s : State) : Prop := GI G 176 σ (eV G) entryLS s ∧ s.gpr .r12 = BitVec.ofNat 64 G.pLen

theorem entry_vp : VP (AE G) (.block entry) (E1 G) := by
  refine VP.taint [.r8, .r10] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r8, .r10]) (.block entry),
      by kernel_rfl⟩
    (fun σ₁ σ₂ s₁ s₂ ⟨e₁, _, g₁⟩ ⟨e₂, _, g₂⟩ => by
      subst e₁ e₂
      show (mkG s₁).sp = (mkG s₂).sp
      rw [g₁, g₂])
    (fun σ₁ σ₂ s₁ s₂ ⟨e₁, _, g₁⟩ ⟨e₂, _, g₂⟩ r hr => by
      subst e₁ e₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · show (mkG s₁).scr = (mkG s₂).scr; rw [g₁, g₂]
      · show (mkG s₁).stP = (mkG s₂).stP; rw [g₁, g₂]) fun σ u ⟨hu, pre, hG⟩ => ?_
  subst hu hG
  exact entry_ok pre

theorem toNat_eq_ofNat {x : BitVec 64} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 64 n := by
  rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `subi r0, r12, x`: whether the modulus's width is `x`. -/
theorem cmpP_vp {x : Nat} (hx : x ≤ 2 ^ 15) :
    VP (E1 G) (.block [.subi .r0 .r12 x])
      (fun σ s => E1 G σ s ∧ isa.eval (.zero .d .r0) s = some (decide (G.pLen = x))) := by
  refine VP.taint [.r12] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r12])
      (.block [.subi .r0 .r12 x]), by kernel_rfl⟩ (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
        have e₁ : σ₁.sp = G.sp := by rw [← h₁.1.hG]; rfl
        have e₂ : σ₂.sp = G.sp := by rw [← h₂.1.hG]; rfl
        rw [h₁.1.sp, h₂.1.sp, e₁, e₂])
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]) fun σ s h => ?_
  have p384 : G.pLen ≤ 384 := by rcases h.1.lens3 with e | e | e <;> rw [e] <;> decide
  refine WP.wr (exec_subi (by decide) hx) fun t u sp _ => WP.block_nil ⟨⟨h.1.of_upd u sp (by decide), ?_⟩, ?_⟩
  · rw [u.other _ (by decide)]; exact h.2
  · rw [eval_zero, u.gpr, h.2, sub_beq_zero]
    by_cases hp : G.pLen = x
    · subst hp; simp
    · rw [decide_eq_false hp]
      refine congrArg some (beq_false_of_ne fun e' => hp ?_)
      have := congrArg BitVec.toNat e'
      simp only [BitVec.toNat_ofNat] at this
      omega

/-- A geometry's search and exit. -/
theorem gen_vp {g : Geo} {pL qL : Nat} (K : GeoOk g pL qL) (hex : ∃ σ, CIn 176 σ ∧ mkG σ = G)
    (hp : G.pLen = pL) (hq : G.qLen = qL) {F : State → State → Prop} (hF : ∀ σ s, F σ s → E1 G σ s) :
    VP F g.generate (fun σ t => FO G (oOf G) σ t ∧ cRes G (oOf G) = sW G) := by
  have O := K.ok G hex hp hq
  by_cases hf : cRes G (oOf G) = sW G ∧ cOk G (oOf G)
  · refine VP.seq ((search_vp (X := fun _ => True) O (by rw [hq]; exact K.hlb) (by decide)
      (by simp [eV]) (by decide) (by simp [eV, fStatus, fSeedLeft]) (by decide)
      (by simp [eV, fC, fSeedLeft])).mono (fun σ s h => ⟨(hF σ s h).1, trivial⟩) fun σ s h => h.1)
      ((finish_vp O.hp O.hq _ hf.2 O.h64).mono (fun _ _ h => h) fun σ t h => ⟨h.1, hf.1⟩)
  · exact VP.seq ((search_vp (X := fun _ => True) O (by rw [hq]; exact K.hlb) (by decide)
      (by simp [eV]) (by decide) (by simp [eV, fStatus, fSeedLeft]) (by decide)
      (by simp [eV, fC, fSeedLeft])).mono (fun σ s h => ⟨(hF σ s h).1, trivial⟩) fun σ s h => h)
      (VP.of_false fun σ s h => hf h.2)

/-- The geometry the modulus's width selects. -/
theorem dispatch_vp {g1 g2 g3 : Geo} (K1 : GeoOk g1 128 20) (K2 : GeoOk g2 256 32) (K3 : GeoOk g3 384 32) :
    VP (E1 G) (dispatch g1 g2 g3) (fun σ t => FO G (oOf G) σ t ∧ cRes G (oOf G) = sW G) := by
  refine (VP.intro (P := ∃ σ, CIn 176 σ ∧ mkG σ = G) fun hex => ?_).mono
    (fun σ s h => ⟨⟨σ, h.1.pre, h.1.hG⟩, h⟩) fun _ _ h => h
  obtain ⟨σ₀, pre₀, hG₀⟩ := hex
  have hl : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32) := by
    rw [← hG₀]; exact pre₀.lens
  unfold dispatch
  refine VP.seq (cmpP_vp (G := G) (x := 128) (by decide)) ?_
  have hc : ∀ {F : State → State → Prop} {b : Prop} [Decidable b],
      (∀ σ s, F σ s → isa.eval (.zero .d .r0) s = some (decide b)) →
      ∀ σ₁ σ₂ s₁ s₂, F σ₁ s₁ → F σ₂ s₂ → isa.eval (.zero .d .r0) s₁ = isa.eval (.zero .d .r0) s₂ :=
    fun hF _ _ _ _ h₁ h₂ => by rw [hF _ _ h₁, hF _ _ h₂]
  have no : ∀ {F : State → State → Prop} {c : Prog isa} {Q : State → State → Prop} {b : Bool} {p : Prop}
      [Decidable p], ¬ (decide p = b) →
      VP (fun σ s => (F σ s ∧ isa.eval (.zero .d .r0) s = some (decide p)) ∧
        isa.eval (.zero .d .r0) s = some b) c Q :=
    fun hb => VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => hb (by rw [e] at z; exact Option.some.inj z)
  rcases hl with ⟨h1, h1'⟩ | ⟨h2, h2'⟩ | ⟨h3, h3'⟩
  · refine VP.ite (hc fun σ s h => h.2) (gen_vp K1 ⟨σ₀, pre₀, hG₀⟩ h1 h1' fun σ s h => h.1.1)
      (no (by simp [h1]))
  · refine VP.ite (hc fun σ s h => h.2) (no (by simp [h2]))
      (VP.seq ((cmpP_vp (G := G) (x := 256) (by decide)).mono (fun σ s h => h.1.1) fun _ _ h => h)
        (VP.ite (hc fun σ s h => h.2) (gen_vp K2 ⟨σ₀, pre₀, hG₀⟩ h2 h2' fun σ s h => h.1.1) (no (by simp [h2]))))
  · refine VP.ite (hc fun σ s h => h.2) (no (by simp [h3]))
      (VP.seq ((cmpP_vp (G := G) (x := 256) (by decide)).mono (fun σ s h => h.1.1) fun _ _ h => h)
        (VP.ite (hc fun σ s h => h.2) (no (by simp [h3])) (gen_vp K3 ⟨σ₀, pre₀, hG₀⟩ h3 h3' fun σ s h => h.1.1)))

/-- Done: our caller's registers back, and the results of `FO`. -/
structure Done (G : GP) (σ t : State) : Prop where
  pre : CIn 176 σ
  hG : mkG σ = G
  abi : abiPreserved σ t
  fo : ∃ u, FO G (oOf G) σ u ∧ t.mem = u.mem ∧ t.gpr .r3 = u.gpr .r3
  res : cRes G (oOf G) = sW G

theorem restore_vp : VP (fun σ t => FO G (oOf G) σ t ∧ cRes G (oOf G) = sW G) (.block restore) (Done G) := by
  refine VP.pub (G := G) (fun σ s h => ⟨h.1.r28, by rw [h.1.sp, ← h.1.hG]; rfl⟩) []
    ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28]) (.block restore), by kernel_rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨h, r⟩ => ?_
  exact WP.mono h.restore fun t ⟨abi, m, r3⟩ => ⟨h.pre, h.hG, abi, ⟨s, h, m, r3⟩, r⟩

theorem body_vp {g1 g2 g3 : Geo} (K1 : GeoOk g1 128 20) (K2 : GeoOk g2 256 32) (K3 : GeoOk g3 384 32) :
    VP (AE G) (code g1 g2 g3) (Done G) :=
  entry_vp.seq ((dispatch_vp K1 K2 K3).seq restore_vp)

end

end VG.Proof.Dsa.PPC64LE.Gen

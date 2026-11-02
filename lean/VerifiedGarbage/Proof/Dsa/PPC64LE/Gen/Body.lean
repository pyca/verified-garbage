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
search and the exit of the geometry `p_len` selects (`dispatch_vp`, each
geometry given by a `GeoOk`), and our caller's registers restored
(`restore_vp`): `Done`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE
open VG.Impl.Dsa.PPC64LE.Generation

/-- Two runs of deterministic code reach the same state. -/
theorem WP.both {c : Prog isa} {s : State} {P Q : State → Prop} (h₁ : WP isa c s P) (h₂ : WP isa c s Q) :
    WP isa c s fun t => P t ∧ Q t := by
  obtain ⟨t₁, s₁, e₁, p⟩ := h₁
  obtain ⟨t₂, s₂, e₂, q⟩ := h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ e₂
  exact ⟨t₁, s₁, e₁, p, q⟩

/-- A geometry's proofs, for every call with its `p_len` (and so its `q_len`). -/
structure GeoOk (g : Geo) (pL qL : Nat) where
  HO : HashOk g.G
  Lq : Impl.Dsa.ProbablePrime.Layout
  Lp : Impl.Dsa.ProbablePrime.Layout
  ok : ∀ G : GP, (∃ σ, CIn 176 σ ∧ mkG σ = G) → G.pLen = pL → G.qLen = qL → GenOk G g HO Lq Lp
  hlb : HO.md.lenBytes qL =
    [0, 0, 0, 0, 0, 0, BitVec.ofNat 8 (8 * qL / 256), BitVec.ofNat 8 (8 * qL % 256)]

/-- What the search returns. -/
abbrev sRes (G : GP) : Option Spec.Dsa.Params :=
  Spec.Dsa.generateParameters.attempt (8 * G.pLen) (hsL G) (8 * G.qLen)
    (Spec.Dsa.generationChunks G.qLen G.seedsB) G.witB

section
variable {G : GP}

/-- The call's entry, for the public parameters `G`. -/
abbrev AE (G : GP) (σ u : State) : Prop := u = σ ∧ CIn 176 σ ∧ mkG σ = G

/-- After the entry. -/
abbrev E1 (G : GP) (σ s : State) : Prop := GI G 176 σ (eV G) entryLS s ∧ s.gpr .r5 = σ.gpr .r5

/-- The entry's code after the load of `scratch`'s address. -/
abbrev entryRest : List Instr := entry.drop 2

/-- After the load of `scratch`'s address. -/
abbrev A1 (G : GP) (σ s : State) : Prop := s.gpr .r11 = G.scr ∧ s.sp = G.sp ∧ WP isa (.block entryRest) s (E1 G σ)

theorem entry_vp : VP (AE G) (.block entry) (E1 G) := by
  rw [show entry = [.addSp .r11 (96 + 8 * 2), .load .d .r11 .r11 0] ++ entryRest from rfl]
  refine VP.block_append (G := A1 G) (VP.taint [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [])
      (.block [.addSp .r11 (96 + 8 * 2), .load .d .r11 .r11 0]), by kernel_rfl⟩
      (fun σ₁ σ₂ s₁ s₂ ⟨e₁, _, g₁⟩ ⟨e₂, _, g₂⟩ => by
        subst e₁ e₂
        show (mkG s₁).sp = (mkG s₂).sp
        rw [g₁, g₂])
      (fun _ _ _ _ _ _ r hr => absurd hr (by simp)) fun σ u ⟨hu, pre, hG⟩ => ?_)
    (VP.taint [.r11] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r11]) (.block entryRest), by kernel_rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2.1, h₂.2.1])
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1, h₂.1]) fun σ s h => h.2.2)
  subst hu hG
  have whole := entry_ok (STK := 176) pre
  rw [show entry = [.addSp .r11 (96 + 8 * 2), .load .d .r11 .r11 0] ++ entryRest from rfl,
    WP.block_append_iff] at whole
  have part : WP isa (.block [.addSp .r11 (96 + 8 * 2), .load .d .r11 .r11 0]) u fun s' =>
      s'.gpr .r11 = (mkG u).scr ∧ s'.sp = u.sp :=
    argLoad_ok (r := .r11) (i := 2) pre rfl rfl (by decide) (by decide) (rest := []) fun s₁ u₁ sp₁ _ =>
      WP.block_nil ⟨by rw [u₁.gpr]; rfl, sp₁⟩
  exact WP.mono (WP.both whole part) fun t ⟨w, r11, sp₁⟩ => ⟨r11, sp₁, w⟩

theorem toNat_eq_ofNat {x : BitVec 64} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 64 n := by
  rw [← h, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `subi r0, r5, x`: whether `p_len` is `x`. -/
theorem cmpP_vp {x : Nat} (hx : x ≤ 2 ^ 15) :
    VP (E1 G) (.block [.subi .r0 .r5 x])
      (fun σ s => E1 G σ s ∧ isa.eval (.zero .d .r0) s = some (decide (G.pLen = x))) := by
  have e : ∀ σ s, E1 G σ s → s.gpr .r5 = BitVec.ofNat 64 G.pLen := fun σ s h => by
    rw [h.2]; exact toNat_eq_ofNat (by rw [← h.1.hG]; rfl)
  refine VP.taint [.r5] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r5])
      (.block [.subi .r0 .r5 x]), by kernel_rfl⟩ (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
        have e₁ : σ₁.sp = G.sp := by rw [← h₁.1.hG]; rfl
        have e₂ : σ₂.sp = G.sp := by rw [← h₂.1.hG]; rfl
        rw [h₁.1.sp, h₂.1.sp, e₁, e₂])
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [e _ _ h₁, e _ _ h₂]) fun σ s h => ?_
  have p384 : G.pLen ≤ 384 := by rcases h.1.lens3 with e | e | e <;> rw [e] <;> decide
  refine WP.wr (exec_subi (by decide) hx) fun t u sp _ => WP.block_nil ⟨⟨h.1.of_upd u sp (by decide), ?_⟩, ?_⟩
  · rw [u.other _ (by decide)]; exact h.2
  · rw [eval_zero, u.gpr, e σ s h, sub_beq_zero]
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
    VP F g.generate (fun σ t => FO G (sRes G) σ t ∧ True) := by
  have O := K.ok G hex hp hq
  refine VP.seq ((search_vp (X := fun _ => True) O (by rw [hq]; exact K.hlb) (by decide) (by simp [eV])
    (by decide) (by simp [eV, fSeedLeft, fSeed]) (by decide) (by simp [eV, fStatus, fSeedLeft, fSeed]) (by decide)
    (by simp [eV, fUsed, fSeedLeft, fSeed])).mono (fun σ s h => ⟨(hF σ s h).1, trivial⟩) fun _ _ h => h)
    (finish_vp O.hp O.hq _)

/-- The geometry `p_len` selects. -/
theorem dispatch_vp {g1 g2 g3 : Geo} (K1 : GeoOk g1 128 20) (K2 : GeoOk g2 256 32) (K3 : GeoOk g3 384 32) :
    VP (E1 G) (dispatch g1 g2 g3) (fun σ t => FO G (sRes G) σ t ∧ True) := by
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

/-- Done: our caller's registers back, `out` holding the result and `r3` the status. -/
structure Done (G : GP) (R : Option Spec.Dsa.Params) (σ t : State) : Prop where
  pre : CIn 176 σ
  hG : mkG σ = G
  abi : abiPreserved σ t
  out : Spec.Rsa.bytesAt t.mem G.out G.outLen =
    (R.map (Spec.Dsa.encodeParams G.pLen G.qLen)).getD (List.replicate G.outLen 0)
  r3 : t.gpr .r3 = BitVec.ofNat 64 (if R.isSome then 1 else 0)

theorem restore_vp {R : Option Spec.Dsa.Params} :
    VP (fun σ t => FO G R σ t ∧ True) (.block restore) (Done G R) := by
  refine VP.pub (G := G) (fun σ s h => ⟨h.1.r28, by rw [h.1.sp, ← h.1.hG]; rfl⟩) []
    ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28]) (.block restore), by kernel_rfl⟩
    (fun _ _ _ _ _ _ _ h => absurd h (by simp)) fun σ s ⟨h, _⟩ => ?_
  exact WP.mono h.restore fun t ⟨abi, m, r3⟩ => ⟨h.pre, h.hG, abi, by rw [m]; exact h.out, by rw [r3]; exact h.r3⟩

theorem body_vp {g1 g2 g3 : Geo} (K1 : GeoOk g1 128 20) (K2 : GeoOk g2 256 32) (K3 : GeoOk g3 384 32) :
    VP (AE G) (code g1 g2 g3) (Done G (sRes G)) :=
  entry_vp.seq ((dispatch_vp K1 K2 K3).seq restore_vp)

end

end VG.Proof.Dsa.PPC64LE.Gen

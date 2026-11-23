module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Same
public import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignCall
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Inst
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Lit
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Verified
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseOCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.SignCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Via
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubFns
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Inv
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Entry

/-!
# ML-DSA on x86-64, `sign_message`: the signing functions on `μ` it calls

Untrusted: everything here is checked by Lean. `vg_mldsa*_sign`, with any
implementation `v` of the polynomial arithmetic, is a function
`sign_message` can call (`signFn`): its proofs give its contract, it never
writes `rsp`, and its calls nest at most four deep, which, as whether it
writes `rsp`, is checked on the code with the arithmetic's functions empty
(`Same`), given that theirs nest at most three deep.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlDsa.X86_64 (Comp Same Same.ok ArithImpl Code.allInstrs_of_all)
open VG.Proof.MlDsa.X86_64.Sign (primsWith prims_okWith sign_correct sign_ct sign_ctl sign_same Ok3)
open VG.Spec.MlDsa

/-- Calls nesting at most `n + 1` deep, from functions whose calls nest at most `n` deep. -/
theorem depthCompN (n : Nat) : Comp (fun c => decide (c.depth ≤ n + 1)) (fun c => decide (c.depth ≤ n)) := by
  refine ⟨fun a b => ?_, fun _ t e => ?_, fun _ _ => rfl, fun _ b => ?_, rfl, fun _ _ _ b nx h => ?_⟩
  · simp only [Code.depth, Nat.max_le, Bool.decide_and]
  · simp only [Code.depth, Nat.max_le, Bool.decide_and]
  · simp only [Code.depth]
    exact decide_eq_decide.mpr (by omega_using [])
  · have := of_decide_eq_true h
    simp only [Code.depth]
    exact decide_eq_decide.mpr (by omega_using [this])

/-- `NoSp` from evaluating the code. -/
noncomputable abbrev noSpB (c : Prog isa) : Bool := c.allInstrs fun i => !Taint.clobbers i .rsp

theorem noSp_of {c : Prog isa} (h : noSpB c = true) : NoSp c := Proof.MlKem.X86_64.nosp_of h

theorem noSpB_of {c : Prog isa} (h : NoSp c) : noSpB c = true := by
  rw [noSpB, Code.allInstrs_eq, List.all_eq_true]
  intro i hi; simp [h i hi]

theorem ok3_of {p : Params} (hp : p ∈ params) : Ok3 p := by
  simp only [params, List.mem_cons, List.not_mem_nil, or_false] at hp
  exact hp

theorem sign0_noSp {p : Params} (h3 : Ok3 p) (vs : Bool := false) :
    noSpB (Impl.MlDsa.X86_64.Sign.sign (primsWith .empty vs) p) = true := by
  rcases h3 with rfl | rfl | rfl <;> cases vs
  · exact (by lit_decide : noSpB Sign.sign44 = true)
  · exact (by lit_decide : noSpB Sign.sign44V = true)
  · exact (by lit_decide : noSpB Sign.sign65 = true)
  · exact (by lit_decide : noSpB Sign.sign65V = true)
  · exact (by lit_decide : noSpB Sign.sign87 = true)
  · exact (by lit_decide : noSpB Sign.sign87V = true)

theorem sign0_depth {p : Params} (h3 : Ok3 p) (vs : Bool := false) :
    decide ((Impl.MlDsa.X86_64.Sign.sign (primsWith .empty vs) p).depth ≤ 4) = true := by
  rcases h3 with rfl | rfl | rfl <;> cases vs
  · exact (by lit_decide : decide (Sign.sign44.depth ≤ 4) = true)
  · exact (by lit_decide : decide (Sign.sign44V.depth ≤ 4) = true)
  · exact (by lit_decide : decide (Sign.sign65.depth ≤ 4) = true)
  · exact (by lit_decide : decide (Sign.sign65V.depth ≤ 4) = true)
  · exact (by lit_decide : decide (Sign.sign87.depth ≤ 4) = true)
  · exact (by lit_decide : decide (Sign.sign87V.depth ≤ 4) = true)

/-- `vg_mldsa*_sign`'s code, with the polynomial arithmetic of `v`, called by
its addresses if `vs`, never writes `rsp` and calls at most four deep. -/
theorem sign_noSp_depth (v : ArithImpl) {p : Params} (hp : p ∈ params) (vs : Bool) :
    NoSp (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code vs) p) ∧
      (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code vs) p).depth ≤ 4 := by
  have h3 := ok3_of hp
  have dep : ∀ {c : Prog isa}, c.depth ≤ 3 → decide (c.depth ≤ 3) = true := fun h => decide_eq_true h
  have dep2 : ∀ {c : Prog isa}, c.depth ≤ 2 → decide (c.depth ≤ 3) = true := fun h => decide_eq_true (by omega_using [h])
  exact ⟨noSp_of (Same.ok (sign_same (Comp.all _) (noSpB_of v.ok.ntt.nosp) (noSpB_of v.ok.invNtt.nosp)
      (noSpB_of v.ok.mul.nosp) (noSpB_of v.ok.add.nosp) (noSpB_of v.ok.sub.nosp)
      (noSpB_of v.ok.rej4.nosp) (noSpB_of v.ok.expandMask4.nosp) (noSpB_of v.ok.highBits.nosp)
      (noSpB_of v.ok.lowBits.nosp) (noSpB_of v.ok.normLt.nosp) (noSpB_of v.ok.makeHint.nosp)
      (noSpB_of (v.ok.dotInv 4 (.inl rfl)).nosp) (noSpB_of (v.ok.dotInv 5 (.inr (.inl rfl))).nosp)
      (noSpB_of (v.ok.dotInv 7 (.inr (.inr rfl))).nosp) p vs) (sign0_noSp h3 vs)),
    of_decide_eq_true (Same.ok (sign_same (depthCompN 3) (dep2 v.ok.ntt.depth) (dep2 v.ok.invNtt.depth)
      (dep2 v.ok.mul.depth) (dep2 v.ok.add.depth) (dep2 v.ok.sub.depth)
      (dep v.ok.rej4.depth) (dep v.ok.expandMask4.depth) (dep2 v.ok.highBits.depth) (dep2 v.ok.lowBits.depth)
      (dep2 v.ok.normLt.depth) (dep2 v.ok.makeHint.depth) (dep2 (v.ok.dotInv 4 (.inl rfl)).depth)
      (dep2 (v.ok.dotInv 5 (.inr (.inl rfl))).depth) (dep2 (v.ok.dotInv 7 (.inr (.inr rfl))).depth) p vs)
      (sign0_depth h3 vs))⟩

/-! ## `vg_mldsa*_sign` of a variant, calling one body shared by every variant -/

theorem fillSlots_spSafe : ∀ (o : Nat) (ns : List String),
    (Impl.MlDsa.X86_64.Sign.fillSlots o ns).all (fun i => !isa.writesSp i) = true
  | _, [] => rfl
  | o, _ :: ns => by
    simp only [Impl.MlDsa.X86_64.Sign.fillSlots, List.all_cons, fillSlots_spSafe (o + 8) ns, Bool.and_true]
    rfl

theorem signVia_spSafe {ns : List String} {n : String} {c : Prog isa}
    (hc : c.all (fun i => !isa.writesSp i) = true) :
    (Impl.MlDsa.X86_64.Sign.signVia ns n c).all (fun i => !isa.writesSp i) = true := by
  simp only [Impl.MlDsa.X86_64.Sign.signVia, Code.all, hc, fillSlots_spSafe, Bool.and_true]
  rfl

theorem signVia_depth (ns : List String) (n : String) (c : Prog isa) :
    (Impl.MlDsa.X86_64.Sign.signVia ns n c).x86_64Depth = c.x86_64Depth + 8 + Impl.MlDsa.X86_64.Sign.viaBytes ns := by
  simp only [Impl.MlDsa.X86_64.Sign.signVia, Code.x86_64Depth, X86_64.Instr.frameBytes]
  omega_using []

/-- The callees of the shared body of the parameter set `p`, for the
arithmetic of `v`. -/
abbrev viaNames (v : ArithImpl) (p : Params) : List String := Impl.MlDsa.X86_64.Sign.slotNames (primsWith v.code true) p.ℓ

/-- `vg_mldsa*_sign` with the polynomial arithmetic of `v`, as a variant's entry
(`signVia`) that calls the body `n`, which calls the arithmetic by the
addresses the entry stores, as `sign_message` calls it. -/
theorem signViaFn (v : ArithImpl) {p : Params} (hp : p ∈ params) (n : String) :
    SignFn p (viaNames v p)
      (Impl.MlDsa.X86_64.Sign.signVia (viaNames v p) n (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code true) p)) := by
  have h3 := ok3_of hp
  have hdot : Proof.MlDsa.X86_64.Sign.DotSl (primsWith v.code true) p (viaNames v p) := fun _ => rfl
  obtain ⟨nosp, depth⟩ := sign_noSp_depth v hp true
  have hns : viaNames v p ≠ [] := List.cons_ne_nil _ _
  have hlen : (viaNames v p).length = 12 := rfl
  have hB : Impl.MlDsa.X86_64.Sign.viaBytes (viaNames v p) < 4096 := by
    unfold Impl.MlDsa.X86_64.Sign.viaBytes; omega_using [hlen]
  have hv := fun σ h => sign_correct (Proof.MlDsa.X86_64.Sign.prims_okWithV v p.ℓ) h3 hdot
    (Proof.MlDsa.X86_64.Sign.sign_ctl v h3 true) σ h
  have e : 32 + Impl.MlDsa.X86_64.Sign.viaBytes (viaNames v p) + 8 = 144 := by
    unfold Impl.MlDsa.X86_64.Sign.viaBytes; omega_using [hlen]
  refine ⟨fun σ h => ?_, ?_, SpSafe.of_all (signVia_spSafe (Proof.MlDsa.X86_64.Sign.sign_spSafe v h3 true)), ?_⟩
  · rw [← e] at h
    obtain ⟨t, s', he, ha, hq⟩ := Sign.signVia_ok (D := 32) hns hB hv nosp (by omega_using [depth]) (by decide) h
    exact ⟨t, s', he, ha, e ▸ hq⟩
  · have hct := Sign.signVia_ct (n := n) hns hB hv (sign_ct (Proof.MlDsa.X86_64.Sign.prims_okWithV v p.ℓ) h3 hdot)
    rw [e] at hct
    exact hct
  · rw [signVia_depth, x86_64Depth_noSp nosp, ← e]
    omega_using [depth]

/-- `signViaFn`, as the entry of an encoded key calls it. -/
theorem kernelVia (v : ArithImpl) {p : Params} (hp : p ∈ params) (n : String) :
    Sign.KernelFn p 144 (viaNames v p)
      (Impl.MlDsa.X86_64.Sign.signVia (viaNames v p) n (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code true) p)) :=
  have h := signViaFn v hp n
  ⟨h.ok, h.ct, h.sp, h.depth, by decide⟩

theorem kabs_spSafe : Impl.Sha3.X86_64.Stream.absorb.all (fun i => !isa.writesSp i) = true := by lit_decide
theorem kpad_spSafe : Impl.Sha3.X86_64.Stream.pad.all (fun i => !isa.writesSp i) = true := by lit_decide
theorem ksqz_spSafe : Impl.Sha3.X86_64.Stream.squeeze.all (fun i => !isa.writesSp i) = true := by lit_decide

theorem arg_wsp (d : Reg) (hd : d ∈ argRegs6) (a : Arg) : (a.mov d).all (fun i => !isa.writesSp i) = true := by
  simp only [argRegs6, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> cases a <;> rfl

theorem setArgs_wsp (as : List Arg) : (setArgs as).all (fun i => !isa.writesSp i) = true := by
  rw [List.all_eq_true]
  intro i hi
  simp only [setArgs, List.mem_flatMap] at hi
  obtain ⟨⟨d, a⟩, hm, hi⟩ := hi
  exact List.all_eq_true.mp (arg_wsp d (List.of_mem_zip hm).1 a) i hi

theorem signMessage_spSafe {p : Params} {n : String} {c : Prog isa} (hc : c.all (fun i => !isa.writesSp i) = true)
    (flag : Nat) : (Impl.MlDsa.X86_64.Message.signMessage n c p flag).all (fun i => !isa.writesSp i) = true := by
  generalize hq : (fun i => !isa.writesSp i) = q at hc ⊢
  have ha : Impl.Sha3.X86_64.Stream.absorb.all q = true := hq ▸ kabs_spSafe
  have hp' : Impl.Sha3.X86_64.Stream.pad.all q = true := hq ▸ kpad_spSafe
  have hs : Impl.Sha3.X86_64.Stream.squeeze.all q = true := hq ▸ ksqz_spSafe
  have hsa : ∀ as, (setArgs as).all q = true := fun as => hq ▸ setArgs_wsp as
  have hmv : ∀ a, (Arg.mov .rdi a).all q = true := fun a => hq ▸ arg_wsp .rdi (by decide) a
  simp only [Impl.MlDsa.X86_64.Message.signMessage, Impl.MlDsa.X86_64.Message.top,
    Impl.MlDsa.X86_64.Message.muHash, Impl.MlDsa.X86_64.Message.zeroSt, Impl.MlDsa.X86_64.Message.kabs,
    Impl.MlDsa.X86_64.Message.kpad, Impl.MlDsa.X86_64.Message.ksqz, Impl.MlDsa.X86_64.Message.callA, Code.all,
    hc, ha, hp', hs, hsa, hmv, Bool.and_true, Bool.true_and]
  subst hq
  decide

/-! ## `vg_mldsa*_sign`: the entry of an encoded key -/

/-- `vg_mldsa*_sign` of a variant that calls the body shared by every
variant, `b`. -/
theorem signEntryV_verified (v : ArithImpl) {p : Params} (hp : p ∈ params) (n b : String) :
    Verified X86_64.target (Impl.MlDsa.X86_64.Sign.entry n
      (Impl.MlDsa.X86_64.Sign.signVia (viaNames v p) b (Impl.MlDsa.X86_64.Sign.sign (primsWith v.code true) p)) 0)
      (signContract p (X86_64.abi.withFns (viaNames v p)) 152) :=
  have hK := kernelVia v hp b
  have I := Sign.signK0_implies (ok3_of hp)
  VG.X86_64.Scrub.verified_withFns
    (fun s h => let ⟨t, s', he, ha, hq⟩ := Sign.entry0_correct (n := n) hK s (I.pre s h)
      ⟨t, s', he, ha, I.post s s' h hq⟩)
    (fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => Sign.entry0_ct (n := n) hK s₁ s₂ t₁ t₂ s₁' s₂'
      (I.pre _ h₁) (I.pre _ h₂) ⟨I.pub _ _ h₁ h₂ hpub.1, hpub.2⟩ e₁ e₂)
    I.sat

theorem signEntry_spSafe {n : String} {c : Prog isa} (hc : c.all (fun i => !isa.writesSp i) = true)
    (flag : Nat) : (Impl.MlDsa.X86_64.Sign.entry n c flag).all (fun i => !isa.writesSp i) = true := by
  simp only [Impl.MlDsa.X86_64.Sign.entry, Code.all, hc, Bool.and_true]
  rfl

end VG.Proof.MlDsa.X86_64.Message

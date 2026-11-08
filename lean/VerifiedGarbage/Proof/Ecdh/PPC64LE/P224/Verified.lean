module

public import VerifiedGarbage.Proof.Ecdh.PPC64LE.Main
public import VerifiedGarbage.Proof.Ecdh.PPC64LE.P224.Contract
public import VerifiedGarbage.Impl.Ecdh.P224.PPC64LE
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Spec.EcKey.P224
public import VerifiedGarbage.Spec.Ecdh.Generic
import VerifiedGarbage.Proof.Ecdh.PPC64LE.P224.Lit
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P224
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P224.Window
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Stages
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Pow
import VerifiedGarbage.Proof.Weierstrass.BytesLen
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Ecdh.PPC64LE.Main
meta import VerifiedGarbage.Proof.Ecdh.PPC64LE.P224.Contract
meta import VerifiedGarbage.Impl.Ecdh.P224.PPC64LE
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Spec.EcKey.P224
meta import VerifiedGarbage.Spec.Ecdh.Generic
meta import VerifiedGarbage.Proof.Ecdh.PPC64LE.P224.Lit
meta import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P224
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# ECDH over P-224 on PPC64LE: `Verified`

`win_mulPowOk`: `[d]P` by the four-bit windows
(`Proof/Ecdsa/PPC64LE/P224/Window.lean`), then `Z^(p-2)` by the power, leaves
what ECDH's last stage needs (`LadPost`). `ecdh_ppc`: from `exchangeWith_ok`,
for P-224's configuration; `ecdh_ct`: the
time depends only on `out`, `d`, `peer` and `scratch` (`taint_decide` on the
code's literal).
-/

@[expose] public section

namespace VG.Proof.Ecdh.PPC64LE.P224

open VG VG.PPC64LE VG.Impl.Ecdsa.PPC64LE VG.Impl.Ecdh.PPC64LE VG.Proof.Ecdsa.PPC64LE Spec.Weierstrass

theorem pre_of {s : State} (h : ecdhPPC.pre s) : EPre p224 s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem post_of {s s' : State} (h : EPost p224 s s') : ecdhPPC.post s s' := by
  unfold EPost at h
  show match ex s.mem (s.gpr .r4) (s.gpr .r5) with
    | some z => s'.gpr .r3 = 1 ∧ Spec.EcKey.bytesAt s'.mem (s.gpr .r3) 28 = z
    | none => s'.gpr .r3 = 0 ∧ Spec.EcKey.bytesAt s'.mem (s.gpr .r3) 28 = List.replicate 28 0
  revert h
  generalize hq : ex s.mem (s.gpr .r4) (s.gpr .r5) = q
  rw [show Spec.Ecdh.exchange p224.C (dk p224 s)
      (Spec.Ecdsa.bytesAt s.mem (s.gpr .r5) (1 + 2 * p224.C.len)) = ex s.mem (s.gpr .r4) (s.gpr .r5) from rfl, hq]
  rcases q with _ | z <;> exact id

open VG.Impl.Mont VG.Impl.Weierstrass.PPC64LE VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass
  VG.Proof.Weierstrass.PPC64LE in
/-- The windows, then the power, meet `MulPowOk`. -/
theorem win_mulPowOk (hL : Weierstrass.Law Spec.P224.curve) (s₀ : State) :
    MulPowOk p224 s₀ (Window.Cfg.mul p224 PX PY BP) := by
  intro base s K hrx hry hrz _ ht₀ ht₁ hbp P hP hG hlx hly rest Q h
  have h7 : p224.n < 10 := by decide
  have hn := K.ws.nowrap
  have hpR := unitMod_pow_two p224_ok.p_odd (64 * p224.n)
  have F' := K.fixed
  have hpre : Proof.Ecdsa.PPC64LE.Window.P224.MPre base s P (dk p224 s₀) :=
    ⟨K.ws, ⟨F'.ap, hbp, F'.zero, F'.onep⟩,
      ⟨hG, hlx, hly, lt_of_eq_of_lt F'.onep (Nat.mod_lt _ (by decide))⟩, hP,
      fun t ht => ht₀ t ht, Nat.lt_of_lt_of_le (ofBytes_bytesAt_lt _ _ _) (by decide)⟩
  refine WP.seq (WP.mono (Proof.Ecdsa.PPC64LE.Window.P224.mul_ok hL hpre) fun s₅ ⟨K₅, U₅, R₅⟩ => ?_)
  have hW₅ : FixedOk p224 Proof.Ecdsa.PPC64LE.Window.P224.mulW := fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> exact Or.inr (by decide)
  have hWs₅ : ∀ w ∈ Proof.Ecdsa.PPC64LE.Window.P224.mulW, w.1 + w.2 ≤ size := by decide
  have K₅' : Keep p224 s₀ base s₅ := K.step h7 K₅ (hU := U₅) (hW := hW₅) (hWs := hWs₅)
  have apS : ∀ i < 45, i ∉ ACC :: PT :: Proof.Ecdsa.PPC64LE.ladIx → ∀ w ∈ Proof.Ecdsa.PPC64LE.Window.P224.mulW,
      p224.sl i + 8 * p224.n ≤ w.1 ∨ w.1 + w.2 ≤ p224.sl i := by
    intro i hi hr w hw
    have hi' : i < 14 ∨ 29 ≤ i := by
      refine Classical.byContradiction fun hc => hr ?_
      have : i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨
        i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl <;> simp only [Cfg.sl, slot, p224] <;> omega
  have e₅ : ∀ {i}, i < 45 → i ∉ ACC :: PT :: Proof.Ecdsa.PPC64LE.ladIx → sv p224 base s₅ i = sv p224 base s i :=
    fun hi hr => sv_unch U₅ h7 hn hi (apS _ hi hr)
  have tA₅ : ∀ j < 3, j ≠ 0 → ∀ t < 64 * p224.n, ∀ w ∈ Proof.Ecdsa.PPC64LE.Window.P224.mulW,
      bitsAt p224.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt p224.n j + t := by
    intro j hj hj0 t ht w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    simp only [bitsAt, p224] at ht ⊢
    rcases hw with rfl | rfl | rfl <;> simp only <;> omega
  have lx₅ : sv p224 base s₅ RX < p224.C.p := R₅.x
  have ly₅ : sv p224 base s₅ RY < p224.C.p := R₅.y
  have lz₅ : sv p224 base s₅ RZ < p224.C.p := R₅.z
  refine WP.seq (WP.mono (pow_ok (P := p224.powP) (S := p224.SP) (e := p224.C.p - 2) p224_ok.fpk p224_ok.fpm
    (modP p224_ok) rfl (powLayP p224_ok) hpR K₅'.ws lz₅ K₅'.fixed.onep
    (fun t ht => by
      show s₅.mem (off base (bitsAt p224.n 1 + t)) = _
      rw [tbl_unch U₅ h7 (j := 1) (by decide) ht (tA₅ 1 (by decide) (by decide) t ht)]
      exact ht₁ t ht)
    (by decide)) fun s₆ ⟨K₆, U₆, lt₆, v₆⟩ => h s₆ ?_)
  rw [powWxP_eq] at U₆
  have K₆' : Keep p224 s₀ base s₆ := K₅'.step h7 K₆ (hU := U₆) (hW := fixedOk_powWx h7) (hWs := powWx_le h7)
  have e₆ : ∀ {i}, i < 45 → i ∉ [ACC, PT] → sv p224 base s₆ i = sv p224 base s₅ i := fun hi hr =>
    sv_unch U₆ h7 hn hi (apart_powWx h7 hi hr)
  have tR : ∀ i ∈ [RX, RY, RZ], Point.tmv p224.C p224.n base s₆ (p224.sl i) =
      Point.tmv p224.C p224.n base s₅ (p224.sl i) := by
    intro i hi
    show toM _ _ (sv p224 base s₆ i) = toM _ _ (sv p224 base s₅ i)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> rw [e₆ (by decide) (by decide)]
  have apF : ∀ w ∈ Proof.Ecdsa.PPC64LE.Window.P224.mulW ++ [(p224.sl ACC, 8 * p224.n), (p224.sl PT, 8 * p224.n),
      (Impl.Weierstrass.PPC64LE.Mont.own p224.n, 64 * p224.n)], p224.sl FLAG + 8 ≤ w.1 ∨ w.1 + w.2 ≤ p224.sl FLAG := by
    intro w hw
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨K₆', fun hi hl => ?_, ?_, ?_,
    by rw [tR RX (by simp), tR RY (by simp), tR RZ (by simp)]; exact R₅.rep,
    by rw [e₆ (by decide) (by decide)]; exact lx₅,
    by rw [e₆ (by decide) (by decide)]; exact ly₅,
    by rw [e₆ (by decide) (by decide)]; exact lz₅, lt₆, ?_⟩
  · rw [e₆ hi (Proof.Ecdsa.PPC64LE.nmem_of hl (by decide)), e₅ hi hl]
  · rw [flagW, (U₅.trans U₆).word apF (by decide), ← flagW]
  · intro t ht
    rw [tbl_unch U₆ h7 (j := 2) (by decide) ht (tbl_apart_powWx h7 2 t),
      tbl_unch U₅ h7 (j := 2) (by decide) ht (tA₅ 2 (by decide) (by decide) t ht)]
  · rw [tR RZ (by simp)]; exact v₆

theorem ecdh_ppc (hL : Weierstrass.Law Spec.P224.curve) (s : State) (hs : ecdhPPC.pre s) :
    ∃ t s', Exec isa exchangeP224 s t s' ∧ abiPreserved s s' ∧ ecdhPPC.post s s' := by
  obtain ⟨t, s', he, K, hpost⟩ := exchangeWith_ok p224_ok hL (pre_of hs) (win_mulPowOk hL s)
  exact ⟨t, s', he, ⟨K.saved, K.sp, K.lr⟩, post_of hpost⟩

theorem ecdh_ct : ConstantTime isa ecdhPPC.pre ecdhPPC.pub exchangeP224 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r3, .r4, .r5, .r6])
    (fun _ _ _ _ ⟨hsp, h3, h4, h5, h6⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h3
      · exact h4
      · exact h5
      · exact h6⟩) (by taint_decide)

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x8000 | _ => 0
  lr := 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, 28⟩, ⟨0x3000, 57⟩]
  wr := [⟨0x1000, 28⟩, ⟨0x8000, 8192⟩]

theorem ecdh_verified (hL : Weierstrass.Law Spec.P224.curve) :
    Verified PPC64LE.target exchangeP224 (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P224.inst PPC64LE.abi) :=
  Verified.of_correct (ecdh_ppc hL) ecdh_ct
    { pre := by
        sig_implies_pre [Spec.EcKey.P224.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P224.curve, Spec.EcKey.scratchWords, ecdhPPC, ex, PPC64LE.abi,
          PPC64LE.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.P224.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P224.curve, Spec.EcKey.scratchWords, ecdhPPC, ex, PPC64LE.abi,
          PPC64LE.argRegs]
        simp only [ecdhPPC, ex, Spec.P224.curve] at h
        revert h
        generalize Spec.Ecdh.exchange _ _ _ = q
        rcases q with _ | z <;> exact fun h => ⟨by rw [h.1]; rfl, h.2⟩
      pub := by
        sig_implies_pub [Spec.EcKey.P224.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P224.curve, Spec.EcKey.scratchWords, ecdhPPC, ex, PPC64LE.abi,
          PPC64LE.argRegs]
      sat := by
        sig_implies_sat [Spec.EcKey.P224.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P224.curve, Spec.EcKey.scratchWords, ecdhPPC, ex, PPC64LE.abi,
          PPC64LE.argRegs] [satState] using satState }

end VG.Proof.Ecdh.PPC64LE.P224

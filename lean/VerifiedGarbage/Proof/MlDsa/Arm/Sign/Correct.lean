module

public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseK
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PrimsD
import VerifiedGarbage.Proof.MlDsa.Round.Decompose
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseL
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds

/-! ### `MlDsa.Arm.Sign.PhaseO`, which only this module used -/

section

/-!
# ML-DSA signing on ARMv7: the signature

Once an iteration passed: `c̃`, then `BitPack(z[r], γ₁ - 1, γ₁)` for each `r`
(in range, as `z` passed its norm check: `inRange_of_norm`), then
`HintBitPack(h)` (with at most `ω` 1s) to `sig`, which then holds
`sigEncode(c̃, z mod± q, h)` (`output_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `z` in range -/

theorem coeff_val {m : Mem} {a : Addr} {f : Poly} (h : PolyIs m a f) {i : Nat} (hi : i < 256) :
    (coeffAt m a i).toNat = f[i].val := by
  have e := congrArg (·[i]) h.2
  simp only [polyAt, Vector.getElem_ofFn] at e
  rw [← e, Fin.val_ofNat, Nat.mod_eq_of_lt (h.1 i hi)]

theorem inRange_of_norm {m : Mem} {a : Addr} {f : Poly} (h : PolyIs m a f) {B γ : Nat}
    (hn : normRq [f] < B) (hB : B ≤ γ) : InRange m a (γ - 1) γ := by
  intro i hi
  have := (VG.Proof.MlDsa.Round.normRq_lt f B).mp hn i hi
  rw [getElem!_pos f i hi] at this
  rw [coeff_val h hi]
  simp only [normZq] at this
  omega_using [hB, this]

/-! ## The hint -/

theorem hintAt_of {m : Mem} {a : Addr} {k : Nat} {f : Nat → Vector Bool n}
    (h : ∀ i < k, HintIs m (a + BitVec.ofNat 64 (1024 * i)) 1 [f i]) :
    hintAt m a k = (List.range k).map f := by
  unfold hintAt
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  apply Vector.ext
  intro j hj
  have hn : n = 256 := rfl
  have e := (h i hi).2 0 (by decide) j hj
  simp only [Nat.mul_zero, Nat.zero_add, List.getD_cons_zero] at e
  have ea : coeffAt m a (256 * i + j) = coeffAt m (a + BitVec.ofNat 64 (1024 * i)) j := by
    simp only [coeffAt]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 1024 * i + 4 * j = 4 * (256 * i + j) by omega_using []]
  rw [Vector.getElem_ofFn, ea, e, getElem!_pos (f i) j hj]
  cases (f i)[j] <;> decide

theorem hintOnes_map (k : Nat) (f : Nat → Vector Bool n) :
    hintOnes ((List.range k).map f) = onesSum f k := by
  simp only [hintOnes, onesSum, List.map_map]
  rfl

/-! ## The signature -/

theorem pS_hint (s : State) (i : Nat) :
    pa s (pS (5 + i)) = pa s (Impl.MlDsa.Arm.Sign.hP 0) + BitVec.ofNat 64 (1024 * i) := by
  show pa s (.r7, oP (5 + i)) = pa s (.r7, oP (5 + 0)) + BitVec.ofNat 64 (1024 * i)
  rw [← pa_add, show oP (5 + 0) + 1024 * i = oP (5 + i) by simp only [oP]; omega_using []]

theorem r8_bases (o : Nat) : ((.r8, o) : Ptr).1 ∈ bases := by
  show Reg.r8 ∈ bases; decide

/-- The encodings of the first `r` polynomials of `z`. -/
abbrev zEnc (p : Params) (σ : State) (κ r : Nat) : List Byte :=
  (List.range r).flatMap fun j => bitPack ((Zv p σ κ j).map fun c => modPm c.val q) (p.γ₁ - 1) p.γ₁

/-- `c̃` and the first `r` polynomials of `z` in `sig`. -/
structure OS (p : Params) (D : Nat) (σ : State) (κ r : Nat) (s : State) : Prop where
  k : IK p D σ s
  z : Fam s (yBase p) p.ℓ (Zv p σ κ)
  h : HFam s 5 p.k (Hv p σ κ)
  sig : bytesAt s.mem (pa s (.r8, 0)) (cLen p + zLen p * r) = CTv p σ κ ++ zEnc p σ κ r
  r11 : s.gpr .r11 = 1

def ofam (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  ikChk p ws && famChk (sgB p) ws (yBase p) p.ℓ && famChk (sgB p) ws 5 p.k

theorem OS.step {p : Params} {D : Nat} {σ s s' : State} {κ r : Nat} (h : OS p D σ κ r s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) (hc : ofam p ws = true)
    (hs : keepB (sgB p) ws (.r8, 0) (cLen p + zLen p * r) = true) (h15 : s'.gpr .r11 = s.gpr .r11) :
    OS p D σ κ r s' := by
  simp only [ofam, Bool.and_eq_true] at hc
  have L := h.k.d.im.st.lay
  exact ⟨h.k.step hP hc.1.1, Fam.keep L hP hc.1.2 h.z, HFam.keep L hP hc.2 h.h, (L.keepBytes hP hs).trans h.sig,
    h15.trans h.r11⟩

/-- What the signature needs of the layout. -/
def oChk (p : Params) : Bool :=
  copyChk (sgB p) (sgW p) (.r8, 0) (sc oCT) (cLen p) && ofam p [((.r8, 0), cLen p)] &&
    (List.range p.ℓ).all (fun r => rwChk (sgB p) (sgW p) (yP p r) 1024 (.r8, sigZ p r) (zLen p) &&
      ofam p [((.r8, sigZ p r), zLen p)] && keepB (sgB p) [((.r8, sigZ p r), zLen p)] (.r8, 0) (cLen p + zLen p * r)) &&
    rwChk (sgB p) (sgW p) (hP 0) (256 * p.k * 4) (.r8, sigH p) (p.ω + p.k) &&
    decide ((p.ω, p.k) ∈ hintParams) && decide ((p.γ₁ - 1, p.γ₁) ∈ bitPackParams) &&
    decide (zLen p = 32 * bitlen (p.γ₁ - 1 + p.γ₁)) && decide (p.sigLen = cLen p + zLen p * p.ℓ + (p.ω + p.k)) &&
    ikChk p [((.r8, sigH p), p.ω + p.k)] &&
    keepB (sgB p) [((.r8, sigH p), p.ω + p.k)] (.r8, 0) (cLen p + zLen p * p.ℓ)

theorem oChk_ok {p : Params} (h : Ok3 p) : oChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

/-- `sigEncode` of what the passing iteration returns. -/
abbrev sigV (p : Params) (σ : State) (κ : Nat) : List Byte :=
  sigOf p (CTv p σ κ, (List.range p.ℓ).map (Zv p σ κ), (List.range p.k).map (Hv p σ κ))

section
variable {P : Prims} {D : Nat} (hPO : PrimsOk P D) {p : Params} (hc : oChk p = true) {σ : State} {κ : Nat}
include hc

omit hPO in
theorem outCopy_ok {s : State} (hk : IK p D σ s) (hct : bytesAt s.mem (pa s (sc oCT)) (cLen p) = CTv p σ κ)
    (hz : Fam s (yBase p) p.ℓ (Zv p σ κ)) (hh : HFam s 5 p.k (Hv p σ κ)) (h15 : s.gpr .r11 = 1) :
    WP isa (copy (.r8, 0) (sc oCT) (cLen p)) s fun s1 =>
      OS p D σ κ 0 s1 ∧ ∀ f, HFam s 5 p.k f → HFam s1 5 p.k f := by
  simp only [oChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨cc, c0⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc
  have L := hk.d.im.st.lay
  refine WP.mono (copy_okB L cc) fun s1 ⟨hP1, hcs1, hb1⟩ => ?_
  simp only [ofam, Bool.and_eq_true] at c0
  refine ⟨⟨hk.step hP1 c0.1.1, Fam.keep L hP1 c0.1.2 hz, HFam.keep L hP1 c0.2 hh, ?_,
    by rw [hcs1 _ (by decide) (by decide), h15]⟩, fun f h => HFam.keep L hP1 c0.2 h⟩
  rw [Nat.mul_zero, Nat.add_zero, hP1.pa (by decide), hb1, hct]
  simp [zEnc]

include hPO in
theorem packZ_ok {r : Nat} (hr : r < p.ℓ) {s : State} (h : OS p D σ κ r s) (hpass : PassV p σ κ) :
    WP isa (packZ P p r) s fun s' => OS p D σ κ (r + 1) s' ∧ ∀ f, HFam s 5 p.k f → HFam s' 5 p.k f := by
  simp only [oChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, cz⟩, -⟩, -⟩, hbp⟩, hzl⟩, -⟩, -⟩, -⟩ := hc
  obtain ⟨⟨c1, c2⟩, c3⟩ := cz r hr
  have Lh := h.k.d.im.st.lay
  have hzr := h.z r hr
  refine WP.mono (bpAt_ok hPO Lh hbp hzl c1 hzr.1 (inRange_of_norm hzr (hpass.1 r hr) (Nat.sub_le _ _)))
    fun s' ⟨hP', hcs', hb'⟩ => ?_
  have O' := h.step hP' c2 c3 (hcs' _ (by decide) (by decide))
  have c2' := c2
  simp only [ofam, Bool.and_eq_true] at c2'
  refine ⟨⟨O'.k, O'.z, O'.h, ?_, O'.r11⟩, fun f hf => HFam.keep Lh hP' c2'.2 hf⟩
  rw [Nat.mul_succ, ← Nat.add_assoc, VG.Proof.MlKem.bytesAt_add, O'.sig, ← pa_add, Nat.zero_add,
    hP'.pa (r8_bases _), hb', hzr.2, zEnc, zEnc, List.range_succ, List.flatMap_append, List.flatMap_singleton,
    List.append_assoc]

omit hc in
theorem hones_ok {s : State} (h : OS p D σ κ p.ℓ s) (hpass : PassV p σ κ) :
    hintOnes (hintAt s.mem (pa s (Impl.MlDsa.Arm.Sign.hP 0)) p.k) ≤ p.ω := by
  rw [hintAt_of (f := Hv p σ κ) fun i hi => by
      have := h.h i hi; rwa [pS_hint] at this,
    hintOnes_map]
  exact hpass.2.2.2

include hPO in
theorem hpack_ok {s : State} (h2 : OS p D σ κ p.ℓ s) (hpass : PassV p σ κ) :
    WP isa (hintBitPackAt P (Impl.MlDsa.Arm.Sign.hP 0) (256 * p.k) p.ω (.r8, sigH p) (p.ω + p.k)) s fun s' =>
      IK p D σ s' ∧ bytesAt s'.mem (pa s' (.r8, 0)) p.sigLen = sigV p σ κ ∧ s'.gpr .r11 = 1 := by
  simp only [oChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, ch⟩, hhp⟩, -⟩, -⟩, hsl⟩, ci⟩, ck⟩ := hc
  have L2 := h2.k.d.im.st.lay
  refine WP.mono (hbpAt_ok hPO L2 hhp ch (hones_ok h2 hpass)) fun s3 ⟨hP3, hcs3, hb3⟩ =>
    ⟨h2.k.step hP3 ci, ?_, by rw [hcs3 _ (by decide) (by decide), h2.r11]⟩
  rw [hsl, VG.Proof.MlKem.bytesAt_add, L2.keepBytes hP3 ck, h2.sig, hP3.pa (by decide), ← pa_add, Nat.zero_add,
    show cLen p + zLen p * p.ℓ = sigH p from rfl, hb3, hintAt_of (f := Hv p σ κ) fun i hi => by
        have := h2.h i hi; rwa [pS_hint] at this]
  simp only [sigV, sigOf, sigEncode, zEnc, List.map_map, List.flatMap_map]
  rfl

include hPO in
theorem output_ok {s : State} (hk : IK p D σ s) (hct : bytesAt s.mem (pa s (sc oCT)) (cLen p) = CTv p σ κ)
    (hz : Fam s (yBase p) p.ℓ (Zv p σ κ)) (hh : HFam s 5 p.k (Hv p σ κ)) (hpass : PassV p σ κ)
    (h15 : s.gpr .r11 = 1) :
    WP isa (output P p) s fun s' => IK p D σ s' ∧ bytesAt s'.mem (pa s' (.r8, 0)) p.sigLen = sigV p σ κ ∧
      s'.gpr .r11 = 1 := by
  unfold output
  refine WP.seq (WP.mono (outCopy_ok hc hk hct hz hh h15) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (seqR_ok (I := fun r => OS p D σ κ r) p.ℓ 0
    (fun r _ hr s h => WP.mono (packZ_ok hPO hc (by omega_using [hr]) h hpass) fun _ h => h.1) s1 h1.1) fun s2 h2 => ?_)
  rw [Nat.zero_add] at h2
  exact hpack_ok hPO hc h2 hpass

end

end VG.Proof.MlDsa.Arm.Sign

end

end


/-!
# ML-DSA signing on ARMv7: correctness

The function returns 1 with `Sign_internal`'s signature (within `maxBounds`)
in `sig`, or 0 when `Sign_internal` returns nothing within `minBounds`
(`sign_correct`): its `ExpandA` or its loop does not finish (`signMu_min_A`,
`signMu_min_L`), or an iteration passes (`signMu_max`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## `Sign_internal` -/

section
variable {p : Params} {σ : State}

theorem seedE_ij {i j : Nat} (hj : j < p.ℓ) : seedE p σ (p.ℓ * i + j) = aSeed (rhoOf p σ) i j := by
  have hl : 0 < p.ℓ := by omega_using [hj]
  have e1 : (p.ℓ * i + j) / p.ℓ = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hl, Nat.div_eq_of_lt hj, Nat.zero_add]
  have e2 : (p.ℓ * i + j) % p.ℓ = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  simp only [seedE, e1, e2]

theorem ij_lt {i j : Nat} (hi : i < p.k) (hj : j < p.ℓ) : p.ℓ * i + j < p.k * p.ℓ := by
  have := Nat.mul_le_mul_left p.ℓ (show i + 1 ≤ p.k from hi)
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm p.ℓ p.k] at this; omega_using [hj, this]

theorem expandA_max (hok : ∀ e < p.k * p.ℓ, (rejNTTPoly maxBounds.rejNTT (seedE p σ e)).isSome) :
    expandA p maxBounds (rhoOf p σ) = some (amat p (Am p σ)) :=
  expandA_some fun i hi j hj => by rw [← seedE_ij hj]; exact hok _ (ij_lt hi hj)

theorem signMu_min_A (h : ∃ e < p.k * p.ℓ, rejNTTPoly minBounds.rejNTT (seedE p σ e) = none) :
    signMu p minBounds (skOf p σ) (muOf σ) (rndOf σ) = none := by
  obtain ⟨e, he, hn⟩ := h
  have hl : 0 < p.ℓ := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at he; omega_using [he]
  exact signMu_none_A (expandA_none ⟨e / p.ℓ, (Nat.div_lt_iff_lt_mul hl).mpr he, e % p.ℓ, Nat.mod_lt _ hl, hn⟩)

theorem signMu_min_L (hA : expandA p maxBounds (rhoOf p σ) = some (amat p (Am p σ)))
    (hL : loopF p σ minBounds minBounds.sign 0 = none) :
    signMu p minBounds (skOf p σ) (muOf σ) (rndOf σ) = none := by
  cases e : expandA p minBounds (rhoOf p σ) with
  | none => exact signMu_none_A e
  | some A' =>
    have := expandA_mono (show minBounds.rejNTT ≤ maxBounds.rejNTT by decide) e
    rw [hA] at this
    obtain rfl := (Option.some.inj this).symm
    exact signMu_none_L e hL

theorem signMu_max (hp : ParamsOk p) (hA : expandA p maxBounds (rhoOf p σ) = some (amat p (Am p σ))) {t : Nat}
    (ht : t < 814) (hr : RejT p σ t) (hs : (sampleInBall p.τ maxBounds.ball (CTv p σ (p.ℓ * t))).isSome)
    (hpass : PassV p σ (p.ℓ * t)) :
    signMu p maxBounds (skOf p σ) (muOf σ) (rndOf σ) = some (sigV p σ (p.ℓ * t)) :=
  signMu_some hA (signLoop_pass _ _ _ _ _ _ _ hr (show t < maxBounds.sign by
    show t < 1000; omega_using [ht]) (iter_pass hp hs hpass))

end

/-! ## After the loop -/

/-- Before the return: `r11`, and the signature in `sig` if it is 1. -/
structure FS (p : Params) (D : Nat) (σ s : State) : Prop where
  st : St p D σ s
  r01 : s.gpr .r11 = 0 ∨ s.gpr .r11 = 1
  ok : s.gpr .r11 = 1 →
    signMu p maxBounds (skOf p σ) (muOf σ) (rndOf σ) = some (bytesAt s.mem (pa s (.r8, 0)) p.sigLen)
  bad : s.gpr .r11 = 0 → signMu p minBounds (skOf p σ) (muOf σ) (rndOf σ) = none

/-- What the function needs of the layout, besides its pieces. -/
def fChk (p : Params) : Bool :=
  stChk p [] && famChk (sgB p) [] (aBase p) (p.k * p.ℓ) && ikChk p [] && famChk (sgB p) [] (yBase p) p.ℓ &&
    famChk (sgB p) [] 5 p.k && keepB (sgB p) [] (sc oCT) (cLen p) &&
    inB (sgB p) (sc oSV) 36 &&
    decide (scrLen p < 2 ^ 32 ∧ p.skLen < 2 ^ 32 ∧ p.sigLen < 2 ^ 32)

theorem fChk_ok {p : Params} (h : Ok3 p) : fChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

/-- Every check of the layout. -/
def allChk (p : Params) : Bool :=
  aChk p && dChk p && cChk p && bChk p && ksChk p && lChk p && oChk p && fChk p

theorem allChk_ok {p : Params} (h : Ok3 p) : allChk p = true := by
  simp only [allChk, aChk_ok h, dChk_ok h, cChk_ok h, bChk_ok h, ksChk_ok h, lChk_ok h, oChk_ok h, fChk_ok h,
    Bool.and_self]

theorem r11_one {s : State} (h : s.gpr .r11 = 0 ∨ s.gpr .r11 = 1) (hne : s.gpr .r11 ≠ 0) : s.gpr .r11 = 1 := by
  rcases h with e | e
  · exact absurd e hne
  · exact e

theorem rest_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (h3 : Ok3 p) {σ s : State}
    (hpre : (signK p D).pre σ) (h : IM p D σ s) :
    WP isa (rest P p) s (FS p D σ) := by
  have hc := allChk_ok h3
  simp only [allChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨-, hd⟩, hc1⟩, hb⟩, hks⟩, hl⟩, ho⟩, hf⟩ := hc
  have hf' := hf
  simp only [fChk, Bool.and_eq_true] at hf'
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, ik⟩, fy⟩, f5⟩, kct⟩, -⟩, -⟩ := hf'
  have hp := paramsOk h3
  have hA := expandA_max h.ok
  unfold rest
  refine WP.seq (WP.mono (decodeC_ok hP hd (dcChk_ok h3) hpre h) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (signLoop_ok hP hp hc1 hb hks hl h1) fun s2 h2 => ?_)
  have L2 := h2.k.d.im.st.lay
  unfold ifOk
  refine ifOkElse_ok (D := D) (fun s3 hP3 hcs3 hm3 hne => ?_) fun s3 hP3 hcs3 hm3 he => ?_
  · have h15 := r11_one h2.r01 hne
    obtain ⟨t, ht, hr, hs, hpass, hct, hz, hh⟩ := h2.pass h15
    refine WP.mono (output_ok hP ho (h2.k.step hP3 ik) (by rw [L2.keepBytes hP3 kct, hct])
      (Fam.keep L2 hP3 fy hz) (HFam.keep L2 hP3 f5 hh) hpass (by rw [hcs3 _ (by decide) (by decide), h15]))
      fun s4 ⟨k4, hb4, h154⟩ => ⟨k4.d.im.st, .inr h154, fun _ => by rw [hb4]; exact signMu_max hp hA ht hr hs hpass,
        fun h0 => absurd (h0.symm.trans h154) (by decide)⟩
  · have h15 := he
    have e15 : s3.gpr .r11 = 0 := by rw [hcs3 _ (by decide) (by decide), h15]
    exact WP.block_nil ⟨(h2.k.step hP3 ik).d.im.st, .inl e15, fun h1 => absurd (h1.symm.trans e15) (by decide),
      fun _ => signMu_min_L hA (h2.fail h15)⟩

/-! ## The function -/

theorem entry_bytes {σ s : State} {r : Reg} {len : Nat} {R : Region} (hf : Frame [R] σ.mem s.mem)
    (hd : Region.Disjoint ⟨State.addr (σ.gpr r), len⟩ R) (hl : len ≤ 2 ^ 64) {b : Reg} (hb : s.gpr b = σ.gpr r) :
    bytesAt s.mem (pa s (b, 0)) len = bytesAt σ.mem (State.addr (σ.gpr r)) len := by
  rw [pa, hb, BitVec.add_zero]
  exact VG.Proof.MlKem.bytesAt_frame hf (fun R' hR => by rw [List.mem_singleton] at hR; subst hR; exact hd) hl

theorem entry_st {p : Params} {D : Nat} (h3 : Ok3 p) {σ s : State}
    (hpre : (signK p D).pre σ) (ht : Top σ s) (hf : Frame [⟨State.addr (stackArg σ 0), scrLen p⟩] σ.mem s.mem) :
    St p D σ s := by
  have hc := fChk_ok h3
  simp only [fChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  have hsz := hc.2
  have hpre' := hpre
  obtain ⟨_, _, -, d2, -, d4, -, d6, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcp⟩ := hpre'
  have ck : CK p D σ s := fun hne => by
    obtain ⟨c1, c2, c3, cf, -⟩ := hcp hne
    exact ⟨c1, c2, c3, by omega_using [cf], VG.Proof.MlKem.bytesAt_frame hf (fun R hR => by
      rw [List.mem_singleton] at hR; subst hR; exact c2) (by omega_using [cf])⟩
  exact ⟨ht, sgLay hpre hsz ht,
    entry_bytes hf d2 (by omega_using [hsz]) (ht.regs .r4 (by decide)),
    entry_bytes hf d4 (by omega_using []) (ht.regs .r5 (by decide)),
    entry_bytes hf d6 (by omega_using []) (ht.regs .r6 (by decide)), ck⟩

theorem sign_correct {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (h3 : Ok3 p) (σ : State)
    (hpre : (signK p D).pre σ) :
    ∃ t s', Exec isa (Impl.MlDsa.Arm.Sign.withCache P p) σ t s' ∧ abiPreserved σ s' ∧ (signK p D).post σ s' := by
  have hc := allChk_ok h3
  simp only [allChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨ha, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hf⟩ := hc
  have hf' := hf
  simp only [fChk, Bool.and_eq_true, decide_eq_true_eq] at hf'
  obtain ⟨⟨⟨⟨⟨⟨⟨st0, fa0⟩, -⟩, -⟩, -⟩, -⟩, hsv⟩, hsz⟩ := hf'
  have main : WP isa (Impl.MlDsa.Arm.Sign.withCache P p) σ fun s₅ => (∀ r ∈ preserved, s₅.gpr r = σ.gpr r) ∧
      s₅.sp = σ.sp ∧ ∃ s₄, FS p D σ s₄ ∧ s₅.gpr .r0 = s₄.gpr .r11 ∧ s₅.mem = s₄.mem := by
    unfold Impl.MlDsa.Arm.Sign.withCache
    refine WP.seq (WP.mono (pro_ok hpre) fun s₁ ⟨h₁, hf₁, h15⟩ => ?_)
    have S1 := entry_st h3 hpre h₁ hf₁
    refine WP.seq (WP.mono (expandA_ok hP ha S1 h15) fun s₂ h₂ => ?_)
    refine WP.seq (WP.mono (show WP isa (ifOk (rest P p)) s₂ (FS p D σ) from ?_) fun s₄ h₄ => ?_)
    · unfold ifOk
      refine ifOkElse_ok (D := D) (fun s₃ hP₃ hcs₃ hm₃ hne => ?_) fun s₃ hP₃ hcs₃ hm₃ he => ?_
      · have h1 := r11_one h₂.r01 hne
        obtain ⟨ok, fam⟩ := h₂.ok h1
        exact rest_ok hP h3 hpre ⟨h₂.st.step hP₃ st0, ok, Fam.keep h₂.st.lay hP₃ fa0 fam⟩
      · have h0 := he
        have e15 : s₃.gpr .r11 = 0 := by rw [hcs₃ _ (by decide) (by decide), h0]
        exact WP.block_nil ⟨h₂.st.step hP₃ st0, .inl e15, fun h1 => absurd (h1.symm.trans e15) (by decide),
          fun _ => signMu_min_A (h₂.bad h0)⟩
    · have hn := h₄.st.lay.nw (.r7, scrLen p) (by simp)
      have hge := scrLen_ge p
      exact WP.mono (topEnd_ok h₄.st.top (h₄.st.lay.iR hsv) (by simp only at hn; omega_using [hn, hge]))
        fun s₅ ⟨hr, hg, hm, hsp⟩ => ⟨hg, hsp.trans h₄.st.top.sp, s₄, h₄, hr, hm⟩
  obtain ⟨t, s', he, hF⟩ := main
  obtain ⟨hg, hsp, s₄, h₄, hr, hm⟩ := hF
  refine ⟨t, s', he, ⟨hg, hsp⟩, ?_⟩
  have e14 : pa s₄ (.r8, 0) = State.addr (σ.gpr .r3) := by
    rw [pa, h₄.st.top.regs .r8 (by decide), BitVec.add_zero]; rfl
  show Outcome _ _ _
  rcases h₄.r01 with h0 | h1
  · exact .inr ⟨by rw [hr, h0], h₄.bad h0⟩
  · exact .inl ⟨by rw [hr, h1], maxBounds, by rw [hm, ← e14]; exact h₄.ok h1⟩

end VG.Proof.MlDsa.Arm.Sign

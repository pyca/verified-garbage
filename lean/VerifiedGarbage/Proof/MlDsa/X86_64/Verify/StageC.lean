module

public import VerifiedGarbage.Impl.MlDsa.X86_64.Verify.Verify
public import VerifiedGarbage.Proof.MlDsa.Verify.Spec
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Control
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CallPack
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.PrimsOk
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Top
import VerifiedGarbage.Proof.MlDsa.Verify.Norm
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha3.X86_64.Round
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Blocks
import VerifiedGarbage.Proof.MlDsa.PreparedKeyContract
import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Flag

/-! ### `MlDsa.X86_64.Verify.StageA`, which this module and modules that import it used -/

section

/-! ### `MlDsa.X86_64.Verify.StageZ`, which this module and modules that import it used -/

section

/-!
# ML-DSA verification on x86-64: the hint and `z`

`HintIs` the hint of the signature, and `r15` whether it is well formed
(`hint_ok`); then, if it is, `z[i]` (polynomial `8 + i`) and `r15` whether
each norm so far is small (`zOne_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Verify (vHint vZ vCt)

/-- The `len` bytes at offset `off` of the signature. -/
theorem T.sigSlice {p : Params} {σ s : State} (h : T p σ s) {off len : Nat} (hl : off + len ≤ p.sigLen) :
    bytesAt s.mem (pa s (.r13, off)) len = ((vSig p σ).drop off).take len := by
  rw [← h.sig, pa, pa, BitVec.add_zero, Proof.MlKem.bytesAt_slice _ _ hl]

theorem T.pkSlice {p : Params} {σ s : State} (h : T p σ s) {off len : Nat} (hl : off + len ≤ p.pkLen) :
    bytesAt s.mem (pa s (.rbp, off)) len = ((vPk p σ).drop off).take len := by
  rw [← h.pk, pa, pa, BitVec.add_zero, Proof.MlKem.bytesAt_slice _ _ hl]

/-! ## The hint -/

/-- After the hint: `r15` whether it is well formed, and the hint. -/
def S1 (p : Params) (σ s : State) : Prop :=
  T p σ s ∧ match vHint p (vSig p σ) with
    | some h => s.gpr .r15 = flag True ∧ HintIs s.mem (pa s (pH 0)) p.k h
    | none => s.gpr .r15 = flag False

/-- The facts about the parameters the hint needs. -/
def hintChk (p : Params) : Bool :=
  huChk (vB p) (vW p) (.r13, oHint p) (p.ω + p.k) (pH 0) (256 * p.k) &&
    tChk p [(pH 0, 256 * p.k * 4)] && decide (HuPar (p.ω + p.k) p.ω (256 * p.k)) &&
    decide (oHint p + (p.ω + p.k) ≤ p.sigLen)

theorem hintChk_all : ∀ p ∈ params, hintChk p = true := by decide +kernel

theorem hint_ok {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) {σ s : State} (hv : VPre p σ)
    (h : T p σ s) : WP isa (hint P p) s (S1 p σ) := by
  have hc := hintChk_all p hp
  simp only [hintChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩ := hc
  have L := h.lay hp hv
  unfold hint
  refine WP.seq (WP.mono (hintUnpackAt_ok C.hintUnpack L c3 c1) fun s₁ ⟨hP₁, _, hq₁⟩ => ?_)
  have h₁ := h.step hp hv hP₁ c2
  refine WP.mono (mov15_ok s₁) fun s₂ ⟨⟨h15, hm₂⟩, k₂⟩ => ?_
  have hP₂ : PPostB s₁ s₂ [] := postB_of_keep k₂ (by decide) (by rw [hm₂]; exact Frame.refl _ _)
  refine ⟨h₁.step hp hv hP₂ (tChk_nil p hp), ?_⟩
  rw [h.sigSlice c4, show p.ω + p.k - p.ω = p.k by omega_using []] at hq₁
  have e : pa s₂ (pH 0) = pa s (pH 0) := by rw [hP₂.pa (by decide), hP₁.pa (by decide)]
  have hv' : vHint p (vSig p σ) = hintBitUnpack p.ω p.k (((vSig p σ).drop (oHint p)).take (p.ω + p.k)) := rfl
  rw [hv']
  revert hq₁
  generalize hintBitUnpack p.ω p.k (((vSig p σ).drop (oHint p)).take (p.ω + p.k)) = H
  cases H with
  | some hh =>
    intro ⟨hr, hH⟩
    simp only [res] at hr
    refine ⟨by rw [h15, hr]; rfl, ?_⟩
    rw [e, hm₂]; exact hH
  | none =>
    intro hr
    simp only [res] at hr
    show s₂.gpr .r15 = flag False
    rw [h15, hr]; rfl


/-! ## `z` -/

/-- After `z[0], …, z[j - 1]`, with the hint `h`. -/
structure S2 (p : Params) (h : List (Vector Bool n)) (j : Nat) (σ s : State) : Prop where
  t : T p σ s
  hint : HintIs s.mem (pa s (pH 0)) p.k h
  z : ∀ i < j, PolyIs s.mem (pa s (pZ i)) (toRq (vZ p (vSig p σ) i))
  r15 : s.gpr .r15 = flag (∀ i < j, normRq [toRq (vZ p (vSig p σ) i)] < p.γ₁ - p.β)

/-- The facts about the parameters `z[i]` needs. -/
def zChk (p : Params) (i : Nat) : Bool :=
  buChk (vB p) (vW p) (.r13, p.ctildeLen + lenZ p * i) (lenZ p) (pZ i) &&
    decide ((p.γ₁ - 1, p.γ₁) ∈ bitPackParams) && decide (lenZ p = 32 * bitlen (p.γ₁ - 1 + p.γ₁)) &&
    decide (p.ctildeLen + lenZ p * i + lenZ p ≤ p.sigLen) && tChk p [(pZ i, 1024)] &&
    keepB (vB p) [(pZ i, 1024)] (pH 0) (1024 * p.k) &&
    (List.range i).all (fun i' => keepB (vB p) [(pZ i, 1024)] (pZ i') 1024) && nlChk (vB p) (pZ i) &&
    decide (p.γ₁ - p.β < 2 ^ 31)

theorem zChk_all : ∀ p ∈ params, ∀ i < p.ℓ, zChk p i = true := by decide +kernel

theorem zOne_ok {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ)
    {h : List (Vector Bool n)} {i : Nat} (hi : i < p.ℓ) {s : State} (hs : S2 p h i σ s) :
    WP isa (zOne P p i) s (S2 p h (i + 1) σ) := by
  have hc := zChk_all p hp i hi
  simp only [zChk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩ := hc
  have L := hs.t.lay hp hv
  unfold zOne
  refine WP.seq (WP.mono (bitUnpackAt_ok C.bitUnpack L c2 c3 c1) fun s₁ ⟨hP₁, h15₁, hq₁⟩ => ?_)
  have t₁ := hs.t.step hp hv hP₁ c5
  have L₁ := t₁.lay hp hv
  rw [hs.t.sigSlice c4] at hq₁
  have e₁ : pa s₁ (pZ i) = pa s (pZ i) := hP₁.pa (show Reg.rbx ∈ bases by decide)
  rw [← e₁] at hq₁
  refine WP.seq (WP.mono (normLtAt_ok C.normLt L₁ c9 c8 hq₁.1) fun s₂ ⟨hP₂, h15₂, hr₂⟩ => ?_)
  have t₂ := t₁.step hp hv hP₂ (tChk_nil p hp)
  refine WP.mono (and15_ok s₂) fun s₃ ⟨⟨h15₃, hm₃⟩, k₃⟩ => ?_
  have hP₃ : PPostB s₂ s₃ [] := postB_of_keep k₃ (by decide) (by rw [hm₃]; exact Frame.refl _ _)
  have hP₂₃ : PPostB s₁ s₃ [] := PPostB.trans hP₂ hP₃ (fun _ h => absurd h List.not_mem_nil)
    (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil)
  refine ⟨t₂.step hp hv hP₃ (tChk_nil p hp), ?_, fun i' hi' => ?_, ?_⟩
  · exact L₁.keepHint hP₂₃ (keepB_nil c6) (L.keepHint hP₁ c6 hs.hint)
  · rcases (by omega_using [hi'] : i' < i ∨ i' = i) with hi' | rfl
    · exact L₁.keepPoly hP₂₃ (keepB_nil (c7 i' hi')) (L.keepPoly hP₁ (c7 i' hi') (hs.z i' hi'))
    · exact L₁.keepPoly hP₂₃ (keepB_nil_of (show Reg.rbx ∈ bases by decide) c8) hq₁
  · rw [h15₃, h15₂, h15₁, hs.r15]
    have hr : res s₂ = 1 ∨ res s₂ = 0 := by
      rw [hr₂]
      by_cases hh : normRq [polyAt s₁.mem (pa s₁ (pZ i))] < p.γ₁ - p.β
      · left; rw [ifp hh]
      · right; rw [ifn hh]
    rw [and_flag hr]
    have hq2 : polyAt s₁.mem (pa s₁ (pZ i)) = toRq (vZ p (vSig p σ) i) := hq₁.2
    refine flag_congr ⟨fun ⟨h1, h2⟩ i' hi' => ?_, fun h1 => ⟨fun i' hi' => h1 i' (by omega_using [hi']), ?_⟩⟩
    · rcases (by omega_using [hi'] : i' < i ∨ i' = i) with hi' | rfl
      · exact h1 i' hi'
      · rw [hr₂, hq2] at h2
        by_contra hn; rw [ifn hn] at h2; cases h2
    · rw [hr₂, hq2, ifp (h1 i (by omega_using []))]

end VG.Proof.MlDsa.X86_64.Verify

end

end

/-!
# ML-DSA verification on x86-64: the samplers

`ρ` to `SB` and `SB4`; each entry `Â[r, s]` (number `ℓr + s`) sampled from
`ρ ‖ s ‖ r`, four at a time (`aGrp_ok`), and then, if `kℓ` is not a multiple
of four, the last four again (`aTail_ok`, sampling again some done already),
and `c` (`ballStage_ok`), each reduced, and `r15` 1 only if every sampler
succeeded, with their outputs (`S3`, `S4`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Verify (vHint vZ vCt vRho aSeed)

/-! ## The seed -/

theorem seed_bytes (m : Mem) (A : Addr) (b1 b2 : Byte) :
    bytesAt ((m.writeW (A + BitVec.ofNat 64 32) b1).writeW (A + BitVec.ofNat 64 33) b2) A 34 =
      bytesAt m A 32 ++ [b1] ++ [b2] := by
  refine Proof.MlKem.bytesAt_eq (by simp [Proof.MlKem.bytesAt_length]) fun i hi => ?_
  rw [VG.WriteBytes.writeW8_apply, VG.WriteBytes.writeW8_apply]
  rcases (by omega_arith : i < 32 ∨ i = 32 ∨ i = 33) with h | rfl | rfl
  · have n1 : A + BitVec.ofNat 64 i ≠ A + BitVec.ofNat 64 33 := by intro e; bv_omega
    have n2 : A + BitVec.ofNat 64 i ≠ A + BitVec.ofNat 64 32 := by intro e; bv_omega
    rw [ifn n1, ifn n2]
    simp [List.getElem_append_left, Proof.MlKem.bytesAt_getElem, h, Proof.MlKem.bytesAt_length]
  · have n1 : A + BitVec.ofNat 64 32 ≠ A + BitVec.ofNat 64 33 := by intro e; bv_omega
    rw [ifn n1, ifp rfl]
    simp [Proof.MlKem.bytesAt_length]
  · rw [ifp rfl]
    simp [Proof.MlKem.bytesAt_length]

theorem integerToBytes_one (x : Nat) : integerToBytes x 1 = [BitVec.ofNat 8 x] := by
  simp [integerToBytes]


/-! ## `Â` -/

/-- Entry `(r', c')` of `Â`, number `l r' + c'` in rows of `l` entries, is sampled before entry `e`. -/
def Done (l e r' c' : Nat) : Prop := l * r' + c' < e

theorem rc_eq {l r c e : Nat} (hc : c < l) (h : l * r + c = e) : r = e / l ∧ c = e % l := by
  have hl : 0 < l := by omega_arith
  subst h
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_left _ _ hl, Nat.div_eq_of_lt hc, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]

theorem pA_eq (l r c : Nat) : pA l r c = pS (20 + (l * r + c)) := by
  show pS (20 + l * r + c) = _
  rw [Nat.add_assoc]

theorem l_pos : ∀ p ∈ params, 0 < p.ℓ := by decide

/-- Entry `e < kℓ` is `Â[e / ℓ, e mod ℓ]`. -/
theorem entry_lt {p : Params} (hp : p ∈ params) {e : Nat} (he : e < p.k * p.ℓ) : e / p.ℓ < p.k ∧ e % p.ℓ < p.ℓ :=
  ⟨(Nat.div_lt_iff_lt_mul (l_pos p hp)).mpr he, Nat.mod_lt _ (l_pos p hp)⟩

theorem done_all {p : Params} {r c : Nat} (hr : r < p.k) (hc : c < p.ℓ) : Done p.ℓ (p.k * p.ℓ) r c := by
  unfold Done
  have := Nat.mul_le_mul_left p.ℓ (show r + 1 ≤ p.k by omega_arith)
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm p.ℓ p.k] at this
  omega_arith

/-- After the first `e` entries of `Â`, with the hint `h`. -/
structure S3 (p : Params) (h : List (Vector Bool n)) (e : Nat) (σ st : State) : Prop where
  t : T p σ st
  hint : HintIs st.mem (pa st (pH 0)) p.k h
  z : ∀ i < p.ℓ, PolyIs st.mem (pa st (pZ i)) (toRq (vZ p (vSig p σ) i))
  rho : bytesAt st.mem (pa st (sc oSB)) 32 = vRho (vPk p σ)
  rho4 : ∀ k < 4, bytesAt st.mem (pa st (sc (oSB4 + 34 * k))) 32 = vRho (vPk p σ)
  red : ∀ r' < p.k, ∀ c' < p.ℓ, Done p.ℓ e r' c' → Reduced st.mem (pa st (pA p.ℓ r' c'))
  ok : ∃ q : Bool, st.gpr .r15 = flag (q = true) ∧
    (q = true → ∀ r' < p.k, ∀ c' < p.ℓ, Done p.ℓ e r' c' →
      ∃ b : Bounds, rejNTTPoly b.rejNTT (aSeed (vPk p σ) r' c') = some (polyAt st.mem (pa st (pA p.ℓ r' c')))) ∧
    (q = false → ∃ r' < p.k, ∃ c' < p.ℓ, Done p.ℓ e r' c' ∧ rejNTTPoly minBounds.rejNTT (aSeed (vPk p σ) r' c') = none)

abbrev wsB : List (Ptr × Nat) := [(sc (oSB + 32), 1), (sc (oSB + 33), 1)]
/-- The two bytes of seed `j` of `SB4`. -/
abbrev wsS (j : Nat) : List (Ptr × Nat) := [(sc (oSB4 + 34 * j + 32), 1), (sc (oSB4 + 34 * j + 33), 1)]
abbrev wsA (e : Nat) : List (Ptr × Nat) := [(pS (20 + e), 1024), (sc oSS, 2048)]

/-- A state keeps what `S3` says across a piece that writes `ws`. -/
def keepChk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  tChk p ws && keepB (vB p) ws (pH 0) (1024 * p.k) && (List.range p.ℓ).all (fun i => keepB (vB p) ws (pZ i) 1024)

/-- The slot of entry `e` lies apart from what the entries after it write but their own slots. -/
def slotKeep (p : Params) (e : Nat) : Bool :=
  keepB (vB p) wsB (pS (20 + e)) 1024 && keepB (vB p) [(sc oSS, 2048)] (pS (20 + e)) 1024 &&
    keepB (vB p) [(sc (oR4 p), 8192)] (pS (20 + e)) 1024 &&
    (List.range 4).all (fun j => keepB (vB p) (wsS j) (pS (20 + e)) 1024)

/-- The facts about the parameters entry `e` needs. -/
def aChk (p : Params) (e : Nat) : Bool :=
  inB (vW p) (sc (oSB + 32)) 1 && inB (vW p) (sc (oSB + 33)) 1 && rejChk (vB p) (vW p) (pS (20 + e)) &&
    inB (vB p) (pS (20 + e)) 1024 && inB (vW p) (pS (20 + e)) 1024 && keepChk p wsB && keepChk p (wsA e) &&
    keepB (vB p) wsB (sc oSB) 32 && keepB (vB p) (wsA e) (sc oSB) 32 &&
    (List.range 4).all (fun k => keepB (vB p) wsB (sc (oSB4 + 34 * k)) 32 &&
      keepB (vB p) (wsA e) (sc (oSB4 + 34 * k)) 32) && slotKeep p e

theorem aChk_all : ∀ p ∈ params, ∀ e < p.k * p.ℓ, aChk p e = true := by decide +kernel

/-- The entries done before `e` are kept by the writes of seed `j`'s bytes. -/
theorem keep_slot_done {p : Params} (hp : p ∈ params) {e j r' c' : Nat} (hj : j < 4) (he : e ≤ p.k * p.ℓ)
    (hd : Done p.ℓ e r' c') : keepB (vB p) (wsS j) (pA p.ℓ r' c') 1024 = true := by
  unfold Done at hd
  have hk := aChk_all p hp _ (show p.ℓ * r' + c' < p.k * p.ℓ by omega_arith)
  simp only [aChk, slotKeep, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hk
  rw [pA_eq]
  exact hk.2.2 j hj

/-- The entries done before the four from `e` are kept by their sampling. -/
theorem keep_grp_done {p : Params} (hp : p ∈ params) {e r' c' : Nat} (he : e ≤ p.k * p.ℓ)
    (hin : inB (vB p) (pS (20 + e)) 4096 = true) (hd : Done p.ℓ e r' c') :
    keepB (vB p) [(pS (20 + e), 4096), (sc (oR4 p), 8192)] (pA p.ℓ r' c') 1024 = true := by
  unfold Done at hd
  have hk := aChk_all p hp _ (show p.ℓ * r' + c' < p.k * p.ℓ by omega_arith)
  simp only [aChk, slotKeep, Bool.and_eq_true] at hk
  have h3 := hk.2.1.2
  rw [pA_eq]
  simp only [keepB, sepB, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h3 ⊢
  simp only [h3, hin, true_and, and_true]
  simp only [oP, bne_self_eq_false, Bool.false_and, beq_self_eq_true, Bool.true_and, Bool.false_or,
    Bool.or_eq_true]
  exact .inl (decide_eq_true (by omega_arith))


theorem keepChk_spec {p : Params} {ws : List (Ptr × Nat)} (h : keepChk p ws = true) :
    tChk p ws = true ∧ keepB (vB p) ws (pH 0) (1024 * p.k) = true ∧ ∀ i < p.ℓ, keepB (vB p) ws (pZ i) 1024 = true := by
  simp only [keepChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem setB2At_ok {p : Params} {s : State} (L : Lay (vR p) (vW p) s) (B : Nat)
    (h32 : inB (vW p) (sc (B + 32)) 1 = true)
    (h33 : inB (vW p) (sc (B + 33)) 1 = true) (x y : Nat) (hx : x < 256) (hy : y < 256) :
    WP isa (.block (setB (sc (B + 32)) x ++ setB (sc (B + 33)) y)) s fun s' =>
      PPostB s s' [(sc (B + 32), 1), (sc (B + 33), 1)] ∧
      s'.gpr .r15 = s.gpr .r15 ∧
      s'.mem = (s.mem.writeW (pa s (sc B) + BitVec.ofNat 64 32) (BitVec.ofNat 8 x)).writeW
        (pa s (sc B) + BitVec.ofNat 64 33) (BitVec.ofNat 8 y) := by
  have e32 : pa s (sc (B + 32)) = pa s (sc B) + BitVec.ofNat 64 32 := by
    simp only [pa]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have e33 : pa s (sc (B + 33)) = pa s (sc B) + BitVec.ofNat 64 33 := by
    simp only [pa]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [WP.block_append_iff]
  refine WP.mono (setB_ok _ x (show Reg.rbx ≠ .rax by decide) hx s (L.inW h32)) fun s₁ ⟨hm₁, k₁⟩ => ?_
  have e₁ : pa s₁ (sc (B + 33)) = pa s (sc (B + 33)) := by simp only [pa]; rw [k₁.gpr (by decide)]
  refine WP.mono (setB_ok _ y (show Reg.rbx ≠ .rax by decide) hy s₁ (by rw [k₁.2.2, e₁]; exact L.inW h33)) fun s₂ ⟨hm₂, k₂⟩ =>
    ⟨postB_of_keep (k₁.trans k₂) (by decide) ?_, by rw [k₂.gpr (by decide), k₁.gpr (by decide)], ?_⟩
  · rw [hm₂, hm₁, e₁]
    have hc : ∀ q : Ptr, (Region.mk (pa s q) 1).Contains (pa s q) 1 := fun q => Region.contains_self _ _
    exact ((Frame.refl _ _).writeW (List.mem_cons_self ..) _ (hc _)).writeW
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _ (hc _)
  · rw [hm₂, hm₁, e₁, e32, e33]

theorem kl_le : ∀ p ∈ params, p.ℓ ≤ 7 ∧ p.k ≤ 8 := by decide

/-! ## Four entries at a time -/

/-- A piece writing `ws` keeps the entries done before `e` but those `ex` says, and `S3`'s other facts. -/
def s3Chk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  keepChk p ws && keepB (vB p) ws (sc oSB) 32 && (List.range 4).all (fun k => keepB (vB p) ws (sc (oSB4 + 34 * k)) 32)

theorem s3Chk_spec {p : Params} {e : Nat} {ex : Nat → Nat → Bool} {ws : List (Ptr × Nat)}
    (h : s3Chk p ws = true)
    (kE : ∀ r' < p.k, ∀ c' < p.ℓ, Done p.ℓ e r' c' → keepB (vB p) ws (pA p.ℓ r' c') 1024 = true) :
    keepChk p ws = true ∧ keepB (vB p) ws (sc oSB) 32 = true ∧
      (∀ k < 4, keepB (vB p) ws (sc (oSB4 + 34 * k)) 32 = true) ∧
      ∀ r' < p.k, ∀ c' < p.ℓ, Done p.ℓ e r' c' → ex r' c' = false → keepB (vB p) ws (pA p.ℓ r' c') 1024 = true := by
  simp only [s3Chk, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, fun k hk => List.all_eq_true.mp h3 k (List.mem_range.mpr hk),
    fun r' hr' c' hc' hd _ => kE r' hr' c' hc' hd⟩

/-- `S3` across a piece that writes `ws`, which `s3Chk` says keeps it. -/
theorem S3.keep {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ) {h : List (Vector Bool n)} {e : Nat}
    {s s' : State} (hs : S3 p h e σ s) {ws : List (Ptr × Nat)} (hP : PPostB s s' ws)
    (h15 : s'.gpr .r15 = s.gpr .r15) (hc : s3Chk p ws = true)
    (hE : ∀ r' < p.k, ∀ c' < p.ℓ, Done p.ℓ e r' c' → keepB (vB p) ws (pA p.ℓ r' c') 1024 = true) :
    S3 p h e σ s' := by
  obtain ⟨hk, kSB, k4, kE⟩ := s3Chk_spec (ex := fun _ _ => false) hc hE
  obtain ⟨tk, hh, zk⟩ := keepChk_spec hk
  have L := hs.t.lay hp hv
  obtain ⟨q, hq, hok, hbad⟩ := hs.ok
  refine ⟨hs.t.step hp hv hP tk, L.keepHint hP hh hs.hint, fun i hi => L.keepPoly hP (zk i hi) (hs.z i hi),
    by rw [L.keepBytes hP kSB, hs.rho], fun k hk => by rw [L.keepBytes hP (k4 k hk), hs.rho4 k hk],
    fun r' hr' c' hc' hd => L.keepRed hP (kE r' hr' c' hc' hd rfl) (hs.red r' hr' c' hc' hd),
    q, by rw [h15, hq], fun hq' r' hr' c' hc' hd => ?_, hbad⟩
  obtain ⟨b, hb⟩ := hok hq' r' hr' c' hc' hd
  exact ⟨b, by rw [hb, L.keepPolyAt hP (kE r' hr' c' hc' hd rfl)]⟩

/-- What setting the bytes of seed `j` needs, after `e` entries. -/
def slotChk (p : Params) (j : Nat) : Bool :=
  inB (vW p) (sc (oSB4 + 34 * j + 32)) 1 && inB (vW p) (sc (oSB4 + 34 * j + 33)) 1 &&
    s3Chk p (wsS j) &&
    (List.range j).all (fun k => keepB (vB p) (wsS j) (sc (oSB4 + 34 * k)) 34)

/-- After the first `d` entries, and the bytes of the first `j` seeds of `SB4`, for the entries `e + k`. -/
structure GS (p : Params) (h : List (Vector Bool n)) (e d j : Nat) (σ st : State) : Prop where
  s3 : S3 p h d σ st
  done : ∀ k < j, bytesAt st.mem (pa st (sc (oSB4 + 34 * k))) 34 = aSeed (vPk p σ) ((e + k) / p.ℓ) ((e + k) % p.ℓ)

theorem slot_ok {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ) {h : List (Vector Bool n)}
    {e d j : Nat} (hj : j < 4) (he : e + j < p.k * p.ℓ) (hd : d ≤ p.k * p.ℓ) (hck : slotChk p j = true) {s : State}
    (hs : GS p h e d j σ s) : WP isa (.block (setSR p e j)) s (GS p h e d (j + 1) σ) := by
  have hkl := kl_le p hp
  obtain ⟨hr, hc⟩ := entry_lt hp he
  simp only [slotChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hck
  obtain ⟨⟨⟨h32, h33⟩, h3⟩, hk⟩ := hck
  have L := hs.s3.t.lay hp hv
  unfold setSR
  refine WP.mono (setB2At_ok L (oSB4 + 34 * j) h32 h33 ((e + j) % p.ℓ) ((e + j) / p.ℓ) (by omega_arith) (by omega_arith))
    fun s₁ ⟨hP₁, h15₁, hm₁⟩ => ⟨hs.s3.keep hp hv hP₁ h15₁ h3 fun _ _ _ _ hd' => keep_slot_done hp hj hd hd', fun k hk' => ?_⟩
  rcases (by omega_arith : k < j ∨ k = j) with hk' | rfl
  · rw [L.keepBytes hP₁ (hk k hk'), hs.done k hk']
  · rw [hP₁.pa (show Reg.rbx ∈ bases by decide), hm₁, seed_bytes, hs.s3.rho4 k hj, aSeed, integerToBytes_one,
      integerToBytes_one]

/-- Whether entry `(r', c')` is one of the four from `e`. -/
abbrev inGrp (l e r' c' : Nat) : Bool := decide (e ≤ l * r' + c') && decide (l * r' + c' < e + 4)

/-- The facts about the parameters the entries `e, …, e + 3` need. -/
def gChk (p : Params) (e : Nat) : Bool :=
  (List.range 4).all (fun j => slotChk p j) && rej4Chk (vB p) (vW p) (pS (20 + e)) (sc (oR4 p)) &&
    inB (vB p) (pS (20 + e)) 4096 && inB (vW p) (pS (20 + e)) 4096 &&
    s3Chk p [(pS (20 + e), 4096), (sc (oR4 p), 8192)] && decide (e + 4 ≤ p.k * p.ℓ)

theorem gChk_all : ∀ p ∈ params, ∀ g < p.k * p.ℓ / 4, gChk p (4 * g) = true := by decide +kernel

theorem pa_poly4 (s : State) (e k : Nat) : poly4 (pa s (pS (20 + e))) k = pa s (pS (20 + (e + k))) := by
  unfold poly4
  simp only [pa]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show oP (20 + e) + 1024 * k = oP (20 + (e + k)) by
    simp only [oP]; omega_arith]

theorem gTail_all : ∀ p ∈ params, gChk p (p.k * p.ℓ - 4) = true := by decide +kernel

/-- The four entries from `e`, after the first `d`, from `e` to `e + 4`: those of them already
done are sampled again. -/
theorem aQuad_ok {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ)
    {h : List (Vector Bool n)} {e d : Nat} (hed : e ≤ d) (hde : d ≤ e + 4) (hck : gChk p e = true) {s : State}
    (hs : S3 p h d σ s) : WP isa (aQuad P p e) s (S3 p h (e + 4) σ) := by
  have hkl := kl_le p hp
  simp only [gChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hck
  obtain ⟨⟨⟨⟨⟨hsl, hrej⟩, hin⟩, hwa⟩, hG⟩, hl⟩ := hck
  obtain ⟨hk, kSB, k4, kE⟩ := s3Chk_spec (ex := inGrp p.ℓ (e)) hG fun _ _ _ _ hd => keep_grp_done hp (by omega_arith) hin hd
  obtain ⟨tk, hh, zk⟩ := keepChk_spec hk
  unfold aQuad
  refine WP.seq (WP.mono (slot_ok hp hv (by decide) (by omega_arith) (by omega_arith) (hsl 0 (by decide))
    ⟨hs, fun _ h => absurd h (by omega_arith)⟩) fun _ g₁ => ?_)
  refine WP.seq (WP.mono (slot_ok hp hv (by decide) (by omega_arith) (by omega_arith) (hsl 1 (by decide)) g₁)
    fun _ g₂ => ?_)
  refine WP.seq (WP.mono (slot_ok hp hv (by decide) (by omega_arith) (by omega_arith) (hsl 2 (by decide)) g₂)
    fun _ g₃ => ?_)
  refine WP.seq (WP.mono (slot_ok hp hv (by decide) (by omega_arith) (by omega_arith) (hsl 3 (by decide)) g₃)
    fun s₄ g₄ => ?_)
  have L₄ := g₄.s3.t.lay hp hv
  obtain ⟨q, h15, hok, hbad⟩ := g₄.s3.ok
  have hseed : ∀ k < 4, seed4 s₄.mem (pa s₄ (sc oSB4)) k =
      aSeed (vPk p σ) ((e + k) / p.ℓ) ((e + k) % p.ℓ) := fun k hk => by
    unfold seed4
    rw [show pa s₄ (sc oSB4) + BitVec.ofNat 64 (34 * k) = pa s₄ (sc (oSB4 + 34 * k)) by
      simp only [pa]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]]
    exact g₄.done k hk
  refine WP.mono (sampled4_ok L₄ hin hwa h15 (List.mem_cons_self ..)
    (F := fun k b => rejNTTPoly b.rejNTT (aSeed (vPk p σ) ((e + k) / p.ℓ) ((e + k) % p.ℓ)))
    (WP.mono (rej4At_ok C.rej4 L₄ hrej) fun s' ⟨hP, h15', hred, ho⟩ => ⟨hP, h15', hred, ?_⟩))
    fun s₅ ⟨hP₅, hred₅, rr, hrr, h15₅, hs1, hs0⟩ => ?_
  · rcases ho with ⟨h1, hb⟩ | ⟨h0, k, hk, hn⟩
    · exact .inl ⟨h1, fun k hk => by rw [← hseed k hk]; exact hb k hk⟩
    · exact .inr ⟨h0, k, hk, by rw [← hseed k hk]; exact hn⟩
  have e₅ : ∀ k, poly4 (pa s₄ (pS (20 + e))) k = pa s₅ (pS (20 + (e + k))) := fun k => by
    rw [pa_poly4, hP₅.pa (show Reg.rbx ∈ bases by decide)]
  have hgrp : ∀ r' c', inGrp p.ℓ (e) r' c' = true → e ≤ p.ℓ * r' + c' ∧ p.ℓ * r' + c' < e + 4 :=
    fun r' c' hg => by simp only [inGrp, Bool.and_eq_true, decide_eq_true_eq] at hg; exact hg
  have hdw : ∀ r' c', Done p.ℓ e r' c' → Done p.ℓ d r' c' := fun r' c' h => by unfold Done at h ⊢; omega_arith
  have hout : ∀ r' c', Done p.ℓ (e + 4) r' c' → inGrp p.ℓ (e) r' c' = false → Done p.ℓ e r' c' :=
    fun r' c' hd hx => by
      simp only [inGrp, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hx
      unfold Done at hd ⊢
      omega_arith
  refine ⟨g₄.s3.t.step hp hv hP₅ tk, L₄.keepHint hP₅ hh g₄.s3.hint,
    fun i hi => L₄.keepPoly hP₅ (zk i hi) (g₄.s3.z i hi), by rw [L₄.keepBytes hP₅ kSB, g₄.s3.rho],
    fun k hk => by rw [L₄.keepBytes hP₅ (k4 k hk), g₄.s3.rho4 k hk], fun r' hr' c' hc' hd => ?_,
    q && (rr == 1), ?_, fun hq r' hr' c' hc' hd => ?_, fun hq => ?_⟩
  · cases hx : inGrp p.ℓ (e) r' c'
    · exact L₄.keepRed hP₅ (kE r' hr' c' hc' (hout r' c' hd hx) hx) (g₄.s3.red r' hr' c' hc' (hdw r' c' (hout r' c' hd hx)))
    · obtain ⟨g1, g2⟩ := hgrp r' c' hx
      have := hred₅ (p.ℓ * r' + c' - e) (by omega_arith)
      rwa [e₅, show e + (p.ℓ * r' + c' - e) = p.ℓ * r' + c' by omega_arith, ← pA_eq] at this
  · rw [h15₅]
    exact flag_congr (by cases q <;> simp)
  · simp only [Bool.and_eq_true, beq_iff_eq] at hq
    cases hx : inGrp p.ℓ (e) r' c'
    · obtain ⟨b, hb⟩ := hok hq.1 r' hr' c' hc' (hdw r' c' (hout r' c' hd hx))
      exact ⟨b, by rw [hb, L₄.keepPolyAt hP₅ (kE r' hr' c' hc' (hout r' c' hd hx) hx)]⟩
    · obtain ⟨g1, g2⟩ := hgrp r' c' hx
      obtain ⟨b, hb⟩ := hs1 hq.2 (p.ℓ * r' + c' - e) (by omega_arith)
      obtain ⟨er, ec⟩ := rc_eq hc' (show p.ℓ * r' + c' = e + (p.ℓ * r' + c' - e) by omega_arith)
      rw [← er, ← ec, e₅, show e + (p.ℓ * r' + c' - e) = p.ℓ * r' + c' by omega_arith, ← pA_eq] at hb
      exact ⟨b, hb⟩
  · cases hq' : q
    · obtain ⟨r', hr', c', hc', hd, hn⟩ := hbad hq'
      exact ⟨r', hr', c', hc', by unfold Done at hd ⊢; omega_arith, hn⟩
    · rw [hq'] at hq
      have h0 : rr = 0 := by
        rcases hrr with h1 | h0
        · rw [h1] at hq; cases hq
        · exact h0
      obtain ⟨k, hk, hn⟩ := hs0 h0
      obtain ⟨hr, hc⟩ := entry_lt hp (show e + k < p.k * p.ℓ by omega_arith)
      exact ⟨_, hr, _, hc, by unfold Done; have := Nat.div_add_mod (e + k) p.ℓ; omega_arith, hn⟩

theorem aGrp_ok {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ)
    {h : List (Vector Bool n)} {g : Nat} (hck : gChk p (4 * g) = true) {s : State}
    (hs : S3 p h (4 * g) σ s) : WP isa (aGrp P p g) s (S3 p h (4 * (g + 1)) σ) :=
  aQuad_ok C hp hv (Nat.le_refl _) (by omega_arith) hck hs

/-- After the samplers, with the hint `h`. -/
structure S4 (p : Params) (h : List (Vector Bool n)) (σ st : State) : Prop where
  t : T p σ st
  hint : HintIs st.mem (pa st (pH 0)) p.k h
  z : ∀ i < p.ℓ, PolyIs st.mem (pa st (pZ i)) (toRq (vZ p (vSig p σ) i))
  red : ∀ r < p.k, ∀ c < p.ℓ, Reduced st.mem (pa st (pA p.ℓ r c))
  redC : Reduced st.mem (pa st pC)
  ok : ∃ q : Bool, st.gpr .r15 = flag (q = true) ∧
    (q = true → (∀ r < p.k, ∀ c < p.ℓ,
      ∃ b : Bounds, rejNTTPoly b.rejNTT (aSeed (vPk p σ) r c) = some (polyAt st.mem (pa st (pA p.ℓ r c)))) ∧
      ∃ b : Bounds, (sampleInBall p.τ b.ball (vCt p (vSig p σ))).map toRq = some (polyAt st.mem (pa st pC))) ∧
    (q = false → (∃ r < p.k, ∃ c < p.ℓ, rejNTTPoly minBounds.rejNTT (aSeed (vPk p σ) r c) = none) ∨
      (sampleInBall p.τ minBounds.ball (vCt p (vSig p σ))).map toRq = none)

abbrev wsC : List (Ptr × Nat) := [(pC, 1024), (sc oSS, 2048)]

/-- The facts about the parameters the copy of `ρ` and `c` need. -/
def sChk (p : Params) : Bool :=
  sepB (vB p) (.rbp, 0) 32 (sc oSB) 32 && inB (vW p) (sc oSB) 32 && keepChk p [(sc oSB, 32)] &&
    decide (32 ≤ p.pkLen) && ballChk (vB p) (vW p) (.r13, 0) p.ctildeLen pC &&
    decide ((p.ctildeLen, p.τ) ∈ ballParams) && decide (p.ctildeLen ≤ p.sigLen) && keepChk p wsC &&
    inB (vB p) pC 1024 && inB (vW p) pC 1024 &&
    (List.range p.k).all (fun r => (List.range p.ℓ).all fun c => keepB (vB p) wsC (pA p.ℓ r c) 1024)

theorem sChk_all : ∀ p ∈ params, sChk p = true := by decide +kernel

/-- After `ρ` is copied to `SB` and the first `j` seeds of `SB4`. -/
structure RhoS (p : Params) (h : List (Vector Bool n)) (j : Nat) (σ st : State) : Prop where
  t : T p σ st
  hint : HintIs st.mem (pa st (pH 0)) p.k h
  z : ∀ i < p.ℓ, PolyIs st.mem (pa st (pZ i)) (toRq (vZ p (vSig p σ) i))
  rho : bytesAt st.mem (pa st (sc oSB)) 32 = vRho (vPk p σ)
  rho4 : ∀ k < j, bytesAt st.mem (pa st (sc (oSB4 + 34 * k))) 32 = vRho (vPk p σ)
  f15 : st.gpr .r15 = flag True

theorem copyRho_ok {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ)
    {h : List (Vector Bool n)} {s : State} (hs : S2 p h p.ℓ σ s) (h15 : s.gpr .r15 = flag True) :
    WP isa (copy (sc oSB) (.rbp, 0) 32) s (RhoS p h 0 σ) := by
  have hc := sChk_all p hp
  simp only [sChk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hc
  obtain ⟨t3, h3, z3⟩ := keepChk_spec c3
  have L := hs.t.lay hp hv
  refine WP.mono (copy_ok L (by decide) c1 c2) fun s₁ ⟨hP₁, h15₁, hcp⟩ => ?_
  have t₁ := hs.t.step hp hv hP₁ t3
  refine ⟨t₁, L.keepHint hP₁ h3 hs.hint, fun i hi => L.keepPoly hP₁ (z3 i hi) (hs.z i hi), ?_,
    fun _ h => absurd h (Nat.not_lt_zero _), by rw [h15₁, h15]⟩
  rw [hP₁.pa (show Reg.rbx ∈ bases by decide), hcp, hs.t.pkSlice c4, List.drop_zero]
  rfl

/-- What copying `ρ` to seed `j` of `SB4` needs. -/
def rChk (p : Params) (j : Nat) : Bool :=
  sepB (vB p) (.rbp, 0) 32 (sc (oSB4 + 34 * j)) 32 && inB (vW p) (sc (oSB4 + 34 * j)) 32 &&
    keepChk p [(sc (oSB4 + 34 * j), 32)] && keepB (vB p) [(sc (oSB4 + 34 * j), 32)] (sc oSB) 32 &&
    (List.range j).all (fun k => keepB (vB p) [(sc (oSB4 + 34 * j), 32)] (sc (oSB4 + 34 * k)) 32)

theorem rChk_all : ∀ p ∈ params, ∀ j < 4, rChk p j = true := by decide +kernel

theorem copyK_ok {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ) {h : List (Vector Bool n)} {j : Nat}
    (hj : j < 4) {s : State} (hs : RhoS p h j σ s) :
    WP isa (copy (sc (oSB4 + 34 * j)) (.rbp, 0) 32) s (RhoS p h (j + 1) σ) := by
  have hc := rChk_all p hp j hj
  simp only [rChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩ := hc
  have hpk : 32 ≤ p.pkLen := by
    have := sChk_all p hp
    simp only [sChk, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.1.1.1.1.1.1.2
  obtain ⟨t3, h3, z3⟩ := keepChk_spec c3
  have L := hs.t.lay hp hv
  refine WP.mono (copy_ok L (by decide) c1 c2) fun s₁ ⟨hP₁, h15₁, hcp⟩ => ?_
  refine ⟨hs.t.step hp hv hP₁ t3, L.keepHint hP₁ h3 hs.hint, fun i hi => L.keepPoly hP₁ (z3 i hi) (hs.z i hi),
    by rw [L.keepBytes hP₁ c4, hs.rho], fun k hk => ?_, by rw [h15₁, hs.f15]⟩
  rcases (by omega_arith : k < j ∨ k = j) with hk | rfl
  · rw [L.keepBytes hP₁ (c5 k hk), hs.rho4 k hk]
  · rw [hP₁.pa (show Reg.rbx ∈ bases by decide), hcp, hs.t.pkSlice hpk, List.drop_zero]
    rfl

theorem RhoS.s3 {p : Params} {h : List (Vector Bool n)} {σ s : State} (r : RhoS p h 4 σ s) : S3 p h 0 σ s :=
  ⟨r.t, r.hint, r.z, r.rho, r.rho4, fun r' _ c' _ hd => absurd hd (by unfold Done; omega_arith),
    true, by rw [r.f15]; exact flag_congr (by simp), fun _ r' _ c' _ hd => absurd hd (by unfold Done; omega_arith),
    fun hq => absurd hq (by simp)⟩

theorem rhos_ok {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ)
    {h : List (Vector Bool n)} {s : State} (hs : S2 p h p.ℓ σ s) (h15 : s.gpr .r15 = flag True) :
    WP isa rhos s (S3 p h 0 σ) := by
  unfold rhos
  refine WP.seq (WP.mono (copyRho_ok hp hv hs h15) fun s₀ r₀ => ?_)
  refine WP.seq (WP.mono (copyK_ok hp hv (j := 0) (by decide) r₀) fun s₁ r₁ => ?_)
  refine WP.seq (WP.mono (copyK_ok hp hv (j := 1) (by decide) r₁) fun s₂ r₂ => ?_)
  refine WP.seq (WP.mono (copyK_ok hp hv (j := 2) (by decide) r₂) fun s₃ r₃ => ?_)
  exact WP.mono (copyK_ok hp hv (j := 3) (by decide) r₃) fun _ r₄ => r₄.s3

theorem ballStage_ok {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ)
    {h : List (Vector Bool n)} {s₂ : State} (hs₂ : S3 p h (p.k * p.ℓ) σ s₂) :
    WP isa (sampled (ballAt P (.r13, 0) p.ctildeLen p.τ pC) pC) s₂ (S4 p h σ) := by
  have hc := sChk_all p hp
  simp only [sChk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩ := hc
  obtain ⟨t8, h8, z8⟩ := keepChk_spec c8
  have L₂ := hs₂.t.lay hp hv
  obtain ⟨q, h15₂, hok, hbad⟩ := hs₂.ok
  refine WP.mono (sampled_ok L₂ c9 c10 h15₂ (List.mem_cons_self ..)
    (WP.mono (ballAt_ok C.ball L₂ c6 c5) fun s' ⟨hP, h15', hr', ho⟩ => ⟨hP, h15', hr', ho⟩))
    fun s₃ ⟨hP₃, hred, rr, hrr, h15₃, hs1, hs0⟩ => ?_
  have hct : bytesAt s₂.mem (pa s₂ (.r13, 0)) p.ctildeLen = vCt p (vSig p σ) := by
    rw [hs₂.t.sigSlice (by omega_arith), List.drop_zero]; rfl
  rw [hct] at hs1 hs0
  have hdone : ∀ r' c', r' < p.k → c' < p.ℓ → Done p.ℓ (p.k * p.ℓ) r' c' := fun _ _ hr hc => done_all hr hc
  have ec : pa s₃ pC = pa s₂ pC := hP₃.pa (show Reg.rbx ∈ bases by decide)
  refine ⟨hs₂.t.step hp hv hP₃ t8, L₂.keepHint hP₃ h8 hs₂.hint, fun i hi => L₂.keepPoly hP₃ (z8 i hi) (hs₂.z i hi),
    fun r hr c hc => L₂.keepRed hP₃ (c11 r hr c hc) (hs₂.red r hr c hc (hdone r c hr hc)), by rw [ec]; exact hred,
    q && (rr == 1), by rw [h15₃]; exact flag_congr (by cases q <;> simp), fun hq => ?_, fun hq => ?_⟩
  · simp only [Bool.and_eq_true, beq_iff_eq] at hq
    refine ⟨fun r hr c hc => ?_, ?_⟩
    · obtain ⟨b, hb⟩ := hok hq.1 r hr c hc (hdone r c hr hc)
      exact ⟨b, by rw [hb, L₂.keepPolyAt hP₃ (c11 r hr c hc)]⟩
    · obtain ⟨b, hb⟩ := hs1 hq.2
      exact ⟨b, by rw [hb, ec]⟩
  · cases hq' : q
    · obtain ⟨r', hr', c', hc', _, hn⟩ := hbad hq'
      exact .inl ⟨r', hr', c', hc', hn⟩
    · rw [hq'] at hq
      have h0 : rr = 0 := by
        rcases hrr with h1 | h0
        · rw [h1] at hq; cases hq
        · exact h0
      exact .inr (hs0 h0)

theorem kl_ge : ∀ p ∈ params, 4 ≤ p.k * p.ℓ := by decide

/-- After the groups of four, the entries left. -/
theorem aTail_ok {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ)
    {h : List (Vector Bool n)} {s : State} (hs : S3 p h (4 * (p.k * p.ℓ / 4)) σ s) :
    WP isa (aTail P p) s (S3 p h (p.k * p.ℓ) σ) := by
  have h4 := kl_ge p hp
  have hm := Nat.div_add_mod (p.k * p.ℓ) 4
  have hlt := Nat.mod_lt (p.k * p.ℓ) (show 4 > 0 by decide)
  unfold aTail
  rcases (by omega_arith : p.k * p.ℓ % 4 = 0 ∨ (p.k * p.ℓ % 4 + 3) / 4 = 1) with h0 | h1
  · rw [show (p.k * p.ℓ % 4 + 3) / 4 = 0 by omega_arith, seqR]
    exact WP.block_nil (by rw [show p.k * p.ℓ = 4 * (p.k * p.ℓ / 4) by omega_arith]; exact hs)
  · rw [h1, seqR, seqR]
    refine WP.seq (WP.mono (aQuad_ok C hp hv (by omega_arith) (by omega_arith) (gTail_all p hp) hs)
      fun s' hs' => WP.block_nil ?_)
    rwa [show p.k * p.ℓ - 4 + 4 = p.k * p.ℓ by omega_arith] at hs'

theorem samples_ok {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ)
    {h : List (Vector Bool n)} {s : State} (hs : S2 p h p.ℓ σ s) (h15 : s.gpr .r15 = flag True) :
    WP isa (samples P p) s (S4 p h σ) := by
  unfold samples
  refine WP.seq (WP.mono (rhos_ok hp hv hs h15) fun s₁ s₁3 => ?_)
  refine WP.seq (WP.mono (seqR_ok (I := fun g => S3 p h (4 * g) σ) (p.k * p.ℓ / 4) 0
    (fun g _ hg st hst => aGrp_ok C hp hv (gChk_all p hp g (by omega_arith)) hst) s₁ s₁3) fun s₂ hs₂ => ?_)
  rw [Nat.zero_add] at hs₂
  refine WP.seq (WP.mono (aTail_ok C hp hv hs₂) fun s₃ hs₃ => ?_)
  exact ballStage_ok C hp hv hs₃

end VG.Proof.MlDsa.X86_64.Verify

end

end

/-!
# ML-DSA verification on x86-64: `w′₁`, row by row

With the entries `A'` of `Â` and `ĉ = cH` as the samplers left them: `ẑ[i] =
NTT(z[i])` (`nttZ_ok`), `ĉ` (`nttC_ok`), and each row `r` of `w′₁`, packed to
`B + r · 32 bitlen b` (`row_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Verify

open VG.Proof.MlDsa.Arith.Representation

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Verify (vHint vZ vCt vRho aSeed zHat dotAcc t1Hat wRow w1Row vT1 add_zero_left hintAt_row useHint_le)

/-- While computing, with the hint `h`, `Â = A'`, the result so far `Q`:
`ẑ[i]` for `i < j` (`z[i]` after), `ĉ` or `c` at `C` (`cH`), and the rows
of `w′₁` before `r` packed. -/
structure SC (p : Params) (h : List (Vector Bool n)) (A' : Nat → Nat → Poly) (Q : Prop) [Decidable Q]
    (j : Nat) (cH : Poly) (r : Nat) (σ st : State) : Prop where
  t : T p σ st
  hint : HintIs st.mem (pa st (pH 0)) p.k h
  a : ∀ r' < p.k, ∀ c < p.ℓ, PolyIs st.mem (pa st (pA p.ℓ r' c)) (A' r' c)
  z : ∀ i < p.ℓ, PolyIs st.mem (pa st (pZ i)) (if i < j then zHat p (vSig p σ) i else toRq (vZ p (vSig p σ) i))
  c : PolyIs st.mem (pa st pC) cH
  rows : ∀ r' < r, bytesAt st.mem (pa st (sc (oB + w1Len p * r'))) (w1Len p) =
    simpleBitPack (w1Row p (vPk p σ) (vSig p σ) A' cH h r') (w1Max p)
  r15 : st.gpr .r15 = flag Q

/-- What a piece writing `ws` keeps of `SC`: `T`, the hint, `Â` and `z[i]`
but `z[ex]`, but for `C` and the rows. -/
def keepC (p : Params) (ws : List (Ptr × Nat)) (ex : Nat) : Bool :=
  tChk p ws && keepB (vB p) ws (pH 0) (1024 * p.k) &&
    (List.range p.ℓ).all (fun i => i == ex || keepB (vB p) ws (pZ i) 1024) &&
    (List.range p.k).all (fun r => (List.range p.ℓ).all fun c => keepB (vB p) ws (pA p.ℓ r c) 1024)

theorem keepC_spec {p : Params} {ws : List (Ptr × Nat)} {ex : Nat} (h : keepC p ws ex = true) :
    tChk p ws = true ∧ keepB (vB p) ws (pH 0) (1024 * p.k) = true ∧
      (∀ i < p.ℓ, i ≠ ex → keepB (vB p) ws (pZ i) 1024 = true) ∧
      ∀ r < p.k, ∀ c < p.ℓ, keepB (vB p) ws (pA p.ℓ r c) 1024 = true := by
  simp only [keepC, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, fun i hi hne => (h.1.2 i hi).resolve_left hne, h.2⟩

/-- The facts about the parameters the NTTs need. -/
def nttChk (p : Params) : Bool :=
  (List.range p.ℓ).all (fun i => ipChk (vB p) (vW p) (pZ i) && keepC p [(pZ i, 1024), (sc oSS, 1024)] i &&
    keepB (vB p) [(pZ i, 1024), (sc oSS, 1024)] pC 1024) &&
  ipChk (vB p) (vW p) pC && keepC p [(pC, 1024), (sc oSS, 1024)] 100

theorem nttChk_all : ∀ p ∈ params, nttChk p = true := by decide +kernel

theorem nttZ_ok {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ)
    {h : List (Vector Bool n)} {A' : Nat → Nat → Poly} {Q : Prop} [Decidable Q] {cH : Poly}
    {i : Nat} (hi : i < p.ℓ) {s : State} (hs : SC p h A' Q i cH 0 σ s) :
    WP isa (nttAt P (pZ i)) s (SC p h A' Q (i + 1) cH 0 σ) := by
  have hc := nttChk_all p hp
  simp only [nttChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨c1, c2⟩, c3⟩ := hc.1.1 i hi
  obtain ⟨tk, hH, hZ, hA⟩ := keepC_spec c2
  have L := hs.t.lay hp hv
  refine WP.mono (ipAt_ok C.ntt L c1 (by have := hs.z i hi; rw [ifn (Nat.lt_irrefl _)] at this; exact this.1))
    fun s' ⟨hP, h15, hq⟩ => ?_
  refine ⟨hs.t.step hp hv hP tk, L.keepHint hP hH hs.hint, fun r' hr' c hc' => L.keepPoly hP (hA r' hr' c hc')
    (hs.a r' hr' c hc'), fun i' hi' => ?_, L.keepPoly hP c3 hs.c, fun _ h => absurd h (Nat.not_lt_zero _),
    by rw [h15]; exact hs.r15⟩
  rcases (by omega_using [] : i' < i ∨ i' = i ∨ i < i') with hlt | rfl | hgt
  · rw [ifp (by omega_using [hlt] : i' < i + 1)]
    have := L.keepPoly hP (hZ i' hi' (by omega_using [hlt])) (hs.z i' hi')
    rwa [ifp hlt] at this
  · rw [ifp (Nat.lt_succ_self _), hP.pa (show Reg.rbx ∈ bases by decide)]
    have := (hs.z i' hi').2
    rw [ifn (Nat.lt_irrefl _)] at this
    rw [this] at hq
    exact hq
  · rw [ifn (by omega_using [hgt] : ¬ i' < i + 1)]
    have := L.keepPoly hP (hZ i' hi' (by omega_using [hgt])) (hs.z i' hi')
    rwa [ifn (by omega_using [hgt] : ¬ i' < i)] at this

theorem nttC_ok {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ)
    {h : List (Vector Bool n)} {A' : Nat → Nat → Poly} {Q : Prop} [Decidable Q] {cH : Poly}
    {s : State} (hs : SC p h A' Q p.ℓ cH 0 σ s) :
    WP isa (nttAt P pC) s (SC p h A' Q p.ℓ (ntt cH) 0 σ) := by
  have hc := nttChk_all p hp
  simp only [nttChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨_, c1⟩, c2⟩ := hc
  obtain ⟨tk, hH, hZ, hA⟩ := keepC_spec c2
  have L := hs.t.lay hp hv
  refine WP.mono (ipAt_ok C.ntt L c1 hs.c.1) fun s' ⟨hP, h15, hq⟩ => ?_
  refine ⟨hs.t.step hp hv hP tk, L.keepHint hP hH hs.hint, fun r' hr' c hc' => L.keepPoly hP (hA r' hr' c hc')
    (hs.a r' hr' c hc'), fun i hi => L.keepPoly hP (hZ i hi (by have := kl_le p hp; omega_using [hi, this])) (hs.z i hi), ?_,
    fun _ h => absurd h (Nat.not_lt_zero _), by rw [h15]; exact hs.r15⟩
  rw [hP.pa (show Reg.rbx ∈ bases by decide), ← hs.c.2]
  exact hq


/-! ## A row -/

/-- What row `r` writes. -/
abbrev wsR (p : Params) (r : Nat) : List (Ptr × Nat) :=
  [(pW, 1024), (pT, 1024), (sc oSS, 1024), (pT2, 1024), (pW1, 1024), (sc (oB + w1Len p * r), w1Len p)]

/-- The facts about the parameters row `r` needs. -/
def rowChk (p : Params) (r : Nat) : Bool :=
  (List.range p.ℓ).all (fun c => mulChk (vB p) (vW p) pW (pA p.ℓ r c) (pZ c)) &&
    t1Chk (vB p) (vW p) (.rbp, 32 + 320 * r) pT && decide (32 + 320 * r + 320 ≤ p.pkLen) &&
    ipChk (vB p) (vW p) pT && ipChk (vB p) (vW p) pW && mulChk (vB p) (vW p) pT2 pC pT &&
    subChk (vB p) (vW p) pW pT2 && uhChk (vB p) (vW p) (pH r) pW pW1 && decide (p.γ₂ ∈ gamma2s) &&
    sbpChk (vB p) (vW p) pW1 (sc (oB + w1Len p * r)) (w1Len p) && decide (w1Max p ∈ simpleBitPackBounds) &&
    decide (w1Len p = 32 * bitlen (w1Max p)) && keepC p (wsR p r) 100 && keepB (vB p) (wsR p r) pC 1024 &&
    (List.range r).all (fun r' => keepB (vB p) (wsR p r) (sc (oB + w1Len p * r')) (w1Len p)) &&
    keepB (vB p) [(pT, 1024), (sc oSS, 1024), (pT2, 1024)] pW 1024 && decide (1 ≤ p.ℓ) &&
    decide (w1Max p = (q - 1) / (2 * p.γ₂) - 1)

theorem rowChk_all : ∀ p ∈ params, ∀ r < p.k, rowChk p r = true := by decide +kernel

theorem hintRow_pa (s : State) (r : Nat) : pa s (pH r) = pa s (pH 0) + BitVec.ofNat 64 (1024 * r) := by
  simp only [pa, oP]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_zero, Nat.add_zero]

theorem wsR_bases (p : Params) (r : Nat) : ∀ w ∈ wsR p r, w.1.1 ∈ bases := by
  intro w hw
  simp only [wsR, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> exact (show Reg.rbx ∈ bases by decide)

/-- `rowChk`, piece by piece. -/
structure RowC (p : Params) (r : Nat) : Prop where
  mul : ∀ c < p.ℓ, mulChk (vB p) (vW p) pW (pA p.ℓ r c) (pZ c) = true
  t1 : t1Chk (vB p) (vW p) (.rbp, 32 + 320 * r) pT = true
  pk : 32 + 320 * r + 320 ≤ p.pkLen
  ipT : ipChk (vB p) (vW p) pT = true
  ipW : ipChk (vB p) (vW p) pW = true
  mulT : mulChk (vB p) (vW p) pT2 pC pT = true
  sub : subChk (vB p) (vW p) pW pT2 = true
  uh : uhChk (vB p) (vW p) (pH r) pW pW1 = true
  g2 : p.γ₂ ∈ gamma2s
  sbp : sbpChk (vB p) (vW p) pW1 (sc (oB + w1Len p * r)) (w1Len p) = true
  sbpB : w1Max p ∈ simpleBitPackBounds
  len : w1Len p = 32 * bitlen (w1Max p)
  keep : keepC p (wsR p r) 100 = true
  keepC' : keepB (vB p) (wsR p r) pC 1024 = true
  rows : ∀ r' < r, keepB (vB p) (wsR p r) (sc (oB + w1Len p * r')) (w1Len p) = true
  keepW : keepB (vB p) [(pT, 1024), (sc oSS, 1024), (pT2, 1024)] pW 1024 = true
  l1 : 1 ≤ p.ℓ
  max : w1Max p = (q - 1) / (2 * p.γ₂) - 1

theorem rowC {p : Params} (hp : p ∈ params) {r : Nat} (hr : r < p.k) : RowC p r := by
  have hc := rowChk_all p hp r hr
  simp only [rowChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩, c12⟩, c13⟩, c14⟩, c15⟩, c16⟩,
    c17⟩, c18⟩ := hc
  exact ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18⟩

theorem wsR_mem (p : Params) (r : Nat) :
    (pW, 1024) ∈ wsR p r ∧ (pT, 1024) ∈ wsR p r ∧ (sc oSS, 1024) ∈ wsR p r ∧ (pT2, 1024) ∈ wsR p r ∧
      (pW1, 1024) ∈ wsR p r ∧ (sc (oB + w1Len p * r), w1Len p) ∈ wsR p r := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [wsR, List.mem_cons, true_or, or_true]

theorem sub1 {α : Type} {x : α} {l : List α} (h : x ∈ l) : ∀ w ∈ [x], w ∈ l := fun _ hw => by
  rw [List.mem_singleton.mp hw]; exact h

theorem sub2 {α : Type} {x y : α} {l : List α} (h : x ∈ l) (h' : y ∈ l) : ∀ w ∈ [x, y], w ∈ l := fun _ hw => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  exacts [h, h']

theorem PPostB.accR {p : Params} {r : Nat} {s s₁ s₂ : State} {ws : List (Ptr × Nat)} (h₁ : PPostB s s₁ (wsR p r))
    (h₂ : PPostB s₁ s₂ ws) (hw : ∀ w ∈ ws, w ∈ wsR p r) : PPostB s s₂ (wsR p r) :=
  h₁.trans h₂ (fun w hw' => wsR_bases p r w (hw w hw')) (fun _ h => h) hw

theorem pa_rbx {s s' : State} {W : List Region} (hP : PostB s s' W) (o : Nat) : pa s' (.rbx, o) = pa s (.rbx, o) :=
  hP.pa (show Reg.rbx ∈ bases by decide)

/-- After `Σ_{s < j} Â[r, s] ẑ[s]`, from `s₀`. -/
def DI (mont : Bool) (p : Params) (σ : State) (A' : Nat → Nat → Poly) (r j : Nat) (s₀ st : State) : Prop :=
  PPostB s₀ st [(pW, 1024)] ∧ st.gpr .r15 = s₀.gpr .r15 ∧ PolyIs st.mem (pa s₀ pW) (encode mont (dotAcc p (vSig p σ) A' r j))

theorem SC.zHat {p : Params} {h : List (Vector Bool n)} {A' : Nat → Nat → Poly} {Q : Prop} [Decidable Q]
    {cH : Poly} {r : Nat} {σ s : State} (hs : SC p h A' Q p.ℓ cH r σ s) {c : Nat} (hc : c < p.ℓ) :
    PolyIs s.mem (pa s (pZ c)) (zHat p (vSig p σ) c) := by
  have := hs.z c hc; rwa [ifp hc] at this

section Dot
variable {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ)
  {h : List (Vector Bool n)} {A' : Nat → Nat → Poly} {Q : Prop} [Decidable Q] {cH : Poly}
  {r : Nat} (hr : r < p.k) {s₀ : State} (hs : SC p h A' Q p.ℓ cH r σ s₀)
include C hp hv hr hs

theorem dotFirst_ok : WP isa (mulAt P pW (pA p.ℓ r 0) (pZ 0)) s₀ (DI P.montgomery p σ A' r 1 s₀) := by
  have R := rowC hp hr
  refine WP.mono (mulAt_ok C.mul (hs.t.lay hp hv) (R.mul 0 R.l1) (hs.a r hr 0 R.l1).1 (hs.zHat R.l1).1)
    fun s₁ ⟨hP₁, e₁, hq₁⟩ => ⟨hP₁, e₁, ?_⟩
  rw [(hs.a r hr 0 R.l1).2, (hs.zHat R.l1).2] at hq₁
  simp only [dotAcc, add_zero_left]
  exact hq₁

theorem dotStep_ok {k : Nat} (hk' : k < p.ℓ) {st : State} (hd : DI P.montgomery p σ A' r k s₀ st) :
    WP isa (mulAddAt P pW (pA p.ℓ r k) (pZ k)) st (DI P.montgomery p σ A' r (k + 1) s₀) := by
  have R := rowC hp hr
  have L := hs.t.lay hp hv
  obtain ⟨_, _, hZ, hA⟩ := keepC_spec R.keep
  obtain ⟨hP, e, hW⟩ := hd
  have H := hP.mono (sub1 (wsR_mem p r).1)
  have ew : pa st pW = pa s₀ pW := pa_rbx hP _
  have hz : k ≠ 100 := by have := kl_le p hp; omega_using [hk', this]
  refine WP.mono (mulAddAt_ok C.mulAdd (L.post hP) (R.mul k hk') (by rw [ew]; exact hW.1)
    (L.keepRed H (hA r hr k hk') (hs.a r hr k hk').1) (L.keepRed H (hZ k hk' hz) (hs.zHat hk').1))
    fun s' ⟨hP', e', hq'⟩ => ?_
  rw [ew, hW.2, L.keepPolyAt H (hA r hr k hk'), (hs.a r hr k hk').2, L.keepPolyAt H (hZ k hk' hz),
    (hs.zHat hk').2, product, ← encode_add] at hq'
  exact ⟨hP.trans hP' (fun w hw => by rw [List.mem_singleton.mp hw]; decide) (fun _ h => h) (fun _ h => h),
    e'.trans e, hq'⟩

theorem dot_ok : WP isa (dot P p r) s₀ (DI P.montgomery p σ A' r p.ℓ s₀) := by
  have R := rowC hp hr
  unfold dot
  refine WP.seq (WP.mono (dotFirst_ok C hp hv hr hs) fun s₁ h₁ => ?_)
  have := seqR_ok (I := fun j => DI P.montgomery p σ A' r j s₀) (p.ℓ - 1) 1
    (fun k _ hk' st hd => dotStep_ok C hp hv hr hs (by omega_arith) hd) s₁ h₁
  rwa [show 1 + (p.ℓ - 1) = p.ℓ by have := R.l1; omega_using [this]] at this

end Dot

theorem keepB_sub {bs : List (Reg × Nat)} {ws ws' : List (Ptr × Nat)} {q : Ptr} {l : Nat} (h : keepB bs ws q l = true)
    (hw : ∀ w ∈ ws', w ∈ ws) : keepB bs ws' q l = true := by
  simp only [keepB, Bool.and_eq_true, List.all_eq_true] at h ⊢
  exact ⟨h.1, fun w hw' => h.2 w (hw w hw')⟩

section Row
variable {p : Params} {σ : State} {h : List (Vector Bool n)} {A' : Nat → Nat → Poly} {cH : Poly} {r : Nat}

/-- `Σₛ Â[r, s] ẑ[s]`. -/
abbrev rDot (p : Params) (σ : State) (A' : Nat → Nat → Poly) (r : Nat) : Poly := dotAcc p (vSig p σ) A' r p.ℓ
/-- `t₁[r] · 2ᵈ`. -/
abbrev rU (p : Params) (σ : State) (r : Nat) : Poly := (vT1 (vPk p σ) r).map fun c => ofInt (c * 2 ^ d : Nat)
/-- `ĉ t̂₁[r]`. -/
abbrev rCT (p : Params) (σ : State) (cH : Poly) (r : Nat) : Poly := multiplyNTT cH (t1Hat (vPk p σ) r)

/-- Row `r` from `s₀`, what every step keeps: the writes and `r15`. -/
abbrev RB (p : Params) (r : Nat) (s₀ s : State) : Prop := PPostB s₀ s (wsR p r) ∧ s.gpr .r15 = s₀.gpr .r15

/-- After `Σₛ Â[r, s] ẑ[s]`, and `t₁[r] · 2ᵈ`, its NTT, and `ĉ t̂₁[r]`. -/
def RF1 (mont : Bool) (p : Params) (σ : State) (A' : Nat → Nat → Poly) (r : Nat) (s₀ s : State) : Prop :=
  RB p r s₀ s ∧ PolyIs s.mem (pa s pW) (encode mont (rDot p σ A' r))
def RF2 (mont : Bool) (p : Params) (σ : State) (A' : Nat → Nat → Poly) (r : Nat) (s₀ s : State) : Prop :=
  RF1 mont p σ A' r s₀ s ∧ PolyIs s.mem (pa s pT) (rU p σ r)
def RF3 (mont : Bool) (p : Params) (σ : State) (A' : Nat → Nat → Poly) (r : Nat) (s₀ s : State) : Prop :=
  RF1 mont p σ A' r s₀ s ∧ PolyIs s.mem (pa s pT) (ntt (rU p σ r))
def RF4 (mont : Bool) (p : Params) (σ : State) (A' : Nat → Nat → Poly) (cH : Poly) (r : Nat) (s₀ s : State) : Prop :=
  RF1 mont p σ A' r s₀ s ∧ PolyIs s.mem (pa s pT2) (encode mont (rCT p σ cH r))
/-- After `w′ = NTT⁻¹(…)` less `ĉ t̂₁[r]`, `w′`, and `w′₁`. -/
def RF5 (mont : Bool) (p : Params) (σ : State) (A' : Nat → Nat → Poly) (cH : Poly) (r : Nat) (s₀ s : State) : Prop :=
  RB p r s₀ s ∧ PolyIs s.mem (pa s pW) (encode mont (sub (rDot p σ A' r) (rCT p σ cH r)))
def RF6 (p : Params) (σ : State) (A' : Nat → Nat → Poly) (cH : Poly) (r : Nat) (s₀ s : State) : Prop :=
  RB p r s₀ s ∧ PolyIs s.mem (pa s pW) (wRow p (vPk p σ) (vSig p σ) A' cH r)
def RF7 (p : Params) (σ : State) (h : List (Vector Bool n)) (A' : Nat → Nat → Poly) (cH : Poly) (r : Nat)
    (s₀ s : State) : Prop :=
  RB p r s₀ s ∧ NatPolyIs s.mem (pa s pW1) (w1Row p (vPk p σ) (vSig p σ) A' cH h r)

theorem RB.acc {s₀ s s' : State} (hb : RB p r s₀ s) {ws : List (Ptr × Nat)} (hP : PPostB s s' ws)
    (e : s'.gpr .r15 = s.gpr .r15) (hw : ∀ w ∈ ws, w ∈ wsR p r) : RB p r s₀ s' :=
  ⟨hb.1.accR hP hw, e.trans hb.2⟩

variable {P : Prims} (C : PrimsOk P) (hp : p ∈ params) (hv : VPre p σ) {Q : Prop} [Decidable Q] (hr : r < p.k)
  {s₀ : State} (hs : SC p h A' Q p.ℓ cH r σ s₀)
include C hp hv hr hs

omit C hp hv hr hs in
theorem DI.rf1 {s : State} (hd : DI P.montgomery p σ A' r p.ℓ s₀ s) : RF1 P.montgomery p σ A' r s₀ s :=
  let ⟨hP, e, hq⟩ := hd
  ⟨⟨hP.mono (sub1 (wsR_mem p r).1), e⟩, by rw [pa_rbx hP]; exact hq⟩

theorem row0_ok : WP isa (dot P p r) s₀ (RF1 P.montgomery p σ A' r s₀) :=
  WP.mono (dot_ok C hp hv hr hs) fun _ hd => DI.rf1 hd

theorem row1_ok {s : State} (hf : RF1 P.montgomery p σ A' r s₀ s) :
    WP isa (unpackT1At P (.rbp, 32 + 320 * r) pT) s (RF2 P.montgomery p σ A' r s₀) := by
  have R := rowC hp hr
  have L := (hs.t.lay hp hv).post hf.1.1
  refine WP.mono (unpackT1At_ok C.unpackT1 L R.t1) fun s' ⟨hP, e, hq⟩ => ⟨⟨hf.1.acc hP e (sub1 (wsR_mem p r).2.1),
    L.keepPoly hP (keepB_sub R.keepW (sub1 (List.mem_cons_self ..))) hf.2⟩, ?_⟩
  rw [(hs.t.step hp hv hf.1.1 (keepC_spec R.keep).1).pkSlice R.pk] at hq
  rw [pa_rbx hP]
  exact hq

theorem row2_ok {s : State} (hf : RF2 P.montgomery p σ A' r s₀ s) : WP isa (nttAt P pT) s (RF3 P.montgomery p σ A' r s₀) := by
  have R := rowC hp hr
  have L := (hs.t.lay hp hv).post hf.1.1.1
  refine WP.mono (ipAt_ok C.ntt L R.ipT hf.2.1) fun s' ⟨hP, e, hq⟩ => ⟨⟨hf.1.1.acc hP e
    (sub2 (wsR_mem p r).2.1 (wsR_mem p r).2.2.1), L.keepPoly hP (keepB_sub R.keepW (sub2 (List.mem_cons_self ..)
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) hf.1.2⟩, ?_⟩
  rw [pa_rbx hP, ← hf.2.2]
  exact hq

theorem row3_ok {s : State} (hf : RF3 P.montgomery p σ A' r s₀ s) : WP isa (mulAt P pT2 pC pT) s (RF4 P.montgomery p σ A' cH r s₀) := by
  have R := rowC hp hr
  have L₀ := hs.t.lay hp hv
  have L := L₀.post hf.1.1.1
  have hC := L₀.keepPoly hf.1.1.1 R.keepC' hs.c
  refine WP.mono (mulAt_ok C.mul L R.mulT hC.1 hf.2.1) fun s' ⟨hP, e, hq⟩ => ⟨⟨hf.1.1.acc hP e
    (sub1 (wsR_mem p r).2.2.2.1), L.keepPoly hP (keepB_sub R.keepW (sub1 (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))))) hf.1.2⟩, ?_⟩
  rw [pa_rbx hP, hC.2, hf.2.2] at *
  exact hq

theorem row4_ok {s : State} (hf : RF4 P.montgomery p σ A' cH r s₀ s) : WP isa (subAt P pW pT2) s (RF5 P.montgomery p σ A' cH r s₀) := by
  have R := rowC hp hr
  have L := (hs.t.lay hp hv).post hf.1.1.1
  refine WP.mono (subAt_ok C.sub L R.sub hf.1.2.1 hf.2.1) fun s' ⟨hP, e, hq⟩ => ⟨hf.1.1.acc hP e
    (sub1 (wsR_mem p r).1), ?_⟩
  rw [pa_rbx hP, hf.1.2.2, hf.2.2] at *
  rw [← encode_sub] at hq
  exact hq

theorem row5_ok {s : State} (hf : RF5 P.montgomery p σ A' cH r s₀ s) : WP isa (invNttAt P pW) s (RF6 p σ A' cH r s₀) := by
  have R := rowC hp hr
  have L := (hs.t.lay hp hv).post hf.1.1
  refine WP.mono (ipAt_ok C.invNtt L R.ipW hf.2.1) fun s' ⟨hP, e, hq⟩ => ⟨hf.1.acc hP e
    (sub2 (wsR_mem p r).1 (wsR_mem p r).2.2.1), ?_⟩
  rw [pa_rbx hP, hf.2.2] at *
  rw [inverse_encode] at hq
  exact hq

theorem row6_ok {s : State} (hf : RF6 p σ A' cH r s₀ s) : WP isa (useHintAt P (pH r) pW p.γ₂ pW1) s (RF7 p σ h A' cH r s₀) := by
  have R := rowC hp hr
  have L₀ := hs.t.lay hp hv
  have L := L₀.post hf.1.1
  have hh := L₀.keepHint hf.1.1 (keepC_spec R.keep).2.1 hs.hint
  refine WP.mono (useHintAt_ok C.useHint L R.g2 R.uh hf.2.1) fun s' ⟨hP, e, hq⟩ => ⟨hf.1.acc hP e
    (sub1 (wsR_mem p r).2.2.2.2.1), ?_⟩
  have hq' : natPolyAt s'.mem (pa s pW1) = _ := hq
  rw [hintRow_pa s r, hintAt_row hh hr, hf.2.2] at hq'
  show natPolyAt s'.mem (pa s' pW1) = _
  rw [pa_rbx hP]
  exact hq'

theorem row7_ok {s : State} (hf : RF7 p σ h A' cH r s₀ s) :
    WP isa (sbpAt P pW1 (w1Max p) (sc (oB + w1Len p * r)) (w1Len p)) s (SC p h A' Q p.ℓ cH (r + 1) σ) := by
  have R := rowC hp hr
  have L₀ := hs.t.lay hp hv
  have L := L₀.post hf.1.1
  obtain ⟨tk, hH, hZ, hA⟩ := keepC_spec R.keep
  have hq₇ : natPolyAt s.mem (pa s pW1) = _ := hf.2
  have hb : ∀ i < n, (coeffAt s.mem (pa s pW1) i).toNat ≤ w1Max p := fun i hi => by
    have := congrArg (·[i]'hi) hq₇
    simp only [natPolyAt, Vector.getElem_ofFn, w1Row, Vector.getElem_zipWith] at this
    rw [this, R.max]
    exact useHint_le R.g2 _ _
  refine WP.mono (sbpAt_ok C.simpleBitPack L R.sbpB R.len R.sbp hb) fun s' ⟨hP, e, hq⟩ => ?_
  rw [hq₇] at hq
  have H := hf.1.1.accR hP (sub1 (wsR_mem p r).2.2.2.2.2)
  refine ⟨hs.t.step hp hv H tk, L₀.keepHint H hH hs.hint,
    fun r' hr' c hc => L₀.keepPoly H (hA r' hr' c hc) (hs.a r' hr' c hc),
    fun i hi => L₀.keepPoly H (hZ i hi (by have := kl_le p hp; omega_using [hi, this])) (hs.z i hi), L₀.keepPoly H R.keepC' hs.c,
    fun r' hr' => ?_, by rw [e, hf.1.2]; exact hs.r15⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hr' with hlt | rfl
  · rw [L₀.keepBytes H (R.rows r' hlt)]; exact hs.rows r' hlt
  · rw [pa_rbx hP]
    exact hq

omit C hp hv hr hs in
/-- The flag at `FL` is the entry's `r8`. -/
theorem testFlag_ok {s : State} (ht : T p σ s) (hin : InRegions (s.rd ++ s.wr) (pa s (sc oFL)) 8) :
    WP isa (.block testFlag) s fun s' => PPostB s s' [] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      s'.mem = s.mem ∧ s'.zf = some (σ.gpr .r8 == 0) := by
  have e := ht.flag
  simp only [pa] at hin e
  unfold testFlag
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax] (Q := fun s' => s'.mem = s.mem ∧
      s'.zf = some (s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 oFL) 64 &&&
        s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 oFL) 64 == 0)) (by xrun [hin]) (by decide))
    fun s' ⟨⟨hm, hz⟩, k⟩ => ⟨postB_of_keep k (by decide) (by rw [hm]; exact Frame.refl _ _), k.gpr (by decide),
      hm, by rw [hz, e, BitVec.and_self]⟩

omit C hp hv [Decidable Q] hr hs in
/-- What copying `t̂₁[r]` from a prepared key needs of the layout. -/
theorem keyRow_chk : ∀ p ∈ params, inB (vW p) pT 1024 = true ∧ inB (vB p) (sc oFL) 8 = true ∧
    (∀ r < p.k, p.pkLen + 1024 * r + 1024 ≤ preparedPublicKeyBytes p) ∧ inB (vB p) pT 1024 = true ∧
    preparedPublicKeyBytes p < 2 ^ 31 := by decide

omit C in
theorem keyFlag_ok {s : State} (hf : RF1 P.montgomery p σ A' r s₀ s) :
    WP isa (.block testFlag) s fun s1 => RF1 P.montgomery p σ A' r s₀ s1 ∧ s1.zf = some (σ.gpr .r8 == 0) := by
  have R := rowC hp hr
  obtain ⟨_, cF, _⟩ := keyRow_chk p hp
  have t := hs.t.step hp hv hf.1.1 (keepC_spec R.keep).1
  refine WP.mono (testFlag_ok t ((t.lay hp hv).inR cF)) fun s1 ⟨hP1, e1, hm1, hz⟩ =>
    ⟨⟨hf.1.acc hP1 e1 (fun _ h => absurd h (List.not_mem_nil)), by rw [pa_rbx hP1, hm1]; exact hf.2⟩, hz⟩

omit C in
theorem keyCopy_ok {s1 : State} (hf1 : RF1 P.montgomery p σ A' r s₀ s1) (hb' : σ.gpr .r8 ≠ 0) :
    WP isa (Impl.MlDsa.X86_64.Sign.copy pT (.rbp, p.pkLen + 1024 * r) 1024) s1 (RF3 P.montgomery p σ A' r s₀) := by
  have R := rowC hp hr
  obtain ⟨cW, _, cK, cW', cP⟩ := keyRow_chk p hp
  have t1 := hs.t.step hp hv hf1.1.1 (keepC_spec R.keep).1
  have L1 := t1.lay hp hv
  have hL : pkL p σ = preparedPublicKeyBytes p := by simp only [pkL, hb', ite_false]
  have d1 := hv.d1; have k1 := hv.k1; have n1 := hv.n1
  rw [hL] at d1 k1 n1
  have hk := cK r hr
  have hprep : preparedPublicKeyBytes p < 2 ^ 64 := by omega_using [cP]
  -- The source, in the prepared key.
  have es : Sign.pa s1 (.rbp, p.pkLen + 1024 * r) = σ.gpr .rdi + BitVec.ofNat 64 (p.pkLen + 1024 * r) := by
    simp only [Sign.pa, t1.rbp]
  have hsub : Region.Sub ⟨σ.gpr .rdi + BitVec.ofNat 64 (p.pkLen + 1024 * r), 1024⟩
      ⟨σ.gpr .rdi, preparedPublicKeyBytes p⟩ := Offset.sub_base _ hk
  obtain ⟨nW, hnW, hsW⟩ := L1.sub (p := pT) (l := 1024) cW'
  have hnW' : nW = scrLen p := by
    simp only [vR, vW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq, reduceCtorEq, false_and, false_or] at hnW
    exact hnW.2
  subst hnW'
  have hsW' : Region.Sub ⟨pa s1 pT, 1024⟩ ⟨σ.gpr .rcx, scrLen p⟩ := by rw [← t1.rbx]; exact hsW
  have hrd : InRegions (s1.rd ++ s1.wr) (Sign.pa s1 (.rbp, p.pkLen + 1024 * r)) 1024 :=
    ⟨⟨σ.gpr .rdi, preparedPublicKeyBytes p⟩, by rw [t1.rd, t1.wr, hv.rd, hL]; simp,
      by rw [es]; exact Sign.contains_offset' hk hprep⟩
  have hwr : InRegions s1.wr (Sign.pa s1 pT) 1024 := L1.inW cW
  have hdj : Region.Disjoint ⟨Sign.pa s1 (.rbp, p.pkLen + 1024 * r), 1024⟩ ⟨Sign.pa s1 pT, 1024⟩ := by
    rw [es]; exact (d1.sub_left hsub).sub_right hsW'
  refine WP.mono (Sign.copy_ok pT (.rbp, p.pkLen + 1024 * r) 1024 (by decide) (by decide) (by decide)
    (by show p.pkLen + 1024 * r < 2 ^ 31; omega_using [cP, hk]) (by simp) s1 hrd hwr hdj) fun s' ⟨hb2, hfr, k⟩ => ?_
  have hP : PPostB s1 s' [(pT, 1024)] := postB_of_keep k (by decide) (by simpa using hfr)
  refine ⟨⟨hf1.1.acc hP (k.gpr (by decide)) (sub1 (wsR_mem p r).2.1),
    L1.keepPoly hP (keepB_sub R.keepW (sub1 (List.mem_cons_self ..))) hf1.2⟩, ?_⟩
  -- `t̂₁[r]`, unchanged since entry, copied.
  have hσ : bytesAt s1.mem (σ.gpr .rdi + BitVec.ofNat 64 (p.pkLen + 1024 * r)) 1024 =
      bytesAt σ.mem (σ.gpr .rdi + BitVec.ofNat 64 (p.pkLen + 1024 * r)) 1024 := by
    refine Proof.MlKem.bytesAt_frame t1.fr (fun R' hR' => ?_) (by decide)
    rw [hv.wr] at hR'
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hR'
    rcases hR' with rfl | rfl
    exacts [d1.sub_left hsub, (k1.sub_right hsub).symm]
  have hpoly : PolyIs σ.mem (σ.gpr .rdi + BitVec.ofNat 64 (p.pkLen + 1024 * r))
      (preparedPublicPolys p (vPk p σ))[r]! := (polyStored_iff).mp (hv.prep hb' r hr)
  rw [PreparedKey.public_poly p _ hr] at hpoly
  rw [pa_rbx hP]
  refine PreparedKey.polyIs_of_copy ?_ hpoly
  have hb3 : bytesAt s'.mem (pa s1 pT) 1024 = _ := hb2
  rw [hb3, es, hσ]

theorem keyRow_ok {s : State} (hf : RF1 P.montgomery p σ A' r s₀ s) :
    WP isa (keyRow P p r) s (RF3 P.montgomery p σ A' r s₀) := by
  unfold keyRow
  refine WP.seq (WP.mono (keyFlag_ok hp hv hr hs hf) fun s1 ⟨hf1, hz⟩ => ?_)
  refine WP.ite (M := isa) (!(σ.gpr .r8 == 0)) (show s1.zf.map (!·) = _ by rw [hz]; rfl)
    (fun hb => keyCopy_ok hp hv hr hs hf1 (by simpa using hb))
    fun _ => WP.seq (WP.mono (row1_ok C hp hv hr hs hf1) fun _ h2 => row2_ok C hp hv hr hs h2)

theorem row_ok : WP isa (row P p r) s₀ (SC p h A' Q p.ℓ cH (r + 1) σ) := by
  unfold row
  exact WP.seq (WP.mono (row0_ok C hp hv hr hs) fun _ h1 =>
    WP.seq (WP.mono (keyRow_ok C hp hv hr hs h1) fun _ h3 =>
    WP.seq (WP.mono (row3_ok C hp hv hr hs h3) fun _ h4 =>
    WP.seq (WP.mono (row4_ok C hp hv hr hs h4) fun _ h5 =>
    WP.seq (WP.mono (row5_ok C hp hv hr hs h5) fun _ h6 =>
    WP.seq (WP.mono (row6_ok C hp hv hr hs h6) fun _ h7 => row7_ok C hp hv hr hs h7))))))

end Row

/-! ## The rows, the hash and the comparison -/

theorem bytesAt_rows {m : Mem} {a : Addr} {L : Nat} {f : Nat → List Byte} :
    ∀ k, (∀ r < k, bytesAt m (a + BitVec.ofNat 64 (L * r)) L = f r) → bytesAt m a (k * L) = (List.range k).flatMap f
  | 0, _ => by rw [Nat.zero_mul]; rfl
  | k + 1, h => by
    rw [Nat.succ_mul, Proof.MlKem.bytesAt_add, bytesAt_rows k (fun r hr => h r (by omega_using [hr])), Nat.mul_comm k L,
      h k (by omega_using []), List.range_succ, List.flatMap_append, List.flatMap_singleton]

theorem row_pa (s : State) (L r : Nat) : pa s (sc (oB + L * r)) = pa s (sc oB) + BitVec.ofNat 64 (L * r) := by
  simp only [pa]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The facts about the parameters the hash and the comparison need. -/
def compChk (p : Params) : Bool :=
  hashChk (vB p) (vW p) (.r12, 0) 64 (sc oB) (p.k * w1Len p) (sc oCT) p.ctildeLen &&
    tChk p [(sc 0, 200), (sc 200, 640), (sc oCT, p.ctildeLen)] && inB (vB p) (sc oCT) p.ctildeLen &&
    inB (vB p) (.r13, 0) p.ctildeLen && decide (0 < p.ctildeLen) && decide (p.ctildeLen ≤ p.sigLen)

theorem compChk_all : ∀ p ∈ params, compChk p = true := by decide +kernel

/-- `w′₁` of the signature, encoded. -/
abbrev w1Enc (p : Params) (σ : State) (h : List (Vector Bool n)) (A' : Nat → Nat → Poly) (cH : Poly) :
    List Byte :=
  (List.range p.k).flatMap fun r => simpleBitPack (w1Row p (vPk p σ) (vSig p σ) A' cH h r) (w1Max p)

theorem tail_ok {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ)
    {h : List (Vector Bool n)} {A' : Nat → Nat → Poly} {Q : Prop} [Decidable Q] {cH : Poly}
    {s₃ : State} (hs₃ : SC p h A' Q p.ℓ cH p.k σ s₃) :
    WP isa (.seq (hash2 (.r12, 0) 64 (sc oB) (p.k * w1Len p) (sc oCT) p.ctildeLen)
      (cmpAnd (sc oCT) (.r13, 0) p.ctildeLen)) s₃ fun s' => T p σ s' ∧
      s'.gpr .r15 = flag (Q ∧ H (vMu σ ++ w1Enc p σ h A' cH) p.ctildeLen = vCt p (vSig p σ)) := by
  have hc := compChk_all p hp
  simp only [compChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩ := hc
  have L₃ := hs₃.t.lay hp hv
  have hB : bytesAt s₃.mem (pa s₃ (sc oB)) (p.k * w1Len p) = w1Enc p σ h A' cH :=
    bytesAt_rows p.k fun r hr => by rw [← row_pa]; exact hs₃.rows r hr
  refine WP.seq (WP.mono (hash2_ok L₃ c1) fun s₄ ⟨hP₄, f₄, hq₄⟩ => ?_)
  rw [hB, hs₃.t.mu] at hq₄
  have t₄ := hs₃.t.step hp hv hP₄ c2
  have L₄ := t₄.lay hp hv
  refine WP.mono (cmpAnd_ok L₄ c5 c3 c4 (P := Q) (by rw [f₄]; exact hs₃.r15)) fun s₅ ⟨hP₅, f₅⟩ => ⟨t₄.step hp hv hP₅
    (tChk_nil p hp), ?_⟩
  rw [f₅, show pa s₄ (sc oCT) = pa s₃ (sc oCT) from pa_rbx hP₄ _, hq₄,
    t₄.sigSlice (by omega_using [c6] : 0 + p.ctildeLen ≤ p.sigLen), List.drop_zero]
  exact flag_congr (and_congr_right fun _ => Iff.rfl)

theorem compute_ok {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) {σ : State} (hv : VPre p σ)
    {h : List (Vector Bool n)} {A' : Nat → Nat → Poly} {Q : Prop} [Decidable Q] {cH : Poly}
    {s : State} (hs : SC p h A' Q 0 cH 0 σ s) :
    WP isa (compute P p) s fun s' => T p σ s' ∧
      s'.gpr .r15 = flag (Q ∧ H (vMu σ ++ w1Enc p σ h A' (ntt cH)) p.ctildeLen = vCt p (vSig p σ)) := by
  unfold compute
  refine WP.seq (WP.mono (seqR_ok (I := fun i => SC p h A' Q i cH 0 σ) p.ℓ 0
    (fun i _ hi st hst => nttZ_ok C hp hv (by omega_using [hi]) hst) s hs) fun s₁ hs₁ => ?_)
  rw [Nat.zero_add] at hs₁
  refine WP.seq (WP.mono (nttC_ok C hp hv hs₁) fun s₂ hs₂ => ?_)
  refine WP.seq (WP.mono (seqR_ok (I := fun r => SC p h A' Q p.ℓ (ntt cH) r σ) p.k 0
    (fun r _ hr st hst => row_ok C hp hv (by omega_using [hr]) hst) s₂ hs₂) fun s₃ hs₃ => ?_)
  rw [Nat.zero_add] at hs₃
  exact tail_ok hp hv hs₃

end VG.Proof.MlDsa.X86_64.Verify

module

import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PrimsD
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Hash
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseA
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PrimsC
import VerifiedGarbage.Proof.MlKem.X86_64.SampleLoop
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Blocks
import VerifiedGarbage.Proof.MlDsa.PreparedKeyContract
import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values

/-!
# ML-DSA signing on x86-64: the private key and `ρ″`

Once `Â` is sampled (`IM`), `ŝ₁[r]`, `ŝ₂[i]` and `t̂₀[i]`, each the `NTT` of
the `BitUnpack` of its piece of `sk` (`dec_ok`), in their slots (`ID`), and
`ρ″ = H(K ‖ rnd ‖ μ, 64)` at `MS` (`decode_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params)

/-- The slots of `ŝ₁`, `ŝ₂` and `t̂₀`. -/
abbrev s1Base : Nat := 5 + 2 * p.k + 2 * p.ℓ
abbrev s2Base : Nat := 5 + 2 * p.k + 3 * p.ℓ
abbrev t0Base : Nat := 5 + 3 * p.k + 3 * p.ℓ

/-- `ŝ₁[r]`, `ŝ₂[i]` and `t̂₀[i]` of the function entered in `σ`. -/
abbrev S1v (σ : State) (r : Nat) : Poly := s1F p (skOf p σ) r
abbrev S2v (σ : State) (i : Nat) : Poly := s2F p (skOf p σ) i
abbrev T0v (σ : State) (i : Nat) : Poly := t0F p (skOf p σ) i

/-- `ρ″ = H(K ‖ rnd ‖ μ, 64)`. -/
abbrev rppOf (σ : State) : List Byte := H (((skOf p σ).drop 32).take 32 ++ rndOf σ ++ muOf σ) 64

end

/-! ## `Â` -/

/-- `Â` sampled within `maxBounds`, in its slots. -/
structure IM (p : Params) (D : Nat) (σ s : State) : Prop where
  st : St p D σ s
  ok : ∀ e < p.k * p.ℓ, (rejNTTPoly maxBounds.rejNTT (seedE p σ e)).isSome
  A : Fam s (aBase p) (p.k * p.ℓ) (aVal p σ)

def imChk (p : Params) (ws : List (Ptr × Nat)) : Bool := stChk p ws && famChk (sgB p) ws (aBase p) (p.k * p.ℓ)

theorem IM.step {p : Params} {D : Nat} {σ s s' : State} (h : IM p D σ s) {ws : List (Ptr × Nat)}
    (hP : PPostB D s s' ws) (hc : imChk p ws = true) : IM p D σ s' := by
  simp only [imChk, Bool.and_eq_true] at hc
  exact ⟨h.st.step hP hc.1, h.ok, Fam.keep h.st.lay hP hc.2 h.A⟩

/-! ## The private key -/

/-- `Â`, the first `a` polynomials of `ŝ₁`, `b` of `ŝ₂` and `c` of `t̂₀`. -/
structure ID (p : Params) (D : Nat) (σ : State) (a b c : Nat) (s : State) : Prop where
  im : IM p D σ s
  s1 : Fam s (s1Base p) a (S1v p σ)
  s2 : Fam s (s2Base p) b (S2v p σ)
  t0 : Fam s (t0Base p) c (T0v p σ)

def idChk (p : Params) (ws : List (Ptr × Nat)) (a b c : Nat) : Bool :=
  imChk p ws && famChk (sgB p) ws (s1Base p) a && famChk (sgB p) ws (s2Base p) b && famChk (sgB p) ws (t0Base p) c

theorem ID.step {p : Params} {D : Nat} {σ s s' : State} {a b c : Nat} (h : ID p D σ a b c s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) (hc : idChk p ws a b c = true) : ID p D σ a b c s' := by
  simp only [idChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  have L := h.im.st.lay
  exact ⟨h.im.step hP h1, Fam.keep L hP h2 h.s1, Fam.keep L hP h3 h.s2, Fam.keep L hP h4 h.t0⟩

theorem pS_bases (j : Nat) : (pS j).1 ∈ bases := List.mem_cons_self ..

theorem sc_bases (o : Nat) : (sc o).1 ∈ bases := List.mem_cons_self ..

theorem pa_add (s : State) (r : Reg) (a b : Nat) : pa s (r, a) + BitVec.ofNat 64 b = pa s (r, a + b) :=
  VG.Proof.MlKem.X86_64.off_add _ _ _

theorem sk_slice {p : Params} {D : Nat} {σ s : State} (h : St p D σ s) {o len : Nat} (hk : o + len ≤ p.skLen) :
    bytesAt s.mem (pa s (.rbp, o)) len = ((skOf p σ).drop o).take len := by
  rw [← h.sk, VG.Proof.MlKem.bytesAt_slice _ _ hk, pa_add, Nat.zero_add]

/-- What decoding a polynomial of `len` bytes at `src` to slot `j` needs of the layout. -/
def decChk (p : Params) (a b c : Nat) (src : Ptr) (len j : Nat) : Bool :=
  rwChk (sgB p) (sgW p) src len (pS j) 1024 && ipChk (sgB p) (sgW p) (pS j) &&
    idChk p [(pS j, 1024)] a b c && idChk p [(pS j, 1024), (sc oPS, 1024)] a b c

theorem dec_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {a b c : Nat} {src : Ptr}
    {len x y j : Nat} (hp : (x, y) ∈ bitPackParams) (hl : len = 32 * bitlen (x + y))
    (hc : decChk p a b c src len j = true) {s : State} (h : ID p D σ a b c s) :
    WP isa (.seq (bitUnpackAt P src len x y (pS j)) (nttAt P (pS j))) s fun s' =>
      ID p D σ a b c s' ∧ Pl s' j (ntt (toRq (bitUnpack (bytesAt s.mem (pa s src) len) x y))) := by
  simp only [decChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
  refine WP.seq (WP.mono (bupAt_ok hP h.im.st.lay hp hl h1) fun s1 ⟨hP1, _, hq1⟩ => ?_)
  have I1 := h.step hP1 h3
  refine WP.mono (ipAt_ok (t := ntt) hP.ntt I1.im.st.lay h2 (by rw [hP1.pa (pS_bases j)]; exact hq1.1))
    fun s2 ⟨hP2, _, hq2⟩ => ⟨I1.step hP2 h4, ?_⟩
  show PolyIs s2.mem (pa s2 (pS j)) _
  rw [hP2.pa (pS_bases j), hP1.pa (pS_bases j), ← hq1.2]
  rw [hP1.pa (pS_bases j)] at hq2
  exact hq2

/-- What `decode` needs of the layout. -/
def dChk (p : Params) : Bool :=
  (List.range p.ℓ).all (fun r => decChk p r 0 0 (.rbp, skS1 p r) (sLen p) (s1Base p + r) &&
      decide (skS1 p r + sLen p ≤ p.skLen)) &&
    (List.range p.k).all (fun i => decChk p p.ℓ i 0 (.rbp, skS2 p i) (sLen p) (s2Base p + i) &&
      decide (skS2 p i + sLen p ≤ p.skLen)) &&
    (List.range p.k).all (fun i => decChk p p.ℓ p.k i (.rbp, skT0 p i) 416 (t0Base p + i) &&
      decide (skT0 p i + 416 ≤ p.skLen)) &&
    shakeChk (sgB p) (sgW p) [((.rbp, 32), 32), ((.r13, 0), 32), ((.r12, 0), 64)] (sc oMS) 64 &&
    idChk p [(sc 0, 200), (sc 200, 640), (sc oMS, 64)] p.ℓ p.k p.k && inB (sgB p) (sc oMS) 64 &&
    decide ((p.η, p.η) ∈ bitPackParams) && decide (64 ≤ p.skLen)

theorem dChk_ok {p : Params} (h : Ok3 p) : dChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

/-- Decoded: `Â`, `ŝ₁`, `ŝ₂`, `t̂₀`, and `ρ″` at `MS`. -/
structure IK (p : Params) (D : Nat) (σ s : State) : Prop where
  d : ID p D σ p.ℓ p.k p.k s
  rpp : bytesAt s.mem (pa s (sc oMS)) 64 = rppOf p σ

theorem dChk_spec {p : Params} (hc : dChk p = true) :
    (∀ r < p.ℓ, decChk p r 0 0 (.rbp, skS1 p r) (sLen p) (s1Base p + r) = true ∧ skS1 p r + sLen p ≤ p.skLen) ∧
    (∀ i < p.k, decChk p p.ℓ i 0 (.rbp, skS2 p i) (sLen p) (s2Base p + i) = true ∧ skS2 p i + sLen p ≤ p.skLen) ∧
    (∀ i < p.k, decChk p p.ℓ p.k i (.rbp, skT0 p i) 416 (t0Base p + i) = true ∧ skT0 p i + 416 ≤ p.skLen) ∧
    shakeChk (sgB p) (sgW p) [((.rbp, 32), 32), ((.r13, 0), 32), ((.r12, 0), 64)] (sc oMS) 64 = true ∧
    idChk p [(sc 0, 200), (sc 200, 640), (sc oMS, 64)] p.ℓ p.k p.k = true ∧ inB (sgB p) (sc oMS) 64 = true ∧
    (p.η, p.η) ∈ bitPackParams ∧ 64 ≤ p.skLen := by
  simp only [dChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, hη⟩, hsk⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, hη, hsk⟩

theorem sLen_eq (p : Params) : sLen p = 32 * bitlen (p.η + p.η) := by rw [← Nat.two_mul]

section
variable {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hc : dChk p = true) {σ : State}
include hP hc

theorem decS1_ok {r : Nat} (hr : r < p.ℓ) {s : State} (hs : ID p D σ r 0 0 s) :
    WP isa (decS1 P p r) s (ID p D σ (r + 1) 0 0) := by
  obtain ⟨c, ck⟩ := (dChk_spec hc).1 r hr
  refine WP.mono (dec_ok hP (dChk_spec hc).2.2.2.2.2.2.1 (sLen_eq p) c hs) fun s' ⟨I', hq⟩ =>
    ⟨I'.im, Fam.snoc I'.s1 ?_, I'.s2, I'.t0⟩
  rw [sk_slice hs.im.st ck] at hq
  exact hq

theorem decS2_ok {i : Nat} (hi : i < p.k) {s : State} (hs : ID p D σ p.ℓ i 0 s) :
    WP isa (decS2 P p i) s (ID p D σ p.ℓ (i + 1) 0) := by
  obtain ⟨c, ck⟩ := (dChk_spec hc).2.1 i hi
  refine WP.mono (dec_ok hP (dChk_spec hc).2.2.2.2.2.2.1 (sLen_eq p) c hs) fun s' ⟨I', hq⟩ =>
    ⟨I'.im, I'.s1, Fam.snoc I'.s2 ?_, I'.t0⟩
  rw [sk_slice hs.im.st ck] at hq
  exact hq

theorem decT0_ok {i : Nat} (hi : i < p.k) {s : State} (hs : ID p D σ p.ℓ p.k i s) :
    WP isa (decT0 P p i) s (ID p D σ p.ℓ p.k (i + 1)) := by
  obtain ⟨c, ck⟩ := (dChk_spec hc).2.2.1 i hi
  refine WP.mono (dec_ok hP (by decide) (by decide) c hs) fun s' ⟨I', hq⟩ => ⟨I'.im, I'.s1, I'.s2,
    Fam.snoc I'.t0 ?_⟩
  have e : skT0 p i = 128 + lenS p * p.ℓ + lenS p * p.k + 32 * 13 * i := by
    unfold skT0 lenS sLen; rw [Nat.mul_add]; omega
  rw [sk_slice hs.im.st ck, e] at hq
  exact hq

theorem rpp_ok {s : State} (hs : ID p D σ p.ℓ p.k p.k s) : WP isa rpp s (IK p D σ) := by
  unfold rpp
  obtain ⟨_, _, _, h4, h5, _, _, hsk⟩ := dChk_spec hc
  refine WP.mono (shake_ok (sgB_bases p) hP.hD h4 hs.im.st.lay) fun s4 ⟨hP4, _, hb⟩ =>
    ⟨hs.step hP4 h5, ?_⟩
  rw [hP4.pa (by decide), hb]
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [sk_slice hs.im.st (o := 32) (len := 32) (by omega), hs.im.st.rnd, hs.im.st.mu, ← List.append_assoc]

theorem decode_ok {s : State} (h : IM p D σ s) : WP isa (decode P p) s (IK p D σ) := by
  unfold decode
  refine WP.seq (WP.mono (seqR_ok (I := fun r => ID p D σ r 0 0) p.ℓ 0
    (fun r _ hr s hs => decS1_ok hP hc (by omega) hs) s
    ⟨h, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s1 hs1 => ?_)
  rw [Nat.zero_add] at hs1
  refine WP.seq (WP.mono (seqR_ok (I := fun i => ID p D σ p.ℓ i 0) p.k 0
    (fun i _ hi s hs => decS2_ok hP hc (by omega) hs) s1
    ⟨hs1.im, hs1.s1, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s2 hs2 => ?_)
  rw [Nat.zero_add] at hs2
  refine WP.seq (WP.mono (seqR_ok (I := fun i => ID p D σ p.ℓ p.k i) p.k 0
    (fun i _ hi s hs => decT0_ok hP hc (by omega) hs) s2
    ⟨hs2.im, hs2.s1, hs2.s2, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s3 hs3 => ?_)
  rw [Nat.zero_add] at hs3
  exact rpp_ok hP hc hs3

end

/-! ## A prepared key -/

/-- The buffers read, with the whole prepared key at `rbp`. -/
abbrev sgRP (p : Params) : List (Reg × Nat) := [(.rbp, preparedSecretKeyBytes p), (.r12, 64), (.r13, 32)]

/-- The length of the polynomials of a prepared key. -/
abbrev polysLen (p : Params) : Nat := 1024 * (p.ℓ + 2 * p.k)

/-- What copying the polynomials of a prepared key needs of the layout. -/
def pkChk (p : Params) : Bool :=
  copyChk (sgRP p ++ sgW p) (sgW p) (s1P p 0) (.rbp, p.skLen) (polysLen p) &&
    imChk p [(s1P p 0, polysLen p)] && imChk p [] && inB (sgB p) (sc oFL) 8 && decide (preparedSecretKeyBytes p < 2 ^ 32) &&
    decide (scrLen p < 2 ^ 32 ∧ p.sigLen < 2 ^ 32) && decide (p.skLen + polysLen p = preparedSecretKeyBytes p)

theorem pkChk_ok {p : Params} (h : Ok3 p) : pkChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

/-- Polynomial `i` of the prepared key of the function entered in `σ`. -/
abbrev prepV (p : Params) (σ : State) (i : Nat) : Poly := (preparedSecretPolys p (skOf p σ))[i]!

theorem prep_fam {p : Params} {D : Nat} {σ s s' : State} (hpre : (signK p D).pre σ) (hf : σ.gpr .r9 ≠ 0)
    (hc : pkChk p = true) (h : IM p D σ s) (hP : PPostB D s s' [(s1P p 0, polysLen p)])
    (hb : bytesAt s'.mem (pa s (s1P p 0)) (polysLen p) = bytesAt s.mem (pa s (.rbp, p.skLen)) (polysLen p))
    {i : Nat} (hi : i < p.ℓ + 2 * p.k) : Pl s' (s1Base p + i) (prepV p σ i) := by
  simp only [pkChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, hlen⟩ := hc
  have hpre' := hpre
  obtain ⟨-, hwr, d1, d2, -, -, -, -, -, -, -, -, -, -, k1, -, -, -, -, n1, -, -, -, -, -, hprep⟩ := hpre'
  have hL : skL p σ = preparedSecretKeyBytes p := by simp only [skL, hf, ite_false]
  rw [hL] at d1 d2 k1 n1
  have e2 : s.gpr .rbp = σ.gpr .rdi := h.st.top.regs (.rbp, .rdi) (by decide)
  -- The polynomial in the prepared key, unchanged since entry.
  have hl : p.skLen + 1024 * (p.ℓ + 2 * p.k) = preparedSecretKeyBytes p := hlen
  have hA : σ.gpr .rdi + BitVec.ofNat 64 p.skLen + BitVec.ofNat 64 (1024 * i) =
      σ.gpr .rdi + BitVec.ofNat 64 (p.skLen + 1024 * i) := VG.Proof.MlKem.X86_64.off_add _ _ _
  have hsub : Region.Sub ⟨σ.gpr .rdi + BitVec.ofNat 64 (p.skLen + 1024 * i), 1024⟩
      ⟨σ.gpr .rdi, preparedSecretKeyBytes p⟩ := Offset.sub_base _ (by omega)
  have hσ : bytesAt s.mem (σ.gpr .rdi + BitVec.ofNat 64 (p.skLen + 1024 * i)) 1024 =
      bytesAt σ.mem (σ.gpr .rdi + BitVec.ofNat 64 (p.skLen + 1024 * i)) 1024 := by
    refine VG.Proof.MlKem.bytesAt_frame h.st.fr (fun r hr => ?_) (by decide)
    rw [hwr] at hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [d1.sub_left hsub, d2.sub_left hsub, (k1.sub_right hsub).symm]
  have hpoly : PolyIs σ.mem (σ.gpr .rdi + BitVec.ofNat 64 (p.skLen + 1024 * i)) (prepV p σ i) :=
    (polyStored_iff).mp (hprep hf i hi)
  show PolyIs s'.mem (pa s' (pS (s1Base p + i))) _
  rw [hP.pa (pS_bases _)]
  refine PreparedKey.polyIs_of_copy ?_ hpoly
  have hd : pa s (pS (s1Base p + i)) = pa s (s1P p 0) + BitVec.ofNat 64 (1024 * i) := by
    rw [pa_add]
    exact congrArg (fun o => pa s (.rbx, o)) (by simp only [oP, s1Base]; omega)
  have hi' : 1024 * i + 1024 ≤ polysLen p := by simp only [polysLen]; omega
  rw [hd, ← VG.Proof.MlKem.bytesAt_slice _ _ hi', hb, VG.Proof.MlKem.bytesAt_slice _ _ hi', ← hσ, ← hA]
  simp only [pa, e2]

theorem prepV_s1 (p : Params) (σ : State) {r : Nat} (hr : r < p.ℓ) : prepV p σ r = S1v p σ r :=
  PreparedKey.secret_s1 p _ hr

theorem prepV_s2 (p : Params) (σ : State) {i : Nat} (hi : i < p.k) : prepV p σ (p.ℓ + i) = S2v p σ i :=
  PreparedKey.secret_s2 p _ hi

theorem prepV_t0 (p : Params) (σ : State) {i : Nat} (hi : i < p.k) : prepV p σ (p.ℓ + p.k + i) = T0v p σ i :=
  PreparedKey.secret_t0 p _ hi

theorem copyKey_ok {p : Params} {D : Nat} {σ s : State} (hpre : (signK p D).pre σ) (hf : σ.gpr .r9 ≠ 0)
    (hD : D < 2 ^ 32) (hc : pkChk p = true) (h : IM p D σ s) :
    WP isa (copyKey p) s (ID p D σ p.ℓ p.k p.k) := by
  have hc' := hc
  simp only [pkChk, Bool.and_eq_true, decide_eq_true_eq] at hc'
  obtain ⟨⟨⟨⟨⟨⟨hcp, him⟩, -⟩, -⟩, hpl⟩, hsz⟩, -⟩ := hc'
  have hL : preparedSecretKeyBytes p ≤ skL p σ := by simp only [skL, hf, ite_false]; exact Nat.le_refl _
  have L' : Lay D (sgRP p) (sgW p) s := sgLayL hpre hL hD ⟨hsz.1, hpl, hsz.2⟩ h.st.top
  unfold copyKey
  refine WP.mono (copy_okB L' hcp) fun s' ⟨hP, _, hb⟩ => ?_
  have I := h.step hP him
  refine ⟨I, fun r hr => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [← prepV_s1 p σ hr]; exact prep_fam hpre hf hc h hP hb (by omega)
  · rw [← prepV_s2 p σ hi, show s2Base p + i = s1Base p + (p.ℓ + i) by simp only [s1Base, s2Base]; omega]
    exact prep_fam hpre hf hc h hP hb (by omega)
  · rw [← prepV_t0 p σ hi, show t0Base p + i = s1Base p + (p.ℓ + p.k + i) by simp only [s1Base, t0Base]; omega]
    exact prep_fam hpre hf hc h hP hb (by omega)

/-- The flag at `FL` is the entry's `r9`. -/
theorem testFlag_ok {D : Nat} {σ s : State} (ht : Top σ s) (hin : InRegions (s.rd ++ s.wr) (pa s (sc oFL)) 8) :
    WP isa (.block testFlag) s fun s' => PPostB D s s' [] ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.zf = some (σ.gpr .r9 == 0) := by
  have e := ht.flag
  simp only [pa] at hin e
  unfold testFlag
  refine WP.mono (VG.Proof.MlKem.X86_64.WP.keep [.rax] (Q := fun s' => s'.mem = s.mem ∧
      s'.zf = some (s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 oFL) 64 &&&
        s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 oFL) 64 == 0)) (by xrun [hin]) (by decide))
    fun s' ⟨⟨hm, hz⟩, k⟩ => ⟨⟨k.2.1, k.2.2, fun r hr => k.gpr (by
        simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide), k.gpr (by decide),
        by rw [hm]; exact Frame.refl _ _⟩,
      fun r hr => k.gpr (by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), hm, by rw [hz, e, BitVec.and_self]⟩

theorem decodeOrCopy_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hc : dChk p = true)
    (hk : pkChk p = true) {σ s : State} (hpre : (signK p D).pre σ) (h : IM p D σ s) :
    WP isa (decodeOrCopy P p) s (IK p D σ) := by
  have hk' := hk
  simp only [pkChk, Bool.and_eq_true] at hk'
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, him⟩, hin⟩, -⟩, -⟩, -⟩ := hk'
  unfold decodeOrCopy
  refine WP.seq (WP.mono (testFlag_ok (D := D) h.st.top (h.st.lay.iR hin)) fun s1 ⟨hP1, _, _, hz⟩ => ?_)
  have h1 := h.step hP1 him
  refine WP.ite (M := isa) (!(σ.gpr .r9 == 0)) (show s1.zf.map (!·) = _ by rw [hz]; rfl) (fun hb => ?_) fun hb => ?_
  · have hf : σ.gpr .r9 ≠ 0 := by simpa using hb
    exact WP.seq (WP.mono (copyKey_ok hpre hf hP.hD' hk h1) fun s2 h2 => rpp_ok hP hc h2)
  · exact decode_ok hP hc h1

end VG.Proof.MlDsa.X86_64.Sign

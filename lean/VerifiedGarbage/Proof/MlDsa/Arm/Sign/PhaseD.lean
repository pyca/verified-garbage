module

public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PhaseA
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PrimsD
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PrimsB
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Hash
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.PrimsC
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Blocks
import VerifiedGarbage.Proof.MlKem.Arm.Loops
import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
import VerifiedGarbage.Proof.MlKem.Mem

/-!
# ML-DSA signing on ARMv7: the private key and `ρ″`

Once `Â` is sampled (`IM`), `ŝ₁[r]`, `ŝ₂[i]` and `t̂₀[i]`, each the `NTT` of
the `BitUnpack` of its piece of `sk` (`dec_ok`), in their slots (`ID`), and
`ρ″ = H(K ‖ rnd ‖ μ, 64)` at `MS` (`decode_ok`); or, with prepared polynomials
(`r9 ≠ 0`), the three copied from them at once (`decodeC_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
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

theorem sk_slice {p : Params} {D : Nat} {σ s : State} (h : St p D σ s) {o len : Nat} (hk : o + len ≤ p.skLen) :
    bytesAt s.mem (pa s (.r4, o)) len = ((skOf p σ).drop o).take len := by
  rw [← h.sk, VG.Proof.MlKem.bytesAt_slice _ _ hk, ← pa_add, Nat.zero_add]

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
  (List.range p.ℓ).all (fun r => decChk p r 0 0 (.r4, skS1 p r) (sLen p) (s1Base p + r) &&
      decide (skS1 p r + sLen p ≤ p.skLen)) &&
    (List.range p.k).all (fun i => decChk p p.ℓ i 0 (.r4, skS2 p i) (sLen p) (s2Base p + i) &&
      decide (skS2 p i + sLen p ≤ p.skLen)) &&
    (List.range p.k).all (fun i => decChk p p.ℓ p.k i (.r4, skT0 p i) 416 (t0Base p + i) &&
      decide (skT0 p i + 416 ≤ p.skLen)) &&
    shakeChk (sgB p) (sgW p) [((.r4, 32), 32), ((.r6, 0), 32), ((.r5, 0), 64)] (sc oMS) 64 &&
    idChk p [(sc 0, 200), (sc 200, 640), (sc oMS, 64)] p.ℓ p.k p.k && inB (sgB p) (sc oMS) 64 &&
    decide ((p.η, p.η) ∈ bitPackParams) && decide (64 ≤ p.skLen)

theorem dChk_ok {p : Params} (h : Ok3 p) : dChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

/-- Decoded: `Â`, `ŝ₁`, `ŝ₂`, `t̂₀`, and `ρ″` at `MS`. -/
structure IK (p : Params) (D : Nat) (σ s : State) : Prop where
  d : ID p D σ p.ℓ p.k p.k s
  rpp : bytesAt s.mem (pa s (sc oMS)) 64 = rppOf p σ

theorem dChk_spec {p : Params} (hc : dChk p = true) :
    (∀ r < p.ℓ, decChk p r 0 0 (.r4, skS1 p r) (sLen p) (s1Base p + r) = true ∧ skS1 p r + sLen p ≤ p.skLen) ∧
    (∀ i < p.k, decChk p p.ℓ i 0 (.r4, skS2 p i) (sLen p) (s2Base p + i) = true ∧ skS2 p i + sLen p ≤ p.skLen) ∧
    (∀ i < p.k, decChk p p.ℓ p.k i (.r4, skT0 p i) 416 (t0Base p + i) = true ∧ skT0 p i + 416 ≤ p.skLen) ∧
    shakeChk (sgB p) (sgW p) [((.r4, 32), 32), ((.r6, 0), 32), ((.r5, 0), 64)] (sc oMS) 64 = true ∧
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

theorem rpp_ok {s : State} (hs : ID p D σ p.ℓ p.k p.k s) :
    WP isa (shakeAt [((.r4, 32), 32), ((.r6, 0), 32), ((.r5, 0), 64)] (sc oMS) 64) s (IK p D σ) := by
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

/-! ## Prepared polynomials -/

/-- What `decodeC` needs of the layout. -/
def dcChk (p : Params) : Bool :=
  inB (sgW p) (s1P p 0) (cacheLen p) && inB (sgB p) (s1P p 0) (cacheLen p) && imChk p [] && imChk p [(s1P p 0, cacheLen p)] &&
    decide (0 < cacheLen p ∧ cacheLen p < 2 ^ 32) && decide (s1Base p + p.ℓ = s2Base p) &&
    decide (s2Base p + p.k = t0Base p)

theorem dcChk_ok {p : Params} (h : Ok3 p) : dcChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

theorem cmp9_ok (s : State) (D : Nat) :
    WP isa (.block [.cmp .r9 (.imm 0)]) s fun s₁ => PPostB D s s₁ [] ∧ CS s s₁ ∧ s₁.mem = s.mem ∧
      s₁.z = (s.gpr .r9 == 0) := by
  have h : WP isa (.block [.cmp .r9 (.imm 0)]) s fun s₁ => s₁.gpr = s.gpr ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr ∧ s₁.sp = s.sp ∧ s₁.z = (s.gpr .r9 == 0) := by
    run_block []
    simp
  refine WP.mono h fun s₁ ⟨g, m, rd, wr, sp, z⟩ => ?_
  have hcs : CS s s₁ := fun r _ _ => by rw [g]
  exact ⟨PostB.of_cs hcs rd wr sp (by rw [m]; exact Frame.refl _ _), hcs, m, z⟩

theorem oP_s1 (p : Params) (j : Nat) : (pS (s1Base p + j)) = (.r7, oP (s1Base p) + 1024 * j) := by
  simp only [pS, sc, oP, Nat.mul_add, Nat.add_assoc]

/-- After the copy: the slots of `ŝ₁ ‖ ŝ₂ ‖ t̂₀` hold the prepared polynomials. -/
theorem cachedSlot {D : Nat} {p : Params} {σ : State} {s : State} (hpre : (signK p D).pre σ) (hne : stackArg σ 1 ≠ 0)
    (hb : bytesAt s.mem (pa s (s1P p 0)) (cacheLen p) = bytesAt σ.mem (State.addr (stackArg σ 1)) (cacheLen p))
    {j : Nat} (hj : j < p.ℓ + 2 * p.k) :
    Pl s (s1Base p + j) (preparedSecretPolys p (skOf p σ))[j]! := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcp⟩ := hpre
  obtain ⟨-, -, -, -, hpol⟩ := hcp hne
  have hpj := hpol j hj
  rw [show 4 * Spec.MlDsa.n * j = 1024 * j by simp only [Spec.MlDsa.n]] at hpj
  refine VG.Proof.MlDsa.PreparedKey.polyIs_of_copy ?_ hpj
  have hk : 1024 * j + 1024 ≤ cacheLen p := by simp only [cacheLen]; omega
  rw [oP_s1, pa_add, ← VG.Proof.MlKem.bytesAt_slice _ _ hk, ← VG.Proof.MlKem.bytesAt_slice _ _ hk]
  show ((bytesAt s.mem (pa s (s1P p 0)) (cacheLen p)).drop (1024 * j)).take 1024 = _
  rw [hb]

theorem cacheR_rd {p : Params} {D : Nat} {σ : State} (hpre : (signK p D).pre σ) (hne : stackArg σ 1 ≠ 0) :
    cacheR p σ ∈ σ.rd := by
  rw [hpre.1]; simp only [cacheRd, hne, ite_false]; simp

/-- The copy of the prepared polynomials to their slots. -/
theorem cachedCopy_ok {D : Nat} {p : Params} (hc : dcChk p = true) {σ s : State} (hpre : (signK p D).pre σ)
    (hne : stackArg σ 1 ≠ 0) (h : IM p D σ s) :
    WP isa (copy (s1P p 0) (.r9, 0) (cacheLen p)) s (ID p D σ p.ℓ p.k p.k) := by
  simp only [dcChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨hin, iw⟩, -⟩, him⟩, hlen0, hlen⟩, e1⟩, e2⟩ := hc
  have L := h.st.lay
  have ht := h.st.top
  obtain ⟨d1, d2, -, -, hb⟩ := h.st.ck hne
  have hpre' := hpre
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcp⟩ := hpre'
  obtain ⟨-, -, -, hfit, -⟩ := hcp hne
  have e9 : s.gpr .r9 = stackArg σ 1 := ht.regs .r9 (by decide)
  unfold copy
  refine WP.seq (WP.mono (copySetup_ok (src := (.r9, 0)) (dst := s1P p 0) (by decide) (pS_bases _) s)
    fun s1 ⟨g0, g1, g2, k⟩ => ?_)
  have ad := L.pa32 iw hlen0
  have as : State.addr (s.gpr .r9 + BitVec.ofNat 32 0) = State.addr (stackArg σ 1) := by
    rw [e9]; simp
  refine WP.mono (VG.Proof.MlKem.Arm.copy_loop (by rw [e9]; simpa using hfit) (L.fit iw hlen0) hlen hlen0
    (by rw [as, ad]; exact cacheR_disj d1 d2 ht hin)
    (by rw [as, k.rd, k.wr]
        exact Covers.one ⟨_, List.mem_append_left _ (by rw [ht.rd]; exact cacheR_rd hpre hne),
          Region.contains_self _ _⟩)
    (by rw [ad, k.wr]; exact L.cW hin) g0 g1 g2) fun s' ⟨hcs, rd, wr, sp, hf, hbs⟩ => ?_
  rw [ad, k.mem] at hf
  rw [ad, as, k.mem] at hbs
  have c : CS s s' := fun r hr hl => (hcs r hr).trans (k.cs r hr hl)
  have hP : PPostB D s s' [(s1P p 0, cacheLen p)] :=
    PostB.of_cs c (rd.trans k.rd) (wr.trans k.wr) (sp.trans k.sp) hf
  have I' := h.step hP him
  have hb' : bytesAt s'.mem (pa s' (s1P p 0)) (cacheLen p) =
      bytesAt σ.mem (State.addr (stackArg σ 1)) (cacheLen p) := by
    rw [hP.pa (pS_bases _), hbs, hb]
  refine ⟨I', fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · have := cachedSlot hpre hne hb' (j := j) (by omega)
    rwa [VG.Proof.MlDsa.PreparedKey.secret_s1 _ _ hj] at this
  · have := cachedSlot hpre hne hb' (j := p.ℓ + j) (by omega)
    rwa [VG.Proof.MlDsa.PreparedKey.secret_s2 _ _ hj, ← Nat.add_assoc, e1] at this
  · have := cachedSlot hpre hne hb' (j := p.ℓ + p.k + j) (by omega)
    rwa [VG.Proof.MlDsa.PreparedKey.secret_t0 _ _ hj, ← Nat.add_assoc, ← Nat.add_assoc, e1, e2] at this

theorem decodeC_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hd : dChk p = true)
    (hc : dcChk p = true) {σ s : State} (hpre : (signK p D).pre σ) (h : IM p D σ s) :
    WP isa (decodeC P p) s (IK p D σ) := by
  have him0 : imChk p [] = true := by
    simp only [dcChk, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨-, -⟩, h0⟩, -⟩, -⟩, -⟩, -⟩ := hc
    exact h0
  unfold decodeC
  refine WP.seq (WP.mono (cmp9_ok s D) fun s₁ ⟨hP₁, _, _, hz⟩ => ?_)
  have h₁ := h.step hP₁ him0
  refine WP.ite (M := isa) (!(s.gpr .r9 == 0)) (show some (!s₁.z) = _ by rw [hz]) (fun hb => ?_)
    fun _ => decode_ok hP hd h₁
  have hne : stackArg σ 1 ≠ 0 := by
    have e := h.st.top.regs .r9 (by decide)
    simp only [ptrOf] at e
    rw [← e]; simpa using hb
  unfold cached
  exact WP.seq (WP.mono (cachedCopy_ok hc hpre hne h₁) fun s₂ h₂ => rpp_ok hP hd h₂)

end VG.Proof.MlDsa.Arm.Sign

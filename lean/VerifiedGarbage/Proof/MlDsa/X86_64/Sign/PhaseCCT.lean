module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseDCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.BlockTr
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Blocks
import VerifiedGarbage.Proof.MlDsa.Arith.DotSum
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseA
import VerifiedGarbage.Proof.Sha3.X86_64.Round

/-! ### `MlDsa.X86_64.Sign.PhaseA4`, which this module and modules that import it used -/

section

/-!
# ML-DSA signing on x86-64: `ExpandA`, four entries at a time

`ρ` to `RS` and to each of the four seeds at `RS4` (`IA4`); then, for each
group of four entries `4g, …, 4g + 3`, their indices to the seeds (`GS`,
`slot_ok`) and one call of `vg_mldsa_rej_ntt_poly4`, ANDed into `r15`
(`call4_ok`); then the last `kℓ mod 4` entries one at a time (`sampleE_ok`).
Each step keeps `IA` (`expandA_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- `ExpandA` after `e` entries, with `ρ` in each seed of `RS4`. -/
structure IA4 (p : Params) (D : Nat) (σ : State) (e : Nat) (s : State) : Prop where
  ia : IA p D σ e s
  rs4 : ∀ k < 4, bytesAt s.mem (pa s (sc (oRS4 + 34 * k))) 32 = rhoOf p σ

/-- … and the seeds of entries `e, …, e + j - 1` in the first `j` seeds. -/
structure GS (p : Params) (D : Nat) (σ : State) (e j : Nat) (s : State) : Prop where
  ia4 : IA4 p D σ e s
  done : ∀ k < j, bytesAt s.mem (pa s (sc (oRS4 + 34 * k))) 34 = seedE p σ (e + k)

/-! ## Pieces that keep `IA` -/

theorem IA.step {p : Params} {D : Nat} {σ : State} {e : Nat} {s s' : State} (h : IA p D σ e s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) (hst : stChk p ws = true) (hk : keepB (sgB p) ws (sc oRS) 32 = true)
    (hf : famChk (sgB p) ws (aBase p) e = true) (e15 : s'.gpr .r15 = s.gpr .r15) : IA p D σ e s' := by
  refine ⟨h.st.step hP hst, (h.st.lay.keepBytes hP hk).trans h.rs, by rw [e15]; exact h.r01, fun h1 => ?_,
    fun h0 => h.bad (by rw [← e15]; exact h0)⟩
  obtain ⟨ok, fam⟩ := h.ok (by rw [← e15]; exact h1)
  exact ⟨ok, Fam.keep h.st.lay hP hf fam⟩

/-- The seeds of `RS4` apart from `ws`. -/
def rs4Chk (p : Params) (ws : List (Ptr × Nat)) (n : Nat) : Bool :=
  (List.range 4).all fun k => keepB (sgB p) ws (sc (oRS4 + 34 * k)) n

theorem rs4Chk_spec {p : Params} {ws : List (Ptr × Nat)} {n : Nat} (h : rs4Chk p ws n = true) {k : Nat}
    (hk : k < 4) : keepB (sgB p) ws (sc (oRS4 + 34 * k)) n = true :=
  List.all_eq_true.mp h k (List.mem_range.mpr hk)

theorem IA4.step {p : Params} {D : Nat} {σ : State} {e : Nat} {s s' : State} (h : IA4 p D σ e s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) (hst : stChk p ws = true) (hk : keepB (sgB p) ws (sc oRS) 32 = true)
    (hf : famChk (sgB p) ws (aBase p) e = true) (h4 : rs4Chk p ws 32 = true) (e15 : s'.gpr .r15 = s.gpr .r15) :
    IA4 p D σ e s' :=
  ⟨h.ia.step hP hst hk hf e15, fun k hk => (h.ia.st.lay.keepBytes hP (rs4Chk_spec h4 hk)).trans (h.rs4 k hk)⟩

/-! ## The seeds of a group -/

/-- What seed `j` of entry `e + j` needs of the layout. -/
def slotChk (p : Params) (e j : Nat) : Bool :=
  let w1 : List (Ptr × Nat) := [(sc (oRS4 + 34 * j + 32), 1)]
  let w2 : List (Ptr × Nat) := [(sc (oRS4 + 34 * j + 33), 1)]
  stChk p w1 && stChk p w2 && inB (sgW p) (sc (oRS4 + 34 * j + 32)) 1 && inB (sgW p) (sc (oRS4 + 34 * j + 33)) 1 &&
    keepB (sgB p) w1 (sc oRS) 32 && keepB (sgB p) w2 (sc oRS) 32 && famChk (sgB p) w1 (aBase p) e &&
    famChk (sgB p) w2 (aBase p) e && rs4Chk p w1 32 && rs4Chk p w2 32 &&
    keepB (sgB p) w2 (sc (oRS4 + 34 * j + 32)) 1 &&
    (List.range j).all (fun k => keepB (sgB p) w1 (sc (oRS4 + 34 * k)) 34 && keepB (sgB p) w2 (sc (oRS4 + 34 * k)) 34) &&
    decide ((e + j) % p.ℓ < 256) && decide ((e + j) / p.ℓ < 256)

theorem slot_ok {p : Params} {D : Nat} {σ : State} {e j : Nat} (hj4 : j < 4) (hc : slotChk p e j = true) {s : State}
    (h : GS p D σ e j s) : WP isa (.block (setSR p e j)) s fun s' => GS p D σ e (j + 1) s' ∧ s'.gpr .r15 = s.gpr .r15 := by
  simp only [slotChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, w1⟩, w2⟩, k1⟩, k2⟩, f1⟩, f2⟩, r1⟩, r2⟩, k12⟩, kd⟩, hj⟩, hi⟩ := hc
  have L := h.ia4.ia.st.lay
  unfold setSR
  rw [WP.block_append_iff]
  refine WP.mono (setB_okB L (show Reg.rbx ≠ .rax by decide) hj w1) fun s1 ⟨hP1, hcs1, hm1⟩ => ?_
  have e1 : s1.gpr .r15 = s.gpr .r15 := hcs1 _ (by decide)
  have I1 := h.ia4.step hP1 c1 k1 f1 r1 e1
  refine WP.mono (setB_okB I1.ia.st.lay (show Reg.rbx ≠ .rax by decide) hi w2) fun s2 ⟨hP2, hcs2, hm2⟩ => ?_
  have e2 : s2.gpr .r15 = s1.gpr .r15 := hcs2 _ (by decide)
  have I2 := I1.step hP2 c2 k2 f2 r2 e2
  refine ⟨⟨I2, fun k hk => ?_⟩, e2.trans e1⟩
  rcases (by omega_using [hk] : k < j ∨ k = j) with hk' | rfl
  · have kk := List.all_eq_true.mp kd k (List.mem_range.mpr hk')
    simp only [Bool.and_eq_true] at kk
    rw [I1.ia.st.lay.keepBytes hP2 kk.2, L.keepBytes hP1 kk.1]
    exact h.done k hk'
  · refine seed34 (I2.rs4 k (by omega_using [hj4])) ?_ ?_
    · rw [pa_sc_add, I1.ia.st.lay.keepBytes hP2 k12, hm1, hP1.pa (show Reg.rbx ∈ bases by decide)]; exact bytes1_write _ _ _
    · rw [pa_sc_add, hm2, hP2.pa (show Reg.rbx ∈ bases by decide)]; exact bytes1_write _ _ _

/-! ## The call -/

theorem pa_poly4 (s : State) (i k : Nat) : poly4 (pa s (pS i)) k = pa s (pS (i + k)) := by
  unfold poly4
  rw [pa_sc_add, show oP i + 1024 * k = oP (i + k) by simp only [oP]; omega_using []]

theorem seed4_eq {p : Params} {D : Nat} {σ : State} {e : Nat} {s : State} (h : GS p D σ e 4 s) {k : Nat}
    (hk : k < 4) : seed4 s.mem (pa s (sc oRS4)) k = seedE p σ (e + k) := by
  unfold seed4
  rw [pa_sc_add]; exact h.done k hk

/-- What the call of a group needs of the layout. -/
def callChk (p : Params) (e : Nat) : Bool :=
  let w3 : List (Ptr × Nat) := [(pS (aBase p + e), 4096), (r4P p, 8192)]
  stChk p w3 && stChk p [] && keepB (sgB p) w3 (sc oRS) 32 && rs4Chk p w3 32 && famChk (sgB p) w3 (aBase p) e &&
    rej4Chk (sgB p) (sgW p) (pS (aBase p + e)) (r4P p)

/-- What the call of group `e` leaves. -/
abbrev R4Post (D : Nat) (a w : Ptr) (s s' : State) : Prop :=
  PPostB D s s' [(a, 4096), (w, 8192)] ∧ (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
    ((s'.gpr .rax).setWidth 32 = 1 → ∀ k < 4, Reduced s'.mem (poly4 (pa s a) k)) ∧
    (((s'.gpr .rax).setWidth 32 = 1 ∧ ∀ k < 4, ∃ b : Bounds,
        rejNTTPoly b.rejNTT (seed4 s.mem (pa s (sc oRS4)) k) = some (polyAt s'.mem (poly4 (pa s a) k))) ∨
      ((s'.gpr .rax).setWidth 32 = 0 ∧ ∃ k < 4,
        rejNTTPoly minBounds.rejNTT (seed4 s.mem (pa s (sc oRS4)) k) = none)) ∧
    ((s'.gpr .rax).setWidth 32 = 1 → ∀ k < 4,
      (rejNTTPoly maxBounds.rejNTT (seed4 s.mem (pa s (sc oRS4)) k)).isSome)

/-- The call of group `e` is done. -/
def J4 (p : Params) (D e : Nat) (σ s : State) : Prop :=
  ∃ s₀, GS p D σ e 4 s₀ ∧ R4Post D (pS (aBase p + e)) (r4P p) s₀ s

theorem callG_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {e : Nat}
    (hc : callChk p e = true) {s : State} (h : GS p D σ e 4 s) :
    WP isa (callP ("vg_mldsa_rej_ntt_poly4" ++ P.sfx) P.rej4 [.ptr (sc oRS4), .ptr (pS (aBase p + e)), .ptr (r4P p)]) s
      fun s' => J4 p D e σ s' ∧ s'.gpr .r15 = s.gpr .r15 := by
  simp only [callChk, Bool.and_eq_true] at hc
  exact WP.mono (rej4Call_ok hP h.ia4.ia.st.lay hc.2) fun s' h' => ⟨⟨s, h, h'⟩, h'.2.1 _ (by decide)⟩

theorem and4_ok {p : Params} {D : Nat} {σ : State} {e : Nat} (hc : callChk p e = true) {s : State}
    (hJ : J4 p D e σ s) : WP isa (.block [.alu32 .and .r15 (.reg .rax)]) s (IA4 p D σ (e + 4)) := by
  simp only [callChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨c3, c0⟩, k3⟩, r3⟩, f3⟩, _⟩ := hc
  obtain ⟨s₀, h, hP3, hcs3, hred, hout, hmax⟩ := hJ
  have L := h.ia4.ia.st.lay
  have I1 := h.ia4.step hP3 c3 k3 f3 r3 (hcs3 _ (by decide))
  refine WP.mono (and15_ok s) fun s4 ⟨h15, hm4, k4⟩ => ?_
  have hP4 : PPostB D s s4 [] := (postB15 k4 hm4 _).1
  rw [hcs3 _ (by decide)] at h15
  have hr : (s.gpr .rax).setWidth 32 = 1 ∨ (s.gpr .rax).setWidth 32 = 0 := by
    rcases hout with ⟨h1, _⟩ | ⟨h0, _⟩
    exacts [.inl h1, .inr h0]
  have hb4 : s4.gpr .rbx = s₀.gpr .rbx := by rw [hP4.bs _ (by decide), hP3.bs _ (by decide)]
  have epa : ∀ q : Ptr, q.1 = .rbx → pa s4 q = pa s₀ q := fun q hq => by simp only [pa, hq, hb4]
  have hia := h.ia4.ia
  refine ⟨⟨I1.ia.st.step hP4 c0, ?_, ?_, fun h1 => ?_, fun h0 => ?_⟩, fun k hk => ?_⟩
  · rw [hm4, epa _ rfl, ← hP3.pa (by decide), I1.ia.rs]
  · rw [h15]
    rcases hia.r01 with e0 | e0 <;> rcases hr with e1 | e1 <;> rw [e0, e1] <;> decide
  · have hs : s₀.gpr .r15 = 1 ∧ (s.gpr .rax).setWidth 32 = 1 := by
      rw [h15] at h1
      rcases hia.r01 with e0 | e0 <;> rcases hr with e1 | e1 <;> rw [e0, e1] at h1 <;>
        first | exact ⟨e0, e1⟩ | exact absurd h1 (by decide)
    obtain ⟨ok1, fam⟩ := hia.ok hs.1
    have hm := hmax hs.2
    refine ⟨fun e' he' => ?_, fun j hj => ?_⟩
    · by_cases he'' : e' < e
      · exact ok1 e' he''
      · obtain ⟨k, hk, rfl⟩ : ∃ k, k < 4 ∧ e' = e + k := ⟨e' - e, by omega_using [he'], by omega_using [he'']⟩
        rw [← seed4_eq h hk]; exact hm k hk
    · by_cases hj' : j < e
      · exact Fam.of_eq hm4 (hP4.bs _ (by decide)) (Fam.keep L hP3 f3 fam) j hj'
      · obtain ⟨k, hk, rfl⟩ : ∃ k, k < 4 ∧ j = e + k := ⟨j - e, by omega_using [hj], by omega_using [hj']⟩
        show PolyIs s4.mem (pa s4 (pS (aBase p + (e + k)))) (aVal p σ (e + k))
        rw [hm4, epa _ rfl, ← Nat.add_assoc, ← pa_poly4]
        rcases hout with ⟨_, hb⟩ | ⟨h0, _⟩
        · refine ⟨hred hs.2 k hk, ?_⟩
          have := rej_val (x := seed4 s₀.mem (pa s₀ (sc oRS4)) k) (.inl ⟨hs.2, hb k hk⟩) hs.2 (hm k hk)
          rw [this, seed4_eq h hk]; rfl
        · rw [hs.2] at h0; cases h0
  · rw [h15] at h0
    rcases hia.r01 with e0 | e0
    · obtain ⟨e', he', hn⟩ := hia.bad e0
      exact ⟨e', by omega_using [he'], hn⟩
    · rcases hr with e1 | e1
      · rw [e0, e1] at h0; exact absurd h0 (by decide)
      · rcases hout with ⟨h1, _⟩ | ⟨_, k, hk, hn⟩
        · rw [e1] at h1; cases h1
        · exact ⟨e + k, by omega_using [hk], by rw [← seed4_eq h hk]; exact hn⟩
  · rw [hm4, epa _ rfl, ← hP3.pa (show Reg.rbx ∈ bases by decide)]; exact I1.rs4 k hk

theorem call4_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {e : Nat}
    (hc : callChk p e = true) {s : State} (h : GS p D σ e 4 s) :
    WP isa (rej4At P (pS (aBase p + e)) (r4P p)) s (IA4 p D σ (e + 4)) := by
  unfold rej4At
  exact WP.seq (WP.mono (callG_ok hP hc h) fun _ h' => and4_ok hc h'.1)

theorem bytes136 (m : Mem) (P : Addr) : bytesAt m P 136 = bytesAt m P 34 ++ bytesAt m (P + BitVec.ofNat 64 34) 34 ++
    bytesAt m (P + BitVec.ofNat 64 68) 34 ++ bytesAt m (P + BitVec.ofNat 64 102) 34 := by
  rw [show 136 = 34 + 102 from rfl, VG.Proof.MlKem.bytesAt_add, show 102 = 34 + 68 from rfl,
    VG.Proof.MlKem.bytesAt_add, show 68 = 34 + 34 from rfl, VG.Proof.MlKem.bytesAt_add]
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add, List.append_assoc, Nat.reduceAdd]

/-- The four seeds of a group, from `ρ`. -/
theorem GS.seeds {p : Params} {D : Nat} {σ : State} {e : Nat} {s : State} (h : GS p D σ e 4 s) :
    bytesAt s.mem (pa s (sc oRS4)) 136 = aSeed (rhoOf p σ) ((e + 0) / p.ℓ) ((e + 0) % p.ℓ) ++
      aSeed (rhoOf p σ) ((e + 1) / p.ℓ) ((e + 1) % p.ℓ) ++ aSeed (rhoOf p σ) ((e + 2) / p.ℓ) ((e + 2) % p.ℓ) ++
      aSeed (rhoOf p σ) ((e + 3) / p.ℓ) ((e + 3) % p.ℓ) := by
  have b : ∀ k < 4, bytesAt s.mem (pa s (sc oRS4) + BitVec.ofNat 64 (34 * k)) 34 = seedE p σ (e + k) :=
    fun k hk => seed4_eq h hk
  have b0 := b 0 (by decide)
  rw [show 34 * 0 = 0 from rfl, BitVec.add_zero] at b0
  rw [bytes136, b0, b 1 (by decide), b 2 (by decide), b 3 (by decide)]

/-- What a group needs of the layout. -/
def g4Chk (p : Params) (e : Nat) : Bool :=
  slotChk p e 0 && slotChk p e 1 && slotChk p e 2 && slotChk p e 3 && callChk p e

theorem sample4_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {g : Nat}
    (hc : g4Chk p (4 * g) = true) {s : State} (h : IA4 p D σ (4 * g) s) :
    WP isa (sample4 P p g) s (IA4 p D σ (4 * g + 4)) := by
  simp only [g4Chk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨s0, s1⟩, s2⟩, s3⟩, cc⟩ := hc
  unfold sample4
  refine WP.seq (WP.mono (slot_ok (by decide) s0 (j := 0) ⟨h, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun x0 h0 => ?_)
  refine WP.seq (WP.mono (slot_ok (by decide) s1 h0.1) fun x1 h1 => ?_)
  refine WP.seq (WP.mono (slot_ok (by decide) s2 h1.1) fun x2 h2 => ?_)
  refine WP.seq (WP.mono (slot_ok (by decide) s3 h2.1) fun x3 h3 => ?_)
  exact call4_ok hP cc h3.1

/-! ## The matrix -/

/-- `ρ` to `sc o`. -/
theorem copyRho_ok {p : Params} {D : Nat} {σ : State} {o : Nat}
    (hc : copyChk (sgB p) (sgW p) (sc o) (.rbp, 0) 32 = true) (hst : stChk p [(sc o, 32)] = true) (hsk : 32 ≤ p.skLen)
    {s : State} (hs : St p D σ s) :
    WP isa (copy (sc o) (.rbp, 0) 32) s fun s' => St p D σ s' ∧ PPostB D s s' [(sc o, 32)] ∧
      bytesAt s'.mem (pa s' (sc o)) 32 = rhoOf p σ ∧ s'.gpr .r15 = s.gpr .r15 :=
  WP.mono (copy_okB hs.lay hc) fun _ ⟨hP1, hcs1, hb⟩ => ⟨hs.step hP1 hst, hP1,
    by rw [hP1.pa (show Reg.rbx ∈ bases by decide), hb, rhoOf, ← hs.sk, VG.Proof.MlKem.bytesAt_take _ _ hsk], hcs1 _ (by decide)⟩

/-- After `ρ` to `RS` and to the first `j` seeds of `RS4`. -/
structure ICopy (p : Params) (D : Nat) (σ : State) (j : Nat) (s : State) : Prop where
  st : St p D σ s
  rs : bytesAt s.mem (pa s (sc oRS)) 32 = rhoOf p σ
  rs4 : ∀ k < j, bytesAt s.mem (pa s (sc (oRS4 + 34 * k))) 32 = rhoOf p σ
  r15 : s.gpr .r15 = 1

/-- What the copy of `ρ` to seed `j` of `RS4` needs of the layout. -/
def cpChk (p : Params) (j : Nat) : Bool :=
  copyChk (sgB p) (sgW p) (sc (oRS4 + 34 * j)) (.rbp, 0) 32 && stChk p [(sc (oRS4 + 34 * j), 32)] &&
    keepB (sgB p) [(sc (oRS4 + 34 * j), 32)] (sc oRS) 32 &&
    (List.range j).all fun k => keepB (sgB p) [(sc (oRS4 + 34 * j), 32)] (sc (oRS4 + 34 * k)) 32

theorem cpR4_ok {p : Params} {D : Nat} {σ : State} {j : Nat} (hc : cpChk p j = true) (hsk : 32 ≤ p.skLen) {s : State}
    (h : ICopy p D σ j s) : WP isa (cpR4 j) s (ICopy p D σ (j + 1)) := by
  simp only [cpChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hcp, hst⟩, k0⟩, kk⟩ := hc
  refine WP.mono (copyRho_ok hcp hst hsk h.st) fun s1 ⟨S1, hP1, hb, e15⟩ =>
    ⟨S1, (h.st.lay.keepBytes hP1 k0).trans h.rs, fun k hk => ?_, e15.trans h.r15⟩
  rcases (by omega_using [hk] : k < j ∨ k = j) with hk' | rfl
  · exact (h.st.lay.keepBytes hP1 (List.all_eq_true.mp kk k (List.mem_range.mpr hk'))).trans (h.rs4 k hk')
  · exact hb

/-- What `ExpandA` needs of the layout. -/
def aChk (p : Params) : Bool :=
  (List.range (p.k * p.ℓ)).all (eChk p) && copyChk (sgB p) (sgW p) (sc oRS) (.rbp, 0) 32 &&
    stChk p [(sc oRS, 32)] && decide (32 ≤ p.skLen) && (List.range 4).all (cpChk p) &&
    (List.range (p.k * p.ℓ / 4)).all fun g => g4Chk p (4 * g)

theorem aChk_ok {p : Params} (h : Ok3 p) : aChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

theorem ICopy.ia4 {p : Params} {D : Nat} {σ s : State} (h : ICopy p D σ 4 s) : IA4 p D σ 0 s :=
  ⟨⟨h.st, h.rs, .inr h.r15, fun _ => ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩,
    fun h0 => absurd (h0.symm.trans h.r15) (by decide)⟩, h.rs4⟩

theorem expandA_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hc : aChk p = true) {σ s : State}
    (hs : St p D σ s) (h15 : s.gpr .r15 = 1) : WP isa (Impl.MlDsa.X86_64.Sign.expandA P p) s (IA p D σ (p.k * p.ℓ)) := by
  simp only [aChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨he, hcp⟩, hst⟩, hsk⟩, hc4⟩, hg⟩ := hc
  unfold Impl.MlDsa.X86_64.Sign.expandA
  refine WP.seq (WP.mono (copyRho_ok hcp hst hsk hs) fun s1 ⟨S1, _, hb, e15⟩ => ?_)
  have I0 : ICopy p D σ 0 s1 := ⟨S1, hb, fun _ h => absurd h (Nat.not_lt_zero _), e15.trans h15⟩
  refine WP.seq (WP.mono (seqR_ok (f := cpR4) (I := ICopy p D σ) 4 0
    (fun k _ hk s h => cpR4_ok (hc4 k (by omega_using [hk])) hsk h) s1 I0) fun s2 h2 => ?_)
  refine WP.seq (WP.mono (seqR_ok (f := sample4 P p) (I := fun g => IA4 p D σ (4 * g)) (p.k * p.ℓ / 4) 0
    (fun g _ hg' s h => sample4_ok hP (hg g (by omega_using [hg'])) h) s2 h2.ia4) fun s3 h3 => ?_)
  have := seqR_ok (f := sampleE P p) (I := IA p D σ) (p.k * p.ℓ % 4) (4 * (p.k * p.ℓ / 4))
    (fun k h1 hk s h => sampleE_ok hP (he k (by omega_using [hk])) h) s3 (by rw [Nat.zero_add] at h3; exact h3.ia)
  rwa [show 4 * (p.k * p.ℓ / 4) + p.k * p.ℓ % 4 = p.k * p.ℓ by omega_using []] at this

end VG.Proof.MlDsa.X86_64.Sign

end

end

/-! ### `MlDsa.X86_64.Sign.PhaseC`, which this module and modules that import it used -/

section

/-!
# ML-DSA signing on x86-64: the commitment of an iteration

At the head of iteration `t` of the loop (`IL`): what decoding left, `κ = ℓt`
at `KAP`, `814 - t` at `CNT`, and the `t` iterations before rejected (within
`maxBounds`). Then `y[r]` from `ExpandMask(ρ″, κ + r)` and `ŷ[r] = NTT(y[r])`
(`maskR_ok`), `w[i] = NTT⁻¹(∑_j Â[i, j] ŷ[j])` (`rowW_ok`),
`w1Encode(HighBits(w[i]))` at `W1` (`w1R_ok`), and `c̃ = H(μ ‖ w1Encode(w₁),
λ/4)` at `CT` (`commit_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Sign

open VG.Proof.MlDsa.Arith.Representation

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params)

/-- `Â[i, j]`, within `maxBounds`. -/
abbrev Am (σ : State) (i j : Nat) : Poly := aF maxBounds.rejNTT (rhoOf p σ) i j

/-- The slots of `h`, `y`, `ŷ` and `w`. -/
abbrev yBase : Nat := 5 + p.k
abbrev yhBase : Nat := 5 + p.k + p.ℓ
abbrev wBase : Nat := 5 + p.k + 2 * p.ℓ

/-- `y[r]`, `ŷ[r]`, `w[i]` and `c̃` of the iteration with counter `κ`. -/
abbrev Yv (σ : State) (κ r : Nat) : Poly := toRq (yF p (rppOf p σ) κ r)
abbrev YHv (σ : State) (κ r : Nat) : Poly := yhF p (rppOf p σ) κ r
abbrev Wv (σ : State) (κ i : Nat) : Poly := wF p (Am p σ) (rppOf p σ) κ i
abbrev CTv (σ : State) (κ : Nat) : List Byte := ctF p (Am p σ) (muOf σ) (rppOf p σ) κ

/-- The iterations before `t` were rejected, within `maxBounds`. -/
abbrev RejT (σ : State) (t : Nat) : Prop :=
  Rej p (amat p (Am p σ)) ((List.range p.ℓ).map (S1v p σ)) ((List.range p.k).map (S2v p σ))
    ((List.range p.k).map (T0v p σ)) (muOf σ) (rppOf p σ) maxBounds 0 t

end

theorem aVal_ij {p : Params} {σ : State} {i j : Nat} (hj : j < p.ℓ) : aVal p σ (p.ℓ * i + j) = Am p σ i j := by
  have hl : 0 < p.ℓ := by omega_using [hj]
  have e1 : (p.ℓ * i + j) / p.ℓ = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ hl, Nat.div_eq_of_lt hj, Nat.zero_add]
  have e2 : (p.ℓ * i + j) % p.ℓ = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  simp only [aVal, e1, e2]

/-! ## The head of an iteration -/

/-- The head of iteration `t`. -/
structure IL (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  k : IK p D σ s
  kap : s.mem.readW (pa s (sc oKAP)) 64 = BitVec.ofNat 64 (p.ℓ * t)
  cnt : s.mem.readW (pa s (sc oCNT)) 64 = BitVec.ofNat 64 (814 - t)
  t_lt : t < 814
  rej : RejT p σ t

/-- A piece that writes `ws` keeps what decoding left (but `KAP` and `CNT`). -/
def ikChk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  idChk p ws p.ℓ p.k p.k && keepB (sgB p) ws (sc oMS) 64

/-- A piece that writes `ws` keeps `IL`. -/
def ilChk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  ikChk p ws && keepB (sgB p) ws (sc oKAP) 8 && keepB (sgB p) ws (sc oCNT) 8

theorem IK.step {p : Params} {D : Nat} {σ s s' : State} (h : IK p D σ s) {ws : List (Ptr × Nat)}
    (hP : PPostB D s s' ws) (hc : ikChk p ws = true) : IK p D σ s' := by
  simp only [ikChk, Bool.and_eq_true] at hc
  exact ⟨h.d.step hP hc.1, (h.d.im.st.lay.keepBytes hP hc.2).trans h.rpp⟩

theorem IL.step {p : Params} {D : Nat} {σ s s' : State} {t : Nat} (h : IL p D σ t s) {ws : List (Ptr × Nat)}
    (hP : PPostB D s s' ws) (hc : ilChk p ws = true) : IL p D σ t s' := by
  simp only [ilChk, Bool.and_eq_true] at hc
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc
  have L := h.k.d.im.st.lay
  exact ⟨h.k.step hP h1, (L.keepW hP h2).trans h.kap, (L.keepW hP h3).trans h.cnt, h.t_lt, h.rej⟩

theorem IL.st {p : Params} {D : Nat} {σ s : State} {t : Nat} (h : IL p D σ t s) : St p D σ s := h.k.d.im.st

/-! ## `κ + r` -/

theorem setKap_ok (o r : Nat) (hr : r < 2 ^ 31) (s : State)
    (h1 : InRegions (s.rd ++ s.wr) (pa s (sc oKAP)) 8) (h2 : InRegions s.wr (pa s (sc o)) 1)
    (h3 : InRegions s.wr (pa s (sc (o + 1))) 1) :
    WP isa (.block (setKap o r)) s fun s' =>
      s'.mem = (s.mem.writeW (pa s (sc o))
        ((s.mem.readW (pa s (sc oKAP)) 64 + BitVec.ofNat 64 r).setWidth 8)).writeW
        (pa s (sc (o + 1))) (((s.mem.readW (pa s (sc oKAP)) 64 + BitVec.ofNat 64 r) >>> 8).setWidth 8) ∧
        Keep [.rax] s s' := by
  refine WP.keep [.rax] ?_ (by rfl)
  unfold setKap
  xrun [h1, h2, h3, sx_ofNat hr]

theorem integerToBytes_two (x : Nat) : integerToBytes x 2 = [BitVec.ofNat 8 x, BitVec.ofNat 8 (x / 256)] := by
  simp [integerToBytes, List.range_succ]

theorem kappa_bytes {x : Nat} (hx : x < 2 ^ 16) :
    [(BitVec.ofNat 64 x).setWidth 8, (BitVec.ofNat 64 x >>> 8).setWidth 8] = integerToBytes x 2 := by
  rw [integerToBytes_two]
  congr 1
  · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  · congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
    omega

theorem add_one_ne (a : Addr) : a ≠ a + 1 := by
  intro h
  have := congrArg BitVec.toNat h
  have ha := a.isLt
  rw [BitVec.toNat_add] at this
  have e1 : (1 : BitVec 64).toNat = 1 := rfl
  rw [e1] at this
  omega_using [this]

theorem bytes2_write (m : Mem) (a : Addr) (v w : Byte) :
    bytesAt ((m.writeW a v).writeW (a + 1) w) a 2 = [v, w] := by
  show [((m.writeW a v).writeW (a + 1) w) (a + BitVec.ofNat 64 0),
    ((m.writeW a v).writeW (a + 1) w) (a + BitVec.ofNat 64 1)] = _
  have e0 : a + BitVec.ofNat 64 0 = a := BitVec.add_zero a
  have e1 : a + BitVec.ofNat 64 1 = a + 1 := rfl
  rw [e0, e1, VG.Proof.MlKem.writeW8_apply, VG.Proof.MlKem.writeW8_apply, ifn (add_one_ne a), ifp rfl,
    VG.Proof.MlKem.writeW8_apply, ifp rfl]

/-- `κ + r` to `scratch + o`, as the two bytes of `ExpandMask`'s seed. -/
theorem setKap_okB {D : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay D rbs wbs s) {r x : Nat}
    {o : Nat} (hr : r < 2 ^ 31) (hx : x + r < 2 ^ 16) (h1 : inB (rbs ++ wbs) (sc oKAP) 8 = true)
    (h2 : inB wbs (sc o) 2 = true) (hk : s.mem.readW (pa s (sc oKAP)) 64 = BitVec.ofNat 64 x) :
    WP isa (.block (setKap o r)) s fun s' => PPostB D s s' [(sc o, 2)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      bytesAt s'.mem (pa s (sc o)) 2 = integerToBytes (x + r) 2 := by
  have e65 : pa s (sc (o + 1)) = pa s (sc o) + 1 := (pa_sc_add s o 1).symm
  have w2 := L.iW h2
  have c0 : (⟨pa s (sc o), 2⟩ : Region).Contains (pa s (sc o)) 1 := by
    have := contains_offset' (base := pa s (sc o)) (off := 0) (len := 1) (n := 2) (by omega_using []) (by decide)
    rwa [BitVec.add_zero] at this
  have c1 : (⟨pa s (sc o), 2⟩ : Region).Contains (pa s (sc (o + 1))) 1 := by
    rw [e65]; exact contains_offset' (off := 1) (by omega_using []) (by decide)
  have i0 : InRegions s.wr (pa s (sc o)) 1 := by
    have := inRegions_sub (off := 0) (l := 1) w2 (by omega_using []) (by decide)
    rwa [BitVec.add_zero] at this
  have i1 : InRegions s.wr (pa s (sc (o + 1))) 1 := by
    rw [e65]; exact inRegions_sub (off := 1) (l := 1) w2 (by omega_using []) (by decide)
  refine WP.mono (setKap_ok o r hr s (L.iR h1) i0 i1) fun s' ⟨hm, k⟩ => ?_
  have hf : Frame [⟨pa s (sc o), 2⟩] s.mem s'.mem := by
    rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c1
  refine ⟨(postB_of_keep (D := D) k (by decide) hf).1, (postB_of_keep (D := D) k (by decide) hf).2, ?_⟩
  rw [hm, e65, bytes2_write, hk, ofNat64_add, kappa_bytes hx]

/-- `κ + r` to `MS + 64`, as the two bytes of `ExpandMask`'s seed. -/
theorem setKappa_okB {D : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay D rbs wbs s) {r x : Nat}
    (hr : r < 2 ^ 31) (hx : x + r < 2 ^ 16) (h1 : inB (rbs ++ wbs) (sc oKAP) 8 = true)
    (h2 : inB wbs (sc (oMS + 64)) 2 = true) (hk : s.mem.readW (pa s (sc oKAP)) 64 = BitVec.ofNat 64 x) :
    WP isa (.block (setKappa r)) s fun s' => PPostB D s s' [(sc (oMS + 64), 2)] ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      bytesAt s'.mem (pa s (sc (oMS + 64))) 2 = integerToBytes (x + r) 2 :=
  setKap_okB L hr hx h1 h2 hk

/-! ## `y` and `ŷ` -/

/-- Iteration `t`, with the first `r` polynomials of `y` and `ŷ`. -/
structure ICm (p : Params) (D : Nat) (σ : State) (t r : Nat) (s : State) : Prop where
  l : IL p D σ t s
  y : Fam s (yBase p) r (Yv p σ (p.ℓ * t))
  yh : Fam s (yhBase p) r (YHv p σ (p.ℓ * t))

def icmChk (p : Params) (ws : List (Ptr × Nat)) (r : Nat) : Bool :=
  ilChk p ws && famChk (sgB p) ws (yBase p) r && famChk (sgB p) ws (yhBase p) r

theorem ICm.step {p : Params} {D : Nat} {σ s s' : State} {t r : Nat} (h : ICm p D σ t r s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) (hc : icmChk p ws r = true) : ICm p D σ t r s' := by
  simp only [icmChk, Bool.and_eq_true] at hc
  have L := h.l.st.lay
  exact ⟨h.l.step hP hc.1.1, Fam.keep L hP hc.1.2 h.y, Fam.keep L hP hc.2 h.yh⟩

/-- What `y[r]` and `ŷ[r]` need of the layout. -/
def mChk (p : Params) (r : Nat) : Bool :=
  let y := pS (yBase p + r)
  let yh := pS (yhBase p + r)
  let w1 : List (Ptr × Nat) := [(sc (oMS + 64), 2)]
  let w2 : List (Ptr × Nat) := [(y, 1024), (sc oPS, 2048)]
  let w3 : List (Ptr × Nat) := [(yh, 1024)]
  let w4 : List (Ptr × Nat) := [(yh, 1024), (sc oPS, 1024)]
  icmChk p w1 r && inB (sgB p) (sc oKAP) 8 && inB (sgW p) (sc (oMS + 64)) 2 && maskChk (sgB p) (sgW p) y &&
    icmChk p w2 r && copyChk (sgB p) (sgW p) yh y 1024 && icmChk p w3 r && famChk (sgB p) w3 (yBase p) (r + 1) &&
    ipChk (sgB p) (sgW p) yh && icmChk p w4 r && famChk (sgB p) w4 (yBase p) (r + 1) &&
    decide (p.ℓ * 813 + r < 2 ^ 16) && decide (r < 2 ^ 31) && decide (p.γ₁ = 2 ^ 17 ∨ p.γ₁ = 2 ^ 19)

theorem maskR_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {t r : Nat}
    (hc : mChk p r = true) {s : State} (h : ICm p D σ t r s) : WP isa (maskR P p r) s (ICm p D σ t (r + 1)) := by
  simp only [mChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, k1⟩, w1⟩, cm⟩, c2⟩, cc⟩, c3⟩, f3⟩, ci⟩, c4⟩, f4⟩, hx⟩, hr⟩, hγ⟩ := hc
  have ht := h.l.t_lt
  unfold maskR
  have hx' : p.ℓ * t + r < 2 ^ 16 := by
    have := Nat.mul_le_mul_left p.ℓ (show t ≤ 813 by omega_using [ht]); omega_using [hx, this]
  refine WP.seq (WP.mono (setKappa_okB h.l.st.lay hr hx' k1 w1 h.l.kap) fun s1 ⟨hP1, _, hb1⟩ => ?_)
  have I1 := h.step hP1 c1
  have hms : bytesAt s1.mem (pa s1 (sc oMS)) 66 = rppOf p σ ++ integerToBytes (p.ℓ * t + r) 2 := by
    rw [VG.Proof.MlKem.bytesAt_add _ _ 64 2, I1.l.k.rpp, pa_sc_add, hP1.pa (by decide), hb1]
  refine WP.seq (WP.mono (maskAt_ok hP I1.l.st.lay hγ cm) fun s2 ⟨hP2, _, hq2⟩ => ?_)
  rw [hms] at hq2
  have I2 := I1.step hP2 c2
  have hy2 : Fam s2 (yBase p) (r + 1) (Yv p σ (p.ℓ * t)) :=
    Fam.snoc I2.y (by
      show PolyIs s2.mem (pa s2 (pS (yBase p + r))) _
      rw [hP2.pa (pS_bases _)]; exact hq2)
  refine WP.seq (WP.mono (copy_okB I2.l.st.lay cc) fun s3 ⟨hP3, _, hb3⟩ => ?_)
  have I3 := I2.step hP3 c3
  have hyh3 : Pl s3 (yhBase p + r) (Yv p σ (p.ℓ * t) r) := by
    show PolyIs _ _ _
    rw [hP3.pa (pS_bases _)]
    exact polyIs_of_bytes hb3 (hy2 r (by omega_using []))
  refine WP.mono (ipAt_ok (t := ntt) hP.ntt I3.l.st.lay ci hyh3.1) fun s4 ⟨hP4, _, hq4⟩ => ?_
  have I4 := I3.step hP4 c4
  refine ⟨I4.l, Fam.keep I3.l.st.lay hP4 f4 (Fam.keep I2.l.st.lay hP3 f3 hy2), Fam.snoc I4.yh ?_⟩
  show PolyIs _ _ _
  rw [hP4.pa (pS_bases _), hyh3.2] at *
  exact hq4

/-! ## `y` and `ŷ`, four at a time -/

/-- Iteration `t`, with the first `ry` polynomials of `y` and the first `r` of `ŷ`. -/
structure ICy (p : Params) (D : Nat) (σ : State) (t ry r : Nat) (s : State) : Prop where
  l : IL p D σ t s
  y : Fam s (yBase p) ry (Yv p σ (p.ℓ * t))
  yh : Fam s (yhBase p) r (YHv p σ (p.ℓ * t))

def icyChk (p : Params) (ws : List (Ptr × Nat)) (ry r : Nat) : Bool :=
  ilChk p ws && famChk (sgB p) ws (yBase p) ry && famChk (sgB p) ws (yhBase p) r

theorem ICy.step {p : Params} {D : Nat} {σ s s' : State} {t ry r : Nat} (h : ICy p D σ t ry r s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) (hc : icyChk p ws ry r = true) : ICy p D σ t ry r s' := by
  simp only [icyChk, Bool.and_eq_true] at hc
  have L := h.l.st.lay
  exact ⟨h.l.step hP hc.1.1, Fam.keep L hP hc.1.2 h.y, Fam.keep L hP hc.2 h.yh⟩

/-- What `ŷ[r]` needs of the layout, with `ry` polynomials of `y`. -/
def yhChk (p : Params) (ry r : Nat) : Bool :=
  let y := pS (yBase p + r)
  let yh := pS (yhBase p + r)
  copyChk (sgB p) (sgW p) yh y 1024 && icyChk p [(yh, 1024)] ry r && ipChk (sgB p) (sgW p) yh &&
    icyChk p [(yh, 1024), (sc oPS, 1024)] ry r

theorem yhR_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {t ry r : Nat}
    (hc : yhChk p ry r = true) (hr : r < ry) {s : State} (h : ICy p D σ t ry r s) :
    WP isa (yhR P p r) s (ICy p D σ t ry (r + 1)) := by
  simp only [yhChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨cc, c3⟩, ci⟩, c4⟩ := hc
  unfold yhR
  refine WP.seq (WP.mono (copy_okB h.l.st.lay cc) fun s3 ⟨hP3, _, hb3⟩ => ?_)
  have I3 := h.step hP3 c3
  have hyh3 : Pl s3 (yhBase p + r) (Yv p σ (p.ℓ * t) r) := by
    show PolyIs _ _ _
    rw [hP3.pa (pS_bases _)]
    exact polyIs_of_bytes hb3 (h.y r hr)
  refine WP.mono (ipAt_ok (t := ntt) hP.ntt I3.l.st.lay ci hyh3.1) fun s4 ⟨hP4, _, hq4⟩ => ?_
  have I4 := I3.step hP4 c4
  refine ⟨I4.l, I4.y, Fam.snoc I4.yh ?_⟩
  show PolyIs _ _ _
  rw [hP4.pa (pS_bases _), hyh3.2] at *
  exact hq4

/-- Iteration `t`, with the first `4g` polynomials of `y` and `ŷ`, and the first `k` seeds of `MS4`. -/
structure SD (p : Params) (D : Nat) (σ : State) (t g k : Nat) (s : State) : Prop where
  m : ICm p D σ t (4 * g) s
  sd : ∀ j < k, bytesAt s.mem (pa s (sc (oMS4 + 66 * j))) 66 =
    rppOf p σ ++ integerToBytes (p.ℓ * t + (4 * g + j)) 2

/-- What seed `k` of `MS4` needs of the layout. -/
def ms4Chk (p : Params) (g k : Nat) : Bool :=
  let w1 : List (Ptr × Nat) := [(sc (oMS4 + 66 * k), 64)]
  let w2 : List (Ptr × Nat) := [(sc (oMS4 + 66 * k + 64), 2)]
  copyChk (sgB p) (sgW p) (sc (oMS4 + 66 * k)) (sc oMS) 64 && icmChk p w1 (4 * g) && icmChk p w2 (4 * g) &&
    inB (sgB p) (sc oKAP) 8 && inB (sgW p) (sc (oMS4 + 66 * k + 64)) 2 &&
    keepB (sgB p) w2 (sc (oMS4 + 66 * k)) 64 &&
    (List.range k).all (fun j => keepB (sgB p) w1 (sc (oMS4 + 66 * j)) 66 &&
      keepB (sgB p) w2 (sc (oMS4 + 66 * j)) 66) &&
    decide (p.ℓ * 813 + (4 * g + k) < 2 ^ 16) && decide (4 * g + k < 2 ^ 31)

theorem ms4_ok {p : Params} {D : Nat} {σ : State} {t g k : Nat} (hc : ms4Chk p g k = true) {s : State}
    (h : SD p D σ t g k s) : WP isa (cpM4 g k) s (SD p D σ t g (k + 1)) := by
  simp only [ms4Chk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨cc, c1⟩, c2⟩, k1⟩, w2⟩, k12⟩, kd⟩, hx⟩, hr⟩ := hc
  have ht := h.m.l.t_lt
  have hx' : p.ℓ * t + (4 * g + k) < 2 ^ 16 := by
    have := Nat.mul_le_mul_left p.ℓ (show t ≤ 813 by omega_using [ht]); omega_using [hx, this]
  unfold cpM4
  refine WP.seq (WP.mono (copy_okB h.m.l.st.lay cc) fun s1 ⟨hP1, _, hb1⟩ => ?_)
  have I1 := h.m.step hP1 c1
  refine WP.mono (setKap_okB I1.l.st.lay hr hx' k1 w2 I1.l.kap) fun s2 ⟨hP2, _, hb2⟩ => ?_
  have I2 := I1.step hP2 c2
  refine ⟨I2, fun j hj => ?_⟩
  rcases (by omega_using [hj] : j < k ∨ j = k) with hj' | rfl
  · have kk := List.all_eq_true.mp kd j (List.mem_range.mpr hj')
    simp only [Bool.and_eq_true] at kk
    rw [I1.l.st.lay.keepBytes hP2 kk.2, h.m.l.st.lay.keepBytes hP1 kk.1]
    exact h.sd j hj'
  · rw [VG.Proof.MlKem.bytesAt_add _ _ 64 2, pa_sc_add, I1.l.st.lay.keepBytes hP2 k12, hP1.pa (sc_bases _), hb1,
      h.m.l.k.rpp, hP2.pa (sc_bases _), hb2]

/-- What `y[4g], …, y[4g + 3]` and their `ŷ` need of the layout. -/
def m4Chk (p : Params) (g : Nat) : Bool :=
  (List.range 4).all (ms4Chk p g) && mask4Chk (sgB p) (sgW p) (yP p (4 * g)) (r4P p) &&
    icmChk p [(yP p (4 * g), 4096), (r4P p, 8192)] (4 * g) &&
    (List.range 4).all (fun r => yhChk p (4 * g + 4) (4 * g + r)) && decide (p.γ₁ = 2 ^ 17 ∨ p.γ₁ = 2 ^ 19)

theorem m4Chk_spec {p : Params} {g : Nat} (hc : m4Chk p g = true) :
    (∀ k < 4, ms4Chk p g k = true) ∧ mask4Chk (sgB p) (sgW p) (yP p (4 * g)) (r4P p) = true ∧
      icmChk p [(yP p (4 * g), 4096), (r4P p, 8192)] (4 * g) = true ∧
      (∀ r, 4 * g ≤ r → r < 4 * g + 4 → yhChk p (4 * g + 4) r = true) ∧ (p.γ₁ = 2 ^ 17 ∨ p.γ₁ = 2 ^ 19) := by
  simp only [m4Chk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hcp, cm⟩, c2⟩, hyh⟩, hγ⟩ := hc
  refine ⟨hcp, cm, c2, fun r h1 h2 => ?_, hγ⟩
  have := hyh (r - 4 * g) (by omega_using [h2])
  rwa [show 4 * g + (r - 4 * g) = r by omega_using [h1]] at this

/-- The call of `vg_mldsa_expand_mask_poly4`, from the four seeds of `MS4`. -/
theorem m4call_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {t g : Nat}
    (hγ : p.γ₁ = 2 ^ 17 ∨ p.γ₁ = 2 ^ 19) (cm : mask4Chk (sgB p) (sgW p) (yP p (4 * g)) (r4P p) = true)
    (c2 : icmChk p [(yP p (4 * g), 4096), (r4P p, 8192)] (4 * g) = true) {s : State} (h : SD p D σ t g 4 s) :
    WP isa (mask4At P p.γ₁ (yP p (4 * g)) (r4P p)) s (ICy p D σ t (4 * g + 4) (4 * g)) := by
  refine WP.mono (mask4Call_ok hP h.m.l.st.lay hγ cm) fun s2 ⟨hP2, _, hq2⟩ => ?_
  have I2 := h.m.step hP2 c2
  refine ⟨I2.l, fun j hj => ?_, I2.yh⟩
  rcases (by omega_using [] : j < 4 * g ∨ 4 * g ≤ j) with hj' | hj'
  · exact I2.y j hj'
  · obtain ⟨k, hk, rfl⟩ : ∃ k, k < 4 ∧ j = 4 * g + k := ⟨j - 4 * g, by omega_using [hj], by omega_using [hj']⟩
    have hq := hq2 k hk
    rw [seed66, pa_sc_add, h.sd k hk] at hq
    show PolyIs s2.mem (pa s2 (pS (yBase p + (4 * g + k)))) _
    rw [hP2.pa (pS_bases _), ← Nat.add_assoc, ← pa_poly4]
    exact hq

theorem mask4_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {t g : Nat}
    (hc : m4Chk p g = true) {s : State} (h : ICm p D σ t (4 * g) s) :
    WP isa (mask4 P p g) s (ICm p D σ t (4 * (g + 1))) := by
  obtain ⟨hcp, cm, c2, hyh, hγ⟩ := m4Chk_spec hc
  unfold mask4
  refine WP.seq (WP.mono (seqR_ok (I := fun k => SD p D σ t g k) 4 0
    (fun k _ hk s hs => ms4_ok (hcp k (by omega_using [hk])) hs) s ⟨h, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s1 hs1 => ?_)
  rw [Nat.zero_add] at hs1
  refine WP.seq (WP.mono (m4call_ok hP hγ cm c2 hs1) fun s2 hs2 => ?_)
  exact WP.mono (seqR_ok (I := fun r => ICy p D σ t (4 * g + 4) r) 4 (4 * g)
    (fun r h1 hr s hs => yhR_ok hP (hyh r h1 hr) (by omega_using [hr]) hs) s2 hs2)
    fun s3 hs3 => ⟨hs3.l, hs3.y, hs3.yh⟩

/-! ## The last three polynomials of `y`, four at a time -/

/-- Iteration `t`, with the first `r` polynomials of `y` and `ŷ`, and in the
temporaries those of the last three of `y` from `r` on. -/
structure ICT (p : Params) (D : Nat) (σ : State) (t r : Nat) (s : State) : Prop where
  m : ICm p D σ t r s
  tmp : ∀ k < 3, r ≤ 4 * (p.ℓ / 4) + k → Pl s (1 + k) (Yv p σ (p.ℓ * t) (4 * (p.ℓ / 4) + k))

/-- The temporaries lie apart from `ws`. -/
def tmpChk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  (List.range 3).all fun k => keepB (sgB p) ws (pS (1 + k)) 1024

theorem tmp_keep {p : Params} {D : Nat} {σ : State} {t r : Nat} {s s' : State} (L : Lay D (sgR p) (sgW p) s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) (hc : tmpChk p ws = true)
    (h : ∀ k < 3, r ≤ 4 * (p.ℓ / 4) + k → Pl s (1 + k) (Yv p σ (p.ℓ * t) (4 * (p.ℓ / 4) + k))) :
    ∀ k < 3, r ≤ 4 * (p.ℓ / 4) + k → Pl s' (1 + k) (Yv p σ (p.ℓ * t) (4 * (p.ℓ / 4) + k)) := fun k hk hr =>
  L.keepPoly hP (List.all_eq_true.mp hc k (List.mem_range.mpr hk)) (h k hk hr)

/-- What `y[r]` from its temporary, and `ŷ[r]`, need of the layout. -/
def tChk (p : Params) (r : Nat) : Bool :=
  let y := pS (yBase p + r)
  let yh := pS (yhBase p + r)
  let w1 : List (Ptr × Nat) := [(y, 1024)]
  let w3 : List (Ptr × Nat) := [(yh, 1024)]
  let w4 : List (Ptr × Nat) := [(yh, 1024), (sc oPS, 1024)]
  copyChk (sgB p) (sgW p) y (pS (1 + (r - 4 * (p.ℓ / 4)))) 1024 && icmChk p w1 r && tmpChk p w1 &&
    copyChk (sgB p) (sgW p) yh y 1024 && icmChk p w3 r && famChk (sgB p) w3 (yBase p) (r + 1) && tmpChk p w3 &&
    ipChk (sgB p) (sgW p) yh && icmChk p w4 r && famChk (sgB p) w4 (yBase p) (r + 1) && tmpChk p w4

theorem tailR_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {t r : Nat}
    (hc : tChk p r = true) (h1 : 4 * (p.ℓ / 4) ≤ r) (h2 : r < 4 * (p.ℓ / 4) + 3) {s : State} (h : ICT p D σ t r s) :
    WP isa (tailR P p r) s (ICT p D σ t (r + 1)) := by
  simp only [tChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c0, c1⟩, k1⟩, cc⟩, c3⟩, f3⟩, k3⟩, ci⟩, c4⟩, f4⟩, k4⟩ := hc
  unfold tailR yhR
  refine WP.seq (WP.mono (copy_okB h.m.l.st.lay c0) fun s1 ⟨hP1, _, hb1⟩ => ?_)
  have I1 := h.m.step hP1 c1
  have T1 := tmp_keep h.m.l.st.lay hP1 k1 h.tmp
  have hy1 : Fam s1 (yBase p) (r + 1) (Yv p σ (p.ℓ * t)) := by
    refine Fam.snoc I1.y ?_
    show PolyIs s1.mem (pa s1 (pS (yBase p + r))) _
    rw [hP1.pa (pS_bases _)]
    have := h.tmp (r - 4 * (p.ℓ / 4)) (by omega_using [h2]) (by omega_using [])
    rw [show 4 * (p.ℓ / 4) + (r - 4 * (p.ℓ / 4)) = r by omega_using [h1]] at this
    exact polyIs_of_bytes hb1 this
  refine WP.seq (WP.mono (copy_okB I1.l.st.lay cc) fun s3 ⟨hP3, _, hb3⟩ => ?_)
  have I3 := I1.step hP3 c3
  have T3 := tmp_keep I1.l.st.lay hP3 k3 T1
  have hyh3 : Pl s3 (yhBase p + r) (Yv p σ (p.ℓ * t) r) := by
    show PolyIs _ _ _
    rw [hP3.pa (pS_bases _)]
    exact polyIs_of_bytes hb3 (hy1 r (by omega_using []))
  refine WP.mono (ipAt_ok (t := ntt) hP.ntt I3.l.st.lay ci hyh3.1) fun s4 ⟨hP4, _, hq4⟩ => ?_
  have I4 := I3.step hP4 c4
  refine ⟨⟨I4.l, Fam.keep I3.l.st.lay hP4 f4 (Fam.keep I1.l.st.lay hP3 f3 hy1), Fam.snoc I4.yh ?_⟩,
    fun k hk hr => tmp_keep I3.l.st.lay hP4 k4 T3 k hk (by omega_using [hr])⟩
  show PolyIs _ _ _
  rw [hP4.pa (pS_bases _), hyh3.2] at *
  exact hq4

/-- What the last three polynomials of `y`, four at a time, need of the layout. -/
def tailChk (p : Params) : Bool :=
  (List.range 4).all (ms4Chk p (p.ℓ / 4)) && mask4Chk (sgB p) (sgW p) t1P (r4P p) &&
    icmChk p [(t1P, 4096), (r4P p, 8192)] (4 * (p.ℓ / 4)) &&
    (List.range 3).all (fun k => tChk p (4 * (p.ℓ / 4) + k)) && decide (p.γ₁ = 2 ^ 17 ∨ p.γ₁ = 2 ^ 19)

/-- The four-at-a-time call of `maskTail`, to the temporaries. -/
theorem maskTailCall_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {t : Nat}
    (hc : tailChk p = true) {s : State} (h : SD p D σ t (p.ℓ / 4) 4 s) :
    WP isa (mask4At P p.γ₁ t1P (r4P p)) s (ICT p D σ t (4 * (p.ℓ / 4))) := by
  simp only [tailChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨_, cm⟩, c2⟩, _⟩, hγ⟩ := hc
  refine WP.mono (mask4Call_ok hP h.m.l.st.lay hγ cm) fun s2 ⟨hP2, _, hq2⟩ => ?_
  refine ⟨h.m.step hP2 c2, fun k hk _ => ?_⟩
  have hq := hq2 k (by omega_using [hk])
  rw [seed66, pa_sc_add, h.sd k (by omega_using [hk])] at hq
  show PolyIs s2.mem (pa s2 (pS (1 + k))) _
  rw [hP2.pa (pS_bases _), ← pa_poly4]
  exact hq

theorem maskTail_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {t : Nat}
    (hl : p.ℓ % 4 = 3) (hc : tailChk p = true) {s : State} (h : ICm p D σ t (4 * (p.ℓ / 4)) s) :
    WP isa (maskTail P p) s (ICm p D σ t p.ℓ) := by
  have hc' := hc
  simp only [tailChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hcp, _⟩, _⟩, ht⟩, _⟩ := hc
  unfold maskTail
  refine WP.seq (WP.mono (seqR_ok (I := fun k => SD p D σ t (p.ℓ / 4) k) 4 0
    (fun k _ hk s hs => ms4_ok (hcp k (by omega_using [hk])) hs) s ⟨h, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s1 hs1 => ?_)
  rw [Nat.zero_add] at hs1
  refine WP.seq (WP.mono (maskTailCall_ok hP hc' hs1) fun s2 T2 => ?_)
  have htr : ∀ r, 4 * (p.ℓ / 4) ≤ r → r < 4 * (p.ℓ / 4) + 3 → tChk p r = true := fun r h1 h2 => by
    have := ht (r - 4 * (p.ℓ / 4)) (by omega_using [h2])
    rwa [show 4 * (p.ℓ / 4) + (r - 4 * (p.ℓ / 4)) = r by omega_using [h1]] at this
  refine WP.mono (seqR_ok (I := fun r => ICT p D σ t r) 3 (4 * (p.ℓ / 4))
    (fun r h1 hr s hs => tailR_ok hP (htr r h1 hr) h1 hr hs) s2 T2) fun s3 hs3 => ?_
  rw [show 4 * (p.ℓ / 4) + 3 = p.ℓ by omega_using [hl]] at hs3
  exact hs3.m

/-- What the polynomials of `y` after the groups of four need of the layout. -/
def restChk (p : Params) : Bool := bif p.ℓ % 4 == 3 then tailChk p else true

theorem maskRest_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {t : Nat}
    (hc : restChk p = true) (hm : ∀ r < p.ℓ, mChk p r = true) {s : State} (h : ICm p D σ t (4 * (p.ℓ / 4)) s) :
    WP isa (maskRest P p) s (ICm p D σ t p.ℓ) := by
  unfold maskRest
  unfold restChk at hc
  cases e : p.ℓ % 4 == 3
  · rw [Bool.cond_false]
    refine WP.mono (seqR_ok (I := fun r => ICm p D σ t r) (p.ℓ % 4) (4 * (p.ℓ / 4))
      (fun r _ hr s hs => maskR_ok hP (hm r (by omega_using [hr])) hs) s h) fun s1 hs1 => ?_
    rwa [Nat.div_add_mod] at hs1
  · rw [Bool.cond_true]
    rw [e, Bool.cond_true] at hc
    exact maskTail_ok hP (beq_iff_eq.mp e) hc h

/-! ## `w` -/

/-- Iteration `t`, with `y`, `ŷ`, and the first `i` polynomials of `w`. -/
structure ICw (p : Params) (D : Nat) (σ : State) (t i : Nat) (s : State) : Prop where
  l : IL p D σ t s
  y : Fam s (yBase p) p.ℓ (Yv p σ (p.ℓ * t))
  yh : Fam s (yhBase p) p.ℓ (YHv p σ (p.ℓ * t))
  w : Fam s (wBase p) i (Wv p σ (p.ℓ * t))

def icwChk (p : Params) (ws : List (Ptr × Nat)) (i : Nat) : Bool :=
  icmChk p ws p.ℓ && famChk (sgB p) ws (wBase p) i

theorem ICw.step {p : Params} {D : Nat} {σ s s' : State} {t i : Nat} (h : ICw p D σ t i s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) (hc : icwChk p ws i = true) : ICw p D σ t i s' := by
  simp only [icwChk, Bool.and_eq_true] at hc
  have I : ICm p D σ t p.ℓ s' := (ICm.mk h.l h.y h.yh).step hP hc.1
  exact ⟨I.l, I.y, I.yh, Fam.keep h.l.st.lay hP hc.2 h.w⟩

theorem aP_ij (p : Params) (i j : Nat) : aP p i j = pS (aBase p + (p.ℓ * i + j)) := by
  show pS (5 + 4 * p.k + 3 * p.ℓ + p.ℓ * i + j) = _
  rw [Nat.add_assoc (5 + 4 * p.k + 3 * p.ℓ)]

theorem famP_aP (p : Params) (i j : Nat) : famP (aP p i 0) j = aP p i j := by
  simp only [famP, aP, pS, sc, oP, Prod.mk.injEq, true_and]; omega_using []

theorem famP_yhP (p : Params) (j : Nat) : famP (yhP p 0) j = yhP p j := by
  simp only [famP, yhP, pS, sc, oP, Prod.mk.injEq, true_and]; omega_using []

/-- What `w[i]` needs of the layout. -/
def wChk (p : Params) (i : Nat) : Bool :=
  let w := pS (wBase p + i)
  dotChk (sgB p) (sgW p) w (aP p i 0) (yhP p 0) p.ℓ && icwChk p [(w, 1024), (sc oPS, 1024)] i &&
    decide (p.ℓ = 4 ∨ p.ℓ = 5 ∨ p.ℓ = 7)

/-- `Â[i, j]`, reduced, for `j < ℓ`. -/
theorem rowA {p : Params} {D : Nat} {σ : State} {t i : Nat} (hi : i < p.k) {s : State} (I : ICw p D σ t i s)
    {j : Nat} (hj : j < p.ℓ) : PolyIs s.mem (pa s (aP p i j)) (Am p σ i j) := by
  have := I.l.k.d.im.A (p.ℓ * i + j) (by
    have := Nat.mul_le_mul_left p.ℓ (show i + 1 ≤ p.k from hi)
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm p.ℓ p.k] at this; omega_using [hj, this])
  rw [aVal_ij hj] at this
  rw [aP_ij]; exact this

theorem rowW_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {t i : Nat}
    (hc : wChk p i = true) (hi : i < p.k) {s : State} (h : ICw p D σ t i s) :
    WP isa (rowW P p i) s (ICw p D σ t (i + 1)) := by
  simp only [wChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨cd, c2⟩, hl⟩ := hc
  unfold rowW
  refine WP.mono (dotAt_ok (hP.dotInv p.ℓ hl) h.l.st.lay cd
    (fun j hj => by rw [famP_aP]; exact (rowA hi h hj).1) (fun j hj => by rw [famP_yhP]; exact (h.yh j hj).1))
    fun s3 ⟨hP3, _, hq3⟩ => ?_
  have I3 := h.step hP3 c2
  refine ⟨I3.l, I3.y, I3.yh, Fam.snoc I3.w ?_⟩
  show PolyIs _ _ _
  rw [hP3.pa (pS_bases _)]
  rw [VG.Proof.MlDsa.Arith.dotNTT_congr (fun j hj => by rw [famP_aP, (rowA hi h hj).2])
    (fun j hj => by rw [famP_yhP, (h.yh j hj).2])] at hq3
  exact hq3

/-! ## `w₁` and `c̃` -/

/-- The encodings of the first `i` polynomials of `w₁`. -/
abbrev w1Enc (p : Params) (σ : State) (κ i : Nat) : List Byte :=
  (List.range i).flatMap fun j => simpleBitPack (w1F p (Am p σ) (rppOf p σ) κ j) (w1Max p)

/-- Iteration `t`, with `y`, `ŷ`, `w`, and the encodings of the first `i` polynomials of `w₁` at `W1`. -/
structure ICh (p : Params) (D : Nat) (σ : State) (t i : Nat) (s : State) : Prop where
  c : ICw p D σ t p.k s
  w1 : bytesAt s.mem (pa s (sc oW1)) (w1Len p * i) = w1Enc p σ (p.ℓ * t) i

/-- What `w1Encode(w₁[i])` needs of the layout. -/
def hChk (p : Params) (i : Nat) : Bool :=
  let w := pS (wBase p + i)
  let o := sc (oW1 + w1Len p * i)
  rwChk (sgB p) (sgW p) w 1024 t1P 1024 && rwChk (sgB p) (sgW p) t1P 1024 o (w1Len p) &&
    icwChk p [(t1P, 1024)] p.k && icwChk p [(o, w1Len p)] p.k && keepB (sgB p) [(t1P, 1024)] (sc oW1) (w1Len p * i) &&
    keepB (sgB p) [(o, w1Len p)] (sc oW1) (w1Len p * i) && decide (w1Max p ∈ simpleBitPackBounds) &&
    decide (p.γ₂ ∈ gamma2s)

theorem natPolyIs_coeff {m : Mem} {a : Addr} {f : Vector Nat n} (h : NatPolyIs m a f) {j : Nat} (hj : j < 256) :
    (coeffAt m a j).toNat = f[j] := by
  have := congrArg (·[j]) h
  simp only [natPolyAt, Vector.getElem_ofFn] at this
  exact this

theorem w1R_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {t i : Nat}
    (hc : hChk p i = true) (hi : i < p.k) {s : State} (h : ICh p D σ t i s) :
    WP isa (w1R P p i) s (ICh p D σ t (i + 1)) := by
  simp only [hChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, k1⟩, k2⟩, e1⟩, e2⟩, hb⟩, hγ⟩ := hc
  unfold w1R
  refine WP.seq (WP.mono (highBitsAt_ok hP h.c.l.st.lay hγ c1 (h.c.w i hi).1) fun s1 ⟨hP1, _, hq1⟩ => ?_)
  have I1 := h.c.step hP1 k1
  rw [(h.c.w i hi).2] at hq1
  refine WP.mono (sbpAt_ok hP I1.l.st.lay hb rfl c2 fun j hj => ?_) fun s2 ⟨hP2, _, hq2⟩ => ?_
  · rw [hP1.pa (by decide), natPolyIs_coeff hq1 hj]
    simp only [Vector.getElem_map]
    exact highBits_le hγ _
  have I2 := I1.step hP2 k2
  refine ⟨I2, ?_⟩
  have b1 : bytesAt s2.mem (pa s2 (sc oW1)) (w1Len p * i) = w1Enc p σ (p.ℓ * t) i := by
    rw [I1.l.st.lay.keepBytes hP2 e2, h.c.l.st.lay.keepBytes hP1 e1, h.w1]
  have b2 : bytesAt s2.mem (pa s2 (sc (oW1 + w1Len p * i))) (w1Len p) =
      simpleBitPack (w1F p (Am p σ) (rppOf p σ) (p.ℓ * t) i) (w1Max p) := by
    rw [hP2.pa (sc_bases _), hq2, hP1.pa (by decide), show natPolyAt s1.mem (pa s t1P) = _ from hq1]
    rfl
  rw [Nat.mul_succ, VG.Proof.MlKem.bytesAt_add, pa_sc_add, b1, b2, w1Enc, w1Enc, List.range_succ,
    List.flatMap_append, List.flatMap_singleton]

/-- The commitment of iteration `t`: `y`, `ŷ`, `w`, and `c̃` at `CT`. -/
structure IC (p : Params) (D : Nat) (σ : State) (t : Nat) (s : State) : Prop where
  c : ICw p D σ t p.k s
  ct : bytesAt s.mem (pa s (sc oCT)) (cLen p) = CTv p σ (p.ℓ * t)

/-- What the commitment needs of the layout. -/
def cChk (p : Params) : Bool :=
  (List.range (p.ℓ / 4)).all (m4Chk p) && (List.range p.ℓ).all (mChk p) && restChk p && (List.range p.k).all (wChk p) && (List.range p.k).all (hChk p) &&
    shakeChk (sgB p) (sgW p) [((.r12, 0), 64), (sc oW1, p.k * w1Len p)] (sc oCT) (cLen p) &&
    icwChk p [(sc 0, 200), (sc 200, 640), (sc oCT, cLen p)] p.k

theorem cChk_ok {p : Params} (h : Ok3 p) : cChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

theorem commit_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hc : cChk p = true) {σ : State} {t : Nat}
    {s : State} (h : IL p D σ t s) : WP isa (commit P p) s (IC p D σ t) := by
  simp only [cChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨hm4, hm⟩, hrest⟩, hw⟩, hh⟩, hs⟩, hk⟩ := hc
  unfold commit
  refine WP.seq (WP.mono (seqR_ok (I := fun g => ICm p D σ t (4 * g)) (p.ℓ / 4) 0
    (fun g _ hg s hs => mask4_ok hP (hm4 g (by omega_using [hg])) hs) s
    ⟨h, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s0 hs0 => ?_)
  rw [Nat.zero_add] at hs0
  refine WP.seq (WP.mono (maskRest_ok hP hrest hm hs0) fun s1 hs1 => ?_)
  refine WP.seq (WP.mono (seqR_ok (I := fun i => ICw p D σ t i) p.k 0
    (fun i _ hi s hs => rowW_ok hP (hw i (by omega_using [hi])) (by omega_using [hi]) hs) s1
    ⟨hs1.l, hs1.y, hs1.yh, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s2 hs2 => ?_)
  rw [Nat.zero_add] at hs2
  refine WP.seq (WP.mono (seqR_ok (I := fun i => ICh p D σ t i) p.k 0
    (fun i _ hi s hs => w1R_ok hP (hh i (by omega_using [hi])) (by omega_using [hi]) hs) s2
    ⟨hs2, by simp [w1Enc]; rfl⟩) fun s3 hs3 => ?_)
  rw [Nat.zero_add] at hs3
  refine WP.mono (shake_ok (sgB_bases p) hP.hD hs hs3.c.l.st.lay) fun s4 ⟨hP4, _, hb⟩ =>
    ⟨hs3.c.step hP4 hk, ?_⟩
  rw [hP4.pa (by decide), hb]
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [Nat.mul_comm p.k, hs3.w1, hs3.c.l.st.mu]
  simp only [CTv, ctF, w1Encode, List.flatMap_map]

end VG.Proof.MlDsa.X86_64.Sign

end

end

/-!
# ML-DSA signing on x86-64: the commitment leaks only the pointers

Each piece of the commitment leaks only its pointers, given that its inputs
are reduced (and the coefficients of `HighBits(w[i])` bounded): `maskR_trL`,
`rowW_trL`, `w1R_trL`; so two runs agree on what the commitment leaks
(`commit_tr`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Sign

open VG.Proof.MlDsa.Arith.Representation

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {p : Params} {D : Nat}

theorem lrel_rbx {x y : State} (h : LRel D (sgR p) (sgW p) x y) : ∀ r ∈ [Reg.rbx], x.gpr r = y.gpr r := by
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact h.regs (.rbx, scrLen p) (by simp [sgR, sgW])

end

/-! ## `y` and `ŷ` -/

theorem setKappa_post {D : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay D rbs wbs s) {r : Nat}
    (hr : r < 2 ^ 31) (h1 : inB (rbs ++ wbs) (sc oKAP) 8 = true) (h2 : inB wbs (sc (oMS + 64)) 2 = true) :
    WP isa (.block (setKappa r)) s fun s' => ∃ W, PostB D s s' W := by
  have e65 : pa s (sc (oMS + 65)) = pa s (sc (oMS + 64)) + 1 := (pa_sc_add s (oMS + 64) 1).symm
  have w2 := L.iW h2
  have c0 : (⟨pa s (sc (oMS + 64)), 2⟩ : Region).Contains (pa s (sc (oMS + 64))) 1 := by
    have := contains_offset' (base := pa s (sc (oMS + 64))) (off := 0) (len := 1) (n := 2) (by omega_using []) (by decide)
    rwa [BitVec.add_zero] at this
  have c1 : (⟨pa s (sc (oMS + 64)), 2⟩ : Region).Contains (pa s (sc (oMS + 65))) 1 := by
    rw [e65]; exact contains_offset' (off := 1) (by omega_using []) (by decide)
  have i0 : InRegions s.wr (pa s (sc (oMS + 64))) 1 := by
    have := inRegions_sub (off := 0) (l := 1) w2 (by omega_using []) (by decide)
    rwa [BitVec.add_zero] at this
  have i1 : InRegions s.wr (pa s (sc (oMS + 65))) 1 := by
    rw [e65]; exact inRegions_sub (off := 1) (l := 1) w2 (by omega_using []) (by decide)
  refine WP.mono (setKap_ok (oMS + 64) r hr s (L.iR h1) i0 i1) fun s' ⟨hm, k⟩ => ⟨_, (postB_of_keep (D := D) k (by decide)
    (W := [⟨pa s (sc (oMS + 64)), 2⟩]) ?_).1⟩
  rw [hm]
  exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c1

theorem maskR_trL {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {r : Nat} (hc : mChk p r = true) :
    RelCT isa (LRel D (sgR p) (sgW p)) (maskR P p r) fun _ _ => True := by
  simp only [mChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, k1⟩, w1⟩, cm⟩, _⟩, cc⟩, _⟩, _⟩, ci⟩, _⟩, _⟩, _⟩, hr⟩, hγ⟩ := hc
  have hcc := copyChk_spec cc
  unfold maskR
  refine RelCT.mono (seqL (p := p) (I := fun _ => True) (J := fun _ => True)
    (block_tr rfl fun x y h => lrel_rbx h.1) (fun x L _ => WP.mono (setKappa_post L hr k1 w1) fun _ h => ⟨h, trivial⟩)
    (seqL (J := fun s => Reduced s.mem (pa s (yP p r)))
      (RelCT.mono (maskAt_tr hP hγ cm) (fun _ _ h => h.1) fun _ _ h => h)
      (fun x L _ => WP.mono (maskAt_ok hP L hγ cm) fun x' ⟨hP', _, hq⟩ =>
        ⟨⟨_, hP'⟩, by rw [hP'.pa (pS_bases _)]; exact hq.1⟩)
      (seqL (J := fun s => Reduced s.mem (pa s (yhP p r)))
        (RelCT.mono (copy_tr hcc.2.2.2.1 hcc.2.2.2.2.1 hcc.2.2.2.2.2.1 hcc.2.2.2.2.2.2.1 hcc.2.2.2.2.2.2.2
          fun x y h => ⟨lrel_rbx h.1 _ (List.mem_singleton_self _), lrel_rbx h.1 _ (List.mem_singleton_self _)⟩)
          (fun _ _ h => h) fun _ _ h => h)
        (fun x L hy => WP.mono (copy_okB L cc) fun x' ⟨hP', _, hb⟩ =>
          ⟨⟨_, hP'⟩, by rw [hP'.pa (pS_bases _)]; exact reduced_congr₂ (bytes_of_bytesAt hb) hy⟩)
        (ipAt_tr (t := ntt) hP.ntt ci))))
    (fun _ _ h => ⟨h, trivial, trivial⟩) fun _ _ h => h

/-! ## `y` and `ŷ`, four at a time -/

theorem ms4_trL {D : Nat} {p : Params} {g k : Nat} (hc : ms4Chk p g k = true) :
    RelCT isa (LRel D (sgR p) (sgW p)) (cpM4 g k) fun _ _ => True := by
  simp only [ms4Chk, Bool.and_eq_true] at hc
  have cc := hc.1.1.1.1.1.1.1.1
  have hcc := copyChk_spec cc
  unfold cpM4
  exact RelCT.mono (seqL (p := p) (I := fun _ => True) (J := fun _ => True)
    (RelCT.mono (copy_tr hcc.2.2.2.1 hcc.2.2.2.2.1 hcc.2.2.2.2.2.1 hcc.2.2.2.2.2.2.1 hcc.2.2.2.2.2.2.2
      fun x y h => ⟨lrel_rbx h.1 _ (List.mem_singleton_self _), lrel_rbx h.1 _ (List.mem_singleton_self _)⟩)
      (fun _ _ h => h) fun _ _ h => h)
    (fun x L _ => WP.mono (copy_okB L cc) fun _ ⟨hP', _⟩ => ⟨⟨_, hP'⟩, trivial⟩)
    (block_tr rfl fun x y h => lrel_rbx h.1))
    (fun _ _ h => ⟨h, trivial, trivial⟩) fun _ _ h => h

theorem yhR_trL {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {t ry r : Nat} (hc : yhChk p ry r = true)
    (hr : r < ry) :
    RelCT isa (fun x y => LRel D (sgR p) (sgW p) x y ∧ (∃ σ, ICy p D σ t ry r x) ∧ ∃ σ, ICy p D σ t ry r y)
      (yhR P p r) fun _ _ => True := by
  simp only [yhChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨cc, _⟩, ci⟩, _⟩ := hc
  have hcc := copyChk_spec cc
  unfold yhR
  exact seqL (J := fun s => Reduced s.mem (pa s (yhP p r)))
    (RelCT.mono (copy_tr hcc.2.2.2.1 hcc.2.2.2.2.1 hcc.2.2.2.2.2.1 hcc.2.2.2.2.2.2.1 hcc.2.2.2.2.2.2.2
      fun x y h => ⟨lrel_rbx h.1 _ (List.mem_singleton_self _), lrel_rbx h.1 _ (List.mem_singleton_self _)⟩)
      (fun _ _ h => h) fun _ _ h => h)
    (fun x L ⟨_, I⟩ => WP.mono (copy_okB L cc) fun x' ⟨hP', _, hb⟩ =>
      ⟨⟨_, hP'⟩, by rw [hP'.pa (pS_bases _)]; exact reduced_congr₂ (bytes_of_bytesAt hb) (I.y r hr).1⟩)
    (ipAt_tr (t := ntt) hP.ntt ci)

theorem mask4_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {g : Nat} (hc : m4Chk p g = true)
    {E : State → State → Prop} {t : Nat} :
    RelCT isa (RS p D E fun σ s => ICm p D σ t (4 * g) s) (mask4 P p g)
      (RS p D E fun σ s => ICm p D σ t (4 * (g + 1)) s) := by
  obtain ⟨hcp, cm, c2, hyh, hγ⟩ := m4Chk_spec hc
  unfold mask4
  refine RelCT.seq (R := RS p D E fun σ s => SD p D σ t g 4 s) ?_
    (RelCT.seq (R := RS p D E fun σ s => ICy p D σ t (4 * g + 4) (4 * g) s) ?_ ?_)
  · refine RelCT.mono (seqR_tr (R := fun k => RS p D E fun σ s => SD p D σ t g k s) 4 0 fun k _ hk =>
      liftT (fun _ _ h => h.m.l.st) (fun _ _ _ h => ms4_ok (hcp k (by omega_using [hk])) h) (ms4_trL (hcp k (by omega_using [hk]))))
      (fun x y h => h.mono (fun _ _ h => h) fun _ _ h => ⟨h, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
      fun x y h => by rwa [Nat.zero_add] at h
  · exact liftT (fun _ _ h => h.m.l.st) (fun _ _ _ h => m4call_ok hP hγ cm c2 h) (mask4Call_tr hP hγ cm)
  · exact RelCT.mono (seqR_tr (R := fun r => RS p D E fun σ s => ICy p D σ t (4 * g + 4) r s) 4 (4 * g)
      fun r h1 hr => liftL (T := fun s => ∃ σ, ICy p D σ t (4 * g + 4) r s) (fun σ s h => ⟨h.l.st, σ, h⟩)
        (fun _ _ _ h => yhR_ok hP (hyh r h1 hr) (by omega_using [hr]) h) (yhR_trL hP (hyh r h1 hr) (by omega_using [hr])))
      (fun x y h => h) fun x y h => h.mono (fun _ _ h => h) fun _ _ h => ⟨h.l, h.y, h.yh⟩

/-! ## The last three polynomials of `y`, four at a time -/

theorem tailR_trL {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {t r : Nat} (hc : tChk p r = true)
    (h1 : 4 * (p.ℓ / 4) ≤ r) (h2 : r < 4 * (p.ℓ / 4) + 3) :
    RelCT isa (fun x y => LRel D (sgR p) (sgW p) x y ∧ (∃ σ, ICT p D σ t r x) ∧ ∃ σ, ICT p D σ t r y)
      (tailR P p r) fun _ _ => True := by
  simp only [tChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c0, _⟩, _⟩, cc⟩, _⟩, _⟩, _⟩, ci⟩, _⟩, _⟩, _⟩ := hc
  have hc0 := copyChk_spec c0
  have hcc := copyChk_spec cc
  unfold tailR yhR
  exact seqL (J := fun s => Reduced s.mem (pa s (yP p r)))
    (RelCT.mono (copy_tr hc0.2.2.2.1 hc0.2.2.2.2.1 hc0.2.2.2.2.2.1 hc0.2.2.2.2.2.2.1 hc0.2.2.2.2.2.2.2
      fun x y h => ⟨lrel_rbx h.1 _ (List.mem_singleton_self _), lrel_rbx h.1 _ (List.mem_singleton_self _)⟩)
      (fun _ _ h => h) fun _ _ h => h)
    (fun x L ⟨_, I⟩ => WP.mono (copy_okB L c0) fun x' ⟨hP', _, hb⟩ => ⟨⟨_, hP'⟩, by
      rw [hP'.pa (pS_bases _)]
      have := I.tmp (r - 4 * (p.ℓ / 4)) (by omega) (by omega_using [])
      exact reduced_congr₂ (bytes_of_bytesAt hb) this.1⟩)
    (seqL (J := fun s => Reduced s.mem (pa s (yhP p r)))
      (RelCT.mono (copy_tr hcc.2.2.2.1 hcc.2.2.2.2.1 hcc.2.2.2.2.2.1 hcc.2.2.2.2.2.2.1 hcc.2.2.2.2.2.2.2
        fun x y h => ⟨lrel_rbx h.1 _ (List.mem_singleton_self _), lrel_rbx h.1 _ (List.mem_singleton_self _)⟩)
        (fun _ _ h => h) fun _ _ h => h)
      (fun x L hy => WP.mono (copy_okB L cc) fun x' ⟨hP', _, hb⟩ =>
        ⟨⟨_, hP'⟩, by rw [hP'.pa (pS_bases _)]; exact reduced_congr₂ (bytes_of_bytesAt hb) hy⟩)
      (ipAt_tr (t := ntt) hP.ntt ci))

theorem maskTail_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hl : p.ℓ % 4 = 3)
    (hc : tailChk p = true) {E : State → State → Prop} {t : Nat} :
    RelCT isa (RS p D E fun σ s => ICm p D σ t (4 * (p.ℓ / 4)) s) (maskTail P p)
      (RS p D E fun σ s => ICm p D σ t p.ℓ s) := by
  have hc' := hc
  simp only [tailChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc'
  obtain ⟨⟨⟨⟨hcp, cm⟩, c2⟩, ht⟩, hγ⟩ := hc'
  have htr : ∀ r, 4 * (p.ℓ / 4) ≤ r → r < 4 * (p.ℓ / 4) + 3 → tChk p r = true := fun r h1 h2 => by
    have := ht (r - 4 * (p.ℓ / 4)) (by omega_using [h2])
    rwa [show 4 * (p.ℓ / 4) + (r - 4 * (p.ℓ / 4)) = r by omega_using [h1]] at this
  unfold maskTail
  refine RelCT.seq (R := RS p D E fun σ s => SD p D σ t (p.ℓ / 4) 4 s) ?_
    (RelCT.seq (R := RS p D E fun σ s => ICT p D σ t (4 * (p.ℓ / 4)) s) ?_ ?_)
  · refine RelCT.mono (seqR_tr (R := fun k => RS p D E fun σ s => SD p D σ t (p.ℓ / 4) k s) 4 0 fun k _ hk =>
      liftT (fun _ _ h => h.m.l.st) (fun _ _ _ h => ms4_ok (hcp k (by omega_using [hk])) h) (ms4_trL (hcp k (by omega_using [hk]))))
      (fun x y h => h.mono (fun _ _ h => h) fun _ _ h => ⟨h, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
      fun x y h => by rwa [Nat.zero_add] at h
  · exact liftT (fun _ _ h => h.m.l.st) (fun _ _ _ h => maskTailCall_ok hP hc h) (mask4Call_tr hP hγ cm)
  · exact RelCT.mono (seqR_tr (R := fun r => RS p D E fun σ s => ICT p D σ t r s) 3 (4 * (p.ℓ / 4))
      fun r h1 hr => liftL (T := fun s => ∃ σ, ICT p D σ t r s) (fun σ s h => ⟨h.m.l.st, σ, h⟩)
        (fun _ _ _ h => tailR_ok hP (htr r h1 hr) h1 hr h) (tailR_trL hP (htr r h1 hr) h1 hr))
      (fun x y h => h) fun x y h => h.mono (fun _ _ h => h) fun _ _ h => by
        rw [show 4 * (p.ℓ / 4) + 3 = p.ℓ by omega_using [hl]] at h; exact h.m

theorem maskRest_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hc : restChk p = true)
    (hm : ∀ r < p.ℓ, mChk p r = true) {E : State → State → Prop} {t : Nat} :
    RelCT isa (RS p D E fun σ s => ICm p D σ t (4 * (p.ℓ / 4)) s) (maskRest P p)
      (RS p D E fun σ s => ICm p D σ t p.ℓ s) := by
  unfold maskRest
  unfold restChk at hc
  cases e : p.ℓ % 4 == 3
  · rw [Bool.cond_false]
    exact RelCT.mono (seqR_tr (R := fun r => RS p D E fun σ s => ICm p D σ t r s) (p.ℓ % 4) (4 * (p.ℓ / 4))
      fun r _ hr =>
      liftT (fun _ _ h => h.l.st) (fun _ _ _ h => maskR_ok hP (hm r (by omega_using [hr])) h) (maskR_trL hP (hm r (by omega_using [hr]))))
      (fun x y h => h) fun x y h => by rwa [Nat.div_add_mod] at h
  · rw [Bool.cond_true]
    rw [e, Bool.cond_true] at hc
    exact maskTail_tr hP (beq_iff_eq.mp e) hc

/-! ## `w` -/

/-- `w[i]` from runs in iteration `t` with `y`, `ŷ` and the first `i` polynomials of `w`. -/
theorem rowW_trL {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {t i : Nat} (hc : wChk p i = true)
    (hi : i < p.k) :
    RelCT isa (fun x y => LRel D (sgR p) (sgW p) x y ∧ (∃ σ, ICw p D σ t i x) ∧ ∃ σ, ICw p D σ t i y) (rowW P p i)
      fun _ _ => True := by
  simp only [wChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨cd, _⟩, hl⟩ := hc
  unfold rowW
  exact RelCT.mono (dotAt_tr (hP.dotInv p.ℓ hl) cd) (fun x y ⟨R, ⟨_, I₁⟩, ⟨_, I₂⟩⟩ =>
    ⟨R, ⟨fun j hj => by rw [famP_aP]; exact (rowA hi I₁ hj).1, fun j hj => by rw [famP_yhP]; exact (I₁.yh j hj).1⟩,
      ⟨fun j hj => by rw [famP_aP]; exact (rowA hi I₂ hj).1, fun j hj => by rw [famP_yhP]; exact (I₂.yh j hj).1⟩⟩)
    fun _ _ h => h

/-! ## `w₁` -/

theorem w1R_trL {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {t i : Nat} (hc : hChk p i = true)
    (hi : i < p.k) :
    RelCT isa (fun x y => LRel D (sgR p) (sgW p) x y ∧ (∃ σ, ICh p D σ t i x) ∧ ∃ σ, ICh p D σ t i y) (w1R P p i)
      fun _ _ => True := by
  simp only [hChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, _⟩, _⟩, _⟩, _⟩, hb⟩, hγ⟩ := hc
  unfold w1R
  refine seqL (J := fun s => ∀ j < 256, (coeffAt s.mem (pa s t1P) j).toNat ≤ w1Max p) ?_ ?_
    (sbpAt_tr hP hb rfl c2)
  · exact RelCT.mono (highBitsAt_tr hP hγ c1) (fun x y ⟨R, ⟨_, I₁⟩, ⟨_, I₂⟩⟩ => ⟨R, (I₁.c.w i hi).1, (I₂.c.w i hi).1⟩)
      fun _ _ h => h
  · rintro x L ⟨σ, I⟩
    refine WP.mono (highBitsAt_ok hP L hγ c1 (I.c.w i hi).1) fun x' ⟨hP', _, hq⟩ => ⟨⟨_, hP'⟩, fun j hj => ?_⟩
    rw [hP'.pa (by decide), natPolyIs_coeff hq hj]
    simp only [Vector.getElem_map]
    exact highBits_le hγ _

/-! ## The commitment -/

theorem ctShake_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hc : cChk p = true) {σ : State} {t : Nat}
    {s : State} (h : ICh p D σ t p.k s) :
    WP isa (shakeAt [((.r12, 0), 64), (sc oW1, p.k * w1Len p)] (sc oCT) (cLen p)) s (IC p D σ t) := by
  simp only [cChk, Bool.and_eq_true] at hc
  obtain ⟨⟨_, hs⟩, hk⟩ := hc
  refine WP.mono (shake_ok (sgB_bases p) hP.hD hs h.c.l.st.lay) fun s4 ⟨hP4, _, hb⟩ => ⟨h.c.step hP4 hk, ?_⟩
  rw [hP4.pa (by decide), hb]
  simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [Nat.mul_comm p.k, h.w1, h.c.l.st.mu]
  simp only [CTv, ctF, w1Encode, List.flatMap_map]

theorem commit_tr {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hc : cChk p = true)
    {E : State → State → Prop} {t : Nat} :
    RelCT isa (RS p D E fun σ s => IL p D σ t s) (commit P p) (RS p D E fun σ s => IC p D σ t s) := by
  have hc' := hc
  simp only [cChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc'
  obtain ⟨⟨⟨⟨⟨⟨hm4, hm⟩, hrest⟩, hw⟩, hh⟩, hs⟩, _⟩ := hc'
  unfold commit
  refine RelCT.seq (R := RS p D E fun σ s => ICm p D σ t (4 * (p.ℓ / 4)) s) ?_
    (RelCT.seq (R := RS p D E fun σ s => ICw p D σ t 0 s) ?_ (RelCT.seq (R := RS p D E fun σ s => ICh p D σ t 0 s)
    ?_ (RelCT.seq (R := RS p D E fun σ s => ICh p D σ t p.k s) ?_ ?_)))
  · refine RelCT.mono (seqR_tr (R := fun g => RS p D E fun σ s => ICm p D σ t (4 * g) s) (p.ℓ / 4) 0 fun g _ hg =>
      mask4_tr hP (hm4 g (by omega_using [hg])))
      (fun x y h => h.mono (fun _ _ h => h) fun _ _ h =>
        ⟨h, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩)
      fun x y h => by rwa [Nat.zero_add] at h
  · exact RelCT.mono (maskRest_tr hP hrest hm) (fun x y h => h) fun x y h => h.mono (fun _ _ h => h) fun _ _ h =>
      ⟨h.l, h.y, h.yh, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  · refine RelCT.mono (seqR_tr (R := fun i => RS p D E fun σ s => ICw p D σ t i s) p.k 0 fun i _ hi =>
      liftL (T := fun s => ∃ σ, ICw p D σ t i s) (fun σ s h => ⟨h.l.st, σ, h⟩)
        (fun _ _ _ h => rowW_ok hP (hw i (by omega_using [hi])) (by omega_using [hi]) h) (rowW_trL hP (hw i (by omega_using [hi])) (by omega_using [hi])))
      (fun x y h => h) fun x y h => by rw [Nat.zero_add] at h; exact h.mono (fun _ _ h => h) fun _ _ h =>
        ⟨h, by simp [w1Enc]; rfl⟩
  · refine RelCT.mono (seqR_tr (R := fun i => RS p D E fun σ s => ICh p D σ t i s) p.k 0 fun i _ hi =>
      liftL (T := fun s => ∃ σ, ICh p D σ t i s) (fun σ s h => ⟨h.c.l.st, σ, h⟩)
        (fun _ _ _ h => w1R_ok hP (hh i (by omega_using [hi])) (by omega_using [hi]) h) (w1R_trL hP (hh i (by omega_using [hi])) (by omega_using [hi])))
      (fun x y h => h) fun x y h => by rwa [Nat.zero_add] at h
  · exact liftT (fun _ _ h => h.c.l.st) (fun _ _ _ h => ctShake_ok hP hc h)
      (RelCT.mono (shake_tr (sgB_bases p) hP.hD hs) (fun _ _ h => h) fun _ _ _ => trivial)

end VG.Proof.MlDsa.X86_64.Sign

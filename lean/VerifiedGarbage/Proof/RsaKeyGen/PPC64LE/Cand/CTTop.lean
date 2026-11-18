module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.WUni
meta import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.WUni
import VerifiedGarbage.Proof.RsaKeyGen.TrialFilter
meta import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
meta import VerifiedGarbage.Proof.RsaKeyGen.TrialFilter
import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
public import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.CTBase
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Main
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Slot
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Sel
public import VerifiedGarbage.Spec.RsaKeyGen
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.RoundCall
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFn
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.RangeCover
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.Minv
public import VerifiedGarbage.Impl.MillerRabin.PPC64LE.Search
meta import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.CTBase
meta import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Main
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Slot
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Sel
meta import VerifiedGarbage.Spec.RsaKeyGen
meta import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.RoundCall
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFn
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Mont.RangeCover
meta import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.Minv
meta import VerifiedGarbage.Impl.MillerRabin.PPC64LE.Search
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.GeFlag
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.GeFlag
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
meta import VerifiedGarbage.Proof.Framework.Block

/-! ### `RsaKeyGen.PPC64LE.Cand.Body`, which this module and modules that import it used -/

section

/-!
# A candidate on PPC64LE: the body

`bodyMid_ok`: `out` zeroed, then 0 if `rand` is shorter than a candidate, else
`main_ok`. `code_correct`: the whole function, as the contract states its
results.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search (geFlag)
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)

/-- `geFlag r5 r27 r24`: `r5 := 1` if `r27 ≥ r24`, else 0. -/
theorem geFlag27_ok {s : State} {x y : Nat} (h27 : s.gpr .r27 = BitVec.ofNat 64 x)
    (h24 : s.gpr .r24 = BitVec.ofNat 64 y) (hx : x < 2 ^ 64) (hy : y < 2 ^ 63) :
    WP isa (.block (geFlag .r5 .r27 .r24)) s fun t =>
      (t.gpr .r5 = BitVec.ofNat 64 (if y ≤ x then 1 else 0) ∧ t.mem = s.mem) ∧ Keep [.r5, .r0] s t := by
  refine WP.keep _ ?_ (by decide)
  simp only [geFlag]
  prun [h27, h24, VG.Proof.MillerRabin.PPC64LE.Search.ge_val hx hy]

/-- Too few octets for a candidate. -/
theorem cOp_none {s0 : State} {w : Nat} (hw : oL s0 = 8 * w) (hw1 : 1 ≤ w) (h : ¬ oL s0 ≤ rL s0) :
    cOp s0 = none := by
  unfold cOp Spec.RsaKeyGen.candidateOp
  rw [hw, VG.Proof.RsaKeyGen.candidateStep_eq _ _ _ _ (by omega_using [hw1]),
    VG.Proof.RsaKeyGen.ite_f (by rw [bytesAt_length]; omega_using [hw, h])]

/-- The body's state, with the registers the entry set. -/
structure BR (s0 s : State) : Prop where
  ctx : Ctx s0 s
  regs : Regs s0 s
  syms : s.syms = s0.syms

theorem BR.keep {s0 s t : State} {rs : List Reg} (h : BR s0 s) (k : Keep rs s t) (hm : t.mem = s.mem)
    (hs : t.syms = s.syms)
    (hr : ∀ r ∈ [Reg.r2, .r23, .r24, .r25, .r21, .r30, .r18, .r19, .r26, .r27, .r31, .r11, .r28], r ∉ rs := by decide) :
    BR s0 t :=
  ⟨h.ctx.keep k hm (fun r h' => hr r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
    rcases h' with rfl | rfl | rfl | rfl <;> simp)), ⟨(k.gpr _ (hr _ (by simp))).trans h.regs.r23, (k.gpr _ (hr _ (by simp))).trans h.regs.r24,
    (k.gpr _ (hr _ (by simp))).trans h.regs.r25, (k.gpr _ (hr _ (by simp))).trans h.regs.r21,
    (k.gpr _ (hr _ (by simp))).trans h.regs.r30, (k.gpr _ (hr _ (by simp))).trans h.regs.r18,
    (k.gpr _ (hr _ (by simp))).trans h.regs.r19, (k.gpr _ (hr _ (by simp))).trans h.regs.r26,
    (k.gpr _ (hr _ (by simp))).trans h.regs.r27, (k.gpr _ (hr _ (by simp))).trans h.regs.r31,
    (k.gpr _ (hr _ (by simp))).trans h.regs.r11, (k.gpr _ (hr _ (by simp))).trans h.regs.r28⟩, hs.trans h.syms⟩

theorem zeroS {s0 s : State} (hb : Bx s0 s) (hr : Regs s0 s) (sy : s.syms = s0.syms) :
    WP isa VG.Impl.RsaKeyGen.PPC64LE.Candidate.zeroOut s (BR s0) := by
  have hp := hb.pre
  have hv := hp.valid
  simp only [Spec.RsaKeyGen.primeLenValid] at hv
  have hfo := hp.fo
  have eO : oL s0 = (s0.gpr .r4).toNat := rfl
  refine WP.mono_syms (zeroOut_ok (L := oL s0) hr.r23 (by rw [hr.r24, eO, ofNat_toNat64]) (by omega_using [hv, eO])
    (by omega_using [hv, eO]) (fun i hi => ⟨cO s0, by rw [hb.wr, bodyWr, hp.wr]; simp,
      Offset.contains_base _ (d := i) (by simp only [oL] at hi; omega_using [hi]) (by omega_using [eO, hi])⟩) (by omega_using [hfo, eO]))
    fun t₁ ⟨z₁, o₁, k₁⟩ sy₁ => ?_
  have c₁ : Ctx s0 t₁ := by
    refine ⟨hb.step k₁.sp k₁.rd k₁.wr ((frame_of_outside (Z := oL s0) o₁ (by omega_using [])).mono (by simp)) (k₁.gpr _ (by decide)),
      (k₁.gpr _ (by decide)).trans hr.r23, (k₁.gpr _ (by decide)).trans hr.r24,
      (k₁.gpr _ (by decide)).trans hr.r25, ?_⟩
    apply List.ext_getElem (by simp [Spec.Rsa.bytesAt])
    intro i h1 h2
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h1
    exact z₁ i h1
  exact ⟨c₁, ⟨(k₁.gpr _ (by decide)).trans hr.r23, (k₁.gpr _ (by decide)).trans hr.r24,
    (k₁.gpr _ (by decide)).trans hr.r25, (k₁.gpr _ (by decide)).trans hr.r21, (k₁.gpr _ (by decide)).trans hr.r30,
    (k₁.gpr _ (by decide)).trans hr.r18, (k₁.gpr _ (by decide)).trans hr.r19, (k₁.gpr _ (by decide)).trans hr.r26,
    (k₁.gpr _ (by decide)).trans hr.r27, (k₁.gpr _ (by decide)).trans hr.r31, (k₁.gpr _ (by decide)).trans hr.r11,
    (k₁.gpr _ (by decide)).trans hr.r28⟩, sy₁.trans sy⟩

/-- The body's state with the test of `rand`'s length. -/
def BF (s0 s : State) : Prop :=
  BR s0 s ∧ s.gpr .r5 = BitVec.ofNat 64 (if oL s0 ≤ rL s0 then 1 else 0)

theorem flagS {s0 s : State} (h : BR s0 s) :
    WP isa (.block (geFlag .r5 .r27 .r24)) s (BF s0) := by
  have hp := h.ctx.bx.pre
  have hv := hp.valid
  simp only [Spec.RsaKeyGen.primeLenValid] at hv
  exact WP.mono_syms (geFlag27_ok (x := rL s0) (y := oL s0) (h.regs.r27.trans (ofNat_toNat64 _).symm)
      (h.regs.r24.trans (ofNat_toNat64 _).symm) (by simp only [rL]; omega_using []) (by simp only [oL]; omega_using [hv]))
    fun t₂ ⟨⟨a5, m₂⟩, k₂⟩ sy₂ => ⟨h.keep k₂ m₂ sy₂, a5⟩

theorem iteS {trial : Prog isa} (D : DivOk trial) (R : RoundImpl) {s0 s : State} (hT : TabOk s0)
    (h : BF s0 s) :
    WP isa (.ite (.zero .d .r5) VG.Impl.RsaKeyGen.PPC64LE.Candidate.finNone
      (VG.Impl.RsaKeyGen.PPC64LE.Candidate.main trial R.name R.code)) s
      fun u => Bx s0 u ∧ CQ s0 (u.gpr .r3) u.mem := by
  obtain ⟨⟨c₂, hr, sy⟩, a5⟩ := h
  have hp := c₂.bx.pre
  obtain ⟨hw, hw4, -⟩ := cw_facts hp
  refine WP.ite _ (eval_zero_ofNat _ _ (by split <;> decide) a5) (fun hz => ?_) (fun hz => ?_)
  · have hav : ¬ oL s0 ≤ rL s0 := by
      intro hc; simp only [hc, ↓reduceIte] at hz; exact absurd hz (by decide)
    exact finNone_post c₂ (cOp_none hw (by omega_using [hw4]) hav)
  · have hav : oL s0 ≤ rL s0 := by
      by_contra hc; simp only [hc, ↓reduceIte] at hz; exact absurd hz (by decide)
    exact main_ok D R ⟨c₂, hr.r21, hr.r30, hr.r18, hr.r19, hr.r26, hr.r27, hr.r31, hr.r11, hav, sy, hT⟩

theorem bodyMid_ok {trial : Prog isa} (D : DivOk trial) (R : RoundImpl) {s0 s : State} (hT : TabOk s0)
    (hb : Bx s0 s) (hr : Regs s0 s) (sy : s.syms = s0.syms) :
    WP isa (mid trial R.name R.code) s fun u => Bx s0 u ∧ CQ s0 (u.gpr .r3) u.mem := by
  unfold mid
  exact WP.seq (WP.mono (zeroS hb hr sy) fun t₁ h₁ => WP.seq (WP.mono (flagS h₁) fun t₂ h₂ => iteS D R hT h₂))

/-- The whole function: its results are the contract's. -/
theorem code_correct {trial : Prog isa} (D : DivOk trial) (R : RoundImpl) {s0 : State} (h : CIn s0)
    (hT : TabOk s0) :
    WP isa (VG.Impl.RsaKeyGen.PPC64LE.Candidate.code trial R.name R.code) s0
      fun t => abiPreserved s0 t ∧ CQ s0 (t.gpr .r3) t.mem :=
  code_ok h (fun _ hb hr sy => bodyMid_ok D R hT hb hr sy) fun r m m' fl ⟨hr, hb, hw⟩ => by
    -- `out` and `used` lie apart from the frame.
    refine ⟨hr, ?_, ?_⟩
    · rw [← hb]
      exact List.map_congr_left fun i hi => lost_byte fl (R := cO s0) h.Fo.symm (List.mem_range.mp hi)
    · simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero] at hw ⊢
      rw [← hw, fl.readW (r := cU s0) (Region.contains_self _ _)
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h.Fu.symm) (by decide)]

end VG.Proof.RsaKeyGen.PPC64LE.Cand

end

end

/-! ### `RsaKeyGen.PPC64LE.Cand.CTMain`, which only this module used -/

section

/-! ### `RsaKeyGen.PPC64LE.Cand.CTTest`, which only this module used -/

section

/-! ### `RsaKeyGen.PPC64LE.Cand.CTMr`, which only this module used -/

section

/-! ### `RsaKeyGen.PPC64LE.Cand.CTDraw`, which only this module used -/

section

/-! ### `RsaKeyGen.PPC64LE.Cand.CTLoop`, which only this module used -/

section

/-! ### `RsaKeyGen.PPC64LE.Cand.CTPre`, which this module and modules that import it used -/

section

/-!
# A candidate on PPC64LE: the states the round is called from

For the constant time of the witnesses' loop, what the correctness proofs
compose in one step is needed at the points in between: `preCall_wp`, the
round's arguments before its call (`CallIn`), whose contract then holds
(`CallIn.pre`) and agrees between two runs (`CallIn.pub`); `call_wp`, the
call keeping `r31`; `load1_wp`, the addresses of a witness's octets.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.MillerRabin.PPC64LE.Search
open VG.Proof.MillerRabin.PPC64LE (Env arr RoundImpl)
open VG.Proof.MillerRabin.PPC64LE.Search (Prep Kept keeps_word r12_inv)
open VG.Proof.Bignum (slot)

/-- The state the round is called from. -/
structure CallIn (s : State) (B : Addr) (L w c : Nat) : Prop where
  prep : Prep s B L w c
  r3 : s.gpr .r3 = B
  r4 : s.gpr .r4 = BitVec.ofNat 64 L
  a5 : arr s.mem B w 5 < c
  wr : (⟨B, 8 * L⟩ : Region) ∈ s.wr
  sp : 176 ≤ s.sp.toNat
  stk : (below s.sp 176).Disjoint ⟨B, 8 * L⟩

/-- The round's arguments, after its witness in Montgomery form. -/
abbrev preCall : Prog isa :=
  .seq (.seq (.block minv32) (PublicChecked.montOp 5 4 1)) (.block [.addi .r3 .r31 0, ldh .r4 hWsLen])

theorem preCall_wp {s : State} {B : Addr} {L w c : Nat} (h : Prep s B L w c) (hwr : (⟨B, 8 * L⟩ : Region) ∈ s.wr)
    (hsp : 176 ≤ s.sp.toNat) (hstk : (below s.sp 176).Disjoint ⟨B, 8 * L⟩) :
    WP isa preCall s fun t => CallIn t B L w c := by
  have e := h.env
  have hnw := e.hs.nowrap
  have hZ := e.hZ
  have hw4 := e.hw
  have hw128 := e.hw'
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have hZ' : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := by rw [← es]; exact hZ
  have hR : Nat.Coprime (2 ^ (64 * w)) c := VG.Proof.Bignum.coprime_pow2 h.odd _
  have l56 : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 56) 8 := e.hs.ld (d := 56) (by omega_using [hZ'])
  refine WP.seq (WP.seq (WP.mono (WP.keep [.r12] (Q := fun u => u.gpr .r12 = (word s.mem B 56 <<< 32) >>> 32 ∧
      u.mem = s.mem) (by simp only [minv32, ldh, hMinv]; prun [e.h31, l56]) (by decide))
    fun u ⟨⟨u12, um⟩, ku⟩ => ?_))
  have hu : Prep u B L w c := h.transfer (e.keep ku (by decide)) (fun d _ _ => by rw [um])
    (fun j _ _ => by rw [um])
  have eu := hu.env
  obtain ⟨i12, iinv⟩ := r12_inv h.inv
  refine WP.mono (Pub.montOp_ok eu.hs (o := 5) (a := 4) (b := 1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by omega_using [hw4]) (by omega_using [hw128]) (by simp only [es]; omega_using [hZ']) eu.h10 eu.h29
    eu.h11 (by rw [u12]; exact i12) (by rw [u12, um, w32_eq_mod]; exact iinv)
    (by show arr u.mem B w 1 < arr u.mem B w 0; rw [hu.r1, hu.n]; exact Nat.mod_lt _ (by have := h.c3; omega_using [this])))
    fun s₁ ⟨⟨lt₁, eq₁, o₁⟩, k₁⟩ => ?_
  have hn0 : val32 u.mem B (slot w 0) (2 * w) = c := hu.n
  rw [hn0] at lt₁
  have sep₁ : ∀ d k, 0 < k → (∀ i, d ≤ i → i < d + k → Kept w i) → ∀ r ∈ [(slot w 2, 8 * (w + 2)),
      (slot w 3, 8 * (w + 2)), (slot w 5, 8 * (w + 2))], d + k ≤ r.1 ∨ r.1 + r.2 ≤ d := by
    intro d k hk0 hk r hr
    have hj : ∃ j ∈ [2, 3, 5, 6, 8], r = (slot w j, 8 * (w + 2)) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [⟨2, by simp, rfl⟩, ⟨3, by simp, rfl⟩, ⟨5, by simp, rfl⟩]
    obtain ⟨j, hjm, rfl⟩ := hj
    show d + k ≤ slot w j ∨ slot w j + 8 * (w + 2) ≤ d
    by_contra hc
    simp only [not_or, Nat.not_le] at hc
    by_cases hd : d ≤ slot w j
    · have := (hk (slot w j) hd (by omega_using [hc])).2.1 j hjm; omega_using [hsp, hnw, hZ, hw4, hw128, hZ', u12, i12, iinv, lt₁, eq₁, hn0, hk0, hc, hd, this]
    · have := (hk d (Nat.le_refl _) (by omega_using [hk0])).2.1 j hjm; omega_using [hsp, hnw, hZ, hw4, hw128, hZ', u12, i12, iinv, lt₁, eq₁, hn0, hk0, hc, hd, this]
  have w₁ : ∀ d, d + 8 ≤ 8 * L → (∀ i, d ≤ i → i < d + 8 → Kept w i) → word s₁.mem B d = word u.mem B d :=
    fun d hd hk => Outs.word o₁ (sep₁ d 8 (by decide) hk) (by omega_using [hnw, hd])
  have v₁ : ∀ j, slot w j + 8 * w ≤ 8 * L → (∀ i, slot w j ≤ i → i < slot w j + 8 * w → Kept w i) →
      val32 s₁.mem B (slot w j) (2 * w) = val32 u.mem B (slot w j) (2 * w) :=
    fun j hd hk => Outs.val32 o₁ (by have := sep₁ _ _ (by omega_using [hw4]) hk; simpa only [show 4 * (2 * w) = 8 * w by omega_using []])
      (by omega_using [hnw, hd])
  have p₁ : Prep s₁ B L w c := hu.transfer (eu.keep k₁ (by decide)) w₁ v₁
  have h31₁ : s₁.gpr .r31 = B := (k₁.gpr .r31 (by decide)).trans eu.h31
  have l0 : InRegions (s₁.rd ++ s₁.wr) B 8 := by
    have := (eu.hs.congr k₁.wr).ld (d := 0) (n := 8) (by omega_using [hZ'])
    simpa only [off, BitVec.add_zero] using this
  have r0 : s₁.mem.readW B 64 = BitVec.ofNat 64 L := by
    have := p₁.len
    simpa only [word, off, BitVec.add_zero] using this
  refine WP.mono (WP.keep [.r3, .r4] (Q := fun t => t.gpr .r3 = B ∧ t.gpr .r4 = BitVec.ofNat 64 L ∧
      t.mem = s₁.mem) (by simp only [ldh, hWsLen]; prun [h31₁, BitVec.add_zero, l0, r0]) (by decide))
    fun t ⟨⟨r3, r4, m⟩, k⟩ => ?_
  have K := (ku.trans k₁).trans k
  exact ⟨p₁.transfer (p₁.env.keep k (by decide)) (fun d _ _ => by rw [m]) (fun j _ _ => by rw [m]), r3, r4,
    by show val32 t.mem B (slot w 5) (2 * w) < c; rw [m]; exact lt₁, by rw [K.wr]; exact hwr,
    by rw [K.sp]; exact hsp, by rw [K.sp]; exact hstk⟩

/-- The round's contract holds where it is called. -/
theorem CallIn.pre {s : State} {B : Addr} {L w c : Nat} (h : CallIn s B L w c) :
    (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 176).pre
      (s.callEntry.withRegions [] [⟨B, 8 * L⟩]) := by
  have e := h.prep.env
  have hnw := e.hs.nowrap
  have hZ := e.hZ
  have hw4 := e.hw
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have hZ' : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := by rw [← es]; exact hZ
  have hL64 : L < 2 ^ 64 := by omega_using [hnw]
  have hsp := h.sp
  have hstk := h.stk
  sig_pre [Proof.MillerRabin.Round.roundContract, Proof.MillerRabin.Round.roundSig, PPC64LE.abi, PPC64LE.argRegs]
  simp only [h.r3, h.r4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hL64, Nat.mul_comm L 8]
  exact ⟨hsp, trivial, hstk, by omega_using [hnw], h.prep.layout, h.prep.prepared h.a5⟩

/-- Two runs' calls agree on the round's public data. -/
theorem CallIn.pub {s₁ s₂ : State} {B : Addr} {L w c₁ c₂ : Nat} (h₁ : CallIn s₁ B L w c₁)
    (h₂ : CallIn s₂ B L w c₂) (hsp : s₁.sp = s₂.sp) :
    (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 176).pub
      (s₁.callEntry.withRegions [] [⟨B, 8 * L⟩]) (s₂.callEntry.withRegions [] [⟨B, 8 * L⟩]) := by
  sig_pub [Proof.MillerRabin.Round.roundContract, Proof.MillerRabin.Round.roundSig, PPC64LE.abi, PPC64LE.argRegs]
  rw [h₁.r3, h₂.r3, h₁.r4, h₂.r4, h₁.prep.width, h₂.prep.width]
  exact ⟨hsp, rfl, rfl, rfl⟩

/-- The round's call, keeping `r31`. -/
theorem call_wp (R : RoundImpl) {s : State} {B : Addr} {L w c : Nat} (h : CallIn s B L w c) :
    WP isa (.call R.name R.code) s fun t => t.gpr .r31 = s.gpr .r31 := by
  refine WP.callAny (k := Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 176) R.verified.1
    (rd := []) (wr := [⟨B, 8 * L⟩]) h.pre ?_ ?_ (fun s₃ _ _ _ _ hcs _ => hcs .r31 (by decide))
    (by have := R.stack; omega_using [this])
  · exact fun x n ⟨r, hr, hc⟩ => ⟨r, List.mem_append_right _ (by
      simp only [List.nil_append, List.mem_singleton] at hr; rw [hr]; exact h.wr), hc⟩
  · exact fun x n ⟨r, hr, hc⟩ => ⟨r, by rw [List.mem_singleton] at hr; rw [hr]; exact h.wr, hc⟩

/-- `load`'s first block. -/
abbrev load1 : List Instr :=
  [ldh .r12 hRand, ldh .r3 hUsed, .add .r12 .r12 .r3, ldh .r6 hK, .add .r3 .r3 .r6, sth .r3 hUsed] ++
    PublicChecked.base .r10 4

theorem load1_wp {s : State} {B R : Addr} {Z w u : Nat} (h : Env s B Z w) (hR : word s.mem B (8 * hRand) = R)
    (hu : word s.mem B (8 * hUsed) = BitVec.ofNat 64 u) (hk : word s.mem B (8 * hK) = BitVec.ofNat 64 (8 * w)) :
    WP isa (.block load1) s fun t => t.gpr .r12 = off R u ∧ t.gpr .r6 = BitVec.ofNat 64 (8 * w) ∧
      t.gpr .r10 = off B (slot w 4) ∧ t.gpr .r11 = s.gpr .r11 ∧ t.gpr .r31 = s.gpr .r31 := by
  have hs := h.hs
  have hnw := hs.nowrap
  have hZ := h.hZ
  rw [slot_lin] at hZ
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r3, .r6, .r12] (Q := fun t => t.gpr .r12 = off R u ∧
      t.gpr .r6 = BitVec.ofNat 64 (8 * w)) ?_ (by decide)) fun t₁ ⟨⟨a12, a6⟩, k₁⟩ => ?_
  · simp only [ldh, sth, hRand, hUsed, hK] at hR hu hk ⊢
    prun [h.h31, hs.ld (d := 136) (n := 8) (by omega_using [hZ]), hs.ld (d := 152) (n := 8) (by omega_using [hZ]),
      hs.ld (d := 216) (n := 8) (by omega_using [hZ]), hs.st (d := 152) (n := 8) (by omega_using [hZ]), hR, hu, hk]
  refine WP.mono (Pub.base_ok (rd := .r10) (by decide) (by decide) ((k₁.gpr _ (by decide)).trans h.h10)
    ((k₁.gpr _ (by decide)).trans h.h29) 4) fun t₂ ⟨⟨a10, _⟩, k₂⟩ => ?_
  exact ⟨(k₂.gpr _ (by decide)).trans a12, (k₂.gpr _ (by decide)).trans a6, a10,
    (k₂.gpr _ (by decide)).trans (k₁.gpr _ (by decide)), (k₂.gpr _ (by decide)).trans (k₁.gpr _ (by decide))⟩

end VG.Proof.RsaKeyGen.PPC64LE.Cand

end

end

/-!
# A candidate on PPC64LE: what two runs of the witnesses' loop share

Two runs of the loop are related at each iteration by `LI n (a, k)`: the
call's public data `a`, `k` witnesses passed and `n + 1` iterations left
(`MrAt`), the same in both runs. Whether the next witness passes
(`pass_agree`) and whether the loop goes on (`mc_agree`) are then the same:
both follow from the shape of the result of the test, which the leak fixes
(`shape_eq`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Proof.MillerRabin.PPC64LE (Env arr RoundImpl)
open VG.Proof.Bignum (slot)
open VG.Proof.RsaKeyGen (MrAt mrS wit)

/-! ## Two runs -/

theorem two_cond {α : Type} {Φ : α → State → Prop} {c : isa.Cond} {b : Bool} {p : Prog isa}
    {Q : State → State → Prop}
    (hag : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → isa.eval c s₁ = isa.eval c s₂)
    (h : RelCT isa (Two fun a s => Φ a s ∧ isa.eval c s = some b) p Q) :
    RelCT isa (fun s₁ s₂ => Two Φ s₁ s₂ ∧ isa.eval c s₁ = some b) p Q :=
  h.mono (fun _ _ ⟨⟨a, h₁, h₂, hsp⟩, e⟩ => ⟨a, ⟨h₁, e⟩, ⟨h₂, (hag a _ _ h₁ h₂) ▸ e⟩, hsp⟩) fun _ _ h => h

theorem two_ite {α : Type} {Φ : α → State → Prop} {c : isa.Cond} {t e : Prog isa} {Q : State → State → Prop}
    (hag : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → isa.eval c s₁ = isa.eval c s₂)
    (ht : RelCT isa (Two fun a s => Φ a s ∧ isa.eval c s = some true) t Q)
    (he : RelCT isa (Two fun a s => Φ a s ∧ isa.eval c s = some false) e Q) :
    RelCT isa (Two Φ) (.ite c t e) Q :=
  RelCT.ite (fun _ _ ⟨a, h₁, h₂, _⟩ => hag a _ _ h₁ h₂) (two_cond hag ht) (two_cond hag he)

theorem two_mono {α : Type} {Φ Ψ : α → State → Prop} {p : Prog isa} {Q : State → State → Prop}
    (hm : ∀ a s, Φ a s → Ψ a s) (h : RelCT isa (Two Ψ) p Q) : RelCT isa (Two Φ) p Q :=
  h.mono (fun _ _ ⟨a, h₁, h₂, hsp⟩ => ⟨a, hm a _ h₁, hm a _ h₂, hsp⟩) fun _ _ h => h

/-- The registers of `Env` agree for calls with the same public data. -/
theorem env_agree {a : CD} {s0 s0' s s' : State} {Z Z' : Nat} (k : KRel a s0) (k' : KRel a s0')
    (e : Env s (sB s0) Z (cw s0)) (e' : Env s' (sB s0') Z' (cw s0')) :
    ∀ r ∈ [Reg.r31, .r10, .r11, .r29], s.gpr r = s'.gpr r := by
  have hB : sB s0 = sB s0' := k.arg k' (i := 1) (by decide)
  have hw : cw s0 = cw s0' := by simp only [cw, k.oL_eq k']
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [e.h31, e'.h31, hB]
  · rw [e.h10, e'.h10, hB, hw]
  · rw [e.h11, e'.h11, hw]
  · rw [e.h29, e'.h29, hw]

/-! ## The loop's context -/

/-- The call from `s0`, and its witnesses' loop from `sL`. -/
structure LCtx (a : CD) (s0 sL : State) : Prop where
  krel : KRel a s0
  t3 : T3 s0 (cw s0) (candOf s0) sL
  ncl : Spec.RsaKeyGen.tooClose (64 * cw s0) (Spec.RsaKeyGen.otherPrime (pB s0)) (candOf s0) = false
  gcd : Nat.gcd (candOf s0 - 1) (Spec.Rsa.os2ip (eB s0)) = 1

/-- The loop's `(a, m)`. -/
abbrev lA (s0 : State) : Nat := (Spec.Rsa.splitTwos (candOf s0 - 1)).1
abbrev lM (s0 : State) : Nat := (Spec.Rsa.splitTwos (candOf s0 - 1)).2

/-- After `k` witnesses passed, `n + 1` iterations left. -/
def LI (n : Nat) (ak : CD × Nat) (s : State) : Prop :=
  ∃ s0 q, LCtx ak.1 s0 q ∧
    MrAt (candOf s0) (VG.Proof.RsaKeyGen.checksW (cw s0)) (lA s0) (lM s0) (8 * cw s0) (rB s0) ak.2 n ∧
    St q (sB s0) (sL s0) (cw s0) (candOf s0) (rB s0) ak.2 s

theorem candS_eq {s0 : State} (hp : CIn s0) (hav : oL s0 ≤ rL s0) : candS s0 = candOf s0 := by
  obtain ⟨hw, -, -⟩ := cw_facts hp
  unfold candS candOf rB
  rw [take_bytesAt _ _ hav, hw, show 8 * (8 * cw s0) = 64 * cw s0 by omega_using []]

theorem LCtx.hav {a : CD} {s0 sL : State} (C : LCtx a s0 sL) : oL s0 ≤ rL s0 := by
  rw [C.t3.tc.hw]; exact C.t3.tc.h8

theorem shape_eq {a : CD} {s0 s0' sL sL' : State} (C : LCtx a s0 sL) (C' : LCtx a s0' sL') :
    VG.Proof.RsaKeyGen.shapeOf (Spec.RsaKeyGen.primalityTest (candOf s0) ((rB s0).drop (8 * cw s0))) =
      VG.Proof.RsaKeyGen.shapeOf (Spec.RsaKeyGen.primalityTest (candOf s0') ((rB s0').drop (8 * cw s0'))) := by
  have hp := C.krel.1
  have hp' := C'.krel.1
  have hav := C.hav
  have hav' := C'.hav
  obtain ⟨hw, -, -⟩ := cw_facts hp
  obtain ⟨hw', -, -⟩ := cw_facts hp'
  have e := shape_agree C.krel C'.krel hav
    (by rw [candS_eq hp hav, show 8 * oL s0 = 64 * cw s0 by omega_using [hw]]; exact C.ncl)
    (by rw [candS_eq hp hav, show 8 * oL s0 = 64 * cw s0 by omega_using [hw]]; exact C.t3.noc)
    (by rw [candS_eq hp hav]; exact C.gcd)
  rwa [candS_eq hp hav, candS_eq hp' hav', hw, hw'] at e

theorem rB_len (s0 : State) : (rB s0).length = rL s0 := bytesAt_length _ _ _

/-- The witness at offset `u` passes in both runs or in neither. -/
theorem pass_agree {a : CD} {s0 s0' sL sL' : State} {k n : Nat} (C : LCtx a s0 sL) (C' : LCtx a s0' sL')
    (ha : MrAt (candOf s0) (VG.Proof.RsaKeyGen.checksW (cw s0)) (lA s0) (lM s0) (8 * cw s0) (rB s0) k n)
    (ha' : MrAt (candOf s0') (VG.Proof.RsaKeyGen.checksW (cw s0')) (lA s0') (lM s0') (8 * cw s0') (rB s0') k n)
    (hav : 8 * cw s0 * (k + 1) + 8 * cw s0 ≤ (rB s0).length) :
    Spec.RsaKeyGen.mrIteration (candOf s0) (lA s0) (lM s0) (wit (candOf s0) (8 * cw s0) (rB s0)
        (8 * cw s0 * (k + 1))).1 =
      Spec.RsaKeyGen.mrIteration (candOf s0') (lA s0') (lM s0') (wit (candOf s0') (8 * cw s0') (rB s0')
        (8 * cw s0' * (k + 1))).1 := by
  have hp := C.krel.1
  have hp' := C'.krel.1
  have hw : cw s0 = cw s0' := by simp only [cw, C.krel.oL_eq C'.krel]
  have hl : (rB s0).length = (rB s0').length := by rw [rB_len, rB_len, C.krel.rL_eq C'.krel]
  obtain ⟨-, hw4, -⟩ := cw_facts hp
  obtain ⟨-, -, hwb⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega_using [hw4] : 1 ≤ cw s0) C.t3.tc.shape
  obtain ⟨-, -, hwb'⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega : 1 ≤ cw s0') C'.t3.tc.shape
  have p₁ := VG.Proof.RsaKeyGen.mr_pass (a := lA s0) (m := lM s0) (r := rB s0) (used := 8 * cw s0 * (k + 1))
    ha.go hwb (by omega_using [hw4]) hav
  have p₂ := VG.Proof.RsaKeyGen.mr_pass (a := lA s0') (m := lM s0') (r := rB s0') (used := 8 * cw s0' * (k + 1))
    ha'.go hwb' (by omega)
    (by rw [← hw, ← hl]; exact hav)
  have l₁ : VG.Proof.RsaKeyGen.shapeOf (Spec.RsaKeyGen.loop (Spec.RsaKeyGen.mrStep (candOf s0)
      (VG.Proof.RsaKeyGen.checksW (cw s0)) (lA s0) (lM s0)) ((mrS (candOf s0) (8 * cw s0) (rB s0) k).1,
      (mrS (candOf s0) (8 * cw s0) (rB s0) k).2) ((rB s0).drop (8 * cw s0 * (k + 1)))) =
      VG.Proof.RsaKeyGen.shapeOf (Spec.RsaKeyGen.primalityTest (candOf s0) ((rB s0).drop (8 * cw s0))) := by
    rw [ha.loop]
  have l₂ : VG.Proof.RsaKeyGen.shapeOf (Spec.RsaKeyGen.loop (Spec.RsaKeyGen.mrStep (candOf s0')
      (VG.Proof.RsaKeyGen.checksW (cw s0')) (lA s0') (lM s0')) ((mrS (candOf s0') (8 * cw s0') (rB s0') k).1,
      (mrS (candOf s0') (8 * cw s0') (rB s0') k).2) ((rB s0').drop (8 * cw s0' * (k + 1)))) =
      VG.Proof.RsaKeyGen.shapeOf (Spec.RsaKeyGen.primalityTest (candOf s0') ((rB s0').drop (8 * cw s0'))) := by
    rw [ha'.loop]
  rw [l₁] at p₁
  rw [l₂] at p₂
  unfold wit
  rw [← p₁, ← p₂, shape_eq C C', hl, hw]

/-- The loop goes on in both runs or in neither. -/
theorem mc_agree {a : CD} {s0 s0' sL sL' : State} {k n : Nat} (C : LCtx a s0 sL) (C' : LCtx a s0' sL')
    (ha : MrAt (candOf s0) (VG.Proof.RsaKeyGen.checksW (cw s0)) (lA s0) (lM s0) (8 * cw s0) (rB s0) k n)
    (ha' : MrAt (candOf s0') (VG.Proof.RsaKeyGen.checksW (cw s0')) (lA s0') (lM s0') (8 * cw s0') (rB s0') k n) :
    MC (candOf s0) (cw s0) (rB s0) k n ↔ MC (candOf s0') (cw s0') (rB s0') k n := by
  have hw : cw s0 = cw s0' := by simp only [cw, C.krel.oL_eq C'.krel]
  have hl : (rB s0).length = (rB s0').length := by rw [rB_len, rB_len, C.krel.rL_eq C'.krel]
  unfold MC
  constructor
  · rintro ⟨hav, hp, hn⟩
    refine ⟨by rw [← hw, ← hl]; exact hav, ?_, hn⟩
    rw [← pass_agree C C' ha ha' hav]; exact hp
  · rintro ⟨hav, hp, hn⟩
    have hav₁ : 8 * cw s0 * (k + 1) + 8 * cw s0 ≤ (rB s0).length := by rw [hw, hl]; exact hav
    refine ⟨hav₁, ?_, hn⟩
    rw [pass_agree C C' ha ha' hav₁]; exact hp

end VG.Proof.RsaKeyGen.PPC64LE.Cand

end

end

/-!
# A candidate on PPC64LE: a draw in constant time

`draw_ct`: two runs of a draw, from the same iteration of the loop, leak the
same trace. The taint analysis checks each piece from the registers the
correctness proofs pin (the working space's and the tape's addresses, the
lengths); the round is a call of verified code (`RelCT.call`), and whether
its witness passed is the same in both runs (`pass_agree`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search (ldh sth hStat roundCall regsBack minv32)
open VG.Impl.RsaKeyGen.PPC64LE.Witness (draw load witness passed)
open VG.Proof.MillerRabin.PPC64LE (Env arr RoundImpl)
open VG.Proof.MillerRabin.PPC64LE.Search (RcPost)
open VG.Proof.Bignum (slot)
open VG.Proof.RsaKeyGen (MrAt mrS wit)

/-- The loop's facts at a draw's start `sD`, `k` witnesses passed, `n + 1`
iterations left, with enough octets. -/
structure DCtx (n : Nat) (a : CD) (k : Nat) (s0 q sD : State) : Prop where
  lc : LCtx a s0 q
  ha : MrAt (candOf s0) (VG.Proof.RsaKeyGen.checksW (cw s0)) (lA s0) (lM s0) (8 * cw s0) (rB s0) k n
  st : St q (sB s0) (sL s0) (cw s0) (candOf s0) (rB s0) k sD
  av : 8 * cw s0 * (k + 1) + 8 * cw s0 ≤ (rB s0).length

theorem DCtx.drIn {n k : Nat} {a : CD} {s0 q sD : State} (h : DCtx n a k s0 q sD) :
    DrIn sD (sB s0) (s0.gpr .r10) (sL s0) (cw s0) (candOf s0) (8 * cw s0 * (k + 1))
      (mrS (candOf s0) (8 * cw s0) (rB s0) k).1 (mrS (candOf s0) (8 * cw s0) (rB s0) k).2
      (VG.Proof.RsaKeyGen.checksW (cw s0)) :=
  drIn_of h.lc.t3.lin h.st h.av

/-- A draw's start. -/
def LD (n : Nat) (ak : CD × Nat) (s : State) : Prop := ∃ s0 q, DCtx n ak.1 ak.2 s0 q s

/-- After `load`'s first block. -/
def LL1 (n : Nat) (ak : CD × Nat) (s : State) : Prop :=
  ∃ s0 q sD, DCtx n ak.1 ak.2 s0 q sD ∧ s.gpr .r12 = off (s0.gpr .r10) (8 * cw s0 * (ak.2 + 1)) ∧
    s.gpr .r6 = BitVec.ofNat 64 (8 * cw s0) ∧ s.gpr .r10 = off (sB s0) (slot (cw s0) 4) ∧
    s.gpr .r11 = sD.gpr .r11 ∧ s.gpr .r31 = sD.gpr .r31

/-- After `load`. -/
def LW (n : Nat) (ak : CD × Nat) (s : State) : Prop :=
  ∃ s0 q sD, DCtx n ak.1 ak.2 s0 q sD ∧
    DrL sD (sB s0) (s0.gpr .r10) (sL s0) (cw s0) (8 * cw s0 * (ak.2 + 1)) s

/-- At the round's start. -/
def LR (n : Nat) (ak : CD × Nat) (s : State) : Prop :=
  ∃ s0 q sD, DCtx n ak.1 ak.2 s0 q sD ∧
    PreRd sD (sB s0) (s0.gpr .r10) (sL s0) (cw s0) (candOf s0) (8 * cw s0 * (ak.2 + 1))
      (mrS (candOf s0) (8 * cw s0) (rB s0) ak.2).1 (mrS (candOf s0) (8 * cw s0) (rB s0) ak.2).2
      (VG.Proof.RsaKeyGen.checksW (cw s0)) s

/-- Where the round is called. -/
def LC (_n : Nat) (ak : CD × Nat) (s : State) : Prop :=
  ∃ s0, KRel ak.1 s0 ∧ CallIn s (sB s0) (sL s0) (cw s0) (candOf s0)

/-- After the round's call. -/
def LC' (_n : Nat) (ak : CD × Nat) (s : State) : Prop := ∃ s0, KRel ak.1 s0 ∧ s.gpr .r31 = sB s0

/-- After the round. -/
def LP (n : Nat) (ak : CD × Nat) (s : State) : Prop :=
  ∃ s0 q sD sR, DCtx n ak.1 ak.2 s0 q sD ∧
    RcPost sR (sB s0) (sL s0) (cw s0) (candOf s0) (drX sD.mem (s0.gpr .r10) (cw s0) (candOf s0)
      (8 * cw s0 * (ak.2 + 1))).1 s

theorem DCtx.cw_eq {n k : Nat} {a : CD} {s0 q sD s0' q' sD' : State} (h : DCtx n a k s0 q sD)
    (h' : DCtx n a k s0' q' sD') : cw s0 = cw s0' := by
  simp only [cw, h.lc.krel.oL_eq h'.lc.krel]

theorem DCtx.sB_eq {n k : Nat} {a : CD} {s0 q sD s0' q' sD' : State} (h : DCtx n a k s0 q sD)
    (h' : DCtx n a k s0' q' sD') : sB s0 = sB s0' := h.lc.krel.arg h'.lc.krel (i := 1) (by decide)

theorem pins_LD {n : Nat} : Pins (LD n) [.r31, .r10, .r29] := by
  rintro ⟨a, k⟩ s₁ s₂ ⟨s0, q, h⟩ ⟨s0', q', h'⟩ r hr
  have := env_agree h.lc.krel h'.lc.krel h.st.prep.env h'.st.prep.env
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact this _ (by simp)

theorem pins_LL1 {n : Nat} : Pins (LL1 n) [.r10, .r12, .r6, .r11, .r31] := by
  rintro ⟨a, k⟩ s₁ s₂ ⟨s0, q, sD, h, a12, a6, a10, a11, a31⟩ ⟨s0', q', sD', h', b12, b6, b10, b11, b31⟩ r hr
  have ea := env_agree h.lc.krel h'.lc.krel h.st.prep.env h'.st.prep.env
  have hw := h.cw_eq h'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [a10, b10, h.sB_eq h', hw]
  · rw [a12, b12, h.lc.krel.reg h'.lc.krel (r := .r10) (by decide), hw]
  · rw [a6, b6, hw]
  · rw [a11, b11]; exact ea _ (by simp)
  · rw [a31, b31]; exact ea _ (by simp)

theorem pins_LW {n : Nat} : Pins (LW n) [.r10, .r11, .r29, .r31] := by
  rintro ⟨a, k⟩ s₁ s₂ ⟨s0, q, sD, h, ⟨⟨-, -, e, -⟩, -⟩⟩ ⟨s0', q', sD', h', ⟨⟨-, -, e', -⟩, -⟩⟩ r hr
  have := env_agree h.lc.krel h'.lc.krel e e'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact this _ (by simp)

theorem pins_LR {n : Nat} : Pins (LR n) [.r10, .r11, .r29, .r31] := by
  rintro ⟨a, k⟩ s₁ s₂ ⟨s0, q, sD, h, p⟩ ⟨s0', q', sD', h', p'⟩ r hr
  have := env_agree h.lc.krel h'.lc.krel p.prep.env p'.prep.env
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact this _ (by simp)

theorem pins_LC' {n : Nat} : Pins (LC' n) [.r31] := by
  rintro ⟨a, k⟩ s₁ s₂ ⟨s0, k₁, h₁⟩ ⟨s0', k₂, h₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [h₁, h₂]; exact k₁.arg k₂ (i := 1) (by decide)

theorem pins_LP {n : Nat} : Pins (LP n) [.r31] := by
  rintro ⟨a, k⟩ s₁ s₂ ⟨s0, q, sD, sR, h, p⟩ ⟨s0', q', sD', sR', h', p'⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [p.prep.env.h31, p'.prep.env.h31]; exact h.sB_eq h'

/-! ## The pieces -/

theorem load_ct {n : Nat} : RelCT isa (Two (LD n)) load fun _ _ => True := by
  unfold load
  refine RelCT.seq (two_post (Ψ := LL1 n) (two_taint _ pins_LD (by taint_decide)) fun ⟨a, k⟩ s ⟨s0, q, h⟩ => ?_)
    (two_taint _ pins_LL1 (by taint_decide))
  have d := h.drIn
  exact WP.mono (load1_wp d.prep.env d.rand d.used d.kk) fun t ⟨a12, a6, a10, a11, a31⟩ =>
    ⟨s0, q, s, h, a12, a6, a10, a11, a31⟩

theorem witness_ct {n : Nat} : RelCT isa (Two (LW n)) witness fun _ _ => True :=
  two_taint _ pins_LW (by taint_decide)

theorem pins_and {α : Type} {Φ : α → State → Prop} {X : α → State → Prop} {rs : List Reg} (h : Pins Φ rs) :
    Pins (fun a s => Φ a s ∧ X a s) rs := fun a _ _ h₁ h₂ => h a _ _ h₁.1 h₂.1

/-- The round's call. -/
theorem call_ct (R : RoundImpl) {n : Nat} : RelCT isa (Two (LC n)) (.call R.name R.code) fun _ _ => True := by
  refine RelCT.callEx R.verified.1 R.verified.2.1 fun s₁ s₂ ⟨⟨a, k⟩, ⟨s0, k₁, c₁⟩, ⟨s0', k₂, c₂⟩, hsp⟩ => ?_
  have hB : sB s0 = sB s0' := k₁.arg k₂ (i := 1) (by decide)
  have hL : sL s0 = sL s0' := by simp only [sL, k₁.arg k₂ (i := 2) (by decide)]
  have hw : cw s0 = cw s0' := by simp only [cw, k₁.oL_eq k₂]
  rw [hB, hL, hw] at c₁
  refine ⟨[], [⟨sB s0', 8 * sL s0'⟩], [], [⟨sB s0', 8 * sL s0'⟩], c₁.pre, c₂.pre, c₁.pub c₂ hsp, ?_, ?_, ?_, ?_⟩
  · exact fun x n ⟨r, hr, hc⟩ => ⟨r, List.mem_append_right _ (by
      simp only [List.nil_append, List.mem_singleton] at hr; rw [hr]; exact c₁.wr), hc⟩
  · exact fun x n ⟨r, hr, hc⟩ => ⟨r, by rw [List.mem_singleton] at hr; rw [hr]; exact c₁.wr, hc⟩
  · exact fun x n ⟨r, hr, hc⟩ => ⟨r, List.mem_append_right _ (by
      simp only [List.nil_append, List.mem_singleton] at hr; rw [hr]; exact c₂.wr), hc⟩
  · exact fun x n ⟨r, hr, hc⟩ => ⟨r, by rw [List.mem_singleton] at hr; rw [hr]; exact c₂.wr, hc⟩

theorem roundCall_ct (R : RoundImpl) {n : Nat} :
    RelCT isa (Two (LR n)) (roundCall R.name R.code) fun _ _ => True := by
  unfold roundCall
  refine RelCT.assoc (RelCT.assoc (RelCT.seq (two_post (Ψ := LC n) (two_taintR _ pins_LR (by taint_decide_rel))
    fun ⟨a, k⟩ s ⟨s0, q, sD, h, p⟩ => WP.mono (preCall_wp p.prep p.wr p.sp p.stk) fun t ht =>
      ⟨s0, h.lc.krel, ht⟩) (RelCT.seq (two_post (Ψ := LC' n) (call_ct R) fun ⟨a, k⟩ s ⟨s0, k₀, c⟩ =>
      WP.mono (call_wp R c) fun t ht => ⟨s0, k₀, ht.trans c.prep.env.h31⟩)
    (two_taint _ pins_LC' (by taint_decide)))))

theorem pass_eval {n : Nat} : ∀ (ak : CD × Nat) (s₁ s₂ : State), LP n ak s₁ → LP n ak s₂ →
    isa.eval (.zero .d .r3) s₁ = isa.eval (.zero .d .r3) s₂ := by
  rintro ⟨a, k⟩ s₁ s₂ ⟨s0, q, sD, sR, h, p⟩ ⟨s0', q', sD', sR', h', p'⟩
  rw [eval_zero_ofNat _ _ (by split <;> decide) p.r3, eval_zero_ofNat _ _ (by split <;> decide) p'.r3]
  have e₁ : drX sD.mem (s0.gpr .r10) (cw s0) (candOf s0) (8 * cw s0 * (k + 1)) =
      wit (candOf s0) (8 * cw s0) (rB s0) (8 * cw s0 * (k + 1)) := drX_eq h.lc.t3.lin h.st h.av
  have e₂ : drX sD'.mem (s0'.gpr .r10) (cw s0') (candOf s0') (8 * cw s0' * (k + 1)) =
      wit (candOf s0') (8 * cw s0') (rB s0') (8 * cw s0' * (k + 1)) := drX_eq h'.lc.t3.lin h'.st h'.av
  rw [e₁, e₂, round_eq, round_eq, pass_agree h.lc h'.lc h.ha h'.ha h.av]

theorem round_ct (R : RoundImpl) {n : Nat} :
    RelCT isa (Two (LR n)) (VG.Impl.RsaKeyGen.PPC64LE.Witness.round R.name R.code) fun _ _ => True := by
  unfold VG.Impl.RsaKeyGen.PPC64LE.Witness.round
  refine RelCT.seq (two_post (Ψ := LP n) (roundCall_ct R) fun ⟨a, k⟩ s ⟨s0, q, sD, h, p⟩ =>
    WP.mono (VG.Proof.MillerRabin.PPC64LE.Search.roundCall_ok R p.prep p.a4 p.ac p.sp p.stk) fun t ht =>
      ⟨s0, q, sD, s, h, ht⟩) (two_ite pass_eval ?_ ?_)
  · exact two_taint _ (pins_and pins_LP) (by taint_decide)
  · exact two_taint _ (pins_and pins_LP) (by taint_decide)

theorem draw_ct (R : RoundImpl) {n : Nat} : RelCT isa (Two (LD n)) (draw R.name R.code) fun _ _ => True := by
  unfold draw
  exact RelCT.seq (two_post (Ψ := LW n) load_ct fun ⟨a, k⟩ s ⟨s0, q, h⟩ =>
    WP.mono (loadS h.drIn) fun t ht => ⟨s0, q, s, h, ht⟩)
    (RelCT.seq (two_post (Ψ := LR n) witness_ct fun ⟨a, k⟩ s ⟨s0, q, sD, h, hl⟩ =>
      WP.mono (witS h.drIn hl) fun t ht => ⟨s0, q, sD, h, ht⟩) (round_ct R))

end VG.Proof.RsaKeyGen.PPC64LE.Cand

end

end

/-!
# A candidate on PPC64LE: the witnesses' loop in constant time

`mr_ct`: two runs of `Witness.millerRabin` from the same public data leak
the same trace. Each iteration (`iter_ct`) tests the octets left (the same in
both runs: the same iteration), draws (`draw_ct`) and tests its status,
whose result `mc_agree` makes the same in both runs; the loop is then
`RelCT.loop` over the iterations left, which the shape of the test's result
fixes for both runs.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search (ldh sth hStat)
open VG.Proof.MillerRabin.PPC64LE (Env arr RoundImpl)
open VG.Proof.Bignum (slot)
open VG.Proof.RsaKeyGen (MrAt mrS wit)

/-- After the test of octets left. -/
def LB (n : Nat) (ak : CD × Nat) (s : State) : Prop :=
  ∃ s0 q, LCtx ak.1 s0 q ∧
    MrAt (candOf s0) (VG.Proof.RsaKeyGen.checksW (cw s0)) (lA s0) (lM s0) (8 * cw s0) (rB s0) ak.2 n ∧
    St q (sB s0) (sL s0) (cw s0) (candOf s0) (rB s0) ak.2 s ∧
    s.gpr .r5 = BitVec.ofNat 64 (if 8 * cw s0 ≤ rL s0 - 8 * cw s0 * (ak.2 + 1) then 1 else 0)

/-- After the draw, or the loop's end for want of octets. -/
def LM (n : Nat) (ak : CD × Nat) (s : State) : Prop :=
  ∃ s0 q, LCtx ak.1 s0 q ∧
    MrAt (candOf s0) (VG.Proof.RsaKeyGen.checksW (cw s0)) (lA s0) (lM s0) (8 * cw s0) (rB s0) ak.2 n ∧
    Mid q (sB s0) (sL s0) (cw s0) (candOf s0) (rL s0) (VG.Proof.RsaKeyGen.checksW (cw s0)) (rB s0) ak.2 n s

/-- After the test of the status. -/
def LT (n : Nat) (ak : CD × Nat) (s : State) : Prop :=
  ∃ s0 q, LCtx ak.1 s0 q ∧
    MrAt (candOf s0) (VG.Proof.RsaKeyGen.checksW (cw s0)) (lA s0) (lM s0) (8 * cw s0) (rB s0) ak.2 n ∧
    Tl q (sB s0) (sL s0) (cw s0) (candOf s0) (rL s0) (VG.Proof.RsaKeyGen.checksW (cw s0)) (rB s0) ak.2 n s

theorem pins_LI {n : Nat} : Pins (LI n) [.r31] := by
  rintro ⟨a, k⟩ s₁ s₂ ⟨s0, q, C, -, hi⟩ ⟨s0', q', C', -, hi'⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  exact env_agree C.krel C'.krel hi.prep.env hi'.prep.env _ (by simp)

theorem pins_LB {n : Nat} : Pins (LB n) [.r31] := by
  rintro ⟨a, k⟩ s₁ s₂ ⟨s0, q, C, -, hi, -⟩ ⟨s0', q', C', -, hi', -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  exact env_agree C.krel C'.krel hi.prep.env hi'.prep.env _ (by simp)

theorem Mid.h31 {s t : State} {B : Addr} {L w c rl ch : Nat} {r : Spec.RsaKeyGen.Rand} {k n : Nat}
    (h : Mid s B L w c rl ch r k n t) : t.gpr .r31 = B := by
  rcases h with ⟨-, -, hi⟩ | ⟨-, -, -, -, ho⟩
  · exact hi.prep.env.h31
  · exact ho.prep.env.h31

theorem pins_LM {n : Nat} : Pins (LM n) [.r31] := by
  rintro ⟨a, k⟩ s₁ s₂ ⟨s0, q, C, -, hm⟩ ⟨s0', q', C', -, hm'⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [hm.h31, hm'.h31]; exact C.krel.arg C'.krel (i := 1) (by decide)

theorem avail_eval {n : Nat} : ∀ (ak : CD × Nat) (s₁ s₂ : State), LB n ak s₁ → LB n ak s₂ →
    isa.eval (.zero .d .r5) s₁ = isa.eval (.zero .d .r5) s₂ := by
  rintro ⟨a, k⟩ s₁ s₂ ⟨s0, q, C, -, -, a5⟩ ⟨s0', q', C', -, -, a5'⟩
  rw [eval_zero_ofNat _ _ (by split <;> decide) a5, eval_zero_ofNat _ _ (by split <;> decide) a5']
  have hw : cw s0 = cw s0' := by simp only [cw, C.krel.oL_eq C'.krel]
  simp only [hw, C.krel.rL_eq C'.krel]

/-- One iteration. -/
theorem iter_ct (R : RoundImpl) (n : Nat) :
    RelCT isa (Two (LI n)) (.seq (.block availB) (.seq (drawI R) (.block tailB))) fun s₁ s₂ =>
      isa.eval (.zero .d .r3) s₁ = isa.eval (.zero .d .r3) s₂ ∧
        (isa.eval (.zero .d .r3) s₁ = some false → True) ∧
        (isa.eval (.zero .d .r3) s₁ = some true → ∃ m < n, Two (LI m) s₁ s₂) := by
  refine RelCT.seq (two_post (Ψ := LB n) (two_taint _ pins_LI (by taint_decide))
    fun ⟨a, k⟩ s ⟨s0, q, C, ha, hi⟩ => WP.mono (availS C.t3.lin ha hi) fun t ⟨h₁, a5⟩ =>
      ⟨s0, q, C, ha, h₁, a5⟩) (RelCT.seq (two_post (Ψ := LM n) (two_ite avail_eval
        (two_taint _ (pins_and pins_LB) (by taint_decide))
        (two_mono (Ψ := LD n) (fun ⟨a, k⟩ s ⟨⟨s0, q, C, ha, hi, a5⟩, ev⟩ => ⟨s0, q, C, ha, hi, ?_⟩) (draw_ct R)))
      fun ⟨a, k⟩ s ⟨s0, q, C, ha, hi, a5⟩ => WP.mono (mid_ok R C.t3.lin ha hi a5) fun t hm =>
        ⟨s0, q, C, ha, hm⟩) ?_)
  · dsimp only at a5 ⊢
    have hw4 := C.t3.prep.env.hw
    rw [eval_zero_ofNat _ _ (by split <;> decide) a5] at ev
    simp only [Option.some.injEq, decide_eq_false_iff_not] at ev
    rw [rB_len]
    split at ev
    · omega_arith
    · exact absurd rfl ev
  · refine (two_post (Ψ := LT n) (two_taint _ pins_LM (by taint_decide)) fun ⟨a, k⟩ s ⟨s0, q, C, ha, hm⟩ =>
      WP.mono (tailS hm) fun t ht => ⟨s0, q, C, ha, ht⟩).mono (fun _ _ h => h) ?_
    rintro s₁ s₂ ⟨⟨a, k⟩, ⟨s0, q, C, ha, ht⟩, ⟨s0', q', C', ha', ht'⟩, hsp⟩
    have hm := mc_agree C C' ha ha'
    rcases ht with ⟨hc, ev, ha1, hi1⟩ | ⟨hc, ev, -⟩ <;> rcases ht' with ⟨hc', ev', ha1', hi1'⟩ | ⟨hc', ev', -⟩
    · refine ⟨by rw [ev, ev'], fun _ => trivial, fun _ => ⟨n - 1, by have := hc.2.2; omega_using [this], (a, k + 1),
        ⟨s0, q, C, ha1, hi1⟩, ⟨s0', q', C', ha1', hi1'⟩, hsp⟩⟩
    · exact absurd (hm.mp hc) hc'
    · exact absurd (hm.mpr hc') hc
    · exact ⟨by rw [ev, ev'], fun _ => trivial, fun h => by rw [ev] at h; cases h⟩

/-- The loop's start: the working space prepared, from `s0`. -/
def L3 (a : CD) (s : State) : Prop := ∃ s0, LCtx a s0 s

/-- After the loop's counts are set up. -/
def L0 (a : CD) (t : State) : Prop :=
  ∃ s0 q, LCtx a s0 q ∧ St q (sB s0) (sL s0) (cw s0) (candOf s0) (rB s0) 0 t

/-- The iterations of the loop, `1` less. -/
def n0 (s0 : State) : Nat :=
  VG.Proof.RsaKeyGen.itersOf (8 * cw s0) (rB s0).length
    (VG.Proof.RsaKeyGen.shapeOf (Spec.RsaKeyGen.primalityTest (candOf s0) ((rB s0).drop (8 * cw s0))))
    (8 * cw s0) - 1

theorem LCtx.mrAt0 {a : CD} {s0 q : State} (C : LCtx a s0 q) :
    MrAt (candOf s0) (VG.Proof.RsaKeyGen.checksW (cw s0)) (lA s0) (lM s0) (8 * cw s0) (rB s0) 0 (n0 s0) := by
  have P := C.t3.lin
  have hw4 := C.t3.prep.env.hw
  obtain ⟨_, _, hwb⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega_using [hw4] : 1 ≤ cw s0) P.shape
  have hrl := rB_len s0
  have h8 := C.t3.tc.h8
  have hc := VG.Proof.RsaKeyGen.primalityTest_cand (by omega_using [hw4]) P.shape ((rB s0).drop (8 * cw s0))
  rw [← P.hch] at hc
  exact VG.Proof.RsaKeyGen.mrAt_zero hc hwb (by omega_using [hw4]) (by omega_using [hrl, h8])

theorem n0_eq {a : CD} {s0 s0' q q' : State} (C : LCtx a s0 q) (C' : LCtx a s0' q') : n0 s0 = n0 s0' := by
  have hw : cw s0 = cw s0' := by simp only [cw, C.krel.oL_eq C'.krel]
  unfold n0
  rw [shape_eq C C', rB_len, rB_len, C.krel.rL_eq C'.krel, hw]

theorem pins_L3 : Pins L3 [.r31] := by
  rintro a s₁ s₂ ⟨s0, C⟩ ⟨s0', C'⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  exact env_agree C.krel C'.krel C.t3.prep.env C'.t3.prep.env _ (by simp)

/-- The witnesses' loop. -/
theorem mr_ct (R : RoundImpl) :
    RelCT isa (Two L3) (VG.Impl.RsaKeyGen.PPC64LE.Witness.millerRabin R.name R.code) fun _ _ => True := by
  unfold VG.Impl.RsaKeyGen.PPC64LE.Witness.millerRabin
  refine RelCT.seq ((two_post (Ψ := L0) (two_taint _ pins_L3 (by taint_decide)) fun a s ⟨s0, C⟩ =>
    WP.mono (init_ok C.t3.prep C.t3.hu0) fun t ht => ⟨s0, s, C, ht⟩).mono (fun _ _ h => h)
      (fun s₁ s₂ ⟨a, ⟨s0, q, C, h₁⟩, ⟨s0', q', C', h₂⟩, hsp⟩ => ⟨n0 s0, (a, 0), ⟨s0, q, C, C.mrAt0, h₁⟩,
        ⟨s0', q', C', n0_eq C C' ▸ C'.mrAt0, h₂⟩, hsp⟩))
    (RelCT.exists_ fun n => RelCT.loop (fun n => Two (LI n)) (iter_ct R) n)

end VG.Proof.RsaKeyGen.PPC64LE.Cand

end

end

/-!
# A candidate on PPC64LE: the test in constant time

`test_ct`: two runs of the test (trial division, then Miller–Rabin), with
the same public data, leak the same trace: trial division by its own
constant time (`DivOk.ct`), from candidates its table divides alike
(`div_agree`); whether it found a divisor, and the test's result, are the
same in both runs (`comp_agree`, `shape_eq`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search (ldh sth hStat hUsed)
open VG.Impl.RsaKeyGen.PPC64LE.Candidate (test testResult trialDiv finish finNone finPrime hOut hOutLen testArgs
  hTrial)
open VG.Proof.MillerRabin.PPC64LE (Env arr RoundImpl)
open VG.Proof.Bignum (slot)

/-- What two runs share once the candidate passed `gcd(c − 1, e) = 1`. -/
structure GOk (a : CD) (s0 : State) : Prop where
  krel : KRel a s0
  ncl : Spec.RsaKeyGen.tooClose (64 * cw s0) (Spec.RsaKeyGen.otherPrime (pB s0)) (candOf s0) = false
  gcd : Nat.gcd (candOf s0 - 1) (Spec.Rsa.os2ip (eB s0)) = 1

theorem GOk.candS {a : CD} {s0 : State} (h : GOk a s0) (hav : oL s0 ≤ rL s0) : candS s0 = candOf s0 :=
  candS_eq h.krel.1 hav

theorem comp_agree' {a : CD} {s0 s0' : State} (h : GOk a s0) (h' : GOk a s0') (hav : oL s0 ≤ rL s0) :
    Spec.RsaKeyGen.obviouslyComposite (64 * cw s0) (candOf s0) =
      Spec.RsaKeyGen.obviouslyComposite (64 * cw s0') (candOf s0') := by
  have hav' : oL s0' ≤ rL s0' := by rw [← h.krel.oL_eq h'.krel, ← h.krel.rL_eq h'.krel]; exact hav
  obtain ⟨hw, -, -⟩ := cw_facts h.krel.1
  obtain ⟨hw', -, -⟩ := cw_facts h'.krel.1
  have e := comp_agree h.krel h'.krel hav
    (by rw [h.candS hav, show 8 * oL s0 = 64 * cw s0 by omega_using [hw]]; exact h.ncl)
  rwa [h.candS hav, h'.candS hav', hw, hw', show 8 * (8 * cw s0) = 64 * cw s0 by omega_using [],
    show 8 * (8 * cw s0') = 64 * cw s0' by omega_using []] at e

theorem comp_same' {a : CD} {s0 s0' : State} (h : GOk a s0) (h' : GOk a s0') (hav : oL s0 ≤ rL s0)
    (ho : Spec.RsaKeyGen.obviouslyComposite (64 * cw s0) (candOf s0) = true) : candOf s0 = candOf s0' := by
  have hav' : oL s0' ≤ rL s0' := by rw [← h.krel.oL_eq h'.krel, ← h.krel.rL_eq h'.krel]; exact hav
  obtain ⟨hw, -, -⟩ := cw_facts h.krel.1
  have e := comp_same h.krel h'.krel hav
    (by rw [h.candS hav, show 8 * oL s0 = 64 * cw s0 by omega_using [hw]]; exact h.ncl)
    (by rw [h.candS hav, show 8 * oL s0 = 64 * cw s0 by omega_using [hw]]; exact ho)
  rwa [h.candS hav, h'.candS hav'] at e

/-! ## Trial division -/

/-- After the test's arguments. -/
def TA (a : CD) (s : State) : Prop := ∃ s0, GOk a s0 ∧ T1 s0 (cw s0) (candOf s0) s

/-- Trial division's start: `out` and `out_len` saved. -/
def TD (a : CD) (s : State) : Prop :=
  ∃ s0 s1, GOk a s0 ∧ T1 s0 (cw s0) (candOf s0) s1 ∧
    s = { s1 with mem := (s1.mem.writeW (off (sB s0) 24) (s1.gpr .r23)).writeW (off (sB s0) 40) (s1.gpr .r24) }

/-- After trial division. -/
def TD' (a : CD) (s : State) : Prop := ∃ s0, GOk a s0 ∧ s.gpr .r31 = sB s0

/-- After it. -/
def TB (a : CD) (s : State) : Prop := ∃ s0, GOk a s0 ∧ T2 s0 (cw s0) (candOf s0) s

theorem pins_TIn : Pins (fun a s => ∃ s0, GOk a s0 ∧ TIn s0 s (cw s0) (candOf s0)) [.r31] := by
  rintro a s₁ s₂ ⟨s0, g, h⟩ ⟨s0', g', h'⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  exact env_agree g.krel g'.krel h.env h'.env _ (by simp)

theorem pins_TA : Pins TA [.r23, .r24, .r31] := by
  rintro a s₁ s₂ ⟨s0, g, h⟩ ⟨s0', g', h'⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h.ctx.r23, h'.ctx.r23]; exact g.krel.reg g'.krel (by decide)
  · rw [h.ctx.r24, h'.ctx.r24]; exact g.krel.reg g'.krel (by decide)
  · exact env_agree g.krel g'.krel h.env h'.env _ (by simp)

theorem pins_TD' : Pins TD' [.r31] := by
  rintro a s₁ s₂ ⟨s0, g, h⟩ ⟨s0', g', h'⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [h, h']; exact g.krel.arg g'.krel (i := 1) (by decide)

theorem TD.divIn {a : CD} {s : State} (h : TD a s) :
    ∃ s0, GOk a s0 ∧ DivIn s (sB s0) (8 * sL s0) (cw s0) (nTrial (cw s0)) ∧ arr s.mem (sB s0) (cw s0) 0 = candOf s0 ∧
      s.syms = s0.syms ∧ oL s0 ≤ rL s0 := by
  obtain ⟨s0, s1, g, h1, rfl⟩ := h
  have e := h1.env
  have hnw := e.hs.nowrap
  have hZ := e.hZ
  rw [slot_lin] at hZ
  have d1 := h1.divIn.write (s1.gpr .r23) (d := 24) (by omega_using []) (by simp only [hTrial]; omega_using []) h1.tabDj
  have d2 := d1.write (s1.gpr .r24) (d := 40) (by omega_using []) (by simp only [hTrial]; omega_using []) h1.tabDj
  refine ⟨s0, g, d2, ?_, h1.syms, by rw [h1.tc.hw]; exact h1.tc.h8⟩
  have o := ((writeW_outside s1.mem (sB s0) (d := 24) (s1.gpr .r23) (by omega_using [])).mono (o' := 24) (n' := 24) (by omega_using [])
    (by omega_using [])).trans ((writeW_outside (s1.mem.writeW (off (sB s0) 24) (s1.gpr .r23)) (sB s0) (d := 40)
      (s1.gpr .r24) (by omega_using [])).mono (o' := 24) (n' := 24) (by omega_using []) (by omega_using []))
  rw [← h1.arr0]
  exact o.val32 (by rw [slot_lin]; omega_using []) (by rw [slot_lin]; omega_using [hnw, hZ])

/-- Candidates the table divides alike. -/
theorem div_agree {a : CD} {s₁ s₂ : State} (h₁ : TD a s₁) (h₂ : TD a s₂) (hsp : s₁.sp = s₂.sp) : DivRel s₁ s₂ := by
  obtain ⟨s0, g, d, a0, sy, hav⟩ := h₁.divIn
  obtain ⟨s0', g', d', a0', sy', -⟩ := h₂.divIn
  have hw4 := d'.env.hw
  have hB : sB s0 = sB s0' := g.krel.arg g'.krel (i := 1) (by decide)
  have hL : sL s0 = sL s0' := by simp only [sL, g.krel.arg g'.krel (i := 2) (by decide)]
  have hw : cw s0 = cw s0' := by simp only [cw, g.krel.oL_eq g'.krel]
  rw [hB, hL, hw] at d
  rw [hB, hw] at a0
  refine ⟨sB s0', 8 * sL s0', cw s0', nTrial (cw s0'), d, d', hsp,
    by rw [sy, sy']; exact g.krel.sym g'.krel, fun i hi => ?_⟩
  rw [a0, a0']
  have c8 : ∀ {t : State}, GOk a t → 4 ≤ cw t → 8161 < candOf t := fun {t} gt h4 => by
    have := (VG.Proof.RsaKeyGen.candidate_shape (bits := 64 * cw t) (by omega_using [h4])
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (t.gpr .r10) (8 * cw t)))).2.1
    have : 2 ^ 14 ≤ 2 ^ (64 * cw t - 2) := Nat.pow_le_pow_right (by decide) (by omega_using [h4])
    show 8161 < Spec.RsaKeyGen.candidate (64 * cw t) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (t.gpr .r10) (8 * cw t)))
    omega_arith
  cases ho : Spec.RsaKeyGen.obviouslyComposite (64 * cw s0) (candOf s0)
  · have ho' := (comp_agree' g g' hav).symm.trans ho
    have none : ∀ {t : State}, GOk a t → 4 ≤ cw t →
        Spec.RsaKeyGen.obviouslyComposite (64 * cw t) (candOf t) = false →
        ∀ j < nTrial (cw t), VG.Proof.RsaKeyGen.entryDivides (candOf t) j = false := by
      intro t gt h4 hc j hj
      have hp := VG.Proof.RsaKeyGen.trialPrefix_spec (w := cw t) (c8 gt h4)
      rw [hc] at hp
      cases he : VG.Proof.RsaKeyGen.entryDivides (candOf t) j
      · rfl
      · rw [VG.Proof.RsaKeyGen.trialPrefix_hit hj he] at hp; cases hp
    rw [none g (by rw [hw]; exact hw4) ho i (by rw [hw]; exact hi), none g' hw4 ho' i hi]
  · rw [comp_same' g g' hav ho]

theorem pins_TD_r31 {a : CD} {s : State} (h : TD a s) : ∃ s0, GOk a s0 ∧ s.gpr .r31 = sB s0 := by
  obtain ⟨s0, s1, g, h1, rfl⟩ := h
  exact ⟨s0, g, h1.env.h31⟩

theorem trialDiv_ct {trial : Prog isa} (D : DivOk trial) :
    RelCT isa (Two TA) (trialDiv trial) fun _ _ => True := by
  unfold trialDiv
  refine RelCT.seq (two_post (Ψ := TD) (two_taint _ pins_TA (by taint_decide)) fun a s ⟨s0, g, h⟩ => ?_)
    (RelCT.seq (two_post (Ψ := TD') (D.ct (P := Two TD) fun s₁ s₂ ⟨a, h₁, h₂, hsp⟩ => div_agree h₁ h₂ hsp)
      fun a s hd => ?_) (two_taint _ pins_TD' (by taint_decide)))
  · have e := h.env
    have hs := e.hs
    have hnw := hs.nowrap
    have hZ := e.hZ
    rw [slot_lin] at hZ
    have hst : WP isa (.block [sth .r23 hOut, sth .r24 hOutLen]) s fun u =>
        u = { s with mem := (s.mem.writeW (off (sB s0) 24) (s.gpr .r23)).writeW (off (sB s0) 40) (s.gpr .r24) } := by
      simp only [sth, hOut, hOutLen]
      prun [e.h31, hs.st (d := 24) (n := 8) (by omega_using [hZ]), hs.st (d := 40) (n := 8) (by omega_using [hZ])]
    exact WP.mono hst fun u hu => ⟨s0, s, g, h, hu⟩
  · obtain ⟨s0, g, d, -, -, -⟩ := hd.divIn
    obtain ⟨s0', g', h31⟩ := pins_TD_r31 hd
    exact WP.mono (D.ok d) fun t ⟨_, _, hk, _⟩ => ⟨s0', g', (hk .r31 (by decide)).trans h31⟩

/-! ## The result -/

/-- The test's status, from what became of the candidate. -/
def stOf (s0 : State) : Nat :=
  match Spec.RsaKeyGen.primalityTest (candOf s0) ((rB s0).drop (8 * cw s0)) with
  | none => 0
  | some (b, _) => if b then 1 else 2

theorem stOf_shape (s0 : State) : stOf s0 = (VG.Proof.RsaKeyGen.shapeOf (Spec.RsaKeyGen.primalityTest (candOf s0)
    ((rB s0).drop (8 * cw s0)))).elim 0 fun x => if x.1 then 1 else 2 := by
  unfold stOf VG.Proof.RsaKeyGen.shapeOf
  rcases Spec.RsaKeyGen.primalityTest (candOf s0) ((rB s0).drop (8 * cw s0)) with _ | ⟨b, rest⟩ <;> rfl

theorem stOf_eq {a : CD} {s0 s0' q q' : State} (C : LCtx a s0 q) (C' : LCtx a s0' q') : stOf s0 = stOf s0' := by
  rw [stOf_shape, stOf_shape, shape_eq C C']

theorem T4.stat {s0 s : State} (h : T4 s0 (cw s0) (candOf s0) s) :
    word s.mem (sB s0) (8 * hStat) = BitVec.ofNat 64 (stOf s0) := by
  have r := h.res
  unfold stOf
  revert r
  rcases Spec.RsaKeyGen.primalityTest (candOf s0) ((rB s0).drop (8 * cw s0)) with _ | ⟨b, rest⟩
  · exact id
  · exact fun r => r.1

/-- After the witnesses. -/
def TR (a : CD) (s : State) : Prop := ∃ s0, (∃ q, LCtx a s0 q) ∧ T4 s0 (cw s0) (candOf s0) s

/-- The status in `r3`. -/
def R1 (a : CD) (t : State) : Prop :=
  ∃ s0, (∃ q, LCtx a s0 q) ∧ Ctx s0 t ∧ t.gpr .r31 = sB s0 ∧ t.gpr .r3 = BitVec.ofNat 64 (stOf s0)

/-- The status less one in `r3`. -/
def R2 (a : CD) (t : State) : Prop :=
  ∃ s0, (∃ q, LCtx a s0 q) ∧ Ctx s0 t ∧ t.gpr .r31 = sB s0 ∧
    t.gpr .r3 = BitVec.ofNat 64 (stOf s0) - BitVec.ofNat 64 1

theorem pins_TR : Pins TR [.r31] := by
  rintro a s₁ s₂ ⟨s0, ⟨q, C⟩, h⟩ ⟨s0', ⟨q', C'⟩, h'⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  exact env_agree C.krel C'.krel h.prep.env h'.prep.env _ (by simp)

theorem ctx_pins {a : CD} {s0 s0' s s' : State} (k : KRel a s0) (k' : KRel a s0') (c : Ctx s0 s) (c' : Ctx s0' s') :
    ∀ r ∈ [Reg.r23, .r24, .r25], s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [c.r23, c'.r23]; exact k.reg k' (by decide)
  · rw [c.r24, c'.r24]; exact k.reg k' (by decide)
  · rw [c.r25, c'.r25]; exact k.reg k' (by decide)

theorem pins_R1 : Pins R1 [.r23, .r24, .r25, .r31] := by
  rintro a s₁ s₂ ⟨s0, ⟨q, C⟩, c, h31, -⟩ ⟨s0', ⟨q', C'⟩, c', h31', -⟩ r hr
  have := ctx_pins C.krel C'.krel c c'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact this _ (by simp)
  · exact this _ (by simp)
  · exact this _ (by simp)
  · rw [h31, h31']; exact C.krel.arg C'.krel (i := 1) (by decide)

theorem pins_R2 : Pins R2 [.r23, .r24, .r25, .r31] := by
  rintro a s₁ s₂ ⟨s0, ⟨q, C⟩, c, h31, -⟩ ⟨s0', ⟨q', C'⟩, c', h31', -⟩ r hr
  have := ctx_pins C.krel C'.krel c c'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact this _ (by simp)
  · exact this _ (by simp)
  · exact this _ (by simp)
  · rw [h31, h31']; exact C.krel.arg C'.krel (i := 1) (by decide)

theorem stOf_lt (s0 : State) : stOf s0 < 3 := by
  unfold stOf
  split
  · decide
  · split <;> decide

theorem result_ct : RelCT isa (Two TR) testResult fun _ _ => True := by
  unfold testResult
  refine RelCT.seq (two_post (Ψ := R1) (two_taint _ pins_TR (by taint_decide)) fun a s ⟨s0, ⟨q, C⟩, h⟩ => ?_)
    (two_ite ?_ (two_taint _ (pins_and pins_R1) (by taint_decide))
      (RelCT.seq (two_post (Ψ := R2) (two_taint [] (fun _ _ _ _ _ _ hr => by simp at hr) (by taint_decide))
        fun a s ⟨⟨s0, CC, c, h31, h3⟩, _⟩ => ?_)
        (two_ite ?_ (two_taint _ (pins_and pins_R2) (by taint_decide))
          (two_taint _ (pins_and pins_R2) (by taint_decide)))))
  · have e := h.prep.env
    have hs := e.hs
    have hnw := hs.nowrap
    have hZ := e.hZ
    rw [slot_lin] at hZ
    exact WP.mono (WP.keep [.r28, .r3] (Q := fun t => t.gpr .r3 = word s.mem (sB s0) (8 * hStat) ∧
      t.mem = s.mem) (by
        simp only [ldh, hUsed, hStat]
        prun [e.h31, hs.ld (d := 152) (n := 8) (by omega_using [hZ]), hs.ld (d := 160) (n := 8) (by omega_using [hZ])]) (by decide))
      fun t ⟨⟨a3, m⟩, k⟩ => ⟨s0, ⟨q, C⟩, h.ctx.keep k m, (k.gpr _ (by decide)).trans e.h31, a3.trans h.stat⟩
  · rintro a s₁ s₂ ⟨s0, ⟨q, C⟩, -, -, h3⟩ ⟨s0', ⟨q', C'⟩, -, -, h3'⟩
    have := stOf_lt s0
    have := stOf_lt s0'
    rw [eval_zero_ofNat _ _ (by omega_arith) h3, eval_zero_ofNat _ _ (by omega_using [this]) h3', stOf_eq C C']
  · exact WP.mono (WP.keep [.r3] (Q := fun t => t.gpr .r3 = BitVec.ofNat 64 (stOf s0) - BitVec.ofNat 64 1 ∧
      t.mem = s.mem) (by prun [h3]) (by decide))
      fun t ⟨⟨a3, m⟩, k⟩ => ⟨s0, CC, c.keep k m, (k.gpr _ (by decide)).trans h31, a3⟩
  · rintro a s₁ s₂ ⟨s0, ⟨q, C⟩, -, -, h3⟩ ⟨s0', ⟨q', C'⟩, -, -, h3'⟩
    rw [eval_zero, eval_zero, h3, h3', stOf_eq C C']

/-! ## The test -/

/-- The test's start. -/
def TI (a : CD) (s : State) : Prop := ∃ s0, GOk a s0 ∧ TIn s0 s (cw s0) (candOf s0)

theorem pins_TB : Pins TB [.r10, .r11, .r29, .r31, .r25] := by
  rintro a s₁ s₂ ⟨s0, g, h⟩ ⟨s0', g', h'⟩ r hr
  have ea := env_agree g.krel g'.krel h.env h'.env
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ea _ (by simp)
  · exact ea _ (by simp)
  · exact ea _ (by simp)
  · exact ea _ (by simp)
  · rw [h.ctx.r25, h'.ctx.r25]; exact g.krel.reg g'.krel (by decide)

theorem comp_eval : ∀ (a : CD) (s₁ s₂ : State), TB a s₁ → TB a s₂ →
    isa.eval (.nonzero .d .r22) s₁ = isa.eval (.nonzero .d .r22) s₂ := by
  rintro a s₁ s₂ ⟨s0, g, h⟩ ⟨s0', g', h'⟩
  rw [eval_nonzero_ofNat' _ _ (by split <;> decide) h.f, eval_nonzero_ofNat' _ _ (by split <;> decide) h'.f,
    comp_agree' g g' (by rw [h.tc.hw]; exact h.tc.h8)]

theorem test_ct {trial : Prog isa} (D : DivOk trial) (R : RoundImpl) :
    RelCT isa (Two TI) (test trial R.name R.code) fun _ _ => True := by
  unfold test
  simp only [VG.Impl.RsaKeyGen.PPC64LE.Candidate.seqs]
  refine RelCT.seq (two_post (Ψ := TA) (two_taint _ pins_TIn (by taint_decide))
    fun a s ⟨s0, g, h⟩ => WP.mono (argsS h) fun t ht => ⟨s0, g, ht⟩)
    (RelCT.seq (two_post (Ψ := TB) (trialDiv_ct D) fun a s ⟨s0, g, h⟩ => WP.mono (trialS D h) fun t ht => ⟨s0, g, ht⟩)
      (two_ite comp_eval (two_taint _ (pins_and pins_TB) (by taint_decide))
        (RelCT.seq (two_post (Ψ := L3) (two_taintR _ (pins_and pins_TB) (by taint_decide_rel))
          fun a s ⟨⟨s0, g, h⟩, ev⟩ => ?_)
          (RelCT.seq (two_post (Ψ := TR) (mr_ct R) fun a s ⟨s0, C⟩ =>
            WP.mono (mrStage R C.t3) fun t ht => ⟨s0, ⟨s, C⟩, ht⟩) result_ct))))
  have hoc : Spec.RsaKeyGen.obviouslyComposite (64 * cw s0) (candOf s0) = false := by
    rw [eval_nonzero_ofNat' _ _ (by split <;> decide) h.f] at ev
    revert ev; cases Spec.RsaKeyGen.obviouslyComposite (64 * cw s0) (candOf s0) <;> decide
  exact WP.mono (prepS h hoc) fun t ht => ⟨s0, ⟨g.krel, ht, g.ncl, g.gcd⟩⟩

end VG.Proof.RsaKeyGen.PPC64LE.Cand

end

end

/-!
# A candidate on PPC64LE: the candidate in constant time

`main_ct`: two runs with the same public data, once `rand` holds a
candidate, leak the same trace. The taint analysis checks the setup, the
candidate's load and the test of its closeness to `p` from the pointers and
lengths; whether it is too close (`close_agree`) and whether
`gcd(c − 1, e) = 1` (`gcd_agree`) are the same in both runs, and
`gcdCheck`'s own branches depend on `e` alone, which the leak gives.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Candidate (main setup loadC closeCheck gcdCheck gcdE loadE finish)
open VG.Proof.MillerRabin.PPC64LE (Env arr RoundImpl)
open VG.Proof.Bignum (slot)

/-- A stage of `main`, from the call `s0`. -/
def SG (X : State → State → Prop) (a : CD) (s : State) : Prop := ∃ s0, KRel a s0 ∧ X s0 s

theorem pins_MIn : Pins (SG MIn) [.r11, .r24, .r31] := by
  rintro a s₁ s₂ ⟨s0, k, h⟩ ⟨s0', k', h'⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h.r11, h'.r11]; exact k.arg k' (by decide)
  · rw [h.ctx.r24, h'.ctx.r24]; exact k.reg k' (by decide)
  · rw [h.r31, h'.r31]; exact k.arg k' (by decide)

theorem pins_M1 : Pins (SG M1) [.r24, .r26, .r10, .r11, .r29, .r31] := by
  rintro a s₁ s₂ ⟨s0, k, h⟩ ⟨s0', k', h'⟩ r hr
  have ea := env_agree k k' h.env h'.env
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.ctx.r24, h'.ctx.r24]; exact k.reg k' (by decide)
  · rw [h.r26, h'.r26]; exact k.reg k' (by decide)
  all_goals exact ea _ (by simp)

theorem pins_M2 : Pins (SG M2) [.r18, .r19, .r24, .r10, .r11, .r29, .r31] := by
  rintro a s₁ s₂ ⟨s0, k, h⟩ ⟨s0', k', h'⟩ r hr
  have ea := env_agree k k' h.env h'.env
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.r18, h'.r18]; exact k.reg k' (by decide)
  · rw [h.r19, h'.r19]; exact k.reg k' (by decide)
  · rw [h.ctx.r24, h'.ctx.r24]; exact k.reg k' (by decide)
  all_goals exact ea _ (by simp)

theorem pins_M3 : Pins (SG M3) [.r21, .r30, .r25] := by
  rintro a s₁ s₂ ⟨s0, k, h⟩ ⟨s0', k', h'⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h.r21, h'.r21]; exact k.reg k' (by decide)
  · rw [h.r30, h'.r30]; exact k.reg k' (by decide)
  · rw [h.ctx.r25, h'.ctx.r25]; exact k.reg k' (by decide)

theorem pins_M4 : Pins (SG M4) [.r25] := by
  rintro a s₁ s₂ ⟨s0, k, h⟩ ⟨s0', k', h'⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [h.ctx.r25, h'.ctx.r25]; exact k.reg k' (by decide)

theorem close_eval : ∀ (a : CD) (s₁ s₂ : State), SG M3 a s₁ → SG M3 a s₂ →
    isa.eval (.nonzero .d .r22) s₁ = isa.eval (.nonzero .d .r22) s₂ := by
  rintro a s₁ s₂ ⟨s0, k, h⟩ ⟨s0', k', h'⟩
  rw [eval_nonzero_ofNat' _ _ (by split <;> decide) h.f, eval_nonzero_ofNat' _ _ (by split <;> decide) h'.f]
  have hav := h.hav
  have hav' := h'.hav
  obtain ⟨hw, -, -⟩ := cw_facts k.1
  obtain ⟨hw', -, -⟩ := cw_facts k'.1
  have e := close_agree k k' hav
  rw [candS_eq k.1 hav, candS_eq k'.1 hav', hw, hw', show 8 * (8 * cw s0) = 64 * cw s0 by omega_using [],
    show 8 * (8 * cw s0') = 64 * cw s0' by omega_using []] at e
  rw [e]

/-! ## `gcdCheck` -/

/-- `gcdCheck`'s states: `M3` with the registers `rs` changed. -/
def GS (rs : List Reg) (V : State → State → Prop) (a : CD) (t : State) : Prop :=
  ∃ s0 sM, KRel a s0 ∧ M3 s0 sM ∧
    Spec.RsaKeyGen.tooClose (64 * cw s0) (Spec.RsaKeyGen.otherPrime (pB s0)) (candOf s0) = false ∧
    Keep rs sM t ∧ V s0 t

theorem pins_GS {rs : List Reg} {V : State → State → Prop}
    (hr : ∀ r ∈ VG.Proof.MillerRabin.PPC64LE.envRegs, r ∉ rs := by decide) :
    Pins (GS rs V) [.r10, .r11, .r29, .r31] := by
  rintro a s₁ s₂ ⟨s0, sM, k, h, -, kk, -⟩ ⟨s0', sM', k', h', -, kk', -⟩ r hr'
  have ea := env_agree k k' (h.env.keep kk hr) (h'.env.keep kk' hr)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl <;> exact ea _ (by simp)

/-- `e`. -/
abbrev eV (s0 : State) : Nat := Spec.Rsa.os2ip (eB s0)

theorem eV_lt {s0 : State} (hp : CIn s0) : eV s0 < 2 ^ 64 := by
  have := os2ip_bytes_lt s0.mem (s0.gpr .r6) (s0.gpr .r7).toNat
  have : 256 ^ (s0.gpr .r7).toNat ≤ 256 ^ 8 := Nat.pow_le_pow_right (by decide) hp.el2
  have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
  show Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r6) (s0.gpr .r7).toNat) < 2 ^ 64
  omega_arith

/-- `gcdCheck`'s start. -/
def G0 (a : CD) (s : State) : Prop :=
  ∃ s0, KRel a s0 ∧ M3 s0 s ∧
    Spec.RsaKeyGen.tooClose (64 * cw s0) (Spec.RsaKeyGen.otherPrime (pB s0)) (candOf s0) = false

theorem pins_G0 : Pins G0 [.r21, .r30] := by
  rintro a s₁ s₂ ⟨s0, k, h, -⟩ ⟨s0', k', h', -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h.r21, h'.r21]; exact k.reg k' (by decide)
  · rw [h.r30, h'.r30]; exact k.reg k' (by decide)

abbrev g1Regs : List Reg := [.r0, .r3, .r14, .r17, .r21]
abbrev g2Regs : List Reg := g1Regs ++ [.r0, .r5]
abbrev g3Regs : List Reg := g2Regs ++ [.r5]

theorem gcd_ct : RelCT isa (Two G0) gcdCheck fun _ _ => True := by
  unfold gcdCheck
  refine RelCT.seq (two_post (Ψ := GS g1Regs fun s0 t => t.gpr .r21 = BitVec.ofNat 64 (eV s0))
    (two_taint _ pins_G0 (by taint_decide)) fun a s ⟨s0, k, h, hn⟩ => ?_)
    (RelCT.seq (two_post (Ψ := GS g2Regs fun s0 t => t.gpr .r21 = BitVec.ofNat 64 (eV s0) ∧
      t.gpr .r5 = BitVec.ofNat 64 (eV s0 % 2)) (two_taint [] (fun _ _ _ _ _ _ hr => by simp at hr) (by taint_decide))
      fun a s ⟨s0, sM, k, h, hn, kk, h21⟩ => ?_)
    (two_ite ?_ (two_taint [] (fun _ _ _ _ _ _ hr => by simp at hr) (by taint_decide))
      (RelCT.seq (two_post (Ψ := GS g3Regs fun s0 t => t.gpr .r5 = BitVec.ofNat 64 (eV s0 - 1))
        (two_taint [] (fun _ _ _ _ _ _ hr => by simp at hr) (by taint_decide))
        fun a s ⟨⟨s0, sM, k, h, hn, kk, h21, h5⟩, ev⟩ => ?_)
        (two_ite ?_ (two_taint [] (fun _ _ _ _ _ _ hr => by simp at hr) (by taint_decide))
          (two_taint _ (pins_and pins_GS) (by taint_decide))))))
  · have hp := k.1
    have hfe := hp.fe
    have bE : Spec.Rsa.bytesAt s.mem (s0.gpr .r6) (s0.gpr .r7).toNat = eB s0 :=
      in_bytes h.ctx.bx (ρ := cE s0) (hE_dj hp) (Nat.le_refl _) (by omega_using [])
    refine WP.mono (loadE_ok (h.r21.trans (BitVec.add_zero _).symm) (h.r30.trans (ofNat_toNat64 _).symm)
      hp.el1 hp.el2 (rd_bytes (n := (s0.gpr .r7).toNat) (by rw [h.ctx.bx.rd]; exact hp.rE) hfe (by omega_using [])))
      fun t ⟨⟨a21, _⟩, kt⟩ => ⟨s0, s, k, h, hn, kt, by show t.gpr .r21 = _; rw [a21, bE]⟩
  · have hEl := eV_lt k.1
    refine WP.mono (WP.keep [.r0, .r5] (Q := fun t => t.gpr .r5 = BitVec.ofNat 64 (eV s0 % 2) ∧
        t.gpr .r21 = s.gpr .r21) (by
      prun [h21, VG.Proof.RsaKeyGen.PPC64LE.Cand.and1_val]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hEl]
      split <;> (congr 1; omega_arith)) (by decide))
      fun t ⟨⟨a5, a21⟩, kt⟩ => ⟨s0, sM, k, h, hn, kk.trans kt, a21.trans h21, a5⟩
  · rintro a s₁ s₂ ⟨s0, sM, k, -, -, -, -, h5⟩ ⟨s0', sM', k', -, -, -, -, h5'⟩
    rw [eval_zero_ofNat _ _ (by have := Nat.mod_lt (eV s0) (show 0 < 2 by decide); omega_using []) h5,
      eval_zero_ofNat _ _ (by have := Nat.mod_lt (eV s0') (show 0 < 2 by decide); omega_using []) h5']
    simp only [eV, k.e k']
  · have hEl := eV_lt k.1
    have he1 : eV s0 % 2 = 1 := by
      rw [eval_zero_ofNat _ _ (by have := Nat.mod_lt (eV s0) (show 0 < 2 by decide); omega_using []) h5] at ev
      simp at ev; omega_using [ev]
    refine WP.mono (WP.keep [.r5] (Q := fun t => t.gpr .r5 = BitVec.ofNat 64 (eV s0 - 1)) (by
      prun [h21]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega_using [he1]) (by decide))
      fun t ⟨a5, kt⟩ => ⟨s0, sM, k, h, hn, kk.trans kt, a5⟩
  · rintro a s₁ s₂ ⟨s0, sM, k, -, -, -, h5⟩ ⟨s0', sM', k', -, -, -, h5'⟩
    have := eV_lt k.1
    have := eV_lt k'.1
    rw [eval_zero_ofNat _ _ (by omega_arith) h5, eval_zero_ofNat _ _ (by omega_using [this]) h5']
    simp only [eV, k.e k']

theorem gcd_eval : ∀ (a : CD) (s₁ s₂ : State), SG M4 a s₁ → SG M4 a s₂ →
    isa.eval (.nonzero .d .r22) s₁ = isa.eval (.nonzero .d .r22) s₂ := by
  rintro a s₁ s₂ ⟨s0, k, h⟩ ⟨s0', k', h'⟩
  rw [VG.PPC64LE.eval_nonzero, VG.PPC64LE.eval_nonzero]
  have hav := h.hav
  have hav' := h'.hav
  obtain ⟨hw, -, -⟩ := cw_facts k.1
  obtain ⟨hw', -, -⟩ := cw_facts k'.1
  have e := gcd_agree k k' hav (by rw [candS_eq k.1 hav, show 8 * oL s0 = 64 * cw s0 by omega_using [hw]]; exact h.ncl)
  rw [candS_eq k.1 hav, candS_eq k'.1 hav'] at e
  have i : s₁.gpr .r22 = 0 ↔ s₂.gpr .r22 = 0 := h.g.trans (e.trans h'.g.symm)
  congr 1
  by_cases z : s₁.gpr .r22 = 0
  · rw [z, i.mp z]
  · have z' : ¬ s₂.gpr .r22 = 0 := fun e' => z (i.mpr e')
    rw [bne_iff_ne.mpr z, bne_iff_ne.mpr z']

theorem main_ct {trial : Prog isa} (D : DivOk trial) (R : RoundImpl) :
    RelCT isa (Two (SG MIn)) (main trial R.name R.code) fun _ _ => True := by
  unfold main
  simp only [VG.Impl.RsaKeyGen.PPC64LE.Candidate.seqs]
  refine RelCT.seq (two_post (Ψ := SG M1) (two_taint _ pins_MIn (by taint_decide))
    fun a s ⟨s0, k, h⟩ => WP.mono (setupS h) fun t ht => ⟨s0, k, ht⟩)
    (RelCT.seq (two_post (Ψ := SG M2) (two_taint _ pins_M1 (by taint_decide))
      fun a s ⟨s0, k, h⟩ => WP.mono (loadCS h) fun t ht => ⟨s0, k, ht⟩)
    (RelCT.seq (two_post (Ψ := SG M3) (two_taint _ pins_M2 (by taint_decide))
      fun a s ⟨s0, k, h⟩ => WP.mono (closeS h) fun t ht => ⟨s0, k, ht⟩)
    (two_ite close_eval (two_taint _ (pins_and pins_M3) (by taint_decide))
      (RelCT.seq (two_post (Ψ := SG M4) (two_mono (Ψ := G0) (fun a s ⟨⟨s0, k, h⟩, ev⟩ => ⟨s0, k, h, ?_⟩) gcd_ct)
        fun a s ⟨⟨s0, k, h⟩, ev⟩ => WP.mono (gcdS h ?_) fun t ht => ⟨s0, k, ht⟩)
        (two_ite gcd_eval (two_taint _ (pins_and pins_M4) (by taint_decide))
          (two_mono (Ψ := TI) (fun a s ⟨⟨s0, k, h⟩, ev⟩ => ⟨s0, ⟨k, h.ncl, ?_⟩, toTIn h ?_⟩) (test_ct D R)))))))
  · rw [eval_nonzero_ofNat' _ _ (by split <;> decide) h.f] at ev
    revert ev; cases Spec.RsaKeyGen.tooClose _ _ (candOf s0) <;> decide
  · rw [eval_nonzero_ofNat' _ _ (by split <;> decide) h.f] at ev
    revert ev; cases Spec.RsaKeyGen.tooClose _ _ (candOf s0) <;> decide
  · rw [VG.PPC64LE.eval_nonzero] at ev
    exact h.g.mp (by simpa using ev)
  · rw [VG.PPC64LE.eval_nonzero] at ev
    exact h.g.mp (by simpa using ev)

end VG.Proof.RsaKeyGen.PPC64LE.Cand

end

end

/-!
# A candidate on PPC64LE: the whole function in constant time

`code_ct`: two runs from calls with the same public data (`KRel`) leak the
same trace. The frames leak the stack pointer; the entry, `out`'s zeroing
and the test of `rand`'s length are checked by the taint analysis from the
arguments, whose test is then the same in both runs; then `main_ct`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Candidate (code body entry zeroOut finNone main restore frameBytes)
open VG.Impl.MillerRabin.PPC64LE.Search (geFlag)
open VG.Proof.MillerRabin.PPC64LE (RoundImpl)

/-- The body's start. -/
def PS (a : CD) (u : State) : Prop := ∃ s0, KRel a s0 ∧ u = started s0

/-- After the entry. -/
def PE (a : CD) (t : State) : Prop := ∃ s0, KRel a s0 ∧ Bx s0 t ∧ Regs s0 t ∧ t.syms = s0.syms

/-- After `out`'s zeroing. -/
def PB (a : CD) (t : State) : Prop := ∃ s0, KRel a s0 ∧ BR s0 t

/-- After the test of `rand`'s length. -/
def PF (a : CD) (t : State) : Prop := ∃ s0, KRel a s0 ∧ BF s0 t

/-- Before the restore. -/
def PX (a : CD) (t : State) : Prop := ∃ s0, KRel a s0 ∧ Bx s0 t

theorem pins_PS : Pins PS [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10] := by
  rintro a s₁ s₂ ⟨s0, k, rfl⟩ ⟨s0', k', rfl⟩ r hr
  rw [(started_ok k.1).gpr r (by revert hr; revert r; decide),
    (started_ok k'.1).gpr r (by revert hr; revert r; decide)]
  exact k.reg k' (by simp only [argRegs]; exact hr)

theorem pins_PE : Pins PE [.r23, .r24] := by
  rintro a s₁ s₂ ⟨s0, k, -, hr, -⟩ ⟨s0', k', -, hr', -⟩ r h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · rw [hr.r23, hr'.r23]; exact k.reg k' (by decide)
  · rw [hr.r24, hr'.r24]; exact k.reg k' (by decide)

theorem pins_PB : Pins PB [.r27, .r24] := by
  rintro a s₁ s₂ ⟨s0, k, h⟩ ⟨s0', k', h'⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h.regs.r27, h'.regs.r27]; exact k.arg k' (by decide)
  · rw [h.regs.r24, h'.regs.r24]; exact k.reg k' (by decide)

theorem pins_PF : Pins PF [.r25] := by
  rintro a s₁ s₂ ⟨s0, k, h⟩ ⟨s0', k', h'⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [h.1.regs.r25, h'.1.regs.r25]; exact k.reg k' (by decide)

theorem len_eval : ∀ (a : CD) (s₁ s₂ : State), PF a s₁ → PF a s₂ →
    isa.eval (.zero .d .r5) s₁ = isa.eval (.zero .d .r5) s₂ := by
  rintro a s₁ s₂ ⟨s0, k, -, h5⟩ ⟨s0', k', -, h5'⟩
  rw [eval_zero_ofNat _ _ (by split <;> decide) h5, eval_zero_ofNat _ _ (by split <;> decide) h5',
    k.oL_eq k', k.rL_eq k']

theorem body_ct {trial : Prog isa} (D : DivOk trial) (R : RoundImpl) :
    RelCT isa (Two PS) (body trial R.name R.code) fun _ _ => True := by
  unfold body
  simp only [VG.Impl.RsaKeyGen.PPC64LE.Candidate.seqs]
  refine RelCT.seq (two_post (Ψ := PE) (two_taint _ pins_PS (by taint_decide)) fun a s ⟨s0, k, hs⟩ => ?_)
    (RelCT.seq (two_post (Ψ := PB) (two_taint _ pins_PE (by taint_decide))
      fun a s ⟨s0, k, hb, hr, sy⟩ => WP.mono (zeroS hb hr sy) fun t ht => ⟨s0, k, ht⟩)
    (RelCT.seq (two_post (Ψ := PF) (two_taint _ pins_PB (by taint_decide))
      fun a s ⟨s0, k, h⟩ => WP.mono (flagS h) fun t ht => ⟨s0, k, ht⟩)
    (RelCT.seq (two_post (Ψ := PX) (two_ite len_eval (two_taint _ (pins_and pins_PF) (by taint_decide))
      (two_mono (Ψ := SG MIn) (fun a s ⟨⟨s0, k, ⟨c, hr, sy⟩, h5⟩, ev⟩ => ⟨s0, k, ?_⟩) (main_ct D R)))
      fun a s ⟨s0, k, h⟩ => WP.mono (iteS D R k.2.1 h) fun t ht => ⟨s0, k, ht.1⟩)
      (two_taint [] (fun _ _ _ _ _ _ hr => by simp at hr) (by taint_decide)))))
  · subst hs
    exact WP.mono_syms (entry_ok (started_ok k.1)) fun t ⟨hb, hr⟩ sy => ⟨s0, k, hb, hr, sy⟩
  · have hav : oL s0 ≤ rL s0 := by
      rw [eval_zero_ofNat _ _ (by split <;> decide) h5] at ev
      by_contra hc; simp only [hc, ↓reduceIte] at ev; exact absurd ev (by decide)
    exact ⟨c, hr.r21, hr.r30, hr.r18, hr.r19, hr.r26, hr.r27, hr.r31, hr.r11, hav, sy, k.2.1⟩

/-- After `mflr`. -/
def P1 (a : CD) (s : State) : Prop := ∃ s0, KRel a s0 ∧ s = s0.write .r0 s0.lr

theorem code_ct {trial : Prog isa} (D : DivOk trial) (R : RoundImpl) :
    RelCT isa (Two KRel) (code trial R.name R.code) fun _ _ => True := by
  unfold code
  refine RelCT.seq (two_post (Ψ := P1) (two_taint [] (fun _ _ _ _ _ _ hr => by simp at hr) (by taint_decide))
    fun a s k => WP.of_runBlock ⟨s.write .r0 s.lr,
      (by simp only [runBlock_cons, runStep_some, runBlock_nil, exec_mflr]), ⟨s, k, rfl⟩⟩)
    (RelCT.seq (RelCT.frame (fun _ _ ⟨a, h₁, h₂, hsp⟩ => hsp)
      (RelCT.alloc (fun s t ⟨s₁, s₂, ⟨a, h₁, h₂, hsp⟩, e₁, e₂⟩ => by subst e₁ e₂; simp only [pushed, hsp])
        ((body_ct D R).mono (fun x y ⟨s, t, ⟨s₁, s₂, ⟨a, ⟨s0, k, e₀⟩, ⟨s0', k', e₀'⟩, hsp⟩, e₁, e₂⟩, e₃, e₄⟩ =>
          ⟨a, ⟨s0, k, by rw [e₃, e₁, e₀]; rfl⟩, ⟨s0', k', by rw [e₄, e₂, e₀']; rfl⟩, by
            subst e₃ e₄ e₁ e₂ e₀ e₀'
            simp only [allocated, pushed, State.write] at hsp ⊢
            rw [hsp]⟩) fun _ _ h => h)))
      (RelCT.taint (A := taint) (ofRegs []) (fun _ _ hsp => ⟨hsp, fun r hr => by simp at hr⟩)
        (by taint_decide)))

end VG.Proof.RsaKeyGen.PPC64LE.Cand

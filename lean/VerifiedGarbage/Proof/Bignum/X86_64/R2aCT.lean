module

public import VerifiedGarbage.Proof.Bignum.X86_64.R2aFast
public import VerifiedGarbage.Proof.Bignum.X86_64.R2wCT
public import VerifiedGarbage.Proof.Bignum.X86_64.R2aD3
import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv
import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aFast
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aD3
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wDiv
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Bignum.WordStep
meta import VerifiedGarbage.Proof.Bignum.WordStep
public import VerifiedGarbage.Proof.Bignum.X86_64.R2aRecip
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2aRecip
public import VerifiedGarbage.Proof.Bignum.Recip
meta import VerifiedGarbage.Proof.Bignum.Recip

/-!
# `R² mod m` by word steps with ADX: constant time but for `m`

A step's addresses depend only on the working space and `w`, and its
branches, `fix`'s, on the sign of `t`, a function of `x` and `m` (as `q̂`
is, refined by `refine`'s masks: `SPub.qr`): in the
steps, `x` is `(R - m) 2^(64 j) mod m` after `j` of them, a function of `m`,
which is public (`SPub`, `step_ct`). The steps' count is `w` (`steps_ct`),
and `choice` branches on the top bit of `m` and on `w` (`choice_ct`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.R2ax

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.R2Adx
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.WordStep VG.Proof.Bignum.Recip

/-! ## A step -/

/-- The public data of a step: the working space, `x` and `m`. -/
structure SPub where
  L : Lay
  X : Nat
  M : Nat

/-- `R` and `2^64 R`. -/
abbrev SPub.R (p : SPub) : Nat := 2 ^ (64 * p.L.w)
abbrev SPub.W (p : SPub) : Nat := 2 ^ (64 * (p.L.w + 1))

/-- `q̂`, from the top words of `x` and `m`. -/
def SPub.q (p : SPub) : Nat :=
  min ((p.X / 2 ^ (64 * (p.L.w - 1)) % 2 ^ 64 * 2 ^ 64 + p.X / 2 ^ (64 * (p.L.w - 2)) % 2 ^ 64) /
    (p.M / 2 ^ (64 * (p.L.w - 1)) % 2 ^ 64)) (2 ^ 64 - 1)

/-- The word `w - i` of `x`, and of `m`. -/
def SPub.u (p : SPub) (i : Nat) : Nat := p.X / 2 ^ (64 * (p.L.w - i)) % 2 ^ 64
def SPub.d (p : SPub) (i : Nat) : Nat := p.M / 2 ^ (64 * (p.L.w - i)) % 2 ^ 64

/-- `q̂` refined once, and twice (`refine`). -/
def SPub.q1 (p : SPub) : Nat := d3 p.q (p.u 1) (p.u 2) (p.u 3) (p.d 1) (p.d 2)
def SPub.qr (p : SPub) : Nat := d3 p.q1 (p.u 1) (p.u 2) (p.u 3) (p.d 1) (p.d 2)

theorem SPub.q_lt (p : SPub) : p.q < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide)
theorem SPub.q1_lt (p : SPub) : p.q1 < 2 ^ 64 := Nat.lt_of_le_of_lt (d3_le _ _ _ _ _ _) p.q_lt
theorem SPub.qr_lt (p : SPub) : p.qr < 2 ^ 64 := Nat.lt_of_le_of_lt (d3_le _ _ _ _ _ _) p.q1_lt

theorem SPub.q_mul_le (p : SPub) : p.q * p.d 1 ≤ p.u 1 * 2 ^ 64 + p.u 2 :=
  Nat.le_trans (Nat.mul_le_mul_right _ (Nat.min_le_left _ _)) (Nat.div_mul_le_self _ _)

/-- `t = x 2^64 - q̂ m` modulo `2^64 R`. -/
def SPub.t1 (p : SPub) : Nat := (p.X * 2 ^ 64 + p.qr * (p.R - p.M) + p.qr * (p.W - p.R)) % p.W

/-- `t + m` if `t` is negative. -/
def fixV (W M T : Nat) : Nat := if W / 2 ≤ T then (T + M) % W else T

/-- `step_ok`'s hypotheses, with the values public. -/
def SPre (p : SPub) (s : State) : Prop :=
  GoodL p.L s ∧ 4 ≤ p.L.w ∧ p.L.w % 4 = 0 ∧ p.L.w < 2 ^ 30 ∧
    2 ^ 63 ≤ (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat ∧
    (word s.mem p.L.B (slot p.L.w aTmp)).toNat =
      (2 ^ 128 - 1) / (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat - 2 ^ 64 ∧
    wv s.mem p.L.B (slot p.L.w aR2) p.L.w = p.X ∧ wv s.mem p.L.B (slot p.L.w aN) p.L.w = p.M ∧ p.X < p.M ∧
    wv s.mem p.L.B (slot p.L.w aAcc) p.L.w + p.M = p.R

theorem GoodL.congr {L : Lay} {s t : State} (h : GoodL L s) (hm : t.mem = s.mem) (hw : t.wr = s.wr)
    (hdi : t.gpr .rdi = s.gpr .rdi) : GoodL L t :=
  ⟨⟨h.1.scr.congr hw, hdi.trans h.1.rdi, hm ▸ h.1.hdr⟩, h.2⟩

theorem SPre.congr {p : SPub} {s t : State} (h : SPre p s) (hm : t.mem = s.mem) (hw : t.wr = s.wr)
    (hdi : t.gpr .rdi = s.gpr .rdi) : SPre p t := by
  obtain ⟨hg, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨GoodL.congr hg hm hw hdi, h1, h2, h3, hm ▸ h4, hm ▸ h5, hm ▸ h6, hm ▸ h7, h8, hm ▸ h9⟩

/-- After a step's loads. -/
def SB (p : SPub) (t : State) : Prop :=
  SPre p t ∧ t.gpr .rbx = off p.L.B (slot p.L.w aR2) ∧ t.gpr .r10 = off p.L.B (slot p.L.w aN) ∧
    t.gpr .r8 = off p.L.B (slot p.L.w aAcc) ∧ t.gpr .r12 = BitVec.ofNat 64 p.L.w ∧
    t.gpr .rbp = off p.L.B (slot p.L.w aTmp)

theorem pins_SB : Pins SB [.rbx, .r10, .r8, .r12, .rbp, .rdi] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.2.2.1, h₂.2.2.2.1]
  · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]
  · rw [h₁.2.2.2.2.2, h₂.2.2.2.2.2]
  · rw [h₁.1.1.1.rdi, h₂.1.1.1.rdi]

theorem sb_ok {p : SPub} {s : State} (h : SPre p s) : WP isa (.block R2Words.bases) s (SB p) :=
  WP.mono (R2w.stepBases_ok h.1) fun t ⟨h1, h2, h3, h4, h5, hm, k⟩ =>
    ⟨SPre.congr h hm k.2.2 (k.gpr (by decide)), h1, h2, h3, h4, h5⟩

/-- With the estimate `V` in `rcx`. -/
def SQ (V : Nat) (p : SPub) (t : State) : Prop :=
  SPre p t ∧ t.gpr .rbx = off p.L.B (slot p.L.w aR2) ∧ t.gpr .r10 = off p.L.B (slot p.L.w aN) ∧
    t.gpr .r12 = BitVec.ofNat 64 p.L.w ∧ t.gpr .rcx = BitVec.ofNat 64 V

theorem pins_SQ (V : SPub → Nat) : Pins (fun p => SQ (V p) p) [.rbx, .r10, .r12] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.2.2.1, h₂.2.2.2.1]

theorem sq_ok {p : SPub} {s : State} (h : SB p s) : WP isa (.block R2Words.quot) s (SQ p.q p) := by
  obtain ⟨hp, hbx, h10, _, h12, hbp⟩ := h
  have hp' := hp
  obtain ⟨hg, hw, _, hw', hd, hv, hX, hM, hXM, _⟩ := hp'
  have hs := hg.1.scr
  have hZ := hg.2
  have hn := hs.nowrap
  have hsx := slot_le (w := p.L.w) (show aR2 < 8 by decide)
  have hsm := slot_le (w := p.L.w) (show aN < 8 by decide)
  have hsv := slot_le (w := p.L.w) (show aTmp < 8 by decide)
  have hu := R2w.top_le (by omega_using [hw]) (hX ▸ hM ▸ hXM)
  refine WP.mono (R2w.quot_ok hs hbx h10 h12 hbp (by omega_using [hw]) (by omega_using [hZ, hsx]) (by omega_using [hZ, hsm]) (by omega_using [hZ, hsv]) hu hd hv)
    fun t ⟨hcx, hm, k⟩ => ⟨SPre.congr hp hm k.2.2 (k.gpr (by decide)), (k.gpr (by decide)).trans hbx,
      (k.gpr (by decide)).trans h10, (k.gpr (by decide)).trans h12, ?_⟩
  rw [hcx, word_of_wv s.mem p.L.B _ p.L.w (show p.L.w - 1 < p.L.w by omega_using [hw]),
    word_of_wv s.mem p.L.B _ p.L.w (show p.L.w - 2 < p.L.w by omega_using [hw]),
    word_of_wv s.mem p.L.B (slot p.L.w aN) p.L.w (show p.L.w - 1 < p.L.w by omega_using [hw]), hX, hM]
  rfl

/-- At the start of the pass. -/
def SH (p : SPub) (t : State) : Prop :=
  SPre p t ∧ t.gpr .rbx = off p.L.B (slot p.L.w aR2) ∧ t.gpr .r10 = off p.L.B (slot p.L.w aN) ∧
    t.gpr .r12 = BitVec.ofNat 64 p.L.w ∧ t.gpr .rsi = off p.L.B (slot p.L.w aAcc) ∧
    t.gpr .rdx = BitVec.ofNat 64 p.qr ∧ t.gpr .r8 = 0 ∧ t.gpr .r9 = 0 ∧ t.gpr .r14 = 0 ∧ t.gpr .r15 = 0

/-- Knuth's test on the estimate `V`, with the words of `x` and `m`. -/
theorem sr_ok {p : SPub} {V : Nat} {s : State} (h : SQ V p s) (hV : V < 2 ^ 64)
    (hle : V * p.d 1 ≤ p.u 1 * 2 ^ 64 + p.u 2) :
    WP isa (.block refine) s (SQ (d3 V (p.u 1) (p.u 2) (p.u 3) (p.d 1) (p.d 2)) p) := by
  obtain ⟨hp, hbx, h10, h12, hcx⟩ := h
  have hp' := hp
  obtain ⟨hg, hw, _, _, _, _, hX, hM, _, _⟩ := hp'
  have hs := hg.1.scr
  have hZ := hg.2
  have hsx := slot_le (w := p.L.w) (show aR2 < 8 by decide)
  have hsm := slot_le (w := p.L.w) (show aN < 8 by decide)
  have hu : ∀ i, 1 ≤ i → i ≤ 3 → (word s.mem p.L.B (slot p.L.w aR2 + 8 * (p.L.w - i))).toNat = p.u i :=
    fun i h1 h3 => by rw [word_of_wv s.mem p.L.B _ p.L.w (show p.L.w - i < p.L.w by omega_using [hw, h1]), hX]; rfl
  have hd : ∀ i, 1 ≤ i → i ≤ 2 → (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - i))).toNat = p.d i :=
    fun i h1 h3 => by rw [word_of_wv s.mem p.L.B _ p.L.w (show p.L.w - i < p.L.w by omega_using [hw, h1]), hM]; rfl
  refine WP.mono (refine_ok hs hbx h10 h12 hcx (by omega_using [hw]) (by omega_using [hZ, hsx]) (by omega_using [hZ, hsm]) hV (by
    rw [hu 1 (by omega_using []) (by omega_using []), hu 2 (by omega_using []) (by omega_using []), hd 1 (by omega_using []) (by omega_using [])]; exact hle))
    fun t ⟨hcx', hm, k⟩ => ⟨SPre.congr hp hm k.2.2 (k.gpr (by decide)), (k.gpr (by decide)).trans hbx,
      (k.gpr (by decide)).trans h10, (k.gpr (by decide)).trans h12, ?_⟩
  rw [hcx', hu 1 (by omega_using []) (by omega_using []), hu 2 (by omega_using []) (by omega_using []), hu 3 (by omega_using []) (by omega_using []),
    hd 1 (by omega_using []) (by omega_using []), hd 2 (by omega_using []) (by omega_using [])]

theorem sh_ok {p : SPub} {s : State} (h : SQ p.qr p s) : WP isa (.block mulHead) s (SH p) := by
  obtain ⟨hp, hbx, h10, h12, hcx⟩ := h
  have hg := hp.1
  have hhd := hdr_lt_slot p.L.w 0 (show sArr aAcc < 32 by decide)
  have hs0 := slot_le (w := p.L.w) (show 0 < 8 by decide)
  have hZ := hg.2
  refine WP.mono (mulHead_ok hg.1.scr hg.1.rdi (hg.1.hdr.harr aAcc (by decide)) (by omega_using [hhd, hs0, hZ]))
    fun t ⟨hdx, hsi, h8, h9, h14, h15, hm, k⟩ => ⟨SPre.congr hp hm k.2.2 (k.gpr (by decide)),
      (k.gpr (by decide)).trans hbx, (k.gpr (by decide)).trans h10, (k.gpr (by decide)).trans h12, hsi,
      hdx.trans hcx, h8, h9, h14, h15⟩

theorem pins_SH : Pins SH [.rbx, .rsi, .r12, .r15, .rdi] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]
  · rw [h₁.2.2.2.1, h₂.2.2.2.1]
  · rw [h₁.2.2.2.2.2.2.2.2.2, h₂.2.2.2.2.2.2.2.2.2]
  · rw [h₁.1.1.1.rdi, h₂.1.1.1.rdi]

/-- Before a `fix`, with `t = V`. -/
def SF (V : Nat) (p : SPub) (t : State) : Prop :=
  GoodL p.L t ∧ t.gpr .rbx = off p.L.B (slot p.L.w aR2) ∧ t.gpr .r10 = off p.L.B (slot p.L.w aN) ∧
    t.gpr .r12 = BitVec.ofNat 64 p.L.w ∧ 4 ≤ p.L.w ∧ p.L.w < 2 ^ 30 ∧
    wv t.mem p.L.B (slot p.L.w aR2) (p.L.w + 1) = V ∧ wv t.mem p.L.B (slot p.L.w aN) p.L.w = p.M

/-- `T` from `T + q R ≡ V`. -/
theorem t_eq {T q R W V : Nat} (hT : T < W) (hR : R ≤ W) (h : (T + q * R) % W = V % W) :
    T = (V + q * (W - R)) % W := by
  have e : (T + q * R + q * (W - R)) % W = (V + q * (W - R)) % W := by
    rw [Nat.add_mod (T + q * R), h, ← Nat.add_mod]
  rw [Nat.add_assoc, ← Nat.mul_add, show R + (W - R) = W by omega_using [hR], Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt hT] at e
  exact e

theorem sf_ok {p : SPub} {s : State} (h : SH p s) :
    WP isa (.seq tiles (.block mulTop)) s (SF p.t1 p) := by
  obtain ⟨hp, hbx, h10, h12, hsi, hdx, h8, h9, h14, h15⟩ := h
  have hp' := hp
  obtain ⟨hg, hw, hw4, hw', _, _, hX, hM, hXM, hC⟩ := hp'
  have hs := hg.1.scr
  have hZ := hg.2
  have hn := hs.nowrap
  have hsx := slot_le (w := p.L.w) (show aR2 < 8 by decide)
  have hsm := slot_le (w := p.L.w) (show aN < 8 by decide)
  have hsa := slot_le (w := p.L.w) (show aAcc < 8 by decide)
  have sXA := slot_sep (w := p.L.w) (show aR2 ≠ aAcc by decide)
  have sXM := slot_sep (w := p.L.w) (show aR2 ≠ aN by decide)
  have hq := p.qr_lt
  refine WP.mono (mulBody_ok (N := p.L.w / 4) hs hbx hsi h12 h8 h9 h14 h15 (by omega_using [hw4]) (by omega_using [hw]) (by omega_using [hZ, hn, hsa])
    (by omega_using [hZ, hsx]) (by omega_using [hZ, hsa]) (by omega_using [sXA])) fun t ⟨hv, ho, k⟩ => ?_
  have hM' : wv t.mem p.L.B (slot p.L.w aN) p.L.w = p.M := by rw [ho.wv (by omega_using [sXM]) (by omega_using [hZ, hn, hsm]), hM]
  have ha : Arrays p.L.B p.L.w [aR2] s.mem t.mem :=
    Arrays.of_outside (List.mem_singleton_self _) ho (Nat.le_refl _) (by omega_using [])
  refine ⟨⟨⟨hs.congr k.2.2, (k.gpr (by decide)).trans hg.1.rdi, ha.hdr hg.1.hdr⟩, hZ⟩,
    (k.gpr (by decide)).trans hbx, (k.gpr (by decide)).trans h10, (k.gpr (by decide)).trans h12, hw, hw', ?_, hM'⟩
  rw [hdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq, hX, show wv s.mem p.L.B (slot p.L.w aAcc) p.L.w = p.R - p.M by
    omega_using [hC]] at hv
  unfold SPub.t1
  exact t_eq (wv_lt _ _ _ _) (Nat.pow_le_pow_right (by decide) (by omega_using [])) hv

theorem pins_SF (V : SPub → Nat) : Pins (fun p => SF (V p) p) [.rbx, .r10, .r12, .rdi] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.2.2.1, h₂.2.2.2.1]
  · rw [h₁.1.1.rdi, h₂.1.1.rdi]

/-- With the sign of `t` in `CF`. -/
def SFc (V : SPub → Nat) (p : SPub) (t : State) : Prop :=
  SF (V p) p t ∧ t.cf = some (decide (p.W / 2 ≤ V p))

theorem fixV_lt {W M T : Nat} (hW : 0 < W) (hT : T < W) : fixV W M T < W := by
  unfold fixV; split
  · exact Nat.mod_lt _ hW
  · exact hT

/-- `fix` leaks the same in runs with the same `t`, which it makes `fixV`. -/
theorem fix_ct (V : SPub → Nat) :
    RelCT isa (Two fun p => SF (V p) p) fix (Two fun p => SF (fixV p.W p.M (V p)) p) := by
  unfold fix
  refine RelCT.seq (two_piece (Ψ := SFc V) _ (pins_SF V) (by taint_decide) fun p s h => ?_) ?_
  · obtain ⟨hg, hbx, h10, h12, hw, hw', hT, hM⟩ := h
    have hs := hg.1.scr
    have hn := hs.nowrap
    have hZ := hg.2
    have hsx := slot_le (w := p.L.w) (show aR2 < 8 by decide)
    have hea : s.ea (ix .rbx .r12) = off p.L.B (slot p.L.w aR2 + 8 * p.L.w) := ea_ix0 s hbx h12
    refine WP.mono (WP.keep [.rax] (Q := fun t => t.cf = some (decide (2 ^ 63 ≤
        (word s.mem p.L.B (slot p.L.w aR2 + 8 * p.L.w)).toNat)) ∧ t.mem = s.mem) (by
      xrun [hea, hs.ld (show slot p.L.w aR2 + 8 * p.L.w + 8 ≤ p.L.Z by omega_using [hZ, hsx]), top_cf]) rfl)
      fun t ⟨⟨hc, hm⟩, k⟩ => ⟨⟨GoodL.congr hg hm k.2.2 (k.gpr (by decide)), (k.gpr (by decide)).trans hbx,
        (k.gpr (by decide)).trans h10, (k.gpr (by decide)).trans h12, hw, hw', hm ▸ hT, hm ▸ hM⟩, ?_⟩
    rw [hc, ← hT]
    congr 1
    exact decide_eq_decide.mpr (R2w.top_half _ _ _ _).symm
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) ?_ ?_
  · refine (two_piece (Ψ := fun p => SF (fixV p.W p.M (V p)) p) _ (fun p s₁ s₂ h₁ h₂ => pins_SF V p s₁ s₂ h₁.1.1 h₂.1.1)
      (by taint_decide) fun p s ⟨⟨h, hc⟩, hb⟩ => ?_).mono (fun _ _ h => h) fun _ _ h => h
    obtain ⟨hg, hbx, h10, h12, hw, hw', hT, hM⟩ := h
    simp only [eval, hc, Option.some.injEq, decide_eq_true_eq] at hb
    have hs := hg.1.scr
    have hn := hs.nowrap
    have hZ := hg.2
    have hsx := slot_le (w := p.L.w) (show aR2 < 8 by decide)
    have hsm := slot_le (w := p.L.w) (show aN < 8 by decide)
    have sXM := slot_sep (w := p.L.w) (show aR2 ≠ aN by decide)
    refine WP.seq (WP.mono (WP.keep [.r8] (Q := fun t => t.gpr .r8 = off p.L.B (slot p.L.w aR2) ∧ t.mem = s.mem)
      (by xrun [hbx]) rfl) fun t₁ ⟨⟨h8, hm₁⟩, k₁⟩ => ?_)
    refine WP.mono (R2w.addBack_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans h10) h8
      ((k₁.gpr (by decide)).trans h12) (by omega_using [hw]) (by omega_using [hw']) (by omega_using [hZ, hsm]) (by omega_using [hZ, hsx]) (by omega_using [sXM]))
      fun t ⟨c, hv, ho, k⟩ => ?_
    simp only [hm₁, ← R2w.top_half, hT, hM] at hv
    simp only [hb, ↓reduceIte] at hv
    have ha : Arrays p.L.B p.L.w [aR2] s.mem t.mem := by
      rw [← hm₁]; exact Arrays.of_outside (List.mem_singleton_self _) ho (Nat.le_refl _) (by omega_using [])
    have kk := k₁.trans k
    refine ⟨⟨⟨hs.congr (k.2.2.trans k₁.2.2), (kk.gpr (by decide)).trans hg.1.rdi, ha.hdr hg.1.hdr⟩, hZ⟩,
      (kk.gpr (by decide)).trans hbx, (kk.gpr (by decide)).trans h10, (kk.gpr (by decide)).trans h12, hw, hw', ?_,
      by rw [ha.wv_of_not_mem (by decide) (by decide) (by omega_using [hn, hZ])]; exact hM⟩
    have hlt := wv_lt t.mem p.L.B (slot p.L.w aR2) (p.L.w + 1)
    unfold fixV
    simp only [hb, ↓reduceIte]
    cases c
    · simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at hv
      rw [← hv, Nat.mod_eq_of_lt hlt]
    · simp only [Bool.toNat_true, Nat.mul_one] at hv
      rw [← hv, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
  · refine (two_piece (Ψ := fun p => SF (fixV p.W p.M (V p)) p) [] (fun _ _ _ _ _ _ h => nomatch h)
      (by taint_decide) fun p s ⟨⟨h, hc⟩, hb⟩ => WP.block_nil ?_).mono (fun _ _ h => h) fun _ _ h => h
    simp only [eval, hc, Option.some.injEq, decide_eq_false_iff_not] at hb
    obtain ⟨hg, hbx, h10, h12, hw, hw', hT, hM⟩ := h
    exact ⟨hg, hbx, h10, h12, hw, hw', by unfold fixV; simp only [hb, ↓reduceIte]; exact hT, hM⟩

/-- The pass: `t` leaks nothing but its addresses. -/
theorem mulSub_ct : RelCT isa (Two fun p => SQ p.qr p) mulSub (Two (fun p => SF p.t1 p)) := by
  unfold mulSub
  refine RelCT.seq (two_piece (Ψ := SH) [.rdi] (pins_rdi_of (·.L) fun _ _ h => h.1.1) (by taint_decide)
    fun _ _ h => sh_ok h) ?_
  exact two_post (two_taint _ pins_SH (by taint_decide)) fun _ _ h => sf_ok h

/-- A step leaks the same in runs with the same working space, `x` and `m`. -/
theorem step_ct : RelCT isa (Two SPre) step fun _ _ => True := by
  rw [show step = .seq (.block R2Words.bases) (.seq (.block R2Words.quot) (.seq (.block refine) (.seq (.block refine)
    (.seq mulSub (.seq fix fix))))) from rfl]
  refine RelCT.seq (two_piece (Ψ := SB) [.rdi] (pins_rdi_of (·.L) fun _ _ h => h.1) (by taint_decide)
    fun _ _ h => sb_ok h) ?_
  refine RelCT.seq (two_piece (Ψ := fun p => SQ p.q p) _ pins_SB (by taint_decide) fun _ _ h => sq_ok h) ?_
  refine RelCT.seq (two_piece (Ψ := fun p => SQ p.q1 p) _ (pins_SQ SPub.q) (by taint_decide)
    fun p _ h => sr_ok h p.q_lt p.q_mul_le) ?_
  refine RelCT.seq (two_piece (Ψ := fun p => SQ p.qr p) _ (pins_SQ SPub.q1) (by taint_decide)
    fun p _ h => sr_ok h p.q1_lt (d3_mul_le p.q_mul_le)) ?_
  refine RelCT.seq mulSub_ct (RelCT.seq (fix_ct (fun p => p.t1)) ?_)
  exact (fix_ct (fun p => fixV p.W p.M p.t1)).mono (fun _ _ h => h) fun _ _ _ => trivial

/-! ## The steps -/

/-- The public data of `steps`: the working space, the count and `m`. -/
structure StPub where
  L : Lay
  c : Nat
  M : Nat

/-- `x` after `j` steps from `R - m`. -/
def StPub.X (p : StPub) (j : Nat) : Nat := (2 ^ (64 * p.L.w) - p.M) * 2 ^ (64 * j) % p.M

/-- What `steps` keeps, after `j` steps. -/
def StepsAt (p : StPub) (j : Nat) (t : State) : Prop :=
  ∃ (σ : State) (T : Nat), StepsInv σ p.L.B p.L.Z p.L.w p.L.minv p.c (2 ^ (64 * p.L.w) - p.M) p.M T j t ∧
    slot p.L.w 8 ≤ p.L.Z ∧ 4 ≤ p.L.w ∧ p.L.w % 4 = 0 ∧ p.L.w < 2 ^ 30 ∧ p.c < 2 ^ 31 ∧ 0 < p.M ∧ 2 ^ 63 ≤ T

theorem stepsAt_good {p : StPub} {j : Nat} {t : State} (h : StepsAt p j t) : GoodL p.L t :=
  let ⟨_, _, hI, hZ, _⟩ := h; ⟨⟨hI.scr, hI.rdi, hI.hdr⟩, hZ⟩

theorem stepsAt_pre {p : StPub} {j : Nat} {t : State} (h : StepsAt p j t) :
    SPre ⟨p.L, p.X j, p.M⟩ t := by
  obtain ⟨_, T, hI, hZ, hw, hw4, hw', _, hM, hT⟩ := h
  exact ⟨⟨⟨hI.scr, hI.rdi, hI.hdr⟩, hZ⟩, hw, hw4, hw', by rw [hI.top]; exact hT, by rw [hI.rcp, hI.top], hI.xv,
    hI.nv, Nat.mod_lt _ hM, hI.acc⟩

/-- `steps`' hypotheses. -/
def StepsPre (p : StPub) (s : State) : Prop :=
  GoodL p.L s ∧ 4 ≤ p.L.w ∧ p.L.w % 4 = 0 ∧ p.L.w < 2 ^ 30 ∧ 1 ≤ p.c ∧ p.c < 2 ^ 31 ∧
    s.gpr .rcx = BitVec.ofNat 64 p.c ∧ 2 ^ 63 ≤ (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat ∧
    (word s.mem p.L.B (slot p.L.w aTmp)).toNat =
      (2 ^ 128 - 1) / (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat - 2 ^ 64 ∧
    wv s.mem p.L.B (slot p.L.w aR2) p.L.w = 2 ^ (64 * p.L.w) - p.M ∧ wv s.mem p.L.B (slot p.L.w aN) p.L.w = p.M ∧
    2 ^ (64 * p.L.w) - p.M < p.M ∧ wv s.mem p.L.B (slot p.L.w aAcc) p.L.w + p.M = 2 ^ (64 * p.L.w)

/-- `steps` leaks the same in runs with the same working space, count and `m`. -/
theorem steps_ct : RelCT isa (Two StepsPre) steps (Two fun p s => StepsAt p p.c s) := by
  rw [steps_eq]
  refine RelCT.seq (two_piece (Ψ := fun p s => 0 < p.c ∧ StepsAt p 0 s) _
    (fun p s₁ s₂ h₁ h₂ => pins_good p.L s₁ s₂ h₁.1 h₂.1) (by taint_decide) ?_) ?_
  · rintro p s ⟨hg, hw, hw4, hw', hc1, hc', hcx, hT, hv, hX, hN, hO, hC⟩
    have hM : 0 < p.M := by omega_using [hO]
    have hO' : wv s.mem p.L.B (slot p.L.w aR2) p.L.w < wv s.mem p.L.B (slot p.L.w aN) p.L.w := by
      rw [hX, hN]; exact hO
    refine WP.mono (stepsStart_ok hg.1.scr hg.1.rdi hg.1.hdr hg.2 hcx hO' hv (by rw [hN]; exact hC))
      fun t hI => ⟨by omega_using [hc1], s, _, ?_, hg.2, hw, hw4, hw', hc', hM, hT⟩
    rw [hX, hN] at hI; exact hI
  refine two_loop (Φ := StepsAt) (fun p => p.c) ?_ ?_
  · refine RelCT.seq (two_post (Ψ := fun (q : StPub × Nat) s => GoodL q.1.L s)
      ((two_map (fun q : StPub × Nat => (⟨q.1.L, q.1.X q.2, q.1.M⟩ : SPub)) (fun _ _ h => stepsAt_pre h.2)
        step_ct).mono (fun _ _ h => h) fun _ _ _ => trivial) ?_)
      (two_taint _ (fun q s₁ s₂ h₁ h₂ => pins_good q.1.L s₁ s₂ h₁ h₂) (by taint_decide))
    rintro ⟨p, j⟩ s ⟨hj, h⟩
    have hp := stepsAt_pre h
    obtain ⟨hg, hw, hw4, hw', hd, hv, hX, hN, hXM, hC⟩ := hp
    exact WP.mono (step_ok hg hw hw4 hw' hd hv (by rw [hX, hN]; exact hXM) (by rw [hN]; exact hC))
      fun t ⟨hg', _⟩ => hg'
  · rintro p j s hj ⟨σ, T, hI, hZ, hw, hw4, hw', hc', hM, hT⟩
    exact WP.mono (stepIter_ok hZ hw hw4 hw' hc' hM hT hj hI)
      fun t ⟨hz, hI'⟩ => ⟨eval_ne_count hj hz, fun _ => ⟨σ, T, hI', hZ, hw, hw4, hw', hc', hM, hT⟩,
        fun e => e ▸ ⟨σ, T, hI', hZ, hw, hw4, hw', hc', hM, hT⟩⟩

/-! ## The reciprocal's corrections

`recipN`'s loops branch on `v` and `d`, which agree in both runs: `d` is
`m`'s top word, and `v` starts as `guessV d`. -/

section Recip
variable {α : Type} (Φ : α → State → Prop) (D : α → Nat)

/-- `Φ`, `d = D a` in `rsi` and the word `v` in `rcx`. -/
def RD (q : α × Nat) (s : State) : Prop :=
  Φ q.1 s ∧ s.gpr .rsi = BitVec.ofNat 64 (D q.1) ∧ s.gpr .rcx = BitVec.ofNat 64 q.2 ∧ q.2 < 2 ^ 64

theorem pins_RD (n : Nat) : Pins (fun a s => RD Φ D (a, n) s) [.rcx, .rsi] := by
  intro a s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.1, h₂.2.1]

/-- With `(2^64 + v) d < 2^128`. -/
def RU (q : α × Nat) (s : State) : Prop := RD Φ D q s ∧ over q.2 (D q.1) = false

theorem pins_RU (n : Nat) : Pins (fun a s => RU Φ D (a, n) s) [.rcx, .rsi] :=
  fun a s₁ s₂ h₁ h₂ => pins_RD Φ D n a s₁ s₂ h₁.1 h₂.1

theorem downLoop_ct (hΦ : ∀ a s t, Φ a s → t.mem = s.mem → Keep [.rdx, .r14, .rax, .rcx] s t → Φ a t)
    (hD : ∀ a, D a < 2 ^ 64) :
    RelCT isa (Two (RD Φ D)) (.loop (.block recipDown) .ne) (Two (RU Φ D)) := by
  have key : ∀ n, RelCT isa (fun s₁ s₂ => ∃ a, RD Φ D (a, n) s₁ ∧ RD Φ D (a, n) s₂)
      (.loop (.block recipDown) .ne) (Two (RU Φ D)) := by
    refine RelCT.loop (M := isa) (fun n s₁ s₂ => ∃ a, RD Φ D (a, n) s₁ ∧ RD Φ D (a, n) s₂) fun n => ?_
    refine (two_post (Φ := fun a s => RD Φ D (a, n) s)
      (Ψ := fun a s => RD Φ D (a, n - (over n (D a)).toNat) s ∧ s.zf = some (!over n (D a)))
      (two_taint [.rcx, .rsi] (pins_RD Φ D n) (by taint_decide)) fun a s h => ?_).mono (fun _ _ h => h) ?_
    · exact WP.mono (down_ok h.2.2.1 h.2.2.2 h.2.1 (hD a)) fun t ⟨hcx, hz, hm, k⟩ =>
        ⟨⟨hΦ _ _ _ h.1 hm k, (k.gpr (by decide)).trans h.2.1, hcx, by omega_using [h.2.2.2]⟩, hz⟩
    · rintro s₁ s₂ ⟨a, ⟨h₁, z₁⟩, h₂, z₂⟩
      refine ⟨by simp only [eval, z₁, z₂], fun hf => ?_, fun ht => ?_⟩
      · have ho : over n (D a) = false := by
          simpa only [eval, z₁, Option.map_some, Bool.not_not, Option.some.injEq] using hf
        rw [ho, Bool.toNat_false, Nat.sub_zero] at h₁ h₂
        exact ⟨(a, n), ⟨h₁, ho⟩, h₂, ho⟩
      · have ho : over n (D a) = true := by
          simpa only [eval, z₁, Option.map_some, Bool.not_not, Option.some.injEq] using ht
        rw [ho, Bool.toNat_true] at h₁ h₂
        exact ⟨n - 1, by have := over_pos (hD a) ho; omega_using [this], a, h₁, h₂⟩
  exact fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨q, h₁, h₂⟩ e₁ e₂ => key q.2 s₁ s₂ t₁ t₂ s₁' s₂' ⟨q.1, h₁, h₂⟩ e₁ e₂

theorem upLoop_ct (hΦ : ∀ a s t, Φ a s → t.mem = s.mem → Keep [.rdx, .r11, .r14, .rax, .rcx] s t → Φ a t)
    (hD : ∀ a, D a < 2 ^ 64) :
    RelCT isa (Two (RU Φ D)) (.loop (.block recipUp) .ne)
      (Two fun q s => RU Φ D q s ∧ up q.2 (D q.1) = false) := by
  have key : ∀ n, RelCT isa (fun s₁ s₂ => ∃ a v, n = 2 ^ 64 - v ∧ RU Φ D (a, v) s₁ ∧ RU Φ D (a, v) s₂)
      (.loop (.block recipUp) .ne) (Two fun q s => RU Φ D q s ∧ up q.2 (D q.1) = false) := by
    refine RelCT.loop (M := isa) (fun n s₁ s₂ => ∃ a v, n = 2 ^ 64 - v ∧ RU Φ D (a, v) s₁ ∧ RU Φ D (a, v) s₂)
      fun n => ?_
    refine RelCT.mono (P := Two fun (q : α × Nat) s => n = 2 ^ 64 - q.2 ∧ RU Φ D q s) ?_
      (fun s₁ s₂ ⟨a, v, hn, h₁, h₂⟩ => ⟨(a, v), ⟨hn, h₁⟩, hn, h₂⟩) (fun _ _ h => h)
    refine (two_post (Φ := fun (q : α × Nat) s => n = 2 ^ 64 - q.2 ∧ RU Φ D q s)
      (Ψ := fun q s => n = 2 ^ 64 - q.2 ∧ RD Φ D (q.1, q.2 + (up q.2 (D q.1)).toNat) s ∧
        over q.2 (D q.1) = false ∧ s.zf = some (!up q.2 (D q.1)))
      (two_taint [.rcx, .rsi] (fun q s₁ s₂ h₁ h₂ => pins_RU Φ D q.2 q.1 s₁ s₂ h₁.2 h₂.2) (by taint_decide))
      fun q s h => ?_).mono (fun _ _ h => h) ?_
    · obtain ⟨hn, ⟨hΦ', hsi, hcx, hv⟩, ho⟩ := h
      have hb : q.2 + (up q.2 (D q.1)).toNat < 2 ^ 64 := by
        cases hu : up q.2 (D q.1)
        · rw [Bool.toNat_false, Nat.add_zero]; exact hv
        · unfold up at hu
          rw [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hu
          rw [Bool.toNat_true]; omega_using [hv, hu.1]
      exact WP.mono (up_ok hcx hv hsi (hD q.1)) fun t ⟨hcx', hz, hm, k⟩ =>
        ⟨hn, ⟨hΦ _ _ _ hΦ' hm k, (k.gpr (by decide)).trans hsi, hcx', hb⟩, ho, hz⟩
    · rintro s₁ s₂ ⟨⟨a, v⟩, ⟨hn, h₁, ho, z₁⟩, -, h₂, -, z₂⟩
      refine ⟨by simp only [eval, z₁, z₂], fun hf => ?_, fun ht => ?_⟩
      · have hu : up v (D a) = false := by
          simpa only [eval, z₁, Option.map_some, Bool.not_not, Option.some.injEq] using hf
        rw [hu, Bool.toNat_false, Nat.add_zero] at h₁ h₂
        exact ⟨(a, v), ⟨⟨h₁, ho⟩, hu⟩, ⟨h₂, ho⟩, hu⟩
      · have hu : up v (D a) = true := by
          simpa only [eval, z₁, Option.map_some, Bool.not_not, Option.some.injEq] using ht
        rw [hu, Bool.toNat_true] at h₁ h₂
        unfold up at hu
        rw [Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true', decide_eq_false_iff_not] at hu
        exact ⟨2 ^ 64 - (v + 1), by omega_using [hn, h₁.2.2.2, hu.1], a, v + 1, rfl, ⟨h₁, hu.2⟩, h₂, hu.2⟩
  exact fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨q, h₁, h₂⟩ e₁ e₂ =>
    key (2 ^ 64 - q.2) s₁ s₂ t₁ t₂ s₁' s₂' ⟨q.1, q.2, rfl, h₁, h₂⟩ e₁ e₂

end Recip

/-! ## `fast` -/

/-- What `fast` keeps from `R - m` on, `x = R - m`. -/
def FX (p : R2Pub) (s : State) : Prop :=
  GoodL p.L s ∧ 4 ≤ p.L.w ∧ p.L.w < 2 ^ 30 ∧ p.L.w % 4 = 0 ∧ wv s.mem p.L.B (slot p.L.w aN) p.L.w = p.N ∧
    2 ^ 63 ≤ (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat ∧
    wv s.mem p.L.B (slot p.L.w aR2) p.L.w = 2 ^ (64 * p.L.w) - p.N ∧ 2 ^ (64 * p.L.w) - p.N < p.N

/-- After `R - m`. -/
def FX2 (p : R2Pub) (s : State) : Prop :=
  FX p s ∧ s.gpr .rbx = off p.L.B (slot p.L.w aR2) ∧ s.gpr .r10 = off p.L.B (slot p.L.w aN) ∧
    s.gpr .r12 = BitVec.ofNat 64 p.L.w

/-- Before the copy into the accumulator. -/
def FX3 (p : R2Pub) (s : State) : Prop :=
  FX p s ∧ s.gpr .r8 = off p.L.B (slot p.L.w aR2) ∧ s.gpr .rbx = off p.L.B (slot p.L.w aAcc) ∧
    s.gpr .r10 = off p.L.B (slot p.L.w aN) ∧ s.gpr .r12 = BitVec.ofNat 64 p.L.w

/-- With `mc = R - m` in the accumulator. -/
def FXA (p : R2Pub) (s : State) : Prop :=
  FX p s ∧ wv s.mem p.L.B (slot p.L.w aAcc) p.L.w + p.N = 2 ^ (64 * p.L.w) ∧
    s.gpr .r10 = off p.L.B (slot p.L.w aN) ∧ s.gpr .r12 = BitVec.ofNat 64 p.L.w

/-- Before `v`. -/
def FX5 (p : R2Pub) (s : State) : Prop := FXA p s ∧ s.gpr .r8 = off p.L.B (slot p.L.w aTmp)

/-- After `v`. -/
def FX6 (p : R2Pub) (s : State) : Prop :=
  GoodL p.L s ∧ 4 ≤ p.L.w ∧ p.L.w < 2 ^ 30 ∧ p.L.w % 4 = 0 ∧ wv s.mem p.L.B (slot p.L.w aN) p.L.w = p.N ∧
    2 ^ 63 ≤ (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat ∧
    wv s.mem p.L.B (slot p.L.w aR2) p.L.w = 2 ^ (64 * p.L.w) - p.N ∧ 2 ^ (64 * p.L.w) - p.N < p.N ∧
    wv s.mem p.L.B (slot p.L.w aAcc) p.L.w + p.N = 2 ^ (64 * p.L.w) ∧
    (word s.mem p.L.B (slot p.L.w aTmp)).toNat =
      (2 ^ 128 - 1) / (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat - 2 ^ 64

theorem pins_FX2 : Pins FX2 [.rbx, .r10, .r12, .rdi] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.2.2, h₂.2.2.2]
  · rw [h₁.1.1.1.rdi, h₂.1.1.1.rdi]

theorem pins_FX3 : Pins FX3 [.r8, .rbx, .r12] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h₁.2.1, h₂.2.1]
  · rw [h₁.2.2.1, h₂.2.2.1]
  · rw [h₁.2.2.2.2, h₂.2.2.2.2]

theorem pins_FX5 : Pins FX5 [.r10, .r12, .r8] := by
  intro p s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [h₁.1.2.2.1, h₂.1.2.2.1]
  · rw [h₁.1.2.2.2, h₂.1.2.2.2]
  · rw [h₁.2, h₂.2]

theorem FX.congr {p : R2Pub} {s t : State} (h : FX p s) (hm : t.mem = s.mem) (hw : t.wr = s.wr)
    (hdi : t.gpr .rdi = s.gpr .rdi) : FX p t := by
  obtain ⟨hg, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨GoodL.congr hg hm hw hdi, h1, h2, h3, hm ▸ h4, hm ▸ h5, hm ▸ h6, h7⟩

/-- `m`'s top word, a word under `FX`. -/
def topW (p : R2Pub) : Nat := p.top % 2 ^ 64

theorem FX.top {p : R2Pub} {s : State} (h : FX p s) :
    word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1)) = BitVec.ofNat 64 (topW p) := by
  obtain ⟨-, hw, -, -, hn, -⟩ := h
  have hsplit : p.N = p.N % 2 ^ (64 * (p.L.w - 1)) +
      2 ^ (64 * (p.L.w - 1)) * (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat := by
    have e : wv s.mem p.L.B (slot p.L.w aN) (p.L.w - 1 + 1) = p.N := by
      rw [Nat.sub_add_cancel (by omega_using [hw])]; exact hn
    rw [wv] at e
    have hlt := wv_lt s.mem p.L.B (slot p.L.w aN) (p.L.w - 1)
    rw [← e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  have hT : (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat = p.top := by
    unfold R2Pub.top
    have hP := Nat.two_pow_pos (64 * (p.L.w - 1))
    have := Nat.mod_lt p.N hP
    rw [Nat.div_eq_of_lt_le (k := (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat) ?_ ?_]
    · rw [Nat.mul_comm]; omega
    · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]; omega
  apply BitVec.eq_of_toNat_eq
  rw [hT, BitVec.toNat_ofNat, topW, Nat.mod_mod]
  exact (Nat.mod_eq_of_lt (hT ▸ BitVec.isLt _)).symm

theorem FX5.keep {p : R2Pub} {s t : State} {rs : List Reg} (h : FX5 p s) (hm : t.mem = s.mem) (k : Keep rs s t)
    (h10 : .r10 ∉ rs) (h12 : .r12 ∉ rs) (h8 : .r8 ∉ rs) (hdi : .rdi ∉ rs) : FX5 p t :=
  ⟨⟨FX.congr h.1.1 hm k.2.2 (k.gpr hdi), hm ▸ h.1.2.1, (k.gpr h10).trans h.1.2.2.1, (k.gpr h12).trans h.1.2.2.2⟩,
    (k.gpr h8).trans h.2⟩

/-- `recipN` leaks the same in runs that agree on `m`: its loops branch on
`m`'s top word and on `v`, which starts as `guessV` of it. -/
theorem recipN_ct : RelCT isa (Two FX5) recipN (Two FX6) := by
  have hD : ∀ p, topW p < 2 ^ 64 := fun p => Nat.mod_lt _ (by decide)
  unfold recipN
  simp only [seqs]
  -- The guess.
  have hguess : RelCT isa (Two FX5) (.block recipGuess) (Two (RD FX5 topW)) := by
    refine (two_piece (Ψ := fun p s => RD FX5 topW (p, (guessV (BitVec.ofNat 64 (topW p))).toNat) s)
      _ pins_FX5 (by taint_decide) fun p s h => ?_).mono (fun _ _ h => h)
        fun s₁ s₂ ⟨p, h₁, h₂⟩ => ⟨(p, (guessV (BitVec.ofNat 64 (topW p))).toNat), h₁, h₂⟩
    have hg := h.1.1.1
    have hs := hg.1.scr
    have hZ := hg.2
    have hsm := slot_le (w := p.L.w) (show aN < 8 by decide)
    refine WP.mono (recipGuess_ok hs h.1.2.2.1 h.1.2.2.2 (by have := h.1.1.2.1; omega_using [this])
      (by omega_using [hZ, hsm])) fun t ⟨hsi, hcx, hm, k⟩ => ?_
    rw [FX.top h.1.1] at hsi hcx
    exact ⟨FX5.keep h hm k (by decide) (by decide) (by decide) (by decide), hsi,
      by rw [hcx, BitVec.ofNat_toNat, BitVec.setWidth_eq], BitVec.isLt _⟩
  refine RelCT.seq hguess ?_
  -- The corrections.
  refine RelCT.seq (downLoop_ct FX5 topW (fun p s t h hm k => FX5.keep h hm k (by decide) (by decide)
    (by decide) (by decide)) hD) ?_
  refine RelCT.seq (upLoop_ct FX5 topW (fun p s t h hm k => FX5.keep h hm k (by decide) (by decide)
    (by decide) (by decide)) hD) ?_
  -- `v` to the temporary.
  refine (two_piece (Ψ := fun q s => FX6 q.1 s) [.r8] (fun q s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; rw [h₁.1.1.1.2, h₂.1.1.1.2])
    (by taint_decide) fun q s h => ?_).mono (fun _ _ h => h) fun s₁ s₂ ⟨q, h₁, h₂⟩ => ⟨q.1, h₁, h₂⟩
  obtain ⟨⟨⟨hfx, hsi, hcx, hv⟩, ho⟩, hu⟩ := h
  obtain ⟨⟨⟨hg, hw, hw', h4, hN, hT, hX, hO⟩, hc, h10, h12⟩, h8⟩ := hfx
  have hs := hg.1.scr
  have hnw := hs.nowrap
  have hZ := hg.2
  have hsx := slot_le (w := q.1.L.w) (show aR2 < 8 by decide)
  have hsm := slot_le (w := q.1.L.w) (show aN < 8 by decide)
  have hsv := slot_le (w := q.1.L.w) (show aTmp < 8 by decide)
  have hsa := slot_le (w := q.1.L.w) (show aAcc < 8 by decide)
  have sXV := slot_sep (w := q.1.L.w) (show aR2 ≠ aTmp by decide)
  have sMV := slot_sep (w := q.1.L.w) (show aN ≠ aTmp by decide)
  have sAV := slot_sep (w := q.1.L.w) (show aAcc ≠ aTmp by decide)
  have eT : (word s.mem q.1.L.B (slot q.1.L.w aN + 8 * (q.1.L.w - 1))).toNat = topW q.1 := by
    rw [FX.top ⟨hg, hw, hw', h4, hN, hT, hX, hO⟩, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hD _)]
  have hvx := recip_exact (by rw [← eT]; exact hT) (hD q.1) ho hu
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW (off q.1.L.B (slot q.1.L.w aTmp))
      (BitVec.ofNat 64 ((2 ^ 128 - 1) / (word s.mem q.1.L.B (slot q.1.L.w aN + 8 * (q.1.L.w - 1))).toNat - 2 ^ 64)))
    (by
      xrun [State.ea, at0, h8, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
        hs.st (show slot q.1.L.w aTmp + 8 ≤ q.1.L.Z by omega_using [hZ, hsv])]
      rw [hcx, hvx, eT]) rfl) fun t ⟨hm, k⟩ => ?_
  have o : Outside q.1.L.B (slot q.1.L.w aTmp) 8 s.mem t.mem := by rw [hm]; exact writeW_outside _ _ _ (by omega_using [hnw, hZ, hsv])
  have ha : Arrays q.1.L.B q.1.L.w [aTmp] s.mem t.mem :=
    Arrays.of_outside (List.mem_singleton_self _) o (Nat.le_refl _) (by omega_using [])
  have hvlt : (2 ^ 128 - 1) / (word s.mem q.1.L.B (slot q.1.L.w aN + 8 * (q.1.L.w - 1))).toNat - 2 ^ 64 < 2 ^ 64 := by
    have : (2 ^ 128 - 1) / (word s.mem q.1.L.B (slot q.1.L.w aN + 8 * (q.1.L.w - 1))).toNat < 2 ^ 65 := by
      rw [Nat.div_lt_iff_lt_mul (by omega_using [hT])]; omega_using [hT]
    omega_using [this]
  have hT₁ : word t.mem q.1.L.B (slot q.1.L.w aN + 8 * (q.1.L.w - 1)) =
      word s.mem q.1.L.B (slot q.1.L.w aN + 8 * (q.1.L.w - 1)) := o.word (by omega_using [sMV]) (by omega_using [hnw, hZ, hsm])
  refine ⟨⟨⟨hs.congr k.2.2, (k.gpr (by decide)).trans hg.1.rdi, ha.hdr hg.1.hdr⟩, hZ⟩, hw, hw', h4,
    by rw [o.wv (by omega_using [sMV]) (by omega_using [hnw, hZ, hsm])]; exact hN, by rw [hT₁]; exact hT,
    by rw [o.wv (by omega_using [sXV]) (by omega_using [hnw, hZ, hsx])]; exact hX, hO, by rw [o.wv (by omega_using [sAV]) (by omega_using [hnw, hZ, hsa])]; exact hc, ?_⟩
  rw [hT₁, hm, word_writeW_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvlt]

/-- `fast` leaks the same in runs that agree on `m`. -/
theorem fast_ct : RelCT isa (Two R2w.FPre) fast fun _ _ => True := by
  rw [fast_eq]
  -- The loads.
  refine RelCT.seq (two_piece (Ψ := R2w.F1) _ (pins_rdi_of (·.L) fun _ _ h => h.1.1) (by taint_decide) ?_) ?_
  · intro p s h
    have hg := h.1.1
    have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.L.B (8 * i)) 8 := fun i hi =>
      hg.1.scr.ld (by have := hdr_lt_slot p.L.w 8 hi; have := hg.2; omega_arith)
    refine WP.mono (WP.keep [.rbx, .r10, .r12, .r8, .rbp] (Q := fun t =>
        t.gpr .rbx = off p.L.B (slot p.L.w aR2) ∧ t.gpr .r10 = off p.L.B (slot p.L.w aN) ∧
        t.gpr .r12 = BitVec.ofNat 64 p.L.w ∧ t.gpr .r8 = off p.L.B (slot p.L.w aTmp) ∧ t.gpr .rbp = mask false ∧
        t.mem = s.mem) (by
      xrun [State.ea, hdr, hg.1.rdi, hdrOff, hl (sArr aR2) (by decide), hl (sArr aN) (by decide), hl sW (by decide),
        hl (sArr aTmp) (by decide), hg.1.hdr.harr aR2 (by decide), hg.1.hdr.harr aN (by decide), hg.1.hdr.hw,
        hg.1.hdr.harr aTmp (by decide)]) rfl)
      fun t ⟨⟨hbx, h10, h12, h8, hbp, hm⟩, k⟩ => ⟨⟨?_, h.2⟩, hbx, hbp, h8⟩
    obtain ⟨⟨hg, hw, hw', hN, hinv, -, -, hodd, hlo⟩, -⟩ := h
    exact ⟨GoodL.congr hg hm k.2.2 (k.gpr (by decide)), hw, hw', hm ▸ hN, hm ▸ hinv, h12, h10, hodd, hlo⟩
  -- `R - m`.
  refine RelCT.seq (two_piece (Ψ := FX2) _ R2w.pins_F1 (by taint_decide) ?_) ?_
  · rintro p s ⟨⟨⟨hg, hw, hw', hN, hinv, h12, h10, hodd, hlo⟩, hT, h4⟩, hbx, hbp, h8⟩
    obtain ⟨hT', -⟩ := R2Pre.top ⟨hg, hw, hw', hN, hinv, h12, h10, hodd, hlo⟩
    have hs := hg.1.scr
    have hnw := hs.nowrap
    have hZ := hg.2
    have hsx := slot_le (w := p.L.w) (show aR2 < 8 by decide)
    have hsm := slot_le (w := p.L.w) (show aN < 8 by decide)
    have sXM := slot_sep (w := p.L.w) (show aR2 ≠ aN by decide)
    have hN0 : 0 < wv s.mem p.L.B (slot p.L.w aN) p.L.w := by rw [hN]; omega_using [hodd]
    have hng := R2w.neg_ok hs hbx h10 h12 hbp (by omega_using [hw]) (by omega_using [hw']) (by omega_using [hZ, hsx]) (by omega_using [hZ, hsm]) (by omega_using [sXM]) hN0
    refine WP.mono hng fun t ⟨hx, ho, k⟩ => ?_
    have ha : Arrays p.L.B p.L.w [aR2] s.mem t.mem :=
      Arrays.of_outside (List.mem_singleton_self _) ho (Nat.le_refl _) (by omega_using [])
    have hn' : p.L.B.toNat + slot p.L.w 8 ≤ 2 ^ 64 := by omega_using [hnw, hZ]
    have hhalf : 2 ^ (64 * p.L.w) < 2 * p.N := by
      have e : p.N = wv s.mem p.L.B (slot p.L.w aN) (p.L.w - 1) +
          2 ^ (64 * (p.L.w - 1)) * (word s.mem p.L.B (slot p.L.w aN + 8 * (p.L.w - 1))).toNat := by
        rw [← hN, show p.L.w = (p.L.w - 1) + 1 by omega_using [hw], wv_succ, show p.L.w - 1 + 1 - 1 = p.L.w - 1 by omega_using []]
      have hp : 2 ^ (64 * p.L.w) = 2 * (2 ^ (64 * (p.L.w - 1)) * 2 ^ 63) := by
        rw [← Nat.pow_add, show 64 * p.L.w = 1 + (64 * (p.L.w - 1) + 63) by omega_using [hw], Nat.pow_add, Nat.pow_one]
      rw [hT'] at e
      have hle := Nat.mul_le_mul_left (2 ^ (64 * (p.L.w - 1))) hT
      have hev : 2 ^ (64 * (p.L.w - 1)) * 2 ^ 63 % 2 = 0 := by
        rw [Nat.mul_mod, show 2 ^ 63 % 2 = 0 by decide, Nat.mul_zero, Nat.zero_mod]
      omega_using [hodd, e, hp, hle]
    have hNR : p.N < 2 ^ (64 * p.L.w) := hN ▸ wv_lt _ _ _ _
    refine ⟨⟨⟨⟨hs.congr k.2.2, (k.gpr (by decide)).trans hg.1.rdi, ha.hdr hg.1.hdr⟩, hZ⟩, by omega_using [hw, h4], hw', h4,
      by rw [ha.wv_of_not_mem (by decide) (by decide) hn']; exact hN,
      by rw [ho.word (by omega_using [sXM]) (by omega_using [hsm, hn']), hT']; exact hT, by rw [hx, hN], by omega_using [hhalf, hNR]⟩,
      (k.gpr (by decide)).trans hbx, (k.gpr (by decide)).trans h10, (k.gpr (by decide)).trans h12⟩
  -- `mc`'s bases.
  refine RelCT.seq (two_piece (Ψ := FX3) _ pins_FX2 (by taint_decide) ?_) ?_
  · rintro p s ⟨hx, hbx, h10, h12⟩
    have hg := hx.1
    have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.L.B (8 * i)) 8 := fun i hi =>
      hg.1.scr.ld (by have := hdr_lt_slot p.L.w 8 hi; have := hg.2; omega_arith)
    refine WP.mono (WP.keep [.r8, .rbx] (Q := fun t => t.gpr .r8 = off p.L.B (slot p.L.w aR2) ∧
        t.gpr .rbx = off p.L.B (slot p.L.w aAcc) ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, hg.1.rdi, hdrOff, hl (sArr aAcc) (by decide), hg.1.hdr.harr aAcc (by decide), hbx]) rfl)
      fun t ⟨⟨h8, hb, hm⟩, k⟩ => ⟨FX.congr hx hm k.2.2 (k.gpr (by decide)), h8, hb,
        (k.gpr (by decide)).trans h10, (k.gpr (by decide)).trans h12⟩
  -- `mc := x`.
  refine RelCT.seq (two_post (Ψ := FXA) (two_taint _ pins_FX3 (by taint_decide)) ?_) ?_
  · rintro p s ⟨hx, h8, hbx, h10, h12⟩
    have hx' := hx
    obtain ⟨hg, hw, hw', h4, hN, hT, hX, hO⟩ := hx'
    have hs := hg.1.scr
    have hnw := hs.nowrap
    have hZ := hg.2
    have hsx := slot_le (w := p.L.w) (show aR2 < 8 by decide)
    have hsm := slot_le (w := p.L.w) (show aN < 8 by decide)
    have hsa := slot_le (w := p.L.w) (show aAcc < 8 by decide)
    have sXA := slot_sep (w := p.L.w) (show aR2 ≠ aAcc by decide)
    have sMA := slot_sep (w := p.L.w) (show aN ≠ aAcc by decide)
    unfold R2Words.copyBack
    refine WP.seq (WP.mono (WP.keep [.rsi] (Q := fun t => t.gpr .rsi = off p.L.B (slot p.L.w aR2) ∧ t.mem = s.mem)
      (by xrun [h8]) rfl) fun t₁ ⟨⟨hsi, hm₁⟩, k₁⟩ => ?_)
    have hs₁ := hs.congr k₁.2.2
    have hsepw : ∀ j < p.L.w, ∀ b < 8, ofs p.L.B (off p.L.B (slot p.L.w aR2 + 8 * j) + BitVec.ofNat 64 b) <
        slot p.L.w aAcc ∨ slot p.L.w aAcc + 8 * p.L.w ≤ ofs p.L.B (off p.L.B (slot p.L.w aR2 + 8 * j) +
          BitVec.ofNat 64 b) := fun j hj b hb => by
      rw [ofs_off p.L.B (by omega_using [hnw, hZ, hsx, hj, hb])]; omega_using [sXA, hj, hb]
    refine WP.mono (copyWords_ok (S := p.L.B) (D := p.L.B) hsi ((k₁.gpr (by decide)).trans hbx)
      ((k₁.gpr (by decide)).trans h12) (by omega_using [hw]) (by omega_using [hw']) (by omega_using [hnw, hZ, hsa]) (fun j hj => hs₁.ld (by omega_using [hZ, hsx, hj]))
      (fun j hj => hs₁.st (by omega_using [hZ, hsa, hj])) hsepw) fun t ⟨hc, _, ho, k⟩ => ?_
    rw [hm₁] at hc ho
    have ha : Arrays p.L.B p.L.w [aAcc] s.mem t.mem :=
      Arrays.of_outside (List.mem_singleton_self _) ho (Nat.le_refl _) (by omega_using [])
    have kk := k₁.trans k
    have hn' : p.L.B.toNat + slot p.L.w 8 ≤ 2 ^ 64 := by omega_using [hnw, hZ]
    have hNR : p.N < 2 ^ (64 * p.L.w) := hN ▸ wv_lt _ _ _ _
    refine ⟨⟨⟨⟨hs.congr (k.2.2.trans k₁.2.2), (kk.gpr (by decide)).trans hg.1.rdi, ha.hdr hg.1.hdr⟩, hZ⟩, hw, hw', h4,
      by rw [ha.wv_of_not_mem (by decide) (by decide) hn']; exact hN,
      by rw [ho.word (by omega_using [sMA]) (by omega_using [hsm, hn'])]; exact hT,
      by rw [ha.wv_of_not_mem (by decide) (by decide) hn']; exact hX, hO⟩,
      by rw [hc, hX]; omega_using [hNR], (kk.gpr (by decide)).trans h10, (kk.gpr (by decide)).trans h12⟩
  -- `v`'s bases.
  refine RelCT.seq (two_piece (Ψ := FX5) _ (pins_rdi_of (·.L) fun _ _ h => h.1.1) (by taint_decide) ?_) ?_
  · rintro p s ⟨hx, hc, h10, h12⟩
    have hg := hx.1
    have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.L.B (8 * i)) 8 := fun i hi =>
      hg.1.scr.ld (by have := hdr_lt_slot p.L.w 8 hi; have := hg.2; omega_arith)
    refine WP.mono (WP.keep [.rbx, .r8] (Q := fun t => t.gpr .r8 = off p.L.B (slot p.L.w aTmp) ∧ t.mem = s.mem) (by
      xrun [State.ea, hdr, hg.1.rdi, hdrOff, hl (sArr aR2) (by decide), hl (sArr aTmp) (by decide),
        hg.1.hdr.harr aR2 (by decide), hg.1.hdr.harr aTmp (by decide)]) rfl)
      fun t ⟨⟨h8, hm⟩, k⟩ => ⟨⟨FX.congr hx hm k.2.2 (k.gpr (by decide)), hm ▸ hc, (k.gpr (by decide)).trans h10,
        (k.gpr (by decide)).trans h12⟩, h8⟩
  -- `v`.
  refine RelCT.seq recipN_ct ?_
  -- The count.
  refine RelCT.seq (two_piece (Ψ := fun p s => FX6 p s ∧ s.gpr .rcx = BitVec.ofNat 64 p.L.w) _
    (pins_rdi_of (·.L) fun _ _ h => h.1) (by taint_decide) ?_) ?_
  · intro p s h
    have hg := h.1
    have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.L.B (8 * i)) 8 := fun i hi =>
      hg.1.scr.ld (by have := hdr_lt_slot p.L.w 8 hi; have := hg.2; omega_arith)
    refine WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 p.L.w ∧ t.mem = s.mem)
      (by xrun [State.ea, hdr, hg.1.rdi, hdrOff, hl sW (by decide), hg.1.hdr.hw]) rfl) fun t ⟨⟨hcx, hm⟩, k⟩ => ⟨?_, hcx⟩
    obtain ⟨hg, hw, hw', h4, hN, hT, hX, hO, hc, hv⟩ := h
    exact ⟨GoodL.congr hg hm k.2.2 (k.gpr (by decide)), hw, hw', h4, hm ▸ hN, hm ▸ hT, hm ▸ hX, hO, hm ▸ hc, hm ▸ hv⟩
  -- The steps.
  refine (two_map (fun p : R2Pub => (⟨p.L, p.L.w, p.N⟩ : StPub)) (fun p s h => ?_) steps_ct).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  obtain ⟨⟨hg, hw, hw', h4, hN, hT, hX, hO, hc, hv⟩, hcx⟩ := h
  exact ⟨hg, hw, h4, hw', show 1 ≤ p.L.w by omega_using [hw], show p.L.w < 2 ^ 31 by omega_using [hw'], hcx, hT, hv, hX, hN, hO, hc⟩

/-! ## The choice -/

/-- `choice` leaks the same in runs that agree on `m`. -/
theorem choice_ct (M : Mont) : RelCT isa (Two R2Pre) (R2Adx.choice M.mm) fun _ _ => True := by
  unfold R2Adx.choice
  refine RelCT.seq (two_piece (Ψ := R2w.R2t) _ pins_r2Pre (by taint_decide) ?_) ?_
  · intro p s h
    obtain ⟨hT, -⟩ := h.top
    have hn := h.1.1.scr.nowrap
    have := slot_le (w := p.L.w) (show aN < 8 by decide)
    refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t => t.zf = some (decide (2 ^ 63 ≤ p.top ∧ p.L.w % 4 = 0)) ∧
        t.mem = s.mem) (by
      unfold R2Words.fastTest
      xrun [State.ea, ix, addrm8 h.2.2.2.2.2.2.1 h.2.2.2.2.2.1 (by have := h.2.1; omega_arith),
        h.1.1.scr.ld (show slot p.L.w aN + 8 * (p.L.w - 1) + 8 ≤ p.L.Z by have := h.1.2; omega_arith)]
      rw [h.2.2.2.2.2.1]
      refine (R2w.fastFlag _ (by have := h.2.2.1; omega_arith)).trans ?_
      rw [← hT]) rfl) fun t ⟨⟨hz, hm⟩, k⟩ => ⟨?_, hz⟩
    obtain ⟨hg, hw, hw', hN, hinv, h12, h10, hodd, hlo⟩ := h
    exact ⟨⟨⟨hg.1.scr.congr k.2.2, (k.gpr (by decide)).trans hg.1.rdi, hm ▸ hg.1.hdr⟩, hg.2⟩, hw, hw',
      hm ▸ hN, hm ▸ hinv, (k.gpr (by decide)).trans h12, (k.gpr (by decide)).trans h10, hodd, hlo⟩
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) ?_ ?_
  · exact two_map id (fun p s ⟨⟨h, hz⟩, hc⟩ => by
      simp only [eval, hz, Option.some.injEq, decide_eq_true_eq] at hc
      exact ⟨h, hc.1, hc.2⟩) fast_ct
  · rw [R2w.old_eq]
    exact two_map id (fun p s h => h.1.1) (r2_ct M)

end VG.Proof.Bignum.X86_64.R2ax

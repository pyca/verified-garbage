module

-- separate module: a group's lanes, which the steps' proofs do not change

public import VerifiedGarbage.Proof.SlhDsa.AArch64.VerifyXmssLanes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.SlhDsa.AArch64.TopLanes
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64, `xmssPk`: the lanes of a group of chains

`chainLanes` sets up lane `k` of group `g` for chain `c = cOf p g k`: its
address's type (`WOTS_HASH`), key pair (`idx`) and chain (`c`), its message
the signature's value of chain `c`, and the group's first step, the least of
the lanes' digits, in `x24` (`lane_ok`, `chainLanes_ok`).
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.XmssPk

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Proof.MlKem.AArch64 (Only Keep)
open VG.Proof.SlhDsa.AArch64.TreeBase (Up in_scr in_scr' wp_subr wp_lsr wp_movz wp_and wp_eor wp_addr wp_mov)

variable {p : Params}

/-- What lane `k` (of `A`) holds for chain `c`: its address's type, key
pair and chain, and its message `X`. -/
structure LaneC (p : Params) (m : Mem) (S : Addr) (k idx c : Nat) (X : List Byte) : Prop where
  ty : bytesAt m (at' S (Layout.laneA k + p.n + 16)) 4 = toByte 0 4
  kp : bytesAt m (at' S (Layout.laneA k + p.n + 20)) 4 = toByte idx 4
  ch : bytesAt m (at' S (Layout.laneA k + p.n + 24)) 4 = toByte c 4
  msg : bytesAt m (at' S (Layout.laneA k + p.n + 32)) p.n = X

/-- The ranges lane `k`'s setup writes. -/
def laneW (p : Params) (S : Addr) (k : Nat) : List Region :=
  [⟨at' S (Layout.laneA k + p.n + 16), 12⟩, ⟨at' S (Layout.laneA k + p.n + 32), p.n⟩]

/-- The facts of the state a lane's setup runs from. -/
structure LaneIn (p : Params) (S sig : Addr) (t : State) : Prop where
  x19 : t.gpr .x19 = S
  x21 : t.gpr .x21 = sig
  x20 : (t.gpr .x20).toNat < 2 ^ 32
  scr : (⟨S, 65536⟩ : Region) ∈ t.wr
  insig : (⟨sig, p.xmssSigLen⟩ : Region) ∈ t.rd
  dsig : Region.Disjoint ⟨sig, p.xmssSigLen⟩ ⟨S, 65536⟩
  slen : p.xmssSigLen ≤ 2 ^ 64

theorem xmssSigLen_eq' : p.xmssSigLen = p.len * p.n + p.hp * p.n := by
  simp only [Params.xmssSigLen]; rw [Nat.add_mul]

/-- The setup of lane `k` of group `g`. -/
theorem lane_ok (hz : Sz p) {g k : Nat} (hg : 4 * g < p.len) (hk : k < 4) {t : State} {S sig : Addr}
    (hI : LaneIn p S sig t) (h22 : t.gpr .x22 = BitVec.ofNat 64 (4 * g)) {mn : Nat} (hmn : mn < 16)
    (h24 : t.gpr .x24 = BitVec.ofNat 64 mn) {is : List Instr} {Q : State → Prop}
    (K : ∀ t', Keep [.x9, .x10, .x11, .x12, .x13, .x14, .x15, .x24] t t' → Frame (laneW p S k) t.mem t'.mem →
      LaneC p t'.mem S k (t.gpr .x20).toNat (cOf p g k) (bytesAt t.mem (sig + BitVec.ofNat 64 (cOf p g k * p.n)) p.n) →
      t'.gpr .x24 = BitVec.ofNat 64 (min mn (digitAt t.mem S (cOf p g k))) → WP isa (.block is) t' Q) :
    WP isa (.block (Impl.SlhDsa.AArch64.Verify.chainOf p k ++
      Impl.SlhDsa.AArch64.setField .x19 (Layout.laneA k + p.n + 16) 0 ++
      Impl.SlhDsa.AArch64.setFieldR .x19 (Layout.laneA k + p.n + 20) .x20 ++
      Impl.SlhDsa.AArch64.setFieldR .x19 (Layout.laneA k + p.n + 24) .x10 ++
      Impl.SlhDsa.AArch64.Verify.chainSig p ++
      Impl.SlhDsa.AArch64.copyWords .x19 (Layout.laneA k + (p.n + 32)) .x12 0 (p.n / 8) ++
      ([.sub .x .x13 .x24 .x11, .lsr .x .x13 .x13 63, .movz .x .x15 0 0, .sub .x .x15 .x15 .x13,
        .logic .eor .x .x13 .x11 .x24, .logic .and .x .x13 .x13 .x15, .logic .eor .x .x24 .x13 .x11] : List Instr) ++
      is)) t Q := by
  have hn32 := hz.n32
  have hn16 := hz.n16
  have hn8 := hz.n8
  have hl := hz.len
  have eA : Layout.laneA k = 3136 + 128 * k := rfl
  have hcl : cOf p g k < p.len := by simp only [cOf]; omega_using [hl, hn32]
  simp only [List.append_assoc]
  refine chainOf_ok hz hg hk hI.x19 h22 hI.scr fun t₁ o₁ c₁ d₁ => ?_
  have g19 : t₁.gpr .x19 = S := by rw [o₁.get .x19, hI.x19]
  refine setField_ok (b := .x19) (by decide) ⟨by rw [eA]; omega, by rw [eA]; omega⟩
    (by rw [g19, o₁.wr]; exact in_scr hI.scr (by rw [eA]; omega)) fun t₂ f₂ => ?_
  refine setFieldR_ok (b := .x19) (r := .x20) (by decide)
    (by rw [f₂.keep.get .x20, o₁.get .x20]; exact hI.x20) ⟨by rw [eA]; omega, by rw [eA]; omega⟩
    (by rw [f₂.keep.get .x19, g19, f₂.keep.wr, o₁.wr]; exact in_scr hI.scr (by rw [eA]; omega)) fun t₃ f₃ => ?_
  refine setFieldR_ok (b := .x19) (r := .x10) (by decide)
    (by rw [f₃.keep.get .x10, f₂.keep.get .x10, c₁, BitVec.toNat_ofNat]; omega_using [hcl, hl, hn32])
    ⟨by rw [eA]; omega, by rw [eA]; omega⟩
    (by rw [f₃.keep.get .x19, f₂.keep.get .x19, g19, f₃.keep.wr, f₂.keep.wr, o₁.wr]
        exact in_scr hI.scr (by rw [eA]; omega)) fun t₄ f₄ => ?_
  simp only [Impl.SlhDsa.AArch64.Verify.chainSig, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_mov fun t₅ u₅ => mulN_ok hz.nv (r := .x12) (tmp := .x13) (by decide) fun t₆ o₆ e₆ =>
    wp_addr fun t₇ u₇ => ?_
  have K₄ : Keep [.x10, .x13, .x14, .x15, .x11, .x9, .x9, .x9] t t₄ :=
    ((o₁.keep.trans f₂.keep).trans (f₃.keep.trans f₄.keep))
  have e10 : t₄.gpr .x10 = BitVec.ofNat 64 (cOf p g k) := by
    rw [f₄.keep.get .x10, f₃.keep.get .x10, f₂.keep.get .x10, c₁]
  have e12 : t₇.gpr .x12 = sig + BitVec.ofNat 64 (cOf p g k * p.n) := by
    rw [u₇.gpr, e₆, u₅.gpr, e10, o₆.get .x21, u₅.other _ (by decide), K₄.get .x21, hI.x21,
      ← BitVec.ofNat_mul, BitVec.add_comm]
  have hcn : cOf p g k * p.n + p.n ≤ p.xmssSigLen := by
    rw [xmssSigLen_eq', ← Nat.succ_mul]
    exact Nat.le_trans (Nat.mul_le_mul_right _ (show cOf p g k + 1 ≤ p.len by omega_using [hcl])) (Nat.le_add_right _ _)
  have hcn64 : cOf p g k * p.n < 2 ^ 64 := by
    have : cOf p g k * p.n ≤ 67 * 32 := Nat.mul_le_mul (by omega_using [hcl, hl, hn32]) hn32
    omega_using [this]
  have g7 : t₇.gpr .x19 = S := by
    rw [u₇.other _ (by decide), o₆.get .x19, u₅.other _ (by decide), K₄.get .x19, hI.x19]
  have w7 : t₇.wr = t.wr := by rw [u₇.wr, o₆.wr, u₅.wr, K₄.wr]
  have r7 : t₇.rd = t.rd := by rw [u₇.rd, o₆.rd, u₅.rd, K₄.rd]
  have h8n : 8 * (p.n / 8) = p.n := by omega_using [hn8]
  have dS : Region.Disjoint ⟨at' S (Layout.laneA k + (p.n + 32)), p.n⟩ ⟨sig + BitVec.ofNat 64 (cOf p g k * p.n), p.n⟩ :=
    (hI.dsig.symm.sub_left (Offset.sub_base S (by rw [eA]; omega))).sub_right
      (Offset.sub_base sig hcn)
  refine copyWords_ok (t := .x19) (sr := .x12) (d₂ := Layout.laneA k + (p.n + 32)) (d₁ := 0) (w := p.n / 8)
    ⟨by decide, by decide, ⟨by decide, by omega⟩, ⟨by rw [eA]; omega, by rw [eA]; omega⟩,
      (by rw [e12, BitVec.add_zero, r7, w7, h8n]
          exact ⟨_, List.mem_append_left _ hI.insig, Offset.contains_base sig hcn hcn64⟩),
      (by rw [g7, w7, h8n]; exact in_scr hI.scr (by rw [eA]; omega)),
      (by rw [g7, e12, BitVec.add_zero, h8n]; exact dS)⟩ fun t₈ k₈ fr₈ b₈ => ?_
  rw [h8n, g7] at fr₈
  rw [e12, BitVec.add_zero, h8n, g7] at b₈
  refine wp_subr fun t₉ u₉ => wp_lsr (by decide) fun t₁₀ u₁₀ => wp_movz fun t₁₁ u₁₁ => wp_subr fun t₁₂ u₁₂ =>
    wp_eor fun t₁₃ u₁₃ => wp_and fun t₁₄ u₁₄ => wp_eor fun t₁₅ u₁₅ => ?_
  have m₁₅ : t₁₅.mem = t₈.mem := by rw [u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem]
  have m₇ : t₇.mem = t₄.mem := by rw [u₇.mem, o₆.mem, u₅.mem]
  have a2 : t₁.gpr .x19 + BitVec.ofNat 64 (Layout.laneA k + p.n + 16) = at' S (Layout.laneA k + p.n + 16) := by
    rw [g19]
  have a3 : t₂.gpr .x19 + BitVec.ofNat 64 (Layout.laneA k + p.n + 20) = at' S (Layout.laneA k + p.n + 20) := by
    rw [f₂.keep.get .x19, g19]
  have a4 : t₃.gpr .x19 + BitVec.ofNat 64 (Layout.laneA k + p.n + 24) = at' S (Layout.laneA k + p.n + 24) := by
    rw [f₃.keep.get .x19, f₂.keep.get .x19, g19]
  have F2 := f₂.frame; have F3 := f₃.frame; have F4 := f₄.frame
  have B2 := f₂.bytes; have B3 := f₃.bytes; have B4 := f₄.bytes
  rw [a2] at F2 B2; rw [a3] at F3 B3; rw [a4] at F4 B4
  have dj : ∀ {o l o' l' : Nat}, (o + l ≤ o' ∨ o' + l' ≤ o) → o + l ≤ 65536 → o' + l' ≤ 65536 →
      ∀ r ∈ [(⟨at' S o', l'⟩ : Region)], Region.Disjoint ⟨at' S o, l⟩ r := fun h h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint S h (by omega) (by omega)
  have keepAll : ∀ {o l : Nat}, o + l ≤ 65536 → (o + l ≤ Layout.laneA k + p.n + 20 ∨ Layout.laneA k + p.n + 24 ≤ o) →
      (o + l ≤ Layout.laneA k + p.n + 24 ∨ Layout.laneA k + p.n + 28 ≤ o) →
      (o + l ≤ Layout.laneA k + (p.n + 32) ∨ Layout.laneA k + (p.n + 32) + p.n ≤ o) →
      bytesAt t₁₅.mem (at' S o) l = bytesAt t₂.mem (at' S o) l := fun hb h₃ h₄ h₈ => by
    rw [m₁₅, TreeBase.bytesAt_frame fr₈ (dj h₈ hb (by rw [eA]; omega)) (by omega), m₇,
      TreeBase.bytesAt_frame F4 (dj h₄ hb (by rw [eA]; omega)) (by omega),
      TreeBase.bytesAt_frame F3 (dj h₃ hb (by rw [eA]; omega)) (by omega)]
  refine K t₁₅ ?_ ?_ ?_ ?_
  · exact (((((((((K₄.trans (upOnly u₅).keep).trans o₆.keep).trans (upOnly u₇).keep).trans k₈).trans
      ((upOnly u₉).keep.trans (upOnly u₁₀).keep)).trans ((upOnly u₁₁).keep.trans (upOnly u₁₂).keep)).trans
      (upOnly u₁₃).keep).trans (upOnly u₁₄).keep).trans (upOnly u₁₅).keep).mono (by simp)
  · rw [m₁₅]
    have S16 : Region.Sub ⟨at' S (Layout.laneA k + p.n + 16), 4⟩ ⟨at' S (Layout.laneA k + p.n + 16), 12⟩ :=
      Region.sub_prefix (by decide)
    have S20 : Region.Sub ⟨at' S (Layout.laneA k + p.n + 20), 4⟩ ⟨at' S (Layout.laneA k + p.n + 16), 12⟩ :=
      Offset.sub S (by omega) (by omega)
    have S24 : Region.Sub ⟨at' S (Layout.laneA k + p.n + 24), 4⟩ ⟨at' S (Layout.laneA k + p.n + 16), 12⟩ :=
      Offset.sub S (by omega) (by omega)
    have mW1 : (⟨at' S (Layout.laneA k + p.n + 16), 12⟩ : Region) ∈ laneW p S k := List.mem_cons_self
    have mW2 : (⟨at' S (Layout.laneA k + p.n + 32), p.n⟩ : Region) ∈ laneW p S k :=
      List.mem_cons_of_mem _ List.mem_cons_self
    have one : ∀ {r R : Region} {m m' : Mem}, Frame [r] m m' → Region.Sub r R → R ∈ laneW p S k →
        Frame (laneW p S k) m m' := fun hf hs hm => hf.sub fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'; exact ⟨_, hm, hs⟩
    rw [o₁.mem] at F2
    rw [m₇] at fr₈
    have e32 : Layout.laneA k + (p.n + 32) = Layout.laneA k + p.n + 32 := by omega
    rw [e32] at fr₈
    exact ((one F2 S16 mW1).trans (one F3 S20 mW1)).trans ((one F4 S24 mW1).trans (one fr₈ (fun _ h => h) mW2))
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [keepAll (by rw [eA]; omega) (by omega) (by omega) (by omega), B2]
    · rw [m₁₅, TreeBase.bytesAt_frame fr₈ (dj (by omega) (by rw [eA]; omega) (by rw [eA]; omega)) (by omega), m₇,
        TreeBase.bytesAt_frame F4 (dj (by omega) (by rw [eA]; omega) (by rw [eA]; omega)) (by omega), B3,
        f₂.keep.get .x20, o₁.get .x20]
    · rw [m₁₅, TreeBase.bytesAt_frame fr₈ (dj (by omega) (by rw [eA]; omega) (by rw [eA]; omega)) (by omega), m₇,
        B4, f₃.keep.get .x10, f₂.keep.get .x10, c₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hcl, hl, hn32])]
    · have ds : ∀ {o l : Nat}, o + l ≤ 65536 → ∀ r ∈ [(⟨at' S o, l⟩ : Region)],
          Region.Disjoint ⟨sig + BitVec.ofNat 64 (cOf p g k * p.n), p.n⟩ r := fun h r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hI.dsig.sub_left (Offset.sub_base sig hcn)).sub_right (Offset.sub_base S h)
      rw [m₁₅, show Layout.laneA k + p.n + 32 = Layout.laneA k + (p.n + 32) by omega, b₈, m₇,
        TreeBase.bytesAt_frame F4 (ds (by rw [eA]; omega)) (by omega),
        TreeBase.bytesAt_frame F3 (ds (by rw [eA]; omega)) (by omega)]
      rw [o₁.mem] at F2
      exact TreeBase.bytesAt_frame F2 (ds (by rw [eA]; omega)) (by omega)
  · have K8 : Keep [.x10, .x13, .x14, .x15, .x11, .x9, .x9, .x9, .x12, .x12, .x13, .x12, .x14] t t₈ :=
      (((K₄.trans (upOnly u₅).keep).trans o₆.keep).trans (upOnly u₇).keep).trans k₈
    have e24 : t₈.gpr .x24 = BitVec.ofNat 64 mn := by rw [K8.get .x24, h24]
    have e11 : t₈.gpr .x11 = BitVec.ofNat 64 (digitAt t.mem S (cOf p g k)) := by
      rw [k₈.get .x11, (upOnly u₇).get .x11, o₆.get .x11, (upOnly u₅).get .x11, f₄.keep.get .x11,
        f₃.keep.get .x11, f₂.keep.get .x11, d₁]
    have hd16 : digitAt t.mem S (cOf p g k) < 2 ^ 62 := by
      have := (t.mem (at' S (Layout.oDigits + cOf p g k))).isLt; simp only [digitAt]; omega_using [this]
    have v10 : t₁₀.gpr .x13 = (BitVec.ofNat 64 mn - BitVec.ofNat 64 (digitAt t.mem S (cOf p g k))) >>> 63 := by
      rw [u₁₀.gpr, u₉.gpr, e24, e11]
    have v12 : t₁₂.gpr .x15 = BitVec.ofNat 64 0 -
        (BitVec.ofNat 64 mn - BitVec.ofNat 64 (digitAt t.mem S (cOf p g k))) >>> 63 := by
      rw [u₁₂.gpr, u₁₁.gpr, u₁₁.other _ (by decide), v10]; rfl
    have x11₁₂ : t₁₂.gpr .x11 = BitVec.ofNat 64 (digitAt t.mem S (cOf p g k)) := by
      rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), e11]
    have x24₁₂ : t₁₂.gpr .x24 = BitVec.ofNat 64 mn := by
      rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), e24]
    have v14 : t₁₄.gpr .x13 = (BitVec.ofNat 64 (digitAt t.mem S (cOf p g k)) ^^^ BitVec.ofNat 64 mn) &&&
        (BitVec.ofNat 64 0 - (BitVec.ofNat 64 mn - BitVec.ofNat 64 (digitAt t.mem S (cOf p g k))) >>> 63) := by
      rw [u₁₄.gpr, u₁₃.gpr, u₁₃.other _ (by decide), x11₁₂, x24₁₂, v12]
    rw [u₁₅.gpr, v14, u₁₄.other _ (by decide), u₁₃.other _ (by decide), x11₁₂]
    exact min_eq (by omega_using [hmn]) hd16

/-- The least digit of the first `j` lanes of group `g` (from 15). -/
def mnOf (p : Params) (m : Mem) (S : Addr) (g : Nat) : Nat → Nat
  | 0 => 15
  | j + 1 => min (mnOf p m S g j) (digitAt m S (cOf p g j))

theorem mnOf_lt (p : Params) (m : Mem) (S : Addr) (g : Nat) : ∀ j, mnOf p m S g j < 16
  | 0 => by simp [mnOf]
  | j + 1 => by simp only [mnOf]; have := mnOf_lt p m S g j; omega_using [this]

/-- The ranges `chainLanes` writes. -/
def allW (p : Params) (S : Addr) : List Region := (List.range 4).flatMap (laneW p S)

theorem laneW_sub {S : Addr} {k : Nat} (hk : k < 4) : ∀ r ∈ laneW p S k, r ∈ allW p S := fun _ hr =>
  List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, hr⟩

theorem laneW_safe (hz : Sz p) {S : Addr} {k : Nat} (hk : k < 4) :
    ∀ r ∈ laneW p S k, ∃ o l, r = ⟨at' S o, l⟩ ∧ Safe p o l := by
  have hn32 := hz.n32
  intro r hr
  simp only [laneW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, _, rfl, .inr (.inr ⟨k, hk, .inl ⟨Nat.le_refl _, by simp only [Layout.strideA]; omega⟩⟩)⟩
  · exact ⟨_, _, rfl, .inr (.inr ⟨k, hk, .inl ⟨by omega, by simp only [Layout.strideA]; omega⟩⟩)⟩

theorem allW_safe (hz : Sz p) {S : Addr} : ∀ r ∈ allW p S, ∃ o l, r = ⟨at' S o, l⟩ ∧ Safe p o l := by
  intro r hr
  obtain ⟨k, hk, hr⟩ := List.mem_flatMap.mp hr
  exact laneW_safe hz (List.mem_range.mp hk) r hr

/-- What `chainLanes` has done after `j` lanes, from `t₀`. -/
structure CLI (p : Params) (t₀ : State) (S sig : Addr) (g j : Nat) (t : State) : Prop where
  keep : Keep [.x9, .x10, .x11, .x12, .x13, .x14, .x15, .x24] t₀ t
  frame : Frame (allW p S) t₀.mem t.mem
  lanes : ∀ k < j, LaneC p t.mem S k (t₀.gpr .x20).toNat (cOf p g k)
    (bytesAt t₀.mem (sig + BitVec.ofNat 64 (cOf p g k * p.n)) p.n)
  x24 : t.gpr .x24 = BitVec.ofNat 64 (mnOf p t₀.mem S g j)

/-- `chainLanes`: the four lanes of group `g`. -/
theorem chainLanes_ok (hz : Sz p) {g : Nat} (hg : 4 * g < p.len) {t₀ : State} {S sig : Addr}
    (hI : LaneIn p S sig t₀) (h22 : t₀.gpr .x22 = BitVec.ofNat 64 (4 * g)) {is : List Instr} {Q : State → Prop}
    (K : ∀ t', CLI p t₀ S sig g 4 t' → WP isa (.block is) t' Q) :
    WP isa (.block (Impl.SlhDsa.AArch64.Verify.chainLanes p ++ is)) t₀ Q := by
  have hn32 := hz.n32
  simp only [Impl.SlhDsa.AArch64.Verify.chainLanes, List.cons_append, List.nil_append]
  have dsg : ∀ {W : List Region}, (∀ r ∈ W, ∃ o l, r = ⟨at' S o, l⟩ ∧ Safe p o l) →
      ∀ r ∈ W, Region.Disjoint ⟨sig + BitVec.ofNat 64 0, p.xmssSigLen⟩ r := fun hW r hr => by
    obtain ⟨o, l, rfl, hs⟩ := hW r hr
    rw [BitVec.add_zero]
    exact hI.dsig.sub_right (Offset.sub_base S (Safe.lt hz hs))
  refine wp_movz fun t₁ u₁ => wp_rangeFlatMap (P := CLI p t₀ S sig g) 4
    ⟨(upOnly u₁).keep.mono (by simp), by rw [u₁.mem]; exact Frame.refl _ _, fun k hk => absurd hk (by omega),
      by rw [u₁.gpr]; rfl⟩ (fun j hj t is' ht k' => ?_) K
  have hI' : LaneIn p S sig t := ⟨by rw [ht.keep.get .x19, hI.x19], by rw [ht.keep.get .x21, hI.x21],
    by rw [ht.keep.get .x20]; exact hI.x20, by rw [ht.keep.wr]; exact hI.scr, by rw [ht.keep.rd]; exact hI.insig,
    hI.dsig, hI.slen⟩
  refine lane_ok hz hg hj hI' (by rw [ht.keep.get .x22, h22]) (mnOf_lt p t₀.mem S g j) ht.x24 fun t' k₁ f₁ l₁ x₁ => k' t' ?_
  have hcl : cOf p g j < p.len := by simp only [cOf]; have := hz.len; omega_using [this, hn32]
  have dig : digitAt t.mem S (cOf p g j) = digitAt t₀.mem S (cOf p g j) := by
    have e := TreeBase.bytesAt_frame (a := at' S (Layout.oDigits + cOf p g j)) (n := 1) ht.frame
      (safe_disj hz (allW_safe hz) (.inr (.inl ⟨by omega, by have := hz.len; simp only [Layout.oDigits]; omega⟩)))
      (by decide)
    have e' := congrArg (fun l => l.getD 0 0) e
    simp only [TreeBase.getD_bytesAt _ _ (show 0 < 1 by decide), BitVec.add_zero] at e'
    simp only [digitAt, e']
  have sgb : ∀ {o l : Nat}, o + l ≤ p.xmssSigLen →
      bytesAt t.mem (sig + BitVec.ofNat 64 o) l = bytesAt t₀.mem (sig + BitVec.ofNat 64 o) l := fun h =>
    TreeBase.bytesAt_frame ht.frame (fun r hr => (dsg (allW_safe hz) r hr).sub_left
      (by rw [BitVec.add_zero]; exact Offset.sub_base sig h)) (by have := hI.slen; omega)
  have hcn : cOf p g j * p.n + p.n ≤ p.xmssSigLen := by
    rw [xmssSigLen_eq', ← Nat.succ_mul]
    exact Nat.le_trans (Nat.mul_le_mul_right _ (show cOf p g j + 1 ≤ p.len by omega_using [hcl])) (Nat.le_add_right _ _)
  refine ⟨(ht.keep.trans k₁).mono (by simp), ht.frame.trans (f₁.mono (laneW_sub hj)), fun k hk => ?_, ?_⟩
  · rw [ht.keep.get .x20] at l₁
    by_cases e : k = j
    · subst e; rw [← sgb hcn]; exact l₁
    · have hk' : k < j := by omega
      have L := ht.lanes k hk'
      have eA : ∀ i, Layout.laneA i = 3136 + 128 * i := fun _ => rfl
      have dj : ∀ {o l : Nat}, Layout.laneA k ≤ o → o + l ≤ Layout.laneA k + 128 →
          ∀ r ∈ laneW p S j, Region.Disjoint ⟨at' S o, l⟩ r := fun h₁ h₂ r hr => by
        simp only [laneW, List.mem_cons, List.not_mem_nil, or_false] at hr
        rw [eA] at h₁ h₂
        rcases hr with rfl | rfl <;> exact Offset.disjoint S (by rw [eA]; omega) (by omega) (by rw [eA]; omega)
      exact ⟨by rw [TreeBase.bytesAt_frame f₁ (dj (by omega) (by omega)) (by omega)]; exact L.ty,
        by rw [TreeBase.bytesAt_frame f₁ (dj (by omega) (by omega)) (by omega)]; exact L.kp,
        by rw [TreeBase.bytesAt_frame f₁ (dj (by omega) (by omega)) (by omega)]; exact L.ch,
        by rw [TreeBase.bytesAt_frame f₁ (dj (by omega) (by omega)) (by omega)]; exact L.msg⟩
  · rw [x₁, dig]; rfl


end VG.Proof.SlhDsa.AArch64.XmssPk

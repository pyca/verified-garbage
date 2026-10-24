module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckDomainFn
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicCT
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckDomainFn
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicCT
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCheck
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCore

/-!
# `vg_ffdh_check_domain` on PPC64LE: constant time

As `CheckPublicCT.lean`, with the public data `CD` of the domain alone (its
y the domain's first `p_len` octets, which the code does not read as y):
the predicates fix what the code branches on, p's validity, whether there is
q, the masks of q's checks and of g's, and each piece between them is checked
by the taint analysis from the registers they fix.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Domain

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain
open VG.Proof.Bignum (slot bytesAt_length)
open VG.Proof.Bignum.PPC64LE (Two Pins two_post two_taint)

def cdDataOf (s : State) : CD :=
  ⟨s.gpr .r3, s.gpr .r3, s.gpr .r6, (s.gpr .r5).toNat, (s.gpr .r4).toNat, (s.gpr .r7).toNat * 8,
    Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat, Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r5).toNat⟩

/-! ## The predicates -/

def E0 (d : CD) (s : State) : Prop := cdContract.pre s ∧ cdDataOf s = d

/-- With `loadN`'s arguments. -/
def E1a (d : CD) (s : State) : Prop := Base d s ∧ s.gpr .r12 = off d.D 0 ∧ s.gpr .r6 = BitVec.ofNat 64 d.k

/-- After `loadN`. -/
def E2 (d : CD) (s : State) : Prop := E1a d s ∧ arr s.mem d.S d.w 0 = d.p

/-- After `check1`. -/
def E3 (d : CD) (s : State) : Prop :=
  Base d s ∧ arr s.mem d.S d.w 0 = d.p ∧ s.gpr .r6 = BitVec.ofNat 64 d.k ∧
    s.gpr .r15 = BitVec.ofNat 64 ((d.db.take d.k).getD 0 0).toNat ∧ s.gpr .r18 = 1 ∧
    (s.gpr .r0 = 0 ↔ ((d.db.take d.k).getD (d.k - 1) 0).toNat % 2 = 1)

/-- After `check2`. -/
def E4 (d : CD) (s : State) : Prop :=
  Base d s ∧ arr s.mem d.S d.w 0 = d.p ∧ (s.gpr .r0 = 0 ↔ Spec.Rsa.modulusValid d.p d.k = true)

theorem pins_E0 : Pins E0 [.r3, .r4, .r5, .r6] := by
  rintro d s₁ s₂ ⟨-, h₁⟩ ⟨-, h₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (congrArg CD.D h₁).trans (congrArg CD.D h₂).symm
  · exact BitVec.eq_of_toNat_eq ((congrArg CD.L h₁).trans (congrArg CD.L h₂).symm)
  · exact BitVec.eq_of_toNat_eq ((congrArg CD.k h₁).trans (congrArg CD.k h₂).symm)
  · exact (congrArg CD.S h₁).trans (congrArg CD.S h₂).symm

theorem pins_E1a {Φ : CD → State → Prop} (h : ∀ d s, Φ d s → E1a d s) :
    Pins Φ (baseRegs ++ ([.r12, .r6] : List Reg)) := by
  intro d s₁ s₂ h₁ h₂ r hr
  have h₁ := h _ _ h₁
  have h₂ := h _ _ h₂
  rcases List.mem_append.mp hr with hr | hr
  · exact h₁.1.pins h₂.1 r hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2, h₂.2.2]

theorem pins_E3 : Pins E3 (baseRegs ++ ([.r6, .r15, .r18] : List Reg)) := by
  intro d s₁ s₂ h₁ h₂ r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact h₁.1.pins h₂.1 r hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2.1, h₂.2.2.2.1]
    · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]

/-! ## The steps up to p's check, by correctness -/

theorem D01 {d : CD} {s : State} (h : E0 d s) : WP isa (.block (save .r6 ++ setup)) s (Base d) := by
  obtain ⟨⟨hrd, hwr, dDS, nwD, nwS, ⟨hk, hk'⟩, hL, hsl⟩, rfl⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  simp only [domR, scrR6] at hrd hwr dDS
  simp only [cdDataOf]
  generalize hDd : s.gpr .r3 = D at hrd dDS nwD ⊢
  generalize hLd : (s.gpr .r4).toNat = L at hrd dDS nwD hL ⊢
  generalize hkd : (s.gpr .r5).toNat = k at hk hk' hL hsl ⊢
  generalize hSd : s.gpr .r6 = S at hwr dDS nwS ⊢
  generalize hZd : (s.gpr .r7).toNat * 8 = Z at hwr dDS nwS ⊢
  have hkL : k ≤ L := by simp only [Spec.Ffdh.domainLenValid] at hL; omega
  have dKS : (⟨D, k⟩ : Region).Disjoint ⟨S, Z⟩ :=
    fun x h1 h2 => dDS x (by simp only [Region.Contains] at h1 ⊢; omega) h2
  have hZ256 : 256 ≤ Z := by omega
  have hZw : slot ((k + 7) / 8) 28 ≤ Z := by rw [slot_eq]; omega_using [hsl, hZd, hk', hk]
  have hs : Scr s S Z := Scr.of_mem (by rw [hwr]; simp) nwS
  have hin : ∀ i < 18, InRegions s.wr (off (savW S) (8 * i)) 8 := fun i hi => ⟨⟨S, Z⟩, by rw [hwr]; simp, by
    rw [off, Offset.add_add]; exact Offset.contains_base S (by omega) (by omega)⟩
  rw [WP.block_append_iff]
  refine WP.mono (save_ok (ws := .r6) (by decide) s (by rw [hSd]; exact hin)) fun s₁ hS => ?_
  have k1 := hS.keep
  have hfr₁ : Frame [savR S] s.mem s₁.mem := hSd ▸ hS.frame
  refine WP.mono (setup0_ok (D := D) (L := L) (k := k) ((k1.gpr .r3 (by decide)).trans hDd)
    (by rw [k1.gpr .r4 (by decide), ← hLd, VG.Proof.Bignum.ofNat_toNat64])
    (by rw [k1.gpr .r5 (by decide), ← hkd, VG.Proof.Bignum.ofNat_toNat64]) (hS.r23.trans hSd) hk')
    fun s₂ ⟨⟨a21, a27, a28, a11, a29, a10, a31, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine ⟨⟨hs.congr k12.wr, a10, a29, a11, a31, show 4 ≤ (k + 7) / 8 by omega, show (k + 7) / 8 ≤ 128 by omega,
    hZw⟩, a21, (k2.gpr .r23 (by decide)).trans (hS.r23.trans hSd), a27, a28, hk, hk',
    by simp only [Spec.Ffdh.domainLenValid] at hL; omega,
    fun i hi => by rw [k12.rd, k12.wr]; exact rd_of_mem (s := s) (D := D) (L := L) (by rw [hrd]; simp) (by omega) i hi,
    sep_of_disjoint (L := L) dDS (by omega),
    fun i hi => by rw [k12.rd, k12.wr]; exact rd_of_mem (s := s) (D := D) (L := L) (by rw [hrd]; simp) (by omega) i (Nat.lt_of_lt_of_le hi hkL),
    sep_of_disjoint (L := k) dKS (by omega), ?_, ?_⟩
  · rw [m2]; exact bytes_frame (L := L) hfr₁ dDS (by omega) hZ256
  · rw [m2]; exact bytes_frame (L := k) hfr₁ dKS (by omega) hZ256

theorem DA {d : CD} {s : State} (h : Base d s) : WP isa (.block [.addi .r12 .r21 0, .addi .r6 .r28 0]) s (E1a d) := by
  refine WP.mono (WP.keep [.r6, .r12] (Q := fun t => t.gpr .r12 = off d.D 0 ∧ t.gpr .r6 = BitVec.ofNat 64 d.k ∧
    t.mem = s.mem) (by prun [h.r21, h.r28, BitVec.add_zero]) (by decide)) fun t ⟨⟨a12, a6, m⟩, k⟩ =>
      ⟨h.same k m, a12, a6⟩

theorem DL {d : CD} {s : State} (h : E1a d s) : WP isa Precompute.loadN s (E2 d) := by
  obtain ⟨hb, h12, h6⟩ := h
  have hwd : d.w = (d.k + 7) / 8 := rfl
  have hZ := hb.env.hZ
  have hk := hb.k64
  have hk' := hb.k1024
  have hnw := hb.env.hs.nowrap
  have e28 := slot_eq d.w 28
  refine WP.mono (loadN_ok (dA := slot d.w 0) hb.env.hs hb.env.h10 h12 h6 hb.env.h11 (by omega) (by omega)
    (by omega) (by rw [slot_eq]; omega) (by rw [slot_eq] at hZ ⊢; omega)
    (fun i hi => hb.rdD i (by rcases hb.hL with h | h <;> omega))
    (fun i hi => hb.sepD i (by rcases hb.hL with h | h <;> omega))) fun t ⟨hv, out, k⟩ => ?_
  have hm : Body d.S d.w s.mem t.mem := Body.of out (Nat.le_refl _) (by rw [slot_eq] at hZ ⊢; omega)
  refine ⟨⟨hb.keep k hm, (k.gpr .r12 (by decide)).trans h12, (k.gpr .r6 (by decide)).trans h6⟩, ?_⟩
  rw [arr, hv, ← Proof.Ffdh.take_bytesAt _ _ (show d.k ≤ d.L by rcases hb.hL with h | h <;> omega), hb.bD]

theorem DC1 {d : CD} {s : State} (h : E2 d s) : WP isa (.block Precompute.check1) s (E3 d) := by
  obtain ⟨⟨hb, h12, h6⟩, hp⟩ := h
  have hl := hb.take_len
  have hk := hb.k64
  refine WP.mono (check1_ok (N := d.D) (nb := d.db.take d.k) h12 h6 hk hl
    (fun i hi => hb.rdD i (by have := hb.kL; omega)) fun i hi => hb.take_byte hi)
    fun t ⟨⟨i0, i15, i18, im⟩, k⟩ => ⟨hb.same k im, by rw [arr, im]; exact hp,
      (k.gpr .r6 (by decide)).trans h6, by rw [i15, getD_of_lt' (by omega)], i18,
      by rw [i0, getD_of_lt' (by omega)]⟩

theorem DC2 {d : CD} {s : State} (h : E3 d s) : WP isa Precompute.check2 s (E4 d) := by
  obtain ⟨hb, hp, h6, h15, h18, h0⟩ := h
  have hl := hb.take_len
  have hk := hb.k64
  refine WP.mono (check2_ok (nb := d.db.take d.k) h6 hk hb.k1024 hl (by rw [h0, getD_of_lt' (by omega)])
    (by rw [h15, getD_of_lt' (by omega)]) h18) fun t ⟨a, m, k⟩ =>
    ⟨hb.same k m, by rw [arr, m]; exact hp, a⟩

/-! ## After p's check -/

/-- q. -/
abbrev CD.q (d : CD) : Nat := Spec.Rsa.os2ip ((d.db.drop (2 * d.k)).take d.k)

/-- g. -/
abbrev CD.g (d : CD) : Nat := Spec.Rsa.os2ip ((d.db.drop d.k).take d.k)

theorem Base.qv {d : CD} {s : State} (h : Base d s) (hL : d.L = 3 * d.k) :
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off d.D (2 * d.k)) d.k) = d.q := by
  show _ = Spec.Rsa.os2ip ((d.db.drop (2 * d.k)).take d.k)
  rw [← h.bD, VG.Proof.Dsa.bytesAt_slice _ _ (by omega)]

theorem Base.gv {d : CD} {s : State} (h : Base d s) :
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off d.D d.k) d.k) = d.g := by
  show _ = Spec.Rsa.os2ip ((d.db.drop d.k).take d.k)
  rw [← h.bD, VG.Proof.Dsa.bytesAt_slice _ _ (by rcases h.hL with h | h <;> omega)]

theorem Base.pv {d : CD} {s : State} (h : Base d s) :
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem d.D d.k) = d.p := by
  show _ = Spec.Rsa.os2ip (d.db.take d.k)
  rw [← h.bD, Proof.Ffdh.take_bytesAt _ _ h.kL]

/-- What `qDiv` needs of q. -/
def QOk (d : CD) : Prop := (1 < d.q ∧ d.q < d.p - 1) ∧ d.q % 2 = 1

/-- What the branches after p's check have. -/
structure PV (d : CD) (s : State) : Prop where
  base : Base d s
  p0 : arr s.mem d.S d.w 0 = d.p
  valid : Spec.Rsa.modulusValid d.p d.k = true

/-- After `hasQ`. -/
def E5 (d : CD) (s : State) : Prop := PV d s ∧ (s.gpr .r0 = 0 ↔ d.L = 3 * d.k)

/-- After `qPtr`. -/
def E5a (d : CD) (s : State) : Prop := PV d s ∧ d.L = 3 * d.k ∧ s.gpr .r26 = off d.D (2 * d.k)

/-- After `range` on q. -/
def E5b (d : CD) (s : State) : Prop :=
  PV d s ∧ d.L = 3 * d.k ∧ s.gpr .r26 = mask (decide (1 < d.q ∧ d.q < d.p - 1))

/-- After `qOdd`. -/
def E6 (d : CD) (s : State) : Prop :=
  PV d s ∧ d.L = 3 * d.k ∧ s.gpr .r26 = mask (decide (1 < d.q ∧ d.q < d.p - 1) && decide (d.q % 2 = 1))

/-- After `qDiv`. -/
def E7 (d : CD) (s : State) : Prop :=
  PV d s ∧ d.L = 3 * d.k ∧ QOk d ∧ s.gpr .r25 = mask (decide (d.p % d.q = 1))

/-- After `checkG` with q. -/
def E8 (d : CD) (s : State) : Prop :=
  PV d s ∧ d.L = 3 * d.k ∧ QOk d ∧ s.gpr .r25 = mask (decide (d.p % d.q = 1)) ∧
    s.gpr .r26 = mask (decide (1 < d.g ∧ d.g < d.p - 1))

/-- After the `and` of the masks. -/
def E9 (d : CD) (s : State) : Prop :=
  PV d s ∧ d.L = 3 * d.k ∧ QOk d ∧ s.gpr .r26 = mask (decide (1 < d.g ∧ d.g < d.p - 1) && decide (d.p % d.q = 1))

/-- After `checkG` without q. -/
def E10 (d : CD) (s : State) : Prop := Base d s ∧ s.gpr .r26 = mask (decide (1 < d.g ∧ d.g < d.p - 1))

theorem PV.of {d : CD} {s t : State} {rs : List Reg} (h : PV d s) (k : Keep rs s t) (hm : t.mem = s.mem)
    (hr : ∀ r ∈ baseRegs, r ∉ rs := by decide) : PV d t :=
  ⟨h.base.same k hm hr, by rw [arr, hm]; exact h.p0, h.valid⟩

theorem DQ {d : CD} {s : State} (h : E4 d s ∧ s.gpr .r0 = 0) : WP isa (.block hasQ) s (E5 d) := by
  obtain ⟨⟨hb, hp, h0⟩, hz⟩ := h
  refine WP.mono (WP.keep [.r0] (Q := fun t => (t.gpr .r0 == 0) = decide (d.L = 3 * d.k) ∧ t.mem = s.mem) (by
      unfold hasQ
      prun [hb.r27, hb.r28]
      exact sub_3k_zero (by rcases hb.hL with h | h <;> have := hb.k1024 <;> omega) (by have := hb.k1024; omega))
    (by decide)) fun t ⟨⟨a0, m⟩, k⟩ => ⟨PV.of ⟨hb, hp, h0.mp hz⟩ k m, ?_⟩
  rw [← beq_iff_eq, a0, decide_eq_true_iff]

theorem DQP {d : CD} {s : State} (h : E5 d s ∧ s.gpr .r0 = 0) : WP isa (.block qPtr) s (E5a d) := by
  obtain ⟨⟨hv, h0⟩, hz⟩ := h
  refine WP.mono (WP.keep [.r26] (Q := fun t => t.gpr .r26 = off d.D (2 * d.k) ∧ t.mem = s.mem) (by
      unfold qPtr
      prun [hv.base.r21, hv.base.r28, shl1_ofNat]
      exact BitVec.add_comm _ _) (by decide)) fun t ⟨⟨a26, m⟩, k⟩ => ⟨hv.of k m, h0.mp hz, a26⟩

theorem DR {d : CD} {s : State} (h : E5a d s) : WP isa range s (E5b d) := by
  obtain ⟨hv, hL, h26⟩ := h
  have hb := hv.base
  have hwd : d.w = (d.k + 7) / 8 := rfl
  have hk := hb.k64
  have hf := modulus_facts hv.valid
  refine WP.mono (range_ok hb.env hb.r23 h26 hb.r28 (by omega) (by omega)
    (fun i hi => by rw [off_off']; exact hb.rdD _ (by omega))
    (fun i hi => by rw [off_off']; exact hb.sepD _ (by omega)) (by rw [hv.p0]; omega))
    fun t ⟨⟨_, p4, _, a26, bt, a10⟩, k⟩ => ⟨⟨hb.of (fun r hr => ?_) k.rd k.wr bt, by rw [p4, hv.p0], hv.valid⟩, hL, ?_⟩
  · simp only [baseRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [a10, hb.env.h10]
    all_goals exact k.gpr _ (by decide)
  · rw [a26, hv.p0, hb.qv hL]

theorem DO {d : CD} {s : State} (h : E5b d s) : WP isa (.block qOdd) s (E6 d) := by
  obtain ⟨hv, hL, h26⟩ := h
  have hb := hv.base
  have hk := hb.k64
  refine WP.mono (qOdd_ok hb.r21 hb.r28 h26 (by omega) hb.k1024 (hb.rdD _ (by omega)))
    fun t ⟨⟨a26, m⟩, k⟩ => ⟨hv.of k m, hL, by rw [a26, hb.qv hL]⟩

theorem DD {d : CD} {s : State} (h : E6 d s ∧ s.gpr .r26 ≠ 0) : WP isa qDiv s (E7 d) := by
  obtain ⟨⟨hv, hL, h26⟩, hnz⟩ := h
  have hb := hv.base
  have hwd : d.w = (d.k + 7) / 8 := rfl
  have hk := hb.k64
  have hq : QOk d := by
    rw [h26, Ne, mask_eq_zero, Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hnz
    exact hnz
  refine WP.mono (qDiv_ok hb.env hb.r23 hb.r21 hb.r28 (by omega) (by omega) (fun i hi => hb.rdD i (by omega))
    (fun i hi => hb.sepD i (by omega)) (by rw [hb.qv hL]; have := hq.1.1; omega))
    fun t ⟨⟨a25, p0, bt, a31⟩, k⟩ => ⟨⟨hb.of (fun r hr => ?_) k.rd k.wr bt, ?_, hv.valid⟩, hL, hq, ?_⟩
  · simp only [baseRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact k.gpr _ (by decide) | rw [a31, hb.env.h31]
  · rw [p0, hb.pv]
  · rw [a25, hb.qv hL, hb.pv]

/-- `checkG` from what `Base` and p in array 0 give: the mask of g's range in
`r26`, with `r25` kept. -/
theorem checkG_base {d : CD} {s : State} (hb : Base d s) (hp : arr s.mem d.S d.w 0 = d.p)
    (hp1 : 1 ≤ d.p) :
    WP isa checkG s fun t => (Base d t ∧ arr t.mem d.S d.w 0 = d.p ∧
      t.gpr .r26 = mask (decide (1 < d.g ∧ d.g < d.p - 1))) ∧ Keep rangeRegs s t := by
  have hwd : d.w = (d.k + 7) / 8 := rfl
  have hk := hb.k64
  have hkL := hb.kL
  refine WP.mono (checkG_ok hb.env hb.r23 hb.r21 hb.r28 (by omega) (by omega)
    (fun i hi => by rw [off_off']; exact hb.rdD _ (by rcases hb.hL with h | h <;> omega))
    (fun i hi => by rw [off_off']; exact hb.sepD _ (by rcases hb.hL with h | h <;> omega)) (by rw [hp]; omega))
    fun t ⟨⟨_, p0, a26, bt, a10⟩, k⟩ => ⟨⟨hb.of (fun r hr => ?_) k.rd k.wr bt, by rw [p0, hp], ?_⟩, k⟩
  · simp only [baseRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [a10, hb.env.h10]
    all_goals exact k.gpr _ (by decide)
  · rw [a26, hp, hb.gv]

theorem DG {d : CD} {s : State} (h : E7 d s) : WP isa checkG s (E8 d) := by
  obtain ⟨hv, hL, hq, h25⟩ := h
  have hf := modulus_facts hv.valid
  refine WP.mono (checkG_base hv.base hv.p0 (by omega)) fun t ⟨⟨hb, p0, a26⟩, k⟩ =>
    ⟨⟨hb, p0, hv.valid⟩, hL, hq, (k.gpr .r25 (by decide)).trans h25, a26⟩

theorem DN {d : CD} {s : State} (h : E8 d s) : WP isa (.block [.logic .and .r26 .r26 .r25]) s (E9 d) := by
  obtain ⟨hv, hL, hq, h25, h26⟩ := h
  refine WP.mono (WP.keep [.r26] (Q := fun t => t.gpr .r26 = mask (decide (1 < d.g ∧ d.g < d.p - 1) &&
    decide (d.p % d.q = 1)) ∧ t.mem = s.mem) (by prun [h25, h26, mask_and']) (by decide))
    fun t ⟨⟨a26, m⟩, k⟩ => ⟨hv.of k m, hL, hq, a26⟩

theorem DS {d : CD} {s : State} (h : E9 d s ∧ s.gpr .r26 ≠ 0) : WP isa subgroup s (CF d) := by
  obtain ⟨⟨hv, hL, _, _⟩, _⟩ := h
  have hb := hv.base
  have hf := modulus_facts hv.valid
  have hk := hb.k64
  refine WP.mono (subgroup_ok hb.env hb.r23 hb.r21 hb.r28 (by omega) hb.k1024 (by rw [hv.p0]; omega)
    (by rw [hv.p0]; exact hf.2)
    (fun i hi => by rw [off_off']; exact hb.rdD _ (by omega))
    (fun i hi => by rw [off_off']; exact hb.sepD _ (by omega))) fun t ⟨_, k⟩ => ?_
  show t.gpr .r23 = d.S
  rw [k.gpr .r23 (by decide), hb.r23]

theorem DG0 {d : CD} {s : State} (h : E5 d s ∧ s.gpr .r0 ≠ 0) : WP isa checkG s (E10 d) := by
  obtain ⟨⟨hv, _⟩, _⟩ := h
  have hf := modulus_facts hv.valid
  exact WP.mono (checkG_base hv.base hv.p0 (by omega)) fun t ⟨⟨hb, _, a26⟩, _⟩ => ⟨hb, a26⟩

/-! ## Constant time -/

theorem fix_mask {α : Type} {Φ : α → State → Prop} {f : α → Bool} (h : ∀ a s, Φ a s → s.gpr .r26 = mask (f a)) :
    ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → (s₁.gpr .r26 = 0 ↔ s₂.gpr .r26 = 0) := fun a s₁ s₂ h₁ h₂ => by
  rw [h a s₁ h₁, h a s₂ h₂]

theorem withQ_rel : RelCT isa (Two fun d s => E5 d s ∧ s.gpr .r0 = 0) withQ (Two CF) := by
  unfold withQ
  refine RelCT.seq (two_post (two_taint _ (pins_base (Φ := fun d s => E5 d s ∧ s.gpr .r0 = 0)
    fun _ _ h => h.1.1.base) (by taint_decide)) fun _ _ h => DQP h) ?_
  refine RelCT.seq (two_post (two_taint (baseRegs ++ ([.r26] : List Reg)) (Φ := E5a) (fun d s₁ s₂ h₁ h₂ r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact h₁.1.base.pins h₂.1.base r hr
      · rw [List.mem_singleton] at hr; subst hr; rw [h₁.2.2, h₂.2.2]) (by taint_decide))
    fun _ _ h => DR h) ?_
  refine RelCT.seq (two_post (two_taint _ (pins_base (Φ := E5b) fun _ _ h => h.1.base) (by taint_decide))
    fun _ _ h => DO h) ?_
  refine two_ite (Φ := E6) (fix_mask fun _ _ h => h.2.2)
    (two_post (two_taint _ (pins_base (Φ := fun d s => E6 d s ∧ s.gpr .r26 = 0) fun _ _ h => h.1.1.base)
      (by taint_decide)) fun _ _ h => TK0 (Φ := fun d s => E6 d s ∧ s.gpr .r26 = 0) (fun _ _ h => h.1.1.base) h) ?_
  refine RelCT.seq (two_post (two_taint _ (pins_base (Φ := fun d s => E6 d s ∧ s.gpr .r26 ≠ 0)
    fun _ _ h => h.1.1.base) (by taint_decide)) fun _ _ h => DD h) ?_
  refine RelCT.seq (two_post (two_taint _ (pins_base (Φ := E7) fun _ _ h => h.1.base) (by taint_decide))
    fun _ _ h => DG h) ?_
  refine RelCT.seq (two_post (two_taint _ (pins_base (Φ := E8) fun _ _ h => h.1.base) (by taint_decide))
    fun _ _ h => DN h) ?_
  exact two_ite (Φ := E9) (fix_mask fun _ _ h => h.2.2.2)
    (two_post (two_taint _ (pins_base (Φ := fun d s => E9 d s ∧ s.gpr .r26 = 0) fun _ _ h => h.1.1.base)
      (by taint_decide)) fun _ _ h => TK0 (Φ := fun d s => E9 d s ∧ s.gpr .r26 = 0) (fun _ _ h => h.1.1.base) h)
    (two_post (two_taint _ (pins_base (Φ := fun d s => E9 d s ∧ s.gpr .r26 ≠ 0) fun _ _ h => h.1.1.base)
      (by taint_decide)) fun _ _ h => DS h)

theorem withoutQ_rel : RelCT isa (Two fun d s => E5 d s ∧ s.gpr .r0 ≠ 0) withoutQ (Two CF) := by
  unfold withoutQ
  refine RelCT.seq (two_post (two_taint _ (pins_base (Φ := fun d s => E5 d s ∧ s.gpr .r0 ≠ 0)
    fun _ _ h => h.1.1.base) (by taint_decide)) fun _ _ h => DG0 h) ?_
  exact two_ite (Φ := E10) (fix_mask fun _ _ h => h.2)
    (two_post (two_taint _ (pins_base (Φ := fun d s => E10 d s ∧ s.gpr .r26 = 0) fun _ _ h => h.1.1)
      (by taint_decide)) fun _ _ h => TK0 (Φ := fun d s => E10 d s ∧ s.gpr .r26 = 0) (fun _ _ h => h.1.1) h)
    (two_post (two_taint _ (pins_base (Φ := fun d s => E10 d s ∧ s.gpr .r26 ≠ 0) fun _ _ h => h.1.1)
      (by taint_decide)) fun _ _ h => TK1 (Φ := fun d s => E10 d s ∧ s.gpr .r26 ≠ 0) (fun _ _ h => h.1.1) h)

theorem cd_rel : RelCT isa (Two E0) checkDomain fun _ _ => True := by
  unfold checkDomain
  refine RelCT.seq (two_post (two_taint _ pins_E0 (by taint_decide)) fun _ _ h => D01 h)
    (RelCT.seq (R := Two E4) ?_ (RelCT.seq (R := Two CF) ?_ (two_taint _ pins_CF (by taint_decide))))
  · unfold loadP Precompute.check
    exact RelCT.seq (two_post (two_taint _ (pins_base (Φ := Base) fun _ _ h => h) (by taint_decide))
      fun _ _ h => DA h)
      (RelCT.seq (two_post (two_taint _ (pins_E1a fun _ _ h => h) (by taint_decide)) fun _ _ h => DL h)
        (RelCT.seq (two_post (two_taint (Φ := E2) _ (pins_E1a fun _ _ h => h.1) (by taint_decide))
          fun _ _ h => DC1 h)
          (two_post (two_taint _ pins_E3 (by taint_decide)) fun _ _ h => DC2 h)))
  · refine two_ite (fun d s₁ s₂ h₁ h₂ => h₁.2.2.trans h₂.2.2.symm) ?_
      (two_post (two_taint _ (pins_base (Φ := fun d s => E4 d s ∧ s.gpr .r0 ≠ 0) fun _ _ h => h.1.1)
        (by taint_decide)) fun _ _ h => TK0 (Φ := fun d s => E4 d s ∧ s.gpr .r0 ≠ 0) (fun _ _ h => h.1.1) h)
    unfold domainBody
    exact RelCT.seq (two_post (two_taint _ (pins_base (Φ := fun d s => E4 d s ∧ s.gpr .r0 = 0) fun _ _ h => h.1.1)
      (by taint_decide)) fun _ _ h => DQ h)
      (two_ite (Φ := E5) (fun d s₁ s₂ h₁ h₂ => h₁.2.trans h₂.2.symm) withQ_rel withoutQ_rel)

theorem cd_ct : ConstantTime isa cdContract.pre cdContract.pub checkDomain :=
  RelCT.constantTime (cd_rel.mono (fun s t ⟨hs, ht, hsp, h3, h4, h5, h6, h7, hb⟩ => ⟨cdDataOf s, ⟨hs, rfl⟩,
    ⟨ht, by
      have hb' := (List.map_inj_right (fun _ _ h => BitVec.eq_of_toNat_eq h)).mp hb
      have hk : Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r5).toNat =
          Spec.Rsa.bytesAt t.mem (t.gpr .r3) (t.gpr .r5).toNat := by
        rw [← h3, ← h5, ← Proof.Ffdh.take_bytesAt _ _ (show (s.gpr .r5).toNat ≤ (s.gpr .r4).toNat by
          have := hs.2.2.2.2.2.2.1; simp only [Spec.Ffdh.domainLenValid] at this; omega),
          ← Proof.Ffdh.take_bytesAt t.mem _ (show (s.gpr .r5).toNat ≤ (s.gpr .r4).toNat by
          have := hs.2.2.2.2.2.2.1; simp only [Spec.Ffdh.domainLenValid] at this; omega), hb', h3, h4]
      simp only [cdDataOf]
      rw [hb', hk]
      simp only [h3, h4, h5, h6, h7]⟩, hsp⟩) fun _ _ h => h)

end VG.Proof.Ffdh.PPC64LE.Domain

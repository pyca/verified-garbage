module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicFn
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicFn
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCheck
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.Domain

/-!
# `vg_ffdh_check_public` on PPC64LE: constant time

As `Proof/Bignum/PPC64LE/PreCT.lean`: the taint analysis treats memory as
secret, so the bytes of p and y, and what is computed from them, are secret
to it, though they are public. Two runs are related by `Two` at each step,
both satisfying the same predicate for the same public data `CD` (the
pointers, the lengths and the bytes of the domain and y), which fixes what
the code branches on: p's first byte (in `check2`), whether p is valid,
whether `1 < y < p − 1`, and whether there is q. Each piece between them is
checked by the taint analysis from the registers the predicate fixes.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Domain

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain
open VG.Proof.Bignum (slot bytesAt_length)
open VG.Proof.Bignum.PPC64LE (Two Pins two_post two_taint)

/-- The public data of a run: the domain, y and the working space, `p_len`,
`domain_len`, the working space's size in bytes, and the bytes of the domain
and y. -/
structure CD where
  D : Addr
  Y : Addr
  S : Addr
  k : Nat
  L : Nat
  Z : Nat
  db : List Byte
  yb : List Byte

abbrev CD.w (d : CD) : Nat := (d.k + 7) / 8

/-- p. -/
abbrev CD.p (d : CD) : Nat := Spec.Rsa.os2ip (d.db.take d.k)

/-- y. -/
abbrev CD.y (d : CD) : Nat := Spec.Rsa.os2ip d.yb

def cdOf (s : State) : CD :=
  ⟨s.gpr .r3, s.gpr .r6, s.gpr .r8, (s.gpr .r5).toNat, (s.gpr .r4).toNat, (s.gpr .r9).toNat * 8,
    Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat, Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat⟩

/-- What holds from `setup` on. -/
structure Base (d : CD) (s : State) : Prop where
  env : Env s d.S d.Z d.w
  r21 : s.gpr .r21 = d.D
  r23 : s.gpr .r23 = d.S
  r27 : s.gpr .r27 = BitVec.ofNat 64 d.L
  r28 : s.gpr .r28 = BitVec.ofNat 64 d.k
  k64 : 64 ≤ d.k
  k1024 : d.k ≤ 1024
  hL : d.L = 2 * d.k ∨ d.L = 3 * d.k
  rdD : ∀ i < d.L, InRegions (s.rd ++ s.wr) (off d.D i) 1
  sepD : ∀ i < d.L, ∀ x, ofs d.S x < d.Z → off d.D i ≠ x
  rdY : ∀ i < d.k, InRegions (s.rd ++ s.wr) (off d.Y i) 1
  sepY : ∀ i < d.k, ∀ x, ofs d.S x < d.Z → off d.Y i ≠ x
  bD : Spec.Rsa.bytesAt s.mem d.D d.L = d.db
  bY : Spec.Rsa.bytesAt s.mem d.Y d.k = d.yb

/-- The registers `Base` fixes. -/
def baseRegs : List Reg := [.r10, .r11, .r21, .r23, .r27, .r28, .r29, .r31]

theorem Base.of {d : CD} {s t : State} (h : Base d s) (hg : ∀ r ∈ baseRegs, t.gpr r = s.gpr r)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hm : Body d.S d.w s.mem t.mem) : Base d t where
  env := ⟨h.env.hs.congr hwr, (hg .r10 (by decide)).trans h.env.h10, (hg .r29 (by decide)).trans h.env.h29,
    (hg .r11 (by decide)).trans h.env.h11, (hg .r31 (by decide)).trans h.env.h31, h.env.hw, h.env.hw', h.env.hZ⟩
  r21 := (hg _ (by decide)).trans h.r21
  r23 := (hg _ (by decide)).trans h.r23
  r27 := (hg _ (by decide)).trans h.r27
  r28 := (hg _ (by decide)).trans h.r28
  k64 := h.k64
  k1024 := h.k1024
  hL := h.hL
  rdD := by rw [hrd, hwr]; exact h.rdD
  sepD := h.sepD
  rdY := by rw [hrd, hwr]; exact h.rdY
  sepY := h.sepY
  bD := by rw [hm.bytesAt h.env.hZ h.sepD]; exact h.bD
  bY := by rw [hm.bytesAt h.env.hZ h.sepY]; exact h.bY

theorem Base.keep {d : CD} {s t : State} {rs : List Reg} (h : Base d s) (k : Keep rs s t)
    (hm : Body d.S d.w s.mem t.mem) (hr : ∀ r ∈ baseRegs, r ∉ rs := by decide) : Base d t :=
  h.of (fun r hr' => k.gpr r (hr r hr')) k.rd k.wr hm

theorem Base.same {d : CD} {s t : State} {rs : List Reg} (h : Base d s) (k : Keep rs s t)
    (hm : t.mem = s.mem) (hr : ∀ r ∈ baseRegs, r ∉ rs := by decide) : Base d t :=
  h.keep k (by rw [hm]; exact Outside.refl _ _ _ _) hr

theorem Base.pins {d : CD} {s₁ s₂ : State} (h₁ : Base d s₁) (h₂ : Base d s₂) :
    ∀ r ∈ baseRegs, s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [baseRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.env.h10, h₂.env.h10]
  · rw [h₁.env.h11, h₂.env.h11]
  · rw [h₁.r21, h₂.r21]
  · rw [h₁.r23, h₂.r23]
  · rw [h₁.r27, h₂.r27]
  · rw [h₁.r28, h₂.r28]
  · rw [h₁.env.h29, h₂.env.h29]
  · rw [h₁.env.h31, h₂.env.h31]

/-- A branch on a register that each predicate fixes. -/
theorem two_ite {α : Type} {Φ : α → State → Prop} {r : Reg} {t e : Prog isa} {Q : State → State → Prop}
    (hfix : ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → (s₁.gpr r = 0 ↔ s₂.gpr r = 0))
    (ht : RelCT isa (Two fun a s => Φ a s ∧ s.gpr r = 0) t Q)
    (he : RelCT isa (Two fun a s => Φ a s ∧ s.gpr r ≠ 0) e Q) :
    RelCT isa (Two Φ) (.ite (.zero .d r) t e) Q := by
  refine RelCT.ite (fun s₁ s₂ ⟨a, h₁, h₂, _⟩ => ?_) (RelCT.mono ht (fun s₁ s₂ ⟨⟨a, h₁, h₂, hsp⟩, hc⟩ => ?_)
    fun _ _ h => h) (RelCT.mono he (fun s₁ s₂ ⟨⟨a, h₁, h₂, hsp⟩, hc⟩ => ?_) fun _ _ h => h)
  · rw [eval_zero, eval_zero]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
    exact hfix a s₁ s₂ h₁ h₂
  · rw [eval_zero] at hc
    have h0 : s₁.gpr r = 0 := by simpa using hc
    exact ⟨a, ⟨h₁, h0⟩, ⟨h₂, (hfix a s₁ s₂ h₁ h₂).mp h0⟩, hsp⟩
  · rw [eval_zero] at hc
    have h0 : s₁.gpr r ≠ 0 := by simpa using hc
    exact ⟨a, ⟨h₁, h0⟩, ⟨h₂, fun e => h0 ((hfix a s₁ s₂ h₁ h₂).mpr e)⟩, hsp⟩

theorem byte_of_bytesAt {m : Mem} {P : Addr} {n i : Nat} {l : List Byte} (h : Spec.Rsa.bytesAt m P n = l)
    (hi : i < n) : m (off P i) = l[i]'(by rw [← h, bytesAt_length]; exact hi) := by
  subst h
  simp [Spec.Rsa.bytesAt, off]

theorem mask_eq_zero (b : Bool) : mask b = 0 ↔ b = false := by cases b <;> decide

/-! ## The predicates -/

def C0 (d : CD) (s : State) : Prop := cpContract.pre s ∧ cdOf s = d

/-- After `setup`. -/
def C1 (d : CD) (s : State) : Prop := Base d s ∧ s.gpr .r26 = d.Y

/-- With `loadN`'s arguments. -/
def C1a (d : CD) (s : State) : Prop := C1 d s ∧ s.gpr .r12 = off d.D 0 ∧ s.gpr .r6 = BitVec.ofNat 64 d.k

/-- After `loadN`. -/
def C2 (d : CD) (s : State) : Prop := C1a d s ∧ arr s.mem d.S d.w 0 = d.p

/-- After `check1`. -/
def C3 (d : CD) (s : State) : Prop :=
  C1 d s ∧ arr s.mem d.S d.w 0 = d.p ∧ s.gpr .r6 = BitVec.ofNat 64 d.k ∧
    s.gpr .r15 = BitVec.ofNat 64 ((d.db.take d.k).getD 0 0).toNat ∧ s.gpr .r18 = 1 ∧
    (s.gpr .r0 = 0 ↔ ((d.db.take d.k).getD (d.k - 1) 0).toNat % 2 = 1)

/-- After `check2`. -/
def C4 (d : CD) (s : State) : Prop :=
  C1 d s ∧ arr s.mem d.S d.w 0 = d.p ∧ (s.gpr .r0 = 0 ↔ Spec.Rsa.modulusValid d.p d.k = true)

/-- After `range`. -/
def C5 (d : CD) (s : State) : Prop :=
  Base d s ∧ arr s.mem d.S d.w 0 = d.p ∧ Spec.Rsa.modulusValid d.p d.k = true ∧
    (s.gpr .r26 = 0 ↔ ¬ (1 < d.y ∧ d.y < d.p - 1))

/-- After `hasQ`. -/
def C6 (d : CD) (s : State) : Prop :=
  Base d s ∧ arr s.mem d.S d.w 0 = d.p ∧ Spec.Rsa.modulusValid d.p d.k = true ∧ (s.gpr .r0 = 0 ↔ d.L = 3 * d.k)

/-- Before `restore`. -/
def CF (d : CD) (s : State) : Prop := s.gpr .r23 = d.S

theorem pins_C0 : Pins C0 [.r3, .r4, .r5, .r6, .r8] := by
  rintro d s₁ s₂ ⟨-, h₁⟩ ⟨-, h₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (congrArg CD.D h₁).trans (congrArg CD.D h₂).symm
  · exact BitVec.eq_of_toNat_eq ((congrArg CD.L h₁).trans (congrArg CD.L h₂).symm)
  · exact BitVec.eq_of_toNat_eq ((congrArg CD.k h₁).trans (congrArg CD.k h₂).symm)
  · exact (congrArg CD.Y h₁).trans (congrArg CD.Y h₂).symm
  · exact (congrArg CD.S h₁).trans (congrArg CD.S h₂).symm

theorem pins_base {Φ : CD → State → Prop} (h : ∀ d s, Φ d s → Base d s) : Pins Φ baseRegs :=
  fun _ _ _ h₁ h₂ => (h _ _ h₁).pins (h _ _ h₂)

theorem pins_C1 {Φ : CD → State → Prop} (h : ∀ d s, Φ d s → C1 d s) : Pins Φ (baseRegs ++ [.r26]) := by
  intro d s₁ s₂ h₁ h₂ r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact (h _ _ h₁).1.pins (h _ _ h₂).1 r hr
  · rw [List.mem_singleton] at hr; subst hr; rw [(h _ _ h₁).2, (h _ _ h₂).2]

theorem pins_C1a : Pins C1a (baseRegs ++ [.r26, .r12, .r6]) := by
  intro d s₁ s₂ h₁ h₂ r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact h₁.1.1.pins h₂.1.1 r hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.1.2, h₂.1.2]
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2, h₂.2.2]

theorem pins_C3 : Pins C3 (baseRegs ++ [.r26, .r6, .r15, .r18]) := by
  intro d s₁ s₂ h₁ h₂ r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact h₁.1.1.pins h₂.1.1 r hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [h₁.1.2, h₂.1.2]
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2.1, h₂.2.2.2.1]
    · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]

theorem pins_CF : Pins CF [.r23] := by
  rintro d s₁ s₂ h₁ h₂ r hr
  rw [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]

/-! ## The steps, by correctness -/

theorem T01 {d : CD} {s : State} (h : C0 d s) :
    WP isa (.block (save .r8 ++ setup ++ [.addi .r26 .r6 0])) s (C1 d) := by
  obtain ⟨⟨hrd, hwr, dDS, dYS, nwD, nwY, nwS, ⟨hk, hk'⟩, hL, hyl, hsl⟩, rfl⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  simp only [domR, yR, scrR] at hrd hwr dDS dYS
  simp only [cdOf]
  rw [hyl]
  rw [hyl] at hrd dYS nwY
  generalize hDd : s.gpr .r3 = D at hrd dDS nwD ⊢
  generalize hLd : (s.gpr .r4).toNat = L at hrd dDS nwD hL ⊢
  generalize hkd : (s.gpr .r5).toNat = k at hk hk' hL hyl hsl hrd dYS nwY ⊢
  generalize hYd : s.gpr .r6 = Y at hrd dYS nwY ⊢
  generalize hSd : s.gpr .r8 = S at hwr dDS dYS nwS ⊢
  generalize hZd : (s.gpr .r9).toNat * 8 = Z at hwr dDS dYS nwS ⊢
  have hZ256 : 256 ≤ Z := by omega
  have hZw : slot ((k + 7) / 8) 28 ≤ Z := by rw [slot_eq]; omega_using [hsl, hZd, hk', hk]
  have hs : Scr s S Z := Scr.of_mem (by rw [hwr]; simp) nwS
  have hin : ∀ i < 18, InRegions s.wr (off (savW S) (8 * i)) 8 := fun i hi => ⟨⟨S, Z⟩, by rw [hwr]; simp, by
    rw [off, Offset.add_add]; exact Offset.contains_base S (by omega) (by omega)⟩
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (save_ok (ws := .r8) (by decide) s (by rw [hSd]; exact hin)) fun s₁ hS => ?_
  have k1 := hS.keep
  have hfr₁ : Frame [savR S] s.mem s₁.mem := hSd ▸ hS.frame
  refine WP.mono (setup_ok (D := D) (Y := Y) (L := L) (k := k) ((k1.gpr .r3 (by decide)).trans hDd)
    (by rw [k1.gpr .r4 (by decide), ← hLd, VG.Proof.Bignum.ofNat_toNat64])
    (by rw [k1.gpr .r5 (by decide), ← hkd, VG.Proof.Bignum.ofNat_toNat64])
    ((k1.gpr .r6 (by decide)).trans hYd) (hS.r23.trans hSd) hk')
    fun s₂ ⟨⟨a21, a27, a28, a11, a29, a10, a31, a26, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine ⟨⟨⟨hs.congr k12.wr, a10, a29, a11, a31, show 4 ≤ (k + 7) / 8 by omega, show (k + 7) / 8 ≤ 128 by omega,
    hZw⟩, a21,
    (k2.gpr .r23 (by decide)).trans (hS.r23.trans hSd), a27, a28, hk, hk',
    by simp only [Spec.Ffdh.domainLenValid] at hL; omega,
    fun i hi => by rw [k12.rd, k12.wr]; exact rd_of_mem (s := s) (D := D) (L := L) (by rw [hrd]; simp) (by omega) i hi,
    sep_of_disjoint (L := L) dDS (by omega),
    fun i hi => by rw [k12.rd, k12.wr]; exact rd_of_mem (s := s) (D := Y) (L := k) (by rw [hrd]; simp) (by omega) i hi,
    sep_of_disjoint (L := k) dYS (by omega), ?_, ?_⟩, a26⟩
  · rw [m2]; exact bytes_frame (L := L) hfr₁ dDS (by omega) hZ256
  · rw [m2]; exact bytes_frame (L := k) hfr₁ dYS (by omega) hZ256

theorem TA {d : CD} {s : State} (h : C1 d s) : WP isa (.block [.addi .r12 .r21 0, .addi .r6 .r28 0]) s (C1a d) := by
  refine WP.mono (WP.keep [.r6, .r12] (Q := fun t => t.gpr .r12 = off d.D 0 ∧ t.gpr .r6 = BitVec.ofNat 64 d.k ∧
    t.mem = s.mem) (by prun [h.1.r21, h.1.r28, BitVec.add_zero]) (by decide)) fun t ⟨⟨a12, a6, m⟩, k⟩ =>
      ⟨⟨h.1.same k m, (k.gpr .r26 (by decide)).trans h.2⟩, a12, a6⟩

theorem TL {d : CD} {s : State} (h : C1a d s) : WP isa Precompute.loadN s (C2 d) := by
  obtain ⟨⟨hb, h26⟩, h12, h6⟩ := h
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
  refine ⟨⟨⟨hb.keep k hm, (k.gpr .r26 (by decide)).trans h26⟩, (k.gpr .r12 (by decide)).trans h12,
    (k.gpr .r6 (by decide)).trans h6⟩, ?_⟩
  rw [arr, hv, ← Proof.Ffdh.take_bytesAt _ _ (show d.k ≤ d.L by rcases hb.hL with h | h <;> omega), hb.bD]

theorem getD_of_lt' {l : List Byte} {i : Nat} (h : i < l.length) : l.getD i 0 = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem Base.kL {d : CD} {s : State} (h : Base d s) : d.k ≤ d.L := by rcases h.hL with h | h <;> omega

theorem Base.take_len {d : CD} {s : State} (h : Base d s) : (d.db.take d.k).length = d.k := by
  have := h.kL
  rw [List.length_take, ← h.bD, bytesAt_length]; omega

theorem Base.take_byte {d : CD} {s : State} (h : Base d s) {i : Nat} (hi : i < d.k) :
    s.mem (off d.D i) = (d.db.take d.k)[i]'(by rw [h.take_len]; exact hi) := by
  have := h.kL
  rw [List.getElem_take]
  exact byte_of_bytesAt h.bD (by omega)

theorem TC1 {d : CD} {s : State} (h : C2 d s) : WP isa (.block Precompute.check1) s (C3 d) := by
  obtain ⟨⟨⟨hb, h26⟩, h12, h6⟩, hp⟩ := h
  have hl := hb.take_len
  have hk := hb.k64
  refine WP.mono (check1_ok (N := d.D) (nb := d.db.take d.k) h12 h6 hk hl
    (fun i hi => hb.rdD i (by have := hb.kL; omega)) fun i hi => hb.take_byte hi)
    fun t ⟨⟨i0, i15, i18, im⟩, k⟩ => ⟨⟨hb.same k im, (k.gpr .r26 (by decide)).trans h26⟩, by rw [arr, im]; exact hp,
      (k.gpr .r6 (by decide)).trans h6, by rw [i15, getD_of_lt' (by omega)], i18,
      by rw [i0, getD_of_lt' (by omega)]⟩

theorem TC2 {d : CD} {s : State} (h : C3 d s) : WP isa Precompute.check2 s (C4 d) := by
  obtain ⟨⟨hb, h26⟩, hp, h6, h15, h18, h0⟩ := h
  have hl := hb.take_len
  have hk := hb.k64
  refine WP.mono (check2_ok (nb := d.db.take d.k) h6 hk hb.k1024 hl (by rw [h0, getD_of_lt' (by omega)])
    (by rw [h15, getD_of_lt' (by omega)]) h18) fun t ⟨a, m, k⟩ =>
    ⟨⟨hb.same k m, (k.gpr .r26 (by decide)).trans h26⟩, by rw [arr, m]; exact hp, a⟩

theorem modulus_facts {p k : Nat} (h : Spec.Rsa.modulusValid p k = true) : 2 ≤ p ∧ p % 2 = 1 := by
  simp only [Spec.Rsa.modulusValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  omega

theorem TR {d : CD} {s : State} (h : C4 d s ∧ s.gpr .r0 = 0) : WP isa range s (C5 d) := by
  obtain ⟨⟨⟨hb, h26⟩, hp, h0⟩, hz⟩ := h
  have hv := h0.mp hz
  have hf := modulus_facts hv
  have hwd : d.w = (d.k + 7) / 8 := rfl
  have hk := hb.k64
  refine WP.mono (range_ok hb.env hb.r23 h26 hb.r28 (by omega) (by omega) hb.rdY hb.sepY (by rw [hp]; omega))
    fun t ⟨⟨_, p4, _, a26, bt, a10⟩, k⟩ => ⟨hb.of (fun r hr => ?_) k.rd k.wr bt, by rw [p4, hp], hv, ?_⟩
  · simp only [baseRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [a10, hb.env.h10]
    all_goals exact k.gpr _ (by decide)
  · rw [a26, mask_eq_zero, hp, hb.bY, decide_eq_false_iff_not]

/-- 0 into `r3`. -/
theorem TK0 {Φ : CD → State → Prop} (hΦ : ∀ d s, Φ d s → Base d s) {d : CD} {s : State}
    (h : Φ d s) : WP isa (.block [.li .r3 0]) s (CF d) := by
  refine WP.mono (WP.keep [.r3] (Q := fun _ => True) (by prun; exact ⟨_, rfl⟩) (by decide)) fun t ⟨_, k⟩ => ?_
  show t.gpr .r23 = d.S
  rw [k.gpr .r23 (by decide), (hΦ d s h).r23]

/-- 1 into `r3`. -/
theorem TK1 {Φ : CD → State → Prop} (hΦ : ∀ d s, Φ d s → Base d s) {d : CD} {s : State}
    (h : Φ d s) : WP isa (.block [.li .r3 1]) s (CF d) := by
  refine WP.mono (WP.keep [.r3] (Q := fun _ => True) (by prun; exact ⟨_, rfl⟩) (by decide)) fun t ⟨_, k⟩ => ?_
  show t.gpr .r23 = d.S
  rw [k.gpr .r23 (by decide), (hΦ d s h).r23]

theorem TQ {d : CD} {s : State} (h : C5 d s ∧ s.gpr .r26 ≠ 0) : WP isa (.block hasQ) s (C6 d) := by
  obtain ⟨⟨hb, hp, hv, _⟩, _⟩ := h
  refine WP.mono (WP.keep [.r0] (Q := fun t => (t.gpr .r0 == 0) = decide (d.L = 3 * d.k) ∧ t.mem = s.mem) (by
      unfold hasQ
      prun [hb.r27, hb.r28]
      exact sub_3k_zero (by rcases hb.hL with h | h <;> have := hb.k1024 <;> omega) (by have := hb.k1024; omega))
    (by decide)) fun t ⟨⟨a0, m⟩, k⟩ => ⟨hb.same k m, by rw [arr, m]; exact hp, hv, ?_⟩
  rw [← beq_iff_eq, a0, decide_eq_true_iff]

theorem TS {d : CD} {s : State} (h : C6 d s ∧ s.gpr .r0 = 0) : WP isa subgroup s (CF d) := by
  obtain ⟨⟨hb, hp, hv, h0⟩, hz⟩ := h
  have h3k := h0.mp hz
  have hf := modulus_facts hv
  have hk := hb.k64
  refine WP.mono (subgroup_ok hb.env hb.r23 hb.r21 hb.r28 (by omega) hb.k1024 (by rw [hp]; omega)
    (by rw [hp]; exact hf.2)
    (fun i hi => by rw [off_off']; exact hb.rdD _ (by omega))
    (fun i hi => by rw [off_off']; exact hb.sepD _ (by omega))) fun t ⟨_, k⟩ => ?_
  show t.gpr .r23 = d.S
  rw [k.gpr .r23 (by decide), hb.r23]

end VG.Proof.Ffdh.PPC64LE.Domain

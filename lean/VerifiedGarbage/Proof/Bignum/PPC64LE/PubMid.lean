module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.PublicChecked
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubE
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubSan
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubScan
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubOut
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.ReverseEncoding
import VerifiedGarbage.Proof.Bignum.ReadPrefix
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# The RSA public-key operation on PPC64LE: from `setup` to the output

`mid_ok`: from the state after `setup` (`Mid`), everything up to restoring
the registers: the result and the return value, with only the arrays and
`out` changed.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Pub

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.PublicChecked

theorem exponentValid_sat (v : Nat) : Spec.Rsa.exponentValid (sat v) = Spec.Rsa.exponentValid v := by
  unfold sat
  by_cases h : v < 2 ^ 33
  · rw [Nat.min_eq_left (Nat.le_of_lt h)]
  · rw [Nat.min_eq_right (by omega)]
    have h2 : (decide (v < 2 ^ 33)) = false := decide_eq_false h
    simp only [Spec.Rsa.exponentValid, h2, Bool.and_false]
    decide

theorem mask_and (a c : Bool) :
    (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if a then 1 else 0)) &&&
        (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if c then 1 else 0)) =
      BitVec.ofNat 64 0 - BitVec.ofNat 64 (if (a && c) then 1 else 0) := by
  cases a <;> cases c <;> decide

/-- `k` bytes reversed from the low bytes of a number of `2 w` digits below
`256^k`: its I2OSP. -/
theorem out_bytes {m m' : Mem} {O B : Addr} {d k w v : Nat} (hkw : k ≤ 8 * w)
    (hv : Mont.val32 m B d (2 * w) = v) (hvk : v < 256 ^ k)
    (h : ∀ i < k, m' (off O i) = m (off B (d + (k - 1 - i)))) :
    Spec.Rsa.bytesAt m' O k = Spec.Rsa.i2osp v k := by
  rw [reversed_i2osp m m' (off B d) O k fun j hj => by rw [h j hj, off, off, Offset.add_add]]
  congr 1
  have e := read_eq_val32 m B (2 * w) d
  rw [hv] at e
  rw [read_prefix_value m (off B d) (show k ≤ 4 * (2 * w) by omega) (by rw [e, ← pow256_eq]; exact hvk), e]

theorem zero_bytes {m' : Mem} {O : Addr} {k : Nat} (h : ∀ i < k, m' (off O i) = 0) :
    Spec.Rsa.bytesAt m' O k = List.replicate k 0 := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt])
  intro i h1 h2
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
  simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h1
  exact h i h1

theorem bytes_apart {m m' : Mem} {B X : Addr} {Z o n k : Nat} (h : Outside B o n m m') (hn : o + n ≤ Z)
    (hsep : ∀ i < k, ∀ x, ofs B x < Z → off X i ≠ x) : Spec.Rsa.bytesAt m' X k = Spec.Rsa.bytesAt m X k := by
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  show m' (off X i) = m (off X i)
  refine h _ (Or.inr ?_)
  have := hsep i hi (off X i)
  by_contra hc
  exact this (by omega) rfl

theorem mask_and_prop (a : Bool) (p : Prop) [Decidable p] :
    (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if a then 1 else 0)) &&&
        (BitVec.ofNat 64 0 - BitVec.ofNat 64 (if p then 1 else 0)) =
      BitVec.ofNat 64 0 - BitVec.ofNat 64 (if (a && decide p) then 1 else 0) := by
  by_cases hp : p <;> simp only [hp, decide_true, decide_false] <;> cases a <;> decide

/-- Memory changed only at offsets `[d, d + L)` of `S`, then at `O`'s first
`k` bytes. -/
theorem frame_two {S O : Addr} {d L k : Nat} {m m₁ m' : Mem} (h₁ : Outside S d L m m₁)
    (h₂ : Outside O 0 k m₁ m') (hdL : d + L ≤ 2 ^ 64) : Frame [⟨off S d, L⟩, ⟨O, k⟩] m m' := by
  intro x hx
  have a := hx _ (List.mem_cons_self ..)
  have b := hx _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  simp only [Region.Contains] at a b
  rw [h₂ x (Or.inr (by simp only [ofs]; omega))]
  refine h₁ x ?_
  have := Offset.lt_iff x S (d := d) (n := L) hdL
  simp only [ofs]
  by_contra hc
  exact a (by have := this.mpr ⟨by omega, by omega⟩; simp only [off]; omega)

/-- The public data of a run: `out` and `k`, `pre`, `e` and its length, the
input, and the working space and its size in bytes. -/
structure PD where
  O : Addr
  k : Nat
  P : Addr
  E : Addr
  L : Nat
  X : Addr
  S : Addr
  Z : Nat

/-- The words of a number of `k` bytes. -/
abbrev PD.w (d : PD) : Nat := (d.k + 7) / 8

/-- What holds after `setup`. -/
structure Mid (d : PD) (s : State) : Prop where
  scr : Scr s d.S d.Z
  out : Scr s d.O d.k
  k64 : 64 ≤ d.k
  k1024 : d.k ≤ 1024
  hZ : slot d.w 8 ≤ d.Z
  L1 : 1 ≤ d.L
  Lk : d.L ≤ d.k
  nwP : d.P.toNat + 16 * d.w ≤ 2 ^ 64
  sepP : ∀ x, ofs d.P x < 16 * d.w → d.Z ≤ ofs d.S x
  sepO : ∀ x, ofs d.O x < d.k → d.Z ≤ ofs d.S x
  sepE : ∀ i < d.L, ∀ x, ofs d.S x < d.Z → off d.E i ≠ x
  sepX : ∀ i < d.k, ∀ x, ofs d.S x < d.Z → off d.X i ≠ x
  rdP : ∀ i < 2 * d.w, InRegions (s.rd ++ s.wr) (off d.P (8 * i)) 8
  rdE : ∀ i < d.L, InRegions (s.rd ++ s.wr) (off d.E i) 1
  rdX : ∀ i < d.k, InRegions (s.rd ++ s.wr) (off d.X i) 1
  r5 : s.gpr .r5 = off d.P 0
  r7 : s.gpr .r7 = off d.E 0
  r8 : s.gpr .r8 = BitVec.ofNat 64 d.L
  r9 : s.gpr .r9 = d.X
  r23 : s.gpr .r23 = d.S
  r27 : s.gpr .r27 = off d.O 0
  r28 : s.gpr .r28 = BitVec.ofNat 64 d.k
  r10 : s.gpr .r10 = off d.S (slot d.w 0)
  r11 : s.gpr .r11 = BitVec.ofNat 64 (2 * d.w)
  r29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (d.w + 2))

/-- The registers from `readE` to `output`. -/
def midRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22, .r24,
    .r25, .r26]

/-- What holds after `output`: the result, with only the arrays and `out`
changed. -/
def MidPost (d : PD) (s t : State) : Prop :=
  (∀ nB : List Byte, nB.length = d.k →
    Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt s.mem d.P (2 * d.w)) →
    Spec.Rsa.written t.mem d.O d.k ((t.gpr .r3).setWidth 32)
      (Spec.Rsa.publicOpChecked nB (Spec.Rsa.bytesAt s.mem d.E d.L) (Spec.Rsa.bytesAt s.mem d.X d.k))) ∧
    Frame [⟨off d.S (slot d.w 0), 8 * (8 * (d.w + 2))⟩, ⟨d.O, d.k⟩] s.mem t.mem ∧ Keep midRegs s t

/-- `e`'s number, saturated. -/
abbrev PD.ev (d : PD) (m : Mem) : Nat := sat (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m d.E d.L))

/-- The input's number. -/
abbrev PD.x (d : PD) (m : Mem) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt m d.X d.k)

/-- What holds after `sanitize`, from `s` after `setup`. -/
structure M5 (d : PD) (s t : State) : Prop where
  keep : Keep midRegs s t
  r24 : t.gpr .r24 = BitVec.ofNat 64 (d.ev s.mem) <<< 31
  r26 : t.gpr .r26 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if Spec.Rsa.exponentValid (d.ev s.mem) then 1 else 0)
  r10 : t.gpr .r10 = off d.S (slot d.w 0)
  odd : wv t.mem d.S (slot d.w 0) d.w % 2 = 1
  ge2 : 2 ≤ wv t.mem d.S (slot d.w 0) d.w
  low : (word t.mem d.S (slot d.w 0)).toNat % 2 = 1
  rr : wv t.mem d.S (slot d.w 1) d.w < wv t.mem d.S (slot d.w 0) d.w
  valid : wv s.mem d.P 0 d.w % 2 = 1 → 2 ^ (64 * (d.w - 1)) ≤ wv s.mem d.P 0 d.w →
    wv t.mem d.S (slot d.w 0) d.w = wv s.mem d.P 0 d.w ∧
      (wv s.mem d.P (8 * d.w) d.w < wv s.mem d.P 0 d.w → wv t.mem d.S (slot d.w 1) d.w = wv s.mem d.P (8 * d.w) d.w)
  top : word t.mem d.S (slot d.w 4 + 8 * d.w) = 0
  x : wv t.mem d.S (slot d.w 4) d.w = d.x s.mem
  frame : Outside d.S (slot d.w 0) (8 * (8 * (d.w + 2))) s.mem t.mem

theorem mid5_ok {d : PD} {s : State} {c : Prog isa} {Q : State → Prop} (h : Mid d s)
    (hQ : ∀ t, M5 d s t → WP isa c t Q) :
    WP isa (.seq readE (.seq (.block checkE) (.seq copyPre (.seq loadX (.seq sanitize c))))) s Q := by
  have hnw := h.scr.nowrap
  have hwd : d.w = (d.k + 7) / 8 := rfl
  have hw8 : 8 ≤ d.w := by have := h.k64; omega
  have hw' : d.w < 2 ^ 31 := by have := h.k1024; omega
  have hkw : d.k ≤ 8 * d.w := by omega
  have e : ∀ j, slot d.w j = hdrBytes + j * (8 * (d.w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have hZ := h.hZ
  -- `e`.
  refine WP.seq (WP.mono (readE_ok (E := d.E) (L := d.L) h.r7 h.r8 h.L1 (by have := h.Lk; have := h.k1024; omega)
    h.rdE) fun s₁ ⟨⟨a24, m1⟩, k1⟩ => ?_)
  have hev2 : d.ev s.mem ≤ 2 ^ 33 := by unfold PD.ev sat; omega
  refine WP.seq (WP.mono (checkE_ok a24 hev2) fun s₂ ⟨⟨a26, a24', m2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  have m12 : s₂.mem = s.mem := m2.trans m1
  -- `pre` into arrays 0 and 1.
  refine WP.seq (WP.mono (copyPre_ok (h.scr.congr k12.wr) h.nwP (by rw [k12.rd, k12.wr]; exact h.rdP)
    ((k12.gpr _ (by decide)).trans h.r5) ((k12.gpr _ (by decide)).trans h.r10)
    ((k12.gpr _ (by decide)).trans h.r29) ((k12.gpr _ (by decide)).trans h.r11) (by omega) hw' hZ h.sepP)
    fun s₃ ⟨⟨c0, c1, out3⟩, k3⟩ => ?_)
  have k13 := k12.trans k3
  rw [m12] at c0 c1 out3
  have N3 : wv s₃.mem d.S (slot d.w 0) d.w = wv s.mem d.P 0 d.w :=
    wv_congr2 fun i hi => by rw [Nat.zero_add]; exact c0 i hi
  have R3 : wv s₃.mem d.S (slot d.w 1) d.w = wv s.mem d.P (8 * d.w) d.w := wv_congr2 fun i hi => c1 i hi
  -- The input into array 4.
  refine WP.seq (WP.mono (loadX_ok (h.scr.congr k13.wr) ((k13.gpr _ (by decide)).trans h.r23)
    ((k13.gpr _ (by decide)).trans h.r9) ((k13.gpr _ (by decide)).trans h.r28)
    ((k13.gpr _ (by decide)).trans h.r10) ((k13.gpr _ (by decide)).trans h.r29)
    ((k13.gpr _ (by decide)).trans h.r11) (by omega) hkw hw' hZ (by rw [k13.rd, k13.wr]; exact h.rdX) h.sepX)
    fun s₄ ⟨⟨x4, z4, out4, a10⟩, k4⟩ => ?_)
  rw [bytes_apart out3 (by omega) h.sepX] at x4
  have k14 := k13.trans k4
  have N4 : wv s₄.mem d.S (slot d.w 0) d.w = wv s.mem d.P 0 d.w := by
    rw [out4.wv (Or.inl (by omega)) (by omega), N3]
  have R4 : wv s₄.mem d.S (slot d.w 1) d.w = wv s.mem d.P (8 * d.w) d.w := by
    rw [out4.wv (Or.inl (by omega)) (by omega), R3]
  -- `n` and `R² mod n` made safe.
  refine WP.seq (WP.mono (sanitize_ok (h.scr.congr k14.wr) (by omega) hw' hZ a10
    ((k14.gpr _ (by decide)).trans h.r29) ((k14.gpr _ (by decide)).trans h.r11))
    fun s₅ ⟨⟨n5o, n5g, n5w, r5l, n5v, out5⟩, k5⟩ => hQ s₅ ⟨(k14.trans k5).mono, ?_, ?_,
      (k5.gpr _ (by decide)).trans a10, ?_, ?_, n5w, ?_, ?_, by rw [out5.word (by omega) (by omega)]; exact z4, ?_,
      ((out3.mono (Nat.le_refl _) (by omega)).trans (out4.mono (by omega) (by omega))).trans
        (out5.mono (Nat.le_refl _) (by omega))⟩)
  · rw [k5.gpr .r24 (by decide), k4.gpr .r24 (by decide), k3.gpr .r24 (by decide)]; exact a24'
  · rw [k5.gpr .r26 (by decide), k4.gpr .r26 (by decide), k3.gpr .r26 (by decide)]; exact a26
  · rw [← Pre.val32_eq_wv]; exact n5o
  · rw [← Pre.val32_eq_wv]; exact n5g
  · rw [← Pre.val32_eq_wv, ← Pre.val32_eq_wv]; exact r5l
  · simp only [Pre.val32_eq_wv, N4, R4] at n5v
    exact n5v
  · rw [out5.wv (Or.inr (by omega)) (by omega), ← Pre.val32_eq_wv]; exact x4

/-- What holds after `power`, from `s` after `setup`, with `N` the modulus
used. -/
structure M8 (d : PD) (s u : State) (N : Nat) : Prop where
  keep : Keep midRegs s u
  r10 : u.gpr .r10 = off d.S (slot d.w 0)
  r26 : u.gpr .r26 = BitVec.ofNat 64 0 -
    BitVec.ofNat 64 (if (Spec.Rsa.exponentValid (d.ev s.mem) && decide (d.x s.mem < N)) then 1 else 0)
  res : wv s.mem d.P 0 d.w % 2 = 1 → 2 ^ (64 * (d.w - 1)) ≤ wv s.mem d.P 0 d.w →
    wv s.mem d.P (8 * d.w) d.w = 2 ^ (64 * d.w) * 2 ^ (64 * d.w) % wv s.mem d.P 0 d.w →
    N = wv s.mem d.P 0 d.w ∧ (Spec.Rsa.exponentValid (d.ev s.mem) = true →
      wv u.mem d.S (slot d.w 4) d.w = d.x s.mem ^ (d.ev s.mem % 2 ^ 33) % N)
  frame : Outside d.S (slot d.w 0) (8 * (8 * (d.w + 2))) s.mem u.mem

/-- What holds after `checkX`, from `t` after `sanitize`. -/
def M7 (d : PD) (t s₇ : State) : Prop :=
  ∃ s₆ : State, ((s₆.gpr .r12).toNat < 2 ^ 32 ∧
      (Mont.w32 t.mem d.S (slot d.w 0) * (s₆.gpr .r12).toNat + 1) % 2 ^ 32 = 0 ∧ s₆.mem = t.mem) ∧
    Keep [.r0, .r3, .r4, .r12] t s₆ ∧
    (s₇.gpr .r26 = s₆.gpr .r26 &&& (BitVec.ofNat 64 0 - BitVec.ofNat 64
        (if Mont.val32 s₆.mem d.S (slot d.w 4) (2 * d.w) < Mont.val32 s₆.mem d.S (slot d.w 0) (2 * d.w) then 1
          else 0)) ∧
      Mont.Outside d.S (slot d.w 3) (8 * d.w) s₆.mem s₇.mem) ∧
    Keep [.r0, .r3, .r8, .r9, .r14, .r15, .r16, .r17, .r20, .r26] s₆ s₇

theorem mid7_ok {d : PD} {s t : State} (h : Mid d s) (h5 : M5 d s t) :
    WP isa (.seq (.block minv) checkX) t (M7 d t) := by
  have hnw := h.scr.nowrap
  have hwd : d.w = (d.k + 7) / 8 := rfl
  have hw8 : 8 ≤ d.w := by have := h.k64; omega
  have hw' : d.w < 2 ^ 31 := by have := h.k1024; omega
  have e : ∀ j, slot d.w j = hdrBytes + j * (8 * (d.w + 2)) := fun _ => rfl
  have e0 := e 0; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have hZ := h.hZ
  have k5 := h5.keep
  have hs₅ := h.scr.congr k5.wr
  -- `-n⁻¹ mod 2³²`.
  refine WP.seq (WP.mono (minv_ok hs₅ h5.r10 (by omega) h5.low) fun s₆ ⟨⟨i12, iinv, m6⟩, k6⟩ => ?_)
  have k56 := k5.trans k6
  -- Whether the input is below `n`.
  exact WP.mono (checkX_ok (h.scr.congr k56.wr) (by omega) hw' hZ ((k6.gpr _ (by decide)).trans h5.r10)
    ((k56.gpr _ (by decide)).trans h.r29) ((k56.gpr _ (by decide)).trans h.r11)
    (by rw [m6]; exact h5.top)) fun s₇ ⟨⟨c26, out7⟩, k7⟩ => ⟨s₆, ⟨i12, iinv, m6⟩, k6, ⟨c26, out7⟩, k7⟩

/-- From `setup` to the checks. -/
theorem prep_ok {d : PD} {s : State} (h : Mid d s) :
    WP isa prep s fun u => ∃ t, M5 d s t ∧ M7 d t u :=
  mid5_ok h fun t h5 => WP.mono (mid7_ok h h5) fun _ h7 => ⟨t, h5, h7⟩

theorem mid8_ok {d : PD} {s t s₇ : State} {Q : State → Prop} (h : Mid d s) (h5 : M5 d s t)
    (h7 : M7 d t s₇) (hQ : ∀ u N, M8 d s u N → Q u) : WP isa power s₇ Q := by
  have hnw := h.scr.nowrap
  have hwd : d.w = (d.k + 7) / 8 := rfl
  have hw8 : 8 ≤ d.w := by have := h.k64; omega
  have hw' : d.w < 2 ^ 31 := by have := h.k1024; omega
  have e : ∀ j, slot d.w j = hdrBytes + j * (8 * (d.w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e3 := e 3; have e4 := e 4; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  have hZ := h.hZ
  have k5 := h5.keep
  obtain ⟨s₆, ⟨i12, iinv, m6⟩, k6, ⟨c26, out7⟩, k7⟩ := h7
  have k56 := k5.trans k6
  have k57 := k56.trans k7
  have out7' : Outside d.S (slot d.w 3) (8 * d.w) t.mem s₇.mem := by
    rw [← m6]; exact fun x hx => out7 x hx
  simp only [Pre.val32_eq_wv] at c26
  rw [m6] at c26
  have N7 : wv s₇.mem d.S (slot d.w 0) d.w = wv t.mem d.S (slot d.w 0) d.w :=
    out7'.wv (Or.inl (by omega)) (by omega)
  have R7 : wv s₇.mem d.S (slot d.w 1) d.w = wv t.mem d.S (slot d.w 1) d.w :=
    out7'.wv (Or.inl (by omega)) (by omega)
  have X7 : wv s₇.mem d.S (slot d.w 4) d.w = wv t.mem d.S (slot d.w 4) d.w :=
    out7'.wv (Or.inr (by omega)) (by omega)
  have W7 : Mont.w32 s₇.mem d.S (slot d.w 0) = Mont.w32 t.mem d.S (slot d.w 0) := by
    rw [Mont.Outside.w32 out7 (Or.inl (by omega)) (by omega), m6]
  -- `x^e mod n` into array 4.
  refine WP.mono (power_ok (E := d.ev s.mem) (h.scr.congr k57.wr) (by omega) hw' hZ
    ((k7.gpr _ (by decide)).trans ((k6.gpr _ (by decide)).trans h5.r10)) ((k57.gpr _ (by decide)).trans h.r29)
    ((k57.gpr _ (by decide)).trans h.r11) (by rw [k7.gpr .r12 (by decide)]; exact i12)
    (by rw [k7.gpr .r12 (by decide), W7]; exact iinv)
    (by rw [Pre.val32_eq_wv, N7]; exact h5.ge2) (by rw [Pre.val32_eq_wv, N7]; exact h5.odd)
    (by rw [Pre.val32_eq_wv, Pre.val32_eq_wv, N7, R7]; exact h5.rr)
    (by rw [k7.gpr .r24 (by decide), k6.gpr .r24 (by decide)]; exact h5.r24)) fun s₈ ⟨⟨p8, out8⟩, k8⟩ => ?_
  simp only [Pre.val32_eq_wv, N7, R7, X7, h5.x] at p8
  refine hQ s₈ (wv t.mem d.S (slot d.w 0) d.w) ⟨(k57.trans k8).mono,
    (k8.gpr _ (by decide)).trans ((k7.gpr _ (by decide)).trans ((k6.gpr _ (by decide)).trans h5.r10)), ?_,
    fun hodd htop hRR => ?_, ?_⟩
  · rw [k8.gpr .r26 (by decide), c26, k6.gpr .r26 (by decide), h5.r26, h5.x, mask_and_prop]
  · obtain ⟨N5, RR5⟩ := h5.valid hodd htop
    have hRl : wv s.mem d.P (8 * d.w) d.w < wv s.mem d.P 0 d.w := by
      rw [hRR]; exact Nat.mod_lt _ (by omega)
    refine ⟨N5, fun he => p8 ?_ ?_⟩
    · simp only [Spec.Rsa.exponentValid, Bool.and_eq_true, decide_eq_true_eq] at he
      omega
    · rw [RR5 hRl, N5, hRR]
  · have o8 : Outside d.S (slot d.w 0) (8 * (8 * (d.w + 2))) s₇.mem s₈.mem := fun x hx => out8 x fun r hr => by
      have e2 := e 2; have e5 := e 5; have e6 := e 6; have e7 := e 7
      simp only [powRs, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hr
      obtain ⟨j, hj, rfl⟩ := hr
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [Mont.ofs, ofs] at hx ⊢ <;> omega
    exact (h5.frame.trans (out7'.mono (by omega) (by omega))).trans o8

theorem midOut_ok {d : PD} {s u : State} {N : Nat} {Q : State → Prop} (h : Mid d s) (h8 : M8 d s u N)
    (hQ : ∀ t, MidPost d s t → WP isa (.block PublicChecked.restore) t Q) :
    WP isa (.seq output (.block PublicChecked.restore)) u Q := by
  have hnw := h.scr.nowrap
  have hwd : d.w = (d.k + 7) / 8 := rfl
  have hkw : d.k ≤ 8 * d.w := by omega
  have e0 : slot d.w 0 = hdrBytes + 0 * (8 * (d.w + 2)) := rfl
  have e8 : slot d.w 8 = hdrBytes + 8 * (8 * (d.w + 2)) := rfl
  have hh : hdrBytes = 256 := rfl
  have k8 := h8.keep
  refine WP.seq (WP.mono (output_ok (h.scr.congr k8.wr) (h.out.congr k8.wr) h8.r10
    ((k8.gpr _ (by decide)).trans h.r29) ((k8.gpr _ (by decide)).trans h.r28)
    ((k8.gpr _ (by decide)).trans h.r27) h8.r26 (by have := h.k64; omega) hkw h.hZ h.sepO)
    fun t ⟨⟨ob, outt, t3⟩, kt⟩ => hQ t ⟨?_, frame_two h8.frame outt (by have := h.k1024; omega),
      (k8.trans kt).mono⟩)
  intro nB hl hpp
  obtain ⟨hv, hn, hr⟩ := pre_of_some hl h.k64 hpp
  obtain ⟨hodd, hn1, htop⟩ := valid_facts hv h.k64
  rw [← hn] at hodd htop hn1
  obtain ⟨hN, res⟩ := h8.res hodd htop
    (by rw [hr, hn, ← Nat.pow_add, show 64 * d.w + 64 * d.w = 128 * d.w by omega])
  rw [hN, hn] at res ob t3
  have hE := exponentValid_sat (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem d.E d.L))
  have hnk : Spec.Rsa.os2ip nB < 256 ^ d.k := by rw [← hl]; exact os2ip_lt nB
  unfold Spec.Rsa.publicOpChecked Spec.Rsa.publicOp Spec.Rsa.encrypt
  rw [← hE, hl]
  by_cases hb : (Spec.Rsa.exponentValid (d.ev s.mem) && decide (d.x s.mem < Spec.Rsa.os2ip nB)) = true
  · obtain ⟨he, hx⟩ : Spec.Rsa.exponentValid (d.ev s.mem) = true ∧ d.x s.mem < Spec.Rsa.os2ip nB := by
      simpa using hb
    have hlt : d.ev s.mem < 2 ^ 33 := by
      simp only [Spec.Rsa.exponentValid, Bool.and_eq_true, decide_eq_true_eq] at he; exact he.2
    have hev : sat (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem d.E d.L)) =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem d.E d.L) := by
      unfold PD.ev sat at hlt; unfold sat; omega
    replace res := res he
    simp only [PD.ev, PD.x] at he hx res
    simp only [he, hv, hx, ↓reduceIte, Option.map_some]
    refine ⟨by rw [t3, hb]; rfl, ?_⟩
    rw [VG.Proof.Bignum.powMod_eq]
    rw [hev, Nat.mod_eq_of_lt (a := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem d.E d.L)) (b := 2 ^ 33)
      (by rw [← hev]; exact hlt)] at res
    exact out_bytes hkw (by rw [Pre.val32_eq_wv]; exact res)
      (Nat.lt_trans (Nat.mod_lt _ (by omega)) hnk) fun i hi => by rw [ob i hi]; simp only [hb, ↓reduceIte]
  · have hnone : (if Spec.Rsa.exponentValid (d.ev s.mem) = true then
        (if Spec.Rsa.modulusValid (Spec.Rsa.os2ip nB) d.k = true then
          Option.map (fun x => Spec.Rsa.i2osp x d.k)
            (if d.x s.mem < Spec.Rsa.os2ip nB then
              some (Spec.Rsa.powMod (d.x s.mem) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem d.E d.L))
                (Spec.Rsa.os2ip nB))
            else none)
        else none)
      else none) = none := by
      by_cases he : Spec.Rsa.exponentValid (d.ev s.mem) = true
      · have hx : ¬ d.x s.mem < Spec.Rsa.os2ip nB := fun hx => hb (by simp [he, hx])
        simp only [he, hv, hx, ↓reduceIte, Option.map_none]
      · simp only [he, Bool.false_eq_true, ↓reduceIte]
    simp only [PD.ev, PD.x] at hnone
    rw [hnone]
    refine ⟨by rw [t3]; simp only [hb]; rfl,
      zero_bytes fun i hi => by rw [ob i hi]; simp only [hb, Bool.false_eq_true, ↓reduceIte]⟩

/-- From `setup` to the output. -/
theorem mid_ok {d : PD} {s : State} {Q : State → Prop} (h : Mid d s)
    (hQ : ∀ t, MidPost d s t → WP isa (.block PublicChecked.restore) t Q) :
    WP isa (.seq prep (.seq power (.seq output (.block PublicChecked.restore)))) s Q :=
  WP.seq (WP.mono (prep_ok h) fun _ ⟨_, h5, h7⟩ => WP.seq (mid8_ok h h5 h7 fun _ _ h8 => midOut_ok h h8 hQ))

end VG.Proof.Bignum.PPC64LE.Pub

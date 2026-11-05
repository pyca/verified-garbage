module

public import VerifiedGarbage.Impl.Ffdh.RISCV64.Domain
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Ffdh.RISCV64.ZMask
public import VerifiedGarbage.Proof.Bignum.RISCV64.PubSave
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Ffdh.RISCV64.Power
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PubMid
import VerifiedGarbage.Proof.Bignum.RISCV64.PubPower
import VerifiedGarbage.Proof.Bignum.RISCV64.PubSan
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCheck
import VerifiedGarbage.Proof.Bignum.RISCV64.ModArith
import VerifiedGarbage.Proof.Bignum.RISCV64.ModExpWin
import VerifiedGarbage.Proof.Bignum.RISCV64.MontCore
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# FFDH's domain checks on RISC-V: the pieces

The public data of a run (`DD`): the domain, its length, `p_len`, the
working space and its size, the domain's octets, and the value checked by
`vg_ffdh_check_public` (y's address and octets). `DCtx`: what holds from the
front on, but for the registers: the working space, the domain apart from it,
its octets and the header's words 0 and 1 (the domain and its length).
`DBase`: `DCtx` and the registers `setup` leaves. Each piece of the code
takes a predicate on the state, for the data, to the next one, changing only
the arrays (`DArr`, memory from byte 256 of the working space on):

* `loadN_P`, `check1_P`, `check2_P`: p into array 0 and its check (`P4`);
* `range_ok`: a value's octets into array 4, and the mask of its range;
* `hasQ_ok`: whether there is q;
* `sg1_ok`, `sg2_ok`, `isOne_ok`: the subgroup check of the value in
  array 4 (`subgroup`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.Domain

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64 VG.Impl.Ffdh.RISCV64.Domain
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot)
open VG.Impl.Bignum.RISCV64.PublicChecked (base)

/-- The public data of a run. -/
structure DD where
  D : Addr
  L : Nat
  k : Nat
  S : Addr
  Z : Nat
  db : List Byte
  Y : Addr
  yb : List Byte

/-- The words of p. -/
abbrev DD.w (x : DD) : Nat := (x.k + 7) / 8

/-- p, g, q and y. -/
abbrev DD.p (x : DD) : Nat := Spec.Rsa.os2ip (x.db.take x.k)
abbrev DD.g (x : DD) : Nat := Spec.Rsa.os2ip ((x.db.drop x.k).take x.k)
abbrev DD.q (x : DD) : Nat := Spec.Rsa.os2ip ((x.db.drop (2 * x.k)).take x.k)
abbrev DD.y (x : DD) : Nat := Spec.Rsa.os2ip x.yb

/-- What holds from the front on, but for the registers. -/
structure DCtx (x : DD) (s : State) : Prop where
  scr : Scr s x.S x.Z
  k64 : 64 ≤ x.k
  k1024 : x.k ≤ 1024
  hL : x.L = 2 * x.k ∨ x.L = 3 * x.k
  hZ : slot x.w 24 ≤ x.Z
  rdD : ∀ i < x.L, InRegions (s.rd ++ s.wr) (off x.D i) 1
  sepD : ∀ i < x.L, ∀ y, ofs x.S y < x.Z → off x.D i ≠ y
  bD : Spec.Rsa.bytesAt s.mem x.D x.L = x.db
  rdY : ∀ i < x.k, InRegions (s.rd ++ s.wr) (off x.Y i) 1
  sepY : ∀ i < x.k, ∀ y, ofs x.S y < x.Z → off x.Y i ≠ y
  bY : Spec.Rsa.bytesAt s.mem x.Y x.k = x.yb
  hD : word s.mem x.S 0 = x.D
  hLw : word s.mem x.S 8 = BitVec.ofNat 64 x.L

/-- The arrays: memory from byte 256 of the working space on. -/
abbrev DArr (x : DD) (m m' : Mem) : Prop := Outside x.S 256 (x.Z - 256) m m'

theorem DArr.trans {x : DD} {m₁ m₂ m₃ : Mem} (a : DArr x m₁ m₂) (b : DArr x m₂ m₃) : DArr x m₁ m₃ :=
  Outside.trans a b

theorem DArr.refl (x : DD) (m : Mem) : DArr x m m := Outside.refl _ _ _ _

theorem darr_of {x : DD} {m m' : Mem} {o n : Nat} (h : Outside x.S o n m m') (ho : 256 ≤ o) (hn : o + n ≤ x.Z) :
    DArr x m m' := h.mono ho (by omega_arith)

theorem DCtx.keep {x : DD} {s t : State} (h : DCtx x s) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hm : DArr x s.mem t.mem) : DCtx x t := by
  have hn := h.scr.nowrap
  have hZ := h.hZ
  have h24 : 256 ≤ slot x.w 24 := by unfold slot hdrBytes; omega_arith
  have hw : ∀ d, d + 8 ≤ 256 → word t.mem x.S d = word s.mem x.S d := fun d hd =>
    Outside.word hm (Or.inl hd) (by omega_arith)
  exact ⟨h.scr.congr hwr, h.k64, h.k1024, h.hL, h.hZ, by rw [hrd, hwr]; exact h.rdD, h.sepD,
    by rw [Pub.bytes_apart hm (by omega_arith) h.sepD]; exact h.bD,
    by rw [hrd, hwr]; exact h.rdY, h.sepY,
    by rw [Pub.bytes_apart hm (by omega_arith) h.sepY]; exact h.bY,
    by rw [hw 0 (by decide)]; exact h.hD, by rw [hw 8 (by decide)]; exact h.hLw⟩

theorem DCtx.same {x : DD} {s t : State} {rs : List Reg} (h : DCtx x s) (k : Keep rs s t) (hm : t.mem = s.mem) :
    DCtx x t := h.keep k.2.1 k.2.2 (by rw [hm]; exact DArr.refl _ _)

/-- `DCtx` and the registers `setup` leaves. -/
structure DBase (x : DD) (s : State) : Prop where
  ctx : DCtx x s
  s6 : s.gpr .s6 = x.S
  a7 : s.gpr .a7 = off x.S (slot x.w 0)
  s5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (x.w + 2))
  t0 : s.gpr .t0 = BitVec.ofNat 64 x.w
  s11 : s.gpr .s11 = BitVec.ofNat 64 x.k

/-- The registers `DBase` fixes. -/
def dbaseRegs : List Reg := [.s6, .a7, .s5, .t0, .s11]

theorem DBase.keep {x : DD} {s t : State} {rs : List Reg} (h : DBase x s) (k : Keep rs s t)
    (hm : DArr x s.mem t.mem) (hr : ∀ r ∈ dbaseRegs, r ∉ rs := by decide) : DBase x t := by
  simp only [dbaseRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  exact ⟨h.ctx.keep k.2.1 k.2.2 hm, (k.gpr hr.1).trans h.s6, (k.gpr hr.2.1).trans h.a7,
    (k.gpr hr.2.2.1).trans h.s5, (k.gpr hr.2.2.2.1).trans h.t0, (k.gpr hr.2.2.2.2).trans h.s11⟩

theorem DBase.same {x : DD} {s t : State} {rs : List Reg} (h : DBase x s) (k : Keep rs s t) (hm : t.mem = s.mem)
    (hr : ∀ r ∈ dbaseRegs, r ∉ rs := by decide) : DBase x t :=
  h.keep k (by rw [hm]; exact DArr.refl _ _) hr

theorem DBase.pins {x : DD} {s₁ s₂ : State} (h₁ : DBase x s₁) (h₂ : DBase x s₂) :
    ∀ r ∈ dbaseRegs, s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [dbaseRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h₁.s6, h₂.s6]
  · rw [h₁.a7, h₂.a7]
  · rw [h₁.s5, h₂.s5]
  · rw [h₁.t0, h₂.t0]
  · rw [h₁.s11, h₂.s11]

/-! ## p -/

theorem dtake_len {x : DD} {s : State} (hc : DCtx x s) : (x.db.take x.k).length = x.k := by
  rw [List.length_take, ← hc.bD, VG.Proof.Bignum.bytesAt_length]; rcases hc.hL with h | h <;> omega_arith

theorem dbytes_p {x : DD} {s : State} (hc : DCtx x s) :
    Spec.Rsa.bytesAt s.mem x.D x.k = x.db.take x.k := by
  rw [← hc.bD, Proof.Ffdh.take_bytesAt _ _ (by rcases hc.hL with h | h <;> omega_arith)]

theorem dtake_byte {x : DD} {s : State} (hc : DCtx x s) {i : Nat} (hi : i < x.k) :
    s.mem (off x.D i) = (x.db.take x.k)[i]'(by rw [dtake_len hc]; exact hi) := by
  simp only [← dbytes_p hc, Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]

/-- Before `loadN`: the domain in `s7` and `p_len` in `s8`. -/
def P1 (x : DD) (s : State) : Prop := DBase x s ∧ s.gpr .s7 = off x.D 0 ∧ s.gpr .s8 = BitVec.ofNat 64 x.k

/-- After `loadN`: p in array 0. -/
def P2 (x : DD) (s : State) : Prop :=
  DBase x s ∧ wordsVal s.mem x.S (slot x.w 0) x.w = x.p ∧ s.gpr .s7 = off x.D 0 ∧
    s.gpr .s8 = BitVec.ofNat 64 x.k

/-- After `check1`. -/
def P3 (x : DD) (s : State) : Prop :=
  DBase x s ∧ wordsVal s.mem x.S (slot x.w 0) x.w = x.p ∧ s.gpr .s8 = BitVec.ofNat 64 x.k ∧
    s.gpr .t4 = BitVec.ofNat 64 ((x.db.take x.k).getD 0 0).toNat ∧
    (s.gpr .s0 = 0 ↔ ((x.db.take x.k).getD (x.k - 1) 0).toNat % 2 = 1)

/-- After `check2`: whether p is valid, in `s0`. -/
def P4 (x : DD) (s : State) : Prop :=
  DBase x s ∧ wordsVal s.mem x.S (slot x.w 0) x.w = x.p ∧
    (s.gpr .s0 = 0 ↔ Spec.Rsa.modulusValid x.p x.k = true)

theorem getD_lt {l : List Byte} {i : Nat} (h : i < l.length) : l.getD i 0 = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem loadN_P {x : DD} {s : State} (h : P1 x s) :
    WP isa Precompute.loadN s fun t => P2 x t ∧ DArr x s.mem t.mem ∧ Keep [.a0, .s0, .t3, .t4, .t5] s t := by
  obtain ⟨hb, h7, h8⟩ := h
  have hc := hb.ctx
  have hn := hc.scr.nowrap
  have hZ := hc.hZ
  have hk := hc.k64
  have hk' := hc.k1024
  have hL := hc.hL
  have hwd : x.w = (x.k + 7) / 8 := rfl
  have e0 : slot x.w 0 = 256 := by simp [slot, hdrBytes]
  have e24 : slot x.w 24 = 256 + 24 * (8 * (x.w + 2)) := by simp [slot, hdrBytes]
  refine WP.mono (loadN_ok (dA := slot x.w 0) hc.scr hb.a7 h7 h8 hb.t0 (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (slot_al _ 0) (by omega_arith)
    (fun i hi => hc.rdD i (by omega_arith)) (fun i hi => hc.sepD i (by omega_arith))) fun t ⟨hv, out, k⟩ => ?_
  have hm : DArr x s.mem t.mem := out.mono (by omega_arith) (by omega_arith)
  exact ⟨⟨hb.keep k hm, by rw [hv, dbytes_p hc], (k.gpr (by decide)).trans h7, (k.gpr (by decide)).trans h8⟩, hm, k⟩

theorem check1_P {x : DD} {s : State} (h : P2 x s) :
    WP isa (.block Precompute.check1) s fun t => P3 x t ∧ t.mem = s.mem := by
  obtain ⟨hb, hp, h7, h8⟩ := h
  have hc := hb.ctx
  have hl := dtake_len hc
  have hk := hc.k64
  refine WP.mono (check1_ok (N := x.D) (nb := x.db.take x.k) h7 h8 hk hl
    (fun i hi => hc.rdD i (by rcases hc.hL with h | h <;> omega_arith)) fun i hi => dtake_byte hc hi)
    fun t ⟨⟨i0, i4, im⟩, k⟩ => ⟨⟨hb.same k im, by rw [im]; exact hp, (k.gpr (by decide)).trans h8,
      by rw [i4, getD_lt (by omega_arith)], by rw [i0, getD_lt (by omega_arith)]⟩, im⟩

theorem check2_P {x : DD} {s : State} (h : P3 x s) :
    WP isa Precompute.check2 s fun t => P4 x t ∧ t.mem = s.mem := by
  obtain ⟨hb, hp, h8, h4, h0⟩ := h
  have hc := hb.ctx
  have hl := dtake_len hc
  have hk := hc.k64
  refine WP.mono (check2_ok (nb := x.db.take x.k) h8 hk hc.k1024 hl (by rw [h0, getD_lt (by omega_arith)])
    (by rw [h4, getD_lt (by omega_arith)])) fun t ⟨a, m, k⟩ => ⟨⟨hb.same k m, by rw [m]; exact hp, a⟩, m⟩

/-- `loadP`: p into array 0, and whether it is valid in `s0`. -/
theorem loadP_P {x : DD} {s : State} (h : P1 x s) : WP isa loadP s fun t => P4 x t ∧ DArr x s.mem t.mem := by
  unfold loadP Precompute.check
  refine WP.seq (WP.mono (loadN_P h) fun s₁ ⟨h1, a1, _⟩ => ?_)
  refine WP.seq (WP.mono (check1_P h1) fun s₂ ⟨h2, m2⟩ => ?_)
  refine WP.mono (check2_P h2) fun t ⟨h4, m4⟩ => ⟨h4, ?_⟩
  rw [m4, m2]; exact a1

/-- A valid p in array 0. -/
def PV (x : DD) (s : State) : Prop :=
  DBase x s ∧ wordsVal s.mem x.S (slot x.w 0) x.w = x.p ∧ Spec.Rsa.modulusValid x.p x.k = true

theorem PV.keep {x : DD} {s t : State} {rs : List Reg} (h : PV x s) (k : Keep rs s t) (hm : DArr x s.mem t.mem)
    (h0 : wordsVal t.mem x.S (slot x.w 0) x.w = wordsVal s.mem x.S (slot x.w 0) x.w)
    (hr : ∀ r ∈ dbaseRegs, r ∉ rs := by decide) : PV x t :=
  ⟨h.1.keep k hm hr, by rw [h0]; exact h.2.1, h.2.2⟩

/-- The sizes of the working space and its arrays. -/
theorem dsizes {x : DD} {s : State} (hc : DCtx x s) :
    8 ≤ x.w ∧ x.w ≤ 128 ∧ x.k ≤ 8 * x.w ∧ x.S.toNat + x.Z ≤ 2 ^ 64 ∧
      ∀ j ≤ 24, slot x.w j = 256 + j * (8 * (x.w + 2)) ∧ slot x.w j ≤ x.Z := by
  have hZ := hc.hZ
  have hk := hc.k64
  have hk' := hc.k1024
  have hwd : x.w = (x.k + 7) / 8 := rfl
  refine ⟨by omega_arith, by omega_arith, by omega_arith, hc.scr.nowrap, fun j hj => ⟨rfl, ?_⟩⟩
  simp only [slot, hdrBytes] at hZ ⊢
  have : j * (8 * (x.w + 2)) ≤ 24 * (8 * (x.w + 2)) := Nat.mul_le_mul_right _ hj
  omega_arith

theorem ite_ones (c : Prop) [Decidable c] :
    (if c then BitVec.allOnes 64 else 0) = bmask (decide c) := by
  by_cases h : c
  · rw [ite_eq_left h, decide_eq_true h]; rfl
  · rw [ite_eq_right h, decide_eq_false h]; rfl

theorem range_dec {v p : Nat} (hp : 1 < p) :
    (decide (v ≠ 0 ∧ v ≠ 1 ∧ v ≠ p - 1) && decide (v < p)) = decide (1 < v ∧ v < p - 1) := by
  rw [← Bool.decide_and]; exact decide_eq_decide.mpr (by omega)

/-- The registers `range` writes. -/
def rangeRegs : List Reg :=
  [.a0, .a1, .a5, .a6, .a7, .s0, .s1, .s2, .s3, .s4, .s7, .s8, .s9, .t3, .t4, .t5]

/-- `range`: the `p_len` octets `v` at `P` (`a6`) into array 4, and
`s9 :=` the mask of `1 < v < p − 1`. -/
theorem range_ok {x : DD} {s : State} {P : Addr} (h : PV x s) (h6 : s.gpr .a6 = P)
    (hrd : ∀ i < x.k, InRegions (s.rd ++ s.wr) (off P i) 1)
    (hsep : ∀ i < x.k, ∀ y, ofs x.S y < x.Z → off P i ≠ y) :
    WP isa range s fun t => (PV x t ∧
      wordsVal t.mem x.S (slot x.w 4) x.w = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P x.k) ∧
      t.gpr .s9 = bmask (decide (1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P x.k) ∧
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P x.k) < x.p - 1)) ∧
      DArr x s.mem t.mem) ∧ Keep rangeRegs s t := by
  obtain ⟨hb, hp, hv⟩ := h
  have hc := hb.ctx
  obtain ⟨hw8, hw128, hkw, hn, hsl⟩ := dsizes hc
  have hf := VG.Proof.Bignum.valid_facts hv hc.k64
  have e0 := (hsl 0 (by decide)).1; have e3 := (hsl 3 (by decide)).1; have e4 := (hsl 4 (by decide)).1
  have e5 := (hsl 5 (by decide)).1; have e8 := (hsl 8 (by decide)).1; have z8 := (hsl 8 (by decide)).2
  have hw' : x.w < 2 ^ 31 := by omega_arith
  have hk := hc.k64
  generalize hvd : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem P x.k) = v
  unfold range
  refine WP.seq (WP.mono (Pub.loadX_ok hc.scr hb.s6 h6 hb.s11 hb.a7 hb.s5 hb.t0 (by omega_arith) hkw hw'
    z8 hrd hsep) fun s₁ ⟨⟨v1, top1, o1, a71, _⟩, k1⟩ => ?_)
  rw [hvd] at v1
  have p1 : wordsVal s₁.mem x.S (slot x.w 0) x.w = x.p := by
    rw [Outside.wordsVal o1 (by omega_arith) (by omega_arith), hp]
  have g5 : s₁.gpr .s5 = BitVec.ofNat 64 (8 * (x.w + 2)) := (k1.gpr (by decide)).trans hb.s5
  have g0 : s₁.gpr .t0 = BitVec.ofNat 64 x.w := (k1.gpr (by decide)).trans hb.t0
  refine WP.seq (WP.mono (zMask_ok (hc.scr.congr k1.2.2) a71 g5 g0 (by omega_arith) hw' z8
    (by rw [p1]; exact hf.1)) fun s₂ ⟨⟨a9, o2⟩, k2⟩ => ?_)
  rw [p1, v1] at a9
  have p2 : wordsVal s₂.mem x.S (slot x.w 0) x.w = x.p := by
    rw [Outside.wordsVal o2 (by omega_arith) (by omega_arith), p1]
  have v2 : wordsVal s₂.mem x.S (slot x.w 4) x.w = v := by
    rw [Outside.wordsVal o2 (by omega_arith) (by omega_arith), v1]
  have top2 : Mont.word s₂.mem x.S (slot x.w 4 + 8 * x.w) = 0 := by
    rw [Outside.word o2 (by omega_arith) (by omega_arith), top1]
  refine WP.mono (Pub.checkX_ok (hc.scr.congr (k1.trans k2).2.2) (by omega_arith) hw' z8
    ((k2.gpr (by decide)).trans a71) ((k2.gpr (by decide)).trans g5) ((k2.gpr (by decide)).trans g0) top2)
    fun t ⟨⟨t9, o3⟩, k3⟩ => ?_
  rw [p2, v2, a9, ite_ones, bmask_and] at t9
  have k13 := (k1.trans k2).trans k3
  have ar : DArr x s.mem t.mem :=
    ((darr_of o1 (by omega_arith) (by omega_arith)).trans (darr_of o2 (by omega_arith) (by omega_arith))).trans
      (darr_of o3 (by omega_arith) (by omega_arith))
  refine ⟨⟨⟨⟨hc.keep k13.2.1 k13.2.2 ar, (k13.gpr (by decide)).trans hb.s6,
      (k3.gpr (by decide)).trans ((k2.gpr (by decide)).trans a71), (k13.gpr (by decide)).trans hb.s5,
      (k13.gpr (by decide)).trans hb.t0, (k13.gpr (by decide)).trans hb.s11⟩,
      by rw [Outside.wordsVal o3 (by omega_arith) (by omega_arith), p2], hv⟩,
    by rw [Outside.wordsVal o3 (by omega_arith) (by omega_arith), v2], ?_, ar⟩, k13.mono (by decide)⟩
  rw [t9, range_dec hf.2.1]

/-! ## The header's words, and whether there is q -/

/-- A header word into a register. -/
theorem ldw_ok {s : State} {x : DD} (hc : DCtx x s) (h6 : s.gpr .s6 = x.S) (r : Reg) {d : Nat} (hd : d + 8 ≤ 256)
    (hd8 : d % 8 = 0) :
    WP isa (.block [.load .d r .s6 d]) s fun t => (t.gpr r = word s.mem x.S d ∧ t.mem = s.mem) ∧ Keep [r] s t := by
  have hZ := hc.hZ
  have h24 : 256 ≤ slot x.w 24 := by unfold slot hdrBytes; omega_arith
  have h6' : s.gpr .s6 = off x.S 0 := by rw [h6]; simp [off]
  have hst : WP isa (.block [.load .d r .s6 d]) s fun t => t = s.write r (word s.mem x.S d) := by
    brun [h6', Nat.zero_add, hc.scr.ld (d := d) (n := 8) (by omega_arith), hc.scr.al8 (d := d) (by omega_arith) hd8,
      show d < 2048 by omega_arith]
  refine WP.mono hst fun t e => ?_
  subst e
  exact ⟨⟨by simp [gpr_write], by gsimp⟩, Keep.write _ _ _⟩

theorem three_k (k : Nat) :
    (BitVec.ofNat 64 k <<< 1) + BitVec.ofNat 64 k = BitVec.ofNat 64 (3 * k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem sub_ofNat_zero {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = 0 ↔ a = b := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
    rw [show (0 : BitVec 64).toNat = 0 from rfl] at this
    omega
  · rintro rfl
    exact BitVec.sub_self _

/-- `hasQ`: `t3 = 0` exactly when `domain_len = 3 p_len`. -/
theorem hasQ_ok {x : DD} {s : State} (h : DBase x s) :
    WP isa (.block hasQ) s fun t => ((t.gpr .t3 = 0 ↔ x.L = 3 * x.k) ∧ t.mem = s.mem) ∧ Keep [.t2, .t3] s t := by
  have hc := h.ctx
  have hk' := hc.k1024
  have hL := hc.hL
  unfold hasQ
  rw [show ([.load .d .t3 .s6 8, .shift .sll .d .t2 .s11 1, .add .t2 .t2 .s11, .sub .t3 .t3 .t2] : List Instr) =
    [.load .d .t3 .s6 8] ++ [.shift .sll .d .t2 .s11 1, .add .t2 .t2 .s11, .sub .t3 .t3 .t2] from rfl,
    WP.block_append_iff]
  refine WP.mono (ldw_ok hc h.s6 .t3 (d := 8) (by decide) (by decide)) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.t2, .t3] (Q := fun t => t.gpr .t3 = s₁.gpr .t3 - BitVec.ofNat 64 (3 * x.k) ∧
    t.mem = s₁.mem) (by brun [(k1.gpr (by decide)).trans h.s11, three_k]) (by rfl) (by rfl))
    fun t ⟨⟨t3, tm⟩, kt⟩ => ⟨⟨?_, by rw [tm, m1]⟩, (k1.trans kt).mono (by decide)⟩
  rw [t3, a3, hc.hLw]
  exact sub_ofNat_zero (by rcases hL with e | e <;> omega_arith) (by omega_arith)

theorem add2 (D : Addr) (k : Nat) : D + BitVec.ofNat 64 k + BitVec.ofNat 64 k = off D (2 * k) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.two_mul]

theorem off_off (p : Addr) (a b : Nat) : off (off p a) b = off p (a + b) := off_add p a b

/-- `gPtr`: g's octets in `a6`. -/
theorem gPtr_ok {x : DD} {s : State} (h : DBase x s) :
    WP isa (.block gPtr) s fun t => (t.gpr .a6 = off x.D x.k ∧ t.mem = s.mem) ∧ Keep [.a6] s t := by
  unfold gPtr
  rw [show ([.load .d .a6 .s6 0, .add .a6 .a6 .s11] : List Instr) = [.load .d .a6 .s6 0] ++ [.add .a6 .a6 .s11]
    from rfl, WP.block_append_iff]
  refine WP.mono (ldw_ok h.ctx h.s6 .a6 (d := 0) (by decide) (by decide)) fun s₁ ⟨⟨a6, m1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.a6] (Q := fun t => t.gpr .a6 = off x.D x.k ∧ t.mem = s₁.mem)
    (by brun [(k1.gpr (by decide)).trans h.s11, a6, h.ctx.hD]) (by rfl) (by rfl))
    fun t ⟨⟨t6, tm⟩, kt⟩ => ⟨⟨t6, by rw [tm, m1]⟩, (k1.trans kt).mono (by decide)⟩

/-- `qPtrA`: q's octets in `a6`. -/
theorem qPtrA_ok {x : DD} {s : State} (h : DBase x s) :
    WP isa (.block qPtrA) s fun t => (t.gpr .a6 = off x.D (2 * x.k) ∧ t.mem = s.mem) ∧ Keep [.a6] s t := by
  unfold qPtrA
  rw [show ([.load .d .a6 .s6 0, .add .a6 .a6 .s11, .add .a6 .a6 .s11] : List Instr) =
    [.load .d .a6 .s6 0] ++ [.add .a6 .a6 .s11, .add .a6 .a6 .s11] from rfl, WP.block_append_iff]
  refine WP.mono (ldw_ok h.ctx h.s6 .a6 (d := 0) (by decide) (by decide)) fun s₁ ⟨⟨a6, m1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.a6] (Q := fun t => t.gpr .a6 = off x.D (2 * x.k) ∧ t.mem = s₁.mem)
    (by brun [(k1.gpr (by decide)).trans h.s11, a6, h.ctx.hD, add2, ← Nat.two_mul]) (by rfl) (by rfl))
    fun t ⟨⟨t6, tm⟩, kt⟩ => ⟨⟨t6, by rw [tm, m1]⟩, (k1.trans kt).mono (by decide)⟩

/-- `qPtr`: q's octets in `s9` and `p_len` in `s10`. -/
theorem qPtr_ok {x : DD} {s : State} (h : DBase x s) :
    WP isa (.block qPtr) s fun t =>
      (t.gpr .s9 = off x.D (2 * x.k) ∧ t.gpr .s10 = BitVec.ofNat 64 x.k ∧ t.mem = s.mem) ∧ Keep [.s9, .s10] s t := by
  unfold qPtr
  rw [show ([.load .d .s9 .s6 0, .add .s9 .s9 .s11, .add .s9 .s9 .s11, .addi .s10 .s11 0] : List Instr) =
    [.load .d .s9 .s6 0] ++ [.add .s9 .s9 .s11, .add .s9 .s9 .s11, .addi .s10 .s11 0] from rfl, WP.block_append_iff]
  refine WP.mono (ldw_ok h.ctx h.s6 .s9 (d := 0) (by decide) (by decide)) fun s₁ ⟨⟨a9, m1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.s9, .s10] (Q := fun t => t.gpr .s9 = off x.D (2 * x.k) ∧
    t.gpr .s10 = BitVec.ofNat 64 x.k ∧ t.mem = s₁.mem)
    (by brun [(k1.gpr (by decide)).trans h.s11, a9, h.ctx.hD, add2, BitVec.add_zero, ← Nat.two_mul]) (by rfl) (by rfl))
    fun t ⟨⟨t9, t10, tm⟩, kt⟩ => ⟨⟨t9, t10, by rw [tm, m1]⟩, (k1.trans kt).mono (by decide)⟩

/-! ## The subgroup -/

/-- Before the power: `v` in array 4, `R² mod p` in array 1, `-p⁻¹` in `t1`,
and q's octets in `s9` and `s10`. -/
def SG1 (x : DD) (v : Nat) (s : State) : Prop :=
  PV x s ∧ wordsVal s.mem x.S (slot x.w 4) x.w = v ∧
    wordsVal s.mem x.S (slot x.w 1) x.w = 2 ^ (64 * x.w) * 2 ^ (64 * x.w) % x.p ∧
    ((Mont.word s.mem x.S (slot x.w 0)).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 64 = 0 ∧
    s.gpr .s9 = off x.D (2 * x.k) ∧ s.gpr .s10 = BitVec.ofNat 64 x.k

/-- `R² mod p` and q's octets. -/
theorem sg1_ok {x : DD} {v : Nat} {s : State} (h : PV x s) (hv : wordsVal s.mem x.S (slot x.w 4) x.w = v) :
    WP isa (.seq r2 (.block qPtr)) s fun t => SG1 x v t ∧ DArr x s.mem t.mem := by
  obtain ⟨hb, hp, hv'⟩ := h
  have hc := hb.ctx
  obtain ⟨hw8, hw128, hkw, hn, hsl⟩ := dsizes hc
  have hf := VG.Proof.Bignum.valid_facts hv' hc.k64
  have e0 := (hsl 0 (by decide)).1; have e1 := (hsl 1 (by decide)).1; have e4 := (hsl 4 (by decide)).1
  have z8 := (hsl 8 (by decide)).2; have e24 := (hsl 24 (by decide)).1; have z24 := (hsl 24 (by decide)).2
  have hw' : x.w < 2 ^ 31 := by omega_arith
  unfold r2
  refine WP.seq (WP.seq ?_)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .a2) (by decide) hb.a7 hb.s5 1) fun s₁ ⟨⟨b2, m1⟩, k1⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .a5) (by decide) ((k1.gpr (by decide)).trans hb.a7)
    ((k1.gpr (by decide)).trans hb.s5) 2) fun s₂ ⟨⟨b5, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.mono (Pub.base_ok (rd := .a6) (by decide) ((k12.gpr (by decide)).trans hb.a7)
    ((k12.gpr (by decide)).trans hb.s5) 3) fun s₃ ⟨⟨b6, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  have hm3 : s₃.mem = s.mem := by rw [m3, m2, m1]
  refine WP.mono (r2t_ok (hc.scr.congr k13.2.2) ((k2.trans k3).gpr (by decide) |>.trans b2)
    ((k3.gpr (by decide)).trans b5) b6 ((k13.gpr (by decide)).trans hb.a7) ((k13.gpr (by decide)).trans hb.t0)
    (by omega_arith) hw' z8 (by rw [hm3, hp]; exact hf.2.2) (by rw [hm3, hp]; exact hf.1))
    fun s₄ ⟨⟨rr, inv, o⟩, k4⟩ => ?_
  rw [hm3, hp] at rr
  rw [hm3] at inv o
  have k14 := k13.trans k4
  have ar4 : DArr x s.mem s₄.mem := darr_of o (by omega_arith) (by omega_arith)
  have b4 : DBase x s₄ := hb.keep k14 ar4
  refine WP.mono (qPtr_ok b4) fun t ⟨⟨t9, t10, tm⟩, kt⟩ => ?_
  have art : DArr x s.mem t.mem := by rw [tm]; exact ar4
  refine ⟨⟨⟨b4.same kt tm, by rw [tm, Outside.wordsVal o (by omega_arith) (by omega_arith), hp], hv'⟩,
    by rw [tm, Outside.wordsVal o (by omega_arith) (by omega_arith), hv], by rw [tm, rr, ← Nat.pow_add]; congr 2; omega_arith,
    by rw [kt.gpr (by decide), tm, Outside.word o (by omega_arith) (by omega_arith)]; exact inv, t9, t10⟩, art⟩

/-- The power: `v^q mod p` into array 4. -/
theorem sg2_ok {x : DD} {v : Nat} {s : State} (h : SG1 x v s) (hq : x.L = 3 * x.k) :
    WP isa ModExp.powWin s fun t =>
      (PV x t ∧ wordsVal t.mem x.S (slot x.w 4) x.w = v ^ x.q % x.p) ∧ DArr x s.mem t.mem := by
  obtain ⟨⟨hb, hp, hv'⟩, h4, hrr, hinv, h9, h10⟩ := h
  have hc := hb.ctx
  obtain ⟨hw8, hw128, hkw, hn, hsl⟩ := dsizes hc
  have hf := VG.Proof.Bignum.valid_facts hv' hc.k64
  have e0 := (hsl 0 (by decide)).1; have e1 := (hsl 1 (by decide)).1; have e4 := (hsl 4 (by decide)).1
  have e24 := (hsl 24 (by decide)).1; have z24 := (hsl 24 (by decide)).2
  have hk := hc.k64
  have hk' := hc.k1024
  have hw' : x.w < 2 ^ 31 := by omega_arith
  have hrdq : ∀ i < x.k, InRegions (s.rd ++ s.wr) (off (off x.D (2 * x.k)) i) 1 := fun i hi => by
    rw [off_off]; exact hc.rdD _ (by omega_arith)
  have hsepq : ∀ i < x.k, ∀ y, ofs x.S y < x.Z → off (off x.D (2 * x.k)) i ≠ y := fun i hi => by
    rw [off_off]; exact hc.sepD _ (by omega_arith)
  have hbq : Spec.Rsa.bytesAt s.mem (off x.D (2 * x.k)) x.k = (x.db.drop (2 * x.k)).take x.k := by
    rw [← hc.bD, VG.Proof.Dsa.bytesAt_slice s.mem x.D (by omega_arith : 2 * x.k + x.k ≤ x.L)]
  refine WP.mono (Win.powWin_ok (D := off x.D (2 * x.k)) hc.scr (by omega_arith) hw' z24 hb.a7 hb.s5 hb.t0 hinv
    (by rw [hp]; omega_arith) (by rw [hp]; exact hf.1) (by rw [hrr, hp]; exact Nat.mod_lt _ (by omega_arith))
    (by rw [h9]; show _ = off (off x.D (2 * x.k)) 0; rw [off_off, Nat.add_zero]) h10 (by omega_arith) (by omega_arith) hrdq hsepq)
    fun t ⟨⟨hpow, ot⟩, kt⟩ => ?_
  have art : DArr x s.mem t.mem := darr_of ot (by omega_arith) (by omega_arith)
  refine ⟨⟨⟨hb.keep kt art, by rw [Outside.wordsVal ot (by omega_arith) (by omega_arith)]; exact hp, hv'⟩, ?_⟩, art⟩
  rw [hpow (by rw [hrr, hp]), h4, hp, hbq]

theorem one_and (c : Prop) [Decidable c] :
    BitVec.ofInt 64 1 &&& bmask (decide c) = BitVec.ofNat 64 (if c then 1 else 0) := by
  by_cases h : c
  · rw [decide_eq_true h, ite_eq_left h]; decide
  · rw [decide_eq_false h, ite_eq_right h]; decide

/-- `isOne`: `a0 :=` 1 if array 4 is 1, else 0. -/
theorem isOne_ok {x : DD} {r : Nat} {s : State} (h : PV x s) (h4 : wordsVal s.mem x.S (slot x.w 4) x.w = r) :
    WP isa isOne s fun t =>
      (DBase x t ∧ t.gpr .a0 = BitVec.ofNat 64 (if r = 1 then 1 else 0)) ∧ DArr x s.mem t.mem := by
  obtain ⟨hb, hp, hv'⟩ := h
  have hc := hb.ctx
  obtain ⟨hw8, hw128, hkw, hn, hsl⟩ := dsizes hc
  have e4 := (hsl 4 (by decide)).1; have e7 := (hsl 7 (by decide)).1; have e8 := (hsl 8 (by decide)).1
  have z8 := (hsl 8 (by decide)).2
  have hw' : x.w < 2 ^ 31 := by omega_arith
  unfold isOne
  refine WP.seq (WP.mono (Pub.oneP_ok hc.scr (by omega_arith) hw' z8 hb.a7 hb.s5 hb.t0) fun s₁ ⟨⟨v7, o1⟩, k1⟩ => ?_)
  have ar1 : DArr x s.mem s₁.mem := darr_of o1 (by omega_arith) (by omega_arith)
  have b1 : DBase x s₁ := hb.keep k1 ar1
  refine WP.seq (WP.mono (WP.keep [.s4] (Q := fun u => u.gpr .s4 = BitVec.allOnes 64 ∧ u.mem = s₁.mem)
    (by brun [li_m1]) (by rfl) (by rfl)) fun s₂ ⟨⟨a4, m2⟩, k2⟩ => ?_)
  have b2 : DBase x s₂ := b1.same k2 m2
  refine WP.seq (WP.mono (eqMask_ok (j := 4) (k := 7) b2.ctx.scr b2.a7 b2.s5 b2.t0 (by omega_arith) hw'
    (by omega_arith) (by omega_arith)) fun s₃ ⟨⟨c4, m3⟩, k3⟩ => ?_)
  have b3 : DBase x s₃ := b2.same k3 m3 (by decide)
  refine WP.mono (WP.keep [.a0] (Q := fun t => t.gpr .a0 = BitVec.ofInt 64 1 &&& s₃.gpr .s4 ∧ t.mem = s₃.mem)
    (by brun [exec_li]) (by rfl) (by rfl)) fun t ⟨⟨t0, tm⟩, kt⟩ => ?_
  refine ⟨⟨b3.same kt tm, ?_⟩, by rw [tm, m3, m2]; exact ar1⟩
  have v7' : wordsVal s₁.mem x.S (slot x.w 7) x.w = 1 := v7
  rw [t0, c4, a4, ones_and, m2, v7', Outside.wordsVal o1 (by omega_arith) (by omega_arith), h4, one_and]

/-- `subgroup`: `a0 :=` 1 if `v^q mod p = 1` for `v` in array 4, else 0. -/
theorem subgroup_ok {x : DD} {v : Nat} {s : State} (h : PV x s) (hv : wordsVal s.mem x.S (slot x.w 4) x.w = v)
    (hq : x.L = 3 * x.k) :
    WP isa subgroup s fun t =>
      (DBase x t ∧ t.gpr .a0 = BitVec.ofNat 64 (if v ^ x.q % x.p = 1 then 1 else 0)) ∧ DArr x s.mem t.mem := by
  unfold subgroup
  exact WP.seq (WP.mono (sg1_ok h hv) fun s₁ ⟨h1, a1⟩ => WP.seq (WP.mono (sg2_ok h1 hq) fun s₂ ⟨h2, a2⟩ =>
    WP.mono (isOne_ok h2.1 h2.2) fun t ⟨ht, a3⟩ => ⟨ht, a1.trans (a2.trans a3)⟩))

/-! ## The values' octets and ranges -/

theorem dbytes_g {x : DD} {s : State} (hc : DCtx x s) :
    Spec.Rsa.bytesAt s.mem (off x.D x.k) x.k = (x.db.drop x.k).take x.k := by
  rw [← hc.bD, VG.Proof.Dsa.bytesAt_slice s.mem x.D (by rcases hc.hL with h | h <;> omega_arith : x.k + x.k ≤ x.L)]

theorem dbytes_q {x : DD} {s : State} (hc : DCtx x s) (hq : x.L = 3 * x.k) :
    Spec.Rsa.bytesAt s.mem (off x.D (2 * x.k)) x.k = (x.db.drop (2 * x.k)).take x.k := by
  rw [← hc.bD, VG.Proof.Dsa.bytesAt_slice s.mem x.D (by omega_arith : 2 * x.k + x.k ≤ x.L)]

/-- After `range`: `v` in array 4, and `s9` the mask of `1 < v < p − 1`. -/
def RG (x : DD) (v : Nat) (s : State) : Prop :=
  PV x s ∧ wordsVal s.mem x.S (slot x.w 4) x.w = v ∧ s.gpr .s9 = bmask (decide (1 < v ∧ v < x.p - 1))

theorem range_at {x : DD} {s : State} {P : Addr} {bs : List Byte} (h : PV x s) (h6 : s.gpr .a6 = P)
    (hrd : ∀ i < x.k, InRegions (s.rd ++ s.wr) (off P i) 1)
    (hsep : ∀ i < x.k, ∀ y, ofs x.S y < x.Z → off P i ≠ y) (hb : Spec.Rsa.bytesAt s.mem P x.k = bs) :
    WP isa range s fun t => (RG x (Spec.Rsa.os2ip bs) t ∧ DArr x s.mem t.mem) ∧ Keep rangeRegs s t :=
  WP.mono (range_ok h h6 hrd hsep) fun _ ⟨⟨a, b, c, d⟩, k⟩ => ⟨⟨⟨a, by rw [b, hb], by rw [c, hb]⟩, d⟩, k⟩

/-- `range` on g. -/
theorem range_g {x : DD} {s : State} (h : PV x s) (h6 : s.gpr .a6 = off x.D x.k) :
    WP isa range s fun t => (RG x x.g t ∧ DArr x s.mem t.mem) ∧ Keep rangeRegs s t :=
  have hc := h.1.ctx
  range_at h h6 (fun i hi => by rw [off_off]; exact hc.rdD _ (by rcases hc.hL with e | e <;> omega_arith))
    (fun i hi => by rw [off_off]; exact hc.sepD _ (by rcases hc.hL with e | e <;> omega_arith)) (dbytes_g hc)

/-- `range` on q. -/
theorem range_q {x : DD} {s : State} (h : PV x s) (hq : x.L = 3 * x.k) (h6 : s.gpr .a6 = off x.D (2 * x.k)) :
    WP isa range s fun t => (RG x x.q t ∧ DArr x s.mem t.mem) ∧ Keep rangeRegs s t :=
  have hc := h.1.ctx
  range_at h h6 (fun i hi => by rw [off_off]; exact hc.rdD _ (by omega_arith))
    (fun i hi => by rw [off_off]; exact hc.sepD _ (by omega_arith)) (dbytes_q hc hq)

/-! ## q odd -/

theorem neg_low (v : BitVec 64) :
    BitVec.ofNat 64 0 - (v &&& BitVec.ofInt 64 1) = bmask (decide (v.toNat % 2 = 1)) := by
  have e : v &&& BitVec.ofInt 64 1 = BitVec.ofNat 64 (v.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat]
    show v.toNat &&& 1 = v.toNat % 2 % 2 ^ 64
    rw [Nat.and_one_is_mod]; omega
  rw [e]
  rcases Nat.mod_two_eq_zero_or_one v.toNat with h | h <;> rw [h] <;> decide

/-- `qOdd`: `s9 &=` the mask of q (array 4) being odd. -/
theorem qOdd_ok {x : DD} {u : Nat} {c : Bool} {s : State} (h : PV x s)
    (h4 : wordsVal s.mem x.S (slot x.w 4) x.w = u) (h9 : s.gpr .s9 = bmask c) :
    WP isa (.block qOdd) s fun t => (t.gpr .s9 = bmask (c && decide (u % 2 = 1)) ∧ t.mem = s.mem) ∧
      Keep [.t3, .t4, .t5, .s9] s t := by
  have hb := h.1
  have hc := hb.ctx
  obtain ⟨hw8, hw128, hkw, hn, hsl⟩ := dsizes hc
  have e4 := (hsl 4 (by decide)).1; have e8 := (hsl 8 (by decide)).1; have z8 := (hsl 8 (by decide)).2
  unfold qOdd
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .t3) (by decide) hb.a7 hb.s5 4) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.t4, .t5, .s9] (Q := fun t => t.gpr .s9 = s₁.gpr .s9 &&&
      (BitVec.ofNat 64 0 - (Mont.word s₁.mem x.S (slot x.w 4) &&& BitVec.ofInt 64 1)) ∧ t.mem = s₁.mem)
    (by brun [a3, BitVec.add_zero, (hc.scr.congr k1.2.2).ld (d := slot x.w 4) (n := 8) (by omega_arith),
      (hc.scr.congr k1.2.2).al8 (d := slot x.w 4) (by omega_arith) (slot_al _ 4), exec_li,
      exec_logicImm (show imm12 1 by decide)]) (by rfl) (by rfl)) fun t ⟨⟨t9, tm⟩, kt⟩ =>
    ⟨⟨?_, by rw [tm, m1]⟩, (k1.trans kt).mono (by decide)⟩
  rw [t9, neg_low, m1, ← Pub.wsv_low s.mem x.S (slot x.w 4) (w := x.w) (by omega_arith), h4, k1.gpr (by decide), h9, bmask_and]

/-! ## `p mod q` -/

/-- What `vg_ffdh_check_domain` knows before `qDiv`. -/
def QF (x : DD) : Prop := Spec.Rsa.modulusValid x.p x.k = true ∧ 0 < x.q ∧ x.L = 3 * x.k

/-- Before q's load. -/
def QA (x : DD) (s : State) : Prop :=
  QF x ∧ DBase x s ∧ s.gpr .s7 = off x.D (2 * x.k) ∧ s.gpr .s8 = BitVec.ofNat 64 x.k

/-- q in array 0. -/
def QB (x : DD) (s : State) : Prop := QF x ∧ DBase x s ∧ wordsVal s.mem x.S (slot x.w 0) x.w = x.q

/-- And p's octets in `s9` and `s10`. -/
def QC (x : DD) (s : State) : Prop := QB x s ∧ s.gpr .s9 = off x.D 0 ∧ s.gpr .s10 = BitVec.ofNat 64 x.k

/-- The mask of `p mod q = 1` in `s10`, before p's load. -/
def QD (x : DD) (s : State) : Prop := QF x ∧ P1 x s ∧ s.gpr .s10 = bmask (decide (x.p % x.q = 1))

/-- After `qDiv`. -/
def QE (x : DD) (s : State) : Prop := PV x s ∧ s.gpr .s10 = bmask (decide (x.p % x.q = 1))

theorem qdA_ok {x : DD} {s : State} (hf : QF x) (h : DBase x s) :
    WP isa (.block [.load .d .s7 .s6 0, .add .s7 .s7 .s11, .add .s7 .s7 .s11, .addi .s8 .s11 0]) s fun t =>
      QA x t ∧ DArr x s.mem t.mem := by
  rw [show ([.load .d .s7 .s6 0, .add .s7 .s7 .s11, .add .s7 .s7 .s11, .addi .s8 .s11 0] : List Instr) =
    [.load .d .s7 .s6 0] ++ [.add .s7 .s7 .s11, .add .s7 .s7 .s11, .addi .s8 .s11 0] from rfl, WP.block_append_iff]
  refine WP.mono (ldw_ok h.ctx h.s6 .s7 (d := 0) (by decide) (by decide)) fun s₁ ⟨⟨a7, m1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.s7, .s8] (Q := fun t => t.gpr .s7 = off x.D (2 * x.k) ∧
    t.gpr .s8 = BitVec.ofNat 64 x.k ∧ t.mem = s₁.mem)
    (by brun [(k1.gpr (by decide)).trans h.s11, a7, h.ctx.hD, add2, BitVec.add_zero, ← Nat.two_mul]) (by rfl) (by rfl))
    fun t ⟨⟨t7, t8, tm⟩, kt⟩ => ?_
  have hm : t.mem = s.mem := by rw [tm, m1]
  exact ⟨⟨hf, h.same (k1.trans kt) hm, t7, t8⟩, by rw [hm]; exact DArr.refl _ _⟩

theorem qdB_ok {x : DD} {s : State} (h : QA x s) :
    WP isa Precompute.loadN s fun t => QB x t ∧ DArr x s.mem t.mem := by
  obtain ⟨hf, hb, h7, h8⟩ := h
  have hc := hb.ctx
  obtain ⟨hw8, hw128, hkw, hn, hsl⟩ := dsizes hc
  have e0 := (hsl 0 (by decide)).1; have e24 := (hsl 24 (by decide)).1; have z24 := (hsl 24 (by decide)).2
  have hk := hc.k64
  have hq := hf.2.2
  refine WP.mono (loadN_ok (dA := slot x.w 0) (N := off x.D (2 * x.k)) hc.scr hb.a7
    (by rw [h7]; show _ = off (off x.D (2 * x.k)) 0; rw [off_off, Nat.add_zero]) h8 hb.t0 (by omega_arith) hkw
    (by omega_arith) (by omega_arith) (slot_al _ 0) (by omega_arith)
    (fun i hi => by rw [off_off]; exact hc.rdD _ (by omega_arith))
    (fun i hi => by rw [off_off]; exact hc.sepD _ (by omega_arith))) fun t ⟨hv, out, k⟩ => ?_
  have hm : DArr x s.mem t.mem := out.mono (by omega_arith) (by omega_arith)
  exact ⟨⟨hf, hb.keep k hm, by rw [hv, dbytes_q hc hq]⟩, hm⟩

theorem qdC_ok {x : DD} {s : State} (h : QB x s) :
    WP isa (.block [.load .d .s9 .s6 0, .addi .s10 .s11 0]) s fun t => QC x t ∧ DArr x s.mem t.mem := by
  obtain ⟨hf, hb, hq⟩ := h
  rw [show ([.load .d .s9 .s6 0, .addi .s10 .s11 0] : List Instr) = [.load .d .s9 .s6 0] ++ [.addi .s10 .s11 0]
    from rfl, WP.block_append_iff]
  refine WP.mono (ldw_ok hb.ctx hb.s6 .s9 (d := 0) (by decide) (by decide)) fun s₁ ⟨⟨a9, m1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.s10] (Q := fun t => t.gpr .s10 = BitVec.ofNat 64 x.k ∧ t.mem = s₁.mem)
    (by brun [(k1.gpr (by decide)).trans hb.s11, BitVec.add_zero]) (by rfl) (by rfl)) fun t ⟨⟨t10, tm⟩, kt⟩ => ?_
  have hm : t.mem = s.mem := by rw [tm, m1]
  refine ⟨⟨⟨hf, hb.same (k1.trans kt) hm, by rw [hm]; exact hq⟩, ?_, t10⟩, by rw [hm]; exact DArr.refl _ _⟩
  rw [kt.gpr (by decide), a9, hb.ctx.hD]; exact (BitVec.add_zero _).symm

theorem qdD_ok {x : DD} {s : State} (h : QC x s) :
    WP isa qMask s fun t => QD x t ∧ DArr x s.mem t.mem := by
  obtain ⟨⟨hf, hb, hq⟩, h9, h10⟩ := h
  have hc := hb.ctx
  obtain ⟨hw8, hw128, hkw, hn, hsl⟩ := dsizes hc
  have e0 := (hsl 0 (by decide)).1; have e1 := (hsl 1 (by decide)).1; have e4 := (hsl 4 (by decide)).1
  have e7 := (hsl 7 (by decide)).1; have e8 := (hsl 8 (by decide)).1; have z8 := (hsl 8 (by decide)).2
  have hk := hc.k64
  have hk' := hc.k1024
  have hL := hc.hL
  have hw' : x.w < 2 ^ 31 := by omega_arith
  unfold qMask
  refine WP.seq (WP.mono (ModArith.reduce64_ok (D := x.D) (L := x.k) hc.scr (by omega_arith) hw' (by omega_arith) hb.a7 hb.s5
    hb.t0 (by rw [hq]; exact hf.2.1) h9 h10 (by omega_arith) (by omega_arith)
    (fun i hi => hc.rdD i (by rcases hL with e | e <;> omega_arith))
    (fun i hi => hc.sepD i (by rcases hL with e | e <;> omega_arith))) fun s₁ ⟨⟨r1, o1⟩, k1⟩ => ?_)
  rw [hq, dbytes_p hc] at r1
  have ar1 : DArr x s.mem s₁.mem := darr_of o1 (by omega_arith) (by omega_arith)
  have b1 : DBase x s₁ := hb.keep k1 ar1
  refine WP.seq (WP.mono (Pub.oneP_ok b1.ctx.scr (by omega_arith) hw' z8 b1.a7 b1.s5 b1.t0) fun s₂ ⟨⟨v7, o2⟩, k2⟩ => ?_)
  have ar2 : DArr x s₁.mem s₂.mem := darr_of o2 (by omega_arith) (by omega_arith)
  have b2 : DBase x s₂ := b1.keep k2 ar2
  refine WP.seq (WP.mono (WP.keep [.s4] (Q := fun u => u.gpr .s4 = BitVec.allOnes 64 ∧ u.mem = s₂.mem)
    (by brun [li_m1]) (by rfl) (by rfl)) fun s₃ ⟨⟨a4, m3⟩, k3⟩ => ?_)
  have b3 : DBase x s₃ := b2.same k3 m3
  refine WP.seq (WP.mono (eqMask_ok (j := 1) (k := 7) b3.ctx.scr b3.a7 b3.s5 b3.t0 (by omega_arith) hw'
    (by omega_arith) (by omega_arith)) fun s₄ ⟨⟨c4, m4⟩, k4⟩ => ?_)
  have b4 : DBase x s₄ := b3.same k4 m4 (by decide)
  rw [show ([.addi .s10 .s4 0, .load .d .s7 .s6 0, .addi .s8 .s11 0] : List Instr) =
    [.addi .s10 .s4 0] ++ [.load .d .s7 .s6 0] ++ [.addi .s8 .s11 0] from rfl, WP.block_append_iff,
    WP.block_append_iff]
  refine WP.mono (WP.keep [.s10] (Q := fun u => u.gpr .s10 = s₄.gpr .s4 ∧ u.mem = s₄.mem)
    (by brun [BitVec.add_zero]) (by rfl) (by rfl)) fun s₅ ⟨⟨a10, m5⟩, k5⟩ => ?_
  have b5 : DBase x s₅ := b4.same k5 m5
  refine WP.mono (ldw_ok b5.ctx b5.s6 .s7 (d := 0) (by decide) (by decide)) fun s₆ ⟨⟨a7, m6⟩, k6⟩ => ?_
  have b6 : DBase x s₆ := b5.same k6 m6
  refine WP.mono (WP.keep [.s8] (Q := fun u => u.gpr .s8 = BitVec.ofNat 64 x.k ∧ u.mem = s₆.mem)
    (by brun [b6.s11, BitVec.add_zero]) (by rfl) (by rfl)) fun t ⟨⟨t8, tm⟩, kt⟩ => ?_
  have v7' : wordsVal s₂.mem x.S (slot x.w 7) x.w = 1 := v7
  have hm : t.mem = s₂.mem := by rw [tm, m6, m5, m4, m3]
  refine ⟨⟨hf, ⟨b6.same kt tm, ?_, t8⟩, ?_⟩, by rw [hm]; exact ar1.trans ar2⟩
  · rw [kt.gpr (by decide), a7, b5.ctx.hD]; exact (BitVec.add_zero _).symm
  · rw [kt.gpr (by decide), k6.gpr (by decide), a10, c4, a4, ones_and, m3, v7',
      Outside.wordsVal o2 (by omega_arith) (by omega_arith), r1]

theorem qdE_ok {x : DD} {s : State} (h : QD x s) :
    WP isa Precompute.loadN s fun t => QE x t ∧ DArr x s.mem t.mem :=
  WP.mono (loadN_P h.2.1) fun _ ⟨⟨hb, hp, _, _⟩, ar, k⟩ => ⟨⟨⟨hb, hp, h.1.1⟩, by rw [k.gpr (by decide)]; exact h.2.2⟩, ar⟩

/-- `qDiv`: `s10 :=` the mask of `p mod q = 1`, p back in array 0. -/
theorem qDiv_ok {x : DD} {s : State} (h : PV x s) (hf : QF x) :
    WP isa qDiv s fun t => QE x t ∧ DArr x s.mem t.mem := by
  unfold qDiv
  exact WP.seq (WP.mono (qdA_ok hf h.1) fun _ ⟨ha, a1⟩ => WP.seq (WP.mono (qdB_ok ha) fun _ ⟨hb, a2⟩ =>
    WP.seq (WP.mono (qdC_ok hb) fun _ ⟨hc, a3⟩ => WP.seq (WP.mono (qdD_ok hc) fun _ ⟨hd, a4⟩ =>
      WP.mono (qdE_ok hd) fun _ ⟨he, a5⟩ => ⟨he, a1.trans (a2.trans (a3.trans (a4.trans a5)))⟩))))

/-! ## The front -/

/-- The working space's address into `t0` and the callee-saved registers
saved there: only its header's words 16–27 change. -/
theorem pre_ok (rS : Reg) {s : State} {S : Addr} {Z : Nat} (hS : s.gpr rS = S) (hs : Scr s S Z) (hZ : 256 ≤ Z) :
    WP isa (.block (([.addi .t0 rS 0] : List Instr) ++ PublicChecked.saveRegs)) s fun t =>
      t.gpr .s6 = S ∧ (∀ i < 12, t.mem.readW (off (Pub.savW S) (8 * i)) 64 = s.gpr (PublicChecked.saved i)) ∧
        Keep [.t0, .s6] s t ∧ Outside S 0 256 s.mem t.mem := by
  have hn := hs.nowrap
  refine WP.block_append (WP.mono (WP.keep [.t0] (Q := fun t => t.gpr .t0 = S ∧ t.mem = s.mem)
    (by brun [hS, BitVec.add_zero]) (by rfl) (by rfl)) fun s₁ ⟨⟨a0, m1⟩, k1⟩ => ?_)
  have e : ∀ i, off (Pub.savW S) (8 * i) = off S (128 + 8 * i) := fun i => by rw [off, off, Offset.add_add]
  have hin : ∀ i < 12, InRegions s₁.wr (off (Pub.savW (s₁.gpr .t0)) (8 * i)) 8 := fun i hi => by
    rw [a0, e]; exact (hs.congr k1.2.2).st (by omega_arith)
  refine WP.mono (Pub.save_ok s₁ hin (fun i hi => by rw [a0]; exact Pub.sav_al hs.al (by omega_arith) hi))
    fun t hS => ⟨hS.s6.trans a0, fun i hi => ?_, (k1.trans hS.keep).mono (by decide), fun y hy => ?_⟩
  · rw [← a0, hS.saved i hi, k1.gpr fun h => Pub.saved_ne_t0 i hi (List.mem_singleton.mp h)]
  · rw [← m1]
    refine hS.frame y fun r hr hc => ?_
    rw [List.mem_singleton] at hr
    subst hr
    rw [a0] at hc
    have hc' := (Offset.sub_base (n := 96) (k := 256) S (d := 128) (by omega_arith)) _ hc
    simp only [Region.Contains] at hc'
    simp only [ofs] at hy
    omega_arith

/-- A register into the header's word at `d`. -/
theorem sth_ok {s : State} {S : Addr} {Z : Nat} (hs : Scr s S Z) (hZ : 128 ≤ Z) (h6 : s.gpr .s6 = S) (r : Reg)
    {d : Nat} (hd : d + 8 ≤ 128) (hd8 : d % 8 = 0) :
    WP isa (.block [.store .d r .s6 d]) s fun t =>
      (word t.mem S d = s.gpr r ∧ Outside S d 8 s.mem t.mem) ∧ Keep [] s t := by
  have hn := hs.nowrap
  have h6' : s.gpr .s6 = off S 0 := by rw [h6]; simp [off]
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW (off S d) (s.gpr r))
    (by brun [h6', Nat.zero_add, hs.st (d := d) (n := 8) (by omega_arith), hs.al8 (d := d) (by omega_arith) hd8,
      show d < 2048 by omega_arith]) (by rfl) (by rfl)) fun t ⟨tm, kt⟩ =>
    ⟨⟨by rw [tm]; exact word_writeW_self _ _ _ _, by rw [tm]; exact writeW_outside _ _ _ (by omega_arith)⟩, kt⟩

/-- `args` and `setup`. -/
theorem tail_ok {s : State} {S : Addr} {k : Nat} (h6 : s.gpr .s6 = S) (h2 : s.gpr .a2 = BitVec.ofNat 64 k)
    (hk' : k ≤ 1024) :
    WP isa (.block (args ++ PublicChecked.setup)) s fun t =>
      (t.gpr .s7 = s.gpr .a0 ∧ t.gpr .s8 = BitVec.ofNat 64 k ∧ t.gpr .s11 = BitVec.ofNat 64 k ∧
        t.gpr .t0 = BitVec.ofNat 64 ((k + 7) / 8) ∧ t.gpr .s5 = BitVec.ofNat 64 (8 * ((k + 7) / 8) + 16) ∧
        t.gpr .a7 = off S (slot ((k + 7) / 8) 0) ∧ t.gpr .s6 = S ∧ t.mem = s.mem) ∧
      Keep [.s7, .s8, .a1, .a7, .s5, .s10, .s11, .t0] s t := by
  refine WP.block_append (WP.mono (WP.keep [.s7, .s8, .a1] (Q := fun t => t.gpr .s7 = s.gpr .a0 ∧
    t.gpr .s8 = BitVec.ofNat 64 k ∧ t.gpr .a1 = BitVec.ofNat 64 k ∧ t.mem = s.mem)
    (by unfold args; brun [h2, BitVec.add_zero]) (by rfl) (by rfl)) fun s₁ ⟨⟨a7, a8, a1, m1⟩, k1⟩ => ?_)
  refine WP.mono (Pub.setup_ok (O := s₁.gpr .a0) rfl a1 ((k1.gpr (by decide)).trans h6) hk')
    fun t ⟨⟨_, t11, t0, t5, t7, tm⟩, kt⟩ => ⟨⟨by rw [kt.gpr (by decide), a7], by rw [kt.gpr (by decide), a8], t11,
      t0, t5, t7, by rw [kt.gpr (by decide), k1.gpr (by decide), h6], by rw [tm, m1]⟩, (k1.trans kt).mono (by decide)⟩

/-! ## Results and the restore -/

/-- `a0 := 0`, for a condition that fails. -/
theorem fail_ok {x : DD} {s : State} (h : DBase x s) {c : Prop} [Decidable c] (hc : ¬c) :
    WP isa (.block [.li .a0 0]) s fun t =>
      (DBase x t ∧ t.gpr .a0 = BitVec.ofNat 64 (if c then 1 else 0)) ∧ DArr x s.mem t.mem :=
  WP.mono (WP.keep [.a0] (Q := fun t => t.gpr .a0 = 0 ∧ t.mem = s.mem) (by brun [exec_li]; rfl) (by rfl) (by rfl))
    fun t ⟨⟨t0, tm⟩, kt⟩ => ⟨⟨h.same kt tm, by rw [t0, ite_eq_right hc]; rfl⟩, by rw [tm]; exact DArr.refl _ _⟩

theorem bmask_beq (b : Bool) : (bmask b == 0) = !b := by cases b <;> decide

theorem not_and_of {a b : Prop} [Decidable a] [Decidable b] (h : (!(decide a && decide b)) = true) : ¬(a ∧ b) :=
  fun hab => by simp [hab.1, hab.2] at h

/-- `a0 := s9 & 1`, for `s9` a mask. -/
theorem retMask_ok {x : DD} {s : State} (h : DBase x s) {c : Prop} [Decidable c]
    (h9 : s.gpr .s9 = bmask (decide c)) :
    WP isa (.block [.li .a0 1, .logic .and .a0 .a0 .s9]) s fun t =>
      (DBase x t ∧ t.gpr .a0 = BitVec.ofNat 64 (if c then 1 else 0)) ∧ DArr x s.mem t.mem :=
  WP.mono (WP.keep [.a0] (Q := fun t => t.gpr .a0 = BitVec.ofInt 64 1 &&& s.gpr .s9 ∧ t.mem = s.mem)
    (by brun [exec_li]) (by rfl) (by rfl))
    fun t ⟨⟨t0, tm⟩, kt⟩ => ⟨⟨h.same kt tm, by rw [t0, h9, one_and]⟩, by rw [tm]; exact DArr.refl _ _⟩

theorem ofNat_toNat' (v : BitVec 64) : BitVec.ofNat 64 v.toNat = v := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem dpres_saved : ∀ r ∈ preserved, ∃ i < 12, r = PublicChecked.saved i := by decide

/-- Every register but `ra`. -/
def dNotRa : List Reg :=
  [.t0, .t1, .t2, .s0, .s1, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10,
    .s11, .t3, .t4, .t5, .t6]

theorem ret_bv32 (c : Prop) [Decidable c] :
    ((BitVec.ofNat 64 (if c then 1 else 0)).setWidth 32).toNat = if c then 1 else 0 := by
  split <;> rfl

/-- `restore`, the arrays changed since the front. -/
theorem dRestore_ok {x : DD} {s₀ t : State} (h : DBase x t)
    (hsv : ∀ i < 12, word t.mem x.S (128 + 8 * i) = s₀.gpr (PublicChecked.saved i)) :
    WP isa (.block PublicChecked.restore) t fun u =>
      (∀ r ∈ preserved, u.gpr r = s₀.gpr r) ∧ u.gpr .a0 = t.gpr .a0 := by
  have hc := h.ctx
  have hn := hc.scr.nowrap
  have hZ := hc.hZ
  have h24 : 256 ≤ slot x.w 24 := by unfold slot hdrBytes; omega_arith
  have e : ∀ i, off (Pub.savW x.S) (8 * i) = off x.S (128 + 8 * i) := fun i => by rw [off, off, Offset.add_add]
  refine WP.mono (Pub.restore_ok t (S := x.S) (v := fun i => s₀.gpr (PublicChecked.saved i)) h.s6
    (fun i hi => by show InRegions t.wr (off (Pub.savW x.S) (8 * i)) 8; rw [e]; exact hc.scr.st (by omega_arith))
    (fun i hi => Pub.sav_al hc.scr.al (by omega_arith) hi)
    (fun i hi => by show t.mem.readW (off (Pub.savW x.S) (8 * i)) 64 = _; rw [e]; exact hsv i hi))
    fun u ⟨urs, uot, _, _, _, _⟩ => ⟨fun r hr => ?_, uot .a0 (by decide)⟩
  obtain ⟨i, hi, rfl⟩ := dpres_saved r hr
  exact urs i hi

theorem beq_mask {s : State} {c : Bool} (h : s.gpr .s9 = bmask c) : (s.gpr .s9 == 0) = !c := by
  rw [h, bmask_beq]

end VG.Proof.Ffdh.RISCV64.Domain

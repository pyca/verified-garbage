module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.Body
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCheck
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubPower
import VerifiedGarbage.Proof.Bignum.PPC64LE.ModArithReduce
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCore
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicFn

/-!
# FFDH's domain check on PPC64LE: q's checks and g's

In the working space of `Body.lean`, p in array 0: `qOdd_ok`, the mask of q
being odd from its last octet; `qDiv_ok`, the mask of `p mod q = 1` (q in
array 0, p's octets reduced modulo q, then p back in array 0).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Domain

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain
open VG.Proof.Bignum (slot slot_sep bytesAt_length)

theorem os2ip_odd (m : Mem) (P : Addr) {k : Nat} (hk : 1 ≤ k) :
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt m P k) % 2 = (m (off P (k - 1))).toNat % 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega_arith⟩
  have e : Spec.Rsa.bytesAt m P (j + 1) = Spec.Rsa.bytesAt m P j ++ [m (off P j)] := by
    simp [Spec.Rsa.bytesAt, List.range_succ, off]
  rw [e, VG.Proof.Rsa.os2ip_snoc, Nat.add_sub_cancel]
  omega_arith

theorem odd_mask (x : Nat) :
    BitVec.ofNat 64 0 - (BitVec.ofNat 64 x &&& BitVec.ofNat 64 1) = mask (decide (x % 2 = 1)) := by
  have e : BitVec.ofNat 64 x &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 (x % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (BitVec.ofNat 64 1).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    simp only [BitVec.toNat_ofNat]
    omega_arith
  rw [e]
  rcases (show x % 2 = 0 ∨ x % 2 = 1 by omega_arith) with h | h <;> rw [h] <;> decide

theorem mask_and' (p q : Bool) : mask p &&& mask q = mask (p && q) := by cases p <;> cases q <;> rfl

/-- `qOdd`: `r26 &=` the mask of q (`k` octets at `D + 2 k`) being odd. -/
theorem qOdd_ok {s : State} {D : Addr} {k : Nat} {b : Bool} (h21 : s.gpr .r21 = D)
    (h28 : s.gpr .r28 = BitVec.ofNat 64 k) (h26 : s.gpr .r26 = mask b) (hk : 1 ≤ k) (hk' : k ≤ 1024)
    (hrd : InRegions (s.rd ++ s.wr) (off D (3 * k - 1)) 1) :
    WP isa (.block qOdd) s fun t =>
      (t.gpr .r26 = mask (b && decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D (2 * k)) k) % 2 = 1)) ∧
        t.mem = s.mem) ∧ Keep [.r0, .r3, .r16, .r26] s t := by
  refine WP.keep _ ?_ (by decide)
  have ea : BitVec.ofNat 64 (2 * k) + BitVec.ofNat 64 k + D - BitVec.ofNat 64 1 = off D (3 * k - 1) := by
    have e1 := off_sub1 D (show 1 ≤ 2 * k + k by omega_arith)
    rw [BitVec.add_comm _ D, ← BitVec.add_assoc, Offset.add_add]
    exact e1.trans (by rw [show 2 * k + k - 1 = 3 * k - 1 by omega_arith])
  have hodd := os2ip_odd s.mem (off D (2 * k)) hk
  rw [off_off', show 2 * k + (k - 1) = 3 * k - 1 by omega_arith] at hodd
  unfold qOdd
  prun [h21, h28, h26, shl1_ofNat, ea, hrd, read_byte64,
    exec_lbz' (show Reg.r16 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide), BitVec.add_zero, odd_mask, mask_and', hodd]

/-- Loading `k` octets at `r12` into array 0, within `Env`. -/
theorem loadA0_ok {s : State} {B N : Addr} {Z w k : Nat} (h : Env s B Z w) (h12 : s.gpr .r12 = off N 0)
    (h6 : s.gpr .r6 = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hkw : k ≤ 8 * w)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off N i) 1) (hsep : ∀ i < k, ∀ x, ofs B x < Z → off N i ≠ x) :
    WP isa Precompute.loadN s fun t =>
      (arr t.mem B w 0 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem N k) ∧ Body B w s.mem t.mem) ∧
        Keep [.r0, .r14, .r15, .r16, .r17] s t := by
  have hZ := h.hZ
  have hw' := h.hw'
  have e0 := slot_eq w 0; have e28 := slot_eq w 28
  refine WP.mono (loadN_ok (dA := slot w 0) h.hs h.h10 h12 h6 h.h11 hk hkw (by omega_arith) (by omega_arith) (by omega_arith) hrd hsep)
    fun t ⟨hv, out, k⟩ => ⟨⟨hv, Body.of out (Nat.le_refl _) (by omega_arith)⟩, k⟩

/-- `reloadP`: p's `k` octets (at `r21`) into array 0. -/
theorem reloadP_ok {s : State} {B D : Addr} {Z w k : Nat} (h : Env s B Z w) (h21 : s.gpr .r21 = D)
    (h28 : s.gpr .r28 = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hkw : k ≤ 8 * w)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off D i) 1) (hsep : ∀ i < k, ∀ x, ofs B x < Z → off D i ≠ x) :
    WP isa reloadP s fun t =>
      (arr t.mem B w 0 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D k) ∧ Body B w s.mem t.mem) ∧
        Keep [.r0, .r6, .r12, .r14, .r15, .r16, .r17] s t := by
  unfold reloadP
  refine WP.seq (WP.mono (WP.keep [.r6, .r12] (Q := fun t => t.gpr .r12 = off D 0 ∧
    t.gpr .r6 = BitVec.ofNat 64 k ∧ t.mem = s.mem) (by prun [h21, h28, BitVec.add_zero]) (by decide))
    fun s₁ ⟨⟨a12, a6, m1⟩, k1⟩ => ?_)
  refine WP.mono (loadA0_ok (h.keep k1 (by decide)) a12 a6 hk hkw (by rw [k1.rd, k1.wr]; exact hrd) hsep)
    fun t ⟨⟨hv, b⟩, k⟩ => ⟨⟨by rw [hv, m1], by rw [← m1]; exact b⟩, (k1.trans k).mono (by decide)⟩

/-- The registers `qDiv` writes. -/
def qDivRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r8, .r9, .r12, .r14, .r15, .r16, .r17, .r20, .r24, .r25, .r30, .r31]

/-- `qDiv`: `r25 :=` the mask of `p mod q = 1` (p's `k` octets at `D`, q's
at `D + 2 k`), and p back in array 0. -/
theorem qDiv_ok {s : State} {B D : Addr} {Z w k : Nat} (h : Env s B Z w) (h23 : s.gpr .r23 = B)
    (h21 : s.gpr .r21 = D) (h28 : s.gpr .r28 = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hkw : k ≤ 8 * w)
    (hrd : ∀ i < 3 * k, InRegions (s.rd ++ s.wr) (off D i) 1)
    (hsep : ∀ i < 3 * k, ∀ x, ofs B x < Z → off D i ≠ x)
    (hq : 0 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D (2 * k)) k)) :
    WP isa qDiv s fun t =>
      (t.gpr .r25 = mask (decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D k) %
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D (2 * k)) k) = 1)) ∧
        arr t.mem B w 0 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D k) ∧ Body B w s.mem t.mem ∧
        t.gpr .r31 = B) ∧ Keep qDivRegs s t := by
  have hZ := h.hZ
  have hw := h.hw
  have hw' := h.hw'
  have e0 := slot_eq w 0; have e1 := slot_eq w 1; have e4 := slot_eq w 4; have e7 := slot_eq w 7
  have e8 := slot_eq w 8; have e28 := slot_eq w 28
  have rdQ : ∀ i < k, InRegions (s.rd ++ s.wr) (off (off D (2 * k)) i) 1 := fun i hi => by
    rw [off_off']; exact hrd _ (by omega_arith)
  have sepQ : ∀ i < k, ∀ x, ofs B x < Z → off (off D (2 * k)) i ≠ x := fun i hi => by
    rw [off_off']; exact hsep _ (by omega_arith)
  have sepP : ∀ i < k, ∀ x, ofs B x < Z → off D i ≠ x := fun i hi => hsep i (by omega_arith)
  generalize hp : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D k) = p
  generalize hqd : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D (2 * k)) k) = q at hq
  unfold qDiv
  refine WP.seq (WP.mono (WP.keep [.r6, .r12] (Q := fun t => t.gpr .r12 = off (off D (2 * k)) 0 ∧
    t.gpr .r6 = BitVec.ofNat 64 k ∧ t.mem = s.mem) (by
      prun [h21, h28, shl1_ofNat, BitVec.add_zero]
      exact BitVec.add_comm _ _) (by decide)) fun s₁ ⟨⟨a12, a6, m1⟩, k1⟩ => ?_)
  have e1' := h.keep k1 (by decide)
  refine WP.seq (WP.mono (loadA0_ok e1' a12 a6 hk hkw (by rw [k1.rd, k1.wr]; exact rdQ) sepQ)
    fun s₂ ⟨⟨q2, b2⟩, k2⟩ => ?_)
  rw [m1, hqd] at q2
  have e2 := e1'.keep k2 (by decide)
  have k12 := k1.trans k2
  refine WP.seq (WP.mono (WP.keep [.r30, .r31] (Q := fun t => t.gpr .r30 = off D 0 ∧
    t.gpr .r31 = BitVec.ofNat 64 k ∧ t.mem = s₂.mem) (by
      prun [(k12.gpr .r21 (by decide)).trans h21, (k12.gpr .r28 (by decide)).trans h28, BitVec.add_zero]) (by decide))
    fun s₃ ⟨⟨a30, a31, m3⟩, k3⟩ => ?_)
  have k13 := k12.trans k3
  refine WP.seq (WP.mono (ModArith.reduce_ok (hs := h.hs.congr k13.wr) (by omega_arith) (by omega_arith) (by omega_arith)
    ((k3.gpr .r10 (by decide)).trans e2.h10) ((k3.gpr .r29 (by decide)).trans e2.h29)
    ((k3.gpr .r11 (by decide)).trans e2.h11) (by rw [m3]; show 0 < arr s₂.mem B w 0; rw [q2]; exact hq)
    a30 a31 hk (by omega_arith) (fun i hi => by rw [k13.rd, k13.wr]; exact hrd i (by omega_arith)) sepP)
    fun s₄ ⟨⟨r1, o4⟩, k4⟩ => ?_)
  have hbP : Spec.Rsa.bytesAt s₃.mem D k = Spec.Rsa.bytesAt s.mem D k := by
    rw [m3, b2.bytesAt hZ sepP, m1]
  rw [hbP, hp, m3] at r1
  change val32 s₄.mem B (slot w 1) (2 * w) = p % arr s₂.mem B w 0 at r1
  rw [q2] at r1
  have k14 := k13.trans k4
  refine WP.seq (WP.mono (WP.keep [.r31] (Q := fun t => t.gpr .r31 = B ∧ t.mem = s₄.mem) (by
      prun [(k14.gpr .r23 (by decide)).trans h23, BitVec.add_zero]) (by decide)) fun s₅ ⟨⟨a31', m5⟩, k5⟩ => ?_)
  have k15 := k14.trans k5
  have e5 : Env s₅ B Z w := ⟨h.hs.congr k15.wr, (k15.gpr .r10 (by decide)).trans h.h10,
    (k15.gpr .r29 (by decide)).trans h.h29, (k15.gpr .r11 (by decide)).trans h.h11, a31', hw, hw', hZ⟩
  refine WP.seq (WP.mono (Pub.oneP_ok e5.hs (by omega_arith) (by omega_arith) (by omega_arith) e5.h10 e5.h29 e5.h11)
    fun s₆ ⟨⟨v7, o6⟩, k6⟩ => ?_)
  have e6 := e5.keep k6 (by decide)
  refine WP.seq (WP.mono (eqMask_ok e6 .r25 (a := 1) (b := 7) (by decide) (by decide)) fun s₇ ⟨⟨a25, m7⟩, k7⟩ => ?_)
  have v1 : val32 s₆.mem B (slot w 1) (2 * w) = p % q := by
    rw [Outside.val32 o6 (by omega_arith) (by omega_arith), m5]
    exact r1
  rw [v1, v7] at a25
  have k17 := (k15.trans k6).trans k7
  refine WP.mono (reloadP_ok (e6.keep k7 (by decide)) ((k17.gpr .r21 (by decide)).trans h21)
    ((k17.gpr .r28 (by decide)).trans h28) hk hkw (fun i hi => by rw [k17.rd, k17.wr]; exact hrd i (by omega_arith))
    sepP) fun t ⟨⟨vt, bt⟩, kt⟩ => ⟨⟨(kt.gpr .r25 (by decide)).trans a25, ?_, ?_,
      ((k6.trans k7).trans kt).gpr .r31 (by decide) |>.trans a31'⟩, (k17.trans kt).mono (by decide)⟩
  · have hb7 : Body B w s.mem s₇.mem := by
      rw [m7]
      refine Outside.trans (m₂ := s₅.mem) ?_ (Body.of o6 (by omega_arith) (by omega_arith))
      rw [m5]
      refine Outside.trans (m₂ := s₃.mem) ?_ (Body.of o4 (by omega_arith) (by omega_arith))
      rw [m3, ← m1]; exact b2
    rw [vt, hb7.bytesAt hZ sepP, hp]
  · refine Outside.trans (m₂ := s₇.mem) ?_ bt
    rw [m7]
    refine Outside.trans (m₂ := s₅.mem) ?_ (Body.of o6 (by omega_arith) (by omega_arith))
    rw [m5]
    refine Outside.trans (m₂ := s₃.mem) ?_ (Body.of o4 (by omega_arith) (by omega_arith))
    rw [m3, ← m1]; exact b2

theorem li_ok (s : State) (v : Nat) (hv : v < 2 ^ 15) :
    WP isa (.block [.li .r3 v]) s fun t => (t.gpr .r3 = BitVec.ofNat 64 v ∧ t.mem = s.mem) ∧ Keep [.r3] s t := by
  refine WP.keep _ ?_ (by rfl)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_li hv, gpr_write, mem_write, ↓reduceIte,
    Option.some.injEq, exists_eq_left', and_self]

/-- `checkG`: g's `k` octets (at `D + k`) into array 4, `r26 :=` the mask of
`1 < g < p − 1`. -/
theorem checkG_ok {s : State} {B D : Addr} {Z w k : Nat} (h : Env s B Z w) (h23 : s.gpr .r23 = B)
    (h21 : s.gpr .r21 = D) (h28 : s.gpr .r28 = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hkw : k ≤ 8 * w)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off (off D k) i) 1)
    (hsep : ∀ i < k, ∀ x, ofs B x < Z → off (off D k) i ≠ x) (hp : 1 ≤ arr s.mem B w 0) :
    WP isa checkG s fun t =>
      (arr t.mem B w 4 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k) ∧ arr t.mem B w 0 = arr s.mem B w 0 ∧
        t.gpr .r26 = mask (decide (1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k) ∧
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k) < arr s.mem B w 0 - 1)) ∧
        Body B w s.mem t.mem ∧ t.gpr .r10 = off B (slot w 0)) ∧ Keep rangeRegs s t := by
  unfold checkG gPtr
  refine WP.seq (WP.mono (WP.keep [.r26] (Q := fun t => t.gpr .r26 = off D k ∧ t.mem = s.mem)
    (by prun [h21, h28]) (by decide)) fun s₁ ⟨⟨a26, m1⟩, k1⟩ => ?_)
  refine WP.mono (range_ok (h.keep k1 (by decide)) ((k1.gpr .r23 (by decide)).trans h23) a26
    ((k1.gpr .r28 (by decide)).trans h28) hk hkw (by rw [k1.rd, k1.wr]; exact hrd) hsep (by rw [m1]; exact hp))
    fun t ⟨⟨v4, v0, _, a, b, a10⟩, kt⟩ => ⟨⟨?_, ?_, ?_, ?_, a10⟩, (k1.trans kt).mono (by decide)⟩
  · rw [v4, m1]
  · rw [v0, m1]
  · rw [a, m1]
  · rw [← m1]; exact b

/-- The registers `withQ` writes. -/
def withQRegs : List Reg := rangeRegs ++ qDivRegs ++ subRegs ++ ([.r0, .r3, .r16, .r26] : List Reg)

/-- What `withQ` checks of q and g (p, q, g their numbers). -/
def qConds (p q g : Nat) : Prop :=
  ((1 < q ∧ q < p - 1) ∧ q % 2 = 1) ∧ ((1 < g ∧ g < p - 1) ∧ p % q = 1) ∧ g ^ q % p = 1

instance (p q g : Nat) : Decidable (qConds p q g) := by unfold qConds; infer_instance

/-- `withQ`: `r3 := 1` if q and g pass their checks, else 0. -/
theorem withQ_ok {s : State} {B D : Addr} {Z w k : Nat} (h : Env s B Z w) (h23 : s.gpr .r23 = B)
    (h21 : s.gpr .r21 = D) (h28 : s.gpr .r28 = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hkw : k ≤ 8 * w)
    (hk' : k ≤ 1024)
    (hrd : ∀ i < 3 * k, InRegions (s.rd ++ s.wr) (off D i) 1)
    (hsep : ∀ i < 3 * k, ∀ x, ofs B x < Z → off D i ≠ x)
    (hP : arr s.mem B w 0 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D k)) (hp2 : 2 ≤ arr s.mem B w 0)
    (hodd : arr s.mem B w 0 % 2 = 1) :
    WP isa withQ s fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 (if qConds (arr s.mem B w 0)
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D (2 * k)) k))
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k)) then 1 else 0) ∧
        Body B w s.mem t.mem) ∧ Keep withQRegs s t := by
  have hZ := h.hZ
  have hw := h.hw
  have hw' := h.hw'
  have sep' : ∀ {a}, a + k ≤ 3 * k → ∀ i < k, ∀ x, ofs B x < Z → off (off D a) i ≠ x := fun ha i hi => by
    rw [off_off']; exact hsep _ (by omega_arith)
  have rd' : ∀ {t : State} {a}, t.rd = s.rd → t.wr = s.wr → a + k ≤ 3 * k →
      ∀ i < k, InRegions (t.rd ++ t.wr) (off (off D a) i) 1 := fun h1 h2 ha i hi => by
    rw [h1, h2, off_off']; exact hrd _ (by omega_arith)
  generalize hp : arr s.mem B w 0 = p at hP hp2 hodd
  generalize hq : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D (2 * k)) k) = q
  generalize hg : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k) = g
  unfold withQ qPtr
  refine WP.seq (WP.mono (WP.keep [.r26] (Q := fun t => t.gpr .r26 = off D (2 * k) ∧ t.mem = s.mem) (by
      prun [h21, h28, shl1_ofNat]
      exact BitVec.add_comm _ _) (by decide)) fun s₁ ⟨⟨a26, m1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (range_ok (h.keep k1 (by decide)) ((k1.gpr .r23 (by decide)).trans h23) a26
    ((k1.gpr .r28 (by decide)).trans h28) hk hkw (rd' k1.rd k1.wr (by omega_arith)) (sep' (by omega_arith))
    (by rw [m1, hp]; omega_arith)) fun s₂ ⟨⟨_, p2, _, r2, b2, a10⟩, k2⟩ => ?_)
  rw [m1, hq, hp] at r2
  rw [m1, hp] at p2
  rw [m1] at b2
  have k12 := k1.trans k2
  have e2 : Env s₂ B Z w := ⟨h.hs.congr k12.wr, a10, (k12.gpr .r29 (by decide)).trans h.h29,
    (k12.gpr .r11 (by decide)).trans h.h11, (k12.gpr .r31 (by decide)).trans h.h31, hw, hw', hZ⟩
  refine WP.seq (WP.mono (qOdd_ok ((k12.gpr .r21 (by decide)).trans h21) ((k12.gpr .r28 (by decide)).trans h28) r2
    hk hk' (by rw [k12.rd, k12.wr]; exact hrd _ (by omega_arith))) fun s₃ ⟨⟨r3', m3⟩, k3⟩ => ?_)
  rw [b2.bytesAt hZ (sep' (by omega_arith)), hq] at r3'
  have k13 := k12.trans k3
  have e3 := e2.keep k3 (by decide)
  refine WP.ite (s₃.gpr .r26 == 0) (eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · rw [r3', mask_beq_zero, Bool.not_eq_true'] at hb
    refine WP.mono (li_ok s₃ 0 (by decide)) fun t ⟨⟨t3, tm⟩, kt⟩ => ⟨⟨?_, ?_⟩, (k13.trans kt).mono (by decide)⟩
    · rw [t3, ite_eq_right fun hc => ?_]
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at hb
      rcases hb with hb | hb
      · exact hb hc.1.1
      · exact hb hc.1.2
    · rw [tm, m3]; exact b2
  · rw [r3', mask_beq_zero, Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hb
    refine WP.seq (WP.mono (qDiv_ok e3 ((k13.gpr .r23 (by decide)).trans h23) ((k13.gpr .r21 (by decide)).trans h21)
      ((k13.gpr .r28 (by decide)).trans h28) hk hkw (by rw [k13.rd, k13.wr]; exact hrd) hsep
      (by rw [m3, b2.bytesAt hZ (sep' (by omega_arith)), hq]; omega_arith)) fun s₄ ⟨⟨r25, p4, b4, a31⟩, k4⟩ => ?_)
    have hbP : Spec.Rsa.bytesAt s₃.mem D k = Spec.Rsa.bytesAt s.mem D k := by
      rw [m3, b2.bytesAt hZ fun i hi => hsep i (by omega_arith)]
    rw [hbP, ← hP, m3, b2.bytesAt hZ (sep' (by omega_arith)), hq] at r25
    rw [hbP, ← hP] at p4
    have k14 := k13.trans k4
    have e4 : Env s₄ B Z w := ⟨h.hs.congr k14.wr, (k4.gpr .r10 (by decide)).trans e3.h10,
      (k4.gpr .r29 (by decide)).trans e3.h29, (k4.gpr .r11 (by decide)).trans e3.h11, a31, hw, hw', hZ⟩
    refine WP.seq (WP.mono (checkG_ok e4 ((k14.gpr .r23 (by decide)).trans h23) ((k14.gpr .r21 (by decide)).trans h21)
      ((k14.gpr .r28 (by decide)).trans h28) hk hkw (rd' k14.rd k14.wr (by omega_arith)) (sep' (by omega_arith))
      (by rw [p4]; omega_arith)) fun s₅ ⟨⟨g5, p5, r5, b5, a10'⟩, k5⟩ => ?_)
    have hb4 : Body B w s.mem s₄.mem := Outside.trans (m₂ := s₂.mem) b2 (by rw [← m3]; exact b4)
    rw [hb4.bytesAt hZ (sep' (by omega_arith)), hg] at g5
    rw [hb4.bytesAt hZ (sep' (by omega_arith)), hg, p4] at r5
    rw [p4] at p5
    have k15 := k14.trans k5
    refine WP.seq (WP.mono (WP.keep [.r26] (Q := fun t => t.gpr .r26 = mask ((decide (1 < g ∧ g < p - 1)) &&
      decide (p % q = 1)) ∧ t.mem = s₅.mem) (by
        prun [r5, (k5.gpr .r25 (by decide)).trans r25, mask_and']) (by decide)) fun s₆ ⟨⟨r6, m6⟩, k6⟩ => ?_)
    have k16 := k15.trans k6
    have hb6 : Body B w s.mem s₆.mem := by rw [m6]; exact Outside.trans hb4 b5
    refine WP.ite (s₆.gpr .r26 == 0) (eval_zero _ _) (fun hb' => ?_) (fun hb' => ?_)
    · rw [r6, mask_beq_zero, Bool.not_eq_true'] at hb'
      refine WP.mono (li_ok s₆ 0 (by decide)) fun t ⟨⟨t3, tm⟩, kt⟩ => ⟨⟨?_, by rw [tm]; exact hb6⟩,
        (k16.trans kt).mono (by decide)⟩
      rw [t3, ite_eq_right fun hc => ?_]
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at hb'
      rcases hb' with hb' | hb'
      · exact hb' hc.2.1.1
      · exact hb' hc.2.1.2
    · rw [r6, mask_beq_zero, Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hb'
      have e6 : Env s₆ B Z w := ⟨h.hs.congr k16.wr, (k6.gpr .r10 (by decide)).trans a10',
        (k16.gpr .r29 (by decide)).trans h.h29, (k16.gpr .r11 (by decide)).trans h.h11,
        (k6.gpr .r31 (by decide)).trans ((k5.gpr .r31 (by decide)).trans a31), hw, hw', hZ⟩
      refine WP.mono (subgroup_ok e6 ((k16.gpr .r23 (by decide)).trans h23) ((k16.gpr .r21 (by decide)).trans h21)
        ((k16.gpr .r28 (by decide)).trans h28) hk hk' (by rw [m6, p5]; exact hp2) (by rw [m6, p5]; exact hodd)
        (rd' k16.rd k16.wr (by omega_arith)) (sep' (by omega_arith))) fun t ⟨⟨t3, bt⟩, kt⟩ =>
          ⟨⟨?_, Outside.trans hb6 bt⟩, (k16.trans kt).mono (by decide)⟩
      rw [t3, m6, g5, p5, Body.bytesAt (Outside.trans hb4 b5) hZ (sep' (by omega_arith)), hq]
      congr 1
      by_cases hc : g ^ q % p = 1
      · rw [ite_eq_left hc, ite_eq_left ⟨hb, hb', hc⟩]
      · rw [ite_eq_right hc, ite_eq_right fun h' => hc h'.2.2]

/-- `withoutQ`: `r3 := 1` if `1 < g < p − 1`, else 0. -/
theorem withoutQ_ok {s : State} {B D : Addr} {Z w k : Nat} (h : Env s B Z w) (h23 : s.gpr .r23 = B)
    (h21 : s.gpr .r21 = D) (h28 : s.gpr .r28 = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hkw : k ≤ 8 * w)
    (hrd : ∀ i < 2 * k, InRegions (s.rd ++ s.wr) (off D i) 1)
    (hsep : ∀ i < 2 * k, ∀ x, ofs B x < Z → off D i ≠ x) (hp : 1 ≤ arr s.mem B w 0) :
    WP isa withoutQ s fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 (if 1 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k) ∧
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k) < arr s.mem B w 0 - 1 then 1 else 0) ∧
        Body B w s.mem t.mem) ∧ Keep (rangeRegs ++ ([.r3, .r26] : List Reg)) s t := by
  unfold withoutQ
  refine WP.seq (WP.mono (checkG_ok h h23 h21 h28 hk hkw (fun i hi => by rw [off_off']; exact hrd _ (by omega_arith))
    (fun i hi => by rw [off_off']; exact hsep _ (by omega_arith)) hp) fun s₁ ⟨⟨_, _, r26, b1, _⟩, k1⟩ => ?_)
  refine WP.ite (s₁.gpr .r26 == 0) (eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · rw [r26, mask_beq_zero, Bool.not_eq_true', decide_eq_false_iff_not] at hb
    refine WP.mono (li_ok s₁ 0 (by decide)) fun t ⟨⟨t3, tm⟩, kt⟩ =>
      ⟨⟨by rw [t3, ite_eq_right hb], by rw [tm]; exact b1⟩, (k1.trans kt).mono (by decide)⟩
  · rw [r26, mask_beq_zero, Bool.not_eq_false', decide_eq_true_eq] at hb
    refine WP.mono (li_ok s₁ 1 (by decide)) fun t ⟨⟨t3, tm⟩, kt⟩ =>
      ⟨⟨by rw [t3, ite_eq_left hb], by rw [tm]; exact b1⟩, (k1.trans kt).mono (by decide)⟩

/-- The registers `domainBody` writes. -/
def domainBodyRegs : List Reg := withQRegs ++ ([.r0] : List Reg)

/-- The condition `domainBody` checks after p's: q's and g's with q, else g's. -/
def bodyCond (L k p q g : Nat) : Prop := if L = 3 * k then qConds p q g else 1 < g ∧ g < p - 1

instance (L k p q g : Nat) : Decidable (bodyCond L k p q g) := by unfold bodyCond; infer_instance

/-- `domainBody`: `r3 := 1` if `bodyCond`, else 0. -/
theorem domainBody_ok {s : State} {B D : Addr} {Z w k L : Nat} (h : Env s B Z w) (h23 : s.gpr .r23 = B)
    (h21 : s.gpr .r21 = D) (h27 : s.gpr .r27 = BitVec.ofNat 64 L) (h28 : s.gpr .r28 = BitVec.ofNat 64 k)
    (hk : 1 ≤ k) (hkw : k ≤ 8 * w) (hk' : k ≤ 1024) (hL : L = 2 * k ∨ L = 3 * k)
    (hrd : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1)
    (hsep : ∀ i < L, ∀ x, ofs B x < Z → off D i ≠ x)
    (hP : arr s.mem B w 0 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem D k)) (hp2 : 2 ≤ arr s.mem B w 0)
    (hodd : arr s.mem B w 0 % 2 = 1) :
    WP isa domainBody s fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 (if bodyCond L k (arr s.mem B w 0)
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D (2 * k)) k))
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k)) then 1 else 0) ∧
        Body B w s.mem t.mem) ∧ Keep domainBodyRegs s t := by
  unfold domainBody
  refine WP.seq (WP.mono (WP.keep [.r0] (Q := fun t => (t.gpr .r0 == 0) = decide (L = 3 * k) ∧ t.mem = s.mem) (by
      unfold hasQ
      prun [h27, h28]
      exact sub_3k_zero (by omega_arith) (by omega_arith)) (by decide)) fun s₁ ⟨⟨a0, m1⟩, k1⟩ => ?_)
  have e1 := h.keep k1 (by decide)
  refine WP.ite (s₁.gpr .r0 == 0) (eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · rw [a0, decide_eq_true_eq] at hb
    subst hb
    refine WP.mono (withQ_ok e1 ((k1.gpr .r23 (by decide)).trans h23) ((k1.gpr .r21 (by decide)).trans h21)
      ((k1.gpr .r28 (by decide)).trans h28) hk hkw hk' (by rw [k1.rd, k1.wr]; exact hrd) hsep
      (by rw [m1]; exact hP) (by rw [m1]; exact hp2) (by rw [m1]; exact hodd)) fun t ⟨⟨t3, bt⟩, kt⟩ =>
        ⟨⟨by rw [t3, m1]; simp only [bodyCond, ↓reduceIte], by rw [← m1]; exact bt⟩, (k1.trans kt).mono (by decide)⟩
  · rw [a0, decide_eq_false_iff_not] at hb
    have h2 : L = 2 * k := by omega_arith
    subst h2
    refine WP.mono (withoutQ_ok e1 ((k1.gpr .r23 (by decide)).trans h23) ((k1.gpr .r21 (by decide)).trans h21)
      ((k1.gpr .r28 (by decide)).trans h28) hk hkw (by rw [k1.rd, k1.wr]; exact hrd) hsep
      (by rw [m1]; omega_arith)) fun t ⟨⟨t3, bt⟩, kt⟩ =>
        ⟨⟨by rw [t3, m1]; simp only [bodyCond, hb, ↓reduceIte], by rw [← m1]; exact bt⟩, (k1.trans kt).mono (by decide)⟩

end VG.Proof.Ffdh.PPC64LE.Domain

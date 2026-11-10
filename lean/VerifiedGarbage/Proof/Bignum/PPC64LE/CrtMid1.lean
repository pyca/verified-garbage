module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Bignum.CrtFrame
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPre
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPhaseA
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPhaseP
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtVals
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtLoadX
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPowerA
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCheckR2
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtRecX
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCopy
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtSetup
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtChecks
import VerifiedGarbage.Proof.Mont.RangeCover

/-!
# The RSA private-key operation on PPC64LE: the powers

`mid1_ok`: after the front, `X` loaded and checked (`phaseA_ok`), then
`m₁ = c^dP mod p` and `m₂ = c^dQ mod q` (`phaseP_ok`), with `p`, `q` and
`qInv` masked.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

variable {pc : Bool}

/-- The numbers of the entry state `s₀`. -/
abbrev vN (s₀ : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .r5) (ck s₀))
abbrev vC (s₀ : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .r7) (ck s₀))
abbrev vP (s₀ : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .r9) (cpL s₀))
abbrev vQ (s₀ : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (stackArg s₀ 0) (cqL s₀))
abbrev vDP (s₀ : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (stackArg s₀ 2) (cpL s₀))
abbrev vDQ (s₀ : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (stackArg s₀ 4) (cqL s₀))
abbrev vQI (s₀ : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (stackArg s₀ 6) (cpL s₀))
/-- The checks' mask. -/
abbrev cb0 (s₀ : State) : Bool := crtMask (vN s₀) (ck s₀) (vC s₀) (vP s₀) (vQ s₀) (vQI s₀)
/-- `wP`, `wQ`, and the offsets of `P` and `Q`. -/
abbrev cwP (s₀ : State) : Nat := wsWords (cpL s₀)
abbrev cwQ (s₀ : State) : Nat := wsWords (cqL s₀)
abbrev oPa (s₀ : State) : Nat := slot (cwX s₀) 8
abbrev oQa (s₀ : State) : Nat := slot (cwX s₀) 8 + slot (cwP s₀) 24
/-- With `vg_rsa_private_crt_precomputed`, the cached values `checkR2` checks,
under the checks' mask: the buffer at the entry's `r12`'s, else 1. -/
abbrev cxP (s₀ : State) : Nat := if cb0 s₀ then wv s₀.mem (s₀.gpr .r12) 0 (cwP s₀) else 1
abbrev cxQ (s₀ : State) : Nat := if cb0 s₀ then wv s₀.mem (s₀.gpr .r12) (8 * cwP s₀) (cwQ s₀) else 1
/-- The mask: the checks', and with `pc` the cached values checked against
the primes (3 under a clear mask). -/
def cb : Bool → State → Bool
  | false, s₀ => cb0 s₀
  | true, s₀ => cb0 s₀ && decide (cxP s₀ = 2 ^ (128 * cwP s₀) % (if cb0 s₀ then vP s₀ else 3)) &&
      decide (cxQ s₀ = 2 ^ (128 * cwQ s₀) % (if cb0 s₀ then vQ s₀ else 3))
/-- The masked `p`, `q` and `qInv`. -/
abbrev mP (pc : Bool) (s₀ : State) : Nat := if cb pc s₀ then vP s₀ else 3
abbrev mQ (pc : Bool) (s₀ : State) : Nat := if cb pc s₀ then vQ s₀ else 3
abbrev mQI (pc : Bool) (s₀ : State) : Nat := if cb pc s₀ then vQI s₀ else 0

theorem cb_cb0 {pc : Bool} {s₀ : State} (h : cb pc s₀ = true) : cb0 s₀ = true := by
  cases pc
  · exact h
  · simp only [cb, Bool.and_eq_true] at h; exact h.1.1

/-- What the masked numbers satisfy. -/
theorem masked_facts {pc : Bool} {s₀ : State} (hP : PF s₀) :
    1 < mP pc s₀ ∧ mP pc s₀ % 2 = 1 ∧ 1 < mQ pc s₀ ∧ mQ pc s₀ % 2 = 1 ∧ mP pc s₀ < 2 ^ (64 * cwP s₀) ∧
      mQ pc s₀ < 2 ^ (64 * cwQ s₀) ∧ mQ pc s₀ ≤ 256 ^ cqL s₀ ∧ mQI pc s₀ < mP pc s₀ ∧ mQI pc s₀ < 2 ^ (64 * cwP s₀) := by
  have hpw : cpL s₀ ≤ 8 * cwP s₀ := by unfold cwP wsWords; omega_arith
  have hqw : cqL s₀ ≤ 8 * cwQ s₀ := by unfold cwQ wsWords; omega_arith
  have h3p : 3 < 2 ^ (64 * cwP s₀) := Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (n := 2) (by decide)
    (show 2 ≤ 64 * cwP s₀ by unfold cwP wsWords; omega_arith))
  have h3q : 3 < 2 ^ (64 * cwQ s₀) := Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (n := 2) (by decide)
    (show 2 ≤ 64 * cwQ s₀ by unfold cwQ wsWords; omega_arith))
  have h3 : 3 ≤ 256 ^ cqL s₀ := Nat.le_trans (by decide) (Nat.pow_le_pow_right (n := 256) (by decide) hP.q1)
  unfold mP mQ mQI
  cases hb : cb pc s₀
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨by decide, by decide, by decide, by decide, h3p, h3q, h3, by decide, by omega_arith⟩
  · simp only [↓reduceIte]
    obtain ⟨_, _, hi, _, hp1, hpo, hq1, hqo⟩ := mask_true hP.k64
      (by rw [VG.Proof.Bignum.bytesAt_length]; exact hP.pk) (by rw [VG.Proof.Bignum.bytesAt_length]; exact hP.qk)
      (cb_cb0 hb)
    exact ⟨hp1, hpo, hq1, hqo, Nat.lt_of_lt_of_le (os2ip_lt' _ (VG.Proof.Bignum.bytesAt_length _ _ _)) (pow256_le hpw),
      Nat.lt_of_lt_of_le (os2ip_lt' _ (VG.Proof.Bignum.bytesAt_length _ _ _)) (pow256_le hqw),
      Nat.le_of_lt (os2ip_lt' _ (VG.Proof.Bignum.bytesAt_length _ _ _)), hi,
      Nat.lt_of_lt_of_le (os2ip_lt' _ (VG.Proof.Bignum.bytesAt_length _ _ _)) (pow256_le hpw)⟩

/-- With `pc`, the cached `R² mod p` and `R² mod q` at the entry's `r12`:
readable and apart from the working space. -/
structure R2F (s₀ : State) : Prop where
  hS : (s₀.gpr .r12).toNat + 8 * (cwP s₀ + cwQ s₀) ≤ 2 ^ 64
  rd : ∀ i < cwP s₀ + cwQ s₀, InRegions (s₀.rd ++ s₀.wr) (off (s₀.gpr .r12) (8 * i)) 8
  sep : ∀ x, ofs (s₀.gpr .r12) x < 8 * (cwP s₀ + cwQ s₀) → cZ s₀ ≤ ofs (cS s₀) x

/-- Memory apart from the working space, as at entry. -/
theorem wv_entry {s₀ s t : State} (hF : Front s₀ s) (ho : Outside (cS s₀) 256 (cZ s₀ - 256) s.mem t.mem)
    (hZ : 256 ≤ cZ s₀) {S : Addr} {n d : Nat} (hS : S.toNat + (d + 8 * n) ≤ 2 ^ 64)
    (hsep : ∀ x, ofs S x < d + 8 * n → cZ s₀ ≤ ofs (cS s₀) x) : wv t.mem S d n = wv s₀.mem S d n := by
  have O : Outside (cS s₀) 0 (cZ s₀) s₀.mem t.mem :=
    (hF.mem.mono (by omega_arith) (by omega_arith)).trans (ho.mono (by omega_arith) (by omega_arith))
  exact wv_congr2 fun i hi => Pub.Outside.word_apart O hsep (by omega_arith) (by omega_arith) hS

/-- Where `r2Copy` copies `R² mod p` from, from `R2F`, under the mask of `b`. -/
theorem R2F.pS {s₀ s t : State} {b : Bool} (F : R2F s₀) (hP : PF s₀)
    (hhd : word s.mem (cS s₀) oR2 = s₀.gpr .r12) (ho : Outside (cS s₀) 256 (cZ s₀ - 256) s.mem t.mem)
    (hrw : t.rd ++ t.wr = s₀.rd ++ s₀.wr) (h26 : t.gpr .r26 = bmask b) :
    R2S false t (cS s₀) (s₀.gpr .r12) (cZ s₀) (cwP s₀) (cpL s₀) b where
  src := by
    rw [ho.word (Or.inl (by unfold oR2; omega_arith)) (by unfold oR2; omega_arith), hhd]
    simp only [Bool.false_eq_true, ↓reduceIte, BitVec.add_zero]
  pl := nofun
  pl1 := hP.p1
  pl2 := by have := hP.pk; have := hP.k1024; omega_arith
  hS := by have := F.hS; omega_arith
  rd i hi := by rw [hrw]; exact F.rd i (by omega_arith)
  sep x hx := F.sep x (by omega_arith)
  r26 := h26

/-- Where `r2Copy` copies `R² mod q` from, from `R2F`: after `p`'s words. -/
theorem R2F.qS {s₀ s t : State} {b : Bool} (F : R2F s₀) (hP : PF s₀) (hF : Front s₀ s)
    (hhd : word s.mem (cS s₀) oR2 = s₀.gpr .r12) (ho : Outside (cS s₀) 256 (cZ s₀ - 256) s.mem t.mem)
    (hrw : t.rd ++ t.wr = s₀.rd ++ s₀.wr) (h26 : t.gpr .r26 = bmask b) :
    R2S true t (cS s₀) (off (s₀.gpr .r12) (8 * cwP s₀)) (cZ s₀) (cwQ s₀) (cpL s₀) b where
  src := by
    rw [ho.word (Or.inl (by unfold oR2; omega_arith)) (by unfold oR2; omega_arith), hhd]
    simp only [↓reduceIte]
  pl _ := by rw [ho.word (Or.inl (by unfold oPLen; omega_arith)) (by unfold oPLen; omega_arith)]; exact hF.hPL
  pl1 := hP.p1
  pl2 := by have := hP.pk; have := hP.k1024; omega_arith
  hS := by have := F.hS; have := toNat_off_le (s₀.gpr .r12) (8 * cwP s₀); omega_arith
  rd i hi := by rw [hrw, off_off, ← Nat.mul_add]; exact F.rd (cwP s₀ + i) (by omega_arith)
  sep x hx := F.sep x (by
    rcases ofs_rebase (s₀.gpr .r12) x (o := 8 * cwP s₀) (by have := F.hS; omega_arith) with ⟨_, h2⟩ | ⟨h1, _⟩
    · change ofs (off (s₀.gpr .r12) (8 * cwP s₀)) x < _ at hx; omega_arith
    · omega_arith)
  r26 := h26

/-- `R2C` for `p`, after `checkR2`: the mask holds only if the cached value
is `R² mod p`. -/
theorem R2F.p {s₀ s t : State} (F : R2F s₀) (hP : PF s₀) (hF : Front s₀ s)
    (hhd : word s.mem (cS s₀) oR2 = s₀.gpr .r12) (ho : Outside (cS s₀) 256 (cZ s₀ - 256) s.mem t.mem)
    (hrw : t.rd ++ t.wr = s₀.rd ++ s₀.wr) (h26 : t.gpr .r26 = bmask (cb true s₀)) :
    R2C false t (cS s₀) (s₀.gpr .r12) (cZ s₀) (cwP s₀) (mP true s₀) (cpL s₀) (cb true s₀) where
  toR2S := F.pS hP hhd ho hrw h26
  val hb := by
    rw [wv_entry hF ho (by have := hP.room; unfold slot hdrBytes at this; omega_arith)
      (by have := F.hS; omega_arith) fun x hx => F.sep x (by omega_arith)]
    have h := hb
    simp only [cb, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h0, hx⟩, _⟩ := h
    simp only [cxP, h0, ↓reduceIte] at hx
    simp only [mP, hb, ↓reduceIte]; exact hx
  three hb := by simp [mP, hb]

/-- `R2C` for `q`, after `checkR2`. -/
theorem R2F.q {s₀ s t : State} (F : R2F s₀) (hP : PF s₀) (hF : Front s₀ s)
    (hhd : word s.mem (cS s₀) oR2 = s₀.gpr .r12) (ho : Outside (cS s₀) 256 (cZ s₀ - 256) s.mem t.mem)
    (hrw : t.rd ++ t.wr = s₀.rd ++ s₀.wr) (h26 : t.gpr .r26 = bmask (cb true s₀)) :
    R2C true t (cS s₀) (off (s₀.gpr .r12) (8 * cwP s₀)) (cZ s₀) (cwQ s₀) (mQ true s₀) (cpL s₀) (cb true s₀) where
  toR2S := F.qS hP hF hhd ho hrw h26
  val hb := by
    rw [wv_off, Nat.add_zero, wv_entry hF ho (by have := hP.room; unfold slot hdrBytes at this; omega_arith)
      (by have := F.hS; omega_arith) fun x hx => F.sep x (by omega_arith)]
    have h := hb
    simp only [cb, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h0, _⟩, hx⟩ := h
    simp only [cxQ, h0, ↓reduceIte] at hx
    simp only [mQ, hb, ↓reduceIte]; exact hx
  three hb := by simp [mQ, hb]

theorem xval {m m' : Mem} {B : Addr} {a n d w : Nat} (h : Outside B a n m m') (hd : d + 8 * w ≤ a ∨ a + n ≤ d)
    (hd' : d + 8 * w ≤ 2 ^ 64) : Mont.val32 m' B d (2 * w) = Mont.val32 m B d (2 * w) := by
  rw [Pre.val32_eq_wv, Pre.val32_eq_wv, h.wv hd hd']

/-- The registers `checksG`'s check of the cached values writes. -/
def valRegs : List Reg := [.r3, .r4, .r10, .r11, .r21, .r29] ++ checkR2Regs

/-- The registers of `mid1`. -/
def mid1Regs : List Reg := loadXRegs ++ checkRegs ++ ([.r0, .r3, .r4, .r14, .r17] : List Reg) ++ valRegs ++
  ([.r0, .r6, .r10, .r12, .r14, .r15, .r16, .r17] : List Reg) ++
  (([.r0, .r3, .r4, .r10, .r11, .r21, .r29] : List Reg) ++ powerRegs) ++
  (([.r0, .r3, .r4, .r10, .r11, .r21, .r29] : List Reg) ++ powerRegs)

/-- What `X` holds after `loadX` and `checks`. -/
structure XA (pc : Bool) (s₀ s t : State) : Prop where
  r26 : t.gpr .r26 = bmask (cb pc s₀)
  v0 : Mont.val32 t.mem (cS s₀) (slot (cwX s₀) 0) (2 * cwX s₀) = 2 ^ (64 * cwX s₀) - 1
  w0 : word t.mem (cS s₀) (slot (cwX s₀) 0) = BitVec.allOnes 64
  v4 : Mont.val32 t.mem (cS s₀) (slot (cwX s₀) 4) (2 * cwX s₀) = mP pc s₀
  v5 : Mont.val32 t.mem (cS s₀) (slot (cwX s₀) 5) (2 * cwX s₀) = mQ pc s₀
  v7 : Mont.val32 t.mem (cS s₀) (slot (cwX s₀) 7) (2 * cwX s₀) = mQI pc s₀
  out : Outside (cS s₀) 256 (cZ s₀ - 256) s.mem t.mem

/-- `loadX` and `checks`, after the front. -/
theorem mid1A0_ok {s₀ s : State} {c : Prog isa} {Q : State → Prop} (hP : PF s₀) (hF : Front s₀ s)
    (hc : ∀ t, XA false s₀ s t → t.gpr .r10 = off (cS s₀) (slot (cwX s₀) 0) →
      Keep (loadXRegs ++ checkRegs ++ ([.r0, .r3, .r4, .r14, .r17] : List Reg)) s t → WP isa c t Q) :
    WP isa (.seq loadX (.seq checks c)) s Q := by
  have hn := hP.nw
  have room := hP.room
  have pq := hP.pq
  have k64 := hP.k64; have k1024 := hP.k1024; have p1 := hP.p1; have pk := hP.pk; have q1 := hP.q1
  have qk := hP.qk
  have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  have eX0 := e (cwX s₀) 0; have eX5 := e (cwX s₀) 5; have eX7 := e (cwX s₀) 7; have eX8 := e (cwX s₀) 8
  have eP0 := e (cwP s₀) 0; have eP4 := e (cwP s₀) 4; have eP8 := e (cwP s₀) 24
  have eQ4 := e (cwQ s₀) 4; have eQ8 := e (cwQ s₀) 24; have eQ0 := e (cwQ s₀) 0
  have dZ : cZ s₀ = (stackArg s₀ 9).toNat * 8 := rfl
  have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
  have dk : ck s₀ = (s₀.gpr .r6).toNat := rfl
  have dp : cpL s₀ = (s₀.gpr .r10).toNat := rfl
  have dq : cqL s₀ = (stackArg s₀ 1).toNat := rfl
  have dP : cwP s₀ = wsWords (cpL s₀) := rfl
  have dQ : cwQ s₀ = wsWords (cqL s₀) := rfl
  have doP : oPa s₀ = slot (cwX s₀) 8 := rfl
  have doQ : oQa s₀ = slot (cwX s₀) 8 + slot (cwP s₀) 24 := rfl
  have dS : cS s₀ = stackArg s₀ 8 := rfl
  have fP8 := e (wsWords (cpL s₀)) 24; have fQ8 := e (wsWords (cqL s₀)) 24
  have fX8 := e (2 * ((ck s₀ + 7) / 8)) 8
  have hwX : cwX s₀ < 2 ^ 31 := by unfold cwX ck; omega_arith
  have k0 := hF.keep
  have rd0 : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [k0.rd, k0.wr]
  have hb0 : ∀ {A : Addr} {L : Nat}, (∀ i < L, ∀ x, ofs (cS s₀) x < cZ s₀ → off A i ≠ x) →
      Spec.Rsa.bytesAt s.mem A L = Spec.Rsa.bytesAt s₀.mem A L := fun hs' => bytesAt_out hF.mem (by omega_arith) hs'
  obtain ⟨mP1, mPo, mQ1, mQo, mPb, mQb, _, mQIP, mQIb⟩ := masked_facts (pc := false) hP
  refine wp_reassoc2 (WP.seq (WP.mono (phaseA_ok hF.scr (by omega_arith) k64 k1024 hF.r23 hF.r10 hF.r21 hF.r29 hF.r11
    hF.hN hF.hNL hF.hP hF.hPL hF.hQ hF.hQL hF.hIn hF.hQI p1 pk q1 qk (by rw [rd0]; exact hP.rN) hP.sN
    (by rw [rd0]; exact hP.rP) hP.sP (by rw [rd0]; exact hP.rQ) hP.sQ (by rw [rd0]; exact hP.rI) hP.sI
    (by rw [rd0]; exact hP.rQI) hP.sQI) fun t₁ ⟨⟨t26, v0, w0, v4, v5, v7, O1, a10⟩, k1⟩ => ?_))
  rw [hb0 hP.sN, hb0 hP.sI, hb0 hP.sP, hb0 hP.sQ, hb0 hP.sQI] at t26 v4 v5 v7
  exact hc t₁ ⟨t26, v0, w0, v4, v5, v7, O1.mono (by omega_arith) (by omega_arith)⟩ a10 k1

/-- A program regrouped under another. -/
theorem wp_inner_assoc {a b v c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq a (.seq b (.seq v c))) s Q) : WP isa (.seq a (.seq (.seq b v) c)) s Q := by
  obtain ⟨t, s', hx, hq⟩ := h
  cases hx with
  | seq h1 h2 =>
    cases h2 with
    | seq hb h3 =>
      cases h3 with
      | seq hv hc => exact ⟨_, _, .seq h1 (.seq (.seq hb hv) hc), hq⟩

/-- `X`'s registers back, after the primes' checks. -/
theorem restoreX_ok {s : State} {BX : Addr} {w : Nat} (h27 : s.gpr .r27 = off BX (slot w 0))
    (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (w + 2))) (hw : w < 2 ^ 31) :
    WP isa (.block [.addi .r10 .r27 0, .addi .r21 .r27 0, .addi .r29 .r28 0, .addi .r11 .r28 0, .subi .r11 .r11 16,
      .lsr .d .r11 .r11 2]) s fun t =>
      (t.gpr .r10 = off BX (slot w 0) ∧ t.gpr .r21 = off BX (slot w 0) ∧
        t.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.gpr .r11 = BitVec.ofNat 64 (2 * w) ∧ t.mem = s.mem) ∧
      Keep [.r10, .r21, .r29, .r11] s t := by
  refine WP.keep _ ?_ (by decide)
  prun [h27, h28, BitVec.add_zero]
  have e1 : BitVec.ofNat 64 (8 * (w + 2)) - 16#64 = BitVec.ofNat 64 (8 * w) := by
    rw [show 8 * (w + 2) = 8 * w + 16 by omega_arith, BitVec.ofNat_add]; exact BitVec.add_sub_cancel _ _
  rw [e1]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 8 * w < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (show 2 * w < 2 ^ 64 by omega_arith)]
  omega_arith

/-- `checksG true`'s check of the cached values, after `checks`: the mask
becomes `cb true`'s, and `p`, `q` and `qInv` are masked by it. -/
theorem mid1V_ok {s₀ s t : State} {c : Prog isa} {Q : State → Prop} (hP : PF s₀) (hF : Front s₀ s)
    (F : R2F s₀) (hhd : word s.mem (cS s₀) oR2 = s₀.gpr .r12) (X : XA false s₀ s t)
    {rs : List Reg} (k : Keep rs s t)
    (h23 : Reg.r23 ∉ rs) (h27 : Reg.r27 ∉ rs) (h28 : Reg.r28 ∉ rs)
    (hc : ∀ u, XA true s₀ s u → u.gpr .r10 = off (cS s₀) (slot (cwX s₀) 0) →
      u.gpr .r21 = off (cS s₀) (slot (cwX s₀) 0) → u.gpr .r29 = BitVec.ofNat 64 (8 * (cwX s₀ + 2)) →
      u.gpr .r11 = BitVec.ofNat 64 (2 * cwX s₀) → Keep (rs ++ valRegs) s u → WP isa c u Q) :
    WP isa (.seq (.seq (.block (setupP oBP oPLen)) (.seq (checkR2 false 4) (.seq (.block (setupP oBQ oQLen))
      (.seq (checkR2 true 5) (.seq (.block [.addi .r10 .r27 0, .addi .r21 .r27 0, .addi .r29 .r28 0,
        .addi .r11 .r28 0, .subi .r11 .r11 16, .lsr .d .r11 .r11 2])
      (.seq (orThree 4) (.seq (orThree 5) (.seq (.block (PublicChecked.base .r14 7)) maskWords)))))))) c) t Q := by
  have hn := hP.nw
  have room := hP.room
  have k64 := hP.k64; have k1024 := hP.k1024; have p1 := hP.p1; have pk := hP.pk; have q1 := hP.q1
  have qk := hP.qk
  have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  have eX0 := e (cwX s₀) 0; have eX4 := e (cwX s₀) 4; have eX5 := e (cwX s₀) 5; have eX7 := e (cwX s₀) 7
  have eX8 := e (cwX s₀) 8
  have eP24 := e (cwP s₀) 24; have eQ24 := e (cwQ s₀) 24
  have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
  have dP : cwP s₀ = wsWords (cpL s₀) := rfl
  have dQ : cwQ s₀ = wsWords (cqL s₀) := rfl
  have doP : oPa s₀ = slot (cwX s₀) 8 := rfl
  have doQ : oQa s₀ = slot (cwX s₀) 8 + slot (cwP s₀) 24 := rfl
  have hwX : cwX s₀ < 2 ^ 31 := by rw [dX]; omega_arith
  have hpw : cwP s₀ ≤ cwX s₀ := by unfold cwP wsWords; omega_arith
  have hqw : cwQ s₀ ≤ cwX s₀ := by unfold cwQ wsWords; omega_arith
  have hp2 : 2 ≤ cwP s₀ := by unfold cwP wsWords; omega_arith
  have hq2 : 2 ≤ cwQ s₀ := by unfold cwQ wsWords; omega_arith
  obtain ⟨mP1, mPo, mQ1, mQo, mPb, mQb, _, _, _⟩ := masked_facts (pc := false) hP
  have rd0 : t.rd ++ t.wr = s₀.rd ++ s₀.wr := by rw [k.rd, k.wr, hF.keep.rd, hF.keep.wr]
  have hd : ∀ d, d + 8 ≤ 256 → word t.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
    X.out.word (Or.inl hd) (by omega_arith)
  have t23 : t.gpr .r23 = cS s₀ := (k.gpr _ h23).trans hF.r23
  have t27 : t.gpr .r27 = off (cS s₀) (slot (cwX s₀) 0) := (k.gpr _ h27).trans hF.r27
  have t28 : t.gpr .r28 = BitVec.ofNat 64 (8 * (cwX s₀ + 2)) := (k.gpr _ h28).trans hF.r28
  -- `p`'s working space, and its check.
  refine WP.seq (WP.seq (WP.mono (setupP_ok (oA := oPa s₀) (hF.scr.congr k.wr) t23 (by decide) (by decide)
    (by omega_arith) (by rw [hd _ (by decide)]; exact hF.hBP) (by rw [hd _ (by decide)]; exact hF.hPL) p1
    (by omega_arith)) fun t₁ ⟨⟨p10, p21, p29, p11, _, pm⟩, kp⟩ => ?_))
  refine WP.seq (WP.mono (checkR2_ok (q := false) (xj := 4) (Pv := mP false s₀) (b := cb false s₀)
    (hF.scr.congr (k.trans kp).wr) (Nat.le_trans (Nat.le_add_right _ _) room) (Nat.le_refl _) hp2 (by omega_arith) hpw (by decide)
    p10 p21 p29 p11 ((kp.gpr _ (by decide)).trans t23) ((kp.gpr _ (by decide)).trans t27)
    ((kp.gpr _ (by decide)).trans t28)
    (by rw [pm]; exact wv_low (by rw [← Pre.val32_eq_wv]; exact X.v4) mPb hpw) (by omega_arith) mPo
    (F.pS hP hhd (by rw [pm]; exact X.out) (by rw [kp.rd, kp.wr, rd0]) ((kp.gpr _ (by decide)).trans X.r26)))
    fun t₂ ⟨⟨c26, co⟩, kc⟩ => ?_)
  have room' : oPa s₀ + slot (cwP s₀) 24 + slot (cwQ s₀) 24 ≤ cZ s₀ := room
  have hS := F.hS
  have x1 : wv t₁.mem (s₀.gpr .r12) 0 (cwP s₀) = wv s₀.mem (s₀.gpr .r12) 0 (cwP s₀) :=
    wv_entry hF (by rw [pm]; exact X.out) (by omega_arith) (by omega_arith) fun x hx => F.sep x (by omega_arith)
  rw [x1, (kp.gpr _ (by decide)).trans X.r26, bmask_decide, bmask_and] at c26
  change t₂.gpr .r26 = bmask (cb0 s₀ && decide (cxP s₀ = 2 ^ (128 * cwP s₀) % (if cb0 s₀ then vP s₀ else 3)))
    at c26
  have o2 : Outside (cS s₀) 256 (cZ s₀ - 256) s.mem t₂.mem :=
    X.out.trans (by rw [← pm]; exact co.mono (by omega_arith) (by omega_arith))
  have hd2 : ∀ d, d + 8 ≤ 256 → word t₂.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
    o2.word (Or.inl hd) (by omega_arith)
  have k2 := (k.trans kp).trans kc
  -- `q`'s working space, and its check.
  refine WP.seq (WP.mono (setupP_ok (oA := oQa s₀) (hF.scr.congr k2.wr)
    ((kc.gpr _ (by decide)).trans ((kp.gpr _ (by decide)).trans t23)) (by decide) (by decide)
    (by omega_arith) (by rw [hd2 _ (by decide)]; exact hF.hBQ) (by rw [hd2 _ (by decide)]; exact hF.hQL) q1
    (by omega_arith)) fun t₃ ⟨⟨q10, q21, q29, q11, _, qm⟩, kq⟩ => ?_)
  have o3 : Outside (cS s₀) 256 (cZ s₀ - 256) s.mem t₃.mem := by rw [qm]; exact o2
  have v5 : wv t₃.mem (cS s₀) (slot (cwX s₀) 5) (cwQ s₀) = mQ false s₀ := by
    rw [qm, co.wv (Or.inl (by omega_arith)) (by omega_arith), pm]
    exact wv_low (by rw [← Pre.val32_eq_wv]; exact X.v5) mQb hqw
  refine WP.seq (WP.mono (checkR2_ok (q := true) (xj := 5) (Pv := mQ false s₀)
    (hF.scr.congr (k2.trans kq).wr) room' (by omega_arith) hq2 (by omega_arith) hqw (by decide)
    q10 q21 q29 q11 ((kq.gpr _ (by decide)).trans ((kc.gpr _ (by decide)).trans ((kp.gpr _ (by decide)).trans t23)))
    ((kq.gpr _ (by decide)).trans ((kc.gpr _ (by decide)).trans ((kp.gpr _ (by decide)).trans t27)))
    ((kq.gpr _ (by decide)).trans ((kc.gpr _ (by decide)).trans ((kp.gpr _ (by decide)).trans t28)))
    v5 (by omega_arith) mQo
    (F.qS hP hF hhd o3 (by rw [(k2.trans kq).rd, (k2.trans kq).wr, hF.keep.rd, hF.keep.wr])
      ((kq.gpr _ (by decide)).trans c26)))
    fun t₄ ⟨⟨d26, co2⟩, kd⟩ => ?_)
  have x2 : wv t₃.mem (off (s₀.gpr .r12) (8 * cwP s₀)) 0 (cwQ s₀) =
      wv s₀.mem (s₀.gpr .r12) (8 * cwP s₀) (cwQ s₀) := by
    rw [wv_off, Nat.add_zero]
    exact wv_entry hF o3 (by omega_arith) (by omega_arith) fun x hx => F.sep x (by omega_arith)
  rw [x2, (kq.gpr _ (by decide)).trans c26, bmask_decide, bmask_and] at d26
  have hcb : (cb0 s₀ && decide (cxP s₀ = 2 ^ (128 * cwP s₀) % (if cb0 s₀ then vP s₀ else 3)) &&
      decide ((if cb0 s₀ && decide (cxP s₀ = 2 ^ (128 * cwP s₀) % (if cb0 s₀ then vP s₀ else 3)) then
        wv s₀.mem (s₀.gpr .r12) (8 * cwP s₀) (cwQ s₀) else 1) = 2 ^ (128 * cwQ s₀) % mQ false s₀)) =
      cb true s₀ := by
    simp only [cb, cxQ, mQ]
    by_cases hA : cxP s₀ = 2 ^ (128 * cwP s₀) % (if cb0 s₀ then vP s₀ else 3) <;>
      rcases Bool.eq_false_or_eq_true (cb0 s₀) with h0 | h0 <;> simp only [hA, decide_true, decide_false] <;>
      simp [h0]
  rw [hcb] at d26
  have o4 : Outside (cS s₀) 256 (cZ s₀ - 256) s.mem t₄.mem :=
    o3.trans (co2.mono (by omega_arith) (by omega_arith))
  have K4 := kq.trans kd
  -- `X`'s registers back, and the masks.
  refine WP.seq (WP.mono (restoreX_ok (BX := cS s₀) (w := cwX s₀)
    ((K4.gpr _ (by decide)).trans ((kc.gpr _ (by decide)).trans ((kp.gpr _ (by decide)).trans t27)))
    ((K4.gpr _ (by decide)).trans ((kc.gpr _ (by decide)).trans ((kp.gpr _ (by decide)).trans t28))) hwX)
    fun t₅ ⟨⟨a10, a21, a29, a11, am⟩, kr⟩ => ?_)
  have k5 := (k2.trans K4).trans kr
  refine WP.mono (checksB_ok (hF.scr.congr k5.wr) (by omega_arith) (by omega_arith) hwX a10 a29 a11
    ((kr.gpr _ (by decide)).trans d26)) fun u ⟨⟨u4, u5, u7, uO⟩, ku⟩ => ?_
  -- What `X` holds.
  have vt : ∀ j, j < 8 → Mont.val32 t₅.mem (cS s₀) (slot (cwX s₀) j) (2 * cwX s₀) =
      Mont.val32 t.mem (cS s₀) (slot (cwX s₀) j) (2 * cwX s₀) := fun j hj => by
    have := slot_le (w := cwX s₀) hj
    rw [am, Mont.Outside.val32 (fun x hx => co2 x hx) (Or.inl (by omega_arith)) (by omega_arith), qm,
      Mont.Outside.val32 (fun x hx => co x hx) (Or.inl (by omega_arith)) (by omega_arith), pm]
  have ap : ∀ r ∈ [(slot (cwX s₀) 4, 8 * (cwX s₀ + 2)),
      (slot (cwX s₀) 5, 8 * (cwX s₀ + 2)), (slot (cwX s₀) 7, 8 * (cwX s₀ + 2))],
      slot (cwX s₀) 0 + 4 * (2 * cwX s₀) ≤ r.1 ∨ r.1 + r.2 ≤ slot (cwX s₀) 0 := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (simp only [slot, hdrBytes]; omega_arith)
  have v0 := X.v0
  rw [← vt 0 (by decide), ← uO.val32 ap (by omega_arith)] at v0
  have hb : cb true s₀ = true → cb false s₀ = true := fun h => cb_cb0 h
  refine hc u ⟨(ku.gpr _ (by decide)).trans ((kr.gpr _ (by decide)).trans d26), v0, ?_, ?_, ?_, ?_, ?_⟩
    ((ku.gpr _ (by decide)).trans a10) ((ku.gpr _ (by decide)).trans a21) ((ku.gpr _ (by decide)).trans a29)
    ((ku.gpr _ (by decide)).trans a11) ?_
  · have w5 : word u.mem (cS s₀) (slot (cwX s₀) 0) = word t₅.mem (cS s₀) (slot (cwX s₀) 0) :=
      Mont.Outs.word (d := slot (cwX s₀) 0) (fun x hx => uO x hx) (fun r hr => by
        have := ap r hr; have : 1 ≤ cwX s₀ := by omega_arith
        omega_arith) (by omega_arith)
    rw [w5, am,
      co2.word (Or.inl (by omega_arith)) (by omega_arith), qm, co.word (Or.inl (by omega_arith)) (by omega_arith),
      pm]
    exact X.w0
  · rw [u4, vt 4 (by decide), X.v4]
    unfold mP; by_cases h : cb true s₀ = true
    · simp [h, hb h]
    · simp [h]
  · rw [u5, vt 5 (by decide), X.v5]
    unfold mQ; by_cases h : cb true s₀ = true
    · simp [h, hb h]
    · simp [h]
  · rw [u7, vt 7 (by decide), X.v7]
    unfold mQI; by_cases h : cb true s₀ = true
    · simp [h, hb h]
    · simp [h]
  · refine o4.trans fun x hx => ?_
    rw [← am]
    have ho : Mont.ofs (cS s₀) x = ofs (cS s₀) x := rfl
    exact uO x fun r hr => by
      rw [ho]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> (dsimp only; omega_arith)
  · exact (k.trans (kp.trans (kc.trans (kq.trans (kd.trans (kr.trans ku)))))).mono fun r hr => by
      rcases List.mem_append.mp hr with h | h
      · exact List.mem_append.mpr (Or.inl h)
      · exact List.mem_append.mpr (Or.inr (by clear hr; revert h; revert r; decide))

/-- `loadX` and `checksG pc`, after the front: with `pc`, the mask is the
checks' and the cached values' (`checkR2`). -/
theorem mid1A_ok {s₀ s : State} {c : Prog isa} {Q : State → Prop} (hP : PF s₀) (hF : Front s₀ s)
    (hR2 : pc = true → R2F s₀ ∧ word s.mem (cS s₀) oR2 = s₀.gpr .r12)
    (hc : ∀ t, XA pc s₀ s t → t.gpr .r10 = off (cS s₀) (slot (cwX s₀) 0) →
      t.gpr .r21 = off (cS s₀) (slot (cwX s₀) 0) → t.gpr .r29 = BitVec.ofNat 64 (8 * (cwX s₀ + 2)) →
      t.gpr .r11 = BitVec.ofNat 64 (2 * cwX s₀) →
      Keep (loadXRegs ++ checkRegs ++ ([.r0, .r3, .r4, .r14, .r17] : List Reg) ++ valRegs) s t → WP isa c t Q) :
    WP isa (.seq loadX (.seq (checksG pc) c)) s Q := by
  cases pc
  · exact mid1A0_ok hP hF fun t X a10 k => hc t X a10 ((k.gpr _ (by decide)).trans hF.r21)
      ((k.gpr _ (by decide)).trans hF.r29) ((k.gpr _ (by decide)).trans hF.r11) k.mono
  · obtain ⟨F, hhd⟩ := hR2 rfl
    exact wp_inner_assoc (mid1A0_ok hP hF fun t X _ k => mid1V_ok hP hF F hhd X k (by decide)
      (by decide) (by decide) hc)

/-- What `X` holds after `loadIn`: the input again in array 6. -/
structure XL (pc : Bool) (s₀ s t : State) extends XA pc s₀ s t where
  v6 : wv t.mem (cS s₀) (slot (cwX s₀) 6) (cwX s₀) = vC s₀

/-- `loadIn`, after `X`'s checks. -/
theorem mid1L_ok {s₀ s t₁ : State} {c : Prog isa} {Q : State → Prop} (hP : PF s₀) (hF : Front s₀ s)
    (X : XA pc s₀ s t₁) (h10 : t₁.gpr .r10 = off (cS s₀) (slot (cwX s₀) 0))
    (e21 : t₁.gpr .r21 = off (cS s₀) (slot (cwX s₀) 0)) (e29 : t₁.gpr .r29 = BitVec.ofNat 64 (8 * (cwX s₀ + 2)))
    (e11 : t₁.gpr .r11 = BitVec.ofNat 64 (2 * cwX s₀)) {rs : List Reg} (k1 : Keep rs s t₁) (h23 : Reg.r23 ∉ rs)
    (hc : ∀ t, XL pc s₀ s t → t.gpr .r10 = off (cS s₀) (slot (cwX s₀) 0) →
      Keep (rs ++ ([.r0, .r6, .r10, .r12, .r14, .r15, .r16, .r17] : List Reg)) s t → WP isa c t Q) :
    WP isa (.seq loadIn c) t₁ Q := by
  have hn := hP.nw
  have room := hP.room
  have k64 := hP.k64; have k1024 := hP.k1024
  have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  have eX0 := e (cwX s₀) 0; have eX4 := e (cwX s₀) 4; have eX5 := e (cwX s₀) 5; have eX6 := e (cwX s₀) 6
  have eX7 := e (cwX s₀) 7; have eX8 := e (cwX s₀) 8
  have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
  have hwX : cwX s₀ < 2 ^ 31 := by rw [dX]; omega_arith
  have k0 := hF.keep
  have rd1 : t₁.rd ++ t₁.wr = s₀.rd ++ s₀.wr := by rw [k1.rd, k1.wr, k0.rd, k0.wr]
  have hd1 : ∀ d, d + 8 ≤ 256 → word t₁.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
    X.out.word (Or.inl hd) (by omega_arith)
  unfold loadIn
  refine WP.seq (WP.mono (loadOne_ok (j := 6) (A := s₀.gpr .r7) (L := ck s₀) (hF.scr.congr k1.wr) (by omega_arith)
    (by decide) hwX ((k1.gpr _ h23).trans hF.r23) h10 e21 e29 e11 (by decide) (by decide) (by rw [hd1 _ (by decide)]; exact hF.hIn)
    (by rw [hd1 _ (by decide)]; exact hF.hNL) (by omega_arith) (by omega_arith) (by rw [rd1]; exact hP.rI) hP.sI)
    fun t ⟨⟨v6, _, O, t10⟩, k2⟩ => ?_)
  have hb : Spec.Rsa.bytesAt t₁.mem (s₀.gpr .r7) (ck s₀) = Spec.Rsa.bytesAt s₀.mem (s₀.gpr .r7) (ck s₀) := by
    rw [bytesAt_out X.out (by omega_arith) hP.sI, bytesAt_out hF.mem (by omega_arith) hP.sI]
  refine hc t ⟨⟨(k2.gpr _ (by decide)).trans X.r26,
    by rw [xval O (Or.inl (by omega_arith)) (by omega_arith)]; exact X.v0,
    by rw [O.word (Or.inl (by omega_arith)) (by omega_arith)]; exact X.w0,
    by rw [xval O (Or.inl (by omega_arith)) (by omega_arith)]; exact X.v4,
    by rw [xval O (Or.inl (by omega_arith)) (by omega_arith)]; exact X.v5,
    by rw [xval O (Or.inr (by omega_arith)) (by omega_arith)]; exact X.v7,
    X.out.trans (O.mono (by omega_arith) (by omega_arith))⟩, by rw [← Pre.val32_eq_wv, v6, hb]⟩ t10 (k1.trans k2)

/-- What `p`'s working space holds after its power. -/
structure XP (pc : Bool) (s₀ s t : State) extends XL pc s₀ s t where
  p0 : Mont.val32 t.mem (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 0) (2 * cwP s₀) = mP pc s₀
  p4 : Mont.val32 t.mem (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 4) (2 * cwP s₀) = vC s₀ ^ vDP s₀ % mP pc s₀

/-- `m₁`, after `X`'s checks. -/
theorem mid1B_ok {pc : Bool} {s₀ s t₁ : State} {c : Prog isa} {Q : State → Prop} (hP : PF s₀)
    (hF : Front s₀ s) (hR2 : pc = true → R2F s₀ ∧ word s.mem (cS s₀) oR2 = s₀.gpr .r12)
    (X : XL pc s₀ s t₁) {rs : List Reg} (k1 : Keep rs s t₁) (h23 : Reg.r23 ∉ rs) (h27 : Reg.r27 ∉ rs)
    (h28 : Reg.r28 ∉ rs)
    (hc : ∀ t, XP pc s₀ s t → Keep (rs ++ (([.r0, .r3, .r4, .r10, .r11, .r21, .r29] : List Reg) ++ powerRegs)) s t →
      WP isa c t Q) :
    WP isa (.seq (.block (setupP oBP oPLen)) (.seq (powerG pc false 4 oDP oPLen) c)) t₁ Q := by
  have hn := hP.nw
  have room := hP.room
  have pq := hP.pq
  have k64 := hP.k64; have k1024 := hP.k1024; have p1 := hP.p1; have pk := hP.pk; have q1 := hP.q1
  have qk := hP.qk
  have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  have eX0 := e (cwX s₀) 0; have eX5 := e (cwX s₀) 5; have eX7 := e (cwX s₀) 7; have eX8 := e (cwX s₀) 8
  have eP0 := e (cwP s₀) 0; have eP4 := e (cwP s₀) 4; have eP8 := e (cwP s₀) 24
  have eQ4 := e (cwQ s₀) 4; have eQ8 := e (cwQ s₀) 24; have eQ0 := e (cwQ s₀) 0
  have dZ : cZ s₀ = (stackArg s₀ 9).toNat * 8 := rfl
  have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
  have dk : ck s₀ = (s₀.gpr .r6).toNat := rfl
  have dp : cpL s₀ = (s₀.gpr .r10).toNat := rfl
  have dq : cqL s₀ = (stackArg s₀ 1).toNat := rfl
  have dP : cwP s₀ = wsWords (cpL s₀) := rfl
  have dQ : cwQ s₀ = wsWords (cqL s₀) := rfl
  have doP : oPa s₀ = slot (cwX s₀) 8 := rfl
  have doQ : oQa s₀ = slot (cwX s₀) 8 + slot (cwP s₀) 24 := rfl
  have dS : cS s₀ = stackArg s₀ 8 := rfl
  have fP8 := e (wsWords (cpL s₀)) 24; have fQ8 := e (wsWords (cqL s₀)) 24
  have fX8 := e (2 * ((ck s₀ + 7) / 8)) 8
  have hwX : cwX s₀ < 2 ^ 31 := by unfold cwX ck; omega_arith
  have k0 := hF.keep
  have rd0 : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [k0.rd, k0.wr]
  have hb0 : ∀ {A : Addr} {L : Nat}, (∀ i < L, ∀ x, ofs (cS s₀) x < cZ s₀ → off A i ≠ x) →
      Spec.Rsa.bytesAt s.mem A L = Spec.Rsa.bytesAt s₀.mem A L := fun hs' => bytesAt_out hF.mem (by omega_arith) hs'
  obtain ⟨mP1, mPo, mQ1, mQo, mPb, mQb, _, mQIP, mQIb⟩ := masked_facts hP
  have eX4 := e (cwX s₀) 4; have eX6 := e (cwX s₀) 6
  have hd1 : ∀ d, d + 8 ≤ 256 → word t₁.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
    X.out.word (Or.inl hd) (by omega_arith)
  have hb1 : ∀ {A : Addr} {L : Nat}, (∀ i < L, ∀ x, ofs (cS s₀) x < cZ s₀ → off A i ≠ x) →
      Spec.Rsa.bytesAt t₁.mem A L = Spec.Rsa.bytesAt s₀.mem A L := fun hs' => by
    rw [bytesAt_out X.out (by omega_arith) hs']; exact hb0 hs'
  have rd1 : t₁.rd ++ t₁.wr = s₀.rd ++ s₀.wr := by rw [k1.rd, k1.wr, rd0]
  refine wp_reassoc2 (WP.seq (WP.mono (phaseP_ok (xj := 4) (oA := oPa s₀) (L := cpL s₀) (k := ck s₀)
    (D := stackArg s₀ 2) (Pv := mP pc s₀) (Cv := vC s₀) (hF.scr.congr k1.wr) (by omega_arith) (Nat.le_refl _)
    rfl (by unfold wsWords; omega_arith) hwX (by decide) ((k1.gpr _ h23).trans hF.r23) ((k1.gpr _ h27).trans hF.r27)
    ((k1.gpr _ h28).trans hF.r28) (by decide) (by decide) (by decide)
    (by rw [hd1 _ (by decide)]; exact hF.hBP) (by rw [hd1 _ (by decide)]; exact hF.hPL)
    (by rw [hd1 _ (by decide)]; exact hF.hNL)
    (by rw [hd1 _ (by decide)]; exact hF.hDP) p1 (by omega_arith) (by omega_arith) (by omega_arith)
    (by rw [rd1]; exact hP.rDP) hP.sDP
    X.v4 mPb (by omega_arith) mPo X.v6 (os2ip_lt' _ (VG.Proof.Bignum.bytesAt_length _ _ _))
    (fun hp => by subst hp; exact ⟨_, _, _, (hR2 rfl).1.p hP hF (hR2 rfl).2 X.out rd1 X.r26⟩))
    fun t₂ ⟨⟨p0, p4, O2, _, _, _, _⟩, k2⟩ => ?_))
  rw [hb1 hP.sDP] at p4
  exact hc t₂ ⟨⟨⟨(k2.gpr _ (by decide)).trans X.r26,
    by rw [xval O2 (Or.inl (by omega_arith)) (by omega_arith)]; exact X.v0,
    by rw [O2.word (Or.inl (by omega_arith)) (by omega_arith)]; exact X.w0,
    by rw [xval O2 (Or.inl (by omega_arith)) (by omega_arith)]; exact X.v4,
    by rw [xval O2 (Or.inl (by omega_arith)) (by omega_arith)]; exact X.v5,
    by rw [xval O2 (Or.inl (by omega_arith)) (by omega_arith)]; exact X.v7,
    X.out.trans (O2.mono (by omega_arith) (by omega_arith))⟩,
    by rw [O2.wv (Or.inl (by omega_arith)) (by omega_arith)]; exact X.v6⟩, p0, p4⟩ (k1.trans k2)

theorem mid1_ok {pc : Bool} {s₀ s : State} {c : Prog isa} {Q : State → Prop} (hP : PF s₀) (hF : Front s₀ s)
    (hR2 : pc = true → R2F s₀ ∧ word s.mem (cS s₀) oR2 = s₀.gpr .r12)
    (hc : ∀ t, t.gpr .r26 = bmask (cb pc s₀) →
      Mont.val32 t.mem (cS s₀) (slot (cwX s₀) 0) (2 * cwX s₀) = 2 ^ (64 * cwX s₀) - 1 →
      word t.mem (cS s₀) (slot (cwX s₀) 0) = BitVec.allOnes 64 →
      Mont.val32 t.mem (cS s₀) (slot (cwX s₀) 5) (2 * cwX s₀) = mQ pc s₀ →
      Mont.val32 t.mem (cS s₀) (slot (cwX s₀) 7) (2 * cwX s₀) = mQI pc s₀ →
      Mont.val32 t.mem (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 0) (2 * cwP s₀) = mP pc s₀ →
      Mont.val32 t.mem (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 4) (2 * cwP s₀) = vC s₀ ^ vDP s₀ % mP pc s₀ →
      Mont.val32 t.mem (off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 4) (2 * cwQ s₀) = vC s₀ ^ vDQ s₀ % mQ pc s₀ →
      t.gpr .r10 = off (off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 0) →
      t.gpr .r29 = BitVec.ofNat 64 (8 * (cwQ s₀ + 2)) →
      Outside (cS s₀) 256 (cZ s₀ - 256) s.mem t.mem →
      Keep mid1Regs s t → WP isa c t Q) :
    WP isa (.seq loadX (.seq (checksG pc) (.seq loadIn (.seq (.block (setupP oBP oPLen)) (.seq (powerG pc false 4 oDP oPLen)
      (.seq (.block (setupP oBQ oQLen)) (.seq (powerG pc true 5 oDQ oQLen) c))))))) s Q := by
  have hn := hP.nw
  have room := hP.room
  have pq := hP.pq
  have k64 := hP.k64; have k1024 := hP.k1024; have p1 := hP.p1; have pk := hP.pk; have q1 := hP.q1
  have qk := hP.qk
  have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  have eX0 := e (cwX s₀) 0; have eX5 := e (cwX s₀) 5; have eX7 := e (cwX s₀) 7; have eX8 := e (cwX s₀) 8
  have eP0 := e (cwP s₀) 0; have eP4 := e (cwP s₀) 4; have eP8 := e (cwP s₀) 24
  have eQ4 := e (cwQ s₀) 4; have eQ8 := e (cwQ s₀) 24; have eQ0 := e (cwQ s₀) 0
  have dZ : cZ s₀ = (stackArg s₀ 9).toNat * 8 := rfl
  have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
  have dk : ck s₀ = (s₀.gpr .r6).toNat := rfl
  have dp : cpL s₀ = (s₀.gpr .r10).toNat := rfl
  have dq : cqL s₀ = (stackArg s₀ 1).toNat := rfl
  have dP : cwP s₀ = wsWords (cpL s₀) := rfl
  have dQ : cwQ s₀ = wsWords (cqL s₀) := rfl
  have doP : oPa s₀ = slot (cwX s₀) 8 := rfl
  have doQ : oQa s₀ = slot (cwX s₀) 8 + slot (cwP s₀) 24 := rfl
  have dS : cS s₀ = stackArg s₀ 8 := rfl
  have fP8 := e (wsWords (cpL s₀)) 24; have fQ8 := e (wsWords (cqL s₀)) 24
  have fX8 := e (2 * ((ck s₀ + 7) / 8)) 8
  have hwX : cwX s₀ < 2 ^ 31 := by rw [dX]; omega_arith
  have k0 := hF.keep
  have rd0 : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [k0.rd, k0.wr]
  have hb0 : ∀ {A : Addr} {L : Nat}, (∀ i < L, ∀ x, ofs (cS s₀) x < cZ s₀ → off A i ≠ x) →
      Spec.Rsa.bytesAt s.mem A L = Spec.Rsa.bytesAt s₀.mem A L := fun hs' => bytesAt_out hF.mem (by omega_arith) hs'
  obtain ⟨mP1, mPo, mQ1, mQo, mPb, mQb, _, mQIP, mQIb⟩ := masked_facts hP
  refine mid1A_ok hP hF hR2 fun t₀ X₀ a10 a21 a29 a11 k0' => ?_
  refine mid1L_ok hP hF X₀ a10 a21 a29 a11 k0' (by decide) fun t₁ X _ k1 => ?_
  refine mid1B_ok hP hF hR2 X k1 (by decide) (by decide) (by decide) fun t₂ Y k12 => ?_
  have hd2 : ∀ d, d + 8 ≤ 256 → word t₂.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
    Y.out.word (Or.inl hd) (by omega_arith)
  have hb2 : ∀ {A : Addr} {L : Nat}, (∀ i < L, ∀ x, ofs (cS s₀) x < cZ s₀ → off A i ≠ x) →
      Spec.Rsa.bytesAt t₂.mem A L = Spec.Rsa.bytesAt s₀.mem A L := fun hs' => by
    rw [bytesAt_out Y.out (by omega_arith) hs']; exact hb0 hs'
  -- `m₂`.
  refine wp_reassoc2 (WP.seq (WP.mono (phaseP_ok (xj := 5) (oA := oQa s₀) (L := cqL s₀) (k := ck s₀)
    (D := stackArg s₀ 4) (Pv := mQ pc s₀) (Cv := vC s₀) (hF.scr.congr k12.wr) (by omega_arith) (by omega_arith)
    rfl (by unfold wsWords; omega_arith) hwX (by decide) ((k12.gpr _ (by decide)).trans hF.r23)
    ((k12.gpr _ (by decide)).trans hF.r27)
    ((k12.gpr _ (by decide)).trans hF.r28) (by decide) (by decide) (by decide)
    (by rw [hd2 _ (by decide)]; exact hF.hBQ) (by rw [hd2 _ (by decide)]; exact hF.hQL)
    (by rw [hd2 _ (by decide)]; exact hF.hNL)
    (by rw [hd2 _ (by decide)]; exact hF.hDQ) q1 (by omega_arith) (by omega_arith) (by omega_arith)
    (by rw [k12.rd, k12.wr, rd0]; exact hP.rDQ) hP.sDQ
    Y.v5 mQb (by omega_arith) mQo Y.v6 (os2ip_lt' _ (VG.Proof.Bignum.bytesAt_length _ _ _))
    (fun hp => by subst hp; exact ⟨_, _, _, (hR2 rfl).1.q hP hF (hR2 rfl).2 Y.out (by rw [k12.rd, k12.wr, rd0]) Y.r26⟩))
    fun t₃ ⟨⟨_, q4, O3, c10, _, c29, _⟩, k3⟩ => ?_))
  rw [hb2 hP.sDQ] at q4
  have k13 := k12.trans k3
  refine hc t₃ ((k3.gpr _ (by decide)).trans Y.r26)
    (by rw [xval O3 (Or.inl (by omega_arith)) (by omega_arith)]; exact Y.v0)
    (by rw [O3.word (Or.inl (by omega_arith)) (by omega_arith)]; exact Y.w0)
    (by rw [xval O3 (Or.inl (by omega_arith)) (by omega_arith)]; exact Y.v5)
    (by rw [xval O3 (Or.inl (by omega_arith)) (by omega_arith)]; exact Y.v7)
    (by rw [val32_off_eq O3 (Or.inl (by omega_arith)) (by omega_arith)]; exact Y.p0)
    (by rw [val32_off_eq O3 (Or.inl (by omega_arith)) (by omega_arith)]; exact Y.p4) q4 c10 c29
    (Y.out.trans (O3.mono (by omega_arith) (by omega_arith))) k13

end VG.Proof.Bignum.PPC64LE.Crt

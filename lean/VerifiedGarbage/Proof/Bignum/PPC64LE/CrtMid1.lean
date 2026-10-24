module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Bignum.CrtFrame
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPre
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPhaseA
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPhaseP
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtVals
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtLoadX
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPowerA
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtRecX
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore

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

/-- The numbers of the entry state `s₀`. -/
abbrev vN (s₀ : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .r5) (ck s₀))
abbrev vC (s₀ : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .r7) (ck s₀))
abbrev vP (s₀ : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (s₀.gpr .r9) (cpL s₀))
abbrev vQ (s₀ : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (stackArg s₀ 0) (cqL s₀))
abbrev vDP (s₀ : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (stackArg s₀ 2) (cpL s₀))
abbrev vDQ (s₀ : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (stackArg s₀ 4) (cqL s₀))
abbrev vQI (s₀ : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₀.mem (stackArg s₀ 6) (cpL s₀))
/-- The mask. -/
abbrev cb (s₀ : State) : Bool := crtMask (vN s₀) (ck s₀) (vC s₀) (vP s₀) (vQ s₀) (vQI s₀)
/-- The masked `p`, `q` and `qInv`. -/
abbrev mP (s₀ : State) : Nat := if cb s₀ then vP s₀ else 3
abbrev mQ (s₀ : State) : Nat := if cb s₀ then vQ s₀ else 3
abbrev mQI (s₀ : State) : Nat := if cb s₀ then vQI s₀ else 0
/-- `wP`, `wQ`, and the offsets of `P` and `Q`. -/
abbrev cwP (s₀ : State) : Nat := wsWords (cpL s₀)
abbrev cwQ (s₀ : State) : Nat := wsWords (cqL s₀)
abbrev oPa (s₀ : State) : Nat := slot (cwX s₀) 8
abbrev oQa (s₀ : State) : Nat := slot (cwX s₀) 8 + slot (cwP s₀) 8

/-- What the masked numbers satisfy. -/
theorem masked_facts {s₀ : State} (hP : PF s₀) :
    1 < mP s₀ ∧ mP s₀ % 2 = 1 ∧ 1 < mQ s₀ ∧ mQ s₀ % 2 = 1 ∧ mP s₀ < 2 ^ (64 * cwP s₀) ∧
      mQ s₀ < 2 ^ (64 * cwQ s₀) ∧ mQ s₀ ≤ 256 ^ cqL s₀ ∧ mQI s₀ < mP s₀ ∧ mQI s₀ < 2 ^ (64 * cwP s₀) := by
  have hpw : cpL s₀ ≤ 8 * cwP s₀ := by unfold cwP wsWords; omega
  have hqw : cqL s₀ ≤ 8 * cwQ s₀ := by unfold cwQ wsWords; omega
  have h3p : 3 < 2 ^ (64 * cwP s₀) := Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (n := 2) (by decide)
    (show 2 ≤ 64 * cwP s₀ by unfold cwP wsWords; omega))
  have h3q : 3 < 2 ^ (64 * cwQ s₀) := Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (n := 2) (by decide)
    (show 2 ≤ 64 * cwQ s₀ by unfold cwQ wsWords; omega))
  have h3 : 3 ≤ 256 ^ cqL s₀ := Nat.le_trans (by decide) (Nat.pow_le_pow_right (n := 256) (by decide) hP.q1)
  unfold mP mQ mQI
  cases hb : cb s₀
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨by decide, by decide, by decide, by decide, h3p, h3q, h3, by decide, by omega⟩
  · simp only [↓reduceIte]
    obtain ⟨_, _, hi, _, hp1, hpo, hq1, hqo⟩ := mask_true hP.k64
      (by rw [VG.Proof.Bignum.bytesAt_length]; exact hP.pk) (by rw [VG.Proof.Bignum.bytesAt_length]; exact hP.qk) hb
    exact ⟨hp1, hpo, hq1, hqo, Nat.lt_of_lt_of_le (os2ip_lt' _ (VG.Proof.Bignum.bytesAt_length _ _ _)) (pow256_le hpw),
      Nat.lt_of_lt_of_le (os2ip_lt' _ (VG.Proof.Bignum.bytesAt_length _ _ _)) (pow256_le hqw),
      Nat.le_of_lt (os2ip_lt' _ (VG.Proof.Bignum.bytesAt_length _ _ _)), hi,
      Nat.lt_of_lt_of_le (os2ip_lt' _ (VG.Proof.Bignum.bytesAt_length _ _ _)) (pow256_le hpw)⟩

theorem xval {m m' : Mem} {B : Addr} {a n d w : Nat} (h : Outside B a n m m') (hd : d + 8 * w ≤ a ∨ a + n ≤ d)
    (hd' : d + 8 * w ≤ 2 ^ 64) : Mont.val32 m' B d (2 * w) = Mont.val32 m B d (2 * w) := by
  rw [Pre.val32_eq_wv, Pre.val32_eq_wv, h.wv hd hd']

/-- The registers of `mid1`. -/
def mid1Regs : List Reg := loadXRegs ++ checkRegs ++ [.r0, .r3, .r4, .r14, .r17] ++
  ([.r0, .r3, .r4, .r10, .r11, .r21, .r29] ++ powerRegs)

/-- What `X` holds after `loadX` and `checks`. -/
structure XA (s₀ s t : State) : Prop where
  r26 : t.gpr .r26 = bmask (cb s₀)
  v0 : Mont.val32 t.mem (cS s₀) (slot (cwX s₀) 0) (2 * cwX s₀) = 2 ^ (64 * cwX s₀) - 1
  w0 : word t.mem (cS s₀) (slot (cwX s₀) 0) = BitVec.allOnes 64
  v4 : Mont.val32 t.mem (cS s₀) (slot (cwX s₀) 4) (2 * cwX s₀) = mP s₀
  v5 : Mont.val32 t.mem (cS s₀) (slot (cwX s₀) 5) (2 * cwX s₀) = mQ s₀
  v7 : Mont.val32 t.mem (cS s₀) (slot (cwX s₀) 7) (2 * cwX s₀) = mQI s₀
  out : Outside (cS s₀) 256 (cZ s₀ - 256) s.mem t.mem

/-- `loadX` and `checks`, after the front. -/
theorem mid1A_ok {s₀ s : State} {c : Prog isa} {Q : State → Prop} (hP : PF s₀) (hF : Front s₀ s)
    (hc : ∀ t, XA s₀ s t → t.gpr .r10 = off (cS s₀) (slot (cwX s₀) 0) →
      Keep (loadXRegs ++ checkRegs ++ [.r0, .r3, .r4, .r14, .r17]) s t → WP isa c t Q) :
    WP isa (.seq loadX (.seq checks c)) s Q := by
  have hn := hP.nw
  have room := hP.room
  have pq := hP.pq
  have k64 := hP.k64; have k1024 := hP.k1024; have p1 := hP.p1; have pk := hP.pk; have q1 := hP.q1
  have qk := hP.qk
  have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  have eX0 := e (cwX s₀) 0; have eX5 := e (cwX s₀) 5; have eX7 := e (cwX s₀) 7; have eX8 := e (cwX s₀) 8
  have eP0 := e (cwP s₀) 0; have eP4 := e (cwP s₀) 4; have eP8 := e (cwP s₀) 8
  have eQ4 := e (cwQ s₀) 4; have eQ8 := e (cwQ s₀) 8; have eQ0 := e (cwQ s₀) 0
  have dZ : cZ s₀ = (stackArg s₀ 9).toNat * 8 := rfl
  have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
  have dk : ck s₀ = (s₀.gpr .r6).toNat := rfl
  have dp : cpL s₀ = (s₀.gpr .r10).toNat := rfl
  have dq : cqL s₀ = (stackArg s₀ 1).toNat := rfl
  have dP : cwP s₀ = wsWords (cpL s₀) := rfl
  have dQ : cwQ s₀ = wsWords (cqL s₀) := rfl
  have doP : oPa s₀ = slot (cwX s₀) 8 := rfl
  have doQ : oQa s₀ = slot (cwX s₀) 8 + slot (cwP s₀) 8 := rfl
  have dS : cS s₀ = stackArg s₀ 8 := rfl
  have fP8 := e (wsWords (cpL s₀)) 8; have fQ8 := e (wsWords (cqL s₀)) 8
  have fX8 := e (2 * ((ck s₀ + 7) / 8)) 8
  have hwX : cwX s₀ < 2 ^ 31 := by unfold cwX ck; omega
  have k0 := hF.keep
  have rd0 : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [k0.rd, k0.wr]
  have hb0 : ∀ {A : Addr} {L : Nat}, (∀ i < L, ∀ x, ofs (cS s₀) x < cZ s₀ → off A i ≠ x) →
      Spec.Rsa.bytesAt s.mem A L = Spec.Rsa.bytesAt s₀.mem A L := fun hs' => bytesAt_out hF.mem (by omega) hs'
  obtain ⟨mP1, mPo, mQ1, mQo, mPb, mQb, _, mQIP, mQIb⟩ := masked_facts hP
  refine wp_reassoc2 (WP.seq (WP.mono (phaseA_ok hF.scr (by omega) k64 k1024 hF.r23 hF.r10 hF.r21 hF.r29 hF.r11
    hF.hN hF.hNL hF.hP hF.hPL hF.hQ hF.hQL hF.hIn hF.hQI p1 pk q1 qk (by rw [rd0]; exact hP.rN) hP.sN
    (by rw [rd0]; exact hP.rP) hP.sP (by rw [rd0]; exact hP.rQ) hP.sQ (by rw [rd0]; exact hP.rI) hP.sI
    (by rw [rd0]; exact hP.rQI) hP.sQI) fun t₁ ⟨⟨t26, v0, w0, v4, v5, v7, O1, a10⟩, k1⟩ => ?_))
  rw [hb0 hP.sN, hb0 hP.sI, hb0 hP.sP, hb0 hP.sQ, hb0 hP.sQI] at t26 v4 v5 v7
  exact hc t₁ ⟨t26, v0, w0, v4, v5, v7, O1.mono (by omega) (by omega)⟩ a10 k1

/-- What `p`'s working space holds after its power. -/
structure XP (s₀ s t : State) extends XA s₀ s t where
  p0 : Mont.val32 t.mem (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 0) (2 * cwP s₀) = mP s₀
  p4 : Mont.val32 t.mem (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 4) (2 * cwP s₀) = vC s₀ ^ vDP s₀ % mP s₀

/-- `m₁`, after `X`'s checks. -/
theorem mid1B_ok {s₀ s t₁ : State} {c : Prog isa} {Q : State → Prop} (hP : PF s₀) (hF : Front s₀ s)
    (X : XA s₀ s t₁) {rs : List Reg} (k1 : Keep rs s t₁) (h23 : Reg.r23 ∉ rs) (h27 : Reg.r27 ∉ rs)
    (h28 : Reg.r28 ∉ rs)
    (hc : ∀ t, XP s₀ s t → Keep (rs ++ ([.r0, .r3, .r4, .r10, .r11, .r21, .r29] ++ powerRegs)) s t →
      WP isa c t Q) :
    WP isa (.seq (.block (setupP oBP oPLen)) (.seq (power 4 oDP oPLen) c)) t₁ Q := by
  have hn := hP.nw
  have room := hP.room
  have pq := hP.pq
  have k64 := hP.k64; have k1024 := hP.k1024; have p1 := hP.p1; have pk := hP.pk; have q1 := hP.q1
  have qk := hP.qk
  have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  have eX0 := e (cwX s₀) 0; have eX5 := e (cwX s₀) 5; have eX7 := e (cwX s₀) 7; have eX8 := e (cwX s₀) 8
  have eP0 := e (cwP s₀) 0; have eP4 := e (cwP s₀) 4; have eP8 := e (cwP s₀) 8
  have eQ4 := e (cwQ s₀) 4; have eQ8 := e (cwQ s₀) 8; have eQ0 := e (cwQ s₀) 0
  have dZ : cZ s₀ = (stackArg s₀ 9).toNat * 8 := rfl
  have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
  have dk : ck s₀ = (s₀.gpr .r6).toNat := rfl
  have dp : cpL s₀ = (s₀.gpr .r10).toNat := rfl
  have dq : cqL s₀ = (stackArg s₀ 1).toNat := rfl
  have dP : cwP s₀ = wsWords (cpL s₀) := rfl
  have dQ : cwQ s₀ = wsWords (cqL s₀) := rfl
  have doP : oPa s₀ = slot (cwX s₀) 8 := rfl
  have doQ : oQa s₀ = slot (cwX s₀) 8 + slot (cwP s₀) 8 := rfl
  have dS : cS s₀ = stackArg s₀ 8 := rfl
  have fP8 := e (wsWords (cpL s₀)) 8; have fQ8 := e (wsWords (cqL s₀)) 8
  have fX8 := e (2 * ((ck s₀ + 7) / 8)) 8
  have hwX : cwX s₀ < 2 ^ 31 := by unfold cwX ck; omega
  have k0 := hF.keep
  have rd0 : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [k0.rd, k0.wr]
  have hb0 : ∀ {A : Addr} {L : Nat}, (∀ i < L, ∀ x, ofs (cS s₀) x < cZ s₀ → off A i ≠ x) →
      Spec.Rsa.bytesAt s.mem A L = Spec.Rsa.bytesAt s₀.mem A L := fun hs' => bytesAt_out hF.mem (by omega) hs'
  obtain ⟨mP1, mPo, mQ1, mQo, mPb, mQb, _, mQIP, mQIb⟩ := masked_facts hP
  have eX4 := e (cwX s₀) 4
  have hd1 : ∀ d, d + 8 ≤ 256 → word t₁.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
    X.out.word (Or.inl hd) (by omega)
  have hb1 : ∀ {A : Addr} {L : Nat}, (∀ i < L, ∀ x, ofs (cS s₀) x < cZ s₀ → off A i ≠ x) →
      Spec.Rsa.bytesAt t₁.mem A L = Spec.Rsa.bytesAt s₀.mem A L := fun hs' => by
    rw [bytesAt_out X.out (by omega) hs']; exact hb0 hs'
  have rd1 : t₁.rd ++ t₁.wr = s₀.rd ++ s₀.wr := by rw [k1.rd, k1.wr, rd0]
  refine wp_reassoc2 (WP.seq (WP.mono (phaseP_ok (xj := 4) (oA := oPa s₀) (L := cpL s₀) (k := ck s₀)
    (I := s₀.gpr .r7) (D := stackArg s₀ 2) (Pv := mP s₀) (hF.scr.congr k1.wr) (by omega) (Nat.le_refl _)
    (by omega) hwX (by decide) ((k1.gpr _ h23).trans hF.r23) ((k1.gpr _ h27).trans hF.r27)
    ((k1.gpr _ h28).trans hF.r28) (by decide) (by decide) (by decide)
    (by rw [hd1 _ (by decide)]; exact hF.hBP) (by rw [hd1 _ (by decide)]; exact hF.hPL)
    (by rw [hd1 _ (by decide)]; exact hF.hIn) (by rw [hd1 _ (by decide)]; exact hF.hNL)
    (by rw [hd1 _ (by decide)]; exact hF.hDP) p1 (by omega) (by omega) (by omega)
    (by rw [rd1]; exact hP.rI) hP.sI (by rw [rd1]; exact hP.rDP) hP.sDP
    X.v4 mPb (by omega) mPo) fun t₂ ⟨⟨p0, p4, O2, _, _, _, _⟩, k2⟩ => ?_))
  rw [hb1 hP.sI, hb1 hP.sDP] at p4
  exact hc t₂ ⟨⟨(k2.gpr _ (by decide)).trans X.r26,
    by rw [xval O2 (Or.inl (by omega)) (by omega)]; exact X.v0,
    by rw [O2.word (Or.inl (by omega)) (by omega)]; exact X.w0,
    by rw [xval O2 (Or.inl (by omega)) (by omega)]; exact X.v4,
    by rw [xval O2 (Or.inl (by omega)) (by omega)]; exact X.v5,
    by rw [xval O2 (Or.inl (by omega)) (by omega)]; exact X.v7,
    X.out.trans (O2.mono (by omega) (by omega))⟩, p0, p4⟩ (k1.trans k2)

theorem mid1_ok {s₀ s : State} {c : Prog isa} {Q : State → Prop} (hP : PF s₀) (hF : Front s₀ s)
    (hc : ∀ t, t.gpr .r26 = bmask (cb s₀) →
      Mont.val32 t.mem (cS s₀) (slot (cwX s₀) 0) (2 * cwX s₀) = 2 ^ (64 * cwX s₀) - 1 →
      word t.mem (cS s₀) (slot (cwX s₀) 0) = BitVec.allOnes 64 →
      Mont.val32 t.mem (cS s₀) (slot (cwX s₀) 5) (2 * cwX s₀) = mQ s₀ →
      Mont.val32 t.mem (cS s₀) (slot (cwX s₀) 7) (2 * cwX s₀) = mQI s₀ →
      Mont.val32 t.mem (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 0) (2 * cwP s₀) = mP s₀ →
      Mont.val32 t.mem (off (cS s₀) (oPa s₀)) (slot (cwP s₀) 4) (2 * cwP s₀) = vC s₀ ^ vDP s₀ % mP s₀ →
      Mont.val32 t.mem (off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 4) (2 * cwQ s₀) = vC s₀ ^ vDQ s₀ % mQ s₀ →
      t.gpr .r10 = off (off (cS s₀) (oQa s₀)) (slot (cwQ s₀) 0) →
      t.gpr .r29 = BitVec.ofNat 64 (8 * (cwQ s₀ + 2)) →
      Outside (cS s₀) 256 (cZ s₀ - 256) s.mem t.mem →
      Keep mid1Regs s t → WP isa c t Q) :
    WP isa (.seq loadX (.seq checks (.seq (.block (setupP oBP oPLen)) (.seq (power 4 oDP oPLen)
      (.seq (.block (setupP oBQ oQLen)) (.seq (power 5 oDQ oQLen) c)))))) s Q := by
  have hn := hP.nw
  have room := hP.room
  have pq := hP.pq
  have k64 := hP.k64; have k1024 := hP.k1024; have p1 := hP.p1; have pk := hP.pk; have q1 := hP.q1
  have qk := hP.qk
  have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  have eX0 := e (cwX s₀) 0; have eX5 := e (cwX s₀) 5; have eX7 := e (cwX s₀) 7; have eX8 := e (cwX s₀) 8
  have eP0 := e (cwP s₀) 0; have eP4 := e (cwP s₀) 4; have eP8 := e (cwP s₀) 8
  have eQ4 := e (cwQ s₀) 4; have eQ8 := e (cwQ s₀) 8; have eQ0 := e (cwQ s₀) 0
  have dZ : cZ s₀ = (stackArg s₀ 9).toNat * 8 := rfl
  have dX : cwX s₀ = 2 * ((ck s₀ + 7) / 8) := rfl
  have dk : ck s₀ = (s₀.gpr .r6).toNat := rfl
  have dp : cpL s₀ = (s₀.gpr .r10).toNat := rfl
  have dq : cqL s₀ = (stackArg s₀ 1).toNat := rfl
  have dP : cwP s₀ = wsWords (cpL s₀) := rfl
  have dQ : cwQ s₀ = wsWords (cqL s₀) := rfl
  have doP : oPa s₀ = slot (cwX s₀) 8 := rfl
  have doQ : oQa s₀ = slot (cwX s₀) 8 + slot (cwP s₀) 8 := rfl
  have dS : cS s₀ = stackArg s₀ 8 := rfl
  have fP8 := e (wsWords (cpL s₀)) 8; have fQ8 := e (wsWords (cqL s₀)) 8
  have fX8 := e (2 * ((ck s₀ + 7) / 8)) 8
  have hwX : cwX s₀ < 2 ^ 31 := by unfold cwX ck; omega
  have k0 := hF.keep
  have rd0 : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [k0.rd, k0.wr]
  have hb0 : ∀ {A : Addr} {L : Nat}, (∀ i < L, ∀ x, ofs (cS s₀) x < cZ s₀ → off A i ≠ x) →
      Spec.Rsa.bytesAt s.mem A L = Spec.Rsa.bytesAt s₀.mem A L := fun hs' => bytesAt_out hF.mem (by omega) hs'
  obtain ⟨mP1, mPo, mQ1, mQo, mPb, mQb, _, mQIP, mQIb⟩ := masked_facts hP
  refine mid1A_ok hP hF fun t₁ X _ k1 => ?_
  refine mid1B_ok hP hF X k1 (by decide) (by decide) (by decide) fun t₂ Y k12 => ?_
  have hd2 : ∀ d, d + 8 ≤ 256 → word t₂.mem (cS s₀) d = word s.mem (cS s₀) d := fun d hd =>
    Y.out.word (Or.inl hd) (by omega)
  have hb2 : ∀ {A : Addr} {L : Nat}, (∀ i < L, ∀ x, ofs (cS s₀) x < cZ s₀ → off A i ≠ x) →
      Spec.Rsa.bytesAt t₂.mem A L = Spec.Rsa.bytesAt s₀.mem A L := fun hs' => by
    rw [bytesAt_out Y.out (by omega) hs']; exact hb0 hs'
  -- `m₂`.
  refine wp_reassoc2 (WP.seq (WP.mono (phaseP_ok (xj := 5) (oA := oQa s₀) (L := cqL s₀) (k := ck s₀)
    (I := s₀.gpr .r7) (D := stackArg s₀ 4) (Pv := mQ s₀) (hF.scr.congr k12.wr) (by omega) (by omega)
    (by omega) hwX (by decide) ((k12.gpr _ (by decide)).trans hF.r23) ((k12.gpr _ (by decide)).trans hF.r27)
    ((k12.gpr _ (by decide)).trans hF.r28) (by decide) (by decide) (by decide)
    (by rw [hd2 _ (by decide)]; exact hF.hBQ) (by rw [hd2 _ (by decide)]; exact hF.hQL)
    (by rw [hd2 _ (by decide)]; exact hF.hIn) (by rw [hd2 _ (by decide)]; exact hF.hNL)
    (by rw [hd2 _ (by decide)]; exact hF.hDQ) q1 (by omega) (by omega) (by omega)
    (by rw [k12.rd, k12.wr, rd0]; exact hP.rI) hP.sI (by rw [k12.rd, k12.wr, rd0]; exact hP.rDQ) hP.sDQ
    Y.v5 mQb (by omega) mQo)
    fun t₃ ⟨⟨_, q4, O3, c10, _, c29, _⟩, k3⟩ => ?_))
  rw [hb2 hP.sI, hb2 hP.sDQ] at q4
  have k13 := k12.trans k3
  refine hc t₃ ((k3.gpr _ (by decide)).trans Y.r26)
    (by rw [xval O3 (Or.inl (by omega)) (by omega)]; exact Y.v0)
    (by rw [O3.word (Or.inl (by omega)) (by omega)]; exact Y.w0)
    (by rw [xval O3 (Or.inl (by omega)) (by omega)]; exact Y.v5)
    (by rw [xval O3 (Or.inl (by omega)) (by omega)]; exact Y.v7)
    (by rw [val32_off_eq O3 (Or.inl (by omega)) (by omega)]; exact Y.p0)
    (by rw [val32_off_eq O3 (Or.inl (by omega)) (by omega)]; exact Y.p4) q4 c10 c29
    (Y.out.trans (O3.mono (by omega) (by omega))) k13.mono

end VG.Proof.Bignum.PPC64LE.Crt

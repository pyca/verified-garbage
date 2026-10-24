module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.CheckKey
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Derive.Y
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Derive.X
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Derive.Output
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Derive
import VerifiedGarbage.Proof.Dsa.PPC64LE.Ptr
import VerifiedGarbage.Proof.Dsa.PPC64LE.Range
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# DSA key derivation on PPC64LE: after the check of the domain

`dbody_ok`: `Derive.body` writes to `out` the domain's octets, then
`y = g^x mod p`'s `p_len` octets and x's `q_len` octets, and leaves 1 in
`r3`, exactly when `1 < y` and `0 < x < q`; else zeros and 0. Memory changes
only in `scratch` past its header and in `out`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Derive
open VG.Proof.Bignum (slot)

/-- The checks of derivation past the domain's, for `y = g^x mod p`. -/
def DeriveOk (p q g x : Nat) : Prop := 1 < g ^ x % p ∧ 0 < x ∧ x < q

instance (p q g x : Nat) : Decidable (DeriveOk p q g x) := inferInstanceAs (Decidable (_ ∧ _))

/-- The registers `Derive.body` writes. -/
def dbodyRegs : List Reg := yValueRegs ++ xRangeRegs ++ doutputRegs

theorem dbody_ok {s₀ s : State} {L : Lay} {key x out : Addr} (hL : L.Ok) (hP : ParamsOk s₀.mem L key)
    (hc : Checked s₀ s L key x out 0) (hkp : Kept L s₀.mem s.mem) (hk : Src s L key (2 * L.pl + L.ql))
    (hx : Src s L x L.ql) (ho : Scr s out (3 * L.pl + 2 * L.ql)) (hos : Src s L out (3 * L.pl + 2 * L.ql))
    (hko : ∀ i < 2 * L.pl + L.ql, ∀ y, ofs out y < 3 * L.pl + 2 * L.ql → off key i ≠ y)
    (hxo : ∀ i < L.ql, ∀ y, ofs out y < 3 * L.pl + 2 * L.ql → off x i ≠ y) :
    WP isa body s fun t =>
      (Spec.Rsa.bytesAt t.mem out (3 * L.pl + 2 * L.ql) =
          (if DeriveOk (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key) (kOf s₀.mem L x) then
            Spec.Rsa.bytesAt s₀.mem key (2 * L.pl + L.ql) ++
              Spec.Dsa.encodeBE L.pl (gOf s₀.mem L key ^ kOf s₀.mem L x % pOf s₀.mem L key) ++
              Spec.Rsa.bytesAt s₀.mem x L.ql
          else List.replicate (3 * L.pl + 2 * L.ql) 0) ∧
        t.gpr .r3 = BitVec.ofNat 64
          (if DeriveOk (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key) (kOf s₀.mem L x) then 1 else 0) ∧
        (∃ m, Kept L s.mem m ∧ Outside out 0 (3 * L.pl + 2 * L.ql) m t.mem) ∧ t.gpr .r21 = L.S ∧ ScrL t L) ∧
        Keep dbodyRegs s t := by
  have hZ := hL.z256
  have hpl := hL.pl
  have hql := hL.ql
  have hw8 := hL.wp_eq
  obtain ⟨ip, scr, regs, p0, -, p8, q0, -, -⟩ := hc
  obtain ⟨-, -, eg⟩ := params_kept hk hkp.out
  have ex : kOf s.mem L x = kOf s₀.mem L x := by simp only [kOf]; rw [hx.kept hkp.out]
  have ekey : Spec.Rsa.bytesAt s.mem key (2 * L.pl + L.ql) = Spec.Rsa.bytesAt s₀.mem key (2 * L.pl + L.ql) :=
    hk.kept hkp.out
  have exb : Spec.Rsa.bytesAt s.mem x L.ql = Spec.Rsa.bytesAt s₀.mem x L.ql := hx.kept hkp.out
  have B := VG.Proof.Dsa.supported_bounds hP.1.1
  have hpo := hP.1.2.2
  have hplt : pOf s₀.mem L key < 256 ^ L.pl := by
    have := VG.Proof.Dsa.decodeBE_lt (Spec.Rsa.bytesAt s₀.mem key L.pl)
    rwa [VG.Proof.Bignum.bytesAt_length] at this
  generalize pOf s₀.mem L key = p at p0 p8 B hpo hplt
  generalize qOf s₀.mem L key = q at q0 B
  generalize gOf s₀.mem L key = g at eg
  unfold body
  -- y.
  refine WP.seq (WP.mono (yValue_ok hL scr regs ip hk hx p0 (by omega) hpo p8) fun s₁ ⟨⟨vy, my, ip1, b1, oq1⟩, k1⟩ => ?_)
  rw [eg, ex] at vy my
  generalize hy : g ^ kOf s₀.mem L x % p = y at vy my
  have hyp : y < p := by rw [← hy]; exact Nat.mod_lt _ (by omega)
  have hr1 := regs.keep k1
  -- x's range.
  refine WP.seq (WP.mono (xRange_ok hL (scr.congr k1.wr) hr1 (hx.keep k1.rd k1.wr) my) fun s₂ ⟨⟨m2, Q2, qa2⟩, k2⟩ => ?_)
  have aq : arrQ s₁.mem L 0 = q := by
    rw [← q0]
    exact Outside.val32 oq1 (Or.inl (by simp only [slot_eq]; omega)) (by simp only [slot_eq]; omega)
  have ex1 : kOf s₁.mem L x = kOf s₀.mem L x := by
    rw [kOf, kOf, hx.kept (Kept.ofBody hL b1).out, exb]
  rw [aq, ex1] at m2
  -- The output.
  have b12 : Body L s.mem s₂.mem := b1.trans (qa2.qbody.body hL)
  have k12 := k1.trans k2
  refine WP.mono (doutput_ok hL Q2.scr Q2.regs m2 (hk.keep k12.rd k12.wr) (hx.keep k12.rd k12.wr)
    (ho.congr k12.wr) (hos.keep k12.rd k12.wr) hko hxo) fun t ⟨⟨vt, ot, t3⟩, kt⟩ => ?_
  have hD : DeriveOk p q g (kOf s₀.mem L x) = (1 < y ∧ 0 < kOf s₀.mem L x ∧ kOf s₀.mem L x < q) := by
    unfold DeriveOk; rw [hy]
  have hc : (decide (y ≠ 0) && decide (y ≠ 1) && decide (0 < kOf s₀.mem L x ∧ kOf s₀.mem L x < q)) =
      decide (1 < y ∧ 0 < kOf s₀.mem L x ∧ kOf s₀.mem L x < q) := by
    by_cases h0 : y = 0 <;> by_cases h1 : y = 1 <;> simp [h0, h1] <;> omega
  rw [hc] at vt t3
  have eb : Spec.Rsa.bytesAt s₂.mem L.Buf L.pl = Spec.Dsa.encodeBE L.pl y := by
    have hb : L.Buf = off L.Q 1600 := by simp only [Lay.Buf, Lay.Q, Lay.bOff, off_off]
    have hb2 : Spec.Rsa.bytesAt s₂.mem L.Buf L.pl = Spec.Rsa.bytesAt s₁.mem L.Buf L.pl := by
      rw [hb]; exact part_kept qa2 (Or.inr (by simp only [slot_eq]; omega)) (by omega)
    rw [hb2]
    exact ((VG.Proof.Dsa.encodeBE_eq_bytes (VG.Proof.Bignum.bytesAt_length _ _ _) (by omega)).mpr vy.symm).symm
  have kall := k12.trans kt
  have K2 := Kept.ofBody hL b12
  rw [eb, hk.kept K2.out, hx.kept K2.out, ekey, exb] at vt
  simp only [decide_eq_true_eq] at vt t3
  simp only [hD]
  exact ⟨⟨vt, t3, ⟨s₂.mem, K2, ot⟩, (kall.gpr .r21 (by decide)).trans regs.r21, scr.congr kall.wr⟩,
    kall.mono (by decide)⟩

end VG.Proof.Dsa.PPC64LE

module

public import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveY
public import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveX
public import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveOutput
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA key derivation on RISC-V: after the check of the domain

As on PPC64LE (`Proof/Dsa/PPC64LE/Derive/Body.lean`). `dbody_ok`:
`Derive.body` writes to `out` the domain's octets, then `y = g^x mod p`'s
`p_len` octets and x's `q_len` octets, and leaves 1 in `a0`, exactly when
`1 < y` and `0 < x < q`; else zeros and 0. Memory changes only in
`scratch` past its header and in `out`.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Impl.Dsa.RISCV64.Derive
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Win (mask)

/-- The checks of derivation past the domain's, for `y = g^x mod p`. -/
def DeriveOk (p q g x : Nat) : Prop := 1 < g ^ x % p ∧ 0 < x ∧ x < q

instance (p q g x : Nat) : Decidable (DeriveOk p q g x) := inferInstanceAs (Decidable (_ ∧ _))

/-- The registers `Derive.body` writes. -/
def dbodyRegs : List Reg := yValueRegs ++ xRangeRegs ++ doutputRegs

theorem dmask_eq (y k q : Nat) :
    (decide (y ≠ 0) && decide (y ≠ 1) && decide (0 < k ∧ k < q)) = decide (1 < y ∧ 0 < k ∧ k < q) := by
  by_cases h0 : y = 0 <;> by_cases h1 : y = 1 <;> simp [h0, h1] <;> omega

theorem dbody_ok {s₀ s : State} {L : Lay} {key x out : Addr} (hL : L.Ok) (hP : ParamsOk s₀.mem L key)
    (hc : Checked s₀ s L key x 0) (hkp : Kept L s₀.mem s.mem) (hw : word s.mem L.S Sign.hOut = out)
    (hk : Src s L key (2 * L.pl + L.ql)) (hx : Src s L x L.ql)
    (hout : ∀ i < 3 * L.pl + 2 * L.ql, InRegions s.wr (off out i) 1)
    (hno : out.toNat + (3 * L.pl + 2 * L.ql) ≤ 2 ^ 64) (hos : Src s L out (3 * L.pl + 2 * L.ql))
    (hko : ∀ i < 2 * L.pl + L.ql, ∀ y, ofs out y < 3 * L.pl + 2 * L.ql → off key i ≠ y)
    (hxo : ∀ i < L.ql, ∀ y, ofs out y < 3 * L.pl + 2 * L.ql → off x i ≠ y) :
    WP isa body s fun t =>
      (Spec.Rsa.bytesAt t.mem out (3 * L.pl + 2 * L.ql) =
          (if DeriveOk (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key) (kOf s₀.mem L x) then
            Spec.Rsa.bytesAt s₀.mem key (2 * L.pl + L.ql) ++
              Spec.Dsa.encodeBE L.pl (gOf s₀.mem L key ^ kOf s₀.mem L x % pOf s₀.mem L key) ++
              Spec.Rsa.bytesAt s₀.mem x L.ql
          else List.replicate (3 * L.pl + 2 * L.ql) 0) ∧
        t.gpr .a0 = BitVec.ofNat 64
          (if DeriveOk (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key) (kOf s₀.mem L x) then 1 else 0) ∧
        (∃ m, Kept L s.mem m ∧ Outside out 0 (3 * L.pl + 2 * L.ql) m t.mem) ∧ t.gpr .s6 = L.S ∧ ScrL t L) ∧
        Keep dbodyRegs s t := by
  have hZ := hL.z256
  have hpl := hL.pl
  have hql := hL.ql
  have hw8 := hL.wp_eq
  have hwq := hL.wq_ge
  obtain ⟨ip, scr, regs, p0, -, inv, p24, q0⟩ := hc
  obtain ⟨-, -, eg⟩ := params_kept hk hkp
  have ex : kOf s.mem L x = kOf s₀.mem L x := by simp only [kOf]; rw [hx.bytes hkp.out (by omega)]
  have ekey : Spec.Rsa.bytesAt s.mem key (2 * L.pl + L.ql) = Spec.Rsa.bytesAt s₀.mem key (2 * L.pl + L.ql) :=
    hk.bytes hkp.out (by omega)
  have exb : Spec.Rsa.bytesAt s.mem x L.ql = Spec.Rsa.bytesAt s₀.mem x L.ql := hx.bytes hkp.out (by omega)
  have B := VG.Proof.Dsa.supported_bounds hP.1.1
  have hpo := hP.1.2.2
  have hplt : pOf s₀.mem L key < 256 ^ L.pl := by
    have := VG.Proof.Dsa.decodeBE_lt (Spec.Rsa.bytesAt s₀.mem key L.pl)
    rwa [VG.Proof.Bignum.bytesAt_length] at this
  generalize pOf s₀.mem L key = p at p0 p24 B hpo hplt
  generalize qOf s₀.mem L key = q at q0 B
  generalize gOf s₀.mem L key = g at eg
  unfold body
  -- y.
  refine WP.seq (WP.mono (yValue_ok hL scr regs ip inv hk hx p0 (by omega) hpo p24)
    fun s₁ ⟨⟨vy, my, ip1, b1, oq1⟩, k1⟩ => ?_)
  rw [eg, ex] at vy my
  generalize hy : g ^ kOf s₀.mem L x % p = y at vy my
  have hyp : y < p := by rw [← hy]; exact Nat.mod_lt _ (by omega)
  have hr1 := regs.keep k1 b1
  -- x's range.
  refine WP.seq (WP.mono (xRange_ok hL (scr.congr k1.2.2) hr1 (hx.keep k1.2.1 k1.2.2) my)
    fun s₂ ⟨⟨m2, Q2, qa2⟩, k2⟩ => ?_)
  have aq : arrQ s₁.mem L 0 = q := by
    rw [← q0]
    exact oq1.wordsVal (Or.inl (by simp only [Lay.slot_eq]; omega)) (by simp only [Lay.slot_eq]; omega)
  have ex1 : kOf s₁.mem L x = kOf s₀.mem L x := by
    rw [kOf, kOf, hx.bytes b1 (by omega), exb]
  rw [aq, ex1] at m2
  -- The output.
  have b12 : Body L s.mem s₂.mem := b1.trans (qa2.body hL)
  have k12 := k1.trans k2
  refine WP.mono (doutput_ok hL Q2.scr Q2.regs m2 (by rw [b12.word (by decide)]; exact hw)
    (hk.keep k12.2.1 k12.2.2) (hx.keep k12.2.1 k12.2.2) (fun i hi => by rw [k12.2.2]; exact hout i hi) hno
    (hos.keep k12.2.1 k12.2.2) hko hxo) fun t ⟨⟨vt, ot, t0⟩, kt⟩ => ?_
  have hD : DeriveOk p q g (kOf s₀.mem L x) = (1 < y ∧ 0 < kOf s₀.mem L x ∧ kOf s₀.mem L x < q) := by
    unfold DeriveOk; rw [hy]
  rw [dmask_eq] at vt t0
  have eb : Spec.Rsa.bytesAt s₂.mem L.Buf L.pl = Spec.Dsa.encodeBE L.pl y := by
    rw [qa2.bufBytes hL (by omega)]
    exact ((VG.Proof.Dsa.encodeBE_eq_bytes (VG.Proof.Bignum.bytesAt_length _ _ _) (by omega)).mpr vy.symm).symm
  have kall := k12.trans kt
  have K2 := Kept.ofBody hL b12
  rw [eb, hk.bytes K2.out (by omega), hx.bytes K2.out (by omega), ekey, exb] at vt
  simp only [decide_eq_true_eq] at vt t0
  simp only [hD]
  refine ⟨⟨vt, t0, ⟨s₂.mem, K2, ot⟩, (kall.gpr (by decide)).trans regs.s6, scr.congr kall.2.2⟩, ?_⟩
  simp only [dbodyRegs, List.append_assoc] at kall ⊢
  exact kall

end VG.Proof.Dsa.RISCV64

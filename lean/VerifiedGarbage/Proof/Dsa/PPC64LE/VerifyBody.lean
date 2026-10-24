module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.CheckKey
public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyProd
public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyComb
public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyEnd
public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyInv
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.Offset

/-!
# DSA verification on PPC64LE: after the check of the key

`body_ok`: `Verify.body` leaves in `r3` 1 exactly when r and s are in
`(0, q)` and `(g^u1 y^u2 mod p) mod q = r`, for `w = s^(q − 2) mod q`,
`u1 = z w mod q` and `u2 = r w mod q` (`vComp`), z the digest's first
`min(digest_len, bitLength q / 8)` octets.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Verify
open VG.Proof.Bignum (slot slot_sep)

/-- The value verification compares with r. -/
def vComp (p q g y z r s : Nat) : Nat :=
  (g ^ (z * (s ^ (q - 2) % q) % q) % p * (y ^ (r * (s ^ (q - 2) % q) % q) % p) % p) % q

/-- Memory that changed only at offsets below `qOff` of `scratch` keeps the Q space. -/
theorem keepQ_of {L : Lay} (hL : L.Ok) {m m' : Mem} (h : ∀ x, L.qOff ≤ ofs L.S x → m' x = m x) :
    Outside L.Q 1600 (2 ^ 64 - 1600) m m' := by
  intro x hx
  have hq : L.qOff ≤ 11456 := by rw [hL.qOff_eq]; rcases hL.pl with e | e | e <;> omega
  have hlt := (x - L.S).isLt
  have hlt' := (x - L.Q).isLt
  refine h x ?_
  simp only [ofs, Lay.Q, off] at hx ⊢
  rw [Offset.toNat_sub_add x L.S (by omega)] at hx
  by_cases hd : L.qOff ≤ (x - L.S).toNat
  · exact hd
  · rw [Nat.mod_eq_of_lt (by omega)] at hx; omega

/-- A change in the Q space's arrays or the buffer keeps the P space. -/
theorem QBuf.keepP {L : Lay} (hL : L.Ok) {m m' : Mem} (h : QBuf L m m') :
    Outside L.S (L.qOff + slot 4 1) (1600 + 2 * L.pl - slot 4 1) m m' := by
  have hq : L.qOff ≤ 11456 := by rw [hL.qOff_eq]; rcases hL.pl with e | e | e <;> omega
  exact outside_shift (B := L.S) (a := L.qOff) h (by have := hL.pl; rw [show slot 4 1 = 304 from rfl]; omega)
    (by omega)

theorem QBuf.arrP {L : Lay} (hL : L.Ok) {m m' : Mem} (h : QBuf L m m') {j : Nat} (hj : j < 28) :
    arrP m' L j = arrP m L j := by
  have := slot_lt (w := L.wp) hj
  exact Outside.val32 (h.keepP hL) (Or.inl (by simp only [Lay.qOff] at *; omega))
    (by have := hL.nowrap; have := hL.buf_end; simp only [Lay.bOff, Lay.qOff] at *; omega)

theorem QBuf.ptop {L : Lay} (hL : L.Ok) {m m' : Mem} (h : QBuf L m m') :
    word m' L.S (slot L.wp 0 + 8 * L.wp) = word m L.S (slot L.wp 0 + 8 * L.wp) := by
  have := slot_lt (w := L.wp) (show 0 < 28 by decide)
  exact Outside.word (h.keepP hL) (Or.inl (by simp only [Lay.qOff] at *; omega))
    (by have := hL.nowrap; have := hL.buf_end; simp only [Lay.bOff, Lay.qOff] at *; omega)

/-- A buffer's first `min n k` octets. -/
theorem bytesAt_take (m : Mem) (D : Addr) (n k : Nat) :
    (Spec.Rsa.bytesAt m D n).take k = Spec.Rsa.bytesAt m D (min n k) := by
  simp only [Spec.Rsa.bytesAt, ← List.map_take, List.take_range, Nat.min_comm]


/-- The first octets of a buffer apart from `scratch`. -/
theorem Src.take {s : State} {L : Lay} {D : Addr} {n : Nat} (h : Src s L D n) {k : Nat} (hk : k ≤ n) :
    Src s L D k :=
  ⟨fun i hi => h.rd i (by omega), fun i hi => h.sep i (by omega)⟩

/-- The change of the digest's length in the header. -/
theorem Kept.ofDl {L : Lay} (hL : L.Ok) {m m' : Mem} (h : Outside L.S hDlen 8 m m') : Kept L m m' :=
  ⟨h.mono (by decide) (by have := hL.z256; simp only [hDlen]; omega), fun i hi =>
    Outside.word h (Or.inr (by simp only [saveOff, hDlen]; omega))
      (by have := hL.nowrap; have := hL.z256; simp only [saveOff]; omega)⟩

/-- The signature's and the digest's values, kept. -/
theorem sig_kept {s : State} {L : Lay} {sig dig : Addr} {D : Nat} (hsg : Src s L sig (2 * L.ql))
    (hdg : Src s L dig D) {m m' : Mem} (h : Kept L m m') (hZ : 72 ≤ L.Z) {k : Nat} (hk : k ≤ D) :
    rOf m' L sig = rOf m L sig ∧ sOf m' L sig = sOf m L sig ∧
      Spec.Rsa.bytesAt m' dig k = Spec.Rsa.bytesAt m dig k := by
  refine ⟨?_, ?_, (hdg.take hk).kept h hZ⟩
  · have e := (hsg.sub (o := 0) (k := L.ql) (by omega)).kept h hZ
    simp only [off, BitVec.add_zero] at e
    simp only [rOf]; rw [e]
  · simp only [sOf]; rw [(hsg.sub (o := L.ql) (k := L.ql) (by omega)).kept h hZ]

/-- The registers `Verify.body` writes. -/
def bodyRegs : List Reg :=
  [.r0, .r3, .r4] ++ rangesRegs ++ rrRegs ++ qm2Regs ++ invRegs ++ prodRegs ++ combRegs ++ cmpRegs

theorem body_ok {s₀ s : State} {L : Lay} {key sig dig : Addr} {D : Nat}
    (hL : L.Ok) (hK : KeyOk s₀.mem L key) (hc : Checked s₀ s L key sig dig)
    (hkp : Kept L s₀.mem s.mem) (hk : Src s L key (3 * L.pl + L.ql)) (hsg : Src s L sig (2 * L.ql))
    (hdg : Src s L dig D) (hD : word s.mem L.S hDlen = BitVec.ofNat 64 D) (hDlt : D < 2 ^ 64) :
    WP isa Verify.body s fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 (if ((0 < rOf s.mem L sig ∧ rOf s.mem L sig < qOf s₀.mem L key) ∧
          (0 < sOf s.mem L sig ∧ sOf s.mem L sig < qOf s₀.mem L key)) ∧
          vComp (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key) (yOf s₀.mem L key)
            (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig
              (min D (Spec.Dsa.bitLength (qOf s₀.mem L key) / 8))))
            (rOf s.mem L sig) (sOf s.mem L sig) = rOf s.mem L sig then 1 else 0) ∧
        Kept L s.mem t.mem ∧ t.gpr .r21 = L.S ∧ ScrL t L) ∧ Keep bodyRegs s t := by
  have hZ := hL.z256
  have hpl := hL.pl
  have hql := hL.ql
  have hnw := hL.nowrap
  obtain ⟨ip, scr, hdr, p0, ptop, p8, q0, qtop, qbw, -⟩ := hc
  obtain ⟨ep, eq, eg, ey⟩ := key_kept hk hkp (by omega)
  unfold KeyOk at hK
  have hqlt : qOf s₀.mem L key < 2 ^ (8 * L.ql) := by
    rw [← eq, qOf, ← VG.Proof.Bignum.pow256_eq]
    have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s.mem (off key L.pl) L.ql)
    rwa [VG.Proof.Bignum.bytesAt_length] at this
  generalize pOf s₀.mem L key = p at hK p0 p8 ⊢
  generalize hq : qOf s₀.mem L key = q at hK q0 qbw hqlt ⊢
  generalize gOf s₀.mem L key = g at hK ⊢
  generalize yOf s₀.mem L key = y at hK ⊢
  have B := VG.Proof.Dsa.supported_bounds hK.1.1
  have hqo : q % 2 = 1 := hK.1.2.1
  have hpo : p % 2 = 1 := hK.1.2.2
  have hqb : Spec.Dsa.bitLength q ≤ 256 := by have := hK.1.1; unfold Spec.Dsa.supportedSizes at this; omega
  generalize hn : Spec.Dsa.bitLength q / 8 = n at qbw ⊢
  have hnq : n ≤ L.ql := by
    sorry
  sorry

end VG.Proof.Dsa.PPC64LE

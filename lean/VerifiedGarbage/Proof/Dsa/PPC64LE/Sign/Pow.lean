module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx
import VerifiedGarbage.Proof.Dsa.PPC64LE.Load
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Verify
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Table
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Comb.Pow
import VerifiedGarbage.Proof.Bignum.PPC64LE.ModExpPow
import VerifiedGarbage.Proof.Dsa.PPC64LE.Elem.Basic
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubPower
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Spec.Rsa.Contract

/-!
# DSA signing on PPC64LE: a power by a secret in the P space

`powSrc_ok`: `powP`, as `combPowP_ok` (`Comb/Pow.lean`), with the exponent's
`q_len` octets in a buffer apart from `scratch` (x in the key, or the nonce).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Verify
open VG.Proof.Bignum (slot)

/-- `powP`: the `p_len` octets at `N` (`r12`) to the power of the `q_len`
octets at `E` (`r24`), apart from `scratch`, modulo p, into array 4. -/
theorem powSrc_ok {s : State} {L : Lay} {key sig dig N E : Addr} {p : Nat} (hL : L.Ok)
    (hr : Regs s L key sig dig) (hin : InP s L) (hN : Src s L N L.pl) (h12 : s.gpr .r12 = N)
    (hE : Src s L E L.ql) (h24 : s.gpr .r24 = E)
    (hp0 : arrP s.mem L 0 = p) (hp : 2 ≤ p) (hpo : p % 2 = 1) (hrr : arrP s.mem L 8 = 2 ^ (128 * L.wp) % p) :
    WP isa powP s fun t =>
      (arrP t.mem L 4 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem N L.pl) ^
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem E L.ql) % p ∧
        InP t L ∧ Outside L.S (slot L.wp 1) (slot L.wp 8 - slot L.wp 1) s.mem t.mem) ∧
        Keep combPowRegs s t := by
  have hZ := hL.hdr
  have hw := hL.wp_ge
  have hw8 := hL.wp_eq
  have hnw := hL.nowrap
  have hql := hL.ql
  have hbe := hL.buf_end
  have hqZ : L.qOff + 1600 ≤ L.Z := by simp only [Lay.bOff] at hbe; omega
  have hq28 : L.qOff = slot L.wp 28 := rfl
  have e0 := Lay.slot_eq L.wp 0; have e1 := Lay.slot_eq L.wp 1; have e4 := Lay.slot_eq L.wp 4
  have e8 := Lay.slot_eq L.wp 8; have e28 := Lay.slot_eq L.wp 28
  have en := hin.env
  unfold powP
  -- `p_len`.
  refine WP.seq (WP.mono (getP_ok hr .r6) fun s₁ ⟨⟨a6, m1⟩, k1⟩ => ?_)
  have en1 := en.keep k1 (by decide)
  -- The number into array 4.
  refine WP.seq (WP.mono (loadArr_ok en1 (j := 4) (by decide) ((k1.gpr .r12 (by decide)).trans h12) a6
      (by omega) (by omega) (by rw [k1.rd, k1.wr]; exact hN.rd)
      (fun i hi x hx => hN.sep i hi x (by omega))) fun s₂ ⟨⟨v4, _, o2, a10⟩, k2⟩ => ?_)
  rw [m1] at v4 o2
  have en2 := env_keep10 en1 k2 (by decide) a10
  -- `R² mod p` into array 1.
  refine WP.seq (WP.mono (copy_ok en2 (o := 1) (a := 8) (by decide) (by decide) (by decide))
    fun s₃ ⟨⟨v1, o3⟩, k3⟩ => ?_)
  have o23 : Outside L.S (slot L.wp 1) (slot L.wp 8 - slot L.wp 1) s.mem s₃.mem :=
    (o2.mono (by omega) (by omega)).trans (o3.mono (by omega) (by omega))
  have k13 := (k1.trans k2).trans k3
  have hr3 := hr.keep k13
  -- The exponent's pointer and length, and `-p⁻¹`.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r30, .r31] (Q := fun t => t.gpr .r30 = E ∧
      t.gpr .r31 = BitVec.ofNat 64 L.ql ∧ t.mem = s₃.mem) (by
      unfold getQ
      prun [(k13.gpr .r24 (by decide)).trans h24, Regs.q_eq hr3, BitVec.add_zero]) (by decide)) fun s₄ ⟨⟨a30, a31, m4⟩, k4⟩ => ?_
  have k24 := k3.trans k4
  have g10 : s₄.gpr .r10 = off L.S (slot L.wp 0) := (k24.gpr .r10 (by decide)).trans a10
  have p4 : val32 s₄.mem L.S (slot L.wp 0) (2 * L.wp) = p := by
    rw [m4, Outside.val32 o23 (by omega) (by omega)]; exact hp0
  have hlow : (word s₄.mem L.S (slot L.wp 0)).toNat % 2 = 1 := by
    have h1 := word_eq_w32 s₄.mem L.S (slot L.wp 0)
    have h2 : val32 s₄.mem L.S (slot L.wp 0) (2 * L.wp - 1 + 1) =
        w32 s₄.mem L.S (slot L.wp 0) + 2 ^ 32 * val32 s₄.mem L.S (slot L.wp 0 + 4) (2 * L.wp - 1) := rfl
    rw [Nat.sub_add_cancel (by omega : 1 ≤ 2 * L.wp), p4] at h2
    omega
  refine WP.mono (Pub.minv_ok (en.hs.congr (k13.trans k4).wr) g10 (by omega) hlow)
    fun s₅ ⟨⟨r12lt, r12inv, m5⟩, k5⟩ => ?_
  have k15 := (k13.trans k4).trans k5
  have p5 : val32 s₅.mem L.S (slot L.wp 0) (2 * L.wp) = p := by rw [m5]; exact p4
  have r1 : val32 s₅.mem L.S (slot L.wp 1) (2 * L.wp) = 2 ^ (128 * L.wp) % p := by
    rw [m5, m4]
    show arr s₃.mem L.S L.wp 1 = _
    rw [v1, arr, Outside.val32 o2 (by omega) (by omega)]; exact hrr
  have x5 : val32 s₅.mem L.S (slot L.wp 4) (2 * L.wp) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem N L.pl) := by
    rw [m5, m4, Outside.val32 o3 (by omega) (by omega)]; exact v4
  have e5 : Spec.Rsa.bytesAt s₅.mem E L.ql = Spec.Rsa.bytesAt s.mem E L.ql := by
    rw [m5, m4]; exact hE.bytes (Body.ofP hL o23 (by omega) (by omega)) hZ
  refine WP.seq (WP.mono (ModExp.powSecret_ok (D := E) (L := L.ql) (en.hs.congr k15.wr) (by omega)
    (by omega) (by omega) ((k5.gpr .r10 (by decide)).trans g10) ((k15.gpr .r29 (by decide)).trans en.h29)
    ((k15.gpr .r11 (by decide)).trans en.h11) r12lt (by rw [m5]; exact r12inv) (by rw [p5]; exact hp)
    (by rw [p5]; exact hpo) (by rw [r1, p5]; exact Nat.mod_lt _ (by omega))
    (by rw [k5.gpr .r30 (by decide), a30]; exact (BitVec.add_zero _).symm)
    ((k5.gpr .r31 (by decide)).trans a31) (by omega) (by omega)
    (by rw [k15.rd, k15.wr]; exact hE.rd)
    (fun i hi x hx => hE.sep i hi x (Nat.lt_of_lt_of_le hx (by omega)))) fun s₆ ⟨⟨hpow, o6⟩, k6⟩ => ?_)
  rw [e5, p5, x5] at hpow
  have v6 := hpow (by rw [r1, ← Nat.pow_add, show 64 * L.wp + 64 * L.wp = 128 * L.wp by omega])
  have k16 := k15.trans k6
  refine WP.mono (WP.keep [.r31] (Q := fun t => t.gpr .r31 = L.S ∧ t.mem = s₆.mem) (by
      prun [(k16.gpr .r23 (by decide)).trans hin.h23, BitVec.add_zero]) (by decide)) fun t ⟨⟨t31, mt⟩, kt⟩ => ?_
  have k3t := (((k4.trans k5).trans k6).trans kt)
  have o6' : Outside L.S (slot L.wp 1) (slot L.wp 8 - slot L.wp 1) s₅.mem s₆.mem := outs_within o6 fun r hr => by
    simp only [Pub.powRs, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> rw [Lay.slot_eq, Lay.slot_eq] <;> omega
  rw [m5, m4] at o6'
  refine ⟨⟨by rw [arrP, arr, mt]; exact v6, ⟨env_keep31 (en2.keep k3 (by decide)) k3t (by decide) t31,
      ((k16.trans kt).gpr .r21 (by decide)).trans hin.h21, ((k16.trans kt).gpr .r23 (by decide)).trans hin.h23⟩,
    by rw [mt]; exact o23.trans o6'⟩, (k16.trans kt).mono (by decide)⟩

end VG.Proof.Dsa.PPC64LE

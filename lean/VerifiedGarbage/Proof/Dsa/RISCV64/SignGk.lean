module

public import VerifiedGarbage.Proof.Dsa.RISCV64.SignKeyPair
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA signing on RISC-V: `g^k mod p`

As on PPC64LE (`Proof/Dsa/PPC64LE/Sign/Gk.lean`). `gk_ok`: in the P space
with p in array 0 and `R² mod p` in array 24, `g^k mod p` (k the `q_len`
octets at `ra`) to the buffer's first `p_len` octets.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Impl.Dsa.RISCV64.Sign
open VG.Proof.Bignum (slot)

/-- A word of the P space, kept by a change in the buffer's first `p_len` octets. -/
theorem buf_pword {L : Lay} (hL : L.Ok) {m m' : Mem} (h : Outside L.Buf 0 L.pl m m') {d : Nat}
    (hd : d + 8 ≤ L.qOff) : word m' L.S d = word m L.S d := by
  have hw := hL.wp_ge
  have hq : L.qOff < 2 ^ 63 := by simp only [Lay.qOff, Lay.slot_eq]; omega
  refine (Mem.readW_congr fun i hi => (h _ (Or.inr ?_)).symm).symm
  by_contra hc
  have h1 := bufPastP hL (off L.S d + BitVec.ofNat 64 i) (by
    simp only [ofs] at hc ⊢; omega)
  have h2 := ofs_off L.S (d := d) (i := i) (by omega)
  simp only [ofs] at h1 h2
  omega

/-- The registers `gk` writes. -/
def gkRegs : List Reg := [.s9] ++ ptrRegs ++ powPRegs ++ [.s7, .t2] ++ [.s8] ++ storeRegs

/-- `gk`: `g^k mod p` to the buffer's first `p_len` octets. Memory changes
only in the P space's arrays 1–23 and the buffer's first `p_len` octets. -/
theorem gk_ok {s : State} {L : Lay} {key nonce : Addr} {p : Nat} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key nonce) (hin : InP s L) (hi : PInv s L) (hk : Src s L key (2 * L.pl + L.ql))
    (hn : Src s L nonce L.ql) (hp0 : arrP s.mem L 0 = p) (hp : 2 ≤ p) (hpo : p % 2 = 1)
    (hrr : arrP s.mem L 24 = 2 ^ (128 * L.wp) % p) :
    WP isa gk s fun t =>
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem L.Buf L.pl) = gOf s.mem L key ^ kOf s.mem L nonce % p ∧
        InP t L ∧ PInv t L ∧ ∃ m, PLow L s.mem m ∧ Outside L.Buf 0 L.pl m t.mem) ∧ Keep gkRegs s t := by
  have hw8 := hL.wp_eq
  have hpl := hL.pl
  unfold gk
  -- The pointers: the nonce into `s9`, g's octets into `s7`.
  refine WP.seq (WP.block_append (WP.mono (WP.keep [.s9] (Q := fun u => u.gpr .s9 = nonce ∧ u.mem = s.mem)
    (by brun [hr.ra, BitVec.add_zero]) (by decide) (by rfl)) fun s₁ ⟨⟨a9, m1⟩, k1⟩ =>
    WP.mono (ptrG_ok (hs.congr k1.2.2) hL (hr.keepM k1 m1)) fun s₂ ⟨⟨b7, _, m2⟩, k2⟩ => ?_))
  have k12 := k1.trans k2
  have hm2 : s₂.mem = s.mem := by rw [m2, m1]
  -- `g^k mod p` into array 4.
  refine WP.seq (WP.mono (powSrc_ok (N := off key (L.pl + L.ql)) (E := nonce) (p := p) hL (hs.congr k12.2.2)
      (hr.keepM k12 hm2) (hin.keep k12) (by
        show ((word s₂.mem L.S (slot L.wp 0)).toNat * (s₂.gpr .t1).toNat + 1) % 2 ^ 64 = 0
        rw [hm2, k12.gpr (by decide)]; exact hi)
      ((hk.keep k12.2.1 k12.2.2).sub (o := L.pl + L.ql) (k := L.pl) (by omega)) b7 (hn.keep k12.2.1 k12.2.2)
      ((k2.gpr (by decide)).trans a9) (by rw [hm2]; exact hp0) hp hpo (by rw [hm2]; exact hrr))
    fun s₃ ⟨⟨v4, in3, i3, o3⟩, k3⟩ => ?_)
  rw [hm2] at v4 o3
  have k13 := k12.trans k3
  have hr3 : Regs s₃ L key nonce := hr.keep k13 (PLow.body hL o3)
  -- To the buffer.
  refine WP.seq (WP.block_append (WP.mono (bufBase_ok (hs.congr k13.2.2) hL hr3 (rd := .s7) (t := .t2)
      (by decide) (by decide) (by decide)) fun u ⟨⟨f7, mu⟩, ku⟩ =>
    WP.mono (getP_ok (hs.congr (k13.trans ku).2.2) hL (hr3.keepM ku mu) .s8) fun s₄ ⟨⟨f8, m4⟩, k4⟩ => ?_))
  have hm4 : s₄.mem = s₃.mem := by rw [m4, mu]
  have k14 := (k13.trans ku).trans k4
  have en4 := in3.env.keep (ku.trans k4)
  refine WP.mono (storeBE_ok (j := 4) (O := L.Buf) (k := L.pl) en4 (by decide)
    (by have := ScrL.bufSt (hs.congr k14.2.2) hL (o := 0) (k := L.pl) (by omega)
        simpa only [off, BitVec.add_zero] using this)
    (by have := buf_nowrap hL (o := 0) (k := L.pl) (by omega) (by omega); simpa only [off, BitVec.add_zero] using this)
    ((k4.gpr (by decide)).trans f7) f8 (by omega) (by omega) (bufPastP hL)) fun t ⟨⟨vt, ot⟩, kt⟩ => ?_
  rw [hm4] at vt ot
  have hplt : p < 2 ^ (8 * L.pl) := by
    rw [← hp0, ← hw8, show 8 * (8 * L.wp) = 64 * L.wp by omega]; exact wordsVal_lt _ _ _ _
  have kall := k14.trans kt
  have y3 : arrP s₃.mem L 4 = gOf s.mem L key ^ kOf s.mem L nonce % p := v4
  refine ⟨⟨?_, ⟨en4.keep kt, (kall.gpr (by decide)).trans hin.s6⟩, ?_, ⟨s₃.mem, o3, ot⟩⟩, ?_⟩
  · rw [vt, read_low _ _ (w := L.wp) (by rw [hw8]) (by
      show arrP s₃.mem L 4 < 2 ^ (8 * L.pl); rw [y3]; exact Nat.lt_trans (Nat.mod_lt _ (by omega)) hplt)]
    exact y3
  · show ((word t.mem L.S (slot L.wp 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
    rw [buf_pword hL ot (by simp only [Lay.qOff, Lay.slot_eq]; omega), ((ku.trans k4).trans kt).gpr (by decide)]
    exact i3
  · simp only [gkRegs, List.append_assoc] at kall ⊢
    exact kall.mono (by decide)

end VG.Proof.Dsa.RISCV64

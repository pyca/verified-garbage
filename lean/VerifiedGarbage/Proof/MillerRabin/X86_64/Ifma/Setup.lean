module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Ifma.Mult

/-!
# The IFMA Miller–Rabin round: the area before the vector code

`setup_ok`: from the prepared workspace at `H` (`rdi`) of `W` words (the
candidate `c` in `aN`, `b R mod c` in `aXm`, `R mod c` in `aR1`,
`R = 2^(64 W)`, and `-c⁻¹ mod 2⁶⁴` in the header), the area at `areaBase l H`
(array `aT0` rounded up to 64 bytes) holds `Pre`'s numbers; only the table
arrays change.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64.Ifma

open VG VG.X86_64 VG.Proof.Bignum.Amm52
open VG.Proof.Bignum (off word ofs Outside mask Frm wv)
open VG.Proof.Bignum.X86_64 (Scr)
open VG.Proof.Bignum.X86_64.Ifma (limb val52)
open VG.Proof.Bignum.X86_64.Ifma.Pub (PubOk Mod)
open VG.Impl.Rsa.X86_64.CrtIfma (mask52)
open VG.Impl.Rsa.X86_64.PubIfma (arr)
open VG.Impl.MillerRabin.X86_64.Ifma
open VG.Impl.Bignum (sMinv)
open VG.Impl.Bignum.Public (aN aXm)
open VG.Impl.RsaKeyGen.X86_64.Candidate (aT0 aR1)

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

/-- The area's base: array `aT0` of the workspace at `H`, rounded up to a
multiple of 64 (`area`). -/
def areaBase (l : VG.Impl.Rsa.X86_64.CrtIfma.Lay) (H : Addr) : Addr :=
  (H + BitVec.ofNat 64 (arr l aT0) + 63#64) &&& BitVec.signExtend 64 (BitVec.ofInt 32 (-64))

set_option warningAsError false

/-- The area lies in the table arrays: from array `aT0`'s offset at most 63
bytes on, `size l` bytes before array `aT0 + 16`'s. -/
theorem areaBase_ofs (hl : PubOk l) {H : Addr} (hn : H.toNat + arr l (aT0 + 16) ≤ 2 ^ 64) :
    arr l aT0 ≤ ofs H (areaBase l H) ∧ ofs H (areaBase l H) + size l ≤ arr l (aT0 + 16) ∧
      areaBase l H = off H (ofs H (areaBase l H)) := by
  sorry

/-- `setup`: the area's numbers, from the prepared workspace. -/
theorem setup_ok (hl : PubOk l) {s : State} {H : Addr} {n c bR : Nat}
    (hdi : s.gpr .rdi = H) (hwr : (⟨H, 8 * n⟩ : Region) ∈ s.wr) (hn : H.toNat + 8 * n ≤ 2 ^ 64)
    (hsz : arr l 27 ≤ 8 * n)
    (hc : wv s.mem H (arr l aN) l.W = c) (h3 : 3 ≤ c) (hodd : c % 2 = 1)
    (hinv : ((word s.mem H (arr l aN)).toNat * (word s.mem H (8 * sMinv)).toNat + 1) % 2 ^ 64 = 0)
    (hr1 : wv s.mem H (arr l aR1) l.W = 2 ^ (64 * l.W) % c)
    (hx : wv s.mem H (arr l aXm) l.W = bR) (hbR : bR < c) :
    WP isa (VG.Impl.Bignum.X86_64.seqs (setup l)) s fun t =>
      t.gpr .rbx = areaBase l H ∧ t.gpr .r12 = mask52 ∧ t.gpr .rdi = H ∧
      Pre l t.mem (areaBase l H) c ((word s.mem H (8 * sMinv)).toNat % 2 ^ 52) bR ∧
      Frm H [(arr l aT0, 16 * (8 * (l.W + 2)))] s.mem t.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r11 → r ≠ .r12 → r ≠ .r13 →
        r ≠ .rbp → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  sorry

end VG.Proof.MillerRabin.X86_64.Ifma

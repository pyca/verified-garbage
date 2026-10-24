module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx
public import VerifiedGarbage.Proof.Dsa.DomainShape
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# DSA on PPC64LE: the sizes and the oddness of p and q

* `sigLen_ok`, `bytesBits_ok`: the scan of a number's octets
  (`Proof/Dsa/DomainShape.lean`'s `significant`): its significant octets in
  `r16`, and `r0 = 0` exactly when the first has its top bit set;
* `pairs_ok`: `r0 = 0` exactly when the significant octets of p and q are a
  supported pair;
* `odd_ok`: `r0 = 0` exactly when the number is odd;
* `sizes_ok`, `odds_ok`: `sizes` and `odds` run `rest` exactly when the
  sizes are supported, and p and q are odd.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE
open VG.Proof.Dsa (significant)
open VG.Proof.Bignum (slot)

/-- The registers `sigLen` and `bytesBits` write. -/
def sigRegs : List Reg := [.r0, .r3, .r14, .r15, .r16, .r17]

/-- `sigLen`: the significant octets of the `k` octets at `N` (`r12`, `k` in
`r6`), into `r16`. -/
theorem sigLen_ok {s : State} {N : Addr} {k : Nat} (h12 : s.gpr .r12 = N) (h6 : s.gpr .r6 = BitVec.ofNat 64 k)
    (hk : 1 ≤ k) (hk' : k ≤ 1024) (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off N i) 1) :
    WP isa sigLen s fun t =>
      (t.gpr .r16 = BitVec.ofNat 64 (significant (Spec.Rsa.bytesAt s.mem N k)).1 ∧ t.mem = s.mem) ∧
        Keep sigRegs s t := by
  sorry

/-- `bytesBits`: the significant octets into `r16`, and `r0 = 0` exactly
when the first has its top bit set. -/
theorem bytesBits_ok {s : State} {N : Addr} {k : Nat} (h12 : s.gpr .r12 = N)
    (h6 : s.gpr .r6 = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hk' : k ≤ 1024)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off N i) 1) :
    WP isa bytesBits s fun t =>
      (t.gpr .r16 = BitVec.ofNat 64 (significant (Spec.Rsa.bytesAt s.mem N k)).1 ∧
        (t.gpr .r0 = 0 ↔ 128 ≤ (significant (Spec.Rsa.bytesAt s.mem N k)).2.toNat) ∧ t.mem = s.mem) ∧
        Keep sigRegs s t := by
  sorry

/-- `pairs`: `r0 = 0` exactly when `(8 a, 8 b)` are supported sizes. -/
theorem pairs_ok {s : State} {a b : Nat} (h27 : s.gpr .r27 = BitVec.ofNat 64 a)
    (h28 : s.gpr .r28 = BitVec.ofNat 64 b) (ha : a ≤ 1024) (hb : b ≤ 1024) :
    WP isa pairs s fun t =>
      ((t.gpr .r0 = 0 ↔ Spec.Dsa.supportedSizes (8 * a) (8 * b)) ∧ t.mem = s.mem) ∧
        Keep [.r0, .r3, .r4] s t := by
  sorry

/-- `odd`: `r0 = 0` exactly when the number of the `k` octets at `N` is odd. -/
theorem odd_ok {s : State} {N : Addr} {k : Nat} (h12 : s.gpr .r12 = N) (h6 : s.gpr .r6 = BitVec.ofNat 64 k)
    (hk : 1 ≤ k) (hk' : k ≤ 1024) (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off N i) 1) :
    WP isa (.block odd) s fun t =>
      ((t.gpr .r0 = 0 ↔ Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem N k) % 2 = 1) ∧ t.mem = s.mem) ∧
        Keep [.r0, .r3, .r14] s t := by
  sorry

/-- The registers `sizes` and `odds` write before `rest` or `fail`. -/
def sizesRegs : List Reg := [.r0, .r3, .r4, .r6, .r12, .r14, .r15, .r16, .r17, .r27, .r28]

/-- The sizes are supported. -/
abbrev SizesOk (m : Mem) (L : Lay) (key : Addr) : Prop :=
  Spec.Dsa.supportedSizes (Spec.Dsa.bitLength (pOf m L key)) (Spec.Dsa.bitLength (qOf m L key))

/-- `sizes rest fail`: `rest` with q's significant octets (`bitLength q / 8`)
in the header's word `hQb`, if the sizes are supported; else `fail`, with at
most that word changed. -/
theorem sizes_ok {s : State} {L : Lay} {key sig dig : Addr} {Q : State → Prop} {rest fail : Prog isa}
    (hL : L.Ok) (hs : ScrL s L) (hh : Hdr s.mem L key sig dig) (h21 : s.gpr .r21 = L.S)
    (hk : Src s L key (3 * L.pl + L.ql))
    (hrest : ∀ t, SizesOk s.mem L key →
      t.mem = s.mem.writeW (off L.S hQb) (BitVec.ofNat 64 (Spec.Dsa.bitLength (qOf s.mem L key) / 8)) →
      Keep sizesRegs s t → WP isa rest t Q)
    (hfail : ∀ t, ¬ SizesOk s.mem L key → Outside L.S hQb 8 s.mem t.mem → Keep sizesRegs s t →
      WP isa fail t Q) :
    WP isa (sizes rest fail) s Q := by
  sorry

/-- `odds rest fail`: `rest` if p and q are odd, else `fail`. -/
theorem odds_ok {s : State} {L : Lay} {key sig dig : Addr} {Q : State → Prop} {rest fail : Prog isa}
    (hL : L.Ok) (hs : ScrL s L) (hh : Hdr s.mem L key sig dig) (h21 : s.gpr .r21 = L.S)
    (hk : Src s L key (3 * L.pl + L.ql))
    (hrest : ∀ t, pOf s.mem L key % 2 = 1 → qOf s.mem L key % 2 = 1 → t.mem = s.mem → Keep sizesRegs s t →
      WP isa rest t Q)
    (hfail : ∀ t, ¬ (pOf s.mem L key % 2 = 1 ∧ qOf s.mem L key % 2 = 1) → t.mem = s.mem →
      Keep sizesRegs s t → WP isa fail t Q) :
    WP isa (odds rest fail) s Q := by
  sorry

end VG.Proof.Dsa.PPC64LE

module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Base
import VerifiedGarbage.Proof.Framework.Offset

/-!
# An FFDH parameter candidate on PPC64LE: the result

`finish_ok`: `used := ` the octets read (0 for the status 0) and `r3 := `
the status.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search

theorem finish_ok (r : Nat) (hr : r ≤ 2) {s : State} {B U : Addr} {Z v : Nat} (hs : Scr s B Z) (hu : Scr s U 8)
    (h31 : s.gpr .r31 = B) (hU : s.mem.readW (B + BitVec.ofNat 64 32) 64 = U)
    (hV : s.mem.readW (B + BitVec.ofNat 64 152) 64 = BitVec.ofNat 64 v) (hZ : 160 ≤ Z) :
    WP isa (.block (finish r)) s fun t => (t.gpr .r3 = BitVec.ofNat 64 r ∧
      t.mem = s.mem.writeW (off U 0) (BitVec.ofNat 64 (if r = 0 then 0 else v))) ∧ Keep [.r3, .r4, .r5] s t := by
  obtain rfl | rfl | rfl : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  · refine WP.keep [.r3, .r4, .r5] ?_ (by decide)
    simp only [finish, ldh, hUsedP, ↓reduceIte]
    prun [h31, hU, hs.ld (d := 32) (n := 8) (by omega), hu.st (d := 0) (n := 8) (by omega)]
  all_goals
    refine WP.keep [.r3, .r4, .r5] ?_ (by decide)
    simp only [finish, ldh, hUsedP, hUsed, Nat.reduceEqDiff, ↓reduceIte, List.cons_append,
      List.nil_append]
    prun [h31, hU, hV, hs.ld (d := 32) (n := 8) (by omega), hs.ld (d := 152) (n := 8) (by omega),
      hu.st (d := 0) (n := 8) (by omega)]

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate

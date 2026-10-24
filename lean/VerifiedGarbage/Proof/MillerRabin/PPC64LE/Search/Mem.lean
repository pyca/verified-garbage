module

public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # A prime search on PPC64LE: words of the working space read through stores -/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE.Search

open VG VG.Proof.Bignum

theorem rw_off (m : Mem) (B : Addr) {a b : Nat} (v : BitVec 64) (hab : a + 8 ≤ b ∨ b + 8 ≤ a)
    (ha : a + 8 ≤ 2 ^ 64) (hb : b + 8 ≤ 2 ^ 64) :
    (m.writeW (B + BitVec.ofNat 64 a) v).readW (B + BitVec.ofNat 64 b) 64 = m.readW (B + BitVec.ofNat 64 b) 64 :=
  Mem.readW_writeW_sep (Offset.sep B (d := b) (e := a) (by simp only [Nat.reduceDiv]; omega) (by omega) (by omega))
    (by decide)

theorem rw_self (m : Mem) (a : Addr) (v : BitVec 64) : (m.writeW a v).readW a 64 = v :=
  Mem.readW_writeW_self64 m a v

/-- A store at a covered offset keeps a change within the ranges. -/
theorem frm_writeW {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm B rs m m') {a : Nat} (v : BitVec 64)
    (ha : ∃ r ∈ rs, r.1 ≤ a ∧ a + 8 ≤ r.1 + r.2) (ha' : a + 8 ≤ 2 ^ 64) :
    Frm B rs m (m'.writeW (B + BitVec.ofNat 64 a) v) :=
  h.trans ((Frm.of_outside (rs := [(a, 8)]) (writeW_outside m' B (d := a) v ha') (List.mem_singleton_self _)).widen
    fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact ha)

end VG.Proof.MillerRabin.PPC64LE.Search

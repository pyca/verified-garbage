import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelect
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Weierstrass.TCombLay

/-!
# The comb from tables in memory on AArch64: the tables

The tables at `T` (`TblMem`): `ws.length` words, readable, word `i` at
`T + 8 i` the word `i` of `ws`; they survive a change of the working space
only (`TblMem.unch`). For the comb's words (`tcombWords`), the words of
entry `m` of table `j` are its coordinates in Montgomery form
(`tbl_entry`, `tcombWords_entry`).
-/

namespace VG.Proof.Weierstrass.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass

/-- The words `ws` at `T`, readable (in one region). -/
structure TblMem (s : State) (T : Addr) (ws : List (BitVec 64)) : Prop where
  rd : InRegions (s.rd ++ s.wr) T (8 * ws.length)
  val : ∀ i < ws.length, s.mem.readW (T + BitVec.ofNat 64 (8 * i)) 64 = ws.getD i 0

/-- The tables survive a change of the memory that keeps their bytes and the
regions. -/
theorem TblMem.unch {s s' : State} {T : Addr} {ws : List (BitVec 64)} (h : TblMem s T ws)
    (hrd : s'.rd ++ s'.wr = s.rd ++ s.wr)
    (hm : ∀ i < ws.length, ∀ b < 8,
      s'.mem (T + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b) =
        s.mem (T + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)) :
    TblMem s' T ws :=
  ⟨hrd ▸ h.rd, fun i hi => by
    rw [← h.val i hi]; exact Mem.readW_congr fun b hb => hm i hi b (by omega)⟩

/-- The `x` and `y` of entry `m` of table `j`, in Montgomery form, at
`16 n m` and `16 n m + 8 n` bytes into the table, at `T + 16 n H j`. -/
theorem tbl_entry {s : State} {T : Addr} {n R p H J : Nat} {tbl : List (List (Nat × Nat))}
    (hT : TblMem s T (tcombWords n R p tbl)) (hJ : tbl.length = J)
    (hH : ∀ j < J, (tbl.getD j []).length = H) {j m : Nat} (hj : j < J) (hm : m < H)
    (hx : (combAt tbl j m).1 * R % p < 2 ^ (64 * n)) (hy : (combAt tbl j m).2 * R % p < 2 ^ (64 * n)) :
    wordsVal s.mem (T + BitVec.ofNat 64 (j * (16 * n * H))) (16 * n * m) n = (combAt tbl j m).1 * R % p ∧
    wordsVal s.mem (T + BitVec.ofNat 64 (j * (16 * n * H))) (16 * n * m + 8 * n) n =
      (combAt tbl j m).2 * R % p :=
  tcombWords_entry hT.val hJ hH hj hm hx hy

end VG.Proof.Weierstrass.AArch64

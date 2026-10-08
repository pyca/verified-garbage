import VerifiedGarbage.Proof.Weierstrass.CombLay
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Impl.Weierstrass.X86.TComb
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Weierstrass.X86.CallOps

/-!
# The fixed-base comb from tables in memory on x86 (32-bit): where it keeps its numbers

As on AArch64 (`Proof/Weierstrass/TCombLay.lean`): `TCombCfg.toComb` is the
comb of the same slots with no tables, whose layout (`CombLay`) the comb's
(`TCombLay`) contains, so the addition's facts are the comb's; the table of
bits is `w J` bytes, those past the scalar's `kbytes` cleared in words by the
comb. The tables are at `T` (`TblMem`): readable, word `i` at `T + 8 i`, and
they survive a change of the working space only (`TblMem.of_unch`).
-/

namespace VG.Proof.Weierstrass.X86

open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Proof.Mont
open VG.Proof.Weierstrass VG.Proof.Mont.X86

/-- Where the field arithmetic's functions keep their own working space. -/
abbrev _root_.VG.Impl.Weierstrass.X86.TCombCfg.wk (K : TCombCfg) : Nat := Mont.own K.M.n

/-- The comb of the same slots, with `J` empty tables. Its table of bits is
the comb's (`TCombLay`'s `bits`, past byte 4096 here), not `CombLay`'s:
that one is the functions' own working space, which no step of the comb
reads, as a placeholder below byte 4096. -/
def _root_.VG.Impl.Weierstrass.X86.TCombCfg.toComb (K : TCombCfg) : CombCfg where
  M := K.M
  S := K.S
  A := K.A
  E := K.E
  D := K.D
  neg := K.neg
  zero := K.zero
  bits := K.wk
  tbl := List.replicate K.J []
  start := K.start
  one := K.one

theorem _root_.VG.Impl.Weierstrass.X86.TCombCfg.toComb_J (K : TCombCfg) : K.toComb.J = K.J := by
  simp [CombCfg.J, TCombCfg.toComb]

/-- What the comb writes: the comb's, the functions' own working space and
memory past the working space (the calls'); and the cleared words of the
table of bits. -/
def combWx (K : TCombCfg) : List (Nat × Nat) := combW K.toComb ++ [(K.wk, 64 * K.M.n), Mont.outW]

def tcombW (K : TCombCfg) : List (Nat × Nat) :=
  combWx K ++ [(K.bits + K.kbytes, 4 * K.zw)]

/-- The comb's layout (`CombLay` of `toComb`); the table of bits of `w J`
bytes (and its cleared words) in the working space, apart from what the loop
writes and its cleared words apart from the slots and the modulus; `E`'s `y`
right after its `x`; and the digits' width and number, the field's words and
the tables' size in range. -/
structure TCombLay (K : TCombCfg) (size : Nat) : Prop where
  comb : CombLay K.toComb size
  sz : size = 8192
  wsl : ∀ x, x ∈ combSlots K.toComb → x + 8 * K.M.n ≤ K.wk
  wmo : K.M.mo + 8 * K.M.n ≤ K.wk
  wtmp : K.M.tmp + 8 * K.M.n ≤ K.wk
  wk_bits : K.bits + K.kbytes + 4 * K.zw ≤ K.wk ∨ K.wk + 64 * K.M.n ≤ K.bits
  ptr_le : K.ptr + 4 ≤ size
  ptr_sl : ∀ x ∈ K.M.mo :: K.M.tmp :: combSlots K.toComb,
    K.ptr + 4 ≤ x ∨ x + 8 * K.M.n ≤ K.ptr
  ptr_wk : K.ptr + 4 ≤ K.wk
  ptr_bits : K.ptr + 4 ≤ K.bits ∨ K.bits + K.kbytes + 4 * K.zw ≤ K.ptr
  w : 1 ≤ K.w ∧ K.w < 9
  kbytes : K.kbytes ≤ K.w * K.J
  bits : K.bits + K.kbytes + 4 * K.zw ≤ size
  bits4 : (K.bits + K.kbytes) % 4 = 0
  bits_w : ∀ w ∈ combW K.toComb, K.bits + K.kbytes + 4 * K.zw ≤ w.1 ∨ w.1 + w.2 ≤ K.bits
  bits_sl : ∀ x ∈ K.M.mo :: combSlots K.toComb,
    K.bits + K.kbytes + 4 * K.zw ≤ x ∨ x + 8 * K.M.n ≤ K.bits + K.kbytes
  n : 1 ≤ K.M.n ∧ K.M.n ≤ 6
  exy : K.E.y = K.E.x + 8 * K.M.n
  tbl : K.tblBytes < 2 ^ 31

/-- The functions' own working space ends at byte 4096. -/
theorem TCombLay.wk_le {K : TCombCfg} {size : Nat} (hL : TCombLay K size) : K.wk + 64 * K.M.n ≤ size := by
  have := hL.n; have := hL.sz
  simp only [TCombCfg.wk, Mont.own, Spec.Weierstrass.Mont.ownAt, Spec.Weierstrass.Mont.ownBytes]; omega

/-- The comb's slots, below the functions' own working space, as the field
programs need them. -/
theorem TCombLay.wkOk {K : TCombCfg} {size m : Nat} (hL : TCombLay K size)
    (hF : K.F.k = K.M.n ∧ K.F.m = m ∧ Mont.FnOk K.F) : WkOk K.F K.M m size K.wk (· ∈ combSlots K.toComb) where
  fn := hF.2.2
  k := hF.1
  fm := hF.2.1
  size := hL.sz
  own := rfl
  sl := hL.wsl
  mo := hL.wmo
  tmp := hL.wtmp

/-- The words `ws` at `T`, readable (in one region). -/
structure TblMem (s : State) (T : Addr) (ws : List (BitVec 64)) : Prop where
  nowrap : T.toNat + 8 * ws.length ≤ 2 ^ 32
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
  ⟨h.nowrap, hrd ▸ h.rd, fun i hi => by
    rw [← h.val i hi]; exact Mem.readW_congr fun b hb => hm i hi b (by omega)⟩

/-- The tables survive a change of the working space, which they are past. -/
theorem TblMem.of_unch {s s' : State} {T : Addr} {ws : List (BitVec 64)} {base : Addr} {size : Nat}
    {W : List (Nat × Nat)} (h : TblMem s T ws) (hrd : s'.rd ++ s'.wr = s.rd ++ s.wr)
    (hU : Unch base W s.mem s'.mem) (hW : ∀ w ∈ W, w.1 + w.2 ≤ size)
    (hout : ∀ i < ws.length, ∀ b < 8, size ≤ ofs base (T + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)) :
    TblMem s' T ws :=
  h.unch hrd fun i hi b hb => hU _ fun w hw => Or.inr (by have := hW w hw; have := hout i hi b hb; omega)

/-- The tables survive code that changes memory only in the regions `L`,
which they are apart from. -/
theorem TblMem.of_frame {s s' : State} {T : Addr} {ws : List (BitVec 64)} {L : List Region}
    (h : TblMem s T ws) (hrd : s'.rd ++ s'.wr = s.rd ++ s.wr) (hf : Frame L s.mem s'.mem)
    (hd : ∀ r ∈ L, Region.Disjoint ⟨T, 8 * ws.length⟩ r) : TblMem s' T ws :=
  h.unch hrd fun i hi b hb => by
    rw [Offset.add_add]
    exact hf.bytes (R := ⟨T, 8 * ws.length⟩) hd (by have := h.nowrap; dsimp only; omega)
      (by dsimp only; omega)

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

end VG.Proof.Weierstrass.X86

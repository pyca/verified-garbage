import VerifiedGarbage.Proof.RsaPss.AArch64.VerifyParts

/-!
# RSASSA-PSS verification on AArch64: unmasking `DB`

From RSAVP1's result in `EM`: the first checks into `acc` (`acc0`), `DB`
unmasked (`mgfXor`) and its top bits cleared (`clearTop`), its first
nonzero byte found (`posScan`) and checked (`posCheck`): `b1_ok`.
-/

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.MlKem.AArch64 (Only Keep MemTo)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)

/-- `EM` after the mask and `clearTop`, from `V`, with `DB` at `e`. -/
def wct (V : Nat → Byte) (mk : List Byte) (e db : Nat) (c : Byte) : Nat → Byte :=
  upd (mixV V mk e db) e (mixV V mk e db e &&& c)

/-- The mask: MGF1 of `H`, the `hLen` bytes after `DB`. -/
def mkB (G : Spec.Mgf1.Hash) (D : Nat) (V : Nat → Byte) (e db : Nat) : List Byte :=
  Spec.Mgf1.mgf1 G ((List.range D).map fun i => V (e + db + i)) db

/-- `acc` after `acc0`. -/
def acc0V (V : Nat → Byte) (k lo : Nat) (c : Byte) : BitVec 64 :=
  ((V (oEm + k - 1)).setWidth 64 ^^^ BitVec.ofNat 64 0xbc) |||
    ((V oEm).setWidth 64 &&& (0#64 - BitVec.ofNat 64 lo)) |||
    ((V (oEm + lo)).setWidth 64 &&& (c.setWidth 64 ^^^ BitVec.ofNat 64 0xFF))

/-- `acc` after `posCheck`, for `DB`'s bytes `f`. -/
def acc1V (a0 : BitVec 64) (f : Nat → Byte) (db : Nat) (any sv : BitVec 64) : BitVec 64 :=
  (a0 ||| (((nzV f db).setWidth 64 ^^^ 1#64) |||
    (if nz f db = none then BitVec.allOnes 64 else 0) >>> 63)) |||
    (if any = 0 then sv ^^^ BitVec.ofNat 64 (db - (nz f db).getD 0 - 1) else 0)

/-- After `posCheck`. -/
structure B1 (G : Spec.Mgf1.Hash) (D : Nat) (t : State) (F S : Addr) (V : Nat → Byte) (k lo db : Nat) (c : Byte)
    (any sv : BitVec 64) (u : State) : Prop where
  sp : u.sp = t.sp
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  cs : ∀ r ∈ [Reg.x19, .x20, .x21, .x23, .x24, .x25], u.gpr r = t.gpr r
  v : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64
  fr : Frame (mgfWr F S ++ [slotR F sPos]) t.mem u.mem
  em : ∀ o, oEm ≤ o → o < oY → u.mem (off S o) = wct V (mkB G D V (oEm + lo) db) (oEm + lo) db c o
  pos : u.mem.readW (off F sPos) 64 =
    BitVec.ofNat 64 ((nz (fun i => wct V (mkB G D V (oEm + lo) db) (oEm + lo) db c (oEm + lo + i)) db).getD 0)
  acc : u.gpr .x26 = acc1V (acc0V V k lo c)
    (fun i => wct V (mkB G D V (oEm + lo) db) (oEm + lo) db c (oEm + lo + i)) db any sv

end VG.Proof.RsaPss.AArch64

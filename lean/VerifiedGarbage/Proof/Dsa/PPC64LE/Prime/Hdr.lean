module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Prime.Load
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA's probable-prime test on PPC64LE: the header

`Hdr`: the header's words after the entry (`hdr_of`), for the working space
at `B = ws + keyOff`: its length, the table's entries, `w`,
the arrays' size and addresses, the tape and its length, no octets read,
and the search's parameters. `Hdr.keep`: a change of memory that keeps the
header's words keeps `Hdr`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Prime
open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE
open VG.Impl.Dsa.PPC64LE.ProbablePrime
open VG.Impl.MillerRabin.PPC64LE.Search
open VG.Impl.MillerRabin.PPC64LE.Blinded (hUni hTopOff)
open VG.Impl.Bignum (hdrBytes)
open VG.Proof.Bignum (word off slot)

/-- The header's words. -/
structure Hdr (bits : Nat) (ws R : Addr) (rl : BitVec 64) (m : Mem) : Prop where
  len : word m (ws + BitVec.ofNat 64 keyOff) 0 = BitVec.ofNat 64 (keyWords bits)
  cnt : word m (ws + BitVec.ofNat 64 keyOff) (8 * hCnt) = BitVec.ofNat 64 (count bits)
  w : word m (ws + BitVec.ofNat 64 keyOff) 48 = BitVec.ofNat 64 (words bits)
  arr : ∀ j < 8, word m (ws + BitVec.ofNat 64 keyOff) (8 * (8 + j)) =
    off (ws + BitVec.ofNat 64 keyOff) (slot (words bits) j)
  topOff : word m (ws + BitVec.ofNat 64 keyOff) (8 * hTopOff) = BitVec.ofNat 64 (topOff bits)
  rand : word m (ws + BitVec.ofNat 64 keyOff) (8 * hRand) = R
  randLen : word m (ws + BitVec.ofNat 64 keyOff) (8 * hRandLen) = rl
  used : word m (ws + BitVec.ofNat 64 keyOff) (8 * hUsed) = BitVec.ofNat 64 0
  checks : word m (ws + BitVec.ofNat 64 keyOff) (8 * hChecks) = BitVec.ofNat 64 (checks bits)
  top : word m (ws + BitVec.ofNat 64 keyOff) (8 * hTop) = BitVec.ofNat 64 (2 ^ topBits bits - 1)
  k : word m (ws + BitVec.ofNat 64 keyOff) (8 * hK) = BitVec.ofNat 64 (draw bits)
  stride : word m (ws + BitVec.ofNat 64 keyOff) 224 = BitVec.ofNat 64 (8 * (words bits + 2))

/-- The header's word offsets. -/
def hdrWords : List Nat := hdrSlots.map Prod.snd

theorem hdrWords_eq : hdrWords = [0, 40, 48, 64, 72, 80, 88, 96, 104, 112, 120, 128, 136, 144, 152, 168,
    192, 216, 224] := by decide

/-- A change of memory that keeps the header's words. -/
theorem Hdr.keep {bits : Nat} {ws R : Addr} {rl : BitVec 64} {m m' : Mem} (h : Hdr bits ws R rl m)
    (hw : ∀ d ∈ hdrWords, word m' (ws + BitVec.ofNat 64 keyOff) d = word m (ws + BitVec.ofNat 64 keyOff) d) :
    Hdr bits ws R rl m' := by
  rw [hdrWords_eq] at hw
  refine ⟨(hw _ (by simp)).trans h.len,
    (hw _ (by simp [hCnt])).trans h.cnt, (hw _ (by simp)).trans h.w, fun j hj => ?_,
    (hw _ (by simp [hTopOff])).trans h.topOff, (hw _ (by simp [hRand])).trans h.rand,
    (hw _ (by simp [hRandLen])).trans h.randLen, (hw _ (by simp [hUsed])).trans h.used,
    (hw _ (by simp [hChecks])).trans h.checks, (hw _ (by simp [hTop])).trans h.top, (hw _ (by simp [hK])).trans h.k,
    (hw _ (by simp)).trans h.stride⟩
  refine (hw _ ?_).trans (h.arr j hj)
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- After the entry. -/
theorem hdr_of {bits : Nat} {σ s : State} (ep : EntryPost bits σ s) :
    Hdr bits (σ.gpr .r3) (σ.gpr .r5) (σ.gpr .r6) s.mem := by
  have hr := ep.regs
  have sv : ∀ r d, (r, d) ∈ hdrSlots → word s.mem (σ.gpr .r3 + BitVec.ofNat 64 keyOff) d = s.gpr r := fun r d hm => by
    have := ep.hdr (r, d) hm
    rw [hr.r31] at this
    exact this
  have o : ∀ r, r ∉ valRegs → r ≠ .r0 → s.gpr r = σ.gpr r := ep.other
  refine ⟨(sv .r14 _ (by decide)).trans hr.r14, (sv .r21 _ (by decide)).trans hr.r21,
    (sv .r16 _ (by decide)).trans hr.r16, fun j hj => ?_, (sv .r19 _ (by decide)).trans hr.r19,
    (sv .r5 _ (by decide)).trans (o .r5 (by decide) (by decide)),
    (sv .r6 _ (by decide)).trans (o .r6 (by decide) (by decide)), (sv .r15 _ (by decide)).trans hr.r15,
    (sv .r20 _ (by decide)).trans hr.r20, (sv .r18 _ (by decide)).trans hr.r18, (sv .r17 _ (by decide)).trans hr.r17,
    (sv .r29 _ (by decide)).trans hr.r29⟩
  rw [sv (arrReg j) _ (by
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), hr.arr j hj]
  show _ = σ.gpr .r3 + BitVec.ofNat 64 keyOff + BitVec.ofNat 64 (slot (words bits) j)
  rw [Offset.add_add]
  rfl

end VG.Proof.Dsa.PPC64LE.Prime

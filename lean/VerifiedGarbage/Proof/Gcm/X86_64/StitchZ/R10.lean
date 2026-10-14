module

public import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Spec
public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.CtrBe

/-!
# What `r10` holds in the AVX-512 loops

`R10`: the address of the last round key, as `Stitch.setupC` leaves it; or,
for the loops given a public block index (`be`), the index of the next block,
less one, in the top byte of `r10d` (`idxR`), with the constants of the
counters added to as bytes in the working space (`BeConsts`).
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZ

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch (nr kp pp cb)

/-- 16 in doubleword 0 of a lane: sixteen counter blocks on. -/
abbrev sixteen : BitVec 128 := 16#128

/-- With a public block index, `r10` before a batch of blocks from `c` on: the
index of block `c`, less one, in its top byte (an `add r10d, 0x10000000`
carries out of it exactly when the low byte of the sixteen indices from `c`
on might wrap around). -/
def idxR (s₀ : State) (c : Nat) : BitVec 64 :=
  (((cb s₀).extractLsb' 0 32 + BitVec.ofNat 32 c - 1) <<< 24).setWidth 64

/-- The constants of the counters added to as bytes, `beFour` and `sixteen`,
in the working space at `p + 896` and `p + 912`. -/
def BeConsts (p : Addr) (m : Mem) : Prop :=
  m.readW (p + BitVec.ofNat 64 896) 128 = beFour ∧ m.readW (p + BitVec.ofNat 64 912) 128 = sixteen

/-- What `r10` holds in the loops: the last round key's address, or, with a
public block index (`be`), `idxR`, and the working space holds `BeConsts`. -/
def R10 (be : Bool) (s₀ : State) (c : Nat) (s : State) : Prop :=
  if be then s.gpr .r10 = idxR s₀ c ∧ BeConsts (pp s₀) s.mem
  else s.gpr .r10 = kp s₀ + BitVec.ofNat 64 (16 * nr s₀)

theorem R10.keep {be : Bool} {s₀ : State} {c : Nat} {s s' : State} (h : R10 be s₀ c s)
    (hg : s'.gpr .r10 = s.gpr .r10) (hm : s'.mem = s.mem) : R10 be s₀ c s' := by
  cases be
  · simp only [R10, Bool.false_eq_true, ↓reduceIte] at h ⊢; rw [hg]; exact h
  · simp only [R10, ↓reduceIte] at h ⊢; rw [hg, hm]; exact h

end VG.Proof.Gcm.X86_64.StitchZ

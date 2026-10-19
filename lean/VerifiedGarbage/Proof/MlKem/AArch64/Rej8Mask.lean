module

public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Sum
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Value

/-! # Connecting acceptance predicates to the packed table index and count -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Rej8
open VG VG.AArch64 VG.Impl.MlKem.AArch64.Rej8

def mask8 (a b c d e f g h : Bool) : Nat :=
  (if a then 1 else 0) + (if b then 2 else 0) + (if c then 4 else 0) +
  (if d then 8 else 0) + (if e then 16 else 0) + (if f then 32 else 0) +
  (if g then 64 else 0) + (if h then 128 else 0)

def weight8 (a b c d e f g h : Bool) : BitVec 16 :=
  (if a then BitVec.ofNat 16 257 else 0) + (if b then BitVec.ofNat 16 258 else 0) + (if c then BitVec.ofNat 16 260 else 0) +
  (if d then BitVec.ofNat 16 264 else 0) + (if e then BitVec.ofNat 16 272 else 0) + (if f then BitVec.ofNat 16 288 else 0) +
  (if g then BitVec.ofNat 16 320 else 0) + (if h then BitVec.ofNat 16 384 else 0)

theorem mask8_bound : ∀ a b c d e f g h, mask8 a b c d e f g h < 256 := by decide +kernel

theorem mask8_bits : ∀ a b c d e f g h, ∀ i < 8,
    ((mask8 a b c d e f g h / 2^i)%2 == 1) = [a,b,c,d,e,f,g,h].getD i false := by decide +kernel

theorem weight8_exact : ∀ a b c d e f g h,
    weight8 a b c d e f g h = BitVec.ofNat 16 (packedCount (mask8 a b c d e f g h)) := by decide +kernel

/-- Acceptance mask of eight decoded candidates. -/
def acceptanceMask (x : BitVec 128) : Nat :=
  mask8 (decide ((vhalf x 0).toNat < 3329)) (decide ((vhalf x 1).toNat < 3329))
    (decide ((vhalf x 2).toNat < 3329)) (decide ((vhalf x 3).toNat < 3329))
    (decide ((vhalf x 4).toNat < 3329)) (decide ((vhalf x 5).toNat < 3329))
    (decide ((vhalf x 6).toNat < 3329)) (decide ((vhalf x 7).toNat < 3329))

theorem acceptanceMask_bound (x : BitVec 128) : acceptanceMask x < 256 := mask8_bound ..

theorem acceptanceMask_bits (x : BitVec 128) {i : Nat} (hi : i < 8) :
    ((acceptanceMask x / 2^i)%2 == 1) = decide ((vhalf x i).toNat < 3329) := by
  rw [acceptanceMask,mask8_bits _ _ _ _ _ _ _ _ i hi]
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl

/-- The horizontal sum really is the table index and accepted count for
these candidates, without modular overflow in the halfword lanes. -/
theorem accepted_sum {x y : BitVec 128}
    (hy : ∀ i < 8, vhalf y i = if (vhalf x i).toNat < 3329 then BitVec.ofNat 16 (256+2^i) else 0) :
    sum8 y = BitVec.ofNat 16 (packedCount (acceptanceMask x)) := by
  rw [sum8,hy 0 (by decide),hy 1 (by decide),hy 2 (by decide),hy 3 (by decide),
    hy 4 (by decide),hy 5 (by decide),hy 6 (by decide),hy 7 (by decide)]
  simpa only [weight8, decide_eq_true_eq, Nat.reducePow, Nat.reduceAdd, acceptanceMask] using
    weight8_exact (decide ((vhalf x 0).toNat < 3329)) (decide ((vhalf x 1).toNat < 3329))
      (decide ((vhalf x 2).toNat < 3329)) (decide ((vhalf x 3).toNat < 3329))
      (decide ((vhalf x 4).toNat < 3329)) (decide ((vhalf x 5).toNat < 3329))
      (decide ((vhalf x 6).toNat < 3329)) (decide ((vhalf x 7).toNat < 3329))

end VG.Proof.MlKem.AArch64.Rej8

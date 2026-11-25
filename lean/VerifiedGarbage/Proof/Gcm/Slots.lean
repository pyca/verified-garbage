module

public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# GHASH: words of working space

Untrusted: everything here is checked by Lean. `Slots m₀ m p n f`: the `n`
doublewords at `p` in `m` hold `f 0`, `f 1`, …, and `m` agrees with `m₀`
everywhere else.
-/

@[expose] public section

namespace VG.Proof.Gcm

structure Slots (m₀ m : Mem) (p : Addr) (n : Nat) (f : Nat → BitVec 64) : Prop where
  get : ∀ k < n, m.readW (p + BitVec.ofNat 64 (8 * k)) 64 = f k
  frame : Frame [⟨p, 8 * n⟩] m₀ m

namespace Slots

variable {m₀ m : Mem} {p : Addr} {n : Nat} {f : Nat → BitVec 64}

theorem init (m : Mem) (p : Addr) (n : Nat) :
    Slots m m p n fun k => m.readW (p + BitVec.ofNat 64 (8 * k)) 64 := ⟨fun _ _ => rfl, Frame.refl _ _⟩

theorem contains (p : Addr) {k n : Nat} (hk : k < n) (hn : 8 * n < 2 ^ 64) :
    (⟨p, 8 * n⟩ : Region).Contains (p + BitVec.ofNat 64 (8 * k)) 8 :=
  Offset.contains_base p (by omega) (by omega)

theorem store (h : Slots m₀ m p n f) {k : Nat} (hk : k < n) (hn : 8 * n < 2 ^ 64) (v : BitVec 64) :
    Slots m₀ (m.writeW (p + BitVec.ofNat 64 (8 * k)) v) p n fun j => if j = k then v else f j := by
  refine ⟨fun j hj => ?_, h.frame.writeW (List.mem_singleton.mpr rfl) v (contains p hk hn)⟩
  by_cases e : j = k
  · subst e; rw [ite_eq_left rfl]; exact Mem.readW_writeW_self64 _ _ _
  · rw [ite_eq_right e, Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)]
    exact h.get j hj

end Slots

end VG.Proof.Gcm

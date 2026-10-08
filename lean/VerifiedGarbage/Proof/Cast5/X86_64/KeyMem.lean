import VerifiedGarbage.Proof.Cast5.X86_64.KeyLine

/-!
# CAST5 key expansion on x86-64: the working space and the subkeys

The working space at `c` holds `x` and `z` (`HoldsXZ`) and the group's extra
lookups (`Extras`); the subkeys so far are at `K` (`Keys`). Each write of key
expansion keeps what it does not overwrite.
-/

namespace VG.Proof.Cast5.X86_64

open VG VG.X86_64 VG.Impl.Cast5 VG.Impl.Cast5.X86_64

/-- The group's extra lookups, lanes `0 … 3` at `c + 48`. -/
def Extras (m : Mem) (c : Addr) (f : Nat → Spec.Cast5.Word) : Prop :=
  ∀ j < 4, m.readW (c + BitVec.ofNat 64 (extraOff + 4 * j)) 32 = f j

/-- `Extras` after a write of `w / 8` bytes at `c + d`, below them. -/
theorem Extras.write {m : Mem} {c : Addr} {f : Nat → Spec.Cast5.Word} (h : Extras m c f) {d w : Nat}
    (v : BitVec w) (hd : d + w / 8 ≤ extraOff) :
    Extras (m.writeW (c + BitVec.ofNat 64 d) v) c f := fun j hj => by
  rw [Mem.readW_writeW_sep (Offset.sep c (by unfold extraOff at *; omega) (by unfold extraOff; omega)
    (by unfold extraOff at *; omega)) (by decide)]
  exact h j hj

/-- `Extras` after a write elsewhere. -/
theorem Extras.write_disj {m : Mem} {c : Addr} {f : Nat → Spec.Cast5.Word} (h : Extras m c f) {a : Addr}
    {w : Nat} (v : BitVec w) (hd : Region.Disjoint ⟨c, 64⟩ ⟨a, w / 8⟩) :
    Extras (m.writeW a v) c f := fun j hj => by
  rw [Mem.readW_writeW_sep (hd.sep (Offset.contains_base c (by unfold extraOff; omega)
    (by unfold extraOff; omega)) (Region.contains_self _ _)) (by decide)]
  exact h j hj

end VG.Proof.Cast5.X86_64

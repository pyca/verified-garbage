module

public import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# PPC64LE: weakest preconditions of byte loads and stores

`wp_lbz` and `wp_stb`, as `Step.lean`'s `wp_*` for words: each runs the
first instruction of a block and hands the continuation the next state,
described by `Upd` or `Mupd`.
-/

@[expose] public section

namespace VG.PPC64LE

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `lbz t, off(n)` -/
theorem wp_lbz {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' t ((s.mem a).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.lbz t n off :: is)) s Q := by
  refine WP.cons (s' := s.write t ((s.mem a).setWidth 64)) ?_ (k _ (Upd.write _ _ _))
  rw [exec_lbz hn ho (by rw [ha]; exact hin), ha]
  simp only [Mem.read]
  congr 2
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_append]
  simp

/-- `stb t, off(n)` -/
theorem wp_stb {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.stb t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl⟩)
  rw [exec_stb hn ho (by rw [ha]; exact hout), ha]
  rfl

end

/-- A byte write, at any address. -/
theorem write1_apply (m : Mem) (a x : Addr) (v : BitVec 8) :
    m.writeW a v x = if (x - a).toNat < 1 then v else m x := by
  simp only [Mem.writeW, Mem.write]
  split
  · rename_i h
    rw [show (x - a).toNat = 0 by omega]
    simp
  · rfl

theorem setWidth8_64 (u : Byte) : (u.setWidth 64).setWidth 8 = u := by
  ext j hj
  simp

end VG.PPC64LE

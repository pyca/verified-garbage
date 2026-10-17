module

public import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Init
public import VerifiedGarbage.Proof.MdStream.AArch64.OneShot
import VerifiedGarbage.Proof.Framework.ReadHalves
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# Streaming SHA-256 on AArch64: `initPairs`

The initial hash value stored by pairs of words packed in doublewords, for
the one-shot digests: the same postcondition as `initWith`'s.
-/

@[expose] public section

namespace VG.Proof.Sha256.AArch64.Stream

open VG VG.AArch64 VG.Impl.Sha256.AArch64.Stream
open VG.Proof.Sha256.AArch64 (contains_offset)
open VG.Spec.Sha256 (HashValue)

/-- The nine instructions storing the 64-bit words `x` and `y` at `[x0 + off]`. -/
def pair (x y : BitVec 64) (off : Nat) : List Instr :=
  movImm64 .x9 x ++ movImm64 .x10 y ++ ([.stp .x9 .x10 .x0 off] : List Instr)

theorem initPairs_eq (iv : HashValue) : initPairs iv =
    .block (pair (iv[1] ++ iv[0]) (iv[3] ++ iv[2]) 0 ++ pair (iv[5] ++ iv[4]) (iv[7] ++ iv[6]) 16) := rfl

theorem pair_ok {x y : BitVec 64} {off : Nat} (ho : off % 8 = 0 ∧ off ≤ 504) {rest : List Instr}
    {s : State} {Q : State → Prop} (hout : ∀ j ≤ 8, InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 (off + j)) 8)
    (k : ∀ s', (∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      s'.mem = (s.mem.writeW (s.gpr .x0 + BitVec.ofNat 64 off) x).writeW
        (s.gpr .x0 + BitVec.ofNat 64 (off + 8)) y → WP isa (.block rest) s' Q) :
    WP isa (.block (pair x y off ++ rest)) s Q := by
  simp only [pair, movImm64, List.cons_append, List.nil_append]
  refine MdStream.AArch64.WP.cons rfl (MdStream.AArch64.WP.cons rfl (MdStream.AArch64.WP.cons rfl
    (MdStream.AArch64.WP.cons rfl (MdStream.AArch64.WP.cons rfl (MdStream.AArch64.WP.cons rfl
    (MdStream.AArch64.WP.cons rfl (MdStream.AArch64.WP.cons rfl ?_)))))))
  refine MdStream.AArch64.OneShot.wp_stpB ho (b := s.gpr .x0) (by simp [State.write])
    (by simpa [State.write] using hout 0 (by omega)) (by simpa [State.write] using hout 8 (by omega))
    fun s' m => k s' (fun r h9 h10 => by rw [m.gpr]; simp [State.write, h9, h10]) (by rw [m.rd]; rfl)
      (by rw [m.wr]; rfl) (by rw [m.sp]; rfl) ?_
  rw [m.mem]
  simp only [State.write, State.read, Size.bits, BitVec.setWidth_eq, ite_true]
  simp only [show Reg.x9 ≠ Reg.x10 by decide, ite_false]
  rw [movz_movk64' x, movz_movk64' y]

/-- The memory after the two pairs of doublewords `a`, `b` and `c`, `d` at `p`. -/
def quad (m : Mem) (p : Addr) (a b c d : BitVec 64) : Mem :=
  (((m.writeW (p + BitVec.ofNat 64 0) a).writeW (p + BitVec.ofNat 64 (0 + 8)) b).writeW
    (p + BitVec.ofNat 64 16) c).writeW (p + BitVec.ofNat 64 (16 + 8)) d

theorem quad_read (m : Mem) (p : Addr) (a b c d : BitVec 64) :
    (quad m p a b c d).readW (p + BitVec.ofNat 64 0) 64 = a ∧
    (quad m p a b c d).readW (p + BitVec.ofNat 64 8) 64 = b ∧
    (quad m p a b c d).readW (p + BitVec.ofNat 64 16) 64 = c ∧
    (quad m p a b c d).readW (p + BitVec.ofNat 64 24) 64 = d := by
  have s : ∀ d e : Nat, d + 8 ≤ e ∨ e + 8 ≤ d → d + 8 ≤ 32 → e + 8 ≤ 32 → ∀ (m : Mem) (v : BitVec 64),
      (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) 64 = m.readW (p + BitVec.ofNat 64 d) 64 :=
    fun d e h hd he _ _ => Mem.readW_writeW_sep (Offset.sep p h (by omega) (by omega)) (by decide)
  refine ⟨?_, ?_, ?_, Mem.readW_writeW_self64 _ _ _⟩
  · rw [quad, s 0 (16 + 8) (by decide) (by decide) (by decide), s 0 16 (by decide) (by decide) (by decide),
      s 0 (0 + 8) (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [quad, s 8 (16 + 8) (by decide) (by decide) (by decide), s 8 16 (by decide) (by decide) (by decide)]
    exact Mem.readW_writeW_self64 _ _ _
  · rw [quad, s 16 (16 + 8) (by decide) (by decide) (by decide), Mem.readW_writeW_self64]

/-- The eight words of the two pairs of doublewords, read back. -/
theorem pairs_read (m : Mem) (p : Addr) (iv : HashValue) {k : Nat} (hk : k < 8) :
    (quad m p (iv[1] ++ iv[0]) (iv[3] ++ iv[2]) (iv[5] ++ iv[4]) (iv[7] ++ iv[6])).readW
      (p + BitVec.ofNat 64 (4 * k)) 32 = iv[k] := by
  obtain ⟨h0, h1, h2, h3⟩ := quad_read m p (iv[1] ++ iv[0]) (iv[3] ++ iv[2]) (iv[5] ++ iv[4]) (iv[7] ++ iv[6])
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (Mem.readW_lo32 h0).trans BitVec.setWidth_append_eq_right
  · rw [← Offset.add_add_eq p (rfl : 0 + 4 = 4 * 1)]
    exact (Mem.readW_hi32 h0).trans BitVec.extractLsb'_append_eq_left
  · exact (Mem.readW_lo32 h1).trans BitVec.setWidth_append_eq_right
  · rw [← Offset.add_add_eq p (rfl : 8 + 4 = 4 * 3)]
    exact (Mem.readW_hi32 h1).trans BitVec.extractLsb'_append_eq_left
  · exact (Mem.readW_lo32 h2).trans BitVec.setWidth_append_eq_right
  · rw [← Offset.add_add_eq p (rfl : 16 + 4 = 4 * 5)]
    exact (Mem.readW_hi32 h2).trans BitVec.extractLsb'_append_eq_left
  · exact (Mem.readW_lo32 h3).trans BitVec.setWidth_append_eq_right
  · rw [← Offset.add_add_eq p (rfl : 24 + 4 = 4 * 7)]
    exact (Mem.readW_hi32 h3).trans BitVec.extractLsb'_append_eq_left

theorem initPairs_correct {s₀ : State} (iv : HashValue) (hp : (Proof.Sha256.initAArch64 iv).pre s₀) :
    WP isa (initPairs iv) s₀ fun s' => abiPreserved s₀ s' ∧ (Proof.Sha256.initAArch64 iv).post s₀ s' := by
  apply WP.withPreservedV (hc := by rfl)
  obtain ⟨-, hwr⟩ := hp
  have o : ∀ j, j + 8 ≤ 32 → InRegions s₀.wr (s₀.gpr .x0 + BitVec.ofNat 64 j) 8 :=
    fun j hj => ⟨⟨s₀.gpr .x0, 96⟩, by simp [hwr], contains_offset (by omega) (by omega)⟩
  rw [initPairs_eq, ← List.append_nil (_ ++ pair (iv[5] ++ iv[4]) (iv[7] ++ iv[6]) 16)]
  simp only [List.append_assoc]
  refine pair_ok (by decide) (fun j hj => o _ (by omega)) fun s1 g1 _ wr1 sp1 m1 => ?_
  have k1 : s1.gpr .x0 = s₀.gpr .x0 := g1 _ (by decide) (by decide)
  refine pair_ok (by decide) (fun j hj => by rw [wr1, k1]; exact o _ (by omega))
    fun s2 g2 _ _ sp2 m2 => WP.block_nil ?_
  have k2 : ∀ r, r ≠ .x9 → r ≠ .x10 → s2.gpr r = s₀.gpr r := fun r h9 h10 => by
    rw [g2 r h9 h10, g1 r h9 h10]
  refine ⟨⟨fun r hr => k2 r ?_ ?_, by rw [sp2, sp1]⟩, ?_⟩
  · rintro rfl; simp [preserved] at hr
  · rintro rfl; simp [preserved] at hr
  · show Spec.Sha256.ReprFrom iv s2.mem (s₀.gpr .x0) []
    refine Proof.Sha256.Stream.reprFrom_nil (Proof.Sha256.StateMem.stateAt_eq fun k hk => ?_)
    rw [m2, m1, k1]
    exact pairs_read _ _ iv hk

theorem initPairs_ok (iv : HashValue) :
    ∀ s, (Proof.Sha256.initAArch64 iv).pre s → ∃ t s', Exec isa (initPairs iv) s t s' ∧
      abiPreserved s s' ∧ (Proof.Sha256.initAArch64 iv).post s s' := fun s h => by
  obtain ⟨t, s', he, h⟩ := initPairs_correct iv h
  exact ⟨t, s', he, h⟩

theorem initPairs_writes (iv : HashValue) :
    ∀ r, r ≠ .x9 → r ≠ .x10 → ∀ i ∈ instrs (initPairs iv), clobbers i r = false := by
  intro r h9 h10 i hi
  simp only [initPairs, instrs, List.mem_flatMap, List.mem_range, movImm64, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hi
  obtain ⟨k, -, hi⟩ := hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [clobbers, dstOf, Ne.symm h9, Ne.symm h10]

theorem initPairs_keepsV (iv : HashValue) :
    (initPairs iv).allInstrs VG.AArch64.keepsV = true := by
  rw [Code.allInstrs_eq]
  simp [initPairs, instrs, movImm64, VG.AArch64.keepsV, vdstOf]

end VG.Proof.Sha256.AArch64.Stream

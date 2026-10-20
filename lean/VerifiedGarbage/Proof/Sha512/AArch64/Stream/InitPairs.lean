module
public import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Impl.Sha512.AArch64.Stream
public import VerifiedGarbage.Proof.Sha512.AArch64.Compress

import VerifiedGarbage.Proof.MdStream.AArch64.OneShot
import VerifiedGarbage.Proof.Sha512.Stream
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Contract

/-!
# Streaming SHA-512 on AArch64: `initPairs`

The initial hash value stored by pairs of doublewords, for the one-shot
digests: the same postcondition as `init`'s.
-/

@[expose] public section

namespace VG.Proof.Sha512.AArch64.Stream

open VG VG.AArch64 VG.Impl.Sha512.AArch64.Stream
open VG.Impl.Sha512.AArch64 (movImm64)
open VG.Proof.Sha512.AArch64 (writeState stateAt_writeState contains_offset)
open VG.Spec.Sha512 (HashValue stateAt)

/-- The nine instructions storing the 64-bit words `x` and `y` at `[x0 + off]`. -/
def pair (x y : BitVec 64) (off : Nat) : List Instr :=
  movImm64 .x9 x ++ movImm64 .x10 y ++ ([.stp .x9 .x10 .x0 off] : List Instr)

theorem initPairs_eq (iv : HashValue) : initPairs iv = .block (pair iv[0] iv[1] 0 ++ pair iv[2] iv[3] 16 ++
    pair iv[4] iv[5] 32 ++ pair iv[6] iv[7] 48) := rfl

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

theorem initPairs_correct {s₀ : State} (iv : HashValue) (hp : (Proof.Sha512.initAArch64 iv).pre s₀) :
    WP isa (initPairs iv) s₀ fun s' => abiPreserved s₀ s' ∧ (Proof.Sha512.initAArch64 iv).post s₀ s' := by
  apply WP.withPreservedV (hc := by rfl)
  obtain ⟨-, hwr⟩ := hp
  have o : ∀ j, j + 8 ≤ 64 → InRegions s₀.wr (s₀.gpr .x0 + BitVec.ofNat 64 j) 8 :=
    fun j hj => ⟨⟨s₀.gpr .x0, 192⟩, by simp [hwr], contains_offset (by omega) (by omega)⟩
  rw [initPairs_eq, ← List.append_nil (_ ++ pair iv[6] iv[7] 48)]
  simp only [List.append_assoc]
  refine pair_ok (by decide) (fun j hj => o _ (by omega)) fun s1 g1 _ wr1 sp1 m1 => ?_
  have k1 : s1.gpr .x0 = s₀.gpr .x0 := g1 _ (by decide) (by decide)
  refine pair_ok (by decide) (fun j hj => by rw [wr1, k1]; exact o _ (by omega)) fun s2 g2 _ wr2 sp2 m2 => ?_
  have k2 : s2.gpr .x0 = s₀.gpr .x0 := by rw [g2 _ (by decide) (by decide), k1]
  refine pair_ok (by decide) (fun j hj => by rw [wr2, wr1, k2]; exact o _ (by omega))
    fun s3 g3 _ wr3 sp3 m3 => ?_
  have k3 : s3.gpr .x0 = s₀.gpr .x0 := by rw [g3 _ (by decide) (by decide), k2]
  refine pair_ok (by decide) (fun j hj => by rw [wr3, wr2, wr1, k3]; exact o _ (by omega))
    fun s4 g4 _ _ sp4 m4 => WP.block_nil ?_
  have k4 : ∀ r, r ≠ .x9 → r ≠ .x10 → s4.gpr r = s₀.gpr r := fun r h9 h10 => by
    rw [g4 r h9 h10, g3 r h9 h10, g2 r h9 h10, g1 r h9 h10]
  have hm : s4.mem = writeState s₀.mem (s₀.gpr .x0) iv := by
    rw [m4, m3, m2, m1, k3, k2, k1]
    rfl
  refine ⟨⟨fun r hr => k4 r ?_ ?_, by rw [sp4, sp3, sp2, sp1]⟩, ?_⟩
  · rintro rfl; simp [preserved] at hr
  · rintro rfl; simp [preserved] at hr
  · show Spec.Sha512.Repr iv s4.mem (s₀.gpr .x0) []
    rw [hm]
    exact Proof.Sha512.Stream.repr_nil (stateAt_writeState _ _ _)

theorem initPairs_ok (iv : HashValue) :
    ∀ s, (Proof.Sha512.initAArch64 iv).pre s → ∃ t s', Exec isa (initPairs iv) s t s' ∧
      abiPreserved s s' ∧ (Proof.Sha512.initAArch64 iv).post s s' := fun s h => by
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

end VG.Proof.Sha512.AArch64.Stream

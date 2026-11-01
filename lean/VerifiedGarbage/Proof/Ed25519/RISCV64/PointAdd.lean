module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldProg
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Point
public import VerifiedGarbage.Proof.Ed25519.Point32Contract
import VerifiedGarbage.Proof.Ed25519.RISCV64.Base
import VerifiedGarbage.Proof.Framework.Offset

/-!
# `vg_ed25519_r32_point_add` on RISC-V: correctness

For a working space whose address is a multiple of 8 (`hal`, which the
contract does not state yet), the function runs the complete addition
formula on the slots inline (`fieldCodeW_ok`): the point at `pAt` becomes
the sum of those at `pAt` and `qAt` (`pointAdd_eval`), and it writes only
the sum, the temporaries and the product's limbs (`keeps_add`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Spec.X25519 (P)

theorem elemAt_eq (m : Mem) (b : Addr) (i : Slot) :
    Proof.Ed25519.Point32.elemAt m b (offset i) = env m b i :=
  congrArg (Fin.ofNat P) (read_V m b (offset i))

theorem pointAt_eq (m : Mem) (b : Addr) :
    Proof.Ed25519.Point32.pointAt m b Proof.Ed25519.Point32.pAt = point (env m b) 0 1 2 3 := by
  simp only [Proof.Ed25519.Point32.pointAt, point, ← elemAt_eq]; rfl

theorem pointAt_q (m : Mem) (b : Addr) :
    Proof.Ed25519.Point32.pointAt m b Proof.Ed25519.Point32.qAt = point (env m b) 4 5 6 7 := by
  simp only [Proof.Ed25519.Point32.pointAt, point, ← elemAt_eq]; rfl

/-- A byte of the eight-KiB working space outside a range of it. -/
theorem byte_out8 {b : Addr} {i e k : Nat} (hi : i + 1 ≤ 8192) (he : e + k ≤ 8192) (h : i < e ∨ e + k ≤ i) :
    ¬ (⟨b + BitVec.ofNat 64 e, k⟩ : Region).Contains (b + BitVec.ofNat 64 i) 1 := fun hc =>
  Offset.disjoint b (d := i) (n := 1) (e := e) (k := k) (by omega) (by omega) (by omega) _ (Region.contains_self _ _) hc

/-- What the point addition writes: the sum, the temporaries and the product's limbs. -/
abbrev addW (b : Addr) : List Region :=
  [⟨b + BitVec.ofNat 64 64, 128⟩, ⟨b + BitVec.ofNat 64 320, 256⟩, ⟨b + BitVec.ofNat 64 ACC, 64⟩]

/-- The point addition's `Keeps`, from its frame. -/
theorem keeps_add {b : Addr} {m m' : Mem} (hf : Frame (addW b) m m') : Proof.Ed25519.Point32.Keeps b m m' := by
  intro i hi hp ht ho
  simp only [Proof.Ed25519.Point32.wsBytes, Proof.Ed25519.Point32.pAt, Proof.Ed25519.Point32.elemBytes] at hi hp ht ho
  have hA := eACC_eq
  refine hf _ fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact byte_out8 (by omega) (by omega) hp
  · exact byte_out8 (by omega) (by omega) ht
  · exact byte_out8 (by omega) (by omega) (by omega)

theorem addW_ok (b : Addr) :
    ∀ op ∈ pointAddOps, ∀ r ∈ opFrame b (offset (opOut op)), ∃ r' ∈ addW b, r.Sub r' := by
  have h : ∀ op ∈ pointAddOps, (opOut op).val < 4 ∨ (8 ≤ (opOut op).val ∧ (opOut op).val < 16) := by
    decide
  intro op hop r hr
  have ho := h op hop
  have hA := eACC_eq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rcases ho with ho | ho
    · exact ⟨_, List.mem_cons_self, Offset.sub _ (by simp only [offset]; omega) (by simp only [offset]; omega)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self,
        Offset.sub _ (by simp only [offset]; omega) (by simp only [offset]; omega)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), Offset.sub _ (Nat.le_refl _)
      (Nat.le_refl _)⟩

theorem addFn_ok {s : State} (hwr : s.wr = [⟨s.gpr .a0, 8192⟩]) (hal : (s.gpr .a0).toNat % 8 = 0)
    (hd : Proof.Ed25519.Point32.elemAt s.mem (s.gpr .a0) Proof.Ed25519.Point32.dAt = Spec.Ed25519.d) :
    WP isa addFn s fun t =>
      Proof.Ed25519.Point32.pointAt t.mem (s.gpr .a0) Proof.Ed25519.Point32.pAt =
        Spec.Ed25519.pointAdd (Proof.Ed25519.Point32.pointAt s.mem (s.gpr .a0) Proof.Ed25519.Point32.pAt)
          (Proof.Ed25519.Point32.pointAt s.mem (s.gpr .a0) Proof.Ed25519.Point32.qAt) ∧
      Proof.Ed25519.Point32.Keeps (s.gpr .a0) s.mem t.mem := by
  have hin : (⟨s.gpr .a0, 8192⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  refine WP.seq (wp_mv fun s1 u1 => WP.block_nil ?_)
  have hc1 : Ctx (s.gpr .a0) s1 :=
    ⟨u1.gpr, hal, fun d n hd => by rw [u1.wr]; exact in_base hin (by omega) (by omega)⟩
  refine WP.mono (fieldCodeW_ok pointAddOps (by decide) _ (addW_ok _) hc1) fun t ⟨_, hf, he⟩ => ?_
  rw [u1.mem] at hf he
  refine ⟨?_, keeps_add hf⟩
  rw [pointAt_eq, pointAt_eq, pointAt_q, he]
  exact pointAdd_eval _ (by rw [← elemAt_eq]; exact hd)

end VG.Proof.Ed25519.RISCV64

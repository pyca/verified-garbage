module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.ReduceAt
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PreparedReductionAllocated
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FactorGeometry
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Subspace
public import VerifiedGarbage.Proof.Mont.X86.OutsZ
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-! Reduce staged modulus candidates in the arithmetic subspace and restore its parent pointer. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (num arr S)

theorem reduce_at {s : State} {base : Addr} {bytes n x q : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes)
    (room : CallRoom (s.gpr .esp) base bytes) (stack : StkOk (s.gpr .esp - 16#32) base bytes)
    (lower : 4 ≤ n) (upper : n ≤ 48)
    (candidate : num s.mem (off base Layout.arithmetic) (2 * n) 0 = x)
    (subgroup : num s.mem (off base Layout.arithmetic) (2 * n) 2 = q)
    (positive : 0 < q) (bound : 2 * q < 2 ^ (64 * n)) :
    WP isa (reduceAt n) s fun t =>
      num t.mem (off base Layout.arithmetic) (2 * n) 5 = x + 1 - x % (2 * q) ∧
      num t.mem (off base Layout.arithmetic) (2 * n) 0 = 2 * (x / (2 * q)) ∧
      Frame [⟨off base Layout.arithmetic, Layout.arithmeticBytes⟩, below (s.gpr .esp) 16] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have geometry := factor_geometry lower upper
  have arraysFit : arr (kw (8 * n)) 6 ≤ Layout.arithmeticBytes := by
    rw [factor_width]
    simp only [arr, S, VG.Impl.Rsa.X86.Keys.hdr, Layout.arithmeticBytes]
    omega
  have fit : Layout.arithmetic + Layout.arithmeticBytes ≤ bytes := capacity
  have offsetLt : Layout.arithmetic < bytes := by unfold Layout.arithmetic; omega
  unfold reduceAt enterArithmetic
  refine WP.seq (wp_addS rfl fun a A _ => wp_movS rfl fun b B _ => WP.block_nil ?_)
  have bsp : b.gpr .esp = s.gpr .esp := (B.other .esp (by decide)).trans (A.other .esp (by decide))
  have bdi : b.gpr .edi = s.gpr .edi + BitVec.ofNat 32 Layout.arithmetic := by
    rw [B.other .edi (by decide), A.gpr]
  have mem : b.mem = s.mem := B.mem.trans A.mem
  have write : Covers [⟨off base Layout.arithmetic, Layout.arithmeticBytes⟩] b.wr := by
    rw [B.wr, A.wr]
    exact workspace_slice_covers scr fit
  have child : Scr (b.withRegions b.rd [⟨off base Layout.arithmetic, Layout.arithmeticBytes⟩])
      (off base Layout.arithmetic) Layout.arithmeticBytes :=
    workspace_slice scr fit offsetLt bdi bsp (List.mem_singleton_self _)
  have childWs : VG.Proof.Rsa.X86.Keys.Ws
      (b.withRegions b.rd [⟨off base Layout.arithmetic, Layout.arithmeticBytes⟩])
      (off base Layout.arithmetic) Layout.arithmeticBytes (kw (8 * n)) 6 :=
    ⟨child, arraysFit, geometry.2.1, geometry.2.2.1⟩
  have baseOffset : (off base Layout.arithmetic).toNat = base.toNat + Layout.arithmetic := by
    have nowrap := scr.nowrap
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by decide : Layout.arithmetic < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  have childStack : StkOk
      ((allocFrame 16 (b.withRegions b.rd [⟨off base Layout.arithmetic, Layout.arithmeticBytes⟩])).gpr .esp)
      (off base Layout.arithmetic) Layout.arithmeticBytes := by
    rw [allocFrame_esp, State.withRegions_gpr, bsp]
    simp only [StkOk] at stack ⊢
    rw [baseOffset]
    omega
  have childApart : Region.Disjoint (below (s.gpr .esp) 16)
      ⟨off base Layout.arithmetic, Layout.arithmeticBytes⟩ :=
    (room.apart.sub_left (below_sub (by decide) room.low)).sub_right (Offset.sub_base base fit)
  have work := prepared_reduction_allocated (x := x) (q := q) childWs (by decide) geometry.1 B.gpr
    (by rw [State.withRegions_gpr, bsp]; have := room.low; omega) childStack
    (by change Region.Disjoint (below (b.gpr .esp) 16) _; rw [bsp]; exact childApart)
    (by rw [State.withRegions_mem, factor_width, mem]; exact candidate)
    (by rw [State.withRegions_mem, factor_width, mem]; exact subgroup) positive
    (by rw [factor_width, show 32 * (2 * n) = 64 * n by omega]; exact bound)
  rw [factor_width] at work
  refine WP.seq (WP.mono (workspace_wp work (Covers.append (Covers.refl _) write) write)
    fun v ⟨u, ⟨p, e, F, K⟩, eq⟩ => ?_)
  subst eq
  unfold leaveArithmetic
  refine wp_subS rfl fun t T _ => WP.block_nil ?_
  have restored : t.gpr .edi = s.gpr .edi := by
    rw [T.gpr, State.withRegions_gpr, K.1 .edi (by decide), State.withRegions_gpr, bdi, BitVec.add_sub_cancel]
  refine ⟨by rw [T.mem]; exact p, by rw [T.mem]; exact e, ?_, ?_⟩
  · rw [T.mem, ← mem]
    rw [State.withRegions_gpr, bsp] at F
    exact F
  · refine ⟨?_, ?_, ?_⟩
    · intro r hr
      have only : r = .edi ∨ r = .esp := by cases r <;> simp_all
      rcases only with rfl | rfl
      · exact restored
      · rw [T.other .esp (by decide), State.withRegions_gpr, K.1 .esp (by decide), State.withRegions_gpr, bsp]
    · rw [T.rd, State.withRegions_rd, B.rd, A.rd]
    · rw [T.wr, State.withRegions_wr, B.wr, A.wr]

end VG.Proof.Dsa.X86.Generation

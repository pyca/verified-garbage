module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrimePreparation
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FactorCandidate
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FactorGeometry
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Subspace
public import VerifiedGarbage.Proof.Mont.X86.OutsZ
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-! Factor a candidate in the arithmetic subspace and restore the parent pointer. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt

theorem factor_at {s : State} {base : Addr} {bytes n candidate : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes)
    (room : CallRoom (s.gpr .esp) base bytes)
    (stack : StkOk (s.gpr .esp - BitVec.ofNat 32 16) base bytes)
    (lower : 4 ≤ n) (upper : n ≤ 48)
    (current : val32 s.mem (off base Layout.arithmetic) 160 (2 * n) = candidate)
    (large : 3 ≤ candidate) (odd : candidate % 2 = 1) :
    WP isa (factorCandidate n) s fun t =>
      val32 t.mem (off base Layout.arithmetic) 160 (2 * n) = Spec.MillerRabin.exponent candidate ∧
      (word t.mem (off base Layout.arithmetic) 64).toNat = 2 ^ (VG.Proof.RsaKeyGen.mrA candidate % 64) ∧
      Frame [⟨off base Layout.arithmetic, Layout.arithmeticBytes⟩, below (s.gpr .esp) 16] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have geometry := factor_geometry lower upper
  have fit : Layout.arithmetic + Layout.arithmeticBytes ≤ bytes := capacity
  have offsetLt : Layout.arithmetic < bytes := by unfold Layout.arithmetic; omega
  unfold factorCandidate enterArithmetic
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
      (off base Layout.arithmetic) Layout.arithmeticBytes (kw (8 * n)) 3 :=
    ⟨child, geometry.2.2.2.2, geometry.2.1, geometry.2.2.1⟩
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
  have work := factor_candidate childWs (by decide) geometry.1 B.gpr (by
      change 16 ≤ (b.gpr .esp).toNat; rw [bsp]; have := room.low; omega)
    childStack (by change Region.Disjoint (below (b.gpr .esp) 16) _; rw [bsp]; exact childApart)
    (by
      simp only [VG.Proof.Rsa.X86.Keys.num, VG.Proof.Rsa.X86.Keys.arr, VG.Impl.Rsa.X86.Keys.hdr,
        Nat.zero_mul, Nat.add_zero, State.withRegions_mem]
      rw [factor_width, mem]; exact current) large odd geometry.2.2.2.1
  refine WP.seq (WP.mono (workspace_wp work (Covers.append (Covers.refl _) write) write)
    fun v ⟨u, ⟨exponent, _, power, F, K⟩, eq⟩ => ?_)
  subst eq
  unfold leaveArithmetic
  refine wp_subS rfl fun t T _ => WP.block_nil ?_
  have memory : t.mem = u.mem := T.mem
  have restored : t.gpr .edi = s.gpr .edi := by
    rw [T.gpr, State.withRegions_gpr, K.1 .edi (by decide), State.withRegions_gpr, bdi,
      BitVec.add_sub_cancel]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [memory]
    simpa only [VG.Proof.Rsa.X86.Keys.num, VG.Proof.Rsa.X86.Keys.arr,
      VG.Impl.Rsa.X86.Keys.hdr, Nat.zero_mul, Nat.add_zero, factor_width] using exponent
  · rw [memory]; exact power
  · rw [memory, ← mem]
    rw [State.withRegions_gpr, bsp] at F
    exact F
  · refine ⟨?_, ?_, ?_⟩
    · intro r hr
      by_cases di : r = .edi
      · subst di; exact restored
      · rw [T.other r di, State.withRegions_gpr, K.1 r (by
          revert hr; cases r <;> simp),
          State.withRegions_gpr, B.other r (by intro h; subst h; simp at hr), A.other r di]
    · rw [T.rd, State.withRegions_rd, B.rd, A.rd]
    · rw [T.wr, State.withRegions_wr, B.wr, A.wr]

end VG.Proof.Dsa.X86.Generation

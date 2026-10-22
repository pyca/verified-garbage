module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.PreparedReduction
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ArithmeticNumber
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ArithmeticPermissions

/-! Run shared candidate reduction through the existing runtime arithmetic argument frame. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (Ws num)

theorem prepared_reduction_noSp (words : Nat) : NoSp (preparedReduction words) :=
  NoSp.of_all (by rfl)

theorem prepared_reduction_allocated {s : State} {base : Addr} {bytes len count x q : Nat}
    (ws : Ws s base bytes (kw len) count) (arrays : 6 ≤ count)
    (length : len ≤ 1024) (lengthReg : s.gpr .esi = BitVec.ofNat 32 len)
    (low : 16 ≤ (s.gpr .esp).toNat)
    (stack : StkOk ((allocFrame 16 s).gpr .esp) base bytes)
    (apart : Region.Disjoint (below (s.gpr .esp) 16) ⟨base, bytes⟩)
    (candidate : num s.mem base (kw len) 0 = x) (subgroup : num s.mem base (kw len) 2 = q)
    (positive : 0 < q) (bound : 2 * q < 2 ^ (32 * kw len)) :
    WP isa (withArithmetic (preparedReduction (kw len))) s fun t =>
      num t.mem base (kw len) 5 = x + 1 - x % (2 * q) ∧
      num t.mem base (kw len) 0 = 2 * (x / (2 * q)) ∧
      Frame [⟨base, bytes⟩, below (s.gpr .esp) 16] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  apply with_arithmetic low (prepared_reduction_noSp _)
  intro t H
  obtain ⟨ready, value⟩ := H.ready ws length lengthReg low stack apart (by omega) candidate
  have qValue := (H.num_keep ws apart (by omega : 2 < count)).trans subgroup
  have physicalWrite : (⟨base, bytes⟩ : Region) ∈ t.wr := by
    rw [H.keeps.2.2, allocFrame_wr]
    exact List.mem_cons_of_mem _ ws.workspace.wr
  have permissions := H.permissions physicalWrite
  refine WP.mono (workspace_wp (prepared_reduction ready arrays positive value qValue bound)
    permissions.1 permissions.2) fun v ⟨u, ⟨_, p, e, F, K⟩, eq⟩ => ?_
  subst eq
  refine ⟨p, e, ?_, ?_⟩
  · exact (H.frame.mono (by simp)).trans (F.mono (by simp))
  · refine ⟨?_, ?_, ?_⟩
    · intro r hr
      by_cases sp : r = .esp
      · subst sp
        rw [freed_esp, State.withRegions_gpr, K.1 .esp (by decide), State.withRegions_gpr,
          H.keeps.1 .esp (by decide), allocFrame_esp, BitVec.sub_add_cancel]
      · rw [freed_gpr _ _ sp, State.withRegions_gpr, K.1 r hr, State.withRegions_gpr,
          H.keeps.1 r (by revert hr; cases r <;> simp), allocFrame_gpr _ _ sp]
    · rw [freed_rd, State.withRegions_rd, H.keeps.2.1, allocFrame_rd]
    · rw [freed_wr, State.withRegions_wr, H.keeps.2.2, allocFrame_wr]
      rfl

end VG.Proof.Dsa.X86.Generation

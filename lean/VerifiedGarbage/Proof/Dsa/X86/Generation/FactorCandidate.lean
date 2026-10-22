module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.ArithmeticAllocated
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ArithmeticPermissions
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ArithmeticNoSp
public import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateExponent
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Mont.OutsFrame

/-! The complete argument-frame wrapper for candidate factorization. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (Ws num)

theorem factor_candidate {s : State} {base : Addr} {bytes len count candidate : Nat}
    (ws : Ws s base bytes (kw len) count) (arrays : 3 ≤ count)
    (length : len ≤ 1024) (lengthReg : s.gpr .esi = BitVec.ofNat 32 len)
    (low : 16 ≤ (s.gpr .esp).toNat)
    (stack : StkOk ((allocFrame 16 s).gpr .esp) base bytes)
    (apart : Region.Disjoint (below (s.gpr .esp) 16) ⟨base, bytes⟩)
    (current : num s.mem base (kw len) 0 = candidate) (large : 3 ≤ candidate)
    (odd : candidate % 2 = 1) (bits : 32 * kw len ≤ 16384) :
    WP isa (withArithmetic (prepareCandidateExponent arithmeticLay)) s fun t =>
      num t.mem base (kw len) 0 = Spec.MillerRabin.exponent candidate ∧
      num t.mem base (kw len) 2 = candidate ∧
      (word t.mem base 64).toNat = 2 ^ (VG.Proof.RsaKeyGen.mrA candidate % 64) ∧
      Frame [⟨base, bytes⟩, below (s.gpr .esp) 16] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  apply with_arithmetic low candidate_exponent_noSp
  intro t H
  obtain ⟨ready, value⟩ := H.ready ws length lengthReg low stack apart (by omega) current
  have physicalWrite : (⟨base, bytes⟩ : Region) ∈ t.wr := by
    rw [H.keeps.2.2, allocFrame_wr]
    exact List.mem_cons_of_mem _ ws.workspace.wr
  have permissions := H.permissions physicalWrite
  refine WP.mono (workspace_wp (prepare_candidate_exponent ready arrays value large odd bits)
    permissions.1 permissions.2) fun v ⟨u, ⟨_, F, exponent, modulus, power, K⟩, eq⟩ => ?_
  subst eq
  have out : Outside base 0 bytes t.mem u.mem := keep_outside ready.ws F
    (by intro j hj; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl <;> omega) (by simp [VG.Impl.Rsa.X86.Keys.hdr])
  have frame : Frame [⟨base, bytes⟩] t.mem u.mem :=
    (Outs.of_outside out (List.mem_singleton_self _)).frame (by
      intro r hr; rw [List.mem_singleton.mp hr]; omega)
  refine ⟨exponent, modulus, power, ?_, ?_⟩
  · exact (H.frame.sub (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨_, by simp, fun _ h => h⟩)).trans (frame.sub (fun r hr => by
        rw [List.mem_singleton.mp hr]
        exact ⟨_, by simp, fun _ h => h⟩))
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

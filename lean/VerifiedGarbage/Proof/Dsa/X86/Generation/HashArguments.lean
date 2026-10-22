module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashRegisters

/-! # Existing SHA call contracts instantiated by the seed-hash wrapper -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86

namespace HashGeometry

theorem init_args {H : Hash} {ok : HashOK H} {st data digest scratch : BitVec 32} {len : Nat} {s : State}
    (G : HashGeometry ok st data digest scratch len s) (R : HashRegisters st data scratch len s) :
    InitArgs (H := H) s .ebx st := by
  refine ⟨R.state, by decide, G.sp48, ?_, G.stack_st, G.st_fit⟩
  apply (Covers.of_mem ?_).trans G.writable
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact List.mem_cons_self

theorem update_args {H : Hash} {ok : HashOK H} {st data digest scratch : BitVec 32} {len : Nat} {s : State}
    (G : HashGeometry ok st data digest scratch len s) (R : HashRegisters st data scratch len s)
    (eax : s.gpr .eax = 0) (ecx : s.gpr .ecx = BitVec.ofNat 32 len) (edx : s.gpr .edx = data) :
    UpdArgs ok s .eax .ebx st data scratch 0 len := by
  refine ⟨R.state, eax, eax, ecx, edx, R.scratch, by decide, by decide, G.small, G.sp48,
    G.readable, ?_, G.st_scratch, G.data_st, G.data_scratch, G.stack_st, G.stack_data,
    G.stack_scratch, G.st_fit, G.data_fit, G.scratch_fit⟩
  apply (Covers.of_mem ?_).trans G.writable
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

theorem finish_args {H : Hash} {ok : HashOK H} {st data digest scratch : BitVec 32} {len : Nat} {s : State}
    (G : HashGeometry ok st data digest scratch len s) (R : HashRegisters st data scratch len s)
    (eax : s.gpr .eax = BitVec.ofNat 32 len) (ecx : s.gpr .ecx = 0) (edx : s.gpr .edx = digest) :
    FinArgs ok s .ebx st digest scratch (BitVec.ofNat 32 len) 0 :=
  ⟨R.state, eax, ecx, edx, R.scratch, by decide, G.sp48, G.writable, G.st_digest, G.st_scratch,
    G.digest_scratch, G.stack_st, G.stack_digest, G.stack_scratch, G.st_fit, G.digest_fit, G.scratch_fit⟩

end HashGeometry
end VG.Proof.Dsa.X86.Generation

module

import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Lit
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Lit

public import VerifiedGarbage.Proof.MlKem.X86_64.KgNtt
import VerifiedGarbage.Proof.MlKem.X86_64.KpkeEncV
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.X86_64.KgNtt
meta import VerifiedGarbage.Proof.MlKem.X86_64.KpkeKgV
meta import VerifiedGarbage.Proof.MlKem.X86_64.DecMulV
meta import VerifiedGarbage.Proof.MlKem.X86_64.KpkeEncV
meta import VerifiedGarbage.Proof.MlKem.X86_64.Contracts
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on x86-64: `vg_mlkem768_kpke_keygen_ntt`, verified

The proof of `KgNtt.lean` with AVX2, its constant time (every address is
the entry's pointers plus constants), and its contract implying the shared
one of `Proof/MlKem/KpkeKgRowsContract.lean`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

theorem kgNtt768_ct :
    ConstantTime isa (kgNttK 3).pre (kgNttK 3).pub (KpkeKgRows.kgNtt kem768 .avx2) :=
  RelCT.constantTime (Q := fun _ _ => True) (RelCT.mono
    (RelCT.taintRegs (τ := X86_64.Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp])
      (fun x y h => X86_64.Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        exacts [h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2])
      [] (by taint_decide)) (fun _ _ h => h) fun _ _ _ => trivial)

theorem kgNtt768_correct : ∀ s, (kgNttK 3).pre s →
    ∃ t s', Exec isa (KpkeKgRows.kgNtt kem768 .avx2) s t s' ∧ abiPreserved s s' ∧ (kgNttK 3).post s s' := by
  intro s hp
  obtain ⟨t, s', he, hg, hq⟩ := KgNtt.kgNtt_wp PrimsOk.avx2 (by lit_decide) (L := kem768) (.inl rfl)
    (by lit_decide) hp
  exact ⟨t, s', he, abiPreserved_of_ctl (by lit_decide) he hg, hq⟩

end VG.Proof.MlKem.X86_64

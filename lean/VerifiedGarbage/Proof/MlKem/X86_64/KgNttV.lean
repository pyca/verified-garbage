module

import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Lit
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Lit

public import VerifiedGarbage.Proof.MlKem.X86_64.KgNtt
public import VerifiedGarbage.Proof.MlKem.KpkeKgRowsContract
import VerifiedGarbage.Proof.MlKem.X86_64.KpkeEncV
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.X86_64.KgNtt
meta import VerifiedGarbage.Proof.MlKem.KpkeKgRowsContract
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

/-- A state the contract permits. -/
def kgNttSat (k : Nat) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x4000 | .rcx => 0x8000 | .r8 => 0x10000 | .rsp => 0x20000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x8000, 1024 * k⟩]
  wr := [⟨0x1000, 384 * k⟩, ⟨0x2000, 1024 * k⟩, ⟨0x4000, 1024 * k⟩, ⟨0x10000, 4096⟩]

theorem kgNtt768_verified :
    Verified X86_64.target (KpkeKgRows.kgNtt kem768 .avx2) (Proof.MlKem.kpkeKeyGenNttContract 3 X86_64.abi) :=
  Verified.of_correct kgNtt768_correct kgNtt768_ct
    { pre := by sig_implies_pre [kpkeKeyGenNttContract, kpkeKeyGenNttSig, kgNttK, X86_64.abi,
        X86_64.argRegs, retR]
      post := by sig_implies_post [kpkeKeyGenNttContract, kpkeKeyGenNttSig, kgNttK, X86_64.abi,
        X86_64.argRegs, retR]
      pub := by sig_implies_pub [kpkeKeyGenNttContract, kpkeKeyGenNttSig, kgNttK, X86_64.abi,
        X86_64.argRegs, retR]
      sat := by
        refine ⟨kgNttSat 3, ?_⟩
        sig_pre [kpkeKeyGenNttContract, kpkeKeyGenNttSig, kgNttK, X86_64.abi, X86_64.argRegs]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          vecReducedW16_zero _ _⟩
        all_goals first
          | exact Region.disjoint_of_sep (by decide)
          | decide }

end VG.Proof.MlKem.X86_64

module

public import VerifiedGarbage.Proof.MlKem.X86_64.KgRow
public import VerifiedGarbage.Proof.MlKem.KpkeKgRowsContract
import VerifiedGarbage.Proof.MlKem.X86_64.DecMulV
import VerifiedGarbage.Proof.MlKem.X86_64.KpkeEncV
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.X86_64.KgRow
meta import VerifiedGarbage.Proof.MlKem.KpkeKgRowsContract
meta import VerifiedGarbage.Proof.MlKem.X86_64.KpkeKgV
meta import VerifiedGarbage.Proof.MlKem.X86_64.DecMulV
meta import VerifiedGarbage.Proof.MlKem.X86_64.KpkeEncV
meta import VerifiedGarbage.Proof.MlKem.X86_64.Contracts
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on x86-64: `vg_mlkem768_kpke_keygen_row`, verified

The proof of `KgRow.lean` with AVX2, its constant time (every address is
the entry's pointers plus constants), and its contract implying the shared
one of `Proof/MlKem/KpkeKgRowsContract.lean`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

theorem kgRow768_ct :
    ConstantTime isa (kgRowK 3).pre (kgRowK 3).pub (KpkeKgRows.kgRow kem768 .avx2) :=
  RelCT.constantTime (Q := fun _ _ => True) (RelCT.mono
    (RelCT.taintRegs (τ := X86_64.Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp])
      (fun x y h => X86_64.Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        exacts [h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2])
      [] (by taint_decide)) (fun _ _ h => h) fun _ _ _ => trivial)

theorem kgRow768_correct : ∀ s, (kgRowK 3).pre s →
    ∃ t s', Exec isa (KpkeKgRows.kgRow kem768 .avx2) s t s' ∧ abiPreserved s s' ∧ (kgRowK 3).post s s' := by
  intro s hp
  obtain ⟨t, s', he, hg, hq⟩ := KgRow.kgRow_wp PrimsOk.avx2 (by lit_decide) (L := kem768) (.inl rfl)
    (by decide +kernel) hp
  exact ⟨t, s', he, abiPreserved_of_ctl (by lit_decide) he hg, hq⟩

/-- A state the contract permits. -/
def kgRowSat (k : Nat) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x4000 | .rcx => 0x8000 | .r8 => 0x10000 | .rsp => 0x20000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 512 * k⟩, ⟨0x4000, 1024 * k⟩]
  wr := [⟨0x1000, 384⟩, ⟨0x8000, 1024⟩, ⟨0x10000, 4096⟩]

theorem kgRow768_verified :
    Verified X86_64.target (KpkeKgRows.kgRow kem768 .avx2) (Proof.MlKem.kpkeKeyGenRowContract 3 X86_64.abi) :=
  Verified.of_correct kgRow768_correct kgRow768_ct
    { pre := by sig_implies_pre [kpkeKeyGenRowContract, kpkeKeyGenRowSig, kgRowK, X86_64.abi,
        X86_64.argRegs, retR]
      post := by sig_implies_post [kpkeKeyGenRowContract, kpkeKeyGenRowSig, kgRowK, X86_64.abi,
        X86_64.argRegs, retR]
      pub := by sig_implies_pub [kpkeKeyGenRowContract, kpkeKeyGenRowSig, kgRowK, X86_64.abi,
        X86_64.argRegs, retR]
      sat := by
        refine ⟨kgRowSat 3, ?_⟩
        sig_pre [kpkeKeyGenRowContract, kpkeKeyGenRowSig, kgRowK, X86_64.abi, X86_64.argRegs]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          vecReducedW16_zero _ _, vecReduced_zero _ _, reduced_zero _⟩
        all_goals first
          | exact Region.disjoint_of_sep (by decide)
          | decide }

end VG.Proof.MlKem.X86_64

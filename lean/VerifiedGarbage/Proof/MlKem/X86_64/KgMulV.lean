module

public import VerifiedGarbage.Proof.MlKem.X86_64.KgMul
meta import VerifiedGarbage.Proof.MlKem.X86_64.KgMul
import VerifiedGarbage.Proof.MlKem.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
meta import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
meta import VerifiedGarbage.Proof.MlKem.X86_64.Lit
import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
meta import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
import VerifiedGarbage.Proof.MlKem.X86_64.DecMulV
meta import VerifiedGarbage.Proof.MlKem.X86_64.DecMulV
import VerifiedGarbage.Impl.MlKem.X86_64.Frag
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.MlKem.PolyW
import VerifiedGarbage.Proof.MlKem.X86_64.AccInvY
import VerifiedGarbage.Proof.MlKem.X86_64.EncMulV
import VerifiedGarbage.Proof.MlKem.X86_64.KpkeBodiesY
import VerifiedGarbage.Proof.MlKem.X86_64.NttInv
import VerifiedGarbage.Proof.MlKem.X86_64.RowY
import VerifiedGarbage.Proof.MlKem.X86_64.VLay42
import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
import VerifiedGarbage.Proof.MlKem.X86_64.VPack
import VerifiedGarbage.Proof.MlKem.X86_64.YAddSub
import VerifiedGarbage.Proof.MlKem.X86_64.YNttLay42
import VerifiedGarbage.Proof.MlKem.X86_64.YNttPack
meta import VerifiedGarbage.Impl.MlKem.X86_64.Frag
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.X86_64.Words
meta import VerifiedGarbage.Proof.MlKem.PolyW
meta import VerifiedGarbage.Proof.MlKem.X86_64.AccInvY
meta import VerifiedGarbage.Proof.MlKem.X86_64.EncMulV
meta import VerifiedGarbage.Proof.MlKem.X86_64.FinY
meta import VerifiedGarbage.Proof.MlKem.X86_64.KpkeBodiesY
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttInv
meta import VerifiedGarbage.Proof.MlKem.X86_64.VLay42
meta import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
meta import VerifiedGarbage.Proof.MlKem.X86_64.VPack
meta import VerifiedGarbage.Proof.MlKem.X86_64.YAddSub
meta import VerifiedGarbage.Proof.MlKem.X86_64.YNttLay42
meta import VerifiedGarbage.Proof.MlKem.X86_64.YNttPack

/-!
# ML-KEM on x86-64: `vg_mlkem768_keygen_mul` and `vg_mlkem1024_keygen_mul`, verified

The proof of `KgMul.lean` for each backend and rank, its constant time,
and its contract implying the shared one of `Proof/MlKem/KpkeMulContract.lean`.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

theorem kgMul_correct {B : Bodies} {R : AccRep} {T : TabRep} (hB : BodiesOk B R T) (hrow : KgMul.RowOk B R T) {k : Nat}
    (hk : k ≤ 4) (hk0 : 0 < k)
    (hwo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14, .r15, .rbp]
      (KgMul.inner B k) = true)
    (hctl : ctlOk (keygenMul B k) = true) (s : State) (hs : (kgMulK k).pre s) :
    ∃ t s', Exec isa (keygenMul B k) s t s' ∧ abiPreserved s s' ∧ (kgMulK k).post s s' := by
  obtain ⟨t, s', he, hg, hpost⟩ := KgMul.wp_all hs hk hB hk0 hrow hwo
  exact ⟨t, s', he, abiPreserved_of_ctl hctl he hg, hpost⟩

theorem kgMul_agree {k : Nat} (s₁ s₂ : State) (_ : (kgMulK k).pre s₁) (_ : (kgMulK k).pre s₂)
    (hp : (kgMulK k).pub s₁ s₂) :
    X86_64.Taint.Agree (X86_64.Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) s₁ s₂ :=
  X86_64.Taint.agree_ofRegs fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2]

/-- A state satisfying the precondition, for `k ≤ 4`. -/
def kgMulSat (k : Nat) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x8000 | .rdx => 0x10000 | .rcx => 0x20000 | .r8 => 0x30000
    | .rsp => 0x40000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x10000, 1024 * (k * k)⟩, ⟨0x20000, 1024 * k⟩]
  wr := [⟨0x1000, 1024 * k⟩, ⟨0x8000, 1024 * k⟩, ⟨0x30000, 4096⟩]

section
variable (B : Bodies)

theorem kgMul3_verified {R : AccRep} {T : TabRep} (hB : BodiesOk B R T) (hrow : KgMul.RowOk B R T)
    (hwo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14, .r15, .rbp]
      (KgMul.inner B 3) = true)
    (hctl : ctlOk (keygenMul B 3) = true)
    (hct : ConstantTime isa (kgMulK 3).pre (kgMulK 3).pub (keygenMul B 3)) :
    Verified X86_64.target (keygenMul B 3) (Proof.MlKem.keygenMulContract 3 X86_64.abi) :=
  Verified.of_correct (kgMul_correct hB hrow (by decide) (by decide) hwo hctl) hct
    { pre := by sig_implies_pre [Proof.MlKem.keygenMulContract, Proof.MlKem.keygenMulSig, kgMulK, X86_64.abi,
        X86_64.argRegs]
      post := by sig_implies_post [Proof.MlKem.keygenMulContract, Proof.MlKem.keygenMulSig, kgMulK, X86_64.abi,
        X86_64.argRegs]
      pub := by sig_implies_pub [Proof.MlKem.keygenMulContract, Proof.MlKem.keygenMulSig, kgMulK, X86_64.abi,
        X86_64.argRegs]
      sat := by
        refine ⟨kgMulSat 3, ?_⟩
        sig_pre [Proof.MlKem.keygenMulContract, Proof.MlKem.keygenMulSig, kgMulK, X86_64.abi, X86_64.argRegs]
        and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | exact vecReduced_zero _ _
          | (intro a h₁ h₂
             simp only [Region.Contains] at h₁ h₂
             bv_omega) }

theorem kgMul4_verified {R : AccRep} {T : TabRep} (hB : BodiesOk B R T) (hrow : KgMul.RowOk B R T)
    (hwo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14, .r15, .rbp]
      (KgMul.inner B 4) = true)
    (hctl : ctlOk (keygenMul B 4) = true)
    (hct : ConstantTime isa (kgMulK 4).pre (kgMulK 4).pub (keygenMul B 4)) :
    Verified X86_64.target (keygenMul B 4) (Proof.MlKem.keygenMulContract 4 X86_64.abi) :=
  Verified.of_correct (kgMul_correct hB hrow (by decide) (by decide) hwo hctl) hct
    { pre := by sig_implies_pre [Proof.MlKem.keygenMulContract, Proof.MlKem.keygenMulSig, kgMulK, X86_64.abi,
        X86_64.argRegs]
      post := by sig_implies_post [Proof.MlKem.keygenMulContract, Proof.MlKem.keygenMulSig, kgMulK, X86_64.abi,
        X86_64.argRegs]
      pub := by sig_implies_pub [Proof.MlKem.keygenMulContract, Proof.MlKem.keygenMulSig, kgMulK, X86_64.abi,
        X86_64.argRegs]
      sat := by
        refine ⟨kgMulSat 4, ?_⟩
        sig_pre [Proof.MlKem.keygenMulContract, Proof.MlKem.keygenMulSig, kgMulK, X86_64.abi, X86_64.argRegs]
        and_intros
        all_goals first
          | rfl
          | decide
          | exact Region.disjoint_of_sep (by decide)
          | exact vecReduced_zero _ _
          | (intro a h₁ h₂
             simp only [Region.Contains] at h₁ h₂
             bv_omega) }

end

/-! The facts about the code, each checked once (on the literals of `Lit.lean`). -/

theorem kgMulSse3_wo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14, .r15, .rbp]
    (KgMul.inner .sse 3) = true :=
  writesOnly_of (by lit_decide)

theorem kgMulSse3_ctl : ctlOk (keygenMul .sse 3) = true := by lit_decide

theorem kgMulSse4_wo : writesOnly [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r12, .r13, .r14, .r15, .rbp]
    (KgMul.inner .sse 4) = true :=
  writesOnly_of (by lit_decide)

theorem kgMulSse4_ctl : ctlOk (keygenMul .sse 4) = true := by lit_decide

theorem kgMulSse3_ct : ConstantTime isa (kgMulK 3).pre (kgMulK 3).pub (keygenMul .sse 3) :=
  VG.Taint.constantTime (A := taint) _ kgMul_agree (by taint_decide)

theorem kgMulSse3_correct : ∀ s, (kgMulK 3).pre s →
    ∃ t s', Exec isa (keygenMul .sse 3) s t s' ∧ abiPreserved s s' ∧ (kgMulK 3).post s s' :=
  kgMul_correct BodiesOk.sse (KgMul.RowOk.ofAcc BodiesOk.sse rfl) (by decide) (by decide) kgMulSse3_wo kgMulSse3_ctl

theorem kgMulSse3_verified :
    Verified X86_64.target (keygenMul .sse 3) (Proof.MlKem.keygenMulContract 3 X86_64.abi) :=
  kgMul3_verified _ BodiesOk.sse (KgMul.RowOk.ofAcc BodiesOk.sse rfl) kgMulSse3_wo kgMulSse3_ctl kgMulSse3_ct

theorem kgMulSse4_ct : ConstantTime isa (kgMulK 4).pre (kgMulK 4).pub (keygenMul .sse 4) :=
  VG.Taint.constantTime (A := taint) _ kgMul_agree (by taint_decide)

theorem kgMulSse4_correct : ∀ s, (kgMulK 4).pre s →
    ∃ t s', Exec isa (keygenMul .sse 4) s t s' ∧ abiPreserved s s' ∧ (kgMulK 4).post s s' :=
  kgMul_correct BodiesOk.sse (KgMul.RowOk.ofAcc BodiesOk.sse rfl) (by decide) (by decide) kgMulSse4_wo kgMulSse4_ctl

theorem kgMulSse4_verified :
    Verified X86_64.target (keygenMul .sse 4) (Proof.MlKem.keygenMulContract 4 X86_64.abi) :=
  kgMul4_verified _ BodiesOk.sse (KgMul.RowOk.ofAcc BodiesOk.sse rfl) kgMulSse4_wo kgMulSse4_ctl kgMulSse4_ct

end VG.Proof.MlKem.X86_64

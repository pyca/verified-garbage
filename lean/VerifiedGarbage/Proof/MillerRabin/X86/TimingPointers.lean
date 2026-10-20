module

public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBase
import VerifiedGarbage.Proof.MillerRabin.X86.TimingPointerRaw
import VerifiedGarbage.Proof.MillerRabin.X86.Copy
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Correctness republishes array pointers and width after header loads -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Impl.MillerRabin.X86 VG.Proof.Dsa.X86

theorem ptr_agree {g : Geometry} {r : Reg} {d : Nat} {s t : State}
    (S : PtrAt s g.W r d) (T : PtrAt t g.W r d) : s.gpr r = t.gpr r :=
  BitVec.eq_of_toNat_eq (S.trans T.symm)

theorem pair_base {g : Geometry} {before : List Reg} {s t : State} (H : Pair g before s t) :
    VG.X86.Taint.Agree (roundTaint [.edi]) s t :=
  round_add_regs (round_forget H.2.2) (by
    intro r mem
    obtain rfl := List.mem_singleton.mp mem
    exact ptr_agree H.1.base H.2.1.base)

theorem pointer_relCT {g : Geometry} (v : g.Valid) (r : Reg) (j : Nat)
    (dst : r ∈ [.ebp, .ebx, .ecx]) (index : j < 28) (before : List Reg)
    (preserve : ∀ a ∈ before, a ≠ r ∧ a ≠ .edx) :
    RelCT isa (Pair g before) (.block (ptr r j)) fun s t =>
      Pair g (r :: before) s t ∧ PtrAt s g.W r (g.array j) ∧ PtrAt t g.W r (g.array j) := by
  have notBase : .edi ≠ r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at dst
    rcases dst with rfl | rfl | rfl <;> decide
  have notTmp : .edx ≠ r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at dst
    rcases dst with rfl | rfl | rfl <;> decide
  intro s t tr ur u z H E G
  obtain ⟨trace, A⟩ := ptr_raw r j dst _ _ _ _ _ _ (pair_base H) E G
  obtain ⟨Pu, Mu, Ku⟩ := wp_result (H.1.ptr v j index r notBase notTmp) E
  obtain ⟨Pz, Mz, Kz⟩ := wp_result (H.2.1.ptr v j index r notBase notTmp) G
  refine ⟨trace, ⟨H.1.keepMem Ku (by simp [notBase]) Mu,
    H.2.1.keepMem Kz (by simp [notBase]) Mz, ?_⟩, Pu, Pz⟩
  apply round_add_regs (round_forget A)
  intro a mem
  rcases List.mem_cons.mp mem with rfl | mem
  · exact ptr_agree Pu Pz
  · have different := preserve a mem
    rw [Ku.1 a (by simp [different.1, different.2]), Kz.1 a (by simp [different.1, different.2])]
    exact round_regs H.2.2 mem

theorem words_relCT {g : Geometry} (v : g.Valid) (before : List Reg)
    (preserve : .esi ∉ before) :
    RelCT isa (Pair g before) (.block words) fun s t =>
      Pair g (.esi :: before) s t ∧ (s.gpr .esi).toNat = g.words ∧ (t.gpr .esi).toNat = g.words := by
  intro s t tr ur u z H E G
  obtain ⟨trace, A⟩ := words_raw _ _ _ _ _ _ (pair_base H) E G
  obtain ⟨Nu, Mu, Ku⟩ := wp_result (words_ok v H.1) E
  obtain ⟨Nz, Mz, Kz⟩ := wp_result (words_ok v H.2.1) G
  refine ⟨trace, ⟨H.1.keepMem Ku (by decide) Mu, H.2.1.keepMem Kz (by decide) Mz, ?_⟩, Nu, Nz⟩
  apply round_add_regs (round_forget A)
  intro a mem
  rcases List.mem_cons.mp mem with rfl | mem
  · exact BitVec.eq_of_toNat_eq (Nu.trans Nz.symm)
  · have different : a ≠ .esi := fun eq => preserve (eq ▸ mem)
    rw [Ku.1 a (by simp [different]), Kz.1 a (by simp [different])]
    exact round_regs H.2.2 mem

theorem pointer_pair_relCT {g : Geometry} (v : g.Valid) (r : Reg) (j : Nat)
    (dst : r ∈ [.ebp, .ebx, .ecx]) (index : j < 28) (before : List Reg)
    (preserve : ∀ a ∈ before, a ≠ r ∧ a ≠ .edx) :
    RelCT isa (Pair g before) (.block (ptr r j)) (Pair g (r :: before)) :=
  (pointer_relCT v r j dst index before preserve).mono (fun _ _ H => H) (fun _ _ H => H.1)

theorem words_pair_relCT {g : Geometry} (v : g.Valid) (before : List Reg) (preserve : .esi ∉ before) :
    RelCT isa (Pair g before) (.block words) (Pair g (.esi :: before)) :=
  (words_relCT v before preserve).mono (fun _ _ H => H) (fun _ _ H => H.1)

end VG.Proof.MillerRabin.X86

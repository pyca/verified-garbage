module

public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Recognize
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rsa.BytesFrame

/-! A miss restores all original general-validator arguments without changing memory. -/

@[expose] public section
namespace VG.Proof.Ffdh.X86_64.VettedValidation
open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.VettedValidation

structure Restored (s t : State) : Prop where
  args : t.gpr .rdi = s.gpr .rdi ∧ t.gpr .rsi = s.gpr .rsi ∧
    t.gpr .rdx = s.gpr .rdx ∧ t.gpr .rcx = s.gpr .rcx ∧ t.gpr .r8 = s.gpr .r8
  mem : t.mem = entryMem s
  keep : Keep allClobbers s t
  mxcsr : t.mxcsr = s.mxcsr

theorem restore_ok {s t : State} (h : Result s t) :
    WP isa (.block restore) t (Restored s) := by
  have length : t.mem.readW (s.gpr .rcx + BitVec.ofNat 64 128) 64 = s.gpr .rsi := by
    rw [h.mem, (entryMem_saved s).1]
  have width : t.mem.readW (s.gpr .rcx + BitVec.ofNat 64 136) 64 = s.gpr .rdx := by
    rw [h.mem, (entryMem_saved s).2]
  refine WP.mono_mx (by decide +kernel)
    (WP.keep [.rsi, .rdx, .rcx] (Q := fun u =>
      (u.gpr .rsi = s.gpr .rsi ∧ u.gpr .rdx = s.gpr .rdx ∧
        u.gpr .rcx = s.gpr .rcx) ∧ u.mem = t.mem) ?_ rfl) ?_
  · xrun [restore, h.context.baseReg, h.context.readLength, h.context.readWidth, length, width]
  · rintro u ⟨⟨⟨len, key, base⟩, mem⟩, rest⟩ mxcsr
    have total : Keep allClobbers s u := (h.keep.trans rest).mono (by
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact hr
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> decide)
    exact ⟨⟨total.gpr (by decide), len, key, base, total.gpr (by decide)⟩,
      mem.trans h.mem, total, mxcsr.trans h.mxcsr⟩

theorem Restored.pre {s t : State} (h : Restored s t) (hs : contract.pre s) :
    (Spec.Ffdh.checkDomainContract abi 8).pre (plain t) := by
  have old := (pre_plain hs).1
  sig_pre [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, abi,
    argRegs, List.append_eq, Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid] at old ⊢
  simpa only [plain, stripConsts, State.withRegions, h.args.1, h.args.2.1,
    h.args.2.2.1, h.args.2.2.2.1, h.args.2.2.2.2, h.keep.2.1, h.keep.2.2,
    h.keep.gpr (r := .rsp) (by decide)] using old

theorem Restored.domain {s t : State} (h : Restored s t) (g : Geometry s) :
    CheckDomain.cdDom t = CheckDomain.cdDom s := by
  unfold CheckDomain.cdDom
  rw [h.args.1, h.args.2.1, h.mem]
  exact VG.Proof.Rsa.rsa_bytes_frame (entryMem_frame g)
    (by have := (s.gpr .rsi).isLt; omega)
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact g.separate)

theorem Restored.abi {s t : State} (h : Restored s t) (g : Geometry s) : abiPreserved s t := by
  refine ⟨fun r hr => h.keep.gpr (by revert r; decide), ?_, ?_⟩
  · rw [h.mem]
    exact (entryMem_frame g).readW (Region.contains_self _ _)
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact g.returnSeparate) (by decide)
  · rw [h.mxcsr]

end VG.Proof.Ffdh.X86_64.VettedValidation

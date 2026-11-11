module

public import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Ctr32
public import VerifiedGarbage.Proof.Aes.X86_64.ExpandKey
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
public import VerifiedGarbage.Impl.Aes.X86_64.Callee
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.Spec.Cmac.Contract
public import VerifiedGarbage.Impl.CmacAes.Stream.X86_64
public import VerifiedGarbage.Impl.AesGcm.X86_64
public import VerifiedGarbage.Impl.StackScratch.X86_64
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Implementations of `vg_aes_ctr32` on x86-64

A `Ctr32Impl` is what a function that calls `vg_aes_ctr32` needs of it, so
that its proof holds for every implementation: each is a variant of the
interface `AesCtr32` on x86-64 (`Variants/AesCtr32/X86_64/`), and each caller
(in `Generic/AesCtr32/X86_64/`) is emitted once for each of them (see
`TCB/Emit.lean`). Every implementation is proven against the same contract,
`Proof.Aes.ctr32X86_64`, and makes no calls. It comes with the
implementation of `vg_aes_expand_key` that goes with it (with the same
suffix and CPU features), for the callers that also expand the key, proven
against `Proof.Aes.expandKeyX86_64`. One that never touches its scratch
buffer also gives its contract without one (`free`), so that a caller of
it alone needs no working space for it, and the residue analyses of the
functions over it that the analysis handles (`gcmInitRes`, `cmacFinishRes`): those instances
then return without secret residue (`X86_64.RScrub.withScrub`).
-/

@[expose] public section

namespace VG.Proof.Aes.X86_64

open VG.X86_64

/-- An implementation of `vg_aes_ctr32_to` on x86-64: `vg_aes_ctr32` out of
place (`AesNi.ctr32ToX86_64`), the data read from `rcx` and the output
written to `r11`. -/
structure Ctr32ToImpl where
  /-- Its symbol and code. -/
  callee : Impl.Aes.X86_64.Ctr32
  /-- It makes no calls. -/
  depth : callee.code.depth = 0
  ok : ∀ s, AesNi.ctr32ToX86_64.pre s →
    ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧ AesNi.ctr32ToX86_64.post s s'
  ct : ConstantTime isa AesNi.ctr32ToX86_64.pre AesNi.ctr32ToX86_64.pub callee.code
  /-- It never writes the stack pointer. -/
  nosp : NoSp callee.code
  /-- It never loads MXCSR. -/
  mxcsr : callee.code.allInstrs (fun i => !loadsMxcsr i) = true
  spSafe : callee.code.all (fun i => !isa.writesSp i) = true
  /-- It uses no stack. -/
  noStack : callee.code.x86_64Depth = 0 := by lit_decide

/-- What an implementation of `vg_aes_ctr32` that never touches its scratch
buffer gives: its contract without one (`AesNi.ctr32X86_64F`), so that its
callers need not set aside one. -/
structure Ctr32Free (callee : Impl.Aes.X86_64.Ctr32) : Type where
  ok : ∀ s, AesNi.ctr32X86_64F.pre s →
    ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧ AesNi.ctr32X86_64F.post s s'
  ct : ConstantTime isa AesNi.ctr32X86_64F.pre AesNi.ctr32X86_64F.pub callee.code

/-- `vg_aes_gcm_init`'s code over `callee` and `vg_aes_expand_key_scratch_aesni`
when neither needs working space (`Ctr32Free`): a frame of only the 176
bytes `init` writes itself. It calls only those two, so the other functions
of its callees are left empty. -/
def gcmInitCodeF (callee : Impl.Aes.X86_64.Ctr32) : Prog isa :=
  Impl.StackScratch.X86_64.withStackScratch 184 .rcx
    (Impl.AesGcm.X86_64.init ⟨⟨callee.name, callee.code⟩,
      ⟨"vg_aes_expand_key_scratch_aesni", Impl.Aes.X86_64.AesNi.expandKey⟩, ⟨"", .block []⟩,
      ⟨"", .block []⟩, ⟨"", .block []⟩⟩)

/-- An implementation of `vg_aes_ctr32` on x86-64. -/
structure Ctr32Impl where
  /-- Its symbol and code. -/
  callee : Impl.Aes.X86_64.Ctr32
  /-- It makes no calls. -/
  depth : callee.code.depth = 0
  ok : ∀ s, Proof.Aes.ctr32X86_64.pre s →
    ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧ Proof.Aes.ctr32X86_64.post s s'
  ct : ConstantTime isa Proof.Aes.ctr32X86_64.pre Proof.Aes.ctr32X86_64.pub callee.code
  /-- It never writes the stack pointer. -/
  nosp : NoSp callee.code
  /-- It never loads MXCSR. -/
  mxcsr : callee.code.allInstrs (fun i => !loadsMxcsr i) = true
  spSafe : callee.code.all (fun i => !isa.writesSp i) = true
  /-- It uses no stack. -/
  noStack : callee.code.x86_64Depth = 0 := by lit_decide
  /-- What the names of its callers' instances end with (e.g. `_aesni`;
  nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String
  /-- The implementation of `vg_aes_expand_key` that goes with it, which
  needs no more CPU features. -/
  expand : Impl.Aes.X86_64.ExpandKey
  expandDepth : expand.code.depth = 0
  expandOk : ∀ s, Proof.Aes.expandKeyX86_64.pre s →
    ∃ t s', Exec isa expand.code s t s' ∧ abiPreserved s s' ∧ Proof.Aes.expandKeyX86_64.post s s'
  expandCt : ConstantTime isa Proof.Aes.expandKeyX86_64.pre Proof.Aes.expandKeyX86_64.pub expand.code
  expandNosp : NoSp expand.code
  expandMxcsr : expand.code.allInstrs (fun i => !loadsMxcsr i) = true
  expandSpSafe : expand.code.all (fun i => !isa.writesSp i) = true
  expandNoStack : expand.code.x86_64Depth = 0 := by lit_decide
  /-- Its form out of place (`vg_aes_ctr32_to`), with the same CPU features:
  AES-GCM's `open_to` decrypts with it in one pass. -/
  ctrTo : Ctr32ToImpl
  /-- Its contract without a scratch buffer, if it never touches one. -/
  free : Option (Ctr32Free callee) := none
  /-- The residue analysis of `vg_aes_gcm_init` over it, without working
  space for it (`free`), if the analysis handles it. -/
  gcmInitRes : Option (RScrub.Analysed Spec.Gcm.initApi.sig 192 [] (gcmInitCodeF callee)) := none
  /-- The residue analysis of `vg_cmac_aes_finish` over it, without working
  space for it (`free`, `Impl.CmacAes.Stream.X86_64.finishF`), if the analysis
  handles it. -/
  cmacFinishRes : Option (RScrub.Analysed Spec.Cmac.aesFinishApi.sig 40 []
    (Impl.StackScratch.X86_64.withStackScratch 24 .r8 (Impl.CmacAes.Stream.X86_64.finishF callee suffix))) :=
    none

namespace Ctr32Impl

theorem scalar_nosp : NoSp Impl.Aes.X86_64.Ctr32.scalar.code := by
  have : ((instrs Impl.Aes.X86_64.Ctr32.scalar.code).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  exact fun i hi => by simpa using List.all_eq_true.mp this i hi

theorem expandKey_nosp : NoSp Impl.Aes.X86_64.ExpandKey.scalar.code := by
  have : ((instrs Impl.Aes.X86_64.ExpandKey.scalar.code).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  exact fun i hi => by simpa using List.all_eq_true.mp this i hi

theorem scalarTo_nosp : NoSp Impl.Aes.X86_64.Ctr32.scalarTo.code := by
  have : ((instrs Impl.Aes.X86_64.Ctr32.scalarTo.code).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  exact fun i hi => by simpa using List.all_eq_true.mp this i hi

/-- `vg_aes_ctr32_to`, the bitsliced implementation out of place. -/
def scalarTo : Ctr32ToImpl where
  callee := .scalarTo
  depth := by lit_decide
  ok := ctr32To_correct
  ct := ctr32To_ct
  nosp := scalarTo_nosp
  mxcsr := by lit_decide
  spSafe := Code.all_of_allInstrs (by lit_decide)

/-- The bitsliced implementation, `vg_aes_ctr32`, in the baseline ISA. -/
def scalar : Ctr32Impl where
  callee := .scalar
  depth := by lit_decide
  ok := ctr32_correct
  ct := ctr32_ct
  nosp := scalar_nosp
  mxcsr := by lit_decide
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := ""
  features := []
  ctrTo := scalarTo
  expand := .scalar
  expandDepth := by lit_decide
  expandOk := expandKey_correct
  expandCt := expandKey_ct
  expandNosp := expandKey_nosp
  expandMxcsr := by lit_decide
  expandSpSafe := Code.all_of_allInstrs (by lit_decide)

theorem aesni_nosp : NoSp Impl.Aes.X86_64.Ctr32.aesni.code := by
  have : ((instrs Impl.Aes.X86_64.Ctr32.aesni.code).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  exact fun i hi => by simpa using List.all_eq_true.mp this i hi

/-- `vg_aes_ctr32_aesni`'s own contract is the same, but for `rsp`, which its
public data leaves out. -/
theorem aesni_ct : ConstantTime isa Proof.Aes.ctr32X86_64.pre Proof.Aes.ctr32X86_64.pub
    Impl.Aes.X86_64.Ctr32.aesni.code :=
  fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ ⟨a, b, c, d, e, f, _⟩ e₁ e₂ =>
    AesNi.ctr32_ct s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ ⟨a, b, c, d, e, f⟩ e₁ e₂

theorem aesni_expandKey_nosp : NoSp Impl.Aes.X86_64.ExpandKey.aesni.code := by
  have : ((instrs Impl.Aes.X86_64.ExpandKey.aesni.code).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  exact fun i hi => by simpa using List.all_eq_true.mp this i hi

/-- `vg_aes_expand_key_aesni`'s own contract asks less of its arguments. -/
theorem aesni_expandKey_ok : ∀ s, Proof.Aes.expandKeyX86_64.pre s →
    ∃ t s', Exec isa Impl.Aes.X86_64.ExpandKey.aesni.code s t s' ∧ abiPreserved s s' ∧
      Proof.Aes.expandKeyX86_64.post s s' :=
  fun s ⟨a, b, _, _, _, c, _, d⟩ => AesNi.Key.expandKey_correct s ⟨a, b, c, d⟩

/-- … and its public data leave out `rsp`. -/
theorem aesni_expandKey_ct : ConstantTime isa Proof.Aes.expandKeyX86_64.pre Proof.Aes.expandKeyX86_64.pub
    Impl.Aes.X86_64.ExpandKey.aesni.code :=
  fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨a, b, _, _, _, c, _, d⟩ ⟨a', b', _, _, _, c', _, d'⟩ ⟨e, f, g, h, _⟩ e₁ e₂ =>
    AesNi.Key.expandKey_ct s₁ s₂ t₁ t₂ s₁' s₂' ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ ⟨e, f, g, h⟩ e₁ e₂

theorem aesniTo_nosp : NoSp Impl.Aes.X86_64.Ctr32.aesniTo.code := by
  have : ((instrs Impl.Aes.X86_64.Ctr32.aesniTo.code).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  exact fun i hi => by simpa using List.all_eq_true.mp this i hi

/-- `vg_aes_ctr32_to_aesni`. -/
def aesniTo : Ctr32ToImpl where
  callee := .aesniTo
  depth := by lit_decide
  ok := AesNi.ctr32To_correct
  ct := AesNi.ctr32To_ct
  nosp := aesniTo_nosp
  mxcsr := by lit_decide
  spSafe := Code.all_of_allInstrs (by lit_decide)

/-- The AES-NI implementation, `vg_aes_ctr32_aesni`. -/
def aesni : Ctr32Impl where
  callee := .aesni
  depth := by lit_decide
  ok := AesNi.ctr32_correct
  ct := aesni_ct
  nosp := aesni_nosp
  mxcsr := by lit_decide
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := "_aesni"
  features := ["aes", "ssse3"]
  ctrTo := aesniTo
  free := some ⟨AesNi.ctr32F_correct, AesNi.ctr32_ctP⟩
  expand := .aesni
  expandDepth := by lit_decide
  expandOk := aesni_expandKey_ok
  expandCt := aesni_expandKey_ct
  expandNosp := aesni_expandKey_nosp
  expandMxcsr := by lit_decide
  expandSpSafe := Code.all_of_allInstrs (by lit_decide)

theorem vaes_nosp : NoSp Impl.Aes.X86_64.Ctr32.vaes.code := by
  have : ((instrs Impl.Aes.X86_64.Ctr32.vaes.code).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  exact fun i hi => by simpa using List.all_eq_true.mp this i hi

/-- `vg_aes_ctr32_vaes`'s own contract is `vg_aes_ctr32_aesni`'s. -/
theorem vaes_ct : ConstantTime isa Proof.Aes.ctr32X86_64.pre Proof.Aes.ctr32X86_64.pub
    Impl.Aes.X86_64.Ctr32.vaes.code :=
  fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ ⟨a, b, c, d, e, f, _⟩ e₁ e₂ =>
    Vaes.ctr32_ct s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ ⟨a, b, c, d, e, f⟩ e₁ e₂

theorem vaesTo_nosp : NoSp Impl.Aes.X86_64.Ctr32.vaesTo.code := by
  have : ((instrs Impl.Aes.X86_64.Ctr32.vaesTo.code).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  exact fun i hi => by simpa using List.all_eq_true.mp this i hi

/-- `vg_aes_ctr32_to_vaes`. -/
def vaesTo : Ctr32ToImpl where
  callee := .vaesTo
  depth := by lit_decide
  ok := Vaes.ctr32To_correct
  ct := Vaes.ctr32To_ct
  nosp := vaesTo_nosp
  mxcsr := by lit_decide
  spSafe := Code.all_of_allInstrs (by lit_decide)

/-- The VAES implementation, `vg_aes_ctr32_vaes`. It goes with
`vg_aes_expand_key_aesni`, which needs no more CPU features. -/
def vaes : Ctr32Impl where
  callee := .vaes
  depth := by lit_decide
  ok := Vaes.ctr32_correct
  ct := vaes_ct
  nosp := vaes_nosp
  mxcsr := by lit_decide
  spSafe := Code.all_of_allInstrs (by lit_decide)
  suffix := "_vaes"
  features := ["aes", "avx", "avx2", "ssse3", "vaes"]
  ctrTo := vaesTo
  free := some ⟨Vaes.ctr32F_correct, Vaes.ctr32_ctP⟩
  expand := .aesni
  expandDepth := by lit_decide
  expandOk := aesni_expandKey_ok
  expandCt := aesni_expandKey_ct
  expandNosp := aesni_expandKey_nosp
  expandMxcsr := by lit_decide
  expandSpSafe := Code.all_of_allInstrs (by lit_decide)

end Ctr32Impl

end VG.Proof.Aes.X86_64

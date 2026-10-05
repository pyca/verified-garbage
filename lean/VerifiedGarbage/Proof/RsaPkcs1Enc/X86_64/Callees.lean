import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.DecContract
import VerifiedGarbage.Proof.Rsa.X86_64.PrivCT
import VerifiedGarbage.Proof.Rsa.X86_64.PrivCT
import VerifiedGarbage.Proof.Rsa.X86_64.PubChecked
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncContract

/-!
# The callees of encryption and decryption

`vg_rsa_public_checked` is a `PubImpl` (`pubImpl`). For each implementation `c` of `vg_rsa_private_crt` (a variant of
`RsaPrivateCrt`), `vg_rsa_private_checked` calling it, as
`Generic/RsaPrivateCrt/X86_64/Rsa.lean` emits it, is a `PrivImpl`
(`privOf`): `privK` is its contract, and it uses its frame and a return
address of stack, since its callees use none.
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64

open VG VG.X86_64 VG.Proof.Rsa.X86_64

theorem pubChkK_eq : pubChkK = pubChkContract := rfl

/-- `vg_rsa_public_checked`, as encryption's callee. -/
def pubImpl : PubImpl where
  name := Spec.Rsa.publicCheckedApi.name
  code := Impl.Rsa.X86_64.Checked.publicChecked
  ok := pubChkK_eq ▸ publicChecked_correct
  ct := pubChkK_eq ▸ publicChecked_constantTime
  nosp := noSp_of (by decide +kernel)
  depth := by decide +kernel
  spSafe := Code.all_of_allInstrs (by decide +kernel)

theorem privK_eq : privK = chkContract := rfl

/-- Code without calls or frames uses no stack. -/
theorem x86_64Depth_zero {c : Prog isa} (hn : NoSp c) (hd : c.depth = 0) : c.x86_64Depth = 0 := by
  induction c with
  | block _ => rfl
  | seq a b iha ihb =>
    simp only [Code.depth] at hd
    simp only [Code.x86_64Depth, iha (fun i hi => hn i (List.mem_append_left _ hi)) (Nat.max_eq_zero_iff.mp hd).1,
      ihb (fun i hi => hn i (List.mem_append_right _ hi)) (Nat.max_eq_zero_iff.mp hd).2, Nat.max_self]
  | ite _ t e iht ihe =>
    simp only [Code.depth] at hd
    simp only [Code.x86_64Depth, iht (fun i hi => hn i (List.mem_append_left _ hi)) (Nat.max_eq_zero_iff.mp hd).1,
      ihe (fun i hi => hn i (List.mem_append_right _ hi)) (Nat.max_eq_zero_iff.mp hd).2, Nat.max_self]
  | loop b _ ih => exact ih hn hd
  | call _ b _ => simp [Code.depth] at hd
  | frame x b y ih =>
    have hx := hn x (List.mem_cons_self ..)
    rw [Code.x86_64Depth, ih (fun i hi => hn i (List.mem_cons_of_mem _ (List.mem_append_left _ hi))) hd]
    cases x <;> first | rfl | simp [Taint.clobbers] at hx

/-- The name of `vg_rsa_private_checked` calling `c`. -/
def privName (c : CrtImpl) : String := Spec.Rsa.privateCheckedApi.name ++ c.suffix

/-- Its code, as `Generic/RsaPrivateCrt/X86_64/Rsa.lean` emits it. -/
def privCode (c : CrtImpl) : Prog isa :=
  Impl.Rsa.X86_64.PrivChecked.code c.name c.code (Spec.Rsa.publicPrecomputeApi.name ++ c.montSuffix)
    (Impl.Rsa.X86_64.Precompute.code c.mont.mm) (Spec.Rsa.publicPrecomputedCheckedApi.name ++ c.montSuffix)
    (Impl.Rsa.X86_64.Checked.precomputedChecked c.mont.mm)

theorem privCode_depth (c : CrtImpl) : (privCode c).x86_64Depth ≤ privStack := by
  simp only [privCode, Impl.Rsa.X86_64.PrivChecked.code, Impl.Rsa.X86_64.PrivChecked.body,
    Impl.Rsa.X86_64.PrivChecked.check, Impl.Rsa.X86_64.PrivChecked.tail, List.cons_append, List.nil_append,
    Impl.Bignum.X86_64.seqs, Code.x86_64Depth, x86_64Depth_zero c.nosp c.depth,
    x86_64Depth_zero c.pcNosp c.pcDepth, x86_64Depth_zero c.pdNosp c.pdDepth]
  decide

/-- `vg_rsa_private_checked` calling `c`, as decryption's callee. -/
def privOf (c : CrtImpl) : PrivImpl where
  name := privName c
  code := privCode c
  ok := privK_eq ▸ code_correct c _ _
  ct := privK_eq ▸ code_constantTime c _ _
  spSafe := code_spSafe c _ _
  depth := privCode_depth c

end VG.Proof.RsaPkcs1Enc.X86_64

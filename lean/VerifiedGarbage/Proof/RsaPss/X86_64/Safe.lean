import VerifiedGarbage.Proof.RsaPss.X86_64.Mgf
import VerifiedGarbage.Proof.RsaPss.X86_64.SignEnc
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame

/-!
# RSASSA-PSS on x86-64: no writes to `rsp`, no loads of MXCSR

Every instruction of `ctHash` (and of what it calls) neither writes `rsp`
(`SpSafe`) nor loads MXCSR (`ctHash_safe`).
-/

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

/-- Neither writes `rsp` nor loads MXCSR. -/
def safeI (i : Instr) : Bool := !isa.writesSp i && !loadsMxcsr i

theorem allInstrs_and (f g : Instr → Bool) (c : Prog isa) :
    c.allInstrs (fun i => f i && g i) = (c.allInstrs f && c.allInstrs g) := by
  simp only [Code.allInstrs_eq]
  induction instrs c with
  | nil => rfl
  | cons i is ih =>
    simp only [List.all_cons, ih]
    cases f i <;> cases g i <;> simp

theorem safeI_eq : safeI = fun i => !isa.writesSp i && !loadsMxcsr i := rfl

theorem safe_sp {c : Prog isa} (h : c.allInstrs safeI = true) : SpSafe c := by
  rw [Code.allInstrs_eq] at h
  intro i hi
  have := List.all_eq_true.mp h i hi
  simp only [safeI, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
  exact this.1

theorem safe_mx {c : Prog isa} (h : c.allInstrs safeI = true) : c.allInstrs (fun i => !loadsMxcsr i) = true := by
  rw [safeI_eq, allInstrs_and] at h
  simp only [Bool.and_eq_true] at h
  exact h.2

variable {H : Hash} (hH : HashOK H) (K : Callees H)

include K in
theorem comp_safe : H.compC.allInstrs safeI = true := by
  rw [safeI_eq, allInstrs_and, K.cSp, K.cMx]; rfl

include K in
theorem init_safe : H.initC.allInstrs safeI = true := by
  rw [safeI_eq, allInstrs_and, K.iSp, K.iMx]; rfl

theorem rec_all (p : Instr → Bool) (l : List Instr) :
    List.rec (motive := fun _ => Bool) true (fun i _ ih => p i && ih) l = l.all p := by
  induction l with
  | nil => rfl
  | cons i is ih => simp only [List.all_cons, ← ih]

include hH K in
theorem ctHashWith_safe {padding : Prog isa} (hp : padding.allInstrs safeI = true) :
    (ctHashWith H padding).allInstrs safeI = true := by
  have hl : H.P.len.all safeI = true := hH.taints.lenSafe
  have ho : H.P.out.all safeI = true := hH.taints.outSafe
  simp only [ctHashWith, hp, seqs, ctInit, lenLoop, compLoop, select, Code.allInstrs, comp_safe K, init_safe K,
    rec_all, lenField, digestOut, List.all_append, hl, ho, byteLoop, step, Bool.and_true, Bool.true_and]
  rfl

include hH K in
theorem ctHash_safe : (ctHash H).allInstrs safeI = true := ctHashWith_safe hH K rfl

include hH K in
theorem mgfHash_safe : (mgfHash H).allInstrs safeI = true := ctHashWith_safe hH K rfl

include hH K in
theorem mgfXor_safe : (mgfXor H).allInstrs safeI = true := by
  simp only [mgfXor, seqs, clearBlock, copyH, xorOut, Code.allInstrs, mgfHash_safe hH K, rec_all, List.all_append,
    byteLoop, step, Bool.and_true, Bool.true_and]
  rfl

include K in
theorem ctHashWith_xd {padding : Prog isa} (hp : padding.x86_64Depth = 0) :
    (ctHashWith H padding).x86_64Depth = 8 := by
  simp only [ctHashWith, hp, seqs, ctInit, lenLoop, compLoop, select, byteLoop, Code.x86_64Depth, K.cXD, K.iXD]
  rfl

include K in
theorem ctHash_xd : (ctHash H).x86_64Depth = 8 := ctHashWith_xd K rfl

include K in
theorem mgfHash_xd : (mgfHash H).x86_64Depth = 8 := ctHashWith_xd K rfl

include K in
theorem mgfXor_xd : (mgfXor H).x86_64Depth = 8 := by
  simp only [mgfXor, seqs, clearBlock, copyH, xorOut, byteLoop, Code.x86_64Depth, mgfHash_xd K]
  rfl

include hH K in
theorem signEnc_safe : (signEnc H).allInstrs safeI = true := by
  simp only [signEnc, seqs, clearY, copyDigest, copySaltY, clearEm, putSalt, putH, Code.allInstrs, ctHash_safe hH K,
    mgfXor_safe hH K, rec_all, List.all_append, byteLoop, step, Bool.and_true, Bool.true_and]
  rfl

include K in
theorem signEnc_xd : (signEnc H).x86_64Depth = 8 := by
  simp only [signEnc, seqs, clearY, copyDigest, copySaltY, clearEm, putSalt, putH, byteLoop, Code.x86_64Depth,
    ctHash_xd K, mgfXor_xd K]
  rfl

/-- Code that is `safeI` and uses at most 8 bytes of stack keeps memory
outside the writable regions and the 8 bytes below `rsp`. -/
theorem WP.keepIn {c : Prog isa} (hc : c.allInstrs safeI = true) (hd : c.x86_64Depth ≤ 8) {u : State}
    {Q : State → Prop} (h : WP isa c u Q) :
    WP isa c u fun v => Q v ∧ ∀ a, (∀ r ∈ u.wr, ¬ r.Contains a 1) → ¬ (below (u.gpr .rsp) 8).Contains a 1 →
      v.mem a = u.mem a := by
  refine WP.mono (X86_64.WP.stackFrame (safe_sp hc) (by omega) h) fun v ⟨hq, hf⟩ => ⟨hq, fun a h1 h2 => ?_⟩
  refine Frame.below_mono hf hd (by decide) a fun r hr => ?_
  rcases List.mem_append.mp hr with hr | hr
  · exact h1 r hr
  · simp only [List.mem_singleton] at hr; subst hr; exact h2

end VG.Proof.RsaPss.X86_64

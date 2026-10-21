module

public import VerifiedGarbage.Proof.Rsa.X86.CvRt.TimeCheck
public import VerifiedGarbage.Proof.Rsa.X86.CvRt.Checks
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Rsa.X86.InvParts
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
public import Init.Data.List.Basic
public import Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Impl.Rsa.X86.KeyRt

/-! # Isolating the inverse in the CRT import trace -/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValuesRt
open VG VG.X86 VG.Impl.Rsa.X86.Keys VG.Impl.Rsa.X86.CrtValuesRt

 theorem exec_seqs_split {l₁ l₂ : List (Prog isa)} (h₁ : l₁≠[]) (h₂ : l₂≠[])
    {s t : State} {tr : List Leak} (E : Exec isa (seqs (l₁++l₂)) s tr t) :
    ∃ a b u,tr=a++b ∧ Exec isa (seqs l₁) s a u ∧ Exec isa (seqs l₂) u b t := by
  induction l₁ generalizing s tr with
  | nil => exact absurd rfl h₁
  | cons c l ih =>
    cases l with
    | nil =>
      have shape : seqs ([c]++l₂)=.seq c (seqs l₂) := by cases l₂ <;> simp_all [seqs]
      rw [shape] at E
      cases E with
      | seq ec er => exact ⟨_,_,_,rfl,ec,er⟩
    | cons d l =>
      change Exec isa (.seq c (seqs ((d::l)++l₂))) s tr t at E
      cases E with
      | seq ec er =>
        obtain ⟨a,b,u,eq,ea,eb⟩ := ih (by simp) er
        refine ⟨_,b,u,?_,.seq ec ea,eb⟩
        rw [eq,List.append_assoc]

 theorem exec_split {s t : State} {tr : List Leak} (E : Exec isa sized s tr t) :
    Exec isa (.seq beforeInverse (.seq inverseChoice afterInverse)) s tr t := by
  change Exec isa (.seq loads (.seq core stores)) s tr t at E
  cases E with
  | seq el er =>
    cases er with
    | seq ec es =>
      change Exec isa (.seq firstDiv (.seq checks (.seq (VG.Impl.Rsa.X86.CrtValuesRt.div VG.Impl.Rsa.X86.CrtValues.aDR2) divQ))) _ _ _ at ec
      cases ec with
      | seq ef er =>
        cases er with
        | seq ech ed =>
          cases ed with
          | seq ep eq =>
            change Exec isa (seqs (checksA++checksB)) _ _ _ at ech
            obtain ⟨a,b,u,eab,ea,eb⟩ := exec_seqs_split (by unfold checksA; exact List.cons_ne_nil _ _) (by unfold checksB; exact List.cons_ne_nil _ _) ech
            change Exec isa (.seq inverseChoice (seqs checksB.tail)) _ _ _ at eb
            cases eb with
            | seq ei et =>
              have out := Exec.seq (Exec.seq el (Exec.seq ef ea)) (Exec.seq ei (Exec.seq et (Exec.seq ep (Exec.seq eq es))))
              simp only [List.append_assoc] at eab ⊢
              rw [eab]
              simpa only [beforeInverse,afterInverse,checksA,checksPrefix,checksB,checksSuffix,List.tail_cons,List.append_assoc] using out

 theorem split_relCT {P Q : State → State → Prop}
    (h : RelCT isa P (.seq beforeInverse (.seq inverseChoice afterInverse)) Q) : RelCT isa P sized Q :=
  fun s t tr ur sf tf hp es et => h s t tr ur sf tf hp (exec_split es) (exec_split et)

end VG.Proof.Rsa.X86.CrtValuesRt

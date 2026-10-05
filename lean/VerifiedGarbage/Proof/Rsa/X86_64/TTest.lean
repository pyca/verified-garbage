import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
namespace VG.Proof.Rsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys VG.Impl.Rsa.X86_64.Keys.CrtValues
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64
example : RelCT isa (Two (fun (_ : Unit) (_ : State) => False)) (.seq (.block (base aU .r8 ++ [.mov .r11 (.reg .r12)] ++ List.replicate 6 (.alu .add .r11 (.reg .r11)) ++
    [.mov32 .r13 (.imm 0)])) (.seq zeroAccLoop (.loop (VG.Impl.Rsa.X86_64.Keys.divStep aU aV aP aT) .ne))) fun _ _ => True :=
  two_taint [.rdi, .r12, .r9] (fun _ _ _ h => h.elim) (by taint_decide)
example : RelCT isa (Two (fun (_ : Unit) (_ : State) => False)) (.seq (.block ([.mov .r11 (.reg .r12)] ++ List.replicate 7 (.alu .add .r11 (.reg .r11)) ++ [.mov32 .r13 (.imm 0)]))
   (.loop (VG.Impl.Rsa.X86_64.Keys.invStep aU aV aX₁ aX₂ aP aT) .ne)) fun _ _ => True :=
  two_taint [.rdi, .r12, .r9] (fun _ _ _ h => h.elim) (by taint_decide)
end VG.Proof.Rsa.X86_64

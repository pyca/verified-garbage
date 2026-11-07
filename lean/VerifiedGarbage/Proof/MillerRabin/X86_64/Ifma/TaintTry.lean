module

public import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTRegion
public import VerifiedGarbage.Impl.MillerRabin.X86_64.Ifma
meta import VerifiedGarbage.Proof.Bignum.X86_64.Ifma.CTRegion
meta import VerifiedGarbage.Impl.MillerRabin.X86_64.Ifma

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64.Ifma
open VG VG.X86_64 VG.Proof.Bignum.X86_64.Ifma

open VG.Impl.Bignum.X86_64 in
open VG.Impl.Bignum.X86_64 in
theorem t_setup : TOk [.rdi] (seqs (VG.Impl.MillerRabin.X86_64.Ifma.setup VG.Impl.Rsa.X86_64.PubIfma.pay2048)) := ⟨_, by taint_decide⟩

open VG.Impl.Bignum.X86_64 in
theorem t_table : TOk [.rdi, .rbx] (VG.Impl.MillerRabin.X86_64.Ifma.table VG.Impl.Rsa.X86_64.PubIfma.pay2048) := ⟨_, by taint_decide⟩

open VG.Impl.Bignum.X86_64 in
theorem t_windows : TOk [.rdi, .rbx] (seqs (VG.Impl.MillerRabin.X86_64.Ifma.windows VG.Impl.Rsa.X86_64.PubIfma.pay2048)) := ⟨_, by taint_decide⟩

open VG.Impl.Bignum.X86_64 in
theorem t_vec : TOk [.rdi, .rbx] (VG.Impl.MillerRabin.X86_64.Ifma.vec VG.Impl.Rsa.X86_64.PubIfma.pay2048) := ⟨_, by taint_decide⟩

open VG.Impl.Bignum.X86_64 in
theorem t_fin : TOk [.rdi, .rsp, .rbx] (.block VG.Impl.MillerRabin.X86_64.Ifma.finish) := ⟨_, by taint_decide⟩

open VG.Impl.Bignum.X86_64 in
theorem t_finsp : TOk [.rdi, .rsp] (.block VG.Impl.MillerRabin.X86_64.Ifma.finish) := ⟨_, by taint_decide⟩

open VG.Impl.Bignum.X86_64 in

open VG.Impl.Bignum.X86_64 in

open VG.Impl.Bignum.X86_64 in

end VG.Proof.MillerRabin.X86_64.Ifma

namespace VG.Proof.MillerRabin.X86_64.Ifma
open VG VG.X86_64 VG.Proof.Bignum.X86_64.Ifma VG.Impl.Bignum.X86_64
theorem t_body : TOk [.rdi, .rsp] (seqs (VG.Impl.MillerRabin.X86_64.Ifma.setup VG.Impl.Rsa.X86_64.PubIfma.pay2048 ++
  [VG.Impl.MillerRabin.X86_64.Ifma.vec VG.Impl.Rsa.X86_64.PubIfma.pay2048, .block VG.Impl.MillerRabin.X86_64.Ifma.finish])) := ⟨_, by taint_decide⟩
theorem t_fr : TOk [.rdi, .rsp] (.frame (.push [.rbx, .rbp, .r12, .r13, .r14, .r15]) (.block []) (.pop .r11 6)) := ⟨_, by taint_decide⟩
end VG.Proof.MillerRabin.X86_64.Ifma

module
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrSq


/-! # Staging saved words does not change the prepared workspace -/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.RsaKeyGen.X86_64
open VG.Proof.MlKem.X86_64

theorem staged_context {s t : State} {B : Addr} {Z w c bm : Nat} {mi : BitVec 64}
    (hc : MrCtx s B Z w mi c bm) (he : ECtx s.mem B w c)
    (hm : t.mem = s.mem) (hk : Keep [.rsi, .rdx, .rcx, .r8, .r9, .rax, .r10, .r11] s t) :
    MrCtx t B Z w mi c bm ∧ ECtx t.mem B w c := by
  refine ⟨⟨⟨hc.good.scr.congr hk.2.2, (hk.gpr (by decide)).trans hc.good.rdi, ?_⟩,
    ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hm]; exact hc.good.hdr
  · rw [hm]; exact hc.inv
  · rw [hm]; exact hc.n
  · rw [hm]; exact hc.b
  · rw [hm]; exact hc.r1
  · rw [hm]; exact hc.rm1
  · rw [hm]; exact he

end VG.Proof.MillerRabin.X86_64

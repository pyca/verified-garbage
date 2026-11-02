module

import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtContract
public import VerifiedGarbage.Proof.Bignum.X86_64.PcCode
public import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Call

/-!
# The RSA functions' postconditions do not read the return address

What `ok_of_inline` and `Verified.of_inline` need of the contracts of the
x86-64 RSA functions that call `vg_rsa_mont_mul`: their postconditions read
memory only in their writable buffers, which a precondition with `Clear`
keeps off the 8 bytes below `rsp`.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64

theorem pc_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64) (hs : pcContract.pre s)
    (hc : Clear (hole (s.gpr .rsp)) s) (hp : pcContract.post s b) :
    pcContract.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  obtain ⟨-, hwr, -, -, -, -, -, -, hn, -⟩ := hs
  have hm := Clear.miss_wr hc (by rw [hwr]; simp) hn (Nat.le_refl _)
  simp only [pcContract, State.patch_gpr] at hp ⊢
  rw [patch_mem, wordsAt_overlay fun i hi => hm i (by omega)]
  exact hp

theorem crt_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64) (hs : crtContract.pre s)
    (hc : Clear (hole (s.gpr .rsp)) s) (hp : crtContract.post s b) :
    crtContract.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  have hn : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, -, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hl, -⟩ := hs
  have hm := Clear.miss_wr hc (by rw [hwr]; simp) hn (Nat.le_of_eq hl.symm)
  simp only [crtContract, State.patch_gpr] at hp ⊢
  rw [patch_mem, written_overlay hm]
  exact hp

end VG.Proof.Bignum.X86_64

module

public import VerifiedGarbage.Impl.RsaKeyGen.X86_64.Fn
public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.Generate.Verified
public import VerifiedGarbage.Proof.Rsa.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubFillG
import VerifiedGarbage.Proof.Framework.Lit

/-!
# RSA key generation's search on x86-64, without secret residue

`vg_rsa_generate` as emitted (`Impl.RsaKeyGen.X86_64.Fn.keySearch`), over any
implementation of the Miller–Rabin round (`RoundImpl`), its whole stack wiped
by its cleanup at the implementation's level. Its code is its code over a
stub (`stub`), with the implementation's round where it calls it and its
Montgomery multiplication where it runs it (`FillG`, `fill_gen`): the kernel
evaluates what the cleanup needs of the stub once, and the implementation
what it needs of its own code where it is defined (`RoundImpl.side`,
`RoundImpl.mmSide`).
-/

-- separate module: the kernel's evaluation of the cleanup's side conditions, which a registration file may not hold

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64.SearchScrub

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64
open VG.Proof.MillerRabin.X86_64 (RoundImpl)

/-- The stack the round (called) and the multiplication need. -/
def stubStack : String → Nat := fun s => if s = "r" then 128 else 8

/-- Key generation's code over stubs of the round and the multiplication. -/
def stub : Prog isa :=
  Impl.RsaKeyGen.X86_64.Generate.code
    (.call "s" (Impl.RsaKeyGen.X86_64.Search.code (.call "c" (Impl.RsaKeyGen.X86_64.Candidate.codeWith
      (fun _ _ _ => .call "mm" (.block [])) (Impl.MillerRabin.X86_64.Caller.call "r" (.block []))))))
    (.call "vg_rsa_keygen_key" Impl.RsaKeyGen.X86_64.Key.code)

theorem stub_side : stubSideG stub VecLevel.sse.level stubStack 552 [] = true := by lit_decide

theorem fill (v : RoundImpl) : FillG v.level.level stubStack stub (Generate.genCode v) := by
  have hr := v.side
  have hm := v.mmSide
  unfold stub Generate.genCode Generate.searchCall Search.searchCode Search.candidateCall
    sharedCandidateCode RoundImpl.name Generate.keyCall
  fill_gen

/-- Key generation over `v`, before its cleanup. -/
def plain [Key.KeyProof] (v : RoundImpl) : Unscrubbed Spec.RsaKeyGen.keySearchApi target where
  code := Generate.genCode v
  verified := Generate.gen_verified v
  spSafe := Generate.genCode_sp v

/-- `Spec.RsaKeyGen.keySearchApi`'s function as emitted over `v` meets its
contract in constant time and returns without secret residue. -/
theorem keySearch_scrubbed [Key.KeyProof] (v : RoundImpl) :
    VerifiedScrubbed target (Impl.RsaKeyGen.X86_64.Fn.keySearch v.level (Generate.searchCall v))
      (Spec.RsaKeyGen.keySearchApi.contract X86_64.abi 552) 32 :=
  verifiedScrubbedAllFillG (plain v) _ (Proof.Rsa.X86_64.Scrub.keySearchOut _) (fill v) (Nat.zero_le _)
    (Nat.le_refl _) (ha := stub_side)

theorem keySearch_spSafe (v : RoundImpl) :
    (Impl.RsaKeyGen.X86_64.Fn.keySearch v.level (Generate.searchCall v)).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Generate.genCode_sp v)

end VG.Proof.RsaKeyGen.X86_64.SearchScrub

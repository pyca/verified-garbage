module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCode
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.RandomSignResult

/-! Randomized signing's functional correctness against its shared contract. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem random_sign_shared_post {extra : Nat} {s t : State} (h : RandomSignABI extra s)
    (hp : RandomSignCodePost s (randomSignRemaining (randomInput s) 0 8) t) :
    (Spec.Dsa.randomSignContract abi (extra + 256)).post s t := by
  sig_post [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, abi, argRegs, randomSignStackArgs]
  sig_post [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, abi, argRegs, randomSignStackArgs]
  have he := random_remaining_bytes h
  have hb : (randomSignRemaining (randomInput s) 0 8).status < 2 ^ 32 := by
    have := randomSignLoop_status_le (randomInput s).pLen (randomInput s).qLen 8
      (randomInput s).key (randomInput s).digest ((randomInput s).rand.drop 0)
    change (randomSignRemaining (randomInput s) 0 8).status ≤ 2 at this
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hp.status]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64),
      Nat.mod_eq_of_lt hb]
    exact congrArg Spec.Dsa.RandomSignResult.status he
  · exact (hp.output.trans (congrArg (fun r : Spec.Dsa.RandomSignResult => r.signature.getD
      (List.replicate (s.gpr .x1).toNat 0)) he))
  · change Spec.Rsa.wordsAt t.mem (s.gpr .x2) 1 = _
    simp only [Spec.Rsa.wordsAt, List.range_succ, List.range_zero, List.nil_append,
      List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero, hp.used]
    exact congrArg (fun r : Spec.Dsa.RandomSignResult => [BitVec.ofNat 64 r.used]) he

theorem random_sign_correct (v : Backend) (s : State)
    (hpre : (Spec.Dsa.randomSignContract abi (v.stack + 256)).pre s) :
    ∃ trace t, Exec isa (RandomSign.code (randomSignerName v) (SignVerify.sign v.mul)) s trace t ∧
      abiPreserved s t ∧ (Spec.Dsa.randomSignContract abi (v.stack + 256)).post s t := by
  have h := randomSignABI_of hpre
  obtain ⟨trace, t, he, hp⟩ := random_sign_code v h
  exact ⟨trace, t, he, ⟨hp.callee, hp.sp, hp.vectors⟩, random_sign_shared_post h hp⟩

end VG.Proof.Dsa.AArch64

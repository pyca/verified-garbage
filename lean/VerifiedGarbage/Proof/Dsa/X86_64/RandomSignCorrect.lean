module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCode
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.RandomSignResult
import VerifiedGarbage.Proof.Framework.Offset

/-! Randomized signing's functional correctness against its shared contract. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem random_sign_shared_post {extra : Nat} {s t : State} (h : RandomSignABI extra s)
    (hp : RandomSignCodePost s (randomSignRemaining (randomInput s) 0 8) t) :
    (Spec.Dsa.randomSignContract abi (extra + 256)).post s t := by
  sig_post [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, abi, argRegs, stackArgs_seven]
  sig_post [Spec.Dsa.randomSignContract, Spec.Dsa.randomSignSig, abi, argRegs, stackArgs_seven]
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
      (List.replicate (s.gpr .rsi).toNat 0)) he))
  · change Spec.Rsa.wordsAt t.mem (s.gpr .rdx) 1 = _
    simp only [Spec.Rsa.wordsAt, List.range_succ, List.range_zero, List.nil_append,
      List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero, hp.used]
    exact congrArg (fun r : Spec.Dsa.RandomSignResult => [BitVec.ofNat 64 r.used]) he

theorem random_sign_correct (v : Backend) (s : State)
    (hpre : (Spec.Dsa.randomSignContract abi (v.stack + 256)).pre s) :
    ∃ trace t, Exec isa (RandomSign.code (randomSignerName v) (SignVerify.sign v.sq v.mul)) s trace t ∧
      abiPreserved s t ∧ (Spec.Dsa.randomSignContract abi (v.stack + 256)).post s t := by
  have h := randomSignABI_of hpre
  obtain ⟨trace, t, he, hp⟩ := random_sign_code v h
  refine ⟨trace, t, he, ⟨hp.callee, ?_, hp.mxcsr⟩, random_sign_shared_post h hp⟩
  have hd := random_sign_depth v
  have hb := v.stackBound
  have hf := Exec.stackFrame (SpSafe.of_all (random_sign_sp v)) he (by omega)
  have hfb := VG.X86_64.Frame.below_mono hf hd (by omega)
  apply hfb.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) _ (by decide)
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rw [h.wr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.retOut
    · exact h.retUsed
    · exact h.retScratch
  · simp only [List.mem_singleton] at hr
    subst r
    exact Offset.base_disjoint_below _ (by omega)

end VG.Proof.Dsa.X86_64

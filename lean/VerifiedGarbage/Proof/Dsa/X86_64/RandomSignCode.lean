module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSingle
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignFinishResult
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignInvalid
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignBody
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.Offset

/-! Whole-entry execution, frame restoration, and stack bounds. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem random_sign_sp (S : Signer) :
    (RandomSign.code S.name S.code).all (fun i => !isa.writesSp i) = true := by
  simp only [RandomSign.code, RandomSign.body, RandomSign.attempt, Code.all, Bool.and_eq_true]
  repeat' constructor
  all_goals first | exact S.sp | decide

theorem random_sign_depth (S : Signer) :
    (RandomSign.code S.name S.code).x86_64Depth ≤ S.stack + 256 := by
  simp only [RandomSign.code, RandomSign.body, RandomSign.attempt, Code.x86_64Depth,
    show Random.prepare.x86_64Depth = 0 from rfl,
    show Random.sample.x86_64Depth = 0 from rfl,
    show RandomSign.callFinish.x86_64Depth = 0 from rfl,
    show RandomSign.finish.x86_64Depth = 0 from rfl,
    Nat.zero_max, Nat.max_zero]
  change S.code.x86_64Depth + 8 + 248 ≤ _
  simpa only [Nat.add_assoc] using Nat.add_le_add_right (Nat.add_le_add_right S.depth 8) 248

theorem random_sign_body (S : Signer) {s : State} (h : RandomSignABI S.stack s) (hv : RandomValid S s) :
    WP isa (RandomSign.body S.name S.code)
      (allocState Random.frameBytes s)
      (RandomSignBodyPost s (randomSignRemaining (randomInput s) 0 8)) := by
  by_cases hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)
  · exact random_sign_body_valid S h hq hv
  · exact random_sign_body_invalid S h hq

theorem random_remaining_bytes {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    randomSignRemaining (randomInput s) 0 8 =
      Spec.Dsa.randomSignBytes (randomInput s).pLen (randomInput s).qLen (randomInput s).key
        (randomInput s).digest (randomInput s).rand := by
  simp only [Spec.Dsa.randomSignBytes, randomInput, bytesAt_length, h.lengths, h.keyLength,
    bne_self_eq_false, decide_true, Bool.not_true, Bool.false_or, Bool.false_eq_true, ite_false,
    randomSignRemaining, List.drop_zero]

structure RandomSignCodePost (s : State) (result : Spec.Dsa.RandomSignResult) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  status : t.gpr .rax = BitVec.ofNat 64 result.status
  output : Spec.Rsa.bytesAt t.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
    result.signature.getD (List.replicate (s.gpr .rsi).toNat 0)
  used : t.mem.readW (s.gpr .rdx) 64 = BitVec.ofNat 64 result.used
  callee : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  mxcsr : t.mxcsr.extractLsb' 6 10 = s.mxcsr.extractLsb' 6 10

theorem random_sign_code (S : Signer) {s : State} (h : RandomSignABI S.stack s) (hv : RandomValid S s) :
    WP isa (RandomSign.code S.name S.code) s
      (RandomSignCodePost s (randomSignRemaining (randomInput s) 0 8)) := by
  apply random_frame_ok h
  refine WP.mono (random_sign_body S h hv) fun t ht => ⟨ht.sp, ht.wr, fun m _ fm => ?_⟩
  -- The frame's bytes, once released, hold anything: the output and `used` lie apart from them.
  have hl := h.stackLower
  have hR : Region.Sub ⟨s.gpr .rsp - BitVec.ofNat 64 Random.frameBytes, Random.frameBytes⟩
      (below (s.gpr .rsp) (S.stack + 256)) :=
    Offset.sub_below _ (by unfold Random.frameBytes; omega_using []) (by unfold Random.frameBytes; omega_using [])
  have sep : ∀ {B : Region}, (below (s.gpr .rsp) (S.stack + 256)).Disjoint B →
      ∀ q ∈ [(⟨s.gpr .rsp - BitVec.ofNat 64 Random.frameBytes, Random.frameBytes⟩ : Region)], B.Disjoint q :=
    fun hB q hq => by
      simp only [List.mem_singleton] at hq; subst hq
      exact fun x h₁ h₂ => hB x (hR x h₂) h₁
  refine ⟨ht.rd, by change t.wr.tail = _; rw [ht.wr]; rfl, ht.status, ?_, ?_, ?_, ht.mxcsr⟩
  · show Spec.Rsa.bytesAt m (s.gpr .rdi) (s.gpr .rsi).toNat = _
    rw [Proof.Rsa.rsa_bytes_frame fm (s.gpr .rsi).isLt (sep h.stackOut)]
    exact ht.output
  · show m.readW (s.gpr .rdx) 64 = _
    rw [fm.readW (r := ⟨s.gpr .rdx, 8⟩) (Region.contains_self _ _) (sep h.stackUsed) (by decide)]
    exact ht.used
  intro r hr
  by_cases he : r = .rsp
  · subst r
    change t.gpr .rsp + BitVec.ofNat 64 Random.frameBytes = s.gpr .rsp
    rw [ht.sp, randomBase, BitVec.sub_add_cancel]
  · change (t.setReg .rsp (t.gpr .rsp + BitVec.ofNat 64 Random.frameBytes)).gpr r = _
    simp only [State.setReg, ite_eq_right he]
    exact ht.callee r hr he

end VG.Proof.Dsa.X86_64

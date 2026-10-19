module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Decrypt
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Word32
public import VerifiedGarbage.Proof.Bignum.X86.ByteOps

/-! # A public mask-building step doubles the mask and tests its bound -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86.Dec
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Enc.X86.Decrypt

theorem maskBody_ok {s : State} {m x : Nat}
    (ax : s.gpr .eax = BitVec.ofNat 32 m) (cx : s.gpr .ecx = BitVec.ofNat 32 x)
    (maskBound : 2 * m + 1 < 2 ^ 31) (valueBound : x < 2 ^ 31) :
    WP isa (.block maskBody) s fun t => t.mem = s.mem ∧ Keeps [.eax, .edx] s t ∧
      t.gpr .eax = BitVec.ofNat 32 (2 * m + 1) ∧
      t.zf = some (!decide (2 * m + 1 < x)) := by
  unfold maskBody
  refine wp_addS rfl fun a A _ => ?_
  refine wp_addS rfl fun b B _ => ?_
  refine wp_movS rfl fun c C _ => ?_
  refine wp_subS rfl fun d D _ => ?_
  refine wp_shr (by decide) fun e E _ => ?_
  have value : b.gpr .eax = BitVec.ofNat 32 (2 * m + 1) := by
    rw [B.gpr, A.gpr, ax]
    change (BitVec.ofNat 32 m + BitVec.ofNat 32 m) + BitVec.ofNat 32 1 = _
    simp only [← BitVec.ofNat_add]
    congr 1
    omega
  have test : e.gpr .edx = if 2 * m + 1 < x then 1 else 0 := by
    rw [E.gpr, D.gpr, C.gpr, C.other .ecx (by decide), B.other .ecx (by decide),
      A.other .ecx (by decide), cx, value]
    exact Word32.top_sub maskBound valueBound
  refine wp_cmpS rfl fun t T Z => WP.block_nil ?_
  have K : Keeps [.eax, .edx] s t := (A.keeps.mono (by decide)).trans
    ((B.keeps.mono (by decide)).trans ((C.keeps.mono (by decide)).trans
      ((D.keeps.mono (by decide)).trans ((E.keeps.mono (by decide)).trans (T.keeps _)))))
  refine ⟨T.mem.trans (E.mem.trans (D.mem.trans (C.mem.trans (B.mem.trans A.mem)))), K, ?_, ?_⟩
  · rw [congrFun T.gpr .eax, E.other .eax (by decide), D.other .eax (by decide), C.other .eax (by decide), value]
  · rw [test] at Z
    by_cases bound : 2 * m + 1 < x
    · simpa only [bound, ite_true, decide_true, Bool.not_true, show ((1 : BitVec 32) - 0 == 0) = false by decide] using Z
    · simpa only [bound, ite_false, decide_false, Bool.not_false, show ((0 : BitVec 32) - 0 == 0) = true by decide] using Z

end VG.Proof.RsaPkcs1Enc.X86.Dec

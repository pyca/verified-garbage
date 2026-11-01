module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifySpec
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyStackWord
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeDispatch
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Weierstrass.PointContract

/-! # Reject signatures whose public byte count differs from the modulus width -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Sig.X86.Verify

theorem lengthCheck_ok {g : Geometry} {bs : Fin 5 → List Byte} {s : State} (h : Context g bs s) :
    WP isa (.block lenCheck) s fun t => Context g bs t ∧ t.mem = s.mem ∧ Keeps [.eax] s t ∧
      t.zf = some (decide (g.signatureLength = g.length)) := by
  unfold lenCheck incoming stackAt
  refine wp_ldm rfl (h.readArg (by decide : 8 < 13)) fun a A => ?_
  have ha := h.after (by rw [A.mem]; exact Frame.refl _ _) A.keeps (A.other .esp (by decide))
  have load : readSrc a (.mem ⟨.esp, VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 20 + 4 * 1⟩) = some (g.argument 1) := by
    change a.load32 (addr (a.gpr .esp) (VG.Impl.RsaPkcs1Sig.X86.Verify.frameBytes + 20 + 4 * 1)) = _
    rw [State.load32, ite_eq_left (ha.readArg (by decide : 1 < 13)), ha.argumentValue (by decide : 1 < 13)]
  refine wp_cmpS load fun t T Z => WP.block_nil ?_
  have K : Keeps [.eax] s t := A.keeps.trans (T.keeps _)
  have M := T.mem.trans A.mem
  refine ⟨h.after (by rw [M]; exact Frame.refl _ _) K (K.1 .esp (by decide)), M, K, ?_⟩
  rw [Z, A.gpr, h.argumentValue (by decide : 8 < 13)]
  change some (BitVec.ofNat 32 g.signatureLength - BitVec.ofNat 32 g.length == 0) = _
  rw [sub_beq32]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro eq
    have := congrArg BitVec.toNat eq
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h.valid.signatureBound,
      Nat.mod_eq_of_lt (by have := h.valid.maxLength; omega : g.length < 2 ^ 32)] using this
  · intro eq; rw [eq]

theorem verifiedResult_bad {g : Geometry} {bs : Fin 5 → List Byte} {s : State}
    (h : Context g bs s) (different : g.signatureLength ≠ g.length) : verifiedResult g bs = 0 := by
  have diff : (bs 3).length ≠ (bs 0).length := by
    rw [(h.sources 0).length, (h.sources 3).length]
    exact different
  unfold verifiedResult Spec.RsaPkcs1Sig.verifyId
  cases Spec.RsaPkcs1Sig.Hash.ofId g.hash.toNat with
  | none => rfl
  | some hv => simp only [Spec.RsaPkcs1Sig.verify, diff, false_and, ite_false, Bool.false_eq_true]

end VG.Proof.RsaPkcs1Sig.X86.Ver

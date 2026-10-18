module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.EncodeMessageCopy
public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Encode

/-! # Copy a public-length message, including the empty-message case -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Enc.X86
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.RsaPkcs1Sig.X86
open VG.Impl.RsaPkcs1Enc.X86

theorem message_ok {s0 s : State} {p : BitVec 32} {k n : Nat} {acc : List Byte}
    (buf : Buf s0 k) (hk : k ≤ 1024) (input : MessageSource s0 p k n)
    (bound : acc.length + n ≤ k) (h : W s0 acc s) (source : s.gpr .esi = p)
    (count : s.gpr .ebp = BitVec.ofNat 32 n) :
    WP isa message s fun t => W s0 (acc ++ Spec.Rsa.bytesAt s0.mem (byteAddr p) n) t ∧
      t.gpr .ebx = s.gpr .ebx := by
  unfold message
  refine WP.seq ?_
  refine wp_cmpS rfl fun u U Z => WP.block_nil ?_
  by_cases empty : n = 0
  · refine WP.ite true (by simp [eval, Z, count, empty]) (fun _ => WP.block_nil ?_) (by simp)
    subst n
    exact ⟨by simpa [Spec.Rsa.bytesAt] using h.after (U.keeps ([] : List Reg)) (by simp) U.mem (congrFun U.gpr .edi), congrFun U.gpr .ebx⟩
  · have flag : u.zf = some false := by
      rw [Z, count]
      have nz : BitVec.ofNat 32 n ≠ 0#32 := by
        intro eq
        have same := congrArg BitVec.toNat eq
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ 32 by omega)] at same
        exact empty same
      rw [show BitVec.ofNat 32 n - 0 = BitVec.ofNat 32 n from BitVec.sub_zero _]
      exact congrArg some (beq_eq_false_iff_ne.mpr nz)
    refine WP.ite false (by simp [eval, flag]) (by simp) (fun _ => ?_)
    refine WP.mono (messageCopy_ok buf hk input (by omega) bound
      (h.after (U.keeps ([] : List Reg)) (by simp) U.mem (congrFun U.gpr .edi))
      ((congrFun U.gpr .esi).trans source) ((congrFun U.gpr .ebp).trans count)) ?_
    rintro t ⟨ht, hb⟩
    exact ⟨ht, hb.trans (congrFun U.gpr .ebx)⟩

end VG.Proof.RsaPkcs1Enc.X86

module

public import VerifiedGarbage.Proof.Bignum.X86.PublicInputs
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Bignum.X86.PublicImport
import VerifiedGarbage.Proof.Bignum.X86.PublicApply
import VerifiedGarbage.Proof.Bignum.X86.PublicExport
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86.PublicLayout
import VerifiedGarbage.Proof.Bignum.MemoryFrame

/-! # Complete checked public arithmetic for the selected modulus width -/

@[expose] public section
namespace VG.Proof.Bignum.X86.PublicContext
open VG VG.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.PublicContext
open VG.Proof.Mont VG.Proof.Mont.X86

def PublicResult (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (mem : Mem) (e : Nat)
    (t : State) : Prop :=
  let m := Spec.Rsa.os2ip (Spec.Rsa.bytesAt mem (byteAddr (args 2)) len)
  let x := Spec.Rsa.os2ip (Spec.Rsa.bytesAt mem (byteAddr (args 6)) len)
  Spec.Rsa.bytesAt t.mem (byteAddr (args 0)) len = Spec.Rsa.i2osp (if x < m then x ^ e % m else 0) len ∧
  t.gpr .eax = BitVec.ofNat 32 (decide (x < m)).toNat ∧
  Frame [⟨off base 16, bytes - 16⟩, ⟨byteAddr (args 0), len⟩] mem t.mem

theorem publicSized_ok {s : State} {base : Addr} {bytes len e : Nat} {args : Nat → BitVec 32}
    (h : PublicInputs base bytes len args s)
    (valid : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)) len = true)
    (exponent : val32 s.mem base 128 2 = e) :
    WP isa (PublicFn.sized (Spec.Rsa.modulusWords len)) s fun t =>
      let m := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)
      let x := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 6)) len)
      Spec.Rsa.bytesAt t.mem (byteAddr (args 0)) len = Spec.Rsa.i2osp (if x < m then x ^ e % m else 0) len ∧
      t.gpr .eax = BitVec.ofNat 32 (decide (x < m)).toNat ∧
      Frame [⟨off base 16, bytes - 16⟩, ⟨byteAddr (args 0), len⟩] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have dims := h.dimensions
  have facts := valid_facts valid h.lower
  have nw := h.scratch.nowrap
  have space := h.space
  have sz := size_eq (Spec.Rsa.modulusWords len)
  have modFit : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len) < 2 ^ (8 * len) := by
    have B := os2ip_lt (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len)
    simpa only [bytesAt_length, pow256_eq] using B
  unfold PublicFn.sized
  refine WP.seq (WP.mono (importNumbers_ok h.scratch dims.1 h.space (by have := h.lower; omega) dims.2.2
    (h.stack 2 (by decide)) (by rw [← h.nLen]; exact h.stack 3 (by decide))
    (h.stack 6 (by decide)) (by rw [← h.inLen]; exact h.stack 7 (by decide))
    h.nFit h.inFit h.nRead h.inRead h.nApart h.inApart)
    fun u ⟨N, X, O, K⟩ => ?_)
  have O' : Outside base 0 bytes s.mem u.mem := O.mono (by omega) (by omega)
  have hu := h.keep K (by decide) (by decide) O'
  have eu : val32 u.mem base 128 2 = e := by
    rw [O.val32 (.inl (by decide)) (by decide), exponent]
  refine WP.seq (WP.mono (acceptAndPower_ok hu.scratch dims.1 dims.2.1 h.space N X eu facts.2.1 facts.1)
    fun v ⟨C, Y, Mask, Ov, Kv⟩ => ?_)
  have Osv : Outside base 16 (bytes - 16) s.mem v.mem :=
    (O.mono (by omega) (by omega)).trans Ov
  have Ksv : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v := K.trans (Kv.mono (by decide))
  have hv := h.keep Ksv (by decide) (by decide) (Osv.mono (by omega) (by omega))
  refine WP.mono (exportResult_ok hv.scratch dims.1 h.space (by have := h.lower; omega) dims.2.2 Y
    (Nat.lt_trans (Nat.mod_lt _ (by omega)) modFit)
    (decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 6)) len) <
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len))) (by simpa only [decide_eq_true_eq] using Mask)
    (hv.stack 0 (by decide)) (by rw [← h.outLen]; exact hv.stack 1 (by decide))
    h.outFit hv.outWrite h.outApart) fun t ⟨R, B, F, T⟩ => ?_
  refine ⟨by simpa only [decide_eq_true_eq] using R, B, ?_, Ksv.trans T⟩
  exact ((outside_frame Osv (by omega)).mono (by simp)).trans F

end VG.Proof.Bignum.X86.PublicContext

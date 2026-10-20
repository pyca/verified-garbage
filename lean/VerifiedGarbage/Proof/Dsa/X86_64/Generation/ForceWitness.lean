module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.ForceWitness
import VerifiedGarbage.Proof.Dsa.Generation.WitnessMemory
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Bignum.X86_64.Words
import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.TCB.X86_64.State

/-! # Native forced-witness byte transformation -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

theorem forceWitness_ok {s : State} {op : Addr} {len : Nat}
    (hlen : 2 ≤ len) (hmax : len < 2 ^ 32) (hop : s.gpr .rdi = op)
    (hrd : ∀ i < len, InRegions (s.rd ++ s.wr) (off op i) 1)
    (hwr : ∀ i < len, InRegions s.wr (off op i) 1) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.forceWitness len)) s fun t =>
      t.mem = (s.mem.writeW op (s.mem op &&& (127 : Byte))).writeW
        (off op (len - 1)) (s.mem (off op (len - 1)) ||| (2 : Byte)) ∧ Keep [.rax] s t := by
  have hne : off op (len - 1) ≠ op := by
    intro he
    have hv : BitVec.ofNat 64 (len - 1) = 0#64 := by
      have he' := congrArg (fun x => x - op) he
      simpa only [off, Offset.add_sub_cancel_left, BitVec.sub_self] using he'
    have := congrArg BitVec.toNat hv
    change (len - 1) % 2 ^ 64 = 0 at this
    omega
  have hr0 := hrd 0 (by omega)
  have hw0 := hwr 0 (by omega)
  have hrn := hrd (len - 1) (by omega)
  have hwn := hwr (len - 1) (by omega)
  simp only [off, BitVec.add_zero] at hr0 hw0 hrn hwn hne
  refine WP.keep [.rax] ?_ rfl
  xrun [Impl.Dsa.X86_64.Generation.forceWitness, State.ea, hop, off,
    BitVec.ofInt_natCast, show BitVec.ofInt 64 0 = 0#64 by rfl, BitVec.add_zero, hr0, hw0, hrn, hwn, WriteBytes.writeW8_apply, hne]

  simp [BitVec.setWidth_and, BitVec.setWidth_or]

/-- The native transformation implements the forced branch of the shared
RSA sampler, with all memory outside the witness buffer preserved. -/
theorem forceWitness_spec {s : State} {op : Addr} {len w : Nat}
    (hlen : 2 ≤ len) (hmax : len < 2 ^ 32) (hop : s.gpr .rdi = op)
    (hrd : ∀ i < len, InRegions (s.rd ++ s.wr) (off op i) 1)
    (hwr : ∀ i < len, InRegions s.wr (off op i) 1)
    (hbits : Spec.RsaKeyGen.bitLength (w - 1) = 8 * len)
    (hbad : ¬ (2 ≤ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem op len) ∧
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem op len) < w - 1)) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.forceWitness len)) s fun t =>
      Spec.RsaKeyGen.witness (w - 1) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem op len)) =
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem op len), false) ∧
      (∀ a, (∀ i < len, a ≠ off op i) → t.mem a = s.mem a) ∧ Keep [.rax] s t := by
  refine WP.mono (forceWitness_ok hlen hmax hop hrd hwr) fun t ⟨hm, hk⟩ => ?_
  refine ⟨?_, ?_, hk⟩
  · rw [hm, VG.Proof.Dsa.Generation.forcedWitness_memory s.mem op hlen (by omega)]
    exact VG.Proof.Dsa.Generation.forcedWitnessBytes_spec
      (by simpa only [bytesAt_length] using hlen) (by simpa only [bytesAt_length] using hbits) hbad
  · intro a ha
    have hzero : a ≠ op := by simpa only [off, BitVec.add_zero] using ha 0 (by omega)
    rw [hm, WriteBytes.writeW8_apply, ite_eq_right (ha (len - 1) (by omega)),
      WriteBytes.writeW8_apply, ite_eq_right hzero]

end VG.Proof.Dsa.X86_64.Generation

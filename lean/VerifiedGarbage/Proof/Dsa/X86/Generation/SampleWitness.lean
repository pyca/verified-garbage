module
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Dsa.X86.Generation.SampleWitness
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleLayout
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleForce
import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleHead
import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleSpec

/-! # The complete native sampler returns RSA's witness and uniformity flag -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Generation
open VG.Proof.Ecdsa.X86

theorem sampleWitness_ok {s : State} {base : Addr} {size n m len : Nat} {p : BitVec 32}
    (C : Context n m base size s) (width : n ≤ 48) (room : primeIsUniform + 4 ≤ size)
    (one : wordsVal s.mem base (slot n 3) n = 1) (ndef : n = (len + 7) / 8)
    (h4 : 4 ≤ len) (hw4 : len % 4 = 0) (hp : s.gpr .esi = p) (fit : p.toNat + len ≤ 2 ^ 32)
    (bits : Spec.RsaKeyGen.bitLength (m - 1) = 8 * len)
    (read4 : ∀ d, d + 4 ≤ len → InRegions (s.rd ++ s.wr) (off (p.setWidth 64) d) 4)
    (read1 : ∀ i < len, InRegions (s.rd ++ s.wr) (off (p.setWidth 64) i) 1)
    (write : ∀ i < len, InRegions s.wr (off (p.setWidth 64) i) 1)
    (apart : Region.Disjoint ⟨p.setWidth 64, len⟩ ⟨base, size⟩) :
    WP isa (sampleWitness len) s fun t =>
      let witness := Spec.RsaKeyGen.witness (m - 1) (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (p.setWidth 64) len))
      Context n m base size t ∧ wordsVal t.mem base (slot n 5) n = witness.1 ∧
      t.mem.readW (off base primeIsUniform) 32 = mask32 (witness.2 = true) ∧
      Frame (sampleWrites base n (p.setWidth 64) len) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  let bs := Spec.Rsa.bytesAt s.mem (p.setWidth 64) len
  let x := Spec.Dsa.decodeBE bs
  have bslen : bs.length = len := by simp only [bs, Spec.Rsa.bytesAt, List.length_map, List.length_range]
  have bbits : Spec.RsaKeyGen.bitLength (m - 1) = 8 * bs.length := by rw [bslen]; exact bits
  unfold sampleWitness
  dsimp only
  rw [← ndef]
  refine WP.seq (WP.mono (sampleHead_ok C width room one ndef h4 hw4
    (by rw [hp]; exact fit) (fun d hd => by rw [hp]; exact read4 d hd) (by rw [hp]; exact apart))
    fun a ⟨Ca, value, flag, zf, bytes, Oa, Ka⟩ => ?_)
  rw [hp] at value flag zf bytes
  change wordsVal a.mem base (slot n 5) n = x at value
  change a.mem.readW (off base primeIsUniform) 32 = mask32 (2 ≤ x ∧ x < m - 1) at flag
  change a.zf = some (decide (¬ (2 ≤ x ∧ x < m - 1))) at zf
  have Fa : Frame (sampleWrites base n (p.setWidth 64) len) s.mem a.mem :=
    Oa.mono (by intro r hr; exact List.mem_append_left _ hr)
  by_cases good : 2 ≤ x ∧ x < m - 1
  · refine WP.ite false (by simp [eval, zf, good]) (fun e => Bool.noConfusion e) (fun _ => WP.block_nil ?_)
    have spec := sample_spec_good bbits good
    change Context n m base size a ∧ wordsVal a.mem base (slot n 5) n = (Spec.RsaKeyGen.witness (m - 1) x).1 ∧
      a.mem.readW (off base primeIsUniform) 32 = mask32 ((Spec.RsaKeyGen.witness (m - 1) x).2 = true) ∧ _
    rw [spec]
    exact ⟨Ca, value, by rw [flag]; simp [mask32, good], Fa, Ka⟩
  · refine WP.ite true (by simp [eval, zf, good]) (fun _ => ?_) (fun e => Bool.noConfusion e)
    have pa : a.gpr .esi = p := (Ka.1 _ (by decide)).trans hp
    refine WP.mono (sampleForce_ok Ca pa h4 (by omega) hw4 fit
      (fun d hd => by rw [Ka.2.1, Ka.2.2]; exact read4 d hd)
      (fun i hi => by rw [Ka.2.1, Ka.2.2]; exact read1 i hi)
      (fun i hi => by rw [Ka.2.2]; exact write i hi) apart) fun t ⟨Ct, vt, Ot, Kt⟩ => ?_
    have flagSame : t.mem.readW (off base primeIsUniform) 32 = a.mem.readW (off base primeIsUniform) 32 := by
      apply Ot.readW (Region.contains_self _ 4) ?_ (by decide)
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact apart.symm.sub_left (Offset.sub_base _ room)
      · exact Offset.disjoint base (by simp only [slot, stride, primeIsUniform]; omega)
          (by decide) (by simp only [slot, stride]; omega)
    have spec := sample_spec_bad (by rw [bslen]; omega) bbits good
    change Context n m base size t ∧ wordsVal t.mem base (slot n 5) n = (Spec.RsaKeyGen.witness (m - 1) x).1 ∧
      t.mem.readW (off base primeIsUniform) 32 = mask32 ((Spec.RsaKeyGen.witness (m - 1) x).2 = true) ∧ _
    rw [spec]
    refine ⟨Ct, by rw [vt, bytes], by rw [flagSame, flag]; simp only [mask32, good, ite_false, Bool.false_eq_true], ?_, Ka.trans (Kt.mono (by decide))⟩
    apply Fa.trans (Ot.mono ?_)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp [sampleWrites, sampleArithmeticWrites]
end VG.Proof.Dsa.X86.Generation

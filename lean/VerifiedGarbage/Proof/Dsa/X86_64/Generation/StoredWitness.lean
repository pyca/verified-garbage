module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.StoredWitness
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ForceWitness
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Prepared
public import VerifiedGarbage.Proof.Dsa.Generation.WitnessBytes
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Dsa.Generation.WitnessMemory
import VerifiedGarbage.Proof.Bignum.ExternalWords
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! # A forced witness preserves all prepared modulus data -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate

theorem forceStoredWitness_ok {s : State} {B p : Addr} {Z w N sp len : Nat} {mi : BitVec 64}
    (h : ModulusReady s B Z w mi N) (hd : MrDims B Z w)
    (hsp : sp < 32) (hp : word s.mem B (8 * sp) = p)
    (hlen : 2 ≤ len) (hmax : len < 2 ^ 32)
    (hwr : ∀ i < len, InRegions s.wr (off p i) 1)
    (hsep : ∀ i < len, Z ≤ ofs B (off p i)) :
    WP isa (Impl.Dsa.X86_64.Generation.forceStoredWitness sp len) s fun t =>
      ModulusReady t B Z w mi N ∧
      Spec.Rsa.bytesAt t.mem p len = VG.Proof.Dsa.Generation.forcedWitnessBytes (Spec.Rsa.bytesAt s.mem p len) ∧
      (∀ a, (∀ i < len, a ≠ off p i) → t.mem a = s.mem a) ∧
      (∀ d, d + 8 ≤ Z → word t.mem B d = word s.mem B d) ∧ Keep [.rax, .rbx] s t := by
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * sp)) 8 :=
    h.good.scr.ld (by have := hdr_lt_slot w 8 hsp; have := hd.z; omega)
  unfold Impl.Dsa.X86_64.Generation.forceStoredWitness
  simp only [seqs]
  refine WP.seq (WP.mono (WP.keep [.rbx, .rdi] (Q := fun u =>
      u.gpr .rbx = B ∧ u.gpr .rdi = p ∧ u.mem = s.mem) (by
        xrun [State.ea, hdr, hdrOff, h.good.rdi, hl, hp]) rfl) fun u ⟨⟨hbx, hdi, hm⟩, ku⟩ => ?_)
  have hwu : ∀ i < len, InRegions u.wr (off p i) 1 := fun i hi => by rw [ku.2.2]; exact hwr i hi
  have hru : ∀ i < len, InRegions (u.rd ++ u.wr) (off p i) 1 := fun i hi => by
    obtain ⟨r, hr, hc⟩ := hwu i hi
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.seq (WP.mono (forceWitness_ok hlen hmax hdi hru hwu) fun v ⟨hmv, kv⟩ => ?_)
  refine WP.mono (WP.keep [.rdi] (Q := fun t => t.gpr .rdi = B ∧ t.mem = v.mem) (by
    xrun [(kv.gpr (by decide) : v.gpr .rbx = u.gpr .rbx).trans hbx]) rfl) fun t ⟨⟨hdit, hmt⟩, kt⟩ => ?_
  have k := (ku.trans kv).trans kt
  have hmfinal : t.mem = (s.mem.writeW p (s.mem p &&& (127 : Byte))).writeW
      (off p (len - 1)) (s.mem (off p (len - 1)) ||| (2 : Byte)) := by rw [hmt, hmv, hm]
  have hf : ∀ a, (∀ i < len, a ≠ off p i) → t.mem a = s.mem a := by
    intro a ha
    have hzero : a ≠ p := by simpa only [off, BitVec.add_zero] using ha 0 (by omega)
    rw [hmfinal, WriteBytes.writeW8_apply, ite_eq_right (ha (len - 1) (by omega)),
      WriteBytes.writeW8_apply, ite_eq_right hzero]
  have hwords := VG.Proof.Bignum.words_outside_bytes (by have := h.good.scr.nowrap; omega : Z ≤ 2 ^ 64) hf hsep
  refine ⟨h.of_words hd hwords k.2.2 hdit, ?_, hf, hwords, ?_⟩
  · rw [hmfinal, VG.Proof.Dsa.Generation.forcedWitness_memory s.mem p hlen (by omega)]
  · refine ⟨fun r hr => ?_, k.2⟩
    by_cases he : r = .rdi
    · subst r; exact hdit.trans h.good.rdi.symm
    · exact k.gpr (by simpa [he, and_comm] using hr)

end VG.Proof.Dsa.X86_64.Generation

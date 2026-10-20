module
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.WitnessCut
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.CutOctets
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Spec.Rsa.Contract

import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CutByte
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Copy
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! # FFDH parameter candidates on x86-64: the complete masked witness draw -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.ParameterCandidate

theorem witnessCut_ok {s : State} {rp op : Addr} {bs : List Byte} {bits : Nat}
    (hb1 : 16 ≤ bits) (hb2 : bits ≤ 8192) (hlen : bs.length = (bits + 7) / 8)
    (hrp : s.gpr .rsi = rp) (hop : s.gpr .rdi = op)
    (hn : s.gpr .rcx = BitVec.ofNat 64 bs.length) (hbits : s.gpr .rdx = BitVec.ofNat 64 bits)
    (hrd : ∀ i < bs.length, InRegions (s.rd ++ s.wr) (off rp i) 1)
    (hwr : ∀ i < bs.length, InRegions s.wr (off op i) 1)
    (hbytes : ∀ i < bs.length, s.mem (off rp i) = bs.getD i 0)
    (hsep : ∀ i < bs.length, ∀ l < bs.length, off rp i ≠ off op l) :
    WP isa witnessCut s fun t =>
      Spec.Rsa.bytesAt t.mem op bs.length = cutOctets bs ((bits - 1) % 8) ∧
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem op bs.length) = Spec.Rsa.os2ip bs % 2 ^ bits ∧
      (∀ a, (∀ i < bs.length, a ≠ off op i) → t.mem a = s.mem a) ∧
      Keep [.rax, .rdx, .r8, .r9, .r10, .r11, .rcx] s t := by
  have hl1 : 2 ≤ bs.length := by omega
  have hl2 : bs.length < 2 ^ 31 := by omega
  have hj : (bits - 1) % 8 < 8 := Nat.mod_lt _ (by decide)
  have hne : bs ≠ [] := by intro he; simp [he] at hl1
  have hcut := cutOctets_length hne ((bits - 1) % 8)
  have h0 : 0 < bs.length := by omega
  unfold witnessCut
  simp only [seqs]
  refine WP.seq (WP.mono (cutMasks_ok (by omega) (by omega) hbits) fun u₁ ⟨hm₁, hh₁, hmem₁, k₁⟩ => ?_)
  have hrd₁ : InRegions (u₁.rd ++ u₁.wr) rp 1 := by rw [k₁.2.1, k₁.2.2]; simpa [off] using hrd 0 h0
  have hwr₁ : InRegions u₁.wr op 1 := by rw [k₁.2.2]; simpa [off] using hwr 0 h0
  have hb₁ : u₁.mem rp = bs.getD 0 0 := by rw [hmem₁]; simpa [off] using hbytes 0 h0
  refine WP.seq (WP.mono (firstByte_cut_ok hl1 hl2 ((k₁.gpr (by decide)).trans hrp)
    ((k₁.gpr (by decide)).trans hop) ((k₁.gpr (by decide)).trans hn) hm₁ hh₁ hrd₁ hwr₁ hb₁)
    fun u₂ ⟨hmem₂, hp₂, ho₂, hn₂, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  have hrds : ∀ i < bs.length, InRegions (u₂.rd ++ u₂.wr) (off rp i) 1 :=
    fun i hi => by rw [k12.2.1, k12.2.2]; exact hrd i hi
  have hwrs : ∀ i < bs.length, InRegions u₂.wr (off op i) 1 :=
    fun i hi => by rw [k12.2.2]; exact hwr i hi
  have hbs : ∀ i < bs.length, u₂.mem (off rp i) = bs.getD i 0 := by
    intro i hi
    have hs : off rp i ≠ op := by simpa [off] using hsep i hi 0 h0
    rw [hmem₂, WriteBytes.writeW8_apply, ite_eq_right hs, hmem₁]
    exact hbytes i hi
  have hfirst : u₂.mem op = ((bs.getD 0 0) &&& BitVec.ofNat 8 (2 ^ ((bits - 1) % 8 + 1) - 1)) := by
    rw [hmem₂, WriteBytes.writeW8_apply, ite_eq_left rfl]
  refine WP.mono (copyTailLoop_ok hl1 hl2 hp₂ ho₂ hn₂ hfirst hrds hwrs hbs hsep) fun t ht => ?_
  have he : Spec.Rsa.bytesAt t.mem op bs.length = cutOctets bs ((bits - 1) % 8) := by
    apply List.ext_getElem
    · rw [bytesAt_length]; exact hcut.symm
    · intro i hi hi'
      have hil : i < bs.length := by rwa [bytesAt_length] at hi
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
      change t.mem (off op i) = (cutOctets bs ((bits - 1) % 8))[i]
      have hb := ht.bytes i hil
      have hci : i < (cutOctets bs ((bits - 1) % 8)).length := by rw [hcut]; exact hil
      change t.mem (off op i) = (cutOctets bs ((bits - 1) % 8)).getD i 0 at hb
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hci, Option.getD_some] using hb
  refine ⟨he, ?_, ?_, (k12.trans ht.keep).mono (by decide)⟩
  · rw [he, cutOctets_value (bits := bits) hne hj (by omega)]
  · intro a ha
    have hx : a ≠ op := by simpa [off] using ha 0 h0
    rw [ht.frame a ha, hmem₂, WriteBytes.writeW8_apply, ite_eq_right hx, hmem₁]

end VG.Proof.Ffdh.X86_64.ParameterCandidate

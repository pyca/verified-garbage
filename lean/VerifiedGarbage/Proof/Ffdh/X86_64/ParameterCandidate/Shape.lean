module

public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Shape
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ShapeOctets
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Spec.Rsa.Contract

import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Copy
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ShapeByte
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Masks
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.Words
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
/-! # FFDH parameter candidates on x86-64: complete shaping and its buffer frame -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/ParameterCandidate/LowByte.lean`, which only this module imported.
section

/-! # FFDH parameter candidates on x86-64: make p odd -/

section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.ParameterCandidate

theorem setLow_ok {s : State} {op : Addr} {len : Nat} {b : Byte}
    (hk1 : 1 ≤ len) (hk : len < 2 ^ 31) (hp : s.gpr .r11 = off op len)
    (hrd : InRegions (s.rd ++ s.wr) (off op (len - 1)) 1) (hwr : InRegions s.wr (off op (len - 1)) 1)
    (hb : s.mem (off op (len - 1)) = b) :
    WP isa (.block setLow) s fun t => t.mem = s.mem.writeW (off op (len - 1)) (b ||| 1) ∧ Keep [.rax] s t := by
  have hsub : BitVec.ofNat 64 len + BitVec.ofInt 64 (-1) = BitVec.ofNat 64 (len - 1) := by
    rw [BitVec.ofInt_neg]
    change BitVec.ofNat 64 len + -(1 : BitVec 64) = _
    rw [BitVec.add_neg_eq_sub]
    exact ofNat64_pred hk1 (by omega)
  have he : off op len + BitVec.ofInt 64 (-1) = off op (len - 1) := by
    simp only [off, BitVec.add_assoc, hsub]
  have hbyte : (b.setWidth 64 ||| 1).setWidth 8 = b ||| 1 := by simp [BitVec.setWidth_or]
  exact WP.keep [.rax] (by unfold setLow; xrun [State.ea, hp, he, hrd, hwr, hb, hbyte]) rfl

end VG.Proof.Ffdh.X86_64.ParameterCandidate
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.ParameterCandidate

theorem shape_ok {s : State} {rp op : Addr} {bs : List Byte} {bits : Nat}
    (hb1 : 9 ≤ bits) (hb2 : bits ≤ 8192) (hlen : bs.length = (bits + 7) / 8)
    (hrp : s.gpr .rsi = rp) (hop : s.gpr .rdi = op)
    (hn : s.gpr .rcx = BitVec.ofNat 64 bs.length) (hbits : s.gpr .rdx = BitVec.ofNat 64 bits)
    (hrd : ∀ i < bs.length, InRegions (s.rd ++ s.wr) (off rp i) 1)
    (hwr : ∀ i < bs.length, InRegions s.wr (off op i) 1)
    (hbytes : ∀ i < bs.length, s.mem (off rp i) = bs.getD i 0)
    (hsep : ∀ i < bs.length, ∀ l < bs.length, off rp i ≠ off op l) :
    WP isa shape s fun t =>
      Spec.Rsa.bytesAt t.mem op bs.length = shapedOctets bs ((bits - 1) % 8) ∧
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem op bs.length) = VG.Spec.Ffdh.candidateOf bits (Spec.Rsa.os2ip bs) ∧
      (∀ a, (∀ i < bs.length, a ≠ off op i) → t.mem a = s.mem a) ∧
      Keep [.rax, .rdx, .r8, .r9, .r10, .r11, .rcx] s t := by
  have hl1 : 2 ≤ bs.length := by omega
  have hl2 : bs.length < 2 ^ 31 := by omega
  have hj : (bits - 1) % 8 < 8 := Nat.mod_lt _ (by decide)
  have hne : bs ≠ [] := by intro he; simp [he] at hl1
  have htop := topCut_length hne ((bits - 1) % 8)
  have hshaped := (lastOne_length (bs := topCut bs ((bits - 1) % 8)) (by simp [topCut])).trans htop
  have h0 : 0 < bs.length := by omega
  have hlast : bs.length - 1 < bs.length := by omega
  unfold shape
  simp only [seqs]
  refine WP.seq (WP.mono (shapeMasks_ok (by omega) (by omega) hbits) fun u₁ ⟨hm₁, hh₁, hmem₁, k₁⟩ => ?_)
  have hrd₁ : InRegions (u₁.rd ++ u₁.wr) rp 1 := by rw [k₁.2.1, k₁.2.2]; simpa [off] using hrd 0 h0
  have hwr₁ : InRegions u₁.wr op 1 := by rw [k₁.2.2]; simpa [off] using hwr 0 h0
  have hb₁ : u₁.mem rp = bs.getD 0 0 := by rw [hmem₁]; simpa [off] using hbytes 0 h0
  refine WP.seq (WP.mono (firstByte_ok hl1 hl2 hj ((k₁.gpr (by decide)).trans hrp)
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
  have hfirst : u₂.mem op = topByte ((bits - 1) % 8) (bs.getD 0 0) := by
    rw [hmem₂, WriteBytes.writeW8_apply, ite_eq_left rfl]
  refine WP.seq (WP.mono (copyLoop_ok hl1 hl2 hp₂ ho₂ hn₂ hfirst hrds hwrs hbs hsep) fun u₃ ht => ?_)
  have hwr₃ : InRegions u₃.wr (off op (bs.length - 1)) 1 := by
    rw [ht.keep.2.2]; exact hwrs _ hlast
  have hrd₃ : InRegions (u₃.rd ++ u₃.wr) (off op (bs.length - 1)) 1 :=
    let ⟨r, hr, hc⟩ := hwr₃; ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (setLow_ok (by omega) hl2 ht.ptrO hrd₃ hwr₃ (ht.bytes _ hlast))
    fun t ⟨hmem, k⟩ => ?_
  have he : Spec.Rsa.bytesAt t.mem op bs.length = shapedOctets bs ((bits - 1) % 8) := by
    apply List.ext_getElem
    · rw [bytesAt_length]; exact hshaped.symm
    · intro i hi hi'
      have hil : i < bs.length := by rwa [bytesAt_length] at hi
      have hit : i < (topCut bs ((bits - 1) % 8)).length := by rw [htop]; exact hil
      have hg : (shapedOctets bs ((bits - 1) % 8)).getD i 0 = (shapedOctets bs ((bits - 1) % 8))[i] := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
      change t.mem (off op i) = _
      rw [← hg, shapedOctets, lastOne_getD hit, htop, hmem, WriteBytes.writeW8_apply]
      by_cases hx : i + 1 = bs.length
      · have hi0 : i = bs.length - 1 := by omega
        rw [ite_eq_left hx, hi0, ite_eq_left rfl]
        rfl
      · have hni : i ≠ bs.length - 1 := by omega
        rw [ite_eq_right hx, ite_eq_right (out_ne (by omega) (by omega) hni)]
        exact ht.bytes i hil
  refine ⟨he, ?_, ?_, (k12.trans (ht.keep.trans k)).mono (by decide)⟩
  · rw [he, shapedOctets_value (bits := bits) hne hj (by omega)]
  · intro a ha
    have hx : a ≠ op := by simpa [off] using ha 0 h0
    rw [hmem, WriteBytes.writeW8_apply, ite_eq_right (ha _ hlast), ht.frame a ha,
      hmem₂, WriteBytes.writeW8_apply, ite_eq_right hx, hmem₁]

end VG.Proof.Ffdh.X86_64.ParameterCandidate

module
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Prepared

import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-! # State preserved while selecting a DSA Miller–Rabin witness -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64 VG.Proof.Ffdh.X86_64.ParameterCandidate

/-- kOut and kUsedP are available while testing a candidate; the outer
parameter-generation frame owns the actual output and tape pointers. -/
structure SampleState (B p : Addr) (Z w N : Nat) (mi : BitVec 64) (bs : List Byte) (s : State) : Prop where
  ready : ModulusReady s B Z w mi N
  ptr : word s.mem B (8 * kOut) = p
  len : word s.mem B (8 * kUsedP) = BitVec.ofNat 64 bs.length
  source : Src s B Z p bs
  writable : ∀ i < bs.length, InRegions s.wr (off p i) 1

theorem SampleState.of_frm {B p : Addr} {Z w N : Nat} {mi : BitVec 64} {bs : List Byte} {s t : State}
    {rs : List (Nat × Nat)} {regs : List Reg} (h : SampleState B p Z w N mi bs s)
    (hd : MrDims B Z w) (ht : ModulusReady t B Z w mi N) (hf : Frm B rs s.mem t.mem)
    (hk : Keep regs s t)
    (hp : ∀ r ∈ rs, 8 * kOut + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * kOut)
    (hl : ∀ r ∈ rs, 8 * kUsedP + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * kUsedP)
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ Z) : SampleState B p Z w N mi bs t := by
  have hz : 256 ≤ Z := by have := hd.z; simp only [slot, hdrBytes] at this; omega
  have hn := h.ready.good.scr.nowrap
  refine ⟨ht, ?_, ?_, ?_, fun i hi => by rw [hk.2.2]; exact h.writable i hi⟩
  · rw [hf.word_eq hp (by change 136 ≤ 2 ^ 64; decide)]; exact h.ptr
  · rw [hf.word_eq hl (by change 152 ≤ 2 ^ 64; decide)]; exact h.len
  · exact h.source.congrK (fun x hx => hf x fun r hmem => Or.inr (Nat.le_trans (hr r hmem) hx)) hk

theorem SampleState.bytes {B p : Addr} {Z w N : Nat} {mi : BitVec 64} {bs : List Byte} {s : State}
    (h : SampleState B p Z w N mi bs s) : Spec.Rsa.bytesAt s.mem p bs.length = bs := by
  apply List.ext_getElem
  · exact bytesAt_length _ _ _
  · intro i hi hi'
    simpa only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range] using h.source.val i hi'

end VG.Proof.Dsa.X86_64.Generation

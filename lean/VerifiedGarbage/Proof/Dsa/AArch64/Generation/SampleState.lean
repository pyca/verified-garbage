module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusFrame
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.ModulusWords
import VerifiedGarbage.Proof.Framework.Omega

/-! The modulus and witness-buffer context retained throughout sampling. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.RsaKeyGen.AArch64
open VG.Proof.MlKem.AArch64

structure SampleState (B p : Addr) (Z w N : Nat) (bs : List Byte) (s : State) : Prop where
  ready : ModulusReady s B Z w N
  ptr : word s.mem B (8 * kOut) = p
  len : word s.mem B (8 * kUsedP) = BitVec.ofNat 64 bs.length
  source : Src s B Z p bs
  writable : ∀ i < bs.length, InRegions s.wr (off p i) 1

theorem SampleState.of_frm {B p : Addr} {Z w N : Nat} {bs : List Byte} {s t : State}
    {rs : List (Nat × Nat)} {regs : List Reg} (h : SampleState B p Z w N bs s)
    (ht : ModulusReady t B Z w N) (hf : Frm B rs s.mem t.mem) (hk : Keep regs s t)
    (hp : ∀ r ∈ rs, 8 * kOut + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * kOut)
    (hl : ∀ r ∈ rs, 8 * kUsedP + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * kUsedP)
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ Z) : SampleState B p Z w N bs t := by
  refine ⟨ht, (hf.word_eq hp (by decide)).trans h.ptr,
    (hf.word_eq hl (by decide)).trans h.len, ?_, ?_⟩
  · exact h.source.congrK (fun x hx => hf x fun r hmem => Or.inr (Nat.le_trans (hr r hmem) hx)) hk
  · intro i hi; rw [hk.wr]; exact h.writable i hi

theorem SampleState.bytes {B p : Addr} {Z w N : Nat} {bs : List Byte} {s : State}
    (h : SampleState B p Z w N bs s) : Spec.Rsa.bytesAt s.mem p bs.length = bs := by
  apply List.ext_getElem
  · exact bytesAt_length _ _ _
  · intro i hi hi'
    simpa only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range] using h.source.val i hi'

end VG.Proof.Dsa.AArch64.Generation

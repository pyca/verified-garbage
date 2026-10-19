module
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Shape
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.HalveOctets
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Spec.Rsa.Contract

import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.HalveByte
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.Octets

/-! # FFDH parameter candidates on x86-64: in-place byte halving -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.ParameterCandidate

structure HalfInv (s₀ : State) (op : Addr) (bs : List Byte) (j : Nat) (t : State) : Prop where
  keep : Keep [.rax, .rdx, .r8, .r10, .rcx] s₀ t
  ptr : t.gpr .r10 = off op j
  count : t.gpr .rcx = BitVec.ofNat 64 (bs.length - j)
  carry : t.gpr .r8 = BitVec.ofNat 64 (128 * carryAt 0 bs j)
  bytes : ∀ i < j, t.mem (off op i) = (halfOctets 0 bs).getD i 0
  frame : ∀ a, (∀ i < j, a ≠ off op i) → t.mem a = s₀.mem a

theorem halfStep_ok {s₀ t : State} {op : Addr} {bs : List Byte} {j : Nat}
    (hk : bs.length < 2 ^ 31) (hj : j < bs.length)
    (hwr : ∀ i < bs.length, InRegions s₀.wr (off op i) 1)
    (hb : ∀ i < bs.length, s₀.mem (off op i) = bs.getD i 0)
    (h : HalfInv s₀ op bs j t) : WP isa (.block halveByte) t fun u =>
      u.zf = some (decide (j + 1 = bs.length)) ∧ HalfInv s₀ op bs (j + 1) u := by
  have hwr' : InRegions t.wr (off op j) 1 := by rw [h.keep.2.2]; exact hwr j hj
  have hrd' : InRegions (t.rd ++ t.wr) (off op j) 1 :=
    let ⟨r, hr, hc⟩ := hwr'; ⟨r, List.mem_append_right _ hr, hc⟩
  have hb' : t.mem (off op j) = bs.getD j 0 := by
    rw [h.frame _ (fun i hi => out_ne (by omega) (by omega) (by omega))]
    exact hb j hj
  refine WP.mono (halveByte_ok hj hk (carryAt_le (by decide) bs j) h.ptr h.count h.carry hrd' hwr' hb')
    fun u ⟨hm, hp, hn, hc, hz, k⟩ => ?_
  refine ⟨hz, ⟨(h.keep.trans k).mono (by decide), hp, hn, ?_, ?_, ?_⟩⟩
  · rw [carryAt_next 0 hj]
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] using hc
  · intro i hi
    rw [hm, WriteBytes.writeW8_apply]
    by_cases he : i = j
    · subst he
      rw [ite_eq_left rfl]
      have hhl : i < (halfOctets 0 bs).length := by rw [halfOctets_length]; exact hj
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
        List.getElem?_eq_getElem hhl, Option.getD_some] using (halfOctets_get 0 hj).symm
    · rw [ite_eq_right (out_ne (by omega) (by omega) he)]
      exact h.bytes i (by omega)
  · intro a ha
    rw [hm, WriteBytes.writeW8_apply, ite_eq_right (ha j (by omega))]
    exact h.frame a (fun i hi => ha i (by omega))

theorem halfLoop_ok {s : State} {op : Addr} {bs : List Byte}
    (hk1 : 1 ≤ bs.length) (hk : bs.length < 2 ^ 31)
    (hp : s.gpr .r10 = op) (hn : s.gpr .rcx = BitVec.ofNat 64 bs.length) (hc : s.gpr .r8 = 0)
    (hwr : ∀ i < bs.length, InRegions s.wr (off op i) 1)
    (hb : ∀ i < bs.length, s.mem (off op i) = bs.getD i 0) :
    WP isa (.loop (.block halveByte) .ne) s (HalfInv s op bs bs.length) :=
  wp_upto (a := 0) (by omega) (HalfInv s op bs)
    (fun j _ hj t ht => halfStep_ok hk hj hwr hb ht) (fun _ h => h)
    ⟨Keep.refl _ _, by rw [hp]; simp, by rw [hn, Nat.sub_zero], by simpa [carryAt] using hc,
      fun i hi => by omega, fun _ _ => rfl⟩

/-- Form q in place, preserving every byte outside the candidate buffer. -/
theorem halve_ok {s : State} {op : Addr} {bs : List Byte}
    (hk1 : 1 ≤ bs.length) (hk : bs.length < 2 ^ 31)
    (hp : s.gpr .rdi = op) (hn : s.gpr .rcx = BitVec.ofNat 64 bs.length)
    (hwr : ∀ i < bs.length, InRegions s.wr (off op i) 1)
    (hb : ∀ i < bs.length, s.mem (off op i) = bs.getD i 0) :
    WP isa halve s fun t => Spec.Rsa.bytesAt t.mem op bs.length = halfOctets 0 bs ∧
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem op bs.length) = Spec.Rsa.os2ip bs / 2 ∧
      (∀ a, (∀ i < bs.length, a ≠ off op i) → t.mem a = s.mem a) ∧
      Keep [.rax, .rdx, .r8, .r10, .rcx] s t := by
  unfold halve
  refine WP.seq (WP.mono (WP.keep [.r10, .r8] (Q := fun u => u.gpr .r10 = op ∧ u.gpr .r8 = 0 ∧ u.mem = s.mem)
    (by xrun [hp]) rfl) fun u ⟨⟨hpu, hcu, hmu⟩, ku⟩ => ?_)
  refine WP.mono (halfLoop_ok hk1 hk hpu ((ku.gpr (by decide)).trans hn) hcu
    (fun i hi => by rw [ku.2.2]; exact hwr i hi)
    (fun i hi => by rw [hmu]; exact hb i hi)) fun t ht => ?_
  have he : Spec.Rsa.bytesAt t.mem op bs.length = halfOctets 0 bs := by
    apply List.ext_getElem
    · rw [bytesAt_length, halfOctets_length]
    · intro i hi hi'
      have hil : i < bs.length := by rwa [bytesAt_length] at hi
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
      change t.mem (off op i) = (halfOctets 0 bs)[i]
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some] using ht.bytes i hil
  exact ⟨he, by rw [he, halfOctets_zero], (fun a ha => (ht.frame a ha).trans (congrFun hmu a)),
    (ku.trans ht.keep).mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate

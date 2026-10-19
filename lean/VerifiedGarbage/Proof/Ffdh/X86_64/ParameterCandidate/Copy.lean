module
public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Shape
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ShapeOctets
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp

import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! # FFDH parameter candidates on x86-64: copy the remaining random bytes -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.ParameterCandidate

theorem copyByte_ok {s : State} {rp op : Addr} {j k : Nat} {b : Byte}
    (hj : j < k) (hk : k < 2 ^ 31) (hrp : s.gpr .r10 = off rp j) (hop : s.gpr .r11 = off op j)
    (hn : s.gpr .rcx = BitVec.ofNat 64 (k - j))
    (hrd : InRegions (s.rd ++ s.wr) (off rp j) 1) (hwr : InRegions s.wr (off op j) 1)
    (hb : s.mem (off rp j) = b) : WP isa (.block copyByte) s fun t =>
      (t.mem = s.mem.writeW (off op j) b ∧ t.gpr .r10 = off rp (j + 1) ∧ t.gpr .r11 = off op (j + 1) ∧
      t.gpr .rcx = BitVec.ofNat 64 (k - (j + 1)) ∧ t.zf = some (decide (j + 1 = k))) ∧
      Keep [.rax, .r10, .r11, .rcx] s t := by
  refine WP.keep _ ?_ rfl
  unfold copyByte
  xrun [State.ea, at0, hrp, hop, hn,
    show off rp j + BitVec.ofInt 64 0 = off rp j from by simp,
    show off op j + BitVec.ofInt 64 0 = off op j from by simp, hrd, hwr, hb,
    ofNat64_pred (show 1 ≤ k - j by omega) (by omega),
    ofNat64_beq_zero (show k - j - 1 < 2 ^ 64 by omega)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp only [off, BitVec.add_assoc, ofNat_add_one]
  · simp only [off, BitVec.add_assoc, ofNat_add_one]
  · rw [show k - j - 1 = k - (j + 1) by omega]
  · exact decide_eq_decide.mpr (by omega)

private theorem headTail_getD (head : Byte) (bs : List Byte) (i : Nat) :
    (head :: bs.drop 1).getD i 0 = if i = 0 then head else bs.getD i 0 := by
  cases i with
  | zero => rfl
  | succ i => simp [List.getD_eq_getElem?_getD]

structure CopyTailInv (s₀ : State) (rp op : Addr) (bs : List Byte) (head : Byte) (j : Nat) (t : State) : Prop where
  keep : Keep [.rax, .r10, .r11, .rcx] s₀ t
  ptrR : t.gpr .r10 = off rp j
  ptrO : t.gpr .r11 = off op j
  count : t.gpr .rcx = BitVec.ofNat 64 (bs.length - j)
  bytes : ∀ i < j, t.mem (off op i) = (head :: bs.drop 1).getD i 0
  frame : ∀ a, (∀ i < j, a ≠ off op i) → t.mem a = s₀.mem a

theorem copyTailStep_ok {s₀ t : State} {rp op : Addr} {bs : List Byte} {head : Byte} {j : Nat}
    (hk : bs.length < 2 ^ 31) (hj1 : 1 ≤ j) (hj : j < bs.length)
    (hrd : ∀ i < bs.length, InRegions (s₀.rd ++ s₀.wr) (off rp i) 1)
    (hwr : ∀ i < bs.length, InRegions s₀.wr (off op i) 1)
    (hb : ∀ i < bs.length, s₀.mem (off rp i) = bs.getD i 0)
    (hsep : ∀ i < bs.length, ∀ l < bs.length, off rp i ≠ off op l)
    (h : CopyTailInv s₀ rp op bs head j t) : WP isa (.block copyByte) t fun u =>
      u.zf = some (decide (j + 1 = bs.length)) ∧ CopyTailInv s₀ rp op bs head (j + 1) u := by
  have hrd' : InRegions (t.rd ++ t.wr) (off rp j) 1 := by rw [h.keep.2.1, h.keep.2.2]; exact hrd j hj
  have hwr' : InRegions t.wr (off op j) 1 := by rw [h.keep.2.2]; exact hwr j hj
  have hb' : t.mem (off rp j) = bs.getD j 0 := by
    rw [h.frame _ (fun i hi => hsep j hj i (by omega))]
    exact hb j hj
  refine WP.mono (copyByte_ok hj hk h.ptrR h.ptrO h.count hrd' hwr' hb') fun u ⟨⟨hm, hrp, hop, hn, hz⟩, k⟩ => ?_
  refine ⟨hz, ⟨(h.keep.trans k).mono (by decide), hrp, hop, hn, ?_, ?_⟩⟩
  · intro i hi
    rw [hm, WriteBytes.writeW8_apply]
    by_cases he : i = j
    · subst he
      rw [ite_eq_left rfl, headTail_getD, ite_eq_right (show i ≠ 0 by omega)]
    · rw [ite_eq_right (out_ne (by omega) (by omega) he)]
      exact h.bytes i (by omega)
  · intro a ha
    rw [hm, WriteBytes.writeW8_apply, ite_eq_right (ha j (by omega))]
    exact h.frame a (fun i hi => ha i (by omega))

/-- An arbitrary first output byte is ready; copy the remaining source bytes unchanged. -/
theorem copyTailLoop_ok {s : State} {rp op : Addr} {bs : List Byte} {head : Byte}
    (hk1 : 2 ≤ bs.length) (hk : bs.length < 2 ^ 31)
    (hp : s.gpr .r10 = off rp 1) (ho : s.gpr .r11 = off op 1)
    (hn : s.gpr .rcx = BitVec.ofNat 64 (bs.length - 1))
    (hfirst : s.mem op = head)
    (hrd : ∀ i < bs.length, InRegions (s.rd ++ s.wr) (off rp i) 1)
    (hwr : ∀ i < bs.length, InRegions s.wr (off op i) 1)
    (hb : ∀ i < bs.length, s.mem (off rp i) = bs.getD i 0)
    (hsep : ∀ i < bs.length, ∀ l < bs.length, off rp i ≠ off op l) :
    WP isa (.loop (.block copyByte) .ne) s (CopyTailInv s rp op bs head bs.length) :=
  wp_upto (a := 1) (by omega) (CopyTailInv s rp op bs head)
    (fun j hj1 hj t ht => copyTailStep_ok hk hj1 hj hrd hwr hb hsep ht) (fun _ h => h)
    ⟨Keep.refl _ _, hp, ho, hn, (fun i hi => by
      have he : i = 0 := by omega
      subst he
      rw [headTail_getD, ite_eq_left rfl]
      simpa [off] using hfirst),
      fun _ _ => rfl⟩

/-- The candidate-shaping instance of the generic tail-copy invariant. -/
abbrev CopyInv (s₀ : State) (rp op : Addr) (bs : List Byte) (bit j : Nat) (t : State) : Prop :=
  CopyTailInv s₀ rp op bs (topByte bit (bs.getD 0 0)) j t

/-- The first byte is already shaped; all remaining bytes are copied unchanged. -/
theorem copyLoop_ok {s : State} {rp op : Addr} {bs : List Byte} {bit : Nat}
    (hk1 : 2 ≤ bs.length) (hk : bs.length < 2 ^ 31)
    (hp : s.gpr .r10 = off rp 1) (ho : s.gpr .r11 = off op 1)
    (hn : s.gpr .rcx = BitVec.ofNat 64 (bs.length - 1))
    (hfirst : s.mem op = topByte bit (bs.getD 0 0))
    (hrd : ∀ i < bs.length, InRegions (s.rd ++ s.wr) (off rp i) 1)
    (hwr : ∀ i < bs.length, InRegions s.wr (off op i) 1)
    (hb : ∀ i < bs.length, s.mem (off rp i) = bs.getD i 0)
    (hsep : ∀ i < bs.length, ∀ l < bs.length, off rp i ≠ off op l) :
    WP isa (.loop (.block copyByte) .ne) s (CopyInv s rp op bs bit bs.length) :=
  copyTailLoop_ok hk1 hk hp ho hn hfirst hrd hwr hb hsep

end VG.Proof.Ffdh.X86_64.ParameterCandidate

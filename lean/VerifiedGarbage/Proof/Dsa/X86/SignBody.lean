module

public import VerifiedGarbage.Proof.Dsa.X86.SavedFrame
public import VerifiedGarbage.Proof.Dsa.X86.SignCompute
public import VerifiedGarbage.Proof.Dsa.X86.WriteSignature
public import VerifiedGarbage.Proof.Dsa.X86.Result

/-! # Functional correctness of the post-shape signing body -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem signBody_ok {base : Addr} {size pLen qLen p q g y x k digestLen digest : Nat} {s0 : State} {out : BitVec 32}
    (M : Moduli base size pLen qLen p q s0)
    (G : CallerBuffer s0 base size (.input .g) pLen)
    (Y : CallerBuffer s0 base size (.input .y) pLen)
    (X : CallerBuffer s0 base size (.input .x) qLen)
    (K : CallerBuffer s0 base size (.input .nonce) qLen)
    (D : CallerBuffer s0 base size (.input .digest) digestLen)
    (hd : digestLen ≤ 32)
    (hP : pointerValue base s0 (.input .digestPrefixLen) = BitVec.ofNat 32 digestLen)
    (hg : operandValue s0 base (.input .g) pLen = g)
    (hy : operandValue s0 base (.input .y) pLen = y)
    (hx : operandValue s0 base (.input .x) qLen = x)
    (hk : operandValue s0 base (.input .nonce) qLen = k)
    (hD : operandValue s0 base (.input .digest) digestLen = digest)
    (hm : flagW base (Layout.field .mask) s0 = BitVec.allOnes 32)
    (hp : pointerValue base s0 (.input .out) = out)
    (hf : out.toNat + 2 * qLen ≤ 2 ^ 32)
    (hw : ∀ e k, e + k ≤ 2 * qLen → InRegions s0.wr (out.setWidth 64 + BitVec.ofNat 64 e) k)
    (ha : Region.Disjoint ⟨base, size⟩ ⟨out.setWidth 64, 2 * qLen⟩) :
    let rv := g ^ k % p % q
    let sv := k ^ (q - 2) % q * ((digest % q + x * rv % q) % q) % q
    let accepted := publicChecks p q g y ∧ (0 < x ∧ x < q) ∧ (0 < k ∧ k < q) ∧
      g ^ x % p = y ∧ rv ≠ 0 ∧ sv ≠ 0
    WP isa (SignVerify.signBody pLen qLen) s0 fun sf =>
      sf.gpr .eax = (if accepted then 1 else 0) ∧
      Spec.Rsa.bytesAt sf.mem (out.setWidth 64) qLen =
        (if accepted then Spec.Dsa.encodeBE qLen rv else List.replicate qLen 0) ∧
      Spec.Rsa.bytesAt sf.mem (out.setWidth 64 + BitVec.ofNat 64 qLen) qLen =
        (if accepted then Spec.Dsa.encodeBE qLen sv else List.replicate qLen 0) ∧
      Keeps powerClob s0 sf ∧
      StackOutputFrame (s0.gpr .esp) base (out.setWidth 64) usedBytes (2 * qLen) s0.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved s0.mem (off base) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off base) regs Entry.savedRegisters := by
  dsimp only
  let accepted := publicChecks p q g y ∧ (0 < x ∧ x < q) ∧ (0 < k ∧ k < q) ∧
    g ^ x % p = y ∧ g ^ k % p % q ≠ 0 ∧
      k ^ (q - 2) % q * ((digest % q + x * (g ^ k % p % q) % q) % q) % q ≠ 0
  unfold SignVerify.signBody
  refine WP.seq (WP.mono (signCompute_ok M G Y X K D hd hP hg hy hx hk hD)
    fun s1 ⟨M1, R1, S1, F1, E1⟩ => ?_)
  have mask1 : flagW base (Layout.field .mask) s1 = mask32 accepted := by
    simpa only [hm, BitVec.allOnes_and] using F1
  have ptr1 : pointerValue base s1 (.input .out) = out := by
    rw [runFrame_pointer E1.mem E1.keeps (by decide) (by decide), hp]
  refine wp_seq_assoc (WP.seq (WP.mono (writeSignature_ok M1 (decide accepted)
    (by simpa only [mask32, decide_eq_true_eq] using mask1) R1 S1 ptr1 hf
    (by intro e k h; rw [E1.keeps.2.2]; exact hw e k h) ha)
    fun s2 ⟨R2, S2, F2, K2, O2⟩ => ?_))
  refine WP.mono (result_ok (M1.scr.of_keeps K2 (by decide)) M1.saved accepted (F2.trans mask1))
    fun sf ⟨Vf, Kf, Of⟩ => ?_
  refine ⟨Vf, ?_, ?_, (E1.keeps.trans (K2.mono (by decide))).trans (Kf.mono (by decide)), ?_, ?_⟩
  · simpa only [Of, decide_eq_true_eq] using R2
  · simpa only [Of, decide_eq_true_eq] using S2

  · intro a ha hb hstack
    rw [Of, O2 a (by have C := VG.Proof.Dsa.X86.Layout.context_bound (by have := M.lengths; omega : (qLen + 7) / 8 ≤ 48); change 15712 ≤ ofs base a at ha; omega) hb]
    apply E1.mem a ?_ (.inr hstack)
    intro pair hp
    simp only [runRanges, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;>
      change 15712 ≤ ofs base a at ha <;> right <;> change _ ≤ ofs base a <;>
      simp only [VG.Impl.Mont.X86.Dynamic.contextBytes, VG.Impl.Mont.X86.Dynamic.slot,
        VG.Impl.Mont.X86.Dynamic.stride, Layout.field, r, usedBytes] <;> omega

  · intro regs saved
    rw [Of]
    exact O2.saved ha
      (by have C := VG.Proof.Dsa.X86.Layout.context_bound (by have := M.lengths; omega : (qLen + 7) / 8 ≤ 48); omega)
      (by have H : 15712 ≤ size := M.extent; omega)
      (by have := M.scr.nowrap; omega) (E1.saved saved)

end VG.Proof.Dsa.X86

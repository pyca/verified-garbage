module

public import VerifiedGarbage.Proof.Rsa.X86.PrivImpl
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# The x86 RSA padding functions: their callee `vg_rsa_private_checked`

Its contract, at a call with given arguments (`priv_pre`, `priv_pub`,
`priv_post`), as on ARMv7 (`Proof/RsaPkcs1Sig/Arm/PrivCall.lean`): the
caller stores its twenty arguments at `esp` (`PrivArgs`), and gives it the
buffers `privRd` to read and `privWr` to write, among them the arguments.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86

open VG VG.X86

/-- The arguments of `vg_rsa_private_checked`, in order. -/
abbrev privArgv (out n e inp p q dp dq qinv scr : BitVec 32) (K el pl ql sl : Nat) : List (BitVec 32) :=
  [out, BitVec.ofNat 32 K, n, BitVec.ofNat 32 K, e, BitVec.ofNat 32 el, inp, BitVec.ofNat 32 K, p,
    BitVec.ofNat 32 pl, q, BitVec.ofNat 32 ql, dp, BitVec.ofNat 32 pl, dq, BitVec.ofNat 32 ql, qinv,
    BitVec.ofNat 32 pl, scr, BitVec.ofNat 32 sl]

section

variable {s : State} {out n e inp p q dp dq qinv scr : BitVec 32} {K el pl ql sl : Nat}

/-- The call's arguments, at `esp`. -/
structure PrivArgs (s : State) (out n e inp p q dp dq qinv scr : BitVec 32) (K el pl ql sl : Nat) : Prop where
  args : ∀ i < 20, s.mem.readW (addr (s.gpr .esp) (4 * i)) 32 =
    (privArgv out n e inp p q dp dq qinv scr K el pl ql sl).getD i 0
  sp : 3448 ≤ (s.gpr .esp).toNat
  fit : (s.gpr .esp).toNat + 80 ≤ 2 ^ 32
  kv : Spec.Rsa.lenValid K
  el1 : 1 ≤ el
  elK : el ≤ K
  pl1 : 1 ≤ pl
  plK : pl < K
  ql1 : 1 ≤ ql
  qlK : ql < K
  slK : Spec.Rsa.scratchWords K ≤ sl
  sl32 : sl < 2 ^ 32

/-- The callee's buffers. -/
abbrev privRd (n e inp p q dp dq qinv : BitVec 32) (K el pl ql : Nat) : List Region :=
  [⟨n.setWidth 64, K⟩, ⟨e.setWidth 64, el⟩, ⟨inp.setWidth 64, K⟩, ⟨p.setWidth 64, pl⟩, ⟨q.setWidth 64, ql⟩,
    ⟨dp.setWidth 64, pl⟩, ⟨dq.setWidth 64, ql⟩, ⟨qinv.setWidth 64, pl⟩]
abbrev privWr (sp out scr : BitVec 32) (K sl : Nat) : List Region :=
  [⟨out.setWidth 64, K⟩, ⟨scr.setWidth 64, sl * 8⟩, ⟨sp.setWidth 64, 80⟩]

theorem PrivArgs.arg (h : PrivArgs s out n e inp p q dp dq qinv scr K el pl ql sl) (rd wr : List Region)
    {i : Nat} (hi : i < 20) :
    VG.X86.arg (s.callEntry.withRegions rd wr) i = (privArgv out n e inp p q dp dq qinv scr K el pl ql sl).getD i 0 := by
  rw [arg_withRegions, arg_callEntry (by have := h.sp; omega) (by have := h.fit; omega)]
  exact h.args i hi

theorem PrivArgs.k32 (h : PrivArgs s out n e inp p q dp dq qinv scr K el pl ql sl) : K < 2 ^ 32 := by
  have := h.kv.2; omega

theorem priv_pre (h : PrivArgs s out n e inp p q dp dq qinv scr K el pl ql sl)
    (dW : ∀ w ∈ privWr (s.gpr .esp) out scr K sl, ∀ r ∈ privRd n e inp p q dp dq qinv K el pl ql, w.Disjoint r)
    (dWW : (privWr (s.gpr .esp) out scr K sl).Pairwise Region.Disjoint)
    (dLow : ∀ r ∈ privWr (s.gpr .esp) out scr K sl ++ privRd n e inp p q dp dq qinv K el pl ql,
      Region.Disjoint (below (s.gpr .esp) 3448) r)
    (fit : ∀ r ∈ privWr (s.gpr .esp) out scr K sl ++ privRd n e inp p q dp dq qinv K el pl ql,
      r.base.toNat + r.len ≤ 2 ^ 32) :
    (Spec.Rsa.privateCheckedContract abi Proof.Rsa.X86.PrivChecked.stackBytes).pre
      (s.callEntry.withRegions (privRd n e inp p q dp dq qinv K el pl ql) (privWr (s.gpr .esp) out scr K sl)) := by
  have k32 := h.k32
  have el32 : el < 2 ^ 32 := by have := h.elK; omega
  have pl32 : pl < 2 ^ 32 := by have := h.plK; omega
  have ql32 : ql < 2 ^ 32 := by have := h.qlK; omega
  have a := fun {i} (hi : i < 20) => h.arg (privRd n e inp p q dp dq qinv K el pl ql)
    (privWr (s.gpr .esp) out scr K sl) hi
  have hsp := h.sp
  have hfit := h.fit
  have e4 : (s.gpr .esp - 4).toNat = (s.gpr .esp).toNat - 4 := sub_toNat (k := 4) (by omega)
  sig_pre [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, abi, argSlots, argVal, argBytes,
    stackBelow]
  simp only [a (by decide : 0 < 20), a (by decide : 1 < 20), a (by decide : 2 < 20), a (by decide : 3 < 20),
    a (by decide : 4 < 20), a (by decide : 5 < 20), a (by decide : 6 < 20), a (by decide : 7 < 20),
    a (by decide : 8 < 20), a (by decide : 9 < 20), a (by decide : 10 < 20), a (by decide : 11 < 20),
    a (by decide : 12 < 20), a (by decide : 13 < 20), a (by decide : 14 < 20), a (by decide : 15 < 20),
    a (by decide : 16 < 20), a (by decide : 17 < 20), a (by decide : 18 < 20), a (by decide : 19 < 20),
    privArgv, List.getD_cons_zero, List.getD_cons_succ, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.mod_eq_of_lt (show K < 4294967296 by omega), Nat.mod_eq_of_lt (show el < 4294967296 by omega),
    Nat.mod_eq_of_lt (show pl < 4294967296 by omega), Nat.mod_eq_of_lt (show ql < 4294967296 by omega),
    Nat.mod_eq_of_lt (show sl < 4294967296 by have := h.sl32; omega),
    argAddr_withRegions, argAddr_callEntry, Nat.mul_zero, BitVec.add_zero, e4]
  have wr := fun {w r : Region} (hw : w ∈ privWr (s.gpr .esp) out scr K sl)
    (hr : r ∈ privRd n e inp p q dp dq qinv K el pl ql) => dW w hw r hr
  simp only [privWr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, and_true, forall_false, implies_true] at dWW
  obtain ⟨⟨oS, oA⟩, sA⟩ := dWW
  have lo := fun {r : Region} (hr : r ∈ privWr (s.gpr .esp) out scr K sl ++ privRd n e inp p q dp dq qinv K el pl ql) =>
    dLow r hr
  have fi := fun {r : Region} (hr : r ∈ privWr (s.gpr .esp) out scr K sl ++ privRd n e inp p q dp dq qinv K el pl ql) =>
    fit r hr
  have fi' : ∀ (x : BitVec 32) (k : Nat),
      (⟨x.setWidth 64, k⟩ : Region) ∈ privWr (s.gpr .esp) out scr K sl ++ privRd n e inp p q dp dq qinv K el pl ql →
      x.toNat + k ≤ 2 ^ 32 := by
    intro x k hx
    have := fi hx
    rwa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := x.isLt; omega)] at this
  have ret : Region.Sub ⟨(s.gpr .esp - 4).setWidth 64, 4⟩ (below (s.gpr .esp) 3448) :=
    below_sub (by decide) h.sp
  have low : Region.Sub ⟨(s.gpr .esp - 4).setWidth 64 - BitVec.ofNat 64 3444, 3444⟩ (below (s.gpr .esp) 3448) := by
    rw [← Taint.sub_setWidth (by omega)]
    exact below_inner (by decide) h.sp
  repeat' apply And.intro
  all_goals first
    | omega | kernel_rfl | trivial | exact h.kv | exact h.el1 | exact h.elK | exact h.pl1 | exact h.plK
    | exact h.ql1 | exact h.qlK | exact h.slK | exact oS | exact oA | exact sA
    | (refine wr ?_ ?_ <;> simp <;> fail) | (refine (wr ?_ ?_).symm <;> simp <;> fail)
    | (refine (lo ?_).sub_left ret; simp <;> fail) | (refine (lo ?_).sub_left low; simp <;> fail)
    | (refine fi' _ _ ?_; simp <;> fail)
    | (simp only [Proof.Rsa.X86.PrivChecked.stackBytes]; omega)
    | exact h.kv.1 | exact h.kv.2

theorem priv_pub {s₁ s₂ : State} (h₁ : PrivArgs s₁ out n e inp p q dp dq qinv scr K el pl ql sl)
    (h₂ : PrivArgs s₂ out n e inp p q dp dq qinv scr K el pl ql sl) (hsp : s₁.gpr .esp = s₂.gpr .esp)
    (hn : Spec.Rsa.bytesAt s₁.mem (n.setWidth 64) K = Spec.Rsa.bytesAt s₂.mem (n.setWidth 64) K)
    (he : Spec.Rsa.bytesAt s₁.mem (e.setWidth 64) el = Spec.Rsa.bytesAt s₂.mem (e.setWidth 64) el)
    (hdn : (below (s₁.gpr .esp) 3448).Disjoint ⟨n.setWidth 64, K⟩)
    (hde : (below (s₁.gpr .esp) 3448).Disjoint ⟨e.setWidth 64, el⟩)
    (rd wr : List Region) :
    (Spec.Rsa.privateCheckedContract abi Proof.Rsa.X86.PrivChecked.stackBytes).pub (s₁.callEntry.withRegions rd wr)
      (s₂.callEntry.withRegions rd wr) := by
  have k32 := h₁.k32
  have a₁ := fun {i} (hi : i < 20) => h₁.arg rd wr hi
  have a₂ := fun {i} (hi : i < 20) => h₂.arg rd wr hi
  sig_pub [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, abi, argSlots, argVal, argBytes]
  simp only [a₁ (by decide : 0 < 20), a₁ (by decide : 1 < 20), a₁ (by decide : 2 < 20), a₁ (by decide : 3 < 20),
    a₁ (by decide : 4 < 20), a₁ (by decide : 5 < 20), a₁ (by decide : 6 < 20), a₁ (by decide : 7 < 20),
    a₁ (by decide : 8 < 20), a₁ (by decide : 9 < 20), a₁ (by decide : 10 < 20), a₁ (by decide : 11 < 20),
    a₁ (by decide : 12 < 20), a₁ (by decide : 13 < 20), a₁ (by decide : 14 < 20), a₁ (by decide : 15 < 20),
    a₁ (by decide : 16 < 20), a₁ (by decide : 17 < 20), a₁ (by decide : 18 < 20), a₁ (by decide : 19 < 20),
    a₂ (by decide : 0 < 20), a₂ (by decide : 1 < 20), a₂ (by decide : 2 < 20), a₂ (by decide : 3 < 20),
    a₂ (by decide : 4 < 20), a₂ (by decide : 5 < 20), a₂ (by decide : 6 < 20), a₂ (by decide : 7 < 20),
    a₂ (by decide : 8 < 20), a₂ (by decide : 9 < 20), a₂ (by decide : 10 < 20), a₂ (by decide : 11 < 20),
    a₂ (by decide : 12 < 20), a₂ (by decide : 13 < 20), a₂ (by decide : 14 < 20), a₂ (by decide : 15 < 20),
    a₂ (by decide : 16 < 20), a₂ (by decide : 17 < 20), a₂ (by decide : 18 < 20), a₂ (by decide : 19 < 20),
    privArgv, List.getD_cons_zero, List.getD_cons_succ, hsp, true_and, and_true]
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt k32,
    Nat.mod_eq_of_lt (show el < 2 ^ 32 by have := h₁.elK; omega)]
  have ret := fun {sx : State} (hx : 3448 ≤ (sx.gpr .esp).toNat) =>
    (Frame.refl [⟨(sx.gpr .esp - 4).setWidth 64, 4⟩] sx.mem).writeW (List.mem_singleton_self _) (sx.unknowns 0)
      (Region.contains_self _ _)
  have ret₁ := ret (sx := s₁) h₁.sp
  have ret₂ := ret (sx := s₂) h₂.sp
  rw [← hsp] at ret₂ ⊢
  have dq : ∀ {x : BitVec 32} {k : Nat}, (below (s₁.gpr .esp) 3448).Disjoint ⟨x.setWidth 64, k⟩ →
      ∀ r ∈ [(⟨(s₁.gpr .esp - 4).setWidth 64, 4⟩ : Region)], (⟨x.setWidth 64, k⟩ : Region).Disjoint r := by
    intro x k hd r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact (hd.sub_left (below_sub (a := 4) (by decide) h₁.sp)).symm
  rw [Proof.RsaPkcs1Sig.bytesAt_frame ret₁ (dq hdn) (by omega), Proof.RsaPkcs1Sig.bytesAt_frame ret₂ (dq hdn) (by omega),
    Proof.RsaPkcs1Sig.bytesAt_frame ret₁ (dq hde) (by have := h₁.elK; omega),
    Proof.RsaPkcs1Sig.bytesAt_frame ret₂ (dq hde) (by have := h₁.elK; omega), hn, he]

/-- The call's result: what it writes to `out` and returns. -/
theorem priv_post {s t : State} (h : PrivArgs s out n e inp p q dp dq qinv scr K el pl ql sl)
    {rd wr : List Region}
    (hp : (Spec.Rsa.privateCheckedContract abi Proof.Rsa.X86.PrivChecked.stackBytes).post
      (s.callEntry.withRegions rd wr) t) :
    Spec.Rsa.writtenOutcome t.mem (out.setWidth 64) K (t.gpr .eax)
      (Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.callEntry.mem (n.setWidth 64) K)
        (Spec.Rsa.bytesAt s.callEntry.mem (e.setWidth 64) el) (Spec.Rsa.bytesAt s.callEntry.mem (inp.setWidth 64) K)
        (Spec.Rsa.bytesAt s.callEntry.mem (p.setWidth 64) pl) (Spec.Rsa.bytesAt s.callEntry.mem (q.setWidth 64) ql)
        (Spec.Rsa.bytesAt s.callEntry.mem (dp.setWidth 64) pl) (Spec.Rsa.bytesAt s.callEntry.mem (dq.setWidth 64) ql)
        (Spec.Rsa.bytesAt s.callEntry.mem (qinv.setWidth 64) pl)) := by
  have a := fun {i} (hi : i < 20) => h.arg rd wr hi
  sig_post [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, abi, argSlots, argVal, argBytes] at hp
  simp only [a (by decide : 0 < 20), a (by decide : 2 < 20), a (by decide : 3 < 20),
    a (by decide : 4 < 20), a (by decide : 5 < 20), a (by decide : 6 < 20),
    a (by decide : 8 < 20), a (by decide : 9 < 20), a (by decide : 10 < 20), a (by decide : 11 < 20),
    a (by decide : 12 < 20), a (by decide : 14 < 20),
    a (by decide : 16 < 20),
    privArgv, List.getD_cons_zero, List.getD_cons_succ, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.mod_eq_of_lt (show K < 4294967296 by have := h.kv.2; omega),
    Nat.mod_eq_of_lt (show el < 4294967296 by have := h.elK; have := h.kv.2; omega),
    Nat.mod_eq_of_lt (show pl < 4294967296 by have := h.plK; have := h.kv.2; omega),
    Nat.mod_eq_of_lt (show ql < 4294967296 by have := h.qlK; have := h.kv.2; omega)] at hp
  rw [BitVec.setWidth_append_eq_right] at hp
  exact hp

end

end VG.Proof.RsaPkcs1Sig.X86

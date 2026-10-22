module

public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt

/-!
# The x86 RSA padding functions: their callee `vg_rsa_public_precomputed_checked`

Its contract with 40 bytes of stack, at a call with given arguments
(`pub_pre`, `pub_pub`, `pub_post`), as `PrivCall.lean` does for
`vg_rsa_private_checked`: the caller stores its ten arguments at `esp`
(`PubArgs`), and gives it the buffers `pubRd` to read and `pubWr` to write,
among them the arguments.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86

open VG VG.X86

/-- The arguments of `vg_rsa_public_precomputed_checked`, in order. -/
abbrev pubArgv (out pre e inp scr : BitVec 32) (K rl el sl : Nat) : List (BitVec 32) :=
  [out, BitVec.ofNat 32 K, pre, BitVec.ofNat 32 rl, e, BitVec.ofNat 32 el, inp, BitVec.ofNat 32 K, scr,
    BitVec.ofNat 32 sl]

section

variable {s : State} {out pre e inp scr : BitVec 32} {K rl el sl : Nat}

/-- The call's arguments, at `esp`. -/
structure PubArgs (s : State) (out pre e inp scr : BitVec 32) (K rl el sl : Nat) : Prop where
  args : ∀ i < 10, s.mem.readW (addr (s.gpr .esp) (4 * i)) 32 = (pubArgv out pre e inp scr K rl el sl).getD i 0
  sp : 44 ≤ (s.gpr .esp).toNat
  fit : (s.gpr .esp).toNat + 40 ≤ 2 ^ 32
  kv : Spec.Rsa.lenValid K
  rlK : rl = Spec.Rsa.precomputedWords K
  el1 : 1 ≤ el
  elK : el ≤ K
  slK : Spec.Rsa.publicScratchWords K ≤ sl
  sl32 : sl < 2 ^ 32

/-- The callee's buffers. -/
abbrev pubRd (pre e inp : BitVec 32) (K rl el : Nat) : List Region :=
  [⟨pre.setWidth 64, rl * 8⟩, ⟨e.setWidth 64, el⟩, ⟨inp.setWidth 64, K⟩]
abbrev pubWr (sp out scr : BitVec 32) (K sl : Nat) : List Region :=
  [⟨out.setWidth 64, K⟩, ⟨scr.setWidth 64, sl * 8⟩, ⟨sp.setWidth 64, 40⟩]

theorem PubArgs.arg (h : PubArgs s out pre e inp scr K rl el sl) (rd wr : List Region) {i : Nat} (hi : i < 10) :
    VG.X86.arg (s.callEntry.withRegions rd wr) i = (pubArgv out pre e inp scr K rl el sl).getD i 0 := by
  rw [arg_withRegions, arg_callEntry (by have := h.sp; omega) (by have := h.fit; omega)]
  exact h.args i hi

theorem PubArgs.k32 (h : PubArgs s out pre e inp scr K rl el sl) : K < 2 ^ 32 := by
  have := h.kv.2; omega

theorem PubArgs.rl32 (h : PubArgs s out pre e inp scr K rl el sl) : rl < 2 ^ 32 := by
  have := h.kv.2; rw [h.rlK]; simp only [Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords]; omega

theorem pub_pre (h : PubArgs s out pre e inp scr K rl el sl)
    (dW : ∀ w ∈ pubWr (s.gpr .esp) out scr K sl, ∀ r ∈ pubRd pre e inp K rl el, w.Disjoint r)
    (dWW : (pubWr (s.gpr .esp) out scr K sl).Pairwise Region.Disjoint)
    (dLow : ∀ r ∈ pubWr (s.gpr .esp) out scr K sl ++ pubRd pre e inp K rl el,
      Region.Disjoint (below (s.gpr .esp) 44) r)
    (fit : ∀ r ∈ pubWr (s.gpr .esp) out scr K sl ++ pubRd pre e inp K rl el, r.base.toNat + r.len ≤ 2 ^ 32) :
    (Spec.Rsa.publicPrecomputedCheckedContract abi 40).pre
      (s.callEntry.withRegions (pubRd pre e inp K rl el) (pubWr (s.gpr .esp) out scr K sl)) := by
  have k32 := h.k32
  have rl32 := h.rl32
  have el32 : el < 2 ^ 32 := by have := h.elK; omega
  have a := fun {i} (hi : i < 10) => h.arg (pubRd pre e inp K rl el) (pubWr (s.gpr .esp) out scr K sl) hi
  have hsp := h.sp
  have hfit := h.fit
  have e4 : (s.gpr .esp - 4).toNat = (s.gpr .esp).toNat - 4 := sub_toNat (k := 4) (by omega)
  sig_pre [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argSlots, argVal,
    argBytes, stackBelow]
  simp only [a (by decide : 0 < 10), a (by decide : 1 < 10), a (by decide : 2 < 10), a (by decide : 3 < 10),
    a (by decide : 4 < 10), a (by decide : 5 < 10), a (by decide : 6 < 10), a (by decide : 7 < 10),
    a (by decide : 8 < 10), a (by decide : 9 < 10),
    pubArgv, List.getD_cons_zero, List.getD_cons_succ, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.mod_eq_of_lt (show K < 4294967296 by omega), Nat.mod_eq_of_lt (show el < 4294967296 by omega),
    Nat.mod_eq_of_lt (show rl < 4294967296 by omega),
    Nat.mod_eq_of_lt (show sl < 4294967296 by have := h.sl32; omega),
    argAddr_withRegions, argAddr_callEntry, Nat.mul_zero, BitVec.add_zero, e4]
  have wr := fun {w r : Region} (hw : w ∈ pubWr (s.gpr .esp) out scr K sl)
    (hr : r ∈ pubRd pre e inp K rl el) => dW w hw r hr
  simp only [pubWr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, and_true, forall_false, implies_true] at dWW
  obtain ⟨⟨oS, oA⟩, sA⟩ := dWW
  have lo := fun {r : Region} (hr : r ∈ pubWr (s.gpr .esp) out scr K sl ++ pubRd pre e inp K rl el) => dLow r hr
  have fi := fun {r : Region} (hr : r ∈ pubWr (s.gpr .esp) out scr K sl ++ pubRd pre e inp K rl el) => fit r hr
  have fi' : ∀ (x : BitVec 32) (k : Nat),
      (⟨x.setWidth 64, k⟩ : Region) ∈ pubWr (s.gpr .esp) out scr K sl ++ pubRd pre e inp K rl el →
      x.toNat + k ≤ 2 ^ 32 := by
    intro x k hx
    have := fi hx
    rwa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := x.isLt; omega)] at this
  have ret : Region.Sub ⟨(s.gpr .esp - 4).setWidth 64, 4⟩ (below (s.gpr .esp) 44) :=
    below_sub (by decide) h.sp
  have low : Region.Sub ⟨(s.gpr .esp - 4).setWidth 64 - BitVec.ofNat 64 40, 40⟩ (below (s.gpr .esp) 44) := by
    rw [← Taint.sub_setWidth (by omega)]
    exact below_inner (by decide) h.sp
  repeat' apply And.intro
  all_goals first
    | omega | rfl | trivial | exact h.kv | exact h.el1 | exact h.elK | exact h.slK | exact h.rlK
    | exact oS | exact oA | exact sA
    | (refine wr ?_ ?_ <;> simp <;> fail) | (refine (wr ?_ ?_).symm <;> simp <;> fail)
    | (refine (lo ?_).sub_left ret; simp <;> fail) | (refine (lo ?_).sub_left low; simp <;> fail)
    | (refine fi' _ _ ?_; simp <;> fail)
    | exact h.kv.1 | exact h.kv.2

theorem pub_pub {s₁ s₂ : State} (h₁ : PubArgs s₁ out pre e inp scr K rl el sl)
    (h₂ : PubArgs s₂ out pre e inp scr K rl el sl) (hsp : s₁.gpr .esp = s₂.gpr .esp)
    (hp : Spec.Rsa.wordsAt s₁.mem (pre.setWidth 64) rl = Spec.Rsa.wordsAt s₂.mem (pre.setWidth 64) rl)
    (he : Spec.Rsa.bytesAt s₁.mem (e.setWidth 64) el = Spec.Rsa.bytesAt s₂.mem (e.setWidth 64) el)
    (hdp : (below (s₁.gpr .esp) 44).Disjoint ⟨pre.setWidth 64, rl * 8⟩)
    (hde : (below (s₁.gpr .esp) 44).Disjoint ⟨e.setWidth 64, el⟩)
    (rd wr : List Region) :
    (Spec.Rsa.publicPrecomputedCheckedContract abi 40).pub (s₁.callEntry.withRegions rd wr)
      (s₂.callEntry.withRegions rd wr) := by
  have rl32 := h₁.rl32
  have a₁ := fun {i} (hi : i < 10) => h₁.arg rd wr hi
  have a₂ := fun {i} (hi : i < 10) => h₂.arg rd wr hi
  sig_pub [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argSlots, argVal,
    argBytes]
  simp only [a₁ (by decide : 0 < 10), a₁ (by decide : 1 < 10), a₁ (by decide : 2 < 10), a₁ (by decide : 3 < 10),
    a₁ (by decide : 4 < 10), a₁ (by decide : 5 < 10), a₁ (by decide : 6 < 10), a₁ (by decide : 7 < 10),
    a₁ (by decide : 8 < 10), a₁ (by decide : 9 < 10),
    a₂ (by decide : 0 < 10), a₂ (by decide : 1 < 10), a₂ (by decide : 2 < 10), a₂ (by decide : 3 < 10),
    a₂ (by decide : 4 < 10), a₂ (by decide : 5 < 10), a₂ (by decide : 6 < 10), a₂ (by decide : 7 < 10),
    a₂ (by decide : 8 < 10), a₂ (by decide : 9 < 10),
    pubArgv, List.getD_cons_zero, List.getD_cons_succ, hsp, true_and, and_true]
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt rl32,
    Nat.mod_eq_of_lt (show el < 2 ^ 32 by have := h₁.elK; have := h₁.k32; omega)]
  have ret := fun {sx : State} (hx : 44 ≤ (sx.gpr .esp).toNat) =>
    (Frame.refl [⟨(sx.gpr .esp - 4).setWidth 64, 4⟩] sx.mem).writeW (List.mem_singleton_self _) (sx.unknowns 0)
      (Region.contains_self _ _)
  have ret₁ := ret (sx := s₁) h₁.sp
  have ret₂ := ret (sx := s₂) h₂.sp
  rw [← hsp] at ret₂ ⊢
  have dq : ∀ {x : BitVec 32} {k : Nat}, (below (s₁.gpr .esp) 44).Disjoint ⟨x.setWidth 64, k⟩ →
      ∀ r ∈ [(⟨(s₁.gpr .esp - 4).setWidth 64, 4⟩ : Region)], (⟨x.setWidth 64, k⟩ : Region).Disjoint r := by
    intro x k hd r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact (hd.sub_left (below_sub (a := 4) (by decide) h₁.sp)).symm
  rw [Proof.RsaPkcs1Sig.wordsAt_frame' ret₁ (dq hdp) (by omega),
    Proof.RsaPkcs1Sig.wordsAt_frame' ret₂ (dq hdp) (by omega),
    Proof.RsaPkcs1Sig.bytesAt_frame ret₁ (dq hde) (by have := h₁.elK; have := h₁.k32; omega),
    Proof.RsaPkcs1Sig.bytesAt_frame ret₂ (dq hde) (by have := h₁.elK; have := h₁.k32; omega), hp, he]

/-- The call's result: what it writes to `out` and returns. -/
theorem pub_post {s t : State} (h : PubArgs s out pre e inp scr K rl el sl) {rd wr : List Region}
    (hp : (Spec.Rsa.publicPrecomputedCheckedContract abi 40).post (s.callEntry.withRegions rd wr) t) :
    ∀ nB : List Byte, nB.length = K →
      Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt s.callEntry.mem (pre.setWidth 64) rl) →
      Spec.Rsa.written t.mem (out.setWidth 64) K (t.gpr .eax)
        (Spec.Rsa.publicOpChecked nB (Spec.Rsa.bytesAt s.callEntry.mem (e.setWidth 64) el)
          (Spec.Rsa.bytesAt s.callEntry.mem (inp.setWidth 64) K)) := by
  have a := fun {i} (hi : i < 10) => h.arg rd wr hi
  sig_post [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argSlots, argVal,
    argBytes] at hp
  simp only [a (by decide : 0 < 10), a (by decide : 1 < 10), a (by decide : 2 < 10), a (by decide : 3 < 10),
    a (by decide : 4 < 10), a (by decide : 5 < 10), a (by decide : 6 < 10),
    pubArgv, List.getD_cons_zero, List.getD_cons_succ, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.mod_eq_of_lt (show K < 4294967296 by have := h.kv.2; omega),
    Nat.mod_eq_of_lt (show el < 4294967296 by have := h.elK; have := h.kv.2; omega),
    Nat.mod_eq_of_lt (show rl < 4294967296 by have := h.rl32; omega)] at hp
  rw [BitVec.setWidth_append_eq_right] at hp
  exact hp

end

end VG.Proof.RsaPkcs1Sig.X86

module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.PrivCall
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Vp
public import VerifiedGarbage.Proof.Rsa.X86.PrivP.Verified
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
public import VerifiedGarbage.Proof.Rsa.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The x86 RSA padding functions: their callee `vg_rsa_private_checked_precomputed`

`PrivCall.lean`'s, with `pre` and `pre_len` the call's arguments 20 and 21
(`PrivArgsP`, `priv_preP`, `priv_pubP`, `priv_postP`), and `pre`'s first
words, which the callee leaks, from the key (`preModulus`); and a piece
proven of a function's stages keeps a fact of the entry (`VP.keep`), such
as what a wider entry adds.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.X86

open VG VG.X86

/-- A piece keeps a fact of the run's entry. -/
theorem VP.keep {F G : State → State → Prop} {c : Prog isa} (h : VP F c G) (X : State → Prop) :
    VP (fun σ s => F σ s ∧ X σ) c (fun σ s => G σ s ∧ X σ) := by
  refine ⟨fun σ s hs => WP.mono (h.wp σ s hs.1) fun _ hq => ⟨hq, hs.2⟩, ?_⟩
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨σ₁, σ₂, ⟨h₁, y₁⟩, ⟨h₂, y₂⟩⟩ e₁ e₂
  have r := ((h.ct.mono (P' := fun a b => F σ₁ a ∧ F σ₂ b) (fun a b hab => ⟨σ₁, σ₂, hab⟩) fun _ _ q => q).wp
    (F₁ := G σ₁) (F₂ := G σ₂) fun _ _ hh => ⟨h.wp _ _ hh.1, h.wp _ _ hh.2⟩) _ _ _ _ _ _ ⟨h₁, h₂⟩ e₁ e₂
  exact ⟨r.1, σ₁, σ₂, ⟨r.2.2.1, y₁⟩, ⟨r.2.2.2, y₂⟩⟩

/-! ## `vg_rsa_private_checked_precomputed`'s arguments -/

/-- The arguments of `vg_rsa_private_checked_precomputed`, in order. -/
abbrev privArgvP (out n e inp p q dp dq qinv scr pre : BitVec 32) (K el pl ql sl L : Nat) : List (BitVec 32) :=
  [out, BitVec.ofNat 32 K, n, BitVec.ofNat 32 K, e, BitVec.ofNat 32 el, inp, BitVec.ofNat 32 K, p,
    BitVec.ofNat 32 pl, q, BitVec.ofNat 32 ql, dp, BitVec.ofNat 32 pl, dq, BitVec.ofNat 32 ql, qinv,
    BitVec.ofNat 32 pl, scr, BitVec.ofNat 32 sl, pre, BitVec.ofNat 32 L]

section

variable {s : State} {out n e inp p q dp dq qinv scr pre : BitVec 32} {K el pl ql sl L : Nat}

/-- The call's arguments, at `esp`, and `pre`'s facts. -/
structure PrivArgsP (s : State) (out n e inp p q dp dq qinv scr pre : BitVec 32) (K el pl ql sl L : Nat) : Prop
    extends PrivArgs s out n e inp p q dp dq qinv scr K el pl ql sl where
  argsP : ∀ i < 22, s.mem.readW (addr (s.gpr .esp) (4 * i)) 32 =
    (privArgvP out n e inp p q dp dq qinv scr pre K el pl ql sl L).getD i 0
  fitP : (s.gpr .esp).toNat + 88 ≤ 2 ^ 32
  lenEq : L = Spec.Rsa.privatePrecomputedWords K pl ql
  key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.callEntry.mem (n.setWidth 64) K)
      (Spec.Rsa.bytesAt s.callEntry.mem (p.setWidth 64) pl) (Spec.Rsa.bytesAt s.callEntry.mem (q.setWidth 64) ql) =
    some (Spec.Rsa.wordsAt s.callEntry.mem (pre.setWidth 64) L)

/-- The callee's buffers. -/
abbrev privRdP (n e inp p q dp dq qinv pre : BitVec 32) (K el pl ql L : Nat) : List Region :=
  [⟨n.setWidth 64, K⟩, ⟨e.setWidth 64, el⟩, ⟨inp.setWidth 64, K⟩, ⟨p.setWidth 64, pl⟩, ⟨q.setWidth 64, ql⟩,
    ⟨dp.setWidth 64, pl⟩, ⟨dq.setWidth 64, ql⟩, ⟨qinv.setWidth 64, pl⟩, ⟨pre.setWidth 64, L * 8⟩]
abbrev privWrP (sp out scr : BitVec 32) (K sl : Nat) : List Region :=
  [⟨out.setWidth 64, K⟩, ⟨scr.setWidth 64, sl * 8⟩, ⟨sp.setWidth 64, 88⟩]

theorem PrivArgsP.arg (h : PrivArgsP s out n e inp p q dp dq qinv scr pre K el pl ql sl L) (rd wr : List Region)
    {i : Nat} (hi : i < 22) :
    VG.X86.arg (s.callEntry.withRegions rd wr) i =
      (privArgvP out n e inp p q dp dq qinv scr pre K el pl ql sl L).getD i 0 := by
  rw [arg_withRegions, arg_callEntry (by have := h.sp; omega) (by have := h.fitP; omega)]
  exact h.argsP i hi

theorem PrivArgsP.L32 (h : PrivArgsP s out n e inp p q dp dq qinv scr pre K el pl ql sl L) : L < 2 ^ 32 := by
  have e := h.lenEq
  have := h.plK; have := h.qlK; have := h.kv.2
  simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords, Spec.Rsa.primeWords,
    Spec.Rsa.modulusWords] at e
  omega

theorem priv_preP (h : PrivArgsP s out n e inp p q dp dq qinv scr pre K el pl ql sl L)
    (dW : ∀ w ∈ privWrP (s.gpr .esp) out scr K sl, ∀ r ∈ privRdP n e inp p q dp dq qinv pre K el pl ql L,
      w.Disjoint r)
    (dWW : (privWrP (s.gpr .esp) out scr K sl).Pairwise Region.Disjoint)
    (dLow : ∀ r ∈ privWrP (s.gpr .esp) out scr K sl ++ privRdP n e inp p q dp dq qinv pre K el pl ql L,
      Region.Disjoint (below (s.gpr .esp) 3448) r)
    (fit : ∀ r ∈ privWrP (s.gpr .esp) out scr K sl ++ privRdP n e inp p q dp dq qinv pre K el pl ql L,
      r.base.toNat + r.len ≤ 2 ^ 32) :
    (Proof.Rsa.privateCheckedPrecomputedContract abi Proof.Rsa.X86.PrivChecked.stackBytes).pre
      (s.callEntry.withRegions (privRdP n e inp p q dp dq qinv pre K el pl ql L)
        (privWrP (s.gpr .esp) out scr K sl)) := by
  have k32 := h.k32
  have el32 : el < 2 ^ 32 := by have := h.elK; omega
  have pl32 : pl < 2 ^ 32 := by have := h.plK; omega
  have ql32 : ql < 2 ^ 32 := by have := h.qlK; omega
  have L32 := h.L32
  have a := fun {i} (hi : i < 22) => h.arg (privRdP n e inp p q dp dq qinv pre K el pl ql L)
    (privWrP (s.gpr .esp) out scr K sl) hi
  have hsp := h.sp
  have hfit := h.fitP
  have e4 : (s.gpr .esp - 4).toNat = (s.gpr .esp).toNat - 4 := sub_toNat (k := 4) (by omega)
  have key := h.key
  rw [State.callEntry_mem] at key
  have lenEq := h.lenEq
  sig_pre [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
    Proof.Rsa.privateCheckedSig, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [a (by decide : 0 < 22),
    a (by decide : 1 < 22),
    a (by decide : 2 < 22),
    a (by decide : 3 < 22),
    a (by decide : 4 < 22),
    a (by decide : 5 < 22),
    a (by decide : 6 < 22),
    a (by decide : 7 < 22),
    a (by decide : 8 < 22),
    a (by decide : 9 < 22),
    a (by decide : 10 < 22),
    a (by decide : 11 < 22),
    a (by decide : 12 < 22),
    a (by decide : 13 < 22),
    a (by decide : 14 < 22),
    a (by decide : 15 < 22),
    a (by decide : 16 < 22),
    a (by decide : 17 < 22),
    a (by decide : 18 < 22),
    a (by decide : 19 < 22),
    a (by decide : 20 < 22),
    a (by decide : 21 < 22),
    privArgvP, List.getD_cons_zero, List.getD_cons_succ,
    BitVec.toNat_ofNat, Nat.reducePow,
    Nat.mod_eq_of_lt (show K < 4294967296 by omega), Nat.mod_eq_of_lt (show el < 4294967296 by omega),
    Nat.mod_eq_of_lt (show pl < 4294967296 by omega), Nat.mod_eq_of_lt (show ql < 4294967296 by omega),
    Nat.mod_eq_of_lt (show sl < 4294967296 by have := h.sl32; omega),
    Nat.mod_eq_of_lt (show L < 4294967296 by omega),
    argAddr_withRegions, argAddr_callEntry, Nat.mul_zero, BitVec.add_zero, e4]
  have wr := fun {w r : Region} (hw : w ∈ privWrP (s.gpr .esp) out scr K sl)
    (hr : r ∈ privRdP n e inp p q dp dq qinv pre K el pl ql L) => dW w hw r hr
  simp only [privWrP, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, and_true, forall_false, implies_true] at dWW
  obtain ⟨⟨oS, oA⟩, sA⟩ := dWW
  have lo := fun {r : Region}
    (hr : r ∈ privWrP (s.gpr .esp) out scr K sl ++ privRdP n e inp p q dp dq qinv pre K el pl ql L) => dLow r hr
  have fi := fun {r : Region}
    (hr : r ∈ privWrP (s.gpr .esp) out scr K sl ++ privRdP n e inp p q dp dq qinv pre K el pl ql L) => fit r hr
  have fi' : ∀ (x : BitVec 32) (k : Nat),
      (⟨x.setWidth 64, k⟩ : Region) ∈
        privWrP (s.gpr .esp) out scr K sl ++ privRdP n e inp p q dp dq qinv pre K el pl ql L →
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
    | exact key | exact lenEq
    | omega | kernel_rfl | trivial | exact h.kv | exact h.el1 | exact h.elK | exact h.pl1 | exact h.plK
    | exact h.ql1 | exact h.qlK | exact h.slK | exact oS | exact oA | exact sA
    | (refine wr ?_ ?_ <;> simp <;> fail) | (refine (wr ?_ ?_).symm <;> simp <;> fail)
    | (refine (lo ?_).sub_left ret; simp <;> fail) | (refine (lo ?_).sub_left low; simp <;> fail)
    | (refine fi' _ _ ?_; simp <;> fail)
    | (simp only [Proof.Rsa.X86.PrivChecked.stackBytes]; omega)
    | exact h.kv.1 | exact h.kv.2
theorem priv_pubP {s₁ s₂ : State} (h₁ : PrivArgsP s₁ out n e inp p q dp dq qinv scr pre K el pl ql sl L)
    (h₂ : PrivArgsP s₂ out n e inp p q dp dq qinv scr pre K el pl ql sl L) (hsp : s₁.gpr .esp = s₂.gpr .esp)
    (hn : Spec.Rsa.bytesAt s₁.mem (n.setWidth 64) K = Spec.Rsa.bytesAt s₂.mem (n.setWidth 64) K)
    (he : Spec.Rsa.bytesAt s₁.mem (e.setWidth 64) el = Spec.Rsa.bytesAt s₂.mem (e.setWidth 64) el)
    (hdn : (below (s₁.gpr .esp) 3448).Disjoint ⟨n.setWidth 64, K⟩)
    (hde : (below (s₁.gpr .esp) 3448).Disjoint ⟨e.setWidth 64, el⟩)
    (hw : Spec.Rsa.wordsAt s₁.callEntry.mem (pre.setWidth 64) (Spec.Rsa.precomputedWords K) =
      Spec.Rsa.wordsAt s₂.callEntry.mem (pre.setWidth 64) (Spec.Rsa.precomputedWords K))
    (rd wr : List Region) :
    (Proof.Rsa.privateCheckedPrecomputedContract abi Proof.Rsa.X86.PrivChecked.stackBytes).pub
      (s₁.callEntry.withRegions rd wr) (s₂.callEntry.withRegions rd wr) := by
  have k32 := h₁.k32
  have a₁ := fun {i} (hi : i < 22) => h₁.arg rd wr hi
  have a₂ := fun {i} (hi : i < 22) => h₂.arg rd wr hi
  sig_pub [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
    Proof.Rsa.privateCheckedSig, abi, argSlots, argVal, argBytes]
  simp only [a₁ (by decide : 0 < 22), a₂ (by decide : 0 < 22),
    a₁ (by decide : 1 < 22), a₂ (by decide : 1 < 22),
    a₁ (by decide : 2 < 22), a₂ (by decide : 2 < 22),
    a₁ (by decide : 3 < 22), a₂ (by decide : 3 < 22),
    a₁ (by decide : 4 < 22), a₂ (by decide : 4 < 22),
    a₁ (by decide : 5 < 22), a₂ (by decide : 5 < 22),
    a₁ (by decide : 6 < 22), a₂ (by decide : 6 < 22),
    a₁ (by decide : 7 < 22), a₂ (by decide : 7 < 22),
    a₁ (by decide : 8 < 22), a₂ (by decide : 8 < 22),
    a₁ (by decide : 9 < 22), a₂ (by decide : 9 < 22),
    a₁ (by decide : 10 < 22), a₂ (by decide : 10 < 22),
    a₁ (by decide : 11 < 22), a₂ (by decide : 11 < 22),
    a₁ (by decide : 12 < 22), a₂ (by decide : 12 < 22),
    a₁ (by decide : 13 < 22), a₂ (by decide : 13 < 22),
    a₁ (by decide : 14 < 22), a₂ (by decide : 14 < 22),
    a₁ (by decide : 15 < 22), a₂ (by decide : 15 < 22),
    a₁ (by decide : 16 < 22), a₂ (by decide : 16 < 22),
    a₁ (by decide : 17 < 22), a₂ (by decide : 17 < 22),
    a₁ (by decide : 18 < 22), a₂ (by decide : 18 < 22),
    a₁ (by decide : 19 < 22), a₂ (by decide : 19 < 22),
    a₁ (by decide : 20 < 22), a₂ (by decide : 20 < 22),
    a₁ (by decide : 21 < 22), a₂ (by decide : 21 < 22),
    privArgvP, List.getD_cons_zero, List.getD_cons_succ, hsp, true_and, and_true]
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
  rw [State.callEntry_mem, State.callEntry_mem, ← hsp] at hw
  simp only [Spec.Rsa.privatePrecomputedLeak]
  rw [Proof.RsaPkcs1Sig.bytesAt_frame ret₁ (dq hdn) (by omega), Proof.RsaPkcs1Sig.bytesAt_frame ret₂ (dq hdn) (by omega),
    Proof.RsaPkcs1Sig.bytesAt_frame ret₁ (dq hde) (by have := h₁.elK; omega),
    Proof.RsaPkcs1Sig.bytesAt_frame ret₂ (dq hde) (by have := h₁.elK; omega), hn, he, hw]

/-- The call's result: what it writes to `out` and returns. -/
theorem priv_postP {s t : State} (h : PrivArgsP s out n e inp p q dp dq qinv scr pre K el pl ql sl L)
    {rd wr : List Region}
    (hp : (Proof.Rsa.privateCheckedPrecomputedContract abi Proof.Rsa.X86.PrivChecked.stackBytes).post
      (s.callEntry.withRegions rd wr) t) :
    Spec.Rsa.writtenOutcome t.mem (out.setWidth 64) K (t.gpr .eax)
      (Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.callEntry.mem (n.setWidth 64) K)
        (Spec.Rsa.bytesAt s.callEntry.mem (e.setWidth 64) el) (Spec.Rsa.bytesAt s.callEntry.mem (inp.setWidth 64) K)
        (Spec.Rsa.bytesAt s.callEntry.mem (p.setWidth 64) pl) (Spec.Rsa.bytesAt s.callEntry.mem (q.setWidth 64) ql)
        (Spec.Rsa.bytesAt s.callEntry.mem (dp.setWidth 64) pl) (Spec.Rsa.bytesAt s.callEntry.mem (dq.setWidth 64) ql)
        (Spec.Rsa.bytesAt s.callEntry.mem (qinv.setWidth 64) pl)) := by
  have a := fun {i} (hi : i < 22) => h.arg rd wr hi
  sig_post [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
    Proof.Rsa.privateCheckedSig, abi, argSlots, argVal, argBytes] at hp
  simp only [a (by decide : 0 < 22), a (by decide : 2 < 22), a (by decide : 3 < 22),
    a (by decide : 4 < 22), a (by decide : 5 < 22), a (by decide : 6 < 22),
    a (by decide : 8 < 22), a (by decide : 9 < 22), a (by decide : 10 < 22), a (by decide : 11 < 22),
    a (by decide : 12 < 22), a (by decide : 14 < 22),
    a (by decide : 16 < 22),
    privArgvP, List.getD_cons_zero, List.getD_cons_succ, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.mod_eq_of_lt (show K < 4294967296 by have := h.kv.2; omega),
    Nat.mod_eq_of_lt (show el < 4294967296 by have := h.elK; have := h.kv.2; omega),
    Nat.mod_eq_of_lt (show pl < 4294967296 by have := h.plK; have := h.kv.2; omega),
    Nat.mod_eq_of_lt (show ql < 4294967296 by have := h.qlK; have := h.kv.2; omega)] at hp
  rw [BitVec.setWidth_append_eq_right] at hp
  exact hp
end

/-- `pre`'s first words, which the call may leak: the modulus' values. -/
theorem preModulus {nB pB qB : List Byte} {m : Mem} {p : Addr} {n : Nat}
    (h : Spec.Rsa.privatePrecompute nB pB qB = some (Spec.Rsa.wordsAt m p n)) :
    some (Spec.Rsa.wordsAt m p (Spec.Rsa.precomputedWords nB.length)) = Spec.Rsa.publicPrecompute nB := by
  unfold Spec.Rsa.privatePrecompute at h
  split at h
  · cases hw : Spec.Rsa.publicPrecompute nB with
    | none => rw [hw] at h; cases h
    | some w =>
      rw [hw] at h
      simp only [Option.map_some, Option.some.injEq] at h
      have hl : w.length = Spec.Rsa.precomputedWords nB.length := by
        unfold Spec.Rsa.publicPrecompute at hw
        dsimp only at hw
        split at hw
        · cases hw
          simp only [List.length_append, Spec.Rsa.toWords, List.length_map, List.length_range,
            Spec.Rsa.precomputedWords]; omega
        · cases hw
      have len : Spec.Rsa.precomputedWords nB.length ≤ n := by
        have := congrArg List.length h
        simp only [List.length_append, Spec.Rsa.wordsAt, List.length_map, List.length_range] at this
        omega
      have take : Spec.Rsa.wordsAt m p (Spec.Rsa.precomputedWords nB.length) =
          (Spec.Rsa.wordsAt m p n).take (Spec.Rsa.precomputedWords nB.length) := by
        simp only [Spec.Rsa.wordsAt, ← List.map_take, List.take_range, Nat.min_eq_left len]
      rw [take, ← h, List.append_assoc, List.take_left' hl]
  · cases h

end VG.Proof.RsaPkcs1Sig.X86

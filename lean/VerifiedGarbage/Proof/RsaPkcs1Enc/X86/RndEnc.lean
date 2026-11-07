module

-- separate module: the unfolding of the callee's contract builds in parallel with `RndBase` and `RndScan`

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on x86: its callee

`vg_rsa_pkcs1_encrypt_precomputed`'s contract with the stack of its x86
implementation (`Proof/RsaPkcs1Enc/X86/PcBase.lean`, 1188 bytes), at a call
with given arguments (`enc_pre`, `enc_pub`, `enc_post`), as
`Proof/RsaPkcs1Sig/X86/PubCall.lean` does for
`vg_rsa_public_precomputed_checked`: the caller stores its fourteen arguments
at `esp` (`EncArgs`), and gives it the buffers `encRd` to read and `encWr`
to write, among them the arguments.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Rnd

open VG VG.X86

/-- The callee's stack. -/
abbrev encStack : Nat := 1188

/-- The arguments of `vg_rsa_pkcs1_encrypt_precomputed`, in order. -/
abbrev encArgv (out n e msg ps scr pre : BitVec 32) (K el ml pl sl rl : Nat) : List (BitVec 32) :=
  [out, BitVec.ofNat 32 K, n, BitVec.ofNat 32 K, e, BitVec.ofNat 32 el, msg, BitVec.ofNat 32 ml, ps,
    BitVec.ofNat 32 pl, scr, BitVec.ofNat 32 sl, pre, BitVec.ofNat 32 rl]

section

variable {s : State} {out n e msg ps scr pre : BitVec 32} {K el ml pl sl rl : Nat}

/-- The call's arguments, at `esp`. -/
structure EncArgs (s : State) (out n e msg ps scr pre : BitVec 32) (K el ml pl sl rl : Nat) : Prop where
  args : ∀ i < 14, s.mem.readW (addr (s.gpr .esp) (4 * i)) 32 = (encArgv out n e msg ps scr pre K el ml pl sl rl).getD i 0
  sp : encStack + 4 ≤ (s.gpr .esp).toNat
  fit : (s.gpr .esp).toNat + 56 ≤ 2 ^ 32
  kv : Spec.Rsa.lenValid K
  el1 : 1 ≤ el
  elK : el ≤ K
  mlK : ml + 11 ≤ K
  plK : pl = K - ml - 3
  slK : Spec.Rsa.publicScratchWords K ≤ sl
  sl32 : sl < 2 ^ 32
  rlK : rl = Spec.Rsa.precomputedWords K

/-- The callee's buffers. -/
abbrev encRd (n e msg ps pre : BitVec 32) (K el ml pl rl : Nat) : List Region :=
  [⟨n.setWidth 64, K⟩, ⟨e.setWidth 64, el⟩, ⟨msg.setWidth 64, ml⟩, ⟨ps.setWidth 64, pl⟩, ⟨pre.setWidth 64, rl * 8⟩]
abbrev encWr (sp out scr : BitVec 32) (K sl : Nat) : List Region :=
  [⟨out.setWidth 64, K⟩, ⟨scr.setWidth 64, sl * 8⟩, ⟨sp.setWidth 64, 56⟩]

theorem EncArgs.arg (h : EncArgs s out n e msg ps scr pre K el ml pl sl rl) (rd wr : List Region) {i : Nat}
    (hi : i < 14) :
    VG.X86.arg (s.callEntry.withRegions rd wr) i = (encArgv out n e msg ps scr pre K el ml pl sl rl).getD i 0 := by
  rw [arg_withRegions, arg_callEntry (by have := h.sp; omega) (by have := h.fit; omega)]
  exact h.args i hi

theorem EncArgs.k32 (h : EncArgs s out n e msg ps scr pre K el ml pl sl rl) : K < 2 ^ 32 := by
  have := h.kv.2; omega

theorem EncArgs.rl32 (h : EncArgs s out n e msg ps scr pre K el ml pl sl rl) : rl < 2 ^ 32 := by
  have := h.kv.2; rw [h.rlK]; simp only [Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords]; omega

theorem enc_pre (h : EncArgs s out n e msg ps scr pre K el ml pl sl rl)
    (dW : ∀ w ∈ encWr (s.gpr .esp) out scr K sl, ∀ r ∈ encRd n e msg ps pre K el ml pl rl, w.Disjoint r)
    (dWW : (encWr (s.gpr .esp) out scr K sl).Pairwise Region.Disjoint)
    (dLow : ∀ r ∈ encWr (s.gpr .esp) out scr K sl ++ encRd n e msg ps pre K el ml pl rl,
      Region.Disjoint (below (s.gpr .esp) (encStack + 4)) r)
    (fit : ∀ r ∈ encWr (s.gpr .esp) out scr K sl ++ encRd n e msg ps pre K el ml pl rl,
      r.base.toNat + r.len ≤ 2 ^ 32) :
    (Proof.RsaPkcs1Enc.encryptPrecomputedContract abi encStack).pre
      (s.callEntry.withRegions (encRd n e msg ps pre K el ml pl rl) (encWr (s.gpr .esp) out scr K sl)) := by
  have k32 := h.k32
  have rl32 := h.rl32
  have el32 : el < 2 ^ 32 := by have := h.elK; omega
  have ml32 : ml < 2 ^ 32 := by have := h.mlK; omega
  have pl32 : pl < 2 ^ 32 := by have := h.plK; omega
  have a := fun {i} (hi : i < 14) => h.arg (encRd n e msg ps pre K el ml pl rl) (encWr (s.gpr .esp) out scr K sl) hi
  have hsp := h.sp
  have hfit := h.fit
  have e4 : (s.gpr .esp - 4).toNat = (s.gpr .esp).toNat - 4 := sub_toNat (k := 4) (by omega)
  sig_pre [Proof.RsaPkcs1Enc.encryptPrecomputedContract, Proof.RsaPkcs1Enc.encryptPrecomputedSig, abi, argSlots,
    argVal, argBytes, stackBelow]
  simp only [a (by decide : 0 < 14), a (by decide : 1 < 14), a (by decide : 2 < 14), a (by decide : 3 < 14),
    a (by decide : 4 < 14), a (by decide : 5 < 14), a (by decide : 6 < 14), a (by decide : 7 < 14),
    a (by decide : 8 < 14), a (by decide : 9 < 14), a (by decide : 10 < 14), a (by decide : 11 < 14),
    a (by decide : 12 < 14), a (by decide : 13 < 14),
    encArgv, List.getD_cons_zero, List.getD_cons_succ, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.mod_eq_of_lt (show K < 4294967296 by omega), Nat.mod_eq_of_lt (show el < 4294967296 by omega),
    Nat.mod_eq_of_lt (show ml < 4294967296 by omega), Nat.mod_eq_of_lt (show pl < 4294967296 by omega),
    Nat.mod_eq_of_lt (show rl < 4294967296 by omega),
    Nat.mod_eq_of_lt (show sl < 4294967296 by have := h.sl32; omega),
    argAddr_withRegions, argAddr_callEntry, Nat.mul_zero, BitVec.add_zero, e4]
  have wr := fun {w r : Region} (hw : w ∈ encWr (s.gpr .esp) out scr K sl)
    (hr : r ∈ encRd n e msg ps pre K el ml pl rl) => dW w hw r hr
  simp only [encWr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, and_true, forall_false, implies_true] at dWW
  obtain ⟨⟨oS, oA⟩, sA⟩ := dWW
  have lo := fun {r : Region} (hr : r ∈ encWr (s.gpr .esp) out scr K sl ++ encRd n e msg ps pre K el ml pl rl) =>
    dLow r hr
  have fi := fun {r : Region} (hr : r ∈ encWr (s.gpr .esp) out scr K sl ++ encRd n e msg ps pre K el ml pl rl) =>
    fit r hr
  have fi' : ∀ (x : BitVec 32) (k : Nat),
      (⟨x.setWidth 64, k⟩ : Region) ∈ encWr (s.gpr .esp) out scr K sl ++ encRd n e msg ps pre K el ml pl rl →
      x.toNat + k ≤ 2 ^ 32 := by
    intro x k hx
    have := fi hx
    rwa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := x.isLt; omega)] at this
  have ret : Region.Sub ⟨(s.gpr .esp - 4).setWidth 64, 4⟩ (below (s.gpr .esp) (encStack + 4)) :=
    below_sub (by decide) h.sp
  have low : Region.Sub ⟨(s.gpr .esp - 4).setWidth 64 - BitVec.ofNat 64 encStack, encStack⟩
      (below (s.gpr .esp) (encStack + 4)) := by
    rw [← Taint.sub_setWidth (by omega)]
    exact below_inner (by decide) h.sp
  repeat' apply And.intro
  all_goals first
    | omega | rfl | trivial | exact h.kv | exact h.el1 | exact h.elK | exact h.slK | exact h.rlK
    | exact h.mlK | exact h.plK
    | exact oS | exact oA | exact sA
    | (refine wr ?_ ?_ <;> simp <;> fail) | (refine (wr ?_ ?_).symm <;> simp <;> fail)
    | (refine (lo ?_).sub_left ret; simp <;> fail) | (refine (lo ?_).sub_left low; simp <;> fail)
    | (refine fi' _ _ ?_; simp <;> fail)
    | exact h.kv.1 | exact h.kv.2

theorem enc_pub {s₁ s₂ : State} (h₁ : EncArgs s₁ out n e msg ps scr pre K el ml pl sl rl)
    (h₂ : EncArgs s₂ out n e msg ps scr pre K el ml pl sl rl) (hsp : s₁.gpr .esp = s₂.gpr .esp)
    (hn : Spec.Rsa.bytesAt s₁.mem (n.setWidth 64) K = Spec.Rsa.bytesAt s₂.mem (n.setWidth 64) K)
    (he : Spec.Rsa.bytesAt s₁.mem (e.setWidth 64) el = Spec.Rsa.bytesAt s₂.mem (e.setWidth 64) el)
    (hp : Spec.Rsa.wordsAt s₁.mem (pre.setWidth 64) rl = Spec.Rsa.wordsAt s₂.mem (pre.setWidth 64) rl)
    (hdn : (below (s₁.gpr .esp) (encStack + 4)).Disjoint ⟨n.setWidth 64, K⟩)
    (hde : (below (s₁.gpr .esp) (encStack + 4)).Disjoint ⟨e.setWidth 64, el⟩)
    (hdp : (below (s₁.gpr .esp) (encStack + 4)).Disjoint ⟨pre.setWidth 64, rl * 8⟩)
    (rd wr : List Region) :
    (Proof.RsaPkcs1Enc.encryptPrecomputedContract abi encStack).pub (s₁.callEntry.withRegions rd wr)
      (s₂.callEntry.withRegions rd wr) := by
  have rl32 := h₁.rl32
  have k32 := h₁.k32
  have el32 : el < 2 ^ 32 := by have := h₁.elK; omega
  have a₁ := fun {i} (hi : i < 14) => h₁.arg rd wr hi
  have a₂ := fun {i} (hi : i < 14) => h₂.arg rd wr hi
  sig_pub [Proof.RsaPkcs1Enc.encryptPrecomputedContract, Proof.RsaPkcs1Enc.encryptPrecomputedSig, abi, argSlots,
    argVal, argBytes]
  simp only [a₁ (by decide : 0 < 14), a₁ (by decide : 1 < 14), a₁ (by decide : 2 < 14), a₁ (by decide : 3 < 14),
    a₁ (by decide : 4 < 14), a₁ (by decide : 5 < 14), a₁ (by decide : 6 < 14), a₁ (by decide : 7 < 14),
    a₁ (by decide : 8 < 14), a₁ (by decide : 9 < 14), a₁ (by decide : 10 < 14), a₁ (by decide : 11 < 14),
    a₁ (by decide : 12 < 14), a₁ (by decide : 13 < 14),
    a₂ (by decide : 0 < 14), a₂ (by decide : 1 < 14), a₂ (by decide : 2 < 14), a₂ (by decide : 3 < 14),
    a₂ (by decide : 4 < 14), a₂ (by decide : 5 < 14), a₂ (by decide : 6 < 14), a₂ (by decide : 7 < 14),
    a₂ (by decide : 8 < 14), a₂ (by decide : 9 < 14), a₂ (by decide : 10 < 14), a₂ (by decide : 11 < 14),
    a₂ (by decide : 12 < 14), a₂ (by decide : 13 < 14),
    encArgv, List.getD_cons_zero, List.getD_cons_succ, hsp, true_and, and_true]
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt rl32, Nat.mod_eq_of_lt k32,
    Nat.mod_eq_of_lt el32]
  have ret := fun {sx : State} (hx : 4 ≤ (sx.gpr .esp).toNat) =>
    (Frame.refl [⟨(sx.gpr .esp - 4).setWidth 64, 4⟩] sx.mem).writeW (List.mem_singleton_self _) (sx.unknowns 0)
      (Region.contains_self _ _)
  have ret₁ := ret (sx := s₁) (by have := h₁.sp; omega)
  have ret₂ := ret (sx := s₂) (by have := h₂.sp; omega)
  rw [← hsp] at ret₂ ⊢
  have dq : ∀ {x : BitVec 32} {k : Nat}, (below (s₁.gpr .esp) (encStack + 4)).Disjoint ⟨x.setWidth 64, k⟩ →
      ∀ r ∈ [(⟨(s₁.gpr .esp - 4).setWidth 64, 4⟩ : Region)], (⟨x.setWidth 64, k⟩ : Region).Disjoint r := by
    intro x k hd r hr
    simp only [List.mem_singleton] at hr; subst hr
    exact (hd.sub_left (below_sub (a := 4) (by decide) h₁.sp)).symm
  rw [Proof.RsaPkcs1Sig.wordsAt_frame' ret₁ (dq hdp) (by omega),
    Proof.RsaPkcs1Sig.wordsAt_frame' ret₂ (dq hdp) (by omega),
    Proof.RsaPkcs1Sig.bytesAt_frame ret₁ (dq hde) (by omega),
    Proof.RsaPkcs1Sig.bytesAt_frame ret₂ (dq hde) (by omega),
    Proof.RsaPkcs1Sig.bytesAt_frame ret₁ (dq hdn) (by omega),
    Proof.RsaPkcs1Sig.bytesAt_frame ret₂ (dq hdn) (by omega), hp, he, hn]

/-- The call's result: what it writes to `out` and returns. -/
theorem enc_post {s t : State} (h : EncArgs s out n e msg ps scr pre K el ml pl sl rl) {rd wr : List Region}
    (hp : (Proof.RsaPkcs1Enc.encryptPrecomputedContract abi encStack).post (s.callEntry.withRegions rd wr) t) :
    Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.callEntry.mem (n.setWidth 64) K) =
        some (Spec.Rsa.wordsAt s.callEntry.mem (pre.setWidth 64) rl) →
      Spec.Rsa.written t.mem (out.setWidth 64) K (t.gpr .eax)
        (Spec.RsaPkcs1Enc.encrypt (Spec.Rsa.bytesAt s.callEntry.mem (n.setWidth 64) K)
          (Spec.Rsa.bytesAt s.callEntry.mem (e.setWidth 64) el)
          (Spec.Rsa.bytesAt s.callEntry.mem (msg.setWidth 64) ml)
          (Spec.Rsa.bytesAt s.callEntry.mem (ps.setWidth 64) pl)) := by
  have a := fun {i} (hi : i < 14) => h.arg rd wr hi
  have k32 := h.k32
  have rl32 := h.rl32
  have el32 : el < 2 ^ 32 := by have := h.elK; omega
  have ml32 : ml < 2 ^ 32 := by have := h.mlK; omega
  have pl32 : pl < 2 ^ 32 := by have := h.plK; omega
  sig_post [Proof.RsaPkcs1Enc.encryptPrecomputedContract, Proof.RsaPkcs1Enc.encryptPrecomputedSig, abi, argSlots,
    argVal, argBytes] at hp
  simp only [a (by decide : 0 < 14), a (by decide : 2 < 14), a (by decide : 3 < 14),
    a (by decide : 4 < 14), a (by decide : 5 < 14), a (by decide : 6 < 14), a (by decide : 7 < 14),
    a (by decide : 8 < 14), a (by decide : 9 < 14), a (by decide : 12 < 14), a (by decide : 13 < 14),
    encArgv, List.getD_cons_zero, List.getD_cons_succ, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.mod_eq_of_lt (show K < 4294967296 by omega), Nat.mod_eq_of_lt (show el < 4294967296 by omega),
    Nat.mod_eq_of_lt (show ml < 4294967296 by omega), Nat.mod_eq_of_lt (show pl < 4294967296 by omega),
    Nat.mod_eq_of_lt (show rl < 4294967296 by omega)] at hp
  rw [BitVec.setWidth_append_eq_right] at hp
  exact hp

end

end VG.Proof.RsaPkcs1Enc.X86.Rnd

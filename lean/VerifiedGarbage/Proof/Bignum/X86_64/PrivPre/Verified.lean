module

public import VerifiedGarbage.Proof.Bignum.X86_64.PrivPre.CTCode
public import VerifiedGarbage.Proof.Bignum.X86_64.PrivPre.Contract
public import VerifiedGarbage.Proof.Rsa.X86_64.CallMont
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
import VerifiedGarbage.Proof.Bignum.X86_64.CallPost
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnBase
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnAdxMont

/-!
# `vg_rsa_private_precompute` on x86-64: verified

With Montgomery multiplication by calls (`CallMont`), whose code inlined is
`PrivPre.code M.mm` for the `Mont` the calls run as: its correctness
(`code_correct`), constant time (`code_constantTime`), the contract on the
registers implying the shared one with 8 bytes of stack (`pp_implies`), and
a postcondition that reads memory only in `pre` (`pp_patch`, `pp_postOut`,
for `X86_64.Scrub.withScrubAll`); and the `Verified` the registration uses
(`pp_verified`, `ppAdx_verified`), from the checks the kernel evaluates on
the code (that it inlines, and that it never loads MXCSR).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64.PrivPre

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.Rsa.X86_64
/-- The postcondition reads memory only in `pre`, apart from the 8 bytes
below `rsp`. -/
theorem pp_patch (s b : State) (hv : Mem) (u : Nat → BitVec 64) (hs : ppContract.pre s)
    (hc : Clear (hole (s.gpr .rsp)) s) (hp : ppContract.post s b) :
    ppContract.post s (b.patch (hole (s.gpr .rsp)) hv u) := by
  have c := ppCtx_of hs
  have hm := Clear.miss_wr hc c.hpreR c.hwrap (k := (s.gpr .rsi).toNat * 8) (Nat.le_refl _)
  simp only [ppContract, State.patch_gpr] at hp ⊢
  rw [patch_mem, wordsAt_overlay fun i hi => hm i (by omega)]
  exact hp

theorem pp_call_verified (M : Mont) {c : Prog isa} (hc : c.InlineOk = true) (hin : c.inline = PrivPre.code M.mm)
    (hmx : (PrivPre.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified target c (Spec.Rsa.privatePrecomputeContract abi 8) :=
  Proof.Rsa.X86_64.Verified.of_inline_sig hc (hin ▸ code_correct M hmx) (hin ▸ code_constantTime M) pp_implies
    (fun _ h => Sig.clear_of_pre h) (fun _ _ _ _ h => Sig.rsp_of_pub h) pp_patch

/-- `n` words at `q` are the same in two memories that agree on the `N`
bytes at `q`, `8 n ≤ N`. -/
theorem wordsAt_congr {m₁ m₂ : Mem} {q : Addr} {k N : Nat} (hk : 8 * k ≤ N) (hN : N < 2 ^ 64)
    (h : ∀ a, Region.Contains ⟨q, N⟩ a 1 → m₁ a = m₂ a) :
    Spec.Rsa.wordsAt m₂ q k = Spec.Rsa.wordsAt m₁ q k :=
  List.map_congr_left fun i hi => Mem.readW_congr fun t ht => by
    have := List.mem_range.mp hi
    rw [Offset.add_add]
    exact (h _ (Offset.contains_base _ (by omega) (by omega))).symm

open VG.X86_64.Scrub in
/-- The postcondition reads memory on return only in `pre`. -/
theorem pp_postOut (stack : Nat) :
    PostOut (Spec.Rsa.privatePrecomputeContract abi stack) (Spec.Rsa.privatePrecomputeSig.retBits 64) :=
  postOut_of_local_pre ScrubAbi.plain fun vs m m₁ m₂ r hlen hpre hb h => by
    obtain ⟨pre, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one (n := 9) hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨preLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨n, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨nLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨p, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨pLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨q, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨qLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨scratch, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain ⟨scratchLen, vs, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    replace hlen := Nat.succ.inj hlen
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    simp only [Spec.Rsa.privatePrecomputeSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Elem.size] at hb
    change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _] _ _ _ m₁ r at h
    change @Curry.apply (Mem → Mem → BitVec _ → Prop) [_, _, _, _, _, _, _, _, _, _] _ _ _ m₂ r
    dsimp only [Curry.apply] at h hpre ⊢
    obtain ⟨hk, hpl1, hpl2, hql1, hql2, hL, -⟩ := hpre
    have hk2 := hk.2
    simp only [Spec.Rsa.privatePrecomputedWords, Spec.Rsa.precomputedWords, Spec.Rsa.primeWords,
      Spec.Rsa.modulusWords] at hL
    rw [wordsAt_congr (q := ArgWord.addr.ofRaw pre) (k := BitVec.toNat ((ArgWord.int abi.ptrBits).ofRaw preLen))
      (N := BitVec.toNat ((ArgWord.int abi.ptrBits).ofRaw preLen) * 8) (by omega) (by omega) hb.1]
    exact h
theorem pp_verified :
    Verified target (Impl.Rsa.X86_64.PrivPre.code Proof.Rsa.X86_64.CallMont.base.mm)
      (Spec.Rsa.privatePrecomputeContract abi 8) :=
  pp_call_verified Mont.fnBase (by decide +kernel) rfl (by decide +kernel)

theorem ppAdx_verified :
    Verified target (Impl.Rsa.X86_64.PrivPre.code Proof.Rsa.X86_64.CallMont.adx.mm)
      (Spec.Rsa.privatePrecomputeContract abi 8) :=
  pp_call_verified Mont.fnAdx (by decide +kernel) rfl (by decide +kernel)

end VG.Proof.Bignum.X86_64.PrivPre

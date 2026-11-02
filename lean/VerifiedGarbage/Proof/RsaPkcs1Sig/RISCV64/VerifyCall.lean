module

public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Impl.RsaPkcs1Sig.RISCV64.Frame
public import VerifiedGarbage.Proof.Bignum.RISCV64.PubVerified
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed
public import VerifiedGarbage.Impl.RsaPkcs1Sig.RISCV64.Precomputed
import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Frame
import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.TCB.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem

/-!
# `vg_rsa_pkcs1_verify_precomputed` on RISC-V: the call

`pubArgs_ok`: the block before the call saves the caller's registers, keeps
`k`, `hash` (zero-extended), `digest` and `digest_len` in `s1`–`s4`, and sets
up the call of `vg_rsa_public_precomputed_checked` (`AtCall`). `call_ok`: the
call writes RSAVP1's result to `EM₁` if `pre` holds the modulus' values
(`AfterCall`). As on PPC64LE (`Proof/RsaPkcs1Sig/PPC64LE/VerifyCall.lean`).
-/

@[expose] public section

/-!
# The RSA operation the signatures call, on RISC-V

Untrusted: everything here is checked by Lean. `vg_rsa_pkcs1_verify_precomputed`
and `vg_rsa_pkcs1_recover_precomputed` call `vg_rsa_public_precomputed_checked`
(`out = a0, out_len = a1, pre = a2, pre_len = a3, e = a4, e_len = a5,
input = a6, input_len = a7, scratch, scratch_len`, the last two on the
stack) by its shared contract (`Spec.Rsa.publicPrecomputedCheckedContract`,
with no stack: it has no frames), which its artifact proves
(`Proof.Bignum.RISCV64.Pub.publicChecked_verified`). As on PPC64LE
(`Proof/RsaPkcs1Sig/PPC64LE/Callee.lean`), the call lemmas evaluate that
contract (`sig_pre`, `sig_post`) into facts about the registers at the call
(`PdOk`, `pdCall`, `pdCallCT`), so the callers' proofs never see
`Sig.contract`.
-/


namespace VG.Proof.RsaPkcs1Sig.RISCV64

open VG VG.RISCV64

theorem stackArgs_two (s : State) :
    List.map (stackArg s) (List.range 2) = [stackArg s 0, stackArg s 1] := rfl

/-- The regions a call of `vg_rsa_public_precomputed_checked` reads and
writes: `pre`, `e`, the input and its two stack arguments; `out` and the
working space. -/
abbrev pdRd (t : State) : List Region :=
  [⟨t.gpr .a2, (t.gpr .a3).toNat * 8⟩, ⟨t.gpr .a4, (t.gpr .a5).toNat⟩, ⟨t.gpr .a6, (t.gpr .a7).toNat⟩,
    ⟨stackArgAddr t 0, 16⟩]

abbrev pdWr (t : State) : List Region :=
  [⟨t.gpr .a0, (t.gpr .a1).toNat⟩, ⟨stackArg t 0, (stackArg t 1).toNat * 8⟩]

/-- What the buffers of a call of `vg_rsa_public_precomputed_checked` need:
they are apart where one is written, from the arguments on the stack, and do
not wrap around. `o`, `n`, `e`, `i`, `sc`, `a`: `out`, `pre`, `e`, the input,
the working space and the stack arguments. -/
structure PdLay (o n e i sc a : Region) : Prop where
  on : o.Disjoint n
  oe : o.Disjoint e
  oi : o.Disjoint i
  os : o.Disjoint sc
  oa : o.Disjoint a
  ns : n.Disjoint sc
  es : e.Disjoint sc
  is : i.Disjoint sc
  sa : sc.Disjoint a
  wo : o.base.toNat + o.len ≤ 2 ^ 64
  wn : n.base.toNat + n.len ≤ 2 ^ 64
  we : e.base.toNat + e.len ≤ 2 ^ 64
  wi : i.base.toNat + i.len ≤ 2 ^ 64
  ws : sc.base.toNat + sc.len ≤ 2 ^ 64

/-- What a call of `vg_rsa_public_precomputed_checked` needs at the call:
the precomputed values of a modulus of `k` bytes (`a3` words at `a2`), `e`
(`a5` bytes) at `a4`, the input at `a6`, `out` at `a0` (`k = a1` bytes); the
working space and its length in words are the two doublewords at `sp`. -/
structure PdOk (t : State) : Prop where
  hl : PdLay ⟨t.gpr .a0, (t.gpr .a1).toNat⟩ ⟨t.gpr .a2, (t.gpr .a3).toNat * 8⟩ ⟨t.gpr .a4, (t.gpr .a5).toNat⟩
    ⟨t.gpr .a6, (t.gpr .a7).toNat⟩ ⟨stackArg t 0, (stackArg t 1).toNat * 8⟩ ⟨stackArgAddr t 0, 16⟩
  spal : t.sp.toNat % 16 = 0
  sp : t.sp.toNat + 16 ≤ 2 ^ 64
  hrd : Covers (pdRd t) (t.rd ++ t.wr)
  hwr : Covers (pdWr t) t.wr
  hk : Spec.Rsa.lenValid (t.gpr .a1).toNat
  h6 : (t.gpr .a3).toNat = Spec.Rsa.precomputedWords (t.gpr .a1).toNat
  h10 : (t.gpr .a7).toNat = (t.gpr .a1).toNat
  he1 : 1 ≤ (t.gpr .a5).toNat
  he2 : (t.gpr .a5).toNat ≤ (t.gpr .a1).toNat
  hs : Spec.Rsa.publicScratchWords (t.gpr .a1).toNat ≤ (stackArg t 1).toNat
  al2 : (t.gpr .a2).toNat % 8 = 0
  al0 : (stackArg t 0).toNat % 8 = 0

theorem PdOk.pre {t : State} (h : PdOk t) :
    (Spec.Rsa.publicPrecomputedCheckedContract abi).pre (t.callEntry.withRegions (pdRd t) (pdWr t)) := by
  have hl := h.hl
  sig_pre [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs,
    stackArgs_two, List.append_eq]
  simp only [Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false,
    Bool.true_or, Bool.false_or, List.cons_append, List.nil_append, Sig.conj, List.append_nil]
  exact ⟨h.spal, h.sp, rfl, rfl, hl.on, hl.oe, ⟨hl.oi, hl.os, hl.oa, hl.ns, hl.es, hl.is, hl.sa⟩,
    hl.wo, hl.wn, hl.we, hl.wi, hl.ws, h.hk, h.h6, h.h10, h.he1, h.he2, h.hs, h.al2, h.al0⟩

/-- The correctness of `vg_rsa_public_precomputed_checked`, from its artifact. -/
theorem pd_correct : ∀ s, (Spec.Rsa.publicPrecomputedCheckedContract abi).pre s →
    ∃ t s', Exec isa Impl.Bignum.RISCV64.PublicChecked.publicChecked s t s' ∧ abiPreserved s s' ∧
      (Spec.Rsa.publicPrecomputedCheckedContract abi).post s s' :=
  Proof.Bignum.RISCV64.Pub.publicChecked_verified.1

/-- A call of `vg_rsa_public_precomputed_checked`. Its result is that of any
modulus whose values `pre` holds. -/
theorem pdCall {t : State} {Q : State → Prop} (h : PdOk t)
    (hQ : ∀ s', s'.rd = t.rd → s'.wr = t.wr → s'.sp = t.sp → Frame (pdWr t) t.mem s'.mem →
      (∀ r ∈ preserved, s'.gpr r = t.gpr r) →
      (∀ nB : List Byte, nB.length = (t.gpr .a1).toNat →
        Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt t.mem (t.gpr .a2) (t.gpr .a3).toNat) →
        Spec.Rsa.written s'.mem (t.gpr .a0) (t.gpr .a1).toNat ((s'.gpr .a0).setWidth 32)
          (Spec.Rsa.publicOpChecked nB (Spec.Rsa.bytesAt t.mem (t.gpr .a4) (t.gpr .a5).toNat)
            (Spec.Rsa.bytesAt t.mem (t.gpr .a6) (t.gpr .a1).toNat))) → Q s') :
    WP isa Impl.RsaPkcs1Sig.RISCV64.pubCall t Q := by
  refine WP.call (k := Spec.Rsa.publicPrecomputedCheckedContract abi) pd_correct h.pre
    (Covers.append_left (Covers.trans h.hrd (Covers.refl _)) (Covers.right h.hwr)) h.hwr ?_
  intro s' hrd' hwr' hsp' hf hpres _ hpost
  sig_post [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs,
    stackArgs_two, List.append_eq] at hpost
  exact hQ s' hrd' hwr' hsp' hf hpres hpost

/-- What two runs agree on at a call of `vg_rsa_public_precomputed_checked`:
the stack pointer, the argument registers and its two stack arguments. -/
structure ArgsEq (t₁ t₂ : State) : Prop where
  sp : t₁.sp = t₂.sp
  gpr : ∀ r ∈ argRegs, t₁.gpr r = t₂.gpr r
  a0 : stackArg t₁ 0 = stackArg t₂ 0
  a1 : stackArg t₁ 1 = stackArg t₂ 1

/-- Two calls of `vg_rsa_public_precomputed_checked` leak alike if their
arguments, the precomputed values and the bytes of `e` agree. -/
theorem pdCallCT {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → PdOk t₁ ∧ PdOk t₂ ∧ ArgsEq t₁ t₂ ∧
      Spec.Rsa.wordsAt t₁.mem (t₁.gpr .a2) (t₁.gpr .a3).toNat =
        Spec.Rsa.wordsAt t₂.mem (t₂.gpr .a2) (t₂.gpr .a3).toNat ∧
      Spec.Rsa.bytesAt t₁.mem (t₁.gpr .a4) (t₁.gpr .a5).toNat =
        Spec.Rsa.bytesAt t₂.mem (t₂.gpr .a4) (t₂.gpr .a5).toNat) :
    RelCT isa P Impl.RsaPkcs1Sig.RISCV64.pubCall fun _ _ => True := by
  refine RelCT.callEx pd_correct Proof.Bignum.RISCV64.Pub.publicChecked_verified.2.1 fun t₁ t₂ hp => ?_
  obtain ⟨h₁, h₂, he, hn, hE⟩ := hP t₁ t₂ hp
  refine ⟨_, _, _, _, h₁.pre, h₂.pre, ?_,
    Covers.append_left (Covers.trans h₁.hrd (Covers.refl _)) (Covers.right h₁.hwr), h₁.hwr,
    Covers.append_left (Covers.trans h₂.hrd (Covers.refl _)) (Covers.right h₂.hwr), h₂.hwr⟩
  sig_pub [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs,
    stackArgs_two, List.append_eq]
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  exact ⟨he.sp, by rw [hn, hE], he.gpr _ (by decide), he.gpr _ (by decide), he.gpr _ (by decide),
    he.gpr _ (by decide), he.gpr _ (by decide), he.gpr _ (by decide), he.gpr _ (by decide),
    he.gpr _ (by decide), he.a0, he.a1⟩

end VG.Proof.RsaPkcs1Sig.RISCV64

/-!
# `vg_rsa_pkcs1_verify_precomputed` on RISC-V: the precondition

Untrusted: everything here is checked by Lean. `PreV s`: the shared
contract's precondition (`verifyPrecomputedContract`, with the stack of the
frame, `frameBytes`), by name (`preV_of`). As on PPC64LE
(`Proof/RsaPkcs1Sig/PPC64LE/VerifyPre.lean`).
-/


namespace VG.Proof.RsaPkcs1Sig.RISCV64.Ver

open VG VG.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64

theorem stackArgs_five (s : State) :
    List.map (stackArg s) (List.range 5) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4] := rfl

/-- The buffers: `n`, `e`, the hash value, the signature and the
precomputed values (the working space, the arguments on the stack and the
stack the function uses are `sR`, `aR` and `kR`). -/
abbrev nR (s : State) : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
abbrev dR (s : State) : Region := ⟨s.gpr .a5, (s.gpr .a6).toNat⟩
abbrev gR (s : State) : Region := ⟨s.gpr .a7, (stackArg s 0).toNat⟩
abbrev pR (s : State) : Region := ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩

/-- What the code needs of `verifyPrecomputedContract.pre`, by name: the
buffers are readable or writable, apart from each other where one is written
and from the stack the function uses, aligned where they hold words, and do
not wrap around; the lengths are within bounds. -/
structure PreV (s : State) : Prop where
  spal : s.sp.toNat % 16 = 0
  sp1 : frameBytes ≤ s.sp.toNat
  sp2 : s.sp.toNat + 40 ≤ 2 ^ 64
  hrd : s.rd = [nR s, eR s, dR s, gR s, pR s, aR s]
  hwr : s.wr = [sR s]
  ns : (nR s).Disjoint (sR s)
  es : (eR s).Disjoint (sR s)
  ds : (dR s).Disjoint (sR s)
  gs : (gR s).Disjoint (sR s)
  sp : (sR s).Disjoint (pR s)
  sa : (sR s).Disjoint (aR s)
  kn : (kR s).Disjoint (nR s)
  ke : (kR s).Disjoint (eR s)
  kd : (kR s).Disjoint (dR s)
  kg : (kR s).Disjoint (gR s)
  ks : (kR s).Disjoint (sR s)
  kp : (kR s).Disjoint (pR s)
  ka : (kR s).Disjoint (aR s)
  wn : (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64
  we : (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64
  wd : (s.gpr .a5).toNat + (s.gpr .a6).toNat ≤ 2 ^ 64
  wg : (s.gpr .a7).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  ws : (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64
  wp : (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .a1).toNat
  k2 : (s.gpr .a1).toNat ≤ 1024
  e1 : 1 ≤ (s.gpr .a3).toNat
  e2 : (s.gpr .a3).toNat ≤ (s.gpr .a1).toNat
  hs : Spec.Rsa.publicScratchWords (s.gpr .a1).toNat ≤ (stackArg s 2).toNat
  hp : (stackArg s 4).toNat = Spec.Rsa.precomputedWords (s.gpr .a1).toNat
  al1 : (stackArg s 1).toNat % 8 = 0
  al3 : (stackArg s 3).toNat % 8 = 0

theorem preV_of {s : State} (h : (Spec.RsaPkcs1Sig.verifyPrecomputedContract abi frameBytes).pre s) : PreV s := by
  have e : frameBytes = 2127 + 1 := rfl
  rw [e] at h
  sig_pre [Spec.RsaPkcs1Sig.verifyPrecomputedContract, Spec.RsaPkcs1Sig.verifyPrecomputedSig, abi, argRegs,
    stackArgs_five, List.append_eq, List.range, List.range.loop] at h
  obtain ⟨spal, sp1, sp2, hrd, hwr, ns, es, ds, gs, sp, sa, kn, ke, kd, kg, ks, kp, ka, wn, we, wd, wg, ws, wp,
    ⟨k1, k2⟩, e1, e2, hs, hp, al1, al3⟩ := h
  exact ⟨spal, sp1, sp2, hrd, hwr, ns, es, ds, gs, sp, sa, kn, ke, kd, kg, ks, kp, ka, wn, we, wd, wg, ws, wp, k1,
    k2, e1, e2, hs, hp, al1, al3⟩

end VG.Proof.RsaPkcs1Sig.RISCV64.Ver


namespace VG.Proof.RsaPkcs1Sig.RISCV64

open VG VG.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64

/-- The low 32 bits of `x`, zero-extended. -/
abbrev zx (x : BitVec 64) : BitVec 64 := (x.setWidth 32).setWidth 64

theorem zx_toNat (x : BitVec 64) : (zx x).toNat = (x.setWidth 32).toNat := by
  simp only [zx, BitVec.toNat_setWidth]; omega

theorem zext_eq (x : BitVec 64) : x <<< 32 >>> 32 = zx x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth]
  omega

section
variable {s : State}

/-- The frame's base is aligned. -/
theorem fb_al (h1 : s.sp.toNat % 16 = 0) (h2 : frameBytes ≤ s.sp.toNat) : (fb s).toNat % 16 = 0 := by
  have := fb_toNat h2; unfold frameBytes at *; omega

theorem fb_al8 (h1 : s.sp.toNat % 16 = 0) (h2 : frameBytes ≤ s.sp.toNat) {d : Nat} (hd : d % 8 = 0) :
    (fb s + BitVec.ofNat 64 d).toNat % 8 = 0 :=
  Spill.al8 (by have := fb_al h1 h2; omega) hd

theorem arg_al (h1 : s.sp.toNat % 16 = 0) (j : Nat) : (stackArgAddr s j).toNat % 8 = 0 := by
  simp only [stackArgAddr, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := s.sp.isLt
  omega

end

namespace Ver

open VG.Impl.RsaPkcs1Sig.RISCV64.Precomputed

/-- In the frame, `k`, `hash`, `digest` and `digest_len` kept. -/
abbrev VMid (s t : State) : Prop :=
  Mid (sR s) s (s.gpr .a1) (zx (s.gpr .a4)) (s.gpr .a5) (s.gpr .a6) t

/-- At the call: the arguments of `vg_rsa_public_precomputed_checked`, `EM₁`,
`n_len`, `pre`, `pre_len`, `e`, `e_len`, `sig` and `n_len`, and on the stack
`scratch` and `scratch_len`. -/
structure AtCall (s t : State) : Prop extends
    Mid (sR s) s (s.gpr .a1) (zx (s.gpr .a4)) (s.gpr .a5) (s.gpr .a6) t where
  g0 : t.gpr .a0 = fb s + BitVec.ofNat 64 oEM1
  g1 : t.gpr .a1 = s.gpr .a1
  g2 : t.gpr .a2 = stackArg s 3
  g3 : t.gpr .a3 = stackArg s 4
  g4 : t.gpr .a4 = s.gpr .a2
  g5 : t.gpr .a5 = s.gpr .a3
  g6 : t.gpr .a6 = s.gpr .a7
  g7 : t.gpr .a7 = s.gpr .a1
  sa0 : stackArg t 0 = stackArg s 1
  sa1 : stackArg t 1 = stackArg s 2

section
variable {s : State}

/-- The stack arguments are readable. -/
theorem arg_rd (hp : PreV s) (rs : List Region) {j : Nat} (hj : j < 5) :
    InRegions (s.rd ++ rs) (stackArgAddr s j) 8 :=
  ⟨aR s, List.mem_append_left _ (by rw [hp.hrd]; simp), in_aR hj⟩

/-- A stack argument, in memory changed only in the frame. -/
theorem arg_frame (hp : PreV s) {m : Mem} (h : Frame [kR s] s.mem m) {j : Nat} (hj : j < 5) :
    m.readW (stackArgAddr s j) 64 = stackArg s j :=
  h.readW (in_aR hj) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.ka.symm) (by decide)

end

theorem pubArgs_ok {s u : State} (hp : PreV s) (hsp : u.sp = fb s) (hwr : u.wr = kR s :: s.wr)
    (hrd : u.rd = s.rd) (hm : Frame [kR s] s.mem u.mem) (hg : ∀ r, r ∉ [Reg.t0] → u.gpr r = s.gpr r) :
    WP isa (.block pubArgs) u (AtCall s) := by
  have hfa := fb_al hp.spal hp.sp1
  unfold pubArgs
  simp only [List.append_assoc]
  refine save_ok hsp hwr (by omega) hm (fun r hr => hg r (by revert r; decide)) fun v kv v0 fv sv => ?_
  have gv : ∀ r, r ∉ [Reg.t0] → v.gpr r = s.gpr r := fun r hr => by
    rw [kv.gpr r hr, hg r hr]
  simp only [zext, List.cons_append, List.nil_append]
  refine wp_mov fun v₁ o₁ e₁ => wp_sll fun v₂ o₂ e₂ => wp_srl fun v₃ o₃ e₃ => wp_mov fun v₄ o₄ e₄ =>
    wp_mov fun v₅ o₅ e₅ => wp_mov fun v₆ o₆ e₆ => wp_mov fun v₇ o₇ e₇ => wp_mov fun v₈ o₈ e₈ =>
    wp_mov fun v₉ o₉ e₉ => ?_
  have O₉ : Only [.s1, .s2, .s2, .s3, .s4, .a4, .a5, .a6, .a7] v v₉ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans (o₇.trans (o₈.trans o₉)))))))).mono
  have t0₉ : v₉.gpr .t0 = fb s := by rw [O₉.get .t0, v0]
  have rd₉ : v₉.rd = s.rd := by rw [O₉.rd, kv.rd, hrd]
  have wr₉ : v₉.wr = kR s :: s.wr := by rw [O₉.wr, kv.wr, hwr]
  have sp₉ : v₉.sp = fb s := by rw [O₉.sp, kv.sp, hsp]
  unfold callTail argBase
  simp only [List.cons_append, List.nil_append]
  refine wp_addSp fun w₁ p₁ f₁ => wp_addi fun w₂ p₂ f₂ => ?_
  have t6₂ : w₂.gpr .t6 = stackArgAddr s 0 := by
    rw [f₂, f₁, sp₉, stackArgAddr_fb, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; rfl
  have P₂ : Only [.t6, .t6] v₉ w₂ := p₁.trans p₂
  refine wp_ld (a := stackArgAddr s 1) (by rw [t6₂, stackArgAddr_eq s 1]) (arg_al hp.spal 1)
    (by rw [P₂.rd, rd₉]; exact arg_rd hp _ (by decide)) fun v₁₀ o₁₀ e₁₀ => ?_
  rw [P₂.mem, O₉.mem, arg_frame hp fv (by decide)] at e₁₀
  refine wp_sd (a := fb s + BitVec.ofNat 64 0) (by rw [o₁₀.get .t0, P₂.get .t0, t0₉])
    (fb_al8 hp.spal hp.sp1 (by decide))
    (by rw [o₁₀.wr, P₂.wr, wr₉]; exact in_fr s _ (by decide)) fun v₁₁ m₁₁ => ?_
  have f₁₁ : Frame [⟨fb s + BitVec.ofNat 64 0, 16⟩] v.mem v₁₁.mem := by
    rw [m₁₁.mem, o₁₀.mem, P₂.mem, O₉.mem]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _
      (Offset.contains (fb s) (d := 0) (e := 0) (by decide) (by decide) (by decide))
  have K₁₁ : Frame [kR s] s.mem v₁₁.mem := fv.trans (f₁₁.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, frame_sub s (by decide)⟩)
  have g₁₁ : ∀ r, r ∉ [Reg.t1] → v₁₁.gpr r = w₂.gpr r := fun r hr => by rw [m₁₁.gpr, o₁₀.gpr r hr]
  have rd₁₁ : v₁₁.rd = s.rd := by rw [m₁₁.rd, o₁₀.rd, P₂.rd, rd₉]
  have wr₁₁ : v₁₁.wr = kR s :: s.wr := by rw [m₁₁.wr, o₁₀.wr, P₂.wr, wr₉]
  refine wp_ld (a := stackArgAddr s 2) (by rw [g₁₁ .t6 (by decide), t6₂, stackArgAddr_eq s 2])
    (arg_al hp.spal 2) (by rw [rd₁₁]; exact arg_rd hp _ (by decide)) fun v₁₂ o₁₂ e₁₂ => ?_
  rw [arg_frame hp K₁₁ (by decide)] at e₁₂
  refine wp_sd (a := fb s + BitVec.ofNat 64 8) (by rw [o₁₂.get .t0, g₁₁ .t0 (by decide), P₂.get .t0, t0₉])
    (fb_al8 hp.spal hp.sp1 (by decide))
    (by rw [o₁₂.wr, wr₁₁]; exact in_fr s _ (by decide)) fun v₁₃ m₁₃ => ?_
  have f₁₃ : Frame [⟨fb s + BitVec.ofNat 64 0, 16⟩] v.mem v₁₃.mem := by
    rw [m₁₃.mem, o₁₂.mem]
    exact f₁₁.writeW (List.mem_singleton_self _) _
      (Offset.contains (fb s) (d := 8) (e := 0) (by decide) (by decide) (by decide))
  have K₁₃ : Frame [kR s] s.mem v₁₃.mem := fv.trans (f₁₃.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, frame_sub s (by decide)⟩)
  have g₁₃ : ∀ r, r ∉ [Reg.t1] → v₁₃.gpr r = w₂.gpr r := fun r hr => by
    rw [m₁₃.gpr, o₁₂.gpr r hr, g₁₁ r hr]
  have rd₁₃ : v₁₃.rd = s.rd := by rw [m₁₃.rd, o₁₂.rd, rd₁₁]
  refine wp_ld (a := stackArgAddr s 3) (by rw [g₁₃ .t6 (by decide), t6₂, stackArgAddr_eq s 3])
    (arg_al hp.spal 3) (by rw [rd₁₃]; exact arg_rd hp _ (by decide)) fun v₁₄ o₁₄ e₁₄ => ?_
  refine wp_ld (a := stackArgAddr s 4) (by rw [o₁₄.get .t6, g₁₃ .t6 (by decide), t6₂, stackArgAddr_eq s 4])
    (arg_al hp.spal 4) (by rw [o₁₄.rd, rd₁₃]; exact arg_rd hp _ (by decide)) fun v₁₅ o₁₅ e₁₅ => ?_
  refine wp_addi fun v₁₆ o₁₆ e₁₆ => wp_mov fun v₁₇ o₁₇ e₁₇ => wp_nil ?_
  rw [arg_frame hp K₁₃ (by decide)] at e₁₄
  rw [o₁₄.mem, arg_frame hp K₁₃ (by decide)] at e₁₅
  have O₁₇ : Only [.a2, .a3, .a0, .a1] v₁₃ v₁₇ := (o₁₄.trans (o₁₅.trans (o₁₆.trans o₁₇))).mono
  have g₁₇ : ∀ r, r ∉ [Reg.a2, .a3, .a0, .a1, .t1, .t6, .t6] → v₁₇.gpr r = v₉.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [O₁₇.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1]), g₁₃ r (by simp [hr.2.2.2.2.1]),
      P₂.gpr r (by simp [hr.2.2.2.2.2.1])]
  have mem₁₇ : v₁₇.mem = v₁₃.mem := O₁₇.mem
  have hd : ∀ r ∈ [(⟨fb s + BitVec.ofNat 64 0, 16⟩ : Region)], ∀ {e k : Nat}, 16 ≤ e → e + k ≤ frameBytes →
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 e, k⟩ r := fun r hr e k h₁ h₂ => by
    rw [List.mem_singleton.mp hr]
    exact Offset.disjoint _ (.inr (by omega)) (by unfold frameBytes at h₂; omega) (by decide)
  have t0₁₃ : v₁₃.gpr .t0 = fb s := by rw [g₁₃ .t0 (by decide), P₂.get .t0, t0₉]
  refine {
    sp := by rw [O₁₇.sp, m₁₃.sp, o₁₂.sp, m₁₁.sp, o₁₀.sp, P₂.sp, sp₉]
    rd := by rw [O₁₇.rd, rd₁₃]
    wr := by rw [O₁₇.wr, m₁₃.wr, o₁₂.wr, wr₁₁]
    s1 := by
      rw [g₁₇ .s1 (by decide), o₉.get .s1, o₈.get .s1, o₇.get .s1, o₆.get .s1, o₅.get .s1, o₄.get .s1,
        o₃.get .s1, o₂.get .s1, e₁, gv .a1 (by decide)]
    s2 := by
      rw [g₁₇ .s2 (by decide), o₉.get .s2, o₈.get .s2, o₇.get .s2, o₆.get .s2, o₅.get .s2, o₄.get .s2,
        e₃, e₂, o₁.get .a4, gv .a4 (by decide), zext_eq]
    s3 := by
      rw [g₁₇ .s3 (by decide), o₉.get .s3, o₈.get .s3, o₇.get .s3, o₆.get .s3, o₅.get .s3, e₄,
        o₃.get .a5, o₂.get .a5, o₁.get .a5, gv .a5 (by decide)]
    s4 := by
      rw [g₁₇ .s4 (by decide), o₉.get .s4, o₈.get .s4, o₇.get .s4, o₆.get .s4, e₅, o₄.get .a6,
        o₃.get .a6, o₂.get .a6, o₁.get .a6, gv .a6 (by decide)]
    hi := fun r hr => by
      have h₁ : r ∉ [Reg.a2, .a3, .a0, .a1, .t1, .t6, .t6] := by revert r; decide
      have h₃ : r ∉ [Reg.s1, .s2, .s2, .s3, .s4, .a4, .a5, .a6, .a7] := by revert r; decide
      have h₄ : r ∉ [Reg.t0] := by revert r; decide
      rw [g₁₇ r h₁, O₉.gpr r h₃, gv r h₄]
    mem := by
      rw [mem₁₇]
      exact K₁₃.mono fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..
    sv := by
      rw [mem₁₇]
      exact sv.frame_in saved_offs f₁₃ fun r hr => hd r hr (by decide) (by decide)
    g0 := by rw [o₁₇.get .a0, e₁₆, o₁₅.get .t0, o₁₄.get .t0, t0₁₃]
    g1 := by rw [e₁₇, o₁₆.get .s1, o₁₅.get .s1, o₁₄.get .s1, g₁₃ .s1 (by decide), P₂.get .s1,
      o₉.get .s1, o₈.get .s1, o₇.get .s1, o₆.get .s1, o₅.get .s1, o₄.get .s1, o₃.get .s1, o₂.get .s1, e₁,
      gv .a1 (by decide)]
    g2 := by rw [o₁₇.get .a2, o₁₆.get .a2, o₁₅.get .a2, e₁₄]
    g3 := by rw [o₁₇.get .a3, o₁₆.get .a3, e₁₅]
    g4 := by
      rw [g₁₇ .a4 (by decide), o₉.get .a4, o₈.get .a4, o₇.get .a4, e₆, o₅.get .a2, o₄.get .a2, o₃.get .a2,
        o₂.get .a2, o₁.get .a2, gv .a2 (by decide)]
    g5 := by
      rw [g₁₇ .a5 (by decide), o₉.get .a5, o₈.get .a5, e₇, o₆.get .a3, o₅.get .a3, o₄.get .a3, o₃.get .a3,
        o₂.get .a3, o₁.get .a3, gv .a3 (by decide)]
    g6 := by
      rw [g₁₇ .a6 (by decide), o₉.get .a6, e₈, o₇.get .a7, o₆.get .a7, o₅.get .a7, o₄.get .a7, o₃.get .a7,
        o₂.get .a7, o₁.get .a7, gv .a7 (by decide)]
    g7 := by
      rw [g₁₇ .a7 (by decide), e₉, o₈.get .a1, o₇.get .a1, o₆.get .a1, o₅.get .a1, o₄.get .a1, o₃.get .a1,
        o₂.get .a1, o₁.get .a1, gv .a1 (by decide)]
    sa0 := by
      show v₁₇.mem.readW (v₁₇.sp + BitVec.ofNat 64 (8 * 0)) 64 = _
      rw [O₁₇.sp, m₁₃.sp, o₁₂.sp, m₁₁.sp, o₁₀.sp, P₂.sp, sp₉, mem₁₇, m₁₃.mem, o₁₂.mem,
        Mem.readW_writeW_sep (Offset.sep _ (.inl (by decide)) (by decide) (by decide)) (by decide), m₁₁.mem,
        Mem.readW_writeW_self64]
      exact e₁₀
    sa1 := by
      show v₁₇.mem.readW (v₁₇.sp + BitVec.ofNat 64 (8 * 1)) 64 = _
      rw [O₁₇.sp, m₁₃.sp, o₁₂.sp, m₁₁.sp, o₁₀.sp, P₂.sp, sp₉, mem₁₇, m₁₃.mem, Mem.readW_writeW_self64]
      exact e₁₂ }

/-- The values of the modulus `pre` holds, which the result is about. -/
def PreOk (s : State) : Prop :=
  Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) =
    some (Spec.Rsa.wordsAt s.mem (stackArg s 3) (stackArg s 4).toNat)

/-- RSAVP1 of the signature, as the entry state gives it. -/
def pubOut (s : State) : Option (List Byte) :=
  Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .a7) (s.gpr .a1).toNat)

/-- `EM₁`, of `k` bytes. -/
abbrev em1R (s : State) : Region := ⟨fb s + BitVec.ofNat 64 oEM1, (s.gpr .a1).toNat⟩

theorem em1_sub {s : State} (hp : PreV s) : Region.Sub (em1R s) (kR s) :=
  frame_sub s (by have := hp.k2; unfold oEM1 frameBytes; omega)

theorem pdOk_of {s t : State} (hp : PreV s) (ha : AtCall s t) (hsig : stackArg s 0 = s.gpr .a1) : PdOk t := by
  have hk1 := hp.k1; have hk2 := hp.k2
  have hfb := fb_toNat hp.sp1
  have hfa := fb_al hp.spal hp.sp1
  have hgK : (kR s).Disjoint ⟨s.gpr .a7, (s.gpr .a1).toNat⟩ := by have := hp.kg; rwa [gR, hsig] at this
  have hgS : (⟨s.gpr .a7, (s.gpr .a1).toNat⟩ : Region).Disjoint (sR s) := by have := hp.gs; rwa [gR, hsig] at this
  have hsa : stackArgAddr t 0 = fb s + BitVec.ofNat 64 0 := by rw [stackArgAddr, ha.sp]
  refine ⟨?hl, ?spal, ?sp, ?hrd, ?hwr, ?hk, ?h6, ?h10, ?he1, ?he2, ?hs, ?al2, ?al0⟩
  case hl =>
    rw [ha.g0, ha.g1, ha.g2, ha.g3, ha.g4, ha.g5, ha.g6, ha.g7, ha.sa0, ha.sa1, hsa]
    exact {
      on := hp.kp.sub_left (em1_sub hp)
      oe := hp.ke.sub_left (em1_sub hp)
      oi := hgK.sub_left (em1_sub hp)
      os := hp.ks.sub_left (em1_sub hp)
      oa := Offset.disjoint _ (.inr (by decide)) (by unfold oEM1 frameBytes at *; omega) (by decide)
      ns := hp.sp.symm
      es := hp.es
      is := hgS
      sa := (hp.ks.sub_left (frame_sub s (by decide))).symm
      wo := by
        show (fb s + BitVec.ofNat 64 oEM1).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oEM1 frameBytes at *; omega
      wn := hp.wp
      we := hp.we
      wi := by have := hp.wg; rwa [hsig] at this
      ws := hp.ws }
  case spal => rw [ha.sp]; exact hfa
  case sp => rw [ha.sp]; unfold frameBytes at hfb; omega
  case hrd =>
    simp only [pdRd]
    rw [ha.g2, ha.g3, ha.g4, ha.g5, ha.g6, ha.g7, hsa, ha.rd, ha.wr]
    have hm : ∀ r ∈ s.rd, Covers [r] (s.rd ++ (kR s :: s.wr)) := fun r hr =>
      Covers.left (Covers.of_mem fun x hx => by rw [List.mem_singleton.mp hx]; exact hr)
    have hg : (⟨s.gpr .a7, (s.gpr .a1).toNat⟩ : Region) ∈ s.rd := by rw [hp.hrd, ← hsig]; simp
    refine Covers.cons (hm _ (by rw [hp.hrd]; simp)) (Covers.cons (hm _ (by rw [hp.hrd]; simp))
      (Covers.cons (hm _ hg) (Covers.one (in_fr' s _ _ (by decide)) |>.cons Covers.nil)))
  case hwr =>
    simp only [pdWr]
    rw [ha.g0, ha.g1, ha.sa0, ha.sa1, ha.wr]
    exact Covers.cons (Covers.one (in_fr s _ (by unfold oEM1 frameBytes; omega)))
      (Covers.of_mem fun x hx => by
        rw [List.mem_singleton.mp hx]; exact List.mem_cons_of_mem _ (by rw [hp.hwr]; simp))
  case hk => rw [ha.g1]; exact ⟨hk1, hk2⟩
  case h6 => rw [ha.g3, ha.g1]; exact hp.hp
  case h10 => rw [ha.g7, ha.g1]
  case he1 => rw [ha.g5]; exact hp.e1
  case he2 => rw [ha.g5, ha.g1]; exact hp.e2
  case hs => rw [ha.g1, ha.sa1]; exact hp.hs
  case al2 => rw [ha.g2]; exact hp.al3
  case al0 => rw [ha.sa0]; exact hp.al1

/-- After the call: `VMid`, and `EM₁` written with RSAVP1's result if `pre`
holds the modulus' values. -/
structure AfterCall (s t : State) : Prop extends
    Mid (sR s) s (s.gpr .a1) (zx (s.gpr .a4)) (s.gpr .a5) (s.gpr .a6) t where
  res : PreOk s →
    Spec.Rsa.written t.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .a1).toNat ((t.gpr .a0).setWidth 32) (pubOut s)

theorem call_ok {s t : State} (hp : PreV s) (ha : AtCall s t) (hsig : stackArg s 0 = s.gpr .a1) :
    WP isa pubCall t (AfterCall s) := by
  have hk2 := hp.k2
  refine pdCall (pdOk_of hp ha hsig) fun s' hrd' hwr' hsp' hf hpres hpost => ?_
  simp only [pdWr] at hf
  rw [ha.g0, ha.g1, ha.sa0, ha.sa1] at hf
  have hfm := ha.toMid.frameMem hp.ks (e := oEM1) (n := (s.gpr .a1).toNat) (by decide)
    (by unfold oEM1 frameBytes; omega) hf
  have hfr0 : Frame [kR s, sR s] s.mem t.mem := ha.mem
  have hgK : (kR s).Disjoint ⟨s.gpr .a7, (s.gpr .a1).toNat⟩ := by have := hp.kg; rwa [gR, hsig] at this
  have hgS : (⟨s.gpr .a7, (s.gpr .a1).toNat⟩ : Region).Disjoint (sR s) := by have := hp.gs; rwa [gR, hsig] at this
  refine { ha.toMid.of (fun r hr => hpres r (by revert r; decide)) hsp' hrd' hwr' hfm.1 hfm.2 with
    res := fun hc => ?_ }
  have hw : Spec.Rsa.wordsAt t.mem (t.gpr .a2) (t.gpr .a3).toNat =
      Spec.Rsa.wordsAt s.mem (stackArg s 3) (stackArg s 4).toNat := by
    rw [ha.g2, ha.g3]; exact words_of_frame hfr0 hp.kp hp.sp hp.wp
  have := hpost (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat)
    (by rw [ha.g1, Proof.RsaPkcs1Sig.bytesAt_length]) (by rw [hw]; exact hc)
  rw [ha.g0, ha.g1, ha.g4, ha.g5, ha.g6, bytes_of_frame hfr0 hp.ke hp.es.symm (by have := hp.we; omega),
    bytes_of_frame hfr0 hgK hgS.symm (by omega)] at this
  exact this

end Ver

end VG.Proof.RsaPkcs1Sig.RISCV64

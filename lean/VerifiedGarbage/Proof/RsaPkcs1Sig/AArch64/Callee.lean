import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.Sig

/-!
# The RSA operations the signatures call, on AArch64

The signature functions call verified implementations of the RSA operations
(`vg_rsa_public_checked`, `vg_rsa_public_precomputed_checked` and
`vg_rsa_private_checked`, or a variant of one of them), of which they need
only what their artifacts state: that the code is `Verified` for the shared
contract of `Spec/Rsa/Contract.lean` with some `stack`, and that its frames
fit in that stack (`Callee`). The call lemmas (`pubCall`, …) evaluate those
contracts (`sig_pre`, `sig_post`) into facts about the registers at the
call, so the callers' proofs never see `Sig.contract`.
-/

namespace VG.Proof.RsaPkcs1Sig.AArch64

open VG VG.AArch64

/-- A verified function with the contract `k stack` (one of the shared
contracts, for the `stack` its calls and frames use), whose frames fit in
that stack. -/
structure Callee (k : Nat → Contract isa) where
  name : String
  code : Prog isa
  stack : Nat
  verified : Verified AArch64.target code (k stack)
  depth : 16 * code.aarch64Depth ≤ stack
  pos : 0 < stack
  le : stack ≤ 2 ^ 20
  /-- What the names of the caller's instances end with, and the CPU
  features the code requires. -/
  suffix : String
  features : List String

/-- `vg_rsa_public_checked`. -/
abbrev PubChecked := Callee fun K => Spec.Rsa.publicCheckedContract abi K

theorem stackArgs_two (s : State) :
    List.map (stackArg s) (List.range 2) = [stackArg s 0, stackArg s 1] := rfl

theorem stackArg_entry (t : State) (rd wr : List Region) (i : Nat) :
    stackArg (t.callEntry.withRegions rd wr) i = stackArg t i := rfl

theorem stackArgAddr_entry (t : State) (rd wr : List Region) (i : Nat) :
    stackArgAddr (t.callEntry.withRegions rd wr) i = stackArgAddr t i := rfl

theorem sa0 (t : State) : stackArgAddr t 0 = t.sp := by simp [stackArgAddr]

/-- What the buffers of a call of `vg_rsa_public_checked` (or
`vg_rsa_public_precomputed_checked`, whose `n` is `pre`) need: they are
apart where one is written, from the arguments on the stack and from the
`K` bytes below the stack pointer, and do not wrap around. `o`, `n`, `e`,
`i`, `sc`: the addresses of `out`, `n`, `e`, the input and the working
space; `ol`, `nl`, `el`, `il`, `sl`: their lengths in bytes. -/
structure PubLay (sp : Addr) (K : Nat) (o n e i sc : Addr) (ol nl el il sl : Nat) : Prop where
  sp1 : K ≤ sp.toNat
  sp2 : sp.toNat + 16 ≤ 2 ^ 64
  on : (⟨o, ol⟩ : Region).Disjoint ⟨n, nl⟩
  oe : (⟨o, ol⟩ : Region).Disjoint ⟨e, el⟩
  oi : (⟨o, ol⟩ : Region).Disjoint ⟨i, il⟩
  os : (⟨o, ol⟩ : Region).Disjoint ⟨sc, sl⟩
  oa : (⟨o, ol⟩ : Region).Disjoint ⟨sp, 16⟩
  ns : (⟨n, nl⟩ : Region).Disjoint ⟨sc, sl⟩
  es : (⟨e, el⟩ : Region).Disjoint ⟨sc, sl⟩
  is : (⟨i, il⟩ : Region).Disjoint ⟨sc, sl⟩
  sa : (⟨sc, sl⟩ : Region).Disjoint ⟨sp, 16⟩
  ko : (⟨sp - BitVec.ofNat 64 K, K⟩ : Region).Disjoint ⟨o, ol⟩
  kn : (⟨sp - BitVec.ofNat 64 K, K⟩ : Region).Disjoint ⟨n, nl⟩
  ke : (⟨sp - BitVec.ofNat 64 K, K⟩ : Region).Disjoint ⟨e, el⟩
  ki : (⟨sp - BitVec.ofNat 64 K, K⟩ : Region).Disjoint ⟨i, il⟩
  ks : (⟨sp - BitVec.ofNat 64 K, K⟩ : Region).Disjoint ⟨sc, sl⟩
  ka : (⟨sp - BitVec.ofNat 64 K, K⟩ : Region).Disjoint ⟨sp, 16⟩
  wo : o.toNat + ol ≤ 2 ^ 64
  wn : n.toNat + nl ≤ 2 ^ 64
  we : e.toNat + el ≤ 2 ^ 64
  wi : i.toNat + il ≤ 2 ^ 64
  ws : sc.toNat + sl ≤ 2 ^ 64

/-- The regions a call of `vg_rsa_public_checked` (or of a precomputed
public operation: `pdRd`) reads and writes. -/
abbrev pubRd (t : State) : List Region :=
  [⟨t.gpr .x2, (t.gpr .x3).toNat⟩, ⟨t.gpr .x4, (t.gpr .x5).toNat⟩, ⟨t.gpr .x6, (t.gpr .x7).toNat⟩,
    ⟨t.sp, 16⟩]

abbrev pdRd (t : State) : List Region :=
  [⟨t.gpr .x2, (t.gpr .x3).toNat * 8⟩, ⟨t.gpr .x4, (t.gpr .x5).toNat⟩, ⟨t.gpr .x6, (t.gpr .x7).toNat⟩,
    ⟨t.sp, 16⟩]

abbrev pubWr (t : State) : List Region :=
  [⟨t.gpr .x0, (t.gpr .x1).toNat⟩, ⟨stackArg t 0, (stackArg t 1).toNat * 8⟩]

/-- What a call of `vg_rsa_public_checked` needs at the call: the modulus
`n` of `k` bytes at `x2`, `e` (`el` bytes) at `x4` and the input at `x6`,
`out` at `x0`; the working space and its length in words are the two words
at `sp`. -/
structure PubOk (K : Nat) (t : State) : Prop where
  hl : PubLay t.sp K (t.gpr .x0) (t.gpr .x2) (t.gpr .x4) (t.gpr .x6) (stackArg t 0)
    (t.gpr .x1).toNat (t.gpr .x3).toNat (t.gpr .x5).toNat (t.gpr .x7).toNat ((stackArg t 1).toNat * 8)
  hrd : Covers (pubRd t) (t.rd ++ t.wr)
  hwr : Covers (pubWr t) t.wr
  hk : Spec.Rsa.lenValid (t.gpr .x3).toNat
  h1 : (t.gpr .x1).toNat = (t.gpr .x3).toNat
  h7 : (t.gpr .x7).toNat = (t.gpr .x3).toNat
  he1 : 1 ≤ (t.gpr .x5).toNat
  he2 : (t.gpr .x5).toNat ≤ (t.gpr .x3).toNat
  hs : Spec.Rsa.scratchWords (t.gpr .x3).toNat ≤ (stackArg t 1).toNat

theorem PubOk.pre {K : Nat} {t : State} (hK : 0 < K) (h : PubOk K t) :
    (Spec.Rsa.publicCheckedContract abi K).pre (t.callEntry.withRegions (pubRd t) (pubWr t)) := by
  obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  have hl := h.hl
  sig_pre [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicSig, abi, argRegs, stackArgs_two, List.append_eq]
  simp only [Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false,
    Bool.true_or, Bool.false_or, List.cons_append, List.nil_append, Sig.conj,
    List.append_nil, sa0]
  exact ⟨hl.sp1, hl.sp2, rfl, rfl, hl.on, hl.oe, ⟨hl.oi, hl.os, hl.oa, hl.ns, hl.es, hl.is, hl.sa⟩,
    hl.ko, hl.kn, hl.ke, hl.ki, hl.ks, hl.ka, hl.wo, hl.wn, hl.we, hl.wi, hl.ws, h.hk, h.h1, h.h7, h.he1,
    h.he2, h.hs⟩

/-- A call of `vg_rsa_public_checked`. -/
theorem pubCall (c : PubChecked) {t : State} {Q : State → Prop} (h : PubOk c.stack t)
    (hQ : ∀ s', s'.rd = t.rd → s'.wr = t.wr → s'.sp = t.sp →
      Frame (pubWr t ++ [below t.sp (16 * c.code.aarch64Depth)]) t.mem s'.mem →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = t.gpr r) →
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64) →
      Spec.Rsa.written s'.mem (t.gpr .x0) (t.gpr .x3).toNat ((s'.gpr .x0).setWidth 32)
        (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt t.mem (t.gpr .x2) (t.gpr .x3).toNat)
          (Spec.Rsa.bytesAt t.mem (t.gpr .x4) (t.gpr .x5).toNat)
          (Spec.Rsa.bytesAt t.mem (t.gpr .x6) (t.gpr .x3).toNat)) → Q s') :
    WP isa (.call c.name c.code) t Q := by
  refine WP.callFV (k := Spec.Rsa.publicCheckedContract abi c.stack) c.verified.1 (h.pre c.pos)
    (Covers.append_left (Covers.trans h.hrd (Covers.refl _)) (Covers.right h.hwr)) h.hwr ?_
    (by have := c.le; have := c.depth; omega)
  intro s' hrd' hwr' hsp' hf hpres hvs hpost
  sig_post [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicSig, abi, argRegs, stackArgs_two, List.append_eq] at hpost
  exact hQ s' hrd' hwr' hsp' hf hpres hvs hpost

/-- What two runs agree on at a call of an RSA operation: the stack
pointer, the argument registers, the first `n` arguments on the stack, and
the bytes the callee leaks (`leak`). -/
structure ArgsEq (n : Nat) (t₁ t₂ : State) : Prop where
  sp : t₁.sp = t₂.sp
  gpr : ∀ r ∈ argRegs, t₁.gpr r = t₂.gpr r
  args : ∀ i < n, stackArg t₁ i = stackArg t₂ i

theorem argsEq_regs {n : Nat} {t₁ t₂ : State} (h : ArgsEq n t₁ t₂) :
    t₁.gpr .x0 = t₂.gpr .x0 ∧ t₁.gpr .x1 = t₂.gpr .x1 ∧ t₁.gpr .x2 = t₂.gpr .x2 ∧
      t₁.gpr .x3 = t₂.gpr .x3 ∧ t₁.gpr .x4 = t₂.gpr .x4 ∧ t₁.gpr .x5 = t₂.gpr .x5 ∧
      t₁.gpr .x6 = t₂.gpr .x6 ∧ t₁.gpr .x7 = t₂.gpr .x7 :=
  ⟨h.gpr _ (by decide), h.gpr _ (by decide), h.gpr _ (by decide), h.gpr _ (by decide),
    h.gpr _ (by decide), h.gpr _ (by decide), h.gpr _ (by decide), h.gpr _ (by decide)⟩

/-- Two calls of `vg_rsa_public_checked` leak alike if their arguments and
the bytes of `n` and `e` agree. -/
theorem pubCallCT (c : PubChecked) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → PubOk c.stack t₁ ∧ PubOk c.stack t₂ ∧ ArgsEq 2 t₁ t₂ ∧
      Spec.Rsa.bytesAt t₁.mem (t₁.gpr .x2) (t₁.gpr .x3).toNat =
        Spec.Rsa.bytesAt t₂.mem (t₂.gpr .x2) (t₂.gpr .x3).toNat ∧
      Spec.Rsa.bytesAt t₁.mem (t₁.gpr .x4) (t₁.gpr .x5).toNat =
        Spec.Rsa.bytesAt t₂.mem (t₂.gpr .x4) (t₂.gpr .x5).toNat) :
    RelCT isa P (.call c.name c.code) fun _ _ => True := by
  refine RelCT.callEx c.verified.1 c.verified.2.1 fun t₁ t₂ hp => ?_
  obtain ⟨h₁, h₂, he, hn, hE⟩ := hP t₁ t₂ hp
  refine ⟨_, _, _, _, h₁.pre c.pos, h₂.pre c.pos, ?_,
    Covers.append_left (Covers.trans h₁.hrd (Covers.refl _)) (Covers.right h₁.hwr), h₁.hwr,
    Covers.append_left (Covers.trans h₂.hrd (Covers.refl _)) (Covers.right h₂.hwr), h₂.hwr⟩
  sig_pub [Spec.Rsa.publicCheckedContract, Spec.Rsa.publicSig, abi, argRegs, stackArgs_two, List.append_eq]
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := argsEq_regs he
  exact ⟨he.sp, by rw [hn, hE], e0, e1, e2, e3, e4, e5, e6, e7, he.args 0 (by decide), he.args 1 (by decide)⟩

/-- `vg_rsa_public_precomputed_checked` and its variants. -/
abbrev PdChecked := Callee fun K => Spec.Rsa.publicPrecomputedCheckedContract abi K

/-- What a call of a precomputed public operation needs: as `PubOk`, with
the precomputed values of a modulus (`x3` words at `x2`) for the modulus,
and `k` in `x1`. -/
structure PdOk (K : Nat) (t : State) : Prop where
  hl : PubLay t.sp K (t.gpr .x0) (t.gpr .x2) (t.gpr .x4) (t.gpr .x6) (stackArg t 0)
    (t.gpr .x1).toNat ((t.gpr .x3).toNat * 8) (t.gpr .x5).toNat (t.gpr .x7).toNat ((stackArg t 1).toNat * 8)
  hrd : Covers (pdRd t) (t.rd ++ t.wr)
  hwr : Covers (pubWr t) t.wr
  hk : Spec.Rsa.lenValid (t.gpr .x1).toNat
  h3 : (t.gpr .x3).toNat = Spec.Rsa.precomputedWords (t.gpr .x1).toNat
  h7 : (t.gpr .x7).toNat = (t.gpr .x1).toNat
  he1 : 1 ≤ (t.gpr .x5).toNat
  he2 : (t.gpr .x5).toNat ≤ (t.gpr .x1).toNat
  hs : Spec.Rsa.scratchWords (t.gpr .x1).toNat ≤ (stackArg t 1).toNat

theorem PdOk.pre {K : Nat} {t : State} (hK : 0 < K) (h : PdOk K t) :
    (Spec.Rsa.publicPrecomputedCheckedContract abi K).pre (t.callEntry.withRegions (pdRd t) (pubWr t)) := by
  obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  have hl := h.hl
  sig_pre [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs,
    stackArgs_two, List.append_eq]
  simp only [Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false,
    Bool.true_or, Bool.false_or, List.cons_append, List.nil_append, Sig.conj,
    List.append_nil, sa0]
  exact ⟨hl.sp1, hl.sp2, rfl, rfl, hl.on, hl.oe, ⟨hl.oi, hl.os, hl.oa, hl.ns, hl.es, hl.is, hl.sa⟩,
    hl.ko, hl.kn, hl.ke, hl.ki, hl.ks, hl.ka, hl.wo, hl.wn, hl.we, hl.wi, hl.ws, h.hk, h.h3, h.h7, h.he1,
    h.he2, h.hs⟩

/-- A call of a precomputed public operation. Its result is that of any
modulus whose values `pre` holds. -/
theorem pdCall (c : PdChecked) {t : State} {Q : State → Prop} (h : PdOk c.stack t)
    (hQ : ∀ s', s'.rd = t.rd → s'.wr = t.wr → s'.sp = t.sp →
      Frame (pubWr t ++ [below t.sp (16 * c.code.aarch64Depth)]) t.mem s'.mem →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = t.gpr r) →
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64) →
      (∀ nB : List Byte, nB.length = (t.gpr .x1).toNat →
        Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt t.mem (t.gpr .x2) (t.gpr .x3).toNat) →
        Spec.Rsa.written s'.mem (t.gpr .x0) (t.gpr .x1).toNat ((s'.gpr .x0).setWidth 32)
          (Spec.Rsa.publicOpChecked nB (Spec.Rsa.bytesAt t.mem (t.gpr .x4) (t.gpr .x5).toNat)
            (Spec.Rsa.bytesAt t.mem (t.gpr .x6) (t.gpr .x1).toNat))) → Q s') :
    WP isa (.call c.name c.code) t Q := by
  refine WP.callFV (k := Spec.Rsa.publicPrecomputedCheckedContract abi c.stack) c.verified.1 (h.pre c.pos)
    (Covers.append_left (Covers.trans h.hrd (Covers.refl _)) (Covers.right h.hwr)) h.hwr ?_
    (by have := c.le; have := c.depth; omega)
  intro s' hrd' hwr' hsp' hf hpres hvs hpost
  sig_post [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs,
    stackArgs_two, List.append_eq] at hpost
  exact hQ s' hrd' hwr' hsp' hf hpres hvs hpost

/-- Two calls of a precomputed public operation leak alike if their
arguments, the precomputed values and the bytes of `e` agree. -/
theorem pdCallCT (c : PdChecked) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → PdOk c.stack t₁ ∧ PdOk c.stack t₂ ∧ ArgsEq 2 t₁ t₂ ∧
      Spec.Rsa.wordsAt t₁.mem (t₁.gpr .x2) (t₁.gpr .x3).toNat =
        Spec.Rsa.wordsAt t₂.mem (t₂.gpr .x2) (t₂.gpr .x3).toNat ∧
      Spec.Rsa.bytesAt t₁.mem (t₁.gpr .x4) (t₁.gpr .x5).toNat =
        Spec.Rsa.bytesAt t₂.mem (t₂.gpr .x4) (t₂.gpr .x5).toNat) :
    RelCT isa P (.call c.name c.code) fun _ _ => True := by
  refine RelCT.callEx c.verified.1 c.verified.2.1 fun t₁ t₂ hp => ?_
  obtain ⟨h₁, h₂, he, hn, hE⟩ := hP t₁ t₂ hp
  refine ⟨_, _, _, _, h₁.pre c.pos, h₂.pre c.pos, ?_,
    Covers.append_left (Covers.trans h₁.hrd (Covers.refl _)) (Covers.right h₁.hwr), h₁.hwr,
    Covers.append_left (Covers.trans h₂.hrd (Covers.refl _)) (Covers.right h₂.hwr), h₂.hwr⟩
  sig_pub [Spec.Rsa.publicPrecomputedCheckedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs,
    stackArgs_two, List.append_eq]
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := argsEq_regs he
  exact ⟨he.sp, by rw [hn, hE], e0, e1, e2, e3, e4, e5, e6, e7, he.args 0 (by decide), he.args 1 (by decide)⟩

/-- `vg_rsa_private_checked` and its variants. -/
abbrev PrivChecked := Callee fun K => Spec.Rsa.privateCheckedContract abi K

theorem stackArgs_twelve (s : State) :
    List.map (stackArg s) (List.range 12) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11] := rfl

/-- What the buffers of a call of `vg_rsa_private_checked` need, as
`PubLay`: `out` (`o`) and the working space (`sc`) are written; `n`, `e`,
the input (`i`), `p`, `q`, `dP`, `dQ` and `qInv` read; `a` is the 96 bytes
of the arguments on the stack. -/
structure PrivLay (sp : Addr) (K : Nat) (o n e i p q dp dq qi sc a : Region) : Prop where
  sp1 : K ≤ sp.toNat
  sp2 : sp.toNat + 96 ≤ 2 ^ 64
  on : o.Disjoint n
  oe : o.Disjoint e
  oi : o.Disjoint i
  op : o.Disjoint p
  oq : o.Disjoint q
  odp : o.Disjoint dp
  odq : o.Disjoint dq
  oqi : o.Disjoint qi
  os : o.Disjoint sc
  oa : o.Disjoint a
  ns : n.Disjoint sc
  es : e.Disjoint sc
  is : i.Disjoint sc
  ps : p.Disjoint sc
  qs : q.Disjoint sc
  dps : dp.Disjoint sc
  dqs : dq.Disjoint sc
  qis : qi.Disjoint sc
  sa : sc.Disjoint a
  ko : (⟨sp - BitVec.ofNat 64 K, K⟩ : Region).Disjoint o
  kn : (⟨sp - BitVec.ofNat 64 K, K⟩ : Region).Disjoint n
  ke : (⟨sp - BitVec.ofNat 64 K, K⟩ : Region).Disjoint e
  ki : (⟨sp - BitVec.ofNat 64 K, K⟩ : Region).Disjoint i
  kp : (⟨sp - BitVec.ofNat 64 K, K⟩ : Region).Disjoint p
  kq : (⟨sp - BitVec.ofNat 64 K, K⟩ : Region).Disjoint q
  kdp : (⟨sp - BitVec.ofNat 64 K, K⟩ : Region).Disjoint dp
  kdq : (⟨sp - BitVec.ofNat 64 K, K⟩ : Region).Disjoint dq
  kqi : (⟨sp - BitVec.ofNat 64 K, K⟩ : Region).Disjoint qi
  ks : (⟨sp - BitVec.ofNat 64 K, K⟩ : Region).Disjoint sc
  ka : (⟨sp - BitVec.ofNat 64 K, K⟩ : Region).Disjoint a
  wo : o.base.toNat + o.len ≤ 2 ^ 64
  wn : n.base.toNat + n.len ≤ 2 ^ 64
  we : e.base.toNat + e.len ≤ 2 ^ 64
  wi : i.base.toNat + i.len ≤ 2 ^ 64
  wp : p.base.toNat + p.len ≤ 2 ^ 64
  wq : q.base.toNat + q.len ≤ 2 ^ 64
  wdp : dp.base.toNat + dp.len ≤ 2 ^ 64
  wdq : dq.base.toNat + dq.len ≤ 2 ^ 64
  wqi : qi.base.toNat + qi.len ≤ 2 ^ 64
  ws : sc.base.toNat + sc.len ≤ 2 ^ 64

/-- The regions a call of `vg_rsa_private_checked` reads and writes, from
its registers and stack arguments. -/
abbrev privRd (t : State) : List Region :=
  [⟨t.gpr .x2, (t.gpr .x3).toNat⟩, ⟨t.gpr .x4, (t.gpr .x5).toNat⟩, ⟨t.gpr .x6, (t.gpr .x7).toNat⟩,
    ⟨stackArg t 0, (stackArg t 1).toNat⟩, ⟨stackArg t 2, (stackArg t 3).toNat⟩,
    ⟨stackArg t 4, (stackArg t 5).toNat⟩, ⟨stackArg t 6, (stackArg t 7).toNat⟩,
    ⟨stackArg t 8, (stackArg t 9).toNat⟩, ⟨t.sp, 96⟩]

abbrev privWr (t : State) : List Region :=
  [⟨t.gpr .x0, (t.gpr .x1).toNat⟩, ⟨stackArg t 10, (stackArg t 11).toNat * 8⟩]

/-- What a call of `vg_rsa_private_checked` needs: the modulus `n` of `k`
bytes at `x2`, `e` at `x4`, the input at `x6`, `out` at `x0`; `p`, `q`,
`dP`, `dQ`, `qInv` and the working space on the stack. -/
structure PrivOk (K : Nat) (t : State) : Prop where
  hl : PrivLay t.sp K ⟨t.gpr .x0, (t.gpr .x1).toNat⟩ ⟨t.gpr .x2, (t.gpr .x3).toNat⟩
    ⟨t.gpr .x4, (t.gpr .x5).toNat⟩ ⟨t.gpr .x6, (t.gpr .x7).toNat⟩ ⟨stackArg t 0, (stackArg t 1).toNat⟩
    ⟨stackArg t 2, (stackArg t 3).toNat⟩ ⟨stackArg t 4, (stackArg t 5).toNat⟩
    ⟨stackArg t 6, (stackArg t 7).toNat⟩ ⟨stackArg t 8, (stackArg t 9).toNat⟩
    ⟨stackArg t 10, (stackArg t 11).toNat * 8⟩ ⟨t.sp, 96⟩
  hrd : Covers (privRd t) (t.rd ++ t.wr)
  hwr : Covers (privWr t) t.wr
  hk : Spec.Rsa.lenValid (t.gpr .x3).toNat
  h1 : (t.gpr .x1).toNat = (t.gpr .x3).toNat
  h7 : (t.gpr .x7).toNat = (t.gpr .x3).toNat
  he1 : 1 ≤ (t.gpr .x5).toNat
  he2 : (t.gpr .x5).toNat ≤ (t.gpr .x3).toNat
  hp1 : 1 ≤ (stackArg t 1).toNat
  hp2 : (stackArg t 1).toNat < (t.gpr .x3).toNat
  hq1 : 1 ≤ (stackArg t 3).toNat
  hq2 : (stackArg t 3).toNat < (t.gpr .x3).toNat
  hdp : (stackArg t 5).toNat = (stackArg t 1).toNat
  hqi : (stackArg t 9).toNat = (stackArg t 1).toNat
  hdq : (stackArg t 7).toNat = (stackArg t 3).toNat
  hs : Spec.Rsa.scratchWords (t.gpr .x3).toNat ≤ (stackArg t 11).toNat

theorem PrivOk.pre {K : Nat} {t : State} (hK : 0 < K) (h : PrivOk K t) :
    (Spec.Rsa.privateCheckedContract abi K).pre (t.callEntry.withRegions (privRd t) (privWr t)) := by
  obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  have hl := h.hl
  sig_pre [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, abi, argRegs, stackArgs_twelve,
    List.append_eq]
  simp only [Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false,
    Bool.true_or, Bool.false_or, List.cons_append, List.nil_append, Sig.conj,
    List.append_nil, sa0]
  exact ⟨hl.sp1, hl.sp2, rfl, rfl, hl.on, hl.oe, ⟨hl.oi, hl.op, hl.oq, hl.odp, hl.odq, hl.oqi, hl.os,
    hl.oa, hl.ns, hl.es, hl.is, hl.ps, hl.qs, hl.dps, hl.dqs, hl.qis, hl.sa⟩,
    hl.ko, hl.kn, hl.ke, hl.ki, hl.kp, hl.kq, hl.kdp, hl.kdq, hl.kqi, hl.ks, hl.ka, hl.wo, hl.wn, hl.we,
    hl.wi, hl.wp, hl.wq, hl.wdp, hl.wdq, hl.wqi, hl.ws, h.hk, h.h1, h.h7, h.he1, h.he2, h.hp1, h.hp2,
    h.hq1, h.hq2, h.hdp, h.hqi, h.hdq, h.hs⟩

/-- A call of `vg_rsa_private_checked`. -/
theorem privCall (c : PrivChecked) {t : State} {Q : State → Prop} (h : PrivOk c.stack t)
    (hQ : ∀ s', s'.rd = t.rd → s'.wr = t.wr → s'.sp = t.sp →
      Frame (privWr t ++ [below t.sp (16 * c.code.aarch64Depth)]) t.mem s'.mem →
      (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = t.gpr r) →
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64) →
      Spec.Rsa.writtenOutcome s'.mem (t.gpr .x0) (t.gpr .x3).toNat ((s'.gpr .x0).setWidth 32)
        (Spec.Rsa.privateChecked (Spec.Rsa.bytesAt t.mem (t.gpr .x2) (t.gpr .x3).toNat)
          (Spec.Rsa.bytesAt t.mem (t.gpr .x4) (t.gpr .x5).toNat)
          (Spec.Rsa.bytesAt t.mem (t.gpr .x6) (t.gpr .x3).toNat)
          (Spec.Rsa.bytesAt t.mem (stackArg t 0) (stackArg t 1).toNat)
          (Spec.Rsa.bytesAt t.mem (stackArg t 2) (stackArg t 3).toNat)
          (Spec.Rsa.bytesAt t.mem (stackArg t 4) (stackArg t 1).toNat)
          (Spec.Rsa.bytesAt t.mem (stackArg t 6) (stackArg t 3).toNat)
          (Spec.Rsa.bytesAt t.mem (stackArg t 8) (stackArg t 1).toNat)) → Q s') :
    WP isa (.call c.name c.code) t Q := by
  refine WP.callFV (k := Spec.Rsa.privateCheckedContract abi c.stack) c.verified.1 (h.pre c.pos)
    (Covers.append_left (Covers.trans h.hrd (Covers.refl _)) (Covers.right h.hwr)) h.hwr ?_
    (by have := c.le; have := c.depth; omega)
  intro s' hrd' hwr' hsp' hf hpres hvs hpost
  sig_post [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, abi, argRegs, stackArgs_twelve,
    List.append_eq] at hpost
  exact hQ s' hrd' hwr' hsp' hf hpres hvs hpost

/-- Two calls of `vg_rsa_private_checked` leak alike if their arguments and
the bytes of `n` and `e` agree. -/
theorem privCallCT (c : PrivChecked) {P : State → State → Prop}
    (hP : ∀ t₁ t₂, P t₁ t₂ → PrivOk c.stack t₁ ∧ PrivOk c.stack t₂ ∧ ArgsEq 12 t₁ t₂ ∧
      Spec.Rsa.bytesAt t₁.mem (t₁.gpr .x2) (t₁.gpr .x3).toNat =
        Spec.Rsa.bytesAt t₂.mem (t₂.gpr .x2) (t₂.gpr .x3).toNat ∧
      Spec.Rsa.bytesAt t₁.mem (t₁.gpr .x4) (t₁.gpr .x5).toNat =
        Spec.Rsa.bytesAt t₂.mem (t₂.gpr .x4) (t₂.gpr .x5).toNat) :
    RelCT isa P (.call c.name c.code) fun _ _ => True := by
  refine RelCT.callEx c.verified.1 c.verified.2.1 fun t₁ t₂ hp => ?_
  obtain ⟨h₁, h₂, he, hn, hE⟩ := hP t₁ t₂ hp
  refine ⟨_, _, _, _, h₁.pre c.pos, h₂.pre c.pos, ?_,
    Covers.append_left (Covers.trans h₁.hrd (Covers.refl _)) (Covers.right h₁.hwr), h₁.hwr,
    Covers.append_left (Covers.trans h₂.hrd (Covers.refl _)) (Covers.right h₂.hwr), h₂.hwr⟩
  sig_pub [Spec.Rsa.privateCheckedContract, Spec.Rsa.privateCheckedSig, abi, argRegs, stackArgs_twelve,
    List.append_eq]
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := argsEq_regs he
  exact ⟨he.sp, by rw [hn, hE], e0, e1, e2, e3, e4, e5, e6, e7, he.args 0 (by decide),
    he.args 1 (by decide), he.args 2 (by decide), he.args 3 (by decide), he.args 4 (by decide),
    he.args 5 (by decide), he.args 6 (by decide), he.args 7 (by decide), he.args 8 (by decide),
    he.args 9 (by decide), he.args 10 (by decide), he.args 11 (by decide)⟩

end VG.Proof.RsaPkcs1Sig.AArch64

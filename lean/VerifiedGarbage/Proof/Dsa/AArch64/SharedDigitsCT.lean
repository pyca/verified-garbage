module
public import VerifiedGarbage.Proof.Dsa.AArch64.SharedBucketCT
public import VerifiedGarbage.Proof.Dsa.AArch64.SharedDigits
import VerifiedGarbage.Proof.Dsa.AArch64.SharedBucket
import VerifiedGarbage.Proof.Dsa.AArch64.SharedGroup
import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.SharedBucketCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.SharedDigits
meta import VerifiedGarbage.Proof.Dsa.AArch64.SharedBucket
meta import VerifiedGarbage.Proof.Dsa.AArch64.SharedGroup
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtBuild
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
meta import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # The digits leak only the public exponent and the layout

The secret exponent's bytes are read at addresses its pointer and length
fix, and its digits go only into the scan and the masked store; the public
exponent's digits choose its bucket's address and whether to multiply. -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64.SharedPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.SharedPower VG.Proof.Dsa.Shared

/-- A block's first part before the rest of a sequence: it runs the same
and leaks the same trace. -/
theorem relct_block_seq {P Q : State → State → Prop} {l₁ l₂ : List Instr} {c : Prog isa}
    (h : RelCT isa P (.seq (.block l₁) (.seq (.block l₂) c)) Q) : RelCT isa P (.seq (.block (l₁ ++ l₂)) c) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq a₁ c₁ =>
    cases e₂ with
    | seq a₂ c₂ =>
      rw [Exec.block_iff, execBlock_append] at a₁ a₂
      obtain ⟨⟨x₁, u₁⟩, ha₁, hb₁⟩ := Option.bind_eq_some_iff.mp a₁
      obtain ⟨⟨y₁, w₁⟩, hc₁, he₁⟩ := Option.map_eq_some_iff.mp hb₁
      obtain ⟨⟨x₂, u₂⟩, ha₂, hb₂⟩ := Option.bind_eq_some_iff.mp a₂
      obtain ⟨⟨y₂, w₂⟩, hc₂, he₂⟩ := Option.map_eq_some_iff.mp hb₂
      simp only [Prod.mk.injEq] at he₁ he₂
      obtain ⟨rfl, rfl⟩ := he₁
      obtain ⟨rfl, rfl⟩ := he₂
      obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.block ha₁) (.seq (.block hc₁) c₁))
        (.seq (.block ha₂) (.seq (.block hc₂) c₂))
      simp only [List.append_assoc] at ht ⊢
      exact ⟨ht, hq⟩

/-! ## A digit -/

/-- `baseSq_ok`'s hypotheses. -/
def SqPre (p : XPub) (s : State) : Prop :=
  ∃ (mi : BitVec 64) (X Xc : Nat), CExpCtx s (off p.B p.o) p.wx mi X Xc ∧ 2 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧ Xc < X

theorem sq_ct (M : Mont) {α : Type} (f : α → XPub) :
    RelCT isa (Two fun a s => SqPre (f a) s) (M.mm Crt.aXc Crt.aXc Crt.aXc) (Two fun a s => SqPre (f a) s) :=
  two_post (two_map (fun a : α => (f a).ws) (fun _ _ ⟨mi, _, _, hc, _⟩ => ⟨mi, hc.good, Nat.le_refl _⟩)
    (M.ct (o := Crt.aXc) (a := Crt.aXc) (b := Crt.aXc) (by unfold MmUse; decide)))
    fun _ _ ⟨mi, X, _, hc, hw, hw', hA⟩ => WP.mono (baseSq_ok M hc hw hw' hA)
      fun _ ⟨hc', hlt, _⟩ => ⟨mi, X, _, hc', hw, hw', hlt⟩

/-- A digit's hypotheses: the public exponent's value in `sMaskX` is public. -/
def DPre (p : XPub × Nat) (s : State) : Prop :=
  ∃ (mi : BitVec 64) (X Xc V : Nat), CExpCtx s (off p.1.B p.1.o) p.1.wx mi X Xc ∧ 8 ≤ p.1.wx ∧
    p.1.wx < 2 ^ 30 ∧ p.1.wx % 8 = 0 ∧
    word s.mem (off p.1.B p.1.o) (8 * Crt.sTab) = off (off p.1.B p.1.o) (slot p.1.wx 8) ∧
    word s.mem (off p.1.B p.1.o) (8 * Crt.sV) = BitVec.ofNat 64 V ∧ V < 2 ^ 64 ∧
    word s.mem (off p.1.B p.1.o) (8 * Crt.sMaskX) = BitVec.ofNat 64 p.2 ∧ p.2 < 2 ^ 64 ∧ Xc < X

/-- A digit of each exponent leaks the same in runs with the same workspace
and the same public exponent. -/
theorem digit_ct (M : Mont) : RelCT isa (Two DPre) (digit M.mm) (fun _ _ => True) := by
  rw [digit_eq]
  refine RelCT.seqs_append (by simp) (by simp) (RelCT.seq (two_post (Ψ := PHPre)
    (two_map (fun p : XPub × Nat => p.1) (fun _ _ ⟨mi, X, Xc, V, hc, hw, hw', hd, ht, hV, hV', _, _, hA⟩ =>
      ⟨mi, X, Xc, V, hc, hw, hw', hd, ht, hV, hV', hA⟩) (secretBucket_ct M))
    fun p s ⟨mi, X, Xc, V, hc, hw, hw', hd, ht, hV, hV', hQ, hQ', hA⟩ => ?_) ?_)
  · refine WP.mono (secretBucket_ok M hc hw hw' hd ht hV hV' hA) fun a ⟨hca, _, _, _, _, hdrA, _, _⟩ => ?_
    exact ⟨mi, X, Xc, hca, by omega_using [hw], hw',
      (hdrA _ (by decide) (by decide) (by decide) (by decide)).trans ht,
      (hdrA _ (by decide) (by decide) (by decide) (by decide)).trans hQ, hQ', hA⟩
  refine RelCT.seqs_append (by simp) (by simp) (RelCT.seq (two_post (Ψ := fun (p : XPub × Nat) s => SqPre p.1 s)
    (publicHalf_ct M) fun p s ⟨mi, X, Xc, hc, hw, hw', ht, hQ, hQ', hA⟩ => ?_) ?_)
  · exact WP.mono (publicHalf_ok M hc hw hw' ht hQ hQ' hA) fun b ⟨hcb, _⟩ => ⟨mi, X, Xc, hcb, hw, hw', hA⟩
  have sq := sq_ct M (fun p : XPub × Nat => p.1)
  simp only [seqs]
  refine RelCT.seq sq (RelCT.seq sq (RelCT.seq sq ?_))
  exact x0_ct (fun p : XPub × Nat => off p.1.B p.1.o) (fun _ _ ⟨_, _, _, hc, _⟩ => hc.good.x0)
    (by unfold digitEnd; taint_decide)

/-- After `i` digits of a group: the public value `p.2.1` and the count `p.2.2`. -/
def DLoop (p : XPub × Nat × Nat) (i : Nat) (s : State) : Prop :=
  ∃ (s₀ : State) (mi : BitVec 64) (N g ex eq k V : Nat),
    DigitsInv s₀ (off p.1.B p.1.o) p.1.wx mi N g ex eq k V p.2.1 p.2.2 i s ∧ 8 ≤ p.1.wx ∧ p.1.wx < 2 ^ 30 ∧
    p.1.wx % 8 = 0 ∧ Nat.Coprime (2 ^ (64 * p.1.wx)) N ∧ p.2.2 ≤ 8 ∧ V < 2 ^ 64 ∧ p.2.1 < 2 ^ 64 ∧
    (∀ i < p.2.2, V / 8 ^ i % 8 = ex / 8 ^ (k + i) % 8) ∧
    (∀ i < p.2.2, p.2.1 / 8 ^ i % 8 = eq / 8 ^ (k + i) % 8)

/-- The digits of a group. -/
theorem digitLoop_ct (M : Mont) :
    RelCT isa (Two fun (p : XPub × Nat × Nat) s => 0 < p.2.2 ∧ DLoop p 0 s)
      (.loop (digit M.mm) (.nonzero .x .x3)) (Two fun p s => DLoop p p.2.2 s) := by
  refine two_loop (Φ := DLoop) (fun p => p.2.2)
    (two_map (fun q : (XPub × Nat × Nat) × Nat => (q.1.1, q.1.2.1 / 8 ^ q.2)) ?_ (digit_ct M)) ?_
  · rintro ⟨p, i⟩ s ⟨_, s₀, mi, N, g, ex, eq, k, V, hI, hw, hw', hd, _, _, hV', hQ', _⟩
    have hle (a b : Nat) : a / 8 ^ b ≤ a := Nat.div_le_self _ _
    exact ⟨mi, N, _, V / 8 ^ i, hI.dig.ctx, hw, hw', hd, hI.dig.tab, hI.v,
      Nat.lt_of_le_of_lt (hle V i) hV', hI.q, Nat.lt_of_le_of_lt (hle _ i) hQ', hI.dig.alt⟩
  · rintro p i s hi ⟨s₀, mi, N, g, ex, eq, k, V, hI, hw, hw', hd, hR, hc8, hV', hQ', hVd, hQd⟩
    exact WP.mono (digitStep_ok M hw hw' hd hR hc8 hi hV' hQ' hVd hQd hI) fun t ⟨hI', hz⟩ =>
      ⟨eval_nz_count hi hz, fun _ => ⟨s₀, mi, N, g, ex, eq, k, V, hI', hw, hw', hd, hR, hc8, hV', hQ', hVd, hQd⟩,
        fun h => h ▸ ⟨s₀, mi, N, g, ex, eq, k, V, hI', hw, hw', hd, hR, hc8, hV', hQ', hVd, hQd⟩⟩

/-! ## A group of bytes -/

/-- The public data of the digits: the workspace, the exponents' pointers,
and the public exponent's bytes (its length is the secret exponent's). -/
structure GPub where
  x : XPub
  xp : Addr
  qp : Addr
  qb : List Byte

abbrev GPub.P (a : GPub) : Addr := off a.x.B a.x.o

/-- The number of groups of three bytes. -/
abbrev GPub.groups (a : GPub) : Nat := (a.qb.length + 2) / 3

/-- After `j` groups. -/
def GInv (a : GPub) (j : Nat) (s : State) : Prop :=
  ∃ (s₀ : State) (mi : BitVec 64) (N g : Nat) (xb : List Byte) (k : Nat),
    GroupsInv s₀ a.P a.x.wx mi N g a.xp a.qp xb a.qb j k s ∧ Exps s₀ a.P a.x.wx a.xp a.qp xb a.qb ∧
    8 ≤ a.x.wx ∧ a.x.wx < 2 ^ 30 ∧ a.x.wx % 8 = 0 ∧ Nat.Coprime (2 ^ (64 * a.x.wx)) N ∧ xb.length < 2 ^ 31

/-- The bytes' addresses and the bytes left, before the bytes are read. -/
def GroupPins (q : GPub × Nat) (s : State) : Prop :=
  s.gpr .x0 = q.1.P ∧ s.gpr .x1 = q.1.xp + BitVec.ofNat 64 (q.1.qb.length - 3 * q.2 - 1) ∧
  s.gpr .x2 = q.1.qp + BitVec.ofNat 64 (q.1.qb.length - 3 * q.2 - 1) ∧
  s.gpr .x4 = BitVec.ofNat 64 (q.1.qb.length - 3 * q.2 - 1)

theorem pins_group : Pins GroupPins [.x0, .x1, .x2, .x4] := by
  rintro q s₁ s₂ ⟨a₁, b₁, c₁, d₁⟩ ⟨a₂, b₂, c₂, d₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [a₁, a₂]
  · rw [b₁, b₂]
  · rw [c₁, c₂]
  · rw [d₁, d₂]

/-- The addresses of the group's last bytes. -/
def groupAddr : List Instr :=
  [ldh .x4 Crt.sI, .subImm .x .x4 .x4 1, ldh .x1 Crt.sExp, .add .x .x1 .x1 .x4, ldh .x2 Crt.sSrc,
    .add .x .x2 .x2 .x4]

theorem groupAddr_ok {s : State} {P : Addr} {wx : Nat} {minv : BitVec 64} {N Xc r : Nat} {xp qp : Addr}
    (hc : CExpCtx s P wx minv N Xc) (hr1 : 1 ≤ r)
    (hI : word s.mem P (8 * Crt.sI) = BitVec.ofNat 64 r) (hE : word s.mem P (8 * Crt.sExp) = xp)
    (hS : word s.mem P (8 * Crt.sSrc) = qp) :
    WP isa (.block groupAddr) s fun t => t.gpr .x0 = P ∧ t.gpr .x1 = xp + BitVec.ofNat 64 (r - 1) ∧
      t.gpr .x2 = qp + BitVec.ofNat 64 (r - 1) ∧ t.gpr .x4 = BitVec.ofNat 64 (r - 1) := by
  have e1 : (1 : BitVec 64) = BitVec.ofNat 64 1 := rfl
  brun [groupAddr, hc.good.x0, hdr_enc (show Crt.sI < 32 by decide), hdr_enc (show Crt.sExp < 32 by decide),
    hdr_enc (show Crt.sSrc < 32 by decide), hc.ld (i := Crt.sI) (by decide), hc.ld (i := Crt.sExp) (by decide),
    hc.ld (i := Crt.sSrc) (by decide), hI, hE, hS, e1, VG.Offset.ofNat_sub_ofNat hr1]

theorem GInv.len {a : GPub} {j : Nat} {s : State} (h : GInv a j s) :
    ∃ (s₀ : State) (mi : BitVec 64) (N g : Nat) (xb : List Byte) (k : Nat),
      GroupsInv s₀ a.P a.x.wx mi N g a.xp a.qp xb a.qb j k s ∧ Exps s₀ a.P a.x.wx a.xp a.qp xb a.qb ∧
      8 ≤ a.x.wx ∧ a.x.wx < 2 ^ 30 ∧ a.x.wx % 8 = 0 ∧ Nat.Coprime (2 ^ (64 * a.x.wx)) N ∧ xb.length < 2 ^ 31 ∧
      a.qb.length = xb.length :=
  let ⟨s₀, mi, N, g, xb, k, hI, hx, r⟩ := h; ⟨s₀, mi, N, g, xb, k, hI, hx, r.1, r.2.1, r.2.2.1, r.2.2.2.1,
    r.2.2.2.2, hx.len⟩

/-- A group's bytes are read at addresses the pointers and the length fix,
and how many it has is the length's. -/
theorem group_ct : RelCT isa (Two fun (q : GPub × Nat) s => q.2 < q.1.groups ∧ GInv q.1 q.2 s) group
    (fun _ _ => True) := by
  unfold group
  refine relct_block_seq (l₁ := groupAddr) (RelCT.seq (two_piece (Ψ := GroupPins) [.x0]
    (pins_x0B (fun q : GPub × Nat => q.1.P) fun _ _ ⟨_, _, _, _, _, _, _, hI, _⟩ => hI.dig.ctx.good.x0)
    (by taint_decide) fun q s ⟨hj, h⟩ => ?_) (two_taint [.x0, .x1, .x2, .x4] pins_group (by taint_decide)))
  obtain ⟨s₀, mi, N, g, xb, k, hI, hx, hw, hw', hd, hR, hL, hlen⟩ := h.len
  have hj' : q.2 < (q.1.qb.length + 2) / 3 := hj
  exact groupAddr_ok hI.dig.ctx (by omega_using [hj']) (by rw [hlen]; exact hI.rem) hI.xptr hI.qptr

/-- The group's values and its digits' count: where the digits start. -/
theorem groupStart_post {q : GPub × Nat} {s : State} (h : q.2 < q.1.groups ∧ GInv q.1 q.2 s) :
    WP isa group s fun u => 0 < gcount (q.1.qb.length - 3 * q.2) ∧
      DLoop (q.1.x, gval q.1.qb (q.1.qb.length - 3 * q.2), gcount (q.1.qb.length - 3 * q.2)) 0 u := by
  obtain ⟨hj, h⟩ := h
  obtain ⟨s₀, mi, N, g, xb, k, hI, hx, hw, hw', hd, hR, hL, hlen⟩ := h.len
  have hj' : q.2 < (xb.length + 2) / 3 := by rw [← hlen]; exact hj
  rw [hlen]
  generalize q.2 = j at hj' hI
  have hn := hI.dig.ctx.scrT.nowrap
  have hr1 : 1 ≤ xb.length - 3 * j := by omega_arith
  have hmemx : ∀ i (h : i < xb.length), s.mem (q.1.xp + BitVec.ofNat 64 i) = xb[i] := fun i hi => by
    rw [hI.frm _ fun r hr => Or.inr (by
      have := (workRanges_ok q.1.x.wx r hr).2; have := hx.xout i hi; omega_arith)]
    exact hx.xv i hi
  have hmemq : ∀ i (h : i < q.1.qb.length), s.mem (q.1.qp + BitVec.ofNat 64 i) = q.1.qb[i] := fun i hi => by
    rw [hI.frm _ fun r hr => Or.inr (by
      have := (workRanges_ok q.1.x.wx r hr).2; have := hx.qout i hi; omega_arith)]
    exact hx.qv i hi
  refine WP.mono (group_ok hI.dig.ctx hr1 (by omega_arith) (by rw [hx.len]; omega_arith) (by omega_arith)
    hI.rem hI.xptr hI.qptr (fun i hi => by rw [hI.keep.rd, hI.keep.wr]; exact hx.xrd i hi) hmemx
    (fun i hi => by rw [hI.keep.rd, hI.keep.wr]; exact hx.qrd i hi) hmemq) fun u ⟨hm, ku⟩ => ?_
  have oU : Outside q.1.P 136 120 s.mem u.mem := by
    rw [hm]
    exact (((fn_outside _ _ _ (by decide) (by decide)).trans (fn_outside _ _ _ (by decide) (by decide))).trans
      (fn_outside _ _ _ (by decide) (by decide))).trans (fn_outside _ _ _ (by decide) (by decide))
  have hh : ∀ i < 32, i ≠ Crt.sI → i ≠ Crt.sV → i ≠ Crt.sMaskX → i ≠ Crt.sBit →
      word u.mem q.1.P (8 * i) = word s.mem q.1.P (8 * i) := fun i hi h1 h2 h3 h4 => by
    rw [hm, hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h4), hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h3),
      hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h2), hdrStore_hdr _ _ _ (by decide) hi (Ne.symm h1)]
  have hdigU := hI.dig.of_fn oU (hh _ (by decide) (by decide) (by decide) (by decide) (by decide)) ku.wr
    (ku.gpr .x0 (by decide))
  have I0 : DigitsInv u q.1.P q.1.x.wx mi N g (Spec.Rsa.os2ip xb) (Spec.Rsa.os2ip q.1.qb) k
      (gval xb (xb.length - 3 * j)) (gval q.1.qb (xb.length - 3 * j)) (gcount (xb.length - 3 * j)) 0 u :=
    ⟨hdigU, by
        rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide),
          hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self, Nat.pow_zero, Nat.div_one],
      by rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self, Nat.pow_zero,
          Nat.div_one],
      by rw [hm, word_writeW_self, Nat.sub_zero], DigitsKeep.refl _ _ _⟩
  have hV24 := gval_lt xb (xb.length - 3 * j)
  have hQ24 := gval_lt q.1.qb (xb.length - 3 * j)
  exact ⟨gcount_pos _, u, mi, N, g, _, _, k, _, I0, hw, hw', hd, hR, gcount_le _, Nat.lt_of_lt_of_le hV24 (by decide),
    Nat.lt_of_lt_of_le hQ24 (by decide), fun i hi => by
      rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, hI.xr]
      exact (group_digit xb hr1 (by omega_arith) hi).symm,
    fun i hi => by
      rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, hI.qr]
      exact (group_digit q.1.qb hr1 (by rw [hx.len]; omega_arith) hi).symm⟩

/-- A group and its digits. -/
theorem groupsBody_ct (M : Mont) :
    RelCT isa (Two fun (q : GPub × Nat) s => q.2 < q.1.groups ∧ GInv q.1 q.2 s)
      (seqs [group, .loop (digit M.mm) (.nonzero .x .x3), .block [ldh .x3 Crt.sI]]) (fun _ _ => True) := by
  simp only [seqs]
  refine RelCT.seq (two_post group_ct fun _ _ h => groupStart_post h) (RelCT.seq
    (two_map (fun q : GPub × Nat => (q.1.x, gval q.1.qb (q.1.qb.length - 3 * q.2),
      gcount (q.1.qb.length - 3 * q.2))) (fun _ _ h => h) (digitLoop_ct M)) ?_)
  exact x0_ct (fun p : XPub × Nat × Nat => off p.1.B p.1.o)
    (fun _ _ ⟨_, _, _, _, _, _, _, _, hI, _⟩ => hI.dig.ctx.good.x0) (by taint_decide)

/-- Every digit of both exponents leaks the same in runs with the same
workspace, pointers and public exponent. -/
theorem digits_ct (M : Mont) :
    RelCT isa (Two fun (a : GPub) s => 0 < a.groups ∧ GInv a 0 s) (digits M.mm) (fun _ _ => True) := by
  unfold digits
  refine (two_loop (Φ := GInv) (Ψ := fun _ _ => True) (fun a => a.groups) (groupsBody_ct M) ?_).mono
    (fun _ _ h => h) fun _ _ _ => trivial
  intro a j s hj h
  obtain ⟨s₀, mi, N, g, xb, k, hI, hx, hw, hw', hd, hR, hL, hlen⟩ := h.len
  have hj' : j < (xb.length + 2) / 3 := by rw [← hlen]; exact hj
  refine WP.mono (groupsStep_ok M hw hw' hd hR hx hL hj' hI) fun t ⟨⟨k', hI'⟩, hz⟩ => ?_
  have hz' : (t.gpr .x3).toNat ≠ 0 ↔ j + 1 ≠ a.groups := by
    rw [hz]; show _ ↔ j + 1 ≠ (a.qb.length + 2) / 3; rw [hlen]
  exact ⟨eval_nz_count hj hz', fun _ => ⟨s₀, mi, N, g, xb, k', hI', hx, hw, hw', hd, hR, hL⟩, fun _ => trivial⟩

end VG.Proof.Dsa.AArch64.SharedPower

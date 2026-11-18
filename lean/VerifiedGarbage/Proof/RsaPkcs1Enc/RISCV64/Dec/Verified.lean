module

public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaPkcs1Enc.Decrypt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rsa.PrivCheck
import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
public import VerifiedGarbage.Proof.Framework.RISCV64.MRun
public meta import VerifiedGarbage.Proof.Framework.RISCV64.MRun
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Select
public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.Irprf
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.Decrypt
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Rsa.PrivCheck
meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.Select
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.Irprf
import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.Kdk
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.Kdk
import VerifiedGarbage.Proof.Rsa.RISCV64.PrivCT
import VerifiedGarbage.Proof.Rsa.RISCV64.PrivPCT
meta import VerifiedGarbage.Proof.Rsa.RISCV64.PrivCT
meta import VerifiedGarbage.Proof.Rsa.RISCV64.PrivPCT
public import VerifiedGarbage.Proof.Rsa.Contract
meta import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.Calls
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
public import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Sha256.RISCV64.Stream.Update
import VerifiedGarbage.Proof.Sha256.RISCV64.Stream.Finalize
import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha256
import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Finalize
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.Calls
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
meta import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Sha256.RISCV64.Stream.Update
meta import VerifiedGarbage.Proof.Sha256.RISCV64.Stream.Finalize
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha256
meta import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Finalize
meta import VerifiedGarbage.Proof.Framework.Covers

/-! ### `RsaPkcs1Enc.RISCV64.Dec.CT3`, which this module and modules that import it used -/

section

/-! ### `RsaPkcs1Enc.RISCV64.Dec.CT2`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.RISCV64.Dec.CT1`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.RISCV64.Dec.CTBase`, which only this module used -/

section

/-!
# `vg_rsa_pkcs1_decrypt` on RISC-V: constant time, the frame of the proof

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Enc/PPC64LE/DecCTBase.lean`): two runs with the same public
data satisfy the same facts about it (`Same`); from the entry states `s₁`
and `s₂` (an `Env`), two runs are related at each step by `Rel e P`: run `i`
satisfies `P sᵢ`, a predicate correctness gives, which fixes as functions of
the entry state the registers the next step's addresses depend on
(`rel_step`, by the taint analysis). The calls of SHA-256's streaming
functions and of HMAC-SHA-256's `init` and `finalize` leak alike by their
constant time (`RelCT.callEx`), from arguments that are functions of the entry
state (`shaInit_rel`, …).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec

open VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK initK updK finK initG finG)

variable {pc : Bool}

/-- The public data's facts. -/
structure Same (pc : Bool) (s₁ s₂ : State) : Prop where
  gpr : ∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r
  arg : ∀ i < nA pc, stackArg s₁ i = stackArg s₂ i
  sp : s₁.sp = s₂.sp
  n : Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a3) (s₁.gpr .a4).toNat = Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a3) (s₂.gpr .a4).toNat
  e : Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a5) (s₁.gpr .a6).toNat = Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a5) (s₂.gpr .a6).toNat
  leak : pc = true → Spec.Rsa.privatePrecomputedLeak s₁.mem (stackArg s₁ 15) (s₁.gpr .a4).toNat =
    Spec.Rsa.privatePrecomputedLeak s₂.mem (stackArg s₂ 15) (s₂.gpr .a4).toNat

theorem same_of {s₁ s₂ : State} (h : (Spec.RsaPkcs1Enc.decryptContract RISCV64.abi stackBytes).pub s₁ s₂) :
    Same false s₁ s₂ := by
  have e : stackBytes = 3455 + 1 := rfl
  rw [e] at h
  sig_pub [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, RISCV64.abi, RISCV64.argRegs,
    stackArgs_fifteen, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13,
    a14⟩ := h
  rw [List.map_append, List.map_append] at hl
  obtain ⟨hn, he⟩ := List.append_inj hl (by simp [Proof.Rsa.bytesAt_length', h7])
  refine ⟨fun r hr => ?_, fun i hi => ?_, hsp,
    ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hn),
    ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 he), nofun⟩
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h3, h4, h5, h6, h7, h8, h9, h10]
  · simp only [nA, Bool.false_eq_true, ↓reduceIte] at hi
    rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
      i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14]

/-- Two entry states with the same public data. -/
structure Env (pc : Bool) where
  s₁ : State
  s₂ : State
  h₁ : DPre pc s₁
  h₂ : DPre pc s₂
  S : Same pc s₁ s₂
  x₁ : pc = true → PreX s₁
  x₂ : pc = true → PreX s₂

/-- Run `i` satisfies `P sᵢ`. -/
def Rel (e : Env pc) (P : State → State → Prop) (a b : State) : Prop := P e.s₁ a ∧ P e.s₂ b

/-- Two runs whose stack pointers and registers `rs` agree. -/
def AgreeOn (rs : List Reg) (a b : State) : Prop := a.sp = b.sp ∧ ∀ r ∈ rs, a.gpr r = b.gpr r

theorem rel_of {rs : List Reg} {c : Prog isa} {hc : VG.Taint.Hint VG.RISCV64.Taint.T}
    (h : (taint.check (VG.RISCV64.Taint.ofRegs rs) c hc).isSome = true) {P : State → State → Prop}
    (hp : ∀ a b, P a b → AgreeOn rs a b) : RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := taint) (VG.RISCV64.Taint.ofRegs rs) (fun a b hab => ⟨(hp a b hab).1, fun r hr =>
    (hp a b hab).2 r (by simpa [VG.RISCV64.Taint.ofRegs] using hr)⟩) h

section
variable {e : Env pc}

theorem Env.r (e : Env pc) {r : Reg} (hr : r ∈ argRegs := by decide) : e.s₁.gpr r = e.s₂.gpr r := e.S.gpr r hr
theorem Env.arg (e : Env pc) {i : Nat} (hi : i < 15 := by decide) : stackArg e.s₁ i = stackArg e.s₂ i := e.S.arg i (lt_nA hi)
theorem Env.fb_eq (e : Env pc) : fb e.s₁ = fb e.s₂ := by
  show e.s₁.sp - _ = e.s₂.sp - _; rw [e.S.sp]
theorem Env.scA_eq (e : Env pc) (a : Nat) : scA e.s₁ a = scA e.s₂ a := by
  show stackArg e.s₁ 13 + _ = stackArg e.s₂ 13 + _; rw [e.arg]

/-- A step, from what correctness gives of each run. -/
theorem rel_post {P P' : State → State → Prop} {c : Prog isa} (hct : RelCT isa (Rel e P) c fun _ _ => True)
    (hw : ∀ s u, DPre pc s → P s u → WP isa c u (P' s)) : RelCT isa (Rel e P) c (Rel e P') := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨_, u₁, x₁, y₁⟩ := hw _ _ e.h₁ hp.1
  obtain ⟨_, u₂, x₂, y₂⟩ := hw _ _ e.h₂ hp.2
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, y₁, y₂⟩

/-- A step the taint analysis checks from the registers `rs`, which `P` fixes. -/
theorem rel_step {P P' : State → State → Prop} {c : Prog isa} (rs : List Reg)
    {hc : VG.Taint.Hint VG.RISCV64.Taint.T}
    (h : (taint.check (VG.RISCV64.Taint.ofRegs rs) c hc).isSome = true)
    (hpin : ∀ a b, P e.s₁ a → P e.s₂ b → AgreeOn rs a b)
    (hw : ∀ s u, DPre pc s → P s u → WP isa c u (P' s)) : RelCT isa (Rel e P) c (Rel e P') :=
  rel_post (rel_of h fun a b hab => hpin a b hab.1 hab.2) hw

/-- Two `Post` states agree on the stack pointer and on what `Mid` fixes. -/
theorem post_agree {R₁ R₂ : BitVec 64} {E₁ E₂ : List Byte} {a b : State} (ha : Post e.s₁ R₁ E₁ a)
    (hb : Post e.s₂ R₂ E₂ b) : a.sp = b.sp ∧ a.gpr .s0 = b.gpr .s0 ∧ a.gpr .s1 = b.gpr .s1 ∧
      a.gpr .s2 = b.gpr .s2 ∧ a.gpr .s3 = b.gpr .s3 ∧ a.gpr .s4 = b.gpr .s4 ∧ a.gpr .s5 = b.gpr .s5 ∧
      a.gpr .s6 = b.gpr .s6 :=
  ⟨by rw [ha.sp, hb.sp, e.fb_eq], by rw [ha.s0, hb.s0, e.arg], by rw [ha.s1, hb.s1, e.r],
    by rw [ha.s2, hb.s2, e.r], by rw [ha.s3, hb.s3, e.r], by rw [ha.s4, hb.s4, e.r],
    by rw [ha.s5, hb.s5, e.arg], by rw [ha.s6, hb.s6, e.arg]⟩

end

/-! ## The calls -/

theorem ct_mono {pre pre' : State → Prop} {pub pub' : State → State → Prop} {c : Prog isa}
    (h : ConstantTime isa pre pub c) (hp : ∀ s, pre' s → pre s) (hq : ∀ s₁ s₂, pub' s₁ s₂ → pub s₁ s₂) :
    ConstantTime isa pre' pub' c :=
  fun _ _ _ _ _ _ h₁ h₂ hpub e₁ e₂ => h _ _ _ _ _ _ (hp _ h₁) (hp _ h₂) (hq _ _ hpub) e₁ e₂

theorem init_ct : ConstantTime isa (initK sha256.S hH.SH.Repr).pre (initK sha256.S hH.SH.Repr).pub sha256.initC :=
  ct_mono Proof.Sha256.RISCV64.Stream.init_verified.2.1 (fun _ hs => hs) fun _ _ h => h
theorem upd_ct : ConstantTime isa (updK sha256.S sha256.F hH.SH.Repr).pre (updK sha256.S sha256.F hH.SH.Repr).pub
    sha256.updC :=
  ct_mono Proof.Sha256.RISCV64.Stream.Update.update_verified.2.1 (fun _ hs => hs) fun _ _ h => h
theorem fin_ct : ConstantTime isa (finK sha256.S sha256.F sha256.D hH.SH.Repr hH.SH.H.hash).pre
    (finK sha256.S sha256.F sha256.D hH.SH.Repr hH.SH.H.hash).pub sha256.finC :=
  ct_mono Proof.Sha256.RISCV64.Stream.Finalize.finalize_verified.2.1 (fun _ hs => hs) fun _ _ h => h

/-- What a run of a call from a `Post` state needs: `Post` and its
arguments, as functions of the entry state. -/
def PostAt (s t : State) : Prop := ∃ R EM, Post s R EM t

section
variable {e : Env pc}

/-- `init` of the state at `scratch + a`. -/
theorem shaInit_rel {P : State → State → Prop} {a : Nat} (ha : a + 96 ≤ scrBytes)
    (hp : ∀ s t, P s t → PostAt s t ∧ t.gpr .a0 = scA s a) :
    RelCT isa (Rel e P) sha256.callInit fun _ _ => True := by
  refine RelCT.callEx hH.init init_ct fun t₁ t₂ ⟨p₁, p₂⟩ => ?_
  obtain ⟨⟨_, _, P₁⟩, g₁⟩ := hp _ _ p₁
  obtain ⟨⟨_, _, P₂⟩, g₂⟩ := hp _ _ p₂
  have pre : ∀ {s t : State}, (initK sha256.S hH.SH.Repr).pre (t.callEntry.withRegions [] [⟨t.gpr .a0, 96⟩]) :=
    fun {s t} => by
      simp only [initK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
        State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide)]
      exact ⟨trivial, rfl⟩
  refine ⟨[], _, [], _, pre (s := e.s₁), pre (s := e.s₂), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [initK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp]
    exact ⟨by rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), g₁, g₂, e.scA_eq],
      (post_agree P₁ P₂).1⟩
  · rw [List.nil_append, g₁]; exact Covers.right (scCov e.h₁ P₁.wr ha)
  · rw [g₁]; exact scCov e.h₁ P₁.wr ha
  · rw [List.nil_append, g₂]; exact Covers.right (scCov e.h₂ P₂.wr ha)
  · rw [g₂]; exact scCov e.h₂ P₂.wr ha

/-- What a run of `update` needs. -/
structure UpdAt (s t : State) (a : Nat) (dat : Addr) (len : Nat) : Prop where
  post : PostAt s t
  h0 : t.gpr .a0 = scA s a
  h2 : t.gpr .a2 = dat
  h3 : (t.gpr .a3).toNat = len
  hdc : Covers [⟨dat, len⟩] (t.rd ++ t.wr)
  hd : Region.Disjoint ⟨dat, len⟩ (scR s a 96)
  hdl : (below (fb s) sha256.F).Disjoint ⟨dat, len⟩

/-- `update` of the state at `scratch + a` with data whose address and
length are functions of the entry state. -/
theorem shaUpd_rel {P : State → State → Prop} {a : Nat} (ha : a + 96 ≤ scrBytes) {dat : State → Addr}
    {len : State → Nat} (hdat : dat e.s₁ = dat e.s₂) (hlen : len e.s₁ = len e.s₂)
    (hp : ∀ s t, P s t → UpdAt s t a (dat s) (len s))
    (h1 : ∀ t₁ t₂, P e.s₁ t₁ → P e.s₂ t₂ → t₁.gpr .a1 = t₂.gpr .a1) :
    RelCT isa (Rel e P) sha256.callUpd fun _ _ => True := by
  refine RelCT.callEx hH.upd upd_ct fun t₁ t₂ ⟨p₁, p₂⟩ => ?_
  have U₁ := hp _ _ p₁
  have U₂ := hp _ _ p₂
  obtain ⟨_, _, P₁⟩ := U₁.post
  obtain ⟨_, _, P₂⟩ := U₂.post
  have pre : ∀ {s t : State}, DPre pc s → (P' : ∃ R EM, Post s R EM t) → UpdAt s t a (dat s) (len s) →
      (updK sha256.S sha256.F hH.SH.Repr).pre (t.callEntry.withRegions [⟨dat s, len s⟩] [scR s a 96]) :=
    fun {s t} h ⟨_, _, P⟩ U => by
      have c0 : t.callEntry.gpr .a0 = t.gpr .a0 := State.callEntry_gpr _ (by decide)
      have c2 : t.callEntry.gpr .a2 = t.gpr .a2 := State.callEntry_gpr _ (by decide)
      have c3 : t.callEntry.gpr .a3 = t.gpr .a3 := State.callEntry_gpr _ (by decide)
      simp only [updK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
        State.callEntry_sp, c0, c2, c3, U.h0, U.h2, U.h3]
      exact ⟨trivial, rfl, U.hd, by rw [P.sp]; exact fb_al h, by rw [P.sp]; exact fb_ge h (by decide),
        by rw [P.sp]; exact lowSc h (by decide) ha, by rw [P.sp]; exact U.hdl⟩
  refine ⟨_, _, _, _, pre e.h₁ U₁.post U₁, pre e.h₂ U₂.post U₂, ?_,
    Covers.append_left U₁.hdc (Covers.right (scCov e.h₁ P₁.wr ha)), scCov e.h₁ P₁.wr ha,
    Covers.append_left U₂.hdc (Covers.right (scCov e.h₂ P₂.wr ha)), scCov e.h₂ P₂.wr ha⟩
  simp only [updK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.a2 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a3 ∉ linkRegs by decide)]
  exact ⟨by rw [U₁.h0, U₂.h0, e.scA_eq], h1 _ _ p₁ p₂, by rw [U₁.h2, U₂.h2, hdat],
    BitVec.eq_of_toNat_eq (by rw [U₁.h3, U₂.h3, hlen]), (post_agree P₁ P₂).1⟩

/-- `finalize` of the state at `scratch + a`, into `scratch + o`. -/
theorem shaFin_rel {P : State → State → Prop} {a o : Nat} (ha : a + 96 ≤ scrBytes) (ho : o + 32 ≤ scrBytes)
    (hao : a + 96 ≤ o ∨ o + 32 ≤ a)
    (hp : ∀ s t, P s t → PostAt s t ∧ t.gpr .a0 = scA s a ∧ t.gpr .a2 = scA s o ∧ t.gpr .a1 = s.gpr .a4) :
    RelCT isa (Rel e P) sha256.callFin fun _ _ => True := by
  refine RelCT.callEx hH.fin fin_ct fun t₁ t₂ ⟨p₁, p₂⟩ => ?_
  obtain ⟨⟨_, _, P₁⟩, g₁, k₁, l₁⟩ := hp _ _ p₁
  obtain ⟨⟨_, _, P₂⟩, g₂, k₂, l₂⟩ := hp _ _ p₂
  have pre : ∀ {s t : State} {R : BitVec 64} {EM : List Byte}, DPre pc s → Post s R EM t → t.gpr .a0 = scA s a →
      t.gpr .a2 = scA s o →
      (finK sha256.S sha256.F sha256.D hH.SH.Repr hH.SH.H.hash).pre
        (t.callEntry.withRegions [] [scR s a 96, scR s o 32]) := fun {s t R EM} h P g k => by
    have c0 : t.callEntry.gpr .a0 = t.gpr .a0 := State.callEntry_gpr _ (by decide)
    have c2 : t.callEntry.gpr .a2 = t.gpr .a2 := State.callEntry_gpr _ (by decide)
    simp only [finK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
      State.callEntry_sp, c0, c2, g, k]
    exact ⟨trivial, rfl, scDisj hao ha ho, by rw [P.sp]; exact fb_al h, by rw [P.sp]; exact fb_ge h (by decide),
      by rw [P.sp]; exact lowSc h (by decide) ha, by rw [P.sp]; exact lowSc h (by decide) ho⟩
  refine ⟨_, _, _, _, pre e.h₁ P₁ g₁ k₁, pre e.h₂ P₂ g₂ k₂, ?_,
    by rw [List.nil_append]; exact Covers.right (Covers.pair (scCov e.h₁ P₁.wr ha) (scCov e.h₁ P₁.wr ho)),
    Covers.pair (scCov e.h₁ P₁.wr ha) (scCov e.h₁ P₁.wr ho),
    by rw [List.nil_append]; exact Covers.right (Covers.pair (scCov e.h₂ P₂.wr ha) (scCov e.h₂ P₂.wr ho)),
    Covers.pair (scCov e.h₂ P₂.wr ha) (scCov e.h₂ P₂.wr ho)⟩
  simp only [finK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.a2 ∉ linkRegs by decide)]
  exact ⟨by rw [g₁, g₂, e.scA_eq], by rw [l₁, l₂, e.r], by rw [k₁, k₂, e.scA_eq], (post_agree P₁ P₂).1⟩

theorem macInit_ok' : ∀ s, (initG hH.SH (sha256.ibytes + sha256.F)).pre s → ∃ t s', Exec isa sha256.init s t s' ∧
    abiPreserved s s' ∧ (initG hH.SH (sha256.ibytes + sha256.F)).post s s' :=
  fun _ hs => VG.Proof.Hmac.Stream.RISCV64.Init.correct hH hs

theorem macFin_ok' : ∀ s, (finG hH.SH (sha256.fbytes + sha256.F)).pre s → ∃ t s', Exec isa sha256.finalize s t s' ∧
    abiPreserved s s' ∧ (finG hH.SH (sha256.fbytes + sha256.F)).post s s' :=
  fun _ hs => VG.Proof.Hmac.Stream.RISCV64.Finalize.correct hH hs

/-- HMAC's `init` of the states at `scratch + sSt` and `scratch + sOuter`, with
the 32-byte key at `scratch + k`. -/
theorem macInit_rel {P : State → State → Prop} {k : Nat} (hk : k + 32 ≤ scrBytes) (hk1 : sOuter + 96 ≤ k)
    (hp : ∀ s t, P s t → PostAt s t ∧ t.gpr .a0 = scA s sSt ∧ t.gpr .a1 = scA s sOuter ∧ t.gpr .a2 = scA s k ∧
      t.gpr .a3 = BitVec.ofNat 64 32) :
    RelCT isa (Rel e P) macInitCall fun _ _ => True := by
  have zz := hmac_sizes
  have X : sha256.ibytes + sha256.F ≤ callX := zz.1
  refine RelCT.callEx macInit_ok' VG.Proof.Hmac.Stream.RISCV64.Sha256.init_ct fun t₁ t₂ ⟨p₁, p₂⟩ => ?_
  obtain ⟨⟨_, _, P₁⟩, a₁, b₁, c₁, d₁⟩ := hp _ _ p₁
  obtain ⟨⟨_, _, P₂⟩, a₂, b₂, c₂, d₂⟩ := hp _ _ p₂
  have hi : sSt + 96 ≤ scrBytes := by decide
  have hu : sOuter + 96 ≤ scrBytes := by decide
  have pre : ∀ {s t : State} {R : BitVec 64} {EM : List Byte}, DPre pc s → Post s R EM t → t.gpr .a0 = scA s sSt →
      t.gpr .a1 = scA s sOuter → t.gpr .a2 = scA s k → t.gpr .a3 = BitVec.ofNat 64 32 →
      (initG hH.SH (sha256.ibytes + sha256.F)).pre
        (t.callEntry.withRegions [scR s k 32] [scR s sSt 96, scR s sOuter 96]) := fun {s t R EM} h P g0 g1 g2 g3 => by
    have c0 : t.callEntry.gpr .a0 = scA s sSt := (State.callEntry_gpr _ (by decide)).trans g0
    have c1 : t.callEntry.gpr .a1 = scA s sOuter := (State.callEntry_gpr _ (by decide)).trans g1
    have c2 : t.callEntry.gpr .a2 = scA s k := (State.callEntry_gpr _ (by decide)).trans g2
    have c3 : (t.callEntry.gpr .a3).toNat = 32 := by rw [State.callEntry_gpr _ (by decide), g3]; rfl
    have hS : hH.SH.stateBytes = 96 := rfl
    simp only [initG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_sp, State.callEntry_sp, c0, c1, c2, c3, P.sp, hS]
    exact ⟨trivial, trivial, scDisj (.inl (by decide)) hi hu, scDisj (.inr (by unfold sSt sOuter at *; omega_using [hk1])) hk hi,
      scDisj (.inr hk1) hk hu, fb_al h, fb_ge h X, lowSc h X hi, lowSc h X hu, lowSc h X hk⟩
  have cov : ∀ {s t : State} {R : BitVec 64} {EM : List Byte}, DPre pc s → Post s R EM t →
      Covers ([scR s k 32] ++ [scR s sSt 96, scR s sOuter 96]) (t.rd ++ t.wr) ∧
      Covers [scR s sSt 96, scR s sOuter 96] t.wr := fun {s t R EM} h P =>
    ⟨Covers.append_left (Covers.right (scCov h P.wr hk))
      (Covers.right (Covers.pair (scCov h P.wr hi) (scCov h P.wr hu))),
      Covers.pair (scCov h P.wr hi) (scCov h P.wr hu)⟩
  refine ⟨_, _, _, _, pre e.h₁ P₁ a₁ b₁ c₁ d₁, pre e.h₂ P₂ a₂ b₂ c₂ d₂, ?_, (cov e.h₁ P₁).1, (cov e.h₁ P₁).2,
    (cov e.h₂ P₂).1, (cov e.h₂ P₂).2⟩
  simp only [initG, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.a2 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a3 ∉ linkRegs by decide)]
  exact ⟨by rw [a₁, a₂, e.scA_eq], by rw [b₁, b₂, e.scA_eq], by rw [c₁, c₂, e.scA_eq], by rw [d₁, d₂],
    (post_agree P₁ P₂).1⟩

/-- HMAC's `finalize` of the states at `scratch + sSt` and `scratch + sOuter`,
into `scratch + o`, with a count that is a function of the entry state. -/
theorem macFin_rel {P : State → State → Prop} {o : Nat} (ho : o + 32 ≤ scrBytes) (ho1 : sOuter + 96 ≤ o)
    {cnt : State → BitVec 64} (hcnt : cnt e.s₁ = cnt e.s₂)
    (hp : ∀ s t, P s t → PostAt s t ∧ t.gpr .a0 = scA s sSt ∧ t.gpr .a1 = scA s sOuter ∧ t.gpr .a2 = cnt s ∧
      t.gpr .a3 = scA s o) :
    RelCT isa (Rel e P) macFinCall fun _ _ => True := by
  have zz := hmac_sizes
  have X : sha256.fbytes + sha256.F ≤ callX := zz.2.1
  refine RelCT.callEx macFin_ok' VG.Proof.Hmac.Stream.RISCV64.Sha256.fin_ct fun t₁ t₂ ⟨p₁, p₂⟩ => ?_
  obtain ⟨⟨_, _, P₁⟩, a₁, b₁, c₁, d₁⟩ := hp _ _ p₁
  obtain ⟨⟨_, _, P₂⟩, a₂, b₂, c₂, d₂⟩ := hp _ _ p₂
  have hi : sSt + 96 ≤ scrBytes := by decide
  have hu : sOuter + 96 ≤ scrBytes := by decide
  have pre : ∀ {s t : State} {R : BitVec 64} {EM : List Byte}, DPre pc s → Post s R EM t → t.gpr .a0 = scA s sSt →
      t.gpr .a1 = scA s sOuter → t.gpr .a3 = scA s o →
      (finG hH.SH (sha256.fbytes + sha256.F)).pre
        (t.callEntry.withRegions [scR s sOuter 96] [scR s sSt 96, scR s o 32]) := fun {s t R EM} h P g0 g1 g3 => by
    have c0 : t.callEntry.gpr .a0 = scA s sSt := (State.callEntry_gpr _ (by decide)).trans g0
    have c1 : t.callEntry.gpr .a1 = scA s sOuter := (State.callEntry_gpr _ (by decide)).trans g1
    have c3 : t.callEntry.gpr .a3 = scA s o := (State.callEntry_gpr _ (by decide)).trans g3
    have hS : hH.SH.stateBytes = 96 := rfl
    have hD : hH.SH.digestBytes = 32 := rfl
    simp only [finG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_sp, State.callEntry_sp, c0, c1, c3, P.sp, hS, hD]
    exact ⟨trivial, trivial, scDisj (.inl (by decide)) hi hu, scDisj (.inl (by unfold sSt sOuter at *; omega_using [ho1])) hi ho,
      scDisj (.inl ho1) hu ho, fb_al h, fb_ge h X, lowSc h X hi, lowSc h X hu, lowSc h X ho⟩
  have cov : ∀ {s t : State} {R : BitVec 64} {EM : List Byte}, DPre pc s → Post s R EM t →
      Covers ([scR s sOuter 96] ++ [scR s sSt 96, scR s o 32]) (t.rd ++ t.wr) ∧
      Covers [scR s sSt 96, scR s o 32] t.wr := fun {s t R EM} h P =>
    ⟨Covers.append_left (Covers.right (scCov h P.wr hu))
      (Covers.right (Covers.pair (scCov h P.wr hi) (scCov h P.wr ho))),
      Covers.pair (scCov h P.wr hi) (scCov h P.wr ho)⟩
  refine ⟨_, _, _, _, pre e.h₁ P₁ a₁ b₁ d₁, pre e.h₂ P₂ a₂ b₂ d₂, ?_, (cov e.h₁ P₁).1, (cov e.h₁ P₁).2,
    (cov e.h₂ P₂).1, (cov e.h₂ P₂).2⟩
  simp only [finG, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (show Reg.a0 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a1 ∉ linkRegs by decide),
    State.callEntry_gpr _ (show Reg.a2 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.a3 ∉ linkRegs by decide)]
  exact ⟨by rw [a₁, a₂, e.scA_eq], by rw [b₁, b₂, e.scA_eq], by rw [c₁, c₂, hcnt], by rw [d₁, d₂, e.scA_eq],
    (post_agree P₁ P₂).1⟩

end

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec

end

end

/-!
# `vg_rsa_pkcs1_decrypt` on RISC-V: constant time up to `KDK`

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Enc/PPC64LE/DecVerified.lean`, `DecCT2.lean`): the setup and `D`,
by the taint analysis from the registers correctness fixes (`setup_ct`,
`dBuild_ct`), the call of `vg_rsa_private_checked` by its constant time
(`priv_ct`), and `DH` and `KDK`: their blocks by the taint analysis and their
calls by `shaInit_rel`, … (`hashD_ct`, `kdkMac_ct`). From the call on, two
runs are related by `PostAt` and the registers each call's arguments are in.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec

open VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt VG.Proof.RsaPkcs1Sig.RISCV64

variable {pc : Bool}

/-- `PostAt` is kept by code writing registers `Post` does not keep. -/
theorem PostAt.only {s t u : State} (h : DPre pc s) (hp : PostAt s t) {rs : List Reg} (o : Only rs t u)
    (hrs : ∀ r ∈ rs, r ∉ kept := by decide) (h7 : Reg.s7 ∉ rs := by decide) : PostAt s u :=
  let ⟨_, _, P⟩ := hp
  ⟨_, _, P.keep h o.keep (ws := []) (by rw [o.mem]; exact Frame.refl _ _) (fun r hr => nomatch hr) hrs h7⟩

section
variable {e : Env pc}

/-- After the frame's allocation. -/
def PEnt (s u : State) : Prop := u = allocd frameBytes s

theorem setup_ct : RelCT isa (Rel e PEnt) (.block (setup pc)) (Rel e (AtCall pc)) := by
  have hpin : ∀ a b, PEnt e.s₁ a → PEnt e.s₂ b → AgreeOn [] a b := fun a b ha hb =>
    ⟨by rw [ha, hb]; show e.s₁.sp - _ = e.s₂.sp - _; rw [e.S.sp], fun _ h => nomatch h⟩
  cases pc
  · exact rel_step [] (by taint_decide) hpin fun _ _ h hu => hu ▸ setup_ok h
  · exact rel_step [] (by taint_decide) hpin fun _ _ h hu => hu ▸ setup_ok h

omit e in
theorem bytes_call {s u : State} (A : AtCall pc s u) {p : Addr} {n : Nat} (hd : Region.Disjoint ⟨p, n⟩ (kR s))
    (hl : n ≤ 2 ^ 64) : Spec.Rsa.bytesAt u.mem p n = Spec.Rsa.bytesAt s.mem p n :=
  bytes_of_frame A.mem (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) hl

/-- The public data at the call, from the entry states'. -/
theorem priv_facts {u₁ u₂ : State} (A₁ : AtCall pc e.s₁ u₁) (A₂ : AtCall pc e.s₂ u₂) :
    (callE pc e.s₁ u₁).sp = (callE pc e.s₂ u₂).sp ∧
    (∀ r ∈ argRegs, (callE pc e.s₁ u₁).gpr r = (callE pc e.s₂ u₂).gpr r) ∧
    (∀ i < nCallArgs pc, stackArg (callE pc e.s₁ u₁) i = stackArg (callE pc e.s₂ u₂) i) ∧
    Spec.Rsa.bytesAt (callE pc e.s₁ u₁).mem ((callE pc e.s₁ u₁).gpr .a2) ((callE pc e.s₁ u₁).gpr .a3).toNat =
      Spec.Rsa.bytesAt (callE pc e.s₂ u₂).mem ((callE pc e.s₂ u₂).gpr .a2) ((callE pc e.s₂ u₂).gpr .a3).toNat ∧
    Spec.Rsa.bytesAt (callE pc e.s₁ u₁).mem ((callE pc e.s₁ u₁).gpr .a4) ((callE pc e.s₁ u₁).gpr .a5).toNat =
      Spec.Rsa.bytesAt (callE pc e.s₂ u₂).mem ((callE pc e.s₂ u₂).gpr .a4) ((callE pc e.s₂ u₂).gpr .a5).toNat := by
  have m : ∀ {s u : State}, (callE pc s u).mem = u.mem := fun {_ _} => rfl
  refine ⟨by rw [show (callE pc e.s₁ u₁).sp = fb e.s₁ from A₁.sp,
    show (callE pc e.s₂ u₂).sp = fb e.s₂ from A₂.sp, e.fb_eq], fun r hr => ?_,
    fun i hi => by rw [callE_stackArg A₁ hi, callE_stackArg A₂ hi, e.S.arg _ (nCall_nA hi)], ?_, ?_⟩
  · rw [callE_gpr _ _ (fun h => by revert r; decide), callE_gpr _ _ (fun h => by revert r; decide)]
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [A₁.a0, A₂.a0, e.r]
    · rw [A₁.a1, A₂.a1, e.r]
    · rw [A₁.a2, A₂.a2, e.r]
    · rw [A₁.a3, A₂.a3, e.r]
    · rw [A₁.a4, A₂.a4, e.r]
    · rw [A₁.a5, A₂.a5, e.r]
    · rw [A₁.a6, A₂.a6, e.arg]
    · rw [A₁.a7, A₂.a7, e.r]
  · rw [m, m, callE_gpr _ _ (r := .a2), callE_gpr _ _ (r := .a3), callE_gpr _ _ (r := .a2),
      callE_gpr _ _ (r := .a3), A₁.a2, A₁.a3, A₂.a2, A₂.a3,
      bytes_call A₁ e.h₁.kn.symm (by have := e.h₁.wn; omega_using []), bytes_call A₂ e.h₂.kn.symm (by have := e.h₂.wn; omega_using []),
      e.S.n]
  · rw [m, m, callE_gpr _ _ (r := .a4), callE_gpr _ _ (r := .a5), callE_gpr _ _ (r := .a4),
      callE_gpr _ _ (r := .a5), A₁.a4, A₁.a5, A₂.a4, A₂.a5,
      bytes_call A₁ e.h₁.ke.symm (by have := e.h₁.we; omega_using []), bytes_call A₂ e.h₂.ke.symm (by have := e.h₂.we; omega_using []),
      e.S.e]

omit e in
/-- With `pc`, what the call may leak of `pre`, as on entry. -/
theorem pre_leak {s t : State} (X : PreX s) (A : AtCall true s t) :
    Spec.Rsa.privatePrecomputedLeak (callE true s t).mem (stackArg (callE true s t) 12)
        ((callE true s t).gpr .a3).toNat =
      Spec.Rsa.privatePrecomputedLeak s.mem (stackArg s 15) (s.gpr .a4).toNat := by
  have pwl : Spec.Rsa.precomputedWords (s.gpr .a4).toNat ≤ (stackArg s 16).toNat := by
    rw [X.pl]; unfold Spec.Rsa.privatePrecomputedWords; omega_using []
  simp only [Spec.Rsa.privatePrecomputedLeak, callE_stackArg A (i := 12) (by decide),
    callE_gpr (pc := true) s t (r := .a3), A.a3]
  congr 1
  have subPre : Region.Sub ⟨stackArg s 15, 8 * Spec.Rsa.precomputedWords (s.gpr .a4).toNat⟩ (preR s) :=
    fun _ hx => by simp only [Region.Contains] at hx ⊢; omega_using [pwl, hx]
  exact VG.Proof.Rsa.RISCV64.Priv.words_of_frame A.mem (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact X.kP.symm.sub_left subPre) (by have := X.wP; omega_using [pwl, this])

theorem priv_rel : RelCT isa (Rel e (AtCall pc)) (privCall pc) fun _ _ => True := by
  cases pc with
  | false =>
    exact RelCT.callEx (k := Rsa.RISCV64.Priv.fnContract) Rsa.RISCV64.Priv.code_correct Rsa.RISCV64.Priv.code_ct
      fun u₁ u₂ ⟨A₁, A₂⟩ => by
        obtain ⟨hsp, hr, ha, hn, he⟩ := priv_facts A₁ A₂
        exact ⟨callRd false e.s₁, callWr e.s₁, callRd false e.s₂, callWr e.s₂,
          Rsa.RISCV64.Priv.pre_of_preP (preP_entry e.h₁ A₁), Rsa.RISCV64.Priv.pre_of_preP (preP_entry e.h₂ A₂),
          Rsa.RISCV64.Priv.pub_of hsp hr ha hn he, (call_covers e.h₁ A₁).1, (call_covers e.h₁ A₁).2,
          (call_covers e.h₂ A₂).1, (call_covers e.h₂ A₂).2⟩
  | true =>
    exact RelCT.callEx (k := Rsa.RISCV64.Priv.fnContractP) Rsa.RISCV64.Priv.codeP_correct Rsa.RISCV64.Priv.codeP_ct
      fun u₁ u₂ ⟨A₁, A₂⟩ => by
        obtain ⟨hsp, hr, ha, hn, he⟩ := priv_facts A₁ A₂
        have X₁ := e.x₁ rfl
        have X₂ := e.x₂ rfl
        exact ⟨callRd true e.s₁, callWr e.s₁, callRd true e.s₂, callWr e.s₂,
          Rsa.RISCV64.Priv.pre_of_prePX (preP_entry e.h₁ A₁) (preX_entry e.h₁ X₁ A₁),
          Rsa.RISCV64.Priv.pre_of_prePX (preP_entry e.h₂ A₂) (preX_entry e.h₂ X₂ A₂),
          Rsa.RISCV64.Priv.pub_ofP hsp hr ha hn he
            (by rw [pre_leak X₁ A₁, pre_leak X₂ A₂, e.S.leak rfl]),
          (call_covers e.h₁ A₁).1, (call_covers e.h₁ A₁).2, (call_covers e.h₂ A₂).1, (call_covers e.h₂ A₂).2⟩

theorem priv_ct : RelCT isa (Rel e (AtCall pc)) (privCall pc) (Rel e AtRet) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := priv_rel _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨_, u₁, x₁, y₁⟩ := call_ok e.h₁ e.x₁ hp.1 (Q := AtRet e.s₁) fun v hv => hv
  obtain ⟨_, u₂, x₂, y₂⟩ := call_ok e.h₂ e.x₂ hp.2 (Q := AtRet e.s₂) fun v hv => hv
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, y₁, y₂⟩

/-! ## `D` -/

theorem dBuild_ct : RelCT isa (Rel e AtRet) dBuild (Rel e PostAt) :=
  rel_step [.s0, .s1, .s4, .s5] (by taint_decide)
    (fun a b A B => ⟨(post_agree (⟨A.toMid, rfl, rfl⟩ : Post e.s₁ _ _ a) ⟨B.toMid, rfl, rfl⟩).1, fun r hr => by
      have g := post_agree (⟨A.toMid, rfl, rfl⟩ : Post e.s₁ _ _ a) ⟨B.toMid, rfl, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [g.2.1, g.2.2.1, g.2.2.2.2.2.1, g.2.2.2.2.2.2.1]⟩)
    fun s u h A => WP.mono (dBuild_ok h A) fun v hv => ⟨_, _, hv.toPost⟩

/-! ## `DH` -/

def H1 (s u : State) : Prop := PostAt s u ∧ u.gpr .a0 = scA s sSt
def H2 (s u : State) : Prop := UpdAt s u sSt (scA s sD) (s.gpr .a4).toNat ∧ u.gpr .a1 = BitVec.ofNat 64 0
def H3 (s u : State) : Prop := PostAt s u ∧ u.gpr .a0 = scA s sSt ∧ u.gpr .a2 = scA s sDH ∧ u.gpr .a1 = s.gpr .a4

theorem pin_post {P : State → State → Prop} (hp : ∀ s u, P s u → PostAt s u) (rs : List Reg)
    (hrs : ∀ r ∈ rs, r ∈ [Reg.s0, .s1, .s2, .s3, .s4, .s5, .s6] := by decide) :
    ∀ a b, P e.s₁ a → P e.s₂ b → AgreeOn rs a b := fun a b ha hb => by
  obtain ⟨_, _, A⟩ := hp _ _ ha
  obtain ⟨_, _, B⟩ := hp _ _ hb
  have g := post_agree A B
  refine ⟨g.1, fun r hr => ?_⟩
  have := hrs r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [g.2.1, g.2.2.1, g.2.2.2.1, g.2.2.2.2.1, g.2.2.2.2.2.1, g.2.2.2.2.2.2.1, g.2.2.2.2.2.2.2]

theorem hashD_ct : RelCT isa (Rel e PostAt) hashD (Rel e PostAt) := by
  unfold hashD
  refine RelCT.seq (rel_step [.s0] (P' := H1) (by taint_decide) (pin_post (fun _ _ h => h) _)
    fun s u h hp => ?_) ?_
  · unfold shaInitArgs
    exact wp_addi (imm := sSt) fun v o f => wp_nil ⟨hp.only h o, by
      obtain ⟨_, _, P⟩ := hp; rw [f, P.s0]⟩
  refine RelCT.seq (rel_post (P' := PostAt) (shaInit_rel (a := sSt) (by decide) fun _ _ h => h)
    fun s u h ⟨⟨_, _, P⟩, g⟩ => shaInit_ok h P (by decide) g fun w P' _ _ => ⟨_, _, P'⟩) ?_
  refine RelCT.seq (rel_step [.s0, .s1] (P' := H2) (by taint_decide) (pin_post (fun _ _ h => h) _)
    fun s u h hp => ?_) ?_
  · have hk := h.k2
    have lk : sD + (s.gpr .a4).toNat ≤ scrBytes := by unfold sD scrBytes; omega_using [hk]
    unfold shaUpdArgs
    refine wp_addi (imm := sSt) (fun v₁ p₁ f₁ => wp_li (imm := 0) (by decide) fun v₂ p₂ f₂ =>
      wp_addi (imm := sD) (fun v₃ p₃ f₃ => wp_mov fun v₄ p₄ f₄ => wp_nil ?_) (by decide))
    have O : Only [.a0, .a1, .a2, .a3] u v₄ := (p₁.trans (p₂.trans (p₃.trans p₄))).mono
    obtain ⟨_, _, P⟩ := hp
    have P₄ := P.keep h O.keep (ws := []) (by rw [O.mem]; exact Frame.refl _ _) (fun r hr => nomatch hr)
    exact ⟨⟨⟨_, _, P₄⟩, by rw [p₄.get .a0, p₃.get .a0, p₂.get .a0, f₁, P.s0],
      by rw [p₄.get .a2, f₃, p₂.get .s0, p₁.get .s0, P.s0],
      by rw [f₄, p₃.get .s1, p₂.get .s1, p₁.get .s1, P.s1],
      Covers.right (scCov h P₄.wr lk), scDisj (.inr (by decide)) lk (by decide), lowSc h (by decide) lk⟩,
      by rw [p₄.get .a1, p₃.get .a1, f₂]⟩
  refine RelCT.seq (rel_post (P' := PostAt) (shaUpd_rel (a := sSt) (by decide) (dat := fun s => scA s sD)
    (len := fun s => (s.gpr .a4).toNat) (e.scA_eq _) (by rw [e.r]) (fun _ _ h => h.1)
    fun _ _ h₁ h₂ => by rw [h₁.2, h₂.2])
    fun s u h ⟨U, _⟩ => ?_) ?_
  · obtain ⟨_, _, P⟩ := U.post
    exact shaUpd_ok h P (by decide) U.h0 U.h2 U.h3 U.hdc U.hd U.hdl fun w P' _ _ => ⟨_, _, P'⟩
  refine RelCT.seq (rel_step [.s0, .s1] (P' := H3) (by taint_decide) (pin_post (fun _ _ h => h) _)
    fun s u h hp => ?_) ?_
  · unfold shaFinArgs
    refine wp_addi (imm := sSt) (fun w₁ q₁ g₁ => wp_mov fun w₂ q₂ g₂ =>
      wp_addi (imm := sDH) (fun w₃ q₃ g₃ => wp_nil ?_) (by decide))
    have O : Only [.a0, .a1, .a2] u w₃ := (q₁.trans (q₂.trans q₃)).mono
    obtain ⟨_, _, P⟩ := hp
    exact ⟨⟨_, _, P.keep h O.keep (ws := []) (by rw [O.mem]; exact Frame.refl _ _) (fun r hr => nomatch hr)⟩,
      by rw [q₃.get .a0, q₂.get .a0, g₁, P.s0], by rw [g₃, q₂.get .s0, q₁.get .s0, P.s0],
      by rw [q₃.get .a1, g₂, q₁.get .s1, P.s1]⟩
  exact rel_post (shaFin_rel (a := sSt) (o := sDH) (by decide) (by decide) (.inl (by decide)) fun _ _ h => h)
    fun s u h ⟨⟨_, _, P⟩, g0, g2, _⟩ => shaFin_ok h P (by decide) (by decide) (.inl (by decide)) g0 g2
      fun w P' _ _ => ⟨_, _, P'⟩

/-! ## `KDK` -/

def MI (k : Nat) (s u : State) : Prop := PostAt s u ∧ u.gpr .a0 = scA s sSt ∧ u.gpr .a1 = scA s sOuter ∧
  u.gpr .a2 = scA s k ∧ u.gpr .a3 = BitVec.ofNat 64 32
def K2 (s u : State) : Prop := UpdAt s u sSt (stackArg s 1) (s.gpr .a4).toNat ∧ u.gpr .a1 = BitVec.ofNat 64 64
def MF (o : Nat) (cnt : State → BitVec 64) (s u : State) : Prop := PostAt s u ∧ u.gpr .a0 = scA s sSt ∧
  u.gpr .a1 = scA s sOuter ∧ u.gpr .a2 = cnt s ∧ u.gpr .a3 = scA s o

theorem macInitArgs_ct {P : State → State → Prop} (hp : ∀ s u, P s u → PostAt s u) {k : Nat} (hk : k < 2048)
    (hct : RelCT isa (Rel e P) (.block (macInitArgs k)) fun _ _ => True) :
    RelCT isa (Rel e P) (.block (macInitArgs k)) (Rel e (MI k)) :=
  rel_post hct fun s u h hu => by
    obtain ⟨_, _, P⟩ := hp _ _ hu
    exact macInitArgs_ok h P hk fun v P' a0 a1 a2 a3 _ _ => ⟨⟨_, _, P'⟩, a0, a1, a2, a3⟩

theorem macInit_ct {k : Nat} (hk : k + 32 ≤ scrBytes) (hk1 : sOuter + 96 ≤ k) :
    RelCT isa (Rel e (MI k)) macInitCall (Rel e PostAt) :=
  rel_post (macInit_rel hk hk1 fun _ _ h => h) fun s u h ⟨⟨_, _, P⟩, a0, a1, a2, a3⟩ =>
    macInit_ok h P (i := sSt) (u := sOuter) (k := k) (by decide) (by decide) hk (.inl (by decide))
      (.inr (by unfold sSt sOuter at *; omega_using [hk1])) (.inr hk1) a0 a1 a2 a3 fun w P' _ _ _ => ⟨_, _, P'⟩

theorem macFin_ct {o : Nat} (ho : o + 32 ≤ scrBytes) (ho1 : sOuter + 96 ≤ o) {cnt : State → BitVec 64}
    (hcnt : cnt e.s₁ = cnt e.s₂) : RelCT isa (Rel e (MF o cnt)) macFinCall (Rel e PostAt) :=
  rel_post (macFin_rel ho ho1 hcnt fun _ _ h => h) fun s u h ⟨⟨_, _, P⟩, a0, a1, _, a3⟩ =>
    macFin_ok h P (i := sSt) (u := sOuter) (o := o) (by decide) (by decide) ho (.inl (by decide))
      (.inl (by unfold sSt sOuter at *; omega_using [ho1])) (.inl ho1) a0 a1 a3 fun w P' _ _ => ⟨_, _, P'⟩

theorem kdkMac_ct : RelCT isa (Rel e PostAt) kdkMac (Rel e PostAt) := by
  unfold kdkMac
  refine RelCT.seq (macInitArgs_ct (fun _ _ h => h) (k := sDH) (by decide)
    (rel_of (rs := [.s0]) (by taint_decide) fun a b h => pin_post (fun _ _ h => h) [.s0] (by decide) a b h.1 h.2)) ?_
  refine RelCT.seq (macInit_ct (by decide) (by decide)) ?_
  refine RelCT.seq (rel_step [.s0, .s1, .s6] (P' := K2) (by taint_decide) (pin_post (fun _ _ h => h) _)
    fun s u h hp => ?_) ?_
  · have hk := h.k2
    unfold kdkUpdArgs
    refine wp_addi (imm := sSt) (fun v₁ p₁ f₁ => wp_li (imm := 64) (by decide) fun v₂ p₂ f₂ =>
      wp_mov fun v₃ p₃ f₃ => wp_mov fun v₄ p₄ f₄ => wp_nil ?_) (by decide)
    have O : Only [.a0, .a1, .a2, .a3] u v₄ := (p₁.trans (p₂.trans (p₃.trans p₄))).mono
    obtain ⟨_, _, P⟩ := hp
    have P₄ := P.keep h O.keep (ws := []) (by rw [O.mem]; exact Frame.refl _ _) (fun r hr => nomatch hr)
    exact ⟨⟨⟨_, _, P₄⟩, by rw [p₄.get .a0, p₃.get .a0, p₂.get .a0, f₁, P.s0],
      by rw [p₄.get .a2, f₃, p₂.get .s6, p₁.get .s6, P.s6],
      by rw [f₄, p₃.get .s1, p₂.get .s1, p₁.get .s1, P.s1], c_cov h P₄, c_sc h (by decide), c_low h (by decide)⟩,
      by rw [p₄.get .a1, p₃.get .a1, f₂]⟩
  refine RelCT.seq (rel_post (P' := PostAt) (shaUpd_rel (a := sSt) (by decide) (dat := fun s => stackArg s 1)
    (len := fun s => (s.gpr .a4).toNat) e.arg (by rw [e.r]) (fun _ _ h => h.1)
    fun _ _ h₁ h₂ => by rw [h₁.2, h₂.2])
    fun s u h ⟨U, _⟩ => ?_) ?_
  · obtain ⟨_, _, P⟩ := U.post
    exact shaUpd_ok h P (by decide) U.h0 U.h2 U.h3 U.hdc U.hd U.hdl fun w P' _ _ => ⟨_, _, P'⟩
  refine RelCT.seq (rel_step [.s0, .s1] (P' := MF sKDK fun s => s.gpr .a4 + BitVec.ofNat 64 64) (by taint_decide)
    (pin_post (fun _ _ h => h) _) fun s u h hp => ?_) (macFin_ct (by decide) (by decide) (by rw [e.r]))
  unfold kdkFinArgs
  refine wp_addi (imm := sSt) (fun w₁ q₁ g₁ => wp_addi (imm := sOuter) (fun w₂ q₂ g₂ =>
    wp_addi (imm := 64) (fun w₃ q₃ g₃ => wp_addi (imm := sKDK) (fun w₄ q₄ g₄ => wp_nil ?_) (by decide))
    (by decide)) (by decide)) (by decide)
  have O : Only [.a0, .a1, .a2, .a3] u w₄ := (q₁.trans (q₂.trans (q₃.trans q₄))).mono
  obtain ⟨_, _, P⟩ := hp
  exact ⟨⟨_, _, P.keep h O.keep (ws := []) (by rw [O.mem]; exact Frame.refl _ _) (fun r hr => nomatch hr)⟩,
    by rw [q₄.get .a0, q₃.get .a0, q₂.get .a0, g₁, P.s0], by rw [q₄.get .a1, q₃.get .a1, g₂, q₁.get .s0, P.s0],
    by rw [q₄.get .a2, g₃, q₂.get .s1, q₁.get .s1, P.s1], by rw [g₄, q₃.get .s0, q₂.get .s0, q₁.get .s0, P.s0]⟩

end

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec

end

end

/-!
# `vg_rsa_pkcs1_decrypt` on RISC-V: constant time of `CL` and `AM`

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Enc/PPC64LE/DecVerified.lean`): a block of IRPRF in two runs
(`prfBody_ct`), its blocks by the taint analysis and its calls by
`macInit_rel`, …, with the counter `i` in `s8` and the number of `AM`'s blocks
in `s9` (`L i`); and the loops of `CL` and `AM`, whose counters agree
(`clLoop_ct`, `amLoop_ct`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec

open VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt VG.Proof.RsaPkcs1Sig.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (mov)

variable {pc : Bool}

/-- The number of `AM`'s blocks. -/
abbrev nbOf (s : State) : BitVec 64 := BitVec.ofNat 64 (((s.gpr .a4).toNat + 31) / 32)

/-- The counter and the number of `AM`'s blocks. -/
def W8 (i : Nat) (s u : State) : Prop := u.gpr .s8 = BitVec.ofNat 64 i ∧ u.gpr .s9 = nbOf s

/-- In the loops, before block `i`. -/
def L (i : Nat) (s u : State) : Prop := PostAt s u ∧ W8 i s u

theorem W8.only {i : Nat} {s u v : State} (w : W8 i s u) {rs : List Reg} (o : Kept rs u v)
    (h8 : Reg.s8 ∉ rs := by decide) (h9 : Reg.s9 ∉ rs := by decide) : W8 i s v :=
  ⟨(o.gpr _ h8).trans w.1, (o.gpr _ h9).trans w.2⟩

theorem W8.after {i : Nat} {s u v : State} (w : W8 i s u) {ws : List Region} (a : After u ws v) : W8 i s v :=
  ⟨(a.cs _ (by decide)).trans w.1, (a.cs _ (by decide)).trans w.2⟩

section
variable {e : Env pc}

theorem w8_agree {i : Nat} {a b : State} (ha : W8 i e.s₁ a) (hb : W8 i e.s₂ b) :
    a.gpr .s8 = b.gpr .s8 ∧ a.gpr .s9 = b.gpr .s9 :=
  ⟨by rw [ha.1, hb.1], by rw [ha.2, hb.2, nbOf, nbOf, e.r]⟩

/-- Two runs that satisfy `PostAt` and `W8 i` agree on `s0`–`s6`, `s8` and `s9`. -/
theorem pin_L {P : State → State → Prop} {i : Nat} (hp : ∀ s u, P s u → PostAt s u ∧ W8 i s u) (rs : List Reg)
    (hrs : ∀ r ∈ rs, r ∈ [Reg.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s8, .s9] := by decide) :
    ∀ a b, P e.s₁ a → P e.s₂ b → AgreeOn rs a b := fun a b ha hb => by
  obtain ⟨⟨_, _, A⟩, wa⟩ := hp _ _ ha
  obtain ⟨⟨_, _, B⟩, wb⟩ := hp _ _ hb
  have g := post_agree A B
  have g8 := w8_agree wa wb
  refine ⟨g.1, fun r hr => ?_⟩
  have := hrs r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [g.2.1, g.2.2.1, g.2.2.2.1, g.2.2.2.2.1, g.2.2.2.2.2.1, g.2.2.2.2.2.2.1, g.2.2.2.2.2.2.2, g8.1, g8.2]

/-- The taint checks of a block of IRPRF's blocks. -/
structure PrfTaint (label : List Nat) (len count : List Instr) (dst : Nat) : Prop where
  msg : ∃ hc, (taint.check (VG.RISCV64.Taint.ofRegs [.s0, .s1, .s8]) (.block (msgBytes label len)) hc).isSome = true
  ini : ∃ hc, (taint.check (VG.RISCV64.Taint.ofRegs [.s0]) (.block (macInitArgs sKDK)) hc).isSome = true
  upd : ∃ hc, (taint.check (VG.RISCV64.Taint.ofRegs [.s0]) (.block (prfUpdArgs (label.length + 4))) hc).isSome = true
  fin : ∃ hc, (taint.check (VG.RISCV64.Taint.ofRegs [.s0, .s8]) (.block (prfFinArgs (label.length + 4) dst)) hc).isSome
    = true
  incr : ∃ hc, (taint.check (VG.RISCV64.Taint.ofRegs [.s8, .s9]) (.block (incr count)) hc).isSome = true

/-- Block `i` of IRPRF, in two runs: after it, `L (i + 1)` and the blocks left
`C - (i + 1)` in `t1`, for `C` a function of the entry state. -/
theorem prfBody_ct {label : List Nat} {len count : List Instr} {dst : Nat} (T : PrfTaint label len count dst)
    {C : State → BitVec 64} {i : Nat} (hi : i < 256) (hd1 : sCL ≤ dst) (hd2 : dst + 32 * i + 32 ≤ scrBytes)
    (hdst : dst < 2048) (hn : label.length + 4 ≤ 16)
    (hmsg : ∀ s R EM u, DPre pc s → Post s R EM u → u.gpr .s8 = BitVec.ofNat 64 i →
      WP isa (.block (msgBytes label len)) u fun w => Frame [⟨scA s sMsg, 16⟩] u.mem w.mem ∧ Kept [.t1, .t2] u w)
    (hcount : ∀ s u, u.gpr .s9 = nbOf s →
      WP isa (.block (count ++ ([.sub .t1 .t1 .s8] : List Instr))) u fun w => Only [.t1] u w ∧ w.gpr .t1 = C s - u.gpr .s8) :
    RelCT isa (Rel e (L i)) (prfBody label len dst count)
      (Rel e fun s u => L (i + 1) s u ∧ u.gpr .t1 = C s - BitVec.ofNat 64 (i + 1)) := by
  have zz := hmac_sizes
  unfold prfBody
  -- The message.
  refine RelCT.seq (rel_post (P' := L i) (rel_of T.msg.choose_spec fun a b h => pin_L (fun _ _ h => h) _ (by decide) a b h.1 h.2)
    fun s u h ⟨⟨_, _, P⟩, w⟩ => WP.mono (hmsg s _ _ u h P w.1) fun v ⟨F, K⟩ =>
      ⟨⟨_, _, P.keep h K F fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (scSub h (by decide))⟩,
        w.only K⟩) ?_
  -- HMAC's `init` with `KDK`.
  refine RelCT.seq (rel_post (P' := fun s u => MI sKDK s u ∧ W8 i s u)
    (rel_of T.ini.choose_spec fun a b h => pin_L (fun _ _ h => h) _ (by decide) a b h.1 h.2)
    fun s u h ⟨⟨_, _, P⟩, w⟩ => macInitArgs_ok h P (by decide) fun v P' a0 a1 a2 a3 _ K =>
      ⟨⟨⟨_, _, P'⟩, a0, a1, a2, a3⟩, w.only K⟩) ?_
  refine RelCT.seq (rel_post (P' := L i) (macInit_rel (by decide) (by decide) fun _ _ h => h.1)
    fun s u h ⟨⟨⟨_, _, P⟩, a0, a1, a2, a3⟩, w⟩ =>
      macInit_ok h P (i := sSt) (u := sOuter) (k := sKDK) (by decide) (by decide) (by decide) (.inl (by decide))
        (.inr (by decide)) (.inr (by decide)) a0 a1 a2 a3 fun v P' A _ _ => ⟨⟨_, _, P'⟩, w.after A⟩) ?_
  -- `update` with the message.
  refine RelCT.seq (rel_post (P' := fun s u => (UpdAt s u sSt (scA s sMsg) (label.length + 4) ∧
      u.gpr .a1 = BitVec.ofNat 64 64) ∧ W8 i s u)
    (rel_of T.upd.choose_spec fun a b h => pin_L (fun _ _ h => h) _ (by decide) a b h.1 h.2) fun s u h ⟨⟨_, _, P⟩, w⟩ => ?_) ?_
  · unfold prfUpdArgs
    refine wp_addi (imm := sSt) (fun v₁ p₁ f₁ => wp_li (imm := 64) (by decide) fun v₂ p₂ f₂ =>
      wp_addi (imm := sMsg) (fun v₃ p₃ f₃ => wp_li (imm := label.length + 4) (by omega) fun v₄ p₄ f₄ =>
        wp_nil ?_) (by decide)) (by decide)
    have O : Only [.a0, .a1, .a2, .a3] u v₄ := (p₁.trans (p₂.trans (p₃.trans p₄))).mono
    have P₄ := P.keep h O.keep (ws := []) (by rw [O.mem]; exact Frame.refl _ _) (fun r hr => nomatch hr)
    have lm : sMsg + (label.length + 4) ≤ scrBytes := by unfold sMsg scrBytes; omega
    exact ⟨⟨⟨⟨_, _, P₄⟩, by rw [p₄.get .a0, p₃.get .a0, p₂.get .a0, f₁, P.s0],
      by rw [p₄.get .a2, f₃, p₂.get .s0, p₁.get .s0, P.s0], by rw [f₄, BitVec.toNat_ofNat]; omega,
      Covers.right (scCov h P₄.wr lm), scDisj (.inr (by decide)) lm (by decide), lowSc h (by decide) lm⟩,
      by rw [p₄.get .a1, p₃.get .a1, f₂]⟩, w.only O.keep⟩
  refine RelCT.seq (rel_post (P' := L i) (shaUpd_rel (a := sSt) (by decide) (dat := fun s => scA s sMsg)
    (len := fun _ => label.length + 4) (e.scA_eq _) rfl (fun _ _ h => h.1.1)
    fun _ _ h₁ h₂ => by rw [h₁.1.2, h₂.1.2])
    fun s u h ⟨⟨U, _⟩, w⟩ => ?_) ?_
  · obtain ⟨_, _, P⟩ := U.post
    exact shaUpd_ok h P (by decide) U.h0 U.h2 U.h3 U.hdc U.hd U.hdl fun v P' A _ => ⟨⟨_, _, P'⟩, w.after A⟩
  -- HMAC's `finalize` to the block.
  refine RelCT.seq (rel_post (P' := fun s u => MF (dst + 32 * i) (fun _ => BitVec.ofNat 64 (64 + (label.length + 4)))
      s u ∧ W8 i s u)
    (rel_of T.fin.choose_spec fun a b h => pin_L (fun _ _ h => h) _ (by decide) a b h.1 h.2) fun s u h ⟨⟨_, _, P⟩, w⟩ => ?_) ?_
  · unfold prfFinArgs
    refine wp_addi (imm := sSt) (fun w₁ q₁ g₁ => wp_addi (imm := sOuter) (fun w₂ q₂ g₂ =>
      wp_li (imm := 64 + (label.length + 4)) (by omega) fun w₃ q₃ g₃ => wp_sll (sh := 5) (fun w₄ q₄ g₄ =>
      wp_add fun w₅ q₅ g₅ => wp_addi (imm := dst) (fun w₆ q₆ g₆ => wp_nil ?_) hdst)) (by decide)) (by decide)
    have O : Only [.a0, .a1, .a2, .a3] u w₆ := (q₁.trans (q₂.trans (q₃.trans (q₄.trans (q₅.trans q₆))))).mono
    exact ⟨⟨⟨_, _, P.keep h O.keep (ws := []) (by rw [O.mem]; exact Frame.refl _ _) (fun r hr => nomatch hr)⟩,
      by rw [q₆.get .a0, q₅.get .a0, q₄.get .a0, q₃.get .a0, q₂.get .a0, g₁, P.s0],
      by rw [q₆.get .a1, q₅.get .a1, q₄.get .a1, q₃.get .a1, g₂, q₁.get .s0, P.s0],
      by rw [q₆.get .a2, q₅.get .a2, q₄.get .a2, g₃],
      by rw [g₆, g₅, g₄, q₃.get .s8, q₂.get .s8, q₁.get .s8, w.1, q₄.get .s0, q₃.get .s0, q₂.get .s0,
        q₁.get .s0, P.s0, shl5]⟩, w.only O.keep⟩
  refine RelCT.seq (rel_post (P' := L i) (macFin_rel hd2 (by unfold sOuter sCL at *; omega) rfl fun _ _ h => h.1)
    fun s u h ⟨⟨⟨_, _, P⟩, a0, a1, _, a3⟩, w⟩ =>
      macFin_ok h P (i := sSt) (u := sOuter) (o := dst + 32 * i) (by decide) (by decide) hd2 (.inl (by decide))
        (.inl (by unfold sSt sCL at *; omega)) (.inl (by unfold sOuter sCL at *; omega)) a0 a1 a3
        fun v P' A _ => ⟨⟨_, _, P'⟩, w.after A⟩) ?_
  -- The counter.
  refine rel_post (rel_of T.incr.choose_spec fun a b h => pin_L (fun _ _ h => h) _ (by decide) a b h.1 h.2)
    fun s u h ⟨⟨_, _, P⟩, w⟩ => ?_
  simp only [incr, List.cons_append, List.nil_append]
  refine wp_addi (imm := 1) (fun x₁ r₁ i₁ => WP.mono (hcount s x₁ (by rw [r₁.get .s9, w.2]))
    fun v ⟨Ov, xv⟩ => ?_) (by decide)
  have O : Only [.s8, .t1] u v := (r₁.trans Ov).mono
  have one : BitVec.ofNat 64 i + BitVec.ofNat 64 1 = BitVec.ofNat 64 (i + 1) := BitVec.ofNat_add _ _ |>.symm
  exact ⟨⟨⟨_, _, P.keep h O.keep (ws := []) (by rw [O.mem]; exact Frame.refl _ _) (fun r hr => nomatch hr)⟩,
    by rw [Ov.get .s8, i₁, w.1, one], by rw [O.get .s9, w.2]⟩, by rw [xv, i₁, w.1, one]⟩

/-- The loop of IRPRF's `N` blocks, in two runs, with `C - (i + 1)` blocks
left after block `i`. -/
theorem prfLoop_ct {label : List Nat} {len count : List Instr} {dst N : Nat} (T : PrfTaint label len count dst)
    {C : State → BitVec 64} (hC : C e.s₁ = C e.s₂) (hCN : ∀ i < N,
      C e.s₁ - BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 (N - (i + 1)))
    (hN0 : 0 < N) (hN : N ≤ 256) (hd1 : sCL ≤ dst) (hd2 : dst + 32 * N ≤ scrBytes) (hdst : dst < 2048)
    (hn : label.length + 4 ≤ 16)
    (hmsg : ∀ i < N, ∀ s R EM u, DPre pc s → Post s R EM u → u.gpr .s8 = BitVec.ofNat 64 i →
      WP isa (.block (msgBytes label len)) u fun w => Frame [⟨scA s sMsg, 16⟩] u.mem w.mem ∧ Kept [.t1, .t2] u w)
    (hcount : ∀ s u, u.gpr .s9 = nbOf s →
      WP isa (.block (count ++ ([.sub .t1 .t1 .s8] : List Instr))) u fun w => Only [.t1] u w ∧ w.gpr .t1 = C s - u.gpr .s8) :
    RelCT isa (Rel e (L 0)) (.loop (prfBody label len dst count) (.nonzero .t1))
      (Rel e fun s u => PostAt s u ∧ u.gpr .s9 = nbOf s) := by
  refine (RelCT.loop (Q := Rel e fun s u => PostAt s u ∧ u.gpr .s9 = nbOf s) (fun m a b => ∃ i, m = N - i ∧ i < N ∧ Rel e (L i) a b)
    (fun m => ?_) N).mono (fun a b h => ⟨0, by omega_using [], hN0, h⟩) fun _ _ h => h
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨i, hm, hiN, hp⟩ e₁ e₂
  obtain ⟨ht, ⟨l₁, c₁⟩, ⟨l₂, c₂⟩⟩ := prfBody_ct (e := e) T (C := C) (i := i) (by omega_using [hN, hiN]) hd1 (by omega_using [hd2, hiN]) hdst hn
    (hmsg i hiN) hcount s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  have v₁ : s₁'.gpr .t1 = BitVec.ofNat 64 (N - (i + 1)) := by rw [c₁, hCN i hiN]
  have v₂ : s₂'.gpr .t1 = BitVec.ofNat 64 (N - (i + 1)) := by rw [c₂, ← hC, hCN i hiN]
  have hz : isa.eval (.nonzero .t1) s₁' = some (decide (i + 1 ≠ N)) := by
    rw [eval_nonzero, ne_zero_iff, v₁]
    exact congrArg some (decide_eq_decide.mpr (counter_ne hiN (by omega_using [hN])))
  have hz₂ : isa.eval (.nonzero .t1) s₂' = some (decide (i + 1 ≠ N)) := by
    rw [eval_nonzero, ne_zero_iff, v₂]
    exact congrArg some (decide_eq_decide.mpr (counter_ne hiN (by omega_using [hN])))
  refine ⟨ht, by rw [hz, hz₂], fun hf => ⟨⟨l₁.1, l₁.2.2⟩, ⟨l₂.1, l₂.2.2⟩⟩, fun ht' => ⟨N - (i + 1), by
    rw [hz] at ht'; simp at ht'; omega_using [hm, hiN], i + 1, rfl, by rw [hz] at ht'; simp at ht'; omega_using [hiN, ht'], l₁, l₂⟩⟩

end

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec

end

end

/-! ### `RsaPkcs1Enc.RISCV64.Dec.Correct`, which this module and modules that import it used -/

section

/-! ### `RsaPkcs1Enc.RISCV64.Dec.Out`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.RISCV64.Dec.Sel`, which only this module used -/

section

/-! ### `RsaPkcs1Enc.RISCV64.Dec.Al`, which only this module used -/

section

/-!
# `vg_rsa_pkcs1_decrypt` on RISC-V: the alternative length

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Enc/PPC64LE/DecAl.lean`): the mask of the candidates,
`bitMask (k - 11)`, by doublings (`maskPart_ok`), and the alternative length,
the last masked candidate of `CL` not above `k - 11` (`alPart_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec

open VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt VG.Proof.RsaPkcs1Sig.RISCV64
open VG.Proof.RsaPkcs1Enc (bitMask altStep)

variable {pc : Bool}

/-- The borrow of `a - b`, for values below `2 ^ 63`. -/
theorem borrow (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63 = BitVec.ofNat 64 (if b ≤ a then 0 else 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  split <;> omega_arith

/-- The select by a mask from a borrow. -/
theorem xor_sel (a c : BitVec 64) (p : Prop) [Decidable p] :
    a ^^^ ((a ^^^ c) &&& (BitVec.ofNat 64 (if p then 0 else 1) - BitVec.ofNat 64 1)) = if p then c else a := by
  by_cases hp : p
  · simp only [hp, ↓reduceIte]
    rw [show BitVec.ofNat 64 0 - BitVec.ofNat 64 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes,
      ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · simp only [hp, ↓reduceIte, BitVec.sub_self, BitVec.and_zero, BitVec.xor_zero]

theorem maskBody_ok {t : State} :
    WP isa (.block [.add .t4 .t4 .t4, .addi .t4 .t4 1, .sub .t5 .t4 .t3, .shift .srl .d .t5 .t5 63]) t
      fun u => Only [.t4, .t5] t u ∧ u.gpr .t4 = t.gpr .t4 + t.gpr .t4 + BitVec.ofNat 64 1 ∧
        u.gpr .t5 = (t.gpr .t4 + t.gpr .t4 + BitVec.ofNat 64 1 - t.gpr .t3) >>> 63 :=
  wp_add fun v₁ p₁ f₁ => wp_addi (imm := 1) (fun v₂ p₂ f₂ => wp_sub fun v₃ p₃ f₃ => wp_srl (sh := 63)
    fun v₄ p₄ f₄ => wp_nil ⟨(p₁.trans (p₂.trans (p₃.trans p₄))).mono, by rw [p₄.get .t4, p₃.get .t4, f₂, f₁],
      by rw [f₄, f₃, f₂, f₁, p₂.get .t3, p₁.get .t3]⟩) (by decide)

theorem dbl (p : Nat) (h1 : 1 ≤ p) (h : p * 2 < 2 ^ 34) :
    BitVec.ofNat 64 (p - 1) + BitVec.ofNat 64 (p - 1) + BitVec.ofNat 64 1 = BitVec.ofNat 64 (p * 2 - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- An iteration of the mask's loop: `2 ^ j - 1` to `2 ^ (j + 1) - 1`, and whether to go on. -/
theorem maskStep_ok {x j : Nat} (hx1 : 1 ≤ x) (hx : x < 2 ^ 32) (hj : j < Spec.RsaPkcs1Enc.bitLength x)
    {u : State} (hu4 : u.gpr .t4 = BitVec.ofNat 64 (2 ^ j - 1)) (hu3 : u.gpr .t3 = BitVec.ofNat 64 x) :
    WP isa (.block [.add .t4 .t4 .t4, .addi .t4 .t4 1, .sub .t5 .t4 .t3, .shift .srl .d .t5 .t5 63]) u
      fun w => (Only [.t4, .t5] u w ∧ w.gpr .t4 = BitVec.ofNat 64 (2 ^ (j + 1) - 1)) ∧
        ((w.gpr .t5).toNat ≠ 0 ↔ j + 1 ≠ Spec.RsaPkcs1Enc.bitLength x) := by
  have hlt := Proof.RsaPkcs1Enc.bitMask_lt (x := x) (j := j) (by omega_using [hx1]) hj
  have hpj : 2 ^ (j + 1) < 2 ^ 34 := by
    rw [Nat.pow_succ]; generalize 2 ^ j = p at *; omega_using [hx, hlt]
  have e8 : BitVec.ofNat 64 (2 ^ j - 1) + BitVec.ofNat 64 (2 ^ j - 1) + BitVec.ofNat 64 1 =
      BitVec.ofNat 64 (2 ^ (j + 1) - 1) := by
    rw [show 2 ^ (j + 1) = 2 ^ j * 2 from Nat.pow_succ ..] at hpj ⊢
    exact dbl _ Nat.one_le_two_pow hpj
  refine WP.mono maskBody_ok fun w ⟨kw, w4, w5⟩ => ⟨⟨kw, by rw [w4, hu4, e8]⟩, ?_⟩
  rw [w5, hu4, hu3, e8, borrow _ _ (by omega_using [hpj]) (by omega_using [hx]), BitVec.toNat_ofNat]
  by_cases he : j + 1 = Spec.RsaPkcs1Enc.bitLength x
  · have h1 := Proof.RsaPkcs1Enc.bitMask_ge (x := x) (by omega_using [hx1])
    rw [he]
    simp only [show x ≤ 2 ^ Spec.RsaPkcs1Enc.bitLength x - 1 from h1, ↓reduceIte]; omega_using []
  · have h1 := Proof.RsaPkcs1Enc.bitMask_lt (x := x) (j := j + 1) (by omega_using [hx1]) (by omega_using [hj, he])
    simp only [show ¬ x ≤ 2 ^ (j + 1) - 1 by omega_using [h1], ↓reduceIte]; omega_using [he]

theorem bitLength_pos {x : Nat} (hx1 : 1 ≤ x) : 0 < Spec.RsaPkcs1Enc.bitLength x := by
  simp only [Spec.RsaPkcs1Enc.bitLength]; split <;> omega_arith

theorem maskLoop_ok {t₀ : State} {x : Nat} (hx1 : 1 ≤ x) (hx : x < 2 ^ 32) (h4 : t₀.gpr .t4 = BitVec.ofNat 64 0)
    (h3 : t₀.gpr .t3 = BitVec.ofNat 64 x) :
    WP isa maskLoop t₀ fun u => Only [.t4, .t5] t₀ u ∧ u.gpr .t4 = BitVec.ofNat 64 (bitMask x) :=
  VG.Proof.Bignum.RISCV64.count_loop (bitLength_pos hx1) (fun j u => Only [.t4, .t5] t₀ u ∧
    u.gpr .t4 = BitVec.ofNat 64 (2 ^ j - 1))
    (fun _ hj u ⟨hk, hu4⟩ => WP.mono (maskStep_ok hx1 hx hj hu4
      (by rw [hk.get .t3, h3])) fun _ ⟨⟨kw, w4⟩, w5⟩ => ⟨⟨(hk.trans kw).mono, w4⟩, w5⟩)
    ⟨Only.refl _ _, h4⟩

theorem cand_bv (a b : Byte) {M : Nat} (hM : M < 2 ^ 64) :
    (a.setWidth 64 <<< 8 + b.setWidth 64) &&& BitVec.ofNat 64 M =
      BitVec.ofNat 64 ((256 * a.toNat + b.toNat) &&& M) := by
  have ha := a.isLt
  have hb := b.isLt
  apply BitVec.eq_of_toNat_eq
  have hl : (256 * a.toNat + b.toNat) &&& M ≤ 256 * a.toNat + b.toNat := Nat.and_le_left
  simp only [BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (a := a.toNat) (by omega_using []), Nat.mod_eq_of_lt (a := b.toNat) (by omega_using []),
    Nat.mod_eq_of_lt (a := M) hM, Nat.mod_eq_of_lt (a := a.toNat * 2 ^ 8) (by omega_using []),
    Nat.mod_eq_of_lt (a := a.toNat * 2 ^ 8 + b.toNat) (by omega_using []), show a.toNat * 2 ^ 8 = 256 * a.toNat by omega_using [],
    Nat.mod_eq_of_lt (by omega_using [hl])]

/-- The candidate at `t1`, masked by `t4`. -/
abbrev cand (t : State) : BitVec 64 :=
  ((t.mem (t.gpr .t1 + BitVec.ofNat 64 0)).setWidth 64 <<< 8 +
    (t.mem (t.gpr .t1 + BitVec.ofNat 64 1)).setWidth 64) &&& t.gpr .t4

theorem alBody_ok {t : State} (h0 : InRegions (t.rd ++ t.wr) (t.gpr .t1 + BitVec.ofNat 64 0) 1)
    (h1 : InRegions (t.rd ++ t.wr) (t.gpr .t1 + BitVec.ofNat 64 1) 1) :
    WP isa (.block alBody) t fun u => Only [.a0, .a1, .a2, .t6, .t1, .t2] t u ∧
      u.gpr .t1 = t.gpr .t1 + BitVec.ofNat 64 2 ∧ u.gpr .t2 = t.gpr .t2 - BitVec.ofNat 64 1 ∧
      u.gpr .t6 = t.gpr .t6 ^^^ ((t.gpr .t6 ^^^ cand t) &&& (((t.gpr .t3 - cand t) >>> 63) - BitVec.ofNat 64 1)) := by
  unfold alBody
  refine wp_lbu rfl h0 fun v₁ p₁ f₁ => wp_sll (sh := 8) fun v₂ p₂ f₂ =>
    wp_lbu (a := t.gpr .t1 + BitVec.ofNat 64 1) (by rw [p₂.get .t1, p₁.get .t1])
      (by rw [p₂.rd, p₂.wr, p₁.rd, p₁.wr]; exact h1) fun v₃ p₃ f₃ =>
    wp_add fun v₄ p₄ f₄ => wp_and fun v₅ p₅ f₅ => wp_sub fun v₆ p₆ f₆ => wp_srl (sh := 63) fun v₇ p₇ f₇ =>
    wp_subi (imm := 1) (fun v₈ p₈ f₈ => wp_xor fun v₉ p₉ f₉ => wp_and fun v₁₀ p₁₀ f₁₀ =>
    wp_xor fun v₁₁ p₁₁ f₁₁ => wp_addi (imm := 2) (fun v₁₂ p₁₂ f₁₂ => wp_subi (imm := 1) (fun v₁₃ p₁₃ f₁₃ =>
      wp_nil ?_) (by decide)) (by decide)) (by decide)
  have O₁ : Only [.a0, .a1, .a2, .t6, .t1, .t2] t v₅ := (p₁.trans (p₂.trans (p₃.trans (p₄.trans p₅)))).mono
  have O₂ : Only [.a0, .a1, .a2, .t6, .t1, .t2] v₅ v₉ := (p₆.trans (p₇.trans (p₈.trans p₉))).mono
  have O₃ : Only [.a0, .a1, .a2, .t6, .t1, .t2] v₉ v₁₃ := (p₁₀.trans (p₁₁.trans (p₁₂.trans p₁₃))).mono
  have O : Only [.a0, .a1, .a2, .t6, .t1, .t2] t v₁₃ := (O₁.trans (O₂.trans O₃)).mono
  have c : v₅.gpr .a0 = cand t := by
    rw [f₅, f₄, p₃.get .a0, f₂, f₁, f₃, p₂.mem, p₁.mem, p₄.get .t4, p₃.get .t4, p₂.get .t4, p₁.get .t4]
  refine ⟨O, ?_, ?_, ?_⟩
  · rw [p₁₃.get .t1, f₁₂, p₁₁.get .t1, p₁₀.get .t1, p₉.get .t1, p₈.get .t1, p₇.get .t1, p₆.get .t1, p₅.get .t1,
      p₄.get .t1, p₃.get .t1, p₂.get .t1, p₁.get .t1]
  · rw [f₁₃, p₁₂.get .t2, p₁₁.get .t2, p₁₀.get .t2, p₉.get .t2, p₈.get .t2, p₇.get .t2, p₆.get .t2, p₅.get .t2,
      p₄.get .t2, p₃.get .t2, p₂.get .t2, p₁.get .t2]
  · have g6 : v₅.gpr .t6 = t.gpr .t6 := by
      rw [p₅.get .t6, p₄.get .t6, p₃.get .t6, p₂.get .t6, p₁.get .t6]
    have g3 : v₅.gpr .t3 = t.gpr .t3 := by
      rw [p₅.get .t3, p₄.get .t3, p₃.get .t3, p₂.get .t3, p₁.get .t3]
    rw [p₁₃.get .t6, p₁₂.get .t6, f₁₁, f₁₀, f₉, p₉.get .a1, f₈, f₇, f₆, p₁₀.get .t6, p₉.get .t6, p₈.get .t6,
      p₇.get .t6, p₆.get .t6, p₈.get .a0, p₇.get .a0, p₆.get .a0, g6, g3, c]

theorem bytes_getD (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (Spec.Rsa.bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, hi]

theorem alLoop_ok {t₀ : State} {x M : Nat} {CL : List Byte} {B : Addr}
    (hx : x < 2 ^ 32) (hM : M = bitMask x) (hMl : M < 2 ^ 32)
    (hm : ∀ i < 256, t₀.mem (B + BitVec.ofNat 64 i) = CL.getD i 0)
    (hr : ∀ i < 256, InRegions (t₀.rd ++ t₀.wr) (B + BitVec.ofNat 64 i) 1)
    (h4 : t₀.gpr .t4 = BitVec.ofNat 64 M) (h3 : t₀.gpr .t3 = BitVec.ofNat 64 x) (h1 : t₀.gpr .t1 = B)
    (h2 : t₀.gpr .t2 = BitVec.ofNat 64 128) (h6 : t₀.gpr .t6 = 0) :
    WP isa alLoop t₀ fun u => Only [.a0, .a1, .a2, .t6, .t1, .t2] t₀ u ∧
      u.gpr .t6 = BitVec.ofNat 64 ((List.range 128).foldl (altStep (x + 11) CL) 0) := by
  refine VG.Proof.Bignum.RISCV64.wp_countdown (cnt := .t2) (N := 128) (by decide) (by decide)
    (fun j u => Only [.a0, .a1, .a2, .t6, .t1, .t2] t₀ u ∧ u.gpr .t1 = B + BitVec.ofNat 64 (2 * j) ∧
      u.gpr .t6 = BitVec.ofNat 64 ((List.range j).foldl (altStep (x + 11) CL) 0))
    (fun j hj u ⟨ku, u1, u6⟩ _ => ?_) ⟨Only.refl _ _, by rw [h1]; exact (BitVec.add_zero _).symm, h6⟩
    h2 |>.mono fun u ⟨a, _, c⟩ => ⟨a, c⟩
  have hr0 := hr (2 * j) (by omega_using [hj])
  have hr1 := hr (2 * j + 1) (by omega_using [hj])
  rw [← ku.rd, ← ku.wr] at hr0 hr1
  have u4 : u.gpr .t4 = BitVec.ofNat 64 M := (ku.get .t4).trans h4
  have u3 : u.gpr .t3 = BitVec.ofNat 64 x := (ku.get .t3).trans h3
  refine WP.mono (alBody_ok (by rw [u1, Offset.add_add]; exact hr0) (by rw [u1, Offset.add_add]; exact hr1))
    fun w ⟨kw, w1, w2, w6⟩ => ⟨⟨(ku.trans kw).mono, by rw [w1, u1, Offset.add_add, show 2 * j + 2 = 2 * (j + 1) by omega_using []], ?_⟩, w2⟩
  rw [w6, u6]
  unfold cand
  rw [u4, u3, u1, Offset.add_add, Offset.add_add, Nat.add_zero (2 * j), ku.mem, hm _ (by omega_using [hj]), hm _ (by omega_using [hj]),
    cand_bv _ _ (by omega_using [hMl]), Proof.RsaPkcs1Enc.foldl_range_succ]
  have hc : (256 * (CL.getD (2 * j) 0).toNat + (CL.getD (2 * j + 1) 0).toNat) &&& M < 2 ^ 32 :=
    Nat.lt_of_le_of_lt Nat.and_le_right hMl
  rw [borrow _ _ (by omega_using [hx]) (by omega_using [hc]), xor_sel]
  have he : (256 * (CL.getD (2 * j) 0).toNat + (CL.getD (2 * j + 1) 0).toNat) &&& M =
      Spec.Rsa.os2ip [CL.getD (2 * j) 0, CL.getD (2 * j + 1) 0] % 2 ^ Spec.RsaPkcs1Enc.bitLength (x + 11 - 11) := by
    rw [Proof.RsaPkcs1Enc.cand_eq, Nat.add_sub_cancel, hM, Proof.RsaPkcs1Enc.bitMask, Nat.and_two_pow_sub_one_eq_mod]
  rw [he]
  simp only [altStep, Nat.add_sub_cancel]
  split <;> rfl

/-! ## The parts -/

section
variable {s : State} (h : DPre pc s) {R : BitVec 64} {EM : List Byte} {kd : List Byte}
include h

/-- `AMR` is kept by code writing only registers it does not keep. -/
theorem AMR.only {t u : State} (hl : AMR s R EM kd t) {rs : List Reg} (o : Only rs t u)
    (hrs : ∀ r ∈ rs, r ∉ kept := by decide) (h7 : Reg.s7 ∉ rs := by decide) : AMR s R EM kd u :=
  ⟨hl.toPost.keep h o.keep (ws := []) (by rw [o.mem]; exact Frame.refl _ _) (fun r hr => nomatch hr) hrs h7,
    by rw [o.mem]; exact hl.cl, by rw [o.mem]; exact hl.am⟩

/-- After the mask: `bitMask (k - 11)` in `t4` and `k - 11` in `t3`. -/
structure MK (s : State) (R : BitVec 64) (EM : List Byte) (kd : List Byte) (t : State) : Prop
    extends AMR s R EM kd t where
  t4 : t.gpr .t4 = BitVec.ofNat 64 (bitMask ((s.gpr .a4).toNat - 11))
  t3 : t.gpr .t3 = BitVec.ofNat 64 ((s.gpr .a4).toNat - 11)

theorem maskPart_ok {t : State} (hl : AMR s R EM kd t) : WP isa maskPart t (MK s R EM kd) := by
  have hk := h.k2
  have hk64 := h.k1
  unfold maskPart maskInit
  refine WP.seq (wp_subi (imm := 11) (fun v₁ p₁ f₁ => wp_li (imm := 0) (by decide) fun t₁ p₂ f₂ =>
    wp_nil ?_) (by decide))
  have O : Only [.t3, .t4] t t₁ := (p₁.trans p₂).mono
  have e3 : t₁.gpr .t3 = BitVec.ofNat 64 ((s.gpr .a4).toNat - 11) := by
    rw [p₂.get .t3, f₁, hl.s1]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_using [hk64]), BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using []), Nat.mod_eq_of_lt (by omega_using [])]
  exact WP.mono (maskLoop_ok (x := (s.gpr .a4).toNat - 11) (by omega_using [hk64]) (by omega_using [hk]) f₂ e3) fun u ⟨ku, u4⟩ =>
    ⟨(hl.only h O).only h ku, u4, (ku.get .t3).trans e3⟩

/-- `CL`. -/
abbrev clOf (kd : List Byte) : List Byte := Spec.RsaPkcs1Enc.irprf kd (Spec.RsaPkcs1Enc.ascii "length") 256

/-- After the alternative length. -/
structure AL (s : State) (R : BitVec 64) (EM : List Byte) (kd : List Byte) (t : State) : Prop
    extends AMR s R EM kd t where
  al : t.gpr .t6 = BitVec.ofNat 64 (Spec.RsaPkcs1Enc.altLength (s.gpr .a4).toNat (clOf kd))
  t3 : t.gpr .t3 = BitVec.ofNat 64 ((s.gpr .a4).toNat - 11)

theorem alPart_ok {t : State} (hm : MK s R EM kd t) : WP isa alPart t (AL s R EM kd) := by
  have hk := h.k2
  have hk64 := h.k1
  unfold alPart alInit
  refine WP.seq (wp_addi (imm := sCL) (fun v₁ p₁ f₁ => wp_li (imm := 128) (by decide) fun v₂ p₂ f₂ =>
    wp_li (imm := 0) (by decide) fun t₁ p₃ f₃ => wp_nil ?_) (by decide))
  have O : Only [.t1, .t2, .t6] t t₁ := (p₁.trans (p₂.trans p₃)).mono
  have P₁ := hm.toAMR.only h O
  have hcl : Spec.Rsa.bytesAt t.mem (scA s sCL) 256 = clOf kd := hm.cl
  have hM := Proof.RsaPkcs1Enc.bitMask_le (x := (s.gpr .a4).toNat - 11) (by omega_using [hk64])
  refine WP.mono (alLoop_ok (x := (s.gpr .a4).toNat - 11) (M := bitMask ((s.gpr .a4).toNat - 11)) (CL := clOf kd)
    (B := scA s sCL) (by omega_using [hk]) rfl (by omega_using [hk, hM])
    (fun i hi => by rw [← hcl, bytes_getD _ _ hi, O.mem])
    (fun i hi => by
      rw [Offset.add_add]
      obtain ⟨r, hr, hc⟩ := scIn h P₁.wr (a := sCL + i) (l := 1) (by unfold sCL scrBytes; omega_using [hi])
      exact ⟨r, List.mem_append_right _ hr, hc⟩)
    (by rw [O.get .t4, hm.t4]) (by rw [O.get .t3, hm.t3])
    (by rw [p₃.get .t1, p₂.get .t1, f₁, hm.s0]) (by rw [p₃.get .t2, f₂]) f₃) fun u ⟨ku, u6⟩ =>
    ⟨P₁.only h ku, by rw [u6, Nat.sub_add_cancel (by omega_using [hk64])]; rfl, by rw [ku.get .t3, O.get .t3, hm.t3]⟩

end

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec

end

end

/-!
# `vg_rsa_pkcs1_decrypt` on RISC-V: the scan of `EM` and the validity of the padding

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Enc/PPC64LE/DecVerified.lean`): the validity of the padding, the
selected length and the mask of the private-key operation's success
(`validBlock_ok`), from the registers the scan left.
-/

@[expose] public section

/-! ## `vg_rsa_pkcs1_decrypt` on RISC-V: the scan of `EM`

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Enc/PPC64LE/DecVerified.lean`): the first zero of `EM` from index
2 (`scanPart_ok`): whether there is one as a mask in `a4`, and where in `a5`,
as `firstZero` says.
-/

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec

open VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt VG.Proof.RsaPkcs1Sig.RISCV64
open VG.Proof.RsaPkcs1Enc (firstZero)

variable {pc : Bool}

/-- A Boolean as a mask. -/
def bm (b : Bool) : BitVec 64 := if b then BitVec.allOnes 64 else 0

theorem zero_mask (b : Byte) :
    (0 : BitVec 64) - ((b.setWidth 64 - BitVec.ofNat 64 1) >>> 63) = bm (decide (b = 0)) := by
  by_cases h : b = 0
  · subst h; decide
  · have hb : b.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq e)
    have hl := b.isLt
    have e : b.setWidth 64 - BitVec.ofNat 64 1 = BitVec.ofNat 64 (b.toNat - 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_using [hb]),
        BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega_using []
    have e2 : BitVec.ofNat 64 (b.toNat - 1) >>> 63 = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      show _ = 0
      omega_using []
    rw [e, e2]
    simp only [bm, h, decide_false, Bool.false_eq_true, ite_false]; rfl

/-- The byte at `t1`. -/
abbrev byt (t : State) : Byte := t.mem (t.gpr .t1 + BitVec.ofNat 64 0)

theorem scanBody_ok {t : State} (h0 : InRegions (t.rd ++ t.wr) (t.gpr .t1 + BitVec.ofNat 64 0) 1)
    (h6 : t.gpr .a6 = 0) (h7 : t.gpr .a7 = BitVec.allOnes 64) :
    WP isa (.block scanBody) t fun u => Only [.a0, .a1, .a5, .a4, .a3, .t1, .t2] t u ∧
      u.gpr .t1 = t.gpr .t1 + BitVec.ofNat 64 1 ∧ u.gpr .t2 = t.gpr .t2 - BitVec.ofNat 64 1 ∧
      u.gpr .a3 = t.gpr .a3 + BitVec.ofNat 64 1 ∧
      u.gpr .a4 = t.gpr .a4 ||| bm (decide (byt t = 0)) ∧
      u.gpr .a5 = t.gpr .a5 ||| ((t.gpr .a4 ^^^ BitVec.allOnes 64) &&& bm (decide (byt t = 0)) &&& t.gpr .a3) := by
  unfold scanBody
  refine wp_lbu rfl h0 fun v₁ p₁ f₁ => wp_subi (imm := 1) (fun v₂ p₂ f₂ => wp_srl (sh := 63) fun v₃ p₃ f₃ =>
    wp_sub fun v₄ p₄ f₄ => wp_xor fun v₅ p₅ f₅ => wp_and fun v₆ p₆ f₆ => wp_and fun v₇ p₇ f₇ =>
    wp_or fun v₈ p₈ f₈ => wp_or fun v₉ p₉ f₉ => wp_addi (imm := 1) (fun v₁₀ p₁₀ f₁₀ =>
    wp_addi (imm := 1) (fun v₁₁ p₁₁ f₁₁ => wp_subi (imm := 1) (fun v₁₂ p₁₂ f₁₂ => wp_nil ?_) (by decide))
      (by decide)) (by decide)) (by decide)
  have O₁ : Only [.a0, .a1, .a5, .a4, .a3, .t1, .t2] t v₄ := (p₁.trans (p₂.trans (p₃.trans p₄))).mono
  have O₂ : Only [.a0, .a1, .a5, .a4, .a3, .t1, .t2] v₄ v₈ := (p₅.trans (p₆.trans (p₇.trans p₈))).mono
  have O₃ : Only [.a0, .a1, .a5, .a4, .a3, .t1, .t2] v₈ v₁₂ := (p₉.trans (p₁₀.trans (p₁₁.trans p₁₂))).mono
  have z : v₄.gpr .a0 = bm (decide (byt t = 0)) := by
    rw [f₄, f₃, f₂, f₁, p₃.get .a6, p₂.get .a6, p₁.get .a6, h6, zero_mask]
  have g4 : v₄.gpr .a4 = t.gpr .a4 := by rw [p₄.get .a4, p₃.get .a4, p₂.get .a4, p₁.get .a4]
  have g3 : v₄.gpr .a3 = t.gpr .a3 := by rw [p₄.get .a3, p₃.get .a3, p₂.get .a3, p₁.get .a3]
  have g5 : v₄.gpr .a5 = t.gpr .a5 := by rw [p₄.get .a5, p₃.get .a5, p₂.get .a5, p₁.get .a5]
  have g7 : v₄.gpr .a7 = t.gpr .a7 := by rw [p₄.get .a7, p₃.get .a7, p₂.get .a7, p₁.get .a7]
  refine ⟨(O₁.trans (O₂.trans O₃)).mono, ?_, ?_, ?_, ?_, ?_⟩
  · rw [p₁₂.get .t1, f₁₁, p₁₀.get .t1, p₉.get .t1, p₈.get .t1, p₇.get .t1, p₆.get .t1, p₅.get .t1,
      p₄.get .t1, p₃.get .t1, p₂.get .t1, p₁.get .t1]
  · rw [f₁₂, p₁₁.get .t2, p₁₀.get .t2, p₉.get .t2, p₈.get .t2, p₇.get .t2, p₆.get .t2, p₅.get .t2,
      p₄.get .t2, p₃.get .t2, p₂.get .t2, p₁.get .t2]
  · rw [p₁₂.get .a3, p₁₁.get .a3, f₁₀, p₉.get .a3, p₈.get .a3, p₇.get .a3, p₆.get .a3, p₅.get .a3, g3]
  · rw [p₁₂.get .a4, p₁₁.get .a4, p₁₀.get .a4, f₉, p₈.get .a4, p₇.get .a4, p₆.get .a4, p₅.get .a4,
      p₈.get .a0, p₇.get .a0, p₆.get .a0, p₅.get .a0, z, g4]
  · rw [p₁₂.get .a5, p₁₁.get .a5, p₁₀.get .a5, p₉.get .a5, f₈, f₇, f₆, f₅, p₇.get .a5, p₆.get .a5, p₅.get .a5,
      g5, p₆.get .a3, p₅.get .a3, g3, p₅.get .a0, z, g4, g7, h7]

theorem firstZero_succ (EM : List Byte) (j : Nat) :
    firstZero EM (2 + (j + 1)) = match firstZero EM (2 + j) with
      | some i => some i
      | none => if EM.getD (2 + j) 1 = 0 then some (2 + j) else none := by
  show firstZero EM ((2 + j) + 1) = _
  rw [firstZero]
  cases firstZero EM (2 + j) with
  | some i => rfl
  | none => simp

theorem a5_pos (n : Nat) :
    BitVec.ofNat 64 0 ||| ((bm false ^^^ BitVec.allOnes 64) &&& bm true &&& BitVec.ofNat 64 n) = BitVec.ofNat 64 n := by
  show 0#64 ||| ((0#64 ^^^ BitVec.allOnes 64) &&& BitVec.allOnes 64 &&& BitVec.ofNat 64 n) = _
  rw [BitVec.zero_xor, BitVec.and_allOnes, BitVec.allOnes_and, BitVec.zero_or]

theorem a5_neg (n : Nat) :
    BitVec.ofNat 64 0 ||| ((bm false ^^^ BitVec.allOnes 64) &&& bm false &&& BitVec.ofNat 64 n) = BitVec.ofNat 64 0 := by
  apply BitVec.eq_of_toNat_eq
  simp [bm]

theorem scanLoop_ok {t₀ : State} {O : Addr} {EM : List Byte} {k : Nat} (hk : 3 ≤ k) (hk2 : k < 2 ^ 32)
    (hEM : ∀ i < k, t₀.mem (O + BitVec.ofNat 64 i) = EM.getD i 1)
    (hr : ∀ i < k, InRegions (t₀.rd ++ t₀.wr) (O + BitVec.ofNat 64 i) 1)
    (h1 : t₀.gpr .t1 = O + BitVec.ofNat 64 2) (h2 : t₀.gpr .t2 = BitVec.ofNat 64 (k - 2))
    (h3 : t₀.gpr .a3 = BitVec.ofNat 64 2) (h4 : t₀.gpr .a4 = 0) (h5 : t₀.gpr .a5 = 0)
    (h6 : t₀.gpr .a6 = 0) (h7 : t₀.gpr .a7 = BitVec.allOnes 64) :
    WP isa scanLoop t₀ fun u => Only [.a0, .a1, .a5, .a4, .a3, .t1, .t2] t₀ u ∧
      u.gpr .a4 = bm (firstZero EM k).isSome ∧ u.gpr .a5 = BitVec.ofNat 64 ((firstZero EM k).getD 0) := by
  refine (VG.Proof.Bignum.RISCV64.wp_countdown (cnt := .t2) (N := k - 2) (by omega_using [hk2]) (by omega_using [hk])
    (fun j u => Only [.a0, .a1, .a5, .a4, .a3, .t1, .t2] t₀ u ∧
      u.gpr .t1 = O + BitVec.ofNat 64 (2 + j) ∧ u.gpr .a3 = BitVec.ofNat 64 (2 + j) ∧
      u.gpr .a4 = bm (firstZero EM (2 + j)).isSome ∧ u.gpr .a5 = BitVec.ofNat 64 ((firstZero EM (2 + j)).getD 0))
    (fun j hj u ⟨ku, u1, u3, u4, u5⟩ _ => ?_)
    ⟨Only.refl _ _, h1, h3, by rw [h4]; rfl, by rw [h5]; rfl⟩ h2).mono
    fun u ⟨ku, _, _, u4, u5⟩ => by
      rw [show 2 + (k - 2) = k by omega_using [hk]] at u4 u5
      exact ⟨ku, u4, u5⟩
  have hr0 := hr (2 + j) (by omega_using [hj])
  rw [← ku.rd, ← ku.wr] at hr0
  have hb : byt u = EM.getD (2 + j) 1 := by
    rw [byt, u1, BitVec.add_zero, ku.mem, hEM _ (by omega_using [hj])]
  refine WP.mono (scanBody_ok (by rw [u1, BitVec.add_zero]; exact hr0) ((ku.get .a6).trans h6)
    ((ku.get .a7).trans h7))
    fun w ⟨kw, w1, w2, w3, w4, w5⟩ => ⟨⟨(ku.trans kw).mono, by rw [w1, u1, Offset.add_add]; rfl,
      by rw [w3, u3, ← BitVec.ofNat_add]; rfl, ?_, ?_⟩, w2⟩
  · rw [w4, u4, hb, firstZero_succ]
    generalize EM.getD (2 + j) 1 = b
    cases firstZero EM (2 + j) with
    | some i => simp only [Option.isSome_some, bm, ite_true, BitVec.allOnes_or]
    | none =>
      by_cases hz : b = 0
      · simp only [Option.isSome_none, bm, hz, decide_true, Bool.false_eq_true, ite_true, ite_false,
          Option.isSome_some]
        rfl
      · simp only [Option.isSome_none, bm, hz, decide_false, Bool.false_eq_true, ite_false]
        rfl
  · rw [w5, u5, u4, u3, hb, firstZero_succ]
    generalize EM.getD (2 + j) 1 = b
    cases firstZero EM (2 + j) with
    | some i =>
      simp only [Option.isSome_some, bm, ite_true, BitVec.xor_self, BitVec.zero_and, BitVec.or_zero,
        Option.getD_some]
    | none =>
      by_cases hz : b = 0
      · simp only [Option.isSome_none, hz, decide_true, ite_true, Option.getD_none, Option.getD_some]
        exact a5_pos _
      · simp only [Option.isSome_none, hz, decide_false, ite_false, Option.getD_none]
        exact a5_neg _

theorem bytes_getD' (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) (d : Byte) :
    (Spec.Rsa.bytesAt m p n).getD i d = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, hi]

section
variable {s : State} (h : DPre pc s) {R : BitVec 64} {EM : List Byte} {kd : List Byte}
include h

/-- After the scan. -/
structure SCN (s : State) (R : BitVec 64) (EM : List Byte) (kd : List Byte) (t : State) : Prop
    extends AMR s R EM kd t where
  al : t.gpr .t6 = BitVec.ofNat 64 (Spec.RsaPkcs1Enc.altLength (s.gpr .a4).toNat (clOf kd))
  a4 : t.gpr .a4 = bm (firstZero EM (s.gpr .a4).toNat).isSome
  a5 : t.gpr .a5 = BitVec.ofNat 64 ((firstZero EM (s.gpr .a4).toNat).getD 0)
  a6 : t.gpr .a6 = 0
  a7 : t.gpr .a7 = BitVec.allOnes 64

/-- A byte of `out` is accessible. -/
theorem outIn {t : State} (hp : Post s R EM t) {i : Nat} (hi : i < (s.gpr .a4).toNat) :
    InRegions (t.rd ++ t.wr) (s.gpr .a0 + BitVec.ofNat 64 i) 1 := by
  have := h.wo; rw [h.h1] at this
  exact ⟨oR s, by rw [hp.wr, h.hwr]; simp, by
    rw [show oR s = ⟨s.gpr .a0, (s.gpr .a4).toNat⟩ by simp only [oR, h.h1]]
    exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩

theorem scanPart_ok {t : State} (hl : AL s R EM kd t) : WP isa scanPart t (SCN s R EM kd) := by
  have hk := h.k2
  have hk64 := h.k1
  unfold scanPart scanInit
  refine WP.seq (wp_addi (imm := 2) (fun v₁ p₁ f₁ => wp_subi (imm := 2) (fun v₂ p₂ f₂ =>
    wp_li (imm := 2) (by decide) fun v₃ p₃ f₃ => wp_li (imm := 0) (by decide) fun v₄ p₄ f₄ =>
    wp_li (imm := 0) (by decide) fun v₅ p₅ f₅ => wp_li (imm := 0) (by decide) fun v₆ p₆ f₆ =>
    wp_li (imm := 0) (by decide) fun v₇ p₇ f₇ => wp_subi (imm := 1) (fun t₁ p₈ f₈ => wp_nil ?_) (by decide))
    (by decide)) (by decide))
  have O : Only [.t1, .t2, .a3, .a4, .a5, .a6, .a7] t t₁ :=
    (p₁.trans (p₂.trans (p₃.trans (p₄.trans (p₅.trans (p₆.trans (p₇.trans p₈))))))).mono
  have P₁ := hl.toAMR.only h O
  have e2 : s.gpr .a4 - BitVec.ofNat 64 2 = BitVec.ofNat 64 ((s.gpr .a4).toNat - 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_using [hk64]), BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using []), Nat.mod_eq_of_lt (by omega_using [])]
  refine WP.mono (scanLoop_ok (O := s.gpr .a0) (EM := EM) (k := (s.gpr .a4).toNat) (by omega_using [hk64]) (by omega_using [hk])
    (fun i hi => by rw [← P₁.em, bytes_getD' _ _ hi]) (fun i hi => outIn h P₁.toPost hi)
    (by rw [p₈.get .t1, p₇.get .t1, p₆.get .t1, p₅.get .t1, p₄.get .t1, p₃.get .t1, p₂.get .t1, f₁, hl.s2])
    (by rw [p₈.get .t2, p₇.get .t2, p₆.get .t2, p₅.get .t2, p₄.get .t2, p₃.get .t2, f₂, p₁.get .s1, hl.s1, e2])
    (by rw [p₈.get .a3, p₇.get .a3, p₆.get .a3, p₅.get .a3, p₄.get .a3, f₃])
    (by rw [p₈.get .a4, p₇.get .a4, p₆.get .a4, p₅.get .a4, f₄]; rfl)
    (by rw [p₈.get .a5, p₇.get .a5, p₆.get .a5, f₅]; rfl)
    (by rw [p₈.get .a6, p₇.get .a6, f₆]; rfl)
    (by rw [f₈, f₇]; decide))
    fun u ⟨ku, u4, u5⟩ => ⟨P₁.only h ku, by rw [ku.get .t6, O.get .t6, hl.al], u4, u5,
      by rw [ku.get .a6, p₈.get .a6, p₇.get .a6, f₆]; rfl, by rw [ku.get .a7, f₈, f₇]; decide⟩

end

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec

open VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt VG.Proof.RsaPkcs1Sig.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (mov)
open VG.Proof.RsaPkcs1Enc (firstZero vOf lselOf outByte)

variable {pc : Bool}

/-- `-(x = 0)`, for `x < 2 ^ 63`. -/
theorem zero_mask64 (x : BitVec 64) (hx : x.toNat < 2 ^ 63) :
    (0 : BitVec 64) - ((x - BitVec.ofNat 64 1) >>> 63) = bm (decide (x = 0)) := by
  by_cases h : x = 0
  · subst h; decide
  · have hb : x.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq e)
    have e2 : (x - BitVec.ofNat 64 1) >>> 63 = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_using [hb]),
        BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      show _ = 0
      omega_using [hx]
    rw [e2]
    simp only [bm, h, decide_false, Bool.false_eq_true, ite_false]; rfl

theorem ten_mask {sep : Nat} (h : sep < 2 ^ 63) :
    (0 : BitVec 64) - ((BitVec.ofNat 64 sep - BitVec.ofNat 64 10) >>> 63) = bm (decide (sep < 10)) := by
  rw [borrow _ _ h (by decide)]
  by_cases hs : sep < 10
  · simp only [show ¬ 10 ≤ sep by omega_using [hs], ↓reduceIte, bm, hs, decide_true]; decide
  · simp only [show 10 ≤ sep by omega_using [hs], ↓reduceIte, bm, hs, decide_false, Bool.false_eq_true]; decide

theorem bm_and (a b : Bool) : bm a &&& bm b = bm (a && b) := by
  cases a <;> cases b <;> rfl

theorem bm_not (a : Bool) : bm a ^^^ BitVec.allOnes 64 = bm (!a) := by
  cases a <;> decide

theorem sel_xor (x y : BitVec 64) (v : Bool) : x ^^^ ((y ^^^ x) &&& bm v) = if v then y else x := by
  cases v
  · simp [bm]
  · simp only [bm, ite_true, BitVec.and_allOnes]
    rw [← BitVec.xor_assoc, BitVec.xor_comm x y, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem byte_zero (b : Byte) : decide (b.setWidth 64 = (0 : BitVec 64)) = decide (b = 0) := by
  by_cases h : b = 0
  · subst h; decide
  · have hb : b.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq e)
    have : b.setWidth 64 ≠ 0 := fun e => hb (by
      have := congrArg BitVec.toNat e
      rwa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide))] at this)
    simp only [this, h, decide_false]

theorem byte_two (b : Byte) :
    decide (b.setWidth 64 ^^^ BitVec.ofNat 64 2 = (0 : BitVec 64)) = decide (b = 2) := by
  rw [decide_eq_decide, show (0 : BitVec 64) = 0#64 from rfl, BitVec.xor_eq_zero_iff]
  constructor
  · intro e
    have := congrArg (BitVec.setWidth 8) e
    rwa [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq] at this
  · intro e; subst e; decide

theorem byte_lt (b : Byte) : (b.setWidth 64).toNat < 2 ^ 63 := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide))]
  exact Nat.lt_trans b.isLt (by decide)

theorem byte2_lt (b : Byte) : (b.setWidth 64 ^^^ BitVec.ofNat 64 2).toNat < 2 ^ 63 := by
  rw [BitVec.toNat_xor, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide)),
    BitVec.toNat_ofNat]
  exact Nat.lt_of_lt_of_le (Nat.xor_lt_two_pow (n := 8) b.isLt (by decide)) (by decide)

theorem vOf_bm (a b : Byte) (f : Bool) (sep : Nat) :
    bm f &&& (bm (decide (a = 0)) &&& bm (decide (b = 2))) &&& bm (!decide (sep < 10)) = bm (vOf a b f sep) := by
  have e : (!decide (sep < 10)) = decide (10 ≤ sep) := by
    by_cases hs : sep < 10
    · simp only [hs, decide_true, Bool.not_true, show ¬ 10 ≤ sep by omega_using [hs], decide_false]
    · simp only [hs, decide_false, Bool.not_false, show 10 ≤ sep by omega_using [hs], decide_true]
  rw [bm_and, bm_and, bm_and, e]
  congr 1
  unfold vOf
  cases f <;> by_cases ha : a = 0 <;> by_cases hb : b = 2 <;> by_cases hs : 10 ≤ sep <;> simp [ha, hb, hs]

/-- The block's results, from the registers the scan left. -/
theorem validBlock_ok {s : State} {R : BitVec 64} {EM : List Byte} {t : State} (hp : Post s R EM t)
    (h0 : InRegions (t.rd ++ t.wr) (s.gpr .a0) 1)
    (h1 : InRegions (t.rd ++ t.wr) (s.gpr .a0 + BitVec.ofNat 64 1) 1)
    {f : Bool} {sep al : Nat} (h4 : t.gpr .a4 = bm f) (h5 : t.gpr .a5 = BitVec.ofNat 64 sep)
    (h6 : t.gpr .t6 = BitVec.ofNat 64 al) (ha6 : t.gpr .a6 = 0) (ha7 : t.gpr .a7 = BitVec.allOnes 64)
    (hsep : sep < 2 ^ 63) (hR : (R ^^^ BitVec.ofNat 64 1).toNat < 2 ^ 63) :
    WP isa (.block validBlock) t fun u => Only [.t1, .t2, .a0, .a1, .a3, .a4, .a5, .t6] t u ∧
      u.gpr .t1 = s.gpr .a0 ∧ u.gpr .t2 = s.gpr .a4 ∧
      u.gpr .a4 = bm (vOf (t.mem (s.gpr .a0)) (t.mem (s.gpr .a0 + BitVec.ofNat 64 1)) f sep) ∧
      u.gpr .a3 = bm (decide (R ^^^ BitVec.ofNat 64 1 = 0)) ∧
      u.gpr .t6 = (if vOf (t.mem (s.gpr .a0)) (t.mem (s.gpr .a0 + BitVec.ofNat 64 1)) f sep then
          s.gpr .a4 - BitVec.ofNat 64 sep - BitVec.ofNat 64 1 else BitVec.ofNat 64 al) &&&
        bm (decide (R ^^^ BitVec.ofNat 64 1 = 0)) ∧
      u.gpr .a5 = s.gpr .a4 - (if vOf (t.mem (s.gpr .a0)) (t.mem (s.gpr .a0 + BitVec.ofNat 64 1))
          f sep then s.gpr .a4 - BitVec.ofNat 64 sep - BitVec.ofNat 64 1 else BitVec.ofNat 64 al) := by
  unfold validBlock
  mrun [mov, hp.s2, hp.s1, hp.r, h0, h1, h4, h5, h6, ha6, ha7]
  refine ⟨⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, ?_⟩
  · obtain ⟨a, b, c, d, e, f, g, i⟩ : r ≠ .t1 ∧ r ≠ .t2 ∧ r ≠ .a0 ∧ r ≠ .a1 ∧ r ≠ .a3 ∧ r ≠ .a4 ∧ r ≠ .a5 ∧
        r ≠ .t6 := by simpa using hr
    simp only [a, b, c, d, e, f, g, i, ite_false]
  simp only [zero_mask64 _ (byte_lt _), zero_mask64 _ (byte2_lt _), zero_mask64 _ hR, ten_mask hsep, bm_not,
    byte_two, byte_zero, vOf_bm, sel_xor]
  exact ⟨trivial, trivial, trivial, trivial⟩

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec

end

end

/-!
# `vg_rsa_pkcs1_decrypt` on RISC-V: writing the output

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Enc/PPC64LE/DecOut.lean`): the output, byte by byte
(`selBody_ok`, `selLoop_ok`): byte `i` of `out` is
`outByte v ok kl i EM[i] AM[i]`, with `Fr3` (`Mid` with `out`, `*msg_len` and
`scratch` written, and the result in `s7`) kept.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec

open VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt VG.Proof.RsaPkcs1Sig.RISCV64
open VG.Proof.RsaPkcs1Enc (firstZero outByte)

variable {pc : Bool}

theorem write1_ne' (m : Mem) {b x : Addr} (v : BitVec (8 * 1)) (h : x ≠ b) : m.write b 1 v x = m x :=
  Mem.write_apply fun h' => h (by bv_omega)

/-- After the scan: `Mid` with `out`, `*msg_len` and `scratch` written, and the
result `R` in `s7`. -/
structure Fr3 (s : State) (R : BitVec 64) (u : State) : Prop extends Mid [oR s, mlR s, sR s] s u where
  r : u.gpr .s7 = R

theorem Post.fr3 {s : State} {R : BitVec 64} {EM : List Byte} {t : State} (hp : Post s R EM t) : Fr3 s R t :=
  ⟨hp.toMid.of (fun _ _ => rfl) rfl rfl rfl (hp.mem.sub fun r hr => ⟨r, by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl <;> simp, fun _ h => h⟩) hp.sv, hp.r⟩

section
variable {s : State} (h : DPre pc s) {R : BitVec 64}
include h

/-- Writes of `out` or `*msg_len`, and of registers `Fr3` does not keep. -/
theorem Fr3.store {t u : State} (hc : Fr3 s R t) {rs : List Reg} (o : Kept rs t u) {X : Region}
    (hX : X = oR s ∨ X = mlR s) {Y : Region} (hY : Region.Sub Y X) (hf : Frame [Y] t.mem u.mem)
    (hrs : ∀ r ∈ rs, r ∉ kept := by decide) (h7 : Reg.s7 ∉ rs := by decide) : Fr3 s R u := by
  have hk : Region.Disjoint (kR s) Y := by
    rcases hX with rfl | rfl
    · exact h.ko.sub_right hY
    · exact h.km.sub_right hY
  refine ⟨hc.toMid.keep o (hc.mem.trans (hf.sub fun r hr => ?_)) (hc.sv.frame hf fun p hp r hr => ?_) hrs,
    (o.gpr _ h7).trans hc.r⟩
  · rw [List.mem_singleton.mp hr]
    rcases hX with rfl | rfl
    · exact ⟨_, by simp, hY⟩
    · exact ⟨_, by simp, hY⟩
  · rw [List.mem_singleton.mp hr]
    have := saved_offs p hp
    exact hk.sub_left (frame_sub s (by unfold oEnd frameBytes at *; omega_using [this]))

omit h in
theorem Fr3.only {t u : State} (hc : Fr3 s R t) {rs : List Reg} (o : Only rs t u)
    (hrs : ∀ r ∈ rs, r ∉ kept := by decide) (h7 : Reg.s7 ∉ rs := by decide) : Fr3 s R u :=
  ⟨hc.toMid.only o hrs, (o.get _ h7).trans hc.r⟩

end

/-! ## A byte of the output -/

theorem outB_eq (v ok : Bool) {kl i : Nat} (hkl : kl < 2 ^ 63) (hi : i < 2 ^ 63) (e a : Byte) :
    ((((e.setWidth 64 ^^^ a.setWidth 64) &&& bm v) ^^^ a.setWidth 64) &&&
      ((((0 : BitVec 64) - ((BitVec.ofNat 64 i - BitVec.ofNat 64 kl) >>> 63)) ^^^ BitVec.allOnes 64) &&& bm ok)).setWidth 8 =
      outByte v ok kl i e a := by
  have sel : ((e.setWidth 64 ^^^ a.setWidth 64) &&& bm v) ^^^ a.setWidth 64 = (if v then e else a).setWidth 64 := by
    cases v
    · simp [bm]
    · simp only [bm, ite_true, BitVec.and_allOnes]
      rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  rw [sel, borrow _ _ hi hkl]
  simp only [outByte]
  by_cases hk : kl ≤ i
  · cases ok
    · simp only [hk, ↓reduceIte, bm, Bool.false_eq_true, and_false]
      apply BitVec.eq_of_toNat_eq; simp
    · simp only [hk, ↓reduceIte, bm, and_self]
      rw [show ((0 : BitVec 64) - BitVec.ofNat 64 0) ^^^ BitVec.allOnes 64 = BitVec.allOnes 64 by decide,
        BitVec.and_allOnes, BitVec.and_allOnes, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]
  · simp only [hk, ↓reduceIte, false_and]
    rw [show ((0 : BitVec 64) - BitVec.ofNat 64 1) ^^^ BitVec.allOnes 64 = 0 by decide]
    apply BitVec.eq_of_toNat_eq; simp

/-- The byte `selBody` writes. -/
abbrev selByte (t : State) : Byte :=
  ((((t.mem (t.gpr .t1)).setWidth 64 ^^^ (t.mem (t.gpr .a0)).setWidth 64) &&& t.gpr .a4) ^^^
      (t.mem (t.gpr .a0)).setWidth 64) &&&
    ((((0 : BitVec 64) - ((t.gpr .a1 - t.gpr .a5) >>> 63)) ^^^ t.gpr .a7) &&& t.gpr .a3) |>.setWidth 8

theorem selBody_ok {t : State} (he : InRegions (t.rd ++ t.wr) (t.gpr .t1) 1)
    (ha : InRegions (t.rd ++ t.wr) (t.gpr .a0) 1) (hw : InRegions t.wr (t.gpr .t1) 1) (h6 : t.gpr .a6 = 0) :
    WP isa (.block selBody) t fun u => (u.mem = t.mem.write (t.gpr .t1) 1 (selByte t) ∧
      u.gpr .a1 = t.gpr .a1 + BitVec.ofNat 64 1 ∧ u.gpr .t1 = t.gpr .t1 + BitVec.ofNat 64 1 ∧
      u.gpr .a0 = t.gpr .a0 + BitVec.ofNat 64 1 ∧ u.gpr .t2 = t.gpr .t2 - BitVec.ofNat 64 1) ∧
      Kept [.t6, .a2, .a1, .t1, .a0, .t2] t u := by
  unfold selBody
  mrun [he, ha, hw, h6]
  refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
  obtain ⟨a, b, c, d, e, f⟩ : r ≠ .t6 ∧ r ≠ .a2 ∧ r ≠ .a1 ∧ r ≠ .t1 ∧ r ≠ .a0 ∧ r ≠ .t2 := by simpa using hr
  simp only [a, b, c, d, e, f, ite_false]

/-! ## The loop -/

/-- After `i` bytes of the output. -/
structure OInv (s : State) (R MLV : BitVec 64) (EM AM : List Byte) (v ok : Bool) (kl : Nat) (i : Nat) (t : State) :
    Prop extends Fr3 s R t where
  ml : t.mem.readW (s.gpr .a2) 64 = MLV
  a1 : t.gpr .a1 = BitVec.ofNat 64 i
  t1 : t.gpr .t1 = s.gpr .a0 + BitVec.ofNat 64 i
  a0 : t.gpr .a0 = scA s sAM + BitVec.ofNat 64 i
  a3 : t.gpr .a3 = bm ok
  a4 : t.gpr .a4 = bm v
  a5 : t.gpr .a5 = BitVec.ofNat 64 kl
  a6 : t.gpr .a6 = 0
  a7 : t.gpr .a7 = BitVec.allOnes 64
  done : ∀ j < i, t.mem (s.gpr .a0 + BitVec.ofNat 64 j) = outByte v ok kl j (EM.getD j 1) (AM.getD j 0)
  todo : ∀ j, i ≤ j → j < (s.gpr .a4).toNat → t.mem (s.gpr .a0 + BitVec.ofNat 64 j) = EM.getD j 1
  am : ∀ j < (s.gpr .a4).toNat, t.mem (scA s sAM + BitVec.ofNat 64 j) = AM.getD j 0

section
variable {s : State} (h : DPre pc s)
include h

theorem outW {t : State} (hwr : t.wr = frR s :: s.wr) {i : Nat} (hi : i < (s.gpr .a4).toNat) :
    InRegions t.wr (s.gpr .a0 + BitVec.ofNat 64 i) 1 := by
  have := h.wo; rw [h.h1] at this
  exact ⟨oR s, by rw [hwr, h.hwr]; simp, by
    rw [show oR s = ⟨s.gpr .a0, (s.gpr .a4).toNat⟩ by simp only [oR, h.h1]]
    exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩

theorem selLoop_ok {R MLV : BitVec 64} {EM AM : List Byte} {v ok : Bool} {kl : Nat}
    (hkl : kl < 2 ^ 63) {t : State} (h0 : OInv s R MLV EM AM v ok kl 0 t) (h2 : t.gpr .t2 = s.gpr .a4) :
    WP isa selLoop t (OInv s R MLV EM AM v ok kl (s.gpr .a4).toNat) := by
  have hk := h.k2
  have hk64 := h.k1
  have hwo := h.wo
  rw [h.h1] at hwo
  have := h.ws; have := scr_le h
  refine VG.Proof.Bignum.RISCV64.wp_countdown (cnt := .t2) (by omega_using []) (by omega_using [hk64]) (OInv s R MLV EM AM v ok kl)
    (fun i hi u hu _ => ?_) h0 (by rw [h2, BitVec.ofNat_toNat, BitVec.setWidth_eq])
  have he : InRegions (u.rd ++ u.wr) (u.gpr .t1) 1 := by
    rw [hu.t1]
    obtain ⟨r, hr, hcr⟩ := outW h hu.wr hi
    exact ⟨r, List.mem_append_right _ hr, hcr⟩
  have ha : InRegions (u.rd ++ u.wr) (u.gpr .a0) 1 := by
    rw [hu.a0, Offset.add_add]
    obtain ⟨r, hr, hcr⟩ := scIn h hu.wr (a := sAM + i) (l := 1) (by unfold sAM scrBytes; omega_using [hk, hi])
    exact ⟨r, List.mem_append_right _ hr, hcr⟩
  have hw : InRegions u.wr (u.gpr .t1) 1 := by rw [hu.t1]; exact outW h hu.wr hi
  refine WP.mono (selBody_ok he ha hw hu.a6) fun x ⟨⟨xm, x1, xt1, x0, x2⟩, kx⟩ => ⟨?_, ?_⟩
  · have hb : selByte u = outByte v ok kl i (EM.getD i 1) (AM.getD i 0) := by
      unfold selByte
      rw [hu.a4, hu.a3, hu.a1, hu.a5, hu.a7, hu.t1, hu.a0, hu.todo i (Nat.le_refl _) hi, hu.am i hi,
        outB_eq _ _ hkl (by omega_using [hk, hi])]
    rw [hb, hu.t1] at xm
    have hf : Frame [⟨s.gpr .a0 + BitVec.ofNat 64 i, 1⟩] u.mem x.mem := by
      rw [xm]; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have hsub : Region.Sub ⟨s.gpr .a0 + BitVec.ofNat 64 i, 1⟩ (oR s) := by
      rw [show oR s = ⟨s.gpr .a0, (s.gpr .a4).toNat⟩ by simp only [oR, h.h1]]; exact Offset.sub_base _ (by omega_using [hi])
    have hne : ∀ j, j ≠ i → j < (s.gpr .a4).toNat → s.gpr .a0 + BitVec.ofNat 64 j ≠ s.gpr .a0 + BitVec.ofNat 64 i :=
      fun j hj hjk => Offset.add_ofNat_ne _ (by omega_using [hjk]) (by omega_using [hi]) hj
    refine ⟨hu.toFr3.store h kx (.inl rfl) hsub hf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hf.readW (Region.contains_self _ _) (fun X hX => by
        rw [List.mem_singleton.mp hX]; exact (h.om.sub_left hsub).symm) (by decide), hu.ml]
    · rw [x1, hu.a1, ← BitVec.ofNat_add]
    · rw [xt1, hu.t1, Offset.add_add]
    · rw [x0, hu.a0, Offset.add_add]
    · rw [kx.gpr _ (by decide), hu.a3]
    · rw [kx.gpr _ (by decide), hu.a4]
    · rw [kx.gpr _ (by decide), hu.a5]
    · rw [kx.gpr _ (by decide), hu.a6]
    · rw [kx.gpr _ (by decide), hu.a7]
    · intro j hj
      rw [xm]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [write1_ne' _ _ (hne j (by omega_using [hj]) (by omega_arith)), hu.done j hj]
      · exact VG.Proof.Bignum.RISCV64.write1_self _ _ _
    · intro j hj hjk
      rw [xm, write1_ne' _ _ (hne j (by omega_using [hj]) hjk), hu.todo j (by omega_using [hj]) hjk]
    · intro j hj
      rw [hf.bytes (R := ⟨scA s sAM, (s.gpr .a4).toNat⟩) (fun X hX => by
        rw [List.mem_singleton.mp hX]
        exact (h.os.sub_left hsub).symm.sub_left (scSub h (by unfold sAM scrBytes; omega_using [hk])))
        (by show (s.gpr .a4).toNat ≤ 2 ^ 64; omega_using []) hj, hu.am j hj]
  · rw [x2]

end

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec

end

end

/-!
# `vg_rsa_pkcs1_decrypt` on RISC-V: correctness

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Enc/PPC64LE/DecCorrect.lean`): the frame's allocation, the
setup, the private-key operation, `D`, `DH`, `KDK`, `CL`, `AM`, the
alternative length, the scan, the output and the restores
(`code_correct`), to the outcome on the registers and the stack (`fnPost`,
`result_ok`).
-/

@[expose] public section

/-! ## `vg_rsa_pkcs1_decrypt` on RISC-V: the selection

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Enc/PPC64LE/DecVerified.lean`): the validity and `*msg_len`
(`outInit_ok`), the output's loop, and the result and our caller's registers
(`finish_ok`): `selPart_ok`, from `SCN` to `Fin`.
-/

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec

open VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt VG.Proof.RsaPkcs1Sig.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (mov)
open VG.Proof.RsaPkcs1Enc (firstZero outByte)

variable {pc : Bool}

/-- `AM`. -/
abbrev amOf (s : State) (kd : List Byte) : List Byte :=
  Spec.RsaPkcs1Enc.irprf kd (Spec.RsaPkcs1Enc.ascii "message") (s.gpr .a4).toNat

/-- The validity of `EM`, as the scan found it. -/
abbrev vOfEM (s : State) (EM : List Byte) : Bool := Proof.RsaPkcs1Enc.vEM EM (s.gpr .a4).toNat

/-- The selected length. -/
abbrev lenOf (s : State) (EM : List Byte) (kd : List Byte) : Nat :=
  Proof.RsaPkcs1Enc.lselOf (vOfEM s EM) ((firstZero EM (s.gpr .a4).toNat).getD 0)
    (Spec.RsaPkcs1Enc.altLength (s.gpr .a4).toNat (clOf kd)) (s.gpr .a4).toNat

theorem sep_lt (EM : List Byte) {k : Nat} (hk : 0 < k) : (firstZero EM k).getD 0 < k := by
  cases h : firstZero EM k with
  | none => simp; omega_using [hk]
  | some i => exact (Proof.RsaPkcs1Enc.firstZero_some h).2.1

/-- At the end of the body: the output and `*msg_len` written, the result in
`a0` and our caller's registers back. -/
structure Fin (s : State) (R : BitVec 64) (EM AM : List Byte) (v ok : Bool) (len : Nat) (u : State) : Prop where
  abi : abiPreserved s (freed frameBytes u)
  a0 : u.gpr .a0 = R
  out : ∀ i < (s.gpr .a4).toNat, u.mem (s.gpr .a0 + BitVec.ofNat 64 i) =
    outByte v ok ((s.gpr .a4).toNat - len) i (EM.getD i 1) (AM.getD i 0)
  ml : u.mem.readW (s.gpr .a2) 64 = BitVec.ofNat 64 len &&& bm ok

section
variable {s : State} (h : DPre pc s) {R : BitVec 64}
include h

/-- `*msg_len := len & ok`; then `AM` in `a0` and the index zero. -/
theorem outInit_ok {t : State} (hc : Fr3 s R t) :
    WP isa (.block outInit) t fun u => Fr3 s R u ∧ u.mem = t.mem.writeW (s.gpr .a2) (t.gpr .t6) ∧
      u.gpr .a0 = scA s sAM ∧ u.gpr .a1 = BitVec.ofNat 64 0 ∧ Kept [.a0, .a1] t u := by
  have hw : InRegions t.wr (s.gpr .a2) 8 := by rw [hc.wr, h.hwr]; exact ⟨mlR s, by simp, Region.contains_self _ _⟩
  unfold outInit
  refine wp_sd (by rw [hc.s3, BitVec.add_zero]) h.mal hw fun w₁ m₁ => wp_addi (imm := sAM) (fun w₂ p₂ f₂ =>
    wp_li (imm := 0) (by decide) fun u p₃ f₃ => wp_nil ?_) (by decide)
  have F : Frame [mlR s] t.mem w₁.mem := by
    rw [m₁.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have O₂ : Only [.a0, .a1] w₁ u := (p₂.trans p₃).mono
  have K : Kept [.a0, .a1] t u := (m₁.keep.trans O₂.keep).mono
  have hc₁ : Fr3 s R w₁ := hc.store h m₁.keep (.inr rfl) (fun _ h => h) F
  refine ⟨hc₁.only O₂, by rw [p₃.mem, p₂.mem, m₁.mem], ?_, f₃, K⟩
  rw [p₃.get .a0, f₂, m₁.gpr, hc.s0]

/-- The result, and our caller's registers. -/
theorem finish_ok {t : State} (hc : Fr3 s R t) :
    WP isa (.block finish) t fun u => abiPreserved s (freed frameBytes u) ∧ u.gpr .a0 = R ∧ u.mem = t.mem := by
  unfold finish
  refine wp_mov fun w o e => ?_
  have hw : Fr3 s R w := hc.only o
  exact WP.mono (restore_ok h hw.saves) fun u ⟨ua, u0, um⟩ => ⟨ua, by rw [u0, e, hc.r], by rw [um, o.mem]⟩

/-- The selection: the validity, `*msg_len`, the output and the end. -/
theorem selPart_ok {EM kd : List Byte} {t : State} (hs : SCN s R EM kd t)
    (hR : (R ^^^ BitVec.ofNat 64 1).toNat < 2 ^ 63) :
    WP isa selPart t (Fin s R EM (amOf s kd) (vOfEM s EM) (decide (R ^^^ BitVec.ofNat 64 1 = 0)) (lenOf s EM kd)) := by
  have hk := h.k2
  have hk64 := h.k1
  have hsep := sep_lt EM (k := (s.gpr .a4).toNat) (by omega_using [hk64])
  have hal := Proof.RsaPkcs1Enc.altLength_le (s.gpr .a4).toNat (clOf kd)
  have o0 := outIn h hs.toPost (i := 0) (by omega_using [hk64])
  rw [BitVec.add_zero] at o0
  unfold selPart
  refine WP.seq (WP.mono (validBlock_ok hs.toPost o0 (outIn h hs.toPost (by omega_using [hk64])) hs.a4 hs.a5 hs.al hs.a6 hs.a7
    (by omega_using [hk, hsep]) hR) fun t₁ ⟨O₁, x1, x2, x4, x3, x6, x5⟩ => ?_)
  -- The values the block computed.
  have e0 : t.mem (s.gpr .a0) = EM.getD 0 1 := by
    rw [← hs.em, bytes_getD' _ _ (by omega_using [hk64]), BitVec.add_zero]
  have e1 : t.mem (s.gpr .a0 + BitVec.ofNat 64 1) = EM.getD 1 1 := by rw [← hs.em, bytes_getD' _ _ (by omega_using [hk64])]
  have eL : (if Proof.RsaPkcs1Enc.vOf (EM.getD 0 1) (EM.getD 1 1) (firstZero EM (s.gpr .a4).toNat).isSome
      ((firstZero EM (s.gpr .a4).toNat).getD 0) then s.gpr .a4 - BitVec.ofNat 64 ((firstZero EM (s.gpr .a4).toNat).getD 0) -
        BitVec.ofNat 64 1 else BitVec.ofNat 64 (Spec.RsaPkcs1Enc.altLength (s.gpr .a4).toNat (clOf kd))) =
      BitVec.ofNat 64 (lenOf s EM kd) := by
    simp only [lenOf, vOfEM, Proof.RsaPkcs1Enc.vEM, Proof.RsaPkcs1Enc.lselOf]
    split
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_sub_of_le
          (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_using [hsep]), BitVec.toNat_ofNat]; omega_using [hsep]),
        BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_using [hsep]), BitVec.toNat_ofNat,
        BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega_using [hsep]
    · rfl
  have hlen : lenOf s EM kd ≤ (s.gpr .a4).toNat := by
    simp only [lenOf, Proof.RsaPkcs1Enc.lselOf]; split <;> omega_arith
  simp only [e0, e1] at x4 x6 x5
  rw [eL] at x6 x5
  rw [show s.gpr .a4 - BitVec.ofNat 64 (lenOf s EM kd) = BitVec.ofNat 64 ((s.gpr .a4).toNat - lenOf s EM kd) by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_using [hlen]), BitVec.toNat_ofNat,
      BitVec.toNat_ofNat]
    omega_using [hlen]] at x5
  have hc₁ : Fr3 s R t₁ := hs.toPost.fr3.only O₁
  -- `*msg_len`.
  refine WP.seq (WP.mono (outInit_ok h hc₁) fun t₂ ⟨hc₂, m₂, x0, xa1, K₂⟩ => ?_)
  rw [x6] at m₂
  have F₂ : Frame [mlR s] t₁.mem t₂.mem := by
    rw [m₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have bk : ∀ (X : Region), X.Disjoint (mlR s) → X.len ≤ 2 ^ 64 → ∀ i < X.len,
      t₂.mem (X.base + BitVec.ofNat 64 i) = t.mem (X.base + BitVec.ofNat 64 i) := fun X hX hl i hi => by
    rw [F₂.bytes (fun Y hY' => by rw [List.mem_singleton.mp hY']; exact hX) hl hi, O₁.mem]
  have hwo := h.wo; have h4 := h.h1
  have h0 : OInv s R (BitVec.ofNat 64 (lenOf s EM kd) &&& bm (decide (R ^^^ BitVec.ofNat 64 1 = 0))) EM (amOf s kd)
      (vOfEM s EM) (decide (R ^^^ BitVec.ofNat 64 1 = 0)) ((s.gpr .a4).toNat - lenOf s EM kd) 0 t₂ :=
    { toFr3 := hc₂
      ml := by rw [m₂, Mem.readW_writeW_self64]
      a1 := xa1
      t1 := by rw [K₂.gpr _ (by decide), x1, BitVec.add_zero]
      a0 := by rw [x0, BitVec.add_zero]
      a3 := by rw [K₂.gpr _ (by decide), x3]
      a4 := by rw [K₂.gpr _ (by decide), x4]
      a5 := by rw [K₂.gpr _ (by decide), x5]
      a6 := by rw [K₂.gpr _ (by decide), O₁.get .a6, hs.a6]
      a7 := by rw [K₂.gpr _ (by decide), O₁.get .a7, hs.a7]
      done := fun j hj => absurd hj (Nat.not_lt_zero _)
      todo := fun j _ hj => by
        rw [show s.gpr .a0 = (oR s).base from rfl, bk (oR s) h.om (by show (s.gpr .a1).toNat ≤ 2 ^ 64; omega_using []) j
          (by show j < (s.gpr .a1).toNat; omega_using [h4, hj]), show (oR s).base = s.gpr .a0 from rfl, ← hs.em, bytes_getD' _ _ hj]
      am := fun j hj => by
        rw [show scA s sAM = (⟨scA s sAM, (s.gpr .a4).toNat⟩ : Region).base from rfl,
          bk ⟨scA s sAM, (s.gpr .a4).toNat⟩ ((h.ms.symm.sub_left (scSub h (by unfold sAM scrBytes; omega_using [hk]))))
            (by show (s.gpr .a4).toNat ≤ 2 ^ 64; omega_using []) j hj]
        have ham : Spec.Rsa.bytesAt t.mem (scA s sAM) (s.gpr .a4).toNat = amOf s kd := hs.am
        rw [← ham, bytes_getD' _ _ hj] }
  refine WP.seq (WP.mono (selLoop_ok h (by omega_using [hk]) h0 (by rw [K₂.gpr _ (by decide), x2])) fun t₃ h₃ => ?_)
  refine WP.mono (finish_ok h h₃.toFr3) fun u ⟨ua, u0, um⟩ => ⟨ua, u0, fun i hi => ?_, ?_⟩
  · rw [um]; exact h₃.done i hi
  · rw [um]; exact h₃.ml

end

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec

open VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt VG.Proof.RsaPkcs1Sig.RISCV64
open VG.Proof.RsaPkcs1Enc (outByte)

variable {pc : Bool}

/-- The outcome, on the registers and the stack. -/
def fnPost (s s' : State) : Prop :=
  Spec.RsaPkcs1Enc.writtenMsg s'.mem (s.gpr .a0) (s.gpr .a2) (s.gpr .a4).toNat ((s'.gpr .a0).setWidth 32)
    (Spec.RsaPkcs1Enc.decrypt (Spec.Rsa.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat) (dBytes s)
      (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 6).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 6).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 4).toNat) (cOf s))

theorem zx_setWidth (x : BitVec 64) : (zx x).setWidth 32 = x.setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp only [zx, BitVec.toNat_setWidth]
  omega_using []

theorem zx_one (x : BitVec 64) : decide (zx x ^^^ BitVec.ofNat 64 1 = 0) = decide (x.setWidth 32 = 1) := by
  have : zx x ^^^ BitVec.ofNat 64 1 = 0 ↔ x.setWidth 32 = 1 := by
    rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.xor_eq_zero_iff]
    constructor
    · intro h; rw [← zx_setWidth, h]; rfl
    · intro h; simp only [zx, h]; rfl
  simp only [this]

theorem zx_lt (x : BitVec 64) : (zx x ^^^ BitVec.ofNat 64 1).toNat < 2 ^ 63 := by
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat]
  have : (zx x).toNat < 2 ^ 32 := by simp only [zx, BitVec.toNat_setWidth]; omega_using []
  exact Nat.lt_of_lt_of_le (Nat.xor_lt_two_pow (n := 32) this (by decide)) (by decide)

/-- RSADP, as the specification calls the private-key operation. -/
def rsadpOf (s : State) (C : List Byte) : Spec.Rsa.Outcome :=
  Spec.Rsa.privateChecked (Spec.Rsa.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat) C
    (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 6).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 6).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 4).toNat)

/-- The outcome, from what the private-key operation gave and the end. -/
theorem result_ok {s : State} (h : DPre pc s) {x : BitVec 64} {mc : Mem} {t : State} {kd : List Byte}
    (hkd : kd = Spec.RsaPkcs1Enc.kdk (s.gpr .a4).toNat (dBytes s) (cOf s))
    (hres : Spec.Rsa.writtenOutcome mc (s.gpr .a0) (s.gpr .a4).toNat (x.setWidth 32) (rsadpOf s (cOf s)))
    (hx : t.gpr .a0 = zx x)
    (hout : ∀ i < (s.gpr .a4).toNat, t.mem (s.gpr .a0 + BitVec.ofNat 64 i) =
      outByte (vOfEM s (Spec.Rsa.bytesAt mc (s.gpr .a0) (s.gpr .a4).toNat)) (decide (zx x ^^^ BitVec.ofNat 64 1 = 0))
        ((s.gpr .a4).toNat - lenOf s (Spec.Rsa.bytesAt mc (s.gpr .a0) (s.gpr .a4).toNat) kd) i
        ((Spec.Rsa.bytesAt mc (s.gpr .a0) (s.gpr .a4).toNat).getD i 1) ((amOf s kd).getD i 0))
    (hml : t.mem.readW (s.gpr .a2) 64 =
      BitVec.ofNat 64 (lenOf s (Spec.Rsa.bytesAt mc (s.gpr .a0) (s.gpr .a4).toNat) kd) &&&
        bm (decide (zx x ^^^ BitVec.ofNat 64 1 = 0)))
    (hAM : (amOf s kd).length = (s.gpr .a4).toNat) : fnPost s t := by
  have hk := h.k1
  unfold fnPost
  have hn : (Spec.Rsa.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat).length = (s.gpr .a4).toNat :=
    Proof.Rsa.bytesAt_length' _ _ _
  have hC : (cOf s).length = (Spec.Rsa.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat).length := by
    rw [hn]; exact Proof.Rsa.bytesAt_length' _ _ _
  have hbytes : Spec.Rsa.bytesAt t.mem (s.gpr .a0) (s.gpr .a4).toNat =
      (List.range (s.gpr .a4).toNat).map fun i => t.mem (s.gpr .a0 + BitVec.ofNat 64 i) := rfl
  have hw : Spec.Rsa.wordsAt t.mem (s.gpr .a2) 1 = [t.mem.readW (s.gpr .a2) 64] := by
    simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero]
  simp only [Spec.RsaPkcs1Enc.decrypt]
  show Spec.RsaPkcs1Enc.writtenMsg _ _ _ _ _ (Spec.RsaPkcs1Enc.decryptWith (rsadpOf s)
    (Spec.Rsa.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat).length (dBytes s) (cOf s))
  cases hO : rsadpOf s (cOf s) with
  | ok EM' =>
    rw [hO] at hres
    obtain ⟨hr, hb⟩ := hres
    have hok : decide (zx x ^^^ BitVec.ofNat 64 1 = 0) = true := by rw [zx_one, hr]; rfl
    rw [Proof.RsaPkcs1Enc.decryptWith_of_ok hC (by rw [hn]; omega_using [hk]) hO]
    subst hb
    have hEMl := Proof.Rsa.bytesAt_length' mc (s.gpr .a0) (s.gpr .a4).toNat
    have hal := Proof.RsaPkcs1Enc.altLength_le (s.gpr .a4).toNat (clOf kd)
    obtain ⟨hL1, hmap⟩ := Proof.RsaPkcs1Enc.sel_eq hEMl hAM (by omega_using [hk]) hal
    have hM : Spec.RsaPkcs1Enc.implicitDecode (dBytes s) (cOf s) (Spec.Rsa.bytesAt mc (s.gpr .a0) (s.gpr .a4).toNat) =
        (if Spec.RsaPkcs1Enc.valid (Spec.Rsa.bytesAt mc (s.gpr .a0) (s.gpr .a4).toNat) then
          Spec.RsaPkcs1Enc.lastN (Spec.RsaPkcs1Enc.msgLength (Spec.Rsa.bytesAt mc (s.gpr .a0) (s.gpr .a4).toNat))
            (Spec.Rsa.bytesAt mc (s.gpr .a0) (s.gpr .a4).toNat)
        else Spec.RsaPkcs1Enc.lastN (Spec.RsaPkcs1Enc.altLength (s.gpr .a4).toNat (clOf kd)) (amOf s kd)) := by
      simp only [Spec.RsaPkcs1Enc.implicitDecode, Spec.RsaPkcs1Enc.alternative, hEMl, hkd]
    rw [hM]
    refine ⟨by rw [hx, zx_setWidth, hr], ?_, ?_⟩
    · rw [hbytes, ← hmap]
      exact List.map_congr_left fun i hi => by rw [hout i (List.mem_range.mp hi), hok]
    · rw [hw, hml, hok, show bm true = BitVec.allOnes 64 from rfl, BitVec.and_allOnes, ← hL1]
  | invalid =>
    rw [hO] at hres
    obtain ⟨hr, -⟩ := hres
    have hok : decide (zx x ^^^ BitVec.ofNat 64 1 = 0) = false := by rw [zx_one, hr]; rfl
    rw [Proof.RsaPkcs1Enc.decryptWith_of_invalid hO]
    refine ⟨by rw [hx, zx_setWidth, hr], ?_, ?_⟩
    · rw [hbytes, List.map_congr_left (g := fun _ => (0 : Byte)) fun i hi => by
        rw [hout i (List.mem_range.mp hi), hok, Proof.RsaPkcs1Enc.outByte_false]]
      rw [List.map_const', List.length_range]
    · rw [hw, hml, hok]; simp [bm]
  | fault =>
    rw [hO] at hres
    obtain ⟨hr, -⟩ := hres
    have hok : decide (zx x ^^^ BitVec.ofNat 64 1 = 0) = false := by rw [zx_one, hr]; rfl
    rw [Proof.RsaPkcs1Enc.decryptWith_of_fault hC (by rw [hn]; omega_using [hk]) hO]
    refine ⟨by rw [hx, zx_setWidth, hr], ?_, ?_⟩
    · rw [hbytes, List.map_congr_left (g := fun _ => (0 : Byte)) fun i hi => by
        rw [hout i (List.mem_range.mp hi), hok, Proof.RsaPkcs1Enc.outByte_false]]
      rw [List.map_const', List.length_range]
    · rw [hw, hml, hok]; simp [bm]

theorem codeG_correct (s : State) (h : DPre pc s) (X : pc = true → PreX s) :
    ∃ tr t, Exec isa (codeG pc) s tr t ∧ abiPreserved s t ∧ fnPost s t := by
  show WP isa (codeG pc) s fun t => abiPreserved s t ∧ fnPost s t
  have hk := h.k2
  unfold codeG
  refine WP.allocLe ⟨by decide, by decide, by decide⟩ (by have := h.sp1; unfold stackBytes at this; omega_using [this]) ?_
  unfold body
  refine WP.seq (WP.mono (setup_ok h) fun t₁ A => ?_)
  refine WP.seq (call_ok h X A fun t₂ A₂ => ?_)
  refine WP.seq (WP.mono (dBuild_ok h A₂) fun t₃ h₃ => ?_)
  refine WP.seq (WP.mono (hashD_ok h h₃) fun t₄ h₄ => ?_)
  refine WP.seq (WP.mono (kdkMac_ok h h₄) fun t₅ h₅ => ?_)
  refine WP.seq (WP.mono (clLoop_ok h h₅.toPost h₅.kdk) fun t₆ h₆ => ?_)
  refine WP.seq (WP.mono (amLoop_ok h h₆) fun t₇ h₇ => ?_)
  refine WP.seq (WP.mono (maskPart_ok h h₇) fun t₈ h₈ => ?_)
  refine WP.seq (WP.mono (alPart_ok h h₈) fun t₉ h₉ => ?_)
  refine WP.seq (WP.mono (scanPart_ok h h₉) fun t₁₀ h₁₀ => ?_)
  refine WP.mono (selPart_ok h h₁₀ (zx_lt _)) fun u hu m _ fl => ⟨⟨hu.abi.1, hu.abi.2.1, hu.abi.2.2⟩, ?_⟩
  have fl' : Frame [frR s] u.mem m := fl
  have hAM : (amOf s (Spec.RsaPkcs1Enc.kdk (s.gpr .a4).toNat (dBytes s) (cOf s))).length = (s.gpr .a4).toNat := by
    show (Spec.RsaPkcs1Enc.irprf _ _ _).length = _
    rw [← h₇.am]; exact Proof.Rsa.bytesAt_length' _ _ _
  refine result_ok h rfl A₂.out hu.a0 (fun i hi => ?_) ?_ hAM
  · exact (lost_byte fl' (R := ⟨s.gpr .a0, (s.gpr .a4).toNat⟩)
      (by rw [← h.h1]; exact (h.ko.sub_left (frR_sub s)).symm) hi).trans (hu.out i hi)
  · exact (fl'.readW (r := mlR s) (by simp only [Region.Contains]; rw [BitVec.sub_self]; decide)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact (h.km.sub_left (frR_sub s)).symm)
      (by decide)).trans hu.ml

theorem code_correct (s : State) (hpre : (Spec.RsaPkcs1Enc.decryptContract RISCV64.abi stackBytes).pre s) :
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ fnPost s t :=
  codeG_correct s (dPre_of hpre) nofun

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec

end

end

/-!
# `vg_rsa_pkcs1_decrypt` on RISC-V: constant time

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Enc/PPC64LE/DecVerified.lean`): the loops of `CL` and `AM`
(`clLoop_ct`, `amLoop_ct`), from `prfLoop_ct` with the taint checks of their
blocks; the alternative length, the scan and the output, which make no call,
by one taint check from the registers `Post` fixes (`tail_ct`); and the whole
function (`code_ct`), from the two entry states' `Env`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec

open VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt VG.Proof.RsaPkcs1Sig.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (mov)

variable {pc : Bool}

theorem clTaint : PrfTaint lengthLabel clLen [.li .t1 8] sCL where
  msg := ⟨_, by taint_decide⟩
  ini := ⟨_, by taint_decide⟩
  upd := ⟨_, by taint_decide⟩
  fin := ⟨_, by taint_decide⟩
  incr := ⟨_, by taint_decide⟩

theorem amTaint : PrfTaint messageLabel amLen [mov .t1 .s9] sAM where
  msg := ⟨_, by taint_decide⟩
  ini := ⟨_, by taint_decide⟩
  upd := ⟨_, by taint_decide⟩
  fin := ⟨_, by taint_decide⟩
  incr := ⟨_, by taint_decide⟩

section
variable {e : Env pc}

theorem clLoop_ct : RelCT isa (Rel e PostAt) clLoop (Rel e fun s u => PostAt s u ∧ u.gpr .s9 = nbOf s) := by
  unfold clLoop
  refine RelCT.seq (rel_step [.s1] (P' := L 0) (by unfold clInit; taint_decide) (pin_post (fun _ _ h => h) _)
    fun s u h ⟨_, _, P⟩ => ?_) ?_
  · have hk := h.k2
    unfold clInit
    refine wp_li (imm := 0) (by decide) fun v₁ p₁ f₁ => wp_addi (imm := 31) (fun v₂ p₂ f₂ =>
      wp_srl (sh := 5) fun t₁ p₃ f₃ => wp_nil ?_) (by decide)
    have O : Only [.s8, .s9] u t₁ := (p₁.trans (p₂.trans p₃)).mono
    exact ⟨⟨_, _, P.keep h O.keep (ws := []) (by rw [O.mem]; exact Frame.refl _ _) (fun r hr => nomatch hr)⟩,
      by rw [p₃.get .s8, p₂.get .s8, f₁], by rw [f₃, f₂, p₁.get .s1, P.s1, nb_eq hk]⟩
  exact prfLoop_ct clTaint (C := fun _ => BitVec.ofNat 64 8) rfl
    (fun i hi => Offset.ofNat_sub_ofNat (by omega_using [hi])) (N := 8) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
    (fun i hi s R EM u h P x8 => WP.mono (msgCL_ok (by rw [P.s0]) x8 (by omega_using [hi]) (P.msgW h)) fun w ⟨⟨F, _⟩, K⟩ => ⟨F, K⟩)
    (fun s u _ => count8_ok u)

theorem amLoop_ct :
    RelCT isa (Rel e fun s u => PostAt s u ∧ u.gpr .s9 = nbOf s) amLoop (Rel e PostAt) := by
  unfold amLoop
  refine RelCT.seq (rel_step [] (P' := L 0) (by taint_decide)
    (fun a b ⟨⟨_, _, A⟩, _⟩ ⟨⟨_, _, B⟩, _⟩ => ⟨(post_agree A B).1, fun _ h => nomatch h⟩)
    fun s u h ⟨⟨_, _, P⟩, h9⟩ => wp_li (imm := 0) (by decide) fun t₁ p₁ f₁ => wp_nil
      ⟨⟨_, _, P.keep h p₁.keep (ws := []) (by rw [p₁.mem]; exact Frame.refl _ _) (fun r hr => nomatch hr)⟩,
        f₁, by rw [p₁.get .s9, h9]⟩) ?_
  refine (prfLoop_ct amTaint (C := nbOf) (by rw [nbOf, nbOf, e.r])
    (fun i hi => Offset.ofNat_sub_ofNat (by omega_using [hi])) (N := ((e.s₁.gpr .a4).toNat + 31) / 32)
    (by have := e.h₁.k1; omega_using [this]) (by have := e.h₁.k2; omega_using [this]) (by decide) (by have := e.h₁.k2; unfold sAM scrBytes; omega_using [this])
    (by decide) (by decide)
    (fun i hi s R EM u h P x8 => WP.mono (msgAM_ok (by rw [P.s0]) x8 P.s1 (by have := e.h₁.k2; omega_using [hi, this]) h.k2 (P.msgW h))
      fun w ⟨⟨F, _⟩, K⟩ => ⟨F, K⟩)
    (fun s u hu => count_ok u _ hu)).mono (fun _ _ h => h) fun _ _ ⟨a, b⟩ => ⟨a.1, b.1⟩

/-! ## The rest -/

theorem tail_ct : RelCT isa (Rel e PostAt) (.seq maskPart (.seq alPart (.seq scanPart selPart))) fun _ _ => True :=
  rel_of (rs := [.s0, .s1, .s2, .s3]) (by taint_decide) fun a b hab =>
    pin_post (fun _ _ h => h) [.s0, .s1, .s2, .s3] (by decide) a b hab.1 hab.2

theorem body_ct : RelCT isa (Rel e PEnt) (body pc) fun _ _ => True := by
  unfold body
  refine RelCT.seq setup_ct (RelCT.seq priv_ct (RelCT.seq dBuild_ct (RelCT.seq hashD_ct
    (RelCT.seq kdkMac_ct (RelCT.seq clLoop_ct (RelCT.seq amLoop_ct tail_ct))))))

end

/-- A frame that allocates `bytes`, its body from both allocated states: the
allocation accesses no memory. -/
theorem rel_alloc {P : State → State → Prop} {bytes : Nat} {body : Prog isa} {R : State → State → Prop}
    (hb : RelCT isa (fun u₁ u₂ => ∃ s₁ s₂, P s₁ s₂ ∧ u₁ = allocd bytes s₁ ∧ u₂ = allocd bytes s₂) body R) :
    RelCT isa P (.frame (.alloc bytes) body (.free bytes)) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | frame p₁ b₁ _ =>
    cases e₂ with
    | frame p₂ b₂ _ =>
      obtain ⟨ht, -⟩ := hb _ _ _ _ _ _ ⟨_, _, hp, alloc_eq p₁, alloc_eq p₂⟩ b₁ b₂
      refine ⟨?_, trivial⟩
      rw [ht]
      simp [addrs]

/-- Two entry states of `codeG pc` with the same public data (an `Env`) run in the same time. -/
theorem codeG_rel : RelCT isa (fun s₁ s₂ => ∃ e : Env pc, e.s₁ = s₁ ∧ e.s₂ = s₂) (codeG pc) fun _ _ => True :=
  rel_alloc ((RelCT.exists_ fun e : Env pc => body_ct (e := e)).mono
    (fun _ _ ⟨s₁, s₂, ⟨e, h₁, h₂⟩, ea, eb⟩ => ⟨e, by subst h₁ h₂; exact ⟨ea, eb⟩⟩) fun _ _ h => h)

theorem code_ct : ConstantTime isa (Spec.RsaPkcs1Enc.decryptContract RISCV64.abi stackBytes).pre
    (Spec.RsaPkcs1Enc.decryptContract RISCV64.abi stackBytes).pub code :=
  RelCT.constantTime ((codeG_rel (pc := false)).mono
    (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨⟨s₁, s₂, dPre_of h₁, dPre_of h₂, same_of hp, nofun, nofun⟩, rfl, rfl⟩)
    fun _ _ h => h)

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec

end

end

/-!
# `vg_rsa_pkcs1_decrypt` on RISC-V: verified against the shared contract

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Enc/PPC64LE/DecVerified.lean`): `fnContract` states the
shared contract's postcondition on the registers and the stack
(`dec_implies`); with correctness (`code_correct`) and constant time
(`code_ct`), `code` is verified for the stack its frame and
`vg_rsa_private_checked`'s use (`dec_verified`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Dec

open VG.RISCV64 VG.Impl.RsaPkcs1Enc.RISCV64.Decrypt

/-- The shared contract, its postcondition on the registers and the stack. -/
def fnContract : Contract isa where
  pre := (Spec.RsaPkcs1Enc.decryptContract RISCV64.abi stackBytes).pre
  post := fnPost
  pub := (Spec.RsaPkcs1Enc.decryptContract RISCV64.abi stackBytes).pub

/-- A state meeting the precondition: a 64-byte modulus, input and `out`,
one-byte exponents, primes, CRT exponents and `qInv`, and the stack
arguments at `sp`. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 64 | .a2 => 0x1100 | .a3 => 0x2000 | .a4 => 64 | .a5 => 0x3000
    | .a6 => 1 | .a7 => 0x3100 | _ => 0
  sp := 0x10000
  mem a :=
    bif Nat.beq a.toNat 0x10000 then 1 else bif Nat.beq a.toNat 0x10009 then 0x40
    else bif Nat.beq a.toNat 0x10010 then 0x40 else bif Nat.beq a.toNat 0x10019 then 0x41
    else bif Nat.beq a.toNat 0x10020 then 1 else bif Nat.beq a.toNat 0x10029 then 0x42
    else bif Nat.beq a.toNat 0x10030 then 1 else bif Nat.beq a.toNat 0x10039 then 0x43
    else bif Nat.beq a.toNat 0x10040 then 1 else bif Nat.beq a.toNat 0x10049 then 0x44
    else bif Nat.beq a.toNat 0x10050 then 1 else bif Nat.beq a.toNat 0x10059 then 0x45
    else bif Nat.beq a.toNat 0x10060 then 1 else bif Nat.beq a.toNat 0x1006A then 0x02
    else bif Nat.beq a.toNat 0x10070 then 0x20 else bif Nat.beq a.toNat 0x10071 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x3100, 1⟩, ⟨0x4000, 64⟩, ⟨0x4100, 1⟩, ⟨0x4200, 1⟩, ⟨0x4300, 1⟩,
    ⟨0x4400, 1⟩, ⟨0x4500, 1⟩, ⟨0x10000, 120⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x1100, 8⟩, ⟨0x20000, 8448⟩]

theorem dec_implies : fnContract.Implies (Spec.RsaPkcs1Enc.decryptContract RISCV64.abi stackBytes) where
  pre := fun _ h => h
  post := by
    sig_implies_post [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, RISCV64.abi,
      RISCV64.argRegs, fnContract, fnPost, stackArgs_fifteen, List.append_eq, dBytes, cOf]
  pub := fun _ _ _ _ h => h
  sat := by
    sig_implies_sat [Spec.RsaPkcs1Enc.decryptContract, Spec.RsaPkcs1Enc.decryptSig, RISCV64.abi,
      RISCV64.argRegs, fnContract, stackArgs_fifteen, List.append_eq]
      [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState

/-- `vg_rsa_pkcs1_decrypt`. -/
theorem dec_verified : Verified RISCV64.target code (Spec.RsaPkcs1Enc.decryptContract RISCV64.abi stackBytes) :=
  Verified.of_correct code_correct code_ct dec_implies

end VG.Proof.RsaPkcs1Enc.RISCV64.Dec

module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.Dec.Calls
public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Two
public import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
public import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rsa.PrivCheck
import VerifiedGarbage.Proof.Sha256.RISCV64.Stream.Init
import VerifiedGarbage.Proof.Sha256.RISCV64.Stream.Update
import VerifiedGarbage.Proof.Sha256.RISCV64.Stream.Finalize
import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Sha256
import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.InitMain
import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Finalize
import VerifiedGarbage.Proof.Framework.Covers

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

/-- The public data's facts. -/
structure Same (s₁ s₂ : State) : Prop where
  gpr : ∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r
  arg : ∀ i < 15, stackArg s₁ i = stackArg s₂ i
  sp : s₁.sp = s₂.sp
  n : Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a3) (s₁.gpr .a4).toNat = Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a3) (s₂.gpr .a4).toNat
  e : Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a5) (s₁.gpr .a6).toNat = Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a5) (s₂.gpr .a6).toNat

theorem same_of {s₁ s₂ : State} (h : (Spec.RsaPkcs1Enc.decryptContract RISCV64.abi stackBytes).pub s₁ s₂) :
    Same s₁ s₂ := by
  have e : stackBytes = 3439 + 1 := rfl
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
    ((List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 he)⟩
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h3, h4, h5, h6, h7, h8, h9, h10]
  · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨
      i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14]

/-- Two entry states with the same public data. -/
structure Env where
  s₁ : State
  s₂ : State
  h₁ : DPre s₁
  h₂ : DPre s₂
  S : Same s₁ s₂

/-- Run `i` satisfies `P sᵢ`. -/
def Rel (e : Env) (P : State → State → Prop) (a b : State) : Prop := P e.s₁ a ∧ P e.s₂ b

/-- Two runs whose stack pointers and registers `rs` agree. -/
def AgreeOn (rs : List Reg) (a b : State) : Prop := a.sp = b.sp ∧ ∀ r ∈ rs, a.gpr r = b.gpr r

theorem rel_of {rs : List Reg} {c : Prog isa} {hc : VG.Taint.Hint VG.RISCV64.Taint.T}
    (h : (taint.check (VG.RISCV64.Taint.ofRegs rs) c hc).isSome = true) {P : State → State → Prop}
    (hp : ∀ a b, P a b → AgreeOn rs a b) : RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := taint) (VG.RISCV64.Taint.ofRegs rs) (fun a b hab => ⟨(hp a b hab).1, fun r hr =>
    (hp a b hab).2 r (by simpa [VG.RISCV64.Taint.ofRegs] using hr)⟩) h

section
variable {e : Env}

theorem Env.r (e : Env) {r : Reg} (hr : r ∈ argRegs := by decide) : e.s₁.gpr r = e.s₂.gpr r := e.S.gpr r hr
theorem Env.arg (e : Env) {i : Nat} (hi : i < 15 := by decide) : stackArg e.s₁ i = stackArg e.s₂ i := e.S.arg i hi
theorem Env.fb_eq (e : Env) : fb e.s₁ = fb e.s₂ := by
  show e.s₁.sp - _ = e.s₂.sp - _; rw [e.S.sp]
theorem Env.scA_eq (e : Env) (a : Nat) : scA e.s₁ a = scA e.s₂ a := by
  show stackArg e.s₁ 13 + _ = stackArg e.s₂ 13 + _; rw [e.arg]

/-- A step, from what correctness gives of each run. -/
theorem rel_post {P P' : State → State → Prop} {c : Prog isa} (hct : RelCT isa (Rel e P) c fun _ _ => True)
    (hw : ∀ s u, DPre s → P s u → WP isa c u (P' s)) : RelCT isa (Rel e P) c (Rel e P') := by
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
    (hw : ∀ s u, DPre s → P s u → WP isa c u (P' s)) : RelCT isa (Rel e P) c (Rel e P') :=
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
variable {e : Env}

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
  have pre : ∀ {s t : State}, DPre s → (P' : ∃ R EM, Post s R EM t) → UpdAt s t a (dat s) (len s) →
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
  have pre : ∀ {s t : State} {R : BitVec 64} {EM : List Byte}, DPre s → Post s R EM t → t.gpr .a0 = scA s a →
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
  have pre : ∀ {s t : State} {R : BitVec 64} {EM : List Byte}, DPre s → Post s R EM t → t.gpr .a0 = scA s sSt →
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
    exact ⟨trivial, trivial, scDisj (.inl (by decide)) hi hu, scDisj (.inr (by unfold sSt sOuter at *; omega)) hk hi,
      scDisj (.inr hk1) hk hu, fb_al h, fb_ge h X, lowSc h X hi, lowSc h X hu, lowSc h X hk⟩
  have cov : ∀ {s t : State} {R : BitVec 64} {EM : List Byte}, DPre s → Post s R EM t →
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
  have pre : ∀ {s t : State} {R : BitVec 64} {EM : List Byte}, DPre s → Post s R EM t → t.gpr .a0 = scA s sSt →
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
    exact ⟨trivial, trivial, scDisj (.inl (by decide)) hi hu, scDisj (.inl (by unfold sSt sOuter at *; omega)) hi ho,
      scDisj (.inl ho1) hu ho, fb_al h, fb_ge h X, lowSc h X hi, lowSc h X hu, lowSc h X ho⟩
  have cov : ∀ {s t : State} {R : BitVec 64} {EM : List Byte}, DPre s → Post s R EM t →
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

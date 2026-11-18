module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Regs
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Table
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Regs
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Table
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.AArch64.TaintErase
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintErase
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.ICall
meta import VerifiedGarbage.Proof.Framework.ICall
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Msg
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Msg
import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Calls
meta import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Calls
import VerifiedGarbage.Proof.RsaOaep.AArch64.Loops
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.Loops
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Cand
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Search
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Reduce
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Cand
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Search
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Reduce
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Curve
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Curve

/-! ### `Ecdsa.Rfc6979.AArch64.Instrs`, which only this module used -/

section

/-!
# Deterministic ECDSA on AArch64: no instruction writes a callee-saved SIMD register

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Table.lean`), for `keepsV`: for
code `c` (`Impl.Ecdsa.Rfc6979.AArch64.Cfg`) whose blocks of the curve keep
the callee-saved SIMD registers (`RfcT`, which each curve's file checks),
whose table's functions keep them (`FnsOk`) and whose `core` keeps them:
the frame's body (`body_okP`), and so the whole function (`sign_okP`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64

/-- No instruction of `x` writes a callee-saved SIMD register. -/
abbrev OkP (x : Prog isa) : Prop := x.allInstrs keepsV = true

theorem okP_seq {a b : Prog isa} (ha : OkP a) (hb : OkP b) : OkP (.seq a b) := by
  show (a.allInstrs keepsV && b.allInstrs keepsV) = true; rw [ha, hb]; rfl

theorem okP_ite {cnd : Cond} {a b : Prog isa} (ha : OkP a) (hb : OkP b) : OkP (.ite cnd a b) := by
  show (a.allInstrs keepsV && b.allInstrs keepsV) = true; rw [ha, hb]; rfl

theorem okP_loop {cnd : Cond} {a : Prog isa} (ha : OkP a) : OkP (.loop a cnd) := ha

theorem okP_call {n : String} {a : Prog isa} (ha : OkP a) : OkP (.call n a) := ha

/-- Nor in any of the functions `ts`. -/
def FnsOk (ts : List (String × Prog isa)) : Prop := ∀ q ∈ ts, OkP q.2

theorem icalls_okP : ∀ {ts : List (String × Prog isa)}, FnsOk ts → OkP (Code.icalls (.blr .x16) ts)
  | [], _ => rfl
  | q :: ts, h => by
    have hq := h q (List.mem_cons_self ..)
    have ih := icalls_okP (ts := ts) fun r hr => h r (List.mem_cons_of_mem _ hr)
    show (Code.icalls (.blr .x16) (q :: ts)).allInstrs keepsV = true
    simp only [Code.icalls, Code.allInstrs, show q.2.allInstrs keepsV = true from hq,
      show (Code.icalls (.blr .x16) ts).allInstrs keepsV = true from ih, Bool.and_true]; rfl

theorem tcall_okP {j : Nat} {ts : List (String × Prog isa)} (h : FnsOk ts) : OkP (Cfg.tcall j ts) :=
  okP_seq rfl (icalls_okP h)

/-- The code's blocks of the curve, with the functions it calls and the
bound on candidates of `cfgC`'s, which each curve's `RfcT` is of. -/
abbrev strip (c : Cfg) : Cfg := { c with f := ⟨[], [], []⟩, tries := 8, coreN := "", coreC := .block [] }

theorem cpLoop_okP : OkP Cfg.cpLoop := rfl

variable {c : Cfg} (hT : RfcT (strip c)) (hf : FnsOk c.f.init ∧ FnsOk c.f.upd ∧ FnsOk c.f.fin)
include hf

theorem initK_okP : OkP c.initK := okP_seq rfl (tcall_okP hf.1)

theorem updV_okP : OkP c.updV := okP_seq rfl (tcall_okP hf.2.1)

theorem updM_okP (len : Nat) : OkP (c.updM len) := okP_seq rfl (tcall_okP hf.2.1)

theorem fin_okP (len dst : Nat) : OkP (c.fin len dst) := okP_seq rfl (tcall_okP hf.2.2)

theorem hmacVS_okP : OkP c.hmacVS :=
  okP_seq (initK_okP hf) (okP_seq (by rfl) (okP_seq (updV_okP hf) (fin_okP hf _ _)))

theorem hmacVR_okP : OkP c.hmacVR := okP_seq (by rfl) (okP_seq (updV_okP hf) (fin_okP hf _ _))

theorem hmacK_okP (fresh : Bool) (len : Nat) : OkP (c.hmacK fresh len) := by
  unfold Cfg.hmacK
  refine okP_seq ?_ (okP_seq (updV_okP hf) (okP_seq (updM_okP hf _) (fin_okP hf _ _)))
  cases fresh
  · exact by rfl
  · exact initK_okP hf

include hT

theorem rekeyFull_okP (b : Nat) (hb : b < 2) : OkP (c.rekeyFull b) := by
  unfold Cfg.rekeyFull
  obtain rfl | rfl : b = 0 ∨ b = 1 := by omega_using [hb]
  · exact okP_seq rfl (okP_seq (by exact hT.iMsgF₀) (okP_seq (hmacK_okP hf _ _) (hmacVS_okP hf)))
  · exact okP_seq rfl (okP_seq (by exact hT.iMsgF₁) (okP_seq (hmacK_okP hf _ _) (hmacVS_okP hf)))

omit hT in
theorem rekey_okP : OkP c.rekey :=
  okP_seq rfl (okP_seq (by simp only [Cfg.msg, Bool.false_eq_true, ite_false, List.append_nil]; rfl)
    (okP_seq (hmacK_okP hf _ _) (hmacVS_okP hf)))

omit hf in
theorem candTop_okP : OkP c.candTop := by
  unfold Cfg.candTop
  split
  · exact okP_seq rfl (by exact hT.iConvT)
  · rfl

theorem cand_okP : OkP c.cand :=
  okP_seq rfl (okP_seq (okP_loop (okP_seq (hmacVR_okP hf) (okP_seq rfl (okP_seq cpLoop_okP (by exact hT.iTStep)))))
    (candTop_okP hT))

theorem tryOne_okP (hcore : OkP c.coreC) : OkP c.tryOne :=
  okP_seq (cand_okP hT hf) (okP_seq (by exact hT.iCoreArgs) (okP_seq (okP_call hcore) (okP_seq rfl
    (okP_ite (okP_seq (rekey_okP hf) rfl) rfl))))

omit hf in
theorem prepH_okP : OkP c.prepH := by
  unfold Cfg.prepH
  split
  · exact okP_seq (by exact hT.iXcArgs) (okP_seq cpLoop_okP (okP_seq rfl (by exact hT.iConvC)))
  · exact by exact hT.iReduce

/-- The frame's body: no instruction writes a callee-saved SIMD register. -/
theorem body_okP (hcore : OkP c.coreC) : OkP c.body :=
  okP_seq rfl (okP_seq (okP_seq (by exact hT.iXArgs) cpLoop_okP) (okP_seq (prepH_okP hT) (okP_seq rfl
    (okP_seq (rekeyFull_okP hT hf 0 (by decide)) (okP_seq (rekeyFull_okP hT hf 1 (by decide)) (okP_seq rfl
      (okP_seq (okP_loop (tryOne_okP hT hf hcore)) rfl)))))))

/-- The whole function: its entry, and the frames' pushes and pops. -/
theorem sign_okP (hcore : OkP c.coreC) : OkP (signCode c) := by
  have hb := body_okP hT hf hcore
  refine okP_seq rfl ?_
  simp only [OkP, Cfg.sign, Code.allInstrs, hb, Bool.and_true]
  rfl

end VG.Proof.Ecdsa.Rfc6979.AArch64

end

end

/-! ### `Ecdsa.Rfc6979.AArch64.CT`, which only this module used -/

section

/-! ### `Ecdsa.Rfc6979.AArch64.Correct`, which only this module used -/

section

/-! ### `Ecdsa.Rfc6979.AArch64.Loop`, which only this module used -/

section

/-! ### `Ecdsa.Rfc6979.AArch64.Core`, which only this module used -/

section

/-!
# Deterministic ECDSA on AArch64: signing with a candidate

The call of `vg_ecdsa_<curve>_sign_k` with the digest `X` (or, if `big`,
the one at `fXc`) and the candidate `T`, above the frame's pointers
(`core_ok`): it returns 1 and writes the signature, or returns 0 and writes
zeros, as `Spec.Ecdsa.signWith` gives for `d` and `Q` bytes of the digest
and of `k`, and changes only `out` and `scratch` (it pushes no frame: its
return address is in `x30`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64

variable {P : RfcHash} {dn : Nat} {L : Lay dn P.R.E} {g : Reg → BitVec 64} {m₀ : Mem}

/-- The signature `core` computes, or none. -/
abbrev coreSig (P : RfcHash) {dn : Nat} (L : Lay dn P.R.E) (m : Mem) : Option (Nat × Nat) :=
  coreSigOf P.R.E m L.d (dgArg P L) (kArg P L)

/-- `core` reads the private key, the digest and `k`, `Q` bytes each, and
the comb's tables. -/
abbrev coreRd (P : RfcHash) {dn : Nat} (L : Lay dn P.R.E) : List Region :=
  [⟨L.d, P.Q⟩, ⟨dgArg P L, P.Q⟩, ⟨kArg P L, P.Q⟩] ++ L.tables
abbrev coreWr (P : RfcHash) {dn : Nat} (L : Lay dn P.R.E) : List Region := [⟨L.out, 2 * P.Q⟩, L.SCR]

/-- What `core`'s arguments need of the layout: the scalars' bytes. -/
def CoreOk (P : RfcHash) {dn : Nat} (L : Lay dn P.R.E) : Prop := L.q = P.Q

/-- `core`'s digest and `k`: in the frame above its pointers, apart from
`out` and `scratch`. -/
theorem coreArg_ok (hL : L.Ok) (_hk : CoreOk P L) {x : Addr} (hx : x = dgArg P L ∨ x = kArg P L) :
    (∃ R ∈ [L.D, L.DG, L.FR], Within ⟨x, P.Q⟩ R) ∧ Region.Disjoint ⟨x, P.Q⟩ L.OUT ∧
      Region.Disjoint ⟨x, P.Q⟩ L.SCR := by
  have hQ : P.Q ≤ 66 := P.sizes.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have he := L.he
  have key : ∀ o, 16 ≤ o → o + 66 ≤ 600 → (∃ R ∈ [L.D, L.DG, L.FR],
      Within ⟨L.B + BitVec.ofNat 64 o, P.Q⟩ R) ∧ Region.Disjoint ⟨L.B + BitVec.ofNat 64 o, P.Q⟩ L.OUT ∧
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 o, P.Q⟩ L.SCR := fun o h₁ h₂ =>
    ⟨⟨L.FR, by simp, within_fr _ h₁ (by omega_using [hQ, he, h₂])⟩, hL.stk_OUT (by omega_using [hQ, he, h₂]), hL.stk_SCR (by omega_using [hQ, he, h₂])⟩
  simp only [dgArg, kArg] at hx
  rcases hx with h | rfl
  · split at h <;> subst h
    · exact key (16 + fXc) (by decide) (by decide)
    · exact key (16 + fX) (by decide) (by decide)
  · exact key (16 + fT) (by decide) (by decide)

theorem ce_gpr (t : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

/-- The comb's tables, as on entry. -/
theorem tbl_held (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) : ∀ i < P.R.E.combWords.length,
    t.mem.readW (L.T + BitVec.ofNat 64 (8 * i)) 64 = P.R.E.combWords.getD i 0 := fun i hi => by
  have hT := hL.nT
  rw [hc.frame.readW (r := L.TBL) (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi, hT])) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hL.tOut
    · exact hL.tScr
    · exact hL.tStk) (by decide)]
  exact hc.held i hi

theorem core_pre (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t)
    (h0 : t.gpr .x0 = L.out) (h1 : t.gpr .x1 = L.d) (h2 : t.gpr .x2 = dgArg P L) (h3 : t.gpr .x3 = kArg P L)
    (h4 : t.gpr .x4 = L.scr) :
    (coreK P.R.E).pre (t.callEntry.withRegions (coreRd P L) (coreWr P L)) := by
  have hq' : L.q = P.R.E.C.len := hk
  have eD : (⟨L.d, P.R.E.C.len⟩ : Region) = L.D := by rw [Lay.D, hq']
  have eO : (⟨L.out, 2 * P.R.E.C.len⟩ : Region) = L.OUT := by rw [Lay.OUT, hq']
  have no : L.out.toNat + 2 * P.R.E.C.len ≤ 2 ^ 64 := by have := hL.no; rw [hq'] at this; omega_using [this]
  obtain ⟨-, gO, gS⟩ := coreArg_ok hL hk (.inl rfl)
  obtain ⟨-, kO, kS⟩ := coreArg_ok hL hk (.inr rfl)
  have sy : ∀ rd wr, tableAddr P.R.E (t.callEntry.withRegions rd wr).syms = L.T := fun _ _ => hc.sy
  simp only [coreK, TblOk, coreRd, coreWr, eD, eO, ce_gpr _ _ _ (by decide : Reg.x0 ∉ linkRegs),
    ce_gpr _ _ _ (by decide : Reg.x1 ∉ linkRegs), ce_gpr _ _ _ (by decide : Reg.x2 ∉ linkRegs),
    ce_gpr _ _ _ (by decide : Reg.x3 ∉ linkRegs), ce_gpr _ _ _ (by decide : Reg.x4 ∉ linkRegs), h0, h1, h2, h3,
    h4, State.withRegions_rd, State.withRegions_wr, State.withRegions_mem, State.callEntry_mem, sy]
  exact ⟨by atriv, by atriv, hL.oc, hL.od, gO.symm, kO.symm, hL.dc, gS, kS, no, hL.nc, tbl_held hL hc,
    hL.nT, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.tOut.sub_right (Region.sub_prefix (by omega_using []))
      · exact hL.tScr⟩

theorem core_covers (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t) :
    Covers (coreRd P L ++ coreWr P L) (t.rd ++ t.wr) := by
  have hq : L.q = P.Q := hk
  have hw : ∀ {x : Addr}, (∃ R ∈ [L.D, L.DG, L.FR], Within ⟨x, P.Q⟩ R) →
      ∃ R ∈ ([L.D, L.DG, L.TAB] ++ L.tables) ++ [L.FR, L.LR, L.OUT, L.SCR], Within ⟨x, P.Q⟩ R :=
    fun ⟨R, hR, hW⟩ => ⟨R, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR; rcases hR with rfl | rfl | rfl <;> simp, hW⟩
  refine covers_of fun r hr => ?_
  rw [hc.rd, hc.wr]
  change r ∈ [⟨L.d, P.Q⟩, ⟨dgArg P L, P.Q⟩, ⟨kArg P L, P.Q⟩] ++ L.tables ++
    [⟨L.out, 2 * P.Q⟩, L.SCR] at hr
  rcases List.mem_append.mp hr with hr | hr
  · rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨L.D, by simp, within_base _ (by omega_using [hq])⟩
      · exact hw (coreArg_ok hL hk (.inl rfl)).1
      · exact hw (coreArg_ok hL hk (.inr rfl)).1
    · exact ⟨r, by simp [hr], within_base _ (Nat.le_refl _)⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨L.OUT, by simp, within_base _ (by omega_using [hq])⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega_using [])⟩

theorem core_coversW (hq : L.q = P.Q) {t : State} (hc : Ctx L g m₀ t) : Covers (coreWr P L) t.wr :=
  hc.coversW fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨L.OUT, by simp, within_base _ (by omega_using [hq])⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega_using [])⟩

/-- `core(out, d, digest, k, scratch)`. -/
theorem core_ok (hL : L.Ok) (hk : CoreOk P L) {t : State} (hc : Ctx L g m₀ t)
    (h0 : t.gpr .x0 = L.out) (h1 : t.gpr .x1 = L.d) (h2 : t.gpr .x2 = dgArg P L) (h3 : t.gpr .x3 = kArg P L)
    (h4 : t.gpr .x4 = L.scr) :
    WP isa (.call (cfgOf P).coreN (cfgOf P).coreC) t fun t' => Ctx L g m₀ t' ∧
      Frame [L.OUT, L.SCR] t.mem t'.mem ∧
      match coreSig P L t.mem with
      | some rs => (t'.gpr .x0).setWidth 32 = 1 ∧
          Spec.Sha256.bytesAt t'.mem L.out (2 * P.Q) = Spec.Ecdsa.encode P.R.E.C rs
      | none => (t'.gpr .x0).setWidth 32 = 0 ∧
          Spec.Sha256.bytesAt t'.mem L.out (2 * P.Q) = List.replicate (2 * P.Q) 0 := by
  have hq : L.q = P.Q := hk
  have eW : coreWr P L = [L.OUT, L.SCR] := by simp only [coreWr, Lay.OUT, hq]
  refine WP.of_syms (WP.call (k := coreK P.R.E) P.R.coreX (core_pre hL hk hc h0 h1 h2 h3 h4)
    (core_covers hL hk hc) (core_coversW hq hc) (fun t' hrd hwr hsp hf hcs _ hpost hsy => ?_) P.R.coreNoFrames)
  rw [eW] at hf
  refine ⟨hc.keep hL hrd hwr hsp hcs hf (hsy := hsy) fun r hr => ?_, hf, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl (sub_refl _)
    · exact .inr (.inl (sub_refl _))
  · simp only [coreK, ce_gpr _ _ _ (by decide : Reg.x0 ∉ linkRegs),
      ce_gpr _ _ _ (by decide : Reg.x1 ∉ linkRegs), ce_gpr _ _ _ (by decide : Reg.x2 ∉ linkRegs),
      ce_gpr _ _ _ (by decide : Reg.x3 ∉ linkRegs), h0, h1, h2, h3, State.withRegions_mem, State.callEntry_mem,
      State.withRegions_gpr, Rfc6979.ecdsa_bytesAt] at hpost
    exact hpost

end VG.Proof.Ecdsa.Rfc6979.AArch64

end

end


/-!
# Deterministic ECDSA on AArch64: the candidates

The values of a run, as RFC 6979 computes them from the private key and the
digest on entry (`kvI`, `candI`, `sigI`), with candidates of `nV` `V`s; the candidate's `k` for `core` (`cand_ok`); the loop's invariant
before candidate `i` (`LoopInv`): `K` and `V` are those before it, the count
is `tries - i`, every earlier candidate was unsuitable, and `core`'s digest is
the digest's (`DgOk`). One iteration either moves to candidate `i + 1`,
branching back, or leaves the loop with the signature of candidate `i`,
which is suitable or the last (`tryOne_ok`, `loop_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64
open VG.Proof.Ecdsa.Rfc6979 (kvAtB candAtB stepB)

variable {P : RfcHash} {L : Lay P.I.hashLen P.R.E} {g : Reg → BitVec 64} {m₀ : Mem}

/-! ## The run's values -/

/-- The private key, the digest and its integer. -/
abbrev xOf (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (m₀ : Mem) : Nat :=
  Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m₀ L.d P.Q)
abbrev hBOf (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) : List Byte := Spec.Sha256.bytesAt m₀ L.dg P.H.D
abbrev eOf (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) : Nat := Spec.Ecdsa.hashToInt P.R.E.C (hBOf P L m₀)

/-- `K` and `V` after steps b–g. -/
abbrev kv0 (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) : List Byte × List Byte :=
  Spec.Ecdsa.Rfc6979.init P.R.E.C P.ok.SH.H P.H.D (xOf P L m₀) (hBOf P L m₀)

/-- `K` and `V` before candidate `i`, candidate `i`'s `T`, and its signature. -/
abbrev kvI (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) (i : Nat) : List Byte × List Byte :=
  kvAtB P.ok.SH.H P.nV (kv0 P L m₀).1 (kv0 P L m₀).2 i
abbrev candI (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) (i : Nat) : List Byte :=
  candAtB P.ok.SH.H P.nV (kv0 P L m₀).1 (kv0 P L m₀).2 i
abbrev sigI (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) (i : Nat) : Option (Nat × Nat) :=
  Spec.Ecdsa.signWith P.R.E.C (xOf P L m₀) (eOf P L m₀) (Spec.Ecdsa.Rfc6979.bits2int P.R.E.C (candI P L m₀ i))

/-- `core`'s digest is the digest's integer. -/
def DgOk (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ m : Mem) : Prop :=
  Spec.Ecdsa.hashToInt P.R.E.C (Spec.Sha256.bytesAt m (dgArg P L) P.Q) = eOf P L m₀

/-- What the function's result is, for the signature `r` of the last candidate. -/
def ResultIs (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (r : Option (Nat × Nat)) (t : State) : Prop :=
  match r with
  | some rs => (t.gpr .x0).setWidth 32 = 1 ∧
      Spec.Sha256.bytesAt t.mem L.out (2 * P.Q) = Spec.Ecdsa.encode P.R.E.C rs
  | none => (t.gpr .x0).setWidth 32 = 0 ∧
      Spec.Sha256.bytesAt t.mem L.out (2 * P.Q) = List.replicate (2 * P.Q) 0

/-- Before candidate `i`. -/
structure LoopInv (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  lt : i < P.I.tries
  k : kOf P L t.mem = (kvI P L m₀ i).1
  v : vOf P L t.mem = (kvI P L m₀ i).2
  cnt : cnt L t.mem = BitVec.ofNat 64 (P.I.tries - i)
  fails : ∀ j < i, sigI P L m₀ j = none
  dg : DgOk P L m₀ t.mem
  saved : SavedK P L t.mem (kOf P L t.mem)

/-- After the loop, at candidate `i`: suitable or the last. -/
structure Exit (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) (i : Nat) (t : State) : Prop where
  lt : i < P.I.tries
  fails : ∀ j < i, sigI P L m₀ j = none
  last : sigI P L m₀ i ≠ none ∨ i + 1 = P.I.tries
  res : ResultIs P L (sigI P L m₀ i) t

/-! ## Facts kept -/

theorem Ctx.dBytes (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {n : Nat} (hn : n ≤ L.q) :
    Spec.Sha256.bytesAt t.mem L.d n = Spec.Sha256.bytesAt m₀ L.d n := by
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => hc.d_byte hL (by have := List.mem_range.mp hi; omega_arith)

theorem Ctx.dgBytes (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {n : Nat} (hn : n ≤ P.I.hashLen) :
    Spec.Sha256.bytesAt t.mem L.dg n = Spec.Sha256.bytesAt m₀ L.dg n := by
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => hc.dg_byte hL (by have := List.mem_range.mp hi; omega_arith)

/-- The count, kept by memory that changed elsewhere. -/
theorem cnt_frame {ws : List Region} {m m' : Mem} (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨L.B + BitVec.ofNat 64 192, 8⟩ r) : cnt L m' = cnt L m :=
  hf.readW (Region.contains_self _ _) hd (by decide)

theorem kvw_cnt (hL : L.Ok) : ∀ r ∈ KVW L, Region.Disjoint ⟨L.B + BitVec.ofNat 64 192, 8⟩ r := by
  simp only [KVW, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact hL.stk_SCR (by anums)
  · exact Offset.disjoint_base _ (by anums) (by anums)

theorem cw_cnt (hL : L.Ok) : ∀ r ∈ CW L, Region.Disjoint ⟨L.B + BitVec.ofNat 64 192, 8⟩ r := by
  simp only [CW, List.mem_cons, List.not_mem_nil, or_false]
  have := L.he
  rintro r (rfl | rfl | rfl)
  · exact hL.stk_SCR (by omega_arith)
  · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
  · exact Offset.disjoint _ (.inl (by simp only [fT]; omega_arith)) (by omega_arith) (by simp only [fT]; omega_arith)

/-- What `core` changes: `out` and `scratch`. -/
abbrev CoreW {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) : List Region := [L.OUT, L.SCR]

theorem corew_disj (hL : L.Ok) {d n : Nat} (h₂ : d + n ≤ 256 + 8 * L.e) :
    ∀ r ∈ CoreW L, Region.Disjoint ⟨L.B + BitVec.ofNat 64 d, n⟩ r := by
  simp only [CoreW, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact hL.stk_OUT h₂
  · exact hL.stk_SCR h₂

/-- The regions the loop writes, which are apart from `core`'s digest. -/
def DgApart {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (r : Region) : Prop :=
  r = L.SCR ∨ r = L.OUT ∨ r = ⟨L.B, 144⟩ ∨ r = ⟨L.B, 152⟩ ∨ r = ⟨L.B + BitVec.ofNat 64 192, 8⟩ ∨
    r = ⟨L.B + BitVec.ofNat 64 (16 + fT), 136⟩ ∨ r = ⟨L.B + BitVec.ofNat 64 16, 128⟩

theorem dg_apart (hL : L.Ok) {r : Region} (h : DgApart L r) : Region.Disjoint ⟨dgArg P L, P.Q⟩ r := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hQ66, -, -⟩ := P.sizes
  have he := L.he
  have key : ∀ o, 200 ≤ o → o + P.Q ≤ 16 + fT → Region.Disjoint ⟨L.B + BitVec.ofNat 64 o, P.Q⟩ r := by
    intro o h₁ h₂
    simp only [fT] at h₂
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hL.stk_SCR (by omega_arith)
    · exact hL.stk_OUT (by omega_arith)
    · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
    · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
    · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
    · exact Offset.disjoint _ (.inl (by simp only [fT]; omega_arith)) (by omega_arith) (by simp only [fT]; omega_arith)
    · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  simp only [dgArg]
  split
  · exact key _ (by simp only [fXc]; omega_arith) (by simp only [fXc, fT]; omega_arith)
  · exact key _ (by simp only [fX]; omega_arith) (by simp only [fX, fT]; omega_arith)

theorem DgOk.frame {m m' : Mem} (h : DgOk P L m₀ m) {ws : List Region} (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨dgArg P L, P.Q⟩ r) : DgOk P L m₀ m' := by
  have hQ : P.Q ≤ 72 := by anums
  unfold DgOk; rw [bytesAt_frame hf hd (by omega_arith)]; exact h

theorem DgOk.frameOf (hL : L.Ok) {m m' : Mem} (h : DgOk P L m₀ m) {ws : List Region}
    (hf : Frame ws m m') (hd : ∀ r ∈ ws, DgApart L r) : DgOk P L m₀ m' :=
  h.frame hf fun r hr => dg_apart hL (hd r hr)

theorem cnt_sub {T i : Nat} (hi : i < T) :
    BitVec.ofNat 64 (T - i) - 1 = BitVec.ofNat 64 (T - (i + 1)) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, h1]
  omega_arith

theorem cnt_ne {T i : Nat} (hT : T < 2 ^ 16) : BitVec.ofNat 64 (T - (i + 1)) ≠ 0 ↔ i + 1 < T := by
  rw [Ne, ← BitVec.toNat_inj]
  have h0 : (0 : BitVec 64).toNat = 0 := rfl
  simp only [BitVec.toNat_ofNat, h0]
  omega_arith

/-- `core`'s signature is the candidate's: it reads the private key, its
digest, and `k`, whose number is `bits2int` of the candidate. -/
theorem coreSig_eq (hL : L.Ok) (hk : HOk P L) {t : State} (hc : Ctx L g m₀ t) (hdg : DgOk P L m₀ t.mem)
    {i : Nat} (hkv : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (kArg P L) P.Q) =
      Spec.Ecdsa.Rfc6979.bits2int P.R.E.C (candI P L m₀ i)) : coreSig P L t.mem = sigI P L m₀ i := by
  have e₄ : Spec.Sha256.bytesAt t.mem L.d P.Q = Spec.Sha256.bytesAt m₀ L.d P.Q := hc.dBytes hL (by rw [hk.1])
  simp only [coreSig, coreSigOf, ecdsa_bytesAt, sigI, xOf]
  rw [show Spec.Sha256.bytesAt t.mem (dgArg P L) P.R.E.C.len = Spec.Sha256.bytesAt t.mem (dgArg P L) P.Q from rfl,
    hdg, show Spec.Sha256.bytesAt t.mem L.d P.R.E.C.len = Spec.Sha256.bytesAt t.mem L.d P.Q from rfl, e₄,
    show Spec.Sha256.bytesAt t.mem (kArg P L) P.R.E.C.len = Spec.Sha256.bytesAt t.mem (kArg P L) P.Q from rfl, hkv]

theorem ResultIs.eax_zero {r : Option (Nat × Nat)} {t : State} (h : ResultIs P L r t) :
    (t.gpr .x0).setWidth 32 = 0 ↔ r = none := by
  cases r with
  | none => exact ⟨fun _ => rfl, fun _ => h.1⟩
  | some rs => exact ⟨fun h' => by rw [h.1] at h'; exact absurd h' (by decide), fun h' => by cases h'⟩

/-- The result, kept by code that keeps `rax` and changes memory elsewhere. -/
theorem ResultIs.keep {r : Option (Nat × Nat)} {t t' : State} (h : ResultIs P L r t) (ha : t'.gpr .x0 = t.gpr .x0)
    (hm : Spec.Sha256.bytesAt t'.mem L.out (2 * P.Q) = Spec.Sha256.bytesAt t.mem L.out (2 * P.Q)) :
    ResultIs P L r t' := by
  cases r with
  | none => exact ⟨by rw [ha]; exact h.1, by rw [hm]; exact h.2⟩
  | some rs => exact ⟨by rw [ha]; exact h.1, by rw [hm]; exact h.2⟩

/-! ## One candidate -/

/-- After the candidate: `k` for `core`. -/
structure P₁ (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) (i : Nat) (u : State) : Prop where
  lt : i < P.I.tries
  k : kOf P L u.mem = (kvI P L m₀ i).1
  v : vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H (kvI P L m₀ i).1 P.nV (kvI P L m₀ i).2).2
  cnt : cnt L u.mem = BitVec.ofNat 64 (P.I.tries - i)
  fails : ∀ j < i, sigI P L m₀ j = none
  dg : DgOk P L m₀ u.mem
  kk : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u.mem (kArg P L) P.Q) =
    Spec.Ecdsa.Rfc6979.bits2int P.R.E.C (candI P L m₀ i)

/-- `core`'s arguments. -/
structure Args (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (u : State) : Prop where
  x0 : u.gpr .x0 = L.out
  x1 : u.gpr .x1 = L.d
  x2 : u.gpr .x2 = dgArg P L
  x3 : u.gpr .x3 = kArg P L
  x4 : u.gpr .x4 = L.scr

/-- After `core`: its result. -/
structure P₃ (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) (i : Nat) (u : State) : Prop where
  lt : i < P.I.tries
  k : kOf P L u.mem = (kvI P L m₀ i).1
  v : vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H (kvI P L m₀ i).1 P.nV (kvI P L m₀ i).2).2
  cnt : cnt L u.mem = BitVec.ofNat 64 (P.I.tries - i)
  fails : ∀ j < i, sigI P L m₀ j = none
  dg : DgOk P L m₀ u.mem
  res : ResultIs P L (sigI P L m₀ i) u

/-- After the decision: whether to go on. -/
structure Mid (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) (i : Nat) (u : State) : Prop where
  lt : i < P.I.tries
  k : kOf P L u.mem = (kvI P L m₀ i).1
  v : vOf P L u.mem = (Spec.Ecdsa.Rfc6979.genT P.ok.SH.H (kvI P L m₀ i).1 P.nV (kvI P L m₀ i).2).2
  cnt : cnt L u.mem = BitVec.ofNat 64 (P.I.tries - (i + 1))
  fails : ∀ j < i, sigI P L m₀ j = none
  dg : DgOk P L m₀ u.mem
  res : ResultIs P L (sigI P L m₀ i) u
  dec : isa.eval (.nonzero .x .x12) u = some (decide (sigI P L m₀ i = none ∧ i + 1 < P.I.tries))

theorem kvw_apart : ∀ r ∈ KVW L, DgApart L r := by
  simp only [KVW, List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> simp [DgApart]

theorem cw_apart : ∀ r ∈ CW L, DgApart L r := by
  simp only [CW, List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;> simp [DgApart]

theorem corew_apart : ∀ r ∈ CoreW L, DgApart L r := by
  simp only [CoreW, List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> simp [DgApart]

theorem try₁_ok (hL : L.Ok) (hk : HOk P L) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : LoopInv P L m₀ i t) :
    WP isa (cfgOf P).cand t fun u => Ctx L g m₀ u ∧ P₁ P L m₀ i u :=
  WP.mono (cand_ok hL hk.2 hc hi.saved) fun u₁ ⟨hc₁, hf₁, hk₁, hv₁, hb₁, _⟩ => ⟨hc₁, hi.lt, hk₁.trans hi.k,
    by rw [hv₁, hi.k, hi.v], (cnt_frame hf₁ (cw_cnt hL)).trans hi.cnt, hi.fails,
    hi.dg.frameOf hL hf₁ cw_apart, by rw [hb₁, hi.k, hi.v]; rfl⟩

theorem try₂_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : P₁ P L m₀ i t) :
    WP isa (.block (cfgOf P).coreArgs) t fun u => Ctx L g m₀ u ∧ P₁ P L m₀ i u ∧ Args P L u :=
  WP.mono (coreArgs_ok hL hc) fun _ ⟨hc₂, hm₂, hdi, hsi, hdx, hcx, h8⟩ =>
    ⟨hc₂, ⟨hi.lt, hm₂ ▸ hi.k, hm₂ ▸ hi.v, hm₂ ▸ hi.cnt, hi.fails, hm₂ ▸ hi.dg, hm₂ ▸ hi.kk⟩, hdi, hsi, hdx, hcx, h8⟩

theorem try₃_ok (hL : L.Ok) (hk : HOk P L) {t : State} (hc : Ctx L g m₀ t) {i : Nat}
    (hi : P₁ P L m₀ i t) (ha : Args P L t) :
    WP isa (.call (cfgOf P).coreN (cfgOf P).coreC) t fun u => Ctx L g m₀ u ∧ P₃ P L m₀ i u := by
  refine WP.mono (core_ok (P := P) hL hk.1 hc ha.x0 ha.x1 ha.x2 ha.x3 ha.x4) fun u₃ ⟨hc₃, hf₃, hr₃⟩ => ?_
  rw [coreSig_eq hL hk hc hi.dg hi.kk] at hr₃
  have he := L.he
  exact ⟨hc₃, hi.lt, (bytesAt_frame hf₃ (corew_disj hL (by anums)) (by anums)).trans hi.k,
    (bytesAt_frame hf₃ (corew_disj hL (by anums)) (by anums)).trans hi.v,
    (cnt_frame hf₃ (corew_disj hL (by anums))).trans hi.cnt, hi.fails,
    hi.dg.frameOf hL hf₃ corew_apart, hr₃⟩

theorem try₄_ok (hL : L.Ok) (hk : HOk P L) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : P₃ P L m₀ i t) :
    WP isa (.block Cfg.goOn) t fun u => Ctx L g m₀ u ∧ Mid P L m₀ i u := by
  refine WP.mono (goOn_ok hL hc) fun u₄ ⟨hc₄, hf₄, hn₄, ha₄, hz₄⟩ => ⟨hc₄, hi.lt, ?_, ?_, ?_, hi.fails,
    hi.dg.frameOf hL hf₄ (by simp [DgApart]), ?_, ?_⟩
  · exact (bytesAt_frame hf₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by anums) (by anums) (by anums))
      (by anums)).trans hi.k
  · exact (bytesAt_frame hf₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by anums) (by anums) (by anums))
      (by anums)).trans hi.v
  · rw [hn₄, hi.cnt, cnt_sub hi.lt]
  · exact hi.res.keep ha₄ (bytesAt_frame hf₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hL.stk_OUT (by anums)).symm.sub_left (Region.sub_prefix (by rw [hk.1]))) (by anums))
  · rw [hz₄, hi.cnt, cnt_sub hi.lt]
    simp only [hi.res.eax_zero, cnt_ne P.tries_lt]

/-- The branch: step h.3 and the next candidate, or the end. -/
theorem branch_ok (hL : L.Ok) (hk : HOk P L) {t : State} (hc : Ctx L g m₀ t) {i : Nat} (hi : Mid P L m₀ i t) :
    WP isa (.ite (.nonzero .x .x12) (.seq (cfgOf P).rekey (.block Cfg.again)) (.block Cfg.stop)) t fun t' => Ctx L g m₀ t' ∧
      ((isa.eval (.nonzero .x .x12) t' = some false ∧ Exit P L m₀ i t') ∨
        (isa.eval (.nonzero .x .x12) t' = some true ∧ LoopInv P L m₀ (i + 1) t')) := by
  by_cases hgo : sigI P L m₀ i = none ∧ i + 1 < P.I.tries
  · refine WP.ite true (by rw [hi.dec, decide_eq_true hgo]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine WP.seq (WP.mono (rekey_ok hL hk hc) fun u₅ ⟨hc₅, hf₅, hk₅, hv₅, hS₅⟩ => ?_)
    refine WP.mono (again_ok hL hc₅) fun u₆ ⟨hc₆, hm₆, hz₆⟩ => ⟨hc₆, .inr ⟨hz₆, ?_⟩⟩
    have hkv : kvI P L m₀ (i + 1) = stepB P.ok.SH.H P.nV (kvI P L m₀ i).1 (kvI P L m₀ i).2 := rfl
    refine ⟨hgo.2, ?_, ?_, ?_, fun j hj => ?_, ?_, by rw [hm₆]; exact hS₅⟩
    · rw [hm₆, hk₅, hi.k, hi.v, hkv]; rfl
    · rw [hm₆, hv₅, hk₅, hi.k, hi.v, hkv]; rfl
    · rw [hm₆, cnt_frame hf₅ (kvw_cnt hL), hi.cnt]
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact hi.fails j hj
      · exact hgo.1
    · rw [hm₆]; exact hi.dg.frameOf hL hf₅ kvw_apart
  · refine WP.ite false (by rw [hi.dec, decide_eq_false hgo]) (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.mono (stop_ok hL hc) fun u₅ ⟨hc₅, hm₅, hz₅, ha₅⟩ => ⟨hc₅, .inl ⟨hz₅,
      ⟨hi.lt, hi.fails, ?_, hi.res.keep ha₅ (by rw [hm₅])⟩⟩⟩
    by_cases hs : sigI P L m₀ i = none
    · exact .inr (by have := hi.lt; have : ¬ i + 1 < P.I.tries := fun h => hgo ⟨hs, h⟩; omega_arith)
    · exact .inl hs

theorem tryOne_ok (hL : L.Ok) (hk : HOk P L) {t : State} (hc : Ctx L g m₀ t) {i : Nat}
    (hi : LoopInv P L m₀ i t) :
    WP isa (cfgOf P).tryOne t fun t' => Ctx L g m₀ t' ∧
      ((isa.eval (.nonzero .x .x12) t' = some false ∧ Exit P L m₀ i t') ∨
        (isa.eval (.nonzero .x .x12) t' = some true ∧ LoopInv P L m₀ (i + 1) t')) :=
  WP.seq (WP.mono (try₁_ok hL hk hc hi) fun _ ⟨h₁, p₁⟩ =>
    WP.seq (WP.mono (try₂_ok hL h₁ p₁) fun _ ⟨h₂, p₂, a₂⟩ =>
      WP.seq (WP.mono (try₃_ok hL hk h₂ p₂ a₂) fun _ ⟨h₃, p₃⟩ =>
        WP.seq (WP.mono (try₄_ok hL hk h₃ p₃) fun _ ⟨h₄, p₄⟩ => branch_ok hL hk h₄ p₄))))

end VG.Proof.Ecdsa.Rfc6979.AArch64

end

end


/-!
# Deterministic ECDSA on AArch64: correctness

The loop leaves it at a candidate that is suitable or the last (`loop_ok`);
before it, `h`, `K`, `V`, `core`'s digest and the count are as RFC 6979's
steps a–g make them (`stageB_ok` … `stageE_ok`); and the signature of that
candidate is RFC 6979's (`result_eq`), for the hash function `P`'s instance
of the contract.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64
open VG.Proof.Ecdsa.Rfc6979 (kvAtB candAtB stepB)

variable {P : RfcHash} {L : Lay P.I.hashLen P.R.E} {g : Reg → BitVec 64} {m₀ : Mem}

/-! ## The loop -/

theorem tries_ok (hL : L.Ok) (hk : HOk P L) {t : State} (hc : Ctx L g m₀ t) (h0 : LoopInv P L m₀ 0 t) :
    WP isa (.loop (cfgOf P).tryOne (.nonzero .x .x12)) t fun t' => Ctx L g m₀ t' ∧ ∃ i, Exit P L m₀ i t' := by
  refine WP.loop (M := isa) (fun n (s : State) => Ctx L g m₀ s ∧ LoopInv P L m₀ (P.I.tries - n) s ∧ n ≤ P.I.tries)
    ?_ P.I.tries t
    ⟨hc, by rw [Nat.sub_self]; exact h0, Nat.le_refl _⟩
  rintro n s ⟨hcs, hi, hn⟩
  have hn1 : 1 ≤ n := by have := hi.lt; omega_using [this]
  refine WP.mono (tryOne_ok hL hk hcs hi) fun s' ⟨hc', h⟩ => ?_
  rcases h with ⟨he, hx⟩ | ⟨he, hx⟩
  · exact .inl ⟨he, hc', _, hx⟩
  · refine .inr ⟨he, n - 1, by omega_using [hn1], hc', ?_, by omega_using [hn]⟩
    rwa [show P.I.tries - (n - 1) = P.I.tries - n + 1 by omega_using [hn, hn1]]

/-! ## Steps a–g -/

/-- `rlen` is the scalars' `Q` bytes. -/
theorem rlen_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.rlen P.R.E.C = P.Q := by
  have := P.R.nBits_len
  exact rlenR (by show _ ≤ 8 * P.R.E.C.len; omega_using [this]) (by show 8 * P.R.E.C.len < _; omega_using [this])

/-- RFC 6979's `K` and `V` after step g, from the code's. -/
theorem kv0_eq (P : RfcHash) {x : Nat} {dB hB h : List Byte} (hd : dB.length = P.Q)
    (hx : x = Spec.Weierstrass.ofBytes dB) (hh : Spec.Ecdsa.Rfc6979.bits2octets P.R.E.C hB = h) :
    Spec.Ecdsa.Rfc6979.init P.R.E.C P.ok.SH.H P.H.D x hB =
      let K₁ := P.mac (List.replicate P.H.D 0) (List.replicate P.H.D 1 ++ [BitVec.ofNat 8 0] ++ (dB ++ h))
      let V₁ := P.mac K₁ (List.replicate P.H.D 1)
      let K₂ := P.mac K₁ (V₁ ++ [BitVec.ofNat 8 1] ++ (dB ++ h))
      (K₂, P.mac K₂ V₁) := by
  have hi : Spec.Ecdsa.Rfc6979.int2octets P.R.E.C x = dB := by
    rw [Spec.Ecdsa.Rfc6979.int2octets, rlen_eq, hx, ← hd, toBytes_ofBytes]
  simp only [Spec.Ecdsa.Rfc6979.init, hi, hh, List.append_assoc, List.singleton_append]
  rfl

/-- `h`, RFC 6979's `bits2octets` of the digest. -/
abbrev hSpec (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) : List Byte :=
  Spec.Ecdsa.Rfc6979.bits2octets P.R.E.C (hBOf P L m₀)
abbrev dB (P : RfcHash) {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (m₀ : Mem) : List Byte := Spec.Sha256.bytesAt m₀ L.d P.Q

/-- `K` and `V` after steps d and e. -/
abbrev K₁ (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) : List Byte :=
  P.mac (List.replicate P.H.D 0) (List.replicate P.H.D 1 ++ [BitVec.ofNat 8 0] ++ (dB P L m₀ ++ hSpec P L m₀))
abbrev V₁ (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) : List Byte := P.mac (K₁ P L m₀) (List.replicate P.H.D 1)

/-- After step c: `h`, `V = 0x01…`, `K = 0x00…` and `core`'s digest. -/
structure QB (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  k : kOf P L u.mem = List.replicate P.H.D 0
  v : vOf P L u.mem = List.replicate P.H.D 1
  dg : DgOk P L m₀ u.mem

/-- After step e. -/
structure QC (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  k : kOf P L u.mem = K₁ P L m₀
  v : vOf P L u.mem = V₁ P L m₀
  dg : DgOk P L m₀ u.mem
  saved : SavedK P L u.mem (kOf P L u.mem)

/-- After step g. -/
structure QD (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) (u : State) : Prop where
  k : kOf P L u.mem = (kv0 P L m₀).1
  v : vOf P L u.mem = (kv0 P L m₀).2
  dg : DgOk P L m₀ u.mem
  saved : SavedK P L u.mem (kOf P L u.mem)

theorem kv0_eq' (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) :
    kv0 P L m₀ = (P.mac (K₁ P L m₀) (V₁ P L m₀ ++ [BitVec.ofNat 8 1] ++ (dB P L m₀ ++ hSpec P L m₀)),
      P.mac (P.mac (K₁ P L m₀) (V₁ P L m₀ ++ [BitVec.ofNat 8 1] ++ (dB P L m₀ ++ hSpec P L m₀))) (V₁ P L m₀)) :=
  kv0_eq P (length_bytesAt _ _ _) rfl rfl

/-- The digest's integer is `X`'s, `Q - m` zero bytes then the digest's first
`m = min(D, Q)`, if the scalars have `8 Q` bits. -/
theorem x_eq {C : Spec.Weierstrass.Curve} {Q D : Nat} (hq : Spec.Ecdsa.nBits C = 8 * Q) (hn : C.n ≠ 0)
    {hB : List Byte} (hl : hB.length = D) :
    Spec.Weierstrass.ofBytes (List.replicate (Q - min D Q) 0 ++ hB.take (min D Q)) = Spec.Ecdsa.hashToInt C hB := by
  by_cases h : Q ≤ D
  · rw [Nat.min_eq_right h, Nat.sub_self, List.replicate_zero, List.nil_append,
      hashToInt_takeQ hq (by rw [hl]; exact h)]
  · rw [Nat.min_eq_left (by omega_using [h]), List.take_of_length_le (by rw [hl]), ofBytes_zeros,
      (hashToInt_short (by rw [hl, hq]; omega_using [h]) hn).1]

/-- After `X` and `h`: `h`, and `core`'s digest. -/
structure QA (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) (u : State) : Prop where
  h : hOf P L u.mem = hSpec P L m₀
  dg : DgOk P L m₀ u.mem

/-- After `X`: `Q - m` zero bytes, then the digest's first `m = min(D, Q)`. -/
abbrev QX (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) (u : State) : Prop :=
  Spec.Sha256.bytesAt u.mem (L.B + BitVec.ofNat 64 (16 + fX)) P.Q =
    List.replicate (P.Q - min P.H.D P.Q) 0 ++ (hBOf P L m₀).take (min P.H.D P.Q)

theorem stageX_ok (hL : L.Ok) (hk : HOk P L) {u : State} (hc : Ctx L g m₀ u) :
    WP isa (cfgOf P).prepX u fun u' => Ctx L g m₀ u' ∧ QX P L m₀ u' := by
  have hT : TabL P L := hk.2
  have hD : P.H.D = P.I.hashLen := P.len.symm
  obtain ⟨-, -, -, -, -, -, hD16, hD64, -, -, -, -, -, -, hQ8, hQ66, -, -⟩ := P.sizes
  have hdg : Spec.Sha256.bytesAt u.mem L.dg (min P.H.D P.Q) =
      (hBOf P L m₀).take (min P.H.D P.Q) := by
    rw [hc.dgBytes hL (by rw [← hD]; omega_using []), hBOf, ← bytesAt_take _ _ (Nat.min_le_left _ _)]
  exact WP.mono (prepX_ok hL hT (by rw [← hD]) hc) fun u₁ ⟨hc₁, _, hx₁⟩ => ⟨hc₁, by show Spec.Sha256.bytesAt _ _ _ = _; rw [hx₁, hdg]⟩

/-- `h` (step c's `h1` as `bits2octets`), and `core`'s digest. -/
theorem stageH_ok (hL : L.Ok) (hk : HOk P L) {u₁ : State} (hc₁ : Ctx L g m₀ u₁) (hx₁ : QX P L m₀ u₁) :
    WP isa (cfgOf P).prepH u₁ fun u' => Ctx L g m₀ u' ∧ QA P L m₀ u' := by
  have hT : TabL P L := hk.2
  have hD : P.H.D = P.I.hashLen := P.len.symm
  have hl := P.R.nBits_len
  obtain ⟨-, -, -, -, -, -, hD16, hD64, -, -, -, -, -, -, hQ8, hQ66, -, -⟩ := P.sizes
  have hlB : (hBOf P L m₀).length = P.H.D := length_bytesAt _ _ _
  unfold QX at hx₁
  cases hb : P.R.big
  · have hq : Spec.Ecdsa.nBits P.R.E.C = 8 * P.Q := (P.R.sizesA hb).2.2.1
    have hX : Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt u₁.mem (xa L) P.Q) = eOf P L m₀ := by
      rw [show xa L = L.B + BitVec.ofNat 64 (16 + fX) from rfl, hx₁, x_eq hq P.R.n_ne hlB]
    rw [show (cfgOf P).prepH = .block (cfgOf P).reduce by simp only [Cfg.prepH, show (cfgOf P).big = false from hb,
      Bool.false_eq_true, ite_false]]
    refine WP.mono (reduce_ok hb hL hc₁) fun u₂ ⟨hc₂, hf₂, hh₂⟩ => ⟨hc₂, ?_, ?_⟩
    · show Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 (16 + (cfgOf P).fHo)) P.Q = _
      rw [show (cfgOf P).fHo = fH by simp only [Cfg.fHo, show (cfgOf P).big = false from hb, Bool.false_eq_true,
        ite_false], show 16 + fH = hB from rfl, hh₂, hX, hSpec, Spec.Ecdsa.Rfc6979.bits2octets,
        Spec.Ecdsa.Rfc6979.int2octets, Spec.Ecdsa.Rfc6979.bits2int, rlen_eq]
    · unfold DgOk
      simp only [dgArg, hb, Bool.false_eq_true, ite_false]
      obtain ⟨-, -, hQ64⟩ := P.sizesA hb
      obtain ⟨-, hb₂, -, -, -, -, hb₇⟩ := hb_facts (L := L) hb
      simp only [fX] at hb₇
      rw [bytesAt_frame hf₂ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact Offset.disjoint _ (.inr (by simp only [fX]; omega_using [])) (by simp only [fX]; omega_using [hQ66]) (by omega_using [])
          · exact Offset.disjoint _ (.inr (by simp only [fX]; omega_using [hb₂, hb₇])) (by simp only [fX]; omega_using [hQ66])
              (by omega_using [hb₂, hb₇])) (by omega_using [hQ66]),
        hashToInt_takeQ hq (by rw [length_bytesAt]), List.take_of_length_le (by rw [length_bytesAt])]
      exact hX
  · obtain ⟨-, hQ66', hQD⟩ := P.sizesW hb
    have hN : 8 * P.H.D < Spec.Ecdsa.nBits P.R.E.C := by
      have : P.H.D < P.R.E.C.len := hQD
      omega_using [hl, this]
    have hm : min P.H.D P.Q = P.H.D := Nat.min_eq_left (by omega_using [hD64, hQ66'])
    rw [hm, List.take_of_length_le (by rw [hlB])] at hx₁
    rw [show (cfgOf P).prepH = (cfgOf P).prepC by simp only [Cfg.prepH, show (cfgOf P).big = true from hb, ite_true]]
    refine WP.mono (prepC_ok hL hT hb (by rw [← hD]) hc₁) fun u₂ ⟨hc₂, hf₂, hx₂⟩ => ⟨hc₂, ?_, ?_⟩
    · show Spec.Sha256.bytesAt u₂.mem (L.B + BitVec.ofNat 64 (16 + (cfgOf P).fHo)) P.Q = _
      rw [show (cfgOf P).fHo = fX by simp only [Cfg.fHo, show (cfgOf P).big = true from hb, ite_true],
        bytesAt_frame hf₂ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hL.stk_scr (by have := L.he; simp only [fX]; omega_using [hQ66, this]) (by decide)
          · exact Offset.disjoint _ (.inl (by simp only [fX, fXc]; omega_using [hQ66])) (by simp only [fX]; omega_using [hQ66])
              (by simp only [fXc]; omega_using [])) (by omega_using [hQ66]),
        hx₁, hSpec, bits2octets_short (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega_using [hl])
          (by show 8 * P.R.E.C.len < _; omega_using [hl]) (by rw [hlB]; exact hN) P.R.n_ne, hlB]
    · -- `core`'s digest: the digest's number `e`, shifted left by `sh` bits.
      have e₂ : eOf P L m₀ = Spec.Weierstrass.ofBytes (hBOf P L m₀) :=
        (hashToInt_short (by rw [hlB]; exact hN) P.R.n_ne).1
      rw [hc₁.dgBytes hL (by rw [← hD])] at hx₂
      have hlt : Spec.Weierstrass.ofBytes (hBOf P L m₀) * 2 ^ P.R.sh < 2 ^ (8 * P.Q) := by
        have := Rfc6979.ofBytes_lt (hBOf P L m₀)
        rw [hlB] at this
        calc _ < 2 ^ (8 * P.H.D) * 2 ^ P.R.sh := Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos _)
          _ ≤ 2 ^ (8 * P.Q) := by
            rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by omega_using []) (by simp only [RfcHash.Q]; omega_using [hl, hN])
      have hl₁ : (Spec.Weierstrass.toBytes P.Q (Spec.Weierstrass.ofBytes (hBOf P L m₀) * 2 ^ P.R.sh)).length = P.Q := by
        simp [Spec.Weierstrass.toBytes]
      unfold DgOk
      simp only [dgArg, hb, ite_true]
      rw [hx₂, hashToInt_takeR (R := P.Q) (by show _ ≤ 8 * P.R.E.C.len; omega_using [hl]) (by rw [hl₁]),
        List.take_of_length_le (by rw [hl₁]), Rfc6979.ofBytes_toBytes _ _ hlt,
        show 8 * P.Q - Spec.Ecdsa.nBits P.R.E.C = P.R.sh from hl.2.2.symm, Nat.shiftRight_eq_div_pow,
        Nat.mul_div_cancel _ (Nat.two_pow_pos _), e₂]

/-- `h` in the message, kept by the steps on `K` and `V`. -/
theorem hOf_frame (hL : L.Ok) {ws : List Region} {m m' : Mem} (hf : Frame ws m m')
    (hd : ∀ r ∈ ws, r = L.SCR ∨ r = ⟨L.B, 144⟩ ∨ ∃ o n, r = ⟨L.B + BitVec.ofNat 64 o, n⟩ ∧ o + n ≤ 16 + fH) :
    hOf P L m' = hOf P L m := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hQ66, -, -⟩ := P.sizes
  have he := L.he
  have hho : 16 + fH ≤ 16 + (cfgOf P).fHo ∧ 16 + (cfgOf P).fHo + P.Q ≤ 16 + fXc := by
    simp only [Cfg.fHo]; split <;> simp only [fH, fX, fXc] <;> omega_using [hQ66]
  refine bytesAt_frame hf (fun r hr => ?_) (by omega_using [hQ66])
  rcases hd r hr with rfl | rfl | ⟨o, n, rfl, hon⟩
  · exact hL.stk_SCR (by simp only [fXc] at hho; omega_using [he, hho])
  · exact Offset.disjoint_base _ (by simp only [fH] at hho; omega_using [hho]) (by simp only [fXc] at hho; omega_using [hho])
  · exact Offset.disjoint _ (.inr (by omega_using [hho, hon])) (by simp only [fXc] at hho; omega_using [hho]) (by simp only [fH] at hon; omega_using [hon])

theorem hOf_kvw (hL : L.Ok) {m m' : Mem} (hf : Frame (KVW L) m m') : hOf P L m' = hOf P L m :=
  hOf_frame hL hf fun r hr => by
    simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl rfl)

/-- `V = 0x01…` and `K = 0x00…`. -/
theorem stageB_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hq : QA P L m₀ u) :
    WP isa (.block Cfg.initKV) u fun u' => Ctx L g m₀ u' ∧ QB P L m₀ u' := by
  obtain ⟨-, -, -, -, -, -, -, hD64, -, -, -, -, -, -, -, -, -, -⟩ := P.sizes
  exact WP.mono (initKV_ok hL hc) fun u₂ ⟨hc₂, hf₂, hv₂, hk₂⟩ =>
    ⟨hc₂, ⟨(hOf_frame hL hf₂ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact .inr (.inr ⟨16, 128, rfl, by simp only [fH]; omega_using []⟩)).trans hq.h,
      hk₂ _ hD64, hv₂ _ hD64, hq.dg.frameOf hL hf₂ (by simp [DgApart])⟩⟩

theorem stageC_ok (hL : L.Ok) (hk : HOk P L) {u : State} (hc : Ctx L g m₀ u) (hq : QB P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 0) u fun u' => Ctx L g m₀ u' ∧ QC P L m₀ u' :=
  WP.mono (rekeyFull_ok hL hk hc 0 fun h => absurd rfl h) fun u' ⟨hc', hf', hk', hv', hS'⟩ =>
    ⟨(hOf_kvw hL hf').trans hq.h,
      by rw [hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])],
      by rw [hv', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])], hq.dg.frameOf hL hf' kvw_apart, hS'⟩ |>
    fun h => ⟨hc', h⟩

theorem stageD_ok (hL : L.Ok) (hk : HOk P L) {u : State} (hc : Ctx L g m₀ u) (hq : QC P L m₀ u) :
    WP isa ((cfgOf P).rekeyFull 1) u fun u' => Ctx L g m₀ u' ∧ QD P L m₀ u' :=
  WP.mono (rekeyFull_ok hL hk hc 1 fun _ => hq.saved) fun u' ⟨hc', hf', hk', hv', hS'⟩ =>
    ⟨hc', by rw [kv0_eq', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])],
      by rw [kv0_eq', hv', hk', hq.k, hq.v, hq.h, hc.dBytes hL (by rw [hk.1])], hq.dg.frameOf hL hf' kvw_apart, hS'⟩

theorem stageE_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) (hq : QD P L m₀ u) :
    WP isa (.block (cfgOf P).initCnt) u fun u' => Ctx L g m₀ u' ∧ LoopInv P L m₀ 0 u' :=
  WP.mono (initCnt_ok hL hc) fun u' ⟨hc', hf', hn'⟩ => ⟨hc', P.tries_pos,
    (bytesAt_frame hf' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by anums) (by anums) (by anums))
      (by anums)).trans hq.k,
    (bytesAt_frame hf' (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by anums) (by anums) (by anums))
      (by anums)).trans hq.v,
    by rw [hn', Nat.sub_zero], fun j hj => absurd hj (Nat.not_lt_zero _), hq.dg.frameOf hL hf' (by simp [DgApart]),
    by
      have hk' : kOf P L u'.mem = kOf P L u.mem := bytesAt_frame hf' (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by anums) (by anums) (by anums)) (by anums)
      rw [hk']
      exact hq.saved.frame hf' fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (hL.stk_scr (by anums) (by anums)).symm⟩

theorem stageG_ok (hL : L.Ok) (hk : HOk P L) {u : State} (hc : Ctx L g m₀ u) {i : Nat}
    (hx : Exit P L m₀ i u) :
    WP isa (.block Cfg.wipe) u fun u' => Ctx L g m₀ u' ∧ Exit P L m₀ i u' :=
  WP.mono (wipe_ok hL hc) fun _ ⟨hc₇, ha₇, hf₇⟩ => ⟨hc₇, hx.lt, hx.fails, hx.last,
    hx.res.keep ha₇ (bytesAt_frame hf₇ (fun r hr => by
      have := L.he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hL.stk_OUT (by omega_using [])).symm.sub_left (Region.sub_prefix (by rw [hk.1]))
      · exact (hL.stk_OUT (d := 248) (n := 8 * L.e - 16) (by omega_using [])).symm.sub_left
          (Region.sub_prefix (by rw [hk.1]))) (by anums))⟩

/-- The frame's body after the pointers' stores. -/
theorem rest_ok (hL : L.Ok) (hk : HOk P L) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.seq (cfgOf P).prepX (.seq (cfgOf P).prepH (.seq (.block Cfg.initKV) (.seq ((cfgOf P).rekeyFull 0)
      (.seq ((cfgOf P).rekeyFull 1) (.seq (.block (cfgOf P).initCnt)
        (.seq (.loop (cfgOf P).tryOne (.nonzero .x .x12)) (.block Cfg.wipe)))))))) t
      fun t' => Ctx L g m₀ t' ∧ ∃ i, Exit P L m₀ i t' :=
  WP.seq (WP.mono (stageX_ok hL hk hc) fun _ ⟨h₀, q₀⟩ =>
    WP.seq (WP.mono (stageH_ok hL hk h₀ q₀) fun _ ⟨h₁, q₁⟩ =>
    WP.seq (WP.mono (stageB_ok hL h₁ q₁) fun _ ⟨h₂, q₂⟩ =>
      WP.seq (WP.mono (stageC_ok hL hk h₂ q₂) fun _ ⟨h₃, q₃⟩ =>
        WP.seq (WP.mono (stageD_ok hL hk h₃ q₃) fun _ ⟨h₄, q₄⟩ =>
          WP.seq (WP.mono (stageE_ok hL h₄ q₄) fun _ ⟨h₅, q₅⟩ =>
            WP.seq (WP.mono (tries_ok hL hk h₅ q₅) fun _ ⟨h₆, i, q₆⟩ =>
              WP.mono (stageG_ok hL hk h₆ q₆) fun _ ⟨h₇, q₇⟩ => ⟨h₇, i, q₇⟩)))))))

/-! ## RFC 6979's result -/

/-- RFC 6979's number of blocks is the candidates' `V`s. -/
theorem blocks_eq (P : RfcHash) : Spec.Ecdsa.Rfc6979.blocks P.R.E.C P.H.D = P.nV := nV_eq P

/-- The instance's signature and number of candidates, as the proof names its parts. -/
theorem result_unfold :
    result P.I m₀ L.d L.dg =
      if 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n then
        let (K, V) := kv0 P L m₀
        Spec.Ecdsa.Rfc6979.search P.R.E.C P.ok.SH.H P.H.D (xOf P L m₀) (eOf P L m₀) K V P.I.tries
      else (none, 0) := by
  simp only [result, Proof.Ecdsa.Rfc6979.Instance.result, P.ecdsa, P.R.curve, P.hash, P.len,
    ecdsa_bytesAt, Spec.Ecdsa.Rfc6979.sign]

/-- The signature of the candidate the loop stopped at is RFC 6979's. -/
theorem result_eq {i : Nat} {t : State} (hx : Exit P L m₀ i t) :
    (result P.I m₀ L.d L.dg).1 = sigI P L m₀ i := by
  rw [result_unfold]
  by_cases hv : 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n
  · simp only [hv, and_self, ite_true]
    rw [Proof.Ecdsa.Rfc6979.searchB_shift (blocks_eq P) i P.I.tries (by have := hx.lt; omega_using [this]) hx.fails,
      show P.I.tries - i = (P.I.tries - 1 - i) + 1 by have := hx.lt; omega_using [this]]
    cases hs : sigI P L m₀ i with
    | some rs => rw [Proof.Ecdsa.Rfc6979.searchB_ok (blocks_eq P) hs]
    | none =>
      have h7 : i + 1 = P.I.tries := hx.last.resolve_left (by simp [hs])
      rw [Proof.Ecdsa.Rfc6979.searchB_fail (blocks_eq P) hs, show P.I.tries - 1 - i = 0 by omega_using [h7]]
      rfl
  · symm
    simp only [hv, ite_false, sigI, Spec.Ecdsa.signWith]
    split
    · rename_i h; exact absurd ⟨h.1, h.2.1⟩ hv
    · rfl

/-! ## How many candidates -/

theorem ite_le_of_not {c : Prop} [Decidable c] {a b i : Nat} (hc : ¬c) (hb : b ≤ i) :
    (if c then a else b) ≤ i := by
  simp only [hc, ite_false]; exact hb

/-- The candidate the loop stops at, from the number RFC 6979 tries. -/
def exitAt (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) : Nat :=
  if (result P.I m₀ L.d L.dg).2 = 0 then P.I.tries - 1 else (result P.I m₀ L.d L.dg).2 - 1

/-- The loop goes on after candidate `i` iff it stops at a later one. -/
theorem go_iff {i : Nat} (hi : i < P.I.tries) (hf : ∀ j < i, sigI P L m₀ j = none) :
    (sigI P L m₀ i = none ∧ i + 1 < P.I.tries) ↔ i < exitAt P L m₀ := by
  unfold exitAt
  rw [result_unfold]
  by_cases hv : 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n
  · simp only [hv, and_self, ite_true]
    rw [Proof.Ecdsa.Rfc6979.searchB_shift (blocks_eq P) i P.I.tries (by omega_using [hi]) hf,
      show P.I.tries - i = (P.I.tries - 1 - i) + 1 by omega_using [hi]]
    cases hs : sigI P L m₀ i with
    | some rs =>
      rw [Proof.Ecdsa.Rfc6979.searchB_ok (blocks_eq P) hs]
      simp
    | none =>
      rw [Proof.Ecdsa.Rfc6979.searchB_fail (blocks_eq P) hs]
      by_cases h7 : i + 1 < P.I.tries
      · have := Proof.Ecdsa.Rfc6979.searchB_pos (C := P.R.E.C) (H := P.ok.SH.H) (hlen := P.H.D)
          (d := xOf P L m₀) (e := eOf P L m₀) (n := P.I.tries - 2 - i)
          (K := (stepB P.ok.SH.H P.nV (kvI P L m₀ i).1 (kvI P L m₀ i).2).1)
          (V := (stepB P.ok.SH.H P.nV (kvI P L m₀ i).1 (kvI P L m₀ i).2).2) (blocks_eq P)
        rw [show P.I.tries - 1 - i = P.I.tries - 2 - i + 1 by omega_using [h7]]
        simp only [true_and, h7]
        simp only [kvI] at this
        rw [true_iff]
        split <;> omega_arith
      · rw [show P.I.tries - 1 - i = 0 by omega_using [h7]]
        simp only [Spec.Ecdsa.Rfc6979.search, h7, and_false, false_iff, Nat.not_lt]
        exact ite_le_of_not (by omega_using []) (by omega_using [])
  · simp only [hv, ite_false, ite_true]
    have hs : sigI P L m₀ i = none := by
      simp only [sigI, Spec.Ecdsa.signWith]
      split
      · rename_i h; exact absurd ⟨h.1, h.2.1⟩ hv
      · rfl
    simp only [hs, true_and]
    omega_using []

/-! ## The whole function -/

/-- The contract the code for `P`'s hash function is proven against, after
the entry, with `P`'s table and the functions `ns`' addresses public. -/
abbrev rfcP (P : RfcHash) (ns : List String) : Contract isa :=
  rfcAArch64 P.R.E P.I (256 + 8 * 48) (tabFacts P.H P.f) ns

/-- The layout of a call from `s`. -/
abbrev layOf (P : RfcHash) (s : State) : Lay P.I.hashLen P.R.E :=
  lay P.I.hashLen P.I.ecdsa.curve.len P.R.E 48 rfl P.H P.f s

theorem hOk_lay (P : RfcHash) (s : State) : HOk P (layOf P s) := ⟨P.curveLen, rfl, rfl⟩

/-- `sign` for `P`'s hash function meets `rfcP P` and keeps the callee-saved
registers and the stack pointer. -/
theorem sign_ok {ns : List String} {s : State} (h : (rfcP P ns).pre s) :
    WP isa (cfgOf P).sign s fun s' => ((∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp) ∧
      (rfcP P ns).post s s' := by
  have hL := lay_ok rfl h
  have hN : 256 + 8 * 48 ≤ s.sp.toNat := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hk := hOk_lay P s
  refine WP.frameAlloc (by omega_arith) (by decide) ?_ ?_
  · show frameBytes ≤ (s.sp - 16).toNat
    rw [BitVec.toNat_sub_of_le (by show 16 ≤ s.sp.toNat; omega_arith)]
    show 608 ≤ s.sp.toNat - 16
    omega_arith
  · show WP isa (cfgOf P).body (entered s) _
    rw [Cfg.body]
    refine WP.seq (WP.mono (save_ctx h) fun t hc => ?_)
    refine WP.mono (rest_ok hL hk hc) fun u ⟨hu, i, hx⟩ mm uu fl => ?_
    have lr : u.mem.read (u.sp + BitVec.ofNat 64 frameBytes) 8 = s.gpr .x30 := by
      rw [hu.sp, Offset.add_add, read8]; exact hu.lr
    refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
    · show (popped .x30 (freed frameBytes u)).gpr r = s.gpr r
      simp only [popped, freed, RegUpd.gpr_write]
      rw [lr]
      by_cases h30 : r = .x30
      · subst r; simp only [ite_true, BitVec.setWidth_eq]
      · simp only [h30, ite_false]
        exact hu.cs r hr h30
    · show (popped .x30 (freed frameBytes u)).sp = s.sp
      simp only [popped, freed]
      rw [hu.sp, Offset.add_add, show (16 : BitVec 64) = BitVec.ofNat 64 16 from rfl, Offset.add_add,
        show 16 + frameBytes + 16 = 256 + 8 * 48 from rfl]
      exact lay_top _ _ _ _ _ _ _ s
    · show match (result P.I s.mem (layOf P s).d (layOf P s).dg).1 with
        | some rs => _ | none => _
      have e₁ : 2 * P.I.ecdsa.curve.len = 2 * P.Q := by rw [P.curveLen]
      have e₂ : Spec.Ecdsa.encode P.I.ecdsa.curve = Spec.Ecdsa.encode P.R.E.C := by rw [P.ecdsa, P.R.curve]
      rw [result_eq hx, e₁, e₂]
      -- The output lies apart from the stack, whose frames' bytes are lost.
      have hS : Region.Sub (below s.sp (frameBytes + 16)) (layOf P s).STK :=
        Offset.sub_below s.sp (a := frameBytes + 16) (n := frameBytes + 16) (b := 256 + 8 * 48)
          (m := 256 + 8 * 48) (by decide) (by decide)
      exact hx.res.keep (by
        show (popped .x30 (freed frameBytes u)).gpr .x0 = _
        simp only [popped, freed]
        exact RegUpd.gpr_write_of_ne _ _ _ (by decide))
        (List.map_congr_left fun i hi => lost_byte (R := (layOf P s).OUT) fl (hL.ko.symm.sub_right hS)
          (show i < 2 * (layOf P s).q by rw [hk.1]; exact List.mem_range.mp hi))

end VG.Proof.Ecdsa.Rfc6979.AArch64

end

end

/-!
# Deterministic ECDSA on AArch64: constant time, up to the number of candidates

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Table.lean`): two runs whose public
data agree have the same layout, and stop at the same candidate (`exitAt`,
from the contract's leakage: the number of candidates RFC 6979 tries).
Between the frames' pushes and pops they are related by `Two`: both satisfy
`Ctx` with that layout (and `Φ`, what the next piece needs). The blocks
address only the stack and the buffers, from registers that agree (the
taint analysis, of the blocks whose contents depend on the curve: `RfcT`,
each curve's `RfcCurve.blk`), or, for the byte loops, from registers both
runs set alike (`T`'s length, `D`); an indirect call reaches, through the
table, whose address the frame holds, the same function in both runs
(`tcall_piece`); each call is of constant-time code whose public data agree
(`RelCT.callEx`); and the loops' branches agree: the candidate's, since both
runs' `T` grows by `D` bytes a block, and the candidates', since in both
runs it goes on after candidate `i` iff `i` is before the candidate it stops
at (`go_iff`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64
open VG.Proof.RsaOaep.AArch64 (eval_nonzero)

/-- What each of two runs has, between the frames' pushes and pops. -/
abbrev Env (P : RfcHash) := Lay P.I.hashLen P.R.E × (Reg → BitVec 64) × (Reg → BitVec 64) × Mem × Mem

/-- Two runs with the same layout that stop at the same candidate, each
satisfying `Ctx` and `Φ`. -/
def Two (P : RfcHash) (Φ : Lay P.I.hashLen P.R.E → Mem → State → Prop) (a b : State) : Prop :=
  ∃ e : Env P, e.1.Ok ∧ HOk P e.1 ∧ exitAt P e.1 e.2.2.2.1 = exitAt P e.1 e.2.2.2.2 ∧ Ctx e.1 e.2.1 e.2.2.2.1 a ∧
    Ctx e.1 e.2.2.1 e.2.2.2.2 b ∧ Φ e.1 e.2.2.2.1 a ∧ Φ e.1 e.2.2.2.2 b

variable {P : RfcHash}

theorem Two.mono {Φ Ψ : Lay P.I.hashLen P.R.E → Mem → State → Prop} (h : ∀ L m₀ t, Φ L m₀ t → Ψ L m₀ t)
    {a b : State} (ht : Two P Φ a b) : Two P Ψ a b :=
  let ⟨e, hL, hq, hx, c₁, c₂, f₁, f₂⟩ := ht
  ⟨e, hL, hq, hx, c₁, c₂, h _ _ _ f₁, h _ _ _ f₂⟩

/-- Code whose runs leak the same, and which keeps `Ctx` and establishes `Ψ`. -/
theorem two_wp {c : Prog isa} {Φ Ψ : Lay P.I.hashLen P.R.E → Mem → State → Prop}
    (hct : RelCT isa (Two P Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay P.I.hashLen P.R.E) g m₀ (t : State), L.Ok → HOk P L → Ctx L g m₀ t → Φ L m₀ t →
      WP isa c t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t') :
    RelCT isa (Two P Φ) c (Two P Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨⟨L, g₁, g₂, m₁, m₂⟩, hL, hq, hx, c₁, c₂, f₁, f₂⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw L g₁ m₁ s₁ hL hq c₁ f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw L g₂ m₂ s₂ hL hq c₂ f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, ⟨L, g₁, g₂, m₁, m₂⟩, hL, hq, hx, y₁.1, y₂.1, y₁.2, y₂.2⟩

theorem sp_two {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 64}
    {m₁ m₂ : Mem} (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) : t₁.sp = t₂.sp :=
  c₁.sp.trans c₂.sp.symm

/-- Code whose addresses depend only on `sp` and the registers `rs`, which agree. -/
theorem two_prog {c : Prog isa} {Φ : Lay P.I.hashLen P.R.E → Mem → State → Prop} (rs : List Reg)
    (hrs : ∀ (L : Lay P.I.hashLen P.R.E) (t₁ t₂ : State) g₁ g₂ m₁ m₂, Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ →
      Φ L m₁ t₁ → Φ L m₂ t₂ → ∀ r ∈ rs, t₁.gpr r = t₂.gpr r)
    (h : ∃ hc, (taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa (Two P Φ) c fun _ _ => True :=
  let ⟨_, h⟩ := h
  RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun _ _ ⟨_, _, _, _, c₁, c₂, f₁, f₂⟩ => ⟨sp_two c₁ c₂, fun r hr =>
      hrs _ _ _ _ _ _ _ c₁ c₂ f₁ f₂ r (Taint.mem_ofRegs.mp hr)⟩) h

/-- A block whose addresses depend only on `sp` and the registers `rs`, which agree. -/
theorem two_blk {is : List Instr} {Φ : Lay P.I.hashLen P.R.E → Mem → State → Prop} (rs : List Reg)
    (hrs : ∀ (L : Lay P.I.hashLen P.R.E) (t₁ t₂ : State) g₁ g₂ m₁ m₂, Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ →
      Φ L m₁ t₁ → Φ L m₂ t₂ → ∀ r ∈ rs, t₁.gpr r = t₂.gpr r)
    (h : TaintOk rs is) : RelCT isa (Two P Φ) (.block is) fun _ _ => True :=
  two_prog rs hrs h

theorem spOnly {Φ : Lay P.I.hashLen P.R.E → Mem → State → Prop} :
    ∀ (L : Lay P.I.hashLen P.R.E) (t₁ t₂ : State) g₁ g₂ m₁ m₂,
      Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ → Φ L m₁ t₁ → Φ L m₂ t₂ → ∀ r ∈ ([] : List Reg), t₁.gpr r = t₂.gpr r :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hr => absurd hr List.not_mem_nil

/-- The taint check of a block is that of the block with the immediates of
its `movz`s zeroed (`Taint.check_eraseImm`). -/
theorem taintOk_erase {rs : List Reg} {is is₀ : List Instr} (h : TaintOk rs is₀)
    (he : is.map Instr.eraseImm = is₀) : TaintOk rs is := by
  obtain ⟨hc, hs⟩ := h
  exact ⟨hc, Taint.isSome_check_of_eraseImm (c := .block is) (by simp only [Code.eraseImm, he]) hs⟩

/-! ## Pieces: related in two runs, and keeping `Ctx` in each -/

/-- What one run's piece needs and gives. -/
abbrev Pr (P : RfcHash) := Lay P.I.hashLen P.R.E → Mem → State → Prop

/-- Nothing. -/
abbrev Tt (P : RfcHash) : Pr P := fun _ _ _ => True

/-- Code that, from `Φ`, leaks the same in two runs and gives `Ψ`, keeping
`Ctx`, in each. -/
structure Piece (P : RfcHash) (Φ : Pr P) (c : Prog isa) (Ψ : Pr P) : Prop where
  ct : RelCT isa (Two P Φ) c (Two P Ψ)
  wp : ∀ (L : Lay P.I.hashLen P.R.E) g m₀ (t : State), L.Ok → HOk P L → Ctx L g m₀ t → Φ L m₀ t →
    WP isa c t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t'

namespace Piece

variable {Φ Ψ Χ : Pr P} {a b c : Prog isa}

theorem of (hct : RelCT isa (Two P Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay P.I.hashLen P.R.E) g m₀ (t : State), L.Ok → HOk P L → Ctx L g m₀ t → Φ L m₀ t →
      WP isa c t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t') : Piece P Φ c Ψ :=
  ⟨two_wp hct hw, hw⟩

theorem seq (h₁ : Piece P Φ a Ψ) (h₂ : Piece P Ψ b Χ) : Piece P Φ (.seq a b) Χ :=
  ⟨h₁.ct.seq h₂.ct, fun L g m₀ t hL hk hc hφ =>
    WP.seq (WP.mono (h₁.wp L g m₀ t hL hk hc hφ) fun _ ⟨c', ψ⟩ => h₂.wp L g m₀ _ hL hk c' ψ)⟩

/-- What the relational proofs of the loop use. -/
theorem rel (h : Piece P Φ c Ψ) {Φ' : Pr P} (hp : ∀ L m₀ t, Φ' L m₀ t → Φ L m₀ t) :
    RelCT isa (Two P Φ') c fun _ _ => True :=
  h.ct.mono (fun _ _ => Two.mono hp) fun _ _ _ => trivial

end Piece

/-- A block whose addresses depend only on `sp` and the registers `rs`, which agree. -/
theorem Piece.blk {is : List Instr} {Φ Ψ : Pr P} (rs : List Reg)
    (hrs : ∀ (L : Lay P.I.hashLen P.R.E) (t₁ t₂ : State) g₁ g₂ m₁ m₂, Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ →
      Φ L m₁ t₁ → Φ L m₂ t₂ → ∀ r ∈ rs, t₁.gpr r = t₂.gpr r)
    (ht : TaintOk rs is)
    (hw : ∀ (L : Lay P.I.hashLen P.R.E) g m₀ (t : State), L.Ok → HOk P L → Ctx L g m₀ t → Φ L m₀ t →
      WP isa (.block is) t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t') : Piece P Φ (.block is) Ψ :=
  Piece.of (two_blk rs hrs ht) hw

/-- A block whose addresses depend only on `sp`. -/
theorem Piece.blkS {is : List Instr} {Φ Ψ : Pr P} (ht : TaintOk [] is)
    (hw : ∀ (L : Lay P.I.hashLen P.R.E) g m₀ (t : State), L.Ok → HOk P L → Ctx L g m₀ t → Φ L m₀ t →
      WP isa (.block is) t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t') : Piece P Φ (.block is) Ψ :=
  Piece.blk [] spOnly ht hw

/-- The blocks of the curve. -/
theorem rT (P : RfcHash) : RfcT (cfgC P.R.E P.R.big P.R.sh) := P.R.blk

/-! ## The indirect calls -/

variable {L : Lay P.I.hashLen P.R.E} {g : Reg → BitVec 64} {m₀ : Mem}

/-- The table's word `j`, to `x16` from the table's address in it. -/
theorem ldTab_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (h16 : t.gpr .x16 = L.tab) {j : Nat}
    (hj : 8 * j + 8 ≤ 48) :
    WP isa (.block [.ldr .x .x16 .x16 (8 * j)]) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .x16 = m₀.readW (L.tab + BitVec.ofNat 64 (8 * j)) 64 ∧ (∀ r, r ≠ .x16 → t'.gpr r = t.gpr r) ∧
      t'.syms = t.syms := by
  have ht := hc.inTab hL (o := 8 * j) hj
  have hj' : 8 * j < 32768 := by omega_using [hj]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, Nat.mul_mod_right, hj', and_self,
    ite_true, Option.bind_some, State.load, Size.bits, BitVec.setWidth_eq, h16, ht, Option.map_some,
    read8, hc.tab_word hL hj, Option.some.injEq, exists_eq_left']
  exact ⟨hc.set hL (d := .x16) (by decide) rfl rfl rfl rfl (fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr) rfl,
    rfl, by rw [RegUpd.gpr_write_self]; exact BitVec.setWidth_eq _, fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr,
    rfl⟩

/-- What an indirect call of `n` needs of the table in each run: its word
`j` (on entry) is `n`'s address, which is the layout's, and of `ts` an
indirect call reaches `n`'s `c`. -/
def TabFn (P : RfcHash) (j : Nat) (n : String) (c : Prog isa) (ts : List (String × Prog isa)) : Prop :=
  ∀ (L : Lay P.I.hashLen P.R.E) g m₀ (t : State), L.Ok → HOk P L → Ctx L g m₀ t →
    m₀.readW (L.tab + BitVec.ofNat 64 (8 * j)) 64 = t.syms n ∧
      ts.find? (fun q => t.syms q.1 == t.syms n) = some (n, c) ∧ t.syms n = L.fa n

theorem tfn_init : TabFn P 0 P.H.hmacInitN P.H.hmacInit P.f.init := fun L _ _ _ _ hk hc => by
  have hok := hc.tabOk; have htm := hc.tabMem; have hf := hc.fsy
  rw [hk.2.1, hk.2.2] at hok; rw [hk.2.1] at htm hf
  exact ⟨htm.1, hok.i, hf _ (by simp)⟩

theorem tfn_upd : TabFn P 1 P.H.updN P.H.updC P.f.upd := fun L _ _ _ _ hk hc => by
  have hok := hc.tabOk; have htm := hc.tabMem; have hf := hc.fsy
  rw [hk.2.1, hk.2.2] at hok; rw [hk.2.1] at htm hf
  exact ⟨htm.2.1, hok.u, hf _ (by simp)⟩

theorem tfn_fin : TabFn P 2 P.H.hmacFinN P.H.hmacFin P.f.fin := fun L _ _ _ _ hk hc => by
  have hok := hc.tabOk; have htm := hc.tabMem; have hf := hc.fsy
  rw [hk.2.1, hk.2.2] at hok; rw [hk.2.1] at htm hf
  exact ⟨htm.2.2, hok.f, hf _ (by simp)⟩

/-- What only `x16` changing keeps. -/
def R16 (Φ : Pr P) : Prop :=
  ∀ L m₀ (t u : State), Φ L m₀ t → (∀ r, r ≠ .x16 → u.gpr r = t.gpr r) → u.mem = t.mem → u.syms = t.syms →
    Φ L m₀ u

theorem tblk1_taint : TaintOk [] [.ldrSp .x16 fTab] := ⟨_, by taint_decide⟩

/-- The indirect call of the table's function `j`: in both runs of the same
function, `n`'s (the table's word `j` holds the layout's address of `n`). -/
theorem tcall_piece {Φ Ψ : Pr P} {j : Nat} (hj : 8 * j + 8 ≤ 48) {n : String} {c : Prog isa}
    {ts : List (String × Prog isa)} (hn : TabFn P j n c ts) (hΦ : R16 Φ)
    (ht : TaintOk [.x16] [.ldr .x .x16 .x16 (8 * j)]) (hcall : Piece P Φ (.call n c) Ψ) :
    Piece P Φ (Cfg.tcall j ts) Ψ := by
  refine ⟨?_, fun L g m₀ t hL hk hc hφ => ?_⟩
  · unfold Cfg.tcall
    rw [show ([.ldrSp .x16 fTab, .ldr .x .x16 .x16 (8 * j)] : List Instr) =
      [.ldrSp .x16 fTab] ++ [.ldr .x .x16 .x16 (8 * j)] from rfl]
    have s₁ : Piece P Φ (.block [.ldrSp .x16 fTab]) fun L m₀ u => Φ L m₀ u ∧ u.gpr .x16 = L.tab :=
      Piece.blkS tblk1_taint fun L g m₀ t hL hk hc hφ => by
        have he := L.he
        exact WP.mono_syms (ldF_ok hL hc (d := .x16) (by decide) (o := fTab) (by simp only [fTab, extra]; omega_using [he]) rfl)
          fun u h hs => ⟨h.ctx, hΦ _ _ _ _ hφ (fun r hr => h.keep r hr) h.mem hs, by
            rw [h.val, show 16 + fTab = 232 + 8 * L.e by simp only [fTab, extra]; omega_using [he]]; exact hc.pTab⟩
    have s₂ : Piece P (fun L m₀ u => Φ L m₀ u ∧ u.gpr .x16 = L.tab) (.block [.ldr .x .x16 .x16 (8 * j)])
        fun L m₀ u => Φ L m₀ u ∧ u.gpr .x16 = L.fa n ∧ u.syms n = L.fa n ∧
          ts.find? (fun q => u.syms q.1 == u.syms n) = some (n, c) :=
      Piece.blk [.x16] (fun _ _ _ _ _ _ _ _ _ f₁ f₂ r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact f₁.2.trans f₂.2.symm) ht
        fun L g m₀ t hL hk hc ⟨hφ, h16⟩ => WP.mono (ldTab_ok hL hc h16 hj) fun u ⟨hc', hm, h16', hr, hs⟩ => by
          obtain ⟨hw, hf, hfa⟩ := hn L g m₀ t hL hk hc
          exact ⟨hc', hΦ _ _ _ _ hφ hr hm hs, by rw [h16', hw, hfa], by rw [hs, hfa], by rw [hs]; exact hf⟩
    refine (RelCT.block_append (s₁.ct.seq s₂.ct)).seq ?_
    cases ts with
    | nil => exact RelCT.of_false fun _ _ ⟨_, _, _, _, _, _, f₁, _⟩ => by simp at f₁
    | cons q ts =>
      exact RelCT.icalls_of_call (hcall.ct.mono (fun _ _ => Two.mono fun _ _ _ h => h.1) fun _ _ h => h)
        fun s₁ s₂ ⟨e, _, _, _, _, _, f₁, f₂⟩ => ⟨e.1.fa n, by simp only [icall, f₁.2.1],
          by simp only [icall, f₂.2.1],
          by show (q :: ts).find? (fun p => isa.fnAddr s₁ p.1 == e.1.fa n) = _
             simp only [isa]; rw [← f₁.2.2.1]; exact f₁.2.2.2,
          by show (q :: ts).find? (fun p => isa.fnAddr s₂ p.1 == e.1.fa n) = _
             simp only [isa]; rw [← f₂.2.2.1]; exact f₂.2.2.2, rfl⟩
  · obtain ⟨hw, hf, -⟩ := hn L g m₀ t hL hk hc
    exact tcall_ok hL hc hj hw hf fun t' hc' hm hr hs =>
      hcall.wp L g m₀ t' hL hk hc' (hΦ _ _ _ _ hφ hr hm hs)

/-! ## HMAC's calls -/

/-- HMAC's `init`'s arguments. -/
def IA (P : RfcHash) : Pr P := fun L _ u =>
  u.gpr .x0 = L.scr + BitVec.ofNat 64 0 ∧ u.gpr .x1 = L.scr + BitVec.ofNat 64 192 ∧
    u.gpr .x2 = L.B + BitVec.ofNat 64 16 ∧ u.gpr .x3 = BitVec.ofNat 64 P.H.D ∧
    u.gpr .x4 = L.scr + BitVec.ofNat 64 384

/-- The streaming `update`'s arguments: the inner state holding `cnt`
bytes, the `len` bytes at `da`, and the working space. -/
def UA (P : RfcHash) (cnt : Nat) (da : Lay P.I.hashLen P.R.E → Addr) (len : Nat) : Pr P := fun L _ u =>
  u.gpr .x0 = L.scr + BitVec.ofNat 64 0 ∧ u.gpr .x1 = BitVec.ofNat 64 cnt ∧ u.gpr .x2 = da L ∧
    u.gpr .x3 = BitVec.ofNat 64 len ∧ u.gpr .x4 = L.scr + BitVec.ofNat 64 384

/-- HMAC's `finalize`'s arguments: the states, the `cnt` bytes the inner one
holds, the MAC's place in the frame at `dst`, and the working space. -/
def FA (P : RfcHash) (cnt dst : Nat) : Pr P := fun L _ u =>
  u.gpr .x0 = L.scr + BitVec.ofNat 64 0 ∧ u.gpr .x1 = L.scr + BitVec.ofNat 64 192 ∧
    u.gpr .x2 = BitVec.ofNat 64 cnt ∧ u.gpr .x3 = L.B + BitVec.ofNat 64 (16 + dst) ∧
    u.gpr .x4 = L.scr + BitVec.ofNat 64 384

theorem ce_sp_two {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 64}
    {m₁ m₂ : Mem} (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) (rd₁ wr₁ rd₂ wr₂ : List Region) :
    (t₁.callEntry.withRegions rd₁ wr₁).sp = (t₂.callEntry.withRegions rd₂ wr₂).sp := by
  rw [State.withRegions_sp, State.withRegions_sp, State.callEntry_sp, State.callEntry_sp, sp_two c₁ c₂]

theorem ce_two {t₁ t₂ : State} {r : Reg} (hr : r ∉ linkRegs) {x : BitVec 64} (h₁ : t₁.gpr r = x)
    (h₂ : t₂.gpr r = x) (rd₁ wr₁ rd₂ wr₂ : List Region) :
    (t₁.callEntry.withRegions rd₁ wr₁).gpr r = (t₂.callEntry.withRegions rd₂ wr₂).gpr r := by
  rw [ce_gpr _ _ _ hr, ce_gpr _ _ _ hr, h₁, h₂]

theorem scr_sub {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {r : Region}
    (h : Region.Sub r ⟨L.scr, 2256⟩) : Safe L r :=
  .inr (.inl (sub_trans h (Region.sub_prefix (by omega_using []))))

theorem hinit_piece : Piece P (IA P) (.call P.H.hmacInitN P.H.hmacInit) (Tt P) := by
  refine Piece.of (AArch64.RelCT.callEx P.hI.1 P.hI.2.1 fun _ _ ⟨⟨L, _, _, _, _⟩, hL, _, _, c₁, c₂, a₁, a₂⟩ => by
    obtain ⟨d₁, s₁, x₁, k₁, r₁⟩ := a₁
    obtain ⟨d₂, s₂, x₂, k₂, r₂⟩ := a₂
    have A₁ := initA (P := P) hL c₁ d₁ s₁ x₁ k₁ r₁
    have A₂ := initA (P := P) hL c₂ d₂ s₂ x₂ k₂ r₂
    exact ⟨_, _, _, _, Pbkdf2.Md.AArch64.Pbk.InitArgs.pre P.ok A₁, Pbkdf2.Md.AArch64.Pbk.InitArgs.pre P.ok A₂,
      ⟨ce_two (by decide) d₁ d₂ _ _ _ _, ce_two (by decide) s₁ s₂ _ _ _ _, ce_two (by decide) x₁ x₂ _ _ _ _,
        ce_two (by decide) k₁ k₂ _ _ _ _, ce_two (by decide) r₁ r₂ _ _ _ _, ce_sp_two c₁ c₂ _ _ _ _⟩,
      Pbkdf2.Md.AArch64.Pbk.covers_app A₁.cr A₁.cw, A₁.cw, Pbkdf2.Md.AArch64.Pbk.covers_app A₂.cr A₂.cw, A₂.cw⟩)
    fun L g m₀ u hL _ hc a => ?_
  obtain ⟨d, s, x, k, r⟩ := a
  refine Pbkdf2.Md.AArch64.Pbk.hinit_call P.ok P.hI P.hId (initA (P := P) hL hc d s x k r)
    fun u' ha _ _ => ⟨hc.after hL ha fun r hr => scr_sub ?_, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact scr_work (by anums)

theorem upd_piece {cnt : Nat} {da : Lay P.I.hashLen P.R.E → Addr} {len : Nat}
    (hd : ∀ L : Lay P.I.hashLen P.R.E, L.Ok → DataOk L (da L) len) (hlen : len ≤ 256) :
    Piece P (UA P cnt da len) (.call P.H.updN P.H.updC) (Tt P) := by
  refine Piece.of (AArch64.RelCT.callEx P.ok.stream.upd.1 P.ok.stream.upd.2.1
    fun _ _ ⟨⟨L, _, _, _, _⟩, hL, _, _, c₁, c₂, a₁, a₂⟩ => by
      obtain ⟨d₁, s₁, x₁, k₁, r₁⟩ := a₁
      obtain ⟨d₂, s₂, x₂, k₂, r₂⟩ := a₂
      have A₁ := updA (P := P) hL c₁ (hd L hL) hlen d₁ x₁ k₁ r₁
      have A₂ := updA (P := P) hL c₂ (hd L hL) hlen d₂ x₂ k₂ r₂
      exact ⟨_, _, _, _, Pbkdf2.Md.AArch64.Calls.UpdArgs.pre P.ok.stream A₁,
        Pbkdf2.Md.AArch64.Calls.UpdArgs.pre P.ok.stream A₂,
        ⟨ce_two (by decide) d₁ d₂ _ _ _ _, ce_two (by decide) s₁ s₂ _ _ _ _, ce_two (by decide) x₁ x₂ _ _ _ _,
          ce_two (by decide) k₁ k₂ _ _ _ _, ce_two (by decide) r₁ r₂ _ _ _ _, ce_sp_two c₁ c₂ _ _ _ _⟩,
        Pbkdf2.Md.AArch64.Calls.UpdArgs.covers P.ok.stream A₁, A₁.cw,
        Pbkdf2.Md.AArch64.Calls.UpdArgs.covers P.ok.stream A₂, A₂.cw⟩) fun L g m₀ u hL _ hc a => ?_
  obtain ⟨d, _, x, k, r⟩ := a
  refine Pbkdf2.Md.AArch64.Calls.upd_call P.ok.stream (updA (P := P) hL hc (hd L hL) hlen d x k r)
    fun u' af _ => ⟨hc.after hL af fun r hr => scr_sub ?_, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact scr_work (by anums)

theorem hfin_piece {cnt dst : Nat} (hdst : dst + P.H.D ≤ 184) :
    Piece P (FA P cnt dst) (.call P.H.hmacFinN P.H.hmacFin) (Tt P) := by
  refine Piece.of (AArch64.RelCT.callEx P.hF.1 P.hF.2.1 fun _ _ ⟨⟨L, _, _, _, _⟩, hL, _, _, c₁, c₂, a₁, a₂⟩ => by
    obtain ⟨d₁, s₁, x₁, k₁, r₁⟩ := a₁
    obtain ⟨d₂, s₂, x₂, k₂, r₂⟩ := a₂
    have A₁ := finA (P := P) hL c₁ hdst d₁ s₁ x₁ k₁ r₁
    have A₂ := finA (P := P) hL c₂ hdst d₂ s₂ x₂ k₂ r₂
    exact ⟨_, _, _, _, Pbkdf2.Md.AArch64.Pbk.FinArgs.pre P.ok A₁, Pbkdf2.Md.AArch64.Pbk.FinArgs.pre P.ok A₂,
      ⟨ce_two (by decide) d₁ d₂ _ _ _ _, ce_two (by decide) s₁ s₂ _ _ _ _, ce_two (by decide) x₁ x₂ _ _ _ _,
        ce_two (by decide) k₁ k₂ _ _ _ _, ce_two (by decide) r₁ r₂ _ _ _ _, ce_sp_two c₁ c₂ _ _ _ _⟩,
      Pbkdf2.Md.AArch64.Pbk.covers_app A₁.cr A₁.cw, A₁.cw, Pbkdf2.Md.AArch64.Pbk.covers_app A₂.cr A₂.cw, A₂.cw⟩)
    fun L g m₀ u hL _ hc a => ?_
  obtain ⟨d, s, x, k, r⟩ := a
  refine Pbkdf2.Md.AArch64.Pbk.hfin_call P.ok P.hF P.hFd (finA (P := P) hL hc hdst d s x k r)
    fun u' ha _ => ⟨hc.after hL ha fun r hr => ?_, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact scr_sub (scr_work (by anums))
  · exact safe_low L (by anums)
  · exact scr_sub (scr_work (by anums))

theorem r16_ia : R16 (IA P) := fun _ _ _ _ ⟨d, s, x, k, r⟩ hr _ _ => ⟨(hr _ (by decide)).trans d,
  (hr _ (by decide)).trans s, (hr _ (by decide)).trans x, (hr _ (by decide)).trans k, (hr _ (by decide)).trans r⟩

theorem r16_ua {cnt : Nat} {da : Lay P.I.hashLen P.R.E → Addr} {len : Nat} : R16 (UA P cnt da len) :=
  fun _ _ _ _ ⟨d, s, x, k, r⟩ hr _ _ => ⟨(hr _ (by decide)).trans d, (hr _ (by decide)).trans s,
    (hr _ (by decide)).trans x, (hr _ (by decide)).trans k, (hr _ (by decide)).trans r⟩

theorem r16_fa {cnt dst : Nat} : R16 (FA P cnt dst) :=
  fun _ _ _ _ ⟨d, s, x, k, r⟩ hr _ _ => ⟨(hr _ (by decide)).trans d, (hr _ (by decide)).trans s,
    (hr _ (by decide)).trans x, (hr _ (by decide)).trans k, (hr _ (by decide)).trans r⟩

/-! ## HMAC through the table -/

theorem initArgs_taint : TaintOk [] Cfg.initArgs := ⟨_, by taint_decide⟩

theorem updVArgs_taint : TaintOk [] Cfg.updVArgs := ⟨_, by taint_decide⟩

/-- For any length: the analysis does not read `movz`'s immediates. -/
theorem updMArgs_taint (len : Nat) : TaintOk [] (Cfg.updMArgs len) :=
  taintOk_erase (is₀ := Cfg.updMArgs 0) ⟨_, by taint_decide⟩ rfl

theorem tload_taint₀ : TaintOk [.x16] [.ldr .x .x16 .x16 (8 * 0)] := ⟨_, by taint_decide⟩
theorem tload_taint₁ : TaintOk [.x16] [.ldr .x .x16 .x16 (8 * 1)] := ⟨_, by taint_decide⟩
theorem tload_taint₂ : TaintOk [.x16] [.ldr .x .x16 .x16 (8 * 2)] := ⟨_, by taint_decide⟩

/-- HMAC's states for `K`. -/
theorem initK_piece {Φ : Pr P} : Piece P Φ (cfgOf P).initK (Tt P) :=
  (Piece.blkS (Ψ := IA P) initArgs_taint fun _ _ _ _ hL hk hc _ =>
    WP.mono (initArgs_ok hL hk.2 hc) fun _ ⟨c, _, d, s, x, k, r⟩ => ⟨c, d, s, x, k, r⟩).seq
    (tcall_piece (by decide) tfn_init r16_ia tload_taint₀ hinit_piece)

/-- The inner state updated with `V`. -/
theorem updV_piece {Φ : Pr P} : Piece P Φ (cfgOf P).updV (Tt P) :=
  (Piece.blkS (Ψ := UA P P.H.P.B (fun L => L.B + BitVec.ofNat 64 80) P.H.D) updVArgs_taint
    fun _ _ _ _ hL hk hc _ =>
      WP.mono (updVArgs_ok hL hk.2 hc) fun _ ⟨c, _, d, s, x, k, r⟩ => ⟨c, d, s, x, k, r⟩).seq
    (tcall_piece (by decide) tfn_upd r16_ua tload_taint₁
      (upd_piece (fun L _ => .inl ⟨80, rfl, by omega_using [], by anums⟩) (by anums)))

/-- The inner state updated with the message's `len` bytes. -/
theorem updM_piece {Φ : Pr P} {len : Nat} (hlen : len ≤ 256) : Piece P Φ ((cfgOf P).updM len) (Tt P) :=
  (Piece.blkS (Ψ := UA P (P.H.P.B + P.H.D) (fun L => L.scr + BitVec.ofNat 64 sMsg) len) (updMArgs_taint len)
    fun _ _ _ _ hL hk hc _ =>
      WP.mono (updMArgs_ok hL hk.2 hc (len := len) (by omega_using [hlen])) fun _ ⟨c, _, d, s, x, k, r⟩ =>
        ⟨c, d, s, x, k, r⟩).seq
    (tcall_piece (by decide) tfn_upd r16_ua tload_taint₁
      (upd_piece (fun L _ => .inr ⟨sMsg, rfl, by simp only [sMsg]; omega_using [], by simp only [sMsg]; omega_using [hlen]⟩) hlen))

/-- The MAC, of `D + len` bytes, to the frame at `dst`. -/
theorem fin_piece {Φ : Pr P} {len dst : Nat} (hlen : len ≤ 256) (hdst : dst + P.H.D ≤ 184)
    (ht : TaintOk [] (Cfg.finArgs len dst)) : Piece P Φ ((cfgOf P).fin len dst) (Tt P) :=
  (Piece.blkS (Ψ := FA P (P.H.P.B + P.H.D + len) dst) ht fun _ _ _ _ hL hk hc _ =>
    WP.mono (finArgs_ok hL hk.2 hc (len := len) (dst := dst) (by omega_using [hlen]) (by omega_using [hdst]))
      fun _ ⟨c, _, d, s, x, k, r⟩ => ⟨c, d, s, x, k, r⟩).seq
    (tcall_piece (by decide) tfn_fin r16_fa tload_taint₂ (hfin_piece hdst))

/-! ## The byte loops -/

theorem cpLoop_taint : ∃ hc, (taint.check (Taint.ofRegs [.x11, .x12, .x13]) Cfg.cpLoop hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- A byte copy's registers. -/
abbrev CpA (P : RfcHash) (p q : Lay P.I.hashLen P.R.E → Addr) (n : Nat) : Pr P := fun L _ u =>
  u.gpr .x11 = q L ∧ u.gpr .x12 = p L ∧ u.gpr .x13 = BitVec.ofNat 64 n

/-- The byte loop, from registers that agree. -/
theorem cp_ct {Φ : Pr P} {p q : Lay P.I.hashLen P.R.E → Addr} {n : Nat}
    (h : ∀ L m₀ u, Φ L m₀ u → CpA P p q n L m₀ u) : RelCT isa (Two P Φ) Cfg.cpLoop fun _ _ => True :=
  two_prog [.x11, .x12, .x13] (fun _ _ _ _ _ _ _ _ _ f₁ f₂ r hr => by
    obtain ⟨a₁, b₁, c₁⟩ := h _ _ _ f₁; obtain ⟨a₂, b₂, c₂⟩ := h _ _ _ f₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact a₁.trans a₂.symm
    · exact b₁.trans b₂.symm
    · exact c₁.trans c₂.symm) cpLoop_taint

/-- The copy of the 384 bytes at `scratch + a` to `scratch + d`, apart. -/
theorem copy384_piece {Φ : Pr P} {a d : Nat} (ha : a < 4096) (hd : d < 4096) (hsep : a + 384 ≤ d ∨ d + 384 ≤ a)
    (hd₂ : d + 384 ≤ 8192) (ht : TaintOk [] (([.ldrSp .x9 fScratch] : List Instr) ++ ([.addImm .x .x11 .x9 a] : List Instr) ++
      ([.addImm .x .x12 .x9 d] : List Instr) ++ ([.movz .x .x13 (BitVec.ofNat 16 384) 0] : List Instr))) :
    Piece P Φ (.seq (.block (([.ldrSp .x9 fScratch] : List Instr) ++ ([.addImm .x .x11 .x9 a] : List Instr) ++
      ([.addImm .x .x12 .x9 d] : List Instr) ++ ([.movz .x .x13 (BitVec.ofNat 16 384) 0] : List Instr))) Cfg.cpLoop) (Tt P) :=
  Piece.of ((two_wp (Ψ := CpA P (fun L => L.scr + BitVec.ofNat 64 d) (fun L => L.scr + BitVec.ofNat 64 a) 384)
      (two_blk [] spOnly ht) fun _ _ _ _ hL _ hc _ =>
        WP.mono (copyArgs_ok hL ha hd hc) fun _ ⟨c, _, h11, h12, h13⟩ => ⟨c, h11, h12, h13⟩).seq
      (cp_ct fun _ _ _ h => h))
    fun _ _ _ _ hL _ hc _ => WP.mono (copy384_ok hL ha hd hsep hd₂ hc) fun _ h => ⟨h.1, trivial⟩

/-- HMAC's states saved. -/
theorem save_piece {Φ : Pr P} : Piece P Φ Cfg.save (Tt P) :=
  copy384_piece (a := 0) (d := 3072) (by decide) (by decide) (by decide) (by decide) ⟨_, by taint_decide⟩

/-- HMAC's states restored. -/
theorem restore_piece {Φ : Pr P} : Piece P Φ Cfg.restore (Tt P) :=
  copy384_piece (a := 3072) (d := 0) (by decide) (by decide) (by decide) (by decide) ⟨_, by taint_decide⟩

/-! ## HMAC -/

theorem finV_taint : TaintOk [] (Cfg.finArgs 0 fV) := ⟨_, by taint_decide⟩

theorem finK1_taint : TaintOk [] (Cfg.finArgs 1 fK) := ⟨_, by taint_decide⟩

theorem hmacVS_piece {Φ : Pr P} : Piece P Φ (cfgOf P).hmacVS (Tt P) :=
  initK_piece.seq (save_piece.seq
    (updV_piece.seq (fin_piece (by decide) (by simp only [fV]; anums) finV_taint)))

theorem hmacVR_piece {Φ : Pr P} : Piece P Φ (cfgOf P).hmacVR (Tt P) :=
  restore_piece.seq (updV_piece.seq (fin_piece (by decide) (by simp only [fV]; anums) finV_taint))

/-- `K = HMAC_K(V ‖ msg)`, for the message's `len` bytes. -/
theorem hmacK_piece {Φ : Pr P} {len : Nat} (hlen : len ≤ 256) (ht : TaintOk [] (Cfg.finArgs len fK))
    (fresh : Bool) : Piece P Φ ((cfgOf P).hmacK fresh len) (Tt P) := by
  unfold Cfg.hmacK
  cases fresh
  · exact restore_piece.seq (updV_piece.seq ((updM_piece hlen).seq
      (fin_piece hlen (by simp only [fK]; anums) ht)))
  · exact initK_piece.seq (updV_piece.seq ((updM_piece hlen).seq (fin_piece hlen (by simp only [fK]; anums) ht)))

/-! ## `K` and `V` from a message -/

/-- `scratch` in `x9`, `d` in `x10` and the frame in `x15`. -/
def PtrsIn (P : RfcHash) : Pr P := fun L _ u =>
  u.gpr .x9 = L.scr ∧ u.gpr .x10 = L.d ∧ u.gpr .x15 = L.B + BitVec.ofNat 64 16

theorem msgPtrs_piece {Φ : Pr P} : Piece P Φ (.block Cfg.msgPtrs) (PtrsIn P) :=
  Piece.blkS ⟨_, by taint_decide⟩ fun _ _ _ _ hL _ hc _ =>
    WP.mono (ptrs_ok hL hc) fun _ ⟨c, _, d, s, f⟩ => ⟨c, d, s, f⟩

/-- The message `b (‖ d ‖ h)` at `scratch + sMsg`. -/
theorem msg_piece {b : Nat} {full : Bool} (ht : TaintOk [.x9, .x10, .x15] ((cfgOf P).msg b full)) :
    Piece P (PtrsIn P) (.block ((cfgOf P).msg b full)) (Tt P) :=
  Piece.blk [.x9, .x10, .x15] (fun _ _ _ _ _ _ _ _ _ f₁ f₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact f₁.1.trans f₂.1.symm
      · exact f₁.2.1.trans f₂.2.1.symm
      · exact f₁.2.2.trans f₂.2.2.symm) ht
    fun _ _ _ _ hL hk hc hp => WP.mono (msg_ok hL hk.1 hc hp.1 hp.2.1 hp.2.2 b full) fun _ h => ⟨h.1, trivial⟩

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)`. -/
theorem rekeyFull_piece {Φ : Pr P} (b : Nat) (ht : TaintOk [.x9, .x10, .x15] ((cfgOf P).msg b true)) :
    Piece P Φ ((cfgOf P).rekeyFull b) (Tt P) := by
  have hlen : 1 + 2 * (cfgOf P).len ≤ 256 := by show 1 + 2 * P.Q ≤ 256; anums
  unfold Cfg.rekeyFull
  exact msgPtrs_piece.seq ((msg_piece ht).seq ((hmacK_piece hlen (by exact (rT P).finM) _).seq hmacVS_piece))

theorem msgN_taint : TaintOk [.x9, .x10, .x15] ((cfgOf P).msg 0 false) := by
  rw [show (cfgOf P).msg 0 false = [.movz .x .x11 (BitVec.ofNat 16 0) 0, .strb .x11 .x9 sMsg] by
    simp only [Cfg.msg, Bool.false_eq_true, ite_false, List.append_nil]]
  exact ⟨_, by taint_decide⟩

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)`. -/
theorem rekey_piece {Φ : Pr P} : Piece P Φ (cfgOf P).rekey (Tt P) := by
  unfold Cfg.rekey
  exact msgPtrs_piece.seq ((msg_piece msgN_taint).seq ((hmacK_piece (by decide) finK1_taint _).seq hmacVS_piece))

/-- `Ctx` with other callee-saved values, which are the same. -/
theorem Ctx.regen {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {g g' : Reg → BitVec 64} {m₀ : Mem}
    {u : State} (hc : Ctx L g' m₀ u) (h : ∀ r ∈ preserved, r ≠ .x30 → g' r = g r) (h30 : g' .x30 = g .x30) :
    Ctx L g m₀ u :=
  { hc with cs := fun r hr hr' => (hc.cs r hr hr').trans (h r hr hr'), lr := hc.lr.trans h30 }

/-! ## The candidate -/

/-- After `j` of the candidate's `V`s, from some `K` and `V`. -/
abbrev CJ (P : RfcHash) (j : Nat) : Pr P := fun L m₀ u => ∃ g' t₀ K V₀, CI P L g' m₀ t₀ K V₀ j u

/-- `T`'s length, `j` blocks. -/
abbrev TL (P : RfcHash) (j : Nat) : Pr P := fun L _ u => tlen L u.mem = BitVec.ofNat 64 (j * P.H.D)

/-- The arguments of the copy of `V` to `T`'s end, and `j` blocks. -/
abbrev KA (P : RfcHash) (j : Nat) : Pr P := fun L m₀ u =>
  CpA P (fun L => L.B + BitVec.ofNat 64 (16 + fT + j * P.H.D)) (fun L => L.B + BitVec.ofNat 64 (16 + fV)) P.H.D
    L m₀ u ∧ TL P j L m₀ u

/-- One `V`'s blocks and calls leak the same in both runs. -/
theorem candStep_trace {j : Nat} (hj : j < P.nV) :
    RelCT isa (Two P (CJ P j)) (cfgOf P).candStep fun _ _ => True := by
  obtain ⟨-, hND, -⟩ := nV_facts P
  obtain ⟨-, -, -, -, -, -, hD16, hD64, -, -, -, -, -, -, -, hQ66, -, -⟩ := P.sizes
  have hb : (j + 1) * P.H.D ≤ 136 :=
    Nat.le_trans (Nat.mul_le_mul (show j + 1 ≤ P.nV by omega_using [hj]) (Nat.le_refl P.H.D)) (by omega_using [hND, hD64, hQ66])
  have hjD : (j + 1) * P.H.D = j * P.H.D + P.H.D := Nat.succ_mul _ _
  refine (two_wp (Ψ := TL P j) (hmacVR_piece.rel fun _ _ _ _ => trivial) fun L g m₀ t hL hk hc hJ => ?_).seq
    ((two_wp (Ψ := KA P j) (two_blk [] spOnly ⟨_, by taint_decide⟩) fun L g m₀ t hL hk hc hl =>
      WP.mono (keepArgs_ok hL hk.2 hc hl) fun u ⟨c, hm, si, di, cx⟩ =>
        ⟨c, ⟨si, di, cx⟩, by show tlen L u.mem = _; rw [hm]; exact hl⟩).seq
    ((two_wp (Ψ := TL P j) (cp_ct fun _ _ _ h => h.1) fun L g m₀ t hL hk hc ⟨⟨si, di, cx⟩, hl⟩ => ?_).seq
      (two_blk [] spOnly (by exact (rT P).tStep))))
  · obtain ⟨_, _, _, _, hI⟩ := hJ
    have hS : SavedK P L t.mem (kOf P L t.mem) := by rw [hI.k]; exact hI.saved
    refine WP.mono (hmacVR_ok hL hk.2 hc hS) fun u ⟨hc₁, hf₁, _⟩ => ⟨hc₁, ?_⟩
    show tlen L u.mem = _
    rw [← hI.len]
    exact hf₁.readW (Region.contains_self _ _) (fun r hr => by
      have := L.he
      simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_SCR (by simp only [fTlen]; omega_using [])
      · exact Offset.disjoint_base _ (by simp only [fTlen]; omega_using []) (by simp only [fTlen]; omega_using [])) (by decide)
  · have he := L.he
    have hnb := hL.nB
    refine WP.mono (cp_ok hL hc (p := L.B + BitVec.ofNat 64 (16 + fT + j * P.H.D))
        (q := L.B + BitVec.ofNat 64 (16 + fV)) (n := P.H.D) (by omega_using [hD16]) (by omega_using [hD64]) cx di si ?_
        (hc.inFrW (by omega_using []) (by simp only [fT]; omega_using [hb, hjD, he]))
        (safe_high L (by simp only [fT]; omega_using []) (by simp only [fT]; omega_using [hb, hjD, he]))
        (fun i hi => by
          obtain ⟨R, hR, h⟩ := hc.inFrW (d := 16 + fV + i) (n := 1) (by omega_using []) (by simp only [fV]; omega_using [hD64, hi])
          exact ⟨R, List.mem_append_right _ hR, by rw [Offset.add_add]; exact h⟩)
        (fun i hi h => Offset.disjoint L.B (d := 16 + fV + i) (n := 1) (e := 16 + fT + j * P.H.D) (k := P.H.D)
          (.inl (by simp only [fV, fT]; omega_using [hD64, hi])) (by simp only [fV]; omega_using [hD64, hi]) (by simp only [fT]; omega_using [hb, hjD]) _
          (by rw [← Offset.add_add]; exact Region.contains_self _ _) h)) fun u ⟨hcu, _, hf, _⟩ => ⟨hcu, ?_⟩
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 + fT + _) (by simp only [fT]; omega_using [hb, hjD]),
        Nat.mod_eq_of_lt (by simp only [fT]; omega_using [hb, hjD, he, hnb])]
      simp only [fT]; omega_using [hb, hjD, he, hnb]
    · show tlen L u.mem = _
      rw [← hl]
      exact hf.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inl (by simp only [fTlen, fT]; omega_using [])) (by simp only [fTlen]; omega_using [])
          (by simp only [fT]; omega_using [hb, hjD])) (by decide)

/-- The loop of the candidate's `V`s, in two runs: at the same block. -/
theorem candLoop_ct :
    RelCT isa (Two P (CJ P 0)) (.loop (cfgOf P).candStep (.nonzero .x .x12)) (Two P (CJ P P.nV)) := by
  obtain ⟨hN1, hND, -⟩ := nV_facts P
  obtain ⟨-, -, -, -, -, -, -, hD64, -, -, -, -, -, -, -, hQ66, -, -⟩ := P.sizes
  have h := VG.RelCT.loop (M := isa) (c := .nonzero .x .x12) (Q := Two P (CJ P P.nV))
    (fun n => fun s₁ s₂ => 0 < n ∧ n ≤ P.nV ∧ Two P (CJ P (P.nV - n)) s₁ s₂) (n := P.nV)
    (body := (cfgOf P).candStep)
    (fun n => by
      refine fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨hn0, hnN, hp⟩ e₁ e₂ => ?_
      have hj : P.nV - n < P.nV := by omega_using [hN1, hn0]
      have hb : (P.nV - n + 1) * P.H.D ≤ 136 :=
        Nat.le_trans (Nat.mul_le_mul (show P.nV - n + 1 ≤ P.nV by omega_using [hN1, hn0]) (Nat.le_refl P.H.D)) (by omega_using [hND, hD64, hQ66])
      obtain ⟨ht, hq⟩ := (two_wp (Ψ := fun L m₀ u => CJ P (P.nV - n + 1) L m₀ u ∧
          (u.gpr .x12 != 0) = decide ((P.nV - n + 1) * P.H.D < P.Q)) (candStep_trace hj)
        fun L g m₀ t hL hk hc ⟨g', t₀, K, V₀, hI⟩ => WP.mono (step_ok hL hk.2 hb hI)
          fun u ⟨hI', hcf⟩ => ⟨hI'.ctx.regen (fun r h h' => (hI.ctx.cs r h h').symm.trans (hc.cs r h h'))
              (hI.ctx.lr.symm.trans hc.lr),
            ⟨g', t₀, K, V₀, hI'⟩, hcf⟩) s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
      refine ⟨ht, ?_, ?_, ?_⟩
      · obtain ⟨_, _, _, _, _, _, f₁, f₂⟩ := hq
        rw [eval_nonzero, eval_nonzero, f₁.2, f₂.2]
      · intro hf
        obtain ⟨e, hL, hk, hx, c₁, c₂, f₁, f₂⟩ := hq
        rw [eval_nonzero, f₁.2, Option.some.injEq, decide_eq_false_iff_not] at hf
        have hNn : P.nV - n + 1 = P.nV := by
          have : ¬ P.nV - n + 1 < P.nV := fun h => hf ((nV_lt P _).mp h)
          omega_using [hN1, hn0, this]
        exact ⟨e, hL, hk, hx, c₁, c₂, hNn ▸ f₁.1, hNn ▸ f₂.1⟩
      · intro hf
        obtain ⟨e, hL, hk, hx, c₁, c₂, f₁, f₂⟩ := hq
        rw [eval_nonzero, f₁.2, Option.some.injEq, decide_eq_true_iff] at hf
        have hlt := (nV_lt P (P.nV - n)).mpr hf
        refine ⟨n - 1, by omega_using [hn0], by omega_using [hlt], by omega_using [hnN], e, hL, hk, hx, c₁, c₂, ?_, ?_⟩ <;>
          rw [show P.nV - (n - 1) = P.nV - n + 1 by omega_using [hn0, hnN]]
        · exact f₁.1
        · exact f₂.1)
  exact h.mono (fun s₁ s₂ hp => ⟨hN1, Nat.le_refl _, by rwa [Nat.sub_self]⟩) fun _ _ h => h

/-- A conversion: its block addresses memory from `scratch`, loaded first into `x0`. -/
theorem conv_ct {Φ : Pr P} {o s : Nat} (h : TaintOk [.x0] ((cfgOf P).convB o s)) :
    RelCT isa (Two P Φ) ((cfgOf P).conv o s) fun _ _ => True := by
  rw [Cfg.conv]
  exact (two_wp (Ψ := fun L _ u => u.gpr .x0 = L.scr) (two_blk [] spOnly ⟨_, by taint_decide⟩)
    fun _ _ _ _ hL _ hc _ => WP.mono (ldScr_ok hL hc) fun _ h => ⟨h.ctx, h.val⟩).seq
    (two_blk [.x0] (fun _ _ _ _ _ _ _ _ _ f₁ f₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact f₁.trans f₂.symm) h)

theorem candTop_ct {Φ : Pr P} : RelCT isa (Two P Φ) (cfgOf P).candTop fun _ _ => True := by
  cases hb : P.R.big
  · rw [show (cfgOf P).candTop = .block [] by
      simp only [Cfg.candTop, show (cfgOf P).big = false from hb, Bool.false_eq_true, ite_false]]
    exact two_blk [] spOnly ⟨_, by taint_decide⟩
  · rw [show (cfgOf P).candTop = (cfgOf P).conv fT (cfgOf P).sh by
      simp only [Cfg.candTop, show (cfgOf P).big = true from hb, ite_true]]
    exact conv_ct (by exact (rT P).convT hb)

/-- The candidate: its calls, blocks and loops leak the same in both runs. -/
theorem cand_ct :
    RelCT isa (Two P fun L _ t => SavedK P L t.mem (kOf P L t.mem)) (cfgOf P).cand fun _ _ => True := by
  unfold Cfg.cand
  exact (two_wp (Ψ := CJ P 0) (two_blk [] spOnly ⟨_, by taint_decide⟩) fun L g m₀ t hL hk hc hS =>
    WP.mono (tInit_ci hL hc hS) fun u hI => ⟨hI.ctx, _, _, _, _, hI⟩).seq (candLoop_ct.seq candTop_ct)

/-! ## One candidate -/

/-- `core`, with arguments that agree. -/
theorem core_ct {i : Nat} :
    RelCT isa (Two P fun L m₀ u => P₁ P L m₀ i u ∧ Args P L u) (.call (cfgOf P).coreN (cfgOf P).coreC)
      fun _ _ => True :=
  AArch64.RelCT.callEx P.R.coreX P.R.coreCT
    fun _ _ ⟨⟨L, _, _, _, _⟩, hL, hq, _, c₁, c₂, ⟨_, a₁⟩, ⟨_, a₂⟩⟩ =>
    ⟨coreRd P L, coreWr P L, coreRd P L, coreWr P L, core_pre hL hq.1 c₁ a₁.x0 a₁.x1 a₁.x2 a₁.x3 a₁.x4,
      core_pre hL hq.1 c₂ a₂.x0 a₂.x1 a₂.x2 a₂.x3 a₂.x4,
      ⟨ce_two (by decide) a₁.x0 a₂.x0 _ _ _ _, ce_two (by decide) a₁.x1 a₂.x1 _ _ _ _,
        ce_two (by decide) a₁.x2 a₂.x2 _ _ _ _, ce_two (by decide) a₁.x3 a₂.x3 _ _ _ _,
        ce_two (by decide) a₁.x4 a₂.x4 _ _ _ _, ce_sp_two c₁ c₂ _ _ _ _, c₁.sy.trans c₂.sy.symm⟩,
      core_covers hL hq.1 c₁, core_coversW hq.1 c₁, core_covers hL hq.1 c₂, core_coversW hq.1 c₂⟩

/-- Whether to go on agrees: in both runs, iff the candidate is before the one it stops at. -/
theorem dec_two {L : Lay P.I.hashLen P.R.E} {m₁ m₂ : Mem} {i : Nat} (hx : exitAt P L m₁ = exitAt P L m₂)
    {u₁ u₂ : State} (h₁ : Mid P L m₁ i u₁) (h₂ : Mid P L m₂ i u₂) :
    isa.eval (.nonzero .x .x12) u₁ = isa.eval (.nonzero .x .x12) u₂ := by
  rw [h₁.dec, h₂.dec]
  refine congrArg some (decide_eq_decide.mpr ?_)
  rw [go_iff h₁.lt h₁.fails, go_iff h₂.lt h₂.fails, hx]

/-- What one candidate leaves: the end, or the next candidate. -/
def After (P : RfcHash) (i : Nat) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) (t : State) : Prop :=
  (isa.eval (.nonzero .x .x12) t = some false ∧ Exit P L m₀ i t) ∨
    (isa.eval (.nonzero .x .x12) t = some true ∧ LoopInv P L m₀ (i + 1) t)

theorem tryOne_trace {i : Nat} :
    RelCT isa (Two P fun L m₀ t => LoopInv P L m₀ i t) (cfgOf P).tryOne fun _ _ => True := by
  refine (two_wp (Ψ := fun L m₀ u => P₁ P L m₀ i u)
    (cand_ct.mono (fun _ _ h => Two.mono (fun _ _ _ hi => hi.saved) h) fun _ _ h => h)
    fun _ _ _ _ hL hk hc hi => try₁_ok hL hk hc hi).seq ?_
  refine (two_wp (Ψ := fun L m₀ u => P₁ P L m₀ i u ∧ Args P L u) (two_blk [] spOnly (by exact (rT P).coreArgs))
    fun _ _ _ _ hL hk hc hi => try₂_ok hL hc hi).seq ?_
  refine (two_wp (Ψ := fun L m₀ u => P₃ P L m₀ i u) core_ct fun _ _ _ _ hL hk hc hi =>
    try₃_ok hL hk hc hi.1 hi.2).seq ?_
  refine (two_wp (Ψ := fun L m₀ u => Mid P L m₀ i u) (two_blk [] spOnly ⟨_, by taint_decide⟩)
    fun _ _ _ _ hL hk hc hi => try₄_ok hL hk hc hi).seq ?_
  refine VG.RelCT.ite (fun _ _ ⟨_, _, _, hx, _, _, f₁, f₂⟩ => dec_two hx f₁ f₂) ?_ ?_
  · exact (rekey_piece.ct.seq (two_blk [] spOnly ⟨_, by taint_decide⟩)).mono (fun _ _ h => h.1) fun _ _ h => h
  · exact (two_blk [] spOnly ⟨_, by taint_decide⟩).mono (fun _ _ h => h.1) fun _ _ h => h

/-- One candidate: both runs end, or both go on. -/
theorem tryOne_ct {i : Nat} :
    RelCT isa (Two P fun L m₀ t => LoopInv P L m₀ i t) (cfgOf P).tryOne fun s₁ s₂ =>
      isa.eval (.nonzero .x .x12) s₁ = isa.eval (.nonzero .x .x12) s₂ ∧
        (isa.eval (.nonzero .x .x12) s₁ = some false → Two P (Exit P · · i) s₁ s₂) ∧
        (isa.eval (.nonzero .x .x12) s₁ = some true → Two P (LoopInv P · · (i + 1)) s₁ s₂) := by
  refine (two_wp (Ψ := After P i) tryOne_trace fun _ _ _ _ hL hk hc hi => tryOne_ok hL hk hc hi).mono
    (fun _ _ h => h) fun s₁ s₂ ⟨e, hL, hk, hx, c₁, c₂, f₁, f₂⟩ => ?_
  -- A run that goes on has a later candidate to stop at, so the other cannot have stopped.
  have mixed : ∀ (m m' : Mem) (u u' : State), exitAt P e.1 m = exitAt P e.1 m' → Exit P e.1 m i u →
      LoopInv P e.1 m' (i + 1) u' → False := fun _ m' _ _ hx' hE hI => by
    have hgo : sigI P e.1 m' i = none ∧ i + 1 < P.I.tries := ⟨hI.fails i (by omega_using []), hI.lt⟩
    rw [go_iff (by omega) (fun j hj => hI.fails j (by omega_using [hj])), ← hx', ← go_iff hE.lt hE.fails] at hgo
    rcases hE.last with h | h
    · exact h hgo.1
    · omega
  rcases f₁ with ⟨d₁, x₁⟩ | ⟨d₁, x₁⟩ <;> rcases f₂ with ⟨d₂, x₂⟩ | ⟨d₂, x₂⟩
  · exact ⟨d₁.trans d₂.symm, fun _ => ⟨e, hL, hk, hx, c₁, c₂, x₁, x₂⟩, fun h => absurd (h.symm.trans d₁) (by decide)⟩
  · exact (mixed _ _ _ _ hx x₁ x₂).elim
  · exact (mixed _ _ _ _ hx.symm x₂ x₁).elim
  · exact ⟨d₁.trans d₂.symm, fun h => absurd (h.symm.trans d₁) (by decide), fun _ => ⟨e, hL, hk, hx, c₁, c₂, x₁, x₂⟩⟩

/-! ## The loop -/

theorem next_n {T n : Nat} (h : T - n + 1 < T) : T - (T - n + 1) < n ∧ T - (T - (T - n + 1)) = T - n + 1 :=
  ⟨by omega_using [h], by omega_using [h]⟩

theorem tries_ct :
    RelCT isa (Two P fun L m₀ t => LoopInv P L m₀ 0 t) (.loop (cfgOf P).tryOne (.nonzero .x .x12))
      (Two P fun L m₀ t => ∃ i, Exit P L m₀ i t) := by
  have h : RelCT isa (Two P fun L m₀ t => LoopInv P L m₀ (P.I.tries - P.I.tries) t)
      (.loop (cfgOf P).tryOne (.nonzero .x .x12)) (Two P fun L m₀ t => ∃ i, Exit P L m₀ i t) :=
    VG.RelCT.loop (M := isa) (fun n => Two P fun L m₀ t => LoopInv P L m₀ (P.I.tries - n) t)
      (fun n => tryOne_ct.mono (fun _ _ h => h) fun _ _ ⟨he, hf, ht⟩ =>
        ⟨he, fun h => (hf h).mono fun _ _ _ hx => ⟨_, hx⟩, fun h => by
          obtain ⟨e, hL, hk, hx, c₁, c₂, f₁, f₂⟩ := ht h
          have hn := next_n f₁.lt
          refine ⟨P.I.tries - (P.I.tries - n + 1), hn.1, e, hL, hk, hx, c₁, c₂, ?_, ?_⟩ <;> rwa [hn.2]⟩)
      P.I.tries
  rwa [Nat.sub_self] at h

/-! ## The frame's body -/

/-- For any count: the analysis does not read `movz`'s immediates. -/
theorem initCnt_taint (c : Cfg) : TaintOk [] c.initCnt :=
  taintOk_erase (is₀ := [.movz .x .x9 0 0, .addSp .x15 0, .str .x .x9 .x15 fCnt]) ⟨_, by taint_decide⟩ rfl

/-- The arguments of `xcArgs`'s copy: the digest's `D` bytes to `fXc`, after
`Q - 1 - D` zero bytes. -/
theorem xcArgs_ok (hL : L.Ok) (hk : HOk P L) (hW : P.R.big = true) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).xcArgs) t fun u => Ctx L g m₀ u ∧
      CpA P (fun L => L.B + BitVec.ofNat 64 (16 + fXc + (P.Q - 1 - P.H.D))) (fun L => L.dg) P.H.D L m₀ u := by
  have he := L.he
  obtain ⟨-, hQ66, hQD⟩ := P.sizesW hW
  obtain ⟨-, -, -, -, -, -, hD16, hD64, -, -, -, -, -, -, -, -, -, -⟩ := P.sizes
  have hlen : (cfgOf P).len = P.Q := rfl
  rw [Cfg.xcArgs, WP.block_append_iff]
  refine WP.mono (zero9_ok hL (o := fXc) (by decide) (by simp only [fXc]; omega_using [he]) (by decide) hc)
    fun u₁ ⟨hc₁, _, _, _, _⟩ => ?_
  rw [hlen, show ([.ldrSp .x13 fDl, .addSp .x12 (fXc + P.Q - 1), .sub .x .x12 .x12 .x13, .ldrSp .x11 fDigest] :
      List Instr) = [.ldrSp .x13 fDl] ++ [.addSp .x12 (fXc + P.Q - 1), .sub .x .x12 .x12 .x13, .ldrSp .x11 fDigest]
      from rfl, WP.block_append_iff]
  refine WP.mono (ldD_ok hL hk.2 hc₁ (d := .x13) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (xTail_ok hL h₂.ctx (o := fXc + P.Q - 1) (by simp only [fXc]; omega_using [hQ66]))
    fun u₃ ⟨hc₃, _, h12₃, h11₃, hg₃⟩ => ?_
  have hx : 16 + (fXc + P.Q - 1 - P.H.D) = 16 + fXc + (P.Q - 1 - P.H.D) := by omega_using [hQD]
  rw [h₂.val, sub_min _ (by omega_using [hQD]), hx] at h12₃
  exact ⟨hc₃, h11₃, h12₃, by rw [hg₃ _ (by decide) (by decide), h₂.val]⟩

/-- The digest's `D` bytes copied to `fXc`, after `Q - 1 - D` zero bytes. -/
theorem xcCopy_ok (hL : L.Ok) (hk : HOk P L) (hW : P.R.big = true) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.seq (.block (cfgOf P).xcArgs) Cfg.cpLoop) t fun u => Ctx L g m₀ u ∧ True := by
  have he := L.he
  have hnb := hL.nB
  obtain ⟨-, hQ66, hQD⟩ := P.sizesW hW
  obtain ⟨-, -, -, -, -, -, hD16, hD64, -, -, -, -, -, -, -, -, -, -⟩ := P.sizes
  have hdn : P.H.D ≤ P.I.hashLen := by rw [P.len]
  refine WP.seq (WP.mono (xcArgs_ok hL hk hW hc) fun u ⟨hcu, h11, h12, h13⟩ => ?_)
  refine WP.mono (cp_ok hL hcu (p := L.B + BitVec.ofNat 64 (16 + fXc + (P.Q - 1 - P.H.D))) (q := L.dg)
      (n := P.H.D) (by omega_using [hD16]) (by omega_using [hD64]) h13 h12 h11 ?_ (hcu.inFrW (by omega_using []) (by simp only [fXc]; omega_using [he, hQ66, hQD]))
      (safe_high L (by simp only [fXc]; omega_using []) (by simp only [fXc]; omega_using [he, hQ66, hQD]))
      (fun i hi => hcu.inDg (o := i) (n := 1) (by omega_using [hdn, hi]) (by omega_using [hD64, hi]))
      (fun i hi hcon => hL.kg _ (Offset.sub_base L.B (k := 256 + 8 * L.e) (by simp only [fXc]; omega_using [he, hQ66, hQD]) _ hcon)
        (Offset.contains_base L.dg (d := i) (n := 1) (k := P.I.hashLen) (by omega_using [hdn, hi]) (by omega_using [hD64, hi]))))
    fun _ h => ⟨h.1, trivial⟩
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 + fXc + _) (by simp only [fXc]; omega_using [hQ66]),
    Nat.mod_eq_of_lt (by simp only [fXc]; omega_using [he, hnb, hQ66])]
  simp only [fXc]; omega_using [he, hnb, hQ66, hQD]

theorem prepX_ct : RelCT isa (Two P (Tt P)) (cfgOf P).prepX (Two P (QX P)) := by
  refine two_wp ?_ fun L g m₀ t hL hk hc _ => stageX_ok hL hk hc
  rw [Cfg.prepX]
  exact (two_wp (Ψ := CpA P (fun L => L.B + BitVec.ofNat 64 (16 + fX + (P.Q - min P.H.D P.Q))) (fun L => L.dg)
      (min P.H.D P.Q)) (two_blk [] spOnly (by exact (rT P).xArgs)) fun L g m₀ t hL hk hc _ =>
    WP.mono (xArgs_ok hL hk.2 hc) fun _ ⟨c, _, _, cx, di, si⟩ => ⟨c, si, di, cx⟩).seq
    (cp_ct fun _ _ _ h => h)

theorem prepH_ct : RelCT isa (Two P (QX P)) (cfgOf P).prepH (Two P (QA P)) := by
  refine two_wp ?_ fun L g m₀ t hL hk hc hx => stageH_ok hL hk hc hx
  cases hb : P.R.big
  · rw [show (cfgOf P).prepH = .block (cfgOf P).reduce by
      simp only [Cfg.prepH, show (cfgOf P).big = false from hb, Bool.false_eq_true, ite_false]]
    exact two_blk [] spOnly (by exact (rT P).reduce hb)
  · rw [show (cfgOf P).prepH = (cfgOf P).prepC by
      simp only [Cfg.prepH, show (cfgOf P).big = true from hb, ite_true], Cfg.prepC]
    refine RelCT.assoc ((two_wp (Ψ := Tt P) ((two_wp (Ψ := CpA P
        (fun L => L.B + BitVec.ofNat 64 (16 + fXc + (P.Q - 1 - P.H.D))) (fun L => L.dg) P.H.D)
        (two_blk [] spOnly (by exact (rT P).xcArgs hb)) fun L g m₀ t hL hk hc _ =>
          xcArgs_ok hL hk hb hc).seq
        (cp_ct fun _ _ _ h => h)) fun L g m₀ t hL hk hc _ => xcCopy_ok hL hk hb hc).seq
      (conv_ct (by exact (rT P).convC hb)))

/-- The frame's body, once the arguments are saved. -/
theorem rest_ct :
    RelCT isa (Two P (Tt P)) (.seq (cfgOf P).prepX (.seq (cfgOf P).prepH (.seq (.block Cfg.initKV)
      (.seq ((cfgOf P).rekeyFull 0) (.seq ((cfgOf P).rekeyFull 1) (.seq (.block (cfgOf P).initCnt)
        (.seq (.loop (cfgOf P).tryOne (.nonzero .x .x12)) (.block Cfg.wipe))))))))
      (Two P fun L m₀ t => ∃ i, Exit P L m₀ i t) := by
  refine prepX_ct.seq (prepH_ct.seq ?_)
  refine (two_wp (Ψ := QB P) (two_blk [] spOnly ⟨_, by taint_decide⟩)
    fun _ _ _ _ hL _ hc h => stageB_ok hL hc h).seq ?_
  refine (two_wp (Ψ := QC P) ((rekeyFull_piece 0 (by exact (rT P).msgF₀)).rel fun _ _ _ _ => trivial)
    fun _ _ _ _ hL hk hc h => stageC_ok (P := P) hL hk hc h).seq ?_
  refine (two_wp (Ψ := QD P) ((rekeyFull_piece 1 (by exact (rT P).msgF₁)).rel fun _ _ _ _ => trivial)
    fun _ _ _ _ hL hk hc h => stageD_ok (P := P) hL hk hc h).seq ?_
  refine (two_wp (Ψ := fun L m₀ t => LoopInv P L m₀ 0 t) (two_blk [] spOnly (initCnt_taint _))
    fun _ _ _ _ hL _ hc h => stageE_ok (P := P) hL hc h).seq ?_
  refine tries_ct.seq ?_
  exact two_wp (two_blk [] spOnly ⟨_, by taint_decide⟩) fun _ _ _ _ hL hk hc ⟨i, h⟩ =>
    WP.mono (stageG_ok hL hk hc h) fun _ ⟨c, x⟩ => ⟨c, i, x⟩

/-! ## The whole function -/

/-- Two calls whose public data agree, in the inner frame. -/
def Entered (P : RfcHash) (ns : List String) (a b : State) : Prop :=
  ∃ s₁ s₂, (rfcP P ns).pre s₁ ∧ (rfcP P ns).pre s₂ ∧ (rfcP P ns).pub s₁ s₂ ∧ a = entered s₁ ∧ b = entered s₂

theorem save_taint : TaintOk [] Cfg.saveArgs := ⟨_, by taint_decide⟩

/-- Saving the arguments: the runs have the same layout, and stop at the same
candidate (with the addresses of the hash function's HMAC functions among
`ns`). -/
theorem save_ct {ns : List String} (hns : ∀ n ∈ [P.H.hmacInitN, P.H.updN, P.H.hmacFinN], n ∈ ns) :
    RelCT isa (Entered P ns) (.block Cfg.saveArgs) (Two P (Tt P)) := by
  intro a b ta tb a' b' ⟨s₁, s₂, h₁, h₂, ⟨hsp, h0, h1, h2, h4, h5, hres, hsy, hns'⟩, ea, eb⟩ e₁ e₂
  subst ea eb
  obtain ⟨_, hc⟩ := save_taint
  obtain ⟨ht, -⟩ := RelCT.taint (A := taint) (P := fun x y => x.sp = y.sp) (Taint.ofRegs [])
    (fun _ _ h => ⟨h, fun r hr => absurd (Taint.mem_ofRegs.mp hr) List.not_mem_nil⟩) hc _ _ _ _ _ _
    (show (entered s₁).sp = (entered s₂).sp by
      show s₁.sp - 16 - BitVec.ofNat 64 frameBytes = s₂.sp - 16 - BitVec.ofNat 64 frameBytes
      rw [hsp]) e₁ e₂
  obtain ⟨_, u₁, x₁, c₁⟩ := save_ctx h₁
  obtain ⟨_, u₂, x₂, c₂⟩ := save_ctx h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  have hfa : (fun n => if n ∈ [P.H.hmacInitN, P.H.updN, P.H.hmacFinN] then s₁.syms n else 0) =
      fun n => if n ∈ [P.H.hmacInitN, P.H.updN, P.H.hmacFinN] then s₂.syms n else 0 :=
    funext fun n => by
      split
      · next h => exact hns' n (hns n h)
      · rfl
  have hl : layOf P s₁ = layOf P s₂ := by
    simp only [layOf, lay, hsp, h0, h1, h2, h4, h5, hsy, hfa]
  have hr : (result P.I s₁.mem (s₁.gpr .x1) (s₁.gpr .x2)).2 = (result P.I s₂.mem (s₁.gpr .x1) (s₁.gpr .x2)).2 := by
    rw [hres, h1, h2]
  exact ⟨ht, ⟨layOf P s₁, s₁.gpr, s₂.gpr, s₁.mem, s₂.mem⟩, lay_ok rfl h₁, hOk_lay P s₁,
    congrArg (fun x => if x = 0 then P.I.tries - 1 else x - 1) hr, c₁, by rw [hl]; exact c₂, trivial, trivial⟩

/-- Runs whose public data agree (with the addresses of the hash function's
HMAC functions among `ns`) have the same layout, and stop at the same
candidate. -/
theorem sign_ct {ns : List String} (hns : ∀ n ∈ [P.H.hmacInitN, P.H.updN, P.H.hmacFinN], n ∈ ns) :
    ConstantTime isa (rfcP P ns).pre (rfcP P ns).pub (cfgOf P).sign := by
  refine VG.RelCT.constantTime (Q := fun _ _ => True) (RelCT.pushFrame (R := fun _ _ => True)
    (fun _ _ h => h.2.2.1) (RelCT.alloc (R := fun _ _ => True) ?_))
  rw [Cfg.body]
  refine ((save_ct hns).seq rest_ct).mono ?_ fun _ _ _ => trivial
  rintro _ _ ⟨_, _, ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩, rfl, rfl⟩
  exact ⟨s₁, s₂, h₁, h₂, hp, rfl, rfl⟩

end VG.Proof.Ecdsa.Rfc6979.AArch64

end

end

/-!
# Deterministic ECDSA on AArch64: the HMAC of a table

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Table.lean`):
`vg_ecdsa_<curve>_sign` (`signCodeT`) loads `D` and `B`, the digest length
and HMAC's block size, from the table `hmac` (its words 4 and 5, to `x6`
and `x7`) and runs the one body (`cfgT`, the same for every hash function),
which calls the table's functions. For the variants `vs` of the hash
functions that pass the registration's checks (`OK`), the table of each
variant `w` makes the body the code for `w`'s hash function (`hashOf`, with
`cfgT_eq`, which holds by `rfl`), which meets the contract with that hash
function fixed (`sign_ok`, `sign_ct`). `tabK` states that contract for
whichever of the tables `hmac` holds, on entry; `TableSpec.lean` shows
`TableInstance.signContract` implies it. No instruction of the function or
of those it calls writes a callee-saved SIMD register (`signT_keepsV`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 (MdHash)
open VG.Proof.HmacTable.AArch64 (tables fnsOf names Coh tableOf mem_names tabOK_of held_tableOf hashAt_tableOf)

/-! ## The code -/

/-- The body, on the curve `R`, with the bound on candidates `tries` and the
tables of `vs`: the same for every hash function. -/
def cfgT (R : RfcCurve) (tries : Nat) (vs : List MdHash) : Cfg where
  f := fnsOf vs
  w := R.E.n
  len := R.E.C.len
  big := R.big
  sh := R.sh
  n := R.E.C.n
  tries := tries
  coreN := R.coreN
  coreC := R.coreC

/-- `vg_ecdsa_<curve>_sign`. -/
def signCodeT (R : RfcCurve) (tries : Nat) (vs : List MdHash) : Prog isa := signCode (cfgT R tries vs)

/-- The stack it uses. -/
def stackT : Nat := 256 + 8 * 48

/-! ## The variants -/

/-- What the code needs of a variant `w`: its hash function has HMAC (over
`w`'s block size), of one of the digest lengths and block sizes the frame
holds, and the working space of `w`'s HMAC fits the one in `scratch`. -/
def WOk (w : MdHash) : Prop :=
  (match Spec.HmacTable.hmacOf w.mgf.G with
    | some F => F.blockSize = w.H.P.B
    | none => False) ∧
  (w.H.D, w.H.P.B) ∈ shapes ∧ 8 * w.H.W ≤ 1872 ∧ w.ok.stream.Wb ≤ 1872

instance (w : MdHash) : Decidable (WOk w) := by
  unfold WOk; cases Spec.HmacTable.hmacOf w.mgf.G <;> infer_instance

/-- What the registrations check of the variants whose tables the function
takes. -/
def OK (vs : List MdHash) : Prop := Coh vs ∧ (names vs).length < 2 ^ 32 ∧ vs ≠ [] ∧ ∀ w ∈ vs, WOk w

instance (vs : List MdHash) : Decidable (OK vs) := by unfold OK; infer_instance

theorem mdHashes_sub {G : Spec.Mgf1.Hash} (h : G ∈ Proof.Pbkdf2.Md.AArch64.mdHashes) : G ∈ Spec.Mgf1.hashes := by
  simp only [Proof.Pbkdf2.Md.AArch64.mdHashes, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Spec.Mgf1.hashes]

/-- The HMAC of `w`'s hash function. -/
theorem WOk.hmac {w : MdHash} (hw : WOk w) : Spec.HmacTable.hmacOf w.mgf.G = some w.ok.SH.H := by
  have h := hw.1
  revert h
  cases hF : Spec.HmacTable.hmacOf w.mgf.G with
  | none => intro h; exact h.elim
  | some F =>
    intro hb
    have hh := Spec.HmacTable.hmacOf_hash _ (mdHashes_sub w.mgf.mem) F hF
    congr 1
    cases F
    rw [Spec.Hmac.HashFunction.mk.injEq]
    exact ⟨hb.trans w.ok.hB.symm, funext fun x => (congrFun hh x).trans (w.mgf.hash x)⟩

/-- HMAC's block size, as the table holds it. -/
theorem WOk.blockSize {w : MdHash} (hw : WOk w) : Spec.HmacTable.blockSize w.mgf.G = w.H.P.B := by
  simp only [Spec.HmacTable.blockSize, hw.hmac, Option.map_some, Option.getD_some]
  exact w.ok.hB

/-- The instance with `w`'s hash function fixed. -/
def instOf (T : Spec.Ecdsa.Rfc6979.TableInstance) (w : MdHash) : Proof.Ecdsa.Rfc6979.Instance where
  ecdsa := T.ecdsa
  hash := w.ok.SH.H
  hashLen := w.H.D
  tries := T.tries

/-- What each curve's file shows of its curve and instance. -/
structure CurveT (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) : Prop where
  ecdsa : T.ecdsa = R.inst
  tries_pos : 0 < T.tries
  tries_lt : T.tries < 2 ^ 16

/-- The proof's hash function: `w`, the functions an indirect call of the
table's reaches those of `vs`. -/
def hashOf {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} (hC : CurveT R T) (vs : List MdHash)
    (w : MdHash) (hw : WOk w) : RfcHash where
  R := R
  I := instOf T w
  H := w.H
  ok := w.ok
  C := w.C
  satI := by rw [w.hSH, w.hW]; exact w.hmacInit.2.2
  satF := by rw [w.hSH, w.hW]; exact w.hmacFin.2.2
  f := fnsOf vs
  ecdsa := hC.ecdsa
  hash := rfl
  len := rfl
  tries_pos := hC.tries_pos
  tries_lt := hC.tries_lt
  hDB := hw.2.1
  hS := by have := w.ok.N_le; have := w.ok.B_le; show _ + _ ≤ 192; omega_arith
  hW := hw.2.2.1
  hWb := hw.2.2.2

/-- The body for `w`'s hash function is the same as for every other. -/
theorem cfgT_eq {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} (hC : CurveT R T) (vs : List MdHash)
    {w : MdHash} (hw : WOk w) : cfgT R T.tries vs = cfgOf (hashOf hC vs w hw) := rfl

/-- RFC 6979's result with `w`'s hash function fixed is the table's. -/
theorem tresult_eq (T : Spec.Ecdsa.Rfc6979.TableInstance) (w : MdHash) (m : Mem) (d dg : Addr) :
    (instOf T w).result m d dg = T.result w.mgf.G w.ok.SH.H m d dg := by
  simp only [Proof.Ecdsa.Rfc6979.Instance.result, Spec.Ecdsa.Rfc6979.TableInstance.result, instOf, w.mgf.len]

/-! ## The contract on entry -/

/-- The state `entry` leaves, with the table of `w`: `D` in `x6` and `B` in `x7`. -/
def entryOf (w : MdHash) (s : State) : State :=
  { s with gpr := fun r => if r = .x6 then BitVec.ofNat 64 w.H.D
    else if r = .x7 then BitVec.ofNat 64 w.H.P.B else s.gpr r }

/-- What the contract with the table of `w` says on entry: the contract the
proof is written against, of the state `entry` leaves, and the table's data. -/
def PreW (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List MdHash) (w : MdHash) (s : State) :
    Prop :=
  (rfcAArch64 R.E (instOf T w) stackT (tabFacts w.H (fnsOf vs)) (names vs)).pre (entryOf w s) ∧
    s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G) ∧
    s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 w.H.D ∧
    s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 w.H.P.B

open Spec.Weierstrass Spec.Ecdsa in
/-- The contract with whichever of the tables of `vs` the table at `x5` is. -/
def tabK (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List MdHash) : Contract isa where
  pre s := ∃ w ∈ vs, WOk w ∧ PreW R T vs w s
  post s s' := ∀ w ∈ vs, WOk w → PreW R T vs w s →
    match (T.result w.mgf.G w.ok.SH.H s.mem (s.gpr .x1) (s.gpr .x2)).1 with
    | some rs => (s'.gpr .x0).setWidth 32 = 1 ∧
        bytesAt s'.mem (s.gpr .x0) (2 * T.ecdsa.curve.len) = encode T.ecdsa.curve rs
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧
        bytesAt s'.mem (s.gpr .x0) (2 * T.ecdsa.curve.len) = List.replicate (2 * T.ecdsa.curve.len) 0
  pub s₁ s₂ := ∃ w ∈ vs, WOk w ∧ PreW R T vs w s₁ ∧ PreW R T vs w s₂ ∧
    (rfcAArch64 R.E (instOf T w) stackT (tabFacts w.H (fnsOf vs)) (names vs)).pub
      (entryOf w s₁) (entryOf w s₂)

/-! ## From the entry to the frame -/

/-- The contract the proof is written against, of a state with the same
arguments, stack pointer, regions, memory and symbols. -/
theorem rfc_congr {E : Impl.Ecdsa.AArch64.Cfg} {I : Proof.Ecdsa.Rfc6979.Instance} {S : Nat}
    {H : Impl.Pbkdf2.Md.AArch64.Hash} {f : Impl.RsaOaep.AArch64.Mgf1.Table.Fns} {ns : List String} {s t : State}
    (h : (rfcAArch64 E I S (tabFacts H f) ns).pre s)
    (hg : ∀ r ∈ [Reg.x0, .x1, .x2, .x4, .x5, .x6, .x7], t.gpr r = s.gpr r) (hsp : t.sp = s.sp)
    (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hm : t.mem = s.mem) (hsy : t.syms = s.syms) :
    (rfcAArch64 E I S (tabFacts H f) ns).pre t := by
  have e₀ := hg .x0 (by simp); have e₁ := hg .x1 (by simp); have e₂ := hg .x2 (by simp)
  have e₄ := hg .x4 (by simp); have e₅ := hg .x5 (by simp); have e₆ := hg .x6 (by simp)
  have e₇ := hg .x7 (by simp)
  simp only [rfcAArch64, TblOk, tabFacts] at h ⊢
  rw [e₀, e₁, e₂, e₄, e₅, e₆, e₇, hsp, hrd, hwr, hm, hsy]
  exact h

variable {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List MdHash}

/-- A table's index names its hash function. -/
theorem index_inj {G G' : Spec.Mgf1.Hash} (hG : G ∈ Proof.Pbkdf2.Md.AArch64.mdHashes)
    (hG' : G' ∈ Proof.Pbkdf2.Md.AArch64.mdHashes) (h : Spec.HashTable.index G = Spec.HashTable.index G') :
    G = G' := by
  simp only [Proof.Pbkdf2.Md.AArch64.mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hG hG'
  rcases hG with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hG' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | (exfalso; revert h; decide)

theorem index_lt {G : Spec.Mgf1.Hash} (hG : G ∈ Proof.Pbkdf2.Md.AArch64.mdHashes) :
    Spec.HashTable.index G < 8 := by
  simp only [Proof.Pbkdf2.Md.AArch64.mdHashes, List.mem_cons, List.not_mem_nil, or_false] at hG
  rcases hG with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Two variants whose tables have the same index have the same hash function. -/
theorem same_hash {w w' : MdHash} (hw : WOk w) (hw' : WOk w')
    (h : BitVec.ofNat 64 (Spec.HashTable.index w'.mgf.G) = BitVec.ofNat 64 (Spec.HashTable.index w.mgf.G)) :
    w'.mgf.G = w.mgf.G ∧ w'.ok.SH.H = w.ok.SH.H := by
  have e : Spec.HashTable.index w'.mgf.G = Spec.HashTable.index w.mgf.G := by
    have h₁ := index_lt w.mgf.mem; have h₂ := index_lt w'.mgf.mem
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h₂]), Nat.mod_eq_of_lt (by omega_using [h₁])] at this
    exact this
  have hG := index_inj w'.mgf.mem w.mgf.mem e
  refine ⟨hG, ?_⟩
  have h₁ := hw.hmac; have h₂ := hw'.hmac
  rw [hG] at h₂
  exact Option.some.inj (h₂.symm.trans h₁)

/-- `entry`'s effect, from the state on entry `σ`. -/
def EntryF (σ u : State) : Prop :=
  (∀ r, r ≠ .x6 → r ≠ .x7 → u.gpr r = σ.gpr r) ∧
    u.gpr .x6 = σ.mem.readW (σ.gpr .x5 + BitVec.ofNat 64 32) 64 ∧
    u.gpr .x7 = σ.mem.readW (σ.gpr .x5 + BitVec.ofNat 64 40) 64 ∧ u.mem = σ.mem ∧ u.rd = σ.rd ∧ u.wr = σ.wr ∧
    u.sp = σ.sp ∧ u.syms = σ.syms

/-- `entry`: `D` and `B` from the table to `x6` and `x7`. -/
theorem entry_ok {w : MdHash} {s : State} (h : PreW R T vs w s) : WP isa (.block entry) s (EntryF s) := by
  obtain ⟨⟨hrd, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, n5, -⟩, -⟩ := h
  have hin : ∀ o, o + 8 ≤ 48 → InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 o) 8 := fun o ho =>
    ⟨⟨s.gpr .x5, 48⟩, by
      rw [show s.rd = (entryOf w s).rd from rfl, hrd]
      exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))),
      Offset.contains_base _ ho (by have : (entryOf w s).gpr .x5 = s.gpr .x5 := rfl; omega_using [ho])⟩
  have h32 := hin 32 (by decide)
  have h40 := hin 40 (by decide)
  rw [show entry = [.ldr .x .x6 .x5 32, .ldr .x .x7 .x5 40] from rfl]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, Nat.reduceMod, Nat.reduceMul,
    Nat.reduceLT, and_self, ite_true, Option.bind_some, State.load, Size.bits, BitVec.setWidth_eq,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, reduceCtorEq, ite_false, h32, h40,
    Option.map_some, read8, Option.some.injEq, exists_eq_left']
  refine ⟨fun r h₁ h₂ => ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
    simp only [RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write,
      reduceCtorEq, ite_false, ite_true, BitVec.setWidth_eq]
  simp only [h₁, h₂, ite_false]

/-- After `entry`: the contract with `w`'s hash function fixed. -/
theorem pre_at (hC : CurveT R T) {w : MdHash} (hw : WOk w) {s t : State} (hp : PreW R T vs w s)
    (hf : EntryF s t) : (rfcP (hashOf hC vs w hw) (names vs)).pre t := by
  obtain ⟨hg, h6, h7, hm, hrd, hwr, hsp, hsy⟩ := hf
  exact rfc_congr hp.1 (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg _ (by decide) (by decide)
    · exact hg _ (by decide) (by decide)
    · exact hg _ (by decide) (by decide)
    · exact hg _ (by decide) (by decide)
    · exact hg _ (by decide) (by decide)
    · exact h6.trans hp.2.2.1
    · exact h7.trans hp.2.2.2) hsp hrd hwr hm hsy

theorem pres_ne {r : Reg} (hr : r ∈ preserved) {x : Reg} (hx : x ∉ preserved) : r ≠ x :=
  fun h => hx (h ▸ hr)

/-- `vg_ecdsa_<curve>_sign` meets `tabK`, and keeps the callee-saved
registers and the stack pointer. -/
theorem signT_ok (hC : CurveT R T) {s : State} (h : (tabK R T vs).pre s) :
    WP isa (signCodeT R T.tries vs) s fun s' => ((∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ s'.sp = s.sp) ∧
      (tabK R T vs).post s s' := by
  obtain ⟨w, -, hw, hp⟩ := h
  unfold signCodeT signCode
  refine WP.seq (WP.mono (entry_ok hp) fun t hf => ?_)
  rw [cfgT_eq hC vs hw]
  have hpre := pre_at hC hw hp hf
  obtain ⟨hg, -, -, hm, -, -, hsp, -⟩ := hf
  refine WP.mono (sign_ok hpre) fun s' ⟨⟨hcs, hsp'⟩, hpost⟩ => ⟨⟨fun r hr => ?_, hsp'.trans hsp⟩, ?_⟩
  · rw [hcs r hr, hg r (pres_ne hr (by decide)) (pres_ne hr (by decide))]
  · intro w' _ hw' hp'
    obtain ⟨hG, hH⟩ := same_hash hw hw' (hp'.2.1.symm.trans hp.2.1)
    have e₁ := hg .x1 (by decide) (by decide)
    have e₂ := hg .x2 (by decide) (by decide)
    have e₀ := hg .x0 (by decide) (by decide)
    rw [hG, hH]
    have hpost' : match ((instOf T w).result t.mem (t.gpr .x1) (t.gpr .x2)).1 with
      | some rs => (s'.gpr .x0).setWidth 32 = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (t.gpr .x0)
          (2 * T.ecdsa.curve.len) = Spec.Ecdsa.encode T.ecdsa.curve rs
      | none => (s'.gpr .x0).setWidth 32 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (t.gpr .x0)
          (2 * T.ecdsa.curve.len) = List.replicate (2 * T.ecdsa.curve.len) 0 := hpost
    rw [tresult_eq, e₁, e₂, e₀, hm] at hpost'
    exact hpost'

/-! ## Constant time -/

/-- Public data that agree. -/
theorem pub_trans {E : Impl.Ecdsa.AArch64.Cfg} {I : Proof.Ecdsa.Rfc6979.Instance} {S S' : Nat}
    {F F' : State → Prop} {ns : List String} {a b c : State} (h₁ : (rfcAArch64 E I S F ns).pub a b)
    (h₂ : (rfcAArch64 E I S F ns).pub a c) : (rfcAArch64 E I S' F' ns).pub b c := by
  obtain ⟨p₁, p₂, p₃, p₄, p₅, p₆, p₇, p₈, p₉⟩ := h₁
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, q₈, q₉⟩ := h₂
  exact ⟨p₁.symm.trans q₁, p₂.symm.trans q₂, p₃.symm.trans q₃, p₄.symm.trans q₄, p₅.symm.trans q₅,
    p₆.symm.trans q₆, p₇.symm.trans q₇, p₈.symm.trans q₈, fun n hn => (p₉ n hn).symm.trans (q₉ n hn)⟩

theorem pub_refl {E : Impl.Ecdsa.AArch64.Cfg} {I : Proof.Ecdsa.Rfc6979.Instance} {S : Nat}
    {F : State → Prop} {ns : List String} (a : State) : (rfcAArch64 E I S F ns).pub a a :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

/-- Public data of a state with the same arguments, stack pointer, memory and symbols. -/
theorem pub_congr {E : Impl.Ecdsa.AArch64.Cfg} {I : Proof.Ecdsa.Rfc6979.Instance} {S S' : Nat}
    {F F' : State → Prop} {ns : List String} {a b c : State} (h : (rfcAArch64 E I S F ns).pub a b)
    (hg : ∀ r ∈ [Reg.x0, .x1, .x2, .x4, .x5], c.gpr r = b.gpr r) (hsp : c.sp = b.sp) (hm : c.mem = b.mem)
    (hsy : c.syms = b.syms) : (rfcAArch64 E I S' F' ns).pub a c := by
  have e₀ := hg .x0 (by simp); have e₁ := hg .x1 (by simp); have e₂ := hg .x2 (by simp)
  have e₄ := hg .x4 (by simp); have e₅ := hg .x5 (by simp)
  simp only [rfcAArch64] at h ⊢
  rw [e₀, e₁, e₂, e₄, e₅, hsp, hm, hsy]
  exact h

theorem entry_taint : TaintOk [.x5] entry := ⟨_, by taint_decide⟩

/-- Runs whose public data agree: the same table, read at the same address. -/
theorem entry_ct :
    RelCT isa (fun s₁ s₂ => (tabK R T vs).pre s₁ ∧ (tabK R T vs).pre s₂ ∧ (tabK R T vs).pub s₁ s₂) (.block entry)
      fun u₁ u₂ => ∃ σ₁ σ₂, ((tabK R T vs).pre σ₁ ∧ (tabK R T vs).pre σ₂ ∧ (tabK R T vs).pub σ₁ σ₂) ∧
        EntryF σ₁ u₁ ∧ EntryF σ₂ u₂ := by
  obtain ⟨_, ht⟩ := entry_taint
  refine (RelCT.wpDep (F := EntryF) (RelCT.taint (A := taint) (Taint.ofRegs [.x5])
      (fun _ _ ⟨_, _, ⟨_, _, _, _, _, ⟨p₁, _, _, _, _, p₆, _⟩⟩⟩ => ⟨p₁, fun r hr => by
        simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst hr; exact p₆⟩) ht)
    fun _ _ ⟨⟨_, _, _, h₁⟩, ⟨_, _, _, h₂⟩, _⟩ => ⟨entry_ok h₁, entry_ok h₂⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2

/-- `vg_ecdsa_<curve>_sign` is constant time: runs whose public data agree
take the same table, whose hash function's code is the body, constant time
for it. -/
theorem signT_ct (hC : CurveT R T) :
    ConstantTime isa (tabK R T vs).pre (tabK R T vs).pub (signCodeT R T.tries vs) := by
  refine VG.RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold signCodeT signCode
  refine entry_ct.seq ?_
  intro u₁ u₂ t₁ t₂ u₁' u₂' ⟨σ₁, σ₂, ⟨_, _, w, hv, hw, p₁, p₂, hpub⟩, f₁, f₂⟩ e₁ e₂
  rw [cfgT_eq hC vs hw] at e₁ e₂
  have hns : ∀ n ∈ [(hashOf hC vs w hw).H.hmacInitN, (hashOf hC vs w hw).H.updN,
      (hashOf hC vs w hw).H.hmacFinN], n ∈ names vs := by
    have := mem_names hv
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl
    · exact this.1
    · exact this.2.1
    · exact this.2.2
  have reg : ∀ {σ u : State}, EntryF σ u → ∀ r ∈ [Reg.x0, .x1, .x2, .x4, .x5],
      u.gpr r = (entryOf w σ).gpr r := fun {σ u} f r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact f.1 _ (by decide) (by decide)
  have pu : (rfcP (hashOf hC vs w hw) (names vs)).pub u₁ u₂ :=
    pub_trans (a := entryOf w σ₁) (S := stackT) (F := tabFacts w.H (fnsOf vs))
      (pub_congr (pub_refl (S := stackT) (F := tabFacts w.H (fnsOf vs)) _) (reg f₁) f₁.2.2.2.2.2.2.1
        f₁.2.2.2.1 f₁.2.2.2.2.2.2.2)
      (pub_congr hpub (reg f₂) f₂.2.2.2.2.2.2.1 f₂.2.2.2.1 f₂.2.2.2.2.2.2.2)
  exact ⟨sign_ct hns u₁ u₂ t₁ t₂ u₁' u₂' (pre_at hC hw p₁ f₁) (pre_at hC hw p₂ f₂) pu e₁ e₂, trivial⟩

/-! ## No instruction writes a callee-saved SIMD register -/

theorem fnsOk_of (vs : List MdHash) : FnsOk (fnsOf vs).init ∧ FnsOk (fnsOf vs).upd ∧ FnsOk (fnsOf vs).fin := by
  refine ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩ <;> obtain ⟨w, -, rfl⟩ := List.mem_map.mp hq
  · exact w.ok.hmacInit_keepsV
  · exact w.ok.updKeepsV
  · exact w.ok.hmacFin_keepsV

/-- No instruction of `vg_ecdsa_<curve>_sign`, or of the functions it calls,
writes a callee-saved SIMD register. -/
theorem signT_keepsV (R : RfcCurve) (tries : Nat) (vs : List MdHash) :
    (signCodeT R tries vs).allInstrs keepsV = true :=
  sign_okP (c := cfgT R tries vs) R.blk (fnsOk_of vs) R.coreKeepsV

end VG.Proof.Ecdsa.Rfc6979.AArch64

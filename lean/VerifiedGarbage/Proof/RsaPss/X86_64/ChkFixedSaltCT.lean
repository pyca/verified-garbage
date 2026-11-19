module

import VerifiedGarbage.Proof.RsaPss.X86_64.FixedHash
import VerifiedGarbage.Proof.RsaPss.X86_64.CtHashOk
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.RsaPss.X86_64.SignPro
import VerifiedGarbage.Proof.RsaPss.X86_64.SignEnc
import VerifiedGarbage.Proof.Framework.X86_64.Syms
public import VerifiedGarbage.Proof.RsaPss.X86_64.ChkFrame
public import VerifiedGarbage.Proof.RsaPss.X86_64.CtBase
import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
public import VerifiedGarbage.Proof.RsaPss.X86_64.PrefixCheck
import VerifiedGarbage.Proof.RsaPss.MgfBytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
public import VerifiedGarbage.Proof.RsaPss.X86_64.Params
public import VerifiedGarbage.Proof.RsaPss.X86_64.VerifyFrame
public import VerifiedGarbage.Proof.RsaPss.X86_64.Mgf
public import VerifiedGarbage.Proof.RsaPss.X86_64.TabCall
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Core
meta import VerifiedGarbage.Proof.RsaPss.X86_64.CtHashOk
meta import VerifiedGarbage.Proof.RsaPss.X86_64.CtBase
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Core
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Sha256.X86_64.Compress
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Framework.OffsetBelow
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.X86_64.Frame
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Hmac.Generic.Implies
meta import VerifiedGarbage.Proof.MdStream.X86_64.FinalizeCT
meta import VerifiedGarbage.Proof.MdStream.X86_64.UpdateCT
meta import VerifiedGarbage.Proof.MdStream.X86_64.Words
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PadW
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Words
meta import VerifiedGarbage.Proof.Sha256.StateMem
meta import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Sha256.X86_64.Compress
public import VerifiedGarbage.Proof.RsaPss.X86_64.Checks
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
meta import VerifiedGarbage.Proof.RsaPss.X86_64.Checks
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.X86_64.Wp

/-! ### `RsaPss.X86_64.ChkCtBack`, which this module and modules that import it used -/

section

/-! ### `RsaPss.X86_64.VerifyFixed`, which this module and modules that import it used -/

section

/-!
# RSASSA-PSS verification on x86-64: the taint checks of the pieces that do
not depend on the hash function
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64

/-- The prologue of `shift`. -/
def shiftPro : List Instr :=
  [.mov .rax (.mem (sp sPos)), .alu .add .rax (.imm 1), .store (sp sA) .rax, .mov32 .rax (.imm 1),
    .store (sp sD) .rax, .mov32 .rax (.imm 10), .store (sp sJ) .rax]

theorem shift_eq (H : Impl.Pbkdf2.Md.X86_64.Hash) :
    shift H = .seq (.block shiftPro) (.loop (.seq (shiftPass H) (.block nextPass)) .ne) := rfl

/-- The checks. -/
structure VFixed : Prop where
  pro : ∃ hc, (taint.check (pT 1 [] [.rdi, .rsi, .rdx, .rcx, .r8, .r9]) (.block (verifyPrologue ++ n0)) hc).isSome
    = true
  fail : ∃ hc, (taint.check (pT 1 [] []) verifyFail hc).isSome = true
  acc0 : ∃ hc, (taint.check (pT 1 [17, 21, 23, 25, 26] []) (.block acc0) hc).isSome = true
  clearTop : ∃ hc, (taint.check (pT 1 [23] []) (.block clearTop) hc).isSome = true
  posScan : ∃ hc, (taint.check (pT 1 [23, 24] []) posScan hc).isSome = true
  shiftPro : ∃ hc, (taint.check (pT 1 [] []) (.block shiftPro) hc).isSome = true
  nextPass : ∃ hc, (taint.check (pT 1 [] []) (.block nextPass) hc).isSome = true
  restore : ∃ hc, (taint.check (pT 1 [] []) (.block restoreRegs) hc).isSome = true
  scanAny : ∃ hc, (taint.check (pT 1 [35] [])
    (.block [.mov .rax (.mem (sp sAny)), .alu .test .rax (.reg .rax)]) hc).isSome = true
  scanLen : ∃ hc, (taint.check (pT 1 [24, 36] [])
    (.block [.mov .rax (.mem (sp sSlen)), .alu .cmp .rax (.mem (sp sDb))]) hc).isSome = true

theorem vFixed : VFixed :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

end VG.Proof.RsaPss.X86_64

end

end

/-! ### `RsaPss.X86_64.CtHashCT`, which this module and modules that import it used -/

section

/-!
# RSASSA-PSS on x86-64: `ctHash` is constant time

Two runs of `ctHash` with the same frame, working space, writable regions
and number of blocks (`HA`), hashing messages of any lengths that fit in
them, leak the same trace (`ctHash_ct`): the pieces between the calls are
checked by the taint analysis (`HashChecks`, `FixedChecks`), the calls
through the table's slots are of the same function in both runs
(`two_scall`), constant time by its contract, and the loop over the blocks
goes the same way in both runs.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Proof.Bignum (off)
open VG.Proof.Bignum.X86_64 (Two two_post two_map two_mono two_loop)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (initK)
open VG.Proof.MdStream.X86_64 (compressK)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

/-! ## A call through a slot in two runs -/

/-- `Pub` after a piece that changes only registers but `rsp`. -/
theorem Pub.keepM {F S : Addr} {rest : List Region} {ws : List (Nat × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} {t t' : State} (h : Pub F S rest ws [] X t)
    (hsp : t'.gpr .rsp = t.gpr .rsp) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem) : Pub F S rest ws [] X t' :=
  ⟨h.L.congr hsp hwr (by rw [hm]), hwr.trans h.wr, by rw [hm]; exact h.W, fun _ hp => by cases hp⟩

/-- A public word, read. -/
theorem pub_slot {F S : Addr} {rest : List Region} {ws : List (Nat × BitVec 64)} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} {t : State} (h : Pub F S rest ws rs X t) {d k : Nat}
    (hd : d = 8 * k) (hk : k < nW) {v : BitVec 64} (hv : (k, v) ∈ ws) : t.mem.readW (off F d) 64 = v := by
  obtain ⟨V, W, R, hw, -⟩ := h.W
  rw [R.rd k hd hk]; exact hw _ hv

/-- The call through the slot `s` in two runs whose slot holds the same
address `addr a`, that of the function `nm` in both: constant time when that
call is, from the states the load of its address leaves. -/
theorem two_scall (n : Nat) {α : Type} {Φ : α → State → Prop} {s : Nat} (hs8 : s + 8 ≤ frameBytes)
    {ts : List (String × Prog isa)} {nm : String} {c : Prog isa} (F S : α → Addr) (rest : α → List Region)
    (addr : α → Addr)
    (hv : ∀ a t, Φ a t → Lay t (F a) (S a) ∧ t.wr = ⟨F a, frameBytes⟩ :: rest a ∧ RestOk n (F a) (rest a) ∧
      t.mem.readW (off (F a) s) 64 = addr a ∧ t.syms nm = addr a ∧
      ts.find? (fun q => t.syms q.1 == t.syms nm) = some (nm, c))
    (htaint : ∃ hc, (taint.check (pT n [] []) (.block [.mov .r11 (.mem (sp s))]) hc).isSome = true)
    (hcall : RelCT isa (Two fun a t => ∃ t₀, Φ a t₀ ∧ Keep [.r11] t₀ t ∧ t.mem = t₀.mem ∧ t.syms = t₀.syms)
      (.call nm c) fun _ _ => True) :
    RelCT isa (Two Φ) (scall s ts) fun _ _ => True := by
  obtain ⟨_, ht⟩ := htaint
  unfold scall
  refine RelCT.seq (two_post (Ψ := fun a t => (∃ t₀, Φ a t₀ ∧ Keep [.r11] t₀ t ∧ t.mem = t₀.mem ∧
      t.syms = t₀.syms) ∧ t.gpr .r11 = addr a ∧ ts.find? (fun q => t.syms q.1 == addr a) = some (nm, c))
    (two_pub0 n [] F rest (fun _ => []) (fun a t h => ⟨(hv a t h).1.rsp, (hv a t h).2.1, fun _ hp => by cases hp⟩)
      (fun a t h => (hv a t h).2.2.1) (fun _ => rfl) ht) fun a t h => ?_) ?_
  · obtain ⟨L, -, -, hw, hn, hf⟩ := hv a t h
    refine WP.mono (WP.keep [.r11] (Q := fun t' => t'.gpr .r11 = addr a ∧ t'.mem = t.mem ∧ t'.syms = t.syms)
      ?_ rfl) fun t' ⟨⟨h11, hm, hsy⟩, kk⟩ => ⟨⟨t, h, kk, hm, hsy⟩, h11, by rw [hsy, ← hn]; exact hf⟩
    xrun [ea_sp, L.rsp, L.ld (d := s) hs8, hw, setReg_syms]
  · cases ts with
    | nil => exact RelCT.of_false fun s₁ s₂ ⟨a, h₁, _⟩ => by simp at h₁
    | cons q ts =>
      exact RelCT.icalls_of_call (hcall.mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, h₁.1, h₂.1⟩) fun _ _ h => h)
        fun s₁ s₂ ⟨a, h₁, h₂⟩ => ⟨addr a, by simp only [icall, h₁.2.1], by simp only [icall, h₂.2.1],
          h₁.2.2, h₂.2.2, rfl⟩

/-! ## The anchor -/

/-- What two runs of `ctHash` share: the frame, the working space, the
writable regions after the frame, the number of blocks and the addresses
of statics. -/
structure HA where
  F : Addr
  S : Addr
  rest : List Region
  nbm : Nat
  sy : String → Addr

variable {H : Hash} (hH : HashOK H) (K : Callees H) {dn : String} {f : MdFns} (hdk : DigOK H) (n : Nat)

variable (H dn) in
/-- The public words: `scratch`, the number of blocks, and the slots of the
table of `MdHash`. -/
def hws (a : HA) : List (Nat × BitVec 64) :=
  [(21, a.S), (28, BitVec.ofNat 64 a.nbm), (8, a.sy H.initN), (9, a.sy H.compN), (10, a.sy dn)]

variable (H dn f) in
/-- The anchor fits `ctHash`, and the calls of `f` reach `H`'s functions. -/
def HOk (a : HA) : Prop := RestOk n a.F a.rest ∧ 1 ≤ a.nbm ∧ a.nbm * H.P.B ≤ 2048

variable (H dn f) in
/-- A run's symbols `sy'`: the calls of `f` reach `H`'s functions, whose
addresses are the anchor's, `sy`. The runs agree on these names alone. -/
def SyH (sy sy' : String → Addr) : Prop :=
  HTF H dn f sy' ∧ sy' H.initN = sy H.initN ∧ sy' H.compN = sy H.compN ∧ sy' dn = sy dn

theorem SyH.tr {sy s₁ s₂ : String → Addr} (h : SyH H dn f sy s₂) (e : s₁ = s₂) : SyH H dn f sy s₁ := e ▸ h

variable (H dn f) in
/-- At the start, and until the length field: the message's length `ℓ`
(secret) fits in the blocks. -/
def HE (a : HA) (t : State) : Prop :=
  HOk H n a ∧ Pub a.F a.S a.rest (hws H dn a) []
    (fun _ W => ∃ ℓ, W 27 = BitVec.ofNat 64 ℓ ∧ ℓ + 1 + H.P.L ≤ a.nbm * H.P.B) t ∧ SyH H dn f a.sy t.syms

/-- The taint checks of the pieces that do not depend on the hash function. -/
structure FixedChecks (n : Nat) : Prop where
  scrSt : ∃ hc, (taint.check (pT n [21, 28, 8, 9, 10] []) (.block (scr .rdi oSt)) hc).isSome = true
  startB : ∃ hc, (taint.check (pT n [21, 28, 8, 9, 10] []) (.block [.mov32 .rax (.imm 0), .store (sp sB) .rax])
    hc).isSome = true
  nextB : ∃ hc, (taint.check (pT n [21, 28, 8, 9, 10, 29] []) (.block nextBlock) hc).isSome = true
  digArgs : ∃ hc, (taint.check (pT n [21] []) (.block (scr .rdi oSel ++ scr .rsi oDig)) hc).isSome = true
  digSt : ∃ hc, (taint.check (pT n [21] []) (.block (scr .rdi oSt ++ scr .rsi oDig)) hc).isSome = true
  ld : ∀ s, s = sIniH ∨ s = sCmpH ∨ s = sDigH ∨ s = sIniG ∨ s = sUpdG ∨ s = sFinG →
    ∃ hc, (taint.check (pT n [] []) (.block [.mov .r11 (.mem (sp s))]) hc).isSome = true
  mgfIni : ∃ hc, (taint.check (pT n [21] []) (.block (Impl.Mgf1.X86_64.initArgs mgfLay)) hc).isSome = true
  mgfSrc : ∃ hc, (taint.check (pT n [21, 29, 30] []) (.block (Impl.Mgf1.X86_64.updSrcArgs mgfLay)) hc).isSome
    = true
  mgfCtr : ∃ hc, (taint.check (pT n [21, 30, 31] []) (.block (Impl.Mgf1.X86_64.updCtrArgs mgfLay)) hc).isSome
    = true
  mgfFin : ∃ hc, (taint.check (pT n [21, 30] []) (.block (Impl.Mgf1.X86_64.finArgs mgfLay)) hc).isSome = true
  mgfXorOut : ∃ hc, (taint.check (pT n [14, 21, 23, 24, 32] []) (Impl.Mgf1.X86_64.Table.xorOut mgfLay sDG)
    hc).isSome = true
  mgfNext : ∃ hc, (taint.check (pT n [14, 24, 31, 32] []) (.block (Impl.Mgf1.X86_64.Table.nextCtr mgfLay sDG))
    hc).isSome = true

theorem fixedChecks {n : Nat} (hn : n = 1 ∨ n = 2) : FixedChecks n := by
  rcases hn with rfl | rfl
  all_goals exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩,
    fun s hs => by rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem Pub.sub {F S : Addr} {rest : List Region} {ws ws' : List (Nat × BitVec 64)} {rs rs' : List (Reg × BitVec 64)}
    {X X' : (Nat → Byte) → (Nat → BitVec 64) → Prop} {t : State} (h : Pub F S rest ws rs X t)
    (hws : ∀ p ∈ ws', p ∈ ws) (hrs : ∀ p ∈ rs', p ∈ rs) (hX : ∀ V W, X V W → X' V W) : Pub F S rest ws' rs' X' t := by
  obtain ⟨V, W, R, hw, hx⟩ := h.W
  exact ⟨h.L, h.wr, ⟨V, W, R, fun p hp => hw p (hws p hp), hX V W hx⟩, fun p hp => h.regs p (hrs p hp)⟩

/-! ## The calls -/

/-- Before the call of `init`. -/
def IA (F S : Addr) (u : State) : Prop := Lay u F S ∧ u.gpr .rdi = off S oSt

include hH in
theorem init_pre {F S : Addr} {u : State} (h : IA F S u) :
    (initK (H.P.N + H.P.B) hH.SH.Repr).pre (u.callEntry.withRegions [] [⟨off S oSt, H.P.N + H.P.B⟩]) := by
  have hNB : H.P.N + H.P.B ≤ 192 := by have := hH.N_le; have := hH.B_le; omega_arith
  simp only [initK, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), h.2, h.1.rsp, true_and]
  exact Region.Disjoint.sub_right h.1.dR8 (Offset.sub_base S (by unfold oSt oRsa; omega_arith))

include hH in
theorem init_rel {P : State → State → Prop} (h : ∀ s₁ s₂, P s₁ s₂ → ∃ F S, IA F S s₁ ∧ IA F S s₂) :
    RelCT isa P (.call H.initN H.initC) fun _ _ => True := by
  have hNB : H.P.N + H.P.B ≤ 192 := by have := hH.N_le; have := hH.B_le; omega_arith
  refine RelCT.callEx hH.init.1 hH.init.2.1 fun s₁ s₂ hp => ?_
  obtain ⟨F, S, h₁, h₂⟩ := h s₁ s₂ hp
  refine ⟨[], _, [], _, init_pre hH h₁, init_pre hH h₂, ?_, Covers.right (h₁.1.cov (by unfold oSt oRsa; omega_arith)),
    h₁.1.cov (by unfold oSt oRsa; omega_arith), Covers.right (h₂.1.cov (by unfold oSt oRsa; omega_arith)),
    h₂.1.cov (by unfold oSt oRsa; omega_arith), by rw [h₁.1.rsp, h₂.1.rsp]⟩
  simp only [initK, State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), h₁.2, h₂.2]

/-- Before the call of the compression function on block `b`. -/
def CA (F S : Addr) (b : Nat) (u : State) : Prop :=
  Lay u F S ∧ u.gpr .rdi = off S oSt ∧ u.gpr .rsi = off S (oY + H.P.B * b) ∧ u.gpr .rdx = 1 ∧ u.gpr .rcx = S ∧
    H.P.B * b + H.P.B ≤ 2048

include hH in
theorem comp_pre {F S : Addr} {b : Nat} {u : State} (h : CA (H := H) F S b u) :
    (compressK hH.md).pre (u.callEntry.withRegions [⟨off S (oY + H.P.B * b), H.P.B * 1⟩]
      [⟨off S oSt, H.P.N⟩, ⟨S, H.P.so⟩]) := by
  obtain ⟨L, hdi, hsi, hdx, hcx, hbB⟩ := h
  have hB := hH.B_le
  have hN := hH.N_le
  have hso := hH.hso
  simp only [compressK, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    hdi, hsi, hdx, hcx, L.rsp, show (1 : BitVec 64).toNat = 1 from rfl, true_and]
  exact ⟨Offset.disjoint_base S (by unfold oSt; omega_arith) (by unfold oSt; omega_arith),
    Offset.disjoint S (by unfold oY oSt; omega_arith) (by unfold oY; omega_arith) (by unfold oSt; omega_arith),
    Offset.disjoint_base S (by unfold oY; omega_arith) (by unfold oY; omega_arith),
    Region.Disjoint.sub_right L.dR8 (Offset.sub_base S (by unfold oSt oRsa; omega_arith)),
    Region.Disjoint.sub_right L.dR8 (Region.sub_prefix (by unfold oRsa; omega_arith))⟩

include hH in
theorem comp_cov {F S : Addr} {b : Nat} {u : State} (h : CA (H := H) F S b u) :
    Covers ([⟨off S (oY + H.P.B * b), H.P.B * 1⟩] ++ [⟨off S oSt, H.P.N⟩, ⟨S, H.P.so⟩]) (u.rd ++ u.wr) ∧
      Covers [⟨off S oSt, H.P.N⟩, ⟨S, H.P.so⟩] u.wr := by
  obtain ⟨L, -, -, -, -, hbB⟩ := h
  have hN := hH.N_le
  have hso := hH.hso
  have hS0 : off S 0 = S := BitVec.add_zero S
  have c₁ := L.cov (o := 0) (n := H.P.so) (by unfold oRsa; omega_arith)
  rw [hS0] at c₁
  exact ⟨Covers.right (Covers.append_left (L.cov (by unfold oY oRsa; omega_arith))
    (Covers.pair (L.cov (by unfold oSt oRsa; omega_arith)) c₁)), Covers.pair (L.cov (by unfold oSt oRsa; omega_arith)) c₁⟩

include hH in
theorem comp_rel {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ F S b, CA (H := H) F S b s₁ ∧ CA (H := H) F S b s₂) :
    RelCT isa P (.call H.compN H.compC) fun _ _ => True := by
  refine RelCT.callEx hH.comp.verified hH.comp.ct fun s₁ s₂ hp => ?_
  obtain ⟨F, S, b, h₁, h₂⟩ := h s₁ s₂ hp
  refine ⟨_, _, _, _, comp_pre hH h₁, comp_pre hH h₂, ?_, (comp_cov hH h₁).1, (comp_cov hH h₁).2,
    (comp_cov hH h₂).1, (comp_cov hH h₂).2, by rw [h₁.1.rsp, h₂.1.rsp]⟩
  obtain ⟨-, a₁, b₁, c₁, d₁, -⟩ := h₁
  obtain ⟨-, a₂, b₂, c₂, d₂, -⟩ := h₂
  simp only [compressK, State.withRegions_gpr, State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide), a₁, a₂, b₁, b₂, c₁, c₂, d₁, d₂, and_self]


/-- Before the call of the digest of the hash value at `scratch + src`. -/
def DA (F S : Addr) (src : Nat) (u : State) : Prop :=
  Lay u F S ∧ u.gpr .rdi = off S src ∧ u.gpr .rsi = off S oDig ∧ src + H.P.N ≤ oDig

include hH in
theorem dig_pre {F S : Addr} {src : Nat} {u : State} (h : DA (H := H) F S src u) :
    (Proof.MdHashTable.X86_64.digestK hH.md).pre
      (u.callEntry.withRegions [⟨off S src, H.P.N⟩] [⟨off S oDig, H.P.N⟩]) := by
  obtain ⟨L, hdi, hsi, ho⟩ := h
  have hN := hH.N_le
  have hsrc : src + H.P.N ≤ oRsa := by unfold oDig oRsa at *; omega_arith
  have hdg : oDig + H.P.N ≤ oRsa := by unfold oDig oRsa; omega_arith
  simp only [Proof.MdHashTable.X86_64.digestK, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
    State.callEntry_rsp, State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide), hdi, hsi, L.rsp, true_and]
  have := L.Sw
  exact ⟨Offset.disjoint S (by unfold oDig at *; omega_arith) (by unfold oDig oRsa at *; omega_arith)
      (by unfold oDig oRsa at *; omega_arith),
    Region.Disjoint.sub_right L.dR8 (Offset.sub_base S hsrc), Region.Disjoint.sub_right L.dR8 (Offset.sub_base S hdg)⟩

include hH hdk in
theorem dig_rel {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → ∃ F S src, DA (H := H) F S src s₁ ∧ DA (H := H) F S src s₂) :
    RelCT isa P (.call dn (Impl.MdHashTable.X86_64.digest H.P)) fun _ _ => True := by
  refine RelCT.callEx (k := Proof.MdHashTable.X86_64.digestK hH.md)
    (Proof.MdHashTable.X86_64.digest_verified hH.shape hdk.mx) (hdk.ct hH.md) fun s₁ s₂ hp => ?_
  obtain ⟨F, S, src, h₁, h₂⟩ := h s₁ s₂ hp
  have hN := hH.N_le
  have cov : ∀ {u : State}, DA (H := H) F S src u →
      Covers ([⟨off S src, H.P.N⟩] ++ [⟨off S oDig, H.P.N⟩]) (u.rd ++ u.wr) ∧ Covers [⟨off S oDig, H.P.N⟩] u.wr :=
    fun h => by
      have ho := h.2.2.2
      have hsrc : src + H.P.N ≤ oRsa := by unfold oDig oRsa at *; omega_arith
      have hdg : oDig + H.P.N ≤ oRsa := by unfold oDig oRsa; omega_arith
      exact ⟨Covers.append_left (Covers.right (h.1.cov hsrc)) (Covers.right (h.1.cov hdg)), h.1.cov hdg⟩
  refine ⟨_, _, _, _, dig_pre hH h₁, dig_pre hH h₂, ?_, (cov h₁).1, (cov h₁).2, (cov h₂).1, (cov h₂).2,
    by rw [h₁.1.rsp, h₂.1.rsp]⟩
  obtain ⟨-, a₁, b₁, -⟩ := h₁
  obtain ⟨-, a₂, b₂, -⟩ := h₂
  simp only [Proof.MdHashTable.X86_64.digestK, State.withRegions_gpr,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    a₁, a₂, b₁, b₂, and_self]

theorem digArgs_ok {u : State} {F S : Addr} (L : Lay u F S) {src : Nat} (ho : src < 2 ^ 31) :
    WP isa (.block (scr .rdi src ++ scr .rsi oDig)) u fun v => v.gpr .rdi = off S src ∧
      v.gpr .rsi = off S oDig ∧ v.mem = u.mem ∧ Keep [.rdi, .rsi] u v := by
  refine WP.mono (WP.keep [.rdi, .rsi] (Q := fun v => v.gpr .rdi = off S src ∧ v.gpr .rsi = off S oDig ∧
    v.mem = u.mem) ?_ rfl) fun v ⟨⟨h₁, h₂, hm⟩, hk⟩ => ⟨h₁, h₂, hm, hk⟩
  have hs := L.slot
  simp only [Bignum.word] at hs
  xrun [scr, List.cons_append, List.nil_append, ea_sp, L.rsp, L.ld (d := sScr) (by decide), hs,
    VG.Proof.MlKem.X86_64.sx_ofNat ho, VG.Proof.MlKem.X86_64.sx_ofNat (show oDig < 2 ^ 31 by decide)]

theorem CA.keep11 {F S : Addr} {b : Nat} {t t' : State} (h : CA (H := H) F S b t) (k : Keep [.r11] t t')
    (hm : t'.mem = t.mem) : CA (H := H) F S b t' :=
  ⟨lay_keep11 h.1 k hm, (k.gpr (by decide)).trans h.2.1, (k.gpr (by decide)).trans h.2.2.1,
    (k.gpr (by decide)).trans h.2.2.2.1, (k.gpr (by decide)).trans h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem DA.keep11 {F S : Addr} {o : Nat} {t t' : State} (h : DA (H := H) F S o t) (k : Keep [.r11] t t')
    (hm : t'.mem = t.mem) : DA (H := H) F S o t' :=
  ⟨lay_keep11 h.1 k hm, (k.gpr (by decide)).trans h.2.1, (k.gpr (by decide)).trans h.2.2.1, h.2.2.2⟩

/-! ## The pieces -/

/-- The `ne` condition after a count that sets ZF when `j + 1 = n`. -/
theorem eval_ne_cnt {s : State} {j N : Nat} (hj : j < N) (hz : s.zf = some (decide (j + 1 = N))) :
    isa.eval .ne s = some (decide (j + 1 < N)) := by
  simp only [eval, hz, Option.map_some, Option.some.injEq]
  by_cases h : j + 1 = N
  · simp [h]
  · simp only [h, decide_false, Bool.not_false]; exact (decide_eq_true (by omega_arith)).symm

/-- `Pub` after a piece that keeps the regions. -/
theorem Pub.next {F S : Addr} {rest : List Region} {ws ws' : List (Nat × BitVec 64)} {rs : List (Reg × BitVec 64)}
    {X X' : (Nat → Byte) → (Nat → BitVec 64) → Prop} {t t' : State} (h : Pub F S rest ws rs X t) (L' : Lay t' F S)
    (hwr : t'.wr = t.wr) {V' : Nat → Byte} {W' : Nat → BitVec 64} (R' : Rep t'.mem F S V' W')
    (hw : ∀ p ∈ ws', W' p.1 = p.2) (hx : X' V' W') : Pub F S rest ws' [] X' t' :=
  ⟨L', hwr.trans h.wr, ⟨V', W', R', hw, hx⟩, fun _ hp => by cases hp⟩

theorem ws_upd {ws : List (Nat × BitVec 64)} {W : Nat → BitVec 64} (hw : ∀ p ∈ ws, W p.1 = p.2) {k : Nat}
    (hk : ∀ p ∈ ws, p.1 ≠ k) (v : BitVec 64) : ∀ p ∈ ws, upd W k v p.1 = p.2 := fun p hp => by
  simp only [upd]; rw [ifn (hk p hp)]; exact hw p hp

theorem hws_w {a : HA} {W : Nat → BitVec 64} (hw : ∀ p ∈ hws H dn a, W p.1 = p.2) :
    W 21 = a.S ∧ W 28 = BitVec.ofNat 64 a.nbm ∧ W 10 = a.sy dn :=
  ⟨hw (21, a.S) (by simp [hws]), hw (28, BitVec.ofNat 64 a.nbm) (by simp [hws]), hw (10, a.sy dn) (by simp [hws])⟩

/-- The slots of the table of `MdHash`, from `hws`. -/
theorem hws_ht {a : HA} {sy : String → Addr} {W : Nat → BitVec 64} (hok : SyH H dn f a.sy sy)
    (hw : ∀ p ∈ hws H dn a, W p.1 = p.2) : HT H dn f W sy :=
  hok.1.ht ((hw (8, _) (by simp [hws])).trans hok.2.1.symm) ((hw (9, _) (by simp [hws])).trans hok.2.2.1.symm)
    ((hw (10, _) (by simp [hws])).trans hok.2.2.2.symm)

variable (H dn f) in
/-- After the length field: the index of the last block (secret). -/
def HF (a : HA) (t : State) : Prop :=
  HOk H n a ∧ Pub a.F a.S a.rest (hws H dn a) [] (fun _ W => ∃ fb, W 30 = BitVec.ofNat 64 fb ∧ fb < a.nbm) t ∧
    SyH H dn f a.sy t.syms

variable (H dn f) in
/-- Before block `j`. -/
def HL (a : HA) (j : Nat) (t : State) : Prop :=
  HOk H n a ∧ Pub a.F a.S a.rest (hws H dn a ++ [(29, BitVec.ofNat 64 j)]) []
    (fun _ W => ∃ fb, W 30 = BitVec.ofNat 64 fb ∧ fb < a.nbm) t ∧ SyH H dn f a.sy t.syms

variable (H dn f) in
/-- After the blocks. -/
def HD (a : HA) (t : State) : Prop :=
  HOk H n a ∧ Pub a.F a.S a.rest [(21, a.S), (10, a.sy dn)] [] (fun _ _ => True) t ∧
    SyH H dn f a.sy t.syms

theorem hl_w {a : HA} {j : Nat} {W : Nat → BitVec 64}
    (hw : ∀ p ∈ hws H dn a ++ [(29, BitVec.ofNat 64 j)], W p.1 = p.2) :
    W 21 = a.S ∧ W 28 = BitVec.ofNat 64 a.nbm ∧ W 29 = BitVec.ofNat 64 j :=
  ⟨hw (21, a.S) (by simp [hws]), hw (28, BitVec.ofNat 64 a.nbm) (by simp [hws]), hw (29, BitVec.ofNat 64 j) (by simp)⟩

theorem mem21 {a : HA} {ws : List (Nat × BitVec 64)} (h : (21, a.S) ∈ ws) : ∀ p ∈ [(21, a.S)], p ∈ ws := by
  intro p hp; rw [List.mem_singleton.mp hp]; exact h

include hH K in
theorem ctInit_ct (hfx : FixedChecks n) : RelCT isa (Two (HE H dn f n)) (ctInit f) (Two (HE H dn f n)) := by
  obtain ⟨_, hs⟩ := hfx.scrSt
  unfold ctInit
  refine two_post (RelCT.seq (two_post (Ψ := fun a t => HE H dn f n a t ∧ t.gpr .rdi = off a.S oSt)
      (two_pub n [21, 28, 8, 9, 10] [] HA.F HA.S HA.rest (hws H dn) (fun _ => []) (fun a t h => ⟨_, h.2.1⟩)
        (fun a t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hs) fun a t h => ?_)
      (two_scall n (s := sIniH) (by decide) HA.F HA.S HA.rest (fun a => a.sy H.initN)
        (fun a t h => ⟨h.1.2.1.L, h.1.2.1.wr, h.1.1.1, pub_slot h.1.2.1 (k := 8) rfl (by decide) (by simp [hws]),
          h.1.2.2.2.1, h.1.2.2.1.fi⟩)
        (hfx.ld _ (.inl rfl)) (init_rel hH fun s₁ s₂ ⟨a, ⟨t₁, h₁, k₁, hm₁, _⟩, ⟨t₂, h₂, k₂, hm₂, _⟩⟩ =>
          ⟨a.F, a.S, ⟨lay_keep11 h₁.1.2.1.L k₁ hm₁, (k₁.gpr (by decide)).trans h₁.2⟩,
            ⟨lay_keep11 h₂.1.2.1.L k₂ hm₂, (k₂.gpr (by decide)).trans h₂.2⟩⟩))) fun a t h => ?_
  · have L := h.2.1.L
    exact X86_64.WP.mono_syms (scr_ok L (d := .rdi) (by decide) (o := oSt) (by decide)) fun u ⟨hdi, hm, hk⟩ sy =>
      ⟨⟨h.1, h.2.1.keepM (hk.gpr (by decide)) hk.2.2 hm, h.2.2.tr sy⟩, hdi⟩
  · obtain ⟨V, W, R, hw, hx⟩ := h.2.1.W
    exact X86_64.WP.mono_syms (ctInit_ok hH K h.2.1.L R (hws_ht h.2.2 hw))
      fun u ⟨L', _, hwr, _, R', _⟩ sy => ⟨h.1, h.2.1.next L' hwr R' hw hx, h.2.2.tr sy⟩

include hH in
theorem pad80_ct (hc : HashChecks H.P H.D n) : RelCT isa (Two (HE H dn f n)) (pad80 H) (Two (HE H dn f n)) := by
  obtain ⟨_, hp⟩ := hc.pad80
  refine two_post (two_pub n [21, 28, 8, 9, 10] [] HA.F HA.S HA.rest (hws H dn) (fun _ => [])
    (fun a t h => ⟨_, h.2.1⟩) (fun a t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp) fun a t h => ?_
  obtain ⟨V, W, R, hw, ℓ, hl, hfit⟩ := h.2.1.W
  obtain ⟨-, h1, hnb⟩ := h.1
  exact X86_64.WP.mono_syms (pad80_ok hH h.2.1.L R hl (hws_w hw).2.1 h1 hnb (by omega_arith)) fun u P sy =>
    ⟨h.1, h.2.1.next P.L P.keep.2.2 P.R hw ⟨ℓ, hl, hfit⟩, h.2.2.tr sy⟩

include hH in
theorem lenField_ct (hc : HashChecks H.P H.D n) :
    RelCT isa (Two (HE H dn f n)) (.block (lenField H)) (Two (HF H dn f n)) := by
  obtain ⟨_, hp⟩ := hc.lenField
  refine two_post (two_pub n [21] [] HA.F HA.S HA.rest (fun a => [(21, a.S)]) (fun _ => [])
    (fun a t h => ⟨_, h.2.1.sub (mem21 (by simp [hws])) (fun _ h => h) fun _ _ x => x⟩)
    (fun a t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp) fun a t h => ?_
  obtain ⟨V, W, R, hw, ℓ, hl, hfit⟩ := h.2.1.W
  obtain ⟨-, h1, hnb⟩ := h.1
  have hB0 := hH.B_pos
  refine X86_64.WP.mono_syms (lenField_ok hH h.2.1.L R hl (by omega_arith)) fun u ⟨L', hk, R'⟩ sy =>
    ⟨h.1, h.2.1.next L' hk.2.2 R' (ws_upd hw (by simp [hws]) _) ⟨RsaPss.lastBlk H.P.B H.P.L ℓ, by simp [upd], ?_⟩,
      h.2.2.tr sy⟩
  exact (Nat.div_lt_iff_lt_mul hB0).mpr (by omega_arith)

include hH in
theorem lenLoop_ct (hc : HashChecks H.P H.D n) : RelCT isa (Two (HF H dn f n)) (lenLoop H) (Two (HF H dn f n)) := by
  obtain ⟨_, hp⟩ := hc.lenLoop
  refine two_post (two_pub n [21, 28, 8, 9, 10] [] HA.F HA.S HA.rest (hws H dn) (fun _ => [])
    (fun a t h => ⟨_, h.2.1⟩) (fun a t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp) fun a t h => ?_
  obtain ⟨V, W, R, hw, fb, hf, hfb⟩ := h.2.1.W
  obtain ⟨-, -, hnb⟩ := h.1
  exact X86_64.WP.mono_syms (lenLoop_ok hH h.2.1.L R (len := (List.range H.P.L).map fun i => V (oLen + i))
    (fun i hi => by simp [List.getD_eq_getElem?_getD, hi]) hf (hws_w hw).2.1 hfb hnb) fun u O sy =>
    ⟨h.1, h.2.1.next O.L O.keep.2.2 O.R hw ⟨fb, hf, hfb⟩, h.2.2.tr sy⟩

theorem startB_ct (hfx : FixedChecks n) :
    RelCT isa (Two (HF H dn f n)) (.block [.mov32 .rax (.imm 0), .store (sp sB) .rax])
      (Two fun a t => 0 < a.nbm ∧ HL H dn f n a 0 t) := by
  obtain ⟨_, hp⟩ := hfx.startB
  refine two_post (two_pub n [21, 28, 8, 9, 10] [] HA.F HA.S HA.rest (hws H dn) (fun _ => [])
    (fun a t h => ⟨_, h.2.1⟩) (fun a t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp) fun a t h => ?_
  obtain ⟨V, W, R, hw, hx⟩ := h.2.1.W
  have L := h.2.1.L
  refine X86_64.WP.mono_syms (WP.keep [.rax] (Q := fun u => u.mem = t.mem.writeW (off a.F sB) (BitVec.ofNat 64 0))
      ?_ rfl) fun u ⟨hm, hk⟩ sy => ?_
  · xrun [ea_sp, L.rsp, L.st (d := sB) (by decide)]
    rfl
  have R0 := R.wf L.geo (k := 29) (by decide) (BitVec.ofNat 64 0)
  rw [show off a.F (8 * 29) = off a.F sB from rfl, ← hm] at R0
  refine ⟨h.1.2.1, h.1, ⟨L.of_rep' R R0 (by simp [upd]) (hk.gpr (by decide)) hk.2.2, hk.2.2.trans h.2.1.wr,
    ⟨_, _, R0, fun p hp => ?_, (by obtain ⟨fb, hf, hfb⟩ := hx; exact ⟨fb, by simp [upd, hf], hfb⟩)⟩,
    fun _ hp => by cases hp⟩, h.2.2.tr sy⟩
  rcases List.mem_append.mp hp with hp | hp
  · exact ws_upd hw (by simp [hws]) _ p hp
  · rw [List.mem_singleton.mp hp]; simp [upd]

variable (H dn f) in
/-- Before block `j`, as the loop sees it. -/
abbrev HB (p : HA × Nat) (t : State) : Prop := p.2 < p.1.nbm ∧ HL H dn f n p.1 p.2 t

theorem hb_bound {p : HA × Nat} {t : State} (h : HB H dn f n p t) : H.P.B * p.2 + H.P.B ≤ 2048 := by
  obtain ⟨hj, -, -, hnb⟩ := h.1, h.2.1
  rw [← Nat.mul_succ]
  exact Nat.le_trans (Nat.mul_le_mul_left _ hj) (by rw [Nat.mul_comm]; exact hnb)

theorem hb_pub {p : HA × Nat} {t : State} (h : HB H dn f n p t) :
    Pub p.1.F p.1.S p.1.rest [(21, p.1.S), (29, BitVec.ofNat 64 p.2)] []
      (fun _ W => ∃ fb, W 30 = BitVec.ofNat 64 fb ∧ fb < p.1.nbm) t :=
  h.2.2.1.sub (fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> simp [hws]) (fun _ h => h) fun _ _ x => x

include hH in
theorem compA_ct (hc : HashChecks H.P H.D n) (hfx : FixedChecks n) :
    RelCT isa (Two (HB H dn f n)) (.seq (.block (compArgs H)) (scall sCmpH f.comp)) (Two (HB H dn f n)) := by
  obtain ⟨_, hp⟩ := hc.compArgs
  have hB := hH.B_le
  refine two_post (RelCT.seq (two_post (Ψ := fun p t => CA (H := H) p.1.F p.1.S p.2 t ∧ HB H dn f n p t)
    (two_pub n [21, 29] [] (fun p => p.1.F) (fun p => p.1.S) (fun p => p.1.rest)
      (fun p => [(21, p.1.S), (29, BitVec.ofNat 64 p.2)]) (fun _ => []) (fun p t h => ⟨_, hb_pub n h⟩)
      (fun p t h => h.2.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp) fun p t h => ?_)
    (two_scall n (s := sCmpH) (by decide) (fun p => p.1.F) (fun p => p.1.S) (fun p => p.1.rest)
      (fun p => p.1.sy H.compN)
      (fun p t h => ⟨h.1.1, h.2.2.2.1.wr, h.2.2.1.1, pub_slot h.2.2.2.1 (k := 9) rfl (by decide) (by simp [hws]),
        h.2.2.2.2.2.2.1, h.2.2.2.2.1.fc⟩)
      (hfx.ld _ (.inr (.inl rfl)))
      (comp_rel hH fun s₁ s₂ ⟨p, ⟨t₁, h₁, k₁, hm₁, _⟩, ⟨t₂, h₂, k₂, hm₂, _⟩⟩ =>
        ⟨p.1.F, p.1.S, p.2, h₁.1.keep11 k₁ hm₁, h₂.1.keep11 k₂ hm₂⟩))) fun p t h => ?_
  · obtain ⟨V, W, R, hw, -⟩ := h.2.2.1.W
    have L := h.2.2.1.L
    have hbB := hb_bound n h
    have := Nat.le_mul_of_pos_left p.2 hH.B_pos
    exact X86_64.WP.mono_syms (compArgs_ok hH L R (b := p.2) (by omega_arith) (hl_w hw).2.2)
      fun u ⟨h1, h2, h3, h4, hm, hk⟩ sy => ⟨⟨L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm]), h1, h2, h3, h4, hbB⟩,
        h.1, h.2.1, h.2.2.1.keepM (hk.gpr (by decide)) hk.2.2 hm, h.2.2.2.tr sy⟩
  · obtain ⟨V, W, R, hw, hx⟩ := h.2.2.1.W
    exact X86_64.WP.mono_syms (compCall_ok hH h.2.2.1.L R (hb_bound n h) (hl_w hw).2.2
        (hws_ht h.2.2.2 fun q hq => hw q (List.mem_append_left _ hq)))
      fun u ⟨L', _, hwr, _, R', _⟩ sy => ⟨h.1, h.2.1, h.2.2.1.next L' hwr R' hw hx, h.2.2.2.tr sy⟩

include hH in
theorem select_ct (hc : HashChecks H.P H.D n) : RelCT isa (Two (HB H dn f n)) (select H) (Two (HB H dn f n)) := by
  obtain ⟨_, hp⟩ := hc.select
  refine two_post (two_pub n [21, 29] [] (fun p => p.1.F) (fun p => p.1.S) (fun p => p.1.rest)
      (fun p => [(21, p.1.S), (29, BitVec.ofNat 64 p.2)]) (fun _ => []) (fun p t h => ⟨_, hb_pub n h⟩)
      (fun p t h => h.2.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp) fun p t h => ?_
  obtain ⟨V, W, R, hw, fb, hf, hfb⟩ := h.2.2.1.W
  have := Nat.le_trans (Nat.le_mul_of_pos_right _ hH.B_pos) h.2.1.2.2
  exact X86_64.WP.mono_syms (select_ok hH h.2.2.1.L R (hl_w hw).2.2 hf (by omega) (by omega_using [hfb, this])) fun u Sw sy =>
    ⟨h.1, h.2.1, h.2.2.1.next Sw.L Sw.keep.2.2 Sw.R hw ⟨fb, hf, hfb⟩, h.2.2.2.tr sy⟩

theorem nextB_ct (hfx : FixedChecks n) : RelCT isa (Two (HB H dn f n)) (.block nextBlock) fun _ _ => True := by
  obtain ⟨_, hp⟩ := hfx.nextB
  exact two_pub n [21, 28, 8, 9, 10, 29] [] (fun p => p.1.F) (fun p => p.1.S) (fun p => p.1.rest)
    (fun p => hws H dn p.1 ++ [(29, BitVec.ofNat 64 p.2)]) (fun _ => []) (fun p t h => ⟨_, h.2.2.1⟩)
    (fun p t h => h.2.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp

include hH in
theorem body_wp {a : HA} {j : Nat} {t : State} (hj : j < a.nbm) (h : HL H dn f n a j t) :
    WP isa (seqs [.block (compArgs H), scall sCmpH f.comp, select H, .block nextBlock]) t fun t' =>
      isa.eval .ne t' = some (decide (j + 1 < a.nbm)) ∧ (j + 1 < a.nbm → HL H dn f n a (j + 1) t') ∧
      (j + 1 = a.nbm → HD H dn f n a t') := by
  have hbB := hb_bound (H := H) n (p := (a, j)) ⟨hj, h⟩
  obtain ⟨V, W, R, hw, fb, hf, hfb⟩ := h.2.1.W
  obtain ⟨w21, w28, w29⟩ := hl_w hw
  have w10 : W 10 = a.sy dn := hw (10, a.sy dn) (by simp [hws])
  have hnbm : a.nbm ≤ 2048 := Nat.le_trans (Nat.le_mul_of_pos_right a.nbm hH.B_pos) h.1.2.2
  refine WP.seq_assoc (WP.seq (X86_64.WP.mono_syms (compCall_ok hH h.2.1.L R hbB w29
      (hws_ht h.2.2 fun q hq => hw q (List.mem_append_left _ hq)))
    fun v ⟨Lv, _, hwrv, _, Rv, _⟩ sv => ?_))
  refine WP.seq (X86_64.WP.mono_syms (select_ok hH Lv Rv (b := j) (fb := fb) w29 hf (by omega_arith)
    (by omega_arith)) fun w Sw sw => ?_)
  have hsy : ∀ u : State, u.syms = w.syms → SyH H dn f a.sy u.syms := fun u su => ((h.2.2.tr sv).tr sw).tr su
  refine X86_64.WP.mono_syms (nextBlock_ok Sw.L Sw.R (b := j) (nbm := a.nbm) w29 w28 (by omega_arith)
      (by omega_arith))
    fun u' ⟨hz, Lu', hk', Ru'⟩ su => ⟨eval_ne_cnt hj hz, fun _ => ⟨h.1, ⟨Lu', hk'.2.2.trans (Sw.keep.2.2.trans
      (hwrv.trans h.2.1.wr)), ⟨_, _, Ru', fun q hq => ?_, fb, by simp [upd, hf], hfb⟩, fun _ hp => by cases hp⟩,
      hsy u' su⟩,
      fun _ => ⟨h.1, ⟨Lu', hk'.2.2.trans (Sw.keep.2.2.trans (hwrv.trans h.2.1.wr)),
        ⟨_, _, Ru', fun q hq => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl <;> simp [upd, w21, w10], trivial⟩, fun _ hp => by cases hp⟩, hsy u' su⟩⟩
  rcases List.mem_append.mp hq with hq | hq
  · exact ws_upd (fun q hq => hw q (List.mem_append_left _ hq)) (by simp [hws]) _ q hq
  · rw [List.mem_singleton.mp hq]; simp [upd]

include hH in
theorem compLoop_ct (hc : HashChecks H.P H.D n) (hfx : FixedChecks n) :
    RelCT isa (Two (HF H dn f n)) (compLoop f H) (Two (HD H dn f n)) := by
  refine RelCT.seq (startB_ct n hfx) (two_loop (Φ := HL H dn f n) HA.nbm ?_ fun a j t hj h => body_wp hH n hj h)
  simp only [seqs]
  exact RelCT.assoc (RelCT.seq (compA_ct hH n hc hfx) (RelCT.seq (select_ct hH n hc) (nextB_ct n hfx)))

include hH hdk in
theorem digestOut_ct (hfx : FixedChecks n) : RelCT isa (Two (HD H dn f n)) (digestOut f) fun _ _ => True := by
  obtain ⟨_, hp⟩ := hfx.digArgs
  have hN := hH.N_le
  unfold digestOut digestAt
  refine RelCT.seq (two_post (Ψ := fun a t => DA (H := H) a.F a.S oSel t ∧ HD H dn f n a t)
    (two_pub n [21] [] HA.F HA.S HA.rest (fun a => [(21, a.S)]) (fun _ => [])
      (fun a t h => ⟨_, h.2.1.sub (mem21 (by simp)) (fun _ h => h) fun _ _ x => x⟩)
      (fun a t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp) fun a t h => ?_)
    (two_scall n (s := sDigH) (by decide) HA.F HA.S HA.rest (fun a => a.sy dn)
      (fun a t h => ⟨h.1.1, h.2.2.1.wr, h.2.1.1, pub_slot h.2.2.1 (k := 10) rfl (by decide) (by simp),
        h.2.2.2.2.2.2, h.2.2.2.1.fd⟩)
      (hfx.ld _ (.inr (.inr (.inl rfl))))
      (dig_rel hH hdk fun s₁ s₂ ⟨a, ⟨t₁, h₁, k₁, hm₁, _⟩, ⟨t₂, h₂, k₂, hm₂, _⟩⟩ =>
        ⟨a.F, a.S, oSel, h₁.1.keep11 k₁ hm₁, h₂.1.keep11 k₂ hm₂⟩))
  have L := h.2.1.L
  exact X86_64.WP.mono_syms (digArgs_ok L (src := oSel) (by decide)) fun u ⟨h1, h2, hm, hk⟩ sy =>
    ⟨⟨L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm]), h1, h2, by unfold oSel oDig; omega_arith⟩,
      h.1, h.2.1.keepM (hk.gpr (by decide)) hk.2.2 hm, h.2.2.tr sy⟩

include hH K hdk in
/-- `ctHash` is constant time. -/
theorem ctHash_ct (hc : HashChecks H.P H.D n) (hfx : FixedChecks n) :
    RelCT isa (Two (HE H dn f n)) (ctHash f H) fun _ _ => True := by
  unfold ctHash ctHashWith seqs seqs seqs seqs seqs
  exact (ctInit_ct hH K n hfx).seq ((pad80_ct hH n hc).seq ((lenField_ct hH n hc).seq ((lenLoop_ct hH n hc).seq
    ((compLoop_ct hH n hc hfx).seq (digestOut_ct hH hdk n hfx)))))

end VG.Proof.RsaPss.X86_64

end

end

/-! ### `RsaPss.X86_64.MgfCT`, which this module and modules that import it used -/

section

/-!
# RSASSA-PSS on x86-64: MGF1 is constant time

Two runs of `mgfXor H g` with the same frame, working space, writable
regions, place and length of `DB`, and addresses of statics (`MA`) leak the
same trace (`mgfXor_ct`): the loop runs once per `hLen` bytes of `DB` in
both, each round's pieces between the calls are checked by the taint
analysis (`FixedChecks`, `HashChecks`), and each call through a slot of the
table of `MdHash` is of the same streaming function of `G` in both runs
(`two_scall`), whose arguments agree (`two_init`, `two_upd`, `two_fin`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifp ifn)
open VG.Proof.Bignum (off)
open VG.Proof.Bignum.X86_64 (Two two_post two_map two_loop)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash Stream)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (StreamOK)
open VG.Impl.Mgf1.X86_64.Table (Fns)

/-- What two runs of `mgfXor` share: the frame, the working space, the
writable regions after the frame, `DB`'s offset and length, and the
addresses of statics. -/
structure MA where
  F : Addr
  S : Addr
  rest : List Region
  e : Nat
  db : Nat
  sy : String → Addr

/-- The public words in round `j`: `scratch`, `DB`, `dbLen`, the seed, the
counter, the bytes done, and the slots of the table of `MdHash`. -/
def mws (G : Stream) (D : Nat) (a : MA) (j : Nat) : List (Nat × BitVec 64) :=
  [(21, a.S), (23, off a.S a.e), (24, BitVec.ofNat 64 a.db), (29, off a.S (a.e + a.db)), (30, BitVec.ofNat 64 D),
    (31, BitVec.ofNat 64 j), (32, BitVec.ofNat 64 (j * G.D)), (14, BitVec.ofNat 64 G.D), (11, a.sy G.initN),
    (12, a.sy G.updN), (13, a.sy G.finN)]

/-- The rounds of `dbLen` bytes, `hLen` at a time. -/
def mN (D : Nat) (a : MA) : Nat := (a.db + D - 1) / D

theorem cnt_iff {j D db : Nat} (hD : 0 < D) : j < (db + D - 1) / D ↔ j * D < db := by
  rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hD, Nat.succ_mul]
  omega_arith

variable {G : Stream} (hG : StreamOK G) {g : Fns} {n : Nat} {H : Hash}
variable {Gs : Spec.Mgf1.Hash} (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = G.D)
  (hGv : Proof.Mgf1.Valid Gs)

variable (G g n H) in
/-- The anchor fits `mgfXor`, and the calls of `g` reach `G`'s functions. -/
def MOk (a : MA) : Prop := RestOk n a.F a.rest ∧ DbAt H.D a.e a.db

variable (G g) in
/-- A run's symbols `sy'`: the calls of `g` reach `G`'s functions, whose
addresses are the anchor's, `sy`. The runs agree on these names alone. -/
def SyG (sy sy' : String → Addr) : Prop :=
  GTF G g sy' ∧ sy' G.initN = sy G.initN ∧ sy' G.updN = sy G.updN ∧ sy' G.finN = sy G.finN

theorem SyG.tr {sy s₁ s₂ : String → Addr} (h : SyG G g sy s₂) (e : s₁ = s₂) : SyG G g sy s₁ := e ▸ h

theorem mws_gt {D : Nat} {a : MA} {j : Nat} {sy : String → Addr} {W : Nat → BitVec 64} (hok : SyG G g a.sy sy)
    (hw : ∀ q ∈ mws G D a j, W q.1 = q.2) : GT G g W sy :=
  hok.1.gt ((hw (11, a.sy G.initN) (by simp only [mws, List.mem_cons, true_or, or_true])).trans hok.2.1.symm)
    ((hw (12, a.sy G.updN) (by simp only [mws, List.mem_cons, true_or, or_true])).trans hok.2.2.1.symm)
    ((hw (13, a.sy G.finN) (by simp only [mws, List.mem_cons, true_or, or_true])).trans hok.2.2.2.symm)
    (hw (14, BitVec.ofNat 64 G.D) (by simp only [mws, List.mem_cons, true_or, or_true]))

variable (G g n H) in
/-- A point of round `j`: the public words as they are at its start. -/
structure RP (a : MA) (j : Nat) (t : State) : Prop where
  ok : MOk n H a
  lt : j * G.D < a.db
  pub : Pub a.F a.S a.rest (mws G H.D a j) [] (fun _ _ => True) t
  sy : SyG G g a.sy t.syms

theorem RP.after {a : MA} {j : Nat} {t t' : State} (h : RP G g n H a j t) (L' : Lay t' a.F a.S)
    (hwr : t'.wr = t.wr) {V' : Nat → Byte} {W : Nat → BitVec 64} (R' : Rep t'.mem a.F a.S V' W)
    (hw : ∀ q ∈ mws G H.D a j, W q.1 = q.2) (hs : t'.syms = t.syms) : RP G g n H a j t' :=
  ⟨h.ok, h.lt, h.pub.next L' hwr R' hw trivial, h.sy.tr hs⟩

theorem RP.keepM {a : MA} {j : Nat} {t t' : State} (h : RP G g n H a j t) (hsp : t'.gpr .rsp = t.gpr .rsp)
    (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem) (hs : t'.syms = t.syms) : RP G g n H a j t' :=
  ⟨h.ok, h.lt, h.pub.keepM hsp hwr hm, h.sy.tr hs⟩

theorem RP.sub {a : MA} {j : Nat} {t : State} (h : RP G g n H a j t) {ws : List (Nat × BitVec 64)}
    (hws : ∀ q ∈ ws, q ∈ mws G H.D a j) : Pub a.F a.S a.rest ws [] (fun _ _ => True) t :=
  h.pub.sub hws (fun _ h => h) fun _ _ x => x

/-! ## A round -/

variable (G g n H) in
abbrev Q0 (p : MA × Nat) (t : State) : Prop := RP G g n H p.1 p.2 t

variable (G g n H) in
abbrev Q1 (p : MA × Nat) (t : State) : Prop := RP G g n H p.1 p.2 t ∧ t.gpr .rdi = off p.1.S oSt

variable (G g n H) in
abbrev Q3 (p : MA × Nat) (t : State) : Prop :=
  RP G g n H p.1 p.2 t ∧ t.gpr .rdi = off p.1.S oSt ∧ t.gpr .rsi = BitVec.ofNat 64 0 ∧
    t.gpr .rdx = off p.1.S (p.1.e + p.1.db) ∧ t.gpr .rcx = BitVec.ofNat 64 H.D ∧ t.gpr .r8 = off p.1.S oCW

variable (G g n H) in
abbrev Q5 (p : MA × Nat) (t : State) : Prop :=
  RP G g n H p.1 p.2 t ∧ t.gpr .rdi = off p.1.S oSt ∧ t.gpr .rsi = BitVec.ofNat 64 H.D ∧
    t.gpr .rdx = off p.1.S oLen ∧ t.gpr .rcx = BitVec.ofNat 64 4 ∧ t.gpr .r8 = off p.1.S oCW

variable (G g n H) in
abbrev Q7 (p : MA × Nat) (t : State) : Prop :=
  RP G g n H p.1 p.2 t ∧ t.gpr .rdi = off p.1.S oSt ∧ t.gpr .rsi = BitVec.ofNat 64 (H.D + 4) ∧
    t.gpr .rdx = off p.1.S oDig ∧ t.gpr .rcx = off p.1.S oCW

theorem mws_w {D : Nat} {a : MA} {j : Nat} {W : Nat → BitVec 64} (hw : ∀ q ∈ mws G D a j, W q.1 = q.2) :
    W 14 = BitVec.ofNat 64 G.D ∧ W 23 = off a.S a.e ∧ W 24 = BitVec.ofNat 64 a.db ∧
      W 29 = off a.S (a.e + a.db) ∧ W 30 = BitVec.ofNat 64 D ∧ W 31 = BitVec.ofNat 64 j ∧
      W 32 = BitVec.ofNat 64 (j * G.D) :=
  have m : ∀ {q}, q ∈ mws G D a j → W q.1 = q.2 := fun h => hw _ h
  ⟨m (q := (14, BitVec.ofNat 64 G.D)) (by simp only [mws, List.mem_cons, true_or, or_true]),
    m (q := (23, off a.S a.e)) (by simp only [mws, List.mem_cons, true_or, or_true]),
    m (q := (24, BitVec.ofNat 64 a.db)) (by simp only [mws, List.mem_cons, true_or, or_true]),
    m (q := (29, off a.S (a.e + a.db))) (by simp only [mws, List.mem_cons, true_or, or_true]),
    m (q := (30, BitVec.ofNat 64 D)) (by simp only [mws, List.mem_cons, true_or, or_true]),
    m (q := (31, BitVec.ofNat 64 j)) (by simp only [mws, List.mem_cons, true_or, or_true]),
    m (q := (32, BitVec.ofNat 64 (j * G.D))) (by simp only [mws, List.mem_cons, true_or, or_true])⟩

include hG in
theorem round_ct (hfx : FixedChecks n) :
    RelCT isa (Two (Q0 G g n H)) (mgfRound g) fun _ _ => True := by
  obtain ⟨hzS, hzF, hzW, hzDF, hzD⟩ := sizes hG
  have c1 : oSt = 2048 := rfl
  have c2 : oDig = 2304 := rfl
  have c3 : oLen = 2368 := rfl
  have c4 : oCW = 0 := rfl
  have c5 : oRsa = 8192 := rfl
  have c6 : oEm = 2560 := rfl
  obtain ⟨_, hmgfIni⟩ := hfx.mgfIni
  obtain ⟨_, hmgfSrc⟩ := hfx.mgfSrc
  obtain ⟨_, hmgfCtr⟩ := hfx.mgfCtr
  obtain ⟨_, hmgfFin⟩ := hfx.mgfFin
  obtain ⟨_, hmgfXorOut⟩ := hfx.mgfXorOut
  obtain ⟨_, hmgfNext⟩ := hfx.mgfNext
  unfold mgfRound seqs seqs seqs seqs seqs seqs seqs seqs seqs
  -- `init`.
  refine RelCT.seq (two_post (Ψ := Q1 G g n H) (two_pub n [21] [] (fun p => p.1.F) (fun p => p.1.S)
      (fun p => p.1.rest) (fun p => [(21, p.1.S)]) (fun _ => []) (fun p t h => ⟨_, h.sub fun q hq => by
        rw [List.mem_singleton.mp hq]; simp only [mws, List.mem_cons, true_or]⟩)
      (fun p t h => h.ok.1) (fun _ => rfl) (fun _ => rfl) (by decide) hmgfIni)
    fun p t h => X86_64.WP.mono_syms (scr_ok h.pub.L (d := .rdi) (by decide) (o := oSt) (by decide))
      fun t' ⟨hdi, hm, k⟩ sy => ⟨h.keepM (k.gpr (by decide)) k.2.2 hm sy, hdi⟩) ?_
  refine RelCT.seq (two_post (Ψ := Q0 G g n H) (two_scall n (s := sIniG) (by decide) (fun p => p.1.F)
      (fun p => p.1.S) (fun p => p.1.rest) (fun p => p.1.sy G.initN)
      (fun p t h => ⟨h.1.pub.L, h.1.pub.wr, h.1.ok.1, pub_slot h.1.pub (k := 11) rfl (by decide) (by simp only [mws, List.mem_cons, true_or, or_true]),
        h.1.sy.2.1, h.1.sy.1.fi⟩) (hfx.ld _ (.inr (.inr (.inr (.inl rfl)))))
      (two_init hG (fun p => p.1.F) (fun p => p.1.S) fun p t ⟨t₀, h, k, hm, _⟩ =>
        ⟨lay_keep11 h.1.pub.L k hm, (k.gpr (by decide)).trans h.2⟩)) fun p t h => ?_) ?_
  · obtain ⟨V, W, R, hw, -⟩ := h.1.pub.W
    exact X86_64.WP.mono_syms (initS_ok hG h.1.pub.L R (mws_gt h.1.sy hw) h.2)
      fun t' ⟨L', _, wr', _, R', _⟩ sy => h.1.after L' wr' R' hw sy
  -- `update` with the seed.
  refine RelCT.seq (two_post (Ψ := Q3 G g n H) (two_pub n [21, 29, 30] [] (fun p => p.1.F) (fun p => p.1.S)
      (fun p => p.1.rest) (fun p => [(21, p.1.S), (29, off p.1.S (p.1.e + p.1.db)), (30, BitVec.ofNat 64 H.D)])
      (fun _ => []) (fun p t h => ⟨_, h.sub fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl <;> simp only [mws, List.mem_cons, true_or, or_true]⟩)
      (fun p t h => h.ok.1) (fun _ => rfl) (fun _ => rfl) (by decide) hmgfSrc) fun p t h => ?_) ?_
  · obtain ⟨V, W, R, hw, -⟩ := h.pub.W
    have w := mws_w hw
    exact X86_64.WP.mono_syms (updSrc_ok h.pub.L R w.2.2.2.1 w.2.2.2.2.1)
      fun t' ⟨hdi, hsi, hdx, hcx, h8, hm, k⟩ sy => ⟨h.keepM (k.gpr (by decide)) k.2.2 hm sy, hdi, hsi, hdx, hcx, h8⟩
  refine RelCT.seq (two_post (Ψ := Q0 G g n H) (two_scall n (s := sUpdG) (by decide) (fun p => p.1.F)
      (fun p => p.1.S) (fun p => p.1.rest) (fun p => p.1.sy G.updN)
      (fun p t h => ⟨h.1.pub.L, h.1.pub.wr, h.1.ok.1, pub_slot h.1.pub (k := 12) rfl (by decide) (by simp only [mws, List.mem_cons, true_or, or_true]),
        h.1.sy.2.2.1, h.1.sy.1.fu⟩) (hfx.ld _ (.inr (.inr (.inr (.inr (.inl rfl))))))
      (two_upd hG (fun p => p.1.F) (fun p => p.1.S) (fun p => p.1.e + p.1.db) (fun _ => H.D)
        (fun _ => BitVec.ofNat 64 0) fun p t ⟨t₀, h, k, hm, _⟩ => by
          have := h.1.ok.2.fit; have := h.1.ok.2.e1
          exact ⟨lay_keep11 h.1.pub.L k hm, by omega_arith, Or.inr (by omega_arith), Or.inr (by omega_arith),
            (k.gpr (by decide)).trans h.2.1, (k.gpr (by decide)).trans h.2.2.1, (k.gpr (by decide)).trans h.2.2.2.1,
            (k.gpr (by decide)).trans h.2.2.2.2.1, (k.gpr (by decide)).trans h.2.2.2.2.2⟩)) fun p t h => ?_) ?_
  · obtain ⟨V, W, R, hw, -⟩ := h.1.pub.W
    have := h.1.ok.2.fit; have := h.1.ok.2.e1
    exact X86_64.WP.mono_syms (updS_ok hG h.1.pub.L R (mws_gt h.1.sy hw)
        (a := p.1.e + p.1.db) (len := H.D) (by omega_arith) (Or.inr (by omega_arith)) (Or.inr (by omega_arith))
        h.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2)
      fun t' ⟨L', _, wr', _, R', _⟩ sy => h.1.after L' wr' R' hw sy
  -- The counter, and `update` with it.
  refine RelCT.seq (two_post (Ψ := Q5 G g n H) (two_pub n [21, 30, 31] [] (fun p => p.1.F) (fun p => p.1.S)
      (fun p => p.1.rest) (fun p => [(21, p.1.S), (30, BitVec.ofNat 64 H.D), (31, BitVec.ofNat 64 p.2)])
      (fun _ => []) (fun p t h => ⟨_, h.sub fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl <;> simp only [mws, List.mem_cons, true_or, or_true]⟩)
      (fun p t h => h.ok.1) (fun _ => rfl) (fun _ => rfl) (by decide) hmgfCtr) fun p t h => ?_) ?_
  · obtain ⟨V, W, R, hw, -⟩ := h.pub.W
    have w := mws_w hw
    have := h.lt; have := h.ok.2.fit; have := h.ok.2.e1
    have hc : p.2 ≤ p.2 * G.D := Nat.le_mul_of_pos_right _ hzD
    exact X86_64.WP.mono_syms (updCtr_ok h.pub.L R w.2.2.2.2.1 w.2.2.2.2.2.1 (by omega_arith))
      fun t' ⟨L', hdi, hsi, hdx, hcx, h8, k, R'⟩ sy => ⟨h.after L' k.2.2 R' hw sy, hdi, hsi, hdx, hcx, h8⟩
  refine RelCT.seq (two_post (Ψ := Q0 G g n H) (two_scall n (s := sUpdG) (by decide) (fun p => p.1.F)
      (fun p => p.1.S) (fun p => p.1.rest) (fun p => p.1.sy G.updN)
      (fun p t h => ⟨h.1.pub.L, h.1.pub.wr, h.1.ok.1, pub_slot h.1.pub (k := 12) rfl (by decide) (by simp only [mws, List.mem_cons, true_or, or_true]),
        h.1.sy.2.2.1, h.1.sy.1.fu⟩) (hfx.ld _ (.inr (.inr (.inr (.inr (.inl rfl))))))
      (two_upd hG (fun p => p.1.F) (fun p => p.1.S) (fun _ => oLen) (fun _ => 4)
        (fun _ => BitVec.ofNat 64 H.D) fun p t ⟨t₀, h, k, hm, _⟩ =>
          ⟨lay_keep11 h.1.pub.L k hm, by omega_arith, Or.inr (by omega_arith), Or.inr (by omega_arith),
            (k.gpr (by decide)).trans h.2.1, (k.gpr (by decide)).trans h.2.2.1, (k.gpr (by decide)).trans h.2.2.2.1,
            (k.gpr (by decide)).trans h.2.2.2.2.1, (k.gpr (by decide)).trans h.2.2.2.2.2⟩)) fun p t h => ?_) ?_
  · obtain ⟨V, W, R, hw, -⟩ := h.1.pub.W
    exact X86_64.WP.mono_syms (updS_ok hG h.1.pub.L R (mws_gt h.1.sy hw)
        (a := oLen) (len := 4) (by omega_arith) (Or.inr (by omega_arith)) (Or.inr (by omega_arith))
        h.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2)
      fun t' ⟨L', _, wr', _, R', _⟩ sy => h.1.after L' wr' R' hw sy
  -- `finalize`.
  refine RelCT.seq (two_post (Ψ := Q7 G g n H) (two_pub n [21, 30] [] (fun p => p.1.F) (fun p => p.1.S)
      (fun p => p.1.rest) (fun p => [(21, p.1.S), (30, BitVec.ofNat 64 H.D)])
      (fun _ => []) (fun p t h => ⟨_, h.sub fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl <;> simp only [mws, List.mem_cons, true_or, or_true]⟩)
      (fun p t h => h.ok.1) (fun _ => rfl) (fun _ => rfl) (by decide) hmgfFin) fun p t h => ?_) ?_
  · obtain ⟨V, W, R, hw, -⟩ := h.pub.W
    have w := mws_w hw
    exact X86_64.WP.mono_syms (finA_ok h.pub.L R w.2.2.2.2.1)
      fun t' ⟨hdi, hsi, hdx, hcx, hm, k⟩ sy => ⟨h.keepM (k.gpr (by decide)) k.2.2 hm sy, hdi, hsi, hdx, hcx⟩
  refine RelCT.seq (two_post (Ψ := Q0 G g n H) (two_scall n (s := sFinG) (by decide) (fun p => p.1.F)
      (fun p => p.1.S) (fun p => p.1.rest) (fun p => p.1.sy G.finN)
      (fun p t h => ⟨h.1.pub.L, h.1.pub.wr, h.1.ok.1, pub_slot h.1.pub (k := 13) rfl (by decide) (by simp only [mws, List.mem_cons, true_or, or_true]),
        h.1.sy.2.2.2, h.1.sy.1.ff⟩) (hfx.ld _ (.inr (.inr (.inr (.inr (.inr rfl))))))
      (two_fin hG (fun p => p.1.F) (fun p => p.1.S) (fun _ => oDig) (fun _ => BitVec.ofNat 64 (H.D + 4))
        fun p t ⟨t₀, h, k, hm, _⟩ =>
          ⟨lay_keep11 h.1.pub.L k hm, ⟨by omega_arith, by omega_arith⟩, (k.gpr (by decide)).trans h.2.1,
            (k.gpr (by decide)).trans h.2.2.1, (k.gpr (by decide)).trans h.2.2.2.1,
            (k.gpr (by decide)).trans h.2.2.2.2⟩)) fun p t h => ?_) ?_
  · obtain ⟨V, W, R, hw, -⟩ := h.1.pub.W
    exact X86_64.WP.mono_syms (finS_ok hG h.1.pub.L R (mws_gt h.1.sy hw) (o := oDig)
        ⟨by omega_arith, by omega_arith⟩ h.2.1 h.2.2.2.1 h.2.2.2.2)
      fun t' ⟨L', _, wr', _, R', _⟩ sy => h.1.after L' wr' R' hw sy
  -- Into `DB`, and the next counter.
  refine RelCT.seq (two_post (Ψ := Q0 G g n H) (two_pub n [14, 21, 23, 24, 32] [] (fun p => p.1.F)
      (fun p => p.1.S) (fun p => p.1.rest)
      (fun p => [(14, BitVec.ofNat 64 G.D), (21, p.1.S), (23, off p.1.S p.1.e), (24, BitVec.ofNat 64 p.1.db),
        (32, BitVec.ofNat 64 (p.2 * G.D))])
      (fun _ => []) (fun p t h => ⟨_, h.sub fun q hq => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp only [mws, List.mem_cons, true_or, or_true]⟩)
      (fun p t h => h.ok.1) (fun _ => rfl) (fun _ => rfl) (by decide) hmgfXorOut) fun p t h => ?_) ?_
  · obtain ⟨V, W, R, hw, -⟩ := h.pub.W
    have w := mws_w hw
    have := h.ok.2.fit; have := h.ok.2.e1
    exact X86_64.WP.mono_syms (xorOut_ok (G := G) h.pub.L R (dst := p.1.e) (dstLen := p.1.db) (done := p.2 * G.D)
        (by omega_arith) (by omega_arith) hzD (by omega_arith) w.1 w.2.1 w.2.2.1 w.2.2.2.2.2.2 h.lt)
      fun t' ⟨L', k, R'⟩ sy => h.after L' k.2.2 R' hw sy
  exact two_pub n [14, 24, 31, 32] [] (fun p => p.1.F) (fun p => p.1.S) (fun p => p.1.rest)
    (fun p => [(14, BitVec.ofNat 64 G.D), (24, BitVec.ofNat 64 p.1.db), (31, BitVec.ofNat 64 p.2),
      (32, BitVec.ofNat 64 (p.2 * G.D))])
    (fun _ => []) (fun p t h => ⟨_, h.sub fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl <;> simp only [mws, List.mem_cons, true_or, or_true]⟩)
    (fun p t h => h.ok.1) (fun _ => rfl) (fun _ => rfl) (by decide) hmgfNext

/-! ## The loop -/

variable (G g n H) in
/-- Before round `j`: the correctness proof's invariant. -/
def MI (a : MA) (j : Nat) (t : State) : Prop :=
  MOk n H a ∧ j * G.D < a.db ∧ ∃ (u₀ : State) (V : Nat → Byte) (W : Nat → BitVec 64),
    u₀.wr = ⟨a.F, frameBytes⟩ :: a.rest ∧ SyG G g a.sy u₀.syms ∧ W 21 = a.S ∧ W 23 = off a.S a.e ∧
    W 24 = BitVec.ofNat 64 a.db ∧ W 29 = off a.S (a.e + a.db) ∧ W 30 = BitVec.ofNat 64 H.D ∧ GT G g W u₀.syms ∧
    MgfI u₀ a.F a.S V W (Spec.Mgf1.mgf1 Gs ((List.range H.D).map fun i => V (a.e + a.db + i)) a.db)
      a.e a.db G.D j t

theorem mi_rp {a : MA} {j : Nat} {t : State} (h : MI G g n H (Gs := Gs) a j t) : RP G g n H a j t := by
  obtain ⟨hok, hj, u₀, V, W, hwr, hsy, h21, h23, h24, h29, h30, T, I⟩ := h
  obtain ⟨V', W', R', h31, h32, hW, -⟩ := I.rep
  have e : ∀ k, k < nW → k ≠ 31 → k ≠ 32 → W' k = W k := hW
  refine ⟨hok, hj, ⟨I.L, I.wr.trans hwr, ⟨V', W', R', fun q hq => ?_, trivial⟩, fun _ hp => by cases hp⟩,
    hsy.tr I.sy⟩
  simp only [mws, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (e 21 (by decide) (by decide) (by decide)).trans h21
  · exact (e 23 (by decide) (by decide) (by decide)).trans h23
  · exact (e 24 (by decide) (by decide) (by decide)).trans h24
  · exact (e 29 (by decide) (by decide) (by decide)).trans h29
  · exact (e 30 (by decide) (by decide) (by decide)).trans h30
  · exact h31
  · exact h32
  · exact (e 14 (by decide) (by decide) (by decide)).trans T.wd
  · exact (e 11 (by decide) (by decide) (by decide)).trans (T.wi.trans hsy.2.1)
  · exact (e 12 (by decide) (by decide) (by decide)).trans (T.wu.trans hsy.2.2.1)
  · exact (e 13 (by decide) (by decide) (by decide)).trans (T.wf.trans hsy.2.2.2)

include hG hGh hGl hGv in
theorem round_wp {a : MA} {j : Nat} {t : State} (h : MI G g n H (Gs := Gs) a j t) :
    WP isa (mgfRound g) t fun t' =>
      isa.eval .b t' = some (decide (j + 1 < mN G.D a)) ∧ (j + 1 < mN G.D a → MI G g n H (Gs := Gs) a (j + 1) t') ∧
      (j + 1 = mN G.D a → True) := by
  have hD := (sizes hG).2.2.2.2
  obtain ⟨hok, hjD, u₀, V, W, hwr, hsy, h21, h23, h24, h29, h30, T, I⟩ := h
  refine WP.mono (round_ok hG hGh hGl hGv hok.2 h23 h24 h29 h30 T I hjD) fun t' ⟨hcf, I'⟩ => ⟨?_, fun h' =>
    ⟨hok, (cnt_iff hD).mp h', u₀, V, W, hwr, hsy, h21, h23, h24, h29, h30, T, I'⟩, fun _ => trivial⟩
  simp only [eval, hcf, Option.some.injEq, decide_eq_decide]
  exact (cnt_iff hD).symm

variable (G g n H) in
/-- At the start: the public words of `DB` and the slots of the table of
`Hash`. -/
def ME (a : MA) (t : State) : Prop :=
  MOk n H a ∧ Pub a.F a.S a.rest [(21, a.S), (23, off a.S a.e), (24, BitVec.ofNat 64 a.db),
    (14, BitVec.ofNat 64 G.D), (11, a.sy G.initN), (12, a.sy G.updN), (13, a.sy G.finN)] [] (fun _ _ => True) t ∧
    SyG G g a.sy t.syms

include hG in
theorem mgfHead_ct (hc : HashChecks H.P H.D n) :
    RelCT isa (Two (ME G g n H))
      (.block (mgfSeed H ++ ([.mov32 .rax (.imm 0), .store (sp sCtr) .rax, .store (sp sDone) .rax] : List Instr)))
      (Two fun a t => 0 < mN G.D a ∧ MI G g n H (Gs := Gs) a 0 t) := by
  have hD := (sizes hG).2.2.2.2
  obtain ⟨_, hhd⟩ := hc.mgfHead
  refine two_post (two_pub n [21, 23, 24] [] MA.F MA.S MA.rest
    (fun a => [(21, a.S), (23, off a.S a.e), (24, BitVec.ofNat 64 a.db)]) (fun _ => [])
    (fun a t h => ⟨_, h.2.1.sub (fun q hq => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl <;> simp) (fun _ h => h) fun _ _ x => x⟩)
    (fun a t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hhd) fun a t h => ?_
  obtain ⟨V, W, R, hw, -⟩ := h.2.1.W
  have hp : ∀ {k v}, (k, v) ∈ [(21, a.S), (23, off a.S a.e), (24, BitVec.ofNat 64 a.db),
      (14, BitVec.ofNat 64 G.D), (11, a.sy G.initN), (12, a.sy G.updN), (13, a.sy G.finN)] → W k = v :=
    fun hm => hw _ hm
  have hdb1 := h.1.2.db1
  refine X86_64.WP.mono_syms (mgfHead_ok H h.2.1.L R h.1.2 (hp (by simp)) (hp (by simp)))
    fun v ⟨Lv, hk, Rv⟩ sv => ?_
  let W₀ := upd (upd W 29 (off a.S (a.e + a.db))) 30 (BitVec.ofNat 64 H.D)
  have hW₀ : ∀ k, k ≠ 29 → k ≠ 30 → W₀ k = W k := fun k h1 h2 => by simp only [W₀, upd, ifn h1, ifn h2]
  have T₀ : GT G g W₀ v.syms := by
    rw [sv]
    exact h.2.2.1.gt (((hW₀ 11 (by decide) (by decide)).trans (hp (by simp))).trans h.2.2.2.1.symm)
      (((hW₀ 12 (by decide) (by decide)).trans (hp (by simp))).trans h.2.2.2.2.1.symm)
      (((hW₀ 13 (by decide) (by decide)).trans (hp (by simp))).trans h.2.2.2.2.2.symm)
      ((hW₀ 14 (by decide) (by decide)).trans (hp (by simp)))
  refine ⟨(cnt_iff hD).mpr (by rw [Nat.zero_mul]; omega_arith), h.1, by rw [Nat.zero_mul]; omega_arith, v, V, W₀,
    hk.2.2.trans h.2.1.wr, h.2.2.tr sv, (hW₀ 21 (by decide) (by decide)).trans (hp (by simp)),
    (hW₀ 23 (by decide) (by decide)).trans (hp (by simp)), (hW₀ 24 (by decide) (by decide)).trans (hp (by simp)),
    by simp [W₀, upd], by simp [W₀, upd], T₀,
    ⟨Lv, rfl, rfl, fun _ _ => rfl, rfl, _, _, Rv, by simp [upd], by simp [upd],
      fun k _ h1 h2 => by simp only [upd, ifn h2, ifn h1]; rfl,
      fun o _ _ => by simp only [mixV, Nat.zero_mul, Nat.zero_min, Nat.add_zero]; rw [ifn (by omega_arith)]⟩⟩

include hG hGh hGl hGv in
/-- `mgfXor` is constant time. -/
theorem mgfXor_ct (hc : HashChecks H.P H.D n) (hfx : FixedChecks n) :
    RelCT isa (Two (ME G g n H)) (mgfXor H g) fun _ _ => True :=
  (mgfHead_ct hG (Gs := Gs) hc).seq ((two_loop (Φ := MI G g n H (Gs := Gs)) (Ψ := fun _ _ => True) (mN G.D)
    (two_map id (fun _ _ h => mi_rp h.2) (round_ct hG hfx))
    fun _ _ _ _ h => round_wp hG hGh hGl hGv h).mono (fun _ _ h => h) fun _ _ _ => trivial)

end VG.Proof.RsaPss.X86_64

end

end

/-! ### `RsaPss.X86_64.VerifyCtBase`, which this module and modules that import it used -/

section

/-!
# RSASSA-PSS verification on x86-64: two runs

Two runs of `verify` from states meeting `verifyK.pre` whose public data
agree (`VSib a s`: each run's entry state `s` agrees with the first's, `a`)
compute the same public values (`vw`): the arguments, the encoding's length,
`DB`'s place and length, the mask of the top bits, the expected salt length
and the hash's blocks. The secret ones (the signature, the digest, and what
the code derives from them, such as the salt's length when any is allowed)
stay out of `vw`. A run's state between two pieces is described by `VS`:
its frame, and its public words, those of `vw`; both runs then start the
next piece's taint analysis from the same public values (`vtwo`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

variable (tsH tsG : List FnTable)

/-- Word 5 of the table `hash`: the index of its hash function. -/
def vidxWord (s : State) : BitVec 64 := s.mem.readW (off (stackArg s 8) 40) 64

/-- The entry state `s` of a run, and the first's, `a`: both meet the
precondition, their public data agree, and so does the index of the hash
function of the table `hash` (word 5 of the table, which the tables of
`MdHash` the precondition allows give, and the public data fix). -/
def VSib (a s : State) : Prop :=
  VPre tsH tsG a ∧ (verifyK tsH tsG).pub a s ∧ VPre tsH tsG s ∧ vidxWord s = vidxWord a

/-- A predicate of the state of a run, given its entry state, for every run
whose entry state agrees with `a`. -/
def VAt (J : State → State → Prop) (a t : State) : Prop := ∃ s, VSib tsH tsG a s ∧ J s t

theorem vpub_refl (s : State) : (verifyK tsH tsG).pub s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl,
    fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

variable {tsH tsG}

namespace VSib

variable {a s : State} (h : VSib tsH tsG a s)
include h

theorem gpr {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) : s.gpr r = a.gpr r :=
  (h.2.1.1 r hr).symm

theorem sig : stackArg s 0 = stackArg a 0 := h.2.1.2.1.symm
theorem arg1 : stackArg s 2 = stackArg a 2 := h.2.1.2.2.2.1.symm
theorem arg2 : (stackArg s 3).setWidth 32 = (stackArg a 3).setWidth 32 := h.2.1.2.2.2.2.1.symm
theorem arg3 : stackArg s 4 = stackArg a 4 := h.2.1.2.2.2.2.2.1.symm
theorem arg4 : stackArg s 5 = stackArg a 5 := h.2.1.2.2.2.2.2.2.1.symm
theorem arg6 : stackArg s 6 = stackArg a 6 := h.2.1.2.2.2.2.2.2.2.1.symm
theorem arg7 : stackArg s 7 = stackArg a 7 := h.2.1.2.2.2.2.2.2.2.2.1.symm
theorem arg8 : stackArg s 8 = stackArg a 8 := h.2.1.2.2.2.2.2.2.2.2.2.1.symm
theorem arg9 : stackArg s 9 = stackArg a 9 := h.2.1.2.2.2.2.2.2.2.2.2.2.1.symm

theorem nB : Spec.Rsa.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat =
    Spec.Rsa.bytesAt a.mem (a.gpr .rdi) (a.gpr .rsi).toNat := h.2.1.2.2.2.2.2.2.2.2.2.2.2.1.symm

theorem eB : Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat =
    Spec.Rsa.bytesAt a.mem (a.gpr .rdx) (a.gpr .rcx).toNat := h.2.1.2.2.2.2.2.2.2.2.2.2.2.2.1.symm

theorem preW : Spec.Rsa.wordsAt s.mem (stackArg s 6) (stackArg s 7).toNat =
    Spec.Rsa.wordsAt a.mem (stackArg a 6) (stackArg a 7).toNat := h.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm

theorem pa : VPre tsH tsG a := h.1
theorem ps : VPre tsH tsG s := h.2.2.1
theorem idxw : vidxWord s = vidxWord a := h.2.2.2

theorem fb : fb s = fb a := by
  simp only [VG.Proof.RsaPss.X86_64.fb, h.gpr (r := .rsp) (by decide)]

theorem wr : s.wr = a.wr := by rw [h.ps.hwr, h.pa.hwr, h.arg3, h.arg4]

theorem frR : frR s = ⟨VG.Proof.RsaPss.X86_64.fb a, frameBytes⟩ := by
  simp only [VG.Proof.RsaPss.X86_64.frR, h.fb]

theorem n0 : s.mem (s.gpr .rdi) = a.mem (a.gpr .rdi) := by
  have := congrArg (fun l => l.getD 0 0) h.nB
  have hk := h.ps.k1
  have hk' := h.pa.k1
  simpa [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_range (show 0 < (s.gpr .rsi).toNat by omega_using [hk]),
    List.getElem?_range (show 0 < (a.gpr .rsi).toNat by omega_using [hk'])] using this

end VSib

/-! ## The public values -/

/-- The modulus' first byte. -/
def n0v (s : State) : Nat := (s.mem (s.gpr .rdi)).toNat

/-- `lo`: 1 if the modulus' first byte is 1 (`EM` one byte shorter). -/
def vlo (s : State) : Nat := loV (n0v s)

/-- `emLen`. -/
def veml (s : State) : Nat := (s.gpr .rsi).toNat - vlo s

/-- `dbLen`. -/
def vdb (D : Nat) (s : State) : Nat := veml s - D - 1

/-- The blocks of the hash of `M'`. -/
def vnb (H : Hash) (s : State) : Nat := (vdb H.D s + (7 + H.D + H.P.L)) / H.P.B + 1

/-- The public words of the frame, by index. -/
def vw (H : Hash) (s : State) (k : Nat) : BitVec 64 :=
  match k with
  | 2 => stackArg s 8
  | 3 => stackArg s 9
  | 47 => vidxWord s
  | 17 => s.gpr .rsi
  | 18 => s.gpr .rdi
  | 19 => s.gpr .rdx
  | 20 => s.gpr .rcx
  | 21 => stackArg s 4
  | 22 => stackArg s 5
  | 23 => off (stackArg s 4) (oEm + vlo s)
  | 24 => BitVec.ofNat 64 (vdb H.D s)
  | 25 => maskV (n0v s)
  | 26 => BitVec.ofNat 64 (vlo s)
  | 28 => BitVec.ofNat 64 (vnb H s)
  | 35 => if (stackArg s 3).setWidth 32 = 0 then 0 else 1
  | 36 => stackArg s 2
  | 37 => s.gpr .r8
  | 38 => stackArg s 0
  | _ => 0

/-- The public words `ks`. -/
def pw (H : Hash) (s : State) (ks : List Nat) : List (Nat × BitVec 64) := ks.map fun k => (k, vw H s k)

namespace VSib

variable {a s : State} (h : VSib tsH tsG a s)
include h

theorem n0v : n0v s = n0v a := by simp only [VG.Proof.RsaPss.X86_64.n0v, h.n0]
theorem vlo : vlo s = vlo a := by simp only [VG.Proof.RsaPss.X86_64.vlo, h.n0v]
theorem veml : veml s = veml a := by
  simp only [VG.Proof.RsaPss.X86_64.veml, h.vlo, h.gpr (r := .rsi) (by decide)]
theorem vdb {D : Nat} : vdb D s = vdb D a := by simp only [VG.Proof.RsaPss.X86_64.vdb, h.veml]
theorem vnb {H : Hash} : vnb H s = vnb H a := by simp only [VG.Proof.RsaPss.X86_64.vnb, h.vdb]
theorem vw {H : Hash} (k : Nat) : vw H s k = vw H a k := by
  unfold VG.Proof.RsaPss.X86_64.vw
  split <;> simp only [h.gpr (r := .rsi) (by decide), h.gpr (r := .rdi) (by decide),
    h.gpr (r := .rdx) (by decide), h.gpr (r := .rcx) (by decide), h.gpr (r := .r8) (by decide),
    h.sig, h.arg1, h.arg2, h.arg3, h.arg4, h.vlo, h.vdb, h.n0v, h.vnb, h.arg8, h.arg9, h.idxw]

/-- The frame and the working space are apart. -/
theorem rest : RestOk 1 (VG.Proof.RsaPss.X86_64.fb a) a.wr := by
  have hp := h.pa
  refine ⟨by rw [hp.hwr]; rfl, ?_, ?_⟩
  · rw [hp.hwr]
    refine List.pairwise_pair.mpr ?_
    exact (hp.dKs.sub_left (vframe_sub a))
  · rw [hp.hwr]; intro r hr
    rw [List.mem_singleton.mp hr]
    have := hp.wS; dsimp only; omega_using [this]

end VSib

/-! ## A run's state between pieces -/

/-- A run, with entry state `s`, between two pieces: its frame, its public
words `ks` (`vw`), the registers `rs`, and what else is true of its working
space and words (`X`). -/
structure VS (H : Hash) (s t : State) (ks : List Nat) (rs : List (Reg × BitVec 64))
    (X : (Nat → Byte) → (Nat → BitVec 64) → Prop) : Prop where
  L : Lay t (fb s) (stackArg s 4)
  wr : t.wr = frR s :: s.wr
  W : ∃ V W, Rep t.mem (fb s) (stackArg s 4) V W ∧ (∀ k ∈ ks, W k = vw H s k) ∧ X V W
  regs : ∀ p ∈ rs, t.gpr p.1 = p.2
  sy : t.syms = s.syms

variable {H : Hash}

theorem vs_pub {a s t : State} (S : VSib tsH tsG a s) {ks : List Nat} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : VS H s t ks rs X) :
    Pub (fb a) (stackArg a 4) a.wr (pw H a ks) rs X t := by
  obtain ⟨V, W, R, hw, hx⟩ := h.W
  refine ⟨?_, ?_, ⟨V, W, ?_, fun p hp => ?_, hx⟩, h.regs⟩
  · rw [← S.fb, ← S.arg3]; exact h.L
  · rw [h.wr, S.frR, S.wr]
  · rw [← S.fb, ← S.arg3]; exact R
  · simp only [pw, List.mem_map] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    rw [hw k hk, S.vw]

/-- A piece the analysis checks from `pT 1 ks rgs`. -/
theorem vtwo {Φ : State → State → Prop} {c : Prog isa} (ks : List Nat) (rgs : List Reg)
    (rs : State → List (Reg × BitVec 64))
    (hΦ : ∀ a t, Φ a t → ∃ s X, VSib tsH tsG a s ∧ VS H s t ks (rs a) X) (hr : ∀ a, (rs a).map Prod.fst = rgs)
    (hks : ∀ k ∈ ks, k < nW) {hc : VG.Taint.Hint X86_64.Taint.T}
    (h : (taint.check (pT 1 ks rgs) c hc).isSome = true) : RelCT isa (Two Φ) c fun _ _ => True :=
  two_pub 1 ks rgs fb (fun a => stackArg a 4) State.wr (fun a => pw H a ks) rs
    (fun a t h => let ⟨_, X, S, v⟩ := hΦ a t h; ⟨X, vs_pub S v⟩) (fun a t h => let ⟨_, _, S, _⟩ := hΦ a t h; S.rest)
    (fun a => by simp [pw, Function.comp_def]) hr hks h

/-- `VS` after code that keeps the memory and the registers but `rs'`. -/
theorem VS.keep {s t t' : State} {ks : List Nat} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : VS H s t ks rs X) {rs' : List Reg} (k : Keep rs' t t')
    (hm : t'.mem = t.mem) (hsp : Reg.rsp ∉ rs') (hrs : ∀ p ∈ rs, p.1 ∉ rs') (hs : t'.syms = t.syms) :
    VS H s t' ks rs X :=
  ⟨h.L.congr (k.gpr hsp) k.2.2 (by rw [hm]), k.2.2.trans h.wr, by rw [hm]; exact h.W,
    fun p hp => (k.gpr (hrs p hp)).trans (h.regs p hp), hs.trans h.sy⟩

/-- `VS` after code that keeps the regions and the scratch slot. -/
theorem VS.next {s t t' : State} {ks ks' : List Nat} {rs : List (Reg × BitVec 64)}
    {X X' : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : VS H s t ks rs X) (L' : Lay t' (fb s) (stackArg s 4))
    (hwr : t'.wr = t.wr) {V' : Nat → Byte} {W' : Nat → BitVec 64} (R' : Rep t'.mem (fb s) (stackArg s 4) V' W')
    (hw : ∀ k ∈ ks', W' k = vw H s k) (hx : X' V' W') (hs : t'.syms = t.syms) : VS H s t' ks' [] X' :=
  ⟨L', hwr.trans h.wr, ⟨V', W', R', hw, hx⟩, (fun _ hp => by cases hp), hs.trans h.sy⟩


theorem VS.sub {s t : State} {ks ks' : List Nat} {rs : List (Reg × BitVec 64)}
    {X X' : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : VS H s t ks rs X) (hks : ∀ k ∈ ks', k ∈ ks)
    (rs' : List (Reg × BitVec 64)) (hrs : ∀ p ∈ rs', t.gpr p.1 = p.2) (hX : ∀ V W, X V W → X' V W) :
    VS H s t ks' rs' X' := by
  obtain ⟨V, W, R, hw, hx⟩ := h.W
  exact ⟨h.L, h.wr, ⟨V, W, R, fun k hk => hw k (hks k hk), hX V W hx⟩, hrs, h.sy⟩

/-- A piece the analysis checks from `pT 1 (ks ++ eks) rgs`: the public
words `ks` of `vw`, and `ex`, of the anchor. -/
theorem vtwoX {α : Type} {Φ : α → State → Prop} {c : Prog isa} (π : α → State) (ks : List Nat)
    (ex : α → List (Nat × BitVec 64)) (eks : List Nat) (rgs : List Reg) (rs : α → List (Reg × BitVec 64))
    (hΦ : ∀ a t, Φ a t → ∃ s, VSib tsH tsG (π a) s ∧ VS H s t ks (rs a) fun _ W => ∀ p ∈ ex a, W p.1 = p.2)
    (he : ∀ a, (ex a).map Prod.fst = eks) (hr : ∀ a, (rs a).map Prod.fst = rgs)
    (hks : ∀ k ∈ ks ++ eks, k < nW) {hc : VG.Taint.Hint X86_64.Taint.T}
    (h : (taint.check (pT 1 (ks ++ eks) rgs) c hc).isSome = true) : RelCT isa (Two Φ) c fun _ _ => True :=
  two_pub 1 (ks ++ eks) rgs (fun a => fb (π a)) (fun a => stackArg (π a) 4) (fun a => (π a).wr)
    (fun a => pw H (π a) ks ++ ex a) rs
    (fun a t h => by
      obtain ⟨s, S, v⟩ := hΦ a t h
      obtain ⟨L, w, ⟨V, W, R, hw, hx⟩, rg⟩ := vs_pub S v
      exact ⟨fun _ _ => True, L, w, ⟨V, W, R, fun p hp => (List.mem_append.mp hp).elim (hw p) (hx p), trivial⟩, rg⟩)
    (fun a t h => let ⟨_, S, _⟩ := hΦ a t h; S.rest)
    (fun a => by simp [pw, Function.comp_def, he a]) hr hks h

theorem fnz_lt {f : Nat → Byte} : ∀ {j i : Nat}, fnz f j = some i → i < j
  | 0, _, h => by simp [fnz] at h
  | j + 1, i, h => by
    simp only [fnz] at h
    split at h
    · rename_i k hk
      cases h; exact Nat.lt_succ_of_lt (fnz_lt hk)
    · split at h
      · cases h
      · cases h; exact Nat.lt_succ_self _

theorem fnz_getD_lt {f : Nat → Byte} {j : Nat} (hj : 1 ≤ j) : (fnz f j).getD 0 < j := by
  cases h : fnz f j with
  | none => simp only [Option.getD_none]; omega_using [hj]
  | some i => exact fnz_lt h

end VG.Proof.RsaPss.X86_64

end

end

/-! ### `RsaPss.X86_64.ChkCtMid`, which only this module used -/

section

/-! ### `RsaPss.X86_64.ChkCtBase`, which only this module used -/

section

/-!
# EMSA-PSS's check of an encoding on x86-64: two runs

As for verification (`VerifyCtBase`): two runs of `checkEncoding` from states
meeting `chkK.pre` whose public data agree (`VSib a s`) compute the same
public values (`vw`): the arguments, the encoding's length, `DB`'s place and
length, the mask of the top bits, the expected salt length and the hash's
blocks. The digest, the encoding, and what the code derives from them (the
salt's length when any is allowed) stay out of `vw`. A run's state between
two pieces is described by `VS`; both runs then start the next piece's
taint analysis from the same public values (`vtwo`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Chk

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

variable (T : Tabs)

/-- `chkK.pub`, which does not depend on the hash functions. -/
def CPub (s₁ s₂ : State) : Prop :=
  (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .rsp], s₁.gpr r = s₂.gpr r) ∧
    (s₁.gpr .r9).setWidth 32 = (s₂.gpr .r9).setWidth 32 ∧
    (List.range 4).map (stackArg s₁) = (List.range 4).map (stackArg s₂) ∧
    tabWords s₁.mem (stackArg s₁ 2) (stackArg s₁ 3) = tabWords s₂.mem (stackArg s₂ 2) (stackArg s₂ 3)

/-- The entry state `s` of a run, and the first's, `a`: both meet the
precondition, and their public data agree. -/
def VSib (a s : State) : Prop := Pre T a ∧ CPub a s ∧ Pre T s

/-- A predicate of the state of a run, given its entry state, for every run
whose entry state agrees with `a`. -/
def VAt (J : State → State → Prop) (a t : State) : Prop := ∃ s, VSib T a s ∧ J s t

theorem vpub_refl (s : State) : CPub s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

variable {T}

namespace VSib

variable {a s : State} (h : VSib T a s)
include h

theorem gpr {r : Reg} (hr : r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .rsp]) : s.gpr r = a.gpr r :=
  (h.2.1.1 r hr).symm

theorem rsl : s.gpr .r8 = a.gpr .r8 := h.gpr (by decide)
theorem r9 : (s.gpr .r9).setWidth 32 = (a.gpr .r9).setWidth 32 := h.2.1.2.1.symm

theorem arg {i : Nat} (hi : i < 4) : stackArg s i = stackArg a i := by
  have := congrArg (fun l => l.getD i 0) h.2.1.2.2.1
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.getD_some] at this
  exact this.symm

theorem arg0 : stackArg s 0 = stackArg a 0 := h.arg (by decide)
theorem arg1 : stackArg s 1 = stackArg a 1 := h.arg (by decide)

theorem pa : Pre T a := h.1
theorem ps : Pre T s := h.2.2

/-- The words of the tables. -/
theorem tws : s.mem.readW (off (stackArg s 2) 0) 64 = a.mem.readW (off (stackArg a 2) 0) 64 ∧
    s.mem.readW (off (stackArg s 2) 24) 64 = a.mem.readW (off (stackArg a 2) 24) 64 ∧
    s.mem.readW (off (stackArg s 2) 32) 64 = a.mem.readW (off (stackArg a 2) 32) 64 ∧
    s.mem.readW (off (stackArg s 3) 0) 64 = a.mem.readW (off (stackArg a 3) 0) 64 ∧
    s.mem.readW (off (stackArg s 3) 8) 64 = a.mem.readW (off (stackArg a 3) 8) 64 ∧
    s.mem.readW (off (stackArg s 3) 16) 64 = a.mem.readW (off (stackArg a 3) 16) 64 ∧
    s.mem.readW (off (stackArg s 3) 48) 64 = a.mem.readW (off (stackArg a 3) 48) 64 := by
  have := h.2.1.2.2.2.symm
  simp only [tabWords, List.cons.injEq, and_true] at this
  exact this

/-- The runs' symbols agree on the tables' functions. -/
theorem syH : SyH T.H T.dn T.f a.syms s.syms :=
  ⟨h.ps.tabs.hf, h.ps.tabs.h0.symm.trans (h.tws.1.trans h.pa.tabs.h0),
    h.ps.tabs.h3.symm.trans (h.tws.2.1.trans h.pa.tabs.h3), h.ps.tabs.h4.symm.trans (h.tws.2.2.1.trans h.pa.tabs.h4)⟩

theorem syG : SyG T.G T.g a.syms s.syms :=
  ⟨h.ps.tabs.gf, h.ps.tabs.g0.symm.trans (h.tws.2.2.2.1.trans h.pa.tabs.g0),
    h.ps.tabs.g1.symm.trans (h.tws.2.2.2.2.1.trans h.pa.tabs.g1),
    h.ps.tabs.g2.symm.trans (h.tws.2.2.2.2.2.1.trans h.pa.tabs.g2)⟩

theorem fb : fb s = fb a := by
  simp only [VG.Proof.RsaPss.X86_64.fb, h.gpr (r := .rsp) (by decide)]

theorem wr : s.wr = a.wr := by rw [h.ps.hwr, h.pa.hwr, h.arg0, h.arg1]

theorem frR : frR s = ⟨VG.Proof.RsaPss.X86_64.fb a, frameBytes⟩ := by
  simp only [VG.Proof.RsaPss.X86_64.frR, h.fb]

end VSib

/-! ## The public values -/

/-- `lo`, always 0. -/
def vlo (_s : State) : Nat := 0

/-- `emLen`. -/
def veml (s : State) : Nat := (s.gpr .rdx).toNat - vlo s

/-- The mask of `maskedDB`'s first byte. -/
def cmask (s : State) : Byte := (0xFF : Byte) >>> (8 * (s.gpr .rdx).toNat - (s.gpr .rcx).toNat)

/-- `dbLen`. -/
def vdb (D : Nat) (s : State) : Nat := veml s - D - 1

/-- The blocks of the hash of `M'`. -/
def vnb (H : Hash) (s : State) : Nat := (vdb H.D s + (7 + H.D + H.P.L)) / H.P.B + 1

/-- The expected salt length's register, 0 if any. -/
def vrdx (s : State) : BitVec 64 := if (s.gpr .r9).setWidth 32 = 0 then s.gpr .r8 else 0

/-- The public words of the frame, by index. -/
def vw (H : Hash) (s : State) (k : Nat) : BitVec 64 :=
  match k with
  | 8 => s.mem.readW (off (stackArg s 2) 0) 64
  | 9 => s.mem.readW (off (stackArg s 2) 24) 64
  | 10 => s.mem.readW (off (stackArg s 2) 32) 64
  | 11 => s.mem.readW (off (stackArg s 3) 0) 64
  | 12 => s.mem.readW (off (stackArg s 3) 8) 64
  | 13 => s.mem.readW (off (stackArg s 3) 16) 64
  | 14 => s.mem.readW (off (stackArg s 3) 48) 64
  | 17 => s.gpr .rdx
  | 21 => stackArg s 0
  | 23 => off (stackArg s 0) (oEm + vlo s)
  | 24 => BitVec.ofNat 64 (vdb H.D s)
  | 25 => BitVec.setWidth 64 (cmask s)
  | 26 => BitVec.ofNat 64 (vlo s)
  | 28 => BitVec.ofNat 64 (vnb H s)
  | 35 => if (s.gpr .r9).setWidth 32 = 0 then 0 else 1
  | 36 => s.gpr .r8
  | 37 => s.gpr .rdi
  | 38 => s.gpr .rsi
  | _ => 0

/-- The public words `ks`. -/
def pw (H : Hash) (s : State) (ks : List Nat) : List (Nat × BitVec 64) := ks.map fun k => (k, vw H s k)

namespace VSib

variable {a s : State} (h : VSib T a s)
include h

theorem vlo : vlo s = vlo a := by have _ := h; rfl
theorem veml : veml s = veml a := by
  simp only [VG.Proof.RsaPss.X86_64.Chk.veml, h.vlo, h.gpr (r := .rdx) (by decide)]
theorem vdb {D : Nat} : vdb D s = vdb D a := by simp only [VG.Proof.RsaPss.X86_64.Chk.vdb, h.veml]
theorem vnb {H : Hash} : vnb H s = vnb H a := by simp only [VG.Proof.RsaPss.X86_64.Chk.vnb, h.vdb]
theorem vrdx : vrdx s = vrdx a := by
  simp only [VG.Proof.RsaPss.X86_64.Chk.vrdx, h.r9, h.gpr (r := .r8) (by decide)]
theorem cmask : cmask s = cmask a := by
  simp only [VG.Proof.RsaPss.X86_64.Chk.cmask, h.gpr (r := .rdx) (by decide), h.gpr (r := .rcx) (by decide)]

theorem vw {H : Hash} (k : Nat) : vw H s k = vw H a k := by
  unfold VG.Proof.RsaPss.X86_64.Chk.vw
  split <;> simp only [h.gpr (r := .rsi) (by decide), h.gpr (r := .rdi) (by decide),
    h.gpr (r := .rdx) (by decide), h.gpr (r := .r8) (by decide), h.r9, h.arg0, h.vlo, h.vdb, h.vnb, h.cmask,
    h.tws.1, h.tws.2.1, h.tws.2.2.1, h.tws.2.2.2.1, h.tws.2.2.2.2.1, h.tws.2.2.2.2.2.1, h.tws.2.2.2.2.2.2]

/-- The frame and the working space are apart. -/
theorem rest : RestOk 1 (VG.Proof.RsaPss.X86_64.fb a) a.wr := by
  have hp := h.pa
  refine ⟨by rw [hp.hwr]; rfl, ?_, ?_⟩
  · rw [hp.hwr]
    refine List.pairwise_pair.mpr ?_
    exact (hp.dKs.sub_left (frame_sub a))
  · rw [hp.hwr]; intro r hr
    rw [List.mem_singleton.mp hr]
    have := hp.wS; dsimp only; omega_using [this]

end VSib

/-! ## A run's state between pieces -/

/-- The public words after the checks. -/
def K5 : List Nat := [8, 9, 10, 11, 12, 13, 14, 17, 21, 25, 26, 35, 36, 37, 38]

/-- And with `DB`'s. -/
def KM : List Nat := [8, 9, 10, 11, 12, 13, 14, 17, 21, 23, 24, 25, 26, 35, 36, 37, 38]

theorem km_k5 {k : Nat} (h : k ∈ KM) (h23 : k ≠ 23) (h24 : k ≠ 24) : k ∈ K5 :=
  (by decide : ∀ k ∈ KM, k ≠ 23 → k ≠ 24 → k ∈ K5) k h h23 h24

theorem km_lt {k : Nat} (h : k ∈ KM) : k < nW := by
  simp only [KM, List.mem_cons, List.not_mem_nil, or_false] at h; unfold nW frameBytes; omega_using [h]

/-- A run, with entry state `s`, between two pieces: its frame, its public
words `ks` (`vw`), the registers `rs`, and what else is true of its working
space and words (`X`). -/
structure VS (H : Hash) (s t : State) (ks : List Nat) (rs : List (Reg × BitVec 64))
    (X : (Nat → Byte) → (Nat → BitVec 64) → Prop) : Prop where
  L : Lay t (fb s) (stackArg s 0)
  wr : t.wr = frR s :: s.wr
  W : ∃ V W, Rep t.mem (fb s) (stackArg s 0) V W ∧ (∀ k ∈ ks, W k = vw H s k) ∧ X V W
  regs : ∀ p ∈ rs, t.gpr p.1 = p.2
  sy : t.syms = s.syms

variable {H : Hash}

theorem vs_pub {a s t : State} (S : VSib T a s) {ks : List Nat} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : VS H s t ks rs X) :
    Pub (fb a) (stackArg a 0) a.wr (pw H a ks) rs X t := by
  obtain ⟨V, W, R, hw, hx⟩ := h.W
  refine ⟨?_, ?_, ⟨V, W, ?_, fun p hp => ?_, hx⟩, h.regs⟩
  · rw [← S.fb, ← S.arg0]; exact h.L
  · rw [h.wr, S.frR, S.wr]
  · rw [← S.fb, ← S.arg0]; exact R
  · simp only [pw, List.mem_map] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    rw [hw k hk, S.vw]

/-- A piece the analysis checks from `pT 1 ks rgs`. -/
theorem vtwo {Φ : State → State → Prop} {c : Prog isa} (ks : List Nat) (rgs : List Reg)
    (rs : State → List (Reg × BitVec 64))
    (hΦ : ∀ a t, Φ a t → ∃ s X, VSib T a s ∧ VS H s t ks (rs a) X) (hr : ∀ a, (rs a).map Prod.fst = rgs)
    (hks : ∀ k ∈ ks, k < nW) {hc : VG.Taint.Hint X86_64.Taint.T}
    (h : (taint.check (pT 1 ks rgs) c hc).isSome = true) : RelCT isa (Two Φ) c fun _ _ => True :=
  two_pub 1 ks rgs fb (fun a => stackArg a 0) State.wr (fun a => pw H a ks) rs
    (fun a t h => let ⟨_, X, S, v⟩ := hΦ a t h; ⟨X, vs_pub S v⟩) (fun a t h => let ⟨_, _, S, _⟩ := hΦ a t h; S.rest)
    (fun a => by simp [pw, Function.comp_def]) hr hks h

/-- `VS` after code that keeps the memory and the registers but `rs'`. -/
theorem VS.keep {s t t' : State} {ks : List Nat} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : VS H s t ks rs X) {rs' : List Reg} (k : Keep rs' t t')
    (hm : t'.mem = t.mem) (hsp : Reg.rsp ∉ rs') (hrs : ∀ p ∈ rs, p.1 ∉ rs') (hs : t'.syms = t.syms) :
    VS H s t' ks rs X :=
  ⟨h.L.congr (k.gpr hsp) k.2.2 (by rw [hm]), k.2.2.trans h.wr, by rw [hm]; exact h.W,
    fun p hp => (k.gpr (hrs p hp)).trans (h.regs p hp), hs.trans h.sy⟩

/-- `VS` after code that keeps the regions and the scratch slot. -/
theorem VS.next {s t t' : State} {ks ks' : List Nat} {rs : List (Reg × BitVec 64)}
    {X X' : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : VS H s t ks rs X) (L' : Lay t' (fb s) (stackArg s 0))
    (hwr : t'.wr = t.wr) {V' : Nat → Byte} {W' : Nat → BitVec 64} (R' : Rep t'.mem (fb s) (stackArg s 0) V' W')
    (hw : ∀ k ∈ ks', W' k = vw H s k) (hx : X' V' W') (hs : t'.syms = t.syms) : VS H s t' ks' [] X' :=
  ⟨L', hwr.trans h.wr, ⟨V', W', R', hw, hx⟩, (fun _ hp => by cases hp), hs.trans h.sy⟩


theorem VS.sub {s t : State} {ks ks' : List Nat} {rs : List (Reg × BitVec 64)}
    {X X' : (Nat → Byte) → (Nat → BitVec 64) → Prop} (h : VS H s t ks rs X) (hks : ∀ k ∈ ks', k ∈ ks)
    (rs' : List (Reg × BitVec 64)) (hrs : ∀ p ∈ rs', t.gpr p.1 = p.2) (hX : ∀ V W, X V W → X' V W) :
    VS H s t ks' rs' X' := by
  obtain ⟨V, W, R, hw, hx⟩ := h.W
  exact ⟨h.L, h.wr, ⟨V, W, R, fun k hk => hw k (hks k hk), hX V W hx⟩, hrs, h.sy⟩

/-- A piece the analysis checks from `pT 1 (ks ++ eks) rgs`: the public
words `ks` of `vw`, and `ex`, of the anchor. -/
theorem vtwoX {α : Type} {Φ : α → State → Prop} {c : Prog isa} (π : α → State) (ks : List Nat)
    (ex : α → List (Nat × BitVec 64)) (eks : List Nat) (rgs : List Reg) (rs : α → List (Reg × BitVec 64))
    (hΦ : ∀ a t, Φ a t → ∃ s, VSib T (π a) s ∧ VS H s t ks (rs a) fun _ W => ∀ p ∈ ex a, W p.1 = p.2)
    (he : ∀ a, (ex a).map Prod.fst = eks) (hr : ∀ a, (rs a).map Prod.fst = rgs)
    (hks : ∀ k ∈ ks ++ eks, k < nW) {hc : VG.Taint.Hint X86_64.Taint.T}
    (h : (taint.check (pT 1 (ks ++ eks) rgs) c hc).isSome = true) : RelCT isa (Two Φ) c fun _ _ => True :=
  two_pub 1 (ks ++ eks) rgs (fun a => fb (π a)) (fun a => stackArg (π a) 0) (fun a => (π a).wr)
    (fun a => pw H (π a) ks ++ ex a) rs
    (fun a t h => by
      obtain ⟨s, S, v⟩ := hΦ a t h
      obtain ⟨L, w, ⟨V, W, R, hw, hx⟩, rg⟩ := vs_pub S v
      exact ⟨fun _ _ => True, L, w, ⟨V, W, R, fun p hp => (List.mem_append.mp hp).elim (hw p) (hx p), trivial⟩, rg⟩)
    (fun a t h => let ⟨_, S, _⟩ := hΦ a t h; S.rest)
    (fun a => by simp [pw, Function.comp_def, he a]) hr hks h

variable (H) in
/-- After the checks: the salt's length fits, `rax = emLen - hLen - 2`. -/
def J7 (s t : State) : Prop :=
  VS H s t K5 [] (fun _ _ => True) ∧ t.rd = s.rd ∧ Frame (wrR s) s.mem t.mem ∧
    t.gpr .rax = BitVec.ofNat 64 (veml s - (H.D + 2)) ∧
    t.cf = some (decide (veml s - (H.D + 2) < (vrdx s).toNat)) ∧ H.D + 2 ≤ veml s

variable (H) in
/-- After `DB`'s slots: the frame, the public words, what else `X` says. -/
def JM (X : State → (Nat → Byte) → (Nat → BitVec 64) → Prop) (s t : State) : Prop :=
  VS H s t KM [] (X s) ∧ t.rd = s.rd ∧ H.D + 2 ≤ veml s

end VG.Proof.RsaPss.X86_64.Chk

end

end


/-!
# RSASSA-PSS verification on x86-64: `DB` in two runs

After the call: `acc`'s first bits, `DB ⊕= MGF1(H)` (`mgfXor_ct`), its top
bits, and the scan for its first nonzero byte and the checks of it, each
constant time from the public words of both runs (`JM`). The scan's result,
the salt's position, is secret: only its bound is kept (`X7`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Chk

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

variable {T : Tabs}

theorem km_ne {k j : Nat} (h : k ∈ KM) (hj : j ∉ KM) : k ≠ j := fun e => hj (e ▸ h)

theorem km_upd {s : State} {W : Nat → BitVec 64} (hw : ∀ k ∈ KM, W k = vw T.H s k) {j : Nat} (hj : j ∉ KM)
    (v : BitVec 64) : ∀ k ∈ KM, upd W j v k = vw T.H s k := fun k hk => by
  simp only [upd]; rw [ifn (km_ne hk hj)]; exact hw k hk

/-- After the call, with nothing else. -/
abbrev JT (H : Hash) : State → State → Prop := JM H fun _ _ _ => True

/-- `JM` as a public piece's start. -/
theorem jm_vs {X : State → (Nat → Byte) → (Nat → BitVec 64) → Prop} {a t : State} (h : VAt T (JM T.H X) a t)
    (ks : List Nat) (hks : ∀ k ∈ ks, k ∈ KM := by decide) :
    ∃ s X', VSib T a s ∧ VS T.H s t ks [] X' :=
  let ⟨s, S, h⟩ := h; ⟨s, _, S, h.1.sub hks [] (fun _ hp => by cases hp) fun _ _ x => x⟩

theorem vlo_le (s : State) : vlo s ≤ 1 := Nat.zero_le 1

theorem acc0_ct : RelCT isa (Two (VAt T (JT T.H))) (.block acc0) (Two (VAt T (JT T.H))) := by
  obtain ⟨_, hc⟩ := vFixed.acc0
  refine two_post (vtwo (T := T) (H := T.H) [17, 21, 23, 25, 26] [] (fun _ => []) (fun a t h => jm_vs h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk1 := hp.k1; have hk2 := hp.k2
  have : vlo s = 0 := rfl; have : veml s = (s.gpr .rdx).toNat - vlo s := rfl
  refine X86_64.WP.mono_syms (acc0_ok v.L R (c := cmask s) (k := (s.gpr .rdx).toNat) (lo := vlo s)
    (by rw [hw 17 (by decide)]; show s.gpr .rdx = _; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (hw 23 (by decide)) (by rw [hw 25 (by decide)]; rfl) (hw 26 (by decide))
    (by omega_arith) hk2 (by omega_arith)) fun u ⟨L', k', R'⟩ sy =>
    ⟨s, S, v.next L' k'.2.2 R' (km_upd hw (by decide) _) trivial sy, k'.2.1.trans hrd, hok⟩

/-- `MGF1`'s anchor: `DB`'s place and length. -/
def mgfA (H : Hash) (a : State) : MA := ⟨fb a, stackArg a 0, a.wr, oEm + vlo a, vdb H.D a, a.syms⟩

/-- A public word of the entry state `a`. -/
theorem pw_w {H : Hash} {a : State} {ks : List Nat} {W : Nat → BitVec 64} (hw : ∀ p ∈ pw H a ks, W p.1 = p.2)
    {k : Nat} (hk : k ∈ ks) : W k = vw H a k :=
  hw (k, vw H a k) (List.mem_map.mpr ⟨k, hk, rfl⟩)

/-- The slots of the table of `MdHash`, in a run. -/
theorem vs_ht {s t : State} {ks : List Nat} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} (hp : Pre T s) (v : VS T.H s t ks rs X) {W : Nat → BitVec 64}
    (hw : ∀ k ∈ ks, W k = vw T.H s k) (h8 : 8 ∈ ks := by decide) (h9 : 9 ∈ ks := by decide)
    (h10 : 10 ∈ ks := by decide) : HT T.H T.dn T.f W t.syms := by
  rw [v.sy]; exact hp.tabs.hf.ht ((hw 8 h8).trans hp.tabs.h0) ((hw 9 h9).trans hp.tabs.h3) ((hw 10 h10).trans hp.tabs.h4)

/-- The slots of the table of `MdHash`, in a run. -/
theorem vs_gt {s t : State} {ks : List Nat} {rs : List (Reg × BitVec 64)}
    {X : (Nat → Byte) → (Nat → BitVec 64) → Prop} (hp : Pre T s) (v : VS T.H s t ks rs X) {W : Nat → BitVec 64}
    (hw : ∀ k ∈ ks, W k = vw T.H s k) (h11 : 11 ∈ ks := by decide) (h12 : 12 ∈ ks := by decide)
    (h13 : 13 ∈ ks := by decide) (h14 : 14 ∈ ks := by decide) : GT T.G T.g W t.syms := by
  rw [v.sy]
  exact hp.tabs.gf.gt ((hw 11 h11).trans hp.tabs.g0) ((hw 12 h12).trans hp.tabs.g1) ((hw 13 h13).trans hp.tabs.g2)
    ((hw 14 h14).trans hp.tabs.g4)

theorem jt_me {a t : State} (h : VAt T (JT T.H) a t) : ME T.G T.g 1 T.H (mgfA T.H a) t := by
  obtain ⟨s, S, v, -, hok⟩ := h
  have hp := S.pa
  have hk1 := hp.k1; have hk2 := hp.k2
  have tb := hp.tabs
  have : vlo a = 0 := rfl; have : veml a = (a.gpr .rdx).toNat - vlo a := rfl
  rw [S.veml] at hok
  obtain ⟨L, w, ⟨V, W, R, hw, -⟩, rg⟩ := vs_pub S v
  refine ⟨⟨S.rest, ⟨by simp only [mgfA]; omega_arith, by simp only [mgfA, vdb]; omega_arith, ?_⟩⟩,
    ⟨L, w, ⟨V, W, R, fun p hp => ?_, trivial⟩, rg⟩, S.syG.tr v.sy⟩
  · simp only [mgfA, vdb, veml] at hok ⊢; omega_arith
  · simp only [mgfA, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact pw_w hw (k := 21) (by decide)
    · exact pw_w hw (k := 23) (by decide)
    · exact pw_w hw (k := 24) (by decide)
    · exact (pw_w hw (k := 14) (by decide)).trans tb.g4
    · exact (pw_w hw (k := 11) (by decide)).trans tb.g0
    · exact (pw_w hw (k := 12) (by decide)).trans tb.g1
    · exact (pw_w hw (k := 13) (by decide)).trans tb.g2

variable (hH : HashOK T.H) (K : Callees T.H) (hG : Pbkdf2.Md.X86_64.Calls.StreamOK T.G) {Gs : Spec.Mgf1.Hash}
  (hGh : ∀ x, Gs.hash x = hG.SH.H.hash x) (hGl : Gs.len = T.G.D) (hGv : Proof.Mgf1.Valid Gs)

include hG hGh hGl hGv in
theorem mgf_ct (hc : HashChecks T.H.P T.H.D 1) :
    RelCT isa (Two (VAt T (JT T.H))) (mgfXor T.H T.g) (Two (VAt T (JT T.H))) := by
  refine two_post (two_map (mgfA T.H) (fun a t h => jt_me h)
    (mgfXor_ct hG hGh hGl hGv hc (fixedChecks (.inl rfl)))) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk1 := hp.k1; have hk2 := hp.k2
  have : vlo s = 0 := rfl; have : veml s = (s.gpr .rdx).toNat - vlo s := rfl
  refine X86_64.WP.mono_syms (mgfXor_ok hG hGh hGl hGv T.H v.L R (vs_gt hp v hw) (e := oEm + vlo s)
    (db := vdb T.H.D s)
    ⟨by omega_arith, by unfold vdb; omega_arith, by unfold vdb veml at *; unfold oEm; omega_arith⟩ (hw 23 (by decide))
    (hw 24 (by decide))) fun u ⟨L', rd', wr', _, V', W', R', hW', _⟩ sy =>
    ⟨s, S, ⟨L', wr'.trans v.wr, ⟨V', W', R', fun k hk => (hW' k (km_lt hk) (by
      simp only [KM, List.mem_cons, List.not_mem_nil, or_false] at hk; omega_arith)).trans (hw k hk), trivial⟩,
      (fun _ hp => by cases hp), sy.trans v.sy⟩, rd'.trans hrd, hok⟩

theorem clearTop_ct : RelCT isa (Two (VAt T (JT T.H))) (.block clearTop) (Two (VAt T (JT T.H))) := by
  obtain ⟨_, hc⟩ := vFixed.clearTop
  refine two_post (vtwo (T := T) (H := T.H) [23] [] (fun _ => []) (fun a t h => jm_vs h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have : vlo s = 0 := rfl; have : veml s = (s.gpr .rdx).toNat - vlo s := rfl
  exact X86_64.WP.mono_syms (clearTop_ok v.L R (e := oEm + vlo s) (c := cmask s) (hw 23 (by decide))
    (by rw [hw 25 (by decide)]; rfl) (by unfold oEm oRsa; omega_arith))
    fun u ⟨L', k', R'⟩ sy => ⟨s, S, v.next L' k'.2.2 R' hw trivial sy, k'.2.1.trans hrd, hok⟩

/-- After the scan: its registers. -/
def JC6 (H : Hash) (s t : State) : Prop :=
  JT H s t ∧ ∃ (fd : Bool) (pos : Nat) (val : Byte), pos < vdb H.D s ∧
    t.gpr .rdx = (if fd then BitVec.allOnes 64 else 0) ∧ t.gpr .rsi = BitVec.ofNat 64 pos ∧
    t.gpr .r11 = BitVec.setWidth 64 val

theorem posScan_ct : RelCT isa (Two (VAt T (JT T.H))) posScan (Two (VAt T (JC6 T.H))) := by
  obtain ⟨_, hc⟩ := vFixed.posScan
  refine two_post (vtwo (T := T) (H := T.H) [23, 24] [] (fun _ => []) (fun a t h => jm_vs h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk2 := hp.k2
  have : vlo s = 0 := rfl; have : veml s = (s.gpr .rdx).toNat - vlo s := rfl
  have hdb1 : 1 ≤ vdb T.H.D s := by unfold vdb; omega_arith
  exact X86_64.WP.mono_syms (posScan_ok v.L R (e := oEm + vlo s) (db := vdb T.H.D s) (hw 23 (by decide)) (hw 24 (by decide))
    hdb1 (by unfold vdb veml oEm oRsa; omega_arith)) fun u ⟨k', hm', hdx, hsi, h11⟩ sy =>
    ⟨s, S, ⟨v.keep k' hm' (by decide) (fun _ hp => by cases hp) sy, k'.2.1.trans hrd, hok⟩, _, _, _,
      fnz_getD_lt hdb1, hdx, hsi, h11⟩

/-- The length of `M'`, from the salt's position, which is secret. -/
def X7 (H : Hash) (s : State) (_ : Nat → Byte) (W : Nat → BitVec 64) : Prop :=
  ∃ pos, pos < vdb H.D s ∧ W 27 = BitVec.ofNat 64 (vdb H.D s - pos - 1 + (8 + H.D)) ∧
    W 34 = BitVec.ofNat 64 pos

include hH in
theorem posCheck_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JC6 T.H))) (posCheck T.H) (Two (VAt T (JM T.H (X7 T.H)))) := by
  obtain ⟨_, hc⟩ := hc.posCheck
  refine two_post (vtwo (T := T) (H := T.H) [24, 35, 36] [] (fun _ => []) (fun a t h => jm_vs (let ⟨s, S, h⟩ := h;
    ⟨s, S, h.1⟩) _) (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, ⟨v, hrd, hok⟩, fd, pos, val, hpos, hdx, hsi, h11⟩ => ?_
  obtain ⟨V, W, R, hw, -⟩ := v.W
  exact X86_64.WP.mono_syms (posCheck_ok hH v.L R (db := vdb T.H.D s) (pos := pos) (fd := fd) (val := val)
    (fixed := decide ((s.gpr .r9).setWidth 32 = 0)) (hw 24 (by decide))
    (by rw [hw 35 (by decide)]; simp only [vw, decide_eq_true_eq]) hpos hdx hsi h11) fun u ⟨L', k', R'⟩ sy =>
    ⟨s, S, v.next L' k'.2.2 R' (km_upd (km_upd (km_upd hw (by decide) _) (by decide) _) (by decide) _)
      ⟨pos, hpos, by simp [upd], by simp [upd]⟩ sy, k'.2.1.trans hrd, hok⟩

/-- Testing the public salt mode before the scan. -/
theorem scanAny_ct : RelCT isa (Two (VAt T (JT T.H)))
    (.block [.mov .rax (.mem (sp sAny)), .alu .test .rax (.reg .rax)])
    (Two fun a t => VAt T (JT T.H) a t ∧
      isa.eval .e t = some (decide (vw T.H a 35 = 0))) := by
  obtain ⟨_, hc⟩ := vFixed.scanAny
  refine two_post (vtwo (T := T) (H := T.H) [35] [] (fun _ => [])
    (fun a t h => jm_vs h _) (fun _ => rfl) (by decide) hc)
    fun a t ⟨s, S, v, hrd, hok⟩ => ?_
  obtain ⟨V, W, R, hw, _⟩ := v.W
  refine X86_64.WP.mono_syms (WP.keep [.rax] (Q := fun u => u.mem = t.mem ∧
    u.zf = some (decide (W 35 = 0))) ?_ rfl) fun u ⟨⟨hm, hz⟩, ku⟩ sy => ?_
  · xrun [ea_sp, v.L.rsp, v.L.ld (d := sAny) (by decide), R.rd (d := sAny) 35 rfl (by decide)]
    rw [BitVec.and_self]
    rfl
  · refine ⟨⟨s, S, v.keep ku hm (by decide) (fun _ hp => by cases hp) sy, ku.2.1.trans hrd, hok⟩, ?_⟩
    change u.zf = _
    rw [hz, hw 35 (by decide), S.vw]

/-- And the bound on the requested length. -/
theorem scanLen_ct : RelCT isa (Two (VAt T (JT T.H)))
    (.block [.mov .rax (.mem (sp sSlen)), .alu .cmp .rax (.mem (sp sDb))])
    (Two fun a t => VAt T (JT T.H) a t ∧
      isa.eval .b t = some (decide ((a.gpr .r8).toNat < vdb T.H.D a))) := by
  obtain ⟨_, hc⟩ := vFixed.scanLen
  refine two_post (vtwo (T := T) (H := T.H) [24, 36] [] (fun _ => [])
    (fun a t h => jm_vs h _) (fun _ => rfl) (by decide) hc)
    fun a t ⟨s, S, v, hrd, hok⟩ => ?_
  obtain ⟨V, W, R, hw, _⟩ := v.W
  have hk2 := S.ps.k2
  refine X86_64.WP.mono_syms (WP.keep [.rax] (Q := fun u => u.mem = t.mem ∧
    u.cf = some (decide ((s.gpr .r8).toNat < vdb T.H.D s))) ?_ rfl) fun u ⟨⟨hm, hz⟩, ku⟩ sy => ?_
  · xrun [ea_sp, v.L.rsp, v.L.ld (d := sSlen) (by decide), v.L.ld (d := sDb) (by decide),
      R.rd (d := sSlen) 36 rfl (by decide), R.rd (d := sDb) 24 rfl (by decide),
      hw 36 (by decide), hw 24 (by decide)]
    simp only [vw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show vdb T.H.D s < 2 ^ 64 by unfold vdb veml; omega_arith)]
  · refine ⟨⟨s, S, v.keep ku hm (by decide) (fun _ hp => by cases hp) sy, ku.2.1.trans hrd, hok⟩, ?_⟩
    change u.cf = _
    rw [hz, S.rsl, S.vdb]

/-- After the call, with the salt's length given and less than `DB`'s. -/
def JTF (H : Hash) (s t : State) : Prop := JT H s t ∧ (s.gpr .r8).toNat < vdb H.D s

include hH in
theorem prefixCheck_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JTF T.H))) (prefixCheck T.H) (Two (VAt T (JM T.H (X7 T.H)))) := by
  obtain ⟨_, hc⟩ := hc.prefixCheck
  refine two_post (vtwo (T := T) (H := T.H) [23, 24, 36] [] (fun _ => []) (fun a t h => jm_vs (let ⟨s, S, h⟩ := h;
    ⟨s, S, h.1⟩) _) (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, ⟨v, hrd, hok⟩, hlt⟩ => ?_
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hp := S.ps
  have hk2 := hp.k2
  have : vlo s = 0 := rfl; have : veml s = (s.gpr .rdx).toNat - vlo s := rfl
  refine X86_64.WP.mono_syms (prefixCheck_ok hH v.L R (e := oEm + vlo s) (db := vdb T.H.D s) (sl := (s.gpr .r8).toNat)
    (hw 23 (by decide)) (hw 24 (by decide)) (by rw [hw 36 (by decide)]; simp [vw]) hlt
    (by unfold vdb veml oEm oRsa; omega_arith) (by unfold vdb veml; omega_arith)) fun u ⟨L', k', a', _, R'⟩ sy =>
    ⟨s, S, v.next L' k'.2.2 R' (km_upd (km_upd (km_upd hw (by decide) _) (by decide) _) (by decide) _)
      ⟨vdb T.H.D s - (s.gpr .r8).toNat - 1, by omega_arith, ?_, by simp [upd]⟩ sy, k'.2.1.trans hrd, hok⟩
  simp only [upd, Nat.reduceEqDiff, ite_true]
  congr 1
  omega_arith

include hH in
theorem scanCheck_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JT T.H))) (scanCheck T.H) (Two (VAt T (JM T.H (X7 T.H)))) := by
  have generic := (posScan_ct (T := T)).seq (posCheck_ct hH hc)
  unfold scanCheck
  refine scanAny_ct.seq (two_ite (fun a t₁ t₂ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_
    (generic.mono (fun _ _ => two_mono fun _ _ h => h.1.1) fun _ _ h => h))
  refine (scanLen_ct.seq (two_ite (fun a t₁ t₂ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_
    (generic.mono (fun _ _ => two_mono fun _ _ h => h.1.1) fun _ _ h => h))).mono
    (fun _ _ => two_mono fun _ _ h => h.1.1) (fun _ _ h => h)
  refine (prefixCheck_ct hH hc).mono (fun _ _ => two_mono fun a t ⟨⟨⟨s, S, h⟩, hz⟩, hb⟩ => ?_) fun _ _ h => h
  have hf : (a.gpr .r8).toNat < vdb T.H.D a := by
    rw [hz, Option.some.injEq, decide_eq_true_eq] at hb
    exact hb
  exact ⟨s, S, h, by rwa [S.rsl, S.vdb]⟩

end VG.Proof.RsaPss.X86_64.Chk

end

end


/-!
# RSASSA-PSS verification on x86-64: `M'` and its hash in two runs

`mHash`, `DB` and the shift by the salt's position into `Y`, the hash of
`M'` over the blocks the longest salt needs (`vnb`), and the comparison:
each constant time from the public words of both runs. The shift's ten
passes and the hash's blocks do not depend on the salt's position.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Chk

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

variable {T : Tabs}

/-- After `mHash`: `rcx` is `Y`. -/
def JC8 (H : Hash) (s t : State) : Prop := JM H (X7 H) s t ∧ t.gpr .rcx = off (stackArg s 0) oY

/-- Before pass `j` of the shift. -/
def JS (H : Hash) (j : Nat) (s t : State) : Prop :=
  VS H s t KM [] (fun V W => X7 H s V W ∧ W 46 = BitVec.ofNat 64 (2 ^ j) ∧ W 44 = BitVec.ofNat 64 (10 - j) ∧
    ∃ x, W 45 = BitVec.ofNat 64 x ∧ x < 2 ^ 64) ∧ t.rd = s.rd ∧ H.D + 2 ≤ veml s

/-- After `nbm`. -/
def JN (H : Hash) (s t : State) : Prop := VS H s t (KM ++ [28]) [] (X7 H s) ∧ t.rd = s.rd ∧ H.D + 2 ≤ veml s

/-- At the end. -/
def JR (H : Hash) (s t : State) : Prop := VS H s t [] [] fun _ _ => True

variable (hH : HashOK T.H) (K : Callees T.H) (hdk : DigOK T.H)

include hH in
theorem cyd_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JM T.H (X7 T.H)))) (.seq clearY (copyDigest T.H)) (Two (VAt T (JC8 T.H))) := by
  obtain ⟨_, hc⟩ := hc.copyDigest
  refine two_post (vtwo (T := T) (H := T.H) [21, 37] [] (fun _ => []) (fun a t h => jm_vs h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, hx⟩ := v.W
  have hp := S.ps
  have wDg := hp.wDg
  have hDN := hH.hDN
  have hN := hH.N_le
  refine WP.seq (X86_64.WP.mono_syms (clearY_ok v.L R) fun u1 ⟨L1, k1, hcx1, R1⟩ sy1 => ?_)
  refine X86_64.WP.mono_syms (copyDigest_ok hH L1 R1 (p := s.gpr .rdi) (hw 37 (by decide)) hcx1
    (fun i hi => by
      rw [k1.2.1, hrd]
      exact ⟨⟨s.gpr .rdi, T.H.D⟩, List.mem_append_left _ (by rw [hp.hrd]; simp),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    (fun i hi j hj => Outside.ne L1 (by
      have := hp.outside hp.ddgs hp.dKdg (a := s.gpr .rdi + BitVec.ofNat 64 i)
        (Offset.contains_base _ (by omega_arith) (by omega_arith))
      rwa [k1.2.2, v.wr]) (by unfold oY oRsa; omega_arith))) fun u2 ⟨L2, k2, R2⟩ sy2 =>
    ⟨s, S, ⟨v.next L2 (k2.2.2.trans k1.2.2) R2 hw hx (sy2.trans sy1), k2.2.1.trans (k1.2.1.trans hrd), hok⟩,
      (k2.gpr (by decide)).trans hcx1⟩

include hH in
theorem copyDb_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JC8 T.H))) (copyDb T.H) (Two (VAt T (JM T.H (X7 T.H)))) := by
  obtain ⟨_, hc⟩ := hc.copyDb
  refine two_post (vtwo (T := T) (H := T.H) [23, 24] [.rcx] (fun a => [(.rcx, off (stackArg a 0) oY)])
    (fun a t ⟨s, S, ⟨v, _⟩, hcx⟩ => ⟨s, _, S, v.sub (by decide) _ (fun p hp => by
      rw [List.mem_singleton.mp hp, ← S.arg0]; exact hcx) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, ⟨v, hrd, hok⟩, hcx⟩ => ?_
  obtain ⟨V, W, R, hw, hx⟩ := v.W
  have hp := S.ps
  have hk2 := hp.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  have : vlo s = 0 := rfl; have : veml s = (s.gpr .rdx).toNat - vlo s := rfl
  exact X86_64.WP.mono_syms (copyDb_ok v.L R (e := oEm + vlo s) (db := vdb T.H.D s) (hw 23 (by decide)) (hw 24 (by decide)) hcx
    (by unfold vdb; omega_arith) (by unfold vdb veml oEm oY; omega_arith) (by unfold vdb veml; omega_arith)) fun u ⟨L', k', R'⟩ sy =>
    ⟨s, S, v.next L' k'.2.2 R' hw hx sy, k'.2.1.trans hrd, hok⟩

/-- `shift`'s first slots. -/
theorem shiftPro_ok {u : State} {F S : Addr} (L : Lay u F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep u.mem F S V W) {pos : Nat} (hpos : W 34 = BitVec.ofNat 64 pos) :
    WP isa (.block shiftPro) u fun v => Lay v F S ∧ Keep [.rax] u v ∧
      Rep v.mem F S V (upd (upd (upd W 45 (BitVec.ofNat 64 (pos + 1))) 46 (BitVec.ofNat 64 1)) 44
        (BitVec.ofNat 64 10)) := by
  have G' := L.geo
  have R1 := R.wf G' (k := 45) (by decide) (BitVec.ofNat 64 (pos + 1))
  rw [show off F (8 * 45) = off F sA from rfl] at R1
  have R2 := R1.wf G' (k := 46) (by decide) (BitVec.ofNat 64 1)
  rw [show off F (8 * 46) = off F sD from rfl] at R2
  have R3 := R2.wf G' (k := 44) (by decide) (BitVec.ofNat 64 10)
  rw [show off F (8 * 44) = off F sJ from rfl] at R3
  refine WP.mono (WP.keep [.rax] (Q := fun v => v.mem = ((u.mem.writeW (off F sA) (BitVec.ofNat 64 (pos + 1))).writeW
      (off F sD) (BitVec.ofNat 64 1)).writeW (off F sJ) (BitVec.ofNat 64 10)) ?_ rfl) fun v ⟨hm, hk⟩ =>
    ⟨L.of_rep' R (hm ▸ R3) (by simp [upd]) (hk.gpr (by decide)) hk.2.2, hk, hm ▸ R3⟩
  xrun [shiftPro, ea_sp, L.rsp, L.ld (d := sPos) (by decide), R.rd (d := sPos) 34 rfl (by decide), hpos,
    L.st (d := sA) (by decide), L.st (d := sD) (by decide), L.st (d := sJ) (by decide), ofNat_add_lit]
  rfl

theorem shiftPro_ct : RelCT isa (Two (VAt T (JM T.H (X7 T.H)))) (.block shiftPro) (Two (VAt T (JS T.H 0))) := by
  obtain ⟨_, hc⟩ := vFixed.shiftPro
  refine two_post (vtwo (T := T) (H := T.H) [] [] (fun _ => []) (fun a t h => jm_vs h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, pos, hpos, h27, h34⟩ := v.W
  have hk2 := S.ps.k2
  have : vlo s = 0 := rfl; have : veml s = (s.gpr .rdx).toNat - vlo s := rfl
  have hp1 : pos + 1 < 2 ^ 64 := by unfold vdb veml at hpos; omega_arith
  exact X86_64.WP.mono_syms (shiftPro_ok v.L R h34) fun u ⟨L', k', R'⟩ sy =>
    ⟨s, S, v.next L' k'.2.2 R' (km_upd (km_upd (km_upd hw (by decide) _) (by decide) _) (by decide) _)
      ⟨⟨pos, hpos, by simp [upd, h27], by simp [upd, h34]⟩, by simp [upd], by simp [upd], pos + 1, by simp [upd], hp1⟩
      sy, k'.2.1.trans hrd, hok⟩

include hH in
theorem pass_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two fun (p : State × Nat) t => p.2 < 10 ∧ VAt T (JS T.H p.2) p.1 t)
      (.seq (shiftPass T.H) (.block nextPass)) fun _ _ => True := by
  obtain ⟨_, hs⟩ := hc.shiftPass
  obtain ⟨_, hn⟩ := vFixed.nextPass
  refine RelCT.seq (two_post (Ψ := fun p t => VAt T (JS T.H p.2) p.1 t)
    (vtwoX (T := T) (H := T.H) Prod.fst [21, 24] (fun p => [(46, BitVec.ofNat 64 (2 ^ p.2))]) [46] [] (fun _ => [])
      (fun p t ⟨_, s, S, v, _⟩ => ⟨s, S, v.sub (by decide) [] (fun _ hp => by cases hp)
        fun _ _ ⟨_, h46, _⟩ q hq => by rw [List.mem_singleton.mp hq]; exact h46⟩)
      (fun _ => rfl) (fun _ => rfl) (by decide) hs) fun p t ⟨_, s, S, ⟨v, hrd, hok⟩⟩ => ?_)
    (vtwoX (T := T) (H := T.H) Prod.fst [] (fun _ => []) [] [] (fun _ => [])
      (fun p t ⟨s, S, v, _⟩ => ⟨s, S, v.sub (by decide) [] (fun _ hp => by cases hp) fun _ _ _ q hq => by cases hq⟩)
      (fun _ => rfl) (fun _ => rfl) (by decide) hn)
  obtain ⟨V, W, R, hw, hx, h46, h44, x, h45, hxl⟩ := v.W
  have hk2 := S.ps.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  have : vlo s = 0 := rfl; have : veml s = (s.gpr .rdx).toNat - vlo s := rfl
  have hpp : 2 ^ p.2 ≤ 512 := by
    calc 2 ^ p.2 ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega_arith)
      _ = 512 := rfl
  exact X86_64.WP.mono_syms (shiftPass_ok hH v.L R h45 h46 (hw 24 (by decide)) hxl Nat.one_le_two_pow
    (by unfold vdb; omega_arith) (by unfold vdb veml oY oRsa; omega_arith)) fun u ⟨L', k', R'⟩ sy =>
    ⟨s, S, v.next L' k'.2.2 R' hw ⟨hx, h46, h44, x, h45, hxl⟩ sy, k'.2.1.trans hrd, hok⟩

include hH in
theorem pass_wp {a : State} {j : Nat} {t : State} (hj : j < 10) (h : VAt T (JS T.H j) a t) :
    WP isa (.seq (shiftPass T.H) (.block nextPass)) t fun t' =>
      isa.eval .ne t' = some (decide (j + 1 < 10)) ∧ (j + 1 < 10 → VAt T (JS T.H (j + 1)) a t') ∧
      (j + 1 = 10 → VAt T (JM T.H (X7 T.H)) a t') := by
  obtain ⟨s, S, v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, hx, h46, h44, x, h45, hxl⟩ := v.W
  have hk2 := S.ps.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  have : vlo s = 0 := rfl; have : veml s = (s.gpr .rdx).toNat - vlo s := rfl
  have hpp : 2 ^ j ≤ 512 := by
    calc 2 ^ j ≤ 2 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega_arith)
      _ = 512 := rfl
  refine WP.seq (X86_64.WP.mono_syms (shiftPass_ok hH v.L R h45 h46 (hw 24 (by decide)) hxl Nat.one_le_two_pow
    (by unfold vdb; omega_arith) (by unfold vdb veml oY oRsa; omega_arith)) fun u ⟨Lu, ku, Ru⟩ syu => ?_)
  refine X86_64.WP.mono_syms (nextPass_ok Lu Ru h45 h46 h44 hxl (by omega_arith) (by omega_arith))
    fun y ⟨Ly, ky, Ry, hzy⟩ syy => ?_
  obtain ⟨pos, hpos, h27, h34⟩ := hx
  have hw' := km_upd (j := 44) (km_upd (j := 46) (km_upd (j := 45) hw (by decide) (BitVec.ofNat 64 (x / 2)))
    (by decide) (BitVec.ofNat 64 (2 * 2 ^ j))) (by decide) (BitVec.ofNat 64 (10 - j - 1))
  have hX : X7 T.H s (shV V (decide (x % 2 = 1)) (2 ^ j) (oY + 8 + T.H.D) (vdb T.H.D s))
      (upd (upd (upd W 45 (BitVec.ofNat 64 (x / 2))) 46 (BitVec.ofNat 64 (2 * 2 ^ j))) 44
        (BitVec.ofNat 64 (10 - j - 1))) := ⟨pos, hpos, by simp [upd, h27], by simp [upd, h34]⟩
  have hwr : y.wr = t.wr := ky.2.2.trans ku.2.2
  have hrd' : y.rd = s.rd := ky.2.1.trans (ku.2.1.trans hrd)
  refine ⟨eval_ne_cnt hj (by rw [hzy]; simp only [Option.some.injEq, decide_eq_decide]; omega_arith), fun _ =>
    ⟨s, S, v.next Ly hwr Ry hw' ⟨hX, by simp [upd, Nat.pow_succ, Nat.mul_comm], by simp only [upd, Nat.reduceEqDiff, ite_true, ite_false]; congr 1,
      x / 2, by simp [upd], by have := Nat.div_le_self x 2; omega_arith⟩ (syy.trans syu), hrd', hok⟩, fun _ =>
    ⟨s, S, v.next Ly hwr Ry hw' hX (syy.trans syu), hrd', hok⟩⟩

include hH in
theorem shift_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JM T.H (X7 T.H)))) (shift T.H) (Two (VAt T (JM T.H (X7 T.H)))) := by
  rw [shift_eq]
  exact RelCT.seq shiftPro_ct ((two_loop (Φ := fun a j t => VAt T (JS T.H j) a t) (fun _ => 10) (pass_ct hH hc)
    fun a j t hj h => pass_wp hH hj h).mono (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a, ⟨by decide, h₁⟩, by decide, h₂⟩)
    fun _ _ h => h)

include hH in
theorem verifyNb_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JM T.H (X7 T.H)))) (.block (verifyNb T.H)) (Two (VAt T (JN T.H))) := by
  obtain ⟨_, hc⟩ := hc.verifyNb
  refine two_post (vtwo (T := T) (H := T.H) [24] [] (fun _ => []) (fun a t h => jm_vs h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, hx⟩ := v.W
  have hk2 := S.ps.k2
  exact X86_64.WP.mono_syms (verifyNb_ok hH v.L R (db := vdb T.H.D s) (hw 24 (by decide))
    (by unfold vdb veml; omega_arith)) fun u ⟨L', k', R'⟩ sy => ⟨s, S, v.next L' k'.2.2 R' (fun k hk => by
      rcases List.mem_append.mp hk with hk | hk
      · exact km_upd hw (by decide) _ k hk
      · rw [List.mem_singleton.mp hk]; simp [upd, vw, vnb])
      (by obtain ⟨pos, hpos, h27, h34⟩ := hx; exact ⟨pos, hpos, by simp [upd, h27], by simp [upd, h34]⟩) sy,
      k'.2.1.trans hrd, hok⟩

/-- The hash's anchor: the blocks of `M'`. -/
def hashA (H : Hash) (a : State) : HA := ⟨fb a, stackArg a 0, a.wr, vnb H a, a.syms⟩

include hH in
theorem jn_he {a t : State} (h : VAt T (JN T.H) a t) : HE T.H T.dn T.f 1 (hashA T.H a) t := by
  obtain ⟨s, S, v, -, hok⟩ := h
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hk2 := S.pa.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  have hL := hH.dims.L
  have h1 := Nat.lt_div_mul_add (a := vdb T.H.D a + (7 + T.H.D + T.H.P.L)) (b := T.H.P.B) hB0
  have h2 := Nat.div_mul_le_self (vdb T.H.D a + (7 + T.H.D + T.H.P.L)) T.H.P.B
  have hdb : vdb T.H.D a ≤ 1024 := by unfold vdb veml; omega_arith
  have tb := S.pa.tabs
  refine ⟨⟨S.rest, Nat.succ_pos _, by simp only [hashA, vnb]; rw [Nat.succ_mul]; omega_arith⟩,
    (vs_pub S v).sub (fun p hp => ?_) (fun _ h => h) (fun _ _ ⟨pos, hpos, h27, _⟩ =>
      ⟨vdb T.H.D s - pos - 1 + (8 + T.H.D), h27, ?_⟩), S.syH.tr v.sy⟩
  · simp only [hws, hashA, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact List.mem_map.mpr ⟨21, by decide, rfl⟩
    · exact List.mem_map.mpr ⟨28, by decide, rfl⟩
    · rw [← tb.h0]; exact List.mem_map.mpr ⟨8, by decide, rfl⟩
    · rw [← tb.h3]; exact List.mem_map.mpr ⟨9, by decide, rfl⟩
    · rw [← tb.h4]; exact List.mem_map.mpr ⟨10, by decide, rfl⟩
  · simp only [hashA, vnb]; rw [S.vdb] at hpos ⊢; rw [Nat.succ_mul]; omega_arith

include hH K hdk in
theorem mhash_ct (hc : HashChecks T.H.P T.H.D 1) :
    RelCT isa (Two (VAt T (JN T.H))) (ctHash T.f T.H) (Two (VAt T (JT T.H))) := by
  refine two_post (two_map (hashA T.H) (fun a t h => jn_he hH h)
    (ctHash_ct hH K hdk 1 hc (fixedChecks (.inl rfl))))
    fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, hrd, hok⟩ := h
  obtain ⟨V, W, R, hw, pos, hpos, h27, _⟩ := v.W
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hk2 := S.ps.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  have hL := hH.dims.L
  have h1 := Nat.lt_div_mul_add (a := vdb T.H.D s + (7 + T.H.D + T.H.P.L)) (b := T.H.P.B) hB0
  have h2 := Nat.div_mul_le_self (vdb T.H.D s + (7 + T.H.D + T.H.P.L)) T.H.P.B
  have hdb : vdb T.H.D s ≤ 1024 := by unfold vdb veml; omega_arith
  exact X86_64.WP.mono_syms (ctHash_gen hH K v.L R h27 (hw 28 (by simp))
    (by unfold vnb; rw [Nat.succ_mul]; omega_arith) (by unfold vnb; rw [Nat.succ_mul]; omega_arith)
    (vs_ht S.ps v hw) hdk) fun u ⟨L', rd', wr', _, V', W', R', _, hW', _⟩ sy =>
    ⟨s, S, ⟨L', wr'.trans v.wr, ⟨V', W', R', fun k hk => (hW' k (km_lt hk) (km_ne hk (by decide))
      (km_ne hk (by decide))).trans (hw k (List.mem_append_left _ hk)), trivial⟩, (fun _ hp => by cases hp),
      sy.trans v.sy⟩, rd'.trans hrd, hok⟩

include hH in
theorem cmpH_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JT T.H))) (cmpH T.H) (Two (VAt T (JR T.H))) := by
  obtain ⟨_, hc⟩ := hc.cmpH
  refine two_post (vtwo (T := T) (H := T.H) [21, 23, 24] [] (fun _ => []) (fun a t h => jm_vs h _)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, h⟩ => ?_
  obtain ⟨v, -, hok⟩ := h
  obtain ⟨V, W, R, hw, -⟩ := v.W
  have hk2 := S.ps.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  have : vlo s = 0 := rfl; have : veml s = (s.gpr .rdx).toNat - vlo s := rfl
  exact X86_64.WP.mono_syms (cmpH_ok hH v.L R (e := oEm + vlo s) (db := vdb T.H.D s) (hw 23 (by decide)) (hw 24 (by decide))
    (by unfold vdb veml oEm oRsa; omega_arith)) fun u ⟨k', hm', _⟩ sy =>
    ⟨s, S, (v.keep k' hm' (by decide) (fun _ hp => by cases hp) sy).sub (fun _ hk => by cases hk) []
      (fun _ hp => by cases hp) fun _ _ _ => trivial⟩

end VG.Proof.RsaPss.X86_64.Chk

end

end

/-! The fixed-salt tail leaks only the requested, public salt length. -/

@[expose] public section

namespace VG.Proof.RsaPss.X86_64.Chk
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Impl.RsaPss.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep ifp ifn)
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK Callees MgfLink)

variable {T : Tabs}

def fixedNb (H : Hash) (s : State) : Nat :=
  (8 + H.D + (s.gpr .r8).toNat + H.P.L) / H.P.B + 1

def JFixed (H : Hash) (s t : State) : Prop :=
  JM H (X7 H) s t ∧ (s.gpr .r8).toNat < vdb H.D s

def JFixedN (H : Hash) (s t : State) : Prop :=
  VS H s t KM [] (fun _ W => W 27 = BitVec.ofNat 64 (8 + H.D + (s.gpr .r8).toNat) ∧
    W 28 = BitVec.ofNat 64 (fixedNb H s)) ∧ t.rd = s.rd ∧
    H.D + 2 ≤ veml s ∧ (s.gpr .r8).toNat < vdb H.D s

variable (hH : HashOK T.H) (K : Callees T.H) (hdk : DigOK T.H)

/-- After `fixedHead`: `rcx` = `Y`. -/
def JFixedC (H : Hash) (s t : State) : Prop :=
  JFixedN H s t ∧ t.gpr .rcx = off (stackArg s 0) oY

include hH in
theorem fixedHead_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JFixed T.H))) (fixedHead T.H)
      (Two (VAt T (JFixedC T.H))) := by
  obtain ⟨_, hc⟩ := hc.fixedHead
  refine two_post (vtwo (T := T) (H := T.H) [21, 36, 37] [] (fun _ => [])
    (fun a t ⟨s, S, h, _⟩ => jm_vs ⟨s, S, h⟩ _) (fun _ => rfl) (by decide) hc)
    fun a t ⟨s, S, ⟨v, hrd, hok⟩, hfit⟩ => ?_
  obtain ⟨V, W, R, hw, hx⟩ := v.W
  have hp := S.ps
  have wDg := hp.wDg
  have hDN := hH.hDN
  have hN := hH.N_le
  have hk2 := S.ps.k2
  have hB0 := hH.B_pos
  have hL := hH.dims.L
  have hBl := hH.B_le
  have h1 := Nat.lt_div_mul_add (a := 8 + T.H.D + (s.gpr .r8).toNat + T.H.P.L) (b := T.H.P.B) hB0
  have h2 := Nat.div_mul_le_self (8 + T.H.D + (s.gpr .r8).toNat + T.H.P.L) T.H.P.B
  have hnb : fixedNb T.H s * T.H.P.B ≤ 2048 := by
    unfold fixedNb; rw [Nat.succ_mul]; unfold vdb veml at hfit; omega_arith
  unfold fixedHead seqs seqs
  refine WP.seq (X86_64.WP.mono_syms (hashSaltLen_ok hH v.L R (k := 36) (by decide)
    (show W 36 = BitVec.ofNat 64 (s.gpr .r8).toNat by rw [hw 36 (by decide)]; simp [vw])
    (by unfold vdb veml at hfit; omega_arith)) fun u0 ⟨L0, k0, R0⟩ sy0 => ?_)
  refine WP.seq (X86_64.WP.mono_syms (clearNb_ok hH L0 R0 (nbm := fixedNb T.H s) (by simp [upd, fixedNb])
    (Nat.succ_pos _) hnb) fun u1 ⟨L1, k1, hcx1, R1⟩ sy1 => ?_)
  refine X86_64.WP.mono_syms (copyDigest_ok hH L1 R1 (p := s.gpr .rdi) (by simp [upd]; exact hw 37 (by decide)) hcx1
    (fun i hi => by
      rw [k1.2.1, k0.2.1, hrd]
      exact ⟨⟨s.gpr .rdi, T.H.D⟩, List.mem_append_left _ (by rw [hp.hrd]; simp),
        Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    (fun i hi j hj => Outside.ne L1 (by
      have := hp.outside hp.ddgs hp.dKdg (a := s.gpr .rdi + BitVec.ofNat 64 i)
        (Offset.contains_base _ (by omega_arith) (by omega_arith))
      rwa [k1.2.2, k0.2.2, v.wr]) (by unfold oY oRsa; omega_arith))) fun u2 ⟨L2, k2, R2⟩ sy2 => ?_
  exact ⟨s, S, ⟨v.next L2 (k2.2.2.trans (k1.2.2.trans k0.2.2)) R2
    (km_upd (km_upd hw (by decide) _) (by decide) _) ⟨by simp [upd], by simp [upd, fixedNb]⟩
    (sy2.trans (sy1.trans sy0)), k2.2.1.trans (k1.2.1.trans (k0.2.1.trans hrd)), hok, hfit⟩,
    (k2.gpr (by decide)).trans hcx1⟩

include hH in
theorem fixedCopy_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JFixedC T.H))) (copyFixedSalt T.H)
      (Two (VAt T (JFixedN T.H))) := by
  obtain ⟨_, hc⟩ := hc.copyFixedSalt
  refine two_post (vtwo (T := T) (H := T.H) [23, 24, 36] [.rcx]
    (fun a => [(.rcx, off (stackArg a 0) oY)])
    (fun a t ⟨s, S, ⟨v, _⟩, hcx⟩ => ⟨s, _, S, v.sub (by decide) _
      (fun p hp => by rw [List.mem_singleton.mp hp, ← S.arg0]; exact hcx) fun _ _ x => x⟩)
    (fun _ => rfl) (by decide) hc) fun a t ⟨s, S, ⟨v, hrd, hok, hf⟩, hcx⟩ => ?_
  obtain ⟨V, W, R, hw, hx⟩ := v.W
  have hk2 := S.ps.k2
  have hlo := vlo_le s
  have hDN := hH.hDN
  have hN := hH.N_le
  refine X86_64.WP.mono_syms (copyFixedSalt_ok hH v.L R (e := oEm + vlo s) (db := vdb T.H.D s)
    (hw 23 (by decide)) (hw 24 (by decide))
    (show W 36 = BitVec.ofNat 64 (s.gpr .r8).toNat by rw [hw 36 (by decide)]; simp [vw]) hf
    (by unfold vdb veml oEm oY; omega_arith) (by unfold vdb veml at hf; omega_arith) hcx)
    fun u ⟨L, k, R⟩ sy => ?_
  exact ⟨s, S, v.next L k.2.2 R hw hx sy, k.2.1.trans hrd, hok, hf⟩

include hH in
theorem padSalt_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JFixedN T.H))) (.block (padSalt T.H))
      (Two (VAt T (JFixedN T.H))) := by
  obtain ⟨_, hc⟩ := hc.padSalt
  refine two_post (vtwo (T := T) (H := T.H) [21, 36] [] (fun _ => [])
    (fun a t ⟨s, S, v, hrd, hok, _⟩ => jm_vs (X := fun _ _ _ => True) ⟨s, S, v.sub (fun _ h => h) [] (fun _ h => by cases h)
      (fun _ _ _ => trivial), hrd, hok⟩ _) (fun _ => rfl) (by decide) hc)
    fun a t ⟨s, S, v, hrd, hok, hf⟩ => ?_
  obtain ⟨V, W, R, hw, hx⟩ := v.W
  have hk2 := S.ps.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  refine X86_64.WP.mono_syms (padSalt_ok v.L R (sl := (s.gpr .r8).toNat)
    (show W 36 = BitVec.ofNat 64 (s.gpr .r8).toNat by rw [hw 36 (by decide)]; simp [vw])
    (by unfold vdb veml at hf; omega_arith)) fun u ⟨L, k, R⟩ sy => ?_
  exact ⟨s, S, v.next L k.2.2 R hw hx sy, k.2.1.trans hrd, hok, hf⟩

include hH in
theorem fixedSaltPrefix_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JFixed T.H))) (fixedSaltPrefix T.H)
      (Two (VAt T (JFixedN T.H))) := by
  unfold fixedSaltPrefix seqs seqs
  exact (fixedHead_ct hH hc).seq ((fixedCopy_ct hH hc).seq (padSalt_ct hH hc))

/-! ## `fixedHash` -/

include hH in
theorem lenLast_ct (hc : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (HF T.H T.dn T.f 1)) (lenLast T.H) (Two (HF T.H T.dn T.f 1)) := by
  obtain ⟨_, hp⟩ := hc.lenLast
  refine two_post (two_pub 1 [21, 28, 8, 9, 10] [] HA.F HA.S HA.rest (hws T.H T.dn) (fun _ => [])
    (fun a t h => ⟨_, h.2.1⟩) (fun a t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp) fun a t h => ?_
  obtain ⟨V, W, R, hw, fb, hf, hfb⟩ := h.2.1.W
  obtain ⟨-, h1, hnb⟩ := h.1
  exact X86_64.WP.mono_syms (lenLast_ok hH h.2.1.L R (len := (List.range T.H.P.L).map fun i => V (oLen + i))
    (fun i hi => by simp [List.getD_eq_getElem?_getD, hi]) (hws_w hw).2.1 h1 hnb) fun u ⟨Lu, ku, Ru⟩ sy =>
    ⟨h.1, h.2.1.next Lu ku.2.2 Ru hw ⟨fb, hf, hfb⟩, h.2.2.tr sy⟩

include hH in
theorem body2_wp {a : HA} {j : Nat} {t : State} (hj : j < a.nbm) (h : HL T.H T.dn T.f 1 a j t) :
    WP isa (seqs [.block (compArgs T.H), scall sCmpH T.f.comp, .block nextBlock]) t fun t' =>
      isa.eval .ne t' = some (decide (j + 1 < a.nbm)) ∧ (j + 1 < a.nbm → HL T.H T.dn T.f 1 a (j + 1) t') ∧
      (j + 1 = a.nbm → HD T.H T.dn T.f 1 a t') := by
  have hbB := hb_bound (H := T.H) 1 (p := (a, j)) ⟨hj, h⟩
  obtain ⟨V, W, R, hw, fb, hf, hfb⟩ := h.2.1.W
  obtain ⟨w21, w28, w29⟩ := hl_w hw
  have w10 : W 10 = a.sy T.dn := hw (10, a.sy T.dn) (by simp [hws])
  have hnbm : a.nbm ≤ 2048 := Nat.le_trans (Nat.le_mul_of_pos_right a.nbm hH.B_pos) h.1.2.2
  refine WP.seq_assoc (WP.seq (X86_64.WP.mono_syms (compCall_ok hH h.2.1.L R hbB w29
      (hws_ht h.2.2 fun q hq => hw q (List.mem_append_left _ hq)))
    fun v ⟨Lv, _, hwrv, _, Rv, _⟩ sv => ?_))
  refine X86_64.WP.mono_syms (nextBlock_ok Lv Rv (b := j) (nbm := a.nbm) w29 w28 (by omega_arith) (by omega_arith))
    fun u' ⟨hz, Lu', hk', Ru'⟩ su => ⟨eval_ne_cnt hj hz, fun _ => ⟨h.1, ⟨Lu', hk'.2.2.trans
      (hwrv.trans h.2.1.wr), ⟨_, _, Ru', fun q hq => ?_, fb, by simp [upd, hf], hfb⟩, fun _ hp => by cases hp⟩,
      (h.2.2.tr sv).tr su⟩,
      fun _ => ⟨h.1, ⟨Lu', hk'.2.2.trans (hwrv.trans h.2.1.wr),
        ⟨_, _, Ru', fun q hq => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl <;> simp [upd, w21, w10], trivial⟩, fun _ hp => by cases hp⟩,
        (h.2.2.tr sv).tr su⟩⟩
  rcases List.mem_append.mp hq with hq | hq
  · exact ws_upd (fun q hq => hw q (List.mem_append_left _ hq)) (by simp [hws]) _ q hq
  · rw [List.mem_singleton.mp hq]; simp [upd]

include hH in
theorem compAll_ct (hc : HashChecks T.H.P T.H.D 1) (hfx : FixedChecks 1) :
    RelCT isa (Two (HF T.H T.dn T.f 1)) (compAll T.f T.H) (Two (HD T.H T.dn T.f 1)) := by
  refine RelCT.seq (startB_ct 1 hfx) (two_loop (Φ := HL T.H T.dn T.f 1) HA.nbm ?_
    fun a j t hj h => body2_wp hH hj h)
  simp only [seqs]
  exact RelCT.assoc (RelCT.seq (compA_ct hH 1 hc hfx) (nextB_ct 1 hfx))

include hH hdk in
theorem digestSt_ct (hfx : FixedChecks 1) :
    RelCT isa (Two (HD T.H T.dn T.f 1)) (digestAt T.f oSt) fun _ _ => True := by
  obtain ⟨_, hp⟩ := hfx.digSt
  have hN := hH.N_le
  unfold digestAt
  refine RelCT.seq (two_post (Ψ := fun a t => DA (H := T.H) a.F a.S oSt t ∧ HD T.H T.dn T.f 1 a t)
    (two_pub 1 [21] [] HA.F HA.S HA.rest (fun a => [(21, a.S)]) (fun _ => [])
      (fun a t h => ⟨_, h.2.1.sub (mem21 (by simp)) (fun _ h => h) fun _ _ x => x⟩)
      (fun a t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp) fun a t h => ?_)
    (two_scall 1 (s := sDigH) (by decide) HA.F HA.S HA.rest (fun a => a.sy T.dn)
      (fun a t h => ⟨h.1.1, h.2.2.1.wr, h.2.1.1, pub_slot h.2.2.1 (k := 10) rfl (by decide) (by simp),
        h.2.2.2.2.2.2, h.2.2.2.1.fd⟩)
      (hfx.ld _ (.inr (.inr (.inl rfl))))
      (dig_rel hH hdk fun s₁ s₂ ⟨a, ⟨t₁, h₁, k₁, hm₁, _⟩, ⟨t₂, h₂, k₂, hm₂, _⟩⟩ =>
        ⟨a.F, a.S, oSt, h₁.1.keep11 k₁ hm₁, h₂.1.keep11 k₂ hm₂⟩))
  have L := h.2.1.L
  exact X86_64.WP.mono_syms (digArgs_ok L (src := oSt) (by decide)) fun u ⟨h1, h2, hm, hk⟩ sy =>
    ⟨⟨L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm]), h1, h2, by unfold oSt oDig; omega_arith⟩,
      h.1, h.2.1.keepM (hk.gpr (by decide)) hk.2.2 hm, h.2.2.tr sy⟩

include hH K hdk in
theorem fixedHash_ct (hc : HashChecks T.H.P T.H.D 1) (hv : VerifyChecks T.H.P T.H.D) (hfx : FixedChecks 1) :
    RelCT isa (Two (HE T.H T.dn T.f 1)) (fixedHash T.f T.H) fun _ _ => True := by
  unfold fixedHash seqs seqs seqs seqs
  exact (ctInit_ct hH K 1 hfx).seq ((lenField_ct hH 1 hc).seq ((lenLast_ct hH hv).seq
    ((compAll_ct hH hc hfx).seq (digestSt_ct hH hdk hfx))))

def fixedHashA (H : Hash) (a : State) : HA := ⟨fb a, stackArg a 0, a.wr, fixedNb H a, a.syms⟩

include hH in
theorem fixedN_he {a t : State} (h : VAt T (JFixedN T.H) a t) :
    HE T.H T.dn T.f 1 (fixedHashA T.H a) t := by
  obtain ⟨s, S, v, _, hok, hfit⟩ := h
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hk2 := S.pa.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  have hL := hH.dims.L
  have tb := S.pa.tabs
  have hf : (a.gpr .r8).toNat < vdb T.H.D a := by rwa [S.rsl, S.vdb] at hfit
  have h1 := Nat.lt_div_mul_add (a := 8 + T.H.D + (a.gpr .r8).toNat + T.H.P.L) (b := T.H.P.B) hB0
  have h2 := Nat.div_mul_le_self (8 + T.H.D + (a.gpr .r8).toNat + T.H.P.L) T.H.P.B
  refine ⟨⟨S.rest, Nat.succ_pos _, by
    simp only [fixedHashA, fixedNb]; rw [Nat.succ_mul]; unfold vdb veml at hf; omega_arith⟩, ?_, S.syH.tr v.sy⟩
  obtain ⟨L, wr, ⟨V, W, R, hw, h27, h28⟩, regs⟩ := vs_pub S v
  refine ⟨L, wr, ⟨V, W, R, fun p hp => ?_, 8 + T.H.D + (s.gpr .r8).toNat, h27, ?_⟩, regs⟩
  · simp only [hws, fixedHashA, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact hw (21, stackArg a 0) (by simp [pw, KM, vw])
    · simpa only [fixedNb, S.rsl] using h28
    · exact (pw_w hw (k := 8) (by decide)).trans tb.h0
    · exact (pw_w hw (k := 9) (by decide)).trans tb.h3
    · exact (pw_w hw (k := 10) (by decide)).trans tb.h4
  · simp only [fixedHashA, fixedNb, S.rsl]; rw [Nat.succ_mul]; omega_arith

include hH K hdk in
theorem fixedMhash_ct (hc : HashChecks T.H.P T.H.D 1) (hv : VerifyChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JFixedN T.H))) (fixedHash T.f T.H)
      (Two (VAt T (JT T.H))) := by
  refine two_post (two_map (fixedHashA T.H) (fun a t h => fixedN_he hH h)
    (fixedHash_ct hH K hdk hc hv (fixedChecks (.inl rfl)))) fun a t ⟨s, S, v, hrd, hok, hf⟩ => ?_
  obtain ⟨V, W, R, hw, h27, h28⟩ := v.W
  have hB0 := hH.B_pos
  have hBl := hH.B_le
  have hk2 := S.ps.k2
  have hDN := hH.hDN
  have hN := hH.N_le
  have hL := hH.dims.L
  have h1 := Nat.lt_div_mul_add (a := 8 + T.H.D + (s.gpr .r8).toNat + T.H.P.L) (b := T.H.P.B) hB0
  have h2 := Nat.div_mul_le_self (8 + T.H.D + (s.gpr .r8).toNat + T.H.P.L) T.H.P.B
  refine X86_64.WP.mono_syms (fixedHash_gen hH K v.L R h27 h28 rfl
    (by unfold fixedNb; rw [Nat.succ_mul]; unfold vdb veml at hf; omega_arith) (vs_ht S.ps v hw) hdk)
    fun u ⟨L', rd', wr', _, V', W', R', _, hW', _⟩ sy => ?_
  exact ⟨s, S, v.next L' wr' R' (fun k hk =>
    (hW' k (km_lt hk) (km_ne hk (by decide)) (km_ne hk (by decide))).trans (hw k hk)) trivial sy,
    rd'.trans hrd, hok⟩

include hH K hdk in
theorem fixedSaltBack_ct (hc : PssChecks T.H.P T.H.D) :
    RelCT isa (Two (VAt T (JFixed T.H))) (fixedSaltBack T.f T.H)
      (Two (VAt T (JR T.H))) :=
  (fixedSaltPrefix_ct hH hc.verify).seq
    ((fixedMhash_ct hH K hdk hc.hash1 hc.verify).seq (cmpH_ct hH hc.verify))

end VG.Proof.RsaPss.X86_64.Chk

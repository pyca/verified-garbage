module

import VerifiedGarbage.Proof.RsaPss.X86_64.CtHashOk
public import VerifiedGarbage.Proof.RsaPss.X86_64.CtBase
public import VerifiedGarbage.Proof.RsaPss.X86_64.TabCall
import VerifiedGarbage.Proof.Framework.X86_64.Syms
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Core
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.RsaPss.X86_64.CtComp
meta import VerifiedGarbage.Proof.RsaPss.X86_64.CtHashOk
meta import VerifiedGarbage.Proof.RsaPss.X86_64.CtBase
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Core
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.RsaPss.X86_64.CtComp
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

theorem w21 {t : State} {F S : Addr} (L : Lay t F S) {V : Nat → Byte} {W : Nat → BitVec 64}
    (R : Rep t.mem F S V W) : W 21 = S := by
  have := L.slot
  rw [slot_eq sScr 21 rfl] at this
  rw [← R.fr 21 (by decide)]; exact this

variable (H dn f) in
/-- The anchor fits `ctHash`, and the calls of `f` reach `H`'s functions. -/
def HOk (a : HA) : Prop := RestOk n a.F a.rest ∧ 1 ≤ a.nbm ∧ a.nbm * H.P.B ≤ 2048 ∧ HTF H dn f a.sy

variable (H dn f) in
/-- At the start, and until the length field: the message's length `ℓ`
(secret) fits in the blocks. -/
def HE (a : HA) (t : State) : Prop :=
  HOk H dn f n a ∧ Pub a.F a.S a.rest (hws H dn a) []
    (fun _ W => ∃ ℓ, W 27 = BitVec.ofNat 64 ℓ ∧ ℓ + 1 + H.P.L ≤ a.nbm * H.P.B) t ∧ t.syms = a.sy

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
theorem hws_ht {a : HA} {W : Nat → BitVec 64} (hok : HTF H dn f a.sy) (hw : ∀ p ∈ hws H dn a, W p.1 = p.2) :
    HT H dn f W a.sy :=
  hok.ht (hw (8, _) (by simp [hws])) (hw (9, _) (by simp [hws])) (hw (10, _) (by simp [hws]))

variable (H dn f) in
/-- After the length field: the index of the last block (secret). -/
def HF (a : HA) (t : State) : Prop :=
  HOk H dn f n a ∧ Pub a.F a.S a.rest (hws H dn a) [] (fun _ W => ∃ fb, W 30 = BitVec.ofNat 64 fb ∧ fb < a.nbm) t ∧
    t.syms = a.sy

variable (H dn f) in
/-- Before block `j`. -/
def HL (a : HA) (j : Nat) (t : State) : Prop :=
  HOk H dn f n a ∧ Pub a.F a.S a.rest (hws H dn a ++ [(29, BitVec.ofNat 64 j)]) []
    (fun _ W => ∃ fb, W 30 = BitVec.ofNat 64 fb ∧ fb < a.nbm) t ∧ t.syms = a.sy

variable (H dn f) in
/-- After the blocks. -/
def HD (a : HA) (t : State) : Prop :=
  HOk H dn f n a ∧ Pub a.F a.S a.rest [(21, a.S), (10, a.sy dn)] [] (fun _ _ => True) t ∧ t.syms = a.sy

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
          by rw [h.1.2.2], by rw [h.1.2.2]; exact h.1.1.2.2.2.fi⟩)
        (hfx.ld _ (.inl rfl)) (init_rel hH fun s₁ s₂ ⟨a, ⟨t₁, h₁, k₁, hm₁, _⟩, ⟨t₂, h₂, k₂, hm₂, _⟩⟩ =>
          ⟨a.F, a.S, ⟨lay_keep11 h₁.1.2.1.L k₁ hm₁, (k₁.gpr (by decide)).trans h₁.2⟩,
            ⟨lay_keep11 h₂.1.2.1.L k₂ hm₂, (k₂.gpr (by decide)).trans h₂.2⟩⟩))) fun a t h => ?_
  · have L := h.2.1.L
    exact X86_64.WP.mono_syms (scr_ok L (d := .rdi) (by decide) (o := oSt) (by decide)) fun u ⟨hdi, hm, hk⟩ sy =>
      ⟨⟨h.1, h.2.1.keepM (hk.gpr (by decide)) hk.2.2 hm, sy.trans h.2.2⟩, hdi⟩
  · obtain ⟨V, W, R, hw, hx⟩ := h.2.1.W
    exact X86_64.WP.mono_syms (ctInit_ok hH K h.2.1.L R (by rw [h.2.2]; exact hws_ht h.1.2.2.2 hw))
      fun u ⟨L', _, hwr, _, R', _⟩ sy => ⟨h.1, h.2.1.next L' hwr R' hw hx, sy.trans h.2.2⟩

include hH in
theorem pad80_ct (hc : HashChecks H.P H.D n) : RelCT isa (Two (HE H dn f n)) (pad80 H) (Two (HE H dn f n)) := by
  obtain ⟨_, hp⟩ := hc.pad80
  refine two_post (two_pub n [21, 28, 8, 9, 10] [] HA.F HA.S HA.rest (hws H dn) (fun _ => [])
    (fun a t h => ⟨_, h.2.1⟩) (fun a t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp) fun a t h => ?_
  obtain ⟨V, W, R, hw, ℓ, hl, hfit⟩ := h.2.1.W
  obtain ⟨-, h1, hnb, -⟩ := h.1
  exact X86_64.WP.mono_syms (pad80_ok hH h.2.1.L R hl (hws_w hw).2.1 h1 hnb (by omega_arith)) fun u P sy =>
    ⟨h.1, h.2.1.next P.L P.keep.2.2 P.R hw ⟨ℓ, hl, hfit⟩, sy.trans h.2.2⟩

include hH in
theorem lenField_ct (hc : HashChecks H.P H.D n) :
    RelCT isa (Two (HE H dn f n)) (.block (lenField H)) (Two (HF H dn f n)) := by
  obtain ⟨_, hp⟩ := hc.lenField
  refine two_post (two_pub n [21] [] HA.F HA.S HA.rest (fun a => [(21, a.S)]) (fun _ => [])
    (fun a t h => ⟨_, h.2.1.sub (mem21 (by simp [hws])) (fun _ h => h) fun _ _ x => x⟩)
    (fun a t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp) fun a t h => ?_
  obtain ⟨V, W, R, hw, ℓ, hl, hfit⟩ := h.2.1.W
  obtain ⟨-, h1, hnb, -⟩ := h.1
  have hB0 := hH.B_pos
  refine X86_64.WP.mono_syms (lenField_ok hH h.2.1.L R hl (by omega_arith)) fun u ⟨L', hk, R'⟩ sy =>
    ⟨h.1, h.2.1.next L' hk.2.2 R' (ws_upd hw (by simp [hws]) _) ⟨RsaPss.lastBlk H.P.B H.P.L ℓ, by simp [upd], ?_⟩,
      sy.trans h.2.2⟩
  exact (Nat.div_lt_iff_lt_mul hB0).mpr (by omega_arith)

include hH in
theorem lenLoop_ct (hc : HashChecks H.P H.D n) : RelCT isa (Two (HF H dn f n)) (lenLoop H) (Two (HF H dn f n)) := by
  obtain ⟨_, hp⟩ := hc.lenLoop
  refine two_post (two_pub n [21, 28, 8, 9, 10] [] HA.F HA.S HA.rest (hws H dn) (fun _ => [])
    (fun a t h => ⟨_, h.2.1⟩) (fun a t h => h.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp) fun a t h => ?_
  obtain ⟨V, W, R, hw, fb, hf, hfb⟩ := h.2.1.W
  obtain ⟨-, -, hnb, -⟩ := h.1
  exact X86_64.WP.mono_syms (lenLoop_ok hH h.2.1.L R (len := (List.range H.P.L).map fun i => V (oLen + i))
    (fun i hi => by simp [List.getD_eq_getElem?_getD, hi]) hf (hws_w hw).2.1 hfb hnb) fun u O sy =>
    ⟨h.1, h.2.1.next O.L O.keep.2.2 O.R hw ⟨fb, hf, hfb⟩, sy.trans h.2.2⟩

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
    fun _ hp => by cases hp⟩, sy.trans h.2.2⟩
  rcases List.mem_append.mp hp with hp | hp
  · exact ws_upd hw (by simp [hws]) _ p hp
  · rw [List.mem_singleton.mp hp]; simp [upd]

variable (H dn f) in
/-- Before block `j`, as the loop sees it. -/
abbrev HB (p : HA × Nat) (t : State) : Prop := p.2 < p.1.nbm ∧ HL H dn f n p.1 p.2 t

theorem hb_bound {p : HA × Nat} {t : State} (h : HB H dn f n p t) : H.P.B * p.2 + H.P.B ≤ 2048 := by
  obtain ⟨hj, -, -, hnb, -⟩ := h.1, h.2.1
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
        by rw [h.2.2.2.2], by rw [h.2.2.2.2]; exact h.2.2.1.2.2.2.fc⟩)
      (hfx.ld _ (.inr (.inl rfl)))
      (comp_rel hH fun s₁ s₂ ⟨p, ⟨t₁, h₁, k₁, hm₁, _⟩, ⟨t₂, h₂, k₂, hm₂, _⟩⟩ =>
        ⟨p.1.F, p.1.S, p.2, h₁.1.keep11 k₁ hm₁, h₂.1.keep11 k₂ hm₂⟩))) fun p t h => ?_
  · obtain ⟨V, W, R, hw, -⟩ := h.2.2.1.W
    have L := h.2.2.1.L
    have hbB := hb_bound n h
    have := Nat.le_mul_of_pos_left p.2 hH.B_pos
    exact X86_64.WP.mono_syms (compArgs_ok hH L R (b := p.2) (by omega_arith) (hl_w hw).2.2)
      fun u ⟨h1, h2, h3, h4, hm, hk⟩ sy => ⟨⟨L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm]), h1, h2, h3, h4, hbB⟩,
        h.1, h.2.1, h.2.2.1.keepM (hk.gpr (by decide)) hk.2.2 hm, sy.trans h.2.2.2⟩
  · obtain ⟨V, W, R, hw, hx⟩ := h.2.2.1.W
    exact X86_64.WP.mono_syms (compCall_ok hH h.2.2.1.L R (hb_bound n h) (hl_w hw).2.2
        (by rw [h.2.2.2]; exact hws_ht h.2.1.2.2.2 fun q hq => hw q (List.mem_append_left _ hq)))
      fun u ⟨L', _, hwr, _, R', _⟩ sy => ⟨h.1, h.2.1, h.2.2.1.next L' hwr R' hw hx, sy.trans h.2.2.2⟩

include hH in
theorem select_ct (hc : HashChecks H.P H.D n) : RelCT isa (Two (HB H dn f n)) (select H) (Two (HB H dn f n)) := by
  obtain ⟨_, hp⟩ := hc.select
  refine two_post (two_pub n [21, 29] [] (fun p => p.1.F) (fun p => p.1.S) (fun p => p.1.rest)
      (fun p => [(21, p.1.S), (29, BitVec.ofNat 64 p.2)]) (fun _ => []) (fun p t h => ⟨_, hb_pub n h⟩)
      (fun p t h => h.2.1.1) (fun _ => rfl) (fun _ => rfl) (by decide) hp) fun p t h => ?_
  obtain ⟨V, W, R, hw, fb, hf, hfb⟩ := h.2.2.1.W
  have := Nat.le_trans (Nat.le_mul_of_pos_right _ hH.B_pos) h.2.1.2.2.1
  exact X86_64.WP.mono_syms (select_ok hH h.2.2.1.L R (hl_w hw).2.2 hf (by omega) (by omega)) fun u Sw sy =>
    ⟨h.1, h.2.1, h.2.2.1.next Sw.L Sw.keep.2.2 Sw.R hw ⟨fb, hf, hfb⟩, sy.trans h.2.2.2⟩

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
  have hnbm : a.nbm ≤ 2048 := Nat.le_trans (Nat.le_mul_of_pos_right a.nbm hH.B_pos) h.1.2.2.1
  refine WP.seq_assoc (WP.seq (X86_64.WP.mono_syms (compCall_ok hH h.2.1.L R hbB w29
      (by rw [h.2.2]; exact hws_ht h.1.2.2.2 fun q hq => hw q (List.mem_append_left _ hq)))
    fun v ⟨Lv, _, hwrv, _, Rv, _⟩ sv => ?_))
  refine WP.seq (X86_64.WP.mono_syms (select_ok hH Lv Rv (b := j) (fb := fb) w29 hf (by omega_arith)
    (by omega_arith)) fun w Sw sw => ?_)
  have hsy : ∀ u : State, u.syms = w.syms → u.syms = a.sy := fun u su => su.trans (sw.trans (sv.trans h.2.2))
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
        by rw [h.2.2.2], by rw [h.2.2.2]; exact h.2.1.2.2.2.fd⟩)
      (hfx.ld _ (.inr (.inr (.inl rfl))))
      (dig_rel hH hdk fun s₁ s₂ ⟨a, ⟨t₁, h₁, k₁, hm₁, _⟩, ⟨t₂, h₂, k₂, hm₂, _⟩⟩ =>
        ⟨a.F, a.S, oSel, h₁.1.keep11 k₁ hm₁, h₂.1.keep11 k₂ hm₂⟩))
  have L := h.2.1.L
  exact X86_64.WP.mono_syms (digArgs_ok L (src := oSel) (by decide)) fun u ⟨h1, h2, hm, hk⟩ sy =>
    ⟨⟨L.congr (hk.gpr (by decide)) hk.2.2 (by rw [hm]), h1, h2, by unfold oSel oDig; omega_arith⟩,
      h.1, h.2.1.keepM (hk.gpr (by decide)) hk.2.2 hm, sy.trans h.2.2⟩

include hH K hdk in
/-- `ctHash` is constant time. -/
theorem ctHash_ct (hc : HashChecks H.P H.D n) (hfx : FixedChecks n) :
    RelCT isa (Two (HE H dn f n)) (ctHash f H) fun _ _ => True := by
  unfold ctHash ctHashWith seqs seqs seqs seqs seqs
  exact (ctInit_ct hH K n hfx).seq ((pad80_ct hH n hc).seq ((lenField_ct hH n hc).seq ((lenLoop_ct hH n hc).seq
    ((compLoop_ct hH n hc hfx).seq (digestOut_ct hH hdk n hfx)))))

end VG.Proof.RsaPss.X86_64

module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Correct
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Correct
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
public import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
public import VerifiedGarbage.Proof.Framework.AArch64.TaintErase
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintErase
import Mathlib.Logic.Function.Basic
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
meta import Mathlib.Logic.Function.Basic
meta import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc

/-!
# Deterministic ECDSA on AArch64: constant time, up to the number of candidates

Two runs whose public data agree have the same layout (the same hash
function among them), and stop at the same candidate (`exitAt`, from the
contract's leakage: the number of candidates RFC 6979 tries). Between the
frame's push and pop they are related by `Two`: both satisfy `Ctx` with that
layout (and `Φ`, what the next piece needs). The blocks address only the
stack and the buffers, from registers that agree (the taint analysis, once
for any hash function, and for each shape of scalars where the code's
depends on it); each dispatch runs the same case in both runs, the one of
their hash function (`disp_ct`), and each call is of constant-time code whose
public data agree (`RelCT.callEx`); the loop making a candidate's `T` runs as
many steps in both runs, as many as `T`'s length, the same in both, needs;
and the loop's branch agrees, since in both runs it goes on after candidate
`i` iff `i` is before the candidate it stops at (`go_iff`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64

/-- What each of two runs has, between the frame's push and pop. -/
abbrev Env (P : RfcHash) := Lay P.I.hashLen P.R.E × (Reg → BitVec 64) × (Reg → BitVec 64) × Mem × Mem

/-- Two runs with the same layout that stop at the same candidate, each
satisfying `Ctx` and `Φ`. -/
def Two (P : RfcHash) (Φ : Lay P.I.hashLen P.R.E → Mem → State → Prop) (a b : State) : Prop :=
  ∃ e : Env P, e.1.Ok ∧ CoreOk P e.1 ∧ exitAt P e.1 e.2.2.2.1 = exitAt P e.1 e.2.2.2.2 ∧ Ctx e.1 e.2.1 e.2.2.2.1 a ∧
    Ctx e.1 e.2.2.1 e.2.2.2.2 b ∧ Φ e.1 e.2.2.2.1 a ∧ Φ e.1 e.2.2.2.2 b

variable {P : RfcHash}

theorem Two.mono {Φ Ψ : Lay P.I.hashLen P.R.E → Mem → State → Prop} (h : ∀ L m₀ t, Φ L m₀ t → Ψ L m₀ t) {a b : State}
    (ht : Two P Φ a b) : Two P Ψ a b :=
  let ⟨e, hL, hq, hx, c₁, c₂, f₁, f₂⟩ := ht
  ⟨e, hL, hq, hx, c₁, c₂, h _ _ _ f₁, h _ _ _ f₂⟩

/-- Code whose runs leak the same, and which keeps `Ctx` and establishes `Ψ`. -/
theorem two_wp {c : Prog isa} {Φ Ψ : Lay P.I.hashLen P.R.E → Mem → State → Prop}
    (hct : RelCT isa (Two P Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay P.I.hashLen P.R.E) g m₀ (t : State), L.Ok → CoreOk P L → Ctx L g m₀ t → Φ L m₀ t →
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

theorem sp_two {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 64} {m₁ m₂ : Mem}
    (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) : t₁.sp = t₂.sp :=
  c₁.sp.trans c₂.sp.symm

/-- A block whose addresses depend only on the registers `rs`, which agree. -/
theorem two_blk {is : List Instr} {Φ : Lay P.I.hashLen P.R.E → Mem → State → Prop} (rs : List Reg)
    (hrs : ∀ (L : Lay P.I.hashLen P.R.E) (t₁ t₂ : State) g₁ g₂ m₁ m₂, Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ → Φ L m₁ t₁ →
      Φ L m₂ t₂ → ∀ r ∈ rs, t₁.gpr r = t₂.gpr r)
    (h : ∃ hc, (taint.check (Taint.ofRegs rs) (.block is) hc).isSome = true) :
    RelCT isa (Two P Φ) (.block is) fun _ _ => True :=
  let ⟨_, h⟩ := h
  RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun _ _ ⟨_, _, _, _, c₁, c₂, f₁, f₂⟩ => ⟨sp_two c₁ c₂, fun r hr =>
      hrs _ _ _ _ _ _ _ c₁ c₂ f₁ f₂ r (Taint.mem_ofRegs.mp hr)⟩) h

theorem spOnly {Φ : Lay P.I.hashLen P.R.E → Mem → State → Prop} : ∀ (L : Lay P.I.hashLen P.R.E) (t₁ t₂ : State) g₁ g₂ m₁ m₂,
    Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ → Φ L m₁ t₁ → Φ L m₂ t₂ → ∀ r ∈ ([] : List Reg), t₁.gpr r = t₂.gpr r :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hr => absurd hr (List.not_mem_nil)

/-- Registers that hold the same value `v L` in both runs, by `Φ`. -/
theorem regsAgree {Φ : Lay P.I.hashLen P.R.E → Mem → State → Prop} {rs : List Reg} {v : Reg → Lay P.I.hashLen P.R.E → BitVec 64}
    (h : ∀ L m₀ t, Φ L m₀ t → ∀ r ∈ rs, t.gpr r = v r L) : ∀ (L : Lay P.I.hashLen P.R.E) (t₁ t₂ : State) g₁ g₂ m₁ m₂,
    Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ → Φ L m₁ t₁ → Φ L m₂ t₂ → ∀ r ∈ rs, t₁.gpr r = t₂.gpr r :=
  fun _ _ _ _ _ _ _ _ _ f₁ f₂ r hr => (h _ _ _ f₁ r hr).trans (h _ _ _ f₂ r hr).symm

/-! ## The dispatches -/

/-- A dispatch runs the case of `P`'s hash function in both runs: the
selector, in `x9`, is its number, and `Φ` holds through the test's write of
`x10`. -/
theorem disp_ct {f : Impl.Pbkdf2.Md.AArch64.Hash → Prog isa} {Φ : Lay P.I.hashLen P.R.E → Mem → State → Prop}
    {Q : State → State → Prop}
    (h9 : ∀ L m₀ u, CoreOk P L → Φ L m₀ u → u.gpr .x9 = BitVec.ofNat 64 P.k)
    (hΦ : ∀ L m₀ u u', Φ L m₀ u → Dispatch.AArch64.WritesOnly .x10 u u' → Φ L m₀ u')
    (hf : RelCT isa (Two P Φ) (f P.H) Q) : RelCT isa (Two P Φ) ((cfgOf P).disp f) Q := by
  have hk : P.k ∈ hashIds := by
    have := P.hk; simp only [Spec.Ecdsa.Rfc6979.hashIds, List.mem_cons] at this; simp only [hashIds, List.mem_cons]
    exact this
  have hsel : ∀ u : State, u.gpr .x9 = BitVec.ofNat 64 P.k → Dispatch.AArch64.sel .x9 u = P.k := fun u h => by
    simp only [Dispatch.AArch64.sel, h, BitVec.toNat_ofNat]; have := P.k8; omega
  refine Dispatch.chain_relCT (Dispatch.AArch64.tests .x10 .x9 (by decide)) (by rw [keys_disp]; decide)
    (by rw [keys_disp]; decide) (fun s₁ s₂ hp => ?_) fun k c hc => ?_
  · obtain ⟨_, _, hq, _, _, _, f₁, f₂⟩ := hp
    rw [keys_disp, hsel _ (h9 _ _ _ hq f₁), hsel _ (h9 _ _ _ hq f₂)]; exact ⟨rfl, hk⟩
  · intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨a₁, a₂, ⟨⟨L, g₁, g₂, m₁, m₂⟩, hL, hq, hx, c₁, c₂, f₁, f₂⟩, hk₁, r₁, r₂, _, _⟩ e₁ e₂
    rw [hsel _ (h9 _ _ _ hq f₁)] at hk₁
    subst hk₁
    obtain ⟨a, -, ha⟩ := List.mem_map.mp hc
    simp only [Prod.mk.injEq] at ha
    obtain ⟨rfl, rfl⟩ := ha
    simp only [hs_k] at e₁ e₂
    exact hf _ _ _ _ _ _ ⟨⟨L, g₁, g₂, m₁, m₂⟩, hL, hq, hx, c₁.writesOnly hL (by decide) r₁,
      c₂.writesOnly hL (by decide) r₂, hΦ _ _ _ _ f₁ r₁, hΦ _ _ _ _ f₂ r₂⟩ e₁ e₂

/-- A register other than `x10`, through the test's write. -/
theorem wo_gpr {u u' : State} (h : Dispatch.AArch64.WritesOnly .x10 u u') {r : Reg} (hr : r ≠ .x10) :
    u'.gpr r = u.gpr r := Dispatch.AArch64.WritesOnly.gpr h hr

/-! ## The blocks' taint checks, once for any hash function -/

/-- The taint check of a block whose addresses depend only on `rs`. -/
abbrev TaintOk (rs : List Reg) (is : List Instr) : Prop :=
  ∃ hc, (taint.check (Taint.ofRegs rs) (.block is) hc).isSome = true

/-- A block's check, from that of a block of the same code but its immediates. -/
theorem taintOk_erase {rs : List Reg} {js is : List Instr} (h : TaintOk rs js)
    (he : Code.eraseImm (.block is : Prog isa) = Code.eraseImm (.block js)) : TaintOk rs is := by
  obtain ⟨hc, hs⟩ := h
  have e₁ := Taint.check_eraseImm (Taint.ofRegs rs) (.block is : Prog isa) hc
  have e₂ := Taint.check_eraseImm (Taint.ofRegs rs) (.block js : Prog isa) hc
  rw [he] at e₁
  exact ⟨hc, (congrArg Option.isSome (e₁.symm.trans e₂)).trans hs⟩

/-- The shapes of scalars: their words and bytes, and whether they are `wide`. -/
theorem shape (P : RfcHash) : P.R.wide = false ∧ P.w = 4 ∧ P.Q = 24 ∨ P.R.wide = false ∧ P.w = 4 ∧ P.Q = 28 ∨
    P.R.wide = false ∧ P.w = 4 ∧ P.Q = 32 ∨ P.R.wide = false ∧ P.w = 6 ∧ P.Q = 48 ∨
    P.R.wide = false ∧ P.w = 8 ∧ P.Q = 64 ∨ P.R.wide = true ∧ P.w = 9 ∧ P.Q = 66 := by
  have hw : P.w = P.R.E.n := rfl
  have hq : P.Q = P.R.E.C.len := rfl
  cases hW : P.R.wide
  · have := (P.R.sizesA hW).2.1
    simp only [true_and, Bool.false_eq_true, false_and, or_false]
    rcases (P.R.sizesA hW).1 with hn | hn | hn <;> omega
  · have := P.R.sizesW hW
    simp only [true_and, Bool.true_eq_false, false_and, false_or]
    omega

/-- The extra bytes HMAC's message has past `V`: none, one, or `int2octets`
of the key and `bits2octets` of the hash after it. -/
abbrev ExOk (ex : Nat) : Prop := ex = 0 ∨ ex = 1 ∨ ex = 49 ∨ ex = 57 ∨ ex = 65 ∨ ex = 97 ∨ ex = 129 ∨ ex = 133

theorem exOk_full (P : RfcHash) : ExOk (2 * P.Q + 1) := by
  rcases shape P with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> omega

theorem args₁_blk : TaintOk [] Cfg.hmacArgs₁ := ⟨_, by taint_decide⟩

theorem args₂V_blk : TaintOk [] (Cfg.hmacArgs₂ (Cfg.fr .x2 fV) 0) := ⟨_, by taint_decide⟩

theorem args₂M_blk {ex : Nat} (h : ExOk ex) : TaintOk [] (Cfg.hmacArgs₂ (Cfg.scr .x2 sMsg) ex) := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩

theorem args₃_blk {ex dst : Nat} (h : ExOk ex) (hd : dst = fK ∨ dst = fV) : TaintOk [] (Cfg.hmacArgs₃ ex dst) := by
  rcases hd with rfl | rfl <;> rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, by taint_decide⟩

theorem msgPtrs_blk : TaintOk [] Cfg.msgPtrs := ⟨_, by taint_decide⟩

/-- The pointers and the length the messages are addressed from. -/
abbrev msgRegs : List Reg := [.x8, .x9, .x10, .x15]

theorem msg₀_blk₀ : TaintOk msgRegs (Cfg.msg 4 32 0 false) := ⟨_, by taint_decide⟩

theorem msg₀_blk (w Q : Nat) : TaintOk msgRegs (Cfg.msg w Q 0 false) := msg₀_blk₀

/-- The message of steps d and f, for each shape of scalars. -/
theorem msg_erase (w Q b : Nat) (full : Bool) :
    Code.eraseImm (.block (Cfg.msg w Q b full) : Prog isa) = Code.eraseImm (.block (Cfg.msg w Q 0 full)) := by
  simp only [Code.eraseImm, Cfg.msg, List.map_append, List.map_cons, List.map_nil, Instr.eraseImm]

theorem msgF_blk (P : RfcHash) (b : Nat) : TaintOk msgRegs (Cfg.msg P.w P.Q b true) := by
  refine taintOk_erase ?_ (msg_erase _ _ b true)
  rcases shape P with ⟨-, hw, hq⟩ | ⟨-, hw, hq⟩ | ⟨-, hw, hq⟩ | ⟨-, hw, hq⟩ | ⟨-, hw, hq⟩ | ⟨-, hw, hq⟩ <;>
    rw [hw, hq] <;> exact ⟨_, by taint_decide⟩

theorem dsel_blk : TaintOk [] (Cfg.digestPtr ++ Cfg.selLd) := ⟨_, by taint_decide⟩

/-- The digest's copy, for `P`'s hash function. -/
theorem digG_blk (P : RfcHash) : TaintOk [.x1] ((cfgOf P).digG P.H.D) := by
  have hv := (dlen_vals P.k P.hk).1
  rw [← P.dEq] at hv
  have e₁ : (cfgOf P).len = P.Q := rfl
  have e₂ : (cfgOf P).wide = P.R.wide := rfl
  simp only [Cfg.digG, e₁, e₂]
  rcases shape P with ⟨hW, -, hq⟩ | ⟨hW, -, hq⟩ | ⟨hW, -, hq⟩ | ⟨hW, -, hq⟩ | ⟨hW, -, hq⟩ | ⟨hW, -, hq⟩ <;>
    rw [hW, hq] <;> rcases hv with h | h | h | h | h <;> rw [h] <;> exact ⟨_, by taint_decide⟩

theorem initKV_blk : TaintOk [] Cfg.initKV := ⟨_, by taint_decide⟩

theorem candInit_blk : TaintOk [] Cfg.candInit := ⟨_, by taint_decide⟩
theorem candLd_blk : TaintOk [] Cfg.candLd := ⟨_, by taint_decide⟩

theorem candCopy_blk₀ : TaintOk [.x8, .x9] (cfgC ⟨4, Spec.P256.curve, [], (0, 0), "", true, none, none⟩).candCopy :=
  ⟨_, by taint_decide⟩

theorem candCopy_blk (c : Cfg) : TaintOk [.x8, .x9] c.candCopy := taintOk_erase candCopy_blk₀ rfl

theorem coreArgs_blk : TaintOk [] Cfg.coreArgs := ⟨_, by taint_decide⟩
theorem goOn_blk : TaintOk [] Cfg.goOn := ⟨_, by taint_decide⟩
theorem again_blk : TaintOk [] Cfg.again := ⟨_, by taint_decide⟩
theorem stop_blk : TaintOk [] Cfg.stop := ⟨_, by taint_decide⟩
theorem wipe_blk : TaintOk [] Cfg.wipe := ⟨_, by taint_decide⟩
theorem save_blk : TaintOk [] Cfg.saveArgs := ⟨_, by taint_decide⟩

theorem initCnt_blk₀ : TaintOk [] (cfgC ⟨4, Spec.P256.curve, [], (0, 0), "", true, none, none⟩).initCnt :=
  ⟨_, by taint_decide⟩

theorem initCnt_blk (c : Cfg) : TaintOk [] c.initCnt := taintOk_erase initCnt_blk₀ rfl

/-- A conversion's block, after `scratch`'s load into `x0`. -/
abbrev convBody (c : Cfg) (o s : Nat) : List Instr :=
  .addSp .x6 o :: Impl.Weierstrass.AArch64.loadBytes c.len c.w sSlot .x6 ++
    Impl.Weierstrass.AArch64.shrWords c.w sSlot s ++
    [.movz .x .x3 0 0, .subImm .x .x3 .x3 1] ++ Impl.Weierstrass.AArch64.storeBytes c.len c.w .x6 0 sSlot

theorem conv_eq (c : Cfg) (o s : Nat) : c.conv o s = .seq (.block [.ldrSp .x0 fScratch]) (.block (convBody c o s)) :=
  rfl

theorem ldScr_blk : TaintOk [] [.ldrSp .x0 fScratch] := ⟨_, by taint_decide⟩

/-- If `wide`, the conversions of `G` and of `T`. -/
theorem conv_blk (hW : P.R.wide = true) {o s : Nat} (ho : o = fG ∧ s = 1 ∨ o = fT ∧ s = 7) :
    TaintOk [.x0] (convBody (cfgOf P) o s) := by
  obtain ⟨hw9, hQ66⟩ := P.sizesW hW
  have e₁ : (cfgOf P).len = 66 := hQ66
  have e₂ : (cfgOf P).w = 9 := hw9
  rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [convBody, e₁, e₂, fG, fT] <;> exact ⟨_, by taint_decide⟩

/-! ## The calls of HMAC's functions -/

/-- The registers HMAC's functions take, and the selector. -/
abbrev R6 (a₀ a₁ a₂ a₃ a₄ a₉ : BitVec 64) (u : State) : Prop :=
  u.gpr .x0 = a₀ ∧ u.gpr .x1 = a₁ ∧ u.gpr .x2 = a₂ ∧ u.gpr .x3 = a₃ ∧ u.gpr .x4 = a₄ ∧ u.gpr .x9 = a₉

theorem R6.wo {a₀ a₁ a₂ a₃ a₄ a₉ : BitVec 64} {u u' : State} (h : R6 a₀ a₁ a₂ a₃ a₄ a₉ u)
    (hw : Dispatch.AArch64.WritesOnly .x10 u u') : R6 a₀ a₁ a₂ a₃ a₄ a₉ u' :=
  ⟨by rw [wo_gpr hw (by decide)]; exact h.1, by rw [wo_gpr hw (by decide)]; exact h.2.1,
    by rw [wo_gpr hw (by decide)]; exact h.2.2.1, by rw [wo_gpr hw (by decide)]; exact h.2.2.2.1,
    by rw [wo_gpr hw (by decide)]; exact h.2.2.2.2.1, by rw [wo_gpr hw (by decide)]; exact h.2.2.2.2.2⟩

/-- The arguments of HMAC's `init`. -/
abbrev IA (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (_ : Mem) : State → Prop :=
  R6 (L.scr + BitVec.ofNat 64 0) (L.scr + BitVec.ofNat 64 192) (L.B + BitVec.ofNat 64 16)
    (BitVec.ofNat 64 P.I.hashLen) (L.scr + BitVec.ofNat 64 384) (BitVec.ofNat 64 L.sel)

/-- The arguments of the streaming `update`, for the data at `dA L` of `D + ex` bytes. -/
abbrev UA (P : RfcHash) (dA : Lay P.I.hashLen P.R.E → Addr) (ex : Nat) (L : Lay P.I.hashLen P.R.E) (_ : Mem) :
    State → Prop :=
  R6 (L.scr + BitVec.ofNat 64 0) (BitVec.ofNat 64 L.bl) (dA L) (BitVec.ofNat 64 (P.I.hashLen + ex))
    (L.scr + BitVec.ofNat 64 384) (BitVec.ofNat 64 L.sel)

/-- The arguments of HMAC's `finalize`, for `D + ex` bytes of data and the MAC to `dst`. -/
abbrev FA (P : RfcHash) (ex dst : Nat) (L : Lay P.I.hashLen P.R.E) (_ : Mem) : State → Prop :=
  R6 (L.scr + BitVec.ofNat 64 0) (L.scr + BitVec.ofNat 64 192) (BitVec.ofNat 64 (L.bl + (P.I.hashLen + ex)))
    (L.B + BitVec.ofNat 64 (16 + dst)) (L.scr + BitVec.ofNat 64 384) (BitVec.ofNat 64 L.sel)

theorem sel9 {a₀ a₁ a₂ a₃ a₄ : BitVec 64} : ∀ (L : Lay P.I.hashLen P.R.E) (_ : Mem) (u : State), CoreOk P L →
    R6 a₀ a₁ a₂ a₃ a₄ (BitVec.ofNat 64 L.sel) u → u.gpr .x9 = BitVec.ofNat 64 P.k :=
  fun _ _ _ hq h => by rw [h.2.2.2.2.2, hq.2.1]

theorem ce_sp_two {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 64}
    {m₁ m₂ : Mem} (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) (rd₁ wr₁ rd₂ wr₂ : List Region) :
    (t₁.callEntry.withRegions rd₁ wr₁).sp = (t₂.callEntry.withRegions rd₂ wr₂).sp := by
  rw [State.withRegions_sp, State.withRegions_sp, State.callEntry_sp, State.callEntry_sp, sp_two c₁ c₂]

theorem ce_two {t₁ t₂ : State} {r : Reg} (hr : r ∉ linkRegs) {x : BitVec 64} (h₁ : t₁.gpr r = x) (h₂ : t₂.gpr r = x)
    (rd₁ wr₁ rd₂ wr₂ : List Region) :
    (t₁.callEntry.withRegions rd₁ wr₁).gpr r = (t₂.callEntry.withRegions rd₂ wr₂).gpr r := by
  rw [ce_gpr _ _ _ hr, ce_gpr _ _ _ hr, h₁, h₂]

theorem hinit_ct : RelCT isa (Two P (IA P)) (.call P.H.hmacInitN P.H.hmacInit) fun _ _ => True :=
  AArch64.RelCT.callEx P.hI.1 P.hI.2.1 fun _ _ ⟨⟨L, _, _, _, _⟩, hL, _, _, c₁, c₂, a₁, a₂⟩ => by
    obtain ⟨d₁, s₁, x₁, k₁, r₁, -⟩ := a₁
    obtain ⟨d₂, s₂, x₂, k₂, r₂, -⟩ := a₂
    have A₁ := initA (P := P) hL c₁ d₁ s₁ x₁ k₁ r₁
    have A₂ := initA (P := P) hL c₂ d₂ s₂ x₂ k₂ r₂
    exact ⟨_, _, _, _, Pbkdf2.Md.AArch64.Pbk.InitArgs.pre P.ok A₁, Pbkdf2.Md.AArch64.Pbk.InitArgs.pre P.ok A₂,
      ⟨ce_two (by decide) d₁ d₂ _ _ _ _, ce_two (by decide) s₁ s₂ _ _ _ _, ce_two (by decide) x₁ x₂ _ _ _ _,
        ce_two (by decide) k₁ k₂ _ _ _ _, ce_two (by decide) r₁ r₂ _ _ _ _, ce_sp_two c₁ c₂ _ _ _ _⟩,
      Pbkdf2.Md.AArch64.Pbk.covers_app A₁.cr A₁.cw, A₁.cw, Pbkdf2.Md.AArch64.Pbk.covers_app A₂.cr A₂.cw, A₂.cw⟩

theorem hupd_ct {dA : Lay P.I.hashLen P.R.E → Addr} {ex : Nat}
    (hd : ∀ L : Lay P.I.hashLen P.R.E, L.Ok → DataOk L (dA L) (P.H.D + ex)) (hlen : P.H.D + ex ≤ 256) :
    RelCT isa (Two P (UA P dA ex)) (.call P.H.updN P.H.updC) fun _ _ => True :=
  AArch64.RelCT.callEx P.ok.stream.upd.1 P.ok.stream.upd.2.1 fun _ _ ⟨⟨L, _, _, _, _⟩, hL, _, _, c₁, c₂, a₁, a₂⟩ => by
    obtain ⟨d₁, s₁, x₁, k₁, r₁, -⟩ := a₁
    obtain ⟨d₂, s₂, x₂, k₂, r₂, -⟩ := a₂
    have A₁ := updA (P := P) hL c₁ (hd L hL) hlen d₁ x₁ k₁ r₁
    have A₂ := updA (P := P) hL c₂ (hd L hL) hlen d₂ x₂ k₂ r₂
    exact ⟨_, _, _, _, Pbkdf2.Md.AArch64.Calls.UpdArgs.pre P.ok.stream A₁,
      Pbkdf2.Md.AArch64.Calls.UpdArgs.pre P.ok.stream A₂,
      ⟨ce_two (by decide) d₁ d₂ _ _ _ _, ce_two (by decide) s₁ s₂ _ _ _ _, ce_two (by decide) x₁ x₂ _ _ _ _,
        ce_two (by decide) k₁ k₂ _ _ _ _, ce_two (by decide) r₁ r₂ _ _ _ _, ce_sp_two c₁ c₂ _ _ _ _⟩,
      Pbkdf2.Md.AArch64.Calls.UpdArgs.covers P.ok.stream A₁, A₁.cw,
      Pbkdf2.Md.AArch64.Calls.UpdArgs.covers P.ok.stream A₂, A₂.cw⟩

theorem hfin_ct {ex dst : Nat} (hdst : dst + P.H.D ≤ 200) :
    RelCT isa (Two P (FA P ex dst)) (.call P.H.hmacFinN P.H.hmacFin) fun _ _ => True :=
  AArch64.RelCT.callEx P.hF.1 P.hF.2.1 fun _ _ ⟨⟨L, _, _, _, _⟩, hL, hq, _, c₁, c₂, a₁, a₂⟩ => by
    obtain ⟨d₁, s₁, x₁, k₁, r₁, -⟩ := a₁
    obtain ⟨d₂, s₂, x₂, k₂, r₂, -⟩ := a₂
    have e : BitVec.ofNat 64 (L.bl + (P.I.hashLen + ex)) = BitVec.ofNat 64 (P.H.P.B + (P.H.D + ex)) := by
      rw [hq.2.2]
    have A₁ := finA (P := P) hL c₁ (len := P.H.D + ex) hdst d₁ s₁ (x₁.trans e) k₁ r₁
    have A₂ := finA (P := P) hL c₂ (len := P.H.D + ex) hdst d₂ s₂ (x₂.trans e) k₂ r₂
    exact ⟨_, _, _, _, Pbkdf2.Md.AArch64.Pbk.FinArgs.pre P.ok A₁, Pbkdf2.Md.AArch64.Pbk.FinArgs.pre P.ok A₂,
      ⟨ce_two (by decide) d₁ d₂ _ _ _ _, ce_two (by decide) s₁ s₂ _ _ _ _, ce_two (by decide) x₁ x₂ _ _ _ _,
        ce_two (by decide) k₁ k₂ _ _ _ _, ce_two (by decide) r₁ r₂ _ _ _ _, ce_sp_two c₁ c₂ _ _ _ _⟩,
      Pbkdf2.Md.AArch64.Pbk.covers_app A₁.cr A₁.cw, A₁.cw, Pbkdf2.Md.AArch64.Pbk.covers_app A₂.cr A₂.cw, A₂.cw⟩

/-! ## The dispatched calls keep `Ctx` -/

variable {L : Lay P.I.hashLen P.R.E} {g : Reg → BitVec 64} {m₀ : Mem}

theorem scr_sub {r : Region} (h : Region.Sub r ⟨L.scr, 2432⟩) : Safe L r :=
  .inr (.inl (sub_trans h (Region.sub_prefix (by omega))))

theorem init_ctx (hL : L.Ok) (hq : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) (ha : IA P L m₀ u) :
    WP isa ((cfgOf P).disp fun H => .call H.hmacInitN H.hmacInit) u fun u' => Ctx L g m₀ u' ∧ True := by
  refine disp_wp P (sel9 L m₀ u hq ha) fun w hw => ?_
  have hcw := hc.writesOnly hL (by decide) hw
  obtain ⟨h0, h1, h2, h3, h4, -⟩ := ha.wo hw
  refine Pbkdf2.Md.AArch64.Pbk.hinit_call P.ok P.hI P.hId (initA (P := P) hL hcw h0 h1 h2 h3 h4)
    fun u' ha' _ _ => ⟨hcw.after hL ha' fun r hr => ?_, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact scr_sub (scr_work (by anums))

theorem upd_ctx {dA : Lay P.I.hashLen P.R.E → Addr} {ex : Nat}
    (hd : ∀ L : Lay P.I.hashLen P.R.E, L.Ok → DataOk L (dA L) (P.H.D + ex)) (hlen : P.H.D + ex ≤ 256)
    (hL : L.Ok) (hq : CoreOk P L) {u : State} (hc : Ctx L g m₀ u) (ha : UA P dA ex L m₀ u) :
    WP isa ((cfgOf P).disp fun H => .call H.updN H.updC) u fun u' => Ctx L g m₀ u' ∧ True := by
  refine disp_wp P (sel9 L m₀ u hq ha) fun w hw => ?_
  have hcw := hc.writesOnly hL (by decide) hw
  obtain ⟨h0, -, h2, h3, h4, -⟩ := ha.wo hw
  refine Pbkdf2.Md.AArch64.Calls.upd_call P.ok.stream (updA (P := P) hL hcw (hd L hL) hlen h0 h2 h3 h4)
    fun u' af _ => ⟨hcw.after hL af fun r hr => ?_, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact scr_sub (scr_work (by anums))

theorem fin_ctx {ex dst : Nat} (hdst : dst + P.H.D ≤ 200) (hL : L.Ok) (hq : CoreOk P L) {u : State}
    (hc : Ctx L g m₀ u) (ha : FA P ex dst L m₀ u) :
    WP isa ((cfgOf P).disp fun H => .call H.hmacFinN H.hmacFin) u fun u' => Ctx L g m₀ u' ∧ True := by
  refine disp_wp P (sel9 L m₀ u hq ha) fun w hw => ?_
  have hcw := hc.writesOnly hL (by decide) hw
  obtain ⟨h0, h1, h2, h3, h4, -⟩ := ha.wo hw
  have h2' : w.gpr .x2 = BitVec.ofNat 64 (P.H.P.B + (P.H.D + ex)) := by rw [h2, hq.2.2]
  refine Pbkdf2.Md.AArch64.Pbk.hfin_call P.ok P.hF P.hFd (finA (P := P) hL hcw hdst h0 h1 h2' h3 h4)
    fun u' ha' _ => ⟨hcw.after hL ha' fun r hr => ?_, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact scr_sub (scr_work (by anums))
  · exact safe_low L (by anums)
  · exact scr_sub (scr_work (by anums))

/-! ## One HMAC -/

/-- `HMAC_K(data)`: its blocks address only the frame and `scratch`, from `sp`,
and each dispatched call is of constant-time code whose arguments agree. -/
theorem hmac_ct {dataA : List Instr} {dA : Lay P.I.hashLen P.R.E → Addr} {ex dst : Nat}
    {Φ : Lay P.I.hashLen P.R.E → Mem → State → Prop}
    (hdA : ∀ (L : Lay P.I.hashLen P.R.E) g m₀ u, L.Ok → Ctx L g m₀ u →
      WP isa (.block dataA) u (Upd L g m₀ u .x2 (dA L)))
    (hd : ∀ L : Lay P.I.hashLen P.R.E, L.Ok → DataOk L (dA L) (P.H.D + ex)) (hlen : P.H.D + ex ≤ 256)
    (hdst : dst + P.H.D ≤ 200) (hex : ex < 4096) (hdst' : dst < 4096)
    (t₂ : TaintOk [] (Cfg.hmacArgs₂ dataA ex)) (t₃ : TaintOk [] (Cfg.hmacArgs₃ ex dst)) :
    RelCT isa (Two P Φ) ((cfgOf P).hmac dataA ex dst) fun _ _ => True := by
  refine (two_wp (Ψ := IA P) (two_blk [] spOnly args₁_blk) fun _ _ _ _ hL _ hc _ =>
    WP.mono (initArgs_ok hL hc) fun _ ⟨c, _, a⟩ => ⟨c, a⟩).seq ?_
  refine (two_wp (Ψ := fun _ _ _ => True) (disp_ct (Φ := IA P) (fun _ _ _ hq h => by rw [h.2.2.2.2.2, hq.2.1]) (fun _ _ _ _ h hw => R6.wo h hw) hinit_ct)
    fun _ _ _ _ hL hq hc ha => init_ctx hL hq hc ha).seq ?_
  refine (two_wp (Ψ := UA P dA ex) (two_blk [] spOnly t₂) fun L g m₀ _ hL _ hc _ =>
    WP.mono (updArgs_ok hL hc (fun u hu => hdA L g m₀ u hL hu) hex) fun _ ⟨c, _, a⟩ => ⟨c, a⟩).seq ?_
  refine (two_wp (Ψ := fun _ _ _ => True) (disp_ct (Φ := UA P dA ex) (fun _ _ _ hq h => by rw [h.2.2.2.2.2, hq.2.1]) (fun _ _ _ _ h hw => R6.wo h hw) (hupd_ct hd hlen))
    fun _ _ _ _ hL hq hc ha => upd_ctx hd hlen hL hq hc ha).seq ?_
  refine (two_wp (Ψ := FA P ex dst) (two_blk [] spOnly t₃) fun _ _ _ _ hL _ hc _ =>
    WP.mono (finArgs_ok hL hc hex hdst') fun _ ⟨c, _, a⟩ => ⟨c, a⟩).seq ?_
  exact disp_ct (Φ := FA P ex dst) (fun _ _ _ hq h => by rw [h.2.2.2.2.2, hq.2.1]) (fun _ _ _ _ h hw => R6.wo h hw) (hfin_ct hdst)

/-- `V = HMAC_K(V)`. -/
theorem hmacV_ct {Φ : Lay P.I.hashLen P.R.E → Mem → State → Prop} :
    RelCT isa (Two P Φ) (cfgOf P).hmacV fun _ _ => True :=
  hmac_ct (dA := fun L => L.B + BitVec.ofNat 64 (16 + 64)) (ex := 0) (dst := 64)
    (fun _ _ _ _ hL hu => fr_ok hL hu (d := .x2) (by decide) (o := 64) (by decide))
    (fun _ _ => .inl ⟨80, rfl, by omega, by anums⟩) (by anums) (by anums) (by decide) (by decide) args₂V_blk
    (args₃_blk (by decide) (.inr rfl))

/-- `K = HMAC_K(m)`, for the message of `D + ex` bytes at `scratch + 2432`. -/
theorem hmacK_ct {Φ : Lay P.I.hashLen P.R.E → Mem → State → Prop} {ex : Nat} (hex : ExOk ex)
    (hlen : P.H.D + ex ≤ 256) :
    RelCT isa (Two P Φ) ((cfgOf P).hmac (Cfg.scr .x2 sMsg) ex fK) fun _ _ => True :=
  hmac_ct (dA := fun L => L.scr + BitVec.ofNat 64 2432) (dst := 0)
    (fun _ _ _ _ hL hu => scr_ok hL hu (d := .x2) (by decide) (a := 2432) (by decide))
    (fun _ _ => .inr ⟨2432, rfl, by omega, by omega⟩) hlen (by anums) (by omega) (by decide) (args₂M_blk hex)
    (args₃_blk hex (.inl rfl))

/-- `scratch` in `x9`, `d` in `x10`, the frame in `x15`, and `D` in `x8`. -/
abbrev PtrsIn (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (_ : Mem) (u : State) : Prop :=
  u.gpr .x9 = L.scr ∧ u.gpr .x10 = L.d ∧ u.gpr .x15 = L.B + BitVec.ofNat 64 16 ∧
    u.gpr .x8 = BitVec.ofNat 64 P.I.hashLen

/-- `K = HMAC_K(m)`, then `V = HMAC_K(V)`, for the message `m = V ‖ b (‖ tail)`. -/
theorem rekey_gen_ct {Φ : Lay P.I.hashLen P.R.E → Mem → State → Prop} {b : Nat} {full : Bool} {ex : Nat}
    (hex : ex = if full then 2 * P.Q + 1 else 1) (t₁ : TaintOk msgRegs (Cfg.msg P.w P.Q b full)) :
    RelCT isa (Two P Φ) (.seq (.block Cfg.msgPtrs) (.seq (.block (Cfg.msg P.w P.Q b full))
      (.seq ((cfgOf P).hmac (Cfg.scr .x2 sMsg) ex fK) (cfgOf P).hmacV))) fun _ _ => True := by
  have hs := P.wsizes
  have hlen : P.H.D + ex ≤ 256 := by
    subst hex; cases full <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> anums
  have hex' : ExOk ex := by
    subst hex; cases full
    · exact .inr (.inl rfl)
    · exact exOk_full P
  refine (two_wp (Ψ := PtrsIn P) (two_blk [] spOnly msgPtrs_blk) fun _ _ _ _ hL _ hc _ =>
    WP.mono (ptrs_ok hL hc) fun _ ⟨c, _, a⟩ => ⟨c, a⟩).seq ?_
  refine (two_wp (Ψ := fun _ _ _ => True) (two_blk msgRegs (fun _ _ _ _ _ _ _ _ _ f₁ f₂ r hr => by
      simp only [msgRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact f₁.2.2.2.trans f₂.2.2.2.symm
      · exact f₁.1.trans f₂.1.symm
      · exact f₁.2.1.trans f₂.2.1.symm
      · exact f₁.2.2.1.trans f₂.2.2.1.symm) t₁) fun _ _ _ _ hL hk hc hp =>
    WP.mono (msg_ok hL hc hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 b full (w := P.w) (Q := P.Q) (by anums)
      fun _ => ⟨by omega, by omega, by omega, by rw [hk.1]⟩) fun _ h => ⟨h.1, trivial⟩).seq ?_
  exact (two_wp (Ψ := fun _ _ _ => True) (hmacK_ct hex' hlen) fun _ _ _ _ hL hk hc _ =>
    WP.mono (hmacK_ok (P := P) hL rfl hk.2 hc hlen) fun _ h => ⟨h.1, trivial⟩).seq hmacV_ct

theorem rekeyFull_ct {Φ : Lay P.I.hashLen P.R.E → Mem → State → Prop} (b : Nat) :
    RelCT isa (Two P Φ) ((cfgOf P).rekeyFull b) fun _ _ => True :=
  rekey_gen_ct (full := true) rfl (msgF_blk P b)

theorem rekey_ct {Φ : Lay P.I.hashLen P.R.E → Mem → State → Prop} :
    RelCT isa (Two P Φ) (cfgOf P).rekey fun _ _ => True :=
  rekey_gen_ct (b := 0) (full := false) rfl (msg₀_blk _ _)

/-! ## The conversions and the candidate -/

/-- `scratch` in `x0`. -/
abbrev ScrIn {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} (L : Lay dn E) (_ : Mem) (u : State) : Prop := u.gpr .x0 = L.scr

/-- A conversion: its block addresses memory from `scratch`, loaded first, and `sp`. -/
theorem conv_ct {Φ : Lay P.I.hashLen P.R.E → Mem → State → Prop} {o s : Nat}
    (h : TaintOk [.x0] (convBody (cfgOf P) o s)) :
    RelCT isa (Two P Φ) ((cfgOf P).conv o s) fun _ _ => True := by
  rw [conv_eq]
  exact (two_wp (Ψ := ScrIn) (two_blk [] spOnly ldScr_blk) fun _ _ _ _ hL _ hc _ =>
    WP.mono (ldScr_ok hL hc) fun _ h => ⟨h.ctx, h.val⟩).seq (two_blk [.x0] (fun _ _ _ _ _ _ _ _ _ f₁ f₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact f₁.trans f₂.symm) h)

/-- Before step `i + 1` of `T`, for some key, `V` and state the candidate started from. -/
abbrev TIn (P : RfcHash) (i : Nat) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) (u : State) : Prop :=
  ∃ (g' : Reg → BitVec 64) (K V₀ : List Byte) (t : State), TInv P L g' m₀ K V₀ t i u

/-- After step `i + 1` of `T`. -/
abbrev TNext (P : RfcHash) (i : Nat) (L : Lay P.I.hashLen P.R.E) (m₀ : Mem) (u : State) : Prop :=
  ∃ (g' : Reg → BitVec 64) (K V₀ : List Byte) (t : State),
    (isa.eval (.nonzero .x .x12) u = some true ∧ TInv P L g' m₀ K V₀ t (i + 1) u) ∨
    (isa.eval (.nonzero .x .x12) u = some false ∧ TOut P L g' m₀ K V₀ t (i + 1) u)

/-- One step of `T`: its blocks address the frame from `sp` and from `T`'s
length, `i D`, in both runs. -/
theorem stepT_trace (i : Nat) : RelCT isa (Two P (TIn P i)) (cfgOf P).candStep fun _ _ => True := by
  refine (two_wp (Ψ := fun L _ u => tlOf L u.mem = BitVec.ofNat 64 (i * P.H.D)) hmacV_ct
    fun _ _ _ _ hL hq hc ⟨_, _, _, _, hi⟩ => WP.mono (hmacV_ok hL rfl hq.2 hc) fun _ ⟨hc₁, hf₁, _, _⟩ =>
      ⟨hc₁, (tl_kvw hL hf₁).trans hi.tl⟩).seq ?_
  refine (two_wp (Ψ := fun _ _ u => u.gpr .x8 = BitVec.ofNat 64 P.I.hashLen ∧
      u.gpr .x9 = BitVec.ofNat 64 (i * P.H.D)) (two_blk [] spOnly candLd_blk)
    fun _ _ _ _ hL _ hc htl => WP.mono (candLd_ok hL hc) fun _ ⟨hc₂, _, h8, h9⟩ =>
      ⟨hc₂, h8, h9.trans htl⟩).seq ?_
  exact two_blk [.x8, .x9] (fun _ _ _ _ _ _ _ _ _ f₁ f₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact f₁.1.trans f₂.1.symm
    · exact f₁.2.trans f₂.2.symm) (candCopy_blk _)

/-- One step of `T`, with whether to go on, which agrees: both runs have `T`'s
same length. -/
theorem stepT_ct (n : Nat) :
    RelCT isa (Two P (TIn P (4 - n))) (cfgOf P).candStep fun s₁ s₂ =>
      isa.eval (.nonzero .x .x12) s₁ = isa.eval (.nonzero .x .x12) s₂ ∧
      (isa.eval (.nonzero .x .x12) s₁ = some false → Two P (fun _ _ _ => True) s₁ s₂) ∧
      (isa.eval (.nonzero .x .x12) s₁ = some true → ∃ m < n, Two P (TIn P (4 - m)) s₁ s₂) := by
  have hD := P.sizes.2.2.2.2.2.2.1
  have hQ := P.wsizes
  have h2 := two_wp (Ψ := TNext P (4 - n)) (stepT_trace _) fun L g m₀ _ hL hq hc hh => by
    obtain ⟨_, K, V₀, t, hi⟩ := hh
    exact WP.mono (step_ok hL hq ({ hi with ctx := hc } : TInv P L g m₀ K V₀ t (4 - n) _)) fun u h => by
      rcases h with ⟨he, hx⟩ | ⟨he, hx⟩
      · exact ⟨hx.ctx, g, K, V₀, t, .inl ⟨he, hx⟩⟩
      · exact ⟨hx.ctx, g, K, V₀, t, .inr ⟨he, hx⟩⟩
  refine h2.mono (fun _ _ h => h) fun s₁ s₂ ⟨e, hL, hq, hx, c₁, c₂, f₁, f₂⟩ => ?_
  obtain ⟨_, _, _, _, f₁⟩ := f₁
  obtain ⟨_, _, _, _, f₂⟩ := f₂
  -- Whether to go on: `T` is shorter than `Q` bytes, the same in both runs.
  have stop : ∀ {g' K V₀ t} {m₀ : Mem} {u : State}, TOut P e.1 g' m₀ K V₀ t (4 - n + 1) u →
      ¬ (4 - n + 1) * P.H.D < P.Q := fun ho => by have := ho.hi; omega
  rcases f₁ with ⟨d₁, x₁⟩ | ⟨d₁, x₁⟩ <;> rcases f₂ with ⟨d₂, x₂⟩ | ⟨d₂, x₂⟩
  · have hlt := x₁.lt
    have h3 : 4 - n + 1 ≤ 3 := by
      by_contra h
      have : 4 * P.H.D ≤ (4 - n + 1) * P.H.D := Nat.mul_le_mul_right _ (by omega)
      omega
    refine ⟨d₁.trans d₂.symm, fun h => absurd (h.symm.trans d₁) (by decide), fun _ =>
      ⟨3 - (4 - n), by omega, e, hL, hq, hx, c₁, c₂, ?_, ?_⟩⟩
    · rw [show 4 - (3 - (4 - n)) = 4 - n + 1 by omega]; exact ⟨_, _, _, _, x₁⟩
    · rw [show 4 - (3 - (4 - n)) = 4 - n + 1 by omega]; exact ⟨_, _, _, _, x₂⟩
  · exact absurd x₁.lt (stop x₂)
  · exact absurd x₂.lt (stop x₁)
  · exact ⟨d₁.trans d₂.symm, fun _ => ⟨e, hL, hq, hx, c₁, c₂, trivial, trivial⟩,
      fun h => absurd (h.symm.trans d₁) (by decide)⟩

/-- The candidate: its calls and blocks leak the same in both runs. -/
theorem cand_ct {Φ : Lay P.I.hashLen P.R.E → Mem → State → Prop} :
    RelCT isa (Two P Φ) (cfgOf P).cand fun _ _ => True := by
  have hloop : RelCT isa (Two P (TIn P (4 - 4))) (.loop (cfgOf P).candStep (.nonzero .x .x12))
      (Two P fun _ _ _ => True) :=
    VG.RelCT.loop (M := isa) (fun n => Two P (TIn P (4 - n))) stepT_ct 4
  refine (two_wp (Ψ := TIn P (4 - 4)) (two_blk [] spOnly candInit_blk) fun _ _ _ _ hL _ hc _ =>
    WP.mono (candInit_inv hL hc) fun _ hi => ⟨hi.ctx, _, _, _, _, hi⟩).seq ?_
  cases hW : P.R.wide
  · have e : (cfgOf P).wide = false := hW
    simp only [e, Bool.false_eq_true, ite_false]
    exact hloop.mono (fun _ _ h => h) fun _ _ _ => trivial
  · have e : (cfgOf P).wide = true := hW
    simp only [e, ite_true]
    exact hloop.seq (conv_ct (conv_blk hW (.inr ⟨rfl, sh7 hW⟩)))

/-! ## The start -/

/-- `digest` in `x1` and the selector in `x9`. -/
abbrev DgIn (P : RfcHash) (L : Lay P.I.hashLen P.R.E) (_ : Mem) (u : State) : Prop :=
  u.gpr .x1 = L.dg ∧ u.gpr .x9 = BitVec.ofNat 64 L.sel

/-- `G`, `h`, and the initial `K` and `V`. -/
theorem start_ct {Φ : Lay P.I.hashLen P.R.E → Mem → State → Prop} :
    RelCT isa (Two P Φ) (cfgOf P).start fun _ _ => True := by
  have hs := P.sizes
  refine (two_wp (Ψ := DgIn P) (two_blk [] spOnly dsel_blk) fun _ _ _ _ hL _ hc _ =>
    WP.mono (dsel_ok hL hc) fun _ ⟨c, _, h1, h9⟩ => ⟨c, h1, h9⟩).seq ?_
  have hdig := disp_ct (P := P) (f := fun H => .block ((cfgOf P).digG H.D)) (Q := fun _ _ => True)
    (Φ := DgIn P) (fun _ _ _ hq h => by rw [h.2, hq.2.1])
    (fun _ _ _ _ h hw => ⟨by rw [wo_gpr hw (by decide)]; exact h.1, by rw [wo_gpr hw (by decide)]; exact h.2⟩)
    (two_blk [.x1] (fun _ _ _ _ _ _ _ _ _ f₁ f₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact f₁.1.trans f₂.1.symm) (digG_blk P))
  cases hW : P.R.wide
  · have e : (cfgOf P).wide = false := hW
    simp only [e, Bool.false_eq_true, ite_false]
    refine (two_wp (Ψ := fun _ _ _ => True) hdig fun _ _ _ _ hL hq hc h =>
      disp_wp P (by rw [h.2, hq.2.1]) fun w hw => WP.mono (digN_ok hW hL (D := P.H.D) (Nat.le_refl _)
        (by omega) (hc.writesOnly hL (by decide) hw) (by rw [wo_gpr hw (by decide)]; exact h.1))
        fun _ h => ⟨h.1, trivial⟩).seq ?_
    exact two_blk [] spOnly (P.R.reduceT hW)
  · have e : (cfgOf P).wide = true := hW
    simp only [e, ite_true]
    have h81 : 8 - (cfgOf P).sh = 1 := by show 8 - P.R.sh = 1; rw [sh7 hW]
    rw [h81]
    refine (two_wp (Ψ := fun _ _ _ => True) hdig fun _ _ _ _ hL hq hc h =>
      disp_wp P (by rw [h.2, hq.2.1]) fun w hw => WP.mono (digW_ok hW hL (D := P.H.D) (Nat.le_refl _)
        (by omega) (by omega) (hc.writesOnly hL (by decide) hw) (by rw [wo_gpr hw (by decide)]; exact h.1))
        fun _ h => ⟨h.1, trivial⟩).seq ?_
    refine (two_wp (Ψ := fun _ _ _ => True) (conv_ct (conv_blk hW (.inl ⟨rfl, rfl⟩))) fun _ _ _ _ hL _ hc _ =>
      WP.mono (conv_ok (P := P) hL hW hc (o := fG) (s := 1) (by decide) (by decide) (by decide) (by decide)
        (by decide)) fun _ h => ⟨h.1, trivial⟩).seq ?_
    exact two_blk [] spOnly initKV_blk

/-! ## One candidate -/

/-- `core`, with arguments that agree. -/
theorem core_ct {i : Nat} :
    RelCT isa (Two P fun L m₀ u => P₁ P L m₀ i u ∧ Args L u) (.call (cfgOf P).coreN (cfgOf P).coreC)
      fun _ _ => True :=
  AArch64.RelCT.callEx P.R.coreX P.R.coreCT
    fun _ _ ⟨⟨L, _, _, _, _⟩, hL, hq, _, c₁, c₂, ⟨_, a₁⟩, ⟨_, a₂⟩⟩ =>
    ⟨coreRd P L, coreWr P L, coreRd P L, coreWr P L, core_pre hL hq c₁ a₁.x0 a₁.x1 a₁.x2 a₁.x3 a₁.x4,
      core_pre hL hq c₂ a₂.x0 a₂.x1 a₂.x2 a₂.x3 a₂.x4,
      ⟨ce_two (by decide) a₁.x0 a₂.x0 _ _ _ _, ce_two (by decide) a₁.x1 a₂.x1 _ _ _ _,
        ce_two (by decide) a₁.x2 a₂.x2 _ _ _ _, ce_two (by decide) a₁.x3 a₂.x3 _ _ _ _,
        ce_two (by decide) a₁.x4 a₂.x4 _ _ _ _, ce_sp_two c₁ c₂ _ _ _ _, c₁.sy.trans c₂.sy.symm⟩,
      core_covers hL hq c₁, core_coversW hq.1 c₁, core_covers hL hq c₂, core_coversW hq.1 c₂⟩

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
  refine (two_wp (Ψ := fun L m₀ u => P₁ P L m₀ i u) cand_ct fun _ _ _ _ hL hk hc hi =>
    try₁_ok hL hk hc hi).seq ?_
  refine (two_wp (Ψ := fun L m₀ u => P₁ P L m₀ i u ∧ Args L u) (two_blk [] spOnly coreArgs_blk)
    fun _ _ _ _ hL _ hc hi => try₂_ok hL hc hi).seq ?_
  refine (two_wp (Ψ := fun L m₀ u => P₃ P L m₀ i u) core_ct fun _ _ _ _ hL hq hc hi =>
    try₃_ok hL hq hc hi.1 hi.2).seq ?_
  refine (two_wp (Ψ := fun L m₀ u => Mid P L m₀ i u) (two_blk [] spOnly goOn_blk)
    fun _ _ _ _ hL hq hc hi => try₄_ok hL hq hc hi).seq ?_
  refine VG.RelCT.ite (fun _ _ ⟨_, _, _, hx, _, _, f₁, f₂⟩ => dec_two hx f₁ f₂) ?_ ?_
  · exact ((two_wp (Ψ := fun _ _ _ => True) rekey_ct fun _ _ _ _ hL hq hc _ =>
      WP.mono (rekey_ok hL hq.1 rfl hq.2 hc) fun _ h => ⟨h.1, trivial⟩).seq
      (two_blk [] spOnly again_blk)).mono (fun _ _ h => h.1) fun _ _ h => h
  · exact (two_blk [] spOnly stop_blk).mono (fun _ _ h => h.1) fun _ _ h => h

/-- One candidate: both runs end, or both go on. -/
theorem tryOne_ct {i : Nat} :
    RelCT isa (Two P fun L m₀ t => LoopInv P L m₀ i t) (cfgOf P).tryOne fun s₁ s₂ =>
      isa.eval (.nonzero .x .x12) s₁ = isa.eval (.nonzero .x .x12) s₂ ∧
        (isa.eval (.nonzero .x .x12) s₁ = some false → Two P (Exit P · · i) s₁ s₂) ∧
        (isa.eval (.nonzero .x .x12) s₁ = some true → Two P (LoopInv P · · (i + 1)) s₁ s₂) := by
  refine (two_wp (Ψ := After P i) tryOne_trace fun _ _ _ _ hL hq hc hi => tryOne_ok hL hq hc hi).mono
    (fun _ _ h => h) fun s₁ s₂ ⟨e, hL, hq, hx, c₁, c₂, f₁, f₂⟩ => ?_
  -- A run that goes on has a later candidate to stop at, so the other cannot have stopped.
  have mixed : ∀ (m m' : Mem) (u u' : State), exitAt P e.1 m = exitAt P e.1 m' → Exit P e.1 m i u →
      LoopInv P e.1 m' (i + 1) u' → False := fun _ m' _ _ hx' hE hI => by
    have hgo : sigI P e.1 m' i = none ∧ i + 1 < P.I.tries := ⟨hI.fails i (by omega), hI.lt⟩
    rw [go_iff (by omega) (fun j hj => hI.fails j (by omega)), ← hx', ← go_iff hE.lt hE.fails] at hgo
    rcases hE.last with h | h
    · exact h hgo.1
    · omega
  rcases f₁ with ⟨d₁, x₁⟩ | ⟨d₁, x₁⟩ <;> rcases f₂ with ⟨d₂, x₂⟩ | ⟨d₂, x₂⟩
  · exact ⟨d₁.trans d₂.symm, fun _ => ⟨e, hL, hq, hx, c₁, c₂, x₁, x₂⟩, fun h => absurd (h.symm.trans d₁) (by decide)⟩
  · exact (mixed _ _ _ _ hx x₁ x₂).elim
  · exact (mixed _ _ _ _ hx.symm x₂ x₁).elim
  · exact ⟨d₁.trans d₂.symm, fun h => absurd (h.symm.trans d₁) (by decide), fun _ => ⟨e, hL, hq, hx, c₁, c₂, x₁, x₂⟩⟩

/-! ## The loop -/

theorem next_n {T n : Nat} (h : T - n + 1 < T) : T - (T - n + 1) < n ∧ T - (T - (T - n + 1)) = T - n + 1 :=
  ⟨by omega, by omega⟩

theorem loop_ct :
    RelCT isa (Two P fun L m₀ t => LoopInv P L m₀ 0 t) (.loop (cfgOf P).tryOne (.nonzero .x .x12))
      (Two P fun L m₀ t => ∃ i, Exit P L m₀ i t) := by
  have h : RelCT isa (Two P fun L m₀ t => LoopInv P L m₀ (P.I.tries - P.I.tries) t)
      (.loop (cfgOf P).tryOne (.nonzero .x .x12)) (Two P fun L m₀ t => ∃ i, Exit P L m₀ i t) :=
    VG.RelCT.loop (M := isa) (fun n => Two P fun L m₀ t => LoopInv P L m₀ (P.I.tries - n) t)
      (fun n => tryOne_ct.mono (fun _ _ h => h) fun _ _ ⟨he, hf, ht⟩ =>
        ⟨he, fun h => (hf h).mono fun _ _ _ hx => ⟨_, hx⟩, fun h => by
          obtain ⟨e, hL, hq, hx, c₁, c₂, f₁, f₂⟩ := ht h
          have hn := next_n f₁.lt
          refine ⟨P.I.tries - (P.I.tries - n + 1), hn.1, e, hL, hq, hx, c₁, c₂, ?_, ?_⟩ <;> rwa [hn.2]⟩)
      P.I.tries
  rwa [Nat.sub_self] at h

/-! ## The frame's body -/

/-- The frame's body, once the arguments are saved. -/
theorem rest_ct :
    RelCT isa (Two P fun _ _ _ => True)
      (.seq (cfgOf P).start
      (.seq ((cfgOf P).rekeyFull 0)
      (.seq ((cfgOf P).rekeyFull 1)
      (.seq (.block (cfgOf P).initCnt)
      (.seq (.loop (cfgOf P).tryOne (.nonzero .x .x12))
        (.block Cfg.wipe))))))
      (Two P fun L m₀ t => ∃ i, Exit P L m₀ i t) := by
  refine (two_wp (Ψ := QB P) start_ct fun _ _ _ _ hL hk hc _ => start_ok hL hk hc).seq ?_
  refine (two_wp (Ψ := QC P) (rekeyFull_ct 0) fun _ _ _ _ hL hk hc h => stageC_ok (P := P) hL hk hc h).seq ?_
  refine (two_wp (Ψ := QD P) (rekeyFull_ct 1) fun _ _ _ _ hL hk hc h => stageD_ok (P := P) hL hk hc h).seq ?_
  refine (two_wp (Ψ := fun L m₀ t => LoopInv P L m₀ 0 t) (two_blk [] spOnly (initCnt_blk _))
    fun _ _ _ _ hL hk hc h => stageE_ok (P := P) hL hk hc h).seq ?_
  refine loop_ct.seq ?_
  exact two_wp (two_blk [] spOnly wipe_blk) fun _ _ _ _ hL hk hc ⟨i, h⟩ =>
    WP.mono (stageG_ok hL hk hc h) fun _ ⟨c, x⟩ => ⟨c, i, x⟩

/-! ## The whole function -/

/-- RFC 6979's result with any hash function, for `P`'s. -/
theorem anyResult_eq (m : Mem) (d dg : Addr) :
    anyResult P.J m d dg P.H.D P.k = some (result P.I m d dg) := by
  simp only [anyResult, Spec.Ecdsa.Rfc6979.Instance.anyResult, ← P.hmacFn, Option.map_some]
  rfl

/-- The precondition, with `P`'s hash function. -/
abbrev preK (P : RfcHash) (s : State) : Prop := (rfcAArch64 P.R.E P.J 512).pre s ∧ selOf s = P.k

/-- Two calls with `P`'s hash function whose public data agree, in the inner frame. -/
def Entered (P : RfcHash) (a b : State) : Prop :=
  ∃ s₁ s₂, preK P s₁ ∧ preK P s₂ ∧ (rfcAArch64 P.R.E P.J 512).pub s₁ s₂ ∧ a = entered s₁ ∧ b = entered s₂

/-- Saving the arguments: the runs have the same layout, and stop at the same candidate. -/
theorem save_ct : RelCT isa (Entered P) (.block Cfg.saveArgs) (Two P fun _ _ _ => True) := by
  intro a b ta tb a' b' ⟨s₁, s₂, ⟨h₁, hs₁⟩, ⟨h₂, hs₂⟩, ⟨hsp, h0, h1, h2, h3, h4, hsel, hres, hsy⟩, ea, eb⟩ e₁ e₂
  subst ea eb
  obtain ⟨_, hc⟩ := save_blk
  obtain ⟨ht, -⟩ := RelCT.taint (A := taint) (P := fun x y => x.sp = y.sp) (Taint.ofRegs [])
    (fun _ _ h => ⟨h, fun r hr => absurd (Taint.mem_ofRegs.mp hr) List.not_mem_nil⟩) hc _ _ _ _ _ _
    (show (entered s₁).sp = (entered s₂).sp by
      show s₁.sp - 16 - BitVec.ofNat 64 frameBytes = s₂.sp - 16 - BitVec.ofNat 64 frameBytes
      rw [hsp]) e₁ e₂
  have hd₁ := dlen_of P h₁ hs₁
  have hd₂ := dlen_of P h₂ hs₂
  obtain ⟨_, u₁, x₁, c₁⟩ := entry_ok h₁ hd₁
  obtain ⟨_, u₂, x₂, c₂⟩ := entry_ok h₂ hd₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  have hl : lay P.H.D P.J.ecdsa.curve.len P.R.E s₁ = lay P.H.D P.J.ecdsa.curve.len P.R.E s₂ := by
    simp only [lay, hsp, h0, h1, h2, h4, hsy, hsel]
  have hr : (result P.I s₁.mem (s₁.gpr .x1) (s₁.gpr .x2)).2 = (result P.I s₂.mem (s₁.gpr .x1) (s₁.gpr .x2)).2 := by
    rw [hd₁, hs₁, anyResult_eq, hd₂, hs₂, anyResult_eq] at hres
    simp only [Option.map_some, Option.getD_some, ← h1, ← h2] at hres
    exact hres
  refine ⟨ht, ⟨lay P.H.D P.J.ecdsa.curve.len P.R.E s₁, s₁.gpr, s₂.gpr, s₁.mem, s₂.mem⟩,
    lay_ok h₁ hd₁, coreOk_lay P s₁ hs₁, congrArg (fun x => if x = 0 then P.I.tries - 1 else x - 1) hr, c₁,
    by rw [hl]; exact c₂, trivial, trivial⟩

/-- Runs with `P`'s hash function whose public data agree have the same
layout, and stop at the same candidate. -/
theorem signK_ct : ConstantTime isa (preK P) (rfcAArch64 P.R.E P.J 512).pub (cfgOf P).sign := by
  refine VG.RelCT.constantTime (Q := fun _ _ => True) (RelCT.pushFrame (R := fun _ _ => True)
    (fun _ _ h => h.2.2.1) (RelCT.alloc (R := fun _ _ => True) ?_))
  refine (save_ct.seq rest_ct).mono ?_ fun _ _ _ => trivial
  rintro _ _ ⟨_, _, ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩, rfl, rfl⟩
  exact ⟨s₁, s₂, h₁, h₂, hp, rfl, rfl⟩

end VG.Proof.Ecdsa.Rfc6979.AArch64

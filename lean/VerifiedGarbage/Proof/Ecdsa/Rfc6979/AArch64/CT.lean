module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Correct
public import VerifiedGarbage.Proof.Framework.AArch64.TaintEraseOff
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Msg
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.ICall
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RelSplit
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Calls
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Correct
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintEraseOff
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Msg
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Reduce
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.ICall
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RelSplit
meta import VerifiedGarbage.Proof.Hmac.Common
meta import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Calls

/-!
# Deterministic ECDSA on AArch64: constant time, up to the number of candidates

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/CT.lean`). Two runs whose public
data agree have the same layout, and stop at the same candidate (`exitAt`,
from the contract's leakage: the number of candidates RFC 6979 tries).
Between the frame's push and pop they are related by `Two`: both satisfy
`Ctx` with that layout (and `Φ`, what the next piece needs). The blocks
address only the stack and the buffers, from registers that agree (the
taint analysis, of the blocks for each size of hash function: `RfcT`, each
curve's `RfcCurve.blkT`); an indirect call reaches, through the table,
whose address the frame holds, the same function in both runs
(`tcall_piece`); each call is of constant-time code whose public data agree
(`RelCT.callEx`, and the streaming calls' `init_rel`, `upd_rel` and
`fin_rel`); and the loop's branch agrees, since in both runs it goes on
after candidate `i` iff `i` is before the candidate it stops at (`go_iff`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64

/-- What each of two runs has, between the frame's push and pop. -/
abbrev Env (P : RfcHash) := Lay P.I.hashLen P.R.E × (Reg → BitVec 64) × (Reg → BitVec 64) × Mem × Mem

/-- What one run's piece needs and gives. -/
abbrev Pr (P : RfcHash) := Lay P.I.hashLen P.R.E → Mem → State → Prop

/-- Nothing. -/
abbrev Tt (P : RfcHash) : Pr P := fun _ _ _ => True

/-- Two runs with the same layout that stop at the same candidate, each
satisfying `Ctx` and `Φ`. -/
def Two (P : RfcHash) (Φ : Pr P) (a b : State) : Prop :=
  ∃ e : Env P, e.1.Ok ∧ CoreOk P e.1 ∧ exitAt P e.1 e.2.2.2.1 = exitAt P e.1 e.2.2.2.2 ∧ Ctx e.1 e.2.1 e.2.2.2.1 a ∧
    Ctx e.1 e.2.2.1 e.2.2.2.2 b ∧ Φ e.1 e.2.2.2.1 a ∧ Φ e.1 e.2.2.2.2 b

variable {P : RfcHash}

theorem Two.mono {Φ Ψ : Pr P} (h : ∀ L m₀ t, Φ L m₀ t → Ψ L m₀ t) {a b : State}
    (ht : Two P Φ a b) : Two P Ψ a b :=
  let ⟨e, hL, hq, hx, c₁, c₂, f₁, f₂⟩ := ht
  ⟨e, hL, hq, hx, c₁, c₂, h _ _ _ f₁, h _ _ _ f₂⟩

/-- Code whose runs leak the same, and which keeps `Ctx` and establishes `Ψ`. -/
theorem two_wp {c : Prog isa} {Φ Ψ : Pr P}
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

theorem sp_two {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 64}
    {m₁ m₂ : Mem} (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) : t₁.sp = t₂.sp :=
  c₁.sp.trans c₂.sp.symm

/-- A block whose addresses depend only on `sp` and the registers `rs`, which agree. -/
theorem two_blk {is : List Instr} {Φ : Pr P} (rs : List Reg)
    (hrs : ∀ (L : Lay P.I.hashLen P.R.E) (t₁ t₂ : State) g₁ g₂ m₁ m₂, Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ →
      Φ L m₁ t₁ → Φ L m₂ t₂ → ∀ r ∈ rs, t₁.gpr r = t₂.gpr r)
    (h : TaintOk rs is) :
    RelCT isa (Two P Φ) (.block is) fun _ _ => True :=
  let ⟨_, h⟩ := h
  RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun _ _ ⟨_, _, _, _, c₁, c₂, f₁, f₂⟩ => ⟨sp_two c₁ c₂, fun r hr =>
      hrs _ _ _ _ _ _ _ c₁ c₂ f₁ f₂ r (Taint.mem_ofRegs.mp hr)⟩) h

theorem spOnly {Φ : Pr P} : ∀ (L : Lay P.I.hashLen P.R.E) (t₁ t₂ : State) g₁ g₂ m₁ m₂,
    Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ → Φ L m₁ t₁ → Φ L m₂ t₂ → ∀ r ∈ ([] : List Reg), t₁.gpr r = t₂.gpr r :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hr => absurd hr List.not_mem_nil

/-- The taint check of a block is that of any block with the same
instructions but for offsets and immediates (`Instr.eraseOff`). -/
theorem taintOk_erase {rs : List Reg} {is is₀ : List Instr} (h : TaintOk rs is₀)
    (he : is.map Instr.eraseOff = is₀.map Instr.eraseOff) : TaintOk rs is :=
  let ⟨hc, hs⟩ := h
  ⟨hc, Taint.isSome_check_of_eraseOff (c := .block is) (c' := Code.eraseOff (.block is₀)) (congrArg Code.block he)
    ((congrArg Option.isSome (Taint.check_eraseOff (Taint.ofRegs rs) (.block is₀) hc)).trans hs)⟩

/-! ## Pieces: related in two runs, and keeping `Ctx` in each -/

/-- Code that, from `Φ`, leaks the same in two runs and gives `Ψ`, keeping
`Ctx`, in each. -/
structure Piece (P : RfcHash) (Φ : Pr P) (c : Prog isa) (Ψ : Pr P) : Prop where
  ct : RelCT isa (Two P Φ) c (Two P Ψ)
  wp : ∀ (L : Lay P.I.hashLen P.R.E) g m₀ (t : State), L.Ok → CoreOk P L → Ctx L g m₀ t → Φ L m₀ t →
    WP isa c t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t'

namespace Piece

variable {Φ Ψ Χ : Pr P} {a b c : Prog isa}

theorem of (hct : RelCT isa (Two P Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay P.I.hashLen P.R.E) g m₀ (t : State), L.Ok → CoreOk P L → Ctx L g m₀ t → Φ L m₀ t →
      WP isa c t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t') : Piece P Φ c Ψ :=
  ⟨two_wp hct hw, hw⟩

theorem seq (h₁ : Piece P Φ a Ψ) (h₂ : Piece P Ψ b Χ) : Piece P Φ (.seq a b) Χ :=
  ⟨h₁.ct.seq h₂.ct, fun L g m₀ t hL hk hc hφ =>
    WP.seq (WP.mono (h₁.wp L g m₀ t hL hk hc hφ) fun _ ⟨c', ψ⟩ => h₂.wp L g m₀ _ hL hk c' ψ)⟩

theorem pre {Φ' : Pr P} (h : Piece P Φ c Ψ) (hp : ∀ L m₀ t, Φ' L m₀ t → Φ L m₀ t) : Piece P Φ' c Ψ :=
  ⟨h.ct.mono (fun _ _ => Two.mono hp) fun _ _ h => h, fun L g m₀ t hL hk hc hφ =>
    h.wp L g m₀ t hL hk hc (hp _ _ _ hφ)⟩

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
    (hw : ∀ (L : Lay P.I.hashLen P.R.E) g m₀ (t : State), L.Ok → CoreOk P L → Ctx L g m₀ t → Φ L m₀ t →
      WP isa (.block is) t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t') : Piece P Φ (.block is) Ψ :=
  Piece.of (two_blk rs hrs ht) hw

/-- A block whose addresses depend only on `sp`. -/
theorem Piece.blkS {is : List Instr} {Φ Ψ : Pr P} (ht : TaintOk [] is)
    (hw : ∀ (L : Lay P.I.hashLen P.R.E) g m₀ (t : State), L.Ok → CoreOk P L → Ctx L g m₀ t → Φ L m₀ t →
      WP isa (.block is) t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t') : Piece P Φ (.block is) Ψ :=
  Piece.blk [] spOnly ht hw

/-- The empty block. -/
theorem Piece.nil {Φ : Pr P} : Piece P Φ (.block []) (Tt P) :=
  Piece.blkS ⟨_, by taint_decide⟩ fun _ _ _ t _ _ hc _ => WP.of_runBlock ⟨t, rfl, hc, trivial⟩

/-! ## The indirect calls -/

/-- What an indirect call of `n` needs of the table in each run: its word
`j` (on entry) is `n`'s address, which is the layout's, and of `f`'s
functions an indirect call reaches `n`'s `c`. -/
def TabFn (P : RfcHash) (j : Nat) (n : String) (c : Prog isa) (ts : List (String × Prog isa)) : Prop :=
  ∀ (L : Lay P.I.hashLen P.R.E) g m₀ (t : State), L.Ok → CoreOk P L → Ctx L g m₀ t →
    m₀.readW (L.tab + BitVec.ofNat 64 (8 * j)) 64 = t.syms n ∧
      ts.find? (fun q => t.syms q.1 == t.syms n) = some (n, c) ∧ t.syms n = L.fa n

theorem tfn_init : TabFn P 0 P.H.stream.initN P.H.stream.initC P.f.init := fun L _ _ _ _ hk hc => by
  have hok := hc.tabOk; have htm := hc.tabMem; have hf := hc.fsy
  rw [hk.tabL.1, hk.tabL.2.1] at hok; rw [hk.tabL.1] at htm hf
  exact ⟨htm.1, hok.i, hf _ (by simp)⟩

theorem tfn_upd : TabFn P 1 P.H.stream.updN P.H.stream.updC P.f.upd := fun L _ _ _ _ hk hc => by
  have hok := hc.tabOk; have htm := hc.tabMem; have hf := hc.fsy
  rw [hk.tabL.1, hk.tabL.2.1] at hok; rw [hk.tabL.1] at htm hf
  exact ⟨htm.2.1, hok.u, hf _ (by simp)⟩

theorem tfn_fin : TabFn P 2 P.H.stream.finN P.H.stream.finC P.f.fin := fun L _ _ _ _ hk hc => by
  have hok := hc.tabOk; have htm := hc.tabMem; have hf := hc.fsy
  rw [hk.tabL.1, hk.tabL.2.1] at hok; rw [hk.tabL.1] at htm hf
  exact ⟨htm.2.2, hok.f, hf _ (by simp)⟩

/-- What only `x16` changing keeps. -/
def R16 (Φ : Pr P) : Prop :=
  ∀ L m₀ (t u : State), Φ L m₀ t → (∀ r, r ≠ .x16 → u.gpr r = t.gpr r) → u.mem = t.mem → u.syms = t.syms →
    Φ L m₀ u

theorem tblk1_taint : TaintOk [] [.ldrSp .x16 fTab] := ⟨_, by taint_decide⟩

theorem tblk2_taint (x : Nat) : TaintOk [.x16] [.ldr .x .x16 .x16 x] :=
  taintOk_erase (is₀ := [.ldr .x .x16 .x16 0]) ⟨_, by taint_decide⟩ rfl

/-- The indirect call of the table's function `j`: in both runs of the same
function, `n`'s (the table's word `j` holds the layout's address of `n`). -/
theorem tcall_piece {Φ Ψ : Pr P} {j : Nat} (hj : 8 * j + 8 ≤ 40) {n : String} {c : Prog isa}
    {ts : List (String × Prog isa)} (hn : TabFn P j n c ts) (hΦ : R16 Φ) (hcall : Piece P Φ (.call n c) Ψ) :
    Piece P Φ (Cfg.tcall j ts) Ψ := by
  refine ⟨?_, fun L g m₀ t hL hk hc hφ => ?_⟩
  · unfold Cfg.tcall
    have s₁ : Piece P Φ (.block [.ldrSp .x16 fTab]) fun L m₀ u => Φ L m₀ u ∧ u.gpr .x16 = L.tab :=
      Piece.blkS tblk1_taint fun L g m₀ t hL hk hc hφ =>
        WP.mono_syms (tblk1_ok hL hc) fun u h hs => ⟨h.ctx, hΦ _ _ _ _ hφ h.keep h.mem hs, h.val⟩
    have s₂ : Piece P (fun L m₀ u => Φ L m₀ u ∧ u.gpr .x16 = L.tab) (.block [.ldr .x .x16 .x16 (8 * j)])
        fun L m₀ u => Φ L m₀ u ∧ u.gpr .x16 = L.fa n ∧ u.syms n = L.fa n ∧
          ts.find? (fun q => u.syms q.1 == u.syms n) = some (n, c) :=
      Piece.blk [.x16] (fun _ _ _ _ _ _ _ _ _ f₁ f₂ r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact f₁.2.trans f₂.2.symm) (tblk2_taint _)
        fun L g m₀ t hL hk hc ⟨hφ, h16⟩ => WP.mono_syms (tblk2_ok hL hc h16 hj) fun u h hs => by
          obtain ⟨hw, hf, hfa⟩ := hn L g m₀ t hL hk hc
          exact ⟨h.ctx, hΦ _ _ _ _ hφ h.keep h.mem hs, by rw [h.val, hw, hfa], by rw [hs, hfa],
            by rw [hs]; exact hf⟩
    refine s₁.ct.seq (s₂.ct.seq ?_)
    cases ts with
    | nil => exact RelCT.of_false fun _ _ ⟨_, _, _, _, _, _, f₁, _⟩ => by simp at f₁
    | cons q ts =>
      exact RelCT.icalls_of_call (hcall.ct.mono (fun _ _ => Two.mono fun _ _ _ h => h.1) fun _ _ h => h)
        fun s₁ s₂ ⟨e, _, _, _, _, _, f₁, f₂⟩ => ⟨e.1.fa n, by simp only [icall, f₁.2.1],
          by simp only [icall, f₂.2.1],
          by show (q :: ts).find? (fun p => s₁.syms p.1 == e.1.fa n) = _; rw [← f₁.2.2.1]; exact f₁.2.2.2,
          by show (q :: ts).find? (fun p => s₂.syms p.1 == e.1.fa n) = _; rw [← f₂.2.2.1]; exact f₂.2.2.2, rfl⟩
  · obtain ⟨hw, hf, -⟩ := hn L g m₀ t hL hk hc
    exact tcall_ok hL hc hj hw hf fun t' hc' hm hr hs => hcall.wp L g m₀ t' hL hk hc' (hΦ _ _ _ _ hφ hr hm hs)

/-! ## The streaming calls -/

/-- A call related in two runs with the same layout. -/
theorem two_call {Φ : Pr P} {n : String} {c : Prog isa}
    (h : ∀ L : Lay P.I.hashLen P.R.E, RelCT isa (fun s₁ s₂ => ∃ g₁ g₂ m₁ m₂, L.Ok ∧ CoreOk P L ∧ Ctx L g₁ m₁ s₁ ∧
      Ctx L g₂ m₂ s₂ ∧ Φ L m₁ s₁ ∧ Φ L m₂ s₂) (.call n c) fun _ _ => True) :
    RelCT isa (Two P Φ) (.call n c) fun _ _ => True :=
  (RelCT.exists_ h).mono (fun _ _ ⟨⟨L, g₁, g₂, m₁, m₂⟩, hL, hk, _, c₁, c₂, f₁, f₂⟩ =>
    ⟨L, g₁, g₂, m₁, m₂, hL, hk, c₁, c₂, f₁, f₂⟩) fun _ _ h => h

/-- `init`'s argument: the state at `scratch + o`. -/
def IA (P : RfcHash) (o : Nat) : Pr P := fun L _ u => u.gpr .x0 = L.scr + BitVec.ofNat 64 o

theorem init_piece {o : Nat} (ho : o + 192 ≤ 384) :
    Piece P (IA P o) (.call P.H.stream.initN P.H.stream.initC) (Tt P) :=
  Piece.of (two_call fun L => Proof.Pbkdf2.Md.AArch64.Calls.init_rel P.ok.stream (st := L.scr + BitVec.ofNat 64 o)
      fun _ _ ⟨_, _, _, _, _, _, c₁, c₂, d₁, d₂⟩ =>
    have cov : ∀ {g m₀} {u : State}, Ctx L g m₀ u → Covers [⟨L.scr + BitVec.ofNat 64 o, P.H.stream.S⟩] u.wr :=
      fun hc => hc.coversW fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨L.SCR, by simp, within_off _ (by anums)⟩
    ⟨d₁, d₂, cov c₁, cov c₂, sp_two c₁ c₂⟩)
    fun _ _ _ _ hL _ hc hd => WP.mono (initRaw_ok hL hc ho hd) fun _ h => ⟨h.1, trivial⟩

/-- `update`'s arguments: the state at `scratch + o` holding `cnt` bytes,
the `len` bytes at `da`, and the working space. -/
def UA (P : RfcHash) (o cnt : Nat) (da : Lay P.I.hashLen P.R.E → Addr) (len : Nat) : Pr P := fun L _ u =>
  u.gpr .x0 = L.scr + BitVec.ofNat 64 o ∧ u.gpr .x1 = BitVec.ofNat 64 cnt ∧ u.gpr .x2 = da L ∧
    u.gpr .x3 = BitVec.ofNat 64 len ∧ u.gpr .x4 = L.scr + BitVec.ofNat 64 384

theorem upd_piece {o cnt : Nat} (ho : o + 192 ≤ 384) {da : Lay P.I.hashLen P.R.E → Addr} {len : Nat}
    (hd : ∀ L : Lay P.I.hashLen P.R.E, L.Ok → UpdData P L o (da L) len) (hlen : len < 2 ^ 16) :
    Piece P (UA P o cnt da len) (.call P.H.stream.updN P.H.stream.updC) (Tt P) :=
  Piece.of (two_call fun L => Proof.Pbkdf2.Md.AArch64.Calls.upd_rel P.ok.stream fun _ _ ⟨_, _, _, _, hL, _, c₁, c₂,
      ⟨d₁, s₁, x₁, k₁, r₁⟩, ⟨d₂, s₂, x₂, k₂, r₂⟩⟩ =>
    ⟨updArgsOf hL c₁ ho (hd L hL) hlen d₁ x₁ k₁ r₁, updArgsOf hL c₂ ho (hd L hL) hlen d₂ x₂ k₂ r₂, s₁.trans s₂.symm,
      sp_two c₁ c₂⟩)
    fun _ _ _ _ hL _ hc ⟨d, s, x, k, r⟩ =>
      WP.mono (updRaw_ok hL hc ho (updArgsOf hL hc ho (hd _ hL) hlen d x k r) s) fun _ h => ⟨h.1, trivial⟩

/-- `finalize`'s arguments: the state at `scratch + o` holding `cnt` bytes,
the output at `scratch + sTmp`, and the working space. -/
def FA (P : RfcHash) (o cnt : Nat) : Pr P := fun L _ u =>
  u.gpr .x0 = L.scr + BitVec.ofNat 64 o ∧ u.gpr .x1 = BitVec.ofNat 64 cnt ∧
    u.gpr .x2 = L.scr + BitVec.ofNat 64 1920 ∧ u.gpr .x3 = L.scr + BitVec.ofNat 64 384

theorem fin_piece {o cnt : Nat} (ho : o + 192 ≤ 384) (hcnt : cnt < 2 ^ 16) :
    Piece P (FA P o cnt) (.call P.H.stream.finN P.H.stream.finC) (Tt P) :=
  Piece.of (two_call fun _ => Proof.Pbkdf2.Md.AArch64.Calls.fin_rel P.ok.stream fun _ _ ⟨_, _, _, _, hL, _, c₁, c₂,
      ⟨d₁, s₁, x₁, k₁⟩, ⟨d₂, s₂, x₂, k₂⟩⟩ =>
    ⟨finArgsOf (P := P) hL c₁ ho d₁ x₁ k₁, finArgsOf (P := P) hL c₂ ho d₂ x₂ k₂, s₁.trans s₂.symm, sp_two c₁ c₂⟩)
    fun _ _ _ _ hL _ hc ⟨d, s, x, k⟩ =>
      WP.mono (finRaw_ok hL hc ho (finArgsOf (P := P) hL hc ho d x k) hcnt s) fun _ h => ⟨h.1, trivial⟩

theorem r16_ia {o : Nat} : R16 (IA P o) := fun _ _ _ _ h hr _ _ => (hr _ (by decide)).trans h

theorem r16_ua {o cnt : Nat} {da : Lay P.I.hashLen P.R.E → Addr} {len : Nat} : R16 (UA P o cnt da len) :=
  fun _ _ _ _ ⟨d, s, x, k, r⟩ hr _ _ => ⟨(hr _ (by decide)).trans d, (hr _ (by decide)).trans s,
    (hr _ (by decide)).trans x, (hr _ (by decide)).trans k, (hr _ (by decide)).trans r⟩

theorem r16_fa {o cnt : Nat} : R16 (FA P o cnt) :=
  fun _ _ _ _ ⟨d, s, x, k⟩ hr _ _ => ⟨(hr _ (by decide)).trans d, (hr _ (by decide)).trans s,
    (hr _ (by decide)).trans x, (hr _ (by decide)).trans k⟩

theorem scr0_taint : TaintOk [] (Cfg.scr .x0 0) := ⟨_, by taint_decide⟩

theorem scr_taint (a : Nat) : TaintOk [] (Cfg.scr .x0 a) := taintOk_erase scr0_taint rfl

/-- `init` of the state at `scratch + o`, through the table. -/
theorem initCall_piece {Φ : Pr P} {o : Nat} (ho : o + 192 ≤ 384) : Piece P Φ ((cfgOf P).initCall o) (Tt P) :=
  (Piece.blkS (Ψ := IA P o) (scr_taint o) fun _ _ _ _ hL _ hc _ =>
    WP.mono (scr_ok hL hc (d := .x0) (by decide) (a := o) (by omega)) fun _ h => ⟨h.ctx, h.val⟩).seq
    (tcall_piece (by decide) tfn_init r16_ia (init_piece ho))

/-- The data block of `update`: the address of the data in `x2`. -/
def DataA (P : RfcHash) (dataA : List Instr) (da : Lay P.I.hashLen P.R.E → Addr) : Prop :=
  ∀ (L : Lay P.I.hashLen P.R.E) g m₀ (u : State), L.Ok → Ctx L g m₀ u →
    WP isa (.block dataA) u (Upd L g m₀ u .x2 (da L))

theorem updArgs_taint {o cnt : Nat} {dataA : List Instr} {len : Nat} (ht : TaintOk [] (Cfg.updArgs 0 0 dataA 0)) :
    TaintOk [] (Cfg.updArgs o cnt dataA len) :=
  taintOk_erase ht (by simp only [Cfg.updArgs, Cfg.scr, List.map_append]; rfl)

/-- `update` of the state at `scratch + o`, holding `cnt` bytes, with `len`
bytes at `da`, through the table. -/
theorem updCall_piece {Φ : Pr P} {o cnt : Nat} (ho : o + 192 ≤ 384) {dataA : List Instr}
    {da : Lay P.I.hashLen P.R.E → Addr} {len : Nat} (hdA : DataA P dataA da)
    (hd : ∀ L : Lay P.I.hashLen P.R.E, L.Ok → UpdData P L o (da L) len) (ht : TaintOk [] (Cfg.updArgs 0 0 dataA 0))
    (hcnt : cnt < 2 ^ 16) (hlen : len < 2 ^ 16) :
    Piece P Φ ((cfgOf P).updCall o cnt dataA len) (Tt P) :=
  (Piece.blkS (Ψ := UA P o cnt da len) (updArgs_taint ht) fun L g m₀ _ hL _ hc _ =>
    WP.mono (updArgs_ok hL hc (o := o) (by omega) (fun u hu => hdA L g m₀ u hL hu) hcnt hlen)
      fun _ ⟨c, _, d, s, x, k, r⟩ => ⟨c, d, s, x, k, r⟩).seq
    (tcall_piece (by decide) tfn_upd r16_ua (upd_piece ho hd hlen))

theorem finArgs_taint (o cnt : Nat) : TaintOk [] (Cfg.finArgs o cnt) :=
  taintOk_erase (is₀ := Cfg.finArgs 0 0) ⟨_, by taint_decide⟩
    (by simp only [Cfg.finArgs, Cfg.scr, List.map_append]; rfl)

/-- `finalize` of the state at `scratch + o`, holding `cnt` bytes, through the table. -/
theorem finCall_piece {Φ : Pr P} {o cnt : Nat} (ho : o + 192 ≤ 384) (hcnt : cnt < 2 ^ 16) :
    Piece P Φ ((cfgOf P).finCall o cnt) (Tt P) :=
  (Piece.blkS (Ψ := FA P o cnt) (finArgs_taint o cnt) fun _ _ _ _ hL _ hc _ =>
    WP.mono (finArgs_ok hL hc ho hcnt) fun _ ⟨c, _, d, s, x, k⟩ => ⟨c, d, s, x, k⟩).seq
    (tcall_piece (by decide) tfn_fin r16_fa (fin_piece ho hcnt))

/-! ## Blocks from `scratch`'s pointer -/

/-- `scratch` in `x9`. -/
def ScrIn (P : RfcHash) : Pr P := fun L _ u => u.gpr .x9 = L.scr

theorem scrPtr_piece {Φ : Pr P} : Piece P Φ (.block Cfg.scrPtr) (ScrIn P) :=
  Piece.blkS ⟨_, by taint_decide⟩ fun _ _ _ _ hL _ hc _ => WP.mono (scrPtr_ok hL hc) fun _ h => ⟨h.ctx, h.val⟩

/-- A block that loads `scratch` into `x9`, then addresses memory only from
`sp` and `x9`. -/
theorem Piece.scrBlk {is : List Instr} {Φ Ψ : Pr P} (ht : TaintOk [.x9] is)
    (hw : ∀ (L : Lay P.I.hashLen P.R.E) g m₀ (t : State), L.Ok → CoreOk P L → Ctx L g m₀ t → Φ L m₀ t →
      WP isa (.block (Cfg.scrPtr ++ is)) t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t') :
    Piece P Φ (.block (Cfg.scrPtr ++ is)) Ψ :=
  Piece.of (RelCT.block_append (scrPtr_piece.ct.seq (two_blk [.x9] (fun _ _ _ _ _ _ _ _ _ f₁ f₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact f₁.trans f₂.symm) ht))) hw

/-! ## HMAC -/

/-- The blocks of the curve and the hash function's sizes. -/
theorem rT (P : RfcHash) : RfcT (cfgS P.R.E P.R.hHigh P.R.sh P.H.D P.H.P.B) := P.R.blkT _ _ P.hDB

/-- `K₀ ⊕ c` at `scratch + sPad`. -/
theorem padBlk_piece {Φ : Pr P} (x : BitVec 32) (c : Byte) (hx : (movzkV x).setWidth 32 = c ++ c ++ c ++ c) :
    Piece P Φ (.block ((cfgOf P).padBlk x)) (Tt P) :=
  Piece.scrBlk (is := (cfgOf P).padBody x) (taintOk_erase (by exact (rT P).pad)
      (by simp only [Cfg.padBody, List.map_append]; rfl))
    fun _ _ _ _ hL _ hc _ => WP.mono (padBlk_ok hL hc x c hx) fun _ h => ⟨h.1, trivial⟩

theorem updScr_taint (a : Nat) : TaintOk [] (Cfg.updArgs 0 0 (Cfg.scr .x2 a) 0) :=
  taintOk_erase (is₀ := Cfg.updArgs 0 0 (Cfg.scr .x2 0) 0) ⟨_, by taint_decide⟩
    (by simp only [Cfg.updArgs, Cfg.scr, List.map_append]; rfl)

theorem updV_taint : TaintOk [] (Cfg.updArgs 0 0 (Cfg.fr .x2 fV) 0) := ⟨_, by taint_decide⟩

/-- Data at `scratch + a`. -/
theorem scrDA (a : Nat) (ha : a < 4096) : DataA P (Cfg.scr .x2 a) fun L => L.scr + BitVec.ofNat 64 a :=
  fun _ _ _ _ hL hu => scr_ok hL hu (d := .x2) (by decide) ha

/-- `V`, in the frame. -/
theorem vDA : DataA P (Cfg.fr .x2 fV) fun L => L.B + BitVec.ofNat 64 (16 + 64) :=
  fun _ _ _ _ hL hu => fr_ok hL hu (d := .x2) (by decide) (o := 64) (by decide)

theorem hB16 (P : RfcHash) : P.H.P.B ≤ 128 ∧ P.H.D ≤ 64 := by anums

/-- `hinit`: each state set by `init` and updated with its padded key. -/
theorem hinit_piece {Φ : Pr P} : Piece P Φ (cfgOf P).hinit (Tt P) := by
  have hb : (cfgOf P).B < 2 ^ 16 := by show P.H.P.B < 2 ^ 16; have := hB16 P; omega
  unfold Cfg.hinit
  exact (initCall_piece (by decide)).seq ((initCall_piece (by decide)).seq ((padBlk_piece _ _ movzk_ipad).seq
    ((updCall_piece (by decide) (scrDA 1792 (by decide)) (fun _ hL => padData hL (by decide)) (updScr_taint _)
      (by decide) hb).seq ((padBlk_piece _ _ movzk_opad).seq
    (updCall_piece (by decide) (scrDA 1792 (by decide)) (fun _ hL => padData hL (by decide)) (updScr_taint _)
      (by decide) hb)))))

/-- `hupd`: the inner state updated with the data. -/
theorem hupd_piece {Φ : Pr P} {dataA : List Instr} {da : Lay P.I.hashLen P.R.E → Addr} {len : Nat}
    (hdA : DataA P dataA da) (hd : ∀ L : Lay P.I.hashLen P.R.E, L.Ok → DataOk L (da L) len)
    (ht : TaintOk [] (Cfg.updArgs 0 0 dataA 0)) (hlen : len ≤ 256) :
    Piece P Φ ((cfgOf P).hupd dataA len) (Tt P) := by
  have := hB16 P
  unfold Cfg.hupd
  exact updCall_piece (by decide) hdA (fun L hL => DataOk.upd hL (hd L hL)) ht
    (by show P.H.P.B < 2 ^ 16; omega) (by omega)

theorem hfinCopy_taint (dst : Nat) : TaintOk [.x9] ((cfgOf P).copyOut dst) :=
  taintOk_erase (by exact (rT P).hfinCopy) (by simp only [Cfg.copyOut, List.map_append]; rfl)

/-- The inner digest, as `update` reads it at `scratch + sTmp`. -/
theorem tmpData {L : Lay P.I.hashLen P.R.E} (hL : L.Ok) : UpdData P L 192 (L.scr + BitVec.ofNat 64 1920) P.H.D :=
  ⟨⟨L.SCR, by simp, within_off _ (by anums)⟩, Offset.disjoint _ (by anums) (by anums) (by anums),
    Offset.disjoint _ (by anums) (by anums) (by anums), hL.low_scr (by anums)⟩

/-- `hfin`: the MAC, for `len` bytes of data, to the frame at `dst`. -/
theorem hfin_piece {Φ : Pr P} {len dst : Nat} (hlen : len ≤ 256) (hdst : dst + P.H.D ≤ 168) :
    Piece P Φ ((cfgOf P).hfin len dst) (Tt P) := by
  have := hB16 P
  unfold Cfg.hfin
  exact (finCall_piece (by decide) (by show P.H.P.B + len < 2 ^ 16; omega)).seq
    ((updCall_piece (by decide) (scrDA 1920 (by decide))
      (fun _ hL => tmpData hL) (updScr_taint _)
      (by show P.H.P.B < 2 ^ 16; omega) (by show P.H.D < 2 ^ 16; omega)).seq
    ((finCall_piece (by decide) (by show P.H.P.B + P.H.D < 2 ^ 16; omega)).seq
    (Piece.scrBlk (hfinCopy_taint dst) fun _ _ _ _ hL _ hc _ =>
      WP.mono (copyOut_ok hL hc hdst) fun _ h => ⟨h.1, trivial⟩)))

/-- `HMAC_K(data)`. -/
theorem hmac_piece {Φ : Pr P} {dataA : List Instr} {da : Lay P.I.hashLen P.R.E → Addr} {len dst : Nat}
    (hdA : DataA P dataA da) (hd : ∀ L : Lay P.I.hashLen P.R.E, L.Ok → DataOk L (da L) len)
    (ht : TaintOk [] (Cfg.updArgs 0 0 dataA 0)) (hlen : len ≤ 256) (hdst : dst + P.H.D ≤ 168) :
    Piece P Φ ((cfgOf P).hmac dataA len dst) (Tt P) :=
  hinit_piece.seq ((hupd_piece hdA hd ht hlen).seq (hfin_piece hlen hdst))

/-- `V = HMAC_K(V)`. -/
theorem hmacV_piece {Φ : Pr P} : Piece P Φ (cfgOf P).hmacV (Tt P) :=
  hmac_piece (len := P.H.D) (dst := 64) vDA (fun _ _ => .inl ⟨80, rfl, by omega, by anums⟩) updV_taint (by anums)
    (by anums)

/-- `K = HMAC_K(m)`, for the message of `len` bytes at `scratch + 2256`. -/
theorem hmacK_piece {Φ : Pr P} {len : Nat} (hlen : len ≤ 256) :
    Piece P Φ ((cfgOf P).hmac (Cfg.scr .x2 sMsg) len fK) (Tt P) :=
  hmac_piece (scrDA 2256 (by decide)) (fun _ _ => .inr ⟨2256, rfl, by omega, by omega⟩) (updScr_taint _) hlen
    (by show 0 + P.H.D ≤ 168; anums)

/-! ## `K` and `V` from a message -/

/-- `scratch` in `x9`, `d` in `x10` and the frame in `x15`. -/
def PtrsIn (P : RfcHash) : Pr P := fun L _ u =>
  u.gpr .x9 = L.scr ∧ u.gpr .x10 = L.d ∧ u.gpr .x15 = L.B + BitVec.ofNat 64 16

theorem msgPtrs_piece {Φ : Pr P} : Piece P Φ (.block Cfg.msgPtrs) (PtrsIn P) :=
  Piece.blkS ⟨_, by taint_decide⟩ fun _ _ _ _ hL _ hc _ =>
    WP.mono (ptrs_ok hL hc) fun _ ⟨c, _, h9, h10, h15⟩ => ⟨c, h9, h10, h15⟩

/-- The message `V ‖ b (‖ d ‖ h)` at `scratch + sMsg`. -/
theorem msg_piece {b : Nat} {full : Bool} {ho : Nat} (hho : full = true → ho = P.hB - 16)
    (ht : TaintOk [.x9, .x10, .x15] (Cfg.msg P.w P.Q P.H.D b full ho)) :
    Piece P (PtrsIn P) (.block (Cfg.msg P.w P.Q P.H.D b full ho)) (Tt P) :=
  Piece.blk [.x9, .x10, .x15] (fun _ _ _ _ _ _ _ _ _ f₁ f₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact f₁.1.trans f₂.1.symm
      · exact f₁.2.1.trans f₂.2.1.symm
      · exact f₁.2.2.trans f₂.2.2.symm) ht
    fun _ _ _ _ hL hk hc hp => WP.mono (msg_ok hL hc hp.1 hp.2.1 hp.2.2 b full (D := P.H.D) (w := P.w) (Q := P.Q)
      (ho := ho) (by anums) (by anums) (fun hf => by
        have := hB_fit (hok_of hk)
        have h8 : (P.hB - 16) % 8 = 0 := by simp only [RfcHash.hB]; split <;> decide
        rw [hho hf]; exact ⟨by anums, by anums, this, h8, (hok_of hk).1⟩))
      fun _ h => ⟨h.1, trivial⟩

theorem msgF_taint (b : Nat) : TaintOk [.x9, .x10, .x15] (Cfg.msg P.w P.Q P.H.D b true (cfgOf P).fHo) :=
  taintOk_erase (by exact (rT P).msgF) (by simp only [Cfg.msg, List.map_append]; rfl)

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)`. -/
theorem rekeyFull_piece {Φ : Pr P} (b : Nat) : Piece P Φ ((cfgOf P).rekeyFull b) (Tt P) := by
  have hlen : P.H.D + 2 * P.Q + 1 ≤ 256 := by anums
  unfold Cfg.rekeyFull
  exact msgPtrs_piece.seq ((msg_piece (fun _ => fHo_eq P) (msgF_taint b)).seq
    ((hmacK_piece hlen).seq hmacV_piece))

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)`. -/
theorem rekey_piece {Φ : Pr P} : Piece P Φ (cfgOf P).rekey (Tt P) := by
  have hlen : P.H.D + 1 ≤ 256 := by anums
  unfold Cfg.rekey
  exact msgPtrs_piece.seq ((msg_piece (fun h => absurd h (by decide)) (by exact (rT P).msgN)).seq
    ((hmacK_piece hlen).seq hmacV_piece))

/-! ## The candidate -/

theorem ce_sp_two {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 64}
    {m₁ m₂ : Mem} (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) (rd₁ wr₁ rd₂ wr₂ : List Region) :
    (t₁.callEntry.withRegions rd₁ wr₁).sp = (t₂.callEntry.withRegions rd₂ wr₂).sp := by
  rw [State.withRegions_sp, State.withRegions_sp, State.callEntry_sp, State.callEntry_sp, sp_two c₁ c₂]

theorem ce_two {t₁ t₂ : State} {r : Reg} (hr : r ∉ linkRegs) {x : BitVec 64} (h₁ : t₁.gpr r = x)
    (h₂ : t₂.gpr r = x) (rd₁ wr₁ rd₂ wr₂ : List Region) :
    (t₁.callEntry.withRegions rd₁ wr₁).gpr r = (t₂.callEntry.withRegions rd₂ wr₂).gpr r := by
  rw [ce_gpr _ _ _ hr, ce_gpr _ _ _ hr, h₁, h₂]

/-- `V`'s `D` bytes to `T + k D`. -/
theorem keepV_piece {Φ : Pr P} (hw : P.wide = true) {k : Nat} (hkb : k * P.H.D + P.H.D ≤ 128) :
    Piece P Φ (.block ((cfgOf P).keepV k)) (Tt P) :=
  Piece.blkS (taintOk_erase (by exact (rT P).keepV) (by simp only [Cfg.keepV, List.map_append]; rfl))
    fun _ _ _ _ hL hk hc _ => WP.mono (keepV_ok hL hk.e_eq hw hc hkb) fun _ h => ⟨h.1, trivial⟩

/-- The first `k` `V`s of the candidate. -/
theorem candW_piece {Φ : Pr P} (hw : P.wide = true) : ∀ k, k * P.H.D ≤ 128 →
    Piece P Φ ((cfgOf P).candW k) (Tt P)
  | 0, _ => by rw [Cfg.candW]; exact Piece.nil
  | k + 1, hk => by
    have hk' : k * P.H.D + P.H.D ≤ 128 := by rw [Nat.succ_mul] at hk; exact hk
    rw [Cfg.candW]
    exact (candW_piece hw k (by omega)).seq (hmacV_piece.seq (keepV_piece hw hk'))

/-- `scratch` in `x0`. -/
def Scr0 (P : RfcHash) : Pr P := fun L _ u => u.gpr .x0 = L.scr

/-- If `sh ≠ 0`: `T`'s first `Q` bytes shifted right by `sh` bits. -/
theorem candTop_piece {Φ : Pr P} : Piece P Φ (cfgOf P).candTop (Tt P) := by
  by_cases hsh : P.R.sh = 0
  · have e : (cfgOf P).candTop = .block [] := by
      simp only [Cfg.candTop, show (cfgOf P).sh = 0 from hsh, ite_true]
    rw [e]; exact Piece.nil
  · refine Piece.of ?_ fun L _ _ _ hL hk hc _ => WP.mono (candTop_ok hL hk.e_eq hsh hc) fun _ h => ⟨h.1, trivial⟩
    have e : (cfgOf P).candTop = (cfgOf P).conv fT (cfgOf P).sh := by
      simp only [Cfg.candTop, show (cfgOf P).sh = P.R.sh from rfl, hsh, ite_false]
    rw [e]
    exact (two_wp (Ψ := Scr0 P) (two_blk [] spOnly ⟨_, by taint_decide⟩) fun _ _ _ _ hL _ hc _ =>
      WP.mono (ldScr_ok hL hc) fun _ h => ⟨h.ctx, h.val⟩).seq (two_blk [.x0] (fun _ _ _ _ _ _ _ _ _ f₁ f₂ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact f₁.trans f₂.symm) (by exact (rT P).candTop hsh))

/-- The candidate: its calls and blocks leak the same in both runs. -/
theorem cand_piece {Φ : Pr P} : Piece P Φ (cfgOf P).cand (Tt P) := by
  cases hw : P.wide
  · simp only [Cfg.cand, cfgOf_wide, hw, Bool.false_eq_true, ite_false]
    exact hmacV_piece
  · simp only [Cfg.cand, cfgOf_wide, hw, ite_true]
    exact (candW_piece hw _ (m_facts P hw).2).seq candTop_piece

/-- `core`, with arguments that agree. -/
theorem core_ct {i : Nat} :
    RelCT isa (Two P fun L m₀ u => P₁ P L m₀ i u ∧ Args P L u) (.call (cfgOf P).coreN (cfgOf P).coreC)
      fun _ _ => True :=
  AArch64.RelCT.callEx P.R.coreX P.R.coreCT
    fun _ _ ⟨⟨L, _, _, _, _⟩, hL, hk, _, c₁, c₂, ⟨_, a₁⟩, ⟨_, a₂⟩⟩ =>
    ⟨coreRd P L, coreWr P L, coreRd P L, coreWr P L, core_pre hL hk c₁ a₁.x0 a₁.x1 a₁.x2 a₁.x3 a₁.x4,
      core_pre hL hk c₂ a₂.x0 a₂.x1 a₂.x2 a₂.x3 a₂.x4,
      ⟨ce_two (by decide) a₁.x0 a₂.x0 _ _ _ _, ce_two (by decide) a₁.x1 a₂.x1 _ _ _ _,
        ce_two (by decide) a₁.x2 a₂.x2 _ _ _ _, ce_two (by decide) a₁.x3 a₂.x3 _ _ _ _,
        ce_two (by decide) a₁.x4 a₂.x4 _ _ _ _, ce_sp_two c₁ c₂ _ _ _ _, c₁.sy.trans c₂.sy.symm⟩,
      core_covers hL hk c₁, core_coversW hk.1 c₁, core_covers hL hk c₂, core_coversW hk.1 c₂⟩

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
  refine (two_wp (Ψ := fun L m₀ u => P₁ P L m₀ i u) ((cand_piece (Φ := Tt P)).rel fun _ _ _ _ => trivial)
    fun _ _ _ _ hL hk hc hi => try₁_ok hL hk hc hi).seq ?_
  refine (two_wp (Ψ := fun L m₀ u => P₁ P L m₀ i u ∧ Args P L u) (two_blk [] spOnly (by exact (rT P).coreArgs))
    fun _ _ _ _ hL hk hc hi => try₂_ok hL hk hc hi).seq ?_
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
    have hgo : sigI P e.1 m' i = none ∧ i + 1 < P.I.tries := ⟨hI.fails i (by omega), hI.lt⟩
    rw [go_iff (by omega) (fun j hj => hI.fails j (by omega)), ← hx', ← go_iff hE.lt hE.fails] at hgo
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
  ⟨by omega, by omega⟩

theorem loop_ct :
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

/-- The count's initial store, for any count: the analysis does not read
immediates (`Instr.eraseOff`), so it is that of one count's. -/
theorem initCnt_blk (c : Cfg) : TaintOk [] c.initCnt :=
  taintOk_erase (is₀ := [.movz .x .x9 0 0, .addSp .x15 0, .str .x .x9 .x15 fCnt]) ⟨_, by taint_decide⟩ rfl

/-- `digest` in `x1`, and, if the hash is shorter than the scalars, `scratch` in `x0`. -/
def DgIn (P : RfcHash) : Pr P := fun L _ u => u.gpr .x1 = L.dg ∧ (P.wide = true → u.gpr .x0 = L.scr)

/-- Unless the hash is shorter, `bits2octets` is the curve's. -/
theorem reduce_eq (hw : P.wide = false) : (cfgOf P).reduce = (cfgC P.R.E P.R.hHigh).reduce := by
  have h₁ : (cfgC P.R.E P.R.hHigh).wide = false := by
    show decide (64 < P.Q) = false
    have := (P.sizesA hw).2.2
    simp only [decide_eq_false_iff_not]; anums
  have h₂ : (cfgOf P).fHo = (cfgC P.R.E P.R.hHigh).fHo := by
    simp only [Cfg.fHo, cfgOf_wide, hw, h₁]; rfl
  have h₃ : (cfgOf P).selWord = (cfgC P.R.E P.R.hHigh).selWord := funext fun j => by
    simp only [Cfg.selWord, h₂]; rfl
  have h₄ : (cfgOf P).subWord = (cfgC P.R.E P.R.hHigh).subWord := rfl
  simp only [Cfg.reduce, h₃, h₄]
  rfl

theorem prep_ct : RelCT isa (Two P (DgIn P)) (.block (cfgOf P).prep) fun _ _ => True := by
  cases hw : P.wide
  · have e : (cfgOf P).prep = (cfgC P.R.E P.R.hHigh).reduce ++ Cfg.initKV := by
      simp only [Cfg.prep, cfgOf_wide, hw, Bool.false_eq_true, ite_false, reduce_eq hw]
    rw [e]
    exact two_blk [.x1] (fun _ _ _ _ _ _ _ _ _ f₁ f₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact f₁.1.trans f₂.1.symm) (P.R.reduceT (P.curveA hw))
  · exact two_blk [.x0, .x1] (fun _ _ _ _ _ _ _ _ _ f₁ f₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (f₁.2 hw).trans (f₂.2 hw).symm
      · exact f₁.1.trans f₂.1.symm) (by exact (rT P).prepW hw)

/-- The frame's body, once the arguments are saved. -/
theorem rest_ct :
    RelCT isa (Two P fun _ _ _ => True) (.seq (.block (cfgOf P).digestPtr)
      (.seq (.block (cfgOf P).prep)
      (.seq ((cfgOf P).rekeyFull 0)
      (.seq ((cfgOf P).rekeyFull 1)
      (.seq (.block (cfgOf P).initCnt)
      (.seq (.loop (cfgOf P).tryOne (.nonzero .x .x12))
        (.block (cfgOf P).wipe)))))))
      (Two P fun L m₀ t => ∃ i, Exit P L m₀ i t) := by
  refine (two_wp (Ψ := DgIn P) (two_blk [] spOnly (by exact (rT P).digestPtr)) fun _ _ _ _ hL _ hc _ =>
    WP.mono (digestPtr_ok hL hc) fun _ h => ⟨h.1, h.2.2.1, h.2.2.2⟩).seq ?_
  refine (two_wp (Ψ := QB P) prep_ct fun _ _ _ _ hL hk hc h => stageB_ok (P := P) hL hk hc h.1 h.2).seq ?_
  refine (two_wp (Ψ := QC P) ((rekeyFull_piece 0).rel fun _ _ _ _ => trivial)
    fun _ _ _ _ hL hk hc h => stageC_ok (P := P) hL hk hc h).seq ?_
  refine (two_wp (Ψ := QD P) ((rekeyFull_piece 1).rel fun _ _ _ _ => trivial)
    fun _ _ _ _ hL hk hc h => stageD_ok (P := P) hL hk hc h).seq ?_
  refine (two_wp (Ψ := fun L m₀ t => LoopInv P L m₀ 0 t) (two_blk [] spOnly (initCnt_blk _))
    fun _ _ _ _ hL hk hc h => stageE_ok (P := P) hL hk hc h).seq ?_
  refine loop_ct.seq ?_
  exact two_wp (two_blk [] spOnly (by exact (rT P).wipe)) fun _ _ _ _ hL hk hc ⟨i, h⟩ =>
    WP.mono (stageG_ok hL hk hc h) fun _ ⟨c, x⟩ => ⟨c, i, x⟩

/-! ## The whole function -/

/-- Two calls whose public data agree, in the inner frame. -/
def Entered (P : RfcHash) (ns : List String) (a b : State) : Prop :=
  ∃ s₁ s₂, (rfcP P ns).pre s₁ ∧ (rfcP P ns).pre s₂ ∧ (rfcP P ns).pub s₁ s₂ ∧ a = entered P.e s₁ ∧
    b = entered P.e s₂

theorem save_blk : TaintOk [] Cfg.saveArgs := ⟨_, by taint_decide⟩

/-- Saving the arguments: the runs have the same layout (with the addresses
of the hash function's functions among `ns`), and stop at the same candidate. -/
theorem save_ct {ns : List String} (hns : ∀ n ∈ [P.H.stream.initN, P.H.stream.updN, P.H.stream.finN], n ∈ ns) :
    RelCT isa (Entered P ns) (.block Cfg.saveArgs) (Two P fun _ _ _ => True) := by
  intro a b ta tb a' b' ⟨s₁, s₂, h₁, h₂, ⟨hsp, h0, h1, h2, h4, h5, hres, hsy, hns'⟩, ea, eb⟩ e₁ e₂
  subst ea eb
  obtain ⟨_, hc⟩ := save_blk
  obtain ⟨ht, -⟩ := RelCT.taint (A := taint) (P := fun x y => x.sp = y.sp) (Taint.ofRegs [])
    (fun _ _ h => ⟨h, fun r hr => absurd (Taint.mem_ofRegs.mp hr) List.not_mem_nil⟩) hc _ _ _ _ _ _
    (show (entered P.e s₁).sp = (entered P.e s₂).sp by
      show s₁.sp - 16 - BitVec.ofNat 64 (224 + P.e) = s₂.sp - 16 - BitVec.ofNat 64 (224 + P.e)
      rw [hsp]) e₁ e₂
  obtain ⟨_, u₁, x₁, c₁⟩ := entry_ok (he := P.e_eq) h₁
  obtain ⟨_, u₂, x₂, c₂⟩ := entry_ok (he := P.e_eq) h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  have hfa : (fun n => if n ∈ [P.H.stream.initN, P.H.stream.updN, P.H.stream.finN] then s₁.syms n else 0) =
      fun n => if n ∈ [P.H.stream.initN, P.H.stream.updN, P.H.stream.finN] then s₂.syms n else 0 :=
    funext fun n => by
      split
      · next h => exact hns' n (hns n h)
      · rfl
  have hl : lay P.I.hashLen P.I.ecdsa.curve.len P.R.E P.e P.e_eq P.H.stream P.f s₁ =
      lay P.I.hashLen P.I.ecdsa.curve.len P.R.E P.e P.e_eq P.H.stream P.f s₂ := by
    unfold lay; rw [hsp, h0, h1, h2, h4, h5, hsy, hfa]
  have hr : (result P.I s₁.mem (s₁.gpr .x1) (s₁.gpr .x2)).2 = (result P.I s₂.mem (s₁.gpr .x1) (s₁.gpr .x2)).2 := by
    rw [hres, h1, h2]
  refine ⟨ht, ⟨lay P.I.hashLen P.I.ecdsa.curve.len P.R.E P.e P.e_eq P.H.stream P.f s₁, s₁.gpr, s₂.gpr, s₁.mem,
    s₂.mem⟩, lay_ok (he := P.e_eq) h₁, coreOk_lay P s₁,
    congrArg (fun x => if x = 0 then P.I.tries - 1 else x - 1) hr, c₁, by rw [hl]; exact c₂, trivial, trivial⟩

/-- Runs whose public data agree (with the addresses of the hash function's
functions among `ns`) have the same layout, and stop at the same candidate. -/
theorem sign_ct {ns : List String} (hns : ∀ n ∈ [P.H.stream.initN, P.H.stream.updN, P.H.stream.finN], n ∈ ns) :
    ConstantTime isa (rfcP P ns).pre (rfcP P ns).pub (cfgOf P).sign := by
  refine VG.RelCT.constantTime (Q := fun _ _ => True) (RelCT.pushFrame (R := fun _ _ => True)
    (fun _ _ h => h.2.2.1) (RelCT.alloc (R := fun _ _ => True) ?_))
  refine ((save_ct hns).seq rest_ct).mono ?_ fun _ _ _ => trivial
  rintro _ _ ⟨_, _, ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩, rfl, rfl⟩
  have e : ∀ s, allocated (cfgOf P).frameBytes (pushed .x30 s) = entered P.e s := fun s => by
    rw [frameBytes_eq]; rfl
  exact ⟨s₁, s₂, h₁, h₂, hp, e s₁, e s₂⟩

end VG.Proof.Ecdsa.Rfc6979.AArch64

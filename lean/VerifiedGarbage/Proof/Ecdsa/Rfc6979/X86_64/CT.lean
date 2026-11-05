module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Correct
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Correct
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Reduce
meta import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.X86_64.Syms
meta import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.ICall
meta import VerifiedGarbage.Proof.Framework.ICall
import VerifiedGarbage.Proof.Framework.KernelList
meta import VerifiedGarbage.Proof.Framework.KernelList
import VerifiedGarbage.Proof.Framework.RelSplit
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelSplit
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Copy
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Copy
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Calls
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Calls

/-!
# Deterministic ECDSA on x86-64: constant time, up to the number of candidates

Two runs whose public data agree have the same layout, and stop at the same
candidate (`exitAt`, from the contract's leakage: the number of candidates
RFC 6979 tries). Between the frame's push and pop they are related by `Two`:
both satisfy `Ctx` with that layout (and `Φ`, what the next piece needs). The
blocks address only the stack and the buffers, from registers that agree
(the taint analysis, of the blocks whose contents depend on the curve:
`RfcT`, each curve's `RfcCurve.blk`), or, for the byte loops, from registers
both runs set alike (`T`'s length, `D`); an indirect call reaches, through
the table, whose address the frame holds, the same function in both runs
(`tcall_piece`);
each call is of constant-time code whose public data agree (`RelCT.callEx`);
and the loop's branch agrees, since in both runs it goes on after candidate
`i` iff `i` is before the candidate it stops at (`go_iff`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64

/-- What each of two runs has, between the frame's push and pop. -/
abbrev Env (P : RfcHash) := Lay P.I.hashLen × (Reg → BitVec 64) × (Reg → BitVec 64) × Mem × Mem

/-- Two runs with the same layout that stop at the same candidate, each
satisfying `Ctx` and `Φ`. -/
def Two (P : RfcHash) (Φ : Lay P.I.hashLen → Mem → State → Prop) (a b : State) : Prop :=
  ∃ e : Env P, e.1.Ok ∧ CoreOk P e.1 ∧ exitAt P e.1 e.2.2.2.1 = exitAt P e.1 e.2.2.2.2 ∧ Ctx e.1 e.2.1 e.2.2.2.1 a ∧
    Ctx e.1 e.2.2.1 e.2.2.2.2 b ∧ Φ e.1 e.2.2.2.1 a ∧ Φ e.1 e.2.2.2.2 b

variable {P : RfcHash}

theorem Two.mono {Φ Ψ : Lay P.I.hashLen → Mem → State → Prop} (h : ∀ L m₀ t, Φ L m₀ t → Ψ L m₀ t) {a b : State}
    (ht : Two P Φ a b) : Two P Ψ a b :=
  let ⟨e, hL, hq, hx, c₁, c₂, f₁, f₂⟩ := ht
  ⟨e, hL, hq, hx, c₁, c₂, h _ _ _ f₁, h _ _ _ f₂⟩

/-- Code whose runs leak the same, and which keeps `Ctx` and establishes `Ψ`. -/
theorem two_wp {c : Prog isa} {Φ Ψ : Lay P.I.hashLen → Mem → State → Prop}
    (hct : RelCT isa (Two P Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay P.I.hashLen) g m₀ (t : State), L.Ok → CoreOk P L → Ctx L g m₀ t → Φ L m₀ t →
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

theorem rsp_two {dn : Nat} {L : Lay dn} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 64} {m₁ m₂ : Mem}
    (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) : t₁.gpr .rsp = t₂.gpr .rsp :=
  c₁.rsp.trans c₂.rsp.symm

/-- Code whose addresses depend only on the registers `rs`, which agree. -/
theorem two_prog {c : Prog isa} {Φ : Lay P.I.hashLen → Mem → State → Prop} (rs : List Reg)
    (hrs : ∀ (L : Lay P.I.hashLen) (t₁ t₂ : State) g₁ g₂ m₁ m₂, Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ → Φ L m₁ t₁ →
      Φ L m₂ t₂ → ∀ r ∈ rs, t₁.gpr r = t₂.gpr r)
    (h : ∃ hc, (taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa (Two P Φ) c fun _ _ => True :=
  let ⟨_, h⟩ := h
  RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun _ _ ⟨_, _, _, _, c₁, c₂, f₁, f₂⟩ => Taint.agree_ofRegs (hrs _ _ _ _ _ _ _ c₁ c₂ f₁ f₂)) h

/-- A block whose addresses depend only on the registers `rs`, which agree. -/
theorem two_blk {is : List Instr} {Φ : Lay P.I.hashLen → Mem → State → Prop} (rs : List Reg)
    (hrs : ∀ (L : Lay P.I.hashLen) (t₁ t₂ : State) g₁ g₂ m₁ m₂, Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ → Φ L m₁ t₁ →
      Φ L m₂ t₂ → ∀ r ∈ rs, t₁.gpr r = t₂.gpr r)
    (h : ∃ hc, (taint.check (Taint.ofRegs rs) (.block is) hc).isSome = true) :
    RelCT isa (Two P Φ) (.block is) fun _ _ => True :=
  let ⟨_, h⟩ := h
  RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun _ _ ⟨_, _, _, _, c₁, c₂, f₁, f₂⟩ => Taint.agree_ofRegs (hrs _ _ _ _ _ _ _ c₁ c₂ f₁ f₂)) h

theorem rspOnly {Φ : Lay P.I.hashLen → Mem → State → Prop} : ∀ (L : Lay P.I.hashLen) (t₁ t₂ : State) g₁ g₂ m₁ m₂,
    Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ → Φ L m₁ t₁ → Φ L m₂ t₂ → ∀ r ∈ [Reg.rsp], t₁.gpr r = t₂.gpr r := by
  intro L t₁ t₂ _ _ _ _ c₁ c₂ _ _ r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact rsp_two c₁ c₂

/-! ## Pieces: related in two runs, and keeping `Ctx` in each -/

/-- What one run's piece needs and gives. -/
abbrev Pr (P : RfcHash) := Lay P.I.hashLen → Mem → State → Prop

/-- Nothing. -/
abbrev Tt (P : RfcHash) : Pr P := fun _ _ _ => True

/-- Code that, from `Φ`, leaks the same in two runs and gives `Ψ`, keeping
`Ctx`, in each. -/
structure Piece (P : RfcHash) (Φ : Pr P) (c : Prog isa) (Ψ : Pr P) : Prop where
  ct : RelCT isa (Two P Φ) c (Two P Ψ)
  wp : ∀ (L : Lay P.I.hashLen) g m₀ (t : State), L.Ok → CoreOk P L → Ctx L g m₀ t → Φ L m₀ t →
    WP isa c t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t'

namespace Piece

variable {Φ Ψ Χ : Pr P} {a b c : Prog isa}

theorem of (hct : RelCT isa (Two P Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay P.I.hashLen) g m₀ (t : State), L.Ok → CoreOk P L → Ctx L g m₀ t → Φ L m₀ t →
      WP isa c t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t') : Piece P Φ c Ψ :=
  ⟨two_wp hct hw, hw⟩

theorem seq (h₁ : Piece P Φ a Ψ) (h₂ : Piece P Ψ b Χ) : Piece P Φ (.seq a b) Χ :=
  ⟨h₁.ct.seq h₂.ct, fun L g m₀ t hL hk hc hφ =>
    WP.seq (WP.mono (h₁.wp L g m₀ t hL hk hc hφ) fun _ ⟨c', ψ⟩ => h₂.wp L g m₀ _ hL hk c' ψ)⟩

theorem pre {Φ' : Pr P} (h : Piece P Φ c Ψ) (hp : ∀ L m₀ t, Φ' L m₀ t → Φ L m₀ t) : Piece P Φ' c Ψ :=
  ⟨h.ct.mono (fun _ _ => Two.mono hp) fun _ _ h => h, fun L g m₀ t hL hk hc hφ => h.wp L g m₀ t hL hk hc (hp _ _ _ hφ)⟩

theorem post {Ψ' : Pr P} (h : Piece P Φ c Ψ) (hq : ∀ L m₀ t, Ψ L m₀ t → Ψ' L m₀ t) : Piece P Φ c Ψ' :=
  ⟨h.ct.mono (fun _ _ h => h) fun _ _ => Two.mono hq, fun L g m₀ t hL hk hc hφ =>
    WP.mono (h.wp L g m₀ t hL hk hc hφ) fun _ ⟨c', ψ⟩ => ⟨c', hq _ _ _ ψ⟩⟩

/-- A piece from nothing, from any `Φ`. -/
theorem any (h : Piece P (Tt P) c Ψ) : Piece P Φ c Ψ := h.pre fun _ _ _ _ => trivial

/-- What the relational proofs of the loop use. -/
theorem rel (h : Piece P Φ c Ψ) {Φ' : Pr P} (hp : ∀ L m₀ t, Φ' L m₀ t → Φ L m₀ t) :
    RelCT isa (Two P Φ') c fun _ _ => True :=
  h.ct.mono (fun _ _ => Two.mono hp) fun _ _ _ => trivial

end Piece

/-- A block whose addresses depend only on the registers `rs`, which agree. -/
theorem Piece.blk {is : List Instr} {Φ Ψ : Pr P} (rs : List Reg)
    (hrs : ∀ (L : Lay P.I.hashLen) (t₁ t₂ : State) g₁ g₂ m₁ m₂, Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ → Φ L m₁ t₁ →
      Φ L m₂ t₂ → ∀ r ∈ rs, t₁.gpr r = t₂.gpr r)
    (ht : TaintOk rs is)
    (hw : ∀ (L : Lay P.I.hashLen) g m₀ (t : State), L.Ok → CoreOk P L → Ctx L g m₀ t → Φ L m₀ t →
      WP isa (.block is) t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t') : Piece P Φ (.block is) Ψ :=
  Piece.of (two_blk rs hrs ht) hw

/-- A block whose addresses depend only on `rsp`. -/
theorem Piece.blkS {is : List Instr} {Φ Ψ : Pr P} (ht : TaintOk [.rsp] is)
    (hw : ∀ (L : Lay P.I.hashLen) g m₀ (t : State), L.Ok → CoreOk P L → Ctx L g m₀ t → Φ L m₀ t →
      WP isa (.block is) t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t') : Piece P Φ (.block is) Ψ :=
  Piece.blk [.rsp] rspOnly ht hw

/-- The taint check of a block is that of any block with the same
instructions but for displacements and immediates (`taint_eraseInv`). -/
theorem taintOk_erase {rs : List Reg} {is is₀ : List Instr} (h : TaintOk rs is₀)
    (he : is.map Instr.erase = is₀.map Instr.erase) : TaintOk rs is := by
  obtain ⟨hc, hs⟩ := h
  refine ⟨hc, ?_⟩
  have e := (taint_eraseInv.check (.block is) (Taint.ofRegs rs) hc rfl).1
  have e₀ := (taint_eraseInv.check (.block is₀) (Taint.ofRegs rs) hc rfl).1
  rw [← e, show Code.mapBlocks Instr.erase (.block is) = Code.mapBlocks Instr.erase (.block is₀) from
    congrArg Code.block (by rw [KList.map_eq, KList.map_eq, he]), e₀]
  exact hs

/-- The layout's table is `P`'s. -/
theorem CoreOk.tabL {L : Lay P.I.hashLen} (hk : CoreOk P L) : TabL P L := ⟨hk.2.2.1, hk.2.2.2⟩

/-- The blocks of the curve. -/
theorem rT (P : RfcHash) : RfcT (cfgC P.R.E P.R.big P.R.sh) := P.R.blk

/-! ## The indirect calls -/

/-- What an indirect call of `n` needs of the table in each run: its word
`j` (on entry) is `n`'s address, which is the layout's, and of `ts` an
indirect call reaches `n`'s `c`. -/
def TabFn (P : RfcHash) (j : Nat) (n : String) (c : Prog isa) (ts : List (String × Prog isa)) : Prop :=
  ∀ (L : Lay P.I.hashLen) g m₀ (t : State), L.Ok → CoreOk P L → Ctx L g m₀ t →
    m₀.readW (L.tab + BitVec.ofNat 64 (8 * j)) 64 = t.syms n ∧
      ts.find? (fun q => t.syms q.1 == t.syms n) = some (n, c) ∧ t.syms n = L.fa n

theorem tfn_init : TabFn P 0 P.H.hmacInitN P.H.hmacInit P.f.init := fun L _ _ _ _ hk hc => by
  have hok := hc.tabOk; have htm := hc.tabMem; have hf := hc.fsy
  rw [hk.2.2.1, hk.2.2.2] at hok; rw [hk.2.2.1] at htm hf
  exact ⟨htm.1, hok.i, hf _ (by simp)⟩

theorem tfn_upd : TabFn P 1 P.H.updN P.H.updC P.f.upd := fun L _ _ _ _ hk hc => by
  have hok := hc.tabOk; have htm := hc.tabMem; have hf := hc.fsy
  rw [hk.2.2.1, hk.2.2.2] at hok; rw [hk.2.2.1] at htm hf
  exact ⟨htm.2.1, hok.u, hf _ (by simp)⟩

theorem tfn_fin : TabFn P 2 P.H.hmacFinN P.H.hmacFin P.f.fin := fun L _ _ _ _ hk hc => by
  have hok := hc.tabOk; have htm := hc.tabMem; have hf := hc.fsy
  rw [hk.2.2.1, hk.2.2.2] at hok; rw [hk.2.2.1] at htm hf
  exact ⟨htm.2.2, hok.f, hf _ (by simp)⟩

/-- What only `r11` changing keeps. -/
def R11 (Φ : Pr P) : Prop :=
  ∀ L m₀ (t u : State), Φ L m₀ t → (∀ r, r ≠ .r11 → u.gpr r = t.gpr r) → u.mem = t.mem → u.syms = t.syms →
    Φ L m₀ u

theorem tblk1_taint (x : Nat) : TaintOk [.rsp] [.mov .r11 (.mem (stk x))] :=
  taintOk_erase (is₀ := [.mov .r11 (.mem (stk 0))]) ⟨_, by taint_decide⟩ rfl

theorem tblk2_taint (x : Nat) : TaintOk [.r11] [.mov .r11 (.mem (at_ .r11 x))] :=
  taintOk_erase (is₀ := [.mov .r11 (.mem (at_ .r11 0))]) ⟨_, by taint_decide⟩ rfl

/-- The indirect call of the table's function `j`: in both runs of the same
function, `n`'s (the table's word `j` holds the layout's address of `n`). -/
theorem tcall_piece {Φ Ψ : Pr P} {j : Nat} (hj : 8 * j + 8 ≤ 48) {n : String} {c : Prog isa}
    {ts : List (String × Prog isa)} (hn : TabFn P j n c ts) (hΦ : R11 Φ) (hcall : Piece P Φ (.call n c) Ψ) :
    Piece P Φ (Cfg.tcall j ts) Ψ := by
  refine ⟨?_, fun L g m₀ t hL hk hc hφ => ?_⟩
  · unfold Cfg.tcall
    rw [show ([.mov .r11 (.mem (stk fTab)), .mov .r11 (.mem (at_ .r11 (8 * j)))] : List Instr) =
      [.mov .r11 (.mem (stk fTab))] ++ [.mov .r11 (.mem (at_ .r11 (8 * j)))] from rfl]
    have s₁ : Piece P Φ (.block [.mov .r11 (.mem (stk fTab))]) fun L m₀ u =>
        Φ L m₀ u ∧ u.gpr .r11 = L.tab :=
      Piece.blkS (tblk1_taint _) fun L g m₀ t hL hk hc hφ =>
        WP.mono_syms (tblk1_ok hL hc) fun u ⟨hc', hm, h11, hr⟩ hs => ⟨hc', hΦ _ _ _ _ hφ hr hm hs, h11⟩
    have s₂ : Piece P (fun L m₀ u => Φ L m₀ u ∧ u.gpr .r11 = L.tab) (.block [.mov .r11 (.mem (at_ .r11 (8 * j)))])
        fun L m₀ u => Φ L m₀ u ∧ u.gpr .r11 = L.fa n ∧ u.syms n = L.fa n ∧
          ts.find? (fun q => u.syms q.1 == u.syms n) = some (n, c) :=
      Piece.blk [.r11] (fun _ _ _ _ _ _ _ _ _ f₁ f₂ r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact f₁.2.trans f₂.2.symm) (tblk2_taint _)
        fun L g m₀ t hL hk hc ⟨hφ, h11⟩ => WP.mono (tblk2_ok hL hc h11 hj) fun u ⟨hc', hm, h11', hr, hs⟩ => by
          obtain ⟨hw, hf, hfa⟩ := hn L g m₀ t hL hk hc
          exact ⟨hc', hΦ _ _ _ _ hφ hr hm hs, by rw [h11', hw, hfa], by rw [hs, hfa], by rw [hs]; exact hf⟩
    refine (RelCT.block_append (s₁.ct.seq s₂.ct)).seq ?_
    cases ts with
    | nil => exact RelCT.of_false fun _ _ ⟨_, _, _, _, _, _, f₁, _⟩ => by simp at f₁
    | cons q ts =>
      exact RelCT.icalls_of_call (hcall.ct.mono (fun _ _ => Two.mono fun _ _ _ h => h.1) fun _ _ h => h)
        fun s₁ s₂ ⟨e, _, _, _, _, _, f₁, f₂⟩ => ⟨e.1.fa n, by simp only [X86_64.icall, f₁.2.1],
          by simp only [X86_64.icall, f₂.2.1],
          by show (q :: ts).find? (fun p => s₁.syms p.1 == e.1.fa n) = _; rw [← f₁.2.2.1]; exact f₁.2.2.2,
          by show (q :: ts).find? (fun p => s₂.syms p.1 == e.1.fa n) = _; rw [← f₂.2.2.1]; exact f₂.2.2.2, rfl⟩
  · obtain ⟨hw, hf, -⟩ := hn L g m₀ t hL hk hc
    exact tcall_ok hL hc hj hw hf fun t' hc' hm hr hs =>
      hcall.wp L g m₀ t' hL hk hc' (hΦ _ _ _ _ hφ hr hm hs)

/-! ## HMAC's calls -/

/-- A call related in two runs with the same layout. -/
theorem two_call {Φ : Pr P} {n : String} {c : Prog isa}
    (h : ∀ L : Lay P.I.hashLen, RelCT isa (fun s₁ s₂ => ∃ g₁ g₂ m₁ m₂, L.Ok ∧ CoreOk P L ∧ Ctx L g₁ m₁ s₁ ∧
      Ctx L g₂ m₂ s₂ ∧ Φ L m₁ s₁ ∧ Φ L m₂ s₂) (.call n c) fun _ _ => True) :
    RelCT isa (Two P Φ) (.call n c) fun _ _ => True :=
  (RelCT.exists_ h).mono (fun _ _ ⟨⟨L, g₁, g₂, m₁, m₂⟩, hL, hk, _, c₁, c₂, f₁, f₂⟩ =>
    ⟨L, g₁, g₂, m₁, m₂, hL, hk, c₁, c₂, f₁, f₂⟩) fun _ _ h => h

/-- HMAC's `init`'s arguments. -/
def IA (P : RfcHash) : Pr P := fun L _ u =>
  u.gpr .rdi = L.scr + BitVec.ofNat 64 0 ∧ u.gpr .rsi = L.scr + BitVec.ofNat 64 192 ∧
    u.gpr .rdx = L.B + BitVec.ofNat 64 24 ∧ u.gpr .rcx = BitVec.ofNat 64 P.H.D ∧
    u.gpr .r8 = L.scr + BitVec.ofNat 64 384

theorem hinit_piece : Piece P (IA P) (.call P.H.hmacInitN P.H.hmacInit) (Tt P) := by
  refine Piece.of (two_call fun L => Proof.Pbkdf2.Md.X86_64.Pbk.hinit_rel P.ok P.hI
      fun _ _ ⟨_, _, _, _, hL, _, c₁, c₂, a₁, a₂⟩ =>
    ⟨initA hL c₁ a₁.1 a₁.2.1 a₁.2.2.1 a₁.2.2.2.1 a₁.2.2.2.2, initA hL c₂ a₂.1 a₂.2.1 a₂.2.2.1 a₂.2.2.2.1 a₂.2.2.2.2,
      rsp_two c₁ c₂⟩) fun L g m₀ u hL _ hc a => ?_
  refine WP.of_syms (Proof.Pbkdf2.Md.X86_64.Pbk.hinit_call P.ok P.hI P.hIsp P.hId
    (initA hL hc a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2) fun v hrd hwr hcs hf _ _ hsy => ?_)
  have hsafe : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 0, P.H.S⟩ : Region), ⟨L.scr + BitVec.ofNat 64 192, P.H.S⟩,
      ⟨L.scr + BitVec.ofNat 64 384, 8 * P.H.W⟩], Region.Sub r ⟨L.scr, 2256⟩ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> exact scr_work (by nums)
  exact ⟨hc.keep hL hrd hwr (hcs .rsp (by decide)) (fun r hr _ => hcs r hr) hf
    (safe_call hc (fun r hr => .inr (.inl ((hsafe r hr).trans (Region.sub_prefix (by omega))))) (Nat.le_refl _))
    hsy, trivial⟩

/-- The streaming `update`'s arguments: the inner state holding `cnt`
bytes, the `len` bytes at `da`, and the working space. -/
def UA (P : RfcHash) (cnt : Nat) (da : Lay P.I.hashLen → Addr) (len : Nat) : Pr P := fun L _ u =>
  u.gpr .rdi = L.scr + BitVec.ofNat 64 0 ∧ u.gpr .rsi = BitVec.ofNat 64 cnt ∧ u.gpr .rdx = da L ∧
    u.gpr .rcx = BitVec.ofNat 64 len ∧ u.gpr .r8 = L.scr + BitVec.ofNat 64 384

theorem upd_piece {cnt : Nat} {da : Lay P.I.hashLen → Addr} {len : Nat}
    (hd : ∀ L : Lay P.I.hashLen, L.Ok → DataOk L (da L) len) (hlen : len ≤ 256) :
    Piece P (UA P cnt da len) (.call P.H.updN P.H.updC) (Tt P) := by
  refine Piece.of (two_call fun L => Proof.Pbkdf2.Md.X86_64.Calls.upd_rel P.ok.stream
      fun _ _ ⟨_, _, _, _, hL, _, c₁, c₂, a₁, a₂⟩ =>
    ⟨updA hL c₁ (hd L hL) hlen a₁.1 a₁.2.2.1 a₁.2.2.2.1 a₁.2.2.2.2,
      updA hL c₂ (hd L hL) hlen a₂.1 a₂.2.2.1 a₂.2.2.2.1 a₂.2.2.2.2, a₁.2.1.trans a₂.2.1.symm, rsp_two c₁ c₂⟩)
    fun L g m₀ u hL _ hc a => ?_
  have hsp : Region.Sub (below (u.gpr .rsp) 16) ⟨L.B, 24⟩ := hc.below_sub (by omega)
  refine WP.of_syms (Proof.Pbkdf2.Md.X86_64.Calls.upd_call P.ok.stream
    (updA hL hc (hd L hL) hlen a.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2) (by omega) fun w' af _ hsy => ?_)
  have hws : ∀ r ∈ [(⟨L.scr + BitVec.ofNat 64 0, P.H.stream.S⟩ : Region),
      ⟨L.scr + BitVec.ofNat 64 384, P.ok.stream.Wb⟩], Region.Sub r ⟨L.scr, 2256⟩ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact scr_work (by nums)
  exact ⟨hc.keep hL af.rd af.wr (af.cs .rsp (by decide)) (fun r hr _ => af.cs r hr) af.frame
    (safe_call hc (fun r hr => .inr (.inl ((hws r hr).trans (Region.sub_prefix (by omega))))) (by omega)) hsy,
    trivial⟩

/-- HMAC's `finalize`'s arguments: the states, the `cnt` bytes the inner one
holds, the MAC's place in the frame at `dst`, and the working space. -/
def FA (P : RfcHash) (cnt dst : Nat) : Pr P := fun L _ u =>
  u.gpr .rdi = L.scr + BitVec.ofNat 64 0 ∧ u.gpr .rsi = L.scr + BitVec.ofNat 64 192 ∧
    u.gpr .rdx = BitVec.ofNat 64 cnt ∧ u.gpr .rcx = L.B + BitVec.ofNat 64 (24 + dst) ∧
    u.gpr .r8 = L.scr + BitVec.ofNat 64 384

theorem hfin_piece {cnt dst : Nat} (hdst : dst + P.H.D ≤ 184) :
    Piece P (FA P cnt dst) (.call P.H.hmacFinN P.H.hmacFin) (Tt P) := by
  refine Piece.of (two_call fun L => Proof.Pbkdf2.Md.X86_64.Pbk.hfin_rel P.ok P.hF
      fun _ _ ⟨_, _, _, _, hL, _, c₁, c₂, a₁, a₂⟩ =>
    ⟨finA hL c₁ hdst a₁.1 a₁.2.1 a₁.2.2.1 a₁.2.2.2.1 a₁.2.2.2.2,
      finA hL c₂ hdst a₂.1 a₂.2.1 a₂.2.2.1 a₂.2.2.2.1 a₂.2.2.2.2, rsp_two c₁ c₂⟩)
    fun L g m₀ u hL _ hc a => ?_
  have hsp : below (u.gpr .rsp) 24 = ⟨L.B, 24⟩ := by rw [hc.rsp, below24]
  refine WP.of_syms (Proof.Pbkdf2.Md.X86_64.Pbk.hfin_call P.ok P.hF P.hFsp P.hFd
    (finA hL hc hdst a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2) fun w' hrd hwr hcs hf _ hsy => ?_)
  refine ⟨hc.keep hL hrd hwr (hcs .rsp (by decide)) (fun r hr _ => hcs r hr) hf (hsy := hsy) fun r hr => ?_,
    trivial⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, hsp] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact .inr (.inl ((scr_work (by nums)).trans (Region.sub_prefix (by omega))))
  · exact safe_low L (by nums)
  · exact .inr (.inl ((scr_work (by nums)).trans (Region.sub_prefix (by omega))))
  · exact .inr (.inr (.inl (Region.sub_prefix (by omega))))

theorem r11_ia : R11 (IA P) := fun _ _ _ _ ⟨d, s, x, k, r⟩ hr _ _ => ⟨(hr _ (by decide)).trans d,
  (hr _ (by decide)).trans s, (hr _ (by decide)).trans x, (hr _ (by decide)).trans k, (hr _ (by decide)).trans r⟩

theorem r11_ua {cnt : Nat} {da : Lay P.I.hashLen → Addr} {len : Nat} : R11 (UA P cnt da len) :=
  fun _ _ _ _ ⟨d, s, x, k, r⟩ hr _ _ => ⟨(hr _ (by decide)).trans d, (hr _ (by decide)).trans s,
    (hr _ (by decide)).trans x, (hr _ (by decide)).trans k, (hr _ (by decide)).trans r⟩

theorem r11_fa {cnt dst : Nat} : R11 (FA P cnt dst) :=
  fun _ _ _ _ ⟨d, s, x, k, r⟩ hr _ _ => ⟨(hr _ (by decide)).trans d, (hr _ (by decide)).trans s,
    (hr _ (by decide)).trans x, (hr _ (by decide)).trans k, (hr _ (by decide)).trans r⟩

/-! ## HMAC through the table -/

theorem initArgs_taint : TaintOk [.rsp] Cfg.initArgs := ⟨_, by taint_decide⟩

theorem updVArgs_taint : TaintOk [.rsp] Cfg.updVArgs := ⟨_, by taint_decide⟩

theorem updMArgs_taint (P : RfcHash) (len : Nat) : TaintOk [.rsp] (Cfg.updMArgs len) :=
  taintOk_erase (is₀ := Cfg.updMArgs (1 + 2 * P.Q)) (rT P).updM rfl

theorem finArgs_taint (P : RfcHash) (len dst : Nat) : TaintOk [.rsp] (Cfg.finArgs len dst) :=
  taintOk_erase (is₀ := Cfg.finArgs (1 + 2 * P.Q) fK) (rT P).finM rfl

/-- HMAC's states for `K`. -/
theorem initK_piece {Φ : Pr P} : Piece P Φ (cfgOf P).initK (Tt P) :=
  (Piece.blkS (Ψ := IA P) initArgs_taint fun _ _ _ _ hL hk hc _ =>
    WP.mono (initArgs_ok hL hk.tabL hc) fun _ ⟨c, _, d, s, x, k, r⟩ => ⟨c, d, s, x, k, r⟩).seq
    (tcall_piece (by decide) tfn_init r11_ia hinit_piece)

/-- The inner state updated with `V`. -/
theorem updV_piece {Φ : Pr P} : Piece P Φ (cfgOf P).updV (Tt P) :=
  (Piece.blkS (Ψ := UA P P.H.P.B (fun L => L.B + BitVec.ofNat 64 88) P.H.D) updVArgs_taint
    fun _ _ _ _ hL hk hc _ =>
      WP.mono (updVArgs_ok hL hk.tabL hc) fun _ ⟨c, _, d, s, x, k, r⟩ => ⟨c, d, s, x, k, r⟩).seq
    (tcall_piece (by decide) tfn_upd r11_ua (upd_piece (fun L _ => .inl ⟨88, rfl, by omega, by nums⟩) (by nums)))

/-- The inner state updated with the message's `len` bytes. -/
theorem updM_piece {Φ : Pr P} {len : Nat} (hlen : len ≤ 256) : Piece P Φ ((cfgOf P).updM len) (Tt P) :=
  (Piece.blkS (Ψ := UA P (P.H.P.B + P.H.D) (fun L => L.scr + BitVec.ofNat 64 sMsg) len) (updMArgs_taint P len)
    fun _ _ _ _ hL hk hc _ =>
      WP.mono (updMArgs_ok hL hk.tabL hc (len := len) (by omega)) fun _ ⟨c, _, d, s, x, k, r⟩ =>
        ⟨c, d, s, x, k, r⟩).seq
    (tcall_piece (by decide) tfn_upd r11_ua
      (upd_piece (fun L _ => .inr ⟨sMsg, rfl, by simp only [sMsg]; omega, by simp only [sMsg]; omega⟩) hlen))

/-- The MAC, of `D + len` bytes, to the frame at `dst`. -/
theorem fin_piece {Φ : Pr P} {len dst : Nat} (hlen : len ≤ 256) (hdst : dst + P.H.D ≤ 184) :
    Piece P Φ ((cfgOf P).fin len dst) (Tt P) :=
  (Piece.blkS (Ψ := FA P (P.H.P.B + P.H.D + len) dst) (finArgs_taint P len dst) fun _ _ _ _ hL hk hc _ =>
    WP.mono (finArgs_ok hL hk.tabL hc (len := len) (dst := dst) (by omega) (by omega))
      fun _ ⟨c, _, d, s, x, k, r⟩ => ⟨c, d, s, x, k, r⟩).seq
    (tcall_piece (by decide) tfn_fin r11_fa (hfin_piece hdst))

/-! ## Blocks from `scratch`'s pointer -/

/-- `scratch` in `rdi`. -/
def ScrIn (P : RfcHash) : Pr P := fun L _ u => u.gpr .rdi = L.scr

theorem scrPtr_piece {Φ : Pr P} : Piece P Φ (.block Cfg.scrPtr) (ScrIn P) :=
  Piece.blkS ⟨_, by taint_decide⟩ fun _ _ _ _ hL _ hc _ => WP.mono (scrPtr_ok hL hc) fun _ h => ⟨h.1, h.2.2.1⟩

theorem scrRegs {Φ : Pr P} (hΦ : ∀ L m₀ t, Φ L m₀ t → t.gpr .rdi = L.scr) :
    ∀ (L : Lay P.I.hashLen) (t₁ t₂ : State) g₁ g₂ m₁ m₂, Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ → Φ L m₁ t₁ →
      Φ L m₂ t₂ → ∀ r ∈ [Reg.rsp, .rdi], t₁.gpr r = t₂.gpr r := by
  intro L _ _ _ _ _ _ c₁ c₂ f₁ f₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact rsp_two c₁ c₂
  · exact (hΦ _ _ _ f₁).trans (hΦ _ _ _ f₂).symm

/-- A block that loads `scratch` into `rdi`, then addresses memory only from
`rsp` and `rdi`. -/
theorem Piece.scrBlk {is : List Instr} {Φ Ψ : Pr P} (ht : TaintOk [.rsp, .rdi] is)
    (hw : ∀ (L : Lay P.I.hashLen) g m₀ (t : State), L.Ok → CoreOk P L → Ctx L g m₀ t → Φ L m₀ t →
      WP isa (.block (Cfg.scrPtr ++ is)) t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t') :
    Piece P Φ (.block (Cfg.scrPtr ++ is)) Ψ :=
  Piece.of (RelCT.block_append (scrPtr_piece.ct.seq (two_blk [.rsp, .rdi] (scrRegs fun _ _ _ h => h) ht))) hw

theorem copyStates_taint (b : Bool) : TaintOk [.rsp, .rdi] (Cfg.copyStates b) := by
  cases b
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩

/-- HMAC's states saved (`b`), or restored. -/
theorem copyStates_piece {Φ : Pr P} (b : Bool) : Piece P Φ (.block (Cfg.scrPtr ++ Cfg.copyStates b)) (Tt P) :=
  Piece.scrBlk (copyStates_taint b) fun L _ _ _ hL _ hc _ => by
    rw [WP.block_append_iff]
    refine WP.mono (scrPtr_ok hL hc) fun u ⟨hcu, _, hdi, _⟩ => ?_
    cases b
    · exact WP.mono (copy_ok hL hcu (src := .rdi) (S := L.scr) hdi (by decide) hdi (so := 3072) (d := 0) (K := 48)
        (by decide) (fun j hj => hcu.inScr (by omega)) (Offset.disjoint _ (by decide) (by decide) (by decide)))
        fun _ h => ⟨h.1, trivial⟩
    · exact WP.mono (copy_ok hL hcu (src := .rdi) (S := L.scr) hdi (by decide) hdi (so := 0) (d := 3072) (K := 48)
        (by decide) (fun j hj => hcu.inScr (by omega)) (Offset.disjoint _ (by decide) (by decide) (by decide)))
        fun _ h => ⟨h.1, trivial⟩

/-! ## HMAC -/

theorem hmacVS_piece {Φ : Pr P} : Piece P Φ (cfgOf P).hmacVS (Tt P) :=
  initK_piece.seq ((copyStates_piece true).seq (updV_piece.seq (fin_piece (by decide) (by simp only [fV]; nums))))

theorem hmacVR_piece {Φ : Pr P} : Piece P Φ (cfgOf P).hmacVR (Tt P) :=
  (copyStates_piece false).seq (updV_piece.seq (fin_piece (by decide) (by simp only [fV]; nums)))

/-- `K = HMAC_K(V ‖ msg)`, for the message's `len` bytes. -/
theorem hmacK_piece {Φ : Pr P} {len : Nat} (hlen : len ≤ 256) (fresh : Bool) :
    Piece P Φ ((cfgOf P).hmacK fresh len) (Tt P) := by
  unfold Cfg.hmacK
  cases fresh
  · exact (copyStates_piece false).seq (updV_piece.seq ((updM_piece hlen).seq (fin_piece hlen (by simp only [fK]; nums))))
  · exact initK_piece.seq (updV_piece.seq ((updM_piece hlen).seq (fin_piece hlen (by simp only [fK]; nums))))

/-! ## `K` and `V` from a message -/

/-- `scratch` in `rdi` and `d` in `rsi`. -/
def PtrsIn (P : RfcHash) : Pr P := fun L _ u => u.gpr .rdi = L.scr ∧ u.gpr .rsi = L.d

theorem msgPtrs_piece {Φ : Pr P} : Piece P Φ (.block Cfg.msgPtrs) (PtrsIn P) :=
  Piece.blkS ⟨_, by taint_decide⟩ fun _ _ _ _ hL _ hc _ =>
    WP.mono (ptrs_ok hL hc) fun _ ⟨c, _, d, s⟩ => ⟨c, d, s⟩

/-- The message `b (‖ d ‖ h)` at `scratch + sMsg`. -/
theorem msg_piece {b : Nat} {full : Bool} (ht : TaintOk [.rsp, .rdi, .rsi] ((cfgOf P).msg b full)) :
    Piece P (PtrsIn P) (.block ((cfgOf P).msg b full)) (Tt P) :=
  Piece.blk [.rsp, .rdi, .rsi] (fun _ _ _ _ _ _ _ c₁ c₂ f₁ f₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact rsp_two c₁ c₂
      · exact f₁.1.trans f₂.1.symm
      · exact f₁.2.trans f₂.2.symm) ht
    fun _ _ _ _ hL hk hc hp => WP.mono (msg_ok hL hk.1 hc hp.1 hp.2 b full) fun _ h => ⟨h.1, trivial⟩

theorem msgF_taint (b : Nat) : TaintOk [.rsp, .rdi, .rsi] ((cfgOf P).msg b true) :=
  taintOk_erase (by exact (rT P).msgF) (by simp only [Cfg.msg, ↓reduceIte, List.map_append]; rfl)

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)`. -/
theorem rekeyFull_piece {Φ : Pr P} (b : Nat) : Piece P Φ ((cfgOf P).rekeyFull b) (Tt P) := by
  have hlen : 1 + 2 * (cfgOf P).len ≤ 256 := by show 1 + 2 * P.Q ≤ 256; nums
  unfold Cfg.rekeyFull
  exact msgPtrs_piece.seq ((msg_piece (msgF_taint b)).seq ((hmacK_piece hlen _).seq hmacVS_piece))

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)`. -/
theorem rekey_piece {Φ : Pr P} : Piece P Φ (cfgOf P).rekey (Tt P) := by
  unfold Cfg.rekey
  exact msgPtrs_piece.seq ((msg_piece (by exact (rT P).msgN)).seq ((hmacK_piece (by decide) _).seq hmacVS_piece))

/-- `Ctx` with other callee-saved values, which are the same. -/
theorem Ctx.regen {dn : Nat} {L : Lay dn} {g g' : Reg → BitVec 64} {m₀ : Mem} {u : State} (hc : Ctx L g' m₀ u)
    (h : ∀ r ∈ calleeSaved, r ≠ .rsp → g' r = g r) : Ctx L g m₀ u :=
  { hc with cs := fun r hr hr' => (hc.cs r hr hr').trans (h r hr hr') }

/-! ## The byte loops -/

theorem cpLoop_taint : ∃ hc, (taint.check (Taint.ofRegs [.rsi, .rdi, .rcx, .r8]) Cfg.cpLoop hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- A byte copy's registers. -/
abbrev CpA (P : RfcHash) (p q : Lay P.I.hashLen → Addr) (n : Nat) : Pr P := fun L _ u =>
  u.gpr .rsi = q L ∧ u.gpr .rdi = p L ∧ u.gpr .rcx = BitVec.ofNat 64 n ∧ u.gpr .r8 = BitVec.ofNat 64 0

/-- The byte loop, from registers that agree. -/
theorem cp_ct {Φ : Pr P} {p q : Lay P.I.hashLen → Addr} {n : Nat} (h : ∀ L m₀ u, Φ L m₀ u → CpA P p q n L m₀ u) :
    RelCT isa (Two P Φ) Cfg.cpLoop fun _ _ => True :=
  two_prog [.rsi, .rdi, .rcx, .r8] (fun _ _ _ _ _ _ _ _ _ f₁ f₂ r hr => by
    obtain ⟨a₁, b₁, c₁, d₁⟩ := h _ _ _ f₁; obtain ⟨a₂, b₂, c₂, d₂⟩ := h _ _ _ f₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact a₁.trans a₂.symm
    · exact b₁.trans b₂.symm
    · exact c₁.trans c₂.symm
    · exact d₁.trans d₂.symm) cpLoop_taint

/-! ## The candidate -/

/-- After `j` of the candidate's `V`s, from some `K` and `V`. -/
abbrev CJ (P : RfcHash) (j : Nat) : Pr P := fun L m₀ u => ∃ g' t₀ K V₀, CI P L g' m₀ t₀ K V₀ j u

/-- `T`'s length, `j` blocks. -/
abbrev TL (P : RfcHash) (j : Nat) : Pr P := fun L _ u => tlen L u.mem = BitVec.ofNat 64 (j * P.H.D)

/-- The arguments of the copy of `V` to `T`'s end, and `j` blocks. -/
abbrev KA (P : RfcHash) (j : Nat) : Pr P := fun L m₀ u =>
  CpA P (fun L => L.B + BitVec.ofNat 64 (24 + fT + j * P.H.D)) (fun L => L.B + BitVec.ofNat 64 (24 + fV)) P.H.D
    L m₀ u ∧ TL P j L m₀ u

/-- One `V`'s blocks and calls leak the same in both runs. -/
theorem candStep_trace {j : Nat} (hj : j < P.nV) :
    RelCT isa (Two P (CJ P j)) (cfgOf P).candStep fun _ _ => True := by
  obtain ⟨-, hND, -⟩ := nV_facts P
  obtain ⟨-, -, -, -, -, -, hD16, hD64, -, -, -, -, -, -, -, hQ66, -, -⟩ := P.sizes
  have hb : (j + 1) * P.H.D ≤ 136 :=
    Nat.le_trans (Nat.mul_le_mul (show j + 1 ≤ P.nV by omega) (Nat.le_refl P.H.D)) (by omega)
  have hjD : (j + 1) * P.H.D = j * P.H.D + P.H.D := Nat.succ_mul _ _
  refine (two_wp (Ψ := TL P j) (hmacVR_piece.rel fun _ _ _ _ => trivial) fun L g m₀ t hL hk hc hJ => ?_).seq
    ((two_wp (Ψ := KA P j) (two_blk [.rsp] rspOnly ⟨_, by taint_decide⟩) fun L g m₀ t hL hk hc hl =>
      WP.mono (keepArgs_ok hL hk.tabL hc hl) fun u ⟨c, hm, si, di, cx, r8⟩ =>
        ⟨c, ⟨si, di, cx, r8⟩, by show tlen L u.mem = _; rw [hm]; exact hl⟩).seq
    ((two_wp (Ψ := TL P j) (cp_ct fun _ _ _ h => h.1) fun L g m₀ t hL hk hc ⟨⟨si, di, cx, r8⟩, hl⟩ => ?_).seq
      (two_blk [.rsp] rspOnly (by exact (rT P).tStep))))
  · obtain ⟨_, _, _, _, hI⟩ := hJ
    have hS : SavedK P L t.mem (kOf P L t.mem) := by rw [hI.k]; exact hI.saved
    refine WP.mono (hmacVR_ok hL hk.tabL hc hS) fun u ⟨hc₁, hf₁, _⟩ => ⟨hc₁, ?_⟩
    show tlen L u.mem = _
    rw [← hI.len]
    exact hf₁.readW (Region.contains_self _ _) (fun r hr => by
      have := L.he
      simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_SCR (by simp only [fTlen]; omega)
      · exact Offset.disjoint_base _ (by simp only [fTlen]; omega) (by simp only [fTlen]; omega)) (by decide)
  · have he := L.he
    have hnb := hL.nb
    refine WP.mono (cp_ok hL hc (p := L.B + BitVec.ofNat 64 (24 + fT + j * P.H.D))
        (q := L.B + BitVec.ofNat 64 (24 + fV)) (n := P.H.D) (by omega) (by omega) cx di si r8 ?_
        (hc.inFrW (by omega) (by simp only [fT]; omega))
        (safe_high L (by simp only [fT]; omega) (by simp only [fT]; omega))
        (fun i hi => by
          obtain ⟨R, hR, h⟩ := hc.inFrW (d := 24 + fV + i) (n := 1) (by omega) (by simp only [fV]; omega)
          exact ⟨R, List.mem_append_right _ hR, by rw [Offset.add_add]; exact h⟩)
        (fun i hi h => Offset.disjoint L.B (d := 24 + fV + i) (n := 1) (e := 24 + fT + j * P.H.D) (k := P.H.D)
          (.inl (by simp only [fV, fT]; omega)) (by simp only [fV]; omega) (by simp only [fT]; omega) _
          (by rw [← Offset.add_add]; exact Region.contains_self _ _) h)) fun u ⟨hcu, _, hf, _⟩ => ⟨hcu, ?_⟩
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 24 + fT + _) (by simp only [fT]; omega),
        Nat.mod_eq_of_lt (by simp only [fT]; omega)]
      simp only [fT]; omega
    · show tlen L u.mem = _
      rw [← hl]
      exact hf.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (.inl (by simp only [fTlen, fT]; omega)) (by simp only [fTlen]; omega)
          (by simp only [fT]; omega)) (by decide)

/-- The loop of the candidate's `V`s, in two runs: at the same block. -/
theorem candLoop_ct :
    RelCT isa (Two P (CJ P 0)) (.loop (cfgOf P).candStep .b) (Two P (CJ P P.nV)) := by
  obtain ⟨hN1, hND, -⟩ := nV_facts P
  obtain ⟨-, -, -, -, -, -, -, hD64, -, -, -, -, -, -, -, hQ66, -, -⟩ := P.sizes
  have h := VG.RelCT.loop (M := isa) (c := .b) (Q := Two P (CJ P P.nV))
    (fun n => fun s₁ s₂ => 0 < n ∧ n ≤ P.nV ∧ Two P (CJ P (P.nV - n)) s₁ s₂) (n := P.nV) (body := (cfgOf P).candStep)
    (fun n => by
      refine fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨hn0, hnN, hp⟩ e₁ e₂ => ?_
      have hj : P.nV - n < P.nV := by omega
      have hb : (P.nV - n + 1) * P.H.D ≤ 136 :=
        Nat.le_trans (Nat.mul_le_mul (show P.nV - n + 1 ≤ P.nV by omega) (Nat.le_refl P.H.D)) (by omega)
      obtain ⟨ht, hq⟩ := (two_wp (Ψ := fun L m₀ u => CJ P (P.nV - n + 1) L m₀ u ∧
          u.cf = some (decide ((P.nV - n + 1) * P.H.D < P.Q))) (candStep_trace hj)
        fun L g m₀ t hL hk hc ⟨g', t₀, K, V₀, hI⟩ => WP.mono (step_ok hL hk.tabL hb hI)
          fun u ⟨hI', hcf⟩ => ⟨hI'.ctx.regen fun r h h' => (hI.ctx.cs r h h').symm.trans (hc.cs r h h'),
            ⟨g', t₀, K, V₀, hI'⟩, hcf⟩) s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
      refine ⟨ht, ?_, ?_, ?_⟩
      · obtain ⟨_, _, _, _, _, _, f₁, f₂⟩ := hq
        show s₁'.cf = s₂'.cf; rw [f₁.2, f₂.2]
      · intro hf
        obtain ⟨e, hL, hk, hx, c₁, c₂, f₁, f₂⟩ := hq
        have : ¬ (P.nV - n + 1) * P.H.D < P.Q := by
          intro h'; have := f₁.2; rw [decide_eq_true h'] at this; exact absurd (this.symm.trans hf) (by decide)
        have hNn : P.nV - n + 1 = P.nV := by
          have : ¬ P.nV - n + 1 < P.nV := fun h => this ((nV_lt P _).mp h)
          omega
        exact ⟨e, hL, hk, hx, c₁, c₂, hNn ▸ f₁.1, hNn ▸ f₂.1⟩
      · intro hf
        obtain ⟨e, hL, hk, hx, c₁, c₂, f₁, f₂⟩ := hq
        have h' : (P.nV - n + 1) * P.H.D < P.Q := by
          by_contra h'; have := f₁.2; rw [decide_eq_false h'] at this; exact absurd (this.symm.trans hf) (by decide)
        have hlt := (nV_lt P (P.nV - n)).mpr h'
        refine ⟨n - 1, by omega, by omega, by omega, e, hL, hk, hx, c₁, c₂, ?_, ?_⟩ <;>
          rw [show P.nV - (n - 1) = P.nV - n + 1 by omega]
        · exact f₁.1
        · exact f₂.1)
  exact h.mono (fun s₁ s₂ hp => ⟨hN1, Nat.le_refl _, by rwa [Nat.sub_self]⟩) fun _ _ h => h


theorem candTop_ct {Φ : Pr P} : RelCT isa (Two P Φ) (.block (cfgOf P).candTop) fun _ _ => True := by
  cases hb : P.R.big
  · rw [show (cfgOf P).candTop = [] by
      simp only [Cfg.candTop, show (cfgOf P).big = false from hb, Bool.false_eq_true, ite_false]]
    exact two_blk [.rsp] rspOnly ⟨_, by taint_decide⟩
  · rw [show (cfgOf P).candTop = Cfg.scrPtr ++ (cfgOf P).conv fT (cfgOf P).sh by
      simp only [Cfg.candTop, show (cfgOf P).big = true from hb, ite_true]]
    exact (RelCT.block_append (scrPtr_piece.ct.seq
      (two_blk [.rsp, .rdi] (scrRegs fun _ _ _ h => h) (by exact (rT P).convT hb)))).mono (fun _ _ h => h)
      fun _ _ _ => trivial

/-- The candidate: its calls, blocks and loops leak the same in both runs. -/
theorem cand_ct :
    RelCT isa (Two P fun L _ t => SavedK P L t.mem (kOf P L t.mem)) (cfgOf P).cand fun _ _ => True := by
  unfold Cfg.cand
  exact (two_wp (Ψ := CJ P 0) (two_blk [.rsp] rspOnly ⟨_, by taint_decide⟩) fun L g m₀ t hL hk hc hS =>
    WP.mono (tInit_ci hL hc hS) fun u hI => ⟨hI.ctx, _, _, _, _, hI⟩).seq (candLoop_ct.seq candTop_ct)

theorem ce_rsp_two {dn : Nat} {L : Lay dn} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 64} {m₁ m₂ : Mem}
    (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) (rd₁ wr₁ rd₂ wr₂ : List Region) :
    (t₁.callEntry.withRegions rd₁ wr₁).gpr .rsp = (t₂.callEntry.withRegions rd₂ wr₂).gpr .rsp := by
  rw [State.withRegions_gpr, State.withRegions_gpr, State.callEntry_rsp, State.callEntry_rsp, rsp_two c₁ c₂]

theorem ce_two {t₁ t₂ : State} {r : Reg} (hr : r ≠ .rsp) {x : BitVec 64} (h₁ : t₁.gpr r = x) (h₂ : t₂.gpr r = x)
    (rd₁ wr₁ rd₂ wr₂ : List Region) :
    (t₁.callEntry.withRegions rd₁ wr₁).gpr r = (t₂.callEntry.withRegions rd₂ wr₂).gpr r := by
  rw [ce_gpr _ _ _ hr, ce_gpr _ _ _ hr, h₁, h₂]


/-- `core`, with arguments that agree. -/
theorem core_ct {i : Nat} :
    RelCT isa (Two P fun L m₀ u => P₁ P L m₀ i u ∧ Args P L u) (.call (cfgOf P).coreN (cfgOf P).coreC)
      fun _ _ => True :=
  RelCT.callEx (k := (coreK P.R.E).clear) (fun s h => P.R.coreX s h.1 h.2)
    (fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ => P.R.coreCT s₁ s₂ t₁ t₂ s₁' s₂' h₁.1 h₂.1)
    fun _ _ ⟨⟨L, _, _, _, _⟩, hL, hk, _, c₁, c₂, ⟨_, a₁⟩, ⟨_, a₂⟩⟩ =>
    ⟨coreRd P L, coreWr P L, coreRd P L, coreWr P L,
      ⟨core_pre hL hk c₁ a₁.rdi a₁.rsi a₁.rdx a₁.rcx a₁.r8, core_clear hL hk c₁⟩,
      ⟨core_pre hL hk c₂ a₂.rdi a₂.rsi a₂.rdx a₂.rcx a₂.r8, core_clear hL hk c₂⟩,
      ⟨ce_rsp_two c₁ c₂ _ _ _ _, ce_two (by decide) a₁.rdi a₂.rdi _ _ _ _, ce_two (by decide) a₁.rsi a₂.rsi _ _ _ _,
        ce_two (by decide) a₁.rdx a₂.rdx _ _ _ _, ce_two (by decide) a₁.rcx a₂.rcx _ _ _ _,
        ce_two (by decide) a₁.r8 a₂.r8 _ _ _ _, fun c hc => by
          have hc' : c ∈ L.cs := by rw [hk.2.1]; exact hc
          exact (c₁.sy c hc').trans (c₂.sy c hc').symm⟩,
      core_covers hk hL c₁, core_coversW hk.1 c₁, core_covers hk hL c₂, core_coversW hk.1 c₂, rsp_two c₁ c₂⟩

/-- Whether to go on agrees: in both runs, iff the candidate is before the one it stops at. -/
theorem dec_two {L : Lay P.I.hashLen} {m₁ m₂ : Mem} {i : Nat} (hx : exitAt P L m₁ = exitAt P L m₂) {u₁ u₂ : State}
    (h₁ : Mid P L m₁ i u₁) (h₂ : Mid P L m₂ i u₂) : isa.eval .ne u₁ = isa.eval .ne u₂ := by
  rw [h₁.dec, h₂.dec]
  refine congrArg some (decide_eq_decide.mpr ?_)
  rw [go_iff h₁.lt h₁.fails, go_iff h₂.lt h₂.fails, hx]

/-- What one candidate leaves: the end, or the next candidate. -/
def After (P : RfcHash) (i : Nat) (L : Lay P.I.hashLen) (m₀ : Mem) (t : State) : Prop :=
  (isa.eval .ne t = some false ∧ Exit P L m₀ i t) ∨ (isa.eval .ne t = some true ∧ LoopInv P L m₀ (i + 1) t)

theorem tryOne_trace {i : Nat} :
    RelCT isa (Two P fun L m₀ t => LoopInv P L m₀ i t) (cfgOf P).tryOne fun _ _ => True := by
  refine (two_wp (Ψ := fun L m₀ u => P₁ P L m₀ i u)
    (cand_ct.mono (fun _ _ h => Two.mono (fun _ _ _ hi => hi.saved) h) fun _ _ h => h)
    fun _ _ _ _ hL hk hc hi => try₁_ok hL hk hc hi).seq ?_
  refine (two_wp (Ψ := fun L m₀ u => P₁ P L m₀ i u ∧ Args P L u) (two_blk [.rsp] rspOnly (by exact (rT P).coreArgs))
    fun _ _ _ _ hL hk hc hi => try₂_ok hL hc hi).seq ?_
  refine (two_wp (Ψ := fun L m₀ u => P₃ P L m₀ i u) core_ct fun _ _ _ _ hL hk hc hi =>
    try₃_ok hL hk hc hi.1 hi.2).seq ?_
  refine (two_wp (Ψ := fun L m₀ u => Mid P L m₀ i u) (two_blk [.rsp] rspOnly ⟨_, by taint_decide⟩)
    fun _ _ _ _ hL hk hc hi => try₄_ok hL hk hc hi).seq ?_
  refine VG.RelCT.ite (fun _ _ ⟨_, _, _, hx, _, _, f₁, f₂⟩ => dec_two hx f₁ f₂) ?_ ?_
  · exact (rekey_piece.ct.seq (two_blk [.rsp] rspOnly ⟨_, by taint_decide⟩)).mono (fun _ _ h => h.1) fun _ _ h => h
  · exact (two_blk [.rsp] rspOnly ⟨_, by taint_decide⟩).mono (fun _ _ h => h.1) fun _ _ h => h

/-- One candidate: both runs end, or both go on. -/
theorem tryOne_ct {i : Nat} :
    RelCT isa (Two P fun L m₀ t => LoopInv P L m₀ i t) (cfgOf P).tryOne fun s₁ s₂ =>
      isa.eval .ne s₁ = isa.eval .ne s₂ ∧ (isa.eval .ne s₁ = some false → Two P (Exit P · · i) s₁ s₂) ∧
        (isa.eval .ne s₁ = some true → Two P (LoopInv P · · (i + 1)) s₁ s₂) := by
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

theorem tries_ct :
    RelCT isa (Two P fun L m₀ t => LoopInv P L m₀ 0 t) (.loop (cfgOf P).tryOne .ne)
      (Two P fun L m₀ t => ∃ i, Exit P L m₀ i t) := by
  have h : RelCT isa (Two P fun L m₀ t => LoopInv P L m₀ (P.I.tries - P.I.tries) t) (.loop (cfgOf P).tryOne .ne)
      (Two P fun L m₀ t => ∃ i, Exit P L m₀ i t) :=
    VG.RelCT.loop (M := isa) (fun n => Two P fun L m₀ t => LoopInv P L m₀ (P.I.tries - n) t)
      (fun n => tryOne_ct.mono (fun _ _ h => h) fun _ _ ⟨he, hf, ht⟩ =>
        ⟨he, fun h => (hf h).mono fun _ _ _ hx => ⟨_, hx⟩, fun h => by
          obtain ⟨e, hL, hk, hx, c₁, c₂, f₁, f₂⟩ := ht h
          have hn := next_n f₁.lt
          refine ⟨P.I.tries - (P.I.tries - n + 1), hn.1, e, hL, hk, hx, c₁, c₂, ?_, ?_⟩ <;> rwa [hn.2]⟩)
      P.I.tries
  rwa [Nat.sub_self] at h

/-! ## The frame's body -/

theorem initCnt_taint (c : Cfg) : TaintOk [.rsp] c.initCnt :=
  taintOk_erase (is₀ := [.mov32 .rax (.imm (BitVec.ofNat 32 0)), .store (stk fCnt) .rax]) ⟨_, by taint_decide⟩ rfl

theorem prepX_ct : RelCT isa (Two P (Tt P)) (cfgOf P).prepX (Two P (QX P)) := by
  refine two_wp ?_ fun L g m₀ t hL hk hc _ => stageX_ok hL hk hc
  rw [Cfg.prepX]
  exact (two_wp (Ψ := CpA P (fun L => L.B + BitVec.ofNat 64 (24 + fX + (P.Q - min P.H.D P.Q))) (fun L => L.dg)
      (min P.H.D P.Q)) (two_blk [.rsp] rspOnly (by exact (rT P).xArgs)) fun L g m₀ t hL hk hc _ =>
    WP.mono (xArgs_ok hL hk.tabL hc) fun _ ⟨c, _, _, cx, di, si, r8⟩ => ⟨c, si, di, cx, r8⟩).seq
    (cp_ct fun _ _ _ h => h)

theorem prepH_ct : RelCT isa (Two P (QX P)) (cfgOf P).prepH (Two P (QA P)) := by
  refine two_wp ?_ fun L g m₀ t hL hk hc hx => stageH_ok hL hk hc hx
  cases hb : P.R.big
  · rw [show (cfgOf P).prepH = .block (cfgOf P).reduce by
      simp only [Cfg.prepH, show (cfgOf P).big = false from hb, Bool.false_eq_true, ite_false]]
    exact two_blk [.rsp] rspOnly (by exact (rT P).reduce hb)
  · rw [show (cfgOf P).prepH = (cfgOf P).prepC by
      simp only [Cfg.prepH, show (cfgOf P).big = true from hb, ite_true], Cfg.prepC]
    refine RelCT.assoc ((two_wp (Ψ := Tt P) ((two_wp (Ψ := CpA P
        (fun L => L.B + BitVec.ofNat 64 (24 + fXc + (P.Q - 1 - P.H.D))) (fun L => L.dg) P.H.D)
        (two_blk [.rsp] rspOnly (by exact (rT P).xcArgs hb)) fun L g m₀ t hL hk hc _ =>
          WP.mono (xcArgs_ok hL hk.tabL hb hc) fun _ ⟨c, cx, di, si, r8⟩ => ⟨c, si, di, cx, r8⟩).seq
        (cp_ct fun _ _ _ h => h)) fun L g m₀ t hL hk hc _ =>
          WP.mono (xcCopy_ok hL hk.tabL hb (Nat.le_of_eq P.len.symm) hc) fun _ h => ⟨h, trivial⟩).seq ?_)
    exact (RelCT.block_append (scrPtr_piece.ct.seq
      (two_blk [.rsp, .rdi] (scrRegs fun _ _ _ h => h) (by exact (rT P).convC hb)))).mono (fun _ _ h => h)
      fun _ _ _ => trivial

theorem body_ct :
    RelCT isa (Two P (Tt P)) (cfgOf P).body (Two P fun L m₀ t => ∃ i, Exit P L m₀ i t) := by
  rw [Cfg.body]
  refine prepX_ct.seq (prepH_ct.seq ?_)
  refine (two_wp (Ψ := QB P) (two_blk [.rsp] rspOnly ⟨_, by taint_decide⟩)
    fun _ _ _ _ hL _ hc h => stageB_ok hL hc h).seq ?_
  refine (two_wp (Ψ := QC P) ((rekeyFull_piece 0).rel fun _ _ _ _ => trivial)
    fun _ _ _ _ hL hk hc h => stageC_ok (P := P) hL hk hc h).seq ?_
  refine (two_wp (Ψ := QD P) ((rekeyFull_piece 1).rel fun _ _ _ _ => trivial)
    fun _ _ _ _ hL hk hc h => stageD_ok (P := P) hL hk hc h).seq ?_
  refine (two_wp (Ψ := fun L m₀ t => LoopInv P L m₀ 0 t) (two_blk [.rsp] rspOnly (initCnt_taint _))
    fun _ _ _ _ hL _ hc h => stageE_ok (P := P) hL hc h).seq ?_
  refine tries_ct.seq ?_
  exact two_wp (two_blk [.rsp] rspOnly ⟨_, by taint_decide⟩) fun _ _ _ _ hL hk hc ⟨i, h⟩ =>
    WP.mono (stageG_ok hL hk hc h) fun _ ⟨c, x⟩ => ⟨c, i, x⟩

/-! ## The whole function -/

/-- Runs whose public data agree (with the addresses of the hash function's
HMAC functions among `ns`) have the same layout, and stop at the same
candidate. -/
theorem sign_ct {ns : List String} (hns : ∀ n ∈ [P.H.hmacInitN, P.H.updN, P.H.hmacFinN], n ∈ ns) :
    ConstantTime isa (rfcP P ns).pre (rfcP P ns).pub (cfgOf P).sign := by
  rw [sign_eq]
  refine VG.RelCT.constantTime (Q := fun _ _ => True) (RelCT.frame (R := fun _ _ => True) (fun _ _ h => h.2.2.1) ?_)
  refine body_ct.mono (fun a b ⟨s₁, s₂, ⟨p₁, p₂, hsp, hdi, hsi, hdx, hcx, h9, hres, hsy, hns'⟩, ea, eb⟩ => ?_)
    fun _ _ _ => trivial
  subst ea eb
  have hsy' : (fun n => if n ∈ P.R.E.combConsts.map Prod.fst then s₁.syms n else 0) =
      fun n => if n ∈ P.R.E.combConsts.map Prod.fst then s₂.syms n else 0 := funext fun n => by
    split
    · next h => obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h; exact hsy c hc
    · rfl
  have hfa : (fun n => if n ∈ [P.H.hmacInitN, P.H.updN, P.H.hmacFinN] then s₁.syms n else 0) =
      fun n => if n ∈ [P.H.hmacInitN, P.H.updN, P.H.hmacFinN] then s₂.syms n else 0 :=
    funext fun n => by
      split
      · next h => exact hns' n (hns n h)
      · rfl
  have hl : layOf P s₁ = layOf P s₂ := by
    unfold layOf lay; rw [hsp, hdi, hsi, hdx, hcx, h9, hsy', hfa]
  have hr : (result P.I s₁.mem (s₁.gpr .rsi) (s₁.gpr .rdx)).2 = (result P.I s₂.mem (s₁.gpr .rsi) (s₁.gpr .rdx)).2 := by
    rw [hres, hsi, hdx]
  refine ⟨⟨layOf P s₁, s₁.gpr, s₂.gpr, s₁.mem, s₂.mem⟩, lay_ok rfl p₁, coreOk_lay P s₁,
    congrArg (fun x => if x = 0 then P.I.tries - 1 else x - 1) hr,
    push_ctx rfl p₁, by rw [hl]; exact push_ctx rfl p₂, trivial, trivial⟩

end VG.Proof.Ecdsa.Rfc6979.X86_64

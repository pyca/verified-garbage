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

end VG.Proof.Ecdsa.Rfc6979.X86_64

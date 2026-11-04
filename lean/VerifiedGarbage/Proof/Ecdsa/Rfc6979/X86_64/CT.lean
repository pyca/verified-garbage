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
(the taint analysis, of the blocks for each size of hash function: `RfcT`,
each curve's `RfcCurve.blkT`); an indirect call reaches, through the
table, whose address the frame holds, the same function in both runs
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
theorem CoreOk.tabL {L : Lay P.I.hashLen} (hk : CoreOk P L) : TabL P L := ⟨hk.2.2.2.2.1, hk.2.2.2.2.2, hk.2.2.1⟩

/-! ## The indirect calls -/

/-- What an indirect call of `n` needs of the table in each run: its word
`j` (on entry) is `n`'s address, which is the layout's, and of `f`'s
functions an indirect call reaches `n`'s `c`. -/
def TabFn (P : RfcHash) (j : Nat) (n : String) (c : Prog isa) (ts : List (String × Prog isa)) : Prop :=
  ∀ (L : Lay P.I.hashLen) g m₀ (t : State), L.Ok → CoreOk P L → Ctx L g m₀ t →
    m₀.readW (L.tab + BitVec.ofNat 64 (8 * j)) 64 = t.syms n ∧
      ts.find? (fun q => t.syms q.1 == t.syms n) = some (n, c) ∧ t.syms n = L.fa n

theorem tfn_init : TabFn P 0 P.H.stream.initN P.H.stream.initC P.f.init := fun L _ _ _ _ hk hc => by
  have hok := hc.tabOk; have htm := hc.tabMem; have hf := hc.fsy
  rw [hk.2.2.2.2.1, hk.2.2.2.2.2] at hok; rw [hk.2.2.2.2.1] at htm hf
  exact ⟨htm.1, hok.1, hf _ (by simp)⟩

theorem tfn_upd : TabFn P 1 P.H.stream.updN P.H.stream.updC P.f.upd := fun L _ _ _ _ hk hc => by
  have hok := hc.tabOk; have htm := hc.tabMem; have hf := hc.fsy
  rw [hk.2.2.2.2.1, hk.2.2.2.2.2] at hok; rw [hk.2.2.2.2.1] at htm hf
  exact ⟨htm.2.1, hok.2.1, hf _ (by simp)⟩

theorem tfn_fin : TabFn P 2 P.H.stream.finN P.H.stream.finC P.f.fin := fun L _ _ _ _ hk hc => by
  have hok := hc.tabOk; have htm := hc.tabMem; have hf := hc.fsy
  rw [hk.2.2.2.2.1, hk.2.2.2.2.2] at hok; rw [hk.2.2.2.2.1] at htm hf
  exact ⟨htm.2.2, hok.2.2, hf _ (by simp)⟩

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
theorem tcall_piece {Φ Ψ : Pr P} {j : Nat} (hj : 8 * j + 8 ≤ 40) {n : String} {c : Prog isa}
    {ts : List (String × Prog isa)} (hn : TabFn P j n c ts) (hΦ : R11 Φ) (hcall : Piece P Φ (.call n c) Ψ) :
    Piece P Φ ((cfgOf P).tcall j ts) Ψ := by
  refine ⟨?_, fun L g m₀ t hL hk hc hφ => ?_⟩
  · unfold Cfg.tcall
    have s₁ : Piece P Φ (.block [.mov .r11 (.mem (stk (cfgOf P).fTab))]) fun L m₀ u =>
        Φ L m₀ u ∧ u.gpr .r11 = L.tab :=
      Piece.blkS (tblk1_taint _) fun L g m₀ t hL hk hc hφ =>
        WP.mono (tblk1_ok hL hk.tabL hc) fun u ⟨hc', hm, h11, hr, hs⟩ => ⟨hc', hΦ _ _ _ _ hφ hr hm hs, h11⟩
    have s₂ : Piece P (fun L m₀ u => Φ L m₀ u ∧ u.gpr .r11 = L.tab) (.block [.mov .r11 (.mem (at_ .r11 (8 * j)))])
        fun L m₀ u => Φ L m₀ u ∧ u.gpr .r11 = L.fa n ∧ u.syms n = L.fa n ∧
          ts.find? (fun q => u.syms q.1 == u.syms n) = some (n, c) :=
      Piece.blk [.r11] (fun _ _ _ _ _ _ _ _ _ f₁ f₂ r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact f₁.2.trans f₂.2.symm) (tblk2_taint _)
        fun L g m₀ t hL hk hc ⟨hφ, h11⟩ => WP.mono (tblk2_ok hL hc h11 hj) fun u ⟨hc', hm, h11', hr, hs⟩ => by
          obtain ⟨hw, hf, hfa⟩ := hn L g m₀ t hL hk hc
          exact ⟨hc', hΦ _ _ _ _ hφ hr hm hs, by rw [h11', hw, hfa], by rw [hs, hfa], by rw [hs]; exact hf⟩
    refine s₁.ct.seq (s₂.ct.seq ?_)
    cases ts with
    | nil => exact RelCT.of_false fun _ _ ⟨_, _, _, _, _, _, f₁, _⟩ => by simp at f₁
    | cons q ts =>
      exact RelCT.icalls_of_call (hcall.ct.mono (fun _ _ => Two.mono fun _ _ _ h => h.1) fun _ _ h => h)
        fun s₁ s₂ ⟨e, _, _, _, _, _, f₁, f₂⟩ => ⟨e.1.fa n, by simp only [X86_64.icall, f₁.2.1],
          by simp only [X86_64.icall, f₂.2.1],
          by show (q :: ts).find? (fun p => s₁.syms p.1 == e.1.fa n) = _; rw [← f₁.2.2.1]; exact f₁.2.2.2,
          by show (q :: ts).find? (fun p => s₂.syms p.1 == e.1.fa n) = _; rw [← f₂.2.2.1]; exact f₂.2.2.2, rfl⟩
  · obtain ⟨hw, hf, -⟩ := hn L g m₀ t hL hk hc
    exact tcall_ok hL hk.tabL hc hj hw hf fun t' hc' hm hr hs =>
      hcall.wp L g m₀ t' hL hk hc' (hΦ _ _ _ _ hφ hr hm hs)

/-! ## The streaming calls -/

/-- A call related in two runs with the same layout. -/
theorem two_call {Φ : Pr P} {n : String} {c : Prog isa}
    (h : ∀ L : Lay P.I.hashLen, RelCT isa (fun s₁ s₂ => ∃ g₁ g₂ m₁ m₂, L.Ok ∧ CoreOk P L ∧ Ctx L g₁ m₁ s₁ ∧
      Ctx L g₂ m₂ s₂ ∧ Φ L m₁ s₁ ∧ Φ L m₂ s₂) (.call n c) fun _ _ => True) :
    RelCT isa (Two P Φ) (.call n c) fun _ _ => True :=
  (RelCT.exists_ h).mono (fun _ _ ⟨⟨L, g₁, g₂, m₁, m₂⟩, hL, hk, _, c₁, c₂, f₁, f₂⟩ =>
    ⟨L, g₁, g₂, m₁, m₂, hL, hk, c₁, c₂, f₁, f₂⟩) fun _ _ h => h

/-- `init`'s argument: the state at `scratch + o`. -/
def IA (P : RfcHash) (o : Nat) : Pr P := fun L _ u => u.gpr .rdi = L.scr + BitVec.ofNat 64 o

theorem init_piece {o : Nat} (ho : o + 192 ≤ 384) :
    Piece P (IA P o) (.call P.H.stream.initN P.H.stream.initC) (Tt P) :=
  Piece.of (two_call fun L => Proof.Pbkdf2.Md.X86_64.Calls.init_rel P.ok.stream (st := L.scr + BitVec.ofNat 64 o)
      fun _ _ ⟨_, _, _, _, hL, _, c₁, c₂, d₁, d₂⟩ =>
    have cov : ∀ {g m₀} {u : State}, Ctx L g m₀ u → Covers [⟨L.scr + BitVec.ofNat 64 o, P.H.stream.S⟩] u.wr :=
      fun hc => hc.coversW fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨L.SCR, by simp, within_off _ (by nums)⟩
    ⟨d₁, d₂, cov c₁, cov c₂, (hL.low_scr (by nums)).sub_left (c₁.below_sub (by omega)),
      (hL.low_scr (by nums)).sub_left (c₂.below_sub (by omega)), rsp_two c₁ c₂⟩)
    fun _ _ _ _ hL _ hc hd => WP.mono (initRaw_ok hL hc ho hd) fun _ h => ⟨h.1, trivial⟩

/-- `update`'s arguments: the state at `scratch + o` holding `cnt` bytes,
the `len` bytes at `da`, and the working space. -/
def UA (P : RfcHash) (o cnt : Nat) (da : Lay P.I.hashLen → Addr) (len : Nat) : Pr P := fun L _ u =>
  u.gpr .rdi = L.scr + BitVec.ofNat 64 o ∧ u.gpr .rsi = BitVec.ofNat 64 cnt ∧ u.gpr .rdx = da L ∧
    u.gpr .rcx = BitVec.ofNat 64 len ∧ u.gpr .r8 = L.scr + BitVec.ofNat 64 384

theorem upd_piece {o cnt : Nat} (ho : o + 192 ≤ 384) {da : Lay P.I.hashLen → Addr} {len : Nat}
    (hd : ∀ L : Lay P.I.hashLen, L.Ok → UpdData P L o (da L) len) (hlen : len < 2 ^ 32) :
    Piece P (UA P o cnt da len) (.call P.H.stream.updN P.H.stream.updC) (Tt P) :=
  Piece.of (two_call fun L => Proof.Pbkdf2.Md.X86_64.Calls.upd_rel P.ok.stream fun _ _ ⟨_, _, _, _, hL, _, c₁, c₂,
      ⟨d₁, s₁, x₁, k₁, r₁⟩, ⟨d₂, s₂, x₂, k₂, r₂⟩⟩ =>
    ⟨updArgsOf hL c₁ ho (hd L hL) hlen d₁ x₁ k₁ r₁, updArgsOf hL c₂ ho (hd L hL) hlen d₂ x₂ k₂ r₂, s₁.trans s₂.symm,
      rsp_two c₁ c₂⟩)
    fun _ _ _ _ hL _ hc ⟨d, s, x, k, r⟩ =>
      WP.mono (updRaw_ok hL hc ho (updArgsOf hL hc ho (hd _ hL) hlen d x k r) hlen s) fun _ h => ⟨h.1, trivial⟩

/-- `finalize`'s arguments: the state at `scratch + o` holding `cnt` bytes,
the output at `scratch + sTmp`, and the working space. -/
def FA (P : RfcHash) (o cnt : Nat) : Pr P := fun L _ u =>
  u.gpr .rdi = L.scr + BitVec.ofNat 64 o ∧ u.gpr .rsi = BitVec.ofNat 64 cnt ∧
    u.gpr .rdx = L.scr + BitVec.ofNat 64 1920 ∧ u.gpr .rcx = L.scr + BitVec.ofNat 64 384

theorem fin_piece {o cnt : Nat} (ho : o + 192 ≤ 384) (hcnt : cnt < 2 ^ 32) :
    Piece P (FA P o cnt) (.call P.H.stream.finN P.H.stream.finC) (Tt P) :=
  Piece.of (two_call fun _ => Proof.Pbkdf2.Md.X86_64.Calls.fin_rel P.ok.stream fun _ _ ⟨_, _, _, _, hL, _, c₁, c₂,
      ⟨d₁, s₁, x₁, k₁⟩, ⟨d₂, s₂, x₂, k₂⟩⟩ =>
    ⟨finArgsOf (P := P) hL c₁ ho d₁ x₁ k₁, finArgsOf (P := P) hL c₂ ho d₂ x₂ k₂, s₁.trans s₂.symm, rsp_two c₁ c₂⟩)
    fun _ _ _ _ hL _ hc ⟨d, s, x, k⟩ =>
      WP.mono (finRaw_ok hL hc ho (finArgsOf (P := P) hL hc ho d x k) hcnt s) fun _ h => ⟨h.1, trivial⟩

theorem r11_ia {o : Nat} : R11 (IA P o) := fun _ _ _ _ h hr _ _ => (hr _ (by decide)).trans h

theorem r11_ua {o cnt : Nat} {da : Lay P.I.hashLen → Addr} {len : Nat} : R11 (UA P o cnt da len) :=
  fun _ _ _ _ ⟨d, s, x, k, r⟩ hr _ _ => ⟨(hr _ (by decide)).trans d, (hr _ (by decide)).trans s,
    (hr _ (by decide)).trans x, (hr _ (by decide)).trans k, (hr _ (by decide)).trans r⟩

theorem r11_fa {o cnt : Nat} : R11 (FA P o cnt) :=
  fun _ _ _ _ ⟨d, s, x, k⟩ hr _ _ => ⟨(hr _ (by decide)).trans d, (hr _ (by decide)).trans s,
    (hr _ (by decide)).trans x, (hr _ (by decide)).trans k⟩

theorem scr_taint (d : Reg) (a : Nat) : TaintOk [.rsp] (Cfg.scr d a) :=
  taintOk_erase (is₀ := Cfg.scr d 0) (by cases d <;> exact ⟨_, by taint_decide⟩) rfl

/-- `init` of the state at `scratch + o`, through the table. -/
theorem initCall_piece {Φ : Pr P} {o : Nat} (ho : o + 192 ≤ 384) : Piece P Φ ((cfgOf P).initCall o) (Tt P) :=
  (Piece.blkS (Ψ := IA P o) (scr_taint .rdi o) fun _ _ _ _ hL _ hc _ =>
    WP.mono (scr_ok hL hc (d := .rdi) (by decide) (a := o) (by omega)) fun _ h => ⟨h.ctx, h.val⟩).seq
    (tcall_piece (by decide) tfn_init r11_ia (init_piece ho))

/-- The data block of `update`: the address of the data in `rdx`. -/
def DataA (P : RfcHash) (dataA : List Instr) (da : Lay P.I.hashLen → Addr) : Prop :=
  ∀ (L : Lay P.I.hashLen) g m₀ (u : State), L.Ok → Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .rdx (da L))

theorem updArgs_taint {o cnt : Nat} {dataA : List Instr} {len : Nat} (ht : TaintOk [.rsp] (Cfg.updArgs 0 0 dataA 0))
    : TaintOk [.rsp] (Cfg.updArgs o cnt dataA len) :=
  taintOk_erase ht (by simp only [Cfg.updArgs, Cfg.scr, List.map_append]; rfl)

/-- `update` of the state at `scratch + o`, holding `cnt` bytes, with `len`
bytes at `da`, through the table. -/
theorem updCall_piece {Φ : Pr P} {o cnt : Nat} (ho : o + 192 ≤ 384) {dataA : List Instr}
    {da : Lay P.I.hashLen → Addr} {len : Nat} (hdA : DataA P dataA da)
    (hd : ∀ L : Lay P.I.hashLen, L.Ok → UpdData P L o (da L) len) (ht : TaintOk [.rsp] (Cfg.updArgs 0 0 dataA 0))
    (hcnt : cnt < 2 ^ 32) (hlen : len < 2 ^ 32) :
    Piece P Φ ((cfgOf P).updCall o cnt dataA len) (Tt P) :=
  (Piece.blkS (Ψ := UA P o cnt da len) (updArgs_taint ht) fun L g m₀ _ hL _ hc _ =>
    WP.mono (updArgs_ok hL hc (o := o) (by omega) (fun u hu => hdA L g m₀ u hL hu) hcnt hlen)
      fun _ ⟨c, _, d, s, x, k, r⟩ => ⟨c, d, s, x, k, r⟩).seq
    (tcall_piece (by decide) tfn_upd r11_ua (upd_piece ho hd hlen))

theorem finArgs_taint (o cnt : Nat) : TaintOk [.rsp] (Cfg.finArgs o cnt) :=
  taintOk_erase (is₀ := Cfg.finArgs 0 0) ⟨_, by taint_decide⟩
    (by simp only [Cfg.finArgs, Cfg.scr, List.map_append]; rfl)

/-- `finalize` of the state at `scratch + o`, holding `cnt` bytes, through the table. -/
theorem finCall_piece {Φ : Pr P} {o cnt : Nat} (ho : o + 192 ≤ 384) (hcnt : cnt < 2 ^ 32) :
    Piece P Φ ((cfgOf P).finCall o cnt) (Tt P) :=
  (Piece.blkS (Ψ := FA P o cnt) (finArgs_taint o cnt) fun _ _ _ _ hL _ hc _ =>
    WP.mono (finArgs_ok hL hc ho hcnt) fun _ ⟨c, _, d, s, x, k⟩ => ⟨c, d, s, x, k⟩).seq
    (tcall_piece (by decide) tfn_fin r11_fa (fin_piece ho hcnt))

/-! ## Blocks from `scratch`'s pointer -/

/-- `scratch` in `rdi`. -/
def ScrIn (P : RfcHash) : Pr P := fun L _ u => u.gpr .rdi = L.scr

theorem scrPtr_piece {Φ : Pr P} : Piece P Φ (.block Cfg.scrPtr) (ScrIn P) :=
  Piece.blkS ⟨_, by taint_decide⟩ fun _ _ _ _ hL _ hc _ => WP.mono (scrPtr_ok hL hc) fun _ h => ⟨h.1, h.2.2⟩

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

/-! ## HMAC -/

/-- The blocks of the curve and the hash function's sizes. -/
theorem rT (P : RfcHash) : RfcT (cfgS P.R.E P.R.hHigh P.R.sh P.H.D P.H.P.B) := P.R.blkT _ _ P.hDB

/-- `K₀ ⊕ c` at `scratch + sPad`. -/
theorem padBlk_piece {Φ : Pr P} (c : Byte) : Piece P Φ (.block ((cfgOf P).padBlk (c ++ c ++ c ++ c))) (Tt P) := by
  have e : (cfgOf P).padBlk (c ++ c ++ c ++ c) = Cfg.scrPtr ++ (([.mov32 .rcx (.imm (c ++ c ++ c ++ c))] : List Instr) ++
      (List.range ((cfgOf P).B / 4)).flatMap (cfgOf P).padW) := by
    simp only [Cfg.padBlk, List.append_assoc]
  rw [e]
  refine Piece.scrBlk (taintOk_erase (by exact (rT P).pad) (by simp only [List.map_append]; rfl))
    fun _ _ _ _ hL _ hc _ => ?_
  rw [← e]
  exact WP.mono (padBlk_ok hL hc c) fun _ h => ⟨h.1, trivial⟩

theorem updScr_taint (a : Nat) : TaintOk [.rsp] (Cfg.updArgs 0 0 (Cfg.scr .rdx a) 0) :=
  taintOk_erase (is₀ := Cfg.updArgs 0 0 (Cfg.scr .rdx 0) 0) ⟨_, by taint_decide⟩
    (by simp only [Cfg.updArgs, Cfg.scr, List.map_append]; rfl)

theorem updFr_taint (a : Nat) : TaintOk [.rsp] (Cfg.updArgs 0 0 (Cfg.fr .rdx a) 0) :=
  taintOk_erase (is₀ := Cfg.updArgs 0 0 (Cfg.fr .rdx 0) 0) ⟨_, by taint_decide⟩
    (by simp only [Cfg.updArgs, Cfg.scr, Cfg.fr, List.map_append]; rfl)

/-- Data at `scratch + a`. -/
theorem scrDA (a : Nat) (ha : a < 2 ^ 31) : DataA P (Cfg.scr .rdx a) fun L => L.scr + BitVec.ofNat 64 a :=
  fun _ _ _ _ hL hu => scr_ok hL hu (d := .rdx) (by decide) ha

/-- Data in the frame at `o`. -/
theorem frDA (o : Nat) (ho : o < 2 ^ 31) : DataA P (Cfg.fr .rdx o) fun L => L.B + BitVec.ofNat 64 (24 + o) :=
  fun _ _ _ _ hL hu => fr_ok hL hu (d := .rdx) (by decide) ho

/-- `hinit`: each state set by `init` and updated with its padded key. -/
theorem hinit_piece {Φ : Pr P} : Piece P Φ (cfgOf P).hinit (Tt P) := by
  unfold Cfg.hinit
  rw [ipad32_eq, opad32_eq]
  exact (initCall_piece (by decide)).seq ((initCall_piece (by decide)).seq ((padBlk_piece _).seq
    ((updCall_piece (by decide) (scrDA 1792 (by decide)) (fun _ hL => padData hL (by decide)) (updScr_taint _)
      (by decide) (by show P.H.P.B < 2 ^ 32; nums)).seq ((padBlk_piece _).seq
    (updCall_piece (by decide) (scrDA 1792 (by decide)) (fun _ hL => padData hL (by decide)) (updScr_taint _)
      (by decide) (by show P.H.P.B < 2 ^ 32; nums))))))

/-- `hupd`: the inner state updated with the data. -/
theorem hupd_piece {Φ : Pr P} {dataA : List Instr} {da : Lay P.I.hashLen → Addr} {len : Nat}
    (hdA : DataA P dataA da) (hd : ∀ L : Lay P.I.hashLen, L.Ok → DataOk L (da L) len)
    (ht : TaintOk [.rsp] (Cfg.updArgs 0 0 dataA 0)) (hlen : len ≤ 256) :
    Piece P Φ ((cfgOf P).hupd dataA len) (Tt P) := by
  unfold Cfg.hupd
  simp only [show (cfgOf P).B = P.H.P.B from rfl, sInner]
  exact updCall_piece (by decide) hdA (fun L hL => (hd L hL).upd hL) ht (by nums) (by omega)

theorem hfinCopy_taint (dst : Nat) : TaintOk [.rsp, .rdi] (Cfg.copyBytes (cfgOf P).D .rdi sTmp .rsp dst) :=
  taintOk_erase (is₀ := Cfg.copyBytes (cfgOf P).D .rdi sTmp .rsp 0) (by exact (rT P).hfinCopy)
    (by simp only [Cfg.copyBytes, Cfg.copyN, List.map_append, List.map_flatMap]; split <;> rfl)

/-- The MAC's copy to the frame. -/
theorem hcopy_piece {Φ : Pr P} {dst : Nat} (hdst : dst + P.H.D ≤ 168) :
    Piece P Φ (.block (Cfg.scrPtr ++ Cfg.copyBytes (cfgOf P).D .rdi sTmp .rsp dst)) (Tt P) :=
  Piece.scrBlk (hfinCopy_taint dst) fun L _ _ _ hL _ hc _ => by
    rw [WP.block_append_iff]
    refine WP.mono (scrPtr_ok hL hc) fun w₄ ⟨hc₄, _, hdi₄⟩ => ?_
    have hsep : Region.Disjoint ⟨L.scr + BitVec.ofNat 64 1920, P.H.D⟩
        ⟨L.B + BitVec.ofNat 64 24 + BitVec.ofNat 64 dst, P.H.D⟩ := by
      rw [Offset.add_add]; exact (hL.stk_scr (by nums) (by nums)).symm
    refine WP.mono_syms (copyBytes_ok (src := .rdi) (dst := .rsp) (S := L.scr) (D := L.B + BitVec.ofNat 64 24)
      (so := 1920) (d := dst) (Q := P.H.D) (by decide) (by decide) hsep (by nums) (by nums) (by omega) hdi₄ hc₄.rsp
      (fun j hj => hc₄.inScr (by nums)) (fun j hj => by
        rw [Offset.add_add]; exact hc₄.inFrW (by omega) (by omega)))
      fun w₅ ⟨hrd₅, hwr₅, hg₅, hf₅, _⟩ hsy₅ => ?_
    rw [Offset.add_add] at hf₅
    exact ⟨hc₄.keep hL hrd₅ hwr₅ (hg₅ _ (by decide)) (fun r hr _ => hg₅ r (ne_cs hr (by decide))) hf₅
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega)) hsy₅, trivial⟩

/-- `hfin`: the MAC, for `len` bytes of data, to the frame at `dst`. -/
theorem hfin_piece {Φ : Pr P} {len dst : Nat} (hlen : len ≤ 256) (hdst : dst + P.H.D ≤ 168) :
    Piece P Φ ((cfgOf P).hfin len dst) (Tt P) := by
  unfold Cfg.hfin
  simp only [show (cfgOf P).B = P.H.P.B from rfl, show (cfgOf P).D = P.H.D from rfl, sInner, sOuter]
  exact (finCall_piece (by decide) (by nums)).seq ((updCall_piece (by decide) (scrDA 1920 (by decide))
    (fun L hL => ⟨⟨L.SCR, by simp, within_off _ (by nums)⟩, Offset.disjoint _ (by nums) (by nums) (by nums),
      Offset.disjoint _ (by nums) (by nums) (by nums), hL.low_scr (by nums)⟩) (updScr_taint _) (by nums)
      (by nums)).seq ((finCall_piece (by decide) (by nums)).seq (hcopy_piece hdst)))

theorem copyStates_taint (b : Bool) : TaintOk [.rsp, .rdi] (Cfg.copyStates b) := by
  cases b
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩

/-- HMAC's states saved, or restored. -/
theorem copyStates_piece {Φ : Pr P} (b : Bool) : Piece P Φ (.block (Cfg.scrPtr ++ Cfg.copyStates b)) (Tt P) :=
  Piece.scrBlk (copyStates_taint b) fun L _ _ _ hL _ hc _ => by
    rw [WP.block_append_iff]
    refine WP.mono (scrPtr_ok hL hc) fun u ⟨hcu, _, hdi⟩ => ?_
    cases b
    · exact WP.mono (copy_ok hL hcu (src := .rdi) (S := L.scr) hdi (by decide) hdi (so := 3072) (d := 0) (K := 48)
        (by decide) (fun j hj => hcu.inScr (by omega)) (Offset.disjoint _ (by decide) (by decide) (by decide)))
        fun _ h => ⟨h.1, trivial⟩
    · exact WP.mono (copy_ok hL hcu (src := .rdi) (S := L.scr) hdi (by decide) hdi (so := 0) (d := 3072) (K := 48)
        (by decide) (fun j hj => hcu.inScr (by omega)) (Offset.disjoint _ (by decide) (by decide) (by decide)))
        fun _ h => ⟨h.1, trivial⟩

section Mac

variable {Φ : Pr P} {dataA : List Instr} {da : Lay P.I.hashLen → Addr} {len dst : Nat}
  (hdA : DataA P dataA da) (hd : ∀ L : Lay P.I.hashLen, L.Ok → DataOk L (da L) len)
  (ht : TaintOk [.rsp] (Cfg.updArgs 0 0 dataA 0)) (hlen : len ≤ 256) (hdst : dst + P.H.D ≤ 168)
include hdA hd ht hlen hdst

theorem hmac_piece : Piece P Φ ((cfgOf P).hmac dataA len dst) (Tt P) :=
  hinit_piece.seq ((hupd_piece hdA hd ht hlen).seq (hfin_piece hlen hdst))

theorem hmacS_piece : Piece P Φ ((cfgOf P).hmacS dataA len dst) (Tt P) :=
  hinit_piece.seq ((copyStates_piece true).seq ((hupd_piece hdA hd ht hlen).seq (hfin_piece hlen hdst)))

theorem hmacR_piece : Piece P Φ ((cfgOf P).hmacR dataA len dst) (Tt P) :=
  (copyStates_piece false).seq ((hupd_piece hdA hd ht hlen).seq (hfin_piece hlen hdst))

end Mac

theorem vData (L : Lay P.I.hashLen) : DataOk L (L.B + BitVec.ofNat 64 (24 + 64)) P.H.D :=
  .inl ⟨88, rfl, by omega, by nums⟩

theorem hmacVS_piece {Φ : Pr P} : Piece P Φ (cfgOf P).hmacVS (Tt P) :=
  hmacS_piece (frDA 64 (by decide)) (fun L _ => vData L) (updFr_taint _) (by show P.H.D ≤ 256; nums)
    (by show 64 + P.H.D ≤ 168; nums)

theorem hmacVR_piece {Φ : Pr P} : Piece P Φ (cfgOf P).hmacVR (Tt P) :=
  hmacR_piece (frDA 64 (by decide)) (fun L _ => vData L) (updFr_taint _) (by show P.H.D ≤ 256; nums)
    (by show 64 + P.H.D ≤ 168; nums)

/-- `K = HMAC_K(m)`, for the message of `len` bytes at `scratch + 2256`, from
the saved states if `rs`. -/
theorem hmacK_piece {Φ : Pr P} {len : Nat} (hlen : len ≤ 256) (rs : Bool) :
    Piece P Φ ((if rs then (cfgOf P).hmacR else (cfgOf P).hmac) (Cfg.scr .rdx sMsg) len fK) (Tt P) := by
  cases rs
  · exact hmac_piece (scrDA 2256 (by decide)) (fun _ _ => .inr ⟨2256, rfl, by omega, by omega⟩) (updScr_taint _)
      hlen (by show 0 + P.H.D ≤ 168; nums)
  · exact hmacR_piece (scrDA 2256 (by decide)) (fun _ _ => .inr ⟨2256, rfl, by omega, by omega⟩) (updScr_taint _)
      hlen (by show 0 + P.H.D ≤ 168; nums)

/-! ## `K` and `V` from a message -/

/-- `scratch` in `rdi` and `d` in `rsi`. -/
def PtrsIn (P : RfcHash) : Pr P := fun L _ u => u.gpr .rdi = L.scr ∧ u.gpr .rsi = L.d

theorem msgPtrs_piece {Φ : Pr P} : Piece P Φ (.block Cfg.msgPtrs) (PtrsIn P) :=
  Piece.blkS ⟨_, by taint_decide⟩ fun _ _ _ _ hL _ hc _ =>
    WP.mono (ptrs_ok hL hc) fun _ ⟨c, _, d, s⟩ => ⟨c, d, s⟩

/-- The message `V ‖ b (‖ d ‖ h)` at `scratch + sMsg`. -/
theorem msg_piece {b : Nat} {full : Bool} {ho : Nat} (hho : full = true → ho = P.hB - 24)
    (ht : TaintOk [.rsp, .rdi, .rsi] (Cfg.msg P.Q P.H.D b full ho)) :
    Piece P (PtrsIn P) (.block (Cfg.msg P.Q P.H.D b full ho)) (Tt P) :=
  Piece.blk [.rsp, .rdi, .rsi] (fun _ _ _ _ _ _ _ c₁ c₂ f₁ f₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact rsp_two c₁ c₂
      · exact f₁.1.trans f₂.1.symm
      · exact f₁.2.trans f₂.2.symm) ht
    fun _ _ _ _ hL hk hc hp => WP.mono (msg_ok hL hc hp.1 hp.2 b full ho (D := P.H.D) (Q := P.Q) (by nums)
      (by nums) (by nums) (by nums) (hok_of hk).1 (fun hf => by rw [hho hf]; exact hB_fit (hok_of hk)))
      fun _ h => ⟨h.1, trivial⟩

theorem msgF_taint (b : Nat) : TaintOk [.rsp, .rdi, .rsi] (Cfg.msg P.Q P.H.D b true (cfgOf P).fHo) :=
  taintOk_erase (by exact (rT P).msgF) (by simp only [Cfg.msg, ↓reduceIte, List.map_append]; rfl)

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)`. -/
theorem rekeyFull_piece {Φ : Pr P} (b : Nat) : Piece P Φ ((cfgOf P).rekeyFull b) (Tt P) := by
  have hlen : P.H.D + 2 * P.Q + 1 ≤ 256 := by nums
  unfold Cfg.rekeyFull
  split
  · exact msgPtrs_piece.seq ((msg_piece (fun _ => fHo_eq P) (msgF_taint b)).seq
      ((hmacK_piece (len := P.H.D + 2 * P.Q + 1) hlen false).seq hmacVS_piece))
  · exact msgPtrs_piece.seq ((msg_piece (fun _ => fHo_eq P) (msgF_taint b)).seq
      ((hmacK_piece (len := P.H.D + 2 * P.Q + 1) hlen true).seq hmacVS_piece))

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)`. -/
theorem rekey_piece {Φ : Pr P} : Piece P Φ (cfgOf P).rekey (Tt P) := by
  have hlen : P.H.D + 1 ≤ 256 := by nums
  unfold Cfg.rekey
  exact msgPtrs_piece.seq ((msg_piece (fun h => absurd h (by decide)) (by exact (rT P).msgN)).seq
    ((hmacK_piece (len := P.H.D + 1) hlen false).seq hmacVS_piece))

/-! ## The candidate -/

theorem ce_rsp_two {dn : Nat} {L : Lay dn} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 64} {m₁ m₂ : Mem}
    (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) (rd₁ wr₁ rd₂ wr₂ : List Region) :
    (t₁.callEntry.withRegions rd₁ wr₁).gpr .rsp = (t₂.callEntry.withRegions rd₂ wr₂).gpr .rsp := by
  rw [State.withRegions_gpr, State.withRegions_gpr, State.callEntry_rsp, State.callEntry_rsp, rsp_two c₁ c₂]

theorem ce_two {t₁ t₂ : State} {r : Reg} (hr : r ≠ .rsp) {x : BitVec 64} (h₁ : t₁.gpr r = x) (h₂ : t₂.gpr r = x)
    (rd₁ wr₁ rd₂ wr₂ : List Region) :
    (t₁.callEntry.withRegions rd₁ wr₁).gpr r = (t₂.callEntry.withRegions rd₂ wr₂).gpr r := by
  rw [ce_gpr _ _ _ hr, ce_gpr _ _ _ hr, h₁, h₂]


/-- `V`'s `D` bytes to `T + k D`. -/
theorem keepV_piece {Φ : Pr P} (hw : P.wide = true) {k : Nat} (hkb : k * P.H.D + P.H.D ≤ 128) :
    Piece P Φ (.block ((cfgOf P).keepV k)) (Tt P) :=
  Piece.blkS (taintOk_erase (is₀ := (cfgOf P).keepV 0) (by exact (rT P).keepV)
      (by simp only [Cfg.keepV, Cfg.copyBytes, Cfg.copyN, List.map_append, List.map_flatMap]; split <;> rfl))
    fun L _ _ _ hL hk hc _ => by
      have he := e34 hk.2.2.1 hw
      have hsep : Region.Disjoint ⟨L.B + BitVec.ofNat 64 24 + BitVec.ofNat 64 64, P.H.D⟩
          ⟨L.B + BitVec.ofNat 64 (24 + (fT + k * (cfgOf P).D)), P.H.D⟩ := by
        rw [fr_add]; exact Offset.disjoint _ (by simp only [fT, cfgOf]; nums) (by nums)
          (by simp only [fT, cfgOf]; nums)
      exact WP.mono (copyBF_ok hL hc (src := .rsp) (S := L.B + BitVec.ofNat 64 24) hc.rsp (by decide) (so := fV)
        (d := fT + k * (cfgOf P).D) (Q := P.H.D) (by nums) (by simp only [fV]; nums) (by simp only [fT]; omega)
        (by simp only [fT, cfgOf]; rw [he]; nums)
        (fun j hj => by rw [fr_add]; exact hc.inFr (by simp only [fV]; omega) (by simp only [fV]; nums)) hsep)
        fun _ h => ⟨h.1, trivial⟩

/-- The first `k` `V`s of the candidate. -/
theorem candW_piece {Φ : Pr P} (hw : P.wide = true) : ∀ k, k * P.H.D ≤ 128 →
    Piece P Φ ((cfgOf P).candW k) (Tt P)
  | 0, _ => by
    rw [Cfg.candW]
    exact Piece.blkS ⟨_, by taint_decide⟩ fun _ _ _ t _ _ hc _ => WP.of_runBlock ⟨t, rfl, hc, trivial⟩
  | k + 1, hk => by
    have hk' : k * P.H.D + P.H.D ≤ 128 := by rw [Nat.succ_mul] at hk; exact hk
    rw [Cfg.candW]
    exact (candW_piece hw k (by omega)).seq (hmacVR_piece.seq (keepV_piece hw hk'))

/-- If `sh ≠ 0`: `T`'s first `Q` bytes shifted right by `sh` bits. -/
theorem candTop_piece {Φ : Pr P} (hw : P.wide = true) : Piece P Φ (.block (cfgOf P).candTop) (Tt P) := by
  by_cases hsh : P.R.sh = 0
  · have e : (cfgOf P).candTop = [] := by
      simp only [Cfg.candTop, show (cfgOf P).sh = 0 from hsh, ite_true]
    rw [e]
    exact Piece.blkS ⟨_, by taint_decide⟩ fun _ _ _ t _ _ hc _ => WP.of_runBlock ⟨t, rfl, hc, trivial⟩
  · have e : (cfgOf P).candTop = Cfg.scrPtr ++ (cfgOf P).conv fT (cfgOf P).sh := by
      simp only [Cfg.candTop, show (cfgOf P).sh = P.R.sh from rfl, hsh, ite_false]
    rw [e]
    refine Piece.scrBlk (by exact (rT P).candTop hsh) fun _ _ _ _ hL hk hc _ => ?_
    rw [← e]
    exact WP.mono (candTop_ok hL hk.2.2.1 hw hsh hc) fun _ h => ⟨h.1, trivial⟩

/-- The candidate: its calls and blocks leak the same in both runs. -/
theorem cand_piece {Φ : Pr P} : Piece P Φ (cfgOf P).cand (Tt P) := by
  cases hw : P.wide
  · simp only [Cfg.cand, cfgOf_wide, hw, Bool.false_eq_true, ite_false]
    exact hmacVR_piece
  · simp only [Cfg.cand, cfgOf_wide, hw, ite_true]
    exact (candW_piece hw _ (m_facts P hw).2).seq (candTop_piece hw)

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
          have hc' : c ∈ L.cs := by rw [hk.2.2.2.1]; exact hc
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
  refine (two_wp (Ψ := fun L m₀ u => P₁ P L m₀ i u) ((cand_piece (Φ := Tt P)).rel fun _ _ _ _ => trivial)
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

theorem loop_ct :
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

theorem initCnt_blk₀ : TaintOk [.rsp] (cfgC { n := 4, C := Spec.P256.curve }).initCnt := ⟨_, by taint_decide⟩

/-- The count's initial store, for any count: the analysis does not read
immediates (`taint_eraseInv`), so it is that of one count's. -/
theorem initCnt_blk (c : Cfg) : TaintOk [.rsp] c.initCnt := by
  obtain ⟨h, hs⟩ := initCnt_blk₀
  refine ⟨h, ?_⟩
  have e := (taint_eraseInv.check (.block c.initCnt) (Taint.ofRegs [.rsp]) h rfl).1
  have e₀ := (taint_eraseInv.check (.block (cfgC { n := 4, C := Spec.P256.curve }).initCnt)
    (Taint.ofRegs [.rsp]) h rfl).1
  rw [← e, show Code.mapBlocks Instr.erase (.block c.initCnt) =
    Code.mapBlocks Instr.erase (.block (cfgC { n := 4, C := Spec.P256.curve }).initCnt) from rfl, e₀]
  exact hs

/-- `digest` in `rsi`, and, if the hash is shorter than the scalars, `scratch` in `rdi`. -/
def DgIn (P : RfcHash) {dn : Nat} (L : Lay dn) (_ : Mem) (u : State) : Prop :=
  u.gpr .rsi = L.dg ∧ (P.wide = true → u.gpr .rdi = L.scr)

/-- Unless the hash is shorter, `bits2octets` is the curve's. -/
theorem reduce_eq (hw : P.wide = false) : (cfgOf P).reduce = (cfgC P.R.E P.R.hHigh).reduce := by
  have h₁ : (cfgC P.R.E P.R.hHigh).wide = false := by
    show decide (64 < P.Q) = false
    have := (P.sizesA hw).2.2
    simp only [decide_eq_false_iff_not]; nums
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
    exact two_blk [.rsp, .rsi] (fun _ _ _ _ _ _ _ c₁ c₂ f₁ f₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact rsp_two c₁ c₂
      · exact f₁.1.trans f₂.1.symm) (P.R.reduceT (P.curveA hw))
  · exact two_blk [.rsp, .rsi, .rdi] (fun _ _ _ _ _ _ _ c₁ c₂ f₁ f₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact rsp_two c₁ c₂
      · exact f₁.1.trans f₂.1.symm
      · exact (f₁.2 hw).trans (f₂.2 hw).symm) (by exact (rT P).prepW hw)

theorem body_ct :
    RelCT isa (Two P fun _ _ _ => True) (cfgOf P).body (Two P fun L m₀ t => ∃ i, Exit P L m₀ i t) := by
  refine (two_wp (Ψ := DgIn P) (two_blk [.rsp] rspOnly (by exact (rT P).digestPtr)) fun _ _ _ _ hL hk hc _ =>
    WP.mono (digestPtr_ok hL hc) fun _ h => ⟨h.1, h.2.2.1, h.2.2.2⟩).seq ?_
  refine (two_wp (Ψ := QB P) prep_ct fun _ _ _ _ hL hk hc h => stageB_ok (P := P) hL hk hc h.1 h.2).seq ?_
  refine (two_wp (Ψ := QC P) ((rekeyFull_piece 0).rel fun _ _ _ _ => trivial)
    fun _ _ _ _ hL hk hc h => stageC_ok (P := P) hL hk hc h).seq ?_
  refine (two_wp (Ψ := QD P) ((rekeyFull_piece 1).rel fun _ _ _ _ => trivial)
    fun _ _ _ _ hL hk hc h => stageD_ok (P := P) hL hk hc h).seq ?_
  refine (two_wp (Ψ := fun L m₀ t => LoopInv P L m₀ 0 t) (two_blk [.rsp] rspOnly (initCnt_blk _))
    fun _ _ _ _ hL hk hc h => stageE_ok (P := P) hL hk hc h).seq ?_
  refine loop_ct.seq ?_
  exact two_wp (two_blk [.rsp] rspOnly (by exact (rT P).wipe)) fun _ _ _ _ hL hk hc ⟨i, h⟩ =>
    WP.mono (stageG_ok hL hk hc h) fun _ ⟨c, x⟩ => ⟨c, i, x⟩

/-! ## The whole function -/

/-- Runs whose public data agree (with the addresses of the hash function's
functions among `ns`) have the same layout, and stop at the same candidate. -/
theorem sign_ct {ns : List String} (hns : ∀ n ∈ [P.H.stream.initN, P.H.stream.updN, P.H.stream.finN], n ∈ ns) :
    ConstantTime isa (rfcP P ns).pre (rfcP P ns).pub (cfgOf P).sign := by
  have he : P.e ≤ 34 := by nums
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
  have hfa : (fun n => if n ∈ [P.H.stream.initN, P.H.stream.updN, P.H.stream.finN] then s₁.syms n else 0) =
      fun n => if n ∈ [P.H.stream.initN, P.H.stream.updN, P.H.stream.finN] then s₂.syms n else 0 :=
    funext fun n => by
      split
      · next h => exact hns' n (hns n h)
      · rfl
  have hl : lay P.I.hashLen P.I.ecdsa.curve.len P.e he P.R.E.combConsts P.H.stream P.f s₁ =
      lay P.I.hashLen P.I.ecdsa.curve.len P.e he P.R.E.combConsts P.H.stream P.f s₂ := by
    unfold lay; rw [hsp, hdi, hsi, hdx, hcx, h9, hsy', hfa]
  have hr : (result P.I s₁.mem (s₁.gpr .rsi) (s₁.gpr .rdx)).2 = (result P.I s₂.mem (s₁.gpr .rsi) (s₁.gpr .rdx)).2 := by
    rw [hres, hsi, hdx]
  refine ⟨⟨lay P.I.hashLen P.I.ecdsa.curve.len P.e he P.R.E.combConsts P.H.stream P.f s₁, s₁.gpr, s₂.gpr, s₁.mem,
    s₂.mem⟩, lay_ok he p₁, coreOk_lay P he s₁, congrArg (fun x => if x = 0 then P.I.tries - 1 else x - 1) hr,
    push_ctx he p₁, by rw [hl]; exact push_ctx he p₂, trivial, trivial⟩

end VG.Proof.Ecdsa.Rfc6979.X86_64

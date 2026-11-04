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
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Calls
meta import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Calls

/-!
# Deterministic ECDSA on x86-64: constant time, up to the number of candidates

Two runs whose public data agree have the same layout, and stop at the same
candidate (`exitAt`, from the contract's leakage: the number of candidates
RFC 6979 tries). Between the frame's push and pop they are related by `Two`:
both satisfy `Ctx` with that layout (and `Φ`, what the next piece needs). The
blocks address only the stack and the buffers, from registers that agree
(the taint analysis, of the blocks for each size of hash function: `Blks`);
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

end VG.Proof.Ecdsa.Rfc6979.X86_64

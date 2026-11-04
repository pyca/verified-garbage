module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Correct
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.TaintErase
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.ICall
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Wide
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Msg
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Args
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Entry
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Step
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Copy
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Correct
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.TaintErase
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Call
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
meta import VerifiedGarbage.Proof.Framework.ICall
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Mont.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Wide
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Msg
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Args
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Entry
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Step
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Copy

/-!
# Deterministic ECDSA on PPC64LE: constant time, up to the number of candidates

Two runs whose public data agree have the same layout, and stop at the same
candidate (`exitAt`, from the contract's leakage: the number of candidates
RFC 6979 tries). Between the frames' pushes and pops they are related by
`Two`: both satisfy `Ctx` with that layout, with the table's facts (`SyOk`),
and `Φ`, what the next piece needs. The blocks address only the frame, from
`sp`, and the buffers, from pointers loaded from the frame, which agree (the
taint analysis of the rest of the block, from the registers that hold them:
`two_split`; of the blocks that depend on the sizes, `HBlks` and `CBlks`);
an indirect call reaches, through the table, whose address the frame holds,
the same function in both runs (`tcall_piece`); each call is of
constant-time code whose public data agree (`RelCT.callEx`); and the loop's
branch agrees, since in both runs it goes on after candidate `i` iff `i` is
before the candidate it stops at (`go_iff`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.Rfc6979.PPC64LE
open VG.Proof.Mont.PPC64LE (Kp)
open VG.Proof.Hmac.Stream.PPC64LE (initK updK finK)

/-! ## Two runs -/

/-- What the proof needs of each run at a point of the code. -/
abbrev Pred (P : Rfc) := Lay P.I.hashLen → (Reg → BitVec 64) → Addr → Mem → State → Prop

/-- Nothing. -/
abbrev Tt (P : Rfc) : Pred P := fun _ _ _ _ _ => True

/-- What each run has: the layout of the instance, and `Ctx` and the
table's facts. -/
structure Run (P : Rfc) (L : Lay P.I.hashLen) (g : Reg → BitVec 64) (lr : Addr) (m₀ : Mem) (t : State) :
    Prop where
  ok : L.Ok
  q : L.q = P.c.len
  gf : L.G = P.K.H ∧ L.f = P.K.f
  c : Ctx L g lr m₀ t
  y : SyOk L m₀ t

/-- Two runs with the layout `L`, that stop at the same candidate, each
satisfying `Run` and `Φ`. -/
structure TwoAt (P : Rfc) (Φ : Pred P) (L : Lay P.I.hashLen) (g₁ g₂ : Reg → BitVec 64) (lr₁ lr₂ : Addr)
    (m₁ m₂ : Mem) (a b : State) : Prop where
  ok : L.Ok
  q : L.q = P.c.len
  gf : L.G = P.K.H ∧ L.f = P.K.f
  x : exitAt P L m₁ = exitAt P L m₂
  c₁ : Ctx L g₁ lr₁ m₁ a
  c₂ : Ctx L g₂ lr₂ m₂ b
  y₁ : SyOk L m₁ a
  y₂ : SyOk L m₂ b
  f₁ : Φ L g₁ lr₁ m₁ a
  f₂ : Φ L g₂ lr₂ m₂ b

/-- Two runs with the same layout that stop at the same candidate. -/
def Two (P : Rfc) (Φ : Pred P) (a b : State) : Prop :=
  ∃ L g₁ g₂ lr₁ lr₂ m₁ m₂, TwoAt P Φ L g₁ g₂ lr₁ lr₂ m₁ m₂ a b

variable {P : Rfc}

theorem Two.mono {Φ Ψ : Pred P} (h : ∀ L g lr m₀ t, Φ L g lr m₀ t → Ψ L g lr m₀ t) {a b : State}
    (ht : Two P Φ a b) : Two P Ψ a b :=
  let ⟨L, g₁, g₂, lr₁, lr₂, m₁, m₂, t⟩ := ht
  ⟨L, g₁, g₂, lr₁, lr₂, m₁, m₂, t.ok, t.q, t.gf, t.x, t.c₁, t.c₂, t.y₁, t.y₂, h _ _ _ _ _ t.f₁,
    h _ _ _ _ _ t.f₂⟩

/-- Code whose runs leak the same, and which keeps `Ctx` and establishes `Ψ`. -/
theorem two_wp {c : Prog isa} {Φ Ψ : Pred P}
    (hct : RelCT isa (Two P Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay P.I.hashLen) g lr m₀ (t : State), Run P L g lr m₀ t → Φ L g lr m₀ t →
      WP isa c t fun t' => Ctx L g lr m₀ t' ∧ Ψ L g lr m₀ t') :
    RelCT isa (Two P Φ) c (Two P Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨L, g₁, g₂, lr₁, lr₂, m₁, m₂, h⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw L g₁ lr₁ m₁ s₁ ⟨h.ok, h.q, h.gf, h.c₁, h.y₁⟩ h.f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw L g₂ lr₂ m₂ s₂ ⟨h.ok, h.q, h.gf, h.c₂, h.y₂⟩ h.f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, L, g₁, g₂, lr₁, lr₂, m₁, m₂, h.ok, h.q, h.gf, h.x, y₁.1, y₂.1, h.y₁.of_syms (Exec.syms e₁),
    h.y₂.of_syms (Exec.syms e₂), y₁.2, y₂.2⟩

/-- The taint check of a block, from the registers `rs` public. -/
abbrev TaintOk (rs : List Reg) (is : List Instr) : Prop :=
  ∃ hc, (VG.Taint.check taint (Taint.ofRegs rs) (.block is) hc).isSome = true

/-- The taint check of a block from that of the block with the immediates
of its `li`, `lis`, `ori` and `oris` zeroed. -/
theorem taintOk_erase {rs : List Reg} {is is₀ : List Instr} (h : TaintOk rs is₀)
    (he : is.map Instr.eraseImm = is₀.map Instr.eraseImm) : TaintOk rs is :=
  let ⟨hc, h⟩ := h
  ⟨hc, Taint.isSome_check_of_eraseImm (c' := .block is₀) (by simp only [Code.eraseImm, he]) h⟩

/-- A block that addresses memory only from `sp`. -/
theorem two_blk {is : List Instr} {Φ : Pred P} (h : TaintOk [] is) :
    RelCT isa (Two P Φ) (.block is) fun _ _ => True :=
  let ⟨_, h⟩ := h
  VG.RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ ⟨_, _, _, _, _, _, _, t⟩ => ⟨t.c₁.sp.trans t.c₂.sp.symm, fun r hr => by
      simp only [Taint.mem_ofRegs, List.not_mem_nil] at hr⟩) h

/-- A block that addresses memory from `sp` and the registers `rs`, which
hold the same values in both runs. -/
theorem two_regs {is : List Instr} {Φ : Pred P} (rs : List Reg) (f : Lay P.I.hashLen → Reg → BitVec 64)
    (hf : ∀ L g lr m₀ (t : State), Φ L g lr m₀ t → ∀ r ∈ rs, t.gpr r = f L r) (h : TaintOk rs is) :
    RelCT isa (Two P Φ) (.block is) fun _ _ => True :=
  let ⟨_, h⟩ := h
  VG.RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun _ _ ⟨_, _, _, _, _, _, _, t⟩ => ⟨t.c₁.sp.trans t.c₂.sp.symm, fun r hr => by
      rw [hf _ _ _ _ _ t.f₁ r (Taint.mem_ofRegs.mp hr), hf _ _ _ _ _ t.f₂ r (Taint.mem_ofRegs.mp hr)]⟩) h

/-- A block that loads pointers, the same in both runs, into `rs`, and then
addresses memory from them and `sp`. -/
theorem two_split {pre rest : List Instr} {Φ : Pred P} (rs : List Reg) (f : Lay P.I.hashLen → Reg → BitVec 64)
    (hpre : TaintOk [] pre)
    (hw : ∀ (L : Lay P.I.hashLen) g lr m₀ (t : State), L.Ok → Ctx L g lr m₀ t →
      WP isa (.block pre) t fun t' => t'.sp = t.sp ∧ ∀ r ∈ rs, t'.gpr r = f L r)
    (hrest : TaintOk rs rest) :
    RelCT isa (Two P Φ) (.block (pre ++ rest)) fun _ _ => True := by
  refine RelCT.block_append (RelCT.seq (R := fun (a b : State) => a.sp = b.sp ∧ ∀ r ∈ rs, a.gpr r = b.gpr r) ?_ ?_)
  · intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
    obtain ⟨ht, -⟩ := two_blk (Φ := Φ) hpre _ _ _ _ _ _ hp e₁ e₂
    obtain ⟨L, g₁, g₂, lr₁, lr₂, m₁, m₂, h⟩ := hp
    obtain ⟨_, u₁, x₁, y₁⟩ := hw L g₁ lr₁ m₁ s₁ h.ok h.c₁
    obtain ⟨_, u₂, x₂, y₂⟩ := hw L g₂ lr₂ m₂ s₂ h.ok h.c₂
    obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
    obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
    exact ⟨ht, by rw [y₁.1, y₂.1, h.c₁.sp, h.c₂.sp], fun r hr => by rw [y₁.2 r hr, y₂.2 r hr]⟩
  · let ⟨_, h⟩ := hrest
    exact VG.RelCT.taint (A := taint) (Taint.ofRegs rs) (fun _ _ hp => ⟨hp.1, fun r hr =>
      hp.2 r (Taint.mem_ofRegs.mp hr)⟩) h

/-! ## Pieces: related in two runs, and keeping `Ctx` in each -/

/-- Code that, from `Φ`, leaks the same in two runs and gives `Ψ`, keeping
`Ctx`, in each. -/
structure Piece (P : Rfc) (Φ : Pred P) (c : Prog isa) (Ψ : Pred P) : Prop where
  ct : RelCT isa (Two P Φ) c (Two P Ψ)
  wp : ∀ (L : Lay P.I.hashLen) g lr m₀ (t : State), Run P L g lr m₀ t → Φ L g lr m₀ t →
    WP isa c t fun t' => Ctx L g lr m₀ t' ∧ Ψ L g lr m₀ t'

namespace Piece

variable {Φ Ψ Χ : Pred P} {a b c : Prog isa}

theorem of (hct : RelCT isa (Two P Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay P.I.hashLen) g lr m₀ (t : State), Run P L g lr m₀ t → Φ L g lr m₀ t →
      WP isa c t fun t' => Ctx L g lr m₀ t' ∧ Ψ L g lr m₀ t') : Piece P Φ c Ψ :=
  ⟨two_wp hct hw, hw⟩

theorem seq (h₁ : Piece P Φ a Ψ) (h₂ : Piece P Ψ b Χ) : Piece P Φ (.seq a b) Χ :=
  ⟨h₁.ct.seq h₂.ct, fun L g lr m₀ t hr hφ =>
    WP.seq (WP.mono_syms (h₁.wp L g lr m₀ t hr hφ) fun _ ⟨c', ψ⟩ hs =>
      h₂.wp L g lr m₀ _ ⟨hr.ok, hr.q, hr.gf, c', hr.y.of_syms hs⟩ ψ)⟩

theorem pre {Φ' : Pred P} (h : Piece P Φ c Ψ) (hp : ∀ L g lr m₀ t, Φ' L g lr m₀ t → Φ L g lr m₀ t) :
    Piece P Φ' c Ψ :=
  ⟨h.ct.mono (fun _ _ => Two.mono hp) fun _ _ h => h, fun L g lr m₀ t hr hφ => h.wp L g lr m₀ t hr (hp _ _ _ _ _ hφ)⟩

/-- A piece from nothing, from any `Φ`. -/
theorem any (h : Piece P (Tt P) c Ψ) : Piece P Φ c Ψ := h.pre fun _ _ _ _ _ _ => trivial

/-- What the relational proofs use. -/
theorem rel (h : Piece P Φ c Ψ) {Φ' : Pred P} (hp : ∀ L g lr m₀ t, Φ' L g lr m₀ t → Φ L g lr m₀ t) :
    RelCT isa (Two P Φ') c fun _ _ => True :=
  h.ct.mono (fun _ _ => Two.mono hp) fun _ _ _ => trivial

/-- A block whose addresses depend only on `sp`. -/
theorem blk {is : List Instr} (ht : TaintOk [] is)
    (hw : ∀ (L : Lay P.I.hashLen) g lr m₀ (t : State), Run P L g lr m₀ t → Φ L g lr m₀ t →
      WP isa (.block is) t fun t' => Ctx L g lr m₀ t' ∧ Ψ L g lr m₀ t') : Piece P Φ (.block is) Ψ :=
  Piece.of (two_blk ht) hw

/-- A block that loads the pointers it addresses memory from. -/
theorem split {pre rest : List Instr} (rs : List Reg) (f : Lay P.I.hashLen → Reg → BitVec 64)
    (hpre : TaintOk [] pre)
    (hpw : ∀ (L : Lay P.I.hashLen) g lr m₀ (t : State), L.Ok → Ctx L g lr m₀ t →
      WP isa (.block pre) t fun t' => t'.sp = t.sp ∧ ∀ r ∈ rs, t'.gpr r = f L r)
    (hrest : TaintOk rs rest)
    (hw : ∀ (L : Lay P.I.hashLen) g lr m₀ (t : State), Run P L g lr m₀ t → Φ L g lr m₀ t →
      WP isa (.block (pre ++ rest)) t fun t' => Ctx L g lr m₀ t' ∧ Ψ L g lr m₀ t') :
    Piece P Φ (.block (pre ++ rest)) Ψ :=
  Piece.of (two_split rs f hpre hpw hrest) hw

end Piece

/-! ## The pointers the blocks load -/

variable {L : Lay P.I.hashLen} {g : Reg → BitVec 64} {lr : Addr} {m₀ : Mem}

/-- The frame's base in `r11` and `scratch` in `r12`. -/
def scrP (L : Lay P.I.hashLen) (r : Reg) : BitVec 64 := if r = .r11 then L.B + BitVec.ofNat 64 96 else L.scr

theorem scrBase_blk : TaintOk [] Cfg.scrBase := ⟨_, by taint_decide⟩

theorem scrBase_two (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block Cfg.scrBase) t fun t' => t'.sp = t.sp ∧ ∀ r ∈ [Reg.r11, .r12], t'.gpr r = scrP L r :=
  WP.mono (scrBase_ok hL hc) fun _ ⟨hc', _, _, h11, h12⟩ => ⟨hc'.sp.trans hc.sp.symm, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h11
    · exact h12⟩

/-- The table's address in `r12`. -/
theorem tabPtr_blk : TaintOk [] [.addSp .r12 0, .load .d .r12 .r12 fTab] := ⟨_, by taint_decide⟩

theorem tabPtr_two (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block [.addSp .r12 0, .load .d .r12 .r12 fTab]) t fun t' =>
      t'.sp = t.sp ∧ ∀ r ∈ [Reg.r12], t'.gpr r = (fun (L : Lay P.I.hashLen) (_ : Reg) => L.tab) L r := by
  have hnB := hL.nB
  refine stepAddSp (by decide) fun t₁ k₁ m₁ v₁ => ?_
  have hb : t₁.gpr .r12 = L.B + BitVec.ofNat 64 96 := by rw [v₁, hc.sp, BitVec.add_zero]
  have hc₁ := hc.kp hL k₁ m₁
  refine stepLd (a := L.B + BitVec.ofNat 64 344) (by decide) (by decide) (by rw [hb, fr_add]; rfl)
    (hc₁.inFr (by omega) (by omega)) fun t₂ k₂ m₂ v₂ => wp_nil ⟨by rw [k₂.sp, k₁.sp], fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [v₂, hc₁.pTab]⟩

theorem tword_blk (j : Nat) (hj : j < 3) : TaintOk [.r12] [.load .d .r12 .r12 (8 * j)] := by
  obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩

/-! ## The indirect calls -/

/-- What an indirect call of `n` needs of the table in each run: its word
`j` (on entry) is `n`'s address, which is the layout's, and of `ts` an
indirect call reaches `n`'s `c`. -/
def TabFn (P : Rfc) (j : Nat) (n : String) (c : Prog isa) (ts : List (String × Prog isa)) : Prop :=
  ∀ (L : Lay P.I.hashLen) m₀ (t : State), L.G = P.K.H ∧ L.f = P.K.f → SyOk L m₀ t →
    m₀.readW (L.tab + BitVec.ofNat 64 (8 * j)) 64 = t.syms n ∧
      ts.find? (fun q => t.syms q.1 == t.syms n) = some (n, c) ∧ t.syms n = L.fa n

theorem tfn_init : TabFn P 0 P.K.H.initN P.K.H.initC P.c.f.init := fun L _ _ hG hy => by
  have hok := hy.tabOk; have htm := hy.tabMem; have hf := hy.fsy
  rw [hG.1, hG.2] at hok; rw [hG.1] at htm hf
  rw [P.hcf]
  exact ⟨by rw [Nat.mul_zero, BitVec.add_zero]; exact htm.1, hok.i, hf _ (by simp)⟩

theorem tfn_upd : TabFn P 1 P.K.H.updN P.K.H.updC P.c.f.upd := fun L _ _ hG hy => by
  have hok := hy.tabOk; have htm := hy.tabMem; have hf := hy.fsy
  rw [hG.1, hG.2] at hok; rw [hG.1] at htm hf
  rw [P.hcf]
  exact ⟨by rw [Nat.mul_one]; exact htm.2.1, hok.u, hf _ (by simp)⟩

theorem tfn_fin : TabFn P 2 P.K.H.finN P.K.H.finC P.c.f.fin := fun L _ _ hG hy => by
  have hok := hy.tabOk; have htm := hy.tabMem; have hf := hy.fsy
  rw [hG.1, hG.2] at hok; rw [hG.1] at htm hf
  rw [P.hcf]
  exact ⟨by rw [show 8 * 2 = 16 from rfl]; exact htm.2.2, hok.f, hf _ (by simp)⟩

/-- What only `r12` changing keeps. -/
def K12 (Φ : Pred P) : Prop :=
  ∀ L g lr m₀ (t t' : State), Φ L g lr m₀ t → Kp [.r12] t t' → Φ L g lr m₀ t'

/-- The indirect call of the table's function `j`: in both runs of the same
function, `n`'s (the table's word `j` holds the layout's address of `n`). -/
theorem tcall_piece {Φ Ψ : Pred P} {j : Nat} (hj : j < 3) {n : String} {c : Prog isa}
    {ts : List (String × Prog isa)} (hn : TabFn P j n c ts) (hΦ : K12 Φ) (hcall : Piece P Φ (.call n c) Ψ) :
    Piece P Φ (Cfg.tcall j ts) Ψ := by
  have hj' : 8 * j + 8 ≤ 40 := by omega
  have hw : ∀ (L : Lay P.I.hashLen) g lr m₀ (t : State), Run P L g lr m₀ t → Φ L g lr m₀ t →
      WP isa (.block [.addSp .r12 0, .load .d .r12 .r12 fTab, .load .d .r12 .r12 (8 * j)]) t fun t' =>
        Ctx L g lr m₀ t' ∧ (Φ L g lr m₀ t' ∧ t'.gpr .r12 = L.fa n) := fun L g lr m₀ t hr hφ =>
    WP.mono (tword_ok hr.ok hr.c hj') fun t' ⟨hc', _, k, h12⟩ => by
      obtain ⟨hw, -, hfa⟩ := hn L m₀ t hr.gf hr.y
      exact ⟨hc', hΦ _ _ _ _ _ _ hφ k, by rw [h12, hw, hfa]⟩
  refine ⟨?_, fun L g lr m₀ t hr hφ => ?_⟩
  · unfold Cfg.tcall
    refine RelCT.seq (two_wp (Ψ := fun L g lr m₀ u => Φ L g lr m₀ u ∧ u.gpr .r12 = L.fa n) ?_ hw) ?_
    · show RelCT isa _ (.block ([.addSp .r12 0, .load .d .r12 .r12 fTab] ++ [.load .d .r12 .r12 (8 * j)])) _
      exact two_split [.r12] (fun L _ => L.tab) tabPtr_blk (fun _ _ _ _ _ hL hc => tabPtr_two hL hc)
        (tword_blk j hj)
    · cases ts with
      | nil => exact RelCT.of_false fun _ _ ⟨L, _, _, _, _, m₁, _, h⟩ => by simpa using (hn L m₁ _ h.gf h.y₁).2.1
      | cons q ts =>
        refine RelCT.icalls_of_call (hcall.ct.mono (fun _ _ h => Two.mono (fun _ _ _ _ _ h => h.1) h)
          fun _ _ h => h) ?_
        rintro s₁ s₂ ⟨L, g₁, g₂, lr₁, lr₂, m₁, m₂, h⟩
        obtain ⟨-, f₁, e₁⟩ := hn L m₁ s₁ h.gf h.y₁
        obtain ⟨-, f₂, e₂⟩ := hn L m₂ s₂ h.gf h.y₂
        refine ⟨L.fa n, by show some (s₁.gpr .r12) = _; rw [h.f₁.2], by show some (s₂.gpr .r12) = _; rw [h.f₂.2],
          ?_, ?_, rfl⟩
        · show (q :: ts).find? (fun p => s₁.syms p.1 == L.fa n) = _; rw [← e₁]; exact f₁
        · show (q :: ts).find? (fun p => s₂.syms p.1 == L.fa n) = _; rw [← e₂]; exact f₂
  · obtain ⟨hw', hf, -⟩ := hn L m₀ t hr.gf hr.y
    exact tcall_ok hr.ok hr.c hj' hw' hf fun t' hc' _ k hs =>
      hcall.wp L g lr m₀ t' ⟨hr.ok, hr.q, hr.gf, hc', hr.y.of_syms hs⟩ (hΦ _ _ _ _ _ _ hφ k)

/-! ## The streaming calls -/

theorem ce_gpr (u : State) (rd wr : List Region) {r : Reg} (hr : r ∉ linkRegs) :
    (u.callEntry.withRegions rd wr).gpr r = u.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr]

/-- The argument registers, on a call's entry. -/
theorem ce_args (u : State) (rd wr : List Region) :
    (u.callEntry.withRegions rd wr).gpr .r3 = u.gpr .r3 ∧ (u.callEntry.withRegions rd wr).gpr .r4 = u.gpr .r4 ∧
      (u.callEntry.withRegions rd wr).gpr .r5 = u.gpr .r5 ∧ (u.callEntry.withRegions rd wr).gpr .r6 = u.gpr .r6 ∧
      (u.callEntry.withRegions rd wr).gpr .r7 = u.gpr .r7 :=
  ⟨ce_gpr u rd wr (by decide), ce_gpr u rd wr (by decide), ce_gpr u rd wr (by decide), ce_gpr u rd wr (by decide),
    ce_gpr u rd wr (by decide)⟩

theorem ce_sp (u : State) (rd wr : List Region) : (u.callEntry.withRegions rd wr).sp = u.sp := by
  rw [State.withRegions_sp, State.callEntry_sp]

/-- `init`'s argument: the state at `scratch + o`. -/
def IA (P : Rfc) (o : Nat) : Pred P := fun L _ _ _ u => u.gpr .r3 = L.scr + BitVec.ofNat 64 o

theorem initPre (hL : L.Ok) {u : State} (hc : Ctx L g lr m₀ u) {o : Nat} (ho : o + 192 ≤ 384)
    (h3 : u.gpr .r3 = L.scr + BitVec.ofNat 64 o) :
    (initK P.K.H.S P.K.hH.SH.Repr).pre (u.callEntry.withRegions [] [⟨L.scr + BitVec.ofNat 64 o, P.K.H.S⟩]) ∧
      Covers ([] ++ [⟨L.scr + BitVec.ofNat 64 o, P.K.H.S⟩]) (u.rd ++ u.wr) ∧
      Covers [⟨L.scr + BitVec.ofNat 64 o, P.K.H.S⟩] u.wr := by
  have hnc := hL.nc
  have hS := P.K.hS
  have hsp : u.sp = L.B + BitVec.ofNat 64 96 := hc.sp
  refine ⟨?_, ?_, ?_⟩
  · simp only [initK, State.withRegions_rd, State.withRegions_wr, ce_sp, (ce_args _ _ _).1, h3]
    exact ⟨trivial, trivial, by rw [hsp, hL.sp_toNat]; omega,
      by rw [hsp, L.below48]; exact hL.stk_scr (by omega) (by omega)⟩
  · rw [List.nil_append]
    exact hc.covers fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.SCR, by simp, within_off _ (by omega)⟩
  · exact hc.coversW fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.SCR, by simp, within_off _ (by omega)⟩

theorem init_piece {o : Nat} (ho : o + 192 ≤ 384) : Piece P (IA P o) (.call P.K.H.initN P.K.H.initC) (Tt P) :=
  Piece.of (RelCT.callEx P.K.hH.init P.K.ct.init fun s₁ s₂ ⟨_, _, _, _, _, _, _, h⟩ =>
    have A := initPre h.ok h.c₁ ho h.f₁
    have B := initPre h.ok h.c₂ ho h.f₂
    ⟨_, _, _, _, A.1, B.1, by
      simp only [initK, ce_sp, (ce_args _ _ _).1]
      exact ⟨by rw [h.f₁, h.f₂], by rw [h.c₁.sp, h.c₂.sp]⟩, A.2.1, A.2.2, B.2.1, B.2.2⟩)
    fun _ _ _ _ _ hr h3 => WP.mono (initRaw_ok P.K hr.ok hr.c ho h3) fun _ h => ⟨h.1, trivial⟩

/-- `update`'s arguments: the state at `scratch + o` holding `cnt` bytes,
the `len` bytes at `da`, and the working space. -/
def UA (P : Rfc) (o cnt : Nat) (da : Lay P.I.hashLen → Addr) (len : Nat) : Pred P := fun L _ _ _ u =>
  u.gpr .r3 = L.scr + BitVec.ofNat 64 o ∧ u.gpr .r4 = BitVec.ofNat 64 cnt ∧ u.gpr .r5 = da L ∧
    u.gpr .r6 = BitVec.ofNat 64 len ∧ u.gpr .r7 = L.scr + BitVec.ofNat 64 384

theorem updPre (hL : L.Ok) {u : State} (hc : Ctx L g lr m₀ u) {o : Nat} (ho : o + 192 ≤ 384) {da : Addr}
    {len : Nat} (hd : UpdData P.K L o da len) (hlen : len < 2 ^ 15) (h3 : u.gpr .r3 = L.scr + BitVec.ofNat 64 o)
    (h5 : u.gpr .r5 = da) (h6 : u.gpr .r6 = BitVec.ofNat 64 len) (h7 : u.gpr .r7 = L.scr + BitVec.ofNat 64 384) :
    (updK P.K.H.S P.K.H.W P.K.hH.SH.Repr).pre (u.callEntry.withRegions [⟨da, len⟩]
        [⟨L.scr + BitVec.ofNat 64 o, P.K.H.S⟩, ⟨L.scr + BitVec.ofNat 64 384, P.K.H.W⟩]) ∧
      Covers ([⟨da, len⟩] ++ [⟨L.scr + BitVec.ofNat 64 o, P.K.H.S⟩, ⟨L.scr + BitVec.ofNat 64 384, P.K.H.W⟩])
        (u.rd ++ u.wr) ∧
      Covers [⟨L.scr + BitVec.ofNat 64 o, P.K.H.S⟩, ⟨L.scr + BitVec.ofNat 64 384, P.K.H.W⟩] u.wr := by
  have hnc := hL.nc
  have hnB := hL.nB
  have hS := P.K.hS
  have hW := P.K.hW
  simp only [sWork, sPad] at hW
  have hsp : u.sp = L.B + BitVec.ofNat 64 96 := hc.sp
  have c6 : (u.gpr .r6).toNat = len := by rw [h6, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨?_, ?_, ?_⟩
  · simp only [updK, State.withRegions_rd, State.withRegions_wr, ce_sp, (ce_args _ _ _).1, (ce_args _ _ _).2.2.1, (ce_args _ _ _).2.2.2.1,
      (ce_args _ _ _).2.2.2.2, h3, h5, c6, h7]
    exact ⟨trivial, trivial, Offset.disjoint _ (by omega) (by omega) (by omega), hd.st, hd.wk,
      by rw [hsp, hL.sp_toNat]; omega, by rw [hsp, L.below48]; exact hL.stk_scr (by omega) (by omega),
      by rw [hsp, L.below48]; exact hd.low, by rw [hsp, L.below48]; exact hL.stk_scr (by omega) (by omega)⟩
  · exact hc.covers fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hd.cov
      all_goals exact ⟨L.SCR, by simp, within_off _ (by omega)⟩
  · exact hc.coversW fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨L.SCR, by simp, within_off _ (by omega)⟩

theorem upd_piece {o cnt : Nat} (ho : o + 192 ≤ 384) {da : Lay P.I.hashLen → Addr} {len : Nat}
    (hd : ∀ L : Lay P.I.hashLen, L.Ok → UpdData P.K L o (da L) len) (hlen : len < 2 ^ 15) :
    Piece P (UA P o cnt da len) (.call P.K.H.updN P.K.H.updC) (Tt P) :=
  Piece.of (RelCT.callEx P.K.hH.upd P.K.ct.upd fun s₁ s₂ ⟨L, _, _, _, _, _, _, h⟩ =>
    have A := updPre h.ok h.c₁ ho (hd L h.ok) hlen h.f₁.1 h.f₁.2.2.1 h.f₁.2.2.2.1 h.f₁.2.2.2.2
    have B := updPre h.ok h.c₂ ho (hd L h.ok) hlen h.f₂.1 h.f₂.2.2.1 h.f₂.2.2.2.1 h.f₂.2.2.2.2
    ⟨_, _, _, _, A.1, B.1, by
      simp only [updK, ce_sp, (ce_args _ _ _).1, (ce_args _ _ _).2.1, (ce_args _ _ _).2.2.1,
        (ce_args _ _ _).2.2.2.1, (ce_args _ _ _).2.2.2.2]
      exact ⟨by rw [h.f₁.1, h.f₂.1], by rw [h.f₁.2.1, h.f₂.2.1], by rw [h.f₁.2.2.1, h.f₂.2.2.1],
        by rw [h.f₁.2.2.2.1, h.f₂.2.2.2.1], by rw [h.f₁.2.2.2.2, h.f₂.2.2.2.2], by rw [h.c₁.sp, h.c₂.sp]⟩,
      A.2.1, A.2.2, B.2.1, B.2.2⟩)
    fun L _ _ _ _ hr ⟨h3, _, h5, h6, h7⟩ =>
      WP.mono (updRaw_ok P.K hr.ok hr.c ho (hd L hr.ok) hlen h3 h5 h6 h7) fun _ h => ⟨h, trivial⟩

/-- `finalize`'s arguments: the state at `scratch + o` holding `cnt` bytes,
the output at `scratch + sTmp`, and the working space. -/
def FA (P : Rfc) (o cnt : Nat) : Pred P := fun L _ _ _ u =>
  u.gpr .r3 = L.scr + BitVec.ofNat 64 o ∧ u.gpr .r4 = BitVec.ofNat 64 cnt ∧
    u.gpr .r5 = L.scr + BitVec.ofNat 64 1920 ∧ u.gpr .r6 = L.scr + BitVec.ofNat 64 384

theorem finPre (hL : L.Ok) {u : State} (hc : Ctx L g lr m₀ u) {o : Nat} (ho : o + 192 ≤ 384)
    (h3 : u.gpr .r3 = L.scr + BitVec.ofNat 64 o) (h5 : u.gpr .r5 = L.scr + BitVec.ofNat 64 1920)
    (h6 : u.gpr .r6 = L.scr + BitVec.ofNat 64 384) :
    (finK P.K.H.S P.K.H.W P.K.H.FD P.K.hH.SH.Repr P.K.hH.fh).pre (u.callEntry.withRegions []
        [⟨L.scr + BitVec.ofNat 64 o, P.K.H.S⟩, ⟨L.scr + BitVec.ofNat 64 1920, P.K.H.FD⟩,
          ⟨L.scr + BitVec.ofNat 64 384, P.K.H.W⟩]) ∧
      Covers ([] ++ [⟨L.scr + BitVec.ofNat 64 o, P.K.H.S⟩, ⟨L.scr + BitVec.ofNat 64 1920, P.K.H.FD⟩,
          ⟨L.scr + BitVec.ofNat 64 384, P.K.H.W⟩]) (u.rd ++ u.wr) ∧
      Covers [⟨L.scr + BitVec.ofNat 64 o, P.K.H.S⟩, ⟨L.scr + BitVec.ofNat 64 1920, P.K.H.FD⟩,
          ⟨L.scr + BitVec.ofNat 64 384, P.K.H.W⟩] u.wr := by
  have hnc := hL.nc
  have hnB := hL.nB
  have hS := P.K.hS
  have hW := P.K.hW
  have hFD := P.K.hH.hFD64
  simp only [sWork, sPad] at hW
  have hsp : u.sp = L.B + BitVec.ofNat 64 96 := hc.sp
  refine ⟨?_, ?_, ?_⟩
  · simp only [finK, State.withRegions_rd, State.withRegions_wr, ce_sp, (ce_args _ _ _).1, (ce_args _ _ _).2.2.1, (ce_args _ _ _).2.2.2.1, h3, h5, h6]
    exact ⟨trivial, trivial, Offset.disjoint _ (by omega) (by omega) (by omega),
      Offset.disjoint _ (by omega) (by omega) (by omega), Offset.disjoint _ (by omega) (by omega) (by omega),
      by rw [hsp, hL.sp_toNat]; omega, by rw [hsp, L.below48]; exact hL.stk_scr (by omega) (by omega),
      by rw [hsp, L.below48]; exact hL.stk_scr (by omega) (by omega),
      by rw [hsp, L.below48]; exact hL.stk_scr (by omega) (by omega)⟩
  · rw [List.nil_append]
    exact hc.covers fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact ⟨L.SCR, by simp, within_off _ (by omega)⟩
  · exact hc.coversW fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact ⟨L.SCR, by simp, within_off _ (by omega)⟩

theorem fin_piece {o cnt : Nat} (ho : o + 192 ≤ 384) :
    Piece P (FA P o cnt) (.call P.K.H.finN P.K.H.finC) (Tt P) :=
  Piece.of (RelCT.callEx P.K.hH.fin P.K.ct.fin fun s₁ s₂ ⟨_, _, _, _, _, _, _, h⟩ =>
    have A := finPre h.ok h.c₁ ho h.f₁.1 h.f₁.2.2.1 h.f₁.2.2.2
    have B := finPre h.ok h.c₂ ho h.f₂.1 h.f₂.2.2.1 h.f₂.2.2.2
    ⟨_, _, _, _, A.1, B.1, by
      simp only [finK, ce_sp, (ce_args _ _ _).1, (ce_args _ _ _).2.1, (ce_args _ _ _).2.2.1,
        (ce_args _ _ _).2.2.2.1]
      exact ⟨by rw [h.f₁.1, h.f₂.1], by rw [h.f₁.2.1, h.f₂.2.1], by rw [h.f₁.2.2.1, h.f₂.2.2.1],
        by rw [h.f₁.2.2.2, h.f₂.2.2.2], by rw [h.c₁.sp, h.c₂.sp]⟩, A.2.1, A.2.2, B.2.1, B.2.2⟩)
    fun _ _ _ _ _ hr ⟨h3, _, h5, h6⟩ => WP.mono (finRaw_ok P.K hr.ok hr.c ho h3 h5 h6) fun _ h => ⟨h, trivial⟩

theorem k12_ia {o : Nat} : K12 (IA P o) := fun _ _ _ _ _ _ h k => (k.gpr _ (by decide)).trans h

theorem k12_ua {o cnt : Nat} {da : Lay P.I.hashLen → Addr} {len : Nat} : K12 (UA P o cnt da len) :=
  fun _ _ _ _ _ _ ⟨a, b, c, d, e⟩ k => ⟨(k.gpr _ (by decide)).trans a, (k.gpr _ (by decide)).trans b,
    (k.gpr _ (by decide)).trans c, (k.gpr _ (by decide)).trans d, (k.gpr _ (by decide)).trans e⟩

theorem k12_fa {o cnt : Nat} : K12 (FA P o cnt) :=
  fun _ _ _ _ _ _ ⟨a, b, c, d⟩ k => ⟨(k.gpr _ (by decide)).trans a, (k.gpr _ (by decide)).trans b,
    (k.gpr _ (by decide)).trans c, (k.gpr _ (by decide)).trans d⟩

/-- `init` of the state at `scratch + o`, through the table. -/
theorem initCall_piece {Φ : Pred P} {o : Nat} (ho : o + 192 ≤ 384) (ht : TaintOk [.r11, .r12] [.addi .r3 .r12 o]) :
    Piece P Φ (P.c.initCall o) (Tt P) :=
  (Piece.split (Ψ := IA P o) [.r11, .r12] scrP scrBase_blk (fun _ _ _ _ _ hL hc => scrBase_two hL hc) ht
    fun _ _ _ _ _ hr _ => WP.mono (initArgs_ok hr.ok hr.c (o := o) (by omega)) fun _ ⟨c, _, _, h3⟩ => ⟨c, h3⟩).seq
    (tcall_piece (by decide) tfn_init k12_ia (init_piece ho))

/-- The data block of `update`: the address of the data in `r5`. -/
def DataA (P : Rfc) (dataA : List Instr) (da : Lay P.I.hashLen → Addr) : Prop :=
  ∀ (L : Lay P.I.hashLen) g lr m₀ (u : State), Ctx L g lr m₀ u → u.gpr .r12 = L.scr →
    WP isa (.block dataA) u fun u' => Kp [.r5] u u' ∧ u'.mem = u.mem ∧ u'.gpr .r5 = da L

/-- Data at `scratch + o`. -/
theorem scrDA (o : Nat) (ho : o < 2 ^ 15) : DataA P [.addi .r5 .r12 o] fun L => L.scr + BitVec.ofNat 64 o :=
  fun _ _ _ _ u _ h => dataS_ok u h ho

/-- Data at `V`. -/
theorem vDA : DataA P [.addSp .r5 fV] fun L => L.B + BitVec.ofNat 64 192 :=
  fun _ _ _ _ u hc _ => dataV_ok hc u rfl

/-- What `updArgs` does after `scrBase`. -/
abbrev updRest (o cnt : Nat) (dataA : List Instr) (len : Nat) : List Instr :=
  ([.addi .r3 .r12 o, .li .r4 cnt] : List Instr) ++ (dataA ++ ([.li .r6 len, .addi .r7 .r12 sWork] : List Instr))

theorem updArgs_eq (o cnt : Nat) (dataA : List Instr) (len : Nat) :
    Cfg.updArgs o cnt dataA len = Cfg.scrBase ++ updRest o cnt dataA len := by
  simp only [Cfg.updArgs, List.append_assoc]

theorem updRest_taint {o cnt : Nat} {dataA : List Instr} {len : Nat}
    (ht : TaintOk [.r11, .r12] (updRest o 0 dataA 0)) : TaintOk [.r11, .r12] (updRest o cnt dataA len) :=
  taintOk_erase ht (by simp [Instr.eraseImm])

/-- `update` of the state at `scratch + o`, holding `cnt` bytes, with `len`
bytes at `da`, through the table. -/
theorem updCall_piece {Φ : Pred P} {o cnt : Nat} (ho : o + 192 ≤ 384) {dataA : List Instr}
    {da : Lay P.I.hashLen → Addr} {len : Nat} (hdA : DataA P dataA da)
    (hd : ∀ L : Lay P.I.hashLen, L.Ok → UpdData P.K L o (da L) len) (hcnt : cnt < 2 ^ 15) (hlen : len < 2 ^ 15)
    (ht : TaintOk [.r11, .r12] (updRest o 0 dataA 0)) :
    Piece P Φ (P.c.updCall o cnt dataA len) (Tt P) := by
  unfold Cfg.updCall
  rw [updArgs_eq]
  exact (Piece.split (Ψ := UA P o cnt da len) [.r11, .r12] scrP scrBase_blk
    (fun _ _ _ _ _ hL hc => scrBase_two hL hc) (updRest_taint ht) fun L g lr m₀ _ hr _ => by
      rw [← updArgs_eq]
      exact WP.mono (updArgs_ok hr.ok hr.c (by omega) hcnt hlen (hdA L g lr m₀))
        fun _ ⟨c, _, _, h3, h4, h5, h6, h7⟩ => ⟨c, h3, h4, h5, h6, h7⟩).seq
    (tcall_piece (by decide) tfn_upd k12_ua (upd_piece ho hd hlen))

/-- What `finArgs` does after `scrBase`. -/
abbrev finRest (o cnt : Nat) : List Instr := [.addi .r3 .r12 o, .li .r4 cnt, .addi .r5 .r12 sTmp, .addi .r6 .r12 sWork]

theorem finRest_taint (o cnt : Nat) (ho : o = 0 ∨ o = 192) : TaintOk [.r11, .r12] (finRest o cnt) := by
  refine taintOk_erase (is₀ := finRest o 0) ?_ (by simp [Instr.eraseImm])
  rcases ho with rfl | rfl
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩

/-- `finalize` of the state at `scratch + o`, holding `cnt` bytes, through the table. -/
theorem finCall_piece {Φ : Pred P} {o cnt : Nat} (ho : o = 0 ∨ o = 192) (hcnt : cnt < 2 ^ 15) :
    Piece P Φ (P.c.finCall o cnt) (Tt P) :=
  have ho' : o + 192 ≤ 384 := by omega
  (Piece.split (Ψ := FA P o cnt) [.r11, .r12] scrP scrBase_blk (fun _ _ _ _ _ hL hc => scrBase_two hL hc)
    (finRest_taint o cnt ho) fun _ _ _ _ _ hr _ =>
      WP.mono (finArgs_ok hr.ok hr.c (o := o) (by omega) hcnt) fun _ ⟨c, _, _, h3, h4, h5, h6⟩ =>
        ⟨c, h3, h4, h5, h6⟩).seq
    (tcall_piece (by decide) tfn_fin k12_fa (fin_piece ho'))

/-! ## HMAC -/

/-- The blocks that depend on the hash function's sizes: the padded key, the
MAC's copies to `K` and `V`, and `V`'s to the candidate. -/
structure HBlks (c : Cfg) : Prop where
  pad : TaintOk [.r11, .r12] (Impl.Mont.PPC64LE.movImm .r9 0 ++ (List.range (c.B / 4)).flatMap c.padW)
  outK : TaintOk [.r11, .r12] (Cfg.copyW (c.D / 4) .r12 sTmp .r11 fK)
  outV : TaintOk [.r11, .r12] (Cfg.copyW (c.D / 4) .r12 sTmp .r11 fV)
  keep : ∀ j < 8, j * c.D + c.D ≤ 128 → TaintOk [] (c.keepV j)

theorem kokP (hG : L.G = P.K.H ∧ L.f = P.K.f) : KOk P.K P.c L := kok hG

/-- `K₀ ⊕ c` at `scratch + sPad`. -/
theorem padBlk_piece (HB : HBlks P.c) {Φ : Pred P} (x : Byte) :
    Piece P Φ (.block (P.c.padBlk (x ++ x ++ x ++ x))) (Tt P) := by
  have e : P.c.padBlk (x ++ x ++ x ++ x) = Cfg.scrBase ++ (Impl.Mont.PPC64LE.movImm .r9 (x ++ x ++ x ++ x) ++
      (List.range (P.c.B / 4)).flatMap P.c.padW) := by
    simp only [Cfg.padBlk, List.append_assoc]
  rw [e]
  refine Piece.split [.r11, .r12] scrP scrBase_blk (fun _ _ _ _ _ hL hc => scrBase_two hL hc)
    (taintOk_erase HB.pad (by simp [Impl.Mont.PPC64LE.movImm, Instr.eraseImm])) fun _ _ _ _ _ hr _ => ?_
  rw [← e]
  exact WP.mono (padBlk_ok P.K (kokP hr.gf) hr.ok hr.c x) fun _ h => ⟨h.1, trivial⟩

/-- The registers that hold the data's pointer in `update`'s arguments. -/
theorem updPad_taint (o : Nat) (ho : o = 0 ∨ o = 192) : TaintOk [.r11, .r12] (updRest o 0 [.addi .r5 .r12 sPad] 0) := by
  rcases ho with rfl | rfl
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩

theorem initI_taint : TaintOk [.r11, .r12] [.addi .r3 .r12 sInner] := ⟨_, by taint_decide⟩
theorem initO_taint : TaintOk [.r11, .r12] [.addi .r3 .r12 sOuter] := ⟨_, by taint_decide⟩

theorem sizes (P : Rfc) : P.K.H.S ≤ 192 ∧ 384 + P.K.H.W ≤ 1792 ∧ 0 < P.K.H.D ∧ P.K.H.D ≤ 64 ∧ P.K.H.D % 4 = 0 ∧
    P.K.H.D ≤ P.K.H.B ∧ (P.K.H.B = 64 ∨ P.K.H.B = 128) ∧ P.K.H.D ≤ P.K.H.FD ∧ P.K.H.FD ≤ 64 :=
  Kit.sizes P.K

/-- `hinit`: each state set by `init` and updated with its padded key. -/
theorem hinit_piece (HB : HBlks P.c) {Φ : Pred P} : Piece P Φ P.c.hinit (Tt P) := by
  obtain ⟨-, -, -, -, -, -, hB, -⟩ := sizes P
  have hcB := P.hcB
  have hBl : P.c.B < 2 ^ 15 := by omega
  unfold Cfg.hinit
  rw [ipad32_eq, opad32_eq]
  exact (initCall_piece (by decide) initI_taint).seq ((initCall_piece (by decide) initO_taint).seq
    ((padBlk_piece HB _).seq ((updCall_piece (by decide) (scrDA sPad (by decide))
      (fun L hL => by rw [hcB]; exact padData P.K hL (by decide)) (by decide) hBl (updPad_taint 0 (.inl rfl))).seq
    ((padBlk_piece HB _).seq (updCall_piece (by decide) (scrDA sPad (by decide))
      (fun L hL => by rw [hcB]; exact padData P.K hL (by decide)) (by decide) hBl (updPad_taint 192 (.inr rfl)))))))

/-- `hupd`: the inner state updated with the data. -/
theorem hupd_piece {Φ : Pred P} {dataA : List Instr} {da : Lay P.I.hashLen → Addr} {len : Nat}
    (hdA : DataA P dataA da) (hd : ∀ L : Lay P.I.hashLen, L.Ok → DataOk L (da L) len)
    (ht : TaintOk [.r11, .r12] (updRest sInner 0 dataA 0)) (hlen : len ≤ 256) :
    Piece P Φ (P.c.hupd dataA len) (Tt P) := by
  obtain ⟨-, -, -, -, -, -, hB, -⟩ := sizes P
  have hcB := P.hcB
  unfold Cfg.hupd
  exact updCall_piece (by decide) hdA (fun L hL => (hd L hL).upd P.K hL) (by omega) (by omega) ht

/-- The MAC's copy to the frame at `dst`. -/
theorem copyOut_ok (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) {dst : Nat} (hdst : 32 ≤ dst ∧ dst + 64 ≤ 216) :
    WP isa (.block (Cfg.scrBase ++ Cfg.copyW (P.c.D / 4) .r12 sTmp .r11 dst)) t fun u => Ctx L g lr m₀ u := by
  have hnc := hL.nc
  have hnB := hL.nB
  have hD := P.K.hH.hD64
  have hcD := P.hcD
  rw [WP.block_append_iff]
  refine WP.mono (scrBase_ok hL hc) fun w₄ ⟨hc₄, _, _, b₄, s₄⟩ => ?_
  have hsep : Region.Disjoint ⟨L.scr + BitVec.ofNat 64 1920, 4 * (P.c.D / 4)⟩
      ⟨L.B + BitVec.ofNat 64 96 + BitVec.ofNat 64 dst, 4 * (P.c.D / 4)⟩ := by
    rw [fr_add]; exact (hL.stk_scr (by omega) (by omega)).symm
  refine WP.mono (copyW_ok (src := .r12) (dst := .r11) (S := L.scr) (D := L.B + BitVec.ofNat 64 96)
    (so := 1920) (d := dst) (K := P.c.D / 4) (by decide) (by decide) (by decide) (by decide) hsep (by omega)
    (by omega) (by omega) (P.c.D / 4) (Nat.le_refl _) w₄ s₄ b₄ (fun j hj => hc₄.inScr (by omega))
    (fun j hj => by rw [fr_add]; exact hc₄.inFrW (by omega) (by have := hc₄.ne; omega)))
    fun w₅ ⟨k₅, hf₅, _⟩ => ?_
  rw [fr_add] at hf₅
  exact hc₄.keep hL k₅.rd k₅.wr k₅.sp (fun r hr => k₅.gpr r fun h => by
      simp only [List.mem_singleton] at h; subst h; simp [preserved] at hr) hf₅
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega))

theorem copyOut_piece {Φ : Pred P} {dst : Nat} (hdst : 32 ≤ dst ∧ dst + 64 ≤ 216)
    (ht : TaintOk [.r11, .r12] (Cfg.copyW (P.c.D / 4) .r12 sTmp .r11 dst)) :
    Piece P Φ (.block (Cfg.scrBase ++ Cfg.copyW (P.c.D / 4) .r12 sTmp .r11 dst)) (Tt P) :=
  Piece.split [.r11, .r12] scrP scrBase_blk (fun _ _ _ _ _ hL hc => scrBase_two hL hc) ht
    fun _ _ _ _ _ hr _ => WP.mono (copyOut_ok hr.ok hr.c hdst) fun _ h => ⟨h, trivial⟩

theorem updTmp_taint : TaintOk [.r11, .r12] (updRest sOuter 0 [.addi .r5 .r12 sTmp] 0) := ⟨_, by taint_decide⟩

/-- `hfin`: the MAC, for `len` bytes of data, to the frame at `dst`. -/
theorem hfin_piece {Φ : Pred P} {len dst : Nat} (hlen : len ≤ 256) (hdst : 32 ≤ dst ∧ dst + 64 ≤ 216)
    (ht : TaintOk [.r11, .r12] (Cfg.copyW (P.c.D / 4) .r12 sTmp .r11 dst)) :
    Piece P Φ (P.c.hfin len dst) (Tt P) := by
  obtain ⟨-, -, -, hD, -, -, hB, hDF, hFD⟩ := sizes P
  have hcB := P.hcB
  have hcD := P.hcD
  unfold Cfg.hfin
  refine (finCall_piece (.inl rfl) (by omega)).seq ((updCall_piece (by decide) (scrDA sTmp (by decide))
    (fun L hL => ?_) (by omega) (by omega) updTmp_taint).seq ((finCall_piece (.inr rfl) (by omega)).seq
    (copyOut_piece hdst ht)))
  have hnc := hL.nc
  have hnB := hL.nB
  rw [hcD]
  exact ⟨⟨L.SCR, by simp, within_off _ (by simp only [sTmp]; omega)⟩,
    Offset.disjoint _ (by have := P.K.hS; simp only [sTmp, sOuter]; omega) (by simp only [sTmp]; omega)
      (by simp only [sOuter]; have := P.K.hS; omega),
    Offset.disjoint _ (by have := P.K.hW; simp only [sTmp, sWork, sPad] at *; omega) (by simp only [sTmp]; omega)
      (by have := P.K.hW; simp only [sWork, sPad] at *; omega),
    hL.stk_scr (by omega) (by simp only [sTmp]; omega)⟩

section Mac

variable (HB : HBlks P.c) {Φ : Pred P} {dataA : List Instr} {da : Lay P.I.hashLen → Addr} {len dst : Nat}
  (hdA : DataA P dataA da) (hd : ∀ L : Lay P.I.hashLen, L.Ok → DataOk L (da L) len)
  (ht : TaintOk [.r11, .r12] (updRest sInner 0 dataA 0)) (hlen : len ≤ 256) (hdst : 32 ≤ dst ∧ dst + 64 ≤ 216)
  (hc : TaintOk [.r11, .r12] (Cfg.copyW (P.c.D / 4) .r12 sTmp .r11 dst))
include HB hdA hd ht hlen hdst hc

theorem hmac_piece : Piece P Φ (P.c.hmac dataA len dst) (Tt P) :=
  (hinit_piece HB).seq ((hupd_piece hdA hd ht hlen).seq (hfin_piece hlen hdst hc))

end Mac

theorem updV_taint : TaintOk [.r11, .r12] (updRest sInner 0 [.addSp .r5 fV] 0) := ⟨_, by taint_decide⟩
theorem updM_taint : TaintOk [.r11, .r12] (updRest sInner 0 [.addi .r5 .r12 sMsg] 0) := ⟨_, by taint_decide⟩

/-- `V = HMAC_K(V)`. -/
theorem hmacV_piece (HB : HBlks P.c) {Φ : Pred P} : Piece P Φ P.c.hmacV (Tt P) := by
  obtain ⟨-, -, -, hD, -, -, -, -, -⟩ := sizes P
  have hcD := P.hcD
  unfold Cfg.hmacV
  exact hmac_piece HB vDA (fun _ _ => .inl ⟨192, rfl, by decide, by omega⟩) updV_taint (by omega)
    (by decide) HB.outV

/-- `K = HMAC_K(m)`, for the message of `len` bytes at `scratch + sMsg`. -/
theorem hmacK_piece (HB : HBlks P.c) {Φ : Pred P} {len : Nat} (hlen : len ≤ 256) :
    Piece P Φ (P.c.hmac [.addi .r5 .r12 sMsg] len fK) (Tt P) :=
  hmac_piece HB (scrDA sMsg (by decide)) (fun _ _ => .inr ⟨2256, rfl, by decide, by omega⟩)
    updM_taint hlen (by decide) HB.outK

end VG.Proof.Ecdsa.Rfc6979.PPC64LE

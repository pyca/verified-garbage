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
  keep : ∀ j, j * c.D + c.D ≤ 128 → TaintOk [] (c.keepV j)

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

/-! ## The blocks of the scalars' and the hash function's sizes -/

/-- The blocks that depend on both the scalars' and the hash function's
sizes, each addressing memory only from `sp` and the pointers loaded before
it: the messages, `h`, the digest for `core` and the shifts. -/
structure CBlks (c : Cfg) : Prop where
  msgF : TaintOk [.r9, .r10, .r11] (Cfg.msg c.len c.D 0 true c.fHo)
  msgN : TaintOk [.r9, .r10, .r11] (Cfg.msg c.len c.D 0 false)
  red : c.wide = false → TaintOk [.r9, .r11] (c.reduce.drop 2 ++ Cfg.initKV)
  hPrep : c.wide = true → TaintOk [.r9, .r11] (Cfg.zero9 fX ++ Cfg.copyW (c.D / 4) .r9 0 .r11 (fX + c.len - c.D))
  xPrep : c.wide = true → c.sh ≠ 0 →
    TaintOk [.r9, .r11] (Cfg.zero9 fXc ++ Cfg.copyW (c.D / 4) .r9 0 .r11 (fXc + c.len - c.D - 1))
  conv₁ : c.wide = true → c.sh ≠ 0 → TaintOk [.r3] (c.convBody fXc (8 - c.sh))
  conv₂ : c.wide = true → c.sh ≠ 0 → TaintOk [.r3] (c.convBody fT c.sh)

/-- The scalars are at most 66 bytes. -/
theorem len_le (P : Rfc) : P.c.len ≤ 66 := by
  cases hw : P.c.wide
  · have := P.hk hw; have := P.hk16 hw; omega
  · exact (P.hW hw).1

/-! ## The messages -/

/-- `scratch` in `r9`, `d` in `r10` and the frame in `r11`. -/
def msgP (L : Lay P.I.hashLen) (r : Reg) : BitVec 64 :=
  if r = .r9 then L.scr else if r = .r10 then L.d else L.B + BitVec.ofNat 64 96

theorem msgPtrs_blk : TaintOk [] Cfg.msgPtrs := ⟨_, by taint_decide⟩

theorem msgPtrs_two (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block Cfg.msgPtrs) t fun t' => t'.sp = t.sp ∧ ∀ r ∈ [Reg.r9, .r10, .r11], t'.gpr r = msgP L r :=
  WP.mono (msgPtrs_ok hL hc) fun _ ⟨hc', _, _, h11, h9, h10⟩ => ⟨hc'.sp.trans hc.sp.symm, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h9
    · exact h10
    · exact h11⟩

theorem msg_erase (Q D b : Nat) (full : Bool) (ho : Nat) :
    (Cfg.msg Q D b full ho).map Instr.eraseImm = (Cfg.msg Q D 0 full ho).map Instr.eraseImm := by
  simp only [Cfg.msg, List.map_append, List.map_cons, List.map_nil]
  rfl

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)`. -/
theorem rekeyFull_piece (HB : HBlks P.c) (CB : CBlks P.c) {Φ : Pred P} {b : Nat} (hb : b < 2) :
    Piece P Φ (P.c.rekeyFull b) (Tt P) := by
  obtain ⟨-, -, -, hD, hD4, -, -, -, -⟩ := sizes P
  have hcD := P.hcD
  have hl := len_le P
  unfold Cfg.rekeyFull
  refine (Piece.split (Ψ := Tt P) [.r9, .r10, .r11] msgP msgPtrs_blk (fun _ _ _ _ _ hL hc => msgPtrs_two hL hc)
    (taintOk_erase CB.msgF (msg_erase _ _ _ _ _)) fun L g lr m₀ t hr _ => ?_).seq
    ((hmacK_piece HB (by omega)).seq (hmacV_piece HB))
  have hq' := lok' hr.q
  have hne := hr.c.ne
  rw [L.fHo_eq hr.q.symm P.hcD', ← hr.q]
  exact WP.mono (msg_ok hr.ok hr.c (D := P.c.D) (b := b) true L.ho (by omega) (by omega) (fun _ => hq'.1)
    (fun _ => hq'.2.1) (fun _ => hq'.2.2) (by omega)) fun _ h => ⟨h.1, trivial⟩

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)`. -/
theorem rekey_piece (HB : HBlks P.c) (CB : CBlks P.c) {Φ : Pred P} : Piece P Φ P.c.rekey (Tt P) := by
  obtain ⟨-, -, -, hD, hD4, -, -, -, -⟩ := sizes P
  have hcD := P.hcD
  unfold Cfg.rekey
  refine (Piece.split (Ψ := Tt P) [.r9, .r10, .r11] msgP msgPtrs_blk (fun _ _ _ _ _ hL hc => msgPtrs_two hL hc) CB.msgN
    fun L g lr m₀ t hr _ => ?_).seq ((hmacK_piece HB (by omega)).seq (hmacV_piece HB))
  rw [← hr.q]
  exact WP.mono (msg_ok hr.ok hr.c (D := P.c.D) (b := 0) false fH (by omega) (by omega) (fun h => nomatch h)
    (fun h => nomatch h) (fun h => nomatch h) (by decide)) fun _ h => ⟨h.1, trivial⟩

/-! ## The conversions -/

/-- `scratch` in `r3`. -/
def ScrIn (P : Rfc) : Pred P := fun L _ _ _ u => u.gpr .r3 = L.scr

theorem ldScr_blk : TaintOk [] [.addSp .r11 0, .load .d .r3 .r11 fScratch] := ⟨_, by taint_decide⟩

/-- A conversion: its block addresses memory from `scratch`, loaded first, and `sp`. -/
theorem conv_ct {Φ : Pred P} {o s : Nat} (h : TaintOk [.r3] (P.c.convBody o s)) :
    RelCT isa (Two P Φ) (P.c.conv o s) fun _ _ => True :=
  (two_wp (Ψ := ScrIn P) (two_blk ldScr_blk) fun _ _ _ _ _ hr _ => ldScr_ok hr.ok hr.c).seq
    (two_regs [.r3] (fun L _ => L.scr) (fun _ _ _ _ _ h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h) h)

/-! ## `h` and the digest for `core` -/

/-- The digest's pointer and the frame. -/
def redP (L : Lay P.I.hashLen) (r : Reg) : BitVec 64 := if r = .r9 then L.dg else L.B + BitVec.ofNat 64 96

theorem redPre_blk : TaintOk [] [.addSp .r11 0, .load .d .r9 .r11 fDigest] := ⟨_, by taint_decide⟩

theorem redPre_two (hL : L.Ok) {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block [.addSp .r11 0, .load .d .r9 .r11 fDigest]) t fun t' => t'.sp = t.sp ∧
      ∀ r ∈ [Reg.r9, .r11], t'.gpr r = redP L r := by
  have hnB := hL.nB
  refine stepAddSp (by decide) fun t₁ k₁ m₁ v₁ => ?_
  have hb : t₁.gpr .r11 = L.B + BitVec.ofNat 64 96 := by rw [v₁, hc.sp, BitVec.add_zero]
  refine stepLd (a := L.B + BitVec.ofNat 64 320) (by decide) (by decide) (by rw [hb, fr_add]; rfl)
    ((hc.kp hL k₁ m₁).inFr (by omega) (by omega)) fun t₂ k₂ m₂ v₂ => wp_nil ⟨by rw [k₂.sp, k₁.sp], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [v₂, m₁, hc.pDg]; rfl
  · rw [k₂.gpr _ (by decide), hb]; rfl

theorem initKV_blk : TaintOk [] Cfg.initKV := ⟨_, by taint_decide⟩

theorem nil_blk : TaintOk [] [] := ⟨_, by taint_decide⟩

/-- `h` (and, if `wide`, the digest for `core`), and `K` and `V`. -/
theorem start_ct (CB : CBlks P.c) {Φ : Pred P} : RelCT isa (Two P Φ) P.c.start fun _ _ => True := by
  obtain ⟨-, -, -, hD, hD4, -, -, -, -⟩ := sizes P
  have hcD := P.hcD
  have hD4' : P.c.D % 4 = 0 := by rw [P.hcD]; exact hD4
  cases hw : P.c.wide
  · simp only [Cfg.start, hw, Bool.false_eq_true, ite_false]
    rw [show P.c.reduce ++ Cfg.initKV = ([.addSp .r11 0, .load .d .r9 .r11 fDigest] : List Instr) ++
      (P.c.reduce.drop 2 ++ Cfg.initKV) by rw [← List.append_assoc]; rfl]
    exact two_split [.r9, .r11] redP redPre_blk (fun _ _ _ _ _ hL hc => redPre_two hL hc) (CB.red hw)
  · obtain ⟨hcl, -, hsh8, hsh66, -⟩ := P.hW hw
    have hQD : P.c.D < P.c.len := of_decide_eq_true hw
    have hdn : P.c.D ≤ P.I.hashLen := by rw [P.hcD']
    have he : ∀ {L : Lay P.I.hashLen}, L.q = P.c.len → L.e = 272 := fun hq => (wide_q hq ((wideL hq).trans hw)).2.2.1
    simp only [Cfg.start, hw, ite_true]
    refine (two_wp (Ψ := Tt P) ?_ fun _ _ _ _ _ hr _ =>
      WP.mono (hPrep_ok hr.ok hD4' hdn hQD (by omega) (he hr.q) hr.c) fun _ h => ⟨h.1, trivial⟩).seq
      ((two_wp (Ψ := Tt P) ?_ fun _ _ _ _ _ hr _ => ?_).seq (two_blk initKV_blk))
    · rw [show P.c.hPrep = ([.addSp .r11 0, .load .d .r9 .r11 fDigest] : List Instr) ++
        (Cfg.zero9 fX ++ Cfg.copyW (P.c.D / 4) .r9 0 .r11 (fX + P.c.len - P.c.D)) by
          simp only [Cfg.hPrep, List.append_assoc]]
      exact two_split [.r9, .r11] redP redPre_blk (fun _ _ _ _ _ hL hc => redPre_two hL hc) (CB.hPrep hw)
    · unfold Cfg.xPrep
      split
      · exact two_blk nil_blk
      · next hsh =>
        have hl66 := hsh66 hsh
        refine (two_wp (Ψ := Tt P) ?_ fun _ _ _ _ _ hr _ => ?_).seq (conv_ct (CB.conv₁ hw hsh))
        · rw [show (([.addSp .r11 0, .load .d .r9 .r11 fDigest] : List Instr) ++ Cfg.zero9 fXc ++
              Cfg.copyW (P.c.D / 4) .r9 0 .r11 (fXc + P.c.len - P.c.D - 1)) =
              ([.addSp .r11 0, .load .d .r9 .r11 fDigest] : List Instr) ++
              (Cfg.zero9 fXc ++ Cfg.copyW (P.c.D / 4) .r9 0 .r11 (fXc + P.c.len - P.c.D - 1)) by
                simp only [List.append_assoc]]
          exact two_split [.r9, .r11] redP redPre_blk (fun _ _ _ _ _ hL hc => redPre_two hL hc) (CB.xPrep hw hsh)
        · have he' := he hr.q
          rw [show fXc + P.c.len - P.c.D - 1 = fXc + (P.c.len - P.c.D - 1) by omega]
          exact WP.mono (dig_ok hr.ok hD4' hdn (o := fXc) (off := P.c.len - P.c.D - 1) (by decide)
            (by simp only [fXc]; omega) (by decide) (by omega) hr.c) fun _ h => ⟨h.1, trivial⟩
    · have he' := he hr.q
      have hcw := P.hcw
      by_cases hsh : P.c.sh = 0
      · simp only [Cfg.xPrep, hsh, ite_true]
        exact wp_nil ⟨hr.c, trivial⟩
      · exact WP.mono (xPrep_ok hr.ok hD4' hdn hQD (hsh66 hsh) (P.hcw (hsh66 hsh)) hsh hsh8 he' hr.c)
          fun _ h => ⟨h.1, trivial⟩

/-! ## The candidate -/

theorem keepV_piece (HB : HBlks P.c) {Φ : Pred P} (hw : P.c.wide = true) {k : Nat} (hk : k * P.c.D + P.c.D ≤ 128) :
    Piece P Φ (.block (P.c.keepV k)) (Tt P) :=
  Piece.blk (HB.keep k hk) fun _ _ _ _ _ hr _ =>
    WP.mono (keepV_ok hr.ok (by rw [P.hcD]; exact P.K.hH.hD4) hk ((wide_q hr.q ((wideL hr.q).trans hw)).2.2.1) hr.c)
      fun _ h => ⟨h.1, trivial⟩

/-- The first `k` `V`s of the candidate. -/
theorem candW_piece (HB : HBlks P.c) {Φ : Pred P} (hw : P.c.wide = true) : ∀ k, k * P.c.D ≤ 128 →
    Piece P Φ (P.c.candW k) (Tt P)
  | 0, _ => by
    rw [Cfg.candW]
    exact Piece.blk nil_blk fun _ _ _ _ _ hr _ => wp_nil ⟨hr.c, trivial⟩
  | k + 1, hk => by
    have hk' : k * P.c.D + P.c.D ≤ 128 := by rw [Nat.succ_mul] at hk; exact hk
    rw [Cfg.candW]
    exact (candW_piece HB hw k (by omega)).seq ((hmacV_piece HB).seq (keepV_piece HB hw hk'))

/-- The candidate: its calls and blocks leak the same in both runs. -/
theorem cand_ct (HB : HBlks P.c) (CB : CBlks P.c) {Φ : Pred P} : RelCT isa (Two P Φ) P.c.cand fun _ _ => True := by
  cases hw : P.c.wide
  · rw [show P.c.cand = P.c.hmacV by simp only [Cfg.cand, hw, Bool.false_eq_true, ite_false]]
    exact (hmacV_piece HB).rel fun _ _ _ _ _ _ => trivial
  · simp only [Cfg.cand, hw, ite_true]
    obtain ⟨-, -, -, -, -, hm, -⟩ := P.hW hw
    refine RelCT.seq (candW_piece HB hw P.c.m hm).ct ?_
    unfold Cfg.candTop
    split
    · exact two_blk nil_blk
    · next hsh => exact conv_ct (CB.conv₂ hw hsh)

/-! ## One candidate -/

abbrev coreRd (P : Rfc) (L : Lay P.I.hashLen) : List Region :=
  [⟨L.d, P.R.E.curve.len⟩, ⟨dgAddr P L, P.R.E.curve.len⟩, ⟨kAddr L, P.R.E.curve.len⟩]
abbrev coreWr (P : Rfc) (L : Lay P.I.hashLen) : List Region :=
  [⟨L.out, 2 * P.R.E.curve.len⟩, ⟨L.scr, 8192⟩]

theorem coreAt (hL : L.Ok) (hq : L.q = P.c.len) {u : State} (hc : Ctx L g lr m₀ u) (ha : CoreRegs L u) :
    (Proof.Ecdsa.Instance.signContract P.R.E PPC64LE.abi).pre (u.callEntry.withRegions (coreRd P L) (coreWr P L)) ∧
      Covers (coreRd P L ++ coreWr P L) (u.rd ++ u.wr) ∧ Covers (coreWr P L) u.wr := by
  obtain ⟨h3, h4, h5, h6, h7⟩ := ha
  have hQ : P.R.E.curve.len = L.q := by rw [← P.hcl, hq]
  obtain ⟨o₁, o₂, o₃, o₄, c₁, c₂, c₃, n₁, n₂, n₃, n₄, n₅, hcov⟩ := core_regions hL hq
  refine ⟨corePre P.R h3 h4 h5 h6 h7 (by rw [hQ]; exact o₁) (by rw [hQ]; exact o₂) (by rw [hQ]; exact o₃)
    (by rw [hQ]; exact o₄) (by rw [hQ]; exact c₁) (by rw [hQ]; exact c₂) (by rw [hQ]; exact c₃)
    (by rw [hQ]; exact n₁) (by rw [hQ]; exact n₂) (by rw [hQ]; exact n₃) (by rw [hQ]; exact n₄) n₅, ?_, ?_⟩
  · simp only [coreRd, coreWr, hQ]
    exact hc.covers hcov
  · simp only [coreWr, hQ]
    refine hc.coversW fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨L.OUT, by simp, within_base _ (Nat.le_refl _)⟩
    · exact ⟨L.SCR, by simp, within_base _ (Nat.le_refl _)⟩

theorem core_ct {i : Nat} :
    RelCT isa (Two P fun L _ _ m₀ u => P₁ P L m₀ i u ∧ CoreRegs L u) (.call P.c.coreN P.c.coreC)
      fun _ _ => True := by
  rw [P.hcN, P.hcC]
  refine RelCT.callEx P.R.V P.R.ct fun s₁ s₂ ⟨L, _, _, _, _, _, _, h⟩ => ?_
  have A := coreAt h.ok h.q h.c₁ h.f₁.2
  have B := coreAt h.ok h.q h.c₂ h.f₂.2
  refine ⟨_, _, _, _, A.1, B.1, ?_, A.2.1, A.2.2, B.2.1, B.2.2⟩
  obtain ⟨-, a3, a4, a5, a6, a7⟩ := h.f₁
  obtain ⟨-, b3, b4, b5, b6, b7⟩ := h.f₂
  sig_pub [Proof.Ecdsa.Instance.signContract, Proof.Ecdsa.Instance.signSig, Spec.Ecdsa.scratchWords,
    PPC64LE.abi, PPC64LE.argRegs, stackBelow]
  exact ⟨by rw [h.c₁.sp, h.c₂.sp], by rw [a3, b3], by rw [a4, b4], by rw [a5, b5], by rw [a6, b6],
    by rw [a7, b7]⟩

theorem coreArgs_blk (c : Cfg) : TaintOk [] c.coreArgs := by
  have e : ∀ (w : Bool) (x : Nat), x = fX ∨ x = fXc → TaintOk []
      (([.addSp .r11 0, .load .d .r3 .r11 fOut, .load .d .r4 .r11 fD] : List Instr) ++
        (if w then [.addSp .r5 x, .addSp .r6 fT] else [.load .d .r5 .r11 fDigest, .addSp .r6 fV]) ++
        [.load .d .r7 .r11 fScratch]) := by
    intro w x hx
    cases w <;> rcases hx with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  exact e c.wide c.fDg (by unfold Cfg.fDg; split <;> simp)

theorem goOn_blk : TaintOk [] Cfg.goOn := ⟨_, by taint_decide⟩
theorem again_blk : TaintOk [] Cfg.again := ⟨_, by taint_decide⟩
theorem stop_blk : TaintOk [] Cfg.stop := ⟨_, by taint_decide⟩

/-- After a candidate: whether to go on, and what the next piece needs. -/
def After (P : Rfc) (i : Nat) : Pred P := fun L _ _ m₀ t =>
  isa.eval (.nonzero .d .r12) t = some (decide (i < exitAt P L m₀)) ∧
    ((i < exitAt P L m₀ ∧ LoopInv P L m₀ (i + 1) t) ∨ (¬ i < exitAt P L m₀ ∧ Exit P L m₀ i t))

theorem tryOne_ct (HB : HBlks P.c) (CB : CBlks P.c) {i : Nat} :
    RelCT isa (Two P fun L _ _ m₀ u => LoopInv P L m₀ i u) P.c.tryOne (Two P (After P i)) := by
  refine two_wp ?_ fun L g lr m₀ t hr hi => WP.mono (tryOne_ok hr.ok hr.q hr.gf hr.c hi) fun t' ⟨hc', h⟩ =>
    ⟨hc', ?_⟩
  · rw [Cfg.tryOne]
    refine (two_wp (Ψ := fun L _ _ m₀ u => P₁ P L m₀ i u) (cand_ct HB CB) fun L g lr m₀ t hr hi =>
      try₁_ok hr.ok hr.q hr.gf hr.c hi).seq ?_
    refine (two_wp (Ψ := fun L _ _ m₀ u => P₁ P L m₀ i u ∧ CoreRegs L u) (two_blk (coreArgs_blk _))
      fun L g lr m₀ t hr hi => try₂_ok hr.ok hr.q hr.c hi).seq ?_
    refine (two_wp (Ψ := fun L _ _ m₀ u => P₃ P L m₀ i u) core_ct
      fun L g lr m₀ t hr hi => try₃_ok hr.ok hr.q hr.c hi.1 hi.2).seq ?_
    refine (two_wp (Ψ := fun L _ _ m₀ u => Mid P L m₀ i u) (two_blk goOn_blk)
      fun L g lr m₀ t hr hi => try₄_ok hr.ok hr.q hr.c hi).seq ?_
    refine RelCT.ite (fun s₁ s₂ ⟨L, g₁, g₂, lr₁, lr₂, m₁, m₂, h⟩ => ?_) ?_ ?_
    · rw [h.f₁.dec, h.f₂.dec]
      refine congrArg some (decide_eq_decide.mpr ?_)
      rw [go_iff h.q h.f₁.lt h.f₁.fails, go_iff h.q h.f₂.lt h.f₂.fails, h.x]
    · exact RelCT.mono (P := Two P fun L _ _ m₀ u => Mid P L m₀ i u)
        ((rekey_piece HB CB).ct.seq (two_blk again_blk)) (fun _ _ h => h.1) fun _ _ h => h
    · exact RelCT.mono (two_blk stop_blk) (fun _ _ h => h.1) fun _ _ h => h
  · rcases h with ⟨he, hx⟩ | ⟨he, hx⟩
    · have hn : ¬ i < exitAt P L m₀ := fun hlt => by
        have := (go_iff hr.q hx.lt hx.fails).mpr hlt
        rcases hx.last with h | h
        · exact h this.1
        · omega
      exact ⟨by rw [he]; simp [hn], .inr ⟨hn, hx⟩⟩
    · have hn : i < exitAt P L m₀ :=
        (go_iff hr.q (by have := hx.lt; omega) fun j hj => hx.fails j (by omega)).mp
          ⟨hx.fails i (by omega), hx.lt⟩
      exact ⟨by rw [he]; simp [hn], .inl ⟨hn, hx⟩⟩

/-! ## The loop -/

theorem loop_ct (HB : HBlks P.c) (CB : CBlks P.c) :
    RelCT isa (Two P fun L _ _ m₀ u => LoopInv P L m₀ 0 u) (.loop P.c.tryOne (.nonzero .d .r12))
      (Two P fun L _ _ m₀ u => ∃ i, Exit P L m₀ i u) := by
  refine RelCT.mono (RelCT.loop (I := fun n => Two P fun L _ _ m₀ u => LoopInv P L m₀ (P.c.tries - n) u ∧
    n ≤ P.c.tries) (fun n => ?_) P.c.tries) (fun _ _ h => Two.mono (fun _ _ _ _ _ hi => ⟨by
      rw [Nat.sub_self]; exact hi, Nat.le_refl _⟩) h) fun _ _ h => h
  by_cases hn : n ≤ P.c.tries
  · refine RelCT.mono (tryOne_ct HB CB (i := P.c.tries - n)) (fun _ _ h => Two.mono (fun _ _ _ _ _ hi => hi.1) h)
      fun s₁ s₂ ⟨L, g₁, g₂, lr₁, lr₂, m₁, m₂, h⟩ => ⟨by rw [h.f₁.1, h.f₂.1, h.x], fun he => ?_, fun he => ?_⟩
    · rw [h.f₁.1] at he
      have hx : ¬ P.c.tries - n < exitAt P L m₁ := by simpa using he
      have hx' : ¬ P.c.tries - n < exitAt P L m₂ := by rw [← h.x]; exact hx
      refine ⟨L, g₁, g₂, lr₁, lr₂, m₁, m₂, h.ok, h.q, h.gf, h.x, h.c₁, h.c₂, h.y₁, h.y₂, ?_, ?_⟩
      · rcases h.f₁.2 with ⟨h', -⟩ | ⟨-, hx₁⟩
        · exact absurd h' hx
        · exact ⟨_, hx₁⟩
      · rcases h.f₂.2 with ⟨h', -⟩ | ⟨-, hx₂⟩
        · exact absurd h' hx'
        · exact ⟨_, hx₂⟩
    · rw [h.f₁.1] at he
      have hx : P.c.tries - n < exitAt P L m₁ := by simpa using he
      have hx' : P.c.tries - n < exitAt P L m₂ := by rw [← h.x]; exact hx
      obtain ⟨-, i₁⟩ | ⟨h', -⟩ := h.f₁.2
      · obtain ⟨-, i₂⟩ | ⟨h', -⟩ := h.f₂.2
        · have := i₁.lt
          refine ⟨n - 1, by omega, L, g₁, g₂, lr₁, lr₂, m₁, m₂, h.ok, h.q, h.gf, h.x, h.c₁, h.c₂, h.y₁, h.y₂,
            ⟨?_, by omega⟩, ⟨?_, by omega⟩⟩
          · rwa [show P.c.tries - (n - 1) = P.c.tries - n + 1 by omega]
          · rwa [show P.c.tries - (n - 1) = P.c.tries - n + 1 by omega]
        · exact absurd hx' h'
      · exact absurd hx h'
  · exact RelCT.of_false fun _ _ ⟨_, _, _, _, _, _, _, h⟩ => hn h.f₁.2

/-! ## The frame's body -/

theorem initCnt_blk (c : Cfg) : TaintOk [] c.initCnt :=
  taintOk_erase (is₀ := [.li .r9 0, .addSp .r11 0, .store .d .r9 .r11 fCnt]) ⟨_, by taint_decide⟩ rfl

theorem wipe_blk (b w : Bool) : TaintOk [] (Cfg.wipe b w) := by
  cases b <;> cases w
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩

theorem rest_ct (HB : HBlks P.c) (CB : CBlks P.c) :
    RelCT isa (Two P (Tt P))
      (.seq P.c.start (.seq (P.c.rekeyFull 0) (.seq (P.c.rekeyFull 1)
        (.seq (.block P.c.initCnt) (.seq (.loop P.c.tryOne (.nonzero .d .r12))
          (.block (Cfg.wipe P.c.hHigh P.c.wide)))))))
      fun _ _ => True := by
  refine (two_wp (Ψ := fun L _ _ m₀ u => QA P L m₀ u) (start_ct CB)
    fun L g lr m₀ t hr _ => stageA_ok hr.ok hr.q hr.c).seq ?_
  refine (two_wp (Ψ := fun L _ _ m₀ u => QB P L m₀ (K₁ P L m₀) (V₁ P L m₀) u)
    ((rekeyFull_piece HB CB (by decide)).rel fun _ _ _ _ _ _ => trivial)
    fun L g lr m₀ t hr ha => stageB_ok hr.ok hr.q hr.gf hr.c ha hr.y).seq ?_
  refine (two_wp (Ψ := fun L _ _ m₀ u => QB P L m₀ (kv0 P L m₀).1 (kv0 P L m₀).2 u)
    ((rekeyFull_piece HB CB (by decide)).rel fun _ _ _ _ _ _ => trivial)
    fun L g lr m₀ t hr hb => stageC_ok hr.ok hr.q hr.gf hr.c hb).seq ?_
  refine (two_wp (Ψ := fun L _ _ m₀ u => LoopInv P L m₀ 0 u) (two_blk (initCnt_blk _))
    fun L g lr m₀ t hr hb => stageD_ok hr.ok hr.q hr.c hb).seq ?_
  exact (loop_ct HB CB).seq (two_blk (wipe_blk _ _))

/-! ## The whole function -/

/-- Two runs whose public data agree, as the contract says. -/
def Pre2 (P : Rfc) (ns : List String) (s₁ s₂ : State) : Prop :=
  (rfcP P ns).pre s₁ ∧ (rfcP P ns).pre s₂ ∧ (rfcP P ns).pub s₁ s₂

/-- In the inner frame's body. -/
def Entered (P : Rfc) (ns : List String) (a b : State) : Prop :=
  ∃ σ₁ σ₂, Pre2 P ns σ₁ σ₂ ∧ a = entered (extra P.c.hHigh P.c.wide) σ₁ ∧ b = entered (extra P.c.hHigh P.c.wide) σ₂

theorem lay_eq {ns : List String} (hns : ∀ n ∈ [P.K.H.initN, P.K.H.updN, P.K.H.finN], n ∈ ns) {σ₁ σ₂ : State}
    (h : Pre2 P ns σ₁ σ₂) :
    lay P.I.hashLen P.I.ecdsa.curve.len P.K.H P.K.f σ₁ = lay P.I.hashLen P.I.ecdsa.curve.len P.K.H P.K.f σ₂ := by
  obtain ⟨-, -, hsp, h3, h4, h5, h6, -, h8, hsy⟩ := h
  have hfa : (fun n => if n ∈ [P.K.H.initN, P.K.H.updN, P.K.H.finN] then σ₁.syms n else 0) =
      fun n => if n ∈ [P.K.H.initN, P.K.H.updN, P.K.H.finN] then σ₂.syms n else 0 := funext fun n => by
    split
    · next hn => exact hsy n (hns n hn)
    · rfl
  simp only [lay, hsp, h3, h4, h5, h6, h8, hfa]

theorem block_two {is : List Instr} {R : State → State → Prop} (hsp : ∀ a b, R a b → a.sp = b.sp)
    (h : TaintOk [] is) : RelCT isa R (.block is) fun _ _ => True :=
  let ⟨_, h⟩ := h
  VG.RelCT.taint (A := taint) (Taint.ofRegs []) (fun a b hr => ⟨hsp a b hr, fun r hr => by
    simp only [Taint.mem_ofRegs, List.not_mem_nil] at hr⟩) h

theorem saveArgs_blk : TaintOk [] Cfg.saveArgs := ⟨_, by taint_decide⟩

theorem save_ct {ns : List String} (hns : ∀ n ∈ [P.K.H.initN, P.K.H.updN, P.K.H.finN], n ∈ ns) :
    RelCT isa (Entered P ns) (.block Cfg.saveArgs) (Two P (Tt P)) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := block_two (R := Entered P ns) (fun a b ⟨σ₁, σ₂, h, ea, eb⟩ => by
      rw [ea, eb]; show σ₁.sp - 48 - BitVec.ofNat 64 (256 + extra P.c.hHigh P.c.wide) =
        σ₂.sp - 48 - BitVec.ofNat 64 (256 + extra P.c.hHigh P.c.wide); rw [h.2.2.1])
    saveArgs_blk _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨σ₁, σ₂, h, rfl, rfl⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := entry_ok (pre_conv h.1)
  obtain ⟨_, u₂, x₂, y₂⟩ := entry_ok (pre_conv h.2.1)
  rw [← e_eq (lay_q P σ₁)] at x₁
  rw [← e_eq (lay_q P σ₂)] at x₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  have z₁ := syOk_entry h.1 (t := s₁') ((Exec.syms x₁).trans rfl)
  have z₂ := syOk_entry h.2.1 (t := s₂') ((Exec.syms x₂).trans rfl)
  rw [← lay_eq hns h] at y₂ z₂
  refine ⟨ht, _, _, _, _, _, _, _, lay_ok (pre_conv h.1), lay_q P σ₁, ⟨rfl, rfl⟩, ?_, y₁, y₂, z₁, z₂, trivial,
    trivial⟩
  obtain ⟨-, -, h4, h5, -, hr, -⟩ := h.2.2
  have e : (result P.I σ₁.mem (σ₁.gpr .r4) (σ₁.gpr .r5)).2 = (result P.I σ₂.mem (σ₁.gpr .r4) (σ₁.gpr .r5)).2 := by
    rw [hr, h4, h5]
  simp only [exitAt, show (lay P.I.hashLen P.I.ecdsa.curve.len P.K.H P.K.f σ₁).d = σ₁.gpr .r4 from rfl,
    show (lay P.I.hashLen P.I.ecdsa.curve.len P.K.H P.K.f σ₁).dg = σ₁.gpr .r5 from rfl, e]

/-- Constant time: only the pointers, the table and the number of candidates
RFC 6979 tries affect it. -/
theorem sign_ct (HB : HBlks P.c) (CB : CBlks P.c) {ns : List String}
    (hns : ∀ n ∈ [P.K.H.initN, P.K.H.updN, P.K.H.finN], n ∈ ns) :
    ConstantTime isa (rfcP P ns).pre (rfcP P ns).pub P.c.sign := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  rw [Cfg.sign]
  refine RelCT.seq (R := fun a b => ∃ σ₁ σ₂, Pre2 P ns σ₁ σ₂ ∧ a = lrSaved σ₁ ∧ b = lrSaved σ₂) ?_ ?_
  · intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
    obtain ⟨ht, -⟩ := block_two (is := [.mflr .r0]) (R := Pre2 P ns) (fun _ _ h => h.2.2.1) ⟨_, by taint_decide⟩
      _ _ _ _ _ _ hp e₁ e₂
    have w : ∀ s, WP isa (.block [.mflr .r0]) s fun s' => s' = lrSaved s := fun s =>
      Proof.Mont.PPC64LE.wp_step exec_mflr (wp_nil rfl)
    obtain ⟨_, u₁, x₁, y₁⟩ := w s₁
    obtain ⟨_, u₂, x₂, y₂⟩ := w s₂
    obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
    obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
    exact ⟨ht, s₁, s₂, hp, y₁, y₂⟩
  refine RelCT.seq (RelCT.frame (fun _ _ ⟨σ₁, σ₂, h, ea, eb⟩ => by rw [ea, eb]; exact h.2.2.1)
    (RelCT.alloc (R := fun _ _ => True) (fun _ _ ⟨_, _, ⟨σ₁, σ₂, h, ea, eb⟩, ea', eb'⟩ => by
      rw [ea', eb', ea, eb]; show σ₁.sp - 48 = σ₂.sp - 48; rw [h.2.2.1]) ?_)) ?_
  · refine RelCT.mono (P := Entered P ns) ?_ (fun a b ⟨_, _, ⟨_, _, ⟨σ₁, σ₂, h, ea, eb⟩, ea', eb'⟩, ea'', eb''⟩ =>
      ⟨σ₁, σ₂, h, by rw [ea'', ea', ea]; rfl, by rw [eb'', eb', eb]; rfl⟩) fun _ _ h => h
    rw [Cfg.body]
    exact (save_ct hns).seq (rest_ct HB CB)
  · exact block_two (fun _ _ h => h) ⟨_, by taint_decide⟩

end VG.Proof.Ecdsa.Rfc6979.PPC64LE

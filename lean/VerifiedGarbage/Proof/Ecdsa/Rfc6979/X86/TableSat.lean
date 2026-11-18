module

public import VerifiedGarbage.Proof.HashTable.Basic
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.HashTable.Basic
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Instrs
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Layout
public import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Table
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Frame
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Correct
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86.TaintErase
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.ICall
import VerifiedGarbage.Proof.Framework.X86.Syms
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Correct
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86.TaintErase
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.ICall
meta import VerifiedGarbage.Proof.Framework.X86.Syms
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Instrs
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Layout
meta import VerifiedGarbage.Spec.Ecdsa.Rfc6979.Table
meta import VerifiedGarbage.Proof.Framework.X86.CallWith
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Frame

/-! ### `Ecdsa.Rfc6979.X86.TableSpec`, which only this module used -/

section

/-! ### `Ecdsa.Rfc6979.X86.Table`, which only this module used -/

section

/-! ### `Ecdsa.Rfc6979.X86.CT`, which only this module used -/

section

/-!
# Deterministic ECDSA on x86 (32-bit): constant time, up to the number of candidates

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Table.lean`): two runs whose public
data agree have the same layout, and stop at the same candidate (`exitAt`,
from the contract's leakage: the number of candidates RFC 6979 tries).
Between the frame's entry and its release they are related by `Two`: both
satisfy `Ctx` with that layout (and `Φ`, what the next piece needs). The
blocks address only the stack and the buffers, from registers that agree
(the taint analysis, of the blocks whose contents depend on the curve:
`RfcT`, each curve's `RfcCurve.blk`), or, for the byte loops, from registers
both runs set alike; an indirect call reaches, through the table, whose
address our arguments hold, the same function in both runs (`tcall_piece`);
each call, in a frame of its arguments, is of constant-time code whose public
data agree (`hi_rel`, `upd_rel`, `hf_rel`, `callWithR_ct`); and the loop's
branch agrees, since in both runs it goes on after candidate `i` iff `i` is
before the candidate it stops at (`go_iff`). The frame's allocation and
release access no memory (`alloc_ct`), and its entry, from `esp` and then
the table's address, which agree, gives `Two` (`start_ct`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.Impl.Ecdsa.Rfc6979.X86
open VG.Proof.Pbkdf2.Whole.X86 (hi_rel hf_rel hi_frame hf_frame)
open VG.Proof.Pbkdf2.Stream.X86 (upd_rel upd_frame)
open VG.X86.Wp

/-! ## Frames -/

/-- Two runs of a frame allocated on the stack leak the same trace when the
runs of its body, from the states after the allocation, do: the allocation
and the release access no memory. -/
theorem alloc_ct {n : Nat} {body : Prog isa} {P R : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s₁ s₂, P s₁ s₂ ∧ a = allocState n s₁ ∧ b = allocState n s₂) body R) :
    RelCT isa P (.frame (.alloc n) body (.free n)) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  have hpush : ∀ {s a : State}, isa.push (.alloc n) s = some a → a = allocState n s := by
    intro s a h
    simp only [isa, push] at h
    split at h <;> [cases h; cases h]
    rfl
  cases e₁ with
  | frame p₁ b₁ _ =>
    cases e₂ with
    | frame p₂ b₂ _ =>
      have ea := hpush p₁
      have eb := hpush p₂
      subst ea eb
      obtain ⟨rfl, -⟩ := hb _ _ _ _ _ _ ⟨s₁, s₂, hp, rfl, rfl⟩ b₁ b₂
      exact ⟨by simp only [addrs], trivial⟩

/-- `RelCT.callWith`, for a frame popped into any register `r`. -/
theorem callWithR_ct {rs : List Reg} {r : Reg} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {Pr : State → State → Prop} (rd wr : List Region)
    (hP : ∀ s₁ s₂, Pr s₁ s₂ → CallPre k rs rd wr s₁ ∧ CallPre k rs rd wr s₂ ∧
      s₁.gpr .esp = s₂.gpr .esp ∧
      k.pub ((pushed rs s₁).callEntry.withRegions rd wr) ((pushed rs s₂).callEntry.withRegions rd wr)) :
    RelCT isa Pr (.frame (.push rs) (.call n c) (.pop r rs.length)) fun _ _ => True := by
  refine VG.X86.RelCT.frame (fun s₁ s₂ h => (hP _ _ h).2.2.1) (VG.X86.RelCT.call hv hct rd wr ?_)
  rintro _ _ ⟨s₁, s₂, h, rfl, rfl⟩
  obtain ⟨k₁, k₂, hsp, hpub⟩ := hP _ _ h
  refine ⟨k₁.pre, k₂.pre, hpub, by rw [pushed_rd, pushed_wr]; exact k₁.cov, by rw [pushed_wr]; exact k₁.covw,
    by rw [pushed_rd, pushed_wr]; exact k₂.cov, by rw [pushed_wr]; exact k₂.covw, ?_⟩
  rw [pushed_esp, pushed_esp, hsp]

/-! ## Two runs -/

/-- What each of two runs has, between the frame's entry and its release. -/
abbrev Env (P : RfcHash) := Lay P.I.hashLen × (Reg → BitVec 32) × (Reg → BitVec 32) × Mem × Mem

/-- What one run's piece needs and gives. -/
abbrev Pr (P : RfcHash) := Lay P.I.hashLen → Mem → State → Prop

/-- Nothing. -/
abbrev Tt (P : RfcHash) : Pr P := fun _ _ _ => True

/-- What the code needs of the layout: `core`'s, and the table of `P`. -/
def LOk (P : RfcHash) {dn : Nat} (L : Lay dn) : Prop := CoreOk P L ∧ TabL P L

/-- Two runs with the layout and saved registers of `e`, that stop at the
same candidate, each satisfying `Ctx` and `Φ`. -/
def TwoAt (P : RfcHash) (Φ : Pr P) (e : Env P) (a b : State) : Prop :=
  e.1.Ok ∧ LOk P e.1 ∧ exitAt P e.1 e.2.2.2.1 = exitAt P e.1 e.2.2.2.2 ∧ Ctx e.1 e.2.1 e.2.2.2.1 a ∧
    Ctx e.1 e.2.2.1 e.2.2.2.2 b ∧ Φ e.1 e.2.2.2.1 a ∧ Φ e.1 e.2.2.2.2 b

/-- Two runs with the same layout that stop at the same candidate. -/
def Two (P : RfcHash) (Φ : Pr P) (a b : State) : Prop := ∃ e, TwoAt P Φ e a b

variable {P : RfcHash}

theorem two_exists {Φ : Pr P} {c : Prog isa} {Q : State → State → Prop}
    (h : ∀ e, RelCT isa (TwoAt P Φ e) c Q) : RelCT isa (Two P Φ) c Q :=
  VG.RelCT.exists_ h

theorem Two.mono {Φ Ψ : Pr P} (h : ∀ L m₀ t, Φ L m₀ t → Ψ L m₀ t) {a b : State}
    (ht : Two P Φ a b) : Two P Ψ a b :=
  let ⟨e, hL, hq, hx, c₁, c₂, f₁, f₂⟩ := ht
  ⟨e, hL, hq, hx, c₁, c₂, h _ _ _ f₁, h _ _ _ f₂⟩

/-- Code whose runs leak the same, and which keeps `Ctx` and establishes `Ψ`. -/
theorem two_wp {c : Prog isa} {Φ Ψ : Pr P}
    (hct : RelCT isa (Two P Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay P.I.hashLen) g m₀ (t : State), L.Ok → LOk P L → Ctx L g m₀ t → Φ L m₀ t →
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

theorem esp_two {dn : Nat} {L : Lay dn} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}
    (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) : t₁.gpr .esp = t₂.gpr .esp :=
  c₁.esp.trans c₂.esp.symm

/-- Registers that agree in two runs. -/
abbrev Agree (P : RfcHash) (Φ : Pr P) (rs : List Reg) : Prop :=
  ∀ (L : Lay P.I.hashLen) (t₁ t₂ : State) g₁ g₂ m₁ m₂, Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ → Φ L m₁ t₁ →
    Φ L m₂ t₂ → ∀ r ∈ rs, t₁.gpr r = t₂.gpr r

/-- Code whose addresses depend only on the registers `rs`, which agree. -/
theorem two_prog {c : Prog isa} {Φ : Pr P} (rs : List Reg) (hrs : Agree P Φ rs)
    (h : ∃ hc, (taint.check (τr rs) c hc).isSome = true) :
    RelCT isa (Two P Φ) c fun _ _ => True :=
  let ⟨_, h⟩ := h
  VG.RelCT.taint (A := taint) (τr rs)
    (fun _ _ ⟨_, _, _, _, c₁, c₂, f₁, f₂⟩ => agree_regs (hrs _ _ _ _ _ _ _ c₁ c₂ f₁ f₂)) h

/-- A block whose addresses depend only on the registers `rs`, which agree. -/
theorem two_blk {is : List Instr} {Φ : Pr P} (rs : List Reg) (hrs : Agree P Φ rs) (h : TaintOk rs is) :
    RelCT isa (Two P Φ) (.block is) fun _ _ => True :=
  two_prog rs hrs h

theorem espOnly {Φ : Pr P} : Agree P Φ [.esp] := by
  intro L t₁ t₂ _ _ _ _ c₁ c₂ _ _ r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact esp_two c₁ c₂

/-! ## Pieces: related in two runs, and keeping `Ctx` in each -/

/-- Code that, from `Φ`, leaks the same in two runs and gives `Ψ`, keeping
`Ctx`, in each. -/
structure Piece (P : RfcHash) (Φ : Pr P) (c : Prog isa) (Ψ : Pr P) : Prop where
  ct : RelCT isa (Two P Φ) c (Two P Ψ)
  wp : ∀ (L : Lay P.I.hashLen) g m₀ (t : State), L.Ok → LOk P L → Ctx L g m₀ t → Φ L m₀ t →
    WP isa c t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t'

namespace Piece

variable {Φ Ψ Χ : Pr P} {a b c : Prog isa}

theorem of (hct : RelCT isa (Two P Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay P.I.hashLen) g m₀ (t : State), L.Ok → LOk P L → Ctx L g m₀ t → Φ L m₀ t →
      WP isa c t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t') : Piece P Φ c Ψ :=
  ⟨two_wp hct hw, hw⟩

theorem seq (h₁ : Piece P Φ a Ψ) (h₂ : Piece P Ψ b Χ) : Piece P Φ (.seq a b) Χ :=
  ⟨h₁.ct.seq h₂.ct, fun L g m₀ t hL hk hc hφ =>
    WP.seq (WP.mono (h₁.wp L g m₀ t hL hk hc hφ) fun _ ⟨c', ψ⟩ => h₂.wp L g m₀ _ hL hk c' ψ)⟩

/-- What the relational proofs of the loop use. -/
theorem rel (h : Piece P Φ c Ψ) {Φ' : Pr P} (hp : ∀ L m₀ t, Φ' L m₀ t → Φ L m₀ t) :
    RelCT isa (Two P Φ') c fun _ _ => True :=
  h.ct.mono (fun _ _ => Two.mono hp) fun _ _ _ => trivial

end Piece

/-- A block whose addresses depend only on the registers `rs`, which agree. -/
theorem Piece.blk {is : List Instr} {Φ Ψ : Pr P} (rs : List Reg) (hrs : Agree P Φ rs) (ht : TaintOk rs is)
    (hw : ∀ (L : Lay P.I.hashLen) g m₀ (t : State), L.Ok → LOk P L → Ctx L g m₀ t → Φ L m₀ t →
      WP isa (.block is) t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t') : Piece P Φ (.block is) Ψ :=
  Piece.of (two_blk rs hrs ht) hw

/-- A block whose addresses depend only on `esp`. -/
theorem Piece.blkS {is : List Instr} {Φ Ψ : Pr P} (ht : TaintOk [.esp] is)
    (hw : ∀ (L : Lay P.I.hashLen) g m₀ (t : State), L.Ok → LOk P L → Ctx L g m₀ t → Φ L m₀ t →
      WP isa (.block is) t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t') : Piece P Φ (.block is) Ψ :=
  Piece.blk [.esp] espOnly ht hw

/-- The blocks of the curve. -/
theorem rT (P : RfcHash) : RfcT (cfgC P.R.E P.R.big P.R.sh) := P.R.blk

/-! ## The byte loops -/

theorem cpLoop_taint : ∃ hc, (taint.check (τr [.esi, .ebx, .ecx]) Cfg.cpLoop hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- A byte copy's registers. -/
abbrev CpA (P : RfcHash) (p q : Lay P.I.hashLen → BitVec 32) (n : Nat) : Pr P := fun L _ u =>
  u.gpr .esi = q L ∧ u.gpr .ebx = p L ∧ u.gpr .ecx = BitVec.ofNat 32 n

/-- The byte loop, from registers that agree. -/
theorem cp_ct {Φ : Pr P} {p q : Lay P.I.hashLen → BitVec 32} {n : Nat}
    (h : ∀ L m₀ u, Φ L m₀ u → CpA P p q n L m₀ u) : RelCT isa (Two P Φ) Cfg.cpLoop fun _ _ => True :=
  two_prog [.esi, .ebx, .ecx] (fun _ _ _ _ _ _ _ _ _ f₁ f₂ r hr => by
    obtain ⟨a₁, b₁, c₁⟩ := h _ _ _ f₁; obtain ⟨a₂, b₂, c₂⟩ := h _ _ _ f₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact a₁.trans a₂.symm
    · exact b₁.trans b₂.symm
    · exact c₁.trans c₂.symm) cpLoop_taint

/-! ## The indirect calls -/

/-- What an indirect call of `n` needs of the table in each run: its word
`j` (on entry) is `n`'s address, which is the layout's, and of `ts` an
indirect call reaches `n`'s `c`. -/
def TabFn (P : RfcHash) (j : Nat) (n : String) (c : Prog isa) (ts : List (String × Prog isa)) : Prop :=
  ∀ (L : Lay P.I.hashLen) g m₀ (t : State), L.Ok → LOk P L → Ctx L g m₀ t →
    m₀.readW (addr L.tb (4 * j)) 32 = t.syms n ∧
      ts.find? (fun q => (t.syms q.1).setWidth 64 == (t.syms n).setWidth 64) = some (n, c) ∧ t.syms n = L.fa n

theorem tfn_init : TabFn P 0 P.F.hiN P.F.hiC P.f.init := fun L _ _ _ _ hk hc => by
  have hok := hc.tabOk; have htm := hc.tabMem; have hf := hc.fsy
  rw [hk.2.1, hk.2.2] at hok; rw [hk.2.1] at htm hf
  exact ⟨htm.1, hok.i, hf _ (by simp)⟩

theorem tfn_upd : TabFn P 1 P.F.H.updN P.F.H.updC P.f.upd := fun L _ _ _ _ hk hc => by
  have hok := hc.tabOk; have htm := hc.tabMem; have hf := hc.fsy
  rw [hk.2.1, hk.2.2] at hok; rw [hk.2.1] at htm hf
  exact ⟨htm.2.1, hok.u, hf _ (by simp)⟩

theorem tfn_fin : TabFn P 2 P.F.hfN P.F.hfC P.f.fin := fun L _ _ _ _ hk hc => by
  have hok := hc.tabOk; have htm := hc.tabMem; have hf := hc.fsy
  rw [hk.2.1, hk.2.2] at hok; rw [hk.2.1] at htm hf
  exact ⟨htm.2.2, hok.f, hf _ (by simp)⟩

/-- What only `ebx` changing keeps. -/
def KeepsB (Φ : Pr P) : Prop :=
  ∀ L m₀ (t u : State), Φ L m₀ t → (∀ r, r ≠ .ebx → u.gpr r = t.gpr r) → u.mem = t.mem → u.syms = t.syms →
    Φ L m₀ u

theorem tblk1_taint : TaintOk [.esp] [.mov .ebx (argM 5)] := ⟨_, by taint_decide⟩

/-- The indirect call of the table's function `j`, pushing `rs`: in both
runs of the same function, `n`'s (the table's word `j` holds the layout's
address of `n`). -/
theorem tcall_piece {Φ Ψ : Pr P} {j : Nat} (hj : 4 * j + 4 ≤ 24)
    (ht : TaintOk [.ebx] [.mov .ebx (.mem (VG.Impl.Pbkdf2.Stream.X86.at_ .ebx (4 * j)))]) {n : String}
    {c : Prog isa} {ts : List (String × Prog isa)} {rs : List Reg} (hn : TabFn P j n c ts) (hΦ : KeepsB Φ)
    (hcall : Piece P Φ (.frame (.push rs) (.call n c) (.pop .eax rs.length)) Ψ) :
    Piece P Φ (Cfg.tcall j ts rs) Ψ := by
  refine ⟨?_, fun L g m₀ t hL hk hc hφ => ?_⟩
  · unfold Cfg.tcall
    have s₁ : Piece P Φ (.block [.mov .ebx (argM 5)]) fun L m₀ u => Φ L m₀ u ∧ u.gpr .ebx = L.tb :=
      Piece.blkS tblk1_taint fun L g m₀ t hL hk hc hφ =>
        WP.mono (arg_ok hL hc (d := .ebx) (by decide) (i := 5) (by decide)) fun u h =>
          ⟨h.ctx, hΦ _ _ _ _ hφ h.keep h.mem h.syms, h.val⟩
    have s₂ : Piece P (fun L m₀ u => Φ L m₀ u ∧ u.gpr .ebx = L.tb)
        (.block [.mov .ebx (.mem (VG.Impl.Pbkdf2.Stream.X86.at_ .ebx (4 * j)))])
        fun L m₀ u => Φ L m₀ u ∧ u.gpr .ebx = L.fa n ∧ u.syms n = L.fa n ∧
          ts.find? (fun q => (u.syms q.1).setWidth 64 == (u.syms n).setWidth 64) = some (n, c) :=
      Piece.blk [.ebx] (fun _ _ _ _ _ _ _ _ _ f₁ f₂ r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact f₁.2.trans f₂.2.symm) ht
        fun L g m₀ t hL hk hc ⟨hφ, hb⟩ => wp_ldm hb (hc.inTab hL hj) fun u v => WP.block_nil (by
          have u₂ := Upd.of_wp hL hc (d := .ebx) (by decide) v
          obtain ⟨hw, hf, hfa⟩ := hn L g m₀ t hL hk hc
          exact ⟨u₂.ctx, hΦ _ _ _ _ hφ u₂.keep u₂.mem u₂.syms, by rw [u₂.val, hc.tabWord hL hj, hw, hfa],
            by rw [u₂.syms, hfa], by rw [u₂.syms]; exact hf⟩)
    refine s₁.ct.seq (s₂.ct.seq ?_)
    cases ts with
    | nil => exact RelCT.of_false fun _ _ ⟨_, _, _, _, _, _, f₁, _⟩ => by simp at f₁
    | cons q ts =>
      refine RelCT.frame_icalls_of_call (hcall.ct.mono (fun _ _ => Two.mono fun _ _ _ h => h.1) fun _ _ h => h)
        fun s₁ s₂ ⟨e, _, _, _, c₁, c₂, f₁, f₂⟩ => ⟨?_, fun u₁ u₂ p₁ p₂ => ?_⟩
      · simp only [addrs, esp_two c₁ c₂]
      · obtain ⟨-, -, -, rfl⟩ := push_some p₁
        obtain ⟨-, -, -, rfl⟩ := push_some p₂
        refine ⟨(e.1.fa n).setWidth 64, by show some _ = _; rw [pushed_gpr _ _ (by decide), f₁.2.1],
          by show some _ = _; rw [pushed_gpr _ _ (by decide), f₂.2.1], ?_, ?_, rfl⟩
        · rw [← f₁.2.2.1, icallTarget_congr (s₂ := s₁) fun q _ => by
            show ((pushed rs s₁).syms q.1).setWidth 64 = (s₁.syms q.1).setWidth 64
            rw [show (pushed rs s₁).syms = s₁.syms from pushRegs_syms s₁ rs]]
          exact f₁.2.2.2
        · rw [← f₂.2.2.1, icallTarget_congr (s₂ := s₂) fun q _ => by
            show ((pushed rs s₂).syms q.1).setWidth 64 = (s₂.syms q.1).setWidth 64
            rw [show (pushed rs s₂).syms = s₂.syms from pushRegs_syms s₂ rs]]
          exact f₂.2.2.2
  · obtain ⟨hw, hf, -⟩ := hn L g m₀ t hL hk hc
    exact tcall_ok hL hc hj hw hf fun t' hc' hm hr hs => hcall.wp L g m₀ t' hL hk hc' (hΦ _ _ _ _ hφ hr hm hs)

/-! ## HMAC's calls -/

/-- HMAC's `init`'s arguments. -/
def IA (P : RfcHash) : Pr P := fun L _ u =>
  u.gpr .edi = L.sc + BitVec.ofNat 32 0 ∧ u.gpr .esi = L.sc + BitVec.ofNat 32 192 ∧
    u.gpr .edx = L.F + BitVec.ofNat 32 0 ∧ u.gpr .ecx = BitVec.ofNat 32 P.F.H.D ∧
    u.gpr .ebp = L.sc + BitVec.ofNat 32 384

/-- The streaming `update`'s arguments: the inner state holding `cnt`
bytes, the `len` bytes at `dv`, and the working space. -/
def UA (P : RfcHash) (cnt : Nat) (dv : Lay P.I.hashLen → BitVec 32) (len : Nat) : Pr P := fun L _ u =>
  u.gpr .edi = L.sc + BitVec.ofNat 32 0 ∧ u.gpr .esi = BitVec.ofNat 32 cnt ∧ u.gpr .eax = 0 ∧
    u.gpr .edx = dv L ∧ u.gpr .ecx = BitVec.ofNat 32 len ∧ u.gpr .ebp = L.sc + BitVec.ofNat 32 384

/-- HMAC's `finalize`'s arguments: the states, the `cnt` bytes the inner one
holds, the MAC's place in the frame at `dst`, and the working space. -/
def FA (P : RfcHash) (cnt dst : Nat) : Pr P := fun L _ u =>
  u.gpr .edx = L.sc + BitVec.ofNat 32 0 ∧ u.gpr .esi = L.sc + BitVec.ofNat 32 192 ∧
    u.gpr .eax = BitVec.ofNat 32 cnt ∧ u.gpr .ecx = 0 ∧ u.gpr .edi = L.F + BitVec.ofNat 32 dst ∧
    u.gpr .ebp = L.sc + BitVec.ofNat 32 384

theorem hinit_piece : Piece P (IA P) (.frame (.push init5) (.call P.F.hiN P.F.hiC) (.pop .eax init5.length)) (Tt P) := by
  refine Piece.of (two_exists fun e => hi_rel P.ok.hi (sp := e.1.F) fun _ _ ⟨hL, _, _, c₁, c₂, a₁, a₂⟩ =>
    ⟨initA (P := P) hL c₁ a₁.1 a₁.2.1 a₁.2.2.1 a₁.2.2.2.1 a₁.2.2.2.2,
      initA (P := P) hL c₂ a₂.1 a₂.2.1 a₂.2.2.1 a₂.2.2.2.1 a₂.2.2.2.2, c₁.esp, c₂.esp⟩)
    fun L g m₀ u hL _ hc a => ?_
  have hS := P.ok.hH.hS
  refine WP.of_syms (hi_frame (fun m m' p q msg hb => P.ok.hH.repr m m' p q msg (fun i hi => hb i (by rw [P.ok.hH.hS]; exact hi)))
    P.ok.hi P.ok.hiSp P.ok.hiSU
    (initA (P := P) hL hc a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2) fun v af _ _ hsy => ?_)
  have hsafe : ∀ r ∈ [(⟨(L.sc + BitVec.ofNat 32 0).setWidth 64, P.ok.hH.SH.stateBytes⟩ : Region),
      ⟨(L.sc + BitVec.ofNat 32 192).setWidth 64, P.ok.hH.SH.stateBytes⟩,
      ⟨(L.sc + BitVec.ofNat 32 384).setWidth 64, P.ok.Wi * 8⟩], Region.Sub r ⟨L.scr, 2256⟩ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> exact scr_work' hL (by omega_arith) (by first | nums | (rw [hS]; nums))
  exact ⟨hc.keep (hsy := hsy) hL af.rd af.wr (af.cs .esp (by decide)) af.frame
    (safe_call hL hc (fun r hr => .inr (.inl (sub_trans (hsafe r hr) (Region.sub_prefix (by omega_arith)))))
      (Nat.le_refl _)), trivial⟩

theorem upd_piece {cnt : Nat} {dv : Lay P.I.hashLen → BitVec 32} {len : Nat}
    (hd : ∀ L : Lay P.I.hashLen, L.Ok → DataOk L (dv L) len) (hlen : len ≤ 256) :
    Piece P (UA P cnt dv len) (.frame (.push upd6) (.call P.F.H.updN P.F.H.updC) (.pop .eax upd6.length))
      (Tt P) := by
  refine Piece.of (two_exists fun e => upd_rel P.ok.hH (sp := e.1.F) fun _ _ ⟨hL, _, _, c₁, c₂, a₁, a₂⟩ =>
    ⟨updA (P := P) hL c₁ (hd _ hL) hlen a₁.1 a₁.2.1 a₁.2.2.1 a₁.2.2.2.1 a₁.2.2.2.2.1 a₁.2.2.2.2.2,
      updA (P := P) hL c₂ (hd _ hL) hlen a₂.1 a₂.2.1 a₂.2.2.1 a₂.2.2.2.1 a₂.2.2.2.2.1 a₂.2.2.2.2.2, c₁.esp, c₂.esp⟩)
    fun L g m₀ w hL _ hcw a => ?_
  have hsp : Region.Sub (Proof.Pbkdf2.Stream.X86.stk w) (below L.F 76) := by
    show Region.Sub (below (w.gpr .esp) 48) _; rw [hcw.esp]; exact hL.below48
  refine WP.of_syms (upd_frame P.ok.hH (updA (P := P) hL hcw (hd _ hL) hlen a.1 a.2.1 a.2.2.1 a.2.2.2.1
    a.2.2.2.2.1 a.2.2.2.2.2) fun w' af _ hsy => ?_)
  have hws : ∀ r ∈ [(⟨(L.sc + BitVec.ofNat 32 0).setWidth 64, P.F.H.S⟩ : Region),
      ⟨(L.sc + BitVec.ofNat 32 384).setWidth 64, P.ok.hH.Wb⟩], Region.Sub r ⟨L.scr, 2256⟩ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> exact scr_work' hL (by omega_arith) (by nums)
  have h76 : Region.Sub (below L.F 76) ⟨L.B, 76⟩ := by rw [hL.below_F]; exact sub_refl _
  refine ⟨hcw.keep (hsy := hsy) hL af.rd af.wr (af.cs .esp (by decide)) af.frame fun r hr => ?_, trivial⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact .inr (.inl (sub_trans (hws r hr) (Region.sub_prefix (by omega_arith))))
  · simp only [List.mem_singleton] at hr; subst hr
    exact .inr (.inr (.inl (sub_trans hsp (sub_trans h76 (Region.sub_prefix (by omega_arith))))))

theorem hfin_piece {cnt dst : Nat} (hdst : dst + P.F.H.D ≤ 128) :
    Piece P (FA P cnt dst) (.frame (.push fin6) (.call P.F.hfN P.F.hfC) (.pop .eax fin6.length)) (Tt P) := by
  refine Piece.of (two_exists fun e => hf_rel P.ok.hf (sp := e.1.F) fun _ _ ⟨hL, _, _, c₁, c₂, a₁, a₂⟩ =>
    ⟨finA (P := P) hL c₁ hdst a₁.1 a₁.2.1 a₁.2.2.1 a₁.2.2.2.1 a₁.2.2.2.2.1 a₁.2.2.2.2.2,
      finA (P := P) hL c₂ hdst a₂.1 a₂.2.1 a₂.2.2.1 a₂.2.2.2.1 a₂.2.2.2.2.1 a₂.2.2.2.2.2, c₁.esp, c₂.esp⟩)
    fun L g m₀ w hL _ hcw a => ?_
  have hS := P.ok.hH.hS
  have hD := P.ok.hH.hD
  refine WP.of_syms (hf_frame P.reprOK (by rw [hS]; nums) P.ok.hf P.ok.hfSp P.ok.hfSU
    (finA (P := P) hL hcw hdst a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2) fun w' af _ hsy => ?_)
  have hO : (L.F + BitVec.ofNat 32 dst).setWidth 64 = L.B + BitVec.ofNat 64 (76 + dst) := hL.frv (by nums)
  refine ⟨hcw.keep (hsy := hsy) hL af.rd af.wr (af.cs .esp (by decide)) af.frame fun r hr => ?_, trivial⟩
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact .inr (.inl (sub_trans (scr_work' hL (by omega_arith) (by rw [hS]; nums)) (Region.sub_prefix (by omega_arith))))
  · rw [hO, hD]; exact safe_low L (by nums)
  · exact .inr (.inl (sub_trans (scr_work' hL (by omega_arith) (by nums)) (Region.sub_prefix (by omega_arith))))
  · rw [show Proof.Pbkdf2.Whole.X86.stk w = below (w.gpr .esp) 76 from rfl, hcw.esp, hL.below_F]
    exact .inr (.inr (.inl (Region.sub_prefix (by omega_arith))))

theorem keepsB_ia : KeepsB (IA P) := fun _ _ _ _ ⟨d, s, x, k, r⟩ hr _ _ => ⟨(hr _ (by decide)).trans d,
  (hr _ (by decide)).trans s, (hr _ (by decide)).trans x, (hr _ (by decide)).trans k, (hr _ (by decide)).trans r⟩

theorem keepsB_ua {cnt : Nat} {dv : Lay P.I.hashLen → BitVec 32} {len : Nat} : KeepsB (UA P cnt dv len) :=
  fun _ _ _ _ ⟨d, s, a, x, k, r⟩ hr _ _ => ⟨(hr _ (by decide)).trans d, (hr _ (by decide)).trans s,
    (hr _ (by decide)).trans a, (hr _ (by decide)).trans x, (hr _ (by decide)).trans k, (hr _ (by decide)).trans r⟩

theorem keepsB_fa {cnt dst : Nat} : KeepsB (FA P cnt dst) :=
  fun _ _ _ _ ⟨d, s, a, x, k, r⟩ hr _ _ => ⟨(hr _ (by decide)).trans d, (hr _ (by decide)).trans s,
    (hr _ (by decide)).trans a, (hr _ (by decide)).trans x, (hr _ (by decide)).trans k, (hr _ (by decide)).trans r⟩

/-! ## HMAC through the table -/

theorem tblk2_taint0 : TaintOk [.ebx] [.mov .ebx (.mem (VG.Impl.Pbkdf2.Stream.X86.at_ .ebx (4 * 0)))] :=
  ⟨_, by taint_decide⟩
theorem tblk2_taint1 : TaintOk [.ebx] [.mov .ebx (.mem (VG.Impl.Pbkdf2.Stream.X86.at_ .ebx (4 * 1)))] :=
  ⟨_, by taint_decide⟩
theorem tblk2_taint2 : TaintOk [.ebx] [.mov .ebx (.mem (VG.Impl.Pbkdf2.Stream.X86.at_ .ebx (4 * 2)))] :=
  ⟨_, by taint_decide⟩

theorem initArgs_taint : TaintOk [.esp] Cfg.initArgs := ⟨_, by taint_decide⟩

theorem updVArgs_taint : TaintOk [.esp] Cfg.updVArgs := ⟨_, by taint_decide⟩

theorem updM1_taint : TaintOk [.esp] (Cfg.updMArgs 1) := ⟨_, by taint_decide⟩

theorem fin0_taint : TaintOk [.esp] (Cfg.finArgs 0 fV) := ⟨_, by taint_decide⟩

theorem fin1_taint : TaintOk [.esp] (Cfg.finArgs 1 fK) := ⟨_, by taint_decide⟩

/-- HMAC's states for `K`. -/
theorem initK_piece {Φ : Pr P} : Piece P Φ (cfgOf P).initK (Tt P) :=
  (Piece.blkS (Ψ := IA P) initArgs_taint fun _ _ _ _ hL hk hc _ =>
    WP.mono (initArgs_ok hL hk.2 hc) fun _ ⟨c, _, _, d, s, x, k, r⟩ => ⟨c, d, s, x, k, r⟩).seq
    (tcall_piece (by decide) tblk2_taint0 tfn_init keepsB_ia hinit_piece)

/-- The inner state updated with `V`. -/
theorem updV_piece {Φ : Pr P} : Piece P Φ (cfgOf P).updV (Tt P) :=
  (Piece.blkS (Ψ := UA P P.F.H.B (fun L => L.F + BitVec.ofNat 32 fV) P.F.H.D) updVArgs_taint
    fun _ _ _ _ hL hk hc _ =>
      WP.mono (updVArgs_ok hL hk.2 hc) fun _ ⟨c, _, _, d, s, a, x, k, r⟩ => ⟨c, d, s, a, x, k, r⟩).seq
    (tcall_piece (by decide) tblk2_taint1 tfn_upd keepsB_ua
      (upd_piece (fun L _ => .inl ⟨fV, rfl, by simp only [fV]; nums⟩) (by nums)))

/-- The inner state updated with the message's `len` bytes. -/
theorem updM_piece {Φ : Pr P} {len : Nat} (hlen : len ≤ 256) (ht : TaintOk [.esp] (Cfg.updMArgs len)) :
    Piece P Φ ((cfgOf P).updM len) (Tt P) :=
  (Piece.blkS (Ψ := UA P (P.F.H.B + P.F.H.D) (fun L => L.sc + BitVec.ofNat 32 sMsg) len) ht
    fun _ _ _ _ hL hk hc _ =>
      WP.mono (updMArgs_ok hL hk.2 hc len) fun _ ⟨c, _, _, d, s, a, x, k, r⟩ => ⟨c, d, s, a, x, k, r⟩).seq
    (tcall_piece (by decide) tblk2_taint1 tfn_upd keepsB_ua
      (upd_piece (fun L _ => .inr ⟨sMsg, rfl, by simp only [sMsg]; omega_arith, by simp only [sMsg]; omega_arith⟩) hlen))

/-- The MAC, of `D + len` bytes, to the frame at `dst`. -/
theorem fin_piece {Φ : Pr P} {len dst : Nat} (hdst : dst + P.F.H.D ≤ 128) (ht : TaintOk [.esp] (Cfg.finArgs len dst)) :
    Piece P Φ ((cfgOf P).fin len dst) (Tt P) :=
  (Piece.blkS (Ψ := FA P (P.F.H.B + P.F.H.D + len) dst) ht fun _ _ _ _ hL hk hc _ =>
    WP.mono (finArgs_ok hL hk.2 hc len dst) fun _ ⟨c, _, _, d, s, a, x, k, r⟩ => ⟨c, d, s, a, x, k, r⟩).seq
    (tcall_piece (by decide) tblk2_taint2 tfn_fin keepsB_fa (hfin_piece hdst))

/-- HMAC's states saved (`toSave`), or restored. -/
theorem copyS_piece {Φ : Pr P} (toSave : Bool) :
    Piece P Φ (.seq (.block (Cfg.copyArgs toSave)) Cfg.cpLoop) (Tt P) := by
  refine Piece.of ((two_wp (Ψ := CpA P (fun L => L.sc + BitVec.ofNat 32 (if toSave then sSave else sInner))
      (fun L => L.sc + BitVec.ofNat 32 (if toSave then sInner else sSave)) 384) (two_blk [.esp] espOnly ?_)
    fun L g m₀ t hL _ hc _ => WP.mono (copyArgs_ok hL hc toSave) fun _ ⟨c, _, si, bx, cx⟩ => ⟨c, si, bx, cx⟩).seq
    (cp_ct fun _ _ _ h => h)) fun L g m₀ t hL _ hc _ => WP.mono (copyS_ok hL hc toSave rfl rfl) fun _ h => ⟨h.1, trivial⟩
  cases toSave
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩

/-! ## HMAC -/

theorem hmacVS_piece {Φ : Pr P} : Piece P Φ (cfgOf P).hmacVS (Tt P) :=
  initK_piece.seq ((copyS_piece true).seq (updV_piece.seq (fin_piece (by simp only [fV]; nums) fin0_taint)))

theorem hmacVR_piece {Φ : Pr P} : Piece P Φ (cfgOf P).hmacVR (Tt P) :=
  (copyS_piece false).seq (updV_piece.seq (fin_piece (by simp only [fV]; nums) fin0_taint))

/-- `K = HMAC_K(V ‖ msg)`, for the message's `len` bytes. -/
theorem hmacK_piece {Φ : Pr P} {len : Nat} (hlen : len ≤ 256) (hu : TaintOk [.esp] (Cfg.updMArgs len))
    (hf : TaintOk [.esp] (Cfg.finArgs len fK)) (fresh : Bool) :
    Piece P Φ ((cfgOf P).hmacK fresh len) (Tt P) := by
  unfold Cfg.hmacK
  cases fresh
  · exact (copyS_piece false).seq (updV_piece.seq ((updM_piece hlen hu).seq (fin_piece (by simp only [fK]; nums) hf)))
  · exact initK_piece.seq (updV_piece.seq ((updM_piece hlen hu).seq (fin_piece (by simp only [fK]; nums) hf)))

/-! ## `K` and `V` from a message -/

/-- `scratch` in `edi` and `d` in `esi`. -/
def PtrsIn (P : RfcHash) : Pr P := fun L _ u => u.gpr .edi = L.sc ∧ u.gpr .esi = L.a1

theorem msgPtrs_piece {Φ : Pr P} : Piece P Φ (.block Cfg.msgPtrs) (PtrsIn P) :=
  Piece.blkS ⟨_, by taint_decide⟩ fun _ _ _ _ hL _ hc _ =>
    WP.mono (ptrs_ok hL hc) fun _ ⟨c, _, d, s⟩ => ⟨c, d, s⟩

/-- The message `b (‖ d ‖ h)` at `scratch + sMsg`. -/
theorem msg_piece {b : Nat} {full : Bool} (ht : TaintOk [.esp, .edi, .esi] ((cfgOf P).msg b full)) :
    Piece P (PtrsIn P) (.block ((cfgOf P).msg b full)) (Tt P) :=
  Piece.blk [.esp, .edi, .esi] (fun _ _ _ _ _ _ _ c₁ c₂ f₁ f₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact esp_two c₁ c₂
      · exact f₁.1.trans f₂.1.symm
      · exact f₁.2.trans f₂.2.symm) ht
    fun _ _ _ _ hL hk hc hp => WP.mono (msg_ok hL hk.1.1 hc hp.1 hp.2 b full) fun _ h => ⟨h.1, trivial⟩

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)`. -/
theorem rekeyFull_piece {Φ : Pr P} (b : Nat) (hb : b < 2) : Piece P Φ ((cfgOf P).rekeyFull b) (Tt P) := by
  have hlen : 1 + 2 * (cfgOf P).len ≤ 256 := by show 1 + 2 * P.Q ≤ 256; nums
  have ht : TaintOk [.esp, .edi, .esi] ((cfgOf P).msg b true) := by
    obtain rfl | rfl : b = 0 ∨ b = 1 := by omega_using [hb]
    · exact (rT P).msgF
    · exact (rT P).msgF₁
  unfold Cfg.rekeyFull
  exact msgPtrs_piece.seq ((msg_piece ht).seq ((hmacK_piece hlen (rT P).updM (rT P).finM _).seq hmacVS_piece))

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)`. -/
theorem rekey_piece {Φ : Pr P} : Piece P Φ (cfgOf P).rekey (Tt P) := by
  unfold Cfg.rekey
  exact msgPtrs_piece.seq ((msg_piece (by exact (rT P).msgN)).seq
    ((hmacK_piece (by decide) updM1_taint fin1_taint _).seq hmacVS_piece))

/-- `Ctx` with other saved registers, which are the same. -/
theorem Ctx.regen {dn : Nat} {L : Lay dn} {g g' : Reg → BitVec 32} {m₀ : Mem} {u : State} (hc : Ctx L g' m₀ u)
    (h : ∀ p ∈ Impl.Ecdsa.Rfc6979.X86.saved, g' p.1 = g p.1) : Ctx L g m₀ u :=
  { hc with saved := fun (p : Reg × Nat) hp => (hc.saved p hp).trans (h p hp) }

/-! ## The candidate -/

/-- After `j` of the candidate's `V`s, from some `K` and `V`. -/
abbrev CJ (P : RfcHash) (j : Nat) : Pr P := fun L m₀ u => ∃ g' t₀ K V₀, CI P L g' m₀ t₀ K V₀ j u

/-- `T`'s length, `j` blocks. -/
abbrev TL (P : RfcHash) (j : Nat) : Pr P := fun L _ u => tlen L u.mem = BitVec.ofNat 32 (j * P.F.H.D)

/-- The arguments of the copy of `V` to `T`'s end, and `j` blocks. -/
abbrev KA (P : RfcHash) (j : Nat) : Pr P := fun L m₀ u =>
  CpA P (fun L => L.F + BitVec.ofNat 32 (fT + j * P.F.H.D)) (fun L => L.F + BitVec.ofNat 32 fV) P.F.H.D L m₀ u ∧
    TL P j L m₀ u

/-- One `V`'s blocks and calls leak the same in both runs. -/
theorem candStep_trace {j : Nat} (hj : j < P.nV) :
    RelCT isa (Two P (CJ P j)) (cfgOf P).candStep fun _ _ => True := by
  obtain ⟨-, hND, -⟩ := nV_facts P
  obtain ⟨-, -, -, -, hD16, hD64, -, -, -, -, -, -, -, -, -, -, hQ66, -, -⟩ := P.sizes
  have hb : (j + 1) * P.F.H.D ≤ 136 :=
    Nat.le_trans (Nat.mul_le_mul (show j + 1 ≤ P.nV by omega_using [hj]) (Nat.le_refl P.F.H.D)) (by omega_using [hND, hD64, hQ66])
  have hjD : (j + 1) * P.F.H.D = j * P.F.H.D + P.F.H.D := Nat.succ_mul _ _
  refine (two_wp (Ψ := TL P j) (hmacVR_piece.rel fun _ _ _ _ => trivial) fun L g m₀ t hL hk hc hJ => ?_).seq
    ((two_wp (Ψ := KA P j) (two_blk [.esp] espOnly ⟨_, by taint_decide⟩) fun L g m₀ t hL hk hc hl =>
      WP.mono (keepArgs_ok hL hk.2 hc hl) fun u ⟨c, hm, si, bx, cx⟩ =>
        ⟨c, ⟨si, bx, cx⟩, by show tlen L u.mem = _; rw [hm]; exact hl⟩).seq
    ((two_wp (Ψ := TL P j) (cp_ct fun _ _ _ h => h.1) fun L g m₀ t hL hk hc ⟨⟨si, bx, cx⟩, hl⟩ => ?_).seq
      (two_blk [.esp] espOnly (by exact (rT P).tStep))))
  · obtain ⟨_, _, _, _, hI⟩ := hJ
    have hnb := hL.nB
    have hS : SavedK P L t.mem (kOf P L t.mem) := by rw [hI.k]; exact hI.saved
    refine WP.mono (hmacVR_ok hL hk.2 hc hS) fun u ⟨hc₁, hf₁, _⟩ => ⟨hc₁, ?_⟩
    show tlen L u.mem = _
    rw [← hI.len]
    have hfTl : fTlen = 152 := rfl
    exact hf₁.readW (Region.contains_self _ _) (fun r hr => by
      simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_SCR (by omega_using [hfTl])
      · exact Offset.disjoint_base _ (by omega_using [hfTl]) (by omega_using [hfTl])) (by decide)
  · have hnb := hL.nB
    have hfV : fV = 64 := rfl
    have hfT : fT = 376 := rfl
    have hfTl : fTlen = 152 := rfl
    have eS : (L.F + BitVec.ofNat 32 fV).setWidth 64 = L.B + BitVec.ofNat 64 (76 + fV) := hL.frv (by decide)
    have eD : (L.F + BitVec.ofNat 32 (fT + j * P.F.H.D)).setWidth 64 =
        L.B + BitVec.ofNat 64 (76 + fT + j * P.F.H.D) := by rw [hL.frv (by omega_using [hb, hjD, hfT]), Nat.add_assoc]
    refine WP.mono (cpLoop_ok hL hc (S := L.F + BitVec.ofNat 32 fV) (D := L.F + BitVec.ofNat 32 (fT + j * P.F.H.D))
        (n := P.F.H.D) (by omega_using [hD16]) (by omega_using [hD64])
        (by rw [hL.frN (by decide)]; have := hL.e28; have := hL.e588; omega_using [hD64, hfV])
        (by rw [hL.frN (by omega_using [hb, hjD, hfT])]; have := hL.e28; have := hL.e588; omega_using [hb, hjD, hfT])
        (by rw [eS]; exact ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains _ (by decide) (by omega_using [hD64, hfV]) (by omega_using [])⟩)
        (by rw [eD]; exact hc.inFrW (by omega_using []) (by omega_using [hb, hjD, hfT]) hL)
        (by rw [eS, eD]; exact Offset.disjoint _ (.inl (by omega_using [hD64, hfV, hfT])) (by omega_using [hD64, hfV]) (by omega_using [hb, hjD, hfT]))
        (by rw [eD]; exact safe_high L (by omega_using [hfT]) (by omega_using [hb, hjD, hfT])) si bx cx) fun u ⟨hcu, hf, _, _⟩ => ⟨hcu, ?_⟩
    show tlen L u.mem = _
    rw [← hl]
    rw [eD] at hf
    exact hf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by omega_using [hfT, hfTl])) (by omega_using [hfTl]) (by omega_using [hb, hjD, hfT])) (by decide)

/-- The loop of the candidate's `V`s, in two runs: at the same block. -/
theorem candLoop_ct :
    RelCT isa (Two P (CJ P 0)) (.loop (cfgOf P).candStep .b) (Two P (CJ P P.nV)) := by
  obtain ⟨hN1, hND, -⟩ := nV_facts P
  obtain ⟨-, -, -, -, -, hD64, -, -, -, -, -, -, -, -, -, -, hQ66, -, -⟩ := P.sizes
  have h := VG.RelCT.loop (M := isa) (c := .b) (Q := Two P (CJ P P.nV))
    (fun n => fun s₁ s₂ => 0 < n ∧ n ≤ P.nV ∧ Two P (CJ P (P.nV - n)) s₁ s₂) (n := P.nV) (body := (cfgOf P).candStep)
    (fun n => by
      refine fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨hn0, hnN, hp⟩ e₁ e₂ => ?_
      have hj : P.nV - n < P.nV := by omega_using [hN1, hn0]
      have hb : (P.nV - n + 1) * P.F.H.D ≤ 136 :=
        Nat.le_trans (Nat.mul_le_mul (show P.nV - n + 1 ≤ P.nV by omega_using [hN1, hn0]) (Nat.le_refl P.F.H.D)) (by omega_using [hND, hD64, hQ66])
      obtain ⟨ht, hq⟩ := (two_wp (Ψ := fun L m₀ u => CJ P (P.nV - n + 1) L m₀ u ∧
          u.cf = some (decide ((P.nV - n + 1) * P.F.H.D < P.Q))) (candStep_trace hj)
        fun L g m₀ t hL hk hc ⟨g', t₀, K, V₀, hI⟩ => WP.mono (step_ok hL hk.2 hb hI)
          fun u ⟨hI', hcf⟩ => ⟨hI'.ctx.regen fun p hp => (hI.ctx.saved p hp).symm.trans (hc.saved p hp),
            ⟨g', t₀, K, V₀, hI'⟩, hcf⟩) s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
      refine ⟨ht, ?_, ?_, ?_⟩
      · obtain ⟨_, _, _, _, _, _, f₁, f₂⟩ := hq
        show s₁'.cf = s₂'.cf; rw [f₁.2, f₂.2]
      · intro hf
        obtain ⟨e, hL, hk, hx, c₁, c₂, f₁, f₂⟩ := hq
        have : ¬ (P.nV - n + 1) * P.F.H.D < P.Q := by
          intro h'; have := f₁.2; rw [decide_eq_true h'] at this; exact absurd (this.symm.trans hf) (by decide)
        have hNn : P.nV - n + 1 = P.nV := by
          have : ¬ P.nV - n + 1 < P.nV := fun h => this ((nV_lt P _).mp h)
          omega_using [hN1, hn0, this]
        exact ⟨e, hL, hk, hx, c₁, c₂, hNn ▸ f₁.1, hNn ▸ f₂.1⟩
      · intro hf
        obtain ⟨e, hL, hk, hx, c₁, c₂, f₁, f₂⟩ := hq
        have h' : (P.nV - n + 1) * P.F.H.D < P.Q := by
          by_contra h'; have := f₁.2; rw [decide_eq_false h'] at this; exact absurd (this.symm.trans hf) (by decide)
        have hlt := (nV_lt P (P.nV - n)).mpr h'
        refine ⟨n - 1, by omega_using [hn0], by omega_using [hlt], by omega_using [hnN], e, hL, hk, hx, c₁, c₂, ?_, ?_⟩ <;>
          rw [show P.nV - (n - 1) = P.nV - n + 1 by omega_using [hn0, hnN]]
        · exact f₁.1
        · exact f₂.1)
  exact h.mono (fun s₁ s₂ hp => ⟨hN1, Nat.le_refl _, by rwa [Nat.sub_self]⟩) fun _ _ h => h

/-- `scratch` in `edi`. -/
theorem scrPtr_ct {Φ : Pr P} : RelCT isa (Two P Φ) (.block Cfg.scrPtr) (Two P fun L _ u => u.gpr .edi = L.sc) :=
  two_wp (two_blk [.esp] espOnly ⟨_, by taint_decide⟩) fun _ _ _ _ hL _ hc _ =>
    WP.mono (scrPtr_ok hL hc) fun _ h => ⟨h.1, h.2.2.1⟩

theorem scrRegs : Agree P (fun L _ u => u.gpr .edi = L.sc) [.esp, .edi] := by
  intro L _ _ _ _ _ _ c₁ c₂ f₁ f₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact esp_two c₁ c₂
  · exact f₁.trans f₂.symm

theorem candTop_ct {Φ : Pr P} : RelCT isa (Two P Φ) (cfgOf P).candTop fun _ _ => True := by
  cases hb : P.R.big
  · rw [show (cfgOf P).candTop = .block [] by
      simp only [Cfg.candTop, show (cfgOf P).big = false from hb, Bool.false_eq_true, ite_false]]
    exact two_blk [.esp] espOnly ⟨_, by taint_decide⟩
  · rw [show (cfgOf P).candTop = .seq (.block Cfg.scrPtr) (.block ((cfgOf P).conv fT (cfgOf P).sh)) by
      simp only [Cfg.candTop, show (cfgOf P).big = true from hb, ite_true]]
    exact scrPtr_ct.seq (two_blk [.esp, .edi] scrRegs (by exact (rT P).convT hb))

/-- The candidate: its calls, blocks and loops leak the same in both runs. -/
theorem cand_ct :
    RelCT isa (Two P fun L _ t => SavedK P L t.mem (kOf P L t.mem)) (cfgOf P).cand fun _ _ => True := by
  unfold Cfg.cand
  exact (two_wp (Ψ := CJ P 0) (two_blk [.esp] espOnly ⟨_, by taint_decide⟩) fun L g m₀ t hL hk hc hS =>
    WP.mono (tInit_ci hL hc hS) fun u hI => ⟨hI.ctx, _, _, _, _, hI⟩).seq (candLoop_ct.seq candTop_ct)

/-- `core`, in a frame of its arguments, which agree. -/
theorem core_ct {i : Nat} :
    RelCT isa (Two P fun L m₀ u => P₁ P L m₀ i u ∧ CoreRegs P L u)
      (.frame (.push init5) (.call (cfgOf P).coreN (cfgOf P).coreC) (.pop .ecx 5)) fun _ _ => True :=
  two_exists fun e => callWithR_ct (rs := core5) P.R.coreX P.R.coreCT (coreRd P e.1) (coreWr P e.1)
    fun _ _ ⟨hL, hk, _, c₁, c₂, ⟨_, a₁⟩, ⟨_, a₂⟩⟩ => by
      obtain ⟨v₀, v₁, v₂, v₃, v₄⟩ := core_argv hL c₁ a₁ (rd := coreRd P e.1) (wr := coreWr P e.1)
      obtain ⟨w₀, w₁, w₂, w₃, w₄⟩ := core_argv hL c₂ a₂ (rd := coreRd P e.1) (wr := coreWr P e.1)
      refine ⟨core_callPre hL hk.1 c₁ a₁, core_callPre hL hk.1 c₂ a₂, esp_two c₁ c₂,
        by rw [State.withRegions_gpr, State.withRegions_gpr, core_esp c₁, core_esp c₂],
        by rw [v₀, w₀], by rw [v₁, w₁], by rw [v₂, w₂], by rw [v₃, w₃], by rw [v₄, w₄], ?_⟩
      intro c hc
      rw [← hk.1.2] at hc
      rw [core_syms c₁ hc, core_syms c₂ hc]

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
    fun _ _ _ _ hL hk hc hi => try₁_ok hL hk.2 hc hi).seq ?_
  refine (two_wp (Ψ := fun L m₀ u => P₁ P L m₀ i u ∧ CoreRegs P L u)
    (two_blk [.esp] espOnly (by exact (rT P).coreArgs))
    fun _ _ _ _ hL hk hc hi => try₂_ok hL hc hi).seq ?_
  refine (two_wp (Ψ := fun L m₀ u => P₃ P L m₀ i u) core_ct fun _ _ _ _ hL hk hc hi =>
    try₃_ok hL hk.1 hc hi.1 hi.2).seq ?_
  refine (two_wp (Ψ := fun L m₀ u => Mid P L m₀ i u) (two_blk [.esp] espOnly ⟨_, by taint_decide⟩)
    fun _ _ _ _ hL hk hc hi => try₄_ok hL hk.1 hc hi).seq ?_
  refine VG.RelCT.ite (fun _ _ ⟨_, _, _, hx, _, _, f₁, f₂⟩ => dec_two hx f₁ f₂) ?_ ?_
  · exact (rekey_piece.ct.seq (two_blk [.esp] espOnly ⟨_, by taint_decide⟩)).mono (fun _ _ h => h.1) fun _ _ h => h
  · exact (two_blk [.esp] espOnly ⟨_, by taint_decide⟩).mono (fun _ _ h => h.1) fun _ _ h => h

/-- One candidate: both runs end, or both go on. -/
theorem tryOne_ct {i : Nat} :
    RelCT isa (Two P fun L m₀ t => LoopInv P L m₀ i t) (cfgOf P).tryOne fun s₁ s₂ =>
      isa.eval .ne s₁ = isa.eval .ne s₂ ∧ (isa.eval .ne s₁ = some false → Two P (Exit P · · i) s₁ s₂) ∧
        (isa.eval .ne s₁ = some true → Two P (LoopInv P · · (i + 1)) s₁ s₂) := by
  refine (two_wp (Ψ := After P i) tryOne_trace fun _ _ _ _ hL hk hc hi => tryOne_ok hL hk.1 hk.2 hc hi).mono
    (fun _ _ h => h) fun s₁ s₂ ⟨e, hL, hk, hx, c₁, c₂, f₁, f₂⟩ => ?_
  -- A run that goes on has a later candidate to stop at, so the other cannot have stopped.
  have mixed : ∀ (m m' : Mem) (u u' : State), exitAt P e.1 m = exitAt P e.1 m' → Exit P e.1 m i u →
      LoopInv P e.1 m' (i + 1) u' → False := fun _ m' _ _ hx' hE hI => by
    have hgo : sigI P e.1 m' i = none ∧ i + 1 < P.I.tries := ⟨hI.fails i (by omega_using []), hI.lt⟩
    rw [go_iff (by omega) (fun j hj => hI.fails j (by omega_using [hj])), ← hx', ← go_iff hE.lt hE.fails] at hgo
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
  ⟨by omega_using [h], by omega_using [h]⟩

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

/-- The count's initial store, whatever the count. -/
theorem initCnt_taint (c : Cfg) : TaintOk [.esp] c.initCnt := by
  refine ⟨.block [] 256, ?_⟩
  have e : Code.erase (.block c.initCnt) =
      Code.erase (.block [.mov .eax (.imm (BitVec.ofNat 32 0)), .store (stk fCnt) .eax]) := rfl
  have h := Taint.check_erase (.block c.initCnt) (τr [.esp]) (.block [] 256) rfl rfl
  rw [e] at h
  have h0 : (taint.check (τr [.esp]) (Code.erase (.block [.mov .eax (.imm (BitVec.ofNat 32 0)),
      .store (stk fCnt) .eax])) (.block [] 256)).isSome = true := by decide +kernel
  exact (congrArg Option.isSome h).symm.trans h0

/-- If `big`: `X` cleared and the digest copied to `fXc`, keeping `Ctx`. -/
theorem xcCopy_ok {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem} (hL : L.Ok) (hT : TabL P L)
    (hW : P.R.big = true) (hdn : P.F.H.D ≤ dn) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.seq (.block (cfgOf P).xcArgs) Cfg.cpLoop) t (Ctx L g m₀) := by
  have hnb := hL.nB
  obtain ⟨-, -, hQ66, hQD⟩ := P.sizesW hW
  obtain ⟨-, -, -, -, hD16, hD64, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := P.sizes
  refine WP.seq (WP.mono (xcArgs_ok hL hT hW hc) fun u₁ ⟨hc₁, _, _, hcx₁, hbx₁, hsi₁⟩ => ?_)
  have ea : (L.F + BitVec.ofNat 32 (fXc + (P.Q - 1 - P.F.H.D))).setWidth 64 =
      L.B + BitVec.ofNat 64 (76 + fXc + (P.Q - 1 - P.F.H.D)) := by
    rw [hL.frv (by simp only [fXc]; omega_using [hQ66]), Nat.add_assoc]
  have sepD : Region.Disjoint ⟨L.a2.setWidth 64, P.F.H.D⟩
      ⟨L.B + BitVec.ofNat 64 (76 + fXc + (P.Q - 1 - P.F.H.D)), P.F.H.D⟩ :=
    ((hL.kg.sub_left (Offset.sub_base _ (by simp only [fXc]; omega_using [hQ66, hQD]))).symm.sub_left (Region.sub_prefix hdn))
  exact WP.mono (cpLoop_ok hL hc₁ (S := L.a2) (D := L.F + BitVec.ofNat 32 (fXc + (P.Q - 1 - P.F.H.D)))
      (n := P.F.H.D) (by omega_using [hD16]) (by omega_using [hD64]) (by have := hL.ng; omega_using [hdn, this])
      (by rw [hL.frN (by simp only [fXc]; omega_using [hQ66])]; have := hL.e28; have := hL.e588; simp only [fXc]; omega_using [hQ66, hQD])
      (by have := hc₁.inDg (o := 0) (n := P.F.H.D) (by omega_using [hdn]) (by omega_using []); rwa [BitVec.add_zero] at this)
      (by rw [ea]; exact hc₁.inFrW (by omega_using []) (by simp only [fXc]; omega_using [hQ66, hQD]) hL)
      (by rw [ea]; exact sepD)
      (by rw [ea]; exact safe_high L (by simp only [fXc]; omega_using []) (by simp only [fXc]; omega_using [hQ66, hQD]))
      hsi₁ hbx₁ hcx₁) fun _ h => h.1

theorem prepX_ct : RelCT isa (Two P (Tt P)) (cfgOf P).prepX (Two P (QX P)) := by
  refine two_wp ?_ fun L g m₀ t hL hk hc _ => stageX_ok hL hk.2 hc
  rw [Cfg.prepX]
  exact (two_wp (Ψ := CpA P (fun L => L.F + BitVec.ofNat 32 (fX + (P.Q - min P.F.H.D P.Q))) (fun L => L.a2)
      (min P.F.H.D P.Q)) (two_blk [.esp] espOnly (by exact (rT P).xArgs)) fun L g m₀ t hL hk hc _ =>
    WP.mono (xArgs_ok hL hk.2 hc) fun _ ⟨c, _, _, cx, bx, si⟩ => ⟨c, si, bx, cx⟩).seq
    (cp_ct fun _ _ _ h => h)

theorem prepH_ct : RelCT isa (Two P (QX P)) (cfgOf P).prepH (Two P (QA P)) := by
  refine two_wp ?_ fun L g m₀ t hL hk hc hx => stageH_ok hL hk.2 hc hx
  cases hb : P.R.big
  · rw [show (cfgOf P).prepH = .block (cfgOf P).reduce by
      simp only [Cfg.prepH, show (cfgOf P).big = false from hb, Bool.false_eq_true, ite_false]]
    exact two_blk [.esp] espOnly (by exact (rT P).reduce hb)
  · rw [show (cfgOf P).prepH = (cfgOf P).prepC by
      simp only [Cfg.prepH, show (cfgOf P).big = true from hb, ite_true], Cfg.prepC]
    refine RelCT.assoc ((two_wp (Ψ := Tt P) ((two_wp (Ψ := CpA P
        (fun L => L.F + BitVec.ofNat 32 (fXc + (P.Q - 1 - P.F.H.D))) (fun L => L.a2) P.F.H.D)
        (two_blk [.esp] espOnly (by exact (rT P).xcArgs hb)) fun L g m₀ t hL hk hc _ =>
          WP.mono (xcArgs_ok hL hk.2 hb hc) fun _ ⟨c, _, _, cx, bx, si⟩ => ⟨c, si, bx, cx⟩).seq
        (cp_ct fun _ _ _ h => h)) fun L g m₀ t hL hk hc _ =>
          WP.mono (xcCopy_ok hL hk.2 hb (Nat.le_of_eq P.len.symm) hc) fun _ h => ⟨h, trivial⟩).seq ?_)
    exact scrPtr_ct.seq (two_blk [.esp, .edi] scrRegs (by exact (rT P).convC hb))

theorem rest_ct :
    RelCT isa (Two P (Tt P)) (rest P) (Two P fun L m₀ t => (∃ i, Exit P L m₀ i t)) := by
  refine prepX_ct.seq (prepH_ct.seq ?_)
  refine (two_wp (Ψ := QB P) (two_blk [.esp] espOnly ⟨_, by taint_decide⟩)
    fun _ _ _ _ hL _ hc h => stageB_ok hL hc h).seq ?_
  refine (two_wp (Ψ := QC P) ((rekeyFull_piece 0 (by decide)).rel fun _ _ _ _ => trivial)
    fun _ _ _ _ hL hk hc h => stageC_ok (P := P) hL hk.1 hk.2 hc h).seq ?_
  refine (two_wp (Ψ := QD P) ((rekeyFull_piece 1 (by decide)).rel fun _ _ _ _ => trivial)
    fun _ _ _ _ hL hk hc h => stageD_ok (P := P) hL hk.1 hk.2 hc h).seq ?_
  refine (two_wp (Ψ := fun L m₀ t => LoopInv P L m₀ 0 t) (two_blk [.esp] espOnly (initCnt_taint _))
    fun _ _ _ _ hL _ hc h => stageE_ok (P := P) hL hc h).seq ?_
  refine tries_ct.seq ?_
  exact two_wp (two_blk [.esp] espOnly ⟨_, by taint_decide⟩) fun _ _ _ _ hL hk hc ⟨i, h⟩ =>
    WP.mono (stageG_ok hL hk.1 hc h) fun _ ⟨c, x, _⟩ => ⟨c, i, x⟩

/-! ## The frame's entry -/

theorem entry_taint : TaintOk [.esp] Cfg.entry := ⟨_, by taint_decide⟩

theorem tabDB_taint : TaintOk [.esp, .eax] Cfg.tabDB := ⟨_, by taint_decide⟩

/-- The layouts of two calls whose public data agree. -/
theorem layOf_eq {ns : List String} (hns : ∀ n ∈ [P.F.hiN, P.F.H.updN, P.F.hfN], n ∈ ns) {s₁ s₂ : State}
    (hpub : (rfcP P ns).pub s₁ s₂) : layOf P s₂ = layOf P s₁ := by
  obtain ⟨hsp, ha, -, hsy, hns'⟩ := hpub
  have hs : (fun n => if n ∈ P.R.E.combConsts.map Prod.fst then s₂.syms n else 0) =
      fun n => if n ∈ P.R.E.combConsts.map Prod.fst then s₁.syms n else 0 := funext fun n => by
    split
    · next h => obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h; exact (hsy c hc).symm
    · rfl
  have hfa : (fun n => if n ∈ [P.F.hiN, P.F.H.updN, P.F.hfN] then s₂.syms n else 0) =
      fun n => if n ∈ [P.F.hiN, P.F.H.updN, P.F.hfN] then s₁.syms n else 0 := funext fun n => by
    split
    · next h => exact (hns' n (hns n h)).symm
    · rfl
  simp only [layOf, lay, hsp, ← ha 0 (by decide), ← ha 1 (by decide), ← ha 2 (by decide), ← ha 3 (by decide),
    ← ha 4 (by decide), ← ha 5 (by decide), hs, hfa]

/-- Our caller's registers saved, and the table's `D` and `B` in the frame:
the runs are related by `Two`, with the layout of the arguments, which agree,
and the same number of candidates. -/
theorem start_at {ns : List String} (hns : ∀ n ∈ [P.F.hiN, P.F.H.updN, P.F.hfN], n ∈ ns) {s₁ s₂ : State}
    (p₁ : (rfcP P ns).pre s₁) (p₂ : (rfcP P ns).pre s₂) (hpub : (rfcP P ns).pub s₁ s₂) :
    RelCT isa (fun a b => a = allocState 512 s₁ ∧ b = allocState 512 s₂)
      (.seq (.block Cfg.entry) (.block Cfg.tabDB)) (Two P (Tt P)) := by
  have hl := layOf_eq hns hpub
  have hF : (layOf P s₂).F = (layOf P s₁).F := by rw [hl]
  obtain ⟨_, het⟩ := entry_taint
  obtain ⟨_, htt⟩ := tabDB_taint
  refine ((VG.RelCT.taint (A := taint) (τr [.esp]) (fun _ _ ⟨ea, eb⟩ => agree_regs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr ea eb
      rw [allocState_esp, allocState_esp, hpub.1]) het).wp
    (F₁ := fun t : State => t.gpr .eax = arg s₁ 5 ∧ t.gpr .esp = (layOf P s₁).F ∧
      WP isa (.block Cfg.tabDB) t (Ctx (layOf P s₁) s₁.gpr s₁.mem))
    (F₂ := fun t : State => t.gpr .eax = arg s₂ 5 ∧ t.gpr .esp = (layOf P s₂).F ∧
      WP isa (.block Cfg.tabDB) t (Ctx (layOf P s₂) s₂.gpr s₂.mem))
    fun _ _ ⟨ea, eb⟩ => by subst ea eb; exact ⟨entry_ok p₁, entry_ok p₂⟩).seq ?_
  refine ((VG.RelCT.taint (A := taint) (τr [.esp, .eax]) (fun _ _ ⟨_, ⟨ax₁, sp₁, _⟩, ⟨ax₂, sp₂, _⟩⟩ =>
      agree_regs fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [sp₁, sp₂, hF]
        · rw [ax₁, ax₂, hpub.2.1 5 (by decide)]) htt).wp
    (F₁ := Ctx (layOf P s₁) s₁.gpr s₁.mem) (F₂ := Ctx (layOf P s₂) s₂.gpr s₂.mem)
    fun _ _ ⟨_, ⟨_, _, w₁⟩, ⟨_, _, w₂⟩⟩ => ⟨w₁, w₂⟩).mono (fun _ _ h => h) fun a b ⟨_, c₁, c₂⟩ => ?_
  have hr : (result P.I s₁.mem (layOf P s₁).d (layOf P s₁).dg).2 =
      (result P.I s₂.mem (layOf P s₁).d (layOf P s₁).dg).2 := by
    show (result P.I s₁.mem ((arg s₁ 1).setWidth 64) ((arg s₁ 2).setWidth 64)).2 =
      (result P.I s₂.mem ((arg s₁ 1).setWidth 64) ((arg s₁ 2).setWidth 64)).2
    rw [hpub.2.2.1, hpub.2.1 1 (by decide), hpub.2.1 2 (by decide)]
  refine ⟨⟨layOf P s₁, s₁.gpr, s₂.gpr, s₁.mem, s₂.mem⟩, lay_ok p₁, ⟨coreOk_lay P s₁, tabL_lay P s₁⟩,
    congrArg (fun x => if x = 0 then P.I.tries - 1 else x - 1) hr, c₁, hl ▸ c₂, trivial, trivial⟩

/-! ## The whole function -/

/-- `vg_ecdsa_<curve>_sign`, for `P`'s hash function, is constant time:
runs whose public data agree (with the addresses of the hash function's
HMAC functions among `ns`) have the same layout, and stop at the same
candidate. -/
theorem sign_ct {ns : List String} (hns : ∀ n ∈ [P.F.hiN, P.F.H.updN, P.F.hfN], n ∈ ns) :
    ConstantTime isa (rfcP P ns).pre (rfcP P ns).pub (cfgOf P).sign := by
  rw [show (cfgOf P).sign = .frame (.alloc 512) (cfgOf P).body (.free 512) from rfl]
  refine VG.RelCT.constantTime (Q := fun _ _ => True)
    (alloc_ct (R := Two P fun L m₀ t => ∃ i, Exit P L m₀ i t) ?_)
  rw [body_eq]
  refine RelCT.assoc ?_
  exact (VG.RelCT.exists_ fun q : State × State => VG.RelCT.exists_ fun h : (rfcP P ns).pre q.1 ∧
      (rfcP P ns).pre q.2 ∧ (rfcP P ns).pub q.1 q.2 => (start_at hns h.1 h.2.1 h.2.2).seq rest_ct).mono
    (fun _ _ ⟨s₁, s₂, h, ea, eb⟩ => ⟨(s₁, s₂), h, ea, eb⟩) fun _ _ h => h

end VG.Proof.Ecdsa.Rfc6979.X86

end

end

/-!
# Deterministic ECDSA on x86 (32-bit): the HMAC of a table

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Table.lean`): `vg_ecdsa_<curve>_sign`
(`signCodeT`) is the one body (`cfgT`, the same for every hash function),
which loads `D` and `B`, the digest length and HMAC's block size, from the
table `hmac` (its words 4 and 5) and calls the table's functions. For the
variants `vs` of the hash functions that pass the registration's checks
(`OK`: their functions of the same name have the same code, and each is of
one of the hash functions with HMAC, of sizes the frame holds), the table of
each variant `w` makes the body the code for `w`'s hash function (`hashOf`,
with `cfgT_eq`, which holds by `rfl`), which meets the contract with that
hash function fixed (`sign_ok`, `sign_ct`). `tabK` states that contract for
whichever of the tables `hmac` holds; `TableSpec.lean` shows
`TableInstance.signContract` implies it.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.Impl.Ecdsa.Rfc6979.X86
open VG.Proof.HmacTable.X86 (HVar tables fnsOf names Coh tableOf mem_names tabOK_of held_tableOf hashAt_tableOf)

/-! ## The code -/

/-- The body, on the curve `R`, with the bound on candidates `tries` and the
tables of `vs`: the same for every hash function. -/
def cfgT (R : RfcCurve) (tries : Nat) (vs : List HVar) : Cfg where
  f := fnsOf vs
  w := 2 * R.E.n - (if R.E.C.len = 28 then 1 else 0)
  len := R.E.C.len
  big := R.big
  sh := R.sh
  n := R.E.C.n
  tries := tries
  coreN := R.coreN
  coreC := R.coreC

/-- `vg_ecdsa_<curve>_sign`. -/
def signCodeT (R : RfcCurve) (tries : Nat) (vs : List HVar) : Prog isa := signCode (cfgT R tries vs)

/-- The stack it uses. -/
def stackT : Nat := 588

/-! ## The variants -/

/-- What the code needs of a variant `w`: its hash function has HMAC (over
`w`'s block size), of one of the digest lengths and block sizes the frame
holds, and the states and working space of `w`'s HMAC fit the frame and
`scratch`. -/
def WOk (w : HVar) : Prop :=
  (match Spec.HmacTable.hmacOf w.G with
    | some F => F.blockSize = w.F.H.B
    | none => False) ∧
  (w.F.H.D, w.F.H.B) ∈ shapes ∧ w.F.H.S ≤ 192 ∧ w.ok.Wi * 8 ≤ 1872 ∧ w.ok.Wf * 8 ≤ 1872 ∧ w.ok.hH.Wb ≤ 1872

instance (w : HVar) : Decidable (WOk w) := by
  unfold WOk; cases Spec.HmacTable.hmacOf w.G <;> infer_instance

/-- What the registrations check of the variants whose tables the function
takes. -/
def OK (vs : List HVar) : Prop := Coh vs ∧ (names vs).length < 2 ^ 24 ∧ vs ≠ [] ∧ ∀ w ∈ vs, WOk w

instance (vs : List HVar) : Decidable (OK vs) := by unfold OK; infer_instance

theorem hvar_mem (w : HVar) : w.G ∈ Spec.Mgf1.hashes := List.mem_of_getElem? w.idx

/-- The HMAC of `w`'s hash function. -/
theorem WOk.hmac {w : HVar} (hw : WOk w) : Spec.HmacTable.hmacOf w.G = some w.ok.hH.SH.H := by
  have h := hw.1
  revert h
  cases hF : Spec.HmacTable.hmacOf w.G with
  | none => intro h; exact h.elim
  | some F =>
    intro hb
    have hh := Spec.HmacTable.hmacOf_hash _ (hvar_mem w) F hF
    congr 1
    cases F
    rw [Spec.Hmac.HashFunction.mk.injEq]
    exact ⟨hb.trans w.ok.hH.hB.symm, funext fun x => (congrFun hh x).trans (w.hash x)⟩

/-- HMAC's block size, as the table holds it. -/
theorem WOk.blockSize {w : HVar} (hw : WOk w) : Spec.HmacTable.blockSize w.G = w.F.H.B := by
  simp only [Spec.HmacTable.blockSize, hw.hmac, Option.map_some, Option.getD_some]
  exact w.ok.hH.hB

/-- The instance with `w`'s hash function fixed. -/
def instOf (T : Spec.Ecdsa.Rfc6979.TableInstance) (w : HVar) : Proof.Ecdsa.Rfc6979.Instance where
  ecdsa := T.ecdsa
  hash := w.ok.hH.SH.H
  hashLen := w.F.H.D
  tries := T.tries

/-- What each curve's file shows of its curve and instance. -/
structure CurveT (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) : Prop where
  ecdsa : T.ecdsa = R.inst
  tries_pos : 0 < T.tries
  tries_lt : T.tries < 2 ^ 32

/-- The proof's hash function: `w`, the functions an indirect call of the
table's reaches those of `vs`. -/
def hashOf {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} (hC : CurveT R T) (vs : List HVar)
    (w : HVar) (hw : WOk w) : RfcHash where
  R := R
  I := instOf T w
  F := w.F
  ok := w.ok
  f := fnsOf vs
  ecdsa := hC.ecdsa
  hash := rfl
  len := rfl
  macLen := w.hlen
  tries_pos := hC.tries_pos
  tries_lt := hC.tries_lt
  hDB := hw.2.1
  hS := hw.2.2.1
  hWi := hw.2.2.2.1
  hWf := hw.2.2.2.2.1
  hWb := hw.2.2.2.2.2

/-- The body for `w`'s hash function is the same as for every other. -/
theorem cfgT_eq {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} (hC : CurveT R T) (vs : List HVar)
    {w : HVar} (hw : WOk w) : cfgT R T.tries vs = cfgOf (hashOf hC vs w hw) := rfl

/-- RFC 6979's result with `w`'s hash function fixed is the table's. -/
theorem tresult_eq (T : Spec.Ecdsa.Rfc6979.TableInstance) (w : HVar) (m : Mem) (d dg : Addr) :
    (instOf T w).result m d dg = T.result w.G w.ok.hH.SH.H m d dg := by
  simp only [Proof.Ecdsa.Rfc6979.Instance.result, Spec.Ecdsa.Rfc6979.TableInstance.result, instOf, w.glen]

/-! ## The contract -/

/-- What the contract with the table of `w` says: the contract the proof is
written against, and the table's index. -/
def PreW (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List HVar) (w : HVar) (s : State) :
    Prop :=
  (rfcX86 R.E.combConsts (instOf T w) stackT (tabFacts w.F (fnsOf vs)) (names vs)).pre s ∧
    s.mem.readW (addr (arg s 5) 12) 32 = BitVec.ofNat 32 (Spec.HashTable.index w.G)

open Spec.Weierstrass Spec.Ecdsa in
/-- The contract with whichever of the tables of `vs` the table `hmac` is. -/
def tabK (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List HVar) : Contract isa where
  pre s := ∃ w ∈ vs, WOk w ∧ PreW R T vs w s
  post s s' := ∀ w ∈ vs, WOk w → PreW R T vs w s →
    match (T.result w.G w.ok.hH.SH.H s.mem ((arg s 1).setWidth 64) ((arg s 2).setWidth 64)).1 with
    | some rs => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 1 ∧
        bytesAt s'.mem ((arg s 0).setWidth 64) (2 * T.ecdsa.curve.len) = encode T.ecdsa.curve rs
    | none => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 0 ∧
        bytesAt s'.mem ((arg s 0).setWidth 64) (2 * T.ecdsa.curve.len) = List.replicate (2 * T.ecdsa.curve.len) 0
  pub s₁ s₂ := ∃ w ∈ vs, WOk w ∧ PreW R T vs w s₁ ∧ PreW R T vs w s₂ ∧
    (rfcX86 R.E.combConsts (instOf T w) stackT (tabFacts w.F (fnsOf vs)) (names vs)).pub s₁ s₂

variable {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List HVar}

theorem index_lt (w : HVar) : Spec.HashTable.index w.G < Spec.Mgf1.hashes.length :=
  (List.getElem?_eq_some_iff.mp w.idx).1

/-- Two variants whose tables have the same index have the same hash function. -/
theorem same_hash {w w' : HVar} (hw : WOk w) (hw' : WOk w')
    (h : BitVec.ofNat 32 (Spec.HashTable.index w'.G) = BitVec.ofNat 32 (Spec.HashTable.index w.G)) :
    w'.G = w.G ∧ w'.ok.hH.SH.H = w.ok.hH.SH.H := by
  have e : Spec.HashTable.index w'.G = Spec.HashTable.index w.G := by
    have h₁ := index_lt w; have h₂ := index_lt w'
    have h8 : Spec.Mgf1.hashes.length < 2 ^ 32 := by decide
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h₂, h8]), Nat.mod_eq_of_lt (by omega_using [h₁, h8])] at this
    exact this
  have hG : w'.G = w.G := Option.some.inj (w'.idx.symm.trans (e ▸ w.idx))
  refine ⟨hG, ?_⟩
  have h₁ := hw.hmac; have h₂ := hw'.hmac
  rw [hG] at h₂
  exact Option.some.inj (h₂.symm.trans h₁)

/-! ## No instruction writes `esp` but the frame's -/

theorem okP_of_noSp {c : Prog isa} (h : NoSp c) : OkP c := by
  rw [OkP, Code.allInstrs_eq, List.all_eq_true]
  intro i hi; simp [h i hi]

theorem fnsOk_of (vs : List HVar) : FnsOk (fnsOf vs).init ∧ FnsOk (fnsOf vs).upd ∧ FnsOk (fnsOf vs).fin := by
  refine ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩ <;> obtain ⟨w, -, rfl⟩ := List.mem_map.mp hq
  · exact okP_of_noSp w.ok.hiSp
  · exact okP_of_noSp w.ok.hH.updSp
  · exact okP_of_noSp w.ok.hfSp

theorem body_okP_cfgT (R : RfcCurve) (tries : Nat) (vs : List HVar) : OkP (cfgT R tries vs).body :=
  body_okP (c := cfgT R tries vs) R.blk (fnsOk_of vs) (okP_of_noSp R.coreNs)

theorem body_noSp (R : RfcCurve) (tries : Nat) (vs : List HVar) : NoSp (cfgT R tries vs).body :=
  NoSp.of_all (body_okP_cfgT R tries vs)

/-- `esp` is written only by the frame's allocation and release. -/
theorem signCode_sp (R : RfcCurve) (tries : Nat) (vs : List HVar) :
    (signCodeT R tries vs).all (fun i => !isa.writesSp i) = true := by
  refine Code.all_of_allInstrs ?_
  have h := body_okP_cfgT R tries vs
  simp only [OkP, Proof.Pbkdf2.Whole.X86.clobbers_esp] at h
  simp only [signCodeT, signCode, Cfg.sign, Code.allInstrs, h]
  rfl

/-! ## Correct and constant time -/

/-- `vg_ecdsa_<curve>_sign` meets `tabK`, and keeps the callee-saved
registers and its return address. -/
theorem signT_ok (hC : CurveT R T) {s : State} (h : (tabK R T vs).pre s) :
    WP isa (signCodeT R T.tries vs) s fun s' => abiPreserved s s' ∧ (tabK R T vs).post s s' := by
  obtain ⟨w, -, hw, hp⟩ := h
  unfold signCodeT signCode
  rw [cfgT_eq hC vs hw]
  refine WP.mono (sign_ok (P := hashOf hC vs w hw) (body_noSp R T.tries vs) hp.1) fun s' ⟨hg, hpost⟩ =>
    ⟨hg, fun w' _ hw' hp' => ?_⟩
  obtain ⟨hG, hH⟩ := same_hash hw hw' (hp'.2.symm.trans hp.2)
  rw [hG, hH]
  have hpost' : match ((instOf T w).result s.mem ((arg s 1).setWidth 64) ((arg s 2).setWidth 64)).1 with
    | some rs => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 1 ∧ Spec.Ecdsa.bytesAt s'.mem
        ((arg s 0).setWidth 64) (2 * T.ecdsa.curve.len) = Spec.Ecdsa.encode T.ecdsa.curve rs
    | none => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 0 ∧ Spec.Ecdsa.bytesAt s'.mem
        ((arg s 0).setWidth 64) (2 * T.ecdsa.curve.len) = List.replicate (2 * T.ecdsa.curve.len) 0 := hpost
  rw [tresult_eq] at hpost'
  exact hpost'

/-- `vg_ecdsa_<curve>_sign` is constant time: runs whose public data agree
take the same table, whose hash function's code is the body, constant time
for it. -/
theorem signT_ct (hC : CurveT R T) :
    ConstantTime isa (tabK R T vs).pre (tabK R T vs).pub (signCodeT R T.tries vs) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ _ ⟨w, hv, hw, p₁, p₂, hpub⟩ e₁ e₂
  unfold signCodeT signCode at e₁ e₂
  rw [cfgT_eq hC vs hw] at e₁ e₂
  have hns : ∀ n ∈ [(hashOf hC vs w hw).F.hiN, (hashOf hC vs w hw).F.H.updN, (hashOf hC vs w hw).F.hfN],
      n ∈ names vs := by
    have := mem_names hv
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl
    · exact this.1
    · exact this.2.1
    · exact this.2.2
  exact sign_ct (P := hashOf hC vs w hw) hns s₁ s₂ t₁ t₂ s₁' s₂' p₁.1 p₂.1 hpub e₁ e₂

end VG.Proof.Ecdsa.Rfc6979.X86

end

end

/-!
# Deterministic ECDSA on x86 (32-bit): the contract with the hash function as a table

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/TableSat.lean`):
`TableInstance.signContract`, with the tables of `vs` for `hmac`, the
curve's tables of constants and `stackT` bytes of stack, implies `tabK`
(`tab_implies`): the table `hmac` points to is one of `vs`', whose words
give the contract the proof is written against (`preW_of`); its hash
function is the one the table names, so the results agree; and two runs
whose public data agree take the same table.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.Impl.Ecdsa.Rfc6979.X86
open VG.Proof.HmacTable.X86 (HVar tables fnsOf names Coh tableOf mem_names tabOK_of held_tableOf hashAt_tableOf)

variable {R : RfcCurve} {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List HVar}

/-- The table `hmac` points to holds `w`'s. -/
abbrev HeldW (w : HVar) (s : State) : Prop :=
  Abi.tableHeld 32 s.mem ((arg s 5).setWidth 64) (FnTable.words isa s (tableOf w))

theorem tableRegion_eq (p : Addr) : Sig.tableRegion 32 p 6 = ⟨p, 24⟩ := rfl

theorem names_eq (vs : List HVar) : (List.map (fun x => x.fns) (tables vs)).flatten = names vs := rfl

/-- The facts of the contract with the table of `w`. -/
theorem preW_of {w : HVar} (hv : w ∈ vs) (hc : Coh vs) (hw : WOk w) {s : State}
    (e588 : 588 ≤ (s.gpr .esp).toNat) (e28 : (s.gpr .esp).toNat + 28 ≤ 2 ^ 32)
    (hrd : s.rd = [⟨(arg s 1).setWidth 64, T.ecdsa.curve.len⟩, ⟨(arg s 2).setWidth 64, w.F.H.D⟩,
      ⟨(arg s 5).setWidth 64, 24⟩] ++ Abi.constRegions (fun n => (s.syms n).setWidth 64) R.E.combConsts)
    (hwr : s.wr = [⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩, ⟨(arg s 4).setWidth 64, 8192⟩,
      ⟨argAddr s 0, 24⟩])
    (od : Region.Disjoint ⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩ ⟨(arg s 1).setWidth 64, T.ecdsa.curve.len⟩)
    (og : Region.Disjoint ⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩ ⟨(arg s 2).setWidth 64, w.F.H.D⟩)
    (oc : Region.Disjoint ⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩ ⟨(arg s 4).setWidth 64, 8192⟩)
    (ot : Region.Disjoint ⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩ ⟨(arg s 5).setWidth 64, 24⟩)
    (dc : Region.Disjoint ⟨(arg s 1).setWidth 64, T.ecdsa.curve.len⟩ ⟨(arg s 4).setWidth 64, 8192⟩)
    (gc : Region.Disjoint ⟨(arg s 2).setWidth 64, w.F.H.D⟩ ⟨(arg s 4).setWidth 64, 8192⟩)
    (ct : Region.Disjoint ⟨(arg s 4).setWidth 64, 8192⟩ ⟨(arg s 5).setWidth 64, 24⟩)
    (oa : Region.Disjoint ⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩ ⟨argAddr s 0, 24⟩)
    (ca : Region.Disjoint ⟨(arg s 4).setWidth 64, 8192⟩ ⟨argAddr s 0, 24⟩)
    (ta : Region.Disjoint ⟨(arg s 5).setWidth 64, 24⟩ ⟨argAddr s 0, 24⟩)
    (ro : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩)
    (rc : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 4).setWidth 64, 8192⟩)
    (rt : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 5).setWidth 64, 24⟩)
    (ko : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 588, 588⟩
      ⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩)
    (kd : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 588, 588⟩
      ⟨(arg s 1).setWidth 64, T.ecdsa.curve.len⟩)
    (kg : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 588, 588⟩ ⟨(arg s 2).setWidth 64, w.F.H.D⟩)
    (kc : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 588, 588⟩ ⟨(arg s 4).setWidth 64, 8192⟩)
    (kt : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 588, 588⟩ ⟨(arg s 5).setWidth 64, 24⟩)
    (no : (arg s 0).toNat + 2 * T.ecdsa.curve.len ≤ 2 ^ 32) (nd : (arg s 1).toNat + T.ecdsa.curve.len ≤ 2 ^ 32)
    (ng : (arg s 2).toNat + w.F.H.D ≤ 2 ^ 32) (nc : (arg s 4).toNat + 8192 ≤ 2 ^ 32)
    (nt : (arg s 5).toNat + 24 ≤ 2 ^ 32)
    (ht : TblsOk R.E.combConsts s [⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩, ⟨(arg s 4).setWidth 64, 8192⟩,
      ⟨(s.gpr .esp).setWidth 64, 4⟩, ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 588, 588⟩])
    (hheld : HeldW w s)
    (hpw : (names vs).Pairwise fun f g => f ≠ g → (s.syms f).setWidth 64 ≠ (s.syms g).setWidth 64) :
    PreW R T vs w s := by
  have hh := held_tableOf nt hheld
  rw [hw.blockSize] at hh
  exact ⟨⟨e588, e28, hrd, hwr, od, og, oc, dc, gc, oa.symm, ca.symm, ro, rc, ko, kd, kg, kc, no, nd, ng, nc, ht,
    nt, ot.symm, ct.symm, ta, rt.symm, kt.symm, tabOK_of hc hpw hv, hh.1, hh.2.2.1, hh.2.2.2⟩, hh.2.1⟩

/-- The contract on the arguments, with the tables of `vs`. -/
abbrev specK (T : Spec.Ecdsa.Rfc6979.TableInstance) (cs : List (String × List (BitVec 64))) (vs : List HVar) :
    Contract isa :=
  T.signContract ((X86.abi.withConsts cs).withTables T.signSig [("hmac", tables vs)]) stackT

/-- What the precondition says: the table is of one of `vs`, and with any
of them it holds, the contract the proof is written against. -/
def PreFacts (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List HVar) (s : State) : Prop :=
  (∃ w ∈ vs, HeldW w s) ∧ ∀ w ∈ vs, HeldW w s → PreW R T vs w s

/-- Unfolds the contract's precondition at `h`. -/
macro "spec_pre" " at " h:ident : tactic => `(tactic| (
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    X86.abi, Abi.withConsts, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil, argSlots, argVal, argBytes, ↓reduceIte, Option.map_some, tableRegion_eq, names_eq] at $h:ident))

/-- Unfolds the contract's precondition in the goal. -/
macro "spec_pre_goal" : tactic => `(tactic| (
  sig_pre [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    X86.abi, Abi.withConsts, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil, argSlots, argVal, argBytes, ↓reduceIte, Option.map_some, tableRegion_eq, names_eq]))

/-- The facts the precondition gives, whichever the tables of constants. -/
theorem facts_of (hsw : T.scratchWords = 1024) (hO : OK vs) {s : State} {w : HVar} (hv : w ∈ vs)
    (hheld : HeldW w s) (e588 : 588 ≤ (s.gpr .esp).toNat) (e28 : (s.gpr .esp).toNat + 4 + 24 ≤ 2 ^ 32)
    (held : Abi.constsHeld s.mem (fun n => (s.syms n).setWidth 64) R.E.combConsts)
    (hfit : ∀ t ∈ Abi.constRegions (fun n => (s.syms n).setWidth 64) R.E.combConsts,
      t.base.toNat + t.len ≤ 2 ^ 32 ∧ (∀ r ∈ s.wr, t.Disjoint r) ∧ t.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ∧
        t.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 588, 588⟩)
    (hpw : (names vs).Pairwise fun f g => f ≠ g → (s.syms f).setWidth 64 ≠ (s.syms g).setWidth 64)
    (hrd : s.rd = [⟨(arg s 1).setWidth 64, T.ecdsa.curve.len⟩, ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩,
      ⟨(arg s 5).setWidth 64, 24⟩] ++ Abi.constRegions (fun n => (s.syms n).setWidth 64) R.E.combConsts)
    (hwr : s.wr = [⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩, ⟨(arg s 4).setWidth 64, T.scratchWords * 8⟩,
      ⟨argAddr s 0, 24⟩])
    (od : Region.Disjoint ⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩ ⟨(arg s 1).setWidth 64, T.ecdsa.curve.len⟩)
    (og : Region.Disjoint ⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩ ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩)
    (oc : Region.Disjoint ⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩
      ⟨(arg s 4).setWidth 64, T.scratchWords * 8⟩)
    (ot : Region.Disjoint ⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩ ⟨(arg s 5).setWidth 64, 24⟩)
    (oa : Region.Disjoint ⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩ ⟨argAddr s 0, 24⟩)
    (dc : Region.Disjoint ⟨(arg s 1).setWidth 64, T.ecdsa.curve.len⟩ ⟨(arg s 4).setWidth 64, T.scratchWords * 8⟩)
    (gc : Region.Disjoint ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩ ⟨(arg s 4).setWidth 64, T.scratchWords * 8⟩)
    (ct : Region.Disjoint ⟨(arg s 4).setWidth 64, T.scratchWords * 8⟩ ⟨(arg s 5).setWidth 64, 24⟩)
    (ca : Region.Disjoint ⟨(arg s 4).setWidth 64, T.scratchWords * 8⟩ ⟨argAddr s 0, 24⟩)
    (ta : Region.Disjoint ⟨(arg s 5).setWidth 64, 24⟩ ⟨argAddr s 0, 24⟩)
    (ro : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩)
    (rc : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 4).setWidth 64, T.scratchWords * 8⟩)
    (rt : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 5).setWidth 64, 24⟩)
    (ko : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 588, 588⟩
      ⟨(arg s 0).setWidth 64, 2 * T.ecdsa.curve.len⟩)
    (kd : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 588, 588⟩
      ⟨(arg s 1).setWidth 64, T.ecdsa.curve.len⟩)
    (kg : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 588, 588⟩
      ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩)
    (kc : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 588, 588⟩
      ⟨(arg s 4).setWidth 64, T.scratchWords * 8⟩)
    (kt : Region.Disjoint ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 588, 588⟩ ⟨(arg s 5).setWidth 64, 24⟩)
    (no : (arg s 0).toNat + 2 * T.ecdsa.curve.len ≤ 2 ^ 32) (nd : (arg s 1).toNat + T.ecdsa.curve.len ≤ 2 ^ 32)
    (ng : (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32) (nc : (arg s 4).toNat + T.scratchWords * 8 ≤ 2 ^ 32)
    (nt : (arg s 5).toNat + 24 ≤ 2 ^ 32)
    (hH : ∀ H, Spec.HmacTable.hashAt 32 s.mem ((arg s 5).setWidth 64) = some H →
      (arg s 3).toNat = H.len ∧ (Spec.HmacTable.hmacOf H).isSome = true) :
    PreW R T vs w s := by
  have hh := held_tableOf nt hheld
  have hlen : (arg s 3).toNat = w.F.H.D := (hH _ (hashAt_tableOf nt hh.2.1)).1.trans w.glen
  rw [hlen] at og gc kg ng hrd
  rw [hsw] at hwr oc dc gc rc kc nc ct ca
  refine preW_of hv hO.1 (hO.2.2.2 w hv) e588 (by omega_using [e28]) hrd hwr od og oc ot dc gc ct oa ca ta ro rc rt
    ko kd kg kc kt no nd ng nc nt ⟨held, fun t htm => ⟨(hfit t htm).1, fun r hr => ?_⟩⟩ hheld hpw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hfit t htm).2.1 _ (by rw [hwr]; simp)
  · exact (hfit t htm).2.1 _ (by rw [hwr]; simp)
  · exact (hfit t htm).2.2.1
  · exact (hfit t htm).2.2.2

/-- The precondition, with tables of constants. -/
theorem pre_cons (hsw : T.scratchWords = 1024) (hO : OK vs) {c : String × List (BitVec 64)}
    {cs : List (String × List (BitVec 64))} (hcs : R.E.combConsts = c :: cs) {s : State}
    (h : (specK T (c :: cs) vs).pre s) : PreFacts R T vs s := by
  spec_pre at h
  obtain ⟨e588, e28, hdrop, held, hfit, -, ⟨Tb, hTb, hheld⟩, hpw, htake, hwr, od, og, oc, ot, oa, dc, -, gc, -,
    ct, ca, ta, ro, -, -, rc, rt, -, ko, kd, kg, kc, kt, -, no, nd, ng, nc, nt, hH⟩ := h
  obtain ⟨w₀, hv₀, rfl⟩ := List.mem_map.mp hTb
  refine ⟨⟨w₀, hv₀, hheld⟩, fun w hv hheld => ?_⟩
  rw [List.append_eq, List.append_nil] at hpw
  refine facts_of (R := R) hsw hO hv hheld e588 e28 (by rw [hcs]; exact held) (by rw [hcs]; exact hfit) hpw ?_ hwr
    od og oc ot oa dc gc ct ca ta ro rc rt ko kd kg kc kt no nd ng nc nt hH
  rw [hcs, ← List.take_append_drop (s.rd.length - (cs.length + 1)) s.rd, htake, hdrop]

/-- The precondition, without tables of constants. -/
theorem pre_nil (hsw : T.scratchWords = 1024) (hO : OK vs) (hcs : R.E.combConsts = []) {s : State}
    (h : (specK T [] vs).pre s) : PreFacts R T vs s := by
  spec_pre at h
  obtain ⟨e588, e28, ⟨Tb, hTb, hheld⟩, hpw, hrd, hwr, od, og, oc, ot, oa, dc, -, gc, -,
    ct, ca, ta, ro, -, -, rc, rt, -, ko, kd, kg, kc, kt, -, no, nd, ng, nc, nt, hH⟩ := h
  obtain ⟨w₀, hv₀, rfl⟩ := List.mem_map.mp hTb
  refine ⟨⟨w₀, hv₀, hheld⟩, fun w hv hheld => ?_⟩
  rw [List.append_eq, List.append_nil] at hpw
  refine facts_of (R := R) hsw hO hv hheld e588 e28 (by rw [hcs]; exact fun _ h => absurd h (by simp))
    (by rw [hcs]; exact fun _ h => absurd h (by simp [Abi.constRegions])) hpw (by rw [hcs, hrd]; rfl) hwr
    od og oc ot oa dc gc ct ca ta ro rc rt ko kd kg kc kt no nd ng nc nt hH

theorem PreW.nt {w : HVar} {s : State} (h : PreW R T vs w s) : (arg s 5).toNat + 24 ≤ 2 ^ 32 := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, nt, -⟩, -⟩ := h
  exact nt

/-- The postcondition: the hash function the table names is its variant's. -/
theorem post_of {s s' : State} (hk : (tabK R T vs).pre s) (hp : (tabK R T vs).post s s') :
    ∀ (H : Spec.Mgf1.Hash) (F : Spec.Hmac.HashFunction),
      Spec.HmacTable.hashAt 32 s.mem ((arg s 5).setWidth 64) = some H → Spec.HmacTable.hmacOf H = some F →
        match (T.result H F s.mem ((arg s 1).setWidth 64) ((arg s 2).setWidth 64)).fst with
        | some rs => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 1 ∧
            Spec.Ecdsa.bytesAt s'.mem ((arg s 0).setWidth 64) (2 * T.ecdsa.curve.len) =
              Spec.Ecdsa.encode T.ecdsa.curve rs
        | none => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 0 ∧
            Spec.Ecdsa.bytesAt s'.mem ((arg s 0).setWidth 64) (2 * T.ecdsa.curve.len) =
              List.replicate (2 * T.ecdsa.curve.len) 0 := by
  intro H F hH hF
  obtain ⟨w, hv, hw, hpre⟩ := hk
  obtain rfl := Option.some.inj (hH.symm.trans (hashAt_tableOf hpre.nt hpre.2))
  obtain rfl := Option.some.inj (hF.symm.trans hw.hmac)
  exact hp w hv hw hpre

/-- What the public data say. -/
def PubFacts (R : RfcCurve) (T : Spec.Ecdsa.Rfc6979.TableInstance) (vs : List HVar) (s₁ s₂ : State) : Prop :=
  (∀ w ∈ vs, HeldW w s₁ ↔ HeldW w s₂) ∧ s₁.gpr .esp = s₂.gpr .esp ∧ (∀ i < 6, arg s₁ i = arg s₂ i) ∧
    T.tried 32 s₁.mem ((arg s₁ 1).setWidth 64) ((arg s₁ 2).setWidth 64) ((arg s₁ 5).setWidth 64) =
      T.tried 32 s₂.mem ((arg s₂ 1).setWidth 64) ((arg s₂ 2).setWidth 64) ((arg s₂ 5).setWidth 64) ∧
    (∀ c ∈ R.E.combConsts, s₁.syms c.1 = s₂.syms c.1) ∧ ∀ n ∈ names vs, s₁.syms n = s₂.syms n

theorem tried_eq {w : HVar} (hw : WOk w) {s : State} (hp : PreW R T vs w s) :
    T.tried 32 s.mem ((arg s 1).setWidth 64) ((arg s 2).setWidth 64) ((arg s 5).setWidth 64) =
      ((instOf T w).result s.mem ((arg s 1).setWidth 64) ((arg s 2).setWidth 64)).2 := by
  simp only [Spec.Ecdsa.Rfc6979.TableInstance.tried, hashAt_tableOf hp.nt hp.2, hw.hmac, tresult_eq]

/-- The public data of `tabK`, from the facts. -/
theorem pub_of (hO : OK vs) {s₁ s₂ : State} (h₁ : PreFacts R T vs s₁) (h₂ : PreFacts R T vs s₂)
    (hp : PubFacts R T vs s₁ s₂) : (tabK R T vs).pub s₁ s₂ := by
  obtain ⟨⟨w, hv, hh⟩, f₁⟩ := h₁
  obtain ⟨hh', hsp, ha, ht, hc, hn⟩ := hp
  have p₁ := f₁ w hv hh
  have p₂ := h₂.2 w hv ((hh' w hv).mp hh)
  have hw := hO.2.2.2 w hv
  refine ⟨w, hv, hw, p₁, p₂, hsp, ha, ?_, hc, hn⟩
  show ((instOf T w).result s₁.mem ((arg s₁ 1).setWidth 64) ((arg s₁ 2).setWidth 64)).2 =
    ((instOf T w).result s₂.mem ((arg s₂ 1).setWidth 64) ((arg s₂ 2).setWidth 64)).2
  rw [← tried_eq hw p₁, ← tried_eq hw p₂, ht]

/-- Unfolds the contract's public data at `h`. -/
macro "spec_pub" " at " h:ident : tactic => `(tactic| (
  sig_pub [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
    Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
    X86.abi, Abi.withConsts, stackBelow, stackT, String.reduceEq, Option.map_some,
    List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
    List.append_nil, argSlots, argVal, argBytes, ↓reduceIte, Option.map_some, tableRegion_eq, names_eq] at $h:ident))

theorem args_of {s₁ s₂ : State} (e₀ : arg s₁ 0 = arg s₂ 0) (e₁ : arg s₁ 1 = arg s₂ 1) (e₂ : arg s₁ 2 = arg s₂ 2)
    (e₃ : arg s₁ 3 = arg s₂ 3) (e₄ : arg s₁ 4 = arg s₂ 4) (e₅ : arg s₁ 5 = arg s₂ 5) :
    ∀ i < 6, arg s₁ i = arg s₂ i
  | 0, _ => e₀ | 1, _ => e₁ | 2, _ => e₂ | 3, _ => e₃ | 4, _ => e₄ | 5, _ => e₅

/-- The public data, with tables of constants. -/
theorem pub_cons {c : String × List (BitVec 64)} {cs : List (String × List (BitVec 64))}
    (hcs : R.E.combConsts = c :: cs) {s₁ s₂ : State}
    (h : (specK T (c :: cs) vs).pub s₁ s₂) : PubFacts R T vs s₁ s₂ := by
  spec_pub at h
  obtain ⟨hsp, hc₀, hcs', hn, hT, htr, e₀, e₁, e₂, e₃, e₄, e₅⟩ := h
  rw [List.append_eq, List.append_nil] at hn
  refine ⟨fun w hv => hT _ _ rfl rfl _ (List.mem_map_of_mem hv), hsp, args_of e₀ e₁ e₂ e₃ e₄ e₅,
    (List.cons.inj htr).1, fun c' hc' => ?_, hn⟩
  rw [hcs] at hc'
  rcases List.mem_cons.mp hc' with rfl | h
  · exact hc₀
  · exact hcs' _ h

/-- The public data, without tables of constants. -/
theorem pub_nil (hcs : R.E.combConsts = []) {s₁ s₂ : State}
    (h : (specK T [] vs).pub s₁ s₂) : PubFacts R T vs s₁ s₂ := by
  spec_pub at h
  obtain ⟨hsp, hn, hT, htr, e₀, e₁, e₂, e₃, e₄, e₅⟩ := h
  rw [List.append_eq, List.append_nil] at hn
  exact ⟨fun w hv => hT _ _ rfl rfl _ (List.mem_map_of_mem hv), hsp, args_of e₀ e₁ e₂ e₃ e₄ e₅,
    (List.cons.inj htr).1, fun c' hc' => absurd hc' (by rw [hcs]; simp), hn⟩

theorem PreFacts.pre (hO : OK vs) {s : State} (h : PreFacts R T vs s) : (tabK R T vs).pre s :=
  let ⟨⟨w, hv, hh⟩, f⟩ := h; ⟨w, hv, hO.2.2.2 w hv, f w hv hh⟩

/-- `TableInstance.signContract` with the tables of `vs` implies `tabK`. -/
theorem tab_implies (hsw : T.scratchWords = 1024) (hO : OK vs)
    (hsat : ∃ s, (specK T R.E.combConsts vs).pre s) : (tabK R T vs).Implies (specK T R.E.combConsts vs) := by
  generalize hcs : R.E.combConsts = cs at hsat ⊢
  have facts : ∀ s, (specK T cs vs).pre s → PreFacts R T vs s := fun s h => by
    cases cs with
    | nil => exact pre_nil hsw hO hcs h
    | cons c cs => exact pre_cons hsw hO hcs h
  have pubs : ∀ s₁ s₂, (specK T cs vs).pub s₁ s₂ → PubFacts R T vs s₁ s₂ := fun s₁ s₂ h => by
    cases cs with
    | nil => exact pub_nil hcs h
    | cons c cs => exact pub_cons hcs h
  refine ⟨fun s h => (facts s h).pre hO, fun s s' h hp => ?_,
    fun s₁ s₂ h₁ h₂ hp => pub_of hO (facts _ h₁) (facts _ h₂) (pubs _ _ hp), hsat⟩
  have hk := (facts s h).pre hO
  cases cs
  all_goals
    sig_post [Spec.Ecdsa.Rfc6979.TableInstance.signContract, Spec.Ecdsa.Rfc6979.TableInstance.signSig,
      Spec.HmacTable.param, Spec.HmacTable.wordCount, Spec.HmacTable.fns, Abi.withTables, Sig.wordIndex,
      X86.abi, Abi.withConsts, stackBelow, stackT, String.reduceEq, Option.map_some,
      List.getD_cons_succ, List.getD_cons_zero, Option.some.injEq, exists_eq_left',
      List.append_nil, argSlots, argVal, argBytes, ↓reduceIte, tableRegion_eq, names_eq]
    exact post_of hk hp

/-- `vg_ecdsa_<curve>_sign`, with the tables of `vs`, meets
`TableInstance.signContract` (given a state that meets it). -/
theorem signT_verified (hC : CurveT R T) (hsw : T.scratchWords = 1024) (hO : OK vs)
    (hsat : ∃ s, (specK T R.E.combConsts vs).pre s) :
    Verified X86.target (signCodeT R T.tries vs) (specK T R.E.combConsts vs) :=
  Verified.of_correct (fun _ h => signT_ok hC h) (signT_ct hC) (tab_implies hsw hO hsat)

end VG.Proof.Ecdsa.Rfc6979.X86

end

end

/-!
# Deterministic ECDSA on x86 (32-bit): the contract with the table is satisfiable

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/TableSat.lean`): a state meeting
`TableInstance.signContract` with the tables of `vs` (`satT`): the buffers
at fixed addresses, our arguments on the stack at `0x20004`, the table of a
variant `w` of `vs` at `0x300000`, the functions of `vs` at distinct
addresses (`HashTable.symsOf32`), and the curve's table of constants, if
any, at `0x100000`, where the memory `m₀` holds it (`sat_nil`, `sat_one`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86
open VG.Proof.HmacTable.X86 (HVar tables names tableOf held_tableOf hashAt_tableOf)
open VG.Proof.HashTable (symsOf32 symsOf32_distinct)

/-- Six 32-bit words at `p`. -/
def put6w (m : Mem) (p : Addr) (w₀ w₁ w₂ w₃ w₄ w₅ : BitVec 32) : Mem :=
  (((((m.writeW (p + BitVec.ofNat 64 (4 * 0)) w₀).writeW (p + BitVec.ofNat 64 (4 * 1)) w₁).writeW
    (p + BitVec.ofNat 64 (4 * 2)) w₂).writeW (p + BitVec.ofNat 64 (4 * 3)) w₃).writeW
    (p + BitVec.ofNat 64 (4 * 4)) w₄).writeW (p + BitVec.ofNat 64 (4 * 5)) w₅

/-- A word apart from a 32-bit write. -/
theorem readW_sepw {m : Mem} {a b : Addr} {w : Nat} {v : BitVec 32} (hw : w / 8 < 2 ^ 64)
    (h : a.toNat + w / 8 ≤ b.toNat ∨ b.toNat + 4 ≤ a.toNat) (ha : a.toNat + w / 8 ≤ 2 ^ 64)
    (hb : b.toNat + 4 ≤ 2 ^ 64) : (m.writeW b v).readW a w = m.readW a w :=
  Mem.readW_writeW_sep (fun x h1 h2 => by
    simp only [Nat.reduceDiv] at h1 h2
    rcases h with h | h <;> bv_omega) hw

theorem toNat_add_lit {p : Addr} {k : Nat} (h : p.toNat + k < 2 ^ 64) :
    (p + BitVec.ofNat 64 k).toNat = p.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega_using [h]), Nat.mod_eq_of_lt h]

/-- The words `put6w` writes. -/
theorem put6w_read {m : Mem} {p : Addr} (hp : p.toNat + 24 ≤ 2 ^ 64) (w₀ w₁ w₂ w₃ w₄ w₅ : BitVec 32) :
    ∀ i < 6, (put6w m p w₀ w₁ w₂ w₃ w₄ w₅).readW (p + BitVec.ofNat 64 (4 * i)) 32 = [w₀, w₁, w₂, w₃, w₄, w₅].getD i 0 := by
  intro i hi
  have t : ∀ k ≤ 20, (p + BitVec.ofNat 64 k).toNat = p.toNat + k := fun k hk => toNat_add_lit (by omega_using [hp, hk])
  have s : ∀ i j, i < 6 → j < 6 → i ≠ j → ∀ v : BitVec 32, ∀ m : Mem,
      (m.writeW (p + BitVec.ofNat 64 (4 * j)) v).readW (p + BitVec.ofNat 64 (4 * i)) 32 =
        m.readW (p + BitVec.ofNat 64 (4 * i)) 32 := fun i j hi hj hij v m => by
    refine readW_sepw (by decide) ?_ ?_ ?_ <;> simp only [Nat.reduceDiv, t (4 * i) (by omega_using [hi]), t (4 * j) (by omega_using [hj])] <;>
      omega_arith
  simp only [put6w]
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [s 0 5 (by decide) (by decide) (by decide), s 0 4 (by decide) (by decide) (by decide),
      s 0 3 (by decide) (by decide) (by decide), s 0 2 (by decide) (by decide) (by decide),
      s 0 1 (by decide) (by decide) (by decide), Mem.readW_writeW_self32]; rfl
  · rw [s 1 5 (by decide) (by decide) (by decide), s 1 4 (by decide) (by decide) (by decide),
      s 1 3 (by decide) (by decide) (by decide), s 1 2 (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]; rfl
  · rw [s 2 5 (by decide) (by decide) (by decide), s 2 4 (by decide) (by decide) (by decide),
      s 2 3 (by decide) (by decide) (by decide), Mem.readW_writeW_self32]; rfl
  · rw [s 3 5 (by decide) (by decide) (by decide), s 3 4 (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32]; rfl
  · rw [s 4 5 (by decide) (by decide) (by decide), Mem.readW_writeW_self32]; rfl
  · rw [Mem.readW_writeW_self32]; rfl

/-- What `put6w` keeps apart from its words. -/
theorem put6w_out {m : Mem} {p a : Addr} {w : Nat} (hw : w / 8 < 2 ^ 64) (hp : p.toNat + 24 ≤ 2 ^ 64)
    (ha : a.toNat + w / 8 ≤ p.toNat ∨ p.toNat + 24 ≤ a.toNat) (ha' : a.toNat + w / 8 ≤ 2 ^ 64)
    (w₀ w₁ w₂ w₃ w₄ w₅ : BitVec 32) : (put6w m p w₀ w₁ w₂ w₃ w₄ w₅).readW a w = m.readW a w := by
  have t : ∀ k ≤ 20, (p + BitVec.ofNat 64 k).toNat = p.toNat + k := fun k hk => toNat_add_lit (by omega_using [hp, hk])
  simp only [put6w]
  rw [readW_sepw hw, readW_sepw hw, readW_sepw hw, readW_sepw hw, readW_sepw hw, readW_sepw hw]
  all_goals first | (simp only [t 0 (by omega_using []), t 4 (by omega_using []), t 8 (by omega_using []), t 12 (by omega_using []), t 16 (by omega_using []),
    t 20 (by omega_using []), show 4 * 0 = 0 from rfl, show 4 * 1 = 4 from rfl, show 4 * 2 = 8 from rfl,
    show 4 * 3 = 12 from rfl, show 4 * 4 = 16 from rfl, show 4 * 5 = 20 from rfl]; omega_arith) | omega_using [ha']

/-- The functions of `vs` at distinct addresses, and every other symbol at `0x100000`. -/
def symT (vs : List HVar) (n : String) : BitVec 32 :=
  if n ∈ names vs then symsOf32 (names vs) n else 0x100000

/-- The arguments' words. -/
def argsMem (m₀ : Mem) (D : Nat) : Mem := put6w m₀ 0x20004 0x1000 0x2000 0x3000 (BitVec.ofNat 32 D) 0x8000 0x300000

/-- A state meeting the contract, for scalars of `Q` bytes, with the table
of `w` and the memory `m₀` (the curve's tables of constants `Tr`). -/
def satT (vs : List HVar) (w : HVar) (m₀ : Mem) (Q : Nat) (Tr : List Region) : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := put6w (argsMem m₀ w.F.H.D) 0x300000 (((symT vs w.F.hiN).setWidth 64).setWidth 32)
    (((symT vs w.F.H.updN).setWidth 64).setWidth 32) (((symT vs w.F.hfN).setWidth 64).setWidth 32)
    ((BitVec.ofNat 64 (Spec.HashTable.index w.G)).setWidth 32) ((BitVec.ofNat 64 w.G.len).setWidth 32)
    ((BitVec.ofNat 64 (Spec.HmacTable.blockSize w.G)).setWidth 32)
  rd := [⟨0x2000, Q⟩, ⟨0x3000, w.F.H.D⟩, ⟨0x300000, 24⟩] ++ Tr
  wr := [⟨0x1000, 2 * Q⟩, ⟨0x8000, 8192⟩, ⟨0x20004, 24⟩]
  syms := symT vs

theorem satT_held (vs : List HVar) (w : HVar) (m₀ : Mem) (Q : Nat) (Tr : List Region) :
    Abi.tableHeld 32 (satT vs w m₀ Q Tr).mem ((0x300000 : BitVec 32).setWidth 64)
      (FnTable.words isa (satT vs w m₀ Q Tr) (tableOf w)) := by
  intro i hi
  have hl : (FnTable.words isa (satT vs w m₀ Q Tr) (tableOf w)).length = 6 := rfl
  rw [hl] at hi
  exact put6w_read (p := 0x300000) (by decide) _ _ _ _ _ _ i hi |>.trans (by
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)

theorem satT_arg (vs : List HVar) (w : HVar) (m₀ : Mem) (Q : Nat) (Tr : List Region) :
    ∀ i < 6, arg (satT vs w m₀ Q Tr) i = [0x1000, 0x2000, 0x3000, BitVec.ofNat 32 w.F.H.D, 0x8000, 0x300000].getD i 0 := by
  intro i hi
  have ha : argAddr (satT vs w m₀ Q Tr) i = 0x20004 + BitVec.ofNat 64 (4 * i) := by
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega_using [hi]) with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  show (satT vs w m₀ Q Tr).mem.readW (argAddr (satT vs w m₀ Q Tr) i) 32 = _
  have h4 : (0x20004 : Addr).toNat = 0x20004 := rfl
  rw [ha]
  simp only [satT]
  rw [put6w_out (by decide) (by decide) (by
    rw [toNat_add_lit (by omega)]
    show 0x20004 + 4 * i + 32 / 8 ≤ 0x300000 ∨ _; omega_using [hi]) (by rw [toNat_add_lit (by omega)]; omega)]
  exact put6w_read (p := 0x20004) (by decide) _ _ _ _ _ _ i hi

theorem symT_distinct {vs : List HVar} (hl : (names vs).length < 2 ^ 24) :
    (names vs).Pairwise fun f g => f ≠ g → (symT vs f).setWidth 64 ≠ (symT vs g).setWidth 64 :=
  (symsOf32_distinct hl).imp_of_mem fun {f g} hf hg h hne => by
    simp only [symT, hf, hg, ite_true]; exact h hne

theorem constRegions_symT (vs : List HVar) (n : String) (W : List (BitVec 64)) (hna : n ∉ names vs) :
    Abi.constRegions (fun name => (symT vs name).setWidth 64) [(n, W)] = [⟨0x100000, 8 * W.length⟩] := by
  simp only [Abi.constRegions, List.map_cons, List.map_nil, symT, hna, ite_false]; rfl

/-- What the contract asks of the state, but for its tables of constants. -/
macro "sat_close" : tactic => `(tactic| first
  | decide
  | rfl
  | exact Region.disjoint_of_sep (by
      simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, BitVec.reduceSetWidth,
        BitVec.reduceSub, BitVec.reduceToNat, BitVec.toNat_ofNat]
      omega_arith)
  | bv_omega)

theorem sat_nil {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List HVar} (hO : OK vs)
    (hQ : T.ecdsa.curve.len ≤ 66) (hsw : T.scratchWords = 1024) : ∃ s, (specK T [] vs).pre s := by
  obtain ⟨w, hv⟩ := List.exists_mem_of_ne_nil vs hO.2.2.1
  have hw := hO.2.2.2 w hv
  refine ⟨satT vs w (fun _ => 0) T.ecdsa.curve.len [], ?_⟩
  have hD : w.F.H.D ≤ 64 := by
    have := hw.2.1; simp only [shapes, List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with h | h | h | h | h | h | h | h <;> rw [Prod.mk.injEq] at h <;> omega_using [h]
  have a := satT_arg vs w (fun _ => 0) T.ecdsa.curve.len []
  have a0 := a 0 (by decide); have a1 := a 1 (by decide); have a2 := a 2 (by decide)
  have a3 := a 3 (by decide); have a4 := a 4 (by decide); have a5 := a 5 (by decide)
  simp only [List.getD_cons_zero, List.getD_cons_succ] at a0 a1 a2 a3 a4 a5
  have e : argAddr (satT vs w (fun _ => 0) T.ecdsa.curve.len []) 0 = 0x20004 := rfl
  have hG : Spec.HmacTable.hashAt 32 (satT vs w (fun _ => 0) T.ecdsa.curve.len []).mem
      ((0x300000 : BitVec 32).setWidth 64) = some w.G :=
    hashAt_tableOf (by decide) (held_tableOf (by decide) (satT_held vs w _ _ _)).2.1
  have hheld := satT_held vs w (fun _ => 0) T.ecdsa.curve.len []
  have hrd : (satT vs w (fun _ => 0) T.ecdsa.curve.len []).rd =
      [⟨0x2000, T.ecdsa.curve.len⟩, ⟨0x3000, w.F.H.D⟩, ⟨0x300000, 24⟩] := rfl
  have hwr : (satT vs w (fun _ => 0) T.ecdsa.curve.len []).wr =
      [⟨0x1000, 2 * T.ecdsa.curve.len⟩, ⟨0x8000, 8192⟩, ⟨0x20004, 24⟩] := rfl
  have hesp : (satT vs w (fun _ => 0) T.ecdsa.curve.len []).gpr .esp = 0x20000 := rfl
  have hsy : (satT vs w (fun _ => 0) T.ecdsa.curve.len []).syms = symT vs := rfl
  generalize satT vs w (fun _ => 0) T.ecdsa.curve.len [] = s at a0 a1 a2 a3 a4 a5 e hG hheld hrd hwr hesp hsy ⊢
  spec_pre_goal
  simp only [a0, a1, a2, a3, a4, a5, e, hrd, hwr, hesp, hsy, hsw] at hG hheld ⊢
  sig_and_intros
  all_goals first
    | sat_close
    | exact ⟨tableOf w, List.mem_map_of_mem hv, hheld⟩
    | (rw [List.append_eq, List.append_nil]; exact symT_distinct hO.2.1)
    | (intro H hH
       obtain rfl := Option.some.inj (hH.symm.trans hG)
       exact ⟨by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hD]), w.glen], by rw [hw.hmac]; rfl⟩)
    | (rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hD])]; rfl)

theorem sat_one {T : Spec.Ecdsa.Rfc6979.TableInstance} {vs : List HVar} (hO : OK vs) {n : String}
    {W : List (BitVec 64)} (m₀ : Mem) (hna : n ∉ names vs) (hW : 8 * W.length ≤ 0x100000)
    (hm : ∀ i < W.length, m₀.readW (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = W.getD i 0)
    (hQ : T.ecdsa.curve.len ≤ 66) (hsw : T.scratchWords = 1024) : ∃ s, (specK T [(n, W)] vs).pre s := by
  obtain ⟨w, hv⟩ := List.exists_mem_of_ne_nil vs hO.2.2.1
  have hw := hO.2.2.2 w hv
  refine ⟨satT vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩], ?_⟩
  have hD : w.F.H.D ≤ 64 := by
    have := hw.2.1; simp only [shapes, List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with h | h | h | h | h | h | h | h <;> rw [Prod.mk.injEq] at h <;> omega_using [h]
  have a := satT_arg vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]
  have a0 := a 0 (by decide); have a1 := a 1 (by decide); have a2 := a 2 (by decide)
  have a3 := a 3 (by decide); have a4 := a 4 (by decide); have a5 := a 5 (by decide)
  simp only [List.getD_cons_zero, List.getD_cons_succ] at a0 a1 a2 a3 a4 a5
  have e : argAddr (satT vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]) 0 = 0x20004 := rfl
  have hG : Spec.HmacTable.hashAt 32 (satT vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]).mem
      ((0x300000 : BitVec 32).setWidth 64) = some w.G :=
    hashAt_tableOf (by decide) (held_tableOf (by decide) (satT_held vs w _ _ _)).2.1
  have hheld := satT_held vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]
  have hc : ∀ i < W.length, (satT vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]).mem.readW
      (0x100000 + BitVec.ofNat 64 (8 * i)) 64 = W.getD i 0 := fun i hi => by
    have l1 : (0x100000 : Addr).toNat = 0x100000 := rfl
    have l2 : (0x20004 : Addr).toNat = 0x20004 := rfl
    have l3 : (0x300000 : Addr).toNat = 0x300000 := rfl
    have h1 : (0x100000 + BitVec.ofNat 64 (8 * i) : Addr).toNat = 0x100000 + 8 * i :=
      toNat_add_lit (by rw [l1]; omega_using [hW, hi])
    simp only [satT, argsMem]
    rw [put6w_out (by decide) (by decide) (by rw [h1, l3]; simp only [Nat.reduceDiv]; omega_using [hW, hi]) (by rw [h1]; omega_using [h1]),
      put6w_out (by decide) (by decide) (by rw [h1, l2]; simp only [Nat.reduceDiv]; omega_using []) (by rw [h1]; omega_using [h1])]
    exact hm i hi
  have hrd : (satT vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]).rd =
      [⟨0x2000, T.ecdsa.curve.len⟩, ⟨0x3000, w.F.H.D⟩, ⟨0x300000, 24⟩] ++ [⟨0x100000, 8 * W.length⟩] := rfl
  have hwr : (satT vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]).wr =
      [⟨0x1000, 2 * T.ecdsa.curve.len⟩, ⟨0x8000, 8192⟩, ⟨0x20004, 24⟩] := rfl
  have hesp : (satT vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]).gpr .esp = 0x20000 := rfl
  have hsy : (satT vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩]).syms = symT vs := rfl
  have hsym : (symT vs n).setWidth 64 = 0x100000 := by simp only [symT, hna, ite_false]; rfl
  generalize satT vs w m₀ T.ecdsa.curve.len [⟨0x100000, 8 * W.length⟩] = s
    at a0 a1 a2 a3 a4 a5 e hG hheld hc hrd hwr hesp hsy ⊢
  spec_pre_goal
  simp only [a0, a1, a2, a3, a4, a5, e, hrd, hwr, hesp, hsy, hsw] at hG hheld ⊢
  sig_and_intros
  all_goals try (intro c hc'; simp only [List.mem_singleton] at hc'; subst hc')
  all_goals try (intro t ht; rw [constRegions_symT vs n W hna, List.mem_singleton] at ht; subst ht)
  all_goals first
    | sat_close
    | exact ⟨tableOf w, List.mem_map_of_mem hv, hheld⟩
    | (rw [List.append_eq, List.append_nil]; exact symT_distinct hO.2.1)
    | (intro H hH
       obtain rfl := Option.some.inj (hH.symm.trans hG)
       exact ⟨by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hD]), w.glen], by rw [hw.hmac]; rfl⟩)
    | (rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hD])]; rfl)
    | exact (constRegions_symT vs n W hna).symm
    | (intro i hi; dsimp only at hi ⊢; rw [hsym]; exact hc i hi)
    | (refine ⟨by bv_omega, ?_, ?_, ?_⟩ <;> first
        | (intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
           rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by
             simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]; bv_omega))
        | exact Region.disjoint_of_sep (by
            simp only [Region.sep, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]; bv_omega))

end VG.Proof.Ecdsa.Rfc6979.X86

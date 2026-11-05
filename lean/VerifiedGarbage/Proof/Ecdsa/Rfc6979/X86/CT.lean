module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Correct
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Reduce
import VerifiedGarbage.Proof.Framework.X86.TaintErase
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.ICall
import VerifiedGarbage.Proof.Framework.X86.Syms
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Correct
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Reduce
meta import VerifiedGarbage.Proof.Framework.X86.TaintErase
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.ICall
meta import VerifiedGarbage.Proof.Framework.X86.Syms

/-!
# Deterministic ECDSA on x86 (32-bit): constant time, up to the number of candidates

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/CT.lean`): two runs whose public
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

theorem pre {Φ' : Pr P} (h : Piece P Φ c Ψ) (hp : ∀ L m₀ t, Φ' L m₀ t → Φ L m₀ t) : Piece P Φ' c Ψ :=
  ⟨h.ct.mono (fun _ _ => Two.mono hp) fun _ _ h => h, fun L g m₀ t hL hk hc hφ => h.wp L g m₀ t hL hk hc (hp _ _ _ hφ)⟩

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
  refine WP.of_syms (hi_frame P.ok.hi P.ok.hiSp P.ok.hiSU
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
    obtain rfl | rfl : b = 0 ∨ b = 1 := by omega
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
    Nat.le_trans (Nat.mul_le_mul (show j + 1 ≤ P.nV by omega) (Nat.le_refl P.F.H.D)) (by omega)
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
      · exact hL.stk_SCR (by omega)
      · exact Offset.disjoint_base _ (by omega) (by omega)) (by decide)
  · have hnb := hL.nB
    have hfV : fV = 64 := rfl
    have hfT : fT = 376 := rfl
    have hfTl : fTlen = 152 := rfl
    have eS : (L.F + BitVec.ofNat 32 fV).setWidth 64 = L.B + BitVec.ofNat 64 (76 + fV) := hL.frv (by decide)
    have eD : (L.F + BitVec.ofNat 32 (fT + j * P.F.H.D)).setWidth 64 =
        L.B + BitVec.ofNat 64 (76 + fT + j * P.F.H.D) := by rw [hL.frv (by omega), Nat.add_assoc]
    refine WP.mono (cpLoop_ok hL hc (S := L.F + BitVec.ofNat 32 fV) (D := L.F + BitVec.ofNat 32 (fT + j * P.F.H.D))
        (n := P.F.H.D) (by omega) (by omega)
        (by rw [hL.frN (by decide)]; have := hL.e28; have := hL.e588; omega)
        (by rw [hL.frN (by omega)]; have := hL.e28; have := hL.e588; omega)
        (by rw [eS]; exact ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains _ (by decide) (by omega) (by omega)⟩)
        (by rw [eD]; exact hc.inFrW (by omega) (by omega) hL)
        (by rw [eS, eD]; exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega))
        (by rw [eD]; exact safe_high L (by omega) (by omega)) si bx cx) fun u ⟨hcu, hf, _, _⟩ => ⟨hcu, ?_⟩
    show tlen L u.mem = _
    rw [← hl]
    rw [eD] at hf
    exact hf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)) (by decide)

/-- The loop of the candidate's `V`s, in two runs: at the same block. -/
theorem candLoop_ct :
    RelCT isa (Two P (CJ P 0)) (.loop (cfgOf P).candStep .b) (Two P (CJ P P.nV)) := by
  obtain ⟨hN1, hND, -⟩ := nV_facts P
  obtain ⟨-, -, -, -, -, hD64, -, -, -, -, -, -, -, -, -, -, hQ66, -, -⟩ := P.sizes
  have h := VG.RelCT.loop (M := isa) (c := .b) (Q := Two P (CJ P P.nV))
    (fun n => fun s₁ s₂ => 0 < n ∧ n ≤ P.nV ∧ Two P (CJ P (P.nV - n)) s₁ s₂) (n := P.nV) (body := (cfgOf P).candStep)
    (fun n => by
      refine fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨hn0, hnN, hp⟩ e₁ e₂ => ?_
      have hj : P.nV - n < P.nV := by omega
      have hb : (P.nV - n + 1) * P.F.H.D ≤ 136 :=
        Nat.le_trans (Nat.mul_le_mul (show P.nV - n + 1 ≤ P.nV by omega) (Nat.le_refl P.F.H.D)) (by omega)
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
          omega
        exact ⟨e, hL, hk, hx, c₁, c₂, hNn ▸ f₁.1, hNn ▸ f₂.1⟩
      · intro hf
        obtain ⟨e, hL, hk, hx, c₁, c₂, f₁, f₂⟩ := hq
        have h' : (P.nV - n + 1) * P.F.H.D < P.Q := by
          by_contra h'; have := f₁.2; rw [decide_eq_false h'] at this; exact absurd (this.symm.trans hf) (by decide)
        have hlt := (nV_lt P (P.nV - n)).mpr h'
        refine ⟨n - 1, by omega, by omega, by omega, e, hL, hk, hx, c₁, c₂, ?_, ?_⟩ <;>
          rw [show P.nV - (n - 1) = P.nV - n + 1 by omega]
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
    rw [hL.frv (by simp only [fXc]; omega), Nat.add_assoc]
  have sepD : Region.Disjoint ⟨L.a2.setWidth 64, P.F.H.D⟩
      ⟨L.B + BitVec.ofNat 64 (76 + fXc + (P.Q - 1 - P.F.H.D)), P.F.H.D⟩ :=
    ((hL.kg.sub_left (Offset.sub_base _ (by simp only [fXc]; omega))).symm.sub_left (Region.sub_prefix hdn))
  exact WP.mono (cpLoop_ok hL hc₁ (S := L.a2) (D := L.F + BitVec.ofNat 32 (fXc + (P.Q - 1 - P.F.H.D)))
      (n := P.F.H.D) (by omega) (by omega) (by have := hL.ng; omega)
      (by rw [hL.frN (by simp only [fXc]; omega)]; have := hL.e28; have := hL.e588; simp only [fXc]; omega)
      (by have := hc₁.inDg (o := 0) (n := P.F.H.D) (by omega) (by omega); rwa [BitVec.add_zero] at this)
      (by rw [ea]; exact hc₁.inFrW (by omega) (by simp only [fXc]; omega) hL)
      (by rw [ea]; exact sepD)
      (by rw [ea]; exact safe_high L (by simp only [fXc]; omega) (by simp only [fXc]; omega))
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

/-- Two runs from states that satisfy the precondition and agree on public
data, after the frame's allocation. -/
def Entered (P : RfcHash) (ns : List String) (a b : State) : Prop :=
  ∃ s₁ s₂, ((rfcP P ns).pre s₁ ∧ (rfcP P ns).pre s₂ ∧ (rfcP P ns).pub s₁ s₂) ∧ a = allocState 512 s₁ ∧
    b = allocState 512 s₂

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

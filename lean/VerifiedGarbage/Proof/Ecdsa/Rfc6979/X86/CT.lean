module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Correct
public import VerifiedGarbage.Proof.Framework.X86.TaintErase
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Reduce
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Copy
import VerifiedGarbage.Proof.Framework.ICall
import VerifiedGarbage.Proof.Framework.KernelList
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.Layout
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Correct
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Reduce
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Copy
meta import VerifiedGarbage.Proof.Framework.X86.TaintErase
meta import VerifiedGarbage.Proof.Framework.X86.Syms
meta import VerifiedGarbage.Proof.Framework.ICall
meta import VerifiedGarbage.Proof.Framework.KernelList
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.Layout

/-!
# Deterministic ECDSA on x86 (32-bit): constant time, up to the number of candidates

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/CT.lean`): two runs whose public
data agree have the same layout, and stop at the same candidate (`exitAt`,
from the contract's leakage: the number of candidates RFC 6979 tries).
Between the save of our caller's registers and the frame's release they are
related by `Two`: both satisfy `Ctx` with that layout (and `Φ`, what the next
piece needs). The blocks address only the stack and the buffers, from
registers that agree (the taint analysis: of the blocks for each size of
hash function, `RfcT`, each curve's `RfcCurve.blkT`, and of those that
read our arguments, for each size of the frame); an indirect call reaches,
through the table, whose address our argument 5 is, the same function in
both runs (`tcall_piece`); each call, in a frame of its arguments, is of
constant-time code whose public data agree (`init_rel`, `upd_rel`,
`fin_rel`, `callWithR_ct`); and the loop's branch agrees, since in both runs
it goes on after candidate `i` iff `i` is before the candidate it stops at
(`go_iff`). The frame's allocation and release access no memory
(`alloc_ct`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.Impl.Ecdsa.Rfc6979.X86
open VG.Proof.Pbkdf2.Stream.X86 (init_rel upd_rel fin_rel)

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

/-- What each of two runs has, between the save of our caller's registers
and the frame's release. -/
abbrev Env (P : RfcHash) := Lay P.I.hashLen × (Reg → BitVec 32) × (Reg → BitVec 32) × Mem × Mem

/-- What the proof needs of each run at a point of the code. -/
abbrev Pred (P : RfcHash) := Lay P.I.hashLen → (Reg → BitVec 32) → Mem → State → Prop

/-- Two runs with the layout and saved registers of `e`, that stop at the
same candidate, each satisfying `Ctx` and `Φ`. -/
def TwoAt (P : RfcHash) (Φ : Pred P) (e : Env P) (a b : State) : Prop :=
  e.1.Ok ∧ CoreOk P e.1 ∧ exitAt P e.1 e.2.2.2.1 = exitAt P e.1 e.2.2.2.2 ∧ Ctx e.1 e.2.1 e.2.2.2.1 a ∧
    Ctx e.1 e.2.2.1 e.2.2.2.2 b ∧ Φ e.1 e.2.1 e.2.2.2.1 a ∧ Φ e.1 e.2.2.1 e.2.2.2.2 b

/-- Two runs with the same layout that stop at the same candidate. -/
def Two (P : RfcHash) (Φ : Pred P) (a b : State) : Prop := ∃ e, TwoAt P Φ e a b

variable {P : RfcHash}

theorem two_exists {Φ : Pred P} {c : Prog isa} {Q : State → State → Prop}
    (h : ∀ e, RelCT isa (TwoAt P Φ e) c Q) : RelCT isa (Two P Φ) c Q :=
  VG.RelCT.exists_ h

theorem Two.mono {Φ Ψ : Pred P} (h : ∀ L g m₀ t, Φ L g m₀ t → Ψ L g m₀ t) {a b : State}
    (ht : Two P Φ a b) : Two P Ψ a b :=
  let ⟨e, hL, hq, hx, c₁, c₂, f₁, f₂⟩ := ht
  ⟨e, hL, hq, hx, c₁, c₂, h _ _ _ _ f₁, h _ _ _ _ f₂⟩

/-- Code whose runs leak the same, and which keeps `Ctx` and establishes `Ψ`. -/
theorem two_wp {c : Prog isa} {Φ Ψ : Pred P}
    (hct : RelCT isa (Two P Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay P.I.hashLen) g m₀ (t : State), L.Ok → CoreOk P L → Ctx L g m₀ t → Φ L g m₀ t →
      WP isa c t fun t' => Ctx L g m₀ t' ∧ Ψ L g m₀ t') :
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

/-- A block whose addresses depend only on the registers `rs`, which agree. -/
theorem two_blk {is : List Instr} {Φ : Pred P} (rs : List Reg)
    (hrs : ∀ (L : Lay P.I.hashLen) (t₁ t₂ : State) g₁ g₂ m₁ m₂, Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ →
      Φ L g₁ m₁ t₁ → Φ L g₂ m₂ t₂ → ∀ r ∈ rs, t₁.gpr r = t₂.gpr r)
    (h : TaintOk rs is) : RelCT isa (Two P Φ) (.block is) fun _ _ => True :=
  let ⟨_, h⟩ := h
  VG.RelCT.taint (A := taint) (τr rs)
    (fun _ _ ⟨_, _, _, _, c₁, c₂, f₁, f₂⟩ => agree_regs (hrs _ _ _ _ _ _ _ c₁ c₂ f₁ f₂)) h

theorem espOnly {Φ : Pred P} : ∀ (L : Lay P.I.hashLen) (t₁ t₂ : State) g₁ g₂ m₁ m₂,
    Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ → Φ L g₁ m₁ t₁ → Φ L g₂ m₂ t₂ → ∀ r ∈ [Reg.esp], t₁.gpr r = t₂.gpr r := by
  intro L t₁ t₂ _ _ _ _ c₁ c₂ _ _ r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact esp_two c₁ c₂

/-! ## Pieces: related in two runs, and keeping `Ctx` in each -/

/-- Nothing. -/
abbrev Tt (P : RfcHash) : Pred P := fun _ _ _ _ => True

/-- Code that, from `Φ`, leaks the same in two runs and gives `Ψ`, keeping
`Ctx`, in each. -/
structure Piece (P : RfcHash) (Φ : Pred P) (c : Prog isa) (Ψ : Pred P) : Prop where
  ct : RelCT isa (Two P Φ) c (Two P Ψ)
  wp : ∀ (L : Lay P.I.hashLen) g m₀ (t : State), L.Ok → CoreOk P L → Ctx L g m₀ t → Φ L g m₀ t →
    WP isa c t fun t' => Ctx L g m₀ t' ∧ Ψ L g m₀ t'

namespace Piece

variable {Φ Ψ Χ : Pred P} {a b c : Prog isa}

theorem of (hct : RelCT isa (Two P Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay P.I.hashLen) g m₀ (t : State), L.Ok → CoreOk P L → Ctx L g m₀ t → Φ L g m₀ t →
      WP isa c t fun t' => Ctx L g m₀ t' ∧ Ψ L g m₀ t') : Piece P Φ c Ψ :=
  ⟨two_wp hct hw, hw⟩

theorem seq (h₁ : Piece P Φ a Ψ) (h₂ : Piece P Ψ b Χ) : Piece P Φ (.seq a b) Χ :=
  ⟨h₁.ct.seq h₂.ct, fun L g m₀ t hL hk hc hφ =>
    WP.seq (WP.mono (h₁.wp L g m₀ t hL hk hc hφ) fun _ ⟨c', ψ⟩ => h₂.wp L g m₀ _ hL hk c' ψ)⟩

/-- What the relational proofs of the loop use. -/
theorem rel (h : Piece P Φ c Ψ) {Φ' : Pred P} (hp : ∀ L g m₀ t, Φ' L g m₀ t → Φ L g m₀ t) :
    RelCT isa (Two P Φ') c fun _ _ => True :=
  h.ct.mono (fun _ _ => Two.mono hp) fun _ _ _ => trivial

end Piece

/-- A block whose addresses depend only on the registers `rs`, which agree. -/
theorem Piece.blk {is : List Instr} {Φ Ψ : Pred P} (rs : List Reg)
    (hrs : ∀ (L : Lay P.I.hashLen) (t₁ t₂ : State) g₁ g₂ m₁ m₂, Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ →
      Φ L g₁ m₁ t₁ → Φ L g₂ m₂ t₂ → ∀ r ∈ rs, t₁.gpr r = t₂.gpr r)
    (ht : TaintOk rs is)
    (hw : ∀ (L : Lay P.I.hashLen) g m₀ (t : State), L.Ok → CoreOk P L → Ctx L g m₀ t → Φ L g m₀ t →
      WP isa (.block is) t fun t' => Ctx L g m₀ t' ∧ Ψ L g m₀ t') : Piece P Φ (.block is) Ψ :=
  Piece.of (two_blk rs hrs ht) hw

/-- A block whose addresses depend only on `esp`. -/
theorem Piece.blkS {is : List Instr} {Φ Ψ : Pred P} (ht : TaintOk [.esp] is)
    (hw : ∀ (L : Lay P.I.hashLen) g m₀ (t : State), L.Ok → CoreOk P L → Ctx L g m₀ t → Φ L g m₀ t →
      WP isa (.block is) t fun t' => Ctx L g m₀ t' ∧ Ψ L g m₀ t') : Piece P Φ (.block is) Ψ :=
  Piece.blk [.esp] espOnly ht hw

/-! ## The blocks that read our arguments, for each size of the frame -/

/-- The taint check from a hint that knows no region base: it holds of the
block with any other immediates and displacements but at `esp`
(`taintOk_erase`). -/
abbrev TaintOkE (rs : List Reg) (is : List Instr) : Prop :=
  ∃ hc, ((VG.Taint.check taint (τr rs) (.block is) hc).isSome && X86.Taint.hintNoBases hc) = true

theorem noB (rs : List Reg) : X86.Taint.noBases (τr rs) = true := rfl

/-- The taint check of a block is that of any block with the same
instructions but for displacements (but at `esp`) and immediates
(`Taint.check_erase`). -/
theorem taintOk_erase {rs : List Reg} {is is₀ : List Instr} (h : TaintOkE rs is₀)
    (he : is.map Instr.erase = is₀.map Instr.erase) : TaintOk rs is := by
  obtain ⟨hc, hs⟩ := h
  rw [Bool.and_eq_true] at hs
  refine ⟨hc, ?_⟩
  rw [← X86.Taint.check_erase (.block is) _ _ (noB rs) hs.2,
    show Code.erase (.block is) = Code.erase (.block is₀) from
      congrArg Code.block (by rw [KList.map_eq, KList.map_eq, he]),
    X86.Taint.check_erase _ _ _ (noB rs) hs.2]
  exact hs.1

/-- The table's address into `esi`. -/
theorem tblk1_taint (c : Cfg) : TaintOk [.esp] [.mov .esi (c.arg 5)] := by
  show TaintOk [.esp] [.mov .esi (argM c.wide c.hHigh 5)]
  generalize c.wide = w; generalize c.hHigh = h
  cases w <;> cases h <;> exact ⟨_, by taint_decide⟩

/-- The table's word `j` into `esi`. -/
theorem tblk2_taint (j : Nat) :
    TaintOk [.esi] [.mov .esi (.mem (Impl.Pbkdf2.Stream.X86.at_ .esi (4 * j)))] :=
  taintOk_erase (is₀ := [.mov .esi (.mem (Impl.Pbkdf2.Stream.X86.at_ .esi 0))]) ⟨_, by taint_decide⟩ rfl

/-- `scratch` into `edi`. -/
theorem scrPtr_taint (c : Cfg) : TaintOk [.esp] c.scrPtr := by
  show TaintOk [.esp] [.mov .edi (argM c.wide c.hHigh 4)]
  generalize c.wide = w; generalize c.hHigh = h
  cases w <;> cases h <;> exact ⟨_, by taint_decide⟩

/-- `scratch` into `edi`, `d` into `esi`. -/
theorem msgPtrs_taint (c : Cfg) : TaintOk [.esp] c.msgPtrs := by
  show TaintOk [.esp] [.mov .edi (argM c.wide c.hHigh 4), .mov .esi (argM c.wide c.hHigh 1)]
  generalize c.wide = w; generalize c.hHigh = h
  cases w <;> cases h <;> exact ⟨_, by taint_decide⟩

/-- `scratch + a` into `ebx`. -/
theorem scrB_taint (c : Cfg) (a : Nat) : TaintOk [.esp] (c.scr .ebx a) := by
  refine taintOk_erase (is₀ := c.scr .ebx 0) ?_ rfl
  show TaintOkE [.esp] [.mov .ebx (argM c.wide c.hHigh 4), .alu .add .ebx (.imm (BitVec.ofNat 32 0))]
  generalize c.wide = w; generalize c.hHigh = h
  cases w <;> cases h <;> exact ⟨_, by taint_decide⟩

/-- `update`'s arguments, with data in the frame (`fr`) or in `scratch`. -/
theorem updArgs_taint (c : Cfg) (o cnt a len : Nat) (fr : Bool) :
    TaintOk [.esp] (c.updArgs o cnt (if fr then Cfg.fr .edx a else c.scr .edx a) len) := by
  refine taintOk_erase (is₀ := c.updArgs 0 0 (if fr then Cfg.fr .edx 0 else c.scr .edx 0) 0) ?_
    (by cases fr <;> rfl)
  simp only [Cfg.updArgs, Cfg.scr, Cfg.fr, Cfg.arg]
  generalize c.wide = w; generalize c.hHigh = h
  cases fr <;> cases w <;> cases h <;> exact ⟨_, by taint_decide⟩

/-- `finalize`'s arguments. -/
theorem finArgs_taint (c : Cfg) (o cnt : Nat) : TaintOk [.esp] (c.finArgs o cnt) := by
  refine taintOk_erase (is₀ := c.finArgs 0 0) ?_ rfl
  simp only [Cfg.finArgs, Cfg.scr, Cfg.arg]
  generalize c.wide = w; generalize c.hHigh = h
  cases w <;> cases h <;> exact ⟨_, by taint_decide⟩

/-! ## The indirect calls -/

/-- What an indirect call of `n` needs of the table in each run: its word
`j` (on entry) is `n`'s address, which is the layout's, and of `ts` an
indirect call reaches `n`'s `c`. -/
def TabFn (P : RfcHash) (j : Nat) (n : String) (c : Prog isa) (ts : List (String × Prog isa)) : Prop :=
  ∀ (L : Lay P.I.hashLen) g m₀ (t : State), L.Ok → CoreOk P L → Ctx L g m₀ t →
    m₀.readW (L.tab + BitVec.ofNat 64 (4 * j)) 32 = t.syms n ∧
      ts.find? (fun q => (t.syms q.1).setWidth 64 == (t.syms n).setWidth 64) = some (n, c) ∧ t.syms n = L.fa n

theorem tfn_init : TabFn P 0 P.H.initN P.H.initC P.f.init := fun L _ _ _ _ hk hc => by
  have hok := hc.tabOk; have htm := hc.tabMem; have hf := hc.fsy
  rw [hk.2.2.2.2.1, hk.2.2.2.2.2] at hok; rw [hk.2.2.2.2.1] at htm hf
  exact ⟨htm.1, hok.1, hf _ (by simp)⟩

theorem tfn_upd : TabFn P 1 P.H.updN P.H.updC P.f.upd := fun L _ _ _ _ hk hc => by
  have hok := hc.tabOk; have htm := hc.tabMem; have hf := hc.fsy
  rw [hk.2.2.2.2.1, hk.2.2.2.2.2] at hok; rw [hk.2.2.2.2.1] at htm hf
  exact ⟨htm.2.1, hok.2.1, hf _ (by simp)⟩

theorem tfn_fin : TabFn P 2 P.H.finN P.H.finC P.f.fin := fun L _ _ _ _ hk hc => by
  have hok := hc.tabOk; have htm := hc.tabMem; have hf := hc.fsy
  rw [hk.2.2.2.2.1, hk.2.2.2.2.2] at hok; rw [hk.2.2.2.2.1] at htm hf
  exact ⟨htm.2.2, hok.2.2, hf _ (by simp)⟩

/-- What only `esi` changing keeps. -/
def EsiK (Φ : Pred P) : Prop :=
  ∀ L g m₀ (t u : State), Φ L g m₀ t → (∀ r, r ≠ .esi → u.gpr r = t.gpr r) → u.mem = t.mem → u.syms = t.syms →
    Φ L g m₀ u

/-- The indirect call of the table's function `j`: in both runs of the same
function, `n`'s (the table's word `j` holds the layout's address of `n`). -/
theorem tcall_piece {Φ Ψ : Pred P} {j : Nat} (hj : 4 * j + 4 ≤ 20) {n : String} {c : Prog isa}
    {ts : List (String × Prog isa)} {rs : List Reg} (hn : TabFn P j n c ts) (hΦ : EsiK Φ)
    (hcall : Piece P Φ (.frame (.push rs) (.call n c) (.pop .eax rs.length)) Ψ) :
    Piece P Φ ((cfgOf P).tcall j ts rs) Ψ := by
  refine ⟨?_, fun L g m₀ t hL hk hc hφ => ?_⟩
  · unfold Cfg.tcall
    have s₁ : Piece P Φ (.block [.mov .esi ((cfgOf P).arg 5)]) fun L g m₀ u => Φ L g m₀ u ∧ u.gpr .esi = L.a5 :=
      Piece.blkS (tblk1_taint _) fun L g m₀ t hL hk hc hφ =>
        WP.mono_syms (tblk1_ok hL hk.tabL hc) fun u h hs => ⟨h.ctx, hΦ _ _ _ _ _ hφ h.keep h.mem hs, h.val⟩
    have s₂ : Piece P (fun L g m₀ u => Φ L g m₀ u ∧ u.gpr .esi = L.a5)
        (.block [.mov .esi (.mem (Impl.Pbkdf2.Stream.X86.at_ .esi (4 * j)))])
        fun L g m₀ u => Φ L g m₀ u ∧ u.gpr .esi = L.fa n ∧ u.syms n = L.fa n ∧
          ts.find? (fun q => (u.syms q.1).setWidth 64 == (u.syms n).setWidth 64) = some (n, c) :=
      Piece.blk [.esi] (fun _ _ _ _ _ _ _ _ _ f₁ f₂ r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact f₁.2.trans f₂.2.symm) (tblk2_taint _)
        fun L g m₀ t hL hk hc ⟨hφ, hsi⟩ => WP.mono_syms (tblk2_ok hL hc hsi hj) fun u h hs => by
          obtain ⟨hw, hf, hfa⟩ := hn L g m₀ t hL hk hc
          exact ⟨h.ctx, hΦ _ _ _ _ _ hφ h.keep h.mem hs, by rw [h.val, hw, hfa], by rw [hs, hfa],
            by rw [hs]; exact hf⟩
    refine s₁.ct.seq (s₂.ct.seq ?_)
    cases ts with
    | nil => exact RelCT.of_false fun _ _ ⟨_, _, _, _, _, _, f₁, _⟩ => by simp at f₁
    | cons q ts =>
      refine RelCT.frame_icalls_of_call (hcall.ct.mono (fun _ _ => Two.mono fun _ _ _ _ h => h.1) fun _ _ h => h)
        fun s₁ s₂ ⟨e, _, _, _, c₁, c₂, f₁, f₂⟩ => ⟨?_, fun u₁ u₂ hp₁ hp₂ => ?_⟩
      · show addrs (.push rs) s₁ = addrs (.push rs) s₂
        simp only [addrs, esp_two c₁ c₂]
      · obtain ⟨-, -, -, rfl⟩ := push_some hp₁
        obtain ⟨-, -, -, rfl⟩ := push_some hp₂
        have g₁ : ((pushed rs s₁).gpr .esi) = e.1.fa n := by rw [pushed_gpr _ _ (by decide), f₁.2.1]
        have g₂ : ((pushed rs s₂).gpr .esi) = e.1.fa n := by rw [pushed_gpr _ _ (by decide), f₂.2.1]
        refine ⟨(e.1.fa n).setWidth 64, by rw [← g₁]; rfl, by rw [← g₂]; rfl, ?_, ?_, rfl⟩
        · show (q :: ts).find? (fun p => ((pushed rs s₁).syms p.1).setWidth 64 == (e.1.fa n).setWidth 64) = _
          rw [show (pushed rs s₁).syms = s₁.syms from pushRegs_syms s₁ rs, ← f₁.2.2.1]; exact f₁.2.2.2
        · show (q :: ts).find? (fun p => ((pushed rs s₂).syms p.1).setWidth 64 == (e.1.fa n).setWidth 64) = _
          rw [show (pushed rs s₂).syms = s₂.syms from pushRegs_syms s₂ rs, ← f₂.2.2.1]; exact f₂.2.2.2
  · obtain ⟨hw, hf, -⟩ := hn L g m₀ t hL hk hc
    exact tcall_ok hL hk.tabL hc hj hw hf fun t' hc' hm hr hs =>
      hcall.wp L g m₀ t' hL hk hc' (hΦ _ _ _ _ _ hφ hr hm hs)

/-! ## The streaming calls -/

/-- `init`'s argument: the state at `scratch + o`. -/
def IA (P : RfcHash) (o : Nat) : Pred P := fun L _ _ u => u.gpr .ebx = L.a4 + BitVec.ofNat 32 o

theorem init_piece {o : Nat} (ho : o + 256 ≤ 512) :
    Piece P (IA P o) (.frame (.push [.ebx]) (.call P.H.initN P.H.initC) (.pop .eax [Reg.ebx].length)) (Tt P) :=
  Piece.of (two_exists fun e => init_rel P.ok (sp := e.1.F) fun _ _ ⟨hL, _, _, c₁, c₂, d₁, d₂⟩ =>
      ⟨initArgsOf hL c₁ ho d₁, initArgsOf hL c₂ ho d₂, c₁.esp, c₂.esp⟩)
    fun _ _ _ _ hL _ hc hd => WP.mono (initRaw_ok hL hc ho hd) fun _ h => ⟨h.1, trivial⟩

/-- `update`'s arguments: the state at `scratch + o` holding `cnt` bytes,
the `len` bytes at `dv`, and the working space. -/
def UA (P : RfcHash) (o cnt : Nat) (dv : Lay P.I.hashLen → BitVec 32) (len : Nat) : Pred P := fun L _ _ u =>
  u.gpr .ebx = L.a4 + BitVec.ofNat 32 o ∧ u.gpr .edi = BitVec.ofNat 32 cnt ∧ u.gpr .eax = 0 ∧
    u.gpr .edx = dv L ∧ u.gpr .ecx = BitVec.ofNat 32 len ∧ u.gpr .ebp = L.a4 + BitVec.ofNat 32 512

theorem upd_piece {o cnt : Nat} (ho : o + 256 ≤ 512) {dv : Lay P.I.hashLen → BitVec 32} {len : Nat}
    (hd : ∀ L : Lay P.I.hashLen, L.Ok → UpdData P L o (dv L) len) (hlen : len < 2 ^ 32) (hcnt : cnt < 2 ^ 32) :
    Piece P (UA P o cnt dv len) (.frame (.push upd6) (.call P.H.updN P.H.updC) (.pop .eax upd6.length)) (Tt P) :=
  Piece.of (two_exists fun e => upd_rel P.ok (sp := e.1.F) fun _ _ ⟨hL, _, _, c₁, c₂,
      ⟨b₁, d₁, a₁, x₁, k₁, p₁⟩, ⟨b₂, d₂, a₂, x₂, k₂, p₂⟩⟩ =>
    ⟨updArgsOf hL c₁ ho (hd _ hL) hlen b₁ d₁ a₁ x₁ k₁ p₁, updArgsOf hL c₂ ho (hd _ hL) hlen b₂ d₂ a₂ x₂ k₂ p₂,
      c₁.esp, c₂.esp⟩)
    fun _ _ _ _ hL _ hc ⟨b, d, a, x, k, p⟩ =>
      WP.mono (updRaw_ok hL hc ho (hd _ hL) hlen hcnt b d a x k p) fun _ h => ⟨h.1, trivial⟩

/-- `finalize`'s arguments: the state at `scratch + o` holding `cnt` bytes,
the output at `scratch + sTmp`, and the working space. -/
def FA (P : RfcHash) (o cnt : Nat) : Pred P := fun L _ _ u =>
  u.gpr .ebx = L.a4 + BitVec.ofNat 32 o ∧ u.gpr .eax = BitVec.ofNat 32 cnt ∧ u.gpr .ecx = 0 ∧
    u.gpr .edx = L.a4 + BitVec.ofNat 32 1152 ∧ u.gpr .ebp = L.a4 + BitVec.ofNat 32 512

theorem fin_piece {o cnt : Nat} (ho : o + 256 ≤ 512) (hcnt : cnt < 2 ^ 32) :
    Piece P (FA P o cnt) (.frame (.push fin5) (.call P.H.finN P.H.finC) (.pop .eax fin5.length)) (Tt P) :=
  Piece.of (two_exists fun e => fin_rel P.ok (sp := e.1.F) fun _ _ ⟨hL, _, _, c₁, c₂,
      ⟨b₁, a₁, x₁, d₁, p₁⟩, ⟨b₂, a₂, x₂, d₂, p₂⟩⟩ =>
    ⟨finArgsOf hL c₁ ho b₁ a₁ x₁ d₁ p₁, finArgsOf hL c₂ ho b₂ a₂ x₂ d₂ p₂, c₁.esp, c₂.esp⟩)
    fun _ _ _ _ hL _ hc ⟨b, a, x, d, p⟩ =>
      WP.mono (finRaw_ok hL hc ho hcnt b a x d p) fun _ h => ⟨h.1, trivial⟩

theorem esi_ia {o : Nat} : EsiK (IA P o) := fun _ _ _ _ _ h hr _ _ => (hr _ (by decide)).trans h

theorem esi_ua {o cnt : Nat} {dv : Lay P.I.hashLen → BitVec 32} {len : Nat} : EsiK (UA P o cnt dv len) :=
  fun _ _ _ _ _ ⟨b, d, a, x, k, p⟩ hr _ _ => ⟨(hr _ (by decide)).trans b, (hr _ (by decide)).trans d,
    (hr _ (by decide)).trans a, (hr _ (by decide)).trans x, (hr _ (by decide)).trans k, (hr _ (by decide)).trans p⟩

theorem esi_fa {o cnt : Nat} : EsiK (FA P o cnt) :=
  fun _ _ _ _ _ ⟨b, a, x, d, p⟩ hr _ _ => ⟨(hr _ (by decide)).trans b, (hr _ (by decide)).trans a,
    (hr _ (by decide)).trans x, (hr _ (by decide)).trans d, (hr _ (by decide)).trans p⟩

/-- `init` of the state at `scratch + o`, through the table. -/
theorem initCall_piece {Φ : Pred P} {o : Nat} (ho : o + 256 ≤ 512) : Piece P Φ ((cfgOf P).initCall o) (Tt P) :=
  (Piece.blkS (Ψ := IA P o) (scrB_taint _ o) fun _ _ _ _ hL hk hc _ =>
    WP.mono (scr_ok hL hk.tabL.cw hk.tabL.ch hc (d := .ebx) (by decide) o) fun _ h => ⟨h.ctx, h.val⟩).seq
    (tcall_piece (by decide) tfn_init esi_ia (init_piece ho))

/-- The data block of `update`: the address of the data in `edx`. -/
def DataA (P : RfcHash) (dataA : List Instr) (dv : Lay P.I.hashLen → BitVec 32) : Prop :=
  ∀ (L : Lay P.I.hashLen) g m₀ (u : State), L.Ok → CoreOk P L → Ctx L g m₀ u →
    WP isa (.block dataA) u (Upd L g m₀ u .edx (dv L))

/-- `update` of the state at `scratch + o`, holding `cnt` bytes, with `len`
bytes at `dv`, through the table. -/
theorem updCall_piece {Φ : Pred P} {o cnt : Nat} (ho : o + 256 ≤ 512) {dataA : List Instr}
    {dv : Lay P.I.hashLen → BitVec 32} {len : Nat} (hdA : DataA P dataA dv)
    (hd : ∀ L : Lay P.I.hashLen, L.Ok → UpdData P L o (dv L) len)
    (ht : TaintOk [.esp] ((cfgOf P).updArgs o cnt dataA len)) (hcnt : cnt < 2 ^ 32) (hlen : len < 2 ^ 32) :
    Piece P Φ ((cfgOf P).updCall o cnt dataA len) (Tt P) :=
  (Piece.blkS (Ψ := UA P o cnt dv len) ht fun L g m₀ _ hL hk hc _ =>
    WP.mono (updArgs_ok hL hk.tabL hc (o := o) (cnt := cnt) (len := len) fun u hu => hdA L g m₀ u hL hk hu)
      fun _ ⟨c, _, b, d, a, x, k, p⟩ => ⟨c, b, d, a, x, k, p⟩).seq
    (tcall_piece (by decide) tfn_upd esi_ua (upd_piece ho hd hlen hcnt))

/-- `finalize` of the state at `scratch + o`, holding `cnt` bytes, through the table. -/
theorem finCall_piece {Φ : Pred P} {o cnt : Nat} (ho : o + 256 ≤ 512) (hcnt : cnt < 2 ^ 32) :
    Piece P Φ ((cfgOf P).finCall o cnt) (Tt P) :=
  (Piece.blkS (Ψ := FA P o cnt) (finArgs_taint _ o cnt) fun _ _ _ _ hL hk hc _ =>
    WP.mono (finArgs_ok hL hk.tabL hc o cnt) fun _ ⟨c, _, b, a, x, d, p⟩ => ⟨c, b, a, x, d, p⟩).seq
    (tcall_piece (by decide) tfn_fin esi_fa (fin_piece ho hcnt))

/-! ## Blocks from `scratch`'s pointer -/

/-- `scratch` in `edi`. -/
def ScrIn (P : RfcHash) : Pred P := fun L _ _ u => u.gpr .edi = L.a4

theorem scrPtr_piece {Φ : Pred P} : Piece P Φ (.block (cfgOf P).scrPtr) (ScrIn P) :=
  Piece.blkS (scrPtr_taint _) fun _ _ _ _ hL hk hc _ =>
    WP.mono (scrPtr_ok hL hk.tabL hc) fun _ h => ⟨h.ctx, h.val⟩

theorem scrRegs {Φ : Pred P} (hΦ : ∀ L g m₀ t, Φ L g m₀ t → t.gpr .edi = L.a4) :
    ∀ (L : Lay P.I.hashLen) (t₁ t₂ : State) g₁ g₂ m₁ m₂, Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ → Φ L g₁ m₁ t₁ →
      Φ L g₂ m₂ t₂ → ∀ r ∈ [Reg.esp, .edi], t₁.gpr r = t₂.gpr r := by
  intro L _ _ _ _ _ _ c₁ c₂ f₁ f₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact esp_two c₁ c₂
  · exact (hΦ _ _ _ _ f₁).trans (hΦ _ _ _ _ f₂).symm

/-- A block that loads `scratch` into `edi`, then addresses memory only from
`esp` and `edi`. -/
theorem Piece.scrBlk {is : List Instr} {Φ Ψ : Pred P} (ht : TaintOk [.esp, .edi] is)
    (hw : ∀ (L : Lay P.I.hashLen) g m₀ (t : State), L.Ok → CoreOk P L → Ctx L g m₀ t → Φ L g m₀ t →
      WP isa (.block ((cfgOf P).scrPtr ++ is)) t fun t' => Ctx L g m₀ t' ∧ Ψ L g m₀ t') :
    Piece P Φ (.block ((cfgOf P).scrPtr ++ is)) Ψ :=
  Piece.of (RelCT.block_append (scrPtr_piece.ct.seq (two_blk [.esp, .edi] (scrRegs fun _ _ _ _ h => h) ht))) hw

/-! ## HMAC -/

/-- `K₀ ⊕ c` at `scratch + sPad`. -/
theorem padBlk_piece {Φ : Pred P} (c : Byte)
    (ht : TaintOk [.esp, .edi] (([.mov .ecx (.imm (c ++ c ++ c ++ c))] : List Instr) ++
      (List.range ((cfgOf P).B / 4)).flatMap (cfgOf P).padW)) :
    Piece P Φ (.block ((cfgOf P).padBlk (c ++ c ++ c ++ c))) (Tt P) := by
  have e : (cfgOf P).padBlk (c ++ c ++ c ++ c) = (cfgOf P).scrPtr ++
      (([.mov .ecx (.imm (c ++ c ++ c ++ c))] : List Instr) ++ (List.range ((cfgOf P).B / 4)).flatMap (cfgOf P).padW) := by
    simp only [Cfg.padBlk, List.append_assoc]
  rw [e]
  refine Piece.scrBlk ht fun _ _ _ _ hL hk hc _ => ?_
  rw [← e]
  exact WP.mono (padBlk_ok hL hk.tabL hc c) fun _ h => ⟨h.1, trivial⟩

/-- Data at `scratch + a`. -/
theorem scrDA (a : Nat) : DataA P ((cfgOf P).scr .edx a) fun L => L.a4 + BitVec.ofNat 32 a :=
  fun _ _ _ _ hL hk hu => scr_ok hL hk.tabL.cw hk.tabL.ch hu (d := .edx) (by decide) a

/-- Data in the frame at `o`. -/
theorem frDA (o : Nat) : DataA P (Cfg.fr .edx o) fun L => L.F + BitVec.ofNat 32 o :=
  fun _ _ _ _ hL _ hu => fr_ok hL hu (d := .edx) (by decide) o

/-- `hinit`: each state set by `init` and updated with its padded key. -/
theorem hinit_piece {Φ : Pred P} : Piece P Φ (cfgOf P).hinit (Tt P) := by
  unfold Cfg.hinit
  have hI := (rfcT_of P).padI
  have hO := (rfcT_of P).padO
  rw [ipad32_eq] at hI ⊢
  rw [opad32_eq] at hO ⊢
  exact (initCall_piece (by decide)).seq ((initCall_piece (by decide)).seq ((padBlk_piece _ hI).seq
    ((updCall_piece (by decide) (scrDA 1024) (fun _ hL => padData hL (by decide))
      (updArgs_taint _ _ _ 1024 _ false) (by decide) (by show P.H.B < 2 ^ 32; nums)).seq ((padBlk_piece _ hO).seq
    (updCall_piece (by decide) (scrDA 1024) (fun _ hL => padData hL (by decide))
      (updArgs_taint _ _ _ 1024 _ false) (by decide) (by show P.H.B < 2 ^ 32; nums))))))

/-- `hupd`: the inner state updated with the data. -/
theorem hupd_piece {Φ : Pred P} {dataA : List Instr} {dv : Lay P.I.hashLen → BitVec 32} {len : Nat}
    (hdA : DataA P dataA dv) (hd : ∀ L : Lay P.I.hashLen, L.Ok → DataOk L (dv L) len)
    (ht : TaintOk [.esp] ((cfgOf P).updArgs sInner (cfgOf P).B dataA len)) (hlen : len ≤ 256) :
    Piece P Φ ((cfgOf P).hupd dataA len) (Tt P) := by
  unfold Cfg.hupd
  exact updCall_piece (by decide) hdA (fun L hL => DataOk.upd hL (hd L hL)) ht
    (by show P.H.B < 2 ^ 32; nums) (by omega)

/-- The MAC's copy to the frame. -/
theorem hcopy_piece {Φ : Pred P} {dst : Nat} (hdst : dst + P.H.D ≤ 128)
    (ht : TaintOk [.esp, .edi] (Cfg.copyBytes (cfgOf P).D .edi sTmp .esp dst)) :
    Piece P Φ (.block ((cfgOf P).scrPtr ++ Cfg.copyBytes (cfgOf P).D .edi sTmp .esp dst)) (Tt P) :=
  Piece.scrBlk ht fun L _ _ _ hL hk hc _ => by
    rw [WP.block_append_iff]
    refine WP.mono (scrPtr_ok hL hk.tabL hc) fun w₄ h₄ => ?_
    have hsep : Region.Disjoint ⟨L.scr + BitVec.ofNat 64 1152, P.H.D⟩ ⟨L.B + BitVec.ofNat 64 (76 + dst), P.H.D⟩ :=
      (hL.stk_scr (by nums) (by nums)).symm
    refine WP.mono_syms (copyBytes_ok (src := .edi) (dst := .esp) (S := L.a4) (D := L.F)
      (SA := L.scr + BitVec.ofNat 64 1152) (DA := L.B + BitVec.ofNat 64 (76 + dst))
      (so := 1152) (d := dst) (Q := P.H.D) (by decide) (by decide)
      (fun j hj => by rw [addr_eq (by have := hL.nc; nums), Offset.add_add])
      (fun j hj => by rw [hL.addrF (by nums), Offset.add_add]; congr 2; omega)
      hsep (by nums) (by nums) h₄.val h₄.ctx.esp
      (fun j hj => by rw [Offset.add_add]; exact h₄.ctx.inScr (by nums)) (fun j hj => by
        rw [Offset.add_add]; exact h₄.ctx.inFrW (by omega) (by nums) hL))
      fun w₅ ⟨hrd₅, hwr₅, hg₅, hf₅, _⟩ hsy₅ => ?_
    exact ⟨h₄.ctx.keep hL hrd₅ hwr₅ (hg₅ _ (by decide)) hf₅
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by nums)) hsy₅, trivial⟩

/-- `hfin`: the MAC, for `len` bytes of data, to the frame at `dst`. -/
theorem hfin_piece {Φ : Pred P} {len dst : Nat} (hlen : len ≤ 256) (hdst : dst + P.H.D ≤ 128)
    (ht : TaintOk [.esp, .edi] (Cfg.copyBytes (cfgOf P).D .edi sTmp .esp dst)) :
    Piece P Φ ((cfgOf P).hfin len dst) (Tt P) := by
  unfold Cfg.hfin
  exact (finCall_piece (by decide) (by show P.H.B + len < 2 ^ 32; nums)).seq
    ((updCall_piece (by decide) (scrDA 1152) (fun L hL => tmpData hL) (updArgs_taint _ _ _ 1152 _ false)
      (by show P.H.B < 2 ^ 32; nums) (by show P.H.D < 2 ^ 32; nums)).seq
    ((finCall_piece (by decide) (by show P.H.B + P.H.D < 2 ^ 32; nums)).seq (hcopy_piece hdst ht)))

theorem copyStates_taint (b : Bool) : TaintOk [.esp, .edi] (Cfg.copyStates b) := by
  cases b
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩

/-- HMAC's states saved, or restored. -/
theorem copyStates_piece {Φ : Pred P} (b : Bool) :
    Piece P Φ (.block ((cfgOf P).scrPtr ++ Cfg.copyStates b)) (Tt P) :=
  Piece.scrBlk (copyStates_taint b) fun L _ _ _ hL hk hc _ => by
    rw [WP.block_append_iff]
    refine WP.mono (scrPtr_ok hL hk.tabL hc) fun u h => ?_
    cases b
    · rw [show Cfg.copyStates false = Cfg.copyN 128 .edi 3072 .edi 0 from rfl]
      exact WP.mono (copy_ok hL h.ctx (src := .edi) (S := L.a4) (SA := L.scr + BitVec.ofNat 64 3072) h.val
        (by decide) h.val (so := 3072) (d := 0) (K := 128) (by decide)
        (fun j hj => by rw [addr_eq (by have := hL.nc; omega), Offset.add_add])
        (fun j hj => by rw [Offset.add_add]; exact h.ctx.inScr (by omega))
        (Offset.disjoint _ (by decide) (by decide) (by decide))) fun _ h => ⟨h.1, trivial⟩
    · rw [show Cfg.copyStates true = Cfg.copyN 128 .edi 0 .edi 3072 from rfl]
      exact WP.mono (copy_ok hL h.ctx (src := .edi) (S := L.a4) (SA := L.scr + BitVec.ofNat 64 0) h.val
        (by decide) h.val (so := 0) (d := 3072) (K := 128) (by decide)
        (fun j hj => by rw [addr_eq (by have := hL.nc; omega), Offset.add_add])
        (fun j hj => by rw [Offset.add_add]; exact h.ctx.inScr (by omega))
        (Offset.disjoint _ (by decide) (by decide) (by decide))) fun _ h => ⟨h.1, trivial⟩

section Mac

variable {Φ : Pred P} {dataA : List Instr} {dv : Lay P.I.hashLen → BitVec 32} {len dst : Nat}
  (hdA : DataA P dataA dv) (hd : ∀ L : Lay P.I.hashLen, L.Ok → DataOk L (dv L) len)
  (ht : TaintOk [.esp] ((cfgOf P).updArgs sInner (cfgOf P).B dataA len)) (hlen : len ≤ 256)
  (hdst : dst + P.H.D ≤ 128) (hct : TaintOk [.esp, .edi] (Cfg.copyBytes (cfgOf P).D .edi sTmp .esp dst))
include hdA hd ht hlen hdst hct

theorem hmac_piece : Piece P Φ ((cfgOf P).hmac dataA len dst) (Tt P) :=
  hinit_piece.seq ((hupd_piece hdA hd ht hlen).seq (hfin_piece hlen hdst hct))

theorem hmacS_piece : Piece P Φ ((cfgOf P).hmacS dataA len dst) (Tt P) :=
  hinit_piece.seq ((copyStates_piece true).seq ((hupd_piece hdA hd ht hlen).seq (hfin_piece hlen hdst hct)))

theorem hmacR_piece : Piece P Φ ((cfgOf P).hmacR dataA len dst) (Tt P) :=
  (copyStates_piece false).seq ((hupd_piece hdA hd ht hlen).seq (hfin_piece hlen hdst hct))

end Mac

theorem vDataOk (L : Lay P.I.hashLen) : DataOk L (L.F + BitVec.ofNat 32 64) P.H.D :=
  .inl ⟨64, rfl, by nums⟩

theorem hmacVS_piece {Φ : Pred P} : Piece P Φ (cfgOf P).hmacVS (Tt P) :=
  hmacS_piece (frDA 64) (fun L _ => vDataOk L) (updArgs_taint _ _ _ 64 _ true) (by show P.H.D ≤ 256; nums)
    (by show 64 + P.H.D ≤ 128; nums) (rfcT_of P).hfinCopyV

theorem hmacVR_piece {Φ : Pred P} : Piece P Φ (cfgOf P).hmacVR (Tt P) :=
  hmacR_piece (frDA 64) (fun L _ => vDataOk L) (updArgs_taint _ _ _ 64 _ true) (by show P.H.D ≤ 256; nums)
    (by show 64 + P.H.D ≤ 128; nums) (rfcT_of P).hfinCopyV

/-- `K = HMAC_K(m)`, for the message of `len` bytes at `scratch + 2256`, from
the saved states if `rs`. -/
theorem hmacK_piece {Φ : Pred P} {len : Nat} (hlen : len ≤ 256) (rs : Bool) :
    Piece P Φ ((if rs then (cfgOf P).hmacR else (cfgOf P).hmac) ((cfgOf P).scr .edx sMsg) len fK) (Tt P) := by
  cases rs
  · exact hmac_piece (scrDA 2256) (fun _ _ => .inr ⟨2256, rfl, by omega, by omega⟩)
      (updArgs_taint _ _ _ 2256 _ false) hlen (by show 0 + P.H.D ≤ 128; nums) (rfcT_of P).hfinCopyK
  · exact hmacR_piece (scrDA 2256) (fun _ _ => .inr ⟨2256, rfl, by omega, by omega⟩)
      (updArgs_taint _ _ _ 2256 _ false) hlen (by show 0 + P.H.D ≤ 128; nums) (rfcT_of P).hfinCopyK

/-! ## `K` and `V` from a message -/

/-- `scratch` in `edi` and `d` in `esi`. -/
def PtrsIn (P : RfcHash) : Pred P := fun L _ _ u => u.gpr .edi = L.a4 ∧ u.gpr .esi = L.a1

theorem msgPtrs_piece {Φ : Pred P} : Piece P Φ (.block (cfgOf P).msgPtrs) (PtrsIn P) :=
  Piece.blkS (msgPtrs_taint _) fun _ _ _ _ hL hk hc _ =>
    WP.mono (ptrs_ok hL hk.tabL.cw hk.tabL.ch hc) fun _ ⟨c, _, d, s⟩ => ⟨c, d, s⟩

/-- The message `V ‖ b (‖ d ‖ h)` at `scratch + sMsg`. -/
theorem msg_piece {b : Nat} {full : Bool} {ho : Nat} (hho : full = true → ho = P.hB - 76)
    (ht : TaintOk [.esp, .edi, .esi] (Cfg.msg P.Q P.H.D b full ho)) :
    Piece P (PtrsIn P) (.block (Cfg.msg P.Q P.H.D b full ho)) (Tt P) :=
  Piece.blk [.esp, .edi, .esi] (fun _ _ _ _ _ _ _ c₁ c₂ f₁ f₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact esp_two c₁ c₂
      · exact f₁.1.trans f₂.1.symm
      · exact f₁.2.trans f₂.2.symm) ht
    fun _ _ _ _ hL hk hc hp => WP.mono (msg_ok hL hc hp.1 hp.2 b full ho (D := P.H.D) (Q := P.Q) (by nums)
      (by nums) (by nums) (by nums) (hok_of hk).1 (fun hf => by rw [hho hf]; exact hB_fit (hok_of hk)))
      fun _ h => ⟨h.1, trivial⟩

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)`. -/
theorem rekeyFull_piece {Φ : Pred P} (b : Nat) (hb : b < 2) : Piece P Φ ((cfgOf P).rekeyFull b) (Tt P) := by
  have hlen : P.H.D + 2 * P.Q + 1 ≤ 256 := by nums
  unfold Cfg.rekeyFull
  split
  · next h =>
    subst h
    exact msgPtrs_piece.seq ((msg_piece (fun _ => fHo_eq P) (rfcT_of P).msgF).seq
      ((hmacK_piece (len := P.H.D + 2 * P.Q + 1) hlen false).seq hmacVS_piece))
  · next h =>
    obtain rfl : b = 1 := by omega
    exact msgPtrs_piece.seq ((msg_piece (fun _ => fHo_eq P) (rfcT_of P).msgF₁).seq
      ((hmacK_piece (len := P.H.D + 2 * P.Q + 1) hlen true).seq hmacVS_piece))

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)`. -/
theorem rekey_piece {Φ : Pred P} : Piece P Φ (cfgOf P).rekey (Tt P) := by
  have hlen : P.H.D + 1 ≤ 256 := by nums
  unfold Cfg.rekey
  exact msgPtrs_piece.seq ((msg_piece (fun h => absurd h (by decide)) (rfcT_of P).msgN).seq
    ((hmacK_piece (len := P.H.D + 1) hlen false).seq hmacVS_piece))

/-! ## The candidate -/

/-- `V`'s `D` bytes to `T + k D`. -/
theorem keepV_piece {Φ : Pred P} (hw : P.wide = true) {k : Nat} (hk8 : k < 8) (hkb : k * P.H.D + P.H.D ≤ 128) :
    Piece P Φ (.block ((cfgOf P).keepV k)) (Tt P) :=
  Piece.blkS ((rfcT_of P).keepV k hk8) fun L _ _ _ hL hk hc _ => by
    have he := e68 hk.e_eq hw
    have nB := hL.nB
    have hsep : Region.Disjoint ⟨L.B + BitVec.ofNat 64 140, P.H.D⟩
        ⟨L.B + BitVec.ofNat 64 (76 + (fT + k * (cfgOf P).D)), P.H.D⟩ :=
      Offset.disjoint _ (by simp only [fT, cfgOf]; nums) (by nums) (by simp only [fT, cfgOf]; nums)
    exact WP.mono (copyBF_ok hL hc (src := .esp) (S := L.F) (SA := L.B + BitVec.ofNat 64 140) hc.esp (by decide)
      (so := fV) (d := fT + k * (cfgOf P).D) (Q := P.H.D) (by nums) (by simp only [fT]; omega)
      (by simp only [fT, cfgOf]; rw [he]; nums)
      (fun j hj => by rw [hL.addrF (by simp only [fV]; nums), Offset.add_add, show 76 + (fV + j) = 140 + j by
        simp only [fV]; omega])
      (fun j hj => by rw [Offset.add_add]; exact hc.inFr (by omega) (by nums) hL) hsep)
      fun _ h => ⟨h.1, trivial⟩

/-- The first `k` `V`s of the candidate. -/
theorem candW_piece {Φ : Pred P} (hw : P.wide = true) : ∀ k, k ≤ 8 → k * P.H.D ≤ 128 →
    Piece P Φ ((cfgOf P).candW k) (Tt P)
  | 0, _, _ => by
    rw [Cfg.candW]
    exact Piece.blkS ⟨_, by taint_decide⟩ fun _ _ _ t _ _ hc _ => WP.of_runBlock ⟨t, rfl, hc, trivial⟩
  | k + 1, h8, hk => by
    have hk' : k * P.H.D + P.H.D ≤ 128 := by rw [Nat.succ_mul] at hk; exact hk
    rw [Cfg.candW]
    exact (candW_piece hw k (by omega) (by omega)).seq (hmacVR_piece.seq (keepV_piece hw (by omega) hk'))

/-- If `sh ≠ 0`: `T`'s first `Q` bytes shifted right by `sh` bits. -/
theorem candTop_piece {Φ : Pred P} (hw : P.wide = true) : Piece P Φ (.block (cfgOf P).candTop) (Tt P) := by
  by_cases hsh : P.R.sh = 0
  · have e : (cfgOf P).candTop = [] := by
      simp only [Cfg.candTop, show (cfgOf P).sh = 0 from hsh, ite_true]
    rw [e]
    exact Piece.blkS ⟨_, by taint_decide⟩ fun _ _ _ t _ _ hc _ => WP.of_runBlock ⟨t, rfl, hc, trivial⟩
  · have e : (cfgOf P).candTop = (cfgOf P).scrPtr ++ (cfgOf P).conv fT (cfgOf P).sh := by
      simp only [Cfg.candTop, show (cfgOf P).sh = P.R.sh from rfl, hsh, ite_false]
    rw [e]
    refine Piece.scrBlk ((rfcT_of P).candTop hsh) fun _ _ _ _ hL hk hc _ => ?_
    rw [← e]
    exact WP.mono (candTop_ok hL hk.e_eq hw hk.tabL hsh hc) fun _ h => ⟨h.1, trivial⟩

/-- The candidate: its calls and blocks leak the same in both runs. -/
theorem cand_piece {Φ : Pred P} : Piece P Φ (cfgOf P).cand (Tt P) := by
  cases hw : P.wide
  · simp only [Cfg.cand, cfgOf_wide, hw, Bool.false_eq_true, ite_false]
    exact hmacVR_piece
  · simp only [Cfg.cand, cfgOf_wide, hw, ite_true]
    exact (candW_piece hw _ (rfcT_of P).m8 (m_facts P hw).2).seq (candTop_piece hw)

/-! ## One candidate -/

/-- `core`, in a frame of its arguments, which agree. -/
theorem core_ct {i : Nat} :
    RelCT isa (Two P fun L _ m₀ u => P₁ P L m₀ i u ∧ CoreRegs P L u)
      (.frame (.push [.ebp, .ecx, .edx, .esi, .edi]) (.call (cfgOf P).coreN (cfgOf P).coreC) (.pop .ecx 5))
      fun _ _ => True :=
  two_exists fun e => callWithR_ct (rs := core5) P.R.coreX P.R.coreCT (coreRd P e.1) (coreWr P e.1)
    fun _ _ ⟨hL, hk, _, c₁, c₂, ⟨_, a₁⟩, ⟨_, a₂⟩⟩ => by
      obtain ⟨v₀, v₁, v₂, v₃, v₄⟩ := core_argv hL c₁ a₁ (rd := coreRd P e.1) (wr := coreWr P e.1)
      obtain ⟨w₀, w₁, w₂, w₃, w₄⟩ := core_argv hL c₂ a₂ (rd := coreRd P e.1) (wr := coreWr P e.1)
      refine ⟨core_callPre hL hk c₁ a₁, core_callPre hL hk c₂ a₂, esp_two c₁ c₂,
        by rw [State.withRegions_gpr, State.withRegions_gpr, core_esp c₁, core_esp c₂],
        by rw [v₀, w₀], by rw [v₁, w₁], by rw [v₂, w₂], by rw [v₃, w₃], by rw [v₄, w₄], ?_⟩
      intro c hc
      rw [← hk.2.2.2.1] at hc
      rw [core_syms c₁ hc, core_syms c₂ hc]

/-- Whether to go on agrees: in both runs, iff the candidate is before the one it stops at. -/
theorem dec_two {L : Lay P.I.hashLen} {m₁ m₂ : Mem} {i : Nat} (hx : exitAt P L m₁ = exitAt P L m₂) {u₁ u₂ : State}
    (h₁ : Mid P L m₁ i u₁) (h₂ : Mid P L m₂ i u₂) : isa.eval .ne u₁ = isa.eval .ne u₂ := by
  rw [h₁.dec, h₂.dec]
  refine congrArg some (decide_eq_decide.mpr ?_)
  rw [go_iff h₁.lt h₁.fails, go_iff h₂.lt h₂.fails, hx]

/-- What one candidate leaves: the end, or the next candidate. -/
def After (P : RfcHash) (i : Nat) (L : Lay P.I.hashLen) (_ : Reg → BitVec 32) (m₀ : Mem) (t : State) : Prop :=
  (isa.eval .ne t = some false ∧ Exit P L m₀ i t) ∨ (isa.eval .ne t = some true ∧ LoopInv P L m₀ (i + 1) t)

theorem tryOne_trace {i : Nat} :
    RelCT isa (Two P fun L _ m₀ t => LoopInv P L m₀ i t) (cfgOf P).tryOne fun _ _ => True := by
  refine (two_wp (Ψ := fun L _ m₀ u => P₁ P L m₀ i u) ((cand_piece (Φ := Tt P)).rel fun _ _ _ _ _ => trivial)
    fun _ _ _ _ hL hk hc hi => try₁_ok hL hk hc hi).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ u => P₁ P L m₀ i u ∧ CoreRegs P L u)
    (two_blk [.esp] espOnly (rfcT_of P).coreArgs) fun _ _ _ _ hL hk hc hi => try₂_ok hL hk hc hi).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ u => P₃ P L m₀ i u) core_ct fun _ _ _ _ hL hk hc hi =>
    try₃_ok hL hk hc hi.1 hi.2).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ u => Mid P L m₀ i u) (two_blk [.esp] espOnly ⟨_, by taint_decide⟩)
    fun _ _ _ _ hL hk hc hi => try₄_ok hL hk hc hi).seq ?_
  refine VG.RelCT.ite (fun _ _ ⟨_, _, _, hx, _, _, f₁, f₂⟩ => dec_two hx f₁ f₂) ?_ ?_
  · exact (rekey_piece.ct.seq (two_blk [.esp] espOnly ⟨_, by taint_decide⟩)).mono (fun _ _ h => h.1)
      fun _ _ h => h
  · exact (two_blk [.esp] espOnly ⟨_, by taint_decide⟩).mono (fun _ _ h => h.1) fun _ _ h => h

/-- One candidate: both runs end, or both go on. -/
theorem tryOne_ct {i : Nat} :
    RelCT isa (Two P fun L _ m₀ t => LoopInv P L m₀ i t) (cfgOf P).tryOne fun s₁ s₂ =>
      isa.eval .ne s₁ = isa.eval .ne s₂ ∧
        (isa.eval .ne s₁ = some false → Two P (fun L _ m₀ t => Exit P L m₀ i t) s₁ s₂) ∧
        (isa.eval .ne s₁ = some true → Two P (fun L _ m₀ t => LoopInv P L m₀ (i + 1) t) s₁ s₂) := by
  refine (two_wp (Ψ := After P i) tryOne_trace fun _ _ _ _ hL hk hc hi => tryOne_ok hL hk hc hi).mono
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
    RelCT isa (Two P fun L _ m₀ t => LoopInv P L m₀ 0 t) (.loop (cfgOf P).tryOne .ne)
      (Two P fun L _ m₀ t => ∃ i, Exit P L m₀ i t) := by
  have h : RelCT isa (Two P fun L _ m₀ t => LoopInv P L m₀ (P.I.tries - P.I.tries) t) (.loop (cfgOf P).tryOne .ne)
      (Two P fun L _ m₀ t => ∃ i, Exit P L m₀ i t) :=
    VG.RelCT.loop (M := isa) (fun n => Two P fun L _ m₀ t => LoopInv P L m₀ (P.I.tries - n) t)
      (fun n => tryOne_ct.mono (fun _ _ h => h) fun _ _ ⟨he, hf, ht⟩ =>
        ⟨he, fun h => (hf h).mono fun _ _ _ _ hx => ⟨_, hx⟩, fun h => by
          obtain ⟨e, hL, hq, hx, c₁, c₂, f₁, f₂⟩ := ht h
          have hn := next_n f₁.lt
          refine ⟨P.I.tries - (P.I.tries - n + 1), hn.1, e, hL, hq, hx, c₁, c₂, ?_, ?_⟩ <;> rwa [hn.2]⟩)
      P.I.tries
  rwa [Nat.sub_self] at h

/-! ## The frame's body -/

/-- The count's initial store, for any count: the analysis does not read
immediates (`check_erase`), so it is that of one count's. -/
theorem initCnt_blk (c : Cfg) : TaintOk [.esp] c.initCnt :=
  taintOk_erase (is₀ := [.mov .eax (.imm 0), .store (stk fCnt) .eax]) ⟨_, by taint_decide⟩ rfl

/-- `digest` in `esi`, and, if the hash is shorter than the scalars, `scratch` in `edi`. -/
def DgIn (P : RfcHash) {dn : Nat} (L : Lay dn) (_ : Reg → BitVec 32) (_ : Mem) (u : State) : Prop :=
  u.gpr .esi = L.a2 ∧ (P.wide = true → u.gpr .edi = L.a4)

/-- Unless the hash is shorter, `bits2octets` is the curve's. -/
theorem reduce_eq (hw : P.wide = false) : (cfgOf P).reduce = (cfgC P.R.E P.R.hHigh).reduce := by
  have h₁ : (cfgC P.R.E P.R.hHigh).wide = false := by
    show decide (64 < P.Q) = false
    have := P.sizes
    have := (P.sizesA hw).2.2
    simp only [decide_eq_false_iff_not]; nums
  have h₂ : (cfgOf P).fHo = (cfgC P.R.E P.R.hHigh).fHo := by
    simp only [Cfg.fHo, cfgOf_wide, hw, h₁]; rfl
  have h₃ : (cfgOf P).selWord = (cfgC P.R.E P.R.hHigh).selWord := funext fun j => by
    simp only [Cfg.selWord, h₂]; rfl
  have h₄ : (cfgOf P).subWord = (cfgC P.R.E P.R.hHigh).subWord := funext fun j => by
    simp only [Cfg.subWord, h₂]; rfl
  simp only [Cfg.reduce, h₃, h₄]
  rfl

theorem prep_ct : RelCT isa (Two P (DgIn P)) (.block (cfgOf P).prep) fun _ _ => True := by
  cases hw : P.wide
  · have e : (cfgOf P).prep = (cfgC P.R.E P.R.hHigh).reduce ++ Cfg.initKV := by
      simp only [Cfg.prep, cfgOf_wide, hw, Bool.false_eq_true, ite_false, reduce_eq hw]
    rw [e]
    exact two_blk [.esp, .esi] (fun _ _ _ _ _ _ _ c₁ c₂ f₁ f₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact esp_two c₁ c₂
      · exact f₁.1.trans f₂.1.symm) (P.R.reduceT (P.curveA hw))
  · exact two_blk [.esp, .esi, .edi] (fun _ _ _ _ _ _ _ c₁ c₂ f₁ f₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact esp_two c₁ c₂
      · exact f₁.1.trans f₂.1.symm
      · exact (f₁.2 hw).trans (f₂.2 hw).symm) ((rfcT_of P).prepW hw)

/-- The body after our caller's registers are saved and `esi` (and `edi`) set. -/
theorem rest_ct :
    RelCT isa (Two P (DgIn P)) (.seq (.block (cfgOf P).prep)
      (.seq ((cfgOf P).rekeyFull 0) (.seq ((cfgOf P).rekeyFull 1) (.seq (.block (cfgOf P).initCnt)
      (.seq (.loop (cfgOf P).tryOne .ne) (.block (cfgOf P).wipe)))))) fun _ _ => True := by
  refine (two_wp (Ψ := fun L _ m₀ t => QB P L m₀ t) prep_ct fun _ _ _ _ hL hk hc h =>
    stageB_ok (P := P) hL hk hc h.1 h.2).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ t => QC P L m₀ t) ((rekeyFull_piece 0 (by decide)).rel fun _ _ _ _ _ => trivial)
    fun _ _ _ _ hL hk hc h => stageC_ok (P := P) hL hk hc h).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ t => QD P L m₀ t) ((rekeyFull_piece 1 (by decide)).rel fun _ _ _ _ _ => trivial)
    fun _ _ _ _ hL hk hc h => stageD_ok (P := P) hL hk hc h).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ t => LoopInv P L m₀ 0 t) (two_blk [.esp] espOnly (initCnt_blk _))
    fun _ _ _ _ hL hk hc h => stageE_ok (P := P) hL hk hc h).seq ?_
  exact loop_ct.seq (two_blk [.esp] espOnly (rfcT_of P).wipe)

/-! ## The whole function -/

/-- Two runs from states that satisfy the precondition and agree on public
data, after the frame's allocation. -/
def Entered (P : RfcHash) (ns : List String) (a b : State) : Prop :=
  ∃ s₁ s₂, ((rfcP P ns).pre s₁ ∧ (rfcP P ns).pre s₂ ∧ (rfcP P ns).pub s₁ s₂) ∧
    a = allocState (196 + 4 * P.e) s₁ ∧ b = allocState (196 + 4 * P.e) s₂

theorem start_blk {ns : List String} :
    RelCT isa (Entered P ns) (.block (save ++ (cfgOf P).digestPtr)) fun _ _ => True :=
  let ⟨_, h⟩ := (rfcT_of P).digestPtr
  VG.RelCT.taint (A := taint) (τr [.esp]) (fun _ _ ⟨s₁, s₂, ⟨_, _, hsp, _⟩, ea, eb⟩ => agree_regs fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr ea eb
    rw [allocState_esp, allocState_esp, hsp]) h

/-- Our caller's registers saved, and `digest` in `esi` (and `scratch` in
`edi`): the runs are related by `Two`, with the layout of the arguments,
which agree, and the same number of candidates. -/
theorem start_ct {ns : List String} (hns : ∀ n ∈ [P.H.initN, P.H.updN, P.H.finN], n ∈ ns) :
    RelCT isa (Entered P ns) (.block (save ++ (cfgOf P).digestPtr)) (Two P (DgIn P)) := by
  intro a b t₁ t₂ a' b' hp e₁ e₂
  obtain ⟨ht, -⟩ := start_blk _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨s₁, s₂, ⟨p₁, p₂, hsp, hdi, hsi, hdx, h3, hcx, h5, hres, hsy, hns'⟩, rfl, rfl⟩ := hp
  have hw : ∀ s, (rfcP P ns).pre s → WP isa (.block (save ++ (cfgOf P).digestPtr)) (allocState (196 + 4 * P.e) s)
      fun u => Ctx (layP P s) s.gpr s.mem u ∧ DgIn P (layP P s) s.gpr s.mem u := fun s h =>
    save_ok h fun _ hc _ => WP.mono (digestPtr_ok (lay_ok h) (c := cfgOf P) rfl rfl hc) fun _ ⟨c, a, d⟩ => ⟨c, a, d⟩
  obtain ⟨_, u₁, x₁, y₁⟩ := hw s₁ p₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw s₂ p₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  have hl : layP P s₂ = layP P s₁ := by
    have hs : (fun n => if n ∈ P.R.E.combConsts.map Prod.fst then s₂.syms n else 0) =
        (fun n => if n ∈ P.R.E.combConsts.map Prod.fst then s₁.syms n else 0) := by
      funext n
      split
      · rename_i hn
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
        exact (hsy c hc).symm
      · rfl
    have hf : (fun n => if n ∈ [P.H.initN, P.H.updN, P.H.finN] then s₂.syms n else 0) =
        (fun n => if n ∈ [P.H.initN, P.H.updN, P.H.finN] then s₁.syms n else 0) := by
      funext n
      split
      · rename_i hn
        exact (hns' n (hns n hn)).symm
      · rfl
    simp only [layP, lay, hsp, hdi, hsi, hdx, h3, hcx, h5, hs, hf]
  have hr : (result P.I s₁.mem (layP P s₁).d (layP P s₁).dg).2 = (result P.I s₂.mem (layP P s₁).d (layP P s₁).dg).2 := by
    show (result P.I s₁.mem ((arg s₁ 1).setWidth 64) ((arg s₁ 2).setWidth 64)).2 =
      (result P.I s₂.mem ((arg s₁ 1).setWidth 64) ((arg s₁ 2).setWidth 64)).2
    rw [hres, hsi, hdx]
  rw [hl] at y₂
  exact ⟨ht, ⟨layP P s₁, s₁.gpr, s₂.gpr, s₁.mem, s₂.mem⟩, lay_ok p₁, coreOk_lay P s₁,
    congrArg (fun x => if x = 0 then P.I.tries - 1 else x - 1) hr, y₁.1, y₂.1, y₁.2, y₂.2⟩

/-- Runs whose public data agree (with the addresses of the hash function's
functions among `ns`) have the same layout, and stop at the same candidate. -/
theorem sign_ct {ns : List String} (hns : ∀ n ∈ [P.H.initN, P.H.updN, P.H.finN], n ∈ ns) :
    ConstantTime isa (rfcP P ns).pre (rfcP P ns).pub (cfgOf P).sign :=
  VG.RelCT.constantTime (Q := fun _ _ => True) (alloc_ct ((start_ct hns).seq rest_ct |>.mono
    (fun _ _ ⟨s₁, s₂, h, ea, eb⟩ => ⟨s₁, s₂, h, ea, eb⟩) fun _ _ h => h))

end VG.Proof.Ecdsa.Rfc6979.X86

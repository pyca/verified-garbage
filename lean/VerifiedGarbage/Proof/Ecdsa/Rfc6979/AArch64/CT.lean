module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Correct
public import VerifiedGarbage.Proof.Framework.AArch64.TaintErase
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Correct
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintErase
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.ICall
meta import VerifiedGarbage.Proof.Framework.ICall
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Msg
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Msg
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Regs
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Regs
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Copy
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Copy
import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Calls
meta import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Calls
import VerifiedGarbage.Proof.RsaOaep.AArch64.Loops
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.Loops

/-!
# Deterministic ECDSA on AArch64: constant time, up to the number of candidates

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/CT.lean`): two runs whose public
data agree have the same layout, and stop at the same candidate (`exitAt`,
from the contract's leakage: the number of candidates RFC 6979 tries).
Between the frames' pushes and pops they are related by `Two`: both satisfy
`Ctx` with that layout (and `Φ`, what the next piece needs). The blocks
address only the stack and the buffers, from registers that agree (the
taint analysis, of the blocks whose contents depend on the curve: `RfcT`,
each curve's `RfcCurve.blk`), or, for the byte loops, from registers both
runs set alike (`T`'s length, `D`); an indirect call reaches, through the
table, whose address the frame holds, the same function in both runs
(`tcall_piece`); each call is of constant-time code whose public data agree
(`RelCT.callEx`); and the loops' branches agree: the candidate's, since both
runs' `T` grows by `D` bytes a block, and the candidates', since in both
runs it goes on after candidate `i` iff `i` is before the candidate it stops
at (`go_iff`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.Rfc6979.AArch64
open VG.Proof.RsaOaep.AArch64 (eval_nonzero)

/-- What each of two runs has, between the frames' pushes and pops. -/
abbrev Env (P : RfcHash) := Lay P.I.hashLen P.R.E × (Reg → BitVec 64) × (Reg → BitVec 64) × Mem × Mem

/-- Two runs with the same layout that stop at the same candidate, each
satisfying `Ctx` and `Φ`. -/
def Two (P : RfcHash) (Φ : Lay P.I.hashLen P.R.E → Mem → State → Prop) (a b : State) : Prop :=
  ∃ e : Env P, e.1.Ok ∧ HOk P e.1 ∧ exitAt P e.1 e.2.2.2.1 = exitAt P e.1 e.2.2.2.2 ∧ Ctx e.1 e.2.1 e.2.2.2.1 a ∧
    Ctx e.1 e.2.2.1 e.2.2.2.2 b ∧ Φ e.1 e.2.2.2.1 a ∧ Φ e.1 e.2.2.2.2 b

variable {P : RfcHash}

theorem Two.mono {Φ Ψ : Lay P.I.hashLen P.R.E → Mem → State → Prop} (h : ∀ L m₀ t, Φ L m₀ t → Ψ L m₀ t)
    {a b : State} (ht : Two P Φ a b) : Two P Ψ a b :=
  let ⟨e, hL, hq, hx, c₁, c₂, f₁, f₂⟩ := ht
  ⟨e, hL, hq, hx, c₁, c₂, h _ _ _ f₁, h _ _ _ f₂⟩

/-- Code whose runs leak the same, and which keeps `Ctx` and establishes `Ψ`. -/
theorem two_wp {c : Prog isa} {Φ Ψ : Lay P.I.hashLen P.R.E → Mem → State → Prop}
    (hct : RelCT isa (Two P Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay P.I.hashLen P.R.E) g m₀ (t : State), L.Ok → HOk P L → Ctx L g m₀ t → Φ L m₀ t →
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

/-- Code whose addresses depend only on `sp` and the registers `rs`, which agree. -/
theorem two_prog {c : Prog isa} {Φ : Lay P.I.hashLen P.R.E → Mem → State → Prop} (rs : List Reg)
    (hrs : ∀ (L : Lay P.I.hashLen P.R.E) (t₁ t₂ : State) g₁ g₂ m₁ m₂, Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ →
      Φ L m₁ t₁ → Φ L m₂ t₂ → ∀ r ∈ rs, t₁.gpr r = t₂.gpr r)
    (h : ∃ hc, (taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa (Two P Φ) c fun _ _ => True :=
  let ⟨_, h⟩ := h
  RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun _ _ ⟨_, _, _, _, c₁, c₂, f₁, f₂⟩ => ⟨sp_two c₁ c₂, fun r hr =>
      hrs _ _ _ _ _ _ _ c₁ c₂ f₁ f₂ r (Taint.mem_ofRegs.mp hr)⟩) h

/-- A block whose addresses depend only on `sp` and the registers `rs`, which agree. -/
theorem two_blk {is : List Instr} {Φ : Lay P.I.hashLen P.R.E → Mem → State → Prop} (rs : List Reg)
    (hrs : ∀ (L : Lay P.I.hashLen P.R.E) (t₁ t₂ : State) g₁ g₂ m₁ m₂, Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ →
      Φ L m₁ t₁ → Φ L m₂ t₂ → ∀ r ∈ rs, t₁.gpr r = t₂.gpr r)
    (h : TaintOk rs is) : RelCT isa (Two P Φ) (.block is) fun _ _ => True :=
  two_prog rs hrs h

theorem spOnly {Φ : Lay P.I.hashLen P.R.E → Mem → State → Prop} :
    ∀ (L : Lay P.I.hashLen P.R.E) (t₁ t₂ : State) g₁ g₂ m₁ m₂,
      Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ → Φ L m₁ t₁ → Φ L m₂ t₂ → ∀ r ∈ ([] : List Reg), t₁.gpr r = t₂.gpr r :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hr => absurd hr List.not_mem_nil

/-- The taint check of a block is that of the block with the immediates of
its `movz`s zeroed (`Taint.check_eraseImm`). -/
theorem taintOk_erase {rs : List Reg} {is is₀ : List Instr} (h : TaintOk rs is₀)
    (he : is.map Instr.eraseImm = is₀) : TaintOk rs is := by
  obtain ⟨hc, hs⟩ := h
  exact ⟨hc, Taint.isSome_check_of_eraseImm (c := .block is) (by simp only [Code.eraseImm, he]) hs⟩

/-! ## Pieces: related in two runs, and keeping `Ctx` in each -/

/-- What one run's piece needs and gives. -/
abbrev Pr (P : RfcHash) := Lay P.I.hashLen P.R.E → Mem → State → Prop

/-- Nothing. -/
abbrev Tt (P : RfcHash) : Pr P := fun _ _ _ => True

/-- Code that, from `Φ`, leaks the same in two runs and gives `Ψ`, keeping
`Ctx`, in each. -/
structure Piece (P : RfcHash) (Φ : Pr P) (c : Prog isa) (Ψ : Pr P) : Prop where
  ct : RelCT isa (Two P Φ) c (Two P Ψ)
  wp : ∀ (L : Lay P.I.hashLen P.R.E) g m₀ (t : State), L.Ok → HOk P L → Ctx L g m₀ t → Φ L m₀ t →
    WP isa c t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t'

namespace Piece

variable {Φ Ψ Χ : Pr P} {a b c : Prog isa}

theorem of (hct : RelCT isa (Two P Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay P.I.hashLen P.R.E) g m₀ (t : State), L.Ok → HOk P L → Ctx L g m₀ t → Φ L m₀ t →
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
    (hw : ∀ (L : Lay P.I.hashLen P.R.E) g m₀ (t : State), L.Ok → HOk P L → Ctx L g m₀ t → Φ L m₀ t →
      WP isa (.block is) t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t') : Piece P Φ (.block is) Ψ :=
  Piece.of (two_blk rs hrs ht) hw

/-- A block whose addresses depend only on `sp`. -/
theorem Piece.blkS {is : List Instr} {Φ Ψ : Pr P} (ht : TaintOk [] is)
    (hw : ∀ (L : Lay P.I.hashLen P.R.E) g m₀ (t : State), L.Ok → HOk P L → Ctx L g m₀ t → Φ L m₀ t →
      WP isa (.block is) t fun t' => Ctx L g m₀ t' ∧ Ψ L m₀ t') : Piece P Φ (.block is) Ψ :=
  Piece.blk [] spOnly ht hw

/-- The blocks of the curve. -/
theorem rT (P : RfcHash) : RfcT (cfgC P.R.E P.R.big P.R.sh) := P.R.blk

/-! ## The indirect calls -/

variable {L : Lay P.I.hashLen P.R.E} {g : Reg → BitVec 64} {m₀ : Mem}

/-- The table's word `j`, to `x16` from the table's address in it. -/
theorem ldTab_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (h16 : t.gpr .x16 = L.tab) {j : Nat}
    (hj : 8 * j + 8 ≤ 48) :
    WP isa (.block [.ldr .x .x16 .x16 (8 * j)]) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .x16 = m₀.readW (L.tab + BitVec.ofNat 64 (8 * j)) 64 ∧ (∀ r, r ≠ .x16 → t'.gpr r = t.gpr r) ∧
      t'.syms = t.syms := by
  have ht := hc.inTab hL (o := 8 * j) hj
  have hj' : 8 * j < 32768 := by omega
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, Nat.mul_mod_right, hj', and_self,
    ite_true, Option.bind_some, State.load, Size.bits, BitVec.setWidth_eq, h16, ht, Option.map_some,
    read8, hc.tab_word hL hj, Option.some.injEq, exists_eq_left']
  exact ⟨hc.set hL (d := .x16) (by decide) rfl rfl rfl rfl (fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr) rfl,
    rfl, by rw [RegUpd.gpr_write_self]; exact BitVec.setWidth_eq _, fun r hr => RegUpd.gpr_write_of_ne _ _ _ hr,
    rfl⟩

/-- What an indirect call of `n` needs of the table in each run: its word
`j` (on entry) is `n`'s address, which is the layout's, and of `ts` an
indirect call reaches `n`'s `c`. -/
def TabFn (P : RfcHash) (j : Nat) (n : String) (c : Prog isa) (ts : List (String × Prog isa)) : Prop :=
  ∀ (L : Lay P.I.hashLen P.R.E) g m₀ (t : State), L.Ok → HOk P L → Ctx L g m₀ t →
    m₀.readW (L.tab + BitVec.ofNat 64 (8 * j)) 64 = t.syms n ∧
      ts.find? (fun q => t.syms q.1 == t.syms n) = some (n, c) ∧ t.syms n = L.fa n

theorem tfn_init : TabFn P 0 P.H.hmacInitN P.H.hmacInit P.f.init := fun L _ _ _ _ hk hc => by
  have hok := hc.tabOk; have htm := hc.tabMem; have hf := hc.fsy
  rw [hk.2.1, hk.2.2] at hok; rw [hk.2.1] at htm hf
  exact ⟨htm.1, hok.i, hf _ (by simp)⟩

theorem tfn_upd : TabFn P 1 P.H.updN P.H.updC P.f.upd := fun L _ _ _ _ hk hc => by
  have hok := hc.tabOk; have htm := hc.tabMem; have hf := hc.fsy
  rw [hk.2.1, hk.2.2] at hok; rw [hk.2.1] at htm hf
  exact ⟨htm.2.1, hok.u, hf _ (by simp)⟩

theorem tfn_fin : TabFn P 2 P.H.hmacFinN P.H.hmacFin P.f.fin := fun L _ _ _ _ hk hc => by
  have hok := hc.tabOk; have htm := hc.tabMem; have hf := hc.fsy
  rw [hk.2.1, hk.2.2] at hok; rw [hk.2.1] at htm hf
  exact ⟨htm.2.2, hok.f, hf _ (by simp)⟩

/-- What only `x16` changing keeps. -/
def R16 (Φ : Pr P) : Prop :=
  ∀ L m₀ (t u : State), Φ L m₀ t → (∀ r, r ≠ .x16 → u.gpr r = t.gpr r) → u.mem = t.mem → u.syms = t.syms →
    Φ L m₀ u

theorem tblk1_taint : TaintOk [] [.ldrSp .x16 fTab] := ⟨_, by taint_decide⟩

/-- The indirect call of the table's function `j`: in both runs of the same
function, `n`'s (the table's word `j` holds the layout's address of `n`). -/
theorem tcall_piece {Φ Ψ : Pr P} {j : Nat} (hj : 8 * j + 8 ≤ 48) {n : String} {c : Prog isa}
    {ts : List (String × Prog isa)} (hn : TabFn P j n c ts) (hΦ : R16 Φ)
    (ht : TaintOk [.x16] [.ldr .x .x16 .x16 (8 * j)]) (hcall : Piece P Φ (.call n c) Ψ) :
    Piece P Φ (Cfg.tcall j ts) Ψ := by
  refine ⟨?_, fun L g m₀ t hL hk hc hφ => ?_⟩
  · unfold Cfg.tcall
    rw [show ([.ldrSp .x16 fTab, .ldr .x .x16 .x16 (8 * j)] : List Instr) =
      [.ldrSp .x16 fTab] ++ [.ldr .x .x16 .x16 (8 * j)] from rfl]
    have s₁ : Piece P Φ (.block [.ldrSp .x16 fTab]) fun L m₀ u => Φ L m₀ u ∧ u.gpr .x16 = L.tab :=
      Piece.blkS tblk1_taint fun L g m₀ t hL hk hc hφ => by
        have he := L.he
        exact WP.mono_syms (ldF_ok hL hc (d := .x16) (by decide) (o := fTab) (by simp only [fTab, extra]; omega) rfl)
          fun u h hs => ⟨h.ctx, hΦ _ _ _ _ hφ (fun r hr => h.keep r hr) h.mem hs, by
            rw [h.val, show 16 + fTab = 232 + 8 * L.e by simp only [fTab, extra]; omega]; exact hc.pTab⟩
    have s₂ : Piece P (fun L m₀ u => Φ L m₀ u ∧ u.gpr .x16 = L.tab) (.block [.ldr .x .x16 .x16 (8 * j)])
        fun L m₀ u => Φ L m₀ u ∧ u.gpr .x16 = L.fa n ∧ u.syms n = L.fa n ∧
          ts.find? (fun q => u.syms q.1 == u.syms n) = some (n, c) :=
      Piece.blk [.x16] (fun _ _ _ _ _ _ _ _ _ f₁ f₂ r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact f₁.2.trans f₂.2.symm) ht
        fun L g m₀ t hL hk hc ⟨hφ, h16⟩ => WP.mono (ldTab_ok hL hc h16 hj) fun u ⟨hc', hm, h16', hr, hs⟩ => by
          obtain ⟨hw, hf, hfa⟩ := hn L g m₀ t hL hk hc
          exact ⟨hc', hΦ _ _ _ _ hφ hr hm hs, by rw [h16', hw, hfa], by rw [hs, hfa], by rw [hs]; exact hf⟩
    refine (RelCT.block_append (s₁.ct.seq s₂.ct)).seq ?_
    cases ts with
    | nil => exact RelCT.of_false fun _ _ ⟨_, _, _, _, _, _, f₁, _⟩ => by simp at f₁
    | cons q ts =>
      exact RelCT.icalls_of_call (hcall.ct.mono (fun _ _ => Two.mono fun _ _ _ h => h.1) fun _ _ h => h)
        fun s₁ s₂ ⟨e, _, _, _, _, _, f₁, f₂⟩ => ⟨e.1.fa n, by simp only [icall, f₁.2.1],
          by simp only [icall, f₂.2.1],
          by show (q :: ts).find? (fun p => isa.fnAddr s₁ p.1 == e.1.fa n) = _
             simp only [isa]; rw [← f₁.2.2.1]; exact f₁.2.2.2,
          by show (q :: ts).find? (fun p => isa.fnAddr s₂ p.1 == e.1.fa n) = _
             simp only [isa]; rw [← f₂.2.2.1]; exact f₂.2.2.2, rfl⟩
  · obtain ⟨hw, hf, -⟩ := hn L g m₀ t hL hk hc
    exact tcall_ok hL hc hj hw hf fun t' hc' hm hr hs =>
      hcall.wp L g m₀ t' hL hk hc' (hΦ _ _ _ _ hφ hr hm hs)

/-! ## HMAC's calls -/

/-- HMAC's `init`'s arguments. -/
def IA (P : RfcHash) : Pr P := fun L _ u =>
  u.gpr .x0 = L.scr + BitVec.ofNat 64 0 ∧ u.gpr .x1 = L.scr + BitVec.ofNat 64 192 ∧
    u.gpr .x2 = L.B + BitVec.ofNat 64 16 ∧ u.gpr .x3 = BitVec.ofNat 64 P.H.D ∧
    u.gpr .x4 = L.scr + BitVec.ofNat 64 384

/-- The streaming `update`'s arguments: the inner state holding `cnt`
bytes, the `len` bytes at `da`, and the working space. -/
def UA (P : RfcHash) (cnt : Nat) (da : Lay P.I.hashLen P.R.E → Addr) (len : Nat) : Pr P := fun L _ u =>
  u.gpr .x0 = L.scr + BitVec.ofNat 64 0 ∧ u.gpr .x1 = BitVec.ofNat 64 cnt ∧ u.gpr .x2 = da L ∧
    u.gpr .x3 = BitVec.ofNat 64 len ∧ u.gpr .x4 = L.scr + BitVec.ofNat 64 384

/-- HMAC's `finalize`'s arguments: the states, the `cnt` bytes the inner one
holds, the MAC's place in the frame at `dst`, and the working space. -/
def FA (P : RfcHash) (cnt dst : Nat) : Pr P := fun L _ u =>
  u.gpr .x0 = L.scr + BitVec.ofNat 64 0 ∧ u.gpr .x1 = L.scr + BitVec.ofNat 64 192 ∧
    u.gpr .x2 = BitVec.ofNat 64 cnt ∧ u.gpr .x3 = L.B + BitVec.ofNat 64 (16 + dst) ∧
    u.gpr .x4 = L.scr + BitVec.ofNat 64 384

theorem ce_sp_two {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 64}
    {m₁ m₂ : Mem} (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) (rd₁ wr₁ rd₂ wr₂ : List Region) :
    (t₁.callEntry.withRegions rd₁ wr₁).sp = (t₂.callEntry.withRegions rd₂ wr₂).sp := by
  rw [State.withRegions_sp, State.withRegions_sp, State.callEntry_sp, State.callEntry_sp, sp_two c₁ c₂]

theorem ce_two {t₁ t₂ : State} {r : Reg} (hr : r ∉ linkRegs) {x : BitVec 64} (h₁ : t₁.gpr r = x)
    (h₂ : t₂.gpr r = x) (rd₁ wr₁ rd₂ wr₂ : List Region) :
    (t₁.callEntry.withRegions rd₁ wr₁).gpr r = (t₂.callEntry.withRegions rd₂ wr₂).gpr r := by
  rw [ce_gpr _ _ _ hr, ce_gpr _ _ _ hr, h₁, h₂]

theorem scr_sub {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {r : Region}
    (h : Region.Sub r ⟨L.scr, 2256⟩) : Safe L r :=
  .inr (.inl (sub_trans h (Region.sub_prefix (by omega))))

theorem hinit_piece : Piece P (IA P) (.call P.H.hmacInitN P.H.hmacInit) (Tt P) := by
  refine Piece.of (AArch64.RelCT.callEx P.hI.1 P.hI.2.1 fun _ _ ⟨⟨L, _, _, _, _⟩, hL, _, _, c₁, c₂, a₁, a₂⟩ => by
    obtain ⟨d₁, s₁, x₁, k₁, r₁⟩ := a₁
    obtain ⟨d₂, s₂, x₂, k₂, r₂⟩ := a₂
    have A₁ := initA (P := P) hL c₁ d₁ s₁ x₁ k₁ r₁
    have A₂ := initA (P := P) hL c₂ d₂ s₂ x₂ k₂ r₂
    exact ⟨_, _, _, _, Pbkdf2.Md.AArch64.Pbk.InitArgs.pre P.ok A₁, Pbkdf2.Md.AArch64.Pbk.InitArgs.pre P.ok A₂,
      ⟨ce_two (by decide) d₁ d₂ _ _ _ _, ce_two (by decide) s₁ s₂ _ _ _ _, ce_two (by decide) x₁ x₂ _ _ _ _,
        ce_two (by decide) k₁ k₂ _ _ _ _, ce_two (by decide) r₁ r₂ _ _ _ _, ce_sp_two c₁ c₂ _ _ _ _⟩,
      Pbkdf2.Md.AArch64.Pbk.covers_app A₁.cr A₁.cw, A₁.cw, Pbkdf2.Md.AArch64.Pbk.covers_app A₂.cr A₂.cw, A₂.cw⟩)
    fun L g m₀ u hL _ hc a => ?_
  obtain ⟨d, s, x, k, r⟩ := a
  refine Pbkdf2.Md.AArch64.Pbk.hinit_call P.ok P.hI P.hId (initA (P := P) hL hc d s x k r)
    fun u' ha _ _ => ⟨hc.after hL ha fun r hr => scr_sub ?_, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> exact scr_work (by anums)

theorem upd_piece {cnt : Nat} {da : Lay P.I.hashLen P.R.E → Addr} {len : Nat}
    (hd : ∀ L : Lay P.I.hashLen P.R.E, L.Ok → DataOk L (da L) len) (hlen : len ≤ 256) :
    Piece P (UA P cnt da len) (.call P.H.updN P.H.updC) (Tt P) := by
  refine Piece.of (AArch64.RelCT.callEx P.ok.stream.upd.1 P.ok.stream.upd.2.1
    fun _ _ ⟨⟨L, _, _, _, _⟩, hL, _, _, c₁, c₂, a₁, a₂⟩ => by
      obtain ⟨d₁, s₁, x₁, k₁, r₁⟩ := a₁
      obtain ⟨d₂, s₂, x₂, k₂, r₂⟩ := a₂
      have A₁ := updA (P := P) hL c₁ (hd L hL) hlen d₁ x₁ k₁ r₁
      have A₂ := updA (P := P) hL c₂ (hd L hL) hlen d₂ x₂ k₂ r₂
      exact ⟨_, _, _, _, Pbkdf2.Md.AArch64.Calls.UpdArgs.pre P.ok.stream A₁,
        Pbkdf2.Md.AArch64.Calls.UpdArgs.pre P.ok.stream A₂,
        ⟨ce_two (by decide) d₁ d₂ _ _ _ _, ce_two (by decide) s₁ s₂ _ _ _ _, ce_two (by decide) x₁ x₂ _ _ _ _,
          ce_two (by decide) k₁ k₂ _ _ _ _, ce_two (by decide) r₁ r₂ _ _ _ _, ce_sp_two c₁ c₂ _ _ _ _⟩,
        Pbkdf2.Md.AArch64.Calls.UpdArgs.covers P.ok.stream A₁, A₁.cw,
        Pbkdf2.Md.AArch64.Calls.UpdArgs.covers P.ok.stream A₂, A₂.cw⟩) fun L g m₀ u hL _ hc a => ?_
  obtain ⟨d, _, x, k, r⟩ := a
  refine Pbkdf2.Md.AArch64.Calls.upd_call P.ok.stream (updA (P := P) hL hc (hd L hL) hlen d x k r)
    fun u' af _ => ⟨hc.after hL af fun r hr => scr_sub ?_, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact scr_work (by anums)

theorem hfin_piece {cnt dst : Nat} (hdst : dst + P.H.D ≤ 184) :
    Piece P (FA P cnt dst) (.call P.H.hmacFinN P.H.hmacFin) (Tt P) := by
  refine Piece.of (AArch64.RelCT.callEx P.hF.1 P.hF.2.1 fun _ _ ⟨⟨L, _, _, _, _⟩, hL, _, _, c₁, c₂, a₁, a₂⟩ => by
    obtain ⟨d₁, s₁, x₁, k₁, r₁⟩ := a₁
    obtain ⟨d₂, s₂, x₂, k₂, r₂⟩ := a₂
    have A₁ := finA (P := P) hL c₁ hdst d₁ s₁ x₁ k₁ r₁
    have A₂ := finA (P := P) hL c₂ hdst d₂ s₂ x₂ k₂ r₂
    exact ⟨_, _, _, _, Pbkdf2.Md.AArch64.Pbk.FinArgs.pre P.ok A₁, Pbkdf2.Md.AArch64.Pbk.FinArgs.pre P.ok A₂,
      ⟨ce_two (by decide) d₁ d₂ _ _ _ _, ce_two (by decide) s₁ s₂ _ _ _ _, ce_two (by decide) x₁ x₂ _ _ _ _,
        ce_two (by decide) k₁ k₂ _ _ _ _, ce_two (by decide) r₁ r₂ _ _ _ _, ce_sp_two c₁ c₂ _ _ _ _⟩,
      Pbkdf2.Md.AArch64.Pbk.covers_app A₁.cr A₁.cw, A₁.cw, Pbkdf2.Md.AArch64.Pbk.covers_app A₂.cr A₂.cw, A₂.cw⟩)
    fun L g m₀ u hL _ hc a => ?_
  obtain ⟨d, s, x, k, r⟩ := a
  refine Pbkdf2.Md.AArch64.Pbk.hfin_call P.ok P.hF P.hFd (finA (P := P) hL hc hdst d s x k r)
    fun u' ha _ => ⟨hc.after hL ha fun r hr => ?_, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact scr_sub (scr_work (by anums))
  · exact safe_low L (by anums)
  · exact scr_sub (scr_work (by anums))

theorem r16_ia : R16 (IA P) := fun _ _ _ _ ⟨d, s, x, k, r⟩ hr _ _ => ⟨(hr _ (by decide)).trans d,
  (hr _ (by decide)).trans s, (hr _ (by decide)).trans x, (hr _ (by decide)).trans k, (hr _ (by decide)).trans r⟩

theorem r16_ua {cnt : Nat} {da : Lay P.I.hashLen P.R.E → Addr} {len : Nat} : R16 (UA P cnt da len) :=
  fun _ _ _ _ ⟨d, s, x, k, r⟩ hr _ _ => ⟨(hr _ (by decide)).trans d, (hr _ (by decide)).trans s,
    (hr _ (by decide)).trans x, (hr _ (by decide)).trans k, (hr _ (by decide)).trans r⟩

theorem r16_fa {cnt dst : Nat} : R16 (FA P cnt dst) :=
  fun _ _ _ _ ⟨d, s, x, k, r⟩ hr _ _ => ⟨(hr _ (by decide)).trans d, (hr _ (by decide)).trans s,
    (hr _ (by decide)).trans x, (hr _ (by decide)).trans k, (hr _ (by decide)).trans r⟩

/-! ## HMAC through the table -/

theorem initArgs_taint : TaintOk [] Cfg.initArgs := ⟨_, by taint_decide⟩

theorem updVArgs_taint : TaintOk [] Cfg.updVArgs := ⟨_, by taint_decide⟩

/-- For any length: the analysis does not read `movz`'s immediates. -/
theorem updMArgs_taint (len : Nat) : TaintOk [] (Cfg.updMArgs len) :=
  taintOk_erase (is₀ := Cfg.updMArgs 0) ⟨_, by taint_decide⟩ rfl

theorem tload_taint₀ : TaintOk [.x16] [.ldr .x .x16 .x16 (8 * 0)] := ⟨_, by taint_decide⟩
theorem tload_taint₁ : TaintOk [.x16] [.ldr .x .x16 .x16 (8 * 1)] := ⟨_, by taint_decide⟩
theorem tload_taint₂ : TaintOk [.x16] [.ldr .x .x16 .x16 (8 * 2)] := ⟨_, by taint_decide⟩

/-- HMAC's states for `K`. -/
theorem initK_piece {Φ : Pr P} : Piece P Φ (cfgOf P).initK (Tt P) :=
  (Piece.blkS (Ψ := IA P) initArgs_taint fun _ _ _ _ hL hk hc _ =>
    WP.mono (initArgs_ok hL hk.2 hc) fun _ ⟨c, _, d, s, x, k, r⟩ => ⟨c, d, s, x, k, r⟩).seq
    (tcall_piece (by decide) tfn_init r16_ia tload_taint₀ hinit_piece)

/-- The inner state updated with `V`. -/
theorem updV_piece {Φ : Pr P} : Piece P Φ (cfgOf P).updV (Tt P) :=
  (Piece.blkS (Ψ := UA P P.H.P.B (fun L => L.B + BitVec.ofNat 64 80) P.H.D) updVArgs_taint
    fun _ _ _ _ hL hk hc _ =>
      WP.mono (updVArgs_ok hL hk.2 hc) fun _ ⟨c, _, d, s, x, k, r⟩ => ⟨c, d, s, x, k, r⟩).seq
    (tcall_piece (by decide) tfn_upd r16_ua tload_taint₁
      (upd_piece (fun L _ => .inl ⟨80, rfl, by omega, by anums⟩) (by anums)))

/-- The inner state updated with the message's `len` bytes. -/
theorem updM_piece {Φ : Pr P} {len : Nat} (hlen : len ≤ 256) : Piece P Φ ((cfgOf P).updM len) (Tt P) :=
  (Piece.blkS (Ψ := UA P (P.H.P.B + P.H.D) (fun L => L.scr + BitVec.ofNat 64 sMsg) len) (updMArgs_taint len)
    fun _ _ _ _ hL hk hc _ =>
      WP.mono (updMArgs_ok hL hk.2 hc (len := len) (by omega)) fun _ ⟨c, _, d, s, x, k, r⟩ =>
        ⟨c, d, s, x, k, r⟩).seq
    (tcall_piece (by decide) tfn_upd r16_ua tload_taint₁
      (upd_piece (fun L _ => .inr ⟨sMsg, rfl, by simp only [sMsg]; omega, by simp only [sMsg]; omega⟩) hlen))

/-- The MAC, of `D + len` bytes, to the frame at `dst`. -/
theorem fin_piece {Φ : Pr P} {len dst : Nat} (hlen : len ≤ 256) (hdst : dst + P.H.D ≤ 184)
    (ht : TaintOk [] (Cfg.finArgs len dst)) : Piece P Φ ((cfgOf P).fin len dst) (Tt P) :=
  (Piece.blkS (Ψ := FA P (P.H.P.B + P.H.D + len) dst) ht fun _ _ _ _ hL hk hc _ =>
    WP.mono (finArgs_ok hL hk.2 hc (len := len) (dst := dst) (by omega) (by omega))
      fun _ ⟨c, _, d, s, x, k, r⟩ => ⟨c, d, s, x, k, r⟩).seq
    (tcall_piece (by decide) tfn_fin r16_fa tload_taint₂ (hfin_piece hdst))

/-! ## The byte loops -/

theorem cpLoop_taint : ∃ hc, (taint.check (Taint.ofRegs [.x11, .x12, .x13]) Cfg.cpLoop hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- A byte copy's registers. -/
abbrev CpA (P : RfcHash) (p q : Lay P.I.hashLen P.R.E → Addr) (n : Nat) : Pr P := fun L _ u =>
  u.gpr .x11 = q L ∧ u.gpr .x12 = p L ∧ u.gpr .x13 = BitVec.ofNat 64 n

/-- The byte loop, from registers that agree. -/
theorem cp_ct {Φ : Pr P} {p q : Lay P.I.hashLen P.R.E → Addr} {n : Nat}
    (h : ∀ L m₀ u, Φ L m₀ u → CpA P p q n L m₀ u) : RelCT isa (Two P Φ) Cfg.cpLoop fun _ _ => True :=
  two_prog [.x11, .x12, .x13] (fun _ _ _ _ _ _ _ _ _ f₁ f₂ r hr => by
    obtain ⟨a₁, b₁, c₁⟩ := h _ _ _ f₁; obtain ⟨a₂, b₂, c₂⟩ := h _ _ _ f₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact a₁.trans a₂.symm
    · exact b₁.trans b₂.symm
    · exact c₁.trans c₂.symm) cpLoop_taint

/-- The copy of the 384 bytes at `scratch + a` to `scratch + d`, apart. -/
theorem copy384_piece {Φ : Pr P} {a d : Nat} (ha : a < 4096) (hd : d < 4096) (hsep : a + 384 ≤ d ∨ d + 384 ≤ a)
    (hd₂ : d + 384 ≤ 8192) (ht : TaintOk [] ([.ldrSp .x9 fScratch] ++ [.addImm .x .x11 .x9 a] ++
      [.addImm .x .x12 .x9 d] ++ [.movz .x .x13 (BitVec.ofNat 16 384) 0])) :
    Piece P Φ (.seq (.block ([.ldrSp .x9 fScratch] ++ [.addImm .x .x11 .x9 a] ++ [.addImm .x .x12 .x9 d] ++
      [.movz .x .x13 (BitVec.ofNat 16 384) 0])) Cfg.cpLoop) (Tt P) :=
  Piece.of ((two_wp (Ψ := CpA P (fun L => L.scr + BitVec.ofNat 64 d) (fun L => L.scr + BitVec.ofNat 64 a) 384)
      (two_blk [] spOnly ht) fun _ _ _ _ hL _ hc _ =>
        WP.mono (copyArgs_ok hL ha hd hc) fun _ ⟨c, _, h11, h12, h13⟩ => ⟨c, h11, h12, h13⟩).seq
      (cp_ct fun _ _ _ h => h))
    fun _ _ _ _ hL _ hc _ => WP.mono (copy384_ok hL ha hd hsep hd₂ hc) fun _ h => ⟨h.1, trivial⟩

/-- HMAC's states saved. -/
theorem save_piece {Φ : Pr P} : Piece P Φ Cfg.save (Tt P) :=
  copy384_piece (a := 0) (d := 3072) (by decide) (by decide) (by decide) (by decide) ⟨_, by taint_decide⟩

/-- HMAC's states restored. -/
theorem restore_piece {Φ : Pr P} : Piece P Φ Cfg.restore (Tt P) :=
  copy384_piece (a := 3072) (d := 0) (by decide) (by decide) (by decide) (by decide) ⟨_, by taint_decide⟩

/-! ## HMAC -/

theorem finV_taint : TaintOk [] (Cfg.finArgs 0 fV) := ⟨_, by taint_decide⟩

theorem finK1_taint : TaintOk [] (Cfg.finArgs 1 fK) := ⟨_, by taint_decide⟩

theorem hmacVS_piece {Φ : Pr P} : Piece P Φ (cfgOf P).hmacVS (Tt P) :=
  initK_piece.seq (save_piece.seq
    (updV_piece.seq (fin_piece (by decide) (by simp only [fV]; anums) finV_taint)))

theorem hmacVR_piece {Φ : Pr P} : Piece P Φ (cfgOf P).hmacVR (Tt P) :=
  restore_piece.seq (updV_piece.seq (fin_piece (by decide) (by simp only [fV]; anums) finV_taint))

/-- `K = HMAC_K(V ‖ msg)`, for the message's `len` bytes. -/
theorem hmacK_piece {Φ : Pr P} {len : Nat} (hlen : len ≤ 256) (ht : TaintOk [] (Cfg.finArgs len fK))
    (fresh : Bool) : Piece P Φ ((cfgOf P).hmacK fresh len) (Tt P) := by
  unfold Cfg.hmacK
  cases fresh
  · exact restore_piece.seq (updV_piece.seq ((updM_piece hlen).seq
      (fin_piece hlen (by simp only [fK]; anums) ht)))
  · exact initK_piece.seq (updV_piece.seq ((updM_piece hlen).seq (fin_piece hlen (by simp only [fK]; anums) ht)))

/-! ## `K` and `V` from a message -/

/-- `scratch` in `x9`, `d` in `x10` and the frame in `x15`. -/
def PtrsIn (P : RfcHash) : Pr P := fun L _ u =>
  u.gpr .x9 = L.scr ∧ u.gpr .x10 = L.d ∧ u.gpr .x15 = L.B + BitVec.ofNat 64 16

theorem msgPtrs_piece {Φ : Pr P} : Piece P Φ (.block Cfg.msgPtrs) (PtrsIn P) :=
  Piece.blkS ⟨_, by taint_decide⟩ fun _ _ _ _ hL _ hc _ =>
    WP.mono (ptrs_ok hL hc) fun _ ⟨c, _, d, s, f⟩ => ⟨c, d, s, f⟩

/-- The message `b (‖ d ‖ h)` at `scratch + sMsg`. -/
theorem msg_piece {b : Nat} {full : Bool} (ht : TaintOk [.x9, .x10, .x15] ((cfgOf P).msg b full)) :
    Piece P (PtrsIn P) (.block ((cfgOf P).msg b full)) (Tt P) :=
  Piece.blk [.x9, .x10, .x15] (fun _ _ _ _ _ _ _ _ _ f₁ f₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact f₁.1.trans f₂.1.symm
      · exact f₁.2.1.trans f₂.2.1.symm
      · exact f₁.2.2.trans f₂.2.2.symm) ht
    fun _ _ _ _ hL hk hc hp => WP.mono (msg_ok hL hk.1 hc hp.1 hp.2.1 hp.2.2 b full) fun _ h => ⟨h.1, trivial⟩

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)`. -/
theorem rekeyFull_piece {Φ : Pr P} (b : Nat) (ht : TaintOk [.x9, .x10, .x15] ((cfgOf P).msg b true)) :
    Piece P Φ ((cfgOf P).rekeyFull b) (Tt P) := by
  have hlen : 1 + 2 * (cfgOf P).len ≤ 256 := by show 1 + 2 * P.Q ≤ 256; anums
  unfold Cfg.rekeyFull
  exact msgPtrs_piece.seq ((msg_piece ht).seq ((hmacK_piece hlen (by exact (rT P).finM) _).seq hmacVS_piece))

theorem msgN_taint : TaintOk [.x9, .x10, .x15] ((cfgOf P).msg 0 false) := by
  rw [show (cfgOf P).msg 0 false = [.movz .x .x11 (BitVec.ofNat 16 0) 0, .strb .x11 .x9 sMsg] by
    simp only [Cfg.msg, Bool.false_eq_true, ite_false, List.append_nil]]
  exact ⟨_, by taint_decide⟩

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)`. -/
theorem rekey_piece {Φ : Pr P} : Piece P Φ (cfgOf P).rekey (Tt P) := by
  unfold Cfg.rekey
  exact msgPtrs_piece.seq ((msg_piece msgN_taint).seq ((hmacK_piece (by decide) finK1_taint _).seq hmacVS_piece))

/-- `Ctx` with other callee-saved values, which are the same. -/
theorem Ctx.regen {dn : Nat} {E : Impl.Ecdsa.AArch64.Cfg} {L : Lay dn E} {g g' : Reg → BitVec 64} {m₀ : Mem}
    {u : State} (hc : Ctx L g' m₀ u) (h : ∀ r ∈ preserved, r ≠ .x30 → g' r = g r) (h30 : g' .x30 = g .x30) :
    Ctx L g m₀ u :=
  { hc with cs := fun r hr hr' => (hc.cs r hr hr').trans (h r hr hr'), lr := hc.lr.trans h30 }

/-! ## The candidate -/

/-- After `j` of the candidate's `V`s, from some `K` and `V`. -/
abbrev CJ (P : RfcHash) (j : Nat) : Pr P := fun L m₀ u => ∃ g' t₀ K V₀, CI P L g' m₀ t₀ K V₀ j u

/-- `T`'s length, `j` blocks. -/
abbrev TL (P : RfcHash) (j : Nat) : Pr P := fun L _ u => tlen L u.mem = BitVec.ofNat 64 (j * P.H.D)

/-- The arguments of the copy of `V` to `T`'s end, and `j` blocks. -/
abbrev KA (P : RfcHash) (j : Nat) : Pr P := fun L m₀ u =>
  CpA P (fun L => L.B + BitVec.ofNat 64 (16 + fT + j * P.H.D)) (fun L => L.B + BitVec.ofNat 64 (16 + fV)) P.H.D
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
    ((two_wp (Ψ := KA P j) (two_blk [] spOnly ⟨_, by taint_decide⟩) fun L g m₀ t hL hk hc hl =>
      WP.mono (keepArgs_ok hL hk.2 hc hl) fun u ⟨c, hm, si, di, cx⟩ =>
        ⟨c, ⟨si, di, cx⟩, by show tlen L u.mem = _; rw [hm]; exact hl⟩).seq
    ((two_wp (Ψ := TL P j) (cp_ct fun _ _ _ h => h.1) fun L g m₀ t hL hk hc ⟨⟨si, di, cx⟩, hl⟩ => ?_).seq
      (two_blk [] spOnly (by exact (rT P).tStep))))
  · obtain ⟨_, _, _, _, hI⟩ := hJ
    have hS : SavedK P L t.mem (kOf P L t.mem) := by rw [hI.k]; exact hI.saved
    refine WP.mono (hmacVR_ok hL hk.2 hc hS) fun u ⟨hc₁, hf₁, _⟩ => ⟨hc₁, ?_⟩
    show tlen L u.mem = _
    rw [← hI.len]
    exact hf₁.readW (Region.contains_self _ _) (fun r hr => by
      have := L.he
      simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_SCR (by simp only [fTlen]; omega)
      · exact Offset.disjoint_base _ (by simp only [fTlen]; omega) (by simp only [fTlen]; omega)) (by decide)
  · have he := L.he
    have hnb := hL.nB
    refine WP.mono (cp_ok hL hc (p := L.B + BitVec.ofNat 64 (16 + fT + j * P.H.D))
        (q := L.B + BitVec.ofNat 64 (16 + fV)) (n := P.H.D) (by omega) (by omega) cx di si ?_
        (hc.inFrW (by omega) (by simp only [fT]; omega))
        (safe_high L (by simp only [fT]; omega) (by simp only [fT]; omega))
        (fun i hi => by
          obtain ⟨R, hR, h⟩ := hc.inFrW (d := 16 + fV + i) (n := 1) (by omega) (by simp only [fV]; omega)
          exact ⟨R, List.mem_append_right _ hR, by rw [Offset.add_add]; exact h⟩)
        (fun i hi h => Offset.disjoint L.B (d := 16 + fV + i) (n := 1) (e := 16 + fT + j * P.H.D) (k := P.H.D)
          (.inl (by simp only [fV, fT]; omega)) (by simp only [fV]; omega) (by simp only [fT]; omega) _
          (by rw [← Offset.add_add]; exact Region.contains_self _ _) h)) fun u ⟨hcu, _, hf, _⟩ => ⟨hcu, ?_⟩
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 + fT + _) (by simp only [fT]; omega),
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
    RelCT isa (Two P (CJ P 0)) (.loop (cfgOf P).candStep (.nonzero .x .x12)) (Two P (CJ P P.nV)) := by
  obtain ⟨hN1, hND, -⟩ := nV_facts P
  obtain ⟨-, -, -, -, -, -, -, hD64, -, -, -, -, -, -, -, hQ66, -, -⟩ := P.sizes
  have h := VG.RelCT.loop (M := isa) (c := .nonzero .x .x12) (Q := Two P (CJ P P.nV))
    (fun n => fun s₁ s₂ => 0 < n ∧ n ≤ P.nV ∧ Two P (CJ P (P.nV - n)) s₁ s₂) (n := P.nV)
    (body := (cfgOf P).candStep)
    (fun n => by
      refine fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨hn0, hnN, hp⟩ e₁ e₂ => ?_
      have hj : P.nV - n < P.nV := by omega
      have hb : (P.nV - n + 1) * P.H.D ≤ 136 :=
        Nat.le_trans (Nat.mul_le_mul (show P.nV - n + 1 ≤ P.nV by omega) (Nat.le_refl P.H.D)) (by omega)
      obtain ⟨ht, hq⟩ := (two_wp (Ψ := fun L m₀ u => CJ P (P.nV - n + 1) L m₀ u ∧
          (u.gpr .x12 != 0) = decide ((P.nV - n + 1) * P.H.D < P.Q)) (candStep_trace hj)
        fun L g m₀ t hL hk hc ⟨g', t₀, K, V₀, hI⟩ => WP.mono (step_ok hL hk.2 hb hI)
          fun u ⟨hI', hcf⟩ => ⟨hI'.ctx.regen (fun r h h' => (hI.ctx.cs r h h').symm.trans (hc.cs r h h'))
              (hI.ctx.lr.symm.trans hc.lr),
            ⟨g', t₀, K, V₀, hI'⟩, hcf⟩) s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
      refine ⟨ht, ?_, ?_, ?_⟩
      · obtain ⟨_, _, _, _, _, _, f₁, f₂⟩ := hq
        rw [eval_nonzero, eval_nonzero, f₁.2, f₂.2]
      · intro hf
        obtain ⟨e, hL, hk, hx, c₁, c₂, f₁, f₂⟩ := hq
        rw [eval_nonzero, f₁.2, Option.some.injEq, decide_eq_false_iff_not] at hf
        have hNn : P.nV - n + 1 = P.nV := by
          have : ¬ P.nV - n + 1 < P.nV := fun h => hf ((nV_lt P _).mp h)
          omega
        exact ⟨e, hL, hk, hx, c₁, c₂, hNn ▸ f₁.1, hNn ▸ f₂.1⟩
      · intro hf
        obtain ⟨e, hL, hk, hx, c₁, c₂, f₁, f₂⟩ := hq
        rw [eval_nonzero, f₁.2, Option.some.injEq, decide_eq_true_iff] at hf
        have hlt := (nV_lt P (P.nV - n)).mpr hf
        refine ⟨n - 1, by omega, by omega, by omega, e, hL, hk, hx, c₁, c₂, ?_, ?_⟩ <;>
          rw [show P.nV - (n - 1) = P.nV - n + 1 by omega]
        · exact f₁.1
        · exact f₂.1)
  exact h.mono (fun s₁ s₂ hp => ⟨hN1, Nat.le_refl _, by rwa [Nat.sub_self]⟩) fun _ _ h => h

/-- A conversion: its block addresses memory from `scratch`, loaded first into `x0`. -/
theorem conv_ct {Φ : Pr P} {o s : Nat} (h : TaintOk [.x0] ((cfgOf P).convB o s)) :
    RelCT isa (Two P Φ) ((cfgOf P).conv o s) fun _ _ => True := by
  rw [Cfg.conv]
  exact (two_wp (Ψ := fun L _ u => u.gpr .x0 = L.scr) (two_blk [] spOnly ⟨_, by taint_decide⟩)
    fun _ _ _ _ hL _ hc _ => WP.mono (ldScr_ok hL hc) fun _ h => ⟨h.ctx, h.val⟩).seq
    (two_blk [.x0] (fun _ _ _ _ _ _ _ _ _ f₁ f₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact f₁.trans f₂.symm) h)

theorem candTop_ct {Φ : Pr P} : RelCT isa (Two P Φ) (cfgOf P).candTop fun _ _ => True := by
  cases hb : P.R.big
  · rw [show (cfgOf P).candTop = .block [] by
      simp only [Cfg.candTop, show (cfgOf P).big = false from hb, Bool.false_eq_true, ite_false]]
    exact two_blk [] spOnly ⟨_, by taint_decide⟩
  · rw [show (cfgOf P).candTop = (cfgOf P).conv fT (cfgOf P).sh by
      simp only [Cfg.candTop, show (cfgOf P).big = true from hb, ite_true]]
    exact conv_ct (by exact (rT P).convT hb)

/-- The candidate: its calls, blocks and loops leak the same in both runs. -/
theorem cand_ct :
    RelCT isa (Two P fun L _ t => SavedK P L t.mem (kOf P L t.mem)) (cfgOf P).cand fun _ _ => True := by
  unfold Cfg.cand
  exact (two_wp (Ψ := CJ P 0) (two_blk [] spOnly ⟨_, by taint_decide⟩) fun L g m₀ t hL hk hc hS =>
    WP.mono (tInit_ci hL hc hS) fun u hI => ⟨hI.ctx, _, _, _, _, hI⟩).seq (candLoop_ct.seq candTop_ct)

/-! ## One candidate -/

/-- `core`, with arguments that agree. -/
theorem core_ct {i : Nat} :
    RelCT isa (Two P fun L m₀ u => P₁ P L m₀ i u ∧ Args P L u) (.call (cfgOf P).coreN (cfgOf P).coreC)
      fun _ _ => True :=
  AArch64.RelCT.callEx P.R.coreX P.R.coreCT
    fun _ _ ⟨⟨L, _, _, _, _⟩, hL, hq, _, c₁, c₂, ⟨_, a₁⟩, ⟨_, a₂⟩⟩ =>
    ⟨coreRd P L, coreWr P L, coreRd P L, coreWr P L, core_pre hL hq.1 c₁ a₁.x0 a₁.x1 a₁.x2 a₁.x3 a₁.x4,
      core_pre hL hq.1 c₂ a₂.x0 a₂.x1 a₂.x2 a₂.x3 a₂.x4,
      ⟨ce_two (by decide) a₁.x0 a₂.x0 _ _ _ _, ce_two (by decide) a₁.x1 a₂.x1 _ _ _ _,
        ce_two (by decide) a₁.x2 a₂.x2 _ _ _ _, ce_two (by decide) a₁.x3 a₂.x3 _ _ _ _,
        ce_two (by decide) a₁.x4 a₂.x4 _ _ _ _, ce_sp_two c₁ c₂ _ _ _ _, c₁.sy.trans c₂.sy.symm⟩,
      core_covers hL hq.1 c₁, core_coversW hq.1 c₁, core_covers hL hq.1 c₂, core_coversW hq.1 c₂⟩

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
  refine (two_wp (Ψ := fun L m₀ u => P₁ P L m₀ i u)
    (cand_ct.mono (fun _ _ h => Two.mono (fun _ _ _ hi => hi.saved) h) fun _ _ h => h)
    fun _ _ _ _ hL hk hc hi => try₁_ok hL hk hc hi).seq ?_
  refine (two_wp (Ψ := fun L m₀ u => P₁ P L m₀ i u ∧ Args P L u) (two_blk [] spOnly (by exact (rT P).coreArgs))
    fun _ _ _ _ hL hk hc hi => try₂_ok hL hc hi).seq ?_
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

theorem tries_ct :
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

/-- For any count: the analysis does not read `movz`'s immediates. -/
theorem initCnt_taint (c : Cfg) : TaintOk [] c.initCnt :=
  taintOk_erase (is₀ := [.movz .x .x9 0 0, .addSp .x15 0, .str .x .x9 .x15 fCnt]) ⟨_, by taint_decide⟩ rfl

/-- The arguments of `xcArgs`'s copy: the digest's `D` bytes to `fXc`, after
`Q - 1 - D` zero bytes. -/
theorem xcArgs_ok (hL : L.Ok) (hk : HOk P L) (hW : P.R.big = true) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).xcArgs) t fun u => Ctx L g m₀ u ∧
      CpA P (fun L => L.B + BitVec.ofNat 64 (16 + fXc + (P.Q - 1 - P.H.D))) (fun L => L.dg) P.H.D L m₀ u := by
  have he := L.he
  obtain ⟨-, hQ66, hQD⟩ := P.sizesW hW
  obtain ⟨-, -, -, -, -, -, hD16, hD64, -, -, -, -, -, -, -, -, -, -⟩ := P.sizes
  have hlen : (cfgOf P).len = P.Q := rfl
  rw [Cfg.xcArgs, WP.block_append_iff]
  refine WP.mono (zero9_ok hL (o := fXc) (by decide) (by simp only [fXc]; omega) (by decide) hc)
    fun u₁ ⟨hc₁, _, _, _, _⟩ => ?_
  rw [hlen, show ([.ldrSp .x13 fDl, .addSp .x12 (fXc + P.Q - 1), .sub .x .x12 .x12 .x13, .ldrSp .x11 fDigest] :
      List Instr) = [.ldrSp .x13 fDl] ++ [.addSp .x12 (fXc + P.Q - 1), .sub .x .x12 .x12 .x13, .ldrSp .x11 fDigest]
      from rfl, WP.block_append_iff]
  refine WP.mono (ldD_ok hL hk.2 hc₁ (d := .x13) (by decide)) fun u₂ h₂ => ?_
  refine WP.mono (xTail_ok hL h₂.ctx (o := fXc + P.Q - 1) (by simp only [fXc]; omega))
    fun u₃ ⟨hc₃, _, h12₃, h11₃, hg₃⟩ => ?_
  have hx : 16 + (fXc + P.Q - 1 - P.H.D) = 16 + fXc + (P.Q - 1 - P.H.D) := by omega
  rw [h₂.val, sub_min _ (by omega), hx] at h12₃
  exact ⟨hc₃, h11₃, h12₃, by rw [hg₃ _ (by decide) (by decide), h₂.val]⟩

/-- The digest's `D` bytes copied to `fXc`, after `Q - 1 - D` zero bytes. -/
theorem xcCopy_ok (hL : L.Ok) (hk : HOk P L) (hW : P.R.big = true) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.seq (.block (cfgOf P).xcArgs) Cfg.cpLoop) t fun u => Ctx L g m₀ u ∧ True := by
  have he := L.he
  have hnb := hL.nB
  obtain ⟨-, hQ66, hQD⟩ := P.sizesW hW
  obtain ⟨-, -, -, -, -, -, hD16, hD64, -, -, -, -, -, -, -, -, -, -⟩ := P.sizes
  have hdn : P.H.D ≤ P.I.hashLen := by rw [P.len]
  refine WP.seq (WP.mono (xcArgs_ok hL hk hW hc) fun u ⟨hcu, h11, h12, h13⟩ => ?_)
  refine WP.mono (cp_ok hL hcu (p := L.B + BitVec.ofNat 64 (16 + fXc + (P.Q - 1 - P.H.D))) (q := L.dg)
      (n := P.H.D) (by omega) (by omega) h13 h12 h11 ?_ (hcu.inFrW (by omega) (by simp only [fXc]; omega))
      (safe_high L (by simp only [fXc]; omega) (by simp only [fXc]; omega))
      (fun i hi => hcu.inDg (o := i) (n := 1) (by omega) (by omega))
      (fun i hi hcon => hL.kg _ (Offset.sub_base L.B (k := 256 + 8 * L.e) (by simp only [fXc]; omega) _ hcon)
        (Offset.contains_base L.dg (d := i) (n := 1) (k := P.I.hashLen) (by omega) (by omega))))
    fun _ h => ⟨h.1, trivial⟩
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16 + fXc + _) (by simp only [fXc]; omega),
    Nat.mod_eq_of_lt (by simp only [fXc]; omega)]
  simp only [fXc]; omega

theorem prepX_ct : RelCT isa (Two P (Tt P)) (cfgOf P).prepX (Two P (QX P)) := by
  refine two_wp ?_ fun L g m₀ t hL hk hc _ => stageX_ok hL hk hc
  rw [Cfg.prepX]
  exact (two_wp (Ψ := CpA P (fun L => L.B + BitVec.ofNat 64 (16 + fX + (P.Q - min P.H.D P.Q))) (fun L => L.dg)
      (min P.H.D P.Q)) (two_blk [] spOnly (by exact (rT P).xArgs)) fun L g m₀ t hL hk hc _ =>
    WP.mono (xArgs_ok hL hk.2 hc) fun _ ⟨c, _, _, cx, di, si⟩ => ⟨c, si, di, cx⟩).seq
    (cp_ct fun _ _ _ h => h)

theorem prepH_ct : RelCT isa (Two P (QX P)) (cfgOf P).prepH (Two P (QA P)) := by
  refine two_wp ?_ fun L g m₀ t hL hk hc hx => stageH_ok hL hk hc hx
  cases hb : P.R.big
  · rw [show (cfgOf P).prepH = .block (cfgOf P).reduce by
      simp only [Cfg.prepH, show (cfgOf P).big = false from hb, Bool.false_eq_true, ite_false]]
    exact two_blk [] spOnly (by exact (rT P).reduce hb)
  · rw [show (cfgOf P).prepH = (cfgOf P).prepC by
      simp only [Cfg.prepH, show (cfgOf P).big = true from hb, ite_true], Cfg.prepC]
    refine RelCT.assoc ((two_wp (Ψ := Tt P) ((two_wp (Ψ := CpA P
        (fun L => L.B + BitVec.ofNat 64 (16 + fXc + (P.Q - 1 - P.H.D))) (fun L => L.dg) P.H.D)
        (two_blk [] spOnly (by exact (rT P).xcArgs hb)) fun L g m₀ t hL hk hc _ =>
          xcArgs_ok hL hk hb hc).seq
        (cp_ct fun _ _ _ h => h)) fun L g m₀ t hL hk hc _ => xcCopy_ok hL hk hb hc).seq
      (conv_ct (by exact (rT P).convC hb)))

/-- The frame's body, once the arguments are saved. -/
theorem rest_ct :
    RelCT isa (Two P (Tt P)) (.seq (cfgOf P).prepX (.seq (cfgOf P).prepH (.seq (.block Cfg.initKV)
      (.seq ((cfgOf P).rekeyFull 0) (.seq ((cfgOf P).rekeyFull 1) (.seq (.block (cfgOf P).initCnt)
        (.seq (.loop (cfgOf P).tryOne (.nonzero .x .x12)) (.block Cfg.wipe))))))))
      (Two P fun L m₀ t => ∃ i, Exit P L m₀ i t) := by
  refine prepX_ct.seq (prepH_ct.seq ?_)
  refine (two_wp (Ψ := QB P) (two_blk [] spOnly ⟨_, by taint_decide⟩)
    fun _ _ _ _ hL _ hc h => stageB_ok hL hc h).seq ?_
  refine (two_wp (Ψ := QC P) ((rekeyFull_piece 0 (by exact (rT P).msgF₀)).rel fun _ _ _ _ => trivial)
    fun _ _ _ _ hL hk hc h => stageC_ok (P := P) hL hk hc h).seq ?_
  refine (two_wp (Ψ := QD P) ((rekeyFull_piece 1 (by exact (rT P).msgF₁)).rel fun _ _ _ _ => trivial)
    fun _ _ _ _ hL hk hc h => stageD_ok (P := P) hL hk hc h).seq ?_
  refine (two_wp (Ψ := fun L m₀ t => LoopInv P L m₀ 0 t) (two_blk [] spOnly (initCnt_taint _))
    fun _ _ _ _ hL _ hc h => stageE_ok (P := P) hL hc h).seq ?_
  refine tries_ct.seq ?_
  exact two_wp (two_blk [] spOnly ⟨_, by taint_decide⟩) fun _ _ _ _ hL hk hc ⟨i, h⟩ =>
    WP.mono (stageG_ok hL hk hc h) fun _ ⟨c, x⟩ => ⟨c, i, x⟩

/-! ## The whole function -/

/-- Two calls whose public data agree, in the inner frame. -/
def Entered (P : RfcHash) (ns : List String) (a b : State) : Prop :=
  ∃ s₁ s₂, (rfcP P ns).pre s₁ ∧ (rfcP P ns).pre s₂ ∧ (rfcP P ns).pub s₁ s₂ ∧ a = entered s₁ ∧ b = entered s₂

theorem save_taint : TaintOk [] Cfg.saveArgs := ⟨_, by taint_decide⟩

/-- Saving the arguments: the runs have the same layout, and stop at the same
candidate (with the addresses of the hash function's HMAC functions among
`ns`). -/
theorem save_ct {ns : List String} (hns : ∀ n ∈ [P.H.hmacInitN, P.H.updN, P.H.hmacFinN], n ∈ ns) :
    RelCT isa (Entered P ns) (.block Cfg.saveArgs) (Two P (Tt P)) := by
  intro a b ta tb a' b' ⟨s₁, s₂, h₁, h₂, ⟨hsp, h0, h1, h2, h4, h5, hres, hsy, hns'⟩, ea, eb⟩ e₁ e₂
  subst ea eb
  obtain ⟨_, hc⟩ := save_taint
  obtain ⟨ht, -⟩ := RelCT.taint (A := taint) (P := fun x y => x.sp = y.sp) (Taint.ofRegs [])
    (fun _ _ h => ⟨h, fun r hr => absurd (Taint.mem_ofRegs.mp hr) List.not_mem_nil⟩) hc _ _ _ _ _ _
    (show (entered s₁).sp = (entered s₂).sp by
      show s₁.sp - 16 - BitVec.ofNat 64 frameBytes = s₂.sp - 16 - BitVec.ofNat 64 frameBytes
      rw [hsp]) e₁ e₂
  obtain ⟨_, u₁, x₁, c₁⟩ := save_ctx h₁
  obtain ⟨_, u₂, x₂, c₂⟩ := save_ctx h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  have hfa : (fun n => if n ∈ [P.H.hmacInitN, P.H.updN, P.H.hmacFinN] then s₁.syms n else 0) =
      fun n => if n ∈ [P.H.hmacInitN, P.H.updN, P.H.hmacFinN] then s₂.syms n else 0 :=
    funext fun n => by
      split
      · next h => exact hns' n (hns n h)
      · rfl
  have hl : layOf P s₁ = layOf P s₂ := by
    simp only [layOf, lay, hsp, h0, h1, h2, h4, h5, hsy, hfa]
  have hr : (result P.I s₁.mem (s₁.gpr .x1) (s₁.gpr .x2)).2 = (result P.I s₂.mem (s₁.gpr .x1) (s₁.gpr .x2)).2 := by
    rw [hres, h1, h2]
  exact ⟨ht, ⟨layOf P s₁, s₁.gpr, s₂.gpr, s₁.mem, s₂.mem⟩, lay_ok rfl h₁, hOk_lay P s₁,
    congrArg (fun x => if x = 0 then P.I.tries - 1 else x - 1) hr, c₁, by rw [hl]; exact c₂, trivial, trivial⟩

/-- Runs whose public data agree (with the addresses of the hash function's
HMAC functions among `ns`) have the same layout, and stop at the same
candidate. -/
theorem sign_ct {ns : List String} (hns : ∀ n ∈ [P.H.hmacInitN, P.H.updN, P.H.hmacFinN], n ∈ ns) :
    ConstantTime isa (rfcP P ns).pre (rfcP P ns).pub (cfgOf P).sign := by
  refine VG.RelCT.constantTime (Q := fun _ _ => True) (RelCT.pushFrame (R := fun _ _ => True)
    (fun _ _ h => h.2.2.1) (RelCT.alloc (R := fun _ _ => True) ?_))
  rw [Cfg.body]
  refine ((save_ct hns).seq rest_ct).mono ?_ fun _ _ _ => trivial
  rintro _ _ ⟨_, _, ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩, rfl, rfl⟩
  exact ⟨s₁, s₂, h₁, h₂, hp, rfl, rfl⟩

end VG.Proof.Ecdsa.Rfc6979.AArch64

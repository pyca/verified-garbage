module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Correct
public import VerifiedGarbage.Proof.Hmac.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Ecdsa.Contract
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
public import VerifiedGarbage.Proof.Framework.PPC64LE.TaintErase
import VerifiedGarbage.Proof.Framework.ICall
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Step
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Prep
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Reduce
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Copy
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Correct
meta import VerifiedGarbage.Proof.Hmac.Contract
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Ecdsa.Contract
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Call
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
meta import VerifiedGarbage.Proof.Framework.PPC64LE.TaintErase
meta import VerifiedGarbage.Proof.Framework.ICall
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
meta import VerifiedGarbage.Proof.Mont.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Step
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Prep
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Reduce
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.PPC64LE.Copy
meta import VerifiedGarbage.Impl.Ecdsa.Rfc6979.PPC64LE
meta import VerifiedGarbage.TCB.Code

/-!
# Deterministic ECDSA on PPC64LE: constant time, up to the number of candidates

Two runs whose public data agree have the same layout, and stop at the same
candidate (`exitAt`, from the contract's leakage: the number of candidates
RFC 6979 tries). Between the frames' pushes and pops they are related by
`Two`: both satisfy `Ctx` with that layout (and `Φ`, what the next piece
needs). The blocks address only the frame, from `sp`, and the buffers, from
pointers loaded from the frame, which agree (the taint analysis of the rest
of the block, from the registers that hold them: `two_split`; of the blocks
whose contents depend on the curve: `RfcT`, which each curve's file
proves); an indirect call reaches, through the table, whose address the
frame holds, the same function in both runs (`tcall_ct`); each call is of
constant-time code whose public data agree (`two_call`); and the loops'
branches agree: the candidate's, at the same number of `V`s, and the
candidates', since in both runs it goes on after candidate `i` iff `i` is
before the candidate it stops at (`go_iff`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE VG.Impl.Ecdsa.Rfc6979.PPC64LE
open VG.Proof.Mont.PPC64LE (Kp)
open VG.Proof.Ecdsa.Rfc6979 (stepB)

/-! ## The candidate the loop stops at -/

theorem ite_le_of_not {c : Prop} [Decidable c] {a b i : Nat} (hc : ¬c) (hb : b ≤ i) :
    (if c then a else b) ≤ i := by
  simp only [hc, ite_false]; exact hb

/-- The candidate the loop stops at, from the number RFC 6979 tries. -/
def exitAt (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : Nat :=
  if (result P.I m₀ L.d L.dg).2 = 0 then P.I.tries - 1 else (result P.I m₀ L.d L.dg).2 - 1

/-- The loop goes on after candidate `i` iff it stops at a later one. -/
theorem go_iff {P : RfcHash} {L : Lay P.I.hashLen} {m₀ : Mem} {i : Nat} (hi : i < P.I.tries)
    (hf : ∀ j < i, sigI P L m₀ j = none) :
    (sigI P L m₀ i = none ∧ i + 1 < P.I.tries) ↔ i < exitAt P L m₀ := by
  unfold exitAt
  rw [result_unfold]
  by_cases hv : 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.C.E.curve.n
  · simp only [hv, and_self, ite_true]
    rw [Proof.Ecdsa.Rfc6979.searchB_shift (nV_eq P) i P.I.tries (by omega) hf,
      show P.I.tries - i = (P.I.tries - 1 - i) + 1 by omega]
    cases hs : sigI P L m₀ i with
    | some rs =>
      rw [Proof.Ecdsa.Rfc6979.searchB_ok (nV_eq P) hs]
      simp
    | none =>
      rw [Proof.Ecdsa.Rfc6979.searchB_fail (nV_eq P) hs]
      by_cases h7 : i + 1 < P.I.tries
      · have := Proof.Ecdsa.Rfc6979.searchB_pos (C := P.R.C.E.curve) (H := P.v.l.ok.SH.H) (hlen := P.v.H.D)
          (d := xOf P L m₀) (e := eOf P L m₀) (n := P.I.tries - 2 - i)
          (K := (stepB P.v.l.ok.SH.H P.nV (kvI P L m₀ i).1 (kvI P L m₀ i).2).1)
          (V := (stepB P.v.l.ok.SH.H P.nV (kvI P L m₀ i).1 (kvI P L m₀ i).2).2) (nV_eq P)
        rw [show P.I.tries - 1 - i = P.I.tries - 2 - i + 1 by omega]
        simp only [true_and, h7]
        simp only [kvI] at this
        rw [true_iff]
        split <;> omega
      · rw [show P.I.tries - 1 - i = 0 by omega]
        simp only [Spec.Ecdsa.Rfc6979.search, h7, and_false, false_iff, Nat.not_lt]
        exact ite_le_of_not (by omega) (by omega)
  · simp only [hv, ite_false, ite_true]
    have hs : sigI P L m₀ i = none := by
      simp only [sigI, Spec.Ecdsa.signWith]
      split
      · rename_i h; exact absurd ⟨h.1, h.2.1⟩ hv
      · rfl
    simp only [hs, true_and]
    omega

/-! ## Two runs -/

/-- What the proof needs of each run at a point of the code. -/
abbrev Pred (P : RfcHash) := Lay P.I.hashLen → (Reg → BitVec 64) → Addr → Mem → State → Prop

/-- Two runs with the layout `L`, that stop at the same candidate, each
satisfying `Ctx` and `Φ`. -/
structure TwoAt (P : RfcHash) (Φ : Pred P) (L : Lay P.I.hashLen) (g₁ g₂ : Reg → BitVec 64) (lr₁ lr₂ : Addr)
    (m₁ m₂ : Mem) (a b : State) : Prop where
  ok : L.Ok
  q : HOk P L
  x : exitAt P L m₁ = exitAt P L m₂
  c₁ : Ctx L g₁ lr₁ m₁ a
  c₂ : Ctx L g₂ lr₂ m₂ b
  f₁ : Φ L g₁ lr₁ m₁ a
  f₂ : Φ L g₂ lr₂ m₂ b

/-- Two runs with the same layout that stop at the same candidate. -/
def Two (P : RfcHash) (Φ : Pred P) (a b : State) : Prop :=
  ∃ L g₁ g₂ lr₁ lr₂ m₁ m₂, TwoAt P Φ L g₁ g₂ lr₁ lr₂ m₁ m₂ a b

variable {P : RfcHash}

theorem Two.mono {Φ Ψ : Pred P} (h : ∀ L g lr m₀ t, Φ L g lr m₀ t → Ψ L g lr m₀ t) {a b : State}
    (ht : Two P Φ a b) : Two P Ψ a b :=
  let ⟨L, g₁, g₂, lr₁, lr₂, m₁, m₂, t⟩ := ht
  ⟨L, g₁, g₂, lr₁, lr₂, m₁, m₂, t.ok, t.q, t.x, t.c₁, t.c₂, h _ _ _ _ _ t.f₁, h _ _ _ _ _ t.f₂⟩

/-- Code whose runs leak the same, and which keeps `Ctx` and establishes `Ψ`. -/
theorem two_wp {c : Prog isa} {Φ Ψ : Pred P}
    (hct : RelCT isa (Two P Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay P.I.hashLen) g lr m₀ (t : State), L.Ok → HOk P L → Ctx L g lr m₀ t →
      Φ L g lr m₀ t → WP isa c t fun t' => Ctx L g lr m₀ t' ∧ Ψ L g lr m₀ t') :
    RelCT isa (Two P Φ) c (Two P Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨L, g₁, g₂, lr₁, lr₂, m₁, m₂, h⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw L g₁ lr₁ m₁ s₁ h.ok h.q h.c₁ h.f₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw L g₂ lr₂ m₂ s₂ h.ok h.q h.c₂ h.f₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, L, g₁, g₂, lr₁, lr₂, m₁, m₂, h.ok, h.q, h.x, y₁.1, y₂.1, y₁.2, y₂.2⟩

/-- The taint check of a block, from the registers `rs` public. -/
abbrev TaintOk (rs : List Reg) (is : List Instr) : Prop :=
  ∃ hc, (VG.Taint.check taint (Taint.ofRegs rs) (.block is) hc).isSome = true

/-- The taint check of a block is that of a block with the same instructions
but for the immediates of `li`, `lis`, `ori` and `oris`. -/
theorem taintOk_erase {rs : List Reg} {is is₀ : List Instr} (h : TaintOk rs is₀)
    (he : is.map Instr.eraseImm = is₀.map Instr.eraseImm) : TaintOk rs is :=
  let ⟨hc, hs⟩ := h
  ⟨hc, Taint.isSome_check_of_eraseImm (c := .block is) (c' := .block is₀)
    (show Code.block _ = Code.block _ from congrArg Code.block he) hs⟩

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

/-- Code (a loop) whose addresses and branches depend only on `sp` and the
registers `rs`, which hold the same values in both runs. -/
theorem two_prog {c : Prog isa} {Φ : Pred P} (rs : List Reg) (f : Lay P.I.hashLen → Reg → BitVec 64)
    (hf : ∀ L g lr m₀ (t : State), Φ L g lr m₀ t → ∀ r ∈ rs, t.gpr r = f L r)
    (h : ∃ hc, (VG.Taint.check taint (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa (Two P Φ) c fun _ _ => True :=
  let ⟨_, h⟩ := h
  VG.RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun _ _ ⟨_, _, _, _, _, _, _, t⟩ => ⟨t.c₁.sp.trans t.c₂.sp.symm, fun r hr => by
      rw [hf _ _ _ _ _ t.f₁ r (Taint.mem_ofRegs.mp hr), hf _ _ _ _ _ t.f₂ r (Taint.mem_ofRegs.mp hr)]⟩) h

/-- A block that loads values, the same in both runs, into `rs`, and then
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

/-- A call of constant-time code whose preconditions hold in both runs and
whose public data agree. -/
theorem two_call {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {Φ : Pred P} (rd wr : Lay P.I.hashLen → List Region)
    (hpre : ∀ (L : Lay P.I.hashLen) g lr m₀ (u : State), L.Ok → HOk P L → Ctx L g lr m₀ u →
      Φ L g lr m₀ u → k.pre (u.callEntry.withRegions (rd L) (wr L)) ∧ Covers (rd L ++ wr L) (u.rd ++ u.wr) ∧
        Covers (wr L) u.wr)
    (hpub : ∀ L g₁ g₂ lr₁ lr₂ m₁ m₂ (u₁ u₂ : State), TwoAt P Φ L g₁ g₂ lr₁ lr₂ m₁ m₂ u₁ u₂ →
      k.pub (u₁.callEntry.withRegions (rd L) (wr L)) (u₂.callEntry.withRegions (rd L) (wr L))) :
    RelCT isa (Two P Φ) (.call n c) fun _ _ => True :=
  RelCT.callEx hv hct fun s₁ s₂ ⟨L, g₁, g₂, lr₁, lr₂, m₁, m₂, h⟩ =>
    let ⟨p₁, c₁, w₁⟩ := hpre L g₁ lr₁ m₁ s₁ h.ok h.q h.c₁ h.f₁
    let ⟨p₂, c₂, w₂⟩ := hpre L g₂ lr₂ m₂ s₂ h.ok h.q h.c₂ h.f₂
    ⟨rd L, wr L, rd L, wr L, p₁, p₂, hpub _ _ _ _ _ _ _ _ _ h, c₁, w₁, c₂, w₂⟩

/-- Nothing. -/
abbrev Tt (P : RfcHash) : Pred P := fun _ _ _ _ _ => True

theorem two_any {c : Prog isa} {Φ : Pred P} (h : RelCT isa (Two P (Tt P)) c fun _ _ => True) :
    RelCT isa (Two P Φ) c fun _ _ => True :=
  h.mono (fun _ _ => Two.mono fun _ _ _ _ _ _ => trivial) fun _ _ h => h

variable {g : Reg → BitVec 64} {lr : Addr} {m₀ : Mem}

/-! ## The blocks whose contents depend on the curve -/

/-- The code's blocks for a curve with scalars of `w` words and `len` bytes
(`h = X` and `core`'s digest shifted if `big`, by `sh` bits) and order `n`,
without the functions it calls. -/
def cfgC (w len : Nat) (big : Bool) (sh n : Nat) : Cfg where
  f := ⟨[], [], []⟩
  w := w
  len := len
  big := big
  sh := sh
  n := n
  tries := 8
  coreN := ""
  coreC := .block []

/-- The curve's blocks: each addresses memory only from `sp` and the
registers that hold the pointers the code loaded before it (the taint
analysis). -/
structure RfcT (c : Cfg) : Prop where
  xArgs : TaintOk [] c.xArgs
  reduce : c.big = false → TaintOk [] c.reduce
  msgF : TaintOk [.r9, .r10, .r11] (c.msg 0 true)
  finM : TaintOk [] (Cfg.finArgs (1 + 2 * c.len) fK)
  coreArgs : TaintOk [] c.coreArgs
  xcArgs : c.big = true → TaintOk [] c.xcArgs
  convC : c.big = true → TaintOk [.r3] (c.convBody fXc (8 - c.sh))
  convT : c.big = true → TaintOk [.r3] (c.convBody fT c.sh)

/-- `RfcT` of a curve's blocks, by evaluating them. -/
macro "rfcT_decide" : tactic => `(tactic| exact
  { xArgs := ⟨_, by taint_decide⟩, reduce := by exact (Function.const _ ⟨_, by taint_decide⟩),
    msgF := ⟨_, by taint_decide⟩, finM := ⟨_, by taint_decide⟩, coreArgs := ⟨_, by taint_decide⟩,
    xcArgs := by exact (Function.const _ ⟨_, by taint_decide⟩),
    convC := by exact (Function.const _ ⟨_, by taint_decide⟩),
    convT := by exact (Function.const _ ⟨_, by taint_decide⟩) })

/-- The curve's blocks of the code for `P`. -/
abbrev cfgP (P : RfcHash) : Cfg := cfgC P.R.w P.R.Q P.R.big P.R.sh P.R.C.E.curve.n

/-! ## The indirect calls -/

/-- What an indirect call of `n` needs of the table in each run: its word
`j` (on entry) is `n`'s address, which is the layout's, and of `ts` an
indirect call reaches `n`'s `c`. -/
def TabFn (P : RfcHash) (j : Nat) (n : String) (c : Prog isa) (ts : List (String × Prog isa)) : Prop :=
  ∀ (L : Lay P.I.hashLen) g lr m₀ (t : State), L.Ok → HOk P L → Ctx L g lr m₀ t →
    m₀.readW (L.tab + BitVec.ofNat 64 (8 * j)) 64 = t.syms n ∧
      ts.find? (fun q => t.syms q.1 == t.syms n) = some (n, c) ∧ t.syms n = L.fa n

theorem tfn_init : TabFn P 0 P.v.initN P.v.H.init P.f.init := fun L _ _ _ _ _ hq hc => by
  have hok := hc.tabOk; have htm := hc.tabMem; have hf := hc.fsy
  rw [hq.2.1, hq.2.2] at hok; rw [hq.2.1] at htm hf
  exact ⟨htm.1, hok.i, hf _ (by simp)⟩

theorem tfn_upd : TabFn P 1 P.v.H.updN P.v.H.updC P.f.upd := fun L _ _ _ _ _ hq hc => by
  have hok := hc.tabOk; have htm := hc.tabMem; have hf := hc.fsy
  rw [hq.2.1, hq.2.2] at hok; rw [hq.2.1] at htm hf
  exact ⟨htm.2.1, hok.u, hf _ (by simp)⟩

theorem tfn_fin : TabFn P 2 P.v.finN P.v.H.finalize P.f.fin := fun L _ _ _ _ _ hq hc => by
  have hok := hc.tabOk; have htm := hc.tabMem; have hf := hc.fsy
  rw [hq.2.1, hq.2.2] at hok; rw [hq.2.1] at htm hf
  exact ⟨htm.2.2, hok.f, hf _ (by simp)⟩

/-- What only `r12` changing keeps. -/
def R12 (Φ : Pred P) : Prop :=
  ∀ L g lr m₀ (t u : State), Φ L g lr m₀ t → (∀ r, r ≠ .r12 → u.gpr r = t.gpr r) → u.mem = t.mem →
    u.syms = t.syms → Φ L g lr m₀ u

/-- The table's address in `r12`. -/
theorem tabPtr_ok {L : Lay P.I.hashLen} {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block [.addSp .r12 0, .load .d .r12 .r12 fTab]) t fun t' =>
      t'.sp = t.sp ∧ ∀ r ∈ [Reg.r12], t'.gpr r = L.tab := by
  refine stepAddSp (by decide) fun t₁ k₁ m₁ v₁ => ?_
  have hb : t₁.gpr .r12 = L.B + BitVec.ofNat 64 96 := by rw [v₁, hc.sp, BitVec.add_zero]
  refine stepLd (a := L.B + BitVec.ofNat 64 320) (by decide) (by decide) (by rw [hb, fr_add]; rfl)
    (hc.inFrK k₁ (by omega) (by omega)) fun t₂ k₂ m₂ v₂ => wp_nil ⟨by rw [k₂.sp, k₁.sp], fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr; subst hr
  rw [v₂, m₁, hc.pTab]

/-- The table's word `j` in `r12`. -/
theorem tblk_ok {L : Lay P.I.hashLen} {t : State} (hL : L.Ok) (hc : Ctx L g lr m₀ t) {j : Nat} (hj : 8 * j + 8 ≤ 48) :
    WP isa (.block [.addSp .r12 0, .load .d .r12 .r12 fTab, .load .d .r12 .r12 (8 * j)]) t fun t' =>
      Ctx L g lr m₀ t' ∧ t'.mem = t.mem ∧ t'.syms = t.syms ∧ (∀ r, r ≠ .r12 → t'.gpr r = t.gpr r) ∧
        t'.gpr .r12 = m₀.readW (L.tab + BitVec.ofNat 64 (8 * j)) 64 := by
  refine WP.of_syms (stepAddSp (by decide) fun t₁ k₁ m₁ v₁ => ?_)
  have hb : t₁.gpr .r12 = L.B + BitVec.ofNat 64 96 := by rw [v₁, hc.sp, BitVec.add_zero]
  refine stepLd (a := L.B + BitVec.ofNat 64 320) (by decide) (by decide) (by rw [hb, fr_add]; rfl)
    (hc.inFrK k₁ (by omega) (by omega)) fun t₂ k₂ m₂ v₂ => ?_
  have h12 : t₂.gpr .r12 = L.tab := by rw [v₂, m₁, hc.pTab]
  refine stepLd (a := L.tab + BitVec.ofNat 64 (8 * j)) (by decide) ⟨by omega, by omega⟩ (by rw [h12])
    (by rw [k₂.rd, k₂.wr, k₁.rd, k₁.wr]; exact hc.inTab hL hj) fun t₃ k₃ m₃ v₃ => wp_nil fun hsy => ?_
  have K : Kp [.r12] t t₃ := (k₁.trans k₂).trans k₃
  have hm : t₃.mem = t.mem := by rw [m₃, m₂, m₁]
  exact ⟨hc.kp hL K hm hsy, hm, hsy, fun r hr => K.gpr r (by simp [hr]), by rw [v₃, m₂, m₁, hc.tabWord hL hj]⟩

/-- The indirect call of the table's function `j`: in both runs of the same
function, `n`'s (the table's word `j` holds the layout's address of `n`). -/
theorem tcall_ct {Φ : Pred P} {j : Nat} (hj : 8 * j + 8 ≤ 48) (ht : TaintOk [.r12] [.load .d .r12 .r12 (8 * j)])
    {n : String} {c : Prog isa} {ts : List (String × Prog isa)} (hn : TabFn P j n c ts) (hΦ : R12 Φ)
    (hcall : RelCT isa (Two P Φ) (.call n c) fun _ _ => True) :
    RelCT isa (Two P Φ) (Cfg.tcall j ts) fun _ _ => True := by
  unfold Cfg.tcall
  have hb : RelCT isa (Two P Φ) (.block [.addSp .r12 0, .load .d .r12 .r12 fTab, .load .d .r12 .r12 (8 * j)])
      (Two P fun L g lr m₀ u => Φ L g lr m₀ u ∧ u.gpr .r12 = L.fa n ∧ u.syms n = L.fa n ∧
        ts.find? (fun q => u.syms q.1 == u.syms n) = some (n, c)) :=
    two_wp (two_split (pre := [.addSp .r12 0, .load .d .r12 .r12 fTab]) [.r12] (fun L _ => L.tab)
        ⟨_, by taint_decide⟩ (fun _ _ _ _ _ _ hc => tabPtr_ok hc) ht)
      fun L g lr m₀ t hL hq hc hφ => WP.mono (tblk_ok hL hc hj) fun u ⟨hc', hm, hs, hr, h12⟩ => by
        obtain ⟨hw, hf, hfa⟩ := hn L g lr m₀ t hL hq hc
        exact ⟨hc', hΦ _ _ _ _ _ _ hφ hr hm hs, by rw [h12, hw, hfa], by rw [hs, hfa], by rw [hs]; exact hf⟩
  refine hb.seq ?_
  cases ts with
  | nil => exact RelCT.of_false fun _ _ ⟨_, _, _, _, _, _, _, t⟩ => absurd t.f₁.2.2.2 (by simp)
  | cons q ts =>
    exact RelCT.icalls_of_call (hcall.mono (fun _ _ => Two.mono fun _ _ _ _ _ h => h.1) fun _ _ h => h)
      fun s₁ s₂ ⟨L, _, _, _, _, _, _, t⟩ => ⟨L.fa n, by simp only [PPC64LE.icall, t.f₁.2.1],
        by simp only [PPC64LE.icall, t.f₂.2.1],
        by show (q :: ts).find? (fun p => s₁.syms p.1 == L.fa n) = _; rw [← t.f₁.2.2.1]; exact t.f₁.2.2.2,
        by show (q :: ts).find? (fun p => s₂.syms p.1 == L.fa n) = _; rw [← t.f₂.2.2.1]; exact t.f₂.2.2.2, rfl⟩

theorem tw0 : TaintOk [.r12] [.load .d .r12 .r12 (8 * 0)] := ⟨_, by taint_decide⟩
theorem tw1 : TaintOk [.r12] [.load .d .r12 .r12 (8 * 1)] := ⟨_, by taint_decide⟩
theorem tw2 : TaintOk [.r12] [.load .d .r12 .r12 (8 * 2)] := ⟨_, by taint_decide⟩

/-! ## HMAC's calls -/

/-- The arguments of HMAC's `init`. -/
def IA (P : RfcHash) : Pred P := fun L _ _ _ u =>
  u.gpr .r3 = L.scr + BitVec.ofNat 64 0 ∧ u.gpr .r4 = L.scr + BitVec.ofNat 64 192 ∧
    u.gpr .r5 = L.B + BitVec.ofNat 64 128 ∧ u.gpr .r6 = BitVec.ofNat 64 P.v.H.D ∧
    u.gpr .r7 = L.scr + BitVec.ofNat 64 384

abbrev initRd (P : RfcHash) (L : Lay P.I.hashLen) : List Region := [⟨L.B + BitVec.ofNat 64 128, P.v.H.D⟩]
abbrev initWr (P : RfcHash) (L : Lay P.I.hashLen) : List Region :=
  [⟨L.scr + BitVec.ofNat 64 0, P.K.H.S⟩, ⟨L.scr + BitVec.ofNat 64 192, P.K.H.S⟩,
    ⟨L.scr + BitVec.ofNat 64 384, P.K.I.scratch * 8⟩]

theorem initAt {L : Lay P.I.hashLen} (hL : L.Ok) {u : State} (hcu : Ctx L g lr m₀ u) (ha : IA P L g lr m₀ u) :
    (Proof.Hmac.Instance.initScratchContract P.K.I PPC64LE.abi (P.K.kI + 1)).pre
        (u.callEntry.withRegions (initRd P L) (initWr P L)) ∧
      Covers (initRd P L ++ initWr P L) (u.rd ++ u.wr) ∧ Covers (initWr P L) u.wr := by
  obtain ⟨h3, h4, h5, h6, h7⟩ := ha
  have hnB := hL.nB
  have eS : P.K.H.S = P.v.H.S := rfl
  have eD : P.K.H.D = P.v.H.D := rfl
  have hS := P.K.hS
  have hSc := P.K.hScr
  simp only [sWork, sMsg] at hSc
  have hnc := hL.nc
  have hsp : u.sp = L.B + BitVec.ofNat 64 96 := hcu.sp
  have dS : ∀ {e k e' k' : Nat}, e + k ≤ e' ∨ e' + k' ≤ e → e' + k' ≤ 8192 → e + k ≤ 8192 →
      Region.Disjoint ⟨L.scr + BitVec.ofNat 64 e, k⟩ ⟨L.scr + BitVec.ofNat 64 e', k'⟩ :=
    fun h h₁ h₂ => Offset.disjoint _ h (by omega) (by omega)
  have kS : ∀ {e k : Nat}, e + k ≤ 8192 →
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 128, P.v.H.D⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
    fun h => hL.stk_scr (by nums) h
  have bS : ∀ {e k : Nat}, e + k ≤ 8192 → (below u.sp 96).Disjoint ⟨L.scr + BitVec.ofNat 64 e, k⟩ := fun h => by
    rw [hsp, L.below96]; exact hL.low_scr h
  have hDB : P.v.H.D ≤ P.v.H.B := by nums
  refine ⟨initPre P.K (inner := L.scr + BitVec.ofNat 64 0) (outer := L.scr + BitVec.ofNat 64 192)
    (key := L.B + BitVec.ofNat 64 128) (scr := L.scr + BitVec.ofNat 64 384) (kl := P.v.H.D) h3 h4 h5
    (by rw [h6, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by nums)]) h7
    (by show P.v.H.D ≤ P.v.I.S.H.blockSize; rw [P.v.hIS, P.v.l.ok.hB]; exact hDB)
    (dS (by nums) (by nums) (by nums)) (kS (by nums)).symm (dS (by nums) (by nums) (by nums))
    (kS (by nums)).symm (dS (by nums) (by nums) (by nums)) (kS (by nums))
    (by rw [hsp, hL.sp_toNat]; omega) (bS (by nums)) (bS (by nums))
    (by rw [hsp, L.below96]; exact Offset.base_disjoint _ (by omega) (by nums)) (bS (by nums))
    (by rw [Offset.toNat_add_ofNat]; nums) (by rw [Offset.toNat_add_ofNat]; nums)
    (by rw [Offset.toNat_add_ofNat]; nums) (by rw [Offset.toNat_add_ofNat]; nums), ?_, ?_⟩
  · exact hcu.covers fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨L.FR, by simp, within_fr _ (by omega) (by nums)⟩
      all_goals exact ⟨L.SCR, by simp, within_off _ (by nums)⟩
  · exact hcu.coversW fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact ⟨L.SCR, by simp, within_off _ (by nums)⟩

theorem init_call_ct : RelCT isa (Two P (IA P)) (.call P.v.initN P.v.H.init) fun _ _ => True :=
  two_call P.K.initV P.K.initCT (initRd P) (initWr P) (fun _ _ _ _ _ hL _ hc ha => initAt hL hc ha)
    fun _ _ _ _ _ _ _ u₁ u₂ h => by
      sig_pub [Proof.Hmac.Instance.initScratchContract, Proof.Hmac.initScratchContract,
        Proof.Hmac.initScratchSig, PPC64LE.abi, PPC64LE.argRegs, stackBelow]
      exact ⟨by rw [h.c₁.sp, h.c₂.sp], by rw [h.f₁.1, h.f₂.1], by rw [h.f₁.2.1, h.f₂.2.1],
        by rw [h.f₁.2.2.1, h.f₂.2.2.1], by rw [h.f₁.2.2.2.1, h.f₂.2.2.2.1], by rw [h.f₁.2.2.2.2, h.f₂.2.2.2.2]⟩

/-- The arguments of the streaming `update`: the inner state holding `cnt`
bytes, the `len` bytes at `da L`. -/
def UA (P : RfcHash) (cnt : Nat) (da : Lay P.I.hashLen → Addr) (len : Nat) : Pred P := fun L _ _ _ u =>
  u.gpr .r3 = L.scr + BitVec.ofNat 64 0 ∧ u.gpr .r4 = BitVec.ofNat 64 cnt ∧ u.gpr .r5 = da L ∧
    u.gpr .r6 = BitVec.ofNat 64 len ∧ u.gpr .r7 = L.scr + BitVec.ofNat 64 384

abbrev updRd (da : Lay P.I.hashLen → Addr) (len : Nat) (L : Lay P.I.hashLen) : List Region := [⟨da L, len⟩]
abbrev updWr (P : RfcHash) (L : Lay P.I.hashLen) : List Region :=
  [⟨L.scr + BitVec.ofNat 64 0, P.v.H.S⟩, ⟨L.scr + BitVec.ofNat 64 384, P.v.H.W⟩]

theorem updAt {cnt : Nat} {da : Lay P.I.hashLen → Addr} {len : Nat} {L : Lay P.I.hashLen} (hL : L.Ok) {u : State}
    (hcu : Ctx L g lr m₀ u) (ha : UA P cnt da len L g lr m₀ u) (hd : DataOk L (da L) len) :
    (Proof.Hmac.Stream.PPC64LE.updK P.v.H.S P.v.H.W P.v.l.ok.SH.Repr).pre
        (u.callEntry.withRegions (updRd da len L) (updWr P L)) ∧
      Covers (updRd da len L ++ updWr P L) (u.rd ++ u.wr) ∧ Covers (updWr P L) u.wr := by
  obtain ⟨h3, -, h5, h6, h7⟩ := ha
  have hnB := hL.nB
  have hS := P.K.hS
  have hSc := P.K.hScr
  simp only [sWork, sMsg] at hSc
  have hnc := hL.nc
  have hW := P.K.hW
  simp only [sWork, sMsg] at hW
  have hl := hd.len_le
  have hsp : u.sp = L.B + BitVec.ofNat 64 96 := hcu.sp
  have dS : ∀ {e k e' k' : Nat}, e + k ≤ e' ∨ e' + k' ≤ e → e' + k' ≤ 8192 → e + k ≤ 8192 →
      Region.Disjoint ⟨L.scr + BitVec.ofNat 64 e, k⟩ ⟨L.scr + BitVec.ofNat 64 e', k'⟩ :=
    fun h h₁ h₂ => Offset.disjoint _ h (by omega) (by omega)
  have bS : ∀ {e k : Nat}, e + k ≤ 8192 → (below u.sp 48).Disjoint ⟨L.scr + BitVec.ofNat 64 e, k⟩ := fun h => by
    rw [hsp, L.below48]; exact hL.stk_scr (by omega) h
  have c3 : u.callEntry.gpr .r3 = L.scr + BitVec.ofNat 64 0 := (State.callEntry_gpr _ (by decide)).trans h3
  have c5 : u.callEntry.gpr .r5 = da L := (State.callEntry_gpr _ (by decide)).trans h5
  have c6 : (u.callEntry.gpr .r6).toNat = len := by
    rw [State.callEntry_gpr _ (by decide), h6, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have c7 : u.callEntry.gpr .r7 = L.scr + BitVec.ofNat 64 384 := (State.callEntry_gpr _ (by decide)).trans h7
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.Hmac.Stream.PPC64LE.updK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.withRegions_sp, State.callEntry_sp, c3, c5, c6, c7]
    exact ⟨trivial, trivial, dS (by nums) (by nums) (by nums), hd.scr hL (by nums), hd.scr hL (by nums),
      by rw [hsp, hL.sp_toNat]; omega, bS (by nums), by rw [hsp, L.below48]; exact hd.low hL (by omega),
      bS (by nums)⟩
  · exact hcu.covers fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hd.within
      all_goals exact ⟨L.SCR, by simp, within_off _ (by nums)⟩
  · exact hcu.coversW fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨L.SCR, by simp, within_off _ (by nums)⟩

theorem upd_call_ct {cnt : Nat} {da : Lay P.I.hashLen → Addr} {len : Nat}
    (hd : ∀ L : Lay P.I.hashLen, L.Ok → DataOk L (da L) len) :
    RelCT isa (Two P (UA P cnt da len)) (.call P.v.H.updN P.v.H.updC) fun _ _ => True :=
  two_call P.v.l.ok.upd P.K.updCT (updRd da len) (updWr P)
    (fun L _ _ _ _ hL _ hc ha => updAt hL hc ha (hd L hL)) fun L _ _ _ _ _ _ u₁ u₂ h => by
      simp only [Proof.Hmac.Stream.PPC64LE.updK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
        State.callEntry_gpr _ (show Reg.r3 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r4 ∉ linkRegs by decide),
        State.callEntry_gpr _ (show Reg.r5 ∉ linkRegs by decide), State.callEntry_gpr _ (show Reg.r6 ∉ linkRegs by decide),
        State.callEntry_gpr _ (show Reg.r7 ∉ linkRegs by decide)]
      exact ⟨by rw [h.f₁.1, h.f₂.1], by rw [h.f₁.2.1, h.f₂.2.1], by rw [h.f₁.2.2.1, h.f₂.2.2.1],
        by rw [h.f₁.2.2.2.1, h.f₂.2.2.2.1], by rw [h.f₁.2.2.2.2, h.f₂.2.2.2.2], by rw [h.c₁.sp, h.c₂.sp]⟩

/-- The arguments of HMAC's `finalize`, for `cnt` bytes the inner state holds and the MAC to `dst`. -/
def FA (P : RfcHash) (cnt dst : Nat) : Pred P := fun L _ _ _ u =>
  u.gpr .r3 = L.scr + BitVec.ofNat 64 0 ∧ u.gpr .r4 = L.scr + BitVec.ofNat 64 192 ∧
    u.gpr .r5 = BitVec.ofNat 64 cnt ∧ u.gpr .r6 = L.B + BitVec.ofNat 64 (96 + dst) ∧
    u.gpr .r7 = L.scr + BitVec.ofNat 64 384

abbrev finRd (P : RfcHash) (L : Lay P.I.hashLen) : List Region := [⟨L.scr + BitVec.ofNat 64 192, P.K.H.S⟩]
abbrev finWr (P : RfcHash) (dst : Nat) (L : Lay P.I.hashLen) : List Region :=
  [⟨L.scr + BitVec.ofNat 64 0, P.K.H.S⟩, ⟨L.B + BitVec.ofNat 64 (96 + dst), P.K.H.D⟩,
    ⟨L.scr + BitVec.ofNat 64 384, P.K.I.scratch * 8⟩]

theorem finAt {cnt dst : Nat} (hdst : 32 ≤ dst ∧ dst + 64 ≤ 176) {L : Lay P.I.hashLen} (hL : L.Ok) {u : State}
    (hcu : Ctx L g lr m₀ u) (ha : FA P cnt dst L g lr m₀ u) :
    (Proof.Hmac.Instance.finalizeScratchContract P.K.I PPC64LE.abi (P.K.kF + 1)).pre
        (u.callEntry.withRegions (finRd P L) (finWr P dst L)) ∧
      Covers (finRd P L ++ finWr P dst L) (u.rd ++ u.wr) ∧ Covers (finWr P dst L) u.wr := by
  obtain ⟨h3, h4, -, h6, h7⟩ := ha
  obtain ⟨hd₁, hd₂⟩ := hdst
  have hnB := hL.nB
  have eS : P.K.H.S = P.v.H.S := rfl
  have eD : P.K.H.D = P.v.H.D := rfl
  have hS := P.K.hS
  have hSc := P.K.hScr
  simp only [sWork, sMsg] at hSc
  have hnc := hL.nc
  have hsp : u.sp = L.B + BitVec.ofNat 64 96 := hcu.sp
  have dS : ∀ {e k e' k' : Nat}, e + k ≤ e' ∨ e' + k' ≤ e → e' + k' ≤ 8192 → e + k ≤ 8192 →
      Region.Disjoint ⟨L.scr + BitVec.ofNat 64 e, k⟩ ⟨L.scr + BitVec.ofNat 64 e', k'⟩ :=
    fun h h₁ h₂ => Offset.disjoint _ h (by omega) (by omega)
  have oS : ∀ {e k : Nat}, e + k ≤ 8192 →
      Region.Disjoint ⟨L.B + BitVec.ofNat 64 (96 + dst), P.v.H.D⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
    fun h => hL.stk_scr (by nums) h
  have bS : ∀ {e k : Nat}, e + k ≤ 8192 → (below u.sp 96).Disjoint ⟨L.scr + BitVec.ofNat 64 e, k⟩ := fun h => by
    rw [hsp, L.below96]; exact hL.low_scr h
  refine ⟨finPre P.K (inner := L.scr + BitVec.ofNat 64 0) (outer := L.scr + BitVec.ofNat 64 192)
    (out := L.B + BitVec.ofNat 64 (96 + dst)) (scr := L.scr + BitVec.ofNat 64 384) h3 h4 h6 h7
    (dS (by nums) (by nums) (by nums)) (oS (by nums)).symm (dS (by nums) (by nums) (by nums))
    (oS (by nums)).symm (dS (by nums) (by nums) (by nums)) (oS (by nums))
    (by rw [hsp, hL.sp_toNat]; omega) (bS (by nums)) (bS (by nums))
    (by rw [hsp, L.below96]; exact Offset.base_disjoint _ (by omega) (by nums)) (bS (by nums))
    (by rw [Offset.toNat_add_ofNat]; nums) (by rw [Offset.toNat_add_ofNat]; nums)
    (by rw [Offset.toNat_add_ofNat]; nums) (by rw [Offset.toNat_add_ofNat]; nums), ?_, ?_⟩
  · exact hcu.covers fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨L.SCR, by simp, within_off _ (by nums)⟩
      · exact ⟨L.SCR, by simp, within_off _ (by nums)⟩
      · exact ⟨L.FR, by simp, within_fr _ (by omega) (by nums)⟩
      · exact ⟨L.SCR, by simp, within_off _ (by nums)⟩
  · exact hcu.coversW fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨L.SCR, by simp, within_off _ (by nums)⟩
      · exact ⟨L.FR, by simp, within_fr _ (by omega) (by nums)⟩
      · exact ⟨L.SCR, by simp, within_off _ (by nums)⟩

theorem fin_call_ct {cnt dst : Nat} (hdst : 32 ≤ dst ∧ dst + 64 ≤ 176) :
    RelCT isa (Two P (FA P cnt dst)) (.call P.v.finN P.v.H.finalize) fun _ _ => True :=
  two_call P.K.finV P.K.finCT (finRd P) (finWr P dst) (fun _ _ _ _ _ hL _ hc ha => finAt hdst hL hc ha)
    fun _ _ _ _ _ _ _ u₁ u₂ h => by
      sig_pub [Proof.Hmac.Instance.finalizeScratchContract, Proof.Hmac.finalizeScratchContract,
        Proof.Hmac.finalizeScratchSig, PPC64LE.abi, PPC64LE.argRegs, stackBelow]
      exact ⟨by rw [h.c₁.sp, h.c₂.sp], by rw [h.f₁.1, h.f₂.1], by rw [h.f₁.2.1, h.f₂.2.1],
        by rw [h.f₁.2.2.1, h.f₂.2.2.1], by rw [h.f₁.2.2.2.1, h.f₂.2.2.2.1], by rw [h.f₁.2.2.2.2, h.f₂.2.2.2.2]⟩

theorem r12_ia : R12 (IA P) := fun _ _ _ _ _ _ ⟨a, b, c, d, e⟩ hr _ _ => ⟨(hr _ (by decide)).trans a,
  (hr _ (by decide)).trans b, (hr _ (by decide)).trans c, (hr _ (by decide)).trans d, (hr _ (by decide)).trans e⟩

theorem r12_ua {cnt : Nat} {da : Lay P.I.hashLen → Addr} {len : Nat} : R12 (UA P cnt da len) :=
  fun _ _ _ _ _ _ ⟨a, b, c, d, e⟩ hr _ _ => ⟨(hr _ (by decide)).trans a, (hr _ (by decide)).trans b,
    (hr _ (by decide)).trans c, (hr _ (by decide)).trans d, (hr _ (by decide)).trans e⟩

theorem r12_fa {cnt dst : Nat} : R12 (FA P cnt dst) :=
  fun _ _ _ _ _ _ ⟨a, b, c, d, e⟩ hr _ _ => ⟨(hr _ (by decide)).trans a, (hr _ (by decide)).trans b,
    (hr _ (by decide)).trans c, (hr _ (by decide)).trans d, (hr _ (by decide)).trans e⟩

/-! ## HMAC through the table -/

theorem initArgs_taint : TaintOk [] Cfg.initArgs := ⟨_, by taint_decide⟩
theorem updVArgs_taint : TaintOk [] Cfg.updVArgs := ⟨_, by taint_decide⟩
theorem updMArgs_taint (len : Nat) : TaintOk [] (Cfg.updMArgs len) :=
  taintOk_erase (is₀ := Cfg.updMArgs 0) ⟨_, by taint_decide⟩ rfl
theorem finV_taint : TaintOk [] (Cfg.finArgs 0 fV) := ⟨_, by taint_decide⟩
theorem finR_taint : TaintOk [] (Cfg.finArgs 1 fK) := ⟨_, by taint_decide⟩

/-- HMAC's states for `K`. -/
theorem initK_ct {Φ : Pred P} : RelCT isa (Two P Φ) (cfgOf P).initK fun _ _ => True :=
  (two_wp (Ψ := IA P) (two_blk initArgs_taint) fun _ _ _ _ _ hL hq hc _ =>
    WP.mono (initArgs_ok hL hq.2 hc) fun _ ⟨c, _, _, a⟩ => ⟨c, a⟩).seq
    (tcall_ct (by decide) tw0 tfn_init r12_ia init_call_ct)

/-- The inner state updated with `V`. -/
theorem updV_ct {Φ : Pred P} : RelCT isa (Two P Φ) (cfgOf P).updV fun _ _ => True :=
  (two_wp (Ψ := UA P P.v.H.B (fun L => L.B + BitVec.ofNat 64 192) P.v.H.D) (two_blk updVArgs_taint)
    fun _ _ _ _ _ hL hq hc _ => WP.mono (updVArgs_ok hL hq.2 hc) fun _ ⟨c, _, _, a⟩ => ⟨c, a⟩).seq
    (tcall_ct (by decide) tw1 tfn_upd r12_ua (upd_call_ct fun L _ => .inl ⟨192, rfl, by omega, by nums⟩))

/-- The inner state updated with the message's `len` bytes. -/
theorem updM_ct {Φ : Pred P} {len : Nat} (hlen : len ≤ 256) :
    RelCT isa (Two P Φ) ((cfgOf P).updM len) fun _ _ => True :=
  (two_wp (Ψ := UA P (P.v.H.B + P.v.H.D) (fun L => L.scr + BitVec.ofNat 64 sMsg) len) (two_blk (updMArgs_taint len))
    fun _ _ _ _ _ hL hq hc _ => WP.mono (updMArgs_ok hL hq.2 hc (len := len) (by omega))
      fun _ ⟨c, _, _, a⟩ => ⟨c, a⟩).seq
    (tcall_ct (by decide) tw1 tfn_upd r12_ua
      (upd_call_ct fun L _ => .inr ⟨sMsg, rfl, by decide, by simp only [sMsg]; omega⟩))

/-- The MAC, of `D + len` bytes of text, to the frame at `dst`. -/
theorem fin_ct {Φ : Pred P} {len dst : Nat} (hlen : len < 2 ^ 14) (hdst : 32 ≤ dst ∧ dst + 64 ≤ 176)
    (ht : TaintOk [] (Cfg.finArgs len dst)) :
    RelCT isa (Two P Φ) ((cfgOf P).fin len dst) fun _ _ => True :=
  (two_wp (Ψ := FA P (P.v.H.B + P.v.H.D + len) dst) (two_blk ht) fun _ _ _ _ _ hL hq hc _ =>
    WP.mono (finArgs_ok hL hq.2 hc (len := len) (dst := dst) (by omega) (by omega))
      fun _ ⟨c, _, _, a⟩ => ⟨c, a⟩).seq
    (tcall_ct (by decide) tw2 tfn_fin r12_fa (fin_call_ct hdst))

/-! ## The states' copies -/

theorem scrBase_taint : TaintOk [] Cfg.scrBase := ⟨_, by taint_decide⟩

/-- `scratch` in `r12`. -/
theorem scrBase_two {L : Lay P.I.hashLen} {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block Cfg.scrBase) t fun t' => t'.sp = t.sp ∧ ∀ r ∈ [Reg.r12], t'.gpr r = L.scr := by
  rw [show Cfg.scrBase = Cfg.scrBase ++ [] from rfl]
  exact scrBase_ok hc fun t' k _ _ h12 => wp_nil ⟨k.sp, fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h12⟩

theorem copyStates_taint (b : Bool) : TaintOk [.r12] (Cfg.copyStates b) := by
  cases b
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩

theorem save_ct {Φ : Pred P} : RelCT isa (Two P Φ) (.block Cfg.save) fun _ _ => True :=
  two_split [.r12] (fun L _ => L.scr) scrBase_taint (fun _ _ _ _ _ _ hc => scrBase_two hc) (copyStates_taint true)

theorem restore_ct {Φ : Pred P} : RelCT isa (Two P Φ) (.block Cfg.restore) fun _ _ => True :=
  two_split [.r12] (fun L _ => L.scr) scrBase_taint (fun _ _ _ _ _ _ hc => scrBase_two hc) (copyStates_taint false)

/-! ## HMAC -/

/-- HMAC's states for some key, holding `text` of `n` bytes. -/
def StN (P : RfcHash) (n : Nat) : Pred P := fun L g lr m₀ u => ∃ k0 text, St P L g lr m₀ k0 text u ∧ text.length = n

/-- `V = HMAC_K(V)`, saving the states for `K`. -/
theorem hmacVS_ct {Φ : Pred P} : RelCT isa (Two P Φ) (cfgOf P).hmacVS fun _ _ => True := by
  unfold Cfg.hmacVS
  refine (two_wp (Ψ := StN P 0) initK_ct fun L g lr m₀ t hL hq hc _ =>
    WP.mono (init_step hL hq.2 hc) fun u ⟨hu, _⟩ => ⟨hu.ctx, _, _, hu, rfl⟩).seq ?_
  refine (two_wp (Ψ := StN P 0) save_ct fun L g lr m₀ t hL hq hc ⟨k0, text, hu, hl⟩ => by
    obtain rfl := List.eq_nil_of_length_eq_zero hl
    exact WP.mono (save_ok hL hu) fun u ⟨hu', _⟩ => ⟨hu'.ctx, _, _, hu', rfl⟩).seq ?_
  refine (two_wp (Ψ := StN P P.v.H.D) updV_ct fun L g lr m₀ t hL hq hc ⟨k0, text, hu, hl⟩ => by
    obtain rfl := List.eq_nil_of_length_eq_zero hl
    exact WP.mono (updV_step hL hq.2 hu) fun u ⟨hu', _⟩ => ⟨hu'.ctx, _, _, hu', length_bytesAt _ _ _⟩).seq ?_
  exact fin_ct (by decide) (by simp only [fV]; omega) finV_taint

/-- `V = HMAC_K(V)`, from the saved states for `K`. -/
theorem hmacVR_ct :
    RelCT isa (Two P fun L _ _ _ t => SavedK P L t.mem (kOf P L t.mem)) (cfgOf P).hmacVR fun _ _ => True := by
  unfold Cfg.hmacVR
  refine (two_wp (Ψ := StN P 0) restore_ct fun L g lr m₀ t hL hq hc hS =>
    WP.mono (restore_ok hL hc hS (blockKey_length (keyOf_length _))) fun u ⟨hu, _⟩ =>
      ⟨hu.ctx, _, _, hu, rfl⟩).seq ?_
  refine (two_wp (Ψ := StN P P.v.H.D) updV_ct fun L g lr m₀ t hL hq hc ⟨k0, text, hu, hl⟩ => by
    obtain rfl := List.eq_nil_of_length_eq_zero hl
    exact WP.mono (updV_step hL hq.2 hu) fun u ⟨hu', _⟩ => ⟨hu'.ctx, _, _, hu', length_bytesAt _ _ _⟩).seq ?_
  exact fin_ct (by decide) (by simp only [fV]; omega) finV_taint

/-- `K = HMAC_K(V ‖ m)`, for the message's `len` bytes, from the states for
`K` by `init` or, if `fresh` is false, the saved ones. -/
theorem hmacK_ct {len : Nat} (hlen : len ≤ 256) (fresh : Bool) (ht : TaintOk [] (Cfg.finArgs len fK)) :
    RelCT isa (Two P fun L _ _ _ t => fresh = false → SavedK P L t.mem (kOf P L t.mem))
      ((cfgOf P).hmacK fresh len) fun _ _ => True := by
  unfold Cfg.hmacK
  refine RelCT.seq (R := Two P (StN P 0)) ?_ ?_
  · cases fresh
    · exact two_wp (restore_ct) fun L g lr m₀ t hL hq hc hS =>
        WP.mono (restore_ok hL hc (hS rfl) (blockKey_length (keyOf_length _))) fun u ⟨hu, _⟩ =>
          ⟨hu.ctx, _, _, hu, rfl⟩
    · exact two_wp initK_ct fun L g lr m₀ t hL hq hc _ =>
        WP.mono (init_step hL hq.2 hc) fun u ⟨hu, _⟩ => ⟨hu.ctx, _, _, hu, rfl⟩
  refine (two_wp (Ψ := StN P P.v.H.D) updV_ct fun L g lr m₀ t hL hq hc ⟨k0, text, hu, hl⟩ => by
    obtain rfl := List.eq_nil_of_length_eq_zero hl
    exact WP.mono (updV_step hL hq.2 hu) fun u ⟨hu', _⟩ => ⟨hu'.ctx, _, _, hu', length_bytesAt _ _ _⟩).seq ?_
  refine (two_wp (Ψ := StN P (P.v.H.D + len)) (updM_ct hlen) fun L g lr m₀ t hL hq hc ⟨k0, text, hu, hl⟩ =>
    WP.mono (updM_step hL hq.2 hu hl hlen) fun u ⟨hu', _⟩ =>
      ⟨hu'.ctx, _, _, hu', by rw [List.length_append, hl, length_bytesAt]⟩).seq ?_
  exact fin_ct (by omega) (by simp only [fK]; omega) ht

/-! ## `K` and `V` from a message -/

/-- The pointers `msgPtrs` loads. -/
def msgP (L : Lay P.I.hashLen) : Reg → BitVec 64
  | .r9 => L.scr
  | .r10 => L.d
  | _ => L.B + BitVec.ofNat 64 96

theorem msgPtrs_taint : TaintOk [] Cfg.msgPtrs := ⟨_, by taint_decide⟩

theorem msgPtrs_two {L : Lay P.I.hashLen} {t : State} (hL : L.Ok) (hc : Ctx L g lr m₀ t) :
    WP isa (.block Cfg.msgPtrs) t fun t' => t'.sp = t.sp ∧ ∀ r ∈ [Reg.r9, .r10, .r11], t'.gpr r = msgP L r :=
  WP.mono (msgPtrs_ok hL hc) fun _ ⟨c, _, _, h11, h9, h10⟩ => ⟨c.sp.trans hc.sp.symm, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h9
    · exact h10
    · exact h11⟩

/-- What a message keeps: the saved states, and `K`. -/
def KS (P : RfcHash) (b : Prop) : Pred P := fun L _ _ _ t => b → SavedK P L t.mem (kOf P L t.mem)

theorem msg_keeps {L : Lay P.I.hashLen} (hL : L.Ok) {m m' : Mem}
    (hf : Frame [⟨L.scr + BitVec.ofNat 64 2256, 1 + 2 * P.Q⟩] m m') {b : Prop}
    (h : b → SavedK P L m (kOf P L m)) : b → SavedK P L m' (kOf P L m') := fun hb => by
  have hQ := Q_le P
  have hnB := hL.nB
  have hk : kOf P L m' = kOf P L m := bytesAt_frame hf (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hL.stk_scr (by nums) (by omega)) (by nums)
  rw [hk]
  exact (h hb).frame (blockKey_length (keyOf_length _)) hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)

/-- `K = HMAC_K(V ‖ b (‖ d ‖ h))`, then `V = HMAC_K(V)`. -/
theorem rekey_gen_ct {b : Nat} (hb : b < 2 ^ 15) {full : Bool} (fresh : Bool)
    (tm : TaintOk [.r9, .r10, .r11] ((cfgOf P).msg b full)) (hl : mlen P full ≤ 256)
    (ht : TaintOk [] (Cfg.finArgs (mlen P full) fK)) :
    RelCT isa (Two P (KS P (fresh = false))) (.seq (.block Cfg.msgPtrs) (.seq (.block ((cfgOf P).msg b full))
      (.seq ((cfgOf P).hmacK fresh (mlen P full)) (cfgOf P).hmacVS))) fun _ _ => True := by
  refine (two_wp (Ψ := fun L g lr m₀ t => KS P (fresh = false) L g lr m₀ t ∧ ∀ r ∈ [Reg.r9, .r10, .r11],
      t.gpr r = msgP L r) (two_blk msgPtrs_taint) fun L g lr m₀ t hL hq hc hS =>
    WP.mono (msgPtrs_ok hL hc) fun u ⟨c, hm, _, h11, h9, h10⟩ => ⟨c, by rw [KS, hm]; exact hS, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h9
      · exact h10
      · exact h11⟩).seq ?_
  refine (two_wp (Ψ := KS P (fresh = false)) (two_regs [.r9, .r10, .r11] msgP (fun _ _ _ _ _ h => h.2) tm)
    fun L g lr m₀ t hL hq hc ⟨hS, hr⟩ => WP.mono (msg_ok hL hq.1 hc (hr .r11 (by simp)) (hr .r9 (by simp))
      (hr .r10 (by simp)) hb full) fun u ⟨c, hf, _⟩ => ⟨c, msg_keeps hL hf hS⟩).seq ?_
  refine (two_wp (Ψ := Tt P) (hmacK_ct hl fresh ht) fun L g lr m₀ t hL hq hc hS =>
    WP.mono (hmacKB_ok hL hq.2 hc hl fresh hS) fun _ h => ⟨h.1, trivial⟩).seq ?_
  exact hmacVS_ct

theorem msgF_taint (B : RfcT (cfgP P)) (b : Nat) : TaintOk [.r9, .r10, .r11] ((cfgOf P).msg b true) :=
  taintOk_erase (is₀ := (cfgP P).msg 0 true) B.msgF rfl

theorem msgN_taint : TaintOk [.r9, .r10, .r11] ((cfgOf P).msg 0 false) :=
  taintOk_erase (is₀ := [.li .r8 0, .stb .r8 .r9 sMsg]) ⟨_, by taint_decide⟩ rfl

theorem rekeyFull_ct (B : RfcT (cfgP P)) (b : Nat) (hb : b < 2 ^ 15) :
    RelCT isa (Two P (KS P (b ≠ 0))) ((cfgOf P).rekeyFull b) fun _ _ => True := by
  have hl : mlen P true ≤ 256 := by simp only [mlen, ite_true]; have := Q_le P; omega
  unfold Cfg.rekeyFull
  exact (rekey_gen_ct hb (decide (b = 0)) (msgF_taint B b) hl (by exact B.finM)).mono
    (fun _ _ => Two.mono fun _ _ _ _ _ h h' => h (by simpa using h')) fun _ _ h => h

theorem rekey_ct {Φ : Pred P} : RelCT isa (Two P Φ) (cfgOf P).rekey fun _ _ => True := by
  unfold Cfg.rekey
  exact (rekey_gen_ct (b := 0) (full := false) (by decide) true msgN_taint (by simp [mlen]) finR_taint).mono
    (fun _ _ => Two.mono fun _ _ _ _ _ _ h => absurd h (by decide)) fun _ _ h => h

/-! ## The byte loops and the conversions -/

theorem copyLoop_taint :
    ∃ hc, (VG.Taint.check taint (Taint.ofRegs [.r4, .r5, .r6]) Impl.RsaOaep.PPC64LE.copyLoop hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- A byte copy's registers. -/
abbrev CpA (P : RfcHash) (p q : Lay P.I.hashLen → Addr) (n : Nat) : Pred P := fun L _ _ _ u =>
  u.gpr .r4 = q L ∧ u.gpr .r5 = p L ∧ u.gpr .r6 = BitVec.ofNat 64 n

/-- The value of each register of a copy. -/
def cpF (p q : Lay P.I.hashLen → Addr) (n : Nat) (L : Lay P.I.hashLen) : Reg → BitVec 64
  | .r4 => q L
  | .r5 => p L
  | _ => BitVec.ofNat 64 n

/-- The byte loop, from registers that agree. -/
theorem cp_ct {Φ : Pred P} {p q : Lay P.I.hashLen → Addr} {n : Nat}
    (h : ∀ L g lr m₀ u, Φ L g lr m₀ u → CpA P p q n L g lr m₀ u) :
    RelCT isa (Two P Φ) Impl.RsaOaep.PPC64LE.copyLoop fun _ _ => True :=
  two_prog [.r4, .r5, .r6] (cpF p q n) (fun _ _ _ _ _ hf r hr => by
    obtain ⟨a, b, c⟩ := h _ _ _ _ _ hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact a
    · exact b
    · exact c) copyLoop_taint

/-- `scratch` in `r3`. -/
def ScrIn (P : RfcHash) : Pred P := fun L _ _ _ u => u.gpr .r3 = L.scr

theorem ldScr_taint : TaintOk [] [.addSp .r11 0, .load .d .r3 .r11 fScratch] := ⟨_, by taint_decide⟩

theorem ldScr_two {L : Lay P.I.hashLen} {t : State} (hc : Ctx L g lr m₀ t) :
    WP isa (.block [.addSp .r11 0, .load .d .r3 .r11 fScratch]) t fun t' =>
      t'.sp = t.sp ∧ ∀ r ∈ [Reg.r3], t'.gpr r = L.scr := by
  refine stepAddSp (by decide) fun t₁ k₁ m₁ v₁ => ?_
  have hb : t₁.gpr .r11 = L.B + BitVec.ofNat 64 96 := by rw [v₁, hc.sp, BitVec.add_zero]
  refine stepLd (a := L.B + BitVec.ofNat 64 272) (by decide) (by decide) (by rw [hb, fr_add]; rfl)
    (hc.inFrK k₁ (by omega) (by omega)) fun t₂ k₂ m₂ v₂ => wp_nil ⟨by rw [k₂.sp, k₁.sp], fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr; subst hr
  rw [v₂, m₁, hc.pScr]

/-- A conversion: its block addresses memory from `scratch`, loaded first, and `sp`. -/
theorem conv_ct {Φ : Pred P} {o s : Nat} (h : TaintOk [.r3] ((cfgOf P).convBody o s)) :
    RelCT isa (Two P Φ) (.block ((cfgOf P).conv o s)) fun _ _ => True :=
  two_split [.r3] (fun L _ => L.scr) ldScr_taint (fun _ _ _ _ _ _ hc => ldScr_two hc) h

/-! ## The candidate -/

/-- After `j` of the candidate's `V`s, from some `K` and `V`. -/
def CJ (P : RfcHash) (j : Nat) : Pred P := fun L g lr m₀ u => ∃ t₀ K V₀, CI P L g lr m₀ t₀ K V₀ j u

theorem keepArgs_taint : TaintOk [] Cfg.keepArgs := ⟨_, by taint_decide⟩
theorem tStep_taint (c : Cfg) : TaintOk [] c.tStep :=
  taintOk_erase (is₀ := (cfgC 0 0 false 0 0).tStep) ⟨_, by taint_decide⟩ rfl

/-- `T`'s length, `j` blocks. -/
abbrev TL (P : RfcHash) (j : Nat) : Pred P := fun L _ _ _ u => tlen L u.mem = BitVec.ofNat 64 (j * P.v.H.D)

/-- One `V`'s blocks and calls leak the same in both runs. -/
theorem candStep_trace {j : Nat} (hj : (j + 1) * P.v.H.D ≤ 136) :
    RelCT isa (Two P (CJ P j)) (cfgOf P).candStep fun _ _ => True := by
  have hs := P.sizes
  have hjD : (j + 1) * P.v.H.D = j * P.v.H.D + P.v.H.D := Nat.succ_mul _ _
  unfold Cfg.candStep
  have s₁ : RelCT isa (Two P (CJ P j)) (cfgOf P).hmacVR (Two P (TL P j)) :=
    two_wp (hmacVR_ct.mono (fun _ _ => Two.mono fun _ _ _ _ _ ⟨_, _, _, hI⟩ => by
      rw [hI.k]; exact hI.saved) fun _ _ h => h) fun L g lr m₀ t hL hq hc ⟨_, _, _, hI⟩ => by
    have hS : SavedK P L t.mem (kOf P L t.mem) := by rw [hI.k]; exact hI.saved
    refine WP.mono (hmacVR_ok hL hq.2 hc hS) fun u ⟨hc₁, hf₁, _⟩ => ⟨hc₁, ?_⟩
    show tlen L u.mem = _
    rw [← hI.len]
    have := hL.nB
    exact hf₁.readW (Region.contains_self _ _) (fun r hr => by
      simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_SCR (by simp only [fTlen]; omega)
      · exact Offset.disjoint_base _ (by simp only [fTlen]; omega) (by simp only [fTlen]; omega)) (by decide)
  refine s₁.seq ?_
  rw [show Cfg.keepArgs = Cfg.keepArgs ++ [] from rfl]
  refine (two_wp (Ψ := fun L g lr m₀ u => CpA P (fun L => L.B + BitVec.ofNat 64 (96 + fT + j * P.v.H.D))
      (fun L => L.B + BitVec.ofNat 64 (96 + fV)) P.v.H.D L g lr m₀ u ∧ TL P j L g lr m₀ u)
    (two_blk (by simpa using keepArgs_taint)) fun L g lr m₀ t hL hq hc hl =>
      WP.of_syms (keepArgs_ok hq.2 hc hl fun u k hm h4 h5 h6 => wp_nil fun hsy =>
        ⟨hc.kp hL k hm hsy, ⟨h4, h5, h6⟩, by show tlen L u.mem = _; rw [hm]; exact hl⟩)).seq ?_
  refine (two_wp (Ψ := TL P j) (cp_ct fun _ _ _ _ _ h => h.1) fun L g lr m₀ t hL hq hc ⟨⟨h4, h5, h6⟩, hl⟩ => ?_).seq
    (two_blk (tStep_taint _))
  have hnB := hL.nB
  refine WP.mono (cp_ok hL hc (p := L.B + BitVec.ofNat 64 (96 + fT + j * P.v.H.D))
      (q := L.B + BitVec.ofNat 64 (96 + fV)) (n := P.v.H.D) (by omega) (by omega) h4 h5 h6
      (fun i hi => by
        obtain ⟨R, hR, h⟩ := hc.inFrW (d := 96 + fT + j * P.v.H.D + i) (n := 1) (by simp only [fT]; omega)
          (by simp only [fT]; omega)
        exact ⟨R, hR, by rw [Offset.add_add]; exact h⟩)
      (safe_high L (by simp only [fT]; omega) (by simp only [fT]; omega))
      (fun i hi => by
        obtain ⟨R, hR, h⟩ := hc.inFr (d := 96 + fV + i) (n := 1) (by simp only [fV]; omega) (by simp only [fV]; omega)
        exact ⟨R, hR, by rw [Offset.add_add]; exact h⟩)
      (Offset.disjoint _ (.inl (by simp only [fV, fT]; omega)) (by simp only [fV]; omega) (by simp only [fT]; omega))
      (by rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (by simp only [fT]; omega),
        Nat.mod_eq_of_lt (by simp only [fT]; omega)]; simp only [fT]; omega)) fun u ⟨hcu, _, hf, _⟩ => ⟨hcu, ?_⟩
  show tlen L u.mem = _
  rw [← hl]
  exact hf.readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint _ (.inl (by simp only [fTlen, fT]; omega)) (by simp only [fTlen]; omega)
      (by simp only [fT]; omega)) (by decide)

end VG.Proof.Ecdsa.Rfc6979.PPC64LE

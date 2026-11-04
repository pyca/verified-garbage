module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Correct
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Reduce
public import VerifiedGarbage.Proof.Framework.Arm.TaintErase
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Regs
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.ICall
import VerifiedGarbage.Proof.Weierstrass.Layout
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Correct
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Reduce
meta import VerifiedGarbage.Proof.Framework.Arm.TaintErase
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Regs
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.ICall
meta import VerifiedGarbage.Proof.Weierstrass.Layout
import VerifiedGarbage.Proof.Framework.Arm.Reduce

/-!
# Deterministic ECDSA on 32-bit ARM: constant time, up to the number of candidates

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/CT.lean`): two runs whose public
data agree have the same layout, and stop at the same candidate (`exitAt`,
from the contract's leakage: the number of candidates RFC 6979 tries).
Between the prologue and the frame's release they are related by `Two`: both
satisfy `Ctx` with that layout (and `Φ`, what the next piece needs). The
blocks address only the frame and the buffers, from the registers that hold
the pointers, which agree (the taint analysis, of the blocks for each size
of hash function: `HashT`, and of the curve's and hash function's together:
each curve's `RfcCurve.blkT`); an indirect call reaches, through the table,
whose address `r4` holds, the same function in both runs (`reach_icalls`,
`reach_frame`: the table holds the functions whose addresses the layout
has); each call, in its frame, is of constant-time code whose public data
agree (`init_rel`, `upd_rel`, `fin_rel`, `frame2_rel`); and the loop's
branch agrees, since in both runs it goes on after candidate `i` iff `i` is
before the candidate it stops at (`go_iff`). The prologue's first
instruction reads `sp`, which agrees (`start_blk`), and the frame's
allocation and release access no memory (`alloc_ct`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Impl.Pbkdf2.Stream.Arm (scrAt)
open VG.Proof.Pbkdf2.Whole.Arm (frame2_rel)

/-! ## Frames and single instructions -/

/-- Allocating and freeing a buffer leaks no addresses. -/
theorem alloc_ct {bytes : Nat} {body : Prog isa} {P R : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s t, P s t ∧ a = allocated bytes s ∧ b = allocated bytes t) body R) :
    RelCT isa P (.frame (.alloc bytes) body (.free bytes)) fun _ _ => True := by
  intro s t ts tt s' t' hp es et
  have alloc_eq : ∀ {a b : State}, isa.push (.alloc bytes) a = some b → b = allocated bytes a := by
    intro a b h
    simp only [isa, push] at h
    split at h <;> cases h
    rfl
  cases es with
  | frame ps bs qs =>
    cases et with
    | frame pt bt qt =>
      have ea := alloc_eq ps
      have eb := alloc_eq pt
      subst ea eb
      obtain ⟨rfl, _⟩ := hb _ _ _ _ _ _ ⟨s, t, hp, rfl, rfl⟩ bs bt
      exact ⟨rfl, trivial⟩

/-- An instruction that leaks the same in two runs, then a block. -/
theorem block_cons_ct {i : Instr} {is : List Instr} {P R Q : State → State → Prop}
    (hi : ∀ a b a' b', P a b → exec i a = some a' → exec i b = some b' →
      addrs i a = addrs i b ∧ R a' b')
    (ht : RelCT isa R (.block is) Q) : RelCT isa P (.block (i :: is)) Q := by
  intro a b ta tb a' b' hp ea eb
  cases ea with | block ea =>
    cases eb with | block eb =>
      cases ha : exec i a with
      | none => simp only [execBlock, ha, reduceCtorEq] at ea
      | some u =>
        cases hb : exec i b with
        | none => simp only [execBlock, hb, reduceCtorEq] at eb
        | some v =>
          simp only [execBlock, ha, hb, Option.map_eq_some_iff,
            Prod.exists, Prod.mk.injEq] at ea eb
          obtain ⟨u', tr, eu, rfl, rfl⟩ := ea
          obtain ⟨v', ts, ev, rfl, rfl⟩ := eb
          obtain ⟨he, hr⟩ := hi a b u v hp ha hb
          obtain ⟨rfl, hq⟩ := ht _ _ _ _ _ _ hr (.block eu) (.block ev)
          exact ⟨by rw [he], hq⟩

/-! ## The taint of the registers that hold pointers -/

theorem agree_regs {rs : List Reg} {s₁ s₂ : State} (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    VG.Arm.Taint.Agree (τr rs) s₁ s₂ where
  rf := ⟨fun r hr => h r (RegSet.mem_ofList.mp hr), fun h => by cases h⟩
  wr h := absurd rfl h
  wf₁ := ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim, fun h => absurd h (Nat.lt_irrefl 0),
    fun _ h => (List.not_mem_nil h).elim⟩
  wf₂ := ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim, fun h => absurd h (Nat.lt_irrefl 0),
    fun _ h => (List.not_mem_nil h).elim⟩
  ok _ h := (List.not_mem_nil h).elim
  slots _ h := (List.not_mem_nil h).elim
  sp h := absurd h (Nat.lt_irrefl 0)
  argMem _ h := absurd h (Nat.not_lt_zero _)

/-- The taint check of a block is that of any block with the same
instructions but for the offsets of loads and stores and the immediates of
`movw` (`Taint.check_eraseOff`). -/
theorem taint_erase {rs : List Reg} {is is₀ : List Instr}
    (h : ∃ hc, (VG.Taint.check taint (τr rs) (.block is₀) hc).isSome = true)
    (he : is.map Instr.eraseOff = is₀.map Instr.eraseOff) :
    ∃ hc, (VG.Taint.check taint (τr rs) (.block is) hc).isSome = true := by
  obtain ⟨hc, hs⟩ := h
  have hb : Taint.NoBase (τr rs) := ⟨rfl, rfl⟩
  have e := Taint.check_eraseOff (.block is) hc hb
  have e₀ := Taint.check_eraseOff (.block is₀) hc hb
  have he' : Code.eraseOff (.block is) = Code.eraseOff (.block is₀) := congrArg Code.block he
  exact ⟨hc, e ▸ he' ▸ e₀ ▸ hs⟩

theorem taintOk_erase {is is₀ : List Instr} (h : TaintOk is₀) (he : is.map Instr.eraseOff = is₀.map Instr.eraseOff) :
    TaintOk is := taint_erase h he

theorem copyN_erase (k : Nat) (src : Reg) (so : Nat) (dst : Reg) (d so' d' : Nat) :
    (Cfg.copyN k src so dst d).map Instr.eraseOff = (Cfg.copyN k src so' dst d').map Instr.eraseOff := by
  unfold Cfg.copyN
  rw [List.map_flatMap, List.map_flatMap]
  rfl

/-! ## Two runs -/

/-- What each of two runs has, between the prologue and the frame's release. -/
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

theorem sp_two {dn : Nat} {L : Lay dn} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}
    (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) : t₁.sp = t₂.sp :=
  c₁.sp.trans c₂.sp.symm

/-- The registers that hold the pointers agree. -/
theorem ptr_two {dn : Nat} {L : Lay dn} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}
    (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) : ∀ r ∈ ptrRegs, t₁.gpr r = t₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [c₁.r4, c₂.r4]
  · rw [c₁.r5, c₂.r5]
  · rw [c₁.r6, c₂.r6]
  · rw [c₁.r8, c₂.r8]
  · rw [c₁.r11, c₂.r11]

/-- A block whose addresses depend only on the registers that hold pointers. -/
theorem two_blk {is : List Instr} {Φ : Pred P} (h : TaintOk is) : RelCT isa (Two P Φ) (.block is) fun _ _ => True :=
  let ⟨_, h⟩ := h
  VG.RelCT.taint (A := taint) (τr ptrRegs) (fun _ _ ⟨_, _, _, _, c₁, c₂, _, _⟩ => agree_regs (ptr_two c₁ c₂)) h

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

theorem pre {Φ' : Pred P} (h : Piece P Φ c Ψ) (hp : ∀ L g m₀ t, Φ' L g m₀ t → Φ L g m₀ t) : Piece P Φ' c Ψ :=
  ⟨h.ct.mono (fun _ _ => Two.mono hp) fun _ _ h => h, fun L g m₀ t hL hk hc hφ =>
    h.wp L g m₀ t hL hk hc (hp _ _ _ _ hφ)⟩

/-- What the relational proofs of the loop use. -/
theorem rel (h : Piece P Φ c Ψ) {Φ' : Pred P} (hp : ∀ L g m₀ t, Φ' L g m₀ t → Φ L g m₀ t) :
    RelCT isa (Two P Φ') c fun _ _ => True :=
  h.ct.mono (fun _ _ => Two.mono hp) fun _ _ _ => trivial

end Piece

/-- A block whose addresses depend only on the registers that hold pointers. -/
theorem Piece.blk {is : List Instr} {Φ Ψ : Pred P} (ht : TaintOk is)
    (hw : ∀ (L : Lay P.I.hashLen) g m₀ (t : State), L.Ok → CoreOk P L → Ctx L g m₀ t → Φ L g m₀ t →
      WP isa (.block is) t fun t' => Ctx L g m₀ t' ∧ Ψ L g m₀ t') : Piece P Φ (.block is) Ψ :=
  Piece.of (two_blk ht) hw

/-! ## The blocks that depend only on the hash function's sizes -/

/-- A configuration with only a hash function's output length `D` and block size `B`. -/
def cfgD (D B : Nat) : Cfg :=
  { D := D, B := B, f := ⟨[], [], []⟩, w := 0, n := 0, tries := 0, coreN := "", coreC := .block [] }

/-- The padded keys and the MAC's copy, for a hash function of output length
`D` and block size `B`. -/
structure HashT (D B : Nat) : Prop where
  ipad : TaintOk ((cfgD D B).padBlk ipad32)
  opad : TaintOk ((cfgD D B).padBlk opad32)
  copy : TaintOk (Cfg.copyN (D / 4) .r11 sTmp .r8 0)

theorem hashT : ∀ D B, (D, B) ∈ shapes → HashT D B := by
  intro D B h
  simp only [shapes, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    exact ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

/-- The blocks of `P`'s sizes. -/
theorem hT (P : RfcHash) : HashT P.H.D P.H.B := hashT _ _ P.hDB

/-- The blocks of the curve and the hash function's sizes. -/
theorem rT (P : RfcHash) : RfcT (cfgS P.R.E P.R.hHigh P.R.sh P.H.D P.H.B) := P.R.blkT _ _ P.hDB

/-! ## Blocks of any size -/

theorem scr_t (o : Nat) : TaintOk (scrAt .r0 o) :=
  taintOk_erase (is₀ := scrAt .r0 0) ⟨_, by taint_decide⟩ rfl

theorem tload_t₁₂ (j : Nat) : TaintOk (Cfg.tload .r12 j) :=
  taintOk_erase (is₀ := Cfg.tload .r12 0) ⟨_, by taint_decide⟩ rfl

theorem tload_t₇ (j : Nat) : TaintOk (Cfg.tload .r7 j) :=
  taintOk_erase (is₀ := Cfg.tload .r7 0) ⟨_, by taint_decide⟩ rfl

theorem updScr_t (o cnt a len : Nat) : TaintOk (Cfg.updArgs o cnt (scrAt .r1 a) len) :=
  taintOk_erase (is₀ := Cfg.updArgs 0 0 (scrAt .r1 0) 0) ⟨_, by taint_decide⟩ rfl

theorem updV_t (o cnt len : Nat) : TaintOk (Cfg.updArgs o cnt [.dp .add .r1 .r8 (.imm (BitVec.ofNat 32 fV))] len) :=
  taintOk_erase (is₀ := Cfg.updArgs 0 0 [.dp .add .r1 .r8 (.imm (BitVec.ofNat 32 fV))] 0) ⟨_, by taint_decide⟩ rfl

theorem finArgs_t (o cnt : Nat) : TaintOk (Cfg.finArgs o cnt) :=
  taintOk_erase (is₀ := Cfg.finArgs 0 0) ⟨_, by taint_decide⟩ rfl

/-! ## The indirect calls -/

/-- What an indirect call through `r` of the table's function `n` needs in
a run: `r` holds `n`'s address, which is the layout's, and of the functions
`ts` an indirect call reaches `n`'s `c`. -/
abbrev Reach (P : RfcHash) (r : Reg) (n : String) (c : Prog isa) (ts : List (String × Prog isa)) : Pred P :=
  fun L _ _ u => u.gpr r = L.fa n ∧ u.syms n = L.fa n ∧
    ts.find? (fun q => (u.syms q.1).setWidth 64 == (u.syms n).setWidth 64) = some (n, c)

/-- The indirect call reaches the same function in both runs. -/
theorem reach_icalls {r : Reg} {n : String} {c : Prog isa} {ts : List (String × Prog isa)} {Φ : Pred P}
    (hΦ : ∀ L g m₀ u, Φ L g m₀ u → Reach P r n c ts L g m₀ u) {Q : State → State → Prop}
    (h : RelCT isa (Two P Φ) (.call n c) Q) : RelCT isa (Two P Φ) (Code.icalls (.blx r) ts) Q := by
  cases ts with
  | nil => exact RelCT.of_false fun _ _ ⟨_, _, _, _, _, _, f₁, _⟩ => absurd (hΦ _ _ _ _ f₁).2.2 (by simp)
  | cons q ts =>
    refine RelCT.icalls_of_call h fun s₁ s₂ ⟨_, _, _, _, _, _, f₁, f₂⟩ => ?_
    have r₁ := hΦ _ _ _ _ f₁
    have r₂ := hΦ _ _ _ _ f₂
    have i₁ := icall_reach r₁.2.2 (r₁.1.trans r₁.2.1.symm)
    have i₂ := icall_reach r₂.2.2 (r₂.1.trans r₂.2.1.symm)
    rw [r₁.1] at i₁
    rw [r₂.1] at i₂
    exact ⟨_, i₁.1, i₂.1, i₁.2, i₂.2, rfl⟩

/-- The indirect call in a frame reaches the same function in both runs. -/
theorem reach_frame {r : Reg} {n : String} {c : Prog isa} {ts : List (String × Prog isa)} {Φ : Pred P}
    (hΦ : ∀ L g m₀ u, Φ L g m₀ u → Reach P r n c ts L g m₀ u) {rs : List Reg} {j : Instr}
    {Q : State → State → Prop} (h : RelCT isa (Two P Φ) (.frame (.push rs) (.call n c) j) Q) :
    RelCT isa (Two P Φ) (.frame (.push rs) (Code.icalls (.blx r) ts) j) Q := by
  cases ts with
  | nil => exact RelCT.of_false fun _ _ ⟨_, _, _, _, _, _, f₁, _⟩ => absurd (hΦ _ _ _ _ f₁).2.2 (by simp)
  | cons q ts =>
    refine RelCT.frame_icalls_of_call h fun s₁ s₂ ⟨_, _, _, _, c₁, c₂, f₁, f₂⟩ => ⟨?_, fun u₁ u₂ p₁ p₂ => ?_⟩
    · show VG.Arm.addrs (.push rs) s₁ = VG.Arm.addrs (.push rs) s₂
      simp only [VG.Arm.addrs, sp_two c₁ c₂]
    · obtain ⟨g₁, y₁⟩ := push_some p₁
      obtain ⟨g₂, y₂⟩ := push_some p₂
      have r₁ := hΦ _ _ _ _ f₁
      have r₂ := hΦ _ _ _ _ f₂
      have i₁ := icall_reach (s := u₁) (r := r) (by rw [y₁]; exact r₁.2.2) (by rw [g₁, y₁]; exact r₁.1.trans r₁.2.1.symm)
      have i₂ := icall_reach (s := u₂) (r := r) (by rw [y₂]; exact r₂.2.2) (by rw [g₂, y₂]; exact r₂.1.trans r₂.2.1.symm)
      rw [g₁, r₁.1] at i₁
      rw [g₂, r₂.1] at i₂
      exact ⟨_, i₁.1, i₂.1, i₁.2, i₂.2, rfl⟩

/-- The table's word `j`, which holds the address of `n`, into `r`. -/
theorem tload_reach {L : Lay P.I.hashLen} {g : Reg → BitVec 32} {m₀ : Mem} (hL : L.Ok) {t : State}
    (hc : Ctx L g m₀ t) {r : Reg} (hr : r ∉ ptrRegs) {j : Nat} (hj : 4 * j + 4 ≤ 20) {n : String} {c : Prog isa}
    {ts : List (String × Prog isa)} (hn : m₀.readW (State.addr (L.tab + BitVec.ofNat 32 (4 * j))) 32 = t.syms n)
    (hfa : t.syms n = L.fa n)
    (hf : ts.find? (fun q => (t.syms q.1).setWidth 64 == (t.syms n).setWidth 64) = some (n, c)) :
    WP isa (.block (Cfg.tload r j)) t fun u => Ctx L g m₀ u ∧ Reach P r n c ts L g m₀ u ∧
      ∀ q, q ≠ r → u.gpr q = t.gpr q :=
  WP.mono (tload_ok hL hc hr hj) fun _ ⟨c', _, hs, v, k⟩ =>
    ⟨c', ⟨by rw [v, hn, hfa], by rw [hs, hfa], by rw [hs]; exact hf⟩, k⟩

/-! ## The streaming calls -/

theorem scrNw (L : Lay P.I.hashLen) (hL : L.Ok) {o : Nat} (ho : o + 192 ≤ 384) :
    (L.scr + BitVec.ofNat 32 o).toNat + P.H.S ≤ 2 ^ 32 := by
  have := hL.nc; have := P.sizes
  rw [scr_toNat hL (by omega_arith)]; anums

theorem scrCov (L : Lay P.I.hashLen) (hL : L.Ok) {g : Reg → BitVec 32} {m₀ : Mem} {u : State} (hc : Ctx L g m₀ u)
    {o : Nat} (ho : o + 192 ≤ 384) : Covers [⟨State.addr (L.scr + BitVec.ofNat 32 o), P.H.S⟩] u.wr :=
  hc.coversW fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    have := P.sizes
    rw [scrA hL (by omega_arith)]; exact ⟨L.SCR, by simp, within_off _ (by anums)⟩

/-- `init`'s argument: the state at `scratch + o`. -/
abbrev IA (P : RfcHash) (o : Nat) : Pred P := fun L _ _ u => u.gpr .r0 = L.scr + BitVec.ofNat 32 o

/-- `init` of the state at `scratch + o`, through the table. -/
theorem initCall_piece {Φ : Pred P} {o : Nat} (ho : o + 192 ≤ 384) : Piece P Φ ((cfgOf P).initCall o) (Tt P) := by
  refine Piece.of ?_ fun L g m₀ t hL hk hc _ => WP.mono (initCall_ok hL hk.2.2.2 hc ho) fun _ h => ⟨h.1, trivial⟩
  unfold Cfg.initCall
  have s₁ : Piece P Φ (.block (scrAt .r0 o)) (IA P o) := Piece.blk (scr_t o) fun L g m₀ t hL hk hc _ =>
    WP.mono (scrAt_blk hc (d := .r0) (by decide) (o := o) (by omega_arith)) fun _ ⟨c, _, v, _⟩ => ⟨c, v⟩
  have s₂ : Piece P (IA P o) (.block (Cfg.tload .r12 0))
      (fun L g m₀ u => IA P o L g m₀ u ∧ Reach P .r12 P.H.initN P.H.initC P.f.init L g m₀ u) :=
    Piece.blk (tload_t₁₂ 0) fun L g m₀ t hL hk hc h0 => by
      have htm := hc.tabMem; have hok := hc.tabOk; have hfs := hc.fsy
      rw [hk.2.2.2.1] at htm hok hfs; rw [hk.2.2.2.2] at hok
      exact WP.mono (tload_reach hL hc (r := .r12) (by decide) (j := 0) (by decide) htm.1 (hfs _ (by simp)) hok.1)
        fun _ ⟨c, h, k⟩ => ⟨c, (k _ (by decide)).trans h0, h⟩
  refine s₁.ct.seq (s₂.ct.seq ?_)
  refine reach_icalls (fun _ _ _ _ h => h.2) ?_
  exact two_exists fun e => Proof.Pbkdf2.Stream.Arm.init_rel P.ok (st := e.1.scr + BitVec.ofNat 32 o)
    fun _ _ ⟨hL, _, _, c₁, c₂, a₁, a₂⟩ => ⟨a₁.1, a₂.1, scrNw e.1 hL ho, scrCov e.1 hL c₁ ho, scrCov e.1 hL c₂ ho⟩

/-- `update`'s arguments: the state at `scratch + o` holding `cnt` bytes,
the `len` bytes at `da`, and the working space. -/
abbrev UA (P : RfcHash) (o cnt : Nat) (da : Lay P.I.hashLen → BitVec 32) (len : Nat) : Pred P := fun L _ _ u =>
  u.gpr .r0 = L.scr + BitVec.ofNat 32 o ∧ u.gpr .r1 = da L ∧ u.gpr .r2 = BitVec.ofNat 32 cnt ∧ u.gpr .r3 = 0 ∧
    u.gpr .r7 = BitVec.ofNat 32 len ∧ u.gpr .r10 = L.scr + BitVec.ofNat 32 384

theorem ua_keep {o cnt : Nat} {da : Lay P.I.hashLen → BitVec 32} {len : Nat} {L : Lay P.I.hashLen}
    {g : Reg → BitVec 32} {m₀ : Mem} {t u : State} (h : UA P o cnt da len L g m₀ t)
    (k : ∀ q, q ≠ .r12 → u.gpr q = t.gpr q) : UA P o cnt da len L g m₀ u :=
  ⟨(k _ (by decide)).trans h.1, (k _ (by decide)).trans h.2.1, (k _ (by decide)).trans h.2.2.1,
    (k _ (by decide)).trans h.2.2.2.1, (k _ (by decide)).trans h.2.2.2.2.1, (k _ (by decide)).trans h.2.2.2.2.2⟩

/-- `update` of the state at `scratch + o`, holding `cnt` bytes, with `len`
bytes at `da`, through the table. -/
theorem updCall_piece {Φ : Pred P} {o cnt : Nat} (ho : o + 192 ≤ 384) {dataA : List Instr}
    {da : Lay P.I.hashLen → BitVec 32} {len : Nat} (hdA : ∀ (L : Lay P.I.hashLen) g m₀, DataA L g m₀ dataA (da L))
    (hd : ∀ L : Lay P.I.hashLen, L.Ok → UpdD P L o (da L) len) (ht : TaintOk (Cfg.updArgs o cnt dataA len))
    (hcnt : cnt < 2 ^ 16) (hlen : len < 2 ^ 16) :
    Piece P Φ ((cfgOf P).updCall o cnt dataA len) (Tt P) := by
  refine Piece.of ?_ fun L g m₀ t hL hk hc _ =>
    WP.mono (updCall_gen hL hk.2.2.2 hc ho (hdA L g m₀) (hd L hL) hcnt hlen) fun _ h => ⟨h.1, trivial⟩
  unfold Cfg.updCall
  have s₁ : Piece P Φ (.block (Cfg.updArgs o cnt dataA len)) (UA P o cnt da len) :=
    Piece.blk ht fun L g m₀ t _ _ hc _ => WP.mono (updArgs_ok hc (by omega_arith) (hdA L g m₀) hcnt hlen)
      fun _ ⟨c, _, h0, h1, h2, h3, h7, h10, _⟩ => ⟨c, h0, h1, h2, h3, h7, h10⟩
  have s₂ : Piece P (UA P o cnt da len) (.block (Cfg.tload .r12 1))
      (fun L g m₀ u => UA P o cnt da len L g m₀ u ∧ Reach P .r12 P.H.updN P.H.updC P.f.upd L g m₀ u) :=
    Piece.blk (tload_t₁₂ 1) fun L g m₀ t hL hk hc ha => by
      have htm := hc.tabMem; have hok := hc.tabOk; have hfs := hc.fsy
      rw [hk.2.2.2.1] at htm hok hfs; rw [hk.2.2.2.2] at hok
      exact WP.mono (tload_reach hL hc (r := .r12) (by decide) (j := 1) (by decide) htm.2.1 (hfs _ (by simp))
        hok.2.1) fun _ ⟨c, h, k⟩ => ⟨c, ua_keep ha k, h⟩
  refine s₁.ct.seq (s₂.ct.seq ?_)
  refine reach_frame (fun _ _ _ _ h => h.2) ?_
  exact two_exists fun e => Proof.Pbkdf2.Whole.Arm.upd_rel P.ok (sp := e.1.fp) (st := e.1.scr + BitVec.ofNat 32 o)
    (d := da e.1) (sc := e.1.scr + BitVec.ofNat 32 384) (len := len)
    fun _ _ ⟨hL, _, _, c₁, c₂, ⟨a₁, _⟩, ⟨a₂, _⟩⟩ =>
    ⟨updA hL c₁ ho (hd _ hL) hlen a₁.1 a₁.2.1 a₁.2.2.2.2.1 a₁.2.2.2.2.2,
      updA hL c₂ ho (hd _ hL) hlen a₂.1 a₂.2.1 a₂.2.2.2.2.1 a₂.2.2.2.2.2,
      by rw [count_of (by omega_arith) a₁.2.2.1 a₁.2.2.2.1, count_of (by omega_arith) a₂.2.2.1 a₂.2.2.2.1],
      c₁.sp, c₂.sp⟩

/-- `finalize`'s arguments: the state at `scratch + o` holding `cnt` bytes,
the output at `scratch + sTmp`, and the working space. -/
abbrev FA (P : RfcHash) (o cnt : Nat) : Pred P := fun L _ _ u =>
  u.gpr .r0 = L.scr + BitVec.ofNat 32 o ∧ u.gpr .r2 = BitVec.ofNat 32 cnt ∧ u.gpr .r3 = 0 ∧
    u.gpr .r1 = L.scr + BitVec.ofNat 32 1920 ∧ u.gpr .r12 = L.scr + BitVec.ofNat 32 384

/-- `finalize` of the state at `scratch + o`, holding `cnt` bytes, through the table. -/
theorem finCall_piece {Φ : Pred P} {o cnt : Nat} (ho : o + 192 ≤ 384) (hcnt : cnt < 2 ^ 16) :
    Piece P Φ ((cfgOf P).finCall o cnt) (Tt P) := by
  refine Piece.of ?_ fun L g m₀ t hL hk hc _ =>
    WP.mono (finCall_gen hL hk.2.2.2 hc ho hcnt) fun _ h => ⟨h.1, trivial⟩
  unfold Cfg.finCall
  have s₁ : Piece P Φ (.block (Cfg.finArgs o cnt)) (FA P o cnt) :=
    Piece.blk (finArgs_t o cnt) fun L g m₀ t _ _ hc _ => WP.mono (finArgs_ok hc (by omega_arith) hcnt)
      fun _ ⟨c, _, h0, h2, h3, h1, h12, _⟩ => ⟨c, h0, h2, h3, h1, h12⟩
  have s₂ : Piece P (FA P o cnt) (.block (Cfg.tload .r7 2))
      (fun L g m₀ u => FA P o cnt L g m₀ u ∧ Reach P .r7 P.H.finN P.H.finC P.f.fin L g m₀ u) :=
    Piece.blk (tload_t₇ 2) fun L g m₀ t hL hk hc ⟨h0, h2, h3, h1, h12⟩ => by
      have htm := hc.tabMem; have hok := hc.tabOk; have hfs := hc.fsy
      rw [hk.2.2.2.1] at htm hok hfs; rw [hk.2.2.2.2] at hok
      exact WP.mono (tload_reach hL hc (r := .r7) (by decide) (j := 2) (by decide) htm.2.2 (hfs _ (by simp))
        hok.2.2) fun _ ⟨c, h, k⟩ => ⟨c, ⟨(k _ (by decide)).trans h0, (k _ (by decide)).trans h2,
          (k _ (by decide)).trans h3, (k _ (by decide)).trans h1, (k _ (by decide)).trans h12⟩, h⟩
  refine s₁.ct.seq (s₂.ct.seq ?_)
  refine reach_frame (fun _ _ _ _ h => h.2) ?_
  exact two_exists fun e => Proof.Pbkdf2.Stream.Arm.fin_rel P.ok (sp := e.1.fp) (st := e.1.scr + BitVec.ofNat 32 o)
    (o := e.1.scr + BitVec.ofNat 32 1920) (sc := e.1.scr + BitVec.ofNat 32 384)
    fun _ _ ⟨hL, _, _, c₁, c₂, ⟨a₁, _⟩, ⟨a₂, _⟩⟩ =>
    ⟨finA hL c₁ ho a₁.1 a₁.2.2.2.1 a₁.2.2.2.2, finA hL c₂ ho a₂.1 a₂.2.2.2.1 a₂.2.2.2.2,
      by rw [count_of (by omega_arith) a₁.2.1 a₁.2.2.1, count_of (by omega_arith) a₂.2.1 a₂.2.2.1],
      c₁.sp, c₂.sp⟩

/-! ## HMAC -/

/-- `K₀ ⊕ c` at `scratch + sPad`. -/
theorem padBlk_piece {Φ : Pred P} {x : BitVec 32} {c : Byte}
    (hx : ((x >>> 16).setWidth 16 ++ ((x.setWidth 16).setWidth 32).extractLsb' 0 16 : BitVec 32) = c ++ c ++ c ++ c)
    (ht : TaintOk ((cfgOf P).padBlk x)) : Piece P Φ (.block ((cfgOf P).padBlk x)) (Tt P) :=
  Piece.blk ht fun _ _ _ _ hL _ hc _ => WP.mono (padBlk_ok (P := P) hL hc hx) fun _ h => ⟨h.1, trivial⟩

/-- `hinit`: each state set by `init` and updated with its padded key. -/
theorem hinit_piece {Φ : Pred P} : Piece P Φ (cfgOf P).hinit (Tt P) := by
  have hB : P.H.B < 2 ^ 16 := by have := P.sizes; anums
  unfold Cfg.hinit
  exact (initCall_piece (by decide)).seq ((initCall_piece (by decide)).seq
    ((padBlk_piece ipad32_eq (by exact (hT P).ipad)).seq
    ((updCall_piece (by decide) (fun _ _ _ => scrData (by decide)) (fun _ hL => padData hL (by decide))
      (updScr_t _ _ _ _) (by decide) hB).seq
    ((padBlk_piece opad32_eq (by exact (hT P).opad)).seq
    (updCall_piece (by decide) (fun _ _ _ => scrData (by decide)) (fun _ hL => padData hL (by decide))
      (updScr_t _ _ _ _) (by decide) hB)))))

/-- `hupd`: the inner state updated with the data. -/
theorem hupd_piece {Φ : Pred P} {dataA : List Instr} {da : Lay P.I.hashLen → BitVec 32} {len : Nat}
    (hdA : ∀ (L : Lay P.I.hashLen) g m₀, DataA L g m₀ dataA (da L)) (hd : ∀ L : Lay P.I.hashLen, L.Ok → DataOk L (da L) len)
    (ht : TaintOk (Cfg.updArgs sInner (cfgOf P).B dataA len)) (hlen : len ≤ 256) :
    Piece P Φ ((cfgOf P).hupd dataA len) (Tt P) := by
  have hB : P.H.B < 2 ^ 16 := by have := P.sizes; anums
  unfold Cfg.hupd
  exact updCall_piece (by decide) hdA (fun L hL => (hd L hL).upd hL) ht hB (by omega_arith)

/-- The temporary digest, as `update`'s data. -/
theorem tmpD {L : Lay P.I.hashLen} (hL : L.Ok) : UpdD P L 192 (L.scr + BitVec.ofNat 32 1920) P.H.D := by
  have := hL.nc; have := P.sizes
  have e1 : State.addr (L.scr + BitVec.ofNat 32 1920) = tmpA L := scrA hL (by decide)
  exact ⟨by rw [e1]; exact ⟨L.SCR, by simp, within_off _ (by anums)⟩,
    by rw [e1]; exact Offset.disjoint _ (by anums) (by anums) (by anums),
    by rw [e1]; exact Offset.disjoint _ (by anums) (by anums) (by anums),
    by rw [e1]; exact low_scr hL (by omega_arith) (by anums), by rw [scr_toNat hL (by decide)]; anums⟩

/-- The MAC's copy to the frame. -/
theorem hcopy_piece {Φ : Pred P} {dst : Nat} (hdst : dst + P.H.D ≤ 176) :
    Piece P Φ (.block (Cfg.copyN ((cfgOf P).D / 4) .r11 sTmp .r8 dst)) (Tt P) :=
  Piece.blk (taintOk_erase (by exact (hT P).copy) (copyN_erase _ _ _ _ _ _ _))
    fun _ _ _ _ hL _ hc _ => WP.mono (hcopy_ok (P := P) hL hc hdst) fun _ h => ⟨h.1, trivial⟩

/-- `hfin`: the MAC, for `len` bytes of data, to the frame at `dst`. -/
theorem hfin_piece {Φ : Pred P} {len dst : Nat} (hlen : len ≤ 256) (hdst : dst + P.H.D ≤ 176) :
    Piece P Φ ((cfgOf P).hfin len dst) (Tt P) := by
  have := P.sizes
  unfold Cfg.hfin
  exact (finCall_piece (by decide) (by show P.H.B + len < _; anums)).seq
    ((updCall_piece (by decide) (fun _ _ _ => scrData (by decide)) (fun _ hL => tmpD hL) (updScr_t _ _ _ _)
      (by show P.H.B < _; anums) (by show P.H.D < _; anums)).seq
    ((finCall_piece (by decide) (by show P.H.B + P.H.D < _; anums)).seq (hcopy_piece hdst)))

/-- `HMAC_K(data)`. -/
theorem hmac_piece {Φ : Pred P} {dataA : List Instr} {da : Lay P.I.hashLen → BitVec 32} {len dst : Nat}
    (hdA : ∀ (L : Lay P.I.hashLen) g m₀, DataA L g m₀ dataA (da L)) (hd : ∀ L : Lay P.I.hashLen, L.Ok → DataOk L (da L) len)
    (ht : TaintOk (Cfg.updArgs sInner (cfgOf P).B dataA len)) (hlen : len ≤ 256) (hdst : dst + P.H.D ≤ 176) :
    Piece P Φ ((cfgOf P).hmac dataA len dst) (Tt P) :=
  hinit_piece.seq ((hupd_piece hdA hd ht hlen).seq (hfin_piece hlen hdst))

/-- `V = HMAC_K(V)`. -/
theorem hmacV_piece {Φ : Pred P} : Piece P Φ (cfgOf P).hmacV (Tt P) := by
  have := P.sizes
  exact hmac_piece (da := fun L => L.fp + BitVec.ofNat 32 64) (fun _ _ _ => dataV) (fun _ _ => .inl ⟨64, rfl, by show 64 + P.H.D ≤ 176; anums⟩)
    (updV_t _ _ _) (by show P.H.D ≤ 256; anums) (by show 64 + P.H.D ≤ 176; anums)

/-- `K = HMAC_K(m)`, for the message of `len` bytes at `scratch + 2256`. -/
theorem hmacK_piece {Φ : Pred P} {len : Nat} (hlen : len ≤ 256) :
    Piece P Φ ((cfgOf P).hmac (scrAt .r1 sMsg) len fK) (Tt P) := by
  have := P.sizes
  exact hmac_piece (da := fun L => L.scr + BitVec.ofNat 32 2256) (fun _ _ _ => dataM)
    (fun _ _ => .inr ⟨2256, rfl, by omega_arith, by omega_arith⟩) (updScr_t _ _ _ _) hlen
    (by show 0 + P.H.D ≤ 176; anums)

/-! ## `K` and `V` from a message -/

/-- The message `V ‖ b (‖ d ‖ h)` at `scratch + sMsg`. -/
theorem msg_piece {Φ : Pred P} {b : Nat} (hb : b < 2) {full : Bool} {ho : Nat} (hho : full = true → ho = P.hB - 24)
    (ht : TaintOk (Cfg.msg P.Q P.H.D b full ho)) :
    Piece P Φ (.block (Cfg.msg P.Q P.H.D b full ho)) (Tt P) :=
  Piece.blk ht fun _ _ _ _ hL hk hc _ => by
    have := P.sizes; have := P.wsizes
    exact WP.mono (msg_ok hL hc hb full ho (D := P.H.D) (Q := P.Q) (by anums) (by anums) (by anums) (by anums)
      (by rw [hk.1]) (fun hf => by
        have := hB_fit P; have := hB_ge P
        rw [hho hf, hk.e_eq]; omega_arith)) fun _ h => ⟨h.1, trivial⟩

/-- `K = HMAC_K(V ‖ b ‖ d ‖ h)`, then `V = HMAC_K(V)`. -/
theorem rekeyFull_piece {Φ : Pred P} {b : Nat} (hb : b < 2) : Piece P Φ ((cfgOf P).rekeyFull b) (Tt P) := by
  have := P.sizes; have := P.wsizes
  unfold Cfg.rekeyFull
  obtain rfl | rfl : b = 0 ∨ b = 1 := by omega_arith
  · exact (msg_piece hb (fun _ => fHo_eq P) (by exact (rT P).msgF)).seq
      ((hmacK_piece (by show P.H.D + 2 * P.Q + 1 ≤ 256; anums)).seq hmacV_piece)
  · exact (msg_piece hb (fun _ => fHo_eq P) (by exact (rT P).msgF₁)).seq
      ((hmacK_piece (by show P.H.D + 2 * P.Q + 1 ≤ 256; anums)).seq hmacV_piece)

/-- `K = HMAC_K(V ‖ 0x00)`, then `V = HMAC_K(V)`. -/
theorem rekey_piece {Φ : Pred P} : Piece P Φ (cfgOf P).rekey (Tt P) := by
  have := P.sizes
  unfold Cfg.rekey
  exact (msg_piece (b := 0) (by decide) (fun h => absurd h (by decide)) (by exact (rT P).msgN)).seq
    ((hmacK_piece (by show P.H.D + 1 ≤ 256; anums)).seq hmacV_piece)

/-! ## The candidate -/

/-- `V`'s `D` bytes to `T + k D`. -/
theorem keepV_piece {Φ : Pred P} (hw : P.wide = true) {k : Nat} (hkb : k * P.H.D + P.H.D ≤ 128) :
    Piece P Φ (.block ((cfgOf P).keepV k)) (Tt P) :=
  Piece.blk (taintOk_erase (by exact (rT P).keepV) (copyN_erase _ _ _ _ _ _ _))
    fun L _ _ _ hL hk hc _ => by
      have he := e68 hk.e_eq hw
      have := P.sizes
      have := L.sp.isLt
      have nB := hL.nB
      have hfp0 : L.fp.toNat + 64 + 4 * (P.H.D / 4) ≤ 2 ^ 32 := by
        have h0 := fp_toNat hL (o := 0) (by omega_arith)
        rw [BitVec.add_zero] at h0
        omega_arith
      exact WP.mono (copyF_ok hL hc (src := .r8) (S := L.fp) hc.r8 (by decide) (so := 64) (d := 360 + k * P.H.D)
        (K := P.H.D / 4) (by omega_arith) (by omega_arith) (by omega_arith) hfp0
        (fun j hj => by rw [fpd hL]; exact hc.inFr (by omega_arith) (by omega_arith))
        (by rw [fpd hL]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)))
        fun _ h => ⟨h.1, trivial⟩

/-- The first `k` `V`s of the candidate. -/
theorem candW_piece {Φ : Pred P} (hw : P.wide = true) : ∀ k, k * P.H.D ≤ 128 →
    Piece P Φ ((cfgOf P).candW k) (Tt P)
  | 0, _ => by
    rw [Cfg.candW]
    exact Piece.blk ⟨_, by taint_decide⟩ fun _ _ _ t _ _ hc _ => WP.block_nil ⟨hc, trivial⟩
  | k + 1, hk => by
    have hk' : k * P.H.D + P.H.D ≤ 128 := by rw [Nat.succ_mul] at hk; exact hk
    rw [Cfg.candW]
    exact (candW_piece hw k (by omega_arith)).seq (hmacV_piece.seq (keepV_piece hw hk'))

/-- If `sh ≠ 0`: `T`'s first `Q` bytes shifted right by `sh` bits. -/
theorem candTop_piece {Φ : Pred P} (hw : P.wide = true) : Piece P Φ (.block (cfgOf P).candTop) (Tt P) := by
  by_cases hsh : P.R.sh = 0
  · have e : (cfgOf P).candTop = [] := by
      simp only [Cfg.candTop, show (cfgOf P).sh = 0 from hsh, ↓reduceIte]
    rw [e]
    exact Piece.blk ⟨_, by taint_decide⟩ fun _ _ _ t _ _ hc _ => WP.block_nil ⟨hc, trivial⟩
  · exact Piece.blk (by exact (rT P).candTop) fun _ _ _ _ hL hk hc _ =>
      WP.mono (candTop_ok hL hk.e_eq hw hsh hc) fun _ h => ⟨h.1, trivial⟩

/-- The candidate: its calls and blocks leak the same in both runs. -/
theorem cand_piece {Φ : Pred P} : Piece P Φ (cfgOf P).cand (Tt P) := by
  cases hw : P.wide
  · simp only [Cfg.cand, cfgOf_wide, hw, Bool.false_eq_true, ↓reduceIte]
    exact hmacV_piece
  · simp only [Cfg.cand, cfgOf_wide, hw, ↓reduceIte]
    exact (candW_piece hw _ (m_facts P hw).2).seq (candTop_piece hw)

/-! ## One candidate -/

/-- `core`, in its frame, with arguments that agree. -/
theorem core_ct {i : Nat} :
    RelCT isa (Two P fun L _ m₀ u => P₁ P L m₀ i u ∧ CoreRegs L P.R.sh u)
      (.frame (.push [.r12, .lr]) (.call (cfgOf P).coreN (cfgOf P).coreC) (.pop .r12 8)) fun _ _ => True :=
  two_exists fun e => frame2_rel rfl P.R.coreX P.R.coreCT (coreRd P e.1) (coreWr P e.1)
    fun s₁ s₂ ⟨hL, hk, _, c₁, c₂, ⟨_, a₁⟩, ⟨_, a₂⟩⟩ => by
      have h₁ := c₁.sp24 hL
      have h₂ := c₂.sp24 hL
      refine ⟨sp_two c₁ c₂, core_pre hL hk c₁ a₁, core_pre hL hk c₂ a₂, ?_,
        core_cov hL hk c₁, core_covW hk.1 c₁, core_cov hL hk c₂, core_covW hk.1 c₂⟩
      simp only [coreK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
        Pbkdf2.Stream.Arm.ce0, Pbkdf2.Stream.Arm.ce1, Pbkdf2.Stream.Arm.ce2, Pbkdf2.Stream.Arm.ce3, pushed_gpr,
        pushed_sp, a₁.r0, a₁.r1, a₁.r2, a₁.r3, a₂.r0, a₂.r1, a₂.r2, a₂.r3,
        Proof.Pbkdf2.Whole.Arm.p2_arg0 (s := s₁) (by omega_arith), Proof.Pbkdf2.Whole.Arm.p2_arg0 (s := s₂) (by omega_arith),
        a₁.r12, a₂.r12, sp_two c₁ c₂, true_and]
      intro c hc
      have hmem : c ∈ e.1.cs := hk.2.1.2.2 ▸ hc
      rw [core_syms c₁ hmem, core_syms c₂ hmem]

/-- Whether to go on agrees: in both runs, iff the candidate is before the one it stops at. -/
theorem dec_two {L : Lay P.I.hashLen} {m₁ m₂ : Mem} {i : Nat} (hx : exitAt P L m₁ = exitAt P L m₂) {u₁ u₂ : State}
    (h₁ : Mid P L m₁ i u₁) (h₂ : Mid P L m₂ i u₂) : isa.eval .ne u₁ = isa.eval .ne u₂ := by
  rw [h₁.dec, h₂.dec]
  refine congrArg some (decide_eq_decide.mpr ?_)
  rw [go_iff h₁.lt h₁.fails, go_iff h₂.lt h₂.fails, hx]

/-- What one candidate leaves: the end, or the next candidate. -/
def After (P : RfcHash) (i : Nat) (L : Lay P.I.hashLen) (_ : Reg → BitVec 32) (m₀ : Mem) (t : State) : Prop :=
  (isa.eval .ne t = some false ∧ Exit P L m₀ i t) ∨ (isa.eval .ne t = some true ∧ LoopInv P L m₀ (i + 1) t)

theorem goOn_blk : TaintOk Cfg.goOn := ⟨_, by taint_decide⟩
theorem again_blk : TaintOk Cfg.again := ⟨_, by taint_decide⟩
theorem stop_blk : TaintOk Cfg.stop := ⟨_, by taint_decide⟩

theorem tryOne_trace {i : Nat} :
    RelCT isa (Two P fun L _ m₀ t => LoopInv P L m₀ i t) (cfgOf P).tryOne fun _ _ => True := by
  refine (two_wp (Ψ := fun L _ m₀ u => P₁ P L m₀ i u) (cand_piece.rel (Φ := Tt P) fun _ _ _ _ _ => trivial)
    fun _ _ _ _ hL hk hc hi => try₁_ok hL hk hc hi).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ u => P₁ P L m₀ i u ∧ CoreRegs L P.R.sh u) (two_blk (by exact (rT P).coreArgs))
    fun _ _ _ _ hL hk hc hi => try₂_ok hL hk hc hi).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ u => P₃ P L m₀ i u) core_ct fun _ _ _ _ hL hk hc hi =>
    try₃_ok hL hk hc hi.1 hi.2).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ u => Mid P L m₀ i u) (two_blk goOn_blk)
    fun _ _ _ _ _ _ hc hi => try₄_ok hc hi).seq ?_
  refine VG.RelCT.ite (fun _ _ ⟨_, _, _, hx, _, _, f₁, f₂⟩ => dec_two hx f₁ f₂) ?_ ?_
  · exact (rekey_piece.ct.seq (two_blk again_blk)).mono (fun _ _ h => Two.mono (fun _ _ _ _ _ => trivial) h.1)
      fun _ _ h => h
  · exact (two_blk stop_blk).mono (fun _ _ h => h.1) fun _ _ h => h

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
    have hgo : sigI P e.1 m' i = none ∧ i + 1 < P.I.tries := ⟨hI.fails i (by omega_arith), hI.lt⟩
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
  ⟨by omega_arith, by omega_arith⟩

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

theorem initCnt_blk₀ : TaintOk [.movw .r9 (BitVec.ofNat 16 8)] := ⟨_, by taint_decide⟩

/-- The count's initial `movw`, for any count: the analysis does not read its
immediate (`Taint.check_eraseOff`), so it is that of one count's. -/
theorem initCnt_blk (c : Cfg) : TaintOk c.initCnt := taintOk_erase initCnt_blk₀ rfl

theorem wipe_blk (wide hHigh : Bool) : TaintOk (Cfg.wipe wide hHigh) := by
  cases wide <;> cases hHigh
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩

/-- The body after the prologue, `h`, `V` and `K`. -/
theorem rest_ct :
    RelCT isa (Two P fun L _ m₀ t => QB P L m₀ t) (.seq ((cfgOf P).rekeyFull 0) (.seq ((cfgOf P).rekeyFull 1)
      (.seq (.block (cfgOf P).initCnt) (.seq (.loop (cfgOf P).tryOne .ne)
        (.block (Cfg.wipe (cfgOf P).wide (cfgOf P).hHigh))))))
      fun _ _ => True := by
  refine (two_wp (Ψ := fun L _ m₀ t => QC P L m₀ t) ((rekeyFull_piece (by decide)).rel (Φ := Tt P)
    fun _ _ _ _ _ => trivial) fun _ _ _ _ hL hk hc h => stageC_ok (P := P) hL hk hc h).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ t => QD P L m₀ t) ((rekeyFull_piece (by decide)).rel (Φ := Tt P)
    fun _ _ _ _ _ => trivial) fun _ _ _ _ hL hk hc h => stageD_ok (P := P) hL hk hc h).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ t => LoopInv P L m₀ 0 t) (two_blk (initCnt_blk _))
    fun _ _ _ _ _ _ hc h => stageE_ok (P := P) hc h).seq ?_
  exact loop_ct.seq (two_blk (wipe_blk _ _))

/-- Unless the hash is shorter, `bits2octets` is the curve's. -/
theorem reduce_eq (hw : P.wide = false) : (cfgOf P).reduce = (cfgC P.R.E P.R.hHigh).reduce := by
  have h₁ : (cfgC P.R.E P.R.hHigh).wide = false := by
    show decide (64 < P.R.E.C.len) = false
    have := (P.sizesA hw)
    simp only [decide_eq_false_iff_not]; simp only [RfcHash.Q, RfcHash.k] at this; omega_arith
  have h₂ : (cfgOf P).fHo = (cfgC P.R.E P.R.hHigh).fHo := by
    simp only [Cfg.fHo, cfgOf_wide, hw, h₁]; rfl
  have h₃ : (cfgOf P).selWord = (cfgC P.R.E P.R.hHigh).selWord := funext fun j => by
    simp only [Cfg.selWord, h₂]; rfl
  have h₄ : (cfgOf P).subWord = (cfgC P.R.E P.R.hHigh).subWord := funext fun j => by
    simp only [Cfg.subWord, h₂]; rfl
  simp only [Cfg.reduce, h₃, h₄]
  rfl

theorem prep_ct : RelCT isa (Two P fun _ _ _ _ => True) (.block ((cfgOf P).prep ++ Cfg.initKV)) fun _ _ => True := by
  cases hw : P.wide
  · have e : (cfgOf P).prep = (cfgC P.R.E P.R.hHigh).reduce := by
      simp only [Cfg.prep, cfgOf_wide, hw, Bool.false_eq_true, ↓reduceIte, reduce_eq hw]
    rw [e]; exact two_blk (P.R.reduceT (P.curveA hw))
  · exact two_blk (by exact (rT P).prepW hw)

/-- `h`, `V` and `K`, after the prologue. -/
theorem stageB_ct :
    RelCT isa (Two P fun _ _ _ _ => True) (.block ((cfgOf P).prep ++ Cfg.initKV))
      (Two P fun L _ m₀ t => QB P L m₀ t) :=
  two_wp prep_ct fun _ _ _ _ hL hk hc _ => stageB_ok (P := P) hL hk hc

/-! ## The prologue -/

/-- Two runs from states that satisfy the precondition and agree on public
data, after the frame's allocation. -/
def Entered (P : RfcHash) (ns : List String) (a b : State) : Prop :=
  ∃ s₁ s₂, ((rfcP P ns).pre s₁ ∧ (rfcP P ns).pre s₂ ∧ (rfcP P ns).pub s₁ s₂) ∧
    a = allocated (cfgOf P).fb s₁ ∧ b = allocated (cfgOf P).fb s₂

/-- After `sp`'s copy: the saves, the table and `scratch` read through `r12`. -/
theorem prologue_tail₀ : ∃ hc, (VG.Taint.check taint (τr [.r0, .r1, .r2, .r12])
    (.block (Impl.Ecdsa.Rfc6979.Arm.saved.map (fun p => Instr.str p.1 .r12 p.2) ++
      ([.ldr .r4 .r12 0, .str .r0 .r12 fOut, .mov .r5 (.reg .r1), .mov .r6 (.reg .r2),
        .ldr .r11 .r12 0, .mov .r8 (.reg .r12)] : List Instr)))
    hc).isSome = true := ⟨_, by taint_decide⟩

theorem prologue_tail (c : Cfg) : ∃ hc, (VG.Taint.check taint (τr [.r0, .r1, .r2, .r12])
    (.block (Impl.Ecdsa.Rfc6979.Arm.saved.map (fun p => Instr.str p.1 .r12 p.2) ++
      ([.ldr .r4 .r12 (c.fb + 4), .str .r0 .r12 fOut, .mov .r5 (.reg .r1), .mov .r6 (.reg .r2),
        .ldr .r11 .r12 c.fb, .mov .r8 (.reg .r12)] : List Instr)))
    hc).isSome = true := taint_erase prologue_tail₀ rfl

/-- The prologue reads `sp`, which agrees, and then addresses the frame through `r12`. -/
theorem start_blk {ns : List String} : RelCT isa (Entered P ns) (.block (cfgOf P).prologue) fun _ _ => True := by
  rw [Cfg.prologue, List.cons_append]
  refine block_cons_ct (R := fun a b => ∀ r ∈ [Reg.r0, .r1, .r2, .r12], a.gpr r = b.gpr r)
    (fun a b a' b' ⟨s₁, s₂, ⟨_, _, hsp, h0, h1, h2, _⟩, ea, eb⟩ ha hb => ?_) ?_
  · subst ea eb
    simp only [reduceExec, show (0 : Nat) < 256 by decide, ↓reduceIte, Option.some.injEq] at ha hb
    subst ha hb
    refine ⟨rfl, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      simp only [State.setReg, reduceCtorEq, ↓reduceIte, allocated, h0, h1, h2, hsp]
  · let ⟨_, h⟩ := prologue_tail (cfgOf P)
    exact VG.RelCT.taint (A := taint) _ (fun _ _ h => agree_regs h) h

/-- After the prologue, the runs are related by `Two`, with the layout of the
arguments, which agree, and the same number of candidates. -/
theorem start_ct {ns : List String} (hns : ∀ n ∈ [P.H.initN, P.H.updN, P.H.finN], n ∈ ns) :
    RelCT isa (Entered P ns) (.block (cfgOf P).prologue) (Two P fun _ _ _ _ => True) := by
  intro a b t₁ t₂ a' b' hp e₁ e₂
  obtain ⟨ht, -⟩ := start_blk _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨s₁, s₂, ⟨p₁, p₂, hsp, h0, h1, h2, ha0, ha1, hres, hsy, hns'⟩, rfl, rfl⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := entry_ok (P := P) p₁
  obtain ⟨_, u₂, x₂, y₂⟩ := entry_ok (P := P) p₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  have eqSy : (fun n => if n ∈ P.R.coreConsts.map Prod.fst then s₂.syms n else 0) =
      (fun n => if n ∈ P.R.coreConsts.map Prod.fst then s₁.syms n else 0) := by
    funext n
    by_cases hn : n ∈ P.R.coreConsts.map Prod.fst
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
      simp only [hn, ↓reduceIte]
      exact (hsy c hc).symm
    · simp only [hn, ↓reduceIte]
  have eqFa : (fun n => if n ∈ [P.H.initN, P.H.updN, P.H.finN] then s₂.syms n else 0) =
      (fun n => if n ∈ [P.H.initN, P.H.updN, P.H.finN] then s₁.syms n else 0) := by
    funext n
    by_cases hn : n ∈ [P.H.initN, P.H.updN, P.H.finN]
    · simp only [hn, ↓reduceIte]
      exact (hns' n (hns n hn)).symm
    · simp only [hn, ↓reduceIte]
  have hl : layP P s₂ = layP P s₁ := by
    simp only [layP, lay, hsp, h0, h1, h2, ha0, ha1, eqSy, eqFa]
  have hr : (result P.I s₁.mem (State.addr (layP P s₁).d) (State.addr (layP P s₁).dg)).2 =
      (result P.I s₂.mem (State.addr (layP P s₁).d) (State.addr (layP P s₁).dg)).2 := by
    show (result P.I s₁.mem (State.addr (s₁.gpr .r1)) (State.addr (s₁.gpr .r2))).2 =
      (result P.I s₂.mem (State.addr (s₁.gpr .r1)) (State.addr (s₁.gpr .r2))).2
    rw [hres, h1, h2]
  rw [hl] at y₂
  exact ⟨ht, ⟨layP P s₁, s₁.gpr, s₂.gpr, s₁.mem, s₂.mem⟩, lay_ok p₁, coreOk_lay P s₁,
    congrArg (fun x => if x = 0 then P.I.tries - 1 else x - 1) hr, y₁, y₂, trivial, trivial⟩

/-- Runs whose public data agree (with the addresses of the hash function's
functions among `ns`) have the same layout, and stop at the same candidate. -/
theorem sign_ct {ns : List String} (hns : ∀ n ∈ [P.H.initN, P.H.updN, P.H.finN], n ∈ ns) :
    ConstantTime isa (rfcP P ns).pre (rfcP P ns).pub (cfgOf P).sign := by
  refine VG.RelCT.constantTime (Q := fun _ _ => True) (alloc_ct (R := fun _ _ => True) ?_)
  rw [Cfg.body, List.append_assoc]
  refine (RelCT.block_append ((start_ct hns).seq stageB_ct)).seq rest_ct |>.mono
    (fun _ _ ⟨s₁, s₂, h, ea, eb⟩ => ⟨s₁, s₂, h, ea, eb⟩) fun _ _ h => h

end VG.Proof.Ecdsa.Rfc6979.Arm

module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Correct
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.ICall
import VerifiedGarbage.Proof.Framework.Arm.TaintErase
import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Framework.Arm.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Blocks
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Prep
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Regs
import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Calls
import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Upd
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Correct
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.ICall
meta import VerifiedGarbage.Proof.Framework.Arm.TaintErase
meta import VerifiedGarbage.Proof.Framework.Arm.Syms
meta import VerifiedGarbage.Proof.Framework.Arm.Reduce
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Blocks
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Prep
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Regs
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Calls
meta import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Upd

/-!
# Deterministic ECDSA on 32-bit ARM: constant time, up to the number of candidates

As on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/CT.lean`): two runs whose public
data agree have the same layout, and stop at the same candidate (`exitAt`,
from the contract's leakage: the number of candidates RFC 6979 tries).
Between the prologue and the frame's release they are related by `Two`:
both satisfy `Ctx` with that layout (and `Φ`, what the next piece needs).
The blocks address only the frame and the buffers, from the registers that
hold the pointers, which agree (the taint analysis, of the blocks whose
contents depend on the curve: `RfcT`, each curve's `RfcCurve.blk`), or, for
the byte loops, from registers both runs set alike (`T`'s length, `D`); an
indirect call reaches, through the table, whose address `r6` holds, the
same function in both runs (`tcall_ct`), each of which is constant time with
arguments that agree (`hi_rel`, `upd_rel`, `hf_rel`, `frame2_rel`); and the
loop's branch agrees, since in both runs it goes on after candidate `i` iff
`i` is before the candidate it stops at (`go_iff`). The prologue's first
instruction reads `sp`, which agrees (`start_blk`), and the frame's
allocation and release access no memory (`alloc_ct`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Impl.AesGcm.Arm (copyLoop)
open VG.Impl.Pbkdf2.Stream.Arm (scrAt)
open VG.Proof.X25519.Arm (op2_reg op2_imm dpVal)
open VG.Proof.Ecdsa.Rfc6979 (kvAtB candAtB stepB)
open VG.Proof.Pbkdf2.Whole.Arm (hi_rel hf_rel frame2_rel)
open VG.Proof.HmacTable.Arm (TabOK TabMem tA)

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

/-! ## How many candidates -/

theorem ite_le_of_not {c : Prop} [Decidable c] {a b i : Nat} (hc : ¬c) (hb : b ≤ i) :
    (if c then a else b) ≤ i := by
  simp only [hc, ite_false]; exact hb

/-- The candidate the loop stops at, from the number RFC 6979 tries. -/
def exitAt (P : RfcHash) (L : Lay P.I.hashLen) (m₀ : Mem) : Nat :=
  if (result P.I m₀ (State.addr L.d) (State.addr L.dg)).2 = 0 then P.I.tries - 1
  else (result P.I m₀ (State.addr L.d) (State.addr L.dg)).2 - 1

/-- The loop goes on after candidate `i` iff it stops at a later one. -/
theorem go_iff {P : RfcHash} {L : Lay P.I.hashLen} {m₀ : Mem} {i : Nat} (hi : i < P.I.tries)
    (hf : ∀ j < i, sigI P L m₀ j = none) :
    (sigI P L m₀ i = none ∧ i + 1 < P.I.tries) ↔ i < exitAt P L m₀ := by
  unfold exitAt
  rw [result_unfold]
  by_cases hv : 1 ≤ xOf P L m₀ ∧ xOf P L m₀ < P.R.E.C.n
  · simp only [hv, and_self, ite_true]
    rw [Proof.Ecdsa.Rfc6979.searchB_shift (blocks_eq P) i P.I.tries (by omega_arith) hf,
      show P.I.tries - i = (P.I.tries - 1 - i) + 1 by omega_arith]
    cases hs : sigI P L m₀ i with
    | some rs =>
      rw [Proof.Ecdsa.Rfc6979.searchB_ok (blocks_eq P) hs]
      simp
    | none =>
      rw [Proof.Ecdsa.Rfc6979.searchB_fail (blocks_eq P) hs]
      by_cases h7 : i + 1 < P.I.tries
      · have := Proof.Ecdsa.Rfc6979.searchB_pos (C := P.R.E.C) (H := P.ok.hH.SH.H) (hlen := P.F.H.D)
          (d := xOf P L m₀) (e := eOf P L m₀) (n := P.I.tries - 2 - i)
          (K := (stepB P.ok.hH.SH.H P.nV (kvI P L m₀ i).1 (kvI P L m₀ i).2).1)
          (V := (stepB P.ok.hH.SH.H P.nV (kvI P L m₀ i).1 (kvI P L m₀ i).2).2) (blocks_eq P)
        rw [show P.I.tries - 1 - i = P.I.tries - 2 - i + 1 by omega_arith]
        simp only [true_and, h7]
        simp only [kvI] at this
        rw [true_iff]
        split <;> omega
      · rw [show P.I.tries - 1 - i = 0 by omega_arith]
        simp only [Spec.Ecdsa.Rfc6979.search, h7, and_false, false_iff, Nat.not_lt]
        exact ite_le_of_not (by omega_arith) (by omega_arith)
  · simp only [hv, ite_false, ite_true]
    have hs : sigI P L m₀ i = none := by
      simp only [sigI, Spec.Ecdsa.signWith]
      split
      · rename_i h; exact absurd ⟨h.1, h.2.1⟩ hv
      · rfl
    simp only [hs, true_and]
    omega_arith

/-! ## Two runs -/

/-- What each of two runs has, between the prologue and the frame's release. -/
abbrev Env (P : RfcHash) := Lay P.I.hashLen × (Reg → BitVec 32) × (Reg → BitVec 32) × Mem × Mem

/-- What the proof needs of each run at a point of the code. -/
abbrev Pred (P : RfcHash) := Lay P.I.hashLen → (Reg → BitVec 32) → Mem → State → Prop

/-- Nothing. -/
abbrev Tt (P : RfcHash) : Pred P := fun _ _ _ _ => True

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

/-- Code whose addresses depend only on the registers `rs`, which agree. -/
theorem two_tr {c : Prog isa} {Φ : Pred P} (rs : List Reg)
    (hrs : ∀ (L : Lay P.I.hashLen) g₁ g₂ m₁ m₂ (t₁ t₂ : State), Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ →
      Φ L g₁ m₁ t₁ → Φ L g₂ m₂ t₂ → ∀ r ∈ rs, t₁.gpr r = t₂.gpr r)
    (h : ∃ hc, (VG.Taint.check taint (τr rs) c hc).isSome = true) : RelCT isa (Two P Φ) c fun _ _ => True :=
  let ⟨_, h⟩ := h
  VG.RelCT.taint (A := taint) (τr rs)
    (fun _ _ ⟨_, _, _, _, c₁, c₂, f₁, f₂⟩ => agree_regs (hrs _ _ _ _ _ _ _ c₁ c₂ f₁ f₂)) h

/-- The blocks of the curve. -/
theorem rT (P : RfcHash) : RfcT (cfgC P.R.E P.R.big P.R.sh) := P.R.blk

/-! ## The indirect calls -/

/-- What an indirect call of `n` needs of the table in each run: its word
`j` (on entry) is `n`'s address, which is the layout's, and of `ts` an
indirect call reaches `n`'s `c`. -/
def TabFn (P : RfcHash) (j : Nat) (n : String) (c : Prog isa) (ts : List (String × Prog isa)) : Prop :=
  ∀ (L : Lay P.I.hashLen) g m₀ (t : State), L.Ok → CoreOk P L → Ctx L g m₀ t →
    m₀.readW (tA L.tab (4 * j)) 32 = t.syms n ∧
      ts.find? (fun q => (t.syms q.1).setWidth 64 == (t.syms n).setWidth 64) = some (n, c) ∧ t.syms n = L.fa n

theorem tfn_init : TabFn P 0 P.F.hiN P.F.hiC P.f.init := fun L _ _ _ _ hk hc => by
  have hok := hc.tabOk; have htm := hc.tabMem; have hf := hc.fsy
  rw [hk.2.2.1.1, hk.2.2.1.2] at hok; rw [hk.2.2.1.1] at htm hf
  exact ⟨htm.1, hok.i, hf _ (by simp)⟩

theorem tfn_upd : TabFn P 1 P.F.H.updN P.F.H.updC P.f.upd := fun L _ _ _ _ hk hc => by
  have hok := hc.tabOk; have htm := hc.tabMem; have hf := hc.fsy
  rw [hk.2.2.1.1, hk.2.2.1.2] at hok; rw [hk.2.2.1.1] at htm hf
  exact ⟨htm.2.1, hok.u, hf _ (by simp)⟩

theorem tfn_fin : TabFn P 2 P.F.hfN P.F.hfC P.f.fin := fun L _ _ _ _ hk hc => by
  have hok := hc.tabOk; have htm := hc.tabMem; have hf := hc.fsy
  rw [hk.2.2.1.1, hk.2.2.1.2] at hok; rw [hk.2.2.1.1] at htm hf
  exact ⟨htm.2.2, hok.f, hf _ (by simp)⟩

/-- What only `lr` changing keeps. -/
def LR (Φ : Pred P) : Prop :=
  ∀ L g m₀ (t u : State), Φ L g m₀ t → (∀ r, r ≠ .lr → u.gpr r = t.gpr r) → Φ L g m₀ u

theorem tload_taint (j : Nat) (hj : j < 3) : TaintOk [.ldr .lr .r6 (4 * j)] := by
  obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩

/-- The indirect call of the table's function `j`: in both runs of the same
function, `n`'s (the table's word `j` holds the layout's address of `n`). -/
theorem tcall_ct {Φ : Pred P} {j : Nat} (hj : j < 3) {n : String} {c : Prog isa}
    {ts : List (String × Prog isa)} {rs : List Reg} {r : Reg} {k : Nat} (hn : TabFn P j n c ts) (hΦ : LR Φ)
    (hcall : RelCT isa (Two P Φ) (.frame (.push rs) (.call n c) (.pop r k)) fun _ _ => True) :
    RelCT isa (Two P Φ) (Cfg.tcall j ts rs r k) fun _ _ => True := by
  unfold Cfg.tcall
  refine (two_wp (Ψ := fun L g m₀ u => Φ L g m₀ u ∧ u.gpr .lr = L.fa n ∧ u.syms n = L.fa n ∧
      ts.find? (fun q => (u.syms q.1).setWidth 64 == (u.syms n).setWidth 64) = some (n, c))
    (two_blk (tload_taint j hj)) fun L g m₀ t hL hk hc hφ => ?_).seq ?_
  · obtain ⟨hw, hf, hfa⟩ := hn L g m₀ t hL hk hc
    exact WP.mono_syms (Q := fun u' => Ctx L g m₀ u' ∧ u'.gpr .lr = m₀.readW (tA L.tab (4 * j)) 32 ∧
        ∀ q, q ≠ .lr → u'.gpr q = t.gpr q)
      (tabLd_ok hL hc (d := .lr) (by decide) (o := 4 * j) (by omega) fun u' c' _ v' k' =>
        WP.block_nil ⟨c', v', k'⟩) fun u' ⟨c', v', k'⟩ sy =>
      ⟨c', hΦ _ _ _ _ _ hφ k', by rw [v', hw, hfa], by rw [sy, hfa], by rw [sy]; exact hf⟩
  · cases ts with
    | nil => exact RelCT.of_false fun _ _ ⟨_, _, _, _, _, _, f₁, _⟩ => by simp at f₁
    | cons q ts =>
      refine RelCT.frame_icalls_of_call (hcall.mono (fun _ _ => Two.mono fun _ _ _ _ h => h.1) fun _ _ h => h)
        fun s₁ s₂ ⟨e, _, _, _, c₁, c₂, f₁, f₂⟩ => ⟨?_, fun u₁ u₂ hp₁ hp₂ => ?_⟩
      · show addrs (.push rs) s₁ = addrs (.push rs) s₂
        simp only [addrs, sp_two c₁ c₂]
      · obtain ⟨g₁, y₁⟩ := push_some_gpr hp₁
        obtain ⟨g₂, y₂⟩ := push_some_gpr hp₂
        refine ⟨(e.1.fa n).setWidth 64, by show some ((u₁.gpr .lr).setWidth 64) = _; rw [g₁, f₁.2.1],
          by show some ((u₂.gpr .lr).setWidth 64) = _; rw [g₂, f₂.2.1], ?_, ?_, rfl⟩
        · show (q :: ts).find? (fun p => (u₁.syms p.1).setWidth 64 == (e.1.fa n).setWidth 64) = _
          rw [y₁, ← f₁.2.2.1]; exact f₁.2.2.2
        · show (q :: ts).find? (fun p => (u₂.syms p.1).setWidth 64 == (e.1.fa n).setWidth 64) = _
          rw [y₂, ← f₂.2.2.1]; exact f₂.2.2.2

/-! ## The calls of HMAC's functions -/

/-- The arguments of HMAC's `init`. -/
def IA (P : RfcHash) : Pred P := fun L _ _ u =>
  u.gpr .r0 = L.scr + BitVec.ofNat 32 0 ∧ u.gpr .r1 = L.scr + BitVec.ofNat 32 192 ∧
    u.gpr .r2 = L.fp + BitVec.ofNat 32 0 ∧ u.gpr .r3 = BitVec.ofNat 32 P.F.H.D ∧
    u.gpr .r12 = L.scr + BitVec.ofNat 32 384

/-- The arguments of the streaming `update`, for `cnt` bytes held and the
data at `dv L` of `len` bytes. -/
def UA (P : RfcHash) (cnt : Nat) (dv : Lay P.I.hashLen → BitVec 32) (len : Nat) : Pred P := fun L _ _ u =>
  u.gpr .r0 = L.scr + BitVec.ofNat 32 0 ∧ u.gpr .r1 = dv L ∧ u.gpr .r2 = BitVec.ofNat 32 cnt ∧
    u.gpr .r3 = 0 ∧ u.gpr .r7 = BitVec.ofNat 32 len ∧ u.gpr .r10 = L.scr + BitVec.ofNat 32 384

/-- The arguments of HMAC's `finalize`, for `cnt` bytes held and the MAC to `dst`. -/
def FA (P : RfcHash) (cnt dst : Nat) : Pred P := fun L _ _ u =>
  u.gpr .r0 = L.scr + BitVec.ofNat 32 0 ∧ u.gpr .r1 = L.scr + BitVec.ofNat 32 192 ∧
    u.gpr .r2 = BitVec.ofNat 32 cnt ∧ u.gpr .r3 = 0 ∧ u.gpr .r10 = L.fp + BitVec.ofNat 32 dst ∧
    u.gpr .r12 = L.scr + BitVec.ofNat 32 384

theorem lr_ia : LR (IA P) := fun _ _ _ _ _ ⟨a, b, c, d, e⟩ hr => ⟨(hr _ (by decide)).trans a,
  (hr _ (by decide)).trans b, (hr _ (by decide)).trans c, (hr _ (by decide)).trans d, (hr _ (by decide)).trans e⟩

theorem lr_ua {cnt : Nat} {dv : Lay P.I.hashLen → BitVec 32} {len : Nat} : LR (UA P cnt dv len) :=
  fun _ _ _ _ _ ⟨a, b, c, d, e, f⟩ hr => ⟨(hr _ (by decide)).trans a, (hr _ (by decide)).trans b,
    (hr _ (by decide)).trans c, (hr _ (by decide)).trans d, (hr _ (by decide)).trans e, (hr _ (by decide)).trans f⟩

theorem lr_fa {cnt dst : Nat} : LR (FA P cnt dst) :=
  fun _ _ _ _ _ ⟨a, b, c, d, e, f⟩ hr => ⟨(hr _ (by decide)).trans a, (hr _ (by decide)).trans b,
    (hr _ (by decide)).trans c, (hr _ (by decide)).trans d, (hr _ (by decide)).trans e, (hr _ (by decide)).trans f⟩

theorem hinit_ct :
    RelCT isa (Two P (IA P)) (.frame (.push [.r12, .lr]) (.call P.F.hiN P.F.hiC) (.pop .r12 8))
      fun _ _ => True :=
  two_exists fun e => hi_rel P.ok.hi (sp := e.1.fp) fun _ _ ⟨hL, _, _, c₁, c₂, a₁, a₂⟩ =>
    ⟨initA (P := P) hL c₁ a₁.1 a₁.2.1 a₁.2.2.1 a₁.2.2.2.1 a₁.2.2.2.2,
      initA (P := P) hL c₂ a₂.1 a₂.2.1 a₂.2.2.1 a₂.2.2.2.1 a₂.2.2.2.2, c₁.sp, c₂.sp⟩

theorem hupd_ct {cnt : Nat} {dv : Lay P.I.hashLen → BitVec 32} {len : Nat}
    (hd : ∀ L : Lay P.I.hashLen, L.Ok → DataOk L (dv L) len) (hlen : len ≤ 256) :
    RelCT isa (Two P (UA P cnt dv len))
      (.frame (.push [.r1, .r7, .r10, .r12]) (.call P.F.H.updN P.F.H.updC) (.pop .r1 16)) fun _ _ => True :=
  two_exists fun e => Proof.Pbkdf2.Whole.Arm.upd_rel P.ok.hH (sp := e.1.fp) fun _ _ ⟨hL, _, _, c₁, c₂, a₁, a₂⟩ =>
    ⟨updA (P := P) hL c₁ (hd _ hL) hlen a₁.1 a₁.2.1 a₁.2.2.2.2.1 a₁.2.2.2.2.2,
      updA (P := P) hL c₂ (hd _ hL) hlen a₂.1 a₂.2.1 a₂.2.2.2.2.1 a₂.2.2.2.2.2,
      by rw [Pbkdf2.Stream.Arm.count, Pbkdf2.Stream.Arm.count, a₁.2.2.1, a₁.2.2.2.1, a₂.2.2.1, a₂.2.2.2.1],
      c₁.sp, c₂.sp⟩

theorem hfin_ct {cnt dst : Nat} (hdst : dst + P.F.H.D ≤ 128) :
    RelCT isa (Two P (FA P cnt dst))
      (.frame (.push [.r10, .r12]) (.call P.F.hfN P.F.hfC) (.pop .r12 8)) fun _ _ => True :=
  two_exists fun e => hf_rel P.ok.hf (sp := e.1.fp) fun _ _ ⟨hL, _, _, c₁, c₂, a₁, a₂⟩ =>
    ⟨finA (P := P) hL c₁ hdst a₁.1 a₁.2.1 a₁.2.2.2.2.1 a₁.2.2.2.2.2,
      finA (P := P) hL c₂ hdst a₂.1 a₂.2.1 a₂.2.2.2.2.1 a₂.2.2.2.2.2,
      by rw [a₁.2.2.1, a₂.2.2.1], by rw [a₁.2.2.2.1, a₂.2.2.2.1], c₁.sp, c₂.sp⟩

/-! ## HMAC through the table -/

theorem initArgs_taint : TaintOk Cfg.initArgs := ⟨_, by taint_decide⟩
theorem updVArgs_taint : TaintOk Cfg.updVArgs := ⟨_, by taint_decide⟩

/-- HMAC's states for `K`. -/
theorem initK_ct {Φ : Pred P} : RelCT isa (Two P Φ) (cfgOf P).initK fun _ _ => True :=
  (two_wp (Ψ := IA P) (two_blk initArgs_taint) fun _ _ _ _ hL hk hc _ =>
    WP.mono (initArgs_ok hL hk.2.2.1 hc) fun _ ⟨c, _, a, b, d, e, f, _⟩ => ⟨c, a, b, d, e, f⟩).seq
    (tcall_ct (by decide) tfn_init lr_ia hinit_ct)

/-- The inner state updated with `V`. -/
theorem updV_ct {Φ : Pred P} : RelCT isa (Two P Φ) (cfgOf P).updV fun _ _ => True := by
  unfold Cfg.updV
  refine (two_wp (Ψ := UA P P.F.H.B (fun L => L.fp + BitVec.ofNat 32 fV) P.F.H.D) (two_blk updVArgs_taint)
    fun L _ _ t hL hk hc _ => ?_).seq
    (tcall_ct (by decide) tfn_upd lr_ua (hupd_ct (fun _ _ => .inl ⟨64, rfl, by anums⟩) (by anums)))
  simp only [Cfg.updVArgs, List.append_assoc, List.cons_append, List.nil_append]
  refine scrAt_ok hc (d := .r0) (by decide) (o := sInner) (by decide) fun t₁ c₁ _ v₁ k₁ => ?_
  refine fpAdd_ok c₁ (d := .r1) (by decide) (o := fV) (by decide) fun t₂ c₂ _ v₂ k₂ => ?_
  refine ldB_ok hL c₂ (d := .r2) (by decide) fun t₃ c₃ _ v₃ k₃ => ?_
  refine mov0_ok c₃ (d := .r3) (by decide) fun t₄ c₄ _ v₄ k₄ => ?_
  refine ldD_ok hL c₄ (d := .r7) (by decide) fun t₅ c₅ _ v₅ k₅ => ?_
  rw [← List.append_nil (scrAt .r10 sWork)]
  refine scrAt_ok c₅ (d := .r10) (by decide) (o := sWork) (by decide) fun t₆ c₆ _ v₆ k₆ => ?_
  refine WP.block_nil ⟨c₆, ?_, ?_, ?_, ?_, ?_, v₆⟩
  · rw [k₆ _ (by decide) (by decide), k₅ _ (by decide), k₄ _ (by decide), k₃ _ (by decide), k₂ _ (by decide)]
    exact v₁
  · rw [k₆ _ (by decide) (by decide), k₅ _ (by decide), k₄ _ (by decide), k₃ _ (by decide)]; exact v₂
  · rw [k₆ _ (by decide) (by decide), k₅ _ (by decide), k₄ _ (by decide), v₃, hk.2.2.1.1]
  · rw [k₆ _ (by decide) (by decide), k₅ _ (by decide)]; exact v₄
  · rw [k₆ _ (by decide) (by decide), v₅, hk.2.2.1.1]

/-- The inner state updated with the message's `len` bytes. -/
theorem updM_ct {Φ : Pred P} {len : Nat} (hlen : len ≤ 256) (ht : TaintOk (Cfg.updMArgs len)) :
    RelCT isa (Two P Φ) ((cfgOf P).updM len) fun _ _ => True := by
  unfold Cfg.updM
  refine (two_wp (Ψ := UA P (P.F.H.B + P.F.H.D) (fun L => L.scr + BitVec.ofNat 32 sMsg) len) (two_blk ht)
    fun L _ _ t hL hk hc _ => ?_).seq
    (tcall_ct (by decide) tfn_upd lr_ua
      (hupd_ct (fun _ _ => .inr ⟨sMsg, rfl, by simp only [sMsg]; omega, by simp only [sMsg]; omega⟩) hlen))
  simp only [Cfg.updMArgs, List.append_assoc, List.cons_append, List.nil_append]
  refine scrAt_ok hc (d := .r0) (by decide) (o := sInner) (by decide) fun t₁ c₁ _ v₁ k₁ => ?_
  refine scrAt_ok c₁ (d := .r1) (by decide) (o := sMsg) (by decide) fun t₂ c₂ _ v₂ k₂ => ?_
  refine ldB_ok hL c₂ (d := .r2) (by decide) fun t₃ c₃ _ v₃ k₃ => ?_
  refine ldD_ok hL c₃ (d := .r3) (by decide) fun t₄ c₄ _ v₄ k₄ => ?_
  refine wp_dpS (op2_reg _ _) fun t₅ u₅ => ?_
  have c₅ := c₄.upd u₅ (by decide)
  refine mov0_ok c₅ (d := .r3) (by decide) fun t₆ c₆ _ v₆ k₆ => ?_
  refine movw_ok c₆ (d := .r7) (v := len) (by decide) (by omega) fun t₇ c₇ _ v₇ k₇ => ?_
  rw [← List.append_nil (scrAt .r10 sWork)]
  refine scrAt_ok c₇ (d := .r10) (by decide) (o := sWork) (by decide) fun t₈ c₈ _ v₈ k₈ => ?_
  refine WP.block_nil ⟨c₈, ?_, ?_, ?_, ?_, ?_, v₈⟩
  · rw [k₈ _ (by decide) (by decide), k₇ _ (by decide), k₆ _ (by decide), u₅.other _ (by decide),
      k₄ _ (by decide), k₃ _ (by decide), k₂ _ (by decide) (by decide)]; exact v₁
  · rw [k₈ _ (by decide) (by decide), k₇ _ (by decide), k₆ _ (by decide), u₅.other _ (by decide),
      k₄ _ (by decide), k₃ _ (by decide)]; exact v₂
  · rw [k₈ _ (by decide) (by decide), k₇ _ (by decide), k₆ _ (by decide), u₅.gpr, dpVal,
      k₄ _ (by decide), v₃, v₄, hk.2.2.1.1, BitVec.ofNat_add]
  · rw [k₈ _ (by decide) (by decide), k₇ _ (by decide)]; exact v₆
  · rw [k₈ _ (by decide) (by decide)]; exact v₇

/-- The MAC, of `D + len` bytes, to the frame at `dst`. -/
theorem fin_ct {Φ : Pred P} {len dst : Nat} (hdst : dst + P.F.H.D ≤ 128)
    (he : encodable (BitVec.ofNat 32 dst) = true) (hle : encodable (BitVec.ofNat 32 len) = true)
    (ht : TaintOk (Cfg.finArgs len dst)) :
    RelCT isa (Two P Φ) ((cfgOf P).fin len dst) fun _ _ => True := by
  unfold Cfg.fin
  refine (two_wp (Ψ := FA P (P.F.H.B + P.F.H.D + len) dst) (two_blk ht) fun L _ _ t hL hk hc _ => ?_).seq
    (tcall_ct (by decide) tfn_fin lr_fa (hfin_ct hdst))
  simp only [Cfg.finArgs, List.append_assoc, List.cons_append, List.nil_append]
  refine scrAt_ok hc (d := .r0) (by decide) (o := sInner) (by decide) fun t₁ c₁ _ v₁ k₁ => ?_
  refine scrAt_ok c₁ (d := .r1) (by decide) (o := sOuter) (by decide) fun t₂ c₂ _ v₂ k₂ => ?_
  refine ldB_ok hL c₂ (d := .r2) (by decide) fun t₃ c₃ _ v₃ k₃ => ?_
  refine ldD_ok hL c₃ (d := .r3) (by decide) fun t₄ c₄ _ v₄ k₄ => ?_
  refine wp_dpS (op2_reg _ _) fun t₅ u₅ => ?_
  have c₅ := c₄.upd u₅ (by decide)
  refine wp_dpS (op2_imm hle) fun t₆ u₆ => ?_
  have c₆ := c₅.upd u₆ (by decide)
  refine mov0_ok c₆ (d := .r3) (by decide) fun t₇ c₇ _ v₇ k₇ => ?_
  refine fpAdd_ok c₇ (d := .r10) (by decide) he fun t₈ c₈ _ v₈ k₈ => ?_
  rw [← List.append_nil (scrAt .r12 sWork)]
  refine scrAt_ok c₈ (d := .r12) (by decide) (o := sWork) (by decide) fun t₉ c₉ _ v₉ k₉ => ?_
  refine WP.block_nil ⟨c₉, ?_, ?_, ?_, ?_, ?_, v₉⟩
  · rw [k₉ _ (by decide) (by decide), k₈ _ (by decide), k₇ _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), k₄ _ (by decide), k₃ _ (by decide), k₂ _ (by decide) (by decide)]; exact v₁
  · rw [k₉ _ (by decide) (by decide), k₈ _ (by decide), k₇ _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), k₄ _ (by decide), k₃ _ (by decide)]; exact v₂
  · rw [k₉ _ (by decide) (by decide), k₈ _ (by decide), k₇ _ (by decide), u₆.gpr, dpVal, u₅.gpr, dpVal,
      k₄ _ (by decide), v₃, v₄, hk.2.2.1.1, BitVec.ofNat_add, BitVec.ofNat_add]
  · rw [k₉ _ (by decide) (by decide), k₈ _ (by decide)]; exact v₇
  · rw [k₉ _ (by decide) (by decide)]; exact v₈

/-! ## HMAC -/

/-- HMAC's states, with `n` bytes of text after the key. -/
def Sx (P : RfcHash) (n : Nat) : Pred P := fun L g m₀ u =>
  ∃ t text, St P L g m₀ t text u ∧ text.length = n

theorem initS_ct {Φ : Pred P} : RelCT isa (Two P Φ) (cfgOf P).initK (Two P (Sx P 0)) :=
  two_wp initK_ct fun _ _ _ t hL hk hc _ =>
    WP.mono (init_step hL hk.2.2.1 hc) fun _ h => ⟨h.ctx, t, [], h, rfl⟩

theorem updVS_ct : RelCT isa (Two P (Sx P 0)) (cfgOf P).updV (Two P (Sx P P.F.H.D)) :=
  two_wp updV_ct fun _ _ _ _ hL hk _ ⟨t, text, hs, hl⟩ => by
    rw [List.eq_nil_of_length_eq_zero hl] at hs
    exact WP.mono (updV_step hL hk.2.2.1 hs) fun _ h => ⟨h.ctx, t, _, h, length_bytesAt _ _ _⟩

theorem updMS_ct {len : Nat} (hlen : len ≤ 256) (ht : TaintOk (Cfg.updMArgs len)) :
    RelCT isa (Two P (Sx P P.F.H.D)) ((cfgOf P).updM len) (Two P (Sx P (P.F.H.D + len))) :=
  two_wp (updM_ct hlen ht) fun _ _ _ _ hL hk _ ⟨t, text, hs, hl⟩ =>
    WP.mono (updM_step hL hk.2.2.1 hs hl hlen) fun _ h => ⟨h.ctx, t, _, h, by
      rw [List.length_append, hl, length_bytesAt]⟩

/-- `V = HMAC_K(V)`. -/
theorem hmacV_ct {Φ : Pred P} : RelCT isa (Two P Φ) (cfgOf P).hmacV fun _ _ => True :=
  initS_ct.seq (updVS_ct.seq (fin_ct (by simp only [fV]; anums) (by decide) (by decide) ⟨_, by taint_decide⟩))

/-- `K = HMAC_K(V ‖ m)`, for the message of `len` bytes at `scratch + sMsg`. -/
theorem hmacK_ct {Φ : Pred P} {len : Nat} (hlen : len ≤ 256) (hle : encodable (BitVec.ofNat 32 len) = true)
    (t₂ : TaintOk (Cfg.updMArgs len)) (t₃ : TaintOk (Cfg.finArgs len fK)) :
    RelCT isa (Two P Φ) ((cfgOf P).hmacK len) fun _ _ => True :=
  initS_ct.seq (updVS_ct.seq ((updMS_ct hlen t₂).seq (fin_ct (by simp only [fK]; anums) (by decide) hle t₃)))

/-- `K = HMAC_K(V ‖ b (‖ d ‖ h))`, then `V = HMAC_K(V)`. -/
theorem rekey_gen_ct {Φ : Pred P} {b : Nat} (hb : b < 2) (full : Bool) {len : Nat}
    (hlen : len = if full then 1 + 2 * P.Q else 1) (t₁ : TaintOk ((cfgOf P).msg b full))
    (t₂ : TaintOk (Cfg.updMArgs len)) (t₃ : TaintOk (Cfg.finArgs len fK)) :
    RelCT isa (Two P Φ) (.seq (.block ((cfgOf P).msg b full)) (.seq ((cfgOf P).hmacK len) (cfgOf P).hmacV))
      fun _ _ => True := by
  have hl : len ≤ 256 := by cases full <;> simp only [hlen, Bool.false_eq_true, ite_true, ite_false] <;> anums
  have he : encodable (BitVec.ofNat 32 len) = true := encodable_lt (by
    cases full <;> simp only [hlen, Bool.false_eq_true, ite_true, ite_false] <;> anums)
  refine (two_wp (Ψ := Tt P) (two_blk t₁) fun _ _ _ _ hL hk hc _ =>
    WP.mono (msg_ok hL (by rw [hk.1]) hc hb full) fun _ h => ⟨h.1, trivial⟩).seq ?_
  exact (two_wp (Ψ := Tt P) (hmacK_ct hl he t₂ t₃) fun _ _ _ _ hL hk hc _ =>
    WP.mono (hmacK_ok hL hk.2.2.1 hc hl he) fun _ h => ⟨h.1, trivial⟩).seq hmacV_ct

theorem rekeyFull_ct {Φ : Pred P} (b : Nat) (hb : b < 2) :
    RelCT isa (Two P Φ) ((cfgOf P).rekeyFull b) fun _ _ => True := by
  obtain rfl | rfl : b = 0 ∨ b = 1 := by omega
  · exact rekey_gen_ct hb true (len := 1 + 2 * (cfgOf P).len) rfl (by exact (rT P).msgF₀) (by exact (rT P).updM)
      (by exact (rT P).finM)
  · exact rekey_gen_ct hb true (len := 1 + 2 * (cfgOf P).len) rfl (by exact (rT P).msgF₁) (by exact (rT P).updM)
      (by exact (rT P).finM)

theorem rekey_ct {Φ : Pred P} : RelCT isa (Two P Φ) (cfgOf P).rekey fun _ _ => True :=
  rekey_gen_ct (b := 0) (by decide) false (len := 1) rfl (by exact (rT P).msgN) ⟨_, by taint_decide⟩
    ⟨_, by taint_decide⟩

/-! ## The byte loops -/

/-- A byte copy's registers: `n` bytes from `q L` to `p L`. -/
abbrev CpA (P : RfcHash) (p q : Lay P.I.hashLen → BitVec 32) (n : Nat) : Pred P := fun L _ _ u =>
  u.gpr .r1 = q L ∧ u.gpr .r2 = p L ∧ u.gpr .r3 = BitVec.ofNat 32 n

theorem copyLoop_taint : ∃ hc, (VG.Taint.check taint (τr [.r1, .r2, .r3]) copyLoop hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- The byte loop, from registers that agree. -/
theorem cp_ct {Φ : Pred P} {p q : Lay P.I.hashLen → BitVec 32} {n : Nat}
    (h : ∀ L g m₀ u, Φ L g m₀ u → CpA P p q n L g m₀ u) :
    RelCT isa (Two P Φ) copyLoop fun _ _ => True :=
  two_tr [.r1, .r2, .r3] (fun _ _ _ _ _ _ _ _ _ f₁ f₂ r hr => by
    obtain ⟨a₁, b₁, c₁⟩ := h _ _ _ _ f₁; obtain ⟨a₂, b₂, c₂⟩ := h _ _ _ _ f₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact a₁.trans a₂.symm
    · exact b₁.trans b₂.symm
    · exact c₁.trans c₂.symm) copyLoop_taint

/-! ## The candidate -/

/-- After `j` of the candidate's `V`s, from some `K` and `V`. -/
abbrev CJ (P : RfcHash) (j : Nat) : Pred P := fun L g m₀ u => ∃ t₀ K V₀, CI P L g m₀ t₀ K V₀ j u

/-- `T`'s length, `j` blocks. -/
abbrev TL (P : RfcHash) (j : Nat) : Pred P := fun L _ _ u => tlen L u.mem = BitVec.ofNat 32 (j * P.F.H.D)

/-- The arguments of the copy of `V` to `T`'s end, and `j` blocks. -/
abbrev KA (P : RfcHash) (j : Nat) : Pred P := fun L g m₀ u =>
  CpA P (fun L => L.fp + BitVec.ofNat 32 (fT + j * P.F.H.D)) (fun L => L.fp + BitVec.ofNat 32 fV) P.F.H.D
    L g m₀ u ∧ TL P j L g m₀ u

theorem keepArgs_taint : TaintOk Cfg.keepArgs := ⟨_, by taint_decide⟩

/-- One `V`'s blocks and calls leak the same in both runs. -/
theorem candStep_trace {j : Nat} (hj : j < P.nV) :
    RelCT isa (Two P (CJ P j)) (cfgOf P).candStep fun _ _ => True := by
  obtain ⟨-, hND, -⟩ := nV_facts P
  obtain ⟨_, _, _, _, hD16, hD64, _, _, _, _, _, _, _⟩ := P.sizes
  obtain ⟨_, _, _, _, hQ8, hQ66, _, _⟩ := P.wsizes
  have hb : (j + 1) * P.F.H.D ≤ 136 :=
    Nat.le_trans (Nat.mul_le_mul (show j + 1 ≤ P.nV by omega) (Nat.le_refl P.F.H.D)) (by omega)
  have hjD : (j + 1) * P.F.H.D = j * P.F.H.D + P.F.H.D := Nat.succ_mul _ _
  have : fT = 328 := rfl; have : fV = 64 := rfl; have : fTlen = 464 := rfl
  refine (two_wp (Ψ := TL P j) hmacV_ct fun L g m₀ t hL hk hc hJ => ?_).seq
    ((two_wp (Ψ := KA P j) (two_blk keepArgs_taint) fun L g m₀ t hL hk hc hl =>
      WP.mono (keepArgs_ok hL hk.2.2.1 hc hl) fun u ⟨c, hm, h1, h2, h3, _⟩ =>
        ⟨c, ⟨h1, h2, h3⟩, by show tlen L u.mem = _; rw [hm]; exact hl⟩).seq
    ((two_wp (Ψ := Tt P) (cp_ct fun _ _ _ _ h => h.1) fun L g m₀ t hL hk hc ⟨⟨h1, h2, h3⟩, _⟩ => ?_).seq
      (two_blk (by exact (rT P).tStep))))
  · obtain ⟨_, _, _, hI⟩ := hJ
    have hbf := hL.B_fit
    refine WP.mono (hmacV_ok hL hk.2.2.1 hc) fun u ⟨hc₁, _, hf₁, _⟩ => ⟨hc₁, ?_⟩
    show tlen L u.mem = _
    rw [← hI.len]
    exact hf₁.readW (Region.contains_self _ _) (fun r hr => by
      simp only [KVW, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hL.stk_SCR (by omega_arith)
      · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)) (by decide)
  · have hbf := hL.B_fit
    have hpa : State.addr (L.fp + BitVec.ofNat 32 (fT + j * P.F.H.D)) =
        L.B + BitVec.ofNat 64 (352 + j * P.F.H.D) := by
      rw [hL.fpA (by omega_arith)]; congr 2; omega_arith
    have hqa : State.addr (L.fp + BitVec.ofNat 32 fV) = L.B + BitVec.ofNat 64 88 := hL.fpA (by omega_arith)
    exact WP.mono (cp_ok hL hc (p := L.fp + BitVec.ofNat 32 (fT + j * P.F.H.D))
      (q := L.fp + BitVec.ofNat 32 fV) (n := P.F.H.D) (by omega_arith) (by omega_arith) h1 h2 h3
      (by rw [fp_toNat hL (by omega_arith)]; have := hL.na; omega_arith)
      (by rw [fp_toNat hL (by omega_arith)]; have := hL.na; omega_arith)
      (by rw [hqa]; exact ⟨L.FR, by simp, within_fr _ (by omega_arith) (by omega_arith)⟩)
      (by rw [hpa]; exact ⟨L.FR, by simp, within_fr _ (by omega_arith) (by omega_arith)⟩)
      (by rw [hpa]; exact safe_low L (by omega_arith))
      (by rw [hpa, hqa]; exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)))
      fun _ h => ⟨h.1, trivial⟩

/-- The loop of the candidate's `V`s, in two runs: at the same block. -/
theorem candLoop_ct :
    RelCT isa (Two P (CJ P 0)) (.loop (cfgOf P).candStep .ne) (Two P (CJ P P.nV)) := by
  obtain ⟨hN1, hND, -⟩ := nV_facts P
  obtain ⟨_, _, _, _, _, hD64, _, _, _, _, _, _, _⟩ := P.sizes
  obtain ⟨_, _, _, _, _, hQ66, _, _⟩ := P.wsizes
  have h := VG.RelCT.loop (M := isa) (c := .ne) (Q := Two P (CJ P P.nV))
    (fun n => fun s₁ s₂ => 0 < n ∧ n ≤ P.nV ∧ Two P (CJ P (P.nV - n)) s₁ s₂) (n := P.nV)
    (body := (cfgOf P).candStep)
    (fun n => by
      refine fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨hn0, hnN, hp⟩ e₁ e₂ => ?_
      have hj : P.nV - n < P.nV := by omega
      have hb : (P.nV - n + 1) * P.F.H.D ≤ 136 :=
        Nat.le_trans (Nat.mul_le_mul (show P.nV - n + 1 ≤ P.nV by omega) (Nat.le_refl P.F.H.D)) (by omega)
      obtain ⟨ht, hq⟩ := (two_wp (Ψ := fun L g m₀ u => CJ P (P.nV - n + 1) L g m₀ u ∧
          isa.eval .ne u = some (decide ((P.nV - n + 1) * P.F.H.D < P.Q))) (candStep_trace hj)
        fun L g m₀ t hL hk hc ⟨t₀, K, V₀, hI⟩ => WP.mono (step_ok hL hk.2.2.1 hb hI)
          fun u ⟨hI', hcf⟩ => ⟨hI'.ctx, ⟨t₀, K, V₀, hI'⟩, hcf⟩) s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
      refine ⟨ht, ?_, ?_, ?_⟩
      · obtain ⟨_, _, _, _, _, _, f₁, f₂⟩ := hq
        rw [f₁.2, f₂.2]
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

theorem candTop_ct {Φ : Pred P} : RelCT isa (Two P Φ) (.block (cfgOf P).candTop) fun _ _ => True := by
  cases hb : P.R.big
  · rw [show (cfgOf P).candTop = [] by
      simp only [Cfg.candTop, show (cfgOf P).big = false from hb, Bool.false_eq_true, ite_false]]
    exact two_blk ⟨_, by taint_decide⟩
  · rw [show (cfgOf P).candTop = (cfgOf P).conv fT (cfgOf P).sh by
      simp only [Cfg.candTop, show (cfgOf P).big = true from hb, ite_true]]
    exact two_blk (by exact (rT P).convT hb)

theorem tInit_taint : TaintOk Cfg.tInit := ⟨_, by taint_decide⟩

/-- The candidate: its calls, blocks and loops leak the same in both runs. -/
theorem cand_ct {Φ : Pred P} : RelCT isa (Two P Φ) (cfgOf P).cand fun _ _ => True := by
  unfold Cfg.cand
  exact (two_wp (Ψ := CJ P 0) (two_blk tInit_taint) fun L g m₀ t hL hk hc _ =>
    WP.mono (tInit_ci hL hc) fun u hI => ⟨hI.ctx, _, _, _, hI⟩).seq (candLoop_ct.seq candTop_ct)

/-! ## One candidate -/

/-- `core`, in its frame, with arguments that agree. -/
theorem core_ct {i : Nat} :
    RelCT isa (Two P fun L _ m₀ u => P₁ P L m₀ i u ∧ CoreRegs P L u)
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
        Proof.Pbkdf2.Whole.Arm.p2_arg0 (s := s₁) (by omega_arith),
        Proof.Pbkdf2.Whole.Arm.p2_arg0 (s := s₂) (by omega_arith), a₁.r12, a₂.r12, sp_two c₁ c₂, true_and]
      intro c hc
      have hmem : c ∈ e.1.cs := hk.2.1 ▸ hc
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
  refine (two_wp (Ψ := fun L _ m₀ u => P₁ P L m₀ i u) cand_ct fun _ _ _ _ hL hk hc hi =>
    try₁_ok hL hk hc hi).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ u => P₁ P L m₀ i u ∧ CoreRegs P L u) (two_blk (by exact (rT P).coreArgs))
    fun _ _ _ _ _ _ hc hi => try₂_ok hc hi).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ u => P₃ P L m₀ i u) core_ct fun _ _ _ _ hL hk hc hi =>
    try₃_ok hL hk hc hi.1 hi.2).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ u => Mid P L m₀ i u) (two_blk goOn_blk)
    fun _ _ _ _ hL _ hc hi => try₄_ok hL hc hi).seq ?_
  refine VG.RelCT.ite (fun _ _ ⟨_, _, _, hx, _, _, f₁, f₂⟩ => dec_two hx f₁ f₂) ?_ ?_
  · exact ((two_wp (Ψ := Tt P) rekey_ct fun _ _ _ _ hL hk hc _ =>
      WP.mono (rekey_ok hL hk.2.2.1 (by rw [hk.1]) hc) fun _ h => ⟨h.1, trivial⟩).seq
      (two_blk again_blk)).mono (fun _ _ h => h.1) fun _ _ h => h
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

theorem tries_ct :
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
theorem initCnt_blk (c : Cfg) : TaintOk c.initCnt := by
  obtain ⟨h, hs⟩ := initCnt_blk₀
  have hb : Taint.NoBase (τr ptrRegs) := ⟨rfl, rfl⟩
  have e := Taint.check_eraseOff (.block c.initCnt) h hb
  have e₀ := Taint.check_eraseOff (.block [.movw .r9 (BitVec.ofNat 16 8)]) h hb
  have he : Code.eraseOff (.block c.initCnt) = Code.eraseOff (.block [.movw .r9 (BitVec.ofNat 16 8)]) := rfl
  exact ⟨h, e ▸ he ▸ e₀ ▸ hs⟩

theorem wipe_taint : ∃ hc, (VG.Taint.check taint (τr ptrRegs) Cfg.wipe hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem prepX_ct : RelCT isa (Two P (Tt P)) (cfgOf P).prepX (Two P (fun L _ m₀ t => QX P L m₀ t)) := by
  refine two_wp ?_ fun L g m₀ t hL hk hc _ => stageX_ok hL hk hc
  rw [Cfg.prepX]
  exact (two_wp (Ψ := CpA P (fun L => L.fp + BitVec.ofNat 32 (fX + P.Q - min P.F.H.D P.Q)) (fun L => L.dg)
      (min P.F.H.D P.Q)) (two_blk (by exact (rT P).xArgs)) fun L g m₀ t hL hk hc _ =>
    WP.mono (xArgs_ok hL hk.2.2.1 hc) fun _ ⟨c, _, _, h3, h2, h1⟩ => ⟨c, h1, h2, h3⟩).seq
    (cp_ct fun _ _ _ _ h => h)

/-- The arguments of the copy of `core`'s digest, if `big`. -/
theorem xcArgs_ok {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem} (hL : L.Ok) (hT : TabL P L)
    (hW : P.R.big = true) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).xcArgs) t fun u => Ctx L g m₀ u ∧ u.gpr .r1 = L.dg ∧
      u.gpr .r2 = L.fp + BitVec.ofNat 32 (fXc + P.Q - 1 - P.F.H.D) ∧ u.gpr .r3 = BitVec.ofNat 32 P.F.H.D := by
  obtain ⟨-, hQ66, -, hQD⟩ := P.sizesW hW
  obtain ⟨_, _, _, _, hD16, hD64, _, _, _, _, _, _, _⟩ := P.sizes
  have : fXc = 260 := rfl
  rw [Cfg.xcArgs, WP.block_append_iff]
  refine WP.mono (zeroN_ok hL hc (k := 17) (o := fXc) (by decide)) fun u₁ ⟨c₁, _, _, _⟩ => ?_
  refine ldD_ok hL c₁ (d := .r3) (by decide) fun u₂ c₂ _ v₂ _ => ?_
  rw [hT.1] at v₂
  refine WP.mono (dstArgs_ok hL c₂ (a := fXc + (cfgOf P).len - 1) (n := P.F.H.D) (by simp only [cfgOf_len]; anums)
    (by simp only [cfgOf_len]; omega_arith) v₂) fun u₃ ⟨c₃, _, h2, h1, h3, _⟩ => ?_
  rw [cfgOf_len] at h2
  exact ⟨c₃, h1, h2, h3⟩

theorem prepH_ct : RelCT isa (Two P (fun L _ m₀ t => QX P L m₀ t)) (cfgOf P).prepH
    (Two P (fun L _ m₀ t => QA P L m₀ t)) := by
  refine two_wp ?_ fun L g m₀ t hL hk hc hx => stageH_ok hL hk hc hx
  cases hb : P.R.big
  · rw [show (cfgOf P).prepH = .block (cfgOf P).reduce by
      simp only [Cfg.prepH, show (cfgOf P).big = false from hb, Bool.false_eq_true, ite_false]]
    exact two_blk (by exact (rT P).reduce hb)
  · rw [show (cfgOf P).prepH = (cfgOf P).prepC by
      simp only [Cfg.prepH, show (cfgOf P).big = true from hb, ite_true], Cfg.prepC]
    obtain ⟨-, hQ66, -, hQD⟩ := P.sizesW hb
    obtain ⟨_, _, _, _, hD16, hD64, _, _, _, _, _, _, _⟩ := P.sizes
    refine (two_wp (Ψ := CpA P (fun L => L.fp + BitVec.ofNat 32 (fXc + P.Q - 1 - P.F.H.D)) (fun L => L.dg) P.F.H.D)
      (two_blk (by exact (rT P).xcArgs hb)) fun L g m₀ t hL hk hc _ =>
        WP.mono (xcArgs_ok hL hk.2.2.1 hb hc) fun _ ⟨c, h1, h2, h3⟩ => ⟨c, h1, h2, h3⟩).seq ?_
    refine (two_wp (Ψ := Tt P) (cp_ct fun _ _ _ _ h => h) fun L g m₀ t hL hk hc ⟨h1, h2, h3⟩ => ?_).seq
      (two_blk (by exact (rT P).convC hb))
    have hbf := hL.B_fit
    have ng := hL.ng
    have hdn : P.F.H.D ≤ P.I.hashLen := hk.2.2.2
    have : fXc = 260 := rfl
    have hpa : State.addr (L.fp + BitVec.ofNat 32 (fXc + P.Q - 1 - P.F.H.D)) =
        L.B + BitVec.ofNat 64 (284 + (P.Q - 1 - P.F.H.D)) := by
      rw [hL.fpA (by omega_arith)]; congr 2; omega_arith
    exact WP.mono (cp_ok hL hc (p := L.fp + BitVec.ofNat 32 (fXc + P.Q - 1 - P.F.H.D)) (q := L.dg)
      (n := P.F.H.D) (by omega_arith) (by omega_arith) h1 h2 h3 (by omega_arith)
      (by rw [fp_toNat hL (by omega_arith)]; have := hL.na; omega_arith)
      ⟨L.DG, by simp, within_base _ hdn⟩
      (by rw [hpa]; exact ⟨L.FR, by simp, within_fr _ (by omega_arith) (by omega_arith)⟩)
      (by rw [hpa]; exact safe_low L (by omega_arith))
      (by rw [hpa]; exact (hL.stk_DG (d := 284 + (P.Q - 1 - P.F.H.D)) (n := P.F.H.D)
        (by omega_arith)).symm.sub_left (Region.sub_prefix hdn))) fun _ h => ⟨h.1, trivial⟩

/-- The body after the prologue. -/
theorem body_ct :
    RelCT isa (Two P (Tt P)) (.seq (cfgOf P).prepX (.seq (cfgOf P).prepH (.seq (.block Cfg.initKV)
      (.seq ((cfgOf P).rekeyFull 0) (.seq ((cfgOf P).rekeyFull 1) (.seq (.block (cfgOf P).initCnt)
        (.seq (.loop (cfgOf P).tryOne .ne) Cfg.wipe))))))) fun _ _ => True := by
  refine prepX_ct.seq (prepH_ct.seq ?_)
  refine (two_wp (Ψ := fun L _ m₀ t => QB P L m₀ t) (two_blk (by exact (rT P).initKV))
    fun _ _ _ _ hL _ hc h => stageB_ok hL hc h).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ t => QC P L m₀ t) (rekeyFull_ct 0 (by decide))
    fun _ _ _ _ hL hk hc h => stageC_ok (P := P) hL hk hc h).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ t => QD P L m₀ t) (rekeyFull_ct 1 (by decide))
    fun _ _ _ _ hL hk hc h => stageD_ok (P := P) hL hk hc h).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ t => LoopInv P L m₀ 0 t) (two_blk (initCnt_blk _))
    fun _ _ _ _ _ _ hc h => stageE_ok (P := P) hc h).seq ?_
  exact tries_ct.seq (two_tr ptrRegs (fun _ _ _ _ _ _ _ c₁ c₂ _ _ => ptr_two c₁ c₂) wipe_taint)

/-! ## The prologue -/

/-- Two runs from states that satisfy the precondition and agree on public
data, after the frame's allocation. -/
def Entered (P : RfcHash) (ns : List String) (a b : State) : Prop :=
  ∃ s₁ s₂, ((rfcP P ns).pre s₁ ∧ (rfcP P ns).pre s₂ ∧ (rfcP P ns).pub s₁ s₂) ∧
    a = allocated frameBytes s₁ ∧ b = allocated frameBytes s₂

theorem prologue_tail : ∃ hc, (VG.Taint.check taint (τr [.r12])
    (.block (Impl.Ecdsa.Rfc6979.Arm.saved.map (fun p => Instr.str p.1 .r12 p.2) ++
      ([.mov .r4 (.reg .r0), .mov .r5 (.reg .r1), .str .r2 .r12 fDigest, .ldr .r11 .r12 frameBytes,
        .ldr .r6 .r12 (frameBytes + 4), .mov .r8 (.reg .r12)] : List Instr)))
    hc).isSome = true := ⟨_, by taint_decide⟩

/-- The prologue reads `sp`, which agrees, and then addresses the frame through `r12`. -/
theorem start_blk {ns : List String} : RelCT isa (Entered P ns) (.block Cfg.prologue) fun _ _ => True := by
  rw [Cfg.prologue, List.cons_append]
  refine block_cons_ct (R := fun a b => ∀ r ∈ [Reg.r12], a.gpr r = b.gpr r)
    (fun a b a' b' ⟨s₁, s₂, ⟨_, _, hsp, _⟩, ea, eb⟩ ha hb => ?_) ?_
  · subst ea eb
    simp only [reduceExec, show (0 : Nat) < 256 by decide, ↓reduceIte, Option.some.injEq] at ha hb
    subst ha hb
    refine ⟨rfl, fun r hr => ?_⟩
    simp only [List.mem_singleton] at hr; subst hr
    simp only [State.setReg, ↓reduceIte, allocated, hsp]
  · let ⟨_, h⟩ := prologue_tail
    exact VG.RelCT.taint (A := taint) _ (fun _ _ h => agree_regs h) h

/-- After the prologue, the runs are related by `Two`, with the layout of the
arguments, which agree, and the same number of candidates. -/
theorem start_ct {ns : List String} (hns : ∀ n ∈ [P.F.hiN, P.F.H.updN, P.F.hfN], n ∈ ns) :
    RelCT isa (Entered P ns) (.block Cfg.prologue) (Two P (Tt P)) := by
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
  have eqFa : (fun n => if n ∈ [P.F.hiN, P.F.H.updN, P.F.hfN] then s₂.syms n else 0) =
      (fun n => if n ∈ [P.F.hiN, P.F.H.updN, P.F.hfN] then s₁.syms n else 0) := by
    funext n
    by_cases hn : n ∈ [P.F.hiN, P.F.H.updN, P.F.hfN]
    · simp only [hn, ↓reduceIte]
      exact (hns' n (hns n hn)).symm
    · simp only [hn, ↓reduceIte]
  have hl : layOf P s₂ = layOf P s₁ := by
    simp only [layOf, lay, hsp, h0, h1, h2, ha0, ha1, eqSy, eqFa]
  have hr : (result P.I s₁.mem (State.addr (layOf P s₁).d) (State.addr (layOf P s₁).dg)).2 =
      (result P.I s₂.mem (State.addr (layOf P s₁).d) (State.addr (layOf P s₁).dg)).2 := by
    show (result P.I s₁.mem (State.addr (s₁.gpr .r1)) (State.addr (s₁.gpr .r2))).2 =
      (result P.I s₂.mem (State.addr (s₁.gpr .r1)) (State.addr (s₁.gpr .r2))).2
    rw [hres, h1, h2]
  rw [hl] at y₂
  exact ⟨ht, ⟨layOf P s₁, s₁.gpr, s₂.gpr, s₁.mem, s₂.mem⟩, lay_ok p₁, coreOk_lay P s₁,
    congrArg (fun x => if x = 0 then P.I.tries - 1 else x - 1) hr, y₁, y₂, trivial, trivial⟩

/-- Runs whose public data agree (with the addresses of the hash function's
HMAC functions among `ns`) have the same layout, and stop at the same
candidate. -/
theorem sign_ct {ns : List String} (hns : ∀ n ∈ [P.F.hiN, P.F.H.updN, P.F.hfN], n ∈ ns) :
    ConstantTime isa (rfcP P ns).pre (rfcP P ns).pub (cfgOf P).sign := by
  refine VG.RelCT.constantTime (Q := fun _ _ => True) (alloc_ct (R := fun _ _ => True) ?_)
  rw [Cfg.body]
  exact ((start_ct hns).seq body_ct).mono (fun _ _ ⟨s₁, s₂, h, ea, eb⟩ => ⟨s₁, s₂, h, ea, eb⟩) fun _ _ h => h

end VG.Proof.Ecdsa.Rfc6979.Arm

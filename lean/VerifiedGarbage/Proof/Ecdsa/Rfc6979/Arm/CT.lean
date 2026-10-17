module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Correct
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Correct
public import VerifiedGarbage.Proof.Framework.Arm.RelCT
meta import VerifiedGarbage.Proof.Framework.Arm.RelCT
public import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
public import VerifiedGarbage.Proof.Framework.Arm.TaintErase
meta import VerifiedGarbage.Proof.Framework.Arm.TaintErase
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-!
# Deterministic ECDSA on 32-bit ARM: constant time, up to the number of candidates

As on x86 (`Proof/Ecdsa/Rfc6979/X86/CT.lean`), for the run's hash function
`P`: two runs whose public data agree have the same layout, the same hash
function, and stop at the same candidate (`exitAt`, from the contract's
leakage: the number of candidates RFC 6979 tries). Between the prologue and
the frame's release they are related by `Two`: both satisfy `Ctx` with that
layout (and `Φ`, what the next piece needs). The code between the calls
addresses only the frame, the buffers and `scratch`, from the registers that
hold the pointers and the hash function's code, which agree (the taint
analysis: of the parts that depend on the curve in each curve's file,
`CurveBlks`, and of the others here); each dispatch on the hash function's
code takes the same case in both runs (`disp_ct`), and each call, in its
frame, is of constant-time code whose public data agree (`hi_rel`,
`upd_rel`, `hf_rel`, `frame2_rel`); whether a candidate takes another `V`
agrees, since it depends on `D` alone (`more_ok`); and the loop's branch
agrees, since in both runs it goes on after candidate `i` iff `i` is before
the candidate it stops at (`go_iff`). The prologue addresses only the frame
and the arguments on the stack, from `sp`, which agrees (`start_blk`), and
the frame's allocation and release access no memory (`alloc_ct`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Impl.Pbkdf2.Stream.Arm (scrAt)
open VG.Proof.Pbkdf2.Whole.Arm (hi_rel hf_rel frame2_rel)

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

/-! ## Two runs -/

/-- What each of two runs has, between the prologue and the frame's release. -/
abbrev Env (P : RfcHash) := Lay P.F.H.D × (Reg → BitVec 32) × (Reg → BitVec 32) × Mem × Mem

/-- What the proof needs of each run at a point of the code. -/
abbrev Pred (P : RfcHash) := Lay P.F.H.D → (Reg → BitVec 32) → Mem → State → Prop

/-- Two runs with the layout and saved registers of `e`, that stop at the
same candidate, each satisfying `Ctx` and `Φ`. -/
def TwoAt (P : RfcHash) (Φ : Pred P) (e : Env P) (a b : State) : Prop :=
  e.1.Ok ∧ HOk P e.1 ∧ exitAt P e.1 e.2.2.2.1 = exitAt P e.1 e.2.2.2.2 ∧ Ctx e.1 e.2.1 e.2.2.2.1 a ∧
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
    (hw : ∀ (L : Lay P.F.H.D) g m₀ (t : State), L.Ok → HOk P L → Ctx L g m₀ t → Φ L g m₀ t →
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

/-- Code that keeps `Ctx`, whatever `Φ` held before. -/
theorem two_any {c : Prog isa} {Φ : Pred P}
    (hct : RelCT isa (Two P Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay P.F.H.D) g m₀ (t : State), L.Ok → HOk P L → Ctx L g m₀ t →
      WP isa c t fun t' => Ctx L g m₀ t') :
    RelCT isa (Two P Φ) c (Two P fun _ _ _ _ => True) :=
  two_wp hct fun L g m₀ t hL hq hc _ => WP.mono (hw L g m₀ t hL hq hc) fun _ h => ⟨h, trivial⟩

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

/-- The taint check of code whose addresses depend only on the registers that hold pointers. -/
abbrev TaintOk (is : List Instr) : Prop := TaintC (τr ptrRegs) (.block is)

/-- Such code. -/
theorem two_prog {c : Prog isa} {Φ : Pred P} (h : TaintC (τr ptrRegs) c) :
    RelCT isa (Two P Φ) c fun _ _ => True :=
  let ⟨_, h⟩ := h
  VG.RelCT.taint (A := taint) (τr ptrRegs) (fun _ _ ⟨_, _, _, _, c₁, c₂, _, _⟩ => agree_regs (ptr_two c₁ c₂)) h

theorem two_blk {is : List Instr} {Φ : Pred P} (h : TaintOk is) :
    RelCT isa (Two P Φ) (.block is) fun _ _ => True :=
  two_prog h

/-! ## The dispatch on the hash function -/

theorem sel_two {L : Lay P.F.H.D} {g : Reg → BitVec 32} {m₀ : Mem} {t : State} (hq : HOk P L)
    (hc : Ctx L g m₀ t) : Proof.Dispatch.Arm.sel .r6 t = P.c := by
  simp only [Proof.Dispatch.Arm.sel, hc.r6, hq.2, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by have := P.codes _ P.mem; show code P.F < 2 ^ 32; omega)

/-- The dispatch takes the case of the run's hash function in both runs,
after the tests, which change only the flags. -/
theorem disp_ct {f : Impl.Pbkdf2.Whole.Arm.Fns → Prog isa} {Φ : Pred P} {Q : State → State → Prop}
    (hΦ : ∀ L g m₀ t t', Φ L g m₀ t → Proof.Dispatch.Arm.FlagsOnly t t' → Φ L g m₀ t')
    (h : RelCT isa (Two P Φ) (f P.F) Q) : RelCT isa (Two P Φ) ((cfgOf P).disp f) Q := by
  refine Proof.Dispatch.chain_relCT (Proof.Dispatch.Arm.tests .r6)
    (by rw [disp_keys]; intro k hk; obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hk; exact P.codes F hF)
    (by rw [disp_keys]; exact P.nodup)
    (fun s₁ s₂ ⟨_, _, hq, _, c₁, c₂, _⟩ => ⟨by rw [sel_two hq c₁, sel_two hq c₂],
      by rw [disp_keys, sel_two hq c₁]; exact List.mem_map_of_mem P.mem⟩) fun k c hm => ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨a₁, a₂, ⟨e, hL, hq, hx, c₁, c₂, f₁, f₂⟩, hk, r₁, r₂, _, _⟩ x₁ x₂
  obtain ⟨F, hF, he⟩ := List.mem_map.mp hm
  obtain ⟨e₁, rfl⟩ := Prod.mk.inj he
  have : F = P.F := nodup_map_inj P.nodup hF P.mem (e₁.trans (hk.symm.trans (sel_two hq c₁)))
  subst this
  exact h _ _ _ _ _ _ ⟨e, hL, hq, hx, c₁.flags r₁, c₂.flags r₂, hΦ _ _ _ _ _ f₁ r₁, hΦ _ _ _ _ _ f₂ r₂⟩ x₁ x₂

/-! ## The blocks that depend on neither the curve nor the hash function -/

theorem init_blk : TaintOk Cfg.hmacArgs₁ := ⟨_, by taint_decide⟩
theorem vUpd_blk : TaintOk (Cfg.hmacArgs₂ [.dp .add .r1 .r8 (.imm (BitVec.ofNat 32 fV))] 0) := ⟨_, by taint_decide⟩
theorem vFin_blk : TaintOk (Cfg.hmacArgs₃ 0 fV) := ⟨_, by taint_decide⟩
theorem kUpd_blk : TaintOk (Cfg.hmacArgs₂ (scrAt .r1 sMsg) 1) := ⟨_, by taint_decide⟩
theorem kFin_blk : TaintOk (Cfg.hmacArgs₃ 1 fK) := ⟨_, by taint_decide⟩
theorem msg₀_blk : TaintOk (Cfg.msg 0 0 false) := ⟨_, by taint_decide⟩
theorem initKV_blk : TaintOk Cfg.initKV := ⟨_, by taint_decide⟩
theorem keepV_blk₀ : TaintOk (Cfg.keepV 0) := ⟨_, by taint_decide⟩
theorem goOn_blk : TaintOk Cfg.goOn := ⟨_, by taint_decide⟩
theorem again_blk : TaintOk Cfg.again := ⟨_, by taint_decide⟩
theorem stop_blk : TaintOk Cfg.stop := ⟨_, by taint_decide⟩
theorem wipe_blk : TaintOk Cfg.wipe := ⟨_, by taint_decide⟩
theorem nil_blk : TaintOk [] := ⟨_, by taint_decide⟩
theorem initCnt_blk₀ : TaintOk [.movw .r9 (BitVec.ofNat 16 8)] := ⟨_, by taint_decide⟩

/-- Code with the same analysis as checked code, up to its offsets and `movw`
immediates, which the analysis does not read (`Taint.check_eraseOff`). -/
theorem taint_erase {c c' : Prog isa} (h : TaintC (τr ptrRegs) c')
    (he : VG.Arm.Code.eraseOff c = VG.Arm.Code.eraseOff c') :
    TaintC (τr ptrRegs) c := by
  obtain ⟨hc, hs⟩ := h
  have hb : VG.Arm.Taint.NoBase (τr ptrRegs) := ⟨rfl, rfl⟩
  exact ⟨hc, VG.Arm.Taint.check_eraseOff c hc hb ▸ he ▸ VG.Arm.Taint.check_eraseOff c' hc hb ▸ hs⟩

theorem initCnt_blk (c : Cfg) : TaintOk c.initCnt := taint_erase initCnt_blk₀ rfl

theorem keepV_blk (i : Nat) : TaintOk (Cfg.keepV i) := taint_erase keepV_blk₀ rfl

/-- The parts of the code that depend on the curve, from its file. -/
theorem curveBlks (P : RfcHash) : CurveBlks (cfgOf P) :=
  let B := P.R.blks
  ⟨B.digest, B.msg₀, B.msg₁, B.upd, B.fin, B.more, B.conv, B.coreArgs⟩

theorem more_blk (i : Nat) : TaintOk ((cfgOf P).more i) := taint_erase (curveBlks P).more rfl

/-! ## The calls of HMAC's functions -/

/-- The arguments of HMAC's `init`. -/
def IA (P : RfcHash) (L : Lay P.F.H.D) (_ : Reg → BitVec 32) (_ : Mem) (u : State) : Prop :=
  u.gpr .r0 = L.scr + BitVec.ofNat 32 0 ∧ u.gpr .r1 = L.scr + BitVec.ofNat 32 192 ∧
    u.gpr .r2 = L.fp + BitVec.ofNat 32 0 ∧ u.gpr .r3 = BitVec.ofNat 32 P.F.H.D ∧
    u.gpr .r12 = L.scr + BitVec.ofNat 32 384

/-- The arguments of the streaming `update`, for the data at `dv L` of `len` bytes. -/
def UA (P : RfcHash) (dv : Lay P.F.H.D → BitVec 32) (len : Nat) (L : Lay P.F.H.D) (_ : Reg → BitVec 32)
    (_ : Mem) (u : State) : Prop :=
  u.gpr .r0 = L.scr + BitVec.ofNat 32 0 ∧ u.gpr .r1 = dv L ∧ u.gpr .r2 = BitVec.ofNat 32 P.F.H.B ∧
    u.gpr .r3 = 0 ∧ u.gpr .r7 = BitVec.ofNat 32 len ∧ u.gpr .r10 = L.scr + BitVec.ofNat 32 384

/-- The arguments of HMAC's `finalize`, for `len` bytes of data and the MAC to `dst`. -/
def FA (P : RfcHash) (len dst : Nat) (L : Lay P.F.H.D) (_ : Reg → BitVec 32) (_ : Mem) (u : State) : Prop :=
  u.gpr .r0 = L.scr + BitVec.ofNat 32 0 ∧ u.gpr .r1 = L.scr + BitVec.ofNat 32 192 ∧
    u.gpr .r2 = BitVec.ofNat 32 (P.F.H.B + len) ∧ u.gpr .r3 = 0 ∧ u.gpr .r10 = L.fp + BitVec.ofNat 32 dst ∧
    u.gpr .r12 = L.scr + BitVec.ofNat 32 384

theorem hinit_ct : RelCT isa (Two P (IA P)) (Cfg.callInit P.F) fun _ _ => True :=
  two_exists fun e => hi_rel P.ok.hi (sp := e.1.fp) fun _ _ ⟨hL, _, _, c₁, c₂, a₁, a₂⟩ =>
    ⟨initA (P := P) hL c₁ a₁.1 a₁.2.1 a₁.2.2.1 a₁.2.2.2.1 a₁.2.2.2.2,
      initA (P := P) hL c₂ a₂.1 a₂.2.1 a₂.2.2.1 a₂.2.2.2.1 a₂.2.2.2.2, c₁.sp, c₂.sp⟩

theorem hupd_ct {dv : Lay P.F.H.D → BitVec 32} {len : Nat} (hd : ∀ L : Lay P.F.H.D, L.Ok → DataOk L (dv L) len)
    (hlen : len ≤ 256) :
    RelCT isa (Two P (UA P dv len)) (Cfg.callUpd P.F) fun _ _ => True :=
  two_exists fun e => Proof.Pbkdf2.Whole.Arm.upd_rel P.ok.hH (sp := e.1.fp) fun _ _ ⟨hL, _, _, c₁, c₂, a₁, a₂⟩ =>
    ⟨updA (P := P) hL c₁ (hd _ hL) hlen a₁.1 a₁.2.1 a₁.2.2.2.2.1 a₁.2.2.2.2.2,
      updA (P := P) hL c₂ (hd _ hL) hlen a₂.1 a₂.2.1 a₂.2.2.2.2.1 a₂.2.2.2.2.2,
      by rw [Pbkdf2.Stream.Arm.count, Pbkdf2.Stream.Arm.count, a₁.2.2.1, a₁.2.2.2.1, a₂.2.2.1, a₂.2.2.2.1],
      c₁.sp, c₂.sp⟩

theorem hfin_ct {len dst : Nat} (hdst : dst + P.F.H.D ≤ 128) :
    RelCT isa (Two P (FA P len dst)) (Cfg.callFin P.F) fun _ _ => True :=
  two_exists fun e => hf_rel P.ok.hf (sp := e.1.fp) fun _ _ ⟨hL, _, _, c₁, c₂, a₁, a₂⟩ =>
    ⟨finA (P := P) hL c₁ hdst a₁.1 a₁.2.1 a₁.2.2.2.2.1 a₁.2.2.2.2.2,
      finA (P := P) hL c₂ hdst a₂.1 a₂.2.1 a₂.2.2.2.2.1 a₂.2.2.2.2.2,
      by rw [a₁.2.2.1, a₂.2.2.1], by rw [a₁.2.2.2.1, a₂.2.2.2.1], c₁.sp, c₂.sp⟩

/-! ## One HMAC -/

/-- After HMAC's `init` and `update`: the states, for the state before. -/
def Ini (P : RfcHash) : Pred P := fun L g m₀ u => ∃ t, Inited P L g m₀ t u
def Upt (P : RfcHash) (dv : Lay P.F.H.D → BitVec 32) (len : Nat) : Pred P :=
  fun L g m₀ u => ∃ t, Updated P L g m₀ t (dv L) len u

theorem initS_ct {Φ : Pred P} :
    RelCT isa (Two P Φ) (.seq (.block Cfg.hmacArgs₁) ((cfgOf P).disp Cfg.callInit)) (Two P (Ini P)) :=
  two_wp ((two_wp (Ψ := IA P) (two_blk init_blk) fun _ _ _ _ _ hq hc _ =>
      WP.mono (initArgs_ok hq hc) fun _ ⟨c, _, a⟩ => ⟨c, a.1, a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2.1⟩).seq
      (disp_ct (fun _ _ _ _ _ h r => by simp only [IA, r.gpr]; exact h) hinit_ct))
    fun _ _ _ t hL hq hc _ => WP.mono (init_step hL hq hc) fun _ h => ⟨h.ctx, t, h⟩

theorem updS_ct {dataA : List Instr} {dv : Lay P.F.H.D → BitVec 32} {lc : Nat}
    (hdA : ∀ (L : Lay P.F.H.D) g m₀, L.Ok → DataA L g m₀ dataA (dv L))
    (hd : ∀ L : Lay P.F.H.D, L.Ok → DataOk L (dv L) (P.F.H.D + lc)) (hlen : P.F.H.D + lc ≤ 256)
    (hlc : encodable (BitVec.ofNat 32 lc) = true) (t₂ : TaintOk (Cfg.hmacArgs₂ dataA lc)) :
    RelCT isa (Two P (Ini P)) (.seq (.block (Cfg.hmacArgs₂ dataA lc)) ((cfgOf P).disp Cfg.callUpd))
      (Two P (Upt P dv (P.F.H.D + lc))) :=
  two_wp ((two_wp (Ψ := UA P dv (P.F.H.D + lc)) (two_blk t₂) fun L g m₀ _ hL hq hc _ =>
      WP.mono (updArgs_ok hq hc (hdA L g m₀ hL) hlc)
        fun _ ⟨c, _, a⟩ => ⟨c, a.1, a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2.1, a.2.2.2.2.2.1⟩).seq
      (disp_ct (fun _ _ _ _ _ h r => by simp only [UA, r.gpr]; exact h) (hupd_ct hd hlen)))
    fun L g m₀ _ hL hq _ ⟨t, hi⟩ => WP.mono (upd_step hL hq hi (hdA L g m₀ hL) hlc (hd L hL) hlen)
      fun _ h => ⟨h.ctx, t, h⟩

theorem finS_ct {dv : Lay P.F.H.D → BitVec 32} {lc dst : Nat} (hdst : dst + P.F.H.D ≤ 128)
    (hlc : encodable (BitVec.ofNat 32 lc) = true) (he : encodable (BitVec.ofNat 32 dst) = true)
    (t₃ : TaintOk (Cfg.hmacArgs₃ lc dst)) :
    RelCT isa (Two P (Upt P dv (P.F.H.D + lc))) (.seq (.block (Cfg.hmacArgs₃ lc dst))
      ((cfgOf P).disp Cfg.callFin)) fun _ _ => True :=
  (two_wp (Ψ := FA P (P.F.H.D + lc) dst) (two_blk t₃) fun _ _ _ _ _ hq hc _ =>
    WP.mono (finArgs_ok hq hc hlc he) fun _ ⟨c, _, a⟩ =>
      ⟨c, a.1, a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2.1, a.2.2.2.2.2.1⟩).seq
    (disp_ct (fun _ _ _ _ _ h r => by simp only [FA, r.gpr]; exact h) (hfin_ct hdst))

/-- `HMAC_K(data)`: its blocks address only the frame and `scratch`, and its
calls are constant time with arguments that agree. -/
theorem hmac_ct {dataA : List Instr} {dv : Lay P.F.H.D → BitVec 32} {lc dst : Nat} {Φ : Pred P}
    (hdA : ∀ (L : Lay P.F.H.D) g m₀, L.Ok → DataA L g m₀ dataA (dv L))
    (hd : ∀ L : Lay P.F.H.D, L.Ok → DataOk L (dv L) (P.F.H.D + lc)) (hlen : P.F.H.D + lc ≤ 256)
    (hdst : dst + P.F.H.D ≤ 128) (hlc : encodable (BitVec.ofNat 32 lc) = true)
    (he : encodable (BitVec.ofNat 32 dst) = true)
    (t₂ : TaintOk (Cfg.hmacArgs₂ dataA lc)) (t₃ : TaintOk (Cfg.hmacArgs₃ lc dst)) :
    RelCT isa (Two P Φ) ((cfgOf P).hmac dataA lc dst) fun _ _ => True :=
  RelCT.assoc (initS_ct.seq (RelCT.assoc ((updS_ct hdA hd hlen hlc t₂).seq (finS_ct hdst hlc he t₃))))

/-- `V = HMAC_K(V)`. -/
theorem hmacV_ct {Φ : Pred P} : RelCT isa (Two P Φ) (cfgOf P).hmacV fun _ _ => True :=
  hmac_ct (dv := fun L => L.fp + BitVec.ofNat 32 64) (lc := 0) (dst := 64)
    (fun _ _ _ _ => dataV) (fun _ _ => .inl ⟨64, rfl, by anums⟩) (by anums) (by anums) (by decide) (by decide)
    vUpd_blk vFin_blk

/-- `K = HMAC_K(m)`, for the message of `D + lc` bytes at `scratch + 2256`. -/
theorem hmacK_ct {Φ : Pred P} {lc : Nat} (hlc : lc ≤ 133)
    (t₂ : TaintOk (Cfg.hmacArgs₂ (scrAt .r1 sMsg) lc)) (t₃ : TaintOk (Cfg.hmacArgs₃ lc fK)) :
    RelCT isa (Two P Φ) ((cfgOf P).hmac (scrAt .r1 sMsg) lc fK) fun _ _ => True :=
  hmac_ct (dv := fun L => L.scr + BitVec.ofNat 32 2256) (dst := 0) (fun _ _ _ _ => dataM)
    (fun _ _ => .inr ⟨2256, rfl, by omega, by anums⟩) (by anums) (by anums) (by clear t₂ t₃; revert lc; decide) (by decide)
    t₂ t₃

/-- `K = HMAC_K(m)`, then `V = HMAC_K(V)`, for the message `m = V ‖ b (‖ d ‖ h)`. -/
theorem rekey_gen_ct {Φ : Pred P} {b : Nat} (hb : b < 2) {full : Bool} {lc : Nat}
    (hlc : lc = if full then 2 * P.Q + 1 else 1)
    (t₁ : TaintOk (Cfg.msg P.Q b full))
    (t₂ : TaintOk (Cfg.hmacArgs₂ (scrAt .r1 sMsg) lc)) (t₃ : TaintOk (Cfg.hmacArgs₃ lc fK)) :
    RelCT isa (Two P Φ) (.seq (.block (Cfg.msg P.Q b full))
      (.seq ((cfgOf P).hmac (scrAt .r1 sMsg) lc fK) (cfgOf P).hmacV)) fun _ _ => True := by
  have hlc' : lc ≤ 133 := by cases full <;> simp only [hlc, Bool.false_eq_true, ite_true, ite_false] <;> anums
  refine (two_any (two_blk t₁) fun _ _ _ _ hL hq hc =>
    WP.mono (msg_ok hL hq hc hb full) fun _ h => h.1).seq ?_
  exact (two_any (hmacK_ct hlc' t₂ t₃) fun _ _ _ _ hL hq hc =>
    WP.mono (hmacK_ok (P := P) hL hq hc hlc') fun _ h => h.1).seq hmacV_ct

theorem rekeyFull_ct {Φ : Pred P} (b : Nat) (hb : b < 2) :
    RelCT isa (Two P Φ) ((cfgOf P).rekeyFull b) fun _ _ => True := by
  obtain rfl | rfl : b = 0 ∨ b = 1 := by omega
  · exact rekey_gen_ct (full := true) hb rfl (curveBlks P).msg₀ (curveBlks P).upd (curveBlks P).fin
  · exact rekey_gen_ct (full := true) hb rfl (curveBlks P).msg₁ (curveBlks P).upd (curveBlks P).fin

theorem rekey_ct {Φ : Pred P} : RelCT isa (Two P Φ) (cfgOf P).rekey fun _ _ => True :=
  rekey_gen_ct (b := 0) (by decide) (full := false) rfl msg₀_blk kUpd_blk kFin_blk

/-! ## The candidate -/

/-- Step `i`, when it runs: `V = HMAC_K(V)`, kept in `T`. -/
theorem step_ct {Φ : Pred P} (i : Nat) : RelCT isa (Two P Φ) ((cfgOf P).step i) fun _ _ => True :=
  (two_any hmacV_ct fun _ _ _ _ hL hq hc => WP.mono (hmacV_ok hL hq hc) fun _ h => h.1).seq
    (two_blk (keepV_blk i))

/-- Whether step `i` runs: as `D`, which agrees, says. -/
def MoreAt (P : RfcHash) (i : Nat) : Pred P := fun _ _ _ u => isa.eval .eq u = some (decide (i * P.F.H.D < P.Q))

theorem stepIte_ok {L : Lay P.F.H.D} {g : Reg → BitVec 32} {m₀ : Mem} (hL : L.Ok) (hq : HOk P L) {i : Nat}
    (hi : i < 4) {u : State} (hc : Ctx L g m₀ u) (hm : MoreAt P i L g m₀ u) :
    WP isa (.ite .eq ((cfgOf P).step i) (.block [])) u fun u' => Ctx L g m₀ u' := by
  refine WP.ite _ hm (fun hb => ?_) (fun _ => WP.block_nil hc)
  have hiQ : P.F.H.D * i < P.Q := by rw [Nat.mul_comm]; exact of_decide_eq_true hb
  exact WP.seq (WP.mono (hmacV_ok hL hq hc) fun _ h => WP.mono (keepV_ok hL hq h.1 hi hiQ) fun _ h => h.1)

/-- The steps after the first. -/
theorem moreSteps_ct : ∀ (is : List Nat), (∀ i ∈ is, i < 4) →
    RelCT isa (Two P fun _ _ _ _ => True) ((cfgOf P).moreSteps is) fun _ _ => True
  | [], _ => two_blk nil_blk
  | i :: is, h => by
    have hi := h i List.mem_cons_self
    refine (two_wp (Ψ := MoreAt P i) (two_blk (more_blk i)) fun _ _ _ _ _ hq hc _ =>
      WP.mono (more_ok hq hc hi) fun _ h => ⟨h.1, h.2.2.2⟩).seq ?_
    exact (two_wp (Ψ := fun _ _ _ _ => True) (VG.RelCT.ite (fun _ _ ⟨_, _, _, _, _, _, f₁, f₂⟩ => f₁.trans f₂.symm)
      ((step_ct i).mono (fun _ _ h => h.1) fun _ _ h => h)
      ((two_blk nil_blk).mono (fun _ _ h => h.1) fun _ _ h => h))
      fun _ _ _ _ hL hq hc hm => WP.mono (stepIte_ok hL hq hi hc hm) fun _ h => ⟨h, trivial⟩).seq
      (moreSteps_ct is fun j hj => h j (List.mem_cons_of_mem _ hj))

/-- The steps after the first keep `Ctx`. -/
theorem moreSteps_ctx {L : Lay P.F.H.D} {g : Reg → BitVec 32} {m₀ : Mem} (hL : L.Ok) (hq : HOk P L) :
    ∀ (is : List Nat), (∀ i ∈ is, i < 4) → ∀ {u : State}, Ctx L g m₀ u →
      WP isa ((cfgOf P).moreSteps is) u fun u' => Ctx L g m₀ u'
  | [], _, _, hc => WP.block_nil hc
  | i :: is, h, _, hc => by
    have hi := h i List.mem_cons_self
    refine WP.seq (WP.mono (more_ok hq hc hi) fun u₁ ⟨c₁, _, _, e₁⟩ => ?_)
    exact WP.seq (WP.mono (stepIte_ok hL hq hi c₁ e₁) fun _ c₂ =>
      moreSteps_ctx hL hq is (fun j hj => h j (List.mem_cons_of_mem _ hj)) c₂)

theorem steps_lt (P : RfcHash) : ∀ i ∈ (List.range (cfgOf P).steps).drop 1, i < 4 := by
  intro i hi
  have hQ := P.wsizes
  have hs4 : (cfgOf P).steps ≤ 4 := by show (P.Q + 19) / 20 ≤ 4; omega
  have := List.mem_range.mp (List.mem_of_mem_drop hi)
  omega

/-- The candidate: its calls and blocks leak the same in both runs. -/
theorem cand_ct {Φ : Pred P} : RelCT isa (Two P Φ) (cfgOf P).cand fun _ _ => True := by
  refine (two_any (step_ct 0) fun _ _ _ _ hL hq hc => WP.seq (WP.mono (hmacV_ok hL hq hc) fun _ h =>
    WP.mono (keepV_ok hL hq h.1 (i := 0) (by decide) (by have := P.wsizes; omega)) fun _ h => h.1)).seq ?_
  refine (two_any (moreSteps_ct _ (steps_lt P)) fun _ _ _ _ hL hq hc =>
    moreSteps_ctx hL hq _ (steps_lt P) hc).seq ?_
  exact two_prog (curveBlks P).conv

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
        Proof.Pbkdf2.Whole.Arm.p2_arg0 (s := s₁) (by omega), Proof.Pbkdf2.Whole.Arm.p2_arg0 (s := s₂) (by omega),
        a₁.r12, a₂.r12, sp_two c₁ c₂, and_self]

/-- Whether to go on agrees: in both runs, iff the candidate is before the one it stops at. -/
theorem dec_two {L : Lay P.F.H.D} {m₁ m₂ : Mem} {i : Nat} (hx : exitAt P L m₁ = exitAt P L m₂) {u₁ u₂ : State}
    (h₁ : Mid P L m₁ i u₁) (h₂ : Mid P L m₂ i u₂) : isa.eval .ne u₁ = isa.eval .ne u₂ := by
  rw [h₁.dec, h₂.dec]
  refine congrArg some (decide_eq_decide.mpr ?_)
  rw [go_iff h₁.lt h₁.fails, go_iff h₂.lt h₂.fails, hx]

/-- What one candidate leaves: the end, or the next candidate. -/
def After (P : RfcHash) (i : Nat) (L : Lay P.F.H.D) (_ : Reg → BitVec 32) (m₀ : Mem) (t : State) : Prop :=
  (isa.eval .ne t = some false ∧ Exit P L m₀ i t) ∨ (isa.eval .ne t = some true ∧ LoopInv P L m₀ (i + 1) t)

theorem tryOne_trace {i : Nat} :
    RelCT isa (Two P fun L _ m₀ t => LoopInv P L m₀ i t) (cfgOf P).tryOne fun _ _ => True := by
  refine (two_wp (Ψ := fun L _ m₀ u => P₁ P L m₀ i u) cand_ct fun _ _ _ _ hL hk hc hi =>
    try₁_ok hL hk hc hi).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ u => P₁ P L m₀ i u ∧ CoreRegs P L u) (two_blk (curveBlks P).coreArgs)
    fun _ _ _ _ _ _ hc hi => try₂_ok hc hi).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ u => P₃ P L m₀ i u) core_ct fun _ _ _ _ hL hk hc hi =>
    try₃_ok hL hk hc hi.1 hi.2).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ u => Mid P L m₀ i u) (two_blk goOn_blk)
    fun _ _ _ _ _ _ hc hi => try₄_ok hc hi).seq ?_
  refine VG.RelCT.ite (fun _ _ ⟨_, _, _, hx, _, _, f₁, f₂⟩ => dec_two hx f₁ f₂) ?_ ?_
  · exact ((two_any rekey_ct fun _ _ _ _ hL hk hc =>
      WP.mono (rekey_ok hL hk hc) fun _ h => h.1).seq
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
    have hgo : sigI P e.1 m' i = none ∧ i + 1 < P.R.I.tries := ⟨hI.fails i (by omega), hI.lt⟩
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
  have h : RelCT isa (Two P fun L _ m₀ t => LoopInv P L m₀ (P.R.I.tries - P.R.I.tries) t)
      (.loop (cfgOf P).tryOne .ne) (Two P fun L _ m₀ t => ∃ i, Exit P L m₀ i t) :=
    VG.RelCT.loop (M := isa) (fun n => Two P fun L _ m₀ t => LoopInv P L m₀ (P.R.I.tries - n) t)
      (fun n => tryOne_ct.mono (fun _ _ h => h) fun _ _ ⟨he, hf, ht⟩ =>
        ⟨he, fun h => (hf h).mono fun _ _ _ _ hx => ⟨_, hx⟩, fun h => by
          obtain ⟨e, hL, hq, hx, c₁, c₂, f₁, f₂⟩ := ht h
          have hn := next_n f₁.lt
          refine ⟨P.R.I.tries - (P.R.I.tries - n + 1), hn.1, e, hL, hq, hx, c₁, c₂, ?_, ?_⟩ <;> rwa [hn.2]⟩)
      P.R.I.tries
  rwa [Nat.sub_self] at h

/-! ## The frame's body -/

/-- The body after the prologue, `h`, `V` and `K`. -/
theorem rest_ct :
    RelCT isa (Two P fun L _ m₀ t => QB P L m₀ t) (.seq ((cfgOf P).rekeyFull 0) (.seq ((cfgOf P).rekeyFull 1)
      (.seq (.block (cfgOf P).initCnt) (.seq (.loop (cfgOf P).tryOne .ne) (.block Cfg.wipe)))))
      fun _ _ => True := by
  refine (two_wp (Ψ := fun L _ m₀ t => QC P L m₀ t) (rekeyFull_ct 0 (by omega)) fun _ _ _ _ hL hk hc h =>
    stageC_ok (P := P) hL hk hc h).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ t => QD P L m₀ t) (rekeyFull_ct 1 (by omega)) fun _ _ _ _ hL hk hc h =>
    stageD_ok (P := P) hL hk hc h).seq ?_
  refine (two_wp (Ψ := fun L _ m₀ t => LoopInv P L m₀ 0 t) (two_blk (initCnt_blk _))
    fun _ _ _ _ _ _ hc h => stageE_ok (P := P) hc h).seq ?_
  exact loop_ct.seq (two_blk wipe_blk)

/-- What the digest needs: `r10` holds its address. -/
def R10 (P : RfcHash) : Pred P := fun L _ _ t => t.gpr .r10 = L.dg

/-- Steps a–c: `h`, `core`'s digest, `V` and `K`, after the prologue. -/
theorem stageB_ct :
    RelCT isa (Two P (R10 P)) (.seq (cfgOf P).digest (.block Cfg.initKV)) (Two P fun L _ m₀ t => QB P L m₀ t) := by
  have hd : RelCT isa (Two P (R10 P)) (cfgOf P).digest fun _ _ => True :=
    let ⟨_, h⟩ := (curveBlks P).digest
    VG.RelCT.taint (A := taint) _ (fun _ _ ⟨_, _, _, _, c₁, c₂, f₁, f₂⟩ => agree_regs fun r hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact f₁.trans f₂.symm
      · exact ptr_two c₁ c₂ r hr) h
  refine (two_wp (Ψ := fun L _ m₀ t => QA P L m₀ t) hd fun _ _ _ _ hL hk hc h10 =>
    stageA_ok (P := P) hL hk hc h10).seq ?_
  exact two_wp (two_blk initKV_blk) fun _ _ _ _ hL _ hc hq => initKV_stage hL hc hq

/-! ## The prologue -/

/-- The relation the prologue keeps after its first instruction: `sp`, and
`r12`, the frame's base, agree. -/
abbrev SR (a b : State) : Prop := a.sp = b.sp ∧ a.gpr .r12 = b.gpr .r12

/-- An instruction that leaks the same from states related by `SR`, and keeps it. -/
def Good (i : Instr) : Prop :=
  ∀ a b a' b', SR a b → exec i a = some a' → exec i b = some b' → addrs i a = addrs i b ∧ SR a' b'

theorem setReg_sr {a b : State} {d : Reg} (hd : d ≠ .r12) (h : SR a b) (x y : BitVec 32) :
    SR (a.setReg d x) (b.setReg d y) := by
  refine ⟨h.1, ?_⟩
  simp only [State.setReg, show (Reg.r12 = d) = False from propext ⟨fun e => hd e.symm, False.elim⟩, ite_false]
  exact h.2

theorem str_good (t : Reg) (off : Nat) : Good (.str t .r12 off) := by
  intro a b a' b' h ha hb
  have k : ∀ {s s' : State}, exec (.str t .r12 off) s = some s' → s'.sp = s.sp ∧ s'.gpr = s.gpr := by
    intro s s' hs
    revert hs
    simp only [exec, State.store32]
    split_ifs <;> intro hs <;> cases hs <;> exact ⟨rfl, rfl⟩
  obtain ⟨k₁, k₂⟩ := k ha
  obtain ⟨k₃, k₄⟩ := k hb
  exact ⟨by simp only [addrs, h.2], by rw [k₁, k₃]; exact h.1, by rw [k₂, k₄]; exact h.2⟩

theorem ldrSp_good {t : Reg} (ht : t ≠ .r12) (off : Nat) : Good (.ldrSp t off) := by
  intro a b a' b' h ha hb
  have k : ∀ {s s' : State}, exec (.ldrSp t off) s = some s' → ∃ x, s' = s.setReg t x := by
    intro s s' hs
    revert hs
    simp only [exec]
    split_ifs
    · intro hs
      obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.mp hs
      exact ⟨x, rfl⟩
    · intro hs; cases hs
  obtain ⟨x, rfl⟩ := k ha
  obtain ⟨y, rfl⟩ := k hb
  exact ⟨by simp only [addrs, h.1], setReg_sr ht h x y⟩

theorem mov_good {d : Reg} (hd : d ≠ .r12) (o : Op2) : Good (.mov d o) := by
  intro a b a' b' h ha hb
  obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.mp ha
  obtain ⟨y, -, rfl⟩ := Option.map_eq_some_iff.mp hb
  exact ⟨rfl, setReg_sr hd h x y⟩

theorem dp_good (op : DpOp) {d : Reg} (hd : d ≠ .r12) (n : Reg) (o : Op2) : Good (.dp op d n o) := by
  intro a b a' b' h ha hb
  obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.mp ha
  obtain ⟨y, -, rfl⟩ := Option.map_eq_some_iff.mp hb
  exact ⟨rfl, setReg_sr hd h _ _⟩

theorem nil_blk₀ : TaintC (τr []) (.block []) := ⟨_, by taint_decide⟩

theorem good_ct : ∀ (is : List Instr), (∀ i ∈ is, Good i) → RelCT isa SR (.block is) fun _ _ => True
  | [], _ =>
    let ⟨_, h⟩ := nil_blk₀
    VG.RelCT.taint (A := taint) (τr []) (fun _ _ _ => agree_regs fun _ h => absurd h List.not_mem_nil) h
  | i :: is, h => block_cons_ct (h i List.mem_cons_self) (good_ct is fun j hj => h j (List.mem_cons_of_mem _ hj))

/-- Two runs from states that satisfy the precondition, with the hash
function `P`, and agree on public data, after the frame's allocation. -/
def Entered (P : RfcHash) (a b : State) : Prop :=
  ∃ s₁ s₂, (((rfcArm P.R.I 456).pre s₁ ∧ (stackArg s₁ 1).toNat = P.k) ∧
    ((rfcArm P.R.I 456).pre s₂ ∧ (stackArg s₂ 1).toNat = P.k) ∧ (rfcArm P.R.I 456).pub s₁ s₂) ∧
    a = allocated frameBytes s₁ ∧ b = allocated frameBytes s₂

/-- The prologue reads `sp`, which agrees, and then addresses the frame through
`r12` and the arguments on the stack from `sp`. -/
theorem start_blk : RelCT isa (Entered P) (.block Cfg.prologue) fun _ _ => True := by
  rw [Cfg.prologue, List.cons_append]
  refine block_cons_ct (R := SR) (fun a b a' b' ⟨s₁, s₂, ⟨_, _, hsp, _⟩, ea, eb⟩ ha hb => ?_) (good_ct _ ?_)
  · subst ea eb
    simp only [exec, show (0 : Nat) < 256 by decide, ↓reduceIte, Option.some.injEq] at ha hb
    subst ha hb
    refine ⟨rfl, ?_, ?_⟩
    · show s₁.sp - _ = s₂.sp - _
      rw [hsp]
    · show (if Reg.r12 = Reg.r12 then s₁.sp - BitVec.ofNat 32 frameBytes + BitVec.ofNat 32 0 else s₁.gpr .r12) =
        (if Reg.r12 = Reg.r12 then s₂.sp - BitVec.ofNat 32 frameBytes + BitVec.ofNat 32 0 else s₂.gpr .r12)
      simp only [hsp, ↓reduceIte]
  · intro i hi
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with ⟨p, -, rfl⟩ | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact str_good _ _
    · exact ldrSp_good (by decide) _
    · exact ldrSp_good (by decide) _
    · exact mov_good (by decide) _
    · exact mov_good (by decide) _
    · exact mov_good (by decide) _
    · exact mov_good (by decide) _
    · exact dp_good _ (by decide) _ _
    · exact mov_good (by decide) _
    · exact dp_good _ (by decide) _ _

/-- After the prologue, the runs are related by `Two`, with the layout of the
arguments, which agree, and the same number of candidates. -/
theorem start_ct : RelCT isa (Entered P) (.block Cfg.prologue) (Two P (R10 P)) := by
  intro a b t₁ t₂ a' b' hp e₁ e₂
  obtain ⟨ht, -⟩ := start_blk _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨s₁, s₂, ⟨⟨p₁, k₁⟩, ⟨p₂, k₂⟩, hsp, h0, h1, h2, h3, ha0, ha1, hres⟩, rfl, rfl⟩ := hp
  have hD₁ := digestLen_eq p₁ k₁
  have hD₂ := digestLen_eq p₂ k₂
  obtain ⟨_, u₁, x₁, y₁⟩ := entry_ok p₁ hD₁
  obtain ⟨_, u₂, x₂, y₂⟩ := entry_ok p₂ hD₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  have hl : lay P.F.H.D P.R.I.ecdsa.curve.len s₂ = lay P.F.H.D P.R.I.ecdsa.curve.len s₁ := by
    simp only [lay, hsp, h0, h1, h2, h3, ha0, ha1]
  have hr : (result P (lay P.F.H.D P.R.I.ecdsa.curve.len s₁) s₁.mem).2 =
      (result P (lay P.F.H.D P.R.I.ecdsa.curve.len s₁) s₂.mem).2 := by
    rw [anyResult_eq hD₁ k₁, anyResult_eq hD₂ k₂, hl] at hres
    exact hres
  rw [hl] at y₂
  exact ⟨ht, ⟨lay P.F.H.D P.R.I.ecdsa.curve.len s₁, s₁.gpr, s₂.gpr, s₁.mem, s₂.mem⟩, lay_ok' p₁ hD₁,
    hOk_lay hD₁ k₁, congrArg (fun x => if x = 0 then P.R.I.tries - 1 else x - 1) hr, y₁.1, y₂.1, y₁.2,
    y₂.2.trans (h2.symm)⟩

/-- Runs with the hash function `P` whose public data agree have the same
layout, and stop at the same candidate. -/
theorem sign_ct : ConstantTime isa (fun s => (rfcArm P.R.I 456).pre s ∧ (stackArg s 1).toNat = P.k)
    (rfcArm P.R.I 456).pub (cfgOf P).sign := by
  refine VG.RelCT.constantTime (Q := fun _ _ => True) (alloc_ct (R := fun _ _ => True) ?_)
  unfold Cfg.body
  exact (start_ct.seq (RelCT.assoc (stageB_ct.seq rest_ct))).mono
    (fun _ _ ⟨s₁, s₂, h, ea, eb⟩ => ⟨s₁, s₂, h, ea, eb⟩) fun _ _ h => h

end VG.Proof.Ecdsa.Rfc6979.Arm

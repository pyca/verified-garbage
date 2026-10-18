module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Correct
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Correct
public import VerifiedGarbage.Proof.HashFns.X86_64.Calls
meta import VerifiedGarbage.Proof.HashFns.X86_64.Calls
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
meta import VerifiedGarbage.Proof.Framework.X86_64.TaintErase
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Reduce
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Reduce

/-!
# Deterministic ECDSA on x86-64: constant time, up to the number of candidates

Two runs whose public data agree have the same layout, and stop at the same
candidate (`exitAt`, from the contract's leakage: the number of candidates
RFC 6979 tries). Between the frame's push and pop they are related by `Two`:
both satisfy `Ctx` with that layout (and `Φ`, what the next piece needs). The
blocks address only the stack and the buffers, from registers that agree
(the taint analysis, of the blocks for each size of hash function and of
the scalars, and a block that differs from one checked only in its
immediates and displacements by `taintOk_erase`); each call of `core` is of
constant-time code whose public data agree (`RelCT.callEx`), and each call of
a streaming function through `r11` is of the same address with arguments that
agree, from entries like the same anchor (`icallI_ct`, `icallU_ct`,
`icallF_ct`); and the loop's branch agrees, since in both runs it goes on
after candidate `i` iff `i` is before the candidate it stops at (`go_iff`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Impl.Mgf1.X86_64 (initF updF finF ldFn)
open VG.Proof.HashFns.X86_64 (UArgs FArgs)

/-- What each of two runs has, between the frame's push and pop. -/
abbrev Env (P : RfcHash) := Lay P.I.hashLen × (Reg → BitVec 64) × (Reg → BitVec 64) × Mem × Mem

/-- Two runs with the layout `e.1` that stop at the same candidate, each
satisfying `Ctx` and `Φ`. -/
abbrev TwoAt (P : RfcHash) (Φ : Lay P.I.hashLen → Mem → State → Prop) (e : Env P) (a b : State) : Prop :=
  e.1.Ok ∧ CoreOk P e.1 ∧ exitAt P e.1 e.2.2.2.1 = exitAt P e.1 e.2.2.2.2 ∧ Ctx e.1 e.2.1 e.2.2.2.1 a ∧
    Ctx e.1 e.2.2.1 e.2.2.2.2 b ∧ Φ e.1 e.2.2.2.1 a ∧ Φ e.1 e.2.2.2.2 b

/-- Two runs with the same layout that stop at the same candidate, each
satisfying `Ctx` and `Φ`. -/
def Two (P : RfcHash) (Φ : Lay P.I.hashLen → Mem → State → Prop) (a b : State) : Prop :=
  ∃ e : Env P, TwoAt P Φ e a b

variable {P : RfcHash}

theorem Two.mono {Φ Ψ : Lay P.I.hashLen → Mem → State → Prop} (h : ∀ L m₀ t, Φ L m₀ t → Ψ L m₀ t) {a b : State}
    (ht : Two P Φ a b) : Two P Ψ a b :=
  let ⟨e, hL, hq, hx, c₁, c₂, f₁, f₂⟩ := ht
  ⟨e, hL, hq, hx, c₁, c₂, h _ _ _ f₁, h _ _ _ f₂⟩

/-- Code whose runs leak the same, and which keeps `Ctx` and establishes `Ψ`. -/
theorem two_wp {c : Prog isa} {Φ Ψ : Lay P.I.hashLen → Mem → State → Prop}
    (hct : RelCT isa (Two P Φ) c fun _ _ => True)
    (hw : ∀ (L : Lay P.I.hashLen) g m₀ (t : State), L.Ok → CoreOk P L → Ctx L g m₀ t → Φ L m₀ t →
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

theorem rsp_two {dn : Nat} {L : Lay dn} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 64} {m₁ m₂ : Mem}
    (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) : t₁.gpr .rsp = t₂.gpr .rsp :=
  c₁.rsp.trans c₂.rsp.symm

/-- A block whose addresses depend only on the registers `rs`, which agree. -/
theorem two_blk {is : List Instr} {Φ : Lay P.I.hashLen → Mem → State → Prop} (rs : List Reg)
    (hrs : ∀ (L : Lay P.I.hashLen) (t₁ t₂ : State) g₁ g₂ m₁ m₂, Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ → Φ L m₁ t₁ →
      Φ L m₂ t₂ → ∀ r ∈ rs, t₁.gpr r = t₂.gpr r)
    (h : ∃ hc, (taint.check (Taint.ofRegs rs) (.block is) hc).isSome = true) :
    RelCT isa (Two P Φ) (.block is) fun _ _ => True :=
  let ⟨_, h⟩ := h
  RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun _ _ ⟨_, _, _, _, c₁, c₂, f₁, f₂⟩ => Taint.agree_ofRegs (hrs _ _ _ _ _ _ _ c₁ c₂ f₁ f₂)) h

theorem rspOnly {Φ : Lay P.I.hashLen → Mem → State → Prop} : ∀ (L : Lay P.I.hashLen) (t₁ t₂ : State) g₁ g₂ m₁ m₂,
    Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ → Φ L m₁ t₁ → Φ L m₂ t₂ → ∀ r ∈ [Reg.rsp], t₁.gpr r = t₂.gpr r := by
  intro L t₁ t₂ _ _ _ _ c₁ c₂ _ _ r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact rsp_two c₁ c₂


/-! ## Blocks the taint analysis checks -/

/-- The taint check of a block whose addresses depend only on `rs`. -/
abbrev TaintOk (rs : List Reg) (is : List Instr) : Prop :=
  ∃ hc, (taint.check (Taint.ofRegs rs) (.block is) hc).isSome = true

/-- A block that differs from one the analysis checks only in its immediates
and displacements: the analysis does not read them (`taint_eraseInv`). -/
theorem taintOk_erase {rs : List Reg} {is js : List Instr} (h : TaintOk rs js)
    (he : KList.map Instr.erase is = KList.map Instr.erase js) : TaintOk rs is := by
  obtain ⟨hc, hs⟩ := h
  refine ⟨hc, ?_⟩
  have e := (taint_eraseInv.check (.block is) (Taint.ofRegs rs) hc rfl).1
  have e₀ := (taint_eraseInv.check (.block js) (Taint.ofRegs rs) hc rfl).1
  rw [← e, show Code.mapBlocks Instr.erase (.block is) = Code.mapBlocks Instr.erase (.block js) from
    congrArg Code.block he, e₀]
  exact hs

theorem scr_blk (d : Reg) (a : Nat) (hd : d ≠ .rsp) : TaintOk [.rsp] (Cfg.scr d a) := by
  cases d <;> first | exact absurd rfl hd | exact taintOk_erase (js := Cfg.scr _ 0) ⟨_, by taint_decide⟩ rfl

theorem ldFn_blk (o : Nat) : TaintOk [.rsp] (ldFn o) := taintOk_erase (js := ldFn 0) ⟨_, by taint_decide⟩ rfl

theorem updArgs_scr_blk (st cnt a len : Nat) : TaintOk [.rsp] (Cfg.updArgs st cnt (Cfg.scr .rdx a) len) :=
  taintOk_erase (js := Cfg.updArgs 0 0 (Cfg.scr .rdx 0) 0) ⟨_, by taint_decide⟩ rfl

theorem updArgs_fr_blk (st cnt o len : Nat) : TaintOk [.rsp] (Cfg.updArgs st cnt (Cfg.fr .rdx o) len) :=
  taintOk_erase (js := Cfg.updArgs 0 0 (Cfg.fr .rdx 0) 0) ⟨_, by taint_decide⟩ rfl

theorem finArgs_scr_blk (st cnt a : Nat) : TaintOk [.rsp] (Cfg.finArgs st cnt (Cfg.scr .rdx a)) :=
  taintOk_erase (js := Cfg.finArgs 0 0 (Cfg.scr .rdx 0)) ⟨_, by taint_decide⟩ rfl

theorem finArgs_fr_blk (st cnt o : Nat) : TaintOk [.rsp] (Cfg.finArgs st cnt (Cfg.fr .rdx o)) :=
  taintOk_erase (js := Cfg.finArgs 0 0 (Cfg.fr .rdx 0)) ⟨_, by taint_decide⟩ rfl

theorem scrPtr_blk : TaintOk [.rsp] Cfg.scrPtr := ⟨_, by taint_decide⟩

/-! ## The calls of the streaming functions -/

theorem Like.two {E e₁ e₂ : State} (h₁ : Like E e₁) (h₂ : Like E e₂) :
    abi.sameWorld e₂ e₁ ∧ e₂.rd = e₁.rd ∧ e₂.wr = e₁.wr ∧ e₂.gpr .rsp = e₁.gpr .rsp := by
  obtain ⟨⟨a₁, b₁, c₁⟩, r₁, w₁, s₁⟩ := h₁
  obtain ⟨⟨a₂, b₂, c₂⟩, r₂, w₂, s₂⟩ := h₂
  simp only [abi, Option.elim] at c₁ c₂
  exact ⟨⟨a₂.trans a₁.symm, b₂.trans b₁.symm, by simp only [abi, Option.elim]; exact c₂.trans c₁.symm⟩,
    r₂.trans r₁.symm, w₂.trans w₁.symm, s₂.trans s₁.symm⟩

/-- The entries two states of the same layout keep `World` of: like the
same anchor, in each of which the streaming functions meet their contracts. -/
theorem calls_two {dn : Nat} {L : Lay dn} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 64} {m₁ m₂ : Mem}
    (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) :
    ∃ e₁ e₂, World 408 e₁ t₁ ∧ World 408 e₂ t₂ ∧ FnsK L.cs e₁ L.T L.fi L.fu L.ff ∧ FnsK L.cs e₂ L.T L.fi L.fu L.ff ∧
      e₁.wr = [L.OUT, L.SCR] ∧ e₁.gpr .rsp = L.B + BitVec.ofNat 64 408 ∧ e₂.wr = [L.OUT, L.SCR] ∧
      e₂.gpr .rsp = L.B + BitVec.ofNat 64 408 ∧ abi.sameWorld e₂ e₁ ∧ e₂.rd = e₁.rd ∧ e₂.wr = e₁.wr ∧
      e₂.gpr .rsp = e₁.gpr .rsp := by
  obtain ⟨e₁, W₁, F₁, l₁, w₁, s₁⟩ := c₁.calls
  obtain ⟨e₂, W₂, F₂, l₂, w₂, s₂⟩ := c₂.calls
  obtain ⟨sw, rd, wr, sp⟩ := l₁.two l₂
  exact ⟨e₁, e₂, W₁, W₂, F₁, F₂, w₁, s₁, w₂, s₂, sw, rd, wr, sp⟩

/-- The argument of `init` on the state at `scratch + st`, and its address in `r11`. -/
def IArg (st : Nat) (L : Lay P.I.hashLen) (_ : Mem) (u : State) : Prop :=
  u.gpr .rdi = L.scr + BitVec.ofNat 64 st ∧ u.gpr .r11 = L.fi

/-- The arguments of `update` of the state at `scratch + st`, after `cnt` bytes, with the `len` bytes at `dA L`. -/
def UArg (st cnt : Nat) (dA : Lay P.I.hashLen → Addr) (len : Nat) (L : Lay P.I.hashLen) (_ : Mem) (u : State) :
    Prop :=
  u.gpr .rdi = L.scr + BitVec.ofNat 64 st ∧ u.gpr .rsi = BitVec.ofNat 64 cnt ∧ u.gpr .rdx = dA L ∧
    u.gpr .rcx = BitVec.ofNat 64 len ∧ u.gpr .r8 = L.scr + BitVec.ofNat 64 sWork

/-- The arguments of `finalize` of the state at `scratch + st`, after `cnt` bytes, to `oA L`. -/
def FArg (st cnt : Nat) (oA : Lay P.I.hashLen → Addr) (L : Lay P.I.hashLen) (_ : Mem) (u : State) : Prop :=
  u.gpr .rdi = L.scr + BitVec.ofNat 64 st ∧ u.gpr .rsi = BitVec.ofNat 64 cnt ∧ u.gpr .rdx = oA L ∧
    u.gpr .rcx = L.scr + BitVec.ofNat 64 sWork

/-- `init` through `r11` in both runs. -/
theorem icallI_ct {st : Nat} (hst : st + 192 ≤ 384) : RelCT isa (Two P (IArg st)) (.icall 8) fun _ _ => True :=
  RelCT.exists_ (P := fun (e : Env P) a b => TwoAt P (IArg st) e a b) fun e =>
    VG.Proof.HashFns.X86_64.C.init_irel P.T (cs₀ := e.1.cs) (stack := 408) (st := e.1.scr + BitVec.ofNat 64 st) fun t₁ t₂ ⟨hL, hk, _, c₁, c₂, f₁, f₂⟩ => by
      obtain ⟨e₁, e₂, W₁, W₂, F₁, F₂, w₁, s₁, w₂, s₂, sw, rd, wr, sp⟩ := calls_two c₁ c₂
      have hT : e.1.T = P.T := hk.2.2.2.2
      have hz := P.sizes
      refine ⟨e₁, e₂, ⟨?_, ?_, F₁.consts, F₂.consts, W₁, W₂, sw, rd, wr, sp, f₂.2.trans f₁.2.symm, rsp_two c₂ c₁⟩,
        c₁.iPass w₁ s₁ hst, c₂.iPass w₂ s₂ hst, f₁.1, f₂.1, scr_bound hL (by omega), c₁.sp16 hL,
        c₁.stk hL (by omega)⟩
      · rw [f₁.2]; exact hT ▸ F₁.init
      · rw [f₂.2]; exact hT ▸ F₂.init

/-- `update` through `r11` in both runs. -/
theorem icallU_ct {st cnt len : Nat} {dA : Lay P.I.hashLen → Addr} (hst : st + 192 ≤ 384)
    (hd : ∀ L : Lay P.I.hashLen, L.Ok → UpdOk L (dA L) len) (hlen : len < 2 ^ 32) :
    RelCT isa (Two P fun L m u => UArg st cnt dA len L m u ∧ u.gpr .r11 = L.fu) (.icall 8) fun _ _ => True :=
  RelCT.exists_ (P := fun (e : Env P) a b => TwoAt P (fun L m u => UArg st cnt dA len L m u ∧ u.gpr .r11 = L.fu)
    e a b) fun e =>
    VG.Proof.HashFns.X86_64.C.upd_irel P.T (cs₀ := e.1.cs) (stack := 408) (st := e.1.scr + BitVec.ofNat 64 st) (d := dA e.1)
      (sc := e.1.scr + BitVec.ofNat 64 sWork) (len := len) fun t₁ t₂ ⟨hL, hk, _, c₁, c₂, f₁, f₂⟩ => by
      obtain ⟨e₁, e₂, W₁, W₂, F₁, F₂, w₁, s₁, w₂, s₂, sw, rd, wr, sp⟩ := calls_two c₁ c₂
      have hT : e.1.T = P.T := hk.2.2.2.2
      obtain ⟨⟨a₁, b₁, x₁, y₁, z₁⟩, r₁⟩ := f₁
      obtain ⟨⟨a₂, b₂, x₂, y₂, z₂⟩, r₂⟩ := f₂
      refine ⟨e₁, e₂, ⟨?_, ?_, F₁.consts, F₂.consts, W₁, W₂, sw, rd, wr, sp, r₂.trans r₁.symm, rsp_two c₂ c₁⟩,
        c₁.uPass w₁ s₁ hst (hd _ hL), c₂.uPass w₂ s₂ hst (hd _ hL), c₁.uArgs hL hst (hd _ hL) a₁ x₁ y₁ hlen z₁,
        c₂.uArgs hL hst (hd _ hL) a₂ x₂ y₂ hlen z₂, b₁.trans b₂.symm⟩
      · rw [r₁]; exact hT ▸ F₁.upd
      · rw [r₂]; exact hT ▸ F₂.upd

/-- `finalize` through `r11` in both runs. -/
theorem icallF_ct {st cnt : Nat} {oA : Lay P.I.hashLen → Addr} (hst : st + 192 ≤ 384)
    (ho : ∀ L : Lay P.I.hashLen, OutOk L (oA L)) :
    RelCT isa (Two P fun L m u => FArg st cnt oA L m u ∧ u.gpr .r11 = L.ff) (.icall 8) fun _ _ => True :=
  RelCT.exists_ (P := fun (e : Env P) a b => TwoAt P (fun L m u => FArg st cnt oA L m u ∧ u.gpr .r11 = L.ff)
    e a b) fun e =>
    VG.Proof.HashFns.X86_64.C.fin_irel P.T (cs₀ := e.1.cs) (stack := 408) (st := e.1.scr + BitVec.ofNat 64 st) (o := oA e.1)
      (sc := e.1.scr + BitVec.ofNat 64 sWork) fun t₁ t₂ ⟨hL, hk, _, c₁, c₂, f₁, f₂⟩ => by
      obtain ⟨e₁, e₂, W₁, W₂, F₁, F₂, w₁, s₁, w₂, s₂, sw, rd, wr, sp⟩ := calls_two c₁ c₂
      have hT : e.1.T = P.T := hk.2.2.2.2
      obtain ⟨⟨a₁, b₁, x₁, y₁⟩, r₁⟩ := f₁
      obtain ⟨⟨a₂, b₂, x₂, y₂⟩, r₂⟩ := f₂
      refine ⟨e₁, e₂, ⟨?_, ?_, F₁.consts, F₂.consts, W₁, W₂, sw, rd, wr, sp, r₂.trans r₁.symm, rsp_two c₂ c₁⟩,
        c₁.fPass w₁ s₁ hst (ho _), c₂.fPass w₂ s₂ hst (ho _), c₁.fArgs hL hst (ho _) a₁ x₁ y₁,
        c₂.fArgs hL hst (ho _) a₂ x₂ y₂, b₁.trans b₂.symm⟩
      · rw [r₁]; exact hT ▸ F₁.fin
      · rw [r₂]; exact hT ▸ F₂.fin

variable {L : Lay P.I.hashLen} {g : Reg → BitVec 64} {m₀ : Mem}

/-- `init` of the state at `scratch + st`, its address loaded from its slot. -/
theorem initF_ct {Φ : Lay P.I.hashLen → Mem → State → Prop} {st : Nat} (hst : st + 192 ≤ 384)
    (hΦ : ∀ L m u, Φ L m u → u.gpr .rdi = L.scr + BitVec.ofNat 64 st) :
    RelCT isa (Two P Φ) (initF fFn) fun _ _ => True :=
  (two_wp (Ψ := IArg st) (two_blk [.rsp] rspOnly (ldFn_blk _)) fun _ _ _ _ hL _ hc hφ =>
    WP.mono (ldFn_ok hL hc (o := fFn) (by decide)) fun _ h =>
      ⟨h.ctx, (h.keep .rdi (by decide)).trans (hΦ _ _ _ hφ), by rw [h.val, ← hc.pFi]; rfl⟩).seq (icallI_ct hst)

/-- `update`, its address loaded from its slot. -/
theorem updF_ct {Φ : Lay P.I.hashLen → Mem → State → Prop} {st cnt len : Nat} {dA : Lay P.I.hashLen → Addr}
    (hst : st + 192 ≤ 384) (hd : ∀ L : Lay P.I.hashLen, L.Ok → UpdOk L (dA L) len) (hlen : len < 2 ^ 32)
    (hΦ : ∀ L m u, Φ L m u → UArg st cnt dA len L m u) :
    RelCT isa (Two P Φ) (updF fFn) fun _ _ => True :=
  (two_wp (Ψ := fun L m u => UArg st cnt dA len L m u ∧ u.gpr .r11 = L.fu) (two_blk [.rsp] rspOnly (ldFn_blk _))
    fun _ _ _ _ hL _ hc hφ => WP.mono (ldFn_ok hL hc (o := fFn + 8) (by decide)) fun _ h => by
      obtain ⟨a, b, x, y, z⟩ := hΦ _ _ _ hφ
      exact ⟨h.ctx, ⟨(h.keep _ (by decide)).trans a, (h.keep _ (by decide)).trans b, (h.keep _ (by decide)).trans x,
        (h.keep _ (by decide)).trans y, (h.keep _ (by decide)).trans z⟩, by rw [h.val, ← hc.pFu]; rfl⟩).seq
    (icallU_ct hst hd hlen)

/-- `finalize`, its address loaded from its slot. -/
theorem finF_ct {Φ : Lay P.I.hashLen → Mem → State → Prop} {st cnt : Nat} {oA : Lay P.I.hashLen → Addr}
    (hst : st + 192 ≤ 384) (ho : ∀ L : Lay P.I.hashLen, OutOk L (oA L))
    (hΦ : ∀ L m u, Φ L m u → FArg st cnt oA L m u) :
    RelCT isa (Two P Φ) (finF fFn) fun _ _ => True :=
  (two_wp (Ψ := fun L m u => FArg st cnt oA L m u ∧ u.gpr .r11 = L.ff) (two_blk [.rsp] rspOnly (ldFn_blk _))
    fun _ _ _ _ hL _ hc hφ => WP.mono (ldFn_ok hL hc (o := fFn + 16) (by decide)) fun _ h => by
      obtain ⟨a, b, x, y⟩ := hΦ _ _ _ hφ
      exact ⟨h.ctx, ⟨(h.keep _ (by decide)).trans a, (h.keep _ (by decide)).trans b, (h.keep _ (by decide)).trans x,
        (h.keep _ (by decide)).trans y⟩, by rw [h.val, ← hc.pFf]; rfl⟩).seq
    (icallF_ct hst ho)

/-! ## The blocks that depend on the sizes -/

/-- The scalars' bytes and words, `n`'s bits and `sh`, for each curve. -/
theorem curve_cases (P : RfcHash) :
    (P.Q = 24 ∧ P.w = 4 ∧ P.R.sh = 0 ∧ Spec.Ecdsa.nBits P.R.E.C = 192) ∨
    (P.Q = 28 ∧ P.w = 4 ∧ P.R.sh = 0 ∧ Spec.Ecdsa.nBits P.R.E.C = 224) ∨
    (P.Q = 32 ∧ P.w = 4 ∧ P.R.sh = 0 ∧ Spec.Ecdsa.nBits P.R.E.C = 256) ∨
    (P.Q = 48 ∧ P.w = 6 ∧ P.R.sh = 0 ∧ Spec.Ecdsa.nBits P.R.E.C = 384) ∨
    (P.Q = 64 ∧ P.w = 8 ∧ P.R.sh = 0 ∧ Spec.Ecdsa.nBits P.R.E.C = 512) ∨
    (P.Q = 66 ∧ P.w = 9 ∧ P.R.sh = 7 ∧ Spec.Ecdsa.nBits P.R.E.C = 521) := by
  have hl := P.R.nBits_len
  simp only [RfcHash.Q, RfcHash.w]
  cases hb : P.R.big
  · obtain ⟨hn, hq, hN, -⟩ := P.R.sizesA hb
    have hs : P.R.sh = 0 := by omega
    rcases hq with hq | ⟨h4, hq | hq⟩
    · rcases hn with h | h | h
      · exact .inr (.inr (.inl ⟨by omega, h, hs, by omega⟩))
      · exact .inr (.inr (.inr (.inl ⟨by omega, h, hs, by omega⟩)))
      · exact .inr (.inr (.inr (.inr (.inl ⟨by omega, h, hs, by omega⟩))))
    · exact .inr (.inl ⟨hq, h4, hs, by omega⟩)
    · exact .inl ⟨hq, h4, hs, by omega⟩
  · obtain ⟨hn, hq, hN⟩ := P.R.sizesW hb
    exact .inr (.inr (.inr (.inr (.inr ⟨hq, hn, by omega, hN⟩))))

theorem D_cases (P : RfcHash) : P.D = 20 ∨ P.D = 28 ∨ P.D = 32 ∨ P.D = 48 ∨ P.D = 64 := by
  rcases P.hDB.2.2.2.2 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega

/-- The block `K ⊕ pad`, then `update`'s arguments. -/
theorem keyed_blk (P : RfcHash) (st : Nat) (pad : BitVec 32) :
    TaintOk [.rsp, .rdi] (Cfg.padBlock P.D P.B pad ++ Cfg.updArgs st 0 (Cfg.scr .rdx sPad) P.B) := by
  rcases P.hDB.2.2.2.2 with ⟨hD, hB⟩ | ⟨hD, hB⟩ | ⟨hD, hB⟩ | ⟨hD, hB⟩ | ⟨hD, hB⟩ | ⟨hD, hB⟩ | ⟨hD, hB⟩ <;>
    rw [hD, hB]
  · exact taintOk_erase (js := Cfg.padBlock 20 64 0 ++ Cfg.updArgs 0 0 (Cfg.scr .rdx 0) 64) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.padBlock 28 64 0 ++ Cfg.updArgs 0 0 (Cfg.scr .rdx 0) 64) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.padBlock 32 64 0 ++ Cfg.updArgs 0 0 (Cfg.scr .rdx 0) 64) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.padBlock 48 128 0 ++ Cfg.updArgs 0 0 (Cfg.scr .rdx 0) 128) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.padBlock 64 128 0 ++ Cfg.updArgs 0 0 (Cfg.scr .rdx 0) 128) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.padBlock 28 128 0 ++ Cfg.updArgs 0 0 (Cfg.scr .rdx 0) 128) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.padBlock 32 128 0 ++ Cfg.updArgs 0 0 (Cfg.scr .rdx 0) 128) ⟨_, by taint_decide⟩ rfl

/-- The registers the message's block addresses memory from. -/
abbrev msgRegs (wide : Bool) : List Reg := [.rsp, .rdi, .rsi] ++ (if wide then [.rdx] else [])

/-- The message `V ‖ b ‖ d ‖ h`. -/
theorem msgF_blk (P : RfcHash) (b ho : Nat) :
    TaintOk (msgRegs P.wide) (Cfg.msg P.Q P.D b true P.wide ho) := by
  rw [show P.wide = decide (P.D < P.Q) from rfl]
  rcases curve_cases P with ⟨hQ, -⟩ | ⟨hQ, -⟩ | ⟨hQ, -⟩ | ⟨hQ, -⟩ | ⟨hQ, -⟩ | ⟨hQ, -⟩ <;>
    rcases D_cases P with hD | hD | hD | hD | hD <;> rw [hQ, hD]
  · exact taintOk_erase (js := Cfg.msg 24 20 0 true (decide (20 < 24)) 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.msg 24 28 0 true (decide (28 < 24)) 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.msg 24 32 0 true (decide (32 < 24)) 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.msg 24 48 0 true (decide (48 < 24)) 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.msg 24 64 0 true (decide (64 < 24)) 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.msg 28 20 0 true (decide (20 < 28)) 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.msg 28 28 0 true (decide (28 < 28)) 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.msg 28 32 0 true (decide (32 < 28)) 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.msg 28 48 0 true (decide (48 < 28)) 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.msg 28 64 0 true (decide (64 < 28)) 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.msg 32 20 0 true (decide (20 < 32)) 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.msg 32 28 0 true (decide (28 < 32)) 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.msg 32 32 0 true (decide (32 < 32)) 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.msg 32 48 0 true (decide (48 < 32)) 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.msg 32 64 0 true (decide (64 < 32)) 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.msg 48 20 0 true (decide (20 < 48)) 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.msg 48 28 0 true (decide (28 < 48)) 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.msg 48 32 0 true (decide (32 < 48)) 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.msg 48 48 0 true (decide (48 < 48)) 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.msg 48 64 0 true (decide (64 < 48)) 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.msg 64 20 0 true (decide (20 < 64)) 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.msg 64 28 0 true (decide (28 < 64)) 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.msg 64 32 0 true (decide (32 < 64)) 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.msg 64 48 0 true (decide (48 < 64)) 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.msg 64 64 0 true (decide (64 < 64)) 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.msg 66 20 0 true (decide (20 < 66)) 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.msg 66 28 0 true (decide (28 < 66)) 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.msg 66 32 0 true (decide (32 < 66)) 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.msg 66 48 0 true (decide (48 < 66)) 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.msg 66 64 0 true (decide (64 < 66)) 0) ⟨_, by taint_decide⟩ rfl

/-- The message `V ‖ 0x00`. -/
theorem msg₀_blk (P : RfcHash) : TaintOk [.rsp, .rdi, .rsi] (Cfg.msg P.Q P.D 0 false false) := by
  rcases D_cases P with hD | hD | hD | hD | hD <;> rw [hD]
  · exact taintOk_erase (js := Cfg.msg 0 20 0 false false 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.msg 0 28 0 false false 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.msg 0 32 0 false false 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.msg 0 48 0 false false 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.msg 0 64 0 false false 0) ⟨_, by taint_decide⟩ rfl

/-- The configuration of the digest for `core` and of the conversions: the
scalars' bytes and words, the hash function's output and `sh`. -/
def cfgW (len D sh w : Nat) : Cfg :=
  { D := D, B := 0, w := w, len := len, sh := sh, n := 0, tries := 0, coreN := "", coreC := .block [] }

theorem coreDigest_congr (c : Cfg) : c.coreDigest = (cfgW c.len c.D c.sh c.w).coreDigest := rfl

theorem conv_congr (c : Cfg) (o s : Nat) : c.conv o s = (cfgW c.len 0 0 c.w).conv o s := rfl

/-- The digest for `core`, then `V = 0x01…` and `K = 0x00…`. -/
theorem coreDigest_blk (hW : P.wide = true) :
    TaintOk [.rsp, .rsi, .rdi] ((cfgOf P).coreDigest ++ Cfg.initKV) := by
  rw [coreDigest_congr, cfgOf_len, cfgOf_D, cfgOf_sh, cfgOf_w]
  rw [show P.wide = decide (P.D < P.Q) from rfl] at hW
  rcases curve_cases P with ⟨hQ, hw, hs, -⟩ | ⟨hQ, hw, hs, -⟩ | ⟨hQ, hw, hs, -⟩ | ⟨hQ, hw, hs, -⟩ |
      ⟨hQ, hw, hs, -⟩ | ⟨hQ, hw, hs, -⟩ <;>
    rcases D_cases P with hD | hD | hD | hD | hD <;> rw [hQ, hD, hs, hw] <;> rw [hQ, hD] at hW
  · exact ⟨_, by taint_decide⟩
  · exact absurd hW (by decide)
  · exact absurd hW (by decide)
  · exact absurd hW (by decide)
  · exact absurd hW (by decide)
  · exact ⟨_, by taint_decide⟩
  · exact absurd hW (by decide)
  · exact absurd hW (by decide)
  · exact absurd hW (by decide)
  · exact absurd hW (by decide)
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
  · exact absurd hW (by decide)
  · exact absurd hW (by decide)
  · exact absurd hW (by decide)
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
  · exact absurd hW (by decide)
  · exact absurd hW (by decide)
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
  · exact absurd hW (by decide)
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩

/-- P-521's candidate shifted right. -/
theorem conv_blk (hbig : P.R.big = true) : TaintOk [.rsp, .rdi] ((cfgOf P).conv fKb P.R.sh) := by
  have hl := P.R.nBits_len
  obtain ⟨hn, hq, hN⟩ := P.R.sizesW hbig
  rw [conv_congr, cfgOf_len, cfgOf_w, show P.Q = 66 from hq, show P.w = 9 from hn, show P.R.sh = 7 by omega]
  exact ⟨_, by taint_decide⟩

/-- A copy within the frame of any length a candidate's `V`s take. -/
theorem copyRsp_blk {n : Nat} (hn : n = 8 ∨ n = 10 ∨ n = 12 ∨ n = 16 ∨ n = 18 ∨ n = 20 ∨ n = 28 ∨ n = 32 ∨ n = 48 ∨ n = 64) (a b : Nat) :
    TaintOk [.rsp] (Cfg.copyBytes n .rsp a .rsp b) := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact taintOk_erase (js := Cfg.copyBytes 8 .rsp 0 .rsp 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.copyBytes 10 .rsp 0 .rsp 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.copyBytes 12 .rsp 0 .rsp 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.copyBytes 16 .rsp 0 .rsp 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.copyBytes 18 .rsp 0 .rsp 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.copyBytes 20 .rsp 0 .rsp 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.copyBytes 28 .rsp 0 .rsp 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.copyBytes 32 .rsp 0 .rsp 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.copyBytes 48 .rsp 0 .rsp 0) ⟨_, by taint_decide⟩ rfl
  · exact taintOk_erase (js := Cfg.copyBytes 64 .rsp 0 .rsp 0) ⟨_, by taint_decide⟩ rfl

/-- The bytes of each `V` a candidate takes. -/
theorem chunk_cases (hW : P.wide = true) {i : Nat} : (cfgOf P).chunk i = 8 ∨ (cfgOf P).chunk i = 10 ∨ (cfgOf P).chunk i = 12 ∨ (cfgOf P).chunk i = 16 ∨ (cfgOf P).chunk i = 18 ∨ (cfgOf P).chunk i = 20 ∨ (cfgOf P).chunk i = 28 ∨ (cfgOf P).chunk i = 32 ∨ (cfgOf P).chunk i = 48 ∨ (cfgOf P).chunk i = 64 := by
  have hw : P.wide = decide (P.D < P.Q) := rfl
  rw [hw] at hW
  simp only [Cfg.chunk, cfgOf_blocks, cfgOf_D, cfgOf_len, Nat.max_def]
  rcases curve_cases P with ⟨hQ, -, -, hN⟩ | ⟨hQ, -, -, hN⟩ | ⟨hQ, -, -, hN⟩ | ⟨hQ, -, -, hN⟩ |
      ⟨hQ, -, -, hN⟩ | ⟨hQ, -, -, hN⟩ <;>
    rcases D_cases P with hD | hD | hD | hD | hD <;> simp only [hQ, hD, hN] <;> rw [hQ, hD] at hW <;>
    first | exact absurd hW (by decide) | (split <;> (try split) <;> omega)

/-! ## One HMAC -/

/-- Registers that agree in two runs: `rsp`, and those `Φ` gives a value of the layout. -/
theorem agree_of {Φ : Lay P.I.hashLen → Mem → State → Prop} {rs : List Reg}
    (h : ∀ r ∈ rs, r = .rsp ∨ ∃ f : Lay P.I.hashLen → BitVec 64, ∀ L m u, Φ L m u → u.gpr r = f L) :
    ∀ (L : Lay P.I.hashLen) (t₁ t₂ : State) g₁ g₂ m₁ m₂, Ctx L g₁ m₁ t₁ → Ctx L g₂ m₂ t₂ → Φ L m₁ t₁ →
      Φ L m₂ t₂ → ∀ r ∈ rs, t₁.gpr r = t₂.gpr r := by
  intro L t₁ t₂ _ _ _ _ c₁ c₂ f₁ f₂ r hr
  rcases h r hr with rfl | ⟨f, hf⟩
  · exact rsp_two c₁ c₂
  · rw [hf _ _ _ f₁, hf _ _ _ f₂]

/-- The state at `scratch + st` set to `init`, then `update` with `K ⊕ pad`. -/
theorem keyed_ct {Φ : Lay P.I.hashLen → Mem → State → Prop} {st : Nat} (hst : st + 192 ≤ 384) {pad : BitVec 32}
    {c : Byte} (hp : pad = c ++ c ++ c ++ c) : RelCT isa (Two P Φ) ((cfgOf P).keyed st pad) fun _ _ => True := by
  have hz := P.sizes
  have hsp : sPad = 1792 := rfl
  rw [Cfg.keyed]
  refine (two_wp (Ψ := fun L _ u => u.gpr .rdi = L.scr + BitVec.ofNat 64 st)
    (two_blk [.rsp] rspOnly (scr_blk .rdi st (by decide))) fun _ _ _ _ hL _ hc _ =>
      WP.mono (scr_ok hL hc (d := .rdi) (by decide) (a := st) (by omega)) fun _ h => ⟨h.ctx, h.val⟩).seq ?_
  refine (two_wp (Ψ := fun _ _ _ => True) (initF_ct hst fun _ _ _ h => h) fun _ _ _ _ hL hk hc h =>
    WP.mono (init_ok hL hk.2.2.2.2 hc hst h) fun _ h => ⟨h.1, trivial⟩).seq ?_
  refine (two_wp (Ψ := fun L _ u => u.gpr .rdi = L.scr) (two_blk [.rsp] rspOnly scrPtr_blk) fun _ _ _ _ hL _ hc _ =>
    WP.mono (scrPtr_ok hL hc) fun _ h => ⟨h.1, h.2.2⟩).seq ?_
  refine (two_wp (Ψ := UArg st 0 (fun L => L.scr + BitVec.ofNat 64 sPad) P.B)
    (two_blk [.rsp, .rdi] (agree_of fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact .inl rfl
      · exact .inr ⟨fun L => L.scr, fun _ _ _ h => h⟩) (keyed_blk P st pad))
    fun _ _ _ _ hL _ hc hdi => ?_).seq
    (updF_ct hst (fun _ _ => .inr ⟨sPad, rfl, by decide, by omega⟩) (by omega) fun _ _ _ h => h)
  subst hp
  rw [WP.block_append_iff]
  refine WP.mono (padBlock_ok hL hc hdi (D := P.D) (B := P.B) (by omega) (by omega) (by omega) (by omega))
    fun u h => WP.mono (updArgs_ok hL h.1 (st := st) (cnt := 0) (by omega) (by decide)
      (fun u hcu => scr_ok hL hcu (d := .rdx) (by decide) (a := sPad) (by decide)) (len := P.B) (by omega))
    fun _ h' => ⟨h'.1, h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2.1, h'.2.2.2.2.2.1, h'.2.2.2.2.2.2⟩

/-- `HMAC_K(data)`: its blocks address only the frame and `scratch`, from
`rsp` (and `scratch`), and its calls are of the same functions with
arguments that agree. -/
theorem hmac_ct {Φ : Lay P.I.hashLen → Mem → State → Prop} {dataA : List Instr} {dA : Lay P.I.hashLen → Addr}
    {len dst : Nat}
    (hdA : ∀ (L : Lay P.I.hashLen) g m₀ u, L.Ok → Ctx L g m₀ u → WP isa (.block dataA) u (Upd L g m₀ u .rdx (dA L)))
    (hd : ∀ L : Lay P.I.hashLen, L.Ok → DataOk L (dA L) len) (hlen : len ≤ 256) (hdst : dst + 64 ≤ 128)
    (t₂ : ∀ st cnt, TaintOk [.rsp] (Cfg.updArgs st cnt dataA len)) :
    RelCT isa (Two P Φ) ((cfgOf P).hmac dataA len dst) fun _ _ => True := by
  have hz := P.sizes
  have hst : sTmp = 1920 := rfl
  rw [Cfg.hmac]
  refine (two_wp (Ψ := fun _ _ _ => True) (keyed_ct (st := sInner) (by decide) ipadW_eq) fun _ _ _ _ hL hk hc _ =>
    WP.mono (keyed_ok hL hk.2.2.2.2 hc (st := sInner) (by decide) ipadW_eq) fun _ h => ⟨h.1, trivial⟩).seq ?_
  refine (two_wp (Ψ := fun _ _ _ => True) (keyed_ct (st := sOuter) (by decide) opadW_eq) fun _ _ _ _ hL hk hc _ =>
    WP.mono (keyed_ok hL hk.2.2.2.2 hc (st := sOuter) (by decide) opadW_eq) fun _ h => ⟨h.1, trivial⟩).seq ?_
  -- The inner `update` with the data.
  refine (two_wp (Ψ := UArg sInner P.B dA len) (two_blk [.rsp] rspOnly (t₂ _ _)) fun L g m _ hL _ hc _ =>
    WP.mono (updArgs_ok hL hc (st := sInner) (cnt := P.B) (by decide) (by omega) (hdA L g m · hL) (len := len)
      (by omega)) fun _ h => ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩).seq ?_
  refine (two_wp (Ψ := fun _ _ _ => True) (updF_ct (by decide) (fun L hL => (hd L hL).upd) (by omega)
    fun _ _ _ h => h) fun _ _ _ _ hL hk hc h =>
      WP.mono (upd_ok hL hk.2.2.2.2 hc (by decide) (hd _ hL).upd h.1 h.2.2.1 h.2.2.2.1 (by omega) h.2.2.2.2)
        fun _ h => ⟨h.1, trivial⟩).seq ?_
  -- The inner `finalize`, to the inner hash.
  refine (two_wp (Ψ := FArg sInner (P.B + len) (fun L => L.scr + BitVec.ofNat 64 sTmp))
    (two_blk [.rsp] rspOnly (finArgs_scr_blk _ _ _)) fun _ _ _ _ hL _ hc _ =>
      WP.mono (finArgs_ok hL hc (st := sInner) (cnt := P.B + len) (by decide) (by omega)
        (fun u hu => scr_ok hL hu (d := .rdx) (by decide) (a := sTmp) (by decide)))
        fun _ h => ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩).seq ?_
  refine (two_wp (Ψ := fun _ _ _ => True) (finF_ct (by decide) (fun _ => .inr rfl) fun _ _ _ h => h)
    fun _ _ _ _ hL hk hc h => WP.mono (fin_ok hL hk.2.2.2.2 hc (by decide) (.inr rfl) h.1 h.2.2.1 h.2.2.2)
      fun _ h => ⟨h.1, trivial⟩).seq ?_
  -- The outer `update` with the inner hash.
  refine (two_wp (Ψ := UArg sOuter P.B (fun L => L.scr + BitVec.ofNat 64 sTmp) P.D)
    (two_blk [.rsp] rspOnly (updArgs_scr_blk _ _ _ _)) fun _ _ _ _ hL _ hc _ =>
      WP.mono (updArgs_ok hL hc (st := sOuter) (cnt := P.B) (by decide) (by omega)
        (fun u hu => scr_ok hL hu (d := .rdx) (by decide) (a := sTmp) (by decide)) (len := P.D) (by omega))
        fun _ h => ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩).seq ?_
  refine (two_wp (Ψ := fun _ _ _ => True) (updF_ct (by decide) (fun _ _ => .inr ⟨sTmp, rfl, by decide, by omega⟩)
    (by omega) fun _ _ _ h => h) fun _ _ _ _ hL hk hc h =>
      WP.mono (upd_ok hL hk.2.2.2.2 hc (by decide) (.inr ⟨sTmp, rfl, by decide, by omega⟩) h.1 h.2.2.1 h.2.2.2.1
        (by omega) h.2.2.2.2) fun _ h => ⟨h.1, trivial⟩).seq ?_
  -- The outer `finalize`, to `dst`.
  refine (two_wp (Ψ := FArg sOuter (P.B + P.D) (fun L => L.B + BitVec.ofNat 64 (24 + dst)))
    (two_blk [.rsp] rspOnly (finArgs_fr_blk _ _ _)) fun _ _ _ _ hL _ hc _ =>
      WP.mono (finArgs_ok hL hc (st := sOuter) (cnt := P.B + P.D) (by decide) (by omega)
        (fun u hu => fr_ok hL hu (d := .rdx) (by decide) (o := dst) (by omega)))
        fun _ h => ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩).seq ?_
  exact finF_ct (by decide) (fun _ => .inl ⟨dst, rfl, hdst⟩) fun _ _ _ h => h

/-- `V = HMAC_K(V)`. -/
theorem hmacV_ct {Φ : Lay P.I.hashLen → Mem → State → Prop} : RelCT isa (Two P Φ) (cfgOf P).hmacV fun _ _ => True :=
  hmac_ct (dA := fun L => L.B + BitVec.ofNat 64 (24 + 64)) (len := P.D) (dst := 64)
    (fun _ _ _ _ hL hu => fr_ok hL hu (d := .rdx) (by decide) (o := 64) (by decide))
    (fun _ _ => .inl ⟨88, rfl, by omega, by nums⟩) (by nums) (by decide) fun _ _ => updArgs_fr_blk _ _ _ _

/-- `K = HMAC_K(m)`, for the message of `len` bytes at `scratch + 2256`. -/
theorem hmacK_ct {Φ : Lay P.I.hashLen → Mem → State → Prop} {len : Nat} (hlen : len ≤ 256) :
    RelCT isa (Two P Φ) ((cfgOf P).hmac (Cfg.scr .rdx sMsg) len fK) fun _ _ => True :=
  hmac_ct (dA := fun L => L.scr + BitVec.ofNat 64 2256) (dst := 0)
    (fun _ _ _ _ hL hu => scr_ok hL hu (d := .rdx) (by decide) (a := 2256) (by decide))
    (fun _ _ => .inr ⟨2256, rfl, by omega, by omega⟩) hlen (by decide) fun _ _ => updArgs_scr_blk _ _ _ _

/-- `scratch` in `rdi`, `d` in `rsi`, and, if `wd`, `digest` in `rdx`. -/
def PtrsIn (wd : Bool) {dn : Nat} (L : Lay dn) (_ : Mem) (u : State) : Prop :=
  u.gpr .rdi = L.scr ∧ u.gpr .rsi = L.d ∧ (wd = true → u.gpr .rdx = L.dg)

theorem msgPtrs_blk (wd : Bool) : TaintOk [.rsp] (Cfg.msgPtrs wd) := by
  cases wd
  · exact ⟨_, by taint_decide⟩
  · exact ⟨_, by taint_decide⟩

/-- `K = HMAC_K(m)`, then `V = HMAC_K(V)`, for the message `m = V ‖ b (‖ d ‖ h)`. -/
theorem rekey_gen_ct {Φ : Lay P.I.hashLen → Mem → State → Prop} {b : Nat} {full wd : Bool}
    (hwd : full = true → wd = P.wide) {ho : Nat} (hho : full = true → ho = P.hB - 24) {len : Nat}
    (hlen : len = if full then P.D + 2 * P.Q + 1 else P.D + 1)
    (t₁ : TaintOk (msgRegs wd) (Cfg.msg P.Q P.D b full wd ho)) :
    RelCT isa (Two P Φ) (.seq (.block (Cfg.msgPtrs wd)) (.seq (.block (Cfg.msg P.Q P.D b full wd ho))
      (.seq ((cfgOf P).hmac (Cfg.scr .rdx sMsg) len fK) (cfgOf P).hmacV))) fun _ _ => True := by
  have hlen' : len ≤ 256 := by cases full <;> simp only [hlen, Bool.false_eq_true, ite_true, ite_false] <;> nums
  refine (two_wp (Ψ := PtrsIn wd) (two_blk [.rsp] rspOnly (msgPtrs_blk wd)) fun _ _ _ _ hL hk hc _ =>
    WP.mono (ptrs_ok hL hc wd) fun _ ⟨c, _, a⟩ => ⟨c, a⟩).seq ?_
  refine (two_wp (Ψ := fun _ _ _ => True) (two_blk (msgRegs wd) (fun L t₁ t₂ _ _ _ _ c₁ c₂ f₁ f₂ r hr => by
      cases wd
      · simp only [msgRegs, Bool.false_eq_true, ite_false, List.append_nil, List.mem_cons, List.not_mem_nil,
          or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact rsp_two c₁ c₂
        · exact f₁.1.trans f₂.1.symm
        · exact f₁.2.1.trans f₂.2.1.symm
      · simp only [msgRegs, ite_true, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact rsp_two c₁ c₂
        · exact f₁.1.trans f₂.1.symm
        · exact f₁.2.1.trans f₂.2.1.symm
        · exact (f₁.2.2 rfl).trans (f₂.2.2 rfl).symm) t₁) fun _ _ _ _ hL hk hc hp =>
    WP.mono (msg_ok hL hc hp.1 hp.2.1 b full wd ho hp.2.2 (D := P.D) (Q := P.Q) (by nums) (by nums) (by nums)
      (by nums) (by rw [hk.1])
      (fun hf hw => by
        have hA := (hw ▸ hwd hf).symm
        have := P.sizesA hA
        obtain ⟨-, -, hb₃, -, -, -⟩ := hb_facts hA hk.2.2.1
        have := hB_ge P
        rw [hho hf]; exact ⟨by omega, by omega⟩)
      (fun hf hw => by
        have hW := (hw ▸ hwd hf).symm
        have hz := P.sizes
        exact ⟨by simpa [RfcHash.wide] using hW, by omega, by rw [P.len]⟩))
      fun _ h => ⟨h.1, trivial⟩).seq ?_
  exact (two_wp (Ψ := fun _ _ _ => True) (hmacK_ct hlen') fun _ _ _ _ hL hq hc _ =>
    WP.mono (hmacK_ok (P := P) hL hq.2.2.2.2 hc hlen') fun _ h => ⟨h.1, trivial⟩).seq hmacV_ct

theorem rekeyFull_ct {Φ : Lay P.I.hashLen → Mem → State → Prop} (b : Nat) :
    RelCT isa (Two P Φ) ((cfgOf P).rekeyFull b) fun _ _ => True :=
  rekey_gen_ct (full := true) (fun _ => rfl) (ho := (cfgOf P).fHo) (fun _ => fHo_eq P)
    (len := P.D + 2 * P.Q + 1) rfl (msgF_blk P b _)

theorem rekey_ct {Φ : Lay P.I.hashLen → Mem → State → Prop} : RelCT isa (Two P Φ) (cfgOf P).rekey fun _ _ => True :=
  rekey_gen_ct (b := 0) (full := false) (wd := false) (fun h => absurd h (by decide)) (ho := fH)
    (fun h => absurd h (by decide)) (len := P.D + 1) rfl (msg₀_blk P)

/-! ## One candidate -/

/-- `scratch` in `rdi`. -/
def ScrIn {dn : Nat} (L : Lay dn) (_ : Mem) (u : State) : Prop := u.gpr .rdi = L.scr

/-- `V = HMAC_K(V)`, and its first bytes to the candidate's place. -/
theorem candStep_ct {Φ : Lay P.I.hashLen → Mem → State → Prop} (hW : P.wide = true) {i : Nat} :
    RelCT isa (Two P Φ) ((cfgOf P).candStep i) fun _ _ => True :=
  (two_wp (Ψ := fun _ _ _ => True) hmacV_ct fun _ _ _ _ hL hk hc _ =>
    WP.mono (hmacV_ok hL hk.2.2.2.2 hc) fun _ h => ⟨h.1, trivial⟩).seq
    (two_blk [.rsp] rspOnly (copyRsp_blk (chunk_cases hW (i := i)) _ _))

theorem candSteps_ct {Φ : Lay P.I.hashLen → Mem → State → Prop} (hW : P.wide = true) :
    ∀ k i, i + k = (cfgOf P).blocks → 0 < k →
      RelCT isa (Two P Φ) ((cfgOf P).candSteps i k) fun _ _ => True
  | 0, _, _, h => absurd h (Nat.lt_irrefl _)
  | 1, i, hik, _ => candStep_ct hW
  | k + 2, i, hik, _ => by
    show RelCT isa (Two P Φ) (.seq ((cfgOf P).candStep i) ((cfgOf P).candSteps (i + 1) (k + 1))) _
    exact (two_wp (Ψ := fun _ _ _ => True) (candStep_ct hW) fun _ _ _ _ hL hk hc _ =>
      WP.mono (candStep_ok hL hk.2.2.2.2 hW hc (by omega)) fun _ h => ⟨h.1, trivial⟩).seq
      (candSteps_ct hW (k + 1) (i + 1) (by omega) (by omega))

/-- The candidate: its calls and blocks leak the same in both runs. -/
theorem cand_ct {Φ : Lay P.I.hashLen → Mem → State → Prop} :
    RelCT isa (Two P Φ) (cfgOf P).cand fun _ _ => True := by
  cases hw : P.wide
  · have e : (cfgOf P).cand = (cfgOf P).hmacV := by rw [Cfg.cand, show (cfgOf P).wide = false from hw]; rfl
    rw [e]; exact hmacV_ct
  · have e : (cfgOf P).wide = true := hw
    have hb := (blocks_sizes hw).1
    rw [Cfg.cand]
    simp only [e, ite_true]
    by_cases h0 : (cfgOf P).sh = 0
    · simp only [h0, ite_true]
      exact candSteps_ct hw _ 0 (Nat.zero_add _) (by omega)
    · simp only [h0, ite_false]
      refine (two_wp (Ψ := fun _ _ _ => True) (candSteps_ct hw _ 0 (Nat.zero_add _) (by omega))
        fun _ _ _ _ hL hk hc _ => WP.mono (candSteps_ok hL hk.2.2.2.2 hw _ 0 (Nat.zero_add _) (by omega) _ hc)
          fun _ h => ⟨h.1, trivial⟩).seq ?_
      refine (two_wp (Ψ := ScrIn) (two_blk [.rsp] rspOnly scrPtr_blk) fun _ _ _ _ hL _ hc _ =>
        WP.mono (scrPtr_ok hL hc) fun _ h => ⟨h.1, h.2.2⟩).seq ?_
      exact two_blk [.rsp, .rdi] (agree_of fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact .inl rfl
        · exact .inr ⟨fun L => L.scr, fun _ _ _ h => h⟩) (conv_blk (big_of_sh h0))

theorem ce_rsp_two {dn : Nat} {L : Lay dn} {t₁ t₂ : State} {g₁ g₂ : Reg → BitVec 64} {m₁ m₂ : Mem}
    (c₁ : Ctx L g₁ m₁ t₁) (c₂ : Ctx L g₂ m₂ t₂) (rd₁ wr₁ rd₂ wr₂ : List Region) :
    (t₁.callEntry.withRegions rd₁ wr₁).gpr .rsp = (t₂.callEntry.withRegions rd₂ wr₂).gpr .rsp := by
  rw [State.withRegions_gpr, State.withRegions_gpr, State.callEntry_rsp, State.callEntry_rsp, rsp_two c₁ c₂]

theorem ce_two {t₁ t₂ : State} {r : Reg} (hr : r ≠ .rsp) {x : BitVec 64} (h₁ : t₁.gpr r = x) (h₂ : t₂.gpr r = x)
    (rd₁ wr₁ rd₂ wr₂ : List Region) :
    (t₁.callEntry.withRegions rd₁ wr₁).gpr r = (t₂.callEntry.withRegions rd₂ wr₂).gpr r := by
  rw [ce_gpr _ _ _ hr, ce_gpr _ _ _ hr, h₁, h₂]

/-- `core`, with arguments that agree. -/
theorem core_ct {i : Nat} :
    RelCT isa (Two P fun L m₀ u => P₁ P L m₀ i u ∧ Args P L u) (.call (cfgOf P).coreN (cfgOf P).coreC)
      fun _ _ => True :=
  RelCT.callEx (k := (coreK P.R.E).clear) (fun s h => P.R.coreX s h.1 h.2)
    (fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ => P.R.coreCT s₁ s₂ t₁ t₂ s₁' s₂' h₁.1 h₂.1)
    fun _ _ ⟨⟨L, _, _, _, _⟩, hL, hk, _, c₁, c₂, ⟨_, a₁⟩, ⟨_, a₂⟩⟩ =>
    ⟨coreRd P L, coreWr P L, coreRd P L, coreWr P L,
      ⟨core_pre hL hk c₁ a₁.rdi a₁.rsi a₁.rdx a₁.rcx a₁.r8, core_clear hL hk c₁⟩,
      ⟨core_pre hL hk c₂ a₂.rdi a₂.rsi a₂.rdx a₂.rcx a₂.r8, core_clear hL hk c₂⟩,
      ⟨ce_rsp_two c₁ c₂ _ _ _ _, ce_two (by decide) a₁.rdi a₂.rdi _ _ _ _, ce_two (by decide) a₁.rsi a₂.rsi _ _ _ _,
        ce_two (by decide) a₁.rdx a₂.rdx _ _ _ _, ce_two (by decide) a₁.rcx a₂.rcx _ _ _ _,
        ce_two (by decide) a₁.r8 a₂.r8 _ _ _ _, fun c hc => by
          have hc' : c ∈ L.cs := by rw [hk.2.2.2.1]; exact hc
          exact (c₁.sy c hc').trans (c₂.sy c hc').symm⟩,
      core_covers hk hL c₁, core_coversW hk.1 c₁, core_covers hk hL c₂, core_coversW hk.1 c₂, rsp_two c₁ c₂⟩

/-- Whether to go on agrees: in both runs, iff the candidate is before the one it stops at. -/
theorem dec_two {L : Lay P.I.hashLen} {m₁ m₂ : Mem} {i : Nat} (hx : exitAt P L m₁ = exitAt P L m₂) {u₁ u₂ : State}
    (h₁ : Mid P L m₁ i u₁) (h₂ : Mid P L m₂ i u₂) : isa.eval .ne u₁ = isa.eval .ne u₂ := by
  rw [h₁.dec, h₂.dec]
  refine congrArg some (decide_eq_decide.mpr ?_)
  rw [go_iff h₁.lt h₁.fails, go_iff h₂.lt h₂.fails, hx]

/-- What one candidate leaves: the end, or the next candidate. -/
def After (P : RfcHash) (i : Nat) (L : Lay P.I.hashLen) (m₀ : Mem) (t : State) : Prop :=
  (isa.eval .ne t = some false ∧ Exit P L m₀ i t) ∨ (isa.eval .ne t = some true ∧ LoopInv P L m₀ (i + 1) t)

theorem coreArgs_blk (P : RfcHash) : TaintOk [.rsp] (cfgOf P).coreArgs := by
  cases hw : P.wide
  · have e : (cfgOf P).wide = false := hw
    simp only [Cfg.coreArgs, e, Bool.false_eq_true, ite_false]; exact ⟨_, by taint_decide⟩
  · have e : (cfgOf P).wide = true := hw
    simp only [Cfg.coreArgs, e, ite_true]; exact ⟨_, by taint_decide⟩

theorem tryOne_trace {i : Nat} :
    RelCT isa (Two P fun L m₀ t => LoopInv P L m₀ i t) (cfgOf P).tryOne fun _ _ => True := by
  refine (two_wp (Ψ := fun L m₀ u => P₁ P L m₀ i u) cand_ct fun _ _ _ _ hL hk hc hi =>
    try₁_ok hL hk hc hi).seq ?_
  refine (two_wp (Ψ := fun L m₀ u => P₁ P L m₀ i u ∧ Args P L u) (two_blk [.rsp] rspOnly (coreArgs_blk P))
    fun _ _ _ _ hL hk hc hi => try₂_ok hL hc hi).seq ?_
  refine (two_wp (Ψ := fun L m₀ u => P₃ P L m₀ i u) core_ct fun _ _ _ _ hL hk hc hi =>
    try₃_ok hL hk hc hi.1 hi.2).seq ?_
  refine (two_wp (Ψ := fun L m₀ u => Mid P L m₀ i u) (two_blk [.rsp] rspOnly ⟨_, by taint_decide⟩)
    fun _ _ _ _ hL hk hc hi => try₄_ok hL hk hc hi).seq ?_
  refine VG.RelCT.ite (fun _ _ ⟨_, _, _, hx, _, _, f₁, f₂⟩ => dec_two hx f₁ f₂) ?_ ?_
  · exact ((two_wp (Ψ := fun _ _ _ => True) rekey_ct fun _ _ _ _ hL hk hc _ =>
      WP.mono (rekey_ok hL (hok_of hk) hc) fun _ h => ⟨h.1, trivial⟩).seq
      (two_blk [.rsp] rspOnly ⟨_, by taint_decide⟩)).mono (fun _ _ h => h.1) fun _ _ h => h
  · exact (two_blk [.rsp] rspOnly ⟨_, by taint_decide⟩).mono (fun _ _ h => h.1) fun _ _ h => h

/-- One candidate: both runs end, or both go on. -/
theorem tryOne_ct {i : Nat} :
    RelCT isa (Two P fun L m₀ t => LoopInv P L m₀ i t) (cfgOf P).tryOne fun s₁ s₂ =>
      isa.eval .ne s₁ = isa.eval .ne s₂ ∧ (isa.eval .ne s₁ = some false → Two P (Exit P · · i) s₁ s₂) ∧
        (isa.eval .ne s₁ = some true → Two P (LoopInv P · · (i + 1)) s₁ s₂) := by
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

theorem loop_ct :
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

/-- The count's initial store, for any count. -/
theorem initCnt_blk (c : Cfg) : TaintOk [.rsp] c.initCnt :=
  taintOk_erase (js := (cfgW 0 0 0 0).initCnt) ⟨_, by taint_decide⟩ rfl

theorem wipe_blk : TaintOk [.rsp] Cfg.wipe := ⟨_, by taint_decide⟩

theorem digestPtr_blk (P : RfcHash) : TaintOk [.rsp] (cfgOf P).digestPtr := by
  cases hw : P.wide
  · have e : (cfgOf P).wide = false := hw
    simp only [Cfg.digestPtr, e, Bool.false_eq_true, ite_false]; exact ⟨_, by taint_decide⟩
  · have e : (cfgOf P).wide = true := hw
    simp only [Cfg.digestPtr, e, ite_true]; exact ⟨_, by taint_decide⟩

/-- `digest` in `rsi`, and, if the hash is shorter than the scalars, `scratch` in `rdi`. -/
def DgIn (P : RfcHash) {dn : Nat} (L : Lay dn) (_ : Mem) (u : State) : Prop :=
  u.gpr .rsi = L.dg ∧ (P.wide = true → u.gpr .rdi = L.scr)

theorem prep_ct : RelCT isa (Two P (DgIn P))
    (.block ((if (cfgOf P).wide then (cfgOf P).coreDigest else (cfgOf P).reduce) ++ Cfg.initKV)) fun _ _ => True := by
  cases hw : P.wide
  · have e : (cfgOf P).wide = false := hw
    simp only [e, Bool.false_eq_true, ite_false]
    exact two_blk [.rsp, .rsi] (fun _ _ _ _ _ _ _ c₁ c₂ f₁ f₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact rsp_two c₁ c₂
      · exact f₁.1.trans f₂.1.symm) (P.R.reduceT (P.big_false hw))
  · have e : (cfgOf P).wide = true := hw
    simp only [e, ite_true]
    exact two_blk [.rsp, .rsi, .rdi] (fun _ _ _ _ _ _ _ c₁ c₂ f₁ f₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact rsp_two c₁ c₂
      · exact f₁.1.trans f₂.1.symm
      · exact (f₁.2 hw).trans (f₂.2 hw).symm) (coreDigest_blk hw)

theorem body_ct :
    RelCT isa (Two P fun _ _ _ => True) (cfgOf P).body (Two P fun L m₀ t => ∃ i, Exit P L m₀ i t) := by
  refine (two_wp (Ψ := DgIn P) (two_blk [.rsp] rspOnly (digestPtr_blk P)) fun _ _ _ _ hL hk hc _ =>
    WP.mono (digestPtr_ok hL hc) fun _ h => ⟨h.1, h.2.2.1, h.2.2.2⟩).seq ?_
  refine (two_wp (Ψ := QB P) prep_ct fun _ _ _ _ hL hk hc h => stageB_ok (P := P) hL hk hc h.1 h.2).seq ?_
  refine (two_wp (Ψ := QC P) (rekeyFull_ct 0) fun _ _ _ _ hL hk hc h => stageC_ok (P := P) hL hk hc h).seq ?_
  refine (two_wp (Ψ := QD P) (rekeyFull_ct 1) fun _ _ _ _ hL hk hc h => stageD_ok (P := P) hL hk hc h).seq ?_
  refine (two_wp (Ψ := fun L m₀ t => LoopInv P L m₀ 0 t) (two_blk [.rsp] rspOnly (initCnt_blk _))
    fun _ _ _ _ hL hk hc h => stageE_ok (P := P) hL hk hc h).seq ?_
  refine loop_ct.seq ?_
  exact two_wp (two_blk [.rsp] rspOnly wipe_blk) fun _ _ _ _ hL hk hc ⟨i, h⟩ =>
    WP.mono (stageG_ok hL hk hc h) fun _ ⟨c, x⟩ => ⟨c, i, x⟩

/-! ## The whole configuration -/

/-- Two entries of `sign`, in runs from entries like `E` (`BodyIn`), whose
public data agree, and with the same addresses of the streaming functions. -/
def BodyPair (P : RfcHash) (E : State) (X : List Region) (s₁ s₂ : State) : Prop :=
  (rfcX86_64 P.R.E.combConsts P.I 408 X).pre s₁ ∧ (rfcX86_64 P.R.E.combConsts P.I 408 X).pre s₂ ∧
    (rfcX86_64 P.R.E.combConsts P.I 408 X).pub s₁ s₂ ∧ BodyIn P.R.E.combConsts P.T E s₁ ∧ BodyIn P.R.E.combConsts P.T E s₂ ∧
    s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .r10 = s₂.gpr .r10 ∧ s₁.gpr .r11 = s₂.gpr .r11

/-- Runs whose public data agree have the same layout, and stop at the same candidate. -/
theorem sign_ct (E : State) (X : List Region) : RelCT isa (BodyPair P E X) (cfgOf P).sign fun _ _ => True := by
  rw [sign_eq]
  refine RelCT.frame (R := Two P fun L m₀ t => ∃ i, Exit P L m₀ i t) (fun _ _ h => h.2.2.1.1) ?_
  refine body_ct.mono (fun a b ⟨s₁, s₂, ⟨p₁, p₂, ⟨hsp, hdi, hsi, hdx, hcx, hres, hsy⟩, b₁, b₂, h9, h10, h11⟩,
    ea, eb⟩ => ?_) fun _ _ h => h
  subst ea eb
  have hsy' : (fun n => if n ∈ P.R.E.combConsts.map Prod.fst then s₁.syms n else 0) =
      fun n => if n ∈ P.R.E.combConsts.map Prod.fst then s₂.syms n else 0 := funext fun n => by
    split
    · next h => obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h; exact hsy c hc
    · rfl
  have hl : lay P.I.hashLen P.I.ecdsa.curve.len P.R.E.combConsts E P.T s₁ X =
      lay P.I.hashLen P.I.ecdsa.curve.len P.R.E.combConsts E P.T s₂ X := by
    unfold lay; rw [hsp, hdi, hsi, hdx, hcx, hsy', h9, h10, h11]
  have hr : (result P.I s₁.mem (s₁.gpr .rsi) (s₁.gpr .rdx)).2 = (result P.I s₂.mem (s₁.gpr .rsi) (s₁.gpr .rdx)).2 := by
    rw [hres, hsi, hdx]
  refine ⟨⟨lay P.I.hashLen P.I.ecdsa.curve.len P.R.E.combConsts E P.T s₁ X, s₁.gpr, s₂.gpr, s₁.mem, s₂.mem⟩,
    lay_ok p₁, coreOk_lay P E s₁ X, congrArg (fun x => if x = 0 then P.I.tries - 1 else x - 1) hr, push_ctx p₁ b₁,
    by rw [hl]; exact push_ctx p₂ b₂, trivial, trivial⟩

end VG.Proof.Ecdsa.Rfc6979.X86_64

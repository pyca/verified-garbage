module

public import VerifiedGarbage.Proof.RsaOaep.X86_64.Hash
public import VerifiedGarbage.Proof.Bignum.X86_64.Mont
import Mathlib.Tactic.Conv
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-!
# RSAES-OAEP on x86-64: relating two runs

The constant-time proofs relate two runs piece by piece (`RelCT`), each
point of the code described in both runs by the same predicate `Φ a` of
public data `a` (`Two`, `Proof/Bignum/X86_64/Mont.lean`), with what
correctness says of each run added after each piece (`two_post`).

The code keeps its public values (pointers, lengths, MGF1's counter) in its
frame's slots, so the taint analysis starts from `rsp`, the base of the
frame (the first writable region), and the slots the piece reads, public
(`frT`), in two runs whose frames and regions agree (`FrV`, `two_taintF`).
The indirect calls of the streaming hash functions, through the addresses
in the frame's slots, are constant time when the addresses and the
arguments agree, from entries of the same program with the same regions
(`Like`): `two_initF`, `two_updF`, `two_updExtF`, `two_finF`.
-/

@[expose] public section

namespace VG.Proof.RsaOaep.X86_64

open VG VG.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Proof.Bignum (off word)
open VG.Proof.Bignum.X86_64 (Two Pins two_post)
open VG.Proof.HashFns (StreamingOK)
open VG.Proof.HashFns.X86_64 (UArgs FArgs init_irel upd_irel fin_irel)
open VG.Impl.Mgf1.X86_64 (ldFn initF updF finF)
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-! ## The taint from the frame -/

/-- The registers `rs` and `rsp` public, `rsp` the base of the frame (the
first of `n + 1` writable regions), and the frame's words `ks` public. -/
def frT (rs : List Reg) (ks : List Nat) (n : Nat) : X86_64.Taint.T :=
  { regs := .ofList (rs ++ [.rsp]), flags := false, lens := frameBytes :: List.replicate n 0,
    bases := [(.rsp, 0, 0)],
    slots := ks.map fun k => (0, 8 * k, 8) }

/-- In the frame at `F`, with the writable regions `F`'s and the `n` of `ws`,
apart. -/
structure FrV (n : Nat) (F : Addr) (ws : List Region) (t : State) : Prop where
  rsp : t.gpr .rsp = F
  wr : t.wr = ⟨F, frameBytes⟩ :: ws
  two : ws.length = n
  pw : (⟨F, frameBytes⟩ :: ws : List Region).Pairwise Region.Disjoint
  len : ∀ r ∈ ws, r.len ≤ 2 ^ 64

theorem FrV.congr {n : Nat} {F : Addr} {ws : List Region} {t t' : State} (h : FrV n F ws t) (hsp : t'.gpr .rsp = t.gpr .rsp)
    (hwr : t'.wr = t.wr) : FrV n F ws t' :=
  ⟨hsp.trans h.rsp, hwr.trans h.wr, h.two, h.pw, h.len⟩

/-- Bytes of a word that both memories hold. -/
theorem word_byte {m₁ m₂ : Mem} {a : Addr} (h : m₁.readW a 64 = m₂.readW a 64) {j : Nat} (hj : j < 8) :
    m₁ (a + BitVec.ofNat 64 j) = m₂ (a + BitVec.ofNat 64 j) := by
  rw [← Mem.extractLsb'_read m₁ a hj, ← Mem.extractLsb'_read m₂ a hj]
  simp only [Mem.readW, BitVec.setWidth_eq] at h
  rw [h]

theorem replicate_le (ws : List Region) :
    List.Forall₂ (fun r l => l ≤ r.len) ws (List.replicate ws.length 0) := by
  induction ws with
  | nil => exact .nil
  | cons _ _ ih => exact .cons (Nat.zero_le _) ih

theorem frT_agree {n : Nat} {F : Addr} {ws : List Region} {rs : List Reg} {ks : List Nat} {t₁ t₂ : State}
    (h₁ : FrV n F ws t₁) (h₂ : FrV n F ws t₂) (hr : ∀ r ∈ rs, t₁.gpr r = t₂.gpr r) (hk : ∀ k ∈ ks, k < nW)
    (hw : ∀ k ∈ ks, word t₁.mem F (8 * k) = word t₂.mem F (8 * k)) : X86_64.Taint.Agree (frT rs ks n) t₁ t₂ := by
  have wf : ∀ {t : State}, FrV n F ws t → X86_64.Taint.Wf (frT rs ks n) t := fun h => by
    refine ⟨fun _ => ⟨?_, ?_, ?_⟩, fun p hp => ?_⟩
    · rw [h.wr, ← h.two]
      exact .cons (Nat.le_refl _) (replicate_le ws)
    · rw [h.wr]; exact h.pw
    · rw [h.wr]; intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · show frameBytes ≤ 2 ^ 64; decide
      · exact h.len r hr
    · simp only [frT, List.mem_singleton] at hp; subst hp
      simp only [X86_64.Taint.region, h.wr, List.getD_cons_zero]
      rw [h.rsp, BitVec.add_zero]
  refine ⟨⟨fun r hr' => ?_, fun hf => by cases hf⟩, fun _ => by rw [h₁.wr, h₂.wr], wf h₁, wf h₂,
    fun sl hsl => ?_, fun sl hsl j hj₁ hj₂ => ?_, X86_64.Taint.noLo, X86_64.Taint.noXr⟩
  · rcases List.mem_append.mp (RegSet.mem_ofList.mp hr') with hr' | hr'
    · exact hr r hr'
    · rw [List.mem_singleton.mp hr', h₁.rsp, h₂.rsp]
  · simp only [frT, List.mem_map] at hsl
    obtain ⟨k, hk', rfl⟩ := hsl
    have := hk k hk'
    simp only [frT, List.getD_cons_zero]
    unfold nW frameBytes at *; omega
  · simp only [frT, List.mem_map] at hsl
    obtain ⟨k, hk', rfl⟩ := hsl
    simp only at hj₁ hj₂
    have hb : ∀ {t : State}, FrV n F ws t → X86_64.Taint.byteAddr t 0 j = off F (8 * k) + BitVec.ofNat 64 (j - 8 * k) :=
      fun h => by
        simp only [X86_64.Taint.byteAddr, X86_64.Taint.region, h.wr, List.getD_cons_zero, off, BitVec.add_assoc,
          ← BitVec.ofNat_add]
        congr 2; omega
    rw [hb h₁, hb h₂]
    exact word_byte (hw k hk') (by omega)

variable {α : Type}

/-- Code the taint analysis checks from `frT rs ks`, in two runs that `Φ a`
puts in the same frame, with the same words `ks` and registers `rs`. -/
theorem two_taintF {n : Nat} {Φ : α → State → Prop} {c : Prog isa} (rs : List Reg) (ks : List Nat)
    (F : α → Addr) (ws : α → List Region) (w : α → Nat → BitVec 64)
    (hv : ∀ a t, Φ a t → FrV n (F a) (ws a) t ∧ ∀ k ∈ ks, word t.mem (F a) (8 * k) = w a k)
    (hpin : Pins Φ rs) (hk : ∀ k ∈ ks, k < nW)
    (h : ∃ hc, (taint.check (frT rs ks n) c hc).isSome = true) :
    RelCT isa (Two Φ) c fun _ _ => True := by
  obtain ⟨_, h⟩ := h
  refine RelCT.taint (A := taint) (frT rs ks n) (fun t₁ t₂ ⟨a, h₁, h₂⟩ => ?_) h
  obtain ⟨v₁, w₁⟩ := hv a t₁ h₁
  obtain ⟨v₂, w₂⟩ := hv a t₂ h₂
  exact frT_agree v₁ v₂ (hpin a _ _ h₁ h₂) hk fun k hk' => (w₁ k hk').trans (w₂ k hk').symm

/-- A piece checked by the taint analysis from `frT rs ks`, with what
correctness gives after it. -/
theorem two_pieceF {n : Nat} {Φ Ψ : α → State → Prop} {c : Prog isa} (rs : List Reg) (ks : List Nat)
    (F : α → Addr) (ws : α → List Region) (w : α → Nat → BitVec 64)
    (hv : ∀ a t, Φ a t → FrV n (F a) (ws a) t ∧ ∀ k ∈ ks, word t.mem (F a) (8 * k) = w a k)
    (hpin : Pins Φ rs) (hk : ∀ k ∈ ks, k < nW)
    (h : ∃ hc, (taint.check (frT rs ks n) c hc).isSome = true) (hw : ∀ a t, Φ a t → WP isa c t (Ψ a)) :
    RelCT isa (Two Φ) c (Two Ψ) :=
  two_post (two_taintF rs ks F ws w hv hpin hk h) hw

/-! ## The calls -/

theorem nopin {β : Type} {Φ : β → State → Prop} : Pins Φ [] := fun _ _ _ _ _ _ h => absurd h List.not_mem_nil

/-- An entry state like the anchor's `E`: of the same program, with the same
regions and stack pointer. -/
structure Like (E e : State) : Prop where
  same : abi.sameWorld e E
  rd : e.rd = E.rd
  wr : e.wr = E.wr
  sp : e.gpr .rsp = E.gpr .rsp

theorem Like.two {E e₁ e₂ : State} (h₁ : Like E e₁) (h₂ : Like E e₂) :
    abi.sameWorld e₂ e₁ ∧ e₂.rd = e₁.rd ∧ e₂.wr = e₁.wr ∧ e₂.gpr .rsp = e₁.gpr .rsp := by
  obtain ⟨⟨a₁, b₁, c₁⟩, r₁, w₁, s₁⟩ := h₁
  obtain ⟨⟨a₂, b₂, c₂⟩, r₂, w₂, s₂⟩ := h₂
  simp only [abi, Option.elim] at c₁ c₂
  exact ⟨⟨a₂.trans a₁.symm, b₂.trans b₁.symm, by simp only [abi, Option.elim]; exact c₂.trans c₁.symm⟩,
    r₂.trans r₁.symm, w₂.trans w₁.symm, s₂.trans s₁.symm⟩

/-- What an entry like `E` may read or write, `E` may. -/
theorem Like.inR {E e : State} (h : Like E e) {stack : Nat} {x : Addr} {n : Nat}
    (hx : InRegions (e.rd ++ e.wr ++ abi.reserved stack e) x n) :
    InRegions (E.rd ++ E.wr ++ abi.reserved stack E) x n := by
  rw [h.rd, h.wr, show abi.reserved stack e = abi.reserved stack E by simp only [abi, h.sp]] at hx
  exact hx

/-- In a run from an entry like `E`, which has the streaming functions `T` at
`fi`, `fu` and `ff`, a state that may call them (`Here`). -/
def Calls (stack : Nat) (T : Spec.HashFns.Streaming) (E : State) (F S fi fu ff : Addr) (t : State) : Prop :=
  ∃ e, Here stack e t F S ∧ Fns stack e T fi fu ff ∧ Like E e

/-- After a piece that keeps `Here`. -/
theorem Calls.of_here {stack : Nat} {T : Spec.HashFns.Streaming} {E : State} {F S fi fu ff : Addr} {t t' : State}
    (h : Calls stack T E F S fi fu ff t) (hh : ∀ e, Here stack e t F S → Here stack e t' F S) :
    Calls stack T E F S fi fu ff t' :=
  let ⟨e, a, b, c⟩ := h; ⟨e, hh e a, b, c⟩

/-- Code that calls nothing keeps `Calls`. -/
theorem Calls.wp {stack : Nat} {T : Spec.HashFns.Streaming} {E : State} {F S fi fu ff : Addr} {t : State}
    {c : Prog isa} (hc : c.noCalls = true) (h : Calls stack T E F S fi fu ff t) {Q : State → Prop}
    (hw : WP isa c t Q) : WP isa c t fun t' => Q t' ∧ Calls stack T E F S fi fu ff t' :=
  let ⟨e, hh, hF, hl⟩ := h
  WP.mono (WP.here hc hh hw) fun _ ⟨hq, hh'⟩ => ⟨hq, e, hh', hF, hl⟩

/-- After the load of an address into `r11`, from a state `Φ a` says. -/
def Ld (Φ : α → State → Prop) (fa : α → Addr) (a : α) (t : State) : Prop :=
  ∃ t₀, Φ a t₀ ∧ t.gpr .r11 = fa a ∧ t.mem = t₀.mem ∧ Keep [.r11] t₀ t ∧ t.funs = t₀.funs ∧ t.syms = t₀.syms

/-- The load of the address `fa a` from the frame's slot `sl`. -/
theorem two_ldFn {n : Nat} {Φ : α → State → Prop} (F S : α → Addr) (ws : α → List Region) (fa : α → Addr)
    {sl : Nat} (hv : ∀ a t, Φ a t → FrV n (F a) (ws a) t ∧ Lay t (F a) (S a) ∧
      t.mem.readW (off (F a) sl) 64 = fa a)
    (hsl : sl + 8 ≤ frameBytes) (ht : ∃ hc, (taint.check (frT [] [] n) (.block (ldFn sl)) hc).isSome = true) :
    RelCT isa (Two Φ) (.block (ldFn sl)) (Two (Ld Φ fa)) :=
  two_post (two_taintF [] [] F ws (fun _ _ => 0) (fun a t h => ⟨(hv a t h).1, fun _ h => absurd h List.not_mem_nil⟩)
    nopin (by decide) ht) fun a t h => by
      obtain ⟨-, L, hr⟩ := hv a t h
      refine WP.of_funs (WP.of_syms (WP.mono (WP.keep [.r11] (Q := fun t' => t'.gpr .r11 = fa a ∧ t'.mem = t.mem)
        ?_ rfl) fun t' ⟨⟨h1, hm⟩, k⟩ hsy hfu => ⟨t, h, h1, hm, k, hfu, hsy⟩))
      xrun [ldFn, ea_sp, L.rsp, L.ld (d := sl) hsl, hr]

/-- What the two states after the loads, of the same address, keep of their
entries. -/
theorem ld_two {Φ : α → State → Prop} {fa : α → Addr} {a : α} {stack : Nat} {T : Spec.HashFns.Streaming}
    {E : State} {F S fi fu ff : Addr} {t₁ t₂ : State}
    (h : ∀ t, Φ a t → Lay t F S ∧ Calls stack T E F S fi fu ff t) (p₁ : Ld Φ fa a t₁) (p₂ : Ld Φ fa a t₂) :
    ∃ e₁ e₂ u₁ u₂, Φ a u₁ ∧ Φ a u₂ ∧ Keep [.r11] u₁ t₁ ∧ Keep [.r11] u₂ t₂ ∧
      Lay t₁ F S ∧ Lay t₂ F S ∧ Here stack e₁ t₁ F S ∧ Here stack e₂ t₂ F S ∧
      Fns stack e₁ T fi fu ff ∧ Fns stack e₂ T fi fu ff ∧
      t₁.gpr .r11 = fa a ∧ t₂.gpr .r11 = fa a ∧ abi.sameWorld e₂ e₁ ∧ e₂.rd = e₁.rd ∧ e₂.wr = e₁.wr ∧
      e₂.gpr .rsp = e₁.gpr .rsp ∧ t₂.gpr .rsp = t₁.gpr .rsp ∧ Like E e₁ ∧ Like E e₂ := by
  obtain ⟨u₁, q₁, r₁, m₁, k₁, f₁, y₁⟩ := p₁
  obtain ⟨u₂, q₂, r₂, m₂, k₂, f₂, y₂⟩ := p₂
  obtain ⟨L₁, e₁, hh₁, F₁, l₁⟩ := h u₁ q₁
  obtain ⟨L₂, e₂, hh₂, F₂, l₂⟩ := h u₂ q₂
  have L₁' : Lay t₁ F S := L₁.congr (k₁.gpr (by decide)) k₁.2.2 (by rw [m₁])
  have L₂' : Lay t₂ F S := L₂.congr (k₂.gpr (by decide)) k₂.2.2 (by rw [m₂])
  obtain ⟨sw, rd, wr, sp⟩ := l₁.two l₂
  exact ⟨e₁, e₂, u₁, u₂, q₁, q₂, k₁, k₂, L₁', L₂', hh₁.keep m₁ k₁ f₁ y₁, hh₂.keep m₂ k₂ f₂ y₂, F₁, F₂, r₁, r₂,
    sw, rd, wr, sp, L₂'.rsp.trans L₁'.rsp.symm, l₁, l₂⟩

variable {T : Spec.HashFns.Streaming} {Hh : Spec.Mgf1.Hash} (hT : StreamingOK T Hh) (stack : Nat)

include hT in
/-- `init` through the address `fi a` in the slot `sl`, on the state at
`scratch + oSt` in both runs. -/
theorem two_initF {n : Nat} {Φ : α → State → Prop} (F S : α → Addr) (ws : α → List Region) (E : α → State)
    (fi fu ff : α → Addr) {sl : Nat}
    (h : ∀ a t, Φ a t → FrV n (F a) (ws a) t ∧ Lay t (F a) (S a) ∧ t.mem.readW (off (F a) sl) 64 = fi a ∧
      t.gpr .rdi = off (S a) oSt ∧ Calls stack T (E a) (F a) (S a) (fi a) (fu a) (ff a) t)
    (hsl : sl + 8 ≤ frameBytes) (ht : ∃ hc, (taint.check (frT [] [] n) (.block (ldFn sl)) hc).isSome = true) :
    RelCT isa (Two Φ) (initF sl) fun _ _ => True := by
  have h1 : oSt + T.S.stateBytes ≤ oRsa := by have := (sizes hT).1; unfold oSt oRsa; omega
  refine RelCT.seq (two_ldFn F S ws fi (fun a t p => let ⟨a1, a2, a3, _⟩ := h a t p; ⟨a1, a2, a3⟩) hsl ht) ?_
  refine (RelCT.exists_ (P := fun a t₁ t₂ => Ld Φ fi a t₁ ∧ Ld Φ fi a t₂) fun a =>
    init_irel T (stack := stack) (st := off (S a) oSt) fun t₁ t₂ ⟨p₁, p₂⟩ => ?_).mono (fun _ _ h => h)
      fun _ _ h => h
  obtain ⟨e₁, e₂, u₁, u₂, q₁, q₂, k₁, k₂, L₁, L₂, hh₁, hh₂, F₁, F₂, r₁, r₂, sw, rd, wr, sp, rsp, l₁, l₂⟩ :=
    ld_two (fun t p => let ⟨_, a2, _, _, a5⟩ := h a t p; ⟨a2, a5⟩) p₁ p₂
  refine ⟨e₁, e₂, ⟨by rw [r₁]; exact F₁.init, by rw [r₂]; exact F₂.init, hh₁.world, hh₂.world, sw, rd, wr, sp,
    r₂.trans r₁.symm, rsp⟩, init_pass hT hh₁ L₁, init_pass hT hh₂ L₂,
    (k₁.gpr (by decide)).trans (h a u₁ q₁).2.2.2.1, (k₂.gpr (by decide)).trans (h a u₂ q₂).2.2.2.1, L₁.bound h1,
    by rw [L₁.rsp]; exact hh₁.sp16, L₁.stk h1⟩

include hT in
/-- `update` through the address `fu a` in the slot `sl + 8`, with the
`len a` bytes at `scratch + o a`, after `cnt a`. -/
theorem two_updF {n : Nat} {Φ : α → State → Prop} (F S : α → Addr) (ws : α → List Region) (E : α → State)
    (fi fu ff : α → Addr) (o len : α → Nat) (cnt : α → BitVec 64) {sl : Nat}
    (h : ∀ a t, Φ a t → FrV n (F a) (ws a) t ∧ Lay t (F a) (S a) ∧
      t.mem.readW (off (F a) (sl + 8)) 64 = fu a ∧ Calls stack T (E a) (F a) (S a) (fi a) (fu a) (ff a) t ∧
      o a + len a ≤ oRsa ∧ (o a + len a ≤ oSt ∨ oSt + T.S.stateBytes ≤ o a) ∧
      (o a + len a ≤ oW ∨ oW + 8 * T.scratch ≤ o a) ∧ t.gpr .rdi = off (S a) oSt ∧ t.gpr .rsi = cnt a ∧
      t.gpr .rdx = off (S a) (o a) ∧ t.gpr .rcx = BitVec.ofNat 64 (len a) ∧ t.gpr .r8 = off (S a) oW)
    (hsl : sl + 8 + 8 ≤ frameBytes)
    (ht : ∃ hc, (taint.check (frT [] [] n) (.block (ldFn (sl + 8))) hc).isSome = true) :
    RelCT isa (Two Φ) (updF sl) fun _ _ => True := by
  refine RelCT.seq (two_ldFn F S ws fu (fun a t p => let ⟨a1, a2, a3, _⟩ := h a t p; ⟨a1, a2, a3⟩) hsl ht) ?_
  refine (RelCT.exists_ (P := fun a t₁ t₂ => Ld Φ fu a t₁ ∧ Ld Φ fu a t₂) fun a =>
    upd_irel T (stack := stack) (st := off (S a) oSt) (d := off (S a) (o a)) (sc := off (S a) oW) (len := len a)
      fun t₁ t₂ ⟨p₁, p₂⟩ => ?_).mono (fun _ _ h => h) fun _ _ h => h
  obtain ⟨e₁, e₂, u₁, u₂, q₁, q₂, k₁, k₂, L₁, L₂, hh₁, hh₂, F₁, F₂, r₁, r₂, sw, rd, wr, sp, rsp, l₁, l₂⟩ :=
    ld_two (fun t p => let ⟨_, a2, _, a4, _⟩ := h a t p; ⟨a2, a4⟩) p₁ p₂
  obtain ⟨-, -, -, -, a₁, b₁, c₁, d₁, s₁, x₁, y₁, z₁⟩ := h a u₁ q₁
  obtain ⟨-, -, -, -, -, -, -, d₂, s₂, x₂, y₂, z₂⟩ := h a u₂ q₂
  have g₁ : ∀ r, r ≠ .r11 → t₁.gpr r = u₁.gpr r := fun r hr => k₁.gpr (by simpa using hr)
  have g₂ : ∀ r, r ≠ .r11 → t₂.gpr r = u₂.gpr r := fun r hr => k₂.gpr (by simpa using hr)
  obtain ⟨A₁, P₁⟩ := upd_args hT hh₁ L₁ a₁ b₁ c₁ ((g₁ _ (by decide)).trans d₁) ((g₁ _ (by decide)).trans x₁)
    ((g₁ _ (by decide)).trans y₁) ((g₁ _ (by decide)).trans z₁)
  obtain ⟨A₂, P₂⟩ := upd_args hT hh₂ L₂ a₁ b₁ c₁ ((g₂ _ (by decide)).trans d₂) ((g₂ _ (by decide)).trans x₂)
    ((g₂ _ (by decide)).trans y₂) ((g₂ _ (by decide)).trans z₂)
  exact ⟨e₁, e₂, ⟨by rw [r₁]; exact F₁.upd, by rw [r₂]; exact F₂.upd, hh₁.world, hh₂.world, sw, rd, wr, sp,
    r₂.trans r₁.symm, rsp⟩, P₁, P₂, A₁, A₂, by rw [g₁ _ (by decide), g₂ _ (by decide), s₁, s₂]⟩

include hT in
/-- `update` through the address `fu a` in the slot `sl + 8`, with the
`len a` bytes at `d a`, outside our working space, after `cnt a`. -/
theorem two_updExtF {n : Nat} {Φ : α → State → Prop} (F S : α → Addr) (ws : α → List Region) (E : α → State)
    (fi fu ff : α → Addr) (d : α → Addr) (len : α → Nat) (cnt : α → BitVec 64) {sl : Nat}
    (h : ∀ a t, Φ a t → FrV n (F a) (ws a) t ∧ Lay t (F a) (S a) ∧
      t.mem.readW (off (F a) (sl + 8)) 64 = fu a ∧ Calls stack T (E a) (F a) (S a) (fi a) (fu a) (ff a) t ∧
      len a < 2 ^ 64 ∧ (d a).toNat + len a ≤ 2 ^ 64 ∧
      (∀ x, (⟨d a, len a⟩ : Region).Contains x 1 →
        InRegions ((E a).rd ++ (E a).wr ++ abi.reserved stack (E a)) x 1) ∧
      Region.Disjoint ⟨d a, len a⟩ ⟨S a, oRsa⟩ ∧ (below (F a) 16).Disjoint ⟨d a, len a⟩ ∧
      t.gpr .rdi = off (S a) oSt ∧ t.gpr .rsi = cnt a ∧ t.gpr .rdx = d a ∧
      t.gpr .rcx = BitVec.ofNat 64 (len a) ∧ t.gpr .r8 = off (S a) oW)
    (hsl : sl + 8 + 8 ≤ frameBytes)
    (ht : ∃ hc, (taint.check (frT [] [] n) (.block (ldFn (sl + 8))) hc).isSome = true) :
    RelCT isa (Two Φ) (updF sl) fun _ _ => True := by
  refine RelCT.seq (two_ldFn F S ws fu (fun a t p => let ⟨a1, a2, a3, _⟩ := h a t p; ⟨a1, a2, a3⟩) hsl ht) ?_
  refine (RelCT.exists_ (P := fun a t₁ t₂ => Ld Φ fu a t₁ ∧ Ld Φ fu a t₂) fun a =>
    upd_irel T (stack := stack) (st := off (S a) oSt) (d := d a) (sc := off (S a) oW) (len := len a)
      fun t₁ t₂ ⟨p₁, p₂⟩ => ?_).mono (fun _ _ h => h) fun _ _ h => h
  obtain ⟨e₁, e₂, u₁, u₂, q₁, q₂, k₁, k₂, L₁, L₂, hh₁, hh₂, F₁, F₂, r₁, r₂, sw, rd, wr, sp, rsp, l₁, l₂⟩ :=
    ld_two (fun t p => let ⟨_, a2, _, a4, _⟩ := h a t p; ⟨a2, a4⟩) p₁ p₂
  obtain ⟨-, -, -, -, a₁, b₁, c₁, ds, dk, d₁, s₁, x₁, y₁, z₁⟩ := h a u₁ q₁
  obtain ⟨-, -, -, -, -, -, -, -, -, d₂, s₂, x₂, y₂, z₂⟩ := h a u₂ q₂
  have g₁ : ∀ r, r ≠ .r11 → t₁.gpr r = u₁.gpr r := fun r hr => k₁.gpr (by simpa using hr)
  have g₂ : ∀ r, r ≠ .r11 → t₂.gpr r = u₂.gpr r := fun r hr => k₂.gpr (by simpa using hr)
  have cd : ∀ {e : State}, Like (E a) e → ∀ x, (⟨d a, len a⟩ : Region).Contains x 1 →
      InRegions (e.rd ++ e.wr ++ abi.reserved stack e) x 1 := fun {e} hl x hx => by
    rw [hl.rd, hl.wr, show abi.reserved stack e = abi.reserved stack (E a) by simp only [abi, hl.sp]]
    exact c₁ x hx
  obtain ⟨A₁, P₁⟩ := updExt_args hT hh₁ L₁ a₁ b₁ (cd l₁) ds dk ((g₁ _ (by decide)).trans d₁)
    ((g₁ _ (by decide)).trans x₁) ((g₁ _ (by decide)).trans y₁) ((g₁ _ (by decide)).trans z₁)
  obtain ⟨A₂, P₂⟩ := updExt_args hT hh₂ L₂ a₁ b₁ (cd l₂) ds dk ((g₂ _ (by decide)).trans d₂)
    ((g₂ _ (by decide)).trans x₂) ((g₂ _ (by decide)).trans y₂) ((g₂ _ (by decide)).trans z₂)
  exact ⟨e₁, e₂, ⟨by rw [r₁]; exact F₁.upd, by rw [r₂]; exact F₂.upd, hh₁.world, hh₂.world, sw, rd, wr, sp,
    r₂.trans r₁.symm, rsp⟩, P₁, P₂, A₁, A₂, by rw [g₁ _ (by decide), g₂ _ (by decide), s₁, s₂]⟩

include hT in
/-- `finalize` through the address `ff a` in the slot `sl + 16`, to
`scratch + o a`, after `cnt a`. -/
theorem two_finF {n : Nat} {Φ : α → State → Prop} (F S : α → Addr) (ws : α → List Region) (E : α → State)
    (fi fu ff : α → Addr) (o : α → Nat) (cnt : α → BitVec 64) {sl : Nat}
    (h : ∀ a t, Φ a t → FrV n (F a) (ws a) t ∧ Lay t (F a) (S a) ∧
      t.mem.readW (off (F a) (sl + 16)) 64 = ff a ∧ Calls stack T (E a) (F a) (S a) (fi a) (fu a) (ff a) t ∧
      (o a + 64 ≤ oSt ∨ (oSt + 256 ≤ o a ∧ o a + 64 ≤ oW)) ∧
      t.gpr .rdi = off (S a) oSt ∧ t.gpr .rsi = cnt a ∧ t.gpr .rdx = off (S a) (o a) ∧
      t.gpr .rcx = off (S a) oW)
    (hsl : sl + 16 + 8 ≤ frameBytes)
    (ht : ∃ hc, (taint.check (frT [] [] n) (.block (ldFn (sl + 16))) hc).isSome = true) :
    RelCT isa (Two Φ) (finF sl) fun _ _ => True := by
  refine RelCT.seq (two_ldFn F S ws ff (fun a t p => let ⟨a1, a2, a3, _⟩ := h a t p; ⟨a1, a2, a3⟩) hsl ht) ?_
  refine (RelCT.exists_ (P := fun a t₁ t₂ => Ld Φ ff a t₁ ∧ Ld Φ ff a t₂) fun a =>
    fin_irel T (stack := stack) (st := off (S a) oSt) (o := off (S a) (o a)) (sc := off (S a) oW)
      fun t₁ t₂ ⟨p₁, p₂⟩ => ?_).mono (fun _ _ h => h) fun _ _ h => h
  obtain ⟨e₁, e₂, u₁, u₂, q₁, q₂, k₁, k₂, L₁, L₂, hh₁, hh₂, F₁, F₂, r₁, r₂, sw, rd, wr, sp, rsp, -, -⟩ :=
    ld_two (fun t p => let ⟨_, a2, _, a4, _⟩ := h a t p; ⟨a2, a4⟩) p₁ p₂
  obtain ⟨-, -, -, -, a₁, d₁, s₁, x₁, y₁⟩ := h a u₁ q₁
  obtain ⟨-, -, -, -, -, d₂, s₂, x₂, y₂⟩ := h a u₂ q₂
  have g₁ : ∀ r, r ≠ .r11 → t₁.gpr r = u₁.gpr r := fun r hr => k₁.gpr (by simpa using hr)
  have g₂ : ∀ r, r ≠ .r11 → t₂.gpr r = u₂.gpr r := fun r hr => k₂.gpr (by simpa using hr)
  obtain ⟨A₁, P₁⟩ := fin_args hT hh₁ L₁ a₁ ((g₁ _ (by decide)).trans d₁) ((g₁ _ (by decide)).trans x₁)
    ((g₁ _ (by decide)).trans y₁)
  obtain ⟨A₂, P₂⟩ := fin_args hT hh₂ L₂ a₁ ((g₂ _ (by decide)).trans d₂) ((g₂ _ (by decide)).trans x₂)
    ((g₂ _ (by decide)).trans y₂)
  exact ⟨e₁, e₂, ⟨by rw [r₁]; exact F₁.fin, by rw [r₂]; exact F₂.fin, hh₁.world, hh₂.world, sw, rd, wr, sp,
    r₂.trans r₁.symm, rsp⟩, P₁, P₂, A₁, A₂, by rw [g₁ _ (by decide), g₂ _ (by decide), s₁, s₂]⟩

/-- `Φ a` of a state but for `rax` and the flags. -/
def Mod (Φ : α → State → Prop) (a : α) (t : State) : Prop :=
  ∃ t₀, Φ a t₀ ∧ t.mem = t₀.mem ∧ t.rd = t₀.rd ∧ t.wr = t₀.wr ∧ ∀ r, r ≠ .rax → t.gpr r = t₀.gpr r

end VG.Proof.RsaOaep.X86_64


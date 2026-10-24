module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Calls
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Contract
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.ChaCha20Poly1305
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# ChaCha20-Poly1305 on PPC64LE: the entry state, the invariant and the prologue

What the proofs use of the precondition (`APre`), the values kept in
`r24`–`r29` and our caller's registers saved in the context, and the
invariant that holds between the parts of the code (`Inv`); then the
prologue, which saves the registers, moves the arguments and stores the
ChaCha20 state for counter 0 in the context.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.PPC64LE

open VG VG.PPC64LE VG.Impl.ChaCha20Poly1305.PPC64LE
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20 (stateAt)

/-- `p + d`, as the code computes it. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d

section
variable (s₀ : State)
abbrev cx : Addr := s₀.gpr .r10
abbrev kp : Addr := s₀.gpr .r3
abbrev np : Addr := s₀.gpr .r4
abbrev ad : Addr := s₀.gpr .r5
abbrev AL : Nat := (s₀.gpr .r6).toNat
abbrev dp : Addr := s₀.gpr .r7
abbrev L : Nat := (s₀.gpr .r8).toNat
abbrev tp : Addr := s₀.gpr .r9

abbrev K : List Byte := bytesAt s₀.mem (kp s₀) 32
abbrev N : List Byte := bytesAt s₀.mem (np s₀) 12
abbrev A : List Byte := bytesAt s₀.mem (ad s₀) (AL s₀)
abbrev D : List Byte := bytesAt s₀.mem (dp s₀) (L s₀)
abbrev T0 : List Byte := bytesAt s₀.mem (tp s₀) 16
abbrev otk : List Byte := Spec.ChaCha20Poly1305.polyKeyGen (K s₀) (N s₀)

abbrev ctxR : Region := ⟨cx s₀, 648⟩
abbrev kR : Region := ⟨kp s₀, 32⟩
abbrev nR : Region := ⟨np s₀, 12⟩
abbrev aR : Region := ⟨ad s₀, AL s₀⟩
abbrev dR : Region := ⟨dp s₀, L s₀⟩
abbrev tR : Region := ⟨tp s₀, 16⟩
/-- The frame of `vg_poly1305_blocks`, below the stack pointer. -/
abbrev belR : Region := ⟨s₀.sp - 160, 160⟩
/-- `ctx[k, k + n)`. -/
abbrev sub (k n : Nat) : Region := ⟨off (cx s₀) k, n⟩
end

/-- What the proof uses of the precondition; `enc` for `seal`. -/
structure APre (enc : Bool) (s₀ : State) : Prop where
  sp160 : 160 ≤ s₀.sp.toNat
  rd : s₀.rd = if enc then [kR s₀, nR s₀, aR s₀] else [kR s₀, nR s₀, aR s₀, tR s₀]
  wr : s₀.wr = if enc then [dR s₀, tR s₀, ctxR s₀] else [dR s₀, ctxR s₀]
  k_d : (kR s₀).Disjoint (dR s₀)
  k_c : (kR s₀).Disjoint (ctxR s₀)
  n_d : (nR s₀).Disjoint (dR s₀)
  n_c : (nR s₀).Disjoint (ctxR s₀)
  a_d : (aR s₀).Disjoint (dR s₀)
  a_c : (aR s₀).Disjoint (ctxR s₀)
  d_t : (dR s₀).Disjoint (tR s₀)
  d_c : (dR s₀).Disjoint (ctxR s₀)
  t_c : (tR s₀).Disjoint (ctxR s₀)
  enc_t : if enc then (kR s₀).Disjoint (tR s₀) ∧ (nR s₀).Disjoint (tR s₀) ∧
    (aR s₀).Disjoint (tR s₀) else True
  b_k : (belR s₀).Disjoint (kR s₀)
  b_n : (belR s₀).Disjoint (nR s₀)
  b_a : (belR s₀).Disjoint (aR s₀)
  b_d : (belR s₀).Disjoint (dR s₀)
  b_t : (belR s₀).Disjoint (tR s₀)
  b_c : (belR s₀).Disjoint (ctxR s₀)
  fit_k : (kp s₀).toNat + 32 ≤ 2 ^ 64
  fit_n : (np s₀).toNat + 12 ≤ 2 ^ 64
  fit_a : (ad s₀).toNat + AL s₀ ≤ 2 ^ 64
  fit_d : (dp s₀).toNat + L s₀ ≤ 2 ^ 64
  fit_t : (tp s₀).toNat + 16 ≤ 2 ^ 64
  fit_c : (cx s₀).toNat + 648 ≤ 2 ^ 64

theorem APre.of {enc : Bool} (s₀ : State) (h : prePPC64LE enc s₀) : APre enc s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25⟩

variable {e : Bool}

theorem APre.ctx_wr {s₀ : State} (hp : APre e s₀) : ctxR s₀ ∈ s₀.wr := by
  rw [hp.wr]; cases e <;> simp

theorem APre.d_wr {s₀ : State} (hp : APre e s₀) : dR s₀ ∈ s₀.wr := by
  rw [hp.wr]; cases e <;> simp

theorem APre.a_rd {s₀ : State} (hp : APre e s₀) : aR s₀ ∈ s₀.rd := by
  rw [hp.rd]; cases e <;> simp

theorem APre.k_rd {s₀ : State} (hp : APre e s₀) : kR s₀ ∈ s₀.rd := by
  rw [hp.rd]; cases e <;> simp

theorem APre.n_rd {s₀ : State} (hp : APre e s₀) : nR s₀ ∈ s₀.rd := by
  rw [hp.rd]; cases e <;> simp

theorem APre.t_wr {s₀ : State} (hp : APre true s₀) : tR s₀ ∈ s₀.wr := by
  rw [hp.wr]; simp

theorem APre.t_rd {s₀ : State} (hp : APre false s₀) : tR s₀ ∈ s₀.rd := by
  rw [hp.rd]; simp

/-! ## Regions -/

theorem sub_ctx (s₀ : State) {k n : Nat} (h : k + n ≤ 648) : Region.Sub (sub s₀ k n) (ctxR s₀) :=
  Offset.sub_base _ h

theorem sub_disj (s₀ : State) {a n b m : Nat} (h : a + n ≤ b ∨ b + m ≤ a) (ha : a + n ≤ 648)
    (hb : b + m ≤ 648) : (sub s₀ a n).Disjoint (sub s₀ b m) :=
  Offset.disjoint (cx s₀) h (by omega) (by omega)

theorem contains_sub (s₀ : State) {k n a w : Nat} (h₁ : k ≤ a) (h₂ : a + w ≤ k + n) (h₃ : k + n ≤ 648) :
    (sub s₀ k n).Contains (off (cx s₀) a) w := Offset.contains (cx s₀) h₁ h₂ (by omega)

theorem contains_ctx (s₀ : State) {a w : Nat} (h : a + w ≤ 648) : (ctxR s₀).Contains (off (cx s₀) a) w :=
  Offset.contains_base (cx s₀) h (by omega)

theorem off_off (p : Addr) (a b : Nat) : off (off p a) b = off p (a + b) := by
  show p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem off_zero (p : Addr) : off p 0 = p := BitVec.add_zero p

theorem sub_zero (s₀ : State) (n : Nat) : sub s₀ 0 n = ⟨cx s₀, n⟩ := by simp [sub, off]

namespace APre
variable {s₀ : State} (hp : APre e s₀)
include hp

theorem in_ctx {a w : Nat} (h : a + w ≤ 648) : InRegions s₀.wr (off (cx s₀) a) w :=
  ⟨ctxR s₀, hp.ctx_wr, contains_ctx s₀ h⟩

theorem in_ctx' {a w : Nat} (h : a + w ≤ 648) : InRegions (s₀.rd ++ s₀.wr) (off (cx s₀) a) w :=
  ⟨ctxR s₀, List.mem_append_right _ hp.ctx_wr, contains_ctx s₀ h⟩

theorem k_in {d : Nat} (h : d + 4 ≤ 32) {s : State} (hrd : s.rd = s₀.rd) :
    InRegions (s.rd ++ s.wr) (off (kp s₀) d) 4 :=
  ⟨kR s₀, by rw [hrd]; exact List.mem_append_left _ hp.k_rd, Offset.contains_base _ h (by omega)⟩

theorem n_in {d : Nat} (h : d + 4 ≤ 12) {s : State} (hrd : s.rd = s₀.rd) :
    InRegions (s.rd ++ s.wr) (off (np s₀) d) 4 :=
  ⟨nR s₀, by rw [hrd]; exact List.mem_append_left _ hp.n_rd, Offset.contains_base _ h (by omega)⟩

end APre

/-! ## The saved registers and the invariant -/

/-- Our caller's `r24`–`r29` and our return address, saved in `ctx[464, 520)`. -/
def Saved (s₀ : State) (m : Mem) : Prop :=
  (∀ i < 6, m.readW (off (cx s₀) (savOff + 8 * i)) 64 = s₀.gpr (saved i)) ∧
    m.readW (off (cx s₀) (savOff + 48)) 64 = s₀.lr

/-- The saved registers survive a frame that does not touch them. -/
theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (sub s₀ savOff 56).Disjoint r) : Saved s₀ m' := by
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [hf.readW (contains_sub s₀ (w := 64 / 8) (by simp only [savOff]; omega)
      (by simp only [savOff]; omega) (by decide)) hd (by decide), h.1 i hi]
  · rw [hf.readW (contains_sub s₀ (w := 64 / 8) (by simp only [savOff]; omega)
      (by simp only [savOff]; omega) (by decide)) hd (by decide), h.2]

/-- The values we keep in `r24`–`r29`. -/
structure Regs (s₀ s : State) : Prop where
  r24 : s.gpr .r24 = cx s₀
  r25 : s.gpr .r25 = s₀.gpr .r5
  r26 : s.gpr .r26 = s₀.gpr .r6
  r27 : s.gpr .r27 = s₀.gpr .r7
  r28 : s.gpr .r28 = s₀.gpr .r8
  r29 : s.gpr .r29 = s₀.gpr .r9

theorem Regs.kept {s₀ s s' : State} (h : Regs s₀ s) (hk : ∀ r ∈ preserved, s'.gpr r = s.gpr r) :
    Regs s₀ s' :=
  ⟨by rw [hk _ (by decide), h.r24], by rw [hk _ (by decide), h.r25],
    by rw [hk _ (by decide), h.r26], by rw [hk _ (by decide), h.r27],
    by rw [hk _ (by decide), h.r28], by rw [hk _ (by decide), h.r29]⟩

/-- What holds between the parts of the code: the registers, the stack
pointer and the regions, the saved registers, and the memory changed only
in the context, the data and the stack below the stack pointer. -/
structure Inv (s₀ : State) (s : State) : Prop where
  regs : Regs s₀ s
  pres : ∀ r ∈ preserved, (∀ i < 6, r ≠ saved i) → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : Saved s₀ s.mem
  frame : Frame [ctxR s₀, dR s₀, belR s₀] s₀.mem s.mem

/-- The invariant survives a part that keeps the callee-saved registers and
writes only the context outside the saved registers, the data and the stack
below the stack pointer. -/
theorem Inv.step {s₀ s s' : State} {rs : List Region} (h : Inv s₀ s) (hk : Kept rs s s')
    (hsub : ∀ r ∈ rs, ∃ r' ∈ [ctxR s₀, dR s₀, belR s₀], Region.Sub r r')
    (hsv : ∀ r ∈ rs, (sub s₀ savOff 56).Disjoint r) : Inv s₀ s' where
  regs := h.regs.kept hk.cs
  pres r hr hne := by rw [hk.cs r hr, h.pres r hr hne]
  sp := by rw [hk.sp, h.sp]
  rd := by rw [hk.rd, h.rd]
  wr := by rw [hk.wr, h.wr]
  saved := h.saved.frame hk.frame hsv
  frame := h.frame.trans (hk.frame.sub hsub)

/-- A part that writes `ctx[k, k + n)` keeps the invariant. -/
theorem Inv.step1 {s₀ s s' : State} (h : Inv s₀ s) {k n : Nat} (hk : Kept [sub s₀ k n] s s')
    (h₂ : k + n ≤ 648) (h₃ : k + n ≤ savOff ∨ savOff + 56 ≤ k) : Inv s₀ s' :=
  h.step hk (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨ctxR s₀, by simp, sub_ctx s₀ h₂⟩)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by simp only [savOff] at h₃ ⊢; omega) (by decide) h₂)

/-- A part that writes no memory keeps the invariant. -/
theorem Inv.step0 {s₀ s s' : State} (h : Inv s₀ s) (hk : Kept [] s s') : Inv s₀ s' :=
  h.step hk (fun _ hr => absurd hr List.not_mem_nil) (fun _ hr => absurd hr List.not_mem_nil)

/-- The context may be read and written. -/
def CtxOk (s₀ s : State) : Prop :=
  ∀ a w, a + w ≤ 648 → InRegions (s.rd ++ s.wr) (off (cx s₀) a) w ∧ InRegions s.wr (off (cx s₀) a) w

theorem Inv.ctxOk {s₀ s : State} (hp : APre e s₀) (h : s.rd = s₀.rd) (h' : s.wr = s₀.wr) : CtxOk s₀ s :=
  fun _ _ hw => by rw [h, h']; exact ⟨hp.in_ctx' hw, hp.in_ctx hw⟩

theorem Kept.mem_eq {s s' : State} (hk : Kept [] s s') : s'.mem = s.mem :=
  funext fun x => hk.frame x fun _ h => absurd h List.not_mem_nil

/-- A block that writes no callee-saved register keeps them. -/
theorem WP.kept {is : List Instr} {s : State} {Q : State → Prop} (h : WP isa (.block is) s Q)
    (hc : (is.all fun i => preserved.all fun r => dstOf i != some r) = true) :
    WP isa (.block is) s fun s' => Q s' ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) := by
  obtain ⟨t, s', he, hq⟩ := h
  refine ⟨t, s', he, hq, fun r hr => Exec.gpr (fun i hi => ?_) he (.inl rfl)⟩
  have := List.all_eq_true.mp (List.all_eq_true.mp hc i hi) r hr
  simpa using this

end VG.Proof.ChaCha20Poly1305.PPC64LE

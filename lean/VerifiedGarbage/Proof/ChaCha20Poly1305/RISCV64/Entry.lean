module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.Calls
public import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Align
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Impl.ChaCha20Poly1305.RISCV64

/-!
# ChaCha20-Poly1305 on RISC-V: the entry state and the invariant

What the proofs use of the precondition (`APre`), the regions of the context
(`work` rounded up to a multiple of 8), our caller's registers saved there,
and the invariant that holds between the parts of the code (`Inv`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.RISCV64

open VG VG.RISCV64 VG.RISCV64.Align VG.Impl.ChaCha20Poly1305.RISCV64
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20 (stateAt)

/-- `p + d`, as the code computes it. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d

section
variable (s₀ : State)
abbrev kp : Addr := s₀.gpr .a0
abbrev np : Addr := s₀.gpr .a1
abbrev ad : Addr := s₀.gpr .a2
abbrev AL : Nat := (s₀.gpr .a3).toNat
abbrev dp : Addr := s₀.gpr .a4
abbrev L : Nat := (s₀.gpr .a5).toNat
abbrev tp : Addr := s₀.gpr .a6
abbrev wk : Addr := s₀.gpr .a7
/-- The context: `work` rounded up to a multiple of 8. -/
abbrev cx : Addr := wk s₀ + BitVec.ofNat 64 (pad (wk s₀))
/-- The Poly1305 state, which `a0` holds between the calls. -/
abbrev ps : Addr := off (cx s₀) polyOff

abbrev K : List Byte := bytesAt s₀.mem (kp s₀) 32
abbrev N : List Byte := bytesAt s₀.mem (np s₀) 12
abbrev A : List Byte := bytesAt s₀.mem (ad s₀) (AL s₀)
abbrev D : List Byte := bytesAt s₀.mem (dp s₀) (L s₀)
abbrev T0 : List Byte := bytesAt s₀.mem (tp s₀) 16
abbrev otk : List Byte := Spec.ChaCha20Poly1305.polyKeyGen (K s₀) (N s₀)

abbrev kR : Region := ⟨kp s₀, 32⟩
abbrev nR : Region := ⟨np s₀, 12⟩
abbrev aR : Region := ⟨ad s₀, AL s₀⟩
abbrev dR : Region := ⟨dp s₀, L s₀⟩
abbrev tR : Region := ⟨tp s₀, 16⟩
abbrev wR : Region := ⟨wk s₀, 616⟩
/-- `ctx[k, k + n)`. -/
abbrev sub (k n : Nat) : Region := ⟨off (cx s₀) k, n⟩
end

/-- What the proof uses of the precondition; `enc` for `seal`. -/
structure APre (enc : Bool) (s₀ : State) : Prop where
  rd : s₀.rd = if enc then [kR s₀, nR s₀, aR s₀] else [kR s₀, nR s₀, aR s₀, tR s₀]
  wr : s₀.wr = if enc then [dR s₀, tR s₀, wR s₀] else [dR s₀, wR s₀]
  k_d : (kR s₀).Disjoint (dR s₀)
  k_w : (kR s₀).Disjoint (wR s₀)
  n_d : (nR s₀).Disjoint (dR s₀)
  n_w : (nR s₀).Disjoint (wR s₀)
  a_d : (aR s₀).Disjoint (dR s₀)
  a_w : (aR s₀).Disjoint (wR s₀)
  d_t : (dR s₀).Disjoint (tR s₀)
  d_w : (dR s₀).Disjoint (wR s₀)
  t_w : (tR s₀).Disjoint (wR s₀)
  enc_t : if enc then (kR s₀).Disjoint (tR s₀) ∧ (nR s₀).Disjoint (tR s₀) ∧
    (aR s₀).Disjoint (tR s₀) else True
  fit_k : (kp s₀).toNat + 32 ≤ 2 ^ 64
  fit_n : (np s₀).toNat + 12 ≤ 2 ^ 64
  fit_a : (ad s₀).toNat + AL s₀ ≤ 2 ^ 64
  fit_d : (dp s₀).toNat + L s₀ ≤ 2 ^ 64
  fit_t : (tp s₀).toNat + 16 ≤ 2 ^ 64
  fit_w : (wk s₀).toNat + 616 ≤ 2 ^ 64

theorem APre.of {enc : Bool} (s₀ : State) (h : preRISCV64 enc s₀) : APre enc s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩

variable {e : Bool}

theorem APre.w_wr {s₀ : State} (hp : APre e s₀) : wR s₀ ∈ s₀.wr := by
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

theorem pad_lt' (s₀ : State) : pad (wk s₀) < 8 := pad_lt _

theorem cx_off (s₀ : State) (k : Nat) : off (cx s₀) k = off (wk s₀) (pad (wk s₀) + k) := by
  show _ + _ + _ = _
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem off_off (p : Addr) (a b : Nat) : off (off p a) b = off p (a + b) := by
  show p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b)
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem off_zero (p : Addr) : off p 0 = p := BitVec.add_zero p

/-- Offsets of the context by multiples of 8 are aligned. -/
theorem cx_al (s₀ : State) {d : Nat} (hd : d % 8 = 0) : (off (cx s₀) d).toNat % 8 = 0 :=
  align_al_add _ hd

theorem sub_work (s₀ : State) {k n : Nat} (h : k + n ≤ 608) : Region.Sub (sub s₀ k n) (wR s₀) := by
  have := pad_lt' s₀
  simp only [sub]; rw [cx_off]; exact Offset.sub_base _ (by omega)

theorem sub_disj (s₀ : State) {a n b m : Nat} (h : a + n ≤ b ∨ b + m ≤ a) (ha : a + n ≤ 608)
    (hb : b + m ≤ 608) : (sub s₀ a n).Disjoint (sub s₀ b m) :=
  Offset.disjoint (cx s₀) h (by omega) (by omega)

theorem contains_sub (s₀ : State) {k n a w : Nat} (h₁ : k ≤ a) (h₂ : a + w ≤ k + n) (h₃ : k + n ≤ 608) :
    (sub s₀ k n).Contains (off (cx s₀) a) w := Offset.contains (cx s₀) h₁ h₂ (by omega)

theorem contains_work (s₀ : State) {a w : Nat} (h : a + w ≤ 608) : (wR s₀).Contains (off (cx s₀) a) w := by
  have := pad_lt' s₀
  rw [cx_off]; exact Offset.contains_base _ (by omega) (by omega)

namespace APre
variable {s₀ : State} (hp : APre e s₀)
include hp

theorem in_w {a w : Nat} (h : a + w ≤ 608) : InRegions s₀.wr (off (cx s₀) a) w :=
  ⟨wR s₀, hp.w_wr, contains_work s₀ h⟩

theorem in_w' {a w : Nat} (h : a + w ≤ 608) : InRegions (s₀.rd ++ s₀.wr) (off (cx s₀) a) w :=
  ⟨wR s₀, List.mem_append_right _ hp.w_wr, contains_work s₀ h⟩

omit hp in
/-- A region apart from the working space is apart from every part of the context. -/
theorem w_sub {r : Region} (h : r.Disjoint (wR s₀)) {k n : Nat} (hk : k + n ≤ 608) :
    r.Disjoint (sub s₀ k n) := h.sub_right (sub_work s₀ hk)

end APre

/-! ## The saved registers and the invariant -/

/-- Our caller's `s7`–`s11` and our return address, saved in `ctx[560, 608)`. -/
structure Saved (s₀ : State) (m : Mem) : Prop where
  s7 : m.readW (off (cx s₀) savOff) 64 = s₀.gpr .s7
  s8 : m.readW (off (cx s₀) (savOff + 8)) 64 = s₀.gpr .s8
  s9 : m.readW (off (cx s₀) (savOff + 16)) 64 = s₀.gpr .s9
  s10 : m.readW (off (cx s₀) (savOff + 24)) 64 = s₀.gpr .s10
  s11 : m.readW (off (cx s₀) (savOff + 32)) 64 = s₀.gpr .s11
  ra : m.readW (off (cx s₀) (savOff + 40)) 64 = s₀.gpr .ra

/-- The saved registers survive a frame that does not touch them. -/
theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (sub s₀ savOff 48).Disjoint r) : Saved s₀ m' := by
  have c : ∀ k, k + 8 ≤ 48 → (sub s₀ savOff 48).Contains (off (cx s₀) (savOff + k)) (64 / 8) :=
    fun k hk => contains_sub s₀ (by omega) (by simp only [savOff]; omega) (by decide)
  have c0 : (sub s₀ savOff 48).Contains (off (cx s₀) savOff) (64 / 8) := by
    simpa using c 0 (by decide)
  exact ⟨by rw [hf.readW c0 hd (by decide), h.s7], by rw [hf.readW (c 8 (by decide)) hd (by decide), h.s8],
    by rw [hf.readW (c 16 (by decide)) hd (by decide), h.s9],
    by rw [hf.readW (c 24 (by decide)) hd (by decide), h.s10],
    by rw [hf.readW (c 32 (by decide)) hd (by decide), h.s11],
    by rw [hf.readW (c 40 (by decide)) hd (by decide), h.ra]⟩

/-- The values we keep in `s7`–`s11`. -/
structure Regs (s₀ s : State) : Prop where
  s7 : s.gpr .s7 = s₀.gpr .a2
  s8 : s.gpr .s8 = s₀.gpr .a3
  s9 : s.gpr .s9 = s₀.gpr .a4
  s10 : s.gpr .s10 = s₀.gpr .a5
  s11 : s.gpr .s11 = s₀.gpr .a6

theorem Regs.kept {s₀ s s' : State} (h : Regs s₀ s) (hk : ∀ r ∈ preserved, s'.gpr r = s.gpr r) :
    Regs s₀ s' :=
  ⟨by rw [hk _ (by decide), h.s7], by rw [hk _ (by decide), h.s8], by rw [hk _ (by decide), h.s9],
    by rw [hk _ (by decide), h.s10], by rw [hk _ (by decide), h.s11]⟩

/-- The callee-saved registers we do not save. -/
abbrev others : List Reg := [.s0, .s1, .s2, .s3, .s4, .s5, .s6]

/-- What holds between the parts of the code: the registers, the stack
pointer and the regions, the saved registers, and memory changed only in
the working space and the data. -/
structure Inv (s₀ : State) (s : State) : Prop where
  regs : Regs s₀ s
  pres : ∀ r ∈ others, s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : Saved s₀ s.mem
  frame : Frame [wR s₀, dR s₀] s₀.mem s.mem

/-- A part's effect: the callee-saved registers, the stack pointer and the
regions kept, and memory changed only within `rs`. -/
structure Step (rs : List Region) (s s' : State) : Prop where
  cs : ∀ r ∈ preserved, s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame rs s.mem s'.mem

theorem Kept.step {rs : List Region} {s s' : State} (h : Kept rs s s') : Step rs s s' :=
  ⟨h.cs, h.sp, h.rd, h.wr, h.frame⟩

theorem Step.refl (rs : List Region) (s : State) : Step rs s s :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩

theorem Step.trans {rs : List Region} {s₁ s₂ s₃ : State} (h₁ : Step rs s₁ s₂) (h₂ : Step rs s₂ s₃) :
    Step rs s₁ s₃ :=
  ⟨fun r hr => (h₂.cs r hr).trans (h₁.cs r hr), h₂.sp.trans h₁.sp, h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr, h₁.frame.trans h₂.frame⟩

theorem Step.mono {rs rs' : List Region} {s s' : State} (h : Step rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    Step rs' s s' := ⟨h.cs, h.sp, h.rd, h.wr, h.frame.mono hs⟩

/-- An instruction writing a temporary register is a step. -/
theorem Step.upd {s s' : State} {d : Reg} {v : BitVec 64} (rs : List Region) (u : Steps.Upd s s' d v)
    (hd : d ∉ preserved := by decide) : Step rs s s' :=
  ⟨fun r hr => u.other r fun e => hd (e ▸ hr), u.sp, u.rd, u.wr, by rw [u.mem]; exact Frame.refl _ _⟩

/-- The invariant survives a step that writes only within the context
outside the saved registers, and the data. -/
theorem Inv.step {s₀ s s' : State} {rs : List Region} (h : Inv s₀ s) (hk : Step rs s s')
    (hsub : ∀ r ∈ rs, ∃ r' ∈ [wR s₀, dR s₀], Region.Sub r r')
    (hsv : ∀ r ∈ rs, (sub s₀ savOff 48).Disjoint r) : Inv s₀ s' where
  regs := h.regs.kept hk.cs
  pres r hr := by rw [hk.cs r (by revert r; decide), h.pres r hr]
  sp := by rw [hk.sp, h.sp]
  rd := by rw [hk.rd, h.rd]
  wr := by rw [hk.wr, h.wr]
  saved := h.saved.frame hk.frame hsv
  frame := h.frame.trans (hk.frame.sub hsub)

/-- A part that writes `ctx[k, k + n)`, below the saved registers, keeps the
invariant. -/
theorem Inv.step1 {s₀ s s' : State} (h : Inv s₀ s) {k n : Nat} (hk : Step [sub s₀ k n] s s')
    (h₂ : k + n ≤ savOff) : Inv s₀ s' :=
  h.step hk (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨wR s₀, by simp, sub_work s₀ (by simp only [savOff] at h₂ ⊢; omega)⟩)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by simp only [savOff] at h₂ ⊢; omega) (by decide)
        (by simp only [savOff] at h₂ ⊢; omega))

theorem Inv.step2 {s₀ s s' : State} (h : Inv s₀ s) {k n k' n' : Nat}
    (hk : Step [sub s₀ k n, sub s₀ k' n'] s s') (h₂ : k + n ≤ savOff) (h₃ : k' + n' ≤ savOff) :
    Inv s₀ s' :=
  h.step hk (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨wR s₀, by simp, sub_work s₀ (by simp only [savOff] at h₂ ⊢; omega)⟩
      · exact ⟨wR s₀, by simp, sub_work s₀ (by simp only [savOff] at h₃ ⊢; omega)⟩)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_disj s₀ (by simp only [savOff] at h₂ ⊢; omega) (by decide)
          (by simp only [savOff] at h₂ ⊢; omega)
      · exact sub_disj s₀ (by simp only [savOff] at h₃ ⊢; omega) (by decide)
          (by simp only [savOff] at h₃ ⊢; omega))

/-! ## Memory through frames -/

/-- Bytes outside a frame are unchanged. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

/-- A ChaCha20 state outside a frame is unchanged. -/
theorem stateAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 64⟩ : Region).Disjoint r) : stateAt m' p = stateAt m p := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn]
  exact hf.readW (Offset.contains_base p (by omega) (by omega)) hd (by decide)

/-- A Poly1305 state with its buffer outside a frame is unchanged. -/
theorem Buffered.frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {P : Addr}
    (hd : ∀ r ∈ rs, (⟨P, 128⟩ : Region).Disjoint r) {key msg : List Byte}
    (h : Spec.Poly1305.Buffered m P key msg) : Spec.Poly1305.Buffered m' P key msg := by
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h
  have hl : msg.length % 16 < 16 := Nat.mod_lt _ (by decide)
  refine ⟨⟨h1, ?_, ?_⟩, ?_⟩
  · rw [show (P + 24 : Addr) = P + BitVec.ofNat 64 24 from rfl,
      bytesAt_frame hf (n := 32) (fun r hr => (hd r hr).sub_left (Offset.sub_base P (d := 24) (by decide)))
      (by decide)]
    exact h2
  · rw [bytesAt_frame hf (n := 24) (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by decide)))
      (by decide)]
    exact h3
  · rw [show (P + 56 : Addr) = P + BitVec.ofNat 64 56 from rfl,
      bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Offset.sub_base P (d := 56) (by omega)))
      (by omega)]
    exact h4

end VG.Proof.ChaCha20Poly1305.RISCV64

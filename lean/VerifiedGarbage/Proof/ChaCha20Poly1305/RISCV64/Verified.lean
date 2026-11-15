module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.Calls
public import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Align
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Impl.ChaCha20Poly1305.RISCV64
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.ChaCha20.Stream
import VerifiedGarbage.Proof.ChaCha20.RISCV64.Stream.Init
import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
import VerifiedGarbage.Proof.Poly1305.Spec
public import VerifiedGarbage.Proof.ChaCha20Poly1305.Spec
import VerifiedGarbage.Proof.ChaCha20.Keystream
import VerifiedGarbage.Proof.Poly1305.RISCV64.Buffer
import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.CT
public import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch
public import VerifiedGarbage.Impl.StackScratch.RISCV64
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
meta import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.Scratch
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.ContractPost
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.RISCV64.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.ChaCha20Poly1305.OpenToScratch
public import VerifiedGarbage.Proof.Framework.RISCV64.StackScratchArgsWipe
public import VerifiedGarbage.Proof.Zeroize.Common
public import VerifiedGarbage.Proof.Framework.RelCT

/-! ### `ChaCha20Poly1305.RISCV64.Mac`, which only this module used -/

section

/-! ### `ChaCha20Poly1305.RISCV64.Prologue`, which only this module used -/

section

/-! ### `ChaCha20Poly1305.RISCV64.Entry`, which only this module used -/

section

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
/-- The destination: `src` in place, or apart from it. -/
abbrev op : Addr := s₀.gpr .t6
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
abbrev oR : Region := ⟨op s₀, L s₀⟩
abbrev wR : Region := ⟨wk s₀, 624⟩
/-- `ctx[k, k + n)`. -/
abbrev sub (k n : Nat) : Region := ⟨off (cx s₀) k, n⟩
end

/-- What the proof uses of the precondition; `enc` for `seal`, which runs
in place. -/
structure APre (enc : Bool) (s₀ : State) : Prop where
  k_rd : kR s₀ ∈ s₀.rd
  n_rd : nR s₀ ∈ s₀.rd
  a_rd : aR s₀ ∈ s₀.rd
  /-- The source is readable. -/
  d_in : dR s₀ ∈ s₀.rd ++ s₀.wr
  /-- The destination is writable. -/
  o_wr : oR s₀ ∈ s₀.wr
  w_wr : wR s₀ ∈ s₀.wr
  t_in : if enc then tR s₀ ∈ s₀.wr else tR s₀ ∈ s₀.rd
  k_w : (kR s₀).Disjoint (wR s₀)
  n_w : (nR s₀).Disjoint (wR s₀)
  a_w : (aR s₀).Disjoint (wR s₀)
  d_w : (dR s₀).Disjoint (wR s₀)
  t_w : (tR s₀).Disjoint (wR s₀)
  k_o : (kR s₀).Disjoint (oR s₀)
  n_o : (nR s₀).Disjoint (oR s₀)
  a_o : (aR s₀).Disjoint (oR s₀)
  o_t : (oR s₀).Disjoint (tR s₀)
  o_w : (oR s₀).Disjoint (wR s₀)
  /-- In place, or (`open` only) apart. -/
  alias : op s₀ = dp s₀ ∨ (enc = false ∧ (dR s₀).Disjoint (oR s₀))
  enc_t : if enc then (kR s₀).Disjoint (tR s₀) ∧ (nR s₀).Disjoint (tR s₀) ∧
    (aR s₀).Disjoint (tR s₀) else True
  fit_k : (kp s₀).toNat + 32 ≤ 2 ^ 64
  fit_n : (np s₀).toNat + 12 ≤ 2 ^ 64
  fit_a : (ad s₀).toNat + AL s₀ ≤ 2 ^ 64
  fit_d : (dp s₀).toNat + L s₀ ≤ 2 ^ 64
  fit_o : (op s₀).toNat + L s₀ ≤ 2 ^ 64
  fit_t : (tp s₀).toNat + 16 ≤ 2 ^ 64
  fit_w : (wk s₀).toNat + 624 ≤ 2 ^ 64

variable {e : Bool}

theorem APre.t_wr {s₀ : State} (hp : APre true s₀) : tR s₀ ∈ s₀.wr := hp.t_in

theorem APre.t_rd {s₀ : State} (hp : APre false s₀) : tR s₀ ∈ s₀.rd := hp.t_in

/-- `seal` runs in place. -/
theorem APre.inPlace {s₀ : State} (hp : APre true s₀) : op s₀ = dp s₀ := by
  rcases hp.alias with h | ⟨h, -⟩
  · exact h
  · exact absurd h (by decide)

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

theorem sub_work (s₀ : State) {k n : Nat} (h : k + n ≤ 616) : Region.Sub (sub s₀ k n) (wR s₀) := by
  have := pad_lt' s₀
  simp only [sub]; rw [cx_off]; exact Offset.sub_base _ (by omega_using [h, this])

theorem sub_disj (s₀ : State) {a n b m : Nat} (h : a + n ≤ b ∨ b + m ≤ a) (ha : a + n ≤ 616)
    (hb : b + m ≤ 616) : (sub s₀ a n).Disjoint (sub s₀ b m) :=
  Offset.disjoint (cx s₀) h (by omega_using [ha]) (by omega_using [hb])

theorem contains_sub (s₀ : State) {k n a w : Nat} (h₁ : k ≤ a) (h₂ : a + w ≤ k + n) (h₃ : k + n ≤ 616) :
    (sub s₀ k n).Contains (off (cx s₀) a) w := Offset.contains (cx s₀) h₁ h₂ (by omega_using [h₃])

theorem contains_work (s₀ : State) {a w : Nat} (h : a + w ≤ 616) : (wR s₀).Contains (off (cx s₀) a) w := by
  have := pad_lt' s₀
  rw [cx_off]; exact Offset.contains_base _ (by omega_using [h, this]) (by omega_using [h, this])

namespace APre
variable {s₀ : State} (hp : APre e s₀)
include hp

theorem in_w {a w : Nat} (h : a + w ≤ 616) : InRegions s₀.wr (off (cx s₀) a) w :=
  ⟨wR s₀, hp.w_wr, contains_work s₀ h⟩

theorem in_w' {a w : Nat} (h : a + w ≤ 616) : InRegions (s₀.rd ++ s₀.wr) (off (cx s₀) a) w :=
  ⟨wR s₀, List.mem_append_right _ hp.w_wr, contains_work s₀ h⟩

omit hp in
/-- A region apart from the working space is apart from every part of the context. -/
theorem w_sub {r : Region} (h : r.Disjoint (wR s₀)) {k n : Nat} (hk : k + n ≤ 616) :
    r.Disjoint (sub s₀ k n) := h.sub_right (sub_work s₀ hk)

end APre

/-! ## The saved registers and the invariant -/

/-- Our caller's `s7`–`s11`, our return address and our caller's `s6`,
saved in `ctx[560, 616)`. -/
structure Saved (s₀ : State) (m : Mem) : Prop where
  s7 : m.readW (off (cx s₀) savOff) 64 = s₀.gpr .s7
  s8 : m.readW (off (cx s₀) (savOff + 8)) 64 = s₀.gpr .s8
  s9 : m.readW (off (cx s₀) (savOff + 16)) 64 = s₀.gpr .s9
  s10 : m.readW (off (cx s₀) (savOff + 24)) 64 = s₀.gpr .s10
  s11 : m.readW (off (cx s₀) (savOff + 32)) 64 = s₀.gpr .s11
  ra : m.readW (off (cx s₀) (savOff + 40)) 64 = s₀.gpr .ra
  s6 : m.readW (off (cx s₀) (savOff + 48)) 64 = s₀.gpr .s6

/-- The saved registers survive a frame that does not touch them. -/
theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : Saved s₀ m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (sub s₀ savOff 56).Disjoint r) : Saved s₀ m' := by
  have c : ∀ k, k + 8 ≤ 56 → (sub s₀ savOff 56).Contains (off (cx s₀) (savOff + k)) (64 / 8) :=
    fun k hk => contains_sub s₀ (by omega_using []) (by simp only [savOff]; omega_using [hk]) (by decide)
  have c0 : (sub s₀ savOff 56).Contains (off (cx s₀) savOff) (64 / 8) := by
    simpa using c 0 (by decide)
  exact ⟨by rw [hf.readW c0 hd (by decide), h.s7], by rw [hf.readW (c 8 (by decide)) hd (by decide), h.s8],
    by rw [hf.readW (c 16 (by decide)) hd (by decide), h.s9],
    by rw [hf.readW (c 24 (by decide)) hd (by decide), h.s10],
    by rw [hf.readW (c 32 (by decide)) hd (by decide), h.s11],
    by rw [hf.readW (c 40 (by decide)) hd (by decide), h.ra],
    by rw [hf.readW (c 48 (by decide)) hd (by decide), h.s6]⟩

/-- The values we keep in `s7`–`s11` and `s6`. -/
structure Regs (s₀ s : State) : Prop where
  s7 : s.gpr .s7 = s₀.gpr .a2
  s8 : s.gpr .s8 = s₀.gpr .a3
  s9 : s.gpr .s9 = s₀.gpr .a4
  s10 : s.gpr .s10 = s₀.gpr .a5
  s11 : s.gpr .s11 = s₀.gpr .a6
  s6 : s.gpr .s6 = s₀.gpr .t6

theorem Regs.kept {s₀ s s' : State} (h : Regs s₀ s) (hk : ∀ r ∈ preserved, s'.gpr r = s.gpr r) :
    Regs s₀ s' :=
  ⟨by rw [hk _ (by decide), h.s7], by rw [hk _ (by decide), h.s8], by rw [hk _ (by decide), h.s9],
    by rw [hk _ (by decide), h.s10], by rw [hk _ (by decide), h.s11], by rw [hk _ (by decide), h.s6]⟩

/-- The callee-saved registers we do not save. -/
abbrev others : List Reg := [.s0, .s1, .s2, .s3, .s4, .s5]

/-- What holds between the parts of the code: the registers, the stack
pointer and the regions, the saved registers, and memory changed only in
the working space and the destination. -/
structure Inv (s₀ : State) (s : State) : Prop where
  regs : Regs s₀ s
  pres : ∀ r ∈ others, s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : Saved s₀ s.mem
  frame : Frame [wR s₀, oR s₀] s₀.mem s.mem

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
outside the saved registers, and the destination. -/
theorem Inv.step {s₀ s s' : State} {rs : List Region} (h : Inv s₀ s) (hk : Step rs s s')
    (hsub : ∀ r ∈ rs, ∃ r' ∈ [wR s₀, oR s₀], Region.Sub r r')
    (hsv : ∀ r ∈ rs, (sub s₀ savOff 56).Disjoint r) : Inv s₀ s' where
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
      exact ⟨wR s₀, by simp, sub_work s₀ (by simp only [savOff] at h₂ ⊢; omega_using [h₂])⟩)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by simp only [savOff] at h₂ ⊢; omega_using [h₂]) (by decide)
        (by simp only [savOff] at h₂ ⊢; omega_using [h₂]))

theorem Inv.step2 {s₀ s s' : State} (h : Inv s₀ s) {k n k' n' : Nat}
    (hk : Step [sub s₀ k n, sub s₀ k' n'] s s') (h₂ : k + n ≤ savOff) (h₃ : k' + n' ≤ savOff) :
    Inv s₀ s' :=
  h.step hk (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨wR s₀, by simp, sub_work s₀ (by simp only [savOff] at h₂ ⊢; omega_using [h₂])⟩
      · exact ⟨wR s₀, by simp, sub_work s₀ (by simp only [savOff] at h₃ ⊢; omega_using [h₃])⟩)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_disj s₀ (by simp only [savOff] at h₂ ⊢; omega_using [h₂]) (by decide)
          (by simp only [savOff] at h₂ ⊢; omega_using [h₂])
      · exact sub_disj s₀ (by simp only [savOff] at h₃ ⊢; omega_using [h₃]) (by decide)
          (by simp only [savOff] at h₃ ⊢; omega_using [h₃]))

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
  exact hf.readW (Offset.contains_base p (by omega_using [hi]) (by omega_using [hi])) hd (by decide)

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
      bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Offset.sub_base P (d := 56) (by omega_using [])))
      (by omega_using [])]
    exact h4

end VG.Proof.ChaCha20Poly1305.RISCV64

end

end


/-!
# ChaCha20-Poly1305 on RISC-V: the prologue

Saving the registers, moving the arguments, and the ChaCha20 state for
counter 0, the zeros of the padding and the lengths block in the context,
byte by byte.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.RISCV64

open VG VG.RISCV64 VG.RISCV64.Align VG.RISCV64.Steps VG.RISCV64.Bytes VG.Impl.ChaCha20Poly1305.RISCV64
open VG.Impl.ChaCha20.RISCV64.Xor (mov)
open VG.Spec.Poly1305 (bytesAt leBytes)
open VG.Spec.ChaCha20 (stateAt initState)

variable {e : Bool}

/-! ## The ChaCha20 state from its bytes -/

/-- A 16-word state whose bytes are the constants, a key, a counter and a nonce. -/
theorem stateAt_init {m : Mem} {p : Addr} {key nonce : List Byte} {c : Spec.ChaCha20.Word}
    (hσ : ∀ i < 16, m (off p i) = Proof.ChaCha20.sigma.getD i 0)
    (hK : ∀ i < 32, m (off p (16 + i)) = key.getD i 0)
    (hc : ∀ i < 4, m (off p (48 + i)) = c.extractLsb' (8 * i) 8)
    (hN : ∀ i < 12, m (off p (52 + i)) = nonce.getD i 0) :
    stateAt m p = initState key c nonce := by
  apply Vector.ext; intro j hj
  simp only [initState, Vector.getElem_ofFn]
  by_cases h4 : j < 4
  · simp only [h4, ↓reduceIte]
    rw [Proof.ChaCha20.stateAt_getElem m p hj (bs := Proof.ChaCha20.sigma)
      fun i hi => hσ _ (by omega_using [h4, hi]), Proof.ChaCha20.sigma_words j h4]
  simp only [h4, ↓reduceIte]
  by_cases h12 : j < 12
  · simp only [h12, ↓reduceIte]
    rw [Proof.ChaCha20.stateAt_getElem m p hj (bs := List.replicate 16 0 ++ key) fun i hi => ?_,
      Proof.ChaCha20.wordLE_append_right (a := 4) (by simp) (by omega_using [h4])]
    rw [Proof.ChaCha20.getD_append_right (by simp; omega_using [h4]), List.length_replicate]
    have := hK (4 * j + i - 16) (by omega_using [h12, hi])
    rwa [show 16 + (4 * j + i - 16) = 4 * j + i by omega_using [h4]] at this
  simp only [h12, ↓reduceIte]
  by_cases h' : j = 12
  · subst h'
    simp only [stateAt, Vector.getElem_ofFn]
    refine Proof.ChaCha20.word_ext fun i hi => ?_
    rw [← Mem.readW_byte m _ hi, Offset.add_add]
    exact hc i hi
  · simp only [h', ↓reduceIte]
    rw [Proof.ChaCha20.stateAt_getElem m p hj (bs := List.replicate 52 0 ++ nonce) fun i hi => ?_,
      Proof.ChaCha20.wordLE_append_right (a := 13) (by simp) (by omega_using [h12, h'])]
    rw [Proof.ChaCha20.getD_append_right (by simp; omega_using [h12, h']), List.length_replicate]
    have := hN (4 * j + i - 52) (by omega_using [hj, hi])
    rwa [show 52 + (4 * j + i - 52) = 4 * j + i by omega_using [h12, h']] at this

/-! ## Memory of the context -/

/-- A doubleword of the context after a doubleword written elsewhere in it. -/
theorem slot_other (s₀ : State) (m : Mem) (v : BitVec 64) {a b : Nat} (h : a + 8 ≤ b ∨ b + 8 ≤ a)
    (ha : a + 8 ≤ 616) (hb : b + 8 ≤ 616) :
    (m.writeW (off (cx s₀) b) v).readW (off (cx s₀) a) 64 = m.readW (off (cx s₀) a) 64 :=
  Mem.readW_writeW_sep (Offset.sep _ h (by omega_using [ha]) (by omega_using [hb])) (by decide)

/-- A byte of the context outside a part written. -/
theorem byte_sub (s₀ : State) {m m' : Mem} {k n i : Nat} (hf : Frame [sub s₀ k n] m m')
    (h : i + 1 ≤ k ∨ k + n ≤ i) (hk : k + n ≤ 616) (hi : i < 616) :
    m' (off (cx s₀) i) = m (off (cx s₀) i) :=
  hf _ fun r hr hc => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint (cx s₀) h (by omega_using [hi]) (by omega_using [hk]) _ (Region.contains_self _ _) hc

theorem fw_sub (s₀ : State) {m m' : Mem} {k n : Nat} (hf : Frame [sub s₀ k n] m m') (h : k + n ≤ 616) :
    Frame [wR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, sub_work s₀ h⟩

theorem sv_sub (s₀ : State) {m m' : Mem} {k n : Nat} (h : Saved s₀ m) (hf : Frame [sub s₀ k n] m m')
    (hk : k + n ≤ savOff) : Saved s₀ m' :=
  h.frame hf fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact sub_disj s₀ (by simp only [savOff] at hk ⊢; omega_using [hk]) (by decide) (by simp only [savOff] at hk ⊢; omega_using [hk])

/-- A byte of a region apart from the working space, through a frame of it. -/
theorem byte_out (s₀ : State) {m m' : Mem} (hf : Frame [wR s₀] m m') {R : Region} (hd : R.Disjoint (wR s₀))
    (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    m' (R.base + BitVec.ofNat 64 i) = m (R.base + BitVec.ofNat 64 i) :=
  hf.bytes (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd) hR hi

/-! ## Saving the registers -/

/-- After `save`. -/
structure PostS (s₀ s : State) : Prop where
  t0 : s.gpr .t0 = cx s₀
  gpr : ∀ r, r ≠ .t0 → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : Saved s₀ s.mem
  frame : Frame [sub s₀ savOff 56] s₀.mem s.mem

theorem save_ok {s₀ : State} (hp : APre e s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s, PostS s₀ s → WP isa (.block rest) s Q) : WP isa (.block (save ++ rest)) s₀ Q := by
  simp only [save, List.cons_append]
  refine wp_addi (imm := 7) (by decide) fun s₁ u₁ => wp_andi (by decide) fun s₂ u₂ => ?_
  have t0 : s₂.gpr .t0 = cx s₀ := by rw [u₂.gpr, u₁.gpr]; exact align_eq _
  have g₂ : ∀ r, r ≠ .t0 → s₂.gpr r = s₀.gpr r := fun r h => by rw [u₂.other r h, u₁.other r h]
  have w₂ : s₂.wr = s₀.wr := by rw [u₂.wr, u₁.wr]
  have hin : ∀ d, d + 8 ≤ 56 → InRegions s₂.wr (off (cx s₀) (savOff + d)) 8 := fun d hd => by
    rw [w₂]; exact hp.in_w (by simp only [savOff]; omega_using [hd])
  have hal : ∀ d, d % 8 = 0 → (off (cx s₀) (savOff + d)).toNat % 8 = 0 := fun d hd =>
    cx_al s₀ (by simp only [savOff]; omega_using [hd])
  refine wp_sd (a := off (cx s₀) (savOff + 0)) (by decide) (by rw [t0]; rfl) (hal 0 (by decide))
    (hin 0 (by decide)) fun s₃ g₃ => ?_
  refine wp_sd (a := off (cx s₀) (savOff + 8)) (by decide) (by rw [g₃.gpr, t0]) (hal 8 (by decide))
    (by rw [g₃.wr]; exact hin 8 (by decide)) fun s₄ g₄ => ?_
  refine wp_sd (a := off (cx s₀) (savOff + 16)) (by decide) (by rw [g₄.gpr, g₃.gpr, t0])
    (hal 16 (by decide)) (by rw [g₄.wr, g₃.wr]; exact hin 16 (by decide)) fun s₅ g₅ => ?_
  refine wp_sd (a := off (cx s₀) (savOff + 24)) (by decide) (by rw [g₅.gpr, g₄.gpr, g₃.gpr, t0])
    (hal 24 (by decide)) (by rw [g₅.wr, g₄.wr, g₃.wr]; exact hin 24 (by decide)) fun s₆ g₆ => ?_
  refine wp_sd (a := off (cx s₀) (savOff + 32)) (by decide) (by rw [g₆.gpr, g₅.gpr, g₄.gpr, g₃.gpr, t0])
    (hal 32 (by decide)) (by rw [g₆.wr, g₅.wr, g₄.wr, g₃.wr]; exact hin 32 (by decide)) fun s₇ g₇ => ?_
  refine wp_sd (a := off (cx s₀) (savOff + 40)) (by decide)
    (by rw [g₇.gpr, g₆.gpr, g₅.gpr, g₄.gpr, g₃.gpr, t0])
    (hal 40 (by decide)) (by rw [g₇.wr, g₆.wr, g₅.wr, g₄.wr, g₃.wr]; exact hin 40 (by decide))
    fun s₈' g₈' => ?_
  refine wp_sd (a := off (cx s₀) (savOff + 48)) (by decide)
    (by rw [g₈'.gpr, g₇.gpr, g₆.gpr, g₅.gpr, g₄.gpr, g₃.gpr, t0])
    (hal 48 (by decide)) (by rw [g₈'.wr, g₇.wr, g₆.wr, g₅.wr, g₄.wr, g₃.wr]; exact hin 48 (by decide))
    fun s₈ g₈ => k s₈ ?_
  have eg : s₈.gpr = s₂.gpr := by rw [g₈.gpr, g₈'.gpr, g₇.gpr, g₆.gpr, g₅.gpr, g₄.gpr, g₃.gpr]
  have em : s₈.mem = (((((((s₂.mem.writeW (off (cx s₀) (savOff + 0)) (s₀.gpr .s7)).writeW
      (off (cx s₀) (savOff + 8)) (s₀.gpr .s8)).writeW (off (cx s₀) (savOff + 16)) (s₀.gpr .s9)).writeW
      (off (cx s₀) (savOff + 24)) (s₀.gpr .s10)).writeW (off (cx s₀) (savOff + 32)) (s₀.gpr .s11)).writeW
      (off (cx s₀) (savOff + 40)) (s₀.gpr .ra)).writeW (off (cx s₀) (savOff + 48)) (s₀.gpr .s6)) := by
    simp only [g₈.mem, g₈'.mem, g₇.mem, g₆.mem, g₅.mem, g₄.mem, g₃.mem, g₈'.gpr, g₇.gpr, g₆.gpr, g₅.gpr,
      g₄.gpr, g₃.gpr, g₂ _ (show Reg.s7 ≠ .t0 by decide), g₂ _ (show Reg.s8 ≠ .t0 by decide),
      g₂ _ (show Reg.s9 ≠ .t0 by decide), g₂ _ (show Reg.s10 ≠ .t0 by decide),
      g₂ _ (show Reg.s11 ≠ .t0 by decide), g₂ _ (show Reg.ra ≠ .t0 by decide),
      g₂ _ (show Reg.s6 ≠ .t0 by decide)]
  have hm₂ : s₂.mem = s₀.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨by rw [eg, t0], fun r hr => by rw [eg, g₂ r hr], by rw [g₈.sp, g₈'.sp, g₇.sp, g₆.sp, g₅.sp,
    g₄.sp, g₃.sp, u₂.sp, u₁.sp], by rw [g₈.rd, g₈'.rd, g₇.rd, g₆.rd, g₅.rd, g₄.rd, g₃.rd, u₂.rd, u₁.rd],
    by rw [g₈.wr, g₈'.wr, g₇.wr, g₆.wr, g₅.wr, g₄.wr, g₃.wr, w₂], ?_, ?_⟩
  · rw [em]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := decide) only [slot_other, Mem.readW_writeW_self64, Nat.add_zero]
  · rw [em, hm₂]
    have c : ∀ d, d + 8 ≤ 56 → (sub s₀ savOff 56).Contains (off (cx s₀) (savOff + d)) (64 / 8) :=
      fun d hd => contains_sub s₀ (by omega_using []) (by simp only [savOff]; omega_using [hd]) (by decide)
    exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 0 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 8 (by decide))).writeW (List.mem_singleton_self _) _
      (c 16 (by decide))).writeW (List.mem_singleton_self _) _ (c 24 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 32 (by decide))).writeW (List.mem_singleton_self _) _
      (c 40 (by decide))).writeW (List.mem_singleton_self _) _ (c 48 (by decide))


/-! ## The prologue -/

/-- After the prologue. -/
structure PostP (s₀ s : State) : Prop where
  inv : Inv s₀ s
  a0 : s.gpr .a0 = cx s₀
  fw : Frame [wR s₀] s₀.mem s.mem
  st : stateAt s.mem (cx s₀) = initState (K s₀) 0 (N s₀)
  zero : ∀ i < 16, s.mem (off (cx s₀) (zeroOff + i)) = 0
  lens : bytesAt s.mem (off (cx s₀) lenOff) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀)

open VG.Impl.ChaCha20.RISCV64.Stream (sigmaBytes) in
open VG.Proof.ChaCha20.RISCV64.Stream (sigmaBytes_lt sigmaBytes_length sigmaBytes_eq) in
theorem prologue_ok {s₀ : State} (hp : APre e s₀) :
    WP isa (.block (save ++ moves ++ setup)) s₀ (PostP s₀) := by
  rw [List.append_assoc]
  refine save_ok hp fun sa ha => ?_
  simp only [moves, mov, List.cons_append]
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ =>
    wp_mv fun sb u₆ => ?_
  have gb : ∀ r, r ≠ .s7 → r ≠ .s8 → r ≠ .s9 → r ≠ .s10 → r ≠ .s11 → r ≠ .s6 → sb.gpr r = sa.gpr r :=
    fun r h7 h8 h9 h10 h11 h6 => by
      rw [u₆.other r h6, u₅.other r h11, u₄.other r h10, u₃.other r h9, u₂.other r h8, u₁.other r h7]
  have rb : Regs s₀ sb :=
    ⟨by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.gpr, ha.gpr _ (by decide)],
      by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.gpr, u₁.other _ (by decide), ha.gpr _ (by decide)],
      by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
        u₂.other _ (by decide), u₁.other _ (by decide), ha.gpr _ (by decide)],
      by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide), ha.gpr _ (by decide)],
      by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide), ha.gpr _ (by decide)],
      by rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
        u₂.other _ (by decide), u₁.other _ (by decide), ha.gpr _ (by decide)]⟩
  have mb : sb.mem = sa.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rdb : sb.rd = s₀.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, ha.rd]
  have wrb : sb.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, ha.wr]
  have spb : sb.sp = s₀.sp := by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, ha.sp]
  have t0b : sb.gpr .t0 = cx s₀ := by
    rw [gb _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ha.t0]
  have a0b : sb.gpr .a0 = kp s₀ := by
    rw [gb _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ha.gpr _ (by decide)]
  have a1b : sb.gpr .a1 = np s₀ := by
    rw [gb _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ha.gpr _ (by decide)]
  have fb : Frame [wR s₀] s₀.mem sb.mem := by rw [mb]; exact fw_sub s₀ ha.frame (by decide)
  -- The constants.
  rw [List.nil_append]
  unfold setup
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (storeBytes_ok (tmp := .t1) (dst := .t0) (doff := 0) (bs := sigmaBytes) (by decide)
    sigmaBytes_lt (by decide) (fun i hi => by
      rw [t0b, wrb]; exact hp.in_w (by rw [sigmaBytes_length] at hi; omega_using [hi]))) fun sc hc => ?_
  have t0c : sc.gpr .t0 = cx s₀ := by rw [hc.gpr _ (by decide), t0b]
  have fc : Frame [sub s₀ 0 16] sb.mem sc.mem := by have := hc.frame; rwa [t0b, sigmaBytes_length] at this
  have σc : ∀ j < 16, sc.mem (off (cx s₀) j) = Proof.ChaCha20.sigma.getD j 0 := fun j hj => by
    have := hc.stored j (by rw [sigmaBytes_length]; exact hj)
    rw [t0b, Nat.zero_add] at this
    rw [this, sigmaBytes_eq j hj]
  -- The key.
  rw [WP.block_append_iff]
  refine WP.mono (copyBytes_ok (tmp := .t1) (src := .a0) (dst := .t0) (soff := 0) (doff := 16) (n := 32)
    (by decide) (by decide) (by decide) (by decide)
    (fun i hi => by
      rw [hc.gpr _ (by decide), a0b, hc.rd, rdb]
      exact ⟨kR s₀, List.mem_append_left _ hp.k_rd, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩)
    (fun i hi => by rw [t0c, hc.wr, wrb]; exact hp.in_w (by omega_using [hi]))
    (fun i hi hcon => by
      rw [t0c, hc.gpr _ (by decide), a0b] at hcon
      exact hp.k_w _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) (sub_work s₀ (k := 16) (n := 32)
        (by decide) _ hcon))) fun sd hd => ?_
  have t0d : sd.gpr .t0 = cx s₀ := by rw [hd.gpr _ (by decide), t0c]
  have fd : Frame [sub s₀ 16 32] sc.mem sd.mem := by have := hd.frame; rwa [t0c] at this
  have fwc : Frame [wR s₀] s₀.mem sc.mem := fb.trans (fw_sub s₀ fc (by decide))
  have kd : ∀ j < 32, sd.mem (off (cx s₀) (16 + j)) = (K s₀).getD j 0 := fun j hj => by
    have := hd.copied j hj
    rw [t0c, hc.gpr _ (by decide), a0b, Nat.zero_add] at this
    rw [this, byte_out s₀ fwc (R := kR s₀) hp.k_w (by show 32 ≤ 2 ^ 64; decide) hj]
    exact (Proof.ChaCha20.bytesAt_getD _ _ hj).symm
  -- The counter.
  rw [WP.block_append_iff]
  refine WP.mono (storeBytes_ok (tmp := .t1) (dst := .t0) (doff := 48) (bs := [0, 0, 0, 0]) (by decide)
    (by decide) (by decide) (fun i hi => by
      rw [t0d, hd.wr, hc.wr, wrb]; exact hp.in_w (by simp at hi; omega_using [hi]))) fun se he => ?_
  have t0e : se.gpr .t0 = cx s₀ := by rw [he.gpr _ (by decide), t0d]
  have fe : Frame [sub s₀ 48 4] sd.mem se.mem := by have := he.frame; rwa [t0d] at this
  have ce : ∀ j < 4, se.mem (off (cx s₀) (48 + j)) = (0 : Spec.ChaCha20.Word).extractLsb' (8 * j) 8 :=
    fun j hj => by
      have := he.stored j (by simpa using hj)
      rw [t0d] at this
      rw [this]
      rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> rfl
  -- The nonce.
  rw [WP.block_append_iff]
  refine WP.mono (copyBytes_ok (tmp := .t1) (src := .a1) (dst := .t0) (soff := 0) (doff := 52) (n := 12)
    (by decide) (by decide) (by decide) (by decide)
    (fun i hi => by
      rw [he.gpr _ (by decide), hd.gpr _ (by decide), hc.gpr _ (by decide), a1b, he.rd, hd.rd, hc.rd, rdb]
      exact ⟨nR s₀, List.mem_append_left _ hp.n_rd, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩)
    (fun i hi => by rw [t0e, he.wr, hd.wr, hc.wr, wrb]; exact hp.in_w (by omega_using [hi]))
    (fun i hi hcon => by
      rw [t0e, he.gpr _ (by decide), hd.gpr _ (by decide), hc.gpr _ (by decide), a1b] at hcon
      exact hp.n_w _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) (sub_work s₀ (k := 52) (n := 12)
        (by decide) _ hcon))) fun sf hf => ?_
  have t0f : sf.gpr .t0 = cx s₀ := by rw [hf.gpr _ (by decide), t0e]
  have ff : Frame [sub s₀ 52 12] se.mem sf.mem := by have := hf.frame; rwa [t0e] at this
  have fwe : Frame [wR s₀] s₀.mem se.mem :=
    (fwc.trans (fw_sub s₀ fd (by decide))).trans (fw_sub s₀ fe (by decide))
  have nf : ∀ j < 12, sf.mem (off (cx s₀) (52 + j)) = (N s₀).getD j 0 := fun j hj => by
    have := hf.copied j hj
    rw [t0e, he.gpr _ (by decide), hd.gpr _ (by decide), hc.gpr _ (by decide), a1b, Nat.zero_add] at this
    rw [this, byte_out s₀ fwe (R := nR s₀) hp.n_w (by show 12 ≤ 2 ^ 64; decide) hj]
    exact (Proof.ChaCha20.bytesAt_getD _ _ hj).symm
  -- The padding, the lengths block and the context into `a0`.
  have wrf : sf.wr = s₀.wr := by rw [hf.wr, he.wr, hd.wr, hc.wr, wrb]
  have hin : ∀ d, d + 8 ≤ 32 → InRegions sf.wr (off (cx s₀) (zeroOff + d)) 8 := fun d hd => by
    rw [wrf]; exact hp.in_w (by simp only [zeroOff]; omega_using [hd])
  refine wp_li (imm := 0) (by decide) fun sg ug => ?_
  have t0g : sg.gpr .t0 = cx s₀ := by rw [ug.other _ (by decide), t0f]
  refine wp_sd (a := off (cx s₀) zeroOff) (by decide) (by rw [t0g]) (cx_al s₀ (by decide))
    (by rw [ug.wr]; simpa using hin 0 (by decide)) fun sh gh => ?_
  refine wp_sd (a := off (cx s₀) (zeroOff + 8)) (by decide) (by rw [gh.gpr, t0g]) (cx_al s₀ (by decide))
    (by rw [gh.wr, ug.wr]; exact hin 8 (by decide)) fun si gi => ?_
  refine wp_sd (a := off (cx s₀) lenOff) (by decide) (by rw [gi.gpr, gh.gpr, t0g]) (cx_al s₀ (by decide))
    (by rw [gi.wr, gh.wr, ug.wr]; exact hin 16 (by decide)) fun sj gj => ?_
  refine wp_sd (a := off (cx s₀) (lenOff + 8)) (by decide) (by rw [gj.gpr, gi.gpr, gh.gpr, t0g])
    (cx_al s₀ (by decide)) (by rw [gj.wr, gi.wr, gh.wr, ug.wr]; exact hin 24 (by decide)) fun sk gk₀ => ?_
  refine wp_mv fun sl ul => WP.block_nil ?_
  -- What the registers hold.
  have gk : ∀ r, r ≠ .t1 → sk.gpr r = sb.gpr r := fun r hr => by
    rw [gk₀.gpr, gj.gpr, gi.gpr, gh.gpr, ug.other r hr, hf.gpr r hr, he.gpr r hr, hd.gpr r hr, hc.gpr r hr]
  have gl : ∀ r, r ≠ .t1 → r ≠ .a0 → sl.gpr r = sb.gpr r := fun r h1 h0 => by rw [ul.other r h0, gk r h1]
  have v1 : sg.gpr .t1 = 0 := ug.gpr
  have v8 : sg.gpr .s8 = s₀.gpr .a3 := by rw [ug.other _ (by decide), hf.gpr _ (by decide),
    he.gpr _ (by decide), hd.gpr _ (by decide), hc.gpr _ (by decide), rb.s8]
  have v10 : sg.gpr .s10 = s₀.gpr .a5 := by rw [ug.other _ (by decide), hf.gpr _ (by decide),
    he.gpr _ (by decide), hd.gpr _ (by decide), hc.gpr _ (by decide), rb.s10]
  have ml : sl.mem = (((sf.mem.writeW (off (cx s₀) zeroOff) (0 : BitVec 64)).writeW (off (cx s₀) (zeroOff + 8))
      (0 : BitVec 64)).writeW
      (off (cx s₀) lenOff) (s₀.gpr .a3)).writeW (off (cx s₀) (lenOff + 8)) (s₀.gpr .a5) := by
    rw [ul.mem, gk₀.mem, gj.mem, gi.mem, gh.mem, ug.mem, gj.gpr, gi.gpr, gh.gpr, v1, v8, v10]
  have fk : Frame [sub s₀ zeroOff 32] sf.mem sl.mem := by
    rw [ml]
    have c : ∀ d, d + 8 ≤ 32 → (sub s₀ zeroOff 32).Contains (off (cx s₀) (zeroOff + d)) (64 / 8) :=
      fun d hd => contains_sub s₀ (by omega_using []) (by simp only [zeroOff]; omega_using [hd]) (by decide)
    exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by simpa using c 0 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 8 (by decide))).writeW (List.mem_singleton_self _) _
      (c 16 (by decide))).writeW (List.mem_singleton_self _) _ (c 24 (by decide))
  have fwl : Frame [wR s₀] s₀.mem sl.mem :=
    (fwe.trans (fw_sub s₀ ff (by decide))).trans (fw_sub s₀ fk (by decide))
  have r0 : sl.mem.readW (off (cx s₀) zeroOff) 64 = 0 := by
    rw [ml]; simp (disch := decide) only [slot_other, Mem.readW_writeW_self64]
  have r1 : sl.mem.readW (off (cx s₀) (zeroOff + 8)) 64 = 0 := by
    rw [ml]; simp (disch := decide) only [slot_other, Mem.readW_writeW_self64]
  have r2 : sl.mem.readW (off (cx s₀) lenOff) 64 = s₀.gpr .a3 := by
    rw [ml]; simp (disch := decide) only [slot_other, Mem.readW_writeW_self64]
  have r3 : sl.mem.readW (off (cx s₀) (lenOff + 8)) 64 = s₀.gpr .a5 := by
    rw [ml, Mem.readW_writeW_self64]
  -- The bytes of the ChaCha20 state, from the part that wrote each.
  have early : ∀ i < 64, sl.mem (off (cx s₀) i) = sf.mem (off (cx s₀) i) := fun i hi =>
    byte_sub s₀ fk (by simp only [zeroOff]; omega_using [hi]) (by decide) (by omega_using [hi])
  have hst : stateAt sl.mem (cx s₀) = initState (K s₀) 0 (N s₀) := by
    refine stateAt_init (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_)
    · rw [early i (by omega_using [hi]), byte_sub s₀ ff (by omega_using [hi]) (by decide) (by omega_using [hi]),
        byte_sub s₀ fe (by omega_using [hi]) (by decide) (by omega_using [hi]), byte_sub s₀ fd (by omega_using [hi]) (by decide) (by omega_using [hi]),
        σc i hi]
    · rw [early _ (by omega_using [hi]), byte_sub s₀ ff (by omega_using [hi]) (by decide) (by omega_using [hi]),
        byte_sub s₀ fe (by omega_using [hi]) (by decide) (by omega_using [hi]), kd i hi]
    · rw [early _ (by omega_using [hi]), byte_sub s₀ ff (by omega_using [hi]) (by decide) (by omega_using [hi]), ce i hi]
    · rw [early _ (by omega_using [hi]), nf i hi]
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun r hr => ?_, ?_, ?_, ?_, ?_, fwl.mono (by simp)⟩, ?_, fwl, hst, ?_, ?_⟩
  · rw [gl _ (by decide) (by decide), rb.s7]
  · rw [gl _ (by decide) (by decide), rb.s8]
  · rw [gl _ (by decide) (by decide), rb.s9]
  · rw [gl _ (by decide) (by decide), rb.s10]
  · rw [gl _ (by decide) (by decide), rb.s11]
  · rw [gl _ (by decide) (by decide), rb.s6]
  · have h : r ≠ .t1 ∧ r ≠ .a0 ∧ r ≠ .s7 ∧ r ≠ .s8 ∧ r ≠ .s9 ∧ r ≠ .s10 ∧ r ≠ .s11 ∧ r ≠ .s6 ∧
        r ≠ .t0 := by
      revert r; decide
    rw [gl r h.1 h.2.1, gb r h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1,
      ha.gpr r h.2.2.2.2.2.2.2.2]
  · rw [ul.sp, gk₀.sp, gj.sp, gi.sp, gh.sp, ug.sp, hf.sp, he.sp, hd.sp, hc.sp, spb]
  · rw [ul.rd, gk₀.rd, gj.rd, gi.rd, gh.rd, ug.rd, hf.rd, he.rd, hd.rd, hc.rd, rdb]
  · rw [ul.wr, gk₀.wr, gj.wr, gi.wr, gh.wr, ug.wr, wrf]
  · refine sv_sub s₀ (sv_sub s₀ (sv_sub s₀ (sv_sub s₀ (sv_sub s₀ (by rw [mb]; exact ha.saved) fc (by decide))
      fd (by decide)) fe (by decide)) ff (by decide)) fk (by decide)
  · rw [ul.gpr, gk _ (by decide), t0b]
  · intro i hi
    rcases (by omega_using [] : i < 8 ∨ 8 ≤ i) with h | h
    · rw [← off_off (cx s₀) zeroOff i, ← Proof.ChaCha20.readW64_byte sl.mem (off (cx s₀) zeroOff) h, r0]; simp
    · rw [show zeroOff + i = zeroOff + 8 + (i - 8) by omega_using [h], ← off_off (cx s₀) (zeroOff + 8) (i - 8),
        ← Proof.ChaCha20.readW64_byte sl.mem (off (cx s₀) (zeroOff + 8)) (show i - 8 < 8 by omega_using [hi]), r1]; simp
  · rw [show (16 : Nat) = 8 + 8 from rfl, Proof.Poly1305.bytesAt_add, Proof.Poly1305.bytesAt_leBytes_64,
      Proof.Poly1305.bytesAt_leBytes_64, r2]
    have r3' : sl.mem.readW (off (cx s₀) lenOff + BitVec.ofNat 64 8) 64 = s₀.gpr .a5 := by
      rw [Offset.add_add (cx s₀) lenOff 8]; exact r3
    rw [r3']

end VG.Proof.ChaCha20Poly1305.RISCV64

end

end


/-!
# ChaCha20-Poly1305 on RISC-V: the parts with calls

The one-time key (`keyGen`), the Poly1305 state for it (`polyInit`), the MAC
of the additional data (`macAad`), the encryption (`crypt`) and the MAC of
the ciphertext and the tag (`macData`): each from the state it starts in, to
what it leaves and the regions it writes (`Step`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Align VG.Impl.ChaCha20Poly1305.RISCV64
open VG.Impl.ChaCha20.RISCV64.Xor (mov)
open VG.Spec.Poly1305 (bytesAt leBytes mac Buffered Repr)
open VG.Spec.ChaCha20 (stateAt initState)
open VG.Spec.ChaCha20Poly1305 (pad16)

variable {e : Bool}

/-! ## Regions and covers -/

theorem covers_right {rs rd wr : List Region} (h : Covers rs wr) : Covers rs (rd ++ wr) := fun a n hi =>
  let ⟨r, hr, hc⟩ := h a n hi; ⟨r, List.mem_append_right _ hr, hc⟩

/-- Parts of the context are in the working space. -/
theorem covers_ctx {s₀ s : State} (hp : APre e s₀) (hwr : s.wr = s₀.wr) (rs : List Region)
    (h : ∀ r ∈ rs, ∃ k, r.base = off (cx s₀) k ∧ k + r.len ≤ 616) : Covers rs s.wr := by
  refine Covers.of_sub fun r hr => ?_
  obtain ⟨k, hb, hk⟩ := h r hr
  have := pad_lt' s₀
  exact ⟨wR s₀, by rw [hwr]; exact hp.w_wr, pad (wk s₀) + k, by rw [hb, cx_off], by show _ ≤ 624; omega_using [hk, this]⟩

theorem cx_zero (s₀ : State) : cx s₀ = off (cx s₀) 0 := (off_zero _).symm

/-- The context is 4-byte aligned, and so is it plus a multiple of 8. -/
theorem cx_al4 (s₀ : State) : (cx s₀).toNat % 4 = 0 := by
  have := cx_al s₀ (d := 0) (by decide); rw [off_zero] at this; omega_using [this]

theorem off_al4 (s₀ : State) {d : Nat} (hd : d % 8 = 0) : (off (cx s₀) d).toNat % 4 = 0 := by
  have := cx_al s₀ hd; omega_using [this]

/-- `ctx[0, 64)` as a part. -/
theorem st_sub (s₀ : State) : (⟨cx s₀, 64⟩ : Region) = sub s₀ 0 64 := by rw [sub, ← cx_zero]

/-! ## The one-time key -/

/-- The first `n ≤ 64` bytes of a ChaCha20 state in memory. -/
theorem bytesAt_serialize (m : Mem) (p : Addr) {n : Nat} (hn : n ≤ 64) :
    bytesAt m p n = (Spec.ChaCha20.serialize (stateAt m p)).take n := by
  apply List.ext_getElem
  · simp [bytesAt, VG.Proof.ChaCha20.length_serialize]; omega_using [hn]
  · intro i h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    have e := VG.Proof.ChaCha20.serialize_stateAt m p (i := i) (by omega_using [hn, h₁])
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
      rw [VG.Proof.ChaCha20.length_serialize]; omega_using [hn, h₁]), Option.getD_some] at e
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_take, e]

theorem keyGen_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s) (ha : s.gpr .a0 = cx s₀)
    (hst : stateAt s.mem (cx s₀) = initState (K s₀) 0 (N s₀)) :
    WP isa keyGen s fun s' => Step [sub s₀ 64 256] s s' ∧ s'.gpr .a0 = cx s₀ ∧
      bytesAt s'.mem (off (cx s₀) 64) 32 = otk s₀ := by
  refine WP.seq (wp_addi (imm := bufOff) (by decide) fun s₁ u₁ => WP.block_nil ?_)
  have a0₁ : s₁.gpr .a0 = cx s₀ := by rw [u₁.other _ (by decide), ha]
  refine block_call a0₁ (B := off (cx s₀) 64) (hSa := cx_al4 s₀) (hBa := off_al4 s₀ (by decide)) (by rw [u₁.gpr, ha]; rfl)
    (Offset.disjoint_base (cx s₀) (d := 64) (n := 256) (k := 64) (by decide) (by decide)) ?_ ?_ fun s' k hb => ?_
  · refine covers_right (covers_ctx hp (by rw [u₁.wr, h.wr]) _ fun r hr => ?_)
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [⟨0, cx_zero s₀, by show 0 + 64 ≤ 616; decide⟩, ⟨64, rfl, by show 64 + 256 ≤ 616; decide⟩]
  · refine covers_ctx hp (by rw [u₁.wr, h.wr]) _ fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨64, rfl, by show 64 + 256 ≤ 616; decide⟩
  refine ⟨(Step.upd _ u₁).trans k.step, by rw [k.a0, a0₁], ?_⟩
  rw [bytesAt_serialize _ _ (by decide), hb, u₁.mem, hst]
  rfl

/-! ## The Poly1305 state -/

theorem polyInit_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s) (ha : s.gpr .a0 = cx s₀)
    (hk : bytesAt s.mem (off (cx s₀) 64) 32 = otk s₀) :
    WP isa polyInit s fun s' => Step [sub s₀ polyOff 128] s s' ∧ s'.gpr .a0 = ps s₀ ∧
      Repr s'.mem (ps s₀) (otk s₀) [] := by
  refine WP.seq (wp_addi (imm := bufOff) (by decide) fun s₁ u₁ =>
    wp_addi (imm := polyOff) (by decide) fun s₂ u₂ => WP.block_nil ?_)
  have hw : s₂.wr = s₀.wr := by rw [u₂.wr, u₁.wr, h.wr]
  refine init_call (P := ps s₀) (K := off (cx s₀) 64) (by rw [u₂.gpr, u₁.other _ (by decide), ha])
    (by rw [u₂.other _ (by decide), u₁.gpr, ha]; rfl) (sub_disj s₀ (a := polyOff) (n := 128) (b := 64) (m := 32) (by decide) (by decide) (by decide))
    ?_ ?_ fun s' k hr => ?_
  · refine covers_right (covers_ctx hp hw _ fun r hr => ?_)
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [⟨64, rfl, by show 64 + 32 ≤ 616; decide⟩, ⟨polyOff, rfl, by show polyOff + 128 ≤ 616; decide⟩]
  · refine covers_ctx hp hw _ fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨polyOff, rfl, by show polyOff + 128 ≤ 616; decide⟩
  refine ⟨((Step.upd _ u₁).trans (Step.upd _ u₂)).trans k.step,
    by rw [k.a0, u₂.gpr, u₁.other _ (by decide), ha], ?_⟩
  rw [u₂.mem, u₁.mem, hk] at hr
  exact hr


/-! ## Padding -/

theorem covers_one {r : Region} {rs : List Region} (h : r ∈ rs) : Covers [r] rs := fun a n ⟨r', hr', hc⟩ => by
  simp only [List.mem_singleton] at hr'; subst hr'; exact ⟨r', h, hc⟩

/-- `-x mod 16`, as `padArgs` computes it. -/
theorem padN (x : BitVec 64) :
    (BitVec.ofNat 64 0 - x) &&& BitVec.ofInt 64 15 = BitVec.ofNat 64 ((16 - x.toNat % 16) % 16) := by
  rw [Proof.Poly1305.RISCV64.and15]
  congr 1
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt
  omega_using []

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- The zeros of the context are the padding of `x`. -/
theorem zeros_pad {m : Mem} {p : Addr} (x : List Byte) (hz : ∀ i < 16, m (p + BitVec.ofNat 64 i) = 0) :
    bytesAt m p ((16 - x.length % 16) % 16) = pad16 x := by
  unfold pad16
  split
  · rename_i h; rw [h]; rfl
  · rename_i h
    rw [Nat.mod_eq_of_lt (by omega_using [h])]
    apply List.ext_getElem (by simp [Proof.Poly1305.length_bytesAt])
    intro i h₁ h₂
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
    exact hz i (by simp [bytesAt] at h₁; omega_using [h₁])

theorem zeros_of {s₀ : State} {m : Mem} (hz : ∀ i < 16, m (off (cx s₀) (zeroOff + i)) = 0) :
    ∀ i < 16, m (off (cx s₀) zeroOff + BitVec.ofNat 64 i) = 0 := fun i hi => by
  rw [Offset.add_add]; exact hz i hi

theorem ps_add (s₀ : State) (d : Nat) : ps s₀ + BitVec.ofNat 64 d = off (cx s₀) (polyOff + d) :=
  Offset.add_add _ _ _

theorem a3_eq (s₀ : State) : s₀.gpr .a3 = BitVec.ofNat 64 (AL s₀) := by simp

theorem a5_eq (s₀ : State) : s₀.gpr .a5 = BitVec.ofNat 64 (L s₀) := by simp

/-! ## The MAC of the additional data -/

theorem macAad_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s) (ha : s.gpr .a0 = ps s₀)
    (hb : Buffered s.mem (ps s₀) (otk s₀) [])
    (hz : ∀ i < 16, s.mem (off (cx s₀) (zeroOff + i)) = 0) :
    WP isa macAad s fun s' => Step [sub s₀ polyOff 128] s s' ∧ s'.gpr .a0 = ps s₀ ∧
      Buffered s'.mem (ps s₀) (otk s₀)
        (bytesAt s.mem (ad s₀) (AL s₀) ++ pad16 (bytesAt s.mem (ad s₀) (AL s₀))) := by
  unfold macAad update padArgs
  simp only [mov]
  refine WP.seq (wp_li (imm := 0) (by decide) fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ =>
    WP.block_nil ?_)
  have w₃ : s₃.wr = s₀.wr := by rw [u₃.wr, u₂.wr, u₁.wr, h.wr]
  have r₃ : s₃.rd = s₀.rd := by rw [u₃.rd, u₂.rd, u₁.rd, h.rd]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have hP : (sub s₀ polyOff 128).Disjoint (aR s₀) := (APre.w_sub (s₀ := s₀) hp.a_w (k := polyOff) (n := 128) (by decide)).symm
  have cP : Covers [sub s₀ polyOff 128] s₃.wr := covers_ctx hp w₃ _ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨polyOff, rfl, by show polyOff + 128 ≤ 616; decide⟩
  refine WP.seq (update_call (P := ps s₀) (hPa := cx_al s₀ (by decide)) (D := ad s₀) (c := BitVec.ofNat 64 0) (n := AL s₀)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), ha])
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr])
    (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), h.regs.s7])
    (by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.regs.s8, a3_eq])
    (s₀.gpr .a3).isLt hP
    (Covers.append (covers_one (r := aR s₀) (rs := s₃.rd) (by rw [r₃]; exact hp.a_rd)) cP) cP
    fun s₄ k₄ hb₄ => ?_)
  refine WP.seq (wp_mv fun s₅ u₅ => wp_li (imm := 0) (by decide) fun s₆ u₆ => wp_sub fun s₇ u₇ =>
    wp_andi (by decide) fun s₈ u₈ => wp_addi (imm := zeroOff - polyOff) (by decide) fun s₉ u₉ =>
    WP.block_nil ?_)
  have hnl : (16 - AL s₀ % 16) % 16 < 16 := Nat.mod_lt _ (by decide)
  have w₉ : s₉.wr = s₀.wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, k₄.wr, w₃]
  have r₉ : s₉.rd = s₀.rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, k₄.rd, r₃]
  have a0₈ : s₈.gpr .a0 = ps s₀ := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), k₄.a0,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), ha]
  have s8₄ : s₄.gpr .s8 = s₀.gpr .a3 := by
    rw [k₄.cs _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      h.regs.s8]
  have cP' : Covers [sub s₀ polyOff 128] s₉.wr := covers_ctx hp w₉ _ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨polyOff, rfl, by show polyOff + 128 ≤ 616; decide⟩
  refine update_call (P := ps s₀) (hPa := cx_al s₀ (by decide)) (D := off (cx s₀) zeroOff) (c := s₀.gpr .a3)
    (n := (16 - AL s₀ % 16) % 16) (by rw [u₉.other _ (by decide), a0₈])
    (by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.gpr, s8₄])
    (by rw [u₉.gpr, a0₈, ps_add]; rfl)
    (by rw [u₉.other _ (by decide), u₈.gpr, u₇.gpr, u₆.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
      s8₄, padN])
    (by omega_using []) (sub_disj s₀ (a := polyOff) (n := 128) (b := zeroOff) (m := (16 - AL s₀ % 16) % 16)
      (by simp only [polyOff, zeroOff]; omega_using []) (by decide) (by simp only [zeroOff]; omega_using []))
    (covers_right (covers_ctx hp w₉ _ fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨zeroOff, rfl, by show zeroOff + _ ≤ 616; simp only [zeroOff]; omega_using []⟩
      · exact ⟨polyOff, rfl, by show polyOff + 128 ≤ 616; decide⟩)) cP' fun s' k' hb' => ?_
  refine ⟨?_, by rw [k'.a0, u₉.other _ (by decide), a0₈], ?_⟩
  · refine ((((((((Step.upd _ u₁).trans (Step.upd _ u₂)).trans (Step.upd _ u₃)).trans k₄.step).trans
      (Step.upd _ u₅)).trans (Step.upd _ u₆)).trans (Step.upd _ u₇)).trans (Step.upd _ u₈)).trans
      ((Step.upd _ u₉).trans k'.step)
  · have hA : bytesAt s₃.mem (ad s₀) (AL s₀) = bytesAt s.mem (ad s₀) (AL s₀) := by rw [m₃]
    have b₄ := hb₄ (otk s₀) [] (by rw [m₃]; exact hb) (by simp)
    rw [List.nil_append, hA] at b₄
    have b' := hb' (otk s₀) _ (by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem]; exact b₄)
      (by rw [Proof.Poly1305.length_bytesAt])
    have hz₄ : ∀ i < 16, s₉.mem (off (cx s₀) zeroOff + BitVec.ofNat 64 i) = 0 := zeros_of fun i hi => by
      rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem,
        byte_sub s₀ (k := polyOff) (n := 128) k₄.frame (by simp only [polyOff, zeroOff]; omega_using []) (by decide)
          (by simp only [zeroOff]; omega_using [hi]), m₃]
      exact hz i hi
    have hp16 := zeros_pad (bytesAt s.mem (ad s₀) (AL s₀)) hz₄
    rw [Proof.Poly1305.length_bytesAt] at hp16
    rw [hp16] at b'
    exact b'


/-! ## The encryption -/

/-- The ChaCha20 state for counter 0, with the low byte of the counter set to 1. -/
theorem stateAt_ctr1 {m : Mem} {p : Addr} {key nonce : List Byte}
    (h : stateAt m p = initState key 0 nonce) :
    stateAt (m.writeW (p + BitVec.ofNat 64 48) (BitVec.ofNat 8 1)) p = initState key 1 nonce := by
  have hc : initState key 1 nonce = Proof.ChaCha20.ctr (initState key 0 nonce) 1 := by
    rw [ctr_initState]; rfl
  have h12 : m.readW (p + BitVec.ofNat 64 48) 32 = 0 := by
    have := congrArg (·[12]) h
    simpa [stateAt, initState] using this
  rw [hc, ← h]
  apply Vector.ext; intro i hi
  simp only [stateAt, Proof.ChaCha20.ctr, Vector.getElem_set, Vector.getElem_ofFn]
  split
  · rename_i e; subst e
    show (m.writeW _ _).readW (p + BitVec.ofNat 64 48) 32 = m.readW (p + BitVec.ofNat 64 48) 32 + _
    rw [h12]
    refine Proof.ChaCha20.word_ext fun j hj => ?_
    rw [← Mem.readW_byte _ _ hj, WriteBytes.writeW8_apply, Offset.add_add]
    rcases (by omega_using [hj] : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · simp
    all_goals
      split
      · exact absurd ‹_› (Offset.add_ofNat_ne p (by decide) (by decide) (by decide))
      · rw [← Offset.add_add p 48, Mem.readW_byte m (p + BitVec.ofNat 64 48) (by decide), h12]
        decide
  · rename_i e
    exact Mem.readW_writeW_sep (Offset.sep p (by omega_using [e]) (by omega_using [hi]) (by decide)) (by decide)

theorem fit_d' (s₀ : State) : L s₀ < 2 ^ 64 := (s₀.gpr .a5).isLt

theorem crypt_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s) (ha : s.gpr .a0 = ps s₀)
    (hst : stateAt s.mem (cx s₀) = initState (K s₀) 0 (N s₀)) :
    WP isa crypt s fun s' => Step [sub s₀ 0 64, oR s₀, sub s₀ 64 320] s s' ∧ s'.gpr .a0 = ps s₀ ∧
      bytesAt s'.mem (op s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀)) := by
  unfold crypt
  simp only [mov]
  refine WP.seq (wp_subi (imm := polyOff) (by decide) fun s₁ u₁ => wp_li (imm := 1) (by decide) fun s₂ u₂ => ?_)
  have a0₁ : s₁.gpr .a0 = cx s₀ := by rw [u₁.gpr, ha, ps, BitVec.add_sub_cancel]
  refine wp_sb (a := off (cx s₀) 48) (by decide) (by rw [u₂.other _ (by decide), a0₁])
    (by rw [u₂.wr, u₁.wr, h.wr]; exact hp.in_w (by decide)) fun s₃ g₃ => ?_
  refine wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ => wp_addi (imm := bufOff) (by decide) fun s₅' u₅' =>
    wp_mv fun s₆ u₆ => WP.block_nil ?_
  have m₆ : s₆.mem = s.mem.writeW (off (cx s₀) 48) (BitVec.ofNat 8 1) := by
    rw [u₆.mem, u₅'.mem, u₅.mem, u₄.mem, g₃.mem, u₂.gpr, VG.RISCV64.Bytes.setWidth_ofNat_byte, u₂.mem, u₁.mem]
  have f₆ : Frame [sub s₀ 0 64] s.mem s₆.mem := by
    rw [m₆]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (contains_sub s₀ (w := 8 / 8) (by decide) (by decide) (by decide))
  have a0₆ : s₆.gpr .a0 = cx s₀ := by
    rw [u₆.other _ (by decide), u₅'.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), g₃.gpr,
      u₂.other _ (by decide), a0₁]
  have g₆ : ∀ r, r ≠ .a0 → r ≠ .t0 → r ≠ .a1 → r ≠ .a2 → r ≠ .a3 → r ≠ .a4 → s₆.gpr r = s.gpr r :=
    fun r h0 ht h1 h2 h3 h4 => by
      rw [u₆.other r h4, u₅'.other r h3, u₅.other r h2, u₄.other r h1, g₃.gpr, u₂.other r ht, u₁.other r h0]
  have w₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅'.wr, u₅.wr, u₄.wr, g₃.wr, u₂.wr, u₁.wr, h.wr]
  have r₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅'.rd, u₅.rd, u₄.rd, g₃.rd, u₂.rd, u₁.rd, h.rd]
  have hSX : (⟨cx s₀, 64⟩ : Region).Disjoint (dR s₀) := by
    rw [st_sub]; exact (APre.w_sub (s₀ := s₀) hp.d_w (k := 0) (n := 64) (by decide)).symm
  have hSD : (⟨cx s₀, 64⟩ : Region).Disjoint (oR s₀) := by
    rw [st_sub]; exact (APre.w_sub (s₀ := s₀) hp.o_w (k := 0) (n := 64) (by decide)).symm
  have hcov : Covers [⟨cx s₀, 64⟩, oR s₀, sub s₀ 64 320] s₆.wr := by
    refine Covers.of_sub fun r hr => ?_
    have := pad_lt' s₀
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨wR s₀, by rw [w₆]; exact hp.w_wr, pad (wk s₀), rfl, by show pad (wk s₀) + 64 ≤ 624; omega_using [this]⟩
    · exact ⟨oR s₀, by rw [w₆]; exact hp.o_wr, 0, (BitVec.add_zero _).symm, by simp⟩
    · exact ⟨wR s₀, by rw [w₆]; exact hp.w_wr, pad (wk s₀) + 64, cx_off s₀ 64,
        by show pad (wk s₀) + 64 + 320 ≤ 624; omega_using [this]⟩
  have hc : Covers ([dR s₀] ++ [⟨cx s₀, 64⟩, oR s₀, sub s₀ 64 320]) (s₆.rd ++ s₆.wr) := by
    intro a m ⟨r, hr, hcr⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact ⟨dR s₀, by rw [r₆, w₆]; exact hp.d_in, hcr⟩
    · exact covers_right hcov a m ⟨r, by simpa using hr, hcr⟩
  have hXD : op s₀ = dp s₀ ∨ (dR s₀).Disjoint (oR s₀) := by
    rcases hp.alias with h' | ⟨-, h'⟩
    · exact .inl h'
    · exact .inr h'
  refine WP.seq (xor_call_to (S := cx s₀) (X := dp s₀) (D := op s₀) (n := L s₀) (B := off (cx s₀) 64)
    (hSa := cx_al4 s₀) (hBa := off_al4 s₀ (by decide)) a0₆
    (by rw [u₆.other _ (by decide), u₅'.other _ (by decide), u₅.other _ (by decide), u₄.gpr, g₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide), h.regs.s9])
    (by rw [u₆.other _ (by decide), u₅'.other _ (by decide), u₅.gpr, u₄.other _ (by decide), g₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide), h.regs.s10, a5_eq])
    (by rw [u₆.other _ (by decide), u₅'.gpr, u₅.other _ (by decide), u₄.other _ (by decide), g₃.gpr,
      u₂.other _ (by decide), a0₁]; rfl)
    (by rw [u₆.gpr, u₅'.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), g₃.gpr,
      u₂.other _ (by decide), u₁.other _ (by decide), h.regs.s6])
    (fit_d' s₀) hSX hSD (Offset.base_disjoint (cx s₀) (k := 64) (e := 64) (n := 320) (by decide) (by decide))
    (APre.w_sub (s₀ := s₀) hp.d_w (k := 64) (n := 320) (by decide))
    (APre.w_sub (s₀ := s₀) hp.o_w (k := 64) (n := 320) (by decide)) hXD hp.fit_d hp.fit_o
    hc hcov fun s₇ k₇ hx => ?_)
  refine wp_addi (imm := polyOff) (by decide) fun s₈ u₈ => WP.block_nil ?_
  refine ⟨?_, by rw [u₈.gpr, k₇.a0, a0₆], ?_⟩
  · have st₆ : Step [sub s₀ 0 64, oR s₀, sub s₀ 64 320] s s₆ :=
      ⟨fun r hr => g₆ r (by revert r; decide) (by revert r; decide) (by revert r; decide)
        (by revert r; decide) (by revert r; decide) (by revert r; decide),
        by rw [u₆.sp, u₅'.sp, u₅.sp, u₄.sp, g₃.sp, u₂.sp, u₁.sp], by rw [r₆, h.rd],
        by rw [w₆, h.wr], f₆.mono (by simp)⟩
    refine (st₆.trans ?_).trans (Step.upd _ u₈)
    have := k₇.step
    rw [st_sub] at this
    exact this
  · have hd : bytesAt s₆.mem (dp s₀) (L s₀) = bytesAt s.mem (dp s₀) (L s₀) :=
      bytesAt_frame f₆ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact APre.w_sub (s₀ := s₀) hp.d_w (k := 0) (n := 64) (by decide)) (Nat.le_of_lt (fit_d' s₀))
    have hs : stateAt s₆.mem (cx s₀) = initState (K s₀) 1 (N s₀) := by rw [m₆]; exact stateAt_ctr1 hst
    rw [u₈.mem]
    show Spec.ChaCha20.bytesAt _ _ _ = _
    rw [hx, hs, encrypt_eq, show (bytesAt s.mem (dp s₀) (L s₀)).length = L s₀ from
      Proof.Poly1305.length_bytesAt _ _ _]
    exact congrArg (fun x => List.zipWith _ x _) hd


/-! ## The MAC of the ciphertext and the tag -/

/-- `round16` leaves a multiple of 16. -/
theorem round16_mod (x : BitVec 64) : ((x + BitVec.ofNat 64 15) &&& BitVec.ofInt 64 (-16)).toNat % 16 = 0 := by
  rw [BitVec.toNat_and, show (16 : Nat) = 2 ^ 4 from rfl, Nat.and_mod_two_pow,
    show (BitVec.ofInt 64 (-16)).toNat % 2 ^ 4 = 0 from rfl, Nat.and_zero]

theorem add_mod16 (a b : BitVec 64) : (a + b).toNat % 16 = (a.toNat + b.toNat) % 16 := by
  rw [BitVec.toNat_add, Nat.mod_mod_of_dvd _ (by decide : 16 ∣ 2 ^ 64)]

theorem length_pad16 (x : List Byte) : (x ++ pad16 x).length % 16 = 0 := by
  unfold pad16; split <;> simp <;> omega_arith

theorem covers_wr2 {r₁ r₂ : Region} {rd wr : List Region} (h₁ : r₁ ∈ rd ++ wr) (h₂ : Covers [r₂] wr) :
    Covers ([r₁] ++ [r₂]) (rd ++ wr) := fun a n ⟨r, hr, hc⟩ => by
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨r, h₁, hc⟩
  · obtain ⟨r', hr', hc'⟩ := h₂ a n ⟨r, List.mem_singleton_self _, hc⟩
    exact ⟨r', List.mem_append_right _ hr', hc'⟩

theorem Step.upd' {rs : List Region} {s s₁ s₂ : State} (h : Step rs s s₁) {d : Reg} {v : BitVec 64}
    (u : Upd s₁ s₂ d v) (hd : d ∉ preserved := by decide) : Step rs s s₂ :=
  h.trans (Step.upd rs u hd)

theorem length_leBytes (n x : Nat) : (leBytes n x).length = n := by simp [leBytes]

/-- The invariant survives an instruction writing a temporary register. -/
theorem Inv.upd {s₀ s s' : State} (h : Inv s₀ s) {d : Reg} {v : BitVec 64} (u : Upd s s' d v)
    (hd : d ∉ preserved := by decide) : Inv s₀ s' :=
  h.step (Step.upd [] u hd) (by simp) (by simp)

/-- The data, the padding and the lengths after `M`, and the tag at `O`, which
`out` puts in `a2`. -/
theorem macData_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s) (ha : s.gpr .a0 = ps s₀)
    {M : List Byte} (hb : Buffered s.mem (ps s₀) (otk s₀) M) (hM : M.length % 16 = 0)
    (hz : ∀ i < 16, s.mem (off (cx s₀) (zeroOff + i)) = 0)
    (hl : bytesAt s.mem (off (cx s₀) lenOff) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀))
    {out : Instr} {O : Addr}
    (hout : ∀ s : State, Inv s₀ s → s.gpr .a0 = ps s₀ → ∀ Q : State → Prop,
      (∀ s', Upd s s' .a2 O → Q s') → WP isa (.block [out]) s Q)
    (hPO : (sub s₀ polyOff 128).Disjoint ⟨O, 16⟩) (hOw : Covers [sub s₀ polyOff 128, ⟨O, 16⟩] s₀.wr) :
    WP isa (macData out) s fun s' => Step [sub s₀ polyOff 128, ⟨O, 16⟩] s s' ∧ s'.gpr .a0 = ps s₀ ∧
      bytesAt s'.mem O 16 = mac (otk s₀) (M ++ (bytesAt s.mem (dp s₀) (L s₀) ++
        pad16 (bytesAt s.mem (dp s₀) (L s₀))) ++ (leBytes 8 (AL s₀) ++ leBytes 8 (L s₀))) := by
  unfold macData update round16 padArgs
  simp only [mov, List.cons_append, List.nil_append]
  have cP : ∀ s' : State, s'.wr = s₀.wr → Covers [sub s₀ polyOff 128] s'.wr := fun s' hw =>
    covers_ctx hp hw _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨polyOff, rfl, by show polyOff + 128 ≤ 616; decide⟩
  have hdP : (sub s₀ polyOff 128).Disjoint (dR s₀) :=
    (APre.w_sub (s₀ := s₀) hp.d_w (k := polyOff) (n := 128) (by decide)).symm
  -- The data.
  refine WP.seq (wp_addi (imm := 15) (by decide) fun s₁ u₁ => wp_andi (by decide) fun s₂ u₂ =>
    wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => WP.block_nil ?_)
  have i₄ : Inv s₀ s₄ := (((h.upd u₁).upd u₂).upd u₃).upd u₄
  have a0₄ : s₄.gpr .a0 = ps s₀ := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), ha]
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have c₄ : (s₄.gpr .a1).toNat % 16 = 0 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr]; exact round16_mod _
  refine WP.seq (update_call (P := ps s₀) (hPa := cx_al s₀ (by decide)) (D := dp s₀) (c := s₄.gpr .a1) (n := L s₀) a0₄ rfl
    (by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.regs.s9])
    (by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.regs.s10, a5_eq])
    (fit_d' s₀) hdP
    (covers_wr2 (by rw [i₄.rd, i₄.wr]; exact hp.d_in) (cP s₄ i₄.wr)) (cP s₄ i₄.wr) fun s₅ k₅ hb₅ => ?_)
  have i₅ : Inv s₀ s₅ := i₄.step1 k₅.step (k := polyOff) (n := 128) (by decide)
  have a0₅ : s₅.gpr .a0 = ps s₀ := by rw [k₅.a0, a0₄]
  have B₅ := hb₅ (otk s₀) M (by rw [m₄]; exact hb) (c₄.trans hM.symm)
  rw [m₄] at B₅
  have st₅ : Step [sub s₀ polyOff 128, ⟨O, 16⟩] s s₅ :=
    ((((Step.refl _ s).upd' u₁).upd' u₂).upd' u₃).upd' u₄ |>.trans (k₅.step.mono (by simp))
  -- The padding of the data.
  refine WP.seq (wp_addi (imm := 15) (by decide) fun s₆ u₆ => wp_andi (by decide) fun s₇ u₇ =>
    wp_add fun s₈ u₈ => wp_li (imm := 0) (by decide) fun s₉ u₉ => wp_sub fun s₁₀ u₁₀ =>
    wp_andi (by decide) fun s₁₁ u₁₁ => wp_addi (imm := zeroOff - polyOff) (by decide) fun s₁₂ u₁₂ =>
    WP.block_nil ?_)
  have i₁₂ : Inv s₀ s₁₂ := ((((((i₅.upd u₆).upd u₇).upd u₈).upd u₉).upd u₁₀).upd u₁₁).upd u₁₂
  have a0₁₂ : s₁₂.gpr .a0 = ps s₀ := by
    rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
      u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), a0₅]
  have m₁₂ : s₁₂.mem = s₅.mem := by
    rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem]
  have hnl : (16 - L s₀ % 16) % 16 < 16 := Nat.mod_lt _ (by decide)
  have c₁₂ : (s₁₂.gpr .a1).toNat % 16 = (M ++ bytesAt s.mem (dp s₀) (L s₀)).length % 16 := by
    rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
      u₈.gpr, u₇.gpr, u₇.other _ (by decide), u₆.gpr, u₆.other _ (by decide), add_mod16, i₅.regs.s10, a5_eq,
      toNat_ofNat_lt (fit_d' s₀), List.length_append, Proof.Poly1305.length_bytesAt]
    have := round16_mod (s₅.gpr .s8)
    omega_using [hM, this]
  have a2₁₂ : s₁₂.gpr .a2 = off (cx s₀) zeroOff := by
    rw [u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
      u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), a0₅, ps_add]
    rfl
  refine WP.seq (update_call (P := ps s₀) (hPa := cx_al s₀ (by decide)) (D := off (cx s₀) zeroOff) (c := s₁₂.gpr .a1)
    (n := (16 - L s₀ % 16) % 16) a0₁₂ rfl a2₁₂
    (by rw [u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.gpr, u₉.gpr, u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.other _ (by decide), i₅.regs.s10, padN])
    (by omega_using []) (sub_disj s₀ (a := polyOff) (n := 128) (b := zeroOff) (m := (16 - L s₀ % 16) % 16)
      (by simp only [polyOff, zeroOff]; omega_using []) (by decide) (by simp only [zeroOff]; omega_using []))
    (covers_right (covers_ctx hp i₁₂.wr _ fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨zeroOff, rfl, by show zeroOff + _ ≤ 616; simp only [zeroOff]; omega_using []⟩
      · exact ⟨polyOff, rfl, by show polyOff + 128 ≤ 616; decide⟩)) (cP s₁₂ i₁₂.wr) fun s₁₃ k₁₃ hb₁₃ => ?_)
  have i₁₃ : Inv s₀ s₁₃ := i₁₂.step1 k₁₃.step (k := polyOff) (n := 128) (by decide)
  have a0₁₃ : s₁₃.gpr .a0 = ps s₀ := by rw [k₁₃.a0, a0₁₂]
  have hz₁₂ : ∀ i < 16, s₁₂.mem (off (cx s₀) zeroOff + BitVec.ofNat 64 i) = 0 := zeros_of fun i hi => by
    rw [m₁₂, byte_sub s₀ (k := polyOff) (n := 128) k₅.frame (by simp only [polyOff, zeroOff]; omega_using [])
      (by decide) (by simp only [zeroOff]; omega_using [hi]), m₄]
    exact hz i hi
  have hp16 := zeros_pad (bytesAt s.mem (dp s₀) (L s₀)) hz₁₂
  rw [Proof.Poly1305.length_bytesAt] at hp16
  have B₁₃ := hb₁₃ (otk s₀) _ (by rw [m₁₂]; exact B₅) c₁₂
  rw [hp16] at B₁₃
  have st₁₃ : Step [sub s₀ polyOff 128, ⟨O, 16⟩] s s₁₃ :=
    ((((((((st₅.upd' u₆).upd' u₇).upd' u₈).upd' u₉).upd' u₁₀).upd' u₁₁).upd' u₁₂).trans
      (k₁₃.step.mono (by simp)))
  -- The lengths block.
  refine WP.seq (wp_addi (imm := 15) (by decide) fun s₁₄ u₁₄ => wp_andi (by decide) fun s₁₅ u₁₅ =>
    wp_addi (imm := 15) (by decide) fun s₁₆ u₁₆ => wp_andi (by decide) fun s₁₇ u₁₇ =>
    wp_add fun s₁₈ u₁₈ => wp_addi (imm := lenOff - polyOff) (by decide) fun s₁₉ u₁₉ =>
    wp_li (imm := 16) (by decide) fun s₂₀ u₂₀ => WP.block_nil ?_)
  have i₂₀ : Inv s₀ s₂₀ := ((((((i₁₃.upd u₁₄).upd u₁₅).upd u₁₆).upd u₁₇).upd u₁₈).upd u₁₉).upd u₂₀
  have a0₂₀ : s₂₀.gpr .a0 = ps s₀ := by
    rw [u₂₀.other _ (by decide), u₁₉.other _ (by decide), u₁₈.other _ (by decide), u₁₇.other _ (by decide),
      u₁₆.other _ (by decide), u₁₅.other _ (by decide), u₁₄.other _ (by decide), a0₁₃]
  have m₂₀ : s₂₀.mem = s₁₃.mem := by
    rw [u₂₀.mem, u₁₉.mem, u₁₈.mem, u₁₇.mem, u₁₆.mem, u₁₅.mem, u₁₄.mem]
  have hM₁₃ : (M ++ bytesAt s.mem (dp s₀) (L s₀) ++ pad16 (bytesAt s.mem (dp s₀) (L s₀))).length % 16 = 0 := by
    have := length_pad16 (bytesAt s.mem (dp s₀) (L s₀))
    rw [List.append_assoc, List.length_append]; omega_using [hM, this]
  have c₂₀ : (s₂₀.gpr .a1).toNat % 16 = 0 := by
    rw [u₂₀.other _ (by decide), u₁₉.other _ (by decide), u₁₈.gpr, u₁₇.other _ (by decide),
      u₁₆.other _ (by decide), u₁₅.gpr, u₁₄.gpr, u₁₇.gpr, u₁₆.gpr, u₁₅.other _ (by decide),
      u₁₄.other _ (by decide), add_mod16]
    have := round16_mod (s₁₃.gpr .s8)
    have := round16_mod (s₁₃.gpr .s10)
    omega_arith
  have a2₂₀ : s₂₀.gpr .a2 = off (cx s₀) lenOff := by
    rw [u₂₀.other _ (by decide), u₁₉.gpr, u₁₈.other _ (by decide), u₁₇.other _ (by decide),
      u₁₆.other _ (by decide), u₁₅.other _ (by decide), u₁₄.other _ (by decide), a0₁₃, ps_add]
    rfl
  refine WP.seq (update_call (P := ps s₀) (hPa := cx_al s₀ (by decide)) (D := off (cx s₀) lenOff) (c := s₂₀.gpr .a1) (n := 16) a0₂₀ rfl
    a2₂₀ u₂₀.gpr (by decide) (sub_disj s₀ (a := polyOff) (n := 128) (b := lenOff) (m := 16) (by decide) (by decide)
      (by decide))
    (covers_right (covers_ctx hp i₂₀.wr _ fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨lenOff, rfl, by show lenOff + 16 ≤ 616; decide⟩
      · exact ⟨polyOff, rfl, by show polyOff + 128 ≤ 616; decide⟩)) (cP s₂₀ i₂₀.wr) fun s₂₁ k₂₁ hb₂₁ => ?_)
  have i₂₁ : Inv s₀ s₂₁ := i₂₀.step1 k₂₁.step (k := polyOff) (n := 128) (by decide)
  have a0₂₁ : s₂₁.gpr .a0 = ps s₀ := by rw [k₂₁.a0, a0₂₀]
  have hl₂₀ : bytesAt s₂₀.mem (off (cx s₀) lenOff) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
    have d : ∀ r ∈ [(⟨ps s₀, 128⟩ : Region)], (⟨off (cx s₀) lenOff, 16⟩ : Region).Disjoint r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (a := lenOff) (n := 16) (b := polyOff) (m := 128) (by decide) (by decide) (by decide)
    rw [m₂₀, bytesAt_frame k₁₃.frame d (by decide), m₁₂, bytesAt_frame k₅.frame d (by decide), m₄, hl]
  have B₂₁ := hb₂₁ (otk s₀) _ (by rw [m₂₀]; exact B₁₃) (by rw [c₂₀, hM₁₃])
  rw [hl₂₀] at B₂₁
  have st₂₁ : Step [sub s₀ polyOff 128, ⟨O, 16⟩] s s₂₁ :=
    (((((((st₁₃.upd' u₁₄).upd' u₁₅).upd' u₁₆).upd' u₁₇).upd' u₁₈).upd' u₁₉).upd' u₂₀).trans
      (k₂₁.step.mono (by simp))
  -- The tag.
  refine WP.seq (wp_addi (imm := 15) (by decide) fun s₂₂ u₂₂ => wp_andi (by decide) fun s₂₃ u₂₃ =>
    wp_addi (imm := 15) (by decide) fun s₂₄ u₂₄ => wp_andi (by decide) fun s₂₅ u₂₅ =>
    wp_add fun s₂₆ u₂₆ => wp_addi (imm := 16) (by decide) fun s₂₇ u₂₇ => ?_)
  have i₂₇ : Inv s₀ s₂₇ := (((((i₂₁.upd u₂₂).upd u₂₃).upd u₂₄).upd u₂₅).upd u₂₆).upd u₂₇
  have a0₂₇ : s₂₇.gpr .a0 = ps s₀ := by
    rw [u₂₇.other _ (by decide), u₂₆.other _ (by decide), u₂₅.other _ (by decide), u₂₄.other _ (by decide),
      u₂₃.other _ (by decide), u₂₂.other _ (by decide), a0₂₁]
  refine hout s₂₇ i₂₇ a0₂₇ _ fun s₂₈ u₂₈ => ?_
  have i₂₈ : Inv s₀ s₂₈ := i₂₇.upd u₂₈
  have c₂₈ : (s₂₈.gpr .a1).toNat % 16 = 0 := by
    rw [u₂₈.other _ (by decide), u₂₇.gpr, u₂₆.gpr, u₂₅.other _ (by decide), u₂₄.other _ (by decide), u₂₃.gpr,
      u₂₂.gpr, u₂₅.gpr, u₂₄.gpr, u₂₃.other _ (by decide), u₂₂.other _ (by decide), add_mod16,
      toNat_ofNat_lt (by decide : 16 < 2 ^ 64)]
    have := round16_mod (s₂₁.gpr .s8)
    have := round16_mod (s₂₁.gpr .s10)
    have := add_mod16 ((s₂₁.gpr .s8 + BitVec.ofNat 64 15) &&& BitVec.ofInt 64 (-16))
      ((s₂₁.gpr .s10 + BitVec.ofNat 64 15) &&& BitVec.ofInt 64 (-16))
    omega_arith
  have m₂₈ : s₂₈.mem = s₂₁.mem := by
    rw [u₂₈.mem, u₂₇.mem, u₂₆.mem, u₂₅.mem, u₂₄.mem, u₂₃.mem, u₂₂.mem]
  refine finalize_call (P := ps s₀) (hPa := cx_al s₀ (by decide)) (O := O) (c := s₂₈.gpr .a1) (by rw [u₂₈.other _ (by decide), a0₂₇]) rfl
    u₂₈.gpr hPO (by rw [List.nil_append]; exact covers_right (by rw [i₂₈.wr]; exact hOw))
    (by rw [i₂₈.wr]; exact hOw) fun s' k' ht => ?_
  refine ⟨((((((((st₂₁.upd' u₂₂).upd' u₂₃).upd' u₂₄).upd' u₂₅).upd' u₂₆).upd' u₂₇).upd' u₂₈).trans k'.step),
    by rw [k'.a0, u₂₈.other _ (by decide), a0₂₇], ?_⟩
  rw [ht (otk s₀) _ (by rw [m₂₈]; exact B₂₁) (by
    simp only [c₂₈, List.length_append, length_leBytes]
    simp only [List.length_append] at hM₁₃; omega_using [hM₁₃])]
  simp only [List.append_assoc]

end VG.Proof.ChaCha20Poly1305.RISCV64

end

end


/-!
# ChaCha20-Poly1305 on RISC-V: correctness

`seal` and `open` from their parts: the prologue, the calls, and the
epilogue, which restores our caller's registers (and, in `open`, compares
the tags without a branch).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Align VG.Impl.ChaCha20Poly1305.RISCV64
open VG.Impl.ChaCha20.RISCV64.Xor (mov)
open VG.Spec.Poly1305 (bytesAt leBytes mac Buffered Repr)
open VG.Spec.ChaCha20 (stateAt initState)
open VG.Spec.ChaCha20Poly1305 (pad16 polyKeyGen)

variable {e : Bool}

/-! ## Memory through the parts -/

/-- A byte of a part of the context through a frame apart from it. -/
theorem byte_frame {s₀ : State} {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {k n : Nat}
    (hd : ∀ r ∈ rs, (sub s₀ k n).Disjoint r) (hn : k + n ≤ 616) {i : Nat} (hi : i < n) :
    m' (off (cx s₀) (k + i)) = m (off (cx s₀) (k + i)) := by
  have := hf.bytes (R := sub s₀ k n) hd (by show n ≤ 2 ^ 64; omega_using [hn]) hi
  rwa [Offset.add_add] at this

/-- The additional data is unchanged. -/
theorem aad_eq {s₀ s : State} (hp : APre e s₀) (h : Inv s₀ s) : bytesAt s.mem (ad s₀) (AL s₀) = A s₀ :=
  bytesAt_frame h.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.a_w
    · exact hp.a_o) (Nat.le_of_lt (s₀.gpr .a3).isLt)

/-- The received tag is unchanged. -/
theorem tag_eq {s₀ s : State} (hp : APre e s₀) (h : Inv s₀ s) : bytesAt s.mem (tp s₀) 16 = T0 s₀ :=
  bytesAt_frame h.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.t_w
    · exact hp.o_t.symm) (by decide)

/-! ## Restoring the registers -/

/-- The registers `restore` loads. -/
abbrev restored : List Reg := [.s7, .s8, .s9, .s10, .s11, .ra, .s6]

theorem restore_ok {s₀ : State} (hp : APre e s₀) {s : State} (ht : s.gpr .t0 = cx s₀) (hs : Saved s₀ s.mem)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block restore) s fun s' => (∀ r ∈ restored, s'.gpr r = s₀.gpr r) ∧
      (∀ r, r ∉ restored → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.sp = s.sp := by
  have hin : ∀ d, d + 8 ≤ 56 → InRegions (s.rd ++ s.wr) (off (cx s₀) (savOff + d)) 8 := fun d hd => by
    rw [hrd, hwr]; exact hp.in_w' (by simp only [savOff]; omega_using [hd])
  have hal : ∀ d, d % 8 = 0 → (off (cx s₀) (savOff + d)).toNat % 8 = 0 := fun d hd =>
    cx_al s₀ (by simp only [savOff]; omega_using [hd])
  unfold restore
  refine wp_ld (a := off (cx s₀) savOff) (by decide) (by rw [ht]) (hal 0 (by decide))
    (by simpa using hin 0 (by decide)) fun s₁ u₁ => ?_
  refine wp_ld (a := off (cx s₀) (savOff + 8)) (by decide) (by rw [u₁.other _ (by decide), ht])
    (hal 8 (by decide)) (by rw [u₁.rd, u₁.wr]; exact hin 8 (by decide)) fun s₂ u₂ => ?_
  refine wp_ld (a := off (cx s₀) (savOff + 16)) (by decide)
    (by rw [u₂.other _ (by decide), u₁.other _ (by decide), ht]) (hal 16 (by decide))
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 16 (by decide)) fun s₃ u₃ => ?_
  refine wp_ld (a := off (cx s₀) (savOff + 24)) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), ht]) (hal 24 (by decide))
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 24 (by decide)) fun s₄ u₄ => ?_
  refine wp_ld (a := off (cx s₀) (savOff + 32)) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), ht])
    (hal 32 (by decide))
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 32 (by decide)) fun s₅ u₅ => ?_
  refine wp_ld (a := off (cx s₀) (savOff + 40)) (by decide)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), ht]) (hal 40 (by decide))
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 40 (by decide))
    fun s₆ u₆ => ?_
  refine wp_ld (a := off (cx s₀) (savOff + 48)) (by decide)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), ht]) (hal 48 (by decide))
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]
        exact hin 48 (by decide))
    fun s₇ u₇ => WP.block_nil ?_
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have m₆ : s₆.mem = s.mem := by rw [u₆.mem, m₅]
  refine ⟨fun r hr => ?_, fun r hr => ?_, by rw [u₇.mem, m₆], by
    rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hs.s7]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.other _ (by decide), u₂.gpr, u₁.mem, hs.s8]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
        u₃.gpr, u₂.mem, u₁.mem, hs.s9]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem, u₂.mem,
        u₁.mem, hs.s10]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem, hs.s11]
    · rw [u₇.other _ (by decide), u₆.gpr, m₅, hs.ra]
    · rw [u₇.gpr, m₆, hs.s6]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h7, h8, h9, h10, h11, hra, h6⟩ := hr
    rw [u₇.other r h6, u₆.other r hra, u₅.other r h11, u₄.other r h10, u₃.other r h9, u₂.other r h8,
      u₁.other r h7]

/-- The callee-saved registers on return, from those restored and those kept. -/
theorem abi_of {s₀ s s' : State} (h : Inv s₀ s)
    (hr : ∀ r ∈ restored, s'.gpr r = s₀.gpr r) (hk : ∀ r ∈ others, s'.gpr r = s.gpr r)
    (hsp : s'.sp = s₀.sp) : abiPreserved s₀ s' := by
  refine ⟨fun r hr' => ?_, hsp, hr _ (by simp)⟩
  by_cases hm : r ∈ restored
  · exact hr r hm
  · have ho : r ∈ others := by revert r; decide
    rw [hk r ho, h.pres r ho]


/-! ## Up to the MAC of the additional data -/

/-- After the MAC of the additional data. -/
structure AfterAad (s₀ s : State) : Prop where
  inv : Inv s₀ s
  a0 : s.gpr .a0 = ps s₀
  fw : Frame [wR s₀] s₀.mem s.mem
  st : stateAt s.mem (cx s₀) = initState (K s₀) 0 (N s₀)
  buf : Buffered s.mem (ps s₀) (otk s₀) (A s₀ ++ pad16 (A s₀))
  zero : ∀ i < 16, s.mem (off (cx s₀) (zeroOff + i)) = 0
  lens : bytesAt s.mem (off (cx s₀) lenOff) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀)

theorem st_disj (s₀ : State) {k n : Nat} (h : 64 ≤ k) (hk : k + n ≤ 616) :
    ∀ r ∈ [sub s₀ k n], (⟨cx s₀, 64⟩ : Region).Disjoint r := fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  rw [st_sub]; exact sub_disj s₀ (.inl h) (by decide) hk

theorem head_ok {s₀ : State} (hp : APre e s₀) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ s, AfterAad s₀ s → WP isa rest s Q) :
    WP isa (.seq (.block (save ++ moves ++ setup)) (.seq keyGen (.seq polyInit (.seq macAad rest)))) s₀ Q := by
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ p₁ => ?_)
  refine WP.seq (WP.mono (keyGen_ok hp p₁.inv p₁.a0 p₁.st) fun s₂ ⟨st₂, a₂, k₂⟩ => ?_)
  have i₂ := p₁.inv.step1 st₂ (by decide)
  refine WP.seq (WP.mono (polyInit_ok hp i₂ a₂ k₂) fun s₃ ⟨st₃, a₃, r₃⟩ => ?_)
  have i₃ := i₂.step1 st₃ (by decide)
  have hz : ∀ {m m' : Mem} {k n : Nat}, Frame [sub s₀ k n] m m' → (zeroOff + 16 ≤ k ∨ k + n ≤ zeroOff) →
      k + n ≤ 616 → ∀ i < 16, m' (off (cx s₀) (zeroOff + i)) = m (off (cx s₀) (zeroOff + i)) :=
    fun hf h hk i hi => byte_sub s₀ hf (by omega_using [h, hi]) hk (by simp only [zeroOff]; omega_using [hi])
  have z₃ : ∀ i < 16, s₃.mem (off (cx s₀) (zeroOff + i)) = 0 := fun i hi => by
    rw [hz st₃.frame (by decide) (by decide) i hi, hz st₂.frame (by decide) (by decide) i hi, p₁.zero i hi]
  have b₃ : Buffered s₃.mem (ps s₀) (otk s₀) [] := ⟨r₃, rfl⟩
  refine WP.seq (WP.mono (macAad_ok hp i₃ a₃ b₃ z₃) fun s₄ ⟨st₄, a₄, b₄⟩ => k s₄ ?_)
  have i₄ := i₃.step1 st₄ (by decide)
  rw [aad_eq hp i₃] at b₄
  have hl : ∀ {m m' : Mem} {k n : Nat}, Frame [sub s₀ k n] m m' → (lenOff + 16 ≤ k ∨ k + n ≤ lenOff) →
      k + n ≤ 616 → bytesAt m' (off (cx s₀) lenOff) 16 = bytesAt m (off (cx s₀) lenOff) 16 :=
    fun hf h hk => bytesAt_frame hf (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (a := lenOff) (n := 16) h (by decide) hk) (by decide)
  refine ⟨i₄, a₄, ?_, ?_, b₄, fun i hi => ?_, ?_⟩
  · exact ((p₁.fw.trans (fw_sub s₀ st₂.frame (by decide))).trans (fw_sub s₀ st₃.frame (by decide))).trans
      (fw_sub s₀ st₄.frame (by decide))
  · rw [stateAt_frame st₄.frame (st_disj s₀ (by decide) (by decide)),
      stateAt_frame st₃.frame (st_disj s₀ (by decide) (by decide)),
      stateAt_frame st₂.frame (st_disj s₀ (by decide) (by decide)), p₁.st]
  · rw [hz st₄.frame (by decide) (by decide) i hi, z₃ i hi]
  · rw [hl st₄.frame (by decide) (by decide), hl st₃.frame (by decide) (by decide),
      hl st₂.frame (by decide) (by decide), p₁.lens]


/-! ## After the encryption -/

theorem crypt_sub (s₀ : State) :
    ∀ r ∈ [sub s₀ 0 64, oR s₀, sub s₀ 64 320], ∃ r' ∈ [wR s₀, oR s₀], Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨wR s₀, by simp, sub_work s₀ (by decide)⟩
  · exact ⟨oR s₀, by simp, fun _ h => h⟩
  · exact ⟨wR s₀, by simp, sub_work s₀ (by decide)⟩

/-- The parts of the context from the Poly1305 state on are apart from what
`crypt` writes. -/
theorem crypt_disj {s₀ : State} (hp : APre e s₀) {k n : Nat} (hk : 384 ≤ k) (hn : k + n ≤ 616) :
    ∀ r ∈ [sub s₀ 0 64, oR s₀, sub s₀ 64 320], (sub s₀ k n).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sub_disj s₀ (.inr (by omega_using [hk])) hn (by decide)
  · exact (APre.w_sub (s₀ := s₀) hp.o_w hn).symm
  · exact sub_disj s₀ (.inr (by omega_using [hk])) hn (by decide)

/-- The data is apart from the working space. -/
theorem data_eq {s₀ : State} (hp : APre e s₀) {m : Mem} (hf : Frame [wR s₀] s₀.mem m) :
    bytesAt m (dp s₀) (L s₀) = D s₀ :=
  bytesAt_frame hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.d_w)
    (Nat.le_of_lt (fit_d' s₀))

theorem length_encrypt (key nonce m : List Byte) :
    (Spec.ChaCha20.encrypt key 1 nonce m).length = m.length := by
  rw [encrypt_eq, List.length_zipWith, VG.Proof.ChaCha20.length_keystream, Nat.min_self]

theorem macData_eq (a c : List Byte) :
    Spec.ChaCha20Poly1305.macData a c =
      a ++ pad16 a ++ (c ++ pad16 c) ++ (leBytes 8 a.length ++ leBytes 8 c.length) := by
  simp [Spec.ChaCha20Poly1305.macData, List.append_assoc]

/-! ## Seal -/

theorem seal_correct {s₀ : State} (hp : APre true s₀) :
    WP isa Impl.ChaCha20Poly1305.RISCV64.«seal» s₀ fun s' => abiPreserved s₀ s' ∧ sealRISCV64.post s₀ s' := by
  unfold «seal»
  refine head_ok hp fun s₄ h₄ => ?_
  refine WP.seq (WP.mono (crypt_ok hp h₄.inv h₄.a0 h₄.st) fun s₅ ⟨st₅, a₅, c₅⟩ => ?_)
  rw [data_eq hp h₄.fw, show op s₀ = dp s₀ from hp.inPlace] at c₅
  have i₅ : Inv s₀ s₅ := h₄.inv.step st₅ (crypt_sub s₀) fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sub_disj s₀ (.inr (by decide)) (by decide) (by decide)
    · exact (APre.w_sub (s₀ := s₀) hp.o_w (by decide)).symm
    · exact sub_disj s₀ (.inr (by decide)) (by decide) (by decide)
  have B₅ := Buffered.frame st₅.frame (crypt_disj hp (k := polyOff) (n := 128) (by decide) (by decide)) h₄.buf
  have z₅ : ∀ i < 16, s₅.mem (off (cx s₀) (zeroOff + i)) = 0 := fun i hi => by
    rw [byte_frame st₅.frame (crypt_disj hp (k := zeroOff) (n := 16) (by decide) (by decide)) (by decide) hi,
      h₄.zero i hi]
  have l₅ : bytesAt s₅.mem (off (cx s₀) lenOff) 16 = leBytes 8 (AL s₀) ++ leBytes 8 (L s₀) := by
    rw [bytesAt_frame st₅.frame (crypt_disj hp (k := lenOff) (n := 16) (by decide) (by decide)) (by decide),
      h₄.lens]
  have hOw : Covers [sub s₀ polyOff 128, tR s₀] s₀.wr := by
    refine Covers.of_sub fun r hr => ?_
    have := pad_lt' s₀
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨wR s₀, hp.w_wr, pad (wk s₀) + polyOff, cx_off s₀ _, by
        show pad (wk s₀) + polyOff + 128 ≤ 624; simp only [polyOff]; omega_using [this]⟩
    · exact ⟨tR s₀, hp.t_wr, 0, (BitVec.add_zero _).symm, by simp⟩
  refine WP.seq (WP.mono (macData_ok hp i₅ a₅ B₅ (length_pad16 _) z₅ l₅ (out := mov .a2 .s11) (O := tp s₀)
    (fun s i _ Q k => wp_mv fun s' u => WP.block_nil (k s' (by rw [i.regs.s11] at u; exact u)))
    (APre.w_sub (s₀ := s₀) hp.t_w (k := polyOff) (n := 128) (by decide)).symm hOw)
    fun s₆ ⟨st₆, a₆, t₆⟩ => ?_)
  refine wp_subi (imm := polyOff) (by decide) fun s₇ u₇ => ?_
  have hsv : Saved s₀ s₇.mem := by
    rw [u₇.mem]
    refine i₅.saved.frame st₆.frame fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sub_disj s₀ (.inr (by decide)) (by decide) (by decide)
    · exact (APre.w_sub (s₀ := s₀) hp.t_w (by decide)).symm
  refine WP.mono (restore_ok hp (by rw [u₇.gpr, a₆, ps, BitVec.add_sub_cancel]) hsv
    (by rw [u₇.rd, st₆.rd, i₅.rd]) (by rw [u₇.wr, st₆.wr, i₅.wr])) fun s' ⟨hr, hk, hm, hsp⟩ => ⟨?_, ?_⟩
  · exact abi_of i₅ hr (fun r hr' => by
      rw [hk r (by revert r; decide), u₇.other r (by revert r; decide), st₆.cs r (by revert r; decide)])
      (by rw [hsp, u₇.sp, st₆.sp, i₅.sp])
  · have d₆ : bytesAt s₆.mem (dp s₀) (L s₀) = bytesAt s₅.mem (dp s₀) (L s₀) :=
      bytesAt_frame st₆.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact APre.w_sub (s₀ := s₀) hp.d_w (by decide)
        · have := hp.o_t
          simp only [oR, op, dp] at this ⊢
          rwa [show s₀.gpr .t6 = s₀.gpr .a4 from hp.inPlace] at this) (Nat.le_of_lt (fit_d' s₀))
    show Spec.ChaCha20Poly1305.encrypt (K s₀) (N s₀) (A s₀) (D s₀) =
      (bytesAt s'.mem (dp s₀) (L s₀), bytesAt s'.mem (tp s₀) 16)
    rw [hm, u₇.mem, d₆, t₆, c₅, Spec.ChaCha20Poly1305.encrypt, macData_eq, length_encrypt,
      Proof.Poly1305.length_bytesAt, Proof.Poly1305.length_bytesAt]


/-! ## Comparing the tags -/

theorem or_zero_iff (x y : BitVec 64) : x ||| y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    constructor <;> (apply BitVec.eq_of_getLsbD_eq; intro i hi
                     have := congrArg (fun z => z.getLsbD i) h
                     simp at this
                     simp [this])
  · rintro ⟨rfl, rfl⟩; rfl

theorem xor_zero_iff (x y : BitVec 64) : x ^^^ y = 0 ↔ x = y := by
  constructor
  · intro h; have := congrArg (· ^^^ y) h; simpa [BitVec.xor_assoc] using this
  · rintro rfl; exact BitVec.xor_self

theorem lt_one_iff (x : BitVec 64) : x < BitVec.ofNat 64 1 ↔ x = 0 := by
  rw [BitVec.lt_def]
  constructor
  · intro h; apply BitVec.eq_of_toNat_eq; simp at h ⊢; omega_using [h]
  · rintro rfl; decide

theorem setWidth_byte_inj (x y : Byte) : x.setWidth 64 = y.setWidth 64 ↔ x = y := by
  constructor
  · intro h; apply BitVec.eq_of_toNat_eq; have := congrArg BitVec.toNat h; simp at this; omega_using [this]
  · intro h; rw [h]

theorem bytesAt_eq_iff (m : Mem) (p q : Addr) (n : Nat) :
    bytesAt m p n = bytesAt m q n ↔ ∀ i < n, m (p + BitVec.ofNat 64 i) = m (q + BitVec.ofNat 64 i) := by
  constructor
  · intro h i hi
    have := congrArg (·.getD i 0) h
    exact (Proof.ChaCha20.bytesAt_getD m p hi).symm.trans (this.trans (Proof.ChaCha20.bytesAt_getD m q hi))
  · intro h
    simp only [bytesAt]
    exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- After the first `k` bytes compared. -/
structure CI (s₀ s s₂ : State) (k : Nat) (s' : State) : Prop where
  t0 : s'.gpr .t0 = cx s₀
  gpr : ∀ r, r ∉ [.t1, .t2, .t3] → s'.gpr r = s₂.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s₂.rd
  wr : s'.wr = s₂.wr
  sp : s'.sp = s₂.sp
  eq : s'.gpr .t1 = 0 ↔ ∀ i < k, s.mem (off (cx s₀) (tagOff + i)) = s.mem (tp s₀ + BitVec.ofNat 64 i)

theorem compare_ok {s₀ : State} (hp : APre false s₀) {s : State} (h : Inv s₀ s) (ha : s.gpr .a0 = ps s₀)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr .t1 = (if bytesAt s.mem (off (cx s₀) tagOff) 16 = bytesAt s.mem (tp s₀) 16 then 1 else 0) →
      s'.gpr .t0 = cx s₀ → (∀ r, r ∉ [.t0, .t1, .t2, .t3] → s'.gpr r = s.gpr r) → s'.mem = s.mem →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → WP isa (.block rest) s' Q) :
    WP isa (.block (Impl.ChaCha20Poly1305.RISCV64.compare ++ rest)) s Q := by
  unfold Impl.ChaCha20Poly1305.RISCV64.compare
  rw [List.append_assoc, List.append_assoc, List.cons_append, List.cons_append, List.nil_append]
  refine wp_subi (imm := polyOff) (by decide) fun s₁ u₁ => wp_li (imm := 0) (by decide) fun s₂ u₂ => ?_
  have t0₂ : s₂.gpr .t0 = cx s₀ := by rw [u₂.other _ (by decide), u₁.gpr, ha, ps, BitVec.add_sub_cancel]
  have s11₂ : s₂.gpr .s11 = tp s₀ := by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.regs.s11]
  have rd₂ : s₂.rd = s₀.rd := by rw [u₂.rd, u₁.rd, h.rd]
  have wr₂ : s₂.wr = s₀.wr := by rw [u₂.wr, u₁.wr, h.wr]
  rw [WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (CI s₀ s s₂) (fun j x hj hx => ?_) 16 (Nat.le_refl _) s₂
    ⟨t0₂, fun _ _ => rfl, by rw [u₂.mem, u₁.mem], rfl, rfl, rfl,
      by rw [u₂.gpr]; exact ⟨fun _ _ hi => absurd hi (Nat.not_lt_zero _), fun _ => rfl⟩⟩) fun s₃ h₃ => ?_
  · refine wp_lbu (a := off (cx s₀) (tagOff + j)) (by simp only [tagOff]; omega_using [hj]) (by rw [hx.t0])
      (by rw [hx.rd, hx.wr, rd₂, wr₂]; exact hp.in_w' (by simp only [tagOff]; omega_using [hj])) fun y₁ v₁ => ?_
    refine wp_lbu (a := tp s₀ + BitVec.ofNat 64 j) (by omega_using [hj])
      (by rw [v₁.other _ (by decide), hx.gpr _ (by decide), s11₂])
      (by rw [v₁.rd, v₁.wr, hx.rd, hx.wr, rd₂, wr₂]
          exact ⟨tR s₀, List.mem_append_left _ hp.t_rd, Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩)
      fun y₂ v₂ => wp_xor fun y₃ v₃ => wp_or fun y₄ v₄ => WP.block_nil ?_
    have o : ∀ r, r ∉ [.t1, .t2, .t3] → y₄.gpr r = x.gpr r := fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [v₄.other r hr.1, v₃.other r hr.2.1, v₂.other r hr.2.2, v₁.other r hr.2.1]
    refine ⟨by rw [o _ (by decide), hx.t0], fun r hr => by rw [o r hr, hx.gpr r hr],
      by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem, hx.mem], by rw [v₄.rd, v₃.rd, v₂.rd, v₁.rd, hx.rd],
      by rw [v₄.wr, v₃.wr, v₂.wr, v₁.wr, hx.wr], by rw [v₄.sp, v₃.sp, v₂.sp, v₁.sp, hx.sp], ?_⟩
    rw [v₄.gpr, v₃.gpr, v₃.other _ (by decide), v₂.gpr, v₂.other _ (by decide), v₂.other _ (by decide), v₁.gpr,
      v₁.other _ (by decide), v₁.mem, hx.mem, or_zero_iff, xor_zero_iff, setWidth_byte_inj, hx.eq]
    constructor
    · rintro ⟨h₁, h₂⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h₁ i hi
      · exact h₂
    · intro h'; exact ⟨fun i hi => h' i (by omega_using [hi]), h' j (by omega_using [])⟩
  refine wp_li (imm := 1) (by decide) fun s₄ u₄ => wp_sltu fun s₅ u₅ => k s₅ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · have e : s₄.gpr .t1 < s₄.gpr .t2 ↔ bytesAt s.mem (off (cx s₀) tagOff) 16 = bytesAt s.mem (tp s₀) 16 := by
      rw [u₄.gpr, u₄.other _ (by decide), lt_one_iff, h₃.eq, bytesAt_eq_iff]
      exact forall_congr' fun i => imp_congr_right fun _ => by rw [Offset.add_add]
    rw [u₅.gpr]
    by_cases hc : bytesAt s.mem (off (cx s₀) tagOff) 16 = bytesAt s.mem (tp s₀) 16
    · simp only [eq_true (e.mpr hc), eq_true hc, ↓reduceIte]
    · simp only [eq_false (fun h' => hc (e.mp h')), eq_false hc, ↓reduceIte]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), h₃.t0]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₅.other r hr.2.1, u₄.other r hr.2.2.1, h₃.gpr r (by simp [hr.2.1, hr.2.2.1, hr.2.2.2]),
      u₂.other r hr.2.1, u₁.other r hr.1]
  · rw [u₅.mem, u₄.mem, h₃.mem]
  · rw [u₅.rd, u₄.rd, h₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, h₃.wr, u₂.wr, u₁.wr]
  · rw [u₅.sp, u₄.sp, h₃.sp, u₂.sp, u₁.sp]


/-! ## Zeroing the data -/

theorem ofNat_sub_one {n : Nat} (h : 0 < n) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n - 1 = BitVec.ofNat 64 (n - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
  omega

theorem ofNat_ne_zero {n : Nat} (h : 0 < n) (hn : n < 2 ^ 64) : BitVec.ofNat 64 n ≠ 0 := by
  intro e
  have := congrArg BitVec.toNat e
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at this
  exact Nat.ne_of_gt h this

/-- One step of `zeroData`'s loop: the byte at `op + j` zeroed, with `t1`
zero and `t2` at it. -/
theorem zeroStep_ok {s₀ : State} (hp : APre false s₀) {u : State} (hu : Inv s₀ u) {j : Nat}
    (hj : j < L s₀) (ht1 : u.gpr .t1 = 0) (ht2 : u.gpr .t2 = op s₀ + BitVec.ofNat 64 j)
    (hz : Proof.Zeroize.Prefix u.mem (op s₀) j) :
    WP isa (.block [.store .b .t1 .t2 0, .addi .t2 .t2 1, .addi .t3 .t3 (-1)]) u fun u' =>
      Inv s₀ u' ∧ u'.gpr .t1 = 0 ∧ u'.gpr .t2 = op s₀ + BitVec.ofNat 64 (j + 1) ∧
      u'.gpr .t3 = u.gpr .t3 - 1 ∧ (∀ r, r ≠ .t2 → r ≠ .t3 → u'.gpr r = u.gpr r) ∧
      Proof.Zeroize.Prefix u'.mem (op s₀) (j + 1) := by
  have hfit := hp.fit_o
  have hL : L s₀ < 2 ^ 64 := (s₀.gpr .a5).isLt
  have hc : (oR s₀).Contains (op s₀ + BitVec.ofNat 64 j) 1 :=
    Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj, hfit])
  refine wp_sb (off := 0) (a := op s₀ + BitVec.ofNat 64 j) (by decide)
    (by rw [ht2, BitVec.add_zero]) ⟨oR s₀, by rw [hu.wr]; exact hp.o_wr, hc⟩ fun u₁ m₁ => ?_
  refine wp_addi (imm := 1) (by decide) fun u₂ v₂ =>
    wp_subi (imm := 1) (by decide) fun u₃ v₃ => WP.block_nil ?_
  have st₁ : Step [oR s₀] u u₁ :=
    ⟨fun r _ => by rw [m₁.gpr], m₁.sp, m₁.rd, m₁.wr,
      by rw [m₁.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hc⟩
  have st : Step [oR s₀] u u₃ := (st₁.trans (Step.upd _ v₂)).trans (Step.upd _ v₃)
  have o : ∀ r, r ≠ .t2 → r ≠ .t3 → u₃.gpr r = u.gpr r := fun r a b => by
    rw [v₃.other r b, v₂.other r a, m₁.gpr]
  refine ⟨hu.step st (fun r hr => ⟨oR s₀, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h⟩)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (APre.w_sub (s₀ := s₀) hp.o_w (by decide)).symm),
    by rw [o _ (by decide) (by decide), ht1], ?_, by rw [v₃.gpr, v₂.other _ (by decide), m₁.gpr]; rfl, o, ?_⟩
  · rw [v₃.other _ (by decide), v₂.gpr, m₁.gpr, ht2, BitVec.add_assoc, BitVec.ofNat_add]
  · rw [v₃.mem, v₂.mem, m₁.mem, ht1, show BitVec.setWidth 8 (0 : BitVec 64) = 0 by decide]
    exact Proof.Zeroize.prefix_writeW hz (by omega_using [hj, hL])

/-- `zeroData`, with `t1` zero: zeros at the destination, and only `t2` and `t3`
written. -/
theorem zeroData_ok {s₀ : State} (hp : APre false s₀) {s : State} (h : Inv s₀ s) (ht1 : s.gpr .t1 = 0) :
    WP isa zeroData s fun s' => Inv s₀ s' ∧ bytesAt s'.mem (op s₀) (L s₀) = List.replicate (L s₀) 0 ∧
      (∀ r, r ≠ .t2 → r ≠ .t3 → s'.gpr r = s.gpr r) := by
  have hL : L s₀ < 2 ^ 64 := (s₀.gpr .a5).isLt
  unfold zeroData
  refine WP.seq (wp_mv fun u₁ v₁ => wp_mv fun u₂ v₂ => WP.block_nil ?_)
  have t2₂ : u₂.gpr .t2 = op s₀ := by rw [v₂.other _ (by decide), v₁.gpr, h.regs.s6]
  have t3₂ : u₂.gpr .t3 = BitVec.ofNat 64 (L s₀) := by
    rw [v₂.gpr, v₁.other _ (by decide), h.regs.s10, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have i₂ : Inv s₀ u₂ := h.step ((Step.upd [] v₁).trans (Step.upd [] v₂)) (by simp) (by simp)
  have o₂ : ∀ r, r ≠ .t2 → r ≠ .t3 → u₂.gpr r = s.gpr r := fun r a b => by
    rw [v₂.other r b, v₁.other r a]
  by_cases hz : L s₀ = 0
  · refine WP.ite true (by simp only [VG.RISCV64.eval, t3₂, hz]; rfl) (fun _ => WP.block_nil ⟨i₂, ?_, o₂⟩)
      (by simp)
    rw [hz]; rfl
  · have hne := ofNat_ne_zero (n := L s₀) (by omega_using [hz]) hL
    refine WP.ite false (by show some (u₂.gpr .t3 == 0) = some false; rw [t3₂, beq_false_of_ne hne])
      (by simp) fun _ => ?_
    refine WP.loop (M := isa) (fun rem u => ∃ j, j < L s₀ ∧ rem = L s₀ - j ∧ Inv s₀ u ∧ u.gpr .t1 = 0 ∧
      u.gpr .t2 = op s₀ + BitVec.ofNat 64 j ∧ u.gpr .t3 = BitVec.ofNat 64 (L s₀ - j) ∧
      (∀ r, r ≠ .t2 → r ≠ .t3 → u.gpr r = s.gpr r) ∧ Proof.Zeroize.Prefix u.mem (op s₀) j) ?_ (L s₀) u₂
      ⟨0, by omega_using [hz], by omega_using [], i₂, by rw [o₂ _ (by decide) (by decide), ht1],
        by rw [t2₂]; exact (BitVec.add_zero _).symm, by rw [t3₂, Nat.sub_zero], o₂,
        fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
    intro rem u ⟨j, hj, hr, hu, h1, h2, h3, ho, hpz⟩
    refine WP.mono (zeroStep_ok hp hu hj h1 h2 hpz) fun u' ⟨i', t1', t2', t3', o', z'⟩ => ?_
    have t3'' : u'.gpr .t3 = BitVec.ofNat 64 (L s₀ - (j + 1)) := by
      rw [t3', h3, ofNat_sub_one (by omega_using [hj]) (by omega_using [hL]), Nat.sub_sub]
    have o'' : ∀ r, r ≠ .t2 → r ≠ .t3 → u'.gpr r = s.gpr r := fun r a b => by rw [o' r a b, ho r a b]
    by_cases he : j + 1 = L s₀
    · left
      refine ⟨by simp only [VG.RISCV64.eval, t3'', he, Nat.sub_self]; rfl, i', ?_, o''⟩
      rw [he] at z'
      exact Proof.Zeroize.prefix_spec z'
    · right
      have hne := ofNat_ne_zero (n := L s₀ - (j + 1)) (by omega_using [hj, he]) (by omega_using [hL])
      refine ⟨by show some (u'.gpr .t3 != 0) = some true; rw [t3'', bne, beq_false_of_ne hne]; rfl,
        L s₀ - (j + 1), by omega_using [hj, hr], j + 1, by omega_using [hj, he], rfl, i', t1', t2', t3'', o'', z'⟩

/-! ## Open -/

/-- The epilogue, from the context in `t0`: our caller's registers restored,
and the result `t1` in `a0`. -/
theorem tail_ok {s₀ : State} (hp : APre false s₀) {s : State} (h : Inv s₀ s) (ht : s.gpr .t0 = cx s₀) :
    WP isa (.block (restore ++ [mov .a0 .t1])) s fun s' =>
      abiPreserved s₀ s' ∧ s'.gpr .a0 = s.gpr .t1 ∧ s'.mem = s.mem := by
  rw [WP.block_append_iff]
  refine WP.mono (restore_ok hp ht h.saved h.rd h.wr) fun s₈ ⟨hr, hk, hm, hsp⟩ => ?_
  refine wp_mv fun s₉ u₉ => WP.block_nil ⟨?_, by rw [u₉.gpr, hk _ (by decide)], by rw [u₉.mem, hm]⟩
  exact abi_of h (fun r hr' => by rw [u₉.other r (by revert r; decide), hr r hr'])
    (fun r hr' => by rw [u₉.other r (by revert r; decide), hk r (by revert r; decide)])
    (by rw [u₉.sp, hsp, h.sp])

/-- Everything but the epilogue: `t1` is whether the tag is right, the
plaintext is at the destination, and the context is in `t0`. -/
theorem body_ok {s₀ : State} (hp : APre false s₀) :
    WP isa openBody s₀ fun s₇ => Inv s₀ s₇ ∧ s₇.gpr .t0 = cx s₀ ∧
      s₇.gpr .t1 = (if mac (otk s₀) (Spec.ChaCha20Poly1305.macData (A s₀) (D s₀)) = T0 s₀ then 1 else 0) ∧
      bytesAt s₇.mem (op s₀) (L s₀) = Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (D s₀) := by
  unfold openBody
  refine head_ok hp fun s₄ h₄ => ?_
  have hOw : Covers [sub s₀ polyOff 128, sub s₀ tagOff 16] s₀.wr := by
    refine Covers.of_sub fun r hr => ?_
    have := pad_lt' s₀
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨wR s₀, hp.w_wr, pad (wk s₀) + polyOff, cx_off s₀ _, by
        show pad (wk s₀) + polyOff + 128 ≤ 624; simp only [polyOff]; omega_using [this]⟩
    · exact ⟨wR s₀, hp.w_wr, pad (wk s₀) + tagOff, cx_off s₀ _, by
        show pad (wk s₀) + tagOff + 16 ≤ 624; simp only [tagOff]; omega_using [this]⟩
  have hO : ps s₀ + BitVec.ofNat 64 (tagOff - polyOff) = off (cx s₀) tagOff := (ps_add _ _).trans rfl
  refine WP.seq (WP.mono (macData_ok hp h₄.inv h₄.a0 h₄.buf (length_pad16 _) h₄.zero h₄.lens
    (out := .addi .a2 .a0 (tagOff - polyOff)) (O := off (cx s₀) tagOff)
    (fun s _ ha Q k => wp_addi (imm := tagOff - polyOff) (by decide) fun s' u =>
      WP.block_nil (k s' (by rw [ha, hO] at u; exact u)))
    (sub_disj s₀ (.inl (by decide)) (by decide) (by decide)) hOw) fun s₅ ⟨st₅, a₅, t₅⟩ => ?_)
  have i₅ := h₄.inv.step2 st₅ (by decide) (by decide)
  rw [data_eq hp h₄.fw] at t₅
  have f₅ : Frame [wR s₀] s₀.mem s₅.mem := h₄.fw.trans (st₅.frame.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_singleton_self _, sub_work s₀ (k := polyOff) (n := 128) (by decide)⟩
    · exact ⟨_, List.mem_singleton_self _, sub_work s₀ (k := tagOff) (n := 16) (by decide)⟩)
  have hst₅ : stateAt s₅.mem (cx s₀) = initState (K s₀) 0 (N s₀) := by
    rw [stateAt_frame st₅.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [st_sub]; exact sub_disj s₀ (.inl (by decide)) (by decide) (by decide)
      · rw [st_sub]; exact sub_disj s₀ (.inl (by decide)) (by decide) (by decide), h₄.st]
  refine WP.seq (WP.mono (crypt_ok hp i₅ a₅ hst₅) fun s₆ ⟨st₆, a₆, c₆⟩ => ?_)
  rw [data_eq hp f₅] at c₆
  have i₆ : Inv s₀ s₆ := i₅.step st₆ (crypt_sub s₀) fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sub_disj s₀ (.inr (by decide)) (by decide) (by decide)
    · exact (APre.w_sub (s₀ := s₀) hp.o_w (by decide)).symm
    · exact sub_disj s₀ (.inr (by decide)) (by decide) (by decide)
  have t₆ : bytesAt s₆.mem (off (cx s₀) tagOff) 16 =
      mac (otk s₀) (Spec.ChaCha20Poly1305.macData (A s₀) (D s₀)) := by
    rw [bytesAt_frame st₆.frame (crypt_disj hp (k := tagOff) (n := 16) (by decide) (by decide)) (by decide), t₅,
      macData_eq, Proof.Poly1305.length_bytesAt, Proof.Poly1305.length_bytesAt]
  rw [show Impl.ChaCha20Poly1305.RISCV64.compare = Impl.ChaCha20Poly1305.RISCV64.compare ++ [] from
    (List.append_nil _).symm]
  refine compare_ok hp i₆ a₆ fun s₇ t1₇ t0₇ g₇ m₇ rd₇ wr₇ sp₇ => WP.block_nil ?_
  have i₇ : Inv s₀ s₇ := i₆.step (rs := [])
    ⟨fun r hr => g₇ r (by revert r; decide), sp₇, rd₇, wr₇, by rw [m₇]; exact Frame.refl _ _⟩
    (by simp) (by simp)
  have ok₇ : s₇.gpr .t1 =
      if mac (otk s₀) (Spec.ChaCha20Poly1305.macData (A s₀) (D s₀)) = T0 s₀ then 1 else 0 := by
    rw [t1₇, t₆, tag_eq hp i₆]
  exact ⟨i₇, t0₇, ok₇, by rw [m₇, c₆]⟩

/-- What `open`'s body leaves, from the source to the destination: the
result in `a0`, and the plaintext or zeros at the destination. -/
def CorePostOf (res : Option (List Byte)) (s₀ s' : State) : Prop :=
  match res with
  | some pt => s'.gpr .a0 = 1 ∧ bytesAt s'.mem (op s₀) (L s₀) = pt
  | none => s'.gpr .a0 = 0 ∧ bytesAt s'.mem (op s₀) (L s₀) = List.replicate (L s₀) 0

/-- What `open` leaves, by the decryption of its arguments: stated through `CorePostOf`, so that
the kernel never compares a `match` on the decryption with its unfolding (it would evaluate
the decryption to do so: `Proof/Framework/ContractPost.lean`). -/
def CorePost (s₀ s' : State) : Prop :=
  CorePostOf (Spec.ChaCha20Poly1305.decrypt (K s₀) (N s₀) (A s₀) (D s₀) (T0 s₀)) s₀ s'

theorem open_correct {s₀ : State} (hp : APre false s₀) :
    WP isa Impl.ChaCha20Poly1305.RISCV64.«open» s₀ fun s' => abiPreserved s₀ s' ∧ CorePost s₀ s' := by
  unfold «open»
  refine WP.seq (WP.mono (body_ok hp) fun s₇ ⟨i₇, t0₇, ok₇, d₇⟩ => ?_)
  show WP isa (.seq (.ite (.zero .t1) zeroData (.block [])) (.block (restore ++ [mov .a0 .t1]))) s₇ fun s' =>
    abiPreserved s₀ s' ∧ CorePost s₀ s'
  refine WP.seq ?_
  -- The decryption as a variable: the kernel would evaluate it to reduce a `match` on it.
  obtain ⟨res, er⟩ : ∃ res, Spec.ChaCha20Poly1305.decrypt (K s₀) (N s₀) (A s₀) (D s₀) (T0 s₀) = res :=
    ⟨_, rfl⟩
  unfold CorePost
  rw [er]
  by_cases hc : mac (otk s₀) (Spec.ChaCha20Poly1305.macData (A s₀) (D s₀)) = T0 s₀
  · simp only [hc, ↓reduceIte] at ok₇
    refine WP.ite false (by simp only [VG.RISCV64.eval, ok₇]; rfl) (by simp) fun _ => WP.block_nil ?_
    refine WP.mono (tail_ok hp i₇ t0₇) fun s₉ ⟨ha, a0₉, m₉⟩ => ⟨ha, ?_⟩
    cases res with
    | some pt =>
      obtain ⟨-, rfl⟩ := decrypt_eq_some er
      exact ⟨by rw [a0₉, ok₇], by rw [m₉, d₇]⟩
    | none => exact absurd hc (decrypt_eq_none er)
  · simp only [hc, ↓reduceIte] at ok₇
    refine WP.ite true (by simp only [VG.RISCV64.eval, ok₇]; rfl) (fun _ => ?_) (by simp)
    refine WP.mono (zeroData_ok hp i₇ ok₇) fun s₈ ⟨i₈, z₈, o₈⟩ => ?_
    refine WP.mono (tail_ok hp i₈ (by rw [o₈ _ (by decide) (by decide), t0₇])) fun s₉ ⟨ha, a0₉, m₉⟩ => ⟨ha, ?_⟩
    cases res with
    | some pt => exact absurd (decrypt_eq_some er).1 hc
    | none => exact ⟨by rw [a0₉, o₈ _ (by decide) (by decide), ok₇], by rw [m₉, z₈]⟩


/-! ## Constant time

Two runs of `open`'s body from states with the same public data leak the
same (`open_rel`): `openBody` by the taint analysis; then both branch the
same way, as whether the tag is right is public; the zeroing and the
epilogue by the taint analysis, from the public data that `body_ok` and
`zeroData_ok` give them in both runs. Each entry then reaches that body
with the same public data in both runs. -/

/-- Both states satisfy `I`. -/
abbrev Both (I : State → Prop) : State → State → Prop := fun s₁ s₂ => I s₁ ∧ I s₂

theorem ct_seq {I J : State → Prop} {c₁ c₂ : Prog isa} (h₁ : RelCT isa (Both I) c₁ fun _ _ => True)
    (w : ∀ s, I s → WP isa c₁ s J) (h₂ : RelCT isa (Both J) c₂ fun _ _ => True) :
    RelCT isa (Both I) (.seq c₁ c₂) fun _ _ => True :=
  ((h₁.wp fun s₁ s₂ h => ⟨w s₁ h.1, w s₂ h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2).seq h₂

theorem ct_taint {I : State → Prop} {c : Prog isa} (rs : List Reg) (v : Reg → BitVec 64) (sp : Addr)
    (hp : ∀ s, I s → s.sp = sp ∧ ∀ r ∈ rs, s.gpr r = v r) {h : VG.Taint.Hint VG.RISCV64.taint.T}
    (hc : (VG.Taint.check VG.RISCV64.taint (Taint.ofRegs rs) c h).isSome = true) :
    RelCT isa (Both I) c fun _ _ => True :=
  RelCT.taint (A := VG.RISCV64.taint) (Taint.ofRegs rs)
    (fun _ _ hh => ⟨(hp _ hh.1).1.trans (hp _ hh.2).1.symm, fun r h' =>
      ((hp _ hh.1).2 r (Taint.mem_ofRegs.mp h')).trans ((hp _ hh.2).2 r (Taint.mem_ofRegs.mp h')).symm⟩) hc

theorem ok_iff (s₀ : State) :
    okRISCV64 s₀ = true ↔ mac (otk s₀) (Spec.ChaCha20Poly1305.macData (A s₀) (D s₀)) = T0 s₀ := by
  unfold okRISCV64
  constructor
  · intro h
    obtain ⟨pt, hpt⟩ := Option.isSome_iff_exists.mp h
    exact (decrypt_eq_some hpt).1
  · intro h
    cases hd : Spec.ChaCha20Poly1305.decrypt (K s₀) (N s₀) (A s₀) (D s₀) (T0 s₀) with
    | none => exact absurd h (decrypt_eq_none hd)
    | some _ => rfl

theorem leak_bool {a b : Bool} (h : [if a = true then 1 else 0] = [if b = true then 1 else 0]) : a = b := by
  cases a <;> cases b <;> simp_all

/-- The registers the body reads as public on entry. -/
abbrev pubRegs : List Reg := [.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .t6]

/-- What two runs of the body agree on: the public registers (`v`), the
stack pointer and whether the tag is right. -/
def Core (v : Reg → BitVec 64) (sp : Addr) (b : Bool) (s : State) : Prop :=
  APre false s ∧ (∀ r ∈ pubRegs, s.gpr r = v r) ∧ s.sp = sp ∧ okRISCV64 s = b

theorem open_rel (v : Reg → BitVec 64) (sp : Addr) (bo : Bool) :
    RelCT isa (Both (Core v sp bo)) Impl.ChaCha20Poly1305.RISCV64.«open» fun _ _ => True := by
  let c : Addr := v .a7 + BitVec.ofNat 64 (pad (v .a7))
  let b : BitVec 64 := if bo then 1 else 0
  let J : State → Prop := fun s => s.sp = sp ∧ s.gpr .t0 = c ∧ s.gpr .t1 = b ∧
    s.gpr .s6 = v .t6 ∧ s.gpr .s10 = v .a5 ∧ ∃ t₀, Core v sp bo t₀ ∧ Inv t₀ s
  let J' : State → Prop := fun s => s.sp = sp ∧ s.gpr .t0 = c
  unfold «open»
  refine ct_seq (J := J) ?_ ?_ ?_
  · obtain ⟨_, hc⟩ := openBody_taint
    exact ct_taint _ v sp (fun s ⟨_, e, esp, _⟩ => ⟨esp, e⟩) hc
  · intro s ⟨hp, e, esp, eok⟩
    refine WP.mono (body_ok hp) fun s' ⟨i, t0, t1, _⟩ => ⟨by rw [i.sp, esp], ?_, ?_,
      by rw [i.regs.s6, e .t6 (by decide)], by rw [i.regs.s10, e .a5 (by decide)], s, ⟨hp, e, esp, eok⟩, i⟩
    · rw [t0]; show wk s + _ = _; simp only [wk, e .a7 (by decide), c]
    · rw [t1]; show _ = if bo = true then _ else _
      rw [← eok]; simp only [ok_iff]
  · refine ct_seq (J := J') ?_ ?_ ?_
    · refine RelCT.ite (fun _ _ h => by simp only [VG.RISCV64.eval, h.1.2.2.1, h.2.2.2.1]) ?_ ?_
      · obtain ⟨_, hc⟩ := zeroData_taint
        refine RelCT.mono (ct_taint (I := J) _ (fun r => match r with | .s6 => v .t6 | _ => v .a5)
          sp (fun s hs => ⟨hs.1, ?_⟩) hc)
          (fun _ _ h => h.1) fun _ _ h => h
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hs.2.2.2.1
        · exact hs.2.2.2.2.1
      · intro _ _ _ _ _ _ _ x₁ x₂
        cases x₁ with
        | block h₁ =>
          cases x₂ with
          | block h₂ =>
            simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
            exact ⟨h₁.2.symm.trans h₂.2, trivial⟩
    · rintro s ⟨esp, et0, et1, -, -, t₀, ⟨hp, -⟩, i⟩
      by_cases hb : bo = true
      · have : s.gpr .t1 = 1 := by rw [et1]; simp only [b, hb, ↓reduceIte]
        exact WP.ite (M := isa) (c := .zero .t1) false (by simp only [VG.RISCV64.eval, this]; rfl) (by simp)
          fun _ => WP.block_nil ⟨esp, et0⟩
      · have : s.gpr .t1 = 0 := by rw [et1]; simp only [b, hb, Bool.false_eq_true, ↓reduceIte]
        exact WP.ite (M := isa) (c := .zero .t1) true (by simp only [VG.RISCV64.eval, this]; rfl)
          (fun _ => WP.mono (zeroData_ok hp i this) fun s' ⟨i', _, o'⟩ =>
            ⟨by rw [i'.sp, ← i.sp, esp], by rw [o' _ (by decide) (by decide), et0]⟩) (by simp)
    · obtain ⟨_, hc⟩ := tail_taint
      exact ct_taint _ (fun _ => c) sp (fun s hs => ⟨hs.1, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hs.2⟩) hc

/-! ## In place -/

/-- After `mv t6, a4`, from the precondition of `seal` or `open`: the
destination is the source. -/
theorem apre_inPlace {enc : Bool} {s s₁ : State} (hs : preRISCV64 enc s)
    (u : Steps.Upd s s₁ .t6 (s.gpr .a4)) : APre enc s₁ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := hs
  have g : ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7], s₁.gpr r = s.gpr r := fun r hr =>
    u.other r (by revert r; decide)
  have g6 : s₁.gpr .t6 = s.gpr .a4 := u.gpr
  have e : ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7], s₁.gpr r = s.gpr r := g
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at e
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := e
  have rd : s₁.rd = s.rd := u.rd
  have wr : s₁.wr = s.wr := u.wr
  refine {
    k_rd := by simp only [kR, kp, e0, rd, h1]; cases enc <;> simp
    n_rd := by simp only [nR, np, e1, rd, h1]; cases enc <;> simp
    a_rd := by simp only [aR, ad, AL, e2, e3, rd, h1]; cases enc <;> simp
    d_in := by simp only [dR, dp, L, e4, e5, rd, wr, h1, h2]; cases enc <;> simp
    o_wr := by simp only [oR, op, L, g6, e5, wr, h2]; cases enc <;> simp
    w_wr := by simp only [wR, wk, e7, wr, h2]; cases enc <;> simp
    t_in := by cases enc <;> simp only [tR, tp, e6, rd, wr, h1, h2, ↓reduceIte] <;> simp
    k_w := ?_, n_w := ?_, a_w := ?_, d_w := ?_, t_w := ?_,
    k_o := ?_, n_o := ?_, a_o := ?_, o_t := ?_, o_w := ?_, alias := ?_, enc_t := ?_,
    fit_k := ?_, fit_n := ?_, fit_a := ?_, fit_d := ?_, fit_o := ?_, fit_t := ?_, fit_w := ?_ } <;>
  simp only [kR, kp, nR, np, aR, ad, AL, dR, dp, L, tR, tp, wR, wk, oR, op, e0, e1, e2, e3, e4, e5, e6, e7,
    g6] <;>
  first
    | exact .inl rfl
    | with_reducible assumption
    | (cases enc <;> simp_all)

theorem abi_inPlace {s s₁ s' : State} (u : Steps.Upd s s₁ .t6 (s.gpr .a4)) (h : abiPreserved s₁ s') :
    abiPreserved s s' :=
  ⟨fun r hr => by rw [h.1 r hr, u.other r (by revert r; decide)], by rw [h.2.1, u.sp],
    by rw [h.2.2, u.other _ (by decide)]⟩

theorem inPlace_ok {enc : Bool} {c : Prog isa} {s : State} (hs : preRISCV64 enc s) {Q : State → Prop}
    (k : ∀ s₁, Steps.Upd s s₁ .t6 (s.gpr .a4) → APre enc s₁ → WP isa c s₁ Q) :
    WP isa (Impl.ChaCha20Poly1305.RISCV64.inPlace c) s Q :=
  WP.seq (wp_mv fun s₁ u => WP.block_nil (k s₁ u (apre_inPlace hs u)))

theorem ok_inPlace {s s₁ : State} (u : Steps.Upd s s₁ .t6 (s.gpr .a4)) : okRISCV64 s₁ = okRISCV64 s := by
  simp only [okRISCV64, u.mem, u.other .a0 (by decide), u.other .a1 (by decide), u.other .a2 (by decide),
    u.other .a3 (by decide), u.other .a4 (by decide), u.other .a5 (by decide), u.other .a6 (by decide)]

theorem open_ct : ConstantTime isa openRISCV64.pre openRISCV64.pub
    (Impl.ChaCha20Poly1305.RISCV64.inPlace Impl.ChaCha20Poly1305.RISCV64.«open») := by
  intro σ₁ σ₂ t₁ t₂ σ₁' σ₂' h₁ h₂ hq e₁ e₂
  obtain ⟨⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp⟩, ql⟩ := hq
  have qok : okRISCV64 σ₁ = okRISCV64 σ₂ := leak_bool ql
  let v : Reg → BitVec 64 := fun r => if r = .t6 then σ₁.gpr .a4 else σ₁.gpr r
  let I₀ : State → Prop := fun s => preRISCV64 false s ∧ (∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7],
    s.gpr r = σ₁.gpr r) ∧ s.sp = σ₁.sp ∧ okRISCV64 s = okRISCV64 σ₁
  have hc : RelCT isa (Both I₀)
      (Impl.ChaCha20Poly1305.RISCV64.inPlace Impl.ChaCha20Poly1305.RISCV64.«open») fun _ _ => True := by
    unfold Impl.ChaCha20Poly1305.RISCV64.inPlace
    refine ct_seq (J := Core v σ₁.sp (okRISCV64 σ₁)) ?_ ?_ (open_rel v σ₁.sp _)
    · obtain ⟨_, hc⟩ := inPlace_taint
      exact ct_taint _ σ₁.gpr σ₁.sp (fun s ⟨_, e, esp, _⟩ => ⟨esp, e⟩) hc
    · intro s ⟨hpre, e, esp, eok⟩
      refine wp_mv fun s₁ u => WP.block_nil ⟨apre_inPlace hpre u, fun r hr => ?_, by rw [u.sp, esp],
        by rw [ok_inPlace u, eok]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · show s₁.gpr .a0 = σ₁.gpr .a0; rw [u.other _ (by decide)]; exact e .a0 (by simp)
      · show s₁.gpr .a1 = σ₁.gpr .a1; rw [u.other _ (by decide)]; exact e .a1 (by simp)
      · show s₁.gpr .a2 = σ₁.gpr .a2; rw [u.other _ (by decide)]; exact e .a2 (by simp)
      · show s₁.gpr .a3 = σ₁.gpr .a3; rw [u.other _ (by decide)]; exact e .a3 (by simp)
      · show s₁.gpr .a4 = σ₁.gpr .a4; rw [u.other _ (by decide)]; exact e .a4 (by simp)
      · show s₁.gpr .a5 = σ₁.gpr .a5; rw [u.other _ (by decide)]; exact e .a5 (by simp)
      · show s₁.gpr .a6 = σ₁.gpr .a6; rw [u.other _ (by decide)]; exact e .a6 (by simp)
      · show s₁.gpr .a7 = σ₁.gpr .a7; rw [u.other _ (by decide)]; exact e .a7 (by simp)
      · show s₁.gpr .t6 = σ₁.gpr .a4; rw [u.gpr]; exact e .a4 (by simp)
  exact (hc _ _ _ _ _ _ ⟨⟨h₁, fun r _ => rfl, rfl, rfl⟩,
    ⟨h₂, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [q0.symm, q1.symm, q2.symm, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm],
      qsp.symm, qok.symm⟩⟩ e₁ e₂).1

/-! ## `Verified` -/

/-- A state satisfying `seal`'s precondition (with no additional data and no
data): `key` at `0x1000`, `nonce` at `0x1100`, `aad` at `0x2000`, `data` at 0,
`tag` at `0x3000` and `work` at `0x4000`. -/
def sealSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x1100 | .a2 => 0x2000 | .a6 => 0x3000 | .a7 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩]
  wr := [⟨0, 0⟩, ⟨0x3000, 16⟩, ⟨0x4000, 624⟩]

/-- A state satisfying `open`'s precondition (as `sealSat`, with `tag` read). -/
def openSat : State :=
  { sealSat with rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x3000, 16⟩], wr := [⟨0, 0⟩, ⟨0x4000, 624⟩] }

theorem seal_ok (s : State) (hs : sealRISCV64.pre s) :
    ∃ t s', Exec isa (Impl.ChaCha20Poly1305.RISCV64.inPlace Impl.ChaCha20Poly1305.RISCV64.«seal») s t s' ∧
      abiPreserved s s' ∧ sealRISCV64.post s s' :=
  inPlace_ok hs fun s₁ u hp => WP.mono (seal_correct hp) fun s' ⟨ha, hpost⟩ => ⟨abi_inPlace u ha, by
    simpa only [sealRISCV64, u.mem, u.other .a0 (by decide), u.other .a1 (by decide), u.other .a2 (by decide),
      u.other .a3 (by decide), u.other .a4 (by decide), u.other .a5 (by decide), u.other .a6 (by decide)]
      using hpost⟩

theorem open_ok (s : State) (hs : openRISCV64.pre s) :
    ∃ t s', Exec isa (Impl.ChaCha20Poly1305.RISCV64.inPlace Impl.ChaCha20Poly1305.RISCV64.«open») s t s' ∧
      abiPreserved s s' ∧ openRISCV64.post s s' :=
  inPlace_ok hs fun s₁ u hp => WP.mono (open_correct hp) fun s' ⟨ha, hpost⟩ => ⟨abi_inPlace u ha, by
    have ed : Spec.ChaCha20Poly1305.decrypt (K s₁) (N s₁) (A s₁) (D s₁) (T0 s₁) =
        Spec.ChaCha20Poly1305.decrypt (bytesAt s.mem (s.gpr .a0) 32) (bytesAt s.mem (s.gpr .a1) 12)
          (bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) (bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat)
          (bytesAt s.mem (s.gpr .a6) 16) := by
      simp only [K, N, A, D, T0, kp, np, ad, AL, dp, L, tp, u.mem, u.other .a0 (by decide),
        u.other .a1 (by decide), u.other .a2 (by decide), u.other .a3 (by decide), u.other .a4 (by decide),
        u.other .a5 (by decide), u.other .a6 (by decide)]
    have eo : op s₁ = s.gpr .a4 := u.gpr
    have eL : L s₁ = (s.gpr .a5).toNat := by simp only [L, u.other .a5 (by decide)]
    unfold CorePost at hpost
    rw [ed] at hpost
    rw [openRISCV64, Contract.post_mk]
    -- The decryption as a variable: the kernel would evaluate it to reduce a `match` on it.
    obtain ⟨res, er⟩ : ∃ res, Spec.ChaCha20Poly1305.decrypt (bytesAt s.mem (s.gpr .a0) 32)
        (bytesAt s.mem (s.gpr .a1) 12) (bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
        (bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) (bytesAt s.mem (s.gpr .a6) 16) = res := ⟨_, rfl⟩
    rw [er] at hpost ⊢
    cases res <;> (simp only [CorePostOf, eo, eL] at hpost; exact hpost)⟩

theorem seal_verified :
    Verified RISCV64.target (Impl.ChaCha20Poly1305.RISCV64.inPlace Impl.ChaCha20Poly1305.RISCV64.«seal»)
      (sealScratchContract RISCV64.abi 78) :=
  Verified.of_correct seal_ok seal_ct (by
    sig_implies [Proof.ChaCha20Poly1305.sealScratchContract, Proof.ChaCha20Poly1305.sealScratchSig,
      Spec.ChaCha20Poly1305.sealPost, Proof.ChaCha20Poly1305.sealRISCV64, Proof.ChaCha20Poly1305.preRISCV64,
      Proof.ChaCha20Poly1305.pubRISCV64, RISCV64.abi, RISCV64.argRegs]
      [Proof.ChaCha20Poly1305.RISCV64.sealSat]
      using Proof.ChaCha20Poly1305.RISCV64.sealSat)

/-- The postcondition of a contract on `openScratchSig`, for any `post`: with `post` a
variable, the kernel evaluates only the signature (`sig_eval` on a postcondition that
matches on `decrypt` has the kernel evaluate the decryption, twice). -/
private theorem openScratch_post {n stack : Nat} (post : (openScratchSig n).Post RISCV64.abi.ptrBits)
    (leak : Option (Curry ((openScratchSig n).words RISCV64.abi.ptrBits) (Mem → List Nat))) (s s' : State) :
    ((openScratchSig n).contract RISCV64.abi (post := post) (writeArgs := true) (stack := stack)
      (leak := leak)).post s s' =
      post (s.gpr .a0) (s.gpr .a1) (s.gpr .a2) (s.gpr .a3) (s.gpr .a4) (s.gpr .a5) (s.gpr .a6) (s.gpr .a7)
        s.mem s'.mem ((s'.gpr .a0).setWidth 32) := rfl

/-- The postconditions match on `decrypt`; the result is the low word of `a0`. -/
theorem open_verified :
    Verified RISCV64.target (Impl.ChaCha20Poly1305.RISCV64.inPlace Impl.ChaCha20Poly1305.RISCV64.«open»)
      (openZeroScratchContract RISCV64.abi 78) :=
  Verified.of_correct open_ok open_ct
    { pre := by
        sig_implies_pre [Proof.ChaCha20Poly1305.openZeroScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openZeroPost, Spec.ChaCha20Poly1305.openLeak, Proof.ChaCha20Poly1305.openRISCV64,
          Proof.ChaCha20Poly1305.openLeakRISCV64, Proof.ChaCha20Poly1305.preRISCV64,
          Proof.ChaCha20Poly1305.pubRISCV64, RISCV64.abi, RISCV64.argRegs]
      post := by
        intro s s' _ h
        rw [Proof.ChaCha20Poly1305.openZeroScratchContract]
        refine (openScratch_post _ _ s s').mpr ?_
        refine (Spec.ChaCha20Poly1305.openZeroPost.eq_1 ..).mpr ?_
        rw [Proof.ChaCha20Poly1305.openRISCV64, Contract.post_mk] at h
        split at h
        next _ pt e₁ =>
          split
          next _ pt' e₂ =>
            obtain rfl := Option.some.inj (e₁.symm.trans e₂)
            exact ⟨by rw [h.1]; rfl, h.2⟩
          next _ e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
        next _ e₁ =>
          split
          next _ pt' e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
          next _ e₂ => exact ⟨by rw [h.1]; rfl, h.2⟩
      pub := by
        sig_implies_pub [Proof.ChaCha20Poly1305.openZeroScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openZeroPost, Spec.ChaCha20Poly1305.openLeak, Proof.ChaCha20Poly1305.openRISCV64,
          Proof.ChaCha20Poly1305.openLeakRISCV64, Proof.ChaCha20Poly1305.preRISCV64,
          Proof.ChaCha20Poly1305.pubRISCV64, RISCV64.abi, RISCV64.argRegs]
      sat := by
        sig_implies_sat [Proof.ChaCha20Poly1305.openZeroScratchContract, Proof.ChaCha20Poly1305.openScratchSig,
          Spec.ChaCha20Poly1305.openZeroPost, Spec.ChaCha20Poly1305.openLeak, Proof.ChaCha20Poly1305.openRISCV64,
          Proof.ChaCha20Poly1305.openLeakRISCV64, Proof.ChaCha20Poly1305.preRISCV64,
          Proof.ChaCha20Poly1305.pubRISCV64, RISCV64.abi, RISCV64.argRegs]
          [Proof.ChaCha20Poly1305.RISCV64.openSat, Proof.ChaCha20Poly1305.RISCV64.sealSat]
          using Proof.ChaCha20Poly1305.RISCV64.openSat }

/-! ## The frame -/

/-- A state satisfying `seal`'s precondition, without the working space. -/
def sealFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩], wr := [⟨0, 0⟩, ⟨0x3000, 16⟩] }

theorem sealFrameSat_pre : ∃ s, (Spec.ChaCha20Poly1305.sealContract RISCV64.abi 624).pre s := by
  implies_sat [Spec.ChaCha20Poly1305.sealContract, Spec.ChaCha20Poly1305.sealSig,
    Spec.ChaCha20Poly1305.sealPost, RISCV64.abi, RISCV64.argRegs]
    [sealFrameSat, sealSat]
    using sealFrameSat

/-- `seal` with its working space in a frame of 624 bytes on the stack, wiped
after the code. -/
theorem seal_framed :
    Verified RISCV64.target
      (Impl.StackScratch.RISCV64.withStackScratchWiped 624 .a7 78
        (Impl.ChaCha20Poly1305.RISCV64.inPlace Impl.ChaCha20Poly1305.RISCV64.«seal»))
      (Spec.ChaCha20Poly1305.sealContract RISCV64.abi 624) :=
  RISCV64.Verified.stackScratchWiped (sig := Spec.ChaCha20Poly1305.sealSig) (nm := "work") (e := .u64)
    (n := 78) (post := Spec.ChaCha20Poly1305.sealPost RISCV64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 624) (words := 78) seal_verified (by decide) (by decide) (by decide)
    (sealPost_out _) sealFrameSat_pre

/-- A state satisfying `open`'s precondition, without the working space. -/
def openFrameSat : State :=
  { sealSat with rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x3000, 16⟩], wr := [⟨0, 0⟩] }

theorem openFrameSat_pre : ∃ s, (Spec.ChaCha20Poly1305.openZeroContract RISCV64.abi 624).pre s := by
  implies_sat [Spec.ChaCha20Poly1305.openZeroContract, Spec.ChaCha20Poly1305.openSig,
    Spec.ChaCha20Poly1305.openZeroPost, Spec.ChaCha20Poly1305.openLeak, RISCV64.abi, RISCV64.argRegs]
    [openFrameSat, sealSat]
    using openFrameSat

/-- `open` with its working space in a frame of 624 bytes on the stack, wiped
after the code. -/
theorem open_framed :
    Verified RISCV64.target
      (Impl.StackScratch.RISCV64.withStackScratchWiped 624 .a7 78
        (Impl.ChaCha20Poly1305.RISCV64.inPlace Impl.ChaCha20Poly1305.RISCV64.«open»))
      (Spec.ChaCha20Poly1305.openZeroContract RISCV64.abi 624) :=
  RISCV64.Verified.stackScratchWiped (sig := Spec.ChaCha20Poly1305.openSig) (nm := "work") (e := .u64)
    (n := 78) (post := Spec.ChaCha20Poly1305.openZeroPost RISCV64.abi.ptrBits) (wa := true) (stack := 0)
    (leak := some (Spec.ChaCha20Poly1305.openLeak RISCV64.abi.ptrBits))
    (bytes := 624) (words := 78) open_verified (by decide) (by decide) (by decide)
    (openZeroPost_out _) openFrameSat_pre

/-! ## Out of place

`vg_chacha20_poly1305_open_to` is `open`'s body after `toEntry`: `dst` into
`t6`, and `tag` and `work` from the stack into `a6` and `a7`, where the body
expects them. -/

/-- After `toEntry`. -/
structure ToEntered (s s₄ : State) : Prop where
  gpr : ∀ r, r ≠ .t6 → r ≠ .t0 → r ≠ .a6 → r ≠ .a7 → s₄.gpr r = s.gpr r
  t6 : s₄.gpr .t6 = s.gpr .a6
  a6 : s₄.gpr .a6 = stackArg s 0
  a7 : s₄.gpr .a7 = stackArg s 1
  mem : s₄.mem = s.mem
  sp : s₄.sp = s.sp
  rd : s₄.rd = s.rd
  wr : s₄.wr = s.wr

theorem toEntry_ok {s : State} (hs : openToPreRISCV64 s) : WP isa (.block toEntry) s (ToEntered s) := by
  obtain ⟨hrd, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hfa, hal, _, _⟩ := hs
  have hin : ∀ j, j < 2 → InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8 := fun j hj => by
    refine ⟨toArgs s, by rw [hrd]; simp, ?_⟩
    show (⟨s.sp + BitVec.ofNat 64 (8 * 0), 16⟩ : Region).Contains (s.sp + BitVec.ofNat 64 (8 * j)) 8
    exact Offset.contains _ (by omega_using []) (by omega_using [hj]) (by simp only [stackArgAddr] at hfa; omega_using [])
  have hal8 : ∀ j, (stackArgAddr s j).toNat % 8 = 0 := fun j =>
    Spill.al8 (by omega_using [hal]) (by omega_using [])
  unfold toEntry
  refine wp_mv fun s₁ u₁ => wp_addSp (imm := 0) (by decide) fun s₂ u₂ => ?_
  have p₂ : s₂.gpr .t0 = s.sp := by rw [u₂.gpr, u₁.sp, BitVec.add_zero]
  refine wp_ld (a := stackArgAddr s 0) (by decide) (by rw [p₂]; rfl) (hal8 0)
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 0 (by decide)) fun s₃ u₃ => ?_
  refine wp_ld (a := stackArgAddr s 1) (by decide) (by rw [u₃.other _ (by decide), p₂]; rfl) (hal8 1)
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact hin 1 (by decide)) fun s₄ u₄ => WP.block_nil ?_
  have hm : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  exact ⟨fun r h6 h0 ha6 ha7 => by rw [u₄.other r ha7, u₃.other r ha6, u₂.other r h0, u₁.other r h6],
    by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr],
    by rw [u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem]; rfl,
    by rw [u₄.gpr, u₃.mem, u₂.mem, u₁.mem]; rfl, hm,
    by rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp], by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd],
    by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩

theorem apre_openTo {s s₄ : State} (hs : openToPreRISCV64 s) (h : ToEntered s s₄) : APre false s₄ := by
  obtain ⟨h1, h2, dk, dn, da, ds, dt, dw, dg, wk', wn, wa, ws, wt, wg, f0, f1, f2, f4, f6, ft, fw, -, -, hl, -⟩ :=
    hs
  have e0 := h.gpr .a0 (by decide) (by decide) (by decide) (by decide)
  have e1 := h.gpr .a1 (by decide) (by decide) (by decide) (by decide)
  have e2 := h.gpr .a2 (by decide) (by decide) (by decide) (by decide)
  have e3 := h.gpr .a3 (by decide) (by decide) (by decide) (by decide)
  have e4 := h.gpr .a4 (by decide) (by decide) (by decide) (by decide)
  have e5 := h.gpr .a5 (by decide) (by decide) (by decide) (by decide)
  simp only [hl] at h1 h2 dk dn da ds dt dw dg f6
  refine {
    k_rd := ?_, n_rd := ?_, a_rd := ?_, d_in := ?_, o_wr := ?_, w_wr := ?_, t_in := ?_,
    k_w := ?_, n_w := ?_, a_w := ?_, d_w := ?_, t_w := ?_,
    k_o := ?_, n_o := ?_, a_o := ?_, o_t := ?_, o_w := ?_, enc_t := trivial,
    alias := by
      refine .inr ⟨rfl, ?_⟩
      simp only [dR, dp, L, oR, op, e4, e5, h.t6]
      exact ds.symm,
    fit_k := ?_, fit_n := ?_, fit_a := ?_, fit_d := ?_, fit_o := ?_, fit_t := ?_, fit_w := ?_ } <;>
  simp only [kR, kp, nR, np, aR, ad, AL, dR, dp, L, tR, tp, wR, wk, oR, op, e0, e1, e2, e3, e4, e5, h.t6,
    h.a6, h.a7, h.rd, h.wr, h1, h2, Bool.false_eq_true, ↓reduceIte] <;>
  first
    | with_reducible assumption
    | (apply Region.Disjoint.symm; with_reducible assumption)
    | simp
    | omega

theorem abi_openTo {s s₄ s' : State} (h : ToEntered s s₄) (ha : abiPreserved s₄ s') : abiPreserved s s' :=
  ⟨fun r hr => by
    rw [ha.1 r hr, h.gpr r (by revert r; decide) (by revert r; decide) (by revert r; decide)
      (by revert r; decide)], by rw [ha.2.1, h.sp],
    by rw [ha.2.2, h.gpr _ (by decide) (by decide) (by decide) (by decide)]⟩

theorem ok_openTo {s s₄ : State} (h : ToEntered s s₄) : okRISCV64 s₄ = (openToRes s).isSome := by
  simp only [okRISCV64, openToRes, h.mem, h.a6, h.gpr .a0 (by decide) (by decide) (by decide) (by decide),
    h.gpr .a1 (by decide) (by decide) (by decide) (by decide),
    h.gpr .a2 (by decide) (by decide) (by decide) (by decide),
    h.gpr .a3 (by decide) (by decide) (by decide) (by decide),
    h.gpr .a4 (by decide) (by decide) (by decide) (by decide),
    h.gpr .a5 (by decide) (by decide) (by decide) (by decide)]

theorem openTo_ok (s : State) (hs : openToRISCV64.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20Poly1305.RISCV64.openTo s t s' ∧ abiPreserved s s' ∧
      openToRISCV64.post s s' :=
  WP.seq (WP.mono (toEntry_ok hs) fun s₄ h₄ => WP.mono (open_correct (apre_openTo hs h₄))
    fun s' ⟨ha, hpost⟩ => ⟨abi_openTo h₄ ha, by
      have ed : Spec.ChaCha20Poly1305.decrypt (K s₄) (N s₄) (A s₄) (D s₄) (T0 s₄) = openToRes s := by
        simp only [K, N, A, D, T0, kp, np, ad, AL, dp, L, tp, openToRes, h₄.mem, h₄.a6,
          h₄.gpr .a0 (by decide) (by decide) (by decide) (by decide),
          h₄.gpr .a1 (by decide) (by decide) (by decide) (by decide),
          h₄.gpr .a2 (by decide) (by decide) (by decide) (by decide),
          h₄.gpr .a3 (by decide) (by decide) (by decide) (by decide),
          h₄.gpr .a4 (by decide) (by decide) (by decide) (by decide),
          h₄.gpr .a5 (by decide) (by decide) (by decide) (by decide)]
      have eo : op s₄ = s.gpr .a6 := h₄.t6
      have eL : L s₄ = (s.gpr .a5).toNat := by
        simp only [L, h₄.gpr .a5 (by decide) (by decide) (by decide) (by decide)]
      unfold CorePost at hpost
      rw [ed] at hpost
      rw [openToRISCV64, Contract.post_mk]
      -- The decryption as a variable: the kernel would evaluate it to reduce a `match` on it.
      obtain ⟨res, er⟩ : ∃ res, openToRes s = res := ⟨_, rfl⟩
      rw [er] at hpost ⊢
      cases res <;> (simp only [CorePostOf, eo, eL] at hpost; exact hpost)⟩)

theorem openTo_ct : ConstantTime isa openToRISCV64.pre openToRISCV64.pub Impl.ChaCha20Poly1305.RISCV64.openTo := by
  intro σ₁ σ₂ t₁ t₂ σ₁' σ₂' h₁ h₂ hq e₁ e₂
  obtain ⟨⟨q0, q1, q2, q3, q4, q5, q6, q7, qsp⟩, qa, ql⟩ := hq
  have qok : (openToRes σ₁).isSome = (openToRes σ₂).isSome := leak_bool ql
  let v : Reg → BitVec 64 := fun r =>
    if r = .t6 then σ₁.gpr .a6 else if r = .a6 then stackArg σ₁ 0 else if r = .a7 then stackArg σ₁ 1
    else σ₁.gpr r
  let I₀ : State → Prop := fun s => openToPreRISCV64 s ∧ (∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7],
    s.gpr r = σ₁.gpr r) ∧ s.sp = σ₁.sp ∧ (∀ i < 2, stackArg s i = stackArg σ₁ i) ∧
    (openToRes s).isSome = (openToRes σ₁).isSome
  have hc : RelCT isa (Both I₀) Impl.ChaCha20Poly1305.RISCV64.openTo fun _ _ => True := by
    unfold Impl.ChaCha20Poly1305.RISCV64.openTo
    refine ct_seq (J := Core v σ₁.sp (openToRes σ₁).isSome) ?_ ?_ (open_rel v σ₁.sp _)
    · obtain ⟨_, hc⟩ := toEntry_taint
      exact ct_taint _ σ₁.gpr σ₁.sp (fun s ⟨_, e, esp, _⟩ => ⟨esp, e⟩) hc
    · intro s ⟨hpre, e, esp, ea, eok⟩
      refine WP.mono (toEntry_ok hpre) fun s₄ h₄ => ⟨apre_openTo hpre h₄, fun r hr => ?_,
        by rw [h₄.sp, esp], by rw [ok_openTo h₄, eok]⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have g : ∀ r, r ≠ .t6 → r ≠ .t0 → r ≠ .a6 → r ≠ .a7 → r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7] →
          s₄.gpr r = σ₁.gpr r := fun r a b c d hm => (h₄.gpr r a b c d).trans (e r hm)
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact g .a0 (by decide) (by decide) (by decide) (by decide) (by simp)
      · exact g .a1 (by decide) (by decide) (by decide) (by decide) (by simp)
      · exact g .a2 (by decide) (by decide) (by decide) (by decide) (by simp)
      · exact g .a3 (by decide) (by decide) (by decide) (by decide) (by simp)
      · exact g .a4 (by decide) (by decide) (by decide) (by decide) (by simp)
      · exact g .a5 (by decide) (by decide) (by decide) (by decide) (by simp)
      · show s₄.gpr .a6 = stackArg σ₁ 0; rw [h₄.a6]; exact ea 0 (by decide)
      · show s₄.gpr .a7 = stackArg σ₁ 1; rw [h₄.a7]; exact ea 1 (by decide)
      · show s₄.gpr .t6 = σ₁.gpr .a6; rw [h₄.t6]; exact e .a6 (by simp)
  exact (hc _ _ _ _ _ _ ⟨⟨h₁, fun r _ => rfl, rfl, fun i _ => rfl, rfl⟩,
    ⟨h₂, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [q0.symm, q1.symm, q2.symm, q3.symm, q4.symm, q5.symm, q6.symm, q7.symm],
      qsp.symm, fun i hi => (qa i hi).symm, qok.symm⟩⟩ e₁ e₂).1

/-- A state satisfying `open_to`'s precondition (with no additional data and
no data): `key`, `nonce` and `aad` as in `sealSat`, `src` at `0x5000`, `dst`
at 0, `tag` at `0x3000` and `work` at `0x4000`, both on the stack at `sp`. -/
def openToSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x1100 | .a2 => 0x2000 | .a4 => 0x5000 | _ => 0
  sp := 0x8000
  mem a := bif Nat.beq a.toNat 0x8001 then 0x30 else bif Nat.beq a.toNat 0x8009 then 0x40 else 0
  rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x5000, 0⟩, ⟨0x3000, 16⟩, ⟨0x8000, 16⟩]
  wr := [⟨0, 0⟩, ⟨0x4000, 624⟩]

/-- As `openScratch_post`, for `openToScratchSig`: its last two arguments are on the stack. -/
private theorem openToScratch_post {n stack : Nat} (post : (openToScratchSig n).Post RISCV64.abi.ptrBits)
    (pre : Curry ((openToScratchSig n).words RISCV64.abi.ptrBits) (Mem → Prop))
    (leak : Option (Curry ((openToScratchSig n).words RISCV64.abi.ptrBits) (Mem → List Nat))) (s s' : State) :
    ((openToScratchSig n).contract RISCV64.abi (pre := pre) (post := post) (writeArgs := true) (stack := stack)
      (leak := leak)).post s s' =
      post (s.gpr .a0) (s.gpr .a1) (s.gpr .a2) (s.gpr .a3) (s.gpr .a4) (s.gpr .a5) (s.gpr .a6) (s.gpr .a7)
        (RISCV64.stackArg s 0) (RISCV64.stackArg s 1) s.mem s'.mem ((s'.gpr .a0).setWidth 32) := rfl

/-- The postconditions match on `decrypt`; the result is the low word of `a0`. -/
theorem openTo_verified :
    Verified RISCV64.target Impl.ChaCha20Poly1305.RISCV64.openTo (openToScratchContract RISCV64.abi 78) :=
  Verified.of_correct openTo_ok openTo_ct
    { pre := by
        intro s h
        sig_pre [Proof.ChaCha20Poly1305.openToScratchContract, Proof.ChaCha20Poly1305.openToScratchSig,
            Spec.ChaCha20Poly1305.openToPre, Spec.ChaCha20Poly1305.openToPost, Spec.ChaCha20Poly1305.openToLeak,
            Proof.ChaCha20Poly1305.openToRISCV64, Proof.ChaCha20Poly1305.openToPreRISCV64,
            Proof.ChaCha20Poly1305.openToRes, Proof.ChaCha20Poly1305.openToLeakRISCV64,
            Proof.ChaCha20Poly1305.toArgs, Proof.ChaCha20Poly1305.pubRISCV64, RISCV64.abi, RISCV64.argRegs,
            RISCV64.stackArg, RISCV64.stackArgAddr, List.getD, List.range, List.range.loop] at h
        sig_split h
        sig_reduce [Proof.ChaCha20Poly1305.openToScratchContract, Proof.ChaCha20Poly1305.openToScratchSig,
            Spec.ChaCha20Poly1305.openToPre, Spec.ChaCha20Poly1305.openToPost, Spec.ChaCha20Poly1305.openToLeak,
            Proof.ChaCha20Poly1305.openToRISCV64, Proof.ChaCha20Poly1305.openToPreRISCV64,
            Proof.ChaCha20Poly1305.openToRes, Proof.ChaCha20Poly1305.openToLeakRISCV64,
            Proof.ChaCha20Poly1305.toArgs, Proof.ChaCha20Poly1305.pubRISCV64, RISCV64.abi, RISCV64.argRegs,
            RISCV64.stackArg, RISCV64.stackArgAddr, List.getD, List.range, List.range.loop]
        sig_and_intros
        sig_close
        all_goals first
          | with_reducible assumption
          | sig_disjoint_symm
          | omega
          | bv_omega_arith
      post := by
        intro s s' _ h
        rw [Proof.ChaCha20Poly1305.openToScratchContract]
        refine (openToScratch_post _ _ _ s s').mpr ?_
        refine (Spec.ChaCha20Poly1305.openToPost.eq_1 ..).mpr ?_
        rw [Proof.ChaCha20Poly1305.openToRISCV64, Contract.post_mk] at h
        simp only [Proof.ChaCha20Poly1305.openToRes] at h
        split at h
        next _ pt e₁ =>
          split
          next _ pt' e₂ =>
            obtain rfl := Option.some.inj (e₁.symm.trans e₂)
            exact ⟨by rw [h.1]; rfl, h.2⟩
          next _ e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
        next _ e₁ =>
          split
          next _ pt' e₂ => exact absurd (e₁.symm.trans e₂) (by simp)
          next _ e₂ => exact ⟨by rw [h.1]; rfl, h.2⟩
      pub := by
        sig_implies_pub [Proof.ChaCha20Poly1305.openToScratchContract, Proof.ChaCha20Poly1305.openToScratchSig,
            Spec.ChaCha20Poly1305.openToPre, Spec.ChaCha20Poly1305.openToPost, Spec.ChaCha20Poly1305.openToLeak,
            Proof.ChaCha20Poly1305.openToRISCV64, Proof.ChaCha20Poly1305.openToPreRISCV64,
            Proof.ChaCha20Poly1305.openToRes, Proof.ChaCha20Poly1305.openToLeakRISCV64,
            Proof.ChaCha20Poly1305.toArgs, Proof.ChaCha20Poly1305.pubRISCV64, RISCV64.abi, RISCV64.argRegs,
            RISCV64.stackArg, RISCV64.stackArgAddr, List.getD, List.range, List.range.loop]
      sat := by
        sig_implies_sat [Proof.ChaCha20Poly1305.openToScratchContract, Proof.ChaCha20Poly1305.openToScratchSig,
            Spec.ChaCha20Poly1305.openToPre, Spec.ChaCha20Poly1305.openToPost, Spec.ChaCha20Poly1305.openToLeak,
            Proof.ChaCha20Poly1305.openToRISCV64, Proof.ChaCha20Poly1305.openToPreRISCV64,
            Proof.ChaCha20Poly1305.openToRes, Proof.ChaCha20Poly1305.openToLeakRISCV64,
            Proof.ChaCha20Poly1305.toArgs, Proof.ChaCha20Poly1305.pubRISCV64, RISCV64.abi, RISCV64.argRegs,
            RISCV64.stackArg, RISCV64.stackArgAddr, List.getD, List.range, List.range.loop]
          [Proof.ChaCha20Poly1305.RISCV64.openToSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
          using Proof.ChaCha20Poly1305.RISCV64.openToSat }

/-- A state satisfying `open_to`'s precondition, without the working space:
`tag`, its one stack argument. -/
def openToFrameSat : State :=
  { openToSat with rd := [⟨0x1000, 32⟩, ⟨0x1100, 12⟩, ⟨0x2000, 0⟩, ⟨0x5000, 0⟩, ⟨0x3000, 16⟩, ⟨0x8000, 8⟩],
                   wr := [⟨0, 0⟩] }

theorem openToFrameSat_pre : ∃ s, (Spec.ChaCha20Poly1305.openToContract RISCV64.abi 640).pre s := by
  implies_sat [Spec.ChaCha20Poly1305.openToContract, Spec.ChaCha20Poly1305.openToSig,
    Spec.ChaCha20Poly1305.openToPre, Spec.ChaCha20Poly1305.openToPost, Spec.ChaCha20Poly1305.openToLeak,
    RISCV64.abi, RISCV64.argRegs, RISCV64.stackArg, RISCV64.stackArgAddr, List.getD, List.range,
    List.range.loop] [openToFrameSat, openToSat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using openToFrameSat

/-- `open_to` with its working space in a frame of 640 bytes on the stack
(after the copy of `tag` and the working space's address), wiped after the
code. -/
theorem openTo_framed :
    Verified RISCV64.target
      (Impl.StackScratch.RISCV64.withStackScratchArgsWiped 640 1 78 Impl.ChaCha20Poly1305.RISCV64.openTo)
      (Spec.ChaCha20Poly1305.openToContract RISCV64.abi 640) :=
  RISCV64.Verified.stackScratchArgsWiped (sig := Spec.ChaCha20Poly1305.openToSig) (nm := "work") (e := .u64)
    (n := 78) (pre := Spec.ChaCha20Poly1305.openToPre RISCV64.abi.ptrBits)
    (post := Spec.ChaCha20Poly1305.openToPost RISCV64.abi.ptrBits) (wa := true) (stack := 0) (bytes := 640)
    (m := 1) (words := 78) (leak := some (Spec.ChaCha20Poly1305.openToLeak RISCV64.abi.ptrBits))
    openTo_verified (by decide) (by decide) (by decide) (by decide) (openToPre_local _) (openToPost_local _)
    (openToPost_out _) openToFrameSat_pre (hleak := openToLeak_local _)

end VG.Proof.ChaCha20Poly1305.RISCV64

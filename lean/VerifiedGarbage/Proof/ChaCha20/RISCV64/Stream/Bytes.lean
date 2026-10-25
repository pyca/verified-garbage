module

import VerifiedGarbage.Proof.ChaCha20.RISCV64.Stream.Init
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.WriteBytes
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.ChaCha20.RISCV64.Xor
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Impl.ChaCha20.RISCV64.Stream
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Inline
public import VerifiedGarbage.Proof.Framework.Semantics

/-!
# Streaming ChaCha20 on RISC-V: XORing bytes

Untrusted: everything here is checked by Lean. `xorBytes` XORs the `a2`
bytes at `t2` into those at `s6`, one at a time, advancing both and
counting them off `a2` and `s7`. The structure of the PPC64LE proof
(`Proof/ChaCha20/PPC64LE/Stream/Bytes.lean`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20.RISCV64.Stream

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.ChaCha20.RISCV64.Stream
open VG.Proof.ChaCha20.RISCV64.Xor (xor_setWidth sub_ofNat add_ofNat)

/-- What `xorBytes` needs: `c` bytes at `D` to write and at `K` to read, not
overlapping. -/
structure BPre (s : State) (D K : Addr) (c : Nat) : Prop where
  s6 : s.gpr .s6 = D
  t2 : s.gpr .t2 = K
  a2 : s.gpr .a2 = BitVec.ofNat 64 c
  c_lt : c ≤ 2 ^ 32
  wD : ∀ k < c, InRegions s.wr (D + BitVec.ofNat 64 k) 1
  rK : ∀ k < c, InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 k) 1
  sep : ∀ j < c, ∀ k < c, D + BitVec.ofNat 64 j ≠ K + BitVec.ofNat 64 k

/-- The registers `xorBytes` writes. -/
abbrev bw : List Reg := [.t2, .a2, .t3, .t4, .s6, .s7]

/-- What `xorBytes` leaves: the bytes XORed, `s6` past them and `s7` less
their number; only the registers `bw` are written. -/
structure BPost (s : State) (D K : Addr) (c : Nat) (s' : State) : Prop where
  s6 : s'.gpr .s6 = D + BitVec.ofNat 64 c
  s7 : s'.gpr .s7 = s.gpr .s7 - BitVec.ofNat 64 c
  keep : ∀ r, r ∉ bw → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  data : ∀ k < c, s'.mem (D + BitVec.ofNat 64 k) =
    s.mem (D + BitVec.ofNat 64 k) ^^^ s.mem (K + BitVec.ofNat 64 k)
  frame : Frame [⟨D, c⟩] s.mem s'.mem

/-- Before byte `i`. -/
structure LInv (s : State) (D K : Addr) (c i : Nat) (s' : State) : Prop where
  s6 : s'.gpr .s6 = D + BitVec.ofNat 64 i
  t2 : s'.gpr .t2 = K + BitVec.ofNat 64 i
  a2 : s'.gpr .a2 = BitVec.ofNat 64 (c - i)
  s7 : s'.gpr .s7 = s.gpr .s7 - BitVec.ofNat 64 i
  keep : ∀ r, r ∉ bw → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  data : ∀ k < c, s'.mem (D + BitVec.ofNat 64 k) =
    if k < i then s.mem (D + BitVec.ofNat 64 k) ^^^ s.mem (K + BitVec.ofNat 64 k)
    else s.mem (D + BitVec.ofNat 64 k)
  frame : Frame [⟨D, c⟩] s.mem s'.mem

/-- A byte read is outside the bytes written. -/
theorem not_contains {D K : Addr} {c i : Nat}
    (hs : ∀ j < c, ∀ k < c, D + BitVec.ofNat 64 j ≠ K + BitVec.ofNat 64 k) (hi : i < c)
    (h : (⟨D, c⟩ : Region).Contains (K + BitVec.ofNat 64 i) 1) : False := by
  simp only [Region.Contains] at h
  refine hs (K + BitVec.ofNat 64 i - D).toNat (by omega) i hi ?_
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]

/-- The loop's body. -/
def body : List Instr :=
  [.load .b .t3 .s6 0, .load .b .t4 .t2 0, .logic .xor .t3 .t3 .t4, .store .b .t3 .s6 0,
    .addi .s6 .s6 1, .addi .t2 .t2 1, .addi .a2 .a2 (-1), .addi .s7 .s7 (-1)]

theorem byte_step {s : State} {D K : Addr} {c i : Nat} (hp : BPre s D K c) (hi : i < c) {s₁ : State}
    (h : LInv s D K c i s₁) : WP isa (.block body) s₁ (LInv s D K c (i + 1)) := by
  have hc := hp.c_lt
  have i₁ : InRegions (s₁.rd ++ s₁.wr) (D + BitVec.ofNat 64 i) 1 := by
    obtain ⟨r, hr, hc⟩ := hp.wD i hi; exact ⟨r, by rw [h.rd, h.wr]; exact List.mem_append_right _ hr, hc⟩
  have i₂ : InRegions (s₁.rd ++ s₁.wr) (K + BitVec.ofNat 64 i) 1 := by rw [h.rd, h.wr]; exact hp.rK i hi
  have o₁ : InRegions s₁.wr (D + BitVec.ofNat 64 i) 1 := by rw [h.wr]; exact hp.wD i hi
  have cd : (⟨D, c⟩ : Region).Contains (D + BitVec.ofNat 64 i) 1 := Offset.contains_base D (by omega) (by omega)
  unfold body
  refine wp_lbu (a := D + BitVec.ofNat 64 i) (by decide) (by rw [h.s6]; exact BitVec.add_zero _) i₁
    fun s₂ u₂ => ?_
  refine wp_lbu (a := K + BitVec.ofNat 64 i) (by decide)
    (by rw [u₂.other _ (by decide), h.t2]; exact BitVec.add_zero _) (by rw [u₂.rd, u₂.wr]; exact i₂)
    fun s₃ u₃ => ?_
  refine wp_xor fun s₄ u₄ => ?_
  refine wp_sb (a := D + BitVec.ofNat 64 i) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h.s6]
        exact BitVec.add_zero _)
    (by rw [u₄.wr, u₃.wr, u₂.wr]; exact o₁) fun s₅ g₅ => ?_
  refine wp_addi (by decide) fun s₆ u₆ => wp_addi (by decide) fun s₇ u₇ =>
    wp_subi (imm := 1) (by decide) fun s₈ u₈ => wp_subi (imm := 1) (by decide) fun s₉ u₉ =>
    WP.block_nil ?_
  have hk : s₁.mem (K + BitVec.ofNat 64 i) = s.mem (K + BitVec.ofNat 64 i) :=
    h.frame _ fun r hr hcont => by
      simp only [List.mem_singleton] at hr; subst hr
      exact not_contains hp.sep hi hcont
  have hv : (s₄.gpr .t3).setWidth 8 = s.mem (D + BitVec.ofNat 64 i) ^^^ s.mem (K + BitVec.ofNat 64 i) := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₃.gpr, u₂.mem, xor_setWidth, h.data _ hi, hk]
    simp
  have hm : s₉.mem = s₁.mem.writeW (D + BitVec.ofNat 64 i)
      (s.mem (D + BitVec.ofNat 64 i) ^^^ s.mem (K + BitVec.ofNat 64 i)) := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, g₅.mem, hv, u₄.mem, u₃.mem, u₂.mem]
  have g : ∀ r, r ∉ bw → s₉.gpr r = s₁.gpr r := fun r hr => by
    have : r ≠ .t2 ∧ r ≠ .a2 ∧ r ≠ .t3 ∧ r ≠ .t4 ∧ r ≠ .s6 ∧ r ≠ .s7 := by
      simp only [bw, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; exact hr
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := this
    rw [u₉.other r h₆, u₈.other r h₂, u₇.other r h₁, u₆.other r h₅, g₅.gpr, u₄.other r h₃, u₃.other r h₄,
      u₂.other r h₃]
  have hfd : Frame [⟨D, c⟩] s₁.mem s₉.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ cd
  refine ⟨?_, ?_, ?_, ?_, fun r hr => by rw [g r hr]; exact h.keep r hr,
    by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, g₅.rd, u₄.rd, u₃.rd, u₂.rd, h.rd],
    by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, g₅.wr, u₄.wr, u₃.wr, u₂.wr, h.wr],
    by rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, g₅.sp, u₄.sp, u₃.sp, u₂.sp, h.sp],
    fun k hk' => ?_, h.frame.trans hfd⟩
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h.s6, add_ofNat]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h.t2, add_ofNat]
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h.a2, sub_ofNat (by omega),
      Nat.sub_sub]
  · rw [u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), h.s7, BitVec.sub_sub,
      BitVec.ofNat_add]
  · rw [hm, WriteBytes.writeW8_apply]
    by_cases he : k = i
    · subst he; simp
    · simp only [Offset.add_ofNat_ne D (by omega) (by omega) he, ite_false]
      rw [h.data k hk']
      by_cases h₁ : k < i
      · simp [h₁, show k < i + 1 by omega]
      · simp [h₁, show ¬ k < i + 1 by omega]

theorem xorBytes_eq : xorBytes = .ite (.zero .a2) (.block []) (.loop (.block body) (.nonzero .a2)) := rfl

theorem LInv.zero {s : State} {D K : Addr} {c : Nat} (hp : BPre s D K c) : LInv s D K c 0 s :=
  ⟨by rw [hp.s6]; simp, by rw [hp.t2]; simp, by rw [hp.a2, Nat.sub_zero], by simp,
    fun _ _ => rfl, rfl, rfl, rfl, fun k _ => by simp, Frame.refl _ _⟩

theorem LInv.post {s : State} {D K : Addr} {c : Nat} {s' : State} (h : LInv s D K c c s') : BPost s D K c s' :=
  ⟨h.s6, h.s7, h.keep, h.rd, h.wr, h.sp, fun k hk => by rw [h.data k hk]; simp [hk], h.frame⟩

theorem xorBytes_ok {s : State} {D K : Addr} {c : Nat} (hp : BPre s D K c) :
    WP isa xorBytes s (BPost s D K c) := by
  have hc := hp.c_lt
  rw [xorBytes_eq]
  refine WP.ite (decide (c = 0)) (eval_zero_ofNat _ _ (by omega) hp.a2)
    (fun h0 => WP.block_nil (M := isa) ?_) (fun h0 => ?_)
  · simp only [decide_eq_true_eq] at h0; subst h0; exact (LInv.zero hp).post
  · simp only [decide_eq_false_iff_not] at h0
    let Inv : Nat → State → Prop := fun n s' => ∃ i, n = c - i ∧ i < c ∧ LInv s D K c i s'
    have hstep : ∀ n s', Inv n s' → WP isa (.block body) s' (fun s'' =>
        (isa.eval (.nonzero .a2) s'' = some false ∧ BPost s D K c s'') ∨
        (isa.eval (.nonzero .a2) s'' = some true ∧ ∃ n' < n, Inv n' s'')) := by
      rintro n s' ⟨i, rfl, hi, hI⟩
      refine WP.mono (byte_step hp hi hI) fun s'' h' => ?_
      have hz := eval_nonzero_ofNat s'' .a2 (by omega) h'.a2
      by_cases hl : i + 1 = c
      · exact .inl ⟨by rw [hz]; simp; omega, LInv.post (hl ▸ h')⟩
      · exact .inr ⟨by rw [hz]; simp; omega, c - (i + 1), by omega, i + 1, rfl, by omega, h'⟩
    exact WP.loop (M := isa) Inv hstep c s ⟨0, by simp, by omega, LInv.zero hp⟩

end VG.Proof.ChaCha20.RISCV64.Stream

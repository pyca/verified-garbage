module

public import VerifiedGarbage.Proof.Rsa.RISCV64.PrivPubCall
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_private_checked` on RISC-V: the comparison

The public operation's status kept in the frame (`cmpArgs_ok`, into
`AtLoop`), then the comparison of `out` with the input (`compare_ok`): the
OR of their bytes' XORs (`cmpAcc`), zero exactly if they are equal.
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Priv

open VG VG.RISCV64 VG.Impl.Rsa.RISCV64.Priv VG.RISCV64.RegUpd

/-- `Late` is kept by a write of a word of the frame apart from the slots. -/
theorem Late.store {s t : State} (M : Late s t) {d : Nat} (hd : oRa + 8 ≤ d ∨ d + 8 ≤ oSave)
    (hd' : d + 8 ≤ frameBytes)
    (v : BitVec 64) {u : State} (hg : ∀ r ∈ preserved, u.gpr r = t.gpr r) (hsp : u.sp = t.sp)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) (hm : u.mem = t.mem.writeW (fb s + BitVec.ofNat 64 d) v) :
    Late s u := by
  have fw : Frame [⟨fb s + BitVec.ofNat 64 d, 8⟩] t.mem u.mem := by
    rw [hm]; exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hsp.trans M.sp, hrd.trans M.rd, hwr.trans M.wr, (hg _ (by decide)).trans M.s1,
    (hg _ (by decide)).trans M.s2, (hg _ (by decide)).trans M.s3, (hg _ (by decide)).trans M.s4,
    (hg _ (by decide)).trans M.s5, (hg _ (by decide)).trans M.s6,
    fun r hr => (hg r (by revert r; decide)).trans (M.hi r hr), ?_,
    M.sv.frame fw fun p hp r hr => by
      rw [List.mem_singleton.mp hr]
      have := saved_offs p hp
      simp only [oSave, oRa] at this hd
      exact Offset.disjoint _ (by omega) (by unfold frameBytes at hd'; omega)
        (by unfold frameBytes at hd'; omega)⟩
  rw [hm]; exact M.mem.writeW (List.mem_cons_self ..) _ (frame_contains s hd')

/-- `m^e mod n` in `out` and the public operation's status kept in the
frame, if `n`'s values are valid. -/
abbrev pubOutM (s u : State) : Prop :=
  ∀ ws, Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) = some ws →
    Spec.Rsa.written u.mem (s.gpr .a0) (s.gpr .a3).toNat
      ((u.mem.readW (fb s + BitVec.ofNat 64 oEs) 64).setWidth 32)
      (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat)
        (Spec.Rsa.bytesAt u.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .a3).toNat))

/-- At the comparison. -/
structure AtLoop (s u : State) : Prop extends Late s u where
  crt : crtOutM s u
  pub : pubOutM s u
  t2 : u.gpr .t2 = s.gpr .a0
  t3 : u.gpr .t3 = s.gpr .a6
  t4 : u.gpr .t4 = 0
  t5 : u.gpr .t5 = s.gpr .a3

theorem cmpArgs_ok {s t : State} (h : PreP s) (A : AtCmp s t) :
    WP isa (.block cmpArgs) t (AtLoop s) := by
  have hk := h.k2
  have ho : InRegions t.wr (fb s + BitVec.ofNat 64 160) 8 := by
    rw [A.wr]; exact in_fr s _ (by decide)
  have hal : (fb s + BitVec.ofNat 64 160).toNat % 8 = 0 := fb_al8 h (by decide)
  refine WP.mono (WP.rdwr (WP.keep [.t0, .t2, .t3, .t4, .t5] (Q := fun u =>
    u.gpr .t2 = s.gpr .a0 ∧ u.gpr .t3 = s.gpr .a6 ∧ u.gpr .t4 = 0 ∧ u.gpr .t5 = s.gpr .a3 ∧
      u.mem = t.mem.writeW (fb s + BitVec.ofNat 64 oEs) (t.gpr .a0)) ?_ (by rfl) (by rfl)))
    fun u ⟨⟨⟨u2, u3, u4, u5, um⟩, k⟩, urd, uwr, usp⟩ => ?_
  · brun [cmpArgs, exec_addSp, A.sp, BitVec.add_zero, ho, hal, oEs, mov, A.s1, A.s6, A.s3,
      exec_li (d := .t4) (imm := 0) (by decide)]
    rfl
  · have fw : Frame [⟨fb s + BitVec.ofNat 64 oEs, 8⟩] t.mem u.mem := by
      rw [um]; exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have ap : ∀ {d n : Nat}, (d + n ≤ oEs ∨ oEs + 8 ≤ d) → d + n ≤ 2 ^ 64 →
        ∀ r ∈ [(⟨fb s + BitVec.ofNat 64 oEs, 8⟩ : Region)], Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, n⟩ r :=
      fun hd hn r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ hd hn (by decide)
    have hm : Spec.Rsa.bytesAt u.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .a3).toNat =
        Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .a3).toNat :=
      bytes_of_frame (s := t) fw (ap (.inr (by decide)) (by unfold oM; omega)) (by omega)
    have ho' : Spec.Rsa.bytesAt u.mem (s.gpr .a0) (s.gpr .a3).toNat =
        Spec.Rsa.bytesAt t.mem (s.gpr .a0) (s.gpr .a3).toNat :=
      bytes_of_frame (s := t) fw (fun r hr => by
        rw [List.mem_singleton.mp hr, show (⟨s.gpr .a0, (s.gpr .a3).toNat⟩ : Region) = oR s from outR_eq h]
        exact (h.ko.sub_left (frame_sub s (by decide))).symm) (by have := h.wo; rw [h.h1] at this; omega)
    refine ⟨A.store (.inl (by decide)) (by decide) _ (fun r hr => k.gpr (by revert r; decide)) usp urd
      uwr um, ?_, ?_, u2, u3, u4, u5⟩
    · show Spec.Rsa.written _ _ _ _ _
      rw [fw.readW (Region.contains_self _ _) (ap (.inl (by decide)) (by decide)) (by decide)]
      exact written_congr hm A.crt
    · intro ws hw
      have := A.pub ws hw
      rw [← hm] at this
      rw [um, Mem.readW_writeW_self64, ← um]
      exact written_congr ho' this

/-- A byte, as `lbu` loads it. -/
abbrev zb (m : Mem) (a : Addr) : BitVec 64 := (m.read a 1).setWidth 64

/-- The OR of the XORs of the first `j` bytes at `a` and `b`. -/
def cmpAcc (m : Mem) (a b : Addr) : Nat → BitVec 64
  | 0 => 0
  | j + 1 => cmpAcc m a b j ||| (zb m (a + BitVec.ofNat 64 j) ^^^ zb m (b + BitVec.ofNat 64 j))

theorem zb_lt (m : Mem) (a : Addr) : (zb m a).toNat < 2 ^ 8 := by
  simp only [zb, BitVec.toNat_setWidth]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (m.read a 1).isLt

theorem cmpAcc_lt (m : Mem) (a b : Addr) (j : Nat) : (cmpAcc m a b j).toNat < 2 ^ 8 := by
  induction j with
  | zero => simp [cmpAcc]
  | succ j ih =>
    simp only [cmpAcc, BitVec.toNat_or, BitVec.toNat_xor]
    exact Nat.or_lt_two_pow ih (Nat.xor_lt_two_pow (zb_lt _ _) (zb_lt _ _))

theorem zb_xor_eq_zero (m : Mem) (a b : Addr) : zb m a ^^^ zb m b = 0#64 ↔ m a = m b := by
  rw [BitVec.xor_eq_zero_iff]
  constructor
  · intro h
    rw [← Proof.Bignum.RISCV64.read_one' m a, ← Proof.Bignum.RISCV64.read_one' m b]
    exact congrArg (BitVec.setWidth 8) h
  · intro h
    simp only [zb]
    congr 1
    show (m.read (a + 1) 0 ++ m a) = (m.read (b + 1) 0 ++ m b)
    rw [h]; simp only [Mem.read]

theorem cmpAcc_eq_zero (m : Mem) (a b : Addr) (j : Nat) :
    cmpAcc m a b j = 0#64 ↔ ∀ i < j, m (a + BitVec.ofNat 64 i) = m (b + BitVec.ofNat 64 i) := by
  induction j with
  | zero => simp [cmpAcc]
  | succ j ih =>
    rw [cmpAcc, BitVec.or_eq_zero_iff, ih, zb_xor_eq_zero]
    constructor
    · rintro ⟨h, h'⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h i hi
      · exact h'
    · intro h; exact ⟨fun i hi => h i (by omega), h j (by omega)⟩

theorem add_ofNat_one (p : Addr) (j : Nat) :
    p + BitVec.ofNat 64 j + BitVec.ofNat 64 1 = p + BitVec.ofNat 64 (j + 1) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- The comparison: the OR of the XORs of `out`'s bytes and the input's in `t4`. -/
theorem compare_ok {s t : State} (h : PreP s) (A : AtLoop s t) :
    WP isa compare t fun u => u.gpr .t4 = cmpAcc t.mem (s.gpr .a0) (s.gpr .a6) (s.gpr .a3).toNat ∧
      u.mem = t.mem ∧ Keep [.a1, .a2, .t2, .t3, .t4, .t5] t u := by
  have hk := h.k2
  have hk1 := h.k1
  let Inv : Nat → State → Prop := fun j u =>
    u.gpr .t2 = s.gpr .a0 + BitVec.ofNat 64 j ∧ u.gpr .t3 = s.gpr .a6 + BitVec.ofNat 64 j ∧
      u.gpr .t4 = cmpAcc t.mem (s.gpr .a0) (s.gpr .a6) j ∧ u.mem = t.mem ∧
      Keep [.a1, .a2, .t2, .t3, .t4, .t5] t u
  refine WP.mono (Proof.Bignum.RISCV64.wp_countdown (N := (s.gpr .a3).toNat) (by omega) (by omega) Inv
    (fun j hj u ⟨u2, u3, u4, um, uk⟩ hc => ?_)
    ⟨by rw [A.t2]; simp, by rw [A.t3]; simp, A.t4, rfl, Keep.refl _ _⟩ (by rw [A.t5]; simp))
    fun u ⟨_, _, u4, um, uk⟩ => ⟨u4, um, uk⟩
  have io : InRegions (u.rd ++ u.wr) (s.gpr .a0 + BitVec.ofNat 64 j) 1 := by
    rw [uk.2.1, uk.2.2, A.wr, h.hwr]
    exact ⟨oR s, by simp, Offset.contains_base _ (by rw [h.h1]; omega) (by omega)⟩
  have ii : InRegions (u.rd ++ u.wr) (s.gpr .a6 + BitVec.ofNat 64 j) 1 := by
    rw [uk.2.1, A.rd, h.hrd]
    exact ⟨iR s, by simp, Offset.contains_base _ (by rw [h.h7]; omega) (by omega)⟩
  refine WP.mono (WP.keep [.a1, .a2, .t2, .t3, .t4, .t5] (Q := fun u' =>
    u'.gpr .t2 = s.gpr .a0 + BitVec.ofNat 64 (j + 1) ∧ u'.gpr .t3 = s.gpr .a6 + BitVec.ofNat 64 (j + 1) ∧
      u'.gpr .t4 = cmpAcc t.mem (s.gpr .a0) (s.gpr .a6) (j + 1) ∧ u'.mem = u.mem ∧
      u'.gpr .t5 = u.gpr .t5 - BitVec.ofNat 64 1) ?_ (by rfl) (by rfl)) fun u' ⟨⟨v2, v3, v4, vm, v5⟩, k⟩ =>
    ⟨⟨v2, v3, v4, vm.trans um, uk.trans k |>.mono fun r hr => (List.mem_append.mp hr).elim id id⟩, v5⟩
  brun [u2, u3, u4, um, io, ii, BitVec.add_zero, add_ofNat_one, cmpAcc]

end VG.Proof.Rsa.RISCV64.Priv

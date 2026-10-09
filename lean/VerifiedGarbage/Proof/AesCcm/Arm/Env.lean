import VerifiedGarbage.Proof.AesCcm.Arm.Contract
import VerifiedGarbage.Proof.AesCcm.Ctr
import VerifiedGarbage.Proof.AesGcm.Arm.Fn
import VerifiedGarbage.Impl.AesCcm.Arm

/-!
# AES-CCM on ARMv7: where everything is

Untrusted: everything here is checked by Lean. The key schedule (240 bytes
at `k`), the working space (2560 bytes at `w`) and the 16 bytes of stack
below `sp` that the calls use (`Lay`), all 32-bit pointers; what a state may
access (`Perm`); and the registers holding `k`, `w`, the number of rounds
and `q − 1`, and the stack pointer (`Env`). The pieces write the parts of
`W` in `mutR` (and the data, and the stack below `sp`), so our caller's
registers saved in `W` stay as the entry left them.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.Arm

open VG VG.Arm
open VG.Proof.AesGcm.Arm (covers_off in_off in_left covers_left covers_of_mem covers_prefix)

/-- The 16 bytes below `sp`. -/
abbrev blw (sp : BitVec 32) : Region := ⟨State.addr sp - BitVec.ofNat 64 16, 16⟩

/-- The key schedule, `W` and the stack below `sp` used by the calls. -/
structure Lay (k w sp : BitVec 32) : Prop where
  kw : k.toNat + 240 ≤ 2 ^ 32
  ww : w.toNat + 2560 ≤ 2 ^ 32
  sp16 : 16 ≤ sp.toNat
  k_w : (⟨State.addr k, 240⟩ : Region).Disjoint ⟨State.addr w, 2560⟩
  stk_k : (blw sp).Disjoint ⟨State.addr k, 240⟩
  stk_w : (blw sp).Disjoint ⟨State.addr w, 2560⟩

/-- What a state may access. -/
structure Perm (k w : BitVec 32) (s : State) : Prop where
  k : Covers [⟨State.addr k, 240⟩] (s.rd ++ s.wr)
  w : Covers [⟨State.addr w, 2560⟩] s.wr

/-- The registers holding the rounds `R`, the key schedule, `q − 1` and `W`,
the stack pointer, and what the state may access. -/
structure Env (k w sp : BitVec 32) (R q1 : Nat) (s : State) : Prop where
  r8 : s.gpr .r8 = BitVec.ofNat 32 R
  r9 : s.gpr .r9 = k
  r10 : s.gpr .r10 = BitVec.ofNat 32 q1
  r11 : s.gpr .r11 = w
  sp : s.sp = sp
  perm : Perm k w s

theorem Perm.of_eq {k w : BitVec 32} {s s' : State} (h : Perm k w s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Perm k w s' := ⟨by rw [hrd, hwr]; exact h.k, by rw [hwr]; exact h.w⟩

/-- An environment, after code that keeps `r8`–`r11`, `sp` and the permissions. -/
theorem Env.keep {k w sp : BitVec 32} {R q1 : Nat} {s s' : State} (h : Env k w sp R q1 s)
    (hg : ∀ r ∈ [Reg.r8, .r9, .r10, .r11], s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Env k w sp R q1 s' :=
  ⟨by rw [hg _ (by simp), h.r8], by rw [hg _ (by simp), h.r9], by rw [hg _ (by simp), h.r10],
    by rw [hg _ (by simp), h.r11], by rw [hsp, h.sp], h.perm.of_eq hrd hwr⟩

/-- After code that keeps the callee-saved registers (but `lr`). -/
theorem Env.of_saved {k w sp : BitVec 32} {R q1 : Nat} {s s' : State} (h : Env k w sp R q1 s)
    (hg : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Env k w sp R q1 s' :=
  h.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hsp hrd hwr

namespace Lay

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 2560) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 2560⟩ :=
  Offset.sub_base _ h

variable {k w sp : BitVec 32} (L : Lay k w sp)
include L

/-- An offset into `W`, as a 64-bit address. -/
theorem wA {d : Nat} (hd : d < 2560) : State.addr (w + BitVec.ofNat 32 d) = State.addr w + BitVec.ofNat 64 d :=
  addr_add (by have := L.ww; omega_arith)

/-- Parts of `W` are disjoint. -/
theorem w_w {a n d m : Nat} (h : a + n ≤ d ∨ d + m ≤ a) (ha : a + n ≤ 2560) (hd : d + m ≤ 2560) :
    (⟨State.addr w + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 d, m⟩ :=
  Offset.disjoint _ h (by have := L.ww; omega_arith) (by have := L.ww; omega_arith)

theorem w0_w {n d m : Nat} (h : n ≤ d) (hd : d + m ≤ 2560) :
    (⟨State.addr w, n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 d, m⟩ := by
  have := L.w_w (a := 0) (n := n) (d := d) (m := m) (.inl (by omega_arith)) (by omega_arith) hd
  simpa using this

theorem wN {d : Nat} (hd : d < 2560) : (w + BitVec.ofNat 32 d).toNat = w.toNat + d := by
  have := L.ww
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]

theorem stk_w' {a n : Nat} (ha : a + n ≤ 2560) : (blw sp).Disjoint ⟨State.addr w + BitVec.ofNat 64 a, n⟩ :=
  L.stk_w.sub_right (wSub ha)

theorem k_w' {a n : Nat} (ha : a + n ≤ 2560) :
    (⟨State.addr k, 240⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 a, n⟩ :=
  L.k_w.sub_right (wSub ha)

end Lay

namespace Perm

variable {k w : BitVec 32} {s : State} (P : Perm k w s)
include P

theorem wW {d n : Nat} (h : d + n ≤ 2560) : InRegions s.wr (State.addr w + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 2560) : InRegions (s.rd ++ s.wr) (State.addr w + BitVec.ofNat 64 d) n :=
  in_left (P.wW h)

theorem wC {d n : Nat} (h : d + n ≤ 2560) : Covers [⟨State.addr w + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

end Perm

/-! ## Buffers -/

/-- A buffer of `n` bytes at the 32-bit pointer `D` that the code may read,
apart from `W`, the key schedule and the stack below `sp`. -/
structure Buf (w sp : BitVec 32) (s : State) (D : BitVec 32) (n : Nat) : Prop where
  rd : Covers [⟨State.addr D, n⟩] (s.rd ++ s.wr)
  fit : D.toNat + n ≤ 2 ^ 32
  w : (⟨State.addr D, n⟩ : Region).Disjoint ⟨State.addr w, 2560⟩
  stk : (blw sp).Disjoint ⟨State.addr D, n⟩

namespace Buf

variable {w sp : BitVec 32} {s : State} {D : BitVec 32} {n : Nat} (h : Buf w sp s D n)
include h

theorem lt32 : n ≤ 2 ^ 32 := by have := h.fit; omega_arith

theorem lt : n < 2 ^ 64 := by have := h.fit; omega_arith

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Buf w sp s' D n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

/-- Byte `j` of the buffer, for `j < n`, as a 64-bit address. -/
theorem addr {j : Nat} (hj : j < n) : State.addr (D + BitVec.ofNat 32 j) = State.addr D + BitVec.ofNat 64 j :=
  addr_add (by have := h.fit; omega_arith)

theorem toNat_add {j : Nat} (hj : j < n) : (D + BitVec.ofNat 32 j).toNat = D.toNat + j := by
  have := h.fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : Buf w sp s D k where
  rd := covers_prefix h.rd hk
  fit := by have := h.fit; omega_arith
  w := h.w.sub_left (Region.sub_prefix hk)
  stk := h.stk.sub_right (Region.sub_prefix hk)

/-- The `k` (at least one) bytes from `j` on. -/
theorem sub {j k : Nat} (hjk : j + k ≤ n) (hk : 0 < k) : Buf w sp s (D + BitVec.ofNat 32 j) k := by
  have ha := h.addr (j := j) (by omega_arith)
  have hs : Region.Sub ⟨State.addr D + BitVec.ofNat 64 j, k⟩ ⟨State.addr D, n⟩ := Offset.sub_base _ hjk
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ha]; exact covers_off h.rd hjk h.lt
  · rw [h.toNat_add (by omega_arith)]; have := h.fit; omega_arith
  · rw [ha]; exact h.w.sub_left hs
  · rw [ha]; exact h.stk.sub_right hs

end Buf

end VG.Proof.AesCcm.Arm

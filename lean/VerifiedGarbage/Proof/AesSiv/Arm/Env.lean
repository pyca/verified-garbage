import VerifiedGarbage.Proof.AesSiv.Arm.Call
import VerifiedGarbage.Proof.AesCcm.Arm.Callee
import VerifiedGarbage.Proof.AesSiv.Ctr32
import VerifiedGarbage.Proof.Siv.Spec

/-!
# AES-SIV on ARMv7: where everything is

Untrusted: everything here is checked by Lean. The key context (512 bytes
at `c`), the working space (2576 bytes at `w`) and the 16 bytes of stack
below `sp` that the calls use (`Lay`), all 32-bit pointers; what a state may
access (`Perm`); and the registers holding the rounds, `c` and `w`, and the
stack pointer (`Env`). The strings S2V absorbs are buffers the code may read
(`Buf`), and the data one it may also write (`Dat`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm
open VG.Proof.AesGcm.Arm (covers_off in_off in_left covers_left covers_of_mem covers_prefix)
open VG.Proof.AesCcm.Arm (blw)

theorem blw16_eq {s : State} {sp : BitVec 32} (h : s.sp = sp) : Proof.CmacAes.Stream.Arm.blw16 s = blw sp := by
  subst h; rfl

/-- The working space of the functions called. -/
abbrev scrR (w : BitVec 32) : Region := ⟨State.addr w + BitVec.ofNat 64 256, 2176⟩

/-- The key context, `W` and the stack below `sp` used by the calls. -/
structure Lay (c w sp : BitVec 32) : Prop where
  cw : c.toNat + 512 ≤ 2 ^ 32
  ww : w.toNat + 2576 ≤ 2 ^ 32
  sp16 : 16 ≤ sp.toNat
  c_w : (⟨State.addr c, 512⟩ : Region).Disjoint ⟨State.addr w, 2576⟩
  stk_c : (blw sp).Disjoint ⟨State.addr c, 512⟩
  stk_w : (blw sp).Disjoint ⟨State.addr w, 2576⟩

/-- What a state may access. -/
structure Perm (c w : BitVec 32) (s : State) : Prop where
  c : Covers [⟨State.addr c, 512⟩] (s.rd ++ s.wr)
  w : Covers [⟨State.addr w, 2576⟩] s.wr

/-- The registers holding the rounds `R`, the key context and `W`, the stack
pointer, and what the state may access. -/
structure Env (c w sp : BitVec 32) (R : Nat) (s : State) : Prop where
  r9 : s.gpr .r9 = BitVec.ofNat 32 R
  r10 : s.gpr .r10 = c
  r11 : s.gpr .r11 = w
  sp : s.sp = sp
  perm : Perm c w s

theorem Perm.of_eq {c w : BitVec 32} {s s' : State} (h : Perm c w s) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Perm c w s' := ⟨by rw [hrd, hwr]; exact h.c, by rw [hwr]; exact h.w⟩

/-- An environment, after code that keeps `r9`–`r11`, `sp` and the permissions. -/
theorem Env.keep {c w sp : BitVec 32} {R : Nat} {s s' : State} (h : Env c w sp R s)
    (hg : ∀ r ∈ [Reg.r9, .r10, .r11], s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Env c w sp R s' :=
  ⟨by rw [hg _ (by simp), h.r9], by rw [hg _ (by simp), h.r10], by rw [hg _ (by simp), h.r11],
    by rw [hsp, h.sp], h.perm.of_eq hrd hwr⟩

/-- After code that keeps the callee-saved registers (but `lr`). -/
theorem Env.of_saved {c w sp : BitVec 32} {R : Nat} {s s' : State} (h : Env c w sp R s)
    (hg : ∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Env c w sp R s' :=
  h.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hsp hrd hwr

namespace Lay

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 2576) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 2576⟩ :=
  Offset.sub_base _ h

theorem cSub {C : Addr} {d n : Nat} (h : d + n ≤ 512) : Region.Sub ⟨C + BitVec.ofNat 64 d, n⟩ ⟨C, 512⟩ :=
  Offset.sub_base _ h

variable {c w sp : BitVec 32} (L : Lay c w sp)
include L

/-- An offset into `W`, as a 64-bit address. -/
theorem wA {d : Nat} (hd : d < 2576) : State.addr (w + BitVec.ofNat 32 d) = State.addr w + BitVec.ofNat 64 d :=
  addr_add (by have := L.ww; omega)

/-- An offset into the context, as a 64-bit address. -/
theorem cA {d : Nat} (hd : d < 512) : State.addr (c + BitVec.ofNat 32 d) = State.addr c + BitVec.ofNat 64 d :=
  addr_add (by have := L.cw; omega)

/-- Parts of `W` are disjoint. -/
theorem w_w {a n d m : Nat} (h : a + n ≤ d ∨ d + m ≤ a) (ha : a + n ≤ 2576) (hd : d + m ≤ 2576) :
    (⟨State.addr w + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 d, m⟩ :=
  Offset.disjoint _ h (by have := L.ww; omega) (by have := L.ww; omega)

theorem wN {d : Nat} (hd : d < 2576) : (w + BitVec.ofNat 32 d).toNat = w.toNat + d := by
  have := L.ww
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem cN {d : Nat} (hd : d < 512) : (c + BitVec.ofNat 32 d).toNat = c.toNat + d := by
  have := L.cw
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem stk_w' {a n : Nat} (ha : a + n ≤ 2576) : (blw sp).Disjoint ⟨State.addr w + BitVec.ofNat 64 a, n⟩ :=
  L.stk_w.sub_right (wSub ha)

theorem stk_c' {a n : Nat} (ha : a + n ≤ 512) : (blw sp).Disjoint ⟨State.addr c + BitVec.ofNat 64 a, n⟩ :=
  L.stk_c.sub_right (cSub ha)

theorem c_w' {a n b m : Nat} (ha : a + n ≤ 512) (hb : b + m ≤ 2576) :
    (⟨State.addr c + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 b, m⟩ :=
  (L.c_w.sub_left (cSub ha)).sub_right (wSub hb)

theorem c0_w' {n b m : Nat} (ha : n ≤ 512) (hb : b + m ≤ 2576) :
    (⟨State.addr c, n⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 b, m⟩ :=
  (L.c_w.sub_left (Region.sub_prefix ha)).sub_right (wSub hb)

end Lay

namespace Perm

variable {c w : BitVec 32} {s : State} (P : Perm c w s)
include P

theorem wW {d n : Nat} (h : d + n ≤ 2576) : InRegions s.wr (State.addr w + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 2576) : InRegions (s.rd ++ s.wr) (State.addr w + BitVec.ofNat 64 d) n :=
  in_left (P.wW h)

theorem wC {d n : Nat} (h : d + n ≤ 2576) : Covers [⟨State.addr w + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

theorem cR {d n : Nat} (h : d + n ≤ 512) : InRegions (s.rd ++ s.wr) (State.addr c + BitVec.ofNat 64 d) n :=
  in_off P.c h (by decide)

theorem cC {d n : Nat} (h : d + n ≤ 512) : Covers [⟨State.addr c + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  covers_off P.c h (by decide)

theorem c0C {n : Nat} (h : n ≤ 512) : Covers [⟨State.addr c, n⟩] (s.rd ++ s.wr) := covers_prefix P.c h

end Perm

/-! ## Buffers -/

/-- A buffer of `n` bytes at the 32-bit pointer `D` that the code may read,
apart from `W` and the stack below `sp`. -/
structure Buf (w sp : BitVec 32) (s : State) (D : BitVec 32) (n : Nat) : Prop where
  rd : Covers [⟨State.addr D, n⟩] (s.rd ++ s.wr)
  fit : D.toNat + n ≤ 2 ^ 32
  w : (⟨State.addr D, n⟩ : Region).Disjoint ⟨State.addr w, 2576⟩
  stk : (blw sp).Disjoint ⟨State.addr D, n⟩

namespace Buf

variable {w sp : BitVec 32} {s : State} {D : BitVec 32} {n : Nat} (h : Buf w sp s D n)
include h

theorem lt32 : n ≤ 2 ^ 32 := by have := h.fit; omega

theorem lt : n < 2 ^ 64 := by have := h.fit; omega

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Buf w sp s' D n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

/-- Byte `j` of the buffer, for `j < n`, as a 64-bit address. -/
theorem addr {j : Nat} (hj : j < n) : State.addr (D + BitVec.ofNat 32 j) = State.addr D + BitVec.ofNat 64 j :=
  addr_add (by have := h.fit; omega)

theorem toNat_add {j : Nat} (hj : j < n) : (D + BitVec.ofNat 32 j).toNat = D.toNat + j := by
  have := h.fit
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := j) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : Buf w sp s D k where
  rd := covers_prefix h.rd hk
  fit := by have := h.fit; omega
  w := h.w.sub_left (Region.sub_prefix hk)
  stk := h.stk.sub_right (Region.sub_prefix hk)

/-- The `k` (at least one) bytes from `j` on. -/
theorem sub {j k : Nat} (hjk : j + k ≤ n) (hk : 0 < k) : Buf w sp s (D + BitVec.ofNat 32 j) k := by
  have ha := h.addr (j := j) (by omega)
  have hs : Region.Sub ⟨State.addr D + BitVec.ofNat 64 j, k⟩ ⟨State.addr D, n⟩ := Offset.sub_base _ hjk
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ha]; exact covers_off h.rd hjk h.lt
  · rw [h.toNat_add (by omega)]; have := h.fit; omega
  · rw [ha]; exact h.w.sub_left hs
  · rw [ha]; exact h.stk.sub_right hs

end Buf

/-- The data: `n` bytes at `D` that the code may write, apart from `W`, the
key context and the stack below `sp`. -/
structure Dat (c w sp : BitVec 32) (s : State) (D : BitVec 32) (n : Nat) : Prop where
  buf : Buf w sp s D n
  wr : Covers [⟨State.addr D, n⟩] s.wr
  c : (⟨State.addr c, 512⟩ : Region).Disjoint ⟨State.addr D, n⟩

theorem Dat.of_eq {c w sp : BitVec 32} {s s' : State} {D : BitVec 32} {n : Nat} (h : Dat c w sp s D n)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Dat c w sp s' D n :=
  ⟨h.buf.of_eq hrd hwr, by rw [hwr]; exact h.wr, h.c⟩

/-! ## The context's functions outside a frame -/

/-- The PRF and the cipher of a key context outside a frame's regions. -/
theorem ctxMac_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {C : Addr}
    (hd : ∀ r ∈ rs, (⟨C, 512⟩ : Region).Disjoint r) {R : Nat} (hR : 16 * (R + 1) ≤ 240) :
    Spec.Siv.ctxMac m' C R = Spec.Siv.ctxMac m C R := by
  unfold Spec.Siv.ctxMac Spec.Siv.schedCiph
  rw [Proof.Cmac.bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix (by omega))) (by omega),
    Proof.Cmac.bytesAt_frame hf (p := C + 240)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base C (d := 240) (n := 16) (by decide))) (by decide),
    Proof.Cmac.bytesAt_frame hf (p := C + 256)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base C (d := 256) (n := 16) (by decide))) (by decide)]

theorem ctxCiph_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {C : Addr}
    (hd : ∀ r ∈ rs, (⟨C, 512⟩ : Region).Disjoint r) {R : Nat} (hR : 16 * (R + 1) ≤ 240) :
    Spec.Siv.ctxCiph m' C R = Spec.Siv.ctxCiph m C R := by
  unfold Spec.Siv.ctxCiph Spec.Siv.schedCiph
  rw [Proof.Cmac.bytesAt_frame hf (p := C + 272)
    (fun r hr => (hd r hr).sub_left (Offset.sub_base C (d := 272) (n := 16 * (R + 1)) (by omega))) (by omega)]

theorem rounds_le {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) : 16 * (R + 1) ≤ 240 := by
  rcases hR with rfl | rfl | rfl <;> decide

end VG.Proof.AesSiv.Arm

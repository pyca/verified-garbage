import VerifiedGarbage.Proof.AesSiv.X86.Contract
import VerifiedGarbage.Proof.AesGcm.X86.Common
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Impl.AesSiv.X86

/-!
# AES-SIV on x86: where everything is

Untrusted: everything here is checked by Lean. The key context (512 bytes
at `C`), the working space (2576 bytes at `W`) and the 56 bytes of stack
below `SP` that the calls use (`Lay`); what a state may access (`Perm`); the
registers holding `W` and the stack pointer (`Env`); and the public values
the entry keeps in `W` (`Slots`). The pieces write the parts of `W` in
`mutR` (and the data, and the stack below `SP`), so the slots and our
caller's registers saved in `W` stay as the entry left them.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.X86

open VG VG.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 w64_add covers_off in_off in_left covers_left
  covers_cons covers_nil slotv)

/-! ## Covering -/

theorem covers_of_mem {r : Region} {ts : List Region} (h : r ∈ ts) : Covers [r] ts := by
  intro a n ⟨x, hx, hc⟩
  simp only [List.mem_singleton] at hx; subst hx; exact ⟨x, h, hc⟩

/-! ## The regions -/

/-- The key context, `W` and the stack below `SP` used by the calls. -/
structure Lay (C W SP : BitVec 32) : Prop where
  fc : C.toNat + 512 ≤ 2 ^ 32
  fw : W.toNat + 2576 ≤ 2 ^ 32
  sp : 56 ≤ SP.toNat
  c_w : (⟨w64 C, 512⟩ : Region).Disjoint ⟨w64 W, 2576⟩
  stk_c : (below SP 56).Disjoint ⟨w64 C, 512⟩
  stk_w : (below SP 56).Disjoint ⟨w64 W, 2576⟩

/-- What a state may access. -/
structure Perm (C W : BitVec 32) (s : State) : Prop where
  c : Covers [⟨w64 C, 512⟩] (s.rd ++ s.wr)
  w : Covers [⟨w64 W, 2576⟩] s.wr

/-- The registers holding `W` and the stack pointer, and what the state may
access. -/
structure Env (C W SP : BitVec 32) (s : State) : Prop where
  ebp : s.gpr .ebp = W
  esp : s.gpr .esp = SP
  perm : Perm C W s

theorem Perm.of_eq {C W : BitVec 32} {s s' : State} (h : Perm C W s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Perm C W s' := ⟨by rw [hrd, hwr]; exact h.c, by rw [hwr]; exact h.w⟩

/-- An environment, after code that keeps `ebp`, `esp` and the permissions. -/
theorem Env.keep {C W SP : BitVec 32} {s s' : State} (h : Env C W SP s) (hbp : s'.gpr .ebp = s.gpr .ebp)
    (hsp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Env C W SP s' :=
  ⟨by rw [hbp, h.ebp], by rw [hsp, h.esp], h.perm.of_eq hrd hwr⟩

namespace Lay

theorem cSub {C : Addr} {d n : Nat} (h : d + n ≤ 512) : Region.Sub ⟨C + BitVec.ofNat 64 d, n⟩ ⟨C, 512⟩ :=
  Offset.sub_base _ h

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 2576) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 2576⟩ :=
  Offset.sub_base _ h

/-- Parts of `W` are disjoint. -/
theorem w_w {W : BitVec 32} {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 2576) (hd : d + k ≤ 2576) :
    (⟨w64 W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by omega) (by omega)

variable {C W SP : BitVec 32} (L : Lay C W SP)
include L

theorem c_w' {a n d k : Nat} (ha : a + n ≤ 512) (hd : d + k ≤ 2576) :
    (⟨w64 C + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, k⟩ :=
  (L.c_w.sub_left (cSub ha)).sub_right (wSub hd)

theorem stk_w' {a n : Nat} (ha : a + n ≤ 2576) : (below SP 56).Disjoint ⟨w64 W + BitVec.ofNat 64 a, n⟩ :=
  L.stk_w.sub_right (wSub ha)

theorem stk_c' {a n : Nat} (ha : a + n ≤ 512) : (below SP 56).Disjoint ⟨w64 C + BitVec.ofNat 64 a, n⟩ :=
  L.stk_c.sub_right (cSub ha)

theorem aW {o : Nat} (ho : o < 2576) : w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o :=
  w64_add (by have := L.fw; omega)

/-- `aW` for `setWidth`, as the callees' arguments state it. -/
theorem sW {o : Nat} (ho : o < 2576) : (W + BitVec.ofNat 32 o).setWidth 64 = w64 W + BitVec.ofNat 64 o :=
  L.aW ho

theorem nW {o : Nat} (ho : o < 2576) : (W + BitVec.ofNat 32 o).toNat = W.toNat + o :=
  toNat_add32 (by have := L.fw; omega)

theorem aC {o : Nat} (ho : o < 512) : w64 (C + BitVec.ofNat 32 o) = w64 C + BitVec.ofNat 64 o :=
  w64_add (by have := L.fc; omega)

theorem nC {o : Nat} (ho : o < 512) : (C + BitVec.ofNat 32 o).toNat = C.toNat + o :=
  toNat_add32 (by have := L.fc; omega)

end Lay

namespace Perm

variable {C W : BitVec 32} {s : State} (P : Perm C W s)
include P

theorem cR {d n : Nat} (h : d + n ≤ 512) : InRegions (s.rd ++ s.wr) (w64 C + BitVec.ofNat 64 d) n :=
  in_off P.c h (by decide)

theorem wW {d n : Nat} (h : d + n ≤ 2576) : InRegions s.wr (w64 W + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 2576) : InRegions (s.rd ++ s.wr) (w64 W + BitVec.ofNat 64 d) n :=
  in_left (P.wW h)

theorem cC {d n : Nat} (h : d + n ≤ 512) : Covers [⟨w64 C + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  covers_off P.c h (by decide)

theorem wC {d n : Nat} (h : d + n ≤ 2576) : Covers [⟨w64 W + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

end Perm

/-! ## Buffers -/

/-- A buffer of `n` bytes at `D` that the code may read, apart from `W` and
the stack below `SP`. -/
structure Buf (W SP : BitVec 32) (s : State) (D : BitVec 32) (n : Nat) : Prop where
  rd : Covers [⟨w64 D, n⟩] (s.rd ++ s.wr)
  wrap : D.toNat + n ≤ 2 ^ 32
  w : (⟨w64 D, n⟩ : Region).Disjoint ⟨w64 W, 2576⟩
  stk : (below SP 56).Disjoint ⟨w64 D, n⟩

namespace Buf

variable {W SP : BitVec 32} {s : State} {D : BitVec 32} {n : Nat} (h : Buf W SP s D n)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Buf W SP s' D n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

theorem lt : n < 2 ^ 64 := by have := h.wrap; omega

omit h in
/-- The address of byte `k`. -/
theorem ptr {k : Nat} (hk : D.toNat + k < 2 ^ 32) : w64 (D + BitVec.ofNat 32 k) = w64 D + BitVec.ofNat 64 k :=
  w64_add hk

/-- The bytes from `k` on. -/
theorem drop {k : Nat} (hk : k ≤ n) (hw : D.toNat + k < 2 ^ 32) : Buf W SP s (D + BitVec.ofNat 32 k) (n - k) where
  rd := by rw [ptr hw]; exact covers_off h.rd (by omega) h.lt
  wrap := by rw [toNat_add32 hw]; have := h.wrap; omega
  w := by rw [ptr hw]; exact h.w.sub_left (Offset.sub_base _ (by omega))
  stk := by rw [ptr hw]; exact h.stk.sub_right (Offset.sub_base _ (by omega))

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : Buf W SP s D k where
  rd := fun a m ⟨r, hr, hc⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.rd a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩
  wrap := by have := h.wrap; omega
  w := h.w.sub_left (Region.sub_prefix hk)
  stk := h.stk.sub_right (Region.sub_prefix hk)

end Buf

/-! ## The slots -/

/-- The public values the entry keeps in `W` that no piece changes: the key
context, the rounds, the data and its length. -/
structure Slots (W C : BitVec 32) (R : Nat) (D : BitVec 32) (n : Nat) (m : Mem) : Prop where
  ctx : slotv m W Impl.AesSiv.X86.ctxO = C
  rounds : slotv m W Impl.AesSiv.X86.roundsO = BitVec.ofNat 32 R
  data : slotv m W Impl.AesSiv.X86.dataO = D
  len : slotv m W Impl.AesSiv.X86.lenO = BitVec.ofNat 32 n

/-- The parts of `W` the pieces write: the blocks at `[0, 128)`, the CMAC
state and `dbl(D)` at `[144, 176)`, the descriptors' cursor and count at
`[184, 192)`, the variables of the pieces at `[200, 256)`, and from `256` on
(the working space of the functions called, and `D`). -/
abbrev wA (W : BitVec 32) : Region := ⟨w64 W, 128⟩
abbrev wB (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 144, 32⟩
abbrev wV (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 184, 8⟩
abbrev wS (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 200, 56⟩
abbrev wC (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 256, 2320⟩

/-- What the pieces may change: those parts of `W`, the stack below `SP`
and the data. -/
abbrev mutR (W SP D : BitVec 32) (n : Nat) : List Region :=
  [wA W, wB W, wV W, wS W, wC W, below SP 56, ⟨w64 D, n⟩]

/-- The part of `W` at `[d, d + k)`, when it misses the parts the pieces write. -/
theorem kept_mut {C W SP D : BitVec 32} {n : Nat} (L : Lay C W SP)
    (hD : (⟨w64 D, n⟩ : Region).Disjoint ⟨w64 W, 2576⟩) {d k : Nat}
    (hd : 128 ≤ d ∧ d + k ≤ 144 ∨ 176 ≤ d ∧ d + k ≤ 184 ∨ 192 ≤ d ∧ d + k ≤ 200) :
    ∀ r ∈ mutR W SP D n, (⟨w64 W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using Lay.w_w (W := W) (a := d) (n := k) (d := 0) (k := 128) (.inr (by omega)) (by omega) (by decide)
  · exact Lay.w_w (by omega) (by omega) (by decide)
  · exact Lay.w_w (by omega) (by omega) (by decide)
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.stk_w' (by omega)).symm
  · exact (hD.sub_right (Lay.wSub (by omega))).symm

/-- The slots, after code that changes only `mutR`. -/
theorem slots_mut {C W SP D' : BitVec 32} {n' : Nat} (L : Lay C W SP)
    (hD : (⟨w64 D', n'⟩ : Region).Disjoint ⟨w64 W, 2576⟩) {m m' : Mem} (hf : Frame (mutR W SP D' n') m m')
    {R : Nat} {D : BitVec 32} {n : Nat} (S : Slots W C R D n m) : Slots W C R D n m' := by
  have k : ∀ o, (128 ≤ o ∧ o + 4 ≤ 144 ∨ 176 ≤ o ∧ o + 4 ≤ 184 ∨ 192 ≤ o ∧ o + 4 ≤ 200) →
      slotv m' W o = slotv m W o := fun o ho =>
    hf.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (kept_mut L hD ho) (by decide)
  exact ⟨by rw [k _ (by decide)]; exact S.ctx, by rw [k _ (by decide)]; exact S.rounds,
    by rw [k _ (by decide)]; exact S.data, by rw [k _ (by decide)]; exact S.len⟩

end VG.Proof.AesSiv.X86

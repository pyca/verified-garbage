import VerifiedGarbage.Proof.AesCcm.X86.Contract
import VerifiedGarbage.Proof.AesCcm.Ctr
import VerifiedGarbage.Proof.AesGcm.X86.Common
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Impl.AesCcm.X86

/-!
# AES-CCM on x86: where everything is

Untrusted: everything here is checked by Lean. The key schedule (240 bytes
at `K`), the working space (2560 bytes at `W`) and the 56 bytes of stack
below `SP` that the calls use (`Lay`); what a state may access (`Perm`); the
registers holding `W` and the stack pointer (`Env`); and the public values
the entry keeps in `W` (`Slots`). The pieces write the parts of `W` in
`mutR` (and the data, and the stack below `SP`), so the slots and our
caller's registers saved in `W` stay as the entry left them.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 w64_add covers_off in_off in_left covers_left
  covers_cons covers_nil slotv)

/-! ## Covering -/

theorem covers_of_mem {r : Region} {ts : List Region} (h : r ∈ ts) : Covers [r] ts := by
  intro a n ⟨x, hx, hc⟩
  simp only [List.mem_singleton] at hx; subst hx; exact ⟨x, h, hc⟩

theorem covers_append {xs ys ts : List Region} (h₁ : Covers xs ts) (h₂ : Covers ys ts) :
    Covers (xs ++ ys) ts := by
  intro a n ⟨x, hx, hc⟩
  rcases List.mem_append.mp hx with hx | hx
  · exact h₁ a n ⟨x, hx, hc⟩
  · exact h₂ a n ⟨x, hx, hc⟩

/-! ## The regions -/

/-- The key schedule, `W` and the stack below `SP` used by the calls. -/
structure Lay (K W SP : BitVec 32) : Prop where
  fk : K.toNat + 240 ≤ 2 ^ 32
  fw : W.toNat + 2560 ≤ 2 ^ 32
  sp : 56 ≤ SP.toNat
  k_w : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 W, 2560⟩
  stk_k : (below SP 56).Disjoint ⟨w64 K, 240⟩
  stk_w : (below SP 56).Disjoint ⟨w64 W, 2560⟩

/-- What a state may access. -/
structure Perm (K W : BitVec 32) (s : State) : Prop where
  k : Covers [⟨w64 K, 240⟩] (s.rd ++ s.wr)
  w : Covers [⟨w64 W, 2560⟩] s.wr

/-- The registers holding `W` and the stack pointer, and what the state may
access. -/
structure Env (K W SP : BitVec 32) (s : State) : Prop where
  ebp : s.gpr .ebp = W
  esp : s.gpr .esp = SP
  perm : Perm K W s

theorem Perm.of_eq {K W : BitVec 32} {s s' : State} (h : Perm K W s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Perm K W s' := ⟨by rw [hrd, hwr]; exact h.k, by rw [hwr]; exact h.w⟩

/-- An environment, after code that keeps `ebp`, `esp` and the permissions. -/
theorem Env.keep {K W SP : BitVec 32} {s s' : State} (h : Env K W SP s) (hbp : s'.gpr .ebp = s.gpr .ebp)
    (hsp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Env K W SP s' :=
  ⟨by rw [hbp, h.ebp], by rw [hsp, h.esp], h.perm.of_eq hrd hwr⟩

namespace Lay

theorem kSub {K : Addr} {d n : Nat} (h : d + n ≤ 240) : Region.Sub ⟨K + BitVec.ofNat 64 d, n⟩ ⟨K, 240⟩ :=
  Offset.sub_base _ h

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 2560) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 2560⟩ :=
  Offset.sub_base _ h

/-- Parts of `W` are disjoint. -/
theorem w_w {W : BitVec 32} {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 2560) (hd : d + k ≤ 2560) :
    (⟨w64 W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by omega_arith) (by omega_arith)

variable {K W SP : BitVec 32} (L : Lay K W SP)
include L

theorem k_w' {a n d k : Nat} (ha : a + n ≤ 240) (hd : d + k ≤ 2560) :
    (⟨w64 K + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, k⟩ :=
  (L.k_w.sub_left (kSub ha)).sub_right (wSub hd)

theorem stk_w' {a n : Nat} (ha : a + n ≤ 2560) : (below SP 56).Disjoint ⟨w64 W + BitVec.ofNat 64 a, n⟩ :=
  L.stk_w.sub_right (wSub ha)

theorem aW {o : Nat} (ho : o < 2560) : w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o :=
  w64_add (by have := L.fw; omega_arith)

theorem nW {o : Nat} (ho : o < 2560) : (W + BitVec.ofNat 32 o).toNat = W.toNat + o :=
  toNat_add32 (by have := L.fw; omega_arith)

end Lay

namespace Perm

variable {K W : BitVec 32} {s : State} (P : Perm K W s)
include P

theorem kR {d n : Nat} (h : d + n ≤ 240) : InRegions (s.rd ++ s.wr) (w64 K + BitVec.ofNat 64 d) n :=
  in_off P.k h (by decide)

theorem wW {d n : Nat} (h : d + n ≤ 2560) : InRegions s.wr (w64 W + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 2560) : InRegions (s.rd ++ s.wr) (w64 W + BitVec.ofNat 64 d) n :=
  in_left (P.wW h)

theorem kC {d n : Nat} (h : d + n ≤ 240) : Covers [⟨w64 K + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  covers_off P.k h (by decide)

theorem wC {d n : Nat} (h : d + n ≤ 2560) : Covers [⟨w64 W + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

end Perm

/-! ## Buffers -/

/-- A buffer of `n` bytes at `D` that the code may read, apart from `W`, the
key schedule and the stack below `SP`. -/
structure Buf (W SP : BitVec 32) (s : State) (D : BitVec 32) (n : Nat) : Prop where
  rd : Covers [⟨w64 D, n⟩] (s.rd ++ s.wr)
  wrap : D.toNat + n ≤ 2 ^ 32
  w : (⟨w64 D, n⟩ : Region).Disjoint ⟨w64 W, 2560⟩
  stk : (below SP 56).Disjoint ⟨w64 D, n⟩

namespace Buf

variable {W SP : BitVec 32} {s : State} {D : BitVec 32} {n : Nat} (h : Buf W SP s D n)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Buf W SP s' D n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

theorem lt : n < 2 ^ 64 := by have := h.wrap; omega_arith

omit h in
/-- The address of byte `k`. -/
theorem ptr {k : Nat} (hk : D.toNat + k < 2 ^ 32) : w64 (D + BitVec.ofNat 32 k) = w64 D + BitVec.ofNat 64 k :=
  w64_add hk

/-- The bytes from `k` on. -/
theorem drop {k : Nat} (hk : k ≤ n) (hw : D.toNat + k < 2 ^ 32) : Buf W SP s (D + BitVec.ofNat 32 k) (n - k) where
  rd := by rw [ptr hw]; exact covers_off h.rd (by omega_arith) h.lt
  wrap := by rw [toNat_add32 hw]; have := h.wrap; omega_arith
  w := by rw [ptr hw]; exact h.w.sub_left (Offset.sub_base _ (by omega_arith))
  stk := by rw [ptr hw]; exact h.stk.sub_right (Offset.sub_base _ (by omega_arith))

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : Buf W SP s D k where
  rd := fun a m ⟨r, hr, hc⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.rd a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega_arith⟩
  wrap := by have := h.wrap; omega_arith
  w := h.w.sub_left (Region.sub_prefix hk)
  stk := h.stk.sub_right (Region.sub_prefix hk)

end Buf

/-! ## The slots -/

/-- The public values the entry keeps in `W`: the key schedule, the rounds,
the nonce and its length, the associated data and its length, the data and
its length, the tag and its length. -/
structure Slots (W K : BitVec 32) (R : Nat) (N A D T : BitVec 32) (nl al n tl : Nat) (m : Mem) : Prop where
  ctx : slotv m W Impl.AesCcm.X86.ctxO = K
  rounds : slotv m W Impl.AesCcm.X86.roundsO = BitVec.ofNat 32 R
  nonce : slotv m W Impl.AesCcm.X86.nonceO = N
  nlen : slotv m W Impl.AesCcm.X86.nlenO = BitVec.ofNat 32 nl
  aad : slotv m W Impl.AesCcm.X86.aadO = A
  alen : slotv m W Impl.AesCcm.X86.alenO = BitVec.ofNat 32 al
  data : slotv m W Impl.AesCcm.X86.dataO = D
  len : slotv m W Impl.AesCcm.X86.lenO = BitVec.ofNat 32 n
  tl : slotv m W Impl.AesGcm.X86.tglO = BitVec.ofNat 32 tl
  tp : slotv m W Impl.AesGcm.X86.tpO = T

/-- The parts of `W` the pieces write: the blocks at `[0, 112)`, the result of
the comparison at `[176, 180)`, the padded received tag at `[196, 212)`, and
`[240, 2560)` (the padded computed tag, the arguments of the piece running
and the working space of the functions called). -/
abbrev wA (W : BitVec 32) : Region := ⟨w64 W, 112⟩
abbrev wO (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 176, 4⟩
abbrev wT (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 196, 16⟩
abbrev wC (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 240, 2320⟩

/-- What the pieces may change: those parts of `W`, the stack below `SP`
and the data. -/
abbrev mutR (W SP D : BitVec 32) (n : Nat) : List Region :=
  [wA W, wO W, wT W, wC W, below SP 56, ⟨w64 D, n⟩]

/-- The parts of `W` the pieces write. -/
abbrev wR (W SP : BitVec 32) : List Region := [wA W, wO W, wT W, wC W, below SP 56]

theorem wR_mut (W SP D : BitVec 32) (n : Nat) : ∀ r ∈ wR W SP, ∃ r' ∈ mutR W SP D n, Region.Sub r r' :=
  fun r hr => ⟨r, by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with h | h | h | h | h <;>
    simp [h], fun _ h => h⟩

/-- The part of `W` at `[d, d + k)`, when it misses the parts the pieces write. -/
theorem kept_mut {K W SP D : BitVec 32} {n : Nat} (L : Lay K W SP)
    (hD : (⟨w64 D, n⟩ : Region).Disjoint ⟨w64 W, 2560⟩) {d k : Nat}
    (hd : 112 ≤ d ∧ d + k ≤ 176 ∨ 180 ≤ d ∧ d + k ≤ 196 ∨ 212 ≤ d ∧ d + k ≤ 240) :
    ∀ r ∈ mutR W SP D n, (⟨w64 W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using Lay.w_w (W := W) (a := d) (n := k) (d := 0) (k := 112) (.inr (by omega_arith)) (by omega_arith) (by decide)
  · exact Lay.w_w (by omega_arith) (by omega_arith) (by decide)
  · exact Lay.w_w (by omega_arith) (by omega_arith) (by decide)
  · exact Lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  · exact (L.stk_w' (by omega_arith)).symm
  · exact (hD.sub_right (Lay.wSub (by omega_arith))).symm

/-- The slots, after code that changes only `mutR`. -/
theorem slots_mut {K W SP D' : BitVec 32} {n' : Nat} (L : Lay K W SP)
    (hD : (⟨w64 D', n'⟩ : Region).Disjoint ⟨w64 W, 2560⟩) {m m' : Mem} (hf : Frame (mutR W SP D' n') m m')
    {R : Nat} {N A D T : BitVec 32} {nl al n tl : Nat} (S : Slots W K R N A D T nl al n tl m) :
    Slots W K R N A D T nl al n tl m' := by
  have k : ∀ o, (112 ≤ o ∧ o + 4 ≤ 176 ∨ 180 ≤ o ∧ o + 4 ≤ 196 ∨ 212 ≤ o ∧ o + 4 ≤ 240) →
      slotv m' W o = slotv m W o := fun o ho =>
    hf.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (kept_mut L hD ho) (by decide)
  exact ⟨by rw [k _ (by decide)]; exact S.ctx, by rw [k _ (by decide)]; exact S.rounds,
    by rw [k _ (by decide)]; exact S.nonce, by rw [k _ (by decide)]; exact S.nlen,
    by rw [k _ (by decide)]; exact S.aad, by rw [k _ (by decide)]; exact S.alen,
    by rw [k _ (by decide)]; exact S.data, by rw [k _ (by decide)]; exact S.len,
    by rw [k _ (by decide)]; exact S.tl, by rw [k _ (by decide)]; exact S.tp⟩

end VG.Proof.AesCcm.X86

module

public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Callee
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.AesOcb.PPC64LE
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-! ### `AesOcb.PPC64LE.Env`, which this module and modules that import it used -/

section

/-!
# AES-OCB on PPC64LE: where everything is

Untrusted: everything here is checked by Lean. The key context (256 bytes
at `K`) and the working space (512 bytes at `W`) (`Lay`); what a state may
access (`Perm`); the registers the pieces keep (AES-GCM's `frozen`), pinned
to values `V`, among them `K` in `r29` and `W` in `r31`, and the stack
pointer (`Env`); the buffers of the associated data, the nonce and the data
(`Buf`, `DBuf`). The pieces write the parts of `W` in `mutR` (and the data),
so our caller's registers saved in `W` at `[128, 248)` stay as the entry
left them. As on AArch64 (`Proof/AesOcb/AArch64/Env.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.Impl.AesOcb.PPC64LE
open VG.Proof.AesGcm.PPC64LE (frozen covers_off in_off in_left covers_left)

theorem runBlock_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rfl
  | cons x a ih =>
    show (exec x s).bind (runBlock isa (a ++ b)) = ((exec x s).bind (runBlock isa a)).bind (runBlock isa b)
    rw [Option.bind_assoc]
    congr 1
    funext u
    exact ih u

/-- Branching on a register holding `n`, while it is not zero. -/
theorem eval_nonzero {s : State} {r : Reg} {n : Nat} (h : s.gpr r = BitVec.ofNat 64 n) (hn : n < 2 ^ 64) :
    isa.eval (.nonzero .d r) s = some (!decide (n = 0)) := by
  show some _ = _
  simp only [State.read, Size.bits, BitVec.setWidth_eq, h]
  by_cases h0 : n = 0
  · subst h0; rfl
  · have : BitVec.ofNat 64 n ≠ 0 := fun e => h0 ((Proof.AesGcm.PPC64LE.ofNat_eq_zero hn).mp e)
    simp only [h0, decide_false, Bool.not_false]
    exact congrArg some (bne_iff_ne.mpr this)

/-! ## The regions -/

/-- The key context and `W`. -/
structure Lay (K W : Addr) : Prop where
  kw : K.toNat + 256 ≤ 2 ^ 64
  ww : W.toNat + 512 ≤ 2 ^ 64
  k_w : (⟨K, 256⟩ : Region).Disjoint ⟨W, 512⟩

/-- What a state may access. -/
structure Perm (K W : Addr) (s : State) : Prop where
  k : Covers [⟨K, 256⟩] (s.rd ++ s.wr)
  w : Covers [⟨W, 512⟩] s.wr

/-- The registers `frozen` hold their values `V`, the stack pointer is `sp`,
and the state may access the key context and `W` (at `V r29` and `V r31`). -/
structure Env (V : Reg → BitVec 64) (sp : Addr) (s : State) : Prop where
  fr : ∀ r ∈ frozen, s.gpr r = V r
  sp : s.sp = sp
  perm : Perm (V .r29) (V .r31) s

theorem Perm.of_eq {K W : Addr} {s s' : State} (h : Perm K W s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Perm K W s' := ⟨by rw [hrd, hwr]; exact h.k, by rw [hwr]; exact h.w⟩

section
variable {V : Reg → BitVec 64} {sp : Addr} {s : State} (h : Env V sp s)
include h

theorem Env.r19 : s.gpr .r19 = V .r19 := h.fr _ (by decide)
theorem Env.r20 : s.gpr .r20 = V .r20 := h.fr _ (by decide)
theorem Env.r21 : s.gpr .r21 = V .r21 := h.fr _ (by decide)
theorem Env.r22 : s.gpr .r22 = V .r22 := h.fr _ (by decide)
theorem Env.r23 : s.gpr .r23 = V .r23 := h.fr _ (by decide)
theorem Env.r27 : s.gpr .r27 = V .r27 := h.fr _ (by decide)
theorem Env.r28 : s.gpr .r28 = V .r28 := h.fr _ (by decide)
theorem Env.r29 : s.gpr .r29 = V .r29 := h.fr _ (by decide)
theorem Env.r31 : s.gpr .r31 = V .r31 := h.fr _ (by decide)

/-- An environment, after code that keeps the frozen registers, `sp` and the
permissions. -/
theorem Env.keep {s' : State} (hg : ∀ r ∈ frozen, s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Env V sp s' :=
  ⟨fun r hr => (hg r hr).trans (h.fr r hr), hsp.trans h.sp, h.perm.of_eq hrd hwr⟩

/-- An environment, after code that writes only the registers `rs`. -/
theorem Env.others {s' : State} {rs : List Reg} (hg : ∀ r, r ∉ rs → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hd : ∀ r ∈ frozen, r ∉ rs := by decide) : Env V sp s' :=
  h.keep (fun r hr => hg r (hd r hr)) hsp hrd hwr

/-- An environment, after a call. -/
theorem Env.of_saved {s' : State} (hg : ∀ r ∈ preserved, s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Env V sp s' :=
  h.keep (fun r hr => hg r (Proof.AesGcm.PPC64LE.frozen_preserved r hr)) hsp hrd hwr

end

namespace Lay

theorem kSub {K : Addr} {d n : Nat} (h : d + n ≤ 256) : Region.Sub ⟨K + BitVec.ofNat 64 d, n⟩ ⟨K, 256⟩ :=
  Offset.sub_base _ h

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 512) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 512⟩ :=
  Offset.sub_base _ h

variable {K W : Addr} (L : Lay K W)
include L

/-- Parts of `W` are disjoint. -/
theorem w_w {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 512) (hd : d + k ≤ 512) :
    (⟨W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by have := L.ww; omega_using [ha]) (by have := L.ww; omega_using [hd])

theorem k_w' {a n d k : Nat} (ha : a + n ≤ 256) (hd : d + k ≤ 512) :
    (⟨K + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, k⟩ :=
  (L.k_w.sub_left (kSub ha)).sub_right (wSub hd)

/-- `W + d`, as a number. -/
theorem toNat_w {d : Nat} (hd : d < 512) : (W + BitVec.ofNat 64 d).toNat = W.toNat + d := by
  have := L.ww
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_using [hd]), Nat.mod_eq_of_lt (by omega_using [hd, this])]

end Lay

namespace Perm

variable {K W : Addr} {s : State} (P : Perm K W s)
include P

theorem kR {d n : Nat} (h : d + n ≤ 256) : InRegions (s.rd ++ s.wr) (K + BitVec.ofNat 64 d) n :=
  in_off P.k h (by decide)

theorem wW {d n : Nat} (h : d + n ≤ 512) : InRegions s.wr (W + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 512) : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 d) n :=
  in_left (P.wW h)

theorem wC {d n : Nat} (h : d + n ≤ 512) : Covers [⟨W + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

end Perm

/-! ## Buffers -/

/-- A buffer of `n` bytes at `D` that the code may read, apart from `W`. -/
structure Buf (W : Addr) (s : State) (D : Addr) (n : Nat) : Prop where
  rd : Covers [⟨D, n⟩] (s.rd ++ s.wr)
  lt : n < 2 ^ 64
  wrap : D.toNat + n ≤ 2 ^ 64
  w : (⟨D, n⟩ : Region).Disjoint ⟨W, 512⟩

namespace Buf

variable {W : Addr} {s : State} {D : Addr} {n : Nat} (h : Buf W s D n)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Buf W s' D n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

/-- The bytes from `k` on. -/
theorem drop {k : Nat} (hk : k ≤ n) : Buf W s (D + BitVec.ofNat 64 k) (n - k) where
  rd := covers_off h.rd (by omega_using [hk]) h.lt
  lt := by have := h.lt; omega_using [this]
  wrap := by
    have := h.wrap
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by have := h.lt; omega_using [hk, this])]
    have := Nat.mod_le (D.toNat + k) (2 ^ 64)
    omega_arith
  w := h.w.sub_left (Offset.sub_base D (by omega_using [hk]))

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : Buf W s D k where
  rd := fun a m ⟨r, hr, hc⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.rd a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega_using [hk, hc]⟩
  lt := by have := h.lt; omega_using [hk, this]
  wrap := by have := h.wrap; omega_using [hk, this]
  w := h.w.sub_left (Region.sub_prefix hk)

/-- Bytes `[a, a + k)`. -/
theorem slice {a k : Nat} (hk : a + k ≤ n) : Buf W s (D + BitVec.ofNat 64 a) k :=
  (h.drop (k := a) (by omega_using [hk])).take (by omega_using [hk])

end Buf

/-- The data: a buffer that the code may also write, apart from the key
context. -/
structure DBuf (K W : Addr) (s : State) (D : Addr) (n : Nat) : Prop extends Buf W s D n where
  wr : Covers [⟨D, n⟩] s.wr
  k : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩

namespace DBuf

variable {K W : Addr} {s : State} {D : Addr} {n : Nat} (h : DBuf K W s D n)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : DBuf K W s' D n :=
  { h.toBuf.of_eq hrd hwr with wr := by rw [hwr]; exact h.wr, k := h.k }

/-- Bytes `[a, a + k)`. -/
theorem slice {a k : Nat} (hk : a + k ≤ n) : DBuf K W s (D + BitVec.ofNat 64 a) k where
  toBuf := h.toBuf.slice hk
  wr := fun x m hx => covers_off h.wr (d := a) (n := k) hk h.lt x m hx
  k := h.k.sub_right ((Offset.sub_base D (by omega_using [hk])))

end DBuf

/-! ## What the pieces write -/

/-- The parts of `W` the pieces write: `[0, 128)` and `[256, 512)`, around
our caller's registers. -/
abbrev wA (W : Addr) : Region := ⟨W, 128⟩
abbrev wB (W : Addr) : Region := ⟨W + BitVec.ofNat 64 256, 256⟩

/-- What the pieces may change: those parts of `W` and the data. -/
abbrev mutR (W D : Addr) (n : Nat) : List Region := [wA W, wB W, ⟨D, n⟩]

theorem sub_wA {W : Addr} {d k : Nat} (h : d + k ≤ 128) : Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ (wA W) := by
  simpa using Offset.sub W (d := d) (n := k) (e := 0) (k := 128) (by omega_using []) (by omega_using [h])

theorem sub_wB {W : Addr} {d k : Nat} (h₁ : 256 ≤ d) (h : d + k ≤ 512) :
    Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ (wB W) := Offset.sub W (by omega_using [h₁]) (by omega_using [h])

/-- A part of `W` within `[0, 128)`, as a part the pieces may write. -/
theorem in_mutA {W D : Addr} {n d k : Nat} (h : d + k ≤ 128) :
    ∃ r' ∈ mutR W D n, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r' := ⟨_, List.mem_cons_self .., sub_wA h⟩

/-- A part of `W` from 256 on, as a part the pieces may write. -/
theorem in_mutB {W D : Addr} {n d k : Nat} (h₁ : 256 ≤ d) (h : d + k ≤ 512) :
    ∃ r' ∈ mutR W D n, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), sub_wB h₁ h⟩

/-- A part of `W`, as a part the pieces may write. -/
theorem in_mutW {W D : Addr} {n d k : Nat} (h : d + k ≤ 128 ∨ (256 ≤ d ∧ d + k ≤ 512)) :
    ∃ r' ∈ mutR W D n, Region.Sub ⟨W + BitVec.ofNat 64 d, k⟩ r' := by
  rcases h with h | ⟨h₁, h₂⟩
  · exact in_mutA h
  · exact in_mutB h₁ h₂

/-- The data, as a part the pieces may write. -/
theorem in_mutD {W D : Addr} {n : Nat} {r : Region} (h : Region.Sub r ⟨D, n⟩) :
    ∃ r' ∈ mutR W D n, Region.Sub r r' := ⟨_, by simp, h⟩

/-- The key context misses the parts the pieces write. -/
theorem k_mut {K W D : Addr} {n : Nat} (L : Lay K W) (hD : (⟨K, 256⟩ : Region).Disjoint ⟨D, n⟩) :
    ∀ r ∈ mutR W D n, (⟨K, 256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.k_w.sub_right (Region.sub_prefix (by decide))
  · exact L.k_w.sub_right (Lay.wSub (by decide))
  · exact hD

end VG.Proof.AesOcb.PPC64LE

end

end

/-!
# AES-OCB on PPC64LE: the calls of the block functions

Untrusted: everything here is checked by Lean. `callArgs ++ args` sets up a
call of `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` with the key
schedule of the key context, the rounds in `r28`, the `n` blocks at `D` that
`args` sets (`Dst`: blocks of `W`, `dstW`, or the data, `dstD`; the block
functions need no working space, `callBlocks_ok`); `encOne d` enciphers
the block at `W + d` (`encOne_ok`). As on AArch64
(`Proof/AesOcb/AArch64/Args.lean`).
-/

@[expose] public section

namespace VG.Proof.AesOcb.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Impl.AesOcb.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (blockAtMem aesWith)
open VG.Proof.AesGcm.PPC64LE (Keeps covers_left covers_prefix)

/-- `n` blocks at `D` for a call: apart from the key context, and readable
and writable. -/
structure Dst (K W : Addr) (s : State) (D : Addr) (n : Nat) : Prop where
  wrap : D.toNat + 16 * n ≤ 2 ^ 64
  k : (⟨K, 256⟩ : Region).Disjoint ⟨D, 16 * n⟩
  rd : Covers [⟨D, 16 * n⟩] (s.rd ++ s.wr)
  wr : Covers [⟨D, 16 * n⟩] s.wr

/-- Blocks of `W`. -/
theorem dstW {K W : Addr} {s : State} (L : Lay K W) (P : Perm K W s) {d n : Nat} (h : d + 16 * n ≤ 512) :
    Dst K W s (W + BitVec.ofNat 64 d) n where
  wrap := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.mul_zero, Nat.add_zero]; exact Nat.le_of_lt (W + BitVec.ofNat 64 d).isLt
    · rw [L.toNat_w (by omega_using [h, hn])]; have := L.ww; omega_using [h, this]
  k := L.k_w.sub_right (Lay.wSub (by omega_using [h]))
  rd := covers_left (P.wC (by omega_using [h]))
  wr := P.wC (by omega_using [h])

/-- Blocks of the data. -/
theorem dstD {K W : Addr} {s : State} {D : Addr} {n : Nat} (h : DBuf K W s D (16 * n)) : Dst K W s D n where
  wrap := h.wrap
  k := h.k
  rd := h.rd
  wr := h.wr

theorem Dst.of_eq {K W : Addr} {s s' : State} {D : Addr} {n : Nat} (h : Dst K W s D n)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Dst K W s' D n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd, wr := by rw [hwr]; exact h.wr }

/-- What the arguments `args` of a call set: `r5` and `r6` (to `D` and `n`),
and nothing else. -/
def ArgsOk (args : List Instr) (s : State) (D : Addr) (n : Nat) : Prop :=
  ∃ s₁, runBlock isa args s = some s₁ ∧ s₁.gpr .r5 = D ∧ s₁.gpr .r6 = BitVec.ofNat 64 n ∧
    (∀ r, r ≠ .r5 → r ≠ .r6 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁

/-- One block at `W + d`. -/
theorem oneBlock_ok {W : Addr} {s : State} (h31 : s.gpr .r31 = W) {d : Nat} (hd : d < 2 ^ 15) :
    ArgsOk [.addi .r5 .r31 d, .li .r6 1] s (W + BitVec.ofNat 64 d) 1 := by
  refine ⟨(s.write .r5 (s.gpr .r31 + BitVec.ofNat 64 d)).write .r6 (BitVec.ofNat 64 1), ?_,
    by rw [gpr_write_of_ne _ _ (by decide), gpr_write_self, h31], gpr_write_self _ _ _,
    fun r h5 h6 => by rw [gpr_write_of_ne _ _ h6, gpr_write_of_ne _ _ h5], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, hd, ne_eq, reduceCtorEq, not_false_eq_true,
    and_self, ↓reduceIte, Nat.reduceLT, Nat.reducePow]

theorem BPost.congr {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s₀ s s' : State} {K D : Addr}
    {R n : Nat} (h : BPost f s K D R n s') (hk : Keeps s₀ s) (hg : ∀ r ∈ preserved, s.gpr r = s₀.gpr r) :
    BPost f s₀ K D R n s' where
  rd := by rw [h.rd, hk.rd]
  wr := by rw [h.wr, hk.wr]
  sp := by rw [h.sp, hk.sp]
  saved r hr := by rw [h.saved r hr, hg r hr]
  frame := by rw [← hk.mem]; exact h.frame
  out := by rw [← hk.mem]; exact h.out

theorem callArgs_run {s : State} :
    ∃ s₁, runBlock isa callArgs s = some s₁ ∧ s₁.gpr .r3 = s.gpr .r29 ∧ s₁.gpr .r4 = s.gpr .r28 ∧
      (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r7 → s₁.gpr r = s.gpr r) ∧ Keeps s s₁ := by
  refine ⟨(s.write .r3 (s.gpr .r29)).write .r4 (s.gpr .r28), ?_,
    by rw [gpr_write_of_ne _ _ (by decide), gpr_write_self], gpr_write_self _ _ _,
    fun r h3 h4 _ => by rw [gpr_write_of_ne _ _ h4, gpr_write_of_ne _ _ h3],
    ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  simp only [callArgs, Impl.AesGcm.PPC64LE.mov, runBlock_cons, runStep_some, runBlock_nil, exec,
    BitVec.or_self, gpr_write_of_ne _ _ (show ¬Reg.r28 = .r3 by decide)]

section
variable {V : Reg → BitVec 64} {sp : Addr} (L : Lay (V .r29) (V .r31))
include L

/-- The arguments of a call, after `callArgs` and `args`. -/
theorem callArgs_ok {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : V .r28 = BitVec.ofNat 64 R) {s : State}
    (E : Env V sp s) {args : List Instr} {D : Addr} {k : Nat}
    (ha : ∀ s₁, (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r7 → s₁.gpr r = s.gpr r) → Keeps s s₁ → ArgsOk args s₁ D k)
    (hD : Dst (V .r29) (V .r31) s D k) :
    WP isa (.block (callArgs ++ args)) s fun s₂ =>
      BCall s₂ (V .r29) D R k ∧
        (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → s₂.gpr r = s.gpr r) ∧ Keeps s s₂ := by
  refine (fun (_ : Lay (V .r29) (V .r31)) => ?_) L
  obtain ⟨s₁, run₁, r3₁, r4₁, g₁, k₁⟩ := callArgs_run (s := s)
  obtain ⟨s₂, run₂, r5₂, r6₂, g₂, k₂⟩ := ha s₁ g₁ k₁
  have k₂' : Keeps s s₂ := k₁.trans k₂
  have hD₂ := hD.of_eq (s' := s₂) k₂'.rd k₂'.wr
  have hc : BCall s₂ (V .r29) D R k :=
    { r3 := by rw [g₂ _ (by decide) (by decide), r3₁, E.r29]
      r4 := by rw [g₂ _ (by decide) (by decide), r4₁, E.r28, h28]
      r5 := r5₂, r6 := r6₂
      rounds := hR, wrap := hD.wrap
      kd := hD.k.sub_left (Region.sub_prefix (by decide))
      reads := Covers.cons (covers_prefix (by rw [k₂'.rd, k₂'.wr]; exact E.perm.k) (by decide))
        (Covers.cons hD₂.rd Covers.nil)
      writes := Covers.cons hD₂.wr Covers.nil }
  exact WP.block_append (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₂, run₂, hc,
    fun r h3 h4 h5 h6 h7 => by rw [g₂ r h5 h6, g₁ r h3 h4 h7], k₂'⟩⟩)

/-- A call of a block function, after `callArgs` and `args`. -/
theorem callBlocks_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksPPC64LEF f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksPPC64LEF f).post s s')
    (nf : c.noFrames = true) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : V .r28 = BitVec.ofNat 64 R)
    {s : State} (E : Env V sp s) {args : List Instr} {D : Addr} {k : Nat}
    (ha : ∀ s₁, (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r7 → s₁.gpr r = s.gpr r) → Keeps s s₁ → ArgsOk args s₁ D k)
    (hD : Dst (V .r29) (V .r31) s D k) :
    WP isa (.seq (.block (callArgs ++ args)) (.call name c)) s
      (BPost f s (V .r29) D R k) :=
  WP.seq (WP.mono (callArgs_ok L hR h28 E ha hD) fun _ ⟨hc, g₂, k₂⟩ =>
    WP.mono (blk_call ok nf hc) fun _ h => h.congr k₂ fun r hr => g₂ r
      (by revert hr; revert r; decide) (by revert hr; revert r; decide) (by revert hr; revert r; decide)
      (by revert hr; revert r; decide) (by revert hr; revert r; decide))

/-- `encOne d`: the block at `W + d` enciphered. -/
theorem encOne_ok {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14) (h28 : V .r28 = BitVec.ofNat 64 R) {s : State}
    (E : Env V sp s) {d : Nat} (hd : d + 16 ≤ 512) :
    WP isa (encOne d) s (BPost Spec.Aes.cipher s (V .r29) (V .r31 + BitVec.ofNat 64 d)
      R 1) :=
  callBlocks_ok L Proof.Aes.PPC64LE.encryptBlocksF_correct encryptBlocks_noFrames hR h28 E
    (fun s₁ g₁ _ => oneBlock_ok (by rw [g₁ _ (by decide) (by decide) (by decide), E.r31]) (by omega_using [hd]))
    (dstW L E.perm (by omega_using [hd]))

end

/-- After a call: the environment. -/
theorem BPost.env {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {V : Reg → BitVec 64} {sp : Addr}
    {s s' : State} {K D : Addr} {R n : Nat} (h : BPost f s K D R n s') (E : Env V sp s) : Env V sp s' :=
  E.of_saved h.saved h.sp h.rd h.wr

end VG.Proof.AesOcb.PPC64LE

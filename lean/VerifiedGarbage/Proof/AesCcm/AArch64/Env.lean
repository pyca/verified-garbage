import VerifiedGarbage.Proof.AesCcm.AArch64.Contract
import VerifiedGarbage.Proof.AesCcm.Words
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.AesGcm.AArch64.Save
import VerifiedGarbage.Impl.AesCcm.AArch64
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# AES-CCM on AArch64: where everything is

Untrusted: everything here is checked by Lean. The public values of a call
(`Cx`): the key schedule (240 bytes at `K`), the working space (2560 bytes at
`W`), the data (`n` bytes at `D`), the associated data (`al` bytes at `A`),
the tag (`tl` bytes at `T`), the rounds, the tag length and the nonce length,
and the stack pointer; what
the precondition says of them (`Lay`); what a state may access (`Perm`); the
registers holding them (`Env`); and the values the entry keeps in `W`
(`Slots`). The pieces write only the parts of `W` in `mutR` and the data, so
the slots, our caller's registers saved in `W`, the key schedule and the
associated data stay as the entry left them. `carun` runs a block
symbolically.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesCcm.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.AArch64 (mov ptr imm)
open VG.Proof.AesGcm.AArch64 (in_off covers_off covers_left in_left)

/-- A `movz` of a 16-bit literal. -/
theorem imm_lit (k : Nat) : (BitVec.setWidth 64 (BitVec.ofNat 16 k) <<< 0 : BitVec 64) = BitVec.ofNat 64 (k % 65536) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.shiftLeft_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]

/-- A byte stored from a register. -/
theorem setWidth_8_32 (x : BitVec 64) : BitVec.setWidth 8 (BitVec.setWidth 32 x) = BitVec.setWidth 8 x :=
  BitVec.setWidth_setWidth_of_le _ (by decide)

/-- Runs a block of the instructions the AES-CCM code uses. -/
macro "carun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr,
    State.load, State.store, Size.bytes, Size.bits, State.read, gpr_write, mem_write, rd_write, wr_write,
    sp_write, ite_true, ite_false, Option.bind_some, Option.map_some, BitVec.setWidth_eq, and_self, BitVec.add_zero,
    mov, ptr, imm, zero16, bO, c0O, c1O, ksO, uO, aadO, alenO, nlenO, vO, rO, scrO, List.cons_append,
    List.nil_append, List.append_assoc, reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceLeDiff,
    Nat.reduceSub, Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, and_true, true_and,
    eq_self_iff_true, imm_lit, setWidth_8_32, $ts,*]) <;> try rfl)

/-! ## Reassociating sequences -/

theorem seq_assoc3 {a b c d : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a (.seq b c)) d) s Q) : WP isa (.seq a (.seq b (.seq c d))) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc h)) fun _ h => WP.assoc h)

theorem seq_assoc4 {a b c d e : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a (.seq b (.seq c d))) e) s Q) : WP isa (.seq a (.seq b (.seq c (.seq d e)))) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc h)) fun _ h => seq_assoc3 h)

theorem seq_assoc5 {a b c d e f : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a (.seq b (.seq c (.seq d e)))) f) s Q) :
    WP isa (.seq a (.seq b (.seq c (.seq d (.seq e f))))) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.assoc h)) fun _ h => seq_assoc4 h)

/-! ## The public values -/

/-- The public values of a call of `seal` or `open`. -/
structure Cx where
  K : Addr
  W : Addr
  D : Addr
  A : Addr
  R : Nat
  tl : Nat
  n : Nat
  al : Nat
  nl : Nat
  SP : Addr
  T : Addr

/-- What the precondition says of the public values. -/
structure Lay (c : Cx) : Prop where
  kw : c.K.toNat + 240 ≤ 2 ^ 64
  ww : c.W.toNat + 2560 ≤ 2 ^ 64
  dw : c.D.toNat + c.n ≤ 2 ^ 64
  aw : c.A.toNat + c.al ≤ 2 ^ 64
  k_w : (⟨c.K, 240⟩ : Region).Disjoint ⟨c.W, 2560⟩
  k_d : (⟨c.K, 240⟩ : Region).Disjoint ⟨c.D, c.n⟩
  d_w : (⟨c.D, c.n⟩ : Region).Disjoint ⟨c.W, 2560⟩
  a_w : (⟨c.A, c.al⟩ : Region).Disjoint ⟨c.W, 2560⟩
  a_d : (⟨c.A, c.al⟩ : Region).Disjoint ⟨c.D, c.n⟩
  rounds : c.R = 10 ∨ c.R = 12 ∨ c.R = 14
  n_lt : c.n < 2 ^ 64
  al_lt : c.al < 2 ^ 64
  t4 : 4 ≤ c.tl
  t16 : c.tl ≤ 16
  te : c.tl % 2 = 0
  h7 : 7 ≤ c.nl
  h13 : c.nl ≤ 13
  hn : c.n < 256 ^ (15 - c.nl)
  tw : c.T.toNat + c.tl ≤ 2 ^ 64
  t_w : (⟨c.T, c.tl⟩ : Region).Disjoint ⟨c.W, 2560⟩
  t_d : (⟨c.T, c.tl⟩ : Region).Disjoint ⟨c.D, c.n⟩

/-- What a state may access. -/
structure Perm (c : Cx) (s : State) : Prop where
  k : Covers [⟨c.K, 240⟩] (s.rd ++ s.wr)
  w : Covers [⟨c.W, 2560⟩] s.wr
  d : Covers [⟨c.D, c.n⟩] s.wr
  a : Covers [⟨c.A, c.al⟩] (s.rd ++ s.wr)
  t : Covers [⟨c.T, c.tl⟩] (s.rd ++ s.wr)

/-- The registers holding the public values throughout, the stack pointer,
and what the state may access. -/
structure Env (c : Cx) (s : State) : Prop where
  x19 : s.gpr .x19 = c.W
  x20 : s.gpr .x20 = BitVec.ofNat 64 c.tl
  x21 : s.gpr .x21 = c.K
  x22 : s.gpr .x22 = BitVec.ofNat 64 c.R
  x27 : s.gpr .x27 = c.D
  x28 : s.gpr .x28 = BitVec.ofNat 64 c.n
  sp : s.sp = c.SP
  perm : Perm c s

/-- The registers `Env` pins. -/
abbrev envRegs : List Reg := [.x19, .x20, .x21, .x22, .x27, .x28]

theorem Perm.of_eq {c : Cx} {s s' : State} (h : Perm c s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Perm c s' :=
  ⟨by rw [hrd, hwr]; exact h.k, by rw [hwr]; exact h.w, by rw [hwr]; exact h.d, by rw [hrd, hwr]; exact h.a,
    by rw [hrd, hwr]; exact h.t⟩

/-- An environment, after code that keeps its registers, the stack pointer
and the permissions. -/
theorem Env.keep {c : Cx} {s s' : State} (h : Env c s) (hg : ∀ r ∈ envRegs, s'.gpr r = s.gpr r)
    (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Env c s' :=
  ⟨by rw [hg _ (by simp), h.x19], by rw [hg _ (by simp), h.x20], by rw [hg _ (by simp), h.x21],
    by rw [hg _ (by simp), h.x22], by rw [hg _ (by simp), h.x27], by rw [hg _ (by simp), h.x28],
    by rw [hsp, h.sp], h.perm.of_eq hrd hwr⟩

/-- An environment, after code that writes only registers outside `envRegs`. -/
theorem Env.others {c : Cx} {s s' : State} (h : Env c s) {rs : List Reg}
    (hg : ∀ r, r ∉ rs → s'.gpr r = s.gpr r) (hd : ∀ r ∈ envRegs, r ∉ rs := by decide)
    (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Env c s' :=
  h.keep (fun r hr => hg r (hd r hr)) hsp hrd hwr

/-- An environment, after a call. -/
theorem Env.of_saved {c : Cx} {s s' : State} (h : Env c s)
    (hg : ∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) : Env c s' :=
  h.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hsp hrd hwr

namespace Lay

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 2560) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 2560⟩ :=
  Offset.sub_base _ h

variable {c : Cx} (L : Lay c)
include L

/-- Parts of `W` are disjoint. -/
theorem w_w {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 2560) (hd : d + k ≤ 2560) :
    (⟨c.W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by have := L.ww; omega) (by have := L.ww; omega)

/-- `W` and a part of it. -/
theorem w0_w {n d k : Nat} (h : n ≤ d) (hd : d + k ≤ 2560) :
    (⟨c.W, n⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ := by
  simpa using L.w_w (a := 0) (n := n) (.inl (by omega)) (by omega) hd

theorem k_w' {d k : Nat} (hd : d + k ≤ 2560) : (⟨c.K, 240⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  L.k_w.sub_right (wSub hd)

theorem d_w' {d k : Nat} (hd : d + k ≤ 2560) : (⟨c.D, c.n⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  L.d_w.sub_right (wSub hd)

theorem a_w' {d k : Nat} (hd : d + k ≤ 2560) : (⟨c.A, c.al⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  L.a_w.sub_right (wSub hd)

theorem wrapW {d : Nat} (hd : d < 2560) : (c.W + BitVec.ofNat 64 d).toNat = c.W.toNat + d := by
  have := L.ww
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem rb : 16 * (c.R + 1) ≤ 240 := by rcases L.rounds with h | h | h <;> rw [h] <;> decide

end Lay

namespace Perm

variable {c : Cx} {s : State} (P : Perm c s)
include P

theorem kR {d n : Nat} (h : d + n ≤ 240) : InRegions (s.rd ++ s.wr) (c.K + BitVec.ofNat 64 d) n :=
  in_off P.k h (by decide)

theorem wW {d n : Nat} (h : d + n ≤ 2560) : InRegions s.wr (c.W + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 2560) : InRegions (s.rd ++ s.wr) (c.W + BitVec.ofNat 64 d) n :=
  in_left (P.wW h)

theorem wC {d n : Nat} (h : d + n ≤ 2560) : Covers [⟨c.W + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

theorem wCR {d n : Nat} (h : d + n ≤ 2560) : Covers [⟨c.W + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  covers_left (P.wC h)

end Perm

/-! ## Buffers -/

/-- A buffer of `len` bytes at `P` that the code may read, apart from `W`. -/
structure Buf (c : Cx) (s : State) (P : Addr) (len : Nat) : Prop where
  rd : Covers [⟨P, len⟩] (s.rd ++ s.wr)
  lt : len < 2 ^ 64
  wrap : P.toNat + len ≤ 2 ^ 64
  w : (⟨P, len⟩ : Region).Disjoint ⟨c.W, 2560⟩

namespace Buf

variable {c : Cx} {s : State} {P : Addr} {len : Nat} (h : Buf c s P len)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Buf c s' P len :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

/-- The bytes from `k` on. -/
theorem drop {k : Nat} (hk : k ≤ len) : Buf c s (P + BitVec.ofNat 64 k) (len - k) where
  rd := covers_off h.rd (by omega) h.lt
  lt := by have := h.lt; omega
  wrap := by
    have := h.wrap
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by have := h.lt; omega)]
    have := Nat.mod_le (P.toNat + k) (2 ^ 64)
    omega
  w := h.w.sub_left (Offset.sub_base P (by omega))

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ len) : Buf c s P k where
  rd := fun a m ⟨r, hr, hc⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.rd a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩
  lt := by have := h.lt; omega
  wrap := by have := h.wrap; omega
  w := h.w.sub_left (Region.sub_prefix hk)

/-- Bytes `[a, a + k)`. -/
theorem slice {a k : Nat} (hk : a + k ≤ len) : Buf c s (P + BitVec.ofNat 64 a) k :=
  (h.drop (k := a) (by omega)).take (by omega)

theorem wd {d k : Nat} (hd : d + k ≤ 2560) : (⟨P, len⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  h.w.sub_right (Lay.wSub hd)

end Buf

/-- The associated data as a buffer. -/
theorem Lay.bufA {c : Cx} (L : Lay c) {s : State} (P : Perm c s) : Buf c s c.A c.al :=
  ⟨P.a, L.al_lt, L.aw, L.a_w⟩

/-- The data as a buffer. -/
theorem Lay.bufD {c : Cx} (L : Lay c) {s : State} (P : Perm c s) : Buf c s c.D c.n :=
  ⟨covers_left P.d, L.n_lt, L.dw, L.d_w⟩

/-- Data for a call: `len` bytes at `P`, which the code may read, apart from
the working space of the functions called. -/
structure Src (c : Cx) (s : State) (P : Addr) (len : Nat) : Prop where
  rd : Covers [⟨P, len⟩] (s.rd ++ s.wr)
  wrap : P.toNat + len ≤ 2 ^ 64
  qs : (⟨P, len⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 384, 2176⟩

theorem Buf.src {c : Cx} {s : State} {P : Addr} {len : Nat} (h : Buf c s P len) : Src c s P len :=
  ⟨h.rd, h.wrap, h.wd (by decide)⟩

/-- Bytes of `W` below 384 as data. -/
theorem Lay.srcW {c : Cx} (L : Lay c) {s : State} (P : Perm c s) {t k : Nat} (hk : t + k ≤ 384) :
    Src c s (c.W + BitVec.ofNat 64 t) k :=
  ⟨P.wCR (by omega), by rw [L.wrapW (by omega)]; have := L.ww; omega, L.w_w (.inl (by omega)) (by omega) (by decide)⟩

/-! ## The slots -/

/-- The values the entry keeps in `W`: the address and length of the
associated data, the length of the nonce and the address of the tag. -/
structure Slots (c : Cx) (m : Mem) : Prop where
  aad : m.readW (c.W + BitVec.ofNat 64 216) 64 = c.A
  alen : m.readW (c.W + BitVec.ofNat 64 224) 64 = BitVec.ofNat 64 c.al
  nlen : m.readW (c.W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 c.nl
  tag : m.readW (c.W + BitVec.ofNat 64 240) 64 = c.T

/-- The parts of `W` the pieces write: `[0, 112)` and `[256, 2560)`. -/
abbrev wLo (W : Addr) : Region := ⟨W, 112⟩
abbrev wHi (W : Addr) : Region := ⟨W + BitVec.ofNat 64 256, 2304⟩

/-- What the pieces may change: those parts of `W` and the data. -/
abbrev mutR (c : Cx) : List Region := [wLo c.W, wHi c.W, ⟨c.D, c.n⟩]

/-- A part of `W` the pieces write, within `mutR`. -/
theorem sub_lo {c : Cx} {d k : Nat} (h : d + k ≤ 112) :
    ∃ r' ∈ mutR c, Region.Sub ⟨c.W + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨wLo c.W, by simp, Offset.sub_base _ h⟩

theorem sub_hi {c : Cx} {d k : Nat} (h₁ : 256 ≤ d) (h₂ : d + k ≤ 2560) :
    ∃ r' ∈ mutR c, Region.Sub ⟨c.W + BitVec.ofNat 64 d, k⟩ r' :=
  ⟨wHi c.W, by simp, Offset.sub _ h₁ (by omega)⟩

theorem sub_data {c : Cx} : ∃ r' ∈ mutR c, Region.Sub ⟨c.D, c.n⟩ r' := ⟨_, by simp, fun _ h => h⟩

/-- The part of `W` at `[d, d + k)`, when it misses the parts the pieces write. -/
theorem kept_mut {c : Cx} (L : Lay c) {d k : Nat} (hd : 112 ≤ d ∧ d + k ≤ 256) :
    ∀ r ∈ mutR c, (⟨c.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (L.w0_w (n := 112) (d := d) (k := k) hd.1 (by omega)).symm
  · exact L.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.d_w' (by omega)).symm

theorem k_mut {c : Cx} (L : Lay c) : ∀ r ∈ mutR c, (⟨c.K, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.k_w.sub_right (Region.sub_prefix (by decide))
  · exact L.k_w' (by decide)
  · exact L.k_d

theorem a_mut {c : Cx} (L : Lay c) : ∀ r ∈ mutR c, (⟨c.A, c.al⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.a_w.sub_right (Region.sub_prefix (by decide))
  · exact L.a_w' (by decide)
  · exact L.a_d

/-- A frame within what the pieces write. -/
theorem frame_mut {c : Cx} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hs : ∀ r ∈ rs, ∃ r' ∈ mutR c, Region.Sub r r') : Frame (mutR c) m m' := hf.sub hs

section
variable {c : Cx} (L : Lay c) {m m' : Mem} (hf : Frame (mutR c) m m')
include L hf

theorem Slots.mut (S : Slots c m) : Slots c m' := by
  have k : ∀ d, 216 ≤ d → d + 8 ≤ 248 →
      m'.readW (c.W + BitVec.ofNat 64 d) 64 = m.readW (c.W + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ =>
    hf.readW (r := ⟨c.W + BitVec.ofNat 64 d, 8⟩) (w := 64) (Region.contains_self _ _)
      (kept_mut L ⟨by omega, by omega⟩) (by decide)
  exact ⟨by rw [k 216 (by decide) (by decide)]; exact S.aad, by rw [k 224 (by decide) (by decide)]; exact S.alen,
    by rw [k 232 (by decide) (by decide)]; exact S.nlen, by rw [k 240 (by decide) (by decide)]; exact S.tag⟩

theorem saved_mut {s₀ : State} (S : Proof.AesGcm.AArch64.SavedAt m c.W s₀) :
    Proof.AesGcm.AArch64.SavedAt m' c.W s₀ :=
  S.frame hf (fun r hr => kept_mut L (d := 128) (k := 88) ⟨by decide, by decide⟩ r hr)

theorem ciph_mut : Spec.Ccm.ctxCiph m' c.K c.R = Spec.Ccm.ctxCiph m c.K c.R := by
  unfold Spec.Ccm.ctxCiph
  rw [Proof.AesGcm.AArch64.bytesAt_frame hf (fun r hr => (k_mut L r hr).sub_left (Region.sub_prefix L.rb))
    (by have := L.rb; omega)]

theorem aad_mut : bytesAt m' c.A c.al = bytesAt m c.A c.al :=
  Proof.AesGcm.AArch64.bytesAt_frame hf (a_mut L) (by have := L.al_lt; omega)

theorem tag_mut (ht : c.tl ≤ 16) : bytesAt m' c.T c.tl = bytesAt m c.T c.tl :=
  Proof.AesGcm.AArch64.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact L.t_w.sub_right (Region.sub_prefix (by decide))
    · exact L.t_w.sub_right (Lay.wSub (by decide))
    · exact L.t_d) (by omega)

end

end VG.Proof.AesCcm.AArch64

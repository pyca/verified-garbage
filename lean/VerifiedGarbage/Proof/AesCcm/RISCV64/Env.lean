module

public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Spec.Ccm
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# AES-CCM on RISC-V: where everything is

Untrusted: everything here is checked by Lean. The public values of a call
(`Cx`): the key schedule (240 bytes at `K`), the working space (2560 bytes at
`W`), the data (`n` bytes at `D`), the associated data (`al` bytes at `A`),
the tag (`tl` bytes at `T`), the rounds, the tag length and the nonce
length; what the precondition says of them (`Lay`); what a state may access
(`Perm`); the registers holding them (`Env`); and the values the entry keeps
in `W` (`Slots`). The pieces write only the parts of `W` in `mutR` and the
data, so the slots, our caller's registers saved in `W`, the key schedule
and the associated data stay as the entry left them. What a piece keeps of
the registers is `PK`, as on PPC64LE (`Proof/AesCcm/PPC64LE/Env.lean`).
-/

@[expose] public section

namespace VG.Proof.AesCcm.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps
open VG.Spec.Aes (bytesAt)

/-! ## Regions -/

/-- The part of a region at an offset is covered when the region is. -/
theorem covers_off {p : Addr} {k d n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hd : d + n ≤ k)
    (hk : k < 2 ^ 64) : Covers [⟨p + BitVec.ofNat 64 d, n⟩] rs := by
  intro a m ⟨r, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst hr
  refine h a m ⟨_, List.mem_singleton_self _, ?_⟩
  simp only [Region.Contains] at hc ⊢
  have e : a - p = (a - (p + BitVec.ofNat 64 d)) + BitVec.ofNat 64 d := by
    rw [Offset.sub_add_eq]; exact (BitVec.sub_add_cancel _ _).symm
  rw [e, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem in_off {p : Addr} {k d n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hd : d + n ≤ k)
    (hk : k < 2 ^ 64) : InRegions rs (p + BitVec.ofNat 64 d) n :=
  covers_off h hd hk _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

theorem covers_prefix {p : Addr} {k n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hn : n ≤ k) :
    Covers [⟨p, n⟩] rs := by
  intro a m ⟨r, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst hr
  exact h a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩

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
  T : Addr

/-- What the precondition says of the public values. -/
structure Lay (c : Cx) : Prop where
  kw : c.K.toNat + 240 ≤ 2 ^ 64
  ww : c.W.toNat + 2560 ≤ 2 ^ 64
  wal : c.W.toNat % 8 = 0
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

/-! ## What the pieces keep -/

/-- The registers the pieces keep: the public values, and our caller's. -/
def keepRegs : List Reg := [.s0, .s1, .s2, .s3, .s4, .s9, .s10, .s11]

/-- What a piece keeps. -/
structure PK (s s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  gpr : ∀ r ∈ keepRegs, s'.gpr r = s.gpr r

theorem PK.refl (s : State) : PK s s := ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

theorem PK.trans {s t u : State} (h₁ : PK s t) (h₂ : PK t u) : PK s u :=
  ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp,
    fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr)⟩

theorem PK.ofUpd {s t : State} {d : Reg} {v : BitVec 64} (u : Upd s t d v)
    (hd : d ∉ keepRegs := by decide) : PK s t :=
  ⟨u.rd, u.wr, u.sp, fun r hr => u.other r fun h => hd (h ▸ hr)⟩

theorem PK.ofMupd {s t : State} {m : Mem} (u : Mupd s t m) : PK s t :=
  ⟨u.rd, u.wr, u.sp, fun r _ => by rw [u.gpr]⟩

theorem keep_preserved : ∀ r ∈ keepRegs, r ∈ preserved := by decide

/-- After a call, which keeps the callee-saved registers. -/
theorem PK.ofSaved {s t : State} (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hsp : t.sp = s.sp)
    (hs : ∀ r ∈ preserved, t.gpr r = s.gpr r) : PK s t :=
  ⟨hrd, hwr, hsp, fun r hr => hs r (keep_preserved r hr)⟩

/-- After code that writes only the registers `rs`, none of `keepRegs`. -/
theorem PK.ofKeep {s t : State} {rs : List Reg} (h : Keep rs s t) (hsp : t.sp = s.sp)
    (hr : ∀ r ∈ keepRegs, r ∉ rs := by decide) : PK s t :=
  ⟨h.2.1, h.2.2, hsp, fun r hk => h.gpr (hr r hk)⟩

/-! ## The environment -/

/-- The registers holding the public values throughout, and what the state
may access. -/
structure Env (c : Cx) (s : State) : Prop where
  s1 : s.gpr .s1 = c.W
  s2 : s.gpr .s2 = BitVec.ofNat 64 c.tl
  s3 : s.gpr .s3 = c.K
  s4 : s.gpr .s4 = BitVec.ofNat 64 c.R
  s9 : s.gpr .s9 = c.D
  s10 : s.gpr .s10 = BitVec.ofNat 64 c.n
  perm : Perm c s

theorem Perm.of_eq {c : Cx} {s s' : State} (h : Perm c s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Perm c s' :=
  ⟨by rw [hrd, hwr]; exact h.k, by rw [hwr]; exact h.w, by rw [hwr]; exact h.d, by rw [hrd, hwr]; exact h.a,
    by rw [hrd, hwr]; exact h.t⟩

theorem Env.of_pk {c : Cx} {s s' : State} (h : Env c s) (k : PK s s') : Env c s' :=
  ⟨by rw [k.gpr .s1 (by decide), h.s1], by rw [k.gpr .s2 (by decide), h.s2],
    by rw [k.gpr .s3 (by decide), h.s3], by rw [k.gpr .s4 (by decide), h.s4],
    by rw [k.gpr .s9 (by decide), h.s9], by rw [k.gpr .s10 (by decide), h.s10], h.perm.of_eq k.rd k.wr⟩

namespace Lay

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 2560) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 2560⟩ :=
  Offset.sub_base _ h

variable {c : Cx} (L : Lay c)
include L

/-- Parts of `W` are disjoint. -/
theorem w_w {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 2560) (hd : d + k ≤ 2560) :
    (⟨c.W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by have := L.ww; omega) (by have := L.ww; omega)

omit L in
/-- `W` and a part of it. -/
theorem w0_w {n d k : Nat} (h : n ≤ d) (hd : d + k ≤ 2560) :
    (⟨c.W, n⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  Offset.base_disjoint _ h (by omega)

theorem k_w' {d k : Nat} (hd : d + k ≤ 2560) : (⟨c.K, 240⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  L.k_w.sub_right (wSub hd)

theorem d_w' {d k : Nat} (hd : d + k ≤ 2560) : (⟨c.D, c.n⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  L.d_w.sub_right (wSub hd)

theorem a_w' {d k : Nat} (hd : d + k ≤ 2560) : (⟨c.A, c.al⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  L.a_w.sub_right (wSub hd)

theorem wrapW {d : Nat} (hd : d < 2560) : (c.W + BitVec.ofNat 64 d).toNat = c.W.toNat + d := by
  have := L.ww
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- Doublewords of `W` are aligned. -/
theorem alW {d : Nat} (hd : d % 8 = 0) (hlt : d < 2560) : (c.W + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  rw [L.wrapW hlt]; have := L.wal; omega

theorem rb : 16 * (c.R + 1) ≤ 240 := by rcases L.rounds with h | h | h <;> rw [h] <;> decide

end Lay

namespace Perm

variable {c : Cx} {s : State} (P : Perm c s)
include P

theorem kR {d n : Nat} (h : d + n ≤ 240) : InRegions (s.rd ++ s.wr) (c.K + BitVec.ofNat 64 d) n :=
  in_off P.k h (by decide)

theorem wW {d n : Nat} (h : d + n ≤ 2560) : InRegions s.wr (c.W + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wC {d n : Nat} (h : d + n ≤ 2560) : Covers [⟨c.W + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

theorem wCR {d n : Nat} (h : d + n ≤ 2560) : Covers [⟨c.W + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  Covers.right (P.wC h)

theorem wR {d n : Nat} (h : d + n ≤ 2560) : InRegions (s.rd ++ s.wr) (c.W + BitVec.ofNat 64 d) n :=
  P.wCR h _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

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
  rd := covers_prefix h.rd hk
  lt := by have := h.lt; omega
  wrap := by have := h.wrap; omega
  w := h.w.sub_left (Region.sub_prefix hk)

theorem wd {d k : Nat} (hd : d + k ≤ 2560) : (⟨P, len⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  h.w.sub_right (Lay.wSub hd)

end Buf

/-- The associated data as a buffer. -/
theorem Lay.bufA {c : Cx} (L : Lay c) {s : State} (P : Perm c s) : Buf c s c.A c.al :=
  ⟨P.a, L.al_lt, L.aw, L.a_w⟩

/-- The data as a buffer. -/
theorem Lay.bufD {c : Cx} (L : Lay c) {s : State} (P : Perm c s) : Buf c s c.D c.n :=
  ⟨Covers.right P.d, L.n_lt, L.dw, L.d_w⟩

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
  · exact (Lay.w0_w (c := c) (n := 112) (d := d) (k := k) hd.1 (by omega)).symm
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

theorem ciph_mut : Spec.Ccm.ctxCiph m' c.K c.R = Spec.Ccm.ctxCiph m c.K c.R := by
  unfold Spec.Ccm.ctxCiph
  rw [Proof.Cmac.bytesAt_frame hf (fun r hr => (k_mut L r hr).sub_left (Region.sub_prefix L.rb))
    (by have := L.rb; omega)]

theorem aad_mut : bytesAt m' c.A c.al = bytesAt m c.A c.al :=
  Proof.Cmac.bytesAt_frame hf (a_mut L) (by have := L.al_lt; omega)

theorem tag_mut : bytesAt m' c.T c.tl = bytesAt m c.T c.tl :=
  Proof.Cmac.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact L.t_w.sub_right (Region.sub_prefix (by decide))
    · exact L.t_w.sub_right (Lay.wSub (by decide))
    · exact L.t_d) (by have := L.t16; omega)

end

end VG.Proof.AesCcm.RISCV64

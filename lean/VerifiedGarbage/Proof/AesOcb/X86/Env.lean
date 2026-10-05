import VerifiedGarbage.Proof.AesOcb.X86.Contract
import VerifiedGarbage.Proof.AesGcm.X86.Common
import VerifiedGarbage.Proof.AesGcm.X86.Fn
import VerifiedGarbage.Proof.AesGcm.X86.Top
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Impl.AesOcb.X86

/-!
# AES-OCB on x86: where everything is

Untrusted: everything here is checked by Lean. The public arguments
(`Prm`): the key context (256 bytes at `K`), the working space (2560 bytes
at `W`), the nonce (`nl` bytes at `N`), the associated data (`al` bytes at
`A`), the data (`n` bytes at `D`), the tag (`tl` bytes at `T`), the stack
pointer and the number of rounds, all 32-bit; how their regions lie, apart
from each other and from the 24 bytes below `SP` that the calls use
(`Lay`); what a state may access (`Perm`); and `W` in `ebp`, the stack
pointer, and the arguments the entry keeps in `W` (`Env`). The pieces write
only the parts of `W` in `mutR` (and the data, and the stack below `SP`), so
they keep the slots and our caller's registers saved in `W`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86

open VG VG.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 w64_add covers_off in_off in_left covers_left
  covers_cons covers_nil slotv)

/-! ## Covering -/

theorem covers_of_mem {r : Region} {ts : List Region} (h : r ∈ ts) : Covers [r] ts := by
  intro a n ⟨x, hx, hc⟩
  simp only [List.mem_singleton] at hx; subst hx; exact ⟨x, h, hc⟩

theorem covers_prefix {p : Addr} {k n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hn : n ≤ k) :
    Covers [⟨p, n⟩] rs := fun a m ⟨r, hr, hc⟩ => by
  simp only [List.mem_singleton] at hr; subst hr
  exact h a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩

/-! ## The public arguments and their regions -/

/-- The public arguments. -/
structure Prm where
  /-- The key context. -/
  K : BitVec 32
  /-- The working space. -/
  W : BitVec 32
  /-- The nonce. -/
  N : BitVec 32
  /-- The associated data. -/
  A : BitVec 32
  /-- The data. -/
  D : BitVec 32
  /-- The tag. -/
  T : BitVec 32
  /-- The stack pointer. -/
  SP : BitVec 32
  /-- The number of rounds. -/
  R : Nat
  /-- The length of the nonce. -/
  nl : Nat
  /-- The length of the associated data. -/
  al : Nat
  /-- The length of the data. -/
  n : Nat
  /-- The length of the tag. -/
  tl : Nat

/-- The stack the calls use. -/
abbrev stk (p : Prm) : Region := below p.SP 24

/-- How the regions lie. -/
structure Lay (p : Prm) : Prop where
  kw : p.K.toNat + 256 ≤ 2 ^ 32
  ww : p.W.toNat + 2560 ≤ 2 ^ 32
  nw : p.N.toNat + p.nl ≤ 2 ^ 32
  aw : p.A.toNat + p.al ≤ 2 ^ 32
  dw : p.D.toNat + p.n ≤ 2 ^ 32
  tw : p.T.toNat + p.tl ≤ 2 ^ 32
  sp : 24 ≤ p.SP.toNat
  k_w : (⟨w64 p.K, 256⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩
  k_d : (⟨w64 p.K, 256⟩ : Region).Disjoint ⟨w64 p.D, p.n⟩
  n_w : (⟨w64 p.N, p.nl⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩
  n_d : (⟨w64 p.N, p.nl⟩ : Region).Disjoint ⟨w64 p.D, p.n⟩
  a_w : (⟨w64 p.A, p.al⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩
  a_d : (⟨w64 p.A, p.al⟩ : Region).Disjoint ⟨w64 p.D, p.n⟩
  d_w : (⟨w64 p.D, p.n⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩
  t_w : (⟨w64 p.T, p.tl⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩
  t_d : (⟨w64 p.T, p.tl⟩ : Region).Disjoint ⟨w64 p.D, p.n⟩
  bk : (stk p).Disjoint ⟨w64 p.K, 256⟩
  bn : (stk p).Disjoint ⟨w64 p.N, p.nl⟩
  ba : (stk p).Disjoint ⟨w64 p.A, p.al⟩
  bd : (stk p).Disjoint ⟨w64 p.D, p.n⟩
  bw : (stk p).Disjoint ⟨w64 p.W, 2560⟩
  bt : (stk p).Disjoint ⟨w64 p.T, p.tl⟩
  rounds : p.R = 10 ∨ p.R = 12 ∨ p.R = 14
  nl1 : 1 ≤ p.nl
  nl15 : p.nl ≤ 15
  tl1 : 1 ≤ p.tl
  tl16 : p.tl ≤ 16
  al32 : p.al < 2 ^ 32
  n32 : p.n < 2 ^ 32
  retW : (⟨w64 p.SP, 4⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩
  retD : (⟨w64 p.SP, 4⟩ : Region).Disjoint ⟨w64 p.D, p.n⟩
  retT : (⟨w64 p.SP, 4⟩ : Region).Disjoint ⟨w64 p.T, p.tl⟩

/-- What a state may access. -/
structure Perm (p : Prm) (s : State) : Prop where
  k : Covers [⟨w64 p.K, 256⟩] (s.rd ++ s.wr)
  non : Covers [⟨w64 p.N, p.nl⟩] (s.rd ++ s.wr)
  aad : Covers [⟨w64 p.A, p.al⟩] (s.rd ++ s.wr)
  d : Covers [⟨w64 p.D, p.n⟩] s.wr
  w : Covers [⟨w64 p.W, 2560⟩] s.wr
  t : Covers [⟨w64 p.T, p.tl⟩] (s.rd ++ s.wr)

theorem Perm.of_eq {p : Prm} {s s' : State} (h : Perm p s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Perm p s' := by
  obtain ⟨a, b, c, d, e, f⟩ := h
  exact ⟨by rw [hrd, hwr]; exact a, by rw [hrd, hwr]; exact b, by rw [hrd, hwr]; exact c, by rw [hwr]; exact d,
    by rw [hwr]; exact e, by rw [hrd, hwr]; exact f⟩

/-- The public values the entry keeps in `W`: all the arguments but `work`. -/
structure Slots (p : Prm) (m : Mem) : Prop where
  ctx : slotv m p.W Impl.AesOcb.X86.ctxO = p.K
  rounds : slotv m p.W Impl.AesOcb.X86.rndO = BitVec.ofNat 32 p.R
  nonce : slotv m p.W Impl.AesOcb.X86.nO = p.N
  nlen : slotv m p.W Impl.AesOcb.X86.nlO = BitVec.ofNat 32 p.nl
  aad : slotv m p.W Impl.AesOcb.X86.aadO = p.A
  alen : slotv m p.W Impl.AesOcb.X86.alenO = BitVec.ofNat 32 p.al
  data : slotv m p.W Impl.AesOcb.X86.dataO = p.D
  len : slotv m p.W Impl.AesOcb.X86.lenO = BitVec.ofNat 32 p.n
  tg : slotv m p.W Impl.AesOcb.X86.tgO = p.T
  tlen : slotv m p.W Impl.AesOcb.X86.tlO = BitVec.ofNat 32 p.tl

/-- `W` in `ebp`, the stack pointer, what the state may access, and the
slots. -/
structure Env (p : Prm) (s : State) : Prop where
  ebp : s.gpr .ebp = p.W
  esp : s.gpr .esp = p.SP
  perm : Perm p s
  slots : Slots p s.mem

namespace Lay

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 2560) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 2560⟩ :=
  Offset.sub_base _ h

/-- Parts of `W` are disjoint. -/
theorem w_w {W : BitVec 32} {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 2560) (hd : d + k ≤ 2560) :
    (⟨w64 W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by omega) (by omega)

variable {p : Prm} (L : Lay p)
include L

/-- An offset into `W`, as a 64-bit address. -/
theorem aW {o : Nat} (ho : o < 2560) : w64 (p.W + BitVec.ofNat 32 o) = w64 p.W + BitVec.ofNat 64 o :=
  w64_add (by have := L.ww; omega)

theorem nW {o : Nat} (ho : o < 2560) : (p.W + BitVec.ofNat 32 o).toNat = p.W.toNat + o :=
  toNat_add32 (by have := L.ww; omega)

/-- An offset into the key context. -/
theorem aK {o : Nat} (ho : o < 256) : w64 (p.K + BitVec.ofNat 32 o) = w64 p.K + BitVec.ofNat 64 o :=
  w64_add (by have := L.kw; omega)

theorem k_w' {d k : Nat} (hd : d + k ≤ 2560) : (⟨w64 p.K, 256⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ :=
  L.k_w.sub_right (wSub hd)

theorem n_w' {d k : Nat} (hd : d + k ≤ 2560) :
    (⟨w64 p.N, p.nl⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ :=
  L.n_w.sub_right (wSub hd)

theorem a_w' {d k : Nat} (hd : d + k ≤ 2560) :
    (⟨w64 p.A, p.al⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ :=
  L.a_w.sub_right (wSub hd)

theorem d_w' {d k : Nat} (hd : d + k ≤ 2560) :
    (⟨w64 p.D, p.n⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ :=
  L.d_w.sub_right (wSub hd)

theorem t_w' {d k : Nat} (hd : d + k ≤ 2560) :
    (⟨w64 p.T, p.tl⟩ : Region).Disjoint ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ :=
  L.t_w.sub_right (wSub hd)

theorem bw' {d k : Nat} (hd : d + k ≤ 2560) : (stk p).Disjoint ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ :=
  L.bw.sub_right (wSub hd)

/-- The stack below `SP` that a call uses, within the 24 bytes. -/
theorem stkSub {k : Nat} (hk : k ≤ 24) : Region.Sub (below p.SP k) (stk p) := VG.X86.below_sub hk L.sp

theorem rounds_le : 16 * (p.R + 1) ≤ 240 := by rcases L.rounds with h | h | h <;> rw [h] <;> decide

theorem toNat_R : (BitVec.ofNat 32 p.R).toNat = p.R := by
  rcases L.rounds with h | h | h <;> rw [h] <;> rfl

theorem R_lt : p.R < 2 ^ 32 := by rcases L.rounds with h | h | h <;> rw [h] <;> decide

end Lay

namespace Perm

variable {p : Prm} {s : State} (P : Perm p s)
include P

theorem wW {d n : Nat} (h : d + n ≤ 2560) : InRegions s.wr (w64 p.W + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 2560) : InRegions (s.rd ++ s.wr) (w64 p.W + BitVec.ofNat 64 d) n :=
  in_left (P.wW h)

theorem wC {d n : Nat} (h : d + n ≤ 2560) : Covers [⟨w64 p.W + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

theorem wCR {d n : Nat} (h : d + n ≤ 2560) : Covers [⟨w64 p.W + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  covers_left (P.wC h)

/-- The first 2560 bytes of `W`, where AES-GCM's save area is. -/
theorem w2560 : Covers [⟨w64 p.W, 2560⟩] s.wr := P.w

theorem kR {d n : Nat} (h : d + n ≤ 256) : InRegions (s.rd ++ s.wr) (w64 p.K + BitVec.ofNat 64 d) n :=
  in_off P.k h (by decide)

end Perm

/-! ## What the pieces write -/

/-- The parts of `W` the pieces write: the blocks at `[0, 128)`, at
`[144, 176)`, the variables and blocks at `[216, 384)`, and from `384` on. -/
abbrev wA (W : BitVec 32) : Region := ⟨w64 W, 128⟩
abbrev wB (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 144, 32⟩
abbrev wV (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 216, 168⟩
abbrev wC (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 384, 2176⟩

/-- What the pieces may change: those parts of `W`, the stack below `SP`
and the data. -/
abbrev mutR (p : Prm) : List Region := [wA p.W, wB p.W, wV p.W, wC p.W, stk p, ⟨w64 p.D, p.n⟩]

/-- The regions `rs` are within `mutR`. -/
abbrev InMut (p : Prm) (rs : List Region) : Prop := ∀ r ∈ rs, ∃ r' ∈ mutR p, Region.Sub r r'

theorem frame_toMut {p : Prm} {rs : List Region} {m m' : Mem} (hf : Frame rs m m') (h : InMut p rs) :
    Frame (mutR p) m m' := hf.sub h

/-- A part of `W` in `wA`, `wB`, `wV` or `wC`. -/
theorem inMut_w (p : Prm) {d k : Nat}
    (h : d + k ≤ 128 ∨ 144 ≤ d ∧ d + k ≤ 176 ∨ 216 ≤ d ∧ d + k ≤ 384 ∨ 384 ≤ d ∧ d + k ≤ 2560) :
    ∃ r' ∈ mutR p, Region.Sub ⟨w64 p.W + BitVec.ofNat 64 d, k⟩ r' := by
  rcases h with h | h | h | h
  · exact ⟨wA p.W, by simp, Offset.sub_base _ h⟩
  · exact ⟨wB p.W, by simp, Offset.sub _ (by omega) (by omega)⟩
  · exact ⟨wV p.W, by simp, Offset.sub _ (by omega) (by omega)⟩
  · exact ⟨wC p.W, by simp, Offset.sub _ (by omega) (by omega)⟩

theorem inMut_stk (p : Prm) : ∃ r' ∈ mutR p, Region.Sub (stk p) r' := ⟨stk p, by simp, fun _ h => h⟩

theorem inMut_d (p : Prm) : ∃ r' ∈ mutR p, Region.Sub ⟨w64 p.D, p.n⟩ r' := ⟨_, by simp, fun _ h => h⟩

/-- The part of `W` at `[d, d + k)`, when it misses the parts the pieces write. -/
theorem kept_mut {p : Prm} (L : Lay p) {d k : Nat} (hd : 128 ≤ d ∧ d + k ≤ 144 ∨ 176 ≤ d ∧ d + k ≤ 216) :
    ∀ r ∈ mutR p, (⟨w64 p.W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using Lay.w_w (W := p.W) (a := d) (n := k) (d := 0) (k := 128) (.inr (by omega)) (by omega) (by decide)
  · exact Lay.w_w (by omega) (by omega) (by decide)
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact Lay.w_w (.inl (by omega)) (by omega) (by decide)
  · exact (L.bw' (by omega)).symm
  · exact (L.d_w' (by omega)).symm

/-- The slots, after code that changes only `mutR`. -/
theorem Slots.mut {p : Prm} (L : Lay p) {m m' : Mem} (hf : Frame (mutR p) m m') (S : Slots p m) : Slots p m' := by
  have k : ∀ o, 176 ≤ o ∧ o + 4 ≤ 216 → slotv m' p.W o = slotv m p.W o := fun o ho =>
    hf.readW (r := ⟨w64 p.W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (kept_mut L (.inr ho)) (by decide)
  exact ⟨by rw [k _ (by decide)]; exact S.ctx, by rw [k _ (by decide)]; exact S.rounds,
    by rw [k _ (by decide)]; exact S.nonce, by rw [k _ (by decide)]; exact S.nlen,
    by rw [k _ (by decide)]; exact S.aad, by rw [k _ (by decide)]; exact S.alen,
    by rw [k _ (by decide)]; exact S.data, by rw [k _ (by decide)]; exact S.len,
    by rw [k _ (by decide)]; exact S.tg, by rw [k _ (by decide)]; exact S.tlen⟩

/-- Our caller's registers saved at `W + 128`, after code that changes only
`mutR`. -/
theorem SavedAt.mut {p : Prm} (L : Lay p) {m m' : Mem} (hf : Frame (mutR p) m m') {s₀ : State}
    (h : Proof.AesGcm.X86.SavedAt m p.W s₀) : Proof.AesGcm.X86.SavedAt m' p.W s₀ :=
  h.frame hf (kept_mut L (.inl (by decide)))

/-- An environment, after code that keeps `ebp`, `esp` and the permissions,
and changes only `mutR`. -/
theorem Env.mut {p : Prm} (L : Lay p) {s s' : State} (h : Env p s) (hbp : s'.gpr .ebp = p.W)
    (hsp : s'.gpr .esp = p.SP) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hf : Frame (mutR p) s.mem s'.mem) :
    Env p s' :=
  ⟨hbp, hsp, h.perm.of_eq hrd hwr, h.slots.mut L hf⟩

/-- An environment, after code that keeps `ebp`, `esp`, the permissions and
the memory. -/
theorem Env.keep {p : Prm} {s s' : State} (h : Env p s) (hbp : s'.gpr .ebp = s.gpr .ebp)
    (hsp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hm : s'.mem = s.mem) : Env p s' :=
  ⟨by rw [hbp, h.ebp], by rw [hsp, h.esp], h.perm.of_eq hrd hwr, by rw [hm]; exact h.slots⟩

/-- The return address, after code that changes only `mutR`. -/
theorem ret_mut {p : Prm} (L : Lay p) {m m' : Mem} (hf : Frame (mutR p) m m') :
    m'.readW (w64 p.SP) 32 = m.readW (w64 p.SP) 32 :=
  Proof.AesGcm.X86.ret_kept hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact L.retW.sub_right (Region.sub_prefix (by decide))
    · exact L.retW.sub_right (Lay.wSub (by decide))
    · exact L.retW.sub_right (Lay.wSub (by decide))
    · exact L.retW.sub_right (Lay.wSub (by decide))
    · exact Proof.AesGcm.X86.ret_below L.sp
    · exact L.retD)

/-! ## Buffers apart from `W` and the stack -/

/-- The bytes of a buffer apart from `mutR` but the data. -/
theorem bytes_mut {p : Prm} {P : BitVec 32} {len : Nat}
    (hw : (⟨w64 P, len⟩ : Region).Disjoint ⟨w64 p.W, 2560⟩) (hb : (stk p).Disjoint ⟨w64 P, len⟩)
    (hd : (⟨w64 P, len⟩ : Region).Disjoint ⟨w64 p.D, p.n⟩) (hl : len ≤ 2 ^ 64) {m m' : Mem}
    (hf : Frame (mutR p) m m') : bytesAt m' (w64 P) len = bytesAt m (w64 P) len :=
  Proof.AesGcm.X86.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hw.sub_right (Region.sub_prefix (by decide))
    · exact hw.sub_right (Lay.wSub (by decide))
    · exact hw.sub_right (Lay.wSub (by decide))
    · exact hw.sub_right (Lay.wSub (by decide))
    · exact hb.symm
    · exact hd) hl

theorem ctx_mut {p : Prm} (L : Lay p) {m m' : Mem} (hf : Frame (mutR p) m m') :
    bytesAt m' (w64 p.K) 256 = bytesAt m (w64 p.K) 256 := bytes_mut L.k_w L.bk L.k_d (by decide) hf

theorem nonce_mut {p : Prm} (L : Lay p) {m m' : Mem} (hf : Frame (mutR p) m m') :
    bytesAt m' (w64 p.N) p.nl = bytesAt m (w64 p.N) p.nl :=
  bytes_mut L.n_w L.bn L.n_d (by have := L.nl15; omega) hf

theorem aad_mut {p : Prm} (L : Lay p) {m m' : Mem} (hf : Frame (mutR p) m m') :
    bytesAt m' (w64 p.A) p.al = bytesAt m (w64 p.A) p.al :=
  bytes_mut L.a_w L.ba L.a_d (by have := L.aw; omega) hf

theorem tag_mut {p : Prm} (L : Lay p) {m m' : Mem} (hf : Frame (mutR p) m m') :
    bytesAt m' (w64 p.T) p.tl = bytesAt m (w64 p.T) p.tl :=
  bytes_mut L.t_w L.bt L.t_d (by have := L.tl16; omega) hf

end VG.Proof.AesOcb.X86

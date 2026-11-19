module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Callee
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Loops
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Gcm.Stream
public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Aes
public import VerifiedGarbage.Spec.GcmSiv
public import VerifiedGarbage.Proof.AesOcb.PPC64LE.Callee
import VerifiedGarbage.Proof.Ocb.State
public import VerifiedGarbage.Proof.ChaCha20Poly1305.PPC64LE.Wp
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Gather.PPC64LE.Copy
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PPC64LE.Inline

/-! ### `AesGcmSiv.PPC64LE.Env`, which this module and modules that import it used -/

section

/-!
# AES-GCM-SIV on PPC64LE: where everything is

Untrusted: everything here is checked by Lean. The public values of a call
(`Cx`): the key schedule of the key-generating key (240 bytes at `K`), the
working space (3824 bytes at `W`), the nonce (12 bytes at `N`), the
additional data (`al` bytes at `A`), the data (`n` bytes at `D`), the tag
(16 bytes at `T`) and the number of rounds; what the precondition says of
them (`Lay`); what a state may access (`Perm`); and the registers holding
them throughout (`Env`), which the functions called preserve. What a piece
keeps of the registers is `PK`, as for AES-GCM.
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.PPC64LE

open VG VG.PPC64LE
open VG.Proof.Gather.PPC64LE (covers_off in_off)

/-! ## The public values -/

/-- The public values of a call of `seal` or `open`. -/
structure Cx where
  K : Addr
  W : Addr
  N : Addr
  A : Addr
  D : Addr
  T : Addr
  R : Nat
  al : Nat
  n : Nat

/-- What the precondition says of the public values. -/
structure Lay (c : Cx) : Prop where
  kw : c.K.toNat + 240 ≤ 2 ^ 64
  ww : c.W.toNat + 3824 ≤ 2 ^ 64
  nw : c.N.toNat + 12 ≤ 2 ^ 64
  aw : c.A.toNat + c.al ≤ 2 ^ 64
  dw : c.D.toNat + c.n ≤ 2 ^ 64
  tw : c.T.toNat + 16 ≤ 2 ^ 64
  k_w : (⟨c.K, 240⟩ : Region).Disjoint ⟨c.W, 3824⟩
  k_d : (⟨c.K, 240⟩ : Region).Disjoint ⟨c.D, c.n⟩
  n_w : (⟨c.N, 12⟩ : Region).Disjoint ⟨c.W, 3824⟩
  n_d : (⟨c.N, 12⟩ : Region).Disjoint ⟨c.D, c.n⟩
  a_w : (⟨c.A, c.al⟩ : Region).Disjoint ⟨c.W, 3824⟩
  a_d : (⟨c.A, c.al⟩ : Region).Disjoint ⟨c.D, c.n⟩
  d_w : (⟨c.D, c.n⟩ : Region).Disjoint ⟨c.W, 3824⟩
  t_w : (⟨c.T, 16⟩ : Region).Disjoint ⟨c.W, 3824⟩
  t_d : (⟨c.T, 16⟩ : Region).Disjoint ⟨c.D, c.n⟩
  rounds : c.R = 10 ∨ c.R = 14
  n_lt : c.n < 2 ^ 64
  al_lt : c.al < 2 ^ 64

/-- What a state may access. -/
structure Perm (c : Cx) (s : State) : Prop where
  k : Covers [⟨c.K, 240⟩] (s.rd ++ s.wr)
  w : Covers [⟨c.W, 3824⟩] s.wr
  nc : Covers [⟨c.N, 12⟩] (s.rd ++ s.wr)
  a : Covers [⟨c.A, c.al⟩] (s.rd ++ s.wr)
  d : Covers [⟨c.D, c.n⟩] s.wr
  t : Covers [⟨c.T, 16⟩] (s.rd ++ s.wr)

theorem Perm.of_eq {c : Cx} {s s' : State} (h : Perm c s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Perm c s' :=
  ⟨by rw [hrd, hwr]; exact h.k, by rw [hwr]; exact h.w, by rw [hrd, hwr]; exact h.nc,
    by rw [hrd, hwr]; exact h.a, by rw [hwr]; exact h.d, by rw [hrd, hwr]; exact h.t⟩

/-! ## What the pieces keep -/

/-- The registers the pieces keep: the public values, and our caller's. -/
def keepRegs : List Reg :=
  [.r2, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r26, .r27, .r28, .r29, .r30, .r31]

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

theorem PK.ofUpd {s t : State} {d : Reg} {v : BitVec 64} (u : Proof.ChaCha20Poly1305.PPC64LE.Upd s t d v)
    (hd : d ∉ keepRegs := by decide) : PK s t :=
  ⟨u.rd, u.wr, u.sp, fun r hr => u.other r fun h => hd (h ▸ hr)⟩

theorem PK.ofMupd {s t : State} {m : Mem} (u : Proof.ChaCha20Poly1305.PPC64LE.Mupd s t m) : PK s t :=
  ⟨u.rd, u.wr, u.sp, fun r _ => by rw [u.gpr]⟩

theorem keep_preserved : ∀ r ∈ keepRegs, r ∈ preserved := by decide

/-- After a call, which keeps the nonvolatile registers. -/
theorem PK.ofSaved {s t : State} (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hsp : t.sp = s.sp)
    (hs : ∀ r ∈ preserved, t.gpr r = s.gpr r) : PK s t :=
  ⟨hrd, hwr, hsp, fun r hr => hs r (keep_preserved r hr)⟩

/-! ## The environment -/

/-- The registers holding the public values throughout, and what the state
may access. -/
structure Env (c : Cx) (s : State) : Prop where
  r14 : s.gpr .r14 = c.W
  r15 : s.gpr .r15 = c.N
  r16 : s.gpr .r16 = c.K
  r17 : s.gpr .r17 = BitVec.ofNat 64 c.R
  r18 : s.gpr .r18 = c.A
  r19 : s.gpr .r19 = BitVec.ofNat 64 c.al
  r20 : s.gpr .r20 = c.D
  r21 : s.gpr .r21 = BitVec.ofNat 64 c.n
  r22 : s.gpr .r22 = c.T
  perm : Perm c s

theorem Env.of_pk {c : Cx} {s s' : State} (h : Env c s) (k : PK s s') : Env c s' :=
  ⟨by rw [k.gpr .r14 (by decide), h.r14], by rw [k.gpr .r15 (by decide), h.r15],
    by rw [k.gpr .r16 (by decide), h.r16], by rw [k.gpr .r17 (by decide), h.r17],
    by rw [k.gpr .r18 (by decide), h.r18], by rw [k.gpr .r19 (by decide), h.r19],
    by rw [k.gpr .r20 (by decide), h.r20], by rw [k.gpr .r21 (by decide), h.r21],
    by rw [k.gpr .r22 (by decide), h.r22], h.perm.of_eq k.rd k.wr⟩

namespace Lay

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 3824) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 3824⟩ :=
  Offset.sub_base _ h

variable {c : Cx} (L : Lay c)
include L

/-- Parts of `W` are disjoint. -/
theorem w_w {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 3824) (hd : d + k ≤ 3824) :
    (⟨c.W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by have := L.ww; omega_using [ha]) (by have := L.ww; omega_using [hd])

omit L in
/-- `W` and a part of it. -/
theorem w0_w {n d k : Nat} (h : n ≤ d) (hd : d + k ≤ 3824) :
    (⟨c.W, n⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  Offset.base_disjoint _ h (by omega_using [hd])

theorem k_w' {d k : Nat} (hd : d + k ≤ 3824) : (⟨c.K, 240⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  L.k_w.sub_right (wSub hd)

theorem a_w' {d k : Nat} (hd : d + k ≤ 3824) : (⟨c.A, c.al⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  L.a_w.sub_right (wSub hd)

theorem d_w' {d k : Nat} (hd : d + k ≤ 3824) : (⟨c.D, c.n⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  L.d_w.sub_right (wSub hd)

theorem wrapW {d : Nat} (hd : d < 3824) : (c.W + BitVec.ofNat 64 d).toNat = c.W.toNat + d := by
  have := L.ww
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_using [hd]), Nat.mod_eq_of_lt (by omega_using [hd, this])]

theorem rb : 16 * (c.R + 1) ≤ 240 := by rcases L.rounds with h | h <;> rw [h] <;> decide

end Lay

namespace Perm

variable {c : Cx} {s : State} (P : Perm c s)
include P

theorem wW {d n : Nat} (h : d + n ≤ 3824) : InRegions s.wr (c.W + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wC {d n : Nat} (h : d + n ≤ 3824) : Covers [⟨c.W + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

theorem wCR {d n : Nat} (h : d + n ≤ 3824) : Covers [⟨c.W + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  Covers.right (P.wC h)

theorem wR {d n : Nat} (h : d + n ≤ 3824) : InRegions (s.rd ++ s.wr) (c.W + BitVec.ofNat 64 d) n :=
  P.wCR h _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

theorem nR {d n : Nat} (h : d + n ≤ 12) : InRegions (s.rd ++ s.wr) (c.N + BitVec.ofNat 64 d) n :=
  in_off P.nc h (by decide)

theorem tR {d n : Nat} (h : d + n ≤ 16) : InRegions (s.rd ++ s.wr) (c.T + BitVec.ofNat 64 d) n :=
  in_off P.t h (by decide)

end Perm

end VG.Proof.AesGcmSiv.PPC64LE

end

end

/-!
# AES-GCM-SIV on PPC64LE: arithmetic and the arguments of calls

Untrusted: everything here is checked by Lean. Shifts and differences of
small numbers as 64-bit words; and the arguments of `vg_aes_ctr32` from the
environment (`cargs`): the encryption key's schedule at `W + 256` or the
key-generating key's at `K`, the counter block at `W + 112`, `k` blocks at
`Q` and the working space at `W + 1776`.
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.PPC64LE

open VG VG.PPC64LE
open VG.Proof.AesGcm.PPC64LE (CtrCall)

theorem ofNat_shl (a k : Nat) : BitVec.ofNat 64 a <<< k = BitVec.ofNat 64 (2 ^ k * a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_mul_mod]
  rw [Nat.mul_comm]

theorem ofNat_lsr {a : Nat} (k : Nat) (ha : a < 2 ^ 64) : BitVec.ofNat 64 a >>> k = BitVec.ofNat 64 (a / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha)]

theorem ofNat_sub {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := b) (by omega_using [h, ha]), Nat.mod_eq_of_lt (a := a) ha, Nat.mod_eq_of_lt (a := a - b) (by omega_using [ha])]
  omega_using [h, ha]

theorem ofNat_add (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) :=
  (BitVec.ofNat_add a b).symm

/-- What code keeps that writes none of the registers the pieces keep. -/
theorem PK.ofKeep {rs : List Reg} {s s' : State} (h : Keep rs s s') (hsp : s'.sp = s.sp)
    (hd : ∀ r ∈ keepRegs, r ∉ rs := by decide) : PK s s' :=
  ⟨h.2.1, h.2.2, hsp, fun r hr => h.gpr (hd r hr)⟩

/-- What the copy and XOR loops keep. -/
theorem PK.ofLoop {s s' : State} {S D : Addr} {n : Nat} (O : Proof.AesGcm.PPC64LE.LoopOut s S D n s') : PK s s' :=
  ⟨O.keeps.1, O.keeps.2.1, O.keeps.2.2.1, fun r hr => by
    have h : r ≠ .r0 ∧ r ≠ .r3 ∧ r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 := by
      revert r; decide
    exact O.other r h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2⟩

/-- Two writes of the same register. -/
theorem upd2 {s t u : State} {d : Reg} {v w w' : BitVec 64} (u₁ : Proof.ChaCha20Poly1305.PPC64LE.Upd s t d v)
    (u₂ : Proof.ChaCha20Poly1305.PPC64LE.Upd t u d w) (h : w = w') : Proof.ChaCha20Poly1305.PPC64LE.Upd s u d w' :=
  ⟨u₂.gpr.trans h, fun r hr => (u₂.other r hr).trans (u₁.other r hr), u₂.mem.trans u₁.mem, u₂.rd.trans u₁.rd,
    u₂.wr.trans u₁.wr, u₂.sp.trans u₁.sp, u₂.lr.trans u₁.lr⟩

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) : Spec.Gcm.blockAt m' p = Spec.Gcm.blockAt m p := by
  rw [Spec.Gcm.blockAt, Spec.Gcm.blockAt, Proof.Cmac.bytesAt_frame16 hf hd]

theorem blocksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, 16 * n⟩ : Region).Disjoint r) (hn : 16 * n ≤ 2 ^ 64) :
    Spec.Gcm.blocksAt m' p n = Spec.Gcm.blocksAt m p n := by
  rw [Proof.Gcm.blocksAt_eq, Proof.Gcm.blocksAt_eq, Proof.Cmac.bytesAt_frame hf hd hn]

theorem setWidth_32_64 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

/-- The arguments of `vg_aes_ctr32`: the schedule of `R` rounds at `K'`, the
counter block at `W + 112`, `k` blocks at `Q`, which it may write, and the
working space at `W + 1776`. -/
theorem cargs {c : Cx} (L : Lay c) {s : State} (E : Env c s) {K' : Addr}
    (hK : Covers [⟨K', 240⟩] (s.rd ++ s.wr)) (hKw : (⟨K', 240⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 112, 16⟩)
    (hKs : (⟨K', 240⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 1776, 2048⟩)
    {Q : Addr} {k : Nat} (hqk : (⟨K', 240⟩ : Region).Disjoint ⟨Q, 16 * k⟩)
    (hqc : (⟨c.W + BitVec.ofNat 64 112, 16⟩ : Region).Disjoint ⟨Q, 16 * k⟩)
    (hqs : (⟨Q, 16 * k⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 1776, 2048⟩)
    (hqw : Covers [⟨Q, 16 * k⟩] s.wr) (hfit : Q.toNat + 16 * k ≤ 2 ^ 64) (hk : k < 2 ^ 64)
    (r3 : s.gpr .r3 = K') (r4 : s.gpr .r4 = BitVec.ofNat 64 c.R) (r5 : s.gpr .r5 = c.W + BitVec.ofNat 64 112)
    (r6 : s.gpr .r6 = Q) (r7 : s.gpr .r7 = BitVec.ofNat 64 k) (r8 : s.gpr .r8 = c.W + BitVec.ofNat 64 1776) :
    CtrCall s K' (c.W + BitVec.ofNat 64 112) Q (c.W + BitVec.ofNat 64 1776) c.R k where
  r3 := r3
  r4 := r4
  r5 := r5
  r6 := r6
  r7 := r7
  r8 := r8
  rounds := by rcases L.rounds with h | h <;> simp [h]
  n_lt := hk
  kc := hKw
  kd := hqk
  ks := hKs
  cd := hqc
  cs := L.w_w (.inl (by decide)) (by decide) (by decide)
  ds := hqs
  fit := hfit
  reads := Covers.append_left (Covers.cons hK Covers.nil)
    (Covers.cons (E.perm.wCR (by decide)) (Covers.cons (Covers.right hqw) (Covers.cons (E.perm.wCR (by decide))
      Covers.nil)))
  writes := Covers.cons (E.perm.wC (by decide)) (Covers.cons hqw (Covers.cons (E.perm.wC (by decide)) Covers.nil))

/-- The bytes just past what `writeBytes` writes are unchanged. -/
theorem bytesAt_writeBytes_past (m : Mem) (q : Addr) (xs : List Byte) (k : Nat) (h : xs.length + k ≤ 2 ^ 64) :
    Spec.Aes.bytesAt (VG.WriteBytes.writeBytes m q xs) (q + BitVec.ofNat 64 xs.length) k = Spec.Aes.bytesAt m (q + BitVec.ofNat 64 xs.length) k := by
  simp only [Spec.Aes.bytesAt, List.map_inj_left, List.mem_range]
  intro j hj
  simp only [VG.WriteBytes.writeBytes]
  rw [show q + BitVec.ofNat 64 xs.length + BitVec.ofNat 64 j - q = BitVec.ofNat 64 (xs.length + j) by
      rw [BitVec.add_assoc, Offset.add_sub_cancel_left, ← BitVec.ofNat_add],
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h, hj])]
  simp only [show ¬ xs.length + j < xs.length by omega_using [], ↓reduceIte]

/-- The arguments of `vg_aes_encrypt_blocks`: the schedule of `R` rounds at
`K'`, `k` blocks at `W + 496` and the working space at `W + 1776`. -/
theorem bargs {c : Cx} (L : Lay c) {s : State} (E : Env c s) {K' : Addr}
    (hK : Covers [⟨K', 240⟩] (s.rd ++ s.wr)) {k : Nat} (hk : k ≤ 64)
    (hKd : (⟨K', 240⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 496, 16 * k⟩)
    (hKs : (⟨K', 240⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 1776, 2048⟩)
    (r3 : s.gpr .r3 = K') (r4 : s.gpr .r4 = BitVec.ofNat 64 c.R)
    (r5 : s.gpr .r5 = c.W + BitVec.ofNat 64 496) (r6 : s.gpr .r6 = BitVec.ofNat 64 k)
    (r7 : s.gpr .r7 = c.W + BitVec.ofNat 64 1776) :
    Proof.AesOcb.PPC64LE.BCallS s K' (c.W + BitVec.ofNat 64 496) (c.W + BitVec.ofNat 64 1776) c.R k where
  r3 := r3
  r4 := r4
  r5 := r5
  r6 := r6
  r7 := r7
  rounds := by rcases L.rounds with h | h <;> simp [h]
  wrap := by rw [L.wrapW (by decide)]; have := L.ww; omega_using [hk, this]
  kd := hKd
  ks := hKs
  ds := L.w_w (.inl (by omega_using [hk])) (by omega_using [hk]) (by decide)
  reads := Covers.append_left (Covers.cons hK Covers.nil)
    (Covers.cons (E.perm.wCR (by omega_using [hk])) (Covers.cons (E.perm.wCR (by decide)) Covers.nil))
  writes := Covers.cons (E.perm.wC (by omega_using [hk])) (Covers.cons (E.perm.wC (by decide)) Covers.nil)

/-- A block `vg_aes_encrypt_blocks` replaced: the cipher of the old one. -/
theorem bytesAt_cipher {m m' : Mem} {D : Addr} {k : Nat} {R : Nat} {w : List Byte}
    (h : Spec.Aes.statesAt m' D k = (Spec.Aes.statesAt m D k).map (Spec.Aes.cipher R w)) {l : Nat} (hl : l < k) :
    Spec.Aes.bytesAt m' (D + BitVec.ofNat 64 (16 * l)) 16 =
      Spec.GcmSiv.aesWith R w (Spec.Aes.bytesAt m (D + BitVec.ofNat 64 (16 * l)) 16) := by
  have e : Spec.Aes.stateAt m (D + BitVec.ofNat 64 (16 * l)) =
      Vector.ofFn fun i => (Spec.Aes.bytesAt m (D + BitVec.ofNat 64 (16 * l)) 16).getD i.1 0 := by
    apply Vector.ext
    intro i hi
    simp [Spec.Aes.stateAt, Spec.Aes.bytesAt, List.getD_eq_getElem?_getD]
  rw [Proof.Ocb.bytesAt_toList, Proof.Ocb.stateAt_of_statesAt h hl, e]
  rfl

end VG.Proof.AesGcmSiv.PPC64LE

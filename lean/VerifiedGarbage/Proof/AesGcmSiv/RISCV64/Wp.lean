module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Callee
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Loops
public import VerifiedGarbage.Proof.AesOcb.RISCV64.Callee
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Gcm.Stream
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Env

/-! ### `AesGcmSiv.RISCV64.Env`, which this module and modules that import it used -/

section

/-!
# AES-GCM-SIV on RISC-V: where everything is

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/AesGcmSiv/PPC64LE/Wp.lean`): the public values of a call (`Cx`):
the key schedule of the key-generating key (240 bytes at `K`), the working
space (3840 bytes at `W`), the nonce (12 bytes at `N`), the additional data
(`al` bytes at `A`), the data (`n` bytes at `D`), the tag (16 bytes at `T`),
the number of rounds and the stack pointer `SP`, below which `vg_ghash`'s
frame takes 2048 bytes; what the precondition says of them (`Lay`); what a
state may access (`Perm`); and the registers holding them throughout
(`Env`), which the functions called preserve. What a piece keeps of the
registers is `PK`.
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.RISCV64

open VG VG.RISCV64
open VG.Proof.AesGcm.RISCV64 (covers_off in_off covers_prefix)

/-! ## The public values -/

/-- The public values of a call of `seal` or `open`. -/
structure Cx where
  K : Addr
  W : Addr
  N : Addr
  A : Addr
  D : Addr
  T : Addr
  SP : Addr
  R : Nat
  al : Nat
  n : Nat

/-- What the precondition says of the public values. -/
structure Lay (c : Cx) : Prop where
  kw : c.K.toNat + 240 ≤ 2 ^ 64
  ww : c.W.toNat + 3840 ≤ 2 ^ 64
  nw : c.N.toNat + 12 ≤ 2 ^ 64
  aw : c.A.toNat + c.al ≤ 2 ^ 64
  dw : c.D.toNat + c.n ≤ 2 ^ 64
  tw : c.T.toNat + 16 ≤ 2 ^ 64
  k_w : (⟨c.K, 240⟩ : Region).Disjoint ⟨c.W, 3840⟩
  k_d : (⟨c.K, 240⟩ : Region).Disjoint ⟨c.D, c.n⟩
  n_w : (⟨c.N, 12⟩ : Region).Disjoint ⟨c.W, 3840⟩
  n_d : (⟨c.N, 12⟩ : Region).Disjoint ⟨c.D, c.n⟩
  a_w : (⟨c.A, c.al⟩ : Region).Disjoint ⟨c.W, 3840⟩
  a_d : (⟨c.A, c.al⟩ : Region).Disjoint ⟨c.D, c.n⟩
  d_w : (⟨c.D, c.n⟩ : Region).Disjoint ⟨c.W, 3840⟩
  t_w : (⟨c.T, 16⟩ : Region).Disjoint ⟨c.W, 3840⟩
  t_d : (⟨c.T, 16⟩ : Region).Disjoint ⟨c.D, c.n⟩
  rounds : c.R = 10 ∨ c.R = 14
  n_lt : c.n < 2 ^ 64
  al_lt : c.al < 2 ^ 64
  wal : c.W.toNat % 8 = 0
  spal : c.SP.toNat % 16 = 0
  spge : 2048 ≤ c.SP.toNat
  b_w : (below c.SP 2048).Disjoint ⟨c.W, 3840⟩
  b_a : (below c.SP 2048).Disjoint ⟨c.A, c.al⟩
  b_d : (below c.SP 2048).Disjoint ⟨c.D, c.n⟩

/-- What a state may access. -/
structure Perm (c : Cx) (s : State) : Prop where
  k : Covers [⟨c.K, 240⟩] (s.rd ++ s.wr)
  w : Covers [⟨c.W, 3840⟩] s.wr
  nc : Covers [⟨c.N, 12⟩] (s.rd ++ s.wr)
  a : Covers [⟨c.A, c.al⟩] (s.rd ++ s.wr)
  d : Covers [⟨c.D, c.n⟩] s.wr
  t : Covers [⟨c.T, 16⟩] (s.rd ++ s.wr)

theorem Perm.of_eq {c : Cx} {s s' : State} (h : Perm c s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Perm c s' :=
  ⟨by rw [hrd, hwr]; exact h.k, by rw [hwr]; exact h.w, by rw [hrd, hwr]; exact h.nc,
    by rw [hrd, hwr]; exact h.a, by rw [hwr]; exact h.d, by rw [hrd, hwr]; exact h.t⟩

/-- Where the nonce's copy is. -/
def nP (W : Addr) : Addr := W + BitVec.ofNat 64 1520

/-! ## What the pieces keep -/

/-- The registers the pieces keep: those holding the public values. -/
def keepRegs : List Reg := [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8]

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

theorem PK.ofUpd {s t : State} {d : Reg} {v : BitVec 64} (u : Steps.Upd s t d v)
    (hd : d ∉ keepRegs := by decide) : PK s t :=
  ⟨u.rd, u.wr, u.sp, fun r hr => u.other r fun h => hd (h ▸ hr)⟩

theorem PK.ofMupd {s t : State} {m : Mem} (u : Steps.Mupd s t m) : PK s t :=
  ⟨u.rd, u.wr, u.sp, fun r _ => by rw [u.gpr]⟩

theorem keep_preserved : ∀ r ∈ keepRegs, r ∈ preserved := by decide

/-- After a call, which keeps the callee-saved registers. -/
theorem PK.ofSaved {s t : State} (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hsp : t.sp = s.sp)
    (hs : ∀ r ∈ preserved, t.gpr r = s.gpr r) : PK s t :=
  ⟨hrd, hwr, hsp, fun r hr => hs r (keep_preserved r hr)⟩

/-! ## The environment -/

/-- The registers holding the public values throughout, the stack pointer,
and what the state may access. -/
structure Env (c : Cx) (s : State) : Prop where
  s0 : s.gpr .s0 = c.W
  s1 : s.gpr .s1 = c.N
  s2 : s.gpr .s2 = c.K
  s3 : s.gpr .s3 = BitVec.ofNat 64 c.R
  s4 : s.gpr .s4 = c.A
  s5 : s.gpr .s5 = BitVec.ofNat 64 c.al
  s6 : s.gpr .s6 = c.D
  s7 : s.gpr .s7 = BitVec.ofNat 64 c.n
  s8 : s.gpr .s8 = c.T
  sp : s.sp = c.SP
  perm : Perm c s

theorem Env.of_pk {c : Cx} {s s' : State} (h : Env c s) (k : PK s s') : Env c s' :=
  ⟨by rw [k.gpr .s0 (by decide), h.s0], by rw [k.gpr .s1 (by decide), h.s1],
    by rw [k.gpr .s2 (by decide), h.s2], by rw [k.gpr .s3 (by decide), h.s3],
    by rw [k.gpr .s4 (by decide), h.s4], by rw [k.gpr .s5 (by decide), h.s5],
    by rw [k.gpr .s6 (by decide), h.s6], by rw [k.gpr .s7 (by decide), h.s7],
    by rw [k.gpr .s8 (by decide), h.s8], k.sp.trans h.sp, h.perm.of_eq k.rd k.wr⟩

namespace Lay

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 3840) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 3840⟩ :=
  Offset.sub_base _ h

variable {c : Cx} (L : Lay c)
include L

/-- Parts of `W` are disjoint. -/
theorem w_w {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 3840) (hd : d + k ≤ 3840) :
    (⟨c.W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by have := L.ww; omega_using [ha]) (by have := L.ww; omega_using [hd])

omit L in
/-- `W` and a part of it. -/
theorem w0_w {n d k : Nat} (h : n ≤ d) (hd : d + k ≤ 3840) :
    (⟨c.W, n⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  Offset.base_disjoint _ h (by omega_using [hd])

theorem k_w' {d k : Nat} (hd : d + k ≤ 3840) : (⟨c.K, 240⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  L.k_w.sub_right (wSub hd)

theorem n_w' {d k : Nat} (hd : d + k ≤ 3840) : (⟨c.N, 12⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  L.n_w.sub_right (wSub hd)

theorem a_w' {d k : Nat} (hd : d + k ≤ 3840) : (⟨c.A, c.al⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  L.a_w.sub_right (wSub hd)

theorem d_w' {d k : Nat} (hd : d + k ≤ 3840) : (⟨c.D, c.n⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  L.d_w.sub_right (wSub hd)

theorem b_w' {d k : Nat} (hd : d + k ≤ 3840) : (below c.SP 2048).Disjoint ⟨c.W + BitVec.ofNat 64 d, k⟩ :=
  L.b_w.sub_right (wSub hd)

theorem wrapW {d : Nat} (hd : d < 3840) : (c.W + BitVec.ofNat 64 d).toNat = c.W.toNat + d := by
  have := L.ww
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega_using [hd]), Nat.mod_eq_of_lt (by omega_using [hd, this])]

/-- `W + d` is aligned for a multiple `d` of 8. -/
theorem wal8 {d : Nat} (hd : d < 3840) (h8 : d % 8 = 0) : (c.W + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  rw [L.wrapW hd]; have := L.wal; omega_using [h8, this]

/-- `W + d` is aligned for a multiple `d` of 4. -/
theorem wal4 {d : Nat} (hd : d < 3840) (h4 : d % 4 = 0) : (c.W + BitVec.ofNat 64 d).toNat % 4 = 0 := by
  rw [L.wrapW hd]; have := L.wal; omega_using [h4, this]

theorem rb : 16 * (c.R + 1) ≤ 240 := by rcases L.rounds with h | h <;> rw [h] <;> decide

end Lay

namespace Perm

variable {c : Cx} {s : State} (P : Perm c s)
include P

theorem wW {d n : Nat} (h : d + n ≤ 3840) : InRegions s.wr (c.W + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wC {d n : Nat} (h : d + n ≤ 3840) : Covers [⟨c.W + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

theorem wCR {d n : Nat} (h : d + n ≤ 3840) : Covers [⟨c.W + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  Covers.right (P.wC h)

theorem wR {d n : Nat} (h : d + n ≤ 3840) : InRegions (s.rd ++ s.wr) (c.W + BitVec.ofNat 64 d) n :=
  P.wCR h _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

end Perm

end VG.Proof.AesGcmSiv.RISCV64

end

end

/-!
# AES-GCM-SIV on RISC-V: arithmetic and the arguments of calls

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/AesGcmSiv/PPC64LE/Wp.lean`): shifts and differences of small
numbers as 64-bit words; and the arguments of `vg_aes_ctr32` from the
environment (`cargs`): the encryption key's schedule at `W + 256` or the
key-generating key's at `K`, the counter block at `W + 112`, `k` blocks at
`Q` and the working space at `W + 1792`; and those of
`vg_aes_encrypt_blocks` (`bargs`): a schedule, `k` blocks at `W + 496` and
the same working space.
-/

@[expose] public section

namespace VG.Proof.AesGcmSiv.RISCV64

open VG VG.RISCV64
open VG.Proof.AesGcm.RISCV64 (CtrCall LoopOut)

theorem wp_and {s : State} {is : List Instr} {Q : State → Prop} {d n m : Reg}
    (k : ∀ s', Steps.Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and d n m :: is)) s Q :=
  Steps.WP.cons exec_logic (k _ (Steps.Upd.write _ _ _))

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

/-- What the copy and XOR loops keep. -/
theorem PK.ofLoop {s s' : State} {S D : Addr} {n : Nat} (O : LoopOut s S D n s') : PK s s' :=
  ⟨O.keeps.1, O.keeps.2.1, O.keeps.2.2, fun r hr => by
    have h : r ≠ .t0 ∧ r ≠ .a0 ∧ r ≠ .a1 ∧ r ≠ .a2 ∧ r ≠ .a3 := by
      revert r; decide
    exact O.other r h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2⟩

/-- Two writes of the same register. -/
theorem upd2 {s t u : State} {d : Reg} {v w w' : BitVec 64} (u₁ : Steps.Upd s t d v)
    (u₂ : Steps.Upd t u d w) (h : w = w') : Steps.Upd s u d w' :=
  ⟨u₂.gpr.trans h, fun r hr => (u₂.other r hr).trans (u₁.other r hr), u₂.mem.trans u₁.mem, u₂.rd.trans u₁.rd,
    u₂.wr.trans u₁.wr, u₂.sp.trans u₁.sp⟩

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
working space at `W + 1792`. -/
theorem cargs {c : Cx} (L : Lay c) {s : State} (E : Env c s) {K' : Addr}
    (hK : Covers [⟨K', 240⟩] (s.rd ++ s.wr)) (hKw : (⟨K', 240⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 112, 16⟩)
    (hKs : (⟨K', 240⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 1792, 2048⟩)
    {Q : Addr} {k : Nat} (hqk : (⟨K', 240⟩ : Region).Disjoint ⟨Q, 16 * k⟩)
    (hqc : (⟨c.W + BitVec.ofNat 64 112, 16⟩ : Region).Disjoint ⟨Q, 16 * k⟩)
    (hqs : (⟨Q, 16 * k⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 1792, 2048⟩)
    (hqw : Covers [⟨Q, 16 * k⟩] s.wr) (hfit : Q.toNat + 16 * k ≤ 2 ^ 64) (hk : k < 2 ^ 64)
    (a0 : s.gpr .a0 = K') (a1 : s.gpr .a1 = BitVec.ofNat 64 c.R) (a2 : s.gpr .a2 = c.W + BitVec.ofNat 64 112)
    (a3 : s.gpr .a3 = Q) (a4 : s.gpr .a4 = BitVec.ofNat 64 k) (a5 : s.gpr .a5 = c.W + BitVec.ofNat 64 1792) :
    CtrCall s K' (c.W + BitVec.ofNat 64 112) Q (c.W + BitVec.ofNat 64 1792) c.R k where
  a0 := a0
  a1 := a1
  a2 := a2
  a3 := a3
  a4 := a4
  a5 := a5
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

/-- The arguments of `vg_aes_encrypt_blocks`: the schedule of `R` rounds at
`K'`, `k` blocks at `W + 496` and the working space at `W + 1792`. -/
theorem bargs {c : Cx} (L : Lay c) {s : State} (E : Env c s) {K' : Addr}
    (hK : Covers [⟨K', 240⟩] (s.rd ++ s.wr)) {k : Nat} (hk : k ≤ 64)
    (hKd : (⟨K', 240⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 496, 16 * k⟩)
    (hKs : (⟨K', 240⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 1792, 2048⟩)
    (a0 : s.gpr .a0 = K') (a1 : s.gpr .a1 = BitVec.ofNat 64 c.R) (a2 : s.gpr .a2 = c.W + BitVec.ofNat 64 496)
    (a3 : s.gpr .a3 = BitVec.ofNat 64 k) (a4 : s.gpr .a4 = c.W + BitVec.ofNat 64 1792) :
    Proof.AesOcb.RISCV64.BCall s K' (c.W + BitVec.ofNat 64 496) (c.W + BitVec.ofNat 64 1792) c.R k where
  a0 := a0
  a1 := a1
  a2 := a2
  a3 := a3
  a4 := a4
  rounds := by rcases L.rounds with h | h <;> simp [h]
  wrap := by rw [L.wrapW (by decide)]; have := L.ww; omega_using [hk, this]
  kd := hKd
  ks := hKs
  ds := L.w_w (.inl (by omega_using [hk])) (by omega_using [hk]) (by decide)
  reads := Covers.append_left (Covers.cons hK Covers.nil)
    (Covers.cons (E.perm.wCR (by omega_using [hk])) (Covers.cons (E.perm.wCR (by decide)) Covers.nil))
  writes := Covers.cons (E.perm.wC (by omega_using [hk])) (Covers.cons (E.perm.wC (by decide)) Covers.nil)

end VG.Proof.AesGcmSiv.RISCV64

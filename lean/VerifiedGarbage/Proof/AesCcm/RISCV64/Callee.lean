module

public import VerifiedGarbage.Proof.AesCcm.RISCV64.Env
public import VerifiedGarbage.Proof.CmacAes.Stream.RISCV64.Common
public import VerifiedGarbage.Proof.AesCtr.RISCV64.Call
import VerifiedGarbage.Proof.Framework.Offset

/-!
# AES-CCM on RISC-V: the functions called

Untrusted: everything here is checked by Lean. The calls of
`vg_cmac_aes_update` are those of streaming AES-CMAC
(`Proof.CmacAes.Stream.RISCV64.upd_call`), and those of `vg_aes_ctr32` those
of AES-CTR (`Proof.AesCtr.RISCV64.ctr_call`); `uargs` and `cargs` build their
arguments from the environment: the key schedule, a block of `W` as the
state or the counter block, the data or blocks of `W` as the data, and the
working space at `W + 384`.
-/

@[expose] public section

namespace VG.Proof.AesCcm.RISCV64

open VG VG.RISCV64
open VG.Proof.CmacAes.Stream.RISCV64 (UArgs)
open VG.Proof.AesCtr.RISCV64 (CtrCall)

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

/-- The arguments of `vg_cmac_aes_update`: the key schedule, the state at
`W + y`, `k` blocks at `Q`, and the working space at `W + 384`. -/
theorem uargs {c : Cx} (L : Lay c) {s : State} (E : Env c s) {y : Nat} (hy : y + 16 ≤ 384) {Q : Addr}
    {k : Nat} (hq : Src c s Q (16 * k)) (hqy : (⟨Q, 16 * k⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 y, 16⟩)
    (hk : 16 * k < 2 ^ 64) (a0 : s.gpr .a0 = c.K) (a1 : s.gpr .a1 = BitVec.ofNat 64 c.R)
    (a2 : s.gpr .a2 = c.W + BitVec.ofNat 64 y) (a3 : s.gpr .a3 = Q) (a4 : s.gpr .a4 = BitVec.ofNat 64 k)
    (a5 : s.gpr .a5 = c.W + BitVec.ofNat 64 384) :
    UArgs s c.K (c.W + BitVec.ofNat 64 y) Q (c.W + BitVec.ofNat 64 384) c.R k where
  a0 := a0
  a1 := a1
  a2 := a2
  a3 := a3
  a4 := a4
  a5 := a5
  rounds := L.rounds
  hn := hk
  wc := L.k_w' (by omega)
  ws := L.k_w' (by decide)
  dc := hqy
  ds := hq.qs
  cs := L.w_w (.inl (by omega)) (by omega) (by decide)
  wrapC := by rw [L.wrapW (by omega)]; have := L.ww; omega
  wrapD := hq.wrap
  wrapS := by rw [L.wrapW (by decide)]; have := L.ww; omega
  reads := Covers.append_left (Covers.cons E.perm.k (Covers.cons hq.rd Covers.nil))
    (Covers.cons (E.perm.wCR (by omega)) (Covers.cons (E.perm.wCR (by decide)) Covers.nil))
  writes := Covers.cons (E.perm.wC (by omega)) (Covers.cons (E.perm.wC (by decide)) Covers.nil)

/-- The arguments of `vg_aes_ctr32`: the key schedule, the counter block at
`W + o`, `k` blocks at `Q`, which it may write, and the working space at
`W + 384`. -/
theorem cargs {c : Cx} (L : Lay c) {s : State} (E : Env c s) {o : Nat} (ho : o + 16 ≤ 384) {Q : Addr}
    {k : Nat} (hq : Src c s Q (16 * k)) (hqo : (⟨Q, 16 * k⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 o, 16⟩)
    (hqk : (⟨c.K, 240⟩ : Region).Disjoint ⟨Q, 16 * k⟩) (hqw : Covers [⟨Q, 16 * k⟩] s.wr)
    (a0 : s.gpr .a0 = c.K) (a1 : s.gpr .a1 = BitVec.ofNat 64 c.R) (a2 : s.gpr .a2 = c.W + BitVec.ofNat 64 o)
    (a3 : s.gpr .a3 = Q) (a4 : s.gpr .a4 = BitVec.ofNat 64 k) (a5 : s.gpr .a5 = c.W + BitVec.ofNat 64 384) :
    CtrCall s c.K (c.W + BitVec.ofNat 64 o) Q (c.W + BitVec.ofNat 64 384) c.R k where
  a0 := a0
  a1 := a1
  a2 := a2
  a3 := a3
  a4 := a4
  a5 := a5
  rounds := L.rounds
  wrap := hq.wrap
  kc := L.k_w' (by omega)
  kd := hqk
  ks := L.k_w' (by decide)
  cd := hqo.symm
  cs := L.w_w (.inl (by omega)) (by omega) (by decide)
  ds := hq.qs.sub_right (Region.sub_prefix (by decide))
  reads := Covers.append_left (Covers.cons E.perm.k Covers.nil)
    (Covers.cons (E.perm.wCR (by omega)) (Covers.cons hq.rd (Covers.cons (E.perm.wCR (by decide)) Covers.nil)))
  writes := Covers.cons (E.perm.wC (by omega)) (Covers.cons hqw (Covers.cons (E.perm.wC (by decide)) Covers.nil))

/-- A block of `W` below 384 as the data of a call of `vg_aes_ctr32`. -/
theorem cargsW {c : Cx} (L : Lay c) {s : State} (E : Env c s) {o : Nat} (ho : o + 16 ≤ 384) {d : Nat}
    (hd : d + 16 ≤ 384) (hod : o + 16 ≤ d ∨ d + 16 ≤ o)
    (a0 : s.gpr .a0 = c.K) (a1 : s.gpr .a1 = BitVec.ofNat 64 c.R) (a2 : s.gpr .a2 = c.W + BitVec.ofNat 64 o)
    (a3 : s.gpr .a3 = c.W + BitVec.ofNat 64 d) (a4 : s.gpr .a4 = BitVec.ofNat 64 1)
    (a5 : s.gpr .a5 = c.W + BitVec.ofNat 64 384) :
    CtrCall s c.K (c.W + BitVec.ofNat 64 o) (c.W + BitVec.ofNat 64 d) (c.W + BitVec.ofNat 64 384) c.R 1 :=
  cargs L E ho (L.srcW E.perm (k := 16 * 1) hd) (L.w_w (by omega) (by omega) (by omega)) (L.k_w' (by omega))
    (E.perm.wC (by omega)) a0 a1 a2 a3 a4 a5

end VG.Proof.AesCcm.RISCV64

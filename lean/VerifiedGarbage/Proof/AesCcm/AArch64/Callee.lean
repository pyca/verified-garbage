import VerifiedGarbage.Proof.AesCcm.AArch64.Env
import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
import VerifiedGarbage.Proof.CmacAes.Stream.AArch64.Common

/-!
# AES-CCM on AArch64: the functions called

Untrusted: everything here is checked by Lean. The calls of
`vg_cmac_aes_update` are those of streaming AES-CMAC
(`Proof.CmacAes.Stream.AArch64.upd_call`), and those of `vg_aes_ctr32` those
of AES-GCM (`Proof.AesGcm.AArch64.ctr_call`); `uargs` and `cargs` build their
arguments from the environment: the key schedule, a block of `W` as the
state or the counter block, the data or blocks of `W` as the data, and the
working space at `W + 384`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.AArch64

open VG VG.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Proof.CmacAes.Stream.AArch64 (UArgs)
open VG.Proof.AesGcm.AArch64 (CtrCall covers_cons covers_nil covers_append covers_left)

/-- The arguments of `vg_cmac_aes_update`: the key schedule, the state at
`W + y`, `k` blocks at `Q`, and the working space at `W + 384`. -/
theorem uargs {c : Cx} (L : Lay c) {s : State} (E : Env c s) {y : Nat} (hy : y + 16 ≤ 384) {Q : Addr}
    {k : Nat} (hq : Src c s Q (16 * k)) (hqy : (⟨Q, 16 * k⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 y, 16⟩)
    (hk : 16 * k < 2 ^ 64) (x0 : s.gpr .x0 = c.K) (x1 : s.gpr .x1 = BitVec.ofNat 64 c.R)
    (x2 : s.gpr .x2 = c.W + BitVec.ofNat 64 y) (x3 : s.gpr .x3 = Q) (x4 : s.gpr .x4 = BitVec.ofNat 64 k)
    (x5 : s.gpr .x5 = c.W + BitVec.ofNat 64 384) :
    UArgs s c.K (c.W + BitVec.ofNat 64 y) Q (c.W + BitVec.ofNat 64 384) c.R k where
  x0 := x0
  x1 := x1
  x2 := x2
  x3 := x3
  x4 := x4
  x5 := x5
  rounds := L.rounds
  hn := hk
  wc := L.k_w' (by omega_arith)
  ws := L.k_w' (by decide)
  dc := hqy
  ds := hq.qs
  cs := L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  wrapC := by rw [L.wrapW (by omega_arith)]; have := L.ww; omega_arith
  wrapD := hq.wrap
  wrapS := by rw [L.wrapW (by decide)]; have := L.ww; omega_arith
  reads := covers_append (covers_cons E.perm.k (covers_cons hq.rd covers_nil))
    (covers_cons (E.perm.wCR (by omega_arith)) (covers_cons (E.perm.wCR (by decide)) covers_nil))
  writes := covers_cons (E.perm.wC (by omega_arith)) (covers_cons (E.perm.wC (by decide)) covers_nil)

/-- The arguments of `vg_aes_ctr32`: the key schedule, the counter block at
`W + o`, `k` blocks at `Q`, which it may write, and the working space at
`W + 384`. -/
theorem cargs {c : Cx} (L : Lay c) {s : State} (E : Env c s) {o : Nat} (ho : o + 16 ≤ 384) {Q : Addr}
    {k : Nat} (hq : Src c s Q (16 * k)) (hqo : (⟨Q, 16 * k⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 o, 16⟩)
    (hqk : (⟨c.K, 240⟩ : Region).Disjoint ⟨Q, 16 * k⟩) (hqw : Covers [⟨Q, 16 * k⟩] s.wr) (hk : k < 2 ^ 64)
    (x0 : s.gpr .x0 = c.K) (x1 : s.gpr .x1 = BitVec.ofNat 64 c.R) (x2 : s.gpr .x2 = c.W + BitVec.ofNat 64 o)
    (x3 : s.gpr .x3 = Q) (x4 : s.gpr .x4 = BitVec.ofNat 64 k) (x5 : s.gpr .x5 = c.W + BitVec.ofNat 64 384) :
    CtrCall s c.K (c.W + BitVec.ofNat 64 o) Q (c.W + BitVec.ofNat 64 384) c.R k where
  x0 := x0
  x1 := x1
  x2 := x2
  x3 := x3
  x4 := x4
  x5 := x5
  rounds := L.rounds
  wrap := hq.wrap
  n_lt := hk
  kc := L.k_w' (by omega_arith)
  kd := hqk
  ks := L.k_w' (by decide)
  cd := hqo.symm
  cs := L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  ds := hq.qs.sub_right (Region.sub_prefix (by decide))
  reads := covers_append (covers_cons E.perm.k covers_nil)
    (covers_cons (E.perm.wCR (by omega_arith)) (covers_cons hq.rd (covers_cons (E.perm.wCR (by decide)) covers_nil)))
  writes := covers_cons (E.perm.wC (by omega_arith)) (covers_cons hqw (covers_cons (E.perm.wC (by decide)) covers_nil))

/-- A block of `W` below 384 as the data of a call of `vg_aes_ctr32`. -/
theorem cargsW {c : Cx} (L : Lay c) {s : State} (E : Env c s) {o : Nat} (ho : o + 16 ≤ 384) {d : Nat}
    (hd : d + 16 ≤ 384) (hod : o + 16 ≤ d ∨ d + 16 ≤ o)
    (x0 : s.gpr .x0 = c.K) (x1 : s.gpr .x1 = BitVec.ofNat 64 c.R) (x2 : s.gpr .x2 = c.W + BitVec.ofNat 64 o)
    (x3 : s.gpr .x3 = c.W + BitVec.ofNat 64 d) (x4 : s.gpr .x4 = BitVec.ofNat 64 1)
    (x5 : s.gpr .x5 = c.W + BitVec.ofNat 64 384) :
    CtrCall s c.K (c.W + BitVec.ofNat 64 o) (c.W + BitVec.ofNat 64 d) (c.W + BitVec.ofNat 64 384) c.R 1 :=
  cargs L E ho (L.srcW E.perm (k := 16 * 1) hd) (L.w_w (by omega_arith) (by omega_arith) (by omega_arith)) (L.k_w' (by omega_arith))
    (E.perm.wC (by omega_arith)) (by decide) x0 x1 x2 x3 x4 x5

end VG.Proof.AesCcm.AArch64

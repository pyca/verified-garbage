import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Args

/-!
# AES-GCM-SIV on x86-64: the arguments of the functions called

Untrusted: everything here is checked by Lean. The calls are those of
AES-GCM (`Proof.AesGcm.X86_64.ctr_call`, `gh_call`, `key_call`); `cargs`,
`gargs` and `kargs` build their arguments from the environment: the key
schedule of the key-generating key (`keyK`) or of the encryption key at
`W + 248` (`keyS`), blocks of `W` as counter blocks, states and data, the
data itself, and the working spaces at `W + 1512` and `W + 1768`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86_64 (CtrCall GhCall KeyCall covers_left covers_cons covers_nil covers_append)

theorem toNat_W {W : Addr} (hw : W.toNat + 3816 ≤ 2 ^ 64) {d : Nat} (hd : d < 3816) :
    (W + BitVec.ofNat 64 d).toNat = W.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- Data for a call: `k` bytes at `Q`, which the code may read, apart from
the working spaces at `W + 1512` and the stack below `SP`. -/
structure Src (W SP : Addr) (s : State) (Q : Addr) (k : Nat) : Prop where
  rd : Covers [⟨Q, k⟩] (s.rd ++ s.wr)
  wrap : Q.toNat + k ≤ 2 ^ 64
  qs : (⟨Q, k⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 1512, 2304⟩
  stk : (below SP 8).Disjoint ⟨Q, k⟩

/-- Bytes of `W` below 1512 as data. -/
theorem srcW {K W SP : Addr} {s : State} (L : Lay K W SP) (P : Perm K W s) {t k : Nat} (hk : t + k ≤ 1512) :
    Src W SP s (W + BitVec.ofNat 64 t) k where
  rd := P.wCR (by omega)
  wrap := by rw [toNat_W L.ww (by omega)]; have := L.ww; omega
  qs := L.w_w (.inl (by omega)) (by omega) (by decide)
  stk := L.stk_w' (by omega)

/-- A buffer as data. -/
theorem srcBuf {K W SP : Addr} {s : State} {Q : Addr} {k : Nat} (h : Buf K W SP s Q k) : Src W SP s Q k :=
  ⟨h.rd, h.wrap, h.w.sub_right (Lay.wSub (by decide)), h.stk⟩

/-- A key schedule for `vg_aes_ctr32`, apart from the blocks of `W` below
248 and the working space at `W + 1768`. -/
structure Key (W SP : Addr) (s : State) (Kc : Addr) : Prop where
  rd : Covers [⟨Kc, 240⟩] (s.rd ++ s.wr)
  stk : (below SP 8).Disjoint ⟨Kc, 240⟩
  lo : (⟨Kc, 240⟩ : Region).Disjoint ⟨W, 248⟩
  hi : (⟨Kc, 240⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 1768, 2048⟩

/-- The key-generating key's schedule. -/
theorem keyK {K W SP : Addr} {s : State} (L : Lay K W SP) (P : Perm K W s) : Key W SP s K :=
  ⟨P.k, L.stk_k, L.k_w.sub_right (Region.sub_prefix (by decide)), L.k_w' (by decide)⟩

/-- The encryption key's schedule, at `W + 248`. -/
theorem keyS {K W SP : Addr} {s : State} (L : Lay K W SP) (P : Perm K W s) : Key W SP s (W + BitVec.ofNat 64 248) :=
  ⟨P.wCR (by decide), L.stk_w' (by decide),
    by simpa using L.w_w (a := 248) (n := 240) (d := 0) (k := 248) (.inr (by decide)) (by decide) (by decide),
    L.w_w (.inl (by decide)) (by decide) (by decide)⟩

/-- The arguments of `vg_aes_ctr32`: the key schedule at `Kc`, the counter
block at `W + c`, `n` blocks at `Q`, which it may write, and the working
space at `W + 1768`. -/
theorem cargs {K W SP : Addr} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 14) {Kc : Addr} (hk : Key W SP s Kc) {c : Nat} (hc : c + 16 ≤ 248) {Q : Addr} {n : Nat}
    (hq : Src W SP s Q (16 * n)) (hqc : (⟨Q, 16 * n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 c, 16⟩)
    (hqk : (⟨Kc, 240⟩ : Region).Disjoint ⟨Q, 16 * n⟩) (hqw : Covers [⟨Q, 16 * n⟩] s.wr)
    (rdi : s.gpr .rdi = Kc) (rsi : s.gpr .rsi = BitVec.ofNat 64 R) (rdx : s.gpr .rdx = W + BitVec.ofNat 64 c)
    (rcx : s.gpr .rcx = Q) (r8 : s.gpr .r8 = BitVec.ofNat 64 n) (r9 : s.gpr .r9 = W + BitVec.ofNat 64 1768) :
    CtrCall s Kc (W + BitVec.ofNat 64 c) Q (W + BitVec.ofNat 64 1768) R n where
  rdi := rdi
  rsi := rsi
  rdx := rdx
  rcx := rcx
  r8 := r8
  r9 := r9
  rounds := by omega
  wrap := hq.wrap
  kc := hk.lo.sub_right (Offset.sub_base W hc)
  kd := hqk
  ks := hk.hi
  cd := hqc.symm
  cs := L.w_w (.inl (by omega)) (by omega) (by decide)
  ds := hq.qs.sub_right (Offset.sub W (by decide) (by decide))
  stkK := by rw [E.rsp]; exact hk.stk
  stkC := by rw [E.rsp]; exact L.stk_w' (by omega)
  stkD := by rw [E.rsp]; exact hq.stk
  stkS := by rw [E.rsp]; exact L.stk_w' (by decide)
  reads := covers_append (covers_cons hk.rd covers_nil)
    (covers_cons (E.perm.wCR (by omega)) (covers_cons hq.rd (covers_cons (E.perm.wCR (by decide)) covers_nil)))
  writes := covers_cons (E.perm.wC (by omega)) (covers_cons hqw (covers_cons (E.perm.wC (by decide)) covers_nil))

/-- The arguments of `vg_ghash`: GHASH's key at `W + 64`, its accumulator at
`W + 80`, `n` blocks at `W + d` and the working space at `W + 1512`. -/
theorem gargs {K W SP : Addr} {s : State} (L : Lay K W SP) (E : Env K W SP s) {d n : Nat} (hd : 96 ≤ d)
    (hdn : d + 16 * n ≤ 1512) (rdi : s.gpr .rdi = W + BitVec.ofNat 64 64) (rsi : s.gpr .rsi = W + BitVec.ofNat 64 80)
    (rdx : s.gpr .rdx = W + BitVec.ofNat 64 d) (rcx : s.gpr .rcx = BitVec.ofNat 64 n)
    (r8 : s.gpr .r8 = W + BitVec.ofNat 64 1512) :
    GhCall s (W + BitVec.ofNat 64 64) (W + BitVec.ofNat 64 80) (W + BitVec.ofNat 64 d) (W + BitVec.ofNat 64 1512) n where
  rdi := rdi
  rsi := rsi
  rdx := rdx
  rcx := rcx
  r8 := r8
  n_lt := by omega
  hy := L.w_w (.inl (by decide)) (by decide) (by decide)
  hs := L.w_w (.inl (by decide)) (by decide) (by decide)
  yd := L.w_w (.inl (by omega)) (by decide) (by omega)
  ys := L.w_w (.inl (by decide)) (by decide) (by decide)
  ds := L.w_w (.inl (by omega)) (by omega) (by decide)
  stkH := by rw [E.rsp]; exact L.stk_w' (by decide)
  stkY := by rw [E.rsp]; exact L.stk_w' (by decide)
  stkD := by rw [E.rsp]; exact L.stk_w' (by omega)
  stkS := by rw [E.rsp]; exact L.stk_w' (by decide)
  reads := covers_append (covers_cons (E.perm.wCR (by decide)) (covers_cons (E.perm.wCR (by omega)) covers_nil))
    (covers_cons (E.perm.wCR (by decide)) (covers_cons (E.perm.wCR (by decide)) covers_nil))
  writes := covers_cons (E.perm.wC (by decide)) (covers_cons (E.perm.wC (by decide)) covers_nil)

/-- The arguments of `vg_aes_expand_key`: the `l`-byte encryption key at
`W + 32`, its schedule at `W + 248` and the working space at `W + 1768`. -/
theorem kargs {K W SP : Addr} {s : State} (L : Lay K W SP) (E : Env K W SP s) {l : Nat} (hl : l = 16 ∨ l = 32)
    (rdi : s.gpr .rdi = W + BitVec.ofNat 64 32) (rsi : s.gpr .rsi = BitVec.ofNat 64 l)
    (rdx : s.gpr .rdx = W + BitVec.ofNat 64 248) (rcx : s.gpr .rcx = W + BitVec.ofNat 64 1768) :
    KeyCall s (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 248) (W + BitVec.ofNat 64 1768) l where
  rdi := rdi
  rsi := rsi
  rdx := rdx
  rcx := rcx
  len := by omega
  kc := L.w_w (.inl (by omega)) (by omega) (by decide)
  ks := L.w_w (.inl (by omega)) (by omega) (by decide)
  cs := L.w_w (.inl (by decide)) (by decide) (by decide)
  stkK := by rw [E.rsp]; exact L.stk_w' (by omega)
  stkC := by rw [E.rsp]; exact L.stk_w' (by decide)
  stkS := by rw [E.rsp]; exact L.stk_w' (by decide)
  reads := covers_append (covers_cons (E.perm.wCR (by omega)) covers_nil)
    (covers_cons (E.perm.wCR (by decide)) (covers_cons (E.perm.wCR (by decide)) covers_nil))
  writes := covers_cons (E.perm.wC (by decide)) (covers_cons (E.perm.wC (by decide)) covers_nil)

end VG.Proof.AesGcmSiv.X86_64

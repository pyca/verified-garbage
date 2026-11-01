module

public import VerifiedGarbage.Proof.AesSiv.RISCV64.Env
import VerifiedGarbage.Proof.AesSiv.RISCV64.FinRaw
public import VerifiedGarbage.Proof.AesCtr.RISCV64.Call
public import VerifiedGarbage.Impl.AesSiv.RISCV64
public import VerifiedGarbage.Spec.Siv
import VerifiedGarbage.Proof.AesSiv.CtrPart
import VerifiedGarbage.Proof.Siv.Spec
public import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.AesCbc.Spec
public import VerifiedGarbage.Proof.CmacAes.Stream.RISCV64.Common
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Spec.Aes
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# AES-SIV on RISC-V: the calls' arguments, and the CMAC of a string

Untrusted: everything here is checked by Lean. What each call is given
(`uargs`, `fargs`, `cargs`): the key context, a state or counter block in
`W` below 384, the data, and the working space at `W + 384`. `cmacOf`
computes the CMAC of the string with the context's PRF into the state at
`W + st` (`cmacOf_wp`): the code zeroes the state, computes `16 nb`, the
bytes of the whole blocks before the last 1 to 16 (`Spec.Cmac.chainedLen`),
into `s8`, chains the `nb` blocks with `vg_cmac_aes_update` and finalizes
the rest with `vg_cmac_aes_finalize`, from the subkeys in the context
(`Siv.cmacWith_chained`). As on PPC64LE (`Proof/AesSiv/PPC64LE/Mac.lean`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.RISCV64

open VG VG.Impl.AesSiv.RISCV64
open VG.RISCV64 VG.RISCV64.Steps
open VG.Proof.CmacAes.Stream.RISCV64 (UArgs UPost upd_call FArgs)
open VG.Proof.AesCtr.RISCV64 (CtrCall)
open VG.Impl.AesCbc.RISCV64 (mov)
open VG.Spec.Aes (bytesAt)

/-! ## Arithmetic -/

theorem ofNat_lsr4' {n : Nat} (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> 4 = BitVec.ofNat 64 (n / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega_arith)]

theorem ofNat_shl4 {n : Nat} (hn : 16 * n < 2 ^ 64) : BitVec.ofNat 64 n <<< 4 = BitVec.ofNat 64 (16 * n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := n) (by omega_arith),
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  omega_arith

theorem ofNat_sub' {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt (a := b) (by omega_arith), Nat.mod_eq_of_lt (a := a - b) (by omega_arith)]
  rw [show 2 ^ 64 - b + a = (a - b) + 2 ^ 64 by omega_arith, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_arith)]

theorem ofNat_add' {a b : Nat} (h : a + b < 2 ^ 64) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := a) (by omega_arith),
    Nat.mod_eq_of_lt (a := b) (by omega_arith)]

theorem chainedLen_le (n : Nat) : Spec.Cmac.chainedLen 16 n ≤ n := by
  simp only [Spec.Cmac.chainedLen]; omega_arith

theorem chainedLen_rest (n : Nat) : n - Spec.Cmac.chainedLen 16 n ≤ 16 := by
  simp only [Spec.Cmac.chainedLen]; omega_arith

theorem chainedLen_div (n : Nat) : 16 * (Spec.Cmac.chainedLen 16 n / 16) = Spec.Cmac.chainedLen 16 n := by
  simp only [Spec.Cmac.chainedLen]; omega_arith

theorem chainedLen_zero : Spec.Cmac.chainedLen 16 0 = 0 := rfl

theorem chainedLen_pos {n : Nat} (_h : n ≠ 0) : Spec.Cmac.chainedLen 16 n = 16 * ((n - 1) / 16) := by
  simp only [Spec.Cmac.chainedLen]; omega_arith

theorem chainedLen_ne {n : Nat} (h : n ≠ 0) : 0 < n - Spec.Cmac.chainedLen 16 n := by
  simp only [Spec.Cmac.chainedLen]; omega_arith

/-! ## The calls' arguments -/

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
  ⟨P.wCR (by omega_arith), by rw [L.wrapW (by omega_arith)]; have := L.ww; omega_arith, L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)⟩

/-- The arguments of `vg_cmac_aes_update`: `K1`'s schedule, the state at
`W + y`, `k` blocks at `Q`, and the working space at `W + 384`. -/
theorem uargs {c : Cx} (L : Lay c) {s : State} (E : Env c s) {y : Nat} (hy : y + 16 ≤ 384) {Q : Addr}
    {k : Nat} (hq : Src c s Q (16 * k)) (hqy : (⟨Q, 16 * k⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 y, 16⟩)
    (hk : 16 * k < 2 ^ 64) (a0 : s.gpr .a0 = c.C) (a1 : s.gpr .a1 = BitVec.ofNat 64 c.R)
    (a2 : s.gpr .a2 = c.W + BitVec.ofNat 64 y) (a3 : s.gpr .a3 = Q) (a4 : s.gpr .a4 = BitVec.ofNat 64 k)
    (a5 : s.gpr .a5 = c.W + BitVec.ofNat 64 384) :
    UArgs s c.C (c.W + BitVec.ofNat 64 y) Q (c.W + BitVec.ofNat 64 384) c.R k where
  a0 := a0
  a1 := a1
  a2 := a2
  a3 := a3
  a4 := a4
  a5 := a5
  rounds := L.rounds
  hn := hk
  wc := L.c0_w' (by decide) (by omega_arith)
  ws := L.c0_w' (by decide) (by decide)
  dc := hqy
  ds := hq.qs
  cs := L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  wrapC := by rw [L.wrapW (by omega_arith)]; have := L.ww; omega_arith
  wrapD := hq.wrap
  wrapS := by rw [L.wrapW (by decide)]; have := L.ww; omega_arith
  reads := Covers.append_left (Covers.cons (E.perm.c0C (by decide)) (Covers.cons hq.rd Covers.nil))
    (Covers.cons (E.perm.wCR (by omega_arith)) (Covers.cons (E.perm.wCR (by decide)) Covers.nil))
  writes := Covers.cons (E.perm.wC (by omega_arith)) (Covers.cons (E.perm.wC (by decide)) Covers.nil)

/-- The arguments of `vg_cmac_aes_finalize`: the key context, the state at
`W + y`, the `k` last bytes at `Q`, and the working space at `W + 384`. -/
theorem fargs {c : Cx} (L : Lay c) {s : State} (E : Env c s) {y : Nat} (hy : y + 16 ≤ 384) {Q : Addr}
    {k : Nat} (hk : k ≤ 16) (hq : Src c s Q k) (hqy : (⟨Q, k⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 y, 16⟩)
    (a0 : s.gpr .a0 = c.C) (a1 : s.gpr .a1 = BitVec.ofNat 64 c.R)
    (a2 : s.gpr .a2 = c.W + BitVec.ofNat 64 y) (a3 : s.gpr .a3 = Q) (a4 : s.gpr .a4 = BitVec.ofNat 64 k)
    (a5 : s.gpr .a5 = c.W + BitVec.ofNat 64 384) :
    FArgs s c.C (c.W + BitVec.ofNat 64 y) Q (c.W + BitVec.ofNat 64 384) k c.R where
  a0 := a0
  a1 := a1
  a2 := a2
  a3 := a3
  a4 := a4
  a5 := a5
  rounds := L.rounds
  len := hk
  kst := L.c0_w' (by decide) (by omega_arith)
  ks := L.c0_w' (by decide) (by decide)
  pst := hqy
  ps := hq.qs
  sts := L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  wrapK := by have := L.cw; omega_arith
  wrapSt := by rw [L.wrapW (by omega_arith)]; have := L.ww; omega_arith
  wrapP := hq.wrap
  wrapS := by rw [L.wrapW (by decide)]; have := L.ww; omega_arith
  reads := Covers.append_left (Covers.cons (E.perm.c0C (by decide)) (Covers.cons hq.rd Covers.nil))
    (Covers.cons (E.perm.wCR (by omega_arith)) (Covers.cons (E.perm.wCR (by decide)) Covers.nil))
  writes := Covers.cons (E.perm.wC (by omega_arith)) (Covers.cons (E.perm.wC (by decide)) Covers.nil)


/-- The arguments of `vg_aes_ctr32`: `K2`'s schedule (at `C + 272`), the
counter block at `W + o`, `k` blocks at `Q`, which it may write, and the
working space at `W + 384`. -/
theorem cargs {c : Cx} (L : Lay c) {s : State} (E : Env c s) {o : Nat} (ho : o + 16 ≤ 384) {Q : Addr}
    {k : Nat} (hq : Src c s Q (16 * k)) (hqo : (⟨Q, 16 * k⟩ : Region).Disjoint ⟨c.W + BitVec.ofNat 64 o, 16⟩)
    (hqk : (⟨c.C + BitVec.ofNat 64 272, 240⟩ : Region).Disjoint ⟨Q, 16 * k⟩) (hqw : Covers [⟨Q, 16 * k⟩] s.wr)
    (a0 : s.gpr .a0 = c.C + BitVec.ofNat 64 272) (a1 : s.gpr .a1 = BitVec.ofNat 64 c.R)
    (a2 : s.gpr .a2 = c.W + BitVec.ofNat 64 o)
    (a3 : s.gpr .a3 = Q) (a4 : s.gpr .a4 = BitVec.ofNat 64 k) (a5 : s.gpr .a5 = c.W + BitVec.ofNat 64 384) :
    CtrCall s (c.C + BitVec.ofNat 64 272) (c.W + BitVec.ofNat 64 o) Q (c.W + BitVec.ofNat 64 384) c.R k where
  a0 := a0
  a1 := a1
  a2 := a2
  a3 := a3
  a4 := a4
  a5 := a5
  rounds := L.rounds
  wrap := hq.wrap
  kc := L.c_w' (by decide) (by omega_arith)
  kd := hqk
  ks := L.c_w' (by decide) (by decide)
  cd := hqo.symm
  cs := L.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  ds := hq.qs.sub_right (Region.sub_prefix (by decide))
  reads := Covers.append_left (Covers.cons (E.perm.cC (by decide)) Covers.nil)
    (Covers.cons (E.perm.wCR (by omega_arith)) (Covers.cons hq.rd (Covers.cons (E.perm.wCR (by decide)) Covers.nil)))
  writes := Covers.cons (E.perm.wC (by omega_arith)) (Covers.cons hqw (Covers.cons (E.perm.wC (by decide)) Covers.nil))

/-- A block of `W` below 384 as the data of a call of `vg_aes_ctr32`. -/
theorem cargsW {c : Cx} (L : Lay c) {s : State} (E : Env c s) {o : Nat} (ho : o + 16 ≤ 384) {d : Nat}
    (hd : d + 16 ≤ 384) (hod : o + 16 ≤ d ∨ d + 16 ≤ o)
    (a0 : s.gpr .a0 = c.C + BitVec.ofNat 64 272) (a1 : s.gpr .a1 = BitVec.ofNat 64 c.R)
    (a2 : s.gpr .a2 = c.W + BitVec.ofNat 64 o)
    (a3 : s.gpr .a3 = c.W + BitVec.ofNat 64 d) (a4 : s.gpr .a4 = BitVec.ofNat 64 1)
    (a5 : s.gpr .a5 = c.W + BitVec.ofNat 64 384) :
    CtrCall s (c.C + BitVec.ofNat 64 272) (c.W + BitVec.ofNat 64 o) (c.W + BitVec.ofNat 64 d)
      (c.W + BitVec.ofNat 64 384) c.R 1 :=
  cargs L E ho (L.srcW E.perm (k := 16 * 1) hd) (L.w_w (by omega_arith) (by omega_arith) (by omega_arith))
    (L.c_w' (by decide) (by omega_arith)) (E.perm.wC (by omega_arith)) a0 a1 a2 a3 a4 a5

/-! ## Zeroing a block of `W` -/

theorem zero16_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {d : Nat} (hd : d + 16 ≤ 2048)
    (hd8 : d % 8 = 0) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', PK s s' → (∀ r, r ≠ .t0 → s'.gpr r = s.gpr r) →
      s'.mem = Proof.Cmac.zero2 s.mem (c.W + BitVec.ofNat 64 d) → WP isa (.block is) s' Q) :
    WP isa (.block (Impl.AesCcm.RISCV64.zero16 d ++ is)) s Q := by
  simp only [Impl.AesCcm.RISCV64.zero16, List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s₁ u₁ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 d) (by omega_arith)
    (by rw [u₁.other _ (by decide), E.s1]) (L.alW hd8 (by omega_arith))
    (by rw [u₁.wr]; exact E.perm.wW (by omega_arith)) fun s₂ u₂ => ?_
  refine wp_sd (a := c.W + BitVec.ofNat 64 d + BitVec.ofNat 64 8) (by omega_arith)
    (by rw [u₂.gpr, u₁.other _ (by decide), E.s1, Offset.add_add])
    (by rw [Offset.add_add]; exact L.alW (by omega_arith) (by omega_arith))
    (by rw [u₂.wr, u₁.wr, Offset.add_add]; exact E.perm.wW (by omega_arith)) fun s₃ u₃ => ?_
  refine k s₃ ((PK.ofUpd u₁).trans ((PK.ofMupd u₂).trans (PK.ofMupd u₃)))
    (fun r hr => by rw [u₃.gpr, u₂.gpr, u₁.other _ hr]) ?_
  rw [u₃.mem, u₂.gpr, u₂.mem, u₁.gpr, u₁.mem, Proof.Cmac.zero2]
  rfl

/-! ## `cmacOf` -/

/-- What the CMAC of a string writes: the state at `W + st` and the working
space of the functions called. -/
abbrev macR (c : Cx) (st : Nat) : List Region := [⟨c.W + BitVec.ofNat 64 st, 16⟩, ⟨c.W + BitVec.ofNat 64 384, 2176⟩]

/-- What `cmacOf` keeps: what every piece does, and the registers holding
the loop's descriptors and the string. -/
structure MacKeep (s s' : State) : Prop where
  pk : PK s s'
  s4 : s'.gpr .s4 = s.gpr .s4
  s5 : s'.gpr .s5 = s.gpr .s5
  s6 : s'.gpr .s6 = s.gpr .s6
  s7 : s'.gpr .s7 = s.gpr .s7

theorem MacKeep.refl (s : State) : MacKeep s s := ⟨PK.refl s, rfl, rfl, rfl, rfl⟩

theorem MacKeep.trans {s t u : State} (h₁ : MacKeep s t) (h₂ : MacKeep t u) : MacKeep s u :=
  ⟨h₁.pk.trans h₂.pk, h₂.s4.trans h₁.s4, h₂.s5.trans h₁.s5, h₂.s6.trans h₁.s6, h₂.s7.trans h₁.s7⟩

theorem keep_sub : ∀ r ∈ keepRegs, r ∈ ([.s1, .s2, .s3, .s4, .s5, .s6, .s7, .s9, .s10, .s11] : List Reg) := by
  decide

theorem MacKeep.ofUpd {s t : State} {d : Reg} {v : BitVec 64} (u : Upd s t d v)
    (hd : d ∉ ([.s1, .s2, .s3, .s4, .s5, .s6, .s7, .s9, .s10, .s11] : List Reg) := by decide) : MacKeep s t :=
  ⟨PK.ofUpd u (fun h => hd (keep_sub d h)), u.other _ (fun h => hd (by simp [h])),
    u.other _ (fun h => hd (by simp [h])), u.other _ (fun h => hd (by simp [h])),
    u.other _ (fun h => hd (by simp [h]))⟩

theorem MacKeep.ofSaved {s t : State} (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hsp : t.sp = s.sp)
    (hs : ∀ r ∈ preserved, t.gpr r = s.gpr r) : MacKeep s t :=
  ⟨PK.ofSaved hrd hwr hsp hs, hs _ (by decide), hs _ (by decide), hs _ (by decide), hs _ (by decide)⟩

/-- `cmacLen`: the state zeroed, and `16 nb` in `s8`. -/
theorem cmacLen_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {st : Nat} (hst : st + 16 ≤ 384) (hst4 : st % 8 = 0)
    {n : Nat} (hn : n < 2 ^ 64) (h20 : s.gpr .s7 = BitVec.ofNat 64 n) :
    WP isa (cmacLen st) s fun s' => MacKeep s s' ∧ s'.gpr .s8 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 n) ∧
      s'.mem = Proof.Cmac.zero2 s.mem (c.W + BitVec.ofNat 64 st) := by
  unfold cmacLen
  refine WP.seq (zero16_wp L E (d := st) (by omega_arith) (by omega_arith) fun s₁ pk₁ g₁ m₁ => ?_)
  refine wp_li (by decide) fun s₂ u₂ => WP.block_nil ?_
  have K₂ : MacKeep s s₂ :=
    ⟨pk₁.trans (PK.ofUpd u₂), by rw [u₂.other _ (by decide), g₁ _ (by decide)],
      by rw [u₂.other _ (by decide), g₁ _ (by decide)], by rw [u₂.other _ (by decide), g₁ _ (by decide)],
      by rw [u₂.other _ (by decide), g₁ _ (by decide)]⟩
  have h20₂ : s₂.gpr .s7 = BitVec.ofNat 64 n := by rw [K₂.s7, h20]
  refine WP.ite (decide (n = 0)) (eval_zero_ofNat _ _ hn h20₂) (fun ht => ?_) (fun hf => ?_)
  · have h0 : n = 0 := by simpa using ht
    subst h0
    exact WP.block_nil ⟨K₂, by rw [u₂.gpr]; rfl, by rw [u₂.mem, m₁]⟩
  · have h0 : n ≠ 0 := by simpa using hf
    refine wp_subi (imm := 1) (by decide) fun s₃ u₃ => wp_srl (by decide) fun s₄ u₄ =>
      wp_sll (by decide) fun s₅ u₅ => WP.block_nil ⟨K₂.trans ((MacKeep.ofUpd u₃).trans ((MacKeep.ofUpd u₄).trans
        (MacKeep.ofUpd u₅))), ?_, by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]⟩
    rw [u₅.gpr, u₄.gpr, u₃.gpr, h20₂, chainedLen_pos h0]
    rw [ofNat_sub' (b := 1) (by omega_arith) hn, ofNat_lsr4' (by omega_arith), ofNat_shl4 (by omega_arith)]

/-- `AES-CMAC(K1, S)` into the state at `W + st`, for the string `S` (`n`
bytes at `P`, in `s6` and `s7`). -/
theorem cmacOf_wp {c : Cx} (L : Lay c) {s : State} (E : Env c s) {st : Nat} (hst : st + 16 ≤ 384)
    (hst8 : st % 8 = 0) {P : Addr} {n : Nat} (hP : Buf c s P n) (h19 : s.gpr .s6 = P)
    (h20 : s.gpr .s7 = BitVec.ofNat 64 n) :
    WP isa (cmacOf st) s fun s' => MacKeep s s' ∧ Frame (macR c st) s.mem s'.mem ∧
      bytesAt s'.mem (c.W + BitVec.ofNat 64 st) 16 = Spec.Siv.ctxMac s.mem c.C c.R (bytesAt s.mem P n) := by
  have hn := hP.lt
  have hcl := chainedLen_le n
  have hcd := chainedLen_div n
  have hrest := chainedLen_rest n
  have hRb := L.rb
  unfold cmacOf
  refine WP.seq (WP.mono (cmacLen_wp L E hst hst8 hn h20) fun s₁ ⟨K₁, h21₁, m₁⟩ => ?_)
  have E₁ := E.of_pk K₁.pk
  have h19₁ : s₁.gpr .s6 = P := by rw [K₁.s6, h19]
  have h20₁ : s₁.gpr .s7 = BitVec.ofNat 64 n := by rw [K₁.s7, h20]
  -- The update's arguments.
  have A₁ : WP isa (.block (cmacArgs₁ st)) s₁ fun s₂ => MacKeep s₁ s₂ ∧ s₂.mem = s₁.mem ∧
      s₂.gpr .s8 = s₁.gpr .s8 ∧
      UArgs s₂ c.C (c.W + BitVec.ofNat 64 st) P (c.W + BitVec.ofNat 64 384) c.R (Spec.Cmac.chainedLen 16 n / 16) := by
    unfold cmacArgs₁ macArgs
    simp only [List.cons_append, List.nil_append]
    refine wp_mv fun t₁ v₁ => wp_mv fun t₂ v₂ => wp_addi (by omega_arith) fun t₃ v₃ =>
      wp_addi (by decide) fun t₄ v₄ => wp_mv fun t₅ v₅ => wp_srl (by decide) fun t₆ v₆ =>
      WP.block_nil ?_
    have K : MacKeep s₁ t₆ := (MacKeep.ofUpd v₁).trans ((MacKeep.ofUpd v₂).trans ((MacKeep.ofUpd v₃).trans
      ((MacKeep.ofUpd v₄).trans ((MacKeep.ofUpd v₅).trans (MacKeep.ofUpd v₆)))))
    have E₆ := E₁.of_pk K.pk
    have hq := (hP.take hcl).of_eq (by rw [K.pk.rd, K₁.pk.rd]) (by rw [K.pk.wr, K₁.pk.wr])
    rw [← hcd] at hq
    refine ⟨K, by rw [v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem],
      by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
        v₂.other _ (by decide), v₁.other _ (by decide)], ?_⟩
    exact uargs L E₆ hst hq.src (hq.wd (d := st) (k := 16) (by omega_arith)) (by omega_arith)
      (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
        v₂.other _ (by decide), v₁.gpr, E₁.s2])
      (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
        v₂.gpr, v₁.other _ (by decide), E₁.s3])
      (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr,
        v₂.other _ (by decide), v₁.other _ (by decide), E₁.s1])
      (by rw [v₆.other _ (by decide), v₅.gpr, v₄.other _ (by decide), v₃.other _ (by decide),
        v₂.other _ (by decide), v₁.other _ (by decide), h19₁])
      (by rw [v₆.gpr, v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
        v₂.other _ (by decide), v₁.other _ (by decide), h21₁, ofNat_lsr4' (by omega_arith)])
      (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.gpr, v₃.other _ (by decide),
        v₂.other _ (by decide), v₁.other _ (by decide), E₁.s1]; rfl)
  refine WP.seq (WP.mono A₁ fun s₂ ⟨K₂, m₂, h21₂, U⟩ => ?_)
  refine WP.seq (WP.mono (upd_call U) fun s₃ h₃ => ?_)
  have K₃ : MacKeep s₂ s₃ := MacKeep.ofSaved h₃.rd h₃.wr h₃.sp h₃.saved
  have K₁₃ := K₂.trans K₃
  have E₃ := E₁.of_pk K₁₃.pk
  have h21₃ : s₃.gpr .s8 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 n) := by
    rw [h₃.saved _ (by decide), h21₂, h21₁]
  -- The finalization's arguments.
  have hq : Buf c s₃ (P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 n)) (n - Spec.Cmac.chainedLen 16 n) :=
    (hP.drop hcl).of_eq (by rw [K₁₃.pk.rd, K₁.pk.rd]) (by rw [K₁₃.pk.wr, K₁.pk.wr])
  have A₂ : WP isa (.block (cmacArgs₂ st)) s₃ fun s₄ => MacKeep s₃ s₄ ∧ s₄.mem = s₃.mem ∧
      FArgs s₄ c.C (c.W + BitVec.ofNat 64 st) (P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 n))
        (c.W + BitVec.ofNat 64 384) (n - Spec.Cmac.chainedLen 16 n) c.R := by
    unfold cmacArgs₂ macArgs
    simp only [List.cons_append, List.nil_append]
    refine wp_mv fun t₁ v₁ => wp_mv fun t₂ v₂ => wp_addi (by omega_arith) fun t₃ v₃ =>
      wp_addi (by decide) fun t₄ v₄ => wp_add fun t₅ v₅ => wp_sub fun t₆ v₆ =>
      WP.block_nil ?_
    have K : MacKeep s₃ t₆ := (MacKeep.ofUpd v₁).trans ((MacKeep.ofUpd v₂).trans ((MacKeep.ofUpd v₃).trans
      ((MacKeep.ofUpd v₄).trans ((MacKeep.ofUpd v₅).trans (MacKeep.ofUpd v₆)))))
    have E₆ := E₃.of_pk K.pk
    have hq' := hq.of_eq K.pk.rd K.pk.wr
    refine ⟨K, by rw [v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem], ?_⟩
    exact fargs L E₆ hst hrest hq'.src (hq'.wd (by omega_arith))
      (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
        v₂.other _ (by decide), v₁.gpr, E₃.s2])
      (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide),
        v₂.gpr, v₁.other _ (by decide), E₃.s3])
      (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr,
        v₂.other _ (by decide), v₁.other _ (by decide), E₃.s1])
      (by simp (disch := decide) only [v₆.other, v₅.gpr, v₄.other, v₃.other, v₂.other, v₁.other, K₁₃.s6, h19₁,
        h21₃])
      (by
        simp (disch := decide) only [v₆.gpr, v₅.other, v₄.other, v₃.other, v₂.other, v₁.other, K₁₃.s7, h20₁, h21₃]
        exact ofNat_sub' hcl hn)
      (by rw [v₆.other _ (by decide), v₅.other _ (by decide), v₄.gpr, v₃.other _ (by decide),
        v₂.other _ (by decide), v₁.other _ (by decide), E₃.s1]; rfl)
  refine WP.seq (WP.mono A₂ fun s₄ ⟨K₄, m₄, F⟩ => ?_)
  refine WP.mono (fin_call_raw F) fun s₅ h₅ => ?_
  have K₅ : MacKeep s₄ s₅ := MacKeep.ofSaved h₅.rd h₅.wr h₅.sp h₅.saved
  refine ⟨K₁.trans (K₁₃.trans (K₄.trans K₅)), ?_, ?_⟩
  -- The memory: what each step writes.
  have f₁ : Frame (macR c st) s.mem s₁.mem := by
    rw [m₁]; exact (Proof.Cmac.frame_store2 _ _ _).mono (by simp)
  have f₃ : Frame (macR c st) s₂.mem s₃.mem := h₃.frame
  have f₅ : Frame (macR c st) s₄.mem s₅.mem := h₅.frame
  have f₁₃ : Frame (macR c st) s.mem s₃.mem := f₁.trans (by rw [← m₂]; exact f₃)
  · exact f₁₃.trans (by rw [← m₄]; exact f₅)
  -- What the calls read is as on entry.
  have f₁ : Frame (macR c st) s.mem s₁.mem := by
    rw [m₁]; exact (Proof.Cmac.frame_store2 _ _ _).mono (by simp)
  have f₁₃ : Frame (macR c st) s.mem s₃.mem := f₁.trans (by rw [← m₂]; exact h₃.frame)
  have dc : ∀ r ∈ macR c st, (⟨c.C, 512⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact L.c0_w' (by decide) (by omega_arith)
    · exact L.c0_w' (by decide) (by decide)
  have dp : ∀ r ∈ macR c st, (⟨P, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hP.wd (by omega_arith)
    · exact hP.wd (by decide)
  have cK {d k : Nat} (hd : d + k ≤ 512) {m' : Mem} (hf : Frame (macR c st) s.mem m') :
      bytesAt m' (c.C + BitVec.ofNat 64 d) k = bytesAt s.mem (c.C + BitVec.ofNat 64 d) k :=
    Proof.Cmac.bytesAt_frame hf (fun r hr => (dc r hr).sub_left (Lay.cSub hd)) (by omega_arith)
  have cP {d k : Nat} (hd : d + k ≤ n) {m' : Mem} (hf : Frame (macR c st) s.mem m') :
      bytesAt m' (P + BitVec.ofNat 64 d) k = bytesAt s.mem (P + BitVec.ofNat 64 d) k :=
    Proof.Cmac.bytesAt_frame hf (fun r hr => (dp r hr).sub_left (Offset.sub_base _ hd)) (by omega_arith)
  have k0 : ∀ a : Addr, a + BitVec.ofNat 64 0 = a := fun a => BitVec.add_zero a
  have sch₁ := cK (d := 0) (k := 16 * (c.R + 1)) (by omega_arith) f₁
  have sch₃ := cK (d := 0) (k := 16 * (c.R + 1)) (by omega_arith) f₁₃
  have k1 := cK (d := 240) (k := 16) (by decide) f₁₃
  have k2 := cK (d := 256) (k := 16) (by decide) f₁₃
  have pre₁ := cP (d := 0) (k := Spec.Cmac.chainedLen 16 n) (by omega_arith) f₁
  have rest₃ := cP (d := Spec.Cmac.chainedLen 16 n) (k := n - Spec.Cmac.chainedLen 16 n) (by omega_arith) f₁₃
  rw [k0] at sch₁ sch₃ pre₁
  have hz : bytesAt s₁.mem (c.W + BitVec.ofNat 64 st) 16 = Spec.Cmac.zeros 16 := by
    rw [m₁, Proof.Cmac.zero2_bytes]
  have hS : (bytesAt s.mem P n).length = n := Proof.Cmac.bytesAt_length _ _ _
  have hsplit : n = Spec.Cmac.chainedLen 16 n + (n - Spec.Cmac.chainedLen 16 n) := by omega_arith
  have tk : (bytesAt s.mem P n).take (Spec.Cmac.chainedLen 16 n) =
      bytesAt s.mem P (Spec.Cmac.chainedLen 16 n) := by
    have := take_bytesAt s.mem P (a := Spec.Cmac.chainedLen 16 n) (b := n - Spec.Cmac.chainedLen 16 n)
    rwa [← hsplit] at this
  have dr : (bytesAt s.mem P n).drop (Spec.Cmac.chainedLen 16 n) =
      bytesAt s.mem (P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 n)) (n - Spec.Cmac.chainedLen 16 n) := by
    have := drop_bytesAt s.mem P (a := Spec.Cmac.chainedLen 16 n) (b := n - Spec.Cmac.chainedLen 16 n)
    rwa [← hsplit] at this
  have out₃ := h₃.out
  have out₅ := h₅.out
  rw [m₄] at out₅
  rw [m₂] at out₃
  rw [out₅, out₃, Proof.CmacAes.RISCV64.mn, Proof.CmacAes.RISCV64.ciphAt, sch₃, k1, k2, rest₃, sch₁, hz, Proof.Cmac.Stream.blocksAt_eq, hcd,
    pre₁, Spec.Siv.ctxMac, Spec.Siv.schedCiph, Siv.cmacWith_chained, hS, tk, dr]
  rfl

end VG.Proof.AesSiv.RISCV64

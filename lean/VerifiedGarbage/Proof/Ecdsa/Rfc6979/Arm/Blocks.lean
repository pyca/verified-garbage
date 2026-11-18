module

import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Weierstrass.Words32
import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.AesGcm.Arm.Loops
import VerifiedGarbage.Proof.AesGcm.Arm.Run
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Words32
import VerifiedGarbage.Proof.Pbkdf2.Whole.Common
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
import VerifiedGarbage.Proof.Hmac.Common
public import VerifiedGarbage.Impl.Ecdsa.Rfc6979.Arm
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Sha256
public import VerifiedGarbage.Proof.Framework.Mem
import Batteries.Logic
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Loop
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Curve
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Arm.Layout

/-! ### `Ecdsa.Rfc6979.Arm.Regs`, which this module and modules that import it used -/

section

/-!
# Deterministic ECDSA on 32-bit ARM: addresses and registers

The code that sets one register to an address in `scratch` or the frame
(`scrAt_ok`, `fpAdd_ok`), and the addresses those registers hold.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Impl.Pbkdf2.Stream.Arm (scrAt)
open VG.Proof.HmacTable.Arm (tA)
open VG.Proof.X25519.Arm (Upd Mupd wp_movw wp_mov wp_dp op2_reg op2_imm dpVal)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `add d, sp, #imm`. -/
theorem wp_addSp {d : Reg} {imm : Nat} (h : imm < 256)
    (k : ∀ s', Upd s s' d (s.sp + BitVec.ofNat 32 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addSp d imm :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons (s' := s.setReg d (s.sp + BitVec.ofNat 32 imm))
    (by simp only [exec, h, ↓reduceIte]) (k _ (Upd.setReg _ _ _))

end

/-- An immediate below 256 is encodable (rotation 0). -/
theorem encodable_lt {n : Nat} (h : n < 256) : encodable (BitVec.ofNat 32 n) = true :=
  List.any_eq_true.2 ⟨0, by simp, by
    have h0 : (BitVec.ofNat 32 n).rotateLeft (2 * 0) = BitVec.ofNat 32 n := by ext i; simp
    simpa only [h0, decide_eq_true_eq, BitVec.toNat_ofNat] using (by omega_using [h] : n % 2 ^ 32 < 256)⟩

theorem bytesAt_frame {ws : List Region} {m m' : Mem} (hf : Frame ws m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) :
    Spec.Sha256.bytesAt m' p n = Spec.Sha256.bytesAt m p n := by
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => Frame.bytes (R := ⟨p, n⟩) hf hd hn (List.mem_range.mp hi)

theorem sub_refl (r : Region) : Region.Sub r r := fun _ h => h

theorem sub_trans {a b c : Region} (h₁ : Region.Sub a b) (h₂ : Region.Sub b c) : Region.Sub a c :=
  fun x hx => h₂ x (h₁ x hx)

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-- `scratch + o` as an address. -/
theorem scrA (hL : L.Ok) {o : Nat} (ho : o < 8192) :
    State.addr (L.scr + BitVec.ofNat 32 o) = State.addr L.scr + BitVec.ofNat 64 o :=
  addr_add (by have := hL.nc; omega_using [ho, this])

theorem movw_val {o : Nat} (ho : o < 2 ^ 16) : (BitVec.ofNat 16 o).setWidth 32 = BitVec.ofNat 32 o := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_using [ho]

/-- `d ← scratch + o`, through `r12`. -/
theorem scrAt_ok {t : State} (hc : Ctx L g m₀ t) {d : Reg} (hd : d ∉ ptrRegs) {o : Nat} (ho : o < 2 ^ 16)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t', Ctx L g m₀ t' → t'.mem = t.mem → t'.gpr d = L.scr + BitVec.ofNat 32 o →
      (∀ r, r ≠ d → r ≠ .r12 → t'.gpr r = t.gpr r) → WP isa (.block is) t' Q) :
    WP isa (.block (scrAt d o ++ is)) t Q := by
  simp only [scrAt, List.cons_append, List.nil_append]
  refine wp_movwS fun t₁ u₁ => ?_
  refine wp_dpS (op2_reg _ _) fun t₂ u₂ => ?_
  have c₁ := hc.upd u₁ (by decide)
  refine k t₂ (c₁.upd u₂ hd) (by rw [u₂.mem, u₁.mem]) ?_ fun r h1 h2 => by rw [u₂.other _ h1, u₁.other _ h2]
  rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), hc.r11, movw_val ho]
  rfl

/-- `d ← r8 + o`, an address in the frame. -/
theorem fpAdd_ok {t : State} (hc : Ctx L g m₀ t) {d : Reg} (hd : d ∉ ptrRegs) {o : Nat}
    (ho : encodable (BitVec.ofNat 32 o) = true) {is : List Instr} {Q : State → Prop}
    (k : ∀ t', Ctx L g m₀ t' → t'.mem = t.mem → t'.gpr d = L.fp + BitVec.ofNat 32 o →
      (∀ r, r ≠ d → t'.gpr r = t.gpr r) → WP isa (.block is) t' Q) :
    WP isa (.block (.dp .add d .r8 (.imm (BitVec.ofNat 32 o)) :: is)) t Q :=
  wp_dpS (op2_imm ho) fun t₁ u₁ => k t₁ (hc.upd u₁ hd) u₁.mem (by rw [u₁.gpr, dpVal, hc.r8]) u₁.other

/-- `d ← v`, a register set to a 16-bit constant. -/
theorem movw_ok {t : State} (hc : Ctx L g m₀ t) {d : Reg} (hd : d ∉ ptrRegs) {v : Nat} (hv : v < 2 ^ 16)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ t', Ctx L g m₀ t' → t'.mem = t.mem → t'.gpr d = BitVec.ofNat 32 v →
      (∀ r, r ≠ d → t'.gpr r = t.gpr r) → WP isa (.block is) t' Q) :
    WP isa (.block (.movw d (BitVec.ofNat 16 v) :: is)) t Q :=
  wp_movwS fun t₁ u₁ => k t₁ (hc.upd u₁ hd) u₁.mem (by rw [u₁.gpr, movw_val hv]) u₁.other

/-- `d ← 0`. -/
theorem mov0_ok {t : State} (hc : Ctx L g m₀ t) {d : Reg} (hd : d ∉ ptrRegs) {is : List Instr}
    {Q : State → Prop}
    (k : ∀ t', Ctx L g m₀ t' → t'.mem = t.mem → t'.gpr d = 0 →
      (∀ r, r ≠ d → t'.gpr r = t.gpr r) → WP isa (.block is) t' Q) :
    WP isa (.block (.mov d (.imm 0) :: is)) t Q :=
  wp_movS (op2_imm (by decide)) fun t₁ u₁ => k t₁ (hc.upd u₁ hd) u₁.mem u₁.gpr u₁.other

/-- `d ← s`, a copy of a register. -/
theorem movr_ok {t : State} (hc : Ctx L g m₀ t) {d r : Reg} (hd : d ∉ ptrRegs) {is : List Instr}
    {Q : State → Prop}
    (k : ∀ t', Ctx L g m₀ t' → t'.mem = t.mem → t'.gpr d = t.gpr r →
      (∀ q, q ≠ d → t'.gpr q = t.gpr q) → WP isa (.block is) t' Q) :
    WP isa (.block (.mov d (.reg r) :: is)) t Q :=
  wp_movS (op2_reg _ _) fun t₁ u₁ => k t₁ (hc.upd u₁ hd) u₁.mem u₁.gpr u₁.other

/-- `d ← [r6 + o]`, a word of the table, as on entry. -/
theorem tabLd_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {d : Reg} (hd : d ∉ ptrRegs) {o : Nat}
    (ho : o + 4 ≤ 24) {is : List Instr} {Q : State → Prop}
    (k : ∀ t', Ctx L g m₀ t' → t'.mem = t.mem → t'.gpr d = m₀.readW (tA L.tab o) 32 →
      (∀ r, r ≠ d → t'.gpr r = t.gpr r) → WP isa (.block is) t' Q) :
    WP isa (.block (.ldr d .r6 o :: is)) t Q :=
  wp_ldrS (a := tA L.tab o) (by omega_using [ho]) (by rw [hc.r6]) (hc.inTab hL ho) fun t₁ u₁ =>
    k t₁ (hc.upd u₁ hd) u₁.mem (by rw [u₁.gpr, hc.tabWord hL ho]) u₁.other

/-- `d ← D`, the table's digest length. -/
theorem ldD_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {d : Reg} (hd : d ∉ ptrRegs) {is : List Instr}
    {Q : State → Prop}
    (k : ∀ t', Ctx L g m₀ t' → t'.mem = t.mem → t'.gpr d = BitVec.ofNat 32 L.F.H.D →
      (∀ r, r ≠ d → t'.gpr r = t.gpr r) → WP isa (.block is) t' Q) :
    WP isa (.block (.ldr d .r6 tD :: is)) t Q :=
  tabLd_ok hL hc hd (by decide) fun t' c' m' v' k' => k t' c' m' (v'.trans hc.tabD) k'

/-- `d ← B`, HMAC's block size. -/
theorem ldB_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {d : Reg} (hd : d ∉ ptrRegs) {is : List Instr}
    {Q : State → Prop}
    (k : ∀ t', Ctx L g m₀ t' → t'.mem = t.mem → t'.gpr d = BitVec.ofNat 32 L.F.H.B →
      (∀ r, r ≠ d → t'.gpr r = t.gpr r) → WP isa (.block is) t' Q) :
    WP isa (.block (.ldr d .r6 tB :: is)) t Q :=
  tabLd_ok hL hc hd (by decide) fun t' c' m' v' k' => k t' c' m' (v'.trans hc.tabB) k'

/-- `d ← [r8 + o]`, a word of the frame. -/
theorem frLd_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {d : Reg} (hd : d ∉ ptrRegs) {o : Nat}
    (ho : o + 4 ≤ 512) {is : List Instr} {Q : State → Prop}
    (k : ∀ t', Ctx L g m₀ t' → t'.mem = t.mem → t'.gpr d = t.mem.readW (L.B + BitVec.ofNat 64 (24 + o)) 32 →
      (∀ r, r ≠ d → t'.gpr r = t.gpr r) → WP isa (.block is) t' Q) :
    WP isa (.block (.ldr d .r8 o :: is)) t Q :=
  wp_ldrS (a := L.B + BitVec.ofNat 64 (24 + o)) (by omega_using [ho]) (by rw [hc.r8]; exact hL.fpA (by omega_using [ho]))
    (hc.inFr (by omega_using []) (by omega_using [ho])) fun t₁ u₁ => k t₁ (hc.upd u₁ hd) u₁.mem u₁.gpr u₁.other

end VG.Proof.Ecdsa.Rfc6979.Arm

end

end

/-! ### `Ecdsa.Rfc6979.Arm.Hash`, which this module and modules that import it used -/

section

/-!
# Deterministic ECDSA on 32-bit ARM: the hash function

What the proof needs of the hash function, for any one of them (`RfcHash`),
as on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Reduce.lean`): the curve
(`RfcCurve`, with what is proven of `vg_ecdsa_<curve>_sign_k`, which each
candidate calls), the instance of the contract it implements (the curve's,
the hash function's HMAC, its output length, the bound on candidates), the
functions PBKDF2's code calls and what its proofs know of them (`FnsOK`:
HMAC's `init` and `finalize` and the streaming `update`, which the table
holds), the functions an indirect call of a table's functions may reach
(`f`), and the sizes the frame and `scratch` hold: the output and block
sizes of one of the hash functions of `shapes` (MD5's, SHA-1's or the SHA-2
family's), and states and working space no larger than SHA-512's.

The code is the same for every hash function (`cfgOf`): the proof is
written for each one, with the table's digest length `D` and block size `B`
the values the table holds.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Proof.Pbkdf2.Whole.Arm (FnsOK)

/-- The digest lengths and block sizes of the hash functions with HMAC on
ARMv7: MD5, SHA-1, SHA-224, SHA-256, SHA-384, SHA-512, SHA-512/224 and
SHA-512/256. -/
def shapes : List (Nat × Nat) := [(16, 64), (20, 64), (28, 64), (32, 64), (48, 128), (64, 128), (28, 128), (32, 128)]

/-- A curve and a hash function, for RFC 6979 on 32-bit ARM. -/
structure RfcHash where
  /-- The curve. -/
  R : RfcCurve
  /-- The instance of the contract, with the hash function fixed. -/
  I : Proof.Ecdsa.Rfc6979.Instance
  /-- The functions PBKDF2's code calls, of the hash function. -/
  F : Impl.Pbkdf2.Whole.Arm.Fns
  ok : FnsOK F
  /-- The functions an indirect call of a table's functions may reach. -/
  f : Fns
  /-- The instance is of the curve, with this hash function's HMAC and its
  output length. -/
  ecdsa : I.ecdsa = R.inst
  hash : I.hash = ok.hH.SH.H
  len : I.hashLen = F.H.D
  /-- The hash function's digests have `F.H.D` bytes. -/
  macLen : ∀ x, (ok.hH.SH.H.hash x).length = F.H.D
  /-- It tries at least one candidate, as many as a 16-bit immediate holds. -/
  tries_pos : 0 < I.tries
  tries_lt : I.tries < 2 ^ 16
  /-- The sizes the frame and `scratch` hold. -/
  hDB : (F.H.D, F.H.B) ∈ shapes
  hS : F.H.S ≤ 192
  hWi : ok.Wi * 8 ≤ 1872
  hWf : ok.Wf * 8 ≤ 1872
  hWb : ok.hH.Wb ≤ 1872

namespace RfcHash

variable (P : RfcHash)

/-- HMAC with the hash function. -/
abbrev mac (K text : List Byte) : List Byte := Spec.Hmac.hmac P.ok.hH.SH.H K text

/-- The 64-bit words of the curve's scalars. -/
abbrev w : Nat := P.R.E.n

/-- Their 32-bit words: seven for P-224, otherwise two per 64-bit word. -/
abbrev k : Nat := 2 * P.R.E.n - (if P.R.E.C.len = 28 then 1 else 0)

/-- The bytes of the curve's scalars. -/
abbrev Q : Nat := P.R.E.C.len

theorem shape (h : (P.F.H.D, P.F.H.B) ∈ shapes) :
    16 ≤ P.F.H.D ∧ P.F.H.D ≤ 64 ∧ P.F.H.D % 4 = 0 ∧ P.F.H.D < P.F.H.B ∧ P.F.H.B ≤ 128 ∧ 64 ≤ P.F.H.B := by
  simp only [shapes, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> omega_using [h, h']

/-- The sizes, as the proofs use them. -/
theorem sizes : P.F.H.S ≤ 192 ∧ P.ok.Wi * 8 ≤ 1872 ∧ P.ok.Wf * 8 ≤ 1872 ∧ P.ok.hH.Wb ≤ 1872 ∧
    16 ≤ P.F.H.D ∧ P.F.H.D ≤ 64 ∧ P.F.H.D % 4 = 0 ∧ P.F.H.D < P.F.H.B ∧ P.F.H.B ≤ 128 ∧ 64 ≤ P.F.H.B ∧
    P.ok.hH.SH.stateBytes = P.F.H.S ∧ P.ok.hH.SH.digestBytes = P.F.H.D ∧
    P.ok.hH.SH.H.blockSize = P.F.H.B := by
  have hs := P.shape P.hDB
  exact ⟨P.hS, P.hWi, P.hWf, P.hWb, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2,
    P.ok.hH.hS, P.ok.hH.hD, P.ok.hH.hB⟩

/-- The sizes of the scalars, as the proofs use them. -/
theorem wsizes : 3 ≤ P.w ∧ P.w ≤ 9 ∧ 6 ≤ P.k ∧ P.k ≤ 2 * P.w ∧ 8 ≤ P.Q ∧ P.Q ≤ 66 ∧ P.Q ≤ 8 * P.w ∧
    8 * P.w < P.Q + 8 := by
  have hw : 8 ≤ P.Q ∧ 8 * P.w < P.Q + 8 ∧ P.Q ≤ 8 * P.w := P.R.len_words
  have hQ : P.Q ≤ 66 := by
    cases hb : P.R.big
    · have := P.R.sizesA hb; simp only [Q]; omega_using [this]
    · have := P.R.sizesW hb; simp only [Q]; omega_using [this]
  exact ⟨P.R.n3, P.R.n9, (by have := P.R.len_words; have := P.R.n3; simp only [k]; split <;> omega_arith),
    (by simp only [k, w]; omega_using []), hw.1, hQ, hw.2.2, hw.2.1⟩

/-- Unless `big`, the scalars fill at most sixteen 32-bit words. -/
theorem sizesA (h : P.R.big = false) : P.Q = 4 * P.k ∧ P.k ≤ 16 ∧ P.Q ≤ 64 := by
  have := P.R.sizesA h
  rcases this.1 with h' | h' | h' | h' <;> simp only [Q, k] <;> split <;> omega_arith

/-- If `big`, P-521's sizes, longer than any digest. -/
theorem sizesW (h : P.R.big = true) : P.w = 9 ∧ P.Q = 66 ∧ P.k = 18 ∧ P.F.H.D < P.Q := by
  have h₁ := P.R.sizesW h
  have h₂ := (P.shape P.hDB).2.1
  refine ⟨h₁.1, h₁.2.1, ?_, by simp only [Q]; omega_using [h₁, h₂]⟩
  simp only [k, h₁.1, h₁.2.1]; decide

theorem mac_length (K t : List Byte) : (P.mac K t).length = P.F.H.D := by
  simp only [mac, Spec.Hmac.hmac, Spec.Hmac.hmacBlockKey, P.macLen]

/-- The curve's scalars are `Q` bytes. -/
theorem curveLen : P.I.ecdsa.curve.len = P.Q := by rw [P.ecdsa, P.R.curve]

end RfcHash

/-- Facts about the sizes of the hash function `‹RfcHash›`'s states, working
space, block and output, and of the scalars, and the arithmetic they decide. -/
tactic_template "anums" : tactic => `(tactic| first | omega |
  (obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _⟩ := RfcHash.sizes ‹RfcHash›
   obtain ⟨_, _, _, _, _, _, _, _⟩ := RfcHash.wsizes ‹RfcHash›; omega))

/-- The code, for the curve of `P` and the functions an indirect call may reach. -/
def cfgOf (P : RfcHash) : Cfg where
  f := P.f
  w := 2 * P.R.E.n - (if P.R.E.C.len = 28 then 1 else 0)
  len := P.R.E.C.len
  big := P.R.big
  sh := P.R.sh
  n := P.R.E.C.n
  tries := P.I.tries
  coreN := P.R.coreN
  coreC := P.R.coreC

theorem cfgOf_len (P : RfcHash) : (cfgOf P).len = P.Q := rfl

end VG.Proof.Ecdsa.Rfc6979.Arm

end

end

/-! ### `Ecdsa.Rfc6979.Arm.Copy`, which this module and modules that import it used -/

section

/-!
# Deterministic ECDSA on 32-bit ARM: copying words

`copyN k src so dst d` copies the `4 k` bytes at `src + so` to `dst + d`, a
word at a time through `r0`, when the two ranges are apart: each word
written is the word read (`copyW_ok`), so the bytes written are the bytes
read (`copyN_ok`, by induction on the words). The model's `ldr` and `str`
take any address, as ARMv7's do, so the ranges need not be aligned.
`copyBytes Q` copies `Q ≥ 4` bytes: the whole words, then the last four bytes
again (`copyBytes_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Proof.X25519.Arm (wp_ldr wp_str)

/-- One word copied through `r0`. -/
theorem copyW_ok {u : State} {src dst : Reg} {S D : BitVec 32} (hs : u.gpr src = S) (hd : u.gpr dst = D)
    {so d : Nat} (hso : so < 4096) (hdo : d < 4096) {SA DA : Addr}
    (hSA : State.addr (S + BitVec.ofNat 32 so) = SA) (hDA : State.addr (D + BitVec.ofNat 32 d) = DA)
    (hr : InRegions (u.rd ++ u.wr) SA 4) (hw : InRegions u.wr DA 4) (hdr : dst ≠ .r0) :
    WP isa (.block [.ldr .r0 src so, .str .r0 dst d]) u fun u' =>
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ (∀ r, r ≠ .r0 → u'.gpr r = u.gpr r) ∧
      u'.mem = u.mem.writeW DA (u.mem.readW SA 32) :=
  wp_ldr (a := SA) hso (by rw [hs]; exact hSA) hr fun s₁ u₁ =>
    wp_strS (a := DA) hdo (by rw [u₁.other _ hdr, hd]; exact hDA) (by rw [u₁.wr]; exact hw) fun s₂ m₂ =>
      WP.block_nil ⟨by rw [m₂.rd, u₁.rd], by rw [m₂.wr, u₁.wr], by rw [m₂.sp, u₁.sp],
        fun r hr => by rw [m₂.gpr, u₁.other _ hr], by rw [m₂.mem, u₁.mem, u₁.gpr]⟩

theorem bytesAt_copied (m : Mem) (D S : Addr) :
    Spec.Sha256.bytesAt (m.writeW D (m.readW S 32)) D 4 = Spec.Sha256.bytesAt m S 4 := by
  rw [show (32 : Nat) = 8 * 4 from rfl, Proof.Hmac.Common.writeW_readW]
  have := Proof.Hmac.Common.bytesAt_writeBytes_self m D (Spec.Sha256.bytesAt m S 4) (by simp [Spec.Sha256.bytesAt])
  rwa [Proof.Hmac.Common.bytesAt_length] at this

theorem copyN_ok {src dst : Reg} {S D : BitVec 32} {so d K : Nat} (hdr : dst ≠ .r0) (hsr : src ≠ .r0)
    (hsep : Region.Disjoint ⟨State.addr S + BitVec.ofNat 64 so, 4 * K⟩ ⟨State.addr D + BitVec.ofNat 64 d, 4 * K⟩)
    (hsn : S.toNat + so + 4 * K ≤ 2 ^ 32) (hdn : D.toNat + d + 4 * K ≤ 2 ^ 32) (hso : so + 4 * K ≤ 4096)
    (hdo : d + 4 * K ≤ 4096) :
    ∀ k ≤ K, ∀ u : State, u.gpr src = S → u.gpr dst = D →
      (∀ j < K, InRegions (u.rd ++ u.wr) (State.addr S + BitVec.ofNat 64 (so + 4 * j)) 4) →
      (∀ j < K, InRegions u.wr (State.addr D + BitVec.ofNat 64 (d + 4 * j)) 4) →
      WP isa (.block (Cfg.copyN k src so dst d)) u fun u' =>
        u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ (∀ r, r ≠ .r0 → u'.gpr r = u.gpr r) ∧
        Frame [⟨State.addr D + BitVec.ofNat 64 d, 4 * K⟩] u.mem u'.mem ∧
        Spec.Sha256.bytesAt u'.mem (State.addr D + BitVec.ofNat 64 d) (4 * k) =
          Spec.Sha256.bytesAt u.mem (State.addr S + BitVec.ofNat 64 so) (4 * k)
  | 0, _, u, _, _, _, _ => WP.block_nil ⟨rfl, rfl, rfl, fun _ _ => rfl, Frame.refl _ _, rfl⟩
  | k + 1, hk, u, hs, hd, hr, hw => by
    rw [Cfg.copyN, List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (copyN_ok hdr hsr hsep hsn hdn hso hdo k (by omega_arith) u hs hd hr hw)
      fun u₁ ⟨hrd₁, hwr₁, hsp₁, hg₁, hf₁, hb₁⟩ => ?_
    refine WP.mono (copyW_ok (u := u₁) (hg₁ _ hsr ▸ hs) (hg₁ _ hdr ▸ hd) (by omega_arith) (by omega_arith)
      (addr_add (by omega_arith)) (addr_add (by omega_arith)) (hrd₁ ▸ hwr₁ ▸ hr k (by omega_arith)) (hwr₁ ▸ hw k (by omega_arith)) hdr)
      fun u₂ ⟨hrd₂, hwr₂, hsp₂, hg₂, hm₂⟩ => ?_
    -- The word written, within the destination.
    have hsub : Region.Sub ⟨State.addr D + BitVec.ofNat 64 (d + 4 * k), 4⟩
        ⟨State.addr D + BitVec.ofNat 64 d, 4 * K⟩ :=
      Offset.sub _ (by omega_arith) (by omega_arith)
    have hf₂ : Frame [⟨State.addr D + BitVec.ofNat 64 (d + 4 * k), 4⟩] u₁.mem u₂.mem := by
      rw [hm₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (Nat.le_refl _) (by omega_arith) (by omega_arith))
    -- The word read, unchanged by the earlier words.
    have hsrc : Spec.Sha256.bytesAt u₁.mem (State.addr S + BitVec.ofNat 64 (so + 4 * k)) 4 =
        Spec.Sha256.bytesAt u.mem (State.addr S + BitVec.ofNat 64 (so + 4 * k)) 4 :=
      bytesAt_frame hf₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hsep.sub_left (Offset.sub _ (by omega_arith) (by omega_arith))) (by omega_arith)
    refine ⟨hrd₂.trans hrd₁, hwr₂.trans hwr₁, hsp₂.trans hsp₁, fun r hr => (hg₂ r hr).trans (hg₁ r hr),
      hf₁.trans (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact hsub⟩), ?_⟩
    rw [show 4 * (k + 1) = 4 * k + 4 by omega_arith, Proof.Hmac.Common.bytesAt_add, Proof.Hmac.Common.bytesAt_add,
      Offset.add_add, Offset.add_add, ← hsrc]
    refine congrArg₂ (· ++ ·) ?_ ?_
    · rw [← hb₁]
      exact bytesAt_frame hf₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by omega_arith)
    · rw [hm₂]
      exact bytesAt_copied _ _ _

/-- The first `n` of `k` bytes. -/
theorem bytesAt_take (m : Mem) (p : Addr) {n k : Nat} (h : n ≤ k) :
    Spec.Sha256.bytesAt m p n = (Spec.Sha256.bytesAt m p k).take n := by
  rw [show k = n + (k - n) by omega_arith, Proof.Hmac.Common.bytesAt_add, List.take_left']
  simp [Spec.Sha256.bytesAt]

theorem copyBytes_ok {src dst : Reg} {S D : BitVec 32} {so d Q : Nat} (hdr : dst ≠ .r0) (hsr : src ≠ .r0)
    (hsep : Region.Disjoint ⟨State.addr S + BitVec.ofNat 64 so, Q⟩ ⟨State.addr D + BitVec.ofNat 64 d, Q⟩)
    (hsn : S.toNat + so + Q ≤ 2 ^ 32) (hdn : D.toNat + d + Q ≤ 2 ^ 32) (hso : so + Q ≤ 4096)
    (hdo : d + Q ≤ 4096) (h4 : 4 ≤ Q) {u : State} (hs : u.gpr src = S) (hd : u.gpr dst = D)
    (hr : ∀ j, j + 4 ≤ Q → InRegions (u.rd ++ u.wr) (State.addr S + BitVec.ofNat 64 (so + j)) 4)
    (hw : ∀ j, j + 4 ≤ Q → InRegions u.wr (State.addr D + BitVec.ofNat 64 (d + j)) 4) :
    WP isa (.block (Cfg.copyBytes Q src so dst d)) u fun u' =>
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ (∀ r, r ≠ .r0 → u'.gpr r = u.gpr r) ∧
      Frame [⟨State.addr D + BitVec.ofNat 64 d, Q⟩] u.mem u'.mem ∧
      Spec.Sha256.bytesAt u'.mem (State.addr D + BitVec.ofNat 64 d) Q =
        Spec.Sha256.bytesAt u.mem (State.addr S + BitVec.ofNat 64 so) Q := by
  rw [Cfg.copyBytes, WP.block_append_iff]
  have hK : 4 * (Q / 4) ≤ Q := Nat.mul_div_le Q 4
  refine WP.mono (copyN_ok (S := S) (D := D) (so := so) (d := d) (K := Q / 4) hdr hsr
      ((hsep.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Region.sub_prefix (by omega_arith)))
      (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (Q / 4) (Nat.le_refl _) u hs hd
      (fun j hj => hr (4 * j) (by omega_arith)) fun j hj => hw (4 * j) (by omega_arith))
    fun u₁ ⟨hrd₁, hwr₁, hsp₁, hg₁, hf₁, hb₁⟩ => ?_
  have hf₁' : Frame [⟨State.addr D + BitVec.ofNat 64 d, Q⟩] u.mem u₁.mem :=
    hf₁.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega_arith)⟩
  by_cases hm : Q % 4 = 0
  · simp only [hm, ite_true]
    have e : 4 * (Q / 4) = Q := by omega_arith
    rw [e] at hb₁
    exact WP.block_nil ⟨hrd₁, hwr₁, hsp₁, hg₁, hf₁', hb₁⟩
  · simp only [hm, ite_false]
    have eS : State.addr (S + BitVec.ofNat 32 (so + Q - 4)) =
        (State.addr S + BitVec.ofNat 64 so) + BitVec.ofNat 64 (Q - 4) := by
      rw [addr_add (by omega_arith), Offset.add_add, show so + (Q - 4) = so + Q - 4 by omega_arith]
    have eD : State.addr (D + BitVec.ofNat 32 (d + Q - 4)) =
        (State.addr D + BitVec.ofNat 64 d) + BitVec.ofNat 64 (Q - 4) := by
      rw [addr_add (by omega_arith), Offset.add_add, show d + (Q - 4) = d + Q - 4 by omega_arith]
    have hr' := hr (Q - 4) (by omega_arith)
    have hw' := hw (Q - 4) (by omega_arith)
    rw [← Offset.add_add] at hr' hw'
    refine WP.mono (copyW_ok (u := u₁) (so := so + Q - 4) (d := d + Q - 4) (hg₁ _ hsr ▸ hs) (hg₁ _ hdr ▸ hd)
      (by omega_arith) (by omega_arith) eS eD (by rw [hrd₁, hwr₁]; exact hr') (by rw [hwr₁]; exact hw') hdr)
      fun u₂ ⟨hrd₂, hwr₂, hsp₂, hg₂, hm₂⟩ => ?_
    have hf₂ : Frame [⟨(State.addr D + BitVec.ofNat 64 d) + BitVec.ofNat 64 (Q - 4), 4⟩] u₁.mem u₂.mem := by
      rw [hm₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    refine ⟨hrd₂.trans hrd₁, hwr₂.trans hwr₁, hsp₂.trans hsp₁, fun r hr => (hg₂ r hr).trans (hg₁ r hr),
      hf₁'.trans (hf₂.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base _ (by omega_arith)⟩), ?_⟩
    rw [show Q = (Q - 4) + 4 by omega_arith, Proof.Hmac.Common.bytesAt_add, Proof.Hmac.Common.bytesAt_add]
    congr 1
    · rw [bytesAt_frame hf₂ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.base_disjoint _ (by omega_arith) (by omega_arith)) (by omega_arith),
        bytesAt_take _ _ (k := 4 * (Q / 4)) (by omega_arith), hb₁, ← bytesAt_take _ _ (by omega_arith)]
    · rw [hm₂, bytesAt_copied]
      exact bytesAt_frame hf₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hsep.sub_left (Offset.sub_base _ (by omega_arith))).sub_right (Region.sub_prefix (by omega_arith)))
        (by omega_arith)

end VG.Proof.Ecdsa.Rfc6979.Arm

end

end

/-! ### `Ecdsa.Rfc6979.Arm.Reduce`, which this module and modules that import it used -/

section

/-!
# Deterministic ECDSA on 32-bit ARM: `h = bits2octets(digest)`

`X`'s `4 k` bytes (the digest's leftmost, in the frame at `xA`),
big-endian in `k` 32-bit words (`Xw`), less `n` (its words `nWn`), computed
as `X` plus the complement of `n` plus 1, by 16-bit digits (the model's
`adc` sets no flags; `digits_ok`): `X`'s words go to `h`'s place, and
those of the sum (`Dw`, with the carries `cc`) to `K`'s (`subWord_ok`).
The last carry is 1 exactly when the subtraction does not borrow; its
negation is a mask that selects, word by word, the difference's word or the
digest's, stored big-endian into `h` (`selWord_ok`). As the number is below
`2^(32 k) < 2n`, this is it modulo `n` (`mod_mathK`, `reduce_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_ldr wp_str wp_dp wp_mov wp_movw op2_reg op2_imm op2_lsr op2_lsl
  dpVal toNat_add_lt toNat_sub_le toNat_shr toNat_shl toNat_and_mask16 mask16)

/-! ## The arithmetic -/

/-- One word of `x + (2³² - 1 - n) + c`. -/
abbrev wsub (x n : BitVec 32) (c : Nat) : Nat := x.toNat + (2 ^ 32 - 1 - n.toNat) + c

/-- The `k` words of the digest, at `dg`, least significant first. -/
abbrev Xw (k : Nat) (m : Mem) (dg : Addr) (j : Nat) : BitVec 32 :=
  rev (m.readW (dg + BitVec.ofNat 64 (4 * (k - 1 - j))) 32)

/-- The carries of the digest plus the complement of `N` plus 1. -/
def cc (N k : Nat) (m : Mem) (dg : Addr) : Nat → Nat
  | 0 => 1
  | j + 1 => wsub (Xw k m dg j) (nWn N j) (cc N k m dg j) / 2 ^ 32

/-- The words of the digest plus the complement of `N` plus 1. -/
abbrev Dw (N k : Nat) (m : Mem) (dg : Addr) (j : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (wsub (Xw k m dg j) (nWn N j) (cc N k m dg j))

theorem cc_le (N k : Nat) (m : Mem) (dg : Addr) : ∀ j, cc N k m dg j ≤ 1
  | 0 => Nat.le_refl _
  | j + 1 => by
    have := cc_le N k m dg j; have := (Xw k m dg j).isLt; have := (nWn N j).isLt
    simp only [cc, wsub]; omega_arith

theorem chain (N k : Nat) (m : Mem) (dg : Addr) : ∀ i,
    wsum (Dw N k m dg) i + 2 ^ (32 * i) * cc N k m dg i + wsum (nWn N) i = wsum (Xw k m dg) i + 2 ^ (32 * i)
  | 0 => by simp [wsum, cc]
  | i + 1 => by
    obtain ih := chain N k m dg i
    obtain hc := cc_le N k m dg i
    obtain hN := (nWn N i).isLt
    obtain hw : (Dw N k m dg i).toNat + 2 ^ 32 * cc N k m dg (i + 1) =
        wsub (Xw k m dg i) (nWn N i) (cc N k m dg i) := by
      simp only [cc, BitVec.toNat_ofNat]; omega_arith
    simp only [wsub] at hw
    simp only [wsum]
    rw [show 32 * (i + 1) = 32 + 32 * i by omega_arith, Nat.pow_add]
    generalize 2 ^ (32 * i) = P at *
    generalize cc N k m dg (i + 1) = c' at *
    generalize cc N k m dg i = c at *
    generalize (Dw N k m dg i).toNat = D at *
    generalize (Xw k m dg i).toNat = X at *
    generalize (nWn N i).toNat = Nw at *
    obtain e : 2 ^ 32 - 1 - Nw + Nw = 2 ^ 32 - 1 := by omega_arith
    generalize 2 ^ 32 - 1 - Nw = M at *
    grind

/-- `x - N + 2^K` or `x`, by the last carry `c`: `x mod N`. -/
theorem select_math {x d c N K : Nat} (hc : c ≤ 1) (hd : d < 2 ^ K) (hx : x < 2 ^ K) (hN : 2 ^ K < 2 * N)
    (hch : d + 2 ^ K * c + N = x + 2 ^ K) :
    (if c = 1 then d else x) = x % N := by
  rcases (by omega_arith : c = 0 ∨ c = 1) with rfl | rfl
  · have := mod_mathK x N d K true (by simp only [Bool.toNat_true, Nat.mul_one]; omega_arith) hd hx hN
    simp only [Nat.zero_ne_one, ↓reduceIte] at this ⊢
    exact this
  · have := mod_mathK x N d K false (by simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero]; omega_arith)
      hd hx hN
    simp only [Bool.false_eq_true, ↓reduceIte] at this ⊢
    exact this

theorem wsum_ite (p : Prop) [Decidable p] (f g : Nat → BitVec 32) (k : Nat) :
    wsum (fun i => if p then f i else g i) k = if p then wsum f k else wsum g k := by
  by_cases h : p <;> simp only [h, ↓reduceIte]

/-- The difference's words or the digest's, by the last carry: the digest modulo `N`. -/
theorem reduce_math (N k : Nat) (m : Mem) (dg : Addr) (hlt : N < 2 ^ (32 * k)) (h2 : 2 ^ (32 * k) < 2 * N) :
    wsum (fun i => if cc N k m dg k = 1 then Dw N k m dg i else Xw k m dg i) k = wsum (Xw k m dg) k % N := by
  obtain hch := chain N k m dg k
  rw [wsum_nWn, Nat.mod_eq_of_lt hlt] at hch
  rw [wsum_ite]
  exact select_math (cc_le N k m dg k) (wsum_lt _ k) (wsum_lt _ k) h2 hch

/-! ## The code -/

/-- Two digits packed into a word. -/
theorem pack_toNat (x y : BitVec 32) (hx : x.toNat < 2 ^ 16) :
    (x ||| y <<< 16).toNat = x.toNat + y.toNat % 2 ^ 16 * 2 ^ 16 := by
  rw [BitVec.toNat_or, toNat_shl]
  obtain e : y.toNat * 2 ^ 16 % 2 ^ 32 = (y.toNat % 2 ^ 16) <<< 16 := by rw [Nat.shiftLeft_eq]; omega_arith
  rw [e, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq]
  omega_arith

theorem toNat_m16 : mask16.toNat = 2 ^ 16 - 1 := rfl

/-- A word of `x + (2³² - 1 - n) + c`, by 16-bit digits, in `r2`, and its
carry in `r7`, from `x` in `r0`, `n` in `r1` and `c` in `r7`, with `r10 = 0xffff`. -/
theorem digits_ok {s : State} (h10 : s.gpr .r10 = mask16) (hc : (s.gpr .r7).toNat ≤ 1)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ u, (u.gpr .r2).toNat + 2 ^ 32 * (u.gpr .r7).toNat = wsub (s.gpr .r0) (s.gpr .r1) (s.gpr .r7).toNat →
      (u.gpr .r7).toNat ≤ 1 → u.mem = s.mem → Rest [.r2, .r3, .r7, .r12] s u → WP isa (.block is) u Q) :
    WP isa (.block (Cfg.subDigit 0 ++ (Cfg.subDigit 1 ++ (.dp .orr .r2 .r2 (.reg .r3) :: is)))) s Q := by
  simp only [Cfg.subDigit, ↓reduceIte, show (1 : Nat) ≠ 0 by decide, List.cons_append, List.nil_append]
  refine wp_dpS (op2_reg _ _) fun s₁ u₁ => wp_dpS (op2_reg _ _) fun s₂ u₂ => wp_dpS (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_dpS (op2_reg _ _) fun s₄ u₄ => wp_dpS (op2_reg _ _) fun s₅ u₅ => ?_
  refine wp_movS (op2_lsr (by decide)) fun s₆ u₆ => wp_dpS (op2_reg _ _) fun s₇ u₇ => ?_
  refine wp_movS (op2_lsr (by decide)) fun s₈ u₈ => wp_movS (op2_lsr (by decide)) fun s₉ u₉ => ?_
  refine wp_dpS (op2_reg _ _) fun s₁₀ u₁₀ => wp_dpS (op2_reg _ _) fun s₁₁ u₁₁ => wp_dpS (op2_reg _ _) fun s₁₂ u₁₂ => ?_
  refine wp_movS (op2_lsr (by decide)) fun s₁₃ u₁₃ => wp_movS (op2_lsl (by decide)) fun s₁₄ u₁₄ => ?_
  refine wp_dpS (op2_reg _ _) fun s₁₅ u₁₅ => ?_
  obtain K : Rest [.r2, .r3, .r7, .r12] s s₁₅ :=
    (u₁.rest (by simp)).trans <| (u₂.rest (by simp)).trans <| (u₃.rest (by simp)).trans <|
    (u₄.rest (by simp)).trans <| (u₅.rest (by simp)).trans <| (u₆.rest (by simp)).trans <|
    (u₇.rest (by simp)).trans <| (u₈.rest (by simp)).trans <| (u₉.rest (by simp)).trans <|
    (u₁₀.rest (by simp)).trans <| (u₁₁.rest (by simp)).trans <| (u₁₂.rest (by simp)).trans <|
    (u₁₃.rest (by simp)).trans <| (u₁₄.rest (by simp)).trans (u₁₅.rest (by simp))
  -- The registers read, as on entry.
  obtain x₁ : (s₁.gpr .r2).toNat = (s.gpr .r0).toNat % 2 ^ 16 := by
    rw [u₁.gpr, dpVal, h10, toNat_and_mask16]
  obtain n₂ : (s₂.gpr .r3).toNat = (s.gpr .r1).toNat % 2 ^ 16 := by
    rw [u₂.gpr, dpVal, u₁.other _ (by decide), u₁.other _ (by decide), h10, toNat_and_mask16]
  obtain r10₂ : s₂.gpr .r10 = mask16 := by rw [u₂.other _ (by decide), u₁.other _ (by decide), h10]
  obtain a₃ : (s₃.gpr .r2).toNat = (s.gpr .r0).toNat % 2 ^ 16 + (2 ^ 16 - 1) := by
    rw [u₃.gpr, dpVal, toNat_add_lt (by rw [u₂.other _ (by decide), x₁, r10₂, toNat_m16]; omega_arith),
      u₂.other _ (by decide), x₁, r10₂, toNat_m16]
  obtain a₄ : (s₄.gpr .r2).toNat = (s.gpr .r0).toNat % 2 ^ 16 + (2 ^ 16 - 1) - (s.gpr .r1).toNat % 2 ^ 16 := by
    rw [u₄.gpr, dpVal, toNat_sub_le (by rw [a₃, u₃.other _ (by decide), n₂]; omega_arith), a₃,
      u₃.other _ (by decide), n₂]
  obtain c₄ : s₄.gpr .r7 = s.gpr .r7 := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  obtain lo : (s₅.gpr .r2).toNat = (s.gpr .r0).toNat % 2 ^ 16 + (2 ^ 16 - 1) - (s.gpr .r1).toNat % 2 ^ 16 +
      (s.gpr .r7).toNat := by
    rw [u₅.gpr, dpVal, toNat_add_lt (by rw [a₄, c₄]; omega_arith), a₄, c₄]
  obtain c₆ : (s₆.gpr .r7).toNat = (s₅.gpr .r2).toNat / 2 ^ 16 := by
    rw [u₆.gpr, toNat_shr]
  obtain r10₆ : s₆.gpr .r10 = mask16 := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), r10₂]
  obtain l₇ : (s₇.gpr .r2).toNat = (s₅.gpr .r2).toNat % 2 ^ 16 := by
    rw [u₇.gpr, dpVal, r10₆, toNat_and_mask16, u₆.other _ (by decide)]
  obtain r0₇ : s₇.gpr .r0 = s.gpr .r0 := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  obtain r1₈ : s₈.gpr .r1 = s.gpr .r1 := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  obtain x₈ : (s₈.gpr .r3).toNat = (s.gpr .r0).toNat / 2 ^ 16 := by rw [u₈.gpr, toNat_shr, r0₇]
  obtain n₉ : (s₉.gpr .r12).toNat = (s.gpr .r1).toNat / 2 ^ 16 := by rw [u₉.gpr, toNat_shr, r1₈]
  obtain r10₉ : s₉.gpr .r10 = mask16 := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), r10₆]
  obtain hx := (s.gpr .r0).isLt; have hn := (s.gpr .r1).isLt
  obtain a₁₀ : (s₁₀.gpr .r3).toNat = (s.gpr .r0).toNat / 2 ^ 16 + (2 ^ 16 - 1) := by
    rw [u₁₀.gpr, dpVal, toNat_add_lt (by rw [u₉.other _ (by decide), x₈, r10₉, toNat_m16]; omega_arith),
      u₉.other _ (by decide), x₈, r10₉, toNat_m16]
  obtain a₁₁ : (s₁₁.gpr .r3).toNat = (s.gpr .r0).toNat / 2 ^ 16 + (2 ^ 16 - 1) - (s.gpr .r1).toNat / 2 ^ 16 := by
    rw [u₁₁.gpr, dpVal, toNat_sub_le (by rw [a₁₀, u₁₀.other _ (by decide), n₉]; omega_arith), a₁₀,
      u₁₀.other _ (by decide), n₉]
  obtain c₁₁ : (s₁₁.gpr .r7).toNat = (s₅.gpr .r2).toNat / 2 ^ 16 := by
    rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), c₆]
  obtain hi : (s₁₂.gpr .r3).toNat = (s.gpr .r0).toNat / 2 ^ 16 + (2 ^ 16 - 1) - (s.gpr .r1).toNat / 2 ^ 16 +
      (s₅.gpr .r2).toNat / 2 ^ 16 := by
    rw [u₁₂.gpr, dpVal, toNat_add_lt (by rw [a₁₁, c₁₁, lo]; omega_arith), a₁₁, c₁₁]
  obtain c₁₃ : (s₁₃.gpr .r7).toNat = (s₁₂.gpr .r3).toNat / 2 ^ 16 := by
    rw [u₁₃.gpr, toNat_shr]
  obtain l₁₄ : (s₁₄.gpr .r2).toNat = (s₅.gpr .r2).toNat % 2 ^ 16 := by
    rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), l₇]
  obtain h₁₄ : s₁₄.gpr .r3 = s₁₂.gpr .r3 <<< 16 := by
    rw [u₁₄.gpr, u₁₃.other _ (by decide)]
  obtain w : (s₁₅.gpr .r2).toNat = (s₅.gpr .r2).toNat % 2 ^ 16 + (s₁₂.gpr .r3).toNat % 2 ^ 16 * 2 ^ 16 := by
    rw [u₁₅.gpr, dpVal, h₁₄, pack_toNat _ _ (by rw [l₁₄]; omega_arith), l₁₄]
  obtain c₁₅ : (s₁₅.gpr .r7).toNat = (s₁₂.gpr .r3).toNat / 2 ^ 16 := by
    rw [u₁₅.other _ (by decide), u₁₄.other _ (by decide), c₁₃]
  refine k s₁₅ ?_ ?_ ?_ K
  · rw [w, c₁₅, hi, lo]; simp only [wsub]; omega_arith
  · rw [c₁₅, hi, lo]; omega_arith
  · rw [u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem,
      u₃.mem, u₂.mem, u₁.mem]

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

theorem nWord_cfgOf (P : RfcHash) (j : Nat) : BitVec.ofNat 32 ((cfgOf P).nWord j) = nWn P.R.E.C.n j := by
  apply BitVec.eq_of_toNat_eq
  simp only [Cfg.nWord, cfgOf, nWn, BitVec.toNat_ofNat]
  omega_arith

theorem w_cfgOf (P : RfcHash) : (cfgOf P).w = P.k := rfl

theorem movw_movt_val {x : Nat} (hx : x < 2 ^ 32) :
    (BitVec.ofNat 16 (x >>> 16) ++ ((BitVec.ofNat 16 x).setWidth 32).extractLsb' 0 16 : BitVec 32) =
      BitVec.ofNat 32 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_append, BitVec.extractLsb'_toNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.shiftRight_zero]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega_arith), Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega_arith

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_movt {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movt d imm :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons (s' := s.setReg d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32)) rfl
    (k _ (Upd.setReg _ _ _))

theorem wp_rev {d m : Reg} (k : ∀ s', Upd s s' d (rev (s.gpr m)) → WP isa (.block is) s' Q) :
    WP isa (.block (.rev d m :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons rfl (k _ (Upd.setReg _ _ _))

end

/-- Where `X` is: the frame at `fX`. -/
abbrev xA {dn : Nat} (L : Lay dn) : Addr := L.B + BitVec.ofNat 64 216

/-- Where `h` is: the frame at `fH`. -/
abbrev hB : Nat := 152

/-- The regions `bits2octets` writes: `K`'s 128 bytes, and `h`'s `4 k`. -/
abbrev HW {dn : Nat} (L : Lay dn) (k : Nat) : List Region :=
  [⟨L.B + BitVec.ofNat 64 24, 128⟩, ⟨L.B + BitVec.ofNat 64 hB, 4 * k⟩]

/-- After `j` words of the subtraction, from `M`. -/
structure SubInv (N k : Nat) (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (M : Mem) (j : Nat) (u : State) :
    Prop where
  ctx : Ctx L g m₀ u
  r10 : u.gpr .r10 = mask16
  r7 : (u.gpr .r7).toNat = cc N k M (xA L) j
  frame : Frame (HW L k) M u.mem
  x : ∀ i < j, u.mem.readW (L.B + BitVec.ofNat 64 (hB + 4 * (k - 1 - i))) 32 = Xw k M (xA L) i
  d : ∀ i < j, u.mem.readW (L.B + BitVec.ofNat 64 (24 + 4 * (k - 1 - i))) 32 = Dw N k M (xA L) i

theorem fr_sep (B : Addr) {x y : Nat} (h : x + 4 ≤ y ∨ y + 4 ≤ x) (hx : x + 4 ≤ 536) (hy : y + 4 ≤ 536) :
    Mem.Sep (B + BitVec.ofNat 64 x) (32 / 8) (B + BitVec.ofNat 64 y) (32 / 8) :=
  Offset.sep B h (by omega_arith) (by omega_arith)

theorem fpA' (hL : L.Ok) {o e : Nat} (ho : o < 520) (he : 24 + o = e) :
    State.addr (L.fp + BitVec.ofNat 32 o) = L.B + BitVec.ofNat 64 e := by
  rw [hL.fpA ho, he]

theorem subWord_ok (hA : P.R.big = false) (hL : L.Ok) {M : Mem} {u : State} {j : Nat}
    (hj : j < P.k) (h : SubInv P.R.E.C.n P.k L g m₀ M j u)
    (hX : ∀ i < P.k, u.mem.readW (xA L + BitVec.ofNat 64 (4 * (P.k - 1 - i))) 32 =
      M.readW (xA L + BitVec.ofNat 64 (4 * (P.k - 1 - i))) 32) :
    WP isa (.block ((cfgOf P).subWord j)) u (SubInv P.R.E.C.n P.k L g m₀ M (j + 1)) := by
  apply WP.of_syms
  have hc := h.ctx
  obtain ⟨hQ, hk, -⟩ := P.sizesA hA
  have : fH = 128 := rfl; have : fK = 0 := rfl; have : fX = 192 := rfl; have : hB = 152 := rfl
  obtain hdg := hX j hj
  obtain o1 : fH + 4 * (P.k - 1 - j) < 4096 := by simp only [fH]; omega_arith
  obtain o2 : fK + 4 * (P.k - 1 - j) < 4096 := by simp only [fK]; omega_arith
  obtain o0 : fX + 4 * (P.k - 1 - j) < 4096 := by simp only [fX]; omega_arith
  obtain a1 : State.addr (L.fp + BitVec.ofNat 32 (fH + 4 * (P.k - 1 - j))) =
      L.B + BitVec.ofNat 64 (hB + 4 * (P.k - 1 - j)) :=
    fpA' hL (by simp only [fH]; omega_arith) (by simp only [fH]; omega_arith)
  obtain a2 : State.addr (L.fp + BitVec.ofNat 32 (fK + 4 * (P.k - 1 - j))) = L.B + BitVec.ofNat 64 (24 + 4 * (P.k - 1 - j)) :=
    fpA' hL (by simp only [fK]; omega_arith) (by simp only [fK]; omega_arith)
  obtain a0 : State.addr (L.fp + BitVec.ofNat 32 (fX + 4 * (P.k - 1 - j))) = xA L + BitVec.ofNat 64 (4 * (P.k - 1 - j)) := by
    rw [fpA' hL (by omega_arith) (show 24 + (fX + 4 * (P.k - 1 - j)) = 216 + 4 * (P.k - 1 - j) by omega_arith),
      xA, Offset.add_add]
  simp only [Cfg.subWord, Cfg.movImm, w_cfgOf, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_ldr (a := xA L + BitVec.ofNat 64 (4 * (P.k - 1 - j))) o0
    (by rw [hc.r8]; exact a0) (by rw [Offset.add_add]; exact hc.inFr (by omega_arith) (by omega_arith)) fun u₁ v₁ => ?_
  refine wp_rev fun u₂ v₂ => ?_
  refine wp_strS (a := L.B + BitVec.ofNat 64 (hB + 4 * (P.k - 1 - j))) o1
    (by rw [v₂.other .r8 (by decide), v₁.other .r8 (by decide), hc.r8]; exact a1)
    (by rw [v₂.wr, v₁.wr]; exact hc.inFrW (by omega_arith) (by omega_arith)) fun u₃ v₃ => ?_
  refine wp_movwS fun u₄ v₄ => wp_movt fun u₅ v₅ => ?_
  obtain hx : u₅.gpr .r0 = Xw P.k M (xA L) j := by
    rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr, v₂.gpr, v₁.gpr, hdg]
  obtain hnw : u₅.gpr .r1 = nWn P.R.E.C.n j := by
    rw [v₅.gpr, v₄.gpr, movw_movt_val (by simp only [Cfg.nWord]; omega_arith), nWord_cfgOf]
  obtain h10 : u₅.gpr .r10 = mask16 := by
    rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr, v₂.other _ (by decide), v₁.other _ (by decide),
      h.r10]
  obtain h7 : (u₅.gpr .r7).toNat = cc P.R.E.C.n P.k M (xA L) j := by
    rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr, v₂.other _ (by decide), v₁.other _ (by decide),
      h.r7]
  refine digits_ok h10 (by rw [h7]; exact cc_le _ _ _ _ _) fun u₆ e₆ c₆ m₆ K₆ => ?_
  obtain K₅ : Rest [.r0, .r1, .r2, .r3, .r7, .r12] u u₆ :=
    (v₁.rest (by simp)).trans <| (v₂.rest (by simp)).trans <| (v₃.rest _).trans <| (v₄.rest (by simp)).trans <|
    (v₅.rest (by simp)).trans (K₆.mono (by simp))
  refine wp_strS (a := L.B + BitVec.ofNat 64 (24 + 4 * (P.k - 1 - j))) o2
    (by rw [K₅.gpr .r8 (by decide), hc.r8]; exact a2)
    (by rw [K₅.wr]; exact hc.inFrW (by omega_arith) (by omega_arith)) fun u₇ v₇ => WP.block_nil (fun sy => ?_)
  rw [hx, hnw, h7] at e₆
  obtain hd : u₆.gpr .r2 = Dw P.R.E.C.n P.k M (xA L) j := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, ← e₆]
    have := (u₆.gpr .r2).isLt
    omega_arith
  obtain hm₇ : u₇.mem = (u.mem.writeW (L.B + BitVec.ofNat 64 (hB + 4 * (P.k - 1 - j))) (Xw P.k M (xA L) j)).writeW
      (L.B + BitVec.ofNat 64 (24 + 4 * (P.k - 1 - j))) (Dw P.R.E.C.n P.k M (xA L) j) := by
    rw [v₇.mem, hd, m₆, v₅.mem, v₄.mem, v₃.mem, v₂.gpr, v₂.mem, v₁.gpr, v₁.mem, hdg]
  obtain hf : Frame (HW L P.k) u.mem u₇.mem := by
    rw [hm₇]
    exact ((Frame.refl _ _).writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
      (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))).writeW List.mem_cons_self _
      (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
  refine ⟨hc.keep hL (by rw [v₇.rd, K₅.rd]) (by rw [v₇.wr, K₅.wr]) (by rw [v₇.sp, K₅.sp])
      (fun r hr => by rw [v₇.gpr, K₅.gpr r (by revert hr r; decide)]) hf
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact safe_low L (by omega_arith)
        · exact safe_low L (by omega_arith)) sy,
    by rw [v₇.gpr, K₅.gpr _ (by decide), h.r10], by rw [v₇.gpr]; simp only [cc]; omega_arith,
    h.frame.trans hf, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hm₇, Mem.readW_writeW_sep (fr_sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
    rcases Nat.lt_or_ge i j with hij | hij
    · rw [Mem.readW_writeW_sep (fr_sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]; exact h.x i hij
    · rw [show i = j by omega_arith, Mem.readW_writeW_self32]
  · rw [hm₇]
    rcases Nat.lt_or_ge i j with hij | hij
    · rw [Mem.readW_writeW_sep (fr_sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        Mem.readW_writeW_sep (fr_sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]; exact h.d i hij
    · rw [show i = j by omega_arith, Mem.readW_writeW_self32]

/-- `X`'s words, unchanged by what `bits2octets` writes. -/
theorem x_kept (hA : P.R.big = false) (hL : L.Ok) {M M' : Mem} (hf : Frame (HW L P.k) M M') :
    ∀ i < P.k, M'.readW (xA L + BitVec.ofNat 64 (4 * (P.k - 1 - i))) 32 =
      M.readW (xA L + BitVec.ofNat 64 (4 * (P.k - 1 - i))) 32 := fun i hi => by
  obtain ⟨hQ, hk, -⟩ := P.sizesA hA
  have : hB = 152 := rfl
  rw [Offset.add_add]
  refine hf.readW (r := ⟨L.B + BitVec.ofNat 64 216, 68⟩) (Offset.contains _ (by omega_arith) (by omega_arith)
    (by have := hL.B_fit; omega_arith)) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

/-- The words before `k`. -/
theorem subs_ok (hA : P.R.big = false) (hL : L.Ok) {M : Mem} :
    ∀ i ≤ P.k, ∀ u, SubInv P.R.E.C.n P.k L g m₀ M 0 u →
    WP isa (.block ((List.range i).flatMap (cfgOf P).subWord)) u (SubInv P.R.E.C.n P.k L g m₀ M i)
  | 0, _, u, h => WP.block_nil h
  | i + 1, hi, u, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    exact WP.mono (subs_ok hA hL i (by omega_arith) u h) fun u' h' =>
      subWord_ok hA hL (by omega_arith) h' fun j hj => x_kept hA hL h'.frame j hj

/-- The mask of the last carry. -/
abbrev mask (N k : Nat) {dn : Nat} (L : Lay dn) (m : Mem) : BitVec 32 :=
  if cc N k m (xA L) k = 1 then BitVec.allOnes 32 else 0

/-- The word selected. -/
abbrev Sw (N k : Nat) {dn : Nat} (L : Lay dn) (m : Mem) (i : Nat) : BitVec 32 :=
  if cc N k m (xA L) k = 1 then Dw N k m (xA L) i else Xw k m (xA L) i

/-- After the mask and `j` words of the selection, from `M`. -/
structure SelInv (N k : Nat) (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (M : Mem) (j : Nat) (u : State) :
    Prop where
  ctx : Ctx L g m₀ u
  r7 : u.gpr .r7 = mask N k L M
  frame : Frame (HW L k) M u.mem
  h : ∀ i < j, u.mem.readW (L.B + BitVec.ofNat 64 (hB + 4 * (k - 1 - i))) 32 = rev (Sw N k L M i)
  x : ∀ i, j ≤ i → i < k → u.mem.readW (L.B + BitVec.ofNat 64 (hB + 4 * (k - 1 - i))) 32 =
    Xw k M (xA L) i
  d : ∀ i < k, u.mem.readW (L.B + BitVec.ofNat 64 (24 + 4 * (k - 1 - i))) 32 = Dw N k M (xA L) i

theorem sel_val (x d : BitVec 32) (p : Prop) [Decidable p] :
    x ^^^ ((d ^^^ x) &&& (if p then BitVec.allOnes 32 else 0)) = if p then d else x := by
  by_cases h : p
  · simp only [h, ↓reduceIte, BitVec.and_allOnes]
    rw [BitVec.xor_comm d x, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · simp only [h, ↓reduceIte]
    rw [show (0 : BitVec 32) = 0#32 from rfl]
    simp only [BitVec.and_zero, BitVec.xor_zero]

theorem selWord_ok (hA : P.R.big = false) (hL : L.Ok) {M : Mem} {u : State} {j : Nat}
    (hj : j < P.k) (h : SelInv P.R.E.C.n P.k L g m₀ M j u) :
    WP isa (.block ((cfgOf P).selWord j)) u (SelInv P.R.E.C.n P.k L g m₀ M (j + 1)) := by
  apply WP.of_syms
  have hc := h.ctx
  obtain ⟨hQ, hk, -⟩ := P.sizesA hA
  have : fH = 128 := rfl; have : fK = 0 := rfl; have : hB = 152 := rfl
  obtain o1 : fH + 4 * (P.k - 1 - j) < 4096 := by simp only [fH]; omega_arith
  obtain o2 : fK + 4 * (P.k - 1 - j) < 4096 := by simp only [fK]; omega_arith
  obtain a1 : State.addr (L.fp + BitVec.ofNat 32 (fH + 4 * (P.k - 1 - j))) =
      L.B + BitVec.ofNat 64 (hB + 4 * (P.k - 1 - j)) :=
    fpA' hL (by simp only [fH]; omega_arith) (by simp only [fH]; omega_arith)
  obtain a2 : State.addr (L.fp + BitVec.ofNat 32 (fK + 4 * (P.k - 1 - j))) = L.B + BitVec.ofNat 64 (24 + 4 * (P.k - 1 - j)) :=
    fpA' hL (by simp only [fK]; omega_arith) (by simp only [fK]; omega_arith)
  simp only [Cfg.selWord, w_cfgOf]
  refine wp_ldr (a := L.B + BitVec.ofNat 64 (hB + 4 * (P.k - 1 - j))) o1 (by rw [hc.r8]; exact a1)
    (hc.inFr (by omega_arith) (by omega_arith)) fun u₁ v₁ => ?_
  refine wp_ldr (a := L.B + BitVec.ofNat 64 (24 + 4 * (P.k - 1 - j))) o2 (by rw [v₁.other .r8 (by decide), hc.r8]; exact a2)
    (by rw [v₁.rd, v₁.wr]; exact hc.inFr (by omega_arith) (by omega_arith)) fun u₂ v₂ => ?_
  refine wp_dpS (op2_reg _ _) fun u₃ v₃ => wp_dpS (op2_reg _ _) fun u₄ v₄ => wp_dpS (op2_reg _ _) fun u₅ v₅ => ?_
  refine wp_rev fun u₆ v₆ => ?_
  obtain K₆ : Rest [.r0, .r1] u u₆ :=
    (v₁.rest (by simp)).trans <| (v₂.rest (by simp)).trans <| (v₃.rest (by simp)).trans <|
    (v₄.rest (by simp)).trans <| (v₅.rest (by simp)).trans (v₆.rest (by simp))
  refine wp_strS (a := L.B + BitVec.ofNat 64 (hB + 4 * (P.k - 1 - j))) o1
    (by rw [K₆.gpr .r8 (by decide), hc.r8]; exact a1)
    (by rw [K₆.wr]; exact hc.inFrW (by omega_arith) (by omega_arith)) fun u₇ v₇ => WP.block_nil (fun sy => ?_)
  obtain val : u₆.gpr .r0 = rev (Sw P.R.E.C.n P.k L M j) := by
    rw [v₆.gpr, v₅.gpr, dpVal, v₄.gpr, dpVal, v₄.other .r0 (by decide), v₃.gpr, dpVal, v₃.other .r0 (by decide),
      v₃.other .r7 (by decide), v₂.gpr, v₂.other .r0 (by decide), v₂.other .r7 (by decide), v₁.gpr,
      v₁.other .r7 (by decide), v₁.mem, h.x j (by omega_arith) hj, h.d j hj, h.r7, Sw, mask]
    exact congrArg rev (sel_val _ _ _)
  obtain hm₇ : u₇.mem = u.mem.writeW (L.B + BitVec.ofNat 64 (hB + 4 * (P.k - 1 - j))) (rev (Sw P.R.E.C.n P.k L M j)) := by
    rw [v₇.mem, val, v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem]
  obtain hf : Frame (HW L P.k) u.mem u₇.mem := by
    rw [hm₇]
    exact (Frame.refl _ _).writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
      (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
  refine ⟨hc.keep hL (by rw [v₇.rd, K₆.rd]) (by rw [v₇.wr, K₆.wr]) (by rw [v₇.sp, K₆.sp])
      (fun r hr => by rw [v₇.gpr, K₆.gpr r (by revert hr r; decide)]) hf
      (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact safe_low L (by omega_arith)
        · exact safe_low L (by omega_arith)) sy,
    by rw [v₇.gpr, K₆.gpr _ (by decide), h.r7], h.frame.trans hf, fun i hi => ?_, fun i hi hi' => ?_,
    fun i hi => ?_⟩
  · rw [hm₇]
    rcases Nat.lt_or_ge i j with hij | hij
    · rw [Mem.readW_writeW_sep (fr_sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]; exact h.h i hij
    · rw [show i = j by omega_arith, Mem.readW_writeW_self32]
  · rw [hm₇, Mem.readW_writeW_sep (fr_sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
    exact h.x i (by omega_arith) hi'
  · rw [hm₇, Mem.readW_writeW_sep (fr_sep _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
    exact h.d i hi

/-- The words before `k`. -/
theorem sels_ok (hA : P.R.big = false) (hL : L.Ok) {M : Mem} :
    ∀ i ≤ P.k, ∀ u, SelInv P.R.E.C.n P.k L g m₀ M 0 u →
    WP isa (.block ((List.range i).flatMap (cfgOf P).selWord)) u (SelInv P.R.E.C.n P.k L g m₀ M i)
  | 0, _, u, h => WP.block_nil h
  | i + 1, hi, u, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    exact WP.mono (sels_ok hA hL i (by omega_arith) u h) fun u' h' => selWord_ok hA hL (by omega_arith) h'

theorem mask_val {c : BitVec 32} (h : c.toNat ≤ 1) :
    0#32 - c = if c.toNat = 1 then BitVec.allOnes 32 else 0 := by
  rcases (by omega_arith : c.toNat = 0 ∨ c.toNat = 1) with e | e
  · rw [show c = 0 from BitVec.eq_of_toNat_eq (by rw [e]; rfl)]; decide
  · rw [show c = 1 from BitVec.eq_of_toNat_eq (by rw [e]; rfl)]; decide

/-- `h`: `X` modulo `n`, big-endian in the frame at `hB`. -/
theorem reduce_ok (hA : P.R.big = false) (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).reduce) t fun t' => Ctx L g m₀ t' ∧
      Frame (HW L P.k) t.mem t'.mem ∧
      Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 hB) (4 * P.k)) =
        Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (xA L) (4 * P.k)) % P.R.E.C.n := by
  simp only [Cfg.reduce, w_cfgOf, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_movwS fun u₁ v₁ => wp_movS (op2_imm (by decide)) fun u₂ v₂ => ?_
  obtain hc₂ : Ctx L g m₀ u₂ := (hc.upd v₁ (by decide)).upd v₂ (by decide)
  rw [WP.block_append_iff]
  obtain hmu : u₂.mem = t.mem := by rw [v₂.mem, v₁.mem]
  refine WP.mono (subs_ok (P := P) (M := t.mem) hA hL P.k (Nat.le_refl _) u₂
    ⟨hc₂, by rw [v₂.other _ (by decide), v₁.gpr], by rw [v₂.gpr]; rfl, by rw [hmu]; exact Frame.refl _ _,
      fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => absurd hi (Nat.not_lt_zero _)⟩) fun u hu => ?_
  refine wp_movS (op2_imm (by decide)) fun u₃ v₃ => wp_dpS (op2_reg _ _) fun u₄ v₄ => ?_
  obtain hc₄ : Ctx L g m₀ u₄ := (hu.ctx.upd v₃ (by decide)).upd v₄ (by decide)
  obtain h7 : u₄.gpr .r7 = mask P.R.E.C.n P.k L t.mem := by
    rw [v₄.gpr, dpVal, v₃.gpr, v₃.other _ (by decide), mask_val (by rw [hu.r7]; exact cc_le _ _ _ _ _), hu.r7]
  obtain hm₄ : u₄.mem = u.mem := by rw [v₄.mem, v₃.mem]
  refine WP.mono (sels_ok (P := P) (M := t.mem) hA hL P.k (Nat.le_refl _) u₄
    ⟨hc₄, h7, by rw [hm₄]; exact hu.frame, fun i hi => absurd hi (Nat.not_lt_zero _),
      fun i _ hi => by rw [hm₄]; exact hu.x i hi, fun i hi => by rw [hm₄]; exact hu.d i hi⟩)
    fun t' h' => ⟨h'.ctx, h'.frame, ?_⟩
  obtain hX := ofBytes_words t.mem (Xw P.k t.mem (xA L)) (xA L) P.k fun j hj => rfl
  obtain hH := ofBytes_words t'.mem (Sw P.R.E.C.n P.k L t.mem) (L.B + BitVec.ofNat 64 hB) P.k fun j hj => by
    rw [Offset.add_add, h'.h j hj]
    exact Proof.Pbkdf2.Whole.byteRev32_byteRev32 _
  obtain e32 : 32 * P.k = 8 * P.R.E.C.len := by have := (P.sizesA hA).1; simp only [RfcHash.Q] at this; omega_arith
  change Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt _ _ (4 * P.k)) =
    Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt _ _ (4 * P.k)) % _
  rw [hH, hX]
  exact reduce_math _ _ _ _ (by rw [e32]; exact (Nat.log2_lt P.R.n_ne).mp (by rw [← (P.R.sizesA hA).2.2.1]; unfold Spec.Ecdsa.nBits; omega_using [])) (by rw [e32]; exact (P.R.sizesA hA).2.2.2)

end VG.Proof.Ecdsa.Rfc6979.Arm

end

end

/-!
# Deterministic ECDSA on 32-bit ARM: the blocks between the calls

`V = 0x01…` and `K = 0x00…` (`initKV_ok`), the number of candidates, in
`r9` (`initCnt_ok`), whether to go on (`goOn_ok`, `again_ok`, `stop_ok`),
and the wiping of the frame below the saved registers, by a loop of word
stores, with our caller's registers restored (`wipe_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.Arm

open VG VG.Arm VG.Impl.Ecdsa.Rfc6979.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_ldr wp_str wp_dp wp_mov wp_movw wp_cmp wp_subs op2_reg op2_imm dpVal)

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

/-- The `4 k` bytes at `q`, each of whose words is `w`. -/
theorem bytesAt_of_readW (m : Mem) (q : Addr) (w : BitVec 32) {k : Nat}
    (h : ∀ j < k, m.readW (q + BitVec.ofNat 64 (4 * j)) 32 = w) :
    Spec.Sha256.bytesAt m q (4 * k) = (List.range (4 * k)).map fun i => w.extractLsb' (8 * (i % 4)) 8 := by
  simp only [Spec.Sha256.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  rw [show i = 4 * (i / 4) + i % 4 by omega_arith, Proof.Weierstrass.byte_word32 m q (i / 4) (Nat.mod_lt _ (by decide)),
    h _ (by omega_arith)]
  congr 2; omega_arith

/-- Code that changes only flags keeps `Ctx`. -/
theorem Ctx.flags (hL : L.Ok) {t t' : State} (hc : Ctx L g m₀ t) (h : FupdS t t') : Ctx L g m₀ t' :=
  hc.keep hL h.rd h.wr h.sp (fun r _ => by rw [h.gpr]) (ws := []) (by rw [h.mem]; exact Frame.refl _ _)
    (by simp) h.syms

/-! ## `V` and `K` -/

theorem kvN_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {a b : BitVec 32} (ha : u.gpr .r0 = a)
    (hb : u.gpr .r1 = b) : ∀ k ≤ 16,
    WP isa (.block ((List.range k).flatMap fun j => [.str .r0 .r8 (fV + 4 * j), .str .r1 .r8 (fK + 4 * j)])) u
      fun u' => u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.sp = u.sp ∧ u'.gpr = u.gpr ∧
        Frame [⟨L.B + BitVec.ofNat 64 24, 128⟩] u.mem u'.mem ∧
        ∀ j < k, u'.mem.readW (L.B + BitVec.ofNat 64 (88 + 4 * j)) 32 = a ∧
          u'.mem.readW (L.B + BitVec.ofNat 64 (24 + 4 * j)) 32 = b
  | 0, _ => WP.block_nil ⟨rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1, hk => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (kvN_ok hL hc ha hb k (by omega_arith)) fun u₁ ⟨hrd, hwr, hsp, hg, hf, hv⟩ => ?_
    have e₁ : State.addr (L.fp + BitVec.ofNat 32 (fV + 4 * k)) = L.B + BitVec.ofNat 64 (88 + 4 * k) :=
      fpA' hL (by simp only [fV]; omega_arith) (by simp only [fV]; omega_arith)
    have e₂ : State.addr (L.fp + BitVec.ofNat 32 (fK + 4 * k)) = L.B + BitVec.ofNat 64 (24 + 4 * k) :=
      fpA' hL (by simp only [fK]; omega_arith) (by simp only [fK]; omega_arith)
    have o₁ : fV + 4 * k < 4096 := by simp only [fV]; omega_arith
    have o₂ : fK + 4 * k < 4096 := by simp only [fK]; omega_arith
    have r8₁ : u₁.gpr .r8 = L.fp := by rw [hg, hc.r8]
    refine wp_strS (a := L.B + BitVec.ofNat 64 (88 + 4 * k)) o₁ (by rw [r8₁]; exact e₁)
      (by rw [hwr]; exact hc.inFrW (by omega_arith) (by omega_arith)) fun u₂ v₂ => ?_
    refine wp_strS (a := L.B + BitVec.ofNat 64 (24 + 4 * k)) o₂ (by rw [v₂.gpr, r8₁]; exact e₂)
      (by rw [v₂.wr, hwr]; exact hc.inFrW (by omega_arith) (by omega_arith)) fun u₃ v₃ => WP.block_nil ?_
    have sep : ∀ x y, x + 4 ≤ y ∨ y + 4 ≤ x → x + 4 ≤ 240 → y + 4 ≤ 240 →
        Mem.Sep (L.B + BitVec.ofNat 64 x) (32 / 8) (L.B + BitVec.ofNat 64 y) (32 / 8) :=
      fun x y h h₁ h₂ => Offset.sep _ h (by omega_arith) (by omega_arith)
    have hm₃ : u₃.mem = (u₁.mem.writeW (L.B + BitVec.ofNat 64 (88 + 4 * k)) a).writeW
        (L.B + BitVec.ofNat 64 (24 + 4 * k)) b := by
      rw [v₃.mem, v₂.mem, v₂.gpr, hg, ha, hb]
    have hf₃ : Frame [⟨L.B + BitVec.ofNat 64 24, 128⟩] u₁.mem u₃.mem := by
      rw [hm₃]
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
    refine ⟨by rw [v₃.rd, v₂.rd, hrd], by rw [v₃.wr, v₂.wr, hwr], by rw [v₃.sp, v₂.sp, hsp],
      by rw [v₃.gpr, v₂.gpr, hg], hf.trans hf₃, fun j hj => ?_⟩
    rw [hm₃]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [Mem.readW_writeW_sep (sep _ _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        Mem.readW_writeW_sep (sep _ _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        Mem.readW_writeW_sep (sep _ _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        Mem.readW_writeW_sep (sep _ _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide)]
      exact hv j hj
    · rw [Mem.readW_writeW_sep (sep _ _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        Mem.readW_writeW_self32, Mem.readW_writeW_self32]
      exact ⟨rfl, rfl⟩

theorem kv_bytes (m : Mem) (B : Addr) (w : BitVec 32) (o : Nat)
    (h : ∀ j < 16, m.readW (B + BitVec.ofNat 64 (o + 4 * j)) 32 = w) :
    Spec.Sha256.bytesAt m (B + BitVec.ofNat 64 o) 64 =
      (List.range 64).map fun i => w.extractLsb' (8 * (i % 4)) 8 :=
  bytesAt_of_readW (k := 16) m _ w fun j hj => by rw [Offset.add_add]; exact h j hj

theorem replicate_take (n k : Nat) (b : Byte) (h : n ≤ k) : (List.replicate k b).take n = List.replicate n b := by
  rw [List.take_replicate, Nat.min_eq_left h]

theorem ones_word : ((0x0101 : BitVec 16) ++ ((0x0101 : BitVec 16).setWidth 32).extractLsb' 0 16 : BitVec 32) =
    0x01010101 := by decide

theorem wp_movt' {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {imm : BitVec 16}
    (k : ∀ s', UpdS s s' d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movt d imm :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons (s' := s.setReg d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32)) rfl
    (k _ ⟨Upd.setReg _ _ _,rfl⟩)

/-- `V = 0x01…` and `K = 0x00…`: their first `n` bytes, for any `n ≤ 64`. -/
theorem initKV_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.initKV) t fun t' => Ctx L g m₀ t' ∧ Frame [⟨L.B + BitVec.ofNat 64 24, 128⟩] t.mem t'.mem ∧
      (∀ n ≤ 64, Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 88) n = List.replicate n 1) ∧
      ∀ n ≤ 64, Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 24) n = List.replicate n 0 := by
  rw [Cfg.initKV, List.cons_append, List.cons_append, List.cons_append, List.nil_append]
  refine wp_movwS fun u₁ v₁ => wp_movt' fun u₂ v₂ => wp_movS (op2_imm (by decide)) fun u₃ v₃ => ?_
  have hc₃ : Ctx L g m₀ u₃ := ((hc.upd v₁ (by decide)).upd v₂ (by decide)).upd v₃ (by decide)
  have h0 : u₃.gpr .r0 = 0x01010101 := by rw [v₃.other _ (by decide), v₂.gpr, v₁.gpr, ones_word]
  have hm₃ : u₃.mem = t.mem := by rw [v₃.mem, v₂.mem, v₁.mem]
  refine WP.mono_syms (kvN_ok hL hc₃ h0 v₃.gpr 16 (by omega_arith)) fun u' ⟨hrd', hwr', hsp', hg, hf, hv⟩ sy =>
      ⟨hc₃.keep hL hrd' hwr' hsp' (fun r _ => by rw [hg]) hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega_arith)) sy,
      by rw [hm₃] at hf; exact hf, fun n hn => ?_, fun n hn => ?_⟩
  · rw [bytesAt_take _ _ (k := 64) hn, show (88 : Nat) = 88 + 0 from rfl,
      kv_bytes _ _ _ _ fun j hj => (hv j hj).1, show (List.range 64).map
        (fun i => (0x01010101 : BitVec 32).extractLsb' (8 * (i % 4)) 8) = List.replicate 64 1 by decide,
      replicate_take _ _ _ hn]
  · rw [bytesAt_take _ _ (k := 64) hn, show (24 : Nat) = 24 + 0 from rfl,
      kv_bytes _ _ _ _ fun j hj => (hv j hj).2, show (List.range 64).map
        (fun i => (0#32 : BitVec 32).extractLsb' (8 * (i % 4)) 8) = List.replicate 64 0 by decide,
      replicate_take _ _ _ hn]

/-! ## The number of candidates -/

theorem initCnt_ok {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).initCnt) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .r9 = BitVec.ofNat 32 P.I.tries :=
  movw_ok hc (d := .r9) (v := P.I.tries) (by decide) P.tries_lt fun t' c' m' v' _ => WP.block_nil ⟨c', m', v'⟩

/-! ## Whether to go on -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `subs`, with its carry: set iff no borrow. -/
theorem wp_subsC {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', UpdS s s' d (s.gpr n - y) → s'.c = decide (y.toNat ≤ (s.gpr n).toNat) → WP isa (.block is) s' Q) :
    WP isa (.block (.subs d n o :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons (s' := (subFlags s (s.gpr n) y).setReg d (s.gpr n - y))
    (by simp only [exec, ho, Option.map_some]) (k _ ⟨Upd.subs _ _ _ _ _,rfl⟩ rfl)

/-- `mov`, keeping the carry. -/
theorem wp_movC {d : Reg} {o : Op2} {v : BitVec 32} (ho : o.eval s = some v)
    (k : ∀ s', UpdS s s' d v → s'.c = s.c → WP isa (.block is) s' Q) : WP isa (.block (.mov d o :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons (s' := s.setReg d v) (by simp only [exec, ho, Option.map_some])
    (k _ ⟨Upd.setReg _ _ _,rfl⟩ rfl)

/-- `adc`. -/
theorem wp_adc {d n : Reg} {o : Op2} {y : BitVec 32} (ho : o.eval s = some y)
    (k : ∀ s', UpdS s s' d (s.gpr n + y + (if s.c then 1 else 0)) → WP isa (.block is) s' Q) :
    WP isa (.block (.adc d n o :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons (s' := s.setReg d (s.gpr n + y + (if s.c then 1 else 0)))
    (by simp only [exec, ho, Option.map_some]) (k _ ⟨Upd.setReg _ _ _,rfl⟩)

end

/-- The decision's arithmetic: `(C - 1) & count`, `C` set iff `r ≥ 1`, is nonzero iff `r = 0` and
`count ≠ 0`. -/
theorem decide_go (r cnt : BitVec 32) :
    (!((((0#32 + 0#32 + (if decide ((1#32 : BitVec 32).toNat ≤ r.toNat) = true then 1 else 0) - 1#32 : BitVec 32) &&& cnt)
      - 0#32) == 0)) = decide (r = 0 ∧ cnt ≠ 0) := by
  by_cases h : r = 0
  · subst h
    have hc : decide ((1#32 : BitVec 32).toNat ≤ (0 : BitVec 32).toNat) = false := by decide
    have e1 : (0#32 + 0#32 + (if false = true then 1 else 0) - 1#32 : BitVec 32) = BitVec.allOnes 32 := by decide
    have e2 : cnt - 0#32 = cnt := BitVec.sub_zero cnt
    rw [hc, e1, BitVec.allOnes_and, e2]
    by_cases h' : cnt = 0
    · subst h'; decide
    · have h'' : cnt ≠ 0#32 := h'
      simp [h'']
  · have h0 : r ≠ 0#32 := h
    have hr : decide ((1#32 : BitVec 32).toNat ≤ r.toNat) = true := by
      rcases Nat.eq_zero_or_pos r.toNat with e | e
      · exact absurd (BitVec.eq_of_toNat_eq (by rw [e]; rfl)) h
      · exact decide_eq_true e
    have e3 : (0#32 + 0#32 + (if true = true then 1 else 0) - 1#32 : BitVec 32) = 0 := by decide
    have e4 : (0 : BitVec 32) &&& cnt = 0 := BitVec.zero_and
    rw [hr, e3, e4]
    simp [h0]

/-- One candidate fewer, and `Z` clear iff the signature failed and candidates are left. -/
theorem goOn_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.goOn) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.gpr .r9 = t.gpr .r9 - 1 ∧
      t'.gpr .r0 = t.gpr .r0 ∧ t'.gpr .r1 = t.gpr .r1 ∧
      isa.eval .ne t' = some (decide (t.gpr .r0 = 0 ∧ t.gpr .r9 - 1 ≠ 0)) := by
  simp only [Cfg.goOn]
  refine wp_dpS (op2_imm (by decide)) fun u₁ v₁ => wp_subsC (op2_imm (by decide)) fun u₂ v₂ c₂ => ?_
  refine wp_movC (op2_imm (by decide)) fun u₃ v₃ c₃ => wp_adc (op2_imm (by decide)) fun u₄ v₄ => ?_
  refine wp_dpS (op2_imm (by decide)) fun u₅ v₅ => wp_dpS (op2_reg _ _) fun u₆ v₆ => ?_
  refine wp_cmpS (op2_imm (by decide)) fun u₇ v₇ z₇ => WP.block_nil ?_
  have hc₆ : Ctx L g m₀ u₆ := (((((hc.upd v₁ (by decide)).upd v₂ (by decide)).upd v₃ (by decide)).upd v₄
    (by decide)).upd v₅ (by decide)).upd v₆ (by decide)
  have K : Rest [.r9, .r10, .r7] t u₆ :=
    (v₁.rest (by simp)).trans <| (v₂.rest (by simp)).trans <| (v₃.rest (by simp)).trans <|
    (v₄.rest (by simp)).trans <| (v₅.rest (by simp)).trans (v₆.rest (by simp))
  have r9₅ : u₅.gpr .r9 = t.gpr .r9 - 1 := by
    rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr,
      dpVal]; rfl
  have r9₆ : u₆.gpr .r9 = t.gpr .r9 - 1 := by rw [v₆.other _ (by decide), r9₅]
  have r0₁ : u₁.gpr .r0 = t.gpr .r0 := v₁.other _ (by decide)
  refine ⟨hc₆.flags hL v₇, by rw [v₇.mem, v₆.mem, v₅.mem, v₄.mem, v₃.mem, v₂.mem, v₁.mem], by rw [v₇.gpr]; exact r9₆,
    by rw [v₇.gpr, K.gpr _ (by decide)], by rw [v₇.gpr, K.gpr _ (by decide)], ?_⟩
  show some (!u₇.z) = _
  rw [z₇, v₆.gpr, dpVal, v₅.gpr, dpVal, v₄.gpr, v₃.gpr, c₃, c₂, r9₅, r0₁]
  exact congrArg some (decide_go _ _)

theorem flag_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {v : Nat} (hv : v < 2) :
    WP isa (.block [.mov .r7 (.imm (BitVec.ofNat 32 v)), .cmp .r7 (.imm 0)]) t fun t' => Ctx L g m₀ t' ∧
      t'.mem = t.mem ∧ (∀ r, r ≠ .r7 → t'.gpr r = t.gpr r) ∧ isa.eval .ne t' = some (decide (v = 1)) :=
  wp_movS (op2_imm (by rcases (by omega_arith : v = 0 ∨ v = 1) with rfl | rfl <;> decide)) fun u₁ v₁ =>
    wp_cmpS (op2_imm (by decide)) fun u₂ v₂ z₂ => WP.block_nil
      ⟨(hc.upd v₁ (by decide)).flags hL v₂, by rw [v₂.mem, v₁.mem], fun r hr => by rw [v₂.gpr, v₁.other _ hr],
      by
        show some (!u₂.z) = _
        rw [z₂, v₁.gpr]
        rcases (by omega_arith : v = 0 ∨ v = 1) with rfl | rfl <;> decide⟩

/-- `Z` clear: go on. -/
theorem again_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.again) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.gpr .r9 = t.gpr .r9 ∧
      isa.eval .ne t' = some true :=
  WP.mono (flag_ok hL hc (v := 1) (by decide)) fun _ ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃ _ (by decide), h₄⟩

/-- `Z` set: stop. -/
theorem stop_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.stop) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.gpr .r0 = t.gpr .r0 ∧
      isa.eval .ne t' = some false :=
  WP.mono (flag_ok hL hc (v := 0) (by decide)) fun _ ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃ _ (by decide), h₄⟩

/-! ## The wiping -/

/-- What the wipe's loop keeps after `i` words. -/
structure WipeI (t : State) (L : Lay dn) (i : Nat) (u : State) : Prop where
  r12 : u.gpr .r12 = L.fp + BitVec.ofNat 32 (4 * i)
  r3 : u.gpr .r3 = BitVec.ofNat 32 (wipeWords - i)
  other : ∀ r, r ≠ .r3 → r ≠ .r12 → u.gpr r = t.gpr r
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  sp : u.sp = t.sp
  frame : Frame [⟨L.B + BitVec.ofNat 64 24, 4 * wipeWords⟩] t.mem u.mem

/-- The loop of word stores: `wipeWords` words from the frame's base. -/
theorem wipeLoop_ok (hL : L.Ok) {t : State} (hwr : t.wr = [L.FR, L.OUT, L.SCR]) (h12 : t.gpr .r12 = L.fp)
    (h3 : t.gpr .r3 = BitVec.ofNat 32 wipeWords) :
    WP isa (.loop (.block Cfg.wipeBody) .ne) t fun t' => WipeI t L wipeWords t' := by
  have hb := hL.B_fit
  refine WP.loop (M := isa) (body := .block Cfg.wipeBody) (c := .ne)
    (fun (k : Nat) (u : State) => ∃ i, k = wipeWords - i ∧ i < wipeWords ∧ WipeI t L i u) ?_ (wipeWords - 0) _
    ⟨0, rfl, by decide, by rw [h12, Nat.mul_zero, BitVec.add_zero], by rw [h3]; rfl, fun _ _ _ => rfl, rfl, rfl, rfl,
      Frame.refl _ _⟩
  rintro k u ⟨i, rfl, hi, I⟩
  have hw : wipeWords = 117 := rfl
  have ea : State.addr (u.gpr .r12 + BitVec.ofNat 32 0) = L.B + BitVec.ofNat 64 (24 + 4 * i) := by
    rw [I.r12, BitVec.add_zero, hL.fpA (by omega_arith)]
  refine wp_str (a := L.B + BitVec.ofNat 64 (24 + 4 * i)) (by decide) ea
    (by rw [I.wr, hwr]; exact ⟨L.FR, by simp, Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith)⟩)
    fun u₁ v₁ => wp_dp (op2_imm (by decide)) fun u₂ v₂ => wp_subs (op2_imm (by decide)) fun u₃ v₃ z₃ => ?_
  refine WP.block_nil ?_
  have e3 : u₃.gpr .r3 = BitVec.ofNat 32 (wipeWords - (i + 1)) := by
    rw [v₃.gpr, v₂.other _ (by decide), v₁.gpr, I.r3, VG.Proof.AesGcm.Arm.dec32 hi (by decide)]
  have hz : u₃.z = decide (i + 1 = wipeWords) := by
    rw [z₃, v₂.other _ (by decide), v₁.gpr, I.r3, VG.Proof.AesGcm.Arm.dec32 hi (by decide),
      VG.Proof.AesGcm.Arm.z_dec hi (by decide)]
  have I' : WipeI t L (i + 1) u₃ := by
    refine ⟨?_, e3, fun r h₁ h₂ => ?_, by rw [v₃.rd, v₂.rd, v₁.rd, I.rd], by rw [v₃.wr, v₂.wr, v₁.wr, I.wr],
      by rw [v₃.sp, v₂.sp, v₁.sp, I.sp], I.frame.trans ?_⟩
    · rw [v₃.other _ (by decide), v₂.gpr, dpVal, v₁.gpr, I.r12, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
        Nat.mul_succ]
    · rw [v₃.other _ h₁, v₂.other _ h₂, v₁.gpr, I.other _ h₁ h₂]
    · rw [v₃.mem, v₂.mem, v₁.mem]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
  have ev : isa.eval .ne u₃ = some !decide (i + 1 = wipeWords) := VG.Proof.AesGcm.Arm.eval_ne' hz
  by_cases he : i + 1 = wipeWords
  · left; exact ⟨by rw [ev]; simp [he], he ▸ I'⟩
  · right; exact ⟨by rw [ev]; simp [he], wipeWords - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, I'⟩

theorem saved_nodup : (Impl.Ecdsa.Rfc6979.Arm.saved.map Prod.fst).Nodup := by decide

/-- The frame below the saved registers cleared, and our caller's registers
back: the result kept. -/
theorem wipe_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa Cfg.wipe t fun t' => t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.sp = t.sp ∧
      (∀ p ∈ Impl.Ecdsa.Rfc6979.Arm.saved, t'.gpr p.1 = g p.1) ∧ t'.gpr .r0 = t.gpr .r0 ∧
      Frame [⟨L.B + BitVec.ofNat 64 24, 4 * wipeWords⟩] t.mem t'.mem := by
  have hb := hL.B_fit
  unfold Cfg.wipe
  refine WP.seq ?_
  simp only [Cfg.wipeArgs]
  refine wp_mov (op2_reg _ _) fun u₁ v₁ => wp_mov (op2_imm (by decide)) fun u₂ v₂ => wp_movw fun u₃ v₃ => ?_
  refine WP.block_nil ?_
  refine WP.seq (WP.mono (wipeLoop_ok hL (t := u₃) (by rw [v₃.wr, v₂.wr, v₁.wr, hc.wr])
    (by rw [v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr, hc.r8])
    (by rw [v₃.gpr, movw_val (by decide)])) fun u₄ I => ?_)
  refine wp_mov (op2_reg _ _) fun u₅ v₅ => ?_
  have h8 : u₄.gpr .r8 = L.fp := by
    rw [I.other _ (by decide) (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide),
      hc.r8]
  have hs : VG.Proof.Mont.Arm.Scr u₅ (L.B + BitVec.ofNat 64 24) 512 :=
    ⟨by rw [v₅.gpr, h8]; exact hL.fpA0, ⟨512, by omega_arith, by omega_arith,
      by rw [v₅.wr, I.wr, v₃.wr, v₂.wr, v₁.wr, hc.wr]; simp⟩,
      by rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith, by omega_arith⟩
  refine WP.mono (Proof.Weierstrass.Arm.ldrs_ok hs _ (fun p hp => by have := saved_off p hp; omega_arith)
    saved_nodup (by decide)) fun u₆ ⟨hm₆, K₆, hv₆⟩ => ⟨?_, ?_, ?_, fun p hp => ?_, ?_, ?_⟩
  · rw [K₆.rd, v₅.rd, I.rd, v₃.rd, v₂.rd, v₁.rd]
  · rw [K₆.wr, v₅.wr, I.wr, v₃.wr, v₂.wr, v₁.wr]
  · rw [K₆.sp, v₅.sp, I.sp, v₃.sp, v₂.sp, v₁.sp]
  · have hfr : Frame [⟨L.B + BitVec.ofNat 64 24, 4 * wipeWords⟩] t.mem u₅.mem := by
      rw [v₅.mem, ← v₁.mem, ← v₂.mem, ← v₃.mem]; exact I.frame
    rw [hv₆ p hp, VG.Proof.Mont.off, Offset.add_add,
      hfr.readW (r := ⟨L.B + BitVec.ofNat 64 492, 36⟩) (Offset.contains _ (by have := saved_off p hp; omega_arith)
        (by have := saved_off p hp; omega_arith) (by omega_arith))
        (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          have : wipeWords = 117 := rfl
          exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))
        (by decide)]
    exact hc.saved p hp
  · rw [K₆.gpr _ (by decide), v₅.other _ (by decide), I.other _ (by decide) (by decide), v₃.other _ (by decide),
      v₂.other _ (by decide), v₁.other _ (by decide)]
  · rw [hm₆, v₅.mem, ← v₁.mem, ← v₂.mem, ← v₃.mem]; exact I.frame

end VG.Proof.Ecdsa.Rfc6979.Arm

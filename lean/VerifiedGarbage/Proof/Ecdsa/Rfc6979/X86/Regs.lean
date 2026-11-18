module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Layout
public import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Loop
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86.Curve

/-! ### `Ecdsa.Rfc6979.X86.Hash`, which the modules that import this one used -/

section

/-!
# Deterministic ECDSA on x86 (32-bit): the hash function

What the proof needs of the hash function, for any one of them (`RfcHash`),
as on x86-64 (`Proof/Ecdsa/Rfc6979/X86_64/Reduce.lean`): the curve
(`RfcCurve`, with what is proven of `vg_ecdsa_<curve>_sign_k`, which each
candidate calls), the instance of the contract it implements (the curve's,
the hash function's HMAC, its output length, the bound on candidates), the
functions PBKDF2's code calls, verified (`FnsOK`: the streaming `update`, and
HMAC's `init` and `finalize`, which take their working space as an argument,
and which the table holds), the functions an indirect call of a table's
functions may reach (`f`), and the sizes the frame and `scratch` hold: the
output and block sizes of one of the hash functions of `shapes` (MD5's,
SHA-1's or the SHA-2 family's), and states and working space no larger than
SHA-512's.

The code is the same for every hash function (`cfgOf`): the proof is
written for each one, with the table's digest length `D` and block size `B`
the values the frame holds.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.Impl.Ecdsa.Rfc6979.X86

open VG.Proof.Pbkdf2.Whole.X86 (FnsOK ReprOK)

/-- The digest lengths and block sizes of the hash functions with HMAC on
x86: MD5, SHA-1, SHA-224, SHA-256, SHA-384, SHA-512, SHA-512/224 and
SHA-512/256. -/
def shapes : List (Nat × Nat) := [(16, 64), (20, 64), (28, 64), (32, 64), (48, 128), (64, 128), (28, 128), (32, 128)]

/-- A curve and a hash function, for RFC 6979 on x86. -/
structure RfcHash where
  /-- The curve. -/
  R : RfcCurve
  /-- The instance of the contract, with the hash function fixed. -/
  I : Proof.Ecdsa.Rfc6979.Instance
  /-- The functions the code calls through the table, verified. -/
  F : Impl.Pbkdf2.Whole.X86.Fns
  ok : FnsOK F
  /-- The functions an indirect call of a table's functions may reach. -/
  f : Impl.Ecdsa.Rfc6979.X86.Fns
  /-- The instance is of the curve, with this hash function's HMAC and its
  output length, and tries at least one candidate, as many as a 32-bit
  immediate holds. -/
  ecdsa : I.ecdsa = R.inst
  hash : I.hash = ok.hH.SH.H
  len : I.hashLen = F.H.D
  /-- The hash function's digests have `F.H.D` bytes. -/
  macLen : ∀ x, (ok.hH.SH.H.hash x).length = F.H.D
  tries_pos : 0 < I.tries
  tries_lt : I.tries < 2 ^ 32
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

theorem reprOK : ReprOK P.ok.hH.SH := fun m m' p q msg hb =>
  P.ok.hH.repr m m' p q msg (fun i hi => hb i (by rw [P.ok.hH.hS]; exact hi))

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
    0 < P.F.H.S ∧ 3 ≤ P.w ∧ P.w ≤ 9 ∧ 6 ≤ P.k ∧ P.k ≤ 2 * P.w ∧ 8 ≤ P.Q ∧ P.Q ≤ 66 ∧ P.Q ≤ 8 * P.w ∧
    8 * P.w < P.Q + 8 := by
  have hs := P.shape P.hDB
  have hS0 := P.ok.hH.hS0
  have hw : 8 ≤ P.Q ∧ 8 * P.w < P.Q + 8 ∧ P.Q ≤ 8 * P.w := P.R.len_words
  have hn9 := P.R.n9
  have hn3 := P.R.n3
  have hc : (P.R.E.C.len = 28 → P.R.E.n = 4) ∧ P.Q ≤ 66 := by
    cases hb : P.R.big
    · have := P.R.sizesA hb; simp only [Q]; omega_using [this]
    · have := P.R.sizesW hb; simp only [Q]; omega_using [this]
  refine ⟨P.hS, P.hWi, P.hWf, P.hWb, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2, hS0, hn3, hn9,
    (by simp only [k]; split <;> omega_arith), (by simp only [k, w]; omega_using []), hw.1, hc.2, hw.2.2, hw.2.1⟩

/-- Unless `big`, the scalars are `Q = 4 k` bytes, in at most sixteen 32-bit words. -/
theorem sizesA (h : P.R.big = false) : P.Q = 4 * P.k ∧ P.k ≤ 16 ∧ P.Q ≤ 64 := by
  have := P.R.sizesA h
  rcases this.1 with h' | h' | h' | h' <;> simp only [Q, k] <;> split <;> omega_arith

/-- If `big`, P-521's sizes, longer than any digest. -/
theorem sizesW (h : P.R.big = true) : P.w = 9 ∧ P.k = 18 ∧ P.Q = 66 ∧ P.F.H.D < P.Q := by
  have h₁ := P.R.sizesW h
  have h₂ := (P.shape P.hDB).2.1
  exact ⟨h₁.1, by simp only [k, h₁.1, h₁.2.1]; decide, h₁.2.1, by simp only [Q]; omega_using [h₁, h₂]⟩

/-- The curve's scalars are `Q` bytes. -/
theorem curveLen : P.I.ecdsa.curve.len = P.Q := by rw [P.ecdsa, P.R.curve]

end RfcHash

/-- Facts about the sizes of the hash function `‹RfcHash›`'s states, working
space, block and output, and the arithmetic they decide. -/
tactic_template "nums" : tactic => `(tactic| first | omega |
  (obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := RfcHash.sizes ‹RfcHash›; omega))

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

end VG.Proof.Ecdsa.Rfc6979.X86

end

end

/-!
# Deterministic ECDSA on x86 (32-bit): addresses and registers

Our arguments as the code loads them (`argM`), the code that sets one
register to an address in `scratch` or the frame or to a constant (`Upd`),
and the bytes of a region a frame of writes misses.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Ecdsa.Rfc6979.X86
open VG.Proof.Mont.X86 (wp_movS)

/-- The bytes of a region a frame of writes misses. -/
theorem bytesAt_frame {ws : List Region} {m m' : Mem} (hf : Frame ws m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ ws, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) :
    Spec.Sha256.bytesAt m' p n = Spec.Sha256.bytesAt m p n := by
  simp only [Spec.Sha256.bytesAt]
  exact List.map_congr_left fun i hi => Frame.bytes (R := ⟨p, n⟩) hf hd hn (List.mem_range.mp hi)

theorem sub_refl (r : Region) : Region.Sub r r := fun _ h => h

theorem sub_trans {a b c : Region} (h₁ : Region.Sub a b) (h₂ : Region.Sub b c) : Region.Sub a c :=
  fun x hx => h₂ x (h₁ x hx)

theorem Lay.Ok.low_scr {dn : Nat} {L : Lay dn} (h : L.Ok) {e k : Nat} (h₂ : e + k ≤ 8192) :
    Region.Disjoint ⟨L.B, 76⟩ ⟨L.scr + BitVec.ofNat 64 e, k⟩ :=
  (h.kc.sub_left (Region.sub_prefix (by omega_using []))).sub_right (Offset.sub_base _ h₂)

variable {dn : Nat} {L : Lay dn} {g : Reg → BitVec 32} {m₀ : Mem}

theorem argM_eq (i : Nat) : argM i = .mem ⟨.esp, 516 + 4 * i⟩ := by
  simp only [argM, Impl.Ecdsa.Rfc6979.X86.frameBytes, stk]

/-- `argM i` reads our argument `i`. -/
theorem Ctx.readArg {u : State} (hL : L.Ok) (hc : Ctx L g m₀ u) {i : Nat} (hi : i < 6) :
    readSrc u (argM i) = some (L.a i) := by
  have e : addr L.F (516 + 4 * i) = L.B + BitVec.ofNat 64 (592 + 4 * i) := by
    rw [hL.addrF (by omega_using [hi]), show 76 + (516 + 4 * i) = 592 + 4 * i by omega_using []]
  rw [argM_eq, readSrc_mem hc.esp (by rw [e]; exact hc.inArgs hi hL), e, hc.pArg i hi]

/-! ## Code that sets one register -/

/-- `u'` is `u` with only the register `d` (not `esp`, and the flags)
changed, to `v`. -/
structure Upd {dn : Nat} (L : Lay dn) (g : Reg → BitVec 32) (m₀ : Mem) (u : State) (d : Reg) (v : BitVec 32)
    (u' : State) : Prop where
  ctx : Ctx L g m₀ u'
  mem : u'.mem = u.mem
  val : u'.gpr d = v
  keep : ∀ r, r ≠ d → u'.gpr r = u.gpr r
  syms : u'.syms = u.syms

theorem Ctx.set (hL : L.Ok) {u u' : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ≠ .esp)
    (hrd : u'.rd = u.rd) (hwr : u'.wr = u.wr) (hm : u'.mem = u.mem) (hk : ∀ r, r ≠ d → u'.gpr r = u.gpr r) (hsy : u'.syms = u.syms) :
    Ctx L g m₀ u' :=
  hc.regs hL hrd hwr hm (hk .esp (Ne.symm hd)) hsy

theorem Upd.of_wp {u u' : State} {d : Reg} {v : BitVec 32} (hL : L.Ok) (hc : Ctx L g m₀ u) (hd : d ≠ .esp)
    (h : VG.X86.Wp.Upd u u' d v) : Upd L g m₀ u d v u' :=
  ⟨hc.set hL hd h.rd h.wr h.mem h.other h.syms, h.mem, h.gpr, h.other, h.syms⟩

theorem Upd.trans {u u' u'' : State} {d : Reg} {v w : BitVec 32} (hL : L.Ok) (hd : d ≠ .esp)
    (h₁ : VG.X86.Wp.Upd u u' d v) (h₂ : VG.X86.Wp.Upd u' u'' d w) (hc : Ctx L g m₀ u) :
    Upd L g m₀ u d w u'' :=
  ⟨hc.set hL hd (h₂.rd.trans h₁.rd) (h₂.wr.trans h₁.wr) (h₂.mem.trans h₁.mem)
      (fun r hr => (h₂.other r hr).trans (h₁.other r hr)) (h₂.syms.trans h₁.syms),
    h₂.mem.trans h₁.mem, h₂.gpr, fun r hr => (h₂.other r hr).trans (h₁.other r hr), h₂.syms.trans h₁.syms⟩

/-- `d ← scratch + a`. -/
theorem scr_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ≠ .esp) (a : Nat) :
    WP isa (.block (Cfg.scr d a)) u (Upd L g m₀ u d (L.sc + BitVec.ofNat 32 a)) := by
  refine wp_movS (hc.readArg hL (i := 4) (by omega_using [])) fun _ v₁ _ => wp_addi fun u₂ v₂ => WP.block_nil ?_
  rw [v₁.gpr] at v₂
  exact Upd.trans hL hd v₁ v₂ hc

/-- `d ← esp + o`, an address in the frame. -/
theorem fr_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ≠ .esp) (o : Nat) :
    WP isa (.block (Cfg.fr d o)) u (Upd L g m₀ u d (L.F + BitVec.ofNat 32 o)) := by
  refine wp_mov fun _ v₁ => wp_addi fun u₂ v₂ => WP.block_nil ?_
  rw [v₁.gpr, hc.esp] at v₂
  exact Upd.trans hL hd v₁ v₂ hc

/-- `d ← v`. -/
theorem movi_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ≠ .esp) (v : BitVec 32) :
    WP isa (.block [.mov d (.imm v)]) u (Upd L g m₀ u d v) :=
  wp_movi fun _ v₁ => WP.block_nil (Upd.of_wp hL hc hd v₁)

/-- `d ← argument i`. -/
theorem arg_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {d : Reg} (hd : d ≠ .esp) {i : Nat} (hi : i < 6) :
    WP isa (.block [.mov d (argM i)]) u (Upd L g m₀ u d (L.a i)) :=
  wp_movS (hc.readArg hL hi) fun _ v₁ _ => WP.block_nil (Upd.of_wp hL hc hd v₁)

end VG.Proof.Ecdsa.Rfc6979.X86

module

import VerifiedGarbage.Proof.X25519.X86_64.Step
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Weierstrass.BytesLen
public import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.Bytes
public import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Syms
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Regs
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hash
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Core
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PbkLoop
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Curve
public import VerifiedGarbage.Proof.RsaOaep.X86_64.MgfT
public import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Hmac
public import VerifiedGarbage.TCB.Mem
public import VerifiedGarbage.TCB.X86_64.Target

/-! ### `Ecdsa.Rfc6979.X86_64.Hash`, which this module and modules that import it used -/

section

/-!
# Deterministic ECDSA on x86-64: the hash function

What the proof needs of the hash function, for any one of them (`RfcHash`):
the curve (`RfcCurve`, with what is proven of `vg_ecdsa_<curve>_sign_k`,
which each candidate calls), the instance of the contract it implements (the
curve's, the hash function's HMAC, its output length, the bound on
candidates), its code and what the proofs of HMAC's functions know of it
(`Hash`, `HashOK`, `CoreOK`, `Callees`: HMAC's `init` and `finalize` and the
streaming `update`, which the table holds), the functions an indirect call
of a table's functions may reach (`f`, of which the table's are, `TabOK`, a
fact of the state), and the sizes the frame and `scratch` hold: the output
and block sizes of one of the hash functions of `shapes` (MD5's, SHA-1's or
the SHA-2 family's), and states and working space no larger than SHA-512's.

The code is the same for every hash function (`cfgOf`): the proof is
written for each one, with the table's digest length `D` and block size `B`
the values the frame holds.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK CoreOK Callees core hmacInit_ok hmacFin_ok core_hmacInit core_hmacFin
  core_hmacInit_depth core_hmacFin_depth nosp_of)
open VG.Proof.Pbkdf2.Md.X86_64.Calls (initG finG)
open VG.Impl.Mgf1.X86_64.Table (Fns)

/-- The digest lengths and block sizes of the hash functions with HMAC on
x86-64: MD5, SHA-1, SHA-224, SHA-256, SHA-384, SHA-512, SHA-512/224 and
SHA-512/256. -/
def shapes : List (Nat × Nat) := [(16, 64), (20, 64), (28, 64), (32, 64), (48, 128), (64, 128), (28, 128), (32, 128)]

/-- A curve and a hash function, for RFC 6979 on x86-64. -/
structure RfcHash where
  /-- The curve. -/
  R : RfcCurve
  /-- The instance of the contract, with the hash function fixed. -/
  I : Proof.Ecdsa.Rfc6979.Instance
  /-- The hash function's code. -/
  H : Impl.Pbkdf2.Md.X86_64.Hash
  ok : HashOK H
  C : CoreOK (core H)
  K : Callees H
  satI : ∃ s, (Proof.Hmac.initScratchContract ok.SH H.W X86_64.abi 16).pre s
  satF : ∃ s, (Proof.Hmac.finalizeScratchContract ok.SH H.W X86_64.abi 16).pre s
  /-- The functions an indirect call of a table's functions may reach. -/
  f : Fns
  /-- The instance is of the curve, with this hash function's HMAC and its
  output length, and tries at least one candidate, as many as a 32-bit
  immediate holds. -/
  ecdsa : I.ecdsa = R.inst
  hash : I.hash = ok.SH.H
  len : I.hashLen = H.D
  tries_pos : 0 < I.tries
  tries_lt : I.tries < 2 ^ 32
  /-- The sizes the frame and `scratch` hold. -/
  hDB : (H.D, H.P.B) ∈ shapes
  hS : H.S ≤ 192
  hW : 8 * H.W ≤ 1872
  hWb : ok.stream.Wb ≤ 1872

namespace RfcHash

variable (P : RfcHash)

/-- HMAC with the hash function. -/
abbrev mac (K text : List Byte) : List Byte := Spec.Hmac.hmac P.ok.SH.H K text

theorem hI : Verified X86_64.target P.H.hmacInit (initG P.ok.SH P.H.W) := hmacInit_ok P.ok P.C P.K P.satI

theorem hIsp : NoSp P.H.hmacInit := nosp_of (core_hmacInit P.K.iNs P.K.b.bNs P.C.hinitNs)

theorem hId : P.H.hmacInit.depth ≤ 2 := core_hmacInit_depth P.K.iD P.K.b.bD P.C.hinitD

theorem hF : Verified X86_64.target P.H.hmacFin (finG P.ok.SH P.H.W) := hmacFin_ok P.ok P.C P.K P.satF

theorem hFsp : NoSp P.H.hmacFin := nosp_of (core_hmacFin P.K.cNs P.C.hfinNs)

theorem hFd : P.H.hmacFin.depth ≤ 2 := core_hmacFin_depth P.K.cD P.C.hfinD

/-- The words of the curve's scalars. -/
abbrev w : Nat := P.R.E.n

/-- The bytes of the curve's scalars. -/
abbrev Q : Nat := P.R.E.C.len

theorem shape (h : (P.H.D, P.H.P.B) ∈ shapes) :
    16 ≤ P.H.D ∧ P.H.D ≤ 64 ∧ P.H.D % 4 = 0 ∧ P.H.D < P.H.P.B ∧ P.H.P.B ≤ 128 ∧ 64 ≤ P.H.P.B := by
  simp only [shapes, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ <;> omega_using [h, h']

/-- The sizes, as the proofs use them. -/
theorem sizes : P.H.S ≤ 192 ∧ P.H.P.N + P.H.P.B ≤ 192 ∧ 8 * P.H.W ≤ 1872 ∧ P.ok.stream.Wb ≤ 1872 ∧
    P.H.stream.S ≤ 192 ∧ P.H.stream.D = P.H.D ∧ 16 ≤ P.H.D ∧ P.H.D ≤ 64 ∧ P.H.D % 4 = 0 ∧
    P.H.D < P.H.P.B ∧ P.H.P.B ≤ 128 ∧ 64 ≤ P.H.P.B ∧ 4 ≤ P.w ∧ P.w ≤ 9 ∧ 8 ≤ P.Q ∧ P.Q ≤ 66 ∧
    P.Q ≤ 8 * P.w ∧ 8 * P.w ≤ P.Q + 8 := by
  have hw : 8 ≤ P.Q ∧ 8 * P.w ≤ P.Q + 8 ∧ P.Q ≤ 8 * P.w := P.R.len_words
  have hn9 := P.R.n9
  have hs := P.shape P.hDB
  have hQ : P.Q ≤ 66 := by
    cases hb : P.R.big
    · have := P.R.sizesA hb; simp only [Q]; omega_using [this]
    · have := P.R.sizesW hb; simp only [Q]; omega_using [this]
  refine ⟨P.hS, P.hS, P.hW, P.hWb, P.hS, rfl, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2,
    P.R.n4, hn9, hw.1, hQ, hw.2.2, hw.2.1⟩

/-- Unless `big`, the scalars are `8 w` bytes (or 24 or 28 in 4 words), at most 8 words. -/
theorem sizesA (h : P.R.big = false) : (P.Q = 8 * P.w ∨ P.w = 4 ∧ (P.Q = 28 ∨ P.Q = 24)) ∧ P.w ≤ 8 ∧ P.Q ≤ 64 := by
  have := P.R.sizesA h
  rcases this.1 with h' | h' | h' <;> simp only [Q, w] <;> omega_using [this]

/-- If `big`, P-521's sizes, longer than any digest. -/
theorem sizesW (h : P.R.big = true) : P.w = 9 ∧ P.Q = 66 ∧ P.H.D < P.Q := by
  have h₁ := P.R.sizesW h
  have h₂ := P.sizes.2.2.2.2.2.2.2.1
  exact ⟨h₁.1, h₁.2.1, by simp only [Q]; omega_using [h₁, h₂]⟩

/-- The curve's scalars are `Q` bytes. -/
theorem curveLen : P.I.ecdsa.curve.len = P.Q := by rw [P.ecdsa, P.R.curve]

end RfcHash

/-- Facts about the sizes of the hash function `‹RfcHash›`'s states, working
space, block and output, and the arithmetic they decide. -/
macro "nums" : tactic => `(tactic| first | omega |
  (obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := RfcHash.sizes ‹RfcHash›; omega))

/-- The code, for the curve of `P` and the functions an indirect call may reach. -/
def cfgOf (P : RfcHash) : Cfg where
  f := P.f
  w := P.R.E.n
  len := P.R.E.C.len
  big := P.R.big
  sh := P.R.sh
  n := P.R.E.C.n
  tries := P.I.tries
  coreN := P.R.coreN
  coreC := P.R.coreC

end VG.Proof.Ecdsa.Rfc6979.X86_64

end

end

/-!
# Deterministic ECDSA on x86-64: `h = bits2octets(digest)`

`X`'s `Q` bytes (in the frame at `xa`: the digest's leftmost bytes, or the
digest after zero bytes, `Prep.lean`), a word at a time from the least
significant (a top word of four bytes, if `Q = 8 w - 4`, by a 32-bit load:
`loadWord_ok`): each to `V`'s place, and it minus the word of `n` (with the
borrow of the words before) to `K`'s (`subs_ok`); then, by the mask of the
last borrow, the number's words or the difference's, big-endian to the `Q`
bytes at `h` (`sels_ok`, at `hB`), the top word's zero bytes below them.
The number is below `2^(8 Q) < 2n`, so this is it modulo `n` (`mod_mathK`,
`reduce_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Proof.X25519.X86_64 (sub_borrow sbb_borrow)
open VG.Proof.Mont (word wordsVal wordsVal_lt wordsVal_succ_top Outside off ofs writeW_outside)

theorem sel_mask (x d : BitVec 64) (y : BitVec 64) (c : Bool) :
    ((x ^^^ d) &&& (y - y - (BitVec.ofBool c).setWidth 64)) ^^^ d = if c then x else d := by
  cases c
  · simp
  · have : y - y - (BitVec.ofBool true).setWidth 64 = BitVec.allOnes 64 := by simp
    rw [this, BitVec.and_allOnes, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    simp

/-- The low `k + 1` words of `n`: its low `k`, and word `k`. -/
theorem n_split (n k : Nat) :
    n % 2 ^ (64 * (k + 1)) = n % 2 ^ (64 * k) + 2 ^ (64 * k) * (BitVec.ofNat 64 (n >>> (64 * k))).toNat := by
  rw [show 64 * (k + 1) = 64 * k + 64 by omega_using [], Nat.pow_add, Nat.mod_mul, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]

theorem frame_of_outside {base : Addr} {d n : Nat} {m m' : Mem} (h : Outside base d n m m')
    (hn : d + n ≤ 2 ^ 64) : Frame [⟨base + BitVec.ofNat 64 d, n⟩] m m' := fun x hx => h x (by
  obtain h₁ := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at h₁
  obtain h₂ := Offset.lt_iff x base hn
  simp only [ofs]
  omega_using [h₁, h₂])

variable {P : RfcHash} {dn : Nat} {L : Lay dn} {g : Reg → BitVec 64} {m₀ : Mem}

/-- Where `X` is, in the frame: `rsp + fX`. -/
abbrev xa {dn : Nat} (L : Lay dn) : Addr := L.B + BitVec.ofNat 64 (24 + fX)

/-- Where `h` is, from the stack's lowest byte: `rsp + fH`. -/
abbrev hB : Nat := 24 + fH


/-- Word `j` of the number at `X`, least significant first: a top word of
four bytes is zero-extended. -/
def xw (P : RfcHash) (L : Lay dn) (m : Mem) (j : Nat) : BitVec 64 :=
  if 8 * (j + 1) ≤ P.Q then bswap64 (m.readW (xa L + BitVec.ofNat 64 (P.Q - 8 * (j + 1))) 64)
  else if P.Q ≤ 8 * j then 0
  else (bswap32 (m.readW (xa L) 32)).setWidth 64

theorem cat8_shr (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 : BitVec 64) >>> 32 =
      (b0 ++ b1 ++ b2 ++ b3 : BitVec 32).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  obtain h0 := b0.isLt; have h1 := b1.isLt; have h2 := b2.isLt; have h3 := b3.isLt
  obtain h4 := b4.isLt; have h5 := b5.isLt; have h6 := b6.isLt; have h7 := b7.isLt
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_append]
  simp only [← Nat.shiftLeft_add_eq_or_of_lt h1, ← Nat.shiftLeft_add_eq_or_of_lt h2,
    ← Nat.shiftLeft_add_eq_or_of_lt h3, ← Nat.shiftLeft_add_eq_or_of_lt h4, ← Nat.shiftLeft_add_eq_or_of_lt h5,
    ← Nat.shiftLeft_add_eq_or_of_lt h6, ← Nat.shiftLeft_add_eq_or_of_lt h7]
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega_using []

/-- The first four bytes at `a`, big-endian: the eight bytes', shifted right. -/
theorem bswap32_readW (m : Mem) (a : Addr) :
    (bswap32 (m.readW a 32)).setWidth 64 = byteRev64 (m.readW a 64) >>> 32 := by
  rw [show bswap32 (m.readW a 32) = byteRev32 (m.readW a 32) from rfl, byteRev32_readW, byteRev64_readW,
    cat8_shr]

/-- The words, as `loadBytes` reads them (`Proof.Weierstrass.X86_64.ldWord`). -/
theorem xw_eq (P : RfcHash) (L : Lay dn) (m : Mem) {j : Nat} (h : 8 * (j + 1) ≤ P.Q ∨ 8 * (j + 1) = P.Q + 4 ∨ 8 * (j + 1) = P.Q + 8) :
    xw P L m j = if 8 * (j + 1) ≤ P.Q then byteRev64 (m.readW (xa L + BitVec.ofNat 64 (P.Q - 8 * (j + 1))) 64)
      else byteRev64 (m.readW (xa L) 64) >>> (8 * (8 * (j + 1) - P.Q)) := by
  unfold xw
  split
  · rfl
  · split
    · rw [BitVec.ushiftRight_eq_zero (by omega_arith)]; rfl
    · rw [bswap32_readW, show 8 * (8 * (j + 1) - P.Q) = 32 by omega_arith]

/-- Only `rax`, `rcx` and `rdx` (and the flags and memory) changed since `t`. -/
structure RK (t u : State) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  gpr : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → u.gpr r = t.gpr r

theorem RK.refl (t : State) : RK t t := ⟨rfl, rfl, fun _ _ _ _ => rfl⟩

theorem RK.trans {t u v : State} (h₁ : RK t u) (h₂ : RK u v) : RK t v :=
  ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, fun r a b c => (h₂.gpr r a b c).trans (h₁.gpr r a b c)⟩

/-! ## The subtraction -/

/-- Word `j` of the number at `digest`, in `rax`, the flags kept. -/
theorem loadWord_ok (hA : P.R.big = false) {t : State} (hc : Ctx L g m₀ t) (hsi : t.gpr .rsi = xa L)
    {u : State} (hk : RK t u) {j : Nat} (_hj : j < P.w) :
    WP isa (.block ((cfgOf P).loadWord j)) u fun u' => RK u u' ∧ u'.mem = u.mem ∧ u'.cf = u.cf ∧
      u'.gpr .rax = xw P L u.mem j := by
  obtain ⟨hQ, h6, -⟩ := P.sizesA hA
  have he := L.he
  obtain hrsi : u.gpr .rsi = xa L := by rw [hk.gpr _ (by decide) (by decide) (by decide), hsi]
  apply WP.of_runBlock
  by_cases h : 8 * (j + 1) ≤ P.Q
  · have hr : InRegions (u.rd ++ u.wr) (xa L + BitVec.ofNat 64 (P.Q - 8 * (j + 1))) 8 := by
      rw [hk.rd, hk.wr, xa, Offset.add_add]; exact hc.inFr (by simp only [fX]; omega_using [])
        (by simp only [fX]; omega_using [hQ, h6, h, he])
    have h' : 8 * (j + 1) ≤ (cfgOf P).len := h
    rw [Cfg.loadWord, ite_eq_left_of_eq_true _ _ (eq_true h'), show (cfgOf P).len = P.Q from rfl]
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      State.load64, ea_at, hrsi, hr, ite_true, Option.map_some, RegUpd.gpr_setReg,
      RegUpd.mem_setReg, RegUpd.cf_setReg, Option.some.injEq, exists_eq_left']
    refine ⟨⟨by triv, by triv, fun r h₁ _ _ => ?_⟩, by triv, by triv, ?_⟩
    · simp only [RegUpd.gpr_setReg, h₁, ite_false]
    · simp only [xw, h, ite_true]
  · by_cases hz : P.Q ≤ 8 * j
    · rw [Cfg.loadWord, ite_eq_right_of_eq_false _ _ (eq_false (show ¬ 8 * (j + 1) ≤ (cfgOf P).len from h)),
        ite_eq_left_of_eq_true _ _ (eq_true (show (cfgOf P).len ≤ 8 * j from hz))]
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
        RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.cf_setReg, Option.some.injEq, exists_eq_left']
      refine ⟨⟨rfl, rfl, fun r hr _ _ => ?_⟩, trivial, trivial, ?_⟩
      · simp only [RegUpd.gpr_setReg, hr, ite_false]
      · simp [xw, h, hz]
    · have hr : InRegions (u.rd ++ u.wr) (xa L + BitVec.ofNat 64 0) 4 := by
        rw [hk.rd, hk.wr, xa, Offset.add_add]
        obtain ⟨r, hr, hcr⟩ := hc.inFrW (d := 24 + fX + 0) (n := 4) (by simp only [fX]; omega_using [])
          (by simp only [fX]; omega_using [he])
        exact ⟨r, List.mem_append_right _ hr, hcr⟩
      have h' : ¬ 8 * (j + 1) ≤ (cfgOf P).len := h
      rw [Cfg.loadWord, ite_eq_right_of_eq_false _ _ (eq_false h'),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ (cfgOf P).len ≤ 8 * j from hz))]
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32,
        State.load32, State.setReg32, ea_at, hrsi, hr, ite_true, Option.map_some, RegUpd.gpr_setReg,
        RegUpd.mem_setReg, RegUpd.cf_setReg, Option.some.injEq, exists_eq_left']
      refine ⟨⟨by triv, by triv, fun r h₁ _ _ => ?_⟩, by triv, by triv, ?_⟩
      · simp only [RegUpd.gpr_setReg, h₁, ite_false]
      · simp only [xw, h, hz, ite_false, add_ofNat_zero, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
          BitVec.setWidth_eq]

/-- Word `j`: of the number to `V`'s place, of the difference to `K`'s. -/
theorem subWord_ok (hA : P.R.big = false) {t : State} (hc : Ctx L g m₀ t) (hsi : t.gpr .rsi = xa L)
    {u : State} (hk : RK t u) {j : Nat} (hj : j < P.w) {c : Bool}
    (hcf : j = 0 ∨ u.cf = some c) :
    WP isa (.block ((cfgOf P).subWord j)) u fun u' => RK u u' ∧
      u'.mem = (u.mem.writeW (off L.B (88 + 8 * j)) (xw P L u.mem j)).writeW (off L.B (24 + 8 * j))
        (xw P L u.mem j - (cfgOf P).nWord j - (BitVec.ofBool (j != 0 && c)).setWidth 64) ∧
      u'.cf = some (decide ((xw P L u.mem j).toNat < ((cfgOf P).nWord j).toNat + (j != 0 && c).toNat)) := by
  obtain h6 : P.w ≤ 8 := (P.sizesA hA).2.1
  rw [Cfg.subWord, WP.block_append_iff]
  refine WP.mono (loadWord_ok hA hc hsi hk hj) fun u₁ ⟨k₁, m₁, cf₁, ax₁⟩ => ?_
  obtain hk₁ := hk.trans k₁
  obtain hrsp : u₁.gpr .rsp = L.B + BitVec.ofNat 64 24 := by
    rw [hk₁.gpr _ (by decide) (by decide) (by decide), hc.rsp]
  obtain hV : InRegions u₁.wr (L.B + BitVec.ofNat 64 (88 + 8 * j)) 8 := by
    rw [hk₁.wr]; exact hc.inFrW (by omega_using []) (by omega_using [hj, h6])
  obtain hK : InRegions u₁.wr (L.B + BitVec.ofNat 64 (24 + 8 * j)) 8 := by
    rw [hk₁.wr]; exact hc.inFrW (by omega_using []) (by omega_using [hj, h6])
  obtain e88 : 24 + (64 + 8 * j) = 88 + 8 * j := by omega_using []
  rw [← m₁] at ax₁ ⊢
  apply WP.of_runBlock
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp only [fV, fK, ite_true, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      readSrc, State.store64, ea_stk, hrsp, ax₁, Offset.add_add, e88,
      RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.gpr_arithFlags,
      RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.cf_setReg, RegUpd.cf_arithFlags,
      Option.bind_some, reduceCtorEq, ite_false, hV, hK, Nat.mul_zero, Nat.add_zero,
      Option.some.injEq, exists_eq_left']
    have hb : (0 != 0 && c) = false := rfl
    refine ⟨⟨k₁.rd, k₁.wr, fun r h₁ h₂ h₃ => ?_⟩, ?_, ?_⟩
    · simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h₁, h₃, ite_false]; exact k₁.gpr r h₁ h₂ h₃
    · have h0 : ∀ a : BitVec 64, a - (BitVec.ofBool false).setWidth 64 = a := fun a => by simp
      rw [hb, h0]
    · simp only [hb, Bool.toNat_false, Nat.add_zero]
  · have hcf' : u₁.cf = some c := cf₁.trans (hcf.resolve_left (by omega_using [hj0]))
    obtain hj' : j ≠ 0 := by omega_using [hj0]
    simp only [fV, fK, hj', ite_false, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      readSrc, State.store64, ea_stk, hrsp, ax₁, Offset.add_add, e88, Nat.zero_add,
      RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.gpr_arithFlags,
      RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.cf_setReg, RegUpd.cf_arithFlags,
      hcf', Option.map_some, Option.bind_some, reduceCtorEq, hV, hK, ite_true, Option.some.injEq,
      exists_eq_left']
    obtain hb : (j != 0 && c) = c := by simp [hj']
    refine ⟨⟨k₁.rd, k₁.wr, fun r h₁ h₂ h₃ => ?_⟩, ?_, ?_⟩
    · simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h₁, h₃, ite_false]; exact k₁.gpr r h₁ h₂ h₃
    · rw [hb]
    · simp only [hb]

/-- `X` is apart from `K` and `V`, so code that writes only there keeps its words. -/
theorem x_kept {m m' : Mem} {n : Nat} (h : Outside L.B 24 n m m') (hn : 24 + n ≤ 240) {d : Nat}
    (hd : d + 8 ≤ 72) : m'.readW (xa L + BitVec.ofNat 64 d) 64 = m.readW (xa L + BitVec.ofNat 64 d) 64 :=
  Proof.Weierstrass.readW_keep fun i hi =>
    Proof.Weierstrass.keep_of_disjoint (k := 72) h (Offset.disjoint _ (by simp only [fX]; omega_using [hn])
      (by simp only [fX]; omega_using []) (by omega_using [hn])) (by omega_using [hn])
      (by omega_using [hd, hi]) (by omega_using [])

/-- The words of the number at `X`, kept by code that writes only `K` and `V`. -/
theorem xw_kept {m m' : Mem} {n : Nat} (h : Outside L.B 24 n m m') (hn : 24 + n ≤ 240)
    (h8 : 8 ≤ P.Q) (hQ : P.Q ≤ 72) (j : Nat) : xw P L m' j = xw P L m j := by
  unfold xw
  split
  · rw [x_kept h hn (by omega_arith)]
  · split
    · rfl
    · refine congrArg (fun x => (bswap32 x).setWidth 64) (Mem.readW_congr fun i hi => ?_)
      obtain e := Proof.Weierstrass.keep_of_disjoint (k := 72) (p := xa L) h (Offset.disjoint _
        (by simp only [fX]; omega_using [hn]) (by simp only [fX]; omega_using []) (by omega_using [hn]))
        (by omega_using [hn]) (i := i) (by omega_using [hi]) (by omega_using [])
      exact e

/-- One more word of a subtraction with borrow: the words below `k` (`hs`)
and word `k` (`e`), weighted by `Q = 2^(64 k)`. -/
private theorem borrow_step {a b r x y z c d Q : Nat} (hs : a + r = b + Q * c)
    (e : x + y + c = z + 2 ^ 64 * d) : a + Q * x + (r + Q * y) = b + Q * z + 2 ^ 64 * Q * d := by
  grind

/-- After `k` words: the number's in `V`'s place, and the difference in
`K`'s with the borrow. -/
theorem subs_ok (hA : P.R.big = false) {t : State} (hc : Ctx L g m₀ t) (hL : L.Ok) (hsi : t.gpr .rsi = xa L) :
    ∀ k ≤ P.w, WP isa (.block ((List.range k).flatMap (cfgOf P).subWord)) t fun u =>
      RK t u ∧ Outside L.B 24 128 t.mem u.mem ∧ (∀ j < k, word u.mem L.B (88 + 8 * j) = xw P L t.mem j) ∧
      ∃ c : Bool, (k = 0 → c = false) ∧ (0 < k → u.cf = some c) ∧
        wordsVal u.mem L.B 24 k + P.R.E.C.n % 2 ^ (64 * k) = wordsVal u.mem L.B 88 k + 2 ^ (64 * k) * c.toNat
  | 0, _ => WP.block_nil ⟨RK.refl _, Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      false, fun _ => rfl, fun h => absurd h (Nat.lt_irrefl _), by simp [wordsVal, Nat.mod_one]⟩
  | k + 1, hk => by
    obtain h6 : P.w ≤ 8 := (P.sizesA hA).2.1
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (subs_ok hA hc hL hsi k (by omega_using [hk])) fun u₁ ⟨k₁, O₁, e₁, c, hc0, hcf, hs⟩ => ?_
    refine WP.mono (subWord_ok (P := P) hA hc hsi k₁ (j := k) (by omega_using [hk]) (c := c)
      (by rcases Nat.eq_zero_or_pos k with h | h; exacts [.inl h, .inr (hcf h)])) fun u₂ ⟨k₂, m₂, cf₂⟩ => ?_
    obtain hx : xw P L u₁.mem k = xw P L t.mem k :=
      xw_kept O₁ (by omega_using []) P.R.len_words.1 (by have := P.sizes; omega_arith) k
    obtain hb : (k != 0 && c) = c := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h; rw [hc0 rfl]; rfl
      · simp [show k ≠ 0 by omega_using [h]]
    rw [hx, hb] at m₂ cf₂
    -- Each write is outside the other's word, and outside the words below `k`.
    obtain oK : Outside L.B (24 + 8 * k) 8 _ _ := writeW_outside (u₁.mem.writeW (off L.B (88 + 8 * k)) (xw P L t.mem k))
      L.B (xw P L t.mem k - (cfgOf P).nWord k - (BitVec.ofBool c).setWidth 64) (d := 24 + 8 * k) (by omega_using [hk, h6])
    obtain oV : Outside L.B (88 + 8 * k) 8 _ _ := writeW_outside u₁.mem L.B (xw P L t.mem k) (d := 88 + 8 * k)
      (by omega_using [hk, h6])
    rw [← m₂] at oK
    obtain wK : ∀ d, d + 8 ≤ 24 + 8 * k ∨ 24 + 8 * k + 8 ≤ d → d + 8 ≤ 2 ^ 64 →
        d + 8 ≤ 88 + 8 * k ∨ 88 + 8 * k + 8 ≤ d → word u₂.mem L.B d = word u₁.mem L.B d := fun d h₁ h₂ h₃ => by
      rw [Proof.Mont.Outside.word oK h₁ h₂, Proof.Mont.Outside.word oV h₃ h₂]
    obtain wsK : wordsVal u₂.mem L.B 24 k = wordsVal u₁.mem L.B 24 k := by
      rw [Proof.Mont.Outside.wordsVal oK (.inl (by omega_using [])) (by omega_using [hk, h6]),
        Proof.Mont.Outside.wordsVal oV (.inl (by omega_using [])) (by omega_using [hk, h6])]
    obtain wsV : wordsVal u₂.mem L.B 88 k = wordsVal u₁.mem L.B 88 k := by
      rw [Proof.Mont.Outside.wordsVal oK (.inr (by omega_using [hk, h6])) (by omega_using [hk, h6]),
        Proof.Mont.Outside.wordsVal oV (.inl (by omega_using [])) (by omega_using [hk, h6])]
    obtain hV : word u₂.mem L.B (88 + 8 * k) = xw P L t.mem k := by
      rw [Proof.Mont.Outside.word oK (.inr (by omega_using [])) (by omega_using [hk, h6]), Proof.Mont.word_writeW_self]
    obtain hK : word u₂.mem L.B (24 + 8 * k) =
        xw P L t.mem k - (cfgOf P).nWord k - (BitVec.ofBool c).setWidth 64 := by
      rw [m₂, Proof.Mont.word_writeW_self]
    refine ⟨k₁.trans k₂, O₁.trans ?_, fun j hj => ?_, _, fun h => absurd h (by omega_using []), fun _ => cf₂, ?_⟩
    · rw [m₂]
      exact ((writeW_outside _ _ _ (by omega_using [hk, h6])).mono (by omega_using []) (by omega_using [hk, h6])).trans
        ((writeW_outside _ _ _ (by omega_using [hk, h6])).mono (by omega_using []) (by omega_using [hk, h6]))
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [wK _ (.inr (by omega_using [hk, h6])) (by omega_arith) (.inl (by omega_arith)), e₁ j hj]
      · exact hV
    · rw [wordsVal_succ_top, wordsVal_succ_top, wsK, wsV, hK, hV, n_split]
      obtain e := sbb_borrow (xw P L t.mem k) ((cfgOf P).nWord k) c
      have hn : (cfgOf P).nWord k = BitVec.ofNat 64 (P.R.E.C.n >>> (64 * k)) := rfl
      rw [hn] at e ⊢
      rw [Proof.Mont.pow64_succ]
      generalize 2 ^ (64 * k) = Q at *
      exact borrow_step hs e

/-! ## The selection -/

/-- Where `h`'s `8 w` bytes are (from `hB + Q - 8 w`, its top word's zero
bytes first): above `K` and `V`, in the frame above its pointers and the
slots of `D` and `B`. -/
theorem hb_facts (hA : P.R.big = false) :
    88 + 8 * P.w ≤ hB + P.Q - 8 * P.w ∧ 8 * P.w ≤ hB + P.Q ∧ hB + P.Q ≤ 240 + 8 * L.e ∧
      256 ≤ hB + P.Q - 8 * P.w ∧ P.Q ≤ 8 * P.w ∧ 8 * P.w ≤ P.Q + 8 ∧ hB + P.Q ≤ 24 + fX := by
  obtain ⟨hQ, h8, h64⟩ := P.sizesA hA
  have := L.he
  have := P.R.len_words
  simp only [hB, fH, fX, RfcHash.w, RfcHash.Q] at *
  omega_arith

/-- Word `j` of the result, by the mask `rdx`, to `h`. -/
theorem selWord_ok (hA : P.R.big = false) {t : State} (hc : Ctx L g m₀ t) {u : State} (hk : RK t u)
    {j : Nat} (hj : j < P.w) :
    WP isa (.block ((cfgOf P).selWord j)) u fun u' => RK u u' ∧ u'.gpr .rdx = u.gpr .rdx ∧
      u'.mem = u.mem.writeW (off L.B (hB + P.Q - 8 * (j + 1)))
        (bswap64 (((word u.mem L.B (88 + 8 * j) ^^^ word u.mem L.B (24 + 8 * j)) &&& u.gpr .rdx) ^^^
          word u.mem L.B (24 + 8 * j))) := by
  obtain ⟨hQ, h6, -⟩ := P.sizesA hA
  obtain ⟨hb₁, hb₂, hb₃, -, -, -, -⟩ := hb_facts (L := L) hA
  obtain hrsp : u.gpr .rsp = L.B + BitVec.ofNat 64 24 := by rw [hk.gpr _ (by decide) (by decide) (by decide), hc.rsp]
  obtain hV : InRegions (u.rd ++ u.wr) (L.B + BitVec.ofNat 64 (88 + 8 * j)) 8 := by
    rw [hk.rd, hk.wr]; exact hc.inFr (by omega_using []) (by omega_using [hj, h6])
  obtain hK : InRegions (u.rd ++ u.wr) (L.B + BitVec.ofNat 64 (24 + 8 * j)) 8 := by
    rw [hk.rd, hk.wr]; exact hc.inFr (by omega_using []) (by omega_using [hj, h6])
  obtain hH : InRegions u.wr (L.B + BitVec.ofNat 64 (hB + P.Q - 8 * (j + 1))) 8 := by
    rw [hk.wr]; exact hc.inFrW (by omega_using [hj, hb₁]) (by omega_using [hj, hb₁, hb₃])
  obtain e88 : 24 + (64 + 8 * j) = 88 + 8 * j := by omega_using []
  have hwn : P.Q = P.R.E.C.len := rfl
  obtain eH : 24 + (fH + P.R.E.C.len - 8 * (j + 1)) = hB + P.Q - 8 * (j + 1) := by
    simp only [hB, fH] at hb₂ ⊢; omega_using [hj, hb₂, hwn, h6]
  apply WP.of_runBlock
  rw [Cfg.selWord]
  simp only [cfgOf, fV, fK, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    State.load64, State.store64, ea_stk, hrsp, Offset.add_add, e88, eH, Nat.zero_add,
    RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, Option.map_some, Option.bind_some,
    reduceCtorEq, ite_false, ite_true, hV, hK, hH, Option.some.injEq, exists_eq_left']
  refine ⟨⟨by trivial, by trivial, fun r h₁ h₂ _ => ?_⟩, by trivial, by trivial⟩
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h₁, h₂, ite_false]

/-- After `k` words of the result, with the mask of the borrow `c` in `rdx`. -/
theorem sels_ok (hA : P.R.big = false) {t : State} (hc : Ctx L g m₀ t) {u : State} (hk : RK t u)
    {c : Bool} {y : BitVec 64} (hm : u.gpr .rdx = y - y - (BitVec.ofBool c).setWidth 64) :
    ∀ k ≤ P.w, WP isa (.block ((List.range k).flatMap (cfgOf P).selWord)) u fun u' =>
      RK u u' ∧ u'.gpr .rdx = u.gpr .rdx ∧ Outside L.B (hB + P.Q - 8 * P.w) (8 * P.w) u.mem u'.mem ∧
      ∀ j < k, word u'.mem L.B (hB + P.Q - 8 * (j + 1)) = bswap64 (word u.mem L.B ((if c then 88 else 24) + 8 * j))
  | 0, _ => WP.block_nil ⟨RK.refl _, rfl, Outside.refl _ _ _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1, hk' => by
    obtain ⟨hQ, h6, -⟩ := P.sizesA hA
    obtain ⟨hb₁, hb₂, hb₃, -, -, -, -⟩ := hb_facts (L := L) hA
    have he := L.he
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (sels_ok hA hc hk hm k (by omega_using [hk'])) fun u₁ ⟨k₁, d₁, O₁, e₁⟩ => ?_
    refine WP.mono (selWord_ok (P := P) hA hc (hk.trans k₁) (j := k) (by omega_using [hk'])) fun u₂ ⟨k₂, d₂, m₂⟩ => ?_
    obtain oH : Outside L.B (hB + P.Q - 8 * (k + 1)) 8 u₁.mem u₂.mem := by
      rw [m₂]; exact writeW_outside _ _ _ (by omega_using [hb₁, hb₃, he])
    obtain hV : word u₁.mem L.B (88 + 8 * k) = word u.mem L.B (88 + 8 * k) :=
      Proof.Mont.Outside.word O₁ (.inl (by omega_using [hk', hb₁])) (by omega_using [hk', h6])
    obtain hK : word u₁.mem L.B (24 + 8 * k) = word u.mem L.B (24 + 8 * k) :=
      Proof.Mont.Outside.word O₁ (.inl (by omega_using [hk', hb₁])) (by omega_using [hk', h6])
    refine ⟨k₁.trans k₂, d₂.trans d₁, O₁.trans (oH.mono (by omega_using [hk', hb₂]) (by omega_using [hk', hb₂])),
      fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [Proof.Mont.Outside.word oH (by omega_arith) (by omega_using [hb₁, hb₃, he]), e₁ j hj]
    · rw [m₂, Proof.Mont.word_writeW_self, hV, hK, d₁, hm, sel_mask]
      cases c <;> rfl

/-! ## The whole of it -/

/-- `h`: `X`'s `Q` bytes modulo `n`, big-endian in the frame at `hB`. -/
theorem reduce_ok (hA : P.R.big = false) (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf P).reduce) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 24, 128⟩, ⟨L.B + BitVec.ofNat 64 (hB + P.Q - 8 * P.w), 8 * P.w⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 hB) P.Q =
        Spec.Weierstrass.toBytes P.Q
          (Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t.mem (xa L) P.Q) % P.R.E.C.n) := by
  obtain ⟨hQ, h6, -⟩ := P.sizesA hA
  obtain ⟨hb₁, hb₂, hb₃, hb₄, -, -, -⟩ := hb_facts (L := L) hA
  have he := L.he
  have h4 : 4 ≤ P.w := P.R.n4
  refine WP.of_syms ?_
  rw [Cfg.reduce, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (fr_ok hL hc (d := .rsi) (by decide) (o := fX) (by decide)) fun t₀ h₀ => ?_
  have hc₀ := h₀.ctx
  have hsi : t₀.gpr .rsi = xa L := h₀.val
  rw [← h₀.mem]
  refine WP.mono (subs_ok hA hc₀ hL hsi P.w (Nat.le_refl _)) fun u₁ ⟨k₁, O₁, e₁, c, _, hcf, hs⟩ => ?_
  obtain hcf₁ : u₁.cf = some c := hcf (by omega_using [h4])
  -- The mask of the borrow.
  refine WP.mono (show WP isa (.block ([.alu .sbb .rdx (.reg .rdx)] : List Instr)) u₁ fun u₂ =>
      RK u₁ u₂ ∧ u₂.mem = u₁.mem ∧ u₂.gpr .rdx = u₁.gpr .rdx - u₁.gpr .rdx - (BitVec.ofBool c).setWidth 64 by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, hcf₁, Option.map_some,
      Option.bind_some, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
      ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨⟨by trivial, by trivial, fun r _ _ h₃ => ?_⟩, by trivial, by trivial⟩
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, h₃, ite_false]) fun u₂ ⟨k₂, m₂, d₂⟩ => ?_
  refine WP.mono (sels_ok (P := P) hA hc₀ (k₁.trans k₂) d₂ P.w (Nat.le_refl _)) fun t' ⟨k₃, _, O₃, e₃⟩ hsy => ?_
  obtain k' : RK t₀ t' := (k₁.trans k₂).trans k₃
  obtain f₁ : Frame [⟨L.B + BitVec.ofNat 64 24, 128⟩] t₀.mem u₂.mem := by
    rw [m₂]; exact frame_of_outside O₁ (by omega_using [])
  obtain f₃ : Frame [⟨L.B + BitVec.ofNat 64 (hB + P.Q - 8 * P.w), 8 * P.w⟩] u₂.mem t'.mem :=
    frame_of_outside O₃ (by omega_using [hb₂, hb₃, he])
  obtain hf : Frame [⟨L.B + BitVec.ofNat 64 24, 128⟩, ⟨L.B + BitVec.ofNat 64 (hB + P.Q - 8 * P.w), 8 * P.w⟩]
      t₀.mem t'.mem :=
    (f₁.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩).trans (f₃.sub fun r hr => ⟨r, by simp_all, sub_refl _⟩)
  obtain hk₀ : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → t'.gpr r = t.gpr r := fun r h₁ h₂ h₃ h₄ =>
    (k'.gpr r h₁ h₂ h₃).trans (h₀.keep r h₄)
  refine ⟨hc.keep hL (k'.rd.trans (hc₀.rd.trans hc.rd.symm)) (k'.wr.trans (hc₀.wr.trans hc.wr.symm))
    (hk₀ _ (by decide) (by decide) (by decide) (by decide))
    (fun r hr _ => hk₀ r (fun h => by subst h; exact absurd hr (by decide)) (fun h => by subst h; exact absurd hr (by decide))
      (fun h => by subst h; exact absurd hr (by decide)) (fun h => by subst h; exact absurd hr (by decide)))
    (h₀.mem ▸ hf)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact safe_low L (by omega_using [])
      · exact safe_high L hb₄ (by omega_using [hb₂, hb₃])) hsy, hf, ?_⟩
  -- The number, the difference, and the one selected.
  obtain ⟨w', hw'⟩ : ∃ w', P.w = w' + 1 := ⟨P.w - 1, by omega_using [h4]⟩
  obtain hX : wordsVal u₁.mem L.B 88 P.w = Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt t₀.mem (xa L) P.Q) := by
    rw [hw']
    exact Proof.Weierstrass.wordsVal_eq_ofBytes_len _ _ _ _ 88 w' P.Q (by omega_using [hQ, hw']) (by omega_using [hQ, hw']) fun j hj => by
      rw [e₁ j (by omega_using [hw', hj]), xw_eq P L t₀.mem (by omega_using [hQ, hw', hj])]
  obtain hsel := Proof.Weierstrass.bytesAt_eq_toBytes t'.mem u₂.mem L.B (L.B + BitVec.ofNat 64 (hB + P.Q - 8 * P.w))
    (a := if c then 88 else 24) (n := P.w) true fun j hj => by
      rw [Offset.add_add, show hB + P.Q - 8 * P.w + 8 * (P.w - 1 - j) = hB + P.Q - 8 * (j + 1) by
        omega_using [hb₂, hj]]
      simp only [ite_true, BitVec.and_allOnes]
      exact e₃ j hj
  simp only [ite_true] at hsel
  rw [show Spec.Sha256.bytesAt = Spec.Ecdsa.bytesAt from rfl] at hX ⊢
  obtain hu : ∀ d, wordsVal u₂.mem L.B d P.w = wordsVal u₁.mem L.B d P.w := fun d => by rw [m₂]
  obtain hn : P.R.E.C.n % 2 ^ (64 * P.w) = P.R.E.C.n := Nat.mod_eq_of_lt P.R.n_lt
  rw [hn] at hs
  obtain hN := (P.R.sizesA hA).2.2.2
  obtain hXl : wordsVal u₁.mem L.B 88 P.w < 2 * P.R.E.C.n := by
    rw [hX]
    have := Proof.Ecdsa.Rfc6979.ofBytes_lt (Spec.Ecdsa.bytesAt t₀.mem (xa L) P.Q)
    rw [Proof.Weierstrass.length_bytesAt] at this
    exact Nat.lt_trans this hN
  obtain key := Proof.Ecdsa.Rfc6979.mod_math2 _ _ _ _ c hs (wordsVal_lt _ _ _ _) hXl
  -- `h`'s `Q` bytes are the last of the `8 w` the words were stored to.
  obtain hv : (if c then wordsVal u₂.mem L.B 88 P.w else wordsVal u₂.mem L.B 24 P.w) =
      Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt t₀.mem (xa L) P.Q) % P.R.E.C.n := by
    rw [← hX, ← key, hu, hu]
  obtain hlt : Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt t₀.mem (xa L) P.Q) % P.R.E.C.n < 2 ^ (8 * P.Q) := by
    have := Nat.mod_lt (Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt t₀.mem (xa L) P.Q)) (Nat.pos_of_ne_zero P.R.n_ne)
    obtain hb : P.R.E.C.n < 2 ^ (8 * P.R.E.C.len) := by
      have := Nat.lt_log2_self (n := P.R.E.C.n)
      rwa [show P.R.E.C.n.log2 + 1 = 8 * P.R.E.C.len from (P.R.sizesA hA).2.2.1] at this
    show _ < 2 ^ (8 * P.R.E.C.len)
    omega_using [this, hb]
  obtain hsel' : Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 (hB + P.Q - 8 * P.w)) (8 * P.w) =
      Spec.Weierstrass.toBytes (8 * P.w) (Spec.Weierstrass.ofBytes (Spec.Ecdsa.bytesAt t₀.mem (xa L) P.Q) % P.R.E.C.n) := by
    rw [show Spec.Sha256.bytesAt = Spec.Ecdsa.bytesAt from rfl, hsel]
    refine congrArg _ ?_
    rw [← hv]; cases c <;> rfl
  rw [show 8 * P.w = (8 * P.w - P.Q) + P.Q by omega_using [hQ], Proof.Hmac.Common.bytesAt_add, Offset.add_add,
    show hB + P.Q - ((8 * P.w - P.Q) + P.Q) + (8 * P.w - P.Q) = hB by omega_using [hQ, hb₂],
    Proof.Ecdsa.Rfc6979.toBytes_pad _ _ _ hlt] at hsel'
  exact (List.append_inj' hsel' (by
    simp only [Spec.Sha256.bytesAt, List.length_map, List.length_range, Proof.Weierstrass.length_toBytes])).2

end VG.Proof.Ecdsa.Rfc6979.X86_64

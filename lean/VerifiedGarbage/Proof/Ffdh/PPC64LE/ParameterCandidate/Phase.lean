module

public import VerifiedGarbage.Spec.Ffdh
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.Mem
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubFn
public import VerifiedGarbage.Impl.Ffdh.PPC64LE.ParameterCandidate
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.Domain

/-! ### `Ffdh.PPC64LE.ParameterCandidate.Base`, which this module and modules that import it used -/

section

/-!
# An FFDH parameter candidate on PPC64LE: the public data and the invariant

`PP`: what the candidate's run depends on, all of it public: the working
space (`n` words at `B`), the arguments and the tape. `Args`: the header
words holding the arguments, which no piece after the entry changes. `mutR`:
the ranges of the working space the pieces may change: header word 1, words
6–15 and 19–31, and the arrays, up to the save area (`saveBytes` at the
end). `St`: what holds between the pieces.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search

/-- What the candidate depends on: the working space (`n` words at `B`),
`out`, `used`, `bits`, the generator, and the tape at `rp`. -/
structure PP where
  B : Addr
  n : Nat
  op : Addr
  up : Addr
  bits : Nat
  g : Nat
  rp : Addr
  r : List Byte
  /-- The stack pointer, which the candidate keeps. -/
  sp : Addr
  /-- The save area's words on entry: the nonvolatile registers and the
  link register. -/
  sv : Nat → BitVec 64
  /-- `r2` on entry, which no piece writes. -/
  toc : BitVec 64

/-- `out_len`. -/
abbrev PP.L (p : PP) : Nat := (p.bits + 7) / 8

/-- The working space's bytes. -/
abbrev PP.Z (p : PP) : Nat := 8 * p.n

/-- The bounds. -/
structure Dims (p : PP) : Prop where
  b1 : 512 ≤ p.bits
  b2 : p.bits ≤ 8192
  g : p.g = 2 ∨ p.g = 5
  n : 16 * p.L + 32 ≤ p.n
  n' : 8 * p.n ≤ 2 ^ 64
  rl : p.r.length < 2 ^ 64

/-- The header words holding the arguments. -/
structure Args (m : Mem) (p : PP) : Prop where
  wsLen : word m p.B (8 * hWsLen) = BitVec.ofNat 64 p.n
  out : word m p.B (8 * hOut) = p.op
  len : word m p.B (8 * hLen) = BitVec.ofNat 64 p.L
  usedP : word m p.B (8 * hUsedP) = p.up
  bits : word m p.B (8 * hBits) = BitVec.ofNat 64 p.bits
  gen : word m p.B (8 * hGen) = BitVec.ofNat 64 p.g
  rand : word m p.B (8 * hRand) = p.rp
  rlen : word m p.B (8 * hRandLen) = BitVec.ofNat 64 p.r.length

/-- The ranges of the working space the pieces may change. -/
def mutR (n : Nat) : List (Nat × Nat) := [(8, 8), (48, 80), (152, 104), (256, 8 * n - saveBytes - 256)]

/-- A range within one of `mutR`. -/
def InMut (n : Nat) (r : Nat × Nat) : Prop := ∃ r' ∈ mutR n, r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2

theorem InMut.arrays {n o k : Nat} (h1 : 256 ≤ o) (h2 : o + k + saveBytes ≤ 8 * n) : InMut n (o, k) :=
  ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))), h1,
    by simp only [saveBytes] at h2 ⊢; omega_arith⟩

theorem InMut.hdr {n i : Nat} (h : i = 1 ∨ (6 ≤ i ∧ i < 16) ∨ (19 ≤ i ∧ i < 32)) : InMut n (8 * i, 8) := by
  rcases h with rfl | h | h
  · exact ⟨_, List.mem_cons_self, by decide, by decide⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by omega_arith, by omega_arith⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), by omega_arith, by omega_arith⟩

/-- A change within ranges of `mutR` is within `mutR`. -/
theorem Frm.toMut {B : Addr} {n : Nat} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm B rs m m')
    (hr : ∀ r ∈ rs, InMut n r) : Frm B (mutR n) m m' := h.widen hr

/-- The argument words are not in `mutR`. -/
theorem Args.frm {m m' : Mem} {p : PP} {B' : Addr} (h : Args m p) (hf : Frm B' (mutR p.n) m m') (hB : B' = p.B) :
    Args m' p := by
  subst hB
  have k : ∀ {i : Nat}, i = 0 ∨ (2 ≤ i ∧ i ≤ 5) ∨ (16 ≤ i ∧ i ≤ 18) →
      word m' p.B (8 * i) = word m p.B (8 * i) := fun hi =>
    hf.word_eq (fun r hr => by
      simp only [mutR, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith) (by omega_arith)
  exact ⟨(k (by decide)).trans h.wsLen, (k (by decide)).trans h.out, (k (by decide)).trans h.len,
    (k (by decide)).trans h.usedP, (k (by decide)).trans h.bits, (k (by decide)).trans h.gen,
    (k (by decide)).trans h.rand, (k (by decide)).trans h.rlen⟩

/-- The buffers: the tape, readable and apart from the working space; `out`
and `used`, writable and apart from the working space and the tape. -/
structure Bufs (p : PP) (s : State) : Prop where
  rdR : ∀ i < p.r.length, InRegions (s.rd ++ s.wr) (off p.rp i) 1
  sepR : ∀ i < p.r.length, ∀ x, ofs p.B x < p.Z → off p.rp i ≠ x
  bR : Spec.Rsa.bytesAt s.mem p.rp p.r.length = p.r
  /-- `out` is zeroed first. -/
  bO : Spec.Rsa.bytesAt s.mem p.op p.L = List.replicate p.L 0
  scrO : Scr s p.op p.L
  sepO : ∀ x, ofs p.op x < p.L → p.Z ≤ ofs p.B x
  scrU : Scr s p.up 8
  sepU : ∀ x, ofs p.up x < 8 → p.Z ≤ ofs p.B x
  stkR : (below p.sp 176).Disjoint ⟨p.rp, p.r.length⟩
  stkO : (below p.sp 176).Disjoint ⟨p.op, p.L⟩
  stkU : (below p.sp 176).Disjoint ⟨p.up, 8⟩
  dOU : (⟨p.op, p.L⟩ : Region).Disjoint ⟨p.up, 8⟩

/-- The tape's bytes are kept by a change in the working space. -/
theorem bytes_frm {p : PP} {m m' : Mem} {rs : List (Nat × Nat)} (hf : Frm p.B rs m m')
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ p.Z) (hsep : ∀ i < p.r.length, ∀ x, ofs p.B x < p.Z → off p.rp i ≠ x) :
    Spec.Rsa.bytesAt m' p.rp p.r.length = Spec.Rsa.bytesAt m p.rp p.r.length := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hf _ fun r hr' => Or.inr ?_
  have := hsep i (List.mem_range.mp hi) (off p.rp i)
  have h2 := hr r hr'
  show r.1 + r.2 ≤ ofs p.B (off p.rp i)
  by_contra hc
  exact this (by omega_arith) rfl

/-- `out`'s bytes are kept by a change in the working space. -/
theorem out_frm {p : PP} {m m' : Mem} {rs : List (Nat × Nat)} (hf : Frm p.B rs m m')
    (hr : ∀ r ∈ rs, r.1 + r.2 ≤ p.Z) (hsep : ∀ x, ofs p.op x < p.L → p.Z ≤ ofs p.B x) (hL : p.L ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p.op p.L = Spec.Rsa.bytesAt m p.op p.L := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hf _ fun r hr' => Or.inr ?_
  have hi' := List.mem_range.mp hi
  have := hsep (p.op + BitVec.ofNat 64 i) (by simp only [ofs]; rw [Mem.sub_ofNat_toNat _ (by omega_arith)]; exact hi')
  have h2 := hr r hr'
  omega_arith

theorem Bufs.step {p : PP} {s t : State} {rs : List (Nat × Nat)} {regs : List Reg} (h : Bufs p s)
    (hf : Frm p.B rs s.mem t.mem) (hr : ∀ r ∈ rs, r.1 + r.2 ≤ p.Z) (k : Keep regs s t) : Bufs p t where
  rdR := by rw [k.rd, k.wr]; exact h.rdR
  sepR := h.sepR
  bR := by rw [bytes_frm hf hr h.sepR]; exact h.bR
  bO := by rw [out_frm hf hr h.sepO (by have := h.scrO.nowrap; omega_arith)]; exact h.bO
  scrO := h.scrO.congr k.wr
  sepO := h.sepO
  scrU := h.scrU.congr k.wr
  sepU := h.sepU
  stkR := h.stkR
  stkO := h.stkO
  stkU := h.stkU
  dOU := h.dOU

/-- Between the pieces: the working space at `r31`, the arguments, the
buffers and the bounds. -/
structure St (p : PP) (s : State) : Prop where
  scr : Scr s p.B p.Z
  r31 : s.gpr .r31 = p.B
  args : Args s.mem p
  bufs : Bufs p s
  dims : Dims p
  ws : (⟨p.B, p.Z⟩ : Region) ∈ s.wr
  sp : s.sp = p.sp
  stk : 176 ≤ p.sp.toNat
  stkB : (below p.sp 176).Disjoint ⟨p.B, p.Z⟩
  save : ∀ i < 19, word s.mem p.B (8 * p.n - saveBytes + 8 * i) = p.sv i
  r2 : s.gpr .r2 = p.toc

/-- `St` survives a piece that keeps `r31` and changes only `mutR` ranges of
the working space. -/
theorem St.step {p : PP} {s t : State} {regs : List Reg} (h : St p s) (hf : Frm p.B (mutR p.n) s.mem t.mem)
    (k : Keep regs s t) (h31 : Reg.r31 ∉ regs := by decide) (h2 : Reg.r2 ∉ regs := by decide) : St p t where
  scr := h.scr.congr k.wr
  r31 := (k.gpr .r31 h31).trans h.r31
  args := h.args.frm hf rfl
  bufs := h.bufs.step hf (fun r hr => by
    have := h.dims.n
    simp only [mutR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> dsimp only [PP.Z, saveBytes] <;> omega_arith) k
  dims := h.dims
  ws := by rw [k.wr]; exact h.ws
  sp := k.sp.trans h.sp
  stk := h.stk
  stkB := h.stkB
  save := fun i hi => by
    have := h.dims.n; have := h.dims.n'; have := h.dims.b1
    refine (hf.word_eq (fun r hr => .inr ?_) (by simp only [saveBytes]; omega_arith)).trans (h.save i hi)
    simp only [mutR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> simp only [saveBytes, PP.L] at * <;> omega_arith
  r2 := (k.gpr .r2 h2).trans h.r2

/-- A header word of `St`'s working space: its load and its store. -/
theorem St.ld {p : PP} {s : State} (h : St p s) {d : Nat} (hd : d + 8 ≤ 256) :
    InRegions (s.rd ++ s.wr) (p.B + BitVec.ofNat 64 d) 8 :=
  h.scr.ld (d := d) (by have := h.dims.n; simp only [PP.Z]; omega_arith)

theorem St.st {p : PP} {s : State} (h : St p s) {d : Nat} (hd : d + 8 ≤ 256) :
    InRegions s.wr (p.B + BitVec.ofNat 64 d) 8 :=
  h.scr.st (d := d) (by have := h.dims.n; simp only [PP.Z]; omega_arith)

/-- The tape's first `k` bytes in memory. -/
theorem St.take_bytes {p : PP} {s : State} (h : St p s) {k : Nat} (hk : k ≤ p.r.length) :
    Spec.Rsa.bytesAt s.mem p.rp k = p.r.take k := by
  rw [← h.bufs.bR, Proof.Ffdh.take_bytesAt _ _ hk]

/-! ## The arguments, at their literal offsets -/

theorem Args.out' {m : Mem} {p : PP} (h : Args m p) : m.readW (p.B + BitVec.ofNat 64 16) 64 = p.op := h.out
theorem Args.len' {m : Mem} {p : PP} (h : Args m p) : m.readW (p.B + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 p.L :=
  h.len
theorem Args.usedP' {m : Mem} {p : PP} (h : Args m p) : m.readW (p.B + BitVec.ofNat 64 32) 64 = p.up := h.usedP
theorem Args.bits' {m : Mem} {p : PP} (h : Args m p) :
    m.readW (p.B + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 p.bits := h.bits
theorem Args.gen' {m : Mem} {p : PP} (h : Args m p) : m.readW (p.B + BitVec.ofNat 64 128) 64 = BitVec.ofNat 64 p.g :=
  h.gen
theorem Args.rand' {m : Mem} {p : PP} (h : Args m p) : m.readW (p.B + BitVec.ofNat 64 136) 64 = p.rp := h.rand
theorem Args.rlen' {m : Mem} {p : PP} (h : Args m p) :
    m.readW (p.B + BitVec.ofNat 64 144) 64 = BitVec.ofNat 64 p.r.length := h.rlen

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate

end

end

/-!
# An FFDH parameter candidate on PPC64LE: a modulus's working space

`phase_ok`: for the modulus of `mb` bits (`bits − 1` for q, `bits` for p),
`w = ⌈mb / 64⌉`, the header (`Ph`: `mb`, `⌈mb / 8⌉`, `w`, the arrays'
addresses and size, the number of checks and the top word's mask) and the
registers of the arrays.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search

/-- The working space of a modulus of `mb` bits: `w = ⌈mb / 64⌉`. -/
abbrev wOf (mb : Nat) : Nat := (mb + 63) / 64

/-- The header and the registers after `phase`, with `K` witnesses to test. -/
structure Ph (p : PP) (mb K : Nat) (s : State) : Prop where
  r10 : s.gpr .r10 = off p.B (slot (wOf mb) 0)
  r11 : s.gpr .r11 = BitVec.ofNat 64 (2 * wOf mb)
  r29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (wOf mb + 2))
  mbW : word s.mem p.B (8 * hMb) = BitVec.ofNat 64 mb
  kW : word s.mem p.B (8 * hK) = BitVec.ofNat 64 ((mb + 7) / 8)
  wW : word s.mem p.B (8 * hW) = BitVec.ofNat 64 (wOf mb)
  strideW : word s.mem p.B (8 * hStride) = BitVec.ofNat 64 (8 * (wOf mb + 2))
  arrW : ∀ j < 8, word s.mem p.B (8 * (8 + j)) = off p.B (slot (wOf mb) j)
  checksW : word s.mem p.B (8 * hChecks) = BitVec.ofNat 64 K
  k1 : 1 ≤ K
  k2 : K ≤ 128
  topW : word s.mem p.B (8 * hTop) = BitVec.ofNat 64 (2 ^ (mb + 64 - 64 * wOf mb) - 1)

/-- The bit length of the modulus: `bits − 1` for q, `bits` for p. -/
abbrev mbOf (p : PP) (q : Bool) : Nat := if q then p.bits - 1 else p.bits

theorem add_shr (x a k : Nat) (h : x + a < 2 ^ 64) :
    (BitVec.ofNat 64 x + BitVec.ofNat 64 a) >>> k = BitVec.ofNat 64 ((x + a) / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.add_mod_mod, Nat.mod_add_mod, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h)]

theorem checks_eq {mb : Nat} (h : mb ≤ 8192) :
    BitVec.ofNat 64 128 - ((BitVec.ofNat 64 mb - BitVec.ofNat 64 2049) >>> 63) <<< 6 =
      BitVec.ofNat 64 (Spec.Ffdh.primeChecks mb) := by
  unfold Spec.Ffdh.primeChecks
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  split
  · have e : (2 ^ 64 - 2049 % 2 ^ 64 + mb % 2 ^ 64) % 2 ^ 64 / 2 ^ 63 = 1 := by
      rw [Nat.mod_eq_of_lt (show 2049 < 2 ^ 64 by decide), Nat.mod_eq_of_lt (show mb < 2 ^ 64 by omega_arith),
        Nat.mod_eq_of_lt (by omega_arith)]
      omega_arith
    rw [e]; rfl
  · have e : (2 ^ 64 - 2049 % 2 ^ 64 + mb % 2 ^ 64) % 2 ^ 64 / 2 ^ 63 = 0 := by
      rw [Nat.mod_eq_of_lt (show 2049 < 2 ^ 64 by decide), Nat.mod_eq_of_lt (show mb < 2 ^ 64 by omega_arith)]
      omega_arith
    rw [e]; rfl

/-- The registers `phaseHead` writes. -/
def phRegs : List Reg := [.r3, .r4, .r5, .r6, .r10, .r11, .r29]

/-- The ranges `phaseHead` changes: words 6–15, 21, 27, 28 and 31. -/
def phRanges : List (Nat × Nat) := [(48, 80), (168, 8), (216, 16), (248, 8)]

theorem phaseHead_ok {p : PP} {s : State} (h : St p s) (q : Bool) :
    WP isa (.block (phaseHead q)) s fun t =>
      (t.gpr .r10 = off p.B (slot (wOf (mbOf p q)) 0) ∧ t.gpr .r11 = BitVec.ofNat 64 (2 * wOf (mbOf p q)) ∧
        t.gpr .r29 = BitVec.ofNat 64 (8 * (wOf (mbOf p q) + 2)) ∧
        word t.mem p.B (8 * hMb) = BitVec.ofNat 64 (mbOf p q) ∧
        word t.mem p.B (8 * hK) = BitVec.ofNat 64 ((mbOf p q + 7) / 8) ∧
        word t.mem p.B (8 * hW) = BitVec.ofNat 64 (wOf (mbOf p q)) ∧
        word t.mem p.B (8 * hStride) = BitVec.ofNat 64 (8 * (wOf (mbOf p q) + 2)) ∧
        (∀ j < 8, word t.mem p.B (8 * (8 + j)) = off p.B (slot (wOf (mbOf p q)) j)) ∧
        word t.mem p.B (8 * hChecks) = BitVec.ofNat 64 (Spec.Ffdh.primeChecks (mbOf p q)) ∧
        Frm p.B phRanges s.mem t.mem) ∧ Keep phRegs s t := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  cases q <;> refine WP.keep _ ?_ (by decide) <;> unfold phaseHead <;>
    simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil, List.flatMap, List.range, List.range.loop,
      List.map, List.flatten, List.cons_append, List.nil_append, List.append_eq, ldh, sth, hBits, hMb, hK, hW, hStride,
      hChecks, hdrBytes, mbOf]
  · have ew : (BitVec.ofNat 64 p.bits + 63#64) >>> 6 = BitVec.ofNat 64 (wOf p.bits) := add_shr _ _ _ (by omega_arith)
    have ek : (BitVec.ofNat 64 p.bits + 7#64) >>> 3 = BitVec.ofNat 64 ((p.bits + 7) / 8) := add_shr _ _ _ (by omega_arith)
    have e29 : BitVec.ofNat 64 (8 * wOf p.bits) + 16#64 = BitVec.ofNat 64 (8 * (wOf p.bits + 2)) := by
      rw [BitVec.ofNat_add_ofNat]; congr 1
    prun [h.r31, h.ld (d := 40) (by decide), h.args.bits', h.st (d := 248) (by decide), h.st (d := 216) (by decide),
      h.st (d := 48) (by decide), h.st (d := 224) (by decide), h.st (d := 64) (by decide), h.st (d := 72) (by decide),
      h.st (d := 80) (by decide), h.st (d := 88) (by decide), h.st (d := 96) (by decide), h.st (d := 104) (by decide),
      h.st (d := 112) (by decide), h.st (d := 120) (by decide), h.st (d := 168) (by decide), ew, ek,
      Pub.ofNat_shl3, Pub.ofNat_shl1, e29, checks_eq hb2]
    refine ⟨by simp [off, slot, hdrBytes], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    any_goals simp (disch := decide) only [word, off, rw_off, rw_self]
    · intro j hj
      rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j
      all_goals first
        | (simp (disch := decide) only [rw_off, rw_self, Nat.reduceMul, Nat.reduceAdd]
           congr 1; simp only [slot, hdrBytes]; omega_arith)
        | omega_arith
    · iterate 13 refine frm_writeW ?_ _ (by decide) (by decide)
      exact Frm.refl _ _ _
  · have e1 : BitVec.ofNat 64 p.bits - 1#64 = BitVec.ofNat 64 (p.bits - 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega_arith
    have ew : (BitVec.ofNat 64 (p.bits - 1) + 63#64) >>> 6 = BitVec.ofNat 64 (wOf (p.bits - 1)) :=
      add_shr _ _ _ (by omega_arith)
    have ek : (BitVec.ofNat 64 (p.bits - 1) + 7#64) >>> 3 = BitVec.ofNat 64 ((p.bits - 1 + 7) / 8) :=
      add_shr _ _ _ (by omega_arith)
    have e29 : BitVec.ofNat 64 (8 * wOf (p.bits - 1)) + 16#64 = BitVec.ofNat 64 (8 * (wOf (p.bits - 1) + 2)) := by
      rw [BitVec.ofNat_add_ofNat]; congr 1
    have ec := checks_eq (mb := p.bits - 1) (by omega_arith)
    prun [h.r31, h.ld (d := 40) (by decide), h.args.bits', h.st (d := 248) (by decide), h.st (d := 216) (by decide),
      h.st (d := 48) (by decide), h.st (d := 224) (by decide), h.st (d := 64) (by decide), h.st (d := 72) (by decide),
      h.st (d := 80) (by decide), h.st (d := 88) (by decide), h.st (d := 96) (by decide), h.st (d := 104) (by decide),
      h.st (d := 112) (by decide), h.st (d := 120) (by decide), h.st (d := 168) (by decide), e1, ew, ek,
      Pub.ofNat_shl3, Pub.ofNat_shl1, e29, ec]
    refine ⟨by simp [off, slot, hdrBytes], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    any_goals simp (disch := decide) only [word, off, rw_off, rw_self]
    · intro j hj
      rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j
      all_goals first
        | (simp (disch := decide) only [rw_off, rw_self, Nat.reduceMul, Nat.reduceAdd]
           congr 1; simp only [slot, hdrBytes]; omega_arith)
        | omega_arith
    · iterate 13 refine frm_writeW ?_ _ (by decide) (by decide)
      exact Frm.refl _ _ _

/-- `topMask`'s first block: its count `k = mb + 64 − 64 w` in `r3`. -/
theorem topT1_ok {p : PP} {s : State} (h : St p s) {mb : Nat}
    (hm : word s.mem p.B (8 * hMb) = BitVec.ofNat 64 mb) (hw : word s.mem p.B (8 * hW) = BitVec.ofNat 64 (wOf mb)) :
    WP isa (.block [ldh .r3 hMb, ldh .r4 hW, .lsl .r4 .r4 6, .sub .r3 .r3 .r4, .addi .r3 .r3 64, .li .r5 0]) s
      fun u => (u.gpr .r3 = BitVec.ofNat 64 (mb + 64 - 64 * wOf mb) ∧ u.gpr .r5 = BitVec.ofNat 64 0 ∧
        u.mem = s.mem) ∧ Keep [.r3, .r4, .r5] s u := by
  have hk1 : 1 ≤ mb + 64 - 64 * wOf mb := by simp only [wOf]; omega_arith
  have hk2 : mb + 64 - 64 * wOf mb ≤ 64 := by simp only [wOf]; omega_arith
  generalize hkd : mb + 64 - 64 * wOf mb = k at hk1 hk2 ⊢
  have ek : BitVec.ofNat 64 mb - BitVec.ofNat 64 (wOf mb) <<< 6 + BitVec.ofNat 64 64 = BitVec.ofNat 64 k := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    simp only [wOf] at hkd ⊢
    omega_arith
  refine WP.keep [.r3, .r4, .r5] ?_ (by decide)
  simp only [ldh, hMb, hW]
  prun [h.r31, h.ld (d := 248) (by decide), h.ld (d := 48) (by decide), show s.mem.readW (p.B + 248#64) 64 =
    BitVec.ofNat 64 mb from hm, show s.mem.readW (p.B + 48#64) 64 = BitVec.ofNat 64 (wOf mb) from hw]
  exact ek

/-- `topMask`: `hTop := 2^k − 1` for `k = mb + 64 − 64 w`, in 1..=64. -/
theorem topMask_ok {p : PP} {s : State} (h : St p s) {mb : Nat}
    (hm : word s.mem p.B (8 * hMb) = BitVec.ofNat 64 mb) (hw : word s.mem p.B (8 * hW) = BitVec.ofNat 64 (wOf mb)) :
    WP isa topMask s fun t =>
      (word t.mem p.B (8 * hTop) = BitVec.ofNat 64 (2 ^ (mb + 64 - 64 * wOf mb) - 1) ∧
        Frm p.B [(8 * hTop, 8)] s.mem t.mem) ∧ Keep [.r3, .r4, .r5] s t := by
  have hk1 : 1 ≤ mb + 64 - 64 * wOf mb := by simp only [wOf]; omega_arith
  have hk2 : mb + 64 - 64 * wOf mb ≤ 64 := by simp only [wOf]; omega_arith
  unfold topMask
  refine WP.seq (WP.mono (topT1_ok h hm hw) fun u ⟨⟨u3, u5, um⟩, ku⟩ => ?_)
  generalize hkd : mb + 64 - 64 * wOf mb = k at hk1 hk2 u3 ⊢
  let Inv : Nat → State → Prop := fun i t =>
    (t.gpr .r5 = BitVec.ofNat 64 (2 ^ i - 1) ∧ t.mem = s.mem) ∧ Keep [.r3, .r4, .r5] s t
  refine WP.seq (WP.mono (wp_countdown (cnt := .r3) (N := k) (by omega_arith) (by omega_arith) Inv
    (fun i hi t ⟨⟨t5, tm⟩, kt⟩ _ => ?_) ⟨⟨u5, um⟩, ku⟩ u3) fun t ⟨⟨t5, tm⟩, kt⟩ => ?_)
  · refine WP.mono (WP.keep [.r3, .r5] (Q := fun t' => t'.gpr .r5 = BitVec.ofNat 64 (2 ^ (i + 1) - 1) ∧
      t'.mem = t.mem ∧ t'.gpr .r3 = t.gpr .r3 - BitVec.ofNat 64 1) ?_ (by decide))
      fun t' ⟨⟨a, b, c⟩, k'⟩ => ⟨⟨⟨a, b.trans tm⟩, (kt.trans k').mono (by decide)⟩, c⟩
    prun [t5]
    apply BitVec.eq_of_toNat_eq
    have : 2 ^ i ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega_arith)
    have : 1 ≤ 2 ^ i := Nat.one_le_two_pow
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.pow_succ]
    omega_arith
  · have hst : InRegions t.wr (p.B + BitVec.ofNat 64 192) 8 := by rw [kt.wr]; exact h.st (d := 192) (by decide)
    refine WP.mono (WP.keep [] (Q := fun t' => t'.mem = t.mem.writeW (p.B + BitVec.ofNat 64 192) (t.gpr .r5)) ?_
      (by decide)) fun t' ⟨e, k'⟩ => ⟨⟨?_, ?_⟩, (kt.trans k').mono (by decide)⟩
    · simp only [sth, hTop]
      prun [(kt.gpr .r31 (by decide)).trans h.r31, hst]
    · show (t'.mem).readW (p.B + BitVec.ofNat 64 192) 64 = _
      rw [e, rw_self, t5]
    · rw [e, ← tm]; exact (frm_writeW (Frm.refl _ _ _) _ (by decide) (by decide))

/-- The registers `phase` writes. -/
def phaseRegs : List Reg := phRegs

theorem phRanges_mut (n : Nat) : ∀ r ∈ phRanges ++ [(8 * hTop, 8)], InMut n r := by
  intro r hr
  simp only [phRanges, hTop, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by decide, by decide⟩
  all_goals exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), by decide, by decide⟩

/-- `phase`: `Ph` for the modulus of `mbOf p q` bits. -/
theorem phase_ok {p : PP} {s : State} (h : St p s) (q : Bool) :
    WP isa (phase q) s fun t => (St p t ∧ Ph p (mbOf p q) (Spec.Ffdh.primeChecks (mbOf p q)) t ∧ Frm p.B (phRanges ++ [(8 * hTop, 8)]) s.mem t.mem) ∧
      Keep phaseRegs s t := by
  unfold phase
  refine WP.seq (WP.mono (phaseHead_ok h q) fun u ⟨⟨u10, u11, u29, um, uk, uw, us, ua, uc, uf⟩, ku⟩ => ?_)
  have fu : Frm p.B (mutR p.n) s.mem u.mem := Frm.toMut (uf.mono fun r hr => List.mem_append_left _ hr)
    (phRanges_mut p.n)
  have hu := h.step fu ku
  refine WP.mono (topMask_ok hu um uw) fun t ⟨⟨tt, tf⟩, kt⟩ => ?_
  have ft : Frm p.B (mutR p.n) u.mem t.mem := Frm.toMut (tf.mono fun r hr => List.mem_append_right _ hr)
    (phRanges_mut p.n)
  have e : ∀ {d : Nat}, d + 8 ≤ 192 ∨ (200 ≤ d ∧ d + 8 ≤ 256) → word t.mem p.B d = word u.mem p.B d := fun hd =>
    tf.word_eq (fun r hr => by rw [List.mem_singleton] at hr; subst hr; simp only [hTop]; omega_arith) (by omega_arith)
  refine ⟨⟨hu.step ft kt, ⟨(kt.gpr .r10 (by decide)).trans u10, (kt.gpr .r11 (by decide)).trans u11,
    (kt.gpr .r29 (by decide)).trans u29, (e (by simp only [hMb]; omega_arith)).trans um,
    (e (by simp only [hK]; omega_arith)).trans uk, (e (by simp only [hW]; omega_arith)).trans uw,
    (e (by simp only [hStride]; omega_arith)).trans us, fun j hj => (e (by omega_arith)).trans (ua j hj),
    (e (by simp only [hChecks]; omega_arith)).trans uc, by unfold Spec.Ffdh.primeChecks; split <;> decide,
    by unfold Spec.Ffdh.primeChecks; split <;> decide, tt⟩,
    (uf.mono fun r hr => List.mem_append_left _ hr).trans (tf.mono fun r hr => List.mem_append_right _ hr)⟩,
    (ku.trans kt).mono (by decide)⟩

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate

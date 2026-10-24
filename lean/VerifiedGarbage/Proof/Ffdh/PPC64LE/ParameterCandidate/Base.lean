module

public import VerifiedGarbage.Impl.Ffdh.PPC64LE.ParameterCandidate
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

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
  n' : p.n < 2 ^ 58
  rl : p.r.length < 2 ^ 63

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
    by simp only [saveBytes] at h2 ⊢; omega⟩

theorem InMut.hdr {n i : Nat} (h : i = 1 ∨ (6 ≤ i ∧ i < 16) ∨ (19 ≤ i ∧ i < 32)) : InMut n (8 * i, 8) := by
  rcases h with rfl | h | h
  · exact ⟨_, List.mem_cons_self, by decide, by decide⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by omega, by omega⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), by omega, by omega⟩

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
      rcases hr with rfl | rfl | rfl | rfl <;> dsimp only <;> omega) (by omega)
  exact ⟨(k (by decide)).trans h.wsLen, (k (by decide)).trans h.out, (k (by decide)).trans h.len,
    (k (by decide)).trans h.usedP, (k (by decide)).trans h.bits, (k (by decide)).trans h.gen,
    (k (by decide)).trans h.rand, (k (by decide)).trans h.rlen⟩

/-- The buffers: the tape, readable and apart from the working space; `out`
and `used`, writable and apart from the working space and the tape. -/
structure Bufs (p : PP) (s : State) : Prop where
  rdR : ∀ i < p.r.length, InRegions (s.rd ++ s.wr) (off p.rp i) 1
  sepR : ∀ i < p.r.length, ∀ x, ofs p.B x < p.Z → off p.rp i ≠ x
  bR : Spec.Rsa.bytesAt s.mem p.rp p.r.length = p.r
  scrO : Scr s p.op p.L
  sepO : ∀ x, ofs p.op x < p.L → p.Z ≤ ofs p.B x
  scrU : Scr s p.up 8
  sepU : ∀ x, ofs p.up x < 8 → p.Z ≤ ofs p.B x
  stkR : (below p.sp 176).Disjoint ⟨p.rp, p.r.length⟩
  stkO : (below p.sp 176).Disjoint ⟨p.op, p.L⟩
  stkU : (below p.sp 176).Disjoint ⟨p.up, 8⟩

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
  exact this (by omega) rfl

theorem Bufs.step {p : PP} {s t : State} {rs : List (Nat × Nat)} {regs : List Reg} (h : Bufs p s)
    (hf : Frm p.B rs s.mem t.mem) (hr : ∀ r ∈ rs, r.1 + r.2 ≤ p.Z) (k : Keep regs s t) : Bufs p t where
  rdR := by rw [k.rd, k.wr]; exact h.rdR
  sepR := h.sepR
  bR := by rw [bytes_frm hf hr h.sepR]; exact h.bR
  scrO := h.scrO.congr k.wr
  sepO := h.sepO
  scrU := h.scrU.congr k.wr
  sepU := h.sepU
  stkR := h.stkR
  stkO := h.stkO
  stkU := h.stkU

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

/-- `St` survives a piece that keeps `r31` and changes only `mutR` ranges of
the working space. -/
theorem St.step {p : PP} {s t : State} {regs : List Reg} (h : St p s) (hf : Frm p.B (mutR p.n) s.mem t.mem)
    (k : Keep regs s t) (h31 : Reg.r31 ∉ regs := by decide) : St p t where
  scr := h.scr.congr k.wr
  r31 := (k.gpr .r31 h31).trans h.r31
  args := h.args.frm hf rfl
  bufs := h.bufs.step hf (fun r hr => by
    have := h.dims.n
    simp only [mutR, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> dsimp only [PP.Z, saveBytes] <;> omega) k
  dims := h.dims
  ws := by rw [k.wr]; exact h.ws
  sp := k.sp.trans h.sp
  stk := h.stk
  stkB := h.stkB

/-- A header word of `St`'s working space: its load and its store. -/
theorem St.ld {p : PP} {s : State} (h : St p s) {d : Nat} (hd : d + 8 ≤ 256) :
    InRegions (s.rd ++ s.wr) (p.B + BitVec.ofNat 64 d) 8 :=
  h.scr.ld (d := d) (by have := h.dims.n; simp only [PP.Z]; omega)

theorem St.st {p : PP} {s : State} (h : St p s) {d : Nat} (hd : d + 8 ≤ 256) :
    InRegions s.wr (p.B + BitVec.ofNat 64 d) 8 :=
  h.scr.st (d := d) (by have := h.dims.n; simp only [PP.Z]; omega)

/-- The tape's first `k` bytes in memory. -/
theorem St.take_bytes {p : PP} {s : State} (h : St p s) {k : Nat} (hk : k ≤ p.r.length) :
    Spec.Rsa.bytesAt s.mem p.rp k = p.r.take k := by
  rw [← h.bufs.bR, Proof.Ffdh.take_bytesAt _ _ hk]

/-! ## The arguments, at their literal offsets -/

theorem Args.wsLen' {m : Mem} {p : PP} (h : Args m p) : m.readW (p.B + BitVec.ofNat 64 0) 64 = BitVec.ofNat 64 p.n :=
  h.wsLen
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

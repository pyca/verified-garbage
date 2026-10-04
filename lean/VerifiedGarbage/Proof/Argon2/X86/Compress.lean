import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Blake2.X86.CompressB.Body
import VerifiedGarbage.Spec.Argon2.Contract
import VerifiedGarbage.Proof.Argon2.X86.Gb
import VerifiedGarbage.Proof.Argon2.Permutation

section

section

section

/-!
# Argon2 on x86 (32-bit): the row and column permutations

As on x86-64 (`Proof/Argon2/X86_64/Compress.lean`): P on any injectively
selected row or column (`permuteAt_ok`), and the rows and columns
(`rounds_ok`).
-/

namespace VG.Proof.Argon2.X86

open VG VG.X86 VG.Spec.Argon2
open VG.Proof.Argon2
open VG.Proof.Sha512.X86 (Acc)


/-- The selected sixteen words and the unchanged words outside them. -/
def Holds (index : Fin 16 → Fin 128) (b : Block) (v : Vector Word 16) (m : Mem)
    (B : BitVec 32) : Prop :=
  gather index (working m B) = v ∧ ∀ k : Fin 128, (∀ j, index j ≠ k) → (working m B)[k] = b[k]

/-- The base and the permissions of `scratch`, and the rest of a `Step`. -/
def At (B : BitVec 32) (s : State) : Prop := s.gpr .esi = B ∧ Acc s.wr B 4096

theorem At.of_step {B : BitVec 32} {s t : State} {v : Block} (h : At B s) (st : Step B s v t) : At B t :=
  ⟨st.keep.esi.trans h.1, st.keep.wr ▸ h.2⟩

section
variable {B : BitVec 32} (hfit : B.toNat + 4096 ≤ 2 ^ 32)

include hfit

/-- One GB advances the selected row or column and preserves its complement. -/
theorem step_ok (index : Fin 16 → Fin 128) (hi : Function.Injective index) {s : State}
    (hs : At B s) (base : Block) (v : Vector Word 16) (hv : Holds index base v s.mem B)
    (a b c d : Fin 16) (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (had : a.val ≠ d.val)
    (hbc : b.val ≠ c.val) (hbd : b.val ≠ d.val) (hcd : c.val ≠ d.val) :
    WP isa (Impl.Argon2.X86.gbAt (index a).val (index b).val (index c).val (index d).val) s
      fun t => Holds index base (GB v a b c d) t.mem B ∧
        ∃ w, Step B s w t := by
  have ne : ∀ {x y : Fin 16}, x.val ≠ y.val → (index x).val ≠ (index y).val :=
    fun h e => h (congrArg Fin.val (hi (Fin.ext e)))
  refine (gbAt_ok hfit hs.1 hs.2 (index a) (index b) (index c) (index d)).mono fun t st => ?_
  rw [gbV_eq _ (ne hab) (ne hac) (ne had) (ne hbc) (ne hbd) (ne hcd)] at st
  refine ⟨⟨?_, ?_⟩, _, st⟩
  · rw [st.working, gather_mixWords index hi, hv.1, GB_eq_mixWords v hab hac had hbc hbd hcd]
  · intro k hn
    rw [st.working]
    have ne' (j : Fin 16) : (index j).val ≠ k.val := fun h => hn j (Fin.ext h)
    simp only [mixWords, Fin.getElem_fin, Vector.getElem_set, ne', ite_false]
    exact hv.2 k hn

/-- P on any injectively selected row or column. -/
theorem permuteAt_holds (index : Fin 16 → Fin 128) (hi : Function.Injective index) {s : State}
    (hs : At B s) (base : Block) (v : Vector Word 16) (hv : Holds index base v s.mem B) :
    WP isa (Impl.Argon2.X86.permuteAt index) s fun t =>
      Holds index base (permute v) t.mem B ∧ ∃ w, Step B s w t := by
  have advance (t : State) (v' : Vector Word 16)
      (h : Holds index base v' t.mem B ∧ ∃ w, Step B s w t)
      (a b c d : Fin 16)
      (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (had : a.val ≠ d.val)
      (hbc : b.val ≠ c.val) (hbd : b.val ≠ d.val) (hcd : c.val ≠ d.val) :
      WP isa (Impl.Argon2.X86.gbAt (index a).val (index b).val (index c).val (index d).val)
        t fun u => Holds index base (GB v' a b c d) u.mem B ∧ ∃ w, Step B s w u := by
    obtain ⟨hh, w, st⟩ := h
    refine (step_ok hfit index hi (hs.of_step st) base v' hh a b c d
      hab hac had hbc hbd hcd).mono ?_
    rintro u ⟨hu, w', st'⟩
    exact ⟨hu, w', st.trans st'⟩
  unfold Impl.Argon2.X86.permuteAt
  apply WP.seq
  refine (advance s _ ⟨hv, _, ⟨.refl s, rfl, Frame.refl _ _⟩⟩ 0 4 8 12
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s1 h1
  apply WP.seq
  refine (advance s1 _ h1 1 5 9 13
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s2 h2
  apply WP.seq
  refine (advance s2 _ h2 2 6 10 14
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s3 h3
  apply WP.seq
  refine (advance s3 _ h3 3 7 11 15
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s4 h4
  apply WP.seq
  refine (advance s4 _ h4 0 5 10 15
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s5 h5
  apply WP.seq
  refine (advance s5 _ h5 1 6 11 12
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s6 h6
  apply WP.seq
  refine (advance s6 _ h6 2 7 8 13
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s7 h7
  exact advance s7 _ h7 3 4 9 14
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The row/column code meets the specification's gather, P, scatter definition. -/
theorem permuteAt_ok (index : Fin 16 → Fin 128) (hi : Function.Injective index) {s : State}
    (hs : At B s) :
    WP isa (Impl.Argon2.X86.permuteAt index) s
      (Step B s (Spec.Argon2.permuteAt index (working s.mem B))) := by
  refine (permuteAt_holds hfit index hi hs (working s.mem B)
    (gather index (working s.mem B)) ⟨rfl, fun _ _ => rfl⟩).mono ?_
  rintro t ⟨ht, w, st⟩
  exact ⟨st.keep, eq_scatter index hi _ _ _ ht.1 ht.2, st.frame⟩

/-- A list of row or column permutations. -/
theorem rounds_ok (index : Fin 8 → Fin 16 → Fin 128)
    (hi : ∀ i, Function.Injective (index i)) (is : List (Fin 8)) {s : State} (hs : At B s) :
    WP isa (is.foldr (fun i rest => .seq (Impl.Argon2.X86.permuteAt (index i)) rest)
      (.block [])) s
      (Step B s (is.foldl (fun b i => Spec.Argon2.permuteAt (index i) b) (working s.mem B))) := by
  induction is generalizing s with
  | nil => exact WP.block_nil ⟨.refl s, rfl, Frame.refl _ _⟩
  | cons i is ih =>
    apply WP.seq
    refine (permuteAt_ok hfit (index i) (hi i) hs).mono ?_
    intro t st
    refine (ih (hs.of_step st)).mono ?_
    intro u st'
    refine st.trans ?_
    rw [List.foldl_cons, ← st.working]
    exact st'

end

end VG.Proof.Argon2.X86

end

/-!
# Argon2 on x86 (32-bit): blocks as 32-bit words

A block at `B + o` (`blk m B o`) as 64-bit words, each the pair of 32-bit words
the code copies: `blk_of_words` builds it from them, `blockAt_eq` relates it to
the contract's `Spec.Argon2.blockAt`, and `xor_words` XORs two blocks word by
word.
-/

namespace VG.Proof.Argon2.X86

open VG VG.X86 VG.Spec.Argon2
open VG.Proof.Sha512.X86 (rd64)
open VG.Proof.Sha512.Word64 (lo hi lo_xor hi_xor lo_append hi_append eq_of_lo_hi)

/-- The block at `B + o`, as pairs of 32-bit words. -/
def blk (m : Mem) (B : BitVec 32) (o : Nat) : Block := Vector.ofFn fun j => rd64 m B (o + 8 * j.val)

/-- The block made of the 32-bit words `f 0, f 1, …` (two per 64-bit word, the low one first). -/
def ofWords (f : Nat → BitVec 32) : Block := Vector.ofFn fun j => f (2 * j.val + 1) ++ f (2 * j.val)

theorem blk_of_words {m : Mem} {B : BitVec 32} {o : Nat} {f : Nat → BitVec 32}
    (h : ∀ i < 256, m.readW (addr B (o + 4 * i)) 32 = f i) : blk m B o = ofWords f := by
  apply Vector.ext
  intro j hj
  simp only [blk, ofWords, Vector.getElem_ofFn, rd64]
  rw [show o + 8 * j + 4 = o + 4 * (2 * j + 1) by omega, show o + 8 * j = o + 4 * (2 * j) by omega,
    h _ (by omega), h _ (by omega)]

theorem working_eq (m : Mem) (B : BitVec 32) : working m B = blk m B 1024 := by
  apply Vector.ext
  intro j hj
  simp only [working, blk, Vector.getElem_ofFn, Impl.Argon2.X86.wOff]

theorem blockAt_eq {m : Mem} {B : BitVec 32} (hfit : B.toNat + 1024 ≤ 2 ^ 32) :
    blockAt m (B.setWidth 64) = blk m B 0 := by
  apply Vector.ext
  intro j hj
  simp only [blockAt, blk, Vector.getElem_ofFn, Nat.zero_add]
  rw [Proof.Blake2.X86.CompressB.rd64_eq (by omega)]
  simp only [Mem.readW, BitVec.setWidth_eq]

theorem append_xor (a b c d : BitVec 32) : (a ++ b) ^^^ (c ++ d) = (a ^^^ c) ++ (b ^^^ d) :=
  eq_of_lo_hi (by rw [lo_xor, lo_append, lo_append, lo_append])
    (by rw [hi_xor, hi_append, hi_append, hi_append])

theorem xor_words (f g : Nat → BitVec 32) :
    xorBlock (ofWords f) (ofWords g) = ofWords fun i => f i ^^^ g i := by
  apply Vector.ext
  intro j hj
  simp only [xorBlock, ofWords, Vector.getElem_zipWith, Vector.getElem_ofFn, append_xor]

/-- A prefix of `n` 32-bit words at `B + o` holds `f`. -/
def Words (m : Mem) (B : BitVec 32) (o : Nat) (f : Nat → BitVec 32) (n : Nat) : Prop :=
  ∀ i < n, m.readW (addr B (o + 4 * i)) 32 = f i

end VG.Proof.Argon2.X86

end

/-!
# Argon2 compression on x86 (32-bit): the contract of the proof

`compressX86`: the contract the proof is written against, with the arguments
on the stack only read; `Spec.Argon2.compressContract`, which lets the code
write them, is reached by narrowing (`Proof/Argon2/X86/CompressVerified.lean`).
`Pre` names the facts of its precondition.
-/

namespace VG.Proof.Argon2.X86

open VG VG.X86 VG.Spec.Argon2
open VG.Proof.Sha512.X86 (Acc mem_rd)
open VG.Proof.Sha256.X86.Stream (contains_addr)

/-- `vg_argon2_compress(x, y, out, scratch)`: reads the arguments (16 bytes
above the return address) and the two input blocks, writes the output block
and 4096 bytes of scratch. -/
def compressX86 : Contract X86.isa where
  pre s :=
    let x : Region := ⟨(arg s 0).setWidth 64, 1024⟩
    let y : Region := ⟨(arg s 1).setWidth 64, 1024⟩
    let out : Region := ⟨(arg s 2).setWidth 64, 1024⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 4096⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [x, y, args] ∧ s.wr = [out, scratch] ∧
    out.Disjoint scratch ∧ x.Disjoint out ∧ x.Disjoint scratch ∧ y.Disjoint out ∧
    y.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧ ret.Disjoint out ∧
    ret.Disjoint scratch ∧
    (arg s 0).toNat + 1024 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 1024 ≤ 2 ^ 32 ∧
    (arg s 2).toNat + 1024 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 4096 ≤ 2 ^ 32 ∧
    (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  post s s' := blockAt s'.mem ((arg s 2).setWidth 64) =
    compress (blockAt s.mem ((arg s 0).setWidth 64)) (blockAt s.mem ((arg s 1).setWidth 64))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

section
variable (s₀ : State)

abbrev xp : BitVec 32 := arg s₀ 0
abbrev yp : BitVec 32 := arg s₀ 1
abbrev op : BitVec 32 := arg s₀ 2
abbrev scr : BitVec 32 := arg s₀ 3
abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev xR : Region := ⟨(xp s₀).setWidth 64, 1024⟩
abbrev yR : Region := ⟨(yp s₀).setWidth 64, 1024⟩
abbrev outR : Region := ⟨(op s₀).setWidth 64, 1024⟩
abbrev scrR : Region := ⟨(scr s₀).setWidth 64, 4096⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 16⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [xR s₀, yR s₀, argR s₀]
  wr : s₀.wr = [outR s₀, scrR s₀]
  out_scr : (outR s₀).Disjoint (scrR s₀)
  x_out : (xR s₀).Disjoint (outR s₀)
  x_scr : (xR s₀).Disjoint (scrR s₀)
  y_out : (yR s₀).Disjoint (outR s₀)
  y_scr : (yR s₀).Disjoint (scrR s₀)
  arg_out : (argR s₀).Disjoint (outR s₀)
  arg_scr : (argR s₀).Disjoint (scrR s₀)
  ret_out : (retR s₀).Disjoint (outR s₀)
  ret_scr : (retR s₀).Disjoint (scrR s₀)
  x_fits : (xp s₀).toNat + 1024 ≤ 2 ^ 32
  y_fits : (yp s₀).toNat + 1024 ≤ 2 ^ 32
  out_fits : (op s₀).toNat + 1024 ≤ 2 ^ 32
  scr_fits : (scr s₀).toNat + 4096 ≤ 2 ^ 32
  esp_fits : (esp₀ s₀).toNat + 20 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : compressX86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem acc {s : State} (hw : s.wr = s₀.wr) : Acc s.wr (scr s₀) 4096 :=
  VG.Proof.Sha512.X86.Acc.of_mem (by rw [hw, hp.wr]; simp) hp.scr_fits

theorem in_scr {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 4096) :
    InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 :=
  mem_rd (hp.acc hw d hd)

theorem out_wr {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 1024) :
    InRegions s.wr (addr (op s₀) d) 4 :=
  ⟨outR s₀, by simp [hw, hp.wr], contains_addr hd (by omega) hp.out_fits⟩

theorem in_x {s : State} (hrd : s.rd = s₀.rd) {d : Nat} (hd : d + 4 ≤ 1024) :
    InRegions (s.rd ++ s.wr) (addr (xp s₀) d) 4 :=
  ⟨xR s₀, by simp [hrd, hp.rd], contains_addr hd (by omega) hp.x_fits⟩

theorem in_y {s : State} (hrd : s.rd = s₀.rd) {d : Nat} (hd : d + 4 ≤ 1024) :
    InRegions (s.rd ++ s.wr) (addr (yp s₀) d) 4 :=
  ⟨yR s₀, by simp [hrd, hp.rd], contains_addr hd (by omega) hp.y_fits⟩

theorem argAddr_eq {d : Nat} (hd : d < 20) :
    addr (esp₀ s₀) d = (esp₀ s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.esp_fits; omega)

theorem arg_contains {d : Nat} (hd : 4 ≤ d) (hd' : d + 4 ≤ 20) :
    (argR s₀).Contains (addr (esp₀ s₀) d) 4 := by
  show (⟨addr (esp₀ s₀) 4, 16⟩ : Region).Contains _ _
  rw [hp.argAddr_eq (by omega), hp.argAddr_eq (by omega)]
  exact Offset.contains _ hd (by omega) (by omega)

theorem in_arg {s : State} (hrd : s.rd = s₀.rd) {d : Nat} (hd : 4 ≤ d) (hd' : d + 4 ≤ 20) :
    InRegions (s.rd ++ s.wr) (addr (esp₀ s₀) d) 4 :=
  ⟨argR s₀, by simp [hrd, hp.rd], hp.arg_contains hd hd'⟩

/-- An argument is unchanged while only `out` and `scratch` are written. -/
theorem arg_frame {m : Mem} (hf : Frame [outR s₀, scrR s₀] s₀.mem m) {d : Nat} (hd : 4 ≤ d)
    (hd' : d + 4 ≤ 20) : m.readW (addr (esp₀ s₀) d) 32 = s₀.mem.readW (addr (esp₀ s₀) d) 32 := by
  refine hf.readW (r := argR s₀) (hp.arg_contains hd hd') ?_ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨hp.arg_out, hp.arg_scr⟩

/-- A word of `x` is unchanged while only `out` and `scratch` are written. -/
theorem x_frame {m : Mem} (hf : Frame [outR s₀, scrR s₀] s₀.mem m) {d : Nat} (hd : d + 4 ≤ 1024) :
    m.readW (addr (xp s₀) d) 32 = s₀.mem.readW (addr (xp s₀) d) 32 := by
  refine hf.readW (r := xR s₀) (contains_addr hd (by omega) hp.x_fits) ?_ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨hp.x_out, hp.x_scr⟩

theorem y_frame {m : Mem} (hf : Frame [outR s₀, scrR s₀] s₀.mem m) {d : Nat} (hd : d + 4 ≤ 1024) :
    m.readW (addr (yp s₀) d) 32 = s₀.mem.readW (addr (yp s₀) d) 32 := by
  refine hf.readW (r := yR s₀) (contains_addr hd (by omega) hp.y_fits) ?_ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨hp.y_out, hp.y_scr⟩

/-- A word of `scratch` is unchanged while only `out` is written. -/
theorem scr_frame {m m' : Mem} (hf : Frame [outR s₀] m m') {d : Nat} (hd : d + 4 ≤ 4096) :
    m'.readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 := by
  refine hf.readW (r := scrR s₀) (contains_addr hd (by omega) hp.scr_fits) ?_ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
  exact hp.out_scr.symm

end Pre

end VG.Proof.Argon2.X86

end

/-!
# Argon2 compression on x86 (32-bit): correctness

The prologue (`prologue_ok`), the initialization of both halves of scratch
with X XOR Y (`init_ok`, one word at a time), the rows and columns
(`Proof/Argon2/X86/Rounds.lean`), and the epilogue writing the output and
restoring `esi` (`epilogue_ok`): `correct`.
-/

namespace VG.Proof.Argon2.X86

open VG VG.X86 VG.Spec.Argon2
open VG.Impl.Argon2.X86 (prologue initWord finishWord epilogue savedOff)
open VG.Proof.Sha512.X86 (Acc rd64 mem_rd ea_of)
open VG.Proof.Sha256.X86.Stream (contains_addr Upd Mupd wp_movm wp_store wp_mov readW_writeW_addr)

/-- 32-bit word `i` of X XOR Y. -/
def xy (s₀ : State) (i : Nat) : BitVec 32 :=
  s₀.mem.readW (addr (xp s₀) (4 * i)) 32 ^^^ s₀.mem.readW (addr (yp s₀) (4 * i)) 32

/-- After the prologue and the first `n` words of the initialization. -/
structure InitInv (s₀ s : State) (n : Nat) : Prop where
  esi : s.gpr .esi = scr s₀
  ecx : s.gpr .ecx = xp s₀
  edx : s.gpr .edx = yp s₀
  regs : ∀ r, r ≠ .eax → r ≠ .esi → r ≠ .ecx → r ≠ .edx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [outR s₀, scrR s₀] s₀.mem s.mem
  saved : s.mem.readW (addr (scr s₀) savedOff) 32 = s₀.gpr .esi
  low : Words s.mem (scr s₀) 0 (xy s₀) n
  high : Words s.mem (scr s₀) 1024 (xy s₀) n

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem scr_contains {d : Nat} (hd : d + 4 ≤ 4096) : (scrR s₀).Contains (addr (scr s₀) d) (32 / 8) :=
  contains_addr hd (by omega) hp.scr_fits

theorem prologue_ok :
    WP isa (.block prologue) s₀ (InitInv s₀ · 0) := by
  have hm : scrR s₀ ∈ [outR s₀, scrR s₀] := by simp
  unfold prologue
  refine wp_movm (ea_of rfl 16) (hp.in_arg (d := 16) rfl (by omega) (by omega)) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = scr s₀ := u₁.gpr
  refine wp_store (ea_of e₁ savedOff) (by rw [u₁.wr]; exact hp.acc rfl _ (by decide)) fun s₂ u₂ => ?_
  have f₂ : Frame [outR s₀, scrR s₀] s₀.mem s₂.mem := by
    rw [u₂.mem, u₁.mem]; exact (Frame.refl _ _).writeW hm _ (scr_contains hp (by decide))
  refine wp_mov fun s₃ u₃ => ?_
  have sp₃ : s₃.gpr .esp = esp₀ s₀ := by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]
  refine wp_movm (ea_of sp₃ 4) (by rw [u₃.rd, u₂.rd, u₁.rd, u₃.wr, u₂.wr, u₁.wr]; exact hp.in_arg (d := 4) rfl (by omega) (by omega))
    fun s₄ u₄ => ?_
  refine wp_movm (ea_of (by rw [u₄.other _ (by decide), sp₃]) 8)
    (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hp.in_arg (d := 8) rfl (by omega) (by omega)) fun s₅ u₅ => ?_
  have m₅ : s₅.mem = s₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  refine WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => absurd hi (Nat.not_lt_zero _),
    fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, e₁]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.mem, hp.arg_frame f₂ (by omega) (by omega)]; rfl
  · rw [u₅.gpr, u₄.mem, u₃.mem, hp.arg_frame f₂ (by omega) (by omega)]; rfl
  · intro r h0 h6 h1 h2
    rw [u₅.other _ h2, u₄.other _ h1, u₃.other _ h6, u₂.gpr, u₁.other _ h0]
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [m₅]; exact f₂
  · rw [m₅, u₂.mem, Mem.readW_writeW_self32, u₁.other _ (by decide)]

/-- One word of the initialization. -/
theorem initWord_ok {s : State} {n : Nat} (hn : n < 256) (h : InitInv s₀ s n) :
    WP isa (.block (initWord n)) s (InitInv s₀ · (n + 1)) := by
  have hm : scrR s₀ ∈ [outR s₀, scrR s₀] := by simp
  have fits := hp.scr_fits
  unfold initWord
  refine wp_movm (ea_of h.ecx _) (hp.in_x h.rd (by omega)) fun s₁ u₁ => ?_
  refine VG.Proof.Sha512.X86.wp_xorS (VG.Proof.Sha512.X86.readSrc_mem
    (by rw [u₁.other _ (by decide), h.edx]) (by rw [u₁.rd, u₁.wr]; exact hp.in_y h.rd (by omega)))
    fun s₂ u₂ => ?_
  have v₂ : s₂.gpr .eax = xy s₀ n := by
    rw [u₂.gpr, u₁.gpr, u₁.mem, hp.x_frame h.frame (by omega), hp.y_frame h.frame (by omega)]; rfl
  have esi₂ : s₂.gpr .esi = scr s₀ := by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.esi]
  refine wp_store (ea_of esi₂ _) (by rw [u₂.wr, u₁.wr, h.wr]; exact hp.acc rfl _ (by omega))
    fun s₃ u₃ => ?_
  have w₃ : InRegions s₃.wr (addr (scr s₀) (1024 + 4 * n)) 4 := by
    rw [u₃.wr, u₂.wr, u₁.wr, h.wr]; exact hp.acc rfl _ (by omega)
  refine wp_store (ea_of (by rw [u₃.gpr, esi₂]) _) w₃ fun s₄ u₄ => WP.block_nil ?_
  have m₄ : s₄.mem = (s.mem.writeW (addr (scr s₀) (4 * n)) (xy s₀ n)).writeW
      (addr (scr s₀) (1024 + 4 * n)) (xy s₀ n) := by
    rw [u₄.mem, u₃.gpr, u₃.mem, u₂.mem, u₁.mem, v₂]
  have r₄ : ∀ e, e + 4 ≤ 4096 → (e + 4 ≤ 4 * n ∨ 4 * n + 4 ≤ e) →
      (e + 4 ≤ 1024 + 4 * n ∨ 1024 + 4 * n + 4 ≤ e) →
      s₄.mem.readW (addr (scr s₀) e) 32 = s.mem.readW (addr (scr s₀) e) 32 := by
    intro e he h1 h2
    rw [m₄, readW_writeW_addr _ _ (by omega) (by omega) h2,
      readW_writeW_addr _ _ (by omega) (by omega) h1]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₄.gpr, u₃.gpr, esi₂]
  · rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.ecx]
  · rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.edx]
  · intro r h0 h6 h1 h2
    rw [u₄.gpr, u₃.gpr, u₂.other _ h0, u₁.other _ h0, h.regs r h0 h6 h1 h2]
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [m₄]
    exact (h.frame.writeW hm _ (scr_contains hp (by omega))).writeW hm _ (scr_contains hp (by omega))
  · rw [r₄ _ (by decide) (by simp only [savedOff]; omega) (by simp only [savedOff]; omega)]
    exact h.saved
  · intro i hi
    by_cases e : i = n
    · subst e
      rw [m₄, readW_writeW_addr _ _ (by omega) (by omega) (by omega), Nat.zero_add,
        Mem.readW_writeW_self32]
    · rw [r₄ _ (by omega) (by omega) (by omega)]; exact h.low i (by omega)
  · intro i hi
    by_cases e : i = n
    · subst e; rw [m₄, Mem.readW_writeW_self32]
    · rw [r₄ _ (by omega) (by omega) (by omega)]; exact h.high i (by omega)

theorem init_ok {s : State} (h : InitInv s₀ s 0) (n : Nat) (hn : n ≤ 256) :
    WP isa (.block ((List.range n).flatMap initWord)) s (InitInv s₀ · n) := by
  induction n with
  | zero => exact WP.block_nil h
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    exact WP.block_append ((ih (by omega)).mono fun t ht => initWord_ok hp (by omega) ht)

end

/-! ## The epilogue -/

/-- Word `i` of the output: the permuted block XOR R, in memory `m`. -/
def outWord (B : BitVec 32) (m : Mem) (i : Nat) : BitVec 32 :=
  m.readW (addr B (1024 + 4 * i)) 32 ^^^ m.readW (addr B (4 * i)) 32

/-- After the first `n` words of the output, from the state `s₄` after the rounds. -/
structure FinInv (s₀ s₄ s : State) (n : Nat) : Prop where
  esi : s.gpr .esi = scr s₀
  ecx : s.gpr .ecx = op s₀
  regs : ∀ r, r ≠ .eax → r ≠ .ecx → s.gpr r = s₄.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [outR s₀] s₄.mem s.mem
  out : Words s.mem (op s₀) 0 (outWord (scr s₀) s₄.mem) n

section
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem finishWord_ok {s₄ s : State} {n : Nat} (hn : n < 256) (h : FinInv s₀ s₄ s n) :
    WP isa (.block (finishWord n)) s (FinInv s₀ s₄ · (n + 1)) := by
  have hm : outR s₀ ∈ [outR s₀] := List.mem_singleton_self _
  have fits := hp.out_fits
  unfold finishWord
  refine wp_movm (ea_of h.esi _) (hp.in_scr h.wr (by omega)) fun s₁ u₁ => ?_
  refine VG.Proof.Sha512.X86.wp_xorS (VG.Proof.Sha512.X86.readSrc_mem
    (by rw [u₁.other _ (by decide), h.esi]) (by rw [u₁.rd, u₁.wr]; exact hp.in_scr h.wr (by omega)))
    fun s₂ u₂ => ?_
  have v₂ : s₂.gpr .eax = outWord (scr s₀) s₄.mem n := by
    rw [u₂.gpr, u₁.gpr, u₁.mem, hp.scr_frame h.frame (by omega), hp.scr_frame h.frame (by omega)]; rfl
  refine wp_store (ea_of (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.ecx]) _)
    (by rw [u₂.wr, u₁.wr, h.wr]; exact hp.out_wr rfl (by omega)) fun s₃ u₃ => WP.block_nil ?_
  have m₃ : s₃.mem = s.mem.writeW (addr (op s₀) (4 * n)) (outWord (scr s₀) s₄.mem n) := by
    rw [u₃.mem, u₂.mem, u₁.mem, v₂]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.esi]
  · rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.ecx]
  · intro r h0 h1
    rw [u₃.gpr, u₂.other _ h0, u₁.other _ h0, h.regs r h0 h1]
  · rw [u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [m₃]; exact h.frame.writeW hm _ (contains_addr (by omega) (by omega) fits)
  · intro i hi
    rw [m₃, Nat.zero_add]
    by_cases e : i = n
    · subst e; rw [Mem.readW_writeW_self32]
    · rw [readW_writeW_addr _ _ (by omega) (by omega) (by omega)]
      have := h.out i (by omega); rwa [Nat.zero_add] at this

theorem finish_ok {s₄ s : State} (h : FinInv s₀ s₄ s 0) (n : Nat) (hn : n ≤ 256) :
    WP isa (.block ((List.range n).flatMap finishWord)) s (FinInv s₀ s₄ · n) := by
  induction n with
  | zero => exact WP.block_nil h
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    exact WP.block_append ((ih (by omega)).mono fun t ht => finishWord_ok hp (by omega) ht)

end

end VG.Proof.Argon2.X86

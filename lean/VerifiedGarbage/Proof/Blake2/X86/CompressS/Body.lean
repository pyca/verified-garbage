import VerifiedGarbage.Proof.Blake2.X86.Stream.Common
import VerifiedGarbage.Proof.Blake2.X86.Contract
import VerifiedGarbage.Proof.Blake2.X86.CompressS.Round
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.MdStream.X86.Common
import VerifiedGarbage.Proof.Blake2.Spec
import VerifiedGarbage.Impl.Blake2.X86.CompressS

section

/-!
# BLAKE2s on x86 (32-bit): words of `scratch`

`workR`, the first 64 bytes of `scratch`, which only the code that sets up
the work vector writes, and reading its words after writes.
-/

namespace VG.Proof.Blake2.X86.CompressS

open VG VG.X86
open VG.Impl.Blake2.X86.CompressS
open VG.Proof.MdStream.X86 (readW_writeW_addr)

/-- The first 64 bytes of `scratch`. -/
abbrev workR (B : BitVec 32) : Region := ⟨B.setWidth 64, 64⟩

theorem mem_rd {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions wr a n) :
    InRegions (rd ++ wr) a n :=
  let ⟨r, hr, hc⟩ := h
  ⟨r, List.mem_append_right _ hr, hc⟩

theorem rw_slot {B : BitVec 32} (hfit : B.toNat + 64 ≤ 2 ^ 32) (m : Mem) (x : BitVec 32) {i k : Nat}
    (hi : i < 16) (hk : k < 16) :
    (m.writeW (addr B (vOff i)) x).readW (addr B (vOff k)) 32 =
      if i = k then x else m.readW (addr B (vOff k)) 32 := by
  by_cases h : i = k
  · subst h; simp only [Mem.readW_writeW_self32, ite_true]
  · simp only [h, ite_false]
    exact readW_writeW_addr m x (by simp only [vOff]; omega) (by simp only [vOff]; omega)
      (by simp only [vOff]; omega)

/-- Doubleword `i` of 16 bytes loaded from `[B + d]`. -/
theorem dword_load (m : Mem) {B : BitVec 32} {d i : Nat} (hfit : B.toNat + d + 16 ≤ 2 ^ 32)
    (hi : i < 4) : dword (m.readW (addr B d) 128) i = m.readW (addr B (d + 4 * i)) 32 := by
  rw [addr_eq (by omega), addr_eq (by omega), dword_readW _ _ hi, Offset.add_add]

/-- Doubleword `i` of 16 bytes stored to `[B + d]`, read back. -/
theorem load_write_self (m : Mem) {B : BitVec 32} {d i : Nat} (v : BitVec 128)
    (hfit : B.toNat + d + 16 ≤ 2 ^ 32) (hi : i < 4) :
    (m.writeW (addr B d) v).readW (addr B (d + 4 * i)) 32 = dword v i := by
  rw [show addr B (d + 4 * i) = addr B d + BitVec.ofNat 64 (4 * i) by
    rw [addr_eq (by omega), addr_eq (by omega), Offset.add_add], readW_writeW128 _ _ _ hi]

end VG.Proof.Blake2.X86.CompressS

end

section

/-!
# BLAKE2s on x86 (32-bit): the compression function's precondition

`Pre` unpacks the precondition of `compressX86 Spec.Blake2.s`; its lemmas
locate the words the code reads and writes. Also `V0` and `F_eq`: `F` in the
order of the code.
-/

namespace VG.Proof.Blake2.X86.CompressS

open VG VG.X86 VG.X86.Wp
open VG.Spec.Blake2 (Work Block HashValue blockBytes stateAt blockAt compressBlocks)
open VG.Impl.Blake2.X86.CompressS
open VG.Proof.MdStream.X86 (contains_addr readW_writeW_addr)

/-! ## The compression function, in the order of the code -/

/-- The work vector before the rounds (RFC 7693 §3.2). -/
def V0 (h : HashValue 32) (t : Nat) (f : Bool) : Work 32 :=
  let v : Work 32 := h ++ Spec.Blake2.s.IV
  let v := v.set 12 (v[12] ^^^ BitVec.ofNat 32 t)
  let v := v.set 13 (v[13] ^^^ BitVec.ofNat 32 (t / 2 ^ 32))
  if f then v.set 14 (v[14] ^^^ BitVec.allOnes 32) else v

theorem F_eq (h : HashValue 32) (m : Block 32) (t : Nat) (f : Bool) :
    Spec.Blake2.F Spec.Blake2.s h m t f = Vector.ofFn fun i : Fin 8 =>
      h[i] ^^^ ((List.range 10).foldl (Spec.Blake2.round Spec.Blake2.s m) (V0 h t f))[i] ^^^
        ((List.range 10).foldl (Spec.Blake2.round Spec.Blake2.s m) (V0 h t f))[i.val + 8] := rfl

/-- The final block flag as a word. -/
def flagW (f : Bool) : BitVec 32 := if f then BitVec.allOnes 32 else 0

theorem V0_get (h : HashValue 32) (t : Nat) (f : Bool) (k : Nat) (hk : k < 16) : (V0 h t f)[k] =
    if hk8 : k < 8 then h[k] else if k = 12 then Spec.Blake2.s.IV[4] ^^^ BitVec.ofNat 32 t
    else if k = 13 then Spec.Blake2.s.IV[5] ^^^ BitVec.ofNat 32 (t / 2 ^ 32)
    else if k = 14 then Spec.Blake2.s.IV[6] ^^^ flagW f else Spec.Blake2.s.IV[k - 8]'(by omega) := by
  have base : ((h ++ Spec.Blake2.s.IV : Work 32))[k] =
      if hk8 : k < 8 then h[k] else Spec.Blake2.s.IV[k - 8]'(by omega) := by
    simp only [Vector.getElem_append]
  have e12 : (h ++ Spec.Blake2.s.IV : Work 32)[12] = Spec.Blake2.s.IV[4] := by
    simp only [Vector.getElem_append]; rfl
  have e13 : (h ++ Spec.Blake2.s.IV : Work 32)[13] = Spec.Blake2.s.IV[5] := by
    simp only [Vector.getElem_append]; rfl
  have e14 : (h ++ Spec.Blake2.s.IV : Work 32)[14] = Spec.Blake2.s.IV[6] := by
    simp only [Vector.getElem_append]; rfl
  by_cases k14 : k = 14
  · subst k14; cases f <;> simp [V0, flagW, e14]
  by_cases k13 : k = 13
  · subst k13; cases f <;> simp [V0, e13]
  by_cases k12 : k = 12
  · subst k12; cases f <;> simp [V0, e12]
  have n14 : ¬14 = k := Ne.symm k14
  have n13 : ¬13 = k := Ne.symm k13
  have n12 : ¬12 = k := Ne.symm k12
  cases f <;> simp only [V0, Vector.getElem_set, n14, n13, n12, k14, k13, k12, ite_false, base,
    Bool.false_eq_true, ite_true]

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := arg s₀ 0
abbrev bp : BitVec 32 := arg s₀ 1
abbrev nb : Nat := (arg s₀ 2).toNat
abbrev t₀ : Nat := (arg s₀ 4 ++ arg s₀ 3).toNat
abbrev fl : Bool := arg s₀ 5 != 0
abbrev scr : BitVec 32 := arg s₀ 6
abbrev stR : Region := ⟨(st s₀).setWidth 64, 32⟩
abbrev blR : Region := ⟨(bp s₀).setWidth 64, 64 * nb s₀⟩
abbrev scrR : Region := ⟨(scr s₀).setWidth 64, 512⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 28⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩
abbrev H₀ : HashValue 32 := stateAt 32 s₀.mem ((st s₀).setWidth 64)

/-- Where block `i` starts. -/
abbrev blkAddr (i : Nat) : BitVec 32 := bp s₀ + BitVec.ofNat 32 (64 * i)

/-- Block `i`, as `compressBlocks` reads it. -/
abbrev blk (i : Nat) : Block 32 :=
  blockAt 32 s₀.mem ((bp s₀).setWidth 64 + BitVec.ofNat 64 (blockBytes 32 * i))

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [blR s₀, argR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)
  blk_st : (blR s₀).Disjoint (stR s₀)
  blk_scr : (blR s₀).Disjoint (scrR s₀)
  arg_st : (argR s₀).Disjoint (stR s₀)
  arg_scr : (argR s₀).Disjoint (scrR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_scr : (retR s₀).Disjoint (scrR s₀)
  st_fits : (st s₀).toNat + 32 ≤ 2 ^ 32
  blk_fits : (bp s₀).toNat + 64 * nb s₀ ≤ 2 ^ 32
  scr_fits : (scr s₀).toNat + 512 ≤ 2 ^ 32
  esp_fits : (esp₀ s₀).toNat + 32 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : (Proof.Blake2.compressX86 Spec.Blake2.s).pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

/-- The callee-saved registers are saved in `scratch`. -/
abbrev Saved (s₀ : State) (m : Mem) : Prop := Spill.Saved m (addr (scr s₀)) s₀.gpr saved

theorem saved_fits : Spill.Fits 92 saved := by decide

theorem saved_bound : ∀ p ∈ saved, 80 ≤ p.2 ∧ p.2 + 4 ≤ 92 := by decide

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem in_st {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 32) :
    InRegions s.wr (addr (st s₀) d) 4 :=
  ⟨stR s₀, by simp [hw, h.wr], contains_addr hd (by omega) h.st_fits⟩

theorem in_scr {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 512) :
    InRegions s.wr (addr (scr s₀) d) 4 :=
  ⟨scrR s₀, by simp [hw, h.wr], contains_addr hd (by omega) h.scr_fits⟩

theorem argAddr_eq {d : Nat} (hd : d < 32) :
    addr (esp₀ s₀) d = (esp₀ s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := h.esp_fits; omega)

theorem arg_contains {d : Nat} (hd : 4 ≤ d) (hd' : d + 4 ≤ 32) :
    (argR s₀).Contains (addr (esp₀ s₀) d) 4 := by
  show (⟨addr (esp₀ s₀) 4, 28⟩ : Region).Contains _ _
  rw [h.argAddr_eq (by omega), h.argAddr_eq (by omega)]
  exact Offset.contains _ hd (by omega) (by omega)

theorem in_arg {s : State} (hrd : s.rd = s₀.rd) {d : Nat} (hd : 4 ≤ d) (hd' : d + 4 ≤ 32) :
    InRegions (s.rd ++ s.wr) (addr (esp₀ s₀) d) 4 :=
  ⟨argR s₀, by simp [hrd, h.rd], h.arg_contains hd hd'⟩

theorem arg_sub {i : Nat} (hi : i < 7) : Region.Sub ⟨argAddr s₀ i, 4⟩ (argR s₀) := by
  show Region.Sub ⟨addr (esp₀ s₀) (4 + 4 * i), 4⟩ ⟨addr (esp₀ s₀) 4, 28⟩
  rw [h.argAddr_eq (by omega), h.argAddr_eq (by omega)]
  exact Offset.sub _ (by omega) (by omega)

/-- The arguments are unchanged while only the state and `scratch` are written. -/
theorem arg_frame {m : Mem} (hf : Frame [stR s₀, scrR s₀] s₀.mem m) {i : Nat} (hi : i < 7) :
    m.readW (addr (esp₀ s₀) (4 + 4 * i)) 32 = arg s₀ i := by
  refine (hf.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) ?_ (by decide))
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨h.arg_st.sub_left (h.arg_sub hi), h.arg_scr.sub_left (h.arg_sub hi)⟩

theorem blk_toNat {i : Nat} (hi : i < nb s₀) : (blkAddr s₀ i).toNat = (bp s₀).toNat + 64 * i := by
  have := h.blk_fits
  simp only [blkAddr, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := 64 * i) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem blk_word {i : Nat} (hi : i < nb s₀) {o : Nat} (ho : o + 4 ≤ 64) :
    addr (blkAddr s₀ i) o = (bp s₀).setWidth 64 + BitVec.ofNat 64 (64 * i + o) := by
  rw [show addr (blkAddr s₀ i) o = addr (bp s₀) (64 * i + o) by
    simp only [addr, blkAddr, BitVec.add_assoc, BitVec.ofNat_add]]
  exact addr_eq (by have := h.blk_fits; have : i + 1 ≤ nb s₀ := hi; omega)

theorem blk_contains {i : Nat} (hi : i < nb s₀) {o : Nat} (ho : o + 4 ≤ 64) :
    (blR s₀).Contains (addr (blkAddr s₀ i) o) 4 := by
  rw [h.blk_word hi ho]
  have := h.blk_fits
  exact Offset.contains_base _ (by have : i + 1 ≤ nb s₀ := hi; omega) (by omega)

theorem scr_contains {d : Nat} (hd : d + 4 ≤ 512) : (scrR s₀).Contains (addr (scr s₀) d) 4 :=
  contains_addr hd (by omega) h.scr_fits

theorem st_contains {d : Nat} (hd : d + 4 ≤ 32) : (stR s₀).Contains (addr (st s₀) d) 4 :=
  contains_addr hd (by omega) h.st_fits

/-- The words of block `i` are readable. -/
theorem blk_rd {i : Nat} (hi : i < nb s₀) :
    ∀ j < 16, InRegions (s₀.rd ++ s₀.wr) (addr (blkAddr s₀ i) (4 * j)) 4 :=
  fun _ hj => ⟨blR s₀, by simp [h.rd], h.blk_contains hi (by omega)⟩

/-- Block `i`, while only the state and `scratch` are written. -/
theorem msg {i : Nat} (hi : i < nb s₀) {m : Mem} (hf : Frame [stR s₀, scrR s₀] s₀.mem m) :
    Msg (blkAddr s₀ i) (blk s₀ i) m := by
  intro j
  have hj := j.isLt
  rw [hf.readW (r := blR s₀) (h.blk_contains hi (by omega)) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨h.blk_st, h.blk_scr⟩) (by decide),
    h.blk_word hi (by omega)]
  have e := Proof.Blake2.blockAt_word (w := 32) s₀.mem
    ((bp s₀).setWidth 64 + BitVec.ofNat 64 (blockBytes 32 * i)) j.1 hj
  rw [show blk s₀ i j = blk s₀ i ⟨j.1, hj⟩ from rfl, blk, e, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  rfl

/-- Word `k` of the state. -/
theorem stateAt_get (m : Mem) {k : Nat} (hk : k < 8) :
    (stateAt 32 m ((st s₀).setWidth 64))[k] = m.readW (addr (st s₀) (4 * k)) 32 := by
  simp only [stateAt, Vector.getElem_ofFn]
  rw [addr_eq (by have := h.st_fits; omega)]

theorem stateAt_ext {m : Mem} {H : HashValue 32}
    (hH : ∀ k (hk : k < 8), m.readW (addr (st s₀) (4 * k)) 32 = H[k]) :
    stateAt 32 m ((st s₀).setWidth 64) = H := by
  ext k hk
  rw [h.stateAt_get m hk, hH k hk]

/-- `scratch` beyond the work vector is unchanged while only the work vector,
or the state, is written. -/
theorem high_frame {m m' : Mem} (hf : Frame [workR (scr s₀)] m m' ∨ Frame [stR s₀] m m') {d : Nat}
    (hd : 64 ≤ d) (hd' : d + 4 ≤ 512) :
    m'.readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 := by
  have hc : (⟨addr (scr s₀) d, 4⟩ : Region).Contains (addr (scr s₀) d) (32 / 8) :=
    Region.contains_self _ _
  have := h.scr_fits
  rcases hf with hf | hf
  · refine hf.readW hc ?_ (by decide)
    simp only [List.mem_singleton, forall_eq]
    rw [addr_eq (by omega)]
    exact Offset.disjoint_base _ hd (by omega)
  · refine hf.readW hc ?_ (by decide)
    simp only [List.mem_singleton, forall_eq]
    refine Region.Disjoint.sub_left h.st_scr.symm ?_
    rw [addr_eq (by omega)]
    exact Offset.sub_base _ (by omega)

/-- The state is unchanged while only the work vector is written. -/
theorem st_frame {m m' : Mem} (hf : Frame [workR (scr s₀)] m m') {d : Nat} (hd : d + 4 ≤ 32) :
    m'.readW (addr (st s₀) d) 32 = m.readW (addr (st s₀) d) 32 := by
  refine hf.readW (r := stR s₀) (h.st_contains hd) ?_ (by decide)
  simp only [List.mem_singleton, forall_eq]
  exact h.st_scr.sub_right (Region.sub_prefix (by omega))

/-- The work vector is unchanged while only the state is written. -/
theorem work_frame {m m' : Mem} (hf : Frame [stR s₀] m m') {d : Nat} (hd : d + 4 ≤ 512) :
    m'.readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 := by
  refine hf.readW (r := scrR s₀) (h.scr_contains hd) ?_ (by decide)
  simp only [List.mem_singleton, forall_eq]
  exact h.st_scr.symm

theorem saved_frame {m m' : Mem} (hs : Saved s₀ m)
    (hf : Frame [workR (scr s₀)] m m' ∨ Frame [stR s₀] m m') : Saved s₀ m' :=
  hs.of_readW fun p hp => have hb := saved_bound p hp; h.high_frame hf (by omega) (by omega)

end Pre

end VG.Proof.Blake2.X86.CompressS

end

/-!
# BLAKE2s on x86 (32-bit): one block

`body_ok`: the loop body compresses block `i` into the state and advances to
the next block, from the loop invariant `LInv`.
-/

namespace VG.Proof.Blake2.X86.CompressS

open VG VG.X86 VG.X86.Wp
open VG.Spec.Blake2 (Work Block HashValue blockBytes stateAt blockAt compressBlocks)
open VG.Impl.Blake2.X86 (at_)
open VG.Impl.Blake2.X86.CompressS
open VG.Proof.MdStream.X86 (contains_addr readW_writeW_addr addr_sep)

/-! ## The loop invariant -/

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  esi : s.gpr .esi = scr s₀
  esp : s.gpr .esp = esp₀ s₀
  ebp : s.gpr .ebp = s₀.gpr .ebp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀, scrR s₀] s₀.mem s.mem
  state : stateAt 32 s.mem ((st s₀).setWidth 64) =
    compressBlocks Spec.Blake2.s (H₀ s₀) s₀.mem ((bp s₀).setWidth 64) i (t₀ s₀) (fl s₀)
  saved : Saved s₀ s.mem

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  edi : s.gpr .edi = blkAddr s₀ i
  tlo : s.mem.readW (addr (scr s₀) tloOff) 32 = BitVec.ofNat 32 (t₀ s₀ + i * 64)
  thi : s.mem.readW (addr (scr s₀) thiOff) 32 = BitVec.ofNat 32 ((t₀ s₀ + i * 64) / 2 ^ 32)
  flag : s.mem.readW (addr (scr s₀) fOff) 32 = flagW (fl s₀)
  cnt : s.mem.readW (addr (scr s₀) nOff) 32 = BitVec.ofNat 32 (nb s₀ - i)

/-! ## Words of `scratch` -/

section
variable {B : BitVec 32} (hfit : B.toNat + 512 ≤ 2 ^ 32)
include hfit

theorem rw_scr (m : Mem) (v : BitVec 32) {d e : Nat} (hd : d + 4 ≤ 512) (he : e + 4 ≤ 512)
    (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (addr B e) v).readW (addr B d) 32 = m.readW (addr B d) 32 :=
  readW_writeW_addr m v (by omega) (by omega) h

theorem rw_hi (m : Mem) (v : BitVec 32) {k d : Nat} (hk : k < 16) (hd : 64 ≤ d) (hd' : d + 4 ≤ 512) :
    (m.writeW (addr B (vOff k)) v).readW (addr B d) 32 = m.readW (addr B d) 32 :=
  readW_writeW_addr m v (by omega) (by simp only [vOff]; omega) (by simp only [vOff]; omega)

end

section
variable {s₀ : State} (hp : Pre s₀)
include hp

/-! ## Setting up the work vector -/

/-- The IV part of the work vector, with the counter and the flag, stored
to `scratch`. -/
def ivs : List Instr :=
  [.mov .ecx (.imm Spec.Blake2.s.IV[0]), .store (at_ .esi (vOff 8)) .ecx,
   .mov .ecx (.imm Spec.Blake2.s.IV[1]), .store (at_ .esi (vOff 9)) .ecx,
   .mov .ecx (.imm Spec.Blake2.s.IV[2]), .store (at_ .esi (vOff 10)) .ecx,
   .mov .ecx (.imm Spec.Blake2.s.IV[3]), .store (at_ .esi (vOff 11)) .ecx,
   .mov .ecx (.imm Spec.Blake2.s.IV[4]), .alu .xor .ecx (.mem (at_ .esi tloOff)),
   .store (at_ .esi (vOff 12)) .ecx,
   .mov .ecx (.imm Spec.Blake2.s.IV[5]), .alu .xor .ecx (.mem (at_ .esi thiOff)),
   .store (at_ .esi (vOff 13)) .ecx,
   .mov .ecx (.imm Spec.Blake2.s.IV[6]), .alu .xor .ecx (.mem (at_ .esi fOff)),
   .store (at_ .esi (vOff 14)) .ecx,
   .mov .ecx (.imm Spec.Blake2.s.IV[7]), .store (at_ .esi (vOff 15)) .ecx]

/-- The rows loaded. -/
def loadX : List Instr :=
  [.movdquLoad .xmm0 (at_ .eax 0), .movdquLoad .xmm1 (at_ .eax 16),
   .movdquLoad .xmm2 (at_ .esi (vOff 8)), .movdquLoad .xmm3 (at_ .esi (vOff 12))]

omit hp in
theorem load_eq : load = (.mov .eax (.mem (at_ .esp 4)) :: ivs) ++ loadX := rfl

/-- The memory after `ivs`. -/
def ivMem (m : Mem) (B : BitVec 32) : Mem :=
  (((((((m.writeW (addr B (vOff 8)) Spec.Blake2.s.IV[0]).writeW (addr B (vOff 9)) Spec.Blake2.s.IV[1]).writeW
    (addr B (vOff 10)) Spec.Blake2.s.IV[2]).writeW (addr B (vOff 11)) Spec.Blake2.s.IV[3]).writeW
    (addr B (vOff 12)) (Spec.Blake2.s.IV[4] ^^^ m.readW (addr B tloOff) 32)).writeW
    (addr B (vOff 13)) (Spec.Blake2.s.IV[5] ^^^ m.readW (addr B thiOff) 32)).writeW
    (addr B (vOff 14)) (Spec.Blake2.s.IV[6] ^^^ m.readW (addr B fOff) 32)).writeW
    (addr B (vOff 15)) Spec.Blake2.s.IV[7]

theorem ivs_ok {s : State} (hesi : s.gpr .esi = scr s₀) (hwr : s.wr = s₀.wr) :
    WP isa (.block ivs) s fun s' =>
      s'.gpr .eax = s.gpr .eax ∧ s'.gpr .esi = s.gpr .esi ∧ s'.gpr .edi = s.gpr .edi ∧
      s'.gpr .esp = s.gpr .esp ∧ s'.gpr .ebp = s.gpr .ebp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = ivMem s.mem (scr s₀) := by
  have fV := hp.scr_fits
  have hw : ∀ k, 8 ≤ k → k < 16 → InRegions s.wr (addr (scr s₀) (vOff k)) 4 := fun k _ hk =>
    hp.in_scr hwr (by simp only [vOff]; omega)
  have w8 := hw 8 (by omega) (by omega)
  have w9 := hw 9 (by omega) (by omega)
  have w10 := hw 10 (by omega) (by omega)
  have w11 := hw 11 (by omega) (by omega)
  have w12 := hw 12 (by omega) (by omega)
  have w13 := hw 13 (by omega) (by omega)
  have w14 := hw 14 (by omega) (by omega)
  have w15 := hw 15 (by omega) (by omega)
  have r64 := mem_rd (rd := s.rd) (hp.in_scr (d := tloOff) hwr (by decide))
  have r68 := mem_rd (rd := s.rd) (hp.in_scr (d := thiOff) hwr (by decide))
  have r72 := mem_rd (rd := s.rd) (hp.in_scr (d := fOff) hwr (by decide))
  have hh : ∀ (m : Mem) (v : BitVec 32) (k d : Nat), k < 16 → 64 ≤ d → d + 4 ≤ 512 →
      (m.writeW (addr (scr s₀) (vOff k)) v).readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 :=
    fun m v k d h1 h2 h3 => rw_hi fV m v h1 h2 h3
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, ivs, at_, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc, ea_mk, State.load32, State.store32, RegUpd.gpr_setReg,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, hesi, w8, w9, w10, w11, w12,
    w13, w14, w15, r64, r68, r72, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, ?_⟩
  simp (disch := decide) only [hh]
  rfl

theorem in_st16 {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {d : Nat} (hd : d + 16 ≤ 32) :
    InRegions (s.rd ++ s.wr) (addr (st s₀) d) 16 := by
  rw [hrd, hwr]; exact mem_rd ⟨stR s₀, by simp [hp.wr], contains_addr hd (by omega) hp.st_fits⟩

theorem out_st16 {s : State} (hwr : s.wr = s₀.wr) {d : Nat} (hd : d + 16 ≤ 32) :
    InRegions s.wr (addr (st s₀) d) 16 := by
  rw [hwr]; exact ⟨stR s₀, by simp [hp.wr], contains_addr hd (by omega) hp.st_fits⟩

theorem in_scr16 {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {d : Nat} (hd : d + 16 ≤ 512) :
    InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 16 := by
  rw [hrd, hwr]; exact mem_rd ⟨scrR s₀, by simp [hp.wr], contains_addr hd (by omega) hp.scr_fits⟩

theorem loadX_ok {s : State} (heax : s.gpr .eax = st s₀) (hesi : s.gpr .esi = scr s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block loadX) s fun s' =>
      s'.xmm .xmm0 = s.mem.readW (addr (st s₀) 0) 128 ∧
      s'.xmm .xmm1 = s.mem.readW (addr (st s₀) 16) 128 ∧
      s'.xmm .xmm2 = s.mem.readW (addr (scr s₀) 32) 128 ∧
      s'.xmm .xmm3 = s.mem.readW (addr (scr s₀) 48) 128 ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i0 := in_st16 hp hrd hwr (d := 0) (by decide)
  have i16 := in_st16 hp hrd hwr (d := 16) (by decide)
  have i32 := in_scr16 hp hrd hwr (d := 32) (by decide)
  have i48 := in_scr16 hp hrd hwr (d := 48) (by decide)
  apply WP.of_runBlock
  simp only [loadX, at_, vOff, Nat.reduceMul, runBlock_cons, runStep_some, runBlock_nil, exec,
    State.load128, ea_mk, heax, hesi, i0, i16, i32, i48, ite_true, RegUpd.mem_setXmm,
    RegUpd.rd_setXmm, RegUpd.wr_setXmm, RegUpd.gpr_setXmm, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, trivial, trivial, trivial, trivial⟩ <;>
    simp only [RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true]

/-! ## The output -/

omit hp in
theorem finish_eq : finish =
    [.xop (.bin .pxor .xmm0 .xmm2), .xop (.bin .pxor .xmm1 .xmm3),
     .movdquLoad .xmm4 ⟨.eax, 0⟩, .xop (.bin .pxor .xmm0 .xmm4), .movdquStore ⟨.eax, 0⟩ .xmm0,
     .movdquLoad .xmm4 ⟨.eax, 16⟩, .xop (.bin .pxor .xmm1 .xmm4), .movdquStore ⟨.eax, 16⟩ .xmm1] := rfl

theorem finish_ok {v : Work 32} {s : State} (hv : Rows v s) (heax : s.gpr .eax = st s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block finish) s fun s' =>
      (∀ k (hk : k < 8), s'.mem.readW (addr (st s₀) (4 * k)) 32 =
        v[k] ^^^ v[k + 8] ^^^ s.mem.readW (addr (st s₀) (4 * k)) 32) ∧
      Frame [stR s₀] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have fS := hp.st_fits
  have i0 := in_st16 hp hrd hwr (d := 0) (by decide)
  have i16 := in_st16 hp hrd hwr (d := 16) (by decide)
  have o0 := out_st16 hp hwr (d := 0) (by decide)
  have o16 := out_st16 hp hwr (d := 16) (by decide)
  rw [finish_eq]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, State.load128,
    State.store128, ea_mk, RegUpd.gpr_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm,
    RegUpd.mem_setXmm, heax, i0, o0, i16, o16, ite_true, Option.map_some, Option.some.injEq,
    exists_eq_left']
  -- The 16 bytes at `[st + 16]` are read after the store to `[st]`.
  have sep : ∀ (m : Mem) (x : BitVec 128),
      (m.writeW (addr (st s₀) 0) x).readW (addr (st s₀) 16) 128 = m.readW (addr (st s₀) 16) 128 :=
    fun m x => Mem.readW_writeW_sep (addr_sep (by omega) (by omega) (by omega)) (by decide)
  refine ⟨fun k hk => ?_, ?_, trivial, trivial, trivial⟩
  · simp only [RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true, sep]
    rcases (by omega : k < 4 ∨ 4 ≤ k) with h | h
    · have a : dword (s.xmm .xmm0) k = v[k] := hv.r0 k h
      have c : dword (s.xmm .xmm2) k = v[8 + k] := hv.r2 k h
      rw [Mem.readW_writeW_sep (addr_sep (n := 4) (k := 16) (by omega) (by omega) (by omega)) (by decide),
        show 4 * k = 0 + 4 * k by omega, load_write_self _ _ (by omega) h, dword_pxor, dword_pxor,
        dword_load _ (by omega) h, a, c]
      simp only [Nat.add_comm 8 k]
    · obtain ⟨i, hi, rfl⟩ : ∃ i, i < 4 ∧ k = 4 + i := ⟨k - 4, by omega, by omega⟩
      have b : dword (s.xmm .xmm1) i = v[4 + i] := hv.r1 i hi
      have d : dword (s.xmm .xmm3) i = v[12 + i] := hv.r3 i hi
      rw [show 4 * (4 + i) = 16 + 4 * i by omega, load_write_self _ _ (by omega) hi, dword_pxor,
        dword_pxor, dword_load _ (by omega) hi, b, d]
      simp only [show 4 + i + 8 = 12 + i by omega]
  · have hm := List.mem_singleton_self (stR s₀)
    exact ((Frame.refl _ _).writeW hm _ (contains_addr (by decide) (by decide) fS)).writeW hm _
      (contains_addr (by decide) (by decide) fS)

/-! ## Advancing -/

/-- The memory after `advance`. -/
def advMem (m : Mem) (B : BitVec 32) : Mem :=
  ((m.writeW (addr B tloOff) (m.readW (addr B tloOff) 32 + 64)).writeW (addr B thiOff)
    (m.readW (addr B thiOff) 32 + 0 + (BitVec.ofBool
      (decide (2 ^ 32 ≤ (m.readW (addr B tloOff) 32).toNat + (64 : BitVec 32).toNat))).setWidth 32)).writeW
    (addr B nOff) (m.readW (addr B nOff) 32 - 1)

theorem advance_ok {s : State} (hesi : s.gpr .esi = scr s₀) (hwr : s.wr = s₀.wr) :
    WP isa (.block advance) s fun s' =>
      s'.gpr .edi = s.gpr .edi + 64 ∧ s'.gpr .esi = s.gpr .esi ∧ s'.gpr .esp = s.gpr .esp ∧
      s'.gpr .ebp = s.gpr .ebp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.zf = some (s.mem.readW (addr (scr s₀) nOff) 32 - 1 == 0) ∧
      s'.mem = advMem s.mem (scr s₀) := by
  have fV := hp.scr_fits
  have hr : ∀ d, d + 4 ≤ 512 → InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 := fun d hd =>
    mem_rd (hp.in_scr hwr hd)
  have hw : ∀ d, d + 4 ≤ 512 → InRegions s.wr (addr (scr s₀) d) 4 := fun d hd => hp.in_scr hwr hd
  have r64 := hr tloOff (by decide)
  have r68 := hr thiOff (by decide)
  have r76 := hr nOff (by decide)
  have w64 := hw tloOff (by decide)
  have w68 := hw thiOff (by decide)
  have w76 := hw nOff (by decide)
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, advance, at_, runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc, ea_mk, State.load32, State.store32, RegUpd.gpr_setReg,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.cf_setReg,
    RegUpd.cf_arithFlags, RegUpd.zf_setReg, RegUpd.zf_arithFlags, hesi, r64, r68, r76, w64, w68, w76,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, ?_, ?_⟩
  · simp (disch := decide) only [rw_scr fV]
  · simp (disch := decide) only [rw_scr fV]
    rfl

end

/-- Words 8 to 15 of the work vector, in `scratch` after `ivs`. -/
theorem ivMem_hi {B : BitVec 32} (hfit : B.toNat + 512 ≤ 2 ^ 32) {m : Mem} {H : HashValue 32} {T : Nat}
    {f : Bool} (hlo : m.readW (addr B tloOff) 32 = BitVec.ofNat 32 T)
    (hhi : m.readW (addr B thiOff) 32 = BitVec.ofNat 32 (T / 2 ^ 32))
    (hf : m.readW (addr B fOff) 32 = flagW f) {k : Nat} (hk8 : 8 ≤ k) (hk : k < 16) :
    (ivMem m B).readW (addr B (vOff k)) 32 = (V0 H T f)[k] := by
  have fV : B.toNat + 64 ≤ 2 ^ 32 := by omega
  rw [V0_get _ _ _ k hk]
  simp (disch := omega) only [ivMem, rw_slot fV]
  rw [hlo, hhi, hf]
  have : k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [↓reduceIte, ↓reduceDIte, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceSub, Nat.reducePow]
  all_goals rfl

theorem frame_ivMem {B : BitVec 32} (hfit : B.toNat + 64 ≤ 2 ^ 32) (m : Mem) :
    Frame [workR B] m (ivMem m B) := by
  have ct : ∀ i < 16, (workR B).Contains (addr B (vOff i)) (32 / 8) := fun i hi =>
    contains_addr (by simp only [vOff]; omega) (by decide) hfit
  have hm := List.mem_singleton_self (workR B)
  simp only [ivMem]
  exact (((((((((Frame.refl _ _).writeW hm _ (ct 8 (by omega))).writeW hm _ (ct 9 (by omega))).writeW hm _
    (ct 10 (by omega))).writeW hm _ (ct 11 (by omega))).writeW hm _ (ct 12 (by omega))).writeW hm _
    (ct 13 (by omega))).writeW hm _ (ct 14 (by omega))).writeW hm _ (ct 15 (by omega)))

theorem xor_order (h a b : BitVec 32) : a ^^^ b ^^^ h = h ^^^ a ^^^ b := by
  rw [BitVec.xor_comm _ h, BitVec.xor_assoc]

/-! ## One block -/

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State} (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  have fS := hp.st_fits
  have fV := hp.scr_fits
  have fV64 : (scr s₀).toNat + 64 ≤ 2 ^ 32 := by omega
  have a0 : s.mem.readW (addr (esp₀ s₀) 4) 32 = st s₀ := hp.arg_frame hL.frame (i := 0) (by decide)
  -- Set up the work vector.
  refine WP.seq ?_
  rw [load_eq, WP.block_append_iff]
  refine wp_ldm hL.esp (hp.in_arg hL.rd (by omega) (by omega)) fun s₁ u₁ => ?_
  rw [a0] at u₁
  refine WP.mono (ivs_ok hp (by rw [u₁.other _ (by decide), hL.esi]) (by rw [u₁.wr, hL.wr]))
    fun s₃ ⟨e₀, e₁, e₂, e₃, e₄, e₅, e₆, e₇⟩ => ?_
  have f₃ : Frame [workR (scr s₀)] s.mem s₃.mem := by
    rw [e₇, u₁.mem]; exact frame_ivMem fV64 _
  refine WP.mono (loadX_ok hp (by rw [e₀, u₁.gpr]) (by rw [e₁, u₁.other _ (by decide), hL.esi])
    (by rw [e₅, u₁.rd, hL.rd]) (by rw [e₆, u₁.wr, hL.wr])) fun s₄ ⟨x0, x1, x2, x3, g₄, m₄, r₄, w₄⟩ => ?_
  have sw : ∀ r ∈ [workR (scr s₀)], ∃ r' ∈ [stR s₀, scrR s₀], Region.Sub r r' :=
    fun r hr => ⟨scrR s₀, by simp, by simp at hr; subst hr; exact Region.sub_prefix (by omega)⟩
  have hrows : Rows (V0 (stateAt 32 s.mem ((st s₀).setWidth 64)) (t₀ s₀ + i * 64) (fl s₀)) s₄ := by
    have hi8 : ∀ k, 8 ≤ k → (hk : k < 16) → s₃.mem.readW (addr (scr s₀) (vOff k)) 32 =
        (V0 (stateAt 32 s.mem ((st s₀).setWidth 64)) (t₀ s₀ + i * 64) (fl s₀))[k] := fun k h8 hk => by
      rw [e₇, u₁.mem]
      exact ivMem_hi fV hL.tlo hL.thi hL.flag h8 hk
    have hs : s₃.mem.readW (addr (st s₀) 0) 128 = s.mem.readW (addr (st s₀) 0) 128 ∧
        s₃.mem.readW (addr (st s₀) 16) 128 = s.mem.readW (addr (st s₀) 16) 128 := by
      have nd : ∀ d, d + 16 ≤ 32 → ∀ r ∈ [workR (scr s₀)], Region.Disjoint ⟨addr (st s₀) d, 16⟩ r :=
        fun d hd r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          refine (hp.st_scr.sub_left ?_).sub_right (Region.sub_prefix (by omega))
          rw [addr_eq (by omega)]; exact Offset.sub_base _ hd
      exact ⟨f₃.readW (Region.contains_self _ _) (nd 0 (by decide)) (by decide),
        f₃.readW (Region.contains_self _ _) (nd 16 (by decide)) (by decide)⟩
    refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
    · rw [dw, x0, hs.1, dword_load _ (by omega) hk, V0_get _ _ _ _ (by omega),
        dite_eq_left (by omega), Nat.zero_add, hp.stateAt_get _ (by omega)]
    · rw [dw, x1, hs.2, dword_load _ (by omega) hk, V0_get _ _ _ _ (by omega),
        dite_eq_left (by omega), hp.stateAt_get _ (by omega), show 4 * (4 + k) = 16 + 4 * k by omega]
    · rw [dw, x2, dword_load _ (by omega) hk, show 32 + 4 * k = vOff (8 + k) by simp only [vOff]; omega,
        hi8 _ (by omega) (by omega)]
    · rw [dw, x3, dword_load _ (by omega) hk, show 48 + 4 * k = vOff (12 + k) by simp only [vOff]; omega,
        hi8 _ (by omega) (by omega)]
  -- The rounds.
  have hedi₄ : s₄.gpr .edi = blkAddr s₀ i := by rw [g₄, e₂, u₁.other _ (by decide), hL.edi]
  have hmsg₄ : Msg (blkAddr s₀ i) (blk s₀ i) s₄.mem := hp.msg hi (by rw [m₄]; exact hL.frame.trans (f₃.sub sw))
  have hrd₄ : ∀ j < 16, InRegions (s₄.rd ++ s₄.wr) (addr (blkAddr s₀ i) (4 * j)) 4 := by
    rw [r₄, w₄, e₅, e₆, u₁.rd, u₁.wr, hL.rd, hL.wr]; exact hp.blk_rd hi
  refine WP.seq (WP.mono (rounds_ok hedi₄ hmsg₄ hrd₄ (s := s₄) ⟨hrows, fun _ _ _ => rfl, rfl, rfl, rfl⟩ 10)
    fun s₅ h₅ => ?_)
  -- The output, and advance.
  have g₅ : ∀ r, r ≠ .ecx → r ≠ .edx → s₅.gpr r = s₃.gpr r := fun r h1 h2 => by rw [h₅.gpr r h1 h2, g₄]
  rw [WP.block_append_iff]
  refine WP.mono (finish_ok hp h₅.rows (by rw [g₅ _ (by decide) (by decide), e₀, u₁.gpr])
    (by rw [h₅.rd, r₄, e₅, u₁.rd, hL.rd]) (by rw [h₅.wr, w₄, e₆, u₁.wr, hL.wr]))
    fun s₆ ⟨o₆, f₆', g₆, r₆, w₆⟩ => ?_
  have hesi₆ : s₆.gpr .esi = scr s₀ := by
    rw [g₆, g₅ _ (by decide) (by decide), e₁, u₁.other _ (by decide), hL.esi]
  have hwr₆ : s₆.wr = s₀.wr := by rw [w₆, h₅.wr, w₄, e₆, u₁.wr, hL.wr]
  refine advance_ok hp hesi₆ hwr₆ |>.mono fun s₇ ⟨d₁, d₂, d₃, d₄, d₅, d₆, d₇, d₈⟩ => ?_
  -- Registers
  have hedi₆ : s₆.gpr .edi = s.gpr .edi := by
    rw [g₆, g₅ _ (by decide) (by decide), e₂, u₁.other _ (by decide)]
  have hesp₆ : s₆.gpr .esp = s.gpr .esp := by
    rw [g₆, g₅ _ (by decide) (by decide), e₃, u₁.other _ (by decide)]
  have hebp₆ : s₆.gpr .ebp = s.gpr .ebp := by
    rw [g₆, g₅ _ (by decide) (by decide), e₄, u₁.other _ (by decide)]
  have hrd : s₇.rd = s₀.rd := by rw [d₅, r₆, h₅.rd, r₄, e₅, u₁.rd, hL.rd]
  have hwr : s₇.wr = s₀.wr := by rw [d₆, hwr₆]
  -- Memory
  have hm₅ : s₅.mem = s₃.mem := by rw [h₅.mem, m₄]
  have f₆ : Frame [stR s₀] s₃.mem s₆.mem := by rw [← hm₅]; exact f₆'
  have rA : ∀ d, d + 4 ≤ 512 → d ≠ tloOff → d ≠ thiOff → d ≠ nOff → (d % 4 = 0) →
      s₇.mem.readW (addr (scr s₀) d) 32 = s₆.mem.readW (addr (scr s₀) d) 32 := fun d hd h1 h2 h3 h4 => by
    rw [d₈]; simp only [advMem]
    rw [rw_scr fV _ _ hd (by decide) (by simp only [nOff] at h3 ⊢; omega),
      rw_scr fV _ _ hd (by decide) (by simp only [thiOff] at h2 ⊢; omega),
      rw_scr fV _ _ hd (by decide) (by simp only [tloOff] at h1 ⊢; omega)]
  have f₇ : Frame [stR s₀, scrR s₀] s₀.mem s₇.mem := by
    rw [d₈]; simp only [advMem]
    have hm : scrR s₀ ∈ [stR s₀, scrR s₀] := by simp
    exact (((((hL.frame.trans (f₃.sub sw)).trans (f₆.mono (by simp)))).writeW hm _
      (hp.scr_contains (by decide))).writeW hm _
      (hp.scr_contains (by decide))).writeW hm _ (hp.scr_contains (by decide))
  have hstate : stateAt 32 s₇.mem ((st s₀).setWidth 64) =
      Spec.Blake2.F Spec.Blake2.s (stateAt 32 s.mem ((st s₀).setWidth 64)) (blk s₀ i) (t₀ s₀ + i * 64)
        (fl s₀) := by
    refine hp.stateAt_ext fun k hk => ?_
    have e7 : s₇.mem.readW (addr (st s₀) (4 * k)) 32 = s₆.mem.readW (addr (st s₀) (4 * k)) 32 := by
      rw [d₈]; simp only [advMem]
      have sep : ∀ d, d + 4 ≤ 512 → Mem.Sep (addr (st s₀) (4 * k)) (32 / 8) (addr (scr s₀) d) (32 / 8) :=
        fun d hd => hp.st_scr.sep (hp.st_contains (by omega)) (hp.scr_contains hd)
      rw [Mem.readW_writeW_sep (sep _ (by decide)) (by decide),
        Mem.readW_writeW_sep (sep _ (by decide)) (by decide),
        Mem.readW_writeW_sep (sep _ (by decide)) (by decide)]
    rw [e7, o₆ k hk, hm₅, hp.st_frame f₃ (by omega), ← hp.stateAt_get _ hk, F_eq]
    simp only [Vector.getElem_ofFn]
    exact xor_order _ _ _
  have hsaved : Saved s₀ s₇.mem := by
    have s₆' : Saved s₀ s₆.mem :=
      hp.saved_frame (hp.saved_frame hL.saved (.inl f₃)) (.inr f₆)
    exact s₆'.of_readW fun p h => rA _ (by have := saved_bound p h; omega) (by revert p h; decide)
      (by revert p h; decide) (by revert p h; decide) (by revert p h; decide)
  have k₆ : ∀ d, 64 ≤ d → d + 4 ≤ 512 → s₆.mem.readW (addr (scr s₀) d) 32 = s.mem.readW (addr (scr s₀) d) 32 :=
    fun d h1 h2 => by
      rw [hp.high_frame (.inr f₆) h1 h2, hp.high_frame (.inl f₃) h1 h2]
  have hcommon : Common s₀ (i + 1) s₇ := by
    refine ⟨by rw [d₂, hesi₆], by rw [d₃, hesp₆, hL.esp],
      by rw [d₄, hebp₆, hL.ebp], hrd, hwr, f₇, ?_, hsaved⟩
    rw [hstate, Proof.Blake2.compressBlocks_succ, ← hL.state]
    rfl
  have hnb : nb s₀ < 2 ^ 32 := (arg s₀ 2).isLt
  have hc1 : s₆.mem.readW (addr (scr s₀) nOff) 32 - 1 = BitVec.ofNat 32 (nb s₀ - (i + 1)) := by
    rw [k₆ _ (by decide) (by decide), hL.cnt, ofNat_pred (by omega), Nat.sub_sub]
  have hev : eval .ne s₇ = some (!(BitVec.ofNat 32 (nb s₀ - (i + 1)) == 0)) := by
    rw [Proof.MdStream.X86.eval_ne, d₇, hc1]; rfl
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    have h0 : BitVec.ofNat 32 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
      exact hne h'
    refine ⟨by rw [hev]; simpa using h0, by omega, ⟨hcommon, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [d₁, hedi₆, hL.edi]
      simp only [blkAddr]
      rw [BitVec.add_assoc, show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl, BitVec.ofNat_add_ofNat]
      rfl
    · rw [d₈]; simp only [advMem]
      rw [rw_scr fV _ _ (by decide) (by decide) (by decide), rw_scr fV _ _ (by decide) (by decide) (by decide),
        Mem.readW_writeW_self32, k₆ _ (by decide) (by decide), hL.tlo,
        show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl, ← BitVec.ofNat_add]
      congr 1; omega
    · rw [d₈]; simp only [advMem]
      rw [rw_scr fV _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32,
        k₆ _ (by decide) (by decide), k₆ _ (by decide) (by decide), hL.tlo, hL.thi,
        show ∀ x : BitVec 32, x + 0 = x from fun x => BitVec.add_zero x,
        show (64 : BitVec 32) = BitVec.ofNat 32 64 from rfl,
        Proof.Blake2.X86.Stream.carry_ofNat _ _ (by decide)]
      congr 2; omega
    · rw [rA _ (by decide) (by decide) (by decide) (by decide) rfl, k₆ _ (by decide) (by decide), hL.flag]
    · rw [d₈]; simp only [advMem]
      rw [Mem.readW_writeW_self32, hc1]

end VG.Proof.Blake2.X86.CompressS

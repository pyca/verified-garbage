import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Blake2.X86.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Sha512.X86.Rounds
import VerifiedGarbage.Proof.Blake2.Spec
import VerifiedGarbage.Impl.Blake2.X86.CompressB
import VerifiedGarbage.Proof.Blake2.X86.CompressB.G

section

section

/-!
# BLAKE2b on x86 (32-bit): the rounds

`G_step` moves `g_ok` to the work vector (`Holds`), for any four of its words;
`round_ok` composes the eight `G`s of a round, for any round, and `rounds_ok`
the rounds.
-/

namespace VG.Proof.Blake2.X86.CompressB

open VG VG.X86
open VG.Impl.Blake2.X86.CompressB (vOff msgOff g gAt round rounds)
open VG.Proof.Sha512.X86 (Acc rd64)
open VG.Spec.Blake2 (Work Block G)
open VG.Proof.Blake2 (mix G_get)

/-- The work vector `v` is in `scratch[128..256)` (at `B`). -/
def Holds (B : BitVec 32) (v : Work 64) (m : Mem) : Prop :=
  ∀ k (hk : k < 16), rd64 m B (vOff k) = v[k]

/-- The block `M` is in `scratch[0..128)` (at `B`). -/
def Msg (B : BitVec 32) (M : Block 64) (m : Mem) : Prop :=
  ∀ j : Fin 16, rd64 m B (msgOff j) = M j

/-- The rounds invariant, relative to the state `s₀` at the start of the rounds. -/
structure RI (B : BitVec 32) (M : Block 64) (v : Work 64) (s₀ s : State) : Prop where
  holds : Holds B v s.mem
  msg : Msg B M s.mem
  keep : Keep s₀ s
  frame : Frame [⟨B.setWidth 64, 256⟩] s₀.mem s.mem

theorem vOff_sep {j k : Nat} (_hj : j < 16) (_hk : k < 16) (h : j ≠ k) : Sep8 (vOff j) (vOff k) := by
  simp only [Sep8, vOff]; omega

theorem msg_vOff (j : Fin 16) {k : Nat} : Sep8 (msgOff j) (vOff k) := by
  have := j.2; simp only [Sep8, msgOff, vOff]; omega

/-- The side conditions of `G_step`, decidable for concrete arguments: the
four words are distinct. -/
def QSide (a b c d : Nat) : Bool := [a, b, c, d].Nodup

theorem G_step {B : BitVec 32} (hfit : B.toNat + 512 ≤ 2 ^ 32) {s₀ : State}
    (h0 : s₀.gpr .esi = B) (hA : Acc s₀.wr B 512) {a b c d : Fin 16} (hq : QSide a b c d = true)
    {M : Block 64} {v : Work 64} {s : State} (hR : RI B M v s₀ s) (j k : Fin 16) :
    WP isa (.block (g (vOff a) (vOff b) (vOff c) (vOff d) (msgOff j) (msgOff k))) s
      (RI B M (G Spec.Blake2.b v a b c d (M j) (M k)) s₀) := by
  have nd : (a.1 ≠ b.1 ∧ a.1 ≠ c.1 ∧ a.1 ≠ d.1) ∧ (b.1 ≠ c.1 ∧ b.1 ≠ d.1) ∧ c.1 ≠ d.1 := by
    simpa [QSide] using hq
  obtain ⟨⟨nab, nac, nad⟩, ⟨nbc, nbd⟩, ncd⟩ := nd
  have hv : ∀ q : Fin 16, vOff q + 8 ≤ 256 := fun q => by have := q.2; simp only [vOff]; omega
  have hm : ∀ q : Fin 16, msgOff q + 8 ≤ 256 := fun q => by have := q.2; simp only [msgOff]; omega
  refine WP.mono (g_ok hfit (hv a) (hv b) (hv c) (hv d) (hm j) (hm k)
    (vOff_sep a.2 b.2 nab) (vOff_sep a.2 c.2 nac) (vOff_sep a.2 d.2 nad) (vOff_sep b.2 c.2 nbc)
    (vOff_sep b.2 d.2 nbd) (vOff_sep c.2 d.2 ncd) (msg_vOff k) (msg_vOff k)
    (hR.keep.esi h0) (hR.keep.acc hA)) fun s' ⟨hk, ea, eb, ec, ed, other, hf⟩ => ?_
  have ra := hR.holds a a.2
  have rb := hR.holds b b.2
  have rc := hR.holds c c.2
  have rd := hR.holds d d.2
  have rj := hR.msg j
  have rk := hR.msg k
  rw [ra, rb, rc, rd, rj, rk] at ea eb ec ed
  refine ⟨fun q hq => ?_, fun i => ?_, hR.keep.trans hk, hR.frame.trans hf⟩
  · rw [G_get Spec.Blake2.b v nab nac nad nbc nbd ncd _ _ q hq]
    by_cases eqb : b.1 = q
    · subst eqb; simp only [ite_true]; exact eb
    by_cases eqc : c.1 = q
    · subst eqc; simp only [eqb, ite_true, ite_false]; exact ec
    by_cases eqd : d.1 = q
    · subst eqd; simp only [eqb, eqc, ite_true, ite_false]; exact ed
    by_cases eqa : a.1 = q
    · subst eqa; simp only [eqb, eqc, eqd, ite_true, ite_false]; exact ea
    simp only [eqb, eqc, eqd, eqa, ite_false]
    rw [other _ (by simp only [vOff]; omega) (vOff_sep a.2 hq eqa) (vOff_sep b.2 hq eqb)
      (vOff_sep c.2 hq eqc) (vOff_sep d.2 hq eqd)]
    exact hR.holds q hq
  · rw [other _ (by have := i.2; simp only [msgOff]; omega) (msg_vOff i).symm (msg_vOff i).symm
      (msg_vOff i).symm (msg_vOff i).symm]
    exact hR.msg i

theorem round_ok {B : BitVec 32} (hfit : B.toNat + 512 ≤ 2 ^ 32) {s₀ : State}
    (h0 : s₀.gpr .esi = B) (hA : Acc s₀.wr B 512) {M : Block 64} {v : Work 64} {s : State}
    (hR : RI B M v s₀ s) (r : Nat) :
    WP isa (round r) s (RI B M (Spec.Blake2.round Spec.Blake2.b M v r) s₀) := by
  unfold round gAt
  refine WP.seq (WP.mono (G_step hfit h0 hA (a := 0) (b := 4) (c := 8) (d := 12) (by decide) hR
    (Spec.Blake2.sigmaAt r 0) (Spec.Blake2.sigmaAt r 1)) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (G_step hfit h0 hA (a := 1) (b := 5) (c := 9) (d := 13) (by decide) h₁
    (Spec.Blake2.sigmaAt r 2) (Spec.Blake2.sigmaAt r 3)) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (G_step hfit h0 hA (a := 2) (b := 6) (c := 10) (d := 14) (by decide) h₂
    (Spec.Blake2.sigmaAt r 4) (Spec.Blake2.sigmaAt r 5)) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (G_step hfit h0 hA (a := 3) (b := 7) (c := 11) (d := 15) (by decide) h₃
    (Spec.Blake2.sigmaAt r 6) (Spec.Blake2.sigmaAt r 7)) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (G_step hfit h0 hA (a := 0) (b := 5) (c := 10) (d := 15) (by decide) h₄
    (Spec.Blake2.sigmaAt r 8) (Spec.Blake2.sigmaAt r 9)) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (G_step hfit h0 hA (a := 1) (b := 6) (c := 11) (d := 12) (by decide) h₅
    (Spec.Blake2.sigmaAt r 10) (Spec.Blake2.sigmaAt r 11)) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (G_step hfit h0 hA (a := 2) (b := 7) (c := 8) (d := 13) (by decide) h₆
    (Spec.Blake2.sigmaAt r 12) (Spec.Blake2.sigmaAt r 13)) fun s₇ h₇ => ?_)
  exact WP.mono (G_step hfit h0 hA (a := 3) (b := 4) (c := 9) (d := 14) (by decide) h₇
    (Spec.Blake2.sigmaAt r 14) (Spec.Blake2.sigmaAt r 15)) fun _ h => h

theorem rounds_ok {B : BitVec 32} (hfit : B.toNat + 512 ≤ 2 ^ 32) {s₀ : State}
    (h0 : s₀.gpr .esi = B) (hA : Acc s₀.wr B 512) {M : Block 64} {v : Work 64}
    (hR : RI B M v s₀ s₀) :
    ∀ n, WP isa (rounds n) s₀ (RI B M ((List.range n).foldl (Spec.Blake2.round Spec.Blake2.b M) v) s₀)
  | 0 => WP.block_nil hR
  | n + 1 => by
    refine WP.seq (WP.mono (rounds_ok hfit h0 hA hR n) fun s h => ?_)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact round_ok hfit h0 hA h n

end VG.Proof.Blake2.X86.CompressB

end

/-!
# BLAKE2b compression function on x86 (32-bit): the precondition

The facts `compressX86 b`'s precondition gives (`Pre`), and the addresses and
regions the code uses.
-/

namespace VG.Proof.Blake2.X86.CompressB

open VG VG.X86 VG.Impl.Blake2.X86.CompressB
open VG.Spec.Blake2 (HashValue Block stateAt blockAt)
open VG.Proof.Sha512.X86 (Acc rd64 mem_rd)
open VG.Proof.Sha256.X86.Stream (contains_addr sub_offset)

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := arg s₀ 0
abbrev bp : BitVec 32 := arg s₀ 1
abbrev nb : Nat := (arg s₀ 2).toNat
/-- The offset counter of the first block. -/
abbrev t₀ : Nat := (arg s₀ 4 ++ arg s₀ 3).toNat
/-- The final block flag. -/
abbrev fl : Bool := arg s₀ 5 != 0
abbrev scr : BitVec 32 := arg s₀ 6
abbrev stR : Region := ⟨(st s₀).setWidth 64, 64⟩
abbrev blR : Region := ⟨(bp s₀).setWidth 64, 128 * nb s₀⟩
abbrev scrR : Region := ⟨(scr s₀).setWidth 64, 512⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 28⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩
abbrev H₀ : HashValue 64 := stateAt 64 s₀.mem ((st s₀).setWidth 64)

/-- Where block `i` starts. -/
abbrev blkAddr (i : Nat) : BitVec 32 := bp s₀ + BitVec.ofNat 32 (128 * i)

/-- Block `i`, as `compressBlocks` reads it. -/
abbrev blk (i : Nat) : Block 64 :=
  blockAt 64 s₀.mem ((bp s₀).setWidth 64 + BitVec.ofNat 64 (Spec.Blake2.blockBytes 64 * i))

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
  st_fits : (st s₀).toNat + 64 ≤ 2 ^ 32
  blk_fits : (bp s₀).toNat + 128 * nb s₀ ≤ 2 ^ 32
  scr_fits : (scr s₀).toNat + 512 ≤ 2 ^ 32
  esp_fits : (esp₀ s₀).toNat + 32 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : (compressX86 Spec.Blake2.b).pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem addr_ofNat {x : BitVec 32} {d : Nat} (h : x.toNat + d < 2 ^ 32) :
    addr x d = x.setWidth 64 + BitVec.ofNat 64 d := addr_eq h

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem acc {s : State} (hw : s.wr = s₀.wr) : Acc s.wr (scr s₀) 512 :=
  VG.Proof.Sha512.X86.Acc.of_mem (by rw [hw, hp.wr]; simp) hp.scr_fits

theorem accS {s : State} (hw : s.wr = s₀.wr) : Acc s.wr (st s₀) 64 :=
  VG.Proof.Sha512.X86.Acc.of_mem (by rw [hw, hp.wr]; simp) hp.st_fits

theorem in_scr {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 512) :
    InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 :=
  mem_rd (hp.acc hw d hd)

theorem in_st {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 64) :
    InRegions (s.rd ++ s.wr) (addr (st s₀) d) 4 :=
  mem_rd (hp.accS hw d hd)

theorem argAddr_eq {d : Nat} (hd : d < 32) :
    addr (esp₀ s₀) d = (esp₀ s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.esp_fits; omega)

theorem arg_contains {d : Nat} (hd : 4 ≤ d) (hd' : d + 4 ≤ 32) :
    (argR s₀).Contains (addr (esp₀ s₀) d) 4 := by
  show (⟨addr (esp₀ s₀) 4, 28⟩ : Region).Contains _ _
  rw [hp.argAddr_eq (by omega), hp.argAddr_eq (by omega)]
  exact Offset.contains _ hd (by omega) (by omega)

theorem in_arg {s : State} (hrd : s.rd = s₀.rd) {d : Nat} (hd : 4 ≤ d)
    (hd' : d + 4 ≤ 32) : InRegions (s.rd ++ s.wr) (addr (esp₀ s₀) d) 4 :=
  ⟨argR s₀, by simp [hrd, hp.rd], hp.arg_contains hd hd'⟩

/-- An argument slot is inside the argument region. -/
theorem arg_sub {i : Nat} (hi : i < 7) : Region.Sub ⟨argAddr s₀ i, 4⟩ (argR s₀) := by
  show Region.Sub ⟨addr (esp₀ s₀) (4 + 4 * i), 4⟩ ⟨addr (esp₀ s₀) 4, 28⟩
  rw [hp.argAddr_eq (by omega), hp.argAddr_eq (by omega)]
  exact Offset.sub _ (by omega) (by omega)

/-- The arguments are unchanged while only the state and the scratch buffer are written. -/
theorem arg_frame {m : Mem} (hf : Frame [stR s₀, scrR s₀] s₀.mem m) {i : Nat} (hi : i < 7) :
    m.readW (addr (esp₀ s₀) (4 + 4 * i)) 32 = arg s₀ i := by
  refine (hf.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) ?_ (by decide))
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨hp.arg_st.sub_left (hp.arg_sub hi), hp.arg_scr.sub_left (hp.arg_sub hi)⟩

theorem blk_toNat {i : Nat} (hi : i < nb s₀) :
    (blkAddr s₀ i).toNat = (bp s₀).toNat + 128 * i := by
  have := hp.blk_fits
  simp only [blkAddr, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := 128 * i) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem blk_fit {i : Nat} (hi : i < nb s₀) : (blkAddr s₀ i).toNat + 128 ≤ 2 ^ 32 := by
  have := hp.blk_fits; rw [hp.blk_toNat hi]; omega

theorem blk_addr {i : Nat} (hi : i < nb s₀) :
    (blkAddr s₀ i).setWidth 64 = (bp s₀).setWidth 64 + BitVec.ofNat 64 (128 * i) :=
  addr_eq (x := bp s₀) (k := 128 * i) (by have := hp.blk_fits; omega)

theorem blk_sub {i : Nat} (hi : i < nb s₀) :
    Region.Sub ⟨(blkAddr s₀ i).setWidth 64, 128⟩ (blR s₀) := by
  have := hp.blk_fits
  rw [hp.blk_addr hi]; exact sub_offset (by omega) (by omega)

theorem blk_rd {i : Nat} (hi : i < nb s₀) {o : Nat} (ho : o + 4 ≤ 128) :
    InRegions (s₀.rd ++ s₀.wr) (addr (blkAddr s₀ i) o) 4 := by
  refine ⟨blR s₀, by simp [hp.rd], ?_⟩
  rw [show addr (blkAddr s₀ i) o = addr (bp s₀) (128 * i + o) by
    simp only [addr, blkAddr, BitVec.add_assoc, BitVec.ofNat_add]]
  exact contains_addr (by have : i + 1 ≤ nb s₀ := hi; omega) (by omega) hp.blk_fits

theorem blk_disj {i : Nat} (hi : i < nb s₀) :
    ∀ r ∈ [stR s₀, scrR s₀], Region.Disjoint ⟨(blkAddr s₀ i).setWidth 64, 128⟩ r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨hp.blk_st.sub_left (hp.blk_sub hi), hp.blk_scr.sub_left (hp.blk_sub hi)⟩

/-- The words of `scratch` from offset 256 on (the parameters and the saved
registers) are unchanged while only `scratch[0, 256)` or the state is written. -/
theorem high_frame {m m' : Mem}
    (hf : Frame [⟨(scr s₀).setWidth 64, 256⟩] m m' ∨ Frame [stR s₀] m m') {d : Nat}
    (hd : 256 ≤ d) (hd' : d + 4 ≤ 512) :
    m'.readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 := by
  have hc : (⟨addr (scr s₀) d, 4⟩ : Region).Contains (addr (scr s₀) d) (32 / 8) :=
    Region.contains_self _ _
  have := hp.scr_fits
  rcases hf with hf | hf
  · refine hf.readW hc ?_ (by decide)
    simp only [List.mem_singleton, forall_eq]
    rw [addr_eq (by omega)]
    exact Offset.disjoint_base _ hd (by omega)
  · refine hf.readW hc ?_ (by decide)
    simp only [List.mem_singleton, forall_eq]
    refine Region.Disjoint.sub_left hp.st_scr.symm ?_
    rw [addr_eq (by omega)]
    exact Offset.sub_base _ (by omega)

theorem high_frame64 {m m' : Mem}
    (hf : Frame [⟨(scr s₀).setWidth 64, 256⟩] m m' ∨ Frame [stR s₀] m m') {d : Nat}
    (hd : 256 ≤ d) (hd' : d + 8 ≤ 512) :
    rd64 m' (scr s₀) d = rd64 m (scr s₀) d := by
  simp only [rd64]
  rw [hp.high_frame hf hd (by omega), hp.high_frame hf (by omega) hd']

/-- The state's words are unchanged while only `scratch` is written. -/
theorem st_frame {m m' : Mem} (hf : Frame [scrR s₀] m m') {d : Nat} (hd : d + 4 ≤ 64) :
    m'.readW (addr (st s₀) d) 32 = m.readW (addr (st s₀) d) 32 := by
  refine hf.readW (contains_addr (len := 64) hd (by omega) hp.st_fits) ?_ (by decide)
  simp only [List.mem_singleton, forall_eq]
  exact hp.st_scr

end Pre

end VG.Proof.Blake2.X86.CompressB

end

/-!
# BLAKE2b compression function on x86 (32-bit): the parts of one block

Copying 32-bit words (`copyWords_ok`), which copies the block and the state
into `scratch`; initializing the rest of the work vector (`ivWord_ok`,
`ivXor_ok`); XORing the work vector into the state (`finish_ok`); and
advancing the parameters to the next block (`advance_ok`).
-/

namespace VG.Proof.Blake2.X86.CompressB

open VG VG.X86 VG.Impl.Blake2.X86.CompressB
open VG.Spec.Blake2 (HashValue Work Block stateAt blockAt)
open VG.Proof.Sha512.X86 (Acc rd64 write64 mem_rd readSrc_mem ea_of wp_movS wp_xorS wp_addS
  wp_adcS lo_rd64 hi_rd64 rd64_write64_self rd64_write64_ne)
open VG.Proof.Sha512.Word64 (lo hi readW64 lo_append hi_append hi_append_lo lo_xor hi_xor)
open VG.Proof.Sha256.X86.Stream (contains_addr Upd Mupd wp_movm wp_store wp_movi wp_subi
  readW_writeW_addr)

/-! ## 64-bit words in `scratch` -/

section
variable {B : BitVec 32} (hfit : B.toNat + 512 ≤ 2 ^ 32)
include hfit

theorem rw64_ne (m : Mem) (x : BitVec 64) {o o' : Nat} (h : o + 8 ≤ 512) (h' : o' + 8 ≤ 512)
    (hs : Sep8 o o') : rd64 (write64 m B o x) B o' = rd64 m B o' :=
  rd64_write64_ne m x (by omega) (by omega) hs

theorem rw64_self (m : Mem) (x : BitVec 64) {o : Nat} (h : o + 8 ≤ 512) :
    rd64 (write64 m B o x) B o = x :=
  rd64_write64_self m x (by omega)

theorem rw32_ne (m : Mem) (x : BitVec 32) {o o' : Nat} (h : o + 4 ≤ 512) (h' : o' + 4 ≤ 512)
    (hs : o + 4 ≤ o' ∨ o' + 4 ≤ o) : (m.writeW (addr B o) x).readW (addr B o') 32 = m.readW (addr B o') 32 :=
  readW_writeW_addr m x (by omega) (by omega) hs.symm

end

/-- A 64-bit word in memory, as its halves. -/
theorem rd64_eq {m : Mem} {x : BitVec 32} {o : Nat} (h : x.toNat + o + 8 ≤ 2 ^ 32) :
    rd64 m x o = m.readW (x.setWidth 64 + BitVec.ofNat 64 o) 64 := by
  rw [readW64, show x.setWidth 64 + BitVec.ofNat 64 o + 4 = x.setWidth 64 + BitVec.ofNat 64 (o + 4) from
      Offset.add_ofNat_add_ofNat _ _ 4, ← addr_eq (by omega), ← addr_eq (by omega)]
  rfl

theorem stateAt_rd64 {x : BitVec 32} (hfit : x.toNat + 64 ≤ 2 ^ 32) (m : Mem) {k : Nat} (hk : k < 8) :
    (stateAt 64 m (x.setWidth 64))[k] = rd64 m x (8 * k) := by
  simp only [stateAt, Vector.getElem_ofFn]
  rw [rd64_eq (by omega)]

/-! ## Copying words -/

/-- Copying `n` words `[src + so + 4j]` to `[esi + d + 4j]`, through `eax`, into
the region `R`, which the words copied are outside of. -/
theorem copyWords_ok {src : Reg} (hsrc : src ≠ .eax) {S D : BitVec 32} {so d n : Nat} {R : Region}
    {s : State} (hS : s.gpr src = S) (hD : s.gpr .esi = D) (hfit : D.toNat + d + 4 * n ≤ 2 ^ 32)
    (hin : ∀ j < n, InRegions (s.rd ++ s.wr) (addr S (so + 4 * j)) 4)
    (hout : ∀ j < n, InRegions s.wr (addr D (d + 4 * j)) 4)
    (hR : ∀ j < n, R.Contains (addr D (d + 4 * j)) 4)
    (hdis : ∀ j < n, Region.Disjoint ⟨addr S (so + 4 * j), 4⟩ R) :
    WP isa (.block (copyWords src so d n)) s fun s' =>
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [R] s.mem s'.mem ∧
      ∀ j < n, s'.mem.readW (addr D (d + 4 * j)) 32 = s.mem.readW (addr S (so + 4 * j)) 32 := by
  unfold copyWords
  refine wp_range_flatMap (M := isa) (fun k (s' : State) => (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [R] s.mem s'.mem ∧
      ∀ j < k, s'.mem.readW (addr D (d + 4 * j)) 32 = s.mem.readW (addr S (so + 4 * j)) 32)
    (fun k s' hk ⟨hg, hrd, hwr, hf, hc⟩ => ?_) n (Nat.le_refl _) s
    ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  refine wp_movm (ea_of ((hg src hsrc).trans hS) _) (by rw [hrd, hwr]; exact hin k hk)
    fun s₁ u₁ => ?_
  refine wp_store (ea_of (by rw [u₁.other _ (by decide), hg _ (by decide), hD]) _)
    (by rw [u₁.wr, hwr]; exact hout k hk) fun s₂ u₂ => WP.block_nil ?_
  have hv : s'.mem.readW (addr S (so + 4 * k)) 32 = s.mem.readW (addr S (so + 4 * k)) 32 :=
    hf.readW (Region.contains_self _ _) (by simpa using hdis k hk) (by decide)
  refine ⟨fun r hr => by rw [u₂.gpr, u₁.other r hr, hg r hr], by rw [u₂.rd, u₁.rd, hrd],
    by rw [u₂.wr, u₁.wr, hwr], ?_, fun j hj => ?_⟩
  · rw [u₂.mem, u₁.mem]; exact hf.writeW (List.mem_singleton_self _) _ (hR k hk)
  · rw [u₂.mem, u₁.gpr, u₁.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [readW_writeW_addr _ _ (by omega) (by omega) (by omega)]; exact hc j hj
    · rw [Mem.readW_writeW_self32, hv]

/-! ## The rest of the work vector -/

section
variable {rest : List Instr} {Q : State → Prop} {B : BitVec 32} {s : State}

theorem ivWord_ok (hD : s.gpr .esi = B) (hA : Acc s.wr B 512) {k : Nat} (hk : vOff k + 8 ≤ 512)
    (v : BitVec 64)
    (K : ∀ s', (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = write64 s.mem B (vOff k) v → WP isa (.block rest) s' Q) :
    WP isa (.block (ivWord k v ++ rest)) s Q := by
  simp only [ivWord, List.cons_append, List.nil_append]
  refine wp_movi fun s₁ u₁ => wp_store (ea_of (by rw [u₁.other _ (by decide), hD]) _)
    (by rw [u₁.wr]; exact hA _ (by omega)) fun s₂ u₂ => wp_movi fun s₃ u₃ =>
    wp_store (ea_of (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hD]) _)
    (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hA _ (by omega)) fun s₄ u₄ => K s₄ ?_ ?_ ?_ ?_
  · intro r hr; rw [u₄.gpr, u₃.other r hr, u₂.gpr, u₁.other r hr]
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₄.mem, u₃.gpr, u₃.mem, u₂.mem, u₁.gpr, u₁.mem]; rfl

theorem ivXor_ok (hD : s.gpr .esi = B) (hA : Acc s.wr B 512) (hfit : B.toNat + 512 ≤ 2 ^ 32)
    {k o : Nat} (hk : vOff k + 8 ≤ 512) (ho : o + 8 ≤ 512) (hs : Sep8 (vOff k) o) (v : BitVec 64)
    (K : ∀ s', (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = write64 s.mem B (vOff k) (v ^^^ rd64 s.mem B o) → WP isa (.block rest) s' Q) :
    WP isa (.block (ivXor k v o ++ rest)) s Q := by
  simp only [ivXor, List.cons_append, List.nil_append]
  refine wp_movi fun s₁ u₁ => ?_
  refine wp_xorS (readSrc_mem (by rw [u₁.other _ (by decide), hD])
    (by rw [u₁.rd, u₁.wr]; exact mem_rd (hA _ (by omega)))) fun s₂ u₂ => ?_
  refine wp_store (ea_of (by rw [u₂.other _ (by decide), u₁.other _ (by decide), hD]) _)
    (by rw [u₂.wr, u₁.wr]; exact hA _ (by omega)) fun s₃ u₃ => wp_movi fun s₄ u₄ => ?_
  have h₄ : s₄.gpr .esi = B := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hD]
  have w₄ : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have r₄ : s₄.rd = s.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  refine wp_xorS (readSrc_mem h₄ (by rw [r₄, w₄]; exact mem_rd (hA _ (by omega))))
    fun s₅ u₅ => ?_
  refine wp_store (ea_of (by rw [u₅.other _ (by decide), h₄]) _)
    (by rw [u₅.wr, w₄]; exact hA _ (by omega)) fun s₆ u₆ => K s₆ ?_ ?_ ?_ ?_
  · intro r hr
    rw [u₆.gpr, u₅.other r hr, u₄.other r hr, u₃.gpr, u₂.other r hr, u₁.other r hr]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₆.wr, u₅.wr, w₄]
  · rw [u₆.mem, u₅.gpr, u₅.mem, u₄.gpr, u₄.mem, u₃.mem, u₂.gpr, u₁.gpr, u₂.mem, u₁.mem,
      readW_writeW_addr _ _ (by omega) (by omega) (by simp only [Sep8] at hs; omega)]
    simp only [write64, rd64, lo_xor, hi_xor, lo_append, hi_append]
    rfl

end

/-! ## XORing the work vector into the state -/

/-- After `n` words of `finish`, from the state `s₁`. -/
structure FI (s₀ s₁ : State) (n : Nat) (s : State) : Prop where
  gpr : ∀ r, r ≠ .eax → s.gpr r = s₁.gpr r
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  frame : Frame [stR s₀] s₁.mem s.mem
  words : ∀ j < 16, s.mem.readW (addr (st s₀) (4 * j)) 32 =
    if j < n then s₁.mem.readW (addr (st s₀) (4 * j)) 32 ^^^
      s₁.mem.readW (addr (scr s₀) (vOff 0 + 4 * j)) 32 ^^^
      s₁.mem.readW (addr (scr s₀) (vOff 8 + 4 * j)) 32
    else s₁.mem.readW (addr (st s₀) (4 * j)) 32

theorem finishWord_ok {s₀ : State} (hp : Pre s₀) {s₁ : State} (hc : s₁.gpr .ecx = st s₀)
    (he : s₁.gpr .esi = scr s₀) (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (n : Nat) (hn : n < 16)
    (s : State) (hf : FI s₀ s₁ n s) :
    WP isa (.block (finishWord n)) s (FI s₀ s₁ (n + 1)) := by
  have fS := hp.st_fits
  have fV := hp.scr_fits
  have hw : s.wr = s₀.wr := hf.wr.trans hwr
  have hsc : s.gpr .ecx = st s₀ := (hf.gpr _ (by decide)).trans hc
  have hsi : s.gpr .esi = scr s₀ := (hf.gpr _ (by decide)).trans he
  -- The scratch words are unchanged.
  have kv : ∀ d, d + 4 ≤ 512 → s.mem.readW (addr (scr s₀) d) 32 = s₁.mem.readW (addr (scr s₀) d) 32 :=
    fun d hd => hf.frame.readW (contains_addr (len := 512) hd (by omega) fV)
      (by simpa using hp.st_scr.symm) (by decide)
  simp only [finishWord]
  refine wp_movm (ea_of hsc _) (by rw [hf.rd, hrd, hw]; exact hp.in_st rfl (by omega))
    fun s₂ u₂ => ?_
  refine wp_xorS (readSrc_mem (by rw [u₂.other _ (by decide), hsi])
    (by rw [u₂.rd, u₂.wr, hf.rd, hrd, hw]; exact hp.in_scr rfl (by simp only [vOff]; omega)))
    fun s₃ u₃ => ?_
  refine wp_xorS (readSrc_mem (by rw [u₃.other _ (by decide), u₂.other _ (by decide), hsi])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, hf.rd, hrd, hw]; exact hp.in_scr rfl (by simp only [vOff]; omega)))
    fun s₄ u₄ => ?_
  refine wp_store (ea_of (by rw [u₄.other _ (by decide), u₃.other _ (by decide),
    u₂.other _ (by decide), hsc]) _) (by rw [u₄.wr, u₃.wr, u₂.wr, hw]; exact hp.accS rfl _ (by omega))
    fun s₅ u₅ => WP.block_nil ?_
  have hv : s₅.mem = s.mem.writeW (addr (st s₀) (4 * n))
      (s.mem.readW (addr (st s₀) (4 * n)) 32 ^^^ s.mem.readW (addr (scr s₀) (vOff 0 + 4 * n)) 32 ^^^
        s.mem.readW (addr (scr s₀) (vOff 8 + 4 * n)) 32) := by
    rw [u₅.mem, u₄.gpr, u₄.mem, u₃.gpr, u₃.mem, u₂.gpr, u₂.mem]
  refine ⟨fun r hr => ?_, by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, hf.rd],
    by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, hf.wr], ?_, fun j hj => ?_⟩
  · rw [u₅.gpr, u₄.other r hr, u₃.other r hr, u₂.other r hr, hf.gpr r hr]
  · rw [hv]
    exact hf.frame.writeW (List.mem_singleton_self _) _ (contains_addr (by omega) (by omega) fS)
  · rw [hv]
    rcases Nat.lt_or_ge j n with hjn | hjn
    · rw [readW_writeW_addr _ _ (by omega) (by omega) (by omega), hf.words j hj]
      simp only [hjn, show j < n + 1 by omega, ite_true]
    · rcases Nat.eq_or_lt_of_le hjn with rfl | hjn'
      · rw [Mem.readW_writeW_self32, hf.words _ hj, kv _ (by simp only [vOff]; omega),
          kv _ (by simp only [vOff]; omega)]
        simp only [Nat.lt_irrefl, ite_false, Nat.lt_succ_self, ite_true]
      · rw [readW_writeW_addr _ _ (by omega) (by omega) (by omega), hf.words j hj]
        simp only [show ¬ j < n by omega, show ¬ j < n + 1 by omega, ite_false]

theorem finishWords_ok {s₀ : State} (hp : Pre s₀) {s₁ : State} (hc : s₁.gpr .ecx = st s₀)
    (he : s₁.gpr .esi = scr s₀) (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) :
    WP isa (.block ((List.range 16).flatMap finishWord)) s₁ (FI s₀ s₁ 16) :=
  wp_range_flatMap (M := isa) (FI s₀ s₁) (fun k s hk h => finishWord_ok hp hc he hrd hwr k hk s h) 16
    (Nat.le_refl _) s₁ ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun j _ => by
      simp only [Nat.not_lt_zero, ite_false]⟩

/-- The state after `finish`, word by word. -/
theorem FI.state {s₀ s₁ s : State} (hf : FI s₀ s₁ 16 s) {k : Nat} (hk : k < 8) :
    rd64 s.mem (st s₀) (8 * k) = rd64 s₁.mem (st s₀) (8 * k) ^^^ rd64 s₁.mem (scr s₀) (vOff k) ^^^
      rd64 s₁.mem (scr s₀) (vOff (k + 8)) := by
  have e₀ := hf.words (2 * k) (by omega)
  have e₁ := hf.words (2 * k + 1) (by omega)
  rw [ite_eq_left_iff.mpr (fun h => absurd (by omega) h)] at e₀ e₁
  rw [show vOff 0 + 4 * (2 * k) = vOff k by simp only [vOff]; omega,
    show vOff 8 + 4 * (2 * k) = vOff (k + 8) by simp only [vOff]; omega,
    show 4 * (2 * k) = 8 * k by omega] at e₀
  rw [show vOff 0 + 4 * (2 * k + 1) = vOff k + 4 by simp only [vOff]; omega,
    show vOff 8 + 4 * (2 * k + 1) = vOff (k + 8) + 4 by simp only [vOff]; omega,
    show 4 * (2 * k + 1) = 8 * k + 4 by omega] at e₁
  rw [← hi_append_lo (rd64 s₁.mem (st s₀) (8 * k) ^^^ _ ^^^ _), hi_xor, hi_xor, lo_xor, lo_xor,
    hi_rd64, hi_rd64, hi_rd64, lo_rd64, lo_rd64, lo_rd64, ← e₀, ← e₁]
  rfl

/-! ## Advancing to the next block -/

section
variable {rest : List Instr} {Q : State → Prop} {s : State}

theorem wp_movC {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ s', Upd s s' d v → s'.cf = s.cf → WP isa (.block rest) s' Q) :
    WP isa (.block (.mov d src :: rest)) s Q :=
  Proof.Sha256.X86.Stream.WP.cons (s' := s.setReg d v) (by simp [exec, h])
    (k _ (Upd.setReg _ _ _) rfl)

theorem wp_storeC {m : MemOp} {r : Reg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', Mupd s s' (s.mem.writeW a (s.gpr r)) → s'.cf = s.cf → s'.zf = s.zf →
      WP isa (.block rest) s' Q) :
    WP isa (.block (.store m r :: rest)) s Q := by
  refine Proof.Sha256.X86.Stream.WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr r) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl⟩ rfl rfl)
  simp [exec, State.store32, ha, hout]

theorem wp_adcC {d : Reg} {v : BitVec 32} {c : Bool} (hc : s.cf = some c)
    (k : ∀ s', Upd s s' d (s.gpr d + v + (BitVec.ofBool c).setWidth 32) →
      s'.cf = some (decide (2 ^ 32 ≤ (s.gpr d).toNat + v.toNat + c.toNat)) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (.alu .adc d (.imm v) :: rest)) s Q :=
  Proof.Sha256.X86.Stream.WP.cons (by simp [exec, execAlu, readSrc, hc]; rfl)
    (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_addC {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d + v) → s'.cf = some (decide (2 ^ 32 ≤ (s.gpr d).toNat + v.toNat)) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: rest)) s Q :=
  Proof.Sha256.X86.Stream.WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

end

/-- The parameters after `advance`: the block's address and the 128-bit
counter advanced by 128 bytes, and the count of blocks decremented. -/
def advMem (B : BitVec 32) (m : Mem) : Mem :=
  let T0 := m.readW (addr B tOff) 32
  let T1 := m.readW (addr B (tOff + 4)) 32
  let T2 := m.readW (addr B (tOff + 8)) 32
  let T3 := m.readW (addr B (tOff + 12)) 32
  let c0 := decide (2 ^ 32 ≤ T0.toNat + (128 : BitVec 32).toNat)
  let c1 := decide (2 ^ 32 ≤ T1.toNat + (0 : BitVec 32).toNat + c0.toNat)
  let c2 := decide (2 ^ 32 ≤ T2.toNat + (0 : BitVec 32).toNat + c1.toNat)
  ((((((m.writeW (addr B blOff) (m.readW (addr B blOff) 32 + 128)).writeW (addr B tOff)
    (T0 + 128)).writeW (addr B (tOff + 4)) (T1 + 0 + (BitVec.ofBool c0).setWidth 32)).writeW
    (addr B (tOff + 8)) (T2 + 0 + (BitVec.ofBool c1).setWidth 32)).writeW (addr B (tOff + 12))
    (T3 + 0 + (BitVec.ofBool c2).setWidth 32)).writeW (addr B nOff) (m.readW (addr B nOff) 32 - 1))

theorem advance_ok {B : BitVec 32} (hfit : B.toNat + 512 ≤ 2 ^ 32) {s : State}
    (hD : s.gpr .esi = B) (hA : Acc s.wr B 512) :
    WP isa (.block advance) s fun s' =>
      s'.mem = advMem B s.mem ∧ s'.zf = some (s.mem.readW (addr B nOff) 32 - 1 == 0) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have r32 := rw32_ne hfit
  have inr : ∀ (rs : List Region) (o : Nat), o + 4 ≤ 512 → InRegions (rs ++ s.wr) (addr B o) 4 :=
    fun rs o ho => let ⟨r, hr, hc⟩ := hA o ho; ⟨r, List.mem_append_right _ hr, hc⟩
  unfold advance
  -- The block's address.
  refine wp_movm (ea_of hD _) (mem_rd (hA blOff (by decide))) fun s₁ u₁ => ?_
  refine wp_addC fun s₂ u₂ _ => ?_
  have e₂ : s₂.gpr .esi = B := by rw [u₂.other _ (by decide), u₁.other _ (by decide), hD]
  have w₂ : s₂.wr = s.wr := by rw [u₂.wr, u₁.wr]
  refine wp_storeC (ea_of e₂ _) (by rw [w₂]; exact hA blOff (by decide)) fun s₃ u₃ _ _ => ?_
  -- The counter.
  refine wp_movm (ea_of (by rw [u₃.gpr, e₂]) _) (by rw [u₃.wr, w₂]; exact inr _ tOff (by decide))
    fun s₄ u₄ => ?_
  refine wp_addC fun s₅ u₅ c₅ => ?_
  have e₅ : s₅.gpr .esi = B := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, e₂]
  have w₅ : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, w₂]
  refine wp_storeC (ea_of e₅ _) (by rw [w₅]; exact hA tOff (by decide)) fun s₆ u₆ f₆ _ => ?_
  refine wp_movC (readSrc_mem (by rw [u₆.gpr, e₅]) (by rw [u₆.wr, w₅]; exact inr _ (tOff + 4) (by decide)))
    fun s₇ u₇ f₇ => ?_
  refine wp_adcC (f₇.trans (f₆.trans c₅)) fun s₈ u₈ c₈ => ?_
  have e₈ : s₈.gpr .esi = B := by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, e₅]
  have w₈ : s₈.wr = s.wr := by rw [u₈.wr, u₇.wr, u₆.wr, w₅]
  refine wp_storeC (ea_of e₈ _) (by rw [w₈]; exact hA (tOff + 4) (by decide)) fun s₉ u₉ f₉ _ => ?_
  refine wp_movC (readSrc_mem (by rw [u₉.gpr, e₈]) (by rw [u₉.wr, w₈]; exact inr _ (tOff + 8) (by decide)))
    fun s₁₀ u₁₀ f₁₀ => ?_
  refine wp_adcC (f₁₀.trans (f₉.trans c₈)) fun s₁₁ u₁₁ c₁₁ => ?_
  have e₁₁ : s₁₁.gpr .esi = B := by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr, e₈]
  have w₁₁ : s₁₁.wr = s.wr := by rw [u₁₁.wr, u₁₀.wr, u₉.wr, w₈]
  refine wp_storeC (ea_of e₁₁ _) (by rw [w₁₁]; exact hA (tOff + 8) (by decide)) fun s₁₂ u₁₂ f₁₂ _ => ?_
  refine wp_movC (readSrc_mem (by rw [u₁₂.gpr, e₁₁]) (by rw [u₁₂.wr, w₁₁]; exact inr _ (tOff + 12) (by decide)))
    fun s₁₃ u₁₃ f₁₃ => ?_
  refine wp_adcC (f₁₃.trans (f₁₂.trans c₁₁)) fun s₁₄ u₁₄ _ => ?_
  have e₁₄ : s₁₄.gpr .esi = B := by rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr, e₁₁]
  have w₁₄ : s₁₄.wr = s.wr := by rw [u₁₄.wr, u₁₃.wr, u₁₂.wr, w₁₁]
  refine wp_storeC (ea_of e₁₄ _) (by rw [w₁₄]; exact hA (tOff + 12) (by decide)) fun s₁₅ u₁₅ _ _ => ?_
  -- The count.
  refine wp_movm (ea_of (by rw [u₁₅.gpr, e₁₄]) _)
    (by rw [u₁₅.wr, w₁₄]; exact inr _ nOff (by decide)) fun s₁₆ u₁₆ => ?_
  refine wp_subi fun s₁₇ u₁₇ z₁₇ => ?_
  have e₁₇ : s₁₇.gpr .esi = B := by rw [u₁₇.other _ (by decide), u₁₆.other _ (by decide), u₁₅.gpr, e₁₄]
  have w₁₇ : s₁₇.wr = s.wr := by rw [u₁₇.wr, u₁₆.wr, u₁₅.wr, w₁₄]
  refine wp_storeC (ea_of e₁₇ _) (by rw [w₁₇]; exact hA nOff (by decide)) fun s₁₈ u₁₈ _ z₁₈ =>
    WP.block_nil ⟨?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · simp (disch := decide) only [advMem, u₁₈.mem, u₁₇.gpr, u₁₇.mem, u₁₆.gpr, u₁₆.mem,
      u₁₅.mem, u₁₄.gpr, u₁₄.mem, u₁₃.gpr, u₁₃.mem, u₁₂.mem, u₁₁.gpr, u₁₁.mem,
      u₁₀.gpr, u₁₀.mem, u₉.mem, u₈.gpr, u₈.mem, u₇.gpr, u₇.mem, u₆.mem, u₅.gpr,
      u₅.mem, u₄.gpr, u₄.mem, u₃.mem, u₂.gpr, u₂.mem, u₁.gpr, u₁.mem, r32]
  · rw [z₁₈, z₁₇]
    simp (disch := decide) only [u₁₆.gpr, u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem,
      u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, r32]
  · rw [u₁₈.gpr, u₁₇.other r hr, u₁₆.other r hr, u₁₅.gpr, u₁₄.other r hr, u₁₃.other r hr, u₁₂.gpr,
      u₁₁.other r hr, u₁₀.other r hr, u₉.gpr, u₈.other r hr, u₇.other r hr, u₆.gpr, u₅.other r hr,
      u₄.other r hr, u₃.gpr, u₂.other r hr, u₁.other r hr]
  · rw [u₁₈.rd, u₁₇.rd, u₁₆.rd, u₁₅.rd, u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd,
      u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₁₈.wr, w₁₇]

end VG.Proof.Blake2.X86.CompressB

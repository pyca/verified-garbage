module

public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Blocks
public import VerifiedGarbage.Proof.Aes.AArch64.Vperm
public import VerifiedGarbage.Impl.Aes.AArch64.OneBlock
public import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Gcm.Spec
meta import VerifiedGarbage.Proof.Aes.AArch64.Aese.Blocks
meta import VerifiedGarbage.Proof.Aes.AArch64.Vperm
meta import VerifiedGarbage.Impl.Aes.AArch64.OneBlock
meta import VerifiedGarbage.Proof.Framework.AArch64.Tbl
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Gcm.Spec

-- separate module: it needs the lemmas of the AES extension's proofs (`Aese/`), which import `Blocks.lean`.

/-!
# AES on AArch64: one block, and the S-box in the table registers

`setup` loads the S-box into the table registers, for the key expansion
(`setup_ok`, `Consts`).

`vg_aes_encrypt_blocks` (`encryptBlocksN`) encrypts one to four blocks one at
a time by vector permutations (`Vperm.core_ok`, `few_wp`) and runs the
bitsliced code otherwise (`fewOr_wp`, `encryptBlocksN_correct`), against the
contract of the bitsliced code, `blocksAArch64`; so does `vg_aes_ctr32`
(`ctr32N`, `ctrFew_wp`, `ctr32N_correct`, against `ctr32AArch64`), on the
counter block, whose `inc₃₂` it writes back (`ctrOneLoad_ok`).
-/

@[expose] public section

namespace VG.Proof.Aes.AArch64.OneBlock

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl VG.Impl.Tbl.AArch64
open VG.Impl.Aes.AArch64 VG.Impl.Aes.AArch64.OneBlock
open VG.Proof.Aes.Vector (st KeyIs rnds rnds_zero rnds_succ cipher_eq eor_st aesmc_st keyIs_readW
  vbyte_mapBytes vbyte_shiftRows vbyte_mixColumns ext_vbyte st_ext getD_st getD_shiftRows getD_subBytes
  getD_ofFn vbyte_readW)
open VG.Spec.Aes (roundKey cipher invCipher addRoundKey bytesAt subBytes shiftRows mixColumns)
open VG.Proof.Aes.AArch64.Vperm (Loaded halves_append)

/-! ## The tables and constants -/

/-- What `setup` leaves in the vector registers. -/
structure Consts (s : State) : Prop where
  tab : ∀ k < 256, tbyte s.v k = aesSbox (BitVec.ofNat 8 k)
  v4 : s.v .v4 = shiftIdx
  v5 : s.v .v5 = bc 0x80
  v6 : s.v .v6 = bc 0x40
  v7 : s.v .v7 = bc 0x1b

theorem Consts.of_v {s t : State} (h : Consts s)
    (hv : ∀ r, r ∉ [VReg.v0, .v1, .v2, .v3] → t.v r = s.v r) : Consts t :=
  ⟨fun k hk => by
      rw [tbyte_congr' (fun a ha => hv _ (by
        have hn := treg_ne a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1⟩)) k hk]
      exact h.tab k hk,
    (hv _ (by decide)).trans h.v4, (hv _ (by decide)).trans h.v5, (hv _ (by decide)).trans h.v6,
    (hv _ (by decide)).trans h.v7⟩

theorem tabWords_length : tabWords.length = 40 := by simp [tabWords]

/-- The two words of vector `j` of the static, as `ldrqTbl` loads them. -/
theorem tabWords_pair {j : Nat} (hj : j < 20) :
    tabWords.getD (16 * j / 8 + 1) 0 ++ tabWords.getD (16 * j / 8) 0 = tabVec j := by
  have g : ∀ i < 40, tabWords.getD i 0 = (tabVec (i / 2)).extractLsb' (64 * (i % 2)) 64 := fun i hi => by
    simp [tabWords, hi]
  rw [show 16 * j / 8 = 2 * j by omega_arith, g _ (by omega_arith), g _ (by omega_arith),
    show (2 * j + 1) / 2 = j by omega_arith, show (2 * j + 1) % 2 = 1 by omega_arith,
    show 2 * j / 2 = j by omega_arith, show 2 * j % 2 = 0 by omega_arith]
  exact halves_append _

/-- Loading vector `j` of the static, whose address is in `x6`. -/
theorem exec_tld (r : VReg) {j : Nat} (hj : j < 20) {s : State} (hx : s.gpr .x6 = s.syms tabName) :
    exec (tld r j) s = some (s.setV r (tabVec j)) := by
  have hc : s.gpr .x6 = s.syms tabName ∧ 16 * j % 16 = 0 ∧ 16 * j < 65536 ∧
      16 * j / 8 + 2 ≤ tabWords.length :=
    ⟨hx, by omega_arith, by omega_arith, by rw [tabWords_length]; omega_arith⟩
  simp only [tld, exec, ite_eq_left_of_eq_true _ _ (eq_true hc), tabWords_pair hj]

/-- One load, then more code. -/
theorem tld_ok {r : VReg} {j : Nat} (hj : j < 20) {s : State} (hx : s.gpr .x6 = s.syms tabName) :
    WP isa (.block [tld r j]) s fun t => t.v r = tabVec j ∧ (∀ w, w ≠ r → t.v w = s.v w) ∧ Loaded s t := by
  rw [WP.block_cons_iff]
  exact ⟨_, exec_tld r hj hx, WP.block_nil ⟨v_setV_self _ _ _, fun w hw => v_setV_of_ne _ _ hw,
    Loaded.setV _ _ _⟩⟩

/-- The S-box from the static into the table registers. -/
theorem tldTable_ok {s : State} (hx : s.gpr .x6 = s.syms tabName) :
    WP isa (.block ((List.range 16).map fun r => tld (treg r) r)) s fun t =>
      (∀ r < 16, t.v (treg r) = tabVec r) ∧ (∀ w, (∀ r < 16, w ≠ treg r) → t.v w = s.v w) ∧ Loaded s t := by
  suffices h : ∀ n ≤ 16, WP isa (.block ((List.range n).map fun r => tld (treg r) r)) s fun t =>
      (∀ r < n, t.v (treg r) = tabVec r) ∧ (∀ w, (∀ r < n, w ≠ treg r) → t.v w = s.v w) ∧ Loaded s t from
    h 16 (Nat.le_refl _)
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨fun _ h => absurd h (by omega_arith), fun _ _ => rfl, Loaded.refl s⟩
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (ih (by omega_arith)) fun a ⟨arow, av, al⟩ => ?_
    refine WP.mono (tld_ok (r := treg n) (j := n) (by omega_arith) (by rw [al.gpr, al.syms]; exact hx))
      fun b ⟨brow, bv, bl⟩ => ⟨fun r hr => ?_, fun w hw => ?_, al.trans bl⟩
    · by_cases he : r = n
      · subst he; exact brow
      · rw [bv _ (fun e => he (treg_inj r (by omega_arith) n (by omega_arith) e)), arow r (by omega_arith)]
    · rw [bv _ (hw n (by omega_arith)), av w (fun r hr => hw r (by omega_arith))]

/-- `setup`: the tables and constants, from the static, through `x6`. -/
theorem setup_ok (s : State) :
    WP isa (.block setup) s fun t => Consts t ∧ t.v .v0 = s.v .v0 ∧
      (∀ g, g ≠ .x6 → g ≠ .x7 → t.gpr g = s.gpr g) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp := by
  unfold setup
  let a := s.write .x .x6 (s.syms tabName)
  have ax : a.gpr .x6 = a.syms tabName := gpr_write_self _ _ _ _
  rw [List.singleton_append, WP.block_cons_iff]
  refine ⟨a, exec_adrSym, ?_⟩
  rw [WP.block_append_iff]
  refine WP.mono (tldTable_ok ax) fun b ⟨brow, bv, bl⟩ => ?_
  have bx : b.gpr .x6 = b.syms tabName := by rw [bl.gpr, bl.syms]; exact ax
  rw [show ([tld .v4 16, tld .v5 17, tld .v6 18, tld .v7 19] : List Instr) =
    [tld .v4 16] ++ ([tld .v5 17] ++ ([tld .v6 18] ++ [tld .v7 19])) from rfl, WP.block_append_iff]
  refine WP.mono (tld_ok (by decide) bx) fun c ⟨c4, cv, cl⟩ => ?_
  have cx : c.gpr .x6 = c.syms tabName := by rw [cl.gpr, cl.syms]; exact bx
  rw [WP.block_append_iff]
  refine WP.mono (tld_ok (by decide) cx) fun d ⟨d5, dv, dl⟩ => ?_
  have dx : d.gpr .x6 = d.syms tabName := by rw [dl.gpr, dl.syms]; exact cx
  rw [WP.block_append_iff]
  refine WP.mono (tld_ok (by decide) dx) fun e ⟨e6, ev, el⟩ => ?_
  have ex : e.gpr .x6 = e.syms tabName := by rw [el.gpr, el.syms]; exact dx
  refine WP.mono (tld_ok (by decide) ex) fun t ⟨t7, tv, tl⟩ => ?_
  have l := (((bl.trans cl).trans dl).trans el).trans tl
  refine ⟨⟨fun k hk => ?_, ?_, ?_, ?_, ?_⟩, ?_, fun g h6 _ => ?_, l.mem, l.rd, l.wr, l.sp⟩
  · have hn := treg_ne8 (k / 16) (by omega_arith)
    rw [tbyte, tv _ hn.2.2.2.2.2.2.2, ev _ hn.2.2.2.2.2.2.1, dv _ hn.2.2.2.2.2.1, cv _ hn.2.2.2.2.1,
      brow _ (by omega_arith), tabVec, ite_eq_left (by omega_arith), vbyte_ofVBytes _ (by omega_arith)]
    congr 2; omega_arith
  · rw [tv _ (by decide), ev _ (by decide), dv _ (by decide), c4]; rfl
  · rw [tv _ (by decide), ev _ (by decide), d5]; rfl
  · rw [tv _ (by decide), e6]; rfl
  · rw [t7]; rfl
  · rw [tv _ (by decide), ev _ (by decide), dv _ (by decide), cv _ (by decide),
      bv _ (fun r hr => (treg_ne8 r hr).1.symm)]
    rfl
  · rw [l.gpr]; exact gpr_write_of_ne _ _ _ h6

/-! ## `vg_aes_encrypt_blocks` -/

/-- The registers the bitsliced code saves are none of those `encryptOne`
writes. -/
theorem sreg_ne : ∀ i < 10, sreg i ≠ .x0 ∧ sreg i ≠ .x1 ∧ sreg i ≠ .x6 ∧ sreg i ≠ .x7 := by decide

/-! ## A few blocks, one at a time -/

/-- What `few` needs of `core`: `v0 := f(v0)`, with the schedule at `x0` and
the rounds in `x1`, writing no other general register but `x6`. -/
def CoreOk (core : Prog isa) (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) : Prop :=
  ∀ {s : State} {K : Addr} {R : Nat}, (⟨K, 240⟩ : Region) ∈ s.rd → s.gpr .x0 = K →
    s.gpr .x1 = BitVec.ofNat 64 R → (R = 10 ∨ R = 12 ∨ R = 14) →
    WP isa core s fun t =>
      st (t.v .v0) = f R (bytesAt s.mem K (16 * (R + 1))) (st (s.v .v0)) ∧
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x6 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.sp = s.sp

theorem enc_coreOk : CoreOk Vperm.core cipher := fun hK h0 h1 hR => Vperm.core_ok hK h0 h1 hR

theorem dec_coreOk : CoreOk Vperm.Dec.core invCipher :=
  fun hK h0 h1 hR => Vperm.Dec.core_ok hK h0 h1 hR

/-- The general registers `few` writes. -/
def fewRegs : List Reg := [.x0, .x1, .x2, .x3, .x6, .x9, .x10]

theorem sreg_few : ∀ i < 10, sreg i ∉ fewRegs := by decide

/-- Before block `k` of `few`. -/
structure FInv (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (s₀ : State) (k : Nat)
    (s : State) : Prop where
  hk : k < (s₀.gpr .x3).toNat
  x0 : s.gpr .x0 = s₀.gpr .x0
  x1 : s.gpr .x1 = BitVec.ofNat 64 (s₀.gpr .x1).toNat
  x9 : s.gpr .x9 = s₀.gpr .x0
  x10 : s.gpr .x10 = BitVec.ofNat 64 (s₀.gpr .x1).toNat
  x2 : s.gpr .x2 = s₀.gpr .x2 + BitVec.ofNat 64 (16 * k)
  x3 : s.gpr .x3 = BitVec.ofNat 64 ((s₀.gpr .x3).toNat - k)
  keep : ∀ r, r ∉ fewRegs → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  data : EcbInv s₀.mem s.mem (s₀.gpr .x2) (s₀.gpr .x3).toNat k
    (ecbOut f s₀.mem (s₀.gpr .x2) (s₀.gpr .x1).toNat
      (bytesAt s₀.mem (s₀.gpr .x0) (16 * ((s₀.gpr .x1).toNat + 1))))
  frame : Frame [⟨s₀.gpr .x2, 16 * (s₀.gpr .x3).toNat⟩] s₀.mem s.mem

/-- After `few`. -/
def FDone (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) (s₀ s : State) : Prop :=
  (∀ r, r ∉ fewRegs → s.gpr r = s₀.gpr r) ∧ (Proof.Aes.blocksAArch64 f).post s₀ s

theorem fewBody_ok {core : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hc : CoreOk core f) {s₀ : State} (hp : (Proof.Aes.blocksAArch64 f).pre s₀) {k : Nat}
    {s : State} (hi : FInv f s₀ k s) :
    WP isa (fewBody core) s fun s' =>
      (AArch64.eval (.nonzero .x .x3) s' = some false ∧ FDone f s₀ s') ∨
      (AArch64.eval (.nonzero .x .x3) s' = some true ∧ FInv f s₀ (k + 1) s') := by
  obtain ⟨hrd, hwr, dSD, -, dDS, hwrap, hR⟩ := hp
  have hk := hi.hk
  have hwD : (⟨s₀.gpr .x2, 16 * (s₀.gpr .x3).toNat⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  have hrS : (⟨s₀.gpr .x0, 240⟩ : Region) ∈ s₀.rd := by rw [hrd]; simp
  have n16 : 16 * (s₀.gpr .x3).toNat < 2 ^ 64 := by
    refine Nat.lt_of_not_le fun hc => dDS (s₀.gpr .x4) ?_ (by simp [Region.Contains])
    simp only [Region.Contains]
    have := (s₀.gpr .x4 - s₀.gpr .x2).isLt
    omega_using [hc, this]
  have hR14 : (s₀.gpr .x1).toNat ≤ 14 := by rcases hR with h | h | h <;> omega_using [h]
  have ha : s.gpr .x2 + BitVec.ofNat 64 0 = s₀.gpr .x2 + BitVec.ofNat 64 (16 * k) := by
    rw [BitVec.add_zero, hi.x2]
  have hcon : (⟨s₀.gpr .x2, 16 * (s₀.gpr .x3).toNat⟩ : Region).Contains
      (s₀.gpr .x2 + BitVec.ofNat 64 (16 * k)) 16 :=
    Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk, n16])
  unfold fewBody
  -- The block.
  let a := s.setV .v0 (s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 0) 128)
  refine WP.seq (WP.of_runBlock ⟨a, by
    rw [runBlock_cons, Aese.exec_ldrq (off := 0) (by decide) (by
      rw [ha, hi.rd, hi.wr]; exact ⟨_, List.mem_append_right _ hwD, hcon⟩), runStep_some,
      runBlock_nil], ?_⟩)
  -- The cipher.
  refine WP.seq (WP.mono (hc (s := a) (K := s₀.gpr .x0) (R := (s₀.gpr .x1).toNat)
    (by show _ ∈ s.rd; rw [hi.rd]; exact hrS) hi.x0 hi.x1 hR) fun b ⟨bst, bg, bm, brd, bwr, _⟩ => ?_)
  have hm : b.mem = s.mem := bm
  have hw : bytesAt s.mem (s₀.gpr .x0) (16 * ((s₀.gpr .x1).toNat + 1)) =
      bytesAt s₀.mem (s₀.gpr .x0) (16 * ((s₀.gpr .x1).toNat + 1)) := by
    simp only [bytesAt]
    exact List.map_congr_left fun i hi' => hi.frame.bytes (R := ⟨s₀.gpr .x0, 240⟩)
      (by simp only [List.mem_singleton, forall_eq]; exact dSD) (show (240 : Nat) ≤ 2 ^ 64 by decide)
      (show i < 240 by have := List.mem_range.mp hi'; omega_using [this, hR14])
  have b2 : b.gpr .x2 + BitVec.ofNat 64 0 = s₀.gpr .x2 + BitVec.ofNat 64 (16 * k) := by
    rw [bg _ (by decide) (by decide) (by decide)]; exact ha
  have hv : ∀ t < 16, vbyte (b.v .v0) t =
      (ecbOut f s₀.mem (s₀.gpr .x2) (s₀.gpr .x1).toNat
        (bytesAt s₀.mem (s₀.gpr .x0) (16 * ((s₀.gpr .x1).toNat + 1))) k).getD t 0 := by
    intro t ht
    rw [← getD_st _ ht, bst]
    show (f _ (bytesAt s.mem _ _) (st (s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 0) 128))).getD t 0 = _
    rw [hw, ha, Aese.st_readW, ecbInv_orig hi.data (Nat.le_refl _) hk]
    rfl
  obtain ⟨hd', hf'⟩ := Aese.ecbInv_write (v := b.v .v0) (by omega_using [n16]) hk hi.data hv
  -- The store, and on to the next block.
  let c₁ : State := { b with mem := b.mem.write (b.gpr .x2 + BitVec.ofNat 64 0) 16 (b.v .v0) }
  let c₂ := c₁.write .x .x2 (c₁.read .x .x2 + BitVec.ofNat 64 16)
  let c₃ := c₂.write .x .x3 (c₂.read .x .x3 - BitVec.ofNat 64 1)
  let c₄ := c₃.write .x .x0 (c₃.read .x .x9 + BitVec.ofNat 64 0)
  let c₅ := c₄.write .x .x1 (c₄.read .x .x10 + BitVec.ofNat 64 0)
  refine WP.of_runBlock ⟨c₅, by
    simp only [movR]
    rw [runBlock_cons, Aese.exec_strq (off := 0) (by decide) (by
        rw [b2, bwr]; show InRegions s.wr _ _; rw [hi.wr]; exact ⟨_, hwD, hcon⟩), runStep_some,
      runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
      exec_subImm_x (by decide), runStep_some, runBlock_cons, exec_addImm_x (by decide),
      runStep_some, runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
  have bk : ∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x6 → b.gpr r = s.gpr r := bg
  have cg : ∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → c₅.gpr r = b.gpr r :=
    fun r h0 h1 h2 h3 => by simp [c₅, c₄, c₃, c₂, c₁, State.write, h0, h1, h2, h3]
  have c0 : c₅.gpr .x0 = s₀.gpr .x0 := by
    have e : c₅.gpr .x0 = b.gpr .x9 := by simp [c₅, c₄, c₃, c₂, c₁, State.write, State.read]
    rw [e, bk _ (by decide) (by decide) (by decide)]; exact hi.x9
  have c1 : c₅.gpr .x1 = BitVec.ofNat 64 (s₀.gpr .x1).toNat := by
    have e : c₅.gpr .x1 = b.gpr .x10 := by simp [c₅, c₄, c₃, c₂, c₁, State.write, State.read]
    rw [e, bk _ (by decide) (by decide) (by decide)]; exact hi.x10
  have c2 : c₅.gpr .x2 = s₀.gpr .x2 + BitVec.ofNat 64 (16 * (k + 1)) := by
    have e : c₅.gpr .x2 = b.gpr .x2 + BitVec.ofNat 64 16 := by
      simp [c₅, c₄, c₃, c₂, c₁, State.write, State.read]
    rw [e, bk _ (by decide) (by decide) (by decide), hi.x2, BitVec.add_assoc, ← BitVec.ofNat_add,
      show 16 * k + 16 = 16 * (k + 1) by omega_using []]
  have c3 : c₅.gpr .x3 = BitVec.ofNat 64 ((s₀.gpr .x3).toNat - (k + 1)) := by
    have e : c₅.gpr .x3 = b.gpr .x3 - BitVec.ofNat 64 1 := by
      simp [c₅, c₄, c₃, c₂, c₁, State.write, State.read]
    rw [e, bk _ (by decide) (by decide) (by decide), hi.x3,
      Offset.ofNat_sub_ofNat (by omega_using [hk]),
      show (s₀.gpr .x3).toNat - k - 1 = (s₀.gpr .x3).toNat - (k + 1) by omega_using []]
  have cm : c₅.mem = s.mem.write (s₀.gpr .x2 + BitVec.ofNat 64 (16 * k)) 16 (b.v .v0) := by
    show b.mem.write (b.gpr .x2 + BitVec.ofNat 64 0) 16 (b.v .v0) = _
    rw [b2, hm]
  have ck : ∀ r, r ∉ fewRegs → c₅.gpr r = s₀.gpr r := fun r hr => by
    simp only [fewRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [cg r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1, bk r hr.1 hr.2.1 hr.2.2.2.2.1]
    exact hi.keep r (by simp [fewRegs, hr])
  have hz := Aese.eval_nonzero c3 (by omega_using [n16])
  by_cases hlast : k + 1 = (s₀.gpr .x3).toNat
  · refine .inl ⟨hz.trans (by simp [hlast]), ck, ?_⟩
    show Spec.Aes.statesAt c₅.mem (s₀.gpr .x2) (s₀.gpr .x3).toNat = _
    rw [cm]
    have hE := hd'
    rw [hlast] at hE
    refine (statesAt_of_ecbInv hE).trans ?_
    simp only [Spec.Aes.statesAt, List.map_map]
    rfl
  · refine .inr ⟨hz.trans (by
        simp [show (s₀.gpr .x3).toNat - (k + 1) ≠ 0 by omega_using [hk, hlast]]),
      { hk := by omega_using [hk, hlast]
        x0 := c0
        x1 := c1
        x9 := (cg _ (by decide) (by decide) (by decide) (by decide)).trans
          ((bk _ (by decide) (by decide) (by decide)).trans hi.x9)
        x10 := (cg _ (by decide) (by decide) (by decide) (by decide)).trans
          ((bk _ (by decide) (by decide) (by decide)).trans hi.x10)
        x2 := c2
        x3 := c3
        keep := ck
        rd := brd.trans hi.rd
        wr := bwr.trans hi.wr
        data := by rw [cm]; exact hd'
        frame := by rw [cm]; exact hi.frame.trans hf' }⟩

/-- `few core`: `f` of each block, in place. -/
theorem few_wp {core : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hc : CoreOk core f) {s₀ : State} (hp : (Proof.Aes.blocksAArch64 f).pre s₀)
    (hn : (s₀.gpr .x3).toNat ≠ 0) : WP isa (few core) s₀ (FDone f s₀) := by
  unfold few
  let s₁ := s₀.write .x .x9 (s₀.read .x .x0 + BitVec.ofNat 64 0)
  let s₂ := s₁.write .x .x10 (s₁.read .x .x1 + BitVec.ofNat 64 0)
  refine WP.seq (WP.of_runBlock ⟨s₂, by
    simp only [movR]
    rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
      exec_addImm_x (by decide), runStep_some, runBlock_nil], ?_⟩)
  have g : ∀ r, r ≠ .x9 → r ≠ .x10 → s₂.gpr r = s₀.gpr r := fun r h9 h10 => by
    simp [s₂, s₁, State.write, h9, h10]
  have hi : FInv f s₀ 0 s₂ :=
    { hk := by omega_using [hn]
      x0 := g _ (by decide) (by decide)
      x1 := by rw [g _ (by decide) (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]
      x9 := by simp [s₂, s₁, State.write, State.read]
      x10 := by simp [s₂, s₁, State.write, State.read]
      x2 := by rw [g _ (by decide) (by decide)]; simp
      x3 := by rw [g _ (by decide) (by decide)]; simp
      keep := fun r hr => by
        simp only [fewRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        exact g r hr.2.2.2.2.2.1 hr.2.2.2.2.2.2
      rd := rfl
      wr := rfl
      data := fun i _ => by show s₀.mem _ = _; simp
      frame := Frame.refl _ _ }
  refine WP.loop (M := isa) (fun m s => ∃ k, m = (s₀.gpr .x3).toNat - k ∧ FInv f s₀ k s)
    (fun m s hs => ?_) (s₀.gpr .x3).toNat s₂ ⟨0, by simp, hi⟩
  obtain ⟨k, rfl, hi⟩ := hs
  refine WP.mono (fewBody_ok hc hp hi) fun s' h => ?_
  rcases h with ⟨hz, hd⟩ | ⟨hz, hi'⟩
  · exact .inl ⟨hz, hd⟩
  · exact .inr ⟨hz, (s₀.gpr .x3).toNat - (k + 1), by have := hi'.hk; omega_using [this], k + 1,
      rfl, hi'⟩

/-- `isFew`: `x6` is zero only if there is a block. -/
theorem isFew_ok (s₀ : State) :
    ∃ s₁, runBlock isa isFew s₀ = some s₁ ∧ (∀ r, r ≠ .x6 → s₁.gpr r = s₀.gpr r) ∧
      s₁.mem = s₀.mem ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧
      AArch64.eval (.zero .x .x6) s₁ = some ((s₀.gpr .x3 - 1) >>> 2 == 0) ∧
      (((s₀.gpr .x3 - 1) >>> 2 == 0) = true → (s₀.gpr .x3).toNat ≠ 0) := by
  let u := s₀.write .x .x6 (s₀.read .x .x3 - BitVec.ofNat 64 1)
  let t := u.write .x .x6 (u.read .x .x6 >>> 2)
  refine ⟨t, by
    rw [isFew, runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_cons,
      exec_lsr_x (by decide), runStep_some, runBlock_nil],
    fun r hr => by simp [t, u, State.write, hr], rfl, rfl, rfl,
    by simp [AArch64.eval, State.read, t, u, State.write], fun h h0 => ?_⟩
  have e : s₀.gpr .x3 = 0 := BitVec.eq_of_toNat_eq h0
  rw [e] at h
  exact absurd h (by decide)

/-- A function that takes one to four blocks one at a time (`few`), and any
other number through `batch`. -/
theorem fewOr_wp {core batch : Prog isa} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    (hc : CoreOk core f) {s₀ : State} (hp : (Proof.Aes.blocksAArch64 f).pre s₀)
    {Q : State → Prop}
    (hfew : ∀ s', (∀ r, r ∉ fewRegs → s'.gpr r = s₀.gpr r) → (Proof.Aes.blocksAArch64 f).post s₀ s' →
      Q s')
    (hbatch : ∀ s₁, (Proof.Aes.blocksAArch64 f).pre s₁ → (∀ r, r ≠ .x6 → s₁.gpr r = s₀.gpr r) →
      (∀ t, (Proof.Aes.blocksAArch64 f).post s₁ t = (Proof.Aes.blocksAArch64 f).post s₀ t) →
      WP isa batch s₁ Q) :
    WP isa (.seq (.block isFew) (.ite (.zero .x .x6) (few core) batch)) s₀ Q := by
  obtain ⟨s₁, h₁, g₁, m₁, rd₁, wr₁, hev, hne⟩ := isFew_ok s₀
  refine WP.seq (WP.of_runBlock ⟨s₁, h₁, ?_⟩)
  have e : ∀ r, r ≠ .x6 → s₁.gpr r = s₀.gpr r := g₁
  have hp₁ : (Proof.Aes.blocksAArch64 f).pre s₁ := by
    obtain ⟨a, b, c, d, e', f', g'⟩ := hp
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [e .x0 (by decide), e .x1 (by decide), e .x2 (by decide), e .x3 (by decide),
        e .x4 (by decide), rd₁, wr₁] <;> with_reducible assumption
  have hpost : ∀ t, (Proof.Aes.blocksAArch64 f).post s₁ t = (Proof.Aes.blocksAArch64 f).post s₀ t :=
    fun t => by
      show (Spec.Aes.statesAt t.mem (s₁.gpr .x2) (s₁.gpr .x3).toNat = _) = _
      rw [e .x0 (by decide), e .x1 (by decide), e .x2 (by decide), e .x3 (by decide), m₁]
      rfl
  refine WP.ite _ hev (fun hb => ?_) (fun _ => hbatch s₁ hp₁ e hpost)
  refine WP.mono (few_wp hc hp₁ (by rw [e .x3 (by decide)]; exact hne hb)) fun s' ⟨hk, hq⟩ => ?_
  refine hfew s' (fun r hr => ?_) (by rw [← hpost s']; exact hq)
  rw [hk r hr]
  exact e r (by simp only [fewRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; exact hr.2.2.2.2.1)

/-- `encryptBlocksN`: one to four blocks one at a time (`few_wp`), any other
number of blocks bitsliced. -/
theorem encryptBlocksN_wp {s₀ : State} (hp : (Proof.Aes.blocksAArch64 Spec.Aes.cipher).pre s₀) :
    WP isa encryptBlocksN s₀ fun s' =>
      (∀ i < 10, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧ (Proof.Aes.blocksAArch64 Spec.Aes.cipher).post s₀ s' := by
  unfold encryptBlocksN
  refine fewOr_wp enc_coreOk hp (fun s' hk hq => ⟨fun i hi => hk _ (sreg_few i hi), hq⟩)
    fun s₁ hp₁ g₁ hpost => ?_
  exact WP.mono (correct_blocks encrypt4_cryptOk hp₁) fun s' ⟨hsv, hq⟩ =>
    ⟨fun i hi => (hsv i hi).trans (g₁ _ (sreg_ne i hi).2.2.1), by rw [← hpost s']; exact hq⟩

theorem encryptBlocksN_correct (s : State) (hs : (Proof.Aes.blocksAArch64 Spec.Aes.cipher).pre s) :
    ∃ t s', Exec isa encryptBlocksN s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksAArch64 Spec.Aes.cipher).post s s' := by
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ :=
    WP.gprs (rs := [.x30]) (encryptBlocksN_wp hs) (by lit_decide) (by lit_decide)
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁ 0 (by omega_arith)
  · exact h₁ 1 (by omega_arith)
  · exact h₁ 2 (by omega_arith)
  · exact h₁ 3 (by omega_arith)
  · exact h₁ 4 (by omega_arith)
  · exact h₁ 5 (by omega_arith)
  · exact h₁ 6 (by omega_arith)
  · exact h₁ 7 (by omega_arith)
  · exact h₁ 8 (by omega_arith)
  · exact h₁ 9 (by omega_arith)
  · exact h₃ _ (by simp)

theorem encryptBlocksN_ct : ConstantTime isa (Proof.Aes.blocksAArch64 Spec.Aes.cipher).pre
    (Proof.Aes.blocksAArch64 Spec.Aes.cipher).pub encryptBlocksN := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem encryptBlocksN_verified :
    Verified AArch64.target encryptBlocksN (Proof.Aes.encryptBlocksRoundsContract AArch64.abi) :=
  Verified.of_correct encryptBlocksN_correct encryptBlocksN_ct (by
    sig_implies [Proof.Aes.encryptBlocksRoundsContract, Spec.Aes.blocksSig, Proof.Aes.blocksAArch64,
      AArch64.abi, AArch64.argRegs] [blocksSat] using blocksSat)

/-! ## `vg_aes_decrypt_blocks` -/

/-- `decryptBlocksN`: one to four blocks one at a time (`few_wp`), any other
number of blocks bitsliced. -/
theorem decryptBlocksN_wp {s₀ : State} (hp : (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).pre s₀) :
    WP isa decryptBlocksN s₀ fun s' =>
      (∀ i < 10, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧ (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).post s₀ s' := by
  unfold decryptBlocksN
  refine fewOr_wp dec_coreOk hp (fun s' hk hq => ⟨fun i hi => hk _ (sreg_few i hi), hq⟩)
    fun s₁ hp₁ g₁ hpost => ?_
  exact WP.mono (correct_blocks decrypt4_cryptOk hp₁) fun s' ⟨hsv, hq⟩ =>
    ⟨fun i hi => (hsv i hi).trans (g₁ _ (sreg_ne i hi).2.2.1), by rw [← hpost s']; exact hq⟩

theorem decryptBlocksN_correct (s : State) (hs : (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).pre s) :
    ∃ t s', Exec isa decryptBlocksN s t s' ∧ abiPreserved s s' ∧
      (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).post s s' := by
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ :=
    WP.gprs (rs := [.x30]) (decryptBlocksN_wp hs) (by lit_decide) (by lit_decide)
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁ 0 (by omega_arith)
  · exact h₁ 1 (by omega_arith)
  · exact h₁ 2 (by omega_arith)
  · exact h₁ 3 (by omega_arith)
  · exact h₁ 4 (by omega_arith)
  · exact h₁ 5 (by omega_arith)
  · exact h₁ 6 (by omega_arith)
  · exact h₁ 7 (by omega_arith)
  · exact h₁ 8 (by omega_arith)
  · exact h₁ 9 (by omega_arith)
  · exact h₃ _ (by simp)

theorem decryptBlocksN_ct : ConstantTime isa (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).pre
    (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).pub decryptBlocksN := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-! ## `vg_aes_ctr32` -/

/-- The counter block, as an AES state. -/
theorem st_ctr (m : Mem) (p : Addr) :
    st (m.readW (p + BitVec.ofNat 64 0) 128) = ctrState (Spec.Gcm.blockAt m p) 0 := by
  apply st_ext; intro j hj
  rw [getD_st _ hj, ctrState, getD_ofFn hj, vbyte_readW _ _ hj, BitVec.add_zero]
  exact (toBytes_blockAt m p hj).symm

/-- `ctrOneLoad`: the counter block in `v0`, and its last four bytes, as a
big-endian integer, plus one, written back. -/
theorem ctrOneLoad_ok (s : State) (hc : (⟨s.gpr .x2, 16⟩ : Region) ∈ s.wr) :
    WP isa (.block ctrOneLoad) s fun a =>
      a.v .v0 = s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 0) 128 ∧
      a.mem = s.mem.writeW (s.gpr .x2 + BitVec.ofNat 64 12)
        (rev32 (rev32 (s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 12) 32) + BitVec.ofNat 32 1)) ∧
      (∀ r, r ≠ .x6 → a.gpr r = s.gpr r) ∧ a.rd = s.rd ∧ a.wr = s.wr ∧ a.sp = s.sp := by
  have hc' := List.mem_append_right s.rd hc
  rw [ctrOneLoad, WP.block_cons_iff]
  refine ⟨_, Aese.exec_ldrq (off := 0) (by decide)
    (in_off (off := 0) (n := 16) hc' (by omega_arith) (by omega_arith)), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_ldr_w (off := 12) (by decide)
    (in_off (off := 12) (n := 4) hc' (by omega_arith) (by omega_arith)), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_rev32, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, Aese.exec_addImm_w (imm := 1) (by decide), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_rev32, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_str_w (off := 12) (by decide)
    (in_off (off := 12) (n := 4) hc (by omega_arith) (by omega_arith)), WP.block_nil ?_⟩
  refine ⟨rfl, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp [State.setV, State.write, State.read, sw_32]
  · simp [State.setV, State.write, hr]

/-- With no block, the contracts ask for nothing. -/
theorem ctr32_none {s : State} (h4 : (s.gpr .x4).toNat = 0) : Proof.Aes.ctr32AArch64.post s s := by
  show Spec.Gcm.blocksAt s.mem (s.gpr .x3) (s.gpr .x4).toNat = _ ∧ Spec.Gcm.blockAt s.mem (s.gpr .x2) = _
  rw [h4]
  exact ⟨rfl, rfl⟩

theorem ctr32To_none {s : State} (h4 : (s.gpr .x4).toNat = 0) : Proof.Aes.ctr32ToAArch64.post s s := by
  show Spec.Gcm.blocksAt s.mem (s.gpr .x6) (s.gpr .x4).toNat = _ ∧ Spec.Gcm.blockAt s.mem (s.gpr .x2) = _
  rw [h4]
  exact ⟨rfl, rfl⟩

theorem toNat_of_beq_zero {x : BitVec 64} (h : (x == 0) = true) : x.toNat = 0 := by
  rw [eq_of_beq h]; rfl

/-! ## A few blocks of counter mode, one at a time -/

/-- The precondition of both contracts, in place and out of place (`to`):
`Aese.Pre`, and that the counter block does not overlap the data, nor the
schedule the output. -/
structure PreC (to : Bool) (s₀ : State) : Prop where
  pre : Aese.Pre to s₀
  c_d : Region.Disjoint ⟨Aese.cp s₀, 16⟩ (Aese.dR s₀)
  s_o : Region.Disjoint ⟨s₀.gpr .x0, 240⟩ (Aese.oR s₀ to)

theorem prec_of {s₀ : State} (h : Proof.Aes.ctr32AArch64.pre s₀) : PreC false s₀ := by
  have hp := Aese.pre_of h
  obtain ⟨_, _, _, h4, _, h6, _, _, _, _⟩ := h
  exact ⟨hp, h6, h4⟩

theorem precTo_of {s₀ : State} (h : Proof.Aes.ctr32ToAArch64.pre s₀) : PreC true s₀ := by
  have hp := Aese.preTo_of h
  obtain ⟨_, _, _, h4, _, h6, _, _, _, _, _, _, _, _⟩ := h
  exact ⟨hp, h6, h4⟩

/-- The data not yet done is as it was. -/
theorem PreC.src {to : Bool} {s₀ : State} (hp : PreC to s₀) {m : Mem} {c : Nat}
    (hf : Frame [⟨Aese.cp s₀, 16⟩, Aese.oR s₀ to] s₀.mem m)
    (hd : DataInvM s₀.mem m (Aese.dp s₀) (Aese.op s₀ to) (Aese.nb s₀) c (Aese.kst s₀)) :
    ∀ i, 16 * c ≤ i → i < 16 * Aese.nb s₀ →
      m (Aese.dp s₀ + BitVec.ofNat 64 i) = s₀.mem (Aese.dp s₀ + BitVec.ofNat 64 i) := by
  have hn := hp.pre.nb16
  cases to with
  | false =>
    intro i h1 h2
    have := hd i h2
    rw [ite_eq_right (by omega_using [h1])] at this
    exact this
  | true =>
    intro i _ h2
    exact hf.bytes (R := Aese.dR s₀)
      (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨hp.c_d.symm, hp.pre.src rfl⟩)
      hn h2

/-- The general registers `ctrFew` writes. -/
def ctrFewRegs : List Reg := [.x0, .x1, .x3, .x4, .x6, .x8, .x9, .x10]

theorem sreg_ctrFew : ∀ i < 10, sreg i ∉ ctrFewRegs := by decide

/-- Before block `k` of `ctrFew`. -/
structure CFInv (to : Bool) (s₀ : State) (k : Nat) (s : State) : Prop where
  hk : k < Aese.nb s₀
  x0 : s.gpr .x0 = s₀.gpr .x0
  x1 : s.gpr .x1 = BitVec.ofNat 64 (Aese.nr s₀)
  x9 : s.gpr .x9 = s₀.gpr .x0
  x10 : s.gpr .x10 = BitVec.ofNat 64 (Aese.nr s₀)
  x2 : s.gpr .x2 = Aese.cp s₀
  x3 : s.gpr .x3 = Aese.dp s₀ + BitVec.ofNat 64 (16 * k)
  x8 : s.gpr .x8 = Aese.op s₀ to + BitVec.ofNat 64 (16 * k)
  x4 : s.gpr .x4 = BitVec.ofNat 64 (Aese.nb s₀ - k)
  keep : ∀ r, r ∉ ctrFewRegs → s.gpr r = s₀.gpr r
  ctr : Spec.Gcm.blockAt s.mem (Aese.cp s₀) = Nat.repeat Spec.Gcm.inc32 k (Aese.cb s₀)
  data : DataInvM s₀.mem s.mem (Aese.dp s₀) (Aese.op s₀ to) (Aese.nb s₀) k (Aese.kst s₀)
  frame : Frame [⟨Aese.cp s₀, 16⟩, Aese.oR s₀ to] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem ctrFewBody_ok {to : Bool} {s₀ : State} (hp : PreC to s₀) {k : Nat} {s : State}
    (hi : CFInv to s₀ k s) :
    WP isa ctrFewBody s fun s' =>
      (AArch64.eval (.nonzero .x .x4) s' = some false ∧
        (∀ r, r ∉ ctrFewRegs → s'.gpr r = s₀.gpr r) ∧ Aese.Post to s₀ s') ∨
      (AArch64.eval (.nonzero .x .x4) s' = some true ∧ CFInv to s₀ (k + 1) s') := by
  have hn := hp.pre.n16
  have hk := hi.hk
  have hR := hp.pre.rounds
  have hR14 : Aese.nr s₀ ≤ 14 := by rcases hR with h | h | h <;> omega_using [h]
  have hC : (⟨s.gpr .x2, 16⟩ : Region) ∈ s.wr := by rw [hi.x2, hi.wr, hp.pre.wr]; simp
  have dco : ∀ r ∈ [(⟨Aese.cp s₀, 16⟩ : Region)], (Aese.oR s₀ to).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.pre.c_o.symm
  unfold ctrFewBody
  refine WP.seq (WP.mono (ctrOneLoad_ok s hC) fun a ⟨av, am, ag, ard, awr, _⟩ => ?_)
  rw [hi.x2] at av am
  -- The counter block.
  have fa : Frame [⟨Aese.cp s₀, 16⟩] s.mem a.mem := by
    rw [am]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (c_off (Aese.cp s₀) (off := 12) (by omega_arith) (by omega_arith))
  have ctrA : Spec.Gcm.blockAt a.mem (Aese.cp s₀) =
      Nat.repeat Spec.Gcm.inc32 (k + 1) (Aese.cb s₀) := by
    have h1 : Spec.Gcm.blockAt a.mem (Aese.cp s₀) =
        Nat.repeat Spec.Gcm.inc32 1 (Spec.Gcm.blockAt s.mem (Aese.cp s₀)) := by
      refine ctr_after (n := 1) fun j hj => ?_
      rw [show (BitVec.ofNat 64 1).setWidth 32 = BitVec.ofNat 32 1 by decide]
      show a.mem (Aese.cp s₀ + BitVec.ofNat 64 j) = _
      rw [am, writeW_apply, off_toNat (Aese.cp s₀) (by omega_using [hj]) (by decide)]
      by_cases h : j < 12
      · rw [ite_eq_right (show ¬ 12 ≤ j by omega_using [h]),
          ite_eq_right (show ¬ 2 ^ 64 + j - 12 < 32 / 8 by omega_using [h]), ite_eq_left h]
      · rw [ite_eq_left (show 12 ≤ j by omega_using [h]),
          ite_eq_left (show j - 12 < 32 / 8 by omega_using [h, hj]), ite_eq_right h,
          BitVec.setWidth_eq]
    rw [h1, hi.ctr]
    rfl
  have f2 : Frame [⟨Aese.cp s₀, 16⟩, Aese.oR s₀ to] s₀.mem a.mem :=
    hi.frame.trans (fa.mono (by simp))
  have hw : bytesAt a.mem (s₀.gpr .x0) (16 * (Aese.nr s₀ + 1)) =
      bytesAt s₀.mem (s₀.gpr .x0) (16 * (Aese.nr s₀ + 1)) := by
    simp only [bytesAt]
    exact List.map_congr_left fun i hi' => f2.bytes (R := ⟨s₀.gpr .x0, 240⟩)
      (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        exact ⟨hp.pre.s_c, hp.s_o⟩)
      (show (240 : Nat) ≤ 2 ^ 64 by decide)
      (show i < 240 by have := List.mem_range.mp hi'; omega_using [this, hR14])
  have hsrc : ∀ t < 16, a.mem (Aese.dp s₀ + BitVec.ofNat 64 (16 * k + t)) =
      s₀.mem (Aese.dp s₀ + BitVec.ofNat 64 (16 * k + t)) := fun t ht => by
    rw [fa.bytes (R := Aese.dR s₀)
      (by simp only [List.mem_singleton, forall_eq]; exact hp.c_d.symm) hp.pre.nb16
      (show 16 * k + t < 16 * Aese.nb s₀ by omega_using [hk, ht])]
    exact hp.src hi.frame hi.data _ (by omega_using []) (by omega_using [hk, ht])
  -- The cipher.
  refine WP.seq (WP.mono (Vperm.core_ok (s := a) (K := s₀.gpr .x0) (R := Aese.nr s₀)
    (by rw [ard, hi.rd, hp.pre.rd]; simp) ((ag _ (by decide)).trans hi.x0)
    ((ag _ (by decide)).trans hi.x1) hR) fun b ⟨bst, bg, bm, brd, bwr, _⟩ => ?_)
  have bgs : ∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x6 → b.gpr r = s.gpr r :=
    fun r h0 h1 h6 => (bg r h0 h1 h6).trans (ag r h6)
  have b3 : b.gpr .x3 + BitVec.ofNat 64 0 = Aese.dp s₀ + BitVec.ofNat 64 (16 * k) := by
    rw [BitVec.add_zero, bgs _ (by decide) (by decide) (by decide), hi.x3]
  have b8 : b.gpr .x8 + BitVec.ofNat 64 0 = Aese.op s₀ to + BitVec.ofNat 64 (16 * k) := by
    rw [BitVec.add_zero, bgs _ (by decide) (by decide) (by decide), hi.x8]
  have brw : b.rd = s₀.rd ∧ b.wr = s₀.wr := ⟨brd.trans (ard.trans hi.rd), bwr.trans (awr.trans hi.wr)⟩
  have hinD : InRegions (b.rd ++ b.wr) (b.gpr .x3 + BitVec.ofNat 64 0) 16 := by
    rw [b3, brw.1, brw.2]
    exact ⟨_, hp.pre.dat, Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk, hn])⟩
  have hinO : InRegions b.wr (b.gpr .x8 + BitVec.ofNat 64 0) 16 := by
    rw [b8, brw.2]
    exact ⟨_, hp.pre.out, Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk, hn])⟩
  -- The data, and on to the next block.
  let d₁ := b.setV .v1 (b.mem.readW (b.gpr .x3 + BitVec.ofNat 64 0) 128)
  let d₂ := d₁.setV .v0 (d₁.v .v0 ^^^ d₁.v .v1)
  let d₃ : State := { d₂ with mem := d₂.mem.write (d₂.gpr .x8 + BitVec.ofNat 64 0) 16 (d₂.v .v0) }
  let d₄ := d₃.write .x .x3 (d₃.read .x .x3 + BitVec.ofNat 64 16)
  let d₅ := d₄.write .x .x8 (d₄.read .x .x8 + BitVec.ofNat 64 16)
  let d₆ := d₅.write .x .x4 (d₅.read .x .x4 - BitVec.ofNat 64 1)
  let d₇ := d₆.write .x .x0 (d₆.read .x .x9 + BitVec.ofNat 64 0)
  let d₈ := d₇.write .x .x1 (d₇.read .x .x10 + BitVec.ofNat 64 0)
  refine WP.of_runBlock ⟨d₈, by
    simp only [movR]
    rw [runBlock_cons, Aese.exec_ldrq (off := 0) (by decide) hinD, runStep_some, runBlock_cons,
      show exec (.vop (.logic .eor .v0 .v0 .v1)) d₁ = some d₂ from rfl, runStep_some,
      runBlock_cons, Aese.exec_strq (s := d₂) (off := 0) (by decide) hinO, runStep_some,
      runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
      exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_subImm_x (by decide),
      runStep_some, runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
      exec_addImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
  have v0₂ : d₂.v .v0 =
      b.v .v0 ^^^ a.mem.readW (Aese.dp s₀ + BitVec.ofNat 64 (16 * k)) 128 := by
    show (d₁.setV _ _).v .v0 = _
    rw [v_setV_self]
    show (b.setV _ _).v .v0 ^^^ (b.setV _ _).v .v1 = _
    rw [v_setV_of_ne _ _ (by decide), v_setV_self, b3, bm]
  have dm : d₈.mem = a.mem.write (Aese.op s₀ to + BitVec.ofNat 64 (16 * k)) 16
      (b.v .v0 ^^^ a.mem.readW (Aese.dp s₀ + BitVec.ofNat 64 (16 * k)) 128) := by
    show b.mem.write (b.gpr .x8 + BitVec.ofNat 64 0) 16 (d₂.v .v0) = _
    rw [b8, v0₂, bm]
  have dataA : DataInvM s₀.mem a.mem (Aese.dp s₀) (Aese.op s₀ to) (Aese.nb s₀) k (Aese.kst s₀) :=
    dataInvM_frame fa dco hn hi.data
  obtain ⟨hd', hf'⟩ := dataInvM_store1 hn hk dataA
    (v := b.v .v0 ^^^ a.mem.readW (Aese.dp s₀ + BitVec.ofNat 64 (16 * k)) 128) fun t ht => by
      rw [vbyte_xor, vbyte_readW _ _ ht,
        Offset.add_add_eq (Aese.dp s₀) (show 16 * k + t = 16 * k + t from rfl), hsrc t ht,
        ← getD_st _ ht, bst, hw, av, st_ctr, hi.ctr]
      show _ = keyStream _ _ _ _ ^^^ _
      rw [keyStream, show (16 * k + t) / 16 = k by omega_using [ht],
        show (16 * k + t) % 16 = t by omega_using [ht]]
      rfl
  rw [← dm] at hd' hf'
  have ctrD : Spec.Gcm.blockAt d₈.mem (Aese.cp s₀) =
      Nat.repeat Spec.Gcm.inc32 (k + 1) (Aese.cb s₀) := by
    rw [← ctrA]
    exact VG.Proof.Gcm.blockAt_congr fun j hj => hf'.bytes (R := ⟨Aese.cp s₀, 16⟩)
      (by simp only [List.mem_singleton, forall_eq]; exact hp.pre.c_o)
      (show (16 : Nat) ≤ 2 ^ 64 by decide) hj
  have dg : ∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x8 → d₈.gpr r = b.gpr r :=
    fun r h0 h1 h3 h4 h8 => by
      simp [d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁, State.write, State.setV, h0, h1, h3, h4, h8]
  have d0 : d₈.gpr .x0 = s₀.gpr .x0 := by
    have e : d₈.gpr .x0 = b.gpr .x9 := by
      simp [d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁, State.write, State.read, State.setV]
    rw [e, bgs _ (by decide) (by decide) (by decide)]; exact hi.x9
  have d1 : d₈.gpr .x1 = BitVec.ofNat 64 (Aese.nr s₀) := by
    have e : d₈.gpr .x1 = b.gpr .x10 := by
      simp [d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁, State.write, State.read, State.setV]
    rw [e, bgs _ (by decide) (by decide) (by decide)]; exact hi.x10
  have d3 : d₈.gpr .x3 = Aese.dp s₀ + BitVec.ofNat 64 (16 * (k + 1)) := by
    have e : d₈.gpr .x3 = b.gpr .x3 + BitVec.ofNat 64 16 := by
      simp [d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁, State.write, State.read, State.setV]
    rw [e, bgs _ (by decide) (by decide) (by decide), hi.x3, BitVec.add_assoc, ← BitVec.ofNat_add,
      show 16 * k + 16 = 16 * (k + 1) by omega_using []]
  have d8 : d₈.gpr .x8 = Aese.op s₀ to + BitVec.ofNat 64 (16 * (k + 1)) := by
    have e : d₈.gpr .x8 = b.gpr .x8 + BitVec.ofNat 64 16 := by
      simp [d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁, State.write, State.read, State.setV]
    rw [e, bgs _ (by decide) (by decide) (by decide), hi.x8, BitVec.add_assoc, ← BitVec.ofNat_add,
      show 16 * k + 16 = 16 * (k + 1) by omega_using []]
  have d4 : d₈.gpr .x4 = BitVec.ofNat 64 (Aese.nb s₀ - (k + 1)) := by
    have e : d₈.gpr .x4 = b.gpr .x4 - BitVec.ofNat 64 1 := by
      simp [d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁, State.write, State.read, State.setV]
    rw [e, bgs _ (by decide) (by decide) (by decide), hi.x4,
      Offset.ofNat_sub_ofNat (by omega_using [hk]),
      show Aese.nb s₀ - k - 1 = Aese.nb s₀ - (k + 1) by omega_using []]
  have dk : ∀ r, r ∉ ctrFewRegs → d₈.gpr r = s₀.gpr r := fun r hr => by
    simp only [ctrFewRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [dg r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.2.1, bgs r hr.1 hr.2.1 hr.2.2.2.2.1]
    exact hi.keep r (by simp [ctrFewRegs, hr])
  have hz := Aese.eval_nonzero d4 (by omega_using [hn])
  by_cases hlast : k + 1 = Aese.nb s₀
  · refine .inl ⟨hz.trans (by simp [hlast]), dk, ?_, ?_⟩
    · rw [hlast] at hd'
      exact ctr32_of_dataInvM hd'
    · rw [ctrD, hlast]
  · refine .inr ⟨hz.trans (by simp [show Aese.nb s₀ - (k + 1) ≠ 0 by omega_using [hk, hlast]]),
      { hk := by omega_using [hk, hlast]
        x0 := d0
        x1 := d1
        x9 := (dg _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans
          ((bgs _ (by decide) (by decide) (by decide)).trans hi.x9)
        x10 := (dg _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans
          ((bgs _ (by decide) (by decide) (by decide)).trans hi.x10)
        x2 := (dg _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans
          ((bgs _ (by decide) (by decide) (by decide)).trans hi.x2)
        x3 := d3
        x8 := d8
        x4 := d4
        keep := dk
        ctr := ctrD
        data := hd'
        frame := f2.trans (hf'.mono (by simp))
        rd := brw.1
        wr := brw.2 }⟩

/-- `ctrFew to`: counter mode of the blocks, and the counter block past
them. -/
theorem ctrFew_wp {to : Bool} {s₀ : State} (hp : PreC to s₀) (hn : Aese.nb s₀ ≠ 0) :
    WP isa (ctrFew to) s₀ fun s' =>
      (∀ r, r ∉ ctrFewRegs → s'.gpr r = s₀.gpr r) ∧ Aese.Post to s₀ s' := by
  unfold ctrFew
  let s₁ := s₀.write .x .x8 (s₀.read .x (cond to .x6 .x3) + BitVec.ofNat 64 0)
  let s₂ := s₁.write .x .x9 (s₁.read .x .x0 + BitVec.ofNat 64 0)
  let s₃ := s₂.write .x .x10 (s₂.read .x .x1 + BitVec.ofNat 64 0)
  refine WP.seq (WP.of_runBlock ⟨s₃, by
    simp only [movR]
    rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
      exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_addImm_x (by decide),
      runStep_some, runBlock_nil], ?_⟩)
  have g : ∀ r, r ≠ .x8 → r ≠ .x9 → r ≠ .x10 → s₃.gpr r = s₀.gpr r := fun r h8 h9 h10 => by
    simp [s₃, s₂, s₁, State.write, h8, h9, h10]
  have hi : CFInv to s₀ 0 s₃ :=
    { hk := by omega_using [hn]
      x0 := g _ (by decide) (by decide) (by decide)
      x1 := by
        rw [g _ (by decide) (by decide) (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]
      x9 := by simp [s₃, s₂, s₁, State.write, State.read]
      x10 := by simp [s₃, s₂, s₁, State.write, State.read]
      x2 := g _ (by decide) (by decide) (by decide)
      x3 := by rw [g _ (by decide) (by decide) (by decide)]; simp
      x8 := by cases to <;> simp [s₃, s₂, s₁, State.write, State.read, Aese.op]
      x4 := by rw [g _ (by decide) (by decide) (by decide)]; simp
      keep := fun r hr => by
        simp only [ctrFewRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        exact g r hr.2.2.2.2.2.1 hr.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2
      ctr := rfl
      data := fun i _ => by show s₀.mem _ = _; simp
      frame := Frame.refl _ _
      rd := rfl
      wr := rfl }
  refine WP.loop (M := isa) (fun m s => ∃ k, m = Aese.nb s₀ - k ∧ CFInv to s₀ k s)
    (fun m s hs => ?_) (Aese.nb s₀) s₃ ⟨0, by simp, hi⟩
  obtain ⟨k, rfl, hi⟩ := hs
  refine WP.mono (ctrFewBody_ok hp hi) fun s' h => ?_
  rcases h with ⟨hz, hd⟩ | ⟨hz, hi'⟩
  · exact .inl ⟨hz, hd⟩
  · exact .inr ⟨hz, Aese.nb s₀ - (k + 1), by have := hi'.hk; omega_using [this], k + 1, rfl, hi'⟩

/-- `ctr32N`: nothing for no block, one to four blocks one at a time by the
tables, any other number of blocks by the batch. -/
theorem ctr32N_wp {s₀ : State} (hp : Proof.Aes.ctr32AArch64.pre s₀) :
    WP isa ctr32N s₀ fun s' =>
      (∀ i < 10, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧ Proof.Aes.ctr32AArch64.post s₀ s' := by
  unfold ctr32N
  refine WP.ite (s₀.gpr .x4 == 0) (by simp [AArch64.eval, State.read])
    (fun hz => WP.block_nil ⟨fun _ _ => rfl, ctr32_none (toNat_of_beq_zero hz)⟩) (fun hz => ?_)
  have hn0 : (s₀.gpr .x4).toNat ≠ 0 := fun h => by
    have : s₀.gpr .x4 = 0 := BitVec.eq_of_toNat_eq h
    simp [this] at hz
  let u := s₀.write .x .x6 (s₀.read .x .x4 - BitVec.ofNat 64 1)
  let s₁ := u.write .x .x6 (u.read .x .x6 >>> 2)
  refine WP.seq (WP.of_runBlock ⟨s₁, by
    rw [runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_cons,
      exec_lsr_x (by decide), runStep_some, runBlock_nil], ?_⟩)
  have hp₁ : Proof.Aes.ctr32AArch64.pre s₁ := hp
  have g₁ : ∀ r, r ≠ .x6 → s₁.gpr r = s₀.gpr r := fun r hr => by simp [s₁, u, State.write, hr]
  refine WP.ite ((s₀.gpr .x4 - BitVec.ofNat 64 1) >>> 2 == 0)
    (by simp [AArch64.eval, State.read, s₁, u, State.write]) (fun _ => ?_) (fun _ => ?_)
  · refine WP.mono (ctrFew_wp (prec_of hp₁) hn0) fun s' ⟨hg, hpost⟩ => ⟨fun i hi => ?_, hpost⟩
    exact (hg _ (sreg_ctrFew i hi)).trans (g₁ _ (sreg_ne i hi).2.2.1)
  · exact WP.mono (correct (cpre_of hp₁)) fun s' ⟨hsv, _, hpost⟩ =>
      ⟨fun i hi => (hsv i hi).trans (g₁ _ (sreg_ne i hi).2.2.1), hpost⟩

theorem ctr32N_correct (s : State) (hs : Proof.Aes.ctr32AArch64.pre s) :
    ∃ t s', Exec isa ctr32N s t s' ∧ abiPreserved s s' ∧ Proof.Aes.ctr32AArch64.post s s' := by
  obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ :=
    WP.gprs (rs := [.x30]) (ctr32N_wp hs) (by lit_decide) (by lit_decide)
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁ 0 (by omega_arith)
  · exact h₁ 1 (by omega_arith)
  · exact h₁ 2 (by omega_arith)
  · exact h₁ 3 (by omega_arith)
  · exact h₁ 4 (by omega_arith)
  · exact h₁ 5 (by omega_arith)
  · exact h₁ 6 (by omega_arith)
  · exact h₁ 7 (by omega_arith)
  · exact h₁ 8 (by omega_arith)
  · exact h₁ 9 (by omega_arith)
  · exact h₃ _ (by simp)

theorem ctr32N_ct : ConstantTime isa Proof.Aes.ctr32AArch64.pre Proof.Aes.ctr32AArch64.pub ctr32N := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-! ## `vg_aes_ctr32_to` -/

/-- `ctr32ToN`: as `ctr32N`, out of place. -/
theorem ctr32ToN_wp {s₀ : State} (hp : Proof.Aes.ctr32ToAArch64.pre s₀) :
    WP isa ctr32ToN s₀ fun s' =>
      (∀ i < 10, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧ s'.gpr .x30 = s₀.gpr .x30 ∧
        Proof.Aes.ctr32ToAArch64.post s₀ s' := by
  unfold ctr32ToN
  refine WP.ite (s₀.gpr .x4 == 0) (by simp [AArch64.eval, State.read])
    (fun hz => WP.block_nil ⟨fun _ _ => rfl, rfl, ctr32To_none (toNat_of_beq_zero hz)⟩) (fun hz => ?_)
  have hn0 : (s₀.gpr .x4).toNat ≠ 0 := fun h => by
    have : s₀.gpr .x4 = 0 := BitVec.eq_of_toNat_eq h
    simp [this] at hz
  let u := s₀.write .x .x7 (s₀.read .x .x4 - BitVec.ofNat 64 1)
  let s₁ := u.write .x .x7 (u.read .x .x7 >>> 2)
  refine WP.seq (WP.of_runBlock ⟨s₁, by
    rw [runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_cons,
      exec_lsr_x (by decide), runStep_some, runBlock_nil], ?_⟩)
  have hp₁ : Proof.Aes.ctr32ToAArch64.pre s₁ := hp
  have g₁ : ∀ r, r ≠ .x7 → s₁.gpr r = s₀.gpr r := fun r hr => by simp [s₁, u, State.write, hr]
  refine WP.ite ((s₀.gpr .x4 - BitVec.ofNat 64 1) >>> 2 == 0)
    (by simp [AArch64.eval, State.read, s₁, u, State.write]) (fun _ => ?_) (fun _ => ?_)
  · refine WP.mono (ctrFew_wp (precTo_of hp₁) hn0) fun s' ⟨hg, hpost⟩ => ⟨fun i hi => ?_, ?_, hpost⟩
    · exact (hg _ (sreg_ctrFew i hi)).trans (g₁ _ (sreg_ne i hi).2.2.2)
    · exact (hg _ (by decide)).trans (g₁ _ (by decide))
  · exact WP.mono (correct (to := true) (cpreTo_of hp₁)) fun s' ⟨hsv, h30, hpost⟩ =>
      ⟨fun i hi => (hsv i hi).trans (g₁ _ (sreg_ne i hi).2.2.2), (h30 rfl).trans (g₁ _ (by decide)), hpost⟩

theorem ctr32ToN_correct (s : State) (hs : Proof.Aes.ctr32ToAArch64.pre s) :
    ∃ t s', Exec isa ctr32ToN s t s' ∧ abiPreserved s s' ∧ Proof.Aes.ctr32ToAArch64.post s s' := by
  obtain ⟨t, s', he, h₁, h₃, h₂⟩ := ctr32ToN_wp hs
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, h₂⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h₁ 0 (by omega_arith)
  · exact h₁ 1 (by omega_arith)
  · exact h₁ 2 (by omega_arith)
  · exact h₁ 3 (by omega_arith)
  · exact h₁ 4 (by omega_arith)
  · exact h₁ 5 (by omega_arith)
  · exact h₁ 6 (by omega_arith)
  · exact h₁ 7 (by omega_arith)
  · exact h₁ 8 (by omega_arith)
  · exact h₁ 9 (by omega_arith)
  · exact h₃

theorem ctr32ToN_ct :
    ConstantTime isa Proof.Aes.ctr32ToAArch64.pre Proof.Aes.ctr32ToAArch64.pub ctr32ToN := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5, .x6])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, h5, h6, h7, hsp⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

end VG.Proof.Aes.AArch64.OneBlock

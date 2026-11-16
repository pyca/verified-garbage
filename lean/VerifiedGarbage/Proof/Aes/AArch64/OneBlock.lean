module

public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Blocks
public import VerifiedGarbage.Proof.Aes.AArch64.Vperm
public import VerifiedGarbage.Impl.Aes.AArch64.OneBlock
public import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Aes.AArch64.Aese.Blocks
meta import VerifiedGarbage.Proof.Aes.AArch64.Vperm
meta import VerifiedGarbage.Impl.Aes.AArch64.OneBlock
meta import VerifiedGarbage.Proof.Framework.AArch64.Tbl
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
meta import VerifiedGarbage.Proof.Framework.Contract

-- separate module: it needs the lemmas of the AES extension's proofs (`Aese/`), which import `Blocks.lean`.

/-!
# AES on AArch64: one block, and the S-box in the table registers

`setup` loads the S-box into the table registers, for the key expansion
(`setup_ok`, `Consts`).

`vg_aes_encrypt_blocks` (`encryptBlocksN`) encrypts one block by vector
permutations (`Vperm.core_ok`) and runs the bitsliced code otherwise
(`encryptBlocksN_correct`), against the contract of the bitsliced code,
`blocksAArch64`; so does `vg_aes_ctr32` (`ctr32N`, `ctr32N_correct`,
against `ctr32AArch64`), on the counter block, whose `inc₃₂` it writes back
(`ctrOneLoad_ok`).
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

/-- One block, encrypted in place. -/
theorem encryptOne_ok {s : State} (hp : (Proof.Aes.blocksAArch64 Spec.Aes.cipher).pre s)
    (h3 : (s.gpr .x3).toNat = 1) :
    WP isa encryptOne s fun s' =>
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → s'.gpr r = s.gpr r) ∧
      (Proof.Aes.blocksAArch64 Spec.Aes.cipher).post s s' := by
  obtain ⟨hrd, hwr, -, -, -, -, hR⟩ := hp
  have hwD : (⟨s.gpr .x2, 16 * (s.gpr .x3).toNat⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  rw [h3] at hwD
  have hrS : (⟨s.gpr .x0, 240⟩ : Region) ∈ s.rd := by rw [hrd]; simp
  unfold encryptOne
  -- The block.
  refine WP.seq ?_
  let a := s.setV .v0 (s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 0) 128)
  rw [WP.block_cons_iff]
  refine ⟨a, Aese.exec_ldrq (off := 0) (by decide)
    ⟨_, List.mem_append_right _ hwD, Offset.contains_base (s.gpr .x2) (d := 0) (by decide) (by decide)⟩,
    WP.block_nil ?_⟩
  -- The cipher.
  have a1 : a.gpr .x1 = BitVec.ofNat 64 (s.gpr .x1).toNat := by
    show s.gpr .x1 = _
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono (Vperm.core_ok (s := a) (K := s.gpr .x0) (R := (s.gpr .x1).toNat) hrS rfl a1 hR)
    fun b ⟨bst, bg, bm, brd, bwr, bsp⟩ => ?_)
  -- The block, back.
  have b2 : b.gpr .x2 = s.gpr .x2 := bg _ (by decide) (by decide) (by decide)
  have bm' : b.mem = s.mem := bm
  rw [WP.block_cons_iff]
  refine ⟨_, Aese.exec_strq (off := 0) (by decide) ⟨_, by rw [bwr]; exact hwD,
    by rw [b2]; exact Offset.contains_base (s.gpr .x2) (d := 0) (by decide) (by decide)⟩,
    WP.block_nil ⟨fun r h0 h1 h6 _ => bg r h0 h1 h6, ?_⟩⟩
  have hE := (Aese.ecbInv_write (m₀ := s.mem) (m := b.mem) (D := s.gpr .x2) (n := 1) (k := 0)
    (F := ecbOut cipher s.mem (s.gpr .x2) (s.gpr .x1).toNat
      (bytesAt s.mem (s.gpr .x0) (16 * ((s.gpr .x1).toNat + 1)))) (v := b.v .v0) (by decide) (by decide)
    (fun i hi => by rw [ite_eq_right (by omega_arith), bm']) (fun t ht => by
      rw [← getD_st _ ht, bst, show a.v .v0 = s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 0) 128 from rfl,
        Aese.st_readW]
      rfl)).1
  show Spec.Aes.statesAt (b.mem.write (b.gpr .x2 + BitVec.ofNat 64 0) 16 (b.v .v0)) (s.gpr .x2)
      (s.gpr .x3).toNat = _
  rw [h3, b2]
  refine (statesAt_of_ecbInv hE).trans ?_
  simp only [Spec.Aes.statesAt, List.map_map]
  rfl

/-- `encryptBlocksN`: one block by the tables, any other number of blocks
bitsliced. -/
theorem encryptBlocksN_wp {s₀ : State} (hp : (Proof.Aes.blocksAArch64 Spec.Aes.cipher).pre s₀) :
    WP isa encryptBlocksN s₀ fun s' =>
      (∀ i < 10, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧ (Proof.Aes.blocksAArch64 Spec.Aes.cipher).post s₀ s' := by
  unfold encryptBlocksN
  let s₁ := s₀.write .x .x6 (s₀.read .x .x3 - BitVec.ofNat 64 1)
  refine WP.seq ?_
  rw [WP.block_cons_iff]
  refine ⟨s₁, exec_subImm_x (imm := 1) (by decide), WP.block_nil ?_⟩
  have hp₁ : (Proof.Aes.blocksAArch64 Spec.Aes.cipher).pre s₁ := hp
  have g₁ : ∀ r, r ≠ .x6 → s₁.gpr r = s₀.gpr r := fun r hr => by simp [s₁, State.write, hr]
  refine WP.ite (s₀.gpr .x3 - BitVec.ofNat 64 1 == 0)
    (by simp [AArch64.eval, State.read, s₁, State.write]) (fun hb => ?_) (fun _ => ?_)
  · have x3 : s₀.gpr .x3 = BitVec.ofNat 64 1 := by
      have h := BitVec.sub_add_cancel (s₀.gpr .x3) (BitVec.ofNat 64 1)
      rw [eq_of_beq hb] at h
      exact h.symm.trans (by decide)
    have h3 : (s₁.gpr .x3).toNat = 1 := by
      show (s₀.gpr .x3).toNat = 1
      rw [x3]; rfl
    refine WP.mono (encryptOne_ok hp₁ h3) fun s' ⟨hg, hpost⟩ => ⟨fun i hi => ?_, hpost⟩
    have hn := sreg_ne i hi
    rw [hg _ hn.1 hn.2.1 hn.2.2.1 hn.2.2.2]
    exact g₁ _ hn.2.2.1
  · exact WP.mono (correct_blocks encrypt4_cryptOk hp₁) fun s' ⟨hsv, hpost⟩ =>
      ⟨fun i hi => (hsv i hi).trans (g₁ _ (sreg_ne i hi).2.2.1), hpost⟩

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

/-- One block, decrypted in place. -/
theorem decryptOne_ok {s : State} (hp : (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).pre s)
    (h3 : (s.gpr .x3).toNat = 1) :
    WP isa decryptOne s fun s' =>
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → s'.gpr r = s.gpr r) ∧
      (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).post s s' := by
  obtain ⟨hrd, hwr, -, -, -, -, hR⟩ := hp
  have hwD : (⟨s.gpr .x2, 16 * (s.gpr .x3).toNat⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  rw [h3] at hwD
  have hrS : (⟨s.gpr .x0, 240⟩ : Region) ∈ s.rd := by rw [hrd]; simp
  unfold decryptOne
  -- The block.
  refine WP.seq ?_
  let a := s.setV .v0 (s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 0) 128)
  rw [WP.block_cons_iff]
  refine ⟨a, Aese.exec_ldrq (off := 0) (by decide)
    ⟨_, List.mem_append_right _ hwD, Offset.contains_base (s.gpr .x2) (d := 0) (by decide) (by decide)⟩,
    WP.block_nil ?_⟩
  -- The cipher.
  have a1 : a.gpr .x1 = BitVec.ofNat 64 (s.gpr .x1).toNat := by
    show s.gpr .x1 = _
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono (Vperm.Dec.core_ok (s := a) (K := s.gpr .x0) (R := (s.gpr .x1).toNat) hrS rfl a1 hR)
    fun b ⟨bst, bg, bm, brd, bwr, bsp⟩ => ?_)
  -- The block, back.
  have b2 : b.gpr .x2 = s.gpr .x2 := bg _ (by decide) (by decide) (by decide)
  have bm' : b.mem = s.mem := bm
  rw [WP.block_cons_iff]
  refine ⟨_, Aese.exec_strq (off := 0) (by decide) ⟨_, by rw [bwr]; exact hwD,
    by rw [b2]; exact Offset.contains_base (s.gpr .x2) (d := 0) (by decide) (by decide)⟩,
    WP.block_nil ⟨fun r h0 h1 h6 _ => bg r h0 h1 h6, ?_⟩⟩
  have hE := (Aese.ecbInv_write (m₀ := s.mem) (m := b.mem) (D := s.gpr .x2) (n := 1) (k := 0)
    (F := ecbOut invCipher s.mem (s.gpr .x2) (s.gpr .x1).toNat
      (bytesAt s.mem (s.gpr .x0) (16 * ((s.gpr .x1).toNat + 1)))) (v := b.v .v0) (by decide) (by decide)
    (fun i hi => by rw [ite_eq_right (by omega_arith), bm']) (fun t ht => by
      rw [← getD_st _ ht, bst, show a.v .v0 = s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 0) 128 from rfl,
        Aese.st_readW]
      rfl)).1
  show Spec.Aes.statesAt (b.mem.write (b.gpr .x2 + BitVec.ofNat 64 0) 16 (b.v .v0)) (s.gpr .x2)
      (s.gpr .x3).toNat = _
  rw [h3, b2]
  refine (statesAt_of_ecbInv hE).trans ?_
  simp only [Spec.Aes.statesAt, List.map_map]
  rfl

/-- `decryptBlocksN`: one block by the tables, any other number of blocks
bitsliced. -/
theorem decryptBlocksN_wp {s₀ : State} (hp : (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).pre s₀) :
    WP isa decryptBlocksN s₀ fun s' =>
      (∀ i < 10, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧ (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).post s₀ s' := by
  unfold decryptBlocksN
  let s₁ := s₀.write .x .x6 (s₀.read .x .x3 - BitVec.ofNat 64 1)
  refine WP.seq ?_
  rw [WP.block_cons_iff]
  refine ⟨s₁, exec_subImm_x (imm := 1) (by decide), WP.block_nil ?_⟩
  have hp₁ : (Proof.Aes.blocksAArch64 Spec.Aes.invCipher).pre s₁ := hp
  have g₁ : ∀ r, r ≠ .x6 → s₁.gpr r = s₀.gpr r := fun r hr => by simp [s₁, State.write, hr]
  refine WP.ite (s₀.gpr .x3 - BitVec.ofNat 64 1 == 0)
    (by simp [AArch64.eval, State.read, s₁, State.write]) (fun hb => ?_) (fun _ => ?_)
  · have x3 : s₀.gpr .x3 = BitVec.ofNat 64 1 := by
      have h := BitVec.sub_add_cancel (s₀.gpr .x3) (BitVec.ofNat 64 1)
      rw [eq_of_beq hb] at h
      exact h.symm.trans (by decide)
    have h3 : (s₁.gpr .x3).toNat = 1 := by
      show (s₀.gpr .x3).toNat = 1
      rw [x3]; rfl
    refine WP.mono (decryptOne_ok hp₁ h3) fun s' ⟨hg, hpost⟩ => ⟨fun i hi => ?_, hpost⟩
    have hn := sreg_ne i hi
    rw [hg _ hn.1 hn.2.1 hn.2.2.1 hn.2.2.2]
    exact g₁ _ hn.2.2.1
  · exact WP.mono (correct_blocks decrypt4_cryptOk hp₁) fun s' ⟨hsv, hpost⟩ =>
      ⟨fun i hi => (hsv i hi).trans (g₁ _ (sreg_ne i hi).2.2.1), hpost⟩

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

/-- One block of the counter mode: the counter block encrypted, XORed into
the block of the data, and the counter block incremented. -/
theorem ctr32One_ok {s : State} (hp : Proof.Aes.ctr32AArch64.pre s) (h4 : (s.gpr .x4).toNat = 1) :
    WP isa ctr32One s fun s' =>
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → s'.gpr r = s.gpr r) ∧
      Proof.Aes.ctr32AArch64.post s s' := by
  obtain ⟨hrd, hwr, dSC, -, -, dCD, -, -, -, hR⟩ := hp
  rw [h4] at hwr dCD
  have hC : (⟨s.gpr .x2, 16⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  have hD : (⟨s.gpr .x3, 16 * 1⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  have hS : (⟨s.gpr .x0, 240⟩ : Region) ∈ s.rd := by rw [hrd]; simp
  unfold ctr32One
  refine WP.seq (WP.mono (ctrOneLoad_ok s hC) fun a ⟨av, am, ag, ard, awr, asp⟩ => ?_)
  -- Only the counter block is written.
  have fa : Frame [⟨s.gpr .x2, 16⟩] s.mem a.mem := by
    rw [am]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (c_off (s.gpr .x2) (off := 12) (by omega_arith) (by omega_arith))
  have hw : bytesAt a.mem (s.gpr .x0) (16 * ((s.gpr .x1).toNat + 1)) =
      bytesAt s.mem (s.gpr .x0) (16 * ((s.gpr .x1).toNat + 1)) := by
    simp only [bytesAt]
    exact List.map_congr_left fun i hi => fa.bytes (R := ⟨s.gpr .x0, 240⟩)
      (by simp only [List.mem_singleton, forall_eq]; exact dSC) (show (240 : Nat) ≤ 2 ^ 64 by decide)
      (show i < 240 by have := List.mem_range.mp hi; omega_using [this, hR])
  have fD : ∀ i < 16 * 1, a.mem (s.gpr .x3 + BitVec.ofNat 64 i) = s.mem (s.gpr .x3 + BitVec.ofNat 64 i) :=
    fun i hi => fa.bytes (R := ⟨s.gpr .x3, 16 * 1⟩)
      (by simp only [List.mem_singleton, forall_eq]; exact dCD.symm) (show (16 * 1 : Nat) ≤ 2 ^ 64 by decide) hi
  -- The cipher.
  have a1 : a.gpr .x1 = BitVec.ofNat 64 (s.gpr .x1).toNat := by
    rw [ag _ (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono (Vperm.core_ok (s := a) (K := s.gpr .x0) (R := (s.gpr .x1).toNat)
    (by rw [ard]; exact hS) (ag _ (by decide)) a1 hR) fun b ⟨bst, bg, bm, brd, bwr, bsp⟩ => ?_)
  have b3 : b.gpr .x3 = s.gpr .x3 :=
    (bg _ (by decide) (by decide) (by decide)).trans (ag _ (by decide))
  have bwD : (⟨s.gpr .x3, 16 * 1⟩ : Region) ∈ b.wr := by rw [bwr, awr]; exact hD
  have hin : (⟨s.gpr .x3, 16 * 1⟩ : Region).Contains (b.gpr .x3 + BitVec.ofNat 64 0) 16 := by
    rw [b3]; exact Offset.contains_base (s.gpr .x3) (d := 0) (by decide) (by decide)
  -- The data.
  rw [WP.block_cons_iff]
  refine ⟨_, Aese.exec_ldrq (off := 0) (by decide) ⟨_, List.mem_append_right _ bwD, hin⟩, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, Aese.exec_strq (off := 0) (by decide) ⟨_, bwD, hin⟩, WP.block_nil ?_⟩
  refine ⟨fun r h0 h1 h6 _ => (bg r h0 h1 h6).trans (ag r h6), ?_⟩
  show Spec.Gcm.blocksAt (b.mem.write (b.gpr .x3 + BitVec.ofNat 64 0) 16
        (b.v .v0 ^^^ b.mem.readW (b.gpr .x3 + BitVec.ofNat 64 0) 128)) (s.gpr .x3) (s.gpr .x4).toNat = _ ∧
      Spec.Gcm.blockAt (b.mem.write (b.gpr .x3 + BitVec.ofNat 64 0) 16
        (b.v .v0 ^^^ b.mem.readW (b.gpr .x3 + BitVec.ofNat 64 0) 128)) (s.gpr .x2) = _
  rw [h4, b3, bm]
  have hst := dataInvM_store1 (m₀ := s.mem) (m := a.mem) (D := s.gpr .x3) (O := s.gpr .x3) (n := 1) (k := 0)
    (ks := keyStream (s.gpr .x1).toNat (bytesAt s.mem (s.gpr .x0) (16 * ((s.gpr .x1).toNat + 1)))
      (Spec.Gcm.blockAt s.mem (s.gpr .x2)))
    (v := b.v .v0 ^^^ a.mem.readW (s.gpr .x3 + BitVec.ofNat 64 0) 128) (by decide) (by decide)
    (fun i hi => by rw [ite_eq_right (by omega_arith)]; exact fD i hi)
    (fun t ht => by
      rw [Nat.mul_zero, Nat.zero_add, keyStream, Nat.div_eq_of_lt ht, Nat.mod_eq_of_lt ht, vbyte_xor,
        vbyte_readW _ _ ht, BitVec.add_zero, fD t (by omega_using [ht]), ← getD_st _ ht, bst, hw, av,
        st_ctr])
  rw [Nat.mul_zero] at hst
  obtain ⟨hd, hf⟩ := hst
  refine ⟨ctr32_of_dataInvM hd, ctr_after (n := 1) fun k hk => ?_⟩
  rw [show (BitVec.ofNat 64 1).setWidth 32 = BitVec.ofNat 32 1 by decide]
  refine (hf.bytes (R := ⟨s.gpr .x2, 16⟩) (by simp only [List.mem_singleton, forall_eq]; exact dCD)
    (show (16 : Nat) ≤ 2 ^ 64 by decide) hk).trans ?_
  show a.mem (s.gpr .x2 + BitVec.ofNat 64 k) = _
  rw [am, writeW_apply, off_toNat (s.gpr .x2) (by omega_using [hk]) (by decide)]
  by_cases h : k < 12
  · rw [ite_eq_right (show ¬ 12 ≤ k by omega_using [h]),
      ite_eq_right (show ¬ 2 ^ 64 + k - 12 < 32 / 8 by omega_using [h]), ite_eq_left h]
  · rw [ite_eq_left (show 12 ≤ k by omega_using [h]),
      ite_eq_left (show k - 12 < 32 / 8 by omega_using [h, hk]), ite_eq_right h, BitVec.setWidth_eq]

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

/-- `ctr32N`: nothing for no block, one block by the tables, any other
number of blocks bitsliced. -/
theorem ctr32N_wp {s₀ : State} (hp : Proof.Aes.ctr32AArch64.pre s₀) :
    WP isa ctr32N s₀ fun s' =>
      (∀ i < 10, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧ Proof.Aes.ctr32AArch64.post s₀ s' := by
  unfold ctr32N
  refine WP.ite (s₀.gpr .x4 == 0) (by simp [AArch64.eval, State.read])
    (fun hz => WP.block_nil ⟨fun _ _ => rfl, ctr32_none (toNat_of_beq_zero hz)⟩) (fun _ => ?_)
  let s₁ := s₀.write .x .x6 (s₀.read .x .x4 - BitVec.ofNat 64 1)
  refine WP.seq ?_
  rw [WP.block_cons_iff]
  refine ⟨s₁, exec_subImm_x (imm := 1) (by decide), WP.block_nil ?_⟩
  have hp₁ : Proof.Aes.ctr32AArch64.pre s₁ := hp
  have g₁ : ∀ r, r ≠ .x6 → s₁.gpr r = s₀.gpr r := fun r hr => by simp [s₁, State.write, hr]
  refine WP.ite (s₀.gpr .x4 - BitVec.ofNat 64 1 == 0)
    (by simp [AArch64.eval, State.read, s₁, State.write]) (fun hb => ?_) (fun _ => ?_)
  · have x4 : s₀.gpr .x4 = BitVec.ofNat 64 1 := by
      have h := BitVec.sub_add_cancel (s₀.gpr .x4) (BitVec.ofNat 64 1)
      rw [eq_of_beq hb] at h
      exact h.symm.trans (by decide)
    have h4 : (s₁.gpr .x4).toNat = 1 := by
      show (s₀.gpr .x4).toNat = 1
      rw [x4]; rfl
    refine WP.mono (ctr32One_ok hp₁ h4) fun s' ⟨hg, hpost⟩ => ⟨fun i hi => ?_, hpost⟩
    have hn := sreg_ne i hi
    rw [hg _ hn.1 hn.2.1 hn.2.2.1 hn.2.2.2]
    exact g₁ _ hn.2.2.1
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

theorem sreg_ne8 : ∀ i < 10, sreg i ≠ .x8 := by decide

/-- One block of the counter mode out of place: the counter block
encrypted, XORed with the block of the source into the destination, and
the counter block incremented. -/
theorem ctr32OneTo_ok {s : State} (hp : Proof.Aes.ctr32ToAArch64.pre s) (h4 : (s.gpr .x4).toNat = 1) :
    WP isa ctr32OneTo s fun s' =>
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → s'.gpr r = s.gpr r) ∧
      Proof.Aes.ctr32ToAArch64.post s s' := by
  obtain ⟨hrd, hwr, dSC, -, -, dCS, dCD, -, -, -, -, -, -, hR⟩ := hp
  rw [h4] at hrd hwr dCS dCD
  have hC : (⟨s.gpr .x2, 16⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  have hD : (⟨s.gpr .x6, 16 * 1⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  have hI : (⟨s.gpr .x3, 16 * 1⟩ : Region) ∈ s.rd := by rw [hrd]; simp
  have hS : (⟨s.gpr .x0, 240⟩ : Region) ∈ s.rd := by rw [hrd]; simp
  unfold ctr32OneTo
  let s₁ := s.write .x .x8 (s.gpr .x6)
  have g₁ : ∀ r, r ≠ .x8 → s₁.gpr r = s.gpr r := fun r hr => by simp [s₁, State.write, hr]
  have x8₁ : s₁.gpr .x8 = s.gpr .x6 := by simp [s₁, State.write]
  refine WP.seq ?_
  rw [List.singleton_append, WP.block_cons_iff]
  refine ⟨s₁, by simp [movR, exec, State.read, s₁], ?_⟩
  refine WP.mono (ctrOneLoad_ok s₁ hC) fun a ⟨av, am, ag, ard, awr, asp⟩ => ?_
  change a.v .v0 = s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 0) 128 at av
  change a.mem = s.mem.writeW (s.gpr .x2 + BitVec.ofNat 64 12)
    (rev32 (rev32 (s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 12) 32) + BitVec.ofNat 32 1)) at am
  have ag' : ∀ r, r ≠ .x6 → r ≠ .x8 → a.gpr r = s.gpr r := fun r h6 h8 => (ag r h6).trans (g₁ r h8)
  -- Only the counter block is written.
  have fa : Frame [⟨s.gpr .x2, 16⟩] s.mem a.mem := by
    rw [am]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (c_off (s.gpr .x2) (off := 12) (by omega_arith) (by omega_arith))
  have hw : bytesAt a.mem (s.gpr .x0) (16 * ((s.gpr .x1).toNat + 1)) =
      bytesAt s.mem (s.gpr .x0) (16 * ((s.gpr .x1).toNat + 1)) := by
    simp only [bytesAt]
    exact List.map_congr_left fun i hi => fa.bytes (R := ⟨s.gpr .x0, 240⟩)
      (by simp only [List.mem_singleton, forall_eq]; exact dSC) (show (240 : Nat) ≤ 2 ^ 64 by decide)
      (show i < 240 by have := List.mem_range.mp hi; omega_using [this, hR])
  have fI : ∀ i < 16 * 1, a.mem (s.gpr .x3 + BitVec.ofNat 64 i) = s.mem (s.gpr .x3 + BitVec.ofNat 64 i) :=
    fun i hi => fa.bytes (R := ⟨s.gpr .x3, 16 * 1⟩)
      (by simp only [List.mem_singleton, forall_eq]; exact dCS.symm) (show (16 * 1 : Nat) ≤ 2 ^ 64 by decide) hi
  have fD : ∀ i < 16 * 1, a.mem (s.gpr .x6 + BitVec.ofNat 64 i) = s.mem (s.gpr .x6 + BitVec.ofNat 64 i) :=
    fun i hi => fa.bytes (R := ⟨s.gpr .x6, 16 * 1⟩)
      (by simp only [List.mem_singleton, forall_eq]; exact dCD.symm) (show (16 * 1 : Nat) ≤ 2 ^ 64 by decide) hi
  -- The cipher.
  have a1 : a.gpr .x1 = BitVec.ofNat 64 (s.gpr .x1).toNat := by
    rw [ag' _ (by decide) (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono (Vperm.core_ok (s := a) (K := s.gpr .x0) (R := (s.gpr .x1).toNat)
    (by rw [ard]; exact hS) (ag' _ (by decide) (by decide)) a1 hR) fun b ⟨bst, bg, bm, brd, bwr, bsp⟩ => ?_)
  have b3 : b.gpr .x3 = s.gpr .x3 :=
    (bg _ (by decide) (by decide) (by decide)).trans (ag' _ (by decide) (by decide))
  have b8 : b.gpr .x8 = s.gpr .x6 :=
    (bg _ (by decide) (by decide) (by decide)).trans ((ag _ (by decide)).trans x8₁)
  have bwD : (⟨s.gpr .x6, 16 * 1⟩ : Region) ∈ b.wr := by rw [bwr, awr]; exact hD
  have brI : (⟨s.gpr .x3, 16 * 1⟩ : Region) ∈ b.rd := by rw [brd, ard]; exact hI
  have hinI : (⟨s.gpr .x3, 16 * 1⟩ : Region).Contains (b.gpr .x3 + BitVec.ofNat 64 0) 16 := by
    rw [b3]; exact Offset.contains_base (s.gpr .x3) (d := 0) (by decide) (by decide)
  have hinD : (⟨s.gpr .x6, 16 * 1⟩ : Region).Contains (b.gpr .x8 + BitVec.ofNat 64 0) 16 := by
    rw [b8]; exact Offset.contains_base (s.gpr .x6) (d := 0) (by decide) (by decide)
  -- The data.
  rw [WP.block_cons_iff]
  refine ⟨_, Aese.exec_ldrq (off := 0) (by decide) ⟨_, List.mem_append_left _ brI, hinI⟩, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, Aese.exec_strq (off := 0) (by decide) ⟨_, bwD, hinD⟩, WP.block_nil ?_⟩
  refine ⟨fun r h0 h1 h6 _ h8 => (bg r h0 h1 h6).trans (ag' r h6 h8), ?_⟩
  show Spec.Gcm.blocksAt (b.mem.write (b.gpr .x8 + BitVec.ofNat 64 0) 16
        (b.v .v0 ^^^ b.mem.readW (b.gpr .x3 + BitVec.ofNat 64 0) 128)) (s.gpr .x6) (s.gpr .x4).toNat = _ ∧
      Spec.Gcm.blockAt (b.mem.write (b.gpr .x8 + BitVec.ofNat 64 0) 16
        (b.v .v0 ^^^ b.mem.readW (b.gpr .x3 + BitVec.ofNat 64 0) 128)) (s.gpr .x2) = _
  rw [h4, b3, b8, bm]
  have hst := dataInvM_store1 (m₀ := s.mem) (m := a.mem) (D := s.gpr .x3) (O := s.gpr .x6) (n := 1) (k := 0)
    (ks := keyStream (s.gpr .x1).toNat (bytesAt s.mem (s.gpr .x0) (16 * ((s.gpr .x1).toNat + 1)))
      (Spec.Gcm.blockAt s.mem (s.gpr .x2)))
    (v := b.v .v0 ^^^ a.mem.readW (s.gpr .x3 + BitVec.ofNat 64 0) 128) (by decide) (by decide)
    (fun i hi => by rw [ite_eq_right (by omega_arith)]; exact fD i hi)
    (fun t ht => by
      rw [Nat.mul_zero, Nat.zero_add, keyStream, Nat.div_eq_of_lt ht, Nat.mod_eq_of_lt ht, vbyte_xor,
        vbyte_readW _ _ ht, BitVec.add_zero, fI t (by omega_using [ht]), ← getD_st _ ht, bst, hw, av,
        st_ctr])
  rw [Nat.mul_zero] at hst
  obtain ⟨hd, hf⟩ := hst
  refine ⟨ctr32_of_dataInvM hd, ctr_after (n := 1) fun k hk => ?_⟩
  rw [show (BitVec.ofNat 64 1).setWidth 32 = BitVec.ofNat 32 1 by decide]
  refine (hf.bytes (R := ⟨s.gpr .x2, 16⟩) (by simp only [List.mem_singleton, forall_eq]; exact dCD)
    (show (16 : Nat) ≤ 2 ^ 64 by decide) hk).trans ?_
  show a.mem (s.gpr .x2 + BitVec.ofNat 64 k) = _
  rw [am, writeW_apply, off_toNat (s.gpr .x2) (by omega_using [hk]) (by decide)]
  by_cases h : k < 12
  · rw [ite_eq_right (show ¬ 12 ≤ k by omega_using [h]),
      ite_eq_right (show ¬ 2 ^ 64 + k - 12 < 32 / 8 by omega_using [h]), ite_eq_left h]
  · rw [ite_eq_left (show 12 ≤ k by omega_using [h]),
      ite_eq_left (show k - 12 < 32 / 8 by omega_using [h, hk]), ite_eq_right h, BitVec.setWidth_eq]

/-- `ctr32ToN`: nothing for no block, one block by the tables, any other
number of blocks bitsliced. -/
theorem ctr32ToN_wp {s₀ : State} (hp : Proof.Aes.ctr32ToAArch64.pre s₀) :
    WP isa ctr32ToN s₀ fun s' =>
      (∀ i < 10, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧ s'.gpr .x30 = s₀.gpr .x30 ∧
        Proof.Aes.ctr32ToAArch64.post s₀ s' := by
  unfold ctr32ToN
  refine WP.ite (s₀.gpr .x4 == 0) (by simp [AArch64.eval, State.read])
    (fun hz => WP.block_nil ⟨fun _ _ => rfl, rfl, ctr32To_none (toNat_of_beq_zero hz)⟩) (fun _ => ?_)
  let s₁ := s₀.write .x .x7 (s₀.read .x .x4 - BitVec.ofNat 64 1)
  refine WP.seq ?_
  rw [WP.block_cons_iff]
  refine ⟨s₁, exec_subImm_x (imm := 1) (by decide), WP.block_nil ?_⟩
  have hp₁ : Proof.Aes.ctr32ToAArch64.pre s₁ := hp
  have g₁ : ∀ r, r ≠ .x7 → s₁.gpr r = s₀.gpr r := fun r hr => by simp [s₁, State.write, hr]
  refine WP.ite (s₀.gpr .x4 - BitVec.ofNat 64 1 == 0)
    (by simp [AArch64.eval, State.read, s₁, State.write]) (fun hb => ?_) (fun _ => ?_)
  · have x4 : s₀.gpr .x4 = BitVec.ofNat 64 1 := by
      have h := BitVec.sub_add_cancel (s₀.gpr .x4) (BitVec.ofNat 64 1)
      rw [eq_of_beq hb] at h
      exact h.symm.trans (by decide)
    have h4 : (s₁.gpr .x4).toNat = 1 := by
      show (s₀.gpr .x4).toNat = 1
      rw [x4]; rfl
    refine WP.mono (ctr32OneTo_ok hp₁ h4) fun s' ⟨hg, hpost⟩ => ⟨fun i hi => ?_, ?_, hpost⟩
    · have hn := sreg_ne i hi
      rw [hg _ hn.1 hn.2.1 hn.2.2.1 hn.2.2.2 (sreg_ne8 i hi)]
      exact g₁ _ hn.2.2.2
    · rw [hg _ (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact g₁ _ (by decide)
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

module

public import VerifiedGarbage.Impl.Aes.AArch64.Vperm
public import VerifiedGarbage.Proof.Aes.Vperm
public import VerifiedGarbage.Proof.Framework.AArch64.Tbl
public import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Aes.AArch64.Aese.Blocks
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: a change to the proofs of the entry points (`OneBlock.lean`) need not run the rounds' code again.

/-!
# AES on AArch64: one block by vector permutations

`Vperm.core` is FIPS 197's cipher on the state in `v0` (`core_ok`). The
state is held as the bytes `L x` (`Lv`), on which `invert` and `mix` compute
a round and `invert` and `last` the last round (`Proof/Aes/Vperm.lean`).
-/

@[expose] public section

namespace VG.Proof.Aes.AArch64.Vperm

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl VG.Impl.Tbl.AArch64
open VG.Impl.Aes.Vperm VG.Impl.Aes.AArch64.Vperm VG.Proof.Aes.Vperm
open VG.Proof.Aes.Vector (st KeyIs rnds rnds_zero rnds_succ cipher_eq eor_st aesmc_st keyIs_readW
  vbyte_mapBytes vbyte_shiftRows vbyte_mixColumns ext_vbyte st_ext getD_st getD_shiftRows getD_subBytes)
open VG.Spec.Aes (roundKey cipher addRoundKey bytesAt subBytes shiftRows mixColumns)

/-! ## The tables -/

/-- What `setup` leaves in the vector registers. -/
structure Consts (s : State) : Prop where
  v16 : s.v .v16 = mask
  v17 : s.v .v17 = inv
  v18 : s.v .v18 = inva
  v19 : s.v .v19 = sb1u
  v20 : s.v .v20 = sb1t
  v21 : s.v .v21 = sb2u
  v22 : s.v .v22 = sb2t
  v23 : s.v .v23 = sr
  v24 : s.v .v24 = rsr
  v25 : s.v .v25 = r3sr
  v26 : s.v .v26 = rot
  v27 : s.v .v27 = keyLo
  v28 : s.v .v28 = keyHi
  v29 : s.v .v29 = sbou
  v30 : s.v .v30 = sbot
  v31 : s.v .v31 = c63

/-- The registers the rounds write. -/
abbrev temps : List VReg := [.v0, .v1, .v2, .v3, .v4, .v5, .v6]

theorem Consts.of_v {s t : State} (h : Consts s) (hv : ∀ r, r ∉ temps → t.v r = s.v r) : Consts t :=
  ⟨(hv _ (by decide)).trans h.v16, (hv _ (by decide)).trans h.v17, (hv _ (by decide)).trans h.v18,
    (hv _ (by decide)).trans h.v19, (hv _ (by decide)).trans h.v20, (hv _ (by decide)).trans h.v21,
    (hv _ (by decide)).trans h.v22, (hv _ (by decide)).trans h.v23, (hv _ (by decide)).trans h.v24,
    (hv _ (by decide)).trans h.v25, (hv _ (by decide)).trans h.v26, (hv _ (by decide)).trans h.v27,
    (hv _ (by decide)).trans h.v28, (hv _ (by decide)).trans h.v29, (hv _ (by decide)).trans h.v30,
    (hv _ (by decide)).trans h.v31⟩

/-- A vector is its two doublewords. -/
theorem halves_append (x : BitVec 128) : x.extractLsb' 64 64 ++ x.extractLsb' 0 64 = x :=
  ofVDwords_halves x

theorem tabWords_length : tabWords.length = 32 := by simp [tabWords]

/-- The two words of vector `j` of the static, as `ldrqTbl` loads them. -/
theorem tabWords_pair {j : Nat} (hj : j < 16) :
    tabWords.getD (16 * j / 8 + 1) 0 ++ tabWords.getD (16 * j / 8) 0 = tabVec j := by
  obtain g : ∀ i < 32, tabWords.getD i 0 = (tabVec (i / 2)).extractLsb' (64 * (i % 2)) 64 := fun i hi => by
    simp [tabWords, hi]
  rw [show 16 * j / 8 = 2 * j by omega_arith, g _ (by omega_arith), g _ (by omega_arith),
    show (2 * j + 1) / 2 = j by omega_arith, show (2 * j + 1) % 2 = 1 by omega_arith,
    show 2 * j / 2 = j by omega_arith, show 2 * j % 2 = 0 by omega_arith]
  exact halves_append _

/-- Loading vector `j` of the static, whose address is in `x6`. -/
theorem exec_tld {j : Nat} (hj : j < 16) {s : State} (hx : s.gpr .x6 = s.syms tabName) :
    exec (tld j) s = some (s.setV (treg j) (tabVec j)) := by
  obtain hc : s.gpr .x6 = s.syms tabName ∧ 16 * j % 16 = 0 ∧ 16 * j < 65536 ∧
      16 * j / 8 + 2 ≤ tabWords.length :=
    ⟨hx, by omega_arith, by omega_arith, by rw [tabWords_length]; omega_arith⟩
  simp only [tld, exec, ite_eq_left_of_eq_true _ _ (eq_true hc), tabWords_pair hj]

/-- What a load of a static changes. -/
structure Loaded (s t : State) : Prop where
  gpr : t.gpr = s.gpr
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  syms : t.syms = s.syms

theorem Loaded.refl (s : State) : Loaded s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Loaded.trans {a b c : State} (h₁ : Loaded a b) (h₂ : Loaded b c) : Loaded a c :=
  ⟨h₂.gpr.trans h₁.gpr, h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp,
    h₂.syms.trans h₁.syms⟩

theorem Loaded.setV (s : State) (r : VReg) (x : BitVec 128) : Loaded s (s.setV r x) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The tables from the static into the table registers. -/
theorem tldTable_ok {s : State} (hx : s.gpr .x6 = s.syms tabName) :
    WP isa (.block ((List.range 16).map tld)) s fun t =>
      (∀ r < 16, t.v (treg r) = tabVec r) ∧ (∀ w, (∀ r < 16, w ≠ treg r) → t.v w = s.v w) ∧ Loaded s t := by
  suffices h : ∀ n ≤ 16, WP isa (.block ((List.range n).map tld)) s fun t =>
      (∀ r < n, t.v (treg r) = tabVec r) ∧ (∀ w, (∀ r < n, w ≠ treg r) → t.v w = s.v w) ∧ Loaded s t from
    h 16 (Nat.le_refl _)
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨fun _ h => absurd h (by omega_arith), fun _ _ => rfl, Loaded.refl s⟩
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (ih (by omega_arith)) fun a ⟨arow, av, al⟩ => ?_
    rw [WP.block_cons_iff]
    refine ⟨_, exec_tld (j := n) (by omega_arith) (by rw [al.gpr, al.syms]; exact hx),
      WP.block_nil ⟨fun r hr => ?_, fun w hw => ?_, al.trans (Loaded.setV _ _ _)⟩⟩
    · by_cases he : r = n
      · subst he; exact v_setV_self _ _ _
      · rw [v_setV_of_ne _ _ (fun e => he (treg_inj r (by omega_arith) n (by omega_arith) e)),
          arow r (by omega_arith)]
    · rw [v_setV_of_ne _ _ (hw n (by omega_arith)), av w (fun r hr => hw r (by omega_arith))]

theorem treg_notTemp : ∀ r < 16, treg r ∉ temps := by decide

/-- `setup`: the tables, from the static, through `x6`. -/
theorem setup_ok (s : State) :
    WP isa (.block setup) s fun t => Consts t ∧ t.v .v0 = s.v .v0 ∧
      (∀ g, g ≠ .x6 → t.gpr g = s.gpr g) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  unfold setup
  let a := s.write .x .x6 (s.syms tabName)
  obtain ax : a.gpr .x6 = a.syms tabName := gpr_write_self _ _ _ _
  rw [List.singleton_append, WP.block_cons_iff]
  refine ⟨a, exec_adrSym, ?_⟩
  refine WP.mono (tldTable_ok ax) fun t ⟨trow, tv, tl⟩ => ?_
  refine ⟨⟨trow 0 (by decide), trow 1 (by decide), trow 2 (by decide), trow 3 (by decide),
    trow 4 (by decide), trow 5 (by decide), trow 6 (by decide), trow 7 (by decide), trow 8 (by decide),
    trow 9 (by decide), trow 10 (by decide), trow 11 (by decide), trow 12 (by decide),
    trow 13 (by decide), trow 14 (by decide), trow 15 (by decide)⟩, ?_, fun g h6 => ?_, tl.mem, tl.rd,
    tl.wr, tl.sp⟩
  · rw [tv _ (fun r hr e => treg_notTemp r hr (e ▸ by decide))]
    rfl
  · rw [tl.gpr]; exact gpr_write_of_ne _ _ _ h6

/-! ## The code of a round -/

/-- `keyx`, on the block (`v0`, through `v1`) or a round key (`v5`, through
`v6`). -/
theorem keyx_run (s : State) (hc : Consts s) {d t : VReg}
    (hd : (d = .v0 ∧ t = .v1) ∨ (d = .v5 ∧ t = .v6)) :
    ∃ u, runBlock isa (keyx d t) s = some u ∧ u.v d = LcV (s.v d) ∧ VOnly [d, t] s u := by
  let a := s.setV t (s.v d &&& s.v .v16)
  let b := a.setV d (ushr4 (a.v d))
  let c := b.setV t (tblV (b.v .v27) (b.v t))
  let e := c.setV d (tblV (c.v .v28) (c.v d))
  let u := e.setV d (e.v d ^^^ e.v t)
  obtain o : VOnly [d, t] s u :=
    ((((VOnly.setV s (by simp) _).trans (VOnly.setV a (by simp) _)).trans (VOnly.setV b (by simp) _)).trans
      (VOnly.setV c (by simp) _)).trans (VOnly.setV e (by simp) _)
  refine ⟨u, ?_, ?_, o⟩
  · rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  · rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [u, e, c, b, a, v_setV, reduceCtorEq, ite_true, ite_false, hc.v16, hc.v27, hc.v28, LcV]

/-- `invert`: `io` and `jo` of the state's bytes. -/
theorem invert_run (s : State) (h16 : s.v .v16 = mask) (h17 : s.v .v17 = inv) (h18 : s.v .v18 = inva) :
    ∃ t, runBlock isa invert s = some t ∧ t.v .v2 = ioV (s.v .v0) ∧ t.v .v3 = joV (s.v .v0) ∧
      VOnly [.v0, .v1, .v2, .v3, .v4] s t := by
  let a := s.setV .v1 (s.v .v0 &&& s.v .v16)
  let b := a.setV .v0 (ushr4 (a.v .v0))
  let c := b.setV .v2 (tblV (b.v .v18) (b.v .v1))
  let d := c.setV .v1 (c.v .v1 ^^^ c.v .v0)
  let e := d.setV .v3 (tblV (d.v .v17) (d.v .v0))
  let f := e.setV .v4 (tblV (e.v .v17) (e.v .v1))
  let g := f.setV .v3 (f.v .v3 ^^^ f.v .v2)
  let h := g.setV .v4 (g.v .v4 ^^^ g.v .v2)
  let i := h.setV .v2 (tblV (h.v .v17) (h.v .v3))
  let j := i.setV .v3 (tblV (i.v .v17) (i.v .v4))
  let k := j.setV .v2 (j.v .v2 ^^^ j.v .v1)
  let t := k.setV .v3 (k.v .v3 ^^^ k.v .v0)
  refine ⟨t, rfl, ?_, ?_, ?_⟩
  · simp only [t, k, j, i, h, g, f, e, d, c, b, a, v_setV, reduceCtorEq, ite_true, ite_false, h16,
      h17, h18, ioV]
  · simp only [t, k, j, i, h, g, f, e, d, c, b, a, v_setV, reduceCtorEq, ite_true, ite_false, h16,
      h17, h18, joV]
  · exact (((((((((((VOnly.setV s (by simp) _).trans (VOnly.setV a (by simp) _)).trans
      (VOnly.setV b (by simp) _)).trans (VOnly.setV c (by simp) _)).trans (VOnly.setV d (by simp) _)).trans
      (VOnly.setV e (by simp) _)).trans (VOnly.setV f (by simp) _)).trans (VOnly.setV g (by simp) _)).trans
      (VOnly.setV h (by simp) _)).trans (VOnly.setV i (by simp) _)).trans (VOnly.setV j (by simp) _)).trans
      (VOnly.setV k (by simp) _)

/-- `mix`, on `io` and `jo` in `v2` and `v3` and the round key in `v5`. -/
theorem mix_run (s : State) (hc : Consts s) :
    ∃ t, runBlock isa mix s = some t ∧ t.v .v0 = mixV (s.v .v2) (s.v .v3) (s.v .v5) ∧
      VOnly [.v0, .v1, .v2, .v3] s t := by
  let a := s.setV .v0 (tblV (s.v .v19) (s.v .v2))
  let b := a.setV .v1 (tblV (a.v .v20) (a.v .v3))
  let c := b.setV .v2 (tblV (b.v .v21) (b.v .v2))
  let d := c.setV .v3 (tblV (c.v .v22) (c.v .v3))
  let e := d.setV .v0 (d.v .v0 ^^^ d.v .v1)
  let f := e.setV .v2 (e.v .v2 ^^^ e.v .v3)
  let g := f.setV .v1 (tblV (f.v .v2) (f.v .v23))
  let h := g.setV .v3 (tblV (g.v .v0) (g.v .v24))
  let i := h.setV .v0 (tblV (h.v .v0) (h.v .v25))
  let j := i.setV .v1 (i.v .v1 ^^^ i.v .v3)
  let k := j.setV .v0 (j.v .v0 ^^^ j.v .v5)
  let l := k.setV .v3 (tblV (k.v .v1) (k.v .v26))
  let m := l.setV .v0 (l.v .v0 ^^^ l.v .v1)
  let t := m.setV .v0 (m.v .v0 ^^^ m.v .v3)
  refine ⟨t, rfl, ?_, ?_⟩
  · simp only [t, m, l, k, j, i, h, g, f, e, d, c, b, a, v_setV, reduceCtorEq, ite_true, ite_false,
      hc.v19, hc.v20, hc.v21, hc.v22, hc.v23, hc.v24, hc.v25, hc.v26, mixV, mixX, sA, sA2]
  · exact (((((((((((((VOnly.setV s (by simp) _).trans (VOnly.setV a (by simp) _)).trans
      (VOnly.setV b (by simp) _)).trans (VOnly.setV c (by simp) _)).trans (VOnly.setV d (by simp) _)).trans
      (VOnly.setV e (by simp) _)).trans (VOnly.setV f (by simp) _)).trans (VOnly.setV g (by simp) _)).trans
      (VOnly.setV h (by simp) _)).trans (VOnly.setV i (by simp) _)).trans (VOnly.setV j (by simp) _)).trans
      (VOnly.setV k (by simp) _)).trans (VOnly.setV l (by simp) _)).trans (VOnly.setV m (by simp) _)

/-- `last`, on `io` and `jo` in `v2` and `v3` and the round key in `v5`. -/
theorem last_run (s : State) (hc : Consts s) :
    ∃ t, runBlock isa last s = some t ∧ t.v .v0 = lastV (s.v .v2) (s.v .v3) (s.v .v5) ∧
      VOnly [.v0, .v1, .v5] s t := by
  let a := s.setV .v0 (tblV (s.v .v29) (s.v .v2))
  let b := a.setV .v1 (tblV (a.v .v30) (a.v .v3))
  let c := b.setV .v0 (b.v .v0 ^^^ b.v .v1)
  let d := c.setV .v0 (tblV (c.v .v0) (c.v .v23))
  let e := d.setV .v5 (d.v .v5 ^^^ d.v .v31)
  let t := e.setV .v0 (e.v .v0 ^^^ e.v .v5)
  refine ⟨t, rfl, ?_, ?_⟩
  · simp only [t, e, d, c, b, a, v_setV, reduceCtorEq, ite_true, ite_false, hc.v23, hc.v29, hc.v30,
      hc.v31, lastV]
  · exact (((((VOnly.setV s (by simp) _).trans (VOnly.setV a (by simp) _)).trans
      (VOnly.setV b (by simp) _)).trans (VOnly.setV c (by simp) _)).trans (VOnly.setV d (by simp) _)).trans
      (VOnly.setV e (by simp) _)

/-! ## The rounds -/

theorem VOnly.sp {ds : List VReg} {s s' : State} (h : VOnly ds s s') : s'.sp = s.sp := by
  rw [h.1]

theorem vonly_mono {ds es : List VReg} {s s' : State} (h : VOnly ds s s') (hs : ∀ r ∈ ds, r ∈ es) :
    VOnly es s s' :=
  ⟨h.1, fun r hr => h.2 r fun hd => hr (hs r hd)⟩

theorem read_x (s : State) (r : Reg) : s.read .x r = s.gpr r := by
  simp [State.read, Size.bits]

theorem ofNat_bne_zero {k : Nat} (h0 : 0 < k) (hk : k < 2 ^ 64) : (BitVec.ofNat 64 k != 0) = true := by
  rw [bne_iff_ne]
  intro h
  obtain h' := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at h'
  have h'' : k = 0 := h'
  omega_using [h0, h'']

theorem ofNat_sub_one {k : Nat} (h : 1 ≤ k) :
    BitVec.ofNat 64 k - BitVec.ofNat 64 1 = BitVec.ofNat 64 (k - 1) :=
  BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) h

/-- A round key from the schedule, into `v5`. -/
theorem key_run (s : State) {off : Nat} (ho : off % 16 = 0 ∧ off < 65536)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 off) 16) :
    ∃ t, runBlock isa [.ldrq .v5 .x0 off] s = some t ∧
      t.v .v5 = s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 off) 128 ∧ VOnly [.v5] s t :=
  ⟨s.setV .v5 (s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 off) 128),
    by rw [runBlock_cons, Aese.exec_ldrq ho hin, runStep_some, runBlock_nil], v_setV_self _ _ _,
    VOnly.setV s (by simp) _⟩

/-- After `j` full rounds from the state `x`, with the key schedule at `K`:
the state `X` as `Lv X` in `v0`, `x0` at round key `j`, and `R − 1 − j` in
`x1`. -/
structure RInv (s₀ : State) (K : Addr) (R : Nat) (w : List Byte) (x : Spec.Aes.State) (j : Nat)
    (s : State) : Prop where
  consts : Consts s
  x0 : s.gpr .x0 = K + BitVec.ofNat 64 (16 * j)
  x1 : s.gpr .x1 = BitVec.ofNat 64 (R - 1 - j)
  st : ∃ X, s.v .v0 = Lv X ∧ st X = rnds w x j
  gpr : ∀ r, r ≠ .x0 → r ≠ .x1 → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

/-- A full round. -/
theorem round_ok {s₀ : State} {K : Addr} {R : Nat} {x : Spec.Aes.State} (hK : (⟨K, 240⟩ : Region) ∈ s₀.rd)
    (hR : R ≤ 14) {j : Nat} (hj : j + 2 ≤ R) {s : State}
    (hI : RInv s₀ K R (bytesAt s₀.mem K (16 * (R + 1))) x j s) :
    WP isa (.block round) s (RInv s₀ K R (bytesAt s₀.mem K (16 * (R + 1))) x (j + 1)) := by
  obtain ⟨X, hX, hst⟩ := hI.st
  unfold round
  rw [show ([.addImm .x .x0 .x0 16, .ldrq .v5 .x0 0] : List Instr) =
    [.addImm .x .x0 .x0 16] ++ [.ldrq .v5 .x0 0] from rfl, List.append_assoc, List.append_assoc,
    List.append_assoc, List.append_assoc, WP.block_append_iff]
  let a := s.write .x .x0 (s.read .x .x0 + BitVec.ofNat 64 16)
  rw [WP.block_cons_iff]
  refine ⟨a, exec_addImm_x (imm := 16) (by decide), WP.block_nil ?_⟩
  obtain a0 : a.gpr .x0 = K + BitVec.ofNat 64 (16 * (j + 1)) := by
    rw [show a.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 16 by simp [a, State.write, read_x], hI.x0,
      BitVec.add_assoc, ← BitVec.ofNat_add]
    rfl
  have ard : a.rd = s₀.rd := hI.rd
  have amem : a.mem = s₀.mem := hI.mem
  obtain ac : Consts a := hI.consts.of_v fun _ _ => rfl
  rw [WP.block_append_iff]
  obtain ⟨b, hb, b5, ob⟩ := key_run a (off := 0) (by decide) ⟨_, List.mem_append_left _ (by rw [ard]; exact hK),
    by rw [a0, BitVec.add_zero]; exact Offset.contains_base K (by omega_arith) (by omega_arith)⟩
  refine WP.of_runBlock ⟨b, hb, ?_⟩
  obtain ob' : VOnly temps a b := vonly_mono ob (by decide)
  obtain bc : Consts b := ac.of_v ob'.2
  rw [WP.block_append_iff]
  obtain ⟨c, hc, c5, oc⟩ := keyx_run b bc (.inr ⟨rfl, rfl⟩)
  refine WP.of_runBlock ⟨c, hc, ?_⟩
  obtain oc' : VOnly temps b c := vonly_mono oc (by decide)
  obtain cc : Consts c := bc.of_v oc'.2
  rw [WP.block_append_iff]
  obtain ⟨d, hd, d2, d3, od⟩ := invert_run c cc.v16 cc.v17 cc.v18
  refine WP.of_runBlock ⟨d, hd, ?_⟩
  obtain od' : VOnly temps c d := vonly_mono od (by decide)
  obtain dc : Consts d := cc.of_v od'.2
  rw [WP.block_append_iff]
  obtain ⟨e, he, e0, oe⟩ := mix_run d dc
  refine WP.of_runBlock ⟨e, he, ?_⟩
  obtain oe' : VOnly temps d e := vonly_mono oe (by decide)
  obtain o : VOnly temps a e := ((ob'.trans oc').trans od').trans oe'
  let f := e.write .x .x1 (e.read .x .x1 - BitVec.ofNat 64 1)
  rw [WP.block_cons_iff]
  refine ⟨f, exec_subImm_x (imm := 1) (by decide), WP.block_nil ?_⟩
  obtain hk : KeyIs (a.mem.readW (a.gpr .x0 + BitVec.ofNat 64 0) 128)
      (roundKey (bytesAt s₀.mem K (16 * (R + 1))) (j + 1)) := by
    rw [a0, BitVec.add_zero, amem]
    exact keyIs_readW s₀.mem K (by omega_arith)
  obtain c0 : c.v .v0 = Lv X := by
    rw [oc.2 _ (by decide), ob.2 _ (by decide)]
    exact hX
  obtain d5 : d.v .v5 = LcV (a.mem.readW (a.gpr .x0 + BitVec.ofNat 64 0) 128) := by
    rw [od.2 _ (by decide), c5, b5]
  obtain ex1 : e.gpr .x1 = BitVec.ofNat 64 (R - 1 - j) := by
    rw [o.gpr, show a.gpr .x1 = s.gpr .x1 by simp [a, State.write]]; exact hI.x1
  refine ⟨dc.of_v oe'.2, ?_, ?_,
    ⟨aesMixColumns (aesMapBytes aesSbox (aesShiftRows X)) ^^^
      a.mem.readW (a.gpr .x0 + BitVec.ofNat 64 0) 128, ?_, ?_⟩, fun r h0 h1 => ?_, o.mem.trans amem, o.rd.trans ard,
    o.wr.trans hI.wr, (VOnly.sp o).trans hI.sp⟩
  · rw [show f.gpr .x0 = e.gpr .x0 by simp [f, State.write], o.gpr]; exact a0
  · rw [show f.gpr .x1 = e.gpr .x1 - BitVec.ofNat 64 1 by simp [f, State.write, read_x], ex1,
      ofNat_sub_one (by omega_arith), Nat.sub_sub]
  · rw [show f.v .v0 = e.v .v0 from rfl, e0, d2, d3, d5, c0]
    exact mixV_eq _ _
  · rw [eor_st hk, aesmc_st, shiftSub_st, hst, rnds_succ]
  · rw [show f.gpr r = e.gpr r by simp [f, State.write, h1], o.gpr,
      show a.gpr r = s.gpr r by simp [a, State.write, h0]]
    exact hI.gpr r h0 h1

/-- The full rounds: `R − 1` of them. -/
theorem loop_ok {s₀ : State} {K : Addr} {R : Nat} {x : Spec.Aes.State} (hK : (⟨K, 240⟩ : Region) ∈ s₀.rd)
    (hR : R ≤ 14) (hR2 : 2 ≤ R) {s : State} (hI : RInv s₀ K R (bytesAt s₀.mem K (16 * (R + 1))) x 0 s) :
    WP isa (.loop (.block round) (.nonzero .x .x1)) s
      (RInv s₀ K R (bytesAt s₀.mem K (16 * (R + 1))) x (R - 1)) := by
  refine WP.loop (M := isa) (fun n t => ∃ j, n = R - 1 - j ∧ j + 2 ≤ R ∧
    RInv s₀ K R (bytesAt s₀.mem K (16 * (R + 1))) x j t) ?_ (R - 1) s ⟨0, rfl, hR2, hI⟩
  rintro n t ⟨j, hn, hj, hI⟩
  refine WP.mono (round_ok hK hR hj hI) fun t' hI' => ?_
  obtain he : isa.eval (.nonzero .x .x1) t' = some (BitVec.ofNat 64 (R - 1 - (j + 1)) != 0) := by
    simp [AArch64.eval, State.read, hI'.x1]
  rcases Nat.lt_or_ge (j + 2) R with h | h
  · exact .inr ⟨by rw [he, ofNat_bne_zero (by omega_arith) (by omega_arith)], R - 1 - (j + 1), by omega_arith,
      j + 1, rfl, h, hI'⟩
  · have e : j + 1 = R - 1 := by omega_arith
    refine .inl ⟨by rw [he, show R - 1 - (j + 1) = 0 by omega_arith]; rfl, ?_⟩
    rw [← e]; exact hI'

/-- The last round. -/
theorem last_ok {s₀ : State} {K : Addr} {R : Nat} {x : Spec.Aes.State} (hK : (⟨K, 240⟩ : Region) ∈ s₀.rd)
    (hR : R ≤ 14) (hR2 : 2 ≤ R) {s : State}
    (hI : RInv s₀ K R (bytesAt s₀.mem K (16 * (R + 1))) x (R - 1) s) :
    WP isa (.block (([.ldrq .v5 .x0 16] : List Instr) ++ invert ++ last)) s fun t =>
      st (t.v .v0) = cipher R (bytesAt s₀.mem K (16 * (R + 1))) x ∧
      (∀ r, r ≠ .x0 → r ≠ .x1 → t.gpr r = s₀.gpr r) ∧ t.mem = s₀.mem ∧ t.rd = s₀.rd ∧ t.wr = s₀.wr ∧
      t.sp = s₀.sp := by
  obtain ⟨X, hX, hst⟩ := hI.st
  rw [List.append_assoc, WP.block_append_iff]
  obtain ea : s.gpr .x0 + BitVec.ofNat 64 16 = K + BitVec.ofNat 64 (16 * R) := by
    rw [hI.x0, BitVec.add_assoc, ← BitVec.ofNat_add, show 16 * (R - 1) + 16 = 16 * R by omega_arith]
  obtain ⟨b, hb, b5, ob⟩ := key_run s (off := 16) (by decide)
    ⟨_, List.mem_append_left _ (by rw [hI.rd]; exact hK),
      by rw [ea]; exact Offset.contains_base K (by omega_arith) (by omega_arith)⟩
  refine WP.of_runBlock ⟨b, hb, ?_⟩
  obtain ob' : VOnly temps s b := vonly_mono ob (by decide)
  obtain bc : Consts b := hI.consts.of_v ob'.2
  rw [WP.block_append_iff]
  obtain ⟨d, hd, d2, d3, od⟩ := invert_run b bc.v16 bc.v17 bc.v18
  refine WP.of_runBlock ⟨d, hd, ?_⟩
  obtain od' : VOnly temps b d := vonly_mono od (by decide)
  obtain dc : Consts d := bc.of_v od'.2
  obtain ⟨t, ht, t0, ot⟩ := last_run d dc
  obtain ot' : VOnly temps d t := vonly_mono ot (by decide)
  obtain o : VOnly temps s t := (ob'.trans od').trans ot'
  refine WP.of_runBlock ⟨t, ht, ?_, fun r h0 h1 => ?_, o.mem.trans hI.mem, o.rd.trans hI.rd,
    o.wr.trans hI.wr, (VOnly.sp o).trans hI.sp⟩
  · have hk : KeyIs (s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 16) 128)
        (roundKey (bytesAt s₀.mem K (16 * (R + 1))) R) := by
      rw [ea, hI.mem]
      exact keyIs_readW s₀.mem K (by omega_arith)
    rw [t0, d2, d3, od.2 _ (by decide), b5, show b.v .v0 = s.v .v0 from ob.2 _ (by decide), hX, lastV_eq,
      eor_st hk, shiftSub_st, hst]
    rfl
  · rw [o.gpr]; exact hI.gpr r h0 h1

/-- `first`: the block and the first round key. -/
theorem first_ok {s : State} {K : Addr} {R : Nat} (hc : Consts s) (hK : (⟨K, 240⟩ : Region) ∈ s.rd)
    (h0 : s.gpr .x0 = K) (h1 : s.gpr .x1 = BitVec.ofNat 64 R) (hR : 2 ≤ R ∧ R ≤ 14) :
    WP isa (.block first) s (RInv s K R (bytesAt s.mem K (16 * (R + 1))) (st (s.v .v0)) 0) := by
  unfold first
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  obtain ⟨a, ha, a5, oa⟩ := key_run s (off := 0) (by decide) ⟨_, List.mem_append_left _ hK,
    by rw [h0]; exact Offset.contains_base K (by decide) (by decide)⟩
  refine WP.of_runBlock ⟨a, ha, ?_⟩
  obtain oa' : VOnly temps s a := vonly_mono oa (by decide)
  obtain ac : Consts a := hc.of_v oa'.2
  rw [WP.block_append_iff]
  obtain ⟨b, hb, b0, ob⟩ := keyx_run a ac (.inl ⟨rfl, rfl⟩)
  refine WP.of_runBlock ⟨b, hb, ?_⟩
  obtain ob' : VOnly temps a b := vonly_mono ob (by decide)
  obtain bc : Consts b := ac.of_v ob'.2
  rw [WP.block_append_iff]
  obtain ⟨c, hc', c5, oc⟩ := keyx_run b bc (.inr ⟨rfl, rfl⟩)
  refine WP.of_runBlock ⟨c, hc', ?_⟩
  obtain oc' : VOnly temps b c := vonly_mono oc (by decide)
  obtain o : VOnly temps s c := (oa'.trans ob').trans oc'
  let d := c.setV .v0 (c.v .v0 ^^^ c.v .v5)
  let f := d.write .x .x1 (d.read .x .x1 - BitVec.ofNat 64 1)
  rw [WP.block_cons_iff]
  refine ⟨d, exec_eorv _ _ _ _, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨f, exec_subImm_x (imm := 1) (by decide), WP.block_nil ?_⟩
  obtain hk : KeyIs (s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 0) 128)
      (roundKey (bytesAt s.mem K (16 * (R + 1))) 0) := by
    obtain h := keyIs_readW s.mem K (L := 16 * (R + 1)) (j := 0) (by omega_arith)
    rw [Nat.mul_zero] at h
    rw [h0]
    exact h
  have dg : d.gpr = s.gpr := o.gpr
  refine ⟨(bc.of_v oc'.2).of_v fun r hr => v_setV_of_ne _ _ (fun e => hr (e ▸ by decide)), ?_, ?_,
    ⟨s.v .v0 ^^^ s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 0) 128, ?_, ?_⟩, fun r _ h1 => ?_, o.mem, o.rd,
    o.wr, (VOnly.sp o :)⟩
  · rw [show f.gpr .x0 = d.gpr .x0 by simp [f, State.write], dg, h0]
    exact (BitVec.add_zero K).symm
  · rw [show f.gpr .x1 = d.gpr .x1 - BitVec.ofNat 64 1 by simp [f, State.write, read_x], dg, h1,
      ofNat_sub_one (by omega_arith)]
    rfl
  · rw [show f.v .v0 = d.v .v0 from rfl, show d.v .v0 = c.v .v0 ^^^ c.v .v5 from v_setV_self _ _ _, c5, oc.2 _ (by decide), b0,
      show b.v .v5 = a.v .v5 from ob.2 _ (by decide), a5, show a.v .v0 = s.v .v0 from oa.2 _ (by decide)]
    exact first_eq _ _
  · rw [eor_st hk, rnds_zero]
  · rw [show f.gpr r = d.gpr r by simp [f, State.write, h1], dg]

/-- `core` is the cipher, on the state in `v0`, with the schedule at `x0`
and the rounds in `x1`. -/
theorem core_ok {s : State} {K : Addr} {R : Nat} (hK : (⟨K, 240⟩ : Region) ∈ s.rd) (h0 : s.gpr .x0 = K)
    (h1 : s.gpr .x1 = BitVec.ofNat 64 R) (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    WP isa core s fun t =>
      st (t.v .v0) = cipher R (bytesAt s.mem K (16 * (R + 1))) (st (s.v .v0)) ∧
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x6 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.sp = s.sp := by
  obtain hR14 : R ≤ 14 := by omega_arith
  obtain hR2 : 2 ≤ R := by omega_arith
  unfold core
  refine WP.seq (WP.mono (setup_ok s) fun a ⟨ac, a0, ag, am, ard, awr, asp⟩ => ?_)
  obtain hKa : (⟨K, 240⟩ : Region) ∈ a.rd := by rw [ard]; exact hK
  unfold rounds
  refine WP.seq (WP.mono (first_ok ac hKa ((ag _ (by decide)).trans h0) ((ag _ (by decide)).trans h1)
    ⟨hR2, hR14⟩) fun c hI => ?_)
  refine WP.seq (WP.mono (loop_ok hKa hR14 hR2 hI) fun d hd => ?_)
  refine WP.mono (last_ok hKa hR14 hR2 hd) fun t ⟨tst, tg, tm, trd, twr, tsp⟩ => ?_
  refine ⟨by rw [tst, am, a0], fun r h0 h1 h6 => (tg r h0 h1).trans (ag r h6), tm.trans am,
    trd.trans ard, twr.trans awr, tsp.trans asp⟩

/-! ## Decryption -/

namespace Dec

open VG.Proof.Aes.Vperm.Dec
open VG.Impl.Aes.AArch64.Vperm.Dec (keyTerm keyRot key)
open VG.Impl.Aes.Vperm.Dec (x0u x0t x1u x1t x2u x2t x3u x3t p0 p1 p2 p3 y0l y0h y1l y1h y2l y2h
  y3l y3h rot2 rot3 dl dh dbou dbot)
open VG.Proof.Aes.Vector (vbyte_invShiftRows vbyte_invMixColumns st_aesimc st_invSub)

/-! ## Decryption: the tables -/

/-- What `Dec.setup` leaves in the vector registers, and in `x6`. -/
structure Consts (s : State) : Prop where
  x6 : s.gpr .x6 = s.syms Dec.tabName
  v16 : s.v .v16 = mask
  v17 : s.v .v17 = inv
  v18 : s.v .v18 = inva
  v19 : s.v .v19 = x0u
  v20 : s.v .v20 = x0t
  v21 : s.v .v21 = x1u
  v22 : s.v .v22 = x1t
  v23 : s.v .v23 = x2u
  v24 : s.v .v24 = x2t
  v25 : s.v .v25 = x3u
  v26 : s.v .v26 = x3t
  v27 : s.v .v27 = p0
  v28 : s.v .v28 = p1
  v29 : s.v .v29 = p2
  v30 : s.v .v30 = p3

/-- The registers the rounds write. -/
abbrev temps : List VReg := [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7]

theorem Consts.of_v {s t : State} (h : Consts s) (o : VOnly temps s t) : Consts t :=
  ⟨by rw [o.gpr, show t.syms = s.syms by rw [o.1]]; exact h.x6,
    (o.2 _ (by decide)).trans h.v16, (o.2 _ (by decide)).trans h.v17, (o.2 _ (by decide)).trans h.v18,
    (o.2 _ (by decide)).trans h.v19, (o.2 _ (by decide)).trans h.v20, (o.2 _ (by decide)).trans h.v21,
    (o.2 _ (by decide)).trans h.v22, (o.2 _ (by decide)).trans h.v23, (o.2 _ (by decide)).trans h.v24,
    (o.2 _ (by decide)).trans h.v25, (o.2 _ (by decide)).trans h.v26, (o.2 _ (by decide)).trans h.v27,
    (o.2 _ (by decide)).trans h.v28, (o.2 _ (by decide)).trans h.v29, (o.2 _ (by decide)).trans h.v30⟩

theorem tabWords_length : Dec.tabWords.length = 60 := by simp [Dec.tabWords]

/-- The two words of vector `j` of the static, as `ldrqTbl` loads them. -/
theorem tabWords_pair {j : Nat} (hj : j < 30) :
    Dec.tabWords.getD (16 * j / 8 + 1) 0 ++ Dec.tabWords.getD (16 * j / 8) 0 = Dec.tabVec j := by
  obtain g : ∀ i < 60, Dec.tabWords.getD i 0 = (Dec.tabVec (i / 2)).extractLsb' (64 * (i % 2)) 64 := fun i hi => by
    simp [Dec.tabWords, hi]
  rw [show 16 * j / 8 = 2 * j by omega_arith, g _ (by omega_arith), g _ (by omega_arith),
    show (2 * j + 1) / 2 = j by omega_arith, show (2 * j + 1) % 2 = 1 by omega_arith,
    show 2 * j / 2 = j by omega_arith, show 2 * j % 2 = 0 by omega_arith]
  exact halves_append _

/-- Loading vector `j` of the static, whose address is in `x6`. -/
theorem exec_tld (r : VReg) {j : Nat} (hj : j < 30) {s : State} (hx : s.gpr .x6 = s.syms Dec.tabName) :
    exec (Dec.tld r j) s = some (s.setV r (Dec.tabVec j)) := by
  obtain hc : s.gpr .x6 = s.syms Dec.tabName ∧ 16 * j % 16 = 0 ∧ 16 * j < 65536 ∧
      16 * j / 8 + 2 ≤ Dec.tabWords.length :=
    ⟨hx, by omega_arith, by omega_arith, by rw [tabWords_length]; omega_arith⟩
  simp only [Dec.tld, exec, ite_eq_left_of_eq_true _ _ (eq_true hc), tabWords_pair hj]

/-- The tables from the static into the table registers. -/
theorem tldTable_ok {s : State} (hx : s.gpr .x6 = s.syms Dec.tabName) :
    WP isa (.block ((List.range 15).map fun j => Dec.tld (treg j) j)) s fun t =>
      (∀ r < 15, t.v (treg r) = Dec.tabVec r) ∧ (∀ w, (∀ r < 15, w ≠ treg r) → t.v w = s.v w) ∧ Loaded s t := by
  suffices h : ∀ n ≤ 15, WP isa (.block ((List.range n).map fun j => Dec.tld (treg j) j)) s fun t =>
      (∀ r < n, t.v (treg r) = Dec.tabVec r) ∧ (∀ w, (∀ r < n, w ≠ treg r) → t.v w = s.v w) ∧ Loaded s t from
    h 15 (Nat.le_refl _)
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨fun _ h => absurd h (by omega_arith), fun _ _ => rfl, Loaded.refl s⟩
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (ih (by omega_arith)) fun a ⟨arow, av, al⟩ => ?_
    rw [WP.block_cons_iff]
    refine ⟨_, exec_tld (treg n) (j := n) (by omega_arith) (by rw [al.gpr, al.syms]; exact hx),
      WP.block_nil ⟨fun r hr => ?_, fun w hw => ?_, al.trans (Loaded.setV _ _ _)⟩⟩
    · by_cases he : r = n
      · subst he; exact v_setV_self _ _ _
      · rw [v_setV_of_ne _ _ (fun e => he (treg_inj r (by omega_arith) n (by omega_arith) e)),
          arow r (by omega_arith)]
    · rw [v_setV_of_ne _ _ (hw n (by omega_arith)), av w (fun r hr => hw r (by omega_arith))]

theorem shl4 : ∀ R : Nat, R = 10 ∨ R = 12 ∨ R = 14 → BitVec.ofNat 64 R <<< 4 = BitVec.ofNat 64 (16 * R) := by
  rintro R (rfl | rfl | rfl) <;> rfl

/-- `Dec.setup`: `x0` at the last round key, and the tables, from the static,
through `x6`. -/
theorem setup_ok {s : State} {K : Addr} {R : Nat} (h0 : s.gpr .x0 = K) (h1 : s.gpr .x1 = BitVec.ofNat 64 R)
    (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    WP isa (.block Dec.setup) s fun t => Consts t ∧ t.v .v0 = s.v .v0 ∧
      t.gpr .x0 = K + BitVec.ofNat 64 (16 * R) ∧ (∀ g, g ≠ .x0 → g ≠ .x6 → t.gpr g = s.gpr g) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  unfold Dec.setup
  let a := s.write .x .x6 (s.read .x .x1 <<< 4)
  let b := a.write .x .x0 (a.read .x .x0 + a.read .x .x6)
  let c := b.write .x .x6 (b.syms Dec.tabName)
  obtain cx : c.gpr .x6 = c.syms Dec.tabName := gpr_write_self _ _ _ _
  rw [show ([.lsl .x .x6 .x1 4, .add .x .x0 .x0 .x6, .adrSym .x6 Dec.tabName] : List Instr) ++
      ((List.range 15).map fun j => Dec.tld (treg j) j) =
    .lsl .x .x6 .x1 4 :: .add .x .x0 .x0 .x6 :: .adrSym .x6 Dec.tabName ::
      ((List.range 15).map fun j => Dec.tld (treg j) j) from rfl, WP.block_cons_iff]
  refine ⟨a, rfl, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨b, exec_add, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨c, exec_adrSym, ?_⟩
  obtain c0 : c.gpr .x0 = K + BitVec.ofNat 64 (16 * R) := by
    rw [show c.gpr .x0 = s.gpr .x0 + s.gpr .x1 <<< 4 by simp [c, b, a, State.write, read_x], h0, h1,
      shl4 R hR]
  refine WP.mono (tldTable_ok cx) fun t ⟨trow, tv, tl⟩ => ?_
  refine ⟨⟨by rw [tl.gpr, tl.syms]; exact cx, trow 0 (by decide), trow 1 (by decide), trow 2 (by decide),
    trow 3 (by decide), trow 4 (by decide), trow 5 (by decide), trow 6 (by decide), trow 7 (by decide),
    trow 8 (by decide), trow 9 (by decide), trow 10 (by decide), trow 11 (by decide), trow 12 (by decide),
    trow 13 (by decide), trow 14 (by decide)⟩, ?_, ?_, fun g g0 g6 => ?_, tl.mem, tl.rd, tl.wr, tl.sp⟩
  · rw [tv _ (fun r hr e => Vperm.treg_notTemp r (by omega_arith) (e ▸ by decide))]
    rfl
  · rw [tl.gpr]; exact c0
  · rw [tl.gpr]
    simp [c, b, a, State.write, g0, g6]

/-! ## Decryption: the code of a round -/

theorem tld_run (s : State) (r : VReg) {j : Nat} (hj : j < 30) (hx : s.gpr .x6 = s.syms Dec.tabName) :
    runBlock isa [Dec.tld r j] s = some (s.setV r (Dec.tabVec j)) := by
  rw [runBlock_cons, exec_tld r hj hx, runStep_some, runBlock_nil]

/-- `keyTerm`: vectors `jl` and `jh` of the static at the round key's low
and high four bits (`v6`, `v5`), XORed, into `v7` or `v1`. -/
theorem keyTerm_run (s : State) (hx : s.gpr .x6 = s.syms Dec.tabName) {d : VReg} (hd : d = .v7 ∨ d = .v1)
    {jl jh : Nat} (hl : jl < 30) (hh : jh < 30) :
    ∃ t, runBlock isa (keyTerm d jl jh) s = some t ∧
      t.v d = tblV (Dec.tabVec jl) (s.v .v6) ^^^ tblV (Dec.tabVec jh) (s.v .v5) ∧
      (d = .v1 → t.v .v7 = s.v .v7) ∧ VOnly [.v1, .v2, .v7] s t := by
  let a := s.setV .v1 (Dec.tabVec jl)
  let b := a.setV .v2 (Dec.tabVec jh)
  let c := b.setV .v1 (tblV (b.v .v1) (b.v .v6))
  let e := c.setV .v2 (tblV (c.v .v2) (c.v .v5))
  let t := e.setV d (e.v .v1 ^^^ e.v .v2)
  obtain hab : runBlock isa [Dec.tld .v1 jl, Dec.tld .v2 jh] s = some b :=
    runBlock_cat_some (a := [Dec.tld .v1 jl]) (b := [Dec.tld .v2 jh]) (tld_run s .v1 hl hx) (tld_run a .v2 hh hx)
  obtain o : VOnly [.v1, .v2, .v7] s t :=
    ((((VOnly.setV s (by simp) _).trans (VOnly.setV a (by simp) _)).trans (VOnly.setV b (by simp) _)).trans
      (VOnly.setV c (by simp) _)).trans (VOnly.setV e (by rcases hd with rfl | rfl <;> simp) _)
  refine ⟨t, ?_, ?_, fun h => ?_, o⟩
  · exact runBlock_cat_some (a := [Dec.tld .v1 jl, Dec.tld .v2 jh]) hab (by rcases hd with rfl | rfl <;> rfl)
  · rcases hd with rfl | rfl <;>
      simp only [t, e, c, b, a, v_setV, reduceCtorEq, ite_true, ite_false]
  · subst h; rfl

/-- `keyRot`: `v1`, its bytes permuted by vector `jp` of the static, XORed
into `v7`. -/
theorem keyRot_run (s : State) (hx : s.gpr .x6 = s.syms Dec.tabName) {jp : Nat} (hp : jp < 30) :
    ∃ t, runBlock isa (keyRot jp) s = some t ∧ t.v .v7 = s.v .v7 ^^^ tblV (s.v .v1) (Dec.tabVec jp) ∧
      t.v .v5 = s.v .v5 ∧ t.v .v6 = s.v .v6 ∧ VOnly [.v1, .v2, .v7] s t := by
  let a := s.setV .v2 (Dec.tabVec jp)
  let b := a.setV .v1 (tblV (a.v .v1) (a.v .v2))
  let t := b.setV .v7 (b.v .v7 ^^^ b.v .v1)
  refine ⟨t, runBlock_cat_some (a := [Dec.tld .v2 jp]) (tld_run s .v2 hp hx) rfl, ?_, rfl, rfl,
    ((VOnly.setV s (by simp) _).trans (VOnly.setV a (by simp) _)).trans (VOnly.setV b (by simp) _)⟩
  simp only [t, b, a, v_setV, reduceCtorEq, ite_true, ite_false]

theorem Consts.of_write {s : State} (h : Consts s) {r : Reg} (hr : r ≠ .x6) (x : BitVec 64) :
    Consts (s.write .x r x) :=
  ⟨(gpr_write_of_ne _ _ _ (Ne.symm hr)).trans h.x6, h.v16, h.v17, h.v18, h.v19, h.v20, h.v21, h.v22, h.v23,
    h.v24, h.v25, h.v26, h.v27, h.v28, h.v29, h.v30⟩

/-- `key`: `D` of InvMixColumns of the round key in `v5`, with `D 0`. -/
theorem key_run (s : State) (hc : Consts s) :
    ∃ t, runBlock isa key s = some t ∧ t.v .v7 = keyV (s.v .v5) ∧
      VOnly [.v1, .v2, .v5, .v6, .v7] s t := by
  let a := s.setV .v6 (s.v .v5 &&& s.v .v16)
  let b := a.setV .v5 (ushr4 (a.v .v5))
  have hb : runBlock isa [.vop (.logic .and .v6 .v5 .v16), .vop (.shift .ushr .b16 .v5 .v5 4)] s = some b := rfl
  obtain ob : VOnly [.v1, .v2, .v5, .v6, .v7] s b := (VOnly.setV s (by simp) _).trans (VOnly.setV a (by simp) _)
  obtain b6 : b.v .v6 = s.v .v5 &&& mask := by
    simp only [b, a, v_setV, reduceCtorEq, ite_true, ite_false, hc.v16]
  obtain b5 : b.v .v5 = ushr4 (s.v .v5) := by
    simp only [b, a, v_setV, reduceCtorEq, ite_true, ite_false]
  obtain w : ∀ {u v : State}, VOnly [.v1, .v2, .v7] u v → VOnly [.v1, .v2, .v5, .v6, .v7] u v :=
    fun o => vonly_mono o (by decide)
  obtain x : ∀ {u v : State}, u.gpr .x6 = u.syms Dec.tabName → VOnly [.v1, .v2, .v7] u v →
      v.gpr .x6 = v.syms Dec.tabName := fun {u v} h o => by
    rw [o.gpr, show v.syms = u.syms by rw [o.1]]; exact h
  have bx : b.gpr .x6 = b.syms Dec.tabName := hc.x6
  obtain ⟨c, hc', c7, -, oc⟩ := keyTerm_run b bx (.inl rfl) (jl := 15) (jh := 16) (by decide) (by decide)
  obtain h1 := runBlock_cat_some hb hc'
  obtain cx := x bx oc
  obtain ⟨d, hd, d1, d7, od⟩ := keyTerm_run c cx (.inr rfl) (jl := 17) (jh := 18) (by decide) (by decide)
  obtain h2 := runBlock_cat_some h1 hd
  obtain dx := x cx od
  obtain ⟨e, he, e7, e5, e6, oe⟩ := keyRot_run d dx (jp := 23) (by decide)
  obtain h3 := runBlock_cat_some h2 he
  obtain ex := x dx oe
  obtain ⟨f, hf, f1, f7, of⟩ := keyTerm_run e ex (.inr rfl) (jl := 19) (jh := 20) (by decide) (by decide)
  obtain h4 := runBlock_cat_some h3 hf
  obtain fx := x ex of
  obtain ⟨g, hg, g7, g5, g6, og⟩ := keyRot_run f fx (jp := 24) (by decide)
  obtain h5 := runBlock_cat_some h4 hg
  obtain gx := x fx og
  obtain ⟨h, hh, i1, i7, oh⟩ := keyTerm_run g gx (.inr rfl) (jl := 21) (jh := 22) (by decide) (by decide)
  obtain h6 := runBlock_cat_some h5 hh
  obtain hx := x gx oh
  obtain ⟨t, ht, t7, -, -, ot⟩ := keyRot_run h hx (jp := 25) (by decide)
  obtain h7 := runBlock_cat_some h6 ht
  obtain c5 : c.v .v5 = b.v .v5 := oc.2 _ (by decide)
  obtain c6 : c.v .v6 = b.v .v6 := oc.2 _ (by decide)
  obtain d5 : d.v .v5 = b.v .v5 := (od.2 _ (by decide)).trans c5
  obtain d6 : d.v .v6 = b.v .v6 := (od.2 _ (by decide)).trans c6
  obtain f5 : f.v .v5 = b.v .v5 := (of.2 _ (by decide)).trans (e5.trans d5)
  obtain f6 : f.v .v6 = b.v .v6 := (of.2 _ (by decide)).trans (e6.trans d6)
  obtain k5 : h.v .v5 = b.v .v5 := (oh.2 _ (by decide)).trans (g5.trans f5)
  obtain k6 : h.v .v6 = b.v .v6 := (oh.2 _ (by decide)).trans (g6.trans f6)
  refine ⟨t, h7, ?_, (((((((ob.trans (w oc)).trans (w od)).trans (w oe)).trans (w of)).trans (w og)).trans
    (w oh)).trans (w ot))⟩
  rw [t7, i7 rfl, g7, f7 rfl, e7, d7 rfl, c7, i1, f1, d1, g6, g5, e6, e5, c6, c5, d6, d5, f6, f5, b6, b5]
  rfl

/-- `mix`, on `io` and `jo` in `v2` and `v3` and the round key's part in `v7`. -/
theorem mix_run (s : State) (hc : Consts s) :
    ∃ t, runBlock isa Dec.mix s = some t ∧ t.v .v0 = Dec.mixV (s.v .v2) (s.v .v3) (s.v .v7) ∧
      VOnly [.v0, .v1, .v4, .v5, .v6] s t := by
  let a := s.setV .v0 (tblV (s.v .v19) (s.v .v2))
  let b := a.setV .v1 (tblV (a.v .v20) (a.v .v3))
  let c := b.setV .v0 (b.v .v0 ^^^ b.v .v1)
  let d := c.setV .v0 (tblV (c.v .v0) (c.v .v27))
  let e := d.setV .v1 (tblV (d.v .v21) (d.v .v2))
  let f := e.setV .v4 (tblV (e.v .v22) (e.v .v3))
  let g := f.setV .v1 (f.v .v1 ^^^ f.v .v4)
  let h := g.setV .v1 (tblV (g.v .v1) (g.v .v28))
  let i := h.setV .v4 (tblV (h.v .v23) (h.v .v2))
  let j := i.setV .v5 (tblV (i.v .v24) (i.v .v3))
  let k := j.setV .v4 (j.v .v4 ^^^ j.v .v5)
  let l := k.setV .v4 (tblV (k.v .v4) (k.v .v29))
  let m := l.setV .v5 (tblV (l.v .v25) (l.v .v2))
  let n := m.setV .v6 (tblV (m.v .v26) (m.v .v3))
  let o := n.setV .v5 (n.v .v5 ^^^ n.v .v6)
  let p := o.setV .v5 (tblV (o.v .v5) (o.v .v30))
  let q := p.setV .v0 (p.v .v0 ^^^ p.v .v1)
  let r := q.setV .v4 (q.v .v4 ^^^ q.v .v5)
  let u := r.setV .v0 (r.v .v0 ^^^ r.v .v7)
  let t := u.setV .v0 (u.v .v0 ^^^ u.v .v4)
  refine ⟨t, rfl, ?_, ?_⟩
  · simp only [t, u, r, q, p, o, n, m, l, k, j, i, h, g, f, e, d, c, b, a, v_setV, reduceCtorEq, ite_true,
      ite_false, hc.v19, hc.v20, hc.v21, hc.v22, hc.v23, hc.v24, hc.v25, hc.v26, hc.v27, hc.v28, hc.v29,
      hc.v30, Dec.mixV, xV]
  · exact (((((((((((((((((((VOnly.setV s (by simp) _).trans (VOnly.setV a (by simp) _)).trans
      (VOnly.setV b (by simp) _)).trans (VOnly.setV c (by simp) _)).trans (VOnly.setV d (by simp) _)).trans
      (VOnly.setV e (by simp) _)).trans (VOnly.setV f (by simp) _)).trans (VOnly.setV g (by simp) _)).trans
      (VOnly.setV h (by simp) _)).trans (VOnly.setV i (by simp) _)).trans (VOnly.setV j (by simp) _)).trans
      (VOnly.setV k (by simp) _)).trans (VOnly.setV l (by simp) _)).trans (VOnly.setV m (by simp) _)).trans
      (VOnly.setV n (by simp) _)).trans (VOnly.setV o (by simp) _)).trans (VOnly.setV p (by simp) _)).trans
      (VOnly.setV q (by simp) _)).trans (VOnly.setV r (by simp) _)).trans (VOnly.setV u (by simp) _)

/-- `last`, on `io` and `jo` in `v2` and `v3` and the round key in `v5`. -/
theorem last_run (s : State) (hc : Consts s) :
    ∃ t, runBlock isa Dec.last s = some t ∧ t.v .v0 = Dec.lastV (s.v .v2) (s.v .v3) (s.v .v5) ∧
      VOnly [.v0, .v1] s t := by
  let a := s.setV .v0 (Dec.tabVec 28)
  let b := a.setV .v1 (Dec.tabVec 29)
  let c := b.setV .v0 (tblV (b.v .v0) (b.v .v2))
  let d := c.setV .v1 (tblV (c.v .v1) (c.v .v3))
  let e := d.setV .v0 (d.v .v0 ^^^ d.v .v1)
  let f := e.setV .v0 (tblV (e.v .v0) (e.v .v27))
  let t := f.setV .v0 (f.v .v0 ^^^ f.v .v5)
  obtain hab : runBlock isa [Dec.tld .v0 28, Dec.tld .v1 29] s = some b :=
    runBlock_cat_some (a := [Dec.tld .v0 28]) (b := [Dec.tld .v1 29]) (tld_run s .v0 (by decide) hc.x6)
      (tld_run a .v1 (by decide) hc.x6)
  refine ⟨t, runBlock_cat_some (a := [Dec.tld .v0 28, Dec.tld .v1 29]) hab rfl, ?_, ?_⟩
  · simp only [t, f, e, d, c, b, a, v_setV, reduceCtorEq, ite_true, ite_false, hc.v27, Dec.lastV]
    rfl
  · exact ((((((VOnly.setV s (by simp) _).trans (VOnly.setV a (by simp) _)).trans
      (VOnly.setV b (by simp) _)).trans (VOnly.setV c (by simp) _)).trans (VOnly.setV d (by simp) _)).trans
      (VOnly.setV e (by simp) _)).trans (VOnly.setV f (by simp) _)

/-! ## Decryption: the rounds -/

open VG.Spec.Aes (invCipher invSubBytes invShiftRows invMixColumns)
open VG.Proof.Aes (invMid invMid_succ invCipher_eq irnd)

/-- After `j` full rounds from the state `z`, with the key schedule at `K`:
the state `Z` as `Dv Z` in `v0`, `x0` at round key `R − j`, and `R − 1 − j`
in `x1`. -/
structure RInv (s₀ : State) (K : Addr) (R : Nat) (w : List Byte) (z : Spec.Aes.State) (j : Nat)
    (s : State) : Prop where
  consts : Consts s
  x0 : s.gpr .x0 = K + BitVec.ofNat 64 (16 * (R - j))
  x1 : s.gpr .x1 = BitVec.ofNat 64 (R - 1 - j)
  st : ∃ Z, s.v .v0 = Dv Z ∧ st Z = invMid R w j z
  gpr : ∀ r, r ≠ .x0 → r ≠ .x1 → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

/-- `x0`, back by a round key. -/
theorem sub16 (K : Addr) {n : Nat} (h : 1 ≤ n) :
    K + BitVec.ofNat 64 (16 * n) - BitVec.ofNat 64 16 = K + BitVec.ofNat 64 (16 * (n - 1)) := by
  rw [show 16 * n = 16 * (n - 1) + 16 by omega_arith, BitVec.ofNat_add, ← BitVec.add_assoc,
    BitVec.add_sub_cancel]

/-- `x0` back by a round key, and that round key into `v5`. -/
theorem prev_ok {s : State} {K : Addr} {n : Nat} (hc : Consts s) (hK : (⟨K, 240⟩ : Region) ∈ s.rd)
    (h0 : s.gpr .x0 = K + BitVec.ofNat 64 (16 * n)) (h1 : 1 ≤ n) (hn : n ≤ 14) :
    WP isa (.block [.subImm .x .x0 .x0 16, .ldrq .v5 .x0 0]) s fun b =>
      Consts b ∧ b.v .v5 = s.mem.readW (K + BitVec.ofNat 64 (16 * (n - 1))) 128 ∧
      b.gpr .x0 = K + BitVec.ofNat 64 (16 * (n - 1)) ∧ (∀ r, r ≠ .x0 → b.gpr r = s.gpr r) ∧
      (∀ r, r ≠ .v5 → b.v r = s.v r) ∧ b.mem = s.mem ∧ b.rd = s.rd ∧ b.wr = s.wr ∧ b.sp = s.sp := by
  let a := s.write .x .x0 (s.read .x .x0 - BitVec.ofNat 64 16)
  rw [WP.block_cons_iff]
  refine ⟨a, exec_subImm_x (imm := 16) (by decide), ?_⟩
  obtain a0 : a.gpr .x0 = K + BitVec.ofNat 64 (16 * (n - 1)) := by
    rw [show a.gpr .x0 = s.gpr .x0 - BitVec.ofNat 64 16 by simp [a, State.write, read_x], h0, sub16 K h1]
  obtain ac : Consts a := hc.of_write (by decide) _
  obtain ⟨b, hb, b5, ob⟩ := Vperm.key_run a (off := 0) (by decide)
    ⟨_, List.mem_append_left _ (show (⟨K, 240⟩ : Region) ∈ a.rd from hK),
      by rw [a0, BitVec.add_zero]; exact Offset.contains_base K (by omega_arith) (by omega_arith)⟩
  refine WP.of_runBlock ⟨b, hb, ac.of_v (vonly_mono ob (by decide)), ?_, ?_, fun r hr => ?_,
    fun r hr => ob.2 r (by simpa using hr), ob.mem, ob.rd, ob.wr, (VOnly.sp ob :)⟩
  · rw [b5, a0, BitVec.add_zero]; rfl
  · rw [ob.gpr]; exact a0
  · rw [ob.gpr]; simp [a, State.write, hr]

/-- A full round. -/
theorem round_ok {s₀ : State} {K : Addr} {R : Nat} {z : Spec.Aes.State} (hK : (⟨K, 240⟩ : Region) ∈ s₀.rd)
    (hR : R ≤ 14) {j : Nat} (hj : j + 2 ≤ R) {s : State}
    (hI : RInv s₀ K R (bytesAt s₀.mem K (16 * (R + 1))) z j s) :
    WP isa (.block Dec.round) s (RInv s₀ K R (bytesAt s₀.mem K (16 * (R + 1))) z (j + 1)) := by
  obtain ⟨Z, hZ, hst⟩ := hI.st
  rw [Dec.round, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (prev_ok (n := R - j) hI.consts (by rw [hI.rd]; exact hK) hI.x0 (by omega_arith)
    (by omega_arith)) fun b ⟨bc, b5, b0, bg, bv, bm, brd, bwr, bsp⟩ => ?_
  rw [WP.block_append_iff]
  obtain ⟨c, hc, c7, oc⟩ := key_run b bc
  refine WP.of_runBlock ⟨c, hc, ?_⟩
  obtain oc' : VOnly temps b c := vonly_mono oc (by decide)
  obtain cc : Consts c := bc.of_v oc'
  rw [WP.block_append_iff]
  obtain ⟨d, hd, d2, d3, od⟩ := invert_run c cc.v16 cc.v17 cc.v18
  refine WP.of_runBlock ⟨d, hd, ?_⟩
  obtain od' : VOnly temps c d := vonly_mono od (by decide)
  obtain dc : Consts d := cc.of_v od'
  rw [WP.block_append_iff]
  obtain ⟨e, he, e0, oe⟩ := mix_run d dc
  refine WP.of_runBlock ⟨e, he, ?_⟩
  obtain oe' : VOnly temps d e := vonly_mono oe (by decide)
  obtain o : VOnly temps b e := (oc'.trans od').trans oe'
  let f := e.write .x .x1 (e.read .x .x1 - BitVec.ofNat 64 1)
  rw [WP.block_cons_iff]
  refine ⟨f, exec_subImm_x (imm := 1) (by decide), WP.block_nil ?_⟩
  obtain hk : KeyIs (s.mem.readW (K + BitVec.ofNat 64 (16 * (R - j - 1))) 128)
      (roundKey (bytesAt s₀.mem K (16 * (R + 1))) (R - 1 - j)) := by
    rw [hI.mem, show R - j - 1 = R - 1 - j by omega_arith]
    exact keyIs_readW s₀.mem K (by omega_arith)
  obtain c0 : c.v .v0 = Dv Z := by
    rw [oc.2 _ (by decide), bv _ (by decide)]
    exact hZ
  obtain d7 : d.v .v7 = keyV (s.mem.readW (K + BitVec.ofNat 64 (16 * (R - j - 1))) 128) := by
    rw [od.2 _ (by decide), c7, b5]
  obtain ex1 : e.gpr .x1 = BitVec.ofNat 64 (R - 1 - j) := by
    rw [o.gpr, bg _ (by decide)]; exact hI.x1
  refine ⟨(dc.of_v oe').of_write (by decide) _, ?_, ?_,
    ⟨aesInvMixColumns (aesMapBytes aesInvSbox (aesInvShiftRows Z) ^^^
      s.mem.readW (K + BitVec.ofNat 64 (16 * (R - j - 1))) 128), ?_, ?_⟩, fun r h0 h1 => ?_,
    o.mem.trans (bm.trans hI.mem), o.rd.trans (brd.trans hI.rd), o.wr.trans (bwr.trans hI.wr),
    (VOnly.sp o).trans (bsp.trans hI.sp)⟩
  · rw [show f.gpr .x0 = e.gpr .x0 by simp [f, State.write], o.gpr, b0,
      show R - (j + 1) = R - j - 1 by omega_arith]
  · rw [show f.gpr .x1 = e.gpr .x1 - BitVec.ofNat 64 1 by simp [f, State.write, read_x], ex1,
      ofNat_sub_one (by omega_arith), Nat.sub_sub]
  · rw [show f.v .v0 = e.v .v0 from rfl, e0, d2, d3, d7, c0]
    exact Dec.mixV_eq _ _
  · rw [invMid_succ, st_aesimc, eor_st hk, st_invSub, hst]
    rfl
  · rw [show f.gpr r = e.gpr r by simp [f, State.write, h1], o.gpr, bg r h0]
    exact hI.gpr r h0 h1

/-- The full rounds: `R − 1` of them. -/
theorem loop_ok {s₀ : State} {K : Addr} {R : Nat} {z : Spec.Aes.State} (hK : (⟨K, 240⟩ : Region) ∈ s₀.rd)
    (hR : R ≤ 14) (hR2 : 2 ≤ R) {s : State} (hI : RInv s₀ K R (bytesAt s₀.mem K (16 * (R + 1))) z 0 s) :
    WP isa (.loop (.block Dec.round) (.nonzero .x .x1)) s
      (RInv s₀ K R (bytesAt s₀.mem K (16 * (R + 1))) z (R - 1)) := by
  refine WP.loop (M := isa) (fun n t => ∃ j, n = R - 1 - j ∧ j + 2 ≤ R ∧
    RInv s₀ K R (bytesAt s₀.mem K (16 * (R + 1))) z j t) ?_ (R - 1) s ⟨0, rfl, hR2, hI⟩
  rintro n t ⟨j, hn, hj, hI⟩
  refine WP.mono (round_ok hK hR hj hI) fun t' hI' => ?_
  obtain he : isa.eval (.nonzero .x .x1) t' = some (BitVec.ofNat 64 (R - 1 - (j + 1)) != 0) := by
    simp [AArch64.eval, State.read, hI'.x1]
  rcases Nat.lt_or_ge (j + 2) R with h | h
  · exact .inr ⟨by rw [he, ofNat_bne_zero (by omega_arith) (by omega_arith)], R - 1 - (j + 1), by omega_arith,
      j + 1, rfl, h, hI'⟩
  · have e : j + 1 = R - 1 := by omega_arith
    refine .inl ⟨by rw [he, show R - 1 - (j + 1) = 0 by omega_arith]; rfl, ?_⟩
    rw [← e]; exact hI'

/-- The last round. -/
theorem last_ok {s₀ : State} {K : Addr} {R : Nat} {x : Spec.Aes.State} (hK : (⟨K, 240⟩ : Region) ∈ s₀.rd)
    (hR : R ≤ 14) (hR2 : 2 ≤ R) {s : State}
    (hI : RInv s₀ K R (bytesAt s₀.mem K (16 * (R + 1)))
      (addRoundKey x (roundKey (bytesAt s₀.mem K (16 * (R + 1))) R)) (R - 1) s) :
    WP isa (.block (([.subImm .x .x0 .x0 16, .ldrq .v5 .x0 0] : List Instr) ++ invert ++ Dec.last)) s fun t =>
      st (t.v .v0) = invCipher R (bytesAt s₀.mem K (16 * (R + 1))) x ∧
      (∀ r, r ≠ .x0 → r ≠ .x1 → t.gpr r = s₀.gpr r) ∧ t.mem = s₀.mem ∧ t.rd = s₀.rd ∧ t.wr = s₀.wr ∧
      t.sp = s₀.sp := by
  obtain ⟨Z, hZ, hst⟩ := hI.st
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (prev_ok (n := R - (R - 1)) hI.consts (by rw [hI.rd]; exact hK) hI.x0 (by omega_arith)
    (by omega_arith)) fun b ⟨bc, b5, b0, bg, bv, bm, brd, bwr, bsp⟩ => ?_
  rw [WP.block_append_iff]
  obtain ⟨d, hd, d2, d3, od⟩ := invert_run b bc.v16 bc.v17 bc.v18
  refine WP.of_runBlock ⟨d, hd, ?_⟩
  obtain od' : VOnly temps b d := vonly_mono od (by decide)
  obtain dc : Consts d := bc.of_v od'
  obtain ⟨t, ht, t0, ot⟩ := last_run d dc
  obtain o : VOnly temps b t := od'.trans (vonly_mono ot (by decide))
  refine WP.of_runBlock ⟨t, ht, ?_, fun r h0 h1 => ?_, o.mem.trans (bm.trans hI.mem),
    o.rd.trans (brd.trans hI.rd), o.wr.trans (bwr.trans hI.wr), (VOnly.sp o).trans (bsp.trans hI.sp)⟩
  · have hk : KeyIs (s.mem.readW (K + BitVec.ofNat 64 (16 * (R - (R - 1) - 1))) 128)
        (roundKey (bytesAt s₀.mem K (16 * (R + 1))) 0) := by
      rw [hI.mem, show R - (R - 1) - 1 = 0 by omega_arith]
      exact keyIs_readW s₀.mem K (by omega_arith)
    rw [t0, d2, d3, od.2 _ (by decide), b5, show b.v .v0 = s.v .v0 from bv _ (by decide), hZ, Dec.lastV_eq,
      eor_st hk, st_invSub, hst, invCipher_eq]
  · rw [o.gpr, bg r h0]; exact hI.gpr r h0 h1

/-- `first`: the block and the last round key. -/
theorem first_ok {s : State} {K : Addr} {R : Nat} (hc : Consts s) (hK : (⟨K, 240⟩ : Region) ∈ s.rd)
    (h0 : s.gpr .x0 = K + BitVec.ofNat 64 (16 * R)) (h1 : s.gpr .x1 = BitVec.ofNat 64 R)
    (hR : 2 ≤ R ∧ R ≤ 14) :
    WP isa (.block Dec.first) s (RInv s K R (bytesAt s.mem K (16 * (R + 1)))
      (addRoundKey (st (s.v .v0)) (roundKey (bytesAt s.mem K (16 * (R + 1))) R)) 0) := by
  rw [show Dec.first = [.ldrq .v5 .x0 0] ++ ([.vop (.logic .eor .v0 .v0 .v5)] ++
    ([Dec.tld .v2 26, Dec.tld .v3 27] ++ ([.vop (.logic .and .v1 .v0 .v16), .vop (.shift .ushr .b16 .v0 .v0 4),
      .vop (.tbl .v1 .v2 .v1), .vop (.tbl .v0 .v3 .v0), .vop (.logic .eor .v0 .v0 .v1)] ++
      [.subImm .x .x1 .x1 1]))) from rfl, WP.block_append_iff]
  obtain ⟨a, ha, a5, oa⟩ := Vperm.key_run s (off := 0) (by decide) ⟨_, List.mem_append_left _ hK,
    by rw [h0, BitVec.add_zero]; exact Offset.contains_base K (by omega_arith) (by omega_arith)⟩
  refine WP.of_runBlock ⟨a, ha, ?_⟩
  obtain oa' : VOnly temps s a := vonly_mono oa (by decide)
  obtain ac : Consts a := hc.of_v oa'
  let b := a.setV .v0 (a.v .v0 ^^^ a.v .v5)
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨b, rfl, ?_⟩
  obtain ob : VOnly temps a b := VOnly.setV a (by simp) _
  obtain bc : Consts b := ac.of_v ob
  let c := b.setV .v2 (Dec.tabVec 26)
  let d := c.setV .v3 (Dec.tabVec 27)
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨d, runBlock_cat_some (a := [Dec.tld .v2 26]) (b := [Dec.tld .v3 27])
    (tld_run b .v2 (by decide) bc.x6) (tld_run c .v3 (by decide) bc.x6), ?_⟩
  obtain od : VOnly temps b d := (VOnly.setV b (by simp) _).trans (VOnly.setV c (by simp) _)
  obtain dc : Consts d := bc.of_v od
  let e := d.setV .v1 (d.v .v0 &&& d.v .v16)
  let f := e.setV .v0 (ushr4 (e.v .v0))
  let g := f.setV .v1 (tblV (f.v .v2) (f.v .v1))
  let h := g.setV .v0 (tblV (g.v .v3) (g.v .v0))
  let i := h.setV .v0 (h.v .v0 ^^^ h.v .v1)
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨i, rfl, ?_⟩
  obtain oi : VOnly temps d i := ((((VOnly.setV d (by simp) _).trans (VOnly.setV e (by simp) _)).trans
    (VOnly.setV f (by simp) _)).trans (VOnly.setV g (by simp) _)).trans (VOnly.setV h (by simp) _)
  obtain o : VOnly temps s i := ((oa'.trans ob).trans od).trans oi
  let t := i.write .x .x1 (i.read .x .x1 - BitVec.ofNat 64 1)
  rw [WP.block_cons_iff]
  refine ⟨t, exec_subImm_x (imm := 1) (by decide), WP.block_nil ?_⟩
  obtain hk : KeyIs (s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 0) 128)
      (roundKey (bytesAt s.mem K (16 * (R + 1))) R) := by
    rw [h0, BitVec.add_zero]
    exact keyIs_readW s.mem K (by omega_arith)
  obtain i0 : i.v .v0 = firstV (s.v .v0 ^^^ s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 0) 128) := by
    simp only [i, h, g, f, e, d, c, b, v_setV, reduceCtorEq, ite_true, ite_false, ac.v16, a5,
      show a.v .v0 = s.v .v0 from oa.2 _ (by decide), firstV]
    rfl
  refine ⟨(dc.of_v oi).of_write (by decide) _, ?_, ?_,
    ⟨s.v .v0 ^^^ s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 0) 128, ?_, ?_⟩, fun r _ h1 => ?_, o.mem, o.rd,
    o.wr, (VOnly.sp o :)⟩
  · rw [show t.gpr .x0 = i.gpr .x0 by simp [t, State.write], o.gpr, h0, Nat.sub_zero]
  · rw [show t.gpr .x1 = i.gpr .x1 - BitVec.ofNat 64 1 by simp [t, State.write, read_x], o.gpr, h1,
      ofNat_sub_one (by omega_arith)]
    rfl
  · rw [show t.v .v0 = i.v .v0 from rfl, i0, firstV_eq]
  · rw [eor_st hk]
    rfl
  · rw [show t.gpr r = i.gpr r by simp [t, State.write, h1], o.gpr]

/-- `core` is the inverse cipher, on the state in `v0`, with the schedule
at `x0` and the rounds in `x1`. -/
theorem core_ok {s : State} {K : Addr} {R : Nat} (hK : (⟨K, 240⟩ : Region) ∈ s.rd) (h0 : s.gpr .x0 = K)
    (h1 : s.gpr .x1 = BitVec.ofNat 64 R) (hR : R = 10 ∨ R = 12 ∨ R = 14) :
    WP isa Dec.core s fun t =>
      st (t.v .v0) = invCipher R (bytesAt s.mem K (16 * (R + 1))) (st (s.v .v0)) ∧
      (∀ r, r ≠ .x0 → r ≠ .x1 → r ≠ .x6 → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
      t.wr = s.wr ∧ t.sp = s.sp := by
  obtain hR14 : R ≤ 14 := by omega_arith
  obtain hR2 : 2 ≤ R := by omega_arith
  rw [Dec.core]
  refine WP.seq (WP.mono (setup_ok h0 h1 hR) fun a ⟨ac, av, a0, ag, am, ard, awr, asp⟩ => ?_)
  obtain hKa : (⟨K, 240⟩ : Region) ∈ a.rd := by rw [ard]; exact hK
  rw [Dec.rounds]
  refine WP.seq (WP.mono (first_ok ac hKa a0 ((ag _ (by decide) (by decide)).trans h1) ⟨hR2, hR14⟩)
    fun c hI => ?_)
  refine WP.seq (WP.mono (loop_ok hKa hR14 hR2 hI) fun d hd => ?_)
  refine WP.mono (last_ok hKa hR14 hR2 hd) fun t ⟨tst, tg, tm, trd, twr, tsp⟩ => ?_
  refine ⟨by rw [tst, am, av], fun r h0 h1 h6 => (tg r h0 h1).trans (ag r h0 h6), tm.trans am,
    trd.trans ard, twr.trans awr, tsp.trans asp⟩

end Dec

end VG.Proof.Aes.AArch64.Vperm

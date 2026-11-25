module

public import VerifiedGarbage.Impl.Aes.RISCV64.Rounds
public import VerifiedGarbage.Proof.Aes.Bitsliced
public import VerifiedGarbage.Proof.Framework.RISCV64.Linear
public import VerifiedGarbage.Proof.Aes.Sbox0
import VerifiedGarbage.Proof.Framework.Bitslice.Lanes

/-!
# The layers of bitsliced AES on RISC-V, by evaluation

Each layer is straight-line bitwise code on the eight slices in `q 0 … q 7`
(`Q s`). The S-boxes combine words bit by bit, so the kernel evaluates them
once on truth tables of the 256 inputs; the linear layers are evaluated over
the lane domain, which gives the input bits each output bit XORs, as (slice,
position) pairs. Both give what the layer does to the slices, and `Rest`,
what else it changes: the registers of `sboxWrites` and the spill slots.

`Bs S` (`BsRel`, four states, form 0) relates the slices to the states, and
`InRel` the registers to them as bytes, before `toBs` and after `fromBs`.
-/

@[expose] public section

namespace VG.Proof.Aes.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Bitslice VG.Impl.Aes.RISCV64
open VG.Proof.Aes (bsByte getLsbD_bsByte termsXor byte_ext)

/-! ## Registers and memory -/

/-- The slices. -/
abbrev Q (s : State) (j : Nat) : BitVec 64 := s.gpr (q j)

/-- The registers the layers may write, and the others they may read. -/
def sboxWrites : List Reg := [q 0, q 1, q 2, q 3, q 4, q 5, q 6, q 7, .t0, .t1, .t2, .t3, .t4,
  .t5, .t6, .a6, .a7, .s8, .s9, .s10, .s11]

def restRegs : List Reg := [.ra, .a0, .a1, .a2, .a3, .a4, .a5]

theorem not_sboxWrites (r : Reg) (hr : r ∉ sboxWrites) : r ∈ restRegs := by
  revert hr; cases r <;> decide

/-- Code that writes none of `restRegs`. -/
def keepsRest (is : List Instr) : Bool := restRegs.all fun r => is.all fun i => dst i != some r

theorem keepsRest_ok {is : List Instr} (h : keepsRest is = true) (r : Reg) (hr : r ∉ sboxWrites) :
    (is.all fun i => dst i != some r) = true :=
  List.all_eq_true.mp h r (not_sboxWrites r hr)

/-- What a layer leaves alone. -/
def Rest (c : Cfg) (s s' : State) : Prop :=
  s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) ∧
    Frame [slotRegion c s] s.mem s'.mem

/-- The masks `ks`, by slot, are in memory. -/
def MasksAt (m : Mem) (b : Addr) (ks : List (Nat × BitVec 64)) : Prop :=
  ∀ k v, (k, v) ∈ ks → m.readW (wordAddr b k) 64 = v

/-- Masks numbered from 1, in the slots from `base` on. -/
def ksOf (base : Nat) (ms : List (Nat × BitVec 64)) : List (Nat × BitVec 64) :=
  ms.map fun p => (base + p.1 - 1, p.2)

def bsKs : List (Nat × BitVec 64) := ksOf bsSlot idxMasks
def srKs : List (Nat × BitVec 64) := ksOf srSlot srMasks

/-! ## Where the layers' memory is -/

def sboxCfg : Cfg := { base := sb, slots := 40, ext := sb, exts := 0 }
def bsCfg : Cfg := { base := sb, slots := 0, ext := sb, exts := 58 }
def srCfg : Cfg := { base := sb, slots := 0, ext := sb, exts := 76 }
def arkCfg : Cfg := { base := sb, slots := 0, ext := kp, exts := 8 }

/-! ## Bitwise code -/

/-- At each position `p`, the word's bit is row `cs p` of the table. -/
def TabAll (cs : Nat → Nat) (a : Nat) (x : BitVec 64) : Prop := ∀ p < 64, TableRel p (cs p) a x

theorem tabAll_sound {cs : Nat → Nat} (hcs : ∀ p < 64, cs p < 256) :
    (table 64 256).Sound (TabAll cs) where
  xor ha hb h p hp := (table_sound hp (hcs p hp)).xor (ha p hp) (hb p hp) h
  and ha hb h p hp := (table_sound hp (hcs p hp)).and (ha p hp) (hb p hp) h
  or ha hb h p hp := (table_sound hp (hcs p hp)).or (ha p hp) (hb p hp) h
  ror _ h := by cases h
  shr _ h := by cases h
  const h p hp := (table_sound hp (hcs p hp)).const h

theorem tabAll_fun {cs : Nat → Nat} (a : Nat) (x y : BitVec 64) (hx : TabAll cs a x) (hy : TabAll cs a y) :
    x = y :=
  BitVec.eq_of_getLsbD_eq fun p hp => (hx p hp).symm.trans (hy p hp)

/-- The slices hold the tables of the 256 inputs. -/
def tabEnv : Env Nat :=
  { reg := fun r => ((List.range 8).find? fun j => q j == r).map fun j => .v (sbIn j)
    slot := fun _ => none }

/-- They hold the tables `T`. -/
def tabPost (T : List Nat) (e : Env Nat) : Bool :=
  (List.range 8).all fun j => word (e.reg (q j)) == some (T.getD j 0)

theorem word_eq {α : Type} {o : Option (Val α)} {a : α} (h : word o = some a) : o = some (.v a) := by
  match o, h with
  | some (.v _), h => rw [word, Option.some.injEq] at h; rw [h]

/-- Code that the tables show to apply `g` to the byte at every position. -/
theorem tab_ok {is : List Instr} {T : List Nat} {g : Byte → Byte}
    (hT : ∀ c j, c < 256 → j < 8 → (T.getD j 0).testBit c = (g (BitVec.ofNat 8 c)).getLsbD j)
    (hchk : check (table 64 256) sboxCfg (fun _ => none) is tabEnv (tabPost T) = true)
    (hkeep : keepsRest is = true) {s : State} (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa is s = some s' ∧
      (∀ j < 8, ∀ p < 64, (Q s' j).getLsbD p = (g (bsByte (Q s) p)).getLsbD j) ∧
      Rest sboxCfg s s' := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hchk
  let cs : Nat → Nat := fun p => (bsByte (Q s) p).toNat
  have hcs : ∀ p < 64, cs p < 256 := fun p _ => (bsByte (Q s) p).isLt
  have hrel : Rel (TabAll cs) sboxCfg (fun _ => none) tabEnv s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩
    simp only [tabEnv, Option.map_eq_some_iff] at h
    obtain ⟨j, hj, rfl⟩ := h
    obtain ⟨rfl, hj8⟩ : q j = r ∧ j < 8 :=
      ⟨by simpa using List.find?_some hj, List.mem_range.mp (List.mem_of_find?_eq_some hj)⟩
    intro p hp
    simp only [TableRel, sbIn, testBit_tableOf, hcs p hp, decide_true, Bool.true_and, cs,
      BitVec.testBit_toNat, getLsbD_bsByte _ _ hj8]
  obtain ⟨s', hs', p₀⟩ := run (tabAll_sound hcs) tabAll_fun hok hrel he
  refine ⟨s', hs', fun j hj p hp => ?_, p₀.rd, p₀.wr, p₀.sp,
    fun r hr => p₀.other r (by simp [keepsRest_ok hkeep r hr]), p₀.frame⟩
  have h := word_eq (beq_iff_eq.mp (List.all_eq_true.mp hpost j (List.mem_range.mpr hj)))
  rw [← p₀.rel.reg (q j) _ h p hp, hT _ _ (hcs p hp) hj]
  simp [cs]

/-! ## Linear code -/

def qIns : List (Reg × Nat) := (List.range 8).map fun j => (q j, j)

def qOuts (g : Nat → Nat → List Nat) : List (Reg × (Nat → List Nat)) :=
  (List.range 8).map fun j => (q j, g j)

/-- Bits given as (word, position), as the lane domain numbers them. -/
def flat (T : Nat → Nat → List (Nat × Nat)) (j p : Nat) : List Nat := (T j p).map fun t => 64 * t.1 + t.2

/-- Every position is in a word. -/
def termsOk (T : Nat → Nat → List (Nat × Nat)) : Bool :=
  (List.range 8).all fun j => (List.range 64).all fun p => (T j p).all fun t => t.2 < 64

theorem termsOk_lt {T : Nat → Nat → List (Nat × Nat)} (h : termsOk T = true) {j p : Nat} (hj : j < 8)
    (hp : p < 64) : ∀ t ∈ T j p, t.2 < 64 := fun t ht =>
  of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp h j
    (List.mem_range.mpr hj)) p (List.mem_range.mpr hp)) t ht)

/-- Code that the lane domain shows to leave slice `j` the sums `T j`, of bits
of the words `W`: the slices, then the external words. -/
theorem lin_ok {k : Nat} {c : Cfg} {is : List Instr} {ext : Nat → Option (Nat × Nat)}
    {T : Nat → Nat → List (Nat × Nat)}
    (hchk : check (lanes 64 k) c ext is (linEnv qIns) (linPost k (qOuts (flat T))) = true)
    (hT : termsOk T = true) (hkeep : keepsRest is = true) (hk : 512 ≤ 2 ^ k) {s : State} (hok : Ok c s)
    (W : Nat → BitVec 64) (hW : ∀ j < 8, W j = Q s j)
    (hext : ∀ j a, j < c.exts → ext j = some a →
      LaneRel k (assign W (2 ^ k)) a (s.mem.readW (wordAddr (s.gpr c.ext) j) 64)) :
    ∃ s', runBlock isa is s = some s' ∧
      (∀ j < 8, ∀ p < 64, (Q s' j).getLsbD p = termsXor W (T j p)) ∧ Rest c s s' := by
  obtain ⟨s', hs', hout, hrd, hwr, hsp, hoth, hfr⟩ := linear_ok hchk hok W (fun r i hi => by
    obtain ⟨j, hj, he⟩ := List.mem_map.mp hi
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ he
    have hj := List.mem_range.mp hj
    exact ⟨by omega, hW j hj⟩) hext
  refine ⟨s', hs', fun j hj p hp => ?_, hrd, hwr, hsp, fun r hr => hoth r (keepsRest_ok hkeep r hr), hfr⟩
  rw [hout (q j) (flat T j) (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩) p hp]
  exact xorBits_map W _ (termsOk_lt hT hj hp)

/-! ## The states -/

/-- The slices hold the four states `S`. -/
abbrev BsRel (W : Nat → BitVec 64) (S : Nat → Spec.Aes.State) : Prop := Proof.Aes.BsRel 4 false W S

/-- They hold the round key, the same for the four. -/
abbrev KeyRel (W : Nat → BitVec 64) (rk : List Byte) : Prop := BsRel W fun _ => rkState rk

/-- The registers hold the four states as bytes: byte `i` of state `b` is
byte `i % 8` of word `b + 4 (i / 8)`. -/
def InRel (W : Nat → BitVec 64) (S : Nat → Spec.Aes.State) : Prop :=
  ∀ b < 4, ∀ i < 16, ∀ j < 8, (W (b + 4 * (i / 8))).getLsbD (8 * (i % 8) + j) = ((S b).getD i 0).getLsbD j

/-! ## SubBytes and its inverse -/

theorem sbox_check : check (table 64 256) sboxCfg (fun _ => none) sboxCode tabEnv (tabPost sboxOfT) = true := by
  decide +kernel

theorem invSbox_check :
    check (table 64 256) sboxCfg (fun _ => none) invSboxCode tabEnv (tabPost (invSboxT sbIns)) = true := by
  decide +kernel

theorem sbox_ok {s : State} (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa sboxCode s = some s' ∧
      (∀ j < 8, ∀ p < 64, (Q s' j).getLsbD p = (Spec.Aes.sbox (bsByte (Q s) p)).getLsbD j) ∧
      Rest sboxCfg s s' :=
  tab_ok (fun _ _ => sboxOfT_bit) sbox_check (by decide +kernel) hok

theorem invSbox_ok {s : State} (hok : Ok sboxCfg s) :
    ∃ s', runBlock isa invSboxCode s = some s' ∧
      (∀ j < 8, ∀ p < 64, (Q s' j).getLsbD p = (Spec.Aes.invSbox (bsByte (Q s) p)).getLsbD j) ∧
      Rest sboxCfg s s' :=
  tab_ok (fun c j hc hj => by rw [← getLsbD_row _ _ hj, row_invSboxT _ hc, row_sbIns hc]) invSbox_check
    (by decide +kernel) hok

theorem bs_subBytes {W W' : Nat → BitVec 64} {S : Nat → Spec.Aes.State}
    (h : ∀ j < 8, ∀ p < 64, (W' j).getLsbD p = (Spec.Aes.sbox (bsByte W p)).getLsbD j) (hS : BsRel W S) :
    BsRel W' fun b => Spec.Aes.subBytes (S b) := hS.map _ h

theorem bs_invSubBytes {W W' : Nat → BitVec 64} {S : Nat → Spec.Aes.State}
    (h : ∀ j < 8, ∀ p < 64, (W' j).getLsbD p = (Spec.Aes.invSbox (bsByte W p)).getLsbD j) (hS : BsRel W S) :
    BsRel W' fun b => Spec.Aes.invSubBytes (S b) := hS.map _ h

/-! ## Bytes to slices -/

def toBsT (j p : Nat) : List (Nat × Nat) :=
  [(p % 4 + 4 * (byteAt 4 false p / 8), 8 * (byteAt 4 false p % 8) + j)]

def fromBsT (w t : Nat) : List (Nat × Nat) := [(t % 8, at_ 4 false (8 * (w / 4) + t / 8) (w % 4))]

theorem toBs_check :
    check (lanes 64 9) bsCfg (kExt bsKs) toBs (linEnv qIns) (linPost 9 (qOuts (flat toBsT))) = true := by
  decide +kernel

theorem fromBs_check :
    check (lanes 64 9) bsCfg (kExt bsKs) fromBs (linEnv qIns) (linPost 9 (qOuts (flat fromBsT))) = true := by
  decide +kernel

theorem toBs_ok {s : State} (hok : Ok bsCfg s) (hks : MasksAt s.mem (s.gpr sb) bsKs) :
    ∃ s', runBlock isa toBs s = some s' ∧
      (∀ j < 8, ∀ p < 64, (Q s' j).getLsbD p = termsXor (Q s) (toBsT j p)) ∧ Rest bsCfg s s' :=
  lin_ok toBs_check (by decide +kernel) (by decide +kernel) (by decide) hok (Q s) (fun _ _ => rfl) (kExt_rel hks)

theorem fromBs_ok {s : State} (hok : Ok bsCfg s) (hks : MasksAt s.mem (s.gpr sb) bsKs) :
    ∃ s', runBlock isa fromBs s = some s' ∧
      (∀ j < 8, ∀ p < 64, (Q s' j).getLsbD p = termsXor (Q s) (fromBsT j p)) ∧ Rest bsCfg s s' :=
  lin_ok fromBs_check (by decide +kernel) (by decide +kernel) (by decide) hok (Q s) (fun _ _ => rfl) (kExt_rel hks)

theorem bs_of_in {W W' : Nat → BitVec 64} {S : Nat → Spec.Aes.State}
    (h : ∀ j < 8, ∀ p < 64, (W' j).getLsbD p = termsXor W (toBsT j p)) (hS : InRel W S) : BsRel W' S :=
  fun j hj n hn k hk => by
    rw [h j hj _ (at_lt false hn hk)]
    simp only [toBsT, termsXor, List.foldr_cons, List.foldr_nil, Bool.xor_false, byteAt_at false hn hk,
      at_mod false n hk]
    exact hS k hk n hn j hj

theorem in_of_bs {W W' : Nat → BitVec 64} {S : Nat → Spec.Aes.State}
    (h : ∀ j < 8, ∀ p < 64, (W' j).getLsbD p = termsXor W (fromBsT j p)) (hS : BsRel W S) : InRel W' S :=
  fun b hb i hi j hj => by
    rw [h _ (by omega) _ (by omega)]
    simp only [fromBsT, termsXor, List.foldr_cons, List.foldr_nil, Bool.xor_false]
    rw [show (8 * (i % 8) + j) % 8 = j by omega, show (b + 4 * (i / 8)) / 4 = i / 8 by omega,
      show (b + 4 * (i / 8)) % 4 = b by omega, show 8 * (i / 8) + (8 * (i % 8) + j) / 8 = i by omega]
    exact hS j hj i hi b hb

/-! ## ShiftRows and its inverse -/

/-- Where ShiftRows takes byte `n` from, and its inverse. -/
def srFrom (n : Nat) : Nat := n % 4 + 4 * ((n / 4 + n % 4) % 4)
def invSrFrom (n : Nat) : Nat := n % 4 + 4 * ((n / 4 + 4 - n % 4) % 4)

def srT (j p : Nat) : List (Nat × Nat) := [(j, at_ 4 false (srFrom (byteAt 4 false p)) (p % 4))]
def invSrT (j p : Nat) : List (Nat × Nat) := [(j, at_ 4 false (invSrFrom (byteAt 4 false p)) (p % 4))]

theorem shiftRows_check :
    check (lanes 64 9) srCfg (kExt srKs) shiftRows (linEnv qIns) (linPost 9 (qOuts (flat srT))) = true := by
  decide +kernel

theorem invShiftRows_check :
    check (lanes 64 9) srCfg (kExt srKs) invShiftRows (linEnv qIns) (linPost 9 (qOuts (flat invSrT))) = true := by
  decide +kernel

theorem shiftRows_ok {s : State} (hok : Ok srCfg s) (hks : MasksAt s.mem (s.gpr sb) srKs) :
    ∃ s', runBlock isa shiftRows s = some s' ∧
      (∀ j < 8, ∀ p < 64, (Q s' j).getLsbD p = termsXor (Q s) (srT j p)) ∧ Rest srCfg s s' :=
  lin_ok shiftRows_check (by decide +kernel) (by decide +kernel) (by decide) hok (Q s) (fun _ _ => rfl) (kExt_rel hks)

theorem invShiftRows_ok {s : State} (hok : Ok srCfg s) (hks : MasksAt s.mem (s.gpr sb) srKs) :
    ∃ s', runBlock isa invShiftRows s = some s' ∧
      (∀ j < 8, ∀ p < 64, (Q s' j).getLsbD p = termsXor (Q s) (invSrT j p)) ∧ Rest srCfg s s' :=
  lin_ok invShiftRows_check (by decide +kernel) (by decide +kernel) (by decide) hok (Q s) (fun _ _ => rfl) (kExt_rel hks)

theorem srFrom_lt : ∀ n < 16, srFrom n < 16 ∧ invSrFrom n < 16 := by decide

theorem bs_shiftRows {W W' : Nat → BitVec 64} {S : Nat → Spec.Aes.State}
    (h : ∀ j < 8, ∀ p < 64, (W' j).getLsbD p = termsXor W (srT j p)) (hS : BsRel W S) :
    BsRel W' fun b => Spec.Aes.shiftRows (S b) := fun j hj n hn k hk => by
  rw [h j hj _ (at_lt false hn hk)]
  simp only [srT, termsXor, List.foldr_cons, List.foldr_nil, Bool.xor_false, byteAt_at false hn hk, at_mod false n hk]
  rw [hS j hj _ (srFrom_lt n hn).1 k hk, Spec.Aes.shiftRows, getD_ofFn _ hn]
  rfl

theorem bs_invShiftRows {W W' : Nat → BitVec 64} {S : Nat → Spec.Aes.State}
    (h : ∀ j < 8, ∀ p < 64, (W' j).getLsbD p = termsXor W (invSrT j p)) (hS : BsRel W S) :
    BsRel W' fun b => Spec.Aes.invShiftRows (S b) := fun j hj n hn k hk => by
  rw [h j hj _ (at_lt false hn hk)]
  simp only [invSrT, termsXor, List.foldr_cons, List.foldr_nil, Bool.xor_false, byteAt_at false hn hk, at_mod false n hk]
  rw [hS j hj _ (srFrom_lt n hn).2 k hk, Spec.Aes.invShiftRows, getD_ofFn _ hn]
  rfl

/-! ## MixColumns and its inverse -/

theorem mixColumns_check :
    check (lanes 64 9) bsCfg (kExt []) mixColumns (linEnv qIns)
      (linPost 9 (qOuts (flat (mixT mcCoeffs 4 false)))) = true := by
  decide +kernel

theorem invMixColumns_check :
    check (lanes 64 9) bsCfg (kExt []) invMixColumns (linEnv qIns)
      (linPost 9 (qOuts (flat (mixT invMcCoeffs 4 false)))) = true := by
  decide +kernel

theorem mixColumns_ok {s : State} (hok : Ok bsCfg s) :
    ∃ s', runBlock isa mixColumns s = some s' ∧
      (∀ j < 8, ∀ p < 64, (Q s' j).getLsbD p = termsXor (Q s) (mixT mcCoeffs 4 false j p)) ∧ Rest bsCfg s s' :=
  lin_ok mixColumns_check (by decide +kernel) (by decide +kernel) (by decide) hok (Q s) (fun _ _ => rfl)
    (kExt_rel (ks := []) fun _ _ h => by cases h)

theorem invMixColumns_ok {s : State} (hok : Ok bsCfg s) :
    ∃ s', runBlock isa invMixColumns s = some s' ∧
      (∀ j < 8, ∀ p < 64, (Q s' j).getLsbD p = termsXor (Q s) (mixT invMcCoeffs 4 false j p)) ∧ Rest bsCfg s s' :=
  lin_ok invMixColumns_check (by decide +kernel) (by decide +kernel) (by decide) hok (Q s) (fun _ _ => rfl)
    (kExt_rel (ks := []) fun _ _ h => by cases h)

theorem bs_mixColumns {W W' : Nat → BitVec 64} {S : Nat → Spec.Aes.State}
    (h : ∀ j < 8, ∀ p < 64, (W' j).getLsbD p = termsXor W (mixT mcCoeffs 4 false j p)) (hS : BsRel W S) :
    BsRel W' fun b => Spec.Aes.mixColumns (S b) := hS.mixColumns h

theorem bs_invMixColumns {W W' : Nat → BitVec 64} {S : Nat → Spec.Aes.State}
    (h : ∀ j < 8, ∀ p < 64, (W' j).getLsbD p = termsXor W (mixT invMcCoeffs 4 false j p)) (hS : BsRel W S) :
    BsRel W' fun b => Spec.Aes.invMixColumns (S b) := hS.invMixColumns h

/-! ## AddRoundKey -/

/-- The round key's words, at `kp`. -/
def keyWord (s : State) (k : Nat) : BitVec 64 := s.mem.readW (wordAddr (s.gpr kp) k) 64

def arkT (j p : Nat) : List (Nat × Nat) := [(j, p), (8 + j, p)]

theorem addRoundKey_check :
    check (lanes 64 10) arkCfg (linExt 8) addRoundKey (linEnv qIns) (linPost 10 (qOuts (flat arkT))) = true := by
  decide +kernel

theorem addRoundKey_ok {s : State} (hok : Ok arkCfg s) :
    ∃ s', runBlock isa addRoundKey s = some s' ∧
      (∀ j < 8, ∀ p < 64, (Q s' j).getLsbD p = ((Q s j).getLsbD p ^^ (keyWord s j).getLsbD p)) ∧
      Rest arkCfg s s' := by
  let W : Nat → BitVec 64 := fun i => if i < 8 then Q s i else keyWord s (i - 8)
  obtain ⟨s', hs', hout, rest⟩ := lin_ok addRoundKey_check (by decide +kernel) (by decide +kernel) (by decide) hok W
    (fun j hj => ite_eq_left hj) (linExt_rel fun j hj => by
      have hj : j < 8 := hj
      refine ⟨by omega, ?_⟩
      simp only [W, show ¬ 8 + j < 8 by omega, ite_false, Nat.add_sub_cancel_left, keyWord]
      rfl)
  refine ⟨s', hs', fun j hj p hp => ?_, rest⟩
  rw [hout j hj p hp]
  simp only [arkT, termsXor, List.foldr_cons, List.foldr_nil, Bool.xor_false, W, hj, ite_true,
    show ¬ 8 + j < 8 by omega, ite_false, Nat.add_sub_cancel_left]

theorem bs_addRoundKey {W W' K : Nat → BitVec 64} {S : Nat → Spec.Aes.State} {rk : List Byte}
    (h : ∀ j < 8, ∀ p < 64, (W' j).getLsbD p = ((W j).getLsbD p ^^ (K j).getLsbD p)) (hS : BsRel W S)
    (hK : KeyRel K rk) : BsRel W' fun b => Spec.Aes.addRoundKey (S b) rk :=
  hS.addRoundKey hK h

end VG.Proof.Aes.RISCV64

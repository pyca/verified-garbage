module

public import VerifiedGarbage.Proof.SlhDsa.AArch64.Thash4Contract
public import VerifiedGarbage.Impl.SlhDsa.AArch64.Thash4
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Call
public import VerifiedGarbage.Proof.SlhDsa.Shake
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Sha3.Arith

-- separate module: it builds in parallel with the constant-time checks (`Thash4CT`).

/-!
# SLH-DSA on AArch64: `thash4`, correctness

`Thash4.thash4 n sha3` from a state satisfying `Thash4Pre n` ends with each
output `SHAKE256` of its message, the calling convention's registers kept,
and memory changed only in the outputs and the first `workUsed` bytes of
`work` (`correct`). The proof follows the code: the prologue (`pro_ok`), the
loop that absorbs a word of each message at a time with the invariant `Inv`
(`body_ok`), the padding, the last permutation, the extraction and the
restoring of the registers. The four states are two pairs of the two-way
permutation (`St4`, lane `i` of state `k` at `la p i k`), which
`Proof.Sha3.AArch64.Neon.X2.callAny_ok` permutes.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Thash4

open VG VG.AArch64
open VG.Impl.SlhDsa.AArch64.Thash4
open VG.Proof.Sha3 (byteOf xorAt xorByte Rep rep_nil rep_append byteOf_xorAt byteOf_xorByte ext_bytes getElem!_eq)
open VG.Proof.Sha3.AArch64 (Upd Mupd wp_addImm wp_subImm wp_movz wp_add wp_eor wp_ldr wp_str wp_nil
  eval_zero eval_nonzero)
open VG.Proof.Sha3.AArch64.Neon (PairAt wordAddr pairR)
open VG.Spec.Sha3 (bytesAt keccakF)
open VG.Proof.SlhDsa (finalState)
open VG.Proof.SlhDsa.AArch64 (Thash4Pre msg outAt thash4Changes workLen workUsed)

abbrev KState := Spec.Sha3.State

/-! ## Memory, byte by byte -/

theorem addOf (p : Addr) (a b : Nat) : p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Byte `j < 8` of the word at `a`. -/
theorem byte_readW (m : Mem) (a : Addr) {j : Nat} (hj : j < 8) :
    m (a + BitVec.ofNat 64 j) = (m.readW a 64).extractLsb' (8 * j) 8 := by
  rw [← Mem.extractLsb'_read m a (n := 8) hj]
  simp only [Mem.readW]
  rfl

/-- Byte `j < 8` of a word written. -/
theorem writeW_in (m : Mem) (a : Addr) (v : BitVec 64) {j : Nat} (hj : j < 8) :
    (m.writeW a v) (a + BitVec.ofNat 64 j) = v.extractLsb' (8 * j) 8 := by
  rw [byte_readW (m.writeW a v) a hj, Mem.readW_writeW_self64]

/-- A byte outside a word written. -/
theorem writeW_out (m : Mem) (a : Addr) (v : BitVec 64) {x : Addr} (h : 8 ≤ (x - a).toNat) :
    (m.writeW a v) x = m x :=
  Mem.write_apply (n := 8) (by omega_using [h])

/-- Two lanes with the same bytes. -/
theorem lane_ext {v w : BitVec 64} (h : ∀ j < 8, v.extractLsb' (8 * j) 8 = w.extractLsb' (8 * j) 8) :
    v = w := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  have := congrArg (·.getLsbD (b % 8)) (h (b / 8) (by omega_using [hb]))
  simp only [BitVec.getLsbD_extractLsb', show b % 8 < 8 by omega_using [], decide_true, Bool.true_and] at this
  rwa [show 8 * (b / 8) + b % 8 = b by omega_using []] at this

theorem readW_frame {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {a : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨a, 8⟩ r) : m'.readW a 64 = m.readW a 64 :=
  hf.readW (r := ⟨a, 8⟩) (by simp [Region.Contains]) hd (by decide)

/-! ## The four states

States `2p` and `2p + 1` are the pair at `p + 400 p`: lane `i` of state `k`
is the word at `la p i k`. -/

/-- The offset of lane `i` of state `k`. -/
abbrev lo (i k : Nat) : Nat := 400 * (k / 2) + 16 * i + 8 * (k % 2)

/-- Lane `i` of state `k` of the four at `p`. -/
abbrev la (p : Addr) (i k : Nat) : Addr := p + BitVec.ofNat 64 (lo i k)

/-- Byte `q` of state `k` of the four at `p`. -/
abbrev ba (p : Addr) (k q : Nat) : Addr := p + BitVec.ofNat 64 (lo (q / 8) k + q % 8)

/-- The four states at `p`. -/
def St4 (m : Mem) (p : Addr) (A : Nat → KState) : Prop :=
  ∀ i < 25, ∀ k < 4, m.readW (la p i k) 64 = (A k)[i]!

theorem lo_lt {i k : Nat} (hi : i < 25) (hk : k < 4) : lo i k + 8 ≤ 800 := by
  simp only [lo]; omega_using [hi, hk]

theorem la_byte (p : Addr) {i k j : Nat} (hj : j < 8) :
    la p i k + BitVec.ofNat 64 j = ba p k (8 * i + j) := by
  rw [la, addOf, ba, show (8 * i + j) / 8 = i by omega_using [hj], show (8 * i + j) % 8 = j by omega_using [hj]]

theorem st4_of_bytes {m : Mem} {p : Addr} {A : Nat → KState}
    (h : ∀ k < 4, ∀ q < 200, m (ba p k q) = byteOf (A k) q) : St4 m p A := fun i hi k hk =>
  lane_ext fun j hj => by
    rw [← byte_readW _ _ hj, la_byte _ hj, h k hk _ (by omega_using [hi, hj]),
      Proof.Sha3.byteOf_eq _ hi hj, getElem!_eq _ hi]

theorem byte_of_st4 {m : Mem} {p : Addr} {A : Nat → KState} (h : St4 m p A) {k q : Nat} (hk : k < 4)
    (hq : q < 200) : m (ba p k q) = byteOf (A k) q := by
  rw [byteOf, ← h (q / 8) (by omega_using [hq]) k hk, ← byte_readW _ _ (by omega_using []),
    la_byte _ (by omega_using []), show 8 * (q / 8) + q % 8 = q by omega_using []]

theorem ba_lt {k q : Nat} (hk : k < 4) (hq : q < 200) : lo (q / 8) k + q % 8 < 800 := by
  have := lo_lt (i := q / 8) (by omega_using [hq]) hk
  omega_using [this]

theorem st4_congr {m : Mem} {p : Addr} {A B : Nat → KState} (h : St4 m p A) (e : ∀ k < 4, A k = B k) :
    St4 m p B := fun i hi k hk => by rw [← e k hk]; exact h i hi k hk

/-- Memory that frames `rs` keeps the four states at `p` if none of `rs`
meets them. -/
theorem st4_frame {m m' : Mem} {p : Addr} {A : Nat → KState} (h : St4 m p A) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 800⟩ r) : St4 m' p A := fun i hi k hk => by
  rw [← h i hi k hk]
  exact readW_frame hf fun r hr => (hd r hr).sub_left (Offset.sub_base p (lo_lt hi hk))

/-- Writing lane `i` of state `k`, its bytes those of the lane XORed with
`bs`. -/
theorem st4_xorLane {m : Mem} {p : Addr} {A : Nat → KState} (h : St4 m p A) {i k : Nat}
    (hi : i < 25) (hk : k < 4) {v : BitVec 64} {bs : List Byte} (hbs : bs.length = 8)
    (hv : ∀ d < 8, v.extractLsb' (8 * d) 8 = m (la p i k + BitVec.ofNat 64 d) ^^^ bs.getD d 0) :
    St4 (m.writeW (la p i k) v) p (fun k' => if k' = k then xorAt (A k') (8 * i) bs else A k') := by
  refine st4_of_bytes fun k' hk' q hq => ?_
  by_cases c : k' = k ∧ q / 8 = i
  · obtain ⟨rfl, hqi⟩ := c
    have e : ba p k' q = la p i k' + BitVec.ofNat 64 (q % 8) := by
      rw [la_byte _ (by omega_using []), ← hqi, show 8 * (q / 8) + q % 8 = q by omega_using []]
    rw [e, writeW_in _ _ _ (by omega_using []), hv _ (by omega_using []), la_byte _ (by omega_using []),
      ← hqi, show 8 * (q / 8) + q % 8 = q by omega_using [], byte_of_st4 h hk hq, ite_eq_left rfl,
      byteOf_xorAt _ _ _ hq, hbs, ite_eq_left (by omega_using [hqi]), show q - 8 * (q / 8) = q % 8 by omega_using []]
  · have hne : 8 ≤ (ba p k' q - la p i k).toNat := by
      have h1 := ba_lt hk' hq
      have h2 := lo_lt hi hk
      simp only [ba, la, lo] at h1 h2 ⊢
      rw [Offset.sub_toNat' _ (by omega_using [h1, h2, hk, hk', hq, hi]) (by omega_using [h1, h2, hk, hk', hq, hi])]
      split <;> rename_i hs <;> omega_using [c, hi, hk, hk', hq, hs]
    rw [writeW_out _ _ _ hne, byte_of_st4 h hk' hq]
    by_cases e : k' = k
    · subst e
      rw [ite_eq_left rfl, byteOf_xorAt _ _ _ hq, hbs, ite_eq_right (by omega_using [c])]
    · rw [ite_eq_right e]

theorem la0 (p : Addr) (i : Nat) : la p i 0 = p + BitVec.ofNat 64 (16 * i) := by
  rw [la, show lo i 0 = 16 * i by unfold lo; omega_using []]
theorem la1 (p : Addr) (i : Nat) : la p i 1 = p + BitVec.ofNat 64 (16 * i + 8) := by
  rw [la, show lo i 1 = 16 * i + 8 by unfold lo; omega_using []]
theorem la2 (p : Addr) (i : Nat) : la p i 2 = p + BitVec.ofNat 64 400 + BitVec.ofNat 64 (16 * i) := by
  rw [la, addOf, show lo i 2 = 400 + 16 * i by unfold lo; omega_using []]
theorem la3 (p : Addr) (i : Nat) : la p i 3 = p + BitVec.ofNat 64 400 + BitVec.ofNat 64 (16 * i + 8) := by
  rw [la, addOf, show lo i 3 = 400 + (16 * i + 8) by unfold lo; omega_using []]

/-- The four states as the two pairs of the two-way permutation. -/
theorem pairs_of_st4 {m : Mem} {p : Addr} {A : Nat → KState} (h : St4 m p A) :
    PairAt m p (A 0) (A 1) ∧ PairAt m (p + BitVec.ofNat 64 400) (A 2) (A 3) :=
  ⟨Proof.Sha3.AArch64.Neon.X2.pairAt_of_words (fun i hi => by rw [← la0]; exact h i hi 0 (by decide))
      (fun i hi => by rw [← la1]; exact h i hi 1 (by decide)),
    Proof.Sha3.AArch64.Neon.X2.pairAt_of_words (fun i hi => by rw [← la2]; exact h i hi 2 (by decide))
      (fun i hi => by rw [← la3]; exact h i hi 3 (by decide))⟩

theorem st4_of_pairs {m : Mem} {p : Addr} {A : Nat → KState} (h₀ : PairAt m p (A 0) (A 1))
    (h₁ : PairAt m (p + BitVec.ofNat 64 400) (A 2) (A 3)) : St4 m p A := by
  intro i hi k hk
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_using [hk]) with rfl | rfl | rfl | rfl
  · rw [la0]; exact Proof.Sha3.AArch64.Neon.X2.word0 h₀ hi
  · rw [la1]; exact Proof.Sha3.AArch64.Neon.X2.word1 h₀ hi
  · rw [la2]; exact Proof.Sha3.AArch64.Neon.X2.word0 h₁ hi
  · rw [la3]; exact Proof.Sha3.AArch64.Neon.X2.word1 h₁ hi

/-! ## Steps -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mov' {d n : Reg} (k : ∀ s', Upd s s' d (s.gpr n) → WP isa (.block is) s' Q) :
    WP isa (.block (mov d n :: is)) s Q :=
  wp_addImm (by decide) fun s' u => k s' (by simpa using u)

theorem wp_movi0 {d : VReg} (k : ∀ s', Proof.MlKem.AArch64.VUpd s s' d 0 → WP isa (.block is) s' Q) :
    WP isa (.block (.vop (.movi0 d) :: is)) s Q :=
  Proof.MlKem.AArch64.wp_vop rfl k

/-- `movz x_d, #imm, lsl #48`. -/
theorem wp_movz3 {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm.setWidth 64 <<< 48) → WP isa (.block is) s' Q) :
    WP isa (.block (.movz .x d imm 3 :: is)) s Q :=
  Proof.Sha3.AArch64.WP.cons (s' := s.write .x d (imm.setWidth 64 <<< 48)) (by simp [reduceExec, Size.bits])
    (k _ (Upd.write64 _ _ _))

end

/-! ## The entry state -/

section
variable (σ : State)

abbrev inp : Addr := σ.gpr .x0
abbrev str : Nat := (σ.gpr .x1).toNat
abbrev L : Nat := (σ.gpr .x2).toNat
abbrev W : Addr := σ.gpr .x4
abbrev laneP (k : Nat) : Addr := inp σ + BitVec.ofNat 64 (k * str σ)
abbrev lanesR : Region := ⟨inp σ, 4 * str σ⟩
abbrev workR : Region := ⟨W σ, workLen⟩
/-- The number of words of each message. -/
abbrev nw : Nat := L σ / 8

end

variable {n : Nat} {σ : State}

theorem work_fit' (hp : Thash4Pre n σ) : (W σ).toNat + 1024 ≤ 2 ^ 64 := hp.work_fit

theorem wr_work (hp : Thash4Pre n σ) {s : State} (hw : s.wr = σ.wr) {d k : Nat} (h : d + k ≤ workLen) :
    InRegions s.wr (W σ + BitVec.ofNat 64 d) k :=
  ⟨workR σ, by rw [hw, hp.wr]; simp, Offset.contains_base _ h (by simp [workLen] at h ⊢; omega_using [h])⟩

theorem rw_work (hp : Thash4Pre n σ) {s : State} (hw : s.wr = σ.wr) {d k : Nat} (h : d + k ≤ workLen) :
    InRegions (s.rd ++ s.wr) (W σ + BitVec.ofNat 64 d) k :=
  let ⟨r, hr, hc⟩ := wr_work hp hw h; ⟨r, List.mem_append_right _ hr, hc⟩

theorem str_lt (hp : Thash4Pre n σ) : 4 * str σ ≤ 2 ^ 64 := by
  have h1 := hp.lanes_fit
  show 4 * (σ.gpr .x1).toNat ≤ 2 ^ 64
  omega_using [h1]

theorem kstr_le {k : Nat} (hk : k < 4) : k * str σ + str σ ≤ 4 * str σ := by
  have := Nat.mul_le_mul_right (str σ) (show k + 1 ≤ 4 by omega_using [hk])
  rw [Nat.succ_mul] at this; exact this

theorem laneP_off (k d : Nat) : laneP σ k + BitVec.ofNat 64 d = inp σ + BitVec.ofNat 64 (k * str σ + d) :=
  addOf _ _ _

theorem laneP_zero : laneP σ 0 = σ.gpr .x0 := by simp [laneP, inp]

theorem laneP_succ (k : Nat) : laneP σ (k + 1) = laneP σ k + σ.gpr .x1 := by
  simp only [laneP, inp, str]
  rw [Nat.succ_mul, ← addOf, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem rd_lane (hp : Thash4Pre n σ) {s : State} (hw : s.wr = σ.wr) {k d : Nat} (hk : k < 4)
    (hd : d + 8 ≤ str σ) : InRegions (s.rd ++ s.wr) (laneP σ k + BitVec.ofNat 64 d) 8 := by
  have := str_lt hp
  refine ⟨lanesR σ, List.mem_append_right _ (by rw [hw, hp.wr]; simp), ?_⟩
  have h2 := kstr_le (σ := σ) hk
  rw [laneP_off]
  exact Offset.contains_base _ (by omega_using [hd, h2]) (by omega_using [hd, h2, this])

theorem wr_lane (hp : Thash4Pre n σ) {s : State} (hw : s.wr = σ.wr) {k d : Nat} (hk : k < 4)
    (hd : d + 8 ≤ str σ) : InRegions s.wr (laneP σ k + BitVec.ofNat 64 d) 8 := by
  have := str_lt hp
  refine ⟨lanesR σ, by rw [hw, hp.wr]; simp, ?_⟩
  have h2 := kstr_le (σ := σ) hk
  rw [laneP_off]
  exact Offset.contains_base _ (by omega_using [hd, h2]) (by omega_using [hd, h2, this])

/-- A byte of the lanes, framed by the work. -/
theorem lane_byte {m : Mem} (hp : Thash4Pre n σ) (hf : Frame [⟨W σ, workUsed⟩] σ.mem m) {a : Addr}
    (ha : (lanesR σ).Contains a 1) : m a = σ.mem a :=
  hf a fun r hr hc => by
    rw [List.mem_singleton] at hr; subst hr
    exact hp.lanes_work a ha (Region.sub_prefix (by decide) a hc)

theorem msg_byte (k : Nat) {j : Nat} (hj : j < L σ) :
    (msg σ k).getD j 0 = σ.mem (laneP σ k + BitVec.ofNat 64 j) := by
  simp [msg, bytesAt, hj]

theorem length_msg (k : Nat) : (msg σ k).length = L σ := by simp [msg, bytesAt]

theorem len_eq (hp : Thash4Pre n σ) : L σ = 8 * nw σ := by
  have h := hp.len_mod
  show (σ.gpr .x2).toNat = 8 * ((σ.gpr .x2).toNat / 8)
  omega_using [h]

/-! ## The invariant of the loop -/

/-- After `w` words of each message. -/
structure Inv (σ : State) (w : Nat) (s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  x19 : s.gpr .x19 = W σ
  ptr : ∀ k < 4, s.gpr (lanePtr k) = laneP σ k
  pos : s.gpr .x24 = BitVec.ofNat 64 (8 * w)
  left : s.gpr .x25 = BitVec.ofNat 64 (L σ - 8 * w)
  row : s.gpr .x26 = W σ + BitVec.ofNat 64 (16 * (w % 17))
  cnt : s.gpr .x27 = BitVec.ofNat 64 (17 - w % 17)
  st : St4 s.mem (W σ) (fun k => Rep 136 ((msg σ k).take (8 * w)))
  frame : Frame [⟨W σ, workUsed⟩] σ.mem s.mem
  sv : ∀ p ∈ saved, s.mem.readW (W σ + BitVec.ofNat 64 p.2) 64 = σ.gpr p.1
  x28 : s.gpr .x28 = σ.gpr .x28
  x30 : s.gpr .x30 = σ.gpr .x30
  vk : ∀ r ∈ preservedV, (s.v r).extractLsb' 0 64 = (σ.v r).extractLsb' 0 64

/-! ## The prologue -/

/-- The saved register `i`. -/
def sreg (i : Nat) : Reg := [Reg.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27].getD i .x19

theorem saved_eq : saved = (List.range 9).map fun i => (sreg i, oSave + 8 * i) := rfl

theorem save_eq : save = (List.range 9).map fun i => .str .x (sreg i) .x4 (oSave + 8 * i) := rfl

theorem saves_ok (hp : Thash4Pre n σ) : ∀ j ≤ 9, ∀ t : State, t.gpr .x4 = W σ → t.wr = σ.wr →
    WP isa (.block ((List.range j).map fun i => .str .x (sreg i) .x4 (oSave + 8 * i))) t (fun t' =>
      t'.gpr = t.gpr ∧ t'.v = t.v ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.sp = t.sp ∧
      (∀ i < j, t'.mem.readW (W σ + BitVec.ofNat 64 (oSave + 8 * i)) 64 = t.gpr (sreg i)) ∧
      Frame [⟨W σ + BitVec.ofNat 64 oSave, 72⟩] t.mem t'.mem) := by
  have hW := work_fit' hp
  intro j
  induction j with
  | zero => intro _ t _ _; exact wp_nil ⟨rfl, rfl, rfl, rfl, rfl, fun i hi => absurd hi (by omega_using []), Frame.refl _ _⟩
  | succ j ih =>
    intro hj t h4 hw
    rw [List.range_succ, List.map_append]
    refine WP.block_append (WP.mono (ih (by omega_using [hj]) t h4 hw) fun t₁ ⟨g₁, v₁, r₁, w₁, p₁, b₁, f₁⟩ => ?_)
    refine wp_str (a := W σ + BitVec.ofNat 64 (oSave + 8 * j)) ⟨by simp only [oSave]; omega_using [], by simp only [oSave]; omega_using [hj]⟩
      (by rw [g₁, h4]) (wr_work hp (by rw [w₁, hw]) (by simp [oSave, workLen]; omega_using [hj])) fun t₂ m₂ => wp_nil ?_
    refine ⟨by rw [m₂.gpr, g₁], by rw [m₂.vec, v₁], by rw [m₂.rd, r₁], by rw [m₂.wr, w₁], by rw [m₂.sp, p₁],
      fun i hi => ?_, ?_⟩
    · rw [m₂.mem, g₁]
      by_cases c : i < j
      · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega_using [c]) (by simp only [oSave]; omega_using [hj, hW, c])
          (by simp only [oSave]; omega_using [hj, hW, c])) (by decide), b₁ i c]
      · obtain rfl : i = j := by omega_using [hi, c]
        rw [Mem.readW_writeW_self64]
    · rw [m₂.mem]
      exact f₁.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by simp only [oSave]; omega_using []) (by simp only [oSave]; omega_using [hj])
        (by simp only [oSave]; omega_using [hW]))

theorem byteOf_zero (q : Nat) : byteOf Spec.Sha3.zero q = 0 := by
  have : (Spec.Sha3.zero)[q / 8]! = 0 := by
    by_cases h : q / 8 < 25
    · rw [getElem!_pos Spec.Sha3.zero (q / 8) h]; simp [Spec.Sha3.zero]
    · rw [getElem!_neg Spec.Sha3.zero (q / 8) h]; rfl
  rw [byteOf, this]; simp

/-- The rows of the states zeroed. -/
theorem zeros_ok (hp : Thash4Pre n σ) : ∀ j ≤ 50, ∀ t : State, t.gpr .x19 = W σ → t.wr = σ.wr → t.v .v16 = 0 →
    WP isa (.block ((List.range j).map fun i => .strq .v16 .x19 (16 * i))) t (fun t' => t'.gpr = t.gpr ∧
      t'.v = t.v ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.sp = t.sp ∧
      (∀ q < 16 * j, t'.mem (W σ + BitVec.ofNat 64 q) = 0) ∧ Frame [⟨W σ, 800⟩] t.mem t'.mem) := by
  have hW := work_fit' hp
  intro j
  induction j with
  | zero => intro _ t _ _ _; exact wp_nil ⟨rfl, rfl, rfl, rfl, rfl, fun q hq => absurd hq (by omega_using []), Frame.refl _ _⟩
  | succ j ih =>
    intro hj t h19 hw h0
    rw [List.range_succ, List.map_append]
    refine WP.block_append (WP.mono (ih (by omega_using [hj]) t h19 hw h0) fun t₁ ⟨g₁, v₁, r₁, w₁, p₁, b₁, f₁⟩ => ?_)
    refine Proof.MlKem.AArch64.wp_strq (a := W σ + BitVec.ofNat 64 (16 * j)) ⟨by omega_using [], by omega_using [hj]⟩
      (by rw [g₁, h19]) (wr_work hp (by rw [w₁, hw]) (by simp [workLen]; omega_using [hj])) fun t₂ m₂ => wp_nil ?_
    refine ⟨by rw [m₂.gpr, g₁], by rw [m₂.v, v₁], by rw [m₂.rd, r₁], by rw [m₂.wr, w₁], by rw [m₂.sp, p₁],
      fun q hq => ?_, ?_⟩
    · rw [m₂.mem, v₁, h0]
      have e := Offset.sub_toNat' (W σ) (d := 16 * j) (e := q) (by omega_using [hq, hj]) (by omega_using [hq, hj])
      by_cases c : q < 16 * j
      · rw [Mem.write_apply (by rw [e]; split <;> rename_i hs <;> omega_using [c, hs, hq, hj]), b₁ q c]
      · have hlt : (W σ + BitVec.ofNat 64 q - (W σ + BitVec.ofNat 64 (16 * j))).toNat < 16 := by
          rw [e]; split <;> rename_i hs <;> omega_using [c, hs, hq, hj]
        simp only [Mem.write, hlt, ite_true]
        simp
    · rw [m₂.mem]
      exact f₁.write (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))

theorem pro_eq : pro = save ++ ([mov .x19 .x4, mov .x20 .x0, .add .x .x21 .x20 .x1, .add .x .x22 .x21 .x1,
    .add .x .x23 .x22 .x1, .movz .x .x24 0 0, mov .x25 .x2, mov .x26 .x19, .movz .x .x27 17 0] : List Instr) ++
    (.vop (.movi0 .v16) :: (List.range 50).map fun i => .strq .v16 .x19 (16 * i)) := rfl

theorem mem_saved {p : Reg × Nat} (h : p ∈ saved) : ∃ i < 9, p = (sreg i, oSave + 8 * i) := by
  rw [saved_eq, List.mem_map] at h
  obtain ⟨i, hi, rfl⟩ := h
  exact ⟨i, List.mem_range.mp hi, rfl⟩

theorem slot_disj (hp : Thash4Pre n σ) {i : Nat} (hi : i < 9) :
    Region.Disjoint ⟨W σ + BitVec.ofNat 64 (oSave + 8 * i), 8⟩ ⟨W σ, 936⟩ :=
  have hW := work_fit' hp
  Offset.disjoint_base _ (by simp only [oSave]; omega_using []) (by simp only [oSave]; omega_using [hi, hW])

theorem pro_ok (hp : Thash4Pre n σ) : WP isa (.block pro) σ (Inv σ 0) := by
  have hW := work_fit' hp
  rw [pro_eq, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (saves_ok hp 9 (Nat.le_refl _) σ rfl rfl) fun s₀ ⟨g₀, v₀, r₀, w₀, p₀, b₀, f₀⟩ => ?_
  refine wp_mov' fun s₁ u₁ => ?_
  have a19 : s₁.gpr .x19 = W σ := by rw [u₁.gpr, g₀]
  refine wp_mov' fun s₂ u₂ => ?_
  have a20 : s₂.gpr .x20 = laneP σ 0 := by rw [u₂.gpr, u₁.other _ (by decide), g₀, laneP_zero]
  refine wp_add fun s₃ u₃ => ?_
  have a21 : s₃.gpr .x21 = laneP σ 1 := by
    rw [u₃.gpr, a20, u₂.other _ (by decide), u₁.other _ (by decide), g₀, laneP_succ (σ := σ) 0]
  refine wp_add fun s₄ u₄ => ?_
  have a22 : s₄.gpr .x22 = laneP σ 2 := by
    rw [u₄.gpr, a21, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), g₀, laneP_succ (σ := σ) 1]
  refine wp_add fun s₅ u₅ => ?_
  have a23 : s₅.gpr .x23 = laneP σ 3 := by
    rw [u₅.gpr, a22, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), g₀, laneP_succ (σ := σ) 2]
  refine wp_movz fun s₆ u₆ => wp_mov' fun s₇ u₇ => wp_mov' fun s₈ u₈ => wp_movz fun s₉ u₉ => wp_nil ?_
  -- the registers after the moves
  have k5 : ∀ r, r ≠ .x24 → r ≠ .x25 → r ≠ .x26 → r ≠ .x27 → s₉.gpr r = s₅.gpr r := fun r h24 h25 h26 h27 => by
    rw [u₉.other _ h27, u₈.other _ h26, u₇.other _ h25, u₆.other _ h24]
  have k0 : ∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → s₅.gpr r = σ.gpr r :=
    fun r h19 h20 h21 h22 h23 => by
      rw [u₅.other _ h23, u₄.other _ h22, u₃.other _ h21, u₂.other _ h20, u₁.other _ h19, g₀]
  have m₉ : s₉.mem = s₀.mem := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have v₉ : s₉.v = σ.v := by
    rw [u₉.vec, u₈.vec, u₇.vec, u₆.vec, u₅.vec, u₄.vec, u₃.vec, u₂.vec, u₁.vec, v₀]
  have rd₉ : s₉.rd = σ.rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, r₀]
  have wr₉ : s₉.wr = σ.wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, w₀]
  have sp₉ : s₉.sp = σ.sp := by rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, p₀]
  have x19₉ : s₉.gpr .x19 = W σ := by
    rw [k5 _ (by decide) (by decide) (by decide) (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), a19]
  refine wp_movi0 fun s₁₀ u₁₀ => ?_
  refine WP.mono (zeros_ok hp 50 (Nat.le_refl _) s₁₀ (by rw [u₁₀.gpr, x19₉]) (by rw [u₁₀.wr, wr₉]) u₁₀.v)
    fun t ⟨gt, vt, rt, wt, pt, bt, ft⟩ => ?_
  have gT : ∀ r, t.gpr r = s₉.gpr r := fun r => by rw [gt, u₁₀.gpr]
  refine ⟨by rw [rt, u₁₀.rd, rd₉], by rw [wt, u₁₀.wr, wr₉], by rw [pt, u₁₀.sp, sp₉], by rw [gT, x19₉],
    fun k hk => ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun p hp' => ?_, ?_, ?_, fun r hr => ?_⟩
  · rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_using [hk]) with rfl | rfl | rfl | rfl
    · show t.gpr .x20 = _; rw [gT, k5 _ (by decide) (by decide) (by decide) (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.other _ (by decide), a20]
    · show t.gpr .x21 = _; rw [gT, k5 _ (by decide) (by decide) (by decide) (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), a21]
    · show t.gpr .x22 = _; rw [gT, k5 _ (by decide) (by decide) (by decide) (by decide), u₅.other _ (by decide), a22]
    · show t.gpr .x23 = _; rw [gT, k5 _ (by decide) (by decide) (by decide) (by decide), a23]
  · rw [gT, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr]; rfl
  · rw [gT, u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide),
      k0 _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp
  · rw [gT, u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), a19]
    simp
  · rw [gT, u₉.gpr]; rfl
  · refine st4_of_bytes fun k hk q hq => ?_
    rw [bt _ (by have := ba_lt hk hq; omega_using [this])]
    simp [rep_nil, byteOf_zero]
  · rw [u₁₀.mem, m₉] at ft
    exact (f₀.sub fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by simp only [oSave, workUsed]; omega_using [])⟩).trans
      (ft.sub fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩)
  · obtain ⟨i, hi, rfl⟩ := mem_saved hp'
    rw [readW_frame ft fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact (slot_disj hp hi).sub_right (Region.sub_prefix (by decide)), u₁₀.mem, m₉, b₀ i hi]
  · rw [gT, k5 _ (by decide) (by decide) (by decide) (by decide), k0 _ (by decide) (by decide) (by decide)
      (by decide) (by decide)]
  · rw [gT, k5 _ (by decide) (by decide) (by decide) (by decide), k0 _ (by decide) (by decide) (by decide)
      (by decide) (by decide)]
  · have hne : r ≠ .v16 := by intro e; subst e; revert hr; decide
    rw [vt, u₁₀.other _ hne, v₉]

/-! ## A row -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_ldp2 {t1 t2 n : Reg} {off : Nat} {a : Addr} (ht : t1 ≠ t2) (ho : off % 8 = 0 ∧ off ≤ 504)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (h₁ : InRegions (s.rd ++ s.wr) a 8)
    (h₂ : InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 8) 8)
    (k : ∀ s₁ s₂, Upd s s₁ t1 (s.mem.readW a 64) → Upd s₁ s₂ t2 (s.mem.readW (a + BitVec.ofNat 64 8) 64) →
      WP isa (.block is) s₂ Q) :
    WP isa (.block (.ldp t1 t2 n off :: is)) s Q := by
  refine Proof.Sha3.AArch64.WP.cons (s' := (s.write .x t1 (s.mem.readW a 64)).write .x t2
    (s.mem.readW (a + BitVec.ofNat 64 8) 64)) ?_ (k _ _ (Upd.write64 _ _ _) (Upd.write64 _ _ _))
  have h₂' : InRegions (s.rd ++ s.wr) (a + 8) 8 := h₂
  simp only [reduceExec, ht, ne_eq, not_false_eq_true, ho, and_self, ite_true, ha, State.load, h₁, h₂',
    Option.bind_some, Option.map_some, Mem.readW]
  rfl

theorem wp_stp2 {t1 t2 n : Reg} {off : Nat} {a : Addr} (ho : off % 8 = 0 ∧ off ≤ 504)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (h₁ : InRegions s.wr a 8) (h₂ : InRegions s.wr (a + BitVec.ofNat 64 8) 8)
    (k : ∀ s', Mupd s s' ((s.mem.writeW a (s.gpr t1)).writeW (a + BitVec.ofNat 64 8) (s.gpr t2)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.stp t1 t2 n off :: is)) s Q := by
  refine Proof.Sha3.AArch64.WP.cons
    (s' := { s with mem := (s.mem.writeW a (s.gpr t1)).writeW (a + BitVec.ofNat 64 8) (s.gpr t2) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  have h₂' : InRegions s.wr (a + 8) 8 := h₂
  simp only [reduceExec, ho, and_self, ite_true, ha, State.store, h₁, h₂', Option.bind_some, Mem.writeW,
    State.read]
  rfl

end

/-- The 8 bytes of message `k` after its first `8 w`. -/
abbrev chunk8 (σ : State) (k w : Nat) : List Byte := ((msg σ k).drop (8 * w)).take 8

theorem chunk8_getD (k w : Nat) {d : Nat} (hd : d < 8) :
    (chunk8 σ k w).getD d 0 = (msg σ k).getD (8 * w + d) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop, hd]

theorem length_chunk8 (k : Nat) {w : Nat} (hw : 8 * w + 8 ≤ L σ) : (chunk8 σ k w).length = 8 := by
  simp [length_msg]; omega_using [hw]

/-- Word `w` of message `k`, as it is in memory framed by the work. -/
theorem msg_word (hp : Thash4Pre n σ) {m : Mem} (hf : Frame [⟨W σ, workUsed⟩] σ.mem m) {k w : Nat} (hk : k < 4)
    (hw8 : 8 * w + 8 ≤ L σ) {d : Nat} (hd : d < 8) :
    (m.readW (laneP σ k + BitVec.ofNat 64 (8 * w)) 64).extractLsb' (8 * d) 8 = (chunk8 σ k w).getD d 0 := by
  have hle : L σ ≤ str σ := hp.len_le
  have h2 := kstr_le (σ := σ) hk
  have := str_lt hp
  rw [← byte_readW _ _ hd, addOf, chunk8_getD _ _ hd, msg_byte _ (by omega_using [hd, hw8])]
  refine lane_byte hp hf ?_
  rw [laneP_off]
  exact Offset.contains_base _ (by omega_using [hd, hw8, hle, h2]) (by omega_using [hd, hw8, hle, h2, this])

/-- Lane `r` of state `k` XORed with word `w` of message `k`. -/
theorem xorWord (hp : Thash4Pre n σ) {m m' : Mem} (hf : Frame [⟨W σ, workUsed⟩] σ.mem m') {A : Nat → KState}
    (h : St4 m (W σ) A) {r k w : Nat} (hr : r < 25) (hk : k < 4) (hw8 : 8 * w + 8 ≤ L σ) {x y : BitVec 64}
    (hx : x = m.readW (la (W σ) r k) 64) (hy : y = m'.readW (laneP σ k + BitVec.ofNat 64 (8 * w)) 64) :
    St4 (m.writeW (la (W σ) r k) (x ^^^ y)) (W σ)
      (fun k' => if k' = k then xorAt (A k') (8 * r) (chunk8 σ k w) else A k') :=
  st4_xorLane h hr hk (length_chunk8 k hw8) fun d hd => by
    rw [BitVec.extractLsb'_xor, hx, hy, ← byte_readW _ _ hd, msg_word hp hf hk hw8 hd]

theorem lanePtr_ne {k : Nat} (hk : k < 4) : lanePtr k ≠ .x9 ∧ lanePtr k ≠ .x10 ∧ lanePtr k ≠ .x11 ∧
    lanePtr k ≠ .x12 ∧ lanePtr k ≠ .x24 ∧ lanePtr k ≠ .x25 ∧ lanePtr k ≠ .x26 ∧ lanePtr k ≠ .x27 ∧
    lanePtr k ≠ .x19 := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_using [hk]) with rfl | rfl | rfl | rfl <;> decide

theorem la_pair {p r : Nat} (hp2 : p < 2) (P : Addr) :
    P + BitVec.ofNat 64 (16 * r) + BitVec.ofNat 64 (oPair1 * p) = la P r (2 * p) ∧
    P + BitVec.ofNat 64 (16 * r) + BitVec.ofNat 64 (oPair1 * p) + BitVec.ofNat 64 8 = la P r (2 * p + 1) := by
  refine ⟨?_, ?_⟩
  · rw [addOf, la, show lo r (2 * p) = 16 * r + oPair1 * p by unfold lo oPair1; omega_using [hp2]]
  · rw [addOf, addOf, ← Nat.add_assoc, la, show lo r (2 * p + 1) = 16 * r + oPair1 * p + 8 by unfold lo oPair1; omega_using [hp2]]

/-- The two states of pair `p` get their messages' next words XORed into
lane `r`. -/
theorem pair_ok (hp : Thash4Pre n σ) {p : Nat} (hp2 : p < 2) {w r : Nat} (hw8 : 8 * w + 8 ≤ L σ) (hr : r < 17)
    {A : Nat → KState} {t : State} (hwr : t.wr = σ.wr) (h26 : t.gpr .x26 = W σ + BitVec.ofNat 64 (16 * r))
    (hptr : ∀ k < 4, t.gpr (lanePtr k) = laneP σ k) (h24 : t.gpr .x24 = BitVec.ofNat 64 (8 * w))
    (hst : St4 t.mem (W σ) A) (hf : Frame [⟨W σ, workUsed⟩] σ.mem t.mem) :
    WP isa (.block (xorPair p)) t fun t' => (∀ g, g ≠ .x9 → g ≠ .x10 → g ≠ .x11 → g ≠ .x12 → t'.gpr g = t.gpr g) ∧
      t'.v = t.v ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.sp = t.sp ∧
      St4 t'.mem (W σ) (fun k' => if k' = 2 * p + 1 then xorAt (if k' = 2 * p then xorAt (A k') (8 * r) (chunk8 σ (2 * p) w)
          else A k') (8 * r) (chunk8 σ (2 * p + 1) w)
        else if k' = 2 * p then xorAt (A k') (8 * r) (chunk8 σ (2 * p) w) else A k') ∧
      Frame [⟨W σ, 800⟩] t.mem t'.mem := by
  have hW := work_fit' hp
  have hle : L σ ≤ str σ := hp.len_le
  have k0 : 2 * p < 4 := by omega_using [hp2]
  have k1 : 2 * p + 1 < 4 := by omega_using [hp2]
  obtain ⟨n0, n0', n0'', -, n0₂₄, -, n0₂₆, -⟩ := lanePtr_ne k0
  obtain ⟨n1, n1', n1'', -, n1₂₄, -, n1₂₆, -⟩ := lanePtr_ne k1
  obtain ⟨ea, eb⟩ := la_pair (r := r) hp2 (W σ)
  have eb' : la (W σ) r (2 * p) + BitVec.ofNat 64 8 = la (W σ) r (2 * p + 1) := by rw [← ea]; exact eb
  have hoff : lo r (2 * p) + 8 ≤ 800 := lo_lt (by omega_using [hr]) k0
  have hoff' : lo r (2 * p + 1) + 8 ≤ 800 := lo_lt (by omega_using [hr]) k1
  unfold xorPair
  refine wp_add fun s₁ u₁ => wp_ldr (a := laneP σ (2 * p) + BitVec.ofNat 64 (8 * w)) ⟨by decide, by decide⟩
    (by rw [u₁.gpr, hptr _ k0, h24, BitVec.add_zero]) (by rw [u₁.rd, u₁.wr]; exact rd_lane hp hwr k0 (by omega_using [hw8, hle]))
    fun s₂ u₂ => wp_add fun s₃ u₃ => wp_ldr (a := laneP σ (2 * p + 1) + BitVec.ofNat 64 (8 * w)) ⟨by decide, by decide⟩
    (by rw [u₃.gpr, u₂.other _ n1, u₁.other _ n1, hptr _ k1, u₂.other _ (by decide), u₁.other _ (by decide), h24,
      BitVec.add_zero]) (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact rd_lane hp hwr k1 (by omega_using [hw8, hle]))
    fun s₄ u₄ => wp_ldp2 (a := la (W σ) r (2 * p)) (by decide) ⟨by unfold oPair1; omega_using [], by unfold oPair1; omega_using [hp2]⟩
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h26, ea])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; rw [la]; exact rw_work hp hwr (by simp only [workLen]; omega_using [hoff]))
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, eb']; rw [la]; exact rw_work hp hwr (by simp only [workLen]; omega_using [hoff']))
    fun s₅ s₆ u₅ u₆ => wp_eor fun s₇ u₇ => wp_eor fun s₈ u₈ => wp_stp2 (a := la (W σ) r (2 * p))
    ⟨by unfold oPair1; omega_using [], by unfold oPair1; omega_using [hp2]⟩
    (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h26, ea])
    (by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; rw [la]; exact wr_work hp hwr (by simp only [workLen]; omega_using [hoff]))
    (by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, eb']; rw [la]; exact wr_work hp hwr (by simp only [workLen]; omega_using [hoff']))
    fun s₉ m₉ => wp_nil ?_
  have mem₈ : s₈.mem = t.mem := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have x11 : s₈.gpr .x11 = t.mem.readW (la (W σ) r (2 * p)) 64 ^^^ t.mem.readW (laneP σ (2 * p) + BitVec.ofNat 64 (8 * w)) 64 := by
    rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have x12 : s₈.gpr .x12 = t.mem.readW (la (W σ) r (2 * p + 1)) 64 ^^^ t.mem.readW (laneP σ (2 * p + 1) + BitVec.ofNat 64 (8 * w)) 64 := by
    rw [u₈.gpr, u₇.other _ (by decide), u₆.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.gpr, u₃.mem, u₂.mem, u₁.mem, ← ea, eb, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hc0 : (⟨W σ, workUsed⟩ : Region).Contains (la (W σ) r (2 * p)) (64 / 8) :=
    Offset.contains_base _ (by simp only [workUsed]; omega_using [hoff]) (by omega_using [hoff])
  have hc1 : (⟨W σ, workUsed⟩ : Region).Contains (la (W σ) r (2 * p + 1)) (64 / 8) :=
    Offset.contains_base _ (by simp only [workUsed]; omega_using [hoff']) (by omega_using [hoff'])
  have st1 := xorWord (r := r) (k := 2 * p) (w := w) hp hf hst (by omega_using [hr]) k0 hw8 rfl rfl
  have f1 : Frame [⟨W σ, workUsed⟩] σ.mem (t.mem.writeW (la (W σ) r (2 * p))
      (t.mem.readW (la (W σ) r (2 * p)) 64 ^^^ t.mem.readW (laneP σ (2 * p) + BitVec.ofNat 64 (8 * w)) 64)) :=
    hf.writeW (List.mem_singleton_self _) _ hc0
  have e1 : (t.mem.writeW (la (W σ) r (2 * p)) (t.mem.readW (la (W σ) r (2 * p)) 64 ^^^
      t.mem.readW (laneP σ (2 * p) + BitVec.ofNat 64 (8 * w)) 64)).readW (la (W σ) r (2 * p + 1)) 64 =
      t.mem.readW (la (W σ) r (2 * p + 1)) 64 := by
    rw [la, la, Mem.readW_writeW_sep (Offset.sep _ (by unfold lo; omega_using [hp2]) (by omega_using [hoff'])
      (by omega_using [hoff])) (by decide)]
  have st2 := xorWord (r := r) (k := 2 * p + 1) (w := w) hp hf st1 (by omega_using [hr]) k1 hw8 e1.symm rfl
  refine ⟨fun g h9 h10 h11 h12 => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [m₉.gpr, u₈.other _ h12, u₇.other _ h11, u₆.other _ h12, u₅.other _ h11, u₄.other _ h10, u₃.other _ h10,
      u₂.other _ h9, u₁.other _ h9]
  · rw [m₉.vec, u₈.vec, u₇.vec, u₆.vec, u₅.vec, u₄.vec, u₃.vec, u₂.vec, u₁.vec]
  · rw [m₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [m₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [m₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · rw [m₉.mem, mem₈, x11, x12, eb']; exact st2
  · rw [m₉.mem, mem₈, x11, x12, eb']
    have hd0 : (⟨W σ, 800⟩ : Region).Contains (la (W σ) r (2 * p)) (64 / 8) :=
      Offset.contains_base _ (by omega_using [hoff]) (by omega_using [hoff])
    have hd1 : (⟨W σ, 800⟩ : Region).Contains (la (W σ) r (2 * p + 1)) (64 / 8) :=
      Offset.contains_base _ (by omega_using [hoff']) (by omega_using [hoff'])
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ hd0).writeW (List.mem_singleton_self _) _ hd1

/-- After a row of the loop from `Inv σ w`. -/
structure RowPost (σ : State) (w : Nat) (t : State) : Prop where
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr
  sp : t.sp = σ.sp
  x19 : t.gpr .x19 = W σ
  ptr : ∀ k < 4, t.gpr (lanePtr k) = laneP σ k
  pos : t.gpr .x24 = BitVec.ofNat 64 (8 * (w + 1))
  left : t.gpr .x25 = BitVec.ofNat 64 (L σ - 8 * (w + 1))
  row : t.gpr .x26 = W σ + BitVec.ofNat 64 (16 * (w % 17) + 16)
  cnt : t.gpr .x27 = BitVec.ofNat 64 (16 - w % 17)
  st : St4 t.mem (W σ) (fun k => xorAt (Rep 136 ((msg σ k).take (8 * w))) (8 * (w % 17)) (chunk8 σ k w))
  frame : Frame [⟨W σ, workUsed⟩] σ.mem t.mem
  sv : ∀ p ∈ saved, t.mem.readW (W σ + BitVec.ofNat 64 p.2) 64 = σ.gpr p.1
  x28 : t.gpr .x28 = σ.gpr .x28
  x30 : t.gpr .x30 = σ.gpr .x30
  vk : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (σ.v r).extractLsb' 0 64

theorem row_eq : row = xorPair 0 ++ (xorPair 1 ++ ([.addImm .x .x24 .x24 8, .addImm .x .x26 .x26 16,
    .subImm .x .x25 .x25 8, .subImm .x .x27 .x27 1] : List Instr)) := by
  simp only [row, List.append_assoc]

theorem frame800 {m m' : Mem} (h : Frame [⟨W σ, 800⟩] m m') : Frame [⟨W σ, workUsed⟩] m m' :=
  h.sub fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩

theorem frame936 {m m' : Mem} (h : Frame [⟨W σ, 936⟩] m m') : Frame [⟨W σ, workUsed⟩] m m' :=
  h.sub fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩

theorem frame800_936 {m m' : Mem} (h : Frame [⟨W σ, 800⟩] m m') : Frame [⟨W σ, 936⟩] m m' :=
  h.sub fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩

theorem sv_frame (hp : Thash4Pre n σ) {m m' : Mem} (h : Frame [⟨W σ, 936⟩] m m')
    (hs : ∀ p ∈ saved, m.readW (W σ + BitVec.ofNat 64 p.2) 64 = σ.gpr p.1) :
    ∀ p ∈ saved, m'.readW (W σ + BitVec.ofNat 64 p.2) 64 = σ.gpr p.1 := fun p hp' => by
  obtain ⟨i, hi, rfl⟩ := mem_saved hp'
  rw [readW_frame h fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact slot_disj hp hi]
  exact hs _ hp'

theorem row_ok (hp : Thash4Pre n σ) {w : Nat} (hw : w + 1 ≤ nw σ) {s : State} (hI : Inv σ w s) :
    WP isa (.block row) s (RowPost σ w) := by
  have hL := len_eq hp
  have hw8 : 8 * w + 8 ≤ L σ := by omega_using [hL, hw]
  have hr : w % 17 < 17 := Nat.mod_lt _ (by decide)
  rw [row_eq]
  refine WP.block_append (WP.mono (pair_ok hp (p := 0) (by decide) hw8 hr hI.wr hI.row hI.ptr hI.pos hI.st hI.frame)
    fun t₀ ⟨g₀, v₀, r₀, w₀, p₀, l₀, f₀⟩ => ?_)
  have g₀' : ∀ g, g ≠ .x9 → g ≠ .x10 → g ≠ .x11 → g ≠ .x12 → t₀.gpr g = s.gpr g := g₀
  refine WP.block_append (WP.mono (pair_ok hp (p := 1) (by decide) hw8 hr (by rw [w₀, hI.wr])
    (by rw [g₀' _ (by decide) (by decide) (by decide) (by decide), hI.row])
    (fun k hk => by obtain ⟨h9, h10, h11, h12, -⟩ := lanePtr_ne hk; rw [g₀' _ h9 h10 h11 h12, hI.ptr k hk])
    (by rw [g₀' _ (by decide) (by decide) (by decide) (by decide), hI.pos]) l₀ (hI.frame.trans (frame800 f₀)))
    fun t₁ ⟨g₁, v₁, r₁, w₁, p₁, l₁, f₁⟩ => ?_)
  have g : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t₁.gpr r = s.gpr r := fun r h9 h10 h11 h12 => by
    rw [g₁ _ h9 h10 h11 h12, g₀' _ h9 h10 h11 h12]
  refine wp_addImm (by decide) fun u₄ v₄ => wp_addImm (by decide) fun u₅ v₅ => wp_subImm (by decide) fun u₆ v₆ =>
    wp_subImm (by decide) fun u₇ v₇ => wp_nil ?_
  have hm : u₇.mem = t₁.mem := by rw [v₇.mem, v₆.mem, v₅.mem, v₄.mem]
  have fT : Frame [⟨W σ, 800⟩] s.mem u₇.mem := by rw [hm]; exact f₀.trans f₁
  refine ⟨by rw [v₇.rd, v₆.rd, v₅.rd, v₄.rd, r₁, r₀, hI.rd], by rw [v₇.wr, v₆.wr, v₅.wr, v₄.wr, w₁, w₀, hI.wr],
    by rw [v₇.sp, v₆.sp, v₅.sp, v₄.sp, p₁, p₀, hI.sp], ?_, fun k hk => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [v₇.other _ (by decide), v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide),
      g _ (by decide) (by decide) (by decide) (by decide), hI.x19]
  · obtain ⟨h9, h10, h11, h12, h24, h25, h26, h27, -⟩ := lanePtr_ne hk
    rw [v₇.other _ h27, v₆.other _ h25, v₅.other _ h26, v₄.other _ h24, g _ h9 h10 h11 h12, hI.ptr k hk]
  · rw [v₇.other _ (by decide), v₆.other _ (by decide), v₅.other _ (by decide), v₄.gpr,
      g _ (by decide) (by decide) (by decide) (by decide), hI.pos, ← BitVec.ofNat_add, Nat.mul_succ]
  · rw [v₇.other _ (by decide), v₆.gpr, v₅.other _ (by decide), v₄.other _ (by decide),
      g _ (by decide) (by decide) (by decide) (by decide), hI.left, Proof.Sha3.sub_ofNat (by omega_using [hw8])]
    congr 1
  · rw [v₇.other _ (by decide), v₆.other _ (by decide), v₅.gpr, v₄.other _ (by decide),
      g _ (by decide) (by decide) (by decide) (by decide), hI.row, addOf]
  · rw [v₇.gpr, v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide),
      g _ (by decide) (by decide) (by decide) (by decide), hI.cnt, Proof.Sha3.sub_ofNat (by omega_using [hr])]
    congr 1; omega_using []
  · rw [hm]
    refine st4_congr l₁ fun k hk => ?_
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_using [hk]) with rfl | rfl | rfl | rfl <;> simp
  · exact hI.frame.trans (frame800 fT)
  · exact sv_frame hp (frame800_936 fT) hI.sv
  · rw [v₇.other _ (by decide), v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide),
      g _ (by decide) (by decide) (by decide) (by decide), hI.x28]
  · rw [v₇.other _ (by decide), v₆.other _ (by decide), v₅.other _ (by decide), v₄.other _ (by decide),
      g _ (by decide) (by decide) (by decide) (by decide), hI.x30]
  · intro r hr'
    rw [v₇.vec, v₆.vec, v₅.vec, v₄.vec, v₁, v₀, hI.vk r hr']

/-! ## The permutation -/

theorem pairAt_frame {m m' : Mem} {p : Addr} {A B : KState} (h : PairAt m p A B) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (pairR p).Disjoint r) : PairAt m' p A B := fun i hi => by
  rw [hf.read (Proof.Sha3.AArch64.Neon.pair_contains p hi) hd (by decide)]
  exact h i hi

theorem cov (hp : Thash4Pre n σ) {s : State} (hw : s.wr = σ.wr) {d k : Nat} (h : d + k ≤ workLen) :
    Covers [⟨W σ + BitVec.ofNat 64 d, k⟩] s.wr := Covers.one (wr_work hp hw h)

theorem cov0 (hp : Thash4Pre n σ) {s : State} (hw : s.wr = σ.wr) {k : Nat} (h : k ≤ workLen) :
    Covers [⟨W σ, k⟩] s.wr := by
  have := cov hp hw (d := 0) (k := k) (by omega_using [h])
  simpa using this

abbrev volatile : List Reg := Proof.Sha3.AArch64.Neon.X2.volatile

/-- The four states permuted, two calls of the two-way permutation. -/
theorem perm_ok (hp : Thash4Pre n σ) (sha3 : Bool) {u : State} (hwr : u.wr = σ.wr) (h19 : u.gpr .x19 = W σ)
    {X : Nat → KState} (hst : St4 u.mem (W σ) X) :
    WP isa (perm sha3) u fun v => St4 v.mem (W σ) (fun k => keccakF (X k)) ∧ Frame [⟨W σ, 936⟩] u.mem v.mem ∧
      v.rd = u.rd ∧ v.wr = u.wr ∧ v.sp = u.sp ∧ (∀ r, r ∉ volatile → v.gpr r = u.gpr r) ∧
      ∀ r ∈ preservedV, (v.v r).extractLsb' 0 64 = (u.v r).extractLsb' 0 64 := by
  have hW := work_fit' hp
  obtain ⟨P0, P1⟩ := pairs_of_st4 hst
  have d0 : (pairR (W σ)).Disjoint (Proof.Sha3.AArch64.Neon.X2.callR (W σ + BitVec.ofNat 64 oX2)) :=
    Offset.base_disjoint _ (by decide) (by simp only [oX2]; omega_using [hW])
  have d1 : (pairR (W σ + BitVec.ofNat 64 oPair1)).Disjoint
      (Proof.Sha3.AArch64.Neon.X2.callR (W σ + BitVec.ofNat 64 oX2)) :=
    Offset.disjoint _ (Or.inl (by decide)) (by simp only [oPair1]; omega_using [hW]) (by simp only [oX2]; omega_using [hW])
  have d01 : (pairR (W σ)).Disjoint (pairR (W σ + BitVec.ofNat 64 oPair1)) :=
    Offset.base_disjoint _ (by decide) (by simp only [oPair1]; omega_using [hW])
  have d1c : (pairR (W σ + BitVec.ofNat 64 oPair1)).Disjoint (pairR (W σ)) := d01.symm
  have dc : ∀ R, R = pairR (W σ + BitVec.ofNat 64 oPair1) →
      ∀ r ∈ [pairR (W σ), Proof.Sha3.AArch64.Neon.X2.callR (W σ + BitVec.ofNat 64 oX2)], R.Disjoint r := by
    rintro R rfl r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact d1c
    · exact d1
  have fr : ∀ p, p = W σ ∨ p = W σ + BitVec.ofNat 64 oPair1 → ∀ r ∈ [pairR p,
      Proof.Sha3.AArch64.Neon.X2.callR (W σ + BitVec.ofNat 64 oX2)], ∃ r' ∈ [(⟨W σ, 936⟩ : Region)], r.Sub r' := by
    rintro p hp' r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    rcases hr with rfl | rfl
    · rcases hp' with rfl | rfl
      · exact Region.sub_prefix (by decide)
      · exact Offset.sub_base _ (by simp only [oPair1]; omega_using [])
    · exact Offset.sub_base _ (by simp only [oX2]; omega_using [])
  unfold perm
  refine WP.seq (WP.mono (Proof.Sha3.AArch64.Neon.X2.callAny_ok sha3 (p := W σ) (q := W σ + BitVec.ofNat 64 oX2)
    (by decide) (by decide) (by decide) (by decide) (by decide) h19 (by rw [h19]) d0 P0
    (Covers.pair (cov0 hp hwr (by decide)) (cov hp hwr (by decide)))) fun t ⟨kt, vt, ft, Pt⟩ => ?_)
  refine WP.seq (wp_addImm (by decide) fun t₁ u₁ => wp_nil ?_)
  have t19 : t.gpr .x19 = W σ := by rw [kt.gpr _ (by decide), h19]
  have P1t : PairAt t₁.mem (W σ + BitVec.ofNat 64 oPair1) (X 2) (X 3) := by
    rw [u₁.mem]; exact pairAt_frame P1 ft (dc _ rfl)
  refine WP.mono (Proof.Sha3.AArch64.Neon.X2.callAny_ok sha3 (p := W σ + BitVec.ofNat 64 oPair1)
    (q := W σ + BitVec.ofNat 64 oX2)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [u₁.gpr, t19])
    (by rw [u₁.other _ (by decide), t19]) d1 P1t
    (Covers.pair (cov hp (by rw [u₁.wr, kt.wr, hwr]) (by decide)) (cov hp (by rw [u₁.wr, kt.wr, hwr]) (by decide))))
    fun v ⟨kv, vv, fv, Pv⟩ => ?_
  have P0v : PairAt v.mem (W σ) (keccakF (X 0)) (keccakF (X 1)) := by
    refine pairAt_frame (m := t₁.mem) (by rw [u₁.mem]; exact Pt) fv fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact d01
    · exact d0
  refine ⟨st4_of_pairs (A := fun k => keccakF (X k)) P0v Pv, ?_, by rw [kv.rd, u₁.rd, kt.rd],
    by rw [kv.wr, u₁.wr, kt.wr], by rw [kv.sp, u₁.sp, kt.sp], fun r hr => ?_, fun r hr => ?_⟩
  · rw [← u₁.mem] at ft
    exact (ft.sub (fr _ (.inl rfl))).trans (fv.sub (fr _ (.inr rfl)))
  · have h9 : r ≠ .x9 := fun e => hr (by rw [e]; decide)
    rw [kv.gpr r hr, u₁.other _ h9, kt.gpr r hr]
  · rw [vv r hr, u₁.vec, vt r hr]

/-! ## The loop -/

theorem rep_step {w : Nat} (hw8 : 8 * w + 8 ≤ L σ) (k : Nat) :
    Rep 136 ((msg σ k).take (8 * (w + 1))) =
      if w % 17 = 16 then keccakF (xorAt (Rep 136 ((msg σ k).take (8 * w))) (8 * (w % 17)) (chunk8 σ k w))
      else xorAt (Rep 136 ((msg σ k).take (8 * w))) (8 * (w % 17)) (chunk8 σ k w) := by
  have hl : ((msg σ k).take (8 * w)).length = 8 * w := by
    rw [List.length_take, length_msg]; omega_using [hw8]
  have hm : ((msg σ k).take (8 * w)).length % 136 = 8 * (w % 17) := by rw [hl]; omega_using []
  rw [show 8 * (w + 1) = 8 * w + 8 by omega_using [], List.take_add,
    rep_append (by decide) (by decide) _ _ (by rw [length_chunk8 k hw8]; decide)
      (by rw [hm, length_chunk8 k hw8]; omega_using []),
    hm, length_chunk8 k hw8]
  by_cases h : w % 17 = 16
  · rw [ite_eq_left (show 8 * (w % 17) + 8 = 136 by omega_using [h]), ite_eq_left h]
  · rw [ite_eq_right (show ¬ 8 * (w % 17) + 8 = 136 by omega_using [h]), ite_eq_right h]

theorem body_ok (hp : Thash4Pre n σ) (sha3 : Bool) {w : Nat} (hw : w + 1 ≤ nw σ) {s : State} (hI : Inv σ w s) :
    WP isa (body sha3) s (Inv σ (w + 1)) := by
  have hL := len_eq hp
  have hw8 : 8 * w + 8 ≤ L σ := by omega_using [hL, hw]
  have hr : w % 17 < 17 := Nat.mod_lt _ (by decide)
  unfold body
  refine WP.seq (WP.mono (row_ok hp hw hI) fun t ht => ?_)
  refine WP.ite (decide (w % 17 = 16)) (by
      rw [show isa.eval (.zero .x .x27) t = _ from eval_zero t .x27, ht.cnt, Proof.Sha3.ofNat_beq_zero (by omega_using [hr])]
      congr 1; simp only [decide_eq_decide]; omega_using [hr]) (fun hb => ?_) (fun hb => ?_)
  · have h16 : w % 17 = 16 := of_decide_eq_true hb
    unfold permuteKeep
    refine WP.seq (WP.mono (perm_ok hp sha3 ht.wr ht.x19 ht.st) fun v ⟨lv, fv, rv, wv, pv, gv, vv⟩ => ?_)
    refine wp_mov' fun v₁ u₁ => wp_movz fun v₂ u₂ => wp_nil ?_
    have g : ∀ r, r ≠ .x26 → r ≠ .x27 → r ∉ volatile → v₂.gpr r = t.gpr r := fun r h26 h27 hv => by
      rw [u₂.other _ h27, u₁.other _ h26, gv r hv]
    refine ⟨by rw [u₂.rd, u₁.rd, rv, ht.rd], by rw [u₂.wr, u₁.wr, wv, ht.wr], by rw [u₂.sp, u₁.sp, pv, ht.sp],
      by rw [g _ (by decide) (by decide) (by decide), ht.x19], fun k hk => ?_,
      by rw [g _ (by decide) (by decide) (by decide), ht.pos], ?_, ?_, ?_, ?_, ?_, ?_,
      by rw [g _ (by decide) (by decide) (by decide), ht.x28], by rw [g _ (by decide) (by decide) (by decide), ht.x30],
      fun r hr' => by rw [u₂.vec, u₁.vec, vv r hr', ht.vk r hr']⟩
    · obtain ⟨-, -, -, -, -, -, h26, h27, -⟩ := lanePtr_ne hk
      have hv : lanePtr k ∉ volatile := by
        rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_using [hk]) with rfl | rfl | rfl | rfl <;> decide
      rw [g _ h26 h27 hv, ht.ptr k hk]
    · rw [g _ (by decide) (by decide) (by decide), ht.left]
    · rw [u₂.other _ (by decide), u₁.gpr, gv _ (by decide), ht.x19, show 16 * ((w + 1) % 17) = 0 by omega_using [h16]]
      simp
    · rw [u₂.gpr, show (w + 1) % 17 = 0 by omega_using [h16]]; rfl
    · rw [u₂.mem, u₁.mem]
      exact st4_congr lv fun k _ => by rw [rep_step hw8 k, ite_eq_left h16]
    · rw [u₂.mem, u₁.mem]; exact ht.frame.trans (frame936 fv)
    · rw [u₂.mem, u₁.mem]; exact sv_frame hp fv ht.sv
  · have h16 : ¬ w % 17 = 16 := fun h => by simp [h] at hb
    refine wp_nil ⟨ht.rd, ht.wr, ht.sp, ht.x19, ht.ptr, ht.pos, ht.left, ?_, ?_, ?_, ht.frame, ht.sv, ht.x28,
      ht.x30, ht.vk⟩
    · rw [ht.row, show 16 * ((w + 1) % 17) = 16 * (w % 17) + 16 by omega_using [h16]]
    · rw [ht.cnt, show 17 - (w + 1) % 17 = 16 - w % 17 by omega_using [h16, hr]]
    · exact st4_congr ht.st fun k _ => by rw [rep_step hw8 k, ite_eq_right h16]

theorem loop_ok (hp : Thash4Pre n σ) (sha3 : Bool) {s : State} (hI : Inv σ 0 s) :
    WP isa (.loop (body sha3) (.nonzero .x .x25)) s (Inv σ (nw σ)) := by
  have hL := len_eq hp
  have h0 : 0 < L σ := hp.len_pos
  have hpos : 1 ≤ nw σ := by omega_using [h0, hL]
  refine WP.loop (M := isa) (Q := Inv σ (nw σ))
    (fun (m : Nat) (t : State) => ∃ w, m = nw σ - w ∧ w + 1 ≤ nw σ ∧ Inv σ w t) ?_ (nw σ) s ⟨0, rfl, hpos, hI⟩
  rintro m t ⟨w, rfl, hw, hIw⟩
  refine WP.mono (body_ok hp sha3 hw hIw) fun t' h1 => ?_
  have hlt : L σ - 8 * (w + 1) < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) (σ.gpr .x2).isLt
  have ev : isa.eval (.nonzero .x .x25) t' = some (decide (w + 1 ≠ nw σ)) := by
    rw [show isa.eval (.nonzero .x .x25) t' = _ from eval_nonzero t' .x25, h1.left]
    have := Proof.Sha3.ofNat_beq_zero hlt
    simp only [bne, this]
    congr 1; rw [← decide_not]; simp only [decide_eq_decide]; omega_using [hL, hw]
  by_cases e : w + 1 = nw σ
  · exact Or.inl ⟨by rw [ev]; simp [e], e ▸ h1⟩
  · exact Or.inr ⟨by rw [ev]; simp [e], _, by omega_using [hw, e], w + 1, rfl, by omega_using [hw, e], h1⟩

/-! ## The padding -/

/-- Writing lane `i` of state `k`, its bytes those of the lane with `b`
XORed into byte `d₀`. -/
theorem st4_xorByte {m : Mem} {p : Addr} {A : Nat → KState} (h : St4 m p A) {i k d₀ : Nat}
    (hi : i < 25) (hk : k < 4) (hd₀ : d₀ < 8) {v : BitVec 64} {b : Byte}
    (hv : ∀ d < 8, v.extractLsb' (8 * d) 8 = m (la p i k + BitVec.ofNat 64 d) ^^^ (if d = d₀ then b else 0)) :
    St4 (m.writeW (la p i k) v) p (fun k' => if k' = k then xorByte (A k') (8 * i + d₀) b else A k') := by
  refine st4_of_bytes fun k' hk' q hq => ?_
  by_cases c : k' = k ∧ q / 8 = i
  · obtain ⟨rfl, hqi⟩ := c
    have e : ba p k' q = la p i k' + BitVec.ofNat 64 (q % 8) := by
      rw [la_byte _ (by omega_using []), ← hqi, show 8 * (q / 8) + q % 8 = q by omega_using []]
    rw [e, writeW_in _ _ _ (by omega_using []), hv _ (by omega_using []), la_byte _ (by omega_using []),
      ← hqi, show 8 * (q / 8) + q % 8 = q by omega_using [], byte_of_st4 h hk hq, ite_eq_left rfl,
      byteOf_xorByte _ _ _ hq]
    by_cases e2 : q % 8 = d₀
    · rw [ite_eq_left e2, ite_eq_left (by omega_using [e2])]
    · rw [ite_eq_right e2, ite_eq_right (by omega_using [e2])]; exact BitVec.xor_zero
  · have hne : 8 ≤ (ba p k' q - la p i k).toNat := by
      have h1 := ba_lt hk' hq
      have h2 := lo_lt hi hk
      simp only [ba, la, lo] at h1 h2 ⊢
      rw [Offset.sub_toNat' _ (by omega_using [h1, h2, hk, hk', hq, hi]) (by omega_using [h1, h2, hk, hk', hq, hi])]
      split <;> rename_i hs <;> omega_using [c, hi, hk, hk', hq, hs]
    rw [writeW_out _ _ _ hne, byte_of_st4 h hk' hq]
    by_cases e : k' = k
    · subst e
      rw [ite_eq_left rfl, byteOf_xorByte _ _ _ hq, ite_eq_right (by omega_using [c, hd₀])]
    · rw [ite_eq_right e]

/-- One lane of the padding. -/
def padL (b : Reg) (o : Nat) : List Instr := [.ldr .x .x9 b o, .logic .eor .x .x9 .x9 .x10, .str .x .x9 b o]

theorem padAll_ok (hp : Thash4Pre n σ) {b : Reg} (hb9 : b ≠ .x9) {off : Nat → Nat} {r d₀ : Nat} (hr : r < 25)
    (hd₀ : d₀ < 8) {byte : Byte} {c : BitVec 64}
    (hc : ∀ d < 8, c.extractLsb' (8 * d) 8 = if d = d₀ then byte else 0)
    (ho : ∀ k < 4, off k % 8 = 0 ∧ off k < 4096 * 8) :
    ∀ j ≤ 4, ∀ (t : State) (A : Nat → KState), t.gpr .x10 = c → t.wr = σ.wr →
      (∀ k < 4, t.gpr b + BitVec.ofNat 64 (off k) = la (W σ) r k) → St4 t.mem (W σ) A →
      WP isa (.block ((List.range j).flatMap fun k => padL b (off k))) t fun t' =>
        St4 t'.mem (W σ) (fun k => if k < j then xorByte (A k) (8 * r + d₀) byte else A k) ∧
        (∀ g, g ≠ .x9 → t'.gpr g = t.gpr g) ∧ t'.v = t.v ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.sp = t.sp ∧
        Frame [⟨W σ, 800⟩] t.mem t'.mem := by
  intro j
  induction j with
  | zero =>
    intro _ t A _ _ _ hst
    exact wp_nil ⟨st4_congr hst fun k _ => by simp, fun _ _ => rfl, rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | succ j ih =>
    intro hj t A h10 hw hb hst
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (ih (by omega_using [hj]) t A h10 hw hb hst)
      fun t₁ ⟨l₁, g₁, v₁, r₁, w₁, p₁, f₁⟩ => ?_)
    have hj4 : j < 4 := by omega_using [hj]
    have hoff := lo_lt (i := r) (k := j) hr hj4
    have ha : t₁.gpr b + BitVec.ofNat 64 (off j) = la (W σ) r j := by rw [g₁ _ hb9, hb j hj4]
    refine wp_ldr (a := la (W σ) r j) (ho j hj4) ha
      (by rw [r₁, w₁, la]; exact rw_work hp hw (by simp only [workLen]; omega_using [hoff])) fun t₂ u₂ => ?_
    refine wp_eor fun t₃ u₃ => wp_str (a := la (W σ) r j) (ho j hj4)
      (by rw [u₃.other _ hb9, u₂.other _ hb9, ha])
      (by rw [u₃.wr, u₂.wr, w₁, la]; exact wr_work hp hw (by simp only [workLen]; omega_using [hoff])) fun t₄ m₄ => wp_nil ?_
    have x9 : t₃.gpr .x9 = t₁.mem.readW (la (W σ) r j) 64 ^^^ c := by
      rw [u₃.gpr, u₂.gpr, u₂.other _ (by decide), g₁ _ (by decide), h10]
    have hm : t₃.mem = t₁.mem := by rw [u₃.mem, u₂.mem]
    refine ⟨?_, fun g hg => by rw [m₄.gpr, u₃.other _ hg, u₂.other _ hg, g₁ _ hg], by rw [m₄.vec, u₃.vec, u₂.vec, v₁],
      by rw [m₄.rd, u₃.rd, u₂.rd, r₁], by rw [m₄.wr, u₃.wr, u₂.wr, w₁], by rw [m₄.sp, u₃.sp, u₂.sp, p₁], ?_⟩
    · rw [m₄.mem, hm, x9]
      refine st4_congr (st4_xorByte l₁ hr hj4 hd₀ fun d hd => by
        rw [BitVec.extractLsb'_xor, ← byte_readW _ _ hd, hc d hd]) fun k hk => ?_
      by_cases e : k = j
      · subst e; simp
      · rw [ite_eq_right e]
        simp only [show (k < j) = (k < j + 1) from propext ⟨fun h => by omega_using [h], fun h => by omega_using [h, e]⟩]
    · rw [m₄.mem, hm]
      exact f₁.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using [hoff]) (by omega_using [hoff]))

theorem pad_eq : pad = .movz .x .x10 0x1f 0 :: ((List.range 4).flatMap fun k => padL .x26 (lo 0 k)) ++
    .movz .x .x10 0x8000 3 :: ((List.range 4).flatMap fun k => padL .x19 (lo 16 k)) := rfl

theorem bytes_1f : ∀ d < 8, ((0x1f : BitVec 16).setWidth 64).extractLsb' (8 * d) 8 =
    if d = 0 then (0x1f : Byte) else 0 := by decide

theorem bytes_80 : ∀ d < 8, ((0x8000 : BitVec 16).setWidth 64 <<< 48).extractLsb' (8 * d) 8 =
    if d = 7 then (0x80 : Byte) else 0 := by decide

theorem lo_ok : ∀ i < 25, ∀ k < 4, lo i k % 8 = 0 ∧ lo i k < 4096 * 8 := by decide

/-- The padded states, whose permutation's first bytes are the outputs. -/
abbrev padded (M : List Byte) : KState := xorByte (xorByte (Rep 136 M) (M.length % 136) 0x1f) 135 0x80

/-- After the padding. -/
structure PadPost (σ : State) (t : State) : Prop where
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr
  sp : t.sp = σ.sp
  x19 : t.gpr .x19 = W σ
  ptr : ∀ k < 4, t.gpr (lanePtr k) = laneP σ k
  st : St4 t.mem (W σ) (fun k => padded (msg σ k))
  frame : Frame [⟨W σ, workUsed⟩] σ.mem t.mem
  sv : ∀ p ∈ saved, t.mem.readW (W σ + BitVec.ofNat 64 p.2) 64 = σ.gpr p.1
  x28 : t.gpr .x28 = σ.gpr .x28
  x30 : t.gpr .x30 = σ.gpr .x30
  vk : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (σ.v r).extractLsb' 0 64

theorem pad_ok (hp : Thash4Pre n σ) {s : State} (hI : Inv σ (nw σ) s) : WP isa (.block pad) s (PadPost σ) := by
  have hL := len_eq hp
  have hr : nw σ % 17 < 17 := Nat.mod_lt _ (by decide)
  have htake : ∀ k, (msg σ k).take (8 * nw σ) = msg σ k := fun k => by
    rw [List.take_of_length_le (by rw [length_msg]; omega_using [hL])]
  rw [pad_eq]
  refine wp_movz fun s₁ u₁ => ?_
  rw [List.append_eq, WP.block_append_iff]
  refine WP.mono (padAll_ok hp (b := .x26) (by decide) (off := fun k => lo 0 k) (r := nw σ % 17) (d₀ := 0)
    (by omega_using [hr]) (by decide) bytes_1f (fun k hk => lo_ok 0 (by decide) k hk) 4 (Nat.le_refl _) s₁ (fun k => Rep 136 ((msg σ k).take (8 * nw σ))) u₁.gpr
    (by rw [u₁.wr, hI.wr]) (fun k hk => by
      rw [u₁.other _ (by decide), hI.row, addOf, la, show lo (nw σ % 17) k = 16 * (nw σ % 17) + lo 0 k by
        unfold lo; omega_using []]) (by rw [u₁.mem]; exact hI.st)) fun t₁ ⟨l₁, g₁, v₁, r₁, w₁, p₁, f₁⟩ => ?_
  refine wp_movz3 fun s₂ u₂ => ?_
  refine WP.mono (padAll_ok hp (b := .x19) (by decide) (off := fun k => lo 16 k) (r := 16) (d₀ := 7)
    (by decide) (by decide) bytes_80 (fun k hk => lo_ok 16 (by decide) k hk) 4 (Nat.le_refl _) s₂
    (fun k => if k < 4 then xorByte (Rep 136 ((msg σ k).take (8 * nw σ))) (8 * (nw σ % 17) + 0) 0x1f
      else Rep 136 ((msg σ k).take (8 * nw σ))) u₂.gpr
    (by rw [u₂.wr, w₁, u₁.wr, hI.wr]) (fun k hk => by
      rw [u₂.other _ (by decide), g₁ _ (by decide), u₁.other _ (by decide), hI.x19]) (by rw [u₂.mem]; exact l₁))
    fun t₂ ⟨l₂, g₂, v₂, r₂, w₂, p₂, f₂⟩ => ?_
  have g : ∀ r, r ≠ .x9 → r ≠ .x10 → t₂.gpr r = s.gpr r := fun r h9 h10 => by
    rw [g₂ _ h9, u₂.other _ h10, g₁ _ h9, u₁.other _ h10]
  have fT : Frame [⟨W σ, 800⟩] s.mem t₂.mem := by
    rw [u₁.mem] at f₁; rw [u₂.mem] at f₂; exact f₁.trans f₂
  refine ⟨by rw [r₂, u₂.rd, r₁, u₁.rd, hI.rd], by rw [w₂, u₂.wr, w₁, u₁.wr, hI.wr], by rw [p₂, u₂.sp, p₁, u₁.sp, hI.sp],
    by rw [g _ (by decide) (by decide), hI.x19], fun k hk => ?_, ?_, hI.frame.trans (frame800 fT),
    sv_frame hp (frame800_936 fT) hI.sv, by rw [g _ (by decide) (by decide), hI.x28],
    by rw [g _ (by decide) (by decide), hI.x30], fun r hr' => by rw [v₂, u₂.vec, v₁, u₁.vec, hI.vk r hr']⟩
  · obtain ⟨h9, h10, -⟩ := lanePtr_ne hk
    rw [g _ h9 h10, hI.ptr k hk]
  · refine st4_congr l₂ fun k hk => ?_
    rw [ite_eq_left hk, ite_eq_left hk, htake, padded, length_msg, hL, show 8 * 16 + 7 = 135 from rfl,
      show 8 * nw σ % 136 = 8 * (nw σ % 17) + 0 by omega_using []]

/-! ## The outputs -/

/-- Word `i` of output `k`. -/
abbrev oaddr (σ : State) (n k i : Nat) : Addr := inp σ + BitVec.ofNat 64 (k * str σ + (n + 32) + 8 * i)

theorem outAt_word (hp : Thash4Pre n σ) (k i : Nat) : outAt σ k + BitVec.ofNat 64 (8 * i) = oaddr σ n k i := by
  rw [outAt, hp.out_eq, addOf, addOf]
  exact congrArg (fun x => σ.gpr .x0 + BitVec.ofNat 64 x) (by simp only [str]; omega_using [])

theorem laneP_word (k i : Nat) : laneP σ k + BitVec.ofNat 64 (n + 32 + 8 * i) = oaddr σ n k i := by
  rw [laneP, addOf]
  exact congrArg (fun x => inp σ + BitVec.ofNat 64 x) (by omega_using [])

theorem out_off (hp : Thash4Pre n σ) {k i : Nat} (hk : k < 4) (hi : 8 * i + 8 ≤ n) :
    k * str σ + (n + 32) + 8 * i + 8 ≤ 4 * str σ ∧ 4 * str σ ≤ 2 ^ 64 := by
  have h := hp.out_fit
  have h2 := kstr_le (σ := σ) hk
  exact ⟨by simp only [str] at h h2 ⊢; omega_using [h, h2, hi], str_lt hp⟩

theorem lanes_work (hp : Thash4Pre n σ) {k i : Nat} (hk : k < 4) (hi : 8 * i + 8 ≤ n) :
    Region.Disjoint ⟨oaddr σ n k i, 8⟩ ⟨W σ, workUsed⟩ := by
  obtain ⟨h1, h2⟩ := out_off hp hk hi
  exact (hp.lanes_work.sub_left (Offset.sub_base _ h1)).sub_right (Region.sub_prefix (by decide))

/-- The regions of the outputs. -/
abbrev outsR (σ : State) (n : Nat) : List Region := (List.range 4).map fun k => ⟨outAt σ k, n⟩

theorem out_mem {k : Nat} (hk : k < 4) : (⟨outAt σ k, n⟩ : Region) ∈ outsR σ n :=
  List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩

theorem out_contains (hp : Thash4Pre n σ) (hn : n ≤ 32) {k i : Nat} (hi : 8 * i + 8 ≤ n) :
    (⟨outAt σ k, n⟩ : Region).Contains (oaddr σ n k i) (64 / 8) := by
  rw [← outAt_word hp]; exact Offset.contains_base _ hi (by omega_using [hi, hn])

/-- Outputs `k` and `k'` are different words. -/
theorem out_sep (hp : Thash4Pre n σ) {k k' i i' : Nat} (hk : k < 4) (hk' : k' < 4) (hi : 8 * i + 8 ≤ n)
    (hi' : 8 * i' + 8 ≤ n) (h : k ≠ k' ∨ i ≠ i') : Mem.Sep (oaddr σ n k i) 8 (oaddr σ n k' i') 8 := by
  obtain ⟨a1, a2⟩ := out_off hp hk hi
  obtain ⟨b1, -⟩ := out_off hp hk' hi'
  have hf := hp.out_fit
  refine Offset.sep _ ?_ (by omega_using [a1, a2]) (by omega_using [b1, a2])
  by_cases e : k = k'
  · subst e; rcases h with h | h
    · exact absurd rfl h
    · omega_using [h]
  · have h : k ≠ k' := e
    rcases Nat.lt_or_gt_of_ne h with c | c
    · have := Nat.mul_le_mul_right (str σ) (show k + 1 ≤ k' by omega_using [c])
      rw [Nat.succ_mul] at this; simp only [str] at hf this ⊢; omega_using [this, hf, hi, hi']
    · have := Nat.mul_le_mul_right (str σ) (show k' + 1 ≤ k by omega_using [c])
      rw [Nat.succ_mul] at this; simp only [str] at hf this ⊢; omega_using [this, hf, hi, hi']

/-- The output words written so far. -/
def OutW (σ : State) (n : Nat) (F : Nat → KState) (m : Mem) (k j : Nat) : Prop :=
  ∀ i < j, m.readW (oaddr σ n k i) 64 = (F k)[i]!

theorem extractPair_ok (hp : Thash4Pre n σ) (hn : n ≤ 32) (hn8 : n % 8 = 0) {p : Nat} (hp2 : p < 2) {F : Nat → KState} :
    ∀ j ≤ n / 8, ∀ t : State, t.gpr .x19 = W σ → (∀ k < 4, t.gpr (lanePtr k) = laneP σ k) → t.wr = σ.wr →
      St4 t.mem (W σ) F →
      WP isa (.block ((List.range j).flatMap fun i => [.ldp .x9 .x10 .x19 (oPair1 * p + 16 * i),
          .str .x .x9 (lanePtr (2 * p)) (n + 32 + 8 * i), .str .x .x10 (lanePtr (2 * p + 1)) (n + 32 + 8 * i)])) t
        fun t' => (∀ g, g ≠ .x9 → g ≠ .x10 → t'.gpr g = t.gpr g) ∧ t'.v = t.v ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧
          t'.sp = t.sp ∧ OutW σ n F t'.mem (2 * p) j ∧ OutW σ n F t'.mem (2 * p + 1) j ∧
          Frame [⟨outAt σ (2 * p), n⟩, ⟨outAt σ (2 * p + 1), n⟩] t.mem t'.mem := by
  have k0 : 2 * p < 4 := by omega_using [hp2]
  have k1 : 2 * p + 1 < 4 := by omega_using [hp2]
  obtain ⟨n0, n0', -⟩ := lanePtr_ne k0
  obtain ⟨n1, n1', -⟩ := lanePtr_ne k1
  intro j
  induction j with
  | zero =>
    intro _ t _ _ _ _
    exact wp_nil ⟨fun _ _ _ => rfl, rfl, rfl, rfl, rfl, fun i hi => absurd hi (by omega_using []),
      fun i hi => absurd hi (by omega_using []), Frame.refl _ _⟩
  | succ j ih =>
    intro hj t h19 hptr hw hst
    have hj8 : 8 * j + 8 ≤ n := by omega_using [hj]
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (ih (by omega_using [hj]) t h19 hptr hw hst)
      fun t₁ ⟨g₁, v₁, r₁, w₁, p₁, o₁, o₁', f₁⟩ => ?_)
    obtain ⟨ea, eb⟩ := la_pair (r := j) hp2 (W σ)
    have eb' : la (W σ) j (2 * p) + BitVec.ofNat 64 8 = la (W σ) j (2 * p + 1) := by rw [← ea]; exact eb
    have hoff : lo j (2 * p) + 8 ≤ 800 := lo_lt (by omega_using [hj, hn]) k0
    have hoff' : lo j (2 * p + 1) + 8 ≤ 800 := lo_lt (by omega_using [hj, hn]) k1
    have hd1 : ∀ r ∈ [(⟨outAt σ (2 * p), n⟩ : Region), ⟨outAt σ (2 * p + 1), n⟩], Region.Disjoint ⟨W σ, 800⟩ r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      have hk : ∀ k < 4, Region.Disjoint ⟨W σ, 800⟩ ⟨outAt σ k, n⟩ := fun k hk =>
        ((hp.lanes_work.sub_left (by
          have hf := hp.out_fit
          have h2 := kstr_le (σ := σ) hk
          rw [outAt, hp.out_eq, addOf, Nat.add_comm (n + 32)]
          exact Offset.sub_base _ (by simp only [str] at hf h2 ⊢; omega_using [hf, h2]))).sub_right (Region.sub_prefix (by decide))).symm
      rcases hr with rfl | rfl
      · exact hk _ k0
      · exact hk _ k1
    have st₁ : St4 t₁.mem (W σ) F := st4_frame hst f₁ hd1
    have x19₁ : t₁.gpr .x19 = W σ := by rw [g₁ _ (by decide) (by decide), h19]
    refine wp_ldp2 (a := la (W σ) j (2 * p)) (by decide) ⟨by unfold oPair1; omega_using [], by unfold oPair1; omega_using [hp2, hj, hn]⟩
      (by rw [x19₁, ← ea, addOf, Nat.add_comm (16 * j)])
      (by rw [r₁, w₁, la]; exact rw_work hp hw (by simp only [workLen]; omega_using [hoff]))
      (by rw [r₁, w₁, eb', la]; exact rw_work hp hw (by simp only [workLen]; omega_using [hoff'])) fun s₁ s₂ u₁ u₂ => ?_
    have l0 := lanePtr_ne k0
    have l1 := lanePtr_ne k1
    refine wp_str (a := oaddr σ n (2 * p) j) ⟨by omega_using [hn8], by omega_using [hj8, hn]⟩
      (by rw [u₂.other _ l0.2.1, u₁.other _ l0.1, g₁ _ l0.1 l0.2.1, hptr _ k0, laneP_word])
      (by
        rw [u₂.wr, u₁.wr, w₁]
        obtain ⟨R, hR, hc⟩ := wr_lane hp hw k0 (d := n + 32 + 8 * j) (by have := hp.out_fit; simp only [str] at this ⊢; omega_using [this, hj8])
        exact ⟨R, hR, by rw [← laneP_word]; exact hc⟩) fun s₃ m₃ => ?_
    refine wp_str (a := oaddr σ n (2 * p + 1) j) ⟨by omega_using [hn8], by omega_using [hj8, hn]⟩
      (by rw [m₃.gpr, u₂.other _ l1.2.1, u₁.other _ l1.1, g₁ _ l1.1 l1.2.1, hptr _ k1, laneP_word])
      (by
        rw [m₃.wr, u₂.wr, u₁.wr, w₁]
        obtain ⟨R, hR, hc⟩ := wr_lane hp hw k1 (d := n + 32 + 8 * j) (by have := hp.out_fit; simp only [str] at this ⊢; omega_using [this, hj8])
        exact ⟨R, hR, by rw [← laneP_word]; exact hc⟩) fun s₄ m₄ => wp_nil ?_
    have v9 : s₃.gpr .x9 = (F (2 * p))[j]! := by
      rw [m₃.gpr, u₂.other _ (by decide), u₁.gpr, st₁ j (by omega_using [hj, hn]) _ k0]
    have v10 : s₃.gpr .x10 = (F (2 * p + 1))[j]! := by
      rw [m₃.gpr, u₂.gpr, eb', st₁ j (by omega_using [hj, hn]) _ k1]
    have mm : s₄.mem = (t₁.mem.writeW (oaddr σ n (2 * p) j) (F (2 * p))[j]!).writeW (oaddr σ n (2 * p + 1) j)
        (F (2 * p + 1))[j]! := by
      rw [m₄.mem, m₃.mem, v10, u₂.mem, u₁.mem, ← v9, m₃.gpr]
    have sep01 := out_sep hp k0 k1 hj8 hj8 (i := j) (i' := j) (.inl (by omega_using []))
    refine ⟨fun g h9 h10 => by rw [m₄.gpr, m₃.gpr, u₂.other _ h10, u₁.other _ h9, g₁ _ h9 h10],
      by rw [m₄.vec, m₃.vec, u₂.vec, u₁.vec, v₁], by rw [m₄.rd, m₃.rd, u₂.rd, u₁.rd, r₁],
      by rw [m₄.wr, m₃.wr, u₂.wr, u₁.wr, w₁], by rw [m₄.sp, m₃.sp, u₂.sp, u₁.sp, p₁], fun i hi => ?_, fun i hi => ?_, ?_⟩
    · rw [mm, Mem.readW_writeW_sep (out_sep hp k0 k1 (by omega_using [hi, hj8]) hj8 (.inl (by omega_using [])))
        (by decide)]
      by_cases c : i < j
      · rw [Mem.readW_writeW_sep (out_sep hp k0 k0 (by omega_using [hi, hj8]) hj8 (.inr (by omega_using [c])))
          (by decide), o₁ i c]
      · obtain rfl : i = j := by omega_using [hi, c]
        rw [Mem.readW_writeW_self64]
    · rw [mm]
      by_cases c : i < j
      · rw [Mem.readW_writeW_sep (out_sep hp k1 k1 (by omega_using [hi, hj8]) hj8 (.inr (by omega_using [c])))
          (by decide), Mem.readW_writeW_sep (out_sep hp k1 k0 (by omega_using [hi, hj8]) hj8 (.inl (by omega_using [])))
          (by decide), o₁' i c]
      · obtain rfl : i = j := by omega_using [hi, c]
        rw [Mem.readW_writeW_self64]
    · rw [mm]
      exact (f₁.writeW (List.mem_cons_self ..) _ (out_contains hp hn hj8)).writeW
        (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (out_contains hp hn hj8)

/-! ## The registers restored -/

theorem restore_eq : restore = ((List.range 8).map fun i => .ldr .x (sreg (i + 1)) .x19 (oSave + 8 * (i + 1))) ++
    ([.ldr .x .x19 .x19 oSave] : List Instr) := rfl

theorem sreg_ne : ∀ i < 8, sreg (i + 1) ≠ .x19 := by decide

theorem sreg_inj : ∀ i < 9, ∀ j < 9, sreg i = sreg j → i = j := by decide

theorem restores_ok (hp : Thash4Pre n σ) : ∀ j ≤ 8, ∀ t : State, t.gpr .x19 = W σ → t.wr = σ.wr →
    (∀ i < 9, t.mem.readW (W σ + BitVec.ofNat 64 (oSave + 8 * i)) 64 = σ.gpr (sreg i)) →
    WP isa (.block ((List.range j).map fun i => .ldr .x (sreg (i + 1)) .x19 (oSave + 8 * (i + 1)))) t fun t' =>
      (∀ i < j, t'.gpr (sreg (i + 1)) = σ.gpr (sreg (i + 1))) ∧
      (∀ g, (∀ i < j, g ≠ sreg (i + 1)) → t'.gpr g = t.gpr g) ∧
      t'.mem = t.mem ∧ t'.v = t.v ∧ t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.sp = t.sp := by
  intro j
  induction j with
  | zero => intro _ t _ _ _; exact wp_nil ⟨fun i hi => absurd hi (by omega_using []), fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ j ih =>
    intro hj t h19 hw hs
    rw [List.range_succ, List.map_append]
    refine WP.block_append (WP.mono (ih (by omega_using [hj]) t h19 hw hs) fun t₁ ⟨a₁, g₁, m₁, v₁, r₁, w₁, p₁⟩ => ?_)
    have x19 : t₁.gpr .x19 = W σ := by
      rw [g₁ _ fun i hi e => sreg_ne i (by omega_using [hi, hj]) e.symm, h19]
    refine wp_ldr (a := W σ + BitVec.ofNat 64 (oSave + 8 * (j + 1))) ⟨by simp only [oSave]; omega_using [],
      by simp only [oSave]; omega_using [hj]⟩ (by rw [x19]) (by rw [r₁, w₁]; exact rw_work hp hw (by
        simp only [oSave, workLen]; omega_using [hj])) fun t₂ u₂ => wp_nil ⟨fun i hi => ?_, fun g hg => ?_,
          by rw [u₂.mem, m₁], by rw [u₂.vec, v₁], by rw [u₂.rd, r₁], by rw [u₂.wr, w₁], by rw [u₂.sp, p₁]⟩
    · by_cases c : i < j
      · rw [u₂.other _ fun e => by have := sreg_inj _ (by omega_using [hi, hj]) _ (by omega_using [hj]) e; omega_using [this, c],
          a₁ i c]
      · obtain rfl : i = j := by omega_using [hi, c]
        rw [u₂.gpr, m₁, hs _ (by omega_using [hj])]
    · rw [u₂.other _ (hg j (by omega_using [])), g₁ _ fun i hi => hg i (by omega_using [hi])]

/-! ## Correctness -/

theorem outAt_eq (hp : Thash4Pre n σ) (k : Nat) : outAt σ k = inp σ + BitVec.ofNat 64 (k * str σ + (n + 32)) := by
  rw [outAt, hp.out_eq, addOf, Nat.add_comm]

theorem word_out_disj (hp : Thash4Pre n σ) {k k' i : Nat} (hk : k < 4) (hk' : k' < 4) (hne : k ≠ k')
    (hi : 8 * i + 8 ≤ n) : Region.Disjoint ⟨oaddr σ n k i, 8⟩ ⟨outAt σ k', n⟩ := by
  obtain ⟨a1, a2⟩ := out_off hp hk hi
  have hf := hp.out_fit
  have h2 := kstr_le (σ := σ) hk'
  rw [outAt_eq hp]
  simp only [str] at a1 a2
  refine Offset.disjoint _ ?_ (by simp only [str]; omega_using [a1, a2]) (by simp only [str] at hf h2 ⊢; omega_using [hf, h2, a2])
  rcases Nat.lt_or_gt_of_ne hne with c | c
  · have := Nat.mul_le_mul_right (str σ) (show k + 1 ≤ k' by omega_using [c])
    rw [Nat.succ_mul] at this; simp only [str] at hf this ⊢; omega_using [this, hf, hi]
  · have := Nat.mul_le_mul_right (str σ) (show k' + 1 ≤ k by omega_using [c])
    rw [Nat.succ_mul] at this; simp only [str] at hf this ⊢; omega_using [this, hf, hi]

theorem outW_frame (hp : Thash4Pre n σ) {F : Nat → KState} {m m' : Mem} {k : Nat} (hk : k < 4) {j : Nat}
    (hj : 8 * j ≤ n) (h : OutW σ n F m k j) {ks : List Nat} (hks : ∀ k' ∈ ks, k' < 4 ∧ k' ≠ k)
    (hf : Frame (ks.map fun k' => (⟨outAt σ k', n⟩ : Region)) m m') : OutW σ n F m' k j := fun i hi => by
  rw [readW_frame hf fun r hr => by
    obtain ⟨k', hk', rfl⟩ := List.mem_map.mp hr
    exact word_out_disj hp hk (hks k' hk').1 (hks k' hk').2.symm (by omega_using [hi, hj])]
  exact h i hi

theorem extract_eq (n : Nat) : extract n = (List.range (n / 8)).flatMap (fun i => [.ldp .x9 .x10 .x19 (oPair1 * 0 + 16 * i),
      .str .x .x9 (lanePtr (2 * 0)) (n + 32 + 8 * i), .str .x .x10 (lanePtr (2 * 0 + 1)) (n + 32 + 8 * i)]) ++
    (List.range (n / 8)).flatMap (fun i => [.ldp .x9 .x10 .x19 (oPair1 * 1 + 16 * i),
      .str .x .x9 (lanePtr (2 * 1)) (n + 32 + 8 * i), .str .x .x10 (lanePtr (2 * 1 + 1)) (n + 32 + 8 * i)]) := rfl

theorem bytes_out (hp : Thash4Pre n σ) (hn : n ≤ 32) {F : Nat → KState} {m : Mem} {k : Nat}
    (h : OutW σ n F m k (n / 8)) (hn8 : n % 8 = 0) (M : List Byte) (hF : F k = finalState M) :
    bytesAt m (outAt σ k) n = Spec.Sha3.shake256 M n := by
  refine Proof.SlhDsa.shake256_ext (by omega_using [hn]) (by simp [bytesAt]) fun j hj => ?_
  simp only [bytesAt, List.getElem_map, List.getElem_range]
  rw [show j = 8 * (j / 8) + j % 8 by omega_using [], ← addOf, outAt_word hp, byte_readW m _ (j := j % 8) (by omega_using []),
    h _ (by omega_using [hj, hn8]), hF]
  simp only [byteOf]
  rw [show (8 * (j / 8) + j % 8) / 8 = j / 8 by omega_using [], show (8 * (j / 8) + j % 8) % 8 = j % 8 by omega_using []]

theorem correct (hp : Thash4Pre n σ) (hn : n ≤ 32) (hn8 : n % 8 = 0) (sha3 : Bool) :
    WP isa (thash4 n sha3) σ fun s' => abiPreserved σ s' ∧ (thash4Contract n).post σ s' := by
  unfold thash4
  refine WP.seq (WP.mono (pro_ok hp) fun s₁ h₁ => WP.seq (WP.mono (loop_ok hp sha3 h₁) fun s₂ h₂ =>
    WP.seq (WP.mono (pad_ok hp h₂) fun s₃ h₃ => WP.seq ?_)))
  refine WP.mono (perm_ok hp sha3 h₃.wr h₃.x19 h₃.st) fun s₄ ⟨l₄, f₄, r₄, w₄, p₄, g₄, v₄⟩ => ?_
  have k4 : ∀ r, r ∉ volatile → s₄.gpr r = s₃.gpr r := g₄
  rw [extract_eq, List.append_assoc, WP.block_append_iff]
  have ptr₄ : ∀ k < 4, s₄.gpr (lanePtr k) = laneP σ k := fun k hk => by
    have hv : lanePtr k ∉ volatile := by
      rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_using [hk]) with rfl | rfl | rfl | rfl <;> decide
    rw [k4 _ hv, h₃.ptr k hk]
  have x19₄ : s₄.gpr .x19 = W σ := by rw [k4 _ (by decide), h₃.x19]
  have wr₄ : s₄.wr = σ.wr := by rw [w₄, h₃.wr]
  refine WP.mono (extractPair_ok hp hn hn8 (p := 0) (by decide) (n / 8) (Nat.le_refl _) s₄ x19₄ ptr₄ wr₄ l₄)
    fun s₅ ⟨g₅, v₅, r₅, w₅, p₅, o₅, o₅', f₅⟩ => ?_
  rw [WP.block_append_iff]
  have g₅' : ∀ g, g ≠ .x9 → g ≠ .x10 → s₅.gpr g = s₄.gpr g := g₅
  have st₅ : St4 s₅.mem (W σ) fun k => keccakF (padded (msg σ k)) := by
    refine st4_frame l₄ f₅ fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
    · refine ((hp.lanes_work.sub_left ?_).sub_right (Region.sub_prefix (by decide))).symm
      have hf := hp.out_fit
      rw [outAt_eq hp]
      exact Offset.sub_base _ (by simp only [str] at hf ⊢; omega_using [hf])
  refine WP.mono (extractPair_ok hp hn hn8 (p := 1) (by decide) (n / 8) (Nat.le_refl _) s₅
    (by rw [g₅' _ (by decide) (by decide), x19₄])
    (fun k hk => by obtain ⟨h9, h10, -⟩ := lanePtr_ne hk; rw [g₅' _ h9 h10, ptr₄ k hk]) (by rw [w₅, wr₄]) st₅)
    fun s₆ ⟨g₆, v₆, r₆, w₆, p₆, o₆, o₆', f₆⟩ => ?_
  rw [restore_eq, WP.block_append_iff]
  have g₆' : ∀ g, g ≠ .x9 → g ≠ .x10 → s₆.gpr g = s₅.gpr g := g₆
  have sv₆ : ∀ i < 9, s₆.mem.readW (W σ + BitVec.ofNat 64 (oSave + 8 * i)) 64 = σ.gpr (sreg i) := fun i hi => by
    have hs := sv_frame hp f₄ h₃.sv (sreg i, oSave + 8 * i) (by rw [saved_eq]; exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    have hd : ∀ m m' : Mem, Frame [⟨outAt σ 0, n⟩, ⟨outAt σ 1, n⟩] m m' ∨ Frame [⟨outAt σ 2, n⟩, ⟨outAt σ 3, n⟩] m m' →
        m'.readW (W σ + BitVec.ofNat 64 (oSave + 8 * i)) 64 = m.readW (W σ + BitVec.ofNat 64 (oSave + 8 * i)) 64 := by
      intro m m' hmm
      have hw : ∀ k < 4, Region.Disjoint ⟨W σ + BitVec.ofNat 64 (oSave + 8 * i), 8⟩ ⟨outAt σ k, n⟩ := fun k hk => by
        have hf := hp.out_fit
        have h2 := kstr_le (σ := σ) hk
        refine (hp.lanes_work.sub_left ?_).sub_right ?_ |>.symm
        · rw [outAt_eq hp]; exact Offset.sub_base _ (by simp only [str] at hf h2 ⊢; omega_using [hf, h2])
        · exact Offset.sub_base _ (by simp only [oSave, workLen]; omega_using [hi])
      rcases hmm with hmm | hmm
      · exact readW_frame hmm fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hw 0 (by decide)
          · exact hw 1 (by decide)
      · exact readW_frame hmm fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hw 2 (by decide)
          · exact hw 3 (by decide)
    rw [hd _ _ (.inr f₆), hd _ _ (.inl f₅)]; exact hs
  refine WP.mono (restores_ok hp 8 (Nat.le_refl _) s₆ (by rw [g₆' _ (by decide) (by decide), g₅' _ (by decide) (by decide), x19₄])
    (by rw [w₆, w₅, wr₄]) sv₆) fun s₇ ⟨a₇, k₇, m₇, v₇, r₇, w₇, p₇⟩ => ?_
  refine wp_ldr (a := W σ + BitVec.ofNat 64 oSave) ⟨by decide, by decide⟩
    (by rw [k₇ _ fun i hi e => sreg_ne i hi e.symm, g₆' _ (by decide) (by decide), g₅' _ (by decide) (by decide), x19₄])
    (by rw [r₇, r₆, r₅, r₄, h₃.rd, w₇, w₆, w₅, wr₄]; exact rw_work hp rfl (d := oSave) (k := 8) (by decide)) fun s₈ u₈ => wp_nil ?_
  -- the registers
  have kg : ∀ g, g ≠ .x9 → g ≠ .x10 → g ≠ .x19 → (∀ i < 8, g ≠ sreg (i + 1)) → g ∉ volatile →
      s₈.gpr g = s₃.gpr g := fun g h9 h10 h19 hs hv => by
    rw [u₈.other _ h19, k₇ _ hs, g₆' _ h9 h10, g₅' _ h9 h10, k4 _ hv]
  refine ⟨⟨fun r hr => ?_, by rw [u₈.sp, p₇, p₆, p₅, p₄, h₃.sp], fun r hr => by
      rw [u₈.vec, v₇, v₆, v₅, v₄ r hr, h₃.vk r hr]⟩, fun k hk => ?_, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [u₈.gpr, m₇]; exact sv₆ 0 (by decide)
    · rw [u₈.other _ (by decide)]; exact a₇ 0 (by decide)
    · rw [u₈.other _ (by decide)]; exact a₇ 1 (by decide)
    · rw [u₈.other _ (by decide)]; exact a₇ 2 (by decide)
    · rw [u₈.other _ (by decide)]; exact a₇ 3 (by decide)
    · rw [u₈.other _ (by decide)]; exact a₇ 4 (by decide)
    · rw [u₈.other _ (by decide)]; exact a₇ 5 (by decide)
    · rw [u₈.other _ (by decide)]; exact a₇ 6 (by decide)
    · rw [u₈.other _ (by decide)]; exact a₇ 7 (by decide)
    · rw [kg _ (by decide) (by decide) (by decide) (by decide) (by decide), h₃.x28]
    · rw [kg _ (by decide) (by decide) (by decide) (by decide) (by decide), h₃.x30]
  · have hm : s₈.mem = s₆.mem := by rw [u₈.mem, m₇]
    rw [hm]
    have o01 : ∀ k < 2, OutW σ n (fun k => keccakF (padded (msg σ k))) s₆.mem k (n / 8) := fun k hk => by
      rcases (show k = 0 ∨ k = 1 by omega_using [hk]) with rfl | rfl
      · exact outW_frame hp (by decide) (by omega_using []) o₅ (ks := [2, 3]) (by decide) f₆
      · exact outW_frame hp (by decide) (by omega_using []) o₅' (ks := [2, 3]) (by decide) f₆
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_using [hk]) with rfl | rfl | rfl | rfl
    · exact bytes_out hp hn (o01 0 (by decide)) hn8 _ rfl
    · exact bytes_out hp hn (o01 1 (by decide)) hn8 _ rfl
    · exact bytes_out hp hn o₆ hn8 _ rfl
    · exact bytes_out hp hn o₆' hn8 _ rfl
  · have hm : s₈.mem = s₆.mem := by rw [u₈.mem, m₇]
    rw [hm]
    have sub : ∀ (rs : List Region), (∀ r ∈ rs, r ∈ thash4Changes n σ) → ∀ {m m'}, Frame rs m m' →
        Frame (thash4Changes n σ) m m' := fun rs h _ _ f => f.mono h
    refine (sub _ ?_ h₃.frame).trans ((sub _ ?_ (frame936 f₄)).trans ((sub _ ?_ f₅).trans (sub _ ?_ f₆)))
    · intro r hr; rw [List.mem_singleton] at hr; subst hr; exact List.mem_append_right _ (List.mem_singleton_self _)
    · intro r hr; rw [List.mem_singleton] at hr; subst hr; exact List.mem_append_right _ (List.mem_singleton_self _)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact List.mem_append_left _ (out_mem (by decide))
      · exact List.mem_append_left _ (out_mem (by decide))
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact List.mem_append_left _ (out_mem (by decide))
      · exact List.mem_append_left _ (out_mem (by decide))

end VG.Proof.SlhDsa.AArch64.Thash4

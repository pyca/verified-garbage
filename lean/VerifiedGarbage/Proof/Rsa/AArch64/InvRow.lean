module
-- separate module: the rows build in parallel with the shifts (`InvShr`) and the reductions (`InvMred`)

public import VerifiedGarbage.Impl.Rsa.AArch64.Keys
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Rsa.AArch64.InvBase
import VerifiedGarbage.Proof.Divstep.RowWord
import VerifiedGarbage.Proof.Rsa.AArch64.Inv
import VerifiedGarbage.Proof.Rsa.AArch64.KeyLoops
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# RSA private keys on AArch64: the batched inverse's linear combinations

`rowP cv x y o`: `[o] := u [x] + v [y]` modulo `2^(64 (n + 1))`, `u` and `v`
the signed lanes of `cv` (`rowP_ok`), by `rowBody` a word at a time
(`rowWord_ok`, `Divstep.rowWord`), its invariant `LinInv`: the words stored
and the signed carry hold `u X + v Y` for the words read (`linStep_ok`).
`[o]` may be `[y]` (or `[x]`): each word is read before it is written.
-/

@[expose] public section

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.InvBatch
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- A word of `rowBody`: `x4 [x16] + x5 [x17] + x13`, its low word stored at
`x8` and its high word the next carry. -/
theorem rowWord_ok (s : State) {B : Addr} {Z eX eY eO : Nat} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B eX) (h17 : s.gpr .x17 = off B eY) (h8 : s.gpr .x8 = off B eO)
    (h9 : s.gpr .x9 = 0#64 - (s.gpr .x4 >>> 63)) (h10 : s.gpr .x10 = 0#64 - (s.gpr .x5 >>> 63))
    (hX : eX + 8 ≤ Z) (hY : eY + 8 ≤ Z) (hO : eO + 8 ≤ Z)
    (hb : (s.gpr .x4).toInt.natAbs + (s.gpr .x5).toInt.natAbs ≤ 2 ^ 62) (hc : (s.gpr .x13).toInt.natAbs ≤ 2 ^ 62) :
    WP isa (.block rowBody) s fun t => ∃ lo : BitVec 64, t.mem = s.mem.writeW (off B eO) lo ∧
      (lo.toNat : Int) + 2 ^ 64 * (t.gpr .x13).toInt = (s.gpr .x4).toInt * (word s.mem B eX).toNat +
        (s.gpr .x5).toInt * (word s.mem B eY).toNat + (s.gpr .x13).toInt ∧ (t.gpr .x13).toInt.natAbs ≤ 2 ^ 62 ∧
      t.gpr .x16 = off B (eX + 8) ∧ t.gpr .x17 = off B (eY + 8) ∧ t.gpr .x8 = off B (eO + 8) := by
  unfold rowBody
  brun [h16, h17, h8, h9, h10, hs.ld hX, hs.ld hY, hs.st hO, exec_sbc_x]
  refine ⟨_, rfl, ?_⟩
  have := Divstep.rowWord (s.gpr .x4) (s.gpr .x5) (word s.mem B eX) (word s.mem B eY) (s.gpr .x13) hb hc
  simp only [Bool.toNat_false, BitVec.add_zero, Nat.add_zero, word] at this ⊢
  exact this

/-- After `j` words of `rowBody`. -/
structure LinInv (s₀ : State) (B : Addr) (Z eX eY eO : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x1, .x2, .x3, .x6, .x7, .x8, .x13, .x14, .x16, .x17] s₀ t
  x16 : t.gpr .x16 = off B (eX + 8 * j)
  x17 : t.gpr .x17 = off B (eY + 8 * j)
  x8 : t.gpr .x8 = off B (eO + 8 * j)
  out : Outside B eO (8 * j) s₀.mem t.mem
  val : (wv t.mem B eO j : Int) + 2 ^ (64 * j) * (t.gpr .x13).toInt =
    (s₀.gpr .x4).toInt * wv s₀.mem B eX j + (s₀.gpr .x5).toInt * wv s₀.mem B eY j + (s₀.gpr .x13).toInt
  cb : (t.gpr .x13).toInt.natAbs ≤ 2 ^ 62

theorem linStep_ok {s₀ : State} {B : Addr} {Z L eX eY eO : Nat}
    (h9 : s₀.gpr .x9 = 0#64 - (s₀.gpr .x4 >>> 63)) (h10 : s₀.gpr .x10 = 0#64 - (s₀.gpr .x5 >>> 63))
    (hb : (s₀.gpr .x4).toInt.natAbs + (s₀.gpr .x5).toInt.natAbs ≤ 2 ^ 62)
    (hX : eX + 8 * L ≤ Z) (hY : eY + 8 * L ≤ Z) (hO : eO + 8 * L ≤ Z)
    (sX : eO ≤ eX ∨ eX + 8 * L ≤ eO) (sY : eO ≤ eY ∨ eY + 8 * L ≤ eO)
    {j : Nat} (hj : j < L) {t : State} (hI : LinInv s₀ B Z eX eY eO j t) :
    WP isa (.block (rowBody ++ ([.subImm .x .x14 .x14 1] : List Instr))) t fun t' =>
      LinInv s₀ B Z eX eY eO (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have k4 : t.gpr .x4 = s₀.gpr .x4 := hI.keep.gpr .x4 (by decide)
  have k5 : t.gpr .x5 = s₀.gpr .x5 := hI.keep.gpr .x5 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x1, .x2, .x3, .x6, .x7, .x8, .x13, .x16, .x17] (rowWord_ok t hI.scr hI.x16 hI.x17 hI.x8
    (by rw [hI.keep.gpr .x9 (by decide), k4, h9]) (by rw [hI.keep.gpr .x10 (by decide), k5, h10])
    (by omega) (by omega) (by omega) (by rw [k4, k5]; exact hb) hI.cb)
    (by decide) (by decide) (by decide +kernel)) fun t₁ ⟨⟨lo, hm, hv, hcb, h16, h17, h8⟩, k₁⟩ => ?_
  refine WP.mono (dec_ok t₁ .x14) fun t' ⟨⟨h14, hm', _⟩, k'⟩ => ⟨?_, by rw [h14, k₁.gpr .x14 (by decide)]⟩
  have hmem : t'.mem = t.mem.writeW (off B (eO + 8 * j)) lo := hm'.trans hm
  have hx : word t.mem B (eX + 8 * j) = word s₀.mem B (eX + 8 * j) :=
    hI.out.word (by omega) (by omega)
  have hy : word t.mem B (eY + 8 * j) = word s₀.mem B (eY + 8 * j) :=
    hI.out.word (by omega) (by omega)
  have e13 : t'.gpr .x13 = t₁.gpr .x13 := k'.gpr .x13 (by decide)
  refine ⟨hI.scr.congr (k'.wr.trans k₁.wr), (hI.keep.trans (k₁.trans k')).mono (by decide),
    by rw [k'.gpr .x16 (by decide), h16, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x17 (by decide), h17, Nat.mul_succ, Nat.add_assoc],
    by rw [k'.gpr .x8 (by decide), h8, Nat.mul_succ, Nat.add_assoc], ?_, ?_, by rw [e13]; exact hcb⟩
  · rw [hmem]
    refine fun x hx' => ?_
    rw [writeW_outside t.mem B lo (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hmem, wv_writeW_top _ _ _ _ _ (by omega), e13]
    simp only [wv]
    rw [hx, hy, k4, k5] at hv
    have hval := hI.val
    have e : (2 : Int) ^ (64 * (j + 1)) = 2 ^ (64 * j) * 2 ^ 64 := by rw [Nat.mul_succ, Int.pow_add]
    rw [e]
    push_cast
    have hv' := congrArg (fun z => (2 : Int) ^ (64 * j) * z) hv
    simp only [Int.mul_add] at hv'
    grind

/-- `rowBody`'s loop over `L` words, from the carry `x13 = 0`. -/
theorem linLoop_ok {s : State} {B : Addr} {Z L eX eY eO : Nat} (hs : Scr s B Z)
    (h16 : s.gpr .x16 = off B eX) (h17 : s.gpr .x17 = off B eY) (h8 : s.gpr .x8 = off B eO)
    (h9 : s.gpr .x9 = 0#64 - (s.gpr .x4 >>> 63)) (h10 : s.gpr .x10 = 0#64 - (s.gpr .x5 >>> 63))
    (h13 : s.gpr .x13 = 0) (h14 : s.gpr .x14 = BitVec.ofNat 64 L) (hL : 1 ≤ L) (hL' : L < 2 ^ 32)
    (hb : (s.gpr .x4).toInt.natAbs + (s.gpr .x5).toInt.natAbs ≤ 2 ^ 62)
    (hX : eX + 8 * L ≤ Z) (hY : eY + 8 * L ≤ Z) (hO : eO + 8 * L ≤ Z)
    (sX : eO ≤ eX ∨ eX + 8 * L ≤ eO) (sY : eO ≤ eY ∨ eY + 8 * L ≤ eO) :
    WP isa (countLoop .x14 rowBody) s (LinInv s B Z eX eY eO L) := by
  have hn := hs.nowrap
  have h0 : LinInv s B Z eX eY eO 0 s :=
    ⟨hs, Keep.refl _ _, by rw [h16]; rfl, by rw [h17]; rfl, by rw [h8]; rfl, Outside.refl _ _ _ _,
      by simp [wv], by rw [h13]; decide⟩
  exact wp_countdown (N := L) (by omega) (by omega) (LinInv s B Z eX eY eO)
    (fun j hj t hI _ => linStep_ok h9 h10 hb hX hY hO sX sY hj hI) h0 h14

/-- `rowP`'s start: the coefficients from `cv` and their sign masks. -/
theorem rowHead_ok (s : State) {cv : VReg} (hcv : cv = .v16 ∨ cv = .v17) :
    WP isa (.block (([.umov .x .x4 cv 0, .umov .x .x5 cv 1] : List Instr) ++ coefMasks)) s fun t =>
      (t.gpr .x4 = (s.v cv).extractLsb' 0 64 ∧ t.gpr .x5 = (s.v cv).extractLsb' 64 64 ∧
        t.gpr .x9 = 0#64 - (t.gpr .x4 >>> 63) ∧ t.gpr .x10 = 0#64 - (t.gpr .x5 >>> 63) ∧ t.mem = s.mem ∧
        t.v = s.v) ∧ Keep [.x4, .x5, .x9, .x10, .x13] s t := by
  rcases hcv with rfl | rfl <;>
  · refine WP.keep [.x4, .x5, .x9, .x10, .x13] ?_ (by decide) (by decide) (by decide +kernel)
    unfold coefMasks
    brun [exec_umov_x, RegUpd.v_write, Nat.mul_zero, Nat.mul_one, show BitVec.setWidth 64 0#16 = 0#64 from rfl]

/-- `rowP cv x y o`: `[o] := u [x] + v [y]` modulo `2^(64 (n + 1))`, for the
signed lanes `u`, `v` of `cv`. -/
theorem rowP_ok {s : State} {B : Addr} {Z w n : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (8 * (w + 2))) (h12 : s.gpr .x12 = BitVec.ofNat 64 n)
    (hn : n ≤ w) (hw : w < 2 ^ 24) (hZ : slot w 16 ≤ Z) {cv : VReg} (hcv : cv = .v16 ∨ cv = .v17)
    {iX iY iO : Nat} (hX : iX < 16) (hY : iY < 16) (hO : iO < 16)
    (hb : ((s.v cv).extractLsb' 0 64).toInt.natAbs + ((s.v cv).extractLsb' 64 64).toInt.natAbs ≤ 2 ^ 62) :
    WP isa (rowP cv iX iY iO) s fun t => ∃ c : Int,
      (wv t.mem B (slot w iO) (n + 1) : Int) + 2 ^ (64 * (n + 1)) * c =
        ((s.v cv).extractLsb' 0 64).toInt * wv s.mem B (slot w iX) (n + 1) +
        ((s.v cv).extractLsb' 64 64).toInt * wv s.mem B (slot w iY) (n + 1) ∧
      Outside B (slot w iO) (8 * (n + 1)) s.mem t.mem ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x13, .x14, .x16, .x17] s t ∧ t.v = s.v := by
  have hn' := hs.nowrap
  have sl : ∀ j < 16, slot w j + 8 * (w + 2) ≤ Z := fun j hj =>
    Nat.le_trans (slot_lt (w := w) hj) hZ
  have sep : ∀ j k, slot w j ≤ slot w k ∨ slot w k + 8 * (n + 1) ≤ slot w j := fun j k => by
    by_cases h : j = k
    · subst h; exact .inl (Nat.le_refl _)
    · rcases slot_sep (w := w) h with h' | h' <;> [exact .inl (by omega); exact .inr (by omega)]
  have hvn : (rowP cv iX iY iO).allInstrs (fun i => (vdstOf i).isNone) = true := by
    rcases hcv with rfl | rfl <;>
    · simp only [rowP, Code.allInstrs_eq, instrs, List.all_append, base_vnone]; decide
  suffices h : WP isa (rowP cv iX iY iO) s fun t => ∃ c : Int,
      (wv t.mem B (slot w iO) (n + 1) : Int) + 2 ^ (64 * (n + 1)) * c =
        ((s.v cv).extractLsb' 0 64).toInt * wv s.mem B (slot w iX) (n + 1) +
        ((s.v cv).extractLsb' 64 64).toInt * wv s.mem B (slot w iY) (n + 1) ∧
      Outside B (slot w iO) (8 * (n + 1)) s.mem t.mem ∧
      Keep [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x13, .x14, .x16, .x17] s t from
    WP.mono (WP.vfix h hvn) fun t ⟨⟨c, e, o, k⟩, v⟩ => ⟨c, e, o, k, v⟩
  unfold rowP
  rw [show ([Instr.umov .x .x4 cv 0, .umov .x .x5 cv 1] ++ coefMasks ++ base iX .x16 ++ base iY .x17 ++
      base iO .x8 ++ ([cntL, movi .x13 0] : List Instr)) = ([Instr.umov .x .x4 cv 0, .umov .x .x5 cv 1] ++ coefMasks) ++
      (base iX .x16 ++ base iY .x17 ++ base iO .x8) ++ ([cntL, movi .x13 0] : List Instr) by simp]
  refine WP.seq (WP.block_append_iff.mpr (WP.block_append_iff.mpr (WP.mono (rowHead_ok s hcv)
    fun s₁ ⟨⟨h4, h5, h9, h10, m₁, v₁⟩, k₁⟩ => WP.mono (base3_ok iX iY iO .x16 .x17 .x8
      ((k₁.gpr .x0 (by decide)).trans h0) ((k₁.gpr .x11 (by decide)).trans h11))
    fun s₂ ⟨⟨h16, h17, h8, m₂, _⟩, k₂⟩ => WP.mono (WP.keep [.x13, .x14] (Q := fun t =>
      t.gpr .x13 = 0 ∧ t.gpr .x14 = BitVec.ofNat 64 (n + 1) ∧ t.mem = s₂.mem)
      (by brun [((k₁.trans k₂).gpr .x12 (by decide)).trans h12, cntL]; exact BitVec.ofNat_add_ofNat (n := 64) n 1) (by decide) (by decide) (by decide +kernel))
    fun s₃ ⟨⟨h13, h14, m₃⟩, k₃⟩ => ?_)))
  have k23 := k₂.trans k₃
  have e4 : s₃.gpr .x4 = (s.v cv).extractLsb' 0 64 := (k23.gpr .x4 (by decide)).trans h4
  have e5 : s₃.gpr .x5 = (s.v cv).extractLsb' 64 64 := (k23.gpr .x5 (by decide)).trans h5
  have hm : s₃.mem = s.mem := m₃.trans (m₂.trans m₁)
  refine WP.mono (linLoop_ok (hs.congr (k₁.trans k23).wr) ((k₃.gpr .x16 (by decide)).trans h16)
    ((k₃.gpr .x17 (by decide)).trans h17) ((k₃.gpr .x8 (by decide)).trans h8)
    (by rw [k23.gpr .x9 (by decide), h9, k23.gpr .x4 (by decide)])
    (by rw [k23.gpr .x10 (by decide), h10, k23.gpr .x5 (by decide)]) h13 h14 (by omega) (by omega)
    (by rw [e4, e5]; exact hb) (by have := sl iX hX; omega) (by have := sl iY hY; omega)
    (by have := sl iO hO; omega) (sep iO iX) (sep iO iY)) fun t hI => ⟨(t.gpr .x13).toInt, ?_, ?_, ?_⟩
  · have := hI.val
    rw [e4, e5, hm, h13] at this
    simpa using this
  · rw [← hm]; exact hI.out
  · exact ((k₁.trans k23).trans hI.keep).mono (by decide)
end VG.Proof.Rsa.AArch64

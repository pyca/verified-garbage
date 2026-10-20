module
public import VerifiedGarbage.Impl.Dsa.AArch64.Random
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
public import VerifiedGarbage.Proof.Framework.Contract

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Public tape bounds and status writes for a scalar draw. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64 VG.Impl.Bignum.AArch64

private theorem sub_nat {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem random_drawHead_ok {s : State} {B : Addr} {len used width : Nat}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (hl : word s.mem B Random.oRandLen = BitVec.ofNat 64 len)
    (hu : word s.mem B Random.oUsed = BitVec.ofNat 64 used)
    (hw : word s.mem B Random.oWidth = BitVec.ofNat 64 width)
    (hused : used ≤ len) (hlen : len < 2 ^ 64) (hwidth : width < 2 ^ 64) :
    WP isa (.block [.ldrSp .x0 Random.oRandLen, .ldrSp .x4 Random.oUsed,
      .sub .x .x0 .x0 .x4, .ldrSp .x4 Random.oWidth, .subs .x .x3 .x0 .x4,
      movi .x0 0, movi .x4 1, .csel .x .x3 .x0 .x4]) s fun t =>
      t.gpr .x3 = BitVec.ofNat 64 (if len - used < width then 1 else 0) ∧
      t.mem = s.mem ∧ Keep [.x0, .x3, .x4] s t := by
  refine WP.mono (WP.keep [.x0, .x3, .x4] (Q := fun t =>
      t.gpr .x3 = BitVec.ofNat 64 (if len - used < width then 1 else 0) ∧ t.mem = s.mem)
      ?_ rfl rfl rfl) fun _ ⟨⟨hc, hm⟩, hk⟩ => ⟨hc, hm, hk⟩
  have hcarry : decide (2 ^ 64 ≤ (len - used) + (~~~(BitVec.ofNat 64 width)).toNat + 1) =
      decide (width ≤ len - used) := by
    simp only [BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwidth]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  brun [exec_ldrSp (show Random.oRandLen % 8 = 0 ∧ Random.oRandLen < 32768 by decide),
    exec_ldrSp (show Random.oUsed % 8 = 0 ∧ Random.oUsed < 32768 by decide),
    exec_ldrSp (show Random.oWidth % 8 = 0 ∧ Random.oWidth < 32768 by decide),
    hsp, hs.ld (d := Random.oRandLen) (by decide), hs.ld (d := Random.oUsed) (by decide),
    hs.ld (d := Random.oWidth) (by decide), hl, hu, hw, sub_nat hused,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show len - used < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt hwidth, Bool.toNat_true, hcarry, decide_eq_true_eq]
  by_cases h : len - used < width <;>
    simp (disch := omega) only [ite_eq_left, ite_eq_right] <;> rfl


theorem random_status_ok {s : State} {B : Addr} (v : Nat)
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B) :
    WP isa (.block (([movi .x0 v] : List Instr) ++ Random.store Random.oStatus .x0)) s fun t =>
      t.gpr .x0 = (BitVec.ofNat 16 v).setWidth 64 ∧
      t.mem = s.mem.writeW (off B Random.oStatus) ((BitVec.ofNat 16 v).setWidth 64) ∧
      Keep [.x0, .x15] s t := by
  refine WP.mono (WP.keep [.x0, .x15] (Q := fun t =>
      t.gpr .x0 = (BitVec.ofNat 16 v).setWidth 64 ∧
      t.mem = s.mem.writeW (off B Random.oStatus) ((BitVec.ofNat 16 v).setWidth 64))
      ?_ rfl rfl rfl) fun _ ⟨⟨ha, hm⟩, hk⟩ => ⟨ha, hm, hk⟩
  unfold Random.store
  brun [exec_addSp (show Random.oStatus < 4096 by decide), hsp,
    hs.st (d := Random.oStatus) (by decide)]


theorem random_draw_short_ok {s : State} {B : Addr} {len used width : Nat}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (hl : word s.mem B Random.oRandLen = BitVec.ofNat 64 len)
    (hu : word s.mem B Random.oUsed = BitVec.ofNat 64 used)
    (hw : word s.mem B Random.oWidth = BitVec.ofNat 64 width)
    (hused : used ≤ len) (hlen : len < 2 ^ 64) (hwidth : width < 2 ^ 64)
    (hshort : len - used < width) :
    WP isa Random.draw s fun t =>
      t.gpr .x0 = 2 ∧ t.mem = s.mem.writeW (off B Random.oStatus) (2 : BitVec 64) ∧
      Keep [.x0, .x3, .x4, .x15] s t := by
  unfold Random.draw
  refine WP.seq (WP.mono (random_drawHead_ok hs hsp hl hu hw hused hlen hwidth)
    fun u ⟨huc, hum, hku⟩ => ?_)
  refine WP.ite true (by simp [eval, State.read, huc, hshort]) (fun _ => ?_)
    (fun h => Bool.noConfusion h)
  refine WP.mono (random_status_ok 2 (hs.congr hku.wr) (hku.sp.trans hsp))
    fun t ⟨hta, htm, hkt⟩ => ?_
  exact ⟨hta, by rw [htm, hum]; rfl, (hku.trans hkt).mono (by decide)⟩

theorem random_used_ok {s : State} {B : Addr} {used width : Nat}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (hu : word s.mem B Random.oUsed = BitVec.ofNat 64 used)
    (hw : word s.mem B Random.oWidth = BitVec.ofNat 64 width) :
    WP isa (.block (([.ldrSp .x0 Random.oUsed, .ldrSp .x4 Random.oWidth,
      .add .x .x0 .x0 .x4] : List Instr) ++ Random.store Random.oUsed .x0)) s fun t =>
      t.mem = s.mem.writeW (off B Random.oUsed) (BitVec.ofNat 64 (used + width)) ∧
      Keep [.x0, .x4, .x15] s t := by
  refine WP.keep [.x0, .x4, .x15] (Q := fun t =>
    t.mem = s.mem.writeW (off B Random.oUsed) (BitVec.ofNat 64 (used + width))) ?_ rfl rfl rfl
  unfold Random.store
  brun [exec_ldrSp (show Random.oUsed % 8 = 0 ∧ Random.oUsed < 32768 by decide),
    exec_ldrSp (show Random.oWidth % 8 = 0 ∧ Random.oWidth < 32768 by decide),
    exec_addSp (show Random.oUsed < 4096 by decide), hsp,
    hs.ld (d := Random.oUsed) (by decide), hs.ld (d := Random.oWidth) (by decide),
    hs.st (d := Random.oUsed) (by decide), hu, hw, BitVec.ofNat_add_ofNat]

def randomDrawFinishMem (m : Mem) (B : Addr) (accept : Bool) (draws : Nat) : Mem :=
  if accept then m.writeW (off B Random.oStatus) (1 : BitVec 64)
  else
    let m' := m.writeW (off B Random.oDraws) (BitVec.ofNat 64 (draws - 1))
    if draws = 1 then m'.writeW (off B Random.oStatus) (0 : BitVec 64) else m'

theorem random_decrement_ok {s : State} {B : Addr} {draws : Nat}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (hd : word s.mem B Random.oDraws = BitVec.ofNat 64 draws)
    (hpos : 0 < draws) (hbound : draws < 2 ^ 64) :
    WP isa (.block (([.ldrSp .x0 Random.oDraws, .subImm .x .x0 .x0 1] : List Instr) ++
      Random.store Random.oDraws .x0)) s fun t =>
      t.gpr .x0 = BitVec.ofNat 64 (draws - 1) ∧
      t.mem = s.mem.writeW (off B Random.oDraws) (BitVec.ofNat 64 (draws - 1)) ∧
      Keep [.x0, .x15] s t := by
  have hp : BitVec.ofNat 64 draws - 1#64 = BitVec.ofNat 64 (draws - 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  refine WP.mono (WP.keep [.x0, .x15] (Q := fun t =>
      t.gpr .x0 = BitVec.ofNat 64 (draws - 1) ∧
      t.mem = s.mem.writeW (off B Random.oDraws) (BitVec.ofNat 64 (draws - 1))) ?_ rfl rfl rfl)
    fun _ ⟨⟨ha, hm⟩, hk⟩ => ⟨ha, hm, hk⟩
  unfold Random.store
  brun [exec_ldrSp (show Random.oDraws % 8 = 0 ∧ Random.oDraws < 32768 by decide),
    exec_addSp (show Random.oDraws < 4096 by decide), hsp,
    hs.ld (d := Random.oDraws) (by decide), hs.st (d := Random.oDraws) (by decide), hd, hp]

/-- Rejection consumes one unit of fuel; only exhausting it changes status. -/
theorem random_drawFinish_ok {s : State} {B : Addr} {draws : Nat} {accept : Bool}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B)
    (hd : word s.mem B Random.oDraws = BitVec.ofNat 64 draws)
    (hz : s.gpr .x8 = BitVec.ofNat 64 (if accept then 1 else 0)) (hpos : 0 < draws) (hbound : draws < 2 ^ 64) :
    WP isa Random.drawFinish s fun t =>
      t.mem = randomDrawFinishMem s.mem B accept draws ∧ Keep [.x0, .x15] s t := by
  unfold Random.drawFinish
  cases accept with
  | true =>
    refine WP.ite true (by simp [eval, State.read, hz])
      (fun _ => ?_) (fun h => Bool.noConfusion h)
    exact WP.mono (random_status_ok 1 hs hsp) fun _ ⟨_, hm, hk⟩ => ⟨hm, hk⟩
  | false =>
    refine WP.ite false (by simp [eval, State.read, hz])
      (fun h => Bool.noConfusion h) (fun _ => ?_)
    refine WP.seq (WP.mono (random_decrement_ok hs hsp hd hpos hbound)
      fun u ⟨hua, hum, hku⟩ => ?_)
    have hus := hs.congr hku.wr
    have husp := hku.sp.trans hsp
    by_cases hd1 : draws = 1
    · refine WP.ite true (by simp [eval, State.read, hua, hd1]) (fun _ => ?_)
        (fun h => Bool.noConfusion h)
      have hua0 : u.gpr .x0 = 0 := by rw [hua, hd1]; rfl
      refine WP.mono (WP.keep [.x15] (Q := fun t =>
        t.mem = u.mem.writeW (off B Random.oStatus) (0 : BitVec 64))
        (by unfold Random.store; brun [exec_addSp (show Random.oStatus < 4096 by decide),
          husp, hus.st (d := Random.oStatus) (by decide), hua0]) rfl rfl rfl)
        fun t ⟨htm, hkt⟩ => ?_
      exact ⟨by rw [htm, hum]; simp only [randomDrawFinishMem, Bool.false_eq_true,
        ite_false, hd1, ite_true], (hku.trans hkt).mono (by decide)⟩
    · refine WP.ite false (by
        simp only [eval, State.read, hua, BitVec.setWidth_eq]
        change some (BitVec.ofNat 64 (draws - 1) == 0#64) = some false
        rw [show (BitVec.ofNat 64 (draws - 1) == 0#64) = false from by
          simp only [beq_eq_false_iff_ne]
          intro he
          have hh := congrArg BitVec.toNat he
          simp only [BitVec.toNat_ofNat] at hh
          omega])
        (fun h => Bool.noConfusion h) (fun _ => WP.block_nil ?_)
      exact ⟨by rw [hum]; simp only [randomDrawFinishMem, Bool.false_eq_true,
        ite_false, hd1], hku⟩

theorem random_drawFinish_outside (m : Mem) (B : Addr) (accept : Bool) (draws : Nat) :
    Outside B 160 40 m (randomDrawFinishMem m B accept draws) := by
  cases accept with
  | true => exact (writeW_outside _ B _ (by decide)).mono (by decide) (by decide)
  | false =>
    unfold randomDrawFinishMem
    simp only [Bool.false_eq_true, ite_false]
    split
    · exact ((writeW_outside _ B _ (by decide)).mono (by decide) (by decide)).trans
        ((writeW_outside _ B _ (by decide)).mono (by decide) (by decide))
    · exact (writeW_outside _ B _ (by decide)).mono (by decide) (by decide)

theorem random_drawFinish_status (m : Mem) (B : Addr) (accept : Bool) (draws : Nat) :
    word (randomDrawFinishMem m B accept draws) B Random.oStatus =
      if accept then 1 else if draws = 1 then 0 else word m B Random.oStatus := by
  cases accept with
  | true => exact word_writeW_self _ _ _ _
  | false =>
    simp only [randomDrawFinishMem, Bool.false_eq_true, ite_false]
    split
    · exact word_writeW_self _ _ _ _
    · exact (writeW_outside _ B _ (by decide)).word (by decide) (by decide)

theorem random_drawFinish_draws (m : Mem) (B : Addr) (accept : Bool) (draws : Nat) :
    word (randomDrawFinishMem m B accept draws) B Random.oDraws =
      if accept then word m B Random.oDraws else BitVec.ofNat 64 (draws - 1) := by
  cases accept with
  | true => exact (writeW_outside _ B _ (by decide)).word (by decide) (by decide)
  | false =>
    simp only [randomDrawFinishMem, Bool.false_eq_true, ite_false]
    split
    · rw [(writeW_outside _ B _ (by decide)).word (by decide) (by decide), word_writeW_self]
    · exact word_writeW_self _ _ _ _

theorem random_drawFinish_word (m : Mem) (B : Addr) (accept : Bool) (draws d : Nat)
    (hd : d + 8 ≤ 2 ^ 64)
    (hd1 : d + 8 ≤ 160 ∨ 168 ≤ d) (hd2 : d + 8 ≤ 192 ∨ 200 ≤ d) :
    word (randomDrawFinishMem m B accept draws) B d = word m B d := by
  cases accept with
  | true => exact (writeW_outside _ B _ (by decide)).word hd2 hd
  | false =>
    simp only [randomDrawFinishMem, Bool.false_eq_true, ite_false]
    split
    · exact ((writeW_outside _ B (d := Random.oStatus) (0 : BitVec 64) (by decide)).word hd2 hd).trans
        ((writeW_outside _ B (d := Random.oDraws) (BitVec.ofNat 64 (draws - 1)) (by decide)).word hd1 hd)
    · exact (writeW_outside _ B _ (by decide)).word hd1 hd

end VG.Proof.Dsa.AArch64

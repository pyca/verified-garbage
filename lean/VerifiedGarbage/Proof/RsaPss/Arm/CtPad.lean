module

public import VerifiedGarbage.Proof.RsaPss.Arm.CtLen
import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Aes.KeyExp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
meta import VerifiedGarbage.Proof.RsaPss.Arm.CtLen
meta import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Common
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.RsaPkcs1Sig.Arm.Mem
meta import VerifiedGarbage.Proof.Framework.Arm.RegUpd
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Aes.KeyExp
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.RsaPss.Arm.Step
meta import VerifiedGarbage.Proof.RsaPss.Arm.Step

/-!
# RSASSA-PSS on ARMv7: hashing, the padding of a message of secret length

`pad_vp`: the padding loop leaves `padY` in `Y`'s `nbm` blocks: `0x80` in
byte `ℓ` and the block at `oLen` ORed into the last block of the padded
message, each through a mask computed without a branch (`eqBit`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.Arm

open VG VG.Arm VG.Impl.RsaPss.Arm VG.Proof.RsaPkcs1Sig.Arm
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.X25519.Arm (dpVal)

/-! ## Masks -/

/-- `((a ⊕ b) - 1) >> 31`: 1 if `a = b`, 0 otherwise, for `a, b < 2^31`. -/
theorem eqBit {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    ((BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 b) - 1) >>> 31 = if a = b then 1 else 0 := by
  by_cases h : a = b
  · subst h; rw [BitVec.xor_self, ite_eq_left rfl]; decide
  · rw [ite_eq_right h]
    have hx : (BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 b).toNat < 2 ^ 31 := by
      rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
      exact Nat.xor_lt_two_pow ha hb
    have hn : (BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 b).toNat ≠ 0 := fun e => h (by
      have : BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 b = 0#32 := BitVec.eq_of_toNat_eq (by simpa using e)
      have := BitVec.xor_eq_zero_iff.mp this
      have := congrArg BitVec.toNat this
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this)
    generalize BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 b = x at hx hn
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
    have h1 : (1 : BitVec 32).toNat = 1 := rfl
    rw [h1, show (2 ^ 32 - 1 + x.toNat) % 2 ^ 32 = x.toNat - 1 by omega]
    show (x.toNat - 1) / 2 ^ 31 = 0
    exact Nat.div_eq_of_lt (by omega)

/-- The byte the padding loop stores. -/
theorem padByte (b l : Byte) (c d : Prop) [Decidable c] [Decidable d] :
    ((b.setWidth 32 ||| (if c then (1 : BitVec 32) else 0) <<< 7) |||
        (l.setWidth 32 &&& (0 - if d then (1 : BitVec 32) else 0))).setWidth 8 =
      b ||| (if c then 0x80 else 0) ||| (if d then l else 0) := by
  have e1 : ∀ x : BitVec 8, (x.setWidth 32).setWidth 8 = x := fun x => by simp
  have e2 : ((1 : BitVec 32) <<< 7).setWidth 8 = 0x80 := by decide
  have e3 : ((0 : BitVec 32) <<< 7).setWidth 8 = 0 := by decide
  have e4 : ((0 : BitVec 32) - 1).setWidth 8 = BitVec.allOnes 8 := by decide
  have e5 : ((0 : BitVec 32) - 0).setWidth 8 = 0 := by decide
  by_cases hc : c <;> by_cases hd : d <;> simp only [hc, hd, BitVec.setWidth_or, BitVec.setWidth_and, e1, e2, e3, e4,
    e5, ite_true, ite_false, BitVec.and_allOnes] <;> simp

theorem ofNat_and_mask {k B : Nat} (hB : B = 64 ∨ B = 128) (hk : k < 2 ^ 32) :
    BitVec.ofNat 32 k &&& BitVec.ofNat 32 (B - 1) = BitVec.ofNat 32 (k % B) := by
  rcases hB with rfl | rfl
  · have := VG.Proof.MdStream.Arm.and_pow_sub_one (BitVec.ofNat 32 k) (n := 6) (by decide)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this; exact this
  · have := VG.Proof.MdStream.Arm.and_pow_sub_one (BitVec.ofNat 32 k) (n := 7) (by decide)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this; exact this

variable {L : Lay} {scr : BitVec 32} (h : PssHash)

/-! ## The loop -/

/-- After `k` bytes of the padding loop. -/
structure PI (scr : BitVec 32) (T : Nat) (msg : List Byte) (k : Nat) (s : State) : Prop where
  r0 : s.gpr .r0 = scr + BitVec.ofNat 32 (oY + k)
  r1 : s.gpr .r1 = BitVec.ofNat 32 k
  lr : s.gpr .lr = BitVec.ofNat 32 (T - k)
  r4 : s.gpr .r4 = BitVec.ofNat 32 msg.length
  r5 : s.gpr .r5 = BitVec.ofNat 32 ((msg.length + h.L) / h.B)
  r6 : s.gpr .r6 = scr + BitVec.ofNat 32 oLen
  r7 : s.gpr .r7 = 0
  r9 : s.gpr .r9 = BitVec.ofNat 32 (h.B - 1)
  lb : LB h scr msg.length s.mem
  y : ∀ i < T, s.mem (sa scr (oY + i)) =
    if i < k then padY h.B h.L msg (h.md.lenBytes msg.length) i else msg.getD i 0

theorem padBody_taint : ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r1, .lr, .r6, .r7, .r9])
    (.block (padBody h.H)) hc).isSome = true := by
  rcases h.lg with ⟨e, -⟩ | ⟨e, -⟩ <;> simp only [padBody, e] <;> exact ⟨_, by taint_decide⟩

/-- One byte. -/
theorem padStep (hg : Geo L scr) {σ : State} {T : Nat} (hnb : T ≤ 2048) {msg : List Byte}
    (hfit : msg.length + 1 + h.L ≤ T) {k : Nat} (hk : k < T) {s : State}
    (hs : L.St σ s) (hp : PI h scr T msg k s) :
    WP isa (.block (padBody h.H)) s fun t =>
      t.mem = s.mem.writeW (sa scr (oY + k)) (padY h.B h.L msg (h.md.lenBytes msg.length) k) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.gpr .r0 = scr + BitVec.ofNat 32 (oY + (k + 1)) ∧
      t.gpr .r1 = BitVec.ofNat 32 (k + 1) ∧ t.gpr .lr = BitVec.ofNat 32 (T - (k + 1)) ∧
      t.gpr .r4 = s.gpr .r4 ∧ t.gpr .r5 = s.gpr .r5 ∧ t.gpr .r6 = s.gpr .r6 ∧ t.gpr .r7 = s.gpr .r7 ∧
      t.gpr .r9 = s.gpr .r9 ∧ t.z = decide (T - (k + 1) = 0) := by
  have hBl := h.B_le
  have hB64 := h.B_ge
  have hL := h.L_le
  have fit := hg.fit
  have hkB := Nat.mod_lt k (show 0 < h.B by omega)
  have aY : State.addr (scr + BitVec.ofNat 32 (oY + k)) = sa scr (oY + k) := hg.addr (by pomega)
  have rY : InRegions (s.rd ++ s.wr) (sa scr (oY + k)) 1 := hg.rd hs (by pomega)
  have wY : InRegions s.wr (sa scr (oY + k)) 1 := hg.wr hs (by pomega)
  have e8 : (BitVec.ofNat 32 k &&& BitVec.ofNat 32 (h.B - 1)) + (scr + BitVec.ofNat 32 oLen) =
      scr + BitVec.ofNat 32 (oLen + k % h.B) := by
    rw [ofNat_and_mask h.B_cases (by pomega), BitVec.add_comm, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  have aL8 : State.addr (scr + BitVec.ofNat 32 (oLen + k % h.B)) = sa scr (oLen + k % h.B) := hg.addr (by pomega)
  have rL8 : InRegions (s.rd ++ s.wr) (sa scr (oLen + k % h.B)) 1 := hg.rd hs (by pomega)
  have esh : BitVec.ofNat 32 k >>> lgB h.H = BitVec.ofNat 32 (k / h.B) := by
    rw [VG.Proof.MdStream.Arm.ofNat_shr (by pomega), h.pow_lg]
  have eq1 := eqBit (a := k) (b := msg.length) (by pomega) (by pomega)
  have eq2 := eqBit (a := k / h.B) (b := (msg.length + h.L) / h.B) (by have := Nat.div_le_self k h.B; pomega)
    (by have := Nat.div_le_self (msg.length + h.L) h.B; pomega)
  have vY := hp.y k hk
  rw [ite_eq_right (Nat.lt_irrefl k)] at vY
  have vL := hp.lb (k % h.B) hkB
  have lr1 : BitVec.ofNat 32 (T - k) - 1 = BitVec.ofNat 32 (T - (k + 1)) := by
    rw [show T - k = (T - (k + 1)) + 1 by omega]
    exact sub_one_ofNat (by omega)
  prun [padBody, hp.r0, hp.r1, hp.r4, hp.r5, hp.r6, hp.r7, hp.r9, hp.lr, aY, rY, wY, e8, aL8, rL8, vY, vL,
    esh, eq1, eq2, lr1, padByte, h.lg_range, dpVal, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · rw [VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32, Nat.add_assoc]
  · exact VG.Proof.Pbkdf2.Stream.Arm.ofNat_succ32 k
  · rw [VG.Proof.X25519.Arm.ofNat_beq_zero (by omega)]

/-- The padding loop: `padY` in `Y`'s `nbm` blocks. -/
theorem pad_vp (hg : Geo L scr) {nbm : Nat} (hnb : nbm * h.B ≤ 2048) (hnb0 : 0 < nbm) {msg : State → List Byte}
    (hfit : ∀ σ, (msg σ).length + 1 + h.L ≤ nbm * h.B) {Inv : State → Mem → Prop}
    (hI : ∀ σ m m', Inv σ m → Frame [sR scr oY (nbm * h.B)] m m' → Inv σ m')
    (hsl : ∀ σ m, Inv σ m → m.readW (L.fr sL) 32 = BitVec.ofNat 32 (msg σ).length)
    (hsn : ∀ σ m, Inv σ m → m.readW (L.fr sNb) 32 = BitVec.ofNat 32 nbm) :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ LB h scr (msg σ).length s.mem ∧
        ∀ i < nbm * h.B, s.mem (sa scr (oY + i)) = (msg σ).getD i 0)
      (.seq (.block (padArgs h.H)) (countLoop (padBody h.H)))
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧
        ∀ i < nbm * h.B, s.mem (sa scr (oY + i)) = padY h.B h.L (msg σ) (h.md.lenBytes (msg σ).length) i) := by
  have hBl := h.B_le
  have hB64 := h.B_ge
  have hL := h.L_le
  have fit := hg.fit
  have hpos : 0 < nbm * h.B := Nat.mul_pos hnb0 (by omega)
  generalize hT : nbm * h.B = T at hnb hpos hfit hI ⊢
  refine VP.seq (G := fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ PI h scr T (msg σ) 0 s)
    (VP.blk (blkOk rfl) (fun _ _ _ _ h₁ h₂ => h₁.1.st.sp.trans h₂.1.st.sp.symm) fun σ s ⟨hc, hi, lb, hy⟩ => ?_) ?_
  · have esh : (BitVec.ofNat 32 (msg σ).length + BitVec.ofNat 32 h.L) >>> lgB h.H =
        BitVec.ofNat 32 (((msg σ).length + h.L) / h.B) := by
      rw [BitVec.ofNat_add_ofNat, VG.Proof.MdStream.Arm.ofNat_shr (by have := hfit σ; pomega), h.pow_lg]
    have esl : BitVec.ofNat 32 nbm <<< lgB h.H = BitVec.ofNat 32 T := by
      rw [← hT]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, h.pow_lg,
        Nat.mod_eq_of_lt (a := nbm) (by have : nbm ≤ T := hT ▸ Nat.le_mul_of_pos_right nbm (show 0 < h.B by omega); omega)]
    prun [padArgs, atS, sp0, ld, mw, hc.st.sp, hc.aFr hg, hc.rFr hg, hc.slotS, Ctx.setReg_iff, hc, hi,
      hsl σ _ hi, hsn σ _ hi, movw_val (show oY < 2 ^ 16 by decide), movw_val (show oLen < 2 ^ 16 by decide),
      movw_val (show h.L < 2 ^ 16 by omega), movw_val (show h.B - 1 < 2 ^ 16 by omega),
      movw_val (show 0 < 2 ^ 16 by decide), esh, esl, h.lg_range, dpVal]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, lb, fun i hi' =>
      (hy i hi').trans (ite_eq_right (Nat.not_lt_zero i)).symm⟩
  let I : Nat → State → State → Prop := fun n σ s =>
    n ≤ T ∧ Ctx L scr σ s ∧ Inv σ s.mem ∧ PI h scr T (msg σ) (T - n) s
  refine (VP.loop (I := I) (fun n => ?_) (T - 1)).mono (fun σ s ⟨hc, hi, hp⟩ => ⟨by omega, hc, hi,
    by rw [show T - (T - 1 + 1) = 0 by omega]; exact hp⟩) fun _ _ h => h
  refine VP.taint _ (padBody_taint h) (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨hn, hc, hi, hp⟩ => ?_
  · obtain ⟨-, -, -, p₁⟩ := h₁
    obtain ⟨-, -, -, p₂⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [p₁.r0, p₂.r0]
    · rw [p₁.r1, p₂.r1]
    · rw [p₁.lr, p₂.lr]
    · rw [p₁.r6, p₂.r6]
    · rw [p₁.r7, p₂.r7]
    · rw [p₁.r9, p₂.r9]
  generalize hk : T - (n + 1) = k at hp
  have hkn : k < T := by omega
  refine WP.mono (padStep h hg hnb (hfit σ) hkn hc.st hp)
    fun t ⟨m, rd, wr, sp, r0, r1, lr, r4, r5, r6, r7, r9, z⟩ => ?_
  have fr : Frame [sR scr oY T] s.mem t.mem := by
    rw [m]; exact frame_byte scr _ _ (by omega) (by omega) (by pomega)
  obtain ⟨σ', ok⟩ := hg.ok
  have hc' : Ctx L scr σ t := hc.write fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hg.inW (by pomega))
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by pomega) (by rw [hg.F]; decide))
    rd wr sp
  have pk : PI h scr T (msg σ) (k + 1) t := by
    refine ⟨r0, r1, lr, r4.trans hp.r4, r5.trans hp.r5, r6.trans hp.r6, r7.trans hp.r7, r9.trans hp.r9,
      fun j hj => ?_, fun i hi' => ?_⟩
    · rw [m, sa_write scr _ _ (by pomega) (by pomega), ite_eq_right (by have := hp.lb; pomega)]
      exact hp.lb j hj
    · rw [m, sa_write scr _ _ (by pomega) (by pomega), hp.y i hi']
      by_cases e : i = k
      · subst e; rw [ite_eq_left rfl, ite_eq_left (Nat.lt_succ_self _)]
      · rw [ite_eq_right (by omega)]
        by_cases e' : i < k
        · rw [ite_eq_left e', ite_eq_left (by omega)]
        · rw [ite_eq_right e', ite_eq_right (by omega)]
  refine ⟨by
    rw [VG.Proof.X25519.Arm.eval_ne, z, show T - (k + 1) = n by omega]
    cases n <;> simp, fun h0 => ⟨hc', hI σ _ _ hi fr, fun i hi' => ?_⟩,
    fun hpos' => ⟨by omega, hc', hI σ _ _ hi fr, by rw [show T - n = k + 1 by omega]; exact pk⟩⟩
  rw [pk.y i hi', ite_eq_left (by omega)]

end VG.Proof.RsaPss.Arm

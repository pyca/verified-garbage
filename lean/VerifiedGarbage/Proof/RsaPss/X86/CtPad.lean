module

public import VerifiedGarbage.Proof.RsaPss.X86.CtLen
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.MdStream.X86.Words
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# RSASSA-PSS on x86: hashing, the padding of a message of secret length

`pad_vp`: the padding loop leaves `padY` in `Y`'s `nbm` blocks: `0x80` in
byte `ℓ` and the block at `oLen` ORed into the last block of the padded
message, each through a mask computed without a branch (`zmask`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes

/-! ## Values -/

/-- `shl r k` (`k` doublings) of a value that does not overflow. -/
theorem wp_shl {s : State} {r : Reg} {n : Nat} (k : Nat) (hn : n * 2 ^ k < 2 ^ 32)
    (hr : s.gpr r = BitVec.ofNat 32 n) {is : List Instr} {Q : State → Prop}
    (kk : ∀ t, Upd s t r (BitVec.ofNat 32 (n * 2 ^ k)) → WP isa (.block is) t Q) :
    WP isa (.block (shl r k ++ is)) s Q := by
  induction k generalizing s n with
  | zero => exact kk s ⟨by rw [hr, Nat.pow_zero, Nat.mul_one], fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | succ k ih =>
    have eq : 2 * n * 2 ^ k = n * 2 ^ (k + 1) := by rw [Nat.pow_succ]; ac_rfl
    have hn' : 2 * n * 2 ^ k < 2 ^ 32 := by rw [eq]; exact hn
    simp only [shl, List.replicate_succ, List.cons_append]
    refine wp_add fun t u _ => ?_
    have e : t.gpr r = BitVec.ofNat 32 (2 * n) := by
      rw [u.gpr, hr, BitVec.ofNat_add_ofNat, Nat.two_mul]
    have := ih (s := t) (n := 2 * n) hn' e fun t' v => kk t' ⟨by rw [v.gpr, eq],
      fun r' hr' => by rw [v.other r' hr', u.other _ hr'], by rw [v.mem, u.mem], by rw [v.rd, u.rd],
      by rw [v.wr, u.wr], by rw [v.syms, u.syms]⟩
    simpa only [shl] using this

/-- The byte the padding loop stores. -/
theorem padByte (b l : Byte) (c d : Prop) [Decidable c] [Decidable d] :
    (((b.setWidth 32 ||| ((if c then BitVec.allOnes 32 else 0) &&& 0x80)) |||
        ((l.setWidth 32) &&& if d then BitVec.allOnes 32 else 0))).setWidth 8 =
      b ||| (if c then 0x80 else 0) ||| (if d then l else 0) := by
  have e1 : ∀ x : BitVec 8, (x.setWidth 32).setWidth 8 = x := fun x => by simp
  have e2 : (BitVec.allOnes 32 &&& (0x80 : BitVec 32)).setWidth 8 = 0x80 := by decide
  have e3 : ((0 : BitVec 32) &&& (0x80 : BitVec 32)).setWidth 8 = 0 := by decide
  have e5 : (0 : BitVec 32).setWidth 8 = 0 := by decide
  by_cases hc : c <;> by_cases hd : d <;> simp only [hc, hd, BitVec.setWidth_or, BitVec.setWidth_and, e1, e2, e3,
    e5, ite_true, ite_false, BitVec.and_allOnes] <;> simp

/-- The mask `sbb r, r` makes after `sub r, 1`. -/
theorem ifz (x : BitVec 32) :
    (if decide (x.toNat < (1 : BitVec 32).toNat) = true then BitVec.allOnes 32 else 0) = zmask x := by
  unfold zmask
  by_cases hx : x = 0
  · subst hx; rfl
  · have : ¬ x.toNat < (1 : BitVec 32).toNat := fun e => hx (BitVec.eq_of_toNat_eq (by
      change _ < 1 at e
      change _ = 0
      omega))
    rw [decide_eq_false this, ite_eq_right hx]
    rfl

theorem ofNat_and_mask {k B : Nat} (hB : B = 64 ∨ B = 128) (hk : k < 2 ^ 32) :
    BitVec.ofNat 32 k &&& BitVec.ofNat 32 (B - 1) = BitVec.ofNat 32 (k % B) := by
  obtain ⟨j, hj, rfl⟩ : ∃ j, j ≤ 7 ∧ B = 2 ^ j := by
    rcases hB with rfl | rfl
    exacts [⟨6, by decide, rfl⟩, ⟨7, by decide, rfl⟩]
  have hp : 2 ^ j ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) hj
  have hm := Nat.mod_lt k (Nat.two_pow_pos j)
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt (show 2 ^ j - 1 < 2 ^ 32 by omega), Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt (show k % 2 ^ j < 2 ^ 32 by omega)]

variable {L : Lay} {scr : BitVec 32} (h : PssHash)

/-! ## The loop -/

/-- After `k` bytes of the padding loop. -/
structure PI (scr : BitVec 32) (T : Nat) (msg : List Byte) (k : Nat) (s : State) : Prop where
  esi : s.gpr .esi = scr + BitVec.ofNat 32 (oY + k)
  edi : s.gpr .edi = BitVec.ofNat 32 k
  ebx : s.gpr .ebx = BitVec.ofNat 32 (T - k)
  sl : s.mem.readW (L.fr sL) 32 = BitVec.ofNat 32 msg.length
  slb : s.mem.readW (L.fr sLb) 32 = BitVec.ofNat 32 ((msg.length + h.L) / h.B)
  lb : LB h scr msg.length s.mem
  y : ∀ i < T, s.mem (sa scr (oY + i)) =
    if i < k then padY h.B h.L msg (h.md.lenBytes msg.length) i else msg.getD i 0

/-- One byte. -/
theorem padStep (hg : Geo L scr) {σ : State} {T : Nat} (hnb : T ≤ 2048) {msg : List Byte}
    (hfit : msg.length + 1 + h.L ≤ T) {k : Nat} (hk : k < T) {s : State}
    (hc : Ctx L scr σ s) (hp : PI (L := L) h scr T msg k s) :
    WP isa (.block (padBody h.H)) s fun t =>
      t.mem = s.mem.writeW (sa scr (oY + k)) (padY h.B h.L msg (h.md.lenBytes msg.length) k) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .esp = s.gpr .esp ∧ t.gpr .ebp = s.gpr .ebp ∧
      t.gpr .esi = scr + BitVec.ofNat 32 (oY + (k + 1)) ∧ t.gpr .edi = BitVec.ofNat 32 (k + 1) ∧
      t.gpr .ebx = BitVec.ofNat 32 (T - (k + 1)) ∧ t.zf = some (decide (T - (k + 1) = 0)) := by
  have hBl := h.B_le
  have hB64 := h.B_ge
  have hL := h.L_le
  have fit := hg.fit
  unfold oRsa at fit
  have hkB := Nat.mod_lt k (show 0 < h.B by omega)
  have sp := hc.st.sp
  have bp := hc.ebp
  have ok := hc.st.ok
  have aY : VG.X86.addr (scr + BitVec.ofNat 32 (oY + k)) 0 = sa scr (oY + k) := by
    rw [hg.addrD (by pomega), Nat.add_zero]
  have rY : InRegions (s.rd ++ s.wr) (sa scr (oY + k)) 1 := hg.rd hc.st (by pomega)
  have wY : InRegions s.wr (sa scr (oY + k)) 1 := hg.wr hc.st (by pomega)
  have aL := hg.aFr ok sL (by decide)
  have aLb := hg.aFr ok sLb (by decide)
  have rL := hc.rFr hg sL (by decide)
  have rLb := hc.rFr hg sLb (by decide)
  have vY := hp.y k hk
  rw [ite_eq_right (Nat.lt_irrefl k)] at vY
  have vL := hp.lb (k % h.B) hkB
  simp only [padBody, isZero, addi, Impl.RsaPkcs1Sig.X86.stk, Impl.RsaPkcs1Sig.X86.at_, List.cons_append,
    List.nil_append]
  refine wp_movzx8 (by rw [ea_at, hp.esi]; exact aY) rY fun t1 u1 => ?_
  refine wp_mov fun t2 u2 => ?_
  refine wp_xorm (B := L.B) (by rw [u2.other _ (by decide), u1.other _ (by decide), sp])
    (by rw [aL, u2.rd, u2.wr, u1.rd, u1.wr]; exact rL) fun t3 u3 => ?_
  refine wp_subi fun t4 u4 c4 _ => wp_sbb_self c4 fun t5 u5 => ?_
  refine wp_andi fun t6 u6 => wp_or fun t7 u7 => wp_mov fun t8 u8 => ?_
  refine wp_shr h.lg_range fun t9 u9 _ => ?_
  have hℓ : msg.length < 2 ^ 32 := by omega
  have hk32 : k < 2 ^ 32 := by omega
  have e7 : t7.gpr .eax = (msg.getD k 0).setWidth 32 |||
      ((if k = msg.length then BitVec.allOnes 32 else 0) &&& 128) := by
    have e3 : t3.gpr .edx = BitVec.ofNat 32 k ^^^ BitVec.ofNat 32 msg.length := by
      simp (disch := decide) only [u3.gpr, u2.gpr, u2.mem, u1.mem, u1.other, hp.edi, aL, hp.sl]
    simp (disch := decide) only [u7.gpr, u6.gpr, u6.other, u5.gpr, u5.other, u4.other, u3.other, u2.other, u1.gpr,
      vY]
    rw [ifz, e3, zmask_xor hk32 hℓ]
  have e9 : t9.gpr .edx = BitVec.ofNat 32 (k / h.B) := by
    simp (disch := decide) only [u9.gpr, u8.gpr, u7.other, u6.other, u5.other, u4.other, u3.other, u2.other,
      u1.other, hp.edi]
    rw [ofNat_shr hk32, h.pow_lg]
  refine wp_xorm (B := L.B) (by simp (disch := decide) only [u9.other, u8.other, u7.other, u6.other, u5.other, u4.other, u3.other, u2.other, u1.other, sp])
    (by simp only [u9.rd, u9.wr, u8.rd, u8.wr, u7.rd, u7.wr, u6.rd, u6.wr, u5.rd, u5.wr, u4.rd, u4.wr, u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr, aLb]; exact rLb) fun t10 u10 => ?_
  refine wp_subi fun t11 u11 c11 _ => wp_sbb_self c11 fun t12 u12 => ?_
  have e12 : t12.gpr .edx = if k / h.B = (msg.length + h.L) / h.B then BitVec.allOnes 32 else 0 := by
    simp only [u12.gpr, u10.gpr, e9, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, aLb, hp.slb]
    rw [ifz, zmask_xor (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hk32)
      (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))]
  refine wp_mov fun t13 u13 => wp_andi fun t14 u14 => wp_add fun t15 u15 _ => ?_
  have e15 : t15.gpr .ecx = scr + BitVec.ofNat 32 (k % h.B) := by
    simp (disch := decide) only [u15.gpr, u14.gpr, u14.other, u13.gpr, u13.other, u12.other, u11.other,
      u10.other, u9.other, u8.other, u7.other, u6.other, u5.other, u4.other, u3.other, u2.other, u1.other, hp.edi, bp]
    rw [show h.H.B = h.B from rfl, ofNat_and_mask h.B_cases hk32, BitVec.add_comm]
  refine wp_movzx8 (a := sa scr (oLen + k % h.B)) (by rw [ea_at, e15, hg.addrD (by pomega), Nat.add_comm])
    (by simp only [u15.rd, u15.wr, u14.rd, u14.wr, u13.rd, u13.wr, u12.rd, u12.wr, u11.rd, u11.wr, u10.rd, u10.wr,
      u9.rd, u9.wr, u8.rd, u8.wr, u7.rd, u7.wr, u6.rd, u6.wr, u5.rd, u5.wr, u4.rd, u4.wr, u3.rd, u3.wr, u2.rd, u2.wr, u1.rd, u1.wr]; exact hg.rd hc.st (by pomega)) fun t16 u16 => ?_
  refine wp_and fun t17 u17 => wp_or fun t18 u18 => ?_
  have e18 : t18.gpr .eax = (msg.getD k 0).setWidth 32 |||
      ((if k = msg.length then BitVec.allOnes 32 else 0) &&& 128) |||
      ((lenBlk h.B h.L (h.md.lenBytes msg.length) (k % h.B)).setWidth 32 &&&
        if k / h.B = (msg.length + h.L) / h.B then BitVec.allOnes 32 else 0) := by
    simp (disch := decide) only [u18.gpr, u17.gpr, u17.other, u16.gpr, u16.other, u15.other, u14.other, u13.other,
      u12.other, u11.other, u10.other, u9.other, u8.other, e7, e12, u15.mem, u14.mem, u13.mem, u12.mem, u11.mem,
      u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, vL]
  refine wp_store8 (a := sa scr (oY + k)) (by
      rw [ea_at]; simp (disch := decide) only [u18.other, u17.other, u16.other, u15.other, u14.other, u13.other, u12.other, u11.other, u10.other, u9.other, u8.other, u7.other, u6.other, u5.other, u4.other, u3.other, u2.other, u1.other, hp.esi]; exact aY)
    (by simp only [u18.wr, u17.wr, u16.wr, u15.wr, u14.wr, u13.wr, u12.wr, u11.wr, u10.wr, u9.wr, u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]; exact wY) fun t19 u19 => ?_
  refine wp_addi fun t20 u20 => wp_addi fun t21 u21 => wp_subi fun t22 u22 _ z22 => WP.block_nil ?_
  have hTk : 1 ≤ T - k := by omega
  have eb : t21.gpr .ebx = BitVec.ofNat 32 (T - k) := by
    simp (disch := decide) only [u21.other, u20.other, u19.gpr, u18.other, u17.other, u16.other, u15.other, u14.other, u13.other, u12.other, u11.other, u10.other, u9.other, u8.other, u7.other, u6.other, u5.other, u4.other, u3.other, u2.other, u1.other, hp.ebx]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u22.mem, u21.mem, u20.mem, u19.mem, Reg8.reg, e18, padByte, u18.mem, u17.mem, u16.mem, u15.mem, u14.mem, u13.mem, u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]; rfl
  · rw [u22.rd, u21.rd, u20.rd, u19.rd, u18.rd, u17.rd, u16.rd, u15.rd, u14.rd, u13.rd, u12.rd, u11.rd, u10.rd, u9.rd, u8.rd, u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd]
  · rw [u22.wr, u21.wr, u20.wr, u19.wr, u18.wr, u17.wr, u16.wr, u15.wr, u14.wr, u13.wr, u12.wr, u11.wr, u10.wr, u9.wr, u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr]
  · simp (disch := decide) only [u22.other, u21.other, u20.other, u19.gpr, u18.other, u17.other, u16.other, u15.other, u14.other, u13.other, u12.other, u11.other, u10.other, u9.other, u8.other, u7.other, u6.other, u5.other, u4.other, u3.other, u2.other, u1.other]
  · simp (disch := decide) only [u22.other, u21.other, u20.other, u19.gpr, u18.other, u17.other, u16.other, u15.other, u14.other, u13.other, u12.other, u11.other, u10.other, u9.other, u8.other, u7.other, u6.other, u5.other, u4.other, u3.other, u2.other, u1.other]
  · simp (disch := decide) only [u22.other, u21.other, u20.gpr, u19.gpr, u18.other, u17.other, u16.other, u15.other, u14.other, u13.other, u12.other, u11.other, u10.other, u9.other, u8.other, u7.other, u6.other, u5.other, u4.other, u3.other, u2.other, u1.other, hp.esi]
    rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_assoc]
  · simp (disch := decide) only [u22.other, u21.gpr, u20.other, u19.gpr, u18.other, u17.other, u16.other, u15.other, u14.other, u13.other, u12.other, u11.other, u10.other, u9.other, u8.other, u7.other, u6.other, u5.other, u4.other, u3.other, u2.other, u1.other, hp.edi]
    rw [BitVec.ofNat_add_ofNat]
  · rw [u22.gpr, eb, ofNat_pred hTk, Nat.sub_sub]
  · rw [z22, eb, ofNat_pred hTk, ofNat_beq_zero (by omega), Nat.sub_sub]

/-- The padding loop: `padY` in `Y`'s `nbm` blocks. -/
theorem pad_vp (hg : Geo L scr) {nbm : Nat} (hnb : nbm * h.B ≤ 2048) (hnb0 : 0 < nbm) {msg : State → List Byte}
    (hfit : ∀ σ, (msg σ).length + 1 + h.L ≤ nbm * h.B) {Inv : State → Mem → Prop}
    (hI : ∀ σ m m', Inv σ m → Frame [sR scr oY (nbm * h.B)] m m' → Inv σ m')
    (hsn : ∀ σ m, Inv σ m → m.readW (L.fr sNb) 32 = BitVec.ofNat 32 nbm) :
    VP (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ LB h scr (msg σ).length s.mem ∧
        s.mem.readW (L.fr sL) 32 = BitVec.ofNat 32 (msg σ).length ∧
        s.mem.readW (L.fr sLb) 32 = BitVec.ofNat 32 (((msg σ).length + h.L) / h.B) ∧
        ∀ i < nbm * h.B, s.mem (sa scr (oY + i)) = (msg σ).getD i 0)
      (padPart h.H)
      (fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ LB h scr (msg σ).length s.mem ∧
        s.mem.readW (L.fr sL) 32 = BitVec.ofNat 32 (msg σ).length ∧
        s.mem.readW (L.fr sLb) 32 = BitVec.ofNat 32 (((msg σ).length + h.L) / h.B) ∧
        ∀ i < nbm * h.B, s.mem (sa scr (oY + i)) = padY h.B h.L (msg σ) (h.md.lenBytes (msg σ).length) i) := by
  have hBl := h.B_le
  have hB64 := h.B_ge
  have fit := hg.fit
  unfold oRsa at fit
  obtain ⟨σ', ok⟩ := hg.ok
  have hpos : 0 < nbm * h.B := Nat.mul_pos hnb0 (by omega)
  generalize hT : nbm * h.B = T at hnb hpos hfit hI ⊢
  refine VP.seq (G := fun σ s => Ctx L scr σ s ∧ Inv σ s.mem ∧ PI (L := L) h scr T (msg σ) 0 s)
    (VP.taint [.esp, .ebp] h.certs.padArgs (sp_bp fun _ _ h => h.1) fun σ s ⟨hc, hi, lb, sl, slb, hy⟩ => ?_) ?_
  · simp only [padArgs, atS, ld, mi, List.cons_append, List.nil_append]
    refine wp_mov fun t1 u1 => wp_addi fun t2 u2 => wp_movi fun t3 u3 => ?_
    have c3 : Ctx L scr σ t3 :=
      ((hc.upd u1 (by decide) (by decide)).upd u2 (by decide) (by decide)).upd u3 (by decide) (by decide)
    refine c3.wp_slot hg (by decide) (by decide) (by decide) fun t4 c4 u4 => ?_
    have m4 : t4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem, u1.mem]
    rw [← List.append_nil (shl .ebx _)]
    refine wp_shl (lgB h.H) (n := nbm) (by rw [h.pow_lg, hT]; omega) (by rw [u4.gpr, u3.mem, u2.mem, u1.mem,
      hsn σ _ hi]) fun t5 u5 => WP.block_nil ⟨c4.upd u5 (by decide) (by decide), by rw [u5.mem, m4]; exact hi,
        ⟨?_, ?_, ?_, by rw [u5.mem, m4]; exact sl, by rw [u5.mem, m4]; exact slb, by rw [u5.mem, m4]; exact lb,
          fun i hi' => ?_⟩⟩
    · rw [u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide), u2.gpr, u1.gpr, hc.ebp,
        Nat.add_zero]
    · rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr]
    · rw [u5.gpr, h.pow_lg, hT, Nat.sub_zero]
    · rw [u5.mem, m4, hy i hi', ite_eq_right (Nat.not_lt_zero i)]
  let I : Nat → State → State → Prop := fun n σ s =>
    n ≤ T ∧ Ctx L scr σ s ∧ Inv σ s.mem ∧ PI (L := L) h scr T (msg σ) (T - n) s
  refine (VP.loop (I := I) (fun n => ?_) (T - 1)).mono (fun σ s ⟨hc, hi, hp⟩ => ⟨by omega, hc, hi,
    by rw [show T - (T - 1 + 1) = 0 by omega]; exact hp⟩) fun _ _ h => h
  refine VP.taint _ h.certs.padBody (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s ⟨hn, hc, hi, hp⟩ => ?_
  · obtain ⟨-, c₁, -, p₁⟩ := h₁
    obtain ⟨-, c₂, -, p₂⟩ := h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [c₁.st.sp, c₂.st.sp]
    · rw [c₁.ebp, c₂.ebp]
    · rw [p₁.esi, p₂.esi]
    · rw [p₁.edi, p₂.edi]
    · rw [p₁.ebx, p₂.ebx]
  generalize hk : T - (n + 1) = k at hp
  have hkn : k < T := by omega
  refine WP.mono (padStep h hg hnb (hfit σ) hkn hc hp) fun t ⟨m, rd, wr, sp, bp, esi, edi, ebx, z⟩ => ?_
  have fr : Frame [sR scr oY T] s.mem t.mem := by
    rw [m]; exact frame_byte scr _ _ (by omega) (by omega) (by pomega)
  have hc' : Ctx L scr σ t := hc.write fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hg.inW (by pomega)) rd wr sp bp
  have dS : ∀ d, d + 4 ≤ frameBytes → ∀ r ∈ [sR scr oY T], (slotR L d).Disjoint r := fun d hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hg.slot ok (by pomega) (by rw [hg.F]; omega)
  have pk : PI (L := L) h scr T (msg σ) (k + 1) t := by
    refine ⟨esi, edi, ebx, slot_keep fr (dS _ (by decide)) hp.sl, slot_keep fr (dS _ (by decide)) hp.slb,
      fun j hj => ?_, fun i hi' => ?_⟩
    · rw [m, sa_write scr _ _ (by pomega) (by pomega), ite_eq_right (by pomega)]
      exact hp.lb j hj
    · rw [m, sa_write scr _ _ (by pomega) (by pomega), hp.y i hi']
      by_cases e : i = k
      · subst e; rw [ite_eq_left rfl, ite_eq_left (Nat.lt_succ_self _)]
      · rw [ite_eq_right (by omega)]
        by_cases e' : i < k
        · rw [ite_eq_left e', ite_eq_left (by omega)]
        · rw [ite_eq_right e', ite_eq_right (by omega)]
  rw [show T - (k + 1) = n by omega] at z
  refine ⟨?_, fun h0 => ⟨hc', hI σ _ _ hi fr, pk.lb, pk.sl, pk.slb, fun i hi' => ?_⟩,
    fun hpos' => ⟨by omega, hc', hI σ _ _ hi fr, by rw [show T - n = k + 1 by omega]; exact pk⟩⟩
  · show eval .ne t = _
    simp only [eval, z]
    by_cases h0 : n = 0 <;> simp [h0] <;> omega
  · rw [pk.y i hi', ite_eq_left (by omega)]

end VG.Proof.RsaPss.X86

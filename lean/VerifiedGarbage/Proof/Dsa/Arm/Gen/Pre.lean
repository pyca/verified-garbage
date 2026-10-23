module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.QPart
public import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Rsa.Arm.KcStart
import VerifiedGarbage.Proof.Dsa.Arm.Gen.KSLoad
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on ARMv7: before the seeds

`pre_vp`: `r7`–`r9` for the key working space (`ksRegs`), and the last 64 −
`qLen` bytes of a hash block after a `qLen`-byte message (`padInit`), which
every seed's hashes share: the search's first stage.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.WriteBytes
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_movw wp_dp wp_str wp_strb op2_imm op2_reg dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa.Arm.Keys (encodable_lt)

/-- A byte into bytes written before. -/
theorem writeBytes_set (m : Mem) (q : Addr) (xs : List Byte) {j : Nat} (hj : j < xs.length)
    (hl : xs.length < 2 ^ 64) (b : Byte) :
    (writeBytes m q xs).writeW (q + BitVec.ofNat 64 j) b = writeBytes m q (xs.set j b) := by
  funext x
  rw [writeW8_apply]
  simp only [writeBytes, List.length_set]
  by_cases hx : x = q + BitVec.ofNat 64 j
  · subst hx
    rw [Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp [hj, List.getD_eq_getElem?_getD]
  · have hne : (x - q).toNat ≠ j := by
      intro h'
      apply hx
      have : x - q = BitVec.ofNat 64 j := BitVec.eq_of_toNat_eq (by rw [h', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)])
      rw [← BitVec.sub_add_cancel x q, this, BitVec.add_comm]
    simp only [hx, ite_false]
    split
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hne)]
    · rfl

/-- Bytes within bytes written before. -/
theorem bytesAt_writeBytes (m : Mem) (q : Addr) (xs : List Byte) {d k : Nat} (h : d + k ≤ xs.length)
    (hl : xs.length < 2 ^ 64) :
    Spec.Rsa.bytesAt (writeBytes m q xs) (q + BitVec.ofNat 64 d) k = (xs.drop d).take k := by
  apply List.ext_getElem
  · simp [Spec.Rsa.bytesAt]; omega
  · intro i h1 h2
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, writeBytes, List.getElem_take,
      List.getElem_drop]
    rw [BitVec.add_assoc, Offset.add_sub_cancel_left, ← BitVec.ofNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by simp [Spec.Rsa.bytesAt] at h1; omega)]
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range] at h1
    simp [show d + i < xs.length by omega, List.getD_eq_getElem?_getD]

/-- The 16 words from `r0` := `r3` (0): 64 zero bytes. -/
theorem zeros_ok {s : State} {a : Addr} (r3 : s.gpr .r3 = 0)
    (ha : ∀ i < 16, State.addr (s.gpr .r0 + BitVec.ofNat 32 (4 * i)) = a + BitVec.ofNat 64 (4 * i))
    (hw : ∀ i < 16, InRegions s.wr (a + BitVec.ofNat 64 (4 * i)) 4) :
    ∀ k ≤ 16, ∀ {rest : List Instr} {Q : State → Prop},
      (∀ t, Rest [] s t → t.mem = writeBytes s.mem a (List.replicate (4 * k) 0) → WP isa (.block rest) t Q) →
      WP isa (.block (((List.range k).map fun i => Instr.str .r3 .r0 (4 * i)) ++ rest)) s Q
  | 0, _, rest, Q, k => k s (Rest.refl _ _) (by simp [writeBytes_nil])
  | j + 1, hj, rest, Q, k => by
    rw [List.range_succ, List.map_append, List.append_assoc]
    refine zeros_ok r3 ha hw j (by omega) fun t R m => ?_
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    refine wp_str (a := a + BitVec.ofNat 64 (4 * j)) (by omega) (by rw [R.gpr .r0 (by simp), ha j (by omega)])
      (by rw [R.wr]; exact hw j (by omega)) fun t' u => k t' (R.trans (u.rest [])) ?_
    rw [u.mem, m, R.gpr _ (by simp), r3]
    show Mem.write (writeBytes s.mem a (List.replicate (4 * j) 0)) (a + BitVec.ofNat 64 (4 * j)) 4
      ((0 : BitVec 32).setWidth (8 * 4)) = _
    rw [write_eq_writeBytes]
    have z4 : ((List.range 4).map fun i => ((0 : BitVec 32).setWidth (8 * 4)).extractLsb' (8 * i) 8) =
        List.replicate 4 (0 : Byte) := by decide
    have ap := writeBytes_append s.mem a (List.replicate (4 * j) (0 : Byte)) (List.replicate 4 0) (by simp; omega)
    rw [List.length_replicate] at ap
    rw [z4, ap, List.replicate_append_replicate, Nat.mul_succ]

section
variable {G : GP} {X : State → Prop}

/-- The 64 bytes `padInit` leaves at `sMsg`. -/
abbrev padList (n : Nat) : List Byte :=
  (((List.replicate 64 (0 : Byte)).set n 0x80).set 62 (BitVec.ofNat 8 (8 * n / 256))).set 63
    (BitVec.ofNat 8 (8 * n % 256))

theorem padList_tail {B N L : Nat} (md : MdStream.Md B N L) {n : Nat} (hn : n = 20 ∨ n = 32)
    (hlb : md.lenBytes n = [0, 0, 0, 0, 0, 0, BitVec.ofNat 8 (8 * n / 256), BitVec.ofNat 8 (8 * n % 256)]) :
    ((padList n).drop n).take (64 - n) = padTail md n := by
  rw [padTail, hlb]; rcases hn with rfl | rfl <;> decide

/-- The search's first stage: `r7`–`r9` and the end of a hash block. -/
theorem pre_vp {V : Nat → BitVec 32} {LS : List Nat} {B N L : Nat} (md : MdStream.Md B N L) (hL : L = 8)
    (hlq : (G.pLen = 128 ∧ G.qLen = 20) ∨ (G.pLen = 256 ∧ G.qLen = 32) ∨ (G.pLen = 384 ∧ G.qLen = 32))
    (hlb : md.lenBytes G.qLen =
      [0, 0, 0, 0, 0, 0, BitVec.ofNat 8 (8 * G.qLen / 256), BitVec.ofNat 8 (8 * G.qLen % 256)]) :
    VP (fun σ s => GI G σ V LS s ∧ X σ) (.block (ksRegs G.pLen ++ padInit G.pLen G.qLen))
      (St G { V := V, LS := LS, cl := [(G.qLen, padTail md G.qLen)] } X) := by
  show VP _ (.block ([ld .r8 fScratch] ++ ([.movw .r12 (BitVec.ofNat 16 (sK G.pLen)), .dp .add .r8 .r8 (.reg .r12)] ++
    wRegs G.pLen ++ padInit G.pLen G.qLen))) _
  refine VP.block_append (G := fun σ s => (GI G σ V LS s ∧ X σ) ∧ s.gpr .r8 = G.scr)
    (VP.ld (G := G) (fun σ s h => h.1.sp) fun σ s ⟨gi, x⟩ => gi.ldV (o := fScratch) (by decide) (by decide)
      (gi.fixed (fScratch, G.scr) (by simp [fixedWords])) fun s' u => WP.block_nil
        ⟨⟨gi.of_rest (u.rest (ws := [.r8]) (by simp)) u.mem, x⟩, u.gpr⟩) ?_
  have cert : Cert8 (.block ([.movw .r12 (BitVec.ofNat 16 (sK G.pLen)), .dp .add .r8 .r8 (.reg .r12)] ++
      wRegs G.pLen ++ padInit G.pLen G.qLen)) := by
    rcases hlq with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
    · exact ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r8]) (.block ([.movw .r12 (BitVec.ofNat 16
        (sK 128)), .dp .add .r8 .r8 (.reg .r12)] ++ wRegs 128 ++ padInit 128 20)), rfl⟩
    · exact ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r8]) (.block ([.movw .r12 (BitVec.ofNat 16
        (sK 256)), .dp .add .r8 .r8 (.reg .r12)] ++ wRegs 256 ++ padInit 256 32)), rfl⟩
    · exact ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r8]) (.block ([.movw .r12 (BitVec.ofNat 16
        (sK 384)), .dp .add .r8 .r8 (.reg .r12)] ++ wRegs 384 ++ padInit 384 32)), rfl⟩
  refine VP.taint [.r8] cert
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2])
    fun σ s ⟨⟨gi, x⟩, r8⟩ => ?_
  have big := gi.scrBig
  have fit := gi.scrFit
  have hn : G.qLen = 20 ∨ G.qLen = 32 := by omega_arith
  have hq32 : G.qLen ≤ 32 := by omega_arith
  have hl : G.pLen = 128 ∨ G.pLen = 256 ∨ G.pLen = 384 := by omega_arith
  have sk := sK_lt hl
  have kz0 : 0 < kz G.pLen := by simp only [kz]; omega_arith
  have s64 : 64 ≤ sK G.pLen := by simp only [sK, sA]; omega_arith
  show WP isa (.block (.movw .r12 (BitVec.ofNat 16 (sK G.pLen)) :: .dp .add .r8 .r8 (.reg .r12) ::
    .mov .r9 (.imm (BitVec.ofNat 32 (G.pLen / 4))) :: (VG.Impl.Rsa.Arm.Keys.stride ++ (scr G.pLen .r0 sMsg ++
      (.mov .r3 (.imm 0) :: (((List.range 16).map fun i => Instr.str .r3 .r0 (4 * i)) ++
        [.mov .r1 (.imm 0x80), .strb .r1 .r0 G.qLen,
          .mov .r1 (.imm (BitVec.ofNat 32 ((8 * G.qLen) / 256))), .strb .r1 .r0 62,
          .mov .r1 (.imm (BitVec.ofNat 32 ((8 * G.qLen) % 256))), .strb .r1 .r0 63])))))) s _
  refine wp_movw fun s₁ u₁ => wp_dp (op2_reg _ _) fun s₂ u₂ => ?_
  have kb : s₂.gpr .r8 = G.KB := by
    rw [u₂.gpr, dpVal, u₁.other _ (by decide), r8, u₁.gpr, setWidth_ofNat16 sk]
  refine wp_mov (op2_imm (encodable_lt (show G.pLen / 4 < 256 by omega_arith))) fun s₃ u₃ => ?_
  refine VG.Proof.Rsa.Arm.KeyCheck.stride_ok (w := G.w) (by simp only [GP.w]; omega_arith) u₃.gpr fun s₄ e7 R₄ M₄ => ?_
  have kb4 : s₄.gpr .r8 = G.KB := by rw [R₄.gpr _ (by decide), u₃.other _ (by decide), kb]
  refine scr_ok (d := .r0) kb4 rfl hl (by simp only [sMsg]; omega_arith) fun s₅ v₅ R₅ M₅ => ?_
  refine wp_mov (op2_imm (encodable_lt (show 0 < 256 by decide))) fun s₆ u₆ => ?_
  have a0 : ∀ i, i < 64 → State.addr (s₆.gpr .r0 + BitVec.ofNat 32 i) = State.addr G.scr + BitVec.ofNat 64 i :=
    fun i hi => by
      rw [u₆.other _ (by decide), v₅, show sMsg = 0 from rfl, BitVec.add_zero]
      exact gi.saddr (by omega_arith)
  have w6 : ∀ {o n : Nat}, o + n ≤ G.scrLen * 8 → InRegions s₆.wr (G.sa o) n := fun h => by
    rw [u₆.wr, R₅.wr, R₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact gi.inScr h
  refine zeros_ok (s := s₆) (a := State.addr G.scr) (by rw [u₆.gpr]) (fun i hi => a0 _ (by omega_arith))
    (fun i hi => w6 (o := 4 * i) (n := 4) (by omega_arith)) 16 (Nat.le_refl _) fun s₇ R₇ M₇ => ?_
  have a7 : ∀ i, i < 64 → State.addr (s₇.gpr .r0 + BitVec.ofNat 32 i) = State.addr G.scr + BitVec.ofNat 64 i :=
    fun i hi => by rw [R₇.gpr _ (by simp)]; exact a0 i hi
  refine wp_mov (op2_imm (encodable_lt (show 0x80 < 256 by decide))) fun s₈ u₈ => ?_
  refine wp_strb (a := State.addr G.scr + BitVec.ofNat 64 G.qLen) (by omega_arith)
    (by rw [u₈.other _ (by decide)]; exact a7 _ (by omega_arith))
    (by rw [u₈.wr, R₇.wr]; exact w6 (o := G.qLen) (n := 1) (by omega_arith)) fun s₉ u₉ => ?_
  refine wp_mov (op2_imm (encodable_lt (show 8 * G.qLen / 256 < 256 by omega_arith))) fun s₁₀ u₁₀ => ?_
  refine wp_strb (a := State.addr G.scr + BitVec.ofNat 64 62) (by omega_arith)
    (by rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide)]; exact a7 _ (by omega_arith))
    (by rw [u₁₀.wr, u₉.wr, u₈.wr, R₇.wr]; exact w6 (o := 62) (n := 1) (by omega_arith)) fun s₁₁ u₁₁ => ?_
  refine wp_mov (op2_imm (encodable_lt (show 8 * G.qLen % 256 < 256 by omega_arith))) fun s₁₂ u₁₂ => ?_
  refine wp_strb (a := State.addr G.scr + BitVec.ofNat 64 63) (by omega_arith)
    (by rw [u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide)]
        exact a7 _ (by omega_arith))
    (by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, R₇.wr]; exact w6 (o := 63) (n := 1) (by omega_arith))
    fun t u₁₃ => WP.block_nil ?_
  have sw8 : ∀ x : Nat, (BitVec.ofNat 32 x).setWidth 8 = BitVec.ofNat 8 x := fun x => by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    exact Nat.mod_mod_of_dvd _ (by decide)
  have hl64 : (List.replicate 64 (0 : Byte)).length < 2 ^ 64 := by simp
  have m6 : s₆.mem = s.mem := by rw [u₆.mem, M₅, M₄, u₃.mem, u₂.mem, u₁.mem]
  have mt : t.mem = writeBytes s.mem (State.addr G.scr) (padList G.qLen) := by
    rw [u₁₃.mem, u₁₂.gpr, u₁₂.mem, u₁₁.mem, u₁₀.gpr, u₁₀.mem, u₉.mem, u₈.gpr, u₈.mem, M₇, m6, sw8, sw8]
    rw [writeBytes_set _ _ _ (by simp; omega_arith) hl64, writeBytes_set _ _ _ (by simp) (by simp),
      writeBytes_set _ _ _ (by simp) (by simp)]
    rfl
  have R : Rest [.r12, .r8, .r9, .r7, .r0, .r3, .r1] s t :=
    ((((u₁.rest (by simp)).trans (u₂.rest (by simp))).trans (u₃.rest (by simp))).trans
      ((R₄.mono (by simp)).trans ((R₅.mono (by simp)).trans (u₆.rest (by simp))))).trans
      ((R₇.mono (by simp)).trans ((u₈.rest (by simp)).trans ((u₉.rest _).trans ((u₁₀.rest (by simp)).trans
        ((u₁₁.rest _).trans ((u₁₂.rest (by simp)).trans (u₁₃.rest _)))))))
  have f : Frame [G.rScr, G.rBelow] s.mem t.mem := by
    rw [mt]
    exact (writeBytes_frame _ _ _ (R := G.rScr) (by
      show (_ - _ : Addr).toNat + _ ≤ _
      rw [BitVec.sub_self, BitVec.toNat_zero]; simp; omega_arith)).mono (by simp)
  have g7 : ∀ r, r ∉ [Reg.r0, .r1, .r3, .r12] → t.gpr r = s₄.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₁₃.gpr, u₁₂.other _ hr.2.1, u₁₁.gpr, u₁₀.other _ hr.2.1, u₉.gpr,
      u₈.other _ hr.2.1, R₇.gpr _ (by simp), u₆.other _ hr.2.2.1,
      R₅.gpr _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨hr.2.2.2, hr.1⟩)]
  have pl := padTail_length md (n := G.qLen) (by omega_arith) hL
  refine ⟨⟨gi.of_scr R f, ?_, ?_, ?_, fun y hy => ?_, fun y hy => ?_, fun j hj => absurd hj (by simp),
    fun j hj => absurd hj (by simp), fun d hd => absurd hd (by simp), fun d hd => absurd hd (by simp)⟩, x⟩
  · rw [g7 _ (by decide), e7]
  · rw [g7 _ (by decide), kb4]
  · rw [g7 _ (by decide), R₄.gpr _ (by decide), u₃.gpr]
  · simp only [List.mem_singleton] at hy; subst hy
    show Spec.Rsa.bytesAt t.mem (State.addr G.scr + BitVec.ofNat 64 G.qLen) (padTail md G.qLen).length = _
    rw [mt, pl, bytesAt_writeBytes _ _ _ (by simp; omega_arith) (by simp), padList_tail md hn hlb]
  · simp only [List.mem_singleton] at hy; subst hy
    show G.qLen + (padTail md G.qLen).length ≤ _
    rw [pl]; omega_arith

end

end VG.Proof.Dsa.Arm.Gen

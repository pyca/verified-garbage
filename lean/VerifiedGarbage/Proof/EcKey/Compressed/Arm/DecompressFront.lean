module

public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Front
public import VerifiedGarbage.Impl.EcKey.Compressed.Arm.Decompress
public import VerifiedGarbage.Proof.Ecdsa.Arm.Fixed
import VerifiedGarbage.Proof.Ecdsa.Arm.Lays
import VerifiedGarbage.Proof.Ecdsa.Arm.SlotOps
import VerifiedGarbage.Proof.Ecdsa.Arm.Middle
public import VerifiedGarbage.Proof.Ecdsa.Arm.Main
import VerifiedGarbage.Proof.Ecdh.Arm.Validate
public import VerifiedGarbage.Proof.Weierstrass.Arm.Fprog
public import VerifiedGarbage.Impl.Weierstrass.Arm
public import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
public import VerifiedGarbage.Proof.Weierstrass.Env
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Frame
import VerifiedGarbage.Proof.Ecdh.Arm.Peer
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Ecdsa.Arm.Scalar
import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
import VerifiedGarbage.Proof.Weierstrass.Arm.Const
import VerifiedGarbage.Proof.Weierstrass.Arm.BytesLen
import VerifiedGarbage.Proof.Ecdsa.Arm.Finish
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Spec.Ecdsa.Generic
import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
public import VerifiedGarbage.Proof.Weierstrass.Arm.Ladder

/-! ### `EcKey.Compressed.Arm.Rhs`, which only this module used -/

section

/-! # The curve polynomial used by coordinate recovery -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.Arm

open VG.Proof.X25519.Arm (Rest)
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdh.Arm (R2P BP QXM QYM QY W0 W1 W2 W3)
open VG.Impl.EcKey.Compressed.Arm (rhsOps)
open VG.Proof.Ecdsa.Arm VG.Proof.Mont.Arm VG.Proof.Mont
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm VG.Proof.Ecdh.Arm

abbrev rhsSlots : List Nat := [QXM, AP, BP, W1, W2, W3]

def rhsTail : List FOp :=
  [.mul W1 QXM QXM, .mul W2 W1 QXM, .mul W1 AP QXM,
    .add W3 W2 W1, .add W2 W3 BP]

theorem rhsTail_run {F : Type} [Lean.Grind.CommRing F] (e : Nat → F) :
    runOps rhsTail e W2 = e QXM * e QXM * e QXM + e AP * e QXM + e BP := by
  simp only [rhsTail, runOps_cons, runOps_nil, FOp.run, Function.update_apply]
  simp only [W1, W2, W3, QXM, AP, BP, TT, SM, RM, XM, EM, Nat.reduceEqDiff, ↓reduceIte]

theorem rhsTail_reads : readsOk rhsTail [QXM, AP, BP] = true := by decide
theorem rhsTail_slots : ∀ op ∈ rhsTail, ∀ x ∈ op.out :: op.ins, x ∈ rhsSlots := by decide
theorem rhsTail_out : ∀ op ∈ rhsTail, op.out ∈ [W1, W2, W3, TMP] := by decide

structure RhsPost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  scr : Scr s' base size
  mod : ModOkW c.MP' size c.C.p s'.mem base
  rest : Rest Mont.callClob s s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  unch : Unch base (slWk c [QXM, W1, W2, W3, TMP]) s.mem s'.mem
  lt : sv c base s' W2 < c.C.p
  val : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' W2) =
    let x := Fin.ofNat c.C.p (sv c base s E)
    x * x * x + Fin.ofNat c.C.p c.C.a * x + Fin.ofNat c.C.p c.C.b

theorem rhs_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hf : Far s base 8192) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hr2 : sv c base s R2P = c.R * c.R % c.C.p)
    (hap : sv c base s AP = c.mont c.C.a) (hbp : sv c base s BP = c.mont c.C.b) :
    WP isa (Impl.Weierstrass.Arm.fprog c.SP (rhsOps c) c.umaal) s (RhsPost c base s) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  change WP isa (.seq (VG.Impl.Weierstrass.Arm.Mont.mulCall c.SP
    (c.sl QXM) (c.sl E) (c.sl R2P) c.umaal)
    (VG.Impl.Weierstrass.Arm.fprog c.SP (rhsTail.map (FOp.rename c.sl)) c.umaal)) s _
  refine WP.seq (WP.mono (slMul_ok hc.fp (MP'_n c) h7 hs hf (o := QXM) (a := E) (b := R2P)
    (by decide) (by decide) (by decide)
    (by rw [hr2]; exact Nat.mod_lt _ (by have := hc.p_ge; omega_using [this])))
    fun s₁ ⟨k₁, lt₁, e₁⟩ => ?_)
  obtain hs₁ := k₁.scr hs
  obtain hM₁ := hM.keepArm (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  obtain v₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ QXM) = Fin.ofNat c.C.p (sv c base s E) :=
    toM_r2 hpR (by simpa only [hr2, Cfg.R] using e₁)
  obtain a₁ : sv c base s₁ AP = c.mont c.C.a :=
    (sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)).trans hap
  obtain b₁ : sv c base s₁ BP = c.mont c.C.b :=
    (sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)).trans hbp
  obtain hL : Lay c.MP' size (· ∈ rhsSlots.map c.sl) := lay_map hc rfl rfl rfl (by decide)
  obtain hW : WkOk c.MP' size c.wk (· ∈ rhsSlots.map c.sl) := by
    refine ⟨wk_le c h7 rfl, ?_, sl_below_wk c h7 (by decide), sl_below_wk c h7 (by decide)⟩
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    obtain H : ∀ i ∈ rhsSlots, i < 45 := by decide
    exact sl_below_wk c h7 (H i hi)
  obtain I : Inv c.MP' base size c.C.p (· ∈ rhsSlots.map c.sl) ([QXM, AP, BP].map c.sl)
      (fun o => toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₁.mem base o c.n)) s₁ := by
    refine ⟨hs₁, hM₁, ?_, ?_, fun _ _ => rfl, hf.of_rest k₁.rest⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      obtain sub : ∀ i ∈ [QXM, AP, BP], i ∈ rhsSlots := by decide
      exact List.mem_map_of_mem (sub i hi)
    · intro x hx
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact lt₁
      · show sv c base s₁ AP < _
        rw [a₁]
        exact Nat.mod_lt _ (by have := hc.p_ge; omega_using [lt₁])
      · show sv c base s₁ BP < _
        rw [b₁]
        exact Nat.mod_lt _ (by have := hc.p_ge; omega_using [lt₁])
  refine WP.mono (fprog_ok hL hW hc.fp hpR _ I (fun op hop x hx => ?_)
    (readsOk_rename c.sl rhsTail_reads)) fun s₂ ⟨PK, I₂⟩ => ?_
  · obtain ⟨op₀, hop₀, rfl⟩ := List.mem_map.mp hop
    obtain hx' : x ∈ (op₀.out :: op₀.ins).map c.sl := by
      cases op₀ <;> simpa [FOp.rename, FOp.out, FOp.ins] using hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    exact List.mem_map_of_mem (rhsTail_slots _ hop₀ _ hi)
  obtain hw : c.sl W2 ∈ validAfter (rhsTail.map (FOp.rename c.sl)) ([QXM, AP, BP].map c.sl) :=
    (mem_validAfter _ _).mpr (Or.inr (by simp [rhsTail, FOp.rename, FOp.out]))
  obtain v₂ := I₂.val _ hw
  rw [congrFun (runOps_rename c.sl rhsTail _ fun _ _ _ h =>
    sl_inj c hc.n0 h) W2, rhsTail_run] at v₂
  obtain U₁ : Unch base (slWk c [QXM, W1, W2, W3, TMP]) s.mem s₁.mem :=
    unch_slots (MP'_n c) rfl k₁.unch (by simp) (by simp)
  obtain U₂ : Unch base (slWk c [QXM, W1, W2, W3, TMP]) s₁.mem s₂.mem := PK.unch.mono fun w hw => by
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hw
      obtain ⟨op, hop, rfl⟩ := List.mem_map.mp ho
      obtain ⟨op₀, h₀, rfl⟩ := List.mem_map.mp hop
      exact List.mem_append_left _ (List.mem_map.mpr ⟨op₀.out, List.mem_cons_of_mem _ (rhsTail_out op₀ h₀), by
        rw [FOp.out_rename]; rfl⟩)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact List.mem_append_left _ (List.mem_map_of_mem (by decide))
      · exact List.mem_append_right _ (by simp [MP'_n])
  refine ⟨PK.scr hs₁, I₂.mod, k₁.rest.trans PK.rest,
    PK.rest.rd.trans k₁.rest.rd, PK.rest.wr.trans k₁.rest.wr,
    (U₁.trans U₂).mono (by intro w hw; simpa only [List.mem_append, or_self] using hw), I₂.lt _ hw, ?_⟩
  simpa only [sv, MP'_n, a₁, b₁, toM_cmont hc, v₁] using v₂

end VG.Proof.EcKey.Compressed.Arm

end

end

/-! ### `EcKey.Compressed.Arm.Peer`, which only this module used -/

section

/-! ### `EcKey.Compressed.Arm.TagCheck`, which only this module used -/

section

/-! # Accept precisely the compressed SEC 1 tags and retain their parity -/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.Arm

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
open VG.Proof.X25519.Arm (Rest wp_ldrb wp_str wp_dp wp_mov op2_imm op2_reg op2_lsr dpVal)

private theorem tagMask : ∀ b : Byte,
    0 - (((((b.setWidth 32 ||| 1) ^^^ 3) - 1) >>> 31)) = mask32 (b = 2 ∨ b = 3) := by
  decide

theorem decompressTag_ok {c : Cfg} {s : State} {base : Addr} {q : BitVec 32}
    (hs : Scr s base size) (hq : s.gpr .r1 = q)
    (hin : InRegions (s.rd ++ s.wr) (State.addr q) 1) (hD : c.sl D + 4 ≤ size) :
    WP isa (.block (Impl.EcKey.Compressed.Arm.decompressTag c)) s fun t =>
      t.gpr .r5 = mask32 (s.mem (State.addr q) = 2 ∨ s.mem (State.addr q) = 3) ∧
      t.mem.readW (off base (c.sl D)) 32 = (s.mem (State.addr q)).setWidth 32 ∧
      Rest [.r4, .r5] s t ∧ Outside base (c.sl D) 4 s.mem t.mem := by
  unfold Impl.EcKey.Compressed.Arm.decompressTag
  refine wp_ldrb (by decide) (a := State.addr q) (by rw [hq]; simp) hin fun s₁ u₁ => ?_
  obtain hs₁ := hs.of_rest (u₁.rest (ws := [.r4]) (by simp)) (by decide)
  refine wp_str (hs₁.off_lt (by omega_using [hD])) (hs₁.ea (by omega_using [hD])) (hs₁.write hD) fun s₂ m₂ => ?_
  refine wp_dp (op2_imm (by decide)) fun s₃ u₃ => ?_
  refine wp_dp (op2_imm (by decide)) fun s₄ u₄ => ?_
  refine wp_dp (op2_imm (by decide)) fun s₅ u₅ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₆ u₆ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₇ u₇ => ?_
  refine wp_dp (op2_reg _ _) fun t u₈ => WP.block_nil ?_
  obtain hm : t.mem = s.mem.writeW (off base (c.sl D)) ((s.mem (State.addr q)).setWidth 32) := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂.mem, u₁.mem, u₁.gpr]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [u₈.gpr, dpVal, u₇.gpr, u₇.other .r4 (by decide), u₆.gpr, u₅.gpr, dpVal,
      u₄.gpr, dpVal, u₃.gpr, dpVal, m₂.gpr, u₁.gpr]
    exact tagMask _
  · rw [hm, Mem.readW_writeW_self32]
  · exact (u₁.rest (by simp)).trans ((m₂.rest _).trans ((u₃.rest (by simp)).trans
      ((u₄.rest (by simp)).trans ((u₅.rest (by simp)).trans ((u₆.rest (by simp)).trans
      ((u₇.rest (by simp)).trans (u₈.rest (by simp))))))))
  · rw [hm]
    exact writeW32_outside _ _ _ (by have := hs.nowrap; omega_using [hD, this])

end VG.Proof.EcKey.Compressed.Arm

end

end


@[expose] public section
namespace VG.Proof.EcKey.Compressed.Arm
open Spec.Weierstrass
open VG.Impl.Mont.Arm
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Impl.Ecdh.Arm (R2P BP)
open VG.Proof.Ecdsa.Arm VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm VG.Proof.Ecdh.Arm
open VG.Proof.X25519.Arm (Rest wp_dp op2_imm dpVal ea toNat_add_lt toNat_imm)

theorem decompressPeer_eq (c : Cfg) : Impl.EcKey.Compressed.Arm.decompressPeer c =
    setConst c.n (c.sl R2P) (c.R * c.R % c.C.p) ++
    (setConst c.n (c.sl BP) (c.mont c.C.b) ++
    (.dp .add .r6 .r1 (.imm 1) ::
    (loadBytes c.C.len c.n (c.sl E) .r6 ++
    (Impl.EcKey.Compressed.Arm.decompressTag c ++
    (c.andFlag ++ Impl.Ecdh.Arm.Cfg.checkLtP c (c.sl E)))))) := by
  simp only [Impl.EcKey.Compressed.Arm.decompressPeer, Impl.Ecdh.Arm.Cfg.consts,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc,
    List.cons_append, List.nil_append]

theorem decompressPeer_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hqfit : (s.gpr .r1).toNat + (1 + c.C.len) ≤ 2 ^ 32)
    (hin : (⟨State.addr (s.gpr .r1), 1 + c.C.len⟩ : Region) ∈ s.rd ++ s.wr)
    (hd : Region.Disjoint ⟨State.addr (s.gpr .r1), 1 + c.C.len⟩ ⟨base, size⟩)
    (hmp : sv c base s MP = c.C.p) (hf : flagW c base s = BitVec.allOnes 32) :
    WP isa (.block (Impl.EcKey.Compressed.Arm.decompressPeer c)) s fun t =>
      Scr t base size ∧ Rest [.r3, .r4, .r5, .r6, .r7, .r8] s t ∧
      Unch base (slW c [R2P, BP, E, D, FLAG]) s.mem t.mem ∧
      sv c base t R2P = c.R * c.R % c.C.p ∧ sv c base t BP = c.mont c.C.b ∧
      sv c base t E = ofBytes (Spec.Ecdsa.bytesAt s.mem (State.addr (s.gpr .r1) + 1) c.C.len) ∧
      t.mem.readW (off base (c.sl D)) 32 = (s.mem (State.addr (s.gpr .r1))).setWidth 32 ∧
      flagW c base t = mask32 ((s.mem (State.addr (s.gpr .r1)) = 2 ∨
        s.mem (State.addr (s.gpr .r1)) = 3) ∧ sv c base t E < c.C.p) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpl := hc.p_lt
  have hp3 := hc.p_ge
  have hl8 := hc.len8
  have hlhi := hc.len_hi
  obtain hF : c.sl FLAG + 4 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega_arith
  obtain hR2 := sl_le c h7 (i := R2P) (by decide)
  obtain hB := sl_le c h7 (i := BP) (by decide)
  obtain hE := sl_le c h7 (i := E) (by decide)
  obtain hM := sl_le c h7 (i := MP) (by decide)
  obtain hD := sl_le c h7 (i := D) (by decide)
  obtain hq : Reg.r1 ∉ [Reg.r4, .r6] := by decide
  generalize hq32 : s.gpr .r1 = q32 at hqfit hin hd ⊢
  generalize hq64 : State.addr q32 = qa at hin hd ⊢
  rw [decompressPeer_eq]
  -- The constants.
  refine VG.Proof.X25519.Arm.WP.append (setConst_ok hs hR2 (show c.R * c.R % c.C.p < 2 ^ (64 * c.n) from
    Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) hpl)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  obtain hs₁ := hs.of_rest k₁ (by decide)
  refine VG.Proof.X25519.Arm.WP.append (setConst_ok hs₁ hB (show c.mont c.C.b < 2 ^ (64 * c.n) from
    Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) hpl)) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  obtain hs₂ := hs₁.of_rest k₂ (by decide)
  obtain W₂ : Outside base 0 size s.mem s₂.mem :=
    (O₁.mono (Nat.zero_le _) (by omega_arith)).trans (O₂.mono (Nat.zero_le _) (by omega_arith))
  obtain K₂ : Rest [.r4] s s₂ := k₁.trans k₂
  -- `peer + 1`
  refine wp_dp (op2_imm (by decide)) fun s₃ u₃ => ?_
  obtain K₃ : Rest [.r4, .r6] s s₃ := (K₂.mono (by simp)).trans (u₃.rest (by simp))
  obtain hs₃ := hs.of_rest K₃ (by decide)
  have hm₃ : s₃.mem = s₂.mem := u₃.mem
  obtain hrw₃ : s₃.rd ++ s₃.wr = s.rd ++ s.wr := by rw [K₃.rd, K₃.wr]
  obtain hb₃ : s₃.gpr .r6 = q32 + BitVec.ofNat 32 1 := by
    rw [u₃.gpr, K₂.gpr _ (by decide), hq32]; rfl
  obtain ha₃ : State.addr (s₃.gpr .r6) = qa + BitVec.ofNat 64 1 := by
    rw [hb₃, ← hq64]; exact ea (by omega_arith)
  obtain ht₃ : (s₃.gpr .r6).toNat = q32.toNat + 1 := by
    rw [hb₃, toNat_add_lt (by rw [toNat_imm (by decide)]; omega_arith), toNat_imm (by decide)]
  -- `x`
  refine VG.Proof.X25519.Arm.WP.append (loadBytes_ok hs₃ (src := .r6) (by decide) hE (by omega_arith) (by omega_arith) hlhi
    (fun e he => ⟨_, by rw [hrw₃]; exact hin, by
      rw [ha₃, Offset.add_add]; exact Offset.contains_base qa (by omega_arith) (by omega_arith)⟩)
    (by rw [ha₃]; exact (hd.sub_left (Offset.sub_base qa (by omega_arith))).sub_right (Offset.sub_base base hE)))
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  rw [ha₃, hm₃] at e₄
  rw [hm₃] at O₄
  obtain hs₄ := hs₃.of_rest k₄ (by decide)
  obtain K₄ : Rest [.r4, .r6] s s₄ := K₃.trans (k₄.mono (by simp))
  obtain W₄ : Outside base 0 size s.mem s₄.mem := W₂.trans (O₄.mono (Nat.zero_le _) hE)
  obtain lead₄ : s₄.mem qa = s.mem qa := by
    obtain e := keep_of_disjoint' W₄ hd (by decide) (i := 0) (by omega_using []) (by omega_using [hqfit])
    simpa only [BitVec.add_zero] using e
  refine VG.Proof.X25519.Arm.WP.append (decompressTag_ok (q := q32) hs₄
    (by rw [K₄.gpr _ (by decide), hq32])
    (by rw [K₄.rd, K₄.wr, hq64]; exact ⟨_, hin, by simpa using Offset.contains_base qa (d := 0) (n := 1) (by omega_using []) (by decide)⟩)
    (by have := sl_le c h7 (i := D) (by decide); omega_using [h0, hD])) fun s₅ ⟨mask₅, tag₅, k₅, O₅⟩ => ?_
  rw [hq64, lead₄] at mask₅ tag₅
  obtain hs₅ := hs₄.of_rest k₅ (by decide)
  refine VG.Proof.X25519.Arm.WP.append (andFlag_ok c hs₅ hF) fun s₆ ⟨f₆, k₆, O₆⟩ => ?_
  obtain hs₆ := hs₅.of_rest k₆ (by decide)
  refine WP.mono (checkLtP_ok c hs₆ hE hM hF) fun t ⟨f₇, k₇, O₇⟩ => ?_
  obtain U₄ : Unch base (slW c [R2P, BP, E, D]) s.mem s₄.mem :=
    unch_same (unch_same (slot_frame (by simp) (Nat.le_refl _) O₁)
      (slot_frame (by simp) (Nat.le_refl _) O₂)) (slot_frame (by simp) (Nat.le_refl _) O₄)
  obtain U₅ := unch_same U₄ (slot_frame (by simp) (by omega_using [h0]) O₅)
  have v₅ {i : Nat} (hi : i < 45) (hw : i ∉ [R2P, BP, E, D]) :
      sv c base s₅ i = sv c base s i := sv_unch U₅ h7 hn hi (apart_slW hw)
  obtain x₅ : sv c base s₅ E = ofBytes (Spec.Ecdsa.bytesAt s.mem (qa + 1) c.C.len) := by
    change wordsVal s₅.mem base (c.sl E) c.n = _
    rw [sv_out (O₅.mono (Nat.le_refl _) (by omega_using [h0] : c.sl D + 4 ≤ c.sl D + 8 * c.n)) h7 hn (by decide) (by decide), e₄]
    congr 1
    exact bytesAt_keep W₂ (hd.sub_left (Offset.sub_base qa (d := 1) (by omega_using []))) (by decide) (by omega_using [hqfit])
  obtain flag₅ : flagW c base s₅ = BitVec.allOnes 32 := by
    rw [flagW, ← hf]
    exact Unch.readW32 U₅ (fun w hw => by have := (apart_slW (c := c) (by decide : FLAG ∉ [R2P, BP, E, D])) w hw; omega_using [h0, this]) (by omega_using [hn, hF])
  refine ⟨hs₆.of_rest k₇ (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (K₄.mono (by simp)).trans ((k₅.mono (by simp)).trans ((k₆.mono (by simp)).trans (k₇.mono (by simp))))
  · exact unch_same (unch_same (slots_widen U₅ (slots' := [R2P, BP, E, D, FLAG]) (by decide)) (slot_frame (by simp) (by omega_using [h0]) O₆)) (slot_frame (by simp) (by omega_using [h0]) O₇)
  · simp only [sv] at *
    rw [sv_flag O₇ h0 h7 hn (by decide) (by decide), sv_flag O₆ h0 h7 hn (by decide) (by decide),
      sv_out (O₅.mono (Nat.le_refl _) (by omega_using [h0] : c.sl D + 4 ≤ c.sl D + 8 * c.n)) h7 hn (by decide) (by decide),
      sv_out O₄ h7 hn (by decide) (by decide), sv_out O₂ h7 hn (by decide) (by decide)]
    exact e₁
  · simp only [sv] at *
    rw [sv_flag O₇ h0 h7 hn (by decide) (by decide), sv_flag O₆ h0 h7 hn (by decide) (by decide),
      sv_out (O₅.mono (Nat.le_refl _) (by omega_using [h0] : c.sl D + 4 ≤ c.sl D + 8 * c.n)) h7 hn (by decide) (by decide),
      sv_out O₄ h7 hn (by decide) (by decide)]
    exact e₂
  · simp only [sv] at *
    rw [sv_flag O₇ h0 h7 hn (by decide) (by decide), sv_flag O₆ h0 h7 hn (by decide) (by decide), x₅]
  · rw [BitVec.eq_of_toNat_eq (O₇.w32 (by have := sl_apart c (i := D) (j := FLAG) (by decide); omega_using [h0, this]) (by omega_using [hn, hD])),
      BitVec.eq_of_toNat_eq (O₆.w32 (by have := sl_apart c (i := D) (j := FLAG) (by decide); omega_using [h0, this]) (by omega_using [hn, hD]))]
    exact tag₅
  · simp only [sv] at *
    rw [f₇, f₆, flag₅, mask₅, BitVec.allOnes_and,
      show wordsVal s₆.mem base (c.sl E) c.n = sv c base s₆ E from rfl,
      show wordsVal s₆.mem base (c.sl MP) c.n = sv c base s₆ MP from rfl]
    simp only [sv]
    simp only [mask32, sv_flag O₆ h0 h7 hn (i := E) (by decide) (by decide),
      sv_flag O₆ h0 h7 hn (i := MP) (by decide) (by decide),
      v₅ (i := MP) (by decide) (by decide), hmp,
      sv_flag O₇ h0 h7 hn (i := E) (by decide) (by decide)]
    exact mask32_and _ _

end VG.Proof.EcKey.Compressed.Arm

end

end


/-! # Prepare the curve polynomial and retain the input checks on ARMv7 -/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.Arm

open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Proof.Ecdsa.Arm
open VG.Impl.Ecdh.Arm (R2P BP W2)
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm

abbrev CompressedPrefix (c : Cfg) (s : State) : Prop :=
  (s.mem (ptr s .r1) = 2 ∨ s.mem (ptr s .r1) = 3) ∧ keyX c s < c.C.p

structure DecompressFront (c : Cfg) (s₀ s : State) : Prop where
  scr : Scr s (ptr s₀ .r2) size
  far : Far s (ptr s₀ .r2) 8192
  fixed : Fixed c (ptr s₀ .r2) s₀.gpr s.mem
  out : s.gpr .lr = s₀.gpr .r0
  x : sv c (ptr s₀ .r2) s E = keyX c s₀
  tag : s.mem.readW (off (ptr s₀ .r2) (c.sl D)) 32 = (s₀.mem (ptr s₀ .r1)).setWidth 32
  r2 : sv c (ptr s₀ .r2) s R2P = c.R * c.R % c.C.p
  rhs_lt : sv c (ptr s₀ .r2) s W2 < c.C.p
  rhs : toM c.C.p (2 ^ (64 * c.n)) (sv c (ptr s₀ .r2) s W2) =
    let x := Fin.ofNat c.C.p (keyX c s₀)
    x * x * x + Fin.ofNat c.C.p c.C.a * x + Fin.ofNat c.C.p c.C.b
  flag : flagW c (ptr s₀ .r2) s = mask32 (CompressedPrefix c s₀)
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem DecompressFront.frame {c : Cfg} (hc : CfgOk c) {s₀ s t : State}
    (F : DecompressFront c s₀ s) (K : VG.Proof.X25519.Arm.Rest powClob s t)
    {W : List (Nat × Nat)} (U : Unch (ptr s₀ .r2) W s.mem t.mem) (hW : FixedOk c W)
    (ha : ∀ i ∈ [E, D, R2P, W2, FLAG], ∀ w ∈ W,
      c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i) : DecompressFront c s₀ t := by
  have hn := F.scr.nowrap
  have h0 := hc.n0
  have h7 := hc.n10
  have e {i : Nat} (hi : i < 45) (hm : i ∈ [E, D, R2P, W2, FLAG]) :
      sv c (ptr s₀ .r2) t i = sv c (ptr s₀ .r2) s i := sv_unch U h7 hn hi (ha i hm)
  have ew {i : Nat} (hi : i < 45) (hm : i ∈ [E, D, R2P, W2, FLAG]) :
      t.mem.readW (off (ptr s₀ .r2) (c.sl i)) 32 = s.mem.readW (off (ptr s₀ .r2) (c.sl i)) 32 :=
    Unch.readW32 U (fun w hw => by have := ha i hm w hw; omega_using [h0, this])
      (by have := sl_le c h7 hi; omega_using [hn, this])
  refine ⟨F.scr.of_rest K (by decide), F.far.of_rest K, F.fixed.unch h7 hn hW U,
    (K.gpr _ (by decide)).trans F.out, (e (by decide) (by simp)).trans F.x,
    (ew (by decide) (by simp)).trans F.tag, (e (by decide) (by simp)).trans F.r2,
    ?_, ?_, ?_, K.sp.trans F.sp, K.rd.trans F.rd, K.wr.trans F.wr⟩
  · rw [e (by decide) (by simp)]; exact F.rhs_lt
  · rw [e (by decide) (by simp)]; exact F.rhs
  · rw [flagW, ew (by decide) (by simp), ← flagW]; exact F.flag

theorem decompressFront_ok {c : Cfg} (hc : CfgOk c) {s₀ : State}
    (hp : InputPre c (1 + c.C.len) s₀) {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s, DecompressFront c s₀ s → WP isa rest s Q) :
    WP isa (.seq (.block (c.setupWith Impl.EcKey.Compressed.Arm.args))
      (.seq (.block (Impl.EcKey.Compressed.Arm.decompressPeer c))
      (.seq (Impl.Weierstrass.Arm.fprog c.SP (Impl.EcKey.Compressed.Arm.rhsOps c) c.umaal) rest))) s₀ Q := by
  have h7 := hc.n10
  have h0 := hc.n0
  obtain hd : Region.Disjoint ⟨ptr s₀ .r1, 1 + c.C.len⟩ ⟨ptr s₀ .r2, size⟩ :=
    hp.disjoint.sub_right (by simpa using Region.sub_prefix (by decide : size ≤ 8192))
  refine WP.seq (WP.mono (setup_ok hc (input_setup hp (by omega_using []))) fun s₁ S => ?_)
  change SetupPost c Impl.EcKey.Compressed.Arm.args s₀ (ptr s₀ .r2) s₁ at S
  obtain F₁ := setup_fixed S
  have hn := S.scr.nowrap
  obtain hr1 : s₁.gpr .r1 = s₀.gpr .r1 := S.keep.gpr _ (by decide)
  obtain W₁ : Outside (ptr s₀ .r2) 0 size s₀.mem s₁.mem := S.unch.outside (by simp)
  refine WP.seq (WP.mono (decompressPeer_ok hc S.scr
    (by rw [hr1]; exact hp.pk_fit)
    (by rw [hr1, S.keep.rd, S.keep.wr]; exact hp.pk)
    (by rw [hr1]; exact hd) F₁.mp S.flag) fun s₂ ⟨hs₂, K₂, U₂, r2₂, bp₂, x₂, tag₂, flag₂⟩ => ?_)
  obtain F₂ := F₁.unch h7 hn (fixedOk_slW (l := [R2P, BP, E, D, FLAG]) (by decide)) U₂
  obtain lead : s₁.mem (ptr s₀ .r1) = s₀.mem (ptr s₀ .r1) := by
    obtain e := keep_of_disjoint' W₁ hd (by decide) (i := 0) (by omega_using []) (by have := hc.len_hi; omega_using [h7, this])
    simpa only [BitVec.add_zero] using e
  obtain x₂' : sv c (ptr s₀ .r2) s₂ E = keyX c s₀ := by
    rw [x₂, hr1]
    congr 1
    exact bytesAt_keep W₁ (hd.sub_left (Offset.sub_base _ (d := 1) (by omega_using []))) (by decide)
      (by have := hc.len_hi; omega_using [h7, this])
  rw [hr1, lead] at tag₂ flag₂
  refine WP.seq (WP.mono (rhs_ok hc hs₂ (S.far.of_rest K₂) (modP_of hc F₂.mp) r2₂ F₂.ap bp₂)
    fun s₃ R => ?_)
  obtain F₃ := F₂.unch h7 hn (fixedOk_slWk h7 (l := [Impl.Ecdh.Arm.QXM, Impl.Ecdh.Arm.W1,
    W2, Impl.Ecdh.Arm.W3, TMP]) (by decide)) R.unch
  have e {i : Nat} (hi : i < 45) (hw : i ∉ [Impl.Ecdh.Arm.QXM, Impl.Ecdh.Arm.W1, W2, Impl.Ecdh.Arm.W3, TMP]) :
      sv c (ptr s₀ .r2) s₃ i = sv c (ptr s₀ .r2) s₂ i :=
    sv_unch R.unch h7 hn hi (apart_slWk h7 hi hw)
  have ew {i : Nat} (hi : i < 45) (hw : i ∉ [Impl.Ecdh.Arm.QXM, Impl.Ecdh.Arm.W1, W2, Impl.Ecdh.Arm.W3, TMP]) :
      s₃.mem.readW (off (ptr s₀ .r2) (c.sl i)) 32 = s₂.mem.readW (off (ptr s₀ .r2) (c.sl i)) 32 :=
    Unch.readW32 R.unch (fun w hw' => by have := apart_slWk h7 hi hw w hw'; omega_using [h0, this])
      (by have := sl_le c h7 hi; omega_using [hn, this])
  apply h s₃
  refine ⟨R.scr, (S.far.of_rest K₂).of_rest R.rest, F₃,
    (R.rest.gpr _ (by decide)).trans ((K₂.gpr _ (by decide)).trans S.lr),
    (e (by decide) (by decide)).trans x₂', (ew (by decide) (by decide)).trans tag₂,
    (e (by decide) (by decide)).trans r2₂, R.lt, ?_, ?_,
    R.rest.sp.trans (K₂.sp.trans S.keep.sp), R.rd.trans (K₂.rd.trans S.keep.rd),
    R.wr.trans (K₂.wr.trans S.keep.wr)⟩
  · simpa only [x₂'] using R.val
  · rw [flagW, ew (by decide) (by decide), ← flagW, flag₂, x₂']

end VG.Proof.EcKey.Compressed.Arm

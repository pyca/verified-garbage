module

public import VerifiedGarbage.Proof.EcKey.Compressed.X86.Front
public import VerifiedGarbage.Impl.EcKey.Compressed.X86.Decompress
public import VerifiedGarbage.Proof.Ecdsa.X86.Fixed
import VerifiedGarbage.Proof.Ecdsa.X86.Lays
import VerifiedGarbage.Proof.Ecdsa.X86.SlotOps
import VerifiedGarbage.Proof.Ecdsa.X86.Middle
import VerifiedGarbage.Proof.Ecdsa.X86.Stages
import VerifiedGarbage.Proof.Ecdh.X86.Validate
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
public import VerifiedGarbage.Proof.Ecdsa.X86.Main
public import VerifiedGarbage.Impl.Weierstrass.X86
public import VerifiedGarbage.Proof.Ecdsa.X86.Layout
public import VerifiedGarbage.Proof.Mont.X86.Loop
public import VerifiedGarbage.Proof.Weierstrass.Env
public import VerifiedGarbage.Proof.Weierstrass.Unch
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Spec.Ecdsa.Generic
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.EcKey.Compressed.X86.Frame
import VerifiedGarbage.Proof.Ecdh.X86.Peer
import VerifiedGarbage.Proof.Ecdsa.X86.Finish
import VerifiedGarbage.Proof.Ecdsa.X86.Scalar
import VerifiedGarbage.Proof.Weierstrass.X86.BytesLen
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Ecdsa.X86.Setup
public import VerifiedGarbage.Proof.Weierstrass.X86.Pow

/-! ### `EcKey.Compressed.X86.Rhs`, which only this module used -/

section

/-! # The curve polynomial used by coordinate recovery -/

@[expose] public section

namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdh.X86 (R2P BP QXM QYM QY W0 W1 W2 W3)
open VG.Impl.EcKey.Compressed.X86 (rhsOps)
open VG.Proof.Ecdsa.X86 VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86 VG.Proof.Ecdh.X86

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
  rest : Keeps clob s s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  unch : Unch base (slWk c [QXM, W1, W2, W3, TMP]) s.mem s'.mem
  lt : sv c base s' W2 < c.C.p
  val : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' W2) =
    let x := Fin.ofNat c.C.p (sv c base s E)
    x * x * x + Fin.ofNat c.C.p c.C.a * x + Fin.ofNat c.C.p c.C.b

theorem rhs_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hr2 : sv c base s R2P = c.R * c.R % c.C.p)
    (hap : sv c base s AP = c.mont c.C.a) (hbp : sv c base s BP = c.mont c.C.b) :
    WP isa (Impl.Weierstrass.X86.fprog c.SP (rhsOps c)) s (RhsPost c base s) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  change WP isa (.seq (VG.Impl.Weierstrass.X86.Mont.mulCall c.SP
    (c.sl QXM) (c.sl E) (c.sl R2P))
    (VG.Impl.Weierstrass.X86.fprog c.SP (rhsTail.map (FOp.rename c.sl)))) s _
  refine WP.seq (WP.mono (slMul_ok (MP'_n c) hc.fp h7 hs (o := QXM) (a := E) (b := R2P)
    (by decide) (by decide) (by decide)
    (by rw [hr2]; exact Nat.mod_lt _ (by have := hc.p_ge; omega_using [this])))
    fun s₁ ⟨k₁, lt₁, e₁⟩ => ?_)
  obtain hs₁ := k₁.scr hs
  obtain hM₁ := hM.keepX86 (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  obtain v₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ QXM) = Fin.ofNat c.C.p (sv c base s E) :=
    toM_r2 hpR (by simpa only [hr2, Cfg.R] using e₁)
  obtain a₁ : sv c base s₁ AP = c.mont c.C.a :=
    (sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)).trans hap
  obtain b₁ : sv c base s₁ BP = c.mont c.C.b :=
    (sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)).trans hbp
  obtain hL : Lay c.MP' size (· ∈ rhsSlots.map c.sl) := lay_map hc rfl rfl rfl (by decide)
  obtain hW : WkOk c.SP c.MP' c.C.p size c.wk (· ∈ rhsSlots.map c.sl) := by
    refine ⟨slCall (MP'_n c) hc.fp, ?_, sl_below_wk c (by decide), sl_below_wk c (by decide)⟩
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    obtain H : ∀ i ∈ rhsSlots, i < 45 := by decide
    exact sl_below_wk c (H i hi)
  obtain I : Inv c.MP' base size c.C.p (· ∈ rhsSlots.map c.sl) ([QXM, AP, BP].map c.sl)
      (fun o => toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₁.mem base o c.n)) s₁ := by
    refine ⟨hs₁, hM₁, ?_, ?_, fun _ _ => rfl⟩
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
  refine WP.mono (fprog_ok hL hW hpR _ I (fun op hop x hx => ?_)
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
      rcases hw with rfl | rfl | rfl
      · exact List.mem_append_left _ (List.mem_map_of_mem (by decide))
      · exact List.mem_append_right _ (by simp [MP'_n, wkW])
      · exact List.mem_append_right _ (by simp [wkW])
  refine ⟨PK.scr hs₁, I₂.mod, Keeps.trans ⟨k₁.gpr, k₁.rd, k₁.wr⟩ ⟨PK.gpr, PK.rd, PK.wr⟩,
    PK.rd.trans k₁.rd, PK.wr.trans k₁.wr,
    (U₁.trans U₂).mono (by intro w hw; simpa only [List.mem_append, or_self] using hw), I₂.lt _ hw, ?_⟩
  simpa only [sv, MP'_n, a₁, b₁, toM_cmont hc, v₁] using v₂

end VG.Proof.EcKey.Compressed.X86

end

end

/-! ### `EcKey.Compressed.X86.Peer`, which only this module used -/

section

-- Formerly `VerifiedGarbage/Proof/EcKey/Compressed/X86/TagCheck.lean`, which only this module imported.
section

/-! # Accept exactly SEC 1 tags 02 and 03 on 32-bit x86 -/

section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Ecdsa.X86
open VG.Proof.Ecdsa.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86 VG.Proof.Ecdh.X86

private theorem tag_key (b : Byte) :
    (((b.setWidth 32 ||| 1) ^^^ 3).toNat < (1 : BitVec 32).toNat) ↔ b = 2 ∨ b = 3 := by
  revert b; decide +kernel

theorem decompressTag_ok {c : Cfg} {s : State} {base : Addr} {q : BitVec 32}
    (hs : Scr s base size) (hq : readSrc s (.mem (Cfg.argOp 1)) = some q)
    (hin : InRegions (s.rd ++ s.wr) (q.setWidth 64) 1) (hD : c.sl D + 4 ≤ size) :
    WP isa (.block (Impl.EcKey.Compressed.X86.decompressTag c)) s fun t =>
      t.gpr .edx = mask32 (s.mem (q.setWidth 64) = 2 ∨ s.mem (q.setWidth 64) = 3) ∧
      t.mem.readW (off base (c.sl D)) 32 = (s.mem (q.setWidth 64)).setWidth 32 ∧
      Keeps [.ebx, .edx] s t ∧ Outside base (c.sl D) 4 s.mem t.mem := by
  unfold Impl.EcKey.Compressed.X86.decompressTag
  refine wp_movS hq fun s₁ u₁ _ => ?_
  refine wp_movzx8S (a := q.setWidth 64)
    (by show (s₁.gpr .ebx + BitVec.ofNat 32 0).setWidth 64 = _; rw [u₁.gpr, BitVec.add_zero])
    (by rw [u₁.rd, u₁.wr]; exact hin) fun s₂ u₂ _ => ?_
  obtain K₂ : Keeps [.ebx, .edx] s s₂ := (u₁.keeps.mono (by simp)).trans (u₂.keeps.mono (by simp))
  obtain hs₂ := hs.of_keeps K₂ (by decide)
  refine wp_storeS (hs₂.ea (by omega)) (hs₂.write hD) fun s₃ m₃ => ?_
  refine wp_orS rfl fun s₄ u₄ => ?_
  refine wp_logicS (.inr rfl) rfl fun s₅ u₅ => ?_
  refine wp_subS rfl fun s₆ u₆ cf₆ => ?_
  refine wp_sbbS rfl cf₆ fun t u₇ _ => WP.block_nil ?_
  obtain hm : t.mem = s.mem.writeW (off base (c.sl D)) ((s.mem (q.setWidth 64)).setWidth 32) := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, m₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.mem]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [u₇.gpr, sbb_mask]
    simp only [u₅.gpr, u₄.gpr, m₃.gpr, u₂.gpr, u₁.mem, reduceCtorEq, ite_false, decide_eq_true_eq, tag_key]
  · rw [hm, Mem.readW_writeW_self32]
  · exact K₂.trans ((m₃.keeps _).trans ((u₄.keeps.mono (by simp)).trans
      ((u₅.keeps.mono (by simp)).trans ((u₆.keeps.mono (by simp)).trans (u₇.keeps.mono (by simp))))))
  · rw [hm]
    exact writeW32_outside _ _ _ (by have := hs.nowrap; omega)

end VG.Proof.EcKey.Compressed.X86
end

end

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86 VG.Impl.Ecdsa.X86
open VG.Impl.Ecdh.X86 (R2P BP)
open VG.Proof.Ecdsa.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Weierstrass VG.Proof.Weierstrass.X86 VG.Proof.Ecdh.X86 Spec.Weierstrass

theorem decompressPeer_eq (c : Cfg) : Impl.EcKey.Compressed.X86.decompressPeer c =
    setConst c.n (c.sl R2P) (c.R * c.R % c.C.p) ++
    (setConst c.n (c.sl BP) (c.mont c.C.b) ++
    (([.mov .ebx (.mem (Cfg.argOp 1)), .alu .add .ebx (.imm 1)] : List Instr) ++
    (loadBytes c.C.len c.n (c.sl E) .ebx ++
    (Impl.EcKey.Compressed.X86.decompressTag c ++
    (c.andFlag ++ Impl.Ecdh.X86.Cfg.checkLtP c (c.sl E)))))) := by
  simp only [Impl.EcKey.Compressed.X86.decompressPeer, Impl.Ecdh.X86.Cfg.consts,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem decompressPeer_ok {c : Cfg} (hc : CfgOk c) {base : Addr} {s : State} {q32 : BitVec 32}
    (hs : Scr s base size)
    (hq : ∀ t : State, t.gpr .esp = s.gpr .esp → t.rd ++ t.wr = s.rd ++ s.wr →
      Outside base 0 size s.mem t.mem → readSrc t (.mem (Cfg.argOp 1)) = some q32)
    (hqfit : q32.toNat + (1 + c.C.len) ≤ 2 ^ 32)
    (hin : (⟨q32.setWidth 64, 1 + c.C.len⟩ : Region) ∈ s.rd ++ s.wr)
    (hd : Region.Disjoint ⟨q32.setWidth 64, 1 + c.C.len⟩ ⟨base, size⟩)
    (hmp : sv c base s MP = c.C.p) (hf : flagW c base s = BitVec.allOnes 32) :
    WP isa (.block (Impl.EcKey.Compressed.X86.decompressPeer c)) s fun t =>
      Scr t base size ∧ Keeps [.eax, .ebx, .edx] s t ∧
      Unch base (slW c [R2P, BP, E, D, FLAG]) s.mem t.mem ∧
      sv c base t R2P = c.R * c.R % c.C.p ∧ sv c base t BP = c.mont c.C.b ∧
      sv c base t E = ofBytes (Spec.Ecdsa.bytesAt s.mem (q32.setWidth 64 + 1) c.C.len) ∧
      t.mem.readW (off base (c.sl D)) 32 = (s.mem (q32.setWidth 64)).setWidth 32 ∧
      flagW c base t = mask32 ((s.mem (q32.setWidth 64) = 2 ∨ s.mem (q32.setWidth 64) = 3) ∧
        sv c base t E < c.C.p) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpl := hc.p_lt
  have hp3 := hc.p_ge
  have hsz : size = 8192 := rfl
  have hl8 := hc.len8
  have hlhi := hc.len_hi
  obtain hF : c.sl FLAG + 4 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega_using [hl8, hlhi, this]
  obtain hR2 := sl_le c h7 (i := R2P) (by decide)
  obtain hB := sl_le c h7 (i := BP) (by decide)
  obtain hE := sl_le c h7 (i := E) (by decide)
  obtain hM := sl_le c h7 (i := MP) (by decide)
  obtain hD := sl_le c h7 (i := D) (by decide)
  generalize hq64 : q32.setWidth 64 = q at hin hd ⊢
  rw [decompressPeer_eq]
  -- The constants.
  refine WP.block_append (WP.mono (setConst_ok hs hR2 (show c.R * c.R % c.C.p < 2 ^ (64 * c.n) from
    Nat.lt_trans (Nat.mod_lt _ (by omega_using [hp3])) hpl)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  refine WP.block_append (WP.mono (setConst_ok hs₁ hB (show c.mont c.C.b < 2 ^ (64 * c.n) from
    Nat.lt_trans (Nat.mod_lt _ (by omega_using [hp3])) hpl)) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_)
  obtain hs₂ := hs₁.of_keeps k₂ (by decide)
  obtain W₂ : Outside base 0 size s.mem s₂.mem :=
    (O₁.mono (Nat.zero_le _) (by omega_using [hR2])).trans (O₂.mono (Nat.zero_le _) (by omega_using [hB]))
  obtain k₂' : Keeps [.eax] s s₂ := k₁.trans k₂
  -- `peer + 1`
  refine WP.block_append ?_
  refine wp_movS (hq s₂ (k₂'.1 _ (by decide)) (by rw [k₂'.2.1, k₂'.2.2]) W₂) fun s₃ u₃ _ => ?_
  refine wp_addS rfl fun s₄ u₄ _ => WP.block_nil ?_
  obtain k₄ : Keeps [.eax, .ebx] s s₄ := ((k₂'.mono (by decide)).widen u₃.keeps).widen u₄.keeps
  obtain hs₄ := hs.of_keeps k₄ (by decide)
  obtain hm₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  obtain hrw₄ : s₄.rd ++ s₄.wr = s.rd ++ s.wr := by rw [k₄.2.1, k₄.2.2]
  obtain hb₄ : s₄.gpr .ebx = q32 + BitVec.ofNat 32 1 := by rw [u₄.gpr, u₃.gpr]; rfl
  obtain hb₄' : (s₄.gpr .ebx).setWidth 64 = q + BitVec.ofNat 64 1 := by
    rw [hb₄, ← hq64]; exact addr_eq (by omega_using [hqfit, hl8])
  obtain hbt₄ : (s₄.gpr .ebx).toNat = q32.toNat + 1 := by
    rw [hb₄, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hqfit, hl8])]
  -- `x`
  refine WP.block_append (WP.mono (loadBytes_ok hs₄ (src := .ebx) (by decide) hE (by omega_using [hqfit, hbt₄]) (by omega_using [hl8]) hlhi
    (fun e he => ⟨_, by rw [hrw₄]; exact hin, by
      rw [hb₄', Offset.add_add]; exact Offset.contains_base q (by omega_using [he]) (by omega_using [hsz, hlhi, hM, he])⟩)
    (by rw [hb₄']; exact (hd.sub_left (Offset.sub_base q (by omega_using []))).sub_right (Offset.sub_base base hE)))
    fun s₅ ⟨e₅, k₅, O₅⟩ => ?_)
  rw [hb₄', hm₄] at e₅
  rw [hm₄] at O₅
  obtain hs₅ := hs₄.of_keeps k₅ (by decide)
  obtain K₅ : Keeps [.eax, .ebx] s s₅ := k₄.widen k₅
  obtain W₅ : Outside base 0 size s.mem s₅.mem := W₂.trans (O₅.mono (Nat.zero_le _) hE)
  obtain lead₅ : s₅.mem q = s.mem q := by
    obtain e := keep_of_disjoint' W₅ hd (by decide) (i := 0) (by omega_arith) (by omega_arith)
    simpa only [BitVec.add_zero] using e
  refine WP.block_append (WP.mono (decompressTag_ok hs₅
    (hq s₅ (K₅.1 _ (by decide)) (by rw [K₅.2.1, K₅.2.2]) W₅)
    (by rw [hq64, K₅.2.1, K₅.2.2]; exact ⟨_, hin, by simpa using Offset.contains_base q (d := 0) (n := 1) (by omega_arith) (by decide)⟩)
    (by have := sl_le c h7 (i := D) (by decide); omega_arith)) fun s₆ ⟨mask₆, tag₆, k₆, O₆⟩ => ?_)
  rw [hq64, lead₅] at mask₆ tag₆
  obtain hs₆ := hs₅.of_keeps k₆ (by decide)
  refine WP.block_append (WP.mono (andFlag_ok c hs₆ hF) fun s₇ ⟨f₇, k₇, O₇⟩ => ?_)
  obtain hs₇ := hs₆.of_keeps k₇ (by decide)
  refine WP.mono (checkLtP_ok c hs₇ h0 hE hM hF) fun t ⟨f₈, k₈, O₈⟩ => ?_
  obtain U₅ : Unch base (slW c [R2P, BP, E, D]) s.mem s₅.mem :=
    unch_same (unch_same (slot_frame (by simp) (Nat.le_refl _) O₁)
      (slot_frame (by simp) (Nat.le_refl _) O₂)) (slot_frame (by simp) (Nat.le_refl _) O₅)
  obtain U₆ := unch_same U₅ (slot_frame (by simp) (by omega_arith) O₆)
  have v₆ {i : Nat} (hi : i < 45) (hw : i ∉ [R2P, BP, E, D]) :
      sv c base s₆ i = sv c base s i := sv_unch U₆ h7 hn hi (apart_slW hw)
  obtain x₆ : sv c base s₆ E = ofBytes (Spec.Ecdsa.bytesAt s.mem (q + 1) c.C.len) := by
    change wordsVal s₆.mem base (c.sl E) c.n = _
    rw [sv_out (O₆.mono (Nat.le_refl _) (by omega_arith : c.sl D + 4 ≤ c.sl D + 8 * c.n)) h7 hn (by decide) (by decide), e₅]
    congr 1
    exact bytesAt_keep W₂ (hd.sub_left (Offset.sub_base q (d := 1) (by omega_arith))) (by decide) (by omega_arith)
  obtain flag₆ : flagW c base s₆ = BitVec.allOnes 32 := by
    rw [flagW, ← hf]
    exact Unch.readW32 U₆ (fun w hw => by have := (apart_slW (c := c) (by decide : FLAG ∉ [R2P, BP, E, D])) w hw; omega_arith) (by omega_arith)
  refine ⟨hs₇.of_keeps k₈ (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (K₅.mono (by decide)).trans ((k₆.mono (by decide)).trans ((k₇.mono (by decide)).trans (k₈.mono (by decide))))
  · exact unch_same (unch_same (slots_widen U₆ (slots' := [R2P, BP, E, D, FLAG]) (by decide)) (slot_frame (by simp) (by omega_arith) O₇)) (slot_frame (by simp) (by omega_arith) O₈)
  · simp only [sv] at *
    rw [sv_flag O₈ h0 h7 hn (by decide) (by decide), sv_flag O₇ h0 h7 hn (by decide) (by decide),
      sv_out (O₆.mono (Nat.le_refl _) (by omega_arith : c.sl D + 4 ≤ c.sl D + 8 * c.n)) h7 hn (by decide) (by decide),
      sv_out O₅ h7 hn (by decide) (by decide), sv_out O₂ h7 hn (by decide) (by decide)]
    exact e₁
  · simp only [sv] at *
    rw [sv_flag O₈ h0 h7 hn (by decide) (by decide), sv_flag O₇ h0 h7 hn (by decide) (by decide),
      sv_out (O₆.mono (Nat.le_refl _) (by omega_arith : c.sl D + 4 ≤ c.sl D + 8 * c.n)) h7 hn (by decide) (by decide),
      sv_out O₅ h7 hn (by decide) (by decide)]
    exact e₂
  · simp only [sv] at *
    rw [sv_flag O₈ h0 h7 hn (by decide) (by decide), sv_flag O₇ h0 h7 hn (by decide) (by decide), x₆]
  · rw [BitVec.eq_of_toNat_eq (O₈.w32 (by have := sl_apart c (i := D) (j := FLAG) (by decide); omega_arith) (by omega_arith)),
      BitVec.eq_of_toNat_eq (O₇.w32 (by have := sl_apart c (i := D) (j := FLAG) (by decide); omega_arith) (by omega_arith))]
    exact tag₆
  · simp only [sv] at *
    rw [f₈, f₇, flag₆, mask₆, BitVec.allOnes_and,
      show wordsVal s₇.mem base (c.sl E) c.n = sv c base s₇ E from rfl,
      show wordsVal s₇.mem base (c.sl MP) c.n = sv c base s₇ MP from rfl]
    simp only [sv]
    simp only [mask32, sv_flag O₇ h0 h7 hn (i := E) (by decide) (by decide),
      sv_flag O₇ h0 h7 hn (i := MP) (by decide) (by decide),
      v₆ (i := MP) (by decide) (by decide), hmp,
      sv_flag O₈ h0 h7 hn (i := E) (by decide) (by decide)]
    exact mask32_and _ _

end VG.Proof.EcKey.Compressed.X86

end

end


/-! # Prepare the curve polynomial and retain the input checks on 32-bit x86 -/

@[expose] public section
namespace VG.Proof.EcKey.Compressed.X86

open VG VG.X86 VG.Impl.Ecdsa.X86 VG.Proof.Ecdsa.X86
open VG.Impl.Ecdh.X86 (R2P BP W2)
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86

abbrev CompressedPrefix (c : Cfg) (s : State) : Prop :=
  (s.mem (ptr s 1) = 2 ∨ s.mem (ptr s 1) = 3) ∧ keyX c s < c.C.p

structure DecompressFront (c : Cfg) (s₀ s : State) : Prop where
  scr : Scr s (ptr s₀ 2) size
  fixed : Fixed c (ptr s₀ 2) s₀.gpr s.mem
  x : sv c (ptr s₀ 2) s E = keyX c s₀
  tag : s.mem.readW (off (ptr s₀ 2) (c.sl D)) 32 = (s₀.mem (ptr s₀ 1)).setWidth 32
  r2 : sv c (ptr s₀ 2) s R2P = c.R * c.R % c.C.p
  rhs_lt : sv c (ptr s₀ 2) s W2 < c.C.p
  rhs : toM c.C.p (2 ^ (64 * c.n)) (sv c (ptr s₀ 2) s W2) =
    let x := Fin.ofNat c.C.p (keyX c s₀)
    x * x * x + Fin.ofNat c.C.p c.C.a * x + Fin.ofNat c.C.p c.C.b
  flag : flagW c (ptr s₀ 2) s = mask32 (CompressedPrefix c s₀)
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem DecompressFront.frame {c : Cfg} (hc : CfgOk c) {s₀ s t : State}
    (F : DecompressFront c s₀ s) (K : Keeps powClob s t)
    {W : List (Nat × Nat)} (U : Unch (ptr s₀ 2) W s.mem t.mem) (hW : FixedOk c W)
    (ha : ∀ i ∈ [E, D, R2P, W2, FLAG], ∀ w ∈ W,
      c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i) : DecompressFront c s₀ t := by
  have hn := F.scr.nowrap
  have h0 := hc.n0
  have h7 := hc.n10
  have e {i : Nat} (hi : i < 45) (hm : i ∈ [E, D, R2P, W2, FLAG]) :
      sv c (ptr s₀ 2) t i = sv c (ptr s₀ 2) s i := sv_unch U h7 hn hi (ha i hm)
  have ew {i : Nat} (hi : i < 45) (hm : i ∈ [E, D, R2P, W2, FLAG]) :
      t.mem.readW (off (ptr s₀ 2) (c.sl i)) 32 = s.mem.readW (off (ptr s₀ 2) (c.sl i)) 32 :=
    Unch.readW32 U (fun w hw => by have := ha i hm w hw; omega_using [h0, this])
      (by have := sl_le c h7 hi; omega_using [hn, this])
  refine ⟨F.scr.of_keeps K (by decide), F.fixed.unch h7 hn hW U,
     (e (by decide) (by simp)).trans F.x,
    (ew (by decide) (by simp)).trans F.tag, (e (by decide) (by simp)).trans F.r2,
    ?_, ?_, ?_, (K.1 _ (by decide)).trans F.esp, K.2.1.trans F.rd, K.2.2.trans F.wr⟩
  · rw [e (by decide) (by simp)]; exact F.rhs_lt
  · rw [e (by decide) (by simp)]; exact F.rhs
  · rw [flagW, ew (by decide) (by simp), ← flagW]; exact F.flag

theorem decompressFront_ok {c : Cfg} (hc : CfgOk c) {s₀ : State}
    (hp : InputPre c (1 + c.C.len) s₀) {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s, DecompressFront c s₀ s → WP isa rest s Q) :
    WP isa (.seq (.block (c.setupWith Impl.EcKey.Compressed.X86.args))
      (.seq (.block (Impl.EcKey.Compressed.X86.decompressPeer c))
      (.seq (Impl.Weierstrass.X86.fprog c.SP (Impl.EcKey.Compressed.X86.rhsOps c)) rest))) s₀ Q := by
  have h7 := hc.n10
  have h0 := hc.n0
  have hd : Region.Disjoint ⟨ptr s₀ 1, 1 + c.C.len⟩ ⟨ptr s₀ 2, size⟩ :=
    hp.disjoint
  refine WP.seq (WP.mono (setup_ok hc (input_setup hp (by omega_using []))) fun s₁ S => ?_)
  change SetupPost c Impl.EcKey.Compressed.X86.args s₀ (ptr s₀ 2) s₁ at S
  obtain F₁ := setup_fixed S
  have hn := S.scr.nowrap
  obtain W₁ : Outside (ptr s₀ 2) 0 size s₀.mem s₁.mem := S.unch.outside (by simp)
  refine WP.seq (WP.mono (decompressPeer_ok hc S.scr (q32 := arg s₀ 1)
    (by
      intro t hesp hrw W
      apply argLoad_ok (s₀ := s₀) (i := 1)
      · exact ⟨_, hp.args, arg_containsN (k := 3) (by have := hp.sp_fit; omega_using [this]) (by decide)⟩
      · exact hp.args_sc.sub_left (arg_subN (k := 3) (by have := hp.sp_fit; omega_using [this]) (by decide))
      · exact hesp.trans (S.keep.1 _ (by decide))
      · rw [hrw, S.keep.2.1, S.keep.2.2]
      · exact W₁.trans W)
    hp.pk_fit (by rw [S.keep.2.1, S.keep.2.2]; exact hp.pk) hd F₁.mp S.flag)
    fun s₂ ⟨hs₂, K₂, U₂, r2₂, bp₂, x₂, tag₂, flag₂⟩ => ?_)
  obtain F₂ := F₁.unch h7 hn (fixedOk_slW (l := [R2P, BP, E, D, FLAG]) (by decide)) U₂
  obtain lead : s₁.mem (ptr s₀ 1) = s₀.mem (ptr s₀ 1) := by
    obtain e := keep_of_disjoint' W₁ hd (by decide) (i := 0) (by omega_using []) (by have := hc.len_hi; omega_using [h7, this])
    simpa only [BitVec.add_zero] using e
  obtain x₂' : sv c (ptr s₀ 2) s₂ E = keyX c s₀ := by
    rw [x₂]
    congr 1
    exact bytesAt_keep W₁ (hd.sub_left (Offset.sub_base _ (d := 1) (by omega_using []))) (by decide)
      (by have := hc.len_hi; omega_using [h7, this])
  rw [lead] at tag₂ flag₂
  refine WP.seq (WP.mono (rhs_ok hc hs₂ (modP_of hc F₂.mp) r2₂ F₂.ap bp₂)
    fun s₃ R => ?_)
  obtain F₃ := F₂.unch h7 hn (fixedOk_slWk (l := [Impl.Ecdh.X86.QXM, Impl.Ecdh.X86.W1,
    W2, Impl.Ecdh.X86.W3, TMP]) (by decide)) R.unch
  have e {i : Nat} (hi : i < 45) (hw : i ∉ [Impl.Ecdh.X86.QXM, Impl.Ecdh.X86.W1, W2, Impl.Ecdh.X86.W3, TMP]) :
      sv c (ptr s₀ 2) s₃ i = sv c (ptr s₀ 2) s₂ i :=
    sv_unch R.unch h7 hn hi (apart_slWk hi hw)
  have ew {i : Nat} (hi : i < 45) (hw : i ∉ [Impl.Ecdh.X86.QXM, Impl.Ecdh.X86.W1, W2, Impl.Ecdh.X86.W3, TMP]) :
      s₃.mem.readW (off (ptr s₀ 2) (c.sl i)) 32 = s₂.mem.readW (off (ptr s₀ 2) (c.sl i)) 32 :=
    Unch.readW32 R.unch (fun w hw' => by have := (apart_slWk hi hw h7) w hw'; omega_using [h0, this])
      (by have := sl_le c h7 hi; omega_using [hn, this])
  apply h s₃
  refine ⟨R.scr, F₃,
    (e (by decide) (by decide)).trans x₂', (ew (by decide) (by decide)).trans tag₂,
    (e (by decide) (by decide)).trans r2₂, R.lt, ?_, ?_,
    (R.rest.1 _ (by decide)).trans ((K₂.1 _ (by decide)).trans (S.keep.1 _ (by decide))),
    R.rd.trans (K₂.2.1.trans S.keep.2.1), R.wr.trans (K₂.2.2.trans S.keep.2.2)⟩
  · simpa only [x₂'] using R.val
  · rw [flagW, ew (by decide) (by decide), ← flagW, flag₂, x₂']

end VG.Proof.EcKey.Compressed.X86

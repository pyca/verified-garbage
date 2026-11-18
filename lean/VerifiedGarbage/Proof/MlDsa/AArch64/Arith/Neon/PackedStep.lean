module

import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.PackedSpec
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Mem
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Step
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Table
public import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Ntt
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Bfly
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
public import VerifiedGarbage.Proof.MlDsa.Arith.Ntt

/-! ### `MlDsa.AArch64.Arith.Neon.Block`, which this module and modules that import it used -/

section

/-! ### `MlDsa.AArch64.Arith.Neon.Table`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (Tab)
open VG.Proof.MlKem.AArch64 (Keep wp_vop VChg)
open VG.Spec.MlDsa (q Zq zetas)

def TabZ (tab : Nat → Nat) (zt : Zq → Zq) : Prop :=
  ∀ k, tab k = (zt (zetas k)).val*2^32%q

theorem zetaTab_eq : TabZ zetaTab id := by
  intro k
  change zetaTab k = (Spec.MlDsa.zetas k).val*2^32%q
  rw [zetaTab,← zetaNat_eq,zetaNat,Nat.mod_mul_mod]

theorem loadZ_ok (up : Bool) (s : State)
    (hin : InRegions (s.rd++s.wr) (s.gpr .x3) 4) :
    WP isa (.block [.ldr .w .x6 .x3 0,stepZ up]) s fun s' =>
      ((s'.gpr .x6 = (s.mem.readW (s.gpr .x3) 32).setWidth 64 ∧
        s'.gpr .x3 = (if up then s.gpr .x3+4 else s.gpr .x3-4) ∧ s'.mem = s.mem) ∧
        Keep [.x6,.x3] s s') ∧ s'.v = s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by cases up <;> rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by cases up <;> rfl) (hv := by cases up <;> rfl)
  cases up <;> arun [stepZ,hin] <;> rfl

/-- A full-width vector of the table's zeta for a large NTT block. -/
theorem zetas_large_ok {tab : Nat → Nat} {zt : Zq → Zq} (htz : TabZ tab zt)
    {len : Nat} (hl1 : len ≠ 1) (hl2 : len ≠ 2) (up : Bool) {s : State} {p : Addr} {k : Nat}
    (hk : k < 256) (h3 : s.gpr .x3 = coeffAddr p k) (ht : Tab tab s.mem p 256)
    (hp : pR p ∈ s.rd++s.wr) (hc : VConsts s) :
    WP isa (.block (Impl.MlDsa.AArch64.Arith.Neon.zetas len up)) s fun s' =>
      Zetas (s'.v .v18) (fun _ => zt (Spec.MlDsa.zetas k)) ∧ VConsts s' ∧
      s'.gpr .x3 = (if up then s.gpr .x3+4 else s.gpr .x3-4) ∧ s'.mem = s.mem ∧
      Keep [.x6,.x3] s s' := by
  simp only [Impl.MlDsa.AArch64.Arith.Neon.zetas,hl1,hl2,ite_false]
  have hread : (s.mem.readW (s.gpr .x3) 32).toNat = (zt (Spec.MlDsa.zetas k)).val*2^32%q := by
    rw [h3,← coeffAt_eq,ht k hk,BitVec.toNat_ofNat,htz k]
    exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))
  change WP isa (.block ([.ldr .w .x6 .x3 0,stepZ up] ++ [.vop (.dup .s4 .v18 .x6)])) s _
  rw [WP.block_append_iff]
  refine WP.mono (loadZ_ok up s (by rw [h3]; exact ⟨_,hp,coeff_contains _ hk⟩))
    fun s₁ ⟨⟨⟨h6,h3',hm⟩,h₁⟩,hv⟩ => wp_vop (d := .v18) rfl fun s₂ h₂ =>
      WP.block_nil_iff.mpr ⟨?_, ?_, by rw [h₂.gpr]; exact h3', by rw [h₂.mem]; exact hm,
        (h₁.trans h₂.keep).mono⟩
  · intro e he
    rw [h₂.v]
    change (vword (ofVWords ((s₁.gpr .x6).setWidth 32) ((s₁.gpr .x6).setWidth 32)
      ((s₁.gpr .x6).setWidth 32) ((s₁.gpr .x6).setWidth 32)) e).toNat = _
    rw [VG.Proof.MlKem.AArch64.vword_dup_s4 _ he,h6,
      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),BitVec.setWidth_eq,hread]
  · exact (⟨by rw [hv]; exact hc.q, by rw [hv]; exact hc.qi⟩ : VConsts s₁).chg h₂.chg
end VG.Proof.MlDsa.AArch64.Arith.Neon

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (Tab wp_countdown imm16)
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa (Poly Zq)
open VG.Proof.MlDsa (PolyIs)

abbrev clob : List Reg := [.x2,.x3,.x4,.x5,.x6]

structure BInv (fP : Addr) (s s' : State) : Prop where
  keep : Keep clob s s'
  frame : Frame [pR fP] s.mem s'.mem
  consts : VConsts s'

theorem BInv.refl {p : Addr} {s : State} (hc : VConsts s) : BInv p s s :=
  ⟨Keep.refl _ _, Frame.refl _ _,hc⟩

theorem BInv.trans {p : Addr} {s₁ s₂ s₃ : State} (h₁ : BInv p s₁ s₂) (h₂ : BInv p s₂ s₃) :
    BInv p s₁ s₃ := ⟨(h₁.keep.trans h₂.keep).mono,h₁.frame.trans h₂.frame,h₂.consts⟩

theorem counter5_ok (N : Nat) (hN : N < 65536) (s : State) :
    WP isa (.block [.movz .x .x5 (BitVec.ofNat 16 N) 0]) s fun s' =>
      ((s'.gpr .x5 = BitVec.ofNat 64 N ∧ s'.mem = s.mem) ∧ Keep [.x5] s s') ∧ s'.v = s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  arun [imm16 hN]

theorem blockEnd_ok (len : Nat) (hl : len ≤ 128) (s : State) :
    WP isa (.block [.addImm .x .x2 .x2 (4*len),.subImm .x .x4 .x4 1]) s fun s' =>
      ((s'.gpr .x2 = s.gpr .x2+BitVec.ofNat 64 (4*len) ∧ s'.gpr .x4 = s.gpr .x4-1 ∧
        s'.mem = s.mem) ∧ Keep [.x2,.x4] s s') ∧ s'.v = s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  arun [show 4*len < 4096 by omega_using [hl]]
  rfl

section
variable {bf : List Instr} {op : Zq → Zq → Zq → Zq × Zq} {zt : Zq → Zq}
  (hbf : VBflyOk bf op zt) {blk : Poly → Nat → Nat → Nat → Nat → Poly} (hblk : BlkOk blk op)
include hbf hblk

theorem block_ok {fP zP : Addr} {len st k : Nat} (h4 : 4 ≤ len) (hl : len ≤ 128)
    (hl4 : len%4 = 0) (hs : st+2*len ≤ 256) (hk : k < 256)
    {tab : Nat → Nat} (hzt : TabZ tab zt) (up : Bool) {G : Poly} {s : State}
    (hx : s.gpr .x2 = coeffAddr fP st) (h3 : s.gpr .x3 = coeffAddr zP k)
    (hc : VConsts s) (hP : PolyIs s.mem fP G) (ht : Tab tab s.mem zP 256)
    (hw : pR fP ∈ s.wr) (hzp : pR zP ∈ s.rd++s.wr) :
    WP isa (block bf len up) s fun s' =>
      PolyIs s'.mem fP (blk G len k st len) ∧ s'.gpr .x2 = coeffAddr fP (st+2*len) ∧
      s'.gpr .x3 = (if up then s.gpr .x3+4 else s.gpr .x3-4) ∧
      s'.gpr .x4 = s.gpr .x4-1 ∧ BInv fP s s' := by
  have hN : len/4 < 65536 := by omega_using [hl]
  have hN0 : 0 < len/4 := by omega_using [h4]
  have hcov : 4*(len/4) = len := by omega_using [hl4]
  unfold block
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (zetas_large_ok hzt (by omega_using [h4]) (by omega_using [h4]) up hk h3 ht hzp hc)
    fun s₁ ⟨lz,c₁,h31,hm₁,k₁⟩ => ?_
  refine WP.mono (counter5_ok (len/4) hN s₁) fun s₂ ⟨⟨⟨hcnt,hm₂⟩,k₂⟩,hv₂⟩ => ?_
  have c₂ : VConsts s₂ := ⟨by rw [hv₂]; exact c₁.q, by rw [hv₂]; exact c₁.qi⟩
  have z₂ : Zetas (s₂.v .v18) (fun _ => zt (Spec.MlDsa.zetas k)) := by rw [hv₂]; exact lz
  refine WP.seq (WP.mono (wp_countdown (cnt := .x5) (N := len/4) (by omega_using [hl]) hN0
    (fun u s' => PolyIs s'.mem fP (blk G len k st (4*u)) ∧
      s'.gpr .x2 = coeffAddr fP (st+4*u) ∧ s'.v .v18 = s₂.v .v18 ∧ Keep [.x2,.x5] s₂ s' ∧ BInv fP s₂ s')
    (fun u hu s' ⟨hp,hx',hv',hki,hi⟩ _ => ?_)
    ⟨by rw [hblk.zero,hm₂,hm₁]; exact hP,
      by rw [k₂.get .x2,k₁.get .x2,hx]; rfl,rfl,Keep.refl _ _,BInv.refl c₂⟩ hcnt)
    fun s₃ ⟨hp,hx3,hv3,hki3,hi3⟩ => ?_)
  · refine WP.mono (step_ok hbf hblk (by omega_using [h4]) hl4 hs (by omega_using [hu]) hi.consts
      (by rw [hv']; exact z₂) hx' hp (by rw [hi.keep.wr,k₂.wr,k₁.wr]; exact hw))
      fun s'' ⟨hp',hf',hc',hv'',hx'',hcnt',hk'⟩ =>
        ⟨⟨hp',hx'',hv''.trans hv',(hki.trans hk').mono,hi.trans ⟨hk'.mono,hf',hc'⟩⟩,hcnt'⟩
  · refine WP.mono (blockEnd_ok len hl s₃) fun s₄ ⟨⟨⟨hx4,hcnt4,hm4⟩,k₄⟩,hv4⟩ =>
      ⟨by rw [hm4]; simpa only [hcov] using hp, ?_, ?_, ?_,
        ⟨(((k₁.trans k₂).trans hi3.keep).trans k₄).mono, ?_,
          ⟨by rw [hv4]; exact hi3.consts.q, by rw [hv4]; exact hi3.consts.qi⟩⟩⟩
    · rw [hx4,hx3,hcov,coeffAddr_add,show st+len+len = st+2*len by omega_using []]
    · rw [k₄.get .x3,hki3.get .x3,k₂.get .x3,h31]
    · rw [hcnt4,hki3.get .x4,k₂.get .x4,k₁.get .x4]
    · rw [hm4]; simpa only [hm₂,hm₁] using hi3.frame
end
end VG.Proof.MlDsa.AArch64.Arith.Neon

end

end

/-! ### `MlDsa.AArch64.Arith.Neon.PackedTable`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (Tab)
open VG.Proof.MlKem.AArch64 (Keep VChg wp_vop wp_ldrq)
open VG.Spec.MlDsa (q Zq)

set_option linter.unusedSimpArgs false

theorem vword_ext8 (v : BitVec 128) {e : Nat} (he : e < 4) :
    vword (((v++v) >>> (8*8)).extractLsb' 0 128) e = vword v ((e+2)%4) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 by omega_arith) with rfl | rfl | rfl | rfl <;>
    simp only [vword,BitVec.getLsbD_extractLsb',BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_append,Nat.reduceAdd,Nat.reduceMul,Nat.reduceMod,Nat.zero_add]
  all_goals rw [BitVec.getLsbD_append]
  all_goals simp +arith [hi]
  all_goals simp [show i ≤ 31 by omega_arith,show i ≤ 63 by omega_arith,show i ≤ 95 by omega_arith,show i ≤ 127 by omega_arith]

theorem table_vec {tab : Nat → Nat} {zt : Zq → Zq} (hzt : TabZ tab zt)
    {m : Mem} {p : Addr} (ht : Tab tab m p 256) {k : Nat} (hk : k+4 ≤ 256) :
    Zetas (m.read (coeffAddr p k) 16) (fun e => zt (Spec.MlDsa.zetas (k+e))) := fun e he => by
  rw [vword_read16 _ _ he,coeffAddr_add,← coeffAt_eq,ht (k+e) (by omega_arith),
    BitVec.toNat_ofNat,hzt (k+e)]
  exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))

theorem zetaPerms_ok {s : State} {F : Nat → Zq} (len : Nat) (hlen : len = 1 ∨ len = 2)
    (up : Bool) (hz : Zetas (s.v .v18) F) :
    WP isa (.block (zetaPerms len up)) s fun s' => VChg [.v18] s s' ∧
      Zetas (s'.v .v18) (fun e => F (if up then e/len else 4/len-1-e/len)) := by
  rcases hlen with rfl | rfl <;> cases up
  · change WP isa (.block [.vop (.rev .rev64s .v18 .v18),.vop (.ext .v18 .v18 .v18 8)]) s _
    refine wp_vop (d := .v18) rfl fun s₁ h₁ => wp_vop (d := .v18) rfl fun s₂ h₂ =>
      WP.block_nil_iff.mpr ⟨(h₁.chg.trans h₂.chg).mono,?_⟩
    intro e he
    simp only [Nat.div_one,ite_true,ite_false,Nat.reduceDiv,Nat.reduceSub]
    change (vword (s₂.v .v18) e).toNat = (F (3-e)).val*2^32%q
    rw [h₂.v,vword_ext8 _ he,h₁.v,VG.Proof.MlKem.AArch64.vword_rev64s _ (by omega_arith)]
    have hi : (if ((e+2)%4)%2 = 0 then (e+2)%4+1 else (e+2)%4-1) = 3-e := by split <;> omega_arith
    rw [hi]; exact hz _ (by omega_arith)
  · change WP isa (.block []) s _
    refine WP.block_nil_iff.mpr ⟨VChg.refl _ _,?_⟩
    intro e he
    simp only [Nat.div_one,ite_true,ite_false,Nat.reduceDiv,Nat.reduceSub]
    change (vword (s.v .v18) e).toNat = (F e).val*2^32%q
    exact hz e he
  · change WP isa (.block [.vop (.perm .zip1 .s4 .v18 .v18 .v18),.vop (.ext .v18 .v18 .v18 8)]) s _
    refine wp_vop (d := .v18) rfl fun s₁ h₁ => wp_vop (d := .v18) rfl fun s₂ h₂ =>
      WP.block_nil_iff.mpr ⟨(h₁.chg.trans h₂.chg).mono,?_⟩
    intro e he
    simp only [Nat.div_one,ite_true,ite_false,Nat.reduceDiv,Nat.reduceSub]
    change (vword (s₂.v .v18) e).toNat = (F (1-e/2)).val*2^32%q
    rw [h₂.v,vword_ext8 _ he,h₁.v,VG.Proof.MlKem.AArch64.vword_zip1_s4 _ (by omega_arith)]
    have hi : ((e+2)%4)/2 = 1-e/2 := by omega_arith
    rw [hi]; exact hz _ (by omega_arith)
  · change WP isa (.block [.vop (.perm .zip1 .s4 .v18 .v18 .v18)]) s _
    refine wp_vop (d := .v18) rfl fun s' h => WP.block_nil_iff.mpr ⟨h.chg,?_⟩
    intro e he
    simp only [Nat.div_one,ite_true,ite_false,Nat.reduceDiv,Nat.reduceSub]
    change (vword (s'.v .v18) e).toNat = (F (e/2)).val*2^32%q
    rw [h.v,VG.Proof.MlKem.AArch64.vword_zip1_s4 _ he]; exact hz _ (by omega_arith)

def baseZ (len : Nat) (up : Bool) (k : Nat) : Nat := if up then k else k-(4/len-1)

theorem coeffAddr_sub (p : Addr) (k j : Nat) (hj : j ≤ k) :
    coeffAddr p k - BitVec.ofNat 64 (4*j) = coeffAddr p (k-j) := by
  have h : coeffAddr p (k-j) + BitVec.ofNat 64 (4*j) = coeffAddr p k := by
    rw [coeffAddr_add,Nat.sub_add_cancel hj]
  rw [← h,BitVec.add_sub_cancel]

theorem moveZ_ok (N : Nat) (hN : N < 4096) (up : Bool) (s : State) :
    WP isa (.block [if up then .addImm .x .x3 .x3 N else .subImm .x .x3 .x3 N]) s fun s' =>
      ((s'.gpr .x3 = (if up then s.gpr .x3+BitVec.ofNat 64 N else s.gpr .x3-BitVec.ofNat 64 N) ∧
        s'.mem = s.mem) ∧ Keep [.x3] s s') ∧ s'.v = s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by cases up <;> rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by cases up <;> rfl) (hv := by cases up <;> rfl)
  cases up <;> arun [hN] <;> rfl

theorem zetaPre_ok (len : Nat) (hlen : len = 1 ∨ len = 2) (up : Bool) {p : Addr} {k : Nat} {s : State}
    (hb : up = false → 4/len ≤ k) (h3 : s.gpr .x3 = coeffAddr p k) :
    WP isa (.block (if up then [] else [.subImm .x .x3 .x3 (4*(4/len-1))])) s fun s' =>
      ((s'.gpr .x3 = coeffAddr p (baseZ len up k) ∧ s'.mem = s.mem) ∧ Keep [.x3] s s') ∧ s'.v = s.v := by
  cases up
  · have hN : 4*(4/len-1) < 4096 := by rcases hlen with rfl | rfl <;> decide
    refine WP.mono (moveZ_ok _ hN false s) fun s' ⟨⟨⟨hx,hm⟩,hk⟩,hv⟩ => ⟨⟨⟨?_,hm⟩,hk⟩,hv⟩
    rw [hx,h3,coeffAddr_sub _ _ _ (by have := hb rfl; omega_arith)]
    rfl
  · exact WP.block_nil_iff.mpr ⟨⟨⟨h3,rfl⟩,Keep.refl _ _⟩,rfl⟩

theorem zetaPost_ok (len : Nat) (hlen : len = 1 ∨ len = 2) (up : Bool) (s : State) :
    WP isa (.block [if up then .addImm .x .x3 .x3 (16/len) else .subImm .x .x3 .x3 4]) s fun s' =>
      ((s'.gpr .x3 = (if up then s.gpr .x3+BitVec.ofNat 64 (16/len) else s.gpr .x3-4) ∧
        s'.mem = s.mem) ∧ Keep [.x3] s s') ∧ s'.v = s.v := by
  cases up
  · exact moveZ_ok 4 (by decide) false s
  · exact moveZ_ok _ (by rcases hlen with rfl | rfl <;> decide) true s

theorem packedZetas_ok {tab : Nat → Nat} {zt : Zq → Zq} (hzt : TabZ tab zt)
    (len : Nat) (hlen : len = 1 ∨ len = 2) (up : Bool) {p : Addr} {k : Nat} {s : State}
    (hb : up = false → 4/len ≤ k) (hbound : baseZ len up k+4 ≤ 256)
    (h3 : s.gpr .x3 = coeffAddr p k) (ht : Tab tab s.mem p 256)
    (hp : pR p ∈ s.rd++s.wr) (hc : VConsts s) :
    WP isa (.block (packedZetas len up)) s fun s' =>
      Zetas (s'.v .v18) (fun e => zt (Spec.MlDsa.zetas (if up then k+e/len else k-e/len))) ∧
      VConsts s' ∧ s'.gpr .x3 = coeffAddr p (if up then k+4/len else k-4/len) ∧
      s'.mem = s.mem ∧ Keep [.x3] s s' ∧ (∀ v, v ≠ .v18 → s'.v v = s.v v) := by
  unfold packedZetas
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (zetaPre_ok len hlen up hb h3) fun s₁ ⟨⟨⟨h31,hm1⟩,k1⟩,hv1⟩ => ?_
  simp only [List.cons_append,List.nil_append]
  refine wp_ldrq (by decide) (by rw [h31,BitVec.add_zero])
    (by rw [k1.rd,k1.wr]; exact ⟨_,hp,vector_contains _ hbound⟩) fun s₂ h2 => ?_
  have c2 : VConsts s₂ :=
    (⟨by rw [hv1]; exact hc.q,by rw [hv1]; exact hc.qi⟩ : VConsts s₁).chg h2.chg
  have z2 : Zetas (s₂.v .v18) (fun e => zt (Spec.MlDsa.zetas (baseZ len up k+e))) := by
    rw [h2.v,hm1]; exact table_vec hzt ht hbound
  rw [WP.block_append_iff]
  refine WP.mono (zetaPerms_ok len hlen up z2) fun s₃ ⟨h3v,z3⟩ => ?_
  refine WP.mono (zetaPost_ok len hlen up s₃) fun s₄ ⟨⟨⟨h34,hm4⟩,k4⟩,hv4⟩ =>
    ⟨?_,⟨by rw [hv4]; exact (c2.chg h3v).q,by rw [hv4]; exact (c2.chg h3v).qi⟩,?_,
      by rw [hm4,h3v.mem,h2.mem,hm1],(((k1.trans h2.keep).trans h3v.keep).trans k4).mono,
      by intro v hv; rw [hv4,h3v.get v (by simp [hv]),h2.get v hv,hv1]⟩
  · rw [hv4]
    exact z3.congr fun e he => by
      have hi : baseZ len up k+(if up then e/len else 4/len-1-e/len) =
          if up then k+e/len else k-e/len := by
        rcases hlen with rfl | rfl <;> cases up <;>
          simp only [baseZ,Bool.false_eq_true,ite_true,ite_false,Nat.div_one,Nat.reduceDiv,Nat.reduceSub] at * <;>
          have hkk := hb (by trivial) <;> omega_arith
      change (zt (Spec.MlDsa.zetas (baseZ len up k+(if up then e/len else 4/len-1-e/len)))).val*2^32%q = _
      rw [hi]
  · rw [h34,h3v.gpr,h2.gpr,h31]
    rcases hlen with rfl | rfl <;> cases up
    · simp only [baseZ,Bool.false_eq_true,ite_false,Nat.div_one,Nat.reduceDiv,Nat.reduceSub]
      rw [show (4 : BitVec 64) = BitVec.ofNat 64 (4*1) from rfl,coeffAddr_sub _ _ _ (by have := hb rfl; omega_arith)]
      exact congrArg (coeffAddr p) (by omega_arith)
    · simp only [baseZ,ite_true,Nat.div_one,Nat.reduceDiv]
      exact coeffAddr_add p k 4
    · simp only [baseZ,Bool.false_eq_true,ite_false,Nat.reduceDiv,Nat.reduceSub]
      rw [show (4 : BitVec 64) = BitVec.ofNat 64 (4*1) from rfl,coeffAddr_sub _ _ _ (by have := hb rfl; omega_arith)]
      exact congrArg (coeffAddr p) (by omega_arith)
    · simp only [baseZ,ite_true,Nat.reduceDiv]
      exact coeffAddr_add p k 2

end VG.Proof.MlDsa.AArch64.Arith.Neon

end

end

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.AArch64.Arith (Tab)
open VG.Proof.MlKem.AArch64 (Keep wp_ldrq wp_strq VChg)
open VG.Spec.MlDsa (Poly Zq zetas)
open VG.Proof.MlDsa (PolyIs)

/-- Advance to the next eight coefficients after a packed butterfly batch. -/
theorem packedEnd_ok (s : State) :
    WP isa (.block [.addImm .x .x2 .x2 32,.subImm .x .x5 .x5 1]) s fun s' =>
      ((s'.gpr .x2 = s.gpr .x2+32 ∧ s'.gpr .x5 = s.gpr .x5-1 ∧ s'.mem = s.mem) ∧
        Keep [.x2,.x5] s s') ∧ s'.v = s.v := by
  apply VG.Proof.MlKem.AArch64.WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  arun
  exact ⟨rfl,rfl⟩

section
variable {bf : List Instr} {op : Zq → Zq → Zq → Zq × Zq} {zt : Zq → Zq}
  (hbf : VBflyOk bf op zt) {blk : Poly → Nat → Nat → Nat → Nat → Poly} (hblk : BlkOk blk op)
include hbf hblk

theorem packedStep_ok {fP zP : Addr} {len u k : Nat} (hlen : len = 1 ∨ len = 2)
    (hu : u < 32) {F : Poly} (zi : Nat → Nat) (up : Bool)
    (hzi : ∀ e < 4, zi ((4/len)*u+e/len) = if up then k+e/len else k-e/len)
    {tab : Nat → Nat} (hzt : TabZ tab zt) (hb : up = false → 4/len ≤ k)
    (hbound : baseZ len up k+4 ≤ 256) {s : State}
    (hc : VConsts s) (hx : s.gpr .x2 = coeffAddr fP (8*u))
    (h3 : s.gpr .x3 = coeffAddr zP k)
    (hP : PolyIs s.mem fP (layF blk F len zi ((4/len)*u)))
    (ht : Tab tab s.mem zP 256) (hw : pR fP ∈ s.wr) (hzp : pR zP ∈ s.rd++s.wr) :
    WP isa (.block (packedBody bf len up)) s fun s' =>
      PolyIs s'.mem fP (layF blk F len zi ((4/len)*(u+1))) ∧
      s'.gpr .x2 = coeffAddr fP (8*(u+1)) ∧
      s'.gpr .x3 = coeffAddr zP (if up then k+4/len else k-4/len) ∧
      s'.gpr .x5 = s.gpr .x5-1 ∧ Keep [.x2,.x3,.x5] s s' ∧ BInv fP s s' := by
  let G := layF blk F len zi ((4/len)*u)
  have j0 : 8*u+4 ≤ 256 := by omega_using [hu]
  have j1 : 8*u+4+4 ≤ 256 := by omega_using [hu]
  have a1 : coeffAddr fP (8*u)+16 = coeffAddr fP (8*u+4) := coeffAddr_add _ _ 4
  have r0 : InRegions (s.rd++s.wr) (coeffAddr fP (8*u)) 16 :=
    ⟨_,List.mem_append_right _ hw,vector_contains _ j0⟩
  have r1 : InRegions (s.rd++s.wr) (coeffAddr fP (8*u+4)) 16 :=
    ⟨_,List.mem_append_right _ hw,vector_contains _ j1⟩
  unfold packedBody
  simp only [List.cons_append,List.nil_append,List.append_assoc]
  refine wp_ldrq (by decide) (by rw [hx,BitVec.add_zero]) r0 fun s₁ h₁ =>
    wp_ldrq (a := coeffAddr fP (8*u+4)) (by decide) (by rw [h₁.gpr,hx]; exact a1)
      (by rw [h₁.rd,h₁.wr]; exact r1) fun s₂ h₂ => ?_
  rw [WP.block_append_iff]
  have hzcode : VG.Impl.MlDsa.AArch64.Arith.Neon.zetas len up = packedZetas len up := by
    rcases hlen with rfl | rfl <;> rfl
  rw [hzcode]
  refine WP.mono (packedZetas_ok (p := zP) (k := k) hzt len hlen up hb hbound
    (by rw [h₂.gpr,h₁.gpr]; exact h3) (by rw [h₂.mem,h₁.mem]; exact ht)
    (by rw [h₂.rd,h₂.wr,h₁.rd,h₁.wr]; exact hzp) (hc.chg (h₁.chg.trans h₂.chg)))
    fun s₃ ⟨lz,c₃,h33,hm₃,k₃,hv₃⟩ => ?_
  rw [WP.block_append_iff]
  have l6 : Coeffs (s₃.v .v6) (fun e => G[8*u+e]!) := by
    rw [hv₃ .v6 (by decide),h₂.get .v6,h₁.v]; exact coeffs_load hP j0
  have l7 : Coeffs (s₃.v .v7) (fun e => G[8*u+(4+e)]!) := by
    rw [hv₃ .v7 (by decide),h₂.v,h₁.mem]
    exact (coeffs_load hP j1).congr fun e _ => by dsimp only; rw [Nat.add_assoc]
  refine WP.mono (gather_ok len hlen l6 l7) fun s₄ ⟨h₄,la,lb⟩ => ?_
  rw [WP.block_append_iff]
  have z₄ : Zetas (s₄.v .v18) (fun e => zt (zetas (zi ((4/len)*u+e/len)))) := by
    rw [h₄.get .v18]
    exact lz.congr fun e he => by dsimp only; rw [hzi e he]
  refine WP.mono (hbf s₄ (c₃.chg h₄) _ _ _ la lb z₄) fun s₅ ⟨va,vb,h₅⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (scatter_ok len hlen va vb) fun s₆ ⟨h₆,v6,v7⟩ => ?_
  have k06 : Keep [.x3] s s₆ := (((((h₁.keep.trans h₂.keep).trans k₃).trans h₄.keep).trans h₅.keep).trans h₆.keep).mono
  have g6 : s₆.gpr .x2 = coeffAddr fP (8*u) := by rw [k06.get .x2,hx]
  have m6 : s₆.mem = s.mem := by rw [h₆.mem,h₅.mem,h₄.mem,hm₃,h₂.mem,h₁.mem]
  refine wp_strq (by decide) (by rw [g6,BitVec.add_zero])
    (by rw [k06.wr]; exact ⟨_,hw,vector_contains _ j0⟩) fun s₇ h₇ =>
    wp_strq (a := coeffAddr fP (8*u+4)) (by decide) (by rw [h₇.gpr,g6]; exact a1)
      (by rw [h₇.wr,k06.wr]; exact ⟨_,hw,vector_contains _ j1⟩) fun s₈ h₈ => ?_
  have mem₈ : s₈.mem = (s.mem.write (coeffAddr fP (8*u)) 16 (s₆.v .v6)).write
      (coeffAddr fP (8*u+4)) 16 (s₆.v .v7) := by rw [h₈.mem,h₇.mem,h₇.v,m6]
  have c₈ : VConsts s₈ := by
    have c₆ := ((c₃.chg h₄).chg h₅).chg h₆
    exact ⟨by rw [h₈.v,h₇.v]; exact c₆.q,by rw [h₈.v,h₇.v]; exact c₆.qi⟩
  refine WP.mono (packedEnd_ok s₈) fun s₉ ⟨⟨⟨hx9,hcnt9,hm9⟩,k₉⟩,hv9⟩ =>
    ⟨?_,?_,?_,?_,(((k06.trans h₇.keep).trans h₈.keep).trans k₉).mono,
      ⟨(((k06.trans h₇.keep).trans h₈.keep).trans k₉).mono,?_,
        ⟨by rw [hv9]; exact c₈.q,by rw [hv9]; exact c₈.qi⟩⟩⟩
  · rw [hm9,mem₈]
    refine polyIs_write2 hP j0 j1 (by omega_using []) v6 v7 fun j hj => ?_
    rw [packed_batch_get hblk F zi len hlen hu hj]
    by_cases c1 : 8*u ≤ j ∧ j < 8*u+4
    · rw [ite_eq_left (by omega_using [c1]),ite_eq_left c1]
      simp only [G,Nat.add_assoc]
    · rw [ite_eq_right c1]
      by_cases c2 : 8*u+4 ≤ j ∧ j < 8*u+8
      · rw [ite_eq_left (by omega_using [c2]),ite_eq_left (by omega_using [c2]),show 4+(j-(8*u+4)) = j-8*u by omega_using [c2]]
        simp only [G,Nat.add_assoc]
      · rw [ite_eq_right (by omega_using [c1, c2]),ite_eq_right (by omega_using [c2])]
  · rw [hx9,h₈.gpr,h₇.gpr,g6,show (32 : BitVec 64) = BitVec.ofNat 64 (4*8) from rfl,
      coeffAddr_add,show 8*u+8 = 8*(u+1) by omega_using []]
  · rw [k₉.get .x3,h₈.gpr,h₇.gpr,h₆.gpr,h₅.gpr,h₄.gpr,h33]
  · rw [hcnt9,h₈.gpr,h₇.gpr,k06.get .x5]
  · rw [hm9,mem₈]; exact frame_write2 (Frame.refl _ _) j0 j1 _ _
end
end VG.Proof.MlDsa.AArch64.Arith.Neon

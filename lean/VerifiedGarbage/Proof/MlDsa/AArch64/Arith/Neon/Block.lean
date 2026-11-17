module

public import VerifiedGarbage.Proof.MlDsa.Arith.VectorNtt
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Step
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Table
public import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Neon.Ntt
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Bfly
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
public import VerifiedGarbage.Proof.MlDsa.Arith.Ntt

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

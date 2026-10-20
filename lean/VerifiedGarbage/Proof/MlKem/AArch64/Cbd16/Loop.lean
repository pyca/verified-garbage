module
public import VerifiedGarbage.Impl.MlKem.AArch64.Cbd16
public import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Base
public import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Lanes
public import VerifiedGarbage.Proof.MlKem.AArch64.Common
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec

import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Input
import VerifiedGarbage.Proof.Rc4.AArch64.Rows
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Stores
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Prepare
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # Eight sixteen-byte CBD2 iterations -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Cbd16
open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Proof.Rc4.AArch64
open VG.Impl.MlKem.AArch64.Cbd16 (body prepare half code constant)

structure Consts (s : State) : Prop where
  q : Lanes (s.v .v16) fun _ => 3329
  c : Lanes (s.v .v17) fun _ => 3327
  zero : s.v .v22 = 0
  c18 : s.v .v18 = broadcast 0x55
  c19 : s.v .v19 = broadcast 0x33
  c20 : s.v .v20 = broadcast 0x22
  c21 : s.v .v21 = broadcast 15

structure Inv (s0 : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  x0 : s.gpr .x0 = Cbd2.bP s0 + BitVec.ofNat 64 (16*k)
  x1 : s.gpr .x1 = coeffAddr (Cbd2.fP s0) (32*k)
  count : (s.gpr .x10).toNat = 8-k
  consts : Consts s
  out : CoeffsUpTo s.mem (Cbd2.fP s0) (32*k) (Cbd2.G s0) (fun i => coeffAt s0.mem (Cbd2.fP s0) i)
  frame : Frame [polyRegion (Cbd2.fP s0)] s0.mem s.mem

theorem read_input {s0 s : State} (hp : Cbd2.Pre s0) {k : Nat} (hk : k < 8)
    (h : Inv s0 k s) {e : Nat} (he : e < 16) :
    vbyte (s.mem.read (s.gpr .x0) 16) e = BitVec.ofNat 8 (Cbd2.byte s0 (16*k+e)) := by
  rw [VG.Proof.Rc4.AArch64.vbyte_read _ _ he,h.x0,ptr_add]
  apply BitVec.eq_of_toNat_eq
  rw [hp.byte_eq h.frame (by omega),BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (byte_lt _)]


theorem step {s0 : State} (hp : Cbd2.Pre s0) {k : Nat} (hk : k < 8)
    {s : State} (h : Inv s0 k s) : WP isa (.block body) s fun t =>
      Inv s0 (k+1) t ∧ ((t.gpr .x10).toNat ≠ 0 ↔ k+1 ≠ 8) := by
  unfold body
  simp only [List.cons_append,List.nil_append,List.append_assoc]
  refine wp_ldrq (a := s.gpr .x0) (by decide) (by simp) ?_ fun s1 h1 => ?_
  · rw [h.rd,h.wr,hp.rd,hp.wr,h.x0]
    exact in_rd (in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide)))
  rw [WP.block_append_iff]
  refine WP.mono (prepare_ok s1
    (by rw [h1.get .v18]; exact h.consts.c18)
    (by rw [h1.get .v19]; exact h.consts.c19)
    (by rw [h1.get .v20]; exact h.consts.c20)
    (by rw [h1.get .v21]; exact h.consts.c21)) ?_
  intro s2 ⟨v2,v3,m2,g2,rd2,wr2,sp2,hv2⟩
  have mem2 : s2.mem = s.mem := m2.trans h1.mem
  have gpr2 : s2.gpr = s.gpr := g2.trans h1.gpr
  have vl : ∀ r, r ≠ .v0 → r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → s2.v r = s.v r := by
    intro r h0 h1' h2 h3; rw [hv2 r h0 h1' h2 h3,h1.get r h0]
  have cs2 : Consts s2 :=
    ⟨by rw [vl .v16 (by decide) (by decide) (by decide) (by decide)]; exact h.consts.q,
     by rw [vl .v17 (by decide) (by decide) (by decide) (by decide)]; exact h.consts.c,
     by rw [vl .v22 (by decide) (by decide) (by decide) (by decide)]; exact h.consts.zero,
     by rw [vl .v18 (by decide) (by decide) (by decide) (by decide)]; exact h.consts.c18,
     by rw [vl .v19 (by decide) (by decide) (by decide) (by decide)]; exact h.consts.c19,
     by rw [vl .v20 (by decide) (by decide) (by decide) (by decide)]; exact h.consts.c20,
     by rw [vl .v21 (by decide) (by decide) (by decide) (by decide)]; exact h.consts.c21⟩
  have hs2 : Stores s2 (Cbd2.fP s0) (Cbd2.G s0) (32*k) s2 := by
    refine ⟨Keep.refl [] _,rfl,?_,Frame.refl _ _,cs2.q,cs2.c,cs2.zero⟩
    intro i hi
    by_cases hh : i < 32*k
    · rw [mem2,h.out i hi,ite_eq_left hh,ite_eq_left hh]
    · rw [ite_eq_right hh]
  let nib (e : Nat) : Nat := (nibble (BitVec.ofNat 8 (Cbd2.byte s0 (16*k+e/2))) (e%2 != 0)).toNat
  have nb : ∀ e < 32, nib e ≤ 4 := by
    intro e _; exact (nibble_values _ (byte_lt _) _).1
  have ng : ∀ e < 32, (Cbd2.G s0 (32*k+e)).toNat = (nib e+3327)%3329 := by
    intro e he; rw [G_nibble _ (by omega)]
    simp only [show (32*k+e)/2 = 16*k+e/2 by omega,
      show (32*k+e)%2 = e%2 by omega,nib]
  have nl : ∀ e < 16,
      (vbyte (VPermOp.eval .zip1 .b16 (s2.v .v2) (s2.v .v3)) e).toNat = nib e ∧
      (vbyte (VPermOp.eval .zip2 .b16 (s2.v .v2) (s2.v .v3)) e).toNat = nib (16+e) := by
    intro e he
    rw [v2,v3,h1.v,(byte_zip_nibbles _ he).1,(byte_zip_nibbles _ he).2,
      read_input hp hk h (by omega),read_input hp hk h (by omega)]
    simp only [nib,show (16+e)/2 = 8+e/2 by omega,
      show (16+e)%2 = e%2 by omega,and_self]
  refine half_ok hs2 (by omega) (by decide)
    (by rw [gpr2,h.x1,ptr_zero])
    (by rw [wr2,h1.wr,h.wr,hp.wr]) (fun e he => (nl e he).1)
    (fun e he => nb e (by omega)) (fun e he => ng e (by omega)) fun s3 hs3 hv3 => ?_
  refine half_ok hs3 (by omega) (by decide) ?_ ?_
    (fun e he => by rw [hv3 .v2 (by decide) (by decide) (by decide) (by decide),
      hv3 .v3 (by decide) (by decide) (by decide) (by decide)]; exact (nl e he).2)
    (fun e he => nb (16+e) (by omega)) ?_ fun s4 hs4 hv4 => ?_
  · rw [hs3.gpr,gpr2,h.x1]; exact coeffAddr_off _ _ 16
  · rw [hs3.keep.wr,wr2,h1.wr,h.wr,hp.wr]
  · intro e he; simpa only [Nat.add_assoc] using ng (16+e) (by omega)
  have gp4 : s4.gpr = s.gpr := hs4.gpr.trans gpr2
  have scalar : WP isa (.block [.addImm .x .x0 .x0 16,.addImm .x .x1 .x1 128,
      .subImm .x .x10 .x10 1]) s4 fun t =>
      Only [.x0,.x1,.x10] s4 t ∧
      t.gpr .x0 = s4.gpr .x0 + 16 ∧ t.gpr .x1 = s4.gpr .x1 + 128 ∧
      (t.gpr .x10).toNat = 8-(k+1) := by
    refine wp_addImm (by decide) fun s5 h5 e5 => wp_addImm (by decide) fun s6 h6 e6 =>
      wp_subImm (by decide) fun s7 h7 e7 => wp_nil ?_
    refine ⟨((h5.trans h6).trans h7).mono (by decide),?_,?_,?_⟩
    · rw [h7.get .x0,h6.get .x0,e5]; rfl
    · rw [h7.get .x1,e6,h5.get .x1]; rfl
    · rw [e7,toNat_sub_n (by rw [h6.get .x10,h5.get .x10,gp4,h.count]; simp; omega),
        h6.get .x10,h5.get .x10,gp4,h.count]
      simp; omega
  refine WP.mono (WP.keepV (by decide) scalar) ?_
  intro s7 ⟨⟨kept,xx0,xx1,cnt⟩,vv⟩
  have mm : s7.mem = s4.mem := kept.mem
  have vconst (r : VReg) (h4 : r ≠ .v4) (h5' : r ≠ .v5) (h6' : r ≠ .v6) (h7' : r ≠ .v7) :
      s7.v r = s2.v r := by
    rw [vv,hv4 r h4 h5' h6' h7',hv3 r h4 h5' h6' h7']
  refine ⟨⟨?_,?_,?_,?_,?_,cnt,?_,?_,?_⟩,by rw [cnt]; omega⟩
  · rw [kept.rd,hs4.keep.rd,rd2,h1.rd,h.rd]
  · rw [kept.wr,hs4.keep.wr,wr2,h1.wr,h.wr]
  · rw [kept.sp,hs4.keep.sp,sp2,h1.sp,h.sp]
  · rw [xx0,gp4,h.x0,show (16:BitVec 64) = BitVec.ofNat 64 16 from rfl,ptr_add]
    congr 2
  · rw [xx1,gp4,h.x1,coeffAddr,show (128:BitVec 64) = BitVec.ofNat 64 128 from rfl,ptr_add,coeffAddr]
    congr 2
  · exact ⟨by rw [vconst .v16 (by decide) (by decide) (by decide) (by decide)]; exact cs2.q,
      by rw [vconst .v17 (by decide) (by decide) (by decide) (by decide)]; exact cs2.c,
      by rw [vconst .v22 (by decide) (by decide) (by decide) (by decide)]; exact cs2.zero,
      by rw [vconst .v18 (by decide) (by decide) (by decide) (by decide)]; exact cs2.c18,
      by rw [vconst .v19 (by decide) (by decide) (by decide) (by decide)]; exact cs2.c19,
      by rw [vconst .v20 (by decide) (by decide) (by decide) (by decide)]; exact cs2.c20,
      by rw [vconst .v21 (by decide) (by decide) (by decide) (by decide)]; exact cs2.c21⟩
  · intro i hi; rw [mm,hs4.out i hi,mem2]
    dsimp only
    rw [h.out i hi]
    by_cases hh : i < 32*k+16+16
    · rw [ite_eq_left hh,ite_eq_left (by omega)]
    · rw [ite_eq_right hh,ite_eq_right (by omega),ite_eq_right (by omega)]
  · rw [mm]; exact h.frame.trans (by simpa only [mem2] using hs4.frame)


theorem init (s : State) : WP isa (.block (constant .v16 .s4 3329 ++ constant .v17 .s4 3327 ++
    constant .v18 .b16 0x55 ++ constant .v19 .b16 0x33 ++ constant .v20 .b16 0x22 ++
    constant .v21 .b16 15 ++ ([.vop (.movi0 .v22),.movz .x .x10 8 0] : List Instr))) s (Inv s 0) := by
  unfold constant
  rrun [List.append_assoc,List.cons_append,List.nil_append,
    RegUpd.sp_write,RegUpd.sp_setV]
  refine ⟨rfl,rfl,rfl,?_,?_,rfl,?_,?_,?_⟩
  · change s.gpr .x0 = Cbd2.bP s + BitVec.ofNat 64 (16*0)
    simp [Cbd2.bP]
  · change s.gpr .x1 = coeffAddr (Cbd2.fP s) (32*0)
    simp [coeffAddr,Cbd2.fP]
  · refine ⟨?_,?_,rfl,rfl,rfl,rfl,rfl⟩
    · intro e he
      change (vword (ofVWords 3329 3329 3329 3329) e).toNat = 3329
      rw [vword_dup_s4 _ he]
      rfl
    · intro e he
      change (vword (ofVWords 3327 3327 3327 3327) e).toNat = 3327
      rw [vword_dup_s4 _ he]
      rfl
  · exact CoeffsUpTo.zero _
  · exact Frame.refl _ _

theorem loop_ok {s0 : State} (hp : Cbd2.Pre s0) : WP isa code s0 (Inv s0 8) := by
  apply WP.seq
  refine WP.mono (init s0) ?_
  intro s hs
  exact count_loop (by decide) (Inv s0) (fun k hk t ht => step hp hk ht) hs

end VG.Proof.MlKem.AArch64.Cbd16

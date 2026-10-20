module

import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.EncMath
public import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.EncBase
public import VerifiedGarbage.Impl.MlKem.AArch64.Codec16
public import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.Lanes
public import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.Bytes
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.Rc4.AArch64.Vec

/-! # ML-KEM encoding eight coefficients at a time -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Codec16
open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.Codec16 (encBody encMath enc maskVec)
open VG.Proof.Rc4.AArch64

structure EncInv (s0 : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s0.rd
  wr : s.wr = s0.wr
  sp : s.sp = s0.sp
  x0 : s.gpr .x0 = coeffAddr (Encode12.fP s0) (8*k)
  x1 : s.gpr .x1 = Encode12.oP s0 + BitVec.ofNat 64 (12*k)
  count : (s.gpr .x11).toNat = 32-k
  mask : s.v .v16 = encMask
  out : BytesUpTo s.mem (Encode12.oP s0) 384 (12*k) (Encode12.L s0)
    (fun j => s0.mem (Encode12.oP s0+BitVec.ofNat 64 j))
  frame : Frame [Encode12.oR s0] s0.mem s.mem

theorem low_byte (v : BitVec 128) {j : Nat} (hj : j<8) :
    (v.extractLsb' 0 64).extractLsb' (8*j) 8 = vbyte v j := by
  rw [BitVec.extractLsb'_extractLsb'_of_le (by omega)]
  rfl

theorem high_byte (v : BitVec 128) {j : Nat} (hj : j<4) :
    ((v.extractLsb' 64 64).setWidth 32).extractLsb' (8*j) 8 = vbyte v (8+j) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vbyte,BitVec.getLsbD_extractLsb',BitVec.getLsbD_setWidth,hi,decide_true,
    Bool.true_and,show 8*j+i<32 by omega,show 8*j+i<64 by omega]
  exact congrArg _ (by omega)

theorem enc_step {s0 : State} (hp : Encode12.Pre s0) {k : Nat} (hk : k<32)
    {s : State} (h : EncInv s0 k s) : WP isa (.block encBody) s fun t =>
      EncInv s0 (k+1) t ∧ ((t.gpr .x11).toNat ≠ 0 ↔ k+1 ≠ 32) := by
  have hin : ∀ j, j+4≤256 → InRegions (s.rd++s.wr) (coeffAddr (Encode12.fP s0) j) 16 := by
    intro j hj; rw [h.rd,h.wr,hp.rd,hp.wr]
    exact in_rd (in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide)))
  unfold encBody
  simp only [List.cons_append,List.nil_append]
  refine wp_ldrq (a := coeffAddr (Encode12.fP s0) (8*k)) (by decide)
    (by rw [h.x0,ptr_zero]) (hin _ (by omega)) fun s1 h1 => ?_
  refine wp_ldrq (a := coeffAddr (Encode12.fP s0) (8*k+4)) (by decide)
    (by rw [h1.gpr,h.x0]; exact coeffAddr_step _ _)
    (by rw [h1.rd,h1.wr]; exact hin _ (by omega)) fun s2 h2 => ?_
  rw [WP.block_append_iff]
  refine WP.mono (math_ok s2 (by rw [h2.get .v16,h1.get .v16]; exact h.mask)) ?_
  intro s3 ⟨x9,x10,m3,rd3,wr3,sp3,g3,v3⟩
  let v := tbl (packed (s2.v .v0) (s2.v .v1)) encMask
  have bytes : ∀ j<12, vbyte v j = Encode12.L s0 (12*k+j) := by
    intro j hj
    apply enc_spec (Encode12.P s0) hk (j:=j) _ _ hj
    · rw [h2.get .v0,h1.v]
      exact lanes_coeffs fun e he => hp.coeff h.frame (by omega)
    · rw [h2.v,h1.mem]
      exact (lanes_coeffs (j:=8*k+4) (fun e he => hp.coeff h.frame (by omega))).congr
        (fun e _ => by rw [Nat.add_assoc])
  have g30 : s3.gpr .x0 = s.gpr .x0 := by rw [g3 .x0 (by decide) (by decide),h2.gpr,h1.gpr]
  have g31 : s3.gpr .x1 = s.gpr .x1 := by rw [g3 .x1 (by decide) (by decide),h2.gpr,h1.gpr]
  have g311 : s3.gpr .x11 = s.gpr .x11 := by rw [g3 .x11 (by decide) (by decide),h2.gpr,h1.gpr]
  have mem3 : s3.mem = s.mem := m3.trans (h2.mem.trans h1.mem)
  have wrs3 : s3.wr = s.wr := wr3.trans (h2.wr.trans h1.wr)
  have scalar : WP isa (.block [.str .x .x9 .x1 0,.str .w .x10 .x1 8,
      .addImm .x .x0 .x0 32,.addImm .x .x1 .x1 12,.subImm .x .x11 .x11 1]) s3 fun t =>
      t.rd=s3.rd ∧ t.wr=s3.wr ∧ t.sp=s3.sp ∧
      t.gpr .x0=s3.gpr .x0+32 ∧ t.gpr .x1=s3.gpr .x1+12 ∧
      (t.gpr .x11).toNat=32-(k+1) ∧
      t.mem=(s3.mem.write (Encode12.oP s0+BitVec.ofNat 64 (12*k)) 8 (v.extractLsb' 0 64)).write
        (Encode12.oP s0+BitVec.ofNat 64 (12*k+8)) 4 ((v.extractLsb' 64 64).setWidth 32) := by
    refine wp_strx (a:=Encode12.oP s0+BitVec.ofNat 64 (12*k)) (by decide)
      (by rw [g31,h.x1,ptr_zero]) ?_ fun s4 h4 => ?_
    · rw [wrs3,h.wr,hp.wr]
      exact in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide))
    refine wp_strw (a:=Encode12.oP s0+BitVec.ofNat 64 (12*k+8)) (by decide)
      (by rw [h4.gpr,g31,h.x1,ptr_add]) ?_ fun s5 h5 => ?_
    · rw [h4.wr,wrs3,h.wr,hp.wr]
      exact in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide))
    refine wp_addImm (by decide) fun s6 h6 e6 => wp_addImm (by decide) fun s7 h7 e7 =>
      wp_subImm (by decide) fun s8 h8 e8 => wp_nil ?_
    have keep := (((h4.keep.trans h5.keep).trans h6.keep).trans h7.keep).trans h8.keep
    refine ⟨keep.rd,keep.wr,keep.sp,?_,?_,?_,?_⟩
    · rw [h8.get .x0,h7.get .x0,e6,h5.gpr,h4.gpr]; rfl
    · rw [h8.get .x1,e7,h6.get .x1,h5.gpr,h4.gpr]; rfl
    · have c : (s7.gpr .x11).toNat=32-k := by
        rw [h7.get .x11,h6.get .x11,h5.gpr,h4.gpr,g311,h.count]
      rw [e8,toNat_sub_n (by rw [c]; simp; omega),c]; simp; omega
    · rw [h8.mem,h7.mem,h6.mem,h5.mem,h4.mem,h4.gpr,x9,x10]
      rfl
  refine WP.mono (WP.keepV (by decide) scalar) ?_
  intro t ⟨⟨rd,wr,sp,p0,p1,ct,mt⟩,vt⟩
  refine ⟨⟨rd.trans (rd3.trans (h2.rd.trans (h1.rd.trans h.rd))),
    wr.trans (wrs3.trans h.wr),sp.trans (sp3.trans (h2.sp.trans (h1.sp.trans h.sp))),?_,?_,ct,?_,?_,?_⟩,
    by rw [ct]; omega⟩
  · rw [p0,g30,h.x0,coeffAddr,show (32:BitVec 64)=BitVec.ofNat 64 32 from rfl,ptr_add,coeffAddr]; congr 2
  · rw [p1,g31,h.x1,show (12:BitVec 64)=BitVec.ofNat 64 12 from rfl,ptr_add]; congr 2
  · rw [vt,v3,h2.get .v16,h1.get .v16,h.mask]
  · rw [mt,mem3,show 12*(k+1)=12*k+8+4 by omega]
    refine bytes_write (bytes_write h.out (by omega) ?_) (by omega) ?_
    · intro j hj; rw [low_byte _ hj]; exact bytes j (by omega)
    · intro j hj; rw [high_byte _ hj]
      simpa only [Nat.add_assoc] using bytes (8+j) (by omega)
  · rw [mt,mem3]
    exact (h.frame.write (n:=8) (List.mem_singleton_self _) _ (contains_off (by omega) (by decide))).write
      (n:=4) (List.mem_singleton_self _) _ (contains_off (by omega) (by decide))


theorem encMask_value : encMask = 0xffffffff0e0d0c0a0908060504020100#128 := by
  apply vbyte_ext
  exact (by decide +kernel : ∀ e<16, vbyte encMask e = vbyte 0xffffffff0e0d0c0a0908060504020100#128 e)

theorem enc_init (s : State) : WP isa (.block (maskVec .v16 [0,1,2,4,5,6,8,9,10,12,13,14] ++
    ([.movz .x .x11 32 0] : List Instr))) s (EncInv s 0) := by
  dsimp [maskVec,VG.Impl.MlKem.AArch64.movImm]
  rrun [RegUpd.sp_write,RegUpd.sp_setV]
  refine ⟨rfl,rfl,rfl,?_,?_,rfl,?_,?_,?_⟩
  · change s.gpr .x0 = coeffAddr (Encode12.fP s) (8*0)
    simp [coeffAddr,Encode12.fP]
  · change s.gpr .x1 = Encode12.oP s + BitVec.ofNat 64 (12*0)
    simp [Encode12.oP]
  · rw [encMask_value]
    rfl
  · exact BytesUpTo.zero _
  · exact Frame.refl _ _

theorem enc_loop_ok {s0 : State} (hp : Encode12.Pre s0) : WP isa enc s0 (EncInv s0 32) := by
  apply WP.seq
  refine WP.mono (enc_init s0) ?_
  intro s hs
  exact count_loop (by decide) (EncInv s0) (fun k hk t ht => enc_step hp hk ht) hs

end VG.Proof.MlKem.AArch64.Codec16

module
public import VerifiedGarbage.Impl.MlKem.AArch64.Codec16
public import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecBase
public import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecLanes
public import VerifiedGarbage.Proof.MlKem.AArch64.Common

import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecInput
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # Eight-coefficient decoding loop -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Codec16
open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.Codec16 (decBody decMath dec maskVec)
open VG.Proof.Rc4.AArch64

structure DecInv (s0 : State) (k : Nat) (s : State) : Prop where
  rd : s.rd=s0.rd
  wr : s.wr=s0.wr
  sp : s.sp=s0.sp
  x0 : s.gpr .x0=Decode12.bP s0+BitVec.ofNat 64 (12*k)
  x1 : s.gpr .x1=coeffAddr (Decode12.fP s0) (8*k)
  count : (s.gpr .x11).toNat=32-k
  mask : s.v .v16=decMask
  bits : s.v .v17=mask12
  q : s.v .v18=qvec
  out : CoeffsUpTo s.mem (Decode12.fP s0) (8*k) (Decode12.G s0)
    (fun i => coeffAt s0.mem (Decode12.fP s0) i)
  frame : Frame [polyRegion (Decode12.fP s0)] s0.mem s.mem

theorem dec_step {s0 : State} (hp : Decode12.Pre s0) {k : Nat} (hk : k<32)
    {s : State} (h : DecInv s0 k s) : WP isa (.block decBody) s fun t =>
      DecInv s0 (k+1) t ∧ ((t.gpr .x11).toNat ≠ 0 ↔ k+1 ≠ 32) := by
  have load : WP isa (.block [.ldr .x .x9 .x0 0,.ldr .w .x10 .x0 8]) s fun t =>
      Only [.x9,.x10] s t ∧ t.gpr .x9=s.mem.readW (s.gpr .x0) 64 ∧
      t.gpr .x10=(s.mem.readW (s.gpr .x0+8) 32).setWidth 64 := by
    refine wp_ldrx (a:=s.gpr .x0) (by decide) (by simp) ?_ fun s1 h1 e1 => ?_
    · rw [h.rd,h.wr,hp.rd,hp.wr,h.x0]
      exact in_rd (in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide)))
    refine wp_ldrw (a:=s.gpr .x0+8) (by decide) (by rw [h1.get .x0]; rfl) ?_ fun s2 h2 e2 => wp_nil ?_
    · rw [h1.rd,h1.wr,h.rd,h.wr,hp.rd,hp.wr,h.x0,
        show (8:BitVec 64)=BitVec.ofNat 64 8 from rfl,ptr_add]
      exact in_rd (in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide)))
    refine ⟨h1.trans h2,by rw [h2.get .x9,e1],?_⟩
    rw [e2,h1.mem]
  unfold decBody
  rw [List.append_assoc]
  refine wp_scalar (by decide) load ?_
  intro s2 ⟨hl,x9,x10⟩ vl
  rw [WP.block_append_iff]
  refine WP.mono (dec_math_ok s2 (by rw [vl,h.mask]) (by rw [vl,h.bits]) (by rw [vl,h.q])) ?_
  intro s3 ⟨v0,v1,g3,m3,rd3,wr3,sp3,hv3⟩
  let x := ofVDwords (s2.gpr .x9) (s2.gpr .x10)
  have xb : ∀ j<12, (vbyte x j).toNat=Decode12.byte s0 (12*k+j) := by
    intro j hj
    rw [show x=ofVDwords (s.mem.readW (s.gpr .x0) 64)
      ((s.mem.readW (s.gpr .x0+8) 32).setWidth 64) by dsimp only [x]; rw [x9,x10],input_byte _ _ hj,
      h.x0,ptr_add,hp.byte_eq h.frame (by omega)]
  have vals : ∀ e<4, vword (s3.v .v0) e=Decode12.G s0 (8*k+e) ∧
      vword (s3.v .v1) e=Decode12.G s0 (8*k+4+e) := by
    intro e he; rw [v0,v1]; exact decoded_spec s0 hk xb he
  have gp (r : Reg) (hr : r ∉ [.x9,.x10]) : s3.gpr r=s.gpr r := by rw [g3,hl.gpr _ hr]
  have mm3 : s3.mem=s.mem := m3.trans hl.mem
  refine wp_strq (a:=coeffAddr (Decode12.fP s0) (8*k)) (by decide)
    (by rw [gp .x1 (by decide),h.x1,ptr_zero]) ?_ fun s4 h4 => ?_
  · rw [wr3,hl.wr,h.wr,hp.wr]
    exact in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide))
  refine wp_strq (a:=coeffAddr (Decode12.fP s0) (8*k+4)) (by decide)
    (by rw [h4.gpr,gp .x1 (by decide),h.x1]; exact coeffAddr_step _ _) ?_ fun s5 h5 => ?_
  · rw [h4.wr,wr3,hl.wr,h.wr,hp.wr]
    exact in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide))
  have scalar : WP isa (.block [.addImm .x .x0 .x0 12,.addImm .x .x1 .x1 32,.subImm .x .x11 .x11 1]) s5
      fun t => Only [.x0,.x1,.x11] s5 t ∧ t.gpr .x0=s5.gpr .x0+12 ∧
        t.gpr .x1=s5.gpr .x1+32 ∧ (t.gpr .x11).toNat=32-(k+1) := by
    refine wp_addImm (by decide) fun s6 h6 e6 => wp_addImm (by decide) fun s7 h7 e7 =>
      wp_subImm (by decide) fun s8 h8 e8 => wp_nil ?_
    refine ⟨((h6.trans h7).trans h8).mono (by decide),?_,?_,?_⟩
    · rw [h8.get .x0,h7.get .x0,e6]; rfl
    · rw [h8.get .x1,e7,h6.get .x1]; rfl
    · have cnt : (s7.gpr .x11).toNat=32-k := by
        rw [h7.get .x11,h6.get .x11,h5.gpr,h4.gpr,gp .x11 (by decide),h.count]
      rw [e8,toNat_sub_n (by rw [cnt]; simp; omega),cnt]; simp; omega
  refine WP.mono (WP.keepV (by decide) scalar) ?_
  intro t ⟨⟨ht,p0,p1,cnt⟩,vt⟩
  have mt : t.mem=(s.mem.write (coeffAddr (Decode12.fP s0) (8*k)) 16 (s3.v .v0)).write
      (coeffAddr (Decode12.fP s0) (8*k+4)) 16 (s3.v .v1) := by
    rw [ht.mem,h5.mem,h4.mem,h4.v,mm3]
  have keepv (r : VReg) (r0 : r ≠ .v0) (r1 : r ≠ .v1) (r2 : r ≠ .v2)
      (r3 : r ≠ .v3) (r4 : r ≠ .v4) : t.v r=s.v r := by
    rw [vt,h5.v,h4.v,hv3 r r0 r1 r2 r3 r4,vl]
  refine ⟨⟨?_,?_,?_,?_,?_,cnt,?_,?_,?_,?_,?_⟩,by rw [cnt]; omega⟩
  · rw [ht.rd,h5.rd,h4.rd,rd3,hl.rd,h.rd]
  · rw [ht.wr,h5.wr,h4.wr,wr3,hl.wr,h.wr]
  · rw [ht.sp,h5.sp,h4.sp,sp3,hl.sp,h.sp]
  · rw [p0,h5.gpr,h4.gpr,gp .x0 (by decide),h.x0,
      show (12:BitVec 64)=BitVec.ofNat 64 12 from rfl,ptr_add]; congr 2
  · rw [p1,h5.gpr,h4.gpr,gp .x1 (by decide),h.x1,coeffAddr,
      show (32:BitVec 64)=BitVec.ofNat 64 32 from rfl,ptr_add,coeffAddr]; congr 2
  · rw [keepv .v16 (by decide) (by decide) (by decide) (by decide) (by decide),h.mask]
  · rw [keepv .v17 (by decide) (by decide) (by decide) (by decide) (by decide),h.bits]
  · rw [keepv .v18 (by decide) (by decide) (by decide) (by decide) (by decide),h.q]
  · rw [mt,show 8*(k+1)=8*k+4+4 by omega]
    exact (h.out.write16 (by omega) (fun e he => (vals e he).1)).write16 (by omega)
      (fun e he => (vals e he).2)
  · rw [mt]; exact frame16 (frame16 h.frame (by omega) _) (by omega) _


theorem decMask_value : decMask = 0xff0b0a09ff080706ff050403ff020100#128 := by
  apply vbyte_ext
  exact (by decide +kernel : ∀ e<16, vbyte decMask e = vbyte 0xff0b0a09ff080706ff050403ff020100#128 e)

theorem dec_init (s : State) : WP isa (.block (maskVec .v16 [0,1,2,255,3,4,5,255,6,7,8,255,9,10,11,255] ++
    ([.movz .x .x9 4095 0,.vop (.dup .s4 .v17 .x9),.movz .x .x9 3329 0,
      .vop (.dup .s4 .v18 .x9),.movz .x .x11 32 0] : List Instr))) s (DecInv s 0) := by
  dsimp [maskVec,VG.Impl.MlKem.AArch64.movImm]
  rrun [RegUpd.sp_write,RegUpd.sp_setV]
  refine ⟨rfl,rfl,rfl,?_,?_,rfl,?_,rfl,rfl,?_,?_⟩
  · change s.gpr .x0 = Decode12.bP s + BitVec.ofNat 64 (12*0)
    simp [Decode12.bP]
  · change s.gpr .x1 = coeffAddr (Decode12.fP s) (8*0)
    simp [coeffAddr,Decode12.fP]
  · rw [decMask_value]
    rfl
  · exact CoeffsUpTo.zero _
  · exact Frame.refl _ _

theorem dec_loop_ok {s0 : State} (hp : Decode12.Pre s0) : WP isa dec s0 (DecInv s0 32) := by
  apply WP.seq
  refine WP.mono (dec_init s0) ?_
  intro s hs
  exact count_loop (by decide) (DecInv s0) (fun k hk t ht => dec_step hp hk ht) hs

end VG.Proof.MlKem.AArch64.Codec16

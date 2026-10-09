import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSegmentLayout

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample (coeffAddr)
open VG.Proof.MlDsa.AArch64.Sample.RejNtt (movQ_ok)

def tailCursor (k : Nat) : List Instr :=
  [.addImm .x .x3 .x21 (1024*k),.movz .x .x6 256 0,.sub .x .x6 .x6 .x4,
   .lsl .x .x6 .x6 2,.add .x .x3 .x3 .x6]

theorem tailCursor_ok {s : State} {k len : Nat} (hk : k<4) (hl : len≤256)
    (hc : (s.gpr .x4).toNat=256-len) :
    WP isa (.block (tailCursor k)) s fun t => Only [.x3,.x6] s t ∧
      t.gpr .x3=coeffAddr (s.gpr .x21+BitVec.ofNat 64 (1024*k)) len := by
  unfold tailCursor
  refine wp_addImm (by omega) fun a ha ea => wp_movz fun b hb eb =>
    wp_sub fun c hc' ec => wp_lsl (by decide) fun d hd ed => wp_add fun t ht et => wp_nil ?_
  have hb6 : b.gpr .x6=256 := by rw [eb]; rfl
  have hc6 : (c.gpr .x6).toNat=len := by
    rw [ec,toNat_sub_n (by rw [hb6,hb.get .x4,ha.get .x4,hc]; change 256-len≤256; omega),
      hb6,hb.get .x4,ha.get .x4,hc]
    change 256-(256-len)=len
    omega
  have hd6 : d.gpr .x6=BitVec.ofNat 64 (4*len) := by
    apply BitVec.eq_of_toNat_eq
    rw [ed,toNat_lsl_n (by rw [hc6]; omega),hc6,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    omega
  refine ⟨((((ha.trans hb).trans hc').trans hd).trans ht).mono (by decide),?_⟩
  rw [et,hd.get .x3,hc'.get .x3,hb.get .x3,ea,hd6]

def tailRead (k : Nat) : List Instr :=
  [.addImm .x .x6 .x19 (840+1008*k),.addImm .x .x6 .x6 1005,.ldr .w .x6 .x6 0,
   .movz .x .x7 65535 0,.movk .x .x7 127 1,.logic .and .x .x6 .x6 .x7]++
  Impl.MlDsa.AArch64.Sample.movQ .x7

theorem tailRead_ok {s : State} {k : Nat} (hk : k<4)
    (hr : InRegions (s.rd++s.wr) (s.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005)) 4) :
    WP isa (.block (tailRead k)) s (Only [.x6,.x7] s) := by
  unfold tailRead
  simp only [List.cons_append,List.nil_append]
  refine wp_addImm (by omega) fun a ha ea => wp_addImm (by decide) fun b hb eb =>
    wp_ldrw (a := s.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005)) (by decide)
      (by rw [ptr_zero,eb,ea,Offset.add_add])
      (by rw [hb.rd,hb.wr,ha.rd,ha.wr]; exact hr) fun c hc ec =>
    wp_movz fun d hd ed => wp_movk1 fun e he ee =>
    wp_and fun f hf ef => movQ_ok fun t ht et => wp_nil ?_
  exact ((((((ha.trans hb).trans hc).trans hd).trans he).trans hf).trans ht).mono (by decide)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

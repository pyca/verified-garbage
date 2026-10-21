module

public import VerifiedGarbage.Impl.Ffdh.Arm.CombPrecompute
public import VerifiedGarbage.Proof.Ffdh.Arm.Locals
public import VerifiedGarbage.Proof.Ffdh.Arm.Output
import VerifiedGarbage.Proof.Bignum.Arm.Store64
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Bignum.Arm.Stack

/-! Three canonical 64-bit metadata words, written by native 32-bit stores. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Impl.Ffdh.Arm.CombPrecompute
open VG.Proof.X25519.Arm (Rest)

private theorem outputWrite {s : State} {ctx : BitVec 32} {d : Nat}
    (h : OutputBuffer ctx 24 s) (fit : d+4≤24) :
    InRegions s.wr (off (State.addr ctx) d) 4 := by
  obtain ⟨r,hr,contains⟩ := h.writable
  refine ⟨r,hr,?_⟩
  change (off (State.addr ctx) d-r.base).toNat+4≤r.len
  have eq : off (State.addr ctx) d-r.base=(State.addr ctx-r.base)+BitVec.ofNat 64 d := by
    simp only [off,BitVec.sub_eq_add_neg]
    ac_rfl
  rw [eq,BitVec.toNat_add,BitVec.toNat_ofNat]
  have hmod := Nat.mod_le ((State.addr ctx-r.base).toNat+d%2^64) (2^64)
  change (State.addr ctx-r.base).toNat+24≤r.len at contains
  have dfit : d<2^64 := by omega
  rw [Nat.mod_eq_of_lt dfit] at *
  omega

def combHeaderWord (slot d : Nat) : List Instr :=
  [.ldrSp .r1 slot] ++ VG.Impl.Bignum.Arm.store64 .r1 .r2 .r4 d

private theorem zero_high_nat {N : Nat} (fit : N<2^32) :
    ((0 : BitVec 32) ++ BitVec.ofNat 32 N)=BitVec.ofNat 64 N := by
  rw [zero_high_addr]
  apply BitVec.eq_of_toNat_eq
  simp only [State.addr,BitVec.toNat_setWidth,BitVec.toNat_ofNat]
  omega

theorem combHeaderWord_ok (s : State) {base ctx : BitVec 32} {len slot d N : Nat}
    (locals : Locals base len s) (ws : OutputBuffer ctx 24 s)
    (slotFit : slot+4≤72) (dstFit : d+8≤24) (valueFit : N<2^32)
    (source : s.mem.readW (off (State.addr s.sp) slot) 32=BitVec.ofNat 32 N)
    (ptr : s.gpr .r4=ctx) (zero : s.gpr .r2=0) :
    WP isa (.block (combHeaderWord slot d)) s fun t =>
      t.mem=s.mem.writeW (off (State.addr ctx) d) (BitVec.ofNat 64 N) ∧
      Frame [⟨off (State.addr ctx) d,8⟩] s.mem t.mem ∧ Rest [.r1] s t := by
  rw [combHeaderWord,WP.block_append_iff]
  refine WP.mono (localLoad_ok s .r1 locals slotFit) ?_
  rintro u ⟨r1,memU,restU⟩
  have ptrU : u.gpr .r4=ctx := (restU.gpr .r4 (by simp)).trans ptr
  have wsU := ws.after restU
  have highU : u.gpr .r2=0 := (restU.gpr .r2 (by simp)).trans zero
  have offset : off (State.addr ctx) d + BitVec.ofNat 64 4=off (State.addr ctx) (d+4) :=
    Offset.add_add _ _ _
  refine WP.mono (store64_ok u .r1 .r2 .r4 d (off (State.addr ctx) d) (by omega)
    (by rw [ptrU]; exact addr_add (by have := ws.fits; omega))
    (by rw [ptrU,offset]; exact addr_add (by have := ws.fits; omega))
    (outputWrite wsU (by omega)) (by rw [offset]; exact outputWrite wsU (by omega))) ?_
  rintro t ⟨memT,restT⟩
  rw [highU,r1,source,zero_high_nat valueFit,memU] at memT
  refine ⟨memT,?_,restU.trans (restT.mono (by simp))⟩
  rw [memT]
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

theorem combHeader_ok (s : State) {base ctx : BitVec 32} {len N width d : Nat}
    (locals : Locals base len s) (ws : OutputBuffer ctx 24 s)
    (separate : Region.Disjoint ⟨State.addr s.sp,72⟩ ⟨State.addr ctx,24⟩)
    (nFit : N<2^32) (wFit : width<2^32) (dFit : d<2^32)
    (savedCtx : s.mem.readW (off (State.addr s.sp) 4) 32=ctx)
    (savedN : s.mem.readW (off (State.addr s.sp) 16) 32=BitVec.ofNat 32 N)
    (savedWidth : s.mem.readW (off (State.addr s.sp) 20) 32=BitVec.ofNat 32 width)
    (savedRows : s.mem.readW (off (State.addr s.sp) 44) 32=BitVec.ofNat 32 d) :
    WP isa (.block header) s fun t =>
      t.mem=((s.mem.writeW (off (State.addr ctx) 0) (BitVec.ofNat 64 N)).writeW
        (off (State.addr ctx) 8) (BitVec.ofNat 64 width)).writeW
        (off (State.addr ctx) 16) (BitVec.ofNat 64 d) ∧
      Frame [⟨State.addr ctx,24⟩] s.mem t.mem ∧ Rest [.r1,.r2,.r4] s t := by
  have whole {m m' : Mem} {off0 : Nat} (fit : off0+8≤24)
      (frame : Frame [⟨off (State.addr ctx) off0,8⟩] m m') :
      Frame [⟨State.addr ctx,24⟩] m m' := by
    apply frame.sub
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact ⟨_,List.mem_singleton_self _,Offset.sub_base _ fit⟩
  have readStack {m m' : Mem} {slot : Nat} (fit : slot+4≤72)
      (frame : Frame [⟨State.addr ctx,24⟩] m m') :
      m'.readW (off (State.addr s.sp) slot) 32=m.readW (off (State.addr s.sp) slot) 32 :=
    frame.readW (r := ⟨State.addr s.sp,72⟩) (Offset.contains_base _ fit (by omega))
      (by intro r hr; rw [List.mem_singleton] at hr; subst r; exact separate) (by decide)
  change WP isa (.block ([.ldrSp .r4 4,.mov .r2 (.imm 0)] ++
    (combHeaderWord 16 0 ++ (combHeaderWord 20 8 ++ combHeaderWord 44 16)))) s _
  rw [WP.block_append_iff]
  refine wp_loadStack (a := off (State.addr s.sp) 4) (by decide)
    (addr_add (by have := locals.space.nowrap; omega)) (locals.read (by decide)) fun a load => ?_
  refine VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_imm (by decide)) fun u move => WP.block_nil ?_
  have restU : Rest [.r1,.r2,.r4] s u := (load.rest (by simp)).trans (move.rest (by simp))
  have memU : u.mem=s.mem := move.mem.trans load.mem
  have ptrU : u.gpr .r4=ctx := (move.other .r4 (by decide)).trans (load.gpr.trans savedCtx)
  rw [WP.block_append_iff]
  refine WP.mono (combHeaderWord_ok u (locals.after restU) (ws.after restU) (by decide) (by decide) nFit
    (by rw [restU.sp,memU]; exact savedN) ptrU move.gpr) ?_
  rintro v ⟨memV,frameV,restV⟩
  have rV : Rest [.r1,.r2,.r4] s v := restU.trans (restV.mono (by simp))
  have fV : Frame [⟨State.addr ctx,24⟩] s.mem v.mem := by rw [memU] at frameV; exact whole (by decide) frameV
  have widthV : v.mem.readW (off (State.addr v.sp) 20) 32=BitVec.ofNat 32 width := by
    rw [rV.sp,readStack (by decide) fV,savedWidth]
  have ptrV : v.gpr .r4=ctx := (restV.gpr .r4 (by simp)).trans ptrU
  have zeroV : v.gpr .r2=0 := (restV.gpr .r2 (by simp)).trans move.gpr
  rw [WP.block_append_iff]
  refine WP.mono (combHeaderWord_ok v (locals.after rV) (ws.after rV) (by decide) (by decide) wFit
    widthV ptrV zeroV) ?_
  rintro w ⟨memW,frameW,restW⟩
  have rW : Rest [.r1,.r2,.r4] s w := rV.trans (restW.mono (by simp))
  have fW : Frame [⟨State.addr ctx,24⟩] s.mem w.mem := fV.trans (whole (by decide) frameW)
  have rowsW : w.mem.readW (off (State.addr w.sp) 44) 32=BitVec.ofNat 32 d := by
    rw [rW.sp,readStack (by decide) fW,savedRows]
  have ptrW : w.gpr .r4=ctx := (restW.gpr .r4 (by simp)).trans ptrV
  have zeroW : w.gpr .r2=0 := (restW.gpr .r2 (by simp)).trans zeroV
  refine WP.mono (combHeaderWord_ok w (locals.after rW) (ws.after rW) (by decide) (by decide) dFit
    rowsW ptrW zeroW) ?_
  rintro t ⟨memT,frameT,restT⟩
  rw [memW,memV,memU] at memT
  exact ⟨memT,fW.trans (whole (by decide) frameT),rW.trans (restT.mono (by simp))⟩

end VG.Proof.Ffdh.Arm

module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.WindowLoop
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

/-! Public seam facts and retained constants after all nonfinal windows. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Mont.AArch64.P521Field
open VG.Impl.Weierstrass.AArch64.P521Native (windowLoop)

 structure NativeAfterWindow (base table : Addr) (k : Nat) (s t : State) : Prop where
  data : WindowData base table k t
  point : canonicalPoint t.mem base 1072
  value : ordinaryPoint t.mem base 1072=windowNonfinal s.mem table k 104 (ordinaryPoint s.mem base 1072)
  counter : t.gpr .x19=1#64
  exit : t.gpr .x4=0#64
  outputPointer : t.gpr .x20=s.gpr .x20
  workspace : t.gpr .x0=base
  tablePointer : t.gpr .x26=table
  sp : t.sp=s.sp
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  vector31 : t.v .v31=s.v .v31
  vector29 : t.v .v29=s.v .v29
  tailGP : ∀r∈[Reg.x27,Reg.x28],t.gpr r=s.gpr r
  lowMemory : ∀d,d<856 → t.mem (off base d)=s.mem (off base d)
  originalD : wordsVal t.mem base 2368 9=wordsVal s.mem base 2368 9
  flag : word t.mem base 3232=word s.mem base 3232
  frame : WindowPhaseFrame base s.mem t.mem

 theorem native_window_ok {s : State} {base table : Addr} {k : Nat}
    (data : WindowData base table k s) (apart : Region.Disjoint ⟨base,8192⟩ ⟨table,3456⟩)
    (bound : canonicalPoint s.mem base 1072) (counter : s.gpr .x19=105#64) :
    WP isa windowLoop s (NativeAfterWindow base table k s) := by
  refine WP.mono (window_loop_104 data apart bound counter) fun t ⟨b,p,d,f,pub,c19,c4⟩ => ?_
  refine ⟨d,b,p,c19,c4,pub.gp .x20 (by decide) (by decide) (by decide),d.scr.x0,d.readable.reg,
    pub.sp,pub.rd,pub.wr,pub.v31,pub.v29,?_,?_,?_,?_,f⟩
  · intro r hr
    have choices : r=Reg.x27 ∨ r=Reg.x28 := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using hr
    rcases choices with rfl|rfl
    · exact pub.gp .x27 (by decide) (by decide) (by decide)
    · exact pub.gp .x28 (by decide) (by decide) (by decide)
  · intro d hd
    have e : ofs base (off base d)=d := by
      simpa only [BitVec.add_zero,Nat.add_zero] using (ofs_off base (d:=d) (i:=0) (by omega_arith))
    exact f _ (by rw [e]; omega_arith) (by rw [e]; omega_arith) (by rw [e]; omega_arith)
  · exact WindowPhaseFrame.wordsVal f (by decide) (by decide) (by decide) (by decide)
  · exact WindowPhaseFrame.word f (by decide) (by decide) (by decide) (by decide)

end VG.Proof.Weierstrass.AArch64.P521Native

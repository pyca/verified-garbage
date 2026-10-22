module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Montgomery
public import VerifiedGarbage.Proof.Bignum.X86.RtCallTiming

/-! Public arguments and the precondition of the shared Montgomery call. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86.RtCall
open VG.Proof.Bignum.X86.PublicRt (calleeOf)

def montgomeryValues (base : Addr) (n o a b : Nat) : Nat → BitVec 32 :=
  callArg (BitVec.ofNat 32 base.toNat) (BitVec.ofNat 32 (montgomeryBytes / 8))
    n (slot n 0) 0 montgomeryScratch (slot n o) (slot n a) (slot n b)

structure MontgomeryInput (base : Addr) (sp : BitVec 32) (n b : Nat) (s : State) : Prop where
  scr : Scr s base montgomeryBytes
  room : CallRoom (s.gpr .esp) base montgomeryBytes
  stack : s.gpr .esp = sp
  inverse : (val32 s.mem base (slot n 0) (2 * n) * w32 s.mem base 0 + 1) % 2 ^ 32 = 0
  reduced : val32 s.mem base (slot n b) (2 * n) < val32 s.mem base (slot n 0) (2 * n)

theorem montgomery_call_setup {s : State} {base : Addr} {sp : BitVec 32} {n o a b : Nat}
    (H : MontgomeryInput base sp n b s) (hn : 0 < n) (hn' : n ≤ 48)
    (ho : o < 9) (ha : a < 9) (hb : b < 9) (ho0 : o ≠ 0) :
    WP isa (.block (montgomeryArgs n o a b)) (allocFrame 36 s)
      (CallState base montgomeryBytes sp (montgomeryValues base n o a b)) := by
  have low := H.room.low
  have fit : ((allocFrame 36 s).gpr .esp).toNat + 36 ≤ 2 ^ 32 := by
    rw [allocFrame_esp, VG.X86.sub_toNat (by omega)]
    have := (s.gpr .esp).isLt; omega
  refine WP.mono (montgomery_arguments_ready fit
    (by rw [allocFrame_wr]; exact List.mem_cons_self ..)) fun g ⟨K, frame, read⟩ => ?_
  have gsp : g.gpr .esp = s.gpr .esp - BitVec.ofNat 32 36 := by
    rw [K.1 .esp (by decide), allocFrame_esp]
  have F : Frame [below (s.gpr .esp) 36] s.mem g.mem := frame
  have reads : ∀ i < 9, g.mem.readW ((g.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 * i)) 32 =
      callArg (s.gpr .edi) (BitVec.ofNat 32 (montgomeryBytes / 8)) n (slot n 0) 0 montgomeryScratch
        (slot n o) (slot n a) (slot n b) i := by
    intro i hi
    rw [K.1 .esp (by decide), read i hi, allocFrame_gpr _ _ (by decide)]
  have abi := callee_abi H.scr (by decide : montgomeryBytes =
      (BitVec.ofNat 32 (montgomeryBytes / 8)).toNat * 8)
    H.room (montgomery_offsets hn hn' ho ha hb ho0) gsp F reads H.inverse H.reduced
  have edi : s.gpr .edi = BitVec.ofNat 32 base.toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [H.scr.edi_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
      have := H.scr.nowrap; unfold montgomeryBytes at this; omega)]
  refine ⟨abi, by rw [gsp, H.stack], ?_, ?_, ?_⟩
  · intro i hi
    rw [callee_arg H.room.low gsp reads hi, edi]
    rfl
  · rw [K.2.2, allocFrame_wr, gsp]; exact List.mem_cons_self ..
  · rw [K.2.2, allocFrame_wr]; exact List.mem_cons_of_mem _ H.scr.wr

end VG.Proof.Dsa.X86.Generation

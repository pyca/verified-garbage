module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.MontgomeryOffsets
public import VerifiedGarbage.Proof.Dsa.X86.Generation.MontgomeryArguments
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Parameter generation calls the existing verified Montgomery implementation. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86.RtCall

theorem montgomery_noSp (n o a b : Nat) :
    NoSp (.seq (.block (montgomeryArgs n o a b))
      (.call Spec.Rsa.MontMul.mulApi.name VG.Impl.Mont.X86.Rt.body) : Prog isa) := by
  apply NoSp.of_all
  have hc : (instrs VG.Impl.Mont.X86.Rt.body).all (fun i => !Taint.clobbers i .esp) = true := by
    simpa only [← Code.allInstrs_eq] using
      (by decide : VG.Impl.Mont.X86.Rt.body.allInstrs (fun i => !Taint.clobbers i .esp) = true)
  rw [Code.allInstrs_eq]
  simp only [instrs, montgomeryArgs, montgomeryStores, List.all_append,
    List.all_cons, List.all_nil, hc]
  simp [Taint.clobbers, Taint.dst]

theorem montgomery_ok {s : State} {base : Addr} {n o a b : Nat}
    (scr : Scr s base montgomeryBytes) (room : CallRoom (s.gpr .esp) base montgomeryBytes)
    (hn : 0 < n) (hn' : n ≤ 48) (ho : o < 9) (ha : a < 9) (hb : b < 9) (ho0 : o ≠ 0)
    (inverse : (val32 s.mem base (slot n 0) (2 * n) * w32 s.mem base 0 + 1) % 2 ^ 32 = 0)
    (bLt : val32 s.mem base (slot n b) (2 * n) < val32 s.mem base (slot n 0) (2 * n)) :
    WP isa (montgomery n o a b) s fun t =>
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [⟨off base (slot n o), 8 * n⟩,
        ⟨off base montgomeryScratch, Spec.Rsa.MontMul.scratchBytes n⟩,
        below (s.gpr .esp) 40] s.mem t.mem ∧
      val32 t.mem base (slot n o) (2 * n) < val32 s.mem base (slot n 0) (2 * n) ∧
      val32 t.mem base (slot n o) (2 * n) * 2 ^ (64 * n) % val32 s.mem base (slot n 0) (2 * n) =
        val32 s.mem base (slot n a) (2 * n) * val32 s.mem base (slot n b) (2 * n) %
          val32 s.mem base (slot n 0) (2 * n) := by
  apply call_ok (wsLen := BitVec.ofNat 32 (montgomeryBytes / 8)) scr (by decide) room
    (montgomery_offsets hn hn' ho ha hb ho0) inverse bLt (montgomery_noSp n o a b)
  have low := room.low
  have fit : ((allocFrame 36 s).gpr .esp).toNat + 36 ≤ 2 ^ 32 := by
    rw [allocFrame_esp, VG.X86.sub_toNat (by omega)]
    have := (s.gpr .esp).isLt
    omega
  simpa only [allocFrame_gpr _ _ (show Reg.edi ≠ .esp by decide)] using
    (montgomery_arguments_ready (n := n) (o := o) (a := a) (b := b) fit
      (by rw [allocFrame_wr]; exact List.mem_cons_self ..))

end VG.Proof.Dsa.X86.Generation

module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.ArithmeticFrame
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Framework.Offset

/-! Bind the allocated public arguments to the existing runtime workspace invariant. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (Ws num arr)

theorem ArithmeticSetup.ready {s t : State} {base : Addr} {bytes len count candidate : Nat}
    (H : ArithmeticSetup s t) (ws : Ws s base bytes (kw len) count)
    (length : len ≤ 1024) (lengthReg : s.gpr .esi = BitVec.ofNat 32 len)
    (low : 16 ≤ (s.gpr .esp).toNat)
    (stack : StkOk ((allocFrame 16 s).gpr .esp) base bytes)
    (apart : Region.Disjoint (below (s.gpr .esp) 16) ⟨base, bytes⟩)
    (arrays : 0 < count) (current : num s.mem base (kw len) 0 = candidate) :
    RtWs arithmeticLay (t.withRegions (arithmeticRead t) [⟨base, bytes⟩]) base bytes len count ∧
      num t.mem base (kw len) 0 = candidate := by
  have wsp : Ws t base bytes (kw len) count := by
    refine ⟨⟨?_, ?_, ws.workspace.nowrap, ?_⟩, ws.fits, ws.wpos, ws.wle⟩
    · rw [H.keeps.1 .edi (by decide), allocFrame_gpr _ _ (by decide)]
      exact ws.workspace.edi
    · rw [H.keeps.2.2, allocFrame_wr]
      exact List.mem_cons_of_mem _ ws.workspace.wr
    · rw [H.keeps.1 .esp (by decide)]; exact stack
  have fit : (t.gpr .esp).toNat + 16 ≤ 2 ^ 32 := by
    rw [H.keeps.1 .esp (by decide), allocFrame_esp, VG.X86.sub_toNat low]
    have := (s.gpr .esp).isLt; omega
  have frameApart : Region.Disjoint ⟨(t.gpr .esp).setWidth 64, 16⟩ ⟨base, bytes⟩ := by
    rw [H.keeps.1 .esp (by decide)]
    exact apart
  have edi : s.gpr .edi = BitVec.ofNat 32 base.toNat := by
    apply BitVec.eq_of_toNat_eq
    have bound : base.toNat < 2 ^ 32 := by rw [← ws.workspace.edi_toNat]; exact (s.gpr .edi).isLt
    rw [ws.workspace.edi_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  refine ⟨arithmetic_ready wsp length fit frameApart (H.workspace.trans edi)
    (H.length.trans lengthReg), ?_⟩
  have fitArray := ws.arr_fit arrays
  have nowrap := ws.workspace.nowrap
  unfold VG.Proof.Rsa.X86.Keys.S at fitArray
  change val32 t.mem base (arr (kw len) 0) (kw len) = candidate
  rw [← VG.Proof.Bignum.read_eq_val32, H.frame.read (r := ⟨base, bytes⟩)
    (Offset.contains_base _ (by omega) (by omega))
    (by intro r hr; rw [List.mem_singleton.mp hr]; exact apart.symm) (by omega),
    VG.Proof.Bignum.read_eq_val32]
  exact current

end VG.Proof.Dsa.X86.Generation

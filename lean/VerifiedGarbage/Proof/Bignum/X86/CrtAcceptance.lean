module

public import VerifiedGarbage.Impl.Bignum.X86.CrtCore
public import VerifiedGarbage.Proof.Ecdsa.X86.Flags
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! # Save and merge private-key acceptance masks without branching -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86.Crt
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Ecdsa.X86

theorem storeMask_ok {s : State} {base : Addr} {bytes : Nat} {r : Reg}
    (hs : Scr s base bytes) (bound : 12 ≤ bytes) :
    WP isa (.block [.store (sc acceptanceOffset) r]) s fun t =>
      t.mem.readW (off base acceptanceOffset) 32 = s.gpr r ∧
      Outside base acceptanceOffset 4 s.mem t.mem ∧ Keeps [] s t := by
  refine wp_storeS (hs.ea (by unfold acceptanceOffset; omega))
    (hs.write (by unfold acceptanceOffset; omega)) fun t T => WP.block_nil ?_
  exact ⟨by rw [T.mem, Mem.readW_writeW_self32],
    by rw [T.mem]; exact writeW32_outside _ _ _ (by unfold acceptanceOffset; decide), T.keeps []⟩

theorem mergeAcceptance_ok {s : State} {base : Addr} {bytes : Nat} (P Q : Prop) [Decidable P] [Decidable Q]
    (hs : Scr s base bytes) (bound : 12 ≤ bytes)
    (saved : s.mem.readW (off base acceptanceOffset) 32 = mask32 P) (next : s.gpr .eax = mask32 Q) :
    WP isa (.block mergeAcceptance) s fun t =>
      t.mem.readW (off base acceptanceOffset) 32 = mask32 (P ∧ Q) ∧
      Outside base acceptanceOffset 4 s.mem t.mem ∧ Keeps [.edx] s t := by
  unfold mergeAcceptance
  refine wp_movS (readSrc_sc hs (by unfold acceptanceOffset; omega)) fun u U _ => ?_
  refine wp_logicS (.inl rfl) rfl fun v V => ?_
  have K := U.keeps.trans V.keeps
  have Hv := hs.of_keeps K (by decide)
  refine wp_storeS (Hv.ea (by unfold acceptanceOffset; omega))
    (Hv.write (by unfold acceptanceOffset; omega)) fun t T => WP.block_nil ?_
  refine ⟨?_, ?_, K.trans (T.keeps _)⟩
  · rw [T.mem, Mem.readW_writeW_self32, V.gpr, ite_eq_left rfl, U.gpr,
      U.other _ (by decide), saved, next, mask32_and]
  · rw [T.mem, V.mem, U.mem]
    exact writeW32_outside _ _ _ (by unfold acceptanceOffset; decide)

end VG.Proof.Bignum.X86.Crt

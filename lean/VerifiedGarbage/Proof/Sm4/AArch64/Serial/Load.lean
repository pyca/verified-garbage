module

public import VerifiedGarbage.Proof.Sm4.AArch64.Serial.Lookup
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Load the prepared SM4 S-box from fixed public offsets -/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.Serial

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl VG.Impl.Tbl.AArch64
open VG.Impl.Sm4.AArch64.Serial

theorem exec_load_vector (s : State) (t : VReg) (n : Reg) (off : Nat)
    (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.ldrq t n off) s = some (s.setV t (s.mem.read (s.gpr n + BitVec.ofNat 64 off) 16)) := by
  simp [exec,addr,ho,State.load,h]

theorem loads_ok (s : State) (readable : InRegions (s.rd ++ s.wr) (s.gpr .x5) 256) (n : Nat)
    (hn : n ≤ 16) :
    WP isa (.block ((List.range n).map fun r => .ldrq (treg r) .x5 (16*r))) s fun t =>
      (∀ r < n, t.v (treg r) = s.mem.read (s.gpr .x5 + BitVec.ofNat 64 (16*r)) 16) ∧
      (∀ w, (∀ r < n, w ≠ treg r) → t.v w = s.v w) ∧ t = { s with v := t.v } := by
  induction n with
  | zero => exact WP.block_nil ⟨fun _ h => absurd h (by omega), fun _ _ => rfl, rfl⟩
  | succ n ih =>
    rw [List.range_succ,List.map_append,List.map_singleton,WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun a ⟨arow,av,ae⟩ => ?_
    have hin : InRegions (a.rd ++ a.wr) (a.gpr .x5 + BitVec.ofNat 64 (16*n)) 16 := by
      rw [ae]
      exact CallLay.inRegions_sub readable (by omega) (by decide)
    refine WP.of_runBlock ⟨_,by
      rw [runBlock_cons,exec_load_vector _ _ _ _ ⟨by omega,by omega⟩ hin,runStep_some,runBlock_nil],
      fun r hr => ?_,fun w hw => ?_,?_⟩
    · have hmx : a.mem = s.mem ∧ a.gpr = s.gpr := by rw [ae]; exact ⟨rfl,rfl⟩
      by_cases he : r = n
      · subst he; rw [v_setV_self,hmx.1,hmx.2]
      · rw [v_setV_of_ne _ _ (fun e => he (treg_inj r (by omega) n (by omega) e)),arow r (by omega)]
    · rw [v_setV_of_ne _ _ (hw n (by omega)),av w (fun r hr => hw r (by omega))]
    · rw [ae]; rfl

theorem loadSbox_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr .x5) 256)
    (bytes : ∀ k < 256, s.mem (s.gpr .x5 + BitVec.ofNat 64 k) = Spec.Sm4.sbox.getD k 0) :
    WP isa (.block loadSbox) s fun t => Table t ∧ t = { s with v := t.v } := by
  refine WP.mono (loads_ok s readable 16 (by decide)) fun t ⟨ht,_,he⟩ => ⟨?_,he⟩
  intro k hk
  rw [tbyte,ht _ (by omega)]
  change (s.mem.read _ 16).extractLsb' (8*(k%16)) 8 = _
  rw [Mem.extractLsb'_read s.mem _ (by omega),VG.Offset.add_add,
    show 16*(k/16)+k%16 = k by omega]
  exact bytes k hk

end VG.Proof.Sm4.AArch64.Serial

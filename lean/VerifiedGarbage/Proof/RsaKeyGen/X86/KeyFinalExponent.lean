module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyFinal
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyBorrowMask
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeySaveSlot
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyConstant
import VerifiedGarbage.Proof.Rsa.X86.KeySub
import VerifiedGarbage.Proof.Rsa.InverseArithmetic
import VerifiedGarbage.Proof.Mont.X86.Instr
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.Prop
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Basic

/-! # Native public-exponent range checks -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem exponentUpper_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) :
    WP isa (.block exponentUpper) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [] [kFlag] s.mem t.mem ∧
      slot t.mem B kFlag = (if val32 s.mem B kEv 2 < 2 ^ 33 then 1 else 0) ∧ Keeps [.eax] s t := by
  have head := h.hdr_le
  unfold exponentUpper
  refine wp_movS (readSrc_sc h.workspace (by unfold kEvHi hdr at *; omega)) fun u U _ => ?_
  refine wp_cmpi fun v V carry _ => ?_
  refine wp_sbb_self carry fun w W => ?_
  refine wp_andi fun a A => ?_
  have K : Keeps [.eax] s a := ((U.keeps.trans (V.keeps _)).trans W.keeps).trans A.keeps
  have ha := h.rest K
  refine wp_storeS (ha.workspace.ea (by unfold kFlag hdr at *; omega))
    (ha.workspace.write (by unfold kFlag hdr at *; omega)) fun t T => WP.block_nil ?_
  have memory : a.mem = s.mem := A.mem.trans (W.mem.trans (V.mem.trans U.mem))
  have value : (a.gpr .eax).toNat = (if w32 s.mem B kEvHi < 2 then 1 else 0) := by
    rw [A.gpr, W.gpr, U.gpr]
    change ((if decide (w32 s.mem B kEvHi < 2) then BitVec.allOnes 32 else 0#32) &&& (1 : BitVec 32)).toNat = _
    simp only [decide_eq_true_eq]
    split <;> rfl
  have upper : w32 s.mem B kEvHi < 2 ↔ val32 s.mem B kEv 2 < 2 ^ 33 := by
    have lo := (s.mem.readW (off B kEv) 32).isLt
    change w32 s.mem B kEv < 2 ^ 32 at lo
    change w32 s.mem B kEvHi < 2 ↔ w32 s.mem B kEv + 2 ^ 32 * w32 s.mem B kEvHi < 2 ^ 33
    omega
  refine ⟨ha.rest (T.keeps []), ?_, ?_, K.trans (T.keeps _)⟩
  · rw [T.mem, memory]
    exact Keep.of_slot (writeW32_outside _ _ _ (by decide)) (by simp)
  · unfold slot
    rw [T.mem, memory, w32_write_self, value]
    simp only [upper]

theorem exponentAtLeastThree_ok {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32)
    (bit : slot s.mem B kOk ≤ 1) :
    WP isa (exponentAtLeastThree n) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [aT1, aT2] [kFlag, kOk] s.mem t.mem ∧
      slot t.mem B kOk = (if 3 ≤ num s.mem B n aE ∧ slot s.mem B kOk = 1 then 1 else 0) ∧
      Keeps [.eax, .ecx, .edx, .ebp, .ebx] s t := by
  have bound : 3 < 2 ^ (32 * n) := by
    have H := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 2 ≤ 32 * n by have := h.wpos; omega)
    omega
  unfold exponentAtLeastThree seqs
  refine WP.seq (WP.mono (constArray_ok h (by decide) bound) fun u ⟨hu, Ou, constant, Ku⟩ => ?_)
  have E : num u.mem B n aE = num s.mem B n aE := Ou.num (by decide) (by simp) (h.fit64 (by decide))
  refine WP.seq (WP.mono (sub3_ok hu (by decide) (by decide) (by decide) (by decide) (by decide))
    fun v ⟨hv, Ov, subtract, borrow, Kv⟩ => ?_)
  rw [E, constant] at subtract
  have iffBorrow := VG.Proof.Rsa.borrow_iff subtract (val32_lt _ _ _ _) borrow
  have maskV : slot v.mem B kOk = slot s.mem B kOk :=
    (Ov.slot (by decide) (by simp)).trans (Ou.slot (by decide) (by simp))
  refine WP.seq (WP.mono (saveSlot_ok hv (by decide) (by decide)) fun w ⟨hw, Ow, flag, Kw⟩ => ?_)
  rw [maskV] at flag
  have borrowW : (w.gpr .ebx).toNat = (v.gpr .ebx).toNat := congrArg BitVec.toNat (Kw.1 .ebx (by decide))
  refine WP.mono (borrowMask_ok hw (by rw [borrowW]; exact borrow)
    (by rw [flag]; exact bit)) fun t ⟨ht, Ot, value, Kt⟩ => ?_
  refine ⟨ht, ((Ou.join Ov (js := [aT1, aT2]) (ds := [])).join Ow
    (js := [aT1, aT2]) (ds := [kFlag])).join Ot (js := [aT1, aT2]) (ds := [kFlag, kOk]), ?_,
    (Ku.mono (by decide)).trans (Kv.trans ((Kw.mono (by decide)).trans (Kt.mono (by decide))))⟩
  simpa only [borrowW, iffBorrow, flag] using value

end VG.Proof.RsaKeyGen.X86.Key

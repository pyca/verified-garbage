module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyLcm
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyEven
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # A secret parity selector for canonicalizing the LCM factors -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.RsaKeyGen.X86.Key

theorem evenFlag_ok {s : State} {B : Addr} {Z n input : Nat}
    (h : Ws s B Z n 32) (hi : input < 32) :
    WP isa (.block (evenFlag n input)) s fun t =>
      Ws t B Z n 32 ∧ Keep B n [] [kFlag] s.mem t.mem ∧
      slot t.mem B kFlag = (if num s.mem B n input % 2 = 0 then 1 else 0) ∧ Keeps [.eax] s t := by
  have fit := h.arr_fit hi
  have head := h.hdr_le
  unfold evenFlag
  refine wp_movS (readSrc_sc h.workspace
    (by change arr n input + 4 ≤ Z; unfold S at fit; omega)) fun u U _ => ?_
  refine wp_logicS (.inl rfl) rfl fun v V => ?_
  refine wp_logicS (.inr rfl) rfl fun w W => ?_
  have K : Keeps [.eax] s w := (U.keeps.trans V.keeps).trans W.keeps
  have hw := h.rest K
  have memory : w.mem = s.mem := W.mem.trans (V.mem.trans U.mem)
  have value : w.gpr .eax =
      (s.mem.readW (off B (arr n input)) 32 &&& (1 : BitVec 32)) ^^^ (1 : BitVec 32) := by
    rw [W.gpr, V.gpr, U.gpr]
    rfl
  have numeric : (w.gpr .eax).toNat = if num s.mem B n input % 2 = 0 then 1 else 0 := by
    rw [value, num_parity _ _ h.wpos input]
    have E := even_bit (s.mem.readW (off B (arr n input)) 32) (s.mem.readW (off B (arr n input)) 32)
    simpa only [BitVec.or_self, and_self] using E
  refine wp_storeS (hw.workspace.ea (by unfold kFlag VG.Impl.Rsa.X86.Keys.hdr at *; omega))
    (hw.workspace.write (by unfold kFlag VG.Impl.Rsa.X86.Keys.hdr at *; omega))
    fun t T => WP.block_nil ?_
  refine ⟨hw.rest (T.keeps []), ?_, ?_, K.trans (T.keeps _)⟩
  · rw [T.mem, memory]
    exact Keep.of_slot (writeW32_outside _ _ _ (by decide)) (by simp)
  · unfold slot
    rw [T.mem, memory, w32_write_self, numeric]

end VG.Proof.RsaKeyGen.X86.Key

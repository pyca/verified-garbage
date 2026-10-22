module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.HalvingState
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Header
public import VerifiedGarbage.Proof.Mont.X86.Instr

/-! The halving schedule is the public bit capacity of the reused workspace. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.Keys (Keep num slot)
open VG.Impl.Rsa.X86.KeyRt (Lay)

theorem halving_init {L : Lay} {s : State} {base : Addr} {bytes len count value : Nat}
    (h : RtWs L s base bytes len count) (arrays : 0 < count)
    (current : num s.mem base (kw len) 0 = value) :
    WP isa (.block (Impl.Dsa.X86.Generation.halvingInit L)) s fun t =>
      HalvingState L base bytes len count value 0 (32 * kw len) t ∧
      Keep base (kw len) [] [20, 56] s.mem t.mem ∧ Keeps [.eax] s t := by
  have widthBound := kw_bound h.lenLe
  unfold Impl.Dsa.X86.Generation.halvingInit
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (set_header h (d := 20) (value := 0) (by decide) (by decide)) ?_)
  rintro u ⟨hu, F, zero, K⟩
  refine bytesB_ok (r := .eax) (lenSrc hu) hu.lenLe fun v Kv memv e => ?_
  change WP isa (.block [.alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
    .alu .add .eax (.reg .eax), .store (Impl.Mont.X86.sc 56) .eax]) v _
  refine wp_addS rfl fun a A _ => wp_addS rfl fun b B _ => wp_addS rfl fun c C _ => ?_
  have ea : (a.gpr .eax).toNat = 8 * kw len := by
    rw [A.gpr, BitVec.toNat_add, e, Nat.mod_eq_of_lt (by omega)]
    omega
  have eb : (b.gpr .eax).toNat = 16 * kw len := by
    rw [B.gpr, BitVec.toNat_add, ea, Nat.mod_eq_of_lt (by omega)]
    omega
  have ec : (c.gpr .eax).toNat = 32 * kw len := by
    rw [C.gpr, BitVec.toNat_add, eb, Nat.mod_eq_of_lt (by omega)]
    omega
  have Kc : Keeps [.eax] u c := ((Kv.trans A.keeps).trans B.keeps).trans C.keeps
  have memc : c.mem = u.mem := C.mem.trans (B.mem.trans (A.mem.trans memv))
  have hc := hu.keep Kc (by decide) (by decide) (by rw [memc]; exact Outside.refl _ _ _ _)
  refine WP.mono (storeSlot_ok hc (d := 56) (by decide) .eax) ?_
  rintro t ⟨ht, F', total, K'⟩
  rw [ec] at total
  rw [memc] at F'
  have frame : Keep base (kw len) [] [20, 56] s.mem t.mem := F.join F'
  exact ⟨⟨ht, (frame.num (by simp) (by decide) (h.ws.fit64 arrays)).trans current,
    (F'.slot (by decide) (by simp)).trans zero, total⟩, frame,
    (K.trans Kc).trans (K'.mono (by simp))⟩

end VG.Proof.Dsa.X86.Generation

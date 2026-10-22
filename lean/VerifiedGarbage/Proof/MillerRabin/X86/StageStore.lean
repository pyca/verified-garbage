module

public import VerifiedGarbage.Proof.MillerRabin.X86.StageFrame
public import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Stores to the loop's header slots and public table cursor -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Mont.X86 VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt)

namespace Stage

theorem store_header {σ s : State} {base : Addr} {bytes w d : Nat} {r : Reg}
    {is : List Instr} {Q : State → Prop}
    (h : Stage base bytes w σ s) (hf : arrAt w 28 ≤ bytes)
    (hd : d ∈ [184, 188, 212, 232, 236, 240, 244])
    (k : ∀ t, Stage base bytes w σ t →
      t.mem = s.mem.writeW (off base d) (s.gpr r) → Keeps [] s t → t.zf = s.zf → WP isa (.block is) t Q) :
    WP isa (.block (.store (sc d) r :: is)) s Q := by
  have small : d + 4 ≤ 256 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have fit : d + 4 ≤ bytes := by simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at hf; omega
  refine wp_storeS (h.context.ws.ea (by omega)) (h.context.ws.write fit) fun t M => ?_
  have F : Frame [⟨off base d, 4⟩] s.mem t.mem := by
    rw [M.mem]
    exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
  exact k t (h.after_header (M.keeps []) F hd) M.mem (M.keeps []) M.zf

theorem store_cursor {σ s : State} {base : Addr} {bytes w : Nat} {r : Reg}
    {is : List Instr} {Q : State → Prop}
    (h : Stage base bytes w σ s)
    (k : ∀ t, Stage base bytes w σ t →
      t.mem = s.mem.writeW (off (byteAddr (s.gpr .esp)) tableCursor) (s.gpr r) →
      Keeps [] s t → t.zf = s.zf → WP isa (.block is) t Q) :
    WP isa (.block (.store (sp tableCursor) r :: is)) s Q := by
  refine wp_storeS (h.context.ea_stack (by decide)) (h.context.write_sp (by decide)) fun t M => ?_
  have F : Frame (stageAreas base w (σ.gpr .esp)) s.mem t.mem := by
    rw [M.mem, h.stack]
    apply (Frame.refl _ _).writeW (r := ⟨off (byteAddr (σ.gpr .esp)) tableCursor, 4⟩)
    · exact List.mem_append_right _ (by simp)
    · exact Region.contains_self _ _
  exact k t (h.after (M.keeps []) F) M.mem (M.keeps []) M.zf

end Stage
end VG.Proof.MillerRabin.X86

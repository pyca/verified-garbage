module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.Header
public import VerifiedGarbage.Proof.Mont.X86.Instr

/-! Use the existing scalar-store code for the generation control fields. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Impl.Dsa.X86.Generation VG.Proof.Mont VG.Proof.Mont.X86

theorem set_word {s : State} {base : Addr} {bytes d value : Nat}
    (scr : Scr s base bytes) (fit : d + 4 ≤ bytes) :
    WP isa (.block (setHeader d value)) s fun t =>
      t.mem = s.mem.writeW (off base d) (BitVec.ofNat 32 value) ∧
      t.gpr .eax = BitVec.ofNat 32 value ∧ Keeps [.eax] s t := by
  unfold setHeader
  refine wp_movS rfl fun a A _ => ?_
  have Sa := scr.of_keeps A.keeps (by decide)
  refine wp_storeS (Sa.ea (d := d) (by omega)) (Sa.write fit) fun t T => WP.block_nil ?_
  exact ⟨by rw [T.mem, A.gpr, A.mem], by rw [T.gpr, A.gpr], A.keeps.trans (T.keeps _)⟩

end VG.Proof.Dsa.X86.Generation

module

public import VerifiedGarbage.Proof.MillerRabin.X86.TableCopies
public import VerifiedGarbage.Proof.MillerRabin.X86.TableCount

/-! # Complete initialization of the append-only power table -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt numAt)

theorem table_init {σ s : State} {base : Addr} {bytes w : Nat}
    (h : Stage base bytes w σ s) (hw : 4 ≤ w) (hu : w ≤ 128)
    (hf : arrAt w 28 ≤ bytes)
    (width : σ.mem.readW (off base 48) 32 = BitVec.ofNat 32 w) :
    WP isa tabInit s fun t =>
      Stage base bytes w σ t ∧ w32 t.mem base sK = 14 ∧
      t.mem.readW (off (byteAddr (σ.gpr .esp)) tableCursor) 32 = ptr32 base (arrAt w 13) ∧
      numAt t.mem base w 11 = numAt s.mem base w 9 ∧
      numAt t.mem base w 12 = numAt s.mem base w 5 ∧
      numAt t.mem base w 6 = numAt s.mem base w 5 ∧
      numAt t.mem base w 5 = numAt s.mem base w 5 := by
  unfold tabInit seqs
  simp only [List.foldr_cons, List.foldr_nil]
  refine WP.seq (WP.mono (table_copies h hw hu hf width) ?_)
  rintro s₃ ⟨h₃, v₁, v₂, v₃, vx⟩
  refine WP.seq (WP.mono (table_count h₃ hu hf width) ?_)
  rintro t ⟨ht, count, cursor, F⟩
  have frame : Frame [⟨off (byteAddr (s₃.gpr .esp)) tableCursor, 4⟩, ⟨off base sK, 4⟩] s₃.mem t.mem := by
    rw [h₃.stack]
    exact F
  have same := fun a ha => stack_header_frame_num h₃.context hf (a := a) ha (by decide : sK + 4 ≤ 256) frame
  exact WP.block_nil ⟨ht, count, cursor, (same 11 (by decide)).trans v₁,
    (same 12 (by decide)).trans v₂,
    (same 6 (by decide)).trans v₃,
    (same 5 (by decide)).trans vx⟩

end VG.Proof.MillerRabin.X86

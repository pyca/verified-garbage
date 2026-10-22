module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrimePreparation
public import VerifiedGarbage.Proof.Dsa.X86.Generation.CompactInverseLayout
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Subspace
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.OutsFrame

/-! Lift the parent's negative inverse into the compact workspace header. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation
open VG.Proof.Mont VG.Proof.Mont.X86

theorem inverse_at {s : State} {base : Addr} {bytes len : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes)
    (layout : Spec.MillerRabin.Layout Spec.MillerRabin.compact s.mem (off base Layout.arithmetic) len)
    (inverse : (w32 s.mem (off base Layout.arithmetic) 256 * w32 s.mem base 0 + 1) % 2 ^ 32 = 0) :
    WP isa (.block ([.mov .ecx (.mem (VG.Impl.Mont.X86.sc 0))] ++
      enterArithmetic ++ compactInverse ++ leaveArithmetic)) s fun t =>
      Spec.MillerRabin.Layout Spec.MillerRabin.compact t.mem (off base Layout.arithmetic) len ∧
      Spec.Rsa.Mont.wOf t.mem (off base Layout.arithmetic) =
        Spec.Rsa.Mont.wOf s.mem (off base Layout.arithmetic) ∧
      ((word t.mem (off base Layout.arithmetic) 256).toNat *
        (word t.mem (off base Layout.arithmetic) 56).toNat + 1) % 2 ^ 64 = 0 ∧
      Frame [⟨off base Layout.arithmetic, 256⟩] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have fit : Layout.arithmetic + Layout.arithmeticBytes ≤ bytes := capacity
  unfold enterArithmetic
  simp only [List.cons_append, List.nil_append]
  refine wp_movS (readSrc_sc scr (d := 0) (by omega)) fun a A _ => ?_
  refine wp_addS rfl fun b B _ => ?_
  have pointer : b.gpr .edi = s.gpr .edi + BitVec.ofNat 32 Layout.arithmetic := by
    rw [B.gpr, A.other .edi (by decide)]
  have stack : b.gpr .esp = s.gpr .esp := (B.other .esp (by decide)).trans (A.other .esp (by decide))
  have mem : b.mem = s.mem := B.mem.trans A.mem
  have child : Scr (b.withRegions b.rd [⟨off base Layout.arithmetic, Layout.arithmeticBytes⟩])
      (off base Layout.arithmetic) Layout.arithmeticBytes :=
    workspace_slice scr fit (by unfold Layout.arithmetic; omega) pointer stack
      (List.mem_singleton_self _)
  have write : Covers [⟨off base Layout.arithmetic, Layout.arithmeticBytes⟩] b.wr := by
    rw [B.wr, A.wr]; exact workspace_slice_covers scr fit
  have ecx : b.gpr .ecx = s.mem.readW (off base 0) 32 := by
    rw [B.other .ecx (by decide), A.gpr]
  have work := compact_inverse_layout child (by decide : 264 ≤ Layout.arithmeticBytes)
    (by rw [State.withRegions_mem, mem]; exact layout)
    (by change (w32 b.mem (off base Layout.arithmetic) 256 * (b.gpr .ecx).toNat + 1) % 2 ^ 32 = 0
        rw [mem, ecx]; exact inverse)
  refine WP.block_append (WP.mono (workspace_wp work (Covers.append (Covers.refl _) write) write)
    fun c ⟨u, ⟨_, F, L, width, inv, K⟩, eq⟩ => ?_)
  subst eq
  unfold leaveArithmetic
  refine wp_subS rfl fun t T _ => WP.block_nil ?_
  have restored : t.gpr .edi = s.gpr .edi := by
    rw [T.gpr, State.withRegions_gpr, K.1 .edi (by decide), State.withRegions_gpr, pointer,
      BitVec.add_sub_cancel]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [T.mem]; exact L
  · rw [T.mem, ← mem]; exact width
  · rw [T.mem]; exact inv
  · rw [T.mem, ← mem]
    exact (Outs.of_outside (F.mono (o' := 0) (n' := 256) (by decide) (by decide))
      (List.mem_singleton_self _)).frame (by
        intro r hr; rw [List.mem_singleton.mp hr]; decide)
  · refine ⟨?_, ?_, ?_⟩
    · intro r hr
      by_cases di : r = .edi
      · subst di; exact restored
      · rw [T.other r di, State.withRegions_gpr, K.1 r (by revert hr; cases r <;> simp),
          State.withRegions_gpr, B.other r di, A.other r (by revert hr; cases r <;> simp)]
    · rw [T.rd, State.withRegions_rd, B.rd, A.rd]
    · rw [T.wr, State.withRegions_wr, B.wr, A.wr]

end VG.Proof.Dsa.X86.Generation

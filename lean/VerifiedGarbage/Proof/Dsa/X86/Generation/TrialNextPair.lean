module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialMachine

/-! Load a packed prime pair and advance its public table pointer. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Mont
open VG.Impl.Dsa.X86.Generation

theorem TrialMachine.next_pair {initial s : State} {base : Addr} {size offset : Nat} {sp : BitVec 32}
    {values : Nat → BitVec 32} (h : TrialMachine initial base size sp values s)
    (ptr : (values 2).toNat = (base.toNat + offset) % 2 ^ 32) (fit : offset + 4 ≤ size) :
    WP isa (.block trialNextPair) s fun t =>
      TrialMachine initial base size sp
        (fun j => if j = 2 then values 2 + 4 else
          if j = 4 then initial.mem.readW (off base offset) 32 else values j) t ∧
      t.gpr .ebx = initial.mem.readW (off base offset) 32 &&& 65535 := by
  unfold trialNextPair
  refine wp_movS (h.read (i := 2) (by decide)) fun u U _ => ?_
  have hu := h.of_keeps U.keeps (by decide) U.mem
  have p : Rt.PtrAt u base .eax offset := by rw [Rt.PtrAt, U.gpr]; exact ptr
  have read := Rt.readSrc_ptr hu.ws (d := 0) p (by omega)
  simp only [Nat.add_zero] at read
  rw [hu.word fit] at read
  refine wp_movS read fun v V _ => ?_
  have hv := hu.of_keeps V.keeps (by decide) V.mem
  refine WP.block_append (WP.mono (hv.store (i := 4) (by decide) .ebx) ?_)
  rintro w ⟨hw, K⟩
  rw [V.gpr] at hw
  refine wp_addS rfl fun x X _ => ?_
  have hx := hw.of_keeps X.keeps (by decide) X.mem
  have xp : x.gpr .eax = values 2 + 4 := by
    rw [X.gpr, K.1 .eax (by simp), V.other .eax (by decide), U.gpr]
  refine WP.block_append (WP.mono (hx.store (i := 2) (by decide) .eax) ?_)
  rintro y ⟨hy, K'⟩
  rw [xp] at hy
  refine wp_logicS (Or.inl rfl) rfl fun t T => WP.block_nil ?_
  refine ⟨hy.of_keeps T.keeps (by decide) T.mem, ?_⟩
  rw [T.gpr, K'.1 .ebx (by simp), X.other .ebx (by decide), K.1 .ebx (by simp), V.gpr]
  rfl

end VG.Proof.Dsa.X86.Generation

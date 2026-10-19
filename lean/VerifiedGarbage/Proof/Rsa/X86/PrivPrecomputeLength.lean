module

public import VerifiedGarbage.Proof.Rsa.X86.PrivStackWord

/-! # Computing the public packed-key length in native 32-bit argument slots -/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.X86.Wp VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86 VG.Proof.Mont.X86

theorem precomputeLength_value (k : Nat) (hk : k ≤ 1024) :
    ((BitVec.ofNat 32 k + 7) >>> 3) + ((BitVec.ofNat 32 k + 7) >>> 3) =
      BitVec.ofNat 32 (2 * Spec.Rsa.modulusWords k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Spec.Rsa.modulusWords]
  change (((k % 2 ^ 32 + 7) % 2 ^ 32 / 8) + ((k % 2 ^ 32 + 7) % 2 ^ 32 / 8)) % 2 ^ 32 =
    (2 * ((k + 7) / 8)) % 2 ^ 32
  omega

theorem precomputeLength_ok (s : State) {g : PrivGeometry} {bs : Fin 8 → List Byte}
    (h : PrivContext g bs s) {j : Nat} (hj : j < 18) :
    WP isa (.block (precomputeLength j)) s fun t =>
      PrivContext g bs t ∧
      t.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 (4 * j))
        (BitVec.ofNat 32 (2 * Spec.Rsa.modulusWords g.length)) ∧
      Frame [⟨byteAddr g.stack + BitVec.ofNat 64 (4 * j), 4⟩] s.mem t.mem ∧ Keeps [.eax] s t := by
  unfold precomputeLength incoming stackAt
  refine wp_ldm rfl (h.readArg (by decide : 3 < 20)) fun a A => ?_
  refine wp_addS rfl fun b B _ => ?_
  refine wp_shr (by decide) fun c C _ => ?_
  refine wp_addS rfl fun d D _ => ?_
  have Kd : Keeps [.eax] s d := A.keeps.trans (B.keeps.trans (C.keeps.trans D.keeps))
  have Md : d.mem = s.mem := D.mem.trans (C.mem.trans (B.mem.trans A.mem))
  have V : d.gpr .eax = BitVec.ofNat 32 (2 * Spec.Rsa.modulusWords g.length) := by
    rw [D.gpr, C.gpr, B.gpr, A.gpr, h.argumentValue (by decide : 3 < 20)]
    exact precomputeLength_value g.length h.valid.maxLength
  refine wp_stm (B := s.gpr .esp) (Kd.1 .esp (by decide))
    (by rw [Kd.2.2, h.address (by omega)]; exact h.inner.write (by simp only [VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega))
    fun t T => WP.block_nil ?_
  have M : t.mem = s.mem.writeW (byteAddr g.stack + BitVec.ofNat 64 (4 * j))
      (BitVec.ofNat 32 (2 * Spec.Rsa.modulusWords g.length)) := by
    rw [T.mem, V, Md, h.address (by omega)]
  have K : Keeps [.eax] s t := Kd.trans (T.keeps _)
  have F : Frame [⟨byteAddr g.stack + BitVec.ofNat 64 (4 * j), 4⟩] s.mem t.mem := by
    rw [M]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨h.after (F.sub ?_) K (K.1 .esp (by decide)), M, F, K⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨g.innerRegion, by simp [bodyWrites], Offset.sub_base _ (by simp only [VG.Impl.Rsa.X86.PrivChecked.frameBytes]; omega)⟩

end VG.Proof.Rsa.X86.PrivChecked

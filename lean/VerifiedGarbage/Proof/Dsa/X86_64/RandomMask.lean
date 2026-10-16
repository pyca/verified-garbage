module

public import VerifiedGarbage.Impl.Dsa.X86_64.Random
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-! Correctness of the sampler's fixed public-byte mask selection. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.MlKem.X86_64

def randomMaskValue (n : Nat) : BitVec 64 :=
  if n < 2 then 1 else if n < 4 then 3 else if n < 8 then 7 else
  if n < 16 then 15 else if n < 32 then 31 else if n < 64 then 63 else
  if n < 128 then 127 else 255

private theorem setReg_same (s : State) (r : Reg) : s.setReg r (s.gpr r) = s := by
  have h : (fun r' => if r' = r then s.gpr r else s.gpr r') = s.gpr := by
    funext r'
    split
    next he => rw [he]
    next _ => rfl
  simp only [State.setReg, h]

private theorem cmov_b_select (s : State) (d r : Reg) :
    execCmov .b d (.reg r) s = s.cf.map (fun b =>
      s.setReg d (if b then s.gpr r else s.gpr d)) := by
  cases hc : s.cf with
  | none => simp [execCmov, readSrc, eval, hc]
  | some b => cases b <;> simp [execCmov, readSrc, eval, hc, setReg_same]

theorem random_mask_ok (s : State) :
    WP isa Impl.Dsa.X86_64.Random.mask s fun t =>
      t.gpr .r8 = randomMaskValue (s.gpr .rax).toNat ∧ t.mem = s.mem ∧
      Keep [.rax, .rcx, .r8] s t := by
  refine WP.mono (WP.keep [.rax, .rcx, .r8] (Q := fun t =>
    t.gpr .r8 = randomMaskValue (s.gpr .rax).toNat ∧ t.mem = s.mem) ?_ rfl)
    fun _ ⟨h, hk⟩ => ⟨h.1, h.2, hk⟩
  unfold Impl.Dsa.X86_64.Random.mask Impl.Dsa.X86_64.Random.maskCode
    Impl.Dsa.X86_64.Random.maskStep
  xrun [List.append_assoc, List.cons_append, List.nil_append, randomMaskValue, BitVec.ult, cmov_b_select, decide_eq_true_eq]
  rfl

/-- The selected mask keeps exactly the significant bits of a nonzero byte. -/
theorem randomMaskValue_eq (n : Nat) (hpos : 0 < n) (hbound : n < 256) :
    randomMaskValue n = BitVec.ofNat 64 (2 ^ (n.log2 + 1) - 1) := by
  unfold randomMaskValue
  split
  · have hlog : n.log2 = 0 := (Nat.log2_eq_iff (by omega)).mpr ⟨by omega, by omega⟩
    rw [hlog]
    rfl
  ·
    split
    · have hlog : n.log2 = 1 := (Nat.log2_eq_iff (by omega)).mpr ⟨by omega, by omega⟩
      rw [hlog]
      rfl
    ·
      split
      · have hlog : n.log2 = 2 := (Nat.log2_eq_iff (by omega)).mpr ⟨by omega, by omega⟩
        rw [hlog]
        rfl
      ·
        split
        · have hlog : n.log2 = 3 := (Nat.log2_eq_iff (by omega)).mpr ⟨by omega, by omega⟩
          rw [hlog]
          rfl
        ·
          split
          · have hlog : n.log2 = 4 := (Nat.log2_eq_iff (by omega)).mpr ⟨by omega, by omega⟩
            rw [hlog]
            rfl
          ·
            split
            · have hlog : n.log2 = 5 := (Nat.log2_eq_iff (by omega)).mpr ⟨by omega, by omega⟩
              rw [hlog]
              rfl
            ·
              split
              · have hlog : n.log2 = 6 := (Nat.log2_eq_iff (by omega)).mpr ⟨by omega, by omega⟩
                rw [hlog]
                rfl
              ·
                have hlog : n.log2 = 7 := (Nat.log2_eq_iff (by omega)).mpr ⟨by omega, by omega⟩
                rw [hlog]
                rfl

end VG.Proof.Dsa.X86_64

module

public import VerifiedGarbage.Proof.Bignum.X86.PrivPre.Body
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset

/-! # `vg_rsa_private_precompute` on x86: a call from its body

A call of verified code, whose stack fits below the frame, from a state of
the body, with permissions narrowed to regions within those the body writes:
it returns in a state of the body, with the callee-saved registers, having
changed memory only within the regions it was given and the 100 bytes below
the frame, and in the callee's postcondition (`body_call`).
-/

@[expose] public section
namespace VG.Proof.Bignum.X86.PrivPre
open VG VG.X86 VG.Proof.Mont.X86

section
variable {s u : State}

theorem below_frame (A : PPABI s) (B : Body s u) {m : Nat} (hm : m ≤ 100) :
    Region.Sub (below (u.gpr .esp) m) ⟨bot s, 100⟩ := by
  have l := A.stackLow
  simp only [stackBytes] at l
  have e : below (u.gpr .esp) 100 = ⟨bot s, 100⟩ := by
    rw [B.sp]
    have := esp_off A (a := 196) (b := 0) (by decide) (by decide)
    simp only [BitVec.add_zero, Nat.sub_self, Nat.add_zero] at this
    simp only [below, Region.mk.injEq, and_true, Impl.Bignum.X86.PrivPre.frameBytes]
    rw [← this]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [sub_toNat (by rw [sub_toNat (by omega)]; omega), sub_toNat (by omega), sub_toNat (by omega)]
    omega
  rw [← e]
  refine below_sub hm ?_
  rw [B.sp, sub_toNat (by simp only [Impl.Bignum.X86.PrivPre.frameBytes]; omega)]
  simp only [Impl.Bignum.X86.PrivPre.frameBytes]; omega

theorem body_call {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hst : stackUse c ≤ 96) (hsp : NoSp c) (A : PPABI s) (B : Body s u) {rd wr : List Region}
    (hpre : k.pre (u.callEntry.withRegions rd wr)) (hc : Covers (rd ++ wr) (u.rd ++ u.wr)) (hw : Covers wr u.wr)
    (hsub : ∀ r ∈ wr, ∃ R ∈ bodyW s, r.Sub R) :
    WP isa (.call n c) u fun v => Body s v ∧ Keeps [.eax, .ecx, .edx] u v ∧
      Frame (wr ++ [⟨bot s, 100⟩]) u.mem v.mem ∧
      ∃ w : State, w.mem = v.mem ∧ (∀ r, r ≠ .esp → w.gpr r = v.gpr r) ∧
        k.post (u.callEntry.withRegions rd wr) w := by
  have l := A.stackLow
  simp only [stackBytes] at l
  have esp : (u.gpr .esp).toNat = (s.gpr .esp).toNat - 96 := by
    rw [B.sp, sub_toNat (by simp only [Impl.Bignum.X86.PrivPre.frameBytes]; omega)]; rfl
  refine VG.X86.WP.call hv hsp (by omega) hpre hc hw fun v rdv wrv regs F _ post => ?_
  have K : Keeps [.eax, .ecx, .edx] u v :=
    ⟨fun r hr => regs r (by cases r <;> simp_all [calleeSaved]), rdv, wrv⟩
  have F' : Frame (wr ++ [⟨bot s, 100⟩]) u.mem v.mem := F.sub fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_frame A B (by omega)⟩
  refine ⟨B.next (K.1 _ (by decide)) rdv wrv (F'.sub fun r hr => ?_), K, F', post⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact hsub r hr
  · obtain rfl := List.mem_singleton.mp hr
    exact ⟨topR s, by simp, Region.sub_prefix (by simp [stackBytes])⟩

end
end VG.Proof.Bignum.X86.PrivPre

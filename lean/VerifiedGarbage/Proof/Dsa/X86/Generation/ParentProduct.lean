module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.ParentConstants

/-! The optimized Montgomery callable inside the full generation workspace. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem parent_product {s : State} {base : Addr} {bytes n candidate out a b : Nat}
    (scr : Scr s base bytes) (capacity : montgomeryBytes ≤ bytes)
    (room : CallRoom (s.gpr .esp) base bytes) (C : ParentContext base n candidate s)
    (positive : 0 < n) (upper : n ≤ 48) (ho : out < 9) (ha : a < 9) (hb : b < 9) (ho0 : out ≠ 0)
    (reduced : val32 s.mem base (slot n b) (2 * n) < candidate) :
    WP isa (montgomery n out a b) s fun t =>
      ParentContext base n candidate t ∧
      val32 t.mem base (slot n out) (2 * n) < candidate ∧
      val32 t.mem base (slot n out) (2 * n) * 2 ^ (64 * n) % candidate =
        val32 s.mem base (slot n a) (2 * n) * val32 s.mem base (slot n b) (2 * n) % candidate ∧
      MontgomeryFrame base (s.gpr .esp) n out s t ∧ Keeps [.eax, .ecx, .edx] s t := by
  have parentRoom : CallRoom ((parentState base s).gpr .esp) base montgomeryBytes :=
    ⟨room.low, room.apart.sub_right (Region.sub_prefix capacity)⟩
  have modulus : val32 (parentState base s).mem base (slot n 0) (2 * n) = candidate := by
    rw [← wordsVal_eq_val32]; exact C.modulus.val
  have work := montgomery_ok C.scr parentRoom positive upper ho ha hb ho0
    (by rw [modulus]; exact C.inverse) (by rw [modulus]; exact reduced)
  have write := workspace_prefix_covers scr capacity
  refine WP.mono (workspace_wp work (Covers.append (Covers.refl _) write) write)
    fun t ⟨u, ⟨cs, rd, wr, F, bound, value⟩, eq⟩ => ?_
  subst eq
  rw [modulus] at bound value
  have Cu := montgomery_context_keep C parentRoom positive upper ho ho0 cs rd wr F
  have state : parentState base (u.withRegions s.rd s.wr) = u := by
    change u.withRegions s.rd [⟨base, montgomeryBytes⟩] = u
    have urd : u.rd = s.rd := rd
    have uwr : u.wr = [⟨base, montgomeryBytes⟩] := wr
    rw [← urd, ← uwr, State.withRegions_self]
  refine ⟨by change Context n candidate base montgomeryBytes (parentState base _); rw [state]; exact Cu,
    bound, value, F, ?_⟩
  exact ⟨fun r hr => cs r (by cases r <;> simp_all [calleeSaved]), rfl, rfl⟩

end VG.Proof.Dsa.X86.Generation

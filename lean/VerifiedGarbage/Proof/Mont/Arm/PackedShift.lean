module

public import VerifiedGarbage.Impl.Mont.ArmPacked
public import VerifiedGarbage.Proof.Mont.Arm.Words
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Fixed-offset quotient shift, with overlapping source and destination. -/

@[expose] public section
namespace VG.Proof.Mont.Arm.Packed
open VG VG.Arm VG.Proof.Mont VG.Proof.Mont.Arm VG.Impl.Mont.Arm.Packed
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str wp_mov op2_imm)

def shiftWords (acc k : Nat) : List Instr :=
  (List.range k).flatMap fun j => [.ldr .r5 .r12 (acc + 4 * j + 4), .str .r5 .r12 (acc + 4 * j)]

 theorem shiftWords_ok {s : State} {base : Addr} {size acc : Nat} (hs : Scr s base size) :
    ∀ k, acc + 4 * (k + 1) ≤ size →
    WP isa (.block (shiftWords acc k)) s fun t =>
      Outside base acc (4 * k) s.mem t.mem ∧
      val32 t.mem base acc k = val32 s.mem base (acc + 4) k ∧ Rest [.r5] s t
  | 0, _ => WP.block_nil ⟨Outside.refl _ _ _ _, rfl, Rest.refl _ _⟩
  | k + 1, fit => by
    have hn := hs.nowrap
    have eq : shiftWords acc (k + 1) = shiftWords acc k ++
        [.ldr .r5 .r12 (acc + 4 * k + 4), .str .r5 .r12 (acc + 4 * k)] := by
      simp only [shiftWords, List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rw [eq]
    refine VG.Proof.X25519.Arm.WP.append (shiftWords_ok hs k (by omega)) fun u ⟨out, val, rest⟩ => ?_
    have hu := hs.of_rest rest (by decide)
    refine wp_ldr (hu.off_lt (by omega)) (hu.ea (by omega)) (hu.read (by omega)) fun v uv => ?_
    have hv := hu.of_rest (uv.rest (ws := [.r5]) (by simp)) (by decide)
    refine wp_str (hv.off_lt (by omega)) (hv.ea (by omega)) (hv.write (by omega)) fun t vt => WP.block_nil ?_
    have mem : t.mem = u.mem.writeW (off base (acc + 4 * k)) (u.mem.readW (off base (acc + 4 * k + 4)) 32) := by
      rw [vt.mem, uv.mem, uv.gpr]
    have wr := writeW32_outside u.mem base (d := acc + 4 * k)
      (u.mem.readW (off base (acc + 4 * k + 4)) 32) (by omega)
    rw [← mem] at wr
    have low := wr.val32 (d := acc) (k := k) (by omega) (by omega)
    have source := out.w32 (d := acc + 4 * k + 4) (by omega) (by omega)
    have top : w32 t.mem base (acc + 4 * k) = w32 u.mem base (acc + 4 * k + 4) := by
      rw [mem, w32_write_self]
    refine ⟨(out.mono (Nat.le_refl _) (by omega)).trans (wr.mono (by omega) (by omega)), ?_,
      rest.trans ((uv.rest (by simp)).trans (vt.rest _))⟩
    rw [val32_succ, val32_succ, low, top, source, val]
    rw [show acc + 4 * k + 4 = acc + 4 + 4 * k by omega]

 theorem shift_ok {s : State} {base : Addr} {size acc n : Nat}
    (hs : Scr s base size) (fit : acc + 4 * (n + 2) ≤ size) :
    WP isa (.block (shift acc n)) s fun t =>
      Outside base acc (4 * (n + 2)) s.mem t.mem ∧
      val32 t.mem base acc (n + 2) = val32 s.mem base acc (n + 2) / 2 ^ 32 ∧ Rest [.r5] s t := by
  change WP isa (.block (shiftWords acc (n + 1) ++ _)) s _
  refine VG.Proof.X25519.Arm.WP.append (shiftWords_ok hs (n + 1) fit) fun u ⟨out, val, rest⟩ => ?_
  refine wp_mov (op2_imm (by decide)) fun v uv => ?_
  have k : Rest [.r5] s v := rest.trans (uv.rest (by simp))
  have hv := hs.of_rest k (by decide)
  refine wp_str (hv.off_lt (by omega)) (hv.ea (by omega)) (hv.write (by omega)) fun t vt => WP.block_nil ?_
  have mem : t.mem = u.mem.writeW (off base (acc + 4 * (n + 1))) (0 : BitVec 32) := by rw [vt.mem, uv.mem, uv.gpr]
  have hn := hs.nowrap
  have wr := writeW32_outside u.mem base (d := acc + 4 * (n + 1)) 0 (by omega)
  rw [← mem] at wr
  have low := wr.val32 (d := acc) (k := n + 1) (by omega) (by omega)
  have top : w32 t.mem base (acc + 4 * (n + 1)) = 0 := by rw [mem, w32_write_self]; rfl
  refine ⟨(out.mono (Nat.le_refl _) (by omega)).trans (wr.mono (by omega) (by omega)), ?_,
    k.trans (vt.rest _)⟩
  rw [show n + 2 = (n + 1) + 1 by omega, val32_succ, top, Nat.mul_zero, Nat.add_zero, low, val]
  rw [val32]
  have h := (s.mem.readW (off base acc) 32).isLt
  change val32 s.mem base (acc + 4) (n + 1) =
    (w32 s.mem base acc + 2 ^ 32 * val32 s.mem base (acc + 4) (n + 1)) / 2 ^ 32
  dsimp only [w32] at *
  omega

end VG.Proof.Mont.Arm.Packed

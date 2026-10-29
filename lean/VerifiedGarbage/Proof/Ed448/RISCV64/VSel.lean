module

import VerifiedGarbage.Proof.Ed448.RISCV64.BaseSel
public import VerifiedGarbage.Proof.Ed448.RISCV64.BaseStep
import VerifiedGarbage.Proof.X448.RISCV64.Mul
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ed448.RISCV64.ScalarBase
public import VerifiedGarbage.Proof.X448.RISCV64.Slots
import VerifiedGarbage.Proof.X25519.RISCV64.Pass

/-!
# Ed448 on RISCV64: selections as updates of the slots

`sel o q r` as an update of the slots `qs` (`selG`): `o` (a slot of the field
area, separate from the others or one of them) gets `pick sw x y` for the
elements `x` and `y` at `q` and `r`, which may be anywhere in the working
space, `q` even `o` itself.
-/

@[expose] public section

namespace VG.Proof.Ed448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed448.RISCV64 VG.Proof.X448.RISCV64
open VG.Proof.X25519.RISCV64 hiding V FS V_lt pass_ok limb_frame ACC_eq
open VG.Proof.X25519
open VG.Impl.X448.RISCV64 (ACC)
open VG.Spec.X448 (Fe)

section
variable {b : Addr}

theorem fs_pick {m m' : Mem} {o q r : Nat} {sw : Nat} (hsw : sw ≤ 1)
    (h : ∀ j < 14, limb m' b o j = VG.Proof.X25519.sel sw (limb m b q j) (limb m b r j)) :
    FS m' b o = pick sw (FS m b q) (FS m b r) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsw with rfl | rfl
  · rw [FS, V, val32_congr (g := limb m b q) fun j hj => h j hj]; rfl
  · rw [FS, V, val32_congr (g := limb m b r) fun j hj => h j hj]; rfl

theorem selG {o q r : Nat} {qs : List Nat} {v : Nat → Fe} {x y : Fe} (hq : Sep1 o qs = true)
    (ho : o + 56 ≤ ACC) (hqf : q + 56 ≤ 2048) (hrf : r + 56 ≤ 2048)
    (hoq : o + 56 ≤ q ∨ q + 56 ≤ o ∨ o = q) (hor : o + 56 ≤ r ∨ r + 56 ≤ o)
    (hq4 : q % 4 = 0) (hr4 : r % 4 = 0) {s : State} (hc : Ctx b s) {sw : Nat} (hsw : sw ≤ 1) (h11 : s.gpr .t0 = 0 - BitVec.ofNat 64 sw)
    (hS : SlotsOk s.mem b qs v) (hx : FS s.mem b q = x) (hy : FS s.mem b r = y) :
    WP isa (.block (sel o q r)) s fun s' => Rest [.a2, .a4] s s' ∧ Frame [FA b] s.mem s'.mem ∧
      SlotsOk s'.mem b (o :: qs) (upd v o (pick sw x y)) := by
  have hA := X448.RISCV64.ACC_eq
  refine WP.mono (sel_ok (b := b) (o := o) (q := q) (r := r) (by omega) hqf hrf hoq hor (sep1_o hq) hq4 hr4 hc hsw h11)
    fun s' h => ⟨h.rest, ?_, fun q' hq' => ?_⟩
  · exact h.frame.sub fun x hx => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hx]; exact Offset.sub_base _ (by omega)⟩
  · by_cases hqo : q' = o
    · subst hqo
      rw [upd_self, fs_pick hsw h.lo, hx, hy]
    · rw [upd_of_ne _ _ hqo]
      exact slots_after hq ho (frame_o (h.frame : Frame [⟨b + BitVec.ofNat 64 o, 56⟩] _ _)) hS
        ((List.mem_cons.mp hq').resolve_left hqo) hqo

end

end VG.Proof.Ed448.RISCV64

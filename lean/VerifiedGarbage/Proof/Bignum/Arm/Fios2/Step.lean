module

public import VerifiedGarbage.Impl.Bignum.Arm.Fios2
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
public import VerifiedGarbage.Proof.Bignum.Arm.Fios2.State
import VerifiedGarbage.Proof.Bignum.Arm.Fios2.Mac
import VerifiedGarbage.Proof.Framework.Block

/-! One step of the two-row scan: a word of row `i` and one of row `i + 1`. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios2
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_ldr wp_str)

/-- With `r0`, `r12` and `r4` at offsets `d`, `bb` and `mm`: the word at
`d + k + 8` plus row `i`'s products with the words at `bb + k + 8` and
`mm + k + 8` and row `i + 1`'s with those at `bb + k + 4` and `mm + k + 4`,
plus the carries, is the word stored at `d + k` and the new carries. -/
theorem step_ok (s : State) {base : BitVec 32} {size d bb mm k : Nat}
    (ws : Workspace s base size) (hk : k + 8 < 4096)
    (fd : d + k + 12 ≤ size) (fb : bb + k + 12 ≤ size) (fm : mm + k + 12 ≤ size)
    (pd : s.gpr .r0 = base + BitVec.ofNat 32 d)
    (pb : s.gpr .r12 = base + BitVec.ofNat 32 bb)
    (pm : s.gpr .r4 = base + BitVec.ofNat 32 mm) :
    WP isa (VG.Impl.Bignum.Arm.Fios2.step k) s fun t =>
      (t.gpr .r6).toNat + 2 ^ 32 * carries t =
        w32 s.mem (State.addr base) (d + k + 8) +
        (s.gpr .r1).toNat * w32 s.mem (State.addr base) (bb + k + 8) +
        (s.gpr .r2).toNat * w32 s.mem (State.addr base) (mm + k + 8) +
        (s.gpr .r9).toNat * w32 s.mem (State.addr base) (bb + k + 4) +
        (s.gpr .r10).toNat * w32 s.mem (State.addr base) (mm + k + 4) + carries s ∧
      t.mem = s.mem.writeW (off (State.addr base) (d + k)) (t.gpr .r6) ∧
      Rest [.r3, .r5, .r6, .r7, .r8, .r11] s t := by
  rw [VG.Impl.Bignum.Arm.Fios2.step, WP.seq_iff]
  refine wp_ldr (a := off (State.addr base) (d + (k + 8))) (by omega) (ws.ea pd (by omega))
    (ws.read (by omega)) fun u hu => WP.block_nil ?_
  have ru : Rest [.r3, .r5, .r6, .r7, .r8, .r11] s u := hu.rest (by simp)
  have wu := ws.congr ru.wr
  rw [WP.seq_iff]
  refine WP.mono (macAt_ok u wu ((ru.gpr .r12 (by simp)).trans pb) (by omega) (by omega)
    (c := .r7) (x := .r1) (by decide) (by decide) (by decide)) ?_
  rintro v ⟨vv, vm, rv⟩
  have r1 := rv.trans (Rest.refl _ _) |>.mono (ws' := [.r3, .r5, .r6, .r7, .r8, .r11]) (by simp)
  have kv : Rest [.r3, .r5, .r6, .r7, .r8, .r11] s v := ru.trans r1
  rw [WP.seq_iff]
  refine WP.mono (macAt_ok v (ws.congr kv.wr) ((kv.gpr .r4 (by simp)).trans pm) (by omega) (by omega)
    (c := .r8) (x := .r2) (by decide) (by decide) (by decide)) ?_
  rintro w ⟨ww, wm, rw'⟩
  have kw : Rest [.r3, .r5, .r6, .r7, .r8, .r11] s w := kv.trans (rw'.mono (by simp))
  rw [WP.seq_iff]
  refine WP.mono (macAt_ok w (ws.congr kw.wr) ((kw.gpr .r12 (by simp)).trans pb) (by omega) (by omega)
    (c := .r5) (x := .r9) (by decide) (by decide) (by decide)) ?_
  rintro x ⟨xv, xm, rx⟩
  have kx : Rest [.r3, .r5, .r6, .r7, .r8, .r11] s x := kw.trans (rx.mono (by simp))
  rw [WP.seq_iff]
  refine WP.mono (macAt_ok x (ws.congr kx.wr) ((kx.gpr .r4 (by simp)).trans pm) (by omega) (by omega)
    (c := .r11) (x := .r10) (by decide) (by decide) (by decide)) ?_
  rintro y ⟨yv, ym, ry⟩
  have ky : Rest [.r3, .r5, .r6, .r7, .r8, .r11] s y := kx.trans (ry.mono (by simp))
  have my : y.mem = s.mem := ym.trans (xm.trans (wm.trans (vm.trans hu.mem)))
  have py : y.gpr .r0 = base + BitVec.ofNat 32 d := (ky.gpr .r0 (by simp)).trans pd
  refine wp_str (a := off (State.addr base) (d + k)) (by omega)
    (by simpa only [Nat.add_assoc] using (ws.congr ky.wr).ea py (imm := k) (by omega))
    (by rw [ky.wr]; exact ws.write (by omega)) fun t ht => WP.block_nil ?_
  refine ⟨?_, by rw [ht.mem, my, ht.gpr], ky.trans (ht.rest _)⟩
  -- the carries and scalars through the four products
  have c8v : v.gpr .r8 = u.gpr .r8 := rv.gpr .r8 (by simp)
  have c5v : v.gpr .r5 = u.gpr .r5 := rv.gpr .r5 (by simp)
  have c11v : v.gpr .r11 = u.gpr .r11 := rv.gpr .r11 (by simp)
  have c7w : w.gpr .r7 = v.gpr .r7 := rw'.gpr .r7 (by simp)
  have c5w : w.gpr .r5 = v.gpr .r5 := rw'.gpr .r5 (by simp)
  have c11w : w.gpr .r11 = v.gpr .r11 := rw'.gpr .r11 (by simp)
  have c7x : x.gpr .r7 = w.gpr .r7 := rx.gpr .r7 (by simp)
  have c8x : x.gpr .r8 = w.gpr .r8 := rx.gpr .r8 (by simp)
  have c11x : x.gpr .r11 = w.gpr .r11 := rx.gpr .r11 (by simp)
  have c7y : y.gpr .r7 = x.gpr .r7 := ry.gpr .r7 (by simp)
  have c8y : y.gpr .r8 = x.gpr .r8 := ry.gpr .r8 (by simp)
  have c5y : y.gpr .r5 = x.gpr .r5 := ry.gpr .r5 (by simp)
  have s1 : u.gpr .r1 = s.gpr .r1 := ru.gpr .r1 (by simp)
  have s2 : v.gpr .r2 = s.gpr .r2 := (rv.gpr .r2 (by simp)).trans (ru.gpr .r2 (by simp))
  have s9 : w.gpr .r9 = s.gpr .r9 :=
    (rw'.gpr .r9 (by simp)).trans ((rv.gpr .r9 (by simp)).trans (ru.gpr .r9 (by simp)))
  have s10 : x.gpr .r10 = s.gpr .r10 :=
    (rx.gpr .r10 (by simp)).trans ((rw'.gpr .r10 (by simp)).trans
      ((rv.gpr .r10 (by simp)).trans (ru.gpr .r10 (by simp))))
  have u6 : (u.gpr .r6).toNat = w32 s.mem (State.addr base) (d + (k + 8)) := by
    rw [hu.gpr]
  have u7 : u.gpr .r7 = s.gpr .r7 := hu.other .r7 (by decide)
  have u8 : u.gpr .r8 = s.gpr .r8 := hu.other .r8 (by decide)
  have u5 : u.gpr .r5 = s.gpr .r5 := hu.other .r5 (by decide)
  have u11 : u.gpr .r11 = s.gpr .r11 := hu.other .r11 (by decide)
  rw [hu.mem, s1, u6, u7] at vv
  rw [vm, hu.mem, s2, c8v, u8] at ww
  rw [wm, vm, hu.mem, s9, c5w, c5v, u5] at xv
  rw [xm, wm, vm, hu.mem, s10, c11x, c11w, c11v, u11] at yv
  simp only [carries, ht.gpr, c7y, c7x, c7w, c8y, c8x, c5y]
  rw [Nat.mul_comm (s.gpr .r1).toNat, Nat.mul_comm (s.gpr .r2).toNat, Nat.mul_comm (s.gpr .r9).toNat,
    Nat.mul_comm (s.gpr .r10).toNat]
  simp only [Nat.add_assoc] at vv ww xv yv ⊢
  omega

end VG.Proof.Bignum.Arm.Fios2

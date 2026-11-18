module

public import VerifiedGarbage.Impl.Bignum.Arm.CrtPadModulus
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Bignum.Arm.CrtWorkspaceState
public import VerifiedGarbage.Impl.Bignum.Arm.CrtClearWide
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Bignum.Arm.CrtClearWide
import VerifiedGarbage.Proof.Bignum.Arm.RestoreBase
import VerifiedGarbage.Proof.Framework.Lit

/-! ### `Bignum.Arm.CrtPadModulusState`, which the modules that import this one used -/

section

/-! # Preserve the modulus workspace while clearing its extended comparison buffer -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem WorkspaceEq.of_outside {base : Addr} {size o n : Nat} {m m' : Mem}
    (fit : size < 2 ^ 64) (sep : size ≤ o) (h : Outside base o n m m') :
    WorkspaceEq base size m m' := by
  refine ⟨fun d k hk => Mem.read_congr ?_⟩
  intro i hi
  apply h
  rw [ofs_off base (by omega_using [fit, hk, hi])]
  omega_using [sep, hk, hi]

structure CrtPadInput (base : BitVec 32) (size len w d : Nat) (s : State) : Prop where
  workspace : Workspace s base size
  main : Workspace s base (8 * len)
  layout : CrtLayoutState base len w s.mem
  separate : 8 * len ≤ d
  fits : d + 4 * (4 * w + 2) ≤ size
  ptr : s.gpr .r0 = base
  link : s.mem.readW (off (State.addr base) 240) 32 = base + BitVec.ofNat 32 d
  stackRead : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4
  stackSep : Region.Disjoint ⟨State.addr s.sp, 4⟩ ⟨State.addr base, size⟩
  saved : s.mem.readW (State.addr s.sp) 32 = base

theorem crt_padClear_ready (s : State) {base : BitVec 32} {size len w d : Nat}
    (h : CrtPadInput base size len w d s) :
    WP isa (clearWide 240) s fun t => CrtPadInput base size len w d t ∧
      val32 t.mem (State.addr base) (d + 8 * w) (2 * w + 2) = 0 ∧
      Outside (State.addr base) d (4 * (4 * w + 2)) s.mem t.mem ∧
      Rest roundClobbers s t := by
  have small := h.layout.size
  have nowrap := h.workspace.nowrap
  have separate := h.separate
  have fits := h.fits
  refine WP.mono (crt_clearWide_ok s h.workspace (by omega_using [small, separate, fits]) (by omega_using [small, separate, fits]) (by decide) h.fits h.ptr
    (h.layout.nativeCount h.main) h.link h.stackRead h.stackSep h.saved) ?_
  rintro t ⟨zero, outside, frame, ptrT, rest⟩
  have eq := WorkspaceEq.of_outside (by omega_using [nowrap, separate, fits] : 8 * len < 2 ^ 64) h.separate outside
  have highZero : val32 t.mem (State.addr base) (d + 8 * w) (2 * w + 2) = 0 := by
    rw [show 4 * w + 2 = 2 * w + (2 * w + 2) by omega_using [], val32_append] at zero
    have positive : 0 < 2 ^ (32 * (2 * w)) := Nat.two_pow_pos _
    have high : 2 ^ (32 * (2 * w)) * val32 t.mem (State.addr base) (d + 4 * (2 * w)) (2 * w + 2) = 0 := by omega_using [zero]
    rcases Nat.mul_eq_zero.mp high with bad | good
    · omega
    · simpa only [show 4 * (2 * w) = 8 * w by omega_using []] using good
  exact ⟨⟨h.workspace.congr rest.wr, h.main.congr rest.wr, h.layout.congr eq,
    h.separate, h.fits, ptrT, (eq.word (by omega_using [small])).trans h.link,
    by rw [rest.rd, rest.wr, rest.sp]; exact h.stackRead,
    by rw [rest.sp]; exact h.stackSep, saved_base_kept frame h.stackSep h.saved rest.sp⟩,
    highZero, outside, rest⟩

end VG.Proof.Bignum.Arm

end

end

/-! # Select the public destination and modulus array for padding -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm.Crt VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_ldr wp_mov op2_imm)

theorem crt_padModulusArgs_ok (s : State) {base dst : BitVec 32} {size : Nat}
    (ws : Workspace s base size) (fit : 244 ≤ size) (ptr : s.gpr .r0 = base)
    (link : s.mem.readW (off (State.addr base) 240) 32 = dst) (operand : Fin 8 := 0) :
    WP isa (.block (padModulusArgs operand)) s fun t => t.gpr .r4 = dst ∧ t.gpr .r2 = BitVec.ofNat 32 operand.val ∧
      t.mem = s.mem ∧ Rest [.r2, .r4] s t := by
  have enc : ∀ i : Fin 8, encodable (BitVec.ofNat 32 i.val) = true := by decide
  unfold padModulusArgs
  refine wp_ldr (a := off (State.addr base) 240) (by decide)
    (by rw [ptr]; exact addr_add (by have := ws.nowrap; omega_using [fit, this])) (ws.read fit) fun u h => ?_
  refine wp_mov (op2_imm (enc operand)) fun t j => WP.block_nil ?_
  exact ⟨(j.other .r4 (by decide)).trans (h.gpr.trans link), j.gpr,
    j.mem.trans h.mem, (h.rest (by simp)).trans (j.rest (by simp))⟩

end VG.Proof.Bignum.Arm

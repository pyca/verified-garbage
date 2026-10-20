module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Proof.Rsa.Arm.RvKS

import VerifiedGarbage.Proof.Rsa.Arm.RvMmul2
import VerifiedGarbage.Proof.Rsa.Arm.RvOps
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # `vg_rsa_recover_primes` on ARMv7: header words on a stage

`KS.ldrSlot`, `KS.strSlot`: loads and stores of the header words a stage
records. -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Rsa.Arm.Recover VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm

section
variable {P : RP} {σ s : State} {A : Nat → Nat} {live : List Nat} {AW : Nat → Nat} {liveW : List Nat}
  {V : Nat → Nat} {ls : List Nat}

/-- `ldr r, [r8, #d]` of a recorded header word. -/
theorem KS.ldrSlot {d : Nat} {r : Reg} {v N : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z v N)
    (hd : d ∈ ls) (hr : r ∉ [.r7, .r8, .r9]) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live AW liveW V ls t → Ws t P.B P.Z v N → Upd s t r (BitVec.ofNat 32 (V d)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (.ldr r .r8 d :: rest)) s Q := by
  refine wp_ldrSlot hv (h.ls_ok d hd).1 fun t u => ?_
  have e : s.mem.readW (off (State.addr P.B) d) 32 = BitVec.ofNat 32 (V d) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, ← h.sl d hd, Nat.mod_eq_of_lt (BitVec.isLt _)]
  rw [e] at u
  have h7 : r ≠ .r7 := fun e => hr (by simp [e])
  have h8 : r ≠ .r8 := fun e => hr (by simp [e])
  have h9 : r ≠ .r9 := fun e => hr (by simp [e])
  exact k t (h.of_rest (u.rest (ws := [r]) (by simp)) u.mem (by simpa using h8.symm))
    (hv.of_upd u h7 h8 h9) u

/-- `str r, [r8, #d]`: the header word `d := r`. -/
theorem KS.strSlot {d : Nat} {r : Reg} {v N : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z v N)
    (hd : SlotOk d) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, KS P σ A live AW liveW (upd V d (s.gpr r).toNat) (d :: ls) t → Ws t P.B P.Z v N →
      t.gpr = s.gpr → t.z = s.z → WP isa (.block rest) t Q) :
    WP isa (.block (.str r .r8 d :: rest)) s Q := by
  have hz := hdr_Z h.sizes
  have hin : InRegions s.wr (State.addr (s.gpr .r8 + BitVec.ofNat 32 d)) 4 := by
    rw [slot_addr hv (by have := hd.1; omega)]; exact hv.write (by have := hd.1; omega)
  refine WP.cons (exec_str (by have := hd.1; simp only [hdr] at this; omega) hin) ?_
  have u : Mupd s { s with mem := s.mem.writeW (State.addr (s.gpr .r8 + BitVec.ofNat 32 d)) (s.gpr r) }
      (s.mem.writeW (off (State.addr P.B) d) (s.gpr r)) :=
    ⟨rfl, by rw [slot_addr hv (by have := hd.1; omega)], rfl, rfl, rfl⟩
  have kt : Keep P.B v [] [d] s.mem (s.mem.writeW (off (State.addr P.B) d) (s.gpr r)) :=
    keep_write _ _ (by simp) (by have := hd.1; simp only [hdr] at this; omega)
  rw [← u.mem] at kt
  exact k _ (h.slot1 kt hd (by rw [u.gpr, h.r8]) u.sp u.rd u.wr (by rw [u.mem, slot_write_self]))
    (hv.of_mupd u) u.gpr rfl

/-- A step that changes registers but `r7`–`r9` and nothing else. -/
theorem KS.reg {t : State} {v N : Nat} (h : KS P σ A live AW liveW V ls s) (hv : Ws s P.B P.Z v N) {rs : List Reg}
    (r : Rest rs s t) (m : t.mem = s.mem) (h7 : .r7 ∉ rs := by decide) (h8 : .r8 ∉ rs := by decide)
    (h9 : .r9 ∉ rs := by decide) :
    KS P σ A live AW liveW V ls t ∧ Ws t P.B P.Z v N :=
  ⟨h.of_rest r m h8, hv.rest r h7 h8 h9⟩

end

end VG.Proof.Rsa.Arm.Recover

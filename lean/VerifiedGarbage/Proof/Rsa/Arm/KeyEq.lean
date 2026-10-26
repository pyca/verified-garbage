module

public import VerifiedGarbage.Proof.Rsa.Arm.KeyOps
import VerifiedGarbage.Proof.Rsa.Arm.KeyEqContext
import VerifiedGarbage.Proof.Rsa.Arm.KeyEqNormalize
import VerifiedGarbage.Proof.Rsa.InverseArithmetic
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PlainSimp
import Batteries.Tactic.Alias

/-! Compare packed arrays in one read-only pass, preserving the existing scratch contract. -/

@[expose] public section
namespace VG.Proof.Rsa.Arm.Keys
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.Bignum.Arm VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm

alias borrow_iff := VG.Proof.Rsa.borrow_iff

theorem eqS_ok {s : State} {B : BitVec 32} {Z w N d a b t : Nat} (h : Ws s B Z w N)
    (_ht : t < N) (ha : a < N) (hb : b < N) (hN : N ≤ 256) (_hta : t ≠ a) (_htb : t ≠ b)
    (hd : d + 4 ≤ hdr) :
    WP isa (eqS d a b t) s fun u => Ws u B Z w N ∧ Keep B w [t] [sT, d] s.mem u.mem ∧
      slot u.mem B d = (if num s.mem B w a = num s.mem B w b then 1 else 0) ∧ Rest opRegs s u := by
  rw [eqS, WP.seq_iff]
  simp only [List.append_assoc]
  refine ptr_ok h (by decide) (by omega) fun s1 first rest1 mem1 h1 => ?_
  refine ptr_ok h1 (by decide) (by omega) fun s2 second rest2 mem2 h2 => ?_
  refine wp_mov (op2_reg _ _) fun s3 u3 => ?_
  have h3 := h2.of_upd u3 (by decide) (by decide) (by decide)
  refine wp_mov (op2_imm (by decide)) fun s4 u4 => WP.block_nil ?_
  have h4 := h3.of_upd u4 (by decide) (by decide) (by decide)
  have pa : s4.gpr .r0 = B + BitVec.ofNat 32 (arr w a) := by
    rw [u4.other .r0 (by decide), u3.other .r0 (by decide), rest2.gpr .r0 (by decide), first]
  have pb : s4.gpr .r1 = B + BitVec.ofNat 32 (arr w b) := by
    rw [u4.other .r1 (by decide), u3.other .r1 (by decide), second]
  have pc : s4.gpr .lr = BitVec.ofNat 32 w := by
    rw [u4.other .lr (by decide), u3.gpr, h2.r9]
  have pz : s4.gpr .r2 = 0 := u4.gpr
  have mem4 : s4.mem = s.mem := u4.mem.trans (u3.mem.trans (mem2.trans mem1))
  have rest4 : Rest opRegs s s4 :=
    (rest1.mono (by simp)).trans ((rest2.mono (by simp)).trans
      ((u3.rest (by simp)).trans (u4.rest (by simp))))
  refine WP.seq (WP.mono (compareWords_ok s4 (h4.compareCtx ha hb) h.wpos pa pb pc pz) ?_)
  intro u inv
  have hu := h4.rest inv.rest (by decide) (by decide) (by decide)
  have same : u.gpr .r2 = 0 ↔ num s.mem B w a = num s.mem B w b := by
    rw [inv.equal, mem4]
    exact h.compareEqual ha hb
  rw [WP.block_append_iff]
  refine WP.mono (eqNormalize_ok u) ?_
  rintro v ⟨⟨bit, memV⟩, restV⟩
  have hv := hu.rest restV (by decide) (by decide) (by decide)
  refine wp_strSlot hv hd fun out store => WP.block_nil ?_
  refine ⟨hv.of_mupd store, ?_, ?_, ?_⟩
  · rw [store.mem, memV, inv.mem, mem4]
    exact keep_write _ _ (by simp) (by simp only [hdr] at hd; omega)
  · rw [store.mem, slot_write_self, bit]
    by_cases eq : num s.mem B w a = num s.mem B w b
    · rw [ite_eq_left (same.mpr eq), ite_eq_left eq]; rfl
    · rw [ite_eq_right (fun z => eq (same.mp z)), ite_eq_right eq]; rfl
  · exact rest4.trans ((inv.rest.mono (by simp [opRegs])).trans
      ((restV.mono (by simp [opRegs])).trans (store.rest _)))

end VG.Proof.Rsa.Arm.Keys

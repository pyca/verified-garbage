module
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Mont2
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.St

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Mont7
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Mont3
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Taint6
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rsa.Arm.RvLoads

/-! # A candidate on ARMv7: the Montgomery forms of 1 and −1 (`montB_vp`)

`St.pctxClr`: after a multiplication, the context and the top words of its
result's key array cleared; `montB`: `R mod c` (from `1 · R²`) into the key
arrays `mBase + 1` and `mBase + 9`, and `c − R mod c` into `mBase + 10`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Keeps Operand)
open VG.Proof.Rsa.Arm.Recover (VP sub32)

section
variable {P : CP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

/-- After a multiplication into array `j`: the context, and `[mBase + j]`'s
top words cleared, so that its key number is Montgomery multiplication's. -/
theorem St.pctxClr {j : Nat} (cert : Cert (.block (clrTop (mBase + j)))) (hj : j < 8) (hjM : MOk (mBase + j))
    {x : State → Nat} :
    VP (fun σ s => (E σ ∧ KS P σ (A σ) L (V σ) LS s) ∧ MS P σ s ∧ numAt s.mem (State.addr P.M0) P.w j = x σ)
      (.block (ctx ++ clrTop (mBase + j)))
      (fun σ s => St P E (fun σ => upd (A σ) (mBase + j) (x σ)) ((mBase + j) :: L) V LS σ s ∧ MS P σ s) := by
  rw [show ctx ++ clrTop (mBase + j) = [.ldrSp .r8 aoS] ++ (ctxW ++ clrTop (mBase + j)) from rfl]
  refine VP.block_append (G := fun σ s => ((E σ ∧ KS P σ (A σ) L (V σ) LS s) ∧ MS P σ s ∧
    numAt s.mem (State.addr P.M0) P.w j = x σ) ∧ s.gpr .r8 = P.B) ?_ ?_
  · show VP _ (.block ([(Reg.r8, aoS)].map fun p => Instr.ldrSp p.1 p.2)) _
    refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨⟨e, k⟩, m, n⟩ => ?_
    · rw [h₁.1.2.sp, h₁.1.2.pre.sp, h₂.1.2.sp, h₂.1.2.pre.sp]
    refine k.ldrSp (o := aoS) (by decide) fun t u => WP.block_nil ⟨⟨⟨e, k.of_rest (u.rest (ws := [.r8])
      (by simp)) u.mem⟩, ⟨m.toMSp.of_same u.mem u.sp u.rd u.wr, by rw [u.mem]; exact m.stride⟩,
      by rw [u.mem]; exact n⟩, by rw [u.gpr, k.pre.aS]⟩
  refine VP.block_append (G := fun σ s => (((E σ ∧ KS P σ (A σ) L (V σ) LS s) ∧ MS P σ s ∧
    numAt s.mem (State.addr P.M0) P.w j = x σ) ∧ Ws s P.B P.Z P.W nArr) ∧ s.gpr .r8 = P.B) ?_ ?_
  · refine VP.taint [.r8] ctxW_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s ⟨⟨⟨e, k⟩, m, n⟩, r8⟩ => ?_
    · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]
    have pre := k.pre
    have hz := pre.hdr_Z
    have hf := pre.fS
    have ea : State.addr (s.gpr .r8 + BitVec.ofNat 32 16) = off (State.addr P.B) 16 := by
      rw [r8]; exact addr_add (by simp only [hdr] at hz; omega)
    have rd : InRegions (s.rd ++ s.wr) (off (State.addr P.B) 16) 4 :=
      ⟨P.rS, List.mem_append_right _ (by rw [k.wr]; exact pre.rS_mem),
        Offset.contains_base _ (by simp only [hdr] at hz; omega) (by omega)⟩
    simp only [ctxW, stride, List.cons_append, List.nil_append]
    refine wp_ldr (by decide) ea rd fun s2 u2 => ?_
    refine wp_dp (op2_imm (by decide)) fun s3 u3 => wp_mov (op2_lsl (by decide)) fun s4 u4 => WP.block_nil ?_
    have m4 : s4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem]
    have r4 : Rest [.r7, .r9] s s4 := (u2.rest (by simp)).trans ((u3.rest (by simp)).trans (u4.rest (by simp)))
    have wl := pre.wle
    have e9 : s4.gpr .r9 = BitVec.ofNat 32 P.W := by
      rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr]
      apply BitVec.eq_of_toNat_eq
      have := k.cnt
      simp only [slot, w32] at this
      rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have e7 : s4.gpr .r7 = BitVec.ofNat 32 (S P.W) := by
      rw [u4.gpr, u3.gpr, dpVal, u2.gpr]
      apply BitVec.eq_of_toNat_eq
      have := k.cnt
      simp only [slot, w32] at this
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_add, this, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      simp only [show (2 : BitVec 32).toNat = 2 from rfl, S]
      omega
    have e8 : s4.gpr .r8 = P.B := by rw [r4.gpr _ (by decide), r8]
    have k4 := k.of_rest r4 m4
    exact ⟨⟨⟨⟨e, k4⟩, ⟨m.toMSp.of_same m4 r4.sp r4.rd r4.wr, by rw [m4]; exact m.stride⟩, by rw [m4]; exact n⟩,
      k4.ws e7 e8 e9⟩, e8⟩
  · refine VP.kv cert (fun _ _ h => h.1.2) fun σ s ⟨⟨⟨⟨e, k⟩, m, n⟩, hw⟩, _⟩ => ?_
    have pre := k.pre
    have hW := pre.W_eq
    rw [← List.append_nil (clrTop (mBase + j))]
    refine clrTopO_ok hw (by simp only [mBase, nArr]; omega) (by decide) (by omega) fun t ht out nt rest => WP.block_nil ?_
    have hS := pre.S_eq
    have fit := pre.fitZ (j := mBase + j) (by simp only [mBase, nArr]; omega)
    have kp : Keep P.B P.W [mBase + j] [] s.mem t.mem :=
      Keep.of_arr (d := 4 * (P.W - 2)) out (by simp only [S]; omega) (by simp)
    have v : num t.mem P.B P.W (mBase + j) = x σ := by
      rw [nt, ← pre.numAt_val32, n]
    exact ⟨⟨e, k.write1 kp (by simp only [mBase, nArr]; omega) (by simp) rest.sp rest.rd rest.wr v (by simp), ht⟩,
      m.of_keep pre kp (by simp only [List.mem_singleton]; rintro _ rfl; exact hjM) (by simp) rest.sp rest.rd rest.wr
        (k.sp.trans pre.sp)⟩

end

end VG.Proof.RsaKeyGen.Arm.Cand

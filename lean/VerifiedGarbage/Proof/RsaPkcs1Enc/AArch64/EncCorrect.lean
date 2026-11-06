module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncTail
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCall
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncEntry
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-!
# RSAES-PKCS1-v1_5 encryption on AArch64: correctness

Pieces of the proof of correctness: the state after `setup`
(`setup_inv`), the mask from the state after the call (`maskArgs_inv`), the
postcondition from the bytes the mask left (`result_ok`), and the pops.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Encrypt

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Rsa.bytesAt m p n).length = n := by
  simp [Spec.Rsa.bytesAt]

theorem encrypt_eq {nB eB M PS : List Byte} (hm : M.length + 11 ≤ nB.length)
    (hps : PS.length = nB.length - M.length - 3) :
    Spec.RsaPkcs1Enc.encrypt nB eB M PS =
      if PS.all (· != 0) then Spec.Rsa.publicOpChecked nB eB (Spec.RsaPkcs1Enc.encode M PS) else none := by
  simp only [Spec.RsaPkcs1Enc.encrypt, hm, hps, true_and]

theorem setup_inv {P : Nat} {s : State} {X : List Region} {al : Nat} {t : State}
    (hc : Ctx (lay P s X al) s.gpr s.v s.mem t) (hs : Setup (lay P s X al) s.gpr t) :
    PsInv (lay P s X al) s.gpr s.v s.mem 0 t :=
  ⟨hc, ⟨hs.x0, hs.x1, hs.x2, hs.x3, hs.x4, hs.x5, hs.x6, hs.x7⟩, by rw [hs.x11, BitVec.add_zero],
    by rw [hs.x12, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq], by rw [hs.x13, Nat.add_zero],
    by rw [hs.x14]; rfl, hs.x15, hs.b0, hs.b1, fun i hi => absurd hi (Nat.not_lt_zero _)⟩

theorem regsOf (P : Nat) (s : State) {X : List Region} {al : Nat} : RegsOf (lay P s X al) s.gpr := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `maskArgs`, from the state after the call. -/
theorem maskArgs_inv {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (h : CalledF L g vv m₀ t) :
    WP isa (.block maskArgs) t (MaskInv L g vv m₀ t.mem (t.gpr .x0 &&& ~~~zmask (Spec.Rsa.bytesAt m₀ L.ps L.pl.toNat))
      (zmask (Spec.Rsa.bytesAt m₀ L.ps L.pl.toNat)) 0) := by
  have hc := h.ctx
  refine WP.mono (maskArgs_ok (by rw [hc.sp]; exact hc.inFrR (by decide)) (by rw [hc.sp]; exact hc.inFrR (by decide))
    (by rw [hc.sp]; exact hc.inFrR (by decide))) fun w hw => ?_
  have go : ∀ r, r ≠ .x0 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 → r ≠ .x15 → w.gpr r = t.gpr r := hw.other
  refine ⟨hc.regs hw.rd hw.wr hw.sp hw.mem hw.v fun r hr _ => go r (mem_ne hr (by decide)) (mem_ne hr (by decide))
    (mem_ne hr (by decide)) (mem_ne hr (by decide)) (mem_ne hr (by decide)) (mem_ne hr (by decide)),
    by rw [hw.x0, hc.sp, h.z], by rw [hw.x11, hc.sp, hc.kept.out, BitVec.add_zero],
    by rw [hw.x12, hc.sp, hc.kept.k, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq],
    by rw [hw.x13, hc.sp, Nat.add_zero], by rw [hw.x14, hc.sp, h.z], hw.x15,
    fun i hi => absurd hi (Nat.not_lt_zero _), fun i _ _ => by rw [hw.mem]⟩

/-- The postcondition, from the bytes the mask left. -/
theorem result_ok {P : Nat} {s : State} (hml : (s.gpr .x7).toNat + 11 ≤ (s.gpr .x3).toNat)
    (hpl : (stackArg s 1).toNat = (s.gpr .x3).toNat - (s.gpr .x7).toNat - 3) {y : Mem} {r : BitVec 64} {t : State}
    (hy : Spec.Rsa.written y (s.gpr .x0) (s.gpr .x3).toNat (r.setWidth 32)
      (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
        (Spec.RsaPkcs1Enc.encode (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat))))
    (hx0 : t.gpr .x0 = r &&& ~~~zmask (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat))
    (hout : ∀ i < (s.gpr .x3).toNat, t.mem (s.gpr .x0 + BitVec.ofNat 64 i) =
      mb (y (s.gpr .x0 + BitVec.ofNat 64 i)) (zmask (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat))) :
    (encK P).post s t := by
  simp only [encK]
  rw [encrypt_eq (by rw [bytesAt_length, bytesAt_length]; exact hml)
    (by rw [bytesAt_length, bytesAt_length, bytesAt_length]; exact hpl)]
  have hb : Spec.Rsa.bytesAt t.mem (s.gpr .x0) (s.gpr .x3).toNat =
      (Spec.Rsa.bytesAt y (s.gpr .x0) (s.gpr .x3).toNat).map
        fun b => mb b (zmask (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)) := by
    simp only [Spec.Rsa.bytesAt, List.map_map]
    exact List.map_congr_left fun i hi => hout i (List.mem_range.mp hi)
  rw [hx0]
  by_cases hz : (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat).all (· != 0) = true
  · have z0 : zmask (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat) = 0 := by
      simp only [zmask, hz, ite_true]
    simp only [hz, ite_true]
    rw [z0, and_not_zero]
    rw [z0] at hb
    simp only [mb_zero, List.map_id'] at hb
    cases hq : Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .x4) (s.gpr .x5).toNat)
        (Spec.RsaPkcs1Enc.encode (Spec.Rsa.bytesAt s.mem (s.gpr .x6) (s.gpr .x7).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)) with
    | none => rw [hq] at hy; exact ⟨hy.1, hb.trans hy.2⟩
    | some c => rw [hq] at hy; exact ⟨hy.1, hb.trans hy.2⟩
  · have z1 : zmask (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat) = BitVec.allOnes 64 := by
      simp only [zmask, hz, ite_false, Bool.false_eq_true]
    simp only [hz, Bool.false_eq_true, ite_false]
    rw [z1, and_not_ones]
    rw [z1] at hb
    simp only [mb_ones] at hb
    refine ⟨rfl, ?_⟩
    rw [hb, List.map_const', bytesAt_length]

theorem popped_mem (r : Reg) (s : State) : (popped r s).mem = s.mem := rfl
theorem popped_sp (r : Reg) (s : State) : (popped r s).sp = s.sp + 16 := rfl
theorem popped_v (r : Reg) (s : State) : (popped r s).v = s.v := rfl
theorem popped_gpr_self (r : Reg) (s : State) : (popped r s).gpr r = s.mem.readW s.sp 64 := by
  show (s.write .x r (s.mem.read s.sp 8)).gpr r = _
  rw [RegUpd.gpr_write_self, read8]; rfl
theorem popped_gpr_ne {r x : Reg} (s : State) (h : x ≠ r) : (popped r s).gpr x = s.gpr x := by
  show (s.write .x r (s.mem.read s.sp 8)).gpr x = _
  rw [RegUpd.gpr_write_of_ne _ _ _ h]
theorem freed_mem (n : Nat) (s : State) : (freed n s).mem = s.mem := rfl
theorem freed_sp (n : Nat) (s : State) : (freed n s).sp = s.sp + BitVec.ofNat 64 n := rfl
theorem freed_v (n : Nat) (s : State) : (freed n s).v = s.v := rfl
theorem freed_gpr (n : Nat) (s : State) : (freed n s).gpr = s.gpr := rfl

end VG.Proof.RsaPkcs1Enc.AArch64.Enc

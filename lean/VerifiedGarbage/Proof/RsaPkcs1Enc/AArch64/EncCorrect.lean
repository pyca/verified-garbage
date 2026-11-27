module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCall
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncEntry
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncLay
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Bytes
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `RsaPkcs1Enc.AArch64.EncTail`, which this module and modules that import it used -/

section

/-!
# RSAES-PKCS1-v1_5 encryption on AArch64: the mask

After the call, `maskArgs` masks the result with the zero test of `PS`, and
`maskLoop` masks each byte of `out` with it, overwriting `EM` with zeros
(`maskLoop_ok`): if `PS` has a zero byte, `out` is zeros and the result 0.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Encrypt

/-- A byte masked by `z`: `b` if `z` is zero, zero if it is all ones. -/
def mb (b : Byte) (z : BitVec 64) : Byte := ((b.setWidth 64 &&& ~~~z)).setWidth 8

theorem mb_zero (b : Byte) : mb b 0 = b := by
  simp [mb]
  have : (255#8 : BitVec 8) = BitVec.allOnes 8 := by decide
  rw [this, BitVec.and_allOnes]

theorem mb_ones (b : Byte) : mb b (BitVec.allOnes 64) = 0 := by
  simp [mb]

theorem and_not_zero (r : BitVec 64) : r &&& ~~~(0 : BitVec 64) = r := by
  have : ~~~(0 : BitVec 64) = BitVec.allOnes 64 := by decide
  rw [this, BitVec.and_allOnes]

theorem and_not_ones (r : BitVec 64) : r &&& ~~~(BitVec.allOnes 64) = 0 := by simp

/-- During the masking loop, after `j` bytes. -/
structure MaskInv (L : Lay) (g : Reg → BitVec 64) (vv : VReg → BitVec 128) (m₀ : Mem) (y : Mem) (r : BitVec 64)
    (z : BitVec 64) (j : Nat) (t : State) : Prop where
  ctx : Ctx L g vv m₀ t
  x0 : t.gpr .x0 = r
  x11 : t.gpr .x11 = L.out + BitVec.ofNat 64 j
  x12 : t.gpr .x12 = BitVec.ofNat 64 (L.k.toNat - j)
  x13 : t.gpr .x13 = L.Q + BitVec.ofNat 64 (oEM + j)
  x14 : t.gpr .x14 = z
  x15 : t.gpr .x15 = 0
  done : ∀ i < j, t.mem (L.out + BitVec.ofNat 64 i) = mb (y (L.out + BitVec.ofNat 64 i)) z
  todo : ∀ i, j ≤ i → i < L.k.toNat → t.mem (L.out + BitVec.ofNat 64 i) = y (L.out + BitVec.ofNat 64 i)

namespace Ctx

variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t t' : State}

/-- Code that writes memory in `out` and in the inner frame apart from the
kept words. -/
theorem store' (hc : Ctx L g vv m₀ t) (hL : L.Ok) {rs : List Region} (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.sp = t.sp) (hv : t'.v = t.v) (hg : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r)
    (hf : Frame rs t.mem t'.mem)
    (hin : ∀ r ∈ rs, Region.Sub r L.OUT ∨
      ∃ d, 32 ≤ d ∧ d + r.len ≤ 1072 ∧ r.base = L.Q + BitVec.ofNat 64 d) :
    Ctx L g vv m₀ t' := by
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp,
    fun r hr hr' => (hg r hr hr').trans (hc.cs r hr hr'), fun r hr => by rw [hv]; exact hc.vs r hr,
    hc.kept.frame hf fun d hd R hR => ?_, hc.frame.trans (Frame.sub hf fun r hr => ?_)⟩
  · rcases hin R hR with hs | ⟨d', h₁, h₂, hb⟩
    · exact hL.kept_buf hd (.inl hs)
    · obtain ⟨b, n⟩ := R
      simp only at hb h₂; subst hb
      unfold keptOff at hd
      exact hL.fr_sep (by omega_using [hd, h₁, h₂]) (by omega_using [hd]) (by omega_using [h₂])
  · rcases hin r hr with hs | ⟨d', h₁, h₂, hb⟩
    · exact ⟨L.OUT, by simp, hs⟩
    · obtain ⟨b, n⟩ := r
      simp only at hb h₂; subst hb
      exact ⟨L.STK, by simp, Lay.Ok.sub_stk (by omega_using [h₂])⟩

end Ctx

theorem maskLoop_ok {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ y : Mem}
    {r z : BitVec 64} {t : State} (h : MaskInv L g vv m₀ y r z 0 t) :
    WP isa maskLoop t (MaskInv L g vv m₀ y r z L.k.toNat) := by
  have hnQ := hL.nQ
  have hk := hL.k1024
  have hk64 := hL.k64
  have hbO := hL.bO
  refine Bytes.count_loop (by omega_using [hk64]) (MaskInv L g vv m₀ y r z) (fun j hj u hu => ?_) h
  have hc := hu.ctx
  have hout : InRegions u.wr (L.out + BitVec.ofNat 64 j + BitVec.ofNat 64 0) 1 :=
    ⟨L.OUT, by rw [hc.wr]; simp, by rw [add_add, Nat.add_zero]; exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩
  have houtR : InRegions (u.rd ++ u.wr) (L.out + BitVec.ofNat 64 j + BitVec.ofNat 64 0) 1 :=
    let ⟨R, hR, hc'⟩ := hout; ⟨R, List.mem_append_right _ hR, hc'⟩
  refine WP.mono (maskBody_ok (by rw [hu.x11]; exact houtR) (by rw [hu.x11]; exact hout)
    (by rw [hu.x13]; exact hc.in_fr (by unfold oEM frameBytes; omega_using [hk, hj]))) fun w hw => ?_
  -- `out`'s bytes and `EM`'s are apart.
  have hsep : ∀ i, i < L.k.toNat → L.out + BitVec.ofNat 64 i ≠ L.Q + BitVec.ofNat 64 (oEM + j) := fun i hi e => by
    have hd := hL.stk_buf (d := oEM + j) (n := 1) (by unfold oEM; omega_using [hk, hj]) (.inl rfl)
    refine hd (L.Q + BitVec.ofNat 64 (oEM + j)) (Region.contains_self _ _) ?_
    rw [← e]; exact Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])
  have hne : ∀ i, i < L.k.toNat → i ≠ j → L.out + BitVec.ofNat 64 i ≠ L.out + BitVec.ofNat 64 j :=
    fun i hi hij => Offset.add_ofNat_ne _ (by omega_using [hi]) (by omega_using [hj]) hij
  have hj' : w.mem (L.out + BitVec.ofNat 64 j) = mb (y (L.out + BitVec.ofNat 64 j)) z := by
    rw [hw.mem, hu.x11, hu.x13, hu.x14, Bytes.write1_ne _ _ (hsep j hj), Bytes.write1_self,
      hu.todo j (Nat.le_refl _) hj]; rfl
  have hi' : ∀ i, i < L.k.toNat → i ≠ j → w.mem (L.out + BitVec.ofNat 64 i) = u.mem (L.out + BitVec.ofNat 64 i) :=
    fun i hi hij => by
      rw [hw.mem, hu.x11, hu.x13, Bytes.write1_ne _ _ (hsep i hi), Bytes.write1_ne _ _ (hne i hi hij)]
  have hf : Frame [⟨L.out + BitVec.ofNat 64 j, 1⟩, ⟨L.Q + BitVec.ofNat 64 (oEM + j), 1⟩] u.mem w.mem := by
    rw [hw.mem, hu.x11, hu.x13]
    exact ((Frame.refl _ _).write (List.mem_cons_self ..) _ (Region.contains_self _ _)).write
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (Region.contains_self _ _)
  have hx12 : w.gpr .x12 = BitVec.ofNat 64 (L.k.toNat - (j + 1)) := by
    rw [hw.x12, hu.x12, Bytes.counter_step hj L.k.isLt]
  have go : ∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → w.gpr r = u.gpr r := hw.other
  refine ⟨⟨?_, (go .x0 (by decide) (by decide) (by decide) (by decide)).trans hu.x0, ?_, hx12, ?_,
    (go .x14 (by decide) (by decide) (by decide) (by decide)).trans hu.x14,
    (go .x15 (by decide) (by decide) (by decide) (by decide)).trans hu.x15, fun i hi => ?_, fun i hi hik => ?_⟩, ?_⟩
  · refine hc.store' hL hw.rd hw.wr hw.sp hw.v (fun r hr _ => go r (mem_ne hr (by decide))
      (mem_ne hr (by decide)) (mem_ne hr (by decide)) (mem_ne hr (by decide))) hf fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl (Offset.sub_base _ (by omega_using [hj]))
    · exact .inr ⟨oEM + j, by unfold oEM; omega_using [], by show oEM + j + 1 ≤ 1072; unfold oEM; omega_using [hk, hj], rfl⟩
  · rw [hw.x11, hu.x11, add_one]
  · rw [hw.x13, hu.x13, add_add, Nat.add_assoc]
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [hi' i (by omega_arith) (by omega_using [hi])]; exact hu.done i hi
    · exact hj'
  · rw [hi' i hik (by omega_using [hi])]; exact hu.todo i (by omega_using [hi]) hik
  · rw [hx12]; exact Bytes.counter_ne hj L.k.isLt

end VG.Proof.RsaPkcs1Enc.AArch64.Enc

end

end

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

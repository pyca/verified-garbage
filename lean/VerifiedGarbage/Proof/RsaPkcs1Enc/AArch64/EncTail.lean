import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCall

/-!
# RSAES-PKCS1-v1_5 encryption on AArch64: the mask

After the call, `maskArgs` masks the result with the zero test of `PS`, and
`maskLoop` masks each byte of `out` with it, overwriting `EM` with zeros
(`maskLoop_ok`): if `PS` has a zero byte, `out` is zeros and the result 0.
-/

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

theorem zmask_cases (bs : List Byte) : zmask bs = 0 ∨ zmask bs = BitVec.allOnes 64 := by
  unfold zmask; split <;> simp

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
      exact hL.fr_sep (by omega) (by omega) (by omega)
  · rcases hin r hr with hs | ⟨d', h₁, h₂, hb⟩
    · exact ⟨L.OUT, by simp, hs⟩
    · obtain ⟨b, n⟩ := r
      simp only at hb h₂; subst hb
      exact ⟨L.STK, by simp, Lay.Ok.sub_stk (by omega)⟩

end Ctx

theorem maskLoop_ok {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ y : Mem}
    {r z : BitVec 64} {t : State} (h : MaskInv L g vv m₀ y r z 0 t) :
    WP isa maskLoop t (MaskInv L g vv m₀ y r z L.k.toNat) := by
  have hnQ := hL.nQ
  have hk := hL.k1024
  have hk64 := hL.k64
  have hbO := hL.bO
  refine Bytes.count_loop (by omega) (MaskInv L g vv m₀ y r z) (fun j hj u hu => ?_) h
  have hc := hu.ctx
  have hout : InRegions u.wr (L.out + BitVec.ofNat 64 j + BitVec.ofNat 64 0) 1 :=
    ⟨L.OUT, by rw [hc.wr]; simp, by rw [add_add, Nat.add_zero]; exact Offset.contains_base _ (by omega) (by omega)⟩
  have houtR : InRegions (u.rd ++ u.wr) (L.out + BitVec.ofNat 64 j + BitVec.ofNat 64 0) 1 :=
    let ⟨R, hR, hc'⟩ := hout; ⟨R, List.mem_append_right _ hR, hc'⟩
  refine WP.mono (maskBody_ok (by rw [hu.x11]; exact houtR) (by rw [hu.x11]; exact hout)
    (by rw [hu.x13]; exact hc.in_fr (by unfold oEM frameBytes; omega))) fun w hw => ?_
  -- `out`'s bytes and `EM`'s are apart.
  have hsep : ∀ i, i < L.k.toNat → L.out + BitVec.ofNat 64 i ≠ L.Q + BitVec.ofNat 64 (oEM + j) := fun i hi e => by
    have hd := hL.stk_buf (d := oEM + j) (n := 1) (by unfold oEM; omega) (.inl rfl)
    refine hd (L.Q + BitVec.ofNat 64 (oEM + j)) (Region.contains_self _ _) ?_
    rw [← e]; exact Offset.contains_base _ (by omega) (by omega)
  have hne : ∀ i, i < L.k.toNat → i ≠ j → L.out + BitVec.ofNat 64 i ≠ L.out + BitVec.ofNat 64 j :=
    fun i hi hij => Offset.add_ofNat_ne _ (by omega) (by omega) hij
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
    · exact .inl (Offset.sub_base _ (by omega))
    · exact .inr ⟨oEM + j, by unfold oEM; omega, by show oEM + j + 1 ≤ 1072; unfold oEM; omega, rfl⟩
  · rw [hw.x11, hu.x11, add_one]
  · rw [hw.x13, hu.x13, add_add, Nat.add_assoc]
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [hi' i (by omega) (by omega)]; exact hu.done i hi
    · exact hj'
  · rw [hi' i hik (by omega)]; exact hu.todo i (by omega) hik
  · rw [hx12]; exact Bytes.counter_ne hj L.k.isLt

end VG.Proof.RsaPkcs1Enc.AArch64.Enc

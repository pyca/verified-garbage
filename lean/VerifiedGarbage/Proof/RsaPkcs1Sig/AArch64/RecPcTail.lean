module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecPcCall
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.RecoverCorrect
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Block

/-!
# `vg_rsa_pkcs1_recover_precomputed` on AArch64: after the call

Whatever the call left in `EM₁` and its status: the status is kept in the
frame's word at `oSt`; `EM₁`'s last `out_len` bytes are encoded into `EM₂`
and, if that succeeds, compared with `EM₁` (`vg_rsa_pkcs1_recover`'s
pieces); the mask, all ones exactly when they are equal and the status is
not 0, goes to the frame's word at `oMk` (`maskM_ok`); the value is copied to
`out` and masked (`maskLoop_ok`), and the result is 1 under the mask. With
the status and `EM₁` the call writes if `pre` holds the modulus' values,
this is `vg_rsa_pkcs1_recover`'s result (`afterPub_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.AArch64.RecPc

open VG VG.AArch64 VG.Impl.RsaPkcs1Sig.AArch64.RecoverPrecomputed VG.WriteBytes
open VG.Impl.RsaPkcs1Sig.AArch64 (encode compare)
open VG.Impl.RsaPkcs1Sig.AArch64.Verify (frameBytes oEM1 oEM2 saved)
open VG.Impl.RsaPkcs1Sig.AArch64.Recover (zeroKept copyOut encArgs cmpArgs)
open VG.Proof.RsaPkcs1Sig.AArch64.Ver (stk sR kR fb frame_sub in_frame in_frame0)
open VG.Proof.RsaPkcs1Sig.AArch64.Rec (PreR oR Mid pubOut hlen valA slots_out out_wr copyOut_ok AtEnc AfterEnc
  AtCmp AfterCmp encRes recOut zeroKept_ok)
open VG.Proof.RsaPkcs1Sig.AArch64.Ver (eval_zero')
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_ldrx wp_strx wp_ldrb wp_strb wp_addImm
  wp_subImm wp_and only_write)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_addSp wp_mov)
open VG.Proof.RsaPkcs1Sig (bytesAt_length bytesAt_writeBytes frame_writeBytes bytes_apart writeBytes_out)

/-! ## Masks -/

theorem add_not_self (r : BitVec 64) : r + ~~~r = BitVec.allOnes 64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_not, BitVec.toNat_allOnes]
  have := r.isLt
  rw [Nat.mod_eq_of_lt (by omega_arith)]; omega_arith

theorem sbc_carry (r : BitVec 64) (c : Bool) :
    r + ~~~r + BitVec.ofNat 64 c.toNat = if c then 0 else BitVec.allOnes 64 := by
  rw [add_not_self]; cases c <;> decide

/-- The carry of `a - 1`: no borrow exactly when `a` is not 0. -/
theorem carry_sub1 {n : Nat} (hn : 0 < n) (a : BitVec n) :
    (2 ^ n ≤ a.toNat + (~~~(1 : BitVec n)).toNat + true.toNat) ↔ a.toNat ≠ 0 := by
  have h1 : (1 : BitVec n).toNat = 1 := by
    show (BitVec.ofNat n 1).toNat = 1
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega_arith))
  rw [BitVec.toNat_not, h1]
  have := a.isLt
  have hp : 2 ≤ 2 ^ n := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hn; simpa using this
  simp only [Bool.toNat_true]
  omega_arith

theorem setWidth_one (sz : Size) : ((1 : BitVec 64).setWidth sz.bits) = 1 := by
  cases sz <;> rfl

theorem bits_pos (sz : Size) : 0 < sz.bits := by cases sz <;> decide

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `d ← -(d = 0)`, from the low `sz` bits of `d`, with `1` in `m`. -/
theorem wp_isZero {sz : Size} {d m : Reg} (h1 : s.gpr m = 1)
    (k : ∀ s', Only [d] s s' → s'.gpr d = (if s.read sz d = 0 then BitVec.allOnes 64 else 0) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.subs sz d d m :: .sbc .x d d d :: is)) s Q := by
  refine VG.Proof.MlKem.AArch64.WP.cons rfl (VG.Proof.MlKem.AArch64.WP.cons rfl
    (k _ ⟨fun r hr => ?_, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩ ?_))
  · have hr' : r ≠ d := fun h => hr (by simp [h])
    simp only [State.write, State.addWithCarry, hr', ite_false]
  · simp only [State.write, State.addWithCarry, State.read, ite_true, BitVec.setWidth_eq, h1, setWidth_one,
      sbc_carry]
    have hc := carry_sub1 (bits_pos sz) ((s.gpr d).setWidth sz.bits)
    by_cases h : (s.gpr d).setWidth sz.bits = 0
    · have : ¬ (2 ^ sz.bits ≤ ((s.gpr d).setWidth sz.bits).toNat + (~~~(1 : BitVec sz.bits)).toNat +
          true.toNat) := fun h' => hc.mp h' (by rw [h]; rfl)
      rw [decide_eq_false this]
      simp only [Bool.false_eq_true, ↓reduceIte, h]
    · have : 2 ^ sz.bits ≤ ((s.gpr d).setWidth sz.bits).toNat + (~~~(1 : BitVec sz.bits)).toNat +
          true.toNat := hc.mpr fun h' => h (BitVec.eq_of_toNat_eq (by rw [h']; rfl))
      rw [decide_eq_true this]
      simp only [↓reduceIte, h]

theorem rotateRight_zero (x : BitVec 64) : x.rotateRight 0 = x := by
  ext i hi; simp [BitVec.getElem_rotateRight, hi]

theorem wp_bic {d n m : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d = (s.gpr n &&& ~~~(s.gpr m)) → WP isa (.block is) s' Q) :
    WP isa (.block (.bicRor .x d n m 0 :: is)) s Q :=
  VG.Proof.MlKem.AArch64.wp_x (by simp [exec, State.read, rotateRight_zero]) k

end

/-- The mask from the comparison's difference `d` and the status `st`. -/
def mk (d st : BitVec 64) : BitVec 64 := if d = 0 ∧ st.setWidth 32 ≠ 0 then BitVec.allOnes 64 else 0

theorem mk_eq (d st : BitVec 64) :
    ((if d.setWidth 64 = 0 then BitVec.allOnes 64 else 0) &&&
      ~~~(if st.setWidth 32 = 0 then BitVec.allOnes 64 else 0)) = mk d st := by
  unfold mk
  rw [BitVec.setWidth_eq]
  (repeat' split) <;> first | decide | simp_all

/-- A word of the frame is readable and writable. -/
theorem frame_rw {s t : State} (hwr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr) {d n : Nat} (h : d + n ≤ frameBytes) :
    InRegions (t.rd ++ t.wr) (fb s + BitVec.ofNat 64 d) n :=
  let ⟨r, hr, hc⟩ := Ver.wr_frame hwr h
  ⟨r, List.mem_append_right _ hr, hc⟩

/-- A word of the frame `d` bytes from its base is apart from the saved
registers' slots if it is at or after `oSt`. -/
theorem slot_saved {s : State} {d : Nat} (hd : 56 ≤ d) (hn : d + 8 ≤ frameBytes) :
    Region.Disjoint ⟨fb s + BitVec.ofNat 64 16, 40⟩ ⟨fb s + BitVec.ofNat 64 d, 8⟩ :=
  Offset.disjoint _ (by omega_arith) (by decide) (by unfold frameBytes at hn; omega_arith)

theorem slot_write {s t w : State} (hm : Mid s t) {d : Nat} (hd : 56 ≤ d) (hn : d + 8 ≤ frameBytes)
    {v : BitVec 64} (m : MemTo t w (t.mem.writeW (fb s + BitVec.ofNat 64 d) v)) : Mid s w :=
  hm.frame m.keep (R := ⟨fb s + BitVec.ofNat 64 d, 8⟩) (by
    rw [m.mem]; exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _))
    (slot_saved hd hn)

/-! ## The mask -/

theorem maskM_ok {s y : State} (hm : Mid s y) :
    WP isa (.block maskM) y fun z => Mid s z ∧
      z.mem = y.mem.writeW (fb s + BitVec.ofNat 64 oMk) (mk (y.gpr .x12) (y.mem.readW (fb s + BitVec.ofNat 64 oSt) 64)) := by
  unfold maskM
  refine wp_movz fun z₁ o₁ e₁ => ?_
  refine wp_isZero (sz := .x) (by rw [e₁]; rfl) fun z₂ o₂ e₂ => ?_
  refine wp_addSp (by decide) fun z₃ o₃ e₃ => ?_
  have x16 : z₃.gpr .x16 = fb s := by rw [e₃, o₂.sp, o₁.sp, hm.sp, BitVec.add_zero]
  have w₃ : z₃.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [o₃.wr, o₂.wr, o₁.wr, hm.wr]
  refine wp_ldrx (a := fb s + BitVec.ofNat 64 oSt) (by decide) (by rw [x16]) (frame_rw w₃ (by decide))
    fun z₄ o₄ e₄ => ?_
  refine wp_isZero (sz := .w) (by rw [o₄.get .x13, o₃.get .x13, o₂.get .x13, e₁]; rfl) fun z₅ o₅ e₅ => ?_
  refine wp_bic fun z₆ o₆ e₆ => ?_
  have O₆ : Only [.x13, .x12, .x16, .x8] y z₆ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans o₆))))).mono
  refine wp_strx (a := fb s + BitVec.ofNat 64 oMk) (by decide)
    (by rw [o₆.get .x16, o₅.get .x16, o₄.get .x16, x16]) (by rw [O₆.wr, hm.wr]; exact in_frame _ _ (by decide))
    fun z₇ m₇ => wp_nil ⟨slot_write (hm.only O₆) (d := oMk) (by decide) (by decide) m₇, ?_⟩
  rw [m₇.mem, e₆, O₆.mem, o₅.get .x12, e₅, o₄.get .x12, o₃.get .x12, e₂]
  simp only [State.read, e₄, o₃.mem, o₂.mem, o₁.mem, o₁.get .x12]
  rw [← mk_eq]

/-! ## Masking `out` -/

theorem and_byte (b : Byte) (x : BitVec 64) : ((b.setWidth 64) &&& x).setWidth 8 = b &&& x.setWidth 8 := by
  ext i hi; simp [show i < 64 by omega_arith]

theorem off_ne {p : Addr} {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) (hne : i ≠ j) :
    p + BitVec.ofNat 64 i ≠ p + BitVec.ofNat 64 j := fun h => by
  have h' := congrArg (· - p) h
  simp only [Offset.add_sub_cancel_left] at h'
  have := congrArg BitVec.toNat h'
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  exact hne this

/-- `maskLoop` ANDs each of the `n` bytes at `x11 = p`, counted down in `x12`,
with the low byte of `x9`. -/
theorem maskLoop_ok {s : State} {p : Addr} {n : Nat} (hn : 0 < n) (hn' : n < 2 ^ 64)
    (h11 : s.gpr .x11 = p) (h12 : s.gpr .x12 = BitVec.ofNat 64 n)
    (hw : ∀ i < n, InRegions s.wr (p + BitVec.ofNat 64 i) 1) :
    WP isa maskLoop s fun t => Keep [.x10, .x11, .x12] s t ∧
      t.mem = writeBytes s.mem p ((Spec.Rsa.bytesAt s.mem p n).map (· &&& (s.gpr .x9).setWidth 8)) := by
  refine WP.mono (VG.Proof.RsaPkcs1Sig.AArch64.wp_countdown (cnt := .x12) hn' hn
    (fun i t => Keep [.x10, .x11, .x12] s t ∧
      t.mem = writeBytes s.mem p (((Spec.Rsa.bytesAt s.mem p n).take i).map (· &&& (s.gpr .x9).setWidth 8)) ∧
      t.gpr .x11 = p + BitVec.ofNat 64 i) ?_
    ⟨Keep.refl _ _, by simp [writeBytes_nil], by simp [h11]⟩ h12) fun t h => ⟨h.1, ?_⟩
  · intro i hi t ⟨hK, hm, h11'⟩ _
    have hlt : (((Spec.Rsa.bytesAt s.mem p n).take i).map (· &&& (s.gpr .x9).setWidth 8)).length = i := by
      simp [bytesAt_length]; omega_arith
    have hR : InRegions (t.rd ++ t.wr) (t.gpr .x11 + BitVec.ofNat 64 0) 1 := by
      obtain ⟨r, hr, hc⟩ := hw i hi
      exact ⟨r, List.mem_append_right _ (by rw [hK.wr]; exact hr), by rw [h11', BitVec.add_zero]; exact hc⟩
    have hv : t.mem (p + BitVec.ofNat 64 i) = s.mem (p + BitVec.ofNat 64 i) := by
      rw [hm, writeBytes_out _ _ _ _ i (fun j hj => off_ne (by omega_arith) (by omega_arith) (by omega_arith)) (by rw [hlt])]
    refine wp_ldrb (by decide) rfl hR fun s₁ o₁ e₁ => ?_
    refine wp_and fun s₂ o₂ e₂ => ?_
    have hW : InRegions s₂.wr (s₂.gpr .x11 + BitVec.ofNat 64 0) 1 := by
      rw [o₂.wr, o₁.wr, o₂.get .x11, o₁.get .x11, h11', hK.wr, BitVec.add_zero]; exact hw i hi
    refine wp_strb (by decide) rfl hW fun s₃ m₃ => ?_
    refine wp_addImm (by decide) fun s₄ o₄ e₄ => ?_
    refine wp_subImm (by decide) fun s₅ o₅ e₅ => wp_nil ?_
    have hK' : Keep [.x10, .x11, .x12] t s₅ :=
      (o₁.keep.trans (o₂.keep.trans (m₃.keep.trans (o₄.keep.trans o₅.keep)))).mono
    refine ⟨⟨(hK.trans hK').mono, ?_, ?_⟩, ?_⟩
    · rw [o₅.mem, o₄.mem, m₃.mem, o₂.mem, e₂, o₂.get .x11, o₁.get .x11, e₁, o₁.mem, o₁.get .x9, hK.get .x9,
        h11', BitVec.add_zero, hv, and_byte, hm, bytesAt_take_succ _ _ hi, List.map_append, List.map_singleton,
        writeBytes_snoc _ _ _ _ (by rw [hlt]; omega_arith), hlt]
    · rw [o₅.get .x11, e₄, m₃.gpr, o₂.get .x11, o₁.get .x11, h11', VG.Proof.RsaPkcs1Sig.AArch64.ofNat_succ']
    · rw [e₅, o₄.get .x12, m₃.gpr, o₂.get .x12, o₁.get .x12]
  · rw [List.take_of_length_le (by simp [bytesAt_length])] at h
    exact h.2.1

/-! ## The release -/

/-- A word of the frame, after writes to `out`. -/
theorem slot_out {K : Nat} {s : State} (hp : PreR K s) {d : Nat} (hd : d + 8 ≤ frameBytes) {m : Mem}
    (xs : List Byte) (hl : xs.length = (s.gpr .x1).toNat) :
    (writeBytes m (s.gpr .x0) xs).readW (fb s + BitVec.ofNat 64 d) 64 = m.readW (fb s + BitVec.ofNat 64 d) 64 :=
  (frame_writeBytes m (s.gpr .x0) xs).readW (r := ⟨fb s + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _)
    (fun r hr => by
      rw [List.mem_singleton.mp hr, hl]
      exact hp.ko.sub_left (frame_sub K s hd)) (by decide)

theorem written_mask {m : Mem} {o : Addr} {n : Nat} {val : List Byte} (hl : val.length = n) (hn : n < 2 ^ 64)
    (M : BitVec 64) (hM : M = BitVec.allOnes 64 ∨ M = 0) :
    Spec.Rsa.written (writeBytes m o (val.map (· &&& M.setWidth 8))) o n ((1 &&& M).setWidth 32)
      (if M = BitVec.allOnes 64 then some val else none) := by
  have hb : Spec.Rsa.bytesAt (writeBytes m o (val.map (· &&& M.setWidth 8))) o n = val.map (· &&& M.setWidth 8) := by
    have := bytesAt_writeBytes m o (val.map (· &&& M.setWidth 8)) (by simp [hl, hn])
    rwa [List.length_map, hl] at this
  rcases hM with rfl | rfl
  · rw [ite_eq_left rfl]
    refine ⟨by decide, ?_⟩
    have ha : ∀ x : Byte, x &&& (BitVec.allOnes 64).setWidth 8 = x := fun x => by
      rw [show (BitVec.allOnes 64).setWidth 8 = BitVec.allOnes 8 from by decide, BitVec.and_allOnes]
    rw [hb]
    simp only [ha, List.map_id']
  · have h0 : ¬ (0 : BitVec 64) = BitVec.allOnes 64 := by decide
    rw [ite_eq_right h0]
    refine ⟨by decide, ?_⟩
    rw [hb, ← hl]
    simp [List.map_const']

theorem mk_cases (d st : BitVec 64) : mk d st = BitVec.allOnes 64 ∨ mk d st = 0 := by
  unfold mk
  by_cases h : d = 0 ∧ st.setWidth 32 ≠ 0
  · exact .inl (ite_eq_left h)
  · exact .inr (ite_eq_right h)

theorem mk_allOnes (d st : BitVec 64) : mk d st = BitVec.allOnes 64 ↔ d = 0 ∧ st.setWidth 32 ≠ 0 := by
  unfold mk
  by_cases h : d = 0 ∧ st.setWidth 32 ≠ 0
  · rw [ite_eq_left h]; exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [ite_eq_right h]; exact ⟨fun e => absurd e (by decide), fun h' => absurd h' h⟩

theorem release_ok {K : Nat} {s y : State} (hp : PreR K s) (hm : Mid s y) {val : List Byte}
    (hv : Spec.Rsa.bytesAt y.mem (valA s) (s.gpr .x1).toNat = val) :
    WP isa release y fun w => Mid s w ∧ Spec.Rsa.written w.mem (s.gpr .x0) (s.gpr .x1).toNat
      ((w.gpr .x0).setWidth 32)
      (if y.gpr .x12 = 0 ∧ (y.mem.readW (fb s + BitVec.ofNat 64 oSt) 64).setWidth 32 ≠ 0 then some val else none) := by
  obtain ⟨hl0, hl1⟩ := hlen hp
  have hk2 := hp.k2
  obtain ⟨M, hM⟩ : ∃ M, M = mk (y.gpr .x12) (y.mem.readW (fb s + BitVec.ofNat 64 oSt) 64) := ⟨_, rfl⟩
  have hvl : val.length = (s.gpr .x1).toNat := by rw [← hv, bytesAt_length]
  unfold release
  refine WP.seq (WP.mono (maskM_ok hm) fun z ⟨mz, hz⟩ => ?_)
  rw [← hM] at hz
  have hvz : Spec.Rsa.bytesAt z.mem (valA s) (s.gpr .x1).toNat = val := by
    rw [← hv, hz]
    refine bytes_apart (R := ⟨valA s, (s.gpr .x1).toNat⟩)
      (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)) ?_
      (by show (s.gpr .x1).toNat ≤ 2 ^ 64; omega_arith)
    show Region.Disjoint ⟨fb s + BitVec.ofNat 64 (oEM1 + ((s.gpr .x3).toNat - (s.gpr .x1).toNat)), _⟩ _
    exact Offset.disjoint _ (.inr (by unfold oEM1 oMk; omega_arith)) (by unfold oEM1; omega_arith) (by unfold oMk; omega_arith)
  refine WP.seq (WP.mono (copyOut_ok hp mz) fun w₁ ⟨m₁, wr₁, hm₁, x0₁⟩ => ?_)
  rw [hvz] at wr₁ hm₁
  have hk₁ : w₁.mem.readW (fb s + BitVec.ofNat 64 oMk) 64 = M := by
    rw [hm₁, slot_out hp (by decide) val hvl, hz]
    exact Mem.readW_writeW_self (n := 8) _ _ _ (by decide)
  have hb₁ : Spec.Rsa.bytesAt w₁.mem (s.gpr .x0) (s.gpr .x1).toNat = val := wr₁.2
  -- The mask loop's registers.
  unfold maskArgs
  refine WP.seq (wp_addSp (by decide) fun w₂ o₂ e₂ => ?_)
  have x16 : w₂.gpr .x16 = fb s := by rw [e₂, m₁.sp, BitVec.add_zero]
  have w₂w : w₂.wr = ⟨fb s, frameBytes⟩ :: s.wr := by rw [o₂.wr, m₁.wr]
  refine wp_ldrx (a := fb s + BitVec.ofNat 64 oMk) (by decide) (by rw [x16]) (frame_rw w₂w (by decide))
    fun w₃ o₃ e₃ => wp_mov fun w₄ o₄ e₄ => wp_mov fun w₅ o₅ e₅ => wp_nil ?_
  have O₅ : Only [.x16, .x9, .x11, .x12] w₁ w₅ := (o₂.trans (o₃.trans (o₄.trans o₅))).mono
  have x9 : w₅.gpr .x9 = M := by rw [o₅.get .x9, o₄.get .x9, e₃, o₂.mem, hk₁]
  have x11 : w₅.gpr .x11 = s.gpr .x0 := by rw [o₅.get .x11, e₄, o₃.get .x19, o₂.get .x19, m₁.x19]
  have x12 : w₅.gpr .x12 = BitVec.ofNat 64 (s.gpr .x1).toNat := by
    rw [e₅, o₄.get .x20, o₃.get .x20, o₂.get .x20, m₁.x20, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have m₅ := m₁.only O₅
  refine WP.seq (WP.mono (maskLoop_ok hl0 (by omega_arith) x11 x12 (by rw [O₅.wr, m₁.wr]; exact out_wr hp [_]))
    fun w₆ ⟨k₆, hm₆⟩ => ?_)
  rw [O₅.mem, hb₁, x9] at hm₆
  unfold fin
  refine wp_and fun w₇ o₇ e₇ => wp_nil ⟨?_, ?_⟩
  · have m₆ : Mid s w₆ := m₅.frame k₆ (R := oR s) (by
      rw [hm₆, O₅.mem]
      have := frame_writeBytes w₁.mem (s.gpr .x0) (val.map (· &&& M.setWidth 8))
      rwa [List.length_map, hvl] at this) (slots_out hp)
    exact m₆.only o₇
  · rw [o₇.mem, hm₆, e₇, k₆.get .x0, k₆.get .x9, x9, O₅.get .x0, x0₁]
    have hif : (y.gpr .x12 = 0 ∧ (y.mem.readW (fb s + BitVec.ofNat 64 oSt) 64).setWidth 32 ≠ 0) ↔
        M = BitVec.allOnes 64 := by rw [hM, mk_allOnes]
    rw [show (if y.gpr .x12 = 0 ∧ (y.mem.readW (fb s + BitVec.ofNat 64 oSt) 64).setWidth 32 ≠ 0 then some val
        else none) = if M = BitVec.allOnes 64 then some val else none from by simp only [hif]]
    exact written_mask hvl (by omega_arith) M (hM ▸ mk_cases _ _)

/-! ## After the encoding -/

theorem cmpArgs_okP {s w : State} {h : Spec.RsaPkcs1Sig.Hash} {em em' : List Byte} (hm : Mid s w)
    (b1 : Spec.Rsa.bytesAt w.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .x3).toNat = em)
    (b2 : Spec.Rsa.bytesAt w.mem (fb s + BitVec.ofNat 64 oEM2) (s.gpr .x3).toNat = em')
    (hv : Spec.Rsa.bytesAt w.mem (valA s) (s.gpr .x1).toNat = em.drop ((s.gpr .x3).toNat - h.len)) :
    WP isa (.block cmpArgs) w fun v => AtCmp s h em em' v ∧ v.mem = w.mem := by
  unfold cmpArgs
  refine wp_addSp (by decide) fun v₁ p₁ f₁ => wp_addSp (by decide) fun v₂ p₂ f₂ =>
    wp_mov fun v₃ p₃ f₃ => wp_nil ?_
  have P₃ : Only [.x14, .x15, .x13] w v₃ := (p₁.trans (p₂.trans p₃)).mono
  refine ⟨⟨hm.only P₃, ?_, ?_, ?_, by rw [P₃.mem, b1], by rw [P₃.mem, b2], by rw [P₃.mem, hv]⟩, P₃.mem⟩
  · rw [p₃.get .x14, p₂.get .x14, f₁, hm.sp]
  · rw [p₃.get .x15, f₂, p₁.sp, hm.sp]
  · rw [f₃, p₂.get .x21, p₁.get .x21, hm.x21, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem cmp_okP {K : Nat} {s v : State} (hp : PreR K s) {h : Spec.RsaPkcs1Sig.Hash} {em em' : List Byte}
    (hv : AtCmp s h em em' v) : WP isa compare v fun y => AfterCmp s h em em' y ∧ y.mem = v.mem := by
  have hk1 := hp.k1; have hk2 := hp.k2
  refine WP.mono (VG.Proof.RsaPkcs1Sig.AArch64.compare_ok (s := v) (n := (s.gpr .x3).toNat) (by omega_arith) (by omega_arith)
    hv.x13
    (fun j hj => by rw [hv.x14]; exact Rec.frame_bytes hv.mid.wr (by unfold oEM1 frameBytes; omega_arith) j hj)
    (fun j hj => by rw [hv.x15]; exact Rec.frame_bytes hv.mid.wr (by unfold oEM2 frameBytes; omega_arith) j hj))
    fun y ⟨oy, hiff, _⟩ => ⟨⟨hv.mid.only oy, ?_, by rw [oy.mem, hv.val]⟩, oy.mem⟩
  rw [hv.x14, hv.x15, hv.b1, hv.b2] at hiff
  exact hiff

/-- The result after the encoding, from `EM₁`'s bytes `em` and the status
`st`. -/
def tailOut (s : State) (h : Spec.RsaPkcs1Sig.Hash) (em : List Byte) (st : BitVec 64) : Option (List Byte) :=
  match encRes s h em with
  | none => none
  | some em' => if em = em' ∧ st.setWidth 32 ≠ 0 then some (em.drop ((s.gpr .x3).toNat - h.len)) else none

theorem tail_ok {K : Nat} {s w : State} (hp : PreR K s) {h : Spec.RsaPkcs1Sig.Hash} {em : List Byte}
    (hw : AfterEnc s h em w) {st : BitVec 64} (hst : w.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 = st) :
    WP isa tail w fun w' => Mid s w' ∧ Spec.Rsa.written w'.mem (s.gpr .x0) (s.gpr .x1).toNat
      ((w'.gpr .x0).setWidth 32) (tailOut s h em st) := by
  have hres := hw.res
  unfold tail tailOut
  cases heo : encRes s h em with
  | none =>
    rw [heo] at hres
    refine WP.ite true ((eval_zero' w .x0).trans (by rw [hres]; rfl)) (fun _ => ?_) (by simp)
    exact zeroKept_ok hp hw.mid
  | some em' =>
    rw [heo] at hres
    obtain ⟨h1, b1, b2, hv⟩ := hres
    dsimp only
    refine WP.ite false ((eval_zero' w .x0).trans (by rw [h1]; rfl)) (by simp) fun _ => ?_
    refine WP.seq (WP.mono (cmpArgs_okP hw.mid b1 b2 hv) fun v ⟨hv', mv⟩ =>
      WP.seq (WP.mono (cmp_okP hp hv') fun y ⟨hy, my⟩ => ?_))
    refine WP.mono (release_ok hp hy.mid hy.val) fun w' ⟨m', r'⟩ => ⟨m', ?_⟩
    rw [my, mv, hst] at r'
    have e : (y.gpr .x12 = 0 ∧ st.setWidth 32 ≠ 0) ↔ (em = em' ∧ st.setWidth 32 ≠ 0) := by rw [hy.hiff]
    simp only [e] at r'
    exact r'

/-- The result is `vg_rsa_pkcs1_recover`'s, with what the call writes if
`pre` holds the modulus' values. -/
theorem tailOut_eq {s : State} {h : Spec.RsaPkcs1Sig.Hash} {em : List Byte} {st : BitVec 64} {m : Mem}
    (hw : Spec.Rsa.written m (fb s + BitVec.ofNat 64 oEM1) (s.gpr .x3).toNat (st.setWidth 32) (pubOut s))
    (hem : Spec.Rsa.bytesAt m (fb s + BitVec.ofNat 64 oEM1) (s.gpr .x3).toNat = em) :
    tailOut s h em st = recOut s h := by
  unfold tailOut recOut encRes
  cases hpo : pubOut s with
  | none =>
    rw [hpo] at hw
    have h0 := hw.1
    cases Spec.RsaPkcs1Sig.encode h (em.drop ((s.gpr .x3).toNat - h.len)) (s.gpr .x3).toNat with
    | none => rfl
    | some em' => exact ite_eq_right fun h' => h'.2 h0
  | some e0 =>
    rw [hpo] at hw
    obtain ⟨h1, hb⟩ := hw
    obtain rfl : em = e0 := hem.symm.trans hb
    dsimp only
    cases Spec.RsaPkcs1Sig.encode h (em.drop ((s.gpr .x3).toNat - h.len)) (s.gpr .x3).toNat with
    | none => exact (ite_eq_right fun (h' : (none : Option (List Byte)) = some em) => by cases h').symm
    | some em' =>
      dsimp only
      by_cases hq : em = em'
      · subst hq
        rw [ite_eq_left ⟨rfl, by rw [h1]; decide⟩, ite_eq_left rfl]
      · rw [ite_eq_right fun h' => hq h'.1, ite_eq_right fun h' => hq (Option.some.inj h').symm]

/-! ## After the call -/

theorem afterPub_ok {K : Nat} {s t : State} (hp : PreR K s) {h : Spec.RsaPkcs1Sig.Hash}
    (hh : Spec.RsaPkcs1Sig.Hash.ofId ((s.gpr .x6).setWidth 32).toNat = some h) (hol : (s.gpr .x1).toNat = h.len)
    (ha : AfterCallP s t) :
    WP isa afterPub t fun w => Mid s w ∧ (Consistent s →
      Spec.Rsa.written w.mem (s.gpr .x0) (s.gpr .x1).toNat ((w.gpr .x0).setWidth 32) (recOut s h)) := by
  have hk2 := hp.k2
  unfold afterPub
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine wp_addSp (by decide) fun t₁ o₁ e₁ => wp_strx (a := fb s + BitVec.ofNat 64 oSt) (by decide)
    (by rw [e₁, ha.sp, BitVec.add_zero]) (by rw [o₁.wr, ha.wr]; exact in_frame _ _ (by decide))
    fun t₂ m₂ => wp_nil ?_
  have mid₂ : Mid s t₂ := slot_write (ha.toMid.only o₁) (d := oSt) (by decide) (by decide) m₂
  have hst₂ : t₂.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 = t.gpr .x0 := by
    rw [m₂.mem, o₁.get .x0]; exact Mem.readW_writeW_self (n := 8) _ _ _ (by decide)
  obtain ⟨em, hem⟩ : ∃ em, Spec.Rsa.bytesAt t₂.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .x3).toNat = em :=
    ⟨_, rfl⟩
  have hemt : Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oEM1) (s.gpr .x3).toNat = em := by
    rw [← hem, m₂.mem, o₁.mem]
    refine (bytes_apart (R := ⟨fb s + BitVec.ofNat 64 oEM1, (s.gpr .x3).toNat⟩)
      (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)) ?_
      (by show (s.gpr .x3).toNat ≤ 2 ^ 64; omega_arith)).symm
    exact Offset.disjoint _ (.inr (by unfold oEM1 oSt; omega_arith)) (by unfold oEM1; omega_arith) (by unfold oSt; omega_arith)
  refine WP.mono (Rec.encArgs_ok hp mid₂) fun u ⟨O, x8, x9, x10, x12, x11⟩ => ?_
  have hu : AtEnc s em u := ⟨mid₂.only O, x8, x9, x10, x12, x11, by rw [O.mem, hem]⟩
  refine WP.seq (WP.mono (Rec.enc_ok hp hh hol hu) fun w ⟨hw, fw⟩ => ?_)
  have hst : w.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 = t.gpr .x0 := by
    rw [fw.readW (r := ⟨fb s + BitVec.ofNat 64 oSt, 8⟩) (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by unfold oEM2 oSt; omega_arith)) (by unfold oSt; omega_arith)
        (by unfold oEM2; omega_arith)) (by decide), O.mem, hst₂]
  refine WP.mono (tail_ok hp hw hst) fun w' ⟨m', r'⟩ => ⟨m', fun hq => ?_⟩
  rwa [tailOut_eq (ha.res hq) hemt] at r'

end VG.Proof.RsaPkcs1Sig.AArch64.RecPc

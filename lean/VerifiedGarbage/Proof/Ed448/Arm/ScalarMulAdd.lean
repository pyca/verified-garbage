import VerifiedGarbage.Proof.Ed448.Arm.ScalarMain
import VerifiedGarbage.Proof.X448.Arm.MulLoop

/-!
# Ed448 scalar multiply-add on ARMv7

`vg_ed448_scalar_mul_add(out = r0, r = r1, k = r2, s = r3, scratch = [sp])`
against a local contract (`scalarMulAddLocal`), the ABI included: the three
inputs reduced (`reduceArg_ok`), the product of two with X448's rows
(`product_ok`), its limbs reduced (`reduceProduct_ok`), and the sum with the
third (`addPass_ok`) reduced once more.
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X25519.Arm
open VG.Spec.Ed448 (L bytesAt decodeLE encodeLE)

section
variable {b : BitVec 32}

/-! ## The arguments -/

/-- The argument registers `g (argReg i)` saved from `OUT` in the working space at `B`. -/
def Args (B : Addr) (g : Reg → BitVec 32) (m : Mem) : Prop :=
  ∀ i < 4, m.readW (B + BitVec.ofNat 64 (OUT + 4 * i)) 32 = g (argReg i)

theorem storeArgs_ok {s : State} (h3 : s.gpr .r12 = b) (hfit : b.toNat + 8192 ≤ 2 ^ 32)
    (hw : (⟨State.addr b, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block ((List.range 4).flatMap fun i => [.str (argReg i) .r12 (OUT + 4 * i)])) s fun s' =>
      Args (State.addr b) s.gpr s'.mem ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 OUT, 16⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ Rest [] s s' := by
  have hO := OUT_eq
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ i < n, s'.mem.readW (State.addr b + BitVec.ofNat 64 (OUT + 4 * i)) 32 =
        s.gpr (argReg i)) ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 OUT, 4 * n⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ Rest [] s s')
    (fun n s' hn ⟨h1, h2, h3', h4⟩ => ?_) 4 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, rfl, Rest.refl _ _⟩)
    fun s' h => ⟨h.1, h.2.1, h.2.2⟩
  refine wp_str (a := State.addr b + BitVec.ofNat 64 (OUT + 4 * n)) (by omega)
    (by rw [h3', h3]; exact addr_add (by omega)) (by rw [h4.wr]; exact in_base hw (by omega) (by omega))
    fun s2 u2 => WP.block_nil ⟨fun i hi => ?_, ?_, by rw [u2.gpr, h3'], h4.trans (u2.rest _)⟩
  · rw [u2.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]; exact h1 i hi
    · rw [Mem.readW_writeW_self32, h3']
  · rw [u2.mem]
    exact (h2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).writeW
      (List.mem_singleton_self _) _
      (Offset.contains _ (d := OUT + 4 * n) (n := 4) (e := OUT) (k := 4 * (n + 1)) (by omega)
        (by omega) (by omega))

theorem ldrSp_ok {s : State} {is : List Instr} {Q : State → Prop}
    (hr : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (k : ∀ t, Upd s t .r12 (stackArg s 0) → WP isa (.block is) t Q) :
    WP isa (.block (.ldrSp .r12 0 :: is)) s Q := by
  refine WP.cons (s' := s.setReg .r12 (stackArg s 0)) ?_ (k _ (Upd.setReg _ _ _))
  simp only [exec, show (0 : Nat) < 4096 from by decide, ite_true, State.load32,
    BitVec.add_zero, hr, Option.map_some]
  simp [stackArg, stackArgAddr]

theorem mulAddArgs_ok {s : State} (hr : InRegions (s.rd ++ s.wr) (State.addr s.sp) 4)
    (hfit : (stackArg s 0).toNat + 8192 ≤ 2 ^ 32)
    (hw : (⟨State.addr (stackArg s 0), 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block mulAddArgs) s fun t =>
      Ctx8 (stackArg s 0) t ∧ t.gpr .r6 = mask16 ∧ Saved (State.addr (stackArg s 0)) s.gpr t.mem ∧
      Args (State.addr (stackArg s 0)) s.gpr t.mem ∧ Rest [.r0, .r6, .r12] s t ∧
      Frame [⟨State.addr (stackArg s 0), 48⟩] s.mem t.mem := by
  have hO := OUT_eq
  unfold mulAddArgs
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine ldrSp_ok hr fun u hu => ?_
  refine WP.append (saveAt_ok hu.gpr hfit (hu.wr ▸ hw)) fun v ⟨sv, fv, gv, kv⟩ => ?_
  refine WP.append (storeArgs_ok (by rw [gv]; exact hu.gpr) hfit
    (by rw [kv.wr, hu.wr]; exact hw)) fun w ⟨aw, fw, gw, kw⟩ => ?_
  refine wp_mov (op2_reg _ _) fun x hx => wp_movw fun t ht => WP.block_nil ?_
  have kt : Rest [.r0, .r6, .r12] s t := (hu.rest (by decide)).trans
    ((kv.mono (by decide)).trans ((kw.mono (by decide)).trans ((hx.rest (by decide)).trans
      (ht.rest (by decide)))))
  have mt : t.mem = w.mem := by rw [ht.mem, hx.mem]
  refine ⟨⟨?_, hfit, by rw [kt.wr]; exact hw⟩, ht.gpr, ?_, ?_, kt, ?_⟩
  · rw [ht.other _ (by decide), hx.gpr, gw, gv, hu.gpr]
  · have sn : ∀ i < 8, savedReg i ≠ .r12 := by decide
    intro i hi
    rw [mt, fw.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide), sv i hi]
    · exact hu.other _ (sn i hi)
    · rw [List.mem_singleton.mp hr]
      exact Offset.disjoint _ (.inl (by omega)) (by omega) (by decide)
  · have an : ∀ i < 4, argReg i ≠ .r12 := by decide
    intro i hi
    rw [mt, aw i hi, gv]
    exact hu.other _ (an i hi)
  · rw [mt, ← hu.mem]
    exact (fv.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩).trans
      (fw.sub fun r hr => ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by decide)⟩)

/-! ## The inputs -/

theorem reduceArg_ok {o off : Nat} (ho : Buf o) (hoff : off + 4 ≤ 64) {p : BitVec 32} {s : State}
    (hc : Ctx8 b s) (h6 : s.gpr .r6 = mask16)
    (hp : s.mem.readW (State.addr b + BitVec.ofNat 64 off) 32 = p) (hfit : p.toNat + 57 ≤ 2 ^ 32)
    (hr : (⟨State.addr p, 57⟩ : Region) ∈ s.rd ++ s.wr)
    (hsep : (⟨State.addr p, 57⟩ : Region).Disjoint ⟨State.addr b, 8192⟩) :
    WP isa (reduceArg off o) s fun t => Rest [.r1, .r2, .r3, .r4, .r5, .r9, .r10, .r11, .r12] s t ∧
      Frame [limbsR b TF, limbsR b o] s.mem t.mem ∧ Lim28 t.mem (State.addr b) o ∧
      V28 t.mem (State.addr b) o = decodeLE (bytesAt s.mem (State.addr p) 57) % L := by
  have hT := TF_eq
  obtain ⟨ho1, ho2⟩ := ho
  unfold reduceArg
  have hld : WP isa (.block [.ldr .r12 .r0 off]) s fun u =>
      Rest [.r12] s u ∧ u.mem = s.mem ∧ u.gpr .r12 = p :=
    ldr0_ok hc (d := off) (by omega) fun u hu => WP.block_nil ⟨hu.rest (by decide), hu.mem,
      by rw [hu.gpr, hp]⟩
  refine WP.seq (WP.mono hld fun u ⟨ku, mu, pu⟩ => ?_)
  refine WP.mono (reduce57_ok ⟨ho1, ho2⟩ (hc.of_rest ku (by decide)) ((ku.gpr _ (by decide)).trans h6) pu
    hfit (fun i hi => by rw [ku.rd, ku.wr]; exact in_base hr (by omega) (by omega))
    (fun r hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl <;> exact hsep.sub_right (Offset.sub_base _ (by omega))))
    fun t ⟨kt, lt, vt⟩ => ⟨(ku.mono (by decide)).trans (kt.rest.mono (by decide)), by
      rw [← mu]; exact kt.frame, lt, by rw [vt, mu]⟩

/-! ## The product -/

theorem valN_eq (f : Nat → Nat) (n : Nat) : Proof.X448.Radix16.valN f n = val16 f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Proof.X448.Radix16.valN_succ, val16_succ, ih, Proof.X448.Radix16.radix, ← Nat.pow_mul]

theorem SK_eq : SK = 320 := rfl
theorem SS_eq : SS = 448 := rfl
theorem SR_eq : SR = 576 := rfl
theorem RA_eq : RA = 192 := rfl

theorem product_ok {s : State} (hc : Ctx8 b s) (h6 : s.gpr .r6 = mask16)
    (hk : Lim28 s.mem (State.addr b) SK) (hs : Lim28 s.mem (State.addr b) SS) :
    WP isa product s fun t => Rest [.r1, .r2, .r3, .r4, .r5, .r7, .r9] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 Impl.X448.Arm.ACC, 224⟩] s.mem t.mem ∧
      (∀ j < 56, limb t.mem (State.addr b) Impl.X448.Arm.ACC j < 65536) ∧
      val16 (limb t.mem (State.addr b) Impl.X448.Arm.ACC) 56 =
        V28 s.mem (State.addr b) SK * V28 s.mem (State.addr b) SS := by
  have hrc : Proof.X448.Arm.RowCtx b s := ⟨hc.r0, by have := hc.fit; omega, hc.wr⟩
  unfold product
  refine WP.seq (WP.mono (Proof.X448.Arm.mulPre_ok (x := SK) (y := SS) hrc h6) fun u hu => ?_)
  refine WP.mono (Proof.X448.Arm.mulLoop_ok (by decide) (by decide) hk hs hu) fun t ht => ?_
  refine ⟨ht.rest, ht.frame, ht.lt, ?_⟩
  have e : val16 (limb t.mem (State.addr b) Impl.X448.Arm.ACC) 56 =
      Proof.X448.Radix16.valN (Proof.X448.Arm.accw t.mem (State.addr b)) (28 + 28) := (valN_eq _ _).symm
  have e' : Proof.X448.Radix16.valN (Proof.X448.Arm.limbs s.mem (State.addr b) SK) 28 *
      Proof.X448.Arm.fe s.mem (State.addr b) SS = V28 s.mem (State.addr b) SK * V28 s.mem (State.addr b) SS := by
    unfold Proof.X448.Arm.fe; rw [valN_eq, valN_eq]; rfl
  exact e.trans (ht.val.trans e')

theorem reduceProduct_ok {s : State} (hc : Ctx8 b s) (h6 : s.gpr .r6 = mask16)
    (hacc : ∀ j < 56, limb s.mem (State.addr b) Impl.X448.Arm.ACC j < 65536) :
    WP isa reduceProduct s fun t => LoopKeep b RA s t ∧ Lim28 t.mem (State.addr b) RA ∧
      V28 t.mem (State.addr b) RA = val16 (limb s.mem (State.addr b) Impl.X448.Arm.ACC) 56 % L := by
  have hA := ACC_eq
  have hR := RA_eq
  have hT := TF_eq
  unfold reduceProduct
  have hinit : WP isa (.block (zeroR RA ++ [.mov .r10 (.imm 224)])) s fun v => LoopKeep b RA s v ∧
      v.gpr .r10 = BitVec.ofNat 32 (4 * 56) ∧ Lim28 v.mem (State.addr b) RA ∧
      V28 v.mem (State.addr b) RA = 0 :=
    WP.append (zeroR_ok (o := RA) (by decide) hc) fun u ⟨ku, fu, zu⟩ =>
      wp_mov (op2_imm (by decide)) fun v hv => WP.block_nil
        ⟨⟨(ku.mono (by decide)).trans (hv.rest (by decide)), by rw [hv.mem]; exact fu.mono (by simp)⟩,
          hv.gpr, by rw [hv.mem]; exact Lim28_zero zu, by rw [hv.mem]; exact V28_zero zu⟩
  refine WP.seq (WP.mono hinit fun v ⟨kv, cv, lv, vv⟩ => ?_)
  have la : ∀ j < 56, limb v.mem (State.addr b) Impl.X448.Arm.ACC j =
      limb s.mem (State.addr b) Impl.X448.Arm.ACC j := fun j hj =>
    wd_frame kv.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega) (by omega) (by omega)
  refine WP.mono (limbLoop_ok (hc.of_rest kv.rest (by decide)) ((kv.rest.gpr _ (by decide)).trans h6)
    (fun j hj => by rw [la j hj]; exact hacc j hj) cv lv vv) fun t ⟨kt, lt, vt⟩ =>
    ⟨kv.trans kt, lt, by rw [vt, val16_congr la]⟩

/-! ## The sum -/

theorem addPass_ok {s : State} (hc : Ctx8 b s) (h6 : s.gpr .r6 = mask16)
    (ha : Lim28 s.mem (State.addr b) RA) (hr : Lim28 s.mem (State.addr b) SR)
    (hva : V28 s.mem (State.addr b) RA < L) (hvr : V28 s.mem (State.addr b) SR < L) :
    WP isa (.block addPass) s fun t => Rest [.r2, .r3, .r4, .r5] s t ∧
      Frame [limbsR b TF] s.mem t.mem ∧ Lim28 t.mem (State.addr b) TF ∧
      V28 t.mem (State.addr b) TF = V28 s.mem (State.addr b) RA + V28 s.mem (State.addr b) SR := by
  have hT := TF_eq
  have hR := RA_eq
  have hS := SR_eq
  unfold addPass
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
  have hc1 := hc.of_rest (u1.rest (ws := [.r5]) (by decide)) (by decide)
  have r0 : s1.gpr .r0 = b := hc1.r0
  refine WP.mono (VG.Proof.X448.Arm.carryPass_ok (rb := .r0) (o := TF) (s0 := s1)
    (c := fun k => limb s.mem (State.addr b) RA k + limb s.mem (State.addr b) SR k) (cin := 0)
    (by decide) (by omega) (by rw [r0]; have := hc.fit; omega)
    (fun k hk => by rw [r0]; exact hc1.inW (by omega)) ((u1.other _ (by decide)).trans h6)
    (by rw [u1.gpr]; rfl) (fun k hk => by have := ha k hk; have := hr k hk; omega) (by decide)
    ?_) fun t ht => ?_
  · intro k hk s' hp
    have hc' := hc1.of_rest hp.rest (by decide)
    have hf : Frame [⟨State.addr b + BitVec.ofNat 64 TF, 4 * k⟩] s.mem s'.mem := by
      have := hp.frame; rwa [r0, u1.mem] at this
    have e1 : wd s'.mem (State.addr b) (RA + 4 * k) = limb s.mem (State.addr b) RA k :=
      wd_frame hf fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
    have e2 : wd s'.mem (State.addr b) (SR + 4 * k) = limb s.mem (State.addr b) SR k :=
      wd_frame hf fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)
    unfold addSrc
    refine ldr0_ok hc' (d := RA + 4 * k) (by omega) fun v1 w1 => ?_
    refine ldr0_ok (hc'.of_rest (w1.rest (ws := [.r3]) (by decide)) (by decide)) (d := SR + 4 * k)
      (by omega) fun v2 w2 => wp_dp (op2_reg _ _) fun v3 w3 => WP.block_nil ⟨?_,
        (w1.rest (by decide)).trans ((w2.rest (by decide)).trans (w3.rest (by decide))),
        by rw [w3.mem, w2.mem, w1.mem]⟩
    have x1 : (v2.gpr .r3).toNat = limb s.mem (State.addr b) RA k := by
      rw [w2.other _ (by decide), w1.gpr]; exact e1
    have x2 : (v2.gpr .r2).toNat = limb s.mem (State.addr b) SR k := by
      rw [w2.gpr, w1.mem]; exact e2
    rw [w3.gpr]
    show (v2.gpr .r3 + v2.gpr .r2).toNat = _
    rw [toNat_add_lt (by rw [x1, x2]; have := ha k hk; have := hr k hk; omega), x1, x2]
  · generalize hcf : (fun k => limb s.mem (State.addr b) RA k + limb s.mem (State.addr b) SR k) = c at ht
    have outs : ∀ k < 28, limb t.mem (State.addr b) TF k = out c 0 k := by
      intro k hk; have := ht.outs k hk; rwa [r0] at this
    have hval := (chain_val c 0 28).trans (Nat.add_zero _)
    have hcv : val16 c 28 = V28 s.mem (State.addr b) RA + V28 s.mem (State.addr b) SR := by
      unfold V28; rw [← hcf, val16_add]
    rw [hcv] at hval
    have hLM := two_L_le
    have hV : V28 t.mem (State.addr b) TF = val16 (out c 0) 28 := val16_congr outs
    refine ⟨(u1.rest (by decide)).trans (ht.rest.mono (by decide)), ?_,
      fun k hk => by rw [outs k hk]; exact out_lt _ _ _, ?_⟩
    · have := ht.frame; rw [r0, u1.mem] at this; exact this
    · rw [hV]
      generalize (2 : Nat) ^ (16 * 28 : Nat) = M at hval hLM
      rcases Nat.eq_zero_or_pos (chain c 0 28) with h | h
      · rw [h, Nat.mul_zero, Nat.add_zero] at hval; exact hval
      · have := Nat.mul_le_mul_left M h
        omega

/-! ## Composing the steps -/

/-- A region of the working space at `b` above its first 64 bytes. -/
def Hi (b : BitVec 32) (r : Region) : Prop :=
  ∃ d n, r = ⟨State.addr b + BitVec.ofNat 64 d, n⟩ ∧ 64 ≤ d ∧ d + n ≤ 8192

theorem hi_of {d n : Nat} (h1 : 64 ≤ d) (h2 : d + n ≤ 8192) :
    Hi b ⟨State.addr b + BitVec.ofNat 64 d, n⟩ := ⟨d, n, rfl, h1, h2⟩

/-- A word of the first 64 bytes across a frame of regions above them. -/
theorem readW_lo {rs : List Region} {m m' : Mem} (hf : Frame rs m m') (hrs : ∀ r ∈ rs, Hi b r)
    {e : Nat} (he : e + 4 ≤ 64) :
    m'.readW (State.addr b + BitVec.ofNat 64 e) 32 = m.readW (State.addr b + BitVec.ofNat 64 e) 32 :=
  hf.readW (Region.contains_self _ _) (fun r hr => by
    obtain ⟨d, n, rfl, h1, h2⟩ := hrs r hr
    exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)) (by decide)

theorem Saved.hi {g : Reg → BitVec 32} {m m' : Mem} (hs : Saved (State.addr b) g m) {rs : List Region}
    (hf : Frame rs m m') (hrs : ∀ r ∈ rs, Hi b r) : Saved (State.addr b) g m' := fun i hi => by
  rw [readW_lo hf hrs (by omega)]; exact hs i hi

theorem Args.hi {g : Reg → BitVec 32} {m m' : Mem} (hs : Args (State.addr b) g m) {rs : List Region}
    (hf : Frame rs m m') (hrs : ∀ r ∈ rs, Hi b r) : Args (State.addr b) g m' := fun i hi => by
  have hO := OUT_eq
  rw [readW_lo hf hrs (by omega)]; exact hs i hi

/-- The inputs and their pointers: `g (argReg i)` points to 57 readable bytes
outside the working space. -/
def Input (b : BitVec 32) (s : State) (p : BitVec 32) : Prop :=
  p.toNat + 57 ≤ 2 ^ 32 ∧ (⟨State.addr p, 57⟩ : Region) ∈ s.rd ++ s.wr ∧
    (⟨State.addr p, 57⟩ : Region).Disjoint ⟨State.addr b, 8192⟩

theorem Input.of_rest {s t : State} {ws : List Reg} {p : BitVec 32} (h : Input b s p) (hr : Rest ws s t) :
    Input b t p := ⟨h.1, by rw [hr.rd, hr.wr]; exact h.2.1, h.2.2⟩

/-- The bytes of an input across a frame of regions of the working space. -/
theorem Input.bytes {s : State} {p : BitVec 32} (h : Input b s p) {rs : List Region} {m m' : Mem}
    (hf : Frame rs m m') (hrs : ∀ r ∈ rs, Hi b r) :
    bytesAt m' (State.addr p) 57 = bytesAt m (State.addr p) 57 :=
  bytesAt_frame hf (fun r hr => by
    obtain ⟨d, n, rfl, h1, h2⟩ := hrs r hr
    exact h.2.2.sub_right (Offset.sub_base _ h2)) (by decide)

theorem limbs_frame_hi {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {o : Nat}
    (hrs : ∀ r ∈ rs, ∃ d n, r = ⟨State.addr b + BitVec.ofNat 64 d, n⟩ ∧ (d + n ≤ o ∨ o + 112 ≤ d) ∧
      d + n ≤ 8192) (ho : o + 112 ≤ 8192) :
    ∀ k < 28, limb m' (State.addr b) o k = limb m (State.addr b) o k :=
  limb_frame28 hf fun r hr k hk => by
    obtain ⟨d, n, rfl, h1, h2⟩ := hrs r hr
    exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem inputs_ok {s : State} (hc : Ctx8 b s) (h6 : s.gpr .r6 = mask16) {g : Reg → BitVec 32}
    (ha : Args (State.addr b) g s.mem) (hin : ∀ i, 1 ≤ i → i < 4 → Input b s (g (argReg i))) :
    WP isa inputs s fun t => Rest [.r1, .r2, .r3, .r4, .r5, .r9, .r10, .r11, .r12] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 TF, 624⟩] s.mem t.mem ∧
      Lim28 t.mem (State.addr b) SK ∧ Lim28 t.mem (State.addr b) SS ∧ Lim28 t.mem (State.addr b) SR ∧
      V28 t.mem (State.addr b) SK = decodeLE (bytesAt s.mem (State.addr (g .r2)) 57) % L ∧
      V28 t.mem (State.addr b) SS = decodeLE (bytesAt s.mem (State.addr (g .r3)) 57) % L ∧
      V28 t.mem (State.addr b) SR = decodeLE (bytesAt s.mem (State.addr (g .r1)) 57) % L := by
  have hT := TF_eq
  have hK := SK_eq
  have hS := SS_eq
  have hR := SR_eq
  have hO := OUT_eq
  have sub : ∀ o, TF ≤ o → o + 112 ≤ 688 → ∀ r ∈ [limbsR b TF, limbsR b o],
      ∃ e ∈ [(⟨State.addr b + BitVec.ofNat 64 TF, 624⟩ : Region)], Region.Sub r e := fun o h1 h2 r hr => by
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub _ (by omega) (by omega)
  have hiTF : ∀ o, TF ≤ o → o + 112 ≤ 4096 → ∀ r ∈ [limbsR b TF, limbsR b o], Hi b r := fun o h1 h2 r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact hi_of (by omega) (by omega)
  unfold inputs
  -- k
  obtain ⟨k1, k2, k3⟩ := hin 2 (by decide) (by decide)
  refine WP.seq (WP.mono (reduceArg_ok (o := SK) ⟨by omega, by omega⟩ (by omega) hc h6 (ha 2 (by decide))
    k1 k2 k3) fun u ⟨ku, fu, lu, vu⟩ => ?_)
  have hcu := hc.of_rest ku (by decide)
  have h6u : u.gpr .r6 = mask16 := (ku.gpr _ (by decide)).trans h6
  have hau := ha.hi fu (hiTF SK (by omega) (by omega))
  -- s
  obtain ⟨s1, s2, s3⟩ := (hin 3 (by decide) (by decide)).of_rest ku
  refine WP.seq (WP.mono (reduceArg_ok (o := SS) ⟨by omega, by omega⟩ (by omega) hcu h6u (hau 3 (by decide))
    s1 s2 s3) fun v ⟨kv, fv, lv, vv⟩ => ?_)
  have hcv := hcu.of_rest kv (by decide)
  have h6v : v.gpr .r6 = mask16 := (kv.gpr _ (by decide)).trans h6u
  have hav := hau.hi fv (hiTF SS (by omega) (by omega))
  -- r
  obtain ⟨r1, r2, r3⟩ := ((hin 1 (by decide) (by decide)).of_rest ku).of_rest kv
  refine WP.mono (reduceArg_ok (o := SR) ⟨by omega, by omega⟩ (by omega) hcv h6v (hav 1 (by decide))
    r1 r2 r3) fun t ⟨kt, ft, lt, vt⟩ => ?_
  have hiW : ∀ r ∈ [(⟨State.addr b + BitVec.ofNat 64 TF, 624⟩ : Region)], Hi b r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact hi_of (by omega) (by omega)
  have fu' := fu.sub (sub SK (by omega) (by omega))
  have fv' := fv.sub (sub SS (by omega) (by omega))
  have ft' := ft.sub (sub SR (by omega) (by omega))
  have pr : ∀ {o : Nat} {m m' : Mem}, o + 112 ≤ 4096 → Frame [limbsR b TF, limbsR b o] m m' →
      ∀ {o' : Nat}, (o + 112 ≤ o' ∨ o' + 112 ≤ o) → TF + 112 ≤ o' → o' + 112 ≤ 4096 →
      ∀ k < 28, limb m' (State.addr b) o' k = limb m (State.addr b) o' k := fun ho hf o' h1 h2 h3 =>
    limbs_frame_hi hf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, _, rfl, by omega, by omega⟩) (by omega)
  have fK : ∀ k < 28, limb t.mem (State.addr b) SK k = limb u.mem (State.addr b) SK k := fun k hk => by
    rw [pr (o := SR) (by omega) ft (o' := SK) (by omega) (by omega) (by omega) k hk,
      pr (o := SS) (by omega) fv (o' := SK) (by omega) (by omega) (by omega) k hk]
  have fS : ∀ k < 28, limb t.mem (State.addr b) SS k = limb v.mem (State.addr b) SS k :=
    pr (o := SR) (by omega) ft (o' := SS) (by omega) (by omega) (by omega)
  have bS := (hin 3 (by decide) (by decide)).bytes fu' hiW
  have bR := (hin 1 (by decide) (by decide)).bytes (fu'.trans fv') hiW
  refine ⟨(ku.trans kv).trans kt, fu'.trans (fv'.trans ft'), fun k hk => by rw [fK k hk]; exact lu k hk,
    fun k hk => by rw [fS k hk]; exact lv k hk, lt, ?_, ?_, ?_⟩
  · change _ = decodeLE (bytesAt s.mem (State.addr (g (argReg 2))) 57) % L
    rw [← vu]; exact val16_congr fK
  · change _ = decodeLE (bytesAt s.mem (State.addr (g (argReg 3))) 57) % L
    rw [← bS, ← vv]; exact val16_congr fS
  · change _ = decodeLE (bytesAt s.mem (State.addr (g (argReg 1))) 57) % L
    rw [← bR, vt]

end

end VG.Proof.Ed448.Arm

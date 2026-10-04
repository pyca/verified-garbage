import VerifiedGarbage.Proof.Ed448.Arm.ScalarStep

/-!
# Ed448 scalar arithmetic on ARMv7: the loops

The remainder of an input's bytes from the top, sixteen bits at a time
(`byteLoop_ok`), and of the product's limbs (`limbLoop_ok`), and the
remainders they start from (`zeroR_ok`, `init57_ok`).
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X25519.Arm
open VG.Spec.Ed448 (L bytesAt decodeLE)

/-! ## The numbers -/

theorem mod_fold (w D : Nat) : (w + 65536 * (D % L)) % L = (w + 65536 * D) % L := by
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp only [bytesAt, List.length_map, List.length_range]

/-- Two bytes more of a suffix. -/
theorem decode_drop2 (m : Mem) (p : Addr) {N n : Nat} (h : n + 2 ≤ N) :
    decodeLE ((bytesAt m p N).drop n) = (m (p + BitVec.ofNat 64 n)).toNat +
      256 * (m (p + BitVec.ofNat 64 (n + 1))).toNat + 65536 * decodeLE ((bytesAt m p N).drop (n + 2)) := by
  rw [List.drop_eq_getElem_cons (by rw [bytesAt_length]; omega),
    List.drop_eq_getElem_cons (by rw [bytesAt_length]; omega)]
  simp only [decodeLE, bytesAt, List.getElem_map, List.getElem_range]
  rw [show n + 1 + 1 = n + 2 from rfl]
  omega

/-- A suffix as the bytes it starts with. -/
theorem decode_drop1 (m : Mem) (p : Addr) {N n : Nat} (h : n + 1 = N) :
    decodeLE ((bytesAt m p N).drop n) = (m (p + BitVec.ofNat 64 n)).toNat := by
  rw [List.drop_eq_getElem_cons (by rw [bytesAt_length]; omega),
    List.drop_eq_nil_of_le (by rw [bytesAt_length]; omega)]
  simp only [decodeLE, bytesAt, List.getElem_map, List.getElem_range, Nat.mul_zero, Nat.add_zero]

section
variable {b : BitVec 32}

/-! ## Reading two bytes -/

theorem readBytes_ok {s : State} {p : BitVec 32} {n N : Nat} (hn : n + 2 ≤ N)
    (hp : s.gpr .r12 = p) (hfit : p.toNat + N ≤ 2 ^ 32)
    (h10 : s.gpr .r10 = BitVec.ofNat 32 (n + 2))
    (hr : ∀ i < N, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1) :
    WP isa (.block readBytes) s fun t =>
      Rest [.r2, .r3, .r10, .r11] s t ∧ t.mem = s.mem ∧ t.gpr .r10 = BitVec.ofNat 32 n ∧
      (t.gpr .r11).toNat = (s.mem (State.addr p + BitVec.ofNat 64 n)).toNat +
        256 * (s.mem (State.addr p + BitVec.ofNat 64 (n + 1))).toNat := by
  unfold readBytes
  refine wp_dp (op2_imm (by decide)) fun u1 v1 => wp_dp (op2_reg _ _) fun u2 v2 => ?_
  have e10 : u1.gpr .r10 = BitVec.ofNat 32 n := by
    rw [v1.gpr]
    change s.gpr .r10 - BitVec.ofNat 32 2 = _
    rw [h10, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have e2 : u2.gpr .r2 = p + BitVec.ofNat 32 n := by
    rw [v2.gpr]; change u1.gpr .r12 + u1.gpr .r10 = _
    rw [v1.other _ (by decide), hp, e10]
  have hpn : (p + BitVec.ofNat 32 n).toNat = p.toNat + n := by
    rw [toNat_add_lt (by rw [toNat_imm (by omega)]; omega), toNat_imm (by omega)]
  refine wp_ldrb (a := State.addr p + BitVec.ofNat 64 n) (by decide)
    (by rw [e2, BitVec.add_zero]; exact addr_add (by omega))
    (by rw [v2.rd, v2.wr, v1.rd, v1.wr]; exact hr n (by omega)) fun u3 v3 => ?_
  refine wp_ldrb (a := State.addr p + BitVec.ofNat 64 (n + 1)) (by decide)
    (by rw [v3.other _ (by decide), e2, addr_add (by omega), addr_add (by omega), Offset.add_add])
    (by rw [v3.rd, v3.wr, v2.rd, v2.wr, v1.rd, v1.wr]; exact hr (n + 1) (by omega)) fun u4 v4 => ?_
  refine wp_dp (op2_lsl (by decide)) fun t vt => WP.block_nil ?_
  have m4 : u4.mem = s.mem := by rw [v4.mem, v3.mem, v2.mem, v1.mem]
  refine ⟨(v1.rest (by decide)).trans ((v2.rest (by decide)).trans ((v3.rest (by decide)).trans
      ((v4.rest (by decide)).trans (vt.rest (by decide))))), by rw [vt.mem, m4], ?_, ?_⟩
  · rw [vt.other _ (by decide), v4.other _ (by decide), v3.other _ (by decide),
      v2.other _ (by decide), e10]
  · rw [vt.gpr]
    show (u4.gpr .r11 + u4.gpr .r3 <<< 8).toNat = _
    have e11 : (u4.gpr .r11).toNat = (s.mem (State.addr p + BitVec.ofNat 64 n)).toNat := by
      rw [v4.other _ (by decide), v3.gpr, BitVec.toNat_setWidth_of_le (by decide), v2.mem, v1.mem]
    have e3 : (u4.gpr .r3).toNat = (s.mem (State.addr p + BitVec.ofNat 64 (n + 1))).toNat := by
      rw [v4.gpr, BitVec.toNat_setWidth_of_le (by decide), v3.mem, v2.mem, v1.mem]
    have b1 := (s.mem (State.addr p + BitVec.ofNat 64 (n + 1))).isLt
    have b0 := (s.mem (State.addr p + BitVec.ofNat 64 n)).isLt
    have e3' : (u4.gpr .r3 <<< 8).toNat = 256 * (s.mem (State.addr p + BitVec.ofNat 64 (n + 1))).toNat := by
      rw [toNat_shl, e3, Nat.mod_eq_of_lt (by omega)]; omega
    rw [toNat_add_lt (by rw [e11, e3']; omega), e11, e3']

/-! ## The byte loop -/

/-- What the loops change. -/
structure LoopKeep (b : BitVec 32) (o : Nat) (s t : State) : Prop where
  rest : Rest [.r1, .r2, .r3, .r4, .r5, .r9, .r10, .r11] s t
  frame : Frame [limbsR b TF, limbsR b o] s.mem t.mem

theorem LoopKeep.refl (b : BitVec 32) (o : Nat) (s : State) : LoopKeep b o s s :=
  ⟨Rest.refl _ _, Frame.refl _ _⟩

theorem LoopKeep.trans {o : Nat} {s t u : State} (h : LoopKeep b o s t) (h' : LoopKeep b o t u) :
    LoopKeep b o s u := ⟨h.rest.trans h'.rest, h.frame.trans h'.frame⟩

/-- After the steps from the top down to byte `n`. -/
structure ByteInv (b : BitVec 32) (o N : Nat) (p : Addr) (s0 : State) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ N
  even : n % 2 = 0
  counter : s.gpr .r10 = BitVec.ofNat 32 n
  limbs : Lim28 s.mem (State.addr b) o
  value : V28 s.mem (State.addr b) o = decodeLE ((bytesAt s0.mem p N).drop n) % L
  keeps : LoopKeep b o s0 s

theorem byteLoop_ok {o N : Nat} (ho : Buf o) {p : BitVec 32} {s0 : State} (hc : Ctx8 b s0)
    (h6 : s0.gpr .r6 = mask16) (hp : s0.gpr .r12 = p) (hfit : p.toNat + N ≤ 2 ^ 32)
    (hread : ∀ i < N, InRegions (s0.rd ++ s0.wr) (State.addr p + BitVec.ofNat 64 i) 1)
    (hsep : ∀ r ∈ [limbsR b TF, limbsR b o], (⟨State.addr p, N⟩ : Region).Disjoint r)
    {n0 : Nat} (hn0 : 0 < n0) (hle : n0 ≤ N) (heven : n0 % 2 = 0)
    (h10 : s0.gpr .r10 = BitVec.ofNat 32 n0) (hl : Lim28 s0.mem (State.addr b) o)
    (hv : V28 s0.mem (State.addr b) o = decodeLE ((bytesAt s0.mem (State.addr p) N).drop n0) % L) :
    WP isa (.loop (.block (byteStep o)) .ne) s0 fun t => LoopKeep b o s0 t ∧
      Lim28 t.mem (State.addr b) o ∧
      V28 t.mem (State.addr b) o = decodeLE (bytesAt s0.mem (State.addr p) N) % L := by
  have hN : N ≤ 2 ^ 32 := by omega
  apply WP.loop (ByteInv b o N (State.addr p) s0) (n := n0)
  · intro n s hi
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by have := hi.even; have := hi.positive; omega⟩
    have hk : k + 2 ≤ N := hi.bound
    have hcs : Ctx8 b s := hc.of_rest hi.keeps.rest (by decide)
    have hps : s.gpr .r12 = p := (hi.keeps.rest.gpr _ (by decide)).trans hp
    have hrs : ∀ i < N, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1 := by
      rw [hi.keeps.rest.rd, hi.keeps.rest.wr]; exact hread
    unfold byteStep
    rw [List.append_assoc]
    refine WP.append (readBytes_ok hk hps hfit hi.counter hrs) fun u ⟨ku, mu, cu, wu⟩ => ?_
    have hcu : Ctx8 b u := hcs.of_rest ku (by decide)
    have h6u : u.gpr .r6 = mask16 :=
      (ku.gpr _ (by decide)).trans ((hi.keeps.rest.gpr _ (by decide)).trans h6)
    have hwu : (u.gpr .r11).toNat < 65536 := by
      rw [wu]
      have := (s.mem (State.addr p + BitVec.ofNat 64 k)).isLt
      have := (s.mem (State.addr p + BitVec.ofNat 64 (k + 1))).isLt
      omega
    refine WP.append (step_ok ho hcu h6u (mu ▸ hi.limbs)
      (by rw [mu, hi.value]; exact Nat.mod_lt _ L_pos) hwu) fun v ⟨kv, lv, vv⟩ => ?_
    refine wp_cmp (op2_imm (by decide)) fun t ht hz => WP.block_nil ?_
    have mb : ∀ i < N, s.mem (State.addr p + BitVec.ofNat 64 i) =
        s0.mem (State.addr p + BitVec.ofNat 64 i) :=
      fun i hi' => hi.keeps.frame.bytes hsep (by show N ≤ 2 ^ 64; omega) hi'
    have val : V28 t.mem (State.addr b) o = decodeLE ((bytesAt s0.mem (State.addr p) N).drop k) % L := by
      rw [ht.mem, vv, wu, mu, hi.value, mod_fold, mb k (by omega), mb (k + 1) (by omega),
        decode_drop2 _ _ hk]
    have keep : LoopKeep b o s0 t := hi.keeps.trans
      ⟨(ku.mono (by decide)).trans ((kv.rest.mono (by decide)).trans (ht.rest _)),
        by rw [ht.mem, ← mu]; exact kv.frame⟩
    have c10 : t.gpr .r10 = BitVec.ofNat 32 k := by
      rw [ht.gpr, kv.rest.gpr _ (by decide), cu]
    have zt : t.z = decide (k = 0) := by
      have he : BitVec.ofNat 32 k - (0 : BitVec 32) = BitVec.ofNat 32 k := BitVec.sub_zero _
      rw [hz, kv.rest.gpr _ (by decide), cu, he, ofNat_beq_zero (by omega)]
    by_cases k0 : k = 0
    · subst k0
      refine .inl ⟨by rw [eval_ne, zt]; rfl, keep, ht.mem ▸ lv, ?_⟩
      simpa only [List.drop_zero] using val
    · refine .inr ⟨by rw [eval_ne, zt]; simp only [k0, decide_false, Bool.not_false], k, by omega,
        ⟨by omega, by omega, by have := hi.even; omega, c10, ht.mem ▸ lv, val, keep⟩⟩
  · exact ⟨hn0, hle, heven, h10, hl, hv, LoopKeep.refl _ _ _⟩

/-! ## The product's limbs -/

theorem ACC_eq : Impl.X448.Arm.ACC = 3584 := rfl

theorem readLimb_ok {s : State} (hc : Ctx8 b s) {j : Nat} (hj : j < 56)
    (h10 : s.gpr .r10 = BitVec.ofNat 32 (4 * (j + 1))) :
    WP isa (.block readLimb) s fun t =>
      Rest [.r2, .r10, .r11] s t ∧ t.mem = s.mem ∧ t.gpr .r10 = BitVec.ofNat 32 (4 * j) ∧
      (t.gpr .r11).toNat = limb s.mem (State.addr b) Impl.X448.Arm.ACC j := by
  have hA := ACC_eq
  have hfit := hc.fit
  unfold readLimb
  refine wp_dp (op2_imm (by decide)) fun u1 v1 => wp_dp (op2_reg _ _) fun u2 v2 => ?_
  have e10 : u1.gpr .r10 = BitVec.ofNat 32 (4 * j) := by
    rw [v1.gpr]
    change s.gpr .r10 - BitVec.ofNat 32 4 = _
    rw [h10, show 4 * (j + 1) = 4 * j + 4 by omega, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have e2 : u2.gpr .r2 = b + BitVec.ofNat 32 (4 * j) := by
    rw [v2.gpr]; change u1.gpr .r0 + u1.gpr .r10 = _
    rw [v1.other _ (by decide), hc.r0, e10]
  refine wp_ldr (a := State.addr b + BitVec.ofNat 64 (Impl.X448.Arm.ACC + 4 * j)) (by omega)
    (by rw [e2, Offset.add_add]; rw [Nat.add_comm]; exact addr_add (by omega))
    (by rw [v2.rd, v2.wr, v1.rd, v1.wr]; exact hc.inR (by omega)) fun t vt => WP.block_nil ?_
  refine ⟨(v1.rest (by decide)).trans ((v2.rest (by decide)).trans (vt.rest (by decide))),
    by rw [vt.mem, v2.mem, v1.mem], by rw [vt.other _ (by decide), v2.other _ (by decide), e10], ?_⟩
  rw [vt.gpr, v2.mem, v1.mem]; rfl

/-- The number of the product's limbs from `j` up. -/
abbrev accFrom (m : Mem) (B : Addr) (j : Nat) : Nat :=
  val16 (fun i => limb m B Impl.X448.Arm.ACC (j + i)) (56 - j)

theorem accFrom_step (m : Mem) (B : Addr) {j : Nat} (hj : j < 56) :
    accFrom m B j = limb m B Impl.X448.Arm.ACC j + 65536 * accFrom m B (j + 1) := by
  unfold accFrom
  rw [show 56 - j = 1 + (56 - (j + 1)) by omega, val16_append]
  simp only [val16, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero]
  congr 1
  refine congrArg (65536 * ·) (val16_congr fun i _ => ?_)
  rw [show j + (1 + i) = j + 1 + i by omega]

/-- After the steps from the top limb down to limb `j`. -/
structure LimbInv (b : BitVec 32) (s0 : State) (j : Nat) (s : State) : Prop where
  positive : 0 < j
  bound : j ≤ 56
  counter : s.gpr .r10 = BitVec.ofNat 32 (4 * j)
  limbs : Lim28 s.mem (State.addr b) RA
  value : V28 s.mem (State.addr b) RA = accFrom s0.mem (State.addr b) j % L
  keeps : LoopKeep b RA s0 s

theorem limbLoop_ok {s0 : State} (hc : Ctx8 b s0) (h6 : s0.gpr .r6 = mask16)
    (hacc : ∀ j < 56, limb s0.mem (State.addr b) Impl.X448.Arm.ACC j < 65536)
    (h10 : s0.gpr .r10 = BitVec.ofNat 32 (4 * 56)) (hl : Lim28 s0.mem (State.addr b) RA)
    (hv : V28 s0.mem (State.addr b) RA = 0) :
    WP isa (.loop (.block limbStep) .ne) s0 fun t => LoopKeep b RA s0 t ∧
      Lim28 t.mem (State.addr b) RA ∧
      V28 t.mem (State.addr b) RA = val16 (limb s0.mem (State.addr b) Impl.X448.Arm.ACC) 56 % L := by
  have hA := ACC_eq
  have hT := TF_eq
  have hR : RA = 192 := rfl
  have ho : Buf RA := ⟨by omega, by omega⟩
  apply WP.loop (LimbInv b s0) (n := 56)
  · intro n s hi
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by have := hi.positive; omega⟩
    have hj : j < 56 := hi.bound
    have hcs : Ctx8 b s := hc.of_rest hi.keeps.rest (by decide)
    have la : ∀ i < 56, limb s.mem (State.addr b) Impl.X448.Arm.ACC i =
        limb s0.mem (State.addr b) Impl.X448.Arm.ACC i := fun i hi' =>
      wd_frame hi.keeps.frame fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact Offset.disjoint _ (by omega) (by omega) (by omega)
    unfold limbStep
    rw [List.append_assoc]
    refine WP.append (readLimb_ok hcs hj hi.counter) fun u ⟨ku, mu, cu, wu⟩ => ?_
    have hcu : Ctx8 b u := hcs.of_rest ku (by decide)
    have h6u : u.gpr .r6 = mask16 :=
      (ku.gpr _ (by decide)).trans ((hi.keeps.rest.gpr _ (by decide)).trans h6)
    have hwu : (u.gpr .r11).toNat < 65536 := by rw [wu, la j hj]; exact hacc j hj
    refine WP.append (step_ok ho hcu h6u (mu ▸ hi.limbs)
      (by rw [mu, hi.value]; exact Nat.mod_lt _ L_pos) hwu) fun v ⟨kv, lv, vv⟩ => ?_
    refine wp_cmp (op2_imm (by decide)) fun t ht hz => WP.block_nil ?_
    have val : V28 t.mem (State.addr b) RA = accFrom s0.mem (State.addr b) j % L := by
      rw [ht.mem, vv, wu, mu, hi.value, mod_fold, la j hj, accFrom_step _ _ hj]
    have keep : LoopKeep b RA s0 t := hi.keeps.trans
      ⟨(ku.mono (by decide)).trans ((kv.rest.mono (by decide)).trans (ht.rest _)),
        by rw [ht.mem, ← mu]; exact kv.frame⟩
    have c10 : t.gpr .r10 = BitVec.ofNat 32 (4 * j) := by
      rw [ht.gpr, kv.rest.gpr _ (by decide), cu]
    have zt : t.z = decide (j = 0) := by
      have he : BitVec.ofNat 32 (4 * j) - (0 : BitVec 32) = BitVec.ofNat 32 (4 * j) := BitVec.sub_zero _
      rw [hz, kv.rest.gpr _ (by decide), cu, he, ofNat_beq_zero (by omega)]
      exact decide_eq_decide.mpr (by omega)
    by_cases j0 : j = 0
    · subst j0
      refine .inl ⟨by rw [eval_ne, zt]; rfl, keep, ht.mem ▸ lv, ?_⟩
      rw [val]
      exact congrArg (· % L) (val16_congr fun i _ => by rw [Nat.zero_add])
    · refine .inr ⟨by rw [eval_ne, zt]; simp only [j0, decide_false, Bool.not_false], j, by omega,
        ⟨by omega, by omega, c10, ht.mem ▸ lv, val, keep⟩⟩
  · refine ⟨by decide, by decide, h10, hl, ?_, LoopKeep.refl _ _ _⟩
    rw [hv]
    exact (Nat.zero_mod _).symm.trans (by rfl)

/-! ## The remainders the loops start from -/

theorem zeroR_ok {o : Nat} (ho : o + 112 ≤ 4096) {s : State} (hc : Ctx8 b s) :
    WP isa (.block (zeroR o)) s fun t =>
      Rest [.r3] s t ∧ Frame [limbsR b o] s.mem t.mem ∧ ∀ k < 28, limb t.mem (State.addr b) o k = 0 := by
  unfold zeroR
  refine wp_mov (op2_imm (by decide)) fun s1 u1 => ?_
  have hc1 := hc.of_rest (u1.rest (ws := [.r3]) (by decide)) (by decide)
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n t => Rest [] s1 t ∧ Frame [⟨State.addr b + BitVec.ofNat 64 o, 4 * n⟩] s1.mem t.mem ∧
      ∀ k < n, limb t.mem (State.addr b) o k = 0)
    (fun n t hn ⟨h1, h2, h3⟩ => ?_) 28 (Nat.le_refl _) s1
    ⟨Rest.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun t ⟨h1, h2, h3⟩ => ⟨(u1.rest (by decide)).trans (h1.mono (by decide)),
      by rw [← u1.mem]; exact h2, h3⟩
  refine str0_ok (hc1.of_rest h1 (by decide)) (d := o + 4 * n) (by omega) fun t2 v2 =>
    WP.block_nil ⟨h1.trans (v2.rest _), ?_, fun k hk => ?_⟩
  · rw [v2.mem]
    exact (h2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).writeW
      (List.mem_singleton_self _) (t.gpr .r3)
      (Offset.contains _ (d := o + 4 * n) (n := 4) (e := o) (k := 4 * (n + 1)) (by omega) (by omega)
        (by omega))
  · show wd t2.mem _ _ = 0
    rw [v2.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega)]; exact h3 k hk
    · rw [wd_write_self, h1.gpr _ (by decide), u1.gpr]; rfl

theorem V28_zero {m : Mem} {B : Addr} {o : Nat} (h : ∀ k < 28, limb m B o k = 0) : V28 m B o = 0 :=
  (val16_congr h).trans (val16_zero_fn 28)

theorem Lim28_zero {m : Mem} {B : Addr} {o : Nat} (h : ∀ k < 28, limb m B o k = 0) : Lim28 m B o :=
  fun k hk => by rw [h k hk]; decide


end

end VG.Proof.Ed448.Arm

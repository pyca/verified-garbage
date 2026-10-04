import VerifiedGarbage.Proof.Ed448.Arm.ScalarLoop
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# Ed448 scalar arithmetic on ARMv7: entry and exit

The callee-saved registers saved in the working space (`saveAt_ok`) and
restored (`restore_ok`), the remainders the input loops start from
(`reduce114_ok`, `reduce57_ok`), and the result: the remainder's limbs as 56
bytes and a zero byte (`pack_ok`), which are its encoding (`encode_57`).
-/

namespace VG.Proof.Ed448.Arm

open VG VG.Arm VG.Impl.Ed448.Arm VG.Proof.X25519.Arm
open VG.Spec.Ed448 (L bytesAt decodeLE encodeLE)

/-- The registers `g` saved at `[0, 32)` of the working space at `B`. -/
def Saved (B : Addr) (g : Reg → BitVec 32) (m : Mem) : Prop :=
  ∀ i < 8, m.readW (B + BitVec.ofNat 64 (4 * i)) 32 = g (savedReg i)

section
variable {b : BitVec 32}

theorem saveAt_ok {s : State} {base : Reg} (h3 : s.gpr base = b) (hfit : b.toNat + 8192 ≤ 2 ^ 32)
    (hw : (⟨State.addr b, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block (saveAt base)) s fun s' =>
      Saved (State.addr b) s.gpr s'.mem ∧ Frame [⟨State.addr b, 32⟩] s.mem s'.mem ∧
        s'.gpr = s.gpr ∧ Rest [] s s' := by
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ i < n, s'.mem.readW (State.addr b + BitVec.ofNat 64 (4 * i)) 32 = s.gpr (savedReg i)) ∧
      Frame [⟨State.addr b, 4 * n⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ Rest [] s s')
    (fun n s' hn ⟨h1, h2, h3', h4⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, rfl, Rest.refl _ _⟩)
    fun s' h => ⟨h.1, h.2.1, h.2.2⟩
  refine wp_str (a := State.addr b + BitVec.ofNat 64 (4 * n)) (by omega)
    (by rw [h3', h3]; exact addr_add (by omega)) (by rw [h4.wr]; exact in_base hw (by omega) (by omega))
    fun s2 u2 => WP.block_nil ⟨fun i hi => ?_, ?_, by rw [u2.gpr, h3'], h4.trans (u2.rest _)⟩
  · rw [u2.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]; exact h1 i hi
    · rw [Mem.readW_writeW_self32, h3']
  · rw [u2.mem]
    exact (h2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))

theorem restore_ok {s : State} (hc : Ctx8 b s) {g : Reg → BitVec 32} (hs : Saved (State.addr b) g s.mem) :
    WP isa (.block restore) s fun s' => (∀ i < 8, s'.gpr (savedReg i) = g (savedReg i)) ∧
      Rest [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s s' ∧ s'.mem = s.mem := by
  have hsr : ∀ i < 8, savedReg i ∈ [Reg.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] := by decide
  have hinj : ∀ i < 8, ∀ j < 8, savedReg i = savedReg j → i = j := by decide
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun n s' => (∀ i < n, s'.gpr (savedReg i) = g (savedReg i)) ∧
      Rest [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s s' ∧ s'.mem = s.mem)
    (fun n s' hn ⟨hl, hr, hm⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Rest.refl _ _, rfl⟩) fun s' h => h
  refine ldr0_ok (hc.of_rest hr (by decide)) (d := 4 * n) (by omega) fun s1 u1 =>
    WP.block_nil ⟨fun i hi => ?_, hr.trans (u1.rest (hsr n hn)), by rw [u1.mem, hm]⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | rfl
  · rw [u1.other _ (fun e => absurd (hinj _ (by omega) _ hn e) (by omega))]; exact hl i h'
  · rw [u1.gpr, hm, hs i hn]

/-- The saved registers stay where no code writes. -/
theorem Saved.frame {g : Reg → BitVec 32} {m m' : Mem} (hs : Saved (State.addr b) g m) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, ∀ i < 8, Region.Disjoint ⟨State.addr b + BitVec.ofNat 64 (4 * i), 4⟩ r) :
    Saved (State.addr b) g m' := fun i hi => by
  rw [hf.readW (Region.contains_self _ _) (fun r hr => hd r hr i hi) (by decide)]; exact hs i hi

/-! ## The remainders of the inputs -/

theorem init114_ok {o : Nat} (ho : Buf o) {s : State} (hc : Ctx8 b s) :
    WP isa (.block (zeroR o ++ ([.mov .r10 (.imm 114)] : List Instr))) s fun v => LoopKeep b o s v ∧
      v.gpr .r10 = BitVec.ofNat 32 114 ∧ Lim28 v.mem (State.addr b) o ∧ V28 v.mem (State.addr b) o = 0 :=
  WP.append (zeroR_ok ho.2 hc) fun u ⟨ku, fu, zu⟩ =>
    wp_mov (op2_imm (by decide)) fun v hv => WP.block_nil
      ⟨⟨(ku.mono (by decide)).trans (hv.rest (by decide)), by rw [hv.mem]; exact fu.mono (by simp)⟩,
        hv.gpr, by rw [hv.mem]; exact Lim28_zero zu, by rw [hv.mem]; exact V28_zero zu⟩

/-- The bytes of an input across a frame of regions it does not overlap. -/
theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {N : Nat}
    (hd : ∀ r ∈ rs, (⟨p, N⟩ : Region).Disjoint r) (hN : N ≤ 2 ^ 64) :
    bytesAt m' p N = bytesAt m p N := by
  unfold bytesAt; apply List.map_congr_left
  intro n hn
  exact hf.bytes hd hN (List.mem_range.mp hn)

theorem reduce114_ok {o : Nat} (ho : Buf o) {p : BitVec 32} {s : State} (hc : Ctx8 b s)
    (h6 : s.gpr .r6 = mask16) (hp : s.gpr .r12 = p) (hfit : p.toNat + 114 ≤ 2 ^ 32)
    (hread : ∀ i < 114, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1)
    (hsep : ∀ r ∈ [limbsR b TF, limbsR b o], (⟨State.addr p, 114⟩ : Region).Disjoint r) :
    WP isa (reduce114 o) s fun t => LoopKeep b o s t ∧ Lim28 t.mem (State.addr b) o ∧
      V28 t.mem (State.addr b) o = decodeLE (bytesAt s.mem (State.addr p) 114) % L := by
  unfold reduce114
  refine WP.seq (WP.mono (init114_ok ho hc) fun v ⟨kv, cv, lv, vv⟩ => ?_)
  have mb := bytesAt_frame kv.frame hsep (by decide)
  refine WP.mono (byteLoop_ok (N := 114) ho (hc.of_rest kv.rest (by decide))
    ((kv.rest.gpr _ (by decide)).trans h6) ((kv.rest.gpr _ (by decide)).trans hp) hfit
    (by rw [kv.rest.rd, kv.rest.wr]; exact hread) hsep (n0 := 114) (by decide) (by decide)
    (by decide) cv lv (by rw [vv, List.drop_eq_nil_of_le (by rw [bytesAt_length]), show decodeLE [] = 0 from rfl,
      Nat.zero_mod]))
    fun t ⟨kt, lt, vt⟩ => ⟨kv.trans kt, lt, by rw [vt, mb]⟩

theorem init57_ok {o : Nat} (ho : Buf o) {p : BitVec 32} {s : State} (hc : Ctx8 b s)
    (hp : s.gpr .r12 = p) (hfit : p.toNat + 57 ≤ 2 ^ 32)
    (hread : ∀ i < 57, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1)
    (hsep : ∀ r ∈ [limbsR b TF, limbsR b o], (⟨State.addr p, 57⟩ : Region).Disjoint r) :
    WP isa (.block (zeroR o ++ ([.ldrb .r3 .r12 56, .str .r3 .r0 o, .mov .r10 (.imm 56)] : List Instr))) s fun v =>
      LoopKeep b o s v ∧ v.gpr .r10 = BitVec.ofNat 32 56 ∧ Lim28 v.mem (State.addr b) o ∧
      V28 v.mem (State.addr b) o = decodeLE ((bytesAt s.mem (State.addr p) 57).drop 56) % L := by
  obtain ⟨ho1, ho2⟩ := ho
  have hT := TF_eq
  refine WP.append (zeroR_ok ho2 hc) fun u ⟨ku, fu, zu⟩ => ?_
  have hpu : u.gpr .r12 = p := (ku.gpr _ (by decide)).trans hp
  refine wp_ldrb (a := State.addr p + BitVec.ofNat 64 56) (by decide)
    (by rw [hpu]; exact addr_add (by omega)) (by rw [ku.rd, ku.wr]; exact hread 56 (by decide))
    fun u1 v1 => ?_
  refine str0_ok (hc.of_rest (ku.trans (v1.rest (ws := [.r3]) (by decide))) (by decide)) (d := o)
    (by omega) fun u2 v2 => wp_mov (op2_imm (by decide)) fun v hv => WP.block_nil ?_
  have m2 : v.mem = u.mem.writeW (State.addr b + BitVec.ofNat 64 (o + 4 * 0))
      ((u.mem (State.addr p + BitVec.ofNat 64 56)).setWidth 32) := by
    rw [hv.mem, v2.mem, v1.gpr, v1.mem]; rfl
  have lv : ∀ k < 28, limb v.mem (State.addr b) o k =
      if k = 0 then (u.mem (State.addr p + BitVec.ofNat 64 56)).toNat else 0 := by
    intro k hk
    show wd v.mem _ _ = _
    rw [m2]
    by_cases k0 : k = 0
    · subst k0
      rw [wd_write_self, BitVec.toNat_setWidth_of_le (by decide)]; rfl
    · rw [wd_write_other _ _ _ (by omega) (by omega) (by omega), ite_eq_right k0]; exact zu k hk
  have fv : Frame [limbsR b o] s.mem v.mem := by
    rw [m2]
    exact fu.writeW (List.mem_singleton_self _) _ (Offset.contains _ (d := o + 4 * 0) (n := 4) (e := o)
      (k := 112) (by omega) (by omega) (by omega))
  have hbyte : (u.mem (State.addr p + BitVec.ofNat 64 56)).toNat =
      (s.mem (State.addr p + BitVec.ofNat 64 56)).toNat := by
    rw [fu.bytes (R := ⟨State.addr p, 57⟩) (fun r hr => hsep r (by
      simp only [List.mem_singleton] at hr; simp [hr])) (by show 57 ≤ 2 ^ 64; omega) (by decide : 56 < 57)]
  have hlt := (u.mem (State.addr p + BitVec.ofNat 64 56)).isLt
  refine ⟨⟨((ku.mono (by decide)).trans ((v1.rest (by decide)).trans ((v2.rest _).trans
    (hv.rest (by decide))))), fv.mono (by simp)⟩, hv.gpr, fun k hk => ?_, ?_⟩
  · rw [lv k hk]; split
    · omega
    · decide
  · rw [decode_drop1 _ _ (by decide : 56 + 1 = 57), ← hbyte]
    have hL : 256 < L := by decide +kernel
    rw [Nat.mod_eq_of_lt (by omega)]
    unfold V28
    rw [show (28 : Nat) = 1 + 27 from rfl, val16_append,
      val16_congr (n := 27) (g := fun _ => 0) (fun k hk => by rw [lv _ (by omega), ite_eq_right (by omega)]),
      val16_zero_fn]
    simp only [val16, lv 0 (by decide), ite_true, Nat.mul_zero, Nat.pow_zero, Nat.one_mul,
      Nat.zero_add, Nat.add_zero]

theorem reduce57_ok {o : Nat} (ho : Buf o) {p : BitVec 32} {s : State} (hc : Ctx8 b s)
    (h6 : s.gpr .r6 = mask16) (hp : s.gpr .r12 = p) (hfit : p.toNat + 57 ≤ 2 ^ 32)
    (hread : ∀ i < 57, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1)
    (hsep : ∀ r ∈ [limbsR b TF, limbsR b o], (⟨State.addr p, 57⟩ : Region).Disjoint r) :
    WP isa (reduce57 o) s fun t => LoopKeep b o s t ∧ Lim28 t.mem (State.addr b) o ∧
      V28 t.mem (State.addr b) o = decodeLE (bytesAt s.mem (State.addr p) 57) % L := by
  unfold reduce57
  refine WP.seq (WP.mono (init57_ok ho hc hp hfit hread hsep) fun v ⟨kv, cv, lv, vv⟩ => ?_)
  have mb := bytesAt_frame kv.frame hsep (by decide)
  refine WP.mono (byteLoop_ok (N := 57) ho (hc.of_rest kv.rest (by decide))
    ((kv.rest.gpr _ (by decide)).trans h6) ((kv.rest.gpr _ (by decide)).trans hp) hfit
    (by rw [kv.rest.rd, kv.rest.wr]; exact hread) hsep (n0 := 56) (by decide) (by decide)
    (by decide) cv lv (by rw [vv, mb])) fun t ⟨kt, lt, vt⟩ => ⟨kv.trans kt, lt, by rw [vt, mb]⟩

/-! ## The result -/

theorem byte_eq {v : BitVec 32} {n : Nat} (h : v.toNat = n) : v.setWidth 8 = BitVec.ofNat 8 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, h]

/-- After `k` limbs of `packLimb`. -/
structure PackInv (q : Addr) (f : Nat → Nat) (s0 : State) (k : Nat) (s : State) : Prop where
  rest : Rest [.r3] s0 s
  frame : Frame [⟨q, 2 * k⟩] s0.mem s.mem
  b0 : ∀ i < k, s.mem (q + BitVec.ofNat 64 (2 * i)) = BitVec.ofNat 8 (f i)
  b1 : ∀ i < k, s.mem (q + BitVec.ofNat 64 (2 * i + 1)) = BitVec.ofNat 8 (f i / 256)

theorem pack_ok {q : BitVec 32} {o : Nat} (ho : o + 112 ≤ 4096) {s0 : State} (hc : Ctx8 b s0)
    (hq : s0.gpr .r12 = q) (hfit : q.toNat + 57 ≤ 2 ^ 32)
    (hw : (⟨State.addr q, 57⟩ : Region) ∈ s0.wr)
    (hsep : (⟨State.addr q, 57⟩ : Region).Disjoint ⟨State.addr b, 8192⟩) :
    WP isa (.block ((List.range 28).flatMap (packLimb o))) s0
      (PackInv (State.addr q) (limb s0.mem (State.addr b) o) s0 28) := by
  let O := State.addr q
  refine wp_range_flatMap (M := isa) (PackInv O (limb s0.mem (State.addr b) o) s0)
    (fun k s hk h => ?_) 28 (Nat.le_refl _) s0
    ⟨Rest.refl _ _, Frame.refl _ _, fun _ h => by omega, fun _ h => by omega⟩
  have hcs := hc.of_rest h.rest (by decide)
  have hq' : s.gpr .r12 = q := (h.rest.gpr _ (by decide)).trans hq
  have he : wd s.mem (State.addr b) (o + 4 * k) = limb s0.mem (State.addr b) o k :=
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (hsep.symm.sub_left (Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix (by omega))
  unfold packLimb
  refine ldr0_ok hcs (by omega) fun s1 u1 => ?_
  have e1 : (s1.gpr .r3).toNat = limb s0.mem (State.addr b) o k := by rw [u1.gpr]; exact he
  refine wp_strb (a := O + BitVec.ofNat 64 (2 * k)) (by omega)
    (by rw [u1.other _ (by decide), hq', addr_add (by omega)])
    (by rw [u1.wr, h.rest.wr]; exact in_base hw (by omega) (by omega))
    fun s2 u2 => wp_mov (op2_lsr (by decide)) fun s3 u3 => ?_
  refine wp_strb (a := O + BitVec.ofNat 64 (2 * k + 1)) (by omega)
    (by rw [u3.other _ (by decide), u2.gpr, u1.other _ (by decide), hq', addr_add (by omega)])
    (by rw [u3.wr, u2.wr, u1.wr, h.rest.wr]; exact in_base hw (by omega) (by omega))
    fun t ht => WP.block_nil ?_
  have hm : t.mem = (s.mem.writeW (O + BitVec.ofNat 64 (2 * k)) ((s1.gpr .r3).setWidth 8)).writeW
      (O + BitVec.ofNat 64 (2 * k + 1)) ((s1.gpr .r3 >>> 8).setWidth 8) := by
    rw [ht.mem, u3.gpr, u2.gpr, u3.mem, u2.mem, u1.mem]
  have ne : ∀ i j : Nat, i < 57 → j < 57 → i ≠ j → O + BitVec.ofNat 64 i ≠ O + BitVec.ofNat 64 j :=
    fun i j hi hj hij => Offset.add_ofNat_ne _ (by omega) (by omega) hij
  refine ⟨h.rest.trans ((u1.rest (by decide)).trans ((u2.rest _).trans
    ((u3.rest (by decide)).trans (ht.rest _)))), ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [hm]
    refine ((h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega)⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · rw [hm, VG.WriteBytes.writeW8_apply, VG.WriteBytes.writeW8_apply,
      ite_eq_right (ne _ _ (by omega) (by omega) (by omega))]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_eq_right (ne _ _ (by omega) (by omega) (by omega))]; exact h.b0 i hi
    · rw [ite_eq_left rfl]; exact byte_eq e1
  · rw [hm, VG.WriteBytes.writeW8_apply, VG.WriteBytes.writeW8_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [ite_eq_right (ne _ _ (by omega) (by omega) (by omega)),
        ite_eq_right (ne _ _ (by omega) (by omega) (by omega))]
      exact h.b1 i hi
    · rw [ite_eq_left rfl]; exact byte_eq (by rw [toNat_shr, e1])

/-- Twenty-eight 16-bit limbs and a zero byte are the 57-byte encoding of
their number. -/
theorem encode_57 {m : Mem} {q : Addr} {f : Nat → Nat} (hl : ∀ k < 28, f k < 65536)
    (h0 : ∀ k < 28, m (q + BitVec.ofNat 64 (2 * k)) = BitVec.ofNat 8 (f k))
    (h1 : ∀ k < 28, m (q + BitVec.ofNat 64 (2 * k + 1)) = BitVec.ofNat 8 (f k / 256))
    (h56 : m (q + BitVec.ofNat 64 56) = 0) :
    bytesAt m q 57 = encodeLE 57 (val16 f 28) := by
  let g : Nat → Nat := fun k => if k < 28 then f k else 0
  have hg : ∀ k < 29, g k < 65536 := fun k _ => by
    simp only [g]; split
    · exact hl k (by omega)
    · decide
  have hv : val16 f 28 = val16 g 29 := by
    have e1 := val16_succ g 28
    have e2 : g 28 = 0 := rfl
    rw [e2] at e1
    have e3 : val16 f 28 = val16 g 28 := val16_congr fun k hk => (ite_eq_left hk).symm
    exact e3.trans ((Nat.add_zero _).symm.trans
      ((congrArg (val16 g 28 + ·) (Nat.mul_zero _).symm).trans e1.symm))
  apply List.ext_getElem (by rw [bytesAt_length]; simp only [encodeLE, List.length_map, List.length_range])
  intro i hi _
  rw [bytesAt_length] at hi
  simp only [bytesAt, encodeLE, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, hv]
  obtain ⟨k, rfl | rfl⟩ : ∃ k, i = 2 * k ∨ i = 2 * k + 1 := ⟨i / 2, by omega⟩
  · have hd := val16_div hg (k := k) (by omega)
    rw [show 8 * (2 * k) = 16 * k by omega, ← Nat.mod_mod_of_dvd _ (by decide : 256 ∣ 65536), hd]
    by_cases hk : k < 28
    · rw [h0 k hk, BitVec.toNat_ofNat, show g k = f k from ite_eq_left hk]
    · rw [show 2 * k = 56 by omega, h56, show g k = 0 from ite_eq_right hk]; rfl
  · have hk : k < 28 := by omega
    have hd := val16_div hg (k := k) (by omega)
    rw [show 8 * (2 * k + 1) = 16 * k + 8 by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul,
      show (2 : Nat) ^ 8 = 256 from rfl, h1 k hk, BitVec.toNat_ofNat,
      ← Nat.mod_mul_right_div_self (val16 g 29 / 2 ^ (16 * k)) 256 256,
      show (256 : Nat) * 256 = 65536 from rfl, hd, show g k = f k from ite_eq_left hk]
    have := hl k hk
    omega

theorem OUT_eq : OUT = 32 := rfl

/-- `output o`: the remainder at `o` as 57 bytes at `r12`, and the
callee-saved registers restored. -/
theorem output_ok {q : BitVec 32} {o : Nat} (ho : o + 112 ≤ 4096) {s : State} (hc : Ctx8 b s)
    (hl : Lim28 s.mem (State.addr b) o) (hq : s.gpr .r12 = q) (hfit : q.toNat + 57 ≤ 2 ^ 32)
    (hw : (⟨State.addr q, 57⟩ : Region) ∈ s.wr)
    (hsep : (⟨State.addr q, 57⟩ : Region).Disjoint ⟨State.addr b, 8192⟩)
    {g : Reg → BitVec 32} (hs : Saved (State.addr b) g s.mem) :
    WP isa (.block (output o)) s fun t =>
      (∀ i < 8, t.gpr (savedReg i) = g (savedReg i)) ∧
      Rest [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s t ∧
      Frame [⟨State.addr q, 57⟩] s.mem t.mem ∧
      bytesAt t.mem (State.addr q) 57 = encodeLE 57 (V28 s.mem (State.addr b) o) := by
  unfold output
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.append (pack_ok (q := q) (o := o) ho hc hq hfit hw hsep) fun v hv => ?_
  have hcv := hc.of_rest hv.rest (by decide)
  refine wp_mov (op2_imm (by decide)) fun v1 w1 => ?_
  refine wp_strb (a := State.addr q + BitVec.ofNat 64 56) (by decide)
    (by rw [w1.other _ (by decide), hv.rest.gpr _ (by decide), hq]; exact addr_add (by omega))
    (by rw [w1.wr, hv.rest.wr]; exact in_base hw (by decide) (by decide)) fun v2 w2 => ?_
  have m2 : v2.mem = v.mem.writeW (State.addr q + BitVec.ofNat 64 56) (0 : BitVec 8) := by
    rw [w2.mem, w1.gpr, w1.mem]; rfl
  have f2 : Frame [⟨State.addr q, 57⟩] s.mem v2.mem := by
    rw [m2]
    refine (?_ : Frame [⟨State.addr q, 57⟩] s.mem v.mem).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by decide) (by decide))
    exact hv.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by decide)⟩
  have hcv2 := hcv.of_rest ((w1.rest (ws := [.r3])  (by decide)).trans (w2.rest _)) (by decide)
  have hs2 : Saved (State.addr b) g v2.mem :=
    hs.frame f2 fun r hr i hi => by
      rw [List.mem_singleton.mp hr]
      exact (hsep.symm.sub_left (Offset.sub_base _ (by omega)))
  refine WP.mono (restore_ok hcv2 hs2) fun t ⟨gt, kt, mt⟩ => ?_
  have ne : ∀ i j : Nat, i < 57 → j < 57 → i ≠ j →
      State.addr q + BitVec.ofNat 64 i ≠ State.addr q + BitVec.ofNat 64 j :=
    fun i j hi hj hij => Offset.add_ofNat_ne _ (by omega) (by omega) hij
  refine ⟨gt, (hv.rest.mono (by decide)).trans ((w1.rest (by decide)).trans
    ((w2.rest _).trans (kt.mono (by decide)))), by rw [mt]; exact f2, ?_⟩
  rw [mt]
  refine encode_57 (fun k hk => hl k hk) (fun k hk => ?_) (fun k hk => ?_) ?_
  · rw [m2, VG.WriteBytes.writeW8_apply, ite_eq_right (ne _ _ (by omega) (by decide) (by omega))]
    exact hv.b0 k hk
  · rw [m2, VG.WriteBytes.writeW8_apply, ite_eq_right (ne _ _ (by omega) (by decide) (by omega))]
    exact hv.b1 k hk
  · rw [m2, VG.WriteBytes.writeW8_apply, ite_eq_left rfl]

/-- `finish o`: `output o` to the output's address, saved at `OUT`. -/
theorem finish_ok {q : BitVec 32} {o : Nat} (ho : o + 112 ≤ 4096) {s : State} (hc : Ctx8 b s)
    (hl : Lim28 s.mem (State.addr b) o)
    (hq : s.mem.readW (State.addr b + BitVec.ofNat 64 OUT) 32 = q) (hfit : q.toNat + 57 ≤ 2 ^ 32)
    (hw : (⟨State.addr q, 57⟩ : Region) ∈ s.wr)
    (hsep : (⟨State.addr q, 57⟩ : Region).Disjoint ⟨State.addr b, 8192⟩)
    {g : Reg → BitVec 32} (hs : Saved (State.addr b) g s.mem) :
    WP isa (.block (finish o)) s fun t =>
      (∀ i < 8, t.gpr (savedReg i) = g (savedReg i)) ∧
      Rest [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] s t ∧
      Frame [⟨State.addr q, 57⟩] s.mem t.mem ∧
      bytesAt t.mem (State.addr q) 57 = encodeLE 57 (V28 s.mem (State.addr b) o) := by
  have hO := OUT_eq
  unfold finish
  refine ldr0_ok hc (d := OUT) (by omega) fun u hu => ?_
  have hcu := hc.of_rest (hu.rest (ws := [.r12]) (by decide)) (by decide)
  refine WP.mono (output_ok ho hcu (hu.mem ▸ hl) (by rw [hu.gpr, hq]) hfit (by rw [hu.wr]; exact hw)
    hsep (hu.mem ▸ hs)) fun t ⟨gt, kt, ft, bt⟩ => ⟨gt, (hu.rest (by decide)).trans (kt.mono (by decide)),
      by rw [← hu.mem]; exact ft, by rw [bt, hu.mem]⟩

end

end VG.Proof.Ed448.Arm

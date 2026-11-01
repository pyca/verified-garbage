module

public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.Slow
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.P256Field.AddSub
import VerifiedGarbage.Proof.Ed25519.RISCV64.MulFn
public import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldCT
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# P-256's field on RISC-V: the functions

`fn core` (`Impl/Weierstrass/RISCV64/P256Field.lean`) from a state with the
working space at `W` in `a0` and the offsets' low words in `a1`–`a3`
(`fn_ok`): the entry (`entry_ok`) zero-extends the offsets and leaves the
pointers and, in `t0`, the low three bits of their `or`, zero only if the
offsets are multiples of 8 (`aligned_of`); then the operation on the
pointers, or on the byte-wise copies (`slowIn_ok`, `slowOut_ok`). Each
operation meets `CoreOk` (`mulCore_ok`, `addCore_ok`, `subCore_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.RISCV64.P256Field

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Wide VG.Impl.Weierstrass.RISCV64.P256Field
open VG.Proof.X25519.RISCV64 (Ctx Rest)
open VG.Proof.X448.RISCV64.R64 (al8)

/-- What an operation on the pointers `t4`, `t5` and `t2` does, for operands
satisfying `pre`: its result `res` of the operands, written at `[t2]`. -/
def CoreOk (core : Prog isa) (pre : Nat → Nat → Prop) (res : Nat → Nat → Nat → Prop) : Prop :=
  ∀ {W : Addr} {s : State} {a bb o : Nat}, WsAt W s → s.gpr .t4 = W + BitVec.ofNat 64 a →
    s.gpr .t5 = W + BitVec.ofNat 64 bb → s.gpr .t2 = W + BitVec.ofNat 64 o → a % 8 = 0 → bb % 8 = 0 →
    o % 8 = 0 → a + 32 ≤ 8192 → bb + 32 ≤ 8192 → o + 32 ≤ 8192 → Apart bb →
    pre (d4 s.mem (W + BitVec.ofNat 64 a)) (d4 s.mem (W + BitVec.ofNat 64 bb)) →
    WP isa core s fun s' =>
      res (d4 s.mem (W + BitVec.ofNat 64 a)) (d4 s.mem (W + BitVec.ofNat 64 bb)) (d4 s'.mem (W + BitVec.ofNat 64 o)) ∧
      Frame (mulW W o) s.mem s'.mem ∧ (∀ r, r ∉ clobM → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp

/-- Montgomery's product modulo `p`. -/
abbrev mulRes (A B r : Nat) : Prop := r < P ∧ r * 2 ^ 256 % P = A * B % P

theorem mulCore_core : CoreOk mulCore (fun _ B => B < P) mulRes :=
  fun hw h4 h5 h2 ha8 hb8 ho8 ha hb ho hdb hB =>
    WP.mono (mulCore_ok hw h4 h5 h2 ha8 hb8 ho8 ha hb ho hdb hB) fun _ ⟨v1, v2, f, g, rd, wr, sp⟩ =>
      ⟨⟨v1, v2⟩, f, g, rd, wr, sp⟩

theorem addCore_core : CoreOk (.block addCore) (fun A B => A + B < 2 * P) (fun A B r => r = (A + B) % P) :=
  fun hw h4 h5 h2 ha8 hb8 ho8 ha hb ho _ hAB =>
    WP.mono (addCore_ok hw h4 h5 h2 ha8 hb8 ho8 ha hb ho hAB) fun _ ⟨v, f, g, rd, wr, sp⟩ =>
      ⟨v, f.mono (by simp), g, rd, wr, sp⟩

theorem subCore_core : CoreOk (.block subCore) (fun A B => A < P ∧ B < P) (fun A B r => r = (A + P - B) % P) :=
  fun hw h4 h5 h2 ha8 hb8 ho8 ha hb ho _ hAB =>
    WP.mono (subCore_ok hw h4 h5 h2 ha8 hb8 ho8 ha hb ho hAB.1 hAB.2) fun _ ⟨v, f, g, rd, wr, sp⟩ =>
      ⟨v, f.mono (by simp), g, rd, wr, sp⟩

/-! ## The entry -/

/-- An offset argument: the low word of its register. -/
abbrev lo (s : State) (r : Reg) : Nat := ((s.gpr r).setWidth 32).toNat

/-- A pointer `W + x` is a multiple of 8 if and only if `x` is, for `W` one and no wrap around. -/
theorem ptr_mod8 {W : Addr} (hW : W.toNat % 8 = 0) {x : Nat} (hx : W.toNat + x < 2 ^ 64) :
    (W + BitVec.ofNat 64 x).toNat % 8 = x % 8 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : x < 2 ^ 64), Nat.mod_eq_of_lt hx]
  omega

/-- The low three bits of an `or` are zero only if each operand's are. -/
theorem aligned_of {x y z : BitVec 64} (h : (x ||| y ||| z) &&& BitVec.ofInt 64 7 = 0) :
    x.toNat % 8 = 0 ∧ y.toNat % 8 = 0 ∧ z.toNat % 8 = 0 := by
  have e : ∀ v : BitVec 64, (v &&& BitVec.ofInt 64 7).toNat = v.toNat % 8 := fun v => by
    rw [BitVec.toNat_and, show (BitVec.ofInt 64 7).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  rw [BitVec.and_or_distrib_right, BitVec.and_or_distrib_right] at h
  have h1 := congrArg BitVec.toNat h
  rw [BitVec.toNat_or, BitVec.toNat_or, e, e, e] at h1
  rw [show BitVec.toNat (0 : BitVec 64) = 0 from rfl] at h1
  have h2 := Nat.or_eq_zero_iff.mp h1
  have h3 := Nat.or_eq_zero_iff.mp h2.1
  exact ⟨h3.1, h3.2, h2.2⟩

/-- What the pointers' block leaves, after the zero-extension from `σ`. -/
theorem ptrs_ok {W : Addr} {σ s : State} (hz : VG.Proof.Ed25519.RISCV64.zextF σ s) (h0 : σ.gpr .a0 = W) :
    WP isa (.block ptrs) s fun t =>
      t.gpr .t2 = W + BitVec.ofNat 64 (lo σ .a1) ∧ t.gpr .t4 = W + BitVec.ofNat 64 (lo σ .a2) ∧
      t.gpr .t5 = W + BitVec.ofNat 64 (lo σ .a3) ∧ t.gpr .a3 = W + BitVec.ofNat 64 2048 ∧
      t.gpr .t0 = ((W + BitVec.ofNat 64 (lo σ .a1)) ||| (W + BitVec.ofNat 64 (lo σ .a2)) |||
        (W + BitVec.ofNat 64 (lo σ .a3))) &&& BitVec.ofInt 64 7 ∧
      Rest [.a3, .t0, .t2, .t4, .t5] s t ∧ t.mem = s.mem := by
  obtain ⟨-, e0, ek⟩ := hz
  have e1 := ek .a1 (by simp)
  have e2 := ek .a2 (by simp)
  have e3 := ek .a3 (by simp)
  rw [h0] at e0
  simp only [ptrs]
  refine wp_add fun s7 u7 => wp_add fun s8 u8 => wp_add fun s9 u9 => wp_addi (by decide) fun s10 u10 =>
    wp_addi (by decide) fun s11 u11 => wp_or fun s12 u12 => wp_or fun s13 u13 =>
    wp_andi (by decide) fun s14 u14 => WP.block_nil ?_
  have p2 : s9.gpr .t2 = W + BitVec.ofNat 64 (lo σ .a1) := by
    rw [u9.other _ (by decide), u8.other _ (by decide), u7.gpr, e0, e1]
  have p4 : s9.gpr .t4 = W + BitVec.ofNat 64 (lo σ .a2) := by
    rw [u9.other _ (by decide), u8.gpr, u7.other _ (by decide), u7.other .a2 (by decide), e0, e2]
  have p5 : s9.gpr .t5 = W + BitVec.ofNat 64 (lo σ .a3) := by
    rw [u9.gpr, u8.other _ (by decide), u8.other .a3 (by decide), u7.other _ (by decide),
      u7.other .a3 (by decide), e0, e3]
  have g14 : ∀ r, r ≠ .t0 → r ≠ .a3 → s14.gpr r = s9.gpr r := fun r h0 h3 => by
    rw [u14.other _ h0, u13.other _ h0, u12.other _ h0, u11.other _ h3, u10.other _ h3]
  refine ⟨by rw [g14 _ (by decide) (by decide), p2], by rw [g14 _ (by decide) (by decide), p4],
    by rw [g14 _ (by decide) (by decide), p5], ?_, ?_, ?_, ?_⟩
  · rw [u14.other _ (by decide), u13.other _ (by decide), u12.other _ (by decide), u11.gpr, u10.gpr,
      u9.other _ (by decide), u8.other _ (by decide), u7.other _ (by decide), e0, BitVec.add_assoc]
    rfl
  · rw [u14.gpr, u13.gpr, u12.gpr, u12.other .t5 (by decide)]
    rw [u11.other .t2 (by decide), u11.other .t4 (by decide), u11.other .t5 (by decide), u10.other .t2 (by decide),
      u10.other .t4 (by decide), u10.other .t5 (by decide), p2, p4, p5]
  · exact (u7.rest (by decide)).trans ((u8.rest (by decide)).trans ((u9.rest (by decide)).trans
      ((u10.rest (by decide)).trans ((u11.rest (by decide)).trans ((u12.rest (by decide)).trans
      ((u13.rest (by decide)).trans (u14.rest (by decide))))))))
  · rw [u14.mem, u13.mem, u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem]

/-- The zero-extension, with what it keeps. -/
theorem zext_ok (σ : State) : WP isa (.block zext) σ fun t =>
    VG.Proof.Ed25519.RISCV64.zextF σ t ∧ Rest [.a1, .a2, .a3] σ t ∧ t.mem = σ.mem := by
  unfold zext Impl.Ed25519.RISCV64.mulZext
  refine wp_sll (by decide) fun s1 u1 => wp_srl (by decide) fun s2 u2 => wp_sll (by decide) fun s3 u3 =>
    wp_srl (by decide) fun s4 u4 => wp_sll (by decide) fun s5 u5 => wp_srl (by decide) fun s6 u6 =>
    WP.block_nil ?_
  have h0 : s6.gpr .a0 = σ.gpr .a0 := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
      u2.other _ (by decide), u1.other _ (by decide)]
  have hk : ∀ r ∈ [Reg.a1, .a2, .a3], s6.gpr r = BitVec.ofNat 64 ((σ.gpr r).setWidth 32).toNat := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
        u2.gpr, u1.gpr, Ed25519.RISCV64.zext_shifts]
    · rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, u3.gpr, u2.other _ (by decide),
        u1.other _ (by decide), Ed25519.RISCV64.zext_shifts]
    · rw [u6.gpr, u5.gpr, u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
        u1.other _ (by decide), Ed25519.RISCV64.zext_shifts]
  have hr : Rest [.a1, .a2, .a3] σ s6 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans ((u5.rest (by decide)).trans (u6.rest (by decide))))))
  exact ⟨⟨by rw [u6.sp, u5.sp, u4.sp, u3.sp, u2.sp, u1.sp], h0, hk⟩, hr,
    by rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]⟩

/-- The registers the functions write. -/
abbrev clobF : List Reg := [.t0, .t1, .t2, .t3, .t4, .t5, .t6, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7]

/-- The regions the functions write: their own working space and the result. -/
abbrev fnW (W : Addr) (o : Nat) : List Region := [⟨W + BitVec.ofNat 64 3840, 256⟩, ⟨W + BitVec.ofNat 64 o, 32⟩]

theorem mulW_fnW (W : Addr) (o : Nat) {m m' : Mem} (h : Frame (mulW W o) m m') : Frame (fnW W o) m m' :=
  h.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub W (by omega) (by omega)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub W (by omega) (by omega)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub W (by omega) (by omega)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩

/-- `fn core`, from the working space at `W` and offsets below its own working space. -/
theorem fn_ok {core : Prog isa} {pre : Nat → Nat → Prop} {res : Nat → Nat → Nat → Prop}
    (hcore : CoreOk core pre res) {W : Addr} {s : State} (h0 : s.gpr .a0 = W) (hal : W.toNat % 8 = 0)
    (hwr : (⟨W, 8192⟩ : Region) ∈ s.wr) (hfit : W.toNat + 8192 ≤ 2 ^ 64)
    (ho : lo s .a1 + 32 ≤ 3840) (ha : lo s .a2 + 32 ≤ 3840) (hb : lo s .a3 + 32 ≤ 3840)
    (hpre : pre (d4 s.mem (W + BitVec.ofNat 64 (lo s .a2))) (d4 s.mem (W + BitVec.ofNat 64 (lo s .a3)))) :
    WP isa (fn core) s fun s' =>
      res (d4 s.mem (W + BitVec.ofNat 64 (lo s .a2))) (d4 s.mem (W + BitVec.ofNat 64 (lo s .a3)))
        (d4 s'.mem (W + BitVec.ofNat 64 (lo s .a1))) ∧
      Frame (fnW W (lo s .a1)) s.mem s'.mem ∧ (∀ r, r ∉ clobF → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  unfold fn
  refine WP.seq (WP.mono (zext_ok s) fun s0 ⟨z0, r0, m0⟩ => ?_)
  refine WP.seq (WP.mono (ptrs_ok z0 h0) fun s1 ⟨p2, p4, p5, p3, p0, r1', m1'⟩ => ?_)
  have r1 : Rest [.a1, .a2, .a3, .t0, .t2, .t4, .t5] s s1 := (r0.mono (by decide)).trans (r1'.mono (by decide))
  have m1 : s1.mem = s.mem := by rw [m1', m0]
  have hw1 : WsAt W s1 := ⟨hal, by rw [r1.wr]; exact hwr, hfit, p3⟩
  have sub1 : ∀ x ∈ [Reg.a1, .a2, .a3, .t0, .t2, .t4, .t5], x ∈ clobF := by decide
  have subM : ∀ x ∈ clobM, x ∈ clobF := by decide
  refine WP.ite (s1.gpr .t0 == 0) rfl (fun hz => ?_) (fun _ => ?_)
  · -- The offsets are multiples of 8.
    rw [p0] at hz
    obtain ⟨al1, al2, al3⟩ := aligned_of (beq_iff_eq.mp hz)
    rw [ptr_mod8 hal (by omega)] at al1 al2 al3
    refine WP.mono (hcore hw1 p4 p5 p2 al2 al3 al1 (by omega) (by omega) (by omega) (.inl (by omega))
      (by rw [m1]; exact hpre)) fun s2 ⟨v2, f2, g2, rd2, wr2, sp2⟩ => ⟨by rw [← m1]; exact v2, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← m1]; exact mulW_fnW W _ f2
    · intro r hr
      rw [g2 r (fun h => hr (subM r h)), r1.gpr r (fun h => hr (sub1 r h))]
    · rw [rd2, r1.rd]
    · rw [wr2, r1.wr]
    · rw [sp2, r1.sp]
  · -- The byte-wise copies.
    refine WP.seq (WP.mono (slowIn_ok hw1 p4 p5 p2 ha hb) fun s2 ⟨hw2, q1, q4, q5, q2, v4, v5, f2, r2⟩ => ?_)
    refine WP.seq (WP.mono (hcore hw2 q4 q5 q2 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (.inr (by decide)) (by rw [v4, v5, m1]; exact hpre)) fun s3 ⟨v3, f3, g3, rd3, wr3, sp3⟩ => ?_)
    have hw3 : WsAt W s3 := ⟨hal, by rw [wr3]; exact hw2.wr, hfit, by rw [g3 _ (by decide), hw2.a3]⟩
    refine WP.mono (slowOut_ok hw3 (by rw [g3 _ (by decide), q1]) ho) fun s4 ⟨r4, f4, v4'⟩ =>
      ⟨by rw [v4']; rw [v4, v5, m1] at v3; exact v3, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← m1]
      refine (f2.sub fun r hr => ?_).trans ((f3.sub fun r hr => ?_).trans (f4.sub fun r hr => ?_))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_self .., Offset.sub W (by omega) (by omega)⟩
        · exact ⟨_, List.mem_cons_self .., Offset.sub W (by omega) (by omega)⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., Offset.sub W (by omega) (by omega)⟩
        · exact ⟨_, List.mem_cons_self .., Offset.sub W (by omega) (by omega)⟩
        · exact ⟨_, List.mem_cons_self .., Offset.sub W (by omega) (by omega)⟩
        · exact ⟨_, List.mem_cons_self .., Offset.sub W (by omega) (by omega)⟩
      · rw [List.mem_singleton.mp hr]
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
    · intro r hr
      have s2' : ∀ x ∈ [Reg.t1, .t2, .t4, .t5, .a4, .a5], x ∈ clobF := by decide
      have s4' : ∀ x ∈ [Reg.a4, .a5], x ∈ clobF := by decide
      rw [r4.gpr r (fun h => hr (s4' r h)), g3 r (fun h => hr (subM r h)), r2.gpr r (fun h => hr (s2' r h)),
        r1.gpr r (fun h => hr (sub1 r h))]
    · rw [r4.rd, rd3, r2.rd, r1.rd]
    · rw [r4.wr, wr3, r2.wr, r1.wr]
    · rw [r4.sp, sp3, r2.sp, r1.sp]

end VG.Proof.Weierstrass.RISCV64.P256Field

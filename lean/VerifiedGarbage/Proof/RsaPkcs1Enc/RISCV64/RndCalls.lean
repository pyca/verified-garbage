module

-- separate module: the proofs of the call and of the two ends build in parallel with the scan's (`RndScan`)

public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.RndPre
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on RISC-V: the call and the two ends

With `PS` full (`Ready`): `tape` is `[i, 0]` and the call's register
arguments (`callRegs_ok`, `Pre`); the call's stack arguments in a frame of
48 bytes below ours (`stack_ok`, `Args`), and the call of
`vg_rsa_pkcs1_encrypt_precomputed` by its contract (`call_ok`): `out`
holds the encryption with `PS` the padding string drawn, if `pre` holds the
values for `n` (`AfterCall`); then the status `2 - r`, the wipe of `PS` and
the restores (`accTail_ok`). With `PS` not full: the tape and the status by
the budget (`budget_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Rnd


open VG VG.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64 VG.Proof.RsaPkcs1Sig.RISCV64 VG.WriteBytes
open VG.Impl.RsaPkcs1Enc.RISCV64.Random

/-! ## Regions -/

/-- `PS`, in the frame. -/
abbrev psR (s : State) : Region := ⟨psA s, psLen s⟩

/-- `out`, of `n_len` bytes. -/
abbrev oR' (s : State) : Region := ⟨s.gpr .a0, (s.gpr .a4).toNat⟩

/-- The callee's frame. -/
abbrev ckR (s : State) : Region := ⟨s.sp - BitVec.ofNat 64 4304, frameBytes⟩

section
variable {s : State}

theorem oR_eq (hp : RPre s) : oR s = oR' s := by
  show (⟨_, _⟩ : Region) = ⟨_, _⟩; rw [hp.ok]

theorem psR_sub (hp : RPre s) : Region.Sub (psR s) (kR s) :=
  frame_sub s (d := oEM1) (n := psLen s) (by have := psLen_le hp; unfold oEM1 frameBytes; omega)

theorem psR_st (hp : RPre s) : Region.Sub (psR s) (stR s) := fun a h => kR_sub a (psR_sub hp a h)

theorem cR_st : Region.Sub (cR s) (stR s) := fun a h => lowR_sub a (cR_sub a h)

theorem ckR_low : Region.Sub (ckR s) (lowR s) := Region.sub_prefix (by unfold frameBytes; omega)

theorem ckR_st : Region.Sub (ckR s) (stR s) := fun a h => lowR_sub a (ckR_low a h)

theorem psR_low (hp : RPre s) : (psR s).Disjoint (lowR s) := (kR_lowR hp).sub_left (psR_sub hp)

theorem fb_toNat' (hp : RPre s) : (fb s).toNat + 2128 = s.sp.toNat := fb_toNat (sp1' hp)

theorem wok_ps (hp : RPre s) {xs : List Byte} (hl : xs.length = psLen s) : Wok s ⟨psA s, xs.length⟩ := by
  rw [hl]; exact wok_frame s (by decide) (by have := psLen_le hp; unfold oEM1 frameBytes; omega)

end

/-! ## `PS` full -/

/-- `PS` full after `i` octets, its octets `ps`. -/
structure Ready (s t : State) (i : Nat) (ps : List Byte) : Prop extends InF s t where
  g : ∀ r ∈ argRegs, t.gpr r = s.gpr r
  s1 : t.gpr .s1 = BitVec.ofNat 64 (psLen s)
  t1 : t.gpr .t1 = psA s
  t2 : t.gpr .t2 = BitVec.ofNat 64 i
  buf : Spec.Rsa.bytesAt t.mem (psA s) (psLen s) = ps
  len : ps.length = psLen s

/-- The callee's stack arguments. -/
def callArg (s : State) : Nat → Addr
  | 0 => psA s
  | 1 => BitVec.ofNat 64 (psLen s)
  | 2 => stackArg s 3
  | 3 => stackArg s 4
  | 4 => stackArg s 5
  | _ => stackArg s 6

/-- Before the call's frame: `tape` is `[i, 0]` and the register arguments. -/
structure Pre (s z : State) (i : Nat) (ps : List Byte) : Prop extends InF s z where
  s1 : z.gpr .s1 = BitVec.ofNat 64 (psLen s)
  t1 : z.gpr .t1 = psA s
  t2 : z.gpr .t2 = stackArg s 3
  t3 : z.gpr .t3 = stackArg s 4
  t4 : z.gpr .t4 = stackArg s 5
  t5 : z.gpr .t5 = stackArg s 6
  a0 : z.gpr .a0 = s.gpr .a0
  a1 : z.gpr .a1 = s.gpr .a4
  a2 : z.gpr .a2 = s.gpr .a3
  a3 : z.gpr .a3 = s.gpr .a4
  a4 : z.gpr .a4 = s.gpr .a5
  a5 : z.gpr .a5 = s.gpr .a6
  a6 : z.gpr .a6 = s.gpr .a7
  a7 : z.gpr .a7 = stackArg s 0
  buf : Spec.Rsa.bytesAt z.mem (psA s) (psLen s) = ps
  len : ps.length = psLen s
  tape0 : z.mem.readW (s.gpr .a2) 64 = BitVec.ofNat 64 i
  tape1 : z.mem.readW (s.gpr .a2 + BitVec.ofNat 64 8) 64 = 0

theorem tR_contains0 (s : State) : (tR s).Contains (s.gpr .a2) 8 := by
  show (s.gpr .a2 - s.gpr .a2).toNat + 8 ≤ 16; simp

theorem tR_contains (s : State) {d : Nat} (hd : d + 8 ≤ 16) : (tR s).Contains (s.gpr .a2 + BitVec.ofNat 64 d) 8 :=
  Offset.contains_base _ hd (by omega)

theorem callRegs_ok {s y : State} (hp : RPre s) {i : Nat} {ps : List Byte} (hr : Ready s y i ps) :
    WP isa (.block callRegs) y fun z => Pre s z i ps := by
  have hwt : InRegions y.wr (s.gpr .a2) 8 := by
    rw [hr.wr, hp.hwr]; exact ⟨tR s, by simp, tR_contains0 s⟩
  unfold callRegs argBase
  simp only [List.cons_append, List.nil_append]
  refine wp_sd (a := s.gpr .a2) (by rw [hr.g .a2 (by decide), BitVec.add_zero]) hp.alt hwt fun y₁ m₁ => ?_
  refine wp_li (imm := 0) (by decide) fun y₂ o₂ e₂ => ?_
  refine wp_sd (a := s.gpr .a2 + BitVec.ofNat 64 8) (by rw [o₂.get .a2, m₁.gpr, hr.g .a2 (by decide)])
    (Spill.al8 hp.alt (by decide))
    (by rw [o₂.wr, m₁.wr, hr.wr, hp.hwr]; exact ⟨tR s, by simp, tR_contains s (by decide)⟩) fun y₃ m₃ => ?_
  have fr₃ : Frame [tR s] y.mem y₃.mem := by
    rw [m₃.mem, o₂.mem, m₁.mem]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (tR_contains0 s)).writeW
      (List.mem_singleton_self _) _ (tR_contains s (by decide))
  have hF₃ : InF s y₃ := hr.toInF.step (m₁.keep.trans (o₂.keep.trans m₃.keep)) fr₃
    (fun r h => by rw [List.mem_singleton.mp h]; exact wok_apart (by simp) hp.kt)
  refine wp_mov fun y₄ o₄ e₄ => wp_mov fun y₅ o₅ e₅ => wp_mov fun y₆ o₆ e₆ => wp_mov fun y₇ o₇ e₇ =>
    wp_mov fun y₈ o₈ e₈ => wp_mov fun y₉ o₉ e₉ => ?_
  refine wp_addSp fun y₁₀ o₁₀ e₁₀ => wp_addi fun y₁₁ o₁₁ e₁₁ => ?_
  have O₁₁ : Only [.a1, .a2, .a3, .a4, .a5, .a6, .t6, .t6] y₃ y₁₁ :=
    o₄.trans (o₅.trans (o₆.trans (o₇.trans (o₈.trans (o₉.trans (o₁₀.trans o₁₁))))))
  have hF₁₁ : InF s y₁₁ := hF₃.only O₁₁
  have t6 : y₁₁.gpr .t6 = stackArgAddr s 0 := by
    rw [e₁₁, e₁₀]; exact Enc.t6_eq (by rw [o₉.sp, o₈.sp, o₇.sp, o₆.sp, o₅.sp, o₄.sp, hF₃.sp])
  have arg : ∀ {j : Nat}, j < 7 → y₁₁.mem.readW (stackArgAddr s j) 64 = stackArg s j := fun hj =>
    arg_mem hp hF₁₁.fr hj
  have ld : ∀ {x : State}, x.rd = s.rd → x.gpr .t6 = stackArgAddr s 0 → ∀ {j : Nat}, j < 7 →
      x.gpr .t6 + BitVec.ofNat 64 (8 * j) = stackArgAddr s j ∧ InRegions (x.rd ++ x.wr) (stackArgAddr s j) 8 :=
    fun hrd h6 j hj => ⟨by rw [h6, ← stackArgAddr_eq], by rw [hrd]; exact arg_rd hp _ hj⟩
  refine wp_ld (ld hF₁₁.rd t6 (j := 0) (by decide)).1 (arg_al hp.spal 0) (ld hF₁₁.rd t6 (by decide)).2
    fun z₁ p₁ f₁ => ?_
  refine wp_ld (ld (p₁.rd.trans hF₁₁.rd) (by rw [p₁.get .t6, t6]) (j := 3) (by decide)).1 (arg_al hp.spal 3)
    (ld (p₁.rd.trans hF₁₁.rd) (by rw [p₁.get .t6, t6]) (by decide)).2 fun z₂ p₂ f₂ => ?_
  refine wp_ld (ld (p₂.rd.trans (p₁.rd.trans hF₁₁.rd)) (by rw [p₂.get .t6, p₁.get .t6, t6]) (j := 4)
    (by decide)).1 (arg_al hp.spal 4)
    (ld (p₂.rd.trans (p₁.rd.trans hF₁₁.rd)) (by rw [p₂.get .t6, p₁.get .t6, t6]) (by decide)).2
    fun z₃ p₃ f₃ => ?_
  have P₃ : Only [.a7, .t2, .t3] y₁₁ z₃ := p₁.trans (p₂.trans p₃)
  refine wp_ld (ld (P₃.rd.trans hF₁₁.rd) (by rw [P₃.get .t6, t6]) (j := 5) (by decide)).1 (arg_al hp.spal 5)
    (ld (P₃.rd.trans hF₁₁.rd) (by rw [P₃.get .t6, t6]) (by decide)).2 fun z₄ p₄ f₄ => ?_
  refine wp_ld (ld (p₄.rd.trans (P₃.rd.trans hF₁₁.rd)) (by rw [p₄.get .t6, P₃.get .t6, t6]) (j := 6)
    (by decide)).1 (arg_al hp.spal 6)
    (ld (p₄.rd.trans (P₃.rd.trans hF₁₁.rd)) (by rw [p₄.get .t6, P₃.get .t6, t6]) (by decide)).2
    fun z₅ p₅ f₅ => wp_nil ?_
  have P₅ : Only [.a7, .t2, .t3, .t4, .t5] y₁₁ z₅ := P₃.trans (p₄.trans p₅)
  have mem₅ : z₅.mem = y₃.mem := by rw [P₅.mem, O₁₁.mem]
  have gy : ∀ r ∈ argRegs, y₃.gpr r = s.gpr r := fun r hr' => by
    rw [m₃.gpr, o₂.gpr r (by
      simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), m₁.gpr, hr.g r hr']
  have hpd : (psR s).Disjoint (tR s) := (k_dis hp.kt).sub_left (psR_sub hp)
  refine { hF₁₁.only P₅ with
    s1 := by rw [P₅.get .s1, O₁₁.get .s1, m₃.gpr, o₂.get .s1, m₁.gpr, hr.s1]
    t1 := by rw [P₅.get .t1, O₁₁.get .t1, m₃.gpr, o₂.get .t1, m₁.gpr, hr.t1]
    t2 := by rw [p₅.get .t2, p₄.get .t2, p₃.get .t2, f₂, p₁.mem, arg (by decide)]
    t3 := by rw [p₅.get .t3, p₄.get .t3, f₃, p₂.mem, p₁.mem, arg (by decide)]
    t4 := by rw [p₅.get .t4, f₄, P₃.mem, arg (by decide)]
    t5 := by rw [f₅, p₄.mem, P₃.mem, arg (by decide)]
    a0 := by rw [P₅.get .a0, O₁₁.get .a0, gy .a0 (by decide)]
    a1 := by rw [P₅.get .a1, o₁₁.get .a1, o₁₀.get .a1, o₉.get .a1, o₈.get .a1, o₇.get .a1, o₆.get .a1,
      o₅.get .a1, e₄, gy .a4 (by decide)]
    a2 := by rw [P₅.get .a2, o₁₁.get .a2, o₁₀.get .a2, o₉.get .a2, o₈.get .a2, o₇.get .a2, o₆.get .a2, e₅,
      o₄.get .a3, gy .a3 (by decide)]
    a3 := by rw [P₅.get .a3, o₁₁.get .a3, o₁₀.get .a3, o₉.get .a3, o₈.get .a3, o₇.get .a3, e₆, o₅.get .a4,
      o₄.get .a4, gy .a4 (by decide)]
    a4 := by rw [P₅.get .a4, o₁₁.get .a4, o₁₀.get .a4, o₉.get .a4, o₈.get .a4, e₇, o₆.get .a5, o₅.get .a5,
      o₄.get .a5, gy .a5 (by decide)]
    a5 := by rw [P₅.get .a5, o₁₁.get .a5, o₁₀.get .a5, o₉.get .a5, e₈, o₇.get .a6, o₆.get .a6, o₅.get .a6,
      o₄.get .a6, gy .a6 (by decide)]
    a6 := by rw [P₅.get .a6, o₁₁.get .a6, o₁₀.get .a6, e₉, o₈.get .a7, o₇.get .a7, o₆.get .a7, o₅.get .a7,
      o₄.get .a7, gy .a7 (by decide)]
    a7 := by rw [p₅.get .a7, p₄.get .a7, p₃.get .a7, p₂.get .a7, f₁, arg (by decide)]
    buf := by
      have := psLen_le hp
      rw [mem₅, Proof.RsaPkcs1Sig.bytes_apart (R := psR s) fr₃ hpd (by dsimp only; omega)]; exact hr.buf
    len := hr.len
    tape0 := by
      rw [mem₅, m₃.mem, Mem.readW_writeW_sep (Offset.sep_base _ (by decide) (by decide)) (by decide), o₂.mem,
        m₁.mem, Mem.readW_writeW_self64, hr.t2]
    tape1 := by rw [mem₅, m₃.mem, Mem.readW_writeW_self64, e₂]; rfl }



open VG VG.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64 VG.Proof.RsaPkcs1Sig.RISCV64
open VG.Impl.RsaPkcs1Enc.RISCV64.Random

/-! ## The stack arguments -/

theorem rsep (m : Mem) (q : Addr) {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (q + BitVec.ofNat 64 e) v).readW (q + BitVec.ofNat 64 d) 64 = m.readW (q + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep q h hd he) (by decide)

/-- Six words at `q`. -/
def six (m : Mem) (q : Addr) (v : Nat → BitVec 64) : Mem :=
  (((((m.writeW (q + BitVec.ofNat 64 0) (v 0)).writeW (q + BitVec.ofNat 64 8) (v 1)).writeW
    (q + BitVec.ofNat 64 16) (v 2)).writeW (q + BitVec.ofNat 64 24) (v 3)).writeW
    (q + BitVec.ofNat 64 32) (v 4)).writeW (q + BitVec.ofNat 64 40) (v 5)

theorem six_read (m : Mem) (q : Addr) (v : Nat → BitVec 64) {j : Nat} (hj : j < 6) :
    (six m q v).readW (q + BitVec.ofNat 64 (8 * j)) 64 = v j := by
  unfold six
  match j, hj with
  | 0, _ =>
    rw [rsep (d := 0) (e := 40) _ _ _ (by decide) (by decide) (by decide),
      rsep (d := 0) (e := 32) _ _ _ (by decide) (by decide) (by decide),
      rsep (d := 0) (e := 24) _ _ _ (by decide) (by decide) (by decide),
      rsep (d := 0) (e := 16) _ _ _ (by decide) (by decide) (by decide),
      rsep (d := 0) (e := 8) _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  | 1, _ =>
    rw [rsep (d := 8) (e := 40) _ _ _ (by decide) (by decide) (by decide),
      rsep (d := 8) (e := 32) _ _ _ (by decide) (by decide) (by decide),
      rsep (d := 8) (e := 24) _ _ _ (by decide) (by decide) (by decide),
      rsep (d := 8) (e := 16) _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  | 2, _ =>
    rw [rsep (d := 16) (e := 40) _ _ _ (by decide) (by decide) (by decide),
      rsep (d := 16) (e := 32) _ _ _ (by decide) (by decide) (by decide),
      rsep (d := 16) (e := 24) _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  | 3, _ =>
    rw [rsep (d := 24) (e := 40) _ _ _ (by decide) (by decide) (by decide),
      rsep (d := 24) (e := 32) _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  | 4, _ => rw [rsep (d := 32) (e := 40) _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  | 5, _ => rw [Mem.readW_writeW_self64]

theorem six_frame {m : Mem} {q : Addr} (v : Nat → BitVec 64) : Frame [⟨q, 48⟩] m (six m q v) := by
  have c : ∀ {d : Nat}, d + 8 ≤ 48 → (⟨q, 48⟩ : Region).Contains (q + BitVec.ofNat 64 d) (64 / 8) :=
    fun h => Offset.contains_base _ h (by omega)
  have m1 := List.mem_singleton_self (⟨q, 48⟩ : Region)
  exact (((((((Frame.refl _ _).writeW m1 _ (c (by decide))).writeW m1 _ (c (by decide))).writeW m1 _
    (c (by decide))).writeW m1 _ (c (by decide))).writeW m1 _ (c (by decide))).writeW m1 _ (c (by decide)))

/-- At the call, in its frame. -/
structure Args (s w : State) (i : Nat) (ps : List Byte) : Prop where
  sp : w.sp = fb s - BitVec.ofNat 64 48
  rd : w.rd = s.rd
  wr : w.wr = cR s :: kR s :: s.wr
  hi : ∀ r ∈ hiRegs, w.gpr r = s.gpr r
  sv : Spill.Saved (fb s) s.gpr saved w.mem
  fr : Frame (W s) s.mem w.mem
  s1 : w.gpr .s1 = BitVec.ofNat 64 (psLen s)
  a0 : w.gpr .a0 = s.gpr .a0
  a1 : w.gpr .a1 = s.gpr .a4
  a2 : w.gpr .a2 = s.gpr .a3
  a3 : w.gpr .a3 = s.gpr .a4
  a4 : w.gpr .a4 = s.gpr .a5
  a5 : w.gpr .a5 = s.gpr .a6
  a6 : w.gpr .a6 = s.gpr .a7
  a7 : w.gpr .a7 = stackArg s 0
  sa : ∀ j < 6, w.mem.readW (fb s - BitVec.ofNat 64 48 + BitVec.ofNat 64 (8 * j)) 64 = callArg s j
  buf : Spec.Rsa.bytesAt w.mem (psA s) (psLen s) = ps
  len : ps.length = psLen s
  tape0 : w.mem.readW (s.gpr .a2) 64 = BitVec.ofNat 64 i
  tape1 : w.mem.readW (s.gpr .a2 + BitVec.ofNat 64 8) 64 = 0

theorem q_al {s : State} (hp : RPre s) : (fb s - BitVec.ofNat 64 48).toNat % 16 = 0 := by
  have := fb_al hp.spal (sp1' hp); have := fb_ge hp
  rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]
  omega

theorem stack_ok {s z : State} (hp : RPre s) {i : Nat} {ps : List Byte} (hz : Pre s z i ps) :
    WP isa (.block callStack) (allocd 48 z) fun w => Args s w i ps := by
  have hq := q_al hp
  have hP := psLen_le hp
  have hsp : (allocd 48 z).sp = fb s - BitVec.ofNat 64 48 := by rw [allocd]; dsimp only; rw [hz.sp]
  have hwr : (allocd 48 z).wr = cR s :: kR s :: s.wr := by rw [allocd]; dsimp only; rw [hz.sp, hz.wr]
  unfold callStack
  refine wp_addSp fun x₀ o₀ e₀ => ?_
  rw [hsp, BitVec.add_zero] at e₀
  have st : ∀ {x : State}, x.wr = cR s :: kR s :: s.wr → x.gpr .t0 = fb s - BitVec.ofNat 64 48 → ∀ {d : Nat},
      d % 8 = 0 → d + 8 ≤ 48 →
      x.gpr .t0 + BitVec.ofNat 64 d = fb s - BitVec.ofNat 64 48 + BitVec.ofNat 64 d ∧
      (fb s - BitVec.ofNat 64 48 + BitVec.ofNat 64 d).toNat % 8 = 0 ∧
      InRegions x.wr (fb s - BitVec.ofNat 64 48 + BitVec.ofNat 64 d) 8 := fun hw h0 d hd hd' =>
    ⟨by rw [h0], Spill.al8 (by omega) hd,
      by rw [hw]; exact ⟨cR s, List.mem_cons_self .., Offset.contains_base _ hd' (by omega)⟩⟩
  have w₀ : x₀.wr = cR s :: kR s :: s.wr := by rw [o₀.wr, hwr]
  refine wp_sd (st w₀ e₀ (d := 0) (by decide) (by decide)).1 (st w₀ e₀ (by decide) (by decide)).2.1
    (st w₀ e₀ (by decide) (by decide)).2.2 fun x₁ m₁ => ?_
  have w₁ := m₁.wr.trans w₀
  have g₁ := (m₁.gpr ▸ e₀ : x₁.gpr .t0 = _)
  refine wp_sd (st w₁ g₁ (d := 8) (by decide) (by decide)).1 (st w₁ g₁ (by decide) (by decide)).2.1
    (st w₁ g₁ (by decide) (by decide)).2.2 fun x₂ m₂ => ?_
  have w₂ := m₂.wr.trans w₁
  have g₂ := (m₂.gpr ▸ g₁ : x₂.gpr .t0 = _)
  refine wp_sd (st w₂ g₂ (d := 16) (by decide) (by decide)).1 (st w₂ g₂ (by decide) (by decide)).2.1
    (st w₂ g₂ (by decide) (by decide)).2.2 fun x₃ m₃ => ?_
  have w₃ := m₃.wr.trans w₂
  have g₃ := (m₃.gpr ▸ g₂ : x₃.gpr .t0 = _)
  refine wp_sd (st w₃ g₃ (d := 24) (by decide) (by decide)).1 (st w₃ g₃ (by decide) (by decide)).2.1
    (st w₃ g₃ (by decide) (by decide)).2.2 fun x₄ m₄ => ?_
  have w₄ := m₄.wr.trans w₃
  have g₄ := (m₄.gpr ▸ g₃ : x₄.gpr .t0 = _)
  refine wp_sd (st w₄ g₄ (d := 32) (by decide) (by decide)).1 (st w₄ g₄ (by decide) (by decide)).2.1
    (st w₄ g₄ (by decide) (by decide)).2.2 fun x₅ m₅ => ?_
  have w₅ := m₅.wr.trans w₄
  have g₅ := (m₅.gpr ▸ g₄ : x₅.gpr .t0 = _)
  refine wp_sd (st w₅ g₅ (d := 40) (by decide) (by decide)).1 (st w₅ g₅ (by decide) (by decide)).2.1
    (st w₅ g₅ (by decide) (by decide)).2.2 fun x₆ m₆ => wp_nil ?_
  have gz : ∀ r, r ≠ .t0 → x₆.gpr r = z.gpr r := fun r hr => by
    rw [m₆.gpr, m₅.gpr, m₄.gpr, m₃.gpr, m₂.gpr, m₁.gpr, o₀.gpr r (by simpa using hr)]; rfl
  let v : Nat → BitVec 64 := fun j => z.gpr ([Reg.t1, .s1, .t2, .t3, .t4, .t5].getD j .t5)
  have hm : x₆.mem = six z.mem (fb s - BitVec.ofNat 64 48) v := by
    simp only [m₆.mem, m₅.mem, m₄.mem, m₃.mem, m₂.mem, m₁.mem, o₀.mem, m₅.gpr, m₄.gpr, m₃.gpr, m₂.gpr, m₁.gpr,
      o₀.get .t1, o₀.get .s1, o₀.get .t2, o₀.get .t3, o₀.get .t4, o₀.get .t5]
    rfl
  have fr : Frame [cR s] z.mem x₆.mem := by rw [hm]; exact six_frame v
  have hcw : Wok s (cR s) := ⟨⟨lowR s, by simp, cR_sub⟩, (kR_lowR hp).sub_left
    (frame_sub s (d := oSave) (n := 40) (by decide)) |>.sub_right cR_sub⟩
  have hsv := hz.sv.frame_in saved_offs fr fun r hr => by rw [List.mem_singleton.mp hr]; exact hcw.2
  have hfr := hz.fr.trans (fr.sub fun r hr => by rw [List.mem_singleton.mp hr]; exact hcw.1)
  have tC : ∀ {d : Nat}, d + 8 ≤ 16 → x₆.mem.readW (s.gpr .a2 + BitVec.ofNat 64 d) 64 =
      z.mem.readW (s.gpr .a2 + BitVec.ofNat 64 d) 64 := fun hd =>
    fr.readW (tR_contains s hd) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (hp.kt.sub_left cR_st).symm) (by decide)
  refine ⟨by rw [m₆.sp, m₅.sp, m₄.sp, m₃.sp, m₂.sp, m₁.sp, o₀.sp, hsp], by
      rw [m₆.rd, m₅.rd, m₄.rd, m₃.rd, m₂.rd, m₁.rd, o₀.rd]; exact hz.rd,
    w₅.symm ▸ m₆.wr, fun r hr => by rw [gz r (by revert r; decide)]; exact hz.hi r hr, hsv, hfr,
    by rw [gz _ (by decide)]; exact hz.s1, by rw [gz _ (by decide)]; exact hz.a0,
    by rw [gz _ (by decide)]; exact hz.a1, by rw [gz _ (by decide)]; exact hz.a2,
    by rw [gz _ (by decide)]; exact hz.a3, by rw [gz _ (by decide)]; exact hz.a4,
    by rw [gz _ (by decide)]; exact hz.a5, by rw [gz _ (by decide)]; exact hz.a6,
    by rw [gz _ (by decide)]; exact hz.a7, fun j hj => ?_, ?_, hz.len, ?_, ?_⟩
  · rw [hm, six_read _ _ _ hj]
    match j, hj with
    | 0, _ => exact hz.t1
    | 1, _ => exact hz.s1
    | 2, _ => exact hz.t2
    | 3, _ => exact hz.t3
    | 4, _ => exact hz.t4
    | 5, _ => exact hz.t5
  · rw [Proof.RsaPkcs1Sig.bytes_apart (R := psR s) fr ((psR_low hp).sub_right cR_sub) (by dsimp only; omega)]
    exact hz.buf
  · have := tC (d := 0) (by decide); rw [BitVec.add_zero] at this; rw [this]; exact hz.tape0
  · rw [tC (by decide)]; exact hz.tape1

/-! ## The call -/

theorem enc_sdepth : sdepth Impl.RsaPkcs1Enc.RISCV64.Precomputed.code = 2128 := by decide +kernel

/-- The callee's regions. -/
abbrev callRd (s : State) : List Region := [nR s, eR s, mR s, psR s, pR s, cR s]
abbrev callWr (s : State) : List Region := [oR' s, scR s]

theorem encPre_of {c : State} (h : Enc.PreE c) :
    (Proof.RsaPkcs1Enc.encryptPrecomputedContract abi frameBytes).pre c := by
  have e : frameBytes = 2127 + 1 := rfl
  rw [e]
  sig_pre [Proof.RsaPkcs1Enc.encryptPrecomputedContract, Proof.RsaPkcs1Enc.encryptPrecomputedSig, abi, argRegs,
    Enc.stackArgs_six, List.append_eq, List.range, List.range.loop]
  exact ⟨h.spal, h.sp1, h.sp2, h.hrd, h.hwr, h.on, h.oe, h.om, h.ops, h.osc, h.op, h.oa, h.ns, h.es, h.ms,
    h.pss, h.sp, h.sa, h.ko, h.kn, h.ke, h.km, h.kps, h.ksc, h.kp, h.ka, h.wo, h.wn, h.we, h.wm, h.wps, h.wsc,
    h.wp, ⟨h.k1, h.k2⟩, h.ok, h.e1, h.e2, h.ml, h.pl, h.hs, h.hp, h.al2, h.al4⟩

section
variable {s : State}

theorem o'_dis (hp : RPre s) {R : Region} (h : (oR s).Disjoint R) : (oR' s).Disjoint R := by
  rwa [oR_eq hp] at h

theorem ck_dis {R : Region} (h : (stR s).Disjoint R) : (ckR s).Disjoint R := h.sub_left ckR_st

theorem ps_dis (hp : RPre s) {R : Region} (h : (stR s).Disjoint R) : (psR s).Disjoint R := h.sub_left (psR_st hp)

theorem c_dis {R : Region} (h : (stR s).Disjoint R) : (cR s).Disjoint R := h.sub_left cR_st

end

theorem preE_c {s w : State} (hp : RPre s) {i : Nat} {ps : List Byte} (hw : Args s w i ps) :
    Enc.PreE (w.callEntry.withRegions (callRd s) (callWr s)) := by
  have hP := psLen_le hp
  have hF := fb_toNat' hp
  have hfg := fb_ge hp
  generalize hc : w.callEntry.withRegions (callRd s) (callWr s) = c
  have csp : c.sp = fb s - BitVec.ofNat 64 48 := by rw [← hc]; exact hw.sp
  have crd : c.rd = callRd s := by rw [← hc]; rfl
  have cwr : c.wr = callWr s := by rw [← hc]; rfl
  have cg : ∀ r, r ∉ linkRegs → c.gpr r = w.gpr r := fun r h => by rw [← hc]; exact State.callEntry_gpr w h
  have ca0 : c.gpr .a0 = s.gpr .a0 := (cg .a0 (by decide)).trans hw.a0
  have ca1 : c.gpr .a1 = s.gpr .a4 := (cg .a1 (by decide)).trans hw.a1
  have ca2 : c.gpr .a2 = s.gpr .a3 := (cg .a2 (by decide)).trans hw.a2
  have ca3 : c.gpr .a3 = s.gpr .a4 := (cg .a3 (by decide)).trans hw.a3
  have ca4 : c.gpr .a4 = s.gpr .a5 := (cg .a4 (by decide)).trans hw.a4
  have ca5 : c.gpr .a5 = s.gpr .a6 := (cg .a5 (by decide)).trans hw.a5
  have ca6 : c.gpr .a6 = s.gpr .a7 := (cg .a6 (by decide)).trans hw.a6
  have ca7 : c.gpr .a7 = stackArg s 0 := (cg .a7 (by decide)).trans hw.a7
  have csa : ∀ j < 6, stackArg c j = callArg s j := fun j hj => by
    have hm : c.mem = w.mem := by rw [← hc]; rfl
    show c.mem.readW (c.sp + BitVec.ofNat 64 (8 * j)) 64 = _
    rw [csp, hm]; exact hw.sa j hj
  have cs0 : stackArg c 0 = psA s := csa 0 (by decide)
  have cs1 : (stackArg c 1).toNat = psLen s := by
    rw [csa 1 (by decide)]; show (BitVec.ofNat 64 (psLen s)).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have cs2 : stackArg c 2 = stackArg s 3 := csa 2 (by decide)
  have cs3 : stackArg c 3 = stackArg s 4 := csa 3 (by decide)
  have cs4 : stackArg c 4 = stackArg s 5 := csa 4 (by decide)
  have cs5 : stackArg c 5 = stackArg s 6 := csa 5 (by decide)
  have cA : stackArgAddr c 0 = fb s - BitVec.ofNat 64 48 := by
    rw [stackArgAddr, csp, Nat.mul_zero, BitVec.add_zero]
  have cK : kR c = ckR s := by
    show (⟨c.sp - BitVec.ofNat 64 2128, 2128⟩ : Region) = ⟨_, _⟩
    rw [csp, fb_sub48, low_eq]; rfl
  have cfb : (c.sp).toNat = (fb s).toNat - 48 := by
    rw [csp, BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]
  have hq := q_al hp
  have wps : (psA s).toNat + psLen s ≤ 2 ^ 64 := by
    show (fb s + BitVec.ofNat 64 oEM1).toNat + _ ≤ _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; unfold oEM1; have := s.sp.isLt; omega
  have kc : (ckR s).Disjoint (cR s) := by
    rw [cR, fb_sub48]
    have := (Offset.base_disjoint_below (s.sp - BitVec.ofNat 64 2176) (n := 2128) (k := 48) (by decide)).symm
    rwa [low_eq] at this
  refine ⟨?spal, ?sp1, ?sp2, ?hrd, ?hwr, ?on, ?oe, ?om, ?ops, ?osc, ?op, ?oa, ?ns, ?es, ?ms, ?pss, ?sp, ?sa, ?ko,
    ?kn, ?ke, ?km, ?kps, ?ksc, ?kp, ?ka, ?wo, ?wn, ?we, ?wm, ?wps, ?wsc, ?wp, ?k1, ?k2, ?ok, ?e1, ?e2, ?ml, ?pl,
    ?hs, ?hp, ?al2, ?al4⟩
  all_goals try simp only [Enc.oR, Enc.nR, Enc.eR, Enc.mR, Enc.psR, Enc.scR, Enc.pR, Enc.a6R, cK, crd, cwr, csp,
    ca0, ca1, ca2, ca3, ca4, ca5, ca6, ca7, cs0, cs1, cs2, cs3, cs4, cs5, cA]
  case spal => exact hq
  case sp1 => rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega),
      BitVec.toNat_ofNat]; unfold frameBytes; omega
  case sp2 => rw [BitVec.toNat_sub_of_le (by simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega),
      BitVec.toNat_ofNat]; have := s.sp.isLt; omega
  case on => exact o'_dis hp hp.on
  case oe => exact o'_dis hp hp.oe
  case om => exact o'_dis hp hp.om
  case ops => exact o'_dis hp (ps_dis hp hp.ko).symm
  case osc => exact o'_dis hp hp.os
  case op => exact o'_dis hp hp.op
  case oa => exact o'_dis hp (c_dis hp.ko).symm
  case ns => exact hp.ns
  case es => exact hp.es
  case ms => exact hp.ms
  case pss => exact ps_dis hp hp.ks
  case sp => exact hp.sp
  case sa => exact (c_dis hp.ks).symm
  case ko => exact (o'_dis hp (ck_dis hp.ko).symm).symm
  case kn => exact ck_dis hp.kn
  case ke => exact ck_dis hp.ke
  case km => exact ck_dis hp.km
  case kps => exact ((kR_lowR hp).sub_left (psR_sub hp)).sub_right ckR_low |>.symm
  case ksc => exact ck_dis hp.ks
  case kp => exact ck_dis hp.kp
  case ka => exact kc
  case wo => have := hp.wo; rw [hp.ok] at this; exact this
  case wn => exact hp.wn
  case we => exact hp.we
  case wm => exact hp.wm
  case wps => exact wps
  case wsc => exact hp.ws
  case wp => exact hp.wp
  case k1 => exact hp.k1
  case k2 => exact hp.k2
  case e1 => exact hp.e1
  case e2 => exact hp.e2
  case ml => exact hp.ml
  case hs => exact hp.hs
  case hp => exact hp.hp
  case al2 => exact hp.als
  case al4 => exact hp.alp

/-- `pre` holds the values of the modulus. -/
abbrev PreOk (s : State) : Prop := Spec.Rsa.publicPrecompute (nB s) = some (preW s)

/-- After the call: in our frame, `psLen` in `s1`, the tape, and `out`
written with the encryption if `pre` holds the modulus' values. -/
structure AfterCall (s u : State) (i : Nat) (ps : List Byte) : Prop extends InF s u where
  s1 : u.gpr .s1 = BitVec.ofNat 64 (psLen s)
  tape0 : u.mem.readW (s.gpr .a2) 64 = BitVec.ofNat 64 i
  tape1 : u.mem.readW (s.gpr .a2 + BitVec.ofNat 64 8) 64 = 0
  res : PreOk s → Spec.Rsa.written u.mem (s.gpr .a0) (s.gpr .a4).toNat ((u.gpr .a0).setWidth 32)
    (Spec.RsaPkcs1Enc.encrypt (nB s) (eB s) (msgB s) ps)

theorem call_covers {s w : State} (hp : RPre s) {i : Nat} {ps : List Byte} (hw : Args s w i ps) :
    Covers (callRd s ++ callWr s) (w.rd ++ w.wr) ∧ Covers (callWr s) w.wr := by
  have hP := psLen_le hp
  have z : ∀ p : Addr, p = p + BitVec.ofNat 64 0 := fun p => (BitVec.add_zero p).symm
  have cw : Covers (callWr s) w.wr := by
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hw.wr, hp.hwr]
    rcases hr with rfl | rfl
    · exact ⟨oR s, by simp, 0, z _, by show 0 + (s.gpr .a4).toNat ≤ (s.gpr .a1).toNat; rw [hp.ok]; simp⟩
    · exact ⟨scR s, by simp, 0, z _, by simp⟩
  refine ⟨Covers.of_sub fun r hr => ?_, cw⟩
  rw [hw.rd, hw.wr, hp.hrd, hp.hwr]
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨nR s, by simp, 0, z _, by simp⟩
  · exact ⟨eR s, by simp, 0, z _, by simp⟩
  · exact ⟨mR s, by simp, 0, z _, by simp⟩
  · exact ⟨kR s, by simp, oEM1, rfl, by show oEM1 + psLen s ≤ frameBytes; unfold oEM1 frameBytes; omega⟩
  · exact ⟨pR s, by simp, 0, z _, by simp⟩
  · exact ⟨cR s, by simp, 0, z _, by simp⟩
  · exact ⟨oR s, by simp, 0, z _, by show 0 + (s.gpr .a4).toNat ≤ (s.gpr .a1).toNat; rw [hp.ok]; simp⟩
  · exact ⟨scR s, by simp, 0, z _, by simp⟩

theorem entry_arg {s w : State} {i : Nat} {ps : List Byte} (hw : Args s w i ps) (rd wr : List Region) {j : Nat}
    (hj : j < 6) : stackArg (w.callEntry.withRegions rd wr) j = callArg s j := by
  show (w.callEntry.withRegions rd wr).mem.readW ((w.callEntry.withRegions rd wr).sp + BitVec.ofNat 64 (8 * j)) 64 = _
  simp only [State.withRegions_mem, State.withRegions_sp, State.callEntry_mem, State.callEntry_sp, hw.sp]
  exact hw.sa j hj

theorem svR_sub (s : State) : Region.Sub (svR s) (kR s) := frame_sub s (d := oSave) (n := 40) (by decide)

theorem call_ok {s z : State} (hp : RPre s) {i : Nat} {ps : List Byte} (hz : Pre s z i ps) :
    WP isa Impl.RsaPkcs1Enc.RISCV64.Random.call z fun u => AfterCall s u i ps := by
  have hP := psLen_le hp
  have hfg := fb_ge hp
  unfold Impl.RsaPkcs1Enc.RISCV64.Random.call
  refine WP.allocLe (by decide) (by rw [hz.sp]; omega) ?_
  refine WP.seq (WP.mono (stack_ok hp hz) fun w hw => ?_)
  obtain ⟨hc, hcw⟩ := call_covers hp hw
  refine WP.callAny (k := Proof.RsaPkcs1Enc.encryptPrecomputedContract abi frameBytes) Enc.code_correct
    (rd := callRd s) (wr := callWr s) (encPre_of (preE_c hp hw)) hc hcw
    (fun s' hrd hwr hsp hf hpres hpost => ?_) (by rw [enc_sdepth]; decide)
  rw [enc_sdepth, hw.sp] at hf
  simp only [below, fb_sub48, low_eq] at hf
  have hf' : Frame [oR' s, scR s, ckR s] w.mem s'.mem := hf
  have hW : ∀ r ∈ [oR' s, scR s, ckR s], Wok s r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨oR s, by simp, by rw [oR_eq hp]; exact fun _ h => h⟩,
        o'_dis hp ((k_dis hp.ko).sub_left (svR_sub s)).symm |>.symm⟩
    · exact wok_apart (by simp) hp.ks
    · exact ⟨⟨lowR s, by simp, ckR_low⟩, ((kR_lowR hp).sub_left (svR_sub s)).sub_right ckR_low⟩
  have tD : ∀ r ∈ [oR' s, scR s, ckR s], (tR s).Disjoint r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (o'_dis hp hp.ot).symm
    · exact hp.ts
    · exact (ck_dis hp.kt).symm
  have tC : ∀ {d : Nat}, d + 8 ≤ 16 → s'.mem.readW (s.gpr .a2 + BitVec.ofNat 64 d) 64 =
      w.mem.readW (s.gpr .a2 + BitVec.ofNat 64 d) 64 := fun hd => hf'.readW (tR_contains s hd) tD (by decide)
  have hF : InF s (freed 48 s') := {
    sp := by show s'.sp + BitVec.ofNat 64 48 = _; rw [hsp, hw.sp, BitVec.sub_add_cancel]
    rd := hrd.trans hw.rd
    wr := by show s'.wr.tail = _; rw [hwr, hw.wr]; rfl
    hi := fun r hr => (hpres r (by revert r; decide)).trans (hw.hi r hr)
    sv := hw.sv.frame_in saved_offs hf' fun r hr => (hW r hr).2
    fr := hw.fr.trans (hf'.sub fun r hr => (hW r hr).1) }
  refine { hF with
    s1 := (hpres .s1 (by decide)).trans hw.s1
    tape0 := by
      have := tC (d := 0) (by decide); rw [BitVec.add_zero] at this
      show s'.mem.readW _ 64 = _; rw [this]; exact hw.tape0
    tape1 := by show s'.mem.readW _ 64 = _; rw [tC (by decide)]; exact hw.tape1
    res := fun hq => ?_ }
  sig_post [Proof.RsaPkcs1Enc.encryptPrecomputedContract, Proof.RsaPkcs1Enc.encryptPrecomputedSig, abi, argRegs,
    Enc.stackArgs_six, List.append_eq] at hpost
  rw [entry_arg hw _ _ (j := 0) (by decide), entry_arg hw _ _ (j := 1) (by decide),
    entry_arg hw _ _ (j := 4) (by decide), entry_arg hw _ _ (j := 5) (by decide)] at hpost
  simp only [hw.a0, hw.a2, hw.a3, hw.a4, hw.a5, hw.a6, hw.a7] at hpost
  have hl : (callArg s 1).toNat = psLen s := by
    show (BitVec.ofNat 64 (psLen s)).toNat = _; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have nE : Spec.Rsa.bytesAt w.mem (s.gpr .a3) (s.gpr .a4).toNat = nB s :=
    bytes_mem (R := nR s) hw.fr (k_dis hp.kn) hp.tn hp.on hp.ns.symm (low_dis hp.kn)
      (by have := hp.wn; show (s.gpr .a4).toNat ≤ 2 ^ 64; omega)
  have eE : Spec.Rsa.bytesAt w.mem (s.gpr .a5) (s.gpr .a6).toNat = eB s :=
    bytes_mem (R := eR s) hw.fr (k_dis hp.ke) hp.te hp.oe hp.es.symm (low_dis hp.ke)
      (by have := hp.we; show (s.gpr .a6).toNat ≤ 2 ^ 64; omega)
  have mE : Spec.Rsa.bytesAt w.mem (s.gpr .a7) (stackArg s 0).toNat = msgB s :=
    bytes_mem (R := mR s) hw.fr (k_dis hp.km) hp.tm hp.om hp.ms.symm (low_dis hp.km)
      (by have := hp.wm; show (stackArg s 0).toNat ≤ 2 ^ 64; omega)
  have qE : Spec.Rsa.wordsAt w.mem (stackArg s 5) (stackArg s 6).toNat = preW s :=
    words_mem hw.fr (k_dis hp.kp) hp.tp hp.op hp.sp (low_dis hp.kp) hp.wp
  rw [hl, show callArg s 0 = psA s from rfl, hw.buf, nE, eE, mE, show callArg s 4 = stackArg s 5 from rfl,
    show callArg s 5 = stackArg s 6 from rfl, qE] at hpost
  exact hpost hq



open VG VG.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64 VG.Proof.RsaPkcs1Sig.RISCV64 VG.WriteBytes
open VG.Impl.RsaPkcs1Enc.RISCV64.Random

/-- `writtenRandom` from `written` and the status `2 - r`. -/
theorem written_random {m : Mem} {out : Addr} {k : Nat} {r : BitVec 32} {res : Option (List Byte)}
    (h : Spec.Rsa.written m out k r res) :
    Spec.RsaPkcs1Enc.writtenRandom m out k (2 - r) res := by
  cases res with
  | some C => obtain ⟨h1, h2⟩ := h; subst h1; exact ⟨rfl, h2⟩
  | none => obtain ⟨h1, h2⟩ := h; subst h1; exact ⟨rfl, h2⟩

theorem setWidth_sub2 (x : BitVec 64) : (BitVec.ofNat 64 2 - x).setWidth 32 = 2 - x.setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  show _ = (2 ^ 32 - x.toNat % 2 ^ 32 + 2) % 2 ^ 32
  have := x.isLt
  omega

/-- The bytes of a region apart from a buffer written. -/
theorem bytes_wb {m : Mem} {q : Addr} {xs : List Byte} {R : Region} (hd : R.Disjoint ⟨q, xs.length⟩)
    (hl : R.len ≤ 2 ^ 64) : Spec.Rsa.bytesAt (writeBytes m q xs) R.base R.len = Spec.Rsa.bytesAt m R.base R.len :=
  Proof.RsaPkcs1Sig.bytes_apart (Proof.RsaPkcs1Sig.frame_writeBytes m q xs) hd hl

theorem word_wb {m : Mem} {q : Addr} {xs : List Byte} {R : Region} {a : Addr} (ha : R.Contains a 8)
    (hd : R.Disjoint ⟨q, xs.length⟩) : (writeBytes m q xs).readW a 64 = m.readW a 64 :=
  (Proof.RsaPkcs1Sig.frame_writeBytes m q xs).readW ha (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd)
    (by decide)

theorem in_ps {s : State} (hp : RPre s) (rs : List Region) {n j : Nat} (hn : n ≤ psLen s) (hj : j < n) :
    InRegions (kR s :: rs) (psA s + BitVec.ofNat 64 j) 1 := by
  rw [psA, Enc.add_ofNat_ofNat]; exact in_fr s _ (by have := psLen_le hp; unfold oEM1 frameBytes; omega)

theorem fb_al8' {s : State} (hp : RPre s) : (fb s).toNat % 8 = 0 := by have := fb_al hp.spal (sp1' hp); omega

theorem psLen_pos {s : State} (hp : RPre s) : 8 ≤ psLen s := by have := hp.ml; have := hp.k1; unfold psLen; omega

/-! ## `PS` full -/

theorem accTail_ok {s u : State} (hp : RPre s) {i : Nat} {ps : List Byte} (h : AfterCall s u i ps) :
    WP isa (.seq (.block status) (.seq fillLoop (.block restore))) u fun x =>
      abiPreserved s (freed frameBytes x) ∧ x.mem.readW (s.gpr .a2) 64 = BitVec.ofNat 64 i ∧
      x.mem.readW (s.gpr .a2 + BitVec.ofNat 64 8) 64 = 0 ∧
      (PreOk s → Spec.RsaPkcs1Enc.writtenRandom x.mem (s.gpr .a0) (s.gpr .a4).toNat ((x.gpr .a0).setWidth 32)
        (Spec.RsaPkcs1Enc.encrypt (nB s) (eB s) (msgB s) ps)) := by
  have hP := psLen_le hp
  have hP' := psLen_pos hp
  unfold status
  refine WP.seq (wp_li (imm := 2) (by decide) fun u₁ o₁ e₁ => wp_sub fun u₂ o₂ e₂ => wp_addSp fun u₃ o₃ e₃ =>
    wp_addi (imm := oPS) fun u₄ o₄ e₄ => wp_mov fun u₅ o₅ e₅ => wp_li (imm := 0) (by decide) fun u₆ o₆ e₆ =>
    wp_nil ?_)
  have O : Only [.t0, .a0, .t0, .a1, .t5, .t0] u u₆ := o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans o₆))))
  have hF : InF s u₆ := h.toInF.only O
  have a1₆ : u₆.gpr .a1 = psA s := by
    rw [o₆.get .a1, o₅.get .a1, e₄, e₃, o₂.sp, o₁.sp, h.sp, BitVec.add_zero]; rfl
  have t5₆ : u₆.gpr .t5 = BitVec.ofNat 64 (psLen s) := by
    rw [o₆.get .t5, e₅, o₄.get .s1, o₃.get .s1, o₂.get .s1, o₁.get .s1, h.s1]
  have a0₆ : u₆.gpr .a0 = BitVec.ofNat 64 2 - u.gpr .a0 := by
    rw [o₆.get .a0, o₅.get .a0, o₄.get .a0, o₃.get .a0, e₂, e₁, o₁.get .a0]
  refine WP.seq (WP.mono (fill_ok (p := psA s) (n := psLen s) (b := 0) (by omega) (by omega) a1₆ t5₆
    (by rw [e₆]; rfl) (fun j hj => by rw [hF.wr]; exact in_ps hp _ (Nat.le_refl _) hj)) fun w ⟨kw, mw⟩ => ?_)
  have hl : (List.replicate (psLen s) (0 : Byte)).length = psLen s := List.length_replicate ..
  have hF' : InF s w := hF.step kw (R := [⟨psA s, (List.replicate (psLen s) (0 : Byte)).length⟩])
    (by rw [mw]; exact Proof.RsaPkcs1Sig.frame_writeBytes _ _ _)
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact wok_ps hp hl)
  have hD : ∀ {R : Region}, (stR s).Disjoint R → R.Disjoint ⟨psA s, (List.replicate (psLen s) (0 : Byte)).length⟩ :=
    fun hR => by rw [hl]; exact (ps_dis hp hR).symm
  refine WP.mono (restore_ok hF'.saves (fb_al8' hp)) fun x ⟨habi, ha0, hxm⟩ => ⟨habi, ?_, ?_, fun hq => ?_⟩
  · rw [hxm, mw, word_wb (tR_contains0 s) (hD hp.kt), O.mem]; exact h.tape0
  · rw [hxm, mw, word_wb (tR_contains s (by decide)) (hD hp.kt), O.mem]; exact h.tape1
  · have hw := written_random (h.res hq)
    have hb : Spec.Rsa.bytesAt x.mem (s.gpr .a0) (s.gpr .a4).toNat =
        Spec.Rsa.bytesAt u.mem (s.gpr .a0) (s.gpr .a4).toNat := by
      rw [hxm, mw, bytes_wb (R := oR' s) (hD (by rw [← oR_eq hp]; exact hp.ko))
        (by have := hp.wo; rw [hp.ok] at this; show (s.gpr .a4).toNat ≤ 2 ^ 64; omega),
        O.mem]
    rw [ha0, kw.get .a0, a0₆, setWidth_sub2]
    cases hres : Spec.RsaPkcs1Enc.encrypt (nB s) (eB s) (msgB s) ps <;> rw [hres] at hw <;>
      exact ⟨hw.1, hb.trans hw.2⟩

/-! ## `PS` not full -/

/-- The budget's two outcomes, after `out` is zeroed and the octets drawn wiped. -/
theorem budget_ok {s y : State} (hp : RPre s) (hF : InF s y) {c : Nat} (ha2 : y.gpr .a2 = s.gpr .a2)
    (ht4 : y.gpr .t4 = stackArg s 2) (hs1 : y.gpr .s1 = BitVec.ofNat 64 (psLen s))
    (ht3 : y.gpr .t3 = BitVec.ofNat 64 c) (hc : c < psLen s) (hcl : c ≤ (stackArg s 2).toNat) :
    WP isa (.seq (.block [.addi .t0 .s1 128]) (.seq (.ite (.ltu .t4 .t0) request (.block exhausted))
      (.block restore))) y fun x =>
      abiPreserved s (freed frameBytes x) ∧ Frame [tR s] y.mem x.mem ∧
      (Spec.RsaPkcs1Enc.padEntropy (psLen s) ≤ (stackArg s 2).toNat →
        x.mem.readW (s.gpr .a2) 64 = stackArg s 2 ∧ x.mem.readW (s.gpr .a2 + BitVec.ofNat 64 8) 64 = 0 ∧
        (x.gpr .a0).setWidth 32 = 3) ∧
      ((stackArg s 2).toNat < Spec.RsaPkcs1Enc.padEntropy (psLen s) →
        x.mem.readW (s.gpr .a2) 64 = 0 ∧
        x.mem.readW (s.gpr .a2 + BitVec.ofNat 64 8) 64 =
          BitVec.ofNat 64 (min (Spec.RsaPkcs1Enc.padEntropy (psLen s)) (psLen s + (stackArg s 2).toNat - c)) ∧
        (x.gpr .a0).setWidth 32 = 0) := by
  have hP := psLen_le hp
  have hrl := hp.rl
  have hpe : Spec.RsaPkcs1Enc.padEntropy (psLen s) = psLen s + 128 := rfl
  refine WP.seq (wp_addi (imm := 128) fun y₁ o₁ e₁ => wp_nil ?_)
  rw [hs1, BitVec.ofNat_add_ofNat] at e₁
  have hF₁ : InF s y₁ := hF.only o₁
  have hwt : ∀ {x : State}, x.wr = kR s :: s.wr → ∀ {d : Nat}, d + 8 ≤ 16 →
      InRegions x.wr (s.gpr .a2 + BitVec.ofNat 64 d) 8 := fun hw d hd => by
    rw [hw, hp.hwr]; exact ⟨tR s, by simp, tR_contains s hd⟩
  have hwt0 : ∀ {x : State}, x.wr = kR s :: s.wr → InRegions x.wr (s.gpr .a2) 8 := fun hw => by
    rw [hw, hp.hwr]; exact ⟨tR s, by simp, tR_contains0 s⟩
  have hev : isa.eval (.ltu .t4 .t0) y₁ =
      some (decide ((stackArg s 2).toNat < Spec.RsaPkcs1Enc.padEntropy (psLen s))) := by
    show some (decide (y₁.gpr .t4 < y₁.gpr .t0)) = _
    rw [o₁.get .t4, ht4, e₁, ← ofNat_lt (a := (stackArg s 2).toNat) (by omega) (by omega), ofNat_toNat]; rfl
  by_cases hlt : (stackArg s 2).toNat < Spec.RsaPkcs1Enc.padEntropy (psLen s)
  · refine WP.seq (WP.ite true (by rw [hev, decide_eq_true hlt]) (fun _ => ?_) (fun h => absurd h (by decide)))
    unfold request
    refine WP.seq (wp_li (imm := 0) (by decide) fun y₂ o₂ e₂ => ?_)
    refine wp_sd (a := s.gpr .a2) (by rw [o₂.get .a2, o₁.get .a2, ha2, BitVec.add_zero]) hp.alt
      (hwt0 (by rw [o₂.wr, hF₁.wr])) fun y₃ m₃ => wp_add fun y₄ o₄ e₄ => wp_sub fun y₅ o₅ e₅ => wp_nil ?_
    have hv : y₅.gpr .t1 = BitVec.ofNat 64 (psLen s + (stackArg s 2).toNat - c) := by
      rw [e₅, o₄.get .t3, m₃.gpr, o₂.get .t3, o₁.get .t3, ht3, e₄, m₃.gpr, o₂.get .s1, o₁.get .s1, hs1,
        o₂.get .t4, o₁.get .t4, ht4]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
      have := (stackArg s 2).isLt
      omega
    have t0₅ : y₅.gpr .t0 = BitVec.ofNat 64 (Spec.RsaPkcs1Enc.padEntropy (psLen s)) := by
      rw [o₅.get .t0, o₄.get .t0, m₃.gpr, o₂.get .t0, e₁]; rfl
    -- the minimum
    have hmin : WP isa (.ite (.ltu .t0 .t1) (.block [mov .t1 .t0]) (.block [])) y₅ fun y₆ =>
        Only [.t1] y₅ y₆ ∧ y₆.gpr .t1 =
          BitVec.ofNat 64 (min (Spec.RsaPkcs1Enc.padEntropy (psLen s)) (psLen s + (stackArg s 2).toNat - c)) := by
      have hev' : isa.eval (.ltu .t0 .t1) y₅ = some (decide (Spec.RsaPkcs1Enc.padEntropy (psLen s) <
          psLen s + (stackArg s 2).toNat - c)) := by
        show some (decide (y₅.gpr .t0 < y₅.gpr .t1)) = _
        rw [t0₅, hv, ofNat_lt (by omega) (by omega)]
      by_cases hm : Spec.RsaPkcs1Enc.padEntropy (psLen s) < psLen s + (stackArg s 2).toNat - c
      · refine WP.ite true (by rw [hev', decide_eq_true hm]) (fun _ => wp_mov fun y₆ o₆ e₆ => wp_nil ⟨o₆, ?_⟩)
          (fun h => absurd h (by decide))
        rw [e₆, t0₅, Nat.min_eq_left (by omega)]
      · refine WP.ite false (by rw [hev', decide_eq_false hm]) (fun h => absurd h (by decide))
          fun _ => wp_nil ⟨Only.refl _ _, ?_⟩
        rw [hv, Nat.min_eq_right (by omega)]
    refine WP.seq (WP.mono hmin fun y₆ ⟨o₆, e₆⟩ => ?_)
    have O₆ : Only [.t1, .t1, .t1] y₃ y₆ := o₄.trans (o₅.trans o₆)
    refine wp_sd (a := s.gpr .a2 + BitVec.ofNat 64 8) (by rw [O₆.get .a2, m₃.gpr, o₂.get .a2, o₁.get .a2, ha2])
      (Spill.al8 hp.alt (by decide)) (hwt (by rw [O₆.wr, m₃.wr, o₂.wr, hF₁.wr]) (by decide)) fun y₇ m₇ =>
      wp_li (imm := 0) (by decide) fun y₈ o₈ e₈ => wp_nil ?_
    have fr₈ : Frame [tR s] y.mem y₈.mem := by
      rw [o₈.mem, m₇.mem, O₆.mem, m₃.mem, o₂.mem, o₁.mem]
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (tR_contains0 s)).writeW
        (List.mem_singleton_self _) _ (tR_contains s (by decide))
    have hF₈ : InF s y₈ := hF.step ((o₁.keep.trans (o₂.keep.trans (m₃.keep.trans (O₆.keep.trans
      (m₇.keep.trans o₈.keep)))))) fr₈ (fun r h => by rw [List.mem_singleton.mp h]; exact wok_apart (by simp) hp.kt)
    refine WP.mono (restore_ok hF₈.saves (fb_al8' hp)) fun x ⟨habi, ha0, hxm⟩ =>
      ⟨habi, hxm ▸ fr₈, fun h => absurd h (by omega), fun _ => ⟨?_, ?_, ?_⟩⟩
    · rw [hxm, o₈.mem, m₇.mem, Mem.readW_writeW_sep (Offset.sep_base _ (by decide) (by decide)) (by decide),
        O₆.mem, m₃.mem, Mem.readW_writeW_self64, e₂]; rfl
    · rw [hxm, o₈.mem, m₇.mem, Mem.readW_writeW_self64, e₆]
    · rw [ha0, e₈]; rfl
  · refine WP.seq (WP.ite false (by rw [hev, decide_eq_false hlt]) (fun h => absurd h (by decide)) fun _ => ?_)
    unfold exhausted
    refine wp_sd (a := s.gpr .a2) (by rw [o₁.get .a2, ha2, BitVec.add_zero]) hp.alt (hwt0 hF₁.wr)
      fun y₂ m₂ => wp_li (imm := 0) (by decide) fun y₃ o₃ e₃ => ?_
    refine wp_sd (a := s.gpr .a2 + BitVec.ofNat 64 8) (by rw [o₃.get .a2, m₂.gpr, o₁.get .a2, ha2])
      (Spill.al8 hp.alt (by decide)) (hwt (by rw [o₃.wr, m₂.wr, hF₁.wr]) (by decide)) fun y₄ m₄ =>
      wp_li (imm := 3) (by decide) fun y₅ o₅ e₅ => wp_nil ?_
    have fr₅ : Frame [tR s] y.mem y₅.mem := by
      rw [o₅.mem, m₄.mem, o₃.mem, m₂.mem, o₁.mem]
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (tR_contains0 s)).writeW
        (List.mem_singleton_self _) _ (tR_contains s (by decide))
    have hF₅ : InF s y₅ := hF.step ((o₁.keep.trans (m₂.keep.trans (o₃.keep.trans (m₄.keep.trans o₅.keep)))))
      fr₅ (fun r h => by rw [List.mem_singleton.mp h]; exact wok_apart (by simp) hp.kt)
    refine WP.mono (restore_ok hF₅.saves (fb_al8' hp)) fun x ⟨habi, ha0, hxm⟩ =>
      ⟨habi, hxm ▸ fr₅, fun _ => ⟨?_, ?_, ?_⟩, fun h => absurd h hlt⟩
    · rw [hxm, o₅.mem, m₄.mem, Mem.readW_writeW_sep (Offset.sep_base _ (by decide) (by decide)) (by decide),
        o₃.mem, m₂.mem, Mem.readW_writeW_self64, o₁.get .t4, ht4]
    · rw [hxm, o₅.mem, m₄.mem, Mem.readW_writeW_self64, e₃]; rfl
    · rw [ha0, e₅]; rfl

end VG.Proof.RsaPkcs1Enc.RISCV64.Rnd

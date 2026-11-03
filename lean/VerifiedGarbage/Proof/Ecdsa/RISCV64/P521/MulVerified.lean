module

public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.MulFn
public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.Window
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Weierstrass.PointFacts
import VerifiedGarbage.Proof.P521.Point
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Weierstrass.RISCV64.Copy
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.MulLit
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.MulFn
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.Window
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Weierstrass.PointFacts
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P521.MulLit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint

/-!
# `vg_p521_mul` on RISC-V: the contract

The facts of `Impl.Weierstrass.Mul.Curve.mulInRangeContract` for P-521 on
RISC-V, by register (`mulRVc`: `ws` in `a0`), and `mulFn` meets them
(`mul_rv`), given the group law: the saves of `s0`, `s1` and `ra` (past the
numbered slots, in the contract's tail), the windows' `body_ok`, and the loads that
restore them. The coordinates the specification decodes are the proofs'
(`Point.dec_eq`, given Fermat's little theorem from the group law), and
`Represents` is `Rep`. What the function writes is its own working space or
the result's (`keeps_of_unch`).

`mul_verified` adds the function's constant time, by taint tracking (only the
pointer, in `a0`, public: every address is `s0` plus a constant or plus the
counter's word, and the only branches are on the counter and on the field
functions' pointers), and a state satisfying the precondition (`satState`:
the constants and `G` in Montgomery's form at their slots).
-/

-- `p`, below `2^521`, is evaluated.
set_option exponentiation.threshold 1024

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.P521

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Spec.Weierstrass (Curve Fe Point)

/-- P-521's curve of `Proof/Weierstrass/MulContract.lean`. -/
abbrev MC : Impl.Weierstrass.Mul.Curve := Impl.Weierstrass.Mul.p521

/-- `vg_p521_mul(ws = a0)`. -/
def mulRVc : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .a0, 8192⟩] ∧ (s.gpr .a0).toNat + 8192 ≤ 2 ^ 64 ∧
    (s.gpr .a0).toNat % 8 = 0 ∧ MC.ConstsOk (s.gpr .a0) s.mem ∧ MC.PointOk (s.gpr .a0) s.mem
  post s s' := MC.ResultInRange (MC.scalar (s.gpr .a0) s.mem) (MC.point (s.gpr .a0) s.mem) (s.gpr .a0) s.mem s'.mem
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0

/-- `Represents` is the proofs' `Rep`. -/
theorem represents_of_rep {C : Curve} {X Y Z : Fe C} {P : Point C}
    (h : Rep C X Y Z P) : Impl.Weierstrass.MulBase.Represents X Y Z P := by
  cases P <;> exact h

/-- The coordinate at an offset below `2³²` is the number `wordsVal` reads. -/
theorem coordAt_eq (m : Mem) (ws : Addr) {o : Nat} (ho : o < 2 ^ 32) :
    MC.toPoint.coordAt m ws o = wordsVal m ws o 9 := by
  unfold Impl.Weierstrass.Point.Curve.coordAt
  rw [Impl.Weierstrass.Mont.numAt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]
  exact read_eq_wordsVal m ws 9 o

/-- The saves, at `mulSave = 3304`. -/
abbrev saves : List (Nat × Nat) := [(3304, 8), (3312, 8), (3320, 8)]

/-- What the conversion in writes: `Q`'s slots, `UA` to `UC`, and the field
functions' own working space. -/
abbrev cinW : List (Nat × Nat) := [(1072, 144), (3592, 288), (7616, 576)]

/-- What the conversion out writes. -/
abbrev coutW : List (Nat × Nat) := [(1072, 216), (3808, 72), (7616, 576)]


/-- What the function writes is its own working space or the result's. -/
theorem keeps_of_unch {ws : Addr} {m m' : Mem} (hu : Unch ws (saves ++ ((cinW ++ Window.bodyW) ++ coutW)) m m') :
    MC.Keeps ws m m' := by
  intro i hi hown hp
  have h8 : Impl.Weierstrass.Mont.wsBytes = 8192 := rfl
  refine hu _ fun w hw => ?_
  rw [show ws + BitVec.ofNat 64 i = off ws i from rfl, ofs_off0 ws (by omega)]
  have hw' := (by decide : ∀ w ∈ saves ++ ((cinW ++ Window.bodyW) ++ coutW), (1072 ≤ w.1 ∧ w.1 + w.2 ≤ 2296) ∨ 3304 ≤ w.1) w hw
  simp only [Impl.Weierstrass.Mul.Curve.Own, Impl.Weierstrass.Mul.Curve.slot, Impl.Weierstrass.Mul.Curve.tmpAt,
    Impl.Weierstrass.Mul.Curve.bitsAt, Impl.Weierstrass.Mul.Curve.pAt, Impl.Weierstrass.Mul.Curve.ptBytes,
    MC, Impl.Weierstrass.Mul.p521, true_and] at hown hp
  omega

/-- `sd t, d(a0)` (`sdAt`) at the working space's base. -/
theorem sdAt_a0 {s : State} {base : Addr} {is : List Instr} {Q : State → Prop} (h0 : s.gpr .a0 = base)
    (hwr : (⟨base, 8192⟩ : Region) ∈ s.wr) (hal : base.toNat % 8 = 0) {t : Reg} (ht : t ≠ .a0) {d : Nat}
    (hd : d + 8 ≤ 4096) (hd8 : d % 8 = 0)
    (k : ∀ s', Mupd s s' (s.mem.writeW (off base d) (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (sdAt t .a0 d ++ is)) s Q :=
  wp_sdAt (by omega) ht (by rw [h0]) (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    ⟨_, hwr, Offset.contains_base base (by omega) (by omega)⟩ k

/-! ## The conversions -/

section Conv

open VG.Impl.Ecdsa.RISCV64.WindowU (c UA UB UONE UC F toU fromU convIn convOut setIn setOut setC)
open VG.Proof.Weierstrass.RISCV64.P521Unsat (uf Tight TightF uv wv lw umulCall_ok unpackCall_ok packCall_ok uf_eq own9)
open VG.Proof.Ecdsa.RISCV64.P521.Window (ev PtOk)
open VG.Proof.X25519.RISCV64 (Rest)

/-- Slots apart from the ones a field program wrote keep their numbers. -/
theorem keepR_wv {s s' : State} {base : Addr} {Wl : List Nat} (k : KeepR 9 base Wl s s') {d : Nat}
    (hd : ∀ o ∈ Wl, d + 72 ≤ o ∨ o + 72 ≤ d) (hd' : d + 72 ≤ 7616) : wv base s' d = wv base s d :=
  outs_wordsVal k.mem (fun r hr => by
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hr
    rcases hr with ⟨o, ho, rfl⟩ | rfl
    · exact hd o ho
    · exact .inl (by rw [own9]; exact hd')) (by omega)

theorem tight_in : Tight (2 ^ 512 * 4) := by unfold Tight TightF lw; decide
theorem uv_in : uv (2 ^ 512 * 4) = 2 ^ 466 := by decide
theorem tight_out : Tight (2 ^ 55) := by unfold Tight TightF lw; decide
theorem uv_out : uv (2 ^ 55) = 2 ^ 55 := by decide

/-- `2⁴⁶⁶` is `R⁻¹` modulo `p`. -/
theorem inv_R : (2 ^ 576 * 2 ^ 466) % W.p = 1 := by decide

/-- The limbs' element, times `2⁴⁶⁶`, of a number in Montgomery's form. -/
theorem ofNat_in (x : Nat) : (Fin.ofNat W.p (2 ^ 576 * x % W.p * 2 ^ 466) : Fe W) = Fin.ofNat W.p x := by
  apply Fin.ext
  simp only [Fin.val_ofNat]
  rw [Nat.mod_mul_mod, show 2 ^ 576 * x * 2 ^ 466 = x * (2 ^ 576 * 2 ^ 466) by ac_rfl, Nat.mul_mod, inv_R,
    Nat.mul_one, Nat.mod_mod]

/-- The limbs' element, times `2⁴⁶⁶`, of a number below `p`: its decoding. -/
theorem ofNat_in_toM {w : Nat} (hw : w < W.p) :
    (Fin.ofNat W.p (w * 2 ^ 466) : Fe W) = toM W.p (2 ^ 576) w := by
  have e : w * 2 ^ 466 * 2 ^ 576 % W.p = w := by
    rw [Nat.mul_assoc, Nat.mul_mod, show 2 ^ 466 * 2 ^ 576 = 2 ^ 576 * 2 ^ 466 from Nat.mul_comm _ _, inv_R,
      Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hw]
  rw [← toM_mont (R := 2 ^ 576) unit (x := w * 2 ^ 466), e]

/-- The residue of limbs times `2⁵⁵`: their element in Montgomery's form. -/
theorem toM_out (y : Nat) : toM W.p (2 ^ 576) (y * 2 ^ 55 % W.p) = Fin.ofNat W.p y := by
  have e : y * 2 ^ 55 % W.p = y * 2 ^ 576 % W.p := by
    rw [Nat.mul_mod, Nat.mul_mod y (2 ^ 576), show 2 ^ 55 % W.p = 2 ^ 576 % W.p by decide]
  rw [e, toM_mont unit]

/-- `UC = 2⁴⁶⁶` in limbs. -/
theorem setIn_ok {s : State} {base : Addr} (hw : WsReg s base) (hz : wordsVal s.mem base (c.sl ZERO) 9 = 0) :
    WP isa (.block setIn) s fun s' => Rest [.t0] s s' ∧ Unch base [(c.sl UC, 72)] s.mem s'.mem ∧
      Tight (wv base s' (c.sl UC)) ∧ uv (wv base s' (c.sl UC)) = 2 ^ 466 := by
  have hn := hw.nowrap
  have hUC : c.sl UC = 3808 := rfl
  rw [setIn, setC, List.append_assoc]
  refine WP.block_append (WP.mono (copy_ok 9 hw (o := c.sl UC) (a := c.sl ZERO) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₁ ⟨e₁, r₁, O₁⟩ => ?_)
  have hw₁ := hw.of_rest r₁
  refine wp_li (imm := 4) (by decide) fun s₂ u₂ => ?_
  have hw₂ := hw₁.of_rest (u₂.rest (ws := [.t0]) (by decide))
  rw [← List.append_nil (sdAt _ _ _)]
  refine sdAt_ws hw₂ (by decide) (d := c.sl UC + 8 * 8) (by decide) (by decide) fun s₃ u₃ => WP.block_nil ?_
  have m₃ : s₃.mem = s₁.mem.writeW (off base (c.sl UC + 8 * 8)) (BitVec.ofNat 64 4) := by rw [u₃.mem, u₂.gpr, u₂.mem]
  have low : wordsVal s₁.mem base (c.sl UC) 8 = 0 := by
    have := wordsVal_succ_top s₁.mem base (c.sl UC) 8
    rw [e₁, hz] at this; omega
  have v₃ : wordsVal s₃.mem base (c.sl UC) 9 = 2 ^ 512 * 4 := by
    rw [wordsVal_succ_top, m₃, word_writeW_self, (writeW_outside _ _ _ (by omega)).wordsVal (.inl (by omega))
      (by omega), low]
    rfl
  refine ⟨(r₁.trans (u₂.rest (by decide))).trans (u₃.rest [.t0]), ?_,
    show Tight (wordsVal _ _ _ 9) by rw [v₃]; exact tight_in, show uv (wordsVal _ _ _ 9) = _ by rw [v₃]; exact uv_in⟩
  rw [m₃]
  exact (O₁.unch.trans ((writeW_outside _ _ _ (by omega)).unch)).cover (by decide)

/-- `UC = 2⁵⁵` in limbs. -/
theorem setOut_ok {s : State} {base : Addr} (hw : WsReg s base) (hz : wordsVal s.mem base (c.sl ZERO) 9 = 0) :
    WP isa (.block setOut) s fun s' => Rest [.t0] s s' ∧ Unch base [(c.sl UC, 72)] s.mem s'.mem ∧
      Tight (wv base s' (c.sl UC)) ∧ uv (wv base s' (c.sl UC)) = 2 ^ 55 := by
  have hn := hw.nowrap
  have hUC : c.sl UC = 3808 := rfl
  rw [setOut, setC, List.append_assoc]
  refine WP.block_append (WP.mono (copy_ok 9 hw (o := c.sl UC) (a := c.sl ZERO) (by decide) (by decide) (by decide)
    (by decide) (by decide)) fun s₁ ⟨e₁, r₁, O₁⟩ => ?_)
  have hw₁ := hw.of_rest r₁
  refine wp_li (imm := 1) (by decide) fun s₂ u₂ => wp_sll (by decide) fun s₃ u₃ => ?_
  have hw₃ := hw₁.of_rest ((u₂.rest (ws := [.t0]) (by decide)).trans (u₃.rest (by decide)))
  rw [← List.append_nil (sdAt _ _ _)]
  refine sdAt_ws hw₃ (by decide) (d := c.sl UC + 8 * 0) (by decide) (by decide) fun s₄ u₄ => WP.block_nil ?_
  have g₃ : s₃.gpr .t0 = BitVec.ofNat 64 (2 ^ 55) := by rw [u₃.gpr, u₂.gpr]; rfl
  have m₄ : s₄.mem = s₁.mem.writeW (off base (c.sl UC)) (BitVec.ofNat 64 (2 ^ 55)) := by
    rw [u₄.mem, g₃, u₃.mem, u₂.mem]; rfl
  have high : wordsVal s₁.mem base (c.sl UC + 8) 8 = 0 := by
    have : wordsVal s₁.mem base (c.sl UC) 9 =
        (word s₁.mem base (c.sl UC)).toNat + 2 ^ 64 * wordsVal s₁.mem base (c.sl UC + 8) 8 := rfl
    rw [e₁, hz] at this; omega
  have v₄ : wordsVal s₄.mem base (c.sl UC) 9 = 2 ^ 55 := by
    show (word s₄.mem base (c.sl UC)).toNat + 2 ^ 64 * wordsVal s₄.mem base (c.sl UC + 8) 8 = _
    rw [m₄, word_writeW_self, (writeW_outside _ _ _ (by omega)).wordsVal (.inr (by omega)) (by omega), high]
    rfl
  refine ⟨((r₁.trans (u₂.rest (by decide))).trans (u₃.rest (by decide))).trans (u₄.rest [.t0]), ?_,
    show Tight (wordsVal _ _ _ 9) by rw [v₄]; exact tight_out, show uv (wordsVal _ _ _ 9) = _ by rw [v₄]; exact uv_out⟩
  rw [m₄]
  exact (O₁.unch.trans ((writeW_outside _ _ _ (by omega)).unch)).cover (by decide)

/-- `[o]` = the limbs of `[a]` times `2⁴⁶⁶`, for `UC = 2⁴⁶⁶`. -/
theorem toU_ok {s : State} {base : Addr} (hw : WsReg s base) {o a : Nat}
    (ho : o + 72 ≤ 4095) (ha : a + 72 ≤ 4095) (hoC : o + 72 ≤ c.sl UC ∨ c.sl UC + 72 ≤ o)
    (hA : wv base s a < 2 ^ 522) (hCt : Tight (wv base s (c.sl UC))) (hCv : uv (wv base s (c.sl UC)) = 2 ^ 466) :
    WP isa (toU o a) s fun s' => KeepR 9 base [o] s s' ∧ Tight (wv base s' o) ∧
      uf (wv base s' o) = Fin.ofNat W.p (wv base s a * 2 ^ 466) := by
  rw [toU]
  refine WP.seq (WP.mono (unpackCall_ok (f := F.S.fn "unpack") hw (o := o) (a := a) (b := 0) (by omega) (by omega)
    (by decide) (by omega) (by omega) (by decide) hA) fun s₁ ⟨K₁, t₁, v₁⟩ => ?_)
  have k₁ := KeepR.of_call K₁
  have eC : wv base s₁ (c.sl UC) = wv base s (c.sl UC) :=
    keepR_wv k₁ (by simp only [List.mem_singleton, forall_eq]; omega) (by decide)
  refine WP.mono (umulCall_ok (hw.of_kp K₁.kp) (o := o) (a := o) (b := c.sl UC) (by omega) (by omega) (by decide)
    (by omega) (by omega) (by decide) t₁ (by rw [eC]; exact hCt)) fun s₂ ⟨K₂, t₂, v₂⟩ =>
    ⟨k₁.trans (KeepR.of_call K₂), t₂, uf_eq (by rw [v₂, v₁, eC, hCv])⟩

/-- `[o]` = the residue of the limbs at `o` times `2⁵⁵`, for `UC = 2⁵⁵`. -/
theorem fromU_ok {s : State} {base : Addr} (hw : WsReg s base) {o : Nat}
    (ho : o + 72 ≤ 4095) (hO : Tight (wv base s o))
    (hCt : Tight (wv base s (c.sl UC))) (hCv : uv (wv base s (c.sl UC)) = 2 ^ 55) :
    WP isa (fromU o) s fun s' => KeepR 9 base [o] s s' ∧
      wv base s' o = uv (wv base s o) * 2 ^ 55 % P521Unsat.p := by
  rw [fromU]
  refine WP.seq (WP.mono (umulCall_ok hw (o := o) (a := o) (b := c.sl UC) (by omega) (by omega) (by decide)
    (by omega) (by omega) (by decide) hO hCt) fun s₁ ⟨K₁, t₁, v₁⟩ => ?_)
  refine WP.mono (packCall_ok (f := F.S.fn "pack") (hw.of_kp K₁.kp) (o := o) (a := o) (b := 0) (by omega)
    (by omega) (by decide) (by omega) (by omega) (by decide) t₁) fun s₂ ⟨K₂, v₂⟩ =>
    ⟨(KeepR.of_call K₁).trans (KeepR.of_call K₂), by rw [v₂, v₁, hCv]⟩

end Conv

section ConvAll

open VG.Impl.Ecdsa.RISCV64.WindowU (c UA UB UONE UC F toU fromU convIn convOut setIn setOut setC)
open VG.Proof.Weierstrass.RISCV64.P521Unsat (uf Tight TightF uv wv lw umulCall_ok unpackCall_ok packCall_ok uf_eq own9)
open VG.Proof.X25519.RISCV64 (Rest)

/-- A step keeps what lies apart from its output. -/
theorem fr {base : Addr} {t t' : State} {o : Nat} (k : KeepR 9 base [o] t t') (d : Nat)
    (h1 : d + 72 ≤ o ∨ o + 72 ≤ d) (h2 : d + 72 ≤ 7616) : wv base t' d = wv base t d :=
  keepR_wv k (by simpa using h1) h2

/-- `Q`, one, `a` and `3 b` to limbs. -/
theorem convIn_ok {s : State} {base : Addr} (hw : WsReg s base) (hz : wordsVal s.mem base (c.sl ZERO) 9 = 0)
    (hx : wv base s (c.sl RX) < 2 ^ 522) (hy : wv base s (c.sl RY) < 2 ^ 522)
    (ho : wv base s (c.sl ONEP) < 2 ^ 522) (ha : wv base s (c.sl AP) < 2 ^ 522)
    (hb : wv base s (c.sl B3P) < 2 ^ 522) :
    WP isa convIn s fun s' => Kp s s' ∧ Unch base cinW s.mem s'.mem ∧
      ∀ q ∈ [(c.sl RX, c.sl RX), (c.sl RY, c.sl RY), (c.sl UONE, c.sl ONEP), (c.sl UA, c.sl AP),
          (c.sl UB, c.sl B3P)],
        Tight (wv base s' q.1) ∧ uf (wv base s' q.1) = Fin.ofNat W.p (wv base s q.2 * 2 ^ 466) := by
  have hn := hw.nowrap
  have hUC : c.sl UC = 3808 := rfl
  rw [convIn]
  simp only [progs]
  refine WP.seq (WP.mono (setIn_ok hw hz) fun s₁ ⟨r₁, U₁, tc₁, vc₁⟩ => ?_)
  have hw₁ := hw.of_rest r₁
  have e₁ : ∀ d, d + 72 ≤ c.sl UC ∨ c.sl UC + 72 ≤ d ∧ d + 72 ≤ 4095 → wv base s₁ d = wv base s d :=
    fun d hd => U₁.wordsVal (by simp only [List.mem_singleton, forall_eq]; omega) (by omega)
  refine WP.seq (WP.mono (toU_ok hw₁ (o := c.sl RX) (a := c.sl RX) (by decide) (by decide) (by decide)
    (by rw [e₁ _ (by decide)]; exact hx) tc₁ vc₁) fun s₂ ⟨k₂, t₂, v₂⟩ => ?_)
  have hw₂ := hw₁.of_kp k₂.kp
  have c₂ : wv base s₂ (c.sl UC) = wv base s₁ (c.sl UC) := fr k₂ _ (by decide) (by decide)
  refine WP.seq (WP.mono (toU_ok hw₂ (o := c.sl RY) (a := c.sl RY) (by decide) (by decide) (by decide)
    (by rw [fr k₂ _ (by decide) (by decide), e₁ _ (by decide)]; exact hy) (by rw [c₂]; exact tc₁)
    (by rw [c₂]; exact vc₁)) fun s₃ ⟨k₃, t₃, v₃⟩ => ?_)
  have hw₃ := hw₂.of_kp k₃.kp
  have c₃ : wv base s₃ (c.sl UC) = wv base s₁ (c.sl UC) := (fr k₃ _ (by decide) (by decide)).trans c₂
  refine WP.seq (WP.mono (toU_ok hw₃ (o := c.sl UONE) (a := c.sl ONEP) (by decide) (by decide) (by decide)
    (by rw [fr k₃ _ (by decide) (by decide), fr k₂ _ (by decide) (by decide), e₁ _ (by decide)]; exact ho)
    (by rw [c₃]; exact tc₁) (by rw [c₃]; exact vc₁)) fun s₄ ⟨k₄, t₄, v₄⟩ => ?_)
  have hw₄ := hw₃.of_kp k₄.kp
  have c₄ : wv base s₄ (c.sl UC) = wv base s₁ (c.sl UC) := (fr k₄ _ (by decide) (by decide)).trans c₃
  refine WP.seq (WP.mono (toU_ok hw₄ (o := c.sl UA) (a := c.sl AP) (by decide) (by decide) (by decide)
    (by rw [fr k₄ _ (by decide) (by decide), fr k₃ _ (by decide) (by decide), fr k₂ _ (by decide) (by decide),
      e₁ _ (by decide)]; exact ha)
    (by rw [c₄]; exact tc₁) (by rw [c₄]; exact vc₁)) fun s₅ ⟨k₅, t₅, v₅⟩ => ?_)
  have hw₅ := hw₄.of_kp k₅.kp
  have c₅ : wv base s₅ (c.sl UC) = wv base s₁ (c.sl UC) := (fr k₅ _ (by decide) (by decide)).trans c₄
  refine WP.mono (toU_ok hw₅ (o := c.sl UB) (a := c.sl B3P) (by decide) (by decide) (by decide)
    (by rw [fr k₅ _ (by decide) (by decide), fr k₄ _ (by decide) (by decide), fr k₃ _ (by decide) (by decide),
      fr k₂ _ (by decide) (by decide), e₁ _ (by decide)]; exact hb)
    (by rw [c₅]; exact tc₁) (by rw [c₅]; exact vc₁)) fun s₆ ⟨k₆, t₆, v₆⟩ => ⟨?_, ?_, ?_⟩
  · exact (Kp.of_rest r₁).trans (k₂.kp.trans (k₃.kp.trans (k₄.kp.trans (k₅.kp.trans k₆.kp))))
  · exact (U₁.trans (Unch.trans k₂.mem (Unch.trans k₃.mem (Unch.trans k₄.mem (Unch.trans k₅.mem k₆.mem))))).cover
      (by decide)
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · rw [fr k₆ _ (by decide) (by decide), fr k₅ _ (by decide) (by decide), fr k₄ _ (by decide) (by decide),
        fr k₃ _ (by decide) (by decide), ← e₁ (c.sl RX) (by decide)]
      exact ⟨t₂, v₂⟩
    · rw [fr k₆ _ (by decide) (by decide), fr k₅ _ (by decide) (by decide), fr k₄ _ (by decide) (by decide),
        ← e₁ (c.sl RY) (by decide), ← fr k₂ (c.sl RY) (by decide) (by decide)]
      exact ⟨t₃, v₃⟩
    · rw [fr k₆ _ (by decide) (by decide), fr k₅ _ (by decide) (by decide),
        ← e₁ (c.sl ONEP) (by decide), ← fr k₂ (c.sl ONEP) (by decide) (by decide),
        ← fr k₃ (c.sl ONEP) (by decide) (by decide)]
      exact ⟨t₄, v₄⟩
    · rw [fr k₆ _ (by decide) (by decide), ← e₁ (c.sl AP) (by decide), ← fr k₂ (c.sl AP) (by decide) (by decide),
        ← fr k₃ (c.sl AP) (by decide) (by decide), ← fr k₄ (c.sl AP) (by decide) (by decide)]
      exact ⟨t₅, v₅⟩
    · rw [← e₁ (c.sl B3P) (by decide), ← fr k₂ (c.sl B3P) (by decide) (by decide),
        ← fr k₃ (c.sl B3P) (by decide) (by decide), ← fr k₄ (c.sl B3P) (by decide) (by decide),
        ← fr k₅ (c.sl B3P) (by decide) (by decide)]
      exact ⟨t₆, v₆⟩

/-- `R` to Montgomery's form. -/
theorem convOut_ok {s : State} {base : Addr} (hw : WsReg s base) (hz : wordsVal s.mem base (c.sl ZERO) 9 = 0)
    (hx : Tight (wv base s (c.sl RX))) (hy : Tight (wv base s (c.sl RY))) (hzz : Tight (wv base s (c.sl RZ))) :
    WP isa convOut s fun s' => Kp s s' ∧ Unch base coutW s.mem s'.mem ∧
      ∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wv base s' x = uv (wv base s x) * 2 ^ 55 % P521Unsat.p := by
  have hn := hw.nowrap
  have hUC : c.sl UC = 3808 := rfl
  rw [convOut]
  simp only [progs]
  refine WP.seq (WP.mono (setOut_ok hw hz) fun s₁ ⟨r₁, U₁, tc₁, vc₁⟩ => ?_)
  have hw₁ := hw.of_rest r₁
  have e₁ : ∀ d, d + 72 ≤ c.sl UC ∨ c.sl UC + 72 ≤ d ∧ d + 72 ≤ 4095 → wv base s₁ d = wv base s d :=
    fun d hd => U₁.wordsVal (by simp only [List.mem_singleton, forall_eq]; omega) (by omega)
  refine WP.seq (WP.mono (fromU_ok hw₁ (o := c.sl RX) (by decide) (by rw [e₁ _ (by decide)]; exact hx)
    tc₁ vc₁) fun s₂ ⟨k₂, v₂⟩ => ?_)
  have hw₂ := hw₁.of_kp k₂.kp
  have c₂ : wv base s₂ (c.sl UC) = wv base s₁ (c.sl UC) := fr k₂ _ (by decide) (by decide)
  refine WP.seq (WP.mono (fromU_ok hw₂ (o := c.sl RY) (by decide)
    (by rw [fr k₂ _ (by decide) (by decide), e₁ _ (by decide)]; exact hy) (by rw [c₂]; exact tc₁)
    (by rw [c₂]; exact vc₁)) fun s₃ ⟨k₃, v₃⟩ => ?_)
  have hw₃ := hw₂.of_kp k₃.kp
  have c₃ : wv base s₃ (c.sl UC) = wv base s₁ (c.sl UC) := (fr k₃ _ (by decide) (by decide)).trans c₂
  refine WP.mono (fromU_ok hw₃ (o := c.sl RZ) (by decide)
    (by rw [fr k₃ _ (by decide) (by decide), fr k₂ _ (by decide) (by decide), e₁ _ (by decide)]; exact hzz)
    (by rw [c₃]; exact tc₁) (by rw [c₃]; exact vc₁)) fun s₄ ⟨k₄, v₄⟩ => ⟨?_, ?_, ?_⟩
  · exact (Kp.of_rest r₁).trans (k₂.kp.trans (k₃.kp.trans k₄.kp))
  · exact (U₁.trans (Unch.trans k₂.mem (Unch.trans k₃.mem k₄.mem))).cover (by decide)
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [fr k₄ _ (by decide) (by decide), fr k₃ _ (by decide) (by decide), v₂, e₁ _ (by decide)]
    · rw [fr k₄ _ (by decide) (by decide), v₃, fr k₂ _ (by decide) (by decide), e₁ _ (by decide)]
    · rw [v₄, fr k₃ _ (by decide) (by decide), fr k₂ _ (by decide) (by decide), e₁ _ (by decide)]

end ConvAll

/-- `vg_p521_mul` meets `mulRVc`, given the group law. -/
theorem mul_rv (hL : VG.Proof.Weierstrass.Law W) (s : State) (hs : mulRVc.pre s) :
    ∃ t s', Exec isa mulP521 s t s' ∧ abiPreserved s s' ∧ mulRVc.post s s' := by
  obtain ⟨-, hwr, hfit, hal, ⟨-, hz, hone, ha, hb3⟩, ⟨hx, hy, hon⟩⟩ := hs
  generalize hb : s.gpr .a0 = base at hwr hfit hal hz hone ha hb3 hx hy hon
  have hwr' : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hwr]; exact List.mem_singleton_self _
  have hpR := unit
  have hp0 : 0 < W.p := by decide
  have ca : ∀ (m : Mem) {o : Nat}, o < 4096 → MC.toPoint.coordAt m base o = wordsVal m base o 9 :=
    fun m _ ho => coordAt_eq m base (by omega)
  have dq : ∀ x, MC.toPoint.dec x = toM W.p (2 ^ 576) x :=
    VG.Proof.Weierstrass.Point.dec_eq MC.toPoint hL.one_ne_zero (VG.Proof.Weierstrass.Point.fermat_of_law hL) hpR
  -- The saves and `s0 = a0`.
  suffices h : WP isa mulP521 s fun s' => abiPreserved s s' ∧ mulRVc.post s s' by
    obtain ⟨t, s', he, h⟩ := h; exact ⟨t, s', he, h⟩
  rw [mulP521, WindowU.mulFn, show WindowU.c.mulSave = 3304 from rfl]
  simp only [List.append_assoc]
  rw [← List.append_nil (ldAt .s0 .s0 3304)]
  refine WP.seq (sdAt_a0 hb hwr' hal (by decide) (d := 3304) (by decide) (by decide) fun s₁ u₁ => ?_)
  refine sdAt_a0 (by rw [u₁.gpr]; exact hb) (by rw [u₁.wr]; exact hwr') hal (by decide) (d := 3312) (by decide)
    (by decide) fun s₂ u₂ => ?_
  refine sdAt_a0 (by rw [u₂.gpr, u₁.gpr]; exact hb) (by rw [u₂.wr, u₁.wr]; exact hwr') hal (by decide)
    (d := 3320) (by decide) (by decide) fun s₃ u₃ => wp_mv fun s₄ u₄ => WP.block_nil ?_
  have g₄ : ∀ r, r ≠ .s0 → s₄.gpr r = s.gpr r := fun r hr => by
    rw [u₄.other r hr, u₃.gpr, u₂.gpr, u₁.gpr]
  have hw₄ : WsReg s₄ base := ⟨by rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, hb],
    by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact hwr', hfit, hal⟩
  have m₄ : s₄.mem = ((s.mem.writeW (off base 3304) (s.gpr .s0)).writeW (off base 3312) (s.gpr .s1)).writeW
      (off base 3320) (s.gpr .ra) := by
    simp only [u₄.mem, u₃.mem, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr]
  have O₄ : Unch base saves s.mem s₄.mem := by
    rw [m₄]
    exact (((writeW_outside _ _ _ (by omega)).unch.trans (writeW_outside _ _ _ (by omega)).unch).trans
      (writeW_outside _ _ _ (by omega)).unch)
  have sv₄ : ∀ i, i < 45 → sv base s₄ i = sv base s i := fun i hi =>
    O₄.wordsVal (fun w hw => by
      simp only [saves, List.mem_cons, List.not_mem_nil, or_false] at hw
      have : p521.sl i + 72 ≤ 3304 := by simp only [Cfg.sl, slot, p521]; omega
      rcases hw with rfl | rfl | rfl <;> (simp only; omega)) (by simp only [Cfg.sl, slot, p521]; omega)
  have cs : ∀ i, i < 45 → MC.toPoint.coordAt s.mem base (p521.sl i) = sv base s i := fun i hi =>
    ca s.mem (by simp only [Cfg.sl, slot, p521]; omega)
  -- The slots' values, from the contract's.
  have hz' : sv base s₄ ZERO = 0 := by rw [sv₄ _ (by decide)]; exact (cs ZERO (by decide)).symm.trans hz
  have hone' : sv base s₄ ONEP = 2 ^ 576 % W.p := by
    rw [sv₄ _ (by decide)]; refine (cs ONEP (by decide)).symm.trans (hone.trans ?_)
    simp only [Impl.Weierstrass.Mul.Curve.mont, Nat.one_mul]; rfl
  have ha' : sv base s₄ AP = 2 ^ 576 * W.a % W.p := by
    rw [sv₄ _ (by decide)]; refine (cs AP (by decide)).symm.trans (ha.trans ?_)
    simp only [Impl.Weierstrass.Mul.Curve.mont]; rw [Nat.mul_comm]; rfl
  have hb3' : sv base s₄ B3P = 2 ^ 576 * (3 * W.b) % W.p := by
    rw [sv₄ _ (by decide)]; refine (cs B3P (by decide)).symm.trans (hb3.trans ?_)
    simp only [Impl.Weierstrass.Mul.Curve.mont]; rw [Nat.mul_comm]; rfl
  have tm : ∀ x, toM W.p (2 ^ 576) (2 ^ 576 * x % W.p) = Fin.ofNat W.p x := fun x => by
    rw [Nat.mul_comm]; exact toM_mont hpR
  have qx : (MC.qCoords base s.mem).1 = sv base s₄ RX := by rw [sv₄ _ (by decide)]; exact cs RX (by decide)
  have qy : (MC.qCoords base s.mem).2 = sv base s₄ RY := by
    rw [sv₄ _ (by decide), ← cs RY (by decide)]; rfl
  have eP : MC.point base s.mem = .affine (toM W.p (2 ^ 576) (sv base s₄ RX)) (toM W.p (2 ^ 576) (sv base s₄ RY)) := by
    unfold Impl.Weierstrass.Mul.Curve.point
    rw [qx, qy, dq, dq]
  have hon' := hon
  rw [eP] at hon'
  -- To limbs.
  have hp522 : W.p < 2 ^ 522 := by decide
  have m522 : ∀ x, x % W.p < 2 ^ 522 := fun x => Nat.lt_trans (Nat.mod_lt _ hp0) hp522
  refine WP.seq (WP.mono (convIn_ok hw₄ hz' (by show sv base s₄ RX < _; exact Nat.lt_trans (qx ▸ hx) hp522)
    (by show sv base s₄ RY < _; exact Nat.lt_trans (qy ▸ hy) hp522)
    (by show sv base s₄ ONEP < _; rw [hone']; exact m522 _)
    (by show sv base s₄ AP < _; rw [ha']; exact m522 _) (by show sv base s₄ B3P < _; rw [hb3']; exact m522 _))
    fun q₅ ⟨K₅, U₅, cv₅⟩ => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at cv₅
  obtain ⟨⟨tx₅, vx₅⟩, ⟨ty₅, vy₅⟩, ⟨to₅, vo₅⟩, ⟨ta₅, va₅⟩, ⟨tb₅, vb₅⟩⟩ := cv₅
  have hw₅ := hw₄.of_kp K₅
  have z₅ : wordsVal q₅.mem base (WindowU.c.sl ZERO) 9 = 0 := by
    rw [U₅.wordsVal (by decide) (by decide)]; exact hz'
  have eQ : Window.qOf base q₅ = .affine (toM W.p (2 ^ 576) (sv base s₄ RX)) (toM W.p (2 ^ 576) (sv base s₄ RY)) := by
    show Point.affine (P521Unsat.uf _) (P521Unsat.uf _) = _
    rw [vx₅, vy₅]
    exact congrArg₂ Point.affine (ofNat_in_toM (show sv base s₄ RX < W.p from qx ▸ hx))
      (ofNat_in_toM (show sv base s₄ RY < W.p from qy ▸ hy))
  -- The body.
  have hpre : Window.WPre base q₅ := by
    refine ⟨hw₅, ⟨ta₅, ?_, tb₅, ?_, z₅, to₅, ?_⟩, tx₅, ty₅, by rw [eQ]; exact hon'⟩
    · show P521Unsat.uf _ = _; rw [va₅]; show Fin.ofNat _ (sv base s₄ AP * _) = _; rw [ha', ofNat_in]
    · show P521Unsat.uf _ = _; rw [vb₅]; show Fin.ofNat _ (sv base s₄ B3P * _) = _; rw [hb3', ofNat_in]
    · show P521Unsat.uf _ = _; rw [vo₅]; show Fin.ofNat _ (sv base s₄ ONEP * _) = _
      rw [hone', ← Nat.mul_one (2 ^ 576), ofNat_in]; rfl
  refine WP.seq (WP.mono (Window.body_ok hL hpre) fun q₆ ⟨K₆, U₆, pR₆⟩ => ?_)
  have hw₆ := hw₅.of_kc K₆
  have z₆ : wordsVal q₆.mem base (WindowU.c.sl ZERO) 9 = 0 := by
    rw [U₆.wordsVal (by decide) (by decide)]; exact z₅
  -- Back to Montgomery's form.
  refine WP.seq (WP.mono (convOut_ok hw₆ z₆ pR₆.x pR₆.y pR₆.z) fun q₇ ⟨K₇, U₇, cv₇⟩ => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at cv₇
  obtain ⟨ox₇, oy₇, oz₇⟩ := cv₇
  have R₆ := pR₆.rep
  have KK : Kc s₄ q₇ := (K₅.kc.trans K₆).trans K₇.kc
  have UU : Unch base ((cinW ++ Window.bodyW) ++ coutW) s₄.mem q₇.mem := (U₅.trans U₆).trans U₇
  -- The loads.
  have hw₇' := hw₄.of_kc KK
  have far : ∀ d ∈ [3304, 3312, 3320], word q₇.mem base d = word s₄.mem base d := fun d hd =>
    UU.word (fun w hw => by
      have := (by decide : ∀ w ∈ (cinW ++ Window.bodyW) ++ coutW, w.1 + w.2 ≤ 3304 ∨ 3376 ≤ w.1) w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      omega) (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; omega)
  have w20 : word q₇.mem base 3320 = s.gpr .ra := by
    rw [far 3320 (by simp), m₄, word_writeW_self]
  have w12 : word q₇.mem base 3312 = s.gpr .s1 := by
    rw [far 3312 (by simp), m₄, (writeW_outside (d := 3320) _ base _ (by omega)).word (by omega) (by omega), word_writeW_self]
  have w04 : word q₇.mem base 3304 = s.gpr .s0 := by
    rw [far 3304 (by simp), m₄, (writeW_outside (d := 3320) _ base _ (by omega)).word (by omega) (by omega),
      (writeW_outside (d := 3312) _ base _ (by omega)).word (by omega) (by omega), word_writeW_self]
  refine ldAt_ws hw₇' (d := 3320) (by decide) (by decide) fun s₆ u₆ => ?_
  refine ldAt_ws (hw₇'.of_kp (Kp.of_upd u₆)) (d := 3312) (by decide) (by decide) fun s₇ u₇ => ?_
  have hw₇ : WsReg s₇ base := ⟨by rw [u₇.other .s0 (by decide), u₆.other .s0 (by decide)]; exact hw₇'.s0,
    by rw [u₇.wr, u₆.wr]; exact hw₇'.wr, hfit, hal⟩
  refine ldAt_ws hw₇ (d := 3304) (by decide) (by decide) fun s₈ u₈ => WP.block_nil ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · have m₇ : s₇.mem = q₇.mem := by rw [u₇.mem, u₆.mem]
    by_cases h0 : r = .s0
    · subst h0; rw [u₈.gpr, m₇, w04]
    by_cases h1 : r = .s1
    · subst h1; rw [u₈.other _ (by decide), u₇.gpr, u₆.mem, w12]
    rw [u₈.other _ h0, u₇.other _ h1, u₆.other _ (fun e => by subst e; revert hr; decide),
      KK.gpr r hr h1, g₄ r h0]
  · rw [u₈.sp, u₇.sp, u₆.sp, KK.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, w20]
  · have m₈ : s₈.mem = q₇.mem := by rw [u₈.mem, u₇.mem, u₆.mem]
    show MC.ResultInRange _ _ (s.gpr .a0) s.mem s₈.mem
    rw [hb, eP, m₈]
    refine ⟨fun _ _ => ?_, keeps_of_unch (O₄.trans UU)⟩
    have e : MC.scalar base s.mem = sv base s₄ K := by rw [sv₄ _ (by decide)]; exact cs K (by decide)
    have k₅ : wordsVal q₅.mem base (WindowU.c.sl K) 9 = sv base s₄ K := U₅.wordsVal (by decide) (by decide)
    have c7 : ∀ i, i < 45 → MC.toPoint.coordAt q₇.mem base (p521.sl i) = sv base q₇ i := fun i hi =>
      ca q₇.mem (by simp only [Cfg.sl, slot, p521]; omega)
    have x0 : MC.toPoint.coordAt q₇.mem base MC.pAt = sv base q₇ RX := c7 RX (by decide)
    have x1 : MC.toPoint.coordAt q₇.mem base (MC.pAt + Impl.Weierstrass.Point.elemBytes MC.toPoint.k) =
        sv base q₇ RY := c7 RY (by decide)
    have x2 : MC.toPoint.coordAt q₇.mem base (MC.pAt + 2 * Impl.Weierstrass.Point.elemBytes MC.toPoint.k) =
        sv base q₇ RZ := c7 RZ (by decide)
    have ex : sv base q₇ RX = P521Unsat.uv (P521Unsat.wv base q₆ (WindowU.c.sl RX)) * 2 ^ 55 % W.p := ox₇
    have ey : sv base q₇ RY = P521Unsat.uv (P521Unsat.wv base q₆ (WindowU.c.sl RY)) * 2 ^ 55 % W.p := oy₇
    have ez : sv base q₇ RZ = P521Unsat.uv (P521Unsat.wv base q₆ (WindowU.c.sl RZ)) * 2 ^ 55 % W.p := oz₇
    rw [e]
    rw [eQ, k₅] at R₆
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · show _ < W.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x0, ex]; exact Nat.mod_lt _ hp0
    · show _ < W.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x1, ey]; exact Nat.mod_lt _ hp0
    · show _ < W.p; rw [Impl.Weierstrass.Point.Curve.pointAt, x2, ez]; exact Nat.mod_lt _ hp0
    · rw [Impl.Weierstrass.Point.Curve.pointAt, x0, x1, x2, dq, dq, dq, ex, ey, ez, toM_out, toM_out, toM_out]
      exact represents_of_rep R₆

/-! ## Constant time, and a state satisfying the precondition -/

theorem mul_ct : ConstantTime isa mulRVc.pre mulRVc.pub mulP521 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0])
    (fun _ _ _ _ hp => ⟨hp.1, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst hr; exact hp.2⟩) (by taint_decide)

/-- Byte `a` of the number `x` at slot `i` of a working space at `0x1000`,
if `a` is in that slot. -/
def satByte (a : Addr) (i x : Nat) : Option (BitVec 8) :=
  if 0x1000 + p521.sl i ≤ a.toNat ∧ a.toNat < 0x1000 + p521.sl i + 72 then
    some (BitVec.ofNat 8 (x >>> (8 * (a.toNat - (0x1000 + p521.sl i)))))
  else none

/-- `x R mod p`. -/
abbrev mont (x : Nat) : Nat := x * 2 ^ 576 % W.p

/-- The memory of `satState`: `p`, and one, `a`, `3 b` and `G`'s coordinates
in Montgomery's form, at their slots for `ws = 0x1000`, zeros elsewhere. -/
def satMem : Mem := fun a =>
  ((satByte a MP W.p).orElse fun _ => (satByte a ONEP (mont 1)).orElse fun _ =>
    (satByte a AP (mont W.a)).orElse fun _ => (satByte a B3P (mont (3 * W.b))).orElse fun _ =>
    (satByte a RX (mont W.gx)).orElse fun _ => satByte a RY (mont W.gy)).getD 0

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | _ => 0
  sp := 0x10000
  mem := satMem
  rd := []
  wr := [⟨0x1000, 8192⟩]

theorem sat_consts : MC.ConstsOk 0x1000 satMem := by
  unfold Impl.Weierstrass.Mul.Curve.ConstsOk
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem sat_x : (MC.qCoords 0x1000 satMem).1 = mont W.gx := by decide +kernel

theorem sat_y : (MC.qCoords 0x1000 satMem).2 = mont W.gy := by decide +kernel

theorem sat_point (hL : VG.Proof.Weierstrass.Law W) : MC.PointOk 0x1000 satMem := by
  have dq : ∀ x, MC.toPoint.dec x = toM W.p (2 ^ 576) x :=
    VG.Proof.Weierstrass.Point.dec_eq MC.toPoint hL.one_ne_zero (VG.Proof.Weierstrass.Point.fermat_of_law hL) unit
  have hp0 : 0 < W.p := by decide
  refine ⟨by rw [sat_x]; exact Nat.mod_lt _ hp0, by rw [sat_y]; exact Nat.mod_lt _ hp0, ?_⟩
  have eG : MC.point 0x1000 satMem = Spec.Weierstrass.G W := by
    unfold Impl.Weierstrass.Mul.Curve.point
    rw [sat_x, sat_y, dq, dq]
    exact congrArg₂ Point.affine (toM_mont unit) (toM_mont unit)
  rw [eG]
  exact VG.Proof.P521.onCurve_G

theorem mul_verified (hL : VG.Proof.Weierstrass.Law W) :
    Verified RISCV64.target mulP521 (MC.mulInRangeContract RISCV64.abi) :=
  Verified.of_correct (mul_rv hL) mul_ct
    { pre := by sig_implies_pre [Impl.Weierstrass.Mul.Curve.mulInRangeContract, Impl.Weierstrass.MulBase.sig,
        mulRVc, RISCV64.abi, RISCV64.argRegs]
      post := by sig_implies_post [Impl.Weierstrass.Mul.Curve.mulInRangeContract, Impl.Weierstrass.MulBase.sig,
        mulRVc, RISCV64.abi, RISCV64.argRegs]
      pub := by sig_implies_pub [Impl.Weierstrass.Mul.Curve.mulInRangeContract, Impl.Weierstrass.MulBase.sig,
        mulRVc, RISCV64.abi, RISCV64.argRegs]
      sat := ⟨satState, Sig.contract_pre_of_check (by decide +kernel) (by
        sig_reduce [Sig.wfPre, Impl.Weierstrass.MulBase.sig, RISCV64.abi, RISCV64.argRegs, satState]
        exact ⟨by decide, sat_consts, sat_point hL⟩)⟩ }

end VG.Proof.Ecdsa.RISCV64.P521

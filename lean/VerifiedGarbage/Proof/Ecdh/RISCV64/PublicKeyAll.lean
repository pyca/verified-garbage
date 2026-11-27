module

public import VerifiedGarbage.Proof.Ecdh.RISCV64.ExchangeAll
public import VerifiedGarbage.Spec.EcKey
import VerifiedGarbage.Proof.Ecdh.RISCV64.Bytes
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
import VerifiedGarbage.Proof.Weierstrass.Words

/-!
# Public keys on RISC-V: correctness, for every curve

`vg_ec_<curve>_public_key` meets its contract by register, given the group
law (`PkKit.pk_ok`), once for every curve. What the proof needs of a curve
is its `Kit` (`ExchangeAll.lean`) and, in a `PkKit`, what the public key
adds: `[d]G` after the point's setup (`tailG_ok`: by the comb, whose table
the state holds, `GT`, or by the ladder, `tailG_of_tail`).

The proof is the saves, `d` and the constants, `G` to `R`'s first two slots
and the flag set, the kit's `tailG_ok`, `y` out of Montgomery's form
(`TKit.affine_ok`), and the point (`04`, `x` and
`y`) under the flag (`Kit.pointOut_ok`, `Kit.finPk_ok`); the specification's
public key is `publicKey_eq`'s (`Proof/EcKey/PublicKey.lean`). Each
`<Curve>/PublicKey.lean` is the curve's `PkKit`, and the statements about it
that other modules use.
-/

@[expose] public section

namespace VG.Proof.Ecdh.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Proof.X25519.RISCV64 (Rest wp_and)
open VG.Spec.Weierstrass (Curve Fe Point ofBytes toBytes)
open VG.Spec.Ecdsa (bytesAt)
open VG.WriteBytes (writeBytes writeBytes_snoc writeBytes_nil writeBytes_append)

/-- Slot arithmetic: the offsets of slots given by number, with the kit's bound on the words. -/
local macro "kit_slots" E:term : tactic => `(tactic| (
  simp only [Cfg.sl, slot, MP, MN, ZERO, ONE, ONEP, AP, B3P, GX, GY, EXPP, R2P, BP, K, FLAG, RX, RY, RZ, XO, YO, YM]
  omega_using [TKit.n9 (Kit.toTKit $E)]))

/-- `∀ w ∈ W, P w` for ranges `W` given as a list of lists: `t` proves it of each. -/
local macro "kit_ranges" t:tacticSeq : tactic =>
  `(tactic| ((repeat' first | with_reducible apply Kit.all_app | with_reducible apply Kit.all_one); all_goals ($t)))

/-- A slot apart from ranges that are other slots, the flag or the constants. -/
local macro "kit_apart" : tactic =>
  `(tactic| kit_ranges (first
    | exact Kit.sl_sep _ (by decide)
    | exact Or.inl (Kit.sl_le _ (by decide))
    | exact Kit.apart_consts _ (by decide)))

namespace Kit

variable (E : Kit)

/-! ## What does not depend on the curve -/

theorem byte_eq (b : Bool) : (BitVec.ofNat 64 4 &&& maskOf b).setWidth 8 = if b then 4 else 0 := by
  cases b <;> decide

theorem publicKey_none {C : Curve} {d : Nat} (h : ¬ (1 ≤ d ∧ d < C.n)) : Spec.EcKey.publicKey C d = none := by
  unfold Spec.EcKey.publicKey; simp only [h, ↓reduceIte]

/-- The zeros of a point that is not written. -/
theorem zeros_eq (L : Nat) : (0 : Byte) :: (toBytes L 0 ++ toBytes L 0) = List.replicate (1 + 2 * L) 0 := by
  rw [toBytes_zero, List.replicate_append_replicate, show 1 + 2 * L = L + L + 1 by omega_using [],
    List.replicate_succ]

/-! ## The point to `out` -/

/-- `04 ‖ x ‖ y` (or zeros, by the mask `a7`) to `out` (in `s2`), from the
slots `xo` and `yo`, the flag's low bit returned and the registers restored:
`Cfg.pointOut`, as the kit writes its numbers. -/
def pointOutC (xo yo : Nat) : List Instr :=
  [.li .t0 4, .logic .and .t0 .t0 .a7, .store .b .t0 .s2 0] ++ E.store (E.c.sl xo) .s2 1 ++
    E.store (E.c.sl yo) .s2 (1 + E.L) ++ retCode E.c

/-- `pointOut`: `04 ‖ x ‖ y` from the slots `xo` and `yo` (or zeros, by the
mask `a7`, which the flag holds) to `out`, the flag's low bit to `a0`, and
the saved registers restored. -/
theorem pointOut_ok {s : State} {base out : Addr} (hw : WsReg s base) (h2 : s.gpr .s2 = out)
    (hfit : out.toNat + (1 + 2 * E.L) ≤ 2 ^ 64)
    (hout : ∀ i < 1 + 2 * E.L, InRegions s.wr (out + BitVec.ofNat 64 i) 1)
    (hdis : (⟨out, 1 + 2 * E.L⟩ : Region).Disjoint ⟨base, 8192⟩)
    {B : Bool} (ha7 : s.gpr .a7 = maskOf B) (hfl : word s.mem base (E.c.sl FLAG) = maskOf B)
    {xo yo : Nat} (hxo : xo < 45) (hyo : yo < 45) :
    WP isa (.block (E.pointOutC xo yo)) s fun s' =>
      s'.gpr .a0 = (if B then 1 else 0) ∧
      bytesAt s'.mem out (1 + 2 * E.L) = (if B then 4 else 0) ::
        (toBytes E.L (if B then sv E.c base s xo else 0) ++ toBytes E.L (if B then sv E.c base s yo else 0)) ∧
      s'.gpr .s0 = word s.mem base 0 ∧ s'.gpr .s1 = word s.mem base 8 ∧ s'.gpr .s2 = word s.mem base 16 ∧
      s'.gpr .ra = word s.mem base 24 ∧ s'.gpr .s3 = word s.mem base 32 ∧
      (∀ r ∈ preserved, r ≠ .s0 → r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp := by
  obtain hL := E.Ln
  obtain h9 := E.n9
  obtain fit : ∀ {i}, i < 45 → E.c.sl i + 8 * E.c.n ≤ 4096 := fun hi => sl_top h9 (by omega_using [hi])
  obtain ap : ∀ {i}, i < 45 → ∀ w ∈ [((8192 : Nat), (2 ^ 64 : Nat))],
      E.c.sl i + 8 * E.c.n ≤ w.1 ∨ w.1 + w.2 ≤ E.c.sl i :=
    fun hi => all_one (.inl (Nat.le_trans (fit hi) (by decide)))
  -- `04` under the mask.
  rw [pointOutC, retCode, restoreCode]
  simp only [List.append_assoc]
  rw [List.cons_append, List.cons_append, List.cons_append, List.nil_append]
  refine wp_li (imm := 4) (by decide) fun s₄ u₄ => wp_and fun s₅ u₅ => ?_
  refine wp_sb (off := 0) (a := out) (by decide) (by rw [u₅.other _ (by decide), u₄.other _ (by decide), h2,
    BitVec.add_zero]) (by rw [u₅.wr, u₄.wr]; simpa using hout 0 (by omega_using [])) fun s₆ u₆ => ?_
  obtain hw₆ := ((hw.of_kp (Kp.of_upd u₄)).of_kp (Kp.of_upd u₅)).of_kp (Kp.of_mupd u₆)
  obtain v₆ : (s₅.gpr .t0).setWidth 8 = if B then 4 else 0 := by
    rw [u₅.gpr, u₄.gpr, u₄.other _ (by decide), ha7, byte_eq]
  obtain m₆ : s₆.mem = writeBytes s.mem out [if B then 4 else 0] := by
    rw [u₆.mem, v₆, u₅.mem, u₄.mem]
    have := writeBytes_snoc s.mem out [] (if B then 4 else 0) (by decide)
    rw [List.nil_append, writeBytes_nil] at this
    rw [this]; simp
  obtain q₆ : s₆.gpr .s2 = out := by rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), h2]
  obtain wr₆ : s₆.wr = s.wr := by rw [u₆.wr, u₅.wr, u₄.wr]
  obtain a₆ : s₆.gpr .a7 = maskOf B := by rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), ha7]
  obtain sp' : ∀ {off k : Nat}, off + k ≤ 1 + 2 * E.L → ∀ i < k,
      ¬ (⟨base, 8192⟩ : Region).Contains (out + BitVec.ofNat 64 off + BitVec.ofNat 64 i) 1 :=
    fun hk => sep_at' hdis hfit hk
  obtain U₆ : Unch base [(8192, 2 ^ 64)] s.mem s₆.mem := by
    rw [m₆]; exact writeBytes_unch _ fun i hi => by
      have := sp' (off := 0) (k := 1) (by omega_using []) i (by simpa using hi); simpa using this
  -- `x` and `y` under the mask.
  refine WP.block_append (WP.mono (E.store_ok _ (i := xo) (q := .s2) (off := 1) hw₆ a₆ hxo (by decide)
    (by omega_using [hL, h9])
    (fun i hi => by rw [q₆, wr₆]; exact hout (1 + i) (by omega_using [hi]))
    (fun i hi => by rw [q₆]; exact out_of_disj hdis hfit (by omega_using [hi]))) fun s₇ ⟨r₇, m₇⟩ => ?_)
  obtain hw₇ := hw₆.of_rest r₇
  obtain q₇ : s₇.gpr .s2 = out := by rw [r₇.gpr _ (by decide), q₆]
  obtain a₇ : s₇.gpr .a7 = maskOf B := by rw [r₇.gpr _ (by decide), a₆]
  obtain xo₆ : wordsVal s₆.mem base (E.c.sl xo) E.c.n = sv E.c base s xo :=
    U₆.wordsVal (ap hxo) (Nat.le_trans (fit hxo) (by decide))
  rw [q₆, xo₆] at m₇
  obtain U₇ : Unch base [(8192, 2 ^ 64)] s₆.mem s₇.mem := by
    rw [m₇]; exact writeBytes_unch _ fun i hi => sp' (off := 1) (k := E.L) (by omega_using []) i
      (by simpa [VG.Proof.Weierstrass.length_toBytes] using hi)
  refine WP.block_append (WP.mono (E.store_ok _ (i := yo) (q := .s2) (off := 1 + E.L) hw₇ a₇ hyo (by decide)
    (by omega_using [hL, h9])
    (fun i hi => by rw [q₇, r₇.wr, wr₆]; exact hout (1 + E.L + i) (by omega_using [hi]))
    (fun i hi => by rw [q₇]; exact out_of_disj hdis hfit (by omega_using [hi]))) fun s₈ ⟨r₈, m₈⟩ => ?_)
  obtain hw₈ := hw₇.of_rest r₈
  obtain yo₇ : wordsVal s₇.mem base (E.c.sl yo) E.c.n = sv E.c base s yo := by
    rw [U₇.wordsVal (ap hyo) (Nat.le_trans (fit hyo) (by decide))]
    exact U₆.wordsVal (ap hyo) (Nat.le_trans (fit hyo) (by decide))
  rw [q₇, yo₇] at m₈
  obtain U₈ : Unch base [(8192, 2 ^ 64)] s₇.mem s₈.mem := by
    rw [m₈]; exact writeBytes_unch _ fun i hi => sp' (off := 1 + E.L) (k := E.L) (by omega_using []) i
      (by simpa [VG.Proof.Weierstrass.length_toBytes] using hi)
  obtain U₃₈ := (U₆.trans U₇).trans U₈
  obtain wd : ∀ d, d + 8 ≤ 4096 → word s₈.mem base d = word s.mem base d := fun d hd =>
    U₃₈.word (by simp; omega_using [hd]) (by omega_using [hd])
  obtain fl₈ : word s₈.mem base (E.c.sl FLAG) = maskOf B := by rw [wd _ (by kit_slots E), hfl]
  -- The bytes.
  obtain hX := VG.Proof.Weierstrass.length_toBytes E.L (if B = true then sv E.c base s xo else 0)
  obtain hY := VG.Proof.Weierstrass.length_toBytes E.L (if B = true then sv E.c base s yo else 0)
  obtain bytes₈ : bytesAt s₈.mem out (1 + 2 * E.L) = (if B then 4 else 0) ::
      (toBytes E.L (if B then sv E.c base s xo else 0) ++ toBytes E.L (if B then sv E.c base s yo else 0)) := by
    obtain e1 := writeBytes_append s.mem out [if B then 4 else 0] (toBytes E.L (if B then sv E.c base s xo else 0))
      (by rw [hX, List.length_singleton]; omega_using [hL, h9])
    obtain e2 := writeBytes_append s.mem out ([if B then 4 else 0] ++ toBytes E.L (if B then sv E.c base s xo else 0))
      (toBytes E.L (if B then sv E.c base s yo else 0))
      (by simp only [List.length_append, List.length_singleton, hX, hY]; omega_using [hL, h9])
    simp only [List.length_singleton] at e1
    simp only [List.length_append, List.length_singleton, hX] at e2
    rw [m₈, m₇, m₆]
    rw [e1, e2]
    have := bytesAt_writeBytes s.mem out
      ([if B then 4 else 0] ++ toBytes E.L (if B then sv E.c base s xo else 0) ++
        toBytes E.L (if B then sv E.c base s yo else 0))
      (by simp only [List.length_append, List.length_singleton, hX, hY]; omega_using [hL, h9])
    simp only [List.length_append, List.length_singleton, hX, hY] at this
    rw [show 1 + 2 * E.L = 1 + E.L + E.L by omega_using [], this]; rfl
  -- The return value and the restores.
  refine ldAt_ws hw₈ (d := E.c.sl FLAG) (by kit_slots E) (sl8 _ _) fun s₉ u₉ => ?_
  refine WP.cons (exec_logicImm (by decide)) ?_
  obtain u₉' := Upd.write s₉ .a0 (s₉.gpr .a0 &&& BitVec.ofInt 64 1)
  obtain hw₉ := (hw₈.of_kp (Kp.of_upd u₉)).of_kp (Kp.of_upd u₉')
  refine ld_ws hw₉ (d := 24) (by decide) (by decide) fun t₁ v₁ => ?_
  obtain hv₁ := hw₉.of_kp (Kp.of_upd v₁)
  refine ld_ws hv₁ (d := 16) (by decide) (by decide) fun t₂ v₂ => ?_
  obtain hv₂ : WsReg t₂ base := ⟨by rw [v₂.other _ (by decide)]; exact hv₁.s0, by rw [v₂.wr]; exact hv₁.wr,
    hv₁.nowrap, hv₁.al⟩
  refine ld_ws hv₂ (d := 8) (by decide) (by decide) fun t₃ v₃ => ?_
  obtain hv₃ : WsReg t₃ base := ⟨by rw [v₃.other _ (by decide)]; exact hv₂.s0, by rw [v₃.wr]; exact hv₂.wr,
    hv₂.nowrap, hv₂.al⟩
  refine ld_ws hv₃ (d := 32) (by decide) (by decide) fun t₄ v₄ => ?_
  obtain hv₄ : WsReg t₄ base := ⟨by rw [v₄.other _ (by decide)]; exact hv₃.s0, by rw [v₄.wr]; exact hv₃.wr,
    hv₃.nowrap, hv₃.al⟩
  refine ld_ws hv₄ (d := 0) (by decide) (by decide) fun t₅ v₅ => WP.block_nil ?_
  obtain M₄ : t₄.mem = s₈.mem := by rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem, u₉'.mem, u₉.mem]
  obtain np : ∀ r ∈ preserved, r ∉ [Reg.t0, .t1, .t3, .t4, .a7, .a0, .ra] := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide),
      v₁.other _ (by decide), u₉'.gpr, u₉.gpr, fl₈, and_one]
  · rw [v₅.mem, M₄]; exact bytes₈
  · rw [v₅.gpr, M₄, wd 0 (by decide)]
  · rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr, v₂.mem, v₁.mem, u₉'.mem, u₉.mem,
      wd 8 (by decide)]
  · rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.mem, u₉'.mem, u₉.mem,
      wd 16 (by decide)]
  · rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.gpr,
      u₉'.mem, u₉.mem, wd 24 (by decide)]
  · rw [v₅.other _ (by decide), v₄.gpr, v₃.mem, v₂.mem, v₁.mem, u₉'.mem, u₉.mem, wd 32 (by decide)]
  · intro r hr h0 h1 h2' h3'
    obtain hn := np r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    rw [v₅.other _ h0, v₄.other _ h3', v₃.other _ h1, v₂.other _ h2', v₁.other _ hn.2.2.2.2.2.2,
      u₉'.other _ hn.2.2.2.2.2.1, u₉.other _ hn.2.2.2.2.2.1, r₈.gpr _ (by simp [hn.1, hn.2.1]),
      r₇.gpr _ (by simp [hn.1, hn.2.1]), u₆.gpr, u₅.other _ hn.1, u₄.other _ hn.1]
  · rw [v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, u₉'.sp, u₉.sp, r₈.sp, r₇.sp, u₆.sp, u₅.sp, u₄.sp]

/-- The end: the flag `&=` the mask of `Z ≠ 0`, the point (or zeros) to
`out`, the flag's low bit to `a0`, and the saved registers restored. -/
theorem finPk_ok {s : State} {base out : Addr} (hw : WsReg s base) (h2 : s.gpr .s2 = out)
    (hfit : out.toNat + (1 + 2 * E.L) ≤ 2 ^ 64)
    (hout : ∀ i < 1 + 2 * E.L, InRegions s.wr (out + BitVec.ofNat 64 i) 1)
    (hdis : (⟨out, 1 + 2 * E.L⟩ : Region).Disjoint ⟨base, 8192⟩)
    {b : Bool} (hF : word s.mem base (E.c.sl FLAG) = maskOf b) :
    WP isa (.block (zCode E.c ++ E.pointOutC XO YO)) s fun s' =>
      s'.gpr .a0 = (if b && !decide (sv E.c base s RZ = 0) then 1 else 0) ∧
      bytesAt s'.mem out (1 + 2 * E.L) = (if b && !decide (sv E.c base s RZ = 0) then 4 else 0) ::
        (toBytes E.L (if b && !decide (sv E.c base s RZ = 0) then sv E.c base s XO else 0) ++
          toBytes E.L (if b && !decide (sv E.c base s RZ = 0) then sv E.c base s YO else 0)) ∧
      s'.gpr .s0 = word s.mem base 0 ∧ s'.gpr .s1 = word s.mem base 8 ∧ s'.gpr .s2 = word s.mem base 16 ∧
      s'.gpr .ra = word s.mem base 24 ∧ s'.gpr .s3 = word s.mem base 32 ∧
      (∀ r ∈ preserved, r ≠ .s0 → r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp := by
  obtain h9 := E.n9
  obtain hfl := sl_lo E.c FLAG
  rw [zCode]
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (zeroMask_ok hw (n := E.c.n) (a := E.c.sl RZ) (sl8 _ _) (sl_top h9 (by decide)))
    fun s₁ ⟨r₁, m₁, g₁⟩ => ?_)
  rw [List.singleton_append]
  refine WP.cons (exec_logicImm (by decide)) ?_
  obtain r₁' := r₁.trans ((Upd.write s₁ .a7 (s₁.gpr .a7 ^^^ BitVec.ofInt 64 (-1))).rest (ws := [.t3, .t4, .a7])
    (by decide))
  obtain hw₁ := hw.of_rest r₁'
  refine WP.block_append (WP.mono (E.andFlag_ok hw₁) fun s₂ ⟨f₂, r₂, O₂⟩ => ?_)
  obtain hw₂ := hw₁.of_rest r₂
  refine ldAt_ws hw₂ (d := E.c.sl FLAG) (by kit_slots E) (sl8 _ _) fun s₃ u₃ => ?_
  obtain hw₃ := hw₂.of_kp (Kp.of_upd u₃)
  generalize hB : (b && !decide (sv E.c base s RZ = 0)) = B
  obtain hb : word s₂.mem base (E.c.sl FLAG) = maskOf B := by
    rw [f₂, ← hB]
    simp only [State.write, ↓reduceIte]
    rw [m₁, hF, g₁, not_mask, maskOf_and]
  obtain a₃ : s₃.gpr .a7 = maskOf B := by rw [u₃.gpr]; exact hb
  obtain wv₃ : ∀ i, i < 44 → wordsVal s₃.mem base (E.c.sl i) E.c.n = sv E.c base s i := fun i hi => by
    rw [u₃.mem, O₂.wordsVal (.inl (sl_le _ hi)) (Nat.le_trans (sl_top h9 (by omega_using [hi])) (by decide))]
    show wordsVal (s₁.write _ _).mem _ _ _ = _
    simp only [State.write]; rw [m₁]
  obtain q₃ : s₃.gpr .s2 = out := by
    rw [u₃.other _ (by decide), r₂.gpr _ (by decide), r₁'.gpr _ (by decide), h2]
  obtain wr₃ : s₃.wr = s.wr := by rw [u₃.wr, r₂.wr, r₁'.wr]
  refine WP.mono (E.pointOut_ok hw₃ q₃ hfit (by rw [wr₃]; exact hout) hdis a₃ (by rw [u₃.mem]; exact hb)
    (xo := XO) (yo := YO) (by decide) (by decide))
    fun s' ⟨a0', b', s0', s1', s2', ra', s3', regs', sp'⟩ => ?_
  obtain w₃ : ∀ d, d + 8 ≤ 40 → word s₃.mem base d = word s.mem base d := fun d hd => by
    rw [u₃.mem, O₂.word (.inl (by omega_using [hd, hfl])) (by omega_using [hd])]
    show word (s₁.write _ _).mem _ _ = _
    simp only [State.write]; rw [m₁]
  obtain ex : sv E.c base s₃ XO = sv E.c base s XO := wv₃ XO (by decide)
  obtain ey : sv E.c base s₃ YO = sv E.c base s YO := wv₃ YO (by decide)
  refine ⟨a0', by rw [b', ex, ey],
    by rw [s0', w₃ 0 (by decide)], by rw [s1', w₃ 8 (by decide)],
    by rw [s2', w₃ 16 (by decide)], by rw [ra', w₃ 24 (by decide)],
    by rw [s3', w₃ 32 (by decide)], fun r hr h0 h1 h2' h3' => ?_,
    by rw [sp', u₃.sp, r₂.sp, r₁'.sp]⟩
  obtain hn : r ∉ [Reg.t0, .t1, .t3, .t4, .a7] := by
    intro h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> exact absurd hr (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  rw [regs' r hr h0 h1 h2' h3', u₃.other _ hn.2.2.2.2, r₂.gpr _ (by simp [hn.1]),
    r₁'.gpr _ (by simp [hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2])]

/-! ## The contract, and what `tail` leaves -/

/-- The public key of the private key at `d`, as the specification computes it. -/
abbrev pk (m : Mem) (d : Addr) : Option (Point E.c.C) :=
  Spec.EcKey.publicKey E.c.C (ofBytes (bytesAt m d E.L))

/-- What `vg_ec_<curve>_public_key` returns. -/
def pkPost (s s' : State) : Prop :=
  match E.pk s.mem (s.gpr .a1) with
  | some (.affine x y) =>
    s'.gpr .a0 = 1 ∧ bytesAt s'.mem (s.gpr .a0) (1 + 2 * E.L) = Spec.EcKey.encodePoint (.affine x y)
  | _ => s'.gpr .a0 = 0 ∧ bytesAt s'.mem (s.gpr .a0) (1 + 2 * E.L) = List.replicate (1 + 2 * E.L) 0

/-- What `tail` leaves: the kit's `tail_ok`'s. -/
abbrev TailPost (base : Addr) (s s' : State) : Prop := TKit.TailPost E.c base s s'

/-- What `y` out of Montgomery's form writes: its slots and the field's own
working space. -/
abbrev affW : List (Nat × Nat) :=
  [(E.c.sl YM, 8 * E.c.n), (own E.c.n, 64 * E.c.n), (E.c.sl YO, 8 * E.c.n), (own E.c.n, 64 * E.c.n)]

/-- `tail` from `G` in `R`'s first two slots, by the kit's `tail_ok` (the
ladder): a `PkKit`'s `tailG_ok` for the curves without a comb. -/
theorem tailG_of_tail (hL : Law E.c.C) {s : State} {base : Addr} (hw : WsReg s base) (h3 : s.gpr .s3 = base)
    (a1 : sv E.c base s MP = E.c.C.p) (a2 : sv E.c base s MN = E.c.C.n) (a3 : sv E.c base s ZERO = 0)
    (a4 : sv E.c base s ONE = 1) (a5 : sv E.c base s ONEP = 1 * 2 ^ (64 * E.c.n) % E.c.C.p)
    (a6 : sv E.c base s AP = E.c.C.a * 2 ^ (64 * E.c.n) % E.c.C.p)
    (a7 : sv E.c base s B3P = 3 * E.c.C.b * 2 ^ (64 * E.c.n) % E.c.C.p) (a8 : sv E.c base s EXPP = E.c.C.p - 2)
    (hx : sv E.c base s RX = E.c.C.gx * 2 ^ (64 * E.c.n) % E.c.C.p)
    (hy : sv E.c base s RY = E.c.C.gy * 2 ^ (64 * E.c.n) % E.c.C.p) :
    WP isa (tail E.c E.mulN E.mulC) s fun s' => E.TailPost base s s' := by
  obtain hp0 : 0 < E.c.C.p := Nat.pos_of_ne_zero (NeZero.ne _)
  refine E.tail_ok hL hw h3 a1 a2 a3 a4 a5 a6 a7 a8 (by rw [hx]; exact Nat.mod_lt _ hp0)
    (by rw [hy]; exact Nat.mod_lt _ hp0) ?_
  rw [hx, hy, toM_mont E.unit, toM_mont E.unit]
  exact E.onG

end Kit

/-! ## The kit of the public key -/

/-- What the public key's proof needs of a curve, with its `Kit`. -/
structure PkKit where
  E : Kit
  /-- `[d]G`: its name and its code. -/
  gmulN : String
  gmulC : Prog isa
  /-- The table `[d]G` reads, if any: what the precondition says of it, and
  what its callers hold, for the working space at `base`. -/
  GT0 : State → Prop
  GT : Addr → State → Prop
  gt_start : ∀ {s : State} {base : Addr}, GT0 s → (⟨base, 8192⟩ : Region) ∈ s.wr → GT base s
  gt_frame : ∀ {s s' : State} {base : Addr}, GT0 s → GT base s → s'.syms = s.syms → s'.rd = s.rd →
    Frame s.wr s.mem s'.mem → GT base s'
  /-- `tail` from `G` in `R`'s first two slots. -/
  tailG_ok : Law E.c.C → ∀ {s : State} {base : Addr}, WsReg s base → s.gpr .s3 = base →
    Kit.sv E.c base s MP = E.c.C.p → Kit.sv E.c base s MN = E.c.C.n → Kit.sv E.c base s ZERO = 0 →
    Kit.sv E.c base s ONE = 1 → Kit.sv E.c base s ONEP = 1 * 2 ^ (64 * E.c.n) % E.c.C.p →
    Kit.sv E.c base s AP = E.c.C.a * 2 ^ (64 * E.c.n) % E.c.C.p →
    Kit.sv E.c base s B3P = 3 * E.c.C.b * 2 ^ (64 * E.c.n) % E.c.C.p → Kit.sv E.c base s EXPP = E.c.C.p - 2 →
    Kit.sv E.c base s RX = E.c.C.gx * 2 ^ (64 * E.c.n) % E.c.C.p →
    Kit.sv E.c base s RY = E.c.C.gy * 2 ^ (64 * E.c.n) % E.c.C.p →
    Kit.sv E.c base s BP = E.c.C.b * 2 ^ (64 * E.c.n) % E.c.C.p → GT base s →
    WP isa (tail E.c gmulN gmulC) s fun s' => E.TailPost base s s'

namespace PkKit

open Kit

variable (P : PkKit)

/-- `tail` keeps one. -/
theorem tail_one : ∀ w ∈ P.E.tailW, P.E.c.sl ONE + 8 * P.E.c.n ≤ w.1 ∨ w.1 + w.2 ≤ P.E.c.sl ONE :=
  TKit.tailW_one P.E.c P.E.n9

/-- `y = Y Z^(p-2)` out of Montgomery's form, `Z^(p-2) R` in `ACC`. -/
theorem affine_ok {s : State} {base : Addr} (hw : WsReg s base) (hacc : sv P.E.c base s ACC < P.E.c.C.p)
    (hone : sv P.E.c base s ONE = 1) :
    WP isa (affineCoord P.E.c YM YO RY) s fun s' =>
      Kp s s' ∧ Unch base P.E.affW s.mem s'.mem ∧
      sv P.E.c base s' YO < P.E.c.C.p ∧
      Fin.ofNat P.E.c.C.p (sv P.E.c base s' YO) =
        toM P.E.c.C.p (2 ^ (64 * P.E.c.n)) (sv P.E.c base s RY) * toM P.E.c.C.p (2 ^ (64 * P.E.c.n)) (sv P.E.c base s ACC) :=
  P.E.toTKit.affine_ok hw (t := YM) (o := YO) (a := RY) (by decide) (by decide) (by decide) (by decide) hacc hone

/-- What the contract gives, by register, and of the table. -/
structure Pre (P : PkKit) (s : State) : Prop where
  rd : (⟨s.gpr .a1, P.E.L⟩ : Region) ∈ s.rd
  wr : s.wr = [⟨s.gpr .a0, 1 + 2 * P.E.L⟩, ⟨s.gpr .a2, 8192⟩]
  out : (⟨s.gpr .a0, 1 + 2 * P.E.L⟩ : Region).Disjoint ⟨s.gpr .a2, 8192⟩
  d : (⟨s.gpr .a1, P.E.L⟩ : Region).Disjoint ⟨s.gpr .a2, 8192⟩
  fo : (s.gpr .a0).toNat + (1 + 2 * P.E.L) ≤ 2 ^ 64
  fd : (s.gpr .a1).toNat + P.E.L ≤ 2 ^ 64
  fs : (s.gpr .a2).toNat + 8192 ≤ 2 ^ 64
  al : (s.gpr .a2).toNat % 8 = 0
  tab : P.GT0 s

/-- `vg_ec_<curve>_public_key`, as the kit reads and writes its numbers. -/
def prog : Prog isa :=
  .seq (.block (saveCode .a2 ++ P.E.load (P.E.c.sl K) .a1 0 ++
    ([.li .t0 0, .addi .t0 .t0 (-1)] : List Instr) ++ sdAt .t0 wb (P.E.c.sl FLAG) ++ constCode P.E.c ++
    copy P.E.c.n (P.E.c.sl RX) (P.E.c.sl GX) ++ copy P.E.c.n (P.E.c.sl RY) (P.E.c.sl GY))) <|
  .seq (tail P.E.c P.gmulN P.gmulC) <|
  .seq (affineCoord P.E.c YM YO RY) <|
  .block (zCode P.E.c ++ P.E.pointOutC XO YO)

/-- `vg_ec_<curve>_public_key` by register. -/
theorem pk_ok (hL : Law P.E.c.C) {s : State} (hs : P.Pre s) :
    WP isa P.prog s fun s' => abiPreserved s s' ∧ P.E.pkPost s s' := by
  obtain ⟨hrd, hwr, hod, hdd, hfo, hfd, hfs, hal, hk⟩ := hs
  obtain hLn := P.E.Ln
  obtain h9 := P.E.n9
  obtain hown := own_ge h9
  obtain fit : ∀ {i}, i ≤ 55 → P.E.c.sl i + 8 * P.E.c.n ≤ 2 ^ 64 := fun hi => Nat.le_trans (sl_top h9 hi) (by decide)
  rw [prog]
  simp only [List.append_assoc]
  generalize hb : s.gpr .a2 = base at hwr hod hdd hfs hal
  obtain hwr' : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hwr]; simp
  obtain hT₀ := P.gt_start hk hwr'
  refine WP.seq (wp_syms_frame (WP.block_append (WP.mono (TKit.save_ok hb hwr' hfs hal)
    fun s₁ ⟨hw₁, h3₁, o₁, g₁, rd₁, wr₁, sp₁, U₁, w0, w1, w2, w3, w4⟩ => ?_)))
  obtain a1 : s₁.gpr .a1 = s.gpr .a1 := g₁ _ (by decide) (by decide) (by decide)
  obtain rd1 : (⟨s.gpr .a1, P.E.L⟩ : Region) ∈ s₁.rd ++ s₁.wr := by
    rw [rd₁]; exact List.mem_append_left _ hrd
  -- `d`.
  refine WP.block_append (WP.mono (P.E.load_ok (i := K) (p := .a1) (off := 0) (R := P.E.L) hw₁ (by decide)
    (by decide) (by omega_using []) (by omega_using [hLn, h9]) (by rw [a1]; exact rd1)
    (fun i hi => by rw [a1]; exact out_of_disj hdd hfd (by omega_using [hi])))
    fun s₂ ⟨r₂, O₂, e₂⟩ => ?_)
  obtain hw₂ := hw₁.of_rest r₂
  -- The flag.
  rw [List.cons_append, List.cons_append, List.nil_append]
  refine wp_li (imm := 0) (by decide) fun s₂a u₂a => ?_
  refine WP.cons (exec_addi (by decide)) ?_
  obtain u₂b := Upd.write s₂a .t0 (s₂a.gpr .t0 + BitVec.ofInt 64 (-1))
  obtain hw₂b := (hw₂.of_kp (Kp.of_upd u₂a)).of_kp (Kp.of_upd u₂b)
  refine sdAt_ws hw₂b (by decide) (d := P.E.c.sl FLAG) (by kit_slots P.E) (sl8 _ _) fun s₃ u₃ => ?_
  obtain hw₃ := hw₂b.of_kp (Kp.of_mupd u₃)
  obtain fl₃ : word s₃.mem base (P.E.c.sl FLAG) = maskOf true := by
    rw [u₃.mem, word_writeW_self, u₂b.gpr, u₂a.gpr]; decide
  -- The constants, and `G` to `R`.
  rw [constCode_eq]
  refine WP.block_append (WP.mono (TKit.consts_ok P.E.c P.E.n9 _ hw₃ (TKit.consts_le P.E.c) (consts_nodup _))
    fun s₄ ⟨r₄, U₄, e₄⟩ => ?_)
  obtain hw₄ := hw₃.of_rest r₄
  obtain cs₄ : ∀ e ∈ consts P.E.c, sv P.E.c base s₄ e.1 = e.2 := fun e he => by
    rw [e₄ e he, Nat.mod_eq_of_lt (P.E.consts_lt e he)]
  refine WP.block_append (WP.mono (copy_ok P.E.c.n hw₄ (o := P.E.c.sl RX) (a := P.E.c.sl GX) (sl8 _ _)
    (sl8 _ _) (sl_top h9 (by decide)) (sl_top h9 (by decide)) (.inr (sl_le _ (by decide))))
    fun s₅ ⟨v₅, r₅, O₅⟩ => ?_)
  obtain hw₅ := hw₄.of_rest r₅
  refine WP.mono (copy_ok P.E.c.n hw₅ (o := P.E.c.sl RY) (a := P.E.c.sl GY) (sl8 _ _) (sl8 _ _)
    (sl_top h9 (by decide)) (sl_top h9 (by decide)) (.inr (sl_le _ (by decide))))
    fun s₆ ⟨v₆, r₆, O₆⟩ sy₆ F₆ => ?_
  obtain hw₆ := hw₅.of_rest r₆
  obtain rd₆ : s₆.rd = s.rd := by rw [r₆.rd, r₅.rd, r₄.rd, u₃.rd, u₂b.rd, u₂a.rd, r₂.rd, rd₁]
  obtain hT₆ := P.gt_frame hk hT₀ sy₆ rd₆ F₆
  obtain U₄₆ := (U₄.trans O₅.unch).trans O₆.unch
  obtain keep : ∀ i ∈ [MP, MN, ZERO, ONE, ONEP, AP, B3P, EXPP, BP], sv P.E.c base s₆ i = sv P.E.c base s₄ i :=
    fun i hi => by
      obtain ⟨hx, hy, h55⟩ := (by decide : ∀ i ∈ [MP, MN, ZERO, ONE, ONEP, AP, B3P, EXPP, BP],
        i ≠ RX ∧ i ≠ RY ∧ i ≤ 55) i hi
      exact (O₅.unch.trans O₆.unch).wordsVal (all_app (all_one (sl_sep _ hx)) (all_one (sl_sep _ hy))) (fit h55)
  obtain one₆ : sv P.E.c base s₆ ONE = 1 := (keep ONE (by decide)).trans (P.E.const_at cs₄ 3)
  obtain rx₆ : sv P.E.c base s₆ RX = P.E.c.C.gx * 2 ^ (64 * P.E.c.n) % P.E.c.C.p := by
    show wordsVal _ _ _ _ = _
    rw [O₆.wordsVal (.inl (sl_le _ (by decide))) (fit (by decide)), v₅]; exact P.E.const_at cs₄ 7
  obtain ry₆ : sv P.E.c base s₆ RY = P.E.c.C.gy * 2 ^ (64 * P.E.c.n) % P.E.c.C.p := by
    show wordsVal _ _ _ _ = _
    rw [v₆, O₅.wordsVal (.inl (sl_le _ (by decide))) (fit (by decide))]; exact P.E.const_at cs₄ 8
  obtain h3₆ : s₆.gpr .s3 = base := by
    rw [r₆.gpr _ (by decide), r₅.gpr _ (by decide), r₄.gpr _ (by decide), u₃.gpr, u₂b.other _ (by decide),
      u₂a.other _ (by decide), r₂.gpr _ (by decide), h3₁]
  -- `[d]G`, `Z^(p-2)` and `x`.
  refine WP.seq (WP.mono (P.tailG_ok hL hw₆ h3₆ ((keep MP (by decide)).trans (P.E.const_at cs₄ 0))
    ((keep MN (by decide)).trans (P.E.const_at cs₄ 1)) ((keep ZERO (by decide)).trans (P.E.const_at cs₄ 2))
    one₆ ((keep ONEP (by decide)).trans (P.E.const_at cs₄ 4))
    ((keep AP (by decide)).trans (P.E.const_at cs₄ 5)) ((keep B3P (by decide)).trans (P.E.const_at cs₄ 6))
    ((keep EXPP (by decide)).trans (P.E.const_at cs₄ 9)) rx₆ ry₆
    ((keep BP (by decide)).trans (P.E.const_at cs₄ 11)) hT₆)
    fun s₇ ⟨Kc₇, U₇, f₇, rep₇, xolt, xoeq, acclt, acceq⟩ => ?_)
  obtain hw₇ := hw₆.of_kc Kc₇
  obtain one₇ : sv P.E.c base s₇ ONE = 1 := (U₇.wordsVal P.tail_one (fit (by decide))).trans one₆
  -- `y`.
  refine WP.seq (WP.mono (P.affine_ok hw₇ acclt one₇) fun s₈ ⟨K₈, U₈, lt₈, v₈⟩ => ?_)
  obtain hw₈ := hw₇.of_kp K₈
  -- The end.
  obtain hn0 : ∀ r ∈ [Reg.t0], r ∉ preserved := by decide
  obtain hn1 : ∀ r ∈ [Reg.t0, .t1], r ∉ preserved := by decide
  obtain K₁₆ : ∀ r ∈ preserved, s₆.gpr r = s₁.gpr r := fun r hr => by
    obtain h0 : r ∉ [Reg.t0] := fun h => hn0 r h hr
    obtain h1 : r ∉ [Reg.t0, .t1] := fun h => hn1 r h hr
    rw [r₆.gpr _ h0, r₅.gpr _ h0, r₄.gpr _ h1, u₃.gpr, u₂b.other _ (by rintro rfl; exact absurd hr (by decide)),
      u₂a.other _ (by rintro rfl; exact absurd hr (by decide)), r₂.gpr _ h1]
  obtain h2₈ : s₈.gpr .s2 = s.gpr .a0 := by
    rw [K₈.gpr _ (by decide), Kc₇.gpr _ (by decide) (by decide), K₁₆ _ (by decide), o₁]
  obtain wr₈ : s₈.wr = s.wr := by rw [K₈.wr, Kc₇.wr, r₆.wr, r₅.wr, r₄.wr, u₃.wr, u₂b.wr, u₂a.wr, r₂.wr, wr₁]
  obtain O₃ : Unch base [(P.E.c.sl FLAG, 8)] s₂.mem s₃.mem := by
    rw [u₃.mem, u₂b.mem, u₂a.mem]; exact (writeW_outside _ _ _ (by kit_slots P.E)).unch
  obtain U₁₈ := ((((O₂.unch.trans O₃).trans U₄₆).trans U₇).trans U₈)
  obtain k₆ : sv P.E.c base s₆ K = ofBytes (bytesAt s.mem (s.gpr .a1) P.E.L) := by
    show wordsVal _ _ _ _ = _
    rw [(O₃.trans U₄₆).wordsVal (by kit_apart) (fit (by decide)), e₂, a1, BitVec.add_zero,
      bytesAt_unch U₁ (by decide) (by simpa using sep_at' hdd hfd (off := 0) (k := P.E.L) (by omega_using []))]
  obtain aff : ∀ {i}, i < 45 → ∀ w ∈ P.E.affW, i ≠ YM → i ≠ YO →
      P.E.c.sl i + 8 * P.E.c.n ≤ w.1 ∨ w.1 + w.2 ≤ P.E.c.sl i := fun {i} hi w hw hm ho => by
    obtain hle := sl_le P.E.c hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact sl_sep _ hm
    · exact .inl (show P.E.c.sl i + 8 * P.E.c.n ≤ own P.E.c.n by omega_using [hle, hown])
    · exact sl_sep _ ho
    · exact .inl (show P.E.c.sl i + 8 * P.E.c.n ≤ own P.E.c.n by omega_using [hle, hown])
  obtain affF : ∀ w ∈ P.E.affW, P.E.c.sl FLAG + 8 ≤ w.1 ∨ w.1 + w.2 ≤ P.E.c.sl FLAG := fun w hw => by
    obtain hle := sl_le P.E.c (by decide : FLAG < 45)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact .inr (sl_le P.E.c (by decide : YM < FLAG))
    · exact .inl (show P.E.c.sl FLAG + 8 ≤ own P.E.c.n by omega_using [hle, hown])
    · exact .inr (sl_le P.E.c (by decide : YO < FLAG))
    · exact .inl (show P.E.c.sl FLAG + 8 ≤ own P.E.c.n by omega_using [hle, hown])
  obtain affL : ∀ w ∈ P.E.affW, 40 ≤ w.1 := fun w hw => by
    obtain hs45 := sl_lo P.E.c 45
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact Nat.le_trans (by decide) (sl_lo _ _)
    · exact (show 40 ≤ own P.E.c.n by omega_using [hs45, hown])
    · exact Nat.le_trans (by decide) (sl_lo _ _)
    · exact (show 40 ≤ own P.E.c.n by omega_using [hs45, hown])
  obtain fl₈ : word s₈.mem base (P.E.c.sl FLAG) =
      maskOf ((true && decide (ofBytes (bytesAt s.mem (s.gpr .a1) P.E.L) < P.E.c.C.n)) &&
        !decide (ofBytes (bytesAt s.mem (s.gpr .a1) P.E.L) = 0)) := by
    rw [U₈.word affF (by kit_slots P.E), f₇,
      U₄₆.word (by kit_ranges (first | exact flag_consts _ | exact Or.inr (sl_le _ (by decide))))
        (by kit_slots P.E), fl₃, k₆, maskOf_and, maskOf_and]
  refine WP.mono (P.E.finPk_ok hw₈ h2₈ hfo (fun i hi => by
      rw [wr₈, hwr]
      exact ⟨_, List.mem_cons_self .., Offset.contains_base (s.gpr .a0) (d := i) (n := 1) (k := 1 + 2 * P.E.L)
        (by omega_using [hi]) (by omega_using [hi, hLn, h9])⟩) hod fl₈)
    fun s' ⟨a0', bytes', s0', s1', s2', ra', s3', regs', sp'⟩ => ?_
  obtain lo : ∀ w ∈ ((([(P.E.c.sl K, 8 * P.E.c.n)] ++ [(P.E.c.sl FLAG, 8)]) ++
      (((consts P.E.c).map fun e => (P.E.c.sl e.1, 8 * P.E.c.n)) ++ [(P.E.c.sl RX, 8 * P.E.c.n)] ++
        [(P.E.c.sl RY, 8 * P.E.c.n)])) ++ P.E.tailW) ++ P.E.affW, 40 ≤ w.1 := by
    kit_ranges (first
      | exact affL
      | exact lo_consts _
      | exact P.E.tail_lo
      | exact Nat.le_trans (by decide) (sl_lo _ _))
  -- The registers.
  refine ⟨⟨fun r hr => ?_, by rw [sp', K₈.sp, Kc₇.sp, r₆.sp, r₅.sp, r₄.sp, u₃.sp, u₂b.sp, u₂a.sp, r₂.sp, sp₁],
    by rw [ra', lo_word U₁₈ lo (d := 24) (by decide), w3]⟩, ?_⟩
  · by_cases h0 : r = .s0
    · subst h0; rw [s0', lo_word U₁₈ lo (d := 0) (by decide), w0]
    by_cases h1 : r = .s1
    · subst h1; rw [s1', lo_word U₁₈ lo (d := 8) (by decide), w1]
    by_cases h2' : r = .s2
    · subst h2'; rw [s2', lo_word U₁₈ lo (d := 16) (by decide), w2]
    by_cases h3' : r = .s3
    · subst h3'; rw [s3', lo_word U₁₈ lo (d := 32) (by decide), w4]
    rw [regs' r hr h0 h1 h2' h3', K₈.gpr r hr, Kc₇.gpr r hr h1, K₁₆ r hr, g₁ r h0 h2' h3']
  -- The specification.
  obtain xo₈ : sv P.E.c base s₈ XO = sv P.E.c base s₇ XO :=
    U₈.wordsVal (fun w hw => aff (by decide) w hw (by decide) (by decide)) (fit (by decide))
  obtain rz₈ : sv P.E.c base s₈ RZ = sv P.E.c base s₇ RZ :=
    U₈.wordsVal (fun w hw => aff (by decide) w hw (by decide) (by decide)) (fit (by decide))
  rw [acceq] at v₈
  rw [rz₈] at a0'
  rw [xo₈, rz₈] at bytes'
  generalize hD : ofBytes (bytesAt s.mem (s.gpr .a1) P.E.L) = D at a0' bytes' k₆
  rw [k₆] at rep₇
  obtain hpk : P.E.pk s.mem (s.gpr .a1) = Spec.EcKey.publicKey P.E.c.C D := by rw [← hD]
  obtain enc : ∀ x y : Fe P.E.c.C, Spec.EcKey.encodePoint (.affine x y) =
      4 :: (toBytes P.E.L x.val ++ toBytes P.E.L y.val) := fun x y => by rw [← P.E.len]; rfl
  unfold pkPost
  rw [hpk]
  by_cases hd : 1 ≤ D ∧ D < P.E.c.C.n
  · obtain ⟨hR, -, -, rzlt⟩ := rep₇ hd.1 hd.2
    obtain eG : Point.affine (toM P.E.c.C.p (2 ^ (64 * P.E.c.n)) (sv P.E.c base s₆ RX))
        (toM P.E.c.C.p (2 ^ (64 * P.E.c.n)) (sv P.E.c base s₆ RY)) = Spec.Weierstrass.G P.E.c.C := by
      rw [rx₆, ry₆, toM_mont P.E.unit, toM_mont P.E.unit]; rfl
    rw [eG] at hR
    obtain hn : decide (D < P.E.c.C.n) = true := decide_eq_true hd.2
    obtain h0 : decide (D = 0) = false := decide_eq_false (by omega_using [hd])
    rw [hn, h0] at a0' bytes'
    obtain hpk' := VG.Proof.EcKey.publicKey_eq hL hR xolt xoeq lt₈ v₈
    rw [ite_eq_left hd] at hpk'
    by_cases hz : sv P.E.c base s₇ RZ = 0
    · rw [ite_eq_left ((toM_eq_zero_iff P.E.unit rzlt).mpr hz)] at hpk'
      rw [hpk']
      rw [decide_eq_true hz] at a0' bytes'
      exact ⟨a0', bytes'.trans (zeros_eq _)⟩
    · rw [ite_eq_right fun h => hz ((toM_eq_zero_iff P.E.unit rzlt).mp h)] at hpk'
      rw [hpk']
      rw [decide_eq_false hz] at a0' bytes'
      refine ⟨a0', bytes'.trans ?_⟩
      exact (enc ⟨_, xolt⟩ ⟨_, lt₈⟩).symm
  · rw [publicKey_none hd]
    obtain hb : ((true && decide (D < P.E.c.C.n)) && !decide (D = 0)) = false := by
      by_cases hn : D < P.E.c.C.n
      · have : D = 0 := by omega_using [hd, hn]
        simp [this]
      · simp [hn]
    rw [hb] at a0' bytes'
    exact ⟨a0', bytes'.trans (zeros_eq _)⟩

end PkKit

end VG.Proof.Ecdh.RISCV64

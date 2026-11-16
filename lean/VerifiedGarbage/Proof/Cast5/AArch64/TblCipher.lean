module

public import VerifiedGarbage.Proof.Cast5.AArch64.TblRound
public import VerifiedGarbage.Proof.Cast5.Round
import VerifiedGarbage.Proof.Cast5.AArch64.Block
import VerifiedGarbage.Proof.Cast5.AArch64.Run
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset

/-!
# CAST5 on AArch64: the rounds on sixteen blocks

`cipherEnc_ok`, `cipherDec_ok`: `cipher up`, with the subkeys at `x0` and
their number, 12 or 16, in `x16`, leaves in `A` and `B` the halves of each of
the sixteen blocks after its rounds (`encFold`, `decFold`).
-/

@[expose] public section

namespace VG.Proof.Cast5.AArch64.Tbl

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Cast5.AArch64.Tbl
open VG.Impl.Blowfish.AArch64 (aReg bReg c64 c128)
open VG.Spec.Cast5 (Word Schedule)
open VG.Proof.Cast5 (encFold decFold encFold_succ decFold_succ add_ofNat_add)
open VG.Proof.Cast5.AArch64 (wp_countdown groups_x7 x8_zero dec_x12 four decFold_zero)
open VG.Proof.Blowfish.AArch64 (lane Consts)
open VG.Proof.MlKem.AArch64 (eval_zero)

/-- What the rounds read: the table's address in `x9`, the constants of the
lookups, and the subkeys `k` at `x0`. -/
structure CPre (s : State) (k : Schedule) : Prop where
  x9 : s.gpr .x9 = s.syms planesSym
  consts : Consts s
  sched : InRegions (s.rd ++ s.wr) (s.gpr .x0) 128
  key : ∀ j < 32, s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 (4 * j)) 32 = k.getD j 0

/-- The general-purpose registers the rounds write. -/
def cipherG : List Reg := [.x4, .x5, .x6, .x7, .x8, .x13, .x14, .x15]

/-- The halves of the sixteen blocks, in `A` and `B`. -/
def Halves (v : VReg → BitVec 128) (lr : Nat → Word × Word) : Prop :=
  ∀ n < 16, (lane v aReg n, lane v bReg n) = lr n

theorem consts_notin_round : c64 ∉ roundV ∧ c128 ∉ roundV := by decide

theorem round_step {s u : State} {k : Schedule} (P : CPre s k) (fr : RFrame cipherG roundV s u) {t i : Nat}
    (ht : t = 1 ∨ t = 2 ∨ t = 3) (hti : i % 3 = t % 3) (hi : 1 ≤ i ∧ i ≤ 16)
    (h5 : u.gpr .x5 = u.gpr .x0 + BitVec.ofNat 64 (4 * (i - 1))) (up : Bool) {lr : Nat → Word × Word}
    (hl : Halves u.v lr) :
    WP isa (.block (round t up)) u fun v =>
      Halves v.v (fun n => Spec.Cast5.round k i (lr n)) ∧ RFrame cipherG roundV s v ∧
      v.gpr .x5 = (if up then u.gpr .x5 + 4 else u.gpr .x5 - 4) ∧ v.gpr .x7 = u.gpr .x7 ∧
      v.gpr .x8 = u.gpr .x8 := by
  have x0 : u.gpr .x0 = s.gpr .x0 := fr.g _ (by decide)
  have h9 : u.gpr .x9 = u.syms planesSym := by rw [fr.g _ (by decide), fr.syms]; exact P.x9
  have hc : Consts u :=
    ⟨fun e he => by rw [fr.v _ consts_notin_round.1]; exact P.consts.1 e he,
      fun e he => by rw [fr.v _ consts_notin_round.2]; exact P.consts.2 e he⟩
  have sched : InRegions (u.rd ++ u.wr) (u.gpr .x0) 128 := by rw [fr.rd, fr.wr, x0]; exact P.sched
  have e0 : u.gpr .x5 + BitVec.ofNat 64 0 = u.gpr .x0 + BitVec.ofNat 64 (4 * (i - 1)) := by
    rw [h5, add_ofNat_add]; rfl
  have e64 : u.gpr .x5 + BitVec.ofNat 64 64 = u.gpr .x0 + BitVec.ofNat 64 (4 * (15 + i)) := by
    rw [h5, add_ofNat_add]; congr 2; omega_using [hi]
  have h0 : InRegions (u.rd ++ u.wr) (u.gpr .x5 + BitVec.ofNat 64 0) 4 := by
    rw [e0]; exact CallLay.inRegions_sub sched (by omega_using [hi]) (by decide)
  have h64 : InRegions (u.rd ++ u.wr) (u.gpr .x5 + BitVec.ofNat 64 64) 4 := by
    rw [e64]; exact CallLay.inRegions_sub sched (by omega_using [hi]) (by decide)
  refine WP.mono (round_ok ht hti up h9 hc h0 h64) ?_
  rintro v ⟨va, vb, v5, vf⟩
  refine ⟨fun n hn => ?_, fr.trans (vf.mono (by decide) (fun _ h => h)), v5, vf.g _ (by decide),
    vf.g _ (by decide)⟩
  show _ = Spec.Cast5.round k i (lr n)
  rw [va n hn, vb n hn, e0, e64, x0, fr.mem, P.key _ (by omega_using [hi]), P.key _ (by omega_using [hi]),
    ← hl n hn]
  rfl

theorem countDown_ok {s u : State} (fr : RFrame cipherG roundV s u) {lr : Nat → Word × Word}
    (hl : Halves u.v lr) :
    WP isa (.block [.subImm .x .x7 .x7 1]) u fun v => Halves v.v lr ∧ RFrame cipherG roundV s v ∧
      v.gpr .x5 = u.gpr .x5 ∧ v.gpr .x7 = u.gpr .x7 - BitVec.ofNat 64 1 ∧ v.gpr .x8 = u.gpr .x8 := by
  refine WP.of_runBlock ⟨u.write .x .x7 (u.read .x .x7 - BitVec.ofNat _ 1), by
    rw [runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_nil], hl, ?_,
    gpr_write_of_ne _ _ _ (by decide), gpr_write_self _ _ _ _, gpr_write_of_ne _ _ _ (by decide)⟩
  refine fr.trans ⟨fun r hr => gpr_write_of_ne _ _ _ fun e => hr (by rw [e]; decide), fun _ _ => rfl, rfl, rfl,
    rfl, rfl, rfl⟩

theorem groupEnc_eq : group true = round 1 true ++ (round 2 true ++ (round 3 true ++
    ([.subImm .x .x7 .x7 1] : List Instr))) := by
  simp only [group, ite_true, List.append_assoc]

theorem groupDec_eq : group false = round 3 false ++ (round 2 false ++ (round 1 false ++
    ([.subImm .x .x7 .x7 1] : List Instr))) := by
  simp only [group, Bool.false_eq_true, ite_false, List.append_assoc]

/-- Rounds `3 g + 1`, `3 g + 2`, `3 g + 3` of encryption. -/
theorem groupEnc_ok {s u : State} {k : Schedule} (P : CPre s k) (fr : RFrame cipherG roundV s u) {g : Nat}
    (hg : 3 * g + 3 ≤ 16) {lr : Nat → Word × Word} (hl : Halves u.v (fun n => encFold k (3 * g) (lr n)))
    (h5 : u.gpr .x5 = u.gpr .x0 + BitVec.ofNat 64 (12 * g)) :
    WP isa (.block (group true)) u fun v =>
      Halves v.v (fun n => encFold k (3 * (g + 1)) (lr n)) ∧ RFrame cipherG roundV s v ∧
      v.gpr .x5 = v.gpr .x0 + BitVec.ofNat 64 (12 * (g + 1)) ∧
      v.gpr .x7 = u.gpr .x7 - BitVec.ofNat 64 1 ∧ v.gpr .x8 = u.gpr .x8 := by
  have hdi : ∀ {v : State}, RFrame cipherG roundV s v → v.gpr .x0 = u.gpr .x0 :=
    fun hv => (hv.g .x0 (by decide)).trans (fr.g .x0 (by decide)).symm
  rw [groupEnc_eq, WP.block_append_iff]
  refine WP.mono (round_step P fr (t := 1) (i := 3 * g + 1) (by decide) (by omega_arith) (by omega_arith)
    (by rw [h5]; congr 2; omega_arith) true hl) fun v₁ ⟨l₁, f₁, a₁, b₁, c₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (round_step P f₁ (t := 2) (i := 3 * g + 2) (by decide) (by omega_arith) (by omega_arith)
    (by rw [a₁, ite_eq_left rfl, h5, hdi f₁, four, add_ofNat_add]; congr 2; omega_arith) true l₁)
    fun v₂ ⟨l₂, f₂, a₂, b₂, c₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (round_step P f₂ (t := 3) (i := 3 * g + 3) (by decide) (by omega_arith) (by omega_arith)
    (by rw [a₂, ite_eq_left rfl, a₁, ite_eq_left rfl, h5, hdi f₂, four, add_ofNat_add, add_ofNat_add]
        congr 2; omega_arith) true l₂) fun v₃ ⟨l₃, f₃, a₃, b₃, c₃⟩ => ?_
  refine WP.mono (countDown_ok f₃ l₃) fun v₄ ⟨l₄, f₄, a₄, b₄, c₄⟩ => ?_
  refine ⟨fun n hn => ?_, f₄, ?_, by rw [b₄, b₃, b₂, b₁], by rw [c₄, c₃, c₂, c₁]⟩
  · show _ = encFold k (3 * (g + 1)) (lr n)
    rw [show 3 * (g + 1) = 3 * g + 2 + 1 by omega_arith, encFold_succ, encFold_succ, encFold_succ]
    exact l₄ n hn
  · rw [a₄, a₃, ite_eq_left rfl, a₂, ite_eq_left rfl, a₁, ite_eq_left rfl, h5, hdi f₄, four,
      add_ofNat_add, add_ofNat_add, add_ofNat_add, show 12 * g + 4 + 4 + 4 = 12 * (g + 1) by omega_arith]

/-- Rounds `n - m`, `n - m - 1`, `n - m - 2` of decryption with `n` rounds,
after the first `m`. -/
theorem groupDec_ok {s u : State} {k : Schedule} (P : CPre s k) (fr : RFrame cipherG roundV s u) {n m : Nat}
    (hm : m + 3 ≤ n) (hn : n ≤ 16) (h3 : (n - m) % 3 = 0) {lr : Nat → Word × Word}
    (hl : Halves u.v (fun j => decFold k n m (lr j)))
    (h5 : u.gpr .x5 = u.gpr .x0 + BitVec.ofNat 64 (4 * (n - m - 1))) :
    WP isa (.block (group false)) u fun v =>
      Halves v.v (fun j => decFold k n (m + 3) (lr j)) ∧ RFrame cipherG roundV s v ∧
      v.gpr .x5 = u.gpr .x5 - 12 ∧ v.gpr .x7 = u.gpr .x7 - BitVec.ofNat 64 1 ∧ v.gpr .x8 = u.gpr .x8 := by
  have hdi : ∀ {v : State}, RFrame cipherG roundV s v → v.gpr .x0 = u.gpr .x0 :=
    fun hv => (hv.g .x0 (by decide)).trans (fr.g .x0 (by decide)).symm
  have sub4 (x : Addr) (a : Nat) (ha : 4 ≤ a) :
      x + BitVec.ofNat 64 a - 4 = x + BitVec.ofNat 64 (a - 4) := by
    rw [show (4 : Addr) = BitVec.ofNat 64 4 from rfl, Offset.add_ofNat_sub _ ha]
  rw [groupDec_eq, WP.block_append_iff]
  refine WP.mono (round_step P fr (t := 3) (i := n - m) (by decide) (by omega_arith) (by omega_arith)
    h5 false hl) fun v₁ ⟨l₁, f₁, a₁, b₁, c₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (round_step P f₁ (t := 2) (i := n - m - 1) (by decide) (by omega_arith) (by omega_arith)
    (by rw [a₁, ite_eq_right Bool.false_ne_true, h5, hdi f₁, sub4 _ _ (by omega_arith)]; congr 2; omega_arith)
    false l₁) fun v₂ ⟨l₂, f₂, a₂, b₂, c₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (round_step P f₂ (t := 1) (i := n - m - 2) (by decide) (by omega_arith) (by omega_arith)
    (by rw [a₂, ite_eq_right Bool.false_ne_true, a₁, ite_eq_right Bool.false_ne_true, h5, hdi f₂,
      sub4 _ _ (by omega_arith), sub4 _ _ (by omega_arith)]; congr 2; omega_arith) false l₂)
    fun v₃ ⟨l₃, f₃, a₃, b₃, c₃⟩ => ?_
  refine WP.mono (countDown_ok f₃ l₃) fun v₄ ⟨l₄, f₄, a₄, b₄, c₄⟩ => ?_
  refine ⟨fun j hj => ?_, f₄, ?_, by rw [b₄, b₃, b₂, b₁], by rw [c₄, c₃, c₂, c₁]⟩
  · show _ = decFold k n (m + 3) (lr j)
    rw [decFold_succ, decFold_succ, decFold_succ, show n - (m + 1) = n - m - 1 by omega_arith,
      show n - (m + 2) = n - m - 2 by omega_arith]
    exact l₄ j hj
  · rw [a₄, a₃, a₂, a₁]
    simp only [Bool.false_eq_true, ite_false]
    rw [BitVec.sub_sub, BitVec.sub_sub]
    rfl

/-! ## The rounds -/

theorem cipherEnc_eq : cipher true =
    .seq (.block (([.addImm .x .x5 .x0 0] : List Instr) ++ groups))
      (.seq (.loop (.block (group true)) (.nonzero .x .x7))
        (.ite (.zero .x .x8) (.block (round 1 true)) (.block []))) := rfl

theorem cipherDec_eq : cipher false =
    .seq (.block (([.lsl .x .x5 .x16 2, .add .x .x5 .x5 .x0, .subImm .x .x5 .x5 4] : List Instr) ++ groups))
      (.seq (.ite (.zero .x .x8) (.block (round 1 false)) (.block []))
        (.loop (.block (group false)) (.nonzero .x .x7))) := rfl

theorem RFrame.refl (gs : List Reg) (vs : List VReg) (s : State) : RFrame gs vs s s :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem RFrame.write {gs : List Reg} {vs : List VReg} {s u : State} (h : RFrame gs vs s u) {d : Reg}
    (hd : d ∈ gs) (a : BitVec 64) : RFrame gs vs s (u.write .x d a) :=
  h.trans ⟨fun r hr => gpr_write_of_ne _ _ _ fun e => hr (by rw [e]; exact hd), fun _ _ => rfl, rfl, rfl, rfl,
    rfl, rfl⟩

/-- Encryption's rounds, 12 or 16, on the sixteen blocks. -/
theorem cipherEnc_ok {s : State} {k : Schedule} {n : Nat} (P : CPre s k) (hn : n = 12 ∨ n = 16)
    (h16 : s.gpr .x16 = BitVec.ofNat 64 n) :
    WP isa (cipher true) s fun v =>
      Halves v.v (fun m => encFold k n (lane s.v aReg m, lane s.v bReg m)) ∧ RFrame cipherG roundV s v := by
  have hG : 0 < n / 4 + 1 ∧ n / 4 + 1 < 2 ^ 64 := by rcases hn with rfl | rfl <;> decide
  let lr (m : Nat) : Word × Word := (lane s.v aReg m, lane s.v bReg m)
  have start : WP isa (.block (([.addImm .x .x5 .x0 0] : List Instr) ++ groups)) s fun u =>
      Halves u.v lr ∧ RFrame cipherG roundV s u ∧ u.gpr .x5 = u.gpr .x0 ∧
      u.gpr .x7 = BitVec.ofNat 64 (n / 4 + 1) ∧ u.gpr .x8 = BitVec.ofNat 64 n - BitVec.ofNat 64 16 := by
    unfold groups
    crun [h16]
    exact ⟨fun m _ => rfl, ((((RFrame.refl _ _ s).write (by decide) _).write (by decide) _).write (by decide) _).write
      (by decide) _, BitVec.add_zero _, groups_x7 hn⟩
  rw [cipherEnc_eq]
  refine WP.seq (WP.mono start fun u ⟨hu, fu, u5, u7, u8⟩ => ?_)
  refine WP.seq (WP.mono (wp_countdown (cnt := .x7) (N := n / 4 + 1) hG.2 hG.1
    (fun g v => Halves v.v (fun m => encFold k (3 * g) (lr m)) ∧ RFrame cipherG roundV s v ∧
      v.gpr .x5 = v.gpr .x0 + BitVec.ofNat 64 (12 * g) ∧ v.gpr .x8 = BitVec.ofNat 64 n - BitVec.ofNat 64 16)
    (fun g hg v ⟨hv, fv, h5, h8⟩ _ =>
      WP.mono (groupEnc_ok P fv (by rcases hn with rfl | rfl <;> omega_arith) hv h5)
        fun w ⟨hw, fw, w5, w7, w8⟩ => ⟨⟨hw, fw, w5, w8.trans h8⟩, w7⟩)
    ⟨fun m hm => hu m hm, fu, by rw [u5, Nat.mul_zero, BitVec.add_zero], u8⟩ u7) fun v ⟨hv, fv, v5, v8⟩ => ?_)
  refine WP.ite (decide (n = 16)) (by rw [eval_zero, v8, x8_zero hn]) (fun hd => ?_) (fun hd => ?_)
  · have e : n = 16 := of_decide_eq_true hd
    subst e
    refine WP.mono (round_step P fv (t := 1) (i := 16) (by decide) (by decide) (by decide) v5 true hv)
      fun x ⟨hx, fx, _, _, _⟩ => ⟨fun m hm => ?_, fx⟩
    show _ = encFold k (15 + 1) (lr m)
    rw [encFold_succ]
    exact hx m hm
  · have e : n = 12 := by
      rcases hn with h' | h'
      · exact h'
      · exact absurd h' (of_decide_eq_false hd)
    subst e
    exact WP.block_nil ⟨fun m hm => hv m hm, fv⟩

/-- Decryption's rounds, 12 or 16, on the sixteen blocks. -/
theorem cipherDec_ok {s : State} {k : Schedule} {n : Nat} (P : CPre s k) (hn : n = 12 ∨ n = 16)
    (h16 : s.gpr .x16 = BitVec.ofNat 64 n) :
    WP isa (cipher false) s fun v =>
      Halves v.v (fun m => decFold k n n (lane s.v aReg m, lane s.v bReg m)) ∧ RFrame cipherG roundV s v := by
  have hG : 0 < n / 4 + 1 ∧ n / 4 + 1 < 2 ^ 64 ∧ n % 3 + 3 * (n / 4 + 1) = n ∧ n % 3 ≤ 1 := by
    rcases hn with rfl | rfl <;> decide
  let lr (m : Nat) : Word × Word := (lane s.v aReg m, lane s.v bReg m)
  have start : WP isa (.block (([.lsl .x .x5 .x16 2, .add .x .x5 .x5 .x0, .subImm .x .x5 .x5 4] :
      List Instr) ++ groups)) s fun u =>
      Halves u.v lr ∧ RFrame cipherG roundV s u ∧ u.gpr .x5 = u.gpr .x0 + BitVec.ofNat 64 (4 * (n - 1)) ∧
      u.gpr .x7 = BitVec.ofNat 64 (n / 4 + 1) ∧ u.gpr .x8 = BitVec.ofNat 64 n - BitVec.ofNat 64 16 := by
    unfold groups
    crun [h16]
    exact ⟨fun m _ => rfl, ((((((RFrame.refl _ _ s).write (by decide) _).write (by decide) _).write (by decide) _).write
      (by decide) _).write (by decide) _).write (by decide) _, dec_x12 hn _, groups_x7 hn⟩
  rw [cipherDec_eq]
  refine WP.seq (WP.mono start fun u ⟨hu, fu, u5, u7, u8⟩ => ?_)
  have first : WP isa (.ite (.zero .x .x8) (.block (round 1 false)) (.block [])) u fun v =>
      Halves v.v (fun m => decFold k n (n % 3) (lr m)) ∧ RFrame cipherG roundV s v ∧
      v.gpr .x5 = v.gpr .x0 + BitVec.ofNat 64 (4 * (n - n % 3 - 1)) ∧
      v.gpr .x7 = BitVec.ofNat 64 (n / 4 + 1) := by
    refine WP.ite (decide (n = 16)) (by rw [eval_zero, u8, x8_zero hn]) (fun hd => ?_) (fun hd => ?_)
    · have e : n = 16 := of_decide_eq_true hd
      subst e
      refine WP.mono (round_step P fu (t := 1) (i := 16) (by decide) (by decide) (by decide) u5 false hu)
        fun x ⟨hx, fx, x5, x7, _⟩ => ⟨fun m hm => ?_, fx, ?_, x7.trans u7⟩
      · show _ = decFold k 16 (0 + 1) (lr m)
        rw [decFold_succ, decFold_zero]
        exact hx m hm
      · have hdi : x.gpr .x0 = u.gpr .x0 := (fx.g .x0 (by decide)).trans (fu.g .x0 (by decide)).symm
        rw [x5, ite_eq_right Bool.false_ne_true, u5, hdi, four, Offset.add_ofNat_sub _ (by decide)]
    · have e : n = 12 := by
        rcases hn with h' | h'
        · exact h'
        · exact absurd h' (of_decide_eq_false hd)
      subst e
      exact WP.block_nil ⟨fun m hm => hu m hm, fu, u5, u7⟩
  refine WP.seq (WP.mono first fun v ⟨hv, fv, v5, v7⟩ => ?_)
  refine WP.mono (wp_countdown (cnt := .x7) (N := n / 4 + 1) hG.2.1 hG.1
    (fun g w => Halves w.v (fun m => decFold k n (n % 3 + 3 * g) (lr m)) ∧ RFrame cipherG roundV s w ∧
      (n % 3 + 3 * g < n → w.gpr .x5 = w.gpr .x0 + BitVec.ofNat 64 (4 * (n - (n % 3 + 3 * g) - 1))))
    (fun g hg w ⟨hw, fw, w5⟩ _ => WP.mono (groupDec_ok P fw (m := n % 3 + 3 * g) (by omega_arith) (by
        rcases hn with rfl | rfl <;> decide) (by omega_arith) hw (w5 (by omega_arith)))
      fun x ⟨hx, fx, x5, x7, _⟩ => ⟨⟨fun m hm => ?_, fx, fun hlt => ?_⟩, x7⟩)
    ⟨fun m hm => hv m hm, fv, fun _ => by rw [Nat.mul_zero, Nat.add_zero]; exact v5⟩ v7)
    fun w ⟨hw, fw, _⟩ => ⟨fun m hm => ?_, fw⟩
  · show _ = decFold k n (n % 3 + 3 * (g + 1)) (lr m)
    rw [show n % 3 + 3 * (g + 1) = n % 3 + 3 * g + 3 by omega_arith]
    exact hx m hm
  · have hdi : x.gpr .x0 = w.gpr .x0 := (fx.g .x0 (by decide)).trans (fw.g .x0 (by decide)).symm
    rw [x5, w5 (by omega_arith), hdi, show (12 : Addr) = BitVec.ofNat 64 12 from rfl,
      Offset.add_ofNat_sub _ (by omega_arith)]
    congr 2
    omega_arith
  · have := hw m hm
    rw [hG.2.2.1] at this
    exact this

end VG.Proof.Cast5.AArch64.Tbl

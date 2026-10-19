module

public import VerifiedGarbage.Proof.Ffdh.AArch64.GenerateKey.CT
public import VerifiedGarbage.Proof.Ffdh.AArch64.GenerateKey.Correct
import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.CT
import VerifiedGarbage.Proof.Ffdh.AArch64.Exchange.Stages
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExpCT
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Ffdh.AArch64.GenerateKey.CT
meta import VerifiedGarbage.Proof.Ffdh.AArch64.GenerateKey.Correct
meta import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.CT
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Exchange.Stages
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowExpCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-!
# `vg_ffdh_generate_key` on AArch64: constant time of the key's part

With the scalar in range (`tail_ct`): `R² mod p`, `g^x mod p` over the
scalar's significant octets (constant time in the exponent), y's range and
subgroup flags, and the results masked by them, without a branch on them.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.GenerateKey

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt (leave)
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive VG.Proof.Ffdh
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Proof.Ffdh.AArch64.CheckDomain (pins_nil)
open VG.Spec.Ffdh

/-- After the test of the domain's length, with `R² mod p`. -/
def T2Q (p : GkP) (rb : List Byte) (t : State) : Prop :=
  (∃ mi, Pa (p.D₁ rb) mi t ∧ R2f (p.D₁ rb) t ∧ t.gpr .x3 = BitVec.ofNat 64 (p.dl - 2 * p.k)) ∧ Ok p rb ∧
    p.pv = true

theorem t2_t2q (p : GkP) (rb : List Byte) (t : State) (h : T2 p rb t) :
    WP isa (.block qTest) t fun u => T2Q p rb u ∧ KX t u := by
  obtain ⟨⟨mi, hP, hR⟩, ho⟩ := h
  exact WP.mono hP.qtest fun u ⟨⟨h3, hm⟩, k⟩ => ⟨⟨⟨mi, hP.keep hm k (by decide), hR.mem hm, h3⟩, ho⟩,
    k.mono (by decide)⟩

theorem t2q_eval {p : GkP} {rb : List Byte} {t : State} (h : T2Q p rb t) :
    isa.eval (.zero .x .x3) t = some (BitVec.ofNat 64 (p.dl - 2 * p.k) == 0) := by
  obtain ⟨⟨_, _, _, h3⟩, _⟩ := h
  rw [eval_zero, h3]

theorem t2q_t3 (p : GkP) (rb : List Byte) (t : State) (h : T2Q p rb t) {sp : Nat} (hsp : (p.D₁ rb).bs = sp) :
    WP isa (seqs (scan sp)) t fun u => T3 p rb u ∧ KX t u := by
  obtain ⟨⟨mi, hP, hR, -⟩, ho⟩ := h
  subst hsp
  refine WP.mono hP.scanB fun u ⟨⟨hu, _, hEl, _, f⟩, k⟩ => ⟨⟨⟨mi, hu, hR.hdr hP.1 f (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [sEp, sEl, sFn] <;> omega), hEl⟩, ho⟩, k⟩

theorem t2q_pre (p : GkP) (rb : List Byte) (t : State) (h : T2Q p rb t) {sp : Nat} (hsp : (p.D₁ rb).bs = sp) :
    ScanPre sp (p.D₀ []).bsp t := by
  obtain ⟨⟨mi, hP, -⟩, -⟩ := h
  subst hsp
  exact hP.scanPreB

/-- The bound's scan, with `R² mod p`. -/
theorem boundT_ct : RelCT isa (Two (Ex T2)) (seqs GenerateKey.bound) (Two (Ex T3)) := by
  unfold GenerateKey.bound
  refine seqs_cons_ct (by simp) (RelCT.seq (R := Two (Ex T2Q)) (ex_post (two_taint [.x0]
    (pins_x0B GkP.B fun (p : GkP) s (h : Ex T2 p s) => by
      obtain ⟨_, ⟨⟨_, hP, _⟩, _⟩, _⟩ := h; exact hP.2.2.2.2.2.2) (by taint_decide)) t2_t2q) ?_)
  rw [seqs_one]
  refine two_ite (fun p s₁ s₂ ⟨_, h₁, _⟩ ⟨_, h₂, _⟩ => by rw [t2q_eval h₁, t2q_eval h₂]) ?_ ?_
  · exact ex_post' (two_map (fun p : GkP => (p.D₀ []).bsp) (fun p s ⟨⟨rb, h, _⟩, he⟩ =>
      t2q_pre p rb s h (bs_n h.1.choose_spec.1.1 (Option.some.inj ((t2q_eval h).symm.trans he))))
      (scan_ct (by taint_decide) (by taint_decide))) fun p rb s h he =>
        t2q_t3 p rb s h (bs_n h.1.choose_spec.1.1 (Option.some.inj ((t2q_eval h).symm.trans he)))
  · exact ex_post' (two_map (fun p : GkP => (p.D₀ []).bsp) (fun p s ⟨⟨rb, h, _⟩, he⟩ =>
      t2q_pre p rb s h (bs_q h.1.choose_spec.1.1 (Option.some.inj ((t2q_eval h).symm.trans he))))
      (scan_ct (by taint_decide) (by taint_decide))) fun p rb s h he =>
        t2q_t3 p rb s h (bs_q h.1.choose_spec.1.1 (Option.some.inj ((t2q_eval h).symm.trans he)))

/-- `g^x`'s public data. -/
abbrev GkP.pwG (p : GkP) : PowPub :=
  (p.D₀ []).pw (p.dp + BitVec.ofNat 64 p.k) p.k (p.xp + BitVec.ofNat 64 (p.D₀ []).bl) (p.k - (p.D₀ []).bl)

/-- `y^q`'s public data. -/
abbrev GkP.pwY (p : GkP) : PowPub :=
  (p.D₀ []).pw p.yp p.k (off (p.dp + BitVec.ofNat 64 (2 * p.k)) (lead (p.D₀ []).qb)) (p.k - lead (p.D₀ []).qb)

/-- From `R² mod p` to y's range. -/
theorem r2pow_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (Two (Ex T0)) (seqs (r2Steps M.mm ++ (.block [leave] :: (GenerateKey.bound ++
      (.block epBlk :: (pow W.code S.code M.mm sG sK sEp sEl ++ range aY)))))) (Two (Ex T6)) := by
  refine RelCT.seqs_append (by simp [r2Steps]) (by simp) (RelCT.seq (R := Two (Ex T1))
    (ex_post ((r2_ct M).mono (fun _ _ h => two_bind (fun p s₁ s₂ ⟨rb₁, ⟨⟨mi₁, hI₁⟩, _⟩, _⟩
        ⟨rb₂, ⟨⟨mi₂, hI₂⟩, _⟩, _⟩ => by
      have hb := hI₁.1
      have ew := hb.ew
      have := hb.k1
      obtain ⟨hodd, -⟩ := valid_facts hI₁.2.2.2.2.2 hb.k1
      obtain rfl : mi₁ = mi₂ := xvals_minv (show 1 ≤ (p.D₁ rb₁).w by omega) hodd hI₁.2.2.1 hI₂.2.2.1
      exact ⟨_, hI₁.r2pre, hI₂.r2pre⟩) h) fun _ _ h => h) (t0_t1 M)) ?_)
  refine seqs_cons_ct (by simp [GenerateKey.bound]) (RelCT.seq (R := Two (Ex T2)) (ex_post (two_taint [.x0]
    (pins_x0B GkP.g fun (p : GkP) s (h : Ex T1 p s) => by
      obtain ⟨_, ⟨⟨_, hM⟩, _⟩, _⟩ := h; exact hM.2.1.sub.x0) (by taint_decide)) t1_t2) ?_)
  refine RelCT.seqs_append (by simp [GenerateKey.bound]) (by simp) (RelCT.seq (R := Two (Ex T3)) boundT_ct ?_)
  refine seqs_cons_ct (by simp [pow]) (RelCT.seq (R := Two (Ex T4)) (ex_post (two_taint [.x0]
    (pins_x0B GkP.B fun (p : GkP) s (h : Ex T3 p s) => by
      obtain ⟨_, ⟨⟨_, hP, _⟩, _⟩, _⟩ := h; exact hP.2.2.2.2.2.2) (by taint_decide)) t3_t4) ?_)
  refine RelCT.seqs_append (by simp [pow]) (by simp [range]) (RelCT.seq (R := Two (Ex T5))
    (ex_post (two_map GkP.pwG (fun p s ⟨rb, h, _⟩ => t4_pre p rb s h)
      (pow_ct W M S (loadArr_ct (by decide) (by taint_decide) (by taint_decide))
        (expLoop_ct W M S (by taint_decide)) (by taint_decide) (by taint_decide) (by taint_decide)))
      (t4_t5 W M S)) ?_)
  exact ex_post (two_map GkP.ws (fun p s ⟨rb, ⟨⟨mi, hM, _⟩, _⟩, _⟩ => hM.inn.goodW1) (range_ct (by decide) (by decide)
    (by taint_decide) (by taint_decide) (by taint_decide))) t5_t6

/-! ## y's store and flags -/

/-- `yBlk`'s first part: the bases. -/
abbrev yb1 : List Instr := [ldh .x12 sW, ldh .x8 (sArr aY), ldh .x5 Crt.sLink]

/-- `yBlk`'s second part. -/
abbrev yb2 : List Instr := [Crt.ldw .x1 .x5 sY, Crt.ldw .x9 .x5 sK, .add .x .x1 .x1 .x9, movi .x7 0, .subImm .x .x15 .x7 1]

theorem t6_fin1 (p : GkP) (rb : List Byte) (s : State) (h : T6 p rb s) (hd : Dst p s) :
    WP isa (.block yb1) s fun t => (t.gpr .x0 = p.g ∧ t.gpr .x8 = off p.g (slot ((p.k + 7) / 8) aY) ∧
      t.gpr .x5 = p.B) ∧ ∃ rb, WP isa (.block yb2) t fun u => T7 p rb u ∧ Dst p u := by
  have hI := h.1.choose_spec.1
  have hc := hI.2.1
  have hw : WP isa (.block (yb1 ++ yb2)) s fun u => T7 p rb u ∧ Dst p u :=
    WP.mono (t6_t7 p rb s h) fun _ ⟨hu, k⟩ => ⟨hu, hd.keep k⟩
  rw [WP.block_append_iff] at hw
  exact WP.mono (wp_and (Exchange.finBlk1_ok hc.x0 (hc.hdr.harr aY (by decide)) hc.link hI.hlG) hw)
    fun t ⟨h₁, h₂⟩ => ⟨h₁, rb, h₂⟩

theorem yBlk_ct : RelCT isa (Two (Ex T6)) (.block yBlk) (Two (Ex T7)) :=
  RelCT.block_append (l₁ := yb1) (l₂ := yb2) (RelCT.seq
    (two_piece (Ψ := fun (p : GkP) t => (t.gpr .x0 = p.g ∧ t.gpr .x8 = off p.g (slot ((p.k + 7) / 8) aY) ∧
        t.gpr .x5 = p.B) ∧ ∃ rb, WP isa (.block yb2) t fun u => T7 p rb u ∧ Dst p u) [.x0]
      (pins_x0B GkP.g fun (p : GkP) s (h : Ex T6 p s) => by
        obtain ⟨_, ⟨⟨_, hI, _⟩, _⟩, _⟩ := h; exact hI.2.1.x0) (by taint_decide)
      fun p s ⟨rb, h, hd⟩ => t6_fin1 p rb s h hd)
    (two_piece [.x0, .x5, .x8] (pins_of (fun (p : GkP) r => if r = .x0 then p.g else if r = .x5 then p.B else
        off p.g (slot ((p.k + 7) / 8) aY)) fun p s h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.1.1
      · exact h.1.2.2
      · exact h.1.2.1) (by taint_decide) fun p s ⟨_, rb, h⟩ => WP.mono h fun _ h => ⟨rb, h⟩))

theorem store_ct : RelCT isa (Two (Ex T7)) storeBE (Two (Ex T8)) :=
  ex_postD (two_taint [.x1, .x8, .x9] (pins_of (fun (p : GkP) r => if r = .x1 then p.yp + BitVec.ofNat 64 p.k
      else if r = .x8 then off p.g (slot ((p.k + 7) / 8) aY) else BitVec.ofNat 64 p.k)
    fun p s ⟨rb, h, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.2.2.1
      · exact h.2.1
      · exact h.2.2.2.1) (by taint_decide)) t7_t8

/-- `sF` into `x9` and back to the outer workspace. -/
theorem ldLeave_ok {D : FD} {mi : BitVec 64} {t : State} (h : In D mi t) :
    WP isa (.block [ldh .x9 sF, leave]) t fun u => u.gpr .x0 = D.B := by
  rw [show [ldh .x9 sF, leave] = [ldh .x9 sF] ++ [leave] from rfl, WP.block_append_iff]
  refine WP.mono (ldF9_ok h.2.1.x0 rfl (h.hlG sF (by decide))) fun u ⟨⟨_, hm⟩, k⟩ => ?_
  exact WP.mono (leave_ok (h.keep hm k (by decide)).2.1) fun _ h => h.1.1

theorem t8_fin1 (p : GkP) (rb : List Byte) (s : State) (h : T8 p rb s) (hd : Dst p s) :
    WP isa (.block [ldh .x9 sF, leave]) s fun t => t.gpr .x0 = p.B ∧
      ∃ rb, WP isa (.block [sth .x9 sF]) t fun u => T9 p rb u ∧ Dst p u := by
  have hw : WP isa (.block ([ldh .x9 sF, leave] ++ [sth .x9 sF])) s fun u => T9 p rb u ∧ Dst p u :=
    WP.mono (t8_t9 p rb s h) fun _ ⟨hu, k⟩ => ⟨hu, hd.keep k⟩
  rw [WP.block_append_iff] at hw
  exact WP.mono (wp_and (ldLeave_ok h.1.choose_spec.1) hw) fun t ⟨h₁, h₂⟩ => ⟨h₁, rb, h₂⟩

theorem flag_ct : RelCT isa (Two (Ex T8)) (.block [ldh .x9 sF, leave, sth .x9 sF]) (Two (Ex T9)) :=
  RelCT.block_append (l₁ := ([ldh .x9 sF, leave] : List Instr)) (l₂ := ([sth .x9 sF] : List Instr)) (RelCT.seq
    (two_piece (Ψ := fun (p : GkP) t => t.gpr .x0 = p.B ∧
        ∃ rb, WP isa (.block [sth .x9 sF]) t fun u => T9 p rb u ∧ Dst p u) [.x0]
      (pins_x0B GkP.g fun (p : GkP) s (h : Ex T8 p s) => by
        obtain ⟨_, ⟨⟨_, hI, _⟩, _⟩, _⟩ := h; exact hI.2.1.x0) (by taint_decide)
      fun p s ⟨rb, h, hd⟩ => t8_fin1 p rb s h hd)
    (two_piece [.x0] (pins_x0B GkP.B fun _ _ h => h.1) (by taint_decide)
      fun p s ⟨_, rb, h⟩ => WP.mono h fun _ h => ⟨rb, h⟩))

theorem q4_fin1 (p : GkP) (rb : List Byte) (s : State) (h : Q4 p rb s) (hd : Dst p s) :
    WP isa (.block [leave]) s fun t => t.gpr .x0 = p.B ∧
      ∃ rb, WP isa (.block [ldh .x3 sF, .logic .and .x .x9 .x9 .x3, sth .x9 sF]) t fun u => T11 p rb u ∧ Dst p u := by
  have hw : WP isa (.block ([leave] ++ ([ldh .x3 sF, .logic .and .x .x9 .x9 .x3, sth .x9 sF] : List Instr))) s
      fun u => T11 p rb u ∧ Dst p u :=
    WP.mono (q4_t11 p rb s h) fun _ ⟨hu, k⟩ => ⟨hu, hd.keep k⟩
  rw [WP.block_append_iff] at hw
  exact WP.mono (wp_and (leave_ok h.1.choose_spec.1.2.1) hw) fun t ⟨⟨⟨h₁, _⟩, _⟩, h₂⟩ => ⟨h₁, rb, h₂⟩

theorem qlast_ct : RelCT isa (Two (Ex Q4)) (.block [leave, ldh .x3 sF, .logic .and .x .x9 .x9 .x3, sth .x9 sF])
    (Two (Ex T11)) :=
  RelCT.block_append (l₁ := ([leave] : List Instr))
    (l₂ := ([ldh .x3 sF, .logic .and .x .x9 .x9 .x3, sth .x9 sF] : List Instr)) (RelCT.seq
    (two_piece (Ψ := fun (p : GkP) t => t.gpr .x0 = p.B ∧
        ∃ rb, WP isa (.block [ldh .x3 sF, .logic .and .x .x9 .x9 .x3, sth .x9 sF]) t fun u => T11 p rb u ∧ Dst p u)
      [.x0] (pins_x0B GkP.g fun (p : GkP) s (h : Ex Q4 p s) => by
        obtain ⟨_, ⟨⟨_, hI, _⟩, _⟩, _⟩ := h; exact hI.2.1.x0) (by taint_decide)
      fun p s ⟨rb, h, hd⟩ => q4_fin1 p rb s h hd)
    (two_piece [.x0] (pins_x0B GkP.B fun _ _ h => h.1) (by taint_decide)
      fun p s ⟨_, rb, h⟩ => WP.mono h fun _ h => ⟨rb, h⟩))

theorem t10_q (p : GkP) (rb : List Byte) (s : State) (h : T10 p rb s) (he : isa.eval (.zero .x .x3) s = some false) :
    p.dl = 3 * p.k :=
  h.1.choose_spec.1.1.q (by rw [t10_eval h] at he; simpa using he)

/-- y's subgroup check. -/
theorem qBr_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (Two fun p s => Ex T10 p s ∧ isa.eval (.zero .x .x3) s = some false) (qBr W M S) (Two (Ex T11)) := by
  simp only [qBr, List.append_assoc, List.cons_append, List.nil_append]
  refine RelCT.seqs_append (by simp [scan]) (by simp) (RelCT.seq (R := Two (Ex Q1))
    (ex_post' (two_map (fun p : GkP => (p.D₀ []).qs)
      (fun p s ⟨⟨rb, h, _⟩, he⟩ => h.1.choose_spec.1.scanPre (t10_q p rb s h he))
      (scan_ct (by taint_decide) (by taint_decide))) fun p rb s h he => t10_q1 p rb s h (t10_q p rb s h he)) ?_)
  refine seqs_cons_ct (by simp [pow]) (RelCT.seq (R := Two (Ex Q2)) (ex_post (two_taint [.x0]
    (pins_x0B GkP.B fun (p : GkP) s (h : Ex Q1 p s) => by
      obtain ⟨_, ⟨⟨_, hP, _⟩, _⟩, _⟩ := h; exact hP.2.2.2.2.2.2) (by taint_decide)) q1_q2) ?_)
  refine RelCT.seqs_append (by simp [pow]) (by simp [isOne, eqArr]) (RelCT.seq (R := Two (Ex Q3))
    (ex_post (two_map GkP.pwY (fun p s ⟨rb, h, _⟩ => q2_pre p rb s h)
      (pow_ct W M S (loadArr_ct (by decide) (by taint_decide) (by taint_decide))
        (expLoop_ct W M S (by taint_decide)) (by taint_decide) (by taint_decide) (by taint_decide))) (q2_q3 W M S)) ?_)
  refine RelCT.seqs_append (by simp [isOne, eqArr]) (by simp) (RelCT.seq (R := Two (Ex Q4))
    (by unfold isOne; exact ex_post (two_map GkP.ws (fun p s ⟨rb, ⟨⟨mi, hM, _⟩, _⟩, _⟩ => hM.inn.goodW1.1)
      (eqArr_ct (by decide) (by decide) (by taint_decide))) q3_q4) ?_)
  rw [seqs_one]
  exact qlast_ct

/-! ## The results masked -/

/-- `maskOut`'s first block. -/
theorem moBlk_ok {t : State} {B ptr : Addr} {k sPtr : Nat} (h0 : t.gpr .x0 = B) (hP : sPtr < 32)
    (hO : word t.mem B (8 * sPtr) = ptr) (hK : word t.mem B (8 * sK) = BitVec.ofNat 64 k)
    (hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8) :
    WP isa (.block [ldh .x1 sPtr, ldh .x2 sK]) t fun u => u.gpr .x1 = ptr ∧ u.gpr .x2 = BitVec.ofNat 64 k :=
  WP.mono (WP.keep [.x1, .x2] (Q := fun u => u.gpr .x1 = ptr ∧ u.gpr .x2 = BitVec.ofNat 64 k)
    (by brun [h0, hdr_enc hP, hdr_enc (show sK < 32 by decide), hl sPtr hP, hl sK (by decide), hO, hK])
    rfl rfl rfl) fun _ h => h.1

/-- `maskOut sPtr`. -/
theorem mo_ct {sPtr : Nat} (ptr : GkP → Addr) (hP : sPtr < 32) {Φ Ψ : GkP → List Byte → State → Prop}
    (hz : ∀ p rb t, Φ p rb t → Fz p t) (hO : ∀ p t, Fz p t → word t.mem p.B (8 * sPtr) = ptr p)
    (hw : ∀ p rb s, Φ p rb s → Dst p s → WP isa (GenerateKey.maskOut sPtr) s fun u => Ψ p rb u ∧ KX s u)
    {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT₁ : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x1 sPtr, ldh .x2 sK]) hc₁).isSome = true)
    (hT₂ : (taint.check (Taint.ofRegs [.x1, .x2])
      (countLoop .x2 [.ldrb .x4 .x1 0, .logic .and .x .x4 .x4 .x15, .strb .x4 .x1 0, .addImm .x .x1 .x1 1])
      hc₂).isSome = true) :
    RelCT isa (Two (Ex Φ)) (GenerateKey.maskOut sPtr) (Two (Ex Ψ)) := by
  have piece : ∀ p t, Ex Φ p t → WP isa (.block [ldh .x1 sPtr, ldh .x2 sK]) t fun u =>
      (u.gpr .x1 = ptr p ∧ u.gpr .x2 = BitVec.ofNat 64 p.k) ∧
      ∃ rb, WP isa (countLoop .x2 [.ldrb .x4 .x1 0, .logic .and .x .x4 .x4 .x15, .strb .x4 .x1 0,
        .addImm .x .x1 .x1 1]) u fun v => Ψ p rb v ∧ Dst p v := fun p t ⟨rb, h, hd⟩ => by
    have z := hz p rb t h
    have hn := z.scr.nowrap
    have hZ := z.hZ
    have hw' := WP.mono (hw p rb t h hd) fun u ⟨hu, k⟩ => (⟨hu, hd.keep k⟩ : Ψ p rb u ∧ Dst p u)
    unfold GenerateKey.maskOut at hw'
    exact WP.mono (wp_and (moBlk_ok z.x0 hP (hO p t z) z.wK fun i hi => z.scr.ld (by omega)) (WP.seq_iff.mp hw'))
      fun u ⟨h₁, h₂⟩ => ⟨h₁, rb, h₂⟩
  unfold GenerateKey.maskOut
  exact RelCT.seq (two_piece [.x0] (pins_x0B GkP.B fun p t (h : Ex Φ p t) => by
      obtain ⟨rb, h, _⟩ := h; exact (hz p rb t h).x0) hT₁ piece)
    (two_post (two_taint [.x1, .x2] (pins_of (fun (p : GkP) r => if r = .x1 then ptr p else
      BitVec.ofNat 64 p.k) fun p s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact h.1.1
        · exact h.1.2) hT₂) fun p t h => by
          obtain ⟨_, rb, h⟩ := h
          exact WP.mono h fun _ h => ⟨rb, h⟩)

/-- The results: the mask, x and y masked, and the status. -/
theorem out_ct : RelCT isa (Two (Ex T11)) (seqs [.block [ldh .x9 sF, movi .x7 0, .sub .x .x15 .x7 .x9],
    GenerateKey.maskOut sX, GenerateKey.maskOut sY,
    .block [ldh .x9 sF, movi .x0 3, .lsl .x .x9 .x9 1, .sub .x .x0 .x0 .x9]]) fun _ _ => True := by
  refine seqs_cons_ct (by simp) (RelCT.seq (R := Two (Ex T12)) (ex_post (two_taint [.x0]
    (pins_x0B GkP.B fun (p : GkP) s (h : Ex T11 p s) => by
      obtain ⟨_, ⟨⟨_, hP, _⟩, _⟩, _⟩ := h; exact hP.2.2.2.2.2.2) (by taint_decide)) t11_t12) ?_)
  refine seqs_cons_ct (by simp) (RelCT.seq (R := Two (Ex T13)) (mo_ct GkP.xp (by decide) (fun _ _ _ h => h.1)
    (fun _ _ h => h.wX) (fun p rb s h hd => t12_t13 p rb s h hd) (by taint_decide) (by taint_decide)) ?_)
  refine seqs_cons_ct (by simp) (RelCT.seq (R := Two (Ex T14)) (mo_ct GkP.yp (by decide) (fun _ _ _ h => h.1)
    (fun _ _ h => h.wY) (fun p rb s h hd => t13_t14 p rb s h hd) (by taint_decide) (by taint_decide)) ?_)
  rw [seqs_one]
  exact two_taint [.x0] (pins_x0B GkP.B fun (p : GkP) s (h : Ex T14 p s) => by
    obtain ⟨_, h, _⟩ := h; exact h.1.x0) (by taint_decide)

theorem tail_eq' (W : Window) (M : Mont) (S : Selector) :
    GenerateKey.tail W.code S.code M.mm = (r2Steps M.mm ++ (.block [leave] :: (GenerateKey.bound ++
      (.block epBlk :: (pow W.code S.code M.mm sG sK sEp sEl ++ range aY))))) ++
        (.block yBlk :: storeBE :: .block [ldh .x9 sF, leave, sth .x9 sF] :: .block qTest ::
          .ite (.zero .x .x3) (.block []) (qBr W M S) :: [.block [ldh .x9 sF, movi .x7 0, .sub .x .x15 .x7 .x9],
            GenerateKey.maskOut sX, GenerateKey.maskOut sY,
            .block [ldh .x9 sF, movi .x0 3, .lsl .x .x9 .x9 1, .sub .x .x0 .x0 .x9]]) := by
  rw [tail_eq]; simp only [List.append_assoc, List.cons_append]

/-- The key's part. -/
theorem tail_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (Two (Ex T0)) (seqs (GenerateKey.tail W.code S.code M.mm)) fun _ _ => True := by
  rw [tail_eq']
  refine RelCT.seqs_append (by simp [r2Steps]) (by simp) (RelCT.seq (r2pow_ct W M S) ?_)
  refine seqs_cons_ct (by simp) (RelCT.seq yBlk_ct ?_)
  refine seqs_cons_ct (by simp) (RelCT.seq store_ct ?_)
  refine seqs_cons_ct (by simp) (RelCT.seq flag_ct ?_)
  refine seqs_cons_ct (by simp) (RelCT.seq (R := Two (Ex T10)) (ex_post (two_taint [.x0]
    (pins_x0B GkP.B fun (p : GkP) s (h : Ex T9 p s) => by
      obtain ⟨_, ⟨⟨_, hP, _⟩, _⟩, _⟩ := h; exact hP.2.2.2.2.2.2) (by taint_decide)) t9_t10) ?_)
  refine seqs_cons_ct (by simp) (RelCT.seq (R := Two (Ex T11)) (two_ite
    (fun p s₁ s₂ ⟨_, h₁, _⟩ ⟨_, h₂, _⟩ => by rw [t10_eval h₁, t10_eval h₂]) ?_ (qBr_ct W M S)) out_ct)
  exact ex_post' (two_taint [] (pins_nil _) (by taint_decide)) fun p rb s h he => t10_t11n p rb s h he

/-! ## The whole function -/

/-- The main part, for a valid p. -/
theorem main_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (Two fun p s => Ex GC p s ∧ isa.eval (.zero .x .x9) s = some false)
      (GenerateKey.main W.code S.code M.mm) fun _ _ => True := by
  rw [main_eq]
  refine RelCT.seqs_append (by simp [pSetup]) (by simp) (RelCT.seq (R := Two (Ex GI))
    (two_post (two_map (fun p : GkP => (⟨p.B, p.Z, p.k, p.dp⟩ : DPub)) (fun p s ⟨⟨rb, h, _⟩, he⟩ =>
      ce_setupP _ s h.1 he) setup_ct) fun p s ⟨⟨rb, h, hd⟩, he⟩ => WP.mono (gc_gi p rb s h he) fun u ⟨hu, k⟩ =>
        ⟨rb, hu, hd.keep k⟩) ?_)
  refine seqs_cons_ct (by simp [GenerateKey.scalar]) (RelCT.seq (R := Two (Ex GP)) (ex_post (two_taint [.x0]
    (pins_x0B GkP.g fun (p : GkP) s (h : Ex GI p s) => by
      obtain ⟨_, ⟨⟨_, hI⟩, _⟩, _⟩ := h; exact hI.2.1.x0) (by taint_decide)) gi_gp) ?_)
  rw [scalar_eq, List.append_assoc]
  refine RelCT.seqs_append (by simp [GenerateKey.bound]) (by simp) (RelCT.seq bound_ct ?_)
  simp only [List.cons_append]
  refine seqs_cons_ct (by simp) (RelCT.seq (R := Two (Ex GB)) (ex_post (two_taint [.x0]
    (pins_x0B GkP.B fun (p : GkP) s (h : Ex GS p s) => by
      obtain ⟨_, ⟨⟨_, hP, _⟩, _⟩, _⟩ := h; exact hP.2.2.2.2.2.2) (by taint_decide)) gs_gb) ?_)
  refine seqs_cons_ct (by simp) (RelCT.seq (R := Two (Ex GX)) (ex_post (two_taint [.x1, .x2, .x10, .x14]
    (pins_of (fun (p : GkP) r => if r = .x1 then p.rp else if r = .x2 then p.xp else if r = .x10 then 0 else
      BitVec.ofNat 64 p.k) fun p s (h : Ex GB p s) r hr => by
        obtain ⟨rb, ⟨⟨_, _, h1, h2, h10, _, _, _, _, h14⟩, _⟩, _⟩ := h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact h1
        · exact h2
        · exact h10
        · exact h14) (by taint_decide)) gb_gx) ?_)
  refine seqs_cons_ct (by simp [Crt.loadArr]) (RelCT.seq (R := Two (Ex G2)) (ex_post (two_taint [.x0]
    (pins_x0B GkP.B fun (p : GkP) s (h : Ex GX p s) => by
      obtain ⟨_, ⟨⟨_, hP⟩, _⟩, _⟩ := h; exact hP.2.2.2.2.2.2) (by taint_decide)) gx_g2) ?_)
  refine RelCT.seqs_append (by simp [Crt.loadArr]) (by simp [CheckPrivate.scalarRange]) (RelCT.seq (R := Two (Ex G3))
    (ex_post (two_map (fun p : GkP => (⟨⟨p.B, p.Z, inner ((p.k + 7) / 8), (p.k + 7) / 8, (p.k + 7) / 8⟩, p.xp,
      p.k⟩ : BPub)) (fun p s ⟨rb, h, _⟩ => g2_lpre p rb s h)
      (loadArr_ct (by decide) (by taint_decide) (by taint_decide))) g2_g3) ?_)
  refine RelCT.seqs_append (by simp [CheckPrivate.scalarRange]) (by simp) (RelCT.seq scalar_ct ?_)
  rw [seqs_one]
  refine two_ite (fun p s₁ s₂ ⟨_, h₁, _⟩ ⟨_, h₂, _⟩ => by rw [g8_eval h₁, g8_eval h₂]) ?_ ?_
  · refine RelCT.seq (R := Two FD') (two_piece [.x0] (pins_x0B GkP.g fun (p : GkP) s
        (h : Ex G8 p s ∧ isa.eval (.zero .x .x9) s = some true) => by
          obtain ⟨⟨_, ⟨⟨_, hI, _⟩, _⟩, _⟩, _⟩ := h; exact hI.2.1.x0) (by taint_decide)
      fun p s ⟨⟨rb, ⟨⟨mi, hI, _⟩, _⟩, hd⟩, _⟩ => WP.mono (leave_ok hI.2.1) fun u ⟨⟨h0, hm⟩, k⟩ =>
        ⟨Fz.of_pa (rb := rb) (hI.pa hm k h0), hd.keep k⟩) fail_ct
  · exact (tail_ct W M S).mono (fun _ _ h => two_mono (fun p s ⟨⟨rb, h, hd⟩, he⟩ => ⟨rb, g8_t0 h he, hd⟩) h)
      fun _ _ h => h

/-- `GenerateKey.code` leaks the same in runs with the same public data. -/
theorem gk_ct (W : Window) (M : Mont) (S : Selector) :
    RelCT isa (Two (Ex' CR)) (GenerateKey.code W.code S.code M.mm) fun _ _ => True := by
  unfold GenerateKey.code
  exact RelCT.seq front_ct (two_ite (fun p s₁ s₂ ⟨_, h₁, _⟩ ⟨_, h₂, _⟩ => by rw [ce_eval h₁.1, ce_eval h₂.1]; rfl)
    (two_taint [] (pins_nil _) (by taint_decide)) (main_ct W M S))

/-- The public data of the second run. -/
theorem cr_pub {s₁ s₂ : State} (h₂ : gkPre s₂) (hp : gkPub s₁ s₂) : CR (gkOf s₁) (gkRand s₂) s₂ := by
  obtain ⟨hr, hsp, ha, hl⟩ := hp
  simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := hr
  rw [stackArgs_three, stackArgs_three] at ha
  simp only [List.cons.injEq, and_true] at ha
  obtain ⟨a0, a1, a2⟩ := ha
  unfold gkLeak at hl
  obtain ⟨hd, hs⟩ := List.append_inj hl (by simp [gkDom, Spec.Rsa.bytesAt, r5])
  have hd' := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hd
  simp only [List.cons.injEq, and_true] at hs
  refine ⟨h₂, hsp.symm, a1.symm, by rw [← a2]; rfl, by rw [← r6]; rfl, by rw [← r5]; rfl, r4.symm, hd'.symm,
    r0.symm, r2.symm, r7.symm, rfl, ?_⟩
  -- Whether the scalar is in range, from the statuses.
  show privateValid (gkA s₁) (gkS s₁) = privateValid (domainOf (gkOf s₁).k (gkOf s₁).dom)
    (scalarOfOctets (domainOf (gkOf s₁).k (gkOf s₁).dom) (gkRand s₂))
  have e : domainOf (gkOf s₁).k (gkOf s₁).dom = gkA s₂ := by
    show domainOf (s₁.gpr .x6).toNat (gkDom s₁) = domainOf (s₂.gpr .x6).toNat (gkDom s₂)
    rw [r6, hd']
  rw [e]
  have e₁ : gkA s₁ = gkA s₂ := by
    show domainOf (s₁.gpr .x6).toNat (gkDom s₁) = domainOf (s₂.gpr .x6).toNat (gkDom s₂)
    rw [r6, hd']
  rw [show gkS s₁ = scalarOfOctets (gkA s₁) (gkRand s₁) from rfl, e₁] at hs ⊢
  rw [show gkS s₂ = scalarOfOctets (gkA s₂) (gkRand s₂) from rfl] at hs
  unfold keyStatus at hs
  generalize privateValid _ (scalarOfOctets (gkA s₂) (gkRand s₁)) = b₁ at hs ⊢
  generalize privateValid _ (scalarOfOctets (gkA s₂) (gkRand s₂)) = b₂ at hs ⊢
  cases b₁ <;> cases b₂ <;> simp at hs ⊢ <;> split at hs <;> simp at hs

/-- `vg_ffdh_generate_key` is constant time. -/
theorem gk_constantTime (W : Window) (M : Mont) (S : Selector) :
    ConstantTime isa gkContract.pre gkContract.pub (GenerateKey.code W.code S.code M.mm) :=
  RelCT.constantTime ((gk_ct W M S).mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ =>
    ⟨gkOf s₁, ⟨gkRand s₁, cr_of s₁ h₁⟩, ⟨gkRand s₂, cr_pub h₂ hp⟩, hp.2.1⟩) fun _ _ h => h)

end VG.Proof.Ffdh.AArch64.GenerateKey

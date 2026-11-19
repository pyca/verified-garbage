module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Stages
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.LadPow
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.LadderP
public import VerifiedGarbage.Impl.Ecdh.PPC64LE
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Spec.Ecdh
import VerifiedGarbage.Proof.Ecdh.Exchange
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.EcKey.PPC64LE.Finish
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Setup
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Flags
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.SlotOps
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.BytesLen
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Pow
import VerifiedGarbage.Proof.Weierstrass.BytesLen
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Copy
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Layout
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Ecdh.PPC64LE.Peer`, which this module and modules that import it used -/

section

/-!
# ECDH on PPC64LE: reading and checking the peer's key

As on 32-bit ARM (`Proof/Ecdh/Arm/Peer.lean`): `checkLtP_ok`,
`checkZero_ok` and `checkLead_ok` and the flag's masks they and, and
`peer_ok`: `peerAt q` stores `R² mod p` and `b R mod p`, reads the `x` and
`y` of the key `q` points to into their slots, and ands into the flag the
masks of the key's first byte being `04`, `x < p` and `y < p`.
-/

@[expose] public section

namespace VG.Proof.Ecdh.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Spec.Weierstrass

/-! ## Below `p` -/

/-- `checkLtP a`: the flag `&=` the mask of `[a] < [MP]`. -/
theorem checkLtP_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Ws s base size)
    (h3 : At s base .r3 0) {a : Nat} (ha : a + 8 * c.n ≤ size) (hm : c.sl MP + 8 * c.n ≤ size)
    (hF : c.sl FLAG + 8 ≤ size) :
    WP isa (.block (Impl.Ecdh.PPC64LE.Cfg.checkLtP c a)) s fun s' =>
      flagW c base s' = flagW c base s &&&
        mask64 (wordsVal s.mem base a c.n < wordsVal s.mem base (c.sl MP) c.n) ∧
      Kp [.r0, .r4, .r5, .r6, .r7, .r8] s s' ∧ Outside base (c.sl FLAG) 8 s.mem s'.mem := by
  have hnw := hs.nowrap
  rw [Impl.Ecdh.PPC64LE.Cfg.checkLtP]
  refine wp_append (WP.mono (ltM_ok c hs h3 ha hm) fun s₁ ⟨g₁, K₁, m₁⟩ => ?_)
  refine WP.mono (andFlag_ok c (K₁.ws hs) (K₁.at h3) hF) fun s' ⟨f', k', m'⟩ =>
    ⟨?_, (K₁.mono (by decide)).trans (k'.mono (by decide)), ?_⟩
  · rw [f', g₁]; simp only [flagW, m₁]
  · rw [m', m₁]; exact writeW_outside _ _ _ (by omega_arith)

/-! ## Zero -/

theorem mask_not (P : Prop) [Decidable P] : BitVec.ofNat 64 0 - mask64 P - BitVec.ofNat 64 1 = mask64 ¬P := by
  by_cases h : P <;> simp only [mask64, h, not_true, not_false_eq_true, ite_true, ite_false] <;> decide

/-- `checkZero a`: the flag `&=` the mask of `[a] = 0`. -/
theorem checkZero_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Ws s base size)
    (h3 : At s base .r3 0) {a : Nat} (ha4 : a % 4 = 0) (hn : 0 < c.n) (ha : a + 8 * c.n ≤ size)
    (hF : c.sl FLAG + 8 ≤ size) :
    WP isa (.block (Impl.Ecdh.PPC64LE.Cfg.checkZero c a)) s fun s' =>
      flagW c base s' = flagW c base s &&& mask64 (wordsVal s.mem base a c.n = 0) ∧
      Kp [.r4, .r5] s s' ∧ Outside base (c.sl FLAG) 8 s.mem s'.mem := by
  have hnw := hs.nowrap
  rw [Impl.Ecdh.PPC64LE.Cfg.checkZero, List.append_assoc]
  refine wp_append (WP.mono (nonzero_ok c hs h3 ha4 hn ha) fun s₁ ⟨g₁, K₁, m₁⟩ => ?_)
  simp only [List.cons_append, List.nil_append]
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_sub ?_
  refine wp_step (exec_subi (by decide) (by decide)) ?_
  refine WP.mono (andFlag_ok c (((K₁.ws hs).write _ _ |>.write _ _).write _ _)
    ((((K₁.at h3).write _).write _).write _) hF) fun s' ⟨f', k', m'⟩ =>
    ⟨?_, (((K₁.trans (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans
      (Kp.write _ _ (by decide))).trans (k'.mono (by decide)), ?_⟩
  · rw [f']
    simp only [write_gpr, write_mem, ite_true, reduceCtorEq, ite_false, g₁, m₁, mask_not, flagW]
    simp only [ne_eq, Decidable.not_not]
  · rw [m']; simp only [write_mem, m₁]; exact writeW_outside _ _ _ (by omega_arith)

/-! ## The first byte -/

/-- `-(((b ^ 4) - 1) >>> 63)` is the mask of `b = 4`, for a byte `b`. -/
theorem lead_mask (b : BitVec 8) :
    BitVec.ofNat 64 0 - ((b.setWidth 64 ^^^ BitVec.ofNat 64 4) - BitVec.ofNat 64 1) >>> 63 = mask64 (b = 4) := by
  revert b; decide +kernel

/-- `checkLead q`: the flag `&=` the mask of the byte `q` points to being `04`. -/
theorem checkLead_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Ws s base size)
    (h3 : At s base .r3 0) {q : Reg} (hq0 : q ≠ .r0)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr q) 1) (hF : c.sl FLAG + 8 ≤ size) :
    WP isa (.block (Impl.Ecdh.PPC64LE.Cfg.checkLead c q)) s fun s' =>
      flagW c base s' = flagW c base s &&& mask64 (s.mem (s.gpr q) = 4) ∧
      Kp [.r4, .r5, .r7] s s' ∧ Outside base (c.sl FLAG) 8 s.mem s'.mem := by
  have hnw := hs.nowrap
  simp only [Impl.Ecdh.PPC64LE.Cfg.checkLead, List.cons_append, List.nil_append]
  refine wp_step (exec_lbz hq0 (by decide) (by rw [BitVec.add_zero]; exact hin)) ?_
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_logic ?_
  refine wp_step (exec_subi (by decide) (by decide)) ?_
  refine wp_step (exec_lsr_d (by decide)) ?_
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_sub ?_
  refine WP.mono (andFlag_ok c ((((((hs.write _ _).write _ _).write _ _).write _ _).write _ _).write _ _ |>.write _ _)
    (((((((h3.write _).write _).write _).write _).write _).write _).write _) hF) fun s' ⟨f', k', m'⟩ =>
    ⟨?_, (((((((Kp.write _ _ (by decide)).trans (Kp.write _ _ (by decide))).trans
      (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans
      (Kp.write _ _ (by decide))).trans (Kp.write _ _ (by decide))).trans (k'.mono (by decide)), ?_⟩
  · rw [f']
    simp only [write_gpr, write_mem, ite_true, reduceCtorEq, ite_false, BitVec.add_zero, read_one, flagW]
    rw [lead_mask]
  · rw [m']; simp only [write_mem]; exact writeW_outside _ _ _ (by omega_arith)

/-!
## Reading the peer's key

`peerAt q` stores `R² mod p` and `b R mod p`, reads the `x` and `y` of the
key `q` points to into their slots (through `r6`, from its byte 1), and ands
into the flag the masks of the peer's first byte being `04`, `x < p` and
`y < p` (`peer_ok`). It writes only those slots and the flag, in the working
space, which the peer's key is apart from.
-/

variable {c : Cfg}

open VG.Impl.Ecdh.PPC64LE (QY R2P BP)

theorem peer_eq (c : Cfg) (q : Reg) : Impl.Ecdh.PPC64LE.Cfg.peerAt c q =
    (Impl.Ecdh.PPC64LE.Cfg.consts c).flatMap (fun (i, x) => VG.Impl.Mont.PPC64LE.setConst c.n (c.sl i) x) ++
    (.addi .r6 q 1 :: (loadBytes c.C.len c.n (c.sl E) .r6 ++
    (.addi .r6 .r6 c.C.len :: (loadBytes c.C.len c.n (c.sl QY) .r6 ++
    (Impl.Ecdh.PPC64LE.Cfg.checkLead c q ++
    (Impl.Ecdh.PPC64LE.Cfg.checkLtP c (c.sl E) ++ Impl.Ecdh.PPC64LE.Cfg.checkLtP c (c.sl QY))))))) := by
  simp only [Impl.Ecdh.PPC64LE.Cfg.peerAt, List.append_assoc, List.cons_append, List.nil_append]

/-- The registers `peerAt` writes. -/
abbrev peerClob : List Reg := [.r0, .r4, .r5, .r6, .r7, .r8, .r9, .r11]

/-- The constants, the key's `x` and `y`, and the checks of its first byte,
`x` and `y`, for a key that `q` points to. -/
theorem peer_ok (hc : CfgOk c) {base : Addr} {s : State} (hw : WsReg s base) {q : Reg}
    (hq : q ∉ peerClob) (hqfit : (s.gpr q).toNat + (1 + 2 * c.C.len) ≤ 2 ^ 64)
    (hin : (⟨s.gpr q, 1 + 2 * c.C.len⟩ : Region) ∈ s.rd ++ s.wr)
    (hd : Region.Disjoint ⟨s.gpr q, 1 + 2 * c.C.len⟩ ⟨base, size⟩) (hmp : sv c base s MP = c.C.p) :
    WP isa (.block (Impl.Ecdh.PPC64LE.Cfg.peerAt c q)) s fun s' =>
      WsReg s' base ∧ Kp peerClob s s' ∧
      Unch base (slW c [R2P, BP, E, QY] ++ [(c.sl FLAG, 8)]) s.mem s'.mem ∧
      sv c base s' R2P = c.R * c.R % c.C.p ∧ sv c base s' BP = c.mont c.C.b ∧
      sv c base s' E = ofBytes (Spec.Ecdsa.bytesAt s.mem (s.gpr q + BitVec.ofNat 64 1) c.C.len) ∧
      sv c base s' QY =
        ofBytes (Spec.Ecdsa.bytesAt s.mem (s.gpr q + BitVec.ofNat 64 (1 + c.C.len)) c.C.len) ∧
      flagW c base s' = flagW c base s &&& mask64 (s.mem (s.gpr q) = 4) &&&
        mask64 (sv c base s' E < c.C.p) &&& mask64 (sv c base s' QY < c.C.p) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hw.nowrap
  have hsz : size = 8192 := rfl
  have hpl := hc.p_lt
  have hp3 := hc.p_ge
  have hl8 := hc.len8
  have hlhi := hc.len_hi
  obtain hF : c.sl FLAG + 8 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega_arith
  obtain hR2 := sl_le c h7 (i := R2P) (by decide)
  obtain hB := sl_le c h7 (i := BP) (by decide)
  obtain hY := sl_le c h7 (i := QY) (by decide)
  obtain hE := sl_le c h7 (i := E) (by decide)
  obtain hM := sl_le c h7 (i := MP) (by decide)
  simp only [peerClob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
  obtain ⟨hq0, hq4, hq5, hq6, hq7, hq8, hq9, hq11⟩ := hq
  generalize hqa : s.gpr q = qa at hqfit hin hd ⊢
  rw [peer_eq]
  -- The constants.
  refine wp_append (WP.mono (setupConsts_ok hc (Impl.Ecdh.PPC64LE.Cfg.consts c) hw (fun ix hix => by
      simp only [Impl.Ecdh.PPC64LE.Cfg.consts, List.mem_cons, List.not_mem_nil, or_false] at hix
      rcases hix with rfl | rfl
      · exact ⟨show R2P < 45 by decide, Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) hpl⟩
      · exact ⟨show BP < 45 by decide, Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) hpl⟩)
      (show [R2P, BP].Nodup by decide))
    fun s₁ ⟨e₁, k₁, U₁⟩ => ?_)
  obtain hw₁ := hw.of_kp k₁
  have U₁' : Unch base (slW c [R2P, BP]) s.mem s₁.mem := U₁
  -- `peer + 1`
  refine wp_step (exec_addi hq0 (by decide)) ?_
  obtain k₂ : Kp [.r6, .r11] s (s₁.write .r6 (s₁.gpr q + BitVec.ofNat 64 1)) :=
    (k₁.mono (by decide)).trans (Kp.write _ _ (by decide))
  obtain hq₁ : s₁.gpr q = qa := by rw [k₁.gpr q (by simp [hq11]), hqa]
  obtain hrw : ∀ {t : State} {rs : List Reg}, Kp rs s t → t.rd ++ t.wr = s.rd ++ s.wr := fun K => by
    rw [K.rd, K.wr]
  obtain O₁ : Outside base 0 4096 s.mem s₁.mem := U₁'.outside fun w hw => by
    simp only [slW, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl <;> exact ⟨Nat.zero_le _, by dsimp only; omega_arith⟩
  obtain hfit₁ : (qa + BitVec.ofNat 64 1).toNat + c.C.len ≤ 2 ^ 64 := by
    rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (show 1 < 2 ^ 64 by decide), Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  -- `x`
  refine wp_append (WP.mono (setupLoad_ok hc (s := s) (i := E) (src := .r6) (p := qa + BitVec.ofNat 64 1)
    (hw₁.of_kp (Kp.write _ (d := .r6) (rs := [.r6]) _ (by decide))) (by decide) (by decide)
    (by simp only [write_gpr, ite_true, hq₁]) hfit₁
    (fun e he => ⟨_, by rw [hrw k₂]; exact hin, by
      rw [Offset.add_add]; exact Offset.contains_base qa (by omega_arith) (by omega_arith)⟩)
    (hd.sub_left (Offset.sub_base qa (by omega_arith))) (by simp only [write_mem]; exact O₁))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_)
  obtain K₃ : Kp [.r6, .r8, .r9, .r11] s s₃ :=
    (k₂.mono (by decide)).trans (k₃.mono (by decide))
  obtain hw₃ := hw.of_kp K₃
  obtain r6₃ : s₃.gpr .r6 = qa + BitVec.ofNat 64 1 := by
    rw [k₃.gpr _ (by decide)]; simp only [write_gpr, ite_true, hq₁]
  -- `peer + 1 + len`
  refine wp_step (exec_addi (by decide) (show c.C.len < 2 ^ 15 by omega_arith)) ?_
  obtain K₄ : Kp [.r6, .r8, .r9, .r11] s (s₃.write .r6 (s₃.gpr .r6 + BitVec.ofNat 64 c.C.len)) :=
    K₃.trans (Kp.write _ _ (by decide))
  obtain hfit₂ : (qa + BitVec.ofNat 64 (1 + c.C.len)).toNat + c.C.len ≤ 2 ^ 64 := by
    rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (show 1 + c.C.len < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  obtain O₃' : Outside base 0 4096 s.mem s₃.mem :=
    O₁.trans (O₃.mono (Nat.zero_le _) (by omega_arith))
  -- `y`
  refine wp_append (WP.mono (setupLoad_ok hc (s := s) (i := QY) (src := .r6)
    (p := qa + BitVec.ofNat 64 (1 + c.C.len))
    (hw₃.of_kp (Kp.write _ (d := .r6) (rs := [.r6]) _ (by decide))) (by decide) (by decide)
    (by simp only [write_gpr, ite_true, r6₃]; exact Offset.add_add _ _ _) hfit₂
    (fun e he => ⟨_, by rw [hrw K₄]; exact hin, by
      rw [Offset.add_add]; exact Offset.contains_base qa (by omega_arith) (by omega_arith)⟩)
    (hd.sub_left (Offset.sub_base qa (by omega_arith))) (by simp only [write_mem]; exact O₃'))
    fun s₅ ⟨e₅, k₅, O₅⟩ => ?_)
  obtain K₅ : Kp [.r6, .r8, .r9, .r11] s s₅ := K₄.trans (k₅.mono (by decide))
  obtain hw₅ := hw.of_kp K₅
  obtain hq₅ : s₅.gpr q = qa := by rw [K₅.gpr q (by simp [hq6, hq8, hq9, hq11]), hqa]
  obtain O₅' : Outside base 0 size s.mem s₅.mem :=
    (O₃'.mono (Nat.le_refl _) (by omega_arith)).trans (O₅.mono (Nat.zero_le _) (by omega_arith))
  -- the first byte
  refine wp_append (WP.mono (checkLead_ok c hw₅.ws hw₅.at3 (q := q) hq0
    ⟨_, by rw [hrw K₅]; exact hin, by
      have := Offset.contains_base qa (d := 0) (n := 1) (k := 1 + 2 * c.C.len) (by omega_arith) (by omega_arith)
      rw [BitVec.add_zero] at this; rw [hq₅]; exact this⟩ hF) fun s₆ ⟨f₆, k₆, O₆⟩ => ?_)
  rw [hq₅] at f₆
  obtain hw₆ := hw₅.of_kp k₆
  -- `x < p`
  refine wp_append (WP.mono (checkLtP_ok c hw₆.ws hw₆.at3 (by omega_arith) (by omega_arith) hF) fun s₇ ⟨f₇, k₇, O₇⟩ => ?_)
  obtain hw₇ := hw₆.of_kp k₇
  -- `y < p`
  refine WP.mono (checkLtP_ok c hw₇.ws hw₇.at3 (by omega_arith) (by omega_arith) hF) fun s₈ ⟨f₈, k₈, O₈⟩ => ?_
  -- The slots.
  obtain UF : Unch base ([(c.sl FLAG, 8)] ++ [(c.sl FLAG, 8)] ++ [(c.sl FLAG, 8)]) s₅.mem s₈.mem :=
    (O₆.unch.trans O₇.unch).trans O₈.unch
  obtain apF : ∀ {i}, i < 45 → i ≠ FLAG →
      ∀ w ∈ [(c.sl FLAG, 8)] ++ [(c.sl FLAG, 8)] ++ [(c.sl FLAG, 8)],
        c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := fun hi hf =>
    apart_append (apart_append (apart_flag h0 hf) (apart_flag h0 hf)) (apart_flag h0 hf)
  obtain v₈ : ∀ {i}, i < 45 → i ≠ FLAG → sv c base s₈ i = sv c base s₅ i := fun hi hf =>
    sv_unch UF h7 hn hi (apF hi hf)
  obtain U₁₅ : Unch base [(c.sl E, 8 * c.n), (c.sl QY, 8 * c.n)] s₁.mem s₅.mem := O₃.unch.trans O₅.unch
  obtain v₅ : ∀ {i}, i < 45 → i ∉ [E, QY] → sv c base s₅ i = sv c base s₁ i := fun hi hl =>
    sv_unch U₁₅ h7 hn hi (apart_slW (c := c) (l := [E, QY]) hl)
  obtain v₁ : ∀ {i}, i < 45 → i ∉ [R2P, BP] → sv c base s₁ i = sv c base s i := fun hi hl =>
    sv_unch U₁' h7 hn hi (apart_slW (c := c) (l := [R2P, BP]) hl)
  obtain xE : sv c base s₈ E = ofBytes (Spec.Ecdsa.bytesAt s.mem (qa + BitVec.ofNat 64 1) c.C.len) := by
    rw [v₈ (by decide) (by decide), ← e₃]
    exact sv_unch O₅.unch h7 hn (i := E) (by decide) (apart_slW (c := c) (l := [QY]) (by decide))
  obtain yQ : sv c base s₈ QY =
      ofBytes (Spec.Ecdsa.bytesAt s.mem (qa + BitVec.ofNat 64 (1 + c.C.len)) c.C.len) := by
    rw [v₈ (by decide) (by decide)]; exact e₅
  refine ⟨hw₇.of_kp k₈, ?_, ?_, ?_, ?_, xE, yQ, ?_⟩
  · exact (((K₅.mono (by decide)).trans (k₆.mono (by decide))).trans (k₇.mono (by decide))).trans
      (k₈.mono (by decide))
  · have U := ((U₁'.trans U₁₅).trans UF)
    refine U.mono fun w hw => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.map_cons, List.map_nil, slW] at hw ⊢
    grind
  · rw [v₈ (by decide) (by decide), v₅ (by decide) (by decide)]
    exact e₁ (R2P, c.R * c.R % c.C.p) List.mem_cons_self
  · rw [v₈ (by decide) (by decide), v₅ (by decide) (by decide)]
    exact e₁ (BP, c.mont c.C.b) (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  · have mp₅ : sv c base s₅ MP = c.C.p := by
      rw [v₅ (by decide) (by decide), v₁ (by decide) (by decide)]; exact hmp
    obtain mp₆ : wordsVal s₆.mem base (c.sl MP) c.n = c.C.p :=
      (sv_unch O₆.unch h7 hn (i := MP) (by decide) (apart_flag h0 (by decide))).trans mp₅
    obtain mp₇ : wordsVal s₇.mem base (c.sl MP) c.n = c.C.p :=
      (sv_unch O₇.unch h7 hn (i := MP) (by decide) (apart_flag h0 (by decide))).trans mp₆
    obtain e₆ : wordsVal s₆.mem base (c.sl E) c.n = sv c base s₈ E :=
      ((sv_unch O₆.unch h7 hn (i := E) (by decide) (apart_flag h0 (by decide))).trans
        (v₈ (by decide) (by decide)).symm)
    obtain y₇ : wordsVal s₇.mem base (c.sl QY) c.n = sv c base s₈ QY :=
      (sv_unch O₈.unch h7 hn (i := QY) (by decide) (apart_flag h0 (by decide))).symm
    obtain hFl := sl_le c h7 (i := FLAG) (by decide)
    obtain fl₅ : flagW c base s₅ = flagW c base s := by
      obtain ap : ∀ w ∈ slW c [R2P, BP] ++ [(c.sl E, 8 * c.n), (c.sl QY, 8 * c.n)],
          c.sl FLAG + 8 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG := fun w hw =>
        (apart_slW (c := c) (l := [R2P, BP, E, QY]) (i := FLAG) (by decide) w (by
          simp only [slW, List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil,
            or_false] at hw ⊢; grind)).imp (fun h => by omega_arith) id
      exact (U₁'.trans U₁₅).word ap (by omega_arith)
    obtain lead₅ : s₅.mem qa = s.mem qa := by
      have := keep_of_disjoint' O₅' hd (by omega_arith) (i := 0) (by omega_arith) (by omega_arith)
      rwa [BitVec.add_zero] at this
    rw [f₈, f₇, f₆, fl₅, lead₅, e₆, mp₆, y₇, mp₇]

end VG.Proof.Ecdh.PPC64LE

end

end

/-! ### `Ecdh.PPC64LE.Validate`, which this module and modules that import it used -/

section

/-!
# ECDH on PPC64LE: checking the peer's point

As on 32-bit ARM (`Proof/Ecdh/Arm/Validate.lean`): `mont_ok` puts the
peer's `x` and `y` into Montgomery's form, `curve_ok` computes
`y² - (x³ + a x + b)`, zero iff the point is on the curve, `select_ok` puts
the peer's point, or `G` if the flag is clear, where the ladder takes its
point from, and `validate_ok` is the three, with the mask of the curve's
equation anded into the flag.
-/

@[expose] public section

namespace VG.Proof.Ecdh.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Spec.Weierstrass
open VG.Impl.Ecdh.PPC64LE (QY R2P BP QXM QYM W0 W1 W2 W3 PX PY)

variable {c : Cfg}

/-! ## Montgomery's form -/

/-- What the two multiplications by `R² mod p` leave. -/
structure MontPost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  ws : WsReg s' base
  rk : Rk fnClob s s'
  unch : Unch base (callW c QXM ++ callW c QYM) s.mem s'.mem
  x_lt : sv c base s' QXM < c.C.p
  x : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' QXM) = Fin.ofNat c.C.p (sv c base s E)
  y_lt : sv c base s' QYM < c.C.p
  y : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' QYM) = Fin.ofNat c.C.p (sv c base s QY)

theorem mont_ok (hc : CfgOk c) {base : Addr} {s : State} (hw : WsReg s base)
    (hr2 : sv c base s R2P = c.R * c.R % c.C.p)
    {rest : Prog isa} {Q : State → Prop} (h : ∀ s', MontPost c base s s' → WP isa rest s' Q) :
    WP isa (.seq (mulCall c.SP (c.sl QXM) (c.sl E) (c.sl R2P))
      (.seq (mulCall c.SP (c.sl QYM) (c.sl QY) (c.sl R2P)) rest)) s Q := by
  have h7 := hc.n10
  have hn := hw.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hr2' : sv c base s R2P = 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.p := hr2
  refine WP.seq (WP.mono (slMul_ok hc.fp hc.fpk hc.fpm h7 hw (o := QXM) (a := E) (b := R2P) (by decide)
    (by decide) (by decide) (by rw [hr2']; exact Nat.mod_lt _ (by omega_arith))) fun s₁ ⟨k₁, U₁, lt₁, e₁⟩ => ?_)
  have hw₁ := hw.of_rk k₁
  have v₁ : ∀ {i}, i < 45 → i ≠ QXM → sv c base s₁ i = sv c base s i := fun hi h₁ =>
    sv_unch U₁ h7 hn hi (apart_callW h7 hi h₁)
  refine WP.seq (WP.mono (slMul_ok hc.fp hc.fpk hc.fpm h7 hw₁ (o := QYM) (a := QY) (b := R2P) (by decide)
    (by decide) (by decide) (by rw [v₁ (by decide) (by decide), hr2']; exact Nat.mod_lt _ (by omega_arith)))
    fun s₂ ⟨k₂, U₂, lt₂, e₂⟩ => h s₂ ?_)
  have x₂ : sv c base s₂ QXM = sv c base s₁ QXM := sv_unch U₂ h7 hn (by decide) (apart_callW h7 (by decide) (by decide))
  refine ⟨hw₁.of_rk k₂, k₁.trans k₂, U₁.trans U₂, by rw [x₂]; exact lt₁, ?_, lt₂, ?_⟩
  · rw [x₂]; exact toM_r2 hpR (by rw [e₁, hr2'])
  · exact toM_r2 hpR (by rw [e₂, v₁ (i := R2P) (by decide) (by decide), v₁ (i := QY) (by decide) (by decide), hr2'])

/-! ## The curve's equation -/

/-- `curveOps` on slot numbers. -/
def curveN : List FOp :=
  [.mul W0 QYM QYM, .mul W1 QXM QXM, .mul W2 W1 QXM, .mul W1 AP QXM, .add W3 W2 W1,
    .add W2 W3 BP, .sub W1 W0 W2]

theorem curveOps_eq (c : Cfg) : fprog c.SP (Impl.Ecdh.PPC64LE.Cfg.curveOps c) = Point.fprogR c.sl c.SP curveN := rfl

theorem curveN_run {F : Type _} [Lean.Grind.CommRing F] (e : Nat → F) :
    runOps curveN e W1 = e QYM * e QYM - ((e QXM * e QXM * e QXM + e AP * e QXM) + e BP) := by
  simp only [curveN, runOps_cons, runOps_nil, FOp.run, Function.update_apply]
  simp only [W0, W1, W2, W3, QYM, QXM, AP, BP, KM, TT, SM, RM, XM, X, EM, Nat.reduceEqDiff, ↓reduceIte]

theorem curveN_reads : readsOk curveN [QXM, QYM, AP, BP] = true := by decide

theorem curveN_ids : ∀ op ∈ curveN, op.out ∈ [W0, W1, W2, W3] ∧ ∀ x ∈ op.out :: op.ins, x < 45 := by decide

/-- The slots `curveN` writes are apart from every other. -/
theorem curveLay (h7 : c.n < 10) : Point.LayR c.n 45 [W0, W1, W2, W3] c.sl where
  le := fun _ hx => sl_below_own c h7 hx
  apart := fun _ _ _ _ hxw => sl_apart c hxw

/-- `curveN` over any modulus `S` of `c.n` words, `m`. -/
theorem curve_core {S : Impl.Weierstrass.Mont.Modulus} {m : Nat} [NeZero m] (hkS : S.k = c.n) (hmS : S.m = m)
    (hM : ModOk c.n m) (h7 : c.n < 10) (hm : UnitMod m (2 ^ (64 * c.n))) {base : Addr} {s : State}
    (hw : WsReg s base) (hlt : ∀ x ∈ [QXM, QYM, AP, BP], sv c base s x < m) :
    WP isa (Point.fprogR c.sl S curveN) s fun s' =>
      Point.KeepR c.n c.sl base (curveN.map FOp.out) s s' ∧
      Point.InvR c.n 45 c.sl base m (validAfter curveN [QXM, QYM, AP, BP])
        (runOps curveN fun x => toM m (2 ^ (64 * c.n)) (sv c base s x)) s' := by
  obtain ⟨cv, w, m', k', d⟩ := S
  dsimp only at hkS hmS
  subst hkS hmS
  exact Point.fprogR_ok (S := ⟨cv, w, m', c.n, d⟩) hM rfl (curveLay h7) hm curveN
    ⟨hw, by decide, hlt, fun _ _ => rfl⟩ curveN_ids curveN_reads

/-- `y² = x³ + a x + b`, in `Fin p`. -/
abbrev OnCurve (c : Cfg) (x y : Fe c.C) : Prop :=
  y * y - ((x * x * x + Fin.ofNat c.C.p c.C.a * x) + Fin.ofNat c.C.p c.C.b) = 0

/-- `y² - (x³ + a x + b)` to `W1`, zero iff the point is on the curve. -/
theorem curve_ok (hc : CfgOk c) {base : Addr} {s : State} (hw : WsReg s base)
    (hx : sv c base s QXM < c.C.p) (hy : sv c base s QYM < c.C.p)
    (hap : sv c base s AP = c.mont c.C.a) (hbp : sv c base s BP = c.mont c.C.b) :
    WP isa (fprog c.SP (Impl.Ecdh.PPC64LE.Cfg.curveOps c)) s fun s' =>
      WsReg s' base ∧ Rk fnClob s s' ∧ Unch base (slW c [W0, W1, W2, W3] ++ [(own c.n, 64 * c.n)]) s.mem s'.mem ∧
      (sv c base s' W1 = 0 ↔ OnCurve c (toM c.C.p (2 ^ (64 * c.n)) (sv c base s QXM))
        (toM c.C.p (2 ^ (64 * c.n)) (sv c base s QYM))) := by
  have h7 := hc.n10
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_arith)
  have hM : ModOk c.n c.C.p := by have := hc.fp; rw [hc.fpk, hc.fpm] at this; exact this
  rw [curveOps_eq]
  refine WP.mono (curve_core hc.fpk hc.fpm hM h7 hpR hw (fun x hx' => ?_)) fun s' ⟨K, I⟩ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
    rcases hx' with rfl | rfl | rfl | rfl
    · exact hx
    · exact hy
    · rw [hap]; exact hmont _
    · rw [hbp]; exact hmont _
  have hW1 : W1 ∈ validAfter curveN [QXM, QYM, AP, BP] := by decide
  have v := I.val W1 hW1
  have lt := I.lt W1 hW1
  rw [curveN_run] at v
  refine ⟨I.ws, ⟨K.gpr, K.rd, K.wr, K.sp⟩, (K.mem : Unch _ _ _ _).mono fun w hw' => ?_, ?_⟩
  · simp only [curveN, List.map_cons, List.map_nil, FOp.out, slW, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hw' ⊢
    grind
  · rw [← toM_eq_zero_iff hpR lt, v]
    show _ * _ - ((_ * _ * _ + toM _ _ (sv c base s AP) * _) + toM _ _ (sv c base s BP)) = 0 ↔ _
    rw [hap, hbp, toM_cmont hc, toM_cmont hc]

/-! ## The point for the ladder -/

theorem select_eq (c : Cfg) : Impl.Ecdh.PPC64LE.Cfg.select c =
    .load .d .r10 wb (c.sl FLAG) ::
    (sel c.n (c.sl PX) (c.sl GX) (c.sl QXM) ++ sel c.n (c.sl PY) (c.sl GY) (c.sl QYM)) := by
  simp only [Impl.Ecdh.PPC64LE.Cfg.select, List.cons_append, List.nil_append]

theorem select_ok (hc : CfgOk c) {base : Addr} {s : State} (hw : WsReg s base) {P : Prop} [Decidable P]
    (hf : flagW c base s = mask64 P) :
    WP isa (.block (Impl.Ecdh.PPC64LE.Cfg.select c)) s fun s' =>
      WsReg s' base ∧ Kp [.r4, .r5, .r10] s s' ∧ Unch base (slW c [PX, PY]) s.mem s'.mem ∧
      sv c base s' PX = (if P then sv c base s QXM else sv c base s GX) ∧
      sv c base s' PY = (if P then sv c base s QYM else sv c base s GY) := by
  have h7 := hc.n10
  have hn := hw.nowrap
  have hsz : size = 8192 := rfl
  have hap : ∀ {i j}, i ≠ j → c.sl i ≤ c.sl j ∨ c.sl j + 8 * c.n ≤ c.sl i := fun h => by
    have := sl_apart c h; omega_arith
  have hle : ∀ {i}, i < 45 → c.sl i + 8 * c.n ≤ size := fun hi => by
    have := sl_le c h7 hi; omega_arith
  rw [select_eq]
  have hF := sl_le c h7 (i := FLAG) (by decide)
  refine wp_step (ld0_ok hw.ws hw.at3 (by decide) (sl_al c FLAG) (by omega_arith)) ?_
  have hc₁ : (s.write .r10 (word s.mem base (c.sl FLAG))).gpr .r10 = if decide P then BitVec.allOnes 64 else 0 := by
    simp only [write_gpr, ite_true]; rw [← flagW, hf]; simp only [mask64, decide_eq_true_eq]
  have hs₁ := hw.ws.write .r10 (word s.mem base (c.sl FLAG))
  have h3₁ := hw.at3.write (d := .r10) (word s.mem base (c.sl FLAG))
  refine wp_append (WP.mono (sel_ok (decide P) c.n hs₁ h3₁ hc₁ (sl_al c _) (sl_al c _) (sl_al c _)
    (hle (i := PX) (by decide)) (hle (i := GX) (by decide)) (hle (i := QXM) (by decide)) (hap (by decide))
    (hap (by decide))) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_)
  have hc₂ : s₂.gpr .r10 = if decide P then BitVec.allOnes 64 else 0 := by rw [k₂.gpr _ (by decide), hc₁]
  refine WP.mono (sel_ok (decide P) c.n (k₂.ws hs₁) (k₂.at h3₁) hc₂ (sl_al c _) (sl_al c _) (sl_al c _)
    (hle (i := PY) (by decide)) (hle (i := GY) (by decide)) (hle (i := QYM) (by decide)) (hap (by decide))
    (hap (by decide))) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have K₃ : Kp [.r4, .r5, .r10] s s₃ :=
    ((Kp.write _ _ (by decide)).trans (k₂.mono (by decide))).trans (k₃.mono (by decide))
  refine ⟨hw.of_kp K₃, K₃, ?_, ?_, ?_⟩
  · have := O₂.unch.trans O₃.unch
    exact this
  · show wordsVal s₃.mem _ _ _ = _
    rw [sv_unch O₃.unch h7 hn (i := PX) (by decide) (apart_slW (c := c) (l := [PY]) (by decide)), e₂]
    by_cases hP : P <;> simp [hP]
  · show wordsVal s₃.mem _ _ _ = _
    rw [e₃, sv_unch O₂.unch h7 hn (i := QYM) (by decide) (apart_slW (c := c) (l := [PX]) (by decide)),
      sv_unch O₂.unch h7 hn (i := GY) (by decide) (apart_slW (c := c) (l := [PX]) (by decide))]
    by_cases hP : P <;> simp [hP]

/-! ## The whole validation -/

/-- The working-space ranges of a stage are in the working space. -/
theorem le_append {W W' : List (Nat × Nat)} (h : ∀ w ∈ W, w.1 + w.2 ≤ size) (h' : ∀ w ∈ W', w.1 + w.2 ≤ size) :
    ∀ w ∈ W ++ W', w.1 + w.2 ≤ size := fun w hw => (List.mem_append.mp hw).elim (h w) (h' w)

/-- The peer's point is valid as the code checks it: `P₀` (its first byte
and the range of its coordinates) and the curve's equation. -/
abbrev PeerOk (c : Cfg) (base : Addr) (s : State) (P₀ : Prop) : Prop :=
  P₀ ∧ OnCurve c (Fin.ofNat c.C.p (sv c base s E)) (Fin.ofNat c.C.p (sv c base s QY))

/-- What the validation writes. -/
abbrev valW (c : Cfg) : List (Nat × Nat) :=
  slW c [QXM, QYM, W0, W1, W2, W3, PY] ++ [(own c.n, 64 * c.n), (c.sl FLAG, 8)]

theorem fixedOk_valW (h7 : c.n < 10) : FixedOk c (valW c) :=
  show FixedOk c (slW c [QXM, QYM, W0, W1, W2, W3, PY] ++ ([(own c.n, 64 * c.n)] ++ [(c.sl FLAG, 8)])) from
    (fixedOk_slW (by decide)).append (FixedOk.append (W := [(own c.n, 64 * c.n)]) (fun w hw => by
      rw [List.mem_singleton.mp hw]
      exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_below_own c h7 (i := 12) (by decide))))
      fixedOk_flag)

theorem valW_le (h7 : c.n < 10) : ∀ w ∈ valW c, w.1 + w.2 ≤ size := by
  have hsz : size = 8192 := rfl
  have ho := own_below_bits c h7 0
  have hb := bitsAt_le c h7 (j := 0) (by decide)
  have hF := sl_le c h7 (i := FLAG) (by decide)
  refine le_append (fun w hw => ?_) (fun w hw => ?_)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    have hl : ∀ i ∈ [QXM, QYM, W0, W1, W2, W3, PY], i < 45 := by decide
    have := sl_le c h7 (hl i hi)
    dsimp only; omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl <;> (dsimp only; omega_arith)

theorem tbl_apart_valW (h7 : c.n < 10) (h0 : 0 < c.n) (j t : Nat) :
    ∀ w ∈ valW c, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t :=
  apart_append (tbl_apart_slW h7 (by decide) j t)
    (show ∀ w ∈ [(own c.n, 64 * c.n)] ++ [(c.sl FLAG, 8)], _ from
      apart_append (tbl_apart_own h7 j t) (tbl_apart_flag h7 h0 j t))

theorem validate_eq (c : Cfg) : Impl.Ecdh.PPC64LE.Cfg.validate c =
    .seq (mulCall c.SP (c.sl QXM) (c.sl E) (c.sl R2P)) (.seq (mulCall c.SP (c.sl QYM) (c.sl QY) (c.sl R2P))
      (.seq (fprog c.SP (Impl.Ecdh.PPC64LE.Cfg.curveOps c))
      (.block (Impl.Ecdh.PPC64LE.Cfg.checkZero c (c.sl W1) ++ Impl.Ecdh.PPC64LE.Cfg.select c)))) := rfl

/-- A word apart from what a stage writes. -/
theorem flag_unch (h7 : c.n < 10) (h0 : 0 < c.n) {base : Addr} {W : List (Nat × Nat)} {m m' : Mem}
    (hu : Unch base W m m') (hW : ∀ w ∈ W, c.sl FLAG + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG) :
    word m' base (c.sl FLAG) = word m base (c.sl FLAG) :=
  hu.word (fun w hw => (hW w hw).imp (fun h => by omega_arith) id)
    (by have := sl_le c h7 (i := FLAG) (by decide); omega_arith)

theorem validate_ok (hc : CfgOk c) {base : Addr} {s : State} (hw : WsReg s base) {g : Reg → BitVec 64}
    {lr : BitVec 64} (F : Fixed c base g lr s.mem) (hr2 : sv c base s R2P = c.R * c.R % c.C.p)
    (hbp : sv c base s BP = c.mont c.C.b) {P₀ : Prop} [Decidable P₀] (hf : flagW c base s = mask64 P₀) :
    WP isa (Impl.Ecdh.PPC64LE.Cfg.validate c) s fun s' =>
      WsReg s' base ∧ Rk fnClob s s' ∧ Unch base (valW c) s.mem s'.mem ∧
      flagW c base s' = mask64 (PeerOk c base s P₀) ∧
      sv c base s' PX < c.C.p ∧ sv c base s' PY < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' PX) =
        (if PeerOk c base s P₀ then Fin.ofNat c.C.p (sv c base s E) else Fin.ofNat c.C.p c.C.gx) ∧
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s' PY) =
        (if PeerOk c base s P₀ then Fin.ofNat c.C.p (sv c base s QY) else Fin.ofNat c.C.p c.C.gy) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hw.nowrap
  have hp3 := hc.p_ge
  have hsz : size = 8192 := rfl
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_arith)
  have hF : c.sl FLAG + 8 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega_arith
  rw [validate_eq]
  refine mont_ok hc hw hr2 fun s₂ Mp => ?_
  have F₂ := F.unch h7 hn ((fixedOk_callW h7 (o := QXM) (by decide)).append (fixedOk_callW h7 (o := QYM) (by decide)))
    Mp.unch
  have e₂ : ∀ {i}, i < 45 → i ∉ [QXM, QYM] → sv c base s₂ i = sv c base s i := fun hi hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hl
    exact sv_unch Mp.unch h7 hn hi (apart_append (apart_callW h7 hi hl.1) (apart_callW h7 hi hl.2))
  refine WP.seq (WP.mono (curve_ok hc Mp.ws Mp.x_lt Mp.y_lt F₂.ap
    (by rw [e₂ (i := BP) (by decide) (by decide)]; exact hbp)) fun s₃ ⟨hw₃, k₃, U₃, z₃⟩ => ?_)
  rw [Mp.x, Mp.y] at z₃
  refine wp_append (WP.mono (checkZero_ok c hw₃.ws hw₃.at3 (sl_al c W1) h0
    (by have := sl_le c h7 (i := W1) (by decide); omega_arith) hF) fun s₄ ⟨f₄, k₄, O₄⟩ => ?_)
  have hw₄ := hw₃.of_kp k₄
  have apC : ∀ w ∈ slW c [W0, W1, W2, W3] ++ [(own c.n, 64 * c.n)],
      c.sl FLAG + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG :=
    apart_append (apart_slW (c := c) (l := [W0, W1, W2, W3]) (i := FLAG) (by decide)) (apart_own h7 (by decide))
  have hf₄ : flagW c base s₄ = mask64 (PeerOk c base s P₀) := by
    rw [f₄, flagW, flag_unch h7 h0 U₃ apC, flag_unch h7 h0 Mp.unch
      (apart_append (apart_callW h7 (by decide) (by decide)) (apart_callW h7 (by decide) (by decide))), ← flagW,
      hf, mask64_and]
    simp only [mask64, z₃]
  have U₄ : Unch base (slW c [W0, W1, W2, W3] ++ [(own c.n, 64 * c.n)] ++ [(c.sl FLAG, 8)]) s₂.mem s₄.mem :=
    U₃.trans O₄.unch
  have F₄ := F₂.unch h7 hn (((fixedOk_slW (l := [W0, W1, W2, W3]) (by decide)).append
    (fun w hw => by
      rw [List.mem_singleton.mp hw]
      exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_below_own c h7 (i := 12) (by decide))))).append
    fixedOk_flag) U₄
  refine WP.mono (select_ok hc hw₄ hf₄) fun s₆ ⟨hw₆, k₆, U₆, px, py⟩ => ?_
  have q₄ : ∀ {i}, i < 45 → i ∉ [W0, W1, W2, W3] → i ≠ FLAG → sv c base s₄ i = sv c base s₂ i :=
    fun hi hl hfl => sv_unch U₄ h7 hn hi (apart_append (apart_append (apart_slW hl) (apart_own h7 hi))
      (apart_flag h0 hfl))
  have qx : sv c base s₄ QXM = sv c base s₂ QXM := q₄ (by decide) (by decide) (by decide)
  have qy : sv c base s₄ QYM = sv c base s₂ QYM := q₄ (by decide) (by decide) (by decide)
  refine ⟨hw₆, (k₃.trans (k₄.rk (rs' := fnClob))).trans (k₆.rk (rs' := fnClob)) |> Mp.rk.trans, ?_,
    by rw [flagW, flag_unch h7 h0 U₆ (apart_slW (c := c) (l := [PX, PY]) (i := FLAG) (by decide)), ← flagW]; exact hf₄,
    ?_, ?_, ?_, ?_⟩
  · refine ((Mp.unch.trans U₄).trans U₆).mono fun w hw' => ?_
    simp only [callW, slW, List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hw' ⊢
    simp only [PX, W3] at hw' ⊢
    grind
  · rw [px]; split
    · rw [qx]; exact Mp.x_lt
    · exact lt_of_eq_of_lt F₄.gx (hmont _)
  · rw [py]; split
    · rw [qy]; exact Mp.y_lt
    · exact lt_of_eq_of_lt F₄.gy (hmont _)
  · rw [px]; split
    · rw [qx, Mp.x]
    · show toM _ _ (wordsVal s₄.mem base (c.sl GX) c.n) = _
      rw [F₄.gx, toM_cmont hc]
  · rw [py]; split
    · rw [qy, Mp.y]
    · show toM _ _ (wordsVal s₄.mem base (c.sl GY) c.n) = _
      rw [F₄.gy, toM_cmont hc]

end VG.Proof.Ecdh.PPC64LE

end

end

/-!
# ECDH on PPC64LE: the whole function

As on 32-bit ARM (`Proof/Ecdh/Arm/Main.lean`). `ecFinish_ok`: `x` or zeros
to `out`, the return value and the callee-saved registers; `middle_ok`:
`x = X Z^(p-2)` out of Montgomery's form, the masks of `d ∈ [1, n-1]` and
`Z ≠ 0`, and the result.

`exchangeWith_ok`: `Cfg.exchangeWith` computes the specification's shared secret of
`d` and the peer's public key, for any curve the proof of the code supports
(`CfgOk`, coordinates of 3 to 6 words) whose group law the proofs support
(`Law`), restores the callee-saved registers and `lr`, and changes memory
only in the working space and `out`: the signature's setup and tables
(`stage₁`'s, with `peer` kept in `r12`), then `peer_ok`, `validate_ok`, the
multiplication and the power (any that meet `MulPowOk`; `exchange_ok`: the
ladder, `ladPow_ok`) and `middle_ok`; `exchange_eq` connects
what they compute to the specification.
-/

@[expose] public section

namespace VG.Proof.Ecdh.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Spec.Weierstrass
open VG.Proof.EcKey.PPC64LE (toNat_add_of)
open VG.Proof.Weierstrass.PPC64LE.Point (tmv)
open VG.Impl.Ecdh.PPC64LE (QY R2P BP QXM QYM W0 W1 W2 W3 PX PY)

variable {c : Cfg}

theorem finish_eq (c : Cfg) : Impl.Ecdh.PPC64LE.Cfg.finish c =
    ([.load .d .r10 wb (c.sl FLAG)] : List Instr) ++ (storeBytes c.C.len c.n .r14 0 (c.sl X) ++
    (.li .r4 1 :: .logic .and .r4 .r10 .r4 :: (Cfg.restore ++ [mov .r3 .r4]))) := by
  simp only [Impl.Ecdh.PPC64LE.Cfg.finish, List.append_assoc, List.cons_append, List.nil_append]

/-- `x` or zeros, the return value and the callee-saved registers. -/
theorem ecFinish_ok (hc : CfgOk c) {base : Addr} {s : State} (hw : WsReg s base) {out : Addr}
    (h14 : s.gpr .r14 = out) (hofit : out.toNat + c.C.len ≤ 2 ^ 64)
    (hwr : (⟨out, c.C.len⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨out, c.C.len⟩ ⟨base, size⟩) (b : Bool)
    (hf : flagW c base s = mask64 (b = true)) :
    WP isa (.block (Impl.Ecdh.PPC64LE.Cfg.finish c)) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem out c.C.len =
        (if b then toBytes c.C.len (sv c base s X) else List.replicate c.C.len 0) ∧
      s'.gpr .r3 = (if b then 1 else 0) ∧
      s'.lr = word s.mem base Cfg.lrAt ∧ s'.gpr .r14 = word s.mem base 0 ∧ s'.gpr .r31 = word s.mem base 8 ∧
      Rk [.r0, .r3, .r4, .r5, .r6, .r10, .r14, .r31] s s' ∧
      Outside out 0 c.C.len s.mem s'.mem := by
  have h7 := hc.n10
  have hl8 := hc.len8
  have hlhi := hc.len_hi
  have hllo := hc.len_lo
  have hn := hw.nowrap
  have hsz : size = 8192 := rfl
  obtain hX := sl_le c h7 (i := X) (by decide)
  obtain hF := sl_le c h7 (i := FLAG) (by decide)
  have hs := hw.ws
  have h3 := hw.at3
  obtain h0 : out + BitVec.ofNat 64 0 = out := BitVec.add_zero out
  rw [finish_eq, List.singleton_append]
  refine wp_step (ld0_ok hs h3 (by decide) (sl_al c FLAG) (by omega_arith)) ?_
  obtain hs₁ := hs.write .r10 (word s.mem base (c.sl FLAG))
  obtain h3₁ := h3.write (d := .r10) (word s.mem base (c.sl FLAG))
  obtain hc₁ : (s.write .r10 (word s.mem base (c.sl FLAG))).gpr .r10 = if b then BitVec.allOnes 64 else 0 := by
    simp only [write_gpr, ite_true]; rw [← flagW, hf]
  obtain hb₁ : (s.write .r10 (word s.mem base (c.sl FLAG))).gpr .r14 = out := by
    simp only [write_gpr, reduceCtorEq, ite_false]; exact h14
  refine wp_append (WP.mono (storeBytes_ok hs₁ h3₁ (dst := .r14) (d := 0) (a := c.sl X) (by decide) (by decide)
    (by decide) (by decide) b hc₁ (by omega_arith) (sl_al c X) (by omega_arith) (by omega_arith) hlhi (by omega_arith)
    (by rw [hb₁, h0]; exact hofit)
    (fun e m he => ⟨_, hwr, by rw [hb₁, h0]; exact Offset.contains_base out he (by omega_arith)⟩)
    (by rw [hb₁, h0]; exact hd.symm.sub_left (Offset.sub_base base (by omega_arith)))) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_)
  rw [hb₁, h0] at e₂ O₂
  obtain U₂ := O₂.unch_far hd.symm
  obtain hsv : ∀ d, d + 8 ≤ 24 → word s₂.mem base d = word s.mem base d := fun d hd' =>
    U₂.word (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega_arith) (by omega_arith)
  obtain hs₂ := k₂.ws hs₁
  obtain h3₂ := k₂.at h3₁
  refine wp_step (exec_li (by decide)) ?_
  refine wp_step exec_logic ?_
  refine restore_ok ((hs₂.write _ _).write _ _) ((h3₂.write _).write _) (by omega_arith) fun t Kt mt lrt r14t r31t => ?_
  refine wp_step exec_mov (WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  · simp only [write_mem]; rw [mt]; simp only [write_mem]; rw [e₂]; rfl
  · simp only [write_gpr, ite_true]
    rw [Kt.gpr _ (by decide)]
    simp only [write_gpr, ite_true, reduceCtorEq, ite_false]
    rw [k₂.g, hc₁, ← mask_bit]
  · simp only [write_lr]; rw [lrt]; simp only [write_mem]; exact hsv _ (by decide)
  · simp only [write_gpr, reduceCtorEq, ite_false]; rw [r14t]; simp only [write_mem]; exact hsv _ (by decide)
  · simp only [write_gpr, reduceCtorEq, ite_false]; rw [r31t]; simp only [write_mem]; exact hsv _ (by decide)
  · have R₁ : Rk [.r0, .r3, .r4, .r5, .r6, .r10, .r14, .r31] s s₂ :=
      ((Kp.write s (d := .r10) _ (rs := [.r10]) (by decide)).rk).trans
        (k₂.rk (rs' := [.r0, .r3, .r4, .r5, .r6, .r10, .r14, .r31]))
    exact ((R₁.trans (((Kp.write s₂ (d := .r4) (BitVec.ofNat 64 1) (rs := [.r4]) (by decide)).trans
      (Kp.write _ (d := .r4) _ (rs := [.r4]) (by decide))).rk)).trans (Kt.mono (by decide))).trans
      ((Kp.write t (d := .r3) _ (rs := [.r3]) (by decide)).rk)
  · simp only [write_mem]; rw [mt]; simp only [write_mem]; exact O₂

theorem middle_eq (c : Cfg) : Impl.Ecdh.PPC64LE.Cfg.middle c =
    .seq (mulCall c.SP (c.sl XM) (c.sl RX) (c.sl ACC))
    (.seq (mulCall c.SP (c.sl X) (c.sl XM) (c.sl ONE))
    (.block (c.checkRange (c.sl D) ++ c.checkNonzero (c.sl RZ) ++ Impl.Ecdh.PPC64LE.Cfg.finish c))) := rfl

/-- Whether the result is a shared secret: the peer's key (`V`), `d` in
`[1, n-1]`, and `Z ≠ 0`. -/
abbrev ok (c : Cfg) (base : Addr) (s : State) (V : Prop) [Decidable V] : Bool :=
  decide ((V ∧ 0 < sv c base s D ∧ sv c base s D < c.C.n) ∧ sv c base s RZ ≠ 0)

/-- `x`, the checks of `d` and `Z`, and the result, from a state that kept
what the stages keep since `s₀`. -/
theorem middle_ok (hc : CfgOk c) {s₀ : State} {base : Addr} {s : State} (K : Keep c s₀ base s)
    (hacc : sv c base s ACC < c.C.p) {V : Prop} [Decidable V] (hflag : flagW c base s = mask64 V)
    (hofit : (s₀.gpr .r3).toNat + c.C.len ≤ 2 ^ 64)
    (hw : (⟨s₀.gpr .r3, c.C.len⟩ : Region) ∈ s₀.wr)
    (hd : Region.Disjoint ⟨s₀.gpr .r3, c.C.len⟩ ⟨base, size⟩) :
    WP isa (Impl.Ecdh.PPC64LE.Cfg.middle c) s fun s' => ∃ xv, xv < c.C.p ∧
      Fin.ofNat c.C.p xv =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) ∧
      Spec.Ecdsa.bytesAt s'.mem (s₀.gpr .r3) c.C.len =
        (if ok c base s V then toBytes c.C.len xv else List.replicate c.C.len 0) ∧
      s'.gpr .r3 = (if ok c base s V then 1 else 0) ∧
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.sp = s₀.sp ∧ s'.lr = s₀.lr ∧
      ∃ m, Unch base [(0, size)] s₀.mem m ∧ Outside (s₀.gpr .r3) 0 c.C.len m s'.mem := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := K.ws.nowrap
  have hsz : size = 8192 := rfl
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  obtain hfl : c.sl FLAG + 8 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega_arith
  have hone : sv c base s ONE = 1 := K.fixed.one
  rw [middle_eq]
  -- `XM = X · ACC`.
  refine WP.seq (WP.mono (slMul_ok hc.fp hc.fpk hc.fpm h7 K.ws (o := XM) (a := RX) (b := ACC) (by decide)
    (by decide) (by decide) hacc) fun s₁ ⟨k₁, U₁, _, e₁⟩ => ?_)
  obtain K₁ := K.step h7 k₁ (hU := U₁) (hW := fixedOk_callW h7 (by decide)) (hWs := callW_le h7 (by decide))
  obtain v₁ : ∀ {i}, i < 45 → i ≠ XM → sv c base s₁ i = sv c base s i := fun hi h₁ =>
    sv_unch U₁ h7 hn hi (apart_callW h7 hi h₁)
  -- `X = XM · 1`.
  refine WP.seq (WP.mono (slMul_ok hc.fp hc.fpk hc.fpm h7 K₁.ws (o := X) (a := XM) (b := ONE) (by decide)
    (by decide) (by decide) (by rw [v₁ (by decide) (by decide), hone]; omega_arith)) fun s₂ ⟨k₂, U₂, lt₂, e₂⟩ => ?_)
  obtain K₂ := K₁.step h7 k₂ (hU := U₂) (hW := fixedOk_callW h7 (by decide)) (hWs := callW_le h7 (by decide))
  obtain v₂ : ∀ {i}, i < 45 → i ≠ XM → i ≠ X → sv c base s₂ i = sv c base s i := fun hi h₁ h₂ =>
    (sv_unch U₂ h7 hn hi (apart_callW h7 hi h₂)).trans (v₁ hi h₁)
  obtain x₂ : Fin.ofNat c.C.p (sv c base s₂ X) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) := by
    rw [toM_one_mul hpR (by rw [e₂, v₁ (i := ONE) (by decide) (by decide), hone]), toM_mul hpR e₁]
  obtain fl₂ : flagW c base s₂ = flagW c base s := by
    simp only [flagW]
    rw [flag_callW h0 h7 (o := X) (by decide) U₂, flag_callW h0 h7 (o := XM) (by decide) U₁]
  rw [List.append_assoc]
  refine wp_append (WP.mono (checkRange_ok c K₂.ws.ws K₂.ws.at3 (sl_al c D) h0
    (by have := sl_le c h7 (i := D) (by decide); omega_arith) (by have := sl_le c h7 (i := MN) (by decide); omega_arith) hfl)
    fun s₅ ⟨f₅, k₅, O₅⟩ => ?_)
  obtain K₅ := K₂.step h7 (k₅.rk (rs' := [.r0, .r4, .r5, .r6, .r7, .r8, .r9])) (hU := O₅.unch) (hW := fixedOk_flag)
    (hWs := by intro w hw; rw [List.mem_singleton.mp hw]; exact hfl)
  refine wp_append (WP.mono (checkNonzero_ok c K₅.ws.ws K₅.ws.at3 (sl_al c RZ) h0
    (by have := sl_le c h7 (i := RZ) (by decide); omega_arith) hfl) fun s₆ ⟨f₆, k₆, O₆⟩ => ?_)
  obtain K₆ := K₅.step h7 (k₆.rk (rs' := [.r4, .r5])) (hU := O₆.unch) (hW := fixedOk_flag) (hWs := by
    intro w hw; rw [List.mem_singleton.mp hw]; exact hfl)
  obtain e₆ : ∀ {i}, i < 45 → i ≠ FLAG → sv c base s₆ i = sv c base s₂ i := fun hi hif =>
    (sv_unch O₆.unch h7 hn hi (apart_flag h0 hif)).trans (sv_unch O₅.unch h7 hn hi (apart_flag h0 hif))
  have hMN : wordsVal s₂.mem base (c.sl MN) c.n = c.C.n := K₂.fixed.mn
  obtain z₅ : wordsVal s₅.mem base (c.sl RZ) c.n = sv c base s RZ :=
    (sv_unch O₅.unch h7 hn (i := RZ) (by decide) (apart_flag h0 (by decide))).trans
      (v₂ (by decide) (by decide) (by decide))
  obtain d₂ : wordsVal s₂.mem base (c.sl D) c.n = sv c base s D := v₂ (by decide) (by decide) (by decide)
  obtain hflag₆ : flagW c base s₆ = mask64 (ok c base s V = true) := by
    rw [f₆, f₅, fl₂, hflag, hMN, z₅, d₂, mask64_and, mask64_and]
    simp only [ok, decide_eq_true_eq]
  refine WP.mono (ecFinish_ok hc K₆.ws (by rw [K₆.r14]) hofit (by rw [K₆.rk.wr]; exact hw) hd _ hflag₆)
    fun s' ⟨bytes, r3, lr, r14, r31, rk, out⟩ => ?_
  obtain x₆ : sv c base s₆ X = sv c base s₂ X := e₆ (by decide) (by decide)
  have hsv := K₆.fixed.saved
  refine ⟨_, lt₂, x₂, by rw [bytes, x₆], r3, ?_, by rw [rk.sp, K₆.rk.sp],
    by rw [lr, K₆.fixed.savedLr], s₆.mem, K₆.whole, out⟩
  intro r hr
  obtain hcases : ∀ r ∈ preserved, r = .r14 ∨ r = .r31 ∨
      (r ∉ [Reg.r0, .r3, .r4, .r5, .r6, .r10, .r14, .r31] ∧ r ∉ work) := by decide
  rcases hcases r hr with rfl | rfl | ⟨h₁, h₂⟩
  · rw [r14]; exact hsv (.r14, 0) (by decide)
  · rw [r31]; exact hsv (.r31, 8) (by decide)
  · rw [rk.gpr r h₁, K₆.rk.gpr r h₂]

/-- The arguments: `out` (`len` bytes), `d` (`len` bytes), `peer`
(`1 + 2 len` bytes) and `scratch`, readable and writable as the contract
says and apart from each other as it says. -/
structure EPre (c : Cfg) (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r4, c.C.len⟩, ⟨s.gpr .r5, 1 + 2 * c.C.len⟩]
  wr : s.wr = [⟨s.gpr .r3, c.C.len⟩, ⟨s.gpr .r6, size⟩]
  out_sc : Region.Disjoint ⟨s.gpr .r3, c.C.len⟩ ⟨s.gpr .r6, size⟩
  d_sc : Region.Disjoint ⟨s.gpr .r4, c.C.len⟩ ⟨s.gpr .r6, size⟩
  peer_sc : Region.Disjoint ⟨s.gpr .r5, 1 + 2 * c.C.len⟩ ⟨s.gpr .r6, size⟩
  out_fit : (s.gpr .r3).toNat + c.C.len ≤ 2 ^ 64
  d_fit : (s.gpr .r4).toNat + c.C.len ≤ 2 ^ 64
  peer_fit : (s.gpr .r5).toNat + (1 + 2 * c.C.len) ≤ 2 ^ 64
  sc_fit : (s.gpr .r6).toNat + size ≤ 2 ^ 64

theorem EPre.setup {s : State} (hp : EPre c s) : SetupPre c Impl.Ecdh.PPC64LE.Args.ecdh s where
  shift := .inl rfl
  k_reg := by decide
  d_reg := by decide
  e_reg := by decide
  sc_reg := by decide
  wr := by show (⟨s.gpr .r6, size⟩ : Region) ∈ s.wr; rw [hp.wr]; simp
  sc_fit := hp.sc_fit
  k_in := inRegions_words (by rw [hp.rd]; simp) (by have := hp.d_fit; omega_arith)
  d_in := inRegions_words (by rw [hp.rd]; simp) (by have := hp.d_fit; omega_arith)
  e_in := inRegions_words (by rw [hp.rd]; simp) (by have := hp.d_fit; omega_arith)
  k_sc := hp.d_sc
  d_sc := hp.d_sc
  e_sc := hp.d_sc
  k_fit := hp.d_fit
  d_fit := hp.d_fit
  e_fit := hp.d_fit

/-- The private key. -/
abbrev dk (c : Cfg) (s₀ : State) : Nat := ofBytes (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r4) c.C.len)

/-- The result the contract asks for: the specification's shared secret, and
`1`, or zeros and `0`. -/
def EPost (c : Cfg) (s₀ s' : State) : Prop :=
  match Spec.Ecdh.exchange c.C (dk c s₀) (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r5) (1 + 2 * c.C.len)) with
  | some z => s'.gpr .r3 = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (s₀.gpr .r3) c.C.len = z
  | none => s'.gpr .r3 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (s₀.gpr .r3) c.C.len = List.replicate c.C.len 0

/-- What the function keeps: the callee-saved registers, `sp` and `lr`, and
memory but the working space and `out`. -/
structure EKeep (c : Cfg) (s₀ s' : State) : Prop where
  saved : ∀ r ∈ preserved, s'.gpr r = s₀.gpr r
  sp : s'.sp = s₀.sp
  lr : s'.lr = s₀.lr
  frame : ∃ m : Mem, Unch (s₀.gpr .r6) [(0, size)] s₀.mem m ∧ Outside (s₀.gpr .r3) 0 c.C.len m s'.mem

/-- The point the ladder multiplies: the peer's, if its key is valid as the
code checks it, else `G`. -/
def peerPt (c : Cfg) (b4 : Prop) [Decidable b4] (x y : Nat) : Point c.C :=
  if h : ((b4 ∧ x < c.C.p) ∧ y < c.C.p) ∧ OnCurve c (Fin.ofNat c.C.p x) (Fin.ofNat c.C.p y) then
    .affine ⟨x, h.1.1.2⟩ ⟨y, h.1.2⟩ else G c.C

theorem peerPt_onCurve (hc : CfgOk c) (b4 : Prop) [Decidable b4] (x y : Nat) :
    onCurve c.C (peerPt c b4 x y) = true := by
  unfold peerPt
  split
  · next h => exact (onCurve_iff _ _).mpr h.2
  · exact hc.onG

theorem peerPt_rep (hC : Law c.C) (b4 : Prop) [Decidable b4] (x y : Nat) {X Y : Fe c.C}
    (hX : X = if ((b4 ∧ x < c.C.p) ∧ y < c.C.p) ∧ OnCurve c (Fin.ofNat c.C.p x) (Fin.ofNat c.C.p y)
      then Fin.ofNat c.C.p x else Fin.ofNat c.C.p c.C.gx)
    (hY : Y = if ((b4 ∧ x < c.C.p) ∧ y < c.C.p) ∧ OnCurve c (Fin.ofNat c.C.p x) (Fin.ofNat c.C.p y)
      then Fin.ofNat c.C.p y else Fin.ofNat c.C.p c.C.gy) :
    Rep c.C X Y 1 (peerPt c b4 x y) := by
  unfold peerPt
  by_cases h : ((b4 ∧ x < c.C.p) ∧ y < c.C.p) ∧ OnCurve c (Fin.ofNat c.C.p x) (Fin.ofNat c.C.p y)
  · rw [dite_eq_left h]; rw [ite_eq_left h] at hX hY
    rw [hX, hY]
    exact ⟨one_ne_zero_fe hC, by rw [EcKey.fe_eq h.1.1.2 rfl, Lean.Grind.Semiring.mul_one],
      by rw [EcKey.fe_eq h.1.2 rfl, Lean.Grind.Semiring.mul_one]⟩
  · rw [dite_eq_right h]; rw [ite_eq_right h] at hX hY; rw [hX, hY]
    exact rep_affine' hC _ _

/-- The peer's key: `04`, `x` and `y`. -/
theorem peer_bytes (m : Mem) (p : Addr) (L : Nat) :
    Spec.Ecdsa.bytesAt m p (1 + 2 * L) = m p :: (Spec.Ecdsa.bytesAt m (p + BitVec.ofNat 64 1) L ++
      Spec.Ecdsa.bytesAt m (p + BitVec.ofNat 64 (1 + L)) L) := by
  obtain h1 : Spec.Ecdsa.bytesAt m p 1 = [m p] := by
    simp only [Spec.Ecdsa.bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero]
  rw [show 1 + 2 * L = 1 + (L + L) by omega_arith, bytesAt_add, bytesAt_add, h1, BitVec.add_assoc,
    BitVec.ofNat_add_ofNat]
  rfl

theorem exchangeWith_eq' (c : Cfg) (mul : Prog isa) : Impl.Ecdh.PPC64LE.Cfg.exchangeWith c mul =
    .seq (.block (c.setupWith Impl.Ecdh.PPC64LE.Args.ecdh ++ [mov .r12 .r5]))
      (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) (.seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n))
      (.seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n))
      (.seq (.block (Impl.Ecdh.PPC64LE.Cfg.peerAt c .r12)) (.seq (Impl.Ecdh.PPC64LE.Cfg.validate c)
      (.seq mul (.seq c.invP (Impl.Ecdh.PPC64LE.Cfg.middle c)))))))) :=
  rfl

/-- What a multiplication `[d]P`, followed by the power `Z^(p-2)`, may assume
of the state after the checks of the peer's key (`s`, from `s₀`): what the
stages keep, `R = O`, `d` at `K`'s slot and in the table of bits, the table
of `p - 2`'s bits, `b R mod p` at `BP`, and `P`, on the curve, at `PX`,
`PY` and `ONEP`; and what it leaves (`LadPost`). -/
def MulPowOk (c : Cfg) (s₀ : State) (mul : Prog isa) : Prop :=
  ∀ {base : Addr} {s : State}, Keep c s₀ base s → sv c base s RX = 0 → sv c base s RY = c.mont 1 →
    sv c base s RZ = 0 → sv c base s K = dk c s₀ →
    (∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if (dk c s₀).testBit t then 1 else 0) →
    (∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 1 + t)) = if (c.C.p - 2).testBit t then 1 else 0) →
    sv c base s BP = c.mont c.C.b → ∀ {P : Point c.C}, onCurve c.C P = true →
    Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY)) (tmv c.C c.n base s (c.sl ONEP)) P →
    sv c base s PX < c.C.p → sv c base s PY < c.C.p →
    ∀ {rest : Prog isa} {Q : State → Prop}, (∀ s', LadPost c s₀ base (dk c s₀) P s s' → WP isa rest s' Q) →
      WP isa (.seq mul (.seq c.invP rest)) s Q

/-- The ladder (`qMul`) meets `MulPowOk`. -/
theorem qMul_mulPowOk (hc : CfgOk c) (h3 : 3 ≤ c.n) (hC : Law c.C) (s₀ : State) :
    MulPowOk c s₀ (c.qMul PX PY) := by
  intro base s K hrx hry hrz hk ht₀ _ _ P hP hG hlx hly rest Q h
  exact ladPow_ok hc h3 hC (gx := PX) (gy := PY) (by decide) (by decide) (by decide) (by decide) K
    (ofBytes_bytesAt_lt _ _ _) hrx hry hrz (fun _ => hk) ht₀ hP hG hlx hly h

/-- `vg_ecdh_<curve>`, with `[d]P` by any `mul` that meets `MulPowOk`,
computes the specification's shared secret and restores the callee-saved
registers and `lr`. -/
theorem exchangeWith_ok (hc : CfgOk c) (hC : Law c.C) {s₀ : State} (hp : EPre c s₀) {mul : Prog isa}
    (hMul : MulPowOk c s₀ mul) :
    WP isa (Impl.Ecdh.PPC64LE.Cfg.exchangeWith c mul) s₀ fun s' => EKeep c s₀ s' ∧ EPost c s₀ s' := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hlhi := hc.len_hi
  have hl8 := hc.len8
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hsz : size = 8192 := rfl
  rw [exchangeWith_eq']
  -- The setup, and `peer` to `r12`.
  refine WP.seq (wp_append (WP.mono (stage₀' hc hp.setup) fun s₁ ⟨S₁, kp₁⟩ =>
    wp_step exec_mov (WP.block_nil ?_)))
  generalize hb : s₀.gpr .r6 = base at S₁
  replace S₁ : St₀ c Impl.Ecdh.PPC64LE.Args.ecdh s₀ base (BitVec.allOnes 64) s₁ := S₁
  have hn := S₁.ws.nowrap
  obtain kw : Kp [.r12] s₁ (s₁.write .r12 (s₁.gpr .r5)) := Kp.write _ _ (by decide)
  obtain S₁' : St₀ c Impl.Ecdh.PPC64LE.Args.ecdh s₀ base (BitVec.allOnes 64) (s₁.write .r12 (s₁.gpr .r5)) :=
    ⟨S₁.toKeep.step h7 (kw.rk (rs' := [.r12])) (W := []) (hU := Unch.refl _ _ _) (hW := fun _ h => absurd h List.not_mem_nil)
      (hWs := fun _ h => absurd h List.not_mem_nil),
      S₁.k, S₁.d, S₁.e, S₁.rx, S₁.ry, S₁.rz, S₁.expp, S₁.expn, S₁.flag⟩
  obtain r12₁ : (s₁.write .r12 (s₁.gpr .r5)).gpr .r12 = s₀.gpr .r5 := by
    simp only [write_gpr, ite_true]; exact kp₁.gpr _ (by decide)
  -- The tables of bits.
  refine tables_ok hc S₁' fun s₂ S₂ kb => ?_
  obtain r12₂ : s₂.gpr .r12 = s₀.gpr .r5 := by rw [kb.gpr _ (by decide), r12₁]
  obtain W₂ : Outside base 0 size s₀.mem s₂.mem :=
    S₂.whole.outside fun w hw => by rw [List.mem_singleton.mp hw]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  obtain hpsc : Region.Disjoint ⟨s₀.gpr .r5, 1 + 2 * c.C.len⟩ ⟨base, size⟩ := by rw [← hb]; exact hp.peer_sc
  -- The peer's key.
  refine WP.seq (WP.mono (peer_ok hc S₂.ws (q := .r12) (by decide)
    (by rw [r12₂]; exact hp.peer_fit) (by rw [r12₂, S₂.rk.rd, S₂.rk.wr, hp.rd]; simp)
    (by rw [r12₂]; exact hpsc) S₂.fixed.mp) fun s₃ ⟨hw₃, k₃, U₃, r2₃, bp₃, x₃, y₃, f₃⟩ => ?_)
  rw [r12₂] at x₃ y₃ f₃
  obtain hl₃ : ∀ i ∈ [R2P, BP, E, QY], i < 45 := by decide
  obtain K₃ := S₂.toKeep.step h7 (k₃.rk (rs' := peerClob)) (hU := U₃)
    (hW := (fixedOk_slW (by decide)).append fixedOk_flag)
    (hWs := le_append (fun w hw => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      have := sl_le c h7 (hl₃ i hi); dsimp only; omega_arith)
      (fun w hw => by
        rw [List.mem_singleton.mp hw]; have := sl_le c h7 (i := FLAG) (by decide); dsimp only; omega_arith))
  obtain e₃ : ∀ {i}, i < 45 → i ∉ [R2P, BP, E, QY] → i ≠ FLAG → sv c base s₃ i = sv c base s₂ i :=
    fun hi hl hf => sv_unch U₃ h7 hn hi (apart_append (apart_slW hl) (apart_flag h0 hf))
  obtain hq0 : s₂.mem (s₀.gpr .r5) = s₀.mem (s₀.gpr .r5) := by
    have := keep_of_disjoint' W₂ hpsc (by omega_arith) (i := 0) (by omega_arith) (by omega_arith)
    rwa [BitVec.add_zero] at this
  -- What the code checks of the peer's key so far.
  obtain hf₃ : flagW c base s₃ = mask64 ((s₀.mem (s₀.gpr .r5) = 4 ∧ sv c base s₃ E < c.C.p) ∧
      sv c base s₃ QY < c.C.p) := by
    rw [f₃, hq0, S₂.flag, BitVec.allOnes_and, mask64_and, mask64_and]
  refine WP.seq (WP.mono (validate_ok hc K₃.ws K₃.fixed r2₃ bp₃ hf₃)
    fun s₄ ⟨hw₄, k₄, U₄, f₄, px_lt, py_lt, px, py⟩ => ?_)
  obtain K₄ := K₃.step h7 k₄ (hU := U₄) (hW := fixedOk_valW h7) (hWs := valW_le h7)
  obtain e₄ : ∀ {i}, i < 45 → i ∉ [QXM, QYM, W0, W1, W2, W3, PY] → i ≠ FLAG → sv c base s₄ i = sv c base s₃ i :=
    fun hi hl hf => sv_unch U₄ h7 hn hi (apart_append (apart_slW hl)
      (show ∀ w ∈ [(own c.n, 64 * c.n)] ++ [(c.sl FLAG, 8)], _ from
        apart_append (apart_own h7 hi) (apart_flag h0 hf)))
  obtain t₄ : ∀ {j}, j < 3 → ∀ t < 64 * c.n,
      s₄.mem (off base (bitsAt c.n j + t)) = s₂.mem (off base (bitsAt c.n j + t)) :=
    fun hj t ht => by
      rw [tbl_unch U₄ h7 hj ht (tbl_apart_valW h7 h0 _ t),
        tbl_unch U₃ h7 hj ht (apart_append (tbl_apart_slW h7 (by decide) _ t) (tbl_apart_flag h7 h0 _ t))]
  have hkv : kv c Impl.Ecdh.PPC64LE.Args.ecdh s₀ = dk c s₀ := Nat.shiftRight_zero
  have hdv : dv c Impl.Ecdh.PPC64LE.Args.ecdh s₀ = dk c s₀ := Nat.shiftRight_zero
  obtain r₄ : ∀ {i}, i ∈ [RX, RY, RZ, D] → sv c base s₄ i = sv c base s₂ i := fun hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;>
      rw [e₄ (by decide) (by decide) (by decide), e₃ (by decide) (by decide) (by decide)]
  -- `[d]P`, then `Z^(p-2)`.
  refine hMul K₄ (by rw [r₄ (by simp)]; exact S₂.rx) (by rw [r₄ (by simp)]; exact S₂.ry)
    (by rw [r₄ (by simp)]; exact S₂.rz)
    (by rw [e₄ (by decide) (by decide) (by decide), e₃ (by decide) (by decide) (by decide), S₂.k, hkv])
    (fun t ht => by rw [t₄ (j := 0) (by decide) t ht, S₂.t₀ t ht, hkv])
    (fun t ht => by rw [t₄ (j := 1) (by decide) t ht, S₂.t₁ t ht])
    (by rw [e₄ (by decide) (by decide) (by decide)]; exact bp₃)
    (peerPt_onCurve hc _ _ _)
    (peerPt_rep hC _ _ _ px py |> fun h => by
      show Rep c.C (toM c.C.p (2 ^ (64 * c.n)) (sv c base s₄ PX))
        (toM c.C.p (2 ^ (64 * c.n)) (sv c base s₄ PY))
        (toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₄.mem base (c.sl ONEP) c.n)) _
      rw [K₄.fixed.onep, toM_one hpR]; exact h) px_lt py_lt fun s₅ L => ?_
  refine WP.mono (middle_ok hc L.toKeep L.acc_lt (L.flag.trans f₄) hp.out_fit (by rw [hp.wr]; simp)
    (by rw [← hb]; exact hp.out_sc))
    fun s' ⟨xv, hxl, hxv, bytes, ret, saved, sp, lr, m, Wm, Om⟩ => ⟨⟨saved, sp, lr, m, by rw [hb]; exact Wm, Om⟩, ?_⟩
  -- The specification.
  obtain hlen : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r5) (1 + 2 * c.C.len)).length = 2 * c.C.len + 1 := by
    rw [length_bytesAt]; omega_arith
  obtain hb0 : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r5) (1 + 2 * c.C.len)).head? = some (s₀.mem (s₀.gpr .r5)) := by
    rw [peer_bytes]; rfl
  obtain hxs : ofBytes (((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r5) (1 + 2 * c.C.len)).drop 1).take c.C.len) =
      sv c base s₃ E := by
    rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _), x₃,
      bytesAt_keep W₂ (hpsc.sub_left (Offset.sub_base _ (by omega_arith))) (by omega_arith) (by omega_arith)]
  obtain hys : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .r5) (1 + 2 * c.C.len)).drop (c.C.len + 1)) =
      sv c base s₃ QY := by
    rw [peer_bytes, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _), y₃,
      bytesAt_keep W₂ (hpsc.sub_left (Offset.sub_base _ (by omega_arith))) (by omega_arith) (by omega_arith)]
  obtain hP' : ∀ h : Valid c.C (s₀.mem (s₀.gpr .r5)) (sv c base s₃ E) (sv c base s₃ QY),
      peerPt c (s₀.mem (s₀.gpr .r5) = 4) (sv c base s₃ E) (sv c base s₃ QY) =
        .affine ⟨_, h.2.1⟩ ⟨_, h.2.2.1⟩ := fun h => by
    unfold peerPt; rw [dite_eq_left ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩]
  have hR := L.rep
  obtain hxoX : Fin.ofNat c.C.p xv = tmv c.C c.n base s₅ (c.sl RX) *
      tmv c.C c.n base s₅ (c.sl RZ) ^ (c.C.p - 2) := by rw [hxv, L.acc]
  obtain hspec := exchange_eq hC hlen hb0 hxs hys hP' hR hxl hxoX
  obtain hD₅ : sv c base s₅ D = dk c s₀ := by
    rw [L.same (by decide) (by decide), r₄ (by simp), S₂.d, hdv]
  obtain hz : tmv c.C c.n base s₅ (c.sl RZ) ≠ 0 ↔ sv c base s₅ RZ ≠ 0 :=
    not_congr (toM_eq_zero_iff hpR L.rz_lt)
  unfold EPost
  rw [hspec]
  by_cases hcond : (1 ≤ dk c s₀ ∧ dk c s₀ < c.C.n) ∧
      Valid c.C (s₀.mem (s₀.gpr .r5)) (sv c base s₃ E) (sv c base s₃ QY) ∧
      tmv c.C c.n base s₅ (c.sl RZ) ≠ 0
  · have hok : ok c base s₅ (PeerOk c base s₃ ((s₀.mem (s₀.gpr .r5) = 4 ∧
        sv c base s₃ E < c.C.p) ∧ sv c base s₃ QY < c.C.p)) = true := by
      refine decide_eq_true ⟨⟨⟨⟨⟨hcond.2.1.1, hcond.2.1.2.1⟩, hcond.2.1.2.2.1⟩, hcond.2.1.2.2.2⟩, ?_, ?_⟩,
        hz.mp hcond.2.2⟩
      · rw [hD₅]; exact hcond.1.1
      · rw [hD₅]; exact hcond.1.2
    rw [ite_eq_left hcond]
    exact ⟨by rw [ret, hok]; rfl, by rw [bytes, hok]; rfl⟩
  · have hok : ok c base s₅ (PeerOk c base s₃ ((s₀.mem (s₀.gpr .r5) = 4 ∧
        sv c base s₃ E < c.C.p) ∧ sv c base s₃ QY < c.C.p)) = false := by
      refine decide_eq_false fun h => hcond ⟨⟨?_, ?_⟩, ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2⟩,
        hz.mpr h.2⟩
      · rw [← hD₅]; exact h.1.2.1
      · rw [← hD₅]; exact h.1.2.2
    rw [ite_eq_right hcond]
    exact ⟨by rw [ret, hok]; rfl, by rw [bytes, hok]; rfl⟩

/-- `vg_ecdh_<curve>` computes the specification's shared secret and restores
the callee-saved registers and `lr`. -/
theorem exchange_ok (hc : CfgOk c) (h3 : 3 ≤ c.n) (hC : Law c.C) {s₀ : State} (hp : EPre c s₀) :
    WP isa (Impl.Ecdh.PPC64LE.Cfg.exchange c) s₀ fun s' => EKeep c s₀ s' ∧ EPost c s₀ s' :=
  exchangeWith_ok hc hC hp (qMul_mulPowOk hc h3 hC s₀)

end VG.Proof.Ecdh.PPC64LE

module

public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Layout
public import VerifiedGarbage.Impl.Ecdh.PPC64LE
public import VerifiedGarbage.Proof.Weierstrass.PPC64LE.MontCall
public import VerifiedGarbage.Proof.Weierstrass.Unch
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Flags
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Setup
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Bits
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.BytesLen
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Keep
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

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
  have hF : c.sl FLAG + 8 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega_arith
  have hR2 := sl_le c h7 (i := R2P) (by decide)
  have hB := sl_le c h7 (i := BP) (by decide)
  have hY := sl_le c h7 (i := QY) (by decide)
  have hE := sl_le c h7 (i := E) (by decide)
  have hM := sl_le c h7 (i := MP) (by decide)
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
  have hw₁ := hw.of_kp k₁
  have U₁' : Unch base (slW c [R2P, BP]) s.mem s₁.mem := U₁
  -- `peer + 1`
  refine wp_step (exec_addi hq0 (by decide)) ?_
  have k₂ : Kp [.r6, .r11] s (s₁.write .r6 (s₁.gpr q + BitVec.ofNat 64 1)) :=
    (k₁.mono (by decide)).trans (Kp.write _ _ (by decide))
  have hq₁ : s₁.gpr q = qa := by rw [k₁.gpr q (by simp [hq11]), hqa]
  have hrw : ∀ {t : State} {rs : List Reg}, Kp rs s t → t.rd ++ t.wr = s.rd ++ s.wr := fun K => by
    rw [K.rd, K.wr]
  have O₁ : Outside base 0 4096 s.mem s₁.mem := U₁'.outside fun w hw => by
    simp only [slW, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl <;> exact ⟨Nat.zero_le _, by dsimp only; omega_arith⟩
  have hfit₁ : (qa + BitVec.ofNat 64 1).toNat + c.C.len ≤ 2 ^ 64 := by
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
  have K₃ : Kp [.r6, .r8, .r9, .r11] s s₃ :=
    (k₂.mono (by decide)).trans (k₃.mono (by decide))
  have hw₃ := hw.of_kp K₃
  have r6₃ : s₃.gpr .r6 = qa + BitVec.ofNat 64 1 := by
    rw [k₃.gpr _ (by decide)]; simp only [write_gpr, ite_true, hq₁]
  -- `peer + 1 + len`
  refine wp_step (exec_addi (by decide) (show c.C.len < 2 ^ 15 by omega_arith)) ?_
  have K₄ : Kp [.r6, .r8, .r9, .r11] s (s₃.write .r6 (s₃.gpr .r6 + BitVec.ofNat 64 c.C.len)) :=
    K₃.trans (Kp.write _ _ (by decide))
  have hfit₂ : (qa + BitVec.ofNat 64 (1 + c.C.len)).toNat + c.C.len ≤ 2 ^ 64 := by
    rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (show 1 + c.C.len < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  have O₃' : Outside base 0 4096 s.mem s₃.mem :=
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
  have K₅ : Kp [.r6, .r8, .r9, .r11] s s₅ := K₄.trans (k₅.mono (by decide))
  have hw₅ := hw.of_kp K₅
  have hq₅ : s₅.gpr q = qa := by rw [K₅.gpr q (by simp [hq6, hq8, hq9, hq11]), hqa]
  have O₅' : Outside base 0 size s.mem s₅.mem :=
    (O₃'.mono (Nat.le_refl _) (by omega_arith)).trans (O₅.mono (Nat.zero_le _) (by omega_arith))
  -- the first byte
  refine wp_append (WP.mono (checkLead_ok c hw₅.ws hw₅.at3 (q := q) hq0
    ⟨_, by rw [hrw K₅]; exact hin, by
      have := Offset.contains_base qa (d := 0) (n := 1) (k := 1 + 2 * c.C.len) (by omega_arith) (by omega_arith)
      rw [BitVec.add_zero] at this; rw [hq₅]; exact this⟩ hF) fun s₆ ⟨f₆, k₆, O₆⟩ => ?_)
  rw [hq₅] at f₆
  have hw₆ := hw₅.of_kp k₆
  -- `x < p`
  refine wp_append (WP.mono (checkLtP_ok c hw₆.ws hw₆.at3 (by omega_arith) (by omega_arith) hF) fun s₇ ⟨f₇, k₇, O₇⟩ => ?_)
  have hw₇ := hw₆.of_kp k₇
  -- `y < p`
  refine WP.mono (checkLtP_ok c hw₇.ws hw₇.at3 (by omega_arith) (by omega_arith) hF) fun s₈ ⟨f₈, k₈, O₈⟩ => ?_
  -- The slots.
  have UF : Unch base ([(c.sl FLAG, 8)] ++ [(c.sl FLAG, 8)] ++ [(c.sl FLAG, 8)]) s₅.mem s₈.mem :=
    (O₆.unch.trans O₇.unch).trans O₈.unch
  have apF : ∀ {i}, i < 45 → i ≠ FLAG →
      ∀ w ∈ [(c.sl FLAG, 8)] ++ [(c.sl FLAG, 8)] ++ [(c.sl FLAG, 8)],
        c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := fun hi hf =>
    apart_append (apart_append (apart_flag h0 hf) (apart_flag h0 hf)) (apart_flag h0 hf)
  have v₈ : ∀ {i}, i < 45 → i ≠ FLAG → sv c base s₈ i = sv c base s₅ i := fun hi hf =>
    sv_unch UF h7 hn hi (apF hi hf)
  have U₁₅ : Unch base [(c.sl E, 8 * c.n), (c.sl QY, 8 * c.n)] s₁.mem s₅.mem := O₃.unch.trans O₅.unch
  have v₅ : ∀ {i}, i < 45 → i ∉ [E, QY] → sv c base s₅ i = sv c base s₁ i := fun hi hl =>
    sv_unch U₁₅ h7 hn hi (apart_slW (c := c) (l := [E, QY]) hl)
  have v₁ : ∀ {i}, i < 45 → i ∉ [R2P, BP] → sv c base s₁ i = sv c base s i := fun hi hl =>
    sv_unch U₁' h7 hn hi (apart_slW (c := c) (l := [R2P, BP]) hl)
  have xE : sv c base s₈ E = ofBytes (Spec.Ecdsa.bytesAt s.mem (qa + BitVec.ofNat 64 1) c.C.len) := by
    rw [v₈ (by decide) (by decide), ← e₃]
    exact sv_unch O₅.unch h7 hn (i := E) (by decide) (apart_slW (c := c) (l := [QY]) (by decide))
  have yQ : sv c base s₈ QY =
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
    have mp₆ : wordsVal s₆.mem base (c.sl MP) c.n = c.C.p :=
      (sv_unch O₆.unch h7 hn (i := MP) (by decide) (apart_flag h0 (by decide))).trans mp₅
    have mp₇ : wordsVal s₇.mem base (c.sl MP) c.n = c.C.p :=
      (sv_unch O₇.unch h7 hn (i := MP) (by decide) (apart_flag h0 (by decide))).trans mp₆
    have e₆ : wordsVal s₆.mem base (c.sl E) c.n = sv c base s₈ E :=
      ((sv_unch O₆.unch h7 hn (i := E) (by decide) (apart_flag h0 (by decide))).trans
        (v₈ (by decide) (by decide)).symm)
    have y₇ : wordsVal s₇.mem base (c.sl QY) c.n = sv c base s₈ QY :=
      (sv_unch O₈.unch h7 hn (i := QY) (by decide) (apart_flag h0 (by decide))).symm
    have hFl := sl_le c h7 (i := FLAG) (by decide)
    have fl₅ : flagW c base s₅ = flagW c base s := by
      have ap : ∀ w ∈ slW c [R2P, BP] ++ [(c.sl E, 8 * c.n), (c.sl QY, 8 * c.n)],
          c.sl FLAG + 8 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG := fun w hw =>
        (apart_slW (c := c) (l := [R2P, BP, E, QY]) (i := FLAG) (by decide) w (by
          simp only [slW, List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil,
            or_false] at hw ⊢; grind)).imp (fun h => by omega_arith) id
      exact (U₁'.trans U₁₅).word ap (by omega_arith)
    have lead₅ : s₅.mem qa = s.mem qa := by
      have := keep_of_disjoint' O₅' hd (by omega_arith) (i := 0) (by omega_arith) (by omega_arith)
      rwa [BitVec.add_zero] at this
    rw [f₈, f₇, f₆, fl₅, lead₅, e₆, mp₆, y₇, mp₇]

end VG.Proof.Ecdh.PPC64LE

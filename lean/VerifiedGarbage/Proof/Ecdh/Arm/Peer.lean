import VerifiedGarbage.Impl.Ecdh.Arm
import VerifiedGarbage.Proof.Ecdsa.Arm.Finish
import VerifiedGarbage.Proof.Ecdsa.Arm.Scalar
import VerifiedGarbage.Proof.Weierstrass.Arm.Copy

/-!
# ECDH on 32-bit ARM: reading and checking the peer's key

As on x86 (`Proof/Ecdh/X86/Peer.lean`).

## The checks

Each check ands a mask into the flag, as the signature's checks do
(`Proof/Ecdsa/Arm/Flags.lean`): the peer's first byte is `04`
(`checkLead_ok`: the top bit of `(byte ^ 4) - 1`, negated), a number is
below `p` (`checkLtP_ok`, the signature's comparison `ltM` with `MP`) and a
number is zero (`checkZero_ok`, `-(-m) - 1` of `nonzero`'s mask `m`).
-/

namespace VG.Proof.Ecdh.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.Arm
open VG.Proof.X25519.Arm (Rest Upd wp_ldrb wp_dp wp_mov op2_reg op2_imm op2_lsr dpVal ea toNat_add_lt toNat_imm)

/-! ## Below `p` -/

/-- `checkLtP a`: the flag `&=` the mask of `[a] < [MP]`. -/
theorem checkLtP_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (ha : a + 8 * c.n ≤ size) (hm : c.sl MP + 8 * c.n ≤ size) (hf : c.sl FLAG + 4 ≤ size) :
    WP isa (.block (Impl.Ecdh.Arm.Cfg.checkLtP c a)) s fun s' =>
      flagW c base s' = flagW c base s &&&
        mask32 (wordsVal s.mem base a c.n < wordsVal s.mem base (c.sl MP) c.n) ∧
      Rest [.r3, .r4, .r5, .r6, .r7, .r8] s s' ∧ Outside base (c.sl FLAG) 4 s.mem s'.mem := by
  rw [Impl.Ecdh.Arm.Cfg.checkLtP]
  refine VG.Proof.X25519.Arm.WP.append (ltM_ok c hs ha hm) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_
  refine WP.mono (andFlag_ok c (hs.of_rest k₁ (by decide)) hf) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  exact ⟨by rw [e₂, e₁, flagW, flagW, m₁], k₁.trans (k₂.mono (by simp)), by rw [← m₁]; exact O₂⟩

/-! ## Zero -/

theorem mask_not (P : Prop) [Decidable P] : (0 : BitVec 32) - mask32 P - 1 = mask32 ¬P := by
  by_cases h : P <;> simp only [mask32, h, not_true, not_false_eq_true, ite_true, ite_false] <;> decide

/-- `checkZero a`: the flag `&=` the mask of `[a] = 0`. -/
theorem checkZero_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {a : Nat}
    (hn : 0 < c.n) (ha : a + 8 * c.n ≤ size) (hf : c.sl FLAG + 4 ≤ size) :
    WP isa (.block (Impl.Ecdh.Arm.Cfg.checkZero c a)) s fun s' =>
      flagW c base s' = flagW c base s &&& mask32 (wordsVal s.mem base a c.n = 0) ∧
      Rest [.r4, .r5] s s' ∧ Outside base (c.sl FLAG) 4 s.mem s'.mem := by
  rw [Impl.Ecdh.Arm.Cfg.checkZero, List.append_assoc]
  refine VG.Proof.X25519.Arm.WP.append (nonzero_ok c hs hn ha) fun s₁ ⟨e₁, k₁, m₁⟩ => ?_
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
  refine wp_dp (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_dp (op2_imm (by decide)) fun s₄ u₄ => ?_
  have k₄ : Rest [.r4, .r5] s s₄ :=
    k₁.trans ((u₂.rest (by simp)).trans ((u₃.rest (by simp)).trans (u₄.rest (by simp))))
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, m₁]
  refine WP.mono (andFlag_ok c (hs.of_rest k₄ (by decide)) hf) fun s₅ ⟨e₅, k₅, O₅⟩ =>
    ⟨?_, k₄.trans (k₅.mono (by simp)), by rw [← m₄]; exact O₅⟩
  have r₄ : s₄.gpr .r5 = mask32 (wordsVal s.mem base a c.n = 0) := by
    rw [u₄.gpr, u₃.gpr, u₂.gpr, u₂.other _ (by decide), e₁]
    simp only [dpVal]
    rw [mask_not]
    simp only [ne_eq, Decidable.not_not]
  rw [e₅, flagW, flagW, m₄, r₄]

/-! ## The first byte -/

/-- `-(((b ^ 4) - 1) >>> 31)` is the mask of `b = 4`, for a byte `b`. -/
theorem lead_mask (b : BitVec 8) :
    (0 : BitVec 32) - ((b.setWidth 32 ^^^ 4) - 1) >>> 31 = mask32 (b = 4) := by
  revert b; decide

/-- `checkLead q`: the flag `&=` the mask of the byte `q` points to being `04`. -/
theorem checkLead_ok (c : Cfg) {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {q : Reg}
    (hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr q)) 1) (hf : c.sl FLAG + 4 ≤ size) :
    WP isa (.block (Impl.Ecdh.Arm.Cfg.checkLead c q)) s fun s' =>
      flagW c base s' = flagW c base s &&& mask32 (s.mem (State.addr (s.gpr q)) = 4) ∧
      Rest [.r4, .r5] s s' ∧ Outside base (c.sl FLAG) 4 s.mem s'.mem := by
  simp only [Impl.Ecdh.Arm.Cfg.checkLead, List.cons_append, List.nil_append]
  refine wp_ldrb (by decide) (congrArg State.addr (BitVec.add_zero _)) hin fun s₁ u₁ => ?_
  refine wp_dp (op2_imm (by decide)) fun s₂ u₂ => ?_
  refine wp_dp (op2_imm (by decide)) fun s₃ u₃ => ?_
  refine wp_mov (op2_lsr (by decide)) fun s₄ u₄ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₅ u₅ => ?_
  refine wp_dp (op2_reg _ _) fun s₆ u₆ => ?_
  have k₆ : Rest [.r4, .r5] s s₆ := (u₁.rest (by simp)).trans ((u₂.rest (by simp)).trans ((u₃.rest (by simp)).trans
    ((u₄.rest (by simp)).trans ((u₅.rest (by simp)).trans (u₆.rest (by simp))))))
  have m₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine WP.mono (andFlag_ok c (hs.of_rest k₆ (by decide)) hf) fun s₇ ⟨e₇, k₇, O₇⟩ =>
    ⟨?_, k₆.trans (k₇.mono (by simp)), by rw [← m₆]; exact O₇⟩
  have r₆ : s₆.gpr .r5 = mask32 (s.mem (State.addr (s.gpr q)) = 4) := by
    rw [u₆.gpr, u₅.gpr, u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr]
    simp only [dpVal]
    exact lead_mask _
  rw [e₇, flagW, flagW, m₆, r₆]

/-!
## Reading the peer's key

`peerAt q` stores `R² mod p` and `b R mod p`, reads the `x` and `y` of the
key `q` points to into their slots (through `r6`, from its byte 1), and ands
into the flag the masks of the peer's first byte being `04`, `x < p` and
`y < p` (`peer_ok`). It writes only those slots and the flag, in the working
space, which the peer's key is apart from.
-/

variable {c : Cfg}

open VG.Impl.Ecdh.Arm (QY R2P BP)

theorem peer_eq (c : Cfg) (q : Reg) : Impl.Ecdh.Arm.Cfg.peerAt c q =
    setConst c.n (c.sl R2P) (c.R * c.R % c.C.p) ++ (setConst c.n (c.sl BP) (c.mont c.C.b) ++
    (.dp .add .r6 q (.imm 1) :: (loadBytes c.C.len c.n (c.sl E) .r6 ++
    (.dp .add .r6 .r6 (.imm (BitVec.ofNat 32 c.C.len)) :: (loadBytes c.C.len c.n (c.sl QY) .r6 ++
    (Impl.Ecdh.Arm.Cfg.checkLead c q ++
    (Impl.Ecdh.Arm.Cfg.checkLtP c (c.sl E) ++ Impl.Ecdh.Arm.Cfg.checkLtP c (c.sl QY)))))))) := by
  simp only [Impl.Ecdh.Arm.Cfg.peerAt, Impl.Ecdh.Arm.Cfg.consts, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- A slot apart from the one an operation wrote keeps its number. -/
theorem sv_out {base : Addr} {m m' : Mem} {j : Nat} (h : Outside base (c.sl j) (8 * c.n) m m')
    (h7 : c.n < 10) (hn : base.toNat + size ≤ 2 ^ 32) {i : Nat} (hi : i < 45) (hij : i ≠ j) :
    wordsVal m' base (c.sl i) c.n = wordsVal m base (c.sl i) c.n := by
  have := sl_le c h7 hi
  exact h.wordsVal (sl_apart c hij) (by omega_arith)

/-- The constants, the key's `x` and `y`, and the checks of its first byte,
`x` and `y`, for a key that `q` points to. -/
theorem peer_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size) {q : Reg}
    (hq4 : q ≠ .r4) (hq6 : q ≠ .r6) (hqfit : (s.gpr q).toNat + (1 + 2 * c.C.len) ≤ 2 ^ 32)
    (hin : (⟨State.addr (s.gpr q), 1 + 2 * c.C.len⟩ : Region) ∈ s.rd ++ s.wr)
    (hd : Region.Disjoint ⟨State.addr (s.gpr q), 1 + 2 * c.C.len⟩ ⟨base, size⟩) (hmp : sv c base s MP = c.C.p) :
    WP isa (.block (Impl.Ecdh.Arm.Cfg.peerAt c q)) s fun s' =>
      Scr s' base size ∧ Rest [.r3, .r4, .r5, .r6, .r7, .r8] s s' ∧
      Unch base (slW c [R2P, BP, E, QY] ++ [(c.sl FLAG, 4)]) s.mem s'.mem ∧
      sv c base s' R2P = c.R * c.R % c.C.p ∧ sv c base s' BP = c.mont c.C.b ∧
      sv c base s' E = ofBytes (Spec.Ecdsa.bytesAt s.mem (State.addr (s.gpr q) + BitVec.ofNat 64 1) c.C.len) ∧
      sv c base s' QY =
        ofBytes (Spec.Ecdsa.bytesAt s.mem (State.addr (s.gpr q) + BitVec.ofNat 64 (1 + c.C.len)) c.C.len) ∧
      flagW c base s' = flagW c base s &&& mask32 (s.mem (State.addr (s.gpr q)) = 4) &&&
        mask32 (sv c base s' E < c.C.p) &&& mask32 (sv c base s' QY < c.C.p) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpl := hc.p_lt
  have hp3 := hc.p_ge
  have hl8 := hc.len8
  have hlhi := hc.len_hi
  have hF : c.sl FLAG + 4 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega_arith
  have hR2 := sl_le c h7 (i := R2P) (by decide)
  have hB := sl_le c h7 (i := BP) (by decide)
  have hY := sl_le c h7 (i := QY) (by decide)
  have hE := sl_le c h7 (i := E) (by decide)
  have hM := sl_le c h7 (i := MP) (by decide)
  have hq : q ∉ [Reg.r4, .r6] := by simp [hq4, hq6]
  generalize hq32 : s.gpr q = q32 at hqfit hin hd ⊢
  generalize hq64 : State.addr q32 = qa at hin hd ⊢
  rw [peer_eq]
  -- The constants.
  refine VG.Proof.X25519.Arm.WP.append (setConst_ok hs hR2 (show c.R * c.R % c.C.p < 2 ^ (64 * c.n) from
    Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) hpl)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_rest k₁ (by decide)
  refine VG.Proof.X25519.Arm.WP.append (setConst_ok hs₁ hB (show c.mont c.C.b < 2 ^ (64 * c.n) from
    Nat.lt_trans (Nat.mod_lt _ (by omega_arith)) hpl)) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_rest k₂ (by decide)
  have W₂ : Outside base 0 size s.mem s₂.mem :=
    (O₁.mono (Nat.zero_le _) (by omega_arith)).trans (O₂.mono (Nat.zero_le _) (by omega_arith))
  have K₂ : Rest [.r4] s s₂ := k₁.trans k₂
  -- `peer + 1`
  refine wp_dp (op2_imm (by decide)) fun s₃ u₃ => ?_
  have K₃ : Rest [.r4, .r6] s s₃ := (K₂.mono (by simp)).trans (u₃.rest (by simp))
  have hs₃ := hs.of_rest K₃ (by decide)
  have hm₃ : s₃.mem = s₂.mem := u₃.mem
  have hrw₃ : s₃.rd ++ s₃.wr = s.rd ++ s.wr := by rw [K₃.rd, K₃.wr]
  have hb₃ : s₃.gpr .r6 = q32 + BitVec.ofNat 32 1 := by
    rw [u₃.gpr, K₂.gpr _ (by simp [hq4]), hq32]; rfl
  have ha₃ : State.addr (s₃.gpr .r6) = qa + BitVec.ofNat 64 1 := by
    rw [hb₃, ← hq64]; exact ea (by omega_arith)
  have ht₃ : (s₃.gpr .r6).toNat = q32.toNat + 1 := by
    rw [hb₃, toNat_add_lt (by rw [toNat_imm (by decide)]; omega_arith), toNat_imm (by decide)]
  -- `x`
  refine VG.Proof.X25519.Arm.WP.append (loadBytes_ok hs₃ (src := .r6) (by decide) hE (by omega_arith) (by omega_arith) hlhi
    (fun e he => ⟨_, by rw [hrw₃]; exact hin, by
      rw [ha₃, Offset.add_add]; exact Offset.contains_base qa (by omega_arith) (by omega_arith)⟩)
    (by rw [ha₃]; exact (hd.sub_left (Offset.sub_base qa (by omega_arith))).sub_right (Offset.sub_base base hE)))
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  rw [ha₃, hm₃] at e₄
  rw [hm₃] at O₄
  have hs₄ := hs₃.of_rest k₄ (by decide)
  -- `peer + 1 + len`
  refine wp_dp (op2_imm (encLen hc)) fun s₅ u₅ => ?_
  have K₅ : Rest [.r4, .r6] s s₅ := (K₃.trans (k₄.mono (by simp))).trans (u₅.rest (by simp))
  have hs₅ := hs.of_rest K₅ (by decide)
  have hrw₅ : s₅.rd ++ s₅.wr = s.rd ++ s.wr := by rw [K₅.rd, K₅.wr]
  have hb₅ : s₅.gpr .r6 = q32 + BitVec.ofNat 32 (1 + c.C.len) := by
    rw [u₅.gpr, k₄.gpr _ (by decide), hb₃]
    exact Offset.add_add _ _ _
  have ha₅ : State.addr (s₅.gpr .r6) = qa + BitVec.ofNat 64 (1 + c.C.len) := by
    rw [hb₅, ← hq64]; exact ea (by omega_arith)
  have ht₅ : (s₅.gpr .r6).toNat = q32.toNat + (1 + c.C.len) := by
    rw [hb₅, toNat_add_lt (by rw [toNat_imm (by omega_arith)]; omega_arith), toNat_imm (by omega_arith)]
  -- `y`
  refine VG.Proof.X25519.Arm.WP.append (loadBytes_ok hs₅ (src := .r6) (by decide) hY (by omega_arith) (by omega_arith) hlhi
    (fun e he => ⟨_, by rw [hrw₅]; exact hin, by
      rw [ha₅, Offset.add_add]; exact Offset.contains_base qa (by omega_arith) (by omega_arith)⟩)
    (by rw [ha₅]; exact (hd.sub_left (Offset.sub_base qa (by omega_arith))).sub_right (Offset.sub_base base hY)))
    fun s₆ ⟨e₆, k₆, O₆⟩ => ?_
  rw [ha₅, u₅.mem] at e₆
  rw [u₅.mem] at O₆
  have K₆ : Rest [.r4, .r6] s s₆ := K₅.trans (k₆.mono (by simp))
  have hs₆ := hs.of_rest K₆ (by decide)
  have W₆ : Outside base 0 size s.mem s₆.mem :=
    ((W₂.trans (O₄.mono (Nat.zero_le _) (by omega_arith))).trans (O₆.mono (Nat.zero_le _) (by omega_arith)))
  have hrw₆ : s₆.rd ++ s₆.wr = s.rd ++ s.wr := by rw [K₆.rd, K₆.wr]
  have hq₆ : State.addr (s₆.gpr q) = qa := by rw [K₆.gpr _ hq, hq32, hq64]
  -- the first byte
  refine VG.Proof.X25519.Arm.WP.append (checkLead_ok c hs₆ (q := q)
    ⟨_, by rw [hrw₆]; exact hin, by
      have := Offset.contains_base qa (d := 0) (n := 1) (k := 1 + 2 * c.C.len) (by omega_arith) (by omega_arith)
      rw [BitVec.add_zero] at this; rw [hq₆]; exact this⟩ hF) fun s₇ ⟨f₇, k₇, O₇⟩ => ?_
  rw [hq₆] at f₇
  have hs₇ := hs₆.of_rest k₇ (by decide)
  -- `x < p`
  refine VG.Proof.X25519.Arm.WP.append (checkLtP_ok c hs₇ hE hM hF) fun s₈ ⟨f₈, k₈, O₈⟩ => ?_
  have hs₈ := hs₇.of_rest k₈ (by decide)
  -- `y < p`
  refine WP.mono (checkLtP_ok c hs₈ hY hM hF) fun s₉ ⟨f₉, k₉, O₉⟩ => ?_
  -- The slots.
  have v₆ : ∀ {i}, i < 45 → i ≠ R2P → i ≠ BP → i ≠ E → i ≠ QY →
      wordsVal s₆.mem base (c.sl i) c.n = wordsVal s.mem base (c.sl i) c.n :=
    fun hi h₁ h₂ h₃ h₄ => by
      rw [sv_out O₆ h7 hn hi h₄, sv_out O₄ h7 hn hi h₃, sv_out O₂ h7 hn hi h₂, sv_out O₁ h7 hn hi h₁]
  have v₉ : ∀ {i}, i < 45 → i ≠ FLAG →
      wordsVal s₉.mem base (c.sl i) c.n = wordsVal s₆.mem base (c.sl i) c.n := fun hi hf =>
    ((sv_flag O₉ h0 h7 hn hi hf).trans (sv_flag O₈ h0 h7 hn hi hf)).trans (sv_flag O₇ h0 h7 hn hi hf)
  have flag₆ : flagW c base s₆ = flagW c base s := by
    have hap : ∀ {j}, j < 45 → j ≠ FLAG → c.sl FLAG + 4 ≤ c.sl j ∨ c.sl j + 8 * c.n ≤ c.sl FLAG :=
      fun hj hjf => by have := sl_apart c (Ne.symm hjf) (i := FLAG); omega_arith
    rw [flagW, flagW, BitVec.eq_of_toNat_eq (O₆.w32 (hap (j := QY) (by decide) (by decide)) (by omega_arith)),
      BitVec.eq_of_toNat_eq (O₄.w32 (hap (j := E) (by decide) (by decide)) (by omega_arith)),
      BitVec.eq_of_toNat_eq (O₂.w32 (hap (j := BP) (by decide) (by decide)) (by omega_arith)),
      BitVec.eq_of_toNat_eq (O₁.w32 (hap (j := R2P) (by decide) (by decide)) (by omega_arith))]
  have mp₆ : wordsVal s₆.mem base (c.sl MP) c.n = c.C.p :=
    (v₆ (i := MP) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hmp
  have xE : sv c base s₉ E = ofBytes (Spec.Ecdsa.bytesAt s.mem (qa + BitVec.ofNat 64 1) c.C.len) := by
    show wordsVal s₉.mem _ _ _ = _
    rw [v₉ (i := E) (by decide) (by decide), sv_out O₆ h7 hn (by decide) (by decide), e₄]
    exact congrArg Spec.Weierstrass.ofBytes (bytesAt_keep W₂ ((hd.sub_left (Offset.sub_base qa (by omega_arith))))
      (by omega_arith) (by omega_arith))
  have yQ : sv c base s₉ QY =
      ofBytes (Spec.Ecdsa.bytesAt s.mem (qa + BitVec.ofNat 64 (1 + c.C.len)) c.C.len) := by
    show wordsVal s₉.mem _ _ _ = _
    rw [v₉ (i := QY) (by decide) (by decide), e₆]
    exact congrArg Spec.Weierstrass.ofBytes (bytesAt_keep (W₂.trans (O₄.mono (Nat.zero_le _) (by omega_arith)))
      (hd.sub_left (Offset.sub_base qa (by omega_arith))) (by omega_arith) (by omega_arith))
  refine ⟨hs₈.of_rest k₉ (by decide), ?_, ?_, ?_, ?_, xE, yQ, ?_⟩
  · exact ((K₆.mono (by simp)).trans (k₇.mono (by simp))).trans (k₈.trans k₉)
  · have U := (((((O₁.unch.trans O₂.unch).trans O₄.unch).trans O₆.unch).trans O₇.unch).trans
      O₈.unch).trans O₉.unch
    refine U.mono fun w hw => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.map_cons, List.map_nil, slW] at hw ⊢
    grind
  · show wordsVal s₉.mem _ _ _ = _
    rw [v₉ (i := R2P) (by decide) (by decide), sv_out O₆ h7 hn (by decide) (by decide),
      sv_out O₄ h7 hn (by decide) (by decide), sv_out O₂ h7 hn (by decide) (by decide), e₁]
  · show wordsVal s₉.mem _ _ _ = _
    rw [v₉ (i := BP) (by decide) (by decide), sv_out O₆ h7 hn (by decide) (by decide),
      sv_out O₄ h7 hn (by decide) (by decide), e₂]
  · have mp₇ : wordsVal s₇.mem base (c.sl MP) c.n = c.C.p := by
      rw [sv_flag O₇ h0 h7 hn (i := MP) (by decide) (by decide)]; exact mp₆
    have mp₈ : wordsVal s₈.mem base (c.sl MP) c.n = c.C.p := by
      rw [sv_flag O₈ h0 h7 hn (i := MP) (by decide) (by decide)]; exact mp₇
    have e₇ : wordsVal s₇.mem base (c.sl E) c.n = sv c base s₉ E :=
      (((sv_flag O₉ h0 h7 hn (i := E) (by decide) (by decide)).trans
        (sv_flag O₈ h0 h7 hn (i := E) (by decide) (by decide)))).symm
    have y₈ : wordsVal s₈.mem base (c.sl QY) c.n = sv c base s₉ QY :=
      (sv_flag O₉ h0 h7 hn (i := QY) (by decide) (by decide)).symm
    have lead₆ : s₆.mem qa = s.mem qa := by
      have := keep_of_disjoint' W₆ hd (by omega_arith) (i := 0) (by omega_arith) (by omega_arith)
      rwa [BitVec.add_zero] at this
    rw [f₉, f₈, f₇, flag₆, lead₆, e₇, mp₇, y₈, mp₈]

end VG.Proof.Ecdh.Arm

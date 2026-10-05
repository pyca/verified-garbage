import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Impl.Rc2.AArch64.Block
import VerifiedGarbage.Impl.Rc2.AArch64.Lookup
import VerifiedGarbage.Proof.Rc2.Stream
import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Spill
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Rc2.AArch64.ExpandKey
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Rc2.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Lookup`. -/
section

/-! # Correctness of baseline AArch64 RC2 lookup steps -/

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Tbl VG.Impl.Tbl.AArch64 VG.Impl.Rc2.AArch64

/-- A register-only block preserves memory, regions, and other GPRs. -/
structure Keep (written : List Reg) (s s' : State) : Prop where
  reg : ∀ r, r ∉ written → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Keep.trans {rs : List Reg} {s s' s'' : State}
    (h : VG.Proof.Rc2.AArch64.Keep rs s s') (h' : VG.Proof.Rc2.AArch64.Keep rs s' s'') : VG.Proof.Rc2.AArch64.Keep rs s s'' :=
  ⟨fun r hr => (h'.reg r hr).trans (h.reg r hr), h'.mem.trans h.mem,
    h'.rd.trans h.rd, h'.wr.trans h.wr⟩

theorem byte_imm (b : Byte) : (BitVec.ofNat 16 b.toNat).setWidth 64 = b.setWidth 64 := by
  simp

theorem index_imm (i : Nat) (hi : i < 256) :
    (BitVec.ofNat 16 i).setWidth 64 = (BitVec.ofNat 8 i).setWidth 64 := by
  have h : BitVec.ofNat 16 i = (BitVec.ofNat 8 i).setWidth 16 := by bv_omega
  rw [h]; simp

theorem Keep.weaken {rs rs' : List Reg} {s s' : State} (h : VG.Proof.Rc2.AArch64.Keep rs s s')
    (hsub : ∀ r ∈ rs, r ∈ rs') : VG.Proof.Rc2.AArch64.Keep rs' s s' :=
  ⟨fun r hr => h.reg r (fun hm => hr (hsub r hm)), h.mem, h.rd, h.wr⟩

theorem maskBits (x : BitVec 64) (n : Nat) (hn : n ≤ 64) :
    x <<< (64 - n) >>> (64 - n) = (x.setWidth n).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth]
  have ha : 64 - n + i < 64 ↔ i < n := by omega
  have hb : ¬64 - n + i < 64 - n := by omega
  simp only [ha, hb, hi, decide_true, decide_false, Bool.not_false,
    Bool.and_true, Bool.true_and, Nat.add_sub_cancel_left]

theorem scheduleAt_getD (m : Mem) (p : Addr) (i : Nat) (hi : i < 64) :
    (Spec.Rc2.scheduleAt m p).getD i 0 =
      (m (p + BitVec.ofNat 64 (2 * i))).setWidth 16 |||
        (m (p + BitVec.ofNat 64 (2 * i + 1))).setWidth 16 <<< 8 := by
  simp [Spec.Rc2.scheduleAt, Vector.getD, hi]

/-! ## Instructions -/

theorem exec_imm (s : State) (r : Reg) (n : Nat) (hn : n < 65536) :
    exec (imm r n) s = some (s.write .x r (BitVec.ofNat 64 n)) := by
  simp only [imm, exec, Size.bits, show 16 * 0 < 64 by decide, ite_true, Option.some.injEq]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mul_zero,
    Nat.shiftLeft_zero]
  omega


/-! ## The indices -/

theorem quarters_run (full : Bool) (s : State) :
    ∃ s', runBlock isa (quarters full) s = some s' ∧
      (∀ e < 16, vbyte (s'.v .v1) e = vbyte (s.v .v0) e ^^^ 64) ∧
      (full = true → ∀ e < 16, vbyte (s'.v .v2) e = vbyte (s.v .v0) e ^^^ 128 ∧
        vbyte (s'.v .v3) e = vbyte (s.v .v0) e ^^^ 192) ∧
      (∀ w, w ≠ .v1 → w ≠ .v2 → w ≠ .v3 → w ≠ .v4 → w ≠ .v5 → s'.v w = s.v w) ∧
      VG.Proof.Rc2.AArch64.Keep [.x6] s s' := by
  let s₁ := s.write .x .x6 (BitVec.ofNat 64 64)
  let s₂ := s₁.setV .v4 (bc ((s₁.gpr .x6).setWidth 8))
  let s₃ := s₂.setV .v1 (s₂.v .v0 ^^^ s₂.v .v4)
  have k₃ : VG.Proof.Rc2.AArch64.Keep [.x6] s s₃ :=
    ⟨fun r hr => gpr_write_of_ne _ _ _ (fun e => hr (by simp [e])), rfl, rfl, rfl⟩
  have h4 : s₃.v .v4 = bc 64 := by
    simp only [s₃, s₂, v_setV_of_ne _ _ (by decide : VReg.v4 ≠ .v1), v_setV_self, s₁,
      gpr_write_self, BitVec.setWidth_eq]; rfl
  have h0 : s₃.v .v0 = s.v .v0 := by
    simp only [s₃, s₂, v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v1),
      v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v4)]; rfl
  have h1 : ∀ e < 16, vbyte (s₃.v .v1) e = vbyte (s.v .v0) e ^^^ 64 := by
    intro e he
    have : s₃.v .v1 = s.v .v0 ^^^ bc 64 := by
      rw [show s₃.v .v1 = s₂.v .v0 ^^^ s₂.v .v4 from v_setV_self _ _ _]
      rw [← h4, ← h0]; rfl
    rw [this, vbyte_xor, vbyte_bc _ he]
  have run₃ : runBlock isa ([imm .x6 64, .vop (.dup .b16 .v4 .x6), .vop (.logic .eor .v1 .v0 .v4)]) s
      = some s₃ := by
    rw [runBlock_cons, VG.Proof.Rc2.AArch64.exec_imm _ _ _ (by decide), runStep_some, runBlock_cons, exec_dupb,
      runStep_some, runBlock_cons, exec_eorv, runStep_some, runBlock_nil]
  have other₃ : ∀ w, w ≠ .v1 → w ≠ .v4 → s₃.v w = s.v w := by
    intro w h1 h4; simp only [s₃, s₂, v_setV_of_ne _ _ h1, v_setV_of_ne _ _ h4]; rfl
  cases full with
  | false =>
    refine ⟨s₃, by simpa [quarters] using run₃, h1, fun h => absurd h (by decide),
      fun w a _ _ d _ => other₃ w a d, k₃⟩
  | true =>
    let s₄ := s₃.write .x .x6 (BitVec.ofNat 64 128)
    let s₅ := s₄.setV .v5 (bc ((s₄.gpr .x6).setWidth 8))
    let s₆ := s₅.setV .v2 (s₅.v .v0 ^^^ s₅.v .v5)
    let s₇ := s₆.setV .v3 (s₆.v .v1 ^^^ s₆.v .v5)
    have h5 : s₆.v .v5 = bc 128 := by
      simp only [s₆, s₅, v_setV_of_ne _ _ (by decide : VReg.v5 ≠ .v2), v_setV_self, s₄,
        gpr_write_self, BitVec.setWidth_eq]; rfl
    have e0 : s₅.v .v0 = s.v .v0 := by
      simp only [s₅, v_setV_of_ne _ _ (by decide : VReg.v0 ≠ .v5)]; exact h0
    refine ⟨s₇, ?_, fun e he => ?_, fun _ e he => ⟨?_, ?_⟩, fun w a b c _ d => ?_, ?_⟩
    · simp only [quarters, ite_true, List.cons_append, List.nil_append]
      rw [runBlock_cons, VG.Proof.Rc2.AArch64.exec_imm _ _ _ (by decide), runStep_some, runBlock_cons, exec_dupb,
        runStep_some, runBlock_cons, exec_eorv, runStep_some, runBlock_cons,
        VG.Proof.Rc2.AArch64.exec_imm _ _ _ (by decide), runStep_some, runBlock_cons, exec_dupb, runStep_some,
        runBlock_cons, exec_eorv, runStep_some, runBlock_cons, exec_eorv, runStep_some,
        runBlock_nil]
    · have : s₇.v .v1 = s₃.v .v1 := by
        simp only [s₇, s₆, s₅, v_setV_of_ne _ _ (by decide : VReg.v1 ≠ .v3),
          v_setV_of_ne _ _ (by decide : VReg.v1 ≠ .v2), v_setV_of_ne _ _ (by decide : VReg.v1 ≠ .v5)]
        rfl
      rw [this]; exact h1 e he
    · have : s₇.v .v2 = s.v .v0 ^^^ bc 128 := by
        simp only [s₇, v_setV_of_ne _ _ (by decide : VReg.v2 ≠ .v3)]
        rw [show s₆.v .v2 = s₅.v .v0 ^^^ s₅.v .v5 from v_setV_self _ _ _, e0,
          show s₅.v .v5 = s₆.v .v5 from (v_setV_of_ne _ _ (by decide)).symm, h5]
      rw [this, vbyte_xor, vbyte_bc _ he]
    · have v1₆ : s₆.v .v1 = s₃.v .v1 := by
        simp only [s₆, s₅, v_setV_of_ne _ _ (by decide : VReg.v1 ≠ .v2),
          v_setV_of_ne _ _ (by decide : VReg.v1 ≠ .v5)]; rfl
      have : s₇.v .v3 = s₃.v .v1 ^^^ bc 128 := by
        rw [show s₇.v .v3 = s₆.v .v1 ^^^ s₆.v .v5 from v_setV_self _ _ _, v1₆, h5]
      rw [this, vbyte_xor, h1 e he, vbyte_bc _ he, BitVec.xor_assoc]; rfl
    · simp only [s₇, s₆, s₅, s₄, v_setV_of_ne _ _ c, v_setV_of_ne _ _ b, v_setV_of_ne _ _ d,
        v_write]
      exact other₃ w a (by assumption)
    · exact k₃.trans ⟨fun r hr => gpr_write_of_ne _ _ _ (fun e => hr (by simp [e])), rfl, rfl, rfl⟩

/-! ## The lookups -/

theorem exec_umovw0 (s : State) (d : Reg) (n : VReg) :
    exec (.umov .w d n 0) s = some (s.write .w d ((s.v n).extractLsb' 0 32)) := by
  simp [exec, Size.bits]

theorem exec_lslx (s : State) (r : Reg) (sh : Nat) (h : sh < 64) :
    exec (.lsl .x r r sh) s = some (s.write .x r (s.gpr r <<< sh)) := by
  simp [exec, Size.bits, h, State.read]

theorem exec_lsrx (s : State) (r : Reg) (sh : Nat) (h : sh < 64) :
    exec (.lsr .x r r sh) s = some (s.write .x r (s.gpr r >>> sh)) := by
  simp [exec, Size.bits, h, State.read]

/-- `umov` of a word and a mask to `n` bits. -/
theorem umov_mask_ok (s : State) (n : Nat) (hn : n < 64) (hn' : 0 < n) :
    WP isa (.block (([.umov .w .x8 .v0 0] : List Instr) ++ mask .x8 n)) s fun t =>
      t.gpr .x8 = ((((s.v .v0).extractLsb' 0 32).setWidth 64).setWidth n).setWidth 64 ∧
      VG.Proof.Rc2.AArch64.Keep [.x8] s t ∧ t.v = s.v := by
  let e₁ := s.write .w .x8 ((s.v .v0).extractLsb' 0 32)
  let e₂ := e₁.write .x .x8 (e₁.gpr .x8 <<< (64 - n))
  let e₃ := e₂.write .x .x8 (e₂.gpr .x8 >>> (64 - n))
  refine WP.of_runBlock ⟨e₃, ?_, ?_, ?_, rfl⟩
  · rw [List.singleton_append, mask, runBlock_cons, VG.Proof.Rc2.AArch64.exec_umovw0, runStep_some, runBlock_cons,
      VG.Proof.Rc2.AArch64.exec_lslx _ _ _ (by omega), runStep_some, runBlock_cons, VG.Proof.Rc2.AArch64.exec_lsrx _ _ _ (by omega),
      runStep_some, runBlock_nil]
  · simp only [e₃, e₂, e₁, gpr_write_self, BitVec.setWidth_eq]
    exact VG.Proof.Rc2.AArch64.maskBits _ n (by omega)
  · exact ⟨fun r hr => by
      have : r ≠ .x8 := fun e => hr (by simp [e])
      simp only [e₃, e₂, e₁, gpr_write_of_ne _ _ _ this], rfl, rfl, rfl⟩

theorem low_byte (v : BitVec 128) :
    ((((v.extractLsb' 0 32).setWidth 64).setWidth 8).setWidth 64) = (vbyte v 0).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, vbyte, BitVec.getLsbD_extractLsb']
  by_cases h : i < 8
  · simp [h, show i < 32 by omega]
  · simp [h]

theorem piLookup_eq : piLookup = loadTable (fun k => Spec.Rc2.piTable.getD k 0) ++
    (([.vop (.dup .b16 .v0 .x8)] : List Instr) ++ (quarters true ++ (select true ++
      (([.umov .w .x8 .v0 0] : List Instr) ++ mask .x8 8)))) := by
  simp only [piLookup, List.append_assoc]

theorem piLookup_ok (s : State) :
    WP isa (.block piLookup) s (fun s' =>
      s'.gpr .x8 = (Spec.Rc2.pi ((s.gpr .x8).setWidth 8)).setWidth 64 ∧
      VG.Proof.Rc2.AArch64.Keep [.x8, .x3, .x6, .x7] s s') := by
  rw [VG.Proof.Rc2.AArch64.piLookup_eq, WP.block_append_iff]
  refine WP.mono (loadTable_ok s _) fun a ⟨arow, _, ag, am, ard, awr, _⟩ => ?_
  have ak : VG.Proof.Rc2.AArch64.Keep [.x6, .x7] s a := ⟨fun r hr => ag r (fun e => hr (by simp [e]))
    (fun e => hr (by simp [e])), am, ard, awr⟩
  let X := (s.gpr .x8).setWidth 8
  let b := a.setV .v0 (bc ((a.gpr .x8).setWidth 8))
  have b0 : b.v .v0 = bc X := by
    simp only [b, v_setV_self, X, ak.reg .x8 (by decide)]
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨b, by rw [runBlock_cons, exec_dupb, runStep_some, runBlock_nil], ?_⟩
  rw [WP.block_append_iff]
  obtain ⟨c, runc, c1, c23, cv, ck⟩ := VG.Proof.Rc2.AArch64.quarters_run true b
  refine WP.of_runBlock ⟨c, runc, ?_⟩
  rw [WP.block_append_iff]
  have c0 : c.v .v0 = bc X := by
    rw [cv _ (by decide) (by decide) (by decide) (by decide) (by decide), b0]
  obtain ⟨d, rund, d0, dv⟩ := select_full_run (s := c) (fun _ => X)
    (fun e he => by rw [c0, vbyte_bc _ he])
    (fun e he => by rw [c1 e he, b0, vbyte_bc _ he])
    (fun e he => by rw [(c23 rfl e he).1, b0, vbyte_bc _ he])
    (fun e he => by rw [(c23 rfl e he).2, b0, vbyte_bc _ he])
  refine WP.of_runBlock ⟨d, rund, ?_⟩
  have tab : tbyte c.v X.toNat = Spec.Rc2.pi X := by
    have hcb : ∀ w, w ≠ .v0 → w ≠ .v1 → w ≠ .v2 → w ≠ .v3 → w ≠ .v4 → w ≠ .v5 → c.v w = a.v w := by
      intro w h0 h1 h2 h3 h4 h5
      rw [cv w h1 h2 h3 h4 h5]
      exact v_setV_of_ne _ _ h0
    rw [tbyte_congr hcb _ X.isLt, arow _ X.isLt]; rfl
  refine WP.mono (VG.Proof.Rc2.AArch64.umov_mask_ok d 8 (by decide) (by decide)) fun t ⟨t8, tk, _⟩ => ⟨?_, ?_⟩
  · rw [t8, VG.Proof.Rc2.AArch64.low_byte, d0 0 (by decide), tab]
  · have kd : VG.Proof.Rc2.AArch64.Keep [.x8, .x3, .x6, .x7] c t :=
      (⟨fun _ _ => by rw [dv.gpr], dv.mem, dv.rd, dv.wr⟩ : VG.Proof.Rc2.AArch64.Keep [] c d).weaken (by simp) |>.trans
        (tk.weaken (by simp))
    have kb : VG.Proof.Rc2.AArch64.Keep [.x8, .x3, .x6, .x7] a b := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
    exact (((ak.weaken (by simp)).trans kb).trans (ck.weaken (by simp))).trans kd

/-! ## Schedule words -/

theorem exec_ldrq' (s : State) (t : VReg) (n : Reg) (off : Nat) (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.ldrq t n off) s = some (s.setV t (s.mem.read (s.gpr n + BitVec.ofNat 64 off) 16)) := by
  simp only [exec, addr, show 4096 * 16 = 65536 from rfl, ho, and_self, ite_true, State.load, h,
    Option.bind_some, Option.map_some]

theorem loads_ok (s : State) (readable : InRegions (s.rd ++ s.wr) (s.gpr .x0) 128) (n : Nat)
    (hn : n ≤ 8) :
    WP isa (.block ((List.range n).map fun r => .ldrq (treg r) .x0 (16 * r))) s fun t =>
      (∀ r < n, t.v (treg r) = s.mem.read (s.gpr .x0 + BitVec.ofNat 64 (16 * r)) 16) ∧
      (∀ w, (∀ r < n, w ≠ treg r) → t.v w = s.v w) ∧ t = { s with v := t.v } := by
  induction n with
  | zero => exact WP.block_nil ⟨fun _ h => absurd h (by omega), fun _ _ => rfl, rfl⟩
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun a ⟨arow, av, ae⟩ => ?_
    have hin : InRegions (a.rd ++ a.wr) (a.gpr .x0 + BitVec.ofNat 64 (16 * n)) 16 := by
      rw [ae]; exact CallLay.inRegions_sub readable (by omega) (by decide)
    refine WP.of_runBlock ⟨_, by
      rw [runBlock_cons, VG.Proof.Rc2.AArch64.exec_ldrq' _ _ _ _ ⟨by omega, by omega⟩ hin, runStep_some, runBlock_nil],
      fun r hr => ?_, fun w hw => ?_, ?_⟩
    · have hmx : a.mem = s.mem ∧ a.gpr = s.gpr := by rw [ae]; exact ⟨rfl, rfl⟩
      by_cases he : r = n
      · subst he; rw [v_setV_self, hmx.1, hmx.2]
      · rw [v_setV_of_ne _ _ (fun e => he (treg_inj r (by omega) n (by omega) e)), arow r (by omega)]
    · rw [v_setV_of_ne _ _ (hw n (by omega)), av w (fun r hr => hw r (by omega))]
    · rw [ae]; rfl

theorem tbyte_loaded {v : VReg → BitVec 128} (m : Mem) (p : Addr)
    (h : ∀ r < 8, v (treg r) = m.read (p + BitVec.ofNat 64 (16 * r)) 16) (k : Nat) (hk : k < 128) :
    tbyte v k = m (p + BitVec.ofNat 64 k) := by
  rw [tbyte, h _ (by omega)]
  change (m.read _ 16).extractLsb' (8 * (k % 16)) 8 = _
  rw [Mem.extractLsb'_read m _ (by omega), Offset.add_add, show 16 * (k / 16) + k % 16 = k by omega]

theorem vbyte_dup4 (w : BitVec 32) {e : Nat} (he : e < 16) :
    vbyte (ofVWords w w w w) e = w.extractLsb' (8 * (e % 4)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vbyte, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  rw [getLsbD_ofVWords _ _ _ _ (by omega)]
  split <;> (try split) <;> (try split) <;> (congr 1; omega)

theorem index_table : ∀ j < 64, ∀ c < 4, (256 + 514 * j) / 2 ^ (8 * c) % 2 ^ 8 =
    if c = 0 then 2 * j else if c = 1 then 2 * j + 1 else 0 := by decide

/-- The index bytes: `2 j`, `2 j + 1`, 0 and 0 in each word. -/
theorem index_bytes (j : Nat) (hj : j < 64) (e : Nat) :
    ((BitVec.ofNat 32 (256 + 514 * j)).extractLsb' (8 * (e % 4)) 8).toNat =
      if e % 4 = 0 then 2 * j else if e % 4 = 1 then 2 * j + 1 else 0 := by
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (show 256 + 514 * j < 2 ^ 32 by omega)]
  exact index_table j hj (e % 4) (by omega)

theorem low_half (v : BitVec 128) :
    ((((v.extractLsb' 0 32).setWidth 64).setWidth 16).setWidth 64) =
      ((vbyte v 0).setWidth 16 ||| (vbyte v 1).setWidth 16 <<< 8).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, vbyte,
    BitVec.getLsbD_extractLsb']
  by_cases h8 : i < 8
  · simp [h8, show i < 16 by omega, show i < 32 by omega]
  · by_cases h16 : i < 16
    · simp [h8, h16, show i < 32 by omega, show i - 8 < 8 by omega, show i - 8 < 16 by omega,
        show 8 + (i - 8) = i by omega]
    · simp [h16]

theorem exec_madd (s : State) (d n m a : Reg) :
    exec (.madd .x d n m a) s = some (s.write .x d (s.gpr a + s.gpr n * s.gpr m)) := by
  simp [exec, State.read]

theorem exec_dups (s : State) (d : VReg) (n : Reg) :
    exec (.vop (.dup .s4 d n)) s =
      some (s.setV d (ofVWords ((s.gpr n).setWidth 32) ((s.gpr n).setWidth 32)
        ((s.gpr n).setWidth 32) ((s.gpr n).setWidth 32))) := rfl

theorem keyLookup_eq : keyLookup = mask .x8 6 ++ (loadSchedule ++
    (([imm .x3 514, imm .x6 256, .madd .x .x8 .x8 .x3 .x6, .vop (.dup .s4 .v0 .x8)] : List Instr) ++
    (quarters false ++ (select false ++ (([.umov .w .x8 .v0 0] : List Instr) ++ mask .x8 16))))) := by
  simp only [keyLookup, List.append_assoc]

theorem keyLookup_ok (s : State) (readable : InRegions (s.rd ++ s.wr) (s.gpr .x0) 128) :
    WP isa (.block keyLookup) s (fun s' =>
      s'.gpr .x8 = ((Spec.Rc2.scheduleAt s.mem (s.gpr .x0)).getD
        ((s.gpr .x8).setWidth 6).toNat 0).setWidth 64 ∧
      VG.Proof.Rc2.AArch64.Keep [.x8, .x3, .x4, .x5, .x6, .x7] s s') := by
  let j := ((s.gpr .x8).setWidth 6).toNat
  have hj : j < 64 := ((s.gpr .x8).setWidth 6).isLt
  rw [VG.Proof.Rc2.AArch64.keyLookup_eq, WP.block_append_iff]
  -- the index, masked
  let a := (s.write .x .x8 (s.gpr .x8 <<< (64 - 6))).write .x .x8
    ((s.write .x .x8 (s.gpr .x8 <<< (64 - 6))).gpr .x8 >>> (64 - 6))
  have a8 : a.gpr .x8 = BitVec.ofNat 64 j := by
    simp only [a, gpr_write_self, BitVec.setWidth_eq]
    rw [VG.Proof.Rc2.AArch64.maskBits _ 6 (by decide)]
    apply BitVec.eq_of_toNat_eq; simp [j]
  have ak : VG.Proof.Rc2.AArch64.Keep [.x8] s a :=
    ⟨fun r hr => by
      have : r ≠ .x8 := fun e => hr (by simp [e])
      simp only [a, gpr_write_of_ne _ _ _ this], rfl, rfl, rfl⟩
  refine WP.of_runBlock ⟨a, by
    rw [mask, runBlock_cons, VG.Proof.Rc2.AArch64.exec_lslx _ _ _ (by decide), runStep_some, runBlock_cons,
      VG.Proof.Rc2.AArch64.exec_lsrx _ _ _ (by decide), runStep_some, runBlock_nil], ?_⟩
  rw [WP.block_append_iff]
  have ra : InRegions (a.rd ++ a.wr) (a.gpr .x0) 128 := by
    rw [ak.rd, ak.wr, ak.reg .x0 (by decide)]; exact readable
  refine WP.mono (VG.Proof.Rc2.AArch64.loads_ok a ra 8 (by decide)) fun b ⟨brow, bv, be⟩ => ?_
  have bg : b.gpr = a.gpr := by rw [be]
  have bm : b.mem = a.mem := by rw [be]
  rw [WP.block_append_iff]
  -- the index bytes
  let W : BitVec 64 := b.gpr .x6 + b.gpr .x8 * b.gpr .x3
  let c₁ := b.write .x .x3 (BitVec.ofNat 64 514)
  let c₂ := c₁.write .x .x6 (BitVec.ofNat 64 256)
  let c₃ := c₂.write .x .x8 (c₂.gpr .x6 + c₂.gpr .x8 * c₂.gpr .x3)
  let w := (c₃.gpr .x8).setWidth 32
  let c := c₃.setV .v0 (ofVWords w w w w)
  have hw : w = BitVec.ofNat 32 (256 + 514 * j) := by
    have h8 : c₃.gpr .x8 = BitVec.ofNat 64 256 + BitVec.ofNat 64 j * BitVec.ofNat 64 514 := by
      simp only [c₃, c₂, c₁, gpr_write_self, BitVec.setWidth_eq]
      rw [gpr_write_of_ne _ _ _ (by decide), gpr_write_of_ne _ _ _ (by decide),
        gpr_write_of_ne _ _ _ (by decide), gpr_write_self, BitVec.setWidth_eq, bg, a8]
    simp only [w, h8]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
    omega
  refine WP.of_runBlock ⟨c, by
    rw [runBlock_cons, VG.Proof.Rc2.AArch64.exec_imm _ _ _ (by decide), runStep_some, runBlock_cons,
      VG.Proof.Rc2.AArch64.exec_imm _ _ _ (by decide), runStep_some, runBlock_cons, VG.Proof.Rc2.AArch64.exec_madd, runStep_some,
      runBlock_cons, VG.Proof.Rc2.AArch64.exec_dups, runStep_some, runBlock_nil], ?_⟩
  rw [WP.block_append_iff]
  let I : Nat → BitVec 8 := fun e => vbyte (c.v .v0) e
  have hI : ∀ e < 16, (I e).toNat =
      if e % 4 = 0 then 2 * j else if e % 4 = 1 then 2 * j + 1 else 0 := by
    intro e he
    simp only [I, c, v_setV_self, VG.Proof.Rc2.AArch64.vbyte_dup4 _ he, hw]
    exact VG.Proof.Rc2.AArch64.index_bytes j hj e
  obtain ⟨d, rund, d1, _, dv, dk⟩ := VG.Proof.Rc2.AArch64.quarters_run false c
  refine WP.of_runBlock ⟨d, rund, ?_⟩
  rw [WP.block_append_iff]
  have d0 : d.v .v0 = c.v .v0 := dv _ (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨f, runf, f0, fv⟩ := select_half_run (s := d) I
    (fun e he => by rw [hI e he]; split <;> (try split) <;> omega)
    (fun e he => by rw [d0])
    (fun e he => by rw [d1 e he])
  refine WP.of_runBlock ⟨f, runf, ?_⟩
  have tab : ∀ k < 128, tbyte d.v k = s.mem (s.gpr .x0 + BitVec.ofNat 64 k) := by
    intro k hk
    have hdb : ∀ v', v' ≠ .v0 → v' ≠ .v1 → v' ≠ .v2 → v' ≠ .v3 → v' ≠ .v4 → v' ≠ .v5 →
        d.v v' = b.v v' := by
      intro v' h0 h1 h2 h3 h4 h5
      rw [dv v' h1 h2 h3 h4 h5]
      simp only [c, v_setV_of_ne _ _ h0, c₃, c₂, c₁, v_write]
    rw [tbyte_congr hdb _ (by omega), VG.Proof.Rc2.AArch64.tbyte_loaded _ _ brow k hk, ak.mem, ak.reg .x0 (by decide)]
  refine WP.mono (VG.Proof.Rc2.AArch64.umov_mask_ok f 16 (by decide) (by decide)) fun t ⟨t8, tk, _⟩ => ⟨?_, ?_⟩
  · have e0 : (I 0).toNat = 2 * j := by rw [hI 0 (by decide)]; rfl
    have e1 : (I 1).toNat = 2 * j + 1 := by rw [hI 1 (by decide)]; rfl
    rw [t8, VG.Proof.Rc2.AArch64.low_half, f0 0 (by decide), f0 1 (by decide), e0, e1, tab _ (by omega), tab _ (by omega),
      VG.Proof.Rc2.AArch64.scheduleAt_getD _ _ _ hj]
  · have kc : VG.Proof.Rc2.AArch64.Keep [.x8, .x3, .x4, .x5, .x6, .x7] b c :=
      ⟨fun r hr => by
        have h8 : r ≠ .x8 := fun e => hr (by simp [e])
        have h3 : r ≠ .x3 := fun e => hr (by simp [e])
        have h6 : r ≠ .x6 := fun e => hr (by simp [e])
        simp only [c, gpr_setV, c₃, c₂, c₁, gpr_write_of_ne _ _ _ h8, gpr_write_of_ne _ _ _ h6,
          gpr_write_of_ne _ _ _ h3], rfl, rfl, rfl⟩
    have kb : VG.Proof.Rc2.AArch64.Keep [.x8, .x3, .x4, .x5, .x6, .x7] a b :=
      ⟨fun r _ => by rw [bg], bm, by rw [be], by rw [be]⟩
    have kf : VG.Proof.Rc2.AArch64.Keep [.x8, .x3, .x4, .x5, .x6, .x7] d f := ⟨fun _ _ => by rw [fv.gpr], fv.mem, fv.rd, fv.wr⟩
    exact ((((ak.weaken (by simp)).trans kb).trans kc).trans (dk.weaken (by simp))).trans
      (kf.trans (tk.weaken (by simp)))

end VG.Proof.Rc2.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Rounds`. -/
section

/-! # RC2 mixing and mashing in AArch64 registers -/

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc2.AArch64

/-- State words never alias the temporaries or argument registers. -/
theorem wordReg_separate (i : Nat) :
    wordReg i ≠ .x8 ∧ wordReg i ≠ .x3 ∧ wordReg i ≠ .x2 ∧ wordReg i ≠ .x0 ∧
    wordReg i ≠ .x1 ∧ wordReg i ≠ .x4 ∧ wordReg i ≠ .x5 ∧
    wordReg i ≠ .x6 ∧ wordReg i ≠ .x7 := by
  have h : ∀ j < 4,
      wordReg j ≠ .x8 ∧ wordReg j ≠ .x3 ∧ wordReg j ≠ .x2 ∧ wordReg j ≠ .x0 ∧
      wordReg j ≠ .x1 ∧ wordReg j ≠ .x4 ∧ wordReg j ≠ .x5 ∧
      wordReg j ≠ .x6 ∧ wordReg j ≠ .x7 := by decide
  simpa only [wordReg, Nat.mod_mod] using h (i % 4) (Nat.mod_lt _ (by decide))

theorem wordReg_injective : ∀ i < 4, ∀ j < 4, wordReg i = wordReg j ↔ i = j := by decide

theorem rotation_bounds (i : Nat) : 1 ≤ Spec.Rc2.rotation i ∧ Spec.Rc2.rotation i < 16 := by
  have h : ∀ j < 4, 1 ≤ Spec.Rc2.rotation j ∧ Spec.Rc2.rotation j < 16 := by decide
  simpa only [Spec.Rc2.rotation, Nat.mod_mod] using h (i % 4) (Nat.mod_lt _ (by decide))

theorem wordReg_ne9 (i : Nat) : wordReg i ≠ .x9 := by
  have h : ∀ j < 4, wordReg j ≠ .x9 := by decide
  simpa only [wordReg, Nat.mod_mod] using h (i % 4) (Nat.mod_lt _ (by decide))

/-- A zero-extended word rotated left by two shifts and a mask. -/
theorem rotWord (x : BitVec 16) (n : Nat) (hn : 1 ≤ n) (hn' : n < 16) :
    ((x.setWidth 64 >>> (16 - n)) ||| (x.setWidth 64 <<< n)) &&& 65535 =
      (x.rotateLeft n).setWidth 64 := by
  rw [maskWord]
  apply congrArg (BitVec.setWidth 64)
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_rotateLeft, Nat.mod_eq_of_lt hn']
  by_cases h : j < n
  · simp (disch := omega) [h, hj, show j + (16 - n) < 64 by omega, Nat.add_comm]
  · simp (disch := omega) [h, hj, show j < 64 by omega, show j - n < 64 by omega,
      show 16 - n + j < 64 by omega, BitVec.getLsbD_of_ge]

theorem mixWord2 (x k a b c : BitVec 16) :
    (x.setWidth 64 + k.setWidth 64 + (a.setWidth 64 &&& b.setWidth 64) +
      (c.setWidth 64 &&& ~~~(a.setWidth 64))) &&& 65535 =
      (x + k + (a &&& b) + (~~~a &&& c)).setWidth 64 := by
  rw [maskWord]
  apply congrArg (BitVec.setWidth 64)
  simp [BitVec.setWidth_add, BitVec.setWidth_not, BitVec.and_comm]

theorem reverseMixWord2 (x k a b c : BitVec 16) :
    (x.setWidth 64 - k.setWidth 64 - (a.setWidth 64 &&& b.setWidth 64) -
      (c.setWidth 64 &&& ~~~(a.setWidth 64))) &&& 65535 =
      (x - k - (a &&& b) - (~~~a &&& c)).setWidth 64 := by
  rw [maskWord]
  apply congrArg (BitVec.setWidth 64)
  simp [BitVec.sub_eq_add_neg, BitVec.setWidth_add, BitVec.setWidth_neg_of_le,
    BitVec.setWidth_not, BitVec.and_comm]

theorem rotate16_ok (s : State) (r : Reg) (hr : r ≠ .x8) (hr9 : r ≠ .x9)
    (hm : s.gpr .x9 = 65535)
    (x : BitVec 16) (hx : s.gpr r = x.setWidth 64)
    (n : Nat) (hn : 1 ≤ n) (hn' : n < 16) :
    ∃ s', runBlock isa (rotate16 r n) s = some s' ∧
      s'.gpr r = (x.rotateLeft n).setWidth 64 ∧ VG.Proof.Rc2.AArch64.Keep [r, .x8] s s' := by
  have hleft : n < 64 := by omega
  have hright : 16 - n < 64 := by omega
  refine ⟨_, by
    simp only [rotate16, runBlock_cons, runStep_some,
      runBlock_nil, exec, State.read, BitVec.setWidth_eq, hleft, hright, ite_true]
    rfl, ?_⟩
  constructor
  · simp only [gpr_write, BitVec.setWidth_eq, ite_true, hr, Ne.symm hr, Ne.symm hr9, ite_false,
      show (Reg.x9 = Reg.x8) = False by decide, hm]
    rw [hx]
    exact VG.Proof.Rc2.AArch64.rotWord x n hn hn'
  · constructor
    · intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      simp only [gpr_write, BitVec.setWidth_eq, hr'.1, hr'.2, ite_false]
    · simp only [mem_write]
    · simp only [rd_write]
    · simp only [wr_write]

theorem rotateRight_zero64 (x : BitVec 64) : x.rotateRight 0 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi]

theorem mixInputs_ok (s : State) (i j : Nat) (hj : j < 64)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr .x0) 128) :
    ∃ s', runBlock isa (mixInputs j i) s = some s' ∧
      s'.gpr .x6 = s.gpr (wordReg (i + 3)) &&& s.gpr (wordReg (i + 2)) ∧
      s'.gpr .x7 = s.gpr (wordReg (i + 1)) &&& ~~~(s.gpr (wordReg (i + 3))) ∧
      s'.gpr .x4 = ((Spec.Rc2.scheduleAt s.mem (s.gpr .x0)).getD j 0).setWidth 64 ∧
      VG.Proof.Rc2.AArch64.Keep [.x4, .x5, .x6, .x7] s s' := by
  have h₁ := VG.Proof.Rc2.AArch64.wordReg_separate (i + 1)
  have h₂ := VG.Proof.Rc2.AArch64.wordReg_separate (i + 2)
  have h₃ := VG.Proof.Rc2.AArch64.wordReg_separate (i + 3)
  have lo := CallLay.inRegions_sub readable (off := 2 * j) (l := 1) (by omega) (by decide)
  have hi := CallLay.inRegions_sub readable (off := 2 * j + 1) (l := 1) (by omega) (by decide)
  have loOff : 2 * j < 4096 := by omega
  have hiOff : 2 * j + 1 < 4096 := by omega
  refine ⟨_, by
    simp (config := {decide := true}) only [mixInputs, loadKey,
      List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
      exec, State.read, addr, State.load, Mem.read, Nat.mod_one, Nat.mul_one,
      Option.bind_some, Option.map_some,
       gpr_write, BitVec.setWidth_eq,
      mem_write, rd_write,
      wr_write, loOff, hiOff, lo, hi, ite_true, ite_false,
      h₁.2.2.2.2.2.2.2.1, h₃.2.2.2.2.2.2.2.1]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false]
  · simp only [gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false, VG.Proof.Rc2.AArch64.rotateRight_zero64]
  · simp only [gpr_write, BitVec.setWidth_eq, reduceCtorEq, ite_true, ite_false]
    change (((0#0 ++ s.mem (s.gpr .x0 + BitVec.ofNat 64 (2 * j))).setWidth 32).setWidth 64 |||
      (((0#0 ++ s.mem (s.gpr .x0 + BitVec.ofNat 64 (2 * j + 1))).setWidth 32).setWidth 64).rotateRight 56) = _
    simp only [BitVec.zero_width_append, BitVec.cast_eq, BitVec.setWidth_setWidth (by decide : ¬(32 < 8 ∧ 32 < 64))]
    rw [joinBytes, VG.Proof.Rc2.AArch64.scheduleAt_getD _ _ _ hj]
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_write, BitVec.setWidth_eq,
        hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
    · simp only [mem_write]
    · simp only [rd_write]
    · simp only [wr_write]

/-- Current RC2 words in the four dedicated registers. -/
def Words (s : State) (v : Spec.Rc2.State) : Prop :=
  (∀ i < 4, s.gpr (wordReg i) = (v.getD i 0).setWidth 64) ∧ s.gpr .x9 = 65535

def temps : List Reg := [.x8, .x3, .x4, .x5, .x6, .x7]
def roundWrites : List Reg := VG.Proof.Rc2.AArch64.temps ++ [.x19, .x20, .x21, .x22]

theorem wordReg_not_temps (i : Nat) : wordReg i ∉ VG.Proof.Rc2.AArch64.temps := by
  have h := VG.Proof.Rc2.AArch64.wordReg_separate i
  simp only [VG.Proof.Rc2.AArch64.temps, List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨h.1, h.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩

theorem wordReg_mem_roundWrites (i : Nat) : wordReg i ∈ VG.Proof.Rc2.AArch64.roundWrites := by
  have h : ∀ j < 4, wordReg j ∈ VG.Proof.Rc2.AArch64.roundWrites := by decide
  simpa only [wordReg, Nat.mod_mod] using h (i % 4) (Nat.mod_lt _ (by decide))

theorem vector_getD {α : Type} {n : Nat} (v : Vector α n) (i : Nat) (hi : i < n) (d : α) :
    v.getD i d = v[i] := by
  simp [Vector.getD, hi]

theorem Words.update {s s' : State} {v : Spec.Rc2.State} (h : VG.Proof.Rc2.AArch64.Words s v)
    (i : Nat) (hi : i < 4) (x : BitVec 16)
    (out : s'.gpr (wordReg i) = x.setWidth 64)
    (keep : VG.Proof.Rc2.AArch64.Keep (wordReg i :: VG.Proof.Rc2.AArch64.temps) s s') : VG.Proof.Rc2.AArch64.Words s' (v.set! i x) := by
  refine ⟨fun j hj => ?_, (keep.reg .x9 (by simp [VG.Proof.Rc2.AArch64.temps, Ne.symm (VG.Proof.Rc2.AArch64.wordReg_ne9 i)])).trans h.2⟩
  by_cases he : j = i
  · subst j
    simpa [Vector.getD, hi] using out
  · have hr : wordReg j ∉ wordReg i :: VG.Proof.Rc2.AArch64.temps := by
      simp only [List.mem_cons, not_or]
      exact ⟨fun e => he ((VG.Proof.Rc2.AArch64.wordReg_injective j hj i hi).mp e), VG.Proof.Rc2.AArch64.wordReg_not_temps j⟩
    rw [keep.reg _ hr, h.1 j hj]
    rw [VG.Proof.Rc2.AArch64.vector_getD _ j hj, VG.Proof.Rc2.AArch64.vector_getD _ j hj, Vector.getElem_set!_ne hj (Ne.symm he)]

theorem Words.preserve {s s' : State} {v : Spec.Rc2.State} (h : VG.Proof.Rc2.AArch64.Words s v)
    (keep : VG.Proof.Rc2.AArch64.Keep VG.Proof.Rc2.AArch64.temps s s') : VG.Proof.Rc2.AArch64.Words s' v :=
  ⟨fun i hi => (keep.reg _ (VG.Proof.Rc2.AArch64.wordReg_not_temps i)).trans (h.1 i hi),
    (keep.reg .x9 (by simp [VG.Proof.Rc2.AArch64.temps])).trans h.2⟩

theorem Keep.round {s s' : State} {i : Nat}
    (h : VG.Proof.Rc2.AArch64.Keep (wordReg i :: VG.Proof.Rc2.AArch64.temps) s s') : VG.Proof.Rc2.AArch64.Keep VG.Proof.Rc2.AArch64.roundWrites s s' :=
  h.weaken (by
    intro r hr
    simp only [List.mem_cons] at hr
    rcases hr with he | hm
    · subst r; exact VG.Proof.Rc2.AArch64.wordReg_mem_roundWrites i
    · exact List.mem_append_left _ hm)


theorem addInputs_ok (s : State) (r : Reg) (h6 : r ≠ .x6) (h7 : r ≠ .x7)
    (h9 : r ≠ .x9) (hm : s.gpr .x9 = 65535) :
    ∃ s', runBlock isa (addInputs r) s = some s' ∧
      s'.gpr r = (s.gpr r + s.gpr .x4 + s.gpr .x6 + s.gpr .x7) &&& 65535 ∧ VG.Proof.Rc2.AArch64.Keep [r] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [addInputs,
      runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
      gpr_write, BitVec.setWidth_eq, Ne.symm h6, Ne.symm h7, Ne.symm h9, ite_true,
      ite_false]
    rfl, ?_⟩
  constructor
  · simp only [gpr_write_self, BitVec.setWidth_eq, hm]
  · constructor
    · intro r' hr
      simp only [List.mem_singleton] at hr
      simp only [gpr_write, BitVec.setWidth_eq, hr, ite_false]
    · rfl
    · rfl
    · rfl

theorem subInputs_ok (s : State) (r : Reg) (h6 : r ≠ .x6) (h7 : r ≠ .x7)
    (h9 : r ≠ .x9) (hm : s.gpr .x9 = 65535) :
    ∃ s', runBlock isa (subInputs r) s = some s' ∧
      s'.gpr r = (s.gpr r - s.gpr .x4 - s.gpr .x6 - s.gpr .x7) &&& 65535 ∧ VG.Proof.Rc2.AArch64.Keep [r] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [subInputs,
      runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
      gpr_write, BitVec.setWidth_eq, Ne.symm h6, Ne.symm h7, Ne.symm h9, ite_true,
      ite_false]
    rfl, ?_⟩
  constructor
  · simp only [gpr_write_self, BitVec.setWidth_eq, hm]
  · constructor
    · intro r' hr
      simp only [List.mem_singleton] at hr
      simp only [gpr_write, BitVec.setWidth_eq, hr, ite_false]
    · rfl
    · rfl
    · rfl

theorem mix_ok (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.AArch64.Words s v)
    (i j : Nat) (hi : i < 4) (hj : j < 64)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr .x0) 128) :
    WP isa (.block (mix j i)) s (fun s' =>
      VG.Proof.Rc2.AArch64.Words s' (Spec.Rc2.mix (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) j i v) ∧
      VG.Proof.Rc2.AArch64.Keep (wordReg i :: VG.Proof.Rc2.AArch64.temps) s s') := by
  rw [mix, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, and₁, bic₁, key₁, keep₁⟩ := VG.Proof.Rc2.AArch64.mixInputs_ok s i j hj readable
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  have sep := VG.Proof.Rc2.AArch64.wordReg_separate i
  have hm₁ : s₁.gpr .x9 = 65535 := (keep₁.reg .x9 (by decide)).trans hv.2
  obtain ⟨s₂, run₂, out₂, keep₂⟩ := VG.Proof.Rc2.AArch64.addInputs_ok s₁ (wordReg i)
    sep.2.2.2.2.2.2.2.1 sep.2.2.2.2.2.2.2.2 (VG.Proof.Rc2.AArch64.wordReg_ne9 i) hm₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  let x := v.getD i 0 + (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)).getD j 0 +
    (v.getD ((i + 3) % 4) 0 &&& v.getD ((i + 2) % 4) 0) +
    (~~~(v.getD ((i + 3) % 4) 0) &&& v.getD ((i + 1) % 4) 0)
  have wordmod (j : Nat) : wordReg j = wordReg (j % 4) := by simp [wordReg]
  have value₂ : s₂.gpr (wordReg i) = x.setWidth 64 := by
    rw [out₂, key₁, and₁, bic₁, keep₁.reg (wordReg i) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨sep.2.2.2.2.2.1, sep.2.2.2.2.2.2.1,
        sep.2.2.2.2.2.2.2.1, sep.2.2.2.2.2.2.2.2⟩), hv.1 i hi,
      wordmod (i + 3), wordmod (i + 2), wordmod (i + 1),
      hv.1 _ (Nat.mod_lt _ (by decide)), hv.1 _ (Nat.mod_lt _ (by decide)),
      hv.1 _ (Nat.mod_lt _ (by decide))]
    exact VG.Proof.Rc2.AArch64.mixWord2 _ _ _ _ _
  have hn := VG.Proof.Rc2.AArch64.rotation_bounds i
  have hm₂ : s₂.gpr .x9 = 65535 :=
    (keep₂.reg .x9 (by simp [Ne.symm (VG.Proof.Rc2.AArch64.wordReg_ne9 i)])).trans hm₁
  obtain ⟨s₃, run₃, out₃, keep₃⟩ := VG.Proof.Rc2.AArch64.rotate16_ok s₂ (wordReg i) sep.1 (VG.Proof.Rc2.AArch64.wordReg_ne9 i) hm₂ x value₂ _
    hn.1 hn.2
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have k₁ : VG.Proof.Rc2.AArch64.Keep (wordReg i :: VG.Proof.Rc2.AArch64.temps) s s₁ := keep₁.weaken (by
    intro r hr
    apply List.mem_cons_of_mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h <;> subst r <;> decide)
  have k₂ : VG.Proof.Rc2.AArch64.Keep (wordReg i :: VG.Proof.Rc2.AArch64.temps) s₁ s₂ := keep₂.weaken (by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r; exact List.mem_cons_self)
  have k₃ : VG.Proof.Rc2.AArch64.Keep (wordReg i :: VG.Proof.Rc2.AArch64.temps) s₂ s₃ := keep₃.weaken (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h
    · subst r; exact List.mem_cons_self
    · subst r; exact List.mem_cons_of_mem _ (by decide))
  have keep := (k₁.trans k₂).trans k₃
  exact ⟨hv.update i hi (x.rotateLeft _) out₃ keep, keep⟩

theorem wordReg_mod (i : Nat) : wordReg i = wordReg (i % 4) := by simp [wordReg]

theorem wordReg_offset_ne (i : Nat) (hi : i < 4) (d : Nat) (hd : 1 ≤ d) (hd' : d < 4) :
    wordReg (i + d) ≠ wordReg i := by
  rw [VG.Proof.Rc2.AArch64.wordReg_mod (i + d)]
  intro he
  have := (VG.Proof.Rc2.AArch64.wordReg_injective _ (Nat.mod_lt _ (by decide)) i hi).mp he
  omega

theorem keep_inputs {s s' : State} (h : VG.Proof.Rc2.AArch64.Keep [.x4, .x5, .x6, .x7] s s') (i : Nat) :
    VG.Proof.Rc2.AArch64.Keep (wordReg i :: VG.Proof.Rc2.AArch64.temps) s s' := h.weaken (by
  intro r hr
  apply List.mem_cons_of_mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h <;> subst r <;> decide)

theorem keep_rotate {i : Nat} {s s' : State} (h : VG.Proof.Rc2.AArch64.Keep [wordReg i, .x8] s s') :
    VG.Proof.Rc2.AArch64.Keep (wordReg i :: VG.Proof.Rc2.AArch64.temps) s s' := h.weaken (by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h
  · subst r; exact List.mem_cons_self
  · subst r; exact List.mem_cons_of_mem _ (by decide))

theorem keep_word {i : Nat} {s s' : State} (h : VG.Proof.Rc2.AArch64.Keep [wordReg i] s s') :
    VG.Proof.Rc2.AArch64.Keep (wordReg i :: VG.Proof.Rc2.AArch64.temps) s s' := h.weaken (by
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r; exact List.mem_cons_self)

theorem reverseMix_ok (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.AArch64.Words s v)
    (i j : Nat) (hi : i < 4) (hj : j < 64)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr .x0) 128) :
    WP isa (.block (reverseMix j i)) s (fun s' =>
      VG.Proof.Rc2.AArch64.Words s' (Spec.Rc2.reverseMix (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) j i v) ∧
      VG.Proof.Rc2.AArch64.Keep (wordReg i :: VG.Proof.Rc2.AArch64.temps) s s') := by
  rw [reverseMix, List.append_assoc, WP.block_append_iff]
  have sep := VG.Proof.Rc2.AArch64.wordReg_separate i
  have hn := VG.Proof.Rc2.AArch64.rotation_bounds i
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := VG.Proof.Rc2.AArch64.rotate16_ok s (wordReg i) sep.1 (VG.Proof.Rc2.AArch64.wordReg_ne9 i) hv.2 (v.getD i 0)
    (hv.1 i hi) (16 - Spec.Rc2.rotation i) (by omega) (by omega)
  rw [rotateLeft_reverse _ _ hn.1 hn.2] at out₁
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  have ptr₁ : s₁.gpr .x0 = s.gpr .x0 := keep₁.reg _ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨Ne.symm sep.2.2.2.1, by decide⟩)
  have read₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x0) 128 := by
    rw [keep₁.rd, keep₁.wr, ptr₁]; exact readable
  have hm₁ : s₁.gpr .x9 = 65535 :=
    (keep₁.reg .x9 (by simp [Ne.symm (VG.Proof.Rc2.AArch64.wordReg_ne9 i)])).trans hv.2
  obtain ⟨s₂, run₂, and₂, bic₂, key₂, keep₂⟩ := VG.Proof.Rc2.AArch64.mixInputs_ok s₁ i j hj read₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  have hm₂ : s₂.gpr .x9 = 65535 := (keep₂.reg .x9 (by decide)).trans hm₁
  obtain ⟨s₃, run₃, out₃, keep₃⟩ := VG.Proof.Rc2.AArch64.subInputs_ok s₂ (wordReg i)
    sep.2.2.2.2.2.2.2.1 sep.2.2.2.2.2.2.2.2 (VG.Proof.Rc2.AArch64.wordReg_ne9 i) hm₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have other (d : Nat) (hd : 1 ≤ d) (hd' : d < 4) :
      s₁.gpr (wordReg (i + d)) = (v.getD ((i + d) % 4) 0).setWidth 64 := by
    rw [keep₁.reg _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨VG.Proof.Rc2.AArch64.wordReg_offset_ne i hi d hd hd', (VG.Proof.Rc2.AArch64.wordReg_separate _).1⟩),
      VG.Proof.Rc2.AArch64.wordReg_mod (i + d)]
    exact hv.1 _ (Nat.mod_lt _ (by decide))
  have keptWord := keep₂.reg (wordReg i) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨sep.2.2.2.2.2.1, sep.2.2.2.2.2.2.1,
      sep.2.2.2.2.2.2.2.1, sep.2.2.2.2.2.2.2.2⟩)
  have value₃ : s₃.gpr (wordReg i) =
      ((v.getD i 0).rotateRight (Spec.Rc2.rotation i) -
        (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)).getD j 0 -
        (v.getD ((i + 3) % 4) 0 &&& v.getD ((i + 2) % 4) 0) -
        (~~~(v.getD ((i + 3) % 4) 0) &&& v.getD ((i + 1) % 4) 0)).setWidth 64 := by
    rw [out₃, keptWord, out₁, key₂, and₂, bic₂, keep₁.mem, ptr₁,
      other 3 (by decide) (by decide), other 2 (by decide) (by decide),
      other 1 (by decide) (by decide)]
    exact VG.Proof.Rc2.AArch64.reverseMixWord2 _ _ _ _ _
  have keep := ((VG.Proof.Rc2.AArch64.keep_rotate keep₁).trans (VG.Proof.Rc2.AArch64.keep_inputs keep₂ i)).trans (VG.Proof.Rc2.AArch64.keep_word keep₃)
  exact ⟨hv.update i hi _ value₃ keep, keep⟩

theorem adjust_ok (s : State) (r : Reg) (sub : Bool) (h9 : r ≠ .x9)
    (hm : s.gpr .x9 = 65535) :
    ∃ s', runBlock isa (adjust sub r) s = some s' ∧
      s'.gpr r = (if sub then s.gpr r - s.gpr .x8 else s.gpr r + s.gpr .x8) &&& 65535 ∧
      VG.Proof.Rc2.AArch64.Keep [r] s s' := by
  cases sub <;> refine ⟨_, by
    simp (config := {decide := true}) only [adjust,
      ite_false, ite_true, runBlock_cons, runStep_some,
      runBlock_nil, exec, State.read, gpr_write, BitVec.setWidth_eq]
    rfl, ?_⟩
  all_goals
    constructor
    · simp only [gpr_write_self, BitVec.setWidth_eq, Bool.false_eq_true,
        ite_false, ite_true, Ne.symm h9, hm]
    · constructor
      · intro r' hr
        simp only [List.mem_singleton] at hr
        simp only [gpr_write, BitVec.setWidth_eq, hr, ite_false]
      · rfl
      · rfl
      · rfl

theorem indexWord (x : BitVec 16) :
    ((x.setWidth 64).setWidth 6).toNat = (x &&& 63).toNat := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and]
  change x.toNat % 18446744073709551616 % 64 = x.toNat &&& (2 ^ 6 - 1)
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (show x.toNat < 18446744073709551616 by have := x.isLt; omega)]

def mashSpec (direction : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule)
    (i : Nat) (v : Spec.Rc2.State) : Spec.Rc2.State :=
  match direction with
  | .encrypt => Spec.Rc2.mash k i v
  | .decrypt => Spec.Rc2.reverseMash k i v

theorem mash_ok (direction : Spec.Rc2.Direction) (s : State)
    (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.AArch64.Words s v) (i : Nat) (hi : i < 4)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr .x0) 128) :
    WP isa (.block (mash direction i)) s (fun s' =>
      VG.Proof.Rc2.AArch64.Words s' (VG.Proof.Rc2.AArch64.mashSpec direction (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) i v) ∧
      VG.Proof.Rc2.AArch64.Keep (wordReg i :: VG.Proof.Rc2.AArch64.temps) s s') := by
  rw [mash, List.append_assoc, WP.block_append_iff]
  let s₁ := s.write .x .x8 (s.gpr (wordReg (i + 3)))
  refine WP.of_runBlock ⟨s₁, ?_, ?_⟩
  · simp only [rr, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, BitVec.setWidth_eq, BitVec.add_zero, show 0 < 4096 by decide, ite_true]
    rfl
  rw [WP.block_append_iff]
  have keep₁ : VG.Proof.Rc2.AArch64.Keep VG.Proof.Rc2.AArch64.temps s s₁ := by
    constructor
    · intro r hr
      exact gpr_write_of_ne _ _ _ (fun he => hr (he ▸ List.mem_cons_self))
    · exact mem_write _ _ _ _
    · exact rd_write _ _ _ _
    · exact wr_write _ _ _ _
  have ptr₁ := keep₁.reg .x0 (by decide)
  have read₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x0) 128 := by
    rw [keep₁.rd, keep₁.wr, ptr₁]; exact readable
  apply WP.mono (VG.Proof.Rc2.AArch64.keyLookup_ok s₁ read₁)
  intro s₂ h₂
  let k := Spec.Rc2.scheduleAt s.mem (s.gpr .x0)
  let key := k.getD ((v.getD ((i + 3) % 4) 0 &&& 63).toNat) 0
  have out₂ : s₂.gpr .x8 = key.setWidth 64 := by
    rw [h₂.1, keep₁.mem, ptr₁]
    change (k.getD (((s.gpr (wordReg (i + 3))).setWidth 6).toNat) 0).setWidth 64 = _
    rw [VG.Proof.Rc2.AArch64.wordReg_mod (i + 3), hv.1 _ (Nat.mod_lt _ (by decide)), VG.Proof.Rc2.AArch64.indexWord]
  have keep₂ : VG.Proof.Rc2.AArch64.Keep VG.Proof.Rc2.AArch64.temps s₁ s₂ := h₂.2
  have value₂ := ((hv.preserve keep₁).preserve keep₂).1 i hi
  obtain ⟨s₃, run₃, out₃, keep₃⟩ := VG.Proof.Rc2.AArch64.adjust_ok s₂ (wordReg i) (direction == .decrypt)
    (VG.Proof.Rc2.AArch64.wordReg_ne9 i) ((hv.preserve keep₁).preserve keep₂).2
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have keep : VG.Proof.Rc2.AArch64.Keep (wordReg i :: VG.Proof.Rc2.AArch64.temps) s s₃ :=
    ((keep₁.trans keep₂).weaken (fun _ hr => List.mem_cons_of_mem _ hr)).trans (VG.Proof.Rc2.AArch64.keep_word keep₃)
  have out₃' : s₃.gpr (wordReg i) =
      (if direction == .decrypt then v.getD i 0 - key else v.getD i 0 + key).setWidth 64 := by
    rw [out₃, value₂, out₂]
    cases direction <;>
      simp [maskWord_lit, BitVec.sub_eq_add_neg, BitVec.setWidth_add, BitVec.setWidth_neg_of_le]
  constructor
  · cases direction <;> exact hv.update i hi _ out₃' keep
  · exact keep


end VG.Proof.Rc2.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Cipher`. -/
section

/-! # Composition of RC2's sixteen rounds -/

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.Impl.Rc2.AArch64

theorem foldWords_ok (code : Nat → List Instr)
    (step : Spec.Rc2.Schedule → Nat → Spec.Rc2.State → Spec.Rc2.State) (is : List Nat)
    (correct : ∀ i ∈ is, ∀ (s : State) (v : Spec.Rc2.State), VG.Proof.Rc2.AArch64.Words s v →
      (InRegions (s.rd ++ s.wr) (s.gpr .x0) 128) →
      WP isa (.block (code i)) s (fun s' =>
        VG.Proof.Rc2.AArch64.Words s' (step (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) i v) ∧ VG.Proof.Rc2.AArch64.Keep VG.Proof.Rc2.AArch64.roundWrites s s'))
    (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.AArch64.Words s v)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr .x0) 128) :
    WP isa (.block (is.flatMap code)) s (fun s' =>
      VG.Proof.Rc2.AArch64.Words s' (is.foldl (fun v i => step (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) i v) v) ∧
      VG.Proof.Rc2.AArch64.Keep VG.Proof.Rc2.AArch64.roundWrites s s') := by
  induction is generalizing s v with
  | nil =>
    apply WP.block_nil
    exact ⟨hv, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    apply WP.mono (correct i (by simp) s v hv readable)
    intro s₁ h₁
    have ptr₁ := h₁.2.reg .x0 (by decide)
    have read₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x0) 128 := by
      rw [h₁.2.rd, h₁.2.wr, ptr₁]; exact readable
    apply WP.mono (ih (fun j hj => correct j (List.mem_cons_of_mem _ hj)) s₁ _ h₁.1 read₁)
    intro s₂ h₂
    refine ⟨?_, h₁.2.trans h₂.2⟩
    rw [h₁.2.mem, ptr₁] at h₂
    exact h₂.1

theorem mixRound_ok (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.AArch64.Words s v)
    (j : Nat) (hj : j < 16)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr .x0) 128) :
    WP isa (.block ((List.range 4).flatMap (fun i => mix (4 * j + i) i))) s (fun s' =>
      VG.Proof.Rc2.AArch64.Words s' (Spec.Rc2.mixRound (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) j v) ∧
      VG.Proof.Rc2.AArch64.Keep VG.Proof.Rc2.AArch64.roundWrites s s') := by
  apply VG.Proof.Rc2.AArch64.foldWords_ok (step := fun k i v => Spec.Rc2.mix k (4 * j + i) i v) _ _ _ s v hv readable
  intro i hi s v hv readable
  have bound := List.mem_range.mp hi
  apply WP.mono (VG.Proof.Rc2.AArch64.mix_ok s v hv i (4 * j + i) bound (by omega) readable)
  exact fun _ h => ⟨h.1, h.2.round⟩

theorem reverseMixRound_ok (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.AArch64.Words s v)
    (j : Nat) (hj : j < 16)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr .x0) 128) :
    WP isa (.block ([3, 2, 1, 0].flatMap (fun i => reverseMix (4 * j + i) i))) s (fun s' =>
      VG.Proof.Rc2.AArch64.Words s' (Spec.Rc2.reverseMixRound (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) j v) ∧
      VG.Proof.Rc2.AArch64.Keep VG.Proof.Rc2.AArch64.roundWrites s s') := by
  apply VG.Proof.Rc2.AArch64.foldWords_ok (step := fun k i v => Spec.Rc2.reverseMix k (4 * j + i) i v) _ _ _ s v hv readable
  intro i hi s v hv readable
  have bound : i < 4 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    omega
  apply WP.mono (VG.Proof.Rc2.AArch64.reverseMix_ok s v hv i (4 * j + i) bound (by omega) readable)
  exact fun _ h => ⟨h.1, h.2.round⟩

def mashRoundSpec (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule)
    (v : Spec.Rc2.State) : Spec.Rc2.State :=
  match d with
  | .encrypt => Spec.Rc2.mashRound k v
  | .decrypt => Spec.Rc2.reverseMashRound k v

def order (d : Spec.Rc2.Direction) : List Nat :=
  match d with
  | .encrypt => List.range 4
  | .decrypt => [3, 2, 1, 0]

theorem mashRound_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.AArch64.Words s v)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr .x0) 128) :
    WP isa (.block ((VG.Proof.Rc2.AArch64.order d).flatMap (mash d))) s (fun s' =>
      VG.Proof.Rc2.AArch64.Words s' (VG.Proof.Rc2.AArch64.mashRoundSpec d (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) v) ∧
      VG.Proof.Rc2.AArch64.Keep VG.Proof.Rc2.AArch64.roundWrites s s') := by
  have he (k : Spec.Rc2.Schedule) : VG.Proof.Rc2.AArch64.mashRoundSpec d k v =
      (VG.Proof.Rc2.AArch64.order d).foldl (fun v i => VG.Proof.Rc2.AArch64.mashSpec d k i v) v := by cases d <;> rfl
  simp only [he]
  apply VG.Proof.Rc2.AArch64.foldWords_ok (step := fun k i v => VG.Proof.Rc2.AArch64.mashSpec d k i v) _ _ _ s v hv readable
  intro i hi s v hv readable
  have bound : i < 4 := by
    cases d with
    | encrypt => exact List.mem_range.mp hi
    | decrypt =>
      simp only [VG.Proof.Rc2.AArch64.order, List.mem_cons, List.not_mem_nil, or_false] at hi
      omega
  apply WP.mono (VG.Proof.Rc2.AArch64.mash_ok d s v hv i bound readable)
  exact fun _ h => ⟨h.1, h.2.round⟩

def roundSpec (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (j : Nat)
    (v : Spec.Rc2.State) : Spec.Rc2.State :=
  let v := match d with
    | .encrypt => Spec.Rc2.mixRound k j v
    | .decrypt => Spec.Rc2.reverseMixRound k (15 - j) v
  if j = 4 ∨ j = 10 then VG.Proof.Rc2.AArch64.mashRoundSpec d k v else v

theorem round_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.AArch64.Words s v)
    (j : Nat) (hj : j < 16)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr .x0) 128) :
    WP isa (.block (VG.Impl.Rc2.AArch64.round d j)) s (fun s' =>
      VG.Proof.Rc2.AArch64.Words s' (VG.Proof.Rc2.AArch64.roundSpec d (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) j v) ∧
      VG.Proof.Rc2.AArch64.Keep VG.Proof.Rc2.AArch64.roundWrites s s') := by
  have finish (s₁ : State) (v₁ : Spec.Rc2.State) (h₁ : VG.Proof.Rc2.AArch64.Words s₁ v₁ ∧ VG.Proof.Rc2.AArch64.Keep VG.Proof.Rc2.AArch64.roundWrites s s₁) :
      WP isa (.block (if j = 4 ∨ j = 10 then (VG.Proof.Rc2.AArch64.order d).flatMap (mash d) else [])) s₁ (fun s₂ =>
        VG.Proof.Rc2.AArch64.Words s₂ (if j = 4 ∨ j = 10 then VG.Proof.Rc2.AArch64.mashRoundSpec d (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) v₁
          else v₁) ∧ VG.Proof.Rc2.AArch64.Keep VG.Proof.Rc2.AArch64.roundWrites s s₂) := by
    by_cases h : j = 4 ∨ j = 10
    · rw [ite_eq_left h]
      have ptr₁ := h₁.2.reg .x0 (by decide)
      have read₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x0) 128 := by
        rw [h₁.2.rd, h₁.2.wr, ptr₁]; exact readable
      apply WP.mono (VG.Proof.Rc2.AArch64.mashRound_ok d s₁ v₁ h₁.1 read₁)
      intro s₂ h₂
      rw [h₁.2.mem, ptr₁] at h₂
      exact ⟨by simpa only [ite_eq_left h] using h₂.1, h₁.2.trans h₂.2⟩
    · rw [ite_eq_right h]
      apply WP.block_nil
      exact ⟨by simpa only [ite_eq_right h] using h₁.1, h₁.2⟩
  cases d with
  | encrypt =>
    rw [VG.Impl.Rc2.AArch64.round, WP.block_append_iff]
    apply WP.mono (VG.Proof.Rc2.AArch64.mixRound_ok s v hv j hj readable)
    intro s₁ h₁
    exact finish s₁ _ h₁
  | decrypt =>
    rw [VG.Impl.Rc2.AArch64.round, WP.block_append_iff]
    apply WP.mono (VG.Proof.Rc2.AArch64.reverseMixRound_ok s v hv (15 - j) (by omega) readable)
    intro s₁ h₁
    exact finish s₁ _ h₁

theorem rounds_ok (d : Spec.Rc2.Direction) (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.AArch64.Words s v)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr .x0) 128) :
    WP isa (.block ((List.range 16).flatMap (VG.Impl.Rc2.AArch64.round d))) s (fun s' =>
      VG.Proof.Rc2.AArch64.Words s' ((List.range 16).foldl (fun v j => VG.Proof.Rc2.AArch64.roundSpec d
        (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) j v) v) ∧ VG.Proof.Rc2.AArch64.Keep VG.Proof.Rc2.AArch64.roundWrites s s') := by
  apply VG.Proof.Rc2.AArch64.foldWords_ok (step := fun k j v => VG.Proof.Rc2.AArch64.roundSpec d k j v) _ _ _ s v hv readable
  intro j hj s v hv readable
  exact VG.Proof.Rc2.AArch64.round_ok d s v hv j (List.mem_range.mp hj) readable

end VG.Proof.Rc2.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.MemOps`. -/
section

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd

theorem readByte (m : Mem) (p : Addr) : m.read p 1 = m p := by
  change (0#0 ++ m p) = _
  exact BitVec.zero_width_append _ _

theorem exec_ldr_x (s : VG.AArch64.State) (t n : Reg) (off : Nat)
    (ho : off % 8 = 0 ∧ off < 32768)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 8) :
    exec (.ldr .x t n off) s =
      some (s.write .x t (s.mem.readW (s.gpr n + BitVec.ofNat 64 off) 64)) := by
  simp only [exec, VG.AArch64.addr, Size.bytes, ho, and_self, ite_true, Option.bind_some,
    State.load, h, Option.map_some, Mem.readW]

theorem exec_str_x (s : VG.AArch64.State) (t n : Reg) (off : Nat)
    (ho : off % 8 = 0 ∧ off < 32768)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 8) :
    exec (.str .x t n off) s =
      some { s with mem := s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) (s.gpr t) } := by
  simp only [exec, VG.AArch64.addr, Size.bytes, ho, and_self, ite_true, Option.bind_some,
    State.store, h, State.read, BitVec.setWidth_eq, Mem.writeW]

end VG.Proof.Rc2.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.BlockIO`. -/
section

/-! # Loading and storing RC2 blocks -/

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc2.AArch64

theorem unpackWord_ok (s : State) (i : Nat) (hi : i < 4) :
    ∃ s', runBlock isa (unpackWord i) s = some s' ∧
      s'.gpr (wordReg i) = (((s.gpr .x8) >>> (16 * i)).setWidth 16).setWidth 64 ∧
      VG.Proof.Rc2.AArch64.Keep [wordReg i] s s' := by
  have hn : 16 * i < 64 := by omega
  refine ⟨_, by
    simp (config := {decide := true}) only [unpackWord, mask, rr, List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, State.read, gpr_write, BitVec.setWidth_eq,
      hn, ite_true, BitVec.add_zero]
    rfl, ?_⟩
  constructor
  · simp only [gpr_write_self, BitVec.setWidth_eq]
    exact VG.Proof.Rc2.AArch64.maskBits _ 16 (by decide)
  · constructor
    · intro r hr
      simp only [List.mem_singleton] at hr
      simp only [gpr_write, BitVec.setWidth_eq, hr, ite_false]
    · rfl
    · rfl
    · rfl

theorem unpackWords_ok (is : List Nat) (hi : ∀ i ∈ is, i < 4) (s : State) :
    WP isa (.block (is.flatMap unpackWord)) s (fun s' =>
      (∀ i ∈ is, s'.gpr (wordReg i) = (((s.gpr .x8) >>> (16 * i)).setWidth 16).setWidth 64) ∧
      VG.Proof.Rc2.AArch64.Keep (is.map wordReg) s s') := by
  induction is generalizing s with
  | nil =>
    apply WP.block_nil
    exact ⟨by simp, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    obtain ⟨s₁, run₁, out₁, keep₁⟩ := VG.Proof.Rc2.AArch64.unpackWord_ok s i (hi i (by simp))
    refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
    apply WP.mono (ih (fun j hj => hi j (List.mem_cons_of_mem _ hj)) s₁)
    intro s₂ h₂
    have input₁ := keep₁.reg .x8 (by
      simp only [List.mem_singleton]
      exact Ne.symm (VG.Proof.Rc2.AArch64.wordReg_separate i).1)
    constructor
    · intro j hj
      rw [List.mem_cons] at hj
      by_cases hm : j ∈ is
      · rw [h₂.1 j hm, input₁]
      · have he : j = i := hj.resolve_right hm
        subst j
        rw [h₂.2.reg _ (by
          intro hm'
          obtain ⟨j, hj, he⟩ := List.mem_map.mp hm'
          have je := (VG.Proof.Rc2.AArch64.wordReg_injective j (hi j (List.mem_cons_of_mem _ hj)) i (hi i (by simp))).mp he
          exact hm (je ▸ hj)), out₁]
    · apply (keep₁.weaken (fun r hr => ?_)).trans (h₂.2.weaken (fun r hr => ?_))
      · simp only [List.mem_singleton] at hr
        subst r; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ hr

theorem blockLoad_ok (s : State)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr .x1) 8) :
    WP isa (.block blockLoad) s (fun s' =>
      VG.Proof.Rc2.AArch64.Words s' (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (s.gpr .x1))) ∧
      VG.Proof.Rc2.AArch64.Keep (.x9 :: VG.Proof.Rc2.AArch64.roundWrites) s s') := by
  rw [blockLoad, WP.block_append_iff]
  let s₀ := s.write .x .x9 (BitVec.ofNat 64 65535)
  let s₁ := s₀.write .x .x8 (s₀.mem.readW (s₀.gpr .x1) 64)
  have r₀ : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x1 + BitVec.ofNat 64 0) 8 := by
    simpa [s₀, gpr_write, rd_write, wr_write] using readable
  refine WP.of_runBlock ⟨s₁, ?_, ?_⟩
  · simp only [runBlock_cons, VG.Proof.Rc2.AArch64.exec_imm _ _ _ (by decide : 65535 < 65536), runStep_some]
    rw [VG.Proof.Rc2.AArch64.exec_ldr_x _ _ _ 0 (by decide) r₀]
    simp only [runStep_some, runBlock_nil, BitVec.add_zero]
    rfl
  apply WP.mono (VG.Proof.Rc2.AArch64.unpackWords_ok (List.range 4) (fun i hi => List.mem_range.mp hi) s₁)
  intro s₂ h₂
  have x1₁ : s₁.gpr .x1 = s.gpr .x1 := by simp [s₁, s₀, gpr_write]
  have m₁ : s₁.mem = s.mem := rfl
  constructor
  · refine ⟨fun i hi => ?_, ?_⟩
    · rw [h₂.1 i (List.mem_range.mpr hi), decode_read64 _ _ i hi]
      rfl
    · rw [h₂.2.reg .x9 (by
        intro hm
        obtain ⟨i, _, he⟩ := List.mem_map.mp hm
        exact VG.Proof.Rc2.AArch64.wordReg_ne9 i he)]
      simp [s₁, s₀, gpr_write]
  · have keep₁ : VG.Proof.Rc2.AArch64.Keep (.x9 :: VG.Proof.Rc2.AArch64.roundWrites) s s₁ := by
      constructor
      · intro r hr
        have h9 : r ≠ .x9 := fun he => hr (he ▸ List.mem_cons_self)
        have h8 : r ≠ .x8 := fun he => hr (he ▸ List.mem_cons_of_mem _ (by decide))
        simp [s₁, s₀, gpr_write, h8, h9]
      · rfl
      · rfl
      · rfl
    apply keep₁.trans
    exact h₂.2.weaken (by
      intro r hr
      obtain ⟨i, _, he⟩ := List.mem_map.mp hr
      subst r; exact List.mem_cons_of_mem _ (VG.Proof.Rc2.AArch64.wordReg_mem_roundWrites i))

theorem packWord_ok (s : State) (i : Nat) (hi : 1 ≤ i) (hi' : i < 4) :
    ∃ s', runBlock isa (packWord i) s = some s' ∧
      s'.gpr .x8 = s.gpr .x8 ||| (s.gpr (wordReg i)).rotateRight (64 - 16 * i) ∧
      VG.Proof.Rc2.AArch64.Keep [.x8, .x3] s s' := by
  have hn : 64 - 16 * i < 64 := by omega
  refine ⟨_, by
    simp only [packWord, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, BitVec.setWidth_eq, gpr_write, BitVec.setWidth_eq,
      hn, reduceCtorEq, ite_true, ite_false]
    rfl, ?_⟩
  constructor
  · exact gpr_write_self _ _ _ _
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_write, BitVec.setWidth_eq, hr.1, hr.2, ite_false]
    · simp only [mem_write]
    · simp only [rd_write]
    · simp only [wr_write]

theorem packWords_ok (is : List Nat) (hi : ∀ i ∈ is, 1 ≤ i ∧ i < 4)
    (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.AArch64.Words s v) :
    WP isa (.block (is.flatMap packWord)) s (fun s' =>
      s'.gpr .x8 = is.foldl (fun acc i => acc |||
        ((v.getD i 0).setWidth 64).rotateRight (64 - 16 * i)) (s.gpr .x8) ∧
      VG.Proof.Rc2.AArch64.Keep [.x8, .x3] s s') := by
  induction is generalizing s with
  | nil =>
    apply WP.block_nil
    exact ⟨rfl, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  | cons i is ih =>
    rw [List.flatMap_cons, WP.block_append_iff]
    have bound := hi i (by simp)
    obtain ⟨s₁, run₁, out₁, keep₁⟩ := VG.Proof.Rc2.AArch64.packWord_ok s i bound.1 bound.2
    refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
    have keepTemps : VG.Proof.Rc2.AArch64.Keep VG.Proof.Rc2.AArch64.temps s s₁ := keep₁.weaken (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with h | h <;> subst r <;> decide)
    apply WP.mono (ih (fun j hj => hi j (List.mem_cons_of_mem _ hj)) s₁ (hv.preserve keepTemps))
    intro s₂ h₂
    refine ⟨?_, keep₁.trans h₂.2⟩
    rw [h₂.1, out₁, hv.1 i bound.2]
    rfl

/-- The block store changes exactly the data word, plus two caller-saved
registers; it leaves all memory-access permissions unchanged. -/
theorem blockStore_ok (s : State) (v : Spec.Rc2.State) (hv : VG.Proof.Rc2.AArch64.Words s v)
    (writable : InRegions s.wr (s.gpr .x1) 8) :
    WP isa (.block blockStore) s (fun s' =>
      s'.mem = s.mem.writeW (s.gpr .x1) (pack v) ∧
      (∀ r, r ∉ [.x8, .x3] → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr) := by
  rw [blockStore, List.append_assoc, WP.block_append_iff]
  let s₁ := s.write .x .x8 (s.gpr (wordReg 0))
  refine WP.of_runBlock ⟨s₁, ?_, ?_⟩
  · simp only [rr, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, BitVec.setWidth_eq, BitVec.add_zero, show 0 < 4096 by decide, ite_true]
    rfl
  rw [WP.block_append_iff]
  have keep₁ : VG.Proof.Rc2.AArch64.Keep [.x8, .x3] s s₁ := by
    constructor
    · intro r hr
      exact gpr_write_of_ne _ _ _ (fun he => hr (he ▸ List.mem_cons_self))
    · exact mem_write _ _ _ _
    · exact rd_write _ _ _ _
    · exact wr_write _ _ _ _
  have keepTemps : VG.Proof.Rc2.AArch64.Keep VG.Proof.Rc2.AArch64.temps s s₁ := keep₁.weaken (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h <;> subst r <;> decide)
  apply WP.mono (VG.Proof.Rc2.AArch64.packWords_ok [1, 2, 3] (by decide) s₁ v (hv.preserve keepTemps))
  intro s₂ h₂
  have keep := keep₁.trans h₂.2
  have ptr₂ := keep.reg .x1 (by decide)
  have out₂ : s₂.gpr .x8 = pack v := by
    rw [h₂.1]
    change ((s.gpr (wordReg 0) ||| ((v.getD 1 0).setWidth 64).rotateRight 48) |||
      ((v.getD 2 0).setWidth 64).rotateRight 32) |||
      ((v.getD 3 0).setWidth 64).rotateRight 16 = _
    rw [hv.1 0 (by decide)]
    exact (pack_eq v).symm
  refine WP.of_runBlock ⟨{s₂ with mem := s₂.mem.writeW (s₂.gpr .x1) (s₂.gpr .x8)}, ?_, ?_⟩
  · have valid : InRegions s₂.wr (s₂.gpr .x1) 8 := by rw [keep.wr, ptr₂]; exact writable
    simp only [runBlock_cons, VG.Proof.Rc2.AArch64.exec_str_x _ _ _ 0 (by decide) (by simpa using valid),
      runStep_some, runBlock_nil, BitVec.add_zero]
  · exact ⟨by rw [keep.mem, ptr₂, out₂], keep.reg, keep.rd, keep.wr⟩

end VG.Proof.Rc2.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Lit`. -/
section

/-! # Literal RC2 programs for kernel-evaluated checks -/

namespace VG

materialize_code Impl.Rc2.AArch64.encryptBlock
materialize_code Impl.Rc2.AArch64.decryptBlock

materialize_code Impl.Rc2.AArch64.expandKey

end VG

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.ConstantTime`. -/
section

/-! # Constant-time RC2 block and key-expansion programs -/

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.Impl.Rc2.AArch64

/-- Only argument pointers and explicitly public integer parameters agree;
all memory contents, including the key, schedule, and data, may differ. -/
def PublicRegs (rs : List Reg) (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

theorem encryptBlock_constantTime (pre : State → Prop) :
    ConstantTime isa pre (VG.Proof.Rc2.AArch64.PublicRegs [.x0, .x1, .x2]) encryptBlock := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

theorem decryptBlock_constantTime (pre : State → Prop) :
    ConstantTime isa pre (VG.Proof.Rc2.AArch64.PublicRegs [.x0, .x1, .x2]) decryptBlock := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

theorem expandKey_constantTime (pre : State → Prop) :
    ConstantTime isa pre (VG.Proof.Rc2.AArch64.PublicRegs [.x0, .x1, .x2, .x3, .x4]) expandKey := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ hp
  exact ⟨hp.1, fun r hr => hp.2 r (Taint.mem_ofRegs.mp hr)⟩

end VG.Proof.Rc2.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.AArch64.Block`. -/
section

/-! # Verified RC2 block encryption and decryption -/

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.Impl.Rc2.AArch64

def cipher (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (b : Spec.Rc2.Block) : Spec.Rc2.Block :=
  match d with
  | .encrypt => Spec.Rc2.encryptBlock k b
  | .decrypt => Spec.Rc2.decryptBlock k b

def blockContract (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, 128⟩
    let data : Region := ⟨s.gpr .x1, 8⟩
    let scratch : Region := ⟨s.gpr .x2, 256⟩
    s.rd = [key] ∧ s.wr = [data, scratch] ∧ key.Disjoint scratch ∧ data.Disjoint scratch
  post s s' := Spec.Rc2.blockAt s'.mem (s.gpr .x1) =
    VG.Proof.Rc2.AArch64.cipher d (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) (Spec.Rc2.blockAt s.mem (s.gpr .x1))
  pub := VG.Proof.Rc2.AArch64.PublicRegs [.x0, .x1, .x2]

theorem cipher_rounds (d : Spec.Rc2.Direction) (k : Spec.Rc2.Schedule) (b : Spec.Rc2.Block) :
    VG.Proof.Rc2.AArch64.cipher d k b = Spec.Rc2.encodeBlock
      ((List.range 16).foldl (fun v j => VG.Proof.Rc2.AArch64.roundSpec d k j v) (Spec.Rc2.decodeBlock b)) := by
  cases d <;> rfl

theorem save_eq : blockSave = Spill.saveCode .x2 (Spill.slots wordReg 4) := by decide +kernel

theorem restore_eq : blockRestore = Spill.restoreCode .x2 (Spill.slots wordReg 4) := by decide +kernel

theorem block_correct (d : Spec.Rc2.Direction) (s : State) (hs : (VG.Proof.Rc2.AArch64.blockContract d).pre s) :
    WP isa (.block (blockCode d)) s (fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ (VG.Proof.Rc2.AArch64.blockContract d).post s s') := by
  obtain ⟨hrd, hwr, keySep, dataSep⟩ := hs
  have writes : ∀ i < 4, InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [hwr]
    exact ⟨⟨s.gpr .x2, 256⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  simp only [blockCode, List.append_assoc]
  rw [WP.block_append_iff, VG.Proof.Rc2.AArch64.save_eq]
  apply WP.mono (Spill.save_wp (by decide) (Spill.forall_slots writes))
  intro s₁ h₁
  have scratchFrame : Frame [⟨s.gpr .x2, 256⟩] s.mem s₁.mem := by
    rw [h₁.mem]
    exact Spill.saveMem_frame_base (by decide) (by decide) _ _ _
  have input₁ : Spec.Rc2.blockAt s₁.mem (s₁.gpr .x1) = Spec.Rc2.blockAt s.mem (s.gpr .x1) := by
    rw [h₁.gpr]
    exact blockAt_frame scratchFrame _ (by simpa using dataSep)
  have schedule₁ : Spec.Rc2.scheduleAt s₁.mem (s₁.gpr .x0) =
      Spec.Rc2.scheduleAt s.mem (s.gpr .x0) := by
    rw [h₁.gpr]
    exact scheduleAt_frame scratchFrame _ (by simpa using keySep)
  have dataRead₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x1) 8 := by
    rw [h₁.gpr, h₁.rd, h₁.wr, hrd, hwr]
    exact ⟨⟨s.gpr .x1, 8⟩, by simp, Region.contains_self _ _⟩
  rw [WP.block_append_iff]
  apply WP.mono (VG.Proof.Rc2.AArch64.blockLoad_ok s₁ dataRead₁)
  intro s₂ h₂
  have read₂ : InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x0) 128 := by
    rw [h₂.2.rd, h₂.2.wr, h₂.2.reg .x0 (by decide), h₁.gpr, h₁.rd, h₁.wr, hrd, hwr]
    exact ⟨⟨s.gpr .x0, 128⟩, by simp, Region.contains_self _ _⟩
  rw [WP.block_append_iff]
  apply WP.mono (VG.Proof.Rc2.AArch64.rounds_ok d s₂ _ h₂.1 read₂)
  intro s₃ h₃
  have keep₂₃ := h₂.2.trans (h₃.2.weaken (fun _ hr => List.mem_cons_of_mem _ hr))
  have ptr₃ : s₃.gpr .x1 = s.gpr .x1 := (keep₂₃.reg .x1 (by decide)).trans (congrFun h₁.gpr .x1)
  have writable₃ : InRegions s₃.wr (s₃.gpr .x1) 8 := by
    rw [keep₂₃.wr, h₁.wr, hwr, ptr₃]
    exact ⟨⟨s.gpr .x1, 8⟩, by simp, Region.contains_self _ _⟩
  let v := (List.range 16).foldl (fun v j => VG.Proof.Rc2.AArch64.roundSpec d
    (Spec.Rc2.scheduleAt s.mem (s.gpr .x0)) j v) (Spec.Rc2.decodeBlock (Spec.Rc2.blockAt s.mem (s.gpr .x1)))
  have words₃ : VG.Proof.Rc2.AArch64.Words s₃ v := by
    rw [h₂.2.mem, h₂.2.reg .x0 (by decide), schedule₁, input₁] at h₃
    exact h₃.1
  rw [WP.block_append_iff]
  apply WP.mono (VG.Proof.Rc2.AArch64.blockStore_ok s₃ v words₃ writable₃)
  intro s₄ h₄
  have mem₄ : s₄.mem = s₁.mem.writeW (s.gpr .x1) (pack v) := by rw [h₄.1, keep₂₃.mem, ptr₃]
  have rd₄ : s₄.rd = s.rd := h₄.2.2.1.trans (keep₂₃.rd.trans h₁.rd)
  have wr₄ : s₄.wr = s.wr := h₄.2.2.2.trans (keep₂₃.wr.trans h₁.wr)
  have regs₄ (r : Reg) (hr : r ∉ .x9 :: VG.Proof.Rc2.AArch64.roundWrites) : s₄.gpr r = s.gpr r := by
    rw [h₄.2.1 r (by
      intro hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with he | he <;> subst r <;> exact hr (by decide)), keep₂₃.reg r hr, h₁.gpr]
  have scratchRead₄ : ∀ i ∈ List.range 4,
      InRegions (s₄.rd ++ s₄.wr) (s₄.gpr .x2 + BitVec.ofNat 64 (8 * i)) 8 := by
    intro i hi
    rw [rd₄, wr₄, regs₄ .x2 (by decide), hrd, hwr]
    have bound := List.mem_range.mp hi
    exact ⟨⟨s.gpr .x2, 256⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have saved₄ : ∀ i ∈ List.range 4,
      s₄.mem.readW (s₄.gpr .x2 + BitVec.ofNat 64 (8 * i)) 64 = s.gpr (wordReg i) := by
    intro i hi
    have bound := List.mem_range.mp hi
    rw [mem₄, regs₄ .x2 (by decide), Mem.readW_writeW_sep
      (dataSep.symm.sep (Offset.contains_base _ (by omega) (by omega)) (Region.contains_self _ _))
      (by decide), h₁.mem]
    exact Spill.saveMem_saved (l := Spill.slots wordReg 4) (by decide) s.mem (s.gpr .x2) s.gpr
      (wordReg i, 8 * i) (Spill.mem_slots bound)
  rw [VG.Proof.Rc2.AArch64.restore_eq]
  apply WP.mono (Spill.restore_wp rfl (by decide) (by decide)
    (Spill.forall_slots fun i hi => scratchRead₄ i (List.mem_range.mpr hi))
    (Spill.forall_slots fun i hi => saved₄ i (List.mem_range.mpr hi)))
  intro s₅ h₅
  have finalMem : s₅.mem = s₁.mem.writeW (s.gpr .x1) (pack v) := h₅.mem.trans mem₄
  constructor
  · intro r hr
    by_cases hm : r ∈ (List.range 4).map wordReg
    · exact h₅.gpr_of (.inl (by rwa [Spill.slots_fst]))
    · rw [h₅.other _ (by rwa [Spill.slots_fst])]
      have covered : ∀ r ∈ preserved,
          r ∈ (List.range 4).map wordReg ∨ r ∉ .x9 :: VG.Proof.Rc2.AArch64.roundWrites := by decide
      exact regs₄ r ((covered r hr).resolve_left hm)
  · change Spec.Rc2.blockAt s₅.mem (s.gpr .x1) = _
    rw [finalMem, blockAt_write64, VG.Proof.Rc2.AArch64.cipher_rounds]

def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 8⟩, ⟨0x3000, 256⟩]

theorem encrypt_correct (s : State) (hs : (VG.Proof.Rc2.AArch64.blockContract .encrypt).pre s) :
    ∃ t s', Exec isa encryptBlock s t s' ∧ abiPreserved s s' ∧
      (VG.Proof.Rc2.AArch64.blockContract .encrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := VG.Proof.Rc2.AArch64.block_correct .encrypt s hs
  change Exec isa encryptBlock s t s' at he
  exact ⟨t, s', he, ⟨ha, (VG.AArch64.Exec.regions he rfl).2.2.1, VG.AArch64.Exec.preservedV he (by lit_decide)⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (VG.Proof.Rc2.AArch64.blockContract .decrypt).pre s) :
    ∃ t s', Exec isa decryptBlock s t s' ∧ abiPreserved s s' ∧
      (VG.Proof.Rc2.AArch64.blockContract .decrypt).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := VG.Proof.Rc2.AArch64.block_correct .decrypt s hs
  change Exec isa decryptBlock s t s' at he
  exact ⟨t, s', he, ⟨ha, (VG.AArch64.Exec.regions he rfl).2.2.1, VG.AArch64.Exec.preservedV he (by lit_decide)⟩, hp⟩

theorem publicRegs_three (s₁ s₂ : State) : VG.Proof.Rc2.AArch64.PublicRegs [.x0, .x1, .x2] s₁ s₂ ↔
    s₁.sp = s₂.sp ∧ s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 := by
  simp [VG.Proof.Rc2.AArch64.PublicRegs]

theorem encrypt_verified :
    Verified target encryptBlock (Spec.Rc2.encryptBlockContract abi) := by
  refine Verified.of_correct VG.Proof.Rc2.AArch64.encrypt_correct (VG.Proof.Rc2.AArch64.encryptBlock_constantTime _) ?_
  sig_implies [Spec.Rc2.encryptBlockContract, Spec.Rc2.blockSig, abi, argRegs,
    VG.Proof.Rc2.AArch64.blockContract, VG.Proof.Rc2.AArch64.publicRegs_three, VG.Proof.Rc2.AArch64.cipher] [satState] using VG.Proof.Rc2.AArch64.satState

theorem decrypt_verified :
    Verified target decryptBlock (Spec.Rc2.decryptBlockContract abi) := by
  refine Verified.of_correct VG.Proof.Rc2.AArch64.decrypt_correct (VG.Proof.Rc2.AArch64.decryptBlock_constantTime _) ?_
  sig_implies [Spec.Rc2.decryptBlockContract, Spec.Rc2.blockSig, abi, argRegs,
    VG.Proof.Rc2.AArch64.blockContract, VG.Proof.Rc2.AArch64.publicRegs_three, VG.Proof.Rc2.AArch64.cipher] [satState] using VG.Proof.Rc2.AArch64.satState

end VG.Proof.Rc2.AArch64

end

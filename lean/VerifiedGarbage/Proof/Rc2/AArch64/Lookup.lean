import VerifiedGarbage.Impl.Rc2.AArch64.Lookup
import VerifiedGarbage.Proof.Rc2.Select
import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

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
    (h : Keep rs s s') (h' : Keep rs s' s'') : Keep rs s s'' :=
  ⟨fun r hr => (h'.reg r hr).trans (h.reg r hr), h'.mem.trans h.mem,
    h'.rd.trans h.rd, h'.wr.trans h.wr⟩

theorem byte_imm (b : Byte) : (BitVec.ofNat 16 b.toNat).setWidth 64 = b.setWidth 64 := by
  simp

theorem index_imm (i : Nat) (hi : i < 256) :
    (BitVec.ofNat 16 i).setWidth 64 = (BitVec.ofNat 8 i).setWidth 64 := by
  have h : BitVec.ofNat 16 i = (BitVec.ofNat 8 i).setWidth 16 := by bv_omega
  rw [h]; simp

theorem Keep.weaken {rs rs' : List Reg} {s s' : State} (h : Keep rs s s')
    (hsub : ∀ r ∈ rs, r ∈ rs') : Keep rs' s s' :=
  ⟨fun r hr => h.reg r (fun hm => hr (hsub r hm)), h.mem, h.rd, h.wr⟩

theorem maskBits (x : BitVec 64) (n : Nat) (hn : n ≤ 64) :
    x <<< (64 - n) >>> (64 - n) = (x.setWidth n).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth]
  have ha : 64 - n + i < 64 ↔ i < n := by omega_arith
  have hb : ¬64 - n + i < 64 - n := by omega_arith
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
  omega_arith


/-! ## The indices -/

theorem quarters_run (full : Bool) (s : State) :
    ∃ s', runBlock isa (quarters full) s = some s' ∧
      (∀ e < 16, vbyte (s'.v .v1) e = vbyte (s.v .v0) e ^^^ 64) ∧
      (full = true → ∀ e < 16, vbyte (s'.v .v2) e = vbyte (s.v .v0) e ^^^ 128 ∧
        vbyte (s'.v .v3) e = vbyte (s.v .v0) e ^^^ 192) ∧
      (∀ w, w ≠ .v1 → w ≠ .v2 → w ≠ .v3 → w ≠ .v4 → w ≠ .v5 → s'.v w = s.v w) ∧
      Keep [.x6] s s' := by
  let s₁ := s.write .x .x6 (BitVec.ofNat 64 64)
  let s₂ := s₁.setV .v4 (bc ((s₁.gpr .x6).setWidth 8))
  let s₃ := s₂.setV .v1 (s₂.v .v0 ^^^ s₂.v .v4)
  have k₃ : Keep [.x6] s s₃ :=
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
    rw [runBlock_cons, exec_imm _ _ _ (by decide), runStep_some, runBlock_cons, exec_dupb,
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
      rw [runBlock_cons, exec_imm _ _ _ (by decide), runStep_some, runBlock_cons, exec_dupb,
        runStep_some, runBlock_cons, exec_eorv, runStep_some, runBlock_cons,
        exec_imm _ _ _ (by decide), runStep_some, runBlock_cons, exec_dupb, runStep_some,
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
      Keep [.x8] s t ∧ t.v = s.v := by
  let e₁ := s.write .w .x8 ((s.v .v0).extractLsb' 0 32)
  let e₂ := e₁.write .x .x8 (e₁.gpr .x8 <<< (64 - n))
  let e₃ := e₂.write .x .x8 (e₂.gpr .x8 >>> (64 - n))
  refine WP.of_runBlock ⟨e₃, ?_, ?_, ?_, rfl⟩
  · rw [List.singleton_append, mask, runBlock_cons, exec_umovw0, runStep_some, runBlock_cons,
      exec_lslx _ _ _ (by omega_arith), runStep_some, runBlock_cons, exec_lsrx _ _ _ (by omega_arith),
      runStep_some, runBlock_nil]
  · simp only [e₃, e₂, e₁, gpr_write_self, BitVec.setWidth_eq]
    exact maskBits _ n (by omega_arith)
  · exact ⟨fun r hr => by
      have : r ≠ .x8 := fun e => hr (by simp [e])
      simp only [e₃, e₂, e₁, gpr_write_of_ne _ _ _ this], rfl, rfl, rfl⟩

theorem low_byte (v : BitVec 128) :
    ((((v.extractLsb' 0 32).setWidth 64).setWidth 8).setWidth 64) = (vbyte v 0).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, vbyte, BitVec.getLsbD_extractLsb']
  by_cases h : i < 8
  · simp [h, show i < 32 by omega_arith]
  · simp [h]

theorem piLookup_eq : piLookup = loadTable (fun k => Spec.Rc2.piTable.getD k 0) ++
    (([.vop (.dup .b16 .v0 .x8)] : List Instr) ++ (quarters true ++ (select true ++
      (([.umov .w .x8 .v0 0] : List Instr) ++ mask .x8 8)))) := by
  simp only [piLookup, List.append_assoc]

theorem piLookup_ok (s : State) :
    WP isa (.block piLookup) s (fun s' =>
      s'.gpr .x8 = (Spec.Rc2.pi ((s.gpr .x8).setWidth 8)).setWidth 64 ∧
      Keep [.x8, .x3, .x6, .x7] s s') := by
  rw [piLookup_eq, WP.block_append_iff]
  refine WP.mono (loadTable_ok s _) fun a ⟨arow, _, ag, am, ard, awr, _⟩ => ?_
  have ak : Keep [.x6, .x7] s a := ⟨fun r hr => ag r (fun e => hr (by simp [e]))
    (fun e => hr (by simp [e])), am, ard, awr⟩
  let X := (s.gpr .x8).setWidth 8
  let b := a.setV .v0 (bc ((a.gpr .x8).setWidth 8))
  have b0 : b.v .v0 = bc X := by
    simp only [b, v_setV_self, X, ak.reg .x8 (by decide)]
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨b, by rw [runBlock_cons, exec_dupb, runStep_some, runBlock_nil], ?_⟩
  rw [WP.block_append_iff]
  obtain ⟨c, runc, c1, c23, cv, ck⟩ := quarters_run true b
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
  refine WP.mono (umov_mask_ok d 8 (by decide) (by decide)) fun t ⟨t8, tk, _⟩ => ⟨?_, ?_⟩
  · rw [t8, low_byte, d0 0 (by decide), tab]
  · have kd : Keep [.x8, .x3, .x6, .x7] c t :=
      (⟨fun _ _ => by rw [dv.gpr], dv.mem, dv.rd, dv.wr⟩ : Keep [] c d).weaken (by simp) |>.trans
        (tk.weaken (by simp))
    have kb : Keep [.x8, .x3, .x6, .x7] a b := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
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
  | zero => exact WP.block_nil ⟨fun _ h => absurd h (by omega_arith), fun _ _ => rfl, rfl⟩
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (ih (by omega_arith)) fun a ⟨arow, av, ae⟩ => ?_
    have hin : InRegions (a.rd ++ a.wr) (a.gpr .x0 + BitVec.ofNat 64 (16 * n)) 16 := by
      rw [ae]; exact CallLay.inRegions_sub readable (by omega_arith) (by decide)
    refine WP.of_runBlock ⟨_, by
      rw [runBlock_cons, exec_ldrq' _ _ _ _ ⟨by omega_arith, by omega_arith⟩ hin, runStep_some, runBlock_nil],
      fun r hr => ?_, fun w hw => ?_, ?_⟩
    · have hmx : a.mem = s.mem ∧ a.gpr = s.gpr := by rw [ae]; exact ⟨rfl, rfl⟩
      by_cases he : r = n
      · subst he; rw [v_setV_self, hmx.1, hmx.2]
      · rw [v_setV_of_ne _ _ (fun e => he (treg_inj r (by omega_arith) n (by omega_arith) e)), arow r (by omega_arith)]
    · rw [v_setV_of_ne _ _ (hw n (by omega_arith)), av w (fun r hr => hw r (by omega_arith))]
    · rw [ae]; rfl

theorem tbyte_loaded {v : VReg → BitVec 128} (m : Mem) (p : Addr)
    (h : ∀ r < 8, v (treg r) = m.read (p + BitVec.ofNat 64 (16 * r)) 16) (k : Nat) (hk : k < 128) :
    tbyte v k = m (p + BitVec.ofNat 64 k) := by
  rw [tbyte, h _ (by omega_arith)]
  change (m.read _ 16).extractLsb' (8 * (k % 16)) 8 = _
  rw [Mem.extractLsb'_read m _ (by omega_arith), Offset.add_add, show 16 * (k / 16) + k % 16 = k by omega_arith]

theorem vbyte_dup4 (w : BitVec 32) {e : Nat} (he : e < 16) :
    vbyte (ofVWords w w w w) e = w.extractLsb' (8 * (e % 4)) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [vbyte, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  rw [getLsbD_ofVWords _ _ _ _ (by omega_arith)]
  split <;> (try split) <;> (try split) <;> (congr 1; omega_arith)

theorem index_table : ∀ j < 64, ∀ c < 4, (256 + 514 * j) / 2 ^ (8 * c) % 2 ^ 8 =
    if c = 0 then 2 * j else if c = 1 then 2 * j + 1 else 0 := by decide

/-- The index bytes: `2 j`, `2 j + 1`, 0 and 0 in each word. -/
theorem index_bytes (j : Nat) (hj : j < 64) (e : Nat) :
    ((BitVec.ofNat 32 (256 + 514 * j)).extractLsb' (8 * (e % 4)) 8).toNat =
      if e % 4 = 0 then 2 * j else if e % 4 = 1 then 2 * j + 1 else 0 := by
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (show 256 + 514 * j < 2 ^ 32 by omega_arith)]
  exact index_table j hj (e % 4) (by omega_arith)

theorem low_half (v : BitVec 128) :
    ((((v.extractLsb' 0 32).setWidth 64).setWidth 16).setWidth 64) =
      ((vbyte v 0).setWidth 16 ||| (vbyte v 1).setWidth 16 <<< 8).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, vbyte,
    BitVec.getLsbD_extractLsb']
  by_cases h8 : i < 8
  · simp [h8, show i < 16 by omega_arith, show i < 32 by omega_arith]
  · by_cases h16 : i < 16
    · simp [h8, h16, show i < 32 by omega_arith, show i - 8 < 8 by omega_arith, show i - 8 < 16 by omega_arith,
        show 8 + (i - 8) = i by omega_arith]
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
      Keep [.x8, .x3, .x4, .x5, .x6, .x7] s s') := by
  let j := ((s.gpr .x8).setWidth 6).toNat
  have hj : j < 64 := ((s.gpr .x8).setWidth 6).isLt
  rw [keyLookup_eq, WP.block_append_iff]
  -- the index, masked
  let a := (s.write .x .x8 (s.gpr .x8 <<< (64 - 6))).write .x .x8
    ((s.write .x .x8 (s.gpr .x8 <<< (64 - 6))).gpr .x8 >>> (64 - 6))
  have a8 : a.gpr .x8 = BitVec.ofNat 64 j := by
    simp only [a, gpr_write_self, BitVec.setWidth_eq]
    rw [maskBits _ 6 (by decide)]
    apply BitVec.eq_of_toNat_eq; simp [j]
  have ak : Keep [.x8] s a :=
    ⟨fun r hr => by
      have : r ≠ .x8 := fun e => hr (by simp [e])
      simp only [a, gpr_write_of_ne _ _ _ this], rfl, rfl, rfl⟩
  refine WP.of_runBlock ⟨a, by
    rw [mask, runBlock_cons, exec_lslx _ _ _ (by decide), runStep_some, runBlock_cons,
      exec_lsrx _ _ _ (by decide), runStep_some, runBlock_nil], ?_⟩
  rw [WP.block_append_iff]
  have ra : InRegions (a.rd ++ a.wr) (a.gpr .x0) 128 := by
    rw [ak.rd, ak.wr, ak.reg .x0 (by decide)]; exact readable
  refine WP.mono (loads_ok a ra 8 (by decide)) fun b ⟨brow, bv, be⟩ => ?_
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
    omega_arith
  refine WP.of_runBlock ⟨c, by
    rw [runBlock_cons, exec_imm _ _ _ (by decide), runStep_some, runBlock_cons,
      exec_imm _ _ _ (by decide), runStep_some, runBlock_cons, exec_madd, runStep_some,
      runBlock_cons, exec_dups, runStep_some, runBlock_nil], ?_⟩
  rw [WP.block_append_iff]
  let I : Nat → BitVec 8 := fun e => vbyte (c.v .v0) e
  have hI : ∀ e < 16, (I e).toNat =
      if e % 4 = 0 then 2 * j else if e % 4 = 1 then 2 * j + 1 else 0 := by
    intro e he
    simp only [I, c, v_setV_self, vbyte_dup4 _ he, hw]
    exact index_bytes j hj e
  obtain ⟨d, rund, d1, _, dv, dk⟩ := quarters_run false c
  refine WP.of_runBlock ⟨d, rund, ?_⟩
  rw [WP.block_append_iff]
  have d0 : d.v .v0 = c.v .v0 := dv _ (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨f, runf, f0, fv⟩ := select_half_run (s := d) I
    (fun e he => by rw [hI e he]; split <;> (try split) <;> omega_arith)
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
    rw [tbyte_congr hdb _ (by omega_arith), tbyte_loaded _ _ brow k hk, ak.mem, ak.reg .x0 (by decide)]
  refine WP.mono (umov_mask_ok f 16 (by decide) (by decide)) fun t ⟨t8, tk, _⟩ => ⟨?_, ?_⟩
  · have e0 : (I 0).toNat = 2 * j := by rw [hI 0 (by decide)]; rfl
    have e1 : (I 1).toNat = 2 * j + 1 := by rw [hI 1 (by decide)]; rfl
    rw [t8, low_half, f0 0 (by decide), f0 1 (by decide), e0, e1, tab _ (by omega_arith), tab _ (by omega_arith),
      scheduleAt_getD _ _ _ hj]
  · have kc : Keep [.x8, .x3, .x4, .x5, .x6, .x7] b c :=
      ⟨fun r hr => by
        have h8 : r ≠ .x8 := fun e => hr (by simp [e])
        have h3 : r ≠ .x3 := fun e => hr (by simp [e])
        have h6 : r ≠ .x6 := fun e => hr (by simp [e])
        simp only [c, gpr_setV, c₃, c₂, c₁, gpr_write_of_ne _ _ _ h8, gpr_write_of_ne _ _ _ h6,
          gpr_write_of_ne _ _ _ h3], rfl, rfl, rfl⟩
    have kb : Keep [.x8, .x3, .x4, .x5, .x6, .x7] a b :=
      ⟨fun r _ => by rw [bg], bm, by rw [be], by rw [be]⟩
    have kf : Keep [.x8, .x3, .x4, .x5, .x6, .x7] d f := ⟨fun _ _ => by rw [fv.gpr], fv.mem, fv.rd, fv.wr⟩
    exact ((((ak.weaken (by simp)).trans kb).trans kc).trans (dk.weaken (by simp))).trans
      (kf.trans (tk.weaken (by simp)))

end VG.Proof.Rc2.AArch64

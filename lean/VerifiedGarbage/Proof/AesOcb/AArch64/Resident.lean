import VerifiedGarbage.Proof.AesOcb.AArch64.Vector

/-! Register-resident offsets and checksums for payload batches. -/
set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Ocb (Block blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt blockAtMem_frame)
open VG.Proof.AesGcm.AArch64 (eval_zero eval_nonzero)

def ckOp (mode : CkMode) (c b o : Block) : Block :=
  match mode with
  | .none => c
  | .before => c ^^^ b
  | .after => c ^^^ (b ^^^ o)

structure ResidentInv (K W D : Addr) (R n : Nat) (SP : Addr) (m : Nat) (O0 l : Block) (X : Nat → Block)
    (ckF : Nat → Block) (t₀ t : State) (i : Nat) : Prop where
  env : Env K W D R n SP t
  frame : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩, ⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 ckO, 16⟩,
    ⟨D, 16 * m⟩] t₀.mem t.mem
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  x23 : t.gpr .x23 = D + BitVec.ofNat 64 (16 * i)
  x25 : t.gpr .x25 = BitVec.ofNat 64 (i + 1)
  x24 : t.gpr .x24 = BitVec.ofNat 64 (m - i)
  ofs : vBlock (t.v .v3) = offAt O0 l i
  ck : vBlock (t.v .v5) = ckF i
  blk : ∀ k < m, blockAtMem t.mem (D + BitVec.ofNat 64 (16 * k)) =
    if k < i then X k ^^^ offAt O0 l (k + 1) else X k
  l0 : blockAtMem t.mem (W + BitVec.ofNat 64 l0O) = lAt l 0
  gpr : ∀ r, r ∉ passRegs → t.gpr r = t₀.gpr r

theorem ResidentInv.of_temp {K W D : Addr} {R n : Nat} {SP : Addr} {m i : Nat} {O0 l : Block}
    {X : Nat → Block} {ckF : Nat → Block} {s t u : State}
    (P : ResidentInv K W D R n SP m O0 l X ckF s t i) (hD : DBuf K W s D (16 * m))
    (fr : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] t.mem u.mem)
    (g : ∀ r, r ∉ ntzRegs → u.gpr r = t.gpr r) (sp : u.sp = t.sp) (rd : u.rd = t.rd) (wr : u.wr = t.wr)
    (v3 : u.v .v3 = t.v .v3) (v5 : u.v .v5 = t.v .v5) :
    ResidentInv K W D R n SP m O0 l X ckF s u i := by
  have wb {a : Nat} (ha : a + 16 ≤ 96) :
      blockAtMem u.mem (W + BitVec.ofNat 64 a) = blockAtMem t.mem (W + BitVec.ofNat 64 a) :=
    blockAtMem_frame fr fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (.inl ha) (by omega) (by decide)
  refine { P with
    env := P.env.keep (fun r hr => g r (by
      simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)) sp rd wr
    frame := P.frame.trans (fr.mono (by simp))
    rd := rd.trans P.rd, wr := wr.trans P.wr
    x23 := (g _ (by decide)).trans P.x23
    x24 := (g _ (by decide)).trans P.x24
    x25 := (g _ (by decide)).trans P.x25
    ofs := (congrArg vBlock v3).trans P.ofs
    ck := (congrArg vBlock v5).trans P.ck
    l0 := (wb (by decide)).trans P.l0
    blk := ?_
    gpr := fun r hr => (g r (fun h => hr (by
      simp only [ntzRegs, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [passRegs]))).trans (P.gpr r hr) }
  intro k hk
  rw [blockAtMem_frame fr (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hD.slice (a := 16 * k) (k := 16) (by omega)).w.sub_right (Lay.wSub (by decide))), P.blk k hk]


/-- One payload block, with both accumulators in registers. -/
theorem residentBlock_ok (mode : CkMode) (s : State) {B : Addr} (h23 : s.gpr .x23 = B)
    (rq : InRegions (s.rd ++ s.wr) B 16) (wq : InRegions s.wr B 16) :
    ∃ t, runBlock isa (residentBody mode ++ nextBlock) s = some t ∧
      Frame [⟨B, 16⟩] s.mem t.mem ∧
      blockAtMem t.mem B = blockAtMem s.mem B ^^^ vBlock (s.v .v3) ∧
      vBlock (t.v .v5) = ckOp mode (vBlock (s.v .v5)) (blockAtMem s.mem B) (vBlock (s.v .v3)) ∧
      t.v .v3 = s.v .v3 ∧ t.gpr .x23 = B + 16#64 ∧
      t.gpr .x25 = s.gpr .x25 + 1#64 ∧ t.gpr .x24 = s.gpr .x24 - 1#64 ∧
      (∀ r, r ≠ .x23 → r ≠ .x24 → r ≠ .x25 → t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  cases mode <;>
    refine ⟨_, by orun [residentBody, nextBlock, h23, rq, wq, VOp.eval, v_setV, gpr_setV, mem_setV, rd_setV, wr_setV, sp_setV],
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h₁ h₂ h₃ => ?_, ?_, ?_, ?_⟩
  all_goals try (exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _))
  all_goals try (simp only [mem_write, mem_setV, gpr_setV, v_setV, reduceCtorEq, ↓reduceIte, h23, BitVec.add_zero])
  all_goals try (rw [blockAtMem_storeV, vBlock_xor, vBlock_read])
  all_goals try (simp only [v_write, v_setV, reduceCtorEq, ↓reduceIte, ckOp, vBlock_xor, vBlock_read, h23, BitVec.add_zero])
  all_goals try (simp [gpr_write, gpr_setV, h23, * ])
  all_goals rfl

theorem residentStep_ok {K W D : Addr} {R n : Nat} {SP : Addr} {m i : Nat} {O0 l : Block}
    {X : Nat → Block} {ckF : Nat → Block} {s t₀ : State} (mode : CkMode)
    (hD : DBuf K W t₀ D (16 * m)) (hi : i < m)
    (P : ResidentInv K W D R n SP m O0 l X ckF t₀ s i)
    (hck : ckF (i + 1) = ckOp mode (ckF i) (X i) (offAt O0 l (i + 1)))
    (v : VReg) (hv : vBlock (s.v v) = lAt l (ntz (i + 1))) :
    WP isa (residentStep v mode) s fun t => ResidentInv K W D R n SP m O0 l X ckF t₀ t (i + 1) := by
  let u := s.setV .v3 (s.v .v3 ^^^ s.v v)
  have run₀ : runBlock isa [.vop (.logic .eor .v3 .v3 v)] s = some u := by orun [VOp.eval]
  have ofs : vBlock (u.v .v3) = offAt O0 l (i + 1) := by
    rw [v_setV_self, vBlock_xor, P.ofs, hv]; rfl
  have B := (hD.of_eq P.rd P.wr).slice (a := 16 * i) (k := 16) (by omega)
  obtain ⟨t, run, fr, val, ck, v3, x23, x25, x24, g, sp, rd, wr⟩ := residentBlock_ok mode u P.x23
    (B.rd _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)
    (B.wr _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)
  have memu : u.mem = s.mem := rfl
  have old : blockAtMem u.mem (D + BitVec.ofNat 64 (16 * i)) = X i := by rw [memu, P.blk i hi]; simp
  unfold residentStep
  refine WP.of_runBlock ⟨t, by rw [List.append_assoc, runBlock_append, run₀, Option.bind_some, run], ?_⟩
  refine ⟨P.env.keep (fun r hr => ?_) sp rd wr,
    P.frame.trans (fr.sub fun r hr => ?_), rd.trans P.rd, wr.trans P.wr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g _ (by decide) (by decide) (by decide)
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨D, 16 * m⟩, by simp, Offset.sub_base D (by omega)⟩
  · rw [x23, Offset.add_add, show 16 * i + 16 = 16 * (i + 1) by omega]
  · rw [x25]; change s.gpr .x25 + 1#64 = _
    rw [P.x25, ← BitVec.ofNat_add]
  · rw [x24]; change s.gpr .x24 - 1#64 = _
    rw [P.x24, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  · rw [v3, ofs]
  · rw [ck, old, ofs]; change ckOp mode (vBlock (s.v .v5)) (X i) _ = _
    rw [P.ck, hck]
  · intro k hk
    by_cases hki : k = i
    · subst hki
      rw [val, old, ofs]; simp
    · rw [blockAtMem_frame fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint D (by omega) (by have := hD.wrap; omega) (by have := hD.wrap; omega)), memu, P.blk k hk]
      by_cases hki' : k < i
      · simp only [ite_eq_left hki', ite_eq_left (show k < i + 1 by omega)]
      · simp only [ite_eq_right hki', ite_eq_right (show ¬k < i + 1 by omega)]
  · rw [blockAtMem_frame fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (B.w.sub_right (Lay.wSub (W := W) (d := l0O) (n := 16) (by decide))).symm), memu, P.l0]
  · have h23 : r ≠ .x23 := fun h => hr (by simp [passRegs, h])
    have h24 : r ≠ .x24 := fun h => hr (by simp [passRegs, h])
    have h25 : r ≠ .x25 := fun h => hr (by simp [passRegs, h])
    rw [g r h23 h24 h25]; exact P.gpr r hr

theorem residentStep_keeps (v : VReg) (mode : CkMode) :
    (residentStep v mode).allInstrs keepsCache = true := by
  rw [Code.allInstrs_eq]
  cases mode <;> simp [residentStep, residentBody, nextBlock, instrs, List.all_append,
    keepsCache, vdstOf, VOp.dst, Impl.AesGcm.AArch64.ptr]

theorem batchLast_noV (v : VReg) :
    batchLastIncrement.allInstrs (fun i => decide (vdstOf i ≠ some v)) = true := by
  rw [Code.allInstrs_eq]
  simp [batchLastIncrement, cachedIncrement, dbl, low1, instrs, List.all_append, vdstOf, ld, st,
    Impl.AesGcm.AArch64.imm]

theorem residentLoad_ok {K W D : Addr} {R n : Nat} {SP : Addr} {m i : Nat} {O0 l : Block}
    {X ckF : Nat → Block} {s t₀ : State}
    (P : PassInv K W D R n SP m O0 l X (fun b o => b ^^^ o) ckF t₀ s i) (C : LCache l s) :
    WP isa (.block [.ldrq .v3 .x19 ofsO, .ldrq .v5 .x19 ckO]) s fun t =>
      ResidentInv K W D R n SP m O0 l X ckF t₀ t i ∧ LCache l t := by
  let u := s.setV .v3 (s.mem.read (W + BitVec.ofNat 64 ofsO) 16)
  let z := u.setV .v5 (u.mem.read (W + BitVec.ofNat 64 ckO) 16)
  have r₁ := loadV_run (s := s) .v3 (a := ofsO) (by decide) P.env.x19 (P.env.perm.wR (by decide))
  have r₂ := loadV_run (s := u) .v5 (a := ckO) (by decide) P.env.x19 (P.env.perm.wR (by decide))
  refine WP.of_runBlock ⟨z, ?_, ?_, ?_⟩
  · change runBlock isa ([.ldrq .v3 .x19 ofsO] ++ [.ldrq .v5 .x19 ckO]) s = some z
    rw [runBlock_append, r₁, Option.bind_some, r₂]
  · refine ⟨P.env.keep (fun _ _ => rfl) rfl rfl rfl, P.frame, P.rd, P.wr, P.x23, P.x25, P.x24, ?_, ?_, P.blk, P.l0, P.gpr⟩
    · simp only [z, u, v_setV, reduceCtorEq, ↓reduceIte, vBlock_read, P.ofs]
    · simp only [z, u, v_setV, reduceCtorEq, ↓reduceIte, mem_setV, vBlock_read, P.ck]
  · simpa only [z, u, LCache, v_setV, reduceCtorEq, ↓reduceIte] using C

theorem residentStore_ok {K W D : Addr} {R n : Nat} {SP : Addr} {m i : Nat} {O0 l : Block}
    {X ckF : Nat → Block} {s t₀ : State} (hD : DBuf K W t₀ D (16 * m))
    (P : ResidentInv K W D R n SP m O0 l X ckF t₀ s i) :
    WP isa (.block [.strq .v3 .x19 ofsO, .strq .v5 .x19 ckO]) s fun t =>
      PassInv K W D R n SP m O0 l X (fun b o => b ^^^ o) ckF t₀ t i := by
  let m₁ := s.mem.write (W + BitVec.ofNat 64 ofsO) 16 (s.v .v3)
  let m₂ := m₁.write (W + BitVec.ofNat 64 ckO) 16 (s.v .v5)
  have f₁ : Frame [⟨W + BitVec.ofNat 64 ofsO, 16⟩] s.mem m₁ :=
    (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have f₂ : Frame [⟨W + BitVec.ofNat 64 ckO, 16⟩] m₁ m₂ :=
    (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have fr : Frame [⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 ckO, 16⟩] s.mem m₂ :=
    (f₁.mono (by simp)).trans (f₂.mono (by simp))
  have wO : InRegions s.wr (W + 16#64) 16 := P.env.perm.wW (d := ofsO) (by decide)
  have wC : InRegions s.wr (W + 32#64) 16 := P.env.perm.wW (d := ckO) (by decide)
  refine WP.of_runBlock ⟨_, by orun [P.env.x19, wO, wC], ?_⟩
  refine ⟨P.env.keep (fun _ _ => rfl) rfl rfl rfl, P.frame.trans (fr.mono (by simp)), P.rd, P.wr, P.x23, P.x25, P.x24, ?_, ?_, ?_, ?_, P.gpr⟩
  · change blockAtMem m₂ _ = _
    rw [blockAtMem_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint W (.inl (by decide)) (by decide) (by decide))]
    rw [blockAtMem_storeV, P.ofs]
  · change blockAtMem (m₁.write (W + BitVec.ofNat 64 ckO) 16 (s.v .v5)) (W + BitVec.ofNat 64 ckO) = _
    rw [blockAtMem_storeV, P.ck]
  · intro k hk
    change blockAtMem m₂ _ = _
    have B := hD.slice (a := 16 * k) (k := 16) (by omega)
    rw [blockAtMem_frame fr (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact B.w.sub_right (Lay.wSub (by decide))), P.blk k hk]
  · change blockAtMem m₂ _ = _
    rw [blockAtMem_frame fr (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact Offset.disjoint W (.inr (by decide)) (by decide) (by decide)), P.l0]

theorem residentCount_ok {K W D : Addr} {R n : Nat} {SP : Addr} {m i : Nat} {O0 l : Block}
    {X ckF : Nat → Block} {s t₀ : State}
    (P : ResidentInv K W D R n SP m O0 l X ckF t₀ s i) (hD : DBuf K W t₀ D (16 * m)) (hm : m < 2^60) :
    WP isa (.block [.lsr .x .x9 .x24 3]) s fun t =>
      ResidentInv K W D R n SP m O0 l X ckF t₀ t i ∧
      t.gpr .x9 = BitVec.ofNat 64 ((m-i)/8) ∧ t.v = s.v := by
  refine WP.of_runBlock ⟨s.write .x .x9 (s.gpr .x24 >>> 3), by orun [], ?_⟩
  refine ⟨P.of_temp hD (Frame.refl _ _) (fun r hr => ?_) rfl rfl rfl rfl rfl, ?_, rfl⟩
  · have h : r ≠ .x9 := fun h => hr (by simp [ntzRegs, h])
    simp [gpr_write, h]
  · simp [gpr_write, P.x24, Proof.AesGcm.AArch64.lsr_ofNat _ _ (show m-i < 2^64 by omega)]

section
variable {K W D : Addr} {R n : Nat} {SP : Addr} {m : Nat} {O0 l : Block}
  {X ckF : Nat → Block} {t₀ : State} (mode : CkMode)
  (hckF : ∀ i < m, ckF (i + 1) = ckOp mode (ckF i) (X i) (offAt O0 l (i + 1)))
  (hD : DBuf K W t₀ D (16 * m)) (hm : m < 2^60)
include mode hckF hD

theorem residentStep_cached_ok {s : State} {i : Nat} (hi : i < m)
    (P : ResidentInv K W D R n SP m O0 l X ckF t₀ s i) (C : LCache l s)
    (v : VReg) (hv : vBlock (s.v v) = lAt l (ntz (i + 1))) :
    WP isa (residentStep v mode) s fun t => ResidentInv K W D R n SP m O0 l X ckF t₀ t (i + 1) ∧ LCache l t :=
  keepCache (residentStep_ok mode hD hi P (hckF i hi) v hv) (residentStep_keeps v mode) C

include hm in
 theorem residentLast_ok {s : State} {k : Nat} (hi : 8 * k + 7 < m)
    (P : ResidentInv K W D R n SP m O0 l X ckF t₀ s (8 * k + 7)) (C : LCache l s) :
    WP isa (residentLast mode) s fun t => ResidentInv K W D R n SP m O0 l X ckF t₀ t (8 * k + 7 + 1) ∧ LCache l t := by
  obtain ⟨tr, u, ex, Q⟩ := batchLastIncrement_ok (k := k) P.env C (by omega)
    (by simpa only [show 8 * k + 7 + 1 = 8 * k + 8 by omega] using P.x25)
  have vv (v : VReg) : u.v v = s.v v := Exec.vec (r := v)
    (fun i hi => of_decide_eq_true (List.all_eq_true.mp
      ((Code.allInstrs_eq _ batchLastIncrement) ▸ batchLast_noV v) i hi)) ex
  have P₁ := P.of_temp hD Q.frame Q.gpr Q.sp Q.rd Q.wr (vv .v3) (vv .v5)
  let u₂ := u.setV .v6 (u.mem.read (W + BitVec.ofNat 64 lO) 16)
  have run := loadV_run (s := u) .v6 (a := lO) (by decide) P₁.env.x19 (P₁.env.perm.wR (by decide))
  have P₂ : ResidentInv K W D R n SP m O0 l X ckF t₀ u₂ (8 * k + 7) :=
    P₁.of_temp hD (Frame.refl _ _) (fun _ _ => rfl) rfl rfl rfl
      (v_setV_of_ne _ _ (by decide)) (v_setV_of_ne _ _ (by decide))
  have C₂ : LCache l u₂ := by simpa only [u₂, LCache, v_setV, reduceCtorEq, ↓reduceIte, vv] using C
  unfold residentLast
  refine WP.seq ⟨tr, u, ex, ?_⟩
  refine WP.seq (WP.of_runBlock ⟨u₂, run, ?_⟩)
  exact residentStep_cached_ok mode hckF hD hi P₂ C₂ .v6
    (by rw [v_setV_self, vBlock_read, Q.val])

include hm in
 theorem residentBatch_ok {t : State} {k : Nat} (hk : 8 * k + 8 ≤ m)
    (P : ResidentInv K W D R n SP m O0 l X ckF t₀ t (8 * k)) (C : LCache l t) :
    WP isa (residentBatch mode) t fun u =>
      ResidentInv K W D R n SP m O0 l X ckF t₀ u (8 * (k + 1)) ∧ LCache l u := by
  unfold residentBatch
  refine WP.seq (WP.mono (residentStep_cached_ok mode hckF hD (by omega) P C .v0
    (by rw [Proof.Ocb.ntz_odd (by omega)]; exact C.1)) fun t₁ ⟨P₁, C₁⟩ => ?_)
  refine WP.seq (WP.mono (residentStep_cached_ok mode hckF hD (by omega) P₁ C₁ .v1
    (by rw [show 8 * k + 1 + 1 = 8 * k + 2 by omega, ntz_eight_two]; exact C₁.2.1)) fun t₂ ⟨P₂, C₂⟩ => ?_)
  refine WP.seq (WP.mono (residentStep_cached_ok mode hckF hD (by omega) P₂ C₂ .v0
    (by rw [Proof.Ocb.ntz_odd (by omega)]; exact C₂.1)) fun t₃ ⟨P₃, C₃⟩ => ?_)
  refine WP.seq (WP.mono (residentStep_cached_ok mode hckF hD (by omega) P₃ C₃ .v2
    (by rw [show 8 * k + 1 + 1 + 1 + 1 = 8 * k + 4 by omega, ntz_eight_four]; exact C₃.2.2)) fun t₄ ⟨P₄, C₄⟩ => ?_)
  refine WP.seq (WP.mono (residentStep_cached_ok mode hckF hD (by omega) P₄ C₄ .v0
    (by rw [Proof.Ocb.ntz_odd (by omega)]; exact C₄.1)) fun t₅ ⟨P₅, C₅⟩ => ?_)
  refine WP.seq (WP.mono (residentStep_cached_ok mode hckF hD (by omega) P₅ C₅ .v1
    (by rw [show 8 * k + 1 + 1 + 1 + 1 + 1 + 1 = 8 * k + 6 by omega, ntz_eight_six]; exact C₅.2.1)) fun t₆ ⟨P₆, C₆⟩ => ?_)
  refine WP.seq (WP.mono (residentStep_cached_ok mode hckF hD (by omega) P₆ C₆ .v0
    (by rw [Proof.Ocb.ntz_odd (by omega)]; exact C₆.1)) fun t₇ ⟨P₇, C₇⟩ => ?_)
  refine WP.mono (residentLast_ok (R := R) (n := n) (SP := SP) (k := k) mode hckF hD hm (by omega)
    (by simpa only [show 8 * k + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 8 * k + 7 by omega] using P₇) C₇) fun u ⟨P₈, C₈⟩ => ?_
  exact ⟨by simpa only [show 8 * k + 7 + 1 = 8 * (k + 1) by omega] using P₈, C₈⟩
include hm in
 theorem passFast_ok (L : Lay K W) {body : List Instr}
    (hB : BodyOk W body (fun b o => b ^^^ o) (ckOp mode)) {t : State} (hm0 : 0 < m)
    (P : PassInv K W D R n SP m O0 l X (fun b o => b ^^^ o) ckF t₀ t 0) :
    WP isa (passFast mode body) t fun u => PassInv K W D R n SP m O0 l X (fun b o => b ^^^ o) ckF t₀ u m := by
  unfold passFast
  refine WP.seq (WP.mono (passCount_ok P hD hm) fun t₁ ⟨P₁, h9, _⟩ => ?_)
  refine WP.ite _ (eval_zero h9 (by omega)) (fun hz => ?_) (fun hn => ?_)
  · exact passScalar_ok L hB hckF hD hm0 hm P₁
  · have hn : m / 8 ≠ 0 := of_decide_eq_false hn
    refine WP.seq (WP.mono (passCacheInit_ok P₁ hD) fun t₂ ⟨P₂, C₂⟩ => ?_)
    refine WP.seq (WP.mono (residentLoad_ok P₂ C₂) fun t₃ ⟨P₃, C₃⟩ => ?_)
    have loop : WP isa (.loop (.seq (residentBatch mode) (.block [.lsr .x .x9 .x24 3])) (.nonzero .x .x9)) t₃
        (fun u => ResidentInv K W D R n SP m O0 l X ckF t₀ u (8 * (m/8))) := by
      refine WP.loop (M := isa)
        (fun (j : Nat) (u : State) => ∃ k, j = m/8-k ∧ 8 * k + 8 ≤ m ∧
          ResidentInv K W D R n SP m O0 l X ckF t₀ u (8 * k) ∧ LCache l u) ?_
        (m/8) _ ⟨0, by omega, by omega, P₃, C₃⟩
      rintro j u ⟨k, rfl, hk, P, C⟩
      refine WP.seq (WP.mono (residentBatch_ok mode hckF hD hm hk P C) fun u₁ ⟨P', C'⟩ => ?_)
      refine WP.mono (residentCount_ok P' hD hm) fun u₂ ⟨P'', h9, hv⟩ => ?_
      have ev := eval_nonzero h9 (by omega)
      by_cases he : (m-8 * (k + 1))/8 = 0
      · left
        exact ⟨ev.trans (by simp [he]), (show k + 1 = m/8 by omega) ▸ P''⟩
      · right
        refine ⟨ev.trans (by simp [he]), m/8-(k + 1), by omega, k + 1, rfl, by omega, P'', ?_⟩
        simpa only [LCache, hv] using C'
    refine WP.seq (WP.mono loop fun u P' => ?_)
    refine WP.seq (WP.mono (residentStore_ok hD P') fun z Pz => ?_)
    refine WP.ite _ (eval_zero Pz.x24 (by omega)) (fun hz => ?_) (fun hn => ?_)
    · have hz : m-8 * (m/8) = 0 := of_decide_eq_true hz
      exact WP.block_nil (by simpa only [show 8 * (m/8) = m by omega] using Pz)
    · have hn : m-8 * (m/8) ≠ 0 := of_decide_eq_false hn
      exact passScalar_ok L hB hckF hD (by omega) hm Pz

end

end VG.Proof.AesOcb.AArch64

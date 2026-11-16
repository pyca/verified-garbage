module
public import VerifiedGarbage.Proof.AesOcb.AArch64.Batch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.AesOcb.AArch64.Args
import VerifiedGarbage.Proof.AesOcb.AArch64.RestTag
import VerifiedGarbage.Proof.Ocb.Bytes
import VerifiedGarbage.Proof.AesOcb.AArch64.Nonce
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! ### `AesOcb.AArch64.Whole`, which only this module used -/

section

/-! ### `AesOcb.AArch64.Resident`, which only this module used -/

section

/-! ### `AesOcb.AArch64.Vector`, which only this module used -/

section

/-! Vector block transfers and XOR, against the existing OCB block specification. -/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Ocb (Block blockAtMem)

theorem vBlock_xor (x y : BitVec 128) : vBlock (x ^^^ y) = vBlock x ^^^ vBlock y := by
  unfold vBlock
  rw [← Proof.Ocb.ofBytes_xor (by simp) (by simp)]
  congr 1
  simp only [Spec.Ocb.xor, List.zipWith_map, List.zipWith_self]
  apply List.map_congr_left
  intro j hj
  exact BitVec.extractLsb'_xor ..

theorem blockAtMem_storeV (m : Mem) (p : Addr) (x : BitVec 128) :
    blockAtMem (m.write p 16 x) p = vBlock x := by
  rw [← vBlock_read]
  change vBlock ((m.writeW p x).readW p 128) = _
  rw [Mem.readW_writeW_self m p 16 x (by decide)]

end VG.Proof.AesOcb.AArch64

end

end


/-! Register-resident offsets and checksums for payload batches. -/

@[expose] public section

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
      exact Offset.disjoint W (.inl ha) (by omega_arith) (by decide)
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
    exact (hD.slice (a := 16 * k) (k := 16) (by omega_arith)).w.sub_right (Lay.wSub (by decide))), P.blk k hk]


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
  obtain run₀ : runBlock isa [.vop (.logic .eor .v3 .v3 v)] s = some u := by orun [VOp.eval]
  obtain ofs : vBlock (u.v .v3) = offAt O0 l (i + 1) := by
    rw [v_setV_self, vBlock_xor, P.ofs, hv]; rfl
  obtain B := (hD.of_eq P.rd P.wr).slice (a := 16 * i) (k := 16) (by omega_arith)
  obtain ⟨t, run, fr, val, ck, v3, x23, x25, x24, g, sp, rd, wr⟩ := residentBlock_ok mode u P.x23
    (B.rd _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)
    (B.wr _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)
  have memu : u.mem = s.mem := rfl
  obtain old : blockAtMem u.mem (D + BitVec.ofNat 64 (16 * i)) = X i := by rw [memu, P.blk i hi]; simp
  unfold residentStep
  refine WP.of_runBlock ⟨t, by rw [List.append_assoc, runBlock_append, run₀, Option.bind_some, run], ?_⟩
  refine ⟨P.env.keep (fun r hr => ?_) sp rd wr,
    P.frame.trans (fr.sub fun r hr => ?_), rd.trans P.rd, wr.trans P.wr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · simp only [envRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g _ (by decide) (by decide) (by decide)
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨⟨D, 16 * m⟩, by simp, Offset.sub_base D (by omega_arith)⟩
  · rw [x23, Offset.add_add, show 16 * i + 16 = 16 * (i + 1) by omega_arith]
  · rw [x25]; change s.gpr .x25 + 1#64 = _
    rw [P.x25, ← BitVec.ofNat_add]
  · rw [x24]; change s.gpr .x24 - 1#64 = _
    rw [P.x24, Offset.ofNat_sub_ofNat (by omega_arith), Nat.sub_sub]
  · rw [v3, ofs]
  · rw [ck, old, ofs]; change ckOp mode (vBlock (s.v .v5)) (X i) _ = _
    rw [P.ck, hck]
  · intro k hk
    by_cases hki : k = i
    · subst hki
      rw [val, old, ofs]; simp
    · rw [blockAtMem_frame fr (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint D (by omega_arith) (by have := hD.wrap; omega_arith) (by have := hD.wrap; omega_arith)), memu, P.blk k hk]
      by_cases hki' : k < i
      · simp only [ite_eq_left hki', ite_eq_left (show k < i + 1 by omega_arith)]
      · simp only [ite_eq_right hki', ite_eq_right (show ¬k < i + 1 by omega_arith)]
  · rw [blockAtMem_frame fr (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (B.w.sub_right (Lay.wSub (W := W) (d := l0O) (n := 16) (by decide))).symm), memu, P.l0]
  · have h23 : r ≠ .x23 := fun h => hr (by simp [passRegs, h])
    obtain h24 : r ≠ .x24 := fun h => hr (by simp [passRegs, h])
    obtain h25 : r ≠ .x25 := fun h => hr (by simp [passRegs, h])
    rw [g r h23 h24 h25]; exact P.gpr r hr

theorem residentStep_keeps (v : VReg) (mode : CkMode) :
    (residentStep v mode).allInstrs keepsCache = true := by
  rw [Code.allInstrs_eq]
  cases mode <;> rfl

theorem batchLast_noV (v : VReg) :
    batchLastIncrement.allInstrs (fun i => decide (vdstOf i ≠ some v)) = true := by
  rw [Code.allInstrs_eq]
  rfl

theorem residentLoad_ok {K W D : Addr} {R n : Nat} {SP : Addr} {m i : Nat} {O0 l : Block}
    {X ckF : Nat → Block} {s t₀ : State}
    (P : PassInv K W D R n SP m O0 l X (fun b o => b ^^^ o) ckF t₀ s i) (C : LCache l s) :
    WP isa (.block [.ldrq .v3 .x19 ofsO, .ldrq .v5 .x19 ckO]) s fun t =>
      ResidentInv K W D R n SP m O0 l X ckF t₀ t i ∧ LCache l t := by
  let u := s.setV .v3 (s.mem.read (W + BitVec.ofNat 64 ofsO) 16)
  let z := u.setV .v5 (u.mem.read (W + BitVec.ofNat 64 ckO) 16)
  obtain r₁ := loadV_run (s := s) .v3 (a := ofsO) (by decide) P.env.x19 (P.env.perm.wR (by decide))
  obtain r₂ := loadV_run (s := u) .v5 (a := ckO) (by decide) P.env.x19 (P.env.perm.wR (by decide))
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
  obtain f₁ : Frame [⟨W + BitVec.ofNat 64 ofsO, 16⟩] s.mem m₁ :=
    (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain f₂ : Frame [⟨W + BitVec.ofNat 64 ckO, 16⟩] m₁ m₂ :=
    (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain fr : Frame [⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 ckO, 16⟩] s.mem m₂ :=
    (f₁.mono (by simp)).trans (f₂.mono (by simp))
  obtain wO : InRegions s.wr (W + 16#64) 16 := P.env.perm.wW (d := ofsO) (by decide)
  obtain wC : InRegions s.wr (W + 32#64) 16 := P.env.perm.wW (d := ckO) (by decide)
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
    obtain B := hD.slice (a := 16 * k) (k := 16) (by omega_arith)
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
  · simp [gpr_write, P.x24, Proof.AesGcm.AArch64.lsr_ofNat _ _ (show m-i < 2^64 by omega_arith)]

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
  obtain ⟨tr, u, ex, Q⟩ := batchLastIncrement_ok (k := k) P.env C (by omega_arith)
    (by simpa only [show 8 * k + 7 + 1 = 8 * k + 8 by omega_arith] using P.x25)
  have vv (v : VReg) : u.v v = s.v v := Exec.vec (r := v)
    (fun i hi => of_decide_eq_true (List.all_eq_true.mp
      ((Code.allInstrs_eq _ batchLastIncrement) ▸ batchLast_noV v) i hi)) ex
  obtain P₁ := P.of_temp hD Q.frame Q.gpr Q.sp Q.rd Q.wr (vv .v3) (vv .v5)
  let u₂ := u.setV .v6 (u.mem.read (W + BitVec.ofNat 64 lO) 16)
  obtain run := loadV_run (s := u) .v6 (a := lO) (by decide) P₁.env.x19 (P₁.env.perm.wR (by decide))
  obtain P₂ : ResidentInv K W D R n SP m O0 l X ckF t₀ u₂ (8 * k + 7) :=
    P₁.of_temp hD (Frame.refl _ _) (fun _ _ => rfl) rfl rfl rfl
      (v_setV_of_ne _ _ (by decide)) (v_setV_of_ne _ _ (by decide))
  obtain C₂ : LCache l u₂ := by simpa only [u₂, LCache, v_setV, reduceCtorEq, ↓reduceIte, vv] using C
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
  refine WP.seq (WP.mono (residentStep_cached_ok mode hckF hD (by omega_arith) P C .v0
    (by rw [Proof.Ocb.ntz_odd (by omega_arith)]; exact C.1)) fun t₁ ⟨P₁, C₁⟩ => ?_)
  refine WP.seq (WP.mono (residentStep_cached_ok mode hckF hD (by omega_arith) P₁ C₁ .v1
    (by rw [show 8 * k + 1 + 1 = 8 * k + 2 by omega_arith, ntz_eight_two]; exact C₁.2.1)) fun t₂ ⟨P₂, C₂⟩ => ?_)
  refine WP.seq (WP.mono (residentStep_cached_ok mode hckF hD (by omega_arith) P₂ C₂ .v0
    (by rw [Proof.Ocb.ntz_odd (by omega_arith)]; exact C₂.1)) fun t₃ ⟨P₃, C₃⟩ => ?_)
  refine WP.seq (WP.mono (residentStep_cached_ok mode hckF hD (by omega_arith) P₃ C₃ .v2
    (by rw [show 8 * k + 1 + 1 + 1 + 1 = 8 * k + 4 by omega_arith, ntz_eight_four]; exact C₃.2.2)) fun t₄ ⟨P₄, C₄⟩ => ?_)
  refine WP.seq (WP.mono (residentStep_cached_ok mode hckF hD (by omega_arith) P₄ C₄ .v0
    (by rw [Proof.Ocb.ntz_odd (by omega_arith)]; exact C₄.1)) fun t₅ ⟨P₅, C₅⟩ => ?_)
  refine WP.seq (WP.mono (residentStep_cached_ok mode hckF hD (by omega_arith) P₅ C₅ .v1
    (by rw [show 8 * k + 1 + 1 + 1 + 1 + 1 + 1 = 8 * k + 6 by omega_arith, ntz_eight_six]; exact C₅.2.1)) fun t₆ ⟨P₆, C₆⟩ => ?_)
  refine WP.seq (WP.mono (residentStep_cached_ok mode hckF hD (by omega_arith) P₆ C₆ .v0
    (by rw [Proof.Ocb.ntz_odd (by omega_arith)]; exact C₆.1)) fun t₇ ⟨P₇, C₇⟩ => ?_)
  refine WP.mono (residentLast_ok (R := R) (n := n) (SP := SP) (k := k) mode hckF hD hm (by omega_arith)
    (by simpa only [show 8 * k + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 8 * k + 7 by omega_arith] using P₇) C₇) fun u ⟨P₈, C₈⟩ => ?_
  exact ⟨by simpa only [show 8 * k + 7 + 1 = 8 * (k + 1) by omega_arith] using P₈, C₈⟩
include hm in
 theorem passFast_ok (L : Lay K W) {body : List Instr}
    (hB : BodyOk W body (fun b o => b ^^^ o) (ckOp mode)) {t : State} (hm0 : 0 < m)
    (P : PassInv K W D R n SP m O0 l X (fun b o => b ^^^ o) ckF t₀ t 0) :
    WP isa (passFast mode body) t fun u => PassInv K W D R n SP m O0 l X (fun b o => b ^^^ o) ckF t₀ u m := by
  unfold passFast
  refine WP.seq (WP.mono (passCount_ok P hD hm) fun t₁ ⟨P₁, h9, _⟩ => ?_)
  refine WP.ite _ (eval_zero h9 (by omega_arith)) (fun hz => ?_) (fun hn => ?_)
  · exact passScalar_ok L hB hckF hD hm0 hm P₁
  · have hn : m / 8 ≠ 0 := of_decide_eq_false hn
    refine WP.seq (WP.mono (passCacheInit_ok P₁ hD) fun t₂ ⟨P₂, C₂⟩ => ?_)
    refine WP.seq (WP.mono (residentLoad_ok P₂ C₂) fun t₃ ⟨P₃, C₃⟩ => ?_)
    obtain loop : WP isa (.loop (.seq (residentBatch mode) (.block [.lsr .x .x9 .x24 3])) (.nonzero .x .x9)) t₃
        (fun u => ResidentInv K W D R n SP m O0 l X ckF t₀ u (8 * (m/8))) := by
      refine WP.loop (M := isa)
        (fun (j : Nat) (u : State) => ∃ k, j = m/8-k ∧ 8 * k + 8 ≤ m ∧
          ResidentInv K W D R n SP m O0 l X ckF t₀ u (8 * k) ∧ LCache l u) ?_
        (m/8) _ ⟨0, by omega_arith, by omega_arith, P₃, C₃⟩
      rintro j u ⟨k, rfl, hk, P, C⟩
      refine WP.seq (WP.mono (residentBatch_ok mode hckF hD hm hk P C) fun u₁ ⟨P', C'⟩ => ?_)
      refine WP.mono (residentCount_ok P' hD hm) fun u₂ ⟨P'', h9, hv⟩ => ?_
      obtain ev := eval_nonzero h9 (by omega_arith)
      by_cases he : (m-8 * (k + 1))/8 = 0
      · left
        exact ⟨ev.trans (by simp [he]), (show k + 1 = m/8 by omega_arith) ▸ P''⟩
      · right
        refine ⟨ev.trans (by simp [he]), m/8-(k + 1), by omega_arith, k + 1, rfl, by omega_arith, P'', ?_⟩
        simpa only [LCache, hv] using C'
    refine WP.seq (WP.mono loop fun u P' => ?_)
    refine WP.seq (WP.mono (residentStore_ok hD P') fun z Pz => ?_)
    refine WP.ite _ (eval_zero Pz.x24 (by omega_arith)) (fun hz => ?_) (fun hn => ?_)
    · have hz : m-8 * (m/8) = 0 := of_decide_eq_true hz
      exact WP.block_nil (by simpa only [show 8 * (m/8) = m by omega_arith] using Pz)
    · have hn : m-8 * (m/8) ≠ 0 := of_decide_eq_false hn
      exact passScalar_ok L hB hckF hD (by omega_arith) hm Pz

end

end VG.Proof.AesOcb.AArch64

end

end


/-!
# AES-OCB on AArch64: the whole blocks (`whole`)

Untrusted: everything here is checked by Lean. `whole f pre post` runs the
first pass (each block XORed with its offset, `pre`), `f` on all the blocks
(`ENCIPHER` or `DECIPHER`), and the second pass from `Offset_0` again
(`post`), each pass also updating the checksum (`whole_ok`): block `k`
becomes `Offset_{k+1} ⊕ g(X_k ⊕ Offset_{k+1})`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt blockAtMem_frame)
open VG.Proof.AesGcm.AArch64 (in_left in_off)

/-- What `whole` writes: the offset and the checksum, `L_{ntz(i)}`, the
working space of the functions called and the data. -/
abbrev wholeR (W D : Addr) (n : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 32⟩, ⟨W + BitVec.ofNat 64 96, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩, ⟨D, n⟩]

theorem wholeR_mut {W D : Addr} {n : Nat} {m m' : Mem} (h : Frame (wholeR W D n) m m') :
    Frame (mutR W D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact in_mutA (by decide)
  · exact in_mutA (by decide)
  · exact in_mutB (by decide) (by decide)
  · exact in_mutD fun _ h => h

/-- The first `k` bytes of a buffer, as a buffer at the same place. -/
theorem DBuf.take' {K W : Addr} {s : State} {D : Addr} {n k : Nat} (h : DBuf K W s D n) (hk : k ≤ n) :
    DBuf K W s D k := by
  have := h.slice (a := 0) (k := k) (by omega_using [hk])
  rwa [BitVec.add_zero] at this

/-- The `m` blocks of the data. -/
theorem dataArgs_ok {D : Addr} {t : State} (h21 : t.gpr .x21 = D) {m : Nat} (h26 : t.gpr .x26 = BitVec.ofNat 64 m) :
    ArgsOk [Impl.AesGcm.AArch64.mov .x2 .x21, Impl.AesGcm.AArch64.mov .x3 .x26] t D m := by
  refine ⟨_, by orun [], ?_, ?_, fun r h1 h2 => ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_write, h21]
  · simp [gpr_write, h26]
  · simp [gpr_write, h1, h2]
  all_goals rfl

/-- The start of a pass: `x23 ← D`, `x24 ← m`, `x25 ← 1`. -/
theorem passStart_ok {D : Addr} {t : State} (h21 : t.gpr .x21 = D) {m : Nat} (h26 : t.gpr .x26 = BitVec.ofNat 64 m) :
    ∃ t', runBlock isa [Impl.AesGcm.AArch64.mov .x23 .x21, Impl.AesGcm.AArch64.mov .x24 .x26,
        Impl.AesGcm.AArch64.imm .x25 1] t = some t' ∧
      t'.gpr .x23 = D + BitVec.ofNat 64 (16 * 0) ∧ t'.gpr .x24 = BitVec.ofNat 64 (m - 0) ∧
      t'.gpr .x25 = BitVec.ofNat 64 (0 + 1) ∧
      (∀ r, r ∉ [.x23, .x24, .x25] → t'.gpr r = t.gpr r) ∧ t'.mem = t.mem ∧ t'.sp = t.sp ∧ t'.rd = t.rd ∧
      t'.wr = t.wr := by
  refine ⟨_, by orun [], ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_write, h21]
  · simp [gpr_write, h26]
  · simp [gpr_write]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_write, hr.1, hr.2.1, hr.2.2]
  all_goals rfl

/-- What `whole` leaves. -/
structure WholePost (K W D : Addr) (R n : Nat) (SP : Addr) (m : Nat) (O0 l : Block) (Z : Nat → Block) (ck : Block)
    (t t' : State) : Prop where
  env : Env K W D R n SP t'
  frame : Frame (wholeR W D (16 * m)) t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  blk : ∀ k < m, blockAtMem t'.mem (D + BitVec.ofNat 64 (16 * k)) = Z k ^^^ offAt O0 l (k + 1)
  ofs : blockAtMem t'.mem (W + BitVec.ofNat 64 ofsO) = offAt O0 l m
  ck : blockAtMem t'.mem (W + BitVec.ofNat 64 ckO) = ck

theorem whole_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.AArch64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksAArch64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64 f).post s s')
    (nf : b.code.noFrames = true) {G : List Byte → Cipher}
    (hcall : ∀ {s s' : State} {K D S : Addr} {R n : Nat}, BPost f s K D S R n s' → ∀ i < n,
      blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) = G (bytesAt s.mem K (16 * (R + 1)))
        (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))))
    {pre post : List Instr} {pm qm : CkMode} {fC1 fC2 : Block → Block → Block → Block} {ckF1 ckF2 : Nat → Block}
    (hB1 : ∀ {W}, BodyOk W pre (fun b o => b ^^^ o) fC1) (hB2 : ∀ {W}, BodyOk W post (fun b o => b ^^^ o) fC2)
    (hM1 : fC1 = ckOp pm) (hM2 : fC2 = ckOp qm)
    {K W D : Addr} {R n : Nat} {SP : Addr} (L : Lay K W) {t : State} (E : Env K W D R n SP t)
    (hR : R = 10 ∨ R = 12 ∨ R = 14) {m : Nat} (hD : DBuf K W t D n) (hmn : 16 * m ≤ n) (hm0 : 0 < m)
    (hm : m < 2 ^ 60) {O0 l : Block} (h26 : t.gpr .x26 = BitVec.ofNat 64 m)
    (hofs : blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) = O0) (ho0 : blockAtMem t.mem (W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem t.mem (W + BitVec.ofNat 64 ckO) = ckF1 0)
    (hl0 : blockAtMem t.mem (W + BitVec.ofNat 64 l0O) = lAt l 0)
    (hckF1 : ∀ i, ckF1 (i + 1) = fC1 (ckF1 i) (blockAtMem t.mem (D + BitVec.ofNat 64 (16 * i))) (offAt O0 l (i + 1)))
    (hckF2₀ : ckF2 0 = ckF1 m)
    (hckF2 : ∀ i, ckF2 (i + 1) = fC2 (ckF2 i)
      (G (bytesAt t.mem K (16 * (R + 1))) (blockAtMem t.mem (D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1)))
      (offAt O0 l (i + 1))) :
    WP isa (whole b pre post pm qm) t (WholePost K W D R n SP m O0 l
      (fun k => G (bytesAt t.mem K (16 * (R + 1))) (blockAtMem t.mem (D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)))
      (ckF2 m) t) := by
  subst fC1 fC2
  obtain hDm := hD.take' hmn
  -- the first pass
  obtain ⟨s₁, run₁, x23₁, x24₁, x25₁, g₁, m₁, sp₁, rd₁, wr₁⟩ := passStart_ok E.x21 h26
  obtain E₁ := E.others g₁ sp₁ rd₁ wr₁
  obtain hD₁ : DBuf K W s₁ D (16 * m) := hDm.of_eq rd₁ wr₁
  obtain P₀ : PassInv K W D R n SP m O0 l (fun k => blockAtMem s₁.mem (D + BitVec.ofNat 64 (16 * k)))
      (fun b o => b ^^^ o) ckF1 s₁ s₁ 0 :=
    { env := E₁, frame := Frame.refl _ _, rd := rfl, wr := rfl, x23 := x23₁, x25 := x25₁, x24 := x24₁
      ofs := by rw [m₁, hofs]; rfl
      ck := by rw [m₁, hck]
      blk := fun k _ => by simp
      l0 := by rw [m₁, hl0]
      gpr := fun _ _ => rfl }
  unfold whole
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (passFast_ok pm (fun i _ => by rw [hckF1, m₁]) hD₁ hm L hB1 hm0 P₀) fun s₂ P₂ => ?_)
  have hw := hD.wrap
  obtain h26₂ : s₂.gpr .x26 = BitVec.ofNat 64 m := by rw [P₂.gpr _ (by decide), g₁ _ (by decide), h26]
  obtain hD₂ : DBuf K W s₂ D (16 * m) := hD₁.of_eq P₂.rd P₂.wr
  refine WP.seq (WP.mono (callBlocks_ok (f := f) (b := b) ok nf L P₂.env hR
    (dataArgs_ok P₂.env.x21 h26₂) (dstD hD₂)) fun s₃ P₃ => ?_)
  obtain E₃ := P₂.env.of_saved P₃.saved P₃.sp P₃.rd P₃.wr
  obtain kC : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨D, 16 * m⟩ →
      (⟨Q, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 512, 2048⟩ → blockAtMem s₃.mem Q = blockAtMem s₂.mem Q :=
    fun h₁ h₂ => blockAtMem_frame P₃.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h₁
      · exact h₂
  obtain kWP : ∀ {d : Nat}, (d + 16 ≤ 16 ∨ (48 ≤ d ∧ d + 16 ≤ 96) ∨ (112 ≤ d ∧ d + 16 ≤ 512)) →
      blockAtMem s₃.mem (W + BitVec.ofNat 64 d) = blockAtMem s₁.mem (W + BitVec.ofNat 64 d) := fun hd => by
    rw [kC ((hD₂.w.sub_right (Lay.wSub (by omega_using [hd]))).symm) (L.w_w (.inl (by omega_using [hd])) (by omega_using [hd]) (by decide)),
      blockAtMem_frame P₂.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.w_w (a := _) (d := 96) (k := 16) (by omega_using [hd]) (by omega_using [hd]) (by decide)
      · exact L.w_w (a := _) (d := 16) (k := 16) (by omega_using [hd]) (by omega_using [hd]) (by decide)
      · exact L.w_w (a := _) (d := 32) (k := 16) (by omega_using [hd]) (by omega_using [hd]) (by decide)
      · exact (hD₁.w.sub_right (Lay.wSub (by omega_using [hd]))).symm)]
  obtain o0₃ : blockAtMem s₃.mem (W + BitVec.ofNat 64 o0O) = O0 := by rw [kWP (by decide), m₁, ho0]
  -- `Offset_0` again
  obtain ⟨s₄a, run₄a, B₄⟩ := copy16_ok (s := s₃) (a := o0O) (d := ofsO) (by decide) (by decide) E₃.x19
    (E₃.perm.wR (by decide)) (E₃.perm.wR (by decide)) (E₃.perm.wW (by decide)) (E₃.perm.wW (by decide))
  obtain E₄a := E₃.others B₄.gpr B₄.sp B₄.rd B₄.wr
  obtain h26₄ : s₄a.gpr .x26 = BitVec.ofNat 64 m := by
    rw [B₄.gpr _ (by decide), P₃.saved _ (by decide) (by decide), h26₂]
  obtain ⟨s₄, run₄, x23₄, x24₄, x25₄, g₄, m₄, sp₄, rd₄, wr₄⟩ := passStart_ok E₄a.x21 h26₄
  obtain E₄ := E₄a.others g₄ sp₄ rd₄ wr₄
  obtain hD₄ : DBuf K W s₄ D (16 * m) := hD₂.of_eq (by rw [rd₄, B₄.rd, P₃.rd]) (by rw [wr₄, B₄.wr, P₃.wr])
  obtain kB₄ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨W, 2560⟩ → blockAtMem s₄.mem Q = blockAtMem s₃.mem Q :=
    fun hQ => by
      rw [m₄]; exact blockAtMem_frame B₄.frame fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hQ.sub_right (Lay.wSub (by decide))
  obtain hK : bytesAt s₂.mem K (16 * (R + 1)) = bytesAt t.mem K (16 * (R + 1)) := by
    obtain hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
    rw [Proof.Cmac.bytesAt_frame P₂.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))
      · exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))
      · exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))
      · exact hD₁.k.sub_left (Region.sub_prefix hRb)) (by omega_using [hR]), m₁]
  obtain X₄ : ∀ k < m, blockAtMem s₄.mem (D + BitVec.ofNat 64 (16 * k)) =
      G (bytesAt t.mem K (16 * (R + 1))) (blockAtMem t.mem (D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)) :=
    fun k hk => by
      rw [kB₄ (hD₂.slice (a := 16 * k) (k := 16) (by omega_using [hk])).w, hcall P₃ k hk, hK, P₂.blk k hk]
      simp only [hk, ↓reduceIte, m₁]
  obtain ck₃ : blockAtMem s₃.mem (W + BitVec.ofNat 64 ckO) = ckF2 0 := by
    rw [kC ((hD₂.w.sub_right (Lay.wSub (by decide))).symm) (L.w_w (.inl (by decide)) (by decide) (by decide)),
      P₂.ck, hckF2₀]
  obtain P₀' : PassInv K W D R n SP m O0 l (fun k => blockAtMem s₄.mem (D + BitVec.ofNat 64 (16 * k)))
      (fun b o => b ^^^ o) ckF2 s₄ s₄ 0 :=
    { env := E₄, frame := Frame.refl _ _, rd := rfl, wr := rfl, x23 := x23₄, x25 := x25₄, x24 := x24₄
      ofs := by rw [m₄, B₄.val, o0₃]; rfl
      ck := by
        rw [m₄, blockAtMem_frame B₄.frame (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)), ck₃]
      blk := fun k _ => by simp
      l0 := by
        rw [m₄, blockAtMem_frame B₄.frame (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)),
          kWP (by decide), m₁, hl0]
      gpr := fun _ _ => rfl }
  refine WP.seq (WP.of_runBlock ⟨s₄, by rw [runBlock_append, run₄a, Option.bind_some, run₄], ?_⟩)
  refine WP.mono (passFast_ok qm (fun i hi => by rw [hckF2, X₄ i hi]) hD₄ hm L hB2 hm0 P₀') fun s₅ P₅ => ?_
  obtain subW : ∀ r ∈ [(⟨W + BitVec.ofNat 64 lO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 ofsO, 16⟩,
      ⟨W + BitVec.ofNat 64 ckO, 16⟩, ⟨D, 16 * m⟩], ∃ r' ∈ wholeR W D (16 * m), Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub W (d := 16) (n := 16) (e := 16) (k := 32) (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub W (d := 32) (n := 16) (e := 16) (k := 32) (by decide) (by decide)⟩
    · exact ⟨⟨D, 16 * m⟩, by simp, fun _ h => h⟩
  refine ⟨P₅.env, ?_, by rw [P₅.rd, rd₄, B₄.rd, P₃.rd, P₂.rd, rd₁], by rw [P₅.wr, wr₄, B₄.wr, P₃.wr, P₂.wr, wr₁],
    fun k hk => ?_, P₅.ofs, P₅.ck⟩
  · rw [← m₁]
    refine (P₂.frame.sub subW).trans ((P₃.frame.sub fun r hr => ?_).trans ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨D, 16 * m⟩, by simp, fun _ h => h⟩
      · exact ⟨_, by simp, fun _ h => h⟩
    · have F₅ := P₅.frame
      rw [m₄] at F₅
      exact (B₄.frame.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self .., Offset.sub W (d := 16) (n := 16) (e := 16) (k := 32) (by decide) (by decide)⟩).trans
        (F₅.sub subW)
  · rw [P₅.blk k hk]
    simp only [hk, ↓reduceIte]
    rw [X₄ k hk]

end VG.Proof.AesOcb.AArch64

end

end


/-!
# AES-OCB on AArch64: the data (`body`)

Untrusted: everything here is checked by Lean. `body` takes the whole blocks
(if any, `wholeIte_ok`) and then the rest (if any, `restIte_ok`); for `seal`
the result is `OCB-ENCRYPT`'s ciphertext, offset and checksum
(`bodySeal_ok`), for `open` `OCB-DECRYPT`'s (`bodyOpen_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ctxCiph ctxLstar pad)
open VG.Proof.Ocb (offAt length_bytesAt blockAtMem_frame)
open VG.Proof.Aes.AArch64 (BlocksImpl)
open VG.Proof.AesGcm.AArch64 (eval_zero toNat_ofNat_of_lt lsr_ofNat and15)

/-- The whole blocks, if there are any. -/
theorem wholeIte_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.AArch64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksAArch64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64 f).post s s')
    (nf : b.code.noFrames = true) {G : List Byte → Cipher}
    (hcall : ∀ {s s' : State} {K D S : Addr} {R n : Nat}, BPost f s K D S R n s' → ∀ i < n,
      blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) = G (bytesAt s.mem K (16 * (R + 1)))
        (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))))
    {pre post : List Instr} {pm qm : CkMode} {fC1 fC2 : Block → Block → Block → Block} {ckF1 ckF2 : Nat → Block}
    (hB1 : ∀ {W}, BodyOk W pre (fun b o => b ^^^ o) fC1) (hB2 : ∀ {W}, BodyOk W post (fun b o => b ^^^ o) fC2)
    (hM1 : fC1 = ckOp pm) (hM2 : fC2 = ckOp qm)
    {K W D : Addr} {R n : Nat} {SP : Addr} (L : Lay K W) {s : State} (E : Env K W D R n SP s)
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hD : DBuf K W s D n) {O0 l : Block}
    (hofs : blockAtMem s.mem (W + BitVec.ofNat 64 ofsO) = O0) (ho0 : blockAtMem s.mem (W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (W + BitVec.ofNat 64 ckO) = ckF1 0)
    (hl0 : blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt l 0)
    (hckF1 : ∀ i, ckF1 (i + 1) = fC1 (ckF1 i) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) (offAt O0 l (i + 1)))
    (hckF2₀ : ckF2 0 = ckF1 (n / 16))
    (hckF2 : ∀ i, ckF2 (i + 1) = fC2 (ckF2 i)
      (G (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1)))
      (offAt O0 l (i + 1))) :
    WP isa (.seq (.block [.lsr .x .x26 .x28 4]) (.ite (.zero .x .x26) (.block []) (whole b pre post pm qm))) s
      (WholePost K W D R n SP (n / 16) O0 l
        (fun k => G (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)))
        (ckF2 (n / 16)) s) := by
  have hn := hD.lt
  obtain ⟨s₁, run₁, h₁⟩ : ∃ s₁, runBlock isa [.lsr .x .x26 .x28 4] s = some s₁ ∧
      s₁ = s.write .x .x26 (s.gpr .x28 >>> 4) := ⟨_, by orun [], rfl⟩
  subst h₁
  obtain x26₁ : (s.write .x .x26 (s.gpr .x28 >>> 4)).gpr .x26 = BitVec.ofNat 64 (n / 16) := by
    simp [gpr_write, E.x28, lsr_ofNat _ _ hn]
  obtain E₁ : Env K W D R n SP (s.write .x .x26 (s.gpr .x28 >>> 4)) :=
    E.others (rs := [.x26]) (fun r hr => by simp at hr; simp [gpr_write, hr]) rfl rfl rfl
  refine WP.seq (WP.of_runBlock ⟨_, run₁, ?_⟩)
  refine WP.ite _ (eval_zero x26₁ (by omega_arith)) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have hm : n / 16 = 0 := of_decide_eq_true h0
    exact ⟨E₁, Frame.refl _ _, rfl, rfl, fun k hk => absurd hk (by omega_arith),
      by rw [mem_write, hofs, hm]; rfl, by rw [mem_write, hck, hm, hckF2₀, hm]⟩
  · have hm : n / 16 ≠ 0 := of_decide_eq_false h0
    refine WP.mono (whole_ok (O0 := O0) (l := l) ok nf hcall hB1 hB2 hM1 hM2 L E₁ hR (hD.of_eq rfl rfl)
      (Nat.mul_div_le n 16) (by omega_arith) (by omega_arith) x26₁ hofs ho0 hck hl0 hckF1 hckF2₀ hckF2) fun t P => ?_
    exact ⟨P.env, P.frame, P.rd, P.wr, P.blk, P.ofs, P.ck⟩

/-- Where the rest of the data is, and how long it is. -/
theorem bodyTail_ok {K W D : Addr} {R n : Nat} {SP : Addr} {t : State} (E : Env K W D R n SP t) (hn : n < 2 ^ 64) :
    ∃ t₁, runBlock isa [Impl.AesGcm.AArch64.imm .x10 15, .logic .and .x .x24 .x28 .x10, .sub .x .x9 .x28 .x24,
        .add .x .x23 .x21 .x9] t = some t₁ ∧
      t₁.gpr .x23 = D + BitVec.ofNat 64 (16 * (n / 16)) ∧ t₁.gpr .x24 = BitVec.ofNat 64 (n % 16) ∧
      t₁.mem = t.mem ∧ (∀ r, r ∉ [.x9, .x10, .x23, .x24] → t₁.gpr r = t.gpr r) ∧ t₁.sp = t.sp ∧ t₁.rd = t.rd ∧
      t₁.wr = t.wr := by
  obtain hsub : BitVec.ofNat 64 n - BitVec.ofNat 64 (n % 16) = BitVec.ofNat 64 (16 * (n / 16)) := by
    rw [Proof.AesGcm.AArch64.ofNat_sub (Nat.mod_le _ _) hn, show n - n % 16 = 16 * (n / 16) by omega_arith]
  refine ⟨_, by orun [], ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · simp [gpr_write, E.x28, E.x21, and15, toNat_ofNat_of_lt hn, hsub]
  · simp [gpr_write, E.x28, and15, toNat_ofNat_of_lt hn]
  · rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]
  all_goals rfl

/-- What the rest of the data leaves, if there is any: `r` bytes at `P`. -/
structure TailPost (enc : Bool) (K W D : Addr) (R n : Nat) (SP : Addr) (P : Addr) (r : Nat) (t t' : State) : Prop where
  env : Env K W D R n SP t'
  frame : Frame [⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩,
    ⟨W + BitVec.ofNat 64 ckO, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩, ⟨P, r⟩] t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  ofs : blockAtMem t'.mem (W + BitVec.ofNat 64 ofsO) =
    if 0 < r then blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem K
    else blockAtMem t.mem (W + BitVec.ofNat 64 ofsO)
  out : bytesAt t'.mem P r =
    if 0 < r then Spec.Ocb.xor (bytesAt t.mem P r)
      (Spec.Ocb.toBytes (ctxCiph t.mem K R (blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) ^^^ ctxLstar t.mem K)))
    else bytesAt t.mem P r
  ck : blockAtMem t'.mem (W + BitVec.ofNat 64 ckO) =
    if 0 < r then blockAtMem t.mem (W + BitVec.ofNat 64 ckO) ^^^ pad (bytesAt (if enc then t.mem else t'.mem) P r)
    else blockAtMem t.mem (W + BitVec.ofNat 64 ckO)

/-- The rest of the data, if there is any. -/
theorem restIte_ok (v : BlocksImpl) (enc : Bool) {K W D : Addr} {R n : Nat} {SP : Addr} (L : Lay K W) {t : State}
    (E : Env K W D R n SP t) (hR : R = 10 ∨ R = 12 ∨ R = 14) (hD : DBuf K W t D n) :
    WP isa (.seq (.block [Impl.AesGcm.AArch64.imm .x10 15, .logic .and .x .x24 .x28 .x10, .sub .x .x9 .x28 .x24,
        .add .x .x23 .x21 .x9]) (.ite (.zero .x .x24) (.block []) (rest (callees v) enc))) t
      (TailPost enc K W D R n SP (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) t) := by
  have hn := hD.lt
  obtain ⟨t₁, run₁, x23₁, x24₁, m₁, g₁, sp₁, rd₁, wr₁⟩ := bodyTail_ok E hn
  obtain E₁ := E.others g₁ sp₁ rd₁ wr₁
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite _ (eval_zero x24₁ (by omega_arith)) (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have hr : ¬ 0 < n % 16 := by have := of_decide_eq_true h0; omega_arith
    refine ⟨E₁, by rw [m₁]; exact Frame.refl _ _, rd₁, wr₁, ?_, ?_, ?_⟩ <;> simp only [hr, ↓reduceIte, m₁]
  · have hr : 0 < n % 16 := by have := of_decide_eq_false h0; omega_arith
    obtain hP : DBuf K W t₁ (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
      (hD.slice (a := 16 * (n / 16)) (k := n % 16) (by omega_arith)).of_eq rd₁ wr₁
    refine WP.mono (rest_ok v enc L E₁ hR hr (Nat.mod_lt _ (by decide)) x23₁ x24₁ hP) fun t' P => ?_
    refine ⟨P.env, by rw [← m₁]; exact P.frame, by rw [P.rd, rd₁], by rw [P.wr, wr₁], ?_, ?_, ?_⟩ <;>
      simp only [hr, ↓reduceIte]
    · rw [P.ofs, m₁]
    · rw [P.out, m₁]
    · rw [P.ck, m₁]

/-- What `body` writes: the offset and the checksum, `L_{ntz(i)}`, `Pad` and
`pad(·)`, the working space of the functions called, the stack and the data. -/
abbrev bodyR (W D : Addr) (n : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 32⟩, ⟨W + BitVec.ofNat 64 96, 48⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩, ⟨D, n⟩]

theorem bodyR_mut {W D : Addr} {n : Nat} {m m' : Mem} (h : Frame (bodyR W D n) m m') :
    Frame (mutR W D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact in_mutA (by decide)
  · exact in_mutA (by decide)
  · exact in_mutB (by decide) (by decide)
  · exact in_mutD fun _ h => h

/-- What `body` leaves: the data, the offset and the checksum. -/
structure BodyPost (K W D : Addr) (R n : Nat) (SP : Addr) (out : List Byte) (ofs ck : Block) (s t : State) : Prop where
  env : Env K W D R n SP t
  frame : Frame (bodyR W D n) s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  out : bytesAt t.mem D n = out
  ofs : blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) = ofs
  ck : blockAtMem t.mem (W + BitVec.ofNat 64 ckO) = ck

/-- A checksum of blocks `X i`. -/
def ckOf (X : Nat → Block) : Nat → Block
  | 0 => 0
  | i + 1 => ckOf X i ^^^ X i

theorem ckOf_eq {X : Nat → Block} {p : List Byte} {m : Nat} (h : ∀ i < m, X i = Spec.Ocb.blockAt p i) :
    ckOf X m = Proof.Ocb.ckAt p m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [ckOf, Proof.Ocb.ckAt, ih (fun i hi => h i (by omega_arith)), h m (by omega_arith)]

theorem flatMap_range_congr {α : Type} {f g : Nat → List α} {m : Nat} (h : ∀ i < m, f i = g i) :
    (List.range m).flatMap f = (List.range m).flatMap g := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, ih (fun i hi => h i (by omega_arith))]
    simp only [List.flatMap_cons, List.flatMap_nil, h m (by omega_arith)]

/-- `ENCIPHER` from the key schedule, whatever its length. -/
def encG (ks : List Byte) : Cipher := Spec.Ocb.aesWith (ks.length / 16 - 1) ks

/-- `DECIPHER` from the key schedule, whatever its length. -/
def decG (ks : List Byte) : Cipher := Spec.Ocb.aesInvWith (ks.length / 16 - 1) ks

theorem encG_eq (m : Mem) (K : Addr) (R : Nat) : encG (bytesAt m K (16 * (R + 1))) = ctxCiph m K R := by
  rw [encG, length_bytesAt, show 16 * (R + 1) / 16 - 1 = R by omega_arith]; rfl

theorem decG_eq (m : Mem) (K : Addr) (R : Nat) : decG (bytesAt m K (16 * (R + 1))) = Spec.Ocb.ctxInv m K R := by
  rw [decG, length_bytesAt, show 16 * (R + 1) / 16 - 1 = R by omega_arith]; rfl

theorem hcall_enc {s s' : State} {K D S : Addr} {R n : Nat} (h : BPost Spec.Aes.cipher s K D S R n s') :
    ∀ i < n, blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) =
      encG (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) := fun i hi => by
  rw [h.enc hi, encG_eq]; rfl

theorem hcall_dec {s s' : State} {K D S : Addr} {R n : Nat} (h : BPost Spec.Aes.invCipher s K D S R n s') :
    ∀ i < n, blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) =
      decG (bytesAt s.mem K (16 * (R + 1))) (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) := fun i hi => by
  rw [h.dec hi, decG_eq]; rfl

/-- A buffer apart from `W` and `⟨P, r⟩` misses what `rest` writes. -/
theorem disj_tail {W Q P : Addr} {k r : Nat} (hw : (⟨Q, k⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hp : (⟨Q, k⟩ : Region).Disjoint ⟨P, r⟩) :
    ∀ x ∈ [(⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩,
      ⟨W + BitVec.ofNat 64 ckO, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩, ⟨P, r⟩], (⟨Q, k⟩ : Region).Disjoint x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hp

/-- A buffer apart from `W` and `⟨D, n⟩` misses what `whole` writes. -/
theorem disj_whole {W Q D : Addr} {k n : Nat} (hw : (⟨Q, k⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hp : (⟨Q, k⟩ : Region).Disjoint ⟨D, n⟩) :
    ∀ x ∈ wholeR W D n, (⟨Q, k⟩ : Region).Disjoint x := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hw.sub_right (Lay.wSub (by decide))
  · exact hp

theorem wholeR_sub {W D : Addr} {k n : Nat} (hk : k ≤ n) :
    ∀ r ∈ wholeR W D k, ∃ r' ∈ bodyR W D n, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, Region.sub_prefix hk⟩

theorem tailR_sub {W D : Addr} {n a r : Nat} (h : a + r ≤ n) :
    ∀ x ∈ [(⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩,
      ⟨W + BitVec.ofNat 64 ckO, 16⟩, ⟨W + BitVec.ofNat 64 512, 2048⟩, ⟨D + BitVec.ofNat 64 a, r⟩],
      ∃ r' ∈ bodyR W D n, Region.Sub x r' := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, Offset.sub_base D h⟩

/-- `body` for `seal`. -/
theorem bodySeal_ok (v : BlocksImpl) {K W D : Addr} {R n : Nat} {SP : Addr} (L : Lay K W) {s : State}
    (E : Env K W D R n SP s) (hR : R = 10 ∨ R = 12 ∨ R = 14) (hD : DBuf K W s D n) {O0 : Block}
    (hofs : blockAtMem s.mem (W + BitVec.ofNat 64 ofsO) = O0) (ho0 : blockAtMem s.mem (W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (W + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem K) 0) :
    WP isa (body (callees v) true) s (BodyPost K W D R n SP
      (if 0 < n % 16 then
        Proof.Ocb.encBlocks (ctxCiph s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) ++
          Spec.Ocb.xor ((bytesAt s.mem D n).drop (16 * (n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem K R (offAt O0 (ctxLstar s.mem K) (n / 16) ^^^ ctxLstar s.mem K)))
      else Proof.Ocb.encBlocks (ctxCiph s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16))
      (if 0 < n % 16 then offAt O0 (ctxLstar s.mem K) (n / 16) ^^^ ctxLstar s.mem K
       else offAt O0 (ctxLstar s.mem K) (n / 16))
      (if 0 < n % 16 then
        Proof.Ocb.ckAt (bytesAt s.mem D n) (n / 16) ^^^ pad ((bytesAt s.mem D n).drop (16 * (n / 16)))
      else Proof.Ocb.ckAt (bytesAt s.mem D n) (n / 16)) s) := by
  have hn := hD.lt
  obtain hmn : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  obtain hDm : DBuf K W s D (16 * (n / 16)) := hD.take' hmn
  obtain hP : DBuf K W s (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    hD.slice (a := 16 * (n / 16)) (k := n % 16) (by omega_arith)
  obtain dDP : (⟨D, 16 * (n / 16)⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩ :=
    Offset.base_disjoint D (Nat.le_refl _) (by omega_arith)
  obtain hl : ∀ i < n / 16, blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) = Spec.Ocb.blockAt (bytesAt s.mem D n) i :=
    fun i hi => (Proof.Ocb.blockAt_bytesAt s.mem D (by omega_arith)).symm
  simp only [body, ↓reduceIte]
  refine WP.assoc (WP.seq (WP.mono (wholeIte_ok (O0 := O0) (l := ctxLstar s.mem K)
    (ckF1 := ckOf fun i => blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)))
    (ckF2 := fun _ => ckOf (fun i => blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))) (n / 16))
    v.encOk v.encNoFrames hcall_enc sealPre_ok xorOfs_ok rfl rfl L E hR hD hofs ho0 hck hl0
    (fun _ => rfl) rfl (fun _ => rfl)) fun t Pw => ?_))
  obtain fW : Frame (mutR W D (16 * (n / 16))) s.mem t.mem := wholeR_mut Pw.frame
  refine WP.mono (restIte_ok v true L Pw.env hR (hD.of_eq Pw.rd Pw.wr)) fun t' Pt => ?_
  obtain cT : ctxCiph t.mem K R = ctxCiph s.mem K R := ctxCiph_mut L hDm.k fW hR
  obtain lT : ctxLstar t.mem K = ctxLstar s.mem K :=
    blockAtMem_frame fW fun r hr => (k_mut L hDm.k r hr).sub_left (Lay.kSub (by decide))
  obtain pT : bytesAt t.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
      bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    Proof.Cmac.bytesAt_frame Pw.frame (disj_whole hP.w dDP.symm) (by omega_arith)
  obtain rest : (bytesAt s.mem D n).drop (16 * (n / 16)) = bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
    rw [Proof.Ocb.bytesAt_drop s.mem D hmn, show n - 16 * (n / 16) = n % 16 by omega_arith]
  obtain ckT : blockAtMem t.mem (W + BitVec.ofNat 64 ckO) = Proof.Ocb.ckAt (bytesAt s.mem D n) (n / 16) := by
    rw [Pw.ck, ckOf_eq hl]
  obtain blk : bytesAt t'.mem D (16 * (n / 16)) =
      Proof.Ocb.encBlocks (ctxCiph s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) := by
    rw [Proof.Cmac.bytesAt_frame Pt.frame (disj_tail hDm.w dDP) (by omega_arith), Proof.Ocb.bytesAt_blocks, Proof.Ocb.encBlocks]
    refine flatMap_range_congr fun i hi => ?_
    rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ 16), ← blockAtMem, Pw.blk i hi, encG_eq, hl i hi,
      BitVec.xor_comm]
  refine ⟨Pt.env, (Pw.frame.sub (wholeR_sub hmn)).trans (Pt.frame.sub (tailR_sub (by omega_arith))),
    by rw [Pt.rd, Pw.rd], by rw [Pt.wr, Pw.wr], ?_, ?_, ?_⟩
  · have e := Proof.Ocb.bytesAt_append t'.mem D (16 * (n / 16)) (n % 16)
    rw [show 16 * (n / 16) + n % 16 = n by omega_arith] at e
    rw [e, blk, Pt.out]
    by_cases hr : 0 < n % 16
    · simp only [hr, ↓reduceIte, pT, cT, lT, Pw.ofs, rest]
    · have b0 : ∀ (m : Mem) (p : Addr), bytesAt m p 0 = [] := fun _ _ => rfl
      simp only [hr, ↓reduceIte, show n % 16 = 0 by omega_arith, b0, List.append_nil, Nat.lt_irrefl]
  · rw [Pt.ofs, Pw.ofs, lT]
  · rw [Pt.ck, ckT]
    simp only [↓reduceIte, pT, rest]

theorem ckOf_dck {X : Nat → Block} {inv : Cipher} {o0 l : Block} {c : List Byte} {m : Nat}
    (h : ∀ i < m, X i = Proof.Ocb.decBlock inv o0 l c i) : ckOf X m = Proof.Ocb.dckAt inv o0 l c m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [ckOf, Proof.Ocb.dckAt, ih (fun i hi => h i (by omega_arith)), h m (by omega_arith)]

/-- `body` for `open`. -/
theorem bodyOpen_ok (v : BlocksImpl) {K W D : Addr} {R n : Nat} {SP : Addr} (L : Lay K W) {s : State}
    (E : Env K W D R n SP s) (hR : R = 10 ∨ R = 12 ∨ R = 14) (hD : DBuf K W s D n) {O0 : Block}
    (hofs : blockAtMem s.mem (W + BitVec.ofNat 64 ofsO) = O0) (ho0 : blockAtMem s.mem (W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem s.mem (W + BitVec.ofNat 64 ckO) = 0)
    (hl0 : blockAtMem s.mem (W + BitVec.ofNat 64 l0O) = lAt (ctxLstar s.mem K) 0) :
    WP isa (body (callees v) false) s (BodyPost K W D R n SP
      (if 0 < n % 16 then
        Proof.Ocb.decBlocks (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) ++
          Spec.Ocb.xor ((bytesAt s.mem D n).drop (16 * (n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem K R (offAt O0 (ctxLstar s.mem K) (n / 16) ^^^ ctxLstar s.mem K)))
      else Proof.Ocb.decBlocks (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16))
      (if 0 < n % 16 then offAt O0 (ctxLstar s.mem K) (n / 16) ^^^ ctxLstar s.mem K
       else offAt O0 (ctxLstar s.mem K) (n / 16))
      (if 0 < n % 16 then
        Proof.Ocb.dckAt (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) ^^^
          pad (Spec.Ocb.xor ((bytesAt s.mem D n).drop (16 * (n / 16)))
            (Spec.Ocb.toBytes (ctxCiph s.mem K R (offAt O0 (ctxLstar s.mem K) (n / 16) ^^^ ctxLstar s.mem K))))
      else Proof.Ocb.dckAt (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16)) s) := by
  have hn := hD.lt
  obtain hmn : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  obtain hDm : DBuf K W s D (16 * (n / 16)) := hD.take' hmn
  obtain hP : DBuf K W s (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    hD.slice (a := 16 * (n / 16)) (k := n % 16) (by omega_arith)
  obtain dDP : (⟨D, 16 * (n / 16)⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * (n / 16)), n % 16⟩ :=
    Offset.base_disjoint D (Nat.le_refl _) (by omega_arith)
  obtain hl : ∀ i < n / 16, blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) = Spec.Ocb.blockAt (bytesAt s.mem D n) i :=
    fun i hi => (Proof.Ocb.blockAt_bytesAt s.mem D (by omega_arith)).symm
  simp only [body, Bool.false_eq_true, ↓reduceIte]
  refine WP.assoc (WP.seq (WP.mono (wholeIte_ok (O0 := O0) (l := ctxLstar s.mem K) (ckF1 := fun _ => 0)
    (ckF2 := ckOf fun i => decG (bytesAt s.mem K (16 * (R + 1)))
      (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 (ctxLstar s.mem K) (i + 1)) ^^^
        offAt O0 (ctxLstar s.mem K) (i + 1))
    v.decOk v.decNoFrames hcall_dec xorOfs_ok openPost_ok rfl rfl L E hR hD hofs ho0 hck hl0
    (fun _ => rfl) rfl (fun _ => rfl)) fun t Pw => ?_))
  obtain fW : Frame (mutR W D (16 * (n / 16))) s.mem t.mem := wholeR_mut Pw.frame
  refine WP.mono (restIte_ok v false L Pw.env hR (hD.of_eq Pw.rd Pw.wr)) fun t' Pt => ?_
  obtain cT : ctxCiph t.mem K R = ctxCiph s.mem K R := ctxCiph_mut L hDm.k fW hR
  obtain lT : ctxLstar t.mem K = ctxLstar s.mem K :=
    blockAtMem_frame fW fun r hr => (k_mut L hDm.k r hr).sub_left (Lay.kSub (by decide))
  obtain pT : bytesAt t.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
      bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    Proof.Cmac.bytesAt_frame Pw.frame (disj_whole hP.w dDP.symm) (by omega_arith)
  obtain rest : (bytesAt s.mem D n).drop (16 * (n / 16)) = bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := by
    rw [Proof.Ocb.bytesAt_drop s.mem D hmn, show n - 16 * (n / 16) = n % 16 by omega_arith]
  obtain ckT : blockAtMem t.mem (W + BitVec.ofNat 64 ckO) =
      Proof.Ocb.dckAt (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) := by
    rw [Pw.ck, ckOf_dck fun i hi => by rw [decG_eq, hl i hi, Proof.Ocb.decBlock, BitVec.xor_comm]]
  obtain blk : bytesAt t'.mem D (16 * (n / 16)) =
      Proof.Ocb.decBlocks (Spec.Ocb.ctxInv s.mem K R) O0 (ctxLstar s.mem K) (bytesAt s.mem D n) (n / 16) := by
    rw [Proof.Cmac.bytesAt_frame Pt.frame (disj_tail hDm.w dDP) (by omega_arith), Proof.Ocb.bytesAt_blocks, Proof.Ocb.decBlocks]
    refine flatMap_range_congr fun i hi => ?_
    rw [← Proof.Ocb.toBytes_ofBytes (length_bytesAt _ _ 16), ← blockAtMem, Pw.blk i hi, decG_eq, hl i hi,
      Proof.Ocb.decBlock, BitVec.xor_comm]
  obtain e := Proof.Ocb.bytesAt_append t'.mem D (16 * (n / 16)) (n % 16)
  rw [show 16 * (n / 16) + n % 16 = n by omega_arith] at e
  refine ⟨Pt.env, (Pw.frame.sub (wholeR_sub hmn)).trans (Pt.frame.sub (tailR_sub (by omega_arith))),
    by rw [Pt.rd, Pw.rd], by rw [Pt.wr, Pw.wr], ?_, ?_, ?_⟩
  · rw [e, blk, Pt.out]
    by_cases hr : 0 < n % 16
    · simp only [hr, ↓reduceIte, pT, cT, lT, Pw.ofs, rest]
    · have b0 : ∀ (m : Mem) (p : Addr), bytesAt m p 0 = [] := fun _ _ => rfl
      simp only [hr, ↓reduceIte, show n % 16 = 0 by omega_arith, b0, List.append_nil, Nat.lt_irrefl]
  · rw [Pt.ofs, Pw.ofs, lT]
  · rw [Pt.ck, ckT]
    by_cases hr : 0 < n % 16
    · simp only [hr, Bool.false_eq_true, ↓reduceIte, Pt.out, pT, cT, lT, Pw.ofs, rest]
    · simp only [hr, ↓reduceIte]

end VG.Proof.AesOcb.AArch64

import VerifiedGarbage.Proof.AesOcb.AArch64.Pass
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved

/-! Cached increments for batches of eight payload blocks. -/
set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesOcb.AArch64
open VG.Spec.Ocb (Block blockAtMem lAt ntz)
open VG.Proof.Ocb (blockAtMem_frame offAt)

/-- Interpret a loaded vector as OCB's big-endian block. -/
def vBlock (x : BitVec 128) : Block :=
  Spec.Ocb.ofBytes ((List.range 16).map fun j => x.extractLsb' (8 * j) 8)

theorem vBlock_read (m : Mem) (p : Addr) : vBlock (m.read p 16) = blockAtMem m p := by
  unfold vBlock blockAtMem
  congr 1
  apply List.map_congr_left
  intro j hj
  exact Mem.extractLsb'_read _ _ (List.mem_range.mp hj)

/-- The three increments needed for the first seven blocks of each batch. -/
def LCache (l : Block) (s : State) : Prop :=
  vBlock (s.v .v0) = lAt l 0 ∧ vBlock (s.v .v1) = lAt l 1 ∧ vBlock (s.v .v2) = lAt l 2

def keepsCache (i : Instr) : Bool :=
  decide (vdstOf i ≠ some .v0 ∧ vdstOf i ≠ some .v1 ∧ vdstOf i ≠ some .v2)

theorem keepCache {p : Prog isa} {s : State} {Q : State → Prop} {l : Block}
    (h : WP isa p s Q) (hc : p.allInstrs keepsCache = true) (C : LCache l s) :
    WP isa p s fun t => Q t ∧ LCache l t := by
  obtain ⟨tr, t, ex, hq⟩ := h
  have hs := List.all_eq_true.mp ((Code.allInstrs_eq keepsCache p) ▸ hc)
  have h0 := Exec.vec (r := .v0) (fun i hi => (of_decide_eq_true (hs i hi)).1) ex
  have h1 := Exec.vec (r := .v1) (fun i hi => (of_decide_eq_true (hs i hi)).2.1) ex
  have h2 := Exec.vec (r := .v2) (fun i hi => (of_decide_eq_true (hs i hi)).2.2) ex
  exact ⟨tr, t, ex, hq, by simpa only [LCache, h0, h1, h2] using C⟩

theorem vBlock_words (x : BitVec 128) :
    Spec.Ocb.ofBytes (Proof.Cmac.le8 (x.extractLsb' 0 64) ++ Proof.Cmac.le8 (x.extractLsb' 64 64)) = vBlock x := by
  unfold vBlock
  congr 1
  apply List.ext_getElem
  · simp [Proof.Cmac.le8]
  · intro j h₁ h₂
    have hj : j < 16 := by simpa using h₂
    by_cases h : j < 8
    · rw [List.getElem_append_left (by simpa [Proof.Cmac.le8] using h)]
      simp only [Proof.Cmac.le8, List.getElem_map, List.getElem_range]
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      simp only [BitVec.getLsbD_extractLsb', show k < 8 by omega, decide_true, Bool.true_and,
        show 8*j+k < 64 by omega, Nat.zero_add]
    · rw [List.getElem_append_right (by simpa [Proof.Cmac.le8] using Nat.le_of_not_gt h)]
      simp only [Proof.Cmac.le8, List.length_map, List.length_range, List.getElem_map, List.getElem_range]
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      simp only [BitVec.getLsbD_extractLsb', show k < 8 by omega, decide_true, Bool.true_and,
        show 8*(j-8)+k < 64 by omega, show 64+(8*(j-8)+k) = 8*j+k by omega]

theorem cachedIncrement_ok {K W D : Addr} {R n : Nat} {SP : Addr} {s : State}
    (E : Env K W D R n SP s) {v : VReg} {l : Block} {i : Nat}
    (hv : vBlock (s.v v) = lAt l (ntz i)) :
    WP isa (.block (cachedIncrement v)) s (LNtzPost W l i s) := by
  have w₀ : InRegions s.wr (W + 96#64) 8 := E.perm.wW (d := lO) (n := 8) (by decide)
  have w₁ : InRegions s.wr (W + 104#64) 8 := E.perm.wW (d := lO+8) (n := 8) (by decide)
  refine WP.of_runBlock ⟨_, by orun [cachedIncrement, E.x19, w₀, w₁, v_write], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · change Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] s.mem
      ((s.mem.writeW (W + BitVec.ofNat 64 lO) ((s.v v).extractLsb' 0 64)).writeW
        (W + BitVec.ofNat 64 (lO+8)) ((s.v v).extractLsb' 64 64))
    rw [← addr8 W lO]; exact Proof.Cmac.frame_store2 _ _ _
  · change blockAtMem ((s.mem.writeW (W + BitVec.ofNat 64 lO) ((s.v v).extractLsb' 0 64)).writeW
      (W + BitVec.ofNat 64 (lO+8)) ((s.v v).extractLsb' 64 64)) _ = _
    rw [← addr8 W lO, blockAtMem_store2, vBlock_words, hv]
  · have h₉ : r ≠ .x9 := fun h => hr (by simp [ntzRegs, h])
    have h₁₀ : r ≠ .x10 := fun h => hr (by simp [ntzRegs, h])
    simp [gpr_write, h₉, h₁₀]

/-- Changes confined to the temporary increment preserve a pass invariant. -/
theorem PassInv.of_temp {K W D : Addr} {R n : Nat} {SP : Addr} {m i : Nat} {O0 l : Block}
    {X : Nat → Block} {fB : Block → Block → Block} {ckF : Nat → Block} {s t u : State}
    (P : PassInv K W D R n SP m O0 l X fB ckF s t i) (hD : DBuf K W s D (16*m))
    (fr : Frame [⟨W + BitVec.ofNat 64 lO, 16⟩] t.mem u.mem)
    (g : ∀ r, r ∉ ntzRegs → u.gpr r = t.gpr r) (sp : u.sp = t.sp) (rd : u.rd = t.rd) (wr : u.wr = t.wr) :
    PassInv K W D R n SP m O0 l X fB ckF s u i := by
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
    ofs := (wb (by decide)).trans P.ofs
    ck := (wb (by decide)).trans P.ck
    l0 := (wb (by decide)).trans P.l0
    blk := ?_
    gpr := fun r hr => (g r (fun h => hr (by
      simp only [ntzRegs, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [passRegs]))).trans (P.gpr r hr) }
  intro k hk
  rw [blockAtMem_frame fr (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hD.slice (a := 16*k) (k := 16) (by omega)).w.sub_right (Lay.wSub (by decide))), P.blk k hk]

theorem block_keepsVec {is : List Instr} {s t : State} {v : VReg}
    (h : runBlock isa is s = some t) (hv : ∀ i ∈ is, vdstOf i ≠ some v) : t.v v = s.v v := by
  obtain ⟨tr, u, ex, rfl⟩ := (WP.of_runBlock ⟨t, h, rfl⟩ : WP isa (.block is) s (fun u => u = t))
  exact Exec.vec (c := .block is) (r := v) hv ex

theorem loadV_run {W : Addr} {s : State} (v : VReg) {a : Nat}
    (ha : a % 16 = 0 ∧ a < 65536) (h19 : s.gpr .x19 = W)
    (rq : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 a) 16) :
    runBlock isa [.ldrq v .x19 a] s = some (s.setV v (s.mem.read (W + BitVec.ofNat 64 a) 16)) := by
  orun [ha.1, ha.2, h19, rq]

/-- Double a scratch block and retain its result in a caller-saved vector. -/
theorem cacheDouble_ok {W : Addr} {s : State} (v : VReg) {a : Nat}
    (ha : a % 8 = 0 ∧ a + 8 < 32768) (h19 : s.gpr .x19 = W)
    (hw : Covers [⟨W, 2560⟩] s.wr) (haW : a + 16 ≤ 2560) :
    ∃ t, runBlock isa (dbl .x19 a lO ++ ([.ldrq v .x19 lO] : List Instr)) s = some t ∧
      BlkStep W lO (Spec.Ocb.double (blockAtMem s.mem (W + BitVec.ofNat 64 a))) ntzRegs s t ∧
      vBlock (t.v v) = Spec.Ocb.double (blockAtMem s.mem (W + BitVec.ofNat 64 a)) ∧
      (∀ r, r ≠ v → t.v r = s.v r) := by
  have wW : ∀ {d n : Nat}, d + n ≤ 2560 → InRegions s.wr (W + BitVec.ofNat 64 d) n := fun h =>
    Proof.AesGcm.AArch64.in_off hw h (by decide)
  obtain ⟨u, run, B⟩ := dbl_ok (b := .x19) (a := a) (d := lO) ha (by decide) h19 h19 (by decide)
    (Proof.AesGcm.AArch64.in_left (wW (by omega)))
    (Proof.AesGcm.AArch64.in_left (wW (by omega))) (wW (by decide)) (wW (by decide))
  have load := loadV_run (s := u) v (a := lO) (by decide) (by rw [B.gpr _ (by decide), h19])
    (by rw [B.rd, B.wr]; exact Proof.AesGcm.AArch64.in_left (wW (by decide)))
  refine ⟨_, by rw [runBlock_append, run, Option.bind_some, load], ?_, ?_, fun r hr => ?_⟩
  · exact ⟨B.frame, B.val, fun r hr => B.gpr r (fun h => hr (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [ntzRegs])), B.sp, B.rd, B.wr⟩
  · rw [v_setV_self, vBlock_read, B.val]
  · rw [v_setV_of_ne _ _ hr]
    exact block_keepsVec run (by simp [dbl, vdstOf, ld, st, Impl.AesGcm.AArch64.imm])

/-- Cache initialization touches only the already permitted increment slot. -/
theorem passCacheInit_ok {K W D : Addr} {R n : Nat} {SP : Addr} {m i : Nat} {O0 l : Block}
    {X : Nat → Block} {fB : Block → Block → Block} {ckF : Nat → Block} {s t : State}
    (P : PassInv K W D R n SP m O0 l X fB ckF s t i) (hD : DBuf K W s D (16*m)) :
    WP isa passCacheInit t fun u => PassInv K W D R n SP m O0 l X fB ckF s u i ∧ LCache l u := by
  let t₁ := t.setV .v0 (t.mem.read (W + BitVec.ofNat 64 l0O) 16)
  have run₁ := loadV_run (s := t) .v0 (a := l0O) (by decide) P.env.x19 (P.env.perm.wR (by decide))
  have P₁ : PassInv K W D R n SP m O0 l X fB ckF s t₁ i :=
    P.of_temp hD (Frame.refl _ _) (fun _ _ => rfl) rfl rfl rfl
  have v₀ : vBlock (t₁.v .v0) = lAt l 0 := by rw [v_setV_self, vBlock_read, P.l0]
  obtain ⟨t₂, run₂, B₂, v₁, keep₂⟩ := cacheDouble_ok .v1 (a := l0O) (by decide) P₁.env.x19 P₁.env.perm.w (by decide)
  have P₂ := P₁.of_temp hD B₂.frame B₂.gpr B₂.sp B₂.rd B₂.wr
  obtain ⟨t₃, run₃, B₃, v₂, keep₃⟩ := cacheDouble_ok .v2 (a := lO) (by decide) P₂.env.x19 P₂.env.perm.w (by decide)
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.of_runBlock ⟨t₂, run₂, ?_⟩)
  refine WP.of_runBlock ⟨t₃, run₃, P₂.of_temp hD B₃.frame B₃.gpr B₃.sp B₃.rd B₃.wr, ?_⟩
  refine ⟨by rw [keep₃ _ (by decide), keep₂ _ (by decide), v₀], ?_, ?_⟩
  · rw [keep₃ _ (by decide), v₁, P₁.l0]; rfl
  · rw [v₂, B₂.val, P₁.l0]; rfl

theorem cachedStep_keeps (v : VReg) {body : List Instr} (hV : body.all keepsCache = true) :
    (passCachedStep v body).allInstrs keepsCache = true := by
  rw [Code.allInstrs_eq]
  simp [passCachedStep, cachedIncrement, instrs, List.all_append, hV, xor16, nextBlock, keepsCache, vdstOf,
    ld, st, Impl.AesGcm.AArch64.ptr]

theorem lastStep_keeps {body : List Instr} (hV : body.all keepsCache = true) :
    (passLastStep body).allInstrs keepsCache = true := by
  rw [Code.allInstrs_eq]
  simp [passLastStep, batchLastIncrement, cachedIncrement, low1, instrs, List.all_append, hV,
    dbl, xor16, nextBlock, keepsCache, vdstOf, ld, st, Impl.AesGcm.AArch64.ptr, Impl.AesGcm.AArch64.imm]

theorem batchLastIncrement_ok {K W D : Addr} {R n : Nat} {SP : Addr} {s : State}
    (E : Env K W D R n SP s) {l : Block} (C : LCache l s) {k : Nat}
    (hi : 8*k+8 < 2^64) (h25 : s.gpr .x25 = BitVec.ofNat 64 (8*k+8)) :
    WP isa batchLastIncrement s (LNtzPost W l (8*k+8) s) := by
  unfold batchLastIncrement
  refine WP.seq (WP.mono (cachedIncrement_ok (i := 4) E
    (by simpa only [show ntz 4 = 2 by decide] using C.2.2)) fun u P => ?_)
  let t := u.write .x .x14 (u.gpr .x25 >>> 2)
  have run : runBlock isa [.lsr .x .x14 .x25 2] u = some t := by orun []
  have h14 : t.gpr .x14 = BitVec.ofNat 64 ((8*k+8)/2^2) := by
    simp only [t,gpr_write,ite_true,BitVec.setWidth_eq,P.gpr .x25 (by decide),h25,
      Proof.AesGcm.AArch64.lsr_ofNat _ _ hi]
  have hntz : ntz (8*k+8) = 2 + ntz ((8*k+8)/2^2) := by
    rw [Proof.Ocb.ntz_even (by omega) (by omega),
      show (8*k+8)/2 = 4*k+4 by omega,Proof.Ocb.ntz_even (by omega) (by omega)]
    simp only [show (4*k+4)/2 = 2*k+2 by omega, show (8*k+8)/2^2 = 2*k+2 by omega]
    omega
  refine WP.seq (WP.of_runBlock ⟨t,run,?_⟩)
  refine WP.mono (lNtzLoop_ok (s := t)
    (by simp only [t,gpr_write,reduceCtorEq,ite_false]; rw [P.gpr _ (by decide),E.x19])
    (by change Covers _ u.wr; rw [P.wr]; exact E.perm.w) hi (by omega) (by omega) hntz h14
    (by change blockAtMem u.mem _ = _; simpa only [show ntz 4 = 2 by decide] using P.val)) fun z Q => ?_
  refine ⟨P.frame.trans Q.frame,Q.val,fun r hr => ?_,Q.sp.trans P.sp,Q.rd.trans P.rd,Q.wr.trans P.wr⟩
  rw [Q.gpr r hr]
  have h : r ≠ .x14 := fun h => hr (by simp [ntzRegs,h])
  simp only [t,gpr_write,h,ite_false]
  exact P.gpr r hr

open VG.Proof.AesGcm.AArch64 (lsr_ofNat eval_zero eval_nonzero)

theorem passCount_ok {K W D : Addr} {R n : Nat} {SP : Addr} {m i : Nat} {O0 l : Block}
    {X : Nat → Block} {fB : Block → Block → Block} {ckF : Nat → Block} {s t : State}
    (P : PassInv K W D R n SP m O0 l X fB ckF s t i) (hD : DBuf K W s D (16*m))
    (hm : m < 2^60) :
    WP isa (.block [.lsr .x .x9 .x24 3]) t fun u =>
      PassInv K W D R n SP m O0 l X fB ckF s u i ∧
      u.gpr .x9 = BitVec.ofNat 64 ((m-i)/8) ∧ u.v = t.v := by
  refine WP.of_runBlock ⟨t.write .x .x9 (t.gpr .x24 >>> 3), by orun [], ?_⟩
  refine ⟨P.of_temp hD (Frame.refl _ _) (fun r hr => ?_) rfl rfl rfl, ?_, rfl⟩
  · have h : r ≠ .x9 := fun h => hr (by simp [ntzRegs, h])
    simp [gpr_write, h]
  · simp [gpr_write, P.x24, lsr_ofNat _ _ (show m-i < 2^64 by omega)]

section
variable {K W D : Addr} {R n : Nat} {SP : Addr} (L : Lay K W) {m : Nat} {O0 l : Block}
  {X : Nat → Block} {fB : Block → Block → Block} {fC : Block → Block → Block → Block}
  {ckF : Nat → Block} {body : List Instr}
  (hB : BodyOk W body fB fC) (hV : body.all keepsCache = true)
  (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
  {t₀ : State} (hD : DBuf K W t₀ D (16 * m)) (hm : m < 2 ^ 60)
include L hB hV hckF hD hm

theorem cachedStep_ok {t : State} {i : Nat} (hi : i < m)
    (P : PassInv K W D R n SP m O0 l X fB ckF t₀ t i) (C : LCache l t)
    (v : VReg) (hv : vBlock (t.v v) = lAt l (ntz (i+1))) :
    WP isa (passCachedStep v body) t fun u =>
      PassInv K W D R n SP m O0 l X fB ckF t₀ u (i+1) ∧ LCache l u :=
  keepCache (pass_step_with L hB hckF hD hm hi P (cachedIncrement_ok P.env hv)) (cachedStep_keeps v hV) C

theorem lastStep_cached_ok {t : State} {k : Nat} (hi : 8*k+7 < m)
    (P : PassInv K W D R n SP m O0 l X fB ckF t₀ t (8*k+7)) (C : LCache l t) :
    WP isa (passLastStep body) t fun u =>
      PassInv K W D R n SP m O0 l X fB ckF t₀ u (8*k+7+1) ∧ LCache l u := by
  have ho := batchLastIncrement_ok (k := k) P.env C (by omega)
    (by simpa only [show 8*k+7+1 = 8*k+8 by omega] using P.x25)
  exact keepCache (pass_step_with L hB hckF hD hm hi P ho) (lastStep_keeps hV) C

omit L hB hV hckF hD hm in
 theorem ntz_eight_two (k : Nat) : ntz (8*k+2) = 1 := by
  rw [Proof.Ocb.ntz_even (by omega) (by omega), show (8*k+2)/2 = 4*k+1 by omega,
    Proof.Ocb.ntz_odd (by omega)]
omit L hB hV hckF hD hm in
 theorem ntz_eight_four (k : Nat) : ntz (8*k+4) = 2 := by
  rw [Proof.Ocb.ntz_even (by omega) (by omega), show (8*k+4)/2 = 4*k+2 by omega,
    Proof.Ocb.ntz_even (by omega) (by omega), show (4*k+2)/2 = 2*k+1 by omega,
    Proof.Ocb.ntz_odd (by omega)]
omit L hB hV hckF hD hm in
 theorem ntz_eight_six (k : Nat) : ntz (8*k+6) = 1 := by
  rw [Proof.Ocb.ntz_even (by omega) (by omega), show (8*k+6)/2 = 4*k+3 by omega,
    Proof.Ocb.ntz_odd (by omega)]

theorem passBatch_ok {t : State} {k : Nat} (hk : 8*k+8 ≤ m)
    (P : PassInv K W D R n SP m O0 l X fB ckF t₀ t (8*k)) (C : LCache l t) :
    WP isa (passBatch body) t fun u =>
      PassInv K W D R n SP m O0 l X fB ckF t₀ u (8*(k+1)) ∧ LCache l u := by
  unfold passBatch
  refine WP.seq (WP.mono (cachedStep_ok L hB hV hckF hD hm (by omega) P C .v0
    (by rw [Proof.Ocb.ntz_odd (by omega)]; exact C.1)) fun t₁ ⟨P₁,C₁⟩ => ?_)
  refine WP.seq (WP.mono (cachedStep_ok L hB hV hckF hD hm (by omega) P₁ C₁ .v1
    (by rw [show 8*k+1+1 = 8*k+2 by omega, ntz_eight_two]; exact C₁.2.1)) fun t₂ ⟨P₂,C₂⟩ => ?_)
  refine WP.seq (WP.mono (cachedStep_ok L hB hV hckF hD hm (by omega) P₂ C₂ .v0
    (by rw [Proof.Ocb.ntz_odd (by omega)]; exact C₂.1)) fun t₃ ⟨P₃,C₃⟩ => ?_)
  refine WP.seq (WP.mono (cachedStep_ok L hB hV hckF hD hm (by omega) P₃ C₃ .v2
    (by rw [show 8*k+1+1+1+1 = 8*k+4 by omega, ntz_eight_four]; exact C₃.2.2)) fun t₄ ⟨P₄,C₄⟩ => ?_)
  refine WP.seq (WP.mono (cachedStep_ok L hB hV hckF hD hm (by omega) P₄ C₄ .v0
    (by rw [Proof.Ocb.ntz_odd (by omega)]; exact C₄.1)) fun t₅ ⟨P₅,C₅⟩ => ?_)
  refine WP.seq (WP.mono (cachedStep_ok L hB hV hckF hD hm (by omega) P₅ C₅ .v1
    (by rw [show 8*k+1+1+1+1+1+1 = 8*k+6 by omega, ntz_eight_six]; exact C₅.2.1)) fun t₆ ⟨P₆,C₆⟩ => ?_)
  refine WP.seq (WP.mono (cachedStep_ok L hB hV hckF hD hm (by omega) P₆ C₆ .v0
    (by rw [Proof.Ocb.ntz_odd (by omega)]; exact C₆.1)) fun t₇ ⟨P₇,C₇⟩ => ?_)
  refine WP.mono (lastStep_cached_ok (R := R) (n := n) (SP := SP) (k := k) L hB hV hckF hD hm (by omega)
    (by simpa only [show 8*k+1+1+1+1+1+1+1 = 8*k+7 by omega] using P₇) C₇) fun u ⟨P₈,C₈⟩ => ?_
  exact ⟨by simpa only [show 8*k+7+1 = 8*(k+1) by omega] using P₈, C₈⟩

theorem pass_ok {t : State} (hm0 : 0 < m)
    (P : PassInv K W D R n SP m O0 l X fB ckF t₀ t 0) :
    WP isa (pass body) t fun u => PassInv K W D R n SP m O0 l X fB ckF t₀ u m := by
  unfold pass
  refine WP.seq (WP.mono (passCount_ok P hD hm) fun t₁ ⟨P₁,h9,_⟩ => ?_)
  refine WP.ite _ (eval_zero h9 (by omega)) (fun hz => ?_) (fun hn => ?_)
  · exact passScalar_ok L hB hckF hD hm0 hm P₁
  · have hn : m / 8 ≠ 0 := of_decide_eq_false hn
    refine WP.seq (WP.mono (passCacheInit_ok P₁ hD) fun t₂ ⟨P₂,C₂⟩ => ?_)
    have loop : WP isa (.loop (.seq (passBatch body) (.block [.lsr .x .x9 .x24 3])) (.nonzero .x .x9)) t₂
        (fun u => PassInv K W D R n SP m O0 l X fB ckF t₀ u (8*(m/8))) := by
      refine WP.loop (M := isa)
        (fun (j : Nat) (u : State) => ∃ k, j = m/8-k ∧ 8*k+8 ≤ m ∧
          PassInv K W D R n SP m O0 l X fB ckF t₀ u (8*k) ∧ LCache l u) ?_
        (m/8) _ ⟨0, by omega, by omega, P₂, C₂⟩
      rintro j u ⟨k,rfl,hk,P,C⟩
      refine WP.seq (WP.mono (passBatch_ok L hB hV hckF hD hm hk P C) fun u₁ ⟨P',C'⟩ => ?_)
      refine WP.mono (passCount_ok P' hD hm) fun u₂ ⟨P'',h9,hv⟩ => ?_
      have ev := eval_nonzero h9 (by omega)
      by_cases he : (m-8*(k+1))/8 = 0
      · left
        exact ⟨ev.trans (by simp [he]), (show k+1 = m/8 by omega) ▸ P''⟩
      · right
        refine ⟨ev.trans (by simp [he]), m/8-(k+1), by omega, k+1, rfl, by omega, P'', ?_⟩
        simpa only [LCache, hv] using C'
    refine WP.seq (WP.mono loop fun u P' => ?_)
    refine WP.ite _ (eval_zero P'.x24 (by omega)) (fun hz => ?_) (fun hn => ?_)
    · have hz : m-8*(m/8) = 0 := of_decide_eq_true hz
      exact WP.block_nil (by simpa only [show 8*(m/8) = m by omega] using P')
    · have hn : m-8*(m/8) ≠ 0 := of_decide_eq_false hn
      exact passScalar_ok L hB hckF hD (by omega) hm P'

end

end VG.Proof.AesOcb.AArch64

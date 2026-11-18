module

public import VerifiedGarbage.Proof.Ecdsa.X86_64.Layout
import VerifiedGarbage.Proof.Ecdsa.X86_64.SharedSlots
import VerifiedGarbage.Proof.Weierstrass.X86_64.Unch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-! ### `Ecdsa.X86_64.Finish`, which the modules that import this one used -/

section

/-!
# ECDSA on x86-64: the result

`finish` writes `r ‖ s` big-endian to `out`, or zeros, by the flag's mask,
returns the flag's low bit, and restores the callee-saved registers
(`finish_ok`). The stores are outside the working space, so it keeps its
numbers and the saved registers (`Outside.unch_far`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps)

variable {c : Cfg}

/-- The bytes of a range apart from the one that changed. -/
theorem bytesAt_keep {q p : Addr} {len k : Nat} {m m' : Mem} (h : Outside q 0 len m m')
    (hd : Region.Disjoint ⟨p, k⟩ ⟨q, len⟩) (hl : len ≤ 2 ^ 64) (hk : k ≤ 2 ^ 64) :
    Spec.Ecdsa.bytesAt m' p k = Spec.Ecdsa.bytesAt m p k := by
  simp only [Spec.Ecdsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  exact keep_of_disjoint' h hd hl hi hk

theorem movRcx_mem_ok {s : State} {base : Addr} (hs : Scr s base size) {d : Nat} (hd : d + 8 ≤ size) :
    WP isa (.block [.mov .rcx (.mem (sc d))]) s fun s' =>
      s'.gpr .rcx = word s.mem base d ∧ Keeps [.rcx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
    State.load64, ea_sc, RegUpd.gpr_setReg, ite_true, hs.rdi, ld_sc hs hd,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, hr, ite_false]

theorem raxBit_ok (s : State) :
    WP isa (.block [.mov .rax (.reg .rcx), .alu .and .rax (.imm 1)]) s fun s' =>
      s'.gpr .rax = s.gpr .rcx &&& 1 ∧ Keeps [.rax] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.map_some,
    Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨by rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem mask_bit (b : Bool) :
    ((if b then BitVec.allOnes 64 else 0) &&& 1 : BitVec 64).setWidth 32 = if b then 1 else 0 := by
  cases b <;> decide

theorem finish_eq (c : Cfg) : c.finish = ([.mov .rcx (.mem (sc (c.sl FLAG)))] : List Instr) ++
    (storeBytes c.C.len c.n .rsi 0 (c.sl RR) ++ (storeBytes c.C.len c.n .rsi c.C.len (c.sl SS) ++
    (([.mov .rax (.reg .rcx), .alu .and .rax (.imm 1)] : List Instr) ++
    Spill.restoreCode .rdi Cfg.saved))) := by
  simp only [Cfg.finish, List.append_assoc]; rfl

theorem saved_lt : ∀ p ∈ Cfg.saved, p.2 + 8 ≤ 48 := by decide

theorem Saved.unch {base : Addr} {g : Reg → BitVec 64} {m m' : Mem}
    (h : Spill.Saved m base g Cfg.saved) {W : List (Nat × Nat)} (hW : ∀ w ∈ W, 48 ≤ w.1)
    (hu : Unch base W m m') : Spill.Saved m' base g Cfg.saved := fun p hp => by
  have := saved_lt p hp
  exact (hu.word (d := p.2) (fun w hw => Or.inl (by have := hW w hw; omega_arith)) (by omega_using [this])).trans (h p hp)

/-- The result, the return value and the callee-saved registers. -/
theorem finish_ok (hc : BaseCfgOk c) {base : Addr} {s : State} (hs : Scr s base size) {out : Addr}
    (hrsi : s.gpr .rsi = out) (hw : (⟨out, 2 * c.C.len⟩ : Region) ∈ s.wr)
    (hd : Region.Disjoint ⟨out, 2 * c.C.len⟩ ⟨base, size⟩) (hfit : out.toNat + 2 * c.C.len ≤ 2 ^ 64)
    {g : Reg → BitVec 64} (hsv : Spill.Saved s.mem base g Cfg.saved) (b : Bool)
    (hf : word s.mem base (c.sl FLAG) = if b then BitVec.allOnes 64 else 0) :
    WP isa (.block c.finish) s fun s' =>
      Spec.Ecdsa.bytesAt s'.mem out (2 * c.C.len) =
        (if b then toBytes c.C.len (sv c base s RR) ++ toBytes c.C.len (sv c base s SS)
          else List.replicate (2 * c.C.len) 0) ∧
      (s'.gpr .rax).setWidth 32 = (if b then 1 else 0) ∧
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = g r) ∧
      (∀ r, r ∉ [.rax, .rcx, .rdx, .rbx, .rbp, .r12, .r13, .r14, .r15] → s'.gpr r = s.gpr r) := by
  have h7 := hc.n10
  have hn0 := hc.n0
  have := hc.len8; have := hc.len_lo; have := hc.len_hi
  have hn := hs.nowrap
  obtain hRR := sl_le c h7 (i := RR) (by decide)
  obtain hSS := sl_le c h7 (i := SS) (by decide)
  obtain hF := sl_le c h7 (i := FLAG) (by decide)
  obtain hq : ∀ d, d + c.C.len ≤ 2 * c.C.len → (out + BitVec.ofNat 64 d).toNat + c.C.len ≤ 2 ^ 64 :=
    fun d hd => by
      rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (show d < 2 ^ 64 by omega_using [hfit, hd]),
        Nat.mod_eq_of_lt (by omega_using [hfit, hd])]
      omega_using [hfit, hd]
  obtain hwr : ∀ {t : State} {d : Nat}, (⟨out, 2 * c.C.len⟩ : Region) ∈ t.wr → d + c.C.len ≤ 2 * c.C.len →
      ∀ e m, e + m ≤ c.C.len → InRegions t.wr (out + BitVec.ofNat 64 d + BitVec.ofNat 64 e) m :=
    fun hw' hd e m hm => ⟨_, hw', by rw [Offset.add_add]; exact Offset.contains_base out (by omega_using [hd, hm]) (by omega_using [h7, this, hd, hm])⟩
  obtain hdsc : ∀ {a d : Nat}, a + 8 * c.n ≤ size → d + c.C.len ≤ 2 * c.C.len →
      Region.Disjoint ⟨off base a, 8 * c.n⟩ ⟨out + BitVec.ofNat 64 d, c.C.len⟩ := fun ha hd' =>
    (hd.symm.sub_left (Offset.sub_base base ha)).sub_right (Offset.sub_base out hd')
  obtain hscd : ∀ {d : Nat}, d + c.C.len ≤ 2 * c.C.len →
      Region.Disjoint ⟨base, size⟩ ⟨out + BitVec.ofNat 64 d, c.C.len⟩ := fun hd' =>
    hd.symm.sub_right (Offset.sub_base out hd')
  rw [finish_eq, WP.block_append_iff]
  refine WP.mono (movRcx_mem_ok hs (d := c.sl FLAG) (by omega_using [hn0, hF])) fun s₁ ⟨e₁, k₁⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  obtain hrsi₁ : s₁.gpr .rsi = out := by rw [k₁.1 _ (by decide), hrsi]
  rw [WP.block_append_iff]
  refine WP.mono (storeBytes_ok hs₁ (dst := .rsi) (d := 0) (a := c.sl RR) (by decide) (by decide) b
    (by rw [e₁, hf]) hRR (by omega_arith) hc.len_lo hc.len_hi (by rw [hrsi₁]; exact hq 0 (by omega_using []))
    (by rw [hrsi₁]; exact hwr (by rw [k₁.2.2.2]; exact hw) (by omega_using []))
    (by rw [hrsi₁]; exact hdsc hRR (by omega_using []))) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  rw [hrsi₁] at e₂ O₂
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  obtain U₂ := O₂.unch_far (hscd (d := 0) (by omega_using []))
  obtain hrsi₂ : s₂.gpr .rsi = out := by rw [k₂.gpr _ (by decide), hrsi₁]
  obtain hrcx₂ : s₂.gpr .rcx = if b then BitVec.allOnes 64 else 0 := by
    rw [k₂.gpr _ (by decide), e₁, hf]
  obtain ss₂ : wordsVal s₂.mem base (c.sl SS) c.n = sv c base s SS := by
    rw [U₂.wordsVal (fun w hw => by simp only [List.mem_singleton] at hw; subst hw; omega_using [hSS]) (by omega_using [hn, hSS]), hm₁]
  rw [WP.block_append_iff]
  refine WP.mono (storeBytes_ok hs₂ (dst := .rsi) (d := c.C.len) (a := c.sl SS) (by decide) (by decide) b
    hrcx₂ hSS (by omega_arith) hc.len_lo hc.len_hi (by rw [hrsi₂]; exact hq _ (by omega_using []))
    (by rw [hrsi₂]; exact hwr (by rw [k₂.wr, k₁.2.2.2]; exact hw) (by omega_using []))
    (by rw [hrsi₂]; exact hdsc hSS (by omega_using []))) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  rw [hrsi₂] at e₃ O₃
  obtain hs₃ := hs₂.of_keepRegs k₃ (by decide)
  obtain U₃ := O₃.unch_far (hscd (d := c.C.len) (by omega_using []))
  obtain hrcx₃ : s₃.gpr .rcx = if b then BitVec.allOnes 64 else 0 := by
    rw [k₃.gpr _ (by decide), hrcx₂]
  obtain first : Spec.Ecdsa.bytesAt s₃.mem out c.C.len =
      if b then toBytes c.C.len (sv c base s RR) else List.replicate c.C.len 0 := by
    rw [bytesAt_keep O₃ (Offset.base_disjoint out (Nat.le_refl _) (by omega_using [hfit])) (by omega_using [hfit]) (by omega_using [hfit])]
    have e₂' := e₂
    rw [(BitVec.add_zero out : out + BitVec.ofNat 64 0 = out)] at e₂'
    rw [e₂', hm₁]
  rw [WP.block_append_iff]
  refine WP.mono (raxBit_ok s₃) fun s₄ ⟨e₄, k₄⟩ => ?_
  obtain hs₄ := hs₃.of_keeps k₄ (by decide)
  obtain hsv₄ : Spill.Saved s₄.mem base g Cfg.saved := by
    rw [k₄.2.1]
    obtain h48 : ∀ w ∈ [(size, 2 ^ 64)], 48 ≤ w.1 := fun w hw => by
      simp only [List.mem_singleton] at hw; subst hw; decide
    exact Saved.unch (Saved.unch (hm₁ ▸ hsv) h48 U₂) h48 U₃
  refine WP.mono (Spill.restore_ok .rdi Cfg.saved g s₄ (by decide) (fun p hp => ?_)
    (by rw [hs₄.rdi]; exact hsv₄)) fun s₅ ⟨g₅, r₅, m₅, _, _⟩ => ?_
  · have := saved_lt p hp
    rw [hs₄.rdi]; exact ⟨_, List.mem_append_right _ hs₄.wr, hs₄.contains (by have : size = 8192 := rfl; omega_arith) (by decide)⟩
  refine ⟨?_, ?_, g₅, fun r hr => ?_⟩
  · rw [m₅, k₄.2.1, show 2 * c.C.len = c.C.len + c.C.len by omega_using [], bytesAt_add, first, e₃, ss₂]
    cases b
    · simp only [Bool.false_eq_true, ite_false, List.replicate_append_replicate]
    · simp only [ite_true]
  · have hra : Reg.rax ∉ Cfg.saved.map Prod.fst := by decide
    rw [r₅ _ hra, e₄, hrcx₃, mask_bit]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [r₅ r (by simp [Cfg.saved, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2]),
      k₄.1 r (by simp [hr.1]), k₃.gpr r (by simp [hr.1, hr.2.2.1]), k₂.gpr r (by simp [hr.1, hr.2.2.1]),
      k₁.1 r (by simp [hr.2.1])]

end VG.Proof.Ecdsa.X86_64

end

end

/-! ### `Ecdsa.X86_64.Middle`, which this module and modules that import it used -/

section

/-!
# ECDSA on x86-64: `x`, `r`, `k R mod n` and the checks of `d`, `k`, `r`

`middle` computes `x = X Z^(p-2)` from `X` and the power in `ACC`, left
Montgomery's form (a multiplication by 1), `r = x mod n` (an addition of
zero modulo `n`, as `x < p < 2n`) and `k R mod n` (a multiplication by
`R² mod n`), then ands the masks of `d, k ∈ [1, n-1]` and `r ≠ 0` into the
flag (`middle_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

theorem middle_eq (c : Cfg) : c.middle.inline = .seq ((c.mulPF (c.sl XM) (c.sl RX) (c.sl ACC)).inline)
    (.seq ((c.mulPF (c.sl X) (c.sl XM) (c.sl ONE)).inline)
    (.seq (.block (add c.MN' (c.sl RR) (c.sl X) (c.sl ZERO)))
    (.seq (opProg c.MN' (.mul (c.sl KM) (c.sl K) (c.sl R2N))).inline
    (.block (c.checkRange (c.sl D) ++ c.checkRange (c.sl K) ++ c.checkNonzero (c.sl RR)))))) := rfl

/-- What `middle`'s field operations leave. -/
structure MidPost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  scr : Scr s' base size
  gpr : ∀ r, r ∉ clob c.n → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  unch : Unch base ([XM, X, RR, KM, TMP].map fun i => (c.sl i, 8 * c.n)) s.mem s'.mem
  modP : ModOkW c.MP' size c.C.p s'.mem base
  modN : ModOkW c.MN' size c.C.n s'.mem base
  x_lt : sv c base s' X < c.C.p
  x : Fin.ofNat c.C.p (sv c base s' X) =
    toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC)
  rr : sv c base s' RR = sv c base s' X % c.C.n
  km_lt : sv c base s' KM < c.C.n
  km : toM c.C.n (2 ^ (64 * c.n)) (sv c base s' KM) = Fin.ofNat c.C.n (sv c base s K)

theorem unch_slots {base : Addr} {m₁ m₂ : Mem} {o : Nat} {l : List Nat} {M : Mod} (hMn : M.n = c.n)
    (hMt : M.tmp = c.sl TMP) (h : Unch base [(c.sl o, 8 * M.n), (M.tmp, 8 * M.n)] m₁ m₂)
    (ho : o ∈ l) (ht : TMP ∈ l) : Unch base (l.map fun i => (c.sl i, 8 * c.n)) m₁ m₂ :=
  h.mono fun w hw => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, hMn, hMt] at hw
    rcases hw with rfl | rfl
    · exact List.mem_map_of_mem ho
    · exact List.mem_map_of_mem ht

/-- The four field operations of `middle`. -/
theorem midOps_ok (hc : BaseCfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    (hMP : ModOkW c.MP' size c.C.p s.mem base) (hMN : ModOkW c.MN' size c.C.n s.mem base)
    (hacc : sv c base s ACC < c.C.p) (hone : sv c base s ONE = 1) (hzero : sv c base s ZERO = 0)
    (hr2 : sv c base s R2N = 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.n) {rest : Prog isa}
    {Q : State → Prop} (h : ∀ s', MidPost c base s s' → WP isa rest s' Q) :
    WP isa (.seq ((c.mulPF (c.sl XM) (c.sl RX) (c.sl ACC)).inline)
      (.seq ((c.mulPF (c.sl X) (c.sl XM) (c.sl ONE)).inline)
      (.seq (.block (add c.MN' (c.sl RR) (c.sl X) (c.sl ZERO)))
      (.seq (opProg c.MN' (.mul (c.sl KM) (c.sl K) (c.sl R2N))).inline rest)))) s Q := by
  have h7 := hc.n10
  have hn := hs.nowrap
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  obtain hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hpn := hc.p_lt_2n
  -- `XM = X · ACC`.
  refine WP.seq (WP.mono (slMulPF_ok h7 hs hMP (o := XM) (a := RX) (b := ACC) (by decide)
    (by decide) (by decide) (by decide) hacc) fun s₁ ⟨k₁, _, e₁⟩ => ?_)
  obtain hs₁ := k₁.scr hs
  obtain kP₁ := hMP.keep (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  obtain kN₁ := hMN.keep (j := MN) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  obtain one₁ : sv c base s₁ ONE = 1 :=
    (sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)).trans hone
  -- `X = XM · 1`.
  refine WP.seq (WP.mono (slMulPF_ok h7 hs₁ kP₁ (o := X) (a := XM) (b := ONE) (by decide)
    (by decide) (by decide) (by decide) (by omega_using [hp3, one₁])) fun s₂ ⟨k₂, lt₂, e₂⟩ => ?_)
  obtain hs₂ := k₂.scr hs₁
  obtain kP₂ := kP₁.keep (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₂ (by decide) (by decide)
  obtain kN₂ := kN₁.keep (j := MN) (by decide) rfl rfl rfl rfl h7 hn k₂ (by decide) (by decide)
  obtain zero₂ : sv c base s₂ ZERO = 0 := by
    rw [sv_keep (MP'_n c) rfl h7 hn k₂ (by decide) (by decide) (by decide),
      sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide), hzero]
  obtain x₂ : Fin.ofNat c.C.p (sv c base s₂ X) =
      toM c.C.p (2 ^ (64 * c.n)) (sv c base s RX) * toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) := by
    rw [toM_one_mul hpR (by rw [e₂, one₁]), toM_mul hpR e₁]
  -- `RR = X mod n`.
  refine WP.seq (WP.mono (slAdd_ok (MN'_n c) (MN'_tmp c) (MN'_mo c) h7 hs₂ kN₂ (o := RR) (a := X) (b := ZERO) (by decide)
    (by decide) (by decide) (by decide) (by omega_using [hpn, lt₂, zero₂])) fun s₃ ⟨k₃, e₃⟩ => ?_)
  obtain hs₃ := k₃.scr hs₂
  obtain kP₃ := kP₂.keep (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₃ (by decide) (by decide)
  obtain kN₃ := kN₂.keep (j := MN) (by decide) rfl rfl rfl rfl h7 hn k₃ (by decide) (by decide)
  obtain r2₃ : sv c base s₃ R2N = 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.n := by
    rw [sv_keep (MN'_n c) rfl h7 hn k₃ (by decide) (by decide) (by decide),
      sv_keep (MP'_n c) rfl h7 hn k₂ (by decide) (by decide) (by decide),
      sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide), hr2]
  obtain K₃ : sv c base s₃ K = sv c base s K := by
    rw [sv_keep (MN'_n c) rfl h7 hn k₃ (by decide) (by decide) (by decide),
      sv_keep (MP'_n c) rfl h7 hn k₂ (by decide) (by decide) (by decide),
      sv_keep (MP'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)]
  -- `KM = K · R² mod n`.
  refine WP.seq (WP.mono (slMulN_ok h7 hs₃ kN₃ (o := KM) (a := K) (b := R2N) (by decide)
    (by decide) (by decide) (by decide) (by rw [r2₃]; exact Nat.mod_lt _ (by omega_using [hpn]))) fun s₄ ⟨k₄, lt₄, e₄⟩ => h s₄ ?_)
  obtain X₄ : sv c base s₄ X = sv c base s₂ X := by
    rw [sv_keep (MN'_n c) rfl h7 hn k₄ (by decide) (by decide) (by decide),
      sv_keep (MN'_n c) rfl h7 hn k₃ (by decide) (by decide) (by decide)]
  refine ⟨k₄.scr hs₃, fun r hr => ?_, by rw [k₄.rd, k₃.rd, k₂.rd, k₁.rd],
    by rw [k₄.wr, k₃.wr, k₂.wr, k₁.wr], ?_,
    kP₃.keep (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₄ (by decide) (by decide),
    kN₃.keep (j := MN) (by decide) rfl rfl rfl rfl h7 hn k₄ (by decide) (by decide),
    by rw [X₄]; exact lt₂, by rw [X₄]; exact x₂, ?_, lt₄,
    by rw [toM_r2 hnR (by rw [e₄, r2₃]), K₃]⟩
  · rw [k₄.gpr r hr, k₃.gpr r hr, k₂.gpr r hr, k₁.gpr r hr]
  · have l := [XM, X, RR, KM, TMP]
    exact (((unch_slots (MP'_n c) rfl k₁.unch (l := [XM, X, RR, KM, TMP]) (by simp) (by simp)).trans
      (unch_slots (MP'_n c) rfl k₂.unch (l := [XM, X, RR, KM, TMP]) (by simp) (by simp))).trans
      ((unch_slots (MN'_n c) rfl k₃.unch (l := [XM, X, RR, KM, TMP]) (by simp) (by simp)).trans
      (unch_slots (MN'_n c) rfl k₄.unch (l := [XM, X, RR, KM, TMP]) (by simp) (by simp)))).mono
      fun w hw => by
        simp only [List.mem_append, or_self] at hw
        exact hw
  · rw [sv_keep (MN'_n c) rfl h7 hn k₄ (by decide) (by decide) (by decide), e₃, zero₂,
      Nat.add_zero, X₄]

end VG.Proof.Ecdsa.X86_64

end

end

/-!
# ECDSA on x86-64: the checks, and `s = k⁻¹ (e + r d) mod n`

`checks_ok`: the masks of `d, k ∈ [1, n-1]` and `r ≠ 0` anded into the flag.
`scalarOps_ok`: `r`, `d` and `e` enter Montgomery's form modulo `n`, then
`s = k⁻¹ (e + r d)`, with `k⁻¹ R` in `ACC`, and `s` leaves it.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

/-- A slot apart from the flag word keeps its number. -/
theorem sv_flag {base : Addr} {m m' : Mem} (h : Outside base (c.sl FLAG) 8 m m') (h0 : 0 < c.n)
    (h7 : c.n < 10) (hn : base.toNat + size ≤ 2 ^ 64) {i : Nat} (hi : i < 45) (hif : i ≠ FLAG) :
    wordsVal m' base (c.sl i) c.n = wordsVal m base (c.sl i) c.n := by
  have := sl_apart c hif
  have := sl_le c h7 hi
  exact h.wordsVal (by omega_arith) (by omega_arith)

/-- The checks of `d`, `k` and `r`. -/
theorem checks_ok (hc : BaseCfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    (hMN : sv c base s MN = c.C.n) :
    WP isa (.block (c.checkRange (c.sl D) ++ c.checkRange (c.sl K) ++ c.checkNonzero (c.sl RR))) s
      fun s' => word s'.mem base (c.sl FLAG) = word s.mem base (c.sl FLAG) &&&
          mask (0 < sv c base s D ∧ sv c base s D < c.C.n) &&&
          mask (0 < sv c base s K ∧ sv c base s K < c.C.n) &&& mask (sv c base s RR ≠ 0) ∧
        KeepRegs [.rax, .rbp, .rcx, .rdx] s s' ∧ Outside base (c.sl FLAG) 8 s.mem s'.mem := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  obtain hf : c.sl FLAG + 8 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega_arith
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (checkRange_ok c hs h0 (sl_le c h7 (i := D) (by decide)) (sl_le c h7 (i := MN) (by decide))
    hf) fun s₁ ⟨f₁, k₁, O₁⟩ => ?_
  obtain hs₁ := hs.of_keepRegs k₁ (by decide)
  refine WP.mono (checkRange_ok c hs₁ h0 (sl_le c h7 (i := K) (by decide)) (sl_le c h7 (i := MN) (by decide))
    hf) fun s₂ ⟨f₂, k₂, O₂⟩ => ?_
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (checkNonzero_ok c hs₂ h0 (sl_le c h7 (i := RR) (by decide)) hf)
    fun s₃ ⟨f₃, k₃, O₃⟩ => ⟨?_, (k₁.trans k₂).trans (k₃.mono (by sub_regs)), O₁.trans (O₂.trans O₃)⟩
  obtain e₁ : ∀ i, i < 45 → i ≠ FLAG → wordsVal s₁.mem base (c.sl i) c.n = sv c base s i :=
    fun i hi hif => sv_flag O₁ h0 h7 hn hi hif
  obtain e₂ : ∀ i, i < 45 → i ≠ FLAG → wordsVal s₂.mem base (c.sl i) c.n = sv c base s i :=
    fun i hi hif => (sv_flag O₂ h0 h7 hn hi hif).trans (e₁ i hi hif)
  have hMN' : wordsVal s.mem base (c.sl MN) c.n = c.C.n := hMN
  rw [f₃, f₂, f₁, e₂ RR (by decide) (by decide), e₁ K (by decide) (by decide),
    e₁ MN (by decide) (by decide), hMN', hMN]

theorem scalar_eq (c : Cfg) : c.scalar.inline =
    .seq (opProg c.MNS (.mul (c.sl RM) (c.sl RR) (c.sl R2N))).inline
    (.seq (opProg c.MNS (.mul (c.sl DM) (c.sl D) (c.sl R2N))).inline
    (.seq (opProg c.MNS (.mul (c.sl EM) (c.sl E) (c.sl R2N))).inline
    (.seq (opProg c.MNS (.mul (c.sl TT) (c.sl RM) (c.sl DM))).inline
    (.seq (.block (add c.MN' (c.sl TT) (c.sl TT) (c.sl EM)))
    (.seq (opProg c.MNS (.mul (c.sl SM) (c.sl ACC) (c.sl TT))).inline
    (.seq (opProg c.MNS (.mul (c.sl SS) (c.sl SM) (c.sl ONE))).inline
    (.block (c.checkNonzero (c.sl SS) ++ c.finish)))))))) := rfl

/-- The first three multiplications by `R² mod n`. -/
theorem scalarIn_ok (hc : BaseCfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    (hMN : ModOkW c.MN' size c.C.n s.mem base)
    (hr2 : sv c base s R2N = 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.n) {rest : Prog isa}
    {Q : State → Prop}
    (h : ∀ s', Scr s' base size → ModOkW c.MN' size c.C.n s'.mem base →
      (∀ r, r ∉ clob c.n → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      Unch base ([62, RM, DM, EM, TT, SM, SS, TMP].map fun i => (c.sl i, 8 * c.n)) s.mem s'.mem →
      sv c base s' RM < c.C.n → sv c base s' DM < c.C.n → sv c base s' EM < c.C.n →
      toM c.C.n (2 ^ (64 * c.n)) (sv c base s' RM) = Fin.ofNat c.C.n (sv c base s RR) →
      toM c.C.n (2 ^ (64 * c.n)) (sv c base s' DM) = Fin.ofNat c.C.n (sv c base s D) →
      toM c.C.n (2 ^ (64 * c.n)) (sv c base s' EM) = Fin.ofNat c.C.n (sv c base s E) →
      WP isa rest s' Q) :
    WP isa (.seq (opProg c.MNS (.mul (c.sl RM) (c.sl RR) (c.sl R2N))).inline
      (.seq (opProg c.MNS (.mul (c.sl DM) (c.sl D) (c.sl R2N))).inline
      (.seq (opProg c.MNS (.mul (c.sl EM) (c.sl E) (c.sl R2N))).inline rest))) s Q := by
  have h7 := hc.n10
  have hn := hs.nowrap
  obtain hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  have hn3 := hc.n_ge
  obtain hr2lt : sv c base s R2N < c.C.n := by rw [hr2]; exact Nat.mod_lt _ (by omega_arith)
  refine WP.seq (WP.mono (slMulNS_ok h7 hs hMN (o := RM) (a := RR) (b := R2N) (by decide)
    (by decide) (by decide) (by decide) hr2lt) fun s₁ ⟨k₁, lt₁, e₁⟩ => ?_)
  obtain hs₁ := k₁.scr hs
  obtain kN₁ := hMN.keepShared (j := MN) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  obtain r₁ : sv c base s₁ R2N = sv c base s R2N := sv_shared_keep (MN'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)
  obtain d₁ : sv c base s₁ D = sv c base s D := sv_shared_keep (MN'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)
  obtain E₁ : sv c base s₁ E = sv c base s E := sv_shared_keep (MN'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (slMulNS_ok h7 hs₁ kN₁ (o := DM) (a := D) (b := R2N) (by decide)
    (by decide) (by decide) (by decide) (by rw [r₁]; exact hr2lt)) fun s₂ ⟨k₂, lt₂, e₂⟩ => ?_)
  obtain hs₂ := k₂.scr hs₁
  obtain kN₂ := kN₁.keepShared (j := MN) (by decide) rfl rfl rfl rfl h7 hn k₂ (by decide) (by decide)
  obtain r₂ : sv c base s₂ R2N = sv c base s R2N :=
    (sv_shared_keep (MN'_n c) rfl h7 hn k₂ (by decide) (by decide) (by decide)).trans r₁
  obtain E₂ : sv c base s₂ E = sv c base s E :=
    (sv_shared_keep (MN'_n c) rfl h7 hn k₂ (by decide) (by decide) (by decide)).trans E₁
  obtain rm₂ : sv c base s₂ RM = sv c base s₁ RM := sv_shared_keep (MN'_n c) rfl h7 hn k₂ (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (slMulNS_ok h7 hs₂ kN₂ (o := EM) (a := E) (b := R2N) (by decide)
    (by decide) (by decide) (by decide) (by rw [r₂]; exact hr2lt)) fun s₃ ⟨k₃, lt₃, e₃⟩ => ?_)
  obtain rm₃ : sv c base s₃ RM = sv c base s₁ RM :=
    (sv_shared_keep (MN'_n c) rfl h7 hn k₃ (by decide) (by decide) (by decide)).trans rm₂
  obtain dm₃ : sv c base s₃ DM = sv c base s₂ DM := sv_shared_keep (MN'_n c) rfl h7 hn k₃ (by decide) (by decide) (by decide)
  refine h s₃ (k₃.scr hs₂) (kN₂.keepShared (j := MN) (by decide) rfl rfl rfl rfl h7 hn k₃ (by decide) (by decide))
    (fun r hr => by rw [k₃.gpr r hr, k₂.gpr r hr, k₁.gpr r hr]) (by rw [k₃.rd, k₂.rd, k₁.rd])
    (by rw [k₃.wr, k₂.wr, k₁.wr]) ?_ (by rw [rm₃]; exact lt₁) (by rw [dm₃]; exact lt₂) lt₃
    (by rw [rm₃, toM_r2 hnR (by rw [e₁, hr2])])
    (by rw [dm₃, toM_r2 hnR (by rw [e₂, r₁, hr2]), d₁])
    (by rw [toM_r2 hnR (by rw [e₃, r₂, hr2]), E₂])
  exact ((unch_shared_slots (MN'_n c) rfl k₁.unch (l := [62, RM, DM, EM, TT, SM, SS, TMP]) (by simp) (by simp) (by simp)).trans
    ((unch_shared_slots (MN'_n c) rfl k₂.unch (l := [62, RM, DM, EM, TT, SM, SS, TMP]) (by simp) (by simp) (by simp)).trans
    (unch_shared_slots (MN'_n c) rfl k₃.unch (l := [62, RM, DM, EM, TT, SM, SS, TMP]) (by simp) (by simp) (by simp)))).mono fun w hw => by
      simp only [List.mem_append, or_self] at hw
      exact hw

/-- The rest of the field operations: `s`, left Montgomery's form. -/
theorem scalarOut_ok (hc : BaseCfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    (hMN : ModOkW c.MN' size c.C.n s.mem base) (hone : sv c base s ONE = 1)
    (hdm : sv c base s DM < c.C.n) (hem : sv c base s EM < c.C.n)
    {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s', Scr s' base size → (∀ r, r ∉ clob c.n → s'.gpr r = s.gpr r) → s'.rd = s.rd →
      s'.wr = s.wr →
      Unch base ([62, RM, DM, EM, TT, SM, SS, TMP].map fun i => (c.sl i, 8 * c.n)) s.mem s'.mem →
      sv c base s' SS < c.C.n →
      Fin.ofNat c.C.n (sv c base s' SS) = toM c.C.n (2 ^ (64 * c.n)) (sv c base s ACC) *
        (toM c.C.n (2 ^ (64 * c.n)) (sv c base s RM) * toM c.C.n (2 ^ (64 * c.n)) (sv c base s DM) +
          toM c.C.n (2 ^ (64 * c.n)) (sv c base s EM)) →
      WP isa rest s' Q) :
    WP isa (.seq (opProg c.MNS (.mul (c.sl TT) (c.sl RM) (c.sl DM))).inline
      (.seq (.block (add c.MN' (c.sl TT) (c.sl TT) (c.sl EM)))
      (.seq (opProg c.MNS (.mul (c.sl SM) (c.sl ACC) (c.sl TT))).inline
      (.seq (opProg c.MNS (.mul (c.sl SS) (c.sl SM) (c.sl ONE))).inline rest)))) s Q := by
  have h7 := hc.n10
  have hn := hs.nowrap
  obtain hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  have hn3 := hc.n_ge
  refine WP.seq (WP.mono (slMulNS_ok h7 hs hMN (o := TT) (a := RM) (b := DM) (by decide)
    (by decide) (by decide) (by decide) hdm) fun s₁ ⟨k₁, lt₁, e₁⟩ => ?_)
  obtain hs₁ := k₁.scr hs
  obtain kN₁ := hMN.keepShared (j := MN) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  obtain em₁ : sv c base s₁ EM = sv c base s EM := sv_shared_keep (MN'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (slAdd_ok (MN'_n c) (MN'_tmp c) (MN'_mo c) h7 hs₁ kN₁ (o := TT) (a := TT) (b := EM) (by decide)
    (by decide) (by decide) (by decide) (by rw [em₁]; omega_arith)) fun s₂ ⟨k₂, e₂⟩ => ?_)
  obtain hs₂ := k₂.scr hs₁
  obtain kN₂ := kN₁.keep (j := MN) (by decide) rfl rfl rfl rfl h7 hn k₂ (by decide) (by decide)
  obtain acc₂ : sv c base s₂ ACC = sv c base s ACC := by
    rw [sv_keep (MN'_n c) rfl h7 hn k₂ (by decide) (by decide) (by decide),
      sv_shared_keep (MN'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)]
  obtain one₂ : sv c base s₂ ONE = 1 := by
    rw [sv_keep (MN'_n c) rfl h7 hn k₂ (by decide) (by decide) (by decide),
      sv_shared_keep (MN'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide), hone]
  obtain tt₂ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₂ TT) =
      toM c.C.n (2 ^ (64 * c.n)) (sv c base s RM) * toM c.C.n (2 ^ (64 * c.n)) (sv c base s DM) +
        toM c.C.n (2 ^ (64 * c.n)) (sv c base s EM) := by
    rw [e₂, toM_add, toM_mul hnR e₁, em₁]
  obtain ttlt : sv c base s₂ TT < c.C.n := by rw [e₂]; exact Nat.mod_lt _ (by omega_arith)
  refine WP.seq (WP.mono (slMulNS_ok h7 hs₂ kN₂ (o := SM) (a := ACC) (b := TT) (by decide)
    (by decide) (by decide) (by decide) ttlt) fun s₃ ⟨k₃, _, e₃⟩ => ?_)
  obtain hs₃ := k₃.scr hs₂
  obtain kN₃ := kN₂.keepShared (j := MN) (by decide) rfl rfl rfl rfl h7 hn k₃ (by decide) (by decide)
  obtain one₃ : sv c base s₃ ONE = 1 :=
    (sv_shared_keep (MN'_n c) rfl h7 hn k₃ (by decide) (by decide) (by decide)).trans one₂
  refine WP.seq (WP.mono (slMulNS_ok h7 hs₃ kN₃ (o := SS) (a := SM) (b := ONE) (by decide)
    (by decide) (by decide) (by decide) (by omega_arith)) fun s₄ ⟨k₄, lt₄, e₄⟩ => ?_)
  refine h s₄ (k₄.scr hs₃) (fun r hr => by rw [k₄.gpr r hr, k₃.gpr r hr, k₂.gpr r hr, k₁.gpr r hr])
    (by rw [k₄.rd, k₃.rd, k₂.rd, k₁.rd]) (by rw [k₄.wr, k₃.wr, k₂.wr, k₁.wr]) ?_ lt₄ ?_
  · exact (((unch_shared_slots (MN'_n c) rfl k₁.unch (l := [62, RM, DM, EM, TT, SM, SS, TMP]) (by simp) (by simp) (by simp)).trans
      (unch_slots (MN'_n c) rfl k₂.unch (l := [62, RM, DM, EM, TT, SM, SS, TMP]) (by simp) (by simp))).trans
      ((unch_shared_slots (MN'_n c) rfl k₃.unch (l := [62, RM, DM, EM, TT, SM, SS, TMP]) (by simp) (by simp) (by simp)).trans
      (unch_shared_slots (MN'_n c) rfl k₄.unch (l := [62, RM, DM, EM, TT, SM, SS, TMP]) (by simp) (by simp) (by simp)))).mono fun w hw => by
        simp only [List.mem_append, or_self] at hw
        exact hw
  · rw [toM_one_mul hnR (by rw [e₄, one₃]), toM_mul hnR e₃, acc₂, tt₂]

end VG.Proof.Ecdsa.X86_64

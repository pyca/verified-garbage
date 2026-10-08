import VerifiedGarbage.Impl.Aes.X86_64.VaesZH
import VerifiedGarbage.Proof.Aes.X86_64.VaesZ.Rounds
import VerifiedGarbage.Proof.Framework.X86_64.HighRegs

/-! # AES rounds using the cached high-register keys -/

namespace VG.Proof.Aes.X86_64.VaesZH

open VG.X86_64
open VG.Impl.Aes.X86_64.VaesZH

/-- Each block register receives one round using its corresponding key lane. -/
theorem keyOp_ok (op : ZKeyOp) (kr : HReg) : ∀ (regs : List XReg) (s : State), regs.Nodup →
    WP isa (.block (keyOp kr regs op)) s fun s' =>
      (∀ b ∈ regs, ∀ l < 4, s'.zlane b l = op.sse.eval (s.zlane b l) (s.zlaneH kr l)) ∧
      ZFrame regs s s' ∧ HKeep s s'
  | [], s, _ => WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, ZFrame.refl _ _, HKeep.refl _⟩
  | b :: bs, s, hnd => by
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    rw [keyOp, List.map_cons, WP.block_cons_iff]
    refine ⟨(ZOp.zbinH op b b kr).exec s, rfl, ?_⟩
    refine WP.mono (keyOp_ok op kr bs _ (List.nodup_cons.mp hnd).2) fun s' ⟨hv, hf, hh⟩ =>
      ⟨?_, ?_, (HKeep.zop _ _).trans hh⟩
    · intro c hc l hl
      rcases List.mem_cons.mp hc with rfl | hc
      · rw [hf.zlane _ hbs l hl, zlane_zbinH _ _ _ _ _ _ hl]; simp
      · have hcb : c ≠ b := fun h => hbs (h ▸ hc)
        rw [hv c hc l hl, zlane_zbinH _ _ _ _ _ _ hl, (HKeep.zop _ _).lane kr l]
        simp [hcb]
    · refine ⟨by rw [hf.gpr]; simp, by rw [hf.mem]; simp, by rw [hf.rd]; simp,
        by rw [hf.wr]; simp, fun r hr l hl => ?_⟩
      simp only [List.mem_cons, not_or] at hr
      rw [hf.zlane r hr.2 l hl, zlane_zbinH _ _ _ _ _ _ hl]; simp [hr.1]

/-- The ordinary low-register frame, together with preservation of the cache. -/
structure KFrame (rs : List XReg) (s s' : State) : Prop extends ZFrame rs s s', HKeep s s'

theorem KFrame.refl (rs : List XReg) (s : State) : KFrame rs s s :=
  ⟨ZFrame.refl _ _, HKeep.refl _⟩

theorem KFrame.trans {rs : List XReg} {s t u : State} (h : KFrame rs s t) (h' : KFrame rs t u) :
    KFrame rs s u := ⟨h.toZFrame.trans h'.toZFrame, h.toHKeep.trans h'.toHKeep⟩

theorem KFrame.mono {rs rs' : List XReg} {s t : State} (h : KFrame rs s t)
    (hs : ∀ r ∈ rs, r ∈ rs') : KFrame rs' s t := ⟨h.toZFrame.mono hs, h.toHKeep⟩

/-- The schedule in memory, and the copies used by the cached rounds. -/
structure Keys (nr : Nat) (w : List Byte) (s : State) : Prop where
  base : VG.Proof.Aes.X86_64.AesNi.Keys nr w s
  inner : ∀ j < nr, j < 14 → ∀ l < 4, s.zlaneH (keyReg j) l =
    s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (16 * j)) 128
  last : ∀ l < 4, s.zlaneH .xmm31 l =
    s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (16 * nr)) 128

theorem KFrame.of_keys {nr : Nat} {w : List Byte} {rs : List XReg} {s t : State}
    (h : Keys nr w s) (hf : KFrame rs s t) : Keys nr w t :=
  ⟨VaesZ.ZFrame.of_keys h.base hf.toZFrame,
    fun j hj h14 l hl => by rw [hf.toHKeep.lane, hf.mem, hf.gpr]; exact h.inner j hj h14 l hl,
    fun l hl => by rw [hf.toHKeep.lane, hf.mem, hf.gpr]; exact h.last l hl⟩

open VG.Proof.Aes.X86_64.AesNi (st rnds rnds_zero rnds_succ cipher_eq
  ea_at ofInt_natCast byte_roundKey pxor_st aesenc_st aesenclast_st)
open VG.Proof.Aes.X86_64.VaesZ (RInv mem_kr_l mem_kr_r)
open VG.Spec.Aes (roundKey cipher)
open VG.Impl.Aes.X86_64.AesNi (at_)

/-- A cached key operation, expressed with the corresponding schedule word. -/
theorem keyOpMem_ok (kr : XReg) (kh : HReg) (regs : List XReg) (op : ZKeyOp)
    (a : Addr) (s : State) (hnd : regs.Nodup)
    (hkey : ∀ l < 4, s.zlaneH kh l = s.mem.readW a 128) :
    WP isa (.block (keyOp kh regs op)) s fun s' =>
      (∀ b ∈ regs, ∀ l < 4, s'.zlane b l = op.sse.eval (s.zlane b l) (s.mem.readW a 128)) ∧
      KFrame (kr :: regs) s s' :=
  WP.mono (keyOp_ok op kh regs s hnd) fun _ ⟨hv, hf, hh⟩ =>
    ⟨fun b hb l hl => by rw [hv b hb l hl, hkey l hl],
      hf.mono (fun _ h => List.mem_cons_of_mem _ h), hh⟩

theorem roundZ_ok (kr : XReg) (regs : List XReg) (hnd : regs.Nodup) (_h8 : kr ∉ regs) {nr : Nat}
    {w : List Byte} {x : XReg → Nat → Spec.Aes.State} {k : Nat} (hk : k + 1 < nr) (h14 : k + 1 < 14)
    {s : State} (hK : Keys nr w s) (hI : RInv regs w x k s) :
    WP isa (.block (round regs (k + 1))) s fun s' =>
      RInv regs w x (k + 1) s' ∧ KFrame (kr :: regs) s s' := by
  refine WP.mono (keyOpMem_ok kr (keyReg (k + 1)) regs .vaesenc _ s hnd (hK.inner _ hk h14))
    fun s' ⟨hv, hf⟩ => ⟨fun b hb l hl => ?_, hf⟩
  rw [hv b hb l hl]
  show st (XBinOp.eval .aesenc _ _) = _
  rw [aesenc_st _ _ (roundKey w (k + 1)) (by
    rw [hK.base.sched]; exact byte_roundKey _ _ (by omega)), hI b hb l hl, rnds_succ]
/-- Rounds 1 to `k` (at most 9), with `g j` after round `j`. -/
theorem roundsZ_ok (kr : XReg) (regs : List XReg) (hnd : regs.Nodup) (h8 : kr ∉ regs) {nr : Nat}
    {w : List Byte} {x : XReg → Nat → Spec.Aes.State} (g : Nat → List Instr) (G : List XReg)
    (hG : ∀ r ∈ G, r ∉ regs) (Q : Nat → State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys nr w s → Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧ KFrame G s s')
    (hq : ∀ j s s', Q j s → KFrame (kr :: regs) s s' → Q j s')
    (k : Nat) (s : State) (hk : k ≤ 9) (hnr : 9 < nr) (hK : Keys nr w s) (hI : RInv regs w x 0 s)
    (hQ : Q 1 s) :
    WP isa (.block ((List.range k).flatMap fun j => round regs (j + 1) ++ g (j + 1))) s fun s' =>
      RInv regs w x k s' ∧ Q (k + 1) s' ∧ KFrame (kr :: (regs ++ G)) s s' := by
  induction k with
  | zero =>
    rw [List.range_zero, List.flatMap_nil]; exact WP.block_nil ⟨hI, hQ, KFrame.refl _ _⟩
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ ⟨hI₁, hQ₁, hf₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [WP.block_append_iff]
    refine WP.mono (roundZ_ok kr regs hnd h8 (k := k) (by omega) (by omega) (KFrame.of_keys hK hf₁) hI₁)
      fun s₂ ⟨hI₂, hf₂⟩ => ?_
    refine WP.mono (hg (k + 1) (by omega) (by omega) s₂ (KFrame.of_keys (KFrame.of_keys hK hf₁) hf₂)
      (hq _ _ _ hQ₁ hf₂)) fun s' ⟨hQ', hf'⟩ => ⟨fun b hb l hl => ?_, hQ', ?_⟩
    · rw [hf'.zlane b (fun h => hG b h hb) l hl]; exact hI₂ b hb l hl
    · exact hf₁.trans ((hf₂.mono fun _ => mem_kr_l).trans
        (hf'.mono fun _ => mem_kr_r))

theorem cmpRsiZ_ok (s : State) (c : BitVec 32) (nr : Nat) (hrsi : s.gpr .rsi = BitVec.ofNat 64 nr) :
    WP isa (.block [.alu .cmp .rsi (.imm c)]) s fun s' =>
      s'.zf = some (BitVec.ofNat 64 nr - c.signExtend 64 == 0) ∧ KFrame [] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags,
    State.setFlags, isa, hrsi, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩, rfl, rfl⟩

theorem aes_ok (kr : XReg) (regs : List XReg) (hnd : regs.Nodup) (h8 : kr ∉ regs) {nr : Nat}
    (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14) {w : List Byte} (g : Nat → List Instr) (G : List XReg)
    (hG : ∀ r ∈ G, r ∉ regs) (Q : Nat → State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys nr w s → Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧ KFrame G s s')
    (hq : ∀ j s s', Q j s → KFrame (kr :: regs) s s' → Q j s')
    (s : State) (hK : Keys nr w s) (hQ : Q 1 s)
    (hrsi : s.gpr .rsi = BitVec.ofNat 64 nr)
    (_hr10 : s.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * nr)) :
    WP isa (aes regs g) s fun s' =>
      (∀ b ∈ regs, ∀ l < 4, st (s'.zlane b l) = cipher nr w (st (s.zlane b l))) ∧ Q 10 s' ∧
      KFrame (kr :: (regs ++ G)) s s' := by
  let x : XReg → Nat → Spec.Aes.State := fun b l => st (s.zlane b l)
  have k0 := byte_roundKey s.mem (s.gpr .rdi) (L := 16 * (nr + 1)) (j := 0) (by omega)
  simp only [Nat.mul_zero] at k0
  -- `AddRoundKey` and rounds 1–9.
  have h₁ : WP isa (.block (keyOp (keyReg 0) regs .vpxord ++
      (List.range 9).flatMap fun j => round regs (j + 1) ++ g (j + 1))) s fun s' =>
      RInv regs w x 9 s' ∧ Q 10 s' ∧ KFrame (kr :: (regs ++ G)) s s' := by
    rw [WP.block_append_iff]
    refine WP.mono (keyOpMem_ok kr (keyReg 0) regs .vpxord _ s hnd
      (hK.inner 0 (by rcases hnr with h | h | h <;> omega) (by decide)))
      fun s₁ ⟨hv₁, hf₁⟩ => ?_
    have hI₁ : RInv regs w x 0 s₁ := fun b hb l hl => by
      rw [hv₁ b hb l hl]
      show st (XBinOp.eval .pxor _ _) = _
      rw [pxor_st _ _ (roundKey w 0) (by rw [hK.base.sched]; exact k0), rnds_zero]
    exact WP.mono (roundsZ_ok kr regs hnd h8 g G hG Q hg hq 9 s₁ (by omega) (by omega)
        (KFrame.of_keys hK hf₁) hI₁ (hq _ _ _ hQ hf₁))
      fun s' ⟨hI', hQ', hf'⟩ => ⟨hI', hQ', (hf₁.mono fun _ => mem_kr_l).trans hf'⟩
  have keep : ∀ {s₁ s₂ : State} {k : Nat}, RInv regs w x k s₁ → KFrame [] s₁ s₂ →
      RInv regs w x k s₂ :=
    fun hI hf b hb l hl => by rw [hf.zlane b (by simp) l hl]; exact hI b hb l hl
  -- Rounds 10 to `nr - 1`.
  have keepQ : ∀ {s₁ s₂ : State}, Q 10 s₁ → KFrame (kr :: regs) s₁ s₂ → Q 10 s₂ :=
    fun h hf => hq _ _ _ h hf
  have h₂ : ∀ s₁, RInv regs w x 9 s₁ → Q 10 s₁ → KFrame (kr :: (regs ++ G)) s s₁ →
      s₁.zf = some (BitVec.ofNat 64 nr - (10 : BitVec 32).signExtend 64 == 0) →
      WP isa (.ite .e (.block [])
        (.seq (.block (round regs 10 ++ round regs 11 ++ [.alu .cmp .rsi (.imm 12)]))
          (.ite .e (.block []) (.block (round regs 12 ++ round regs 13))))) s₁ fun s' =>
        RInv regs w x (nr - 1) s' ∧ Q 10 s' ∧ KFrame (kr :: (regs ++ G)) s s' := by
    intro s₁ hI₁ hQ₁ hf₁ hz₁
    have hK₁ := KFrame.of_keys hK hf₁
    have hrsi₁ : s₁.gpr .rsi = BitVec.ofNat 64 nr := by rw [hf₁.gpr, hrsi]
    rcases hnr with rfl | rfl | rfl
    · exact WP.ite true (by simp [eval, hz₁]) (fun _ => WP.block_nil ⟨hI₁, hQ₁, hf₁⟩)
        (fun h => absurd h (by decide))
    all_goals
      refine WP.ite false (by simp [eval, hz₁]) (fun h => absurd h (by decide)) fun _ => ?_
      refine WP.seq ?_
      rw [WP.block_append_iff, WP.block_append_iff]
      refine WP.mono (roundZ_ok kr regs hnd h8 (k := 9) (by omega) (by omega) hK₁ hI₁) fun s₂ ⟨hI₂, hf₂⟩ => ?_
      refine WP.mono (roundZ_ok kr regs hnd h8 (k := 10) (by omega) (by omega) (KFrame.of_keys hK₁ hf₂) hI₂)
        fun s₃ ⟨hI₃, hf₃⟩ => ?_
      have hrsi₃ : s₃.gpr .rsi = s₁.gpr .rsi := by rw [hf₃.gpr, hf₂.gpr]
      refine WP.mono (cmpRsiZ_ok s₃ 12 _ (hrsi₃.trans hrsi₁)) fun s₄ ⟨hz₄, hf₄⟩ => ?_
      have hQ₄ : Q 10 s₄ := keepQ (keepQ (keepQ hQ₁ hf₂) hf₃) (hf₄.mono (by simp))
      have hf₂₄ : KFrame (kr :: regs) s₁ s₄ := hf₂.trans (hf₃.trans (hf₄.mono (by simp)))
      have hf₁₄ := hf₁.trans (hf₂₄.mono fun _ => mem_kr_l)
    · exact WP.ite true (by simp [eval, hz₄]) (fun _ => WP.block_nil ⟨keep hI₃ hf₄, hQ₄, hf₁₄⟩)
        (fun h => absurd h (by decide))
    · refine WP.ite false (by simp [eval, hz₄]) (fun h => absurd h (by decide)) fun _ => ?_
      rw [WP.block_append_iff]
      have hK₄ := KFrame.of_keys hK₁ (hf₂.trans (hf₃.trans (hf₄.mono (by simp))))
      refine WP.mono (roundZ_ok kr regs hnd h8 (k := 11) (by omega) (by omega) hK₄ (keep hI₃ hf₄))
        fun s₅ ⟨hI₅, hf₅⟩ => ?_
      exact WP.mono (roundZ_ok kr regs hnd h8 (k := 12) (by omega) (by omega) (KFrame.of_keys hK₄ hf₅) hI₅)
        fun s' ⟨hI', hf'⟩ => ⟨hI', keepQ (keepQ hQ₄ hf₅) hf', hf₁₄.trans ((hf₅.trans hf').mono fun _ => mem_kr_l)⟩
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono h₁ fun s₁ ⟨hI₁, hQ₁, hf₁⟩ => ?_
  refine WP.mono (cmpRsiZ_ok s₁ 10 nr (by rw [hf₁.gpr, hrsi])) fun s₁' ⟨hz₁, hf₁'⟩ => ?_
  have hf₁₁ := hf₁.trans (hf₁'.mono (by simp))
  refine WP.seq (WP.mono (h₂ s₁' (keep hI₁ hf₁') (keepQ hQ₁ (hf₁'.mono (by simp))) hf₁₁ hz₁)
    fun s₂ ⟨hI₂, hQ₂, hf₂⟩ => ?_)
  have hK₂ := KFrame.of_keys hK hf₂
  refine WP.mono (keyOpMem_ok kr .xmm31 regs .vaesenclast _ s₂ hnd hK₂.last)
    fun s' ⟨hv, hf'⟩ => ⟨fun b hb l hl => ?_, keepQ hQ₂ hf', hf₂.trans (hf'.mono fun _ => mem_kr_l)⟩
  rw [hv b hb l hl]
  show st (XBinOp.eval .aesenclast _ _) = _
  rw [aesenclast_st _ _ (roundKey w nr) (by
    rw [hK₂.base.sched]; exact byte_roundKey _ _ (by omega)), hI₂ b hb l hl, cipher_eq]

/-- A write outside the schedule does not invalidate cached round keys.
The two memory-key facts establish equality of every schedule word. -/
theorem Keys.keep {nr : Nat} {w : List Byte} {s t : State} (h : Keys nr w s)
    (hh : HKeep s t) (hb : VG.Proof.Aes.X86_64.AesNi.Keys nr w t) : Keys nr w t := by
  have eqkey : ∀ j ≤ nr,
      s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (16 * j)) 128 =
      t.mem.readW (t.gpr .rdi + BitVec.ofNat 64 (16 * j)) 128 := by
    intro j hj
    apply VG.Proof.Gcm.X86_64.ext_byte
    intro i hi
    have hs := byte_roundKey s.mem (s.gpr .rdi) (L := 16 * (nr + 1)) (j := j) (by omega) i hi
    have ht := byte_roundKey t.mem (t.gpr .rdi) (L := 16 * (nr + 1)) (j := j) (by omega) i hi
    rw [← h.base.sched, BitVec.ofInt_natCast] at hs
    rw [← hb.sched, BitVec.ofInt_natCast] at ht
    exact hs.trans ht.symm
  exact ⟨hb, fun j hj h14 l hl => (hh.lane _ _).trans ((h.inner j hj h14 l hl).trans (eqkey j (by omega))),
    fun l hl => (hh.lane _ _).trans ((h.last l hl).trans (eqkey nr (Nat.le_refl _)))⟩

end VG.Proof.Aes.X86_64.VaesZH

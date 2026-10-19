module

public import VerifiedGarbage.Proof.Blowfish.ModeBytes
public import VerifiedGarbage.Proof.Modes.X86_64.FbLoop
public import VerifiedGarbage.Proof.Modes.X86_64.KeepGpr
public import VerifiedGarbage.Impl.Blowfish.X86_64.Modes
import VerifiedGarbage.Proof.Blowfish.Blocks
import VerifiedGarbage.Proof.Blowfish.X86_64.Block
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Modes.X86_64.Steps
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Blowfish.X86_64.Ecb
import VerifiedGarbage.Proof.Framework.Taint

/-!
# Blowfish's core for the modes on x86-64

`dirCoreSpec up`: Blowfish's core (`Impl.Blowfish.X86_64.dirCore up`) meets
what the modes need of a core of one-word blocks
(`Proof.Modes.X86_64.BlockSpec`), with the key a schedule, its cipher
encryption (`up`) or decryption (`dirCipher`), and the key ready when the
schedule is at `rdi`, readable and outside every writable region (`SchedAt`),
where nothing the modes or the core write can reach it. `crypt` is the ECB
functions' block code (`loadBlock_run`, `cipher_run`, `storeBlock_run`) on
the buffer.

`crypt_keepsIv`: `crypt` keeps `xmm15`, its upper half zero, which it puts
back from `r14` after the block code, which keeps `r14` (`gprSafe`).
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Blowfish.X86_64 VG.Spec.Blowfish VG.Proof.Blowfish
open VG.Impl.Aes.X86_64 (sb movR)
open VG.Proof.Modes.X86_64 (ScrIn WrIn coreRegion blkRegion blkAddr BlockSpec KeepsIv movR_ok addImm_ok
  signExtend_small gprSafe keepsGpr_of_gprSafe)

/-- The 16 bytes of working space, with the scratch buffer at `B`. -/
abbrev wsAddr (B : Addr) : Addr := B + BitVec.ofNat 64 (8 * wsSlot)

/-- The schedule at `p`: readable, within the address space, and outside
every writable region. -/
structure SchedAt (s : State) (p : Addr) : Prop where
  rd : (⟨p, 4168⟩ : Region) ∈ s.rd
  fit : p.toNat + 4168 ≤ 2 ^ 64
  sep : ∀ w ∈ s.wr, Region.Disjoint ⟨p, 4168⟩ w

theorem SchedAt.congr {s s' : State} {p : Addr} (h : SchedAt s p) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    SchedAt s' p :=
  ⟨by rw [hrd]; exact h.rd, h.fit, by rw [hwr]; exact h.sep⟩

/-- The schedule at `rdi`, outside the regions `rs` and every writable one. -/
def ModeKeyArgs (s : State) (rs : List Region) (k : Schedule) : Prop :=
  ∃ p : Addr, s.gpr .rdi = p ∧ k = scheduleAt s.mem p ∧ SchedAt s p ∧ ∀ r ∈ rs, Region.Disjoint ⟨p, 4168⟩ r

/-- The schedule at `rdi` is `k`. -/
def ReadyAt (s : State) (k : Schedule) : Prop :=
  ∃ p : Addr, s.gpr .rdi = p ∧ scheduleAt s.mem p = k ∧ SchedAt s p

@[simp] theorem dirCore_bw (up : Bool) : (dirCore up).bw = 1 := rfl

theorem core_eq (up : Bool) (B : Addr) : coreRegion (dirCore up) B = ⟨B, 24⟩ := rfl
theorem total_eq (up : Bool) : (dirCore up).total = 11 := rfl

theorem buf_ws (B : Addr) : Region.Disjoint ⟨B, 8⟩ ⟨wsAddr B, 16⟩ := by
  have : Region.Disjoint ⟨B + BitVec.ofNat 64 0, 8⟩ ⟨wsAddr B, 16⟩ := Offset.disjoint B (.inl (by decide)) (by decide) (by decide)
  rwa [BitVec.add_zero] at this

theorem rdi_not_mode (up : Bool) : Reg.rdi ∉ Modes.X86_64.modeRegs (dirCore up) := by
  simp only [Modes.X86_64.modeRegs, dirCore]; decide

theorem ready_frame {up : Bool} {s s' : State} {k : Schedule} {rs : List Region} (h : ReadyAt s k)
    (hf : Frame rs s.mem s'.mem) (hw : WrIn rs s s')
    (hg : ∀ r, r ∉ Modes.X86_64.modeRegs (dirCore up) → s'.gpr r = s.gpr r) : ReadyAt s' k := by
  obtain ⟨p, hp, hk, hS⟩ := h
  refine ⟨p, by rw [hg _ (rdi_not_mode up), hp], ?_, hS.congr hw.rd hw.wr⟩
  rw [scheduleAt_eq_of_frame _ hf fun r hr => ?_, hk]
  obtain ⟨w, hw', hsub⟩ := hw.sub r hr
  exact (hS.sep w hw').sub_right hsub

theorem keyArgs_congr {s s' : State} {rs : List Region} {k : Schedule} (h : ModeKeyArgs s rs k)
    (hr : ∀ r ∈ [Reg.rdi], s'.gpr r = s.gpr r) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hf : Frame rs s.mem s'.mem) : ModeKeyArgs s' rs k := by
  obtain ⟨p, hp, hk, hS, hdis⟩ := h
  refine ⟨p, by rw [hr .rdi List.mem_cons_self, hp], ?_, hS.congr hrd hwr, hdis⟩
  rw [hk]
  exact (scheduleAt_eq_of_frame _ hf hdis).symm

theorem prepare_wp {up : Bool} {s : State} {B : Addr} {rs : List Region} {k : Schedule}
    (hB : s.gpr sb = B) (_ : ScrIn s B (dirCore up).total) (_ : (⟨B, 8 * (dirCore up).total⟩ : Region) ∈ rs)
    (hk : ModeKeyArgs s rs k) :
    WP isa (dirCore up).prepare s fun s' => ReadyAt s' k ∧ s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr .r12 = s.gpr .r12 ∧ s'.gpr .r13 = s.gpr .r13 ∧
      Frame [coreRegion (dirCore up) B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hp, hk, hS, -⟩ := hk
  exact WP.block_nil ⟨⟨p, hp, hk.symm, hS⟩, hB, rfl, rfl, rfl, Frame.refl _ _, rfl, rfl⟩

theorem saveIv_run (s : State) :
    ∃ s', runBlock isa saveIv s = some s' ∧ (∀ g, g ≠ .r14 → s'.gpr g = s.gpr g) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨s.setReg .r14 ((s.xmm .xmm15).extractLsb' 0 64), by simp only [saveIv, runBlock_cons, runStep_some,
    runBlock_nil, exec], fun _ h => gpr_setReg_of_ne _ _ h, rfl, rfl, rfl⟩

theorem restoreIv_run (s : State) :
    ∃ s', runBlock isa restoreIv s = some s' ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  ⟨(XOp.movq .xmm15 .r14).exec s, by simp only [restoreIv, runBlock_cons, runStep_some, runBlock_nil, exec],
    rfl, rfl, rfl, rfl⟩

/-- The scratch buffer's bytes `t` to `t + n`, within the writable regions. -/
theorem inScr {s : State} {B : Addr} (hw : (⟨B, 8 * 11⟩ : Region) ∈ s.wr)
    {t n : Nat} (ht : t + n ≤ 8 * 11) : InRegions s.wr (B + BitVec.ofNat 64 t) n :=
  ⟨_, hw, Offset.contains_base B ht (by omega)⟩

theorem inScr' {s : State} {B : Addr} (hw : (⟨B, 8 * 11⟩ : Region) ∈ s.wr)
    {t n : Nat} (ht : t + n ≤ 8 * 11) : InRegions (s.rd ++ s.wr) (B + BitVec.ofNat 64 t) n := by
  obtain ⟨r, h1, h2⟩ := inScr hw ht; exact ⟨r, List.mem_append_right _ h1, h2⟩

theorem crypt_wp {up : Bool} {s : State} {B : Addr} {k : Schedule} (hB : s.gpr sb = B)
    (hs : ScrIn s B (dirCore up).total) (hr : ReadyAt s k) :
    WP isa (dirCore up).crypt s fun s' => s'.gpr sb = B ∧ s'.gpr .rsp = s.gpr .rsp ∧
      s'.gpr .r12 = s.gpr .r12 ∧ s'.gpr .r13 = s.gpr .r13 ∧ ReadyAt s' k ∧
      Frame [coreRegion (dirCore up) B] s.mem s'.mem ∧
      (∀ j < (dirCore up).G, Spec.Aes.bytesAt s'.mem (blkAddr (dirCore up) B j) (8 * (dirCore up).bw) =
        dirCipher up k (Spec.Aes.bytesAt s.mem (blkAddr (dirCore up) B j) (8 * (dirCore up).bw))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨p, hp, hK, hS⟩ := hr
  have hw := hs.wr
  rw [total_eq] at hw
  -- `xmm15` to `r14`.
  obtain ⟨s₁, e₁, g₁, m₁, rd₁, wr₁⟩ := saveIv_run s
  show WP isa (cryptCode up) s _
  apply WP.seq
  refine WP.of_runBlock ⟨s₁, e₁, ?_⟩
  -- The setup.
  obtain ⟨t₁, f₁, r₁, o₁, n₁, d₁, w₁⟩ := movR_ok s₁ .rdx sb
  obtain ⟨t₂, f₂, r₂, o₂, n₂, d₂, w₂⟩ := movR_ok t₁ .rsi sb
  obtain ⟨t₃, f₃, r₃, o₃, n₃, d₃, w₃⟩ := movR_ok t₂ .rcx sb
  obtain ⟨t₄, f₄, r₄, o₄, n₄, d₄, w₄⟩ := addImm_ok t₃ .rcx (BitVec.ofNat 32 (8 * wsSlot))
  obtain ⟨t₅, f₅, x₅a, x₅b, x₅c, x₅d, g₅, u₅⟩ := constants_run t₄
  have sb₁ : s₁.gpr sb = B := by rw [g₁ _ (by decide), hB]
  have mem₅ : t₅.mem = s.mem := by rw [u₅, n₄, n₃, n₂, n₁, m₁]
  have rd₅ : t₅.rd = s.rd := by rw [u₅, d₄, d₃, d₂, d₁, rd₁]
  have wr₅ : t₅.wr = s.wr := by rw [u₅, w₄, w₃, w₂, w₁, wr₁]
  have rsi₅ : t₅.gpr .rsi = B := by
    rw [g₅ _ (by decide), o₄ _ (by decide), o₃ _ (by decide), r₂, o₁ _ (by decide), sb₁]
  obtain ⟨t₆, f₆, l₆a, l₆b, k₆, g₆, u₆⟩ := loadBlock_run t₅ B rsi₅ fun o ho => by
    rw [rd₅, wr₅]; exact inScr' (s := s) hw (by omega)
  have mem₆ : t₆.mem = s.mem := by rw [u₆, mem₅]
  have rd₆ : t₆.rd = s.rd := by rw [u₆, rd₅]
  have wr₆ : t₆.wr = s.wr := by rw [u₆, wr₅]
  have g₆' : ∀ g, g ≠ .rdx → g ≠ .rsi → g ≠ .rcx → g ≠ .r11 → t₆.gpr g = s₁.gpr g :=
    fun g h1 h3 h4 h5 => by rw [g₆ _ h5, g₅ _ h5, o₄ _ h4, o₃ _ h4, o₂ _ h3, o₁ _ h1]
  have rdx₆ : t₆.gpr .rdx = B := by
    rw [g₆ _ (by decide), g₅ _ (by decide), o₄ _ (by decide), o₃ _ (by decide), o₂ _ (by decide), r₁, sb₁]
  have rdi₆ : t₆.gpr .rdi = p := by
    rw [g₆' _ (by decide) (by decide) (by decide) (by decide), g₁ _ (by decide), hp]
  have rsi₆ : t₆.gpr .rsi = B := by rw [g₆ _ (by decide), rsi₅]
  have rcx₆ : t₆.gpr .rcx = wsAddr B := by
    rw [g₆ _ (by decide), g₅ _ (by decide), r₄, r₃, o₂ _ (by decide), o₁ _ (by decide), sb₁,
      signExtend_small (by decide)]
  apply WP.seq
  refine WP.of_runBlock ⟨t₆, cat_run (cat_run (cat_run f₁ (cat_run f₂ (cat_run f₃ f₄))) f₅) f₆, ?_⟩
  -- The rounds.
  have inSch : ∀ off n, off + n ≤ 4168 → InRegions (t₆.rd ++ t₆.wr) (p + BitVec.ofNat 64 off) n :=
    fun off n h => ⟨_, List.mem_append_left _ (by rw [rd₆]; exact hS.rd), Offset.contains_base p h (by omega)⟩
  have CE : CipherEnv .rdi p t₆ := by
    refine ⟨⟨rdi₆, by decide, by decide, by decide, fun off h => inSch off 16 (by omega),
      by rw [k₆ _ (by decide) (by decide), x₅a], by rw [k₆ _ (by decide) (by decide), x₅b],
      by rw [k₆ _ (by decide) (by decide), x₅c]⟩, by decide, by decide, fun i hi => inSch _ 4 (by omega)⟩
  apply WP.seq
  refine WP.mono (cipher_run CE up) fun t₇ ⟨c₁, c₂, O⟩ => ?_
  have mem₇ : t₇.mem = s.mem := by rw [O.upd, mem₆]
  have rd₇ : t₇.rd = s.rd := by rw [O.upd, rd₆]
  have wr₇ : t₇.wr = s.wr := by rw [O.upd, wr₆]
  have g₇ : ∀ g, g ≠ .rax → g ≠ .r8 → g ≠ .r9 → g ≠ .r10 → g ≠ .r11 → t₇.gpr g = t₆.gpr g := O.gpr
  -- The block out, and `sb` back.
  have SE : StoreEnv B (wsAddr B) t₇ := by
    refine ⟨by rw [g₇ _ (by decide) (by decide) (by decide) (by decide) (by decide), rsi₆],
      by rw [g₇ _ (by decide) (by decide) (by decide) (by decide) (by decide), rcx₆],
      by rw [wr₇, show B = B + BitVec.ofNat 64 0 by simp]; exact inScr hw (by decide),
      by rw [wr₇]; exact inScr hw (by simp only [wsSlot]; omega),
      sep_of_disjoint (buf_ws B), sep_of_disjoint (buf_ws B).symm⟩
  obtain ⟨t₈, f₈, b₈, fr₈, g₈, e₈⟩ := storeBlock_run SE
  obtain ⟨t₉, f₉, r₉, o₉, n₉, d₉, w₉⟩ := movR_ok t₈ sb .rdx
  apply WP.seq
  refine WP.of_runBlock ⟨t₉, cat_run f₈ f₉, ?_⟩
  obtain ⟨t₁₀, f₁₀, g₁₀, n₁₀, d₁₀, w₁₀⟩ := restoreIv_run t₉
  refine WP.of_runBlock ⟨t₁₀, f₁₀, ?_⟩
  have mem₁₀ : t₁₀.mem = t₈.mem := by rw [n₁₀, n₉]
  have fr : Frame [⟨B, 8⟩, ⟨wsAddr B, 16⟩] s.mem t₁₀.mem := by rw [mem₁₀, ← mem₇]; exact fr₈
  have sub : Region.Sub ⟨B, 8⟩ ⟨B, 8 * 11⟩ ∧ Region.Sub ⟨wsAddr B, 16⟩ ⟨B, 8 * 11⟩ :=
    ⟨Region.sub_prefix (by decide), Offset.sub_base B (by simp only [wsSlot]; omega)⟩
  have kp : ∀ g, g ≠ .r14 → g ≠ .rdx → g ≠ .rsi → g ≠ .rcx → g ≠ .rax → g ≠ .r8 →
      g ≠ .r9 → g ≠ .r10 → g ≠ .r11 → t₁₀.gpr g = s.gpr g := fun g h1 h3 h5 h6 h7 h8 h9 h10 h11 => by
    rw [g₁₀, o₉ _ h9, g₈ _ h11, g₇ _ h7 h8 h9 h10 h11, g₆' _ h3 h5 h6 h11, g₁ _ h1]
  have rd₁₀ : t₁₀.rd = s.rd := by rw [d₁₀, d₉, e₈, rd₇]
  have wr₁₀ : t₁₀.wr = s.wr := by rw [w₁₀, w₉, e₈, wr₇]
  refine ⟨by rw [g₁₀, r₉, g₈ _ (by decide), g₇ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      rdx₆], kp _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide),
    kp _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide),
    kp _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), ⟨p, ?_, ?_, hS.congr rd₁₀ wr₁₀⟩, ?_, fun j hj => ?_, rd₁₀, wr₁₀⟩
  · rw [kp _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), hp]
  · rw [scheduleAt_eq_of_frame _ fr fun r hr => ?_]
    · exact hK
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hS.sep _ hw).sub_right sub.1
      · exact (hS.sep _ hw).sub_right sub.2
  · rw [core_eq]
    exact fr.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
      · exact ⟨_, List.mem_singleton_self _, Offset.sub_base B (by simp only [wsSlot]; omega)⟩
  · have hj0 : j = 0 := by simp only [dirCore] at hj; omega
    subst hj0
    have ea : blkAddr (dirCore up) B 0 = B := by simp [dirCore]
    have hK₆ : scheduleAt t₆.mem p = k := by rw [mem₆]; exact hK
    rw [dirCore_bw, ea, Nat.mul_one, dirCipher_bytes, bytesAt_eq]
    refine congrArg Vector.toList (blockAt_eq _ _ _ fun i hi => ?_)
    rw [mem₁₀, b₈ i hi, c₁, c₂, l₆a, l₆b, hK₆, mem₅, show dirBlock k up (blockAt s.mem B) =
      blockOut k up (blockAt s.mem B) from rfl, blockOut_eq]

/-- Blowfish's core meets what the modes need. -/
def dirCoreSpec (up : Bool) : BlockSpec (dirCore up) where
  Key := Schedule
  cipher := dirCipher up
  KeyArgs := ModeKeyArgs
  Ready s _ k := ReadyAt s k
  cipher_len := dirCipher_len up
  layout := ⟨by simp only [dirCore]; decide, by simp only [dirCore]; decide, by simp only [dirCore]; decide,
    by simp only [dirCore]; decide, by simp only [dirCore]; decide, by simp only [dirCore]; decide⟩
  keyRegs_ok := by simp only [dirCore]; decide
  regs_ok := by simp only [dirCore, Modes.X86_64.regsOk]; decide
  keyArgs_congr h hr hrd hwr _ hf := keyArgs_congr h hr hrd hwr hf
  ready_frame h hf _ hw hg := ready_frame h hf hw hg
  prepare_wp := prepare_wp
  crypt_wp := crypt_wp

/-! ## `xmm15` -/

/-- `movq xmm, r64` of a register's low half puts back one whose upper half is zero. -/
theorem movq_lo {v : BitVec 128} (h : v.extractLsb' 64 64 = 0) : (0 : BitVec 64) ++ v.extractLsb' 0 64 = v := by
  rw [← h]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h64 : i < 64
  · simp [h64, hi]
  · simp only [h64, decide_false, Bool.false_and, ite_false]
    simp only [Bool.true_and, show i - 64 < 64 by omega, decide_true]
    congr 1; omega

theorem gprSafe_setup : gprSafe .r14 (.block setup) = true := by decide

theorem gprSafe_cipher (up : Bool) : gprSafe .r14 (cipher .rdi up) = true := by cases up <;> decide

theorem gprSafe_finish : gprSafe .r14 (.block finish) = true := by decide

/-- `crypt` keeps `xmm15`, its upper half zero. -/
theorem crypt_keepsIv (up : Bool) : KeepsIv (dirCore up).crypt := by
  intro s t s' h hz
  cases h with
  | seq e₁ e₂ =>
    cases e₁ with
    | block b₁ =>
      cases e₂ with
      | seq e₃ e₄ =>
        cases e₄ with
        | seq e₅ e₆ =>
          cases e₆ with
          | seq e₇ e₈ =>
            cases e₈ with
            | block b₈ =>
              rename_i s₁ _ s₂ _ s₃ _ s₄ _ _
              simp only [saveIv, execBlock, exec, Option.map_some, Option.some.injEq, Prod.mk.injEq] at b₁
              simp only [restoreIv, execBlock, exec, Option.map_some, Option.some.injEq, Prod.mk.injEq] at b₈
              have k14 : s₄.gpr .r14 = s₁.gpr .r14 :=
                ((keepsGpr_of_gprSafe gprSafe_finish _ _ _ e₇).trans
                  (keepsGpr_of_gprSafe (gprSafe_cipher up) _ _ _ e₅)).trans
                  (keepsGpr_of_gprSafe gprSafe_setup _ _ _ e₃)
              rw [← b₁.1] at k14
              rw [← b₈.1]
              simp only [XOp.exec, gpr_setReg_self] at k14 ⊢
              rw [k14]
              exact movq_lo hz

end VG.Proof.Blowfish.X86_64

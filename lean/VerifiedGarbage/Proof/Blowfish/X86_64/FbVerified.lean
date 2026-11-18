module

import VerifiedGarbage.Proof.Modes.X86_64.Fb
public import VerifiedGarbage.Proof.Blowfish.FbScratch
import VerifiedGarbage.Proof.Blowfish.X86_64.ModesLit
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
public import VerifiedGarbage.Impl.Blowfish.X86_64.Modes
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
public import VerifiedGarbage.Proof.Modes.Fb
public import VerifiedGarbage.Spec.Blowfish.Cfb
public import VerifiedGarbage.Impl.StackScratch.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Modes.X86_64.Fb
meta import VerifiedGarbage.Proof.Blowfish.FbScratch
meta import VerifiedGarbage.Proof.Blowfish.X86_64.ModesLit
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
meta import VerifiedGarbage.Impl.Blowfish.X86_64.Modes
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Modes.Fb
meta import VerifiedGarbage.Spec.Blowfish.Cfb
meta import VerifiedGarbage.Impl.StackScratch.X86_64
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintSum
public import VerifiedGarbage.Proof.Blowfish.ModeBytes
public import VerifiedGarbage.Proof.Modes.X86_64.FbLoop
public import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Blowfish.Blocks
import VerifiedGarbage.Proof.Blowfish.X86_64.Ecb
import VerifiedGarbage.Proof.Blowfish.Schedule
import VerifiedGarbage.Proof.Modes.X86_64.Steps
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Impl.Rc2.X86_64.Sse2Lookup
import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Blowfish.ModeBytes
meta import VerifiedGarbage.Proof.Modes.X86_64.FbLoop
meta import VerifiedGarbage.TCB.X86_64.Isa
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.GetElem
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.Framework.X86_64.Reduce
meta import VerifiedGarbage.Proof.Blowfish.Blocks
meta import VerifiedGarbage.Proof.Blowfish.X86_64.Ecb
meta import VerifiedGarbage.Proof.Blowfish.Schedule
meta import VerifiedGarbage.Proof.Modes.X86_64.Steps
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Rc2.X86_64.Sse2Lookup
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-! ### `Blowfish.X86_64.ModeCore`, which this module and modules that import it used -/

section

/-! ### `Modes.X86_64.KeepGpr`, which only this module used -/

section

/-!
# Code that keeps a general-purpose register

`keepsGpr_of_gprSafe`: code whose every instruction writes no
general-purpose register (an SSE instruction, a 128-bit load, a store) or
one other than `r` keeps `r`, whatever it does to the rest. A core whose
block code needs every `xmm` register, `ivX` among them, keeps the IV's
address in such a register around it (`Proof/Blowfish/X86_64/FbVerified.lean`).
-/

@[expose] public section

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd

/-- Whether `i` writes no general-purpose register but, at most, one other
than `r`. -/
def gprSafeI (r : Reg) : Instr → Bool
  | .xop _ | .movdquLoad .. | .movdquStore .. | .store .. | .store32 .. => true
  | .mov d _ | .mov32 d _ | .alu _ d _ | .movImm64 d _ | .bswap32 d | .movqR d _ => d != r
  | _ => false

theorem xop_exec_gpr (op : XOp) (s : State) : (op.exec s).gpr = s.gpr := by
  cases op <;> rfl

theorem execAlu_gpr {op : AluOp} {d : Reg} {src : Src} {s t : State} (h : execAlu op d src s = some t)
    {r : Reg} (hr : r ≠ d) : t.gpr r = s.gpr r := by
  simp only [execAlu, Option.bind_eq_some_iff] at h
  obtain ⟨b, -, h⟩ := h
  cases op <;> simp only [Option.some.injEq, Option.map_eq_some_iff] at h
  all_goals first
    | (subst h; simp only [gpr_setReg_of_ne _ _ hr, gpr_arithFlags])
    | (obtain ⟨c, -, rfl⟩ := h; simp only [gpr_setReg_of_ne _ _ hr, gpr_arithFlags])

theorem exec_gprSafe {r : Reg} {i : Instr} (hi : gprSafeI r i = true) {s t : State} (h : exec i s = some t) :
    t.gpr r = s.gpr r := by
  cases i <;> simp only [gprSafeI, bne_iff_ne, ne_eq, Bool.false_eq_true] at hi
  all_goals simp only [reduceExec, Option.map_eq_some_iff, Option.some.injEq] at h
  all_goals first
    | (subst h; first | rfl | exact congrFun (xop_exec_gpr _ _) _ |
        simp only [State.setReg32, gpr_setReg_of_ne _ _ (Ne.symm hi)])
    | (obtain ⟨v, -, rfl⟩ := h; first | rfl | simp only [State.setReg32, gpr_setReg_of_ne _ _ (Ne.symm hi)])
    | exact execAlu_gpr h (Ne.symm hi)
    | (simp only [State.store64, State.store32, State.store128] at h
       split at h
       · cases h; rfl
       · cases h)

/-- Whether every instruction of `c` keeps `r`, with no calls or frames. -/
def gprSafe (r : Reg) : Prog isa → Bool
  | .block is => is.all (gprSafeI r)
  | .seq a b => gprSafe r a && gprSafe r b
  | .ite _ a b => gprSafe r a && gprSafe r b
  | .loop b _ => gprSafe r b
  | _ => false

theorem execBlock_gprSafe {r : Reg} : ∀ {is : List Instr}, is.all (gprSafeI r) = true → ∀ {s s' : State}
    {t : List Leak}, execBlock isa is s = some (s', t) → s'.gpr r = s.gpr r
  | [], _, _, _, _, h => by simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h; rw [h.1]
  | i :: is, hs, s, s', t, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hs
    simp only [execBlock] at h
    split at h
    · cases h
    · rename_i s₁ he
      simp only [Option.map_eq_some_iff, Prod.exists] at h
      obtain ⟨s₂, t₂, h, he'⟩ := h
      simp only [Prod.mk.injEq] at he'
      rw [← he'.1]
      exact (execBlock_gprSafe hs.2 h).trans (exec_gprSafe hs.1 he)

theorem keepsGpr_of_gprSafe {r : Reg} {c : Prog isa} (hc : gprSafe r c = true) :
    ∀ s t s', Exec isa c s t s' → s'.gpr r = s.gpr r := by
  intro s t s' h
  revert hc
  induction h with
  | icall | icallNext => intro hc; simp only [gprSafe, Bool.false_eq_true] at hc
  | block e => exact fun hc => execBlock_gprSafe hc e
  | seq _ _ ih₁ ih₂ =>
    intro hc
    simp only [gprSafe, Bool.and_eq_true] at hc
    exact (ih₂ hc.2).trans (ih₁ hc.1)
  | iteT _ _ ih => intro hc; simp only [gprSafe, Bool.and_eq_true] at hc; exact ih hc.1
  | iteF _ _ ih => intro hc; simp only [gprSafe, Bool.and_eq_true] at hc; exact ih hc.2
  | loopExit _ _ ih => exact ih
  | loopNext _ _ _ ih₁ ih₂ => intro hc; exact (ih₂ hc).trans (ih₁ hc)
  | call => intro hc; simp only [gprSafe, Bool.false_eq_true] at hc
  | frame => intro hc; simp only [gprSafe, Bool.false_eq_true] at hc

end VG.Proof.Modes.X86_64

end

end


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
  ⟨_, hw, Offset.contains_base B ht (by omega_using [ht])⟩

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
  obtain sb₁ : s₁.gpr sb = B := by rw [g₁ _ (by decide), hB]
  obtain mem₅ : t₅.mem = s.mem := by rw [u₅, n₄, n₃, n₂, n₁, m₁]
  obtain rd₅ : t₅.rd = s.rd := by rw [u₅, d₄, d₃, d₂, d₁, rd₁]
  obtain wr₅ : t₅.wr = s.wr := by rw [u₅, w₄, w₃, w₂, w₁, wr₁]
  obtain rsi₅ : t₅.gpr .rsi = B := by
    rw [g₅ _ (by decide), o₄ _ (by decide), o₃ _ (by decide), r₂, o₁ _ (by decide), sb₁]
  obtain ⟨t₆, f₆, l₆a, l₆b, k₆, g₆, u₆⟩ := loadBlock_run t₅ B rsi₅ fun o ho => by
    rw [rd₅, wr₅]; exact inScr' (s := s) hw (by omega_using [ho])
  obtain mem₆ : t₆.mem = s.mem := by rw [u₆, mem₅]
  obtain rd₆ : t₆.rd = s.rd := by rw [u₆, rd₅]
  obtain wr₆ : t₆.wr = s.wr := by rw [u₆, wr₅]
  obtain g₆' : ∀ g, g ≠ .rdx → g ≠ .rsi → g ≠ .rcx → g ≠ .r11 → t₆.gpr g = s₁.gpr g :=
    fun g h1 h3 h4 h5 => by rw [g₆ _ h5, g₅ _ h5, o₄ _ h4, o₃ _ h4, o₂ _ h3, o₁ _ h1]
  obtain rdx₆ : t₆.gpr .rdx = B := by
    rw [g₆ _ (by decide), g₅ _ (by decide), o₄ _ (by decide), o₃ _ (by decide), o₂ _ (by decide), r₁, sb₁]
  obtain rdi₆ : t₆.gpr .rdi = p := by
    rw [g₆' _ (by decide) (by decide) (by decide) (by decide), g₁ _ (by decide), hp]
  obtain rsi₆ : t₆.gpr .rsi = B := by rw [g₆ _ (by decide), rsi₅]
  obtain rcx₆ : t₆.gpr .rcx = wsAddr B := by
    rw [g₆ _ (by decide), g₅ _ (by decide), r₄, r₃, o₂ _ (by decide), o₁ _ (by decide), sb₁,
      signExtend_small (by decide)]
  apply WP.seq
  refine WP.of_runBlock ⟨t₆, cat_run (cat_run (cat_run f₁ (cat_run f₂ (cat_run f₃ f₄))) f₅) f₆, ?_⟩
  -- The rounds.
  obtain inSch : ∀ off n, off + n ≤ 4168 → InRegions (t₆.rd ++ t₆.wr) (p + BitVec.ofNat 64 off) n :=
    fun off n h => ⟨_, List.mem_append_left _ (by rw [rd₆]; exact hS.rd), Offset.contains_base p h (by omega_using [h])⟩
  obtain CE : CipherEnv .rdi p t₆ := by
    refine ⟨⟨rdi₆, by decide, by decide, by decide, fun off h => inSch off 16 (by omega_using [h]),
      by rw [k₆ _ (by decide) (by decide), x₅a], by rw [k₆ _ (by decide) (by decide), x₅b],
      by rw [k₆ _ (by decide) (by decide), x₅c]⟩, by decide, by decide, fun i hi => inSch _ 4 (by omega_using [hi])⟩
  apply WP.seq
  refine WP.mono (cipher_run CE up) fun t₇ ⟨c₁, c₂, O⟩ => ?_
  obtain mem₇ : t₇.mem = s.mem := by rw [O.upd, mem₆]
  obtain rd₇ : t₇.rd = s.rd := by rw [O.upd, rd₆]
  obtain wr₇ : t₇.wr = s.wr := by rw [O.upd, wr₆]
  have g₇ : ∀ g, g ≠ .rax → g ≠ .r8 → g ≠ .r9 → g ≠ .r10 → g ≠ .r11 → t₇.gpr g = t₆.gpr g := O.gpr
  -- The block out, and `sb` back.
  obtain SE : StoreEnv B (wsAddr B) t₇ := by
    refine ⟨by rw [g₇ _ (by decide) (by decide) (by decide) (by decide) (by decide), rsi₆],
      by rw [g₇ _ (by decide) (by decide) (by decide) (by decide) (by decide), rcx₆],
      by rw [wr₇, show B = B + BitVec.ofNat 64 0 by simp]; exact inScr hw (by decide),
      by rw [wr₇]; exact inScr hw (by simp only [wsSlot]; omega_using []),
      sep_of_disjoint (buf_ws B), sep_of_disjoint (buf_ws B).symm⟩
  obtain ⟨t₈, f₈, b₈, fr₈, g₈, e₈⟩ := storeBlock_run SE
  obtain ⟨t₉, f₉, r₉, o₉, n₉, d₉, w₉⟩ := movR_ok t₈ sb .rdx
  apply WP.seq
  refine WP.of_runBlock ⟨t₉, cat_run f₈ f₉, ?_⟩
  obtain ⟨t₁₀, f₁₀, g₁₀, n₁₀, d₁₀, w₁₀⟩ := restoreIv_run t₉
  refine WP.of_runBlock ⟨t₁₀, f₁₀, ?_⟩
  obtain mem₁₀ : t₁₀.mem = t₈.mem := by rw [n₁₀, n₉]
  obtain fr : Frame [⟨B, 8⟩, ⟨wsAddr B, 16⟩] s.mem t₁₀.mem := by rw [mem₁₀, ← mem₇]; exact fr₈
  obtain sub : Region.Sub ⟨B, 8⟩ ⟨B, 8 * 11⟩ ∧ Region.Sub ⟨wsAddr B, 16⟩ ⟨B, 8 * 11⟩ :=
    ⟨Region.sub_prefix (by decide), Offset.sub_base B (by simp only [wsSlot]; omega_using [])⟩
  obtain kp : ∀ g, g ≠ .r14 → g ≠ .rdx → g ≠ .rsi → g ≠ .rcx → g ≠ .rax → g ≠ .r8 →
      g ≠ .r9 → g ≠ .r10 → g ≠ .r11 → t₁₀.gpr g = s.gpr g := fun g h1 h3 h5 h6 h7 h8 h9 h10 h11 => by
    rw [g₁₀, o₉ _ h9, g₈ _ h11, g₇ _ h7 h8 h9 h10 h11, g₆' _ h3 h5 h6 h11, g₁ _ h1]
  obtain rd₁₀ : t₁₀.rd = s.rd := by rw [d₁₀, d₉, e₈, rd₇]
  obtain wr₁₀ : t₁₀.wr = s.wr := by rw [w₁₀, w₉, e₈, wr₇]
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
      · exact ⟨_, List.mem_singleton_self _, Offset.sub_base B (by simp only [wsSlot]; omega_using [])⟩
  · have hj0 : j = 0 := by simp only [dirCore] at hj; omega_using [hj]
    subst hj0
    obtain ea : blkAddr (dirCore up) B 0 = B := by simp [dirCore]
    obtain hK₆ : scheduleAt t₆.mem p = k := by rw [mem₆]; exact hK
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
    simp only [Bool.true_and, show i - 64 < 64 by omega_using [hi], decide_true]
    congr 1; omega_using [h64]

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
              obtain k14 : s₄.gpr .r14 = s₁.gpr .r14 :=
                ((keepsGpr_of_gprSafe gprSafe_finish _ _ _ e₇).trans
                  (keepsGpr_of_gprSafe (gprSafe_cipher up) _ _ _ e₅)).trans
                  (keepsGpr_of_gprSafe gprSafe_setup _ _ _ e₃)
              rw [← b₁.1] at k14
              rw [← b₈.1]
              simp only [XOp.exec, gpr_setReg_self] at k14 ⊢
              rw [k14]
              exact movq_lo hz

end VG.Proof.Blowfish.X86_64

end

end

/-!
# Blowfish-OFB and -CFB64 on x86-64 meet their contracts

`ofb_wp`, `cfbEncrypt_wp`, `cfbDecrypt_wp`: the modes' OFB and CFB
(`Proof.Modes.X86_64.fb_wp`) over Blowfish's core (`modeCoreSpec`), with the
specification's results (`Proof.Modes.ofb_of`, …). `ofb_verified`, …: each
is correct and constant time, by the taint analysis: the pointers, `n` and
the stack pointer are public, and so is everything the code computes from
them; the IV is secret. `ofb_framed`, … run them with their working space on
the stack, zeroed on return: 96 bytes, the 11 words of the scratch buffer
and 8 more.
-/

@[expose] public section

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.Impl.Blowfish.X86_64

/-- The precondition of the feedback modes on x86-64, with the data `len`
bytes long and the working space at `r8`. -/
def fbPre (len : State → Nat) (s : State) : Prop :=
  let sched : Region := ⟨s.gpr .rdi, 4168⟩
  let iv : Region := ⟨s.gpr .rsi, 8⟩
  let data : Region := ⟨s.gpr .rdx, len s⟩
  let scratch : Region := ⟨s.gpr .r8, 8 * 11⟩
  let ret : Region := ⟨s.gpr .rsp, 8⟩
  s.rd = [sched] ∧ s.wr = [iv, data, scratch] ∧ sched.Disjoint iv ∧ sched.Disjoint data ∧
    sched.Disjoint scratch ∧ iv.Disjoint data ∧ iv.Disjoint scratch ∧ data.Disjoint scratch ∧
    ret.Disjoint iv ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
    (s.gpr .rdi).toNat + 4168 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 8 ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + len s ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 8 * 11 ≤ 2 ^ 64

/-- The public arguments. -/
def fbPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `n` blocks. -/
abbrev blkLen (s : State) : Nat := 8 * (s.gpr .rcx).toNat

/-- The schedule, IV and data of `s`'s arguments. -/
abbrev ciphOf (s : State) : Spec.Cbc.Cipher := Spec.Blowfish.cipher (Spec.Blowfish.scheduleAt s.mem (s.gpr .rdi))
abbrev ivOf (s : State) : List Byte := Spec.Aes.bytesAt s.mem (s.gpr .rsi) 8
abbrev blocksOf (s : State) (m : Mem) : List (List Byte) := Spec.Blowfish.cbcBlocksAt m (s.gpr .rdx) (s.gpr .rcx).toNat

def ofbX86_64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem = Spec.Ofb.crypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .rsi) 8 = Spec.Ofb.next (ciphOf s) (ivOf s) (s.gpr .rcx).toNat
  pub := fbPub

def cfbEncX86_64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem = Spec.Cfb.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .rsi) 8 =
      Spec.Cbc.next (ivOf s) (Spec.Cfb.encrypt (ciphOf s) (ivOf s) (blocksOf s s.mem))
  pub := fbPub

def cfbDecX86_64 : Contract isa where
  pre := fbPre blkLen
  post s s' := blocksOf s s'.mem = Spec.Cfb.decrypt (ciphOf s) (ivOf s) (blocksOf s s.mem) ∧
    Spec.Aes.bytesAt s'.mem (s.gpr .rsi) 8 = Spec.Cbc.next (ivOf s) (blocksOf s s.mem)
  pub := fbPub

/-- What the modes' OFB and CFB give, for a mode `mo`: the data and the
IV as `fbOut` and `fbIn`, keeping the callee-saved registers. -/
theorem fb_wp' (mo : Impl.Modes.FbMode) {s₀ : State} (hp : fbPre blkLen s₀) :
    WP isa ((dirCore true).fb mo modeRegs) s₀ fun s' => gprPreserved s₀ s' ∧
      Modes.blocksOf 8 s'.mem (s₀.gpr .rdx) (s₀.gpr .rcx).toNat =
        (List.range (s₀.gpr .rcx).toNat).map (Modes.fbOut mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀)) ∧
      Spec.Aes.bytesAt s'.mem (s₀.gpr .rsi) 8 = Modes.fbIn mo 8 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀) (s₀.gpr .rcx).toNat := by
  obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, dRV, dRD, dRS, fitK, fitV, fitD, fitB⟩ := hp
  have hwS : (⟨s₀.gpr .r8, 8 * 11⟩ : Region) ∈ s₀.wr := by rw [hwr]; simp
  refine WP.mono (Proof.Modes.X86_64.fb_wp (dirCoreSpec true) mo (r := modeRegs)
    ⟨by decide, by decide, by decide⟩ (by decide)
    (B := s₀.gpr .r8) (P := s₀.gpr .rsi) (D := s₀.gpr .rdx) (n := (s₀.gpr .rcx).toNat)
    (k := Spec.Blowfish.scheduleAt s₀.mem (s₀.gpr .rdi)) rfl rfl rfl rfl ⟨hwS, fitB⟩
    (by rw [hwr]; simp) (by rw [hwr]; simp [Nat.mul_comm]) dVS dDS dVD fitD
    ⟨s₀.gpr .rdi, rfl, rfl, ⟨by rw [hrd]; simp, fitK, fun w hw => by
      rw [hwr] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact dKV
      · exact dKD
      · exact dKS⟩, fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dKS⟩ ⟨Modes.X86_64.keepsIv_of_scal (by lit_decide), crypt_keepsIv true⟩)
    fun s' ⟨hcs, hdata, hiv, hf, _, _⟩ =>
    ⟨⟨hcs, ?_⟩, by rw [dirCore_bw, Nat.mul_one] at hdata hiv; exact ⟨hdata, hiv⟩⟩
  rw [VG.Proof.Modes.X86_64.stkList_eq_nil rfl, List.append_nil] at hf
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact dRS
  · exact dRD
  · exact dRV

theorem ofb_wp {s₀ : State} (hp : ofbX86_64.pre s₀) :
    WP isa ofb s₀ fun s' => gprPreserved s₀ s' ∧ ofbX86_64.post s₀ s' :=
  WP.mono (fb_wp' .ofb hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.ofb_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀) (s₀.gpr .rcx).toNat
    refine ⟨hg, ?_, by rw [hv, h2]⟩
    change Spec.Blowfish.cbcBlocksAt _ _ _ = Spec.Ofb.crypt _ _ (Spec.Blowfish.cbcBlocksAt _ _ _)
    rw [cbcBlocksAt_eq, cbcBlocksAt_eq, hd, h1]

theorem cfbEncrypt_wp {s₀ : State} (hp : cfbEncX86_64.pre s₀) :
    WP isa cfbEncrypt s₀ fun s' => gprPreserved s₀ s' ∧ cfbEncX86_64.post s₀ s' :=
  WP.mono (fb_wp' .cfbEnc hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbEnc_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀) (s₀.gpr .rcx).toNat
    refine ⟨hg, ?_, ?_⟩
    · change Spec.Blowfish.cbcBlocksAt _ _ _ = Spec.Cfb.encrypt _ _ (Spec.Blowfish.cbcBlocksAt _ _ _)
      rw [cbcBlocksAt_eq, cbcBlocksAt_eq, hd, h1]
    · change _ = Spec.Cbc.next _ (Spec.Cfb.encrypt _ _ (Spec.Blowfish.cbcBlocksAt _ _ _))
      rw [hv, h2, cbcBlocksAt_eq]

theorem cfbDecrypt_wp {s₀ : State} (hp : cfbDecX86_64.pre s₀) :
    WP isa cfbDecrypt s₀ fun s' => gprPreserved s₀ s' ∧ cfbDecX86_64.post s₀ s' :=
  WP.mono (fb_wp' .cfbDec hp) fun s' ⟨hg, hd, hv⟩ => by
    obtain ⟨h1, h2⟩ := Modes.cfbDec_of 8 (ciphOf s₀) s₀.mem (s₀.gpr .rdx) (ivOf s₀) (s₀.gpr .rcx).toNat
    refine ⟨hg, ?_, ?_⟩
    · change Spec.Blowfish.cbcBlocksAt _ _ _ = Spec.Cfb.decrypt _ _ (Spec.Blowfish.cbcBlocksAt _ _ _)
      rw [cbcBlocksAt_eq, cbcBlocksAt_eq, hd, h1]
    · change _ = Spec.Cbc.next _ (Spec.Blowfish.cbcBlocksAt _ _ _)
      rw [hv, h2, cbcBlocksAt_eq]

/-! ## Constant time -/

def fbTaint : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .rsp], flags := false,
    lens := [8, 0, 8 * 11], bases := [(.r8, 2, 0)] }

theorem fbTaint_wf {len : State → Nat} (s : State) (hs : fbPre len s) : Taint.Wf fbTaint s := by
  obtain ⟨_, hwr, _, _, _, dVD, dVS, dDS, _, _, _, _, fitV, fitD, fitB⟩ := hs
  refine ⟨fun _ => ?_, ?_⟩
  · rw [hwr]
    refine ⟨?_, ?_, ?_⟩
    · exact List.Forall₂.cons (by change 8 ≤ 8; omega_using []) (List.Forall₂.cons (by change 0 ≤ len s; omega_using [])
        (List.Forall₂.cons (by change 8 * 11 ≤ 8 * 11; omega_using []) List.Forall₂.nil))
    · refine List.Pairwise.cons (fun r hr => ?_) (List.Pairwise.cons (fun r hr => ?_)
        (List.Pairwise.cons (by simp) List.Pairwise.nil))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dVD
        · exact dVS
      · obtain rfl := List.mem_singleton.mp hr; exact dDS
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · change 8 ≤ 2 ^ 64; omega_using []
      · change len s ≤ 2 ^ 64; omega_using [fitD]
      · change 8 * 11 ≤ 2 ^ 64; omega_using []
  · intro p hp
    simp only [fbTaint, List.mem_singleton] at hp
    subst p
    unfold Taint.region
    rw [hwr]
    change s.gpr .r8 = s.gpr .r8 + (0 : BitVec 64)
    exact (BitVec.add_zero _).symm

theorem fbTaint_agree {len : State → Nat} (hlen : ∀ s t, s.gpr .rcx = t.gpr .rcx → len s = len t) (s t : State)
    (hs : fbPre len s) (ht : fbPre len t) (hp : fbPub s t) : X86_64.Taint.Agree fbTaint s t := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hp
  refine ⟨?_, ?_, fbTaint_wf s hs, fbTaint_wf t ht, ?_, ?_, ?_, X86_64.Taint.noXr⟩
  · constructor
    · intro r hr
      simp only [fbTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [p1, p2, p3, p4, p5, p6]
    · intro h
      change false = true at h
      contradiction
  · intro _
    rw [hs.2.1, ht.2.1, p2, p3, p5, hlen s t p4]
  · intro slot hslot
    change slot ∈ ([] : List (Nat × Nat × Nat)) at hslot
    exact False.elim (List.not_mem_nil hslot)
  · intro slot hslot
    change slot ∈ ([] : List (Nat × Nat × Nat)) at hslot
    exact False.elim (List.not_mem_nil hslot)
  · intro r hr
    simp only [fbTaint, RegSet.not_mem_empty] at hr

theorem blkLen_congr : ∀ s t : State, s.gpr .rcx = t.gpr .rcx → blkLen s = blkLen t := fun _ _ h => by
  simp only [blkLen, h]

/-- A state satisfying the precondition (one block, or one byte). -/
def fbSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x3000 | .rdx => 0x4000 | .rcx => 1 | .r8 => 0x5000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 4168⟩]
  wr := [⟨0x3000, 8⟩, ⟨0x4000, 8⟩, ⟨0x5000, 8 * 11⟩]

theorem ofb_verified :
    Verified X86_64.target ofb (Proof.Blowfish.fbScratchContract X86_64.abi 11 Proof.Blowfish.ofbPost) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := ofb_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := ofb) (by lit_decide) he hg, hpost⟩)
    (VG.Taint.constantTime (A := taint) fbTaint (fbTaint_agree blkLen_congr) (by taint_decide)) (by
    sig_implies [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig,
      Proof.Blowfish.ofbPost, ofbX86_64, fbPre, fbPub, X86_64.abi, X86_64.argRegs] [fbSat] using fbSat)

theorem cfbEncrypt_verified :
    Verified X86_64.target cfbEncrypt (Proof.Blowfish.fbScratchContract X86_64.abi 11 Proof.Blowfish.cfbEncPost) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := cfbEncrypt_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := cfbEncrypt) (by lit_decide) he hg, hpost⟩)
    (VG.Taint.constantTime (A := taint) fbTaint (fbTaint_agree blkLen_congr) (by taint_decide)) (by
    sig_implies [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig,
      Proof.Blowfish.cfbEncPost, cfbEncX86_64, fbPre, fbPub, X86_64.abi, X86_64.argRegs] [fbSat] using fbSat)

theorem cfbDecrypt_verified :
    Verified X86_64.target cfbDecrypt (Proof.Blowfish.fbScratchContract X86_64.abi 11 Proof.Blowfish.cfbDecPost) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, hg, hpost⟩ := cfbDecrypt_wp hs
      exact ⟨t, s', he, abiPreserved_of_exec (c := cfbDecrypt) (by lit_decide) he hg, hpost⟩)
    (VG.Taint.constantTime (A := taint) fbTaint (fbTaint_agree blkLen_congr) (by taint_decide)) (by
    sig_implies [Proof.Blowfish.fbScratchContract, Proof.Blowfish.fbScratchSig, Spec.Blowfish.ofbSig,
      Proof.Blowfish.cfbDecPost, cfbDecX86_64, fbPre, fbPub, X86_64.abi, X86_64.argRegs] [fbSat] using fbSat)

/-- OFB with its working space on the stack. -/
theorem ofb_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 ofb)
      (Spec.Blowfish.ofbContract X86_64.abi 96) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Blowfish.ofbSig) (nm := "scratch") (e := .u64)
    (n := 11) (post := Proof.Blowfish.ofbPost X86_64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 96) ofb_verified (by decide) (by decide) (by decide)
    (Code.all_of_spTest (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Blowfish.ofbPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- CFB64 encryption with its working space on the stack. -/
theorem cfbEncrypt_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 cfbEncrypt)
      (Spec.Blowfish.cfbEncryptContract X86_64.abi 96) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Blowfish.cfbSig) (nm := "scratch") (e := .u64)
    (n := 11) (post := Proof.Blowfish.cfbEncPost X86_64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 96) cfbEncrypt_verified (by decide) (by decide) (by decide)
    (Code.all_of_spTest (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Blowfish.cfbEncPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

/-- CFB64 decryption with its working space on the stack. -/
theorem cfbDecrypt_framed :
    Verified X86_64.target (Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 cfbDecrypt)
      (Spec.Blowfish.cfbDecryptContract X86_64.abi 96) :=
  X86_64.Verified.stackScratchWiped (sig := Spec.Blowfish.cfbSig) (nm := "scratch") (e := .u64)
    (n := 11) (post := Proof.Blowfish.cfbDecPost X86_64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 96) cfbDecrypt_verified (by decide) (by decide) (by decide)
    (Code.all_of_spTest (by lit_decide)) (by lit_decide) (by decide)
    (Proof.Blowfish.cfbDecPostOut_local _)
    (X86_64.sat_regs (by decide) (by decide) (by decide +kernel) (by rw [Curry.apply_const]; trivial))

end VG.Proof.Blowfish.X86_64

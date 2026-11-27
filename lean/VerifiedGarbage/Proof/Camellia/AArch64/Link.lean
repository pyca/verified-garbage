module

public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Verified
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Modes.AArch64.Steps
public import VerifiedGarbage.Impl.Camellia.AArch64.Cbc
public import VerifiedGarbage.Impl.Camellia.AArch64.Fb
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Inline
public import VerifiedGarbage.Proof.Modes.AArch64.FbLoop
import VerifiedGarbage.Proof.Camellia.Common
import VerifiedGarbage.Proof.Camellia.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Camellia.AArch64.Serial.Verified
meta import VerifiedGarbage.Proof.Framework.AArch64.Inline
meta import VerifiedGarbage.Proof.Camellia.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Impl.Camellia.AArch64.Serial.Prepared
public import VerifiedGarbage.Proof.Camellia.AArch64.Serial.State
public import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Camellia.Ctr
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Modes.AArch64.Steps
meta import VerifiedGarbage.Proof.Modes.AArch64.FbLoop
meta import VerifiedGarbage.Proof.Camellia.Common
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Camellia.AArch64.Serial.Prepared
meta import VerifiedGarbage.Proof.Camellia.AArch64.Serial.State
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Camellia.Ctr

/-! ### `Camellia.AArch64.Serial.CallCore`, which this module and modules that import it used -/

section

/-!
# The serial core's calls implement the modes' core

`coreSpec`: `callCore`, whose `prepare` and `crypt` call
`vg_camellia_prepare_encrypt_keys` and `vg_camellia_encrypt_prepared`
(`WP.call`, with their contracts on AArch64, `prepAArch64` and
`cryptAArch64`) on the core's 418 slots, meets what the modes need of a
core (`Proof.Modes.AArch64.CoreSpec`). The key is ready when the slots hold
the table (`Ready`), `x26` the number of rounds and `x22` the slots'
address. Neither function writes a register the AAPCS64 preserves, so the
modes' `x19`, `x23` and `x24` and the core's `x20` (the return address
across the call), `x22` and `x26` survive the calls (`keeps_x19`).
-/

@[expose] public section

namespace VG.Proof.Camellia.AArch64.Serial

open VG VG.AArch64 VG.Impl.Camellia.AArch64.Serial
open VG.Impl.Aes.AArch64 (sb movR)
open VG.Proof.Camellia (schedWords)
open VG.Proof.Modes.AArch64 (ScrIn coreRegion bufRegion bufAddr CoreSpec BlockSpec KeepsReg runBlock_app modeRegs WrIn)
open VG.Proof.Camellia.Prepared (Holds Keeps)

/-- The table ready in the slots at `B`, the number of rounds in `x26` and
`B` in `x22`. -/
def CallReady (s : State) (B : Addr) (k : Nat × List (BitVec 64)) : Prop :=
  Ready s.mem B k ∧ s.gpr .x26 = BitVec.ofNat 64 k.1 ∧ s.gpr .x22 = B

theorem toNat_rounds {R : Nat} (hR : R = 18 ∨ R = 24) : (BitVec.ofNat 64 R).toNat = R := by
  rcases hR with rfl | rfl <;> rfl

theorem toNat_total : (BitVec.ofNat 64 core.total).toNat = 418 := rfl

theorem total_eq : callCore.total = 418 := rfl

@[simp] theorem callCore_bw : callCore.bw = 2 := rfl

/-- The core's slots, as the calls' working space. -/
theorem ws_covers {s : State} {B : Addr} (hs : ScrIn s B callCore.total) :
    Covers [⟨B, 8 * core.total⟩] s.wr := Covers.of_sub fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨_, hs.wr, 0, by rw [BitVec.add_zero], by show 0 + 3344 ≤ 3344; omega_using []⟩

/-- What a call changed in the working space, within the core's slots. -/
theorem frame_core {m m' : Mem} {B : Addr} {e n : Nat} (hf : Frame [⟨B, 8 * core.total⟩] m m')
    (hk : Keeps B core.total [(e, n)] m m') (he : e + n ≤ 8 * core.slots) :
    Frame [coreRegion callCore B] m m' :=
  (frame_of_keeps hf hk (by show e + n ≤ 3344; have : 8 * core.slots = 3152 := rfl; omega_using [he, this]) (by decide)).sub
    fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.sub_base B he⟩

theorem callPrepare_wp {s : State} {B : Addr} {rs : List Region} {k : Nat × List (BitVec 64)}
    (hB : s.gpr sb = B) (hs : ScrIn s B callCore.total) (hR : (⟨B, 8 * callCore.total⟩ : Region) ∈ rs)
    (hk : VG.Proof.Camellia.AArch64.KeyArgs s rs k) :
    WP isa callCore.prepare s fun s' => CallReady s' B k ∧ s'.gpr sb = B ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 ∧
      Frame [coreRegion callCore B] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨R, ws⟩ := k
  obtain ⟨p, hp, hx1, hRr, hws, hin, hfit, hdis⟩ := hk
  simp only at hx1 hRr hws
  have hfB := hs.fit
  rw [total_eq] at hfB
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := Modes.AArch64.movR_ok s .x20 .x30
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := Modes.AArch64.movR_ok s₁ .x22 sb
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := Modes.AArch64.movR_ok s₂ .x26 .x1
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := Modes.AArch64.movR_ok s₃ .x2 sb
  obtain ⟨s₅, e₅, r₅, o₅, m₅, rd₅, wr₅⟩ := Modes.AArch64.movz_ok s₄ .x3 (v := core.total) (by decide)
  obtain e : runBlock isa [movR .x20 .x30, movR .x22 sb, movR .x26 .x1, movR .x2 sb,
      .movz .x .x3 (BitVec.ofNat 16 core.total) 0] s = some s₅ := by
    rw [show [movR .x20 .x30, movR .x22 sb, movR .x26 .x1, movR .x2 sb,
        Instr.movz .x .x3 (BitVec.ofNat 16 core.total) 0] = [movR .x20 .x30] ++ ([movR .x22 sb] ++
        ([movR .x26 .x1] ++ ([movR .x2 sb] ++ [.movz .x .x3 (BitVec.ofNat 16 core.total) 0]))) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃,
      Option.bind_some, runBlock_app, e₄, Option.bind_some, e₅]
  obtain x0₅ : s₅.gpr .x0 = p := by
    rw [o₅ _ (by decide), o₄ _ (by decide), o₃ _ (by decide), o₂ _ (by decide), o₁ _ (by decide), hp]
  obtain x1₅ : s₅.gpr .x1 = BitVec.ofNat 64 R := by
    rw [o₅ _ (by decide), o₄ _ (by decide), o₃ _ (by decide), o₂ _ (by decide), o₁ _ (by decide), hx1]
  obtain x2₅ : s₅.gpr .x2 = B := by
    rw [o₅ _ (by decide), r₄, o₃ _ (by decide), o₂ _ (by decide), o₁ _ (by decide), hB]
  have x3₅ : s₅.gpr .x3 = BitVec.ofNat 64 core.total := r₅
  obtain x20₅ : s₅.gpr .x20 = s.gpr .x30 := by
    rw [o₅ _ (by decide), o₄ _ (by decide), o₃ _ (by decide), o₂ _ (by decide), r₁]
  obtain x22₅ : s₅.gpr .x22 = B := by
    rw [o₅ _ (by decide), o₄ _ (by decide), o₃ _ (by decide), r₂, o₁ _ (by decide), hB]
  obtain x26₅ : s₅.gpr .x26 = BitVec.ofNat 64 R := by
    rw [o₅ _ (by decide), o₄ _ (by decide), r₃, o₂ _ (by decide), o₁ _ (by decide), hx1]
  obtain x23₅ : s₅.gpr .x23 = s.gpr .x23 := by
    rw [o₅ _ (by decide), o₄ _ (by decide), o₃ _ (by decide), o₂ _ (by decide), o₁ _ (by decide)]
  obtain x24₅ : s₅.gpr .x24 = s.gpr .x24 := by
    rw [o₅ _ (by decide), o₄ _ (by decide), o₃ _ (by decide), o₂ _ (by decide), o₁ _ (by decide)]
  obtain mem₅ : s₅.mem = s.mem := by rw [m₅, m₄, m₃, m₂, m₁]
  obtain rd₅' : s₅.rd = s.rd := by rw [rd₅, rd₄, rd₃, rd₂, rd₁]
  obtain wr₅' : s₅.wr = s.wr := by rw [wr₅, wr₄, wr₃, wr₂, wr₁]
  show WP isa prepareCall s _
  refine WP.seq (WP.of_runBlock ⟨s₅, e, ?_⟩)
  obtain hsep : Region.Disjoint ⟨p, 272⟩ ⟨B, 8 * core.total⟩ := hdis _ hR
  obtain g0 : (s₅.callEntry.withRegions [⟨p, 272⟩] [⟨B, 8 * core.total⟩]).gpr .x0 = p := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ VG.AArch64.linkRegs), x0₅]
  obtain g1 : ((s₅.callEntry.withRegions [⟨p, 272⟩] [⟨B, 8 * core.total⟩]).gpr .x1).toNat = R := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x1 ∉ VG.AArch64.linkRegs), x1₅,
      toNat_rounds hRr]
  obtain g2 : (s₅.callEntry.withRegions [⟨p, 272⟩] [⟨B, 8 * core.total⟩]).gpr .x2 = B := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x2 ∉ VG.AArch64.linkRegs), x2₅]
  obtain g3 : ((s₅.callEntry.withRegions [⟨p, 272⟩] [⟨B, 8 * core.total⟩]).gpr .x3).toNat = 418 := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x3 ∉ VG.AArch64.linkRegs), x3₅,
      toNat_total]
  obtain hm₀ : (s₅.callEntry.withRegions [⟨p, 272⟩] [⟨B, 8 * core.total⟩]).mem = s.mem := by
    rw [State.withRegions_mem, State.callEntry_mem, mem₅]
  obtain w : WP isa (.call "vg_camellia_prepare_encrypt_keys" prepareEncrypt) s₅ fun s' =>
      s'.rd = s₅.rd ∧ s'.wr = s₅.wr ∧ (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s₅.gpr r) ∧
      Frame [⟨B, 8 * core.total⟩] s₅.mem s'.mem ∧
      Holds layout s'.mem B R (schedWords s.mem p R) .encrypt ∧ Keeps B core.total [(0, 528)] s.mem s'.mem := by
    refine WP.call (k := prepAArch64) prep_correct (rd := [⟨p, 272⟩]) (wr := [⟨B, 8 * core.total⟩]) ?_
      (Covers.append_left (Covers.left (Covers.of_mem fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [rd₅']; exact hin))
        (Covers.right (by rw [wr₅']; exact ws_covers hs)))
      (by rw [wr₅']; exact ws_covers hs) (fun s' hrd hwr _ hf hg _ hpost => ⟨hrd, hwr, hg, hf, ?_⟩)
      (by lit_decide)
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [State.withRegions_rd, g0]
      · rw [State.withRegions_wr, g2, g3]; rfl
      · rw [g0, g2, g3]; exact hsep
      · rw [g0]; exact hfit
      · rw [g2, g3]; omega_using [hfB]
      · rw [g1]; exact hRr
      · rw [g3, size_eq]
    · obtain ⟨hH, hK⟩ := hpost
      change Holds layout s'.mem _ _ _ _ at hH
      change Keeps _ _ _ _ s'.mem at hK
      rw [hm₀, g0, g1, g2] at hH
      rw [hm₀, g2, g3] at hK
      exact ⟨hH, hK⟩
  obtain ⟨t₆, s₆, e₆, rd₆, wr₆, g₆, f₆, hH, hK⟩ := w
  refine WP.seq ⟨t₆, s₆, e₆, ?_⟩
  obtain x22₆ : s₆.gpr .x22 = B := by rw [g₆ _ (by simp [preserved]) (by decide), x22₅]
  obtain x20₆ : s₆.gpr .x20 = s.gpr .x30 := by rw [g₆ _ (by simp [preserved]) (by decide), x20₅]
  obtain ⟨s₇, e₇, r₇, o₇, m₇, rd₇, wr₇⟩ := Modes.AArch64.movR_ok s₆ sb .x22
  obtain ⟨s₈, e₈, -, o₈, m₈, rd₈, wr₈⟩ := Modes.AArch64.movR_ok s₇ .x30 .x20
  obtain e' : runBlock isa [movR sb .x22, movR .x30 .x20] s₆ = some s₈ := by
    rw [show [movR sb .x22, movR .x30 .x20] = [movR sb .x22] ++ [movR .x30 .x20] from rfl, runBlock_app, e₇,
      Option.bind_some, e₈]
  obtain g₈ : ∀ r, r ≠ sb → r ≠ .x30 → s₈.gpr r = s₆.gpr r := fun r h1 h2 => by rw [o₈ _ h2, o₇ _ h1]
  obtain mem₈ : s₈.mem = s₆.mem := by rw [m₈, m₇]
  refine WP.of_runBlock ⟨s₈, e', ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [mem₈, hws]; exact ready_of_holds hRr hH
  · rw [g₈ _ (by decide) (by decide), g₆ _ (by simp [preserved]) (by decide), x26₅]
  · rw [g₈ _ (by decide) (by decide), x22₆]
  · rw [o₈ _ (by decide), r₇, x22₆]
  · rw [g₈ _ (by decide) (by decide), g₆ _ (by simp [preserved]) (by decide), x23₅]
  · rw [g₈ _ (by decide) (by decide), g₆ _ (by simp [preserved]) (by decide), x24₅]
  · rw [mem₈]; rw [mem₅] at f₆
    exact frame_core f₆ hK (by decide)
  · rw [rd₈, rd₇, rd₆, rd₅']
  · rw [wr₈, wr₇, wr₆, wr₅']

theorem callCrypt_wp {s : State} {B : Addr} {k : Nat × List (BitVec 64)} (hB : s.gpr sb = B)
    (hs : ScrIn s B callCore.total) (hr : CallReady s B k) :
    WP isa callCore.crypt s fun s' => s'.gpr sb = B ∧
      s'.gpr .x23 = s.gpr .x23 ∧ s'.gpr .x24 = s.gpr .x24 ∧ CallReady s' B k ∧
      Frame [coreRegion callCore B] s.mem s'.mem ∧
      (∀ j < callCore.G, Spec.Aes.bytesAt s'.mem (bufAddr callCore B j) 16 =
        Spec.Camellia.cipher (Spec.Camellia.subkeysOfWords k.1 k.2)
          (Spec.Aes.bytesAt s.mem (bufAddr callCore B j) 16)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨R, ws⟩ := k
  obtain ⟨hready, hx26, hx22⟩ := hr
  simp only at hx26
  have hRr := hready.rounds
  simp only at hRr
  obtain ⟨s₁, e₁, r₁, o₁, m₁, rd₁, wr₁⟩ := Modes.AArch64.movR_ok s .x20 .x30
  obtain ⟨s₂, e₂, r₂, o₂, m₂, rd₂, wr₂⟩ := Modes.AArch64.movR_ok s₁ .x0 .x26
  obtain ⟨s₃, e₃, r₃, o₃, m₃, rd₃, wr₃⟩ := Modes.AArch64.movR_ok s₂ .x1 sb
  obtain ⟨s₄, e₄, r₄, o₄, m₄, rd₄, wr₄⟩ := Modes.AArch64.movz_ok s₃ .x2 (v := core.total) (by decide)
  obtain e : runBlock isa [movR .x20 .x30, movR .x0 .x26, movR .x1 sb,
      .movz .x .x2 (BitVec.ofNat 16 core.total) 0] s = some s₄ := by
    rw [show [movR .x20 .x30, movR .x0 .x26, movR .x1 sb, Instr.movz .x .x2 (BitVec.ofNat 16 core.total) 0] =
        [movR .x20 .x30] ++ ([movR .x0 .x26] ++ ([movR .x1 sb] ++
        [.movz .x .x2 (BitVec.ofNat 16 core.total) 0])) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃,
      Option.bind_some, e₄]
  obtain g₄ : ∀ r, r ≠ .x20 → r ≠ .x0 → r ≠ .x1 → r ≠ .x2 → s₄.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [o₄ _ h4, o₃ _ h3, o₂ _ h2, o₁ _ h1]
  obtain x0₄ : s₄.gpr .x0 = BitVec.ofNat 64 R := by
    rw [o₄ _ (by decide), o₃ _ (by decide), r₂, o₁ _ (by decide), hx26]
  obtain x1₄ : s₄.gpr .x1 = B := by rw [o₄ _ (by decide), r₃, o₂ _ (by decide), o₁ _ (by decide), hB]
  have x2₄ : s₄.gpr .x2 = BitVec.ofNat 64 core.total := r₄
  obtain x20₄ : s₄.gpr .x20 = s.gpr .x30 := by rw [o₄ _ (by decide), o₃ _ (by decide), o₂ _ (by decide), r₁]
  obtain mem₄ : s₄.mem = s.mem := by rw [m₄, m₃, m₂, m₁]
  obtain rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂, rd₁]
  obtain wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂, wr₁]
  show WP isa cryptCall s _
  refine WP.seq (WP.of_runBlock ⟨s₄, e, ?_⟩)
  obtain hH : Holds layout s.mem B R ws .encrypt := holds_of_ready hready .encrypt
  obtain g0 : ((s₄.callEntry.withRegions [] [⟨B, 8 * core.total⟩]).gpr .x0).toNat = R := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ VG.AArch64.linkRegs), x0₄,
      toNat_rounds hRr]
  obtain g1 : (s₄.callEntry.withRegions [] [⟨B, 8 * core.total⟩]).gpr .x1 = B := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x1 ∉ VG.AArch64.linkRegs), x1₄]
  obtain g2 : ((s₄.callEntry.withRegions [] [⟨B, 8 * core.total⟩]).gpr .x2).toNat = 418 := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x2 ∉ VG.AArch64.linkRegs), x2₄,
      toNat_total]
  obtain hm₀ : (s₄.callEntry.withRegions [] [⟨B, 8 * core.total⟩]).mem = s.mem := by
    rw [State.withRegions_mem, State.callEntry_mem, mem₄]
  obtain w : WP isa (.call "vg_camellia_encrypt_prepared" encryptPrepared) s₄ fun s' =>
      s'.rd = s₄.rd ∧ s'.wr = s₄.wr ∧ (∀ r ∈ preserved, r ≠ .x30 → s'.gpr r = s₄.gpr r) ∧
      Frame [⟨B, 8 * core.total⟩] s₄.mem s'.mem ∧
      Spec.Camellia.blocksAt s'.mem (B + BitVec.ofNat 64 layout.buf) layout.blocks =
        Spec.Camellia.ecb (Spec.Camellia.subkeysOfWords R ws) .encrypt
          (Spec.Camellia.blocksAt s.mem (B + BitVec.ofNat 64 layout.buf) layout.blocks) ∧
      Keeps B core.total [(768, 16)] s.mem s'.mem := by
    refine WP.call (k := cryptAArch64) crypt_correct (rd := []) (wr := [⟨B, 8 * core.total⟩]) ?_
      (Covers.append_left Covers.nil (Covers.right (by rw [wr₄']; exact ws_covers hs)))
      (by rw [wr₄']; exact ws_covers hs) (fun s' hrd hwr _ hf hg _ hpost => ⟨hrd, hwr, hg, hf, ?_⟩)
      (by lit_decide)
    · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
      · rw [State.withRegions_wr, g1, g2]; rfl
      · rw [g1, g2]; have := hs.fit; rw [total_eq] at this; omega_using [this]
      · rw [g0]; exact hRr
      · rw [g2, size_eq]
      · rw [g0, g1, hm₀]; exact ⟨ws, hH⟩
    · obtain ⟨hE, hK⟩ := hpost
      change (∀ w, Holds layout _ _ _ w _ → _) at hE
      change Keeps _ _ _ _ s'.mem at hK
      rw [hm₀, g0, g1] at hE
      rw [hm₀, g1, g2] at hK
      exact ⟨hE ws hH, hK⟩
  obtain ⟨t₅, s₅, e₅, rd₅, wr₅, g₅, f₅, hE, hK⟩ := w
  refine WP.seq ⟨t₅, s₅, e₅, ?_⟩
  obtain x22₅ : s₅.gpr .x22 = B := by
    rw [g₅ _ (by simp [preserved]) (by decide), g₄ _ (by decide) (by decide) (by decide) (by decide), hx22]
  obtain x20₅ : s₅.gpr .x20 = s.gpr .x30 := by rw [g₅ _ (by simp [preserved]) (by decide), x20₄]
  obtain ⟨s₆, e₆, r₆, o₆, m₆, rd₆, wr₆⟩ := Modes.AArch64.movR_ok s₅ sb .x22
  obtain ⟨s₇, e₇, -, o₇, m₇, rd₇, wr₇⟩ := Modes.AArch64.movR_ok s₆ .x30 .x20
  obtain e' : runBlock isa [movR sb .x22, movR .x30 .x20] s₅ = some s₇ := by
    rw [show [movR sb .x22, movR .x30 .x20] = [movR sb .x22] ++ [movR .x30 .x20] from rfl, runBlock_app, e₆,
      Option.bind_some, e₇]
  obtain g₇ : ∀ r, r ≠ sb → r ≠ .x30 → s₇.gpr r = s₅.gpr r := fun r h1 h2 => by rw [o₇ _ h2, o₆ _ h1]
  obtain mem₇ : s₇.mem = s₅.mem := by rw [m₇, m₆]
  obtain kept : ∀ r, r ∈ [Reg.x22, .x23, .x24, .x26] → s₇.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [g₇ _ (by decide) (by decide), g₅ _ (by simp [preserved]) (by decide),
        g₄ _ (by decide) (by decide) (by decide) (by decide)]
  rw [← mem₄] at hK
  obtain fbuf := frame_of_keeps f₅ hK (by decide) (by decide)
  rw [mem₄] at fbuf
  refine WP.of_runBlock ⟨s₇, e', ?_, kept _ (by simp), kept _ (by simp), ⟨?_, ?_, ?_⟩, ?_, fun j hj => ?_, ?_, ?_⟩
  · rw [o₇ _ (by decide), r₆, x22₅]
  · rw [mem₇]
    exact hready.frame (s := s) (s' := s₅) fbuf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inr fun _ h => h
  · rw [kept _ (by simp), hx26]
  · rw [kept _ (by simp), hx22]
  · rw [mem₇]
    exact fbuf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Offset.sub_base B (by decide : 768 + 16 ≤ 8 * core.slots)⟩
  · have hj0 : j = 0 := by change j < 1 at hj; omega_using [hj]
    subst hj0
    rw [mem₇]
    exact blocks_of_ecb hE
  · rw [rd₇, rd₆, rd₅, rd₄']
  · rw [wr₇, wr₆, wr₅, wr₄']

/-! ## The modes' core -/

def coreSpec : CoreSpec callCore where
  Key := Nat × List (BitVec 64)
  cipher k := Spec.Camellia.cipher (Spec.Camellia.subkeysOfWords k.1 k.2)
  KeyArgs := VG.Proof.Camellia.AArch64.KeyArgs
  Ready := CallReady
  cipher_len _ _ := by simp [Spec.Camellia.cipher]
  layout := ⟨by decide, by decide, by decide, by decide, by decide⟩
  keyRegs_ok := by decide
  regs_ok := by decide
  keyArgs_congr h hr hrd hwr _ hf := VG.Proof.Camellia.AArch64.keyArgs_congr h hr hrd hwr hf
  ready_frame h hf hd _ hg :=
    ⟨h.1.frame hf hd, (hg .x26 (by decide)).trans h.2.1, (hg .x22 (by decide)).trans h.2.2⟩
  prepare_wp hb hs hr hk := callPrepare_wp hb hs hr hk
  crypt_wp hb hs hr := callCrypt_wp hb hs hr

abbrev blockSpec : BlockSpec callCore := coreSpec.toBlock rfl

/-- Code none of whose instructions, nor its callees', writes `r`, which a
call does not change either, keeps `r`. -/
theorem keepsReg_of_allInstrs {r : Reg} {c : Prog isa} (hc : c.allInstrs (fun i => !clobbers i r) = true)
    (hl : r ∉ VG.AArch64.linkRegs) : KeepsReg r c := fun _ _ _ he => by
  rw [Code.allInstrs_eq] at hc
  exact Exec.gpr (fun i hi => by simpa using List.all_eq_true.mp hc i hi) he (.inr hl)

theorem keeps_x19 : KeepsReg .x19 callCore.prepare ∧ KeepsReg .x19 callCore.crypt :=
  ⟨keepsReg_of_allInstrs (by lit_decide) (by decide), keepsReg_of_allInstrs (by lit_decide) (by decide)⟩

/-- The calls' first blocks keep the return address in `x20`. -/
theorem prepareHead_ok (s : State) : ∃ s', runBlock isa [movR .x20 .x30, movR .x22 sb, movR .x26 .x1,
    movR .x2 sb, .movz .x .x3 (BitVec.ofNat 16 core.total) 0] s = some s' ∧ s'.gpr .x20 = s.gpr .x30 := by
  obtain ⟨s₁, e₁, r₁, -, -, -, -⟩ := Modes.AArch64.movR_ok s .x20 .x30
  obtain ⟨s₂, e₂, -, o₂, -, -, -⟩ := Modes.AArch64.movR_ok s₁ .x22 sb
  obtain ⟨s₃, e₃, -, o₃, -, -, -⟩ := Modes.AArch64.movR_ok s₂ .x26 .x1
  obtain ⟨s₄, e₄, -, o₄, -, -, -⟩ := Modes.AArch64.movR_ok s₃ .x2 sb
  obtain ⟨s₅, e₅, -, o₅, -, -, -⟩ := Modes.AArch64.movz_ok s₄ .x3 (v := core.total) (by decide)
  refine ⟨s₅, ?_, by rw [o₅ _ (by decide), o₄ _ (by decide), o₃ _ (by decide), o₂ _ (by decide), r₁]⟩
  rw [show [movR .x20 .x30, movR .x22 sb, movR .x26 .x1, movR .x2 sb,
      Instr.movz .x .x3 (BitVec.ofNat 16 core.total) 0] = [movR .x20 .x30] ++ ([movR .x22 sb] ++
      ([movR .x26 .x1] ++ ([movR .x2 sb] ++ [.movz .x .x3 (BitVec.ofNat 16 core.total) 0]))) from rfl,
    runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃,
    Option.bind_some, runBlock_app, e₄, Option.bind_some, e₅]

theorem cryptHead_ok (s : State) : ∃ s', runBlock isa [movR .x20 .x30, movR .x0 .x26, movR .x1 sb,
    .movz .x .x2 (BitVec.ofNat 16 core.total) 0] s = some s' ∧ s'.gpr .x20 = s.gpr .x30 := by
  obtain ⟨s₁, e₁, r₁, -, -, -, -⟩ := Modes.AArch64.movR_ok s .x20 .x30
  obtain ⟨s₂, e₂, -, o₂, -, -, -⟩ := Modes.AArch64.movR_ok s₁ .x0 .x26
  obtain ⟨s₃, e₃, -, o₃, -, -, -⟩ := Modes.AArch64.movR_ok s₂ .x1 sb
  obtain ⟨s₄, e₄, -, o₄, -, -, -⟩ := Modes.AArch64.movz_ok s₃ .x2 (v := core.total) (by decide)
  refine ⟨s₄, ?_, by rw [o₄ _ (by decide), o₃ _ (by decide), o₂ _ (by decide), r₁]⟩
  rw [show [movR .x20 .x30, movR .x0 .x26, movR .x1 sb, Instr.movz .x .x2 (BitVec.ofNat 16 core.total) 0] =
      [movR .x20 .x30] ++ ([movR .x0 .x26] ++ ([movR .x1 sb] ++
      [.movz .x .x2 (BitVec.ofNat 16 core.total) 0])) from rfl,
    runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃,
    Option.bind_some, e₄]

/-- The calls' last block moves the return address back. -/
theorem tail_ok (s : State) :
    ∃ s', runBlock isa [movR sb .x22, movR .x30 .x20] s = some s' ∧ s'.gpr .x30 = s.gpr .x20 := by
  obtain ⟨s₁, e₁, -, o₁, -, -, -⟩ := Modes.AArch64.movR_ok s sb .x22
  obtain ⟨s₂, e₂, r₂, -, -, -, -⟩ := Modes.AArch64.movR_ok s₁ .x30 .x20
  refine ⟨s₂, ?_, by rw [r₂, o₁ _ (by decide)]⟩
  rw [show [movR sb .x22, movR .x30 .x20] = [movR sb .x22] ++ [movR .x30 .x20] from rfl, runBlock_app, e₁,
    Option.bind_some, e₂]

theorem prepareEncrypt_keeps_x20 : prepareEncrypt.allInstrs (fun i => !clobbers i .x20) = true := by
  lit_decide

theorem encryptPrepared_keeps_x20 : encryptPrepared.allInstrs (fun i => !clobbers i .x20) = true := by
  lit_decide

end VG.Proof.Camellia.AArch64.Serial

end

end

/-!
# Camellia's core for the modes on AArch64: the return address across the calls

The core's `prepare` and `crypt` call `vg_camellia_prepare_keys`
and `vg_camellia_crypt_prepared`, which overwrite the return address (`x30`): each
keeps it in `v28`, which no instruction of the callees writes, and moves it
back (`prepare_keeps_x30`, `crypt_keeps_x30`). The serial core's calls of
`vg_camellia_prepare_encrypt_keys` and `vg_camellia_encrypt_prepared` keep
it in `x20` instead (`serialPrepare_keeps_x30`, `serialCrypt_keeps_x30`). `camellia_keeps_x30` proves that
a mode's code keeps `x30`, the core's code being the only code with calls.
-/

@[expose] public section

namespace VG.Proof.Camellia.AArch64

open VG VG.AArch64 VG.Impl.Camellia.AArch64
open VG.Impl.Aes.AArch64 (sb movR)
open VG.Proof.Modes.AArch64 (KeepsReg runBlock_app dup_ok umov_ok extract_ofVDwords vSafe keepsV_of_vSafe)

/-- The block's state from `s`, as a function. -/
theorem block_det {is : List Instr} {s s₁ s' : State} {t : List Leak} (h : Exec isa (.block is) s t s')
    (e : runBlock isa is s = some s₁) : s' = s₁ := by
  have w : WP isa (.block is) s fun x => x = s₁ := WP.of_runBlock ⟨s₁, e, rfl⟩
  obtain ⟨t', s'', he, rfl⟩ := w
  exact (Exec.det h he).2

theorem call_keeps_x30 {r : Reg} {args : List Instr} {name : String} {c : Prog isa}
    (hargs : ∀ i ∈ (keepHeadWith r).tail ++ args, vdstOf i ≠ some .v28) (hc : vSafe .v28 c = true)
    {s s₁ s₂ s' : State} {t₁ t₂ t₃ : List Leak}
    (hA : Exec isa (.block (keepHeadWith r ++ args)) s t₁ s₁) (hC : Exec isa (.call name c) s₁ t₂ s₂)
    (hB : Exec isa (.block keepTail) s₂ t₃ s') : s'.gpr .x30 = s.gpr .x30 := by
  have v28₁ : s₁.v .v28 = ofVDwords (s.gpr .x30) (s.gpr .x30) := by
    have w : WP isa (.block ([.vop (.dup .d2 .v28 .x30)] ++ ((keepHeadWith r).tail ++ args))) s fun x => x = s₁ :=
      ⟨t₁, s₁, hA, rfl⟩
    obtain ⟨_, u, hu, w⟩ := WP.block_append_iff.mp w
    obtain ⟨t', u', hu', hq⟩ := w
    rw [block_det hu (dup_ok s .v28 .x30)] at hu'
    rw [← hq, Exec.vec (c := .block ((keepHeadWith r).tail ++ args)) hargs hu', RegUpd.v_setV_self]
  have v28₂ : s₂.v .v28 = s₁.v .v28 := keepsV_of_vSafe (c := .call name c) hc _ _ _ hC
  obtain ⟨s'', e'', -, r28, -⟩ := keepTail_ok s₂
  rw [block_det hB e'', r28, v28₂, v28₁, extract_ofVDwords]

theorem vsafe28 {c : Prog isa} (h : keepsVs c = true) : vSafe .v28 c = true := by
  simp only [keepsVs, Bool.and_eq_true] at h
  exact h.1.1.2

theorem prepare_keeps_x30 (d : Dir) : KeepsReg .x30 (dirCore d).prepare := by
  intro s t s' h
  cases h with
  | seq hA hR =>
    cases hR with
    | seq hC hB => exact call_keeps_x30 (by cases d <;> decide) (vsafe28 prepareKeys_vsafe) hA hC hB

theorem crypt_keeps_x30 (d : Dir) : KeepsReg .x30 (dirCore d).crypt := by
  intro s t s' h
  cases h with
  | seq hA hR =>
    cases hR with
    | seq hC hB => exact call_keeps_x30 (r := .x4) (by decide) (vsafe28 cryptPrepared_vsafe) hA hC hB

/-- A call of code that does not write `x20`, between a block that moves
the return address to `x20` and one that moves it back. -/
theorem serialCall_keeps_x30 {A : List Instr} {name : String} {c : Prog isa}
    (hA : ∀ s, ∃ s', runBlock isa A s = some s' ∧ s'.gpr .x20 = s.gpr .x30)
    (hc : c.allInstrs (fun i => !clobbers i .x20) = true) :
    KeepsReg .x30 (.seq (.block A) (.seq (.call name c) (.block [movR sb .x22, movR .x30 .x20]))) := by
  intro s t s' h
  cases h with
  | seq hA' hR =>
    cases hR with
    | seq hC hB =>
      obtain ⟨s₁, e₁, x20₁⟩ := hA s
      rw [block_det hA' e₁] at hC
      obtain ⟨s₃, e₃, x30₃⟩ := Serial.tail_ok _
      rw [block_det hB e₃, x30₃, Serial.keepsReg_of_allInstrs (c := .call name c) hc (by decide) _ _ _ hC, x20₁]

theorem serialPrepare_keeps_x30 : KeepsReg .x30 Serial.callCore.prepare :=
  serialCall_keeps_x30 Serial.prepareHead_ok Serial.prepareEncrypt_keeps_x20

theorem serialCrypt_keeps_x30 : KeepsReg .x30 Serial.callCore.crypt :=
  serialCall_keeps_x30 Serial.cryptHead_ok Serial.encryptPrepared_keeps_x20

/-- `WP.gprs` for `x30`, from `KeepsReg` rather than the absence of calls. -/
theorem WP.gprs' {c : Prog isa} {s : State} {Q : State → Prop} (hk : KeepsReg .x30 c) (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ ∀ r ∈ [Reg.x30], s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hk _ _ _ he⟩

/-- `KeepsReg .x30` of a mode's code: its structure, down to the core's code
and blocks that do not write `x30`. -/
tactic_template "camellia_keeps_x30" : tactic => `(tactic| repeat (first
  | with_reducible exact serialPrepare_keeps_x30
  | with_reducible exact serialCrypt_keeps_x30
  | with_reducible exact crypt_keeps_x30 _
  | with_reducible exact prepare_keeps_x30 _
  | apply KeepsReg.seq
  | apply KeepsReg.ite
  | apply KeepsReg.loop
  | exact Modes.AArch64.keepsReg_of_regSafe (by decide)))

theorem ctr_keeps_x30 : KeepsReg .x30 ctr := by camellia_keeps_x30
theorem cbcEncryptChained_keeps_x30 : KeepsReg .x30 cbcEncryptChained := by camellia_keeps_x30
theorem cbcDecryptChained_keeps_x30 : KeepsReg .x30 cbcDecryptChained := by camellia_keeps_x30
theorem ofb_keeps_x30 : KeepsReg .x30 ofb := by camellia_keeps_x30
theorem cfbEncrypt_keeps_x30 : KeepsReg .x30 cfbEncrypt := by camellia_keeps_x30
theorem cfbDecrypt_keeps_x30 : KeepsReg .x30 cfbDecrypt := by camellia_keeps_x30

end VG.Proof.Camellia.AArch64

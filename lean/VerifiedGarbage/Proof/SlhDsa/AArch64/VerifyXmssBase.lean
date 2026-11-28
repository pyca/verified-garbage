module

-- separate module: the entry and the invariant `XK`, which the later phases' proofs do not change

public import VerifiedGarbage.Proof.SlhDsa.AArch64.XmssDigits
public import VerifiedGarbage.Proof.SlhDsa.AArch64.TreeBase
public import VerifiedGarbage.Proof.SlhDsa.AArch64.TopShared
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
public import VerifiedGarbage.Impl.SlhDsa.AArch64.Verify
public import VerifiedGarbage.Proof.SlhDsa.Lemmas
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64, `xmssPk`: what holds throughout, and the prologue

`xmssPk(scratch = x0, idx = x1, sig = x2)` (`Impl/SlhDsa/AArch64/Verify.lean`)
saves the caller's `x19`–`x26` and `x30` in frame 1 (`slotsX`), keeps
`scratch`, `idx` and `sig` in `x19`–`x21` and computes the digits of the
message at `oMsg` (`entry_ok`). Throughout (`XK`), it keeps those, the
caller's `x27` and `x28`, the stack pointer, the permissions, the low halves
of `v8`–`v15`, `Env` and the saved registers, and changes memory only in
`changes p S`.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.XmssPk

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Proof.SlhDsa.AArch64.TreeBase (in_scr in_scr' disj_scr env_frame regions_scr bytesAt_frame wp_mov wp_movz)

variable {p : Params}

/-- Frame 1's slots of the registers `xmssPk` saves. -/
def slotsX : List (Reg × Nat) :=
  [(.x19, 1152), (.x20, 1160), (.x21, 1168), (.x22, 1176), (.x23, 1184), (.x24, 1192), (.x25, 1200),
    (.x26, 1208), (.x30, 1216)]

theorem xpro_eq : Impl.SlhDsa.AArch64.Verify.xpro =
    Spill.saveCode .x0 slotsX ++ ([.addImm .x .x19 .x0 0, .addImm .x .x20 .x1 0, .addImm .x .x21 .x2 0] : List Instr) :=
  rfl

theorem slotsX_in : ∀ q ∈ slotsX, 1152 ≤ q.2 ∧ q.2 + 8 ≤ 1224 := by decide

theorem slotsX_ok : ∀ q ∈ slotsX, q.2 % 8 = 0 ∧ q.2 < 32768 := by decide

/-- The saved slots, past a frame apart from them. -/
theorem saved_keep {σ : State} {S : Addr} {m : Mem} (h : Spill.Saved S σ.gpr slotsX m)
    {rs : List Region} {m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨at' S 1152, 72⟩ r) : Spill.Saved S σ.gpr slotsX m' :=
  h.frame hf fun q hq r hr => (hd r hr).sub_left (by
    have := slotsX_in q hq
    exact Offset.sub S this.1 (by omega))

/-- What holds throughout `xmssPk`, from its entry state `σ`, with `scratch`
at `S`, the signature at `sig`, and the digits `D`. -/
structure XK (p : Params) (σ : State) (S sig : Addr) (pk a : List Byte) (D : List Nat) (t : State) : Prop where
  x19 : t.gpr .x19 = S
  x20 : t.gpr .x20 = σ.gpr .x1
  x21 : t.gpr .x21 = sig
  kept : ∀ r ∈ [Reg.x27, .x28], t.gpr r = σ.gpr r
  sp : t.sp = σ.sp
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr
  vcs : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (σ.v r).extractLsb' 0 64
  env : Env p t.mem S pk a
  saved : Spill.Saved S σ.gpr slotsX t.mem
  dig : ∀ i < p.len, digitAt t.mem S i = D.getD i 0
  frame : Frame (changes p S) σ.mem t.mem

/-- The prologue and the digits. -/
theorem entry_ok (hz : Sz p) {σ : State} {S : Addr} (hS : σ.gpr .x0 = S)
    (hR : Regions σ S [⟨σ.gpr .x2, p.xmssSigLen⟩] ⟨S, 0⟩) {pk a : List Byte} (hE : Env p σ.mem S pk a) :
    WP isa (.block (Impl.SlhDsa.AArch64.Verify.xpro ++ Impl.SlhDsa.AArch64.Xmss.digits ⟨p.n, p.len⟩ ++
      ([.movz .x .x22 0 0] : List Instr))) σ fun t =>
      XK p σ S (σ.gpr .x2) pk a (wotsDigits p (bytesAt σ.mem (at' S Layout.oMsg) p.n)) t ∧
        t.gpr .x22 = BitVec.ofNat 64 0 := by
  have hn32 := hz.n32
  have hl := hz.len
  have eD : Layout.oDigits = 1856 := rfl
  have eM : Layout.oMsg = 1984 := rfl
  have hwS := regions_scr hR
  rw [xpro_eq, List.append_assoc, List.append_assoc]
  refine Spill.save_ok slotsX_ok (fun q hq => by
    rw [hS]; have := slotsX_in q hq; exact in_scr hwS (by omega)) ?_
  have hsv : Spill.Saved S σ.gpr slotsX (Spill.saveMem σ.mem (σ.gpr .x0) σ.gpr slotsX) := by
    rw [← hS]; exact Spill.saveMem_saved (by decide) _ _ _
  have hf₁ : Frame [⟨at' S 1152, 72⟩] σ.mem (Spill.saveMem σ.mem (σ.gpr .x0) σ.gpr slotsX) := by
    rw [← hS]; exact Spill.saveMem_frame slotsX_in (by decide) _ _ _
  generalize Spill.saveMem σ.mem (σ.gpr .x0) σ.gpr slotsX = m₁ at hsv hf₁
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun t₁ e₁ => wp_mov fun t₂ e₂ => wp_mov fun t₃ e₃ => ?_
  have h19 : t₃.gpr .x19 = S := by rw [e₃.other _ (by decide), e₂.other _ (by decide), e₁.gpr]; exact hS
  have hm₃ : t₃.mem = m₁ := by rw [e₃.mem, e₂.mem, e₁.mem]
  have hw₃ : (⟨S, 65536⟩ : Region) ∈ t₃.wr := by rw [e₃.wr, e₂.wr, e₁.wr]; exact hwS
  have hg₃ : ∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → t₃.gpr r = σ.gpr r := fun r h19 h20 h21 => by
    rw [e₃.other _ h21, e₂.other _ h20, e₁.other _ h19]
  refine Xmss.digits_ok hz h19 hw₃ fun t₄ hdig hfd hg₄ hsp₄ hrd₄ hwr₄ hv₄ => ?_
  refine wp_movz fun t₅ e₅ => WP.block_nil ?_
  rw [hm₃] at hdig hfd
  have hm₅ : t₅.mem = t₄.mem := e₅.mem
  have hg₅ : ∀ r, r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x22 → t₅.gpr r = t₃.gpr r :=
    fun r h9 h10 h11 h12 h13 h22 => by rw [e₅.other _ h22, hg₄ r h9 h10 h11 h12 h13]
  have hd₁ : ∀ {o l : Nat}, (o + l ≤ 1152 ∨ 1224 ≤ o) → o + l ≤ 65536 →
      ∀ r ∈ [(⟨at' S 1152, 72⟩ : Region)], Region.Disjoint ⟨at' S o, l⟩ r := fun h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact disj_scr S h₁ h₂ (by omega)
  have hd₂ : ∀ {o l : Nat}, (o + l ≤ Layout.oDigits ∨ Layout.oDigits + p.len ≤ o) → o + l ≤ 65536 →
      ∀ r ∈ [(⟨at' S Layout.oDigits, p.len⟩ : Region)], Region.Disjoint ⟨at' S o, l⟩ r := fun h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact disj_scr S h₁ h₂ (by rw [eD, hl]; omega)
  have hM : bytesAt m₁ (at' S Layout.oMsg) p.n = bytesAt σ.mem (at' S Layout.oMsg) p.n :=
    bytesAt_frame hf₁ (hd₁ (by rw [eM]; omega) (by rw [eM]; omega)) (by omega)
  have hF : Frame ([(⟨at' S 1152, 72⟩ : Region)] ++ [⟨at' S Layout.oDigits, p.len⟩]) σ.mem t₅.mem := by
    rw [hm₅]
    exact (hf₁.mono fun r hr => List.mem_append_left _ hr).trans (hfd.mono fun r hr => List.mem_append_right _ hr)
  have hkeep : ∀ {o l : Nat}, (1224 ≤ o ∧ o + l ≤ Layout.oDigits) ∨ (Layout.oDigits + p.len ≤ o ∧ o + l ≤ 65536) →
      ∀ r ∈ [(⟨at' S 1152, 72⟩ : Region)] ++ [⟨at' S Layout.oDigits, p.len⟩], Region.Disjoint ⟨at' S o, l⟩ r := by
    intro o l ho r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hd₁ (by omega) (by rw [eD] at ho; omega) r hr
    · exact hd₂ (by omega) (by rw [eD] at ho; omega) r hr
  refine ⟨⟨?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, fun r _ => ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [hg₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h19]
  · rw [hg₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), e₃.other _ (by decide),
      e₂.gpr, e₁.other _ (by decide)]
  · rw [hg₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), e₃.gpr, e₂.other _ (by decide),
      e₁.other _ (by decide)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
      exact (hg₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (hg₃ _ (by decide) (by decide) (by decide))
  · rw [e₅.sp, hsp₄, e₃.sp, e₂.sp, e₁.sp]
  · rw [e₅.rd, hrd₄, e₃.rd, e₂.rd, e₁.rd]
  · rw [e₅.wr, hwr₄, e₃.wr, e₂.wr, e₁.wr]
  · rw [e₅.v, hv₄, e₃.v, e₂.v, e₁.v]
  · exact env_frame hn32 hE hF fun ho₁ ho₂ => hkeep (.inr ⟨by rw [eD, hl]; simp only [Layout.oA] at ho₁; omega,
      by simp only [Layout.oN] at ho₂; omega⟩)
  · rw [hm₅]
    exact saved_keep hsv hfd fun r hr => hd₂ (by rw [eD]; omega) (by omega) r hr
  · intro i hi; simp only [digitAt]; rw [hm₅]; rw [← hM]; exact hdig i hi
  · refine hF.sub fun r hr => ?_
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨at' S Layout.oVars, 4 * Layout.frameLen⟩, by simp [changes],
        Offset.sub S (by simp [Layout.oVars]) (by simp [Layout.oVars, Layout.frameLen])⟩
    · exact ⟨⟨at' S Layout.oDigits, 128⟩, by simp [changes], Region.sub_prefix (by rw [hl]; omega)⟩
  · rw [e₅.gpr]; rfl

end VG.Proof.SlhDsa.AArch64.XmssPk

module

public import VerifiedGarbage.Proof.Ffdh.X86_64.SetupCT
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupWs
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.SetupCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH on x86-64: allocate and enter a workspace in constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64.Crt (wsEnd wsNew)
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

private theorem wp_seqs_split {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ [])
    {s : State} {Q : State → Prop} (h : WP isa (seqs (a ++ b)) s Q) :
    WP isa (seqs a) s fun t => WP isa (seqs b) t Q := by
  obtain ⟨tr, t, he, hq⟩ := h
  exact WP.seq_iff.mp ⟨tr, t, exec_seqs_append ha hb he, hq⟩

abbrev wsHead : List Instr := ([.mov .rdx (.reg .rdi)] : List Instr) ++ wsEnd

private abbrev MPub.wp (a : MPub) : WPub := ⟨a.B, a.Z, inner a.w, a.len⟩

private theorem m1_wn {sp sl : Nat} (hsl : sl < 32) (hne : sl ≠ sWs) (a : MPub) (s : State)
    (h : M1 sp sl a s) : WP isa (.block wsHead) s (WN sWs sl a.wp) := by
  obtain ⟨bs, hO, hlen, _, _, _, hlen1, hlenw, _⟩ := h
  have hroom := hO.room
  have hw28 := hO.w28
  have hw2 := hO.w2
  have hwx : wsWords a.len ≤ a.w := by unfold wsWords; omega
  have hsl8 : slot (wsWords a.len) 8 ≤ slot a.w 8 := by unfold slot hdrBytes; omega
  unfold wsHead
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rdx] (Q := fun t => t.gpr .rdx = a.B ∧ t.mem = s.mem)
    (by xrun [hO.rdi]) rfl) fun s₁ ⟨⟨hdx, hm₁⟩, k₁⟩ => ?_
  refine WP.mono (wsEnd_ok (wx := a.w) (hO.scr.congr k₁.2.2) hdx (by rw [hm₁]; exact hO.hw)
    (by rw [hm₁]; exact hO.harr _ (by decide)) (by omega)) fun t ⟨hax, hm₂, k₂⟩ => ?_
  have K := k₁.trans k₂
  exact ⟨hO.scr.congr K.2.2, (K.gpr (by decide)).trans hO.rdi, hax,
    by rw [hm₂, hm₁]; exact hlen, by decide, hsl, Ne.symm hne, by change a.len < 2 ^ 32; omega,
    by change 256 ≤ inner a.w; unfold inner slot hdrBytes; omega,
    by change inner a.w + slot (wsWords a.len) 8 ≤ a.Z; omega⟩

private def WS1 (sp sl : Nat) (a : MPub) (s : State) : Prop :=
  WN sWs sl a.wp s ∧ WP isa (seqs (wsNew sWs sl ++ ([.block [enter]] : List (Prog isa)))) s (M2 sp sl a)

private def WS2 (sp sl : Nat) (a : MPub) (s : State) : Prop :=
  s.gpr .rdi = a.B ∧ WP isa (.block [enter]) s (M2 sp sl a)

private theorem ws1_ws2 {sp sl : Nat} (a : MPub) (s : State) (h : WS1 sp sl a s) :
    WP isa (seqs (wsNew sWs sl)) s (WS2 sp sl a) := by
  obtain ⟨⟨hs, hdi, hax, hlen, hws, hsl, hne, hlen', ho, hZ⟩, hw⟩ := h
  have hdir := WP.mono (wsNew_ok hs hdi hax hws hsl hne hlen hlen' ho hZ)
    fun _ ⟨_, _, _, _, hdi', _, _⟩ => hdi'
  exact WP.and hdir (wp_seqs_split (by simp [wsNew]) (by simp) hw)

/-- The public length determines the max(2, ceil(len/8)) branch. -/
theorem wsSetup_ct {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) (hspW : sp ≠ sWs) (hslW : sl ≠ sWs)
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (wsB1 sWs sl)) hc).isSome = true) :
    RelCT isa (Two (M1 sp sl)) (seqs (wsSetup sl ++ ([.block [enter]] : List (Prog isa)))) fun _ _ => True := by
  change RelCT isa (Two (M1 sp sl))
    (.seq (.block wsHead) (seqs (wsNew sWs sl ++ ([.block [enter]] : List (Prog isa))))) _
  refine RelCT.seq (R := Two (WS1 sp sl))
    (two_piece [.rdi] (pins_of (fun a _ => a.B) fun a s h r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact h.choose_spec.1.rdi) (by taint_decide) fun a s h => ?_) ?_
  · exact WP.and (m1_wn hsl hslW a s h) (WP.seq_iff.mp (m1_m2 hsp hsl hspW hslW a s h))
  refine RelCT.seqs_append (by simp [wsNew]) (by simp) (RelCT.seq (R := Two (WS2 sp sl))
    (two_post (two_map MPub.wp (fun _ _ h => h.1) (wsNew_ct hT)) ws1_ws2) ?_)
  exact (two_piece (Φ := WS2 sp sl) [.rdi] (pins_of (fun (a : MPub) _ => a.B) fun a s h r hr => by
    simp only [List.mem_singleton] at hr
    subst hr
    exact h.1) (by taint_decide) fun _ _ h => h.2).mono (fun _ _ h => h) (fun _ _ _ => True.intro)

end VG.Proof.Ffdh.X86_64

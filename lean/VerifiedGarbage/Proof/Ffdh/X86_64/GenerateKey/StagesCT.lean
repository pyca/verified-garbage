module
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Start

import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.MainCT
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.SetupCT
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Start
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.MainCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.SetupCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH key generation on x86-64: public entry and modulus validation -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (stk ws)

def CR (p : GkP) (s : State) : Prop := gkPre s ∧ gkOf s = p

def E1 (p : GkP) (s : State) : Prop := ∃ rb, Base p rb s ∧ s.gpr .rdi = p.B

def CE (p : GkP) (s : State) : Prop := E1 p s ∧ s.zf = some p.mv ∧
  word s.mem p.B (8 * sG) = off p.dp p.k ∧ word s.mem p.B (8 * sQ) = off p.dp (2 * p.k)

private def loads : List Instr :=
  [.mov .rax (.mem (stk 4)), .mov .r10 (.mem (stk 1)), .mov .r11 (.mem (stk 2))]

private def entryTail : List Instr := save .rax ++
  [.store (ws .rax sX) .rdi, .store (ws .rax sY) .rdx, .store (ws .rax sDom) .r8,
    .store (ws .rax sDomLen) .r9, .store (ws .rax sK) .r10, .store (ws .rax sRand) .r11, .mov .rdi (.reg .rax)]

private def EL (p : GkP) (s : State) : Prop := s.gpr .rax = p.B ∧ WP isa (.block entryTail) s (E1 p)

private theorem loads_ok (s : State) (c : GkCtx s) : WP isa (.block loads) s
    fun t => t.gpr .rax = stackArg s 3 := by
  have h3 : InRegions (s.rd ++ s.wr) (off (s.gpr .rsp) 32) 8 := c.ha 3 (by decide)
  have h0 : InRegions (s.rd ++ s.wr) (off (s.gpr .rsp) 8) 8 := c.ha 0 (by decide)
  have h1 : InRegions (s.rd ++ s.wr) (off (s.gpr .rsp) 16) 8 := c.ha 1 (by decide)
  unfold loads stk
  xrun [State.ea, hdrOff, h3, h0, h1]
  rfl

private theorem entry_ct : RelCT isa (Two CR) (.block VG.Impl.Ffdh.X86_64.Domain.GenerateKey.entry) (Two E1) := by
  change RelCT isa (Two CR) (.block (loads ++ entryTail)) (Two E1)
  refine RelCT.block_append (RelCT.seq (R := Two EL)
    (two_piece [.rsp] (pins_of (fun p _ => p.sp) fun p s h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact congrArg GkP.sp h.2)
      (by taint_decide) ?_) ?_)
  · intro p s h
    have c := gkCtx_of h.1
    have hw : WP isa (.block VG.Impl.Ffdh.X86_64.Domain.GenerateKey.entry) s (E1 p) :=
      WP.mono (entry_base c) fun t ⟨hb, hd, _⟩ => by rw [h.2] at hb hd; exact ⟨gkRand s, hb, hd⟩
    change WP isa (.block (loads ++ entryTail)) s (E1 p) at hw
    refine WP.and ?_ (WP.block_append_iff.mp hw)
    exact WP.mono (loads_ok s c) fun t hh => by rw [← h.2]; exact hh
  exact two_piece [.rax] (pins_of (fun p _ => p.B) fun _ _ h _ hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.1) (by taint_decide) fun _ _ h => h.2

private theorem e1_dhp (p : GkP) (s : State) (h : E1 p s) : DHP p.d s := by
  obtain ⟨rb, hb, hd⟩ := h
  have hZ := hb.hZ
  exact ⟨hb.scr, hd, by change 256 ≤ p.Z; omega,
    hb.hdr (sDom, p.dp) (by simp [GkP.headers]),
    hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [GkP.headers])⟩

private theorem e1_ce (p : GkP) (s : State) (h : E1 p s) : WP isa (.block domHead) s (CE p) := by
  obtain ⟨rb, hb, hd⟩ := h
  exact WP.mono (dom_base hb hd) fun _ ⟨hb', hz, hd', hG, hQ, _⟩ => ⟨⟨rb, hb', hd'⟩, hz, hG, hQ⟩

private theorem ce_eval {p : GkP} {s : State} (h : CE p s) : isa.eval .ne s = some (!p.mv) := by
  simp [eval, h.2.1]

private theorem ce_zero (p : GkP) (s : State) (h : CE p s ∧ isa.eval .ne s = some false) : ZeroPre p s := by
  have he := h.2
  rw [ce_eval h.1] at he
  have hm : p.mv = true := by simpa using he
  obtain ⟨⟨rb, hb, hd⟩, _, hG, hQ⟩ := h.1
  exact ⟨rb, hb, hd, hG, hQ, hm⟩

theorem body_ct (M : Mont) (E : CrtExpL M) (R : R2Impl M) (hE : ExpCTL E sX sXl) :
    RelCT isa (Two CR)
      (VG.Impl.Ffdh.X86_64.Domain.GenerateKey.body M.mm E.code (.seq (.block r2Head) R.code))
      fun _ _ => True := by
  unfold VG.Impl.Ffdh.X86_64.Domain.GenerateKey.body
  refine RelCT.seq (R := Two CE) (RelCT.block_append (RelCT.seq entry_ct
    (two_post (two_map GkP.d e1_dhp domHead_ct) e1_ce))) ?_
  exact two_ite (fun _ _ _ h₁ h₂ => by rw [ce_eval h₁, ce_eval h₂])
    (two_taint [] (fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil) (by taint_decide))
    (two_map id ce_zero (main_ct M E R hE))

end VG.Proof.Ffdh.X86_64.GenerateKey

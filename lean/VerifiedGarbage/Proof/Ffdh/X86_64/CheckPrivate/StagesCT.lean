module

public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.ScalarCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
public meta import VerifiedGarbage.Impl.Ffdh.X86_64.CheckPrivate
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Start
public import VerifiedGarbage.Proof.Ffdh.X86_64.SetupCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp5
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.R2aStep
import VerifiedGarbage.Proof.Bignum.X86_64.R2aSub
import VerifiedGarbage.Proof.Bignum.X86_64.R2aWord
import VerifiedGarbage.Proof.Bignum.X86_64.R2wAdd
import VerifiedGarbage.Proof.Bignum.X86_64.R2wStep
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Correct
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Entry
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Main
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Math
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Scalar
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.ScalarBound
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.ScalarLess
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Tail
import VerifiedGarbage.Proof.Ffdh.X86_64.DomainHead
import VerifiedGarbage.Proof.Ffdh.X86_64.Exit
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Ffdh.X86_64.Moves
import VerifiedGarbage.Proof.Ffdh.X86_64.PowCT
import VerifiedGarbage.Proof.Ffdh.X86_64.R2
import VerifiedGarbage.Proof.Ffdh.X86_64.Setup
import VerifiedGarbage.Proof.Ffdh.X86_64.SetupModCT
import VerifiedGarbage.Proof.Ffdh.X86_64.SetupWsCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Ffdh.Domain
meta import VerifiedGarbage.Proof.Ffdh.X86_64.DomainHead
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Front
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Setup
meta import VerifiedGarbage.Proof.Ffdh.X86_64.SetupModCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.SetupWsCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Poly1305.Limbs64

/-! # FFDH exchange on x86-64: public stages for the timing proof -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckPrivate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev KpP.d (p : KpP) : DPub := ⟨p.B, p.Z, p.k, p.dp⟩

def CR (p : KpP) (s : State) : Prop := kpPre s ∧ kpOf s = p

def E1 (p : KpP) (s : State) : Prop := ∃ xb, Base p xb s ∧ s.gpr .rdi = p.B

def CE (p : KpP) (s : State) : Prop := E1 p s ∧ s.zf = some p.mv ∧
  word s.mem p.B (8 * sG) = off p.dp p.k ∧ word s.mem p.B (8 * sQ) = off p.dp (2 * p.k)

private def loads : List Instr :=
  [.mov .rax (.mem (VG.Impl.Rsa.X86_64.Crt.stk 2)), .mov .r10 (.mem (VG.Impl.Rsa.X86_64.Crt.stk 1))]

private def entryTail : List Instr := save .rax ++
  [.store (VG.Impl.Rsa.X86_64.Crt.ws .rax sDom) .rdi,
    .store (VG.Impl.Rsa.X86_64.Crt.ws .rax sDomLen) .rsi, .store (VG.Impl.Rsa.X86_64.Crt.ws .rax sK) .rdx,
    .store (VG.Impl.Rsa.X86_64.Crt.ws .rax sY) .rcx, .store (VG.Impl.Rsa.X86_64.Crt.ws .rax sX) .r9,
    .store (VG.Impl.Rsa.X86_64.Crt.ws .rax sXl) .r10, .mov .rdi (.reg .rax)]

private def EL (p : KpP) (s : State) : Prop := s.gpr .rax = p.B ∧ WP isa (.block entryTail) s (E1 p)

private theorem loads_ok (s : State) (c : KpCtx s) : WP isa (.block loads) s
    fun t => t.gpr .rax = stackArg s 1 := by
  have h1 : InRegions (s.rd ++ s.wr) (off (s.gpr .rsp) 16) 8 := c.ha 1 (by decide)
  have h0 : InRegions (s.rd ++ s.wr) (off (s.gpr .rsp) 8) 8 := c.ha 0 (by decide)
  unfold loads VG.Impl.Rsa.X86_64.Crt.stk
  xrun [State.ea, hdrOff, h1, h0]
  rfl

theorem entry_ct : RelCT isa (Two CR) (.block VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.entry) (Two E1) := by
  change RelCT isa (Two CR) (.block (loads ++ entryTail)) (Two E1)
  refine RelCT.block_append (RelCT.seq (R := Two EL)
    (two_piece [.rsp] (pins_of (fun p _ => p.sp) fun p s h r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact congrArg KpP.sp h.2) (by taint_decide) ?_) ?_)
  · intro p s h
    have c := kpCtx_of h.1
    have he : WP isa (.block VG.Impl.Ffdh.X86_64.Domain.CheckPrivate.entry) s (E1 p) :=
      WP.mono (entry_base c) fun t ⟨hb, hd, _⟩ => by rw [h.2] at hb hd; exact ⟨kpX s, hb, hd⟩
    change WP isa (.block (loads ++ entryTail)) s (E1 p) at he
    refine WP.and ?_ (WP.block_append_iff.mp he)
    exact WP.mono (loads_ok s c) fun t hh => by rw [← h.2]; exact hh
  exact two_piece [.rax] (pins_of (fun p _ => p.B) fun _ _ h _ hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.1) (by taint_decide) fun _ _ h => h.2

theorem e1_dhp (p : KpP) (s : State) (h : E1 p s) : DHP p.d s := by
  obtain ⟨xb, hb, hd⟩ := h
  have := hb.hZ
  exact ⟨hb.scr, hd, by change 256 ≤ p.Z; omega, hb.hdr (sDom, p.dp) (by simp [KpP.headers]),
    hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [KpP.headers])⟩

theorem e1_ce (p : KpP) (s : State) (h : E1 p s) : WP isa (.block domHead) s (CE p) := by
  obtain ⟨xb, hb, hd⟩ := h
  exact WP.mono (dom_base hb hd) fun t ⟨hb', hz, hd', hG, hQ, _⟩ => ⟨⟨xb, hb', hd'⟩, hz, hG, hQ⟩

theorem ce_eval {p : KpP} {s : State} (h : CE p s) : isa.eval .ne s = some (!p.mv) := by
  simp [eval, h.2.1]

theorem ce_valid {p : KpP} {s : State} (h : CE p s) (he : isa.eval .ne s = some false) : p.mv = true := by
  rw [ce_eval h] at he
  simpa using he

theorem ce_setup (p : KpP) (s : State) (h : CE p s ∧ isa.eval .ne s = some false) : SetupP p.d s := by
  obtain ⟨⟨xb, hb, hd⟩, _⟩ := h.1
  obtain ⟨hodd, _⟩ := valid_facts (ce_valid h.1 h.2) hb.k1
  exact ⟨p.pb, hb.scr, hd, hb.k1, hb.k2, hb.hZ,
    hb.hdr (sDom, p.dp) (by simp [KpP.headers]), hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [KpP.headers]),
    hb.dom.take p.k, hb.plen, hodd⟩

private theorem wp_seqs_split {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ [])
    {s : State} {Q : State → Prop} (h : WP isa (seqs (a ++ b)) s Q) :
    WP isa (seqs a) s fun t => WP isa (seqs b) t Q := by
  obtain ⟨tr, t, he, hq⟩ := h
  exact WP.seq_iff.mp ⟨tr, t, exec_seqs_append ha hb he, hq⟩

def BeforeX (p : KpP) (s : State) : Prop := ∃ xb mi,
  Base p xb s ∧ SubCtx s p.B p.Z (inner p.w) p.w p.w mi ∧
    WP isa (seqs (VG.Impl.Rsa.X86_64.Crt.loadArr aXm sX sXl)) s (Inner p)

theorem ce_beforeX (p : KpP) (s : State) (h : CE p s ∧ isa.eval .ne s = some false) :
    WP isa (seqs (([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup)) s (BeforeX p) := by
  obtain ⟨⟨xb, hb, hd⟩, _, hG, hQ⟩ := h.1
  have hm := ce_valid h.1 h.2
  have ho := (valid_facts hm hb.k1).1
  have hfull := WP.mono (setup_work hb hd hG hQ hm) fun t ⟨⟨mi, hw, hd'⟩, _⟩ =>
    (show Inner p t from ⟨xb, mi, hw, hd', hm⟩)
  have ht := wp_seqs_split (a := ([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup)
    (b := VG.Impl.Rsa.X86_64.Crt.loadArr aXm sX sXl) (by simp [pSetup]) (by simp [VG.Impl.Rsa.X86_64.Crt.loadArr]) hfull
  have hs : WP isa (seqs (([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup)) s
      fun t => ∃ mi, Base p xb t ∧ SubCtx t p.B p.Z (inner p.w) p.w p.w mi :=
    WP.mono (setup_ok (B := p.B) (Z := p.Z) (k := p.k) (dp := p.dp) (pb := p.pb) hb.scr hd hb.k1 hb.k2 hb.hZ
      (hb.hdr (sDom, p.dp) (by simp [KpP.headers])) (hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [KpP.headers]))
      (hb.dom.take p.k) hb.plen ho) fun t ⟨mi, hc, _, _, hf, k⟩ => by
        obtain ⟨hi, hh, _⟩ := setup_frame hb.k1 hb.hZ hf
        exact ⟨mi, hb.keep hi k hh, hc⟩
  exact WP.mono (WP.and hs ht) fun t ⟨⟨mi, hb', hc⟩, htail⟩ => ⟨xb, mi, hb', hc, htail⟩

abbrev KpP.xlPub (p : KpP) : BPub := ⟨⟨p.B, p.Z, inner p.w, p.w, p.w⟩, p.xp, p.xl⟩

theorem beforeX_load (p : KpP) (s : State) (h : BeforeX p s) : LPre aXm sX sXl p.xlPub s := by
  obtain ⟨xb, mi, hb, hc, _⟩ := h
  have hk := hb.k1
  have hk' := hb.k2
  have hxl := hb.xl2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold KpP.w; omega
  exact ⟨mi, xb, hc, show 2 ≤ p.w by omega, Nat.le_refl _, show p.w < 2 ^ 30 by omega,
    by decide, by decide, by decide, hb.hdr (sX, p.xp) (by simp [KpP.headers]),
    by rw [hb.xlen]; exact hb.hdr (sXl, BitVec.ofNat 64 p.xl) (by simp [KpP.headers]), hb.xlen,
    hb.x, by rw [hb.xlen]; exact hb.xl1, by rw [hb.xlen]; omega,
    by change (xb.length + 7) / 8 ≤ p.w; rw [hb.xlen]; omega⟩

theorem beforeX_inner (p : KpP) (s : State) (h : BeforeX p s) :
    WP isa (seqs (VG.Impl.Rsa.X86_64.Crt.loadArr aXm sX sXl)) s (Inner p) := h.choose_spec.choose_spec.2.2

end VG.Proof.Ffdh.X86_64.CheckPrivate

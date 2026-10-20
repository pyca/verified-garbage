module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ChecksCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.PowCT
public import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Arithmetic
public import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Body
public import VerifiedGarbage.Proof.Ffdh.X86_64.SetupCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ChecksCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.PowCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Arithmetic
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Body
meta import VerifiedGarbage.Proof.Ffdh.X86_64.SetupCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.Octets

/-! # FFDH exchange on x86-64: public stages for the timing proof -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Exchange

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev ExP.d (p : ExP) : DPub := ⟨p.B, p.Z, p.k, p.dp⟩
abbrev ExP.ws (p : ExP) : Ws := ⟨off p.B (inner p.w), slot p.w 8, p.w⟩
abbrev ExP.pw (p : ExP) : PowPub := ⟨⟨p.B, p.Z, inner p.w, p.w, p.w⟩, p.yp, p.k, p.xp, p.xl⟩

def CR (p : ExP) (s : State) : Prop := exPre s ∧ exOf s = p

def E1 (p : ExP) (s : State) : Prop := ∃ xb, Base p xb s ∧ s.gpr .rdi = p.B

def CE (p : ExP) (s : State) : Prop := E1 p s ∧ s.zf = some p.mv

def C1 (p : ExP) (s : State) : Prop := (∃ xb, Entered p xb s) ∧ p.mv = true

def C2 (p : ExP) (s : State) : Prop := ∃ xb, Ready p xb s

def C3 (p : ExP) (s : State) : Prop := ∃ xb, Value p xb s

def C4 (p : ExP) (s : State) : Prop := ∃ xb, Checked p xb s

private def loads : List Instr :=
  [.mov .rax (.mem (VG.Impl.Rsa.X86_64.Crt.stk 4)), .mov .r10 (.mem (VG.Impl.Rsa.X86_64.Crt.stk 1)),
    .mov .r11 (.mem (VG.Impl.Rsa.X86_64.Crt.stk 2))]

private def entryTail : List Instr := save .rax ++
  [.store (VG.Impl.Rsa.X86_64.Crt.ws .rax VG.Impl.Ffdh.X86_64.Domain.sOut) .rdi,
    .store (VG.Impl.Rsa.X86_64.Crt.ws .rax sDom) .rdx,
    .store (VG.Impl.Rsa.X86_64.Crt.ws .rax sDomLen) .rcx, .store (VG.Impl.Rsa.X86_64.Crt.ws .rax sK) .r8,
    .store (VG.Impl.Rsa.X86_64.Crt.ws .rax sX) .r9, .store (VG.Impl.Rsa.X86_64.Crt.ws .rax sXl) .r10,
    .store (VG.Impl.Rsa.X86_64.Crt.ws .rax sY) .r11, .mov .rdi (.reg .rax)]

private def EL (p : ExP) (s : State) : Prop := s.gpr .rax = p.B ∧ WP isa (.block entryTail) s (E1 p)

private theorem loads_ok (s : State) (c : ExCtx s) : WP isa (.block loads) s
    fun t => t.gpr .rax = stackArg s 3 := by
  have h3 : InRegions (s.rd ++ s.wr) (off (s.gpr .rsp) 32) 8 := c.ha 3 (by decide)
  have h0 : InRegions (s.rd ++ s.wr) (off (s.gpr .rsp) 8) 8 := c.ha 0 (by decide)
  have h1 : InRegions (s.rd ++ s.wr) (off (s.gpr .rsp) 16) 8 := c.ha 1 (by decide)
  unfold loads VG.Impl.Rsa.X86_64.Crt.stk
  xrun [State.ea, hdrOff, h3, h0, h1]
  rfl

theorem entry_ct : RelCT isa (Two CR) (.block VG.Impl.Ffdh.X86_64.Domain.Exchange.entry) (Two E1) := by
  change RelCT isa (Two CR) (.block (loads ++ entryTail)) (Two E1)
  refine RelCT.block_append (RelCT.seq (R := Two EL)
    (two_piece [.rsp] (pins_of (fun p _ => p.sp) fun p s h r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact congrArg ExP.sp h.2) (by taint_decide) ?_) ?_)
  · intro p s h
    have c := exCtx_of h.1
    have he : WP isa (.block VG.Impl.Ffdh.X86_64.Domain.Exchange.entry) s (E1 p) :=
      WP.mono (entry_base c) fun t ⟨hb, hd, _⟩ => by rw [h.2] at hb hd; exact ⟨exX s, hb, hd⟩
    change WP isa (.block (loads ++ entryTail)) s (E1 p) at he
    refine WP.and ?_ (WP.block_append_iff.mp he)
    exact WP.mono (loads_ok s c) fun t hh => by rw [← h.2]; exact hh
  exact two_piece [.rax] (pins_of (fun p _ => p.B) fun _ _ h _ hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.1) (by taint_decide) fun _ _ h => h.2

theorem e1_dhp (p : ExP) (s : State) (h : E1 p s) : DHP p.d s := by
  obtain ⟨xb, hb, hd⟩ := h
  have := hb.hZ
  exact ⟨hb.scr, hd, by change 256 ≤ p.Z; omega, hb.hdr (sDom, p.dp) (by simp [ExP.headers]),
    hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [ExP.headers])⟩

theorem e1_ce (p : ExP) (s : State) (h : E1 p s) : WP isa (.block domHead) s (CE p) := by
  obtain ⟨xb, hb, hd⟩ := h
  exact WP.mono (dom_base hb hd) fun t ⟨hb', hz, hd', _⟩ => ⟨⟨xb, hb', hd'⟩, hz⟩

theorem ce_eval {p : ExP} {s : State} (h : CE p s) : isa.eval .ne s = some (!p.mv) := by
  simp [eval, h.2]

theorem ce_valid {p : ExP} {s : State} (h : CE p s) (he : isa.eval .ne s = some false) : p.mv = true := by
  rw [ce_eval h] at he
  simpa using he

theorem ce_setup (p : ExP) (s : State) (h : CE p s ∧ isa.eval .ne s = some false) : SetupP p.d s := by
  obtain ⟨⟨xb, hb, hd⟩, _⟩ := h.1
  obtain ⟨hodd, _⟩ := valid_facts (ce_valid h.1 h.2) hb.k1
  exact ⟨p.pb, hb.scr, hd, hb.k1, hb.k2, hb.hZ,
    hb.hdr (sDom, p.dp) (by simp [ExP.headers]), hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [ExP.headers]),
    hb.dom.take p.k, hb.plen, hodd⟩

theorem ce_c1 (p : ExP) (s : State) (h : CE p s ∧ isa.eval .ne s = some false) :
    WP isa (seqs (([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup)) s (C1 p) := by
  obtain ⟨⟨xb, hb, hd⟩, _⟩ := h.1
  have hm := ce_valid h.1 h.2
  exact WP.mono (setup_entered hb hd hm) fun t ⟨hh, _⟩ => ⟨⟨xb, hh⟩, hm⟩

theorem c2_ps0 (p : ExP) (s : State) (h : C2 p s) : PS0 sY sK sX sXl p.pw s := by
  obtain ⟨xb, mi, hb, hc⟩ := h
  have hk := hb.k1
  have hk' := hb.k2
  simpa only [ExP.pw, hb.ylen, hb.xlen] using ps0_of hc
    (bp := sY) (bl := sK) (ep := sX) (el := sXl) (pb := p.yp) (pe := p.xp) (bb := p.yb) (eb := xb) (by decide) (by decide) (by decide) (by decide)
    (hb.hdr (sY, p.yp) (by simp [ExP.headers]))
    (by rw [hb.ylen]; exact hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [ExP.headers])) hb.y
    (by rw [hb.ylen]; omega) (by rw [hb.ylen])
    (hb.hdr (sX, p.xp) (by simp [ExP.headers]))
    (by rw [hb.xlen]; exact hb.hdr (sXl, BitVec.ofNat 64 p.xl) (by simp [ExP.headers]))
    hb.x (by rw [hb.xlen]; exact hb.xl1) (by rw [hb.xlen]; exact hb.xl2.trans hk')

theorem c2_c3 (M : Mont) (E : CrtExpL M) (p : ExP) (s : State) (h : C2 p s) :
    WP isa (seqs (pow M.mm E.code sY sK sX sXl)) s (C3 p) := by
  obtain ⟨xb, hh⟩ := h
  exact WP.mono (ready_value M E hh) fun _ ⟨hv, _⟩ => ⟨xb, hv⟩

theorem c3_good (p : ExP) (s : State) (h : C3 p s) : GoodW1 p.ws s := by
  obtain ⟨xb, ⟨mi, hb, hc⟩, _⟩ := h
  have hw := hc.w2
  have hw' := hc.w28
  exact ⟨⟨mi, hc.sub.good, Nat.le_refl _⟩, by change 1 ≤ p.w; omega, by change p.w < 2 ^ 31; omega⟩

theorem c3_c4 (p : ExP) (s : State) (h : C3 p s) : WP isa (seqs (range aY)) s (C4 p) := by
  obtain ⟨xb, hh⟩ := h
  exact WP.mono (value_checked hh) fun _ ⟨hv, _⟩ => ⟨xb, hv⟩

end VG.Proof.Ffdh.X86_64.Exchange

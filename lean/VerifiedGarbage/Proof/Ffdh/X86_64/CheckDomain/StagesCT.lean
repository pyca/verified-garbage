module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ChecksCT
public import VerifiedGarbage.Impl.Ffdh.X86_64.CheckDomain
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Context
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Setup
public import VerifiedGarbage.Proof.Ffdh.X86_64.SetupCT
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Range
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Loads
import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Start
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ChecksCT
meta import VerifiedGarbage.Impl.Ffdh.X86_64.CheckDomain
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Context
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Setup
meta import VerifiedGarbage.Proof.Ffdh.X86_64.SetupCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Range
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Loads
meta import VerifiedGarbage.Proof.Ffdh.X86_64.CheckDomain.Start
meta import VerifiedGarbage.Proof.Bignum.Octets

/-! # FFDH domain validation on x86-64: public stages for constant time -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.CheckDomain

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev CdP.d (p : CdP) : DPub := ⟨p.B, p.Z, p.k, p.dp⟩
abbrev CdP.x (p : CdP) : XPub := ⟨p.B, p.Z, inner p.w, p.w, p.w⟩
abbrev CdP.ws (p : CdP) : Ws := p.x.ws
abbrev CdP.gl (p : CdP) : BPub := ⟨p.x, off p.dp p.k, p.k⟩
abbrev CdP.ql (p : CdP) : BPub := ⟨p.x, off p.dp (2 * p.k), p.k⟩

def CR (p : CdP) (s : State) : Prop := cdPre s ∧ cdOf s = p

def E1 (p : CdP) (s : State) : Prop := Base p s ∧ s.gpr .rdi = p.B

def CE (p : CdP) (s : State) : Prop := E1 p s ∧ s.zf = some p.mv ∧
  word s.mem p.B (8 * sG) = off p.dp p.k ∧ word s.mem p.B (8 * sQ) = off p.dp (2 * p.k)

def Inner (p : CdP) (s : State) : Prop := ∃ mi,
  Work p mi s ∧ s.gpr .rdi = off p.B (inner p.w) ∧ p.mv = true

def Generator (p : CdP) (s : State) : Prop := Inner p s ∧
  wv s.mem (off p.B (inner p.w)) (slot p.w aXm) p.w = p.G

def GeneratorChecked (p : CdP) (s : State) : Prop := Inner p s ∧ s.zf = some (!decide p.gr)

theorem entry_ct : RelCT isa (Two CR) (.block VG.Impl.Ffdh.X86_64.Domain.CheckDomain.entry) (Two E1) := by
  refine two_piece [.rcx] (pins_of (fun p _ => p.B) (fun p s h r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact congrArg CdP.B h.2)) (by taint_decide) ?_
  intro p s h
  exact WP.mono (entry_base (cdCtx_of h.1)) fun t ⟨hb, hd, _⟩ => by
    rw [h.2] at hb hd
    exact ⟨hb, hd⟩

theorem e1_dhp (p : CdP) (s : State) (h : E1 p s) : DHP p.d s := by
  have hz := h.1.hZ
  exact ⟨h.1.scr, h.2, by change 256 ≤ p.Z; omega,
    h.1.hdr (sDom, p.dp) (by simp [CdP.headers]), h.1.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers])⟩

theorem e1_ce (p : CdP) (s : State) (h : E1 p s) : WP isa (.block domHead) s (CE p) :=
  WP.mono (dom_base h.1 h.2) fun _ ⟨hb, hz, hd, hG, hQ, _⟩ => ⟨⟨hb, hd⟩, hz, hG, hQ⟩

theorem ce_valid {p : CdP} {s : State} (h : CE p s) (he : isa.eval .ne s = some false) : p.mv = true := by
  simpa only [eval, h.2.1, Option.map_some, Option.some.injEq, Bool.not_eq_false'] using he

theorem ce_setup (p : CdP) (s : State) (h : CE p s ∧ isa.eval .ne s = some false) : SetupP p.d s := by
  have hb := h.1.1.1
  exact ⟨p.pb, hb.scr, h.1.1.2, hb.k1, hb.k2, hb.hZ,
    hb.hdr (sDom, p.dp) (by simp [CdP.headers]), hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers]),
    hb.dom.take p.k, hb.plen, (valid_facts (ce_valid h.1 h.2) hb.k1).1⟩

theorem ce_inner (p : CdP) (s : State) (h : CE p s ∧ isa.eval .ne s = some false) :
    WP isa (seqs (([.block VG.Impl.Rsa.X86_64.head] : List (Prog isa)) ++ pSetup)) s (Inner p) :=
  WP.mono (setup_work h.1.1.1 h.1.1.2 h.1.2.2.1 h.1.2.2.2 (ce_valid h.1 h.2))
    fun _ ⟨⟨mi, hw, hd⟩, _⟩ => ⟨mi, hw, hd, ce_valid h.1 h.2⟩

theorem inner_good (p : CdP) (s : State) (h : Inner p s) : GoodW1 p.ws s := by
  obtain ⟨mi, hw, hd, _⟩ := h
  have hk := hw.base.k1
  have hk' := hw.base.k2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega
  exact ⟨⟨mi, (hw.mem.ctx hd).good, Nat.le_refl _⟩, show 1 ≤ p.w by omega, show p.w < 2 ^ 31 by omega⟩

theorem inner_load (p : CdP) (s : State) (h : Inner p s) : LPre aXm sG sK p.gl s := by
  obtain ⟨mi, hw, hd, _⟩ := h
  have hb := hw.base
  have hk := hb.k1
  have hk' := hb.k2
  have ew : 8 * p.w ≤ p.k + 7 ∧ p.k ≤ 8 * p.w := by unfold CdP.w; omega
  exact ⟨mi, p.gb, hw.mem.ctx hd, show 2 ≤ p.w by omega, Nat.le_refl _, show p.w < 2 ^ 30 by omega,
    by decide, by decide, by decide, hw.g,
    by rw [hb.glen]; exact hb.hdr (sK, BitVec.ofNat 64 p.k) (by simp [CdP.headers]),
    hb.glen, (hb.dom.drop p.k).take p.k, by rw [hb.glen]; omega,
    by rw [hb.glen]; omega, by rw [hb.glen]⟩

theorem inner_generator (p : CdP) (s : State) (h : Inner p s) :
    WP isa (seqs (VG.Impl.Rsa.X86_64.Crt.loadArr aXm sG sK)) s (Generator p) := by
  obtain ⟨mi, hw, hd, hm⟩ := h
  exact WP.mono (load_generator hw hd) fun t ⟨⟨hw', hd', hx⟩, _⟩ => ⟨⟨mi, hw', hd', hm⟩, hx⟩

theorem generator_checked (p : CdP) (s : State) (h : Generator p s) :
    WP isa (seqs (rangeTest aXm)) s (GeneratorChecked p) := by
  obtain ⟨⟨mi, hw, hd, hm⟩, hx⟩ := h
  exact WP.mono (generator_range hw hd hx) fun t ⟨⟨hw', hd', hz⟩, _⟩ => ⟨⟨mi, hw', hd', hm⟩, hz⟩

end VG.Proof.Ffdh.X86_64.CheckDomain

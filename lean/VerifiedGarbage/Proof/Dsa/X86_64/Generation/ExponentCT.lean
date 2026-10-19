module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeConstantsCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeConstantsCT
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrShift
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrShift
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega

/-! # Constant-time preparation of the windowed Miller–Rabin exponent -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaKeyGen.X86_64

def ExponentBefore (p : PrimeParams) (s : State) : Prop :=
  PrimeGood p s ∧ wv s.mem p.B (slot p.w aN) p.w = p.N

theorem lowWordArgs_state {p : PrimeParams} {s : State} (h : PrimeGood p s) :
    WP isa (.block [.mov .r12 (.mem (hdr sW)), .mov .r8 (.mem (hdr (sArr aN)))]) s
      (fun t => t.gpr .r12 = BitVec.ofNat 64 p.w ∧ t.gpr .r8 = off p.B (slot p.w aN)) := by
  obtain ⟨mi, hg⟩ := h
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off p.B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot p.w 8 hi; have := p.dims.z; omega)
  xrun [State.ea, hdr, hdrOff, hg.rdi, hl sW (by decide), hl (sArr aN) (by decide),
    hg.hdr.hw, hg.hdr.harr aN (by decide)]

theorem lowWord_ct : RelCT isa (Two PrimeGood) (seqs lowWord) (fun _ _ => True) := by
  unfold lowWord
  simp only [seqs]
  apply VG.Proof.Rsa.X86_64.RelCT.block_seq (l₁ :=
    [.mov .r12 (.mem (hdr sW)), .mov .r8 (.mem (hdr (sArr aN)))])
  refine RelCT.seq (two_post (two_taint [.rdi] ?_ (by taint_decide))
    (fun _ _ h => lowWordArgs_state h)) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    obtain ⟨mi, hs⟩ := hs
    obtain ⟨mi', ht⟩ := ht
    exact hs.rdi.trans ht.rdi.symm
  · exact two_taint [.r12, .r8] (by
      intro p s t hs ht r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.1.trans ht.1.symm
      · exact hs.2.trans ht.2.symm) (by taint_decide)

theorem lowWord_good {p : PrimeParams} {s : State} (h : ExponentBefore p s) :
    WP isa (seqs lowWord) s (PrimeGood p) := by
  obtain ⟨mi, hg⟩ := h.1
  refine WP.mono (lowWord_ok hg p.dims.z (by have := p.dims.w4; omega)
    (by have := p.dims.w128; omega) h.2 p.odd (by have := p.n3; omega)) fun t ⟨_, hm, hk⟩ => ?_
  exact ⟨mi, hg.scr.congr hk.2.2, (hk.gpr (by decide)).trans hg.rdi, by rw [hm]; exact hg.hdr⟩

def ExponentRegs (p : PrimeParams) (s : State) : Prop :=
  s.gpr .r12 = BitVec.ofNat 64 p.w ∧ s.gpr .rsi = off p.B (slot p.w aN) ∧
    s.gpr .rbx = off p.B (slot p.w aE)

theorem exponentArgs_state {p : PrimeParams} {s : State} (h : PrimeGood p s) :
    WP isa (.block (extBase aE .rbx ++
      ([.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aN)))] : List Instr))) s (ExponentRegs p) := by
  obtain ⟨mi, hg⟩ := h
  rw [WP.block_append_iff]
  refine WP.mono (extBase_ok hg p.dims.z (by have := p.dims.w128; omega)
    (j := aE) (by decide) (r := .rbx) (by decide) rfl rfl) fun u ⟨hbx, hm, hk⟩ => ?_
  have hu : Good u p.B p.Z p.w mi :=
    ⟨hg.scr.congr hk.2.2, (hk.gpr (by decide)).trans hg.rdi, by rw [hm]; exact hg.hdr⟩
  have hl : ∀ i < 32, InRegions (u.rd ++ u.wr) (off p.B (8 * i)) 8 := fun i hi =>
    hu.scr.ld (by have := hdr_lt_slot p.w 8 hi; have := p.dims.z; omega)
  xrun [ExponentRegs, State.ea, hdr, hdrOff, hu.rdi, hl sW (by decide), hl (sArr aN) (by decide),
    hu.hdr.hw, hu.hdr.harr aN (by decide), hbx]

theorem exponentTail_ct : RelCT isa (Two PrimeGood)
    (seqs (([.block (extBase aE .rbx ++ ([.mov .r12 (.mem (hdr sW)),
      .mov .rsi (.mem (hdr (sArr aN))), .mov .r15 (.imm (BitVec.ofInt 32 (-1))),
      .mov32 .rax (.imm 0), .alu .sub .rax (.reg .rbp), .alu .and .rax (.reg .rbp),
      .store (ix .rbx .r12) .rax] : List Instr))] : List (Prog isa)) ++
      (halfPass ++ (halfCond 1 ++ (halfCond 2 ++ halfCond 3))))) (fun _ _ => True) := by
  simp only [halfPass, halfCond, List.cons_append, List.nil_append, seqs]
  rw [show extBase aE .rbx ++
      ([.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aN))),
        .mov .r15 (.imm (BitVec.ofInt 32 (-1))), .mov32 .rax (.imm 0),
        .alu .sub .rax (.reg .rbp), .alu .and .rax (.reg .rbp), .store (ix .rbx .r12) .rax] : List Instr) =
      (extBase aE .rbx ++ ([.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aN)))] : List Instr)) ++
        ([.mov .r15 (.imm (BitVec.ofInt 32 (-1))), .mov32 .rax (.imm 0), .alu .sub .rax (.reg .rbp),
          .alu .and .rax (.reg .rbp), .store (ix .rbx .r12) .rax] : List Instr) by
      simp only [List.append_assoc, List.cons_append, List.nil_append]]
  apply VG.Proof.Rsa.X86_64.RelCT.block_seq
    (l₁ := extBase aE .rbx ++ ([.mov .r12 (.mem (hdr sW)), .mov .rsi (.mem (hdr (sArr aN)))] : List Instr))
    (l₂ := [.mov .r15 (.imm (BitVec.ofInt 32 (-1))), .mov32 .rax (.imm 0), .alu .sub .rax (.reg .rbp),
      .alu .and .rax (.reg .rbp), .store (ix .rbx .r12) .rax])
  refine RelCT.seq (two_post (two_taint [.rdi] ?_ (by taint_decide))
    (fun _ _ h => exponentArgs_state h)) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    obtain ⟨mi, hs⟩ := hs
    obtain ⟨mi', ht⟩ := ht
    exact hs.rdi.trans ht.rdi.symm
  · exact two_taint [.r12, .rsi, .rbx] (by
      intro p s t hs ht r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hs.1.trans ht.1.symm
      · exact hs.2.1.trans ht.2.1.symm
      · exact hs.2.2.trans ht.2.2.symm) (by taint_decide)

theorem primeExponent_ct : RelCT isa (Two ExponentBefore) (seqs expSetup) (fun _ _ => True) := by
  rw [expSetup_eq]
  apply RelCT.seqs_append (by simp [lowWord]) (by simp)
  exact RelCT.seq (two_post (two_map id (fun _ _ h => h.1) lowWord_ct)
    (fun _ _ h => lowWord_good h)) exponentTail_ct

end VG.Proof.Dsa.X86_64.Generation

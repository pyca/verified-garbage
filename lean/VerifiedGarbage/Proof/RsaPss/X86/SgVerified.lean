module

public import VerifiedGarbage.Proof.RsaPss.X86.SgCall
public import VerifiedGarbage.Proof.RsaPss.X86.SgEnc3
public import VerifiedGarbage.Proof.MdHashTable.X86.Tables
public import VerifiedGarbage.Proof.HashTable.X86
import VerifiedGarbage.Proof.RsaPss.X86.NoSp
import VerifiedGarbage.Proof.RsaPss.X86.NoSpT
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaOaep.X86.LabelT
import VerifiedGarbage.Proof.RsaOaep.X86.NoSp
import VerifiedGarbage.Proof.RsaOaep.X86.Taint
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.X86.Exec

/-!
# RSASSA-PSS signing on x86: verified

As on ARMv7 (`Proof/RsaPss/Arm/SgVerified.lean`), with the hash functions as
tables: the checks, then zeros or the encoding and the private-key
operation (`tail_vp`), for the hash function `h` of the table of `MdHash` at
the argument 22 and MGF1's `g` of the table of `Hash` at 23; the index of
`h` (the table's word 5, `idx_vp`) chooses that tail among those of `idxs`
(`body_vp`, by `Proof.RsaOaep.X86.byLen_vp`), whose code for the index is
that for `h`'s sizes (`Shape`). The body writes `esp` only through the frames
of its calls (`body_noSp`); with the frames around it (`wrap_ok`, `wrap_ct`)
and the result as the shared contract states it, for the variants `w` and
`wg` whose tables the arguments are (`held_entered`, `tabFacts_entered`):
`vg_rsa_pss_sign`, calling `vg_rsa_private_checked` over `v`, with the hash
function any of the tables of `vs` and MGF1's any of those of `gs`, is
verified (`sign_verified`), given a state that meets the contract
(`SgSat.lean`). Every stage keeps the addresses of the statics (`VP.syms`),
which the indirect calls need.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86.Sg

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86 VG.Proof.RsaPss.X86
open VG.X86 hiding frameBytes
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl privCode)
open VG.Impl.RsaOaep.X86 (Fns byLen)
open VG.Proof.RsaOaep.X86 (OHash TabFacts VP.syms byLen_vp byLen_noSp St_roW)
open VG.Proof.MdHashTable.X86 (MVar)
open VG.Proof.HashTable.X86 (TVar)

variable (h : PssHash)

/-- A stage, keeping the addresses of the statics. -/
abbrev Sy (F : State → State → Prop) (σ s : State) : Prop := F σ s ∧ s.syms = σ.syms

/-- The checks, then zeros or the encoding and the private-key operation,
for the hash function `h` of the table at the argument 22 and MGF1's `g` of
that at 23. -/
theorem tail_vp (P : EP) {dn : String} {f : MdFns}
    (hTH : ∀ σ, P.TH σ → HFacts h dn f P.tabH P.hai P.hac P.had σ)
    (fneH : f.init ≠ [] ∧ f.comp ≠ [] ∧ f.dig ≠ []) (g : OHash) {fG : Fns}
    (hT : ∀ σ, P.T σ → TabFacts g.H fG P.tab P.ai P.au P.af σ)
    (fne : fG.init ≠ [] ∧ fG.upd ≠ [] ∧ fG.fin ≠ []) (v : CrtImpl) :
    VP (Sy (S h P)) (signTail f h.H fG (privName v) (privCode v)) (Fin h g.G P) := by
  by_cases hP : ∃ σ, In h.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.1⟩
  show VP _ (.seq (.block (signChk ++ params h.H)) (.ite .ne signFail (.seq (signEncT f h.H fG)
    (.seq (.block privArgs) (.call (privName v) (privCode v)))))) _
  exact (VP.syms (chk_vp h P)).seq (VP.ite
    (fun σ s hs => ⟨!decide (fits h P), by simp only [eval, hs.1.2.2.2.2.2, Option.map_some]⟩)
    (fun _ _ _ _ h₁ h₂ => by simp only [eval, h₁.1.2.2.2.2.2, h₂.1.2.2.2.2.2])
    ((fail_vp h g.G P).mono (fun σ s ⟨⟨h1, _⟩, e⟩ => ⟨h1, e⟩) fun _ _ h => h)
    (((enc_vp h P hP hTH fneH g hT fne).mono (fun σ s ⟨⟨h1, sy⟩, e⟩ => ⟨e0_of h h1 e, sy⟩)
      fun _ _ h => h.1).seq ((pa_vp h g.G P).seq (call_vp h g.G g.valid P v))))

/-- The index of the hash function of the table at the argument 22, to
`edx`. -/
theorem idx_vp (P : EP) {ix : Nat} (hix : ∀ σ, P.TH σ → σ.mem.readW (VG.X86.addr P.tabH 20) 32 = BitVec.ofNat 32 ix) :
    VP (Sy (S h P)) (.block (idxLoad 22)) (fun σ s => Sy (S h P) σ s ∧ s.gpr .edx = BitVec.ofNat 32 ix) := by
  by_cases hP : ∃ σ, In h.D P σ
  swap
  · exact VP.empty fun σ s hs => hP ⟨σ, hs.1.1⟩
  obtain ⟨σ₀, hi₀⟩ := hP
  obtain ⟨tR, tRo, tC⟩ := hi₀.tblH5
  show VP _ (.block ([ld .edx (arg 22)] ++ [.mov .edx (.mem (Impl.RsaPkcs1Sig.X86.at_ .edx 20))])) _
  refine VP.block_append (G := fun σ s => Sy (S h P) σ s ∧ s.gpr .edx = P.tabH)
    (VP.taint [.esp] idxArg22_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s hs => ?_)
    (VP.taint [.esp, .edx] idxWord_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s hs => ?_)
  · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.2.sp, h₂.1.2.sp]
  · obtain ⟨⟨hi, hs⟩, sy⟩ := hs
    simp only [ld]
    refine hs.wp_arg (sg_arg h (j := 22) (by decide)) (by decide) fun t1 s1 u1 => WP.block_nil
      ⟨⟨⟨hi, s1⟩, u1.syms.trans sy⟩, by rw [u1.gpr]; rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1.1.2.sp, h₂.1.1.2.sp]
    · rw [h₁.2, h₂.2]
  · obtain ⟨⟨⟨hi, hs⟩, sy⟩, hdx⟩ := hs
    have hin : InRegions (s.rd ++ s.wr) (VG.X86.addr P.tabH 20) 4 := ⟨tR, hs.inRo tRo, tC⟩
    refine wp_ldm (B := P.tabH) hdx hin fun t2 u2 => WP.block_nil ⟨⟨⟨hi, hs.upd u2 (by decide)⟩, u2.syms.trans sy⟩, ?_⟩
    rw [u2.gpr, St_roW hs tRo tC, hix σ hi.tabTH]

/-- The tail for an index is that for the sizes of its hash function. -/
theorem tail_eq {i : Nat} {f : MdFns} {fG : Fns} {pn : String} {pc : Prog isa}
    (hs : sizes h.H = sizesOf i) : signTail f (ofIdx i) fG pn pc = signTail f h.H fG pn pc := by
  rw [show ofIdx i = ofSizes (sizes h.H) by rw [hs]; rfl]
  rfl

/-- The body, for the hash function `h` of index `ix` and MGF1's `g`. -/
theorem body_vp (P : EP) {dn : String} {f : MdFns} {ix : Nat} (hix₀ : ix ∈ idxs) (hs : sizes h.H = sizesOf ix)
    (hTH : ∀ σ, P.TH σ → HFacts h dn f P.tabH P.hai P.hac P.had σ ∧
      σ.mem.readW (VG.X86.addr P.tabH 20) 32 = BitVec.ofNat 32 ix)
    (fneH : f.init ≠ [] ∧ f.comp ≠ [] ∧ f.dig ≠ []) (g : OHash) {fG : Fns}
    (hT : ∀ σ, P.T σ → TabFacts g.H fG P.tab P.ai P.au P.af σ)
    (fne : fG.init ≠ [] ∧ fG.upd ≠ [] ∧ fG.fin ≠ []) (v : CrtImpl) :
    VP (Sy (S h P)) (signBodyT f fG (privName v) (privCode v)) (Fin h g.G P) := by
  have hlt : ix < 2 ^ 32 := (cmpIdxs_taint ix hix₀).1
  show VP _ (.seq (.block (idxLoad 22)) (byLen (fun i => signTail f (ofIdx i) fG (privName v) (privCode v)) idxs)) _
  refine (idx_vp h P fun σ hσ => (hTH σ hσ).2).seq (byLen_vp (D := ix) hlt (fun _ _ hs => hs.2)
    (fun σ s t ⟨⟨⟨hi, hs⟩, sy⟩, dx⟩ fu sy' => ⟨⟨⟨hi, hs.fupd fu⟩, sy'.trans sy⟩, by rw [fu.gpr]; exact dx⟩) ?_ hix₀
    cmpIdxs_taint)
  rw [tail_eq h hs]
  exact (tail_vp h P (fun σ hσ => (hTH σ hσ).1) fneH g hT fne v).mono (fun _ _ hs => hs.1) fun _ _ h => h

/-! ## The stack -/

theorem tail_noSp {f : MdFns} (hi : ∀ q ∈ f.init, NoSp q.2) (hc : ∀ q ∈ f.comp, NoSp q.2)
    (hd : ∀ q ∈ f.dig, NoSp q.2) {fG : Fns} (gi : ∀ q ∈ fG.init, NoSp q.2) (gu : ∀ q ∈ fG.upd, NoSp q.2)
    (gf : ∀ q ∈ fG.fin, NoSp q.2) (v : CrtImpl) : NoSp (signTail f h.H fG (privName v) (privCode v)) := by
  have sp := spOk h
  have p1 := sp.params
  have p2 := sp.cpDig16
  have p3 := sp.cpSalt
  have p4 := sp.lenArgs19
  have p5 := sp.putH
  have p6 := sp.mgfArgs
  have hct := ctHashT_noSp h hi hc hd (j := 22) (NoSp.of_all (by decide +kernel))
  have hm := Proof.RsaOaep.X86.mgfX_noSp gi gu gf (j := 23) (NoSp.of_all (by decide +kernel))
  have hp := Proof.Rsa.X86.PrivChecked.privateCode_noSp v
  simp only [signTail, seqs]
  refine noSp_seq (noSp_append (NoSp.of_all (by decide +kernel)) p1) ?_
  simp only [signEncT, yDig, signFail, seqs]
  repeat' (first
    | with_reducible apply noSp_seq | with_reducible apply noSp_ite | with_reducible apply noSp_loop
    | with_reducible apply noSp_call
    | with_reducible assumption
    | exact NoSp.of_all (by decide +kernel))

/-- `vs`' and `gs`' functions write `esp` only through their frames. -/
structure FnsSp (f : MdFns) (fG : Fns) : Prop where
  hi : ∀ q ∈ f.init, NoSp q.2
  hc : ∀ q ∈ f.comp, NoSp q.2
  hd : ∀ q ∈ f.dig, NoSp q.2
  gi : ∀ q ∈ fG.init, NoSp q.2
  gu : ∀ q ∈ fG.upd, NoSp q.2
  gf : ∀ q ∈ fG.fin, NoSp q.2

theorem body_noSp {f : MdFns} {fG : Fns} (hf : FnsSp f fG) (hall : ∀ i ∈ idxs, ∃ h : PssHash, sizes h.H = sizesOf i)
    (v : CrtImpl) : NoSp (signBodyT f fG (privName v) (privCode v)) := by
  refine noSp_seq (NoSp.of_all (by decide +kernel)) (byLen_noSp fun i hi => ?_)
  obtain ⟨h', hs⟩ := hall i hi
  rw [tail_eq h' hs]
  exact tail_noSp h' hf.hi hf.hc hf.hd hf.gi hf.gu hf.gf v

end VG.Proof.RsaPss.X86.Sg

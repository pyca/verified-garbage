module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.PcFn
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.PcBody
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.Recognize
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckDomainFn
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.Save
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.PcRecog
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.Table
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
import VerifiedGarbage.Proof.Ffdh.GenerationPrecompute
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_ffdh_generate_key_precompute` on PPC64LE: correctness

`front` saves the registers in the working space and the context's pointer
in its header (`pc_front`); the domain is recognized (`recognize_ok'`) and
the width stored in the header; then the setup, p's check, which the
domain's validity passes, `main_ok`, and the registers restored
(`pc_correct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Cached

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain
open VG.Impl.Ffdh.PPC64LE.Cached VG.Impl.Ffdh.PPC64LE.Cached.Precompute
open VG.Proof.Ffdh.PPC64LE.Domain
open VG.Proof.Bignum (slot)
open VG.Impl.Ffdh.PPC64LE.VettedValidation (tableSym tableConsts)

/-- The bytes at `Q` apart from `[S, S + Z)`. -/
theorem bytes_out {m m' : Mem} {S : Addr} {Z : Nat} (hf : ∀ x, Z ≤ ofs S x → m' x = m x) {Q : Addr} {n : Nat}
    (hsep : ∀ i < n, ∀ x, ofs S x < Z → off Q i ≠ x) : Spec.Rsa.bytesAt m' Q n = Spec.Rsa.bytesAt m Q n := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hf _ ?_
  by_contra hc
  exact hsep i (List.mem_range.mp hi) _ (by simp only [off]; omega) rfl

/-- What code ends in, with `sp` too. -/
theorem wp_sp {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun t => Q t ∧ t.sp = s.sp := by
  obtain ⟨tr, t, he, hq⟩ := h
  exact ⟨tr, t, he, hq, Exec.sp he⟩

/-- The context's pointer into the header, and the domain's arguments where
`recognize` reads them. -/
theorem pcHdr_ok {s : State} {S : Addr} (h23 : s.gpr .r23 = S) (hin : InRegions s.wr (off S 0) 8) :
    WP isa (.block [sth .r3 hCtx, .addi .r3 .r5 0, .addi .r4 .r6 0, .addi .r5 .r7 0]) s fun t =>
      (t.gpr .r3 = s.gpr .r5 ∧ t.gpr .r4 = s.gpr .r6 ∧ t.gpr .r5 = s.gpr .r7 ∧
        t.mem = s.mem.writeW (off S 0) (s.gpr .r3)) ∧ Bignum.PPC64LE.Keep [.r3, .r4, .r5] s t := by
  refine Bignum.PPC64LE.WP.keep _ ?_ (by decide)
  have i0 : InRegions s.wr (S + BitVec.ofNat 64 0) 8 := hin
  unfold sth
  prun [hCtx, h23, i0]
  simp

/-- `front`. -/
theorem pc_front {s : State} {S : Addr} {Z : Nat} (h8 : s.gpr .r8 = S) (hZ : 256 ≤ Z)
    (hin : ∀ i < 18, InRegions s.wr (off (savW S) (8 * i)) 8) (hin0 : InRegions s.wr (off S 0) 8) :
    WP isa (.block front) s fun t =>
      t.gpr .r23 = S ∧ t.gpr .r3 = s.gpr .r5 ∧ t.gpr .r4 = s.gpr .r6 ∧ t.gpr .r5 = s.gpr .r7 ∧
      word t.mem S 0 = s.gpr .r3 ∧ (∀ i < 18, word t.mem S (112 + 8 * i) = s.gpr (Impl.Ffdh.PPC64LE.Domain.saved i)) ∧
      (∀ x, Z ≤ ofs S x → t.mem x = s.mem x) ∧ Bignum.PPC64LE.Keep [.r23, .r3, .r4, .r5] s t := by
  unfold front
  refine WP.block_append (WP.mono (save_ok (ws := .r8) (by decide) s (by rw [h8]; exact hin)) fun s₁ hS => ?_)
  have h23 : s₁.gpr .r23 = S := hS.r23.trans h8
  refine WP.mono (pcHdr_ok h23 (by rw [hS.keep.wr]; exact hin0)) fun t ⟨⟨t3, t4, t5, tm⟩, kt⟩ => ?_
  have o := writeW_outside s₁.mem S (d := 0) (s₁.gpr .r3) (by omega)
  rw [← tm] at o
  refine ⟨(kt.gpr .r23 (by decide)).trans h23, ?_, ?_, ?_, ?_, fun i hi => ?_, fun x hx => ?_, hS.keep.trans kt⟩
  · rw [t3, hS.keep.gpr .r5 (by decide)]
  · rw [t4, hS.keep.gpr .r6 (by decide)]
  · rw [t5, hS.keep.gpr .r7 (by decide)]
  · rw [tm, word_writeW_self, hS.keep.gpr .r3 (by decide)]
  · rw [o.word (by omega) (by omega)]
    have ea : off (savW S) (8 * i) = off S (112 + 8 * i) := by rw [off, off, Offset.add_add]
    rw [← hS.saved i hi, h8, ea]
  · rw [o x (.inr (by omega))]
    refine hS.frame x fun r hr hcx => ?_
    rw [List.mem_singleton] at hr
    subst hr
    rw [h8] at hcx
    have hc' := (Offset.sub_base (n := 144) (k := Z) S (d := 112) (by omega)) _ hcx
    simp only [Region.Contains] at hc'
    simp only [ofs] at hx
    omega

/-- The width into the header. -/
theorem pcCap_ok {s : State} {S : Addr} (h23 : s.gpr .r23 = S) (hin : InRegions s.wr (off S 96) 8) :
    WP isa (.block [sth .r8 hCap]) s fun t => (t.mem = s.mem.writeW (off S 96) (s.gpr .r8)) ∧ Bignum.PPC64LE.Keep [] s t := by
  refine Bignum.PPC64LE.WP.keep _ ?_ (by decide)
  have i0 : InRegions s.wr (S + BitVec.ofNat 64 96) 8 := hin
  unfold sth
  prun [hCap, h23, i0]

/-- A table is apart from the writable regions. -/
theorem const_disjoint {K : List (String × List (BitVec 64))} {st : Nat} {s : State} {name : String}
    {ws : List (BitVec 64)} (h : ConstsOk K st s) (hc : (name, ws) ∈ K) :
    ∀ r ∈ s.wr, (⟨s.syms name, 8 * ws.length⟩ : Region).Disjoint r :=
  (h.2.2.1 ⟨s.syms name, 8 * ws.length⟩ (List.mem_map_of_mem (f := fun c =>
    (⟨s.syms c.1, 8 * c.2.length⟩ : Region)) hc)).2.1

/-- The table, in a state whose bytes apart from the working space are the
caller's. -/
theorem table_after {s t : State} {S : Addr} {Z : Nat} (hc : ConstsOk tableConsts 0 s)
    (hS : (⟨S, Z⟩ : Region) ∈ s.wr) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr) (hsym : t.syms = s.syms)
    (hfr : ∀ x, Z ≤ ofs S x → t.mem x = s.mem x) :
    VettedValidation.TableAt (t.syms tableSym) VG.Impl.Ffdh.VettedGroups.groups t := by
  have hK : (tableSym, VG.Impl.Ffdh.VettedGroups.tableWords) ∈ tableConsts := List.mem_cons_self
  have dTS := const_disjoint hc hK _ hS
  rw [VG.Proof.Ffdh.VettedTableFacts.tableWords_length, show 8 * 2218 = 17744 by decide] at dTS
  have sepT := sep_of_disjoint (L := 17744) dTS (by decide)
  have tread := VettedValidation.consts_read hc
  have tbytes := VettedValidation.consts_bytes hc
  rw [hsym]
  apply VettedValidation.tableOfBytes _ _ t (by rw [hrd, hwr]; exact tread)
    (by rw [bytes_out hfr fun i hi => sepT i (by
        change i < VG.Impl.Ffdh.VettedGroups.tableBytes.length at hi
        rw [VG.Proof.Ffdh.VettedTableFacts.tableBytes_length] at hi; exact hi)]
        exact tbytes)
    (by change VG.Impl.Ffdh.VettedGroups.tableBytes.length ≤ 17744
        rw [VG.Proof.Ffdh.VettedTableFacts.tableBytes_length])
  intro g hg
  simp only [VG.Impl.Ffdh.VettedGroups.groups, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem pc_pres_not_written : ∀ r ∈ preserved, (∀ i < 18, r ≠ Impl.Ffdh.PPC64LE.Domain.saved i) →
    r ∉ ([.r23, .r3, .r4, .r5] : List Reg) ++ VettedValidation.allClobbers ++ (([] : List Reg) ++ setup0Regs) ++
      ([.r0, .r6, .r12, .r14, .r15, .r16, .r17, .r18] : List Reg) ++ mainRegs := by
  decide

theorem pc_correct (s : State) (h : pcContract.pre s) :
    ∃ tr t, Exec isa Precompute.code s tr t ∧ abiPreserved s t ∧ pcContract.post s t := by
  show WP isa Precompute.code s fun t => abiPreserved s t ∧ pcPost s t
  obtain ⟨⟨hrd, hwr, dCD, dCS, dDS, nwC, nwD, nwS, ⟨hk, hk'⟩, hL, hcl, hsl, hdv⟩, hc⟩ := h
  simp only [stripConsts_gpr, stripConsts_wr, pcCtx, pcDomR, pcScr] at hwr dCD dCS dDS nwC nwD nwS hrd
  simp only [stripConsts_gpr, stripConsts_mem, pcDom] at hk hk' hL hcl hsl hdv
  simp only [Spec.Rsa.scratchWords] at hsl
  have memD : (⟨s.gpr .r5, (s.gpr .r6).toNat⟩ : Region) ∈ s.rd := by
    have : (⟨s.gpr .r5, (s.gpr .r6).toNat⟩ : Region) ∈ (stripConsts tableConsts s).rd := by
      rw [hrd]; exact List.mem_singleton_self _
    exact List.mem_of_mem_take this
  have hcl' : (s.gpr .r4).toNat = 3 + 34 * (((s.gpr .r7).toNat + 7) / 8) := by
    rw [hcl]
    simp only [Spec.Ffdh.generationPrecomputedWords, Spec.Rsa.FixedBaseComb.precomputedWords,
      Spec.Rsa.precomputedWords, Spec.Rsa.FixedBaseComb.entries, Spec.Rsa.FixedBaseComb.teeth, Spec.Rsa.modulusWords]
    omega
  rw [hcl'] at hwr dCD dCS nwC
  generalize hCd : s.gpr .r3 = C at hwr dCD dCS nwC ⊢
  generalize hDd : s.gpr .r5 = D at hwr dCD dDS nwD memD hL hdv ⊢
  generalize hLd : (s.gpr .r6).toNat = L at hwr dCD dDS nwD memD hL hdv ⊢
  generalize hkd : (s.gpr .r7).toNat = k at hk hk' hL hsl hdv hcl' hwr dCD dCS nwC ⊢
  generalize hSd : s.gpr .r8 = S at hwr dCS dDS nwS ⊢
  generalize hZd : (s.gpr .r9).toNat * 8 = Z at hwr dCS dDS nwS ⊢
  have tab := fun t => table_after (t := t) hc (S := S) (Z := Z) (by rw [hwr]; simp)
  clear hc
  have hL' : L = 2 * k ∨ L = 3 * k := by simp only [Spec.Ffdh.domainLenValid] at hL; omega
  generalize hwd : (k + 7) / 8 = w at hcl' hwr dCD dCS nwC
  have hw4 : 4 ≤ w := by omega
  have hw' : w ≤ 128 := by omega
  have hZw : slot w 28 ≤ Z := by rw [Domain.slot_eq]; omega_using [hsl, hZd, hwd, hk', hk]
  have e0 : slot w 0 = 256 := by rw [Domain.slot_eq]; omega
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ Z := by have := hZw; rw [Domain.slot_eq] at this; omega
  have hs : Scr s S Z := Scr.of_mem (by rw [hwr]; simp) nwS
  have hinS : ∀ d, d + 8 ≤ 256 → InRegions s.wr (off S d) 8 := fun d hd => ⟨⟨S, Z⟩, by rw [hwr]; simp,
    Offset.contains_base S (by omega) (by omega)⟩
  have hin : ∀ i < 18, InRegions s.wr (off (savW S) (8 * i)) 8 := fun i hi => ⟨⟨S, Z⟩, by rw [hwr]; simp, by
    rw [off, Offset.add_add]; exact Offset.contains_base S (by omega) (by omega)⟩
  have sepD := sep_of_disjoint (L := L) dDS (by omega)
  have sepDC := sep_of_disjoint (L := L) dCD.symm (by omega)
  have rdD := rd_of_mem (s := s) (D := D) (L := L) memD (by omega)
  have sepCB : ∀ x, ofs C x < 8 * (3 + 34 * w) → Z ≤ ofs S x := fun x hx => by
    have := Pub.sep_of_disjoint dCS x (by simp only [VG.Proof.Bignum.ofs, ofs] at hx ⊢; omega)
    simp only [VG.Proof.Bignum.ofs, ofs] at this ⊢; omega
  have sepBC : ∀ x, ofs S x < Z → 8 * (3 + 34 * w) ≤ ofs C x := fun x hx => by
    have := Pub.sep_of_disjoint dCS.symm x (by simp only [VG.Proof.Bignum.ofs, ofs] at hx ⊢; omega)
    simp only [VG.Proof.Bignum.ofs, ofs] at this ⊢; omega
  unfold Precompute.code
  -- The front.
  refine WP.seq (WP.mono_syms (pc_front (Z := Z) hSd (Nat.le_trans (Nat.le_add_right _ _) hZ) hin (hinS 0 (by decide)))
    fun s₁ ⟨a23, a3, a4, a5, w0, wsav, fr1, k1⟩ sym1 => ?_)
  rw [hCd] at w0
  have hdom1 : Spec.Rsa.bytesAt s₁.mem D L = Spec.Rsa.bytesAt s.mem D L := bytes_out fr1 sepD
  have hlen : (Spec.Rsa.bytesAt s.mem D L).length = L := VG.Proof.Bignum.bytesAt_length _ _ _
  have ctx1 : VettedValidation.Context D k (Spec.Rsa.bytesAt s.mem D L) s₁ := by
    refine ⟨a3.trans hDd, ?_, ?_, ?_, ?_, by rw [hlen]; exact hL', hk, hk'⟩
    · rw [a4, hlen, ← hLd, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [a5, ← hkd, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [hlen, k1.rd, k1.wr]
      exact ⟨_, List.mem_append_left _ memD, Region.contains_self _ _⟩
    · rw [hlen, hdom1]
  have table1 := tab s₁ k1.rd k1.wr sym1 fr1
  -- The recognition.
  refine WP.seq (WP.mono (wp_sp (VettedValidation.recognize_ok' ctx1 table1))
    fun s₂ ⟨⟨r8v, m2, k2', lr2⟩, sp2⟩ => ?_)
  have k2 : Bignum.PPC64LE.Keep VettedValidation.allClobbers s₁ s₂ := ⟨k2'.1, k2'.2.1, k2'.2.2, sp2, lr2⟩
  have k12 := k1.trans k2
  -- The width and the setup.
  have g23 : s₂.gpr .r23 = S := (k2.gpr .r23 (by decide)).trans a23
  refine WP.seq (WP.block_append (WP.mono (pcCap_ok g23 (by rw [k12.wr]; exact hinS 96 (by decide)))
    fun s₂' ⟨m2', kc⟩ => ?_))
  refine WP.mono (setup0_ok (D := D) (L := L) (k := k)
    ((kc.gpr .r3 (by decide)).trans ((k2.gpr .r3 (by decide)).trans (a3.trans hDd)))
    (by rw [kc.gpr .r4 (by decide), k2.gpr .r4 (by decide), a4, ← hLd, VG.Proof.Bignum.ofNat_toNat64])
    (by rw [kc.gpr .r5 (by decide), k2.gpr .r5 (by decide), a5, ← hkd, VG.Proof.Bignum.ofNat_toNat64])
    ((kc.gpr .r23 (by decide)).trans g23) hk') fun s₃ ⟨⟨a21, a27, a28, a11, a29, a10, a31, m3⟩, k3⟩ => ?_
  rw [hwd] at a11 a29 a10
  have k13 := (k12.trans kc).trans k3
  have oc := writeW_outside s₂.mem S (d := 96) (s₂.gpr .r8) (by omega)
  rw [← m2'] at oc
  have fr3 : ∀ x, Z ≤ ofs S x → s₃.mem x = s.mem x := fun x hx => by
    rw [m3, oc x (.inr (by omega)), m2]; exact fr1 x hx
  have e3 : Env s₃ S Z w := ⟨hs.congr k13.wr, a10, a29, a11, a31, hw4, hw', hZw⟩
  have w3 : ∀ d, d + 8 ≤ 96 ∨ 104 ≤ d → d + 8 ≤ 256 → word s₃.mem S d = word s₁.mem S d := fun d hd hd' => by
    rw [m3, oc.word (by omega) (by omega), m2]
  have hdom3 : Spec.Rsa.bytesAt s₃.mem D L = Spec.Rsa.bytesAt s.mem D L := bytes_out fr3 sepD
  -- p.
  refine WP.seq (WP.mono (loadP_ok e3 a21 a28 hwd.symm hk hk' (fun i hi => by
      rw [k13.rd, k13.wr]; exact rdD i (by omega)) (fun i hi => sepD i (by omega)))
    fun s₄ ⟨⟨p4, c4, b4⟩, k4⟩ => ?_)
  have hDk : Spec.Rsa.bytesAt s₃.mem D k = Spec.Rsa.bytesAt s.mem D k := bytes_out fr3 fun i hi => sepD i (by omega)
  rw [hDk] at p4 c4
  have k14 := k13.trans k4
  have e4 : Env s₄ S Z w := e3.keep k4 (by decide)
  have fr4 : ∀ x, Z ≤ ofs S x → s₄.mem x = s.mem x := fun x hx => by
    rw [b4 x (.inr (by rw [e0]; omega)), fr3 x hx]
  have w4 : ∀ d, d + 8 ≤ 96 ∨ 104 ≤ d → d + 8 ≤ 256 → word s₄.mem S d = word s₁.mem S d := fun d hd hd' => by
    rw [Outside.word b4 (by rw [e0]; omega) (by omega), w3 d hd hd']
  have hdom4 : Spec.Rsa.bytesAt s₄.mem D L = Spec.Rsa.bytesAt s.mem D L := bytes_out fr4 sepD
  have hmod := VG.Proof.Ffdh.domainValid_mod hdv
  rw [VG.Proof.Ffdh.domainOf_p _ _ (by omega)] at hmod
  have hlenD : k ≤ (Spec.Rsa.bytesAt s.mem D L).length := by rw [hlen]; omega
  have hgen := VG.Proof.Ffdh.generationPrecompute_eq hlenD (by
    rw [VG.Proof.Ffdh.take_bytesAt s.mem D (by omega : k ≤ L)]; exact hmod)
  have mp : MP S D C Z k L s₄ := by
    refine ⟨by rw [hwd]; exact e4, (k4.gpr .r23 (by decide)).trans ((k3.gpr .r23 (by decide)).trans ((kc.gpr .r23 (by decide)).trans g23)),
      (k4.gpr .r21 (by decide)).trans a21, (k4.gpr .r27 (by decide)).trans a27, (k4.gpr .r28 (by decide)).trans a28,
      hk, hk', hL', fun i hi => by rw [k14.rd, k14.wr]; exact rdD i hi, sepD,
      fun i hi x hx => sepDC i hi x (by rw [ctxWords] at hx; omega), ?_, fun x hx => sepCB x (by rw [ctxWords] at hx; omega),
      fun x hx => by have := sepBC x hx; rw [ctxWords]; omega, ?_, ?_, ?_, by rw [hdom4]; exact hdv⟩
    · exact Scr.of_mem (by rw [k14.wr, hwr]; simp [ctxWords]; omega) (by rw [ctxWords]; omega)
    · show word s₄.mem S hCtx = C
      rw [show hCtx = 0 from rfl, w4 0 (by omega) (by omega), w0]
    · show word s₄.mem S hCap = _
      rw [show hCap = 96 from rfl, Outside.word b4 (by rw [e0]; omega) (by omega), m3, m2', word_writeW_self,
        r8v, hdom4]
    · rw [hwd, p4, hdom4, VG.Proof.Ffdh.domainOf_p _ _ (by omega)]
  -- The main or, impossibly, the invalid branch.
  have hite : WP isa (.ite (.zero .d .r0) main (.block [.li .r3 0])) s₄ fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 1 ∧
        Spec.Rsa.wordsAt t.mem C (3 + 34 * w) = VG.Proof.Ffdh.generationValues k (Spec.Rsa.bytesAt s.mem D L) ∧
        (∀ i < 18, word t.mem S (112 + 8 * i) = s.gpr (Impl.Ffdh.PPC64LE.Domain.saved i))) ∧ Bignum.PPC64LE.Keep mainRegs s₄ t := by
    refine WP.ite (s₄.gpr .r0 == 0) (eval_zero _ _) (fun hz => ?_) (fun hz => ?_)
    · refine WP.mono (main_ok mp) fun t ⟨⟨t3, tw, tm⟩, kt⟩ => ⟨⟨t3, by rw [← hwd, tw, hdom4], fun i hi => ?_⟩, kt⟩
      have hm : Outside S (slot w 1) (2 ^ 64) s₄.mem t.mem := fun x hx => by
        rcases hx with hx | hx
        · rw [← hwd] at hx; exact tm x hx
        · exact absurd hx (by have := (x - S).isLt; simp only [ofs]; omega)
      rw [Outside.word hm (by rw [Domain.slot_eq]; omega) (by omega), w4 _ (by omega) (by omega)]
      exact wsav i hi
    · exact absurd (c4.mpr hmod) (by simpa using hz)
  refine WP.seq (WP.mono hite fun t₅ ⟨⟨t3, tw, tsav⟩, k5⟩ => ?_)
  have kall := k14.trans k5
  have hsav' : ∀ i < 18, t₅.mem.readW (off (savW S) (8 * i)) 64 = s.gpr (Impl.Ffdh.PPC64LE.Domain.saved i) :=
      fun i hi => by
    have ea : off (savW S) (8 * i) = off S (112 + 8 * i) := by rw [off, off, Offset.add_add]
    rw [ea]
    exact tsav i hi
  refine WP.mono (restore_ok t₅ ((k5.gpr .r23 (by decide)).trans ((k4.gpr .r23 (by decide)).trans
      ((k3.gpr .r23 (by decide)).trans ((kc.gpr .r23 (by decide)).trans g23)))) (by rw [kall.wr]; exact hin) hsav')
    fun u ⟨urs, uot, um, _, _, usp, ulr⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [usp, kall.sp], by rw [ulr, kall.lr]⟩, ?_, ?_⟩
  · by_cases hs' : ∃ i < 18, r = Impl.Ffdh.PPC64LE.Domain.saved i
    · obtain ⟨i, hi, rfl⟩ := hs'
      exact urs i hi
    · have hn : ∀ i < 18, r ≠ Impl.Ffdh.PPC64LE.Domain.saved i := fun i hi e => hs' ⟨i, hi, e⟩
      rw [uot r hn, kall.gpr r (pc_pres_not_written r hr hn)]
  · rw [uot .r3 (by decide), t3]; rfl
  · show Spec.Ffdh.generationPrecompute (s.gpr .r7).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) =
      some (Spec.Rsa.wordsAt u.mem (s.gpr .r3) (s.gpr .r4).toNat)
    rw [hCd, hDd, hLd, hkd, hcl', um, tw]
    exact hgen

end VG.Proof.Ffdh.PPC64LE.Cached

module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.PcBody
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.PcFn
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.PcRecog
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PubSave
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Bignum.RISCV64.PubMid
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.GenerationPrecompute
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RISCV64.Syms
import VerifiedGarbage.Proof.Ffdh.VettedTableFacts
-- separate module: the precompute's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it

/-!
# `vg_ffdh_generate_key_precompute` on RISC-V: correctness

The exchange's data of the precompute (`pcx`): `out` the context, x the
domain's `p_len` octets and the peer g's. `pcFront_ok`: the registers saved
and the header's words 0–3; `recog_ok`: the recognized width; `post_ok`:
`Base`; then `loadP_X`, `bound_step` and `rest_ok` (`pc_correct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.Cached

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64.Cached VG.Impl.Ffdh.RISCV64.Cached.Precompute
open VG.Proof.Bignum.RISCV64
open VG.Proof.Ffdh.RISCV64
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Pub (savW savR)
open VG.Impl.Ffdh.RISCV64.VettedValidation (tableSym tableConsts)

/-- The exchange's data of a precompute: the context as `out`, the domain's
`p_len` octets as x, g's as the peer. -/
def pcx (s : State) : XD :=
  ⟨s.gpr .a0, s.gpr .a2, (s.gpr .a3).toNat, (s.gpr .a4).toNat, s.gpr .a2, (s.gpr .a4).toNat,
    off (s.gpr .a2) (s.gpr .a4).toNat, s.gpr .a5, (s.gpr .a6).toNat * 8,
    Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat⟩

theorem ofNat_toNat64 (v : BitVec 64) : BitVec.ofNat 64 v.toNat = v := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The header's words 0–3: the context, the domain, `p_len` and g's
address; the domain's arguments where `recognize` reads them. -/
theorem pcHdr_ok {s : State} {S : Addr} {Z : Nat} (hs : Scr s S Z) (hZ : 32 ≤ Z) (h6 : s.gpr .s6 = S) :
    WP isa (.block ([.store .d .a0 .s6 0, .store .d .a2 .s6 8, .store .d .a4 .s6 16, .add .t2 .a2 .a4,
      .store .d .t2 .s6 24, .addi .a0 .a2 0, .addi .a1 .a3 0, .addi .a2 .a4 0] : List Instr)) s fun t =>
      (word t.mem S 0 = s.gpr .a0 ∧ word t.mem S 8 = s.gpr .a2 ∧ word t.mem S 16 = s.gpr .a4 ∧
        word t.mem S 24 = s.gpr .a2 + s.gpr .a4 ∧ t.gpr .a0 = s.gpr .a2 ∧ t.gpr .a1 = s.gpr .a3 ∧
        t.gpr .a2 = s.gpr .a4 ∧ Outside S 0 32 s.mem t.mem) ∧ Keep [.t2, .a0, .a1, .a2] s t := by
  have hn := hs.nowrap
  have h6' : s.gpr .s6 = off S 0 := by rw [h6]; simp [off]
  have i0 := hs.st (d := 0) (n := 8) (by omega_arith)
  have i8 := hs.st (d := 8) (n := 8) (by omega_arith)
  have i16 := hs.st (d := 16) (n := 8) (by omega_arith)
  have i24 := hs.st (d := 24) (n := 8) (by omega_arith)
  have l0 := hs.al8 (d := 0) (by omega_arith) (by decide)
  have l8 := hs.al8 (d := 8) (by omega_arith) (by decide)
  have l16 := hs.al8 (d := 16) (by omega_arith) (by decide)
  have l24 := hs.al8 (d := 24) (by omega_arith) (by decide)
  have o0 := writeW_outside s.mem S (d := 0) (s.gpr .a0) (by omega_arith)
  have o1 := writeW_outside (s.mem.writeW (off S 0) (s.gpr .a0)) S (d := 8) (s.gpr .a2) (by omega_arith)
  have o2 := writeW_outside ((s.mem.writeW (off S 0) (s.gpr .a0)).writeW (off S 8) (s.gpr .a2)) S (d := 16)
    (s.gpr .a4) (by omega_arith)
  have o3 := writeW_outside (((s.mem.writeW (off S 0) (s.gpr .a0)).writeW (off S 8) (s.gpr .a2)).writeW
    (off S 16) (s.gpr .a4)) S (d := 24) (s.gpr .a2 + s.gpr .a4) (by omega_arith)
  refine WP.mono (WP.keep [.t2, .a0, .a1, .a2] (Q := fun t => t.mem = (((s.mem.writeW (off S 0) (s.gpr .a0)).writeW
      (off S 8) (s.gpr .a2)).writeW (off S 16) (s.gpr .a4)).writeW (off S 24) (s.gpr .a2 + s.gpr .a4) ∧
      t.gpr .a0 = s.gpr .a2 ∧ t.gpr .a1 = s.gpr .a3 ∧ t.gpr .a2 = s.gpr .a4) ?_ (by rfl) (by rfl))
    fun t ⟨⟨tm, t0, t1, t2⟩, kt⟩ => ⟨⟨?_, ?_, ?_, ?_, t0, t1, t2, ?_⟩, kt⟩
  · brun [h6', i0, i8, i16, i24, l0, l8, l16, l24]
    exact ⟨BitVec.add_zero _, BitVec.add_zero _, BitVec.add_zero _⟩
  · rw [tm, o3.word (by omega_arith) (by omega_arith), o2.word (by omega_arith) (by omega_arith),
      o1.word (by omega_arith) (by omega_arith)]
    exact word_writeW_self _ _ _ _
  · rw [tm, o3.word (by omega_arith) (by omega_arith), o2.word (by omega_arith) (by omega_arith)]
    exact word_writeW_self _ _ _ _
  · rw [tm, o3.word (by omega_arith) (by omega_arith)]
    exact word_writeW_self _ _ _ _
  · rw [tm]; exact word_writeW_self _ _ _ _
  · rw [tm]
    exact (((o0.mono (by omega_arith) (by omega_arith)).trans (o1.mono (by omega_arith) (by omega_arith))).trans
      (o2.mono (by omega_arith) (by omega_arith))).trans (o3.mono (by omega_arith) (by omega_arith))

/-- What the front leaves. -/
structure PF (s t : State) : Prop where
  s6 : t.gpr .s6 = s.gpr .a5
  sav : ∀ i < 12, t.mem.readW (off (savW (s.gpr .a5)) (8 * i)) 64 = s.gpr (PublicChecked.saved i)
  w0 : word t.mem (s.gpr .a5) 0 = s.gpr .a0
  w8 : word t.mem (s.gpr .a5) 8 = s.gpr .a2
  w16 : word t.mem (s.gpr .a5) 16 = s.gpr .a4
  w24 : word t.mem (s.gpr .a5) 24 = s.gpr .a2 + s.gpr .a4
  a0 : t.gpr .a0 = s.gpr .a2
  a1 : t.gpr .a1 = s.gpr .a3
  a2 : t.gpr .a2 = s.gpr .a4
  a3 : t.gpr .a3 = s.gpr .a3
  a4 : t.gpr .a4 = s.gpr .a4
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  out : Outside (s.gpr .a5) 0 256 s.mem t.mem
  syms : t.syms = s.syms

theorem pcWords_eq (k : Nat) : Spec.Ffdh.generationPrecomputedWords k = ctxWords ((k + 7) / 8) := by
  simp only [Spec.Ffdh.generationPrecomputedWords, Spec.Rsa.FixedBaseComb.precomputedWords,
    Spec.Rsa.precomputedWords, Spec.Rsa.FixedBaseComb.entries, Spec.Rsa.FixedBaseComb.teeth, Spec.Rsa.modulusWords,
    ctxWords]
  omega_arith

/-- The precondition's facts, by name. -/
structure PP (s : State) : Prop where
  rd : (pcDomR s) ∈ s.rd
  wr : s.wr = [pcCtx s, pcScr s]
  dCD : (pcCtx s).Disjoint (pcDomR s)
  dCS : (pcCtx s).Disjoint (pcScr s)
  dDS : (pcDomR s).Disjoint (pcScr s)
  nwC : (s.gpr .a0).toNat + (s.gpr .a1).toNat * 8 ≤ 2 ^ 64
  nwD : (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64
  nwS : (s.gpr .a5).toNat + (s.gpr .a6).toNat * 8 ≤ 2 ^ 64
  k64 : 64 ≤ (s.gpr .a4).toNat
  k1024 : (s.gpr .a4).toNat ≤ 1024
  hL : (s.gpr .a3).toNat = 2 * (s.gpr .a4).toNat ∨ (s.gpr .a3).toNat = 3 * (s.gpr .a4).toNat
  hcl : (s.gpr .a1).toNat = ctxWords (((s.gpr .a4).toNat + 7) / 8)
  hsl : 16 * (s.gpr .a4).toNat + 32 ≤ (s.gpr .a6).toNat
  dv : Spec.Ffdh.domainValid (s.gpr .a4).toNat (pcDom s) = true
  alC : (s.gpr .a0).toNat % 8 = 0
  alS : (s.gpr .a5).toNat % 8 = 0
  cs : ConstsOk tableConsts 0 s

theorem pp_of {s : State} (h : pcContract.pre s) : PP s := by
  obtain ⟨⟨hrd, hwr, dCD, dCS, dDS, nwC, nwD, nwS, ⟨hk, hk'⟩, hL, hcl, hsl, hdv, alC, alS⟩, hc⟩ := h
  simp only [Spec.Rsa.scratchWords, stripConsts_gpr] at hsl hL hcl
  refine ⟨stripConsts_rd_mem (K := tableConsts) (by rw [hrd]; exact List.mem_cons_self), hwr, dCD, dCS, dDS, nwC,
    nwD, nwS, hk, hk', by simp only [Spec.Ffdh.domainLenValid] at hL; omega_arith, by rw [hcl, pcWords_eq], hsl,
    hdv, alC, alS, hc⟩

/-- `front`. -/
theorem pcFront_ok {s : State} (h : PP s) : WP isa (.block front) s (PF s) := by
  suffices hw : WP isa (.block front) s fun t => t.syms = s.syms → PF s t from WP.mono_syms hw fun _ h₁ h₂ => h₁ h₂
  have hS : Scr s (s.gpr .a5) ((s.gpr .a6).toNat * 8) := Scr.of_mem (by rw [h.wr]; simp) h.nwS h.alS
  have hn := h.nwS
  unfold front
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (WP.keep [.t0] (Q := fun t => t.gpr .t0 = s.gpr .a5 ∧ t.mem = s.mem)
    (by brun [add_ofNat_zero]) (by rfl) (by rfl)) fun s₁ ⟨⟨a0', m1⟩, k1⟩ => ?_)
  have hin : ∀ i < 12, InRegions s₁.wr (off (savW (s₁.gpr .t0)) (8 * i)) 8 := fun i hi => by
    rw [a0', k1.2.2, h.wr]
    show InRegions _ (s.gpr .a5 + BitVec.ofNat 64 128 + BitVec.ofNat 64 (8 * i)) 8
    rw [Offset.add_add]
    have := h.hsl
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  refine WP.block_append (WP.mono (Pub.save_ok s₁ hin (fun i hi => by
    rw [a0']; exact Pub.sav_al h.alS (by have := h.hsl; omega_arith) hi)) fun s₂ hSv => ?_)
  have k12 := k1.trans hSv.keep
  have h6₂ : s₂.gpr .s6 = s.gpr .a5 := hSv.s6.trans a0'
  refine WP.mono (pcHdr_ok (hS.congr k12.2.2) (by have := h.hsl; omega_arith) h6₂)
    fun t ⟨⟨w0, w8, w16, w24, t0, t1, t2, o3⟩, k3⟩ hsy => ?_
  have k := k12.trans k3
  have g : ∀ r ∈ ([.a0, .a2, .a3, .a4] : List Reg), s₂.gpr r = s.gpr r := fun r hr => k12.gpr (by revert r hr; decide)
  have hm2 : Outside (s.gpr .a5) 0 256 s.mem s₂.mem := fun y hy => by
    rw [← m1]
    refine hSv.frame y fun r hr hc => ?_
    rw [List.mem_singleton] at hr
    subst hr
    rw [a0'] at hc
    have hc' := (Offset.sub_base (n := 96) (k := 256) (s.gpr .a5) (d := 128) (by have := h.hsl; omega_arith)) _ hc
    simp only [Region.Contains] at hc'
    simp only [ofs] at hy
    omega_arith
  refine ⟨(k3.gpr (by decide)).trans h6₂, fun i hi => ?_, by rw [w0, g .a0 (by decide)],
    by rw [w8, g .a2 (by decide)], by rw [w16, g .a4 (by decide)], by rw [w24, g .a2 (by decide), g .a4 (by decide)],
    by rw [t0, g .a2 (by decide)], by rw [t1, g .a3 (by decide)], by rw [t2, g .a4 (by decide)],
    by rw [k3.gpr (by decide), g .a3 (by decide)], by rw [k3.gpr (by decide), g .a4 (by decide)], k.2.1, k.2.2,
    hm2.trans (o3.mono (Nat.le_refl _) (by omega_arith)), hsy⟩
  have e : off (savW (s.gpr .a5)) (8 * i) = off (s.gpr .a5) (128 + 8 * i) := by rw [off, off, Offset.add_add]
  rw [e]
  show word t.mem (s.gpr .a5) (128 + 8 * i) = _
  rw [o3.word (Or.inr (by omega_arith)) (by have := h.hsl; omega_arith)]
  show s₂.mem.readW (off (s.gpr .a5) (128 + 8 * i)) 64 = _
  rw [← e, ← a0', hSv.saved i hi, k1.gpr fun h' => Pub.saved_ne_t0 i hi (List.mem_singleton.mp h')]

/-- The domain's octets after the front, apart from the working space. -/
theorem pf_bytes {s t : State} (h : PP s) (hf : PF s t) {Q : Addr} {n : Nat}
    (hsep : ∀ i < n, ∀ x, ofs (s.gpr .a5) x < (s.gpr .a6).toNat * 8 → off Q i ≠ x) :
    Spec.Rsa.bytesAt t.mem Q n = Spec.Rsa.bytesAt s.mem Q n :=
  Pub.bytes_apart (o := 0) (n := 256) hf.out (by have := h.hsl; omega_arith) hsep

/-- The recognized width of the domain. -/
abbrev pcCap (s : State) : Nat :=
  VG.Impl.Ffdh.VettedGroups.recognizeList VG.Impl.Ffdh.VettedGroups.groups (s.gpr .a4).toNat (pcDom s)

theorem sepDS {s : State} (h : PP s) :
    ∀ i < (s.gpr .a3).toNat, ∀ x, ofs (s.gpr .a5) x < (s.gpr .a6).toNat * 8 → off (s.gpr .a2) i ≠ x :=
  Pub.ne_of_disjoint h.dDS (Nat.le_of_lt (s.gpr .a3).isLt)

/-- `recognize`, after the front. -/
theorem recog_ok {s t : State} (h : PP s) (hf : PF s t) :
    WP isa VG.Impl.Ffdh.RISCV64.VettedValidation.recognize t fun u =>
      PF s u ∧ u.gpr .a5 = BitVec.ofNat 64 (pcCap s) := by
  have hlen : (pcDom s).length = (s.gpr .a3).toNat := by simp [pcDom, Spec.Rsa.bytesAt]
  have input : VettedValidation.Ctx (s.gpr .a2) (s.gpr .a4).toNat (pcDom s) t :=
    ⟨hf.a0, by rw [hf.a1, hlen, ofNat_toNat64], by rw [hf.a2, ofNat_toNat64],
      ⟨_, List.mem_append_left _ (by rw [hf.rd]; exact h.rd), by rw [hlen]; exact Region.contains_self _ _⟩,
      by rw [hlen, pf_bytes h hf (sepDS h)], by rw [hlen]; exact h.hL, h.k64, h.k1024⟩
  have cb := VettedValidation.consts_bytes h.cs
  have hT : (⟨s.syms tableSym, 8 * VG.Impl.Ffdh.VettedGroups.tableWords.length⟩ : Region).Disjoint (pcScr s) :=
    ConstsOk.wr1 h.cs _ (by rw [h.wr]; simp)
  rw [VG.Proof.Ffdh.VettedTableFacts.tableWords_length] at hT
  have table : VettedValidation.TableAt (t.syms tableSym) VG.Impl.Ffdh.VettedGroups.groups t := by
    refine VettedValidation.table_at (s := t) (by rw [hf.rd, hf.wr, hf.syms]; exact cb.1) ?_
    · have sepT : ∀ i < VG.Impl.Ffdh.VettedGroups.tableBytes.length, ∀ x,
          ofs (s.gpr .a5) x < (s.gpr .a6).toNat * 8 → off (s.syms tableSym) i ≠ x := fun i hi =>
        Pub.ne_of_disjoint hT (by decide) i (by rw [VG.Proof.Ffdh.VettedTableFacts.tableBytes_length] at hi; omega_arith)
      rw [hf.syms, pf_bytes h hf sepT]
      exact cb.2
  refine WP.mono_syms (VettedValidation.recognize_val input table) fun u ⟨ua, um, uk⟩ usy => ⟨?_, ua⟩
  have g : ∀ r ∈ ([.s6, .a0, .a1, .a2, .a3, .a4] : List Reg), u.gpr r = t.gpr r :=
    fun r hr => uk.gpr (by revert r hr; decide)
  exact ⟨(g .s6 (by decide)).trans hf.s6, fun i hi => by rw [um]; exact hf.sav i hi, by rw [um]; exact hf.w0,
    by rw [um]; exact hf.w8, by rw [um]; exact hf.w16, by rw [um]; exact hf.w24, (g .a0 (by decide)).trans hf.a0,
    (g .a1 (by decide)).trans hf.a1, (g .a2 (by decide)).trans hf.a2, (g .a3 (by decide)).trans hf.a3,
    (g .a4 (by decide)).trans hf.a4, uk.2.1.trans hf.rd, uk.2.2.trans hf.wr, by rw [um]; exact hf.out,
    usy.trans hf.syms⟩

/-- `post`: `Base` of the precompute's data. -/
theorem post_ok {s u : State} (h : PP s) (hf : PF s u) :
    WP isa (.block post) u fun v => Base (pcx s) v ∧ v.gpr .a2 = s.gpr .a2 ∧ v.gpr .a3 = s.gpr .a3 ∧
      v.gpr .a4 = s.gpr .a4 ∧ v.gpr .a5 = u.gpr .a5 ∧ v.mem = u.mem ∧ v.rd = s.rd ∧ v.wr = s.wr := by
  have hS : Scr u (s.gpr .a5) ((s.gpr .a6).toNat * 8) := Scr.of_mem (by rw [hf.wr, h.wr]; simp) h.nwS h.alS
  have hsl := h.hsl
  have hk := h.k64; have hk' := h.k1024
  have h6' : u.gpr .s6 = off (s.gpr .a5) 0 := by rw [hf.s6]; simp [off]
  have l0 := hS.ld (d := 0) (n := 8) (by omega_arith)
  have a0' := hS.al8 (d := 0) (by omega_arith) (by decide)
  unfold post
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.a2, .s7, .s8, .a1, .a0] (Q := fun t => t.gpr .a2 = s.gpr .a2 ∧ t.gpr .s7 = s.gpr .a2 ∧
      t.gpr .s8 = s.gpr .a4 ∧ t.gpr .a1 = s.gpr .a4 ∧ t.gpr .a0 = s.gpr .a0 ∧ t.mem = u.mem)
    (by
      brun [hf.a0, hf.a2, hf.a4, h6', l0, a0']
      exact ⟨BitVec.add_zero _, BitVec.add_zero _, BitVec.add_zero _, BitVec.add_zero _, hf.w0⟩) (by rfl) (by rfl)) fun t₁ ⟨⟨b2, b7, b8, b1, b0, m1⟩, k1⟩ => ?_
  refine WP.mono (Pub.setup_ok (O := s.gpr .a0) (k := (s.gpr .a4).toNat) b0 (by rw [b1, ofNat_toNat64])
    ((k1.gpr (by decide)).trans hf.s6) hk') fun v ⟨⟨j10, j11, j0, j5, j7, jm⟩, k2⟩ => ?_
  have k := k1.trans k2
  have hrdv : v.rd ++ v.wr = s.rd ++ s.wr := by rw [k.2.1, k.2.2, hf.rd, hf.wr]
  have hvm : v.mem = u.mem := by rw [jm, m1]
  have hLk : 2 * (s.gpr .a4).toNat ≤ (s.gpr .a3).toNat ∧ (s.gpr .a3).toNat ≤ 3 * (s.gpr .a4).toNat := by
    have := h.hL; omega_arith
  have hcl := h.hcl
  have nwC := h.nwC
  have hCk : (s.gpr .a4).toNat ≤ (s.gpr .a1).toNat * 8 := by rw [hcl]; unfold ctxWords; omega_arith
  have sepD := sepDS h
  have rdD : ∀ i < (s.gpr .a3).toNat, InRegions (v.rd ++ v.wr) (off (s.gpr .a2) i) 1 := by
    rw [hrdv]; exact rd_of_mem h.rd (Nat.le_refl _) (BitVec.isLt _)
  have hb := pf_bytes h hf sepD
  refine ⟨⟨⟨Scr.of_mem (by rw [k.2.2, hf.wr, h.wr]; simp [pcx]) h.nwS h.alS, hk, hk', hLk, ?_, by
      change (s.gpr .a0).toNat + (s.gpr .a4).toNat ≤ _; omega_arith,
      fun i hi => ⟨pcCtx s, by rw [k.2.2, hf.wr, h.wr]; simp,
        Offset.contains_base _ (by change i < (s.gpr .a4).toNat at hi; omega_arith)
          (by change i < (s.gpr .a4).toNat at hi; omega_arith)⟩,
      fun y hy => Pub.sep_of_disjoint h.dCS y (by
        have : (y - s.gpr .a0).toNat < (s.gpr .a4).toNat := hy
        show (y - s.gpr .a0).toNat < _; omega_arith),
      rdD, sepD,
      fun i hi => by
        change i < (s.gpr .a4).toNat at hi
        show InRegions _ (off (off (s.gpr .a2) (s.gpr .a4).toNat) i) 1
        rw [Derive.off_off]; exact rdD _ (by omega_arith),
      fun i hi => by
        change i < (s.gpr .a4).toNat at hi
        show ∀ y, _ → off (off (s.gpr .a2) (s.gpr .a4).toNat) i ≠ y
        rw [Derive.off_off]; exact sepD _ (by omega_arith),
      fun i hi => rdD i (by change i < (s.gpr .a4).toNat at hi; omega_arith),
      fun i hi => sepD i (by change i < (s.gpr .a4).toNat at hi; omega_arith),
      by change 1 ≤ (s.gpr .a4).toNat; omega_arith, Nat.le_refl _, by rw [hvm]; exact hb,
      by rw [hvm]; exact hf.w0.trans (add_ofNat_zero _).symm, by rw [hvm]; exact hf.w8.trans (add_ofNat_zero _).symm,
      by rw [hvm]; exact hf.w16.trans (ofNat_toNat64 _).symm,
      by
        rw [hvm]; refine hf.w24.trans ?_
        show s.gpr .a2 + s.gpr .a4 = s.gpr .a2 + BitVec.ofNat 64 (s.gpr .a4).toNat
        rw [ofNat_toNat64]⟩,
    by rw [k2.gpr (by decide), k1.gpr (by decide), hf.s6]; rfl, j7, by rw [j5]; rfl, j0,
    by rw [k2.gpr (by decide), b7]; exact (add_ofNat_zero _).symm,
    by rw [k2.gpr (by decide), b8]; exact (ofNat_toNat64 _).symm,
    by rw [j10]; exact (add_ofNat_zero _).symm, j11⟩,
    by rw [k2.gpr (by decide), b2], by rw [k.gpr (by decide), hf.a3], by rw [k.gpr (by decide), hf.a4],
    k.gpr (by decide), hvm, by rw [k.2.1, hf.rd], by rw [k.2.2, hf.wr]⟩
  show slot (((s.gpr .a4).toNat + 7) / 8) 24 ≤ (s.gpr .a6).toNat * 8
  unfold slot hdrBytes; omega_arith

/-- `MP` after p's load, from the precondition. -/
theorem mp_of {s t₄ : State} (h : PP s) (h4 : X4 (pcx s) t₄) (r4 : t₄.wr = s.wr) (a2 : t₄.gpr .a2 = s.gpr .a2)
    (a3 : t₄.gpr .a3 = s.gpr .a3) (a4 : t₄.gpr .a4 = s.gpr .a4) (a5 : t₄.gpr .a5 = BitVec.ofNat 64 (pcCap s)) :
    MP (pcx s) t₄ := by
  have hcl := h.hcl
  have e8 : (s.gpr .a1).toNat * 8 = 8 * ctxWords (pcx s).w := by
    show _ = 8 * ctxWords (((s.gpr .a4).toNat + 7) / 8); rw [hcl]; omega_arith
  have dCD := h.dCD
  have dCS := h.dCS
  rw [show pcCtx s = ⟨s.gpr .a0, 8 * ctxWords (pcx s).w⟩ by simp only [pcCtx, e8]] at dCD dCS
  refine ⟨h4.1, h4.2.1, a2, by rw [a3]; exact (ofNat_toNat64 _).symm,
    by rw [a4]; exact (ofNat_toNat64 _).symm, a5, h.dv, h.hL, rfl,
    Scr.of_mem (by rw [r4, h.wr]; simp [pcCtx, pcx, e8]) (by rw [← e8]; exact h.nwC) h.alC,
    fun y hy => Pub.sep_of_disjoint dCS y hy, fun y hy => Pub.sep_of_disjoint dCS.symm y hy,
    fun i hi y hy => Pub.ne_of_disjoint dCD.symm (Nat.le_of_lt (s.gpr .a3).isLt) i hi y hy⟩

/-- Every register but `ra`. -/
def pcNotRa : List Reg :=
  [.t0, .t1, .t2, .s0, .s1, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10,
    .s11, .t3, .t4, .t5, .t6]

theorem pc_pres_saved : ∀ r ∈ preserved, ∃ i < 12, r = PublicChecked.saved i := by decide

theorem pc_correct (s : State) (h : pcContract.pre s) :
    ∃ tr t, Exec isa Precompute.code s tr t ∧ abiPreserved s t ∧ pcContract.post s t := by
  show WP isa Precompute.code s fun t => abiPreserved s t ∧ pcContract.post s t
  suffices main : WP isa Precompute.code s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ pcPost s t from
    WP.mono (WP.rdwr (WP.keep pcNotRa main (by rfl))) fun t ⟨⟨⟨hp, hpost⟩, kra⟩, _, _, hsp⟩ =>
      ⟨⟨hp, hsp, kra.gpr (by decide)⟩, hpost⟩
  have hp := pp_of h
  have hsl := hp.hsl
  have hk := hp.k64
  have hn := hp.nwS
  unfold Precompute.code
  refine WP.seq (WP.mono (pcFront_ok hp) fun t₁ f1 => ?_)
  refine WP.seq (WP.mono (recog_ok hp f1) fun t₂ ⟨f2, c2⟩ => ?_)
  refine WP.seq (WP.mono (post_ok hp f2) fun t₃ ⟨b3, a2, a3, a4, a5, m3, r3, w3⟩ => ?_)
  refine WP.seq (WP.mono (WP.rdwr (WP.keep [.a0, .s0, .t3, .t4, .t5] (loadP_X b3) (by rfl)))
    fun t₄ ⟨⟨⟨h4, ar4⟩, k4⟩, r4, w4, _⟩ => ?_)
  have hv : Spec.Rsa.modulusValid (pcx s).p (pcx s).k = true := Proof.Ffdh.domainValid_mod hp.dv
  have hz4 : t₄.gpr .s0 = 0 := h4.2.2.mpr hv
  have mp := mp_of hp h4 (by rw [w4, w3]) ((k4.gpr (by decide)).trans a2) ((k4.gpr (by decide)).trans a3)
    ((k4.gpr (by decide)).trans a4) ((k4.gpr (by decide)).trans (a5.trans c2))
  refine WP.seq (WP.mono (WP.rdwr (show WP isa (.ite (.zero .s0) main (.block [.li .a0 0])) t₄ (fun t =>
      Spec.Rsa.wordsAt t.mem (pcx s).O (3 + 34 * (pcx s).w) = VG.Proof.Ffdh.generationValues (pcx s).k (pcx s).db ∧
        t.gpr .a0 = 1 ∧ t.gpr .s6 = (pcx s).S ∧ ∀ y, ofs (pcx s).S y < 256 → t.mem y = t₄.mem y) from
    WP.ite (t₄.gpr .s0 == 0) (Steps.eval_zero _ _) (fun _ => by
        unfold main
        simp only [seqs]
        exact WP.seq (WP.mono (bound_step mp) fun u ⟨⟨mpu, u3⟩, um⟩ => WP.mono (rest_ok mpu u3)
          fun t ⟨tw, t0, t6, tf, _, _⟩ => ⟨tw, t0, t6, fun y hy => (tf y hy).trans (by rw [um])⟩))
      (fun hb => absurd hz4 (by simpa using hb)))) fun t₅ ⟨⟨tw5, t05, t65, tf5⟩, r5, w5, _⟩ => ?_)
  -- The saved registers' words.
  have hin : ∀ i < 12, InRegions t₅.wr (off (savW (s.gpr .a5)) (8 * i)) 8 := fun i hi => by
    rw [w5, w4, w3, hp.wr]
    show InRegions _ (s.gpr .a5 + BitVec.ofNat 64 128 + BitVec.ofNat 64 (8 * i)) 8
    rw [Offset.add_add]
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have hsav : ∀ i < 12, t₅.mem.readW (off (savW (s.gpr .a5)) (8 * i)) 64 = s.gpr (PublicChecked.saved i) :=
      fun i hi => by
    have e : off (savW (s.gpr .a5)) (8 * i) = off (s.gpr .a5) (128 + 8 * i) := by
      rw [off, off, Offset.add_add]
    rw [← f2.sav i hi, e]
    show word t₅.mem (s.gpr .a5) (128 + 8 * i) = word t₂.mem (s.gpr .a5) (128 + 8 * i)
    have o5 : Outside (s.gpr .a5) 256 (2 ^ 64) t₄.mem t₅.mem := fun y hy => tf5 y (hy.elim id fun h' => by
      have := (y - s.gpr .a5).isLt; simp only [ofs] at h'; omega_arith)
    have ar4' : Outside (s.gpr .a5) 256 ((s.gpr .a6).toNat * 8 - 256) t₃.mem t₄.mem := ar4
    rw [Outside.word o5 (Or.inl (by omega_arith)) (by omega_arith),
      Outside.word ar4' (Or.inl (by omega_arith)) (by omega_arith), m3]
  refine WP.mono (Pub.restore_ok t₅ (S := s.gpr .a5) (v := fun i => s.gpr (PublicChecked.saved i)) t65 hin
    (fun i hi => Pub.sav_al hp.alS (by omega_arith) hi) hsav) fun u ⟨urs, uot, um, _, _, _⟩ => ⟨fun r hr => ?_, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := pc_pres_saved r hr
    exact urs i hi
  refine ⟨by rw [uot .a0 (by decide), t05]; decide, ?_⟩
  rw [um, show (s.gpr .a1).toNat = 3 + 34 * (pcx s).w by rw [hp.hcl]; rfl]
  have hlk : (s.gpr .a4).toNat ≤ (pcDom s).length := by
    simp only [pcDom, VG.Proof.Bignum.bytesAt_length]; have := hp.hL; omega_arith
  have tw5' : Spec.Rsa.wordsAt t₅.mem (s.gpr .a0) (3 + 34 * (pcx s).w) =
      VG.Proof.Ffdh.generationValues (s.gpr .a4).toNat (pcDom s) := tw5
  rw [tw5', Proof.Ffdh.generationPrecompute_eq hlk hv]

end VG.Proof.Ffdh.RISCV64.Cached

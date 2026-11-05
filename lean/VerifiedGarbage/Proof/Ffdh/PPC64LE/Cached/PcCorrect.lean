module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.PcFn
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.PcBody
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.VettedValidation.Recognize
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckDomainFn
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.Save
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.PcRecog
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckDomainCT
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

/-! ## The public data and the stages

`pc_s1` … `pc_s5` run the code up to the registers' restoring, each from the
stage before; the constant-time proof uses them too. -/

/-- A run's public data: the context, the domain, the working space, `p_len`,
`domain_len`, the working space's size in bytes, the domain's bytes, the
table's address and the stack pointer. -/
structure PQ where
  C : Addr
  D : Addr
  S : Addr
  k : Nat
  L : Nat
  Z : Nat
  db : List Byte
  T : Addr
  sp : Addr

abbrev PQ.w (q : PQ) : Nat := (q.k + 7) / 8

/-- The recognized width. -/
abbrev PQ.cap (q : PQ) : Nat :=
  VG.Impl.Ffdh.VettedGroups.recognizeList VG.Impl.Ffdh.VettedGroups.groups q.k q.db

def pqOf (s : State) : PQ :=
  ⟨s.gpr .r3, s.gpr .r5, s.gpr .r8, (s.gpr .r7).toNat, (s.gpr .r6).toNat, (s.gpr .r9).toNat * 8,
    Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat, s.syms tableSym, s.sp⟩

/-- The domain's public data, as `vg_ffdh_check_domain`'s proof has it. -/
def PQ.cd (q : PQ) : CD := ⟨q.D, q.D, q.S, q.k, q.L, q.Z, q.db, q.db.take q.k⟩

/-- What the precondition gives. -/
structure Geo (q : PQ) (s : State) : Prop where
  r3 : s.gpr .r3 = q.C
  r4 : (s.gpr .r4).toNat = 3 + 34 * q.w
  r5 : s.gpr .r5 = q.D
  r6 : (s.gpr .r6).toNat = q.L
  r7 : (s.gpr .r7).toNat = q.k
  r8 : s.gpr .r8 = q.S
  wr : s.wr = [⟨q.C, (3 + 34 * q.w) * 8⟩, ⟨q.S, q.Z⟩]
  memD : (⟨q.D, q.L⟩ : Region) ∈ s.rd
  dCD : (⟨q.C, (3 + 34 * q.w) * 8⟩ : Region).Disjoint ⟨q.D, q.L⟩
  dCS : (⟨q.C, (3 + 34 * q.w) * 8⟩ : Region).Disjoint ⟨q.S, q.Z⟩
  dDS : (⟨q.D, q.L⟩ : Region).Disjoint ⟨q.S, q.Z⟩
  nwC : q.C.toNat + (3 + 34 * q.w) * 8 ≤ 2 ^ 64
  nwD : q.D.toNat + q.L ≤ 2 ^ 64
  nwS : q.S.toNat + q.Z ≤ 2 ^ 64
  hk : 64 ≤ q.k
  hk' : q.k ≤ 1024
  hL : q.L = 2 * q.k ∨ q.L = 3 * q.k
  hZw : slot q.w 28 ≤ q.Z
  dom : Spec.Rsa.bytesAt s.mem q.D q.L = q.db
  dv : Spec.Ffdh.domainValid q.k q.db = true
  tab : ∀ t : State, t.rd = s.rd → t.wr = s.wr → t.syms = s.syms → (∀ x, q.Z ≤ ofs q.S x → t.mem x = s.mem x) →
    VettedValidation.TableAt (t.syms tableSym) VG.Impl.Ffdh.VettedGroups.groups t
  syms : s.syms tableSym = q.T
  sp : s.sp = q.sp

theorem geo_of_pre {s : State} (h : pcContract.pre s) : Geo (pqOf s) s := by
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
  refine ⟨rfl, hcl', rfl, rfl, rfl, rfl, hwr, memD, dCD, dCS, dDS, nwC, nwD, nwS, hk, hk',
    by show (s.gpr .r6).toNat = 2 * (s.gpr .r7).toNat ∨ (s.gpr .r6).toNat = 3 * (s.gpr .r7).toNat
       simp only [Spec.Ffdh.domainLenValid] at hL; omega, ?_, rfl, hdv,
    fun t => table_after (t := t) hc (by rw [hwr]; simp [pqOf]), rfl, rfl⟩
  show slot (((s.gpr .r7).toNat + 7) / 8) 28 ≤ (s.gpr .r9).toNat * 8
  rw [Domain.slot_eq]; omega_using [hsl, hk', hk]

theorem slot0 (w : Nat) : slot w 0 = 256 := by rw [Domain.slot_eq]; omega

section Geo
variable {q : PQ} {s : State} (g : Geo q s)
include g

theorem Geo.hw4 : 4 ≤ q.w := by have := g.hk; simp only [PQ.w]; omega
theorem Geo.hw' : q.w ≤ 128 := by have := g.hk'; simp only [PQ.w]; omega
theorem Geo.hZ : 256 + 28 * (8 * (q.w + 2)) ≤ q.Z := by have := g.hZw; rw [Domain.slot_eq] at this; omega
theorem Geo.hs : Scr s q.S q.Z := Scr.of_mem (by rw [g.wr]; simp) g.nwS
theorem Geo.hinS : ∀ d, d + 8 ≤ 256 → InRegions s.wr (off q.S d) 8 := fun d hd => by
  have := g.hZ; have := g.nwS
  exact ⟨⟨q.S, q.Z⟩, by rw [g.wr]; simp, Offset.contains_base q.S (by omega) (by omega)⟩
theorem Geo.hin : ∀ i < 18, InRegions s.wr (off (savW q.S) (8 * i)) 8 := fun i hi => by
  have := g.hZ; have := g.nwS
  exact ⟨⟨q.S, q.Z⟩, by rw [g.wr]; simp, by
    rw [off, Offset.add_add]; exact Offset.contains_base q.S (by omega) (by omega)⟩
theorem Geo.sepD : ∀ i < q.L, ∀ x, ofs q.S x < q.Z → off q.D i ≠ x :=
  sep_of_disjoint (L := q.L) g.dDS (by have := g.nwD; omega)
theorem Geo.sepDC : ∀ i < q.L, ∀ x, ofs q.C x < (3 + 34 * q.w) * 8 → off q.D i ≠ x :=
  sep_of_disjoint (L := q.L) g.dCD.symm (by have := g.nwD; omega)
theorem Geo.rdD : ∀ i < q.L, InRegions (s.rd ++ s.wr) (off q.D i) 1 :=
  rd_of_mem (s := s) (D := q.D) (L := q.L) g.memD (by have := g.nwD; omega)
theorem Geo.sepCB : ∀ x, ofs q.C x < 8 * (3 + 34 * q.w) → q.Z ≤ ofs q.S x := fun x hx => by
  have := Pub.sep_of_disjoint g.dCS x (by simp only [VG.Proof.Bignum.ofs, ofs] at hx ⊢; omega)
  simp only [VG.Proof.Bignum.ofs, ofs] at this ⊢; omega
theorem Geo.sepBC : ∀ x, ofs q.S x < q.Z → 8 * (3 + 34 * q.w) ≤ ofs q.C x := fun x hx => by
  have := Pub.sep_of_disjoint g.dCS.symm x (by simp only [VG.Proof.Bignum.ofs, ofs] at hx ⊢; omega)
  simp only [VG.Proof.Bignum.ofs, ofs] at this ⊢; omega
theorem Geo.hlen : q.db.length = q.L := by rw [← g.dom]; exact VG.Proof.Bignum.bytesAt_length _ _ _
theorem Geo.hmod : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (q.db.take q.k)) q.k = true :=
  VG.Proof.Ffdh.domainValid_mod g.dv
theorem Geo.hgen : Spec.Ffdh.generationPrecompute q.k q.db = some (VG.Proof.Ffdh.generationValues q.k q.db) :=
  VG.Proof.Ffdh.generationPrecompute_eq (by rw [g.hlen]; rcases g.hL with h | h <;> omega) g.hmod

end Geo

/-- After `front`. -/
structure St1 (q : PQ) (s₀ s : State) : Prop where
  r23 : s.gpr .r23 = q.S
  r3 : s.gpr .r3 = q.D
  r4 : s.gpr .r4 = BitVec.ofNat 64 q.L
  r5 : s.gpr .r5 = BitVec.ofNat 64 q.k
  w0 : word s.mem q.S 0 = q.C
  sav : ∀ i < 18, word s.mem q.S (112 + 8 * i) = s₀.gpr (Impl.Ffdh.PPC64LE.Domain.saved i)
  fr : ∀ x, q.Z ≤ ofs q.S x → s.mem x = s₀.mem x
  keep : Bignum.PPC64LE.Keep [.r23, .r3, .r4, .r5] s₀ s
  syms : s.syms = s₀.syms

theorem pc_s1 {q : PQ} {s : State} (g : Geo q s) : WP isa (.block front) s (St1 q s) :=
  WP.mono_syms (pc_front (Z := q.Z) g.r8 (Nat.le_trans (Nat.le_add_right _ _) g.hZ) g.hin (g.hinS 0 (by decide)))
    fun _ ⟨a23, a3, a4, a5, w0, wsav, fr1, k1⟩ sym1 =>
      ⟨a23, a3.trans g.r5, by rw [a4, ← g.r6, BitVec.ofNat_toNat, BitVec.setWidth_eq],
        by rw [a5, ← g.r7, BitVec.ofNat_toNat, BitVec.setWidth_eq], w0.trans g.r3, wsav, fr1, k1, sym1⟩

/-- What `recognize` reads, after `front`. -/
theorem St1.ri {q : PQ} {s₀ s : State} (g : Geo q s₀) (h : St1 q s₀ s) :
    VettedValidation.RI q.D q.k q.db q.T q.sp s := by
  refine ⟨⟨h.r3, by rw [h.r4, g.hlen], h.r5, ?_, ?_, by rw [g.hlen]; exact g.hL, g.hk, g.hk'⟩,
    by rw [h.syms, g.syms], by rw [← g.syms, ← h.syms]; exact g.tab s h.keep.rd h.keep.wr h.syms h.fr,
    h.keep.sp.trans g.sp⟩
  · rw [g.hlen, h.keep.rd, h.keep.wr]
    exact ⟨_, List.mem_append_left _ g.memD, Region.contains_self _ _⟩
  · rw [g.hlen, bytes_out h.fr g.sepD, g.dom]

/-- After `recognize`. -/
def St2 (q : PQ) (s₀ s : State) : Prop :=
  ∃ s₁, St1 q s₀ s₁ ∧ s.gpr .r8 = BitVec.ofNat 64 q.cap ∧ s.mem = s₁.mem ∧
    Bignum.PPC64LE.Keep VettedValidation.allClobbers s₁ s

theorem pc_s2 {q : PQ} {s₀ s : State} (g : Geo q s₀) (h : St1 q s₀ s) :
    WP isa VG.Impl.Ffdh.PPC64LE.VettedValidation.recognize s (St2 q s₀) :=
  WP.mono (wp_sp (VettedValidation.recognize_ok' (h.ri g).1 (by rw [(h.ri g).2.1]; exact (h.ri g).2.2.1)))
    fun _ ⟨⟨r8v, m2, k2, lr2⟩, sp2⟩ => ⟨s, h, r8v, m2, ⟨k2.1, k2.2.1, k2.2.2, sp2, lr2⟩⟩

/-- The registers the stages write. -/
abbrev rs3 : List Reg := [.r23, .r3, .r4, .r5] ++ VettedValidation.allClobbers ++ (([] : List Reg) ++ setup0Regs)
abbrev rs4 : List Reg := rs3 ++ ([.r0, .r6, .r12, .r14, .r15, .r16, .r17, .r18] : List Reg)
abbrev rs5 : List Reg := rs4 ++ mainRegs

/-- What the stages keep in the header and apart from the working space. -/
structure Sx (rs : List Reg) (q : PQ) (s₀ s : State) : Prop where
  w0 : word s.mem q.S 0 = q.C
  wcap : word s.mem q.S 96 = BitVec.ofNat 64 q.cap
  sav : ∀ i < 18, word s.mem q.S (112 + 8 * i) = s₀.gpr (Impl.Ffdh.PPC64LE.Domain.saved i)
  fr : ∀ x, q.Z ≤ ofs q.S x → s.mem x = s₀.mem x
  keep : Bignum.PPC64LE.Keep rs s₀ s

/-- After the width's store and `setup`. -/
def St3 (q : PQ) (s₀ s : State) : Prop := Base q.cd s ∧ Sx rs3 q s₀ s

theorem pc_s3 {q : PQ} {s₀ s : State} (g : Geo q s₀) (h : St2 q s₀ s) :
    WP isa (.block ([sth .r8 hCap] ++ VG.Impl.Ffdh.PPC64LE.Domain.setup)) s (St3 q s₀) := by
  obtain ⟨s₁, h1, r8v, m2, k2⟩ := h
  have hZ := g.hZ
  have hnw := g.nwS
  have k12 := h1.keep.trans k2
  have g23 : s.gpr .r23 = q.S := (k2.gpr .r23 (by decide)).trans h1.r23
  refine WP.block_append (WP.mono (pcCap_ok g23 (by rw [k12.wr]; exact g.hinS 96 (by decide)))
    fun s₂' ⟨m2', kc⟩ => ?_)
  refine WP.mono (setup0_ok (D := q.D) (L := q.L) (k := q.k)
    ((kc.gpr .r3 (by decide)).trans ((k2.gpr .r3 (by decide)).trans h1.r3))
    (by rw [kc.gpr .r4 (by decide), k2.gpr .r4 (by decide), h1.r4])
    (by rw [kc.gpr .r5 (by decide), k2.gpr .r5 (by decide), h1.r5])
    ((kc.gpr .r23 (by decide)).trans g23) g.hk') fun s₃ ⟨⟨a21, a27, a28, a11, a29, a10, a31, m3⟩, k3⟩ => ?_
  have k13 := (k12.trans kc).trans k3
  have oc := writeW_outside s.mem q.S (d := 96) (s.gpr .r8) (by omega)
  rw [← m2'] at oc
  have fr3 : ∀ x, q.Z ≤ ofs q.S x → s₃.mem x = s₀.mem x := fun x hx => by
    rw [m3, oc x (.inr (by omega)), m2]; exact h1.fr x hx
  have w3 : ∀ d, d + 8 ≤ 96 ∨ 104 ≤ d → d + 8 ≤ 256 → word s₃.mem q.S d = word s₁.mem q.S d := fun d hd hd' => by
    rw [m3, oc.word (by omega) (by omega), m2]
  have hk := g.hk
  have hL := g.hL
  refine ⟨⟨⟨g.hs.congr k13.wr, a10, a29, a11, a31, g.hw4, g.hw', g.hZw⟩, a21,
    (k3.gpr .r23 (by decide)).trans ((kc.gpr .r23 (by decide)).trans g23), a27, a28, g.hk, g.hk', g.hL,
    fun i hi => by rw [k13.rd, k13.wr]; exact g.rdD i hi, g.sepD,
    fun i hi => by rw [k13.rd, k13.wr]; exact g.rdD i (by show i < q.L; change i < q.k at hi; omega),
    fun i hi => g.sepD i (by change i < q.k at hi; omega), ?_, ?_⟩,
    ⟨by rw [w3 0 (by omega) (by omega)]; exact h1.w0, ?_, fun i hi => by rw [w3 _ (by omega) (by omega)]; exact h1.sav i hi,
      fr3, k13⟩⟩
  · show Spec.Rsa.bytesAt s₃.mem q.D q.L = q.db
    rw [bytes_out fr3 g.sepD, g.dom]
  · show Spec.Rsa.bytesAt s₃.mem q.D q.k = q.db.take q.k
    rw [bytes_out fr3 (fun i hi => g.sepD i (by omega)), ← g.dom,
      VG.Proof.Ffdh.take_bytesAt s₀.mem q.D (by omega : q.k ≤ q.L)]
  · rw [m3, m2', word_writeW_self, r8v]

/-- After p's check. -/
def St4 (q : PQ) (s₀ s : State) : Prop := E4 q.cd s ∧ Sx rs4 q s₀ s

theorem pc_s4 {q : PQ} {s₀ s : State} (g : Geo q s₀) (h : St3 q s₀ s) : WP isa loadP s (St4 q s₀) := by
  obtain ⟨hb, hX⟩ := h
  have hZ := g.hZ
  have e0 := slot0 q.w
  refine WP.mono (loadP_ok hb.env hb.r21 hb.r28 rfl g.hk g.hk' (fun i hi => hb.rdY i hi) (fun i hi => hb.sepY i hi))
    fun s₄ ⟨⟨p4, c4, b4⟩, k4⟩ => ?_
  have hy : Spec.Rsa.bytesAt s.mem q.cd.D q.cd.k = q.db.take q.k := hb.bY
  rw [hy] at p4 c4
  refine ⟨⟨hb.keep k4 b4, p4, c4⟩, ⟨?_, ?_, fun i hi => ?_, fun x hx => ?_, hX.keep.trans k4⟩⟩
  all_goals change Body q.S q.w s.mem s₄.mem at b4
  · rw [Outside.word b4 (by omega) (by omega)]; exact hX.w0
  · rw [Outside.word b4 (by omega) (by omega)]; exact hX.wcap
  · rw [Outside.word b4 (by omega) (by omega)]; exact hX.sav i hi
  · rw [b4 x (.inr (by rw [e0]; omega))]; exact hX.fr x hx

/-- `main`'s precondition, after p's check. -/
theorem St4.mp {q : PQ} {s₀ s : State} (g : Geo q s₀) (h : St4 q s₀ s) : MP q.S q.D q.C q.Z q.k q.L s := by
  obtain ⟨⟨hb, p4, -⟩, hx⟩ := h
  have hb' : Spec.Rsa.bytesAt s.mem q.D q.L = q.db := hb.bD
  have nwC := g.nwC
  have hw : q.w = (q.k + 7) / 8 := rfl
  refine ⟨hb.env, hb.r23, hb.r21, hb.r27, hb.r28, g.hk, g.hk', g.hL, hb.rdD, g.sepD,
    fun i hi x hx => g.sepDC i hi x (by rw [ctxWords] at hx; omega), ?_,
    fun x hx => g.sepCB x (by rw [ctxWords] at hx; omega),
    fun x hx => by have := g.sepBC x hx; rw [ctxWords]; omega, hx.w0, by rw [hb']; exact hx.wcap, ?_,
    by rw [hb']; exact g.dv⟩
  · exact Scr.of_mem (by rw [hx.keep.wr, g.wr]; simp [ctxWords]; omega) (by rw [ctxWords]; omega)
  · rw [hb']; exact p4

/-- After the branch. -/
structure St5 (q : PQ) (s₀ s : State) : Prop where
  r3 : s.gpr .r3 = BitVec.ofNat 64 1
  words : Spec.Rsa.wordsAt s.mem q.C (3 + 34 * q.w) = VG.Proof.Ffdh.generationValues q.k q.db
  sav : ∀ i < 18, word s.mem q.S (112 + 8 * i) = s₀.gpr (Impl.Ffdh.PPC64LE.Domain.saved i)
  keep : Bignum.PPC64LE.Keep rs5 s₀ s
  r23 : s.gpr .r23 = q.S

/-- `main`, with p valid. -/
theorem pc_main {q : PQ} {s₀ s : State} (g : Geo q s₀) (h : St4 q s₀ s) : WP isa main s (St5 q s₀) := by
  have mp := h.mp g
  have hZ := g.hZ
  have hb' : Spec.Rsa.bytesAt s.mem q.D q.L = q.db := h.1.1.bD
  refine WP.mono (main_ok mp) fun t ⟨⟨t3, tw, tm⟩, kt⟩ => ⟨t3, by rw [tw, hb'], fun i hi => ?_,
    h.2.keep.trans kt, (kt.gpr .r23 (by decide)).trans h.1.1.r23⟩
  have hm : Outside q.S (slot q.w 1) (2 ^ 64) s.mem t.mem := fun x hx => by
    rcases hx with hx | hx
    · exact tm x hx
    · exact absurd hx (by have := (x - q.S).isLt; simp only [ofs]; omega)
  rw [Outside.word hm (by rw [Domain.slot_eq]; omega) (by omega)]
  exact h.2.sav i hi

theorem pc_s5 {q : PQ} {s₀ s : State} (g : Geo q s₀) (h : St4 q s₀ s) :
    WP isa (.ite (.zero .d .r0) main (.block [.li .r3 0])) s (St5 q s₀) :=
  WP.ite (s.gpr .r0 == 0) (eval_zero _ _) (fun _ => pc_main g h)
    (fun hz => absurd (h.1.2.2.mpr g.hmod) (by simpa using hz))

theorem pc_correct (s : State) (h : pcContract.pre s) :
    ∃ tr t, Exec isa Precompute.code s tr t ∧ abiPreserved s t ∧ pcContract.post s t := by
  show WP isa Precompute.code s fun t => abiPreserved s t ∧ pcPost s t
  have g := geo_of_pre h
  unfold Precompute.code
  refine WP.seq (WP.mono (pc_s1 g) fun s₁ h1 => ?_)
  refine WP.seq (WP.mono (pc_s2 g h1) fun s₂ h2 => ?_)
  refine WP.seq (WP.mono (pc_s3 g h2) fun s₃ h3 => ?_)
  refine WP.seq (WP.mono (pc_s4 g h3) fun s₄ h4 => ?_)
  refine WP.seq (WP.mono (pc_s5 g h4) fun t₅ h5 => ?_)
  have hsav' : ∀ i < 18, t₅.mem.readW (off (savW (pqOf s).S) (8 * i)) 64 =
      s.gpr (Impl.Ffdh.PPC64LE.Domain.saved i) := fun i hi => by
    have ea : off (savW (pqOf s).S) (8 * i) = off (pqOf s).S (112 + 8 * i) := by rw [off, off, Offset.add_add]
    rw [ea]
    exact h5.sav i hi
  refine WP.mono (restore_ok t₅ h5.r23 (by rw [h5.keep.wr]; exact g.hin) hsav')
    fun u ⟨urs, uot, um, _, _, usp, ulr⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [usp, h5.keep.sp], by rw [ulr, h5.keep.lr]⟩, ?_, ?_⟩
  · by_cases hs' : ∃ i < 18, r = Impl.Ffdh.PPC64LE.Domain.saved i
    · obtain ⟨i, hi, rfl⟩ := hs'
      exact urs i hi
    · have hn : ∀ i < 18, r ≠ Impl.Ffdh.PPC64LE.Domain.saved i := fun i hi e => hs' ⟨i, hi, e⟩
      rw [uot r hn, h5.keep.gpr r (pc_pres_not_written r hr hn)]
  · rw [uot .r3 (by decide), h5.r3]; rfl
  · show Spec.Ffdh.generationPrecompute (pqOf s).k (pqOf s).db =
      some (Spec.Rsa.wordsAt u.mem (pqOf s).C (s.gpr .r4).toNat)
    rw [g.r4, um, h5.words]
    exact g.hgen

end VG.Proof.Ffdh.PPC64LE.Cached

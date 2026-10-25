module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Stage
import VerifiedGarbage.Proof.Bignum.AArch64.Store
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Framework.Offset

/-!
# FFDH on AArch64: a number stored masked by its range

With a number z in `aY` of the inner workspace for p, `range aY` and then
the stores of `outMask` write z to the output at the outer slot `sOut`
(`D.k` octets) if `1 < z < p − 1`, zeros otherwise, without a branch, and
leave the flag in the inner `sF` (`outMask_ok`). `vg_ffdh_exchange` stores
the shared value so, and `vg_ffdh_derive_public` the public value.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Ffdh.AArch64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowFive VG.Proof.Bignum.CrtWindowFive
open VG.Proof.MlKem.AArch64 (Keep eval_zero)

theorem _root_.VG.Proof.Ffdh.AArch64.In.hlG {D : FD} {mi : BitVec 64} {t : State} (h : In D mi t) :
    ∀ i < 32, InRegions (t.rd ++ t.wr) (off (off D.B (inner D.w)) (8 * i)) 8 :=
  fun _ hi => h.2.1.good.ld (Nat.le_refl _) hi

theorem _root_.VG.Proof.Ffdh.AArch64.In.hlB {D : FD} {mi : BitVec 64} {t : State} (h : In D mi t) :
    ∀ i < 32, InRegions (t.rd ++ t.wr) (off D.B (8 * i)) 8 :=
  fun _ hi => h.1.scr.ld (by have := h.1.hZ; omega_arith)

theorem bit_mask (P : Prop) [Decidable P] : (0 : BitVec 64) - bit P = mask (decide P) := by
  by_cases h : P <;> simp [bit, h, mask]

/-- Octets from their values. -/
theorem bytesAt_of {m : Mem} {ptr : Addr} {n : Nat} {l : List Byte} (hl : l.length = n)
    (h : ∀ i < n, m (ptr + BitVec.ofNat 64 i) = l.getD i 0) : Spec.Rsa.bytesAt m ptr n = l := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt, hl])
  intro i h1 h2
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
  rw [h i (by simpa [Spec.Rsa.bytesAt] using h1), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2,
    Option.getD_some]

/-- The results' status. -/
theorem fin_status (F : Prop) [Decidable F] :
    ((BitVec.ofNat 64 3 - (bit F <<< 1)) = BitVec.ofNat 64 (if F then 1 else 3)) := by
  by_cases h : F <;> simp [bit, h] <;> decide

/-- The status from the flag. -/
theorem fBlk_ok {t : State} {B : Addr} {f : BitVec 64} (h0 : t.gpr .x0 = B) (hF : word t.mem B (8 * sF) = f)
    (hl : InRegions (t.rd ++ t.wr) (off B (8 * sF)) 8) :
    WP isa (.block [ldh .x9 sF, movi .x0 3, .lsl .x .x9 .x9 1, .sub .x .x0 .x0 .x9]) t fun u =>
      (u.gpr .x0 = BitVec.ofNat 64 3 - (f <<< 1) ∧ u.mem = t.mem) ∧ Keep [.x0, .x9] t u :=
  WP.keep _ (by brun [h0, hdr_enc (show sF < 32 by decide), hl, hF]; rfl) (by decide) (by decide)
    (by decide +kernel)

/-- `zeroOut`'s first block. -/
theorem zoBlk_ok {t : State} {B ptr : Addr} {k sPtr : Nat} (h0 : t.gpr .x0 = B) (hP : sPtr < 32)
    (hO : word t.mem B (8 * sPtr) = ptr) (hK : word t.mem B (8 * sK) = BitVec.ofNat 64 k)
    (hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8) :
    WP isa (.block [ldh .x1 sPtr, ldh .x2 sK, movi .x3 0]) t fun u => u.gpr .x1 = ptr ∧ u.gpr .x2 = BitVec.ofNat 64 k :=
  WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun u => u.gpr .x1 = ptr ∧ u.gpr .x2 = BitVec.ofNat 64 k)
    (by brun [h0, hdr_enc hP, hdr_enc (show sK < 32 by decide), hl sPtr hP, hl sK (by decide), hO, hK])
    rfl rfl rfl) fun _ h => h.1

namespace OutMask

/-- The final block's first loads. -/
abbrev finBlk1 : List Instr := [ldh .x12 sW, ldh .x8 (sArr aY), ldh .x5 Crt.sLink]

/-- The final block's later part. -/
abbrev finBlk2 : List Instr :=
  [Crt.ldw .x1 .x5 VG.Impl.Ffdh.AArch64.Domain.sOut, Crt.ldw .x9 .x5 sK, .add .x .x1 .x1 .x9, movi .x7 0, ldh .x3 sF,
    .sub .x .x15 .x7 .x3]

/-- The final block: `storeBE`'s operands. -/
abbrev finBlk : List Instr := finBlk1 ++ finBlk2

/-- `range aY`, then z stored masked by its flag. -/
abbrev outMask : List (Prog isa) := range aY ++ [.block finBlk, storeBE]

/-- The final block's loads, in the inner workspace `G` of the outer one `B`. -/
theorem finBlk_ok {t : State} {G B : Addr} {w k : Nat} {a op f : BitVec 64} (h0 : t.gpr .x0 = G)
    (hW : word t.mem G (8 * sW) = BitVec.ofNat 64 w) (hA : word t.mem G (8 * sArr aY) = a)
    (hL : word t.mem G (8 * Crt.sLink) = B) (hO : word t.mem B (8 * VG.Impl.Ffdh.AArch64.Domain.sOut) = op)
    (hK : word t.mem B (8 * sK) = BitVec.ofNat 64 k) (hF : word t.mem G (8 * sF) = f)
    (hlG : ∀ i < 32, InRegions (t.rd ++ t.wr) (off G (8 * i)) 8)
    (hlB : ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8) :
    WP isa (.block finBlk) t fun u =>
      (u.gpr .x8 = a ∧ u.gpr .x1 = op + BitVec.ofNat 64 k ∧ u.gpr .x9 = BitVec.ofNat 64 k ∧ u.gpr .x15 = 0 - f ∧
        u.gpr .x5 = B ∧ u.mem = t.mem) ∧ Keep [.x1, .x3, .x5, .x7, .x8, .x9, .x12, .x15] t u := by
  refine WP.keep _ ?_ (by decide) (by decide) (by decide +kernel)
  brun [Crt.ldw, h0, hdr_enc (show sW < 32 by decide), hdr_enc (sArr_lt (show aY < 8 by decide)),
    hdr_enc (show Crt.sLink < 32 by decide), hdr_enc (show VG.Impl.Ffdh.AArch64.Domain.sOut < 32 by decide),
    hdr_enc (show sK < 32 by decide), hdr_enc (show sF < 32 by decide), hlG sW (by decide),
    hlG (sArr aY) (sArr_lt (show aY < 8 by decide)), hlG Crt.sLink (by decide), hlG sF (by decide),
    hlB VG.Impl.Ffdh.AArch64.Domain.sOut (by decide), hlB sK (by decide), hW, hA, hL, hO, hK, hF]
  rfl

/-- The final block's first loads: the bases. -/
theorem finBlk1_ok {t : State} {G B : Addr} {a : BitVec 64} (h0 : t.gpr .x0 = G)
    (hA : word t.mem G (8 * sArr aY) = a) (hL : word t.mem G (8 * Crt.sLink) = B)
    (hlG : ∀ i < 32, InRegions (t.rd ++ t.wr) (off G (8 * i)) 8) :
    WP isa (.block finBlk1) t fun u => u.gpr .x0 = G ∧ u.gpr .x8 = a ∧ u.gpr .x5 = B :=
  WP.mono (WP.keep [.x5, .x8, .x12] (Q := fun u => u.gpr .x8 = a ∧ u.gpr .x5 = B)
    (by brun [h0, hdr_enc (show sW < 32 by decide), hdr_enc (sArr_lt (show aY < 8 by decide)),
      hdr_enc (show Crt.sLink < 32 by decide), hlG sW (by decide), hlG (sArr aY) (sArr_lt (show aY < 8 by decide)),
      hlG Crt.sLink (by decide), hA, hL]) (by decide) (by decide) (by decide +kernel))
    fun u ⟨⟨h8, h5⟩, k⟩ => ⟨(k.gpr .x0 (by decide)).trans h0, h8, h5⟩

/-- The inner workspace's base. -/
abbrev FD.G (D : FD) : Addr := off D.B (inner D.w)

/-- The output: `D.k` octets at `op`, writable and outside the working space. -/
def Dst (D : FD) (op : Addr) (t : State) : Prop :=
  ∀ j < D.k, InRegions t.wr (op + BitVec.ofNat 64 j) 1 ∧ D.Z ≤ ofs D.B (op + BitVec.ofNat 64 j)

theorem Dst.keep {D : FD} {op : Addr} {t u : State} (h : Dst D op t) {rs : List Reg} (k : Keep rs t u) :
    Dst D op u :=
  fun j hj => ⟨by rw [k.wr]; exact (h j hj).1, (h j hj).2⟩

/-- z's flag: `1 < z < p − 1`, as the code compares. -/
abbrev fl (D : FD) (z : Nat) : Prop := 1 < z ∧ 2 * (z / 2) + 1 < D.P

/-- With z in `aY`, and the output's pointer in `sOut`. -/
def O3 (D : FD) (op : Addr) (z : Nat) (t : State) : Prop :=
  (∃ mi, In D mi t ∧ wv t.mem (FD.G D) (slot D.w aY) D.w = z) ∧
    (VG.Impl.Ffdh.AArch64.Domain.sOut, op) ∈ D.hs ∧ Dst D op t

/-- After z's range: its flag in `x9` and `sF`. -/
def O4 (D : FD) (op : Addr) (z : Nat) (t : State) : Prop :=
  (∃ mi, In D mi t ∧ t.gpr .x9 = bit (fl D z) ∧ word t.mem (FD.G D) (8 * sF) = bit (fl D z) ∧
    wv t.mem (FD.G D) (slot D.w aY) D.w = z) ∧ (VG.Impl.Ffdh.AArch64.Domain.sOut, op) ∈ D.hs ∧ Dst D op t

theorem o3_o4 {D : FD} {op : Addr} {z : Nat} {t : State} (h : O3 D op z t) :
    WP isa (seqs (range aY)) t fun u => O4 D op z u ∧ KX t u := by
  obtain ⟨⟨mi, hI, hY⟩, ho, hd⟩ := h
  have hG := hI.2.1.good.scr.nowrap
  refine WP.mono (hI.range (show aY < 8 by decide) (by decide)) fun u ⟨⟨hu, h9, hF, f⟩, k⟩ =>
    ⟨⟨⟨mi, hu, by rw [h9, hY], by rw [hF, h9, hY], ?_⟩, ho, hd.keep k⟩, k⟩
  have sY := slot_le (w := D.w) (show aY < 8 by decide)
  have hY0 := hdr_lt_slot D.w aY (show sF < 32 by decide)
  have sT := slot_sep (w := D.w) (show aTmp ≠ aY by decide)
  rw [f.wv_eq (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_arith)]
  exact hY

/-- `storeBE`'s operands. -/
def O5 (D : FD) (op : Addr) (z : Nat) (t : State) : Prop :=
  (∃ mi, In D mi t ∧ word t.mem (FD.G D) (8 * sF) = bit (fl D z) ∧
    wv t.mem (FD.G D) (slot D.w aY) D.w = z) ∧
  t.gpr .x8 = off (FD.G D) (slot D.w aY) ∧ t.gpr .x1 = op + BitVec.ofNat 64 D.k ∧
  t.gpr .x9 = BitVec.ofNat 64 D.k ∧ t.gpr .x15 = mask (decide (fl D z)) ∧ Dst D op t

theorem o4_o5 {D : FD} {op : Addr} {z : Nat} {t : State} (h : O4 D op z t) :
    WP isa (.block finBlk) t fun u => O5 D op z u ∧ KX t u := by
  obtain ⟨⟨mi, hI, -, hF, hY⟩, ho, hd⟩ := h
  have hc := hI.2.1
  have hs := hI.2.2.2.2.1
  refine WP.mono (finBlk_ok hc.x0 hc.hdr.hw (hc.hdr.harr aY (by decide)) hc.link
    (hs.get (i := VG.Impl.Ffdh.AArch64.Domain.sOut) (v := op) (List.mem_append_left _ (List.mem_append_right _ ho)))
    (hs.get (i := sK) (v := BitVec.ofNat 64 D.k) (by simp)) hF hI.hlG hI.hlB)
    fun u ⟨⟨h8, h1, h9, h15, _, hm⟩, k⟩ => ⟨⟨⟨mi, hI.keep hm k (by decide), by rw [hm]; exact hF,
      by rw [hm]; exact hY⟩, h8, h1, h9, by rw [h15, bit_mask], hd.keep k⟩, k.mono (by decide)⟩

/-- The final block's first loads, and what its later part gives. -/
theorem o4_fin1 {D : FD} {op : Addr} {z : Nat} {t : State} (h : O4 D op z t) :
    WP isa (.block finBlk1) t fun u =>
      (u.gpr .x0 = FD.G D ∧ u.gpr .x8 = off (FD.G D) (slot D.w aY) ∧ u.gpr .x5 = D.B) ∧
        WP isa (.block finBlk2) u (O5 D op z) := by
  have hI := h.1.choose_spec.1
  have hc := hI.2.1
  have hw : WP isa (.block (finBlk1 ++ finBlk2)) t (O5 D op z) := WP.mono (o4_o5 h) fun _ h => h.1
  rw [WP.block_append_iff] at hw
  exact WP.mono (wp_and (finBlk1_ok hc.x0 (hc.hdr.harr aY (by decide)) hc.link hI.hlG) hw)
    fun _ ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩

/-- After `storeBE`. -/
def O6 (D : FD) (op : Addr) (z : Nat) (t : State) : Prop :=
  Spec.Rsa.bytesAt t.mem op D.k = Spec.Rsa.i2osp (if fl D z then z else 0) D.k ∧
    t.gpr .x0 = FD.G D ∧ word t.mem (FD.G D) (8 * sF) = bit (fl D z) ∧
    InRegions (t.rd ++ t.wr) (off (FD.G D) (8 * sF)) 8

theorem o5_o6 {D : FD} {op : Addr} {z : Nat} {t : State} (h : O5 D op z t) :
    WP isa storeBE t fun u => O6 D op z u ∧ KX t u := by
  obtain ⟨⟨mi, hI, hF, hY⟩, h8, h1, h9, h15, hd⟩ := h
  have hb := hI.1
  have hc := hI.2.1
  have hn := hb.scr.nowrap
  have hroom := hb.room
  have hk1 : 64 ≤ D.k := hb.k1
  have hk2 : D.k ≤ 1024 := hb.k2
  have ew' : 8 * D.w ≤ D.k + 7 ∧ D.k ≤ 8 * D.w := hb.ew
  have hsY := slot_le (w := D.w) (show aY < 8 by decide)
  have hiZ : inner D.w + slot D.w 8 ≤ D.Z := by unfold tabBytes32 at hroom; omega_arith
  have h8' : t.gpr .x8 = off D.B (inner D.w + slot D.w aY) := by rw [h8, off_off]
  refine WP.mono (storeBE_ok (c := decide (fl D z)) (w := D.w) hb.scr h8' h1 h9 h15 (by omega_arith) (by omega_arith)
    rfl (by omega_arith) (fun j hj => (hd j hj).1) (fun j hj => (hd j hj).2)) fun u ⟨hb', hfr, hwr, hrd, k⟩ => ?_
  have hF8 := hdr_lt_slot D.w 8 (show sF < 32 by decide)
  refine ⟨⟨?_, (k.gpr .x0 (by decide)).trans hc.x0, ?_, ?_⟩, k.mono (by decide)⟩
  · show (List.range D.k).map (fun i => u.mem (op + BitVec.ofNat 64 i)) = _
    rw [hb', ← wv_off, hY]
    simp only [decide_eq_true_eq]
  · rw [← hF]
    refine Mem.readW_congr fun i hi => (hfr _ fun j hj he => ?_)
    have h1 := (hd j hj).2
    have h2 : ofs D.B (off (FD.G D) (8 * sF) + BitVec.ofNat 64 i) = inner D.w + 8 * sF + i := by
      rw [off_off, ofs_off _ (by omega_arith)]
    rw [he] at h2
    omega_arith
  · rw [hwr, hrd]; exact hI.hlG sF (by decide)

/-- `outMask`: z stored masked by its flag, which is left in `sF`. -/
theorem outMask_ok {D : FD} {op : Addr} {z : Nat} {t : State} (h : O3 D op z t) :
    WP isa (seqs outMask) t fun u => O6 D op z u ∧ KX t u := by
  refine wp_seqs_append (by simp [range]) (by simp) (WP.mono (o3_o4 h) fun t₁ ⟨h₁, k₁⟩ => ?_)
  refine wp_seqs_cons (by simp) (WP.mono (o4_o5 h₁) fun t₂ ⟨h₂, k₂⟩ => ?_)
  rw [seqs_one]
  exact WP.mono (o5_o6 h₂) fun u ⟨hu, k⟩ => ⟨hu, keep_trans k₁ (keep_trans k₂ k)⟩

end OutMask

end VG.Proof.Ffdh.AArch64

module

public import VerifiedGarbage.Proof.Cast5.X86.Block
public import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86.RegUpd

/-!
# CAST5 on 32-bit x86: ECB

`ecb up` takes the working space from the stack, saves the callee-saved
registers in it, keeps its arguments in their slots, runs `crypt` on each
block in turn (`ecbLoop_ok`) and restores the registers (`ecb_correct`).
-/

@[expose] public section

namespace VG.Proof.Cast5.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Cast5.X86
open VG.Impl.Cast5 (s1234Sym s1234)
open VG.Proof.Cast5 (tableEnt Held)

/-! ## Frames of the layouts -/

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {Q : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨Q, 8⟩ r) : Spec.Cast5.blockAt m' Q = Spec.Cast5.blockAt m Q := by
  apply Vector.ext
  intro j hj
  rw [Proof.Cast5.blockAt_get _ _ hj, Proof.Cast5.blockAt_get _ _ hj]
  exact hf.bytes (R := ⟨Q, 8⟩) hd (by show (8 : Nat) ≤ 2 ^ 64; decide) hj

theorem scheduleAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {K : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨K, 128⟩ r) : Spec.Cast5.scheduleAt m' K = Spec.Cast5.scheduleAt m K := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Cast5.scheduleAt, Vector.getElem_ofFn]
  rw [hf.bytes (R := ⟨K, 128⟩) hd (by show (128 : Nat) ≤ 2 ^ 64; decide) (show 4 * i + 3 < 128 by omega_arith),
    hf.bytes (R := ⟨K, 128⟩) hd (by show (128 : Nat) ≤ 2 ^ 64; decide) (show 4 * i + 2 < 128 by omega_arith),
    hf.bytes (R := ⟨K, 128⟩) hd (by show (128 : Nat) ≤ 2 ^ 64; decide) (show 4 * i + 1 < 128 by omega_arith),
    hf.bytes (R := ⟨K, 128⟩) hd (by show (128 : Nat) ≤ 2 ^ 64; decide) (show 4 * i < 128 by omega_arith)]

/-- The table's words, as the scans read them. -/
theorem tabAt_of_held {m : Mem} {T : BitVec 32} (h : Held m (T.setWidth 64) s1234) : TabAt m T tab1234 :=
  fun _ hj _ hk => Proof.Cast5.ent_table h hj hk

theorem s1234_length : s1234.length = 512 := Proof.Cast5.table_length _ _ _ _

theorem held_frame {rs : List Region} {m m' : Mem} {T : Addr} (h : Held m T s1234) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨T, 4096⟩ r) : Held m' T s1234 := by
  intro i hi
  rw [s1234_length] at hi
  rw [← h i (by rw [s1234_length]; exact hi)]
  exact hf.readW (r := ⟨T, 4096⟩) (Offset.contains_base _ (by omega_arith) (by omega_arith)) hd (by decide)

/-! ## The layout -/

/-- The regions the loop writes: the data, the scan's result, the slots of
the data, the count, the subkeys' pointer and the count of groups, and the
word below `esp`. -/
def loopMem (S D : BitVec 32) (N : Nat) (sp : BitVec 32) : List Region :=
  [⟨D.setWidth 64, 8 * N⟩, slotR S 0 16, slotR S dataOff 16, below sp 4]

/-- What the loop needs of the layout, from the state `s` on entry and the
memory `m0` after the setup: the schedule `k` at `K`, the `N` blocks at `D`,
the working space at `S`, the table and the word below `esp`, separate and
within the address space; the slots of the subkeys and the rounds. -/
structure Lay (s : State) (m0 : Mem) (S D K : BitVec 32) (k : Spec.Cast5.Schedule) (n N : Nat) : Prop where
  fitS : S.toNat + 256 ≤ 2 ^ 32
  fitD : D.toNat + 8 * N ≤ 2 ^ 32
  fitK : K.toNat + 128 ≤ 2 ^ 32
  fitT : (s.syms s1234Sym).toNat + 4096 ≤ 2 ^ 32
  wS : InRegions s.wr (S.setWidth 64) 256
  wD : InRegions s.wr (D.setWidth 64) (8 * N)
  inK : InRegions (s.rd ++ s.wr) (K.setWidth 64) 128
  inT : InRegions (s.rd ++ s.wr) ((s.syms s1234Sym).setWidth 64) 4096
  sp : 4 ≤ (s.gpr .esp).toNat
  dDS : Region.Disjoint ⟨D.setWidth 64, 8 * N⟩ ⟨S.setWidth 64, 256⟩
  dKS : Region.Disjoint ⟨K.setWidth 64, 128⟩ ⟨S.setWidth 64, 256⟩
  dKD : Region.Disjoint ⟨K.setWidth 64, 128⟩ ⟨D.setWidth 64, 8 * N⟩
  dTS : Region.Disjoint ⟨(s.syms s1234Sym).setWidth 64, 4096⟩ ⟨S.setWidth 64, 256⟩
  dTD : Region.Disjoint ⟨(s.syms s1234Sym).setWidth 64, 4096⟩ ⟨D.setWidth 64, 8 * N⟩
  dS : Region.Disjoint ⟨S.setWidth 64, 256⟩ (below (s.gpr .esp) 4)
  dD : Region.Disjoint ⟨D.setWidth 64, 8 * N⟩ (below (s.gpr .esp) 4)
  dK : Region.Disjoint ⟨K.setWidth 64, 128⟩ (below (s.gpr .esp) 4)
  dT : Region.Disjoint ⟨(s.syms s1234Sym).setWidth 64, 4096⟩ (below (s.gpr .esp) 4)
  nv : n = 12 ∨ n = 16
  sk : Spec.Cast5.scheduleAt m0 (K.setWidth 64) = k
  held : Held m0 ((s.syms s1234Sym).setWidth 64) s1234
  schedSlot : m0.readW (addr S schedOff) 32 = K
  roundsSlot : m0.readW (addr S roundsOff) 32 = BitVec.ofNat 32 n

/-- The state of ECB with `j` of the `N` blocks done. -/
structure LInv (s : State) (m0 : Mem) (up : Bool) (S D : BitVec 32) (k : Spec.Cast5.Schedule) (n N j : Nat)
    (u : State) : Prop where
  si : u.gpr .esi = S
  sp : u.gpr .esp = s.gpr .esp
  fr : Frame (loopMem S D N (s.gpr .esp)) m0 u.mem
  blocks : ∀ i < N, Spec.Cast5.blockAt u.mem (D.setWidth 64 + BitVec.ofNat 64 (8 * i)) =
    if i < j then cipher up k n (Spec.Cast5.blockAt m0 (D.setWidth 64 + BitVec.ofNat 64 (8 * i)))
    else Spec.Cast5.blockAt m0 (D.setWidth 64 + BitVec.ofNat 64 (8 * i))
  dslot : u.mem.readW (addr S dataOff) 32 = D + BitVec.ofNat 32 (8 * j)
  nslot : u.mem.readW (addr S nOff) 32 = BitVec.ofNat 32 (N - j)
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  syms : u.syms = s.syms

theorem setWidth_blk {D : BitVec 32} {N j : Nat} (hd : D.toNat + 8 * N ≤ 2 ^ 32) (hj : j < N) :
    (D + BitVec.ofNat 32 (8 * j)).setWidth 64 = D.setWidth 64 + BitVec.ofNat 64 (8 * j) :=
  addr_eq (x := D) (k := 8 * j) (by omega_arith)

theorem sub_blk (P : Addr) {N j : Nat} (hj : j < N) :
    Region.Sub ⟨P + BitVec.ofNat 64 (8 * j), 8⟩ ⟨P, 8 * N⟩ := Offset.sub_base _ (by omega_arith)

/-- The regions the loop writes miss the subkeys, the table and the slots
`32 … 55`. -/
theorem loopMem_disjoint {s : State} {m0 : Mem} {S D K : BitVec 32} {k : Spec.Cast5.Schedule} {n N : Nat}
    (hl : Lay s m0 S D K k n N) : ∀ r ∈ loopMem S D N (s.gpr .esp), r.Disjoint ⟨K.setWidth 64, 128⟩ ∧
      r.Disjoint ⟨(s.syms s1234Sym).setWidth 64, 4096⟩ ∧ r.Disjoint (slotR S 32 24) := by
  intro r hr
  simp only [loopMem, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨hl.dKD.symm, hl.dTD.symm, hl.dDS.sub_right (slot_sub S (by decide))⟩
  · exact ⟨(hl.dKS.sub_right (slot_sub S (by decide))).symm, (hl.dTS.sub_right (slot_sub S (by decide))).symm,
      Offset.disjoint _ (by decide) (by decide) (by decide)⟩
  · exact ⟨(hl.dKS.sub_right (slot_sub S (by decide))).symm, (hl.dTS.sub_right (slot_sub S (by decide))).symm,
      Offset.disjoint _ (by decide) (by decide) (by decide)⟩
  · exact ⟨hl.dK.symm, hl.dT.symm, (hl.dS.sub_left (slot_sub S (by decide))).symm⟩

theorem slot32_frame {m m' : Mem} {rs : List Region} {S : BitVec 32} (hfit : S.toNat + 256 ≤ 2 ^ 32)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, r.Disjoint (slotR S 32 24)) {d : Nat} (h1 : 32 ≤ d) (h2 : d + 4 ≤ 56) :
    m'.readW (addr S d) 32 = m.readW (addr S d) 32 := by
  rw [addr_off hfit d (by omega_arith)]
  exact hf.readW (r := slotR S 32 24) (Offset.contains _ h1 (by omega_arith) (by omega_arith))
    (fun r hr => (hd r hr).symm) (by decide)

/-- `crypt`'s precondition, at block `j`. -/
theorem LInv.bpre {s u : State} {m0 : Mem} {up : Bool} {S D K : BitVec 32} {k : Spec.Cast5.Schedule} {n N j : Nat}
    (hl : Lay s m0 S D K k n N) (h : LInv s m0 up S D k n N j u) (hj : j < N) :
    BPre u S K (D + BitVec.ofNat 32 (8 * j)) k n := by
  have hd := loopMem_disjoint hl
  have eD := setWidth_blk hl.fitD hj
  have hsub : Region.Sub (blockR (D + BitVec.ofNat 32 (8 * j))) ⟨D.setWidth 64, 8 * N⟩ := by
    rw [blockR, eD]; exact sub_blk _ hj
  refine ⟨⟨h.si, hl.fitS, by rw [h.wr]; exact hl.wS, ?_, ?_, hl.nv, hl.fitK, by rw [h.rd, h.wr]; exact hl.inK,
    fun i hi => ?_, by rw [h.sp]; exact hl.sp, by rw [h.sp]; exact hl.dS, by rw [h.sp]; exact hl.dK, hl.dKS,
    by rw [h.syms]; exact hl.fitT, by rw [h.rd, h.wr, h.syms]; exact hl.inT, by rw [h.syms, h.sp]; exact hl.dT,
    by rw [h.syms]; exact hl.dTS, ?_⟩, h.dslot, ?_, ?_, hl.dDS.sub_left hsub, (hl.dKD.symm).sub_left hsub,
    by rw [h.syms]; exact (hl.dTD.symm).sub_left hsub, by rw [h.sp]; exact hl.dD.sub_left hsub⟩
  · rw [slot32_frame hl.fitS h.fr (fun r hr => (hd r hr).2.2) (by decide) (by decide)]; exact hl.schedSlot
  · rw [slot32_frame hl.fitS h.fr (fun r hr => (hd r hr).2.2) (by decide) (by decide)]; exact hl.roundsSlot
  · rw [← Proof.Cast5.scheduleAt_getD _ _ hi, scheduleAt_frame h.fr (fun r hr => ((hd r hr).1).symm), hl.sk]
  · rw [h.syms]
    exact tabAt_of_held (held_frame hl.held h.fr fun r hr => ((hd r hr).2.1).symm)
  · have := hl.fitD
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * j) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  · rw [h.wr, eD]
    exact CallLay.inRegions_sub hl.wD (by omega_arith) (by have := hl.fitD; omega_arith)

/-! ## The loop over the blocks -/

theorem ofNat_sub_one {a : Nat} (ha : 1 ≤ a) (hb : a < 2 ^ 32) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 1 = BitVec.ofNat 32 (a - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_arith

/-- `advance`: on to the next block. -/
theorem advance_ok (v : State) {S : BitVec 32} (hsi : v.gpr .esi = S) (hfit : S.toNat + 256 ≤ 2 ^ 32)
    (hw : InRegions v.wr (S.setWidth 64) 256) {x y : BitVec 32}
    (hx : v.mem.readW (addr S dataOff) 32 = x) (hy : v.mem.readW (addr S nOff) 32 = y) :
    WP isa (.block advance) v fun w =>
      w.mem = (v.mem.writeW (addr S dataOff) (x + BitVec.ofNat 32 8)).writeW (addr S nOff) (y - BitVec.ofNat 32 1) ∧
      w.zf = some (y - BitVec.ofNat 32 1 == 0) ∧ w.gpr .esi = S ∧ w.gpr .esp = v.gpr .esp ∧ w.rd = v.rd ∧ w.wr = v.wr ∧
      w.syms = v.syms := by
  have hy' : (v.mem.writeW (addr S dataOff) (x + BitVec.ofNat 32 8)).readW (addr S nOff) 32 = y := by
    rw [rd_sep hfit _ _ (by decide) (by decide) (by decide)]; exact hy
  have rD := slot_rd (s := v) hfit hw (d := dataOff) (n := 4) (by decide)
  have rN := slot_rd (s := v) hfit hw (d := nOff) (n := 4) (by decide)
  have wD := slot_wr (s := v) hfit hw (d := dataOff) (n := 4) (by decide)
  have wN := slot_wr (s := v) hfit hw (d := nOff) (n := 4) (by decide)
  unfold advance
  crun [hsi, rD, rN, wD, wN, hx, hy']

theorem dslot_contains (S : BitVec 32) (hfit : S.toNat + 256 ≤ 2 ^ 32) {d : Nat} (h1 : dataOff ≤ d)
    (h2 : d + 4 ≤ 72) : Region.Contains (slotR S dataOff 16) (addr S d) (32 / 8) := by
  rw [addr_off hfit d (by omega_arith)]; exact Offset.contains _ h1 (by simp only [dataOff] at h2 ⊢; omega_arith) (by decide)

/-- A block and another. -/
theorem blk_disj_blk (P : Addr) {N i j : Nat} (hi : i < N) (hj : j < N) (hN : 8 * N ≤ 2 ^ 32) (hij : i ≠ j) :
    Region.Disjoint ⟨P + BitVec.ofNat 64 (8 * i), 8⟩ ⟨P + BitVec.ofNat 64 (8 * j), 8⟩ :=
  Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

/-- One block, then on to the next. -/
theorem step_ok {s u : State} {m0 : Mem} {up : Bool} {S D K : BitVec 32} {k : Spec.Cast5.Schedule} {n N j : Nat}
    (hl : Lay s m0 S D K k n N) (h : LInv s m0 up S D k n N j u) (hj : j < N) :
    WP isa (.seq (crypt up) (.block advance)) u fun w => LInv s m0 up S D k n N (j + 1) w ∧
      w.zf = some (decide (j + 1 = N)) := by
  have hdf := hl.fitD
  have eD := setWidth_blk hl.fitD hj
  have hb := h.bpre hl hj
  refine WP.seq (WP.mono (crypt_ok hb up) fun v hv => ?_)
  have vb := hv.blk
  have vf := hv.frame
  rw [blockR, eD, h.sp] at vf
  rw [eD] at vb
  have vsi : v.gpr .esi = S := (hv.same .esi (by decide)).trans h.si
  have vsp : v.gpr .esp = s.gpr .esp := (hv.same .esp (by decide)).trans h.sp
  -- The regions `crypt` wrote, against the slots of the data and the count.
  have dSl (o : Nat) (h1 : dataOff ≤ o) (h2 : o + 4 ≤ dataOff + 8) :
      ∀ r ∈ (⟨D.setWidth 64 + BitVec.ofNat 64 (8 * j), 8⟩ : Region) :: blockMem S (s.gpr .esp),
        Region.Disjoint (slotR S o 4) r := by
    intro r hr
    simp only [blockMem, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [dataOff] at h1 h2
    rcases hr with rfl | rfl | rfl | rfl
    · exact ((hl.dDS.sub_left (sub_blk _ hj)).symm.sub_left (slot_sub S (by omega_arith)))
    · exact hl.dS.sub_left (slot_sub S (by omega_arith))
    · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by decide)
    · exact Offset.disjoint _ (by simp only [kpOff]; omega_arith) (by omega_arith) (by decide)
  have vslot (o : Nat) (h1 : dataOff ≤ o) (h2 : o + 4 ≤ dataOff + 8) :
      v.mem.readW (addr S o) 32 = u.mem.readW (addr S o) 32 := by
    rw [addr_off hl.fitS o (by simp only [dataOff] at h2; omega_arith)]
    exact vf.readW (r := slotR S o 4)
      (Offset.contains _ (Nat.le_refl _) (Nat.le_refl _) (by simp only [dataOff] at h2; omega_arith)) (dSl o h1 h2)
      (by decide)
  have hw : InRegions v.wr (S.setWidth 64) 256 := by rw [hv.wr, h.wr]; exact hl.wS
  refine WP.mono (advance_ok v vsi hl.fitS hw (x := D + BitVec.ofNat 32 (8 * j)) (y := BitVec.ofNat 32 (N - j))
    (by rw [vslot dataOff (by decide) (by decide)]; exact h.dslot)
    (by rw [vslot nOff (by decide) (by decide)]; exact h.nslot)) fun w ⟨wm, wz, wsi, wsp, wrd, wwr, wsy⟩ => ?_
  -- The writes of `advance`.
  have fw : Frame [slotR S dataOff 16] v.mem w.mem := by
    rw [wm]
    exact ((Frame.refl _ _).writeW List.mem_cons_self _ (dslot_contains S hl.fitS (by decide) (by decide))).writeW
      List.mem_cons_self _ (dslot_contains S hl.fitS (by decide) (by decide))
  have dW (R : Region) (hR : Region.Disjoint R ⟨S.setWidth 64, 256⟩) : ∀ r ∈ [slotR S dataOff 16],
      Region.Disjoint R r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hR.sub_right (slot_sub S (by decide))
  refine ⟨⟨wsi, wsp.trans vsp, ?_, fun i hi => ?_, ?_, ?_, wrd.trans (hv.rd.trans h.rd),
    wwr.trans (hv.wr.trans h.wr), wsy.trans (hv.syms.trans h.syms)⟩, ?_⟩
  · refine h.fr.trans ((vf.sub fun r hr => ?_).trans (fw.mono (by simp [loopMem])))
    simp only [blockMem, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨D.setWidth 64, 8 * N⟩, by simp [loopMem], sub_blk _ hj⟩
    · exact ⟨below (s.gpr .esp) 4, by simp [loopMem], fun _ x => x⟩
    · exact ⟨slotR S 0 16, by simp [loopMem], fun _ x => x⟩
    · exact ⟨slotR S dataOff 16, by simp [loopMem], Offset.sub _ (by decide) (by decide)⟩
  · have hdi : Region.Disjoint ⟨D.setWidth 64 + BitVec.ofNat 64 (8 * i), 8⟩ ⟨S.setWidth 64, 256⟩ :=
      hl.dDS.sub_left (sub_blk _ hi)
    rw [blockAt_frame fw (dW _ hdi)]
    by_cases hij : i = j
    · subst hij
      rw [vb, ite_eq_left (by omega_arith), h.blocks i hi, ite_eq_right (by omega_arith)]
    · rw [blockAt_frame vf ?_, h.blocks i hi]
      · by_cases hlt : i < j
        · rw [ite_eq_left hlt, ite_eq_left (by omega_arith)]
        · rw [ite_eq_right hlt, ite_eq_right (by omega_arith)]
      · intro r hr
        simp only [blockMem, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact blk_disj_blk _ hi hj (by omega_arith) hij
        · exact hl.dD.sub_left (sub_blk _ hi)
        · exact hdi.sub_right (slot_sub S (by decide))
        · exact hdi.sub_right (slot_sub S (by decide))
  · rw [wm, rd_sep hl.fitS _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, BitVec.add_assoc,
      Nat.mul_add, BitVec.ofNat_add (8 * j)]
  · rw [wm, Mem.readW_writeW_self32, ofNat_sub_one (by omega_arith) (by omega_arith), Nat.sub_sub]
  · rw [wz, ofNat_sub_one (by omega_arith) (by omega_arith)]
    by_cases he : j + 1 = N
    · rw [decide_eq_true he, show N - j - 1 = 0 by omega_arith]; rfl
    · rw [decide_eq_false he]
      have : BitVec.ofNat 32 (N - j - 1) ≠ 0 := fun e => by
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, show (0 : BitVec 32).toNat = 0 from rfl] at this
        omega_arith
      simpa using this

/-- The loop over the blocks, from `j = 0`: afterwards every block is done. -/
theorem ecbLoop_ok {s u : State} {m0 : Mem} {up : Bool} {S D K : BitVec 32} {k : Spec.Cast5.Schedule} {n N : Nat}
    (hl : Lay s m0 S D K k n N) (hN : 0 < N) (h : LInv s m0 up S D k n N 0 u) :
    WP isa (.loop (.seq (crypt up) (.block advance)) .ne) u (LInv s m0 up S D k n N N) := by
  refine WP.loop (M := isa) (fun m (v : State) => ∃ j, m = N - j ∧ j < N ∧ LInv s m0 up S D k n N j v)
    ?_ N u ⟨0, rfl, hN, h⟩
  rintro m v ⟨j, rfl, hj, hv⟩
  refine WP.mono (step_ok hl hv hj) fun w ⟨hw, wz⟩ => ?_
  have hev : isa.eval .ne w = some (!decide (j + 1 = N)) := by
    simp only [eval, wz, Option.map_some]
  by_cases he : j + 1 = N
  · exact .inl ⟨by rw [hev, decide_eq_true he]; rfl, he ▸ hw⟩
  · exact .inr ⟨by rw [hev, decide_eq_false he]; rfl, N - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, hw⟩

/-! ## The whole function -/

/-- What the ECB functions need, as their proof states it: the arguments
(`schedule`, `rounds`, `data`, `n`, `scratch`) readable on the stack, the
schedule, the blocks, the working space and the table separate from each
other, from the word below `esp` and (those written) from the arguments and
the return address. -/
structure EPre (s : State) : Prop where
  rdEq : s.rd = [⟨(arg s 0).setWidth 64, 128⟩, ⟨argAddr s 0, 20⟩, ⟨(s.syms s1234Sym).setWidth 64, 4096⟩]
  wrEq : s.wr = [⟨(arg s 2).setWidth 64, (arg s 3).toNat * 8⟩, ⟨(arg s 4).setWidth 64, 256⟩]
  sp : 4 ≤ (s.gpr .esp).toNat
  spfit : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  inA : InRegions (s.rd ++ s.wr) (argAddr s 0) 20
  fitS : (arg s 4).toNat + 256 ≤ 2 ^ 32
  fitD : (arg s 2).toNat + 8 * (arg s 3).toNat ≤ 2 ^ 32
  fitK : (arg s 0).toNat + 128 ≤ 2 ^ 32
  fitT : (s.syms s1234Sym).toNat + 4096 ≤ 2 ^ 32
  wS : InRegions s.wr ((arg s 4).setWidth 64) 256
  wD : InRegions s.wr ((arg s 2).setWidth 64) (8 * (arg s 3).toNat)
  inK : InRegions (s.rd ++ s.wr) ((arg s 0).setWidth 64) 128
  inT : InRegions (s.rd ++ s.wr) ((s.syms s1234Sym).setWidth 64) 4096
  held : Held s.mem ((s.syms s1234Sym).setWidth 64) s1234
  dDS : Region.Disjoint ⟨(arg s 2).setWidth 64, 8 * (arg s 3).toNat⟩ ⟨(arg s 4).setWidth 64, 256⟩
  dKS : Region.Disjoint ⟨(arg s 0).setWidth 64, 128⟩ ⟨(arg s 4).setWidth 64, 256⟩
  dKD : Region.Disjoint ⟨(arg s 0).setWidth 64, 128⟩ ⟨(arg s 2).setWidth 64, 8 * (arg s 3).toNat⟩
  dTS : Region.Disjoint ⟨(s.syms s1234Sym).setWidth 64, 4096⟩ ⟨(arg s 4).setWidth 64, 256⟩
  dTD : Region.Disjoint ⟨(s.syms s1234Sym).setWidth 64, 4096⟩ ⟨(arg s 2).setWidth 64, 8 * (arg s 3).toNat⟩
  dS : Region.Disjoint ⟨(arg s 4).setWidth 64, 256⟩ (below (s.gpr .esp) 4)
  dD : Region.Disjoint ⟨(arg s 2).setWidth 64, 8 * (arg s 3).toNat⟩ (below (s.gpr .esp) 4)
  dK : Region.Disjoint ⟨(arg s 0).setWidth 64, 128⟩ (below (s.gpr .esp) 4)
  dT : Region.Disjoint ⟨(s.syms s1234Sym).setWidth 64, 4096⟩ (below (s.gpr .esp) 4)
  dAS : Region.Disjoint ⟨argAddr s 0, 20⟩ ⟨(arg s 4).setWidth 64, 256⟩
  dAD : Region.Disjoint ⟨argAddr s 0, 20⟩ ⟨(arg s 2).setWidth 64, 8 * (arg s 3).toNat⟩
  dRS : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 4).setWidth 64, 256⟩
  dRD : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨(arg s 2).setWidth 64, 8 * (arg s 3).toNat⟩
  nv : (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 16

/-- The ECB functions' contract on x86, as their proof states it. -/
def ecbX (up : Bool) : Contract isa where
  pre s := EPre s
  post s s' :=
    Spec.Cast5.blocksAt s'.mem ((arg s 2).setWidth 64) (arg s 3).toNat =
      Spec.Cast5.ecb (Spec.Cast5.scheduleAt s.mem ((arg s 0).setWidth 64)) (arg s 1).toNat
        (if up then .encrypt else .decrypt) (Spec.Cast5.blocksAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ (∀ i < 5, arg s₁ i = arg s₂ i) ∧ s₁.syms s1234Sym = s₂.syms s1234Sym

theorem cipher_map (up : Bool) (k : Spec.Cast5.Schedule) (n : Nat) (bs : List Spec.Cast5.Block) :
    bs.map (cipher up k n) = Spec.Cast5.ecb k n (if up then .encrypt else .decrypt) bs := by
  cases up <;> rfl

/-- Argument `i`, as the code reads it. -/
theorem argAddr_eq (s : State) {i : Nat} (h : (s.gpr .esp).toNat + 24 ≤ 2 ^ 32) (hi : i < 5) :
    addr (s.gpr .esp) (4 + 4 * i) = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) :=
  addr_eq (by omega_arith)

theorem arg_in {s : State} (h : EPre s) {i : Nat} (hi : i < 5) :
    InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) (4 + 4 * i)) 4 := by
  have e0 : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 := argAddr_eq s (i := 0) h.spfit (by decide)
  have hA := h.inA
  rw [e0] at hA
  rw [argAddr_eq s h.spfit hi, show 4 + 4 * i = 4 + 4 * i from rfl, ← Offset.add_add]
  exact CallLay.inRegions_sub hA (by omega_arith) (by decide)

/-- The saved registers. -/
def savedL : List (Reg × Nat) := [(.ebx, savedOff), (.edi, savedOff + 8), (.ebp, savedOff + 12)]

theorem saved_eq : saved = savedL ++ [(.esi, savedOff + 4)] := rfl
theorem restore_eq : restore = Spill.restoreCode .esi saved := rfl
theorem save_eq : save = Spill.saveCode .eax saved := rfl
theorem saved_fits : Spill.Fits 256 saved := by decide

theorem saved_contains {S : BitVec 32} (hfit : S.toNat + 256 ≤ 2 ^ 32) :
    ∀ p ∈ saved, Region.Contains (slotR S 32 16) (addr S p.2) 4 := by
  intro p hp
  simp only [saved, savedOff, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;>
  · rw [addr_off hfit _ (by decide)]; exact Offset.contains _ (by decide) (by decide) (by decide)

theorem saved_in {S : BitVec 32} (hfit : S.toNat + 256 ≤ 2 ^ 32) :
    ∀ p ∈ saved, Region.Contains ⟨S.setWidth 64, 256⟩ (addr S p.2) 4 := by
  intro p hp
  simp only [saved, savedOff, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;>
  · rw [addr_off hfit _ (by decide)]; exact Offset.contains_base _ (by decide) (by decide)

theorem ofNat_toNat32 (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The slots of the arguments, after the setup. -/
def argMem (m : Mem) (S K R D N : BitVec 32) : Mem :=
  (((m.writeW (addr S schedOff) K).writeW (addr S roundsOff) R).writeW (addr S dataOff) D).writeW (addr S nOff) N

theorem argMem_frame (m : Mem) {S : BitVec 32} (hfit : S.toNat + 256 ≤ 2 ^ 32) (K R D N : BitVec 32) :
    Frame [slotR S schedOff 16] m (argMem m S K R D N) := by
  have c (d : Nat) (h1 : schedOff ≤ d) (h2 : d + 4 ≤ 64) : Region.Contains (slotR S schedOff 16) (addr S d) (32 / 8) := by
    rw [addr_off hfit d (by omega_arith)]; exact Offset.contains _ h1 (by simp only [schedOff] at h2 ⊢; omega_arith) (by decide)
  exact (((Frame.refl _ _).writeW List.mem_cons_self _ (c schedOff (by decide) (by decide))).writeW
    List.mem_cons_self _ (c roundsOff (by decide) (by decide))).writeW List.mem_cons_self _
    (c dataOff (by decide) (by decide)) |>.writeW List.mem_cons_self _ (c nOff (by decide) (by decide))

theorem ecb_correct (up : Bool) (s : State) (h : EPre s) :
    WP isa (ecb up) s fun s' => abiPreserved s s' ∧ (ecbX up).post s s' := by
  obtain ⟨S, hS⟩ : ∃ S, arg s 4 = S := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, arg s 0 = K := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, arg s 1 = R := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, arg s 2 = D := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, arg s 3 = N := ⟨_, rfl⟩
  have fitS : S.toNat + 256 ≤ 2 ^ 32 := hS ▸ h.fitS
  have wS : InRegions s.wr (S.setWidth 64) 256 := hS ▸ h.wS
  have a4 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 20) 4 := arg_in h (i := 4) (by decide)
  have a0 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 4) 4 := arg_in h (i := 0) (by decide)
  have a1 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 8) 4 := arg_in h (i := 1) (by decide)
  have a2 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 12) 4 := arg_in h (i := 2) (by decide)
  have a3 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 16) 4 := arg_in h (i := 3) (by decide)
  have v4 : s.mem.readW (addr (s.gpr .esp) 20) 32 = S := hS
  -- The saved registers' memory.
  let g := (s.setReg .eax S).gpr
  let SM := Spill.saveMem s.mem (addr S) g saved
  have argSM (i : Nat) (hi : i < 4) : SM.readW (addr (s.gpr .esp) (4 + 4 * i)) 32 = arg s i := by
    refine Spill.saveMem_readW_of_sep _ _ (by decide) saved s.mem fun p hp => ?_
    refine Region.Disjoint.sep h.dAS ?_ ?_
    · have e0 : argAddr s 0 = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 4 :=
        argAddr_eq s (i := 0) h.spfit (by decide)
      rw [argAddr_eq s h.spfit (by omega_arith), e0, ← Offset.add_add]
      exact Offset.contains_base _ (by omega_arith) (by omega_arith)
    · rw [hS]; exact saved_in fitS p hp
  have sK : SM.readW (addr (s.gpr .esp) 4) 32 = K := (argSM 0 (by decide)).trans hK
  have sR : SM.readW (addr (s.gpr .esp) 8) 32 = R := (argSM 1 (by decide)).trans hR
  have sD : SM.readW (addr (s.gpr .esp) 12) 32 = D := (argSM 2 (by decide)).trans hD
  have sN : SM.readW (addr (s.gpr .esp) 16) 32 = N := (argSM 3 (by decide)).trans hN
  have wK := slot_wr (s := s) fitS wS (d := schedOff) (n := 4) (by decide)
  have wR := slot_wr (s := s) fitS wS (d := roundsOff) (n := 4) (by decide)
  have wD := slot_wr (s := s) fitS wS (d := dataOff) (n := 4) (by decide)
  have wN := slot_wr (s := s) fitS wS (d := nOff) (n := 4) (by decide)
  unfold ecb
  rw [List.append_assoc]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  have h1 : WP isa (.block [.mov .eax (.mem (at_ .esp 20))]) s fun s₁ => s₁ = s.setReg .eax S := by
    crun [a4, v4]
  refine WP.mono h1 fun s₁ e₁ => ?_
  subst e₁
  rw [save_eq]
  refine Spill.save_ok saved (fun p hp => ?_) fun s₂ u₂ => ?_
  · rw [wr_setReg, gpr_setReg_self]
    exact slot_wr fitS wS (d := p.2) (n := 4) (by have := saved_fits.1 p hp; omega_arith)
  have g₂ : s₂.gpr = g := u₂.gpr
  have m₂ : s₂.mem = SM := by rw [u₂.mem]; rfl
  have rd₂ : s₂.rd = s.rd := u₂.rd
  have wr₂ : s₂.wr = s.wr := u₂.wr
  have sy₂ : s₂.syms = s.syms := u₂.syms
  have hge : g .eax = S := gpr_setReg_self _ _ _
  have hgsp : g .esp = s.gpr .esp := gpr_setReg_of_ne _ _ (by decide)
  have hsetup : WP isa (.block setup) s₂ fun s₃ => s₃.mem = argMem SM S K R D N ∧ s₃.gpr .esi = S ∧
      s₃.gpr .esp = s.gpr .esp ∧ s₃.zf = some (N - BitVec.ofNat 32 0 == 0) ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr ∧
      s₃.syms = s.syms := by
    unfold setup
    crun [g₂, m₂, rd₂, wr₂, sy₂, hge, hgsp, a0, a1, a2, a3, sK, sR, sD, sN, wK, wR, wD, wN]
    rfl
  refine WP.mono hsetup fun s₃ ⟨m₃, si₃, sp₃, z₃, rd₃, wr₃, sy₃⟩ => ?_
  -- The memory after the setup, and the layout.
  let m0 := argMem SM S K R D N
  have F : Frame [⟨S.setWidth 64, 256⟩] s.mem m0 :=
    (Spill.saveMem_frame (R := ⟨S.setWidth 64, 256⟩) List.mem_cons_self (addr S) g saved s.mem (saved_in fitS)).trans
      ((argMem_frame SM fitS K R D N).sub fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self, slot_sub S (by decide)⟩)
  have dF (X : Region) (hX : X.Disjoint ⟨S.setWidth 64, 256⟩) : ∀ r ∈ [(⟨S.setWidth 64, 256⟩ : Region)], X.Disjoint r :=
    fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact hX
  have hl : Lay s m0 S D K (Spec.Cast5.scheduleAt s.mem (K.setWidth 64)) R.toNat N.toNat := by
    subst hS hK hR hD hN
    refine ⟨h.fitS, h.fitD, h.fitK, h.fitT, h.wS, h.wD, h.inK, h.inT, h.sp, h.dDS, h.dKS, h.dKD, h.dTS, h.dTD,
      h.dS, h.dD, h.dK, h.dT, h.nv, scheduleAt_frame F (dF _ h.dKS), held_frame h.held F (dF _ h.dTS), ?_, ?_⟩
    · simp only [m0, argMem]
      rw [rd_sep h.fitS _ _ (by decide) (by decide) (by decide), rd_sep h.fitS _ _ (by decide) (by decide) (by decide),
        rd_sep h.fitS _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
    · simp only [m0, argMem]
      rw [rd_sep h.fitS _ _ (by decide) (by decide) (by decide), rd_sep h.fitS _ _ (by decide) (by decide) (by decide),
        Mem.readW_writeW_self32, ofNat_toNat32]
  have h0 : LInv s m0 up S D (Spec.Cast5.scheduleAt s.mem (K.setWidth 64)) R.toNat N.toNat 0 s₃ := by
    refine ⟨si₃, sp₃, by rw [m₃]; exact Frame.refl _ _, fun i hi => by rw [m₃, ite_eq_right (by omega_arith)], ?_, ?_, rd₃,
      wr₃, sy₃⟩
    · rw [m₃]
      simp only [argMem]
      rw [rd_sep fitS _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]
      exact (BitVec.add_zero D).symm
    · rw [m₃]
      simp only [argMem]
      rw [Mem.readW_writeW_self32, Nat.sub_zero, ofNat_toNat32]
  -- The registers restored, and the blocks as the contract says.
  have fin : ∀ u, LInv s m0 up S D (Spec.Cast5.scheduleAt s.mem (K.setWidth 64)) R.toNat N.toNat N.toNat u →
      WP isa (.block restore) u fun s' => abiPreserved s s' ∧ (ecbX up).post s s' := by
    intro u hu
    have hd := loopMem_disjoint hl
    have hs0 : Spill.Saved SM (addr S) g saved := Spill.saveMem_saved_addr s.mem g saved_fits fitS
    have hs1 : Spill.Saved m0 (addr S) g saved :=
      hs0.of_frame (argMem_frame SM fitS K R D N) (saved_contains fitS) fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (by decide) (by decide) (by decide)
    have hs2 : Spill.Saved u.mem (addr S) g saved :=
      hs1.of_frame hu.fr (saved_contains fitS) fun r hr =>
        ((hd r hr).2.2.symm).sub_left (Offset.sub _ (by decide) (by decide))
    rw [restore_eq, saved_eq, ← List.append_nil (Spill.restoreCode _ _)]
    refine Spill.restoreBase_ok savedL (by decide) (fun p hp => ?_) (by rw [hu.si, ← saved_eq]; exact hs2)
      fun s' hr => WP.block_nil ⟨⟨fun r hr' => ?_, ?_⟩, ?_⟩
    · rw [hu.si, hu.rd, hu.wr]
      rw [← saved_eq] at hp
      exact slot_rd fitS wS (d := p.2) (n := 4) (by have := saved_fits.1 p hp; omega_arith)
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl
      · exact (hr.gpr (.ebx, savedOff) (by decide)).trans (gpr_setReg_of_ne _ _ (by decide))
      · exact (hr.gpr (.esi, savedOff + 4) (by decide)).trans (gpr_setReg_of_ne _ _ (by decide))
      · exact (hr.gpr (.edi, savedOff + 8) (by decide)).trans (gpr_setReg_of_ne _ _ (by decide))
      · exact (hr.gpr (.ebp, savedOff + 12) (by decide)).trans (gpr_setReg_of_ne _ _ (by decide))
      · exact (hr.other .esp (by decide)).trans hu.sp
    · have dR : ∀ r ∈ loopMem S D N.toNat (s.gpr .esp), Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ r := by
        intro r hr'
        simp only [loopMem, List.mem_cons, List.not_mem_nil, or_false] at hr'
        rcases hr' with rfl | rfl | rfl | rfl
        · rw [← hD, ← hN]; exact h.dRD
        · rw [← hS]; exact h.dRS.sub_right (by rw [hS]; exact slot_sub S (by decide))
        · rw [← hS]; exact h.dRS.sub_right (by rw [hS]; exact slot_sub S (by decide))
        · rw [below, Taint.sub_setWidth h.sp]
          exact Offset.base_disjoint_below _ (by decide)
      rw [hr.mem, hu.fr.readW (Region.contains_self _ _) dR (by decide),
        F.readW (Region.contains_self _ _) (dF _ (by rw [← hS]; exact h.dRS)) (by decide)]
    · show Spec.Cast5.blocksAt s'.mem _ _ = _
      rw [hK, hR, hD, hN, hr.mem, ← cipher_map]
      unfold Spec.Cast5.blocksAt
      rw [List.map_map]
      refine List.map_congr_left fun i hi => ?_
      rw [List.mem_range] at hi
      simp only [Function.comp]
      rw [hu.blocks i hi, ite_eq_left hi, blockAt_frame F fun r hr' => by
        rw [List.mem_singleton] at hr'; subst hr'
        exact (show Region.Disjoint ⟨D.setWidth 64, 8 * N.toNat⟩ ⟨S.setWidth 64, 256⟩ by
          rw [← hD, ← hN, ← hS]; exact h.dDS).sub_left (sub_blk _ hi)]
  refine WP.seq (WP.mono (Q := LInv s m0 up S D (Spec.Cast5.scheduleAt s.mem (K.setWidth 64)) R.toNat N.toNat N.toNat)
    ?_ fin)
  have hz : isa.eval .e s₃ = some (decide (N.toNat = 0)) := by
    simp only [eval, z₃, BitVec.sub_zero]
    congr 1
  refine WP.ite (decide (N.toNat = 0)) hz (fun hN0 => ?_) (fun hN0 => ?_)
  · have e : N.toNat = 0 := of_decide_eq_true hN0
    refine WP.block_nil ?_
    rw [e]; rw [e] at h0; exact h0
  · exact ecbLoop_ok hl (by have := of_decide_eq_false hN0; omega_arith) h0

end VG.Proof.Cast5.X86

module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.KcCckMain
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KcCkCT
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Rsa.PPC64LE.KcCckMain
meta import VerifiedGarbage.Proof.Rsa.PPC64LE.KcCkCT
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvCheck
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvLoads
meta import VerifiedGarbage.Proof.Rsa.PPC64LE.KcEntry
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KcEntry

/-!
# `vg_rsa_check_crt_key` on PPC64LE: constant time

As `KcCkCT.lean`, with the stack arguments and registers of
`vg_rsa_check_crt_key`.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.KeyCheck

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.KeyCheck
open VG.Impl.Rsa.PPC64LE.Keys (seqs)
open VG.Proof.Bignum.PPC64LE.Pub (sat)

def cckPub (s : State) : KD :=
  ⟨argRegs.map s.gpr, (List.range 8).map (PPC64LE.stackArg s), (nB s ++ eB s).map (·.toNat)⟩

/-- A state the contract allows, with the public data `d`. -/
def CK0 (d : KD) (s : State) : Prop := cckP.pre s ∧ cckPub s = d

theorem CK0.reg {d : KD} {s₁ s₂ : State} (h₁ : CK0 d s₁) (h₂ : CK0 d s₂) {r : Reg} (hr : r ∈ argRegs) :
    s₁.gpr r = s₂.gpr r :=
  List.map_inj_left.mp ((congrArg KD.regs h₁.2).trans (congrArg KD.regs h₂.2).symm) r hr

theorem CK0.arg {d : KD} {s₁ s₂ : State} (h₁ : CK0 d s₁) (h₂ : CK0 d s₂) {i : Nat} (hi : i < 8) :
    PPC64LE.stackArg s₁ i = PPC64LE.stackArg s₂ i :=
  List.map_inj_left.mp ((congrArg KD.stk h₁.2).trans (congrArg KD.stk h₂.2).symm) i (List.mem_range.mpr hi)

theorem CK0.bytes {d : KD} {s₁ s₂ : State} (h₁ : CK0 d s₁) (h₂ : CK0 d s₂) : nB s₁ = nB s₂ ∧ eB s₁ = eB s₂ :=
  bytes_of_map ((congrArg KD.ne h₁.2).trans (congrArg KD.ne h₂.2).symm)
    (by rw [len_bytes, len_bytes, kK, kK, h₁.reg h₂ (r := .r4) (by decide)])

theorem CK0.k {d : KD} {s₁ s₂ : State} (h₁ : CK0 d s₁) (h₂ : CK0 d s₂) : kK s₁ = kK s₂ := by
  rw [kK, kK, h₁.reg h₂ (r := .r4) (by decide)]

/-! ### The entry -/

/-- What the entry establishes. -/
def cckE (s0 t : State) : Prop :=
  ∃ u v, Keep [.r11, .r31] s0 u ∧ CckM u v ∧
    Keep [.r0, .r3, .r4, .r7, .r8, .r24, .r0, .r3, .r4, .r24, .r26] v t ∧ KBase (cckB s0) (cckZ s0) s0 t ∧
    t.gpr .r24 = BitVec.ofNat 64 (sat (Spec.Rsa.os2ip (eB s0))) <<< 31 ∧
    t.gpr .r26 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if Spec.Rsa.exponentValid (Spec.Rsa.os2ip (eB s0)) then 1 else 0) ∧
    Keep (entryRegs [.r14, .r15, .r18, .r19, .r20, .r21, .r7, .r8]) s0 t

/-- The entry after its first load. -/
abbrev cckR1 : List Instr :=
  (save 6).drop 2 ++ VG.Impl.Rsa.PPC64LE.CheckCrtKey.moves ++ ([.addi .r7 .r5 0, .addi .r8 .r6 0] : List Instr)

/-- The reading and the check of `e`. -/
abbrev cckY : Prog isa :=
  .seq VG.Impl.Bignum.PPC64LE.PublicChecked.readE (.block VG.Impl.Bignum.PPC64LE.PublicChecked.checkE)

theorem cck_entry_split : entry 6 VG.Impl.Rsa.PPC64LE.CheckCrtKey.moves =
    .seq (.block (VG.Impl.Rsa.PPC64LE.CrtValues.stackArg .r11 6 ++ cckR1)) cckY := rfl

/-- After the entry's first load. -/
def CK1 (d : KD) (t : State) : Prop :=
  ∃ s0, CK0 d s0 ∧ t.gpr .r11 = PPC64LE.stackArg s0 6 ∧ t.gpr .r5 = s0.gpr .r5 ∧ t.gpr .r6 = s0.gpr .r6 ∧
    WP isa (.block cckR1) t fun v => (v.gpr .r7 = s0.gpr .r5 ∧ v.gpr .r8 = s0.gpr .r6) ∧ WP isa cckY v (cckE s0)

/-- After the moves. -/
def CK1' (d : KD) (v : State) : Prop :=
  ∃ s0, CK0 d s0 ∧ v.gpr .r7 = s0.gpr .r5 ∧ v.gpr .r8 = s0.gpr .r6 ∧ WP isa cckY v (cckE s0)

/-- After the entry. -/
def CK2 (d : KD) (t : State) : Prop := ∃ s0, CK0 d s0 ∧ cckE s0 t

theorem pins_CK1 : Pins CK1 [.r11, .r5, .r6] := by
  rintro d s₁ s₂ ⟨a, ha, a11, a5, a6, -⟩ ⟨b, hb, b11, b5, b6, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [a11, b11, ha.arg hb (by decide)]
  · rw [a5, b5, ha.reg hb (by decide)]
  · rw [a6, b6, ha.reg hb (by decide)]

theorem pins_CK1' : Pins CK1' [.r7, .r8] := by
  rintro d s₁ s₂ ⟨a, ha, a7, a8, -⟩ ⟨b, hb, b7, b8, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a7, b7, ha.reg hb (by decide)]
  · rw [a8, b8, ha.reg hb (by decide)]

theorem cck_entry {s0 : State} (h : cckP.pre s0) : WP isa (entry 6 VG.Impl.Rsa.PPC64LE.CheckCrtKey.moves) s0 (cckE s0) := by
  have hp := cck_kpre h
  obtain ⟨-, hrd, -, -, de, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hk, hk'⟩, e1, e2, -⟩ := id h
  exact entry_ok hp (by decide) cck_moves (by decide) rfl (CrtValues.ofNat_toNat64 _) e1 (by omega)
    (by rw [hrd]; simp) de

theorem CK1_of {d : KD} {s : State} (hs : CK0 d s) :
    WP isa (.block (VG.Impl.Rsa.PPC64LE.CrtValues.stackArg .r11 6)) s (CK1 d) := by
  have hp := cck_kpre hs.1
  have hw1 := cck_entry hs.1
  rw [cck_entry_split, WP.seq_iff] at hw1
  have hw2 : WP isa (.block (VG.Impl.Rsa.PPC64LE.CrtValues.stackArg .r11 6 ++ cckR1)) s fun v =>
      v.gpr .r7 = s.gpr .r5 ∧ v.gpr .r8 = s.gpr .r6 := by
    rw [show VG.Impl.Rsa.PPC64LE.CrtValues.stackArg .r11 6 ++ cckR1 =
      save 6 ++ (VG.Impl.Rsa.PPC64LE.CheckCrtKey.moves ++ ([.addi .r7 .r5 0, .addi .r8 .r6 0] : List Instr)) from rfl]
    exact save_ok hp (by decide) fun u _ ku => WP.mono (cck_moves u) fun v ⟨⟨_, _, v7, v8⟩, _⟩ =>
      ⟨by rw [v7, ku.gpr _ (by decide)], by rw [v8, ku.gpr _ (by decide)]⟩
  have hw := WP.and hw2 hw1
  rw [WP.block_append_iff] at hw
  have h11 : WP isa (.block (VG.Impl.Rsa.PPC64LE.CrtValues.stackArg .r11 6)) s fun t =>
      t.gpr .r11 = PPC64LE.stackArg s 6 ∧ t.gpr .r5 = s.gpr .r5 ∧ t.gpr .r6 = s.gpr .r6 := by
    rw [← List.append_nil (VG.Impl.Rsa.PPC64LE.CrtValues.stackArg .r11 6)]
    refine hp.stackArg_ok rfl rfl (r := .r11) (by decide) (by decide) (by decide) (WP.block_nil ?_)
    simp only [State.write, ↓reduceIte, reduceCtorEq, and_self]
  exact WP.mono (WP.and hw h11) fun t ⟨w, e11, e5, e6⟩ => ⟨s, hs, e11, e5, e6, w⟩

theorem cck_entry_ct : RelCT isa (Two CK0) (entry 6 VG.Impl.Rsa.PPC64LE.CheckCrtKey.moves) (Two CK2) := by
  rw [cck_entry_split]
  refine RelCT.seq (RelCT.block_append (RelCT.seq
    (two_post (two_taint _ pins_nil (by taint_decide)) fun _ _ h => CK1_of h)
    (two_post (Ψ := CK1') (two_taint _ pins_CK1 (by taint_decide)) fun _ _ ⟨s0, hs, _, _, _, w⟩ =>
      WP.mono w fun _ ⟨⟨e7, e8⟩, y⟩ => ⟨s0, hs, e7, e8, y⟩)))
    (two_post (two_taint _ pins_CK1' (by taint_decide)) fun _ _ ⟨s0, hs, _, _, y⟩ =>
      WP.mono y fun _ e => ⟨s0, hs, e⟩)

/-! ### After the entry -/

/-- With `e` valid and the stack arguments read. -/
def CckS (s0 t : State) : Prop :=
  KBase (cckB s0) (cckZ s0) s0 t ∧ CckRegs s0 t ∧
    t.gpr .r24 = BitVec.ofNat 64 (sat (Spec.Rsa.os2ip (eB s0))) <<< 31 ∧
    Spec.Rsa.exponentValid (Spec.Rsa.os2ip (eB s0)) = true

theorem CckS.of_keep {s0 t u : State} (h : CckS s0 t) {rs : List Reg} (k : Keep rs t u) (hm : u.mem = t.mem)
    (hr : ∀ r ∈ [Reg.r14, .r15, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r26, .r31], r ∉ rs :=
      by decide) : CckS s0 u :=
  ⟨h.1.of_regs k hm (hr _ (by decide)), h.2.1.of_keep k fun r h' => hr r (by revert h'; revert r; decide),
    (k.gpr _ (hr _ (by decide))).trans h.2.2.1, h.2.2.2⟩

/-- Before the restore. -/
def CKF (d : KD) (t : State) : Prop := ∃ s0, CK0 d s0 ∧ KBase (cckB s0) (cckZ s0) s0 t

theorem pins_CKF : Pins CKF [.r31] := by
  rintro d s₁ s₂ ⟨a, ha, b₁⟩ ⟨b, hb, b₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [b₁.r31, b₂.r31]; exact ha.arg hb (by decide)

theorem cev_iff {d : KD} {s₁ s₂ t₁ t₂ : State} (h₁ : CK0 d s₁) (h₂ : CK0 d s₂) (e₁ : cckE s₁ t₁) (e₂ : cckE s₂ t₂) :
    isa.eval (.zero .d .r26) t₁ = isa.eval (.zero .d .r26) t₂ := by
  obtain ⟨-, -, -, -, -, -, -, a, -⟩ := e₁
  obtain ⟨-, -, -, -, -, -, -, b, -⟩ := e₂
  rw [eval_zero, eval_zero, a, b, (h₁.bytes h₂).2]

theorem cck_ev {s0 t : State} (e : cckE s0 t) (hz : (t.gpr .r26 == 0) = false) :
    Spec.Rsa.exponentValid (Spec.Rsa.os2ip (eB s0)) = true := by
  obtain ⟨-, -, -, -, -, -, -, h26, -⟩ := e
  rw [h26] at hz
  cases e : Spec.Rsa.exponentValid (Spec.Rsa.os2ip (eB s0))
  · rw [e] at hz; simp at hz
  · rfl

theorem cck_stkS {s0 t1 : State} (h : cckP.pre s0) (he : cckE s0 t1) (hz : (t1.gpr .r26 == 0) = false) :
    WP isa (.block VG.Impl.Rsa.PPC64LE.CheckCrtKey.stk) t1 (CckS s0) := by
  have hev := cck_ev he hz
  obtain ⟨u, v, ku, ⟨m14, m15, m18, m19, m20, m21⟩, kv, b1, h24, -, -⟩ := he
  refine WP.mono (cck_stk (cck_kpre h) b1) fun t2 ⟨⟨m2, a22, a23, a26⟩, k2⟩ =>
    ⟨b1.of_regs k2 m2, ?_, by rw [k2.gpr _ (by decide), h24], hev⟩
  exact ⟨by rw [k2.gpr _ (by decide), kv.gpr _ (by decide), m14, ku.gpr _ (by decide)],
    by rw [k2.gpr _ (by decide), kv.gpr _ (by decide), m15, ku.gpr _ (by decide)],
    by rw [k2.gpr _ (by decide), kv.gpr _ (by decide), m18, ku.gpr _ (by decide)],
    by rw [k2.gpr _ (by decide), kv.gpr _ (by decide), m19, ku.gpr _ (by decide)],
    by rw [k2.gpr _ (by decide), kv.gpr _ (by decide), m20, ku.gpr _ (by decide)],
    by rw [k2.gpr _ (by decide), kv.gpr _ (by decide), m21, ku.gpr _ (by decide)], a22, a23, a26⟩

/-- After the stack arguments are read. -/
def CKS (d : KD) (t : State) : Prop := ∃ s0, CK0 d s0 ∧ CckS s0 t

/-- After `check1`. -/
def CKC1 (d : KD) (t : State) : Prop :=
  ∃ s0, CK0 d s0 ∧ CckS s0 t ∧ t.gpr .r10 = BitVec.ofNat 64 (kK s0) ∧
    (t.gpr .r0 = 0 ↔ ((nB s0).getD (kK s0 - 1) 0).toNat % 2 = 1) ∧
    t.gpr .r11 = BitVec.ofNat 64 ((nB s0).getD 0 0).toNat

/-- After `check2`. -/
def CKC2 (d : KD) (t : State) : Prop :=
  ∃ s0, CK0 d s0 ∧ CckS s0 t ∧ (t.gpr .r0 = 0 ↔ Spec.Rsa.modulusValid (Spec.Rsa.os2ip (nB s0)) (kK s0) = true)

theorem pins_CKS : Pins CKS [.r14, .r15] := by
  rintro d s₁ s₂ ⟨a, ha, -, R₁, -⟩ ⟨b, hb, -, R₂, -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [R₁.r14, R₂.r14, ha.reg hb (by decide)]
  · rw [R₁.r15, R₂.r15, ha.reg hb (by decide)]

theorem pins_CKC1 : Pins CKC1 [.r10, .r11] := by
  rintro d s₁ s₂ ⟨a, ha, -, a10, -, a11⟩ ⟨b, hb, -, b10, -, b11⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a10, b10, ha.k hb]
  · rw [a11, b11, (ha.bytes hb).1]

/-- The registers the checks start from. -/
abbrev cckBody : List Reg := [.r14, .r15, .r18, .r19, .r20, .r21, .r22, .r23, .r26, .r31]

theorem pins_cbody {Φ : KD → State → Prop} (hΦ : ∀ d s, Φ d s → CKC2 d s) : Pins Φ cckBody := by
  intro d s₁ s₂ h₁ h₂ r hr
  obtain ⟨a, ha, ⟨b₁, R₁, -⟩, -⟩ := hΦ _ _ h₁
  obtain ⟨b, hb, ⟨b₂, R₂, -⟩, -⟩ := hΦ _ _ h₂
  simp only [cckBody, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [R₁.r14, R₂.r14, ha.reg hb (by decide)]
  · rw [R₁.r15, R₂.r15, ha.reg hb (by decide)]
  · rw [R₁.r18, R₂.r18, ha.reg hb (by decide)]
  · rw [R₁.r19, R₂.r19, ha.reg hb (by decide)]
  · rw [R₁.r20, R₂.r20, ha.reg hb (by decide)]
  · rw [R₁.r21, R₂.r21, ha.reg hb (by decide)]
  · rw [R₁.r22, R₂.r22, ha.arg hb (by decide)]
  · rw [R₁.r23, R₂.r23, ha.arg hb (by decide)]
  · rw [R₁.r26, R₂.r26, ha.arg hb (by decide)]
  · rw [b₁.r31, b₂.r31]; exact ha.arg hb (by decide)

theorem CKC1_of {d : KD} {s : State} (h : CKS d s) :
    WP isa (.seq (.block [.addi .r9 .r14 0, .addi .r10 .r15 0])
      (.block VG.Impl.Rsa.PPC64LE.CrtValues.check1)) s (CKC1 d) := by
  obtain ⟨s0, hs, S⟩ := h
  obtain ⟨-, hrd, -, dn, -, -, -, -, -, -, -, wn, -, -, -, -, -, -, -, ⟨hk, -⟩, -⟩ := id hs.1
  refine WP.seq (WP.mono (CrtValues.mv2_ok (s := s) (d₁ := .r9) (d₂ := .r10) (a := .r14) (b := .r15)
    (by decide) (by decide) (by decide) (by decide)) fun t3 ⟨⟨u9, u10, m3⟩, k3⟩ => ?_)
  have S3 := S.of_keep k3 m3
  have wn' : (s0.gpr .r3).toNat + kK s0 ≤ 2 ^ 64 := wn
  have hc : ∀ i < kK s0, (⟨s0.gpr .r3, kK s0⟩ : Region).Contains (off (s0.gpr .r3) i) 1 := fun i hi =>
    Offset.contains_base _ (by omega) (by omega)
  have h10 : t3.gpr .r10 = BitVec.ofNat 64 (kK s0) := by rw [u10, S.2.1.r15]; exact CrtValues.ofNat_toNat64 _
  refine WP.mono (CrtValues.check1_ok (N := s0.gpr .r3) (k := kK s0) (nb := nB s0)
    (by rw [u9, S.2.1.r14]; simp [off]) h10 hk (len_bytes _ _ _)
    (fun i hi => ⟨_, List.mem_append_left _ (by rw [S3.1.rd, hrd]; simp), hc i hi⟩)
    (fun i hi => by
      rw [S3.1.frame _ (CrtValues.past_of_disjoint dn (hc i hi))]; simp [Spec.Rsa.bytesAt, off]))
    fun t4 ⟨⟨i0, i11, im⟩, k4⟩ => ⟨s0, hs, S3.of_keep k4 im, by rw [k4.gpr _ (by decide), h10],
      by rw [i0, getD_of_lt (l := nB s0) (i := kK s0 - 1) (by simp only [len_bytes, kK]; omega)], by rw [i11, getD_of_lt (l := nB s0) (i := 0) (by simp only [len_bytes, kK]; omega)]⟩

theorem CKC2_of {d : KD} {s : State} (h : CKC1 d s) : WP isa VG.Impl.Rsa.PPC64LE.CrtValues.check2 s (CKC2 d) := by
  obtain ⟨s0, hs, S, h10, i0, i11⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hk, hk'⟩, -⟩ := id hs.1
  refine WP.mono (CrtValues.check2_ok h10 hk hk' (len_bytes _ _ _)
    (by rw [i0, getD_of_lt (l := nB s0) (i := kK s0 - 1) (by simp only [len_bytes, kK]; omega)]) (by rw [i11, getD_of_lt (l := nB s0) (i := 0) (by simp only [len_bytes, kK]; omega)]))
    fun t ⟨hv, tm, kt⟩ => ⟨s0, hs, S.of_keep kt tm, hv⟩

theorem cnv_iff {d : KD} {s₁ s₂ : State} (h₁ : CKC2 d s₁) (h₂ : CKC2 d s₂) :
    (s₁.gpr .r0 = 0 ↔ s₂.gpr .r0 = 0) := by
  obtain ⟨a, ha, -, i₁⟩ := h₁
  obtain ⟨b, hb, -, i₂⟩ := h₂
  rw [i₁, i₂, (ha.bytes hb).1, ha.k hb]

theorem ret0_CKF {Φ : KD → State → Prop} (hΦ : ∀ d s, Φ d s → CKF d s) :
    RelCT isa (Two Φ) (.block ret0) (Two CKF) :=
  two_post (two_taint _ pins_nil (by taint_decide)) fun _ _ h => by
    obtain ⟨s0, hs, b⟩ := hΦ _ _ h
    exact WP.mono (ret0_ok _) fun _ ⟨⟨_, tm⟩, kt⟩ => ⟨s0, hs, b.of_regs kt tm⟩

theorem cck_checks_ct :
    RelCT isa (Two CKC2) (.ite (.zero .d .r0)
      (seqs (([setup, .block eArr] : List (Prog isa)) ++ VG.Impl.Rsa.PPC64LE.CheckCrtKey.loads ++
        (start ++ crtChecks) ++
        ([.block ret] : List (Prog isa)))) (.block ret0)) (Two CKF) := by
  refine ite_rel (fun _ _ _ h₁ h₂ => cnv_iff h₁ h₂)
    (two_post (two_taint _ (pins_cbody fun _ _ h => h.1) (by taint_decide)) fun _ _ ⟨⟨s0, hs, S, hv⟩, h0⟩ => ?_)
    (ret0_CKF fun _ _ ⟨⟨s0, hs, S, _⟩, _⟩ => ⟨s0, hs, S.1⟩)
  refine WP.mono (cck_valid hs.1 S.1 S.2.1 S.2.2.1 (hv.mp h0) S.2.2.2) fun _ ⟨b, _⟩ => ⟨s0, hs, b⟩

theorem cck_rel : RelCT isa (Two CK0) VG.Impl.Rsa.PPC64LE.CheckCrtKey.code fun _ _ => True := by
  unfold VG.Impl.Rsa.PPC64LE.CheckCrtKey.code fn
  refine RelCT.seq cck_entry_ct (RelCT.seq ?_ (two_taint _ pins_CKF (by taint_decide)))
  refine ite_rel (fun _ _ _ ⟨a, ha, ea⟩ ⟨b, hb, eb⟩ => ?_) (ret0_CKF fun _ _ ⟨⟨s0, hs, ⟨_, _, _, _, _, b, _⟩⟩, _⟩ => ⟨s0, hs, b⟩) ?_
  · have := cev_iff ha hb ea eb
    rw [eval_zero, eval_zero, Option.some.injEq] at this
    simpa only [beq_iff_eq] using Bool.eq_iff_iff.mp this
  refine RelCT.seq (two_post (Ψ := CKS) (two_taint _ pins_nil (by taint_decide))
    fun _ _ ⟨⟨s0, hs, e⟩, hz⟩ => WP.mono (cck_stkS hs.1 e (by simpa using hz)) fun _ h => ⟨s0, hs, h⟩) ?_
  unfold nCheck VG.Impl.Rsa.PPC64LE.CrtValues.check
  exact RelCT.seq (RelCT.assoc (RelCT.seq (two_post (two_taint _ pins_CKS (by taint_decide)) fun _ _ h => CKC1_of h)
    (two_post (two_taint _ pins_CKC1 (by taint_decide)) fun _ _ h => CKC2_of h))) cck_checks_ct

theorem cck_ct : ConstantTime isa cckP.pre cckP.pub VG.Impl.Rsa.PPC64LE.CheckCrtKey.code :=
  RelCT.constantTime (cck_rel.mono (fun s t ⟨hs, ht, hr, hsp, hst, hb⟩ =>
    ⟨cckPub s, ⟨hs, rfl⟩, ⟨ht, by
      simp only [cckPub, KD.mk.injEq]
      exact ⟨(List.map_inj_left.mpr hr).symm, hst.symm, hb.symm⟩⟩, hsp⟩) fun _ _ h => h)

end VG.Proof.Rsa.PPC64LE.KeyCheck

import VerifiedGarbage.Proof.Ed448.X86_64.BaseBits
import VerifiedGarbage.Proof.Ed448.X86_64.BaseEncode
import VerifiedGarbage.Proof.X448.X86_64.Main
import VerifiedGarbage.Proof.Ed448.X86_64.BaseLocal

/-!
# Ed448 base-point multiplication on x86-64: the whole function

The correctness of `vg_ed448_scalar_base` against the contract the proof is
written against (`scalarBaseLocal`, `BaseLocal.lean`): the scalar's bits, the
loop (`R` ends as the reference ladder's point, which encodes `[k]B` by
`BaseLadderOk`; the output's address kept in `rsi` across it and stored at
`OUT` again after it), the inversion of `Z` and the encoding, every write in the
working space but the result's, so the scalar is read unchanged, the
callee-saved registers are restored from the working space, and the return
address is kept.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64 VG.Proof.Ed448
open VG.Proof.X448.X86_64 (Scr Index Env E FieldOk word off Outside ofs Saved clob writeW_outside
  word_writeW_self invert_ok setRbx_ok E_outside contains_sc ofs_off' InvPost invert_post invertCall_post)
open VG.Impl.X448.X86_64 (BITS slot)
open VG.Spec.Ed448 (bytesAt decodeLE)

/-- The result's bytes: those of `y = Y/Z` and the sign of `x = X/Z`, for
`(X : Y : Z)` the ladder's point of a scalar of 57 bytes. -/
theorem encode_result (hL : BaseLadderOk) {X Y Z : Spec.X448.Fe} {m : Mem} {p : Addr}
    (h : (⟨X, Y, Z⟩ : Spec.Ed448.Point) = ladder (decodeLE (bytesAt m p 57)) 456) :
    Proof.X25519.leBytes 56 (Y * Proof.X448.invert Z).val ++
      [BitVec.ofNat 8 (128 * ((X * Proof.X448.invert Z).val % 2))] =
      Spec.Ed448.scalarBase (bytesAt m p 57) := by
  rw [Spec.Ed448.scalarBase, ← hL _ (decodeLE_below (by rw [bytesAt_eq]; simp [Spec.X25519.bytesAt])),
    ← h, encodePoint_code]

/-- The output's address into `r15`, the working space into `rdi`. -/
theorem movOut_ok (s : State) :
    WP isa (.block ([.mov .r15 (.reg .rdi), .mov .rdi (.reg .rdx)] : List Instr)) s fun t =>
      t.mem = s.mem ∧ t.gpr .r15 = s.gpr .rdi ∧ t.gpr .rdi = s.gpr .rdx ∧
      (∀ r, r ∉ [Reg.rdi, .r15] → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ?_, ?_, fun r hr => ?_, rfl, rfl⟩
  · simp [RegUpd.gpr_setReg]
  · simp [RegUpd.gpr_setReg]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]

theorem stashOut_ok {s : State} {base : Addr} (hb : s.gpr .rdi = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block stashOut) s fun t =>
      t.mem = s.mem.writeW (off base OUT) (s.gpr .r15) ∧ t.gpr .rsi = s.gpr .r15 ∧
        (∀ r, r ≠ .rsi → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have w : InRegions s.wr (off base OUT) 8 := ⟨_, hw, contains_sc (by decide)⟩
  apply WP.of_runBlock
  simp only [stashOut, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, hb, readSrc,
    State.store64, w, ite_true, Option.some.injEq, exists_eq_left', Option.map_some,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_setReg_self]
  refine ⟨trivial, trivial, fun r hr => ?_, trivial, trivial⟩
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr]

theorem restashOut_ok {s : State} {base : Addr} (hb : s.gpr .rdi = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block restashOut) s fun t =>
      t.mem = s.mem.writeW (off base OUT) (s.gpr .rsi) ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧
        t.wr = s.wr := by
  have w : InRegions s.wr (off base OUT) 8 := ⟨_, hw, contains_sc (by decide)⟩
  apply WP.of_runBlock
  simp only [restashOut, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, hb,
    State.store64, w, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial⟩

variable {fld : Impl.X448.X86_64.Field} (hf : FieldOk fld) {P : Point64.Ops} (hP : Point64.PointOk P)

include hf hP in
/-- With any point operations `P` that run the field programs (`PointOk`), and any inversion
`inv` that keeps and computes what `invert` does (`InvPost`). -/
theorem scalarBase_correct_of (hL : BaseLadderOk) {inv : Prog isa}
    (hinv : ∀ {s : State} {base : Addr}, Scr s base → WP isa inv s (InvPost base s))
    {s : State} (hp : scalarBaseLocal.pre s) :
    WP isa (scalarBaseWith fld P inv) s fun t => gprPreserved s t ∧ scalarBaseLocal.post s t := by
  obtain ⟨hr, hw, hd, hro, hrs, hos, hn⟩ := hp
  obtain ⟨base, hbase⟩ : ∃ b, s.gpr .rdx = b := ⟨_, rfl⟩
  rw [hbase] at hd hrs hos hn
  have hws : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hw, hbase]; simp
  have hwo : (⟨s.gpr .rdi, 57⟩ : Region) ∈ s.wr := by rw [hw]; simp
  rw [scalarBaseWith]
  -- The entry: the callee-saved registers, the output's address, the constants.
  apply WP.seq
  rw [entry, WP.block_append_iff]
  refine WP.mono (saveAt_ok .rdx hbase hws) fun s₁ ⟨g₁, rd₁, wr₁, o₁, sv₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (movOut_ok s₁) fun s₂ ⟨m₂, r15₂, di₂, g₂, rd₂, wr₂⟩ => ?_
  rw [g₁, hbase] at di₂
  rw [g₁] at r15₂
  have hs₂ : Scr s₂ base := ⟨di₂, by rw [wr₂, wr₁]; exact hws, by omega⟩
  refine WP.mono (consts_ok hs₂) fun s₃ ⟨p₃, q₃, d₃, o₃, g₃, rd₃, wr₃, _⟩ => ?_
  have hs₃ : Scr s₃ base := ⟨(g₃ _ (by decide)).trans di₂, wr₃ ▸ hs₂.wr, hs₂.nowrap⟩
  have rsi₃ : s₃.gpr .rsi = s.gpr .rsi := by
    rw [g₃ _ (by decide), g₂ _ (by decide), g₁]
  have rw₃ : s₃.rd = s.rd ∧ s₃.wr = s.wr := ⟨by rw [rd₃, rd₂, rd₁], by rw [wr₃, wr₂, wr₁]⟩
  have hfar : ∀ i < 57, 8192 ≤ ofs base (s.gpr .rsi + BitVec.ofNat 64 i) :=
    fun i hi => far hd hi (by decide)
  have O₃ : Outside base 0 8192 s.mem s₃.mem := by
    rw [m₂] at o₃
    exact (o₁.mono (by decide) (by decide)).trans (o₃.mono (by decide) (by decide))
  have hmem₃ : ∀ i < 57, s₃.mem (s.gpr .rsi + BitVec.ofNat 64 i) =
      s.mem (s.gpr .rsi + BitVec.ofNat 64 i) :=
    fun i hi => O₃ _ (Or.inr (hfar i hi))
  -- The scalar's bits.
  apply WP.seq
  refine WP.mono (bits_ok hs₃ rsi₃ (fun q hq => ⟨⟨s.gpr .rsi, 57⟩, by rw [rw₃.1, hr]; simp,
      Offset.contains_base _ (d := q) (n := 1) (k := 57) (by omega) (by omega)⟩) hfar)
    fun s₄' ⟨g₄', rd₄', wr₄', o₄', b₄⟩ => ?_
  have hs₄' : Scr s₄' base := ⟨(g₄' _ (by decide)).trans hs₃.rdi, wr₄' ▸ hs₃.wr, hs₃.nowrap⟩
  -- The output's address at `OUT`.
  apply WP.seq
  refine WP.mono (stashOut_ok hs₄'.rdi hs₄'.wr) fun s₄ ⟨m₄, si₄, g₄'', rd₄'', wr₄''⟩ => ?_
  have g₄ : ∀ r, r ∉ [Reg.rax, .rdx, .rbx, .rsi] → s₄.gpr r = s₃.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g₄'' r hr.2.2.2, g₄' r (by simp [hr.1, hr.2.1, hr.2.2.1])]
  have rd₄ : s₄.rd = s₃.rd := by rw [rd₄'', rd₄']
  have wr₄ : s₄.wr = s₃.wr := by rw [wr₄'', wr₄']
  have oo : Outside base OUT 8 s₄'.mem s₄.mem := by
    rw [m₄]; exact writeW_outside _ _ _ (by decide)
  have o₄ : Outside base OUT (BITS + 456 - OUT) s₃.mem s₄.mem :=
    (o₄'.mono (by decide) (by decide)).trans (oo.mono (by decide) (by decide))
  have hs₄ : Scr s₄ base := ⟨by rw [g₄'' _ (by decide)]; exact hs₄'.rdi, wr₄'' ▸ hs₄'.wr, hs₄'.nowrap⟩
  have si₄' : s₄.gpr .rsi = s.gpr .rdi := by rw [si₄, g₄' _ (by decide), g₃ _ (by decide), r15₂]
  have b₄' : ∀ t < 456, s₄.mem (off base (BITS + t)) =
      BitVec.ofNat 8 (((s₃.mem (s.gpr .rsi + BitVec.ofNat 64 (t / 8))).toNat >>> (t % 8)) &&& 1) :=
    fun t ht => by
      rw [oo _ (Or.inr (by rw [ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS, OUT]; omega))]
      exact b₄ t ht
  have hout₄ : word s₄.mem base OUT = s.gpr .rdi := by
    have r15₄ : s₄'.gpr .r15 = s.gpr .rdi := by rw [g₄' _ (by decide), g₃ _ (by decide), r15₂]
    rw [m₄, word_writeW_self, r15₄]
  have e₄ : ∀ i : Index, E s₄.mem base i = E s₃.mem base i := fun i => by
    have h1 := Proof.X448.X86_64.slot_lt i
    have h2 := Proof.X448.X86_64.slot_ge i
    simp only [Impl.X448.X86_64.ACC] at h1
    exact (E_outside oo i (Or.inr (by simp only [OUT]; omega))).trans
      (E_outside o₄' i (Or.inl (by simp only [BITS]; omega)))
  -- The loop.
  apply WP.seq
  rw [mulLoop]
  apply WP.seq
  refine WP.mono (show WP isa (.block [.mov32 .rbx (.imm (BitVec.ofNat 32 456))]) s₄ _ from
    setRbx_ok s₄ 456 (by decide)) fun s₅ ⟨rbx₅, g₅, m₅, rd₅, wr₅⟩ => ?_
  have hs₅ : Scr s₅ base := ⟨(g₅ _ (by decide)).trans hs₄.rdi, wr₅ ▸ hs₄.wr, hs₄.nowrap⟩
  let K := decodeLE (bytesAt s.mem (s.gpr .rsi) 57)
  have hbits : ∀ t < 456, s₅.mem (off base (BITS + t)) = BitVec.ofNat 8 ((K >>> t) &&& 1) := by
    intro t ht
    rw [m₅, b₄' t ht, hmem₃ _ (by omega), scalar_bit s.mem _ ht]
  have e₅ : ∀ i : Index, E s₅.mem base i = E s₃.mem base i := fun i => by rw [m₅, e₄]
  have I₅ : MInv base K s₅ 456 s₅ := by
    refine ⟨hs₅, rbx₅, fun _ _ => rfl, rfl, rfl, Outside.refl _ _ _ _, ?_, ?_, ?_⟩
    · show Proof.Ed448.pt (E s₅.mem base) 8 9 10 = _
      simp only [Proof.Ed448.pt, e₅]; exact q₃
    · rw [e₅]; exact d₃
    · simp only [Proof.Ed448.pt, e₅, Nat.sub_self]; exact p₃
  refine WP.mono (loop_ok hP hbits 456 s₅ (by decide) (by decide) I₅) fun s₆' I₆ => ?_
  -- The output's address at `OUT` again.
  apply WP.seq
  refine WP.mono (restashOut_ok I₆.scr.rdi I₆.scr.wr) fun s₆ ⟨m₆, g₆, rd₆, wr₆⟩ => ?_
  have hs₆ : Scr s₆ base := ⟨by rw [g₆]; exact I₆.scr.rdi, wr₆ ▸ I₆.scr.wr, hn⟩
  have si₆ : s₆'.gpr .rsi = s.gpr .rdi := by rw [I₆.gpr _ (by decide), g₅ _ (by decide), si₄']
  have o₆ : Outside base OUT 8 s₆'.mem s₆.mem := by
    rw [m₆]; exact writeW_outside _ _ _ (by decide)
  have e₆ : E s₆.mem base = E s₆'.mem base := funext fun i => by
    have h2 := Proof.X448.X86_64.slot_ge i
    exact E_outside o₆ i (Or.inr (by simp only [OUT]; omega))
  -- The inversion of `Z`.
  apply WP.seq
  refine WP.mono (hinv hs₆) fun s₇ ⟨g₇, rd₇, wr₇, o₇, e₇⟩ => ?_
  have hs₇ : Scr s₇ base := ⟨(g₇ _ (by decide) (by decide)).trans hs₆.rdi, wr₇ ▸ hs₆.wr, hn⟩
  -- The encoding.
  have hout₇ : word s₇.mem base OUT = s.gpr .rdi := by
    rw [o₇.word (by decide) (by decide), m₆, word_writeW_self, si₆]
  have sv₇ : Saved base s.gpr s₇.mem := by
    have sv₂ : Saved base s.gpr s₂.mem := by rw [m₂]; exact sv₁
    have sv₄ := (sv₂.outside o₃ (by decide)).outside o₄ (by decide)
    have sv₅ : Saved base s.gpr s₅.mem := by rw [m₅]; exact sv₄
    exact ((sv₅.outside I₆.mem (by decide)).outside o₆ (by decide)).outside o₇ (by decide)
  refine WP.mono (encode_ok hf hs₇ hout₇ (by rw [wr₇, wr₆, I₆.wr, wr₅, wr₄, rw₃.2]; exact hwo) hos sv₇)
    fun t ⟨bt, rt, gt, ft, _, _⟩ => ?_
  have O₇ : Outside base 0 8192 s.mem s₇.mem := by
    have O₅ : Outside base 0 8192 s.mem s₅.mem := by
      rw [m₅]; exact O₃.trans (o₄.mono (by decide) (by decide))
    exact ((O₅.trans (I₆.mem.mono (by decide) (by decide))).trans (o₆.mono (by decide) (by decide))).trans
      (o₇.mono (by decide) (by decide))
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rt (.rbx, 0) (by decide)
    · exact rt (.rbp, 8) (by decide)
    · rw [gt _ (by decide), g₇ _ (by decide) (by decide), g₆, I₆.gpr _ (by decide), g₅ _ (by decide),
        g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), g₁]
    · exact rt (.r12, 16) (by decide)
    · exact rt (.r13, 24) (by decide)
    · exact rt (.r14, 32) (by decide)
    · exact rt (.r15, 40) (by decide)
  · have F : Frame [⟨base, 8192⟩, ⟨s.gpr .rdi, 57⟩] s.mem t.mem :=
      ((VG.Proof.Ed448.X86_64.Outside.frame O₇).mono (by simp)).trans (ft.mono (by simp))
    exact F.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hrs
      · exact hro) (by decide)
  · show bytesAt t.mem (s.gpr .rdi) 57 = _
    have r₆ := I₆.rep
    rw [Nat.sub_zero] at r₆
    rw [bt, e₇, E_outside o₇ 0 (by decide), E_outside o₇ 1 (by decide), e₆]
    exact encode_result hL r₆

include hf hP in
theorem scalarBase_correct (hL : BaseLadderOk) {s : State} (hp : scalarBaseLocal.pre s) :
    WP isa (scalarBaseWith fld P) s fun t => gprPreserved s t ∧ scalarBaseLocal.post s t :=
  scalarBase_correct_of hf hP hL (fun hs => invert_post hf hs) hp

theorem scalarBase_inline : scalarBase.inline =
    scalarBaseWith Impl.X448.X86_64.baseline Point64.bodies
      (Impl.X448.X86_64.invertCall Impl.X448.X86_64.baseline [OUT]).inline :=
  rfl

/-- `vg_ed448_scalar_base`, its calls of the point functions and `vg_gf448_r64_pow223`
inlined. -/
theorem scalarBase_correct_inline (hL : BaseLadderOk) {s : State} (hp : scalarBaseLocal.pre s) :
    WP isa scalarBase.inline s fun t => gprPreserved s t ∧ scalarBaseLocal.post s t := by
  rw [scalarBase_inline]
  exact scalarBase_correct_of Proof.X448.X86_64.baseline_ok Point64.bodies_ok hL
    (fun hs => invertCall_post Proof.X448.X86_64.baseline_ok (keep := [OUT]) (by simp [OUT]) hs) hp

end VG.Proof.Ed448.X86_64

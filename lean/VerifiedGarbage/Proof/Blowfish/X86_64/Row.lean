import VerifiedGarbage.Proof.Blowfish.X86_64.Scan
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.LaneSse

/-!
# A row of the scan, instruction by instruction

`masks_run`: the masks of the row; `plane_run`: one plane's row into its
accumulator.
-/

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Blowfish.X86_64

theorem exec_xop (s : State) (op : XOp) : exec (.xop op) s = some (op.exec s) := rfl

theorem byte_readW128 (m : Mem) (a : Addr) {e : Nat} (he : e < 16) :
    byte (m.readW a 128) e = m (a + BitVec.ofNat 64 e) := by
  rw [← Mem.extractLsb'_read m a (n := 16) he]
  simp only [byte, Mem.readW]
  rfl

theorem word_psubw (a b : BitVec 128) {i : Nat} (hi : i < 8) :
    word (XBinOp.eval .psubw a b) i = word a i - word b i := by
  simp only [XBinOp.eval]; exact word_ofWords _ hi

theorem word_paddw (a b : BitVec 128) {i : Nat} (hi : i < 8) :
    word (XBinOp.eval .paddw a b) i = word a i + word b i := by
  simp only [XBinOp.eval]; exact word_ofWords _ hi

theorem word_psraw15 (a : BitVec 128) {i : Nat} (hi : i < 8) :
    word (XShiftOp.eval .psraw a (BitVec.ofNat 8 15)) i = (word a i).sshiftRight 15 := by
  simp only [XShiftOp.eval, word_ofWords _ hi]
  rfl

theorem runXops : ∀ (l : List XOp) (t : State),
    runBlock isa (l.map .xop) t = some (l.foldl (fun t op => op.exec t) t)
  | [], _ => runBlock_nil
  | op :: l, t => by rw [List.map_cons, runBlock_cons, exec_xop, runStep_some, runXops l]; rfl

/-- The row's even entries' numbers. -/
def rowK (r : Nat) : BitVec 128 := ofWords fun w => BitVec.ofNat 16 (16 * r + 2 * w)

/-- The index in every word. -/
def bcast (x : Byte) : BitVec 128 := ofWords fun _ => x.setWidth 16

theorem masks_run (u : State) (x : Byte) {r : Nat} (hr : r < 16) (hk : u.xmm kReg = rowK r)
    (hx : u.xmm idxReg = bcast x) (h1 : u.xmm onesReg = wordsOf 1) :
    ∃ u', runBlock isa masks u = some u' ∧
      (∀ w < 8, word (u'.xmm mEven) w = if x.toNat = 16 * r + 2 * w then BitVec.allOnes 16 else 0) ∧
      (∀ w < 8, word (u'.xmm mOdd) w = if x.toNat = 16 * r + 2 * w + 1 then BitVec.allOnes 16 else 0) ∧
      (∀ d, d ≠ mEven → d ≠ mOdd → u'.xmm d = u.xmm d) ∧ u' = { u with xmm := u'.xmm } := by
  let ops : List XOp := [.bin .movdqa mEven kReg, .bin .pxor mEven idxReg, .bin .psubw mEven onesReg,
    .shift .psraw mEven (BitVec.ofNat 8 15), .bin .movdqa mOdd kReg, .bin .paddw mOdd onesReg,
    .bin .pxor mOdd idxReg, .bin .psubw mOdd onesReg, .shift .psraw mOdd (BitVec.ofNat 8 15)]
  let u' := ops.foldl (fun t op => op.exec t) u
  refine ⟨u', runXops ops u, fun w hw => ?_, fun w hw => ?_, fun d h1 h2 => ?_, ?_⟩
  · simp (disch := decide) only [u', ops, List.foldl, XOp.exec, xmm_setXmm_self, xmm_setXmm_of_ne, hk, hx, h1]
    rw [word_psraw15 _ hw, word_psubw _ _ hw]
    simp only [XBinOp.eval]
    rw [word_pxor, rowK, bcast, wordsOf, word_ofWords _ hw, word_ofWords _ hw, word_ofWords _ hw]
    exact word_mask x _ (by omega_arith)
  · simp (disch := decide) only [u', ops, List.foldl, XOp.exec, xmm_setXmm_self, xmm_setXmm_of_ne, hk, hx, h1]
    rw [word_psraw15 _ hw, word_psubw _ _ hw]
    simp only [XBinOp.eval]
    rw [word_pxor, word_ofWords _ hw, rowK, bcast, wordsOf, word_ofWords _ hw, word_ofWords _ hw,
      word_ofWords _ hw, show BitVec.ofNat 16 (16 * r + 2 * w) + BitVec.ofNat 16 1 =
        BitVec.ofNat 16 (16 * r + 2 * w + 1) by rw [BitVec.ofNat_add_ofNat]]
    exact word_mask x _ (by omega_arith)
  · simp only [u', ops, List.foldl, XOp.exec, xmm_setXmm_of_ne _ _ h1, xmm_setXmm_of_ne _ _ h2]
  · simp only [u', ops, List.foldl, XOp.exec, State.setXmm]

theorem accReg_ne : ∀ b < 4, accReg b ≠ tmp ∧ accReg b ≠ tmp2 ∧ accReg b ≠ mEven ∧ accReg b ≠ mOdd ∧
    accReg b ≠ lowReg ∧ accReg b ≠ kReg ∧ accReg b ≠ idxReg ∧ accReg b ≠ onesReg ∧ accReg b ≠ sixteenReg ∧
    accReg b ≠ xL ∧ accReg b ≠ xR ∧ accReg b ≠ fReg := by decide

theorem exec_movdquLoad {s : State} {d : XReg} {m : MemOp} (h : InRegions (s.rd ++ s.wr) (s.ea m) 16) :
    exec (.movdquLoad d m) s = some (s.setXmm d (s.mem.readW (s.ea m) 128)) := by
  simp only [exec, State.load128, h, ite_true, Option.map_some]

/-- One plane's row, masked into its accumulator. -/
theorem plane_run (u : State) (sch : Reg) (j : Nat) {b : Nat} (hb : b < 4)
    (hR : InRegions (u.rd ++ u.wr) (u.ea (rowMem sch j b)) 16) :
    ∃ u', runBlock isa (plane sch j b) u = some u' ∧
      u'.xmm (accReg b) = (u.xmm (accReg b) |||
        ((u.mem.readW (u.ea (rowMem sch j b)) 128 &&&
          u.xmm lowReg) &&& u.xmm mEven)) |||
        (XShiftOp.eval .psrlw (u.mem.readW (u.ea (rowMem sch j b)) 128) (BitVec.ofNat 8 8) &&& u.xmm mOdd) ∧
      (∀ d, d ≠ tmp → d ≠ tmp2 → d ≠ accReg b → u'.xmm d = u.xmm d) ∧
      u' = { u with xmm := u'.xmm } := by
  obtain ⟨n1, n2, n3, n4, n5, -⟩ := accReg_ne b hb
  let T := u.mem.readW (u.ea (rowMem sch j b)) 128
  let u₁ := u.setXmm tmp T
  let ops : List XOp := [.bin .movdqa tmp2 tmp, .bin .pand tmp lowReg, .shift .psrlw tmp2 (BitVec.ofNat 8 8),
    .bin .pand tmp mEven, .bin .pand tmp2 mOdd, .bin .por (accReg b) tmp, .bin .por (accReg b) tmp2]
  refine ⟨ops.foldl (fun t op => op.exec t) u₁, ?_, ?_, fun d h1 h2 h3 => ?_, ?_⟩
  · rw [plane, runBlock_cons, exec_movdquLoad hR, runStep_some]
    exact runXops ops u₁
  · simp (disch := first | decide | with_reducible assumption | exact Ne.symm ‹_›) only [ops, u₁, List.foldl, XOp.exec,
      xmm_setXmm_self, xmm_setXmm_of_ne, XBinOp.eval]
    rfl
  · simp (disch := decide) only [ops, u₁, List.foldl, XOp.exec, xmm_setXmm_of_ne _ _ h1, xmm_setXmm_of_ne _ _ h2,
      xmm_setXmm_of_ne _ _ h3]
  · simp only [ops, u₁, List.foldl, XOp.exec, State.setXmm]

theorem cat_run {a b : List Instr} {s s₁ s₂ : State} (h₁ : runBlock isa a s = some s₁)
    (h₂ : runBlock isa b s₁ = some s₂) : runBlock isa (a ++ b) s = some s₂ := by
  rw [runBlock_append, h₁]; exact h₂

/-- Byte `e` of plane `b` of S-box `j` of the schedule at `S`. -/
def pl (S : Addr) (j b : Nat) (m : Mem) (e : Nat) : Byte := m (S + BitVec.ofNat 64 (planeOff j b + e))

/-- The S-boxes' planes are readable at `S`. -/
def Readable (s : State) (S : Addr) : Prop :=
  ∀ off, off + 16 ≤ 4096 → InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 off) 16

/-- What the rows need of the state the scan starts in. -/
structure ScanEnv (sch : Reg) (S : Addr) (x : Byte) (j : Nat) (u₀ : State) : Prop where
  j4 : j < 4
  hsch : u₀.gpr sch = S
  ne8 : sch ≠ Reg.r8
  ne9 : sch ≠ Reg.r9
  rd : Readable u₀ S
  idx : u₀.xmm idxReg = bcast x
  ones : u₀.xmm onesReg = wordsOf 1
  sixteen : u₀.xmm sixteenReg = wordsOf 16
  low : u₀.xmm lowReg = wordsOf 0xFF

/-- The vector registers the rows write. -/
def rowXRegs : List XReg := [kReg, tmp, tmp2, mEven, mOdd, .xmm8, .xmm9, .xmm10, .xmm11]

/-- After `r` rows. -/
structure RowInv (sch : Reg) (S : Addr) (x : Byte) (j : Nat) (u₀ : State) (r : Nat) (u : State) : Prop where
  le : r ≤ 16
  r8 : u.gpr .r8 = BitVec.ofNat 64 (16 * r)
  r9 : u.gpr .r9 = BitVec.ofNat 64 (16 - r)
  k : u.xmm kReg = rowK r
  acc : ∀ b < 4, u.xmm (accReg b) = scanAcc (pl S j b u₀.mem) x.toNat r
  xmm : ∀ d, d ∉ rowXRegs → u.xmm d = u₀.xmm d
  gpr : ∀ g, g ≠ .r8 → g ≠ .r9 → u.gpr g = u₀.gpr g
  eq : u = { u₀ with gpr := u.gpr, xmm := u.xmm, cf := u.cf, zf := u.zf, sf := u.sf, of := u.of }

theorem rowK_succ (r : Nat) : XBinOp.eval .paddw (rowK r) (wordsOf 16) = rowK (r + 1) :=
  ext_word fun w hw => by
    rw [word_paddw _ _ hw, rowK, rowK, wordsOf, word_ofWords _ hw, word_ofWords _ hw, word_ofWords _ hw,
      BitVec.ofNat_add_ofNat]
    congr 1; omega_arith

theorem ea_row (t : State) (sch : Reg) (S : Addr) (j b r : Nat) (h1 : t.gpr sch = S)
    (h2 : t.gpr .r8 = BitVec.ofNat 64 (16 * r)) :
    t.ea (rowMem sch j b) = S + BitVec.ofNat 64 (planeOff j b + 16 * r) := by
  simp only [State.ea, rowMem, h1, h2, BitVec.mul_one, Rc2.X86_64.offset_nat]
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_comm]

/-- After the masks and the planes `< b` of a row. -/
structure PlaneInv (sch : Reg) (S : Addr) (x : Byte) (j : Nat) (u₀ : State) (r : Nat) (u t : State)
    (mE mO : BitVec 128) (b : Nat) : Prop where
  eq : t = { u with xmm := t.xmm }
  mE : t.xmm mEven = mE
  mO : t.xmm mOdd = mO
  done : ∀ b' < b, t.xmm (accReg b') = scanAcc (pl S j b' u₀.mem) x.toNat (r + 1)
  todo : ∀ b', b ≤ b' → b' < 4 → t.xmm (accReg b') = scanAcc (pl S j b' u₀.mem) x.toNat r
  keep : ∀ d, d ∉ rowXRegs → t.xmm d = u.xmm d
  k : t.xmm kReg = rowK r

theorem plane_step {sch : Reg} {S : Addr} {x : Byte} {j : Nat} {u₀ : State} (E : ScanEnv sch S x j u₀)
    {r : Nat} (hr : r < 16) {u : State} (I : RowInv sch S x j u₀ r u) {mE mO : BitVec 128}
    (hE : ∀ w < 8, word mE w = if x.toNat = 16 * r + 2 * w then BitVec.allOnes 16 else 0)
    (hO : ∀ w < 8, word mO w = if x.toNat = 16 * r + 2 * w + 1 then BitVec.allOnes 16 else 0)
    {b : Nat} (hb : b < 4) {t : State} (P : PlaneInv sch S x j u₀ r u t mE mO b) :
    ∃ t', runBlock isa (plane sch j b) t = some t' ∧ PlaneInv sch S x j u₀ r u t' mE mO (b + 1) := by
  have hg : t.gpr = u.gpr := by rw [P.eq]
  have hm : t.mem = u₀.mem := by rw [P.eq, I.eq]
  have ea := ea_row t sch S j b r (by rw [hg, I.gpr _ E.ne8 E.ne9, E.hsch]) (by rw [hg, I.r8])
  have hoff : planeOff j b + 16 * r + 16 ≤ 4096 := by have := E.j4; unfold planeOff; omega_arith
  have hR : InRegions (t.rd ++ t.wr) (t.ea (rowMem sch j b)) 16 := by
    rw [ea, show t.rd = u₀.rd by rw [P.eq, I.eq], show t.wr = u₀.wr by rw [P.eq, I.eq]]
    exact E.rd _ hoff
  obtain ⟨t', run, hacc, keep, e'⟩ := plane_run t sch j hb hR
  obtain ⟨n1, n2, n3, n4, n5, n6, -⟩ := accReg_ne b hb
  refine ⟨t', run, ⟨by rw [e', P.eq], ?_, ?_, fun b' hb' => ?_, fun b' h1 h2 => ?_, fun d hd => ?_, ?_⟩⟩
  · rw [keep _ (by decide) (by decide) (Ne.symm n3), P.mE]
  · rw [keep _ (by decide) (by decide) (Ne.symm n4), P.mO]
  · by_cases h : b' = b
    · subst h
      rw [hacc, P.todo _ (Nat.le_refl _) hb, P.mE, P.mO,
        show t.xmm lowReg = wordsOf 0xFF by rw [P.keep _ (by decide), I.xmm _ (by decide), E.low]]
      refine row_acc _ x _ _ _ (fun e he => ?_) hE hO
      rw [ea, byte_readW128 _ _ he, hm, pl, Offset.add_add, Nat.add_assoc]
    · have ne : accReg b' ≠ accReg b := by
        have : ∀ a < 4, ∀ c < 4, a ≠ c → accReg a ≠ accReg c := by decide
        exact this _ (by omega_arith) _ hb h
      rw [keep _ (fun e => by obtain ⟨-, -⟩ := accReg_ne b' (by omega_arith); exact (accReg_ne b' (by omega_arith)).1 e)
        (fun e => (accReg_ne b' (by omega_arith)).2.1 e) ne]
      exact P.done _ (by omega_arith)
  · have ne : accReg b' ≠ accReg b := by
      have : ∀ a < 4, ∀ c < 4, a ≠ c → accReg a ≠ accReg c := by decide
      exact this _ h2 _ hb (by omega_arith)
    rw [keep _ (accReg_ne b' h2).1 (accReg_ne b' h2).2.1 ne]
    exact P.todo _ (by omega_arith) h2
  · have : d ≠ tmp ∧ d ≠ tmp2 ∧ d ≠ accReg b := by
      refine ⟨fun e => hd (by subst e; decide), fun e => hd (by subst e; decide), fun e => hd ?_⟩
      subst e
      have : ∀ c < 4, accReg c ∈ rowXRegs := by decide
      exact this b hb
    rw [keep _ this.1 this.2.1 this.2.2, P.keep _ hd]
  · rw [keep _ (by decide) (by decide) (Ne.symm n6), P.k]

/-- The end of a row. -/
theorem rowTail_run (t : State) :
    ∃ t', runBlock isa [bin .paddw kReg sixteenReg, .alu .add .r8 (.imm 16), .alu .sub .r9 (.imm 1)] t = some t' ∧
      t'.xmm = (t.setXmm kReg (XBinOp.eval .paddw (t.xmm kReg) (t.xmm sixteenReg))).xmm ∧
      t'.gpr .r8 = t.gpr .r8 + 16 ∧ t'.gpr .r9 = t.gpr .r9 - 1 ∧ t'.zf = some (t.gpr .r9 - 1 == 0) ∧
      (∀ g, g ≠ .r8 → g ≠ .r9 → t'.gpr g = t.gpr g) ∧
      t' = { t with gpr := t'.gpr, xmm := t'.xmm, cf := t'.cf, zf := t'.zf, sf := t'.sf, of := t'.of } := by
  let t₁ := (XOp.bin .paddw kReg sixteenReg).exec t
  let i16 : BitVec 64 := BitVec.signExtend 64 (16 : BitVec 32)
  let i1 : BitVec 64 := BitVec.signExtend 64 (1 : BitVec 32)
  let a8 := t₁.gpr .r8 + i16
  let t₂ := (arithFlags t₁ a8 (decide (2 ^ 64 ≤ (t₁.gpr .r8).toNat + i16.toNat))
    (addOverflow (t₁.gpr .r8) i16 a8)).setReg .r8 a8
  let a9 := t₂.gpr .r9 - i1
  let t₃ := (arithFlags t₂ a9 (decide ((t₂.gpr .r9).toNat < i1.toNat)) (subOverflow (t₂.gpr .r9) i1 a9)).setReg .r9 a9
  have g1 : t₁.gpr = t.gpr := rfl
  have h29 : t₂.gpr .r9 = t.gpr .r9 := by simp only [t₂, gpr_setReg_of_ne _ _ (show Reg.r9 ≠ Reg.r8 by decide), gpr_arithFlags, g1]
  refine ⟨t₃, ?_, rfl, ?_, ?_, ?_, fun g h8 h9 => ?_, ?_⟩
  · simp only [bin, runBlock_cons, runStep_some, exec, execAlu, readSrc, Option.bind_some, runBlock_nil]
    rfl
  · simp only [t₃, gpr_setReg_of_ne _ _ (show Reg.r8 ≠ Reg.r9 by decide), gpr_arithFlags, t₂, gpr_setReg_self, a8, g1]
    rfl
  · simp only [t₃, gpr_setReg_self, a9, h29]
    rfl
  · simp only [t₃, zf_setReg, zf_arithFlags, a9, h29]
    rfl
  · simp only [t₃, t₂, gpr_setReg_of_ne _ _ h9, gpr_setReg_of_ne _ _ h8, gpr_arithFlags, g1]
  · simp only [t₃, t₂, t₁, XOp.exec, State.setReg, State.setXmm, arithFlags, State.setFlags]

theorem row_run {sch : Reg} {S : Addr} {x : Byte} {j : Nat} {u₀ : State} (E : ScanEnv sch S x j u₀)
    {r : Nat} (hr : r < 16) {u : State} (I : RowInv sch S x j u₀ r u) :
    ∃ u', runBlock isa (row sch j) u = some u' ∧ RowInv sch S x j u₀ (r + 1) u' ∧
      u'.zf = some (BitVec.ofNat 64 (16 - (r + 1)) == 0) := by
  obtain ⟨u₁, r₁, hE, hO, k₁, e₁⟩ := masks_run u x hr I.k (by rw [I.xmm _ (by decide), E.idx])
    (by rw [I.xmm _ (by decide), E.ones])
  have P0 : PlaneInv sch S x j u₀ r u u₁ (u₁.xmm mEven) (u₁.xmm mOdd) 0 := by
    refine ⟨e₁, rfl, rfl, fun _ h => absurd h (by omega_arith), fun b' _ h => ?_, fun d hd => ?_, ?_⟩
    · rw [k₁ _ (accReg_ne b' h).2.2.1 (accReg_ne b' h).2.2.2.1]; exact I.acc b' h
    · exact k₁ d (fun e => hd (e ▸ by decide)) (fun e => hd (e ▸ by decide))
    · rw [k₁ _ (by decide) (by decide)]; exact I.k
  obtain ⟨p1, rp1, P1⟩ := plane_step E hr I hE hO (b := 0) (by decide) P0
  obtain ⟨p2, rp2, P2⟩ := plane_step E hr I hE hO (b := 1) (by decide) P1
  obtain ⟨p3, rp3, P3⟩ := plane_step E hr I hE hO (b := 2) (by decide) P2
  obtain ⟨p4, rp4, P4⟩ := plane_step E hr I hE hO (b := 3) (by decide) P3
  have g4 : p4.gpr = u.gpr := by rw [P4.eq]
  have s4 : p4.xmm sixteenReg = wordsOf 16 := by rw [P4.keep _ (by decide), I.xmm _ (by decide), E.sixteen]
  obtain ⟨v, rv, xv, r8v, r9v, zv, gv, ev⟩ := rowTail_run p4
  refine ⟨v, ?_, ⟨by omega_arith, ?_, ?_, ?_, fun b hb => ?_, fun d hd => ?_, fun g h8 h9 => ?_, ?_⟩, ?_⟩
  · rw [row, List.append_assoc]
    refine cat_run r₁ (cat_run (a := (List.range 4).flatMap (plane sch j)) ?_ rv)
    show runBlock isa (plane sch j 0 ++ (plane sch j 1 ++ (plane sch j 2 ++ (plane sch j 3 ++ [])))) u₁ = _
    exact cat_run rp1 (cat_run rp2 (cat_run rp3 (cat_run rp4 runBlock_nil)))
  · rw [r8v, g4, I.r8]; apply BitVec.eq_of_toNat_eq; simp; omega_arith
  · rw [r9v, g4, I.r9]; apply BitVec.eq_of_toNat_eq; simp; omega_arith
  · rw [xv, xmm_setXmm_self, P4.k, s4, rowK_succ]
  · rw [xv, xmm_setXmm_of_ne _ _ (accReg_ne b hb).2.2.2.2.2.1, P4.done b hb]
  · rw [xv, xmm_setXmm_of_ne _ _ (show d ≠ kReg from fun e => hd (by rw [e]; decide)), P4.keep d hd, I.xmm d hd]
  · rw [gv g h8 h9, g4, I.gpr g h8 h9]
  · rw [ev, P4.eq, I.eq]
  · rw [zv, g4, I.r9]; congr 2; apply BitVec.eq_of_toNat_eq; simp; omega_arith


end VG.Proof.Blowfish.X86_64

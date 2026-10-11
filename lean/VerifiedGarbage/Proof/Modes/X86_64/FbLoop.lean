import VerifiedGarbage.Proof.Modes.X86_64.CbcEncLoop
import VerifiedGarbage.Proof.Modes.Fb
import VerifiedGarbage.Impl.Modes.X86_64.Fb
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep

/-!
# OFB and CFB on x86-64, for any core: the data loop

`fbOp_wp`: the mode's step after `crypt` (`fbOp`) XORs the buffer's first
block into the data's block and makes the buffer the next input block
(`fbByte`), each a `copyN_wp` or `xorN_wp`. `fbBlock_wp`: one iteration
enciphers the input block `Iⱼ` in the buffer (`BlockSpec.crypt_wp`), makes
block `j` of the data its output (`fbOut`) and the buffer `Iⱼ₊₁` (`fbIn`).
Blocks are `8 bw` bytes.
-/

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64
open VG.Impl.Modes (FbMode)
open VG.Impl.Aes.X86_64 (sb movR movS st)
open VG.Spec.Aes (bytesAt)

variable {c : Core}

/-- The step after `crypt`, on the data's block at `A` (in `dataReg`) and the
buffer's first block at `T`. -/
theorem fbOp_wp (mo : FbMode) {s : State} {A T : Addr} (hA : s.gpr c.dataReg = A)
    (hT : s.gpr sb + BitVec.ofNat 64 (8 * c.buf) = T) (da : c.dataReg ≠ .rax)
    (wA : ∀ w < c.bw, InRegions s.wr (A + BitVec.ofNat 64 (8 * w)) 8)
    (wT : ∀ w < c.bw, InRegions s.wr (T + BitVec.ofNat 64 (8 * w)) 8)
    (sep : Region.Disjoint ⟨A, 8 * c.bw⟩ ⟨T, 8 * c.bw⟩) (fit : 8 * c.bw ≤ 2 ^ 64) :
    WP isa (.block (c.fbOp mo)) s fun s' => (∀ x, x ≠ .rax → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ (∀ u < 8 * c.bw, s'.mem (A + BitVec.ofNat 64 u) =
        s.mem (A + BitVec.ofNat 64 u) ^^^ s.mem (T + BitVec.ofNat 64 u)) ∧
      (∀ u < 8 * c.bw, s'.mem (T + BitVec.ofNat 64 u) =
        fbByte mo (s.mem (T + BitVec.ofNat 64 u)) (s.mem (A + BitVec.ofNat 64 u))) ∧
      Frame [⟨A, 8 * c.bw⟩, ⟨T, 8 * c.bw⟩] s.mem s'.mem := by
  have p0 : ∀ X : Addr, X + BitVec.ofNat 64 0 = X := fun X => by simp
  have hx : NPre c.bw s .rax c.dataReg sb 0 (8 * c.buf) A T :=
    ⟨by rw [hA, p0], hT, Ne.symm da, by decide, wA, fun w hw => inRd (wT w hw), sep, fit⟩
  have fA : ∀ {m : Mem} {f : Nat → Byte}, Frame [⟨A, 8 * c.bw⟩, ⟨T, 8 * c.bw⟩] m (over m A (8 * c.bw) f) :=
    (over_frame _ _ _ _).sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩
  have fT : ∀ {m : Mem} {f : Nat → Byte}, Frame [⟨A, 8 * c.bw⟩, ⟨T, 8 * c.bw⟩] m (over m T (8 * c.bw) f) :=
    (over_frame _ _ _ _).sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩
  cases mo
  · refine WP.mono (xorN_wp hx) fun s₁ h₁ => ⟨h₁.regs, h₁.rd, h₁.wr, fun u hu => ?_, fun u hu => ?_, ?_⟩
    · rw [h₁.mem, over_at hu fit]
    · rw [h₁.mem, over_sep sep hu fit]; rfl
    · rw [h₁.mem]; exact fA
  · refine WP.block_append (WP.mono (xorN_wp hx) fun s₁ h₁ => ?_)
    have hy : NPre c.bw s₁ .rax sb c.dataReg (8 * c.buf) 0 T A :=
      ⟨by rw [h₁.regs _ (by decide)]; exact hT, by rw [h₁.regs _ da, hA, p0], by decide, Ne.symm da,
        fun w hw => by rw [h₁.wr]; exact wT w hw, fun w hw => by rw [h₁.rd, h₁.wr]; exact inRd (wA w hw),
        sep.symm, fit⟩
    refine WP.mono (copyN_wp hy) fun s₂ h₂ => ⟨fun x hx => by rw [h₂.regs x hx, h₁.regs x hx],
      by rw [h₂.rd, h₁.rd], by rw [h₂.wr, h₁.wr], fun u hu => ?_, fun u hu => ?_, ?_⟩
    · rw [h₂.mem, over_sep sep.symm hu fit, h₁.mem, over_at hu fit]
    · rw [h₂.mem, over_at hu fit, h₁.mem, over_at hu fit]; rfl
    · rw [h₂.mem, h₁.mem]; exact fA.trans fT
  · refine WP.block_append (WP.mono (xorN_wp hx) fun s₁ h₁ => ?_)
    have hy : NPre c.bw s₁ .rax sb c.dataReg (8 * c.buf) 0 T A :=
      ⟨by rw [h₁.regs _ (by decide)]; exact hT, by rw [h₁.regs _ da, hA, p0], by decide, Ne.symm da,
        fun w hw => by rw [h₁.wr]; exact wT w hw, fun w hw => by rw [h₁.rd, h₁.wr]; exact inRd (wA w hw),
        sep.symm, fit⟩
    refine WP.mono (xorN_wp hy) fun s₂ h₂ => ⟨fun x hx => by rw [h₂.regs x hx, h₁.regs x hx],
      by rw [h₂.rd, h₁.rd], by rw [h₂.wr, h₁.wr], fun u hu => ?_, fun u hu => ?_, ?_⟩
    · rw [h₂.mem, over_sep sep.symm hu fit, h₁.mem, over_at hu fit]
    · rw [h₂.mem, over_at hu fit, h₁.mem, over_at hu fit, over_sep sep hu fit]
      exact xor_xor_cancel _ _
    · rw [h₂.mem, h₁.mem]; exact fA.trans fT

/-- A block of scalar instructions keeps the vector registers. -/
theorem runBlock_vec : ∀ {is : List Instr}, is.all scalarI = true → ∀ {s s' : State},
    runBlock isa is s = some s' → s'.xmm = s.xmm
  | [], _, _, _, h => by cases h; rfl
  | i :: is, hs, s, s', h => by
    obtain ⟨s₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
    simp only [List.all_cons, Bool.and_eq_true] at hs
    rw [runBlock_vec hs.2 h₂, (exec_vec hs.1 h₁).1]

theorem copyW_scal (t rd rs : Reg) (od os w : Nat) : (copyW t rd rs od os w).all scalarI = true := rfl

theorem xorW_scal (t rd rs : Reg) (od os w : Nat) : (xorW t rd rs od os w).all scalarI = true := rfl

theorem flatMap_scal {f : Nat → List Instr} (h : ∀ w, (f w).all scalarI = true) (k : Nat) :
    ((List.range k).flatMap f).all scalarI = true := by
  simp only [List.all_flatMap, List.all_eq_true]
  intro w _ i hi
  exact List.all_eq_true.mp (h w) i hi

/-- Every execution of `p` keeps the IV's address, in `ivX`: the modes'
requirement of a core's `prepare` and `crypt`. Scalar code meets it
(`keepsIv_of_scal`); other code may save and restore `ivX` around its own. -/
def KeepsIv (p : Prog isa) : Prop := ∀ s t s', Exec isa p s t s' → s'.xmm Core.ivX = s.xmm Core.ivX

theorem keepsIv_of_scal {p : Prog isa} (h : scalCode p = true) : KeepsIv p :=
  fun _ _ _ e => congrFun (exec_scal e h).1 _

theorem WP.keepIv {p : Prog isa} (h : KeepsIv p) {s : State} {Q : State → Prop} (w : WP isa p s Q) :
    WP isa p s fun t => Q t ∧ t.xmm Core.ivX = s.xmm Core.ivX :=
  let ⟨t, s', e, q⟩ := w
  ⟨t, s', e, q, h _ _ _ e⟩

/-- The step after `crypt` is scalar. -/
theorem fbOp_scal (c : Core) (mo : FbMode) : scalCode (.block (c.fbOp mo)) = true := by
  simp only [scalCode]
  cases mo
  · exact flatMap_scal (xorW_scal _ _ _ _ _) _
  · simp only [Core.fbOp, List.all_append, Bool.and_eq_true]
    exact ⟨flatMap_scal (xorW_scal _ _ _ _ _) _, flatMap_scal (copyW_scal _ _ _ _ _) _⟩
  · simp only [Core.fbOp, List.all_append, Bool.and_eq_true]
    exact ⟨flatMap_scal (xorW_scal _ _ _ _ _) _, flatMap_scal (xorW_scal _ _ _ _ _) _⟩

/-- The data loop, before block `j`; `m₀` is the memory on entry, `iv` the
IV. -/
structure FInv (cs : BlockSpec c) (mo : FbMode) (s₀ : State) (m₀ : Mem) (B D : Addr) (n : Nat) (k : cs.Key)
    (iv : List Byte) (j : Nat) (s : State) : Prop where
  base : s.gpr sb = B
  rsp : s.gpr .rsp = s₀.gpr .rsp
  ready : cs.Ready s B k
  saved : ∀ i < 7, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  dataR : s.gpr c.dataReg = D + BitVec.ofNat 64 (8 * c.bw * j)
  leftR : s.gpr c.leftReg = BitVec.ofNat 64 (n - j)
  lt : j < n
  buf : ∀ u < 8 * c.bw, s.mem (B + BitVec.ofNat 64 (8 * c.buf) + BitVec.ofNat 64 u) =
    (fbIn mo (8 * c.bw) (cs.cipher k) m₀ D iv j).getD u 0
  data : ∀ q < n, ∀ r < 8 * c.bw, s.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r)) =
    if q < j then (fbOut mo (8 * c.bw) (cs.cipher k) m₀ D iv q).getD r 0
    else m₀ (D + BitVec.ofNat 64 (8 * c.bw * q + r))
  frame : Frame [⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  xmm : s.xmm Core.ivX = s₀.xmm Core.ivX

/-- The data loop, done. -/
structure FDone (cs : BlockSpec c) (mo : FbMode) (s₀ : State) (m₀ : Mem) (B D : Addr) (n : Nat) (k : cs.Key)
    (iv : List Byte) (s : State) : Prop where
  base : s.gpr sb = B
  rsp : s.gpr .rsp = s₀.gpr .rsp
  saved : ∀ i < 7, s.mem.readW (wordAddr B (c.slots + i)) 64 = s₀.mem.readW (wordAddr B (c.slots + i)) 64
  buf : ∀ u < 8 * c.bw, s.mem (B + BitVec.ofNat 64 (8 * c.buf) + BitVec.ofNat 64 u) =
    (fbIn mo (8 * c.bw) (cs.cipher k) m₀ D iv n).getD u 0
  data : DInv (8 * c.bw) m₀ s.mem D n n (fbOut mo (8 * c.bw) (cs.cipher k) m₀ D iv)
  frame : Frame [⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  xmm : s.xmm Core.ivX = s₀.xmm Core.ivX

theorem fbBlock_wp (cs : BlockSpec c) (mo : FbMode) {s₀ : State} {m₀ : Mem} {B D : Addr} {n : Nat} {k : cs.Key}
    {iv : List Byte} (hiv : iv.length = 8 * c.bw) (hp : GPre c s₀ B D n (8 * c.bw)) (hsc : KeepsIv c.crypt)
    {j : Nat} {s : State} (hi : FInv cs mo s₀ m₀ B D n k iv j s) :
    WP isa (c.fbBlock mo) s fun s' => (s'.zf = some true ∧ FDone cs mo s₀ m₀ B D n k iv s') ∨
      (s'.zf = some false ∧ FInv cs mo s₀ m₀ B D n k iv (j + 1) s') := by
  have hL := cs.layout
  have hsm := hL.small
  have hroom := hL.room
  have hbuf := hL.buf_le
  have hG0 := hL.G_pos
  have hbw0 := hL.bw_pos
  have hbw2 := hL.bw_le
  have hfit := hp.scr.fit
  have hfitD := hp.fitD
  have hj := hi.lt
  have hL0 : 0 < 8 * c.bw := by omega
  have hGb : c.bw ≤ c.bw * c.G := Nat.le_mul_of_pos_right _ hG0
  have hLG : 8 * c.bw ≤ 8 * c.bw * c.G := Nat.le_mul_of_pos_right _ hG0
  have hLn : 8 * c.bw * n = 8 * (c.bw * n) := Nat.mul_assoc _ _ _
  have h8n : 8 * n ≤ 8 * c.bw * n := Nat.mul_le_mul_right n (by omega)
  have hjl := idx_lt (L := 8 * c.bw) hj
  have hj1 : 8 * c.bw * (j + 1) = 8 * c.bw * j + 8 * c.bw := Nat.mul_succ _ _
  obtain ⟨hregs, hdl⟩ := regsOk_ne cs.regs_ok
  obtain ⟨da, -, -, -, -, dsb, dsp, -⟩ := hregs c.dataReg List.mem_cons_self
  obtain ⟨la, -, -, -, -, lsb, lsp, -⟩ := hregs c.leftReg (List.mem_cons_of_mem _ List.mem_cons_self)
  have hn64 : 8 * c.bw * n ≤ 2 ^ 64 := by omega
  let ciph := cs.cipher k
  let A := D + BitVec.ofNat 64 (8 * c.bw * j)
  let T := B + BitVec.ofNat 64 (8 * c.buf)
  have hwS : (⟨B, 8 * c.ctrSlots⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.scr.wr
  have hwD : (⟨D, 8 * c.bw * n⟩ : Region) ∈ s.wr := by rw [hi.wr]; exact hp.dat
  have subT : Region.Sub ⟨T, 8 * c.bw⟩ ⟨B, 8 * c.ctrSlots⟩ :=
    VG.Offset.sub_base B (by simp only [Core.ctrSlots]; omega)
  have subTbuf : Region.Sub ⟨T, 8 * c.bw⟩ (blkRegion c B) := Region.sub_prefix hLG
  have subCore : Region.Sub (coreRegion c B) ⟨B, 8 * c.ctrSlots⟩ :=
    Region.sub_prefix (by simp only [Core.ctrSlots]; omega)
  have subA : Region.Sub ⟨A, 8 * c.bw⟩ ⟨D, 8 * c.bw * n⟩ := VG.Offset.sub_base D hjl
  have dDS : ∀ {r : Region}, Region.Sub r ⟨B, 8 * c.ctrSlots⟩ → Region.Disjoint ⟨D, 8 * c.bw * n⟩ r :=
    fun h => hp.sep.sub_right h
  have dAT : Region.Disjoint ⟨A, 8 * c.bw⟩ ⟨T, 8 * c.bw⟩ := (dDS subT).sub_left subA
  have hw : ∀ w, 8 * c.bw * j + 8 * w = 8 * (c.bw * j + w) := fun w => by rw [Nat.mul_add, Nat.mul_assoc]
  have hbj : ∀ w < c.bw, c.bw * j + w < c.bw * n := fun w hw' => by have := idx_lt (L := c.bw) hj; omega
  have inT : ∀ w < c.bw, InRegions s.wr (T + BitVec.ofNat 64 (8 * w)) 8 := fun w hw' =>
    ⟨_, hwS, by rw [addr_add]; exact VG.Offset.contains_base B (by simp only [Core.ctrSlots]; omega) (by omega)⟩
  have inA : ∀ w < c.bw, InRegions s.wr (A + BitVec.ofNat 64 (8 * w)) 8 := fun w hw' =>
    ⟨_, hwD, by rw [addr_add, hw]; exact VG.Offset.contains_base D (by have := hbj w hw'; omega) (by have := hbj w hw'; omega)⟩
  have hqr : ∀ {q r}, q < n → r < 8 * c.bw → 8 * c.bw * q + r < 8 * c.bw * n := fun hq hr => by
    have := idx_lt (L := 8 * c.bw) hq; omega
  -- Enciphered.
  unfold Core.fbBlock
  refine WP.seq (WP.mono (WP.keepIv hsc (cs.crypt_wp hi.base ⟨hwS, hfit⟩ hi.ready))
    fun s₂ ⟨⟨base₂, rsp₂, dr₂, lr₂, ready₂, f₂, ks₂, rd₂, wr₂⟩, x₂⟩ => ?_)
  have eT : blkAddr c B 0 = T := by simp only [blkAddr, T, Nat.mul_zero, Nat.add_zero]
  have hin : bytesAt s.mem T (8 * c.bw) = fbIn mo (8 * c.bw) ciph m₀ D iv j := by
    apply List.ext_getElem (by
      simp only [bytesAt, List.length_map, List.length_range]; rw [fbIn_length (cs.cipher_len k) m₀ D hiv])
    intro u h1 _
    have hu : u < 8 * c.bw := by simpa [bytesAt] using h1
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    rw [hi.buf u hu, List.getElem_eq_getD 0]
  have E₂ : ∀ u < 8 * c.bw, s₂.mem (T + BitVec.ofNat 64 u) = (ciph (fbIn mo (8 * c.bw) ciph m₀ D iv j)).getD u 0 :=
    fun u hu => by rw [← bytesAt_getD s₂.mem T hu, ← eT, ks₂ 0 hG0, eT, hin]
  have D₂ : ∀ q < n, ∀ r < 8 * c.bw, s₂.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r)) =
      s.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r)) := fun q hq r hr =>
    f₂.bytes (R := ⟨D, 8 * c.bw * n⟩) (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx; exact dDS subCore) hn64 (hqr hq hr)
  -- The step after `crypt`.
  have data₂ : s₂.gpr c.dataReg = A := by rw [dr₂, hi.dataR]
  refine WP.block_append (WP.mono (WP.vecKeep (fbOp_scal c mo) (fbOp_wp mo data₂ (by rw [base₂]) da
    (fun w hw' => by rw [wr₂]; exact inA w hw') (fun w hw' => by rw [wr₂]; exact inT w hw') dAT (by omega)))
    fun s₃a ⟨⟨g₃a, rd₃a, wr₃a, mA₃, mT₃, f₃a⟩, x₃a, _⟩ => ?_)
  obtain ⟨s₃b, e₃b, a₃b, o₃b, m₃b, rd₃b, wr₃b⟩ := addImm_ok s₃a c.dataReg (BitVec.ofNat 32 (8 * c.bw))
  obtain ⟨s₃, e₃, l₃, z₃, o₃, m₃, rd₃, wr₃⟩ := subImm_ok s₃b c.leftReg 1
  refine WP.of_runBlock ⟨s₃, by
    rw [Core.fbNext, show ([.alu .add c.dataReg (.imm (BitVec.ofNat 32 (8 * c.bw))), .alu .sub c.leftReg (.imm 1)] :
      List Instr) = [.alu .add c.dataReg (.imm (BitVec.ofNat 32 (8 * c.bw)))] ++ [.alu .sub c.leftReg (.imm 1)] from rfl,
      runBlock_app, e₃b, Option.bind_some, e₃], ?_⟩
  have keep₃ : ∀ x, x ≠ .rax → x ≠ c.dataReg → x ≠ c.leftReg → s₃.gpr x = s₂.gpr x := fun x h1 h2 h3 => by
    rw [o₃ x h3, o₃b x h2, g₃a x h1]
  have left₂ : s₃b.gpr c.leftReg = BitVec.ofNat 64 (n - j) := by
    rw [o₃b _ (Ne.symm hdl), g₃a _ la, lr₂, hi.leftR]
  have left₃ : s₃.gpr c.leftReg = BitVec.ofNat 64 (n - (j + 1)) := by
    rw [l₃, left₂, show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
      VG.Offset.ofNat_sub_ofNat (by omega), show n - j - 1 = n - (j + 1) by omega]
  have hz₃ : s₃.zf = some (decide (j + 1 = n)) := by
    rw [z₃, left₂, show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
      VG.Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]
    simp only [Option.some.injEq, decide_eq_decide]; omega
  have hAL : A + BitVec.ofNat 64 (8 * c.bw) = D + BitVec.ofNat 64 (8 * c.bw * (j + 1)) := by rw [addr_add, hj1]
  have data₃ : s₃.gpr c.dataReg = D + BitVec.ofNat 64 (8 * c.bw * (j + 1)) := by
    rw [o₃ _ hdl, a₃b, g₃a _ da, data₂, signExtend_small (by omega), hAL]
  have mem₃ : s₃.mem = s₃a.mem := by rw [m₃, m₃b]
  have xmm₃ : s₃.xmm Core.ivX = s₀.xmm Core.ivX := by
    rw [runBlock_vec rfl e₃, runBlock_vec rfl e₃b, x₃a, x₂, hi.xmm]
  have base₃ : s₃.gpr sb = B := by rw [keep₃ _ (by decide) (Ne.symm dsb) (Ne.symm lsb), base₂]
  have rsp₃ : s₃.gpr .rsp = s₀.gpr .rsp := by
    rw [keep₃ _ (by decide) (Ne.symm dsp) (Ne.symm lsp), rsp₂, hi.rsp]
  have rd₃' : s₃.rd = s₀.rd := by rw [rd₃, rd₃b, rd₃a, rd₂, hi.rd]
  have wr₃' : s₃.wr = s₀.wr := by rw [wr₃, wr₃b, wr₃a, wr₂, hi.wr]
  have f₃ : Frame [⟨A, 8 * c.bw⟩, ⟨T, 8 * c.bw⟩] s₂.mem s₃.mem := by rw [mem₃]; exact f₃a
  -- The slots.
  have slotOut : ∀ i < 7, ∀ {R : Region}, (Region.Sub R ⟨D, 8 * c.bw * n⟩ ∨ R = ⟨T, 8 * c.bw⟩ ∨
      R = coreRegion c B) → Region.Disjoint ⟨wordAddr B (c.slots + i), 8⟩ R := fun i hi7 R hR => by
    rcases hR with h | rfl | rfl
    · exact ((dDS (VG.Offset.sub_base B (show 8 * (c.slots + i) + 8 ≤ 8 * c.ctrSlots by
        simp only [Core.ctrSlots]; omega))).sub_left h).symm
    · exact VG.Offset.disjoint B (.inr (by omega)) (by omega) (by omega)
    · exact VG.Offset.disjoint_base B (by omega) (by omega)
  have saved₃ : ∀ i < 7, s₃.mem.readW (wordAddr B (c.slots + i)) 64 =
      s₀.mem.readW (wordAddr B (c.slots + i)) 64 := fun i hi7 => by
    rw [← hi.saved i hi7]
    refine (f₃.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact slotOut i hi7 (.inl subA)
      · exact slotOut i hi7 (.inr (.inl rfl))) (by decide)).trans ?_
    exact f₂.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact slotOut i hi7 (.inr (.inr rfl))) (by decide)
  have fr₃ : Frame [⟨B, 8 * c.ctrSlots⟩, ⟨D, 8 * c.bw * n⟩] s₀.mem s₃.mem :=
    hi.frame.trans ((f₂.sub fun r hr => ⟨_, List.mem_cons_self, by
        simp only [List.mem_singleton] at hr; subst hr; exact subCore⟩).trans
      (f₃.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, subA⟩
        · exact ⟨_, List.mem_cons_self, subT⟩))
  have ready₃ : cs.Ready s₃ B k := cs.ready_frame ready₂ f₃ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl ((dDS subCore).sub_left subA).symm
    · exact .inr subTbuf) fun r hr => by
    obtain ⟨h1, -, -, -, -, h6, h7⟩ := of_not_modeRegs hr; exact keep₃ r h1 h6 h7
  -- The buffer and the data.
  have mA : ∀ u < 8 * c.bw, s.mem (A + BitVec.ofNat 64 u) = m₀ (A + BitVec.ofNat 64 u) := fun u hu => by
    rw [addr_add, hi.data j hj u hu, ite_eq_right (Nat.lt_irrefl _)]
  have D₂' : ∀ u < 8 * c.bw, s₂.mem (A + BitVec.ofNat 64 u) = s.mem (A + BitVec.ofNat 64 u) := fun u hu => by
    rw [addr_add]; exact D₂ j hj u hu
  have buf₃ : ∀ u < 8 * c.bw, s₃.mem (T + BitVec.ofNat 64 u) =
      (fbIn mo (8 * c.bw) ciph m₀ D iv (j + 1)).getD u 0 := fun u hu => by
    rw [mem₃, mT₃ u hu, E₂ u hu, fbIn_succ_getD mo (cs.cipher_len k) m₀ D iv j hu, ← addr_add,
      ← mA u hu, D₂' u hu]
  have data₃' : ∀ q < n, ∀ r < 8 * c.bw, s₃.mem (D + BitVec.ofNat 64 (8 * c.bw * q + r)) =
      if q < j + 1 then (fbOut mo (8 * c.bw) ciph m₀ D iv q).getD r 0
      else m₀ (D + BitVec.ofNat 64 (8 * c.bw * q + r)) := fun q hq r hr => by
    by_cases hqj : q = j
    · rw [ite_eq_left (by omega), hqj, fbOut_getD mo (cs.cipher_len k) m₀ D iv j hr, mem₃, ← addr_add, mA₃ r hr,
        E₂ r hr, D₂' r hr, mA r hr]
    · have out : ∀ R ∈ [(⟨A, 8 * c.bw⟩ : Region), ⟨T, 8 * c.bw⟩],
          ¬ R.Contains (D + BitVec.ofNat 64 (8 * c.bw * q + r)) 1 := fun R hR => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
        rcases hR with rfl | rfl
        · have := hqr hq hr
          refine not_contains_off D ?_ (by omega) hL0 (by omega)
          rcases Nat.lt_or_gt_of_ne hqj with h | h
          · have := idx_lt (L := 8 * c.bw) h; omega
          · have := idx_lt (L := 8 * c.bw) h; omega
        · exact fun hc => dDS subT _ (VG.Offset.contains_base D (by have := hqr hq hr; omega) (by have := hqr hq hr; omega)) hc
      rw [mem₃, f₃a _ out, D₂ q hq r hr, hi.data q hq r hr]
      by_cases h3 : q < j
      · rw [ite_eq_left h3, ite_eq_left (by omega)]
      · rw [ite_eq_right h3, ite_eq_right (by omega)]
  by_cases hdone : j + 1 = n
  · exact .inl ⟨by rw [hz₃, decide_eq_true hdone], base₃, rsp₃, saved₃, by rw [← hdone]; exact buf₃,
      dinv_of_blocks hL0 fun q hq r hr => by rw [data₃' q hq r hr, hdone], fr₃, rd₃', wr₃', xmm₃⟩
  · exact .inr ⟨by rw [hz₃, decide_eq_false hdone], base₃, rsp₃, ready₃, saved₃, data₃, left₃, by omega, buf₃,
      data₃', fr₃, rd₃', wr₃', xmm₃⟩

/-- The data loop. -/
theorem fbLoop_wp (cs : BlockSpec c) (mo : FbMode) {s₀ : State} {m₀ : Mem} {B D : Addr} {n : Nat} {k : cs.Key}
    {iv : List Byte} (hiv : iv.length = 8 * c.bw) (hp : GPre c s₀ B D n (8 * c.bw)) (hsc : KeepsIv c.crypt)
    {s : State} (hi : FInv cs mo s₀ m₀ B D n k iv 0 s) :
    WP isa (.loop (c.fbBlock mo) .ne) s (FDone cs mo s₀ m₀ B D n k iv) := by
  refine WP.loop (M := isa) (fun m s => ∃ j, m = n - j ∧ FInv cs mo s₀ m₀ B D n k iv j s) (fun m s hs => ?_) n s
    ⟨0, by simp, hi⟩
  obtain ⟨j, rfl, hj⟩ := hs
  refine WP.mono (fbBlock_wp cs mo hiv hp hsc hj) fun s' h => ?_
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨by simp [X86_64.eval, z], d⟩
  · exact .inr ⟨by simp [X86_64.eval, z], n - (j + 1), by have := d.lt; have := hj.lt; omega, j + 1, rfl, d⟩

end VG.Proof.Modes.X86_64

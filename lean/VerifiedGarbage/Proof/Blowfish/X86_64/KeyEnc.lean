import VerifiedGarbage.Proof.Blowfish.X86_64.KeyStore

/-!
# Key expansion: the 521 encryptions

Each encryption runs ECB's rounds under the schedule as written so far,
and its output replaces the next two entries: the P-array's, as words
(`encryptP_run`), then the S-boxes', a byte per plane (`encryptS_run`).
-/

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Blowfish.X86_64 VG.Spec.Blowfish VG.Proof.Blowfish

/-- What the encryptions need, of the state they start in. -/
structure EncEnv (S B : Addr) (s₀ : State) : Prop where
  rdx : s₀.gpr .rdx = S
  rcx : s₀.gpr .rcx = B
  wrS : SchedW S s₀
  wrB : InRegions s₀.wr B 32
  sep : (⟨S, 4168⟩ : Region).Disjoint ⟨B, 32⟩
  fitS : S.toNat + 4168 ≤ 2 ^ 64
  fitB : B.toNat + 32 ≤ 2 ^ 64
  ones : s₀.xmm onesReg = wordsOf 1
  sixteen : s₀.xmm sixteenReg = wordsOf 16
  low : s₀.xmm lowReg = wordsOf 0xFF

/-- The registers an encryption and its stores write. -/
abbrev EncRegs (g : Reg) : Prop :=
  g ≠ .rax ∧ g ≠ .rsi ∧ g ≠ .rdi ∧ g ≠ .r8 ∧ g ≠ .r9 ∧ g ≠ .r10 ∧ g ≠ .r11

/-- After `j` encryptions. -/
structure EncInv (key : List Byte) (S B : Addr) (s₀ : State) (j : Nat) (u : State) : Prop where
  le : j ≤ 521
  sched : scheduleAt u.mem S = (ksIter key j).1
  xl : dword (u.xmm xL) 0 = (ksIter key j).2.1
  xr : dword (u.xmm xR) 0 = (ksIter key j).2.2
  gpr : ∀ g, EncRegs g → u.gpr g = s₀.gpr g
  xmm : ∀ d, d ∉ cXRegs → u.xmm d = s₀.xmm d
  frame : Frame [⟨S, 4168⟩, ⟨B, 32⟩] s₀.mem u.mem
  eq : UpdM s₀ u

theorem EncInv.rdx {key : List Byte} {S B : Addr} {s₀ : State} (E : EncEnv S B s₀) {j : Nat} {u : State}
    (I : EncInv key S B s₀ j u) : u.gpr .rdx = S := (I.gpr _ (by decide)).trans E.rdx

theorem EncInv.rcx {key : List Byte} {S B : Addr} {s₀ : State} (E : EncEnv S B s₀) {j : Nat} {u : State}
    (I : EncInv key S B s₀ j u) : u.gpr .rcx = B := (I.gpr _ (by decide)).trans E.rcx

theorem EncInv.wrS {key : List Byte} {S B : Addr} {s₀ : State} (E : EncEnv S B s₀) {j : Nat} {u : State}
    (I : EncInv key S B s₀ j u) : SchedW S u := fun off n h => by rw [I.eq]; exact E.wrS off n h

theorem EncInv.wrB {key : List Byte} {S B : Addr} {s₀ : State} (E : EncEnv S B s₀) {j : Nat} {u : State}
    (I : EncInv key S B s₀ j u) : InRegions u.wr B 32 := by rw [I.eq]; exact E.wrB

/-- The encryption of the last output. -/
theorem enc_cipher {key : List Byte} {S B : Addr} {s₀ : State} (E : EncEnv S B s₀) {j : Nat} {u : State}
    (I : EncInv key S B s₀ j u) :
    WP isa (cipher .rdx true) u (fun u' =>
      dword (u'.xmm xR) 0 = (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).1 ∧
      dword (u'.xmm xL) 0 = (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).2 ∧
      COnly u u') := by
  have W := I.wrS E
  have CE : CipherEnv .rdx S u :=
    ⟨⟨I.rdx E, by decide, by decide, by decide, fun off h => inRegions_append_right (W off 16 (by omega)),
      by rw [I.xmm _ (by decide), E.ones], by rw [I.xmm _ (by decide), E.sixteen],
      by rw [I.xmm _ (by decide), E.low]⟩, by decide, by decide,
      fun i hi => inRegions_append_right (W _ 4 (by omega))⟩
  refine WP.mono (cipher_run CE true) fun u' ⟨h1, h2, O⟩ => ⟨?_, ?_, O⟩
  · rw [h1, I.sched, I.xl, I.xr]; rfl
  · rw [h2, I.sched, I.xl, I.xr]; rfl

theorem ksIter_step (key : List Byte) {j : Nat} (hj : j < 521) :
    ksIter key (j + 1) =
      (((ksIter key j).1.set (2 * j) (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).1
          (by omega)).set (2 * j + 1)
          (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).2 (by omega),
        (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).1,
        (encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2).2) := by
  rw [ksIter_succ, ksStep, set!_eq_set _ (by omega), set!_eq_set _ (by omega)]

/-- The scratch writes leave the schedule as it was. -/
theorem scheduleAt_scratch {S B : Addr} (sep : (⟨S, 4168⟩ : Region).Disjoint ⟨B, 32⟩)
    (m : Mem) (x y : BitVec 128) :
    scheduleAt ((m.writeW (B + BitVec.ofNat 64 0) x).writeW (B + BitVec.ofNat 64 16) y) S = scheduleAt m S :=
  scheduleAt_eq_of_frame S (rs := [⟨B, 32⟩])
    (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base B (by omega) (by omega))).writeW
      (List.mem_singleton_self _) _ (Offset.contains_base B (by omega) (by omega)))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact sep)

theorem readW_scratch0 {B : Addr} (m : Mem) (x y : BitVec 128) :
    ((m.writeW (B + BitVec.ofNat 64 0) x).writeW (B + BitVec.ofNat 64 16) y).readW (B + BitVec.ofNat 64 0) 32 =
      dword x 0 := by
  rw [Mem.readW_writeW_sep (Offset.sep B (by omega) (by omega) (by omega)) (by decide), readW_writeW128_0]

theorem readW_scratch16 {B : Addr} (m : Mem) (x y : BitVec 128) :
    ((m.writeW (B + BitVec.ofNat 64 0) x).writeW (B + BitVec.ofNat 64 16) y).readW (B + BitVec.ofNat 64 16) 32 =
      dword y 0 := readW_writeW128_0 _ _ _

/-- `r11`'s low doubleword at `rdx + rdi + o`. -/
abbrev pStore (o : Nat) : Instr := .store32 { base := .rdx, index := some .rdi, disp := Int.ofNat o } .r11

theorem withMem_run {b : List Instr} {t : State} {M : Mem} (h : runBlock isa b t = some { t with mem := M }) :
    ∃ t', runBlock isa b t = some t' ∧ t'.mem = M ∧ t'.gpr = t.gpr ∧ t'.xmm = t.xmm ∧ t'.rd = t.rd ∧
      t'.wr = t.wr ∧ UpdM t t' := ⟨_, h, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The working space's word at `B + o` apart from the schedule's at `S + e`. -/
theorem sep_scratch {S B : Addr} (sep : (⟨S, 4168⟩ : Region).Disjoint ⟨B, 32⟩) {o e : Nat} (ho : o + 4 ≤ 32)
    (he : e + 4 ≤ 4168) : Mem.Sep (B + BitVec.ofNat 64 o) (32 / 8) (S + BitVec.ofNat 64 e) (32 / 8) :=
  sep_of_disjoint ((sep.symm.sub_left (Offset.sub_base B ho)).sub_right (Offset.sub_base S he))

/-- An encryption's output into P-array entries `2 j` and `2 j + 1`. -/
theorem encP_step {key : List Byte} {S B : Addr} {s₀ : State} (E : EncEnv S B s₀) {j : Nat} (hj : j < 9)
    {u : State} (I : EncInv key S B s₀ j u) (hrdi : u.gpr .rdi = BitVec.ofNat 64 (8 * j))
    (hrsi : u.gpr .rsi = BitVec.ofNat 64 (9 - j)) :
    WP isa (.seq (cipher .rdx true) (.block (storeP ++ ([.alu .add .rdi (.imm 8), .alu .sub .rsi (.imm 1)] : List Instr)))) u
      (fun u' => EncInv key S B s₀ (j + 1) u' ∧ u'.gpr .rdi = BitVec.ofNat 64 (8 * (j + 1)) ∧
        u'.gpr .rsi = BitVec.ofNat 64 (9 - (j + 1)) ∧ u'.zf = some (BitVec.ofNat 64 (9 - (j + 1)) == 0)) := by
  have fitS := E.fitS
  apply WP.seq
  refine WP.mono (enc_cipher E I) fun u₁ ⟨h1, h2, O⟩ => ?_
  let out := encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2
  have wr₁ : u₁.wr = u.wr := by rw [O.upd]
  have g₁ : ∀ g, g ≠ .rax → g ≠ .r8 → g ≠ .r9 → g ≠ .r10 → g ≠ .r11 → u₁.gpr g = u.gpr g := O.gpr
  have rcx₁ : u₁.gpr .rcx = B := (g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans (I.rcx E)
  have rdx₁ : u₁.gpr .rdx = S := (g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans (I.rdx E)
  have rdi₁ : u₁.gpr .rdi = BitVec.ofNat 64 (8 * j) :=
    (g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hrdi
  have W : SchedW S u₁ := fun off n h => by rw [wr₁]; exact I.wrS E off n h
  -- the halves to the working space
  let M₂ := (u₁.mem.writeW (B + BitVec.ofNat 64 0) (u₁.xmm xR)).writeW (B + BitVec.ofNat 64 16) (u₁.xmm xL)
  obtain ⟨u₂, r₂, m₂, gp₂, x₂, rd₂, wr₂, up₂⟩ := withMem_run (scratchOut_run rcx₁ (by rw [wr₁]; exact I.wrB E))
  have rB : ∀ o, o + 4 ≤ 32 → InRegions (u₂.rd ++ u₂.wr) (B + BitVec.ofNat 64 o) 4 := fun o ho => by
    rw [rd₂, wr₂, wr₁, show u₁.rd = u.rd by rw [O.upd]]
    exact inRegions_append_right (inRegions_off (I.wrB E) ho)
  obtain ⟨u₃, r₃, a₃, x₃, k₃, g₃, up₃⟩ := take_run (t := u₂) (by rw [gp₂]; exact rcx₁) (rB 0 (by omega)) xL
  have A₃ : (u₃.gpr .r11).setWidth 32 = out.1 := by
    rw [a₃, setWidth_setWidth_32, m₂, readW_scratch0, h1]
  have m₃ : u₃.mem = M₂ := by rw [up₃]; exact m₂
  have wr₃ : u₃.wr = u.wr := by rw [up₃]; rw [wr₂]; exact wr₁
  have rd₃ : u₃.rd = u.rd := by rw [up₃]; rw [rd₂]; rw [O.upd]
  have G₃ : ∀ g, g ≠ .r11 → u₃.gpr g = u₁.gpr g := fun g h => by rw [g₃ _ h, gp₂]
  let M₄ := M₂.writeW (S + BitVec.ofNat 64 (pOff + 8 * j)) ((u₃.gpr .r11).setWidth 32)
  obtain ⟨u₄, r₄, m₄, gp₄, x₄, rd₄, wr₄, up₄⟩ := withMem_run (b := [pStore pOff]) (M := M₄)
    (by rw [store32_idx_run (S := S) (d := 8 * j) (o := pOff) ((G₃ _ (by decide)).trans rdx₁)
      ((G₃ _ (by decide)).trans rdi₁) (by rw [wr₃]; exact I.wrS E _ _ (by simp only [pOff]; omega)), m₃])
  have rB₄ : InRegions (u₄.rd ++ u₄.wr) (B + BitVec.ofNat 64 16) 4 := by
    rw [rd₄, wr₄, rd₃, wr₃]; exact inRegions_append_right (inRegions_off (I.wrB E) (by omega))
  obtain ⟨u₅, r₅, a₅, x₅, k₅, g₅, up₅⟩ := take_run (t := u₄) (o := 16)
    ((congrFun gp₄ .rcx).trans ((G₃ _ (by decide)).trans rcx₁)) rB₄ xR
  have B₅ : (u₅.gpr .r11).setWidth 32 = out.2 := by
    rw [a₅, setWidth_setWidth_32, m₄]
    rw [Mem.readW_writeW_sep (sep_scratch (o := 16) (e := pOff + 8 * j) E.sep (by omega) (by simp only [pOff]; omega)) (by decide), readW_scratch16, h2]
  have m₅ : u₅.mem = M₄ := by rw [up₅]; exact m₄
  have wr₅ : u₅.wr = u.wr := by rw [up₅]; rw [wr₄]; exact wr₃
  have G₅ : ∀ g, g ≠ .r11 → u₅.gpr g = u₁.gpr g := fun g h => by rw [g₅ _ h, gp₄]; exact G₃ _ h
  let M₆ := M₄.writeW (S + BitVec.ofNat 64 (pOff + 4 + 8 * j)) ((u₅.gpr .r11).setWidth 32)
  obtain ⟨u₆, r₆, m₆, gp₆, x₆, rd₆, wr₆, up₆⟩ := withMem_run (b := [pStore (pOff + 4)]) (M := M₆)
    (by rw [store32_idx_run (S := S) (d := 8 * j) (o := pOff + 4) ((G₅ _ (by decide)).trans rdx₁)
      ((G₅ _ (by decide)).trans rdi₁) (by rw [wr₅]; exact I.wrS E _ _ (by simp only [pOff]; omega)), m₅])
  obtain ⟨u₇, e₇, a₇, k₇, x₇, up₇⟩ := add_imm_run u₆ .rdi 8
  obtain ⟨u₈, e₈, a₈, z₈, k₈, x₈, up₈⟩ := sub_imm_run u₇ .rsi 1
  have mem₈ : u₈.mem = M₆ := by rw [up₈, up₇]; exact m₆
  have xmm₈ : u₈.xmm = u₅.xmm := by rw [x₈, x₇, x₆]
  have G₈ : ∀ g, g ≠ .rdi → g ≠ .rsi → g ≠ .r11 → u₈.gpr g = u₁.gpr g := fun g h1 h2 h3 => by
    rw [k₈ _ h2, k₇ _ h1, gp₆]; exact G₅ g h3
  refine WP.of_runBlock ⟨u₈, ?_, ⟨by omega, ?_, ?_, ?_, fun g hg => ?_, fun d hd => ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [storeP, List.append_assoc]
    refine cat_run r₂ ?_
    rw [show ([.mov32 .r11 (.mem (mem .rcx 0)), .xop (.movq xL .r11), pStore pOff,
        .mov32 .r11 (.mem (mem .rcx 16)), .xop (.movq xR .r11), pStore (pOff + 4)] ++
        [.alu .add .rdi (.imm 8), .alu .sub .rsi (.imm 1)] : List Instr) =
        ([.mov32 .r11 (.mem (mem .rcx 0)), .xop (.movq xL .r11)] : List Instr) ++ ([pStore pOff] ++
        (([.mov32 .r11 (.mem (mem .rcx 16)), .xop (.movq xR .r11)] : List Instr) ++ ([pStore (pOff + 4)] ++
        ([.alu .add .rdi (.imm 8), .alu .sub .rsi (.imm 1)] : List Instr)))) from rfl]
    refine cat_run r₃ (cat_run r₄ (cat_run r₅ (cat_run r₆ ?_)))
    rw [runBlock_cons, e₇, runStep_some, runBlock_cons, e₈, runStep_some, runBlock_nil]
  · rw [mem₈, ksIter_step key (by omega)]
    rw [show M₆ = M₄.writeW _ ((u₅.gpr .r11).setWidth 32) from rfl, B₅, show pOff + 4 + 8 * j = 4096 + 4 * (2 * j + 1) by simp only [pOff]; omega,
      scheduleAt_writeW_P _ _ (by omega)]
    rw [show M₄ = M₂.writeW _ ((u₃.gpr .r11).setWidth 32) from rfl, A₃, show pOff + 8 * j = 4096 + 4 * (2 * j) by simp only [pOff]; omega, scheduleAt_writeW_P _ _ (by omega),
      scheduleAt_scratch E.sep, show u₁.mem = u.mem by rw [O.upd], I.sched]
  · rw [xmm₈, k₅ _ (by decide), x₄, x₃, m₂, readW_scratch0, h1, ksIter_step key (by omega)]
  · have b := B₅
    rw [a₅, setWidth_setWidth_32] at b
    rw [xmm₈, x₅, b, ksIter_step key (by omega)]
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hg
    rw [G₈ g h3 h2 h7, g₁ g h1 h4 h5 h6 h7]; exact I.gpr g ⟨h1, h2, h3, h4, h5, h6, h7⟩
  · have n0 : d ≠ xL := fun e => hd (by rw [e]; decide)
    have n1 : d ≠ xR := fun e => hd (by rw [e]; decide)
    rw [xmm₈, k₅ _ n1, x₄, k₃ _ n0, x₂, O.xmm d hd, I.xmm d hd]
  · rw [mem₈]
    have hS : ∀ e, e + 4 ≤ 4168 → (⟨S, 4168⟩ : Region).Contains (S + BitVec.ofNat 64 e) (32 / 8) :=
      fun e he => Offset.contains_base S he (by omega)
    have mS : (⟨S, 4168⟩ : Region) ∈ [⟨S, 4168⟩, ⟨B, 32⟩] := List.mem_cons_self
    have mB : (⟨B, 32⟩ : Region) ∈ [⟨S, 4168⟩, ⟨B, 32⟩] := List.mem_cons_of_mem _ List.mem_cons_self
    refine ((((I.frame.trans ?_).writeW mB _ (Offset.contains_base B (by omega) (by omega))).writeW mB _
      (Offset.contains_base B (by omega) (by omega))).writeW mS _ (hS _ (by simp only [pOff]; omega))).writeW mS _
      (hS _ (by simp only [pOff]; omega))
    rw [show u₁.mem = u.mem by rw [O.upd]]; exact Frame.refl _ _
  · exact UpdM.trans (UpdM.of_upd up₈) (UpdM.trans (UpdM.of_upd up₇) (UpdM.trans up₆
      (UpdM.trans (UpdM.of_upd up₅) (UpdM.trans up₄ (UpdM.trans (UpdM.of_upd up₃)
        (UpdM.trans up₂ (UpdM.trans (UpdM.of_upd O.upd) I.eq)))))))
  · rw [k₈ _ (by decide), a₇, gp₆, G₅ _ (by decide), rdi₁]
    apply BitVec.eq_of_toNat_eq; simp; omega
  · rw [a₈, k₇ _ (by decide), gp₆, G₅ _ (by decide),
      g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide), hrsi]
    apply BitVec.eq_of_toNat_eq; simp; omega
  · rw [z₈, k₇ _ (by decide), gp₆, G₅ _ (by decide),
      g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide), hrsi,
      show BitVec.ofNat 64 (9 - j) - BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 (9 - (j + 1)) from by
        apply BitVec.eq_of_toNat_eq; simp; omega]

/-- The offset of S-box entry `sDone j`'s first plane. -/
def sOff (j : Nat) : Nat := 1024 * (sDone j / 256) + sDone j % 256

theorem sOff_entry {j : Nat} (h9 : 9 ≤ j) (hj : j < 521) {b k : Nat} (hk : k < 2) :
    256 * b + k + sOff j = entryOff (2 * j + k) b := by
  rw [← entryOff_sbox h9 hj k hk, sOff]; omega

theorem sOff_lt {j : Nat} (h9 : 9 ≤ j) (hj : j < 521) : sOff j ≤ 3326 := by
  unfold sOff sDone; omega

theorem sOff_succ {j : Nat} (h9 : 9 ≤ j) :
    sOff (j + 1) = if (sOff j + 2) % 256 = 0 then sOff j + 2 + 768 else sOff j + 2 := by
  unfold sOff sDone; split <;> omega

theorem and_255 {x : Nat} (h : x < 2 ^ 64) : (BitVec.ofNat 64 x &&& BitVec.ofNat 64 255).toNat = x % 256 := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    show (255 % 2 ^ 64) = 2 ^ 8 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]

theorem test_imm_run (t : State) (d : Reg) (v : BitVec 32) :
    ∃ t', exec (.alu .test d (.imm v)) t = some t' ∧ t'.zf = some ((t.gpr d &&& v.signExtend 64) == 0) ∧
      t'.gpr = t.gpr ∧ t'.xmm = t.xmm ∧ Upd t t' :=
  ⟨_, rfl, rfl, rfl, rfl, by unfold Upd; simp only [arithFlags, State.setFlags]⟩

/-- `storeEntry_run` at the offsets of entry `i`. -/
theorem storeEntry_at {t : State} {S : Addr} {d e i : Nat} (hS : t.gpr .rdx = S) (hd : t.gpr .rdi = BitVec.ofNat 64 d)
    (hoff : ∀ b < 4, 256 * b + e + d = entryOff i b)
    (hw : ∀ b < 4, InRegions t.wr (S + BitVec.ofNat 64 (entryOff i b)) 1) :
    ∃ t', runBlock isa (storeEntry e) t = some t' ∧
      t'.mem = (((t.mem.write (S + BitVec.ofNat 64 (entryOff i 0)) 1 (((t.gpr .r11).setWidth 32).extractLsb' 0 8)).write
        (S + BitVec.ofNat 64 (entryOff i 1)) 1 (((t.gpr .r11).setWidth 32).extractLsb' 8 8)).write
        (S + BitVec.ofNat 64 (entryOff i 2)) 1 (((t.gpr .r11).setWidth 32).extractLsb' 16 8)).write
        (S + BitVec.ofNat 64 (entryOff i 3)) 1 (((t.gpr .r11).setWidth 32).extractLsb' 24 8) ∧
      (∀ g, g ≠ .r11 → t'.gpr g = t.gpr g) ∧ t'.xmm = t.xmm ∧ UpdM t t' := by
  obtain ⟨t', r, m, g, x, u⟩ := storeEntry_run (e := e) hS hd fun b hb => by rw [hoff b hb]; exact hw b hb
  refine ⟨t', r, ?_, g, x, u⟩
  have h0 := hoff 0 (by decide)
  have h1 := hoff 1 (by decide)
  have h2 := hoff 2 (by decide)
  have h3 := hoff 3 (by decide)
  rw [m, show e + d = entryOff i 0 by omega, show 256 + e + d = entryOff i 1 by omega,
    show 512 + e + d = entryOff i 2 by omega, show 768 + e + d = entryOff i 3 by omega]

/-- The four byte writes of an entry stay in the schedule. -/
theorem frame_bytes {rs : List Region} {m m' : Mem} (h : Frame rs m m') {S : Addr} (hS : (⟨S, 4168⟩ : Region) ∈ rs)
    {i : Nat} (hi : i < 1042) (w : Word) :
    Frame rs m ((((m'.write (S + BitVec.ofNat 64 (entryOff i 0)) 1 (w.extractLsb' 0 8)).write
        (S + BitVec.ofNat 64 (entryOff i 1)) 1 (w.extractLsb' 8 8)).write
        (S + BitVec.ofNat 64 (entryOff i 2)) 1 (w.extractLsb' 16 8)).write
        (S + BitVec.ofNat 64 (entryOff i 3)) 1 (w.extractLsb' 24 8)) :=
  have c : ∀ b < 4, (⟨S, 4168⟩ : Region).Contains (S + BitVec.ofNat 64 (entryOff i b)) 1 := fun b hb =>
    Offset.contains_base S (by have := entryOff_lt hi hb; omega) (by have := entryOff_lt hi hb; omega)
  (((h.write hS _ (c 0 (by decide))).write hS _ (c 1 (by decide))).write hS _ (c 2 (by decide))).write hS _
    (c 3 (by decide))

/-- An encryption's output into S-box entries `2 j` and `2 j + 1` (`sDone j`
and the next of the S-boxes). -/
theorem encS_step {key : List Byte} {S B : Addr} {s₀ : State} (E : EncEnv S B s₀) {j : Nat} (h9 : 9 ≤ j)
    (hj : j < 521) {u : State} (I : EncInv key S B s₀ j u) (hrdi : u.gpr .rdi = BitVec.ofNat 64 (sOff j))
    (hrsi : u.gpr .rsi = BitVec.ofNat 64 (521 - j)) :
    WP isa (.seq (cipher .rdx true)
        (.seq (.block (storeS ++ ([.alu .add .rdi (.imm 2), .alu .test .rdi (.imm 255)] : List Instr)))
          (.seq (.ite .e (.block [.alu .add .rdi (.imm 768)]) (.block [])) (.block [.alu .sub .rsi (.imm 1)])))) u
      (fun u' => EncInv key S B s₀ (j + 1) u' ∧ u'.gpr .rdi = BitVec.ofNat 64 (sOff (j + 1)) ∧
        u'.gpr .rsi = BitVec.ofNat 64 (521 - (j + 1)) ∧ u'.zf = some (BitVec.ofNat 64 (521 - (j + 1)) == 0)) := by
  have fitS := E.fitS
  have so := sOff_lt h9 hj
  apply WP.seq
  refine WP.mono (enc_cipher E I) fun u₁ ⟨h1, h2, O⟩ => ?_
  let out := encryptWords (ksIter key j).1 (ksIter key j).2.1 (ksIter key j).2.2
  have wr₁ : u₁.wr = u.wr := by rw [O.upd]
  have rd₁ : u₁.rd = u.rd := by rw [O.upd]
  have g₁ : ∀ g, g ≠ .rax → g ≠ .r8 → g ≠ .r9 → g ≠ .r10 → g ≠ .r11 → u₁.gpr g = u.gpr g := O.gpr
  have rcx₁ : u₁.gpr .rcx = B := (g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans (I.rcx E)
  have rdx₁ : u₁.gpr .rdx = S := (g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans (I.rdx E)
  have rdi₁ : u₁.gpr .rdi = BitVec.ofNat 64 (sOff j) :=
    (g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hrdi
  have hw : ∀ (t : State), t.wr = u.wr → ∀ k < 2, ∀ b < 4,
      InRegions t.wr (S + BitVec.ofNat 64 (entryOff (2 * j + k) b)) 1 := fun t ht k hk b hb => by
    rw [ht]; exact I.wrS E _ _ (by have := entryOff_lt (i := 2 * j + k) (by omega) hb; omega)
  have hoff : ∀ k < 2, ∀ b < 4, 256 * b + k + sOff j = entryOff (2 * j + k) b :=
    fun k hk b _ => sOff_entry h9 hj hk
  -- the halves to the working space
  let M₂ := (u₁.mem.writeW (B + BitVec.ofNat 64 0) (u₁.xmm xR)).writeW (B + BitVec.ofNat 64 16) (u₁.xmm xL)
  obtain ⟨u₂, r₂, m₂, gp₂, x₂, rd₂, wr₂, up₂⟩ := withMem_run (scratchOut_run rcx₁ (by rw [wr₁]; exact I.wrB E))
  have rB : ∀ o, o + 4 ≤ 32 → InRegions (u.rd ++ u.wr) (B + BitVec.ofNat 64 o) 4 := fun o ho =>
    inRegions_append_right (inRegions_off (I.wrB E) ho)
  obtain ⟨u₃, r₃, a₃, x₃, k₃, g₃, up₃⟩ := take_run (t := u₂) (B := B) (o := 0) (by rw [gp₂]; exact rcx₁)
    (by rw [rd₂, wr₂, wr₁, rd₁]; exact rB 0 (by omega)) xL
  have A₃ : (u₃.gpr .r11).setWidth 32 = out.1 := by
    rw [a₃, setWidth_setWidth_32, m₂, readW_scratch0, h1]
  have m₃ : u₃.mem = M₂ := by rw [up₃]; exact m₂
  have wr₃ : u₃.wr = u.wr := by rw [up₃]; rw [wr₂]; exact wr₁
  have rd₃ : u₃.rd = u.rd := by rw [up₃]; rw [rd₂]; exact rd₁
  have G₃ : ∀ g, g ≠ .r11 → u₃.gpr g = u₁.gpr g := fun g h => by rw [g₃ _ h, gp₂]
  obtain ⟨u₄, r₄, m₄, G₄, x₄, up₄⟩ := storeEntry_at (e := 0) (i := 2 * j + 0) ((G₃ _ (by decide)).trans rdx₁)
    ((G₃ _ (by decide)).trans rdi₁) (fun b hb => hoff 0 (by decide) b hb) (hw u₃ wr₃ 0 (by decide))
  have wr₄ : u₄.wr = u.wr := by rw [up₄]; exact wr₃
  have rd₄ : u₄.rd = u.rd := by rw [up₄]; exact rd₃
  have f₄ : Frame [⟨S, 4168⟩] M₂ u₄.mem := by
    rw [m₄, m₃]; exact frame_bytes (Frame.refl _ _) (List.mem_singleton_self _) (by omega) _
  obtain ⟨u₅, r₅, a₅, x₅, k₅, g₅, up₅⟩ := take_run (t := u₄) (o := 16)
    ((G₄ _ (by decide)).trans ((G₃ _ (by decide)).trans rcx₁)) (by rw [rd₄, wr₄]; exact rB 16 (by omega)) xR
  have B₅ : (u₅.gpr .r11).setWidth 32 = out.2 := by
    rw [a₅, setWidth_setWidth_32,
      f₄.readW (r := ⟨B + BitVec.ofNat 64 16, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (E.sep.symm.sub_left (Offset.sub_base B (by omega)))) (by decide),
      readW_scratch16, h2]
  have wr₅ : u₅.wr = u.wr := by rw [up₅]; exact wr₄
  have G₅ : ∀ g, g ≠ .r11 → u₅.gpr g = u₁.gpr g := fun g h => by rw [g₅ _ h, G₄ _ h]; exact G₃ _ h
  obtain ⟨u₆, r₆, m₆, G₆, x₆, up₆⟩ := storeEntry_at (e := 1) (i := 2 * j + 1) ((G₅ _ (by decide)).trans rdx₁)
    ((G₅ _ (by decide)).trans rdi₁) (fun b hb => hoff 1 (by decide) b hb) (hw u₅ wr₅ 1 (by decide))
  obtain ⟨u₇, e₇, a₇, k₇, x₇, up₇⟩ := add_imm_run u₆ .rdi 2
  obtain ⟨u₈, e₈, z₈, gp₈, xx₈, up₈⟩ := test_imm_run u₇ .rdi 255
  have G₈ : ∀ g, g ≠ .rdi → g ≠ .r11 → u₈.gpr g = u₁.gpr g := fun g h1 h2 => by
    rw [gp₈, k₇ _ h1, G₆ _ h2]; exact G₅ _ h2
  have rdi₈ : u₈.gpr .rdi = BitVec.ofNat 64 (sOff j + 2) := by
    rw [gp₈, a₇, G₆ _ (by decide), G₅ _ (by decide), rdi₁]
    exact BitVec.eq_of_toNat_eq (by simp)
  have mem₈ : u₈.mem = u₆.mem := by rw [show u₈.mem = u₇.mem by rw [up₈]]; rw [up₇]
  have xmm₈ : u₈.xmm = u₅.xmm := by rw [xx₈, x₇, x₆]
  have m₅ : u₅.mem = u₄.mem := by rw [up₅]
  have U₈ : UpdM u u₈ := UpdM.trans (UpdM.of_upd up₈) (UpdM.trans (UpdM.of_upd up₇) (UpdM.trans up₆
      (UpdM.trans (UpdM.of_upd up₅) (UpdM.trans up₄ (UpdM.trans (UpdM.of_upd up₃)
        (UpdM.trans up₂ (UpdM.of_upd O.upd)))))))
  -- the invariant, but for `rdi` and `rsi`
  have I₈ : ∀ v : State, UpdM u₈ v → v.mem = u₈.mem → v.xmm = u₈.xmm →
      (∀ g, g ≠ .rdi → g ≠ .rsi → v.gpr g = u₈.gpr g) → EncInv key S B s₀ (j + 1) v := by
    intro v uv mv xv gv
    refine ⟨by omega, ?_, ?_, ?_, fun g hg => ?_, fun d hd => ?_, ?_, uv.trans (U₈.trans I.eq)⟩
    · rw [mv, mem₈, m₆, scheduleAt_write_bytes _ _ (by omega), B₅, m₅, m₄,
        scheduleAt_write_bytes _ _ (by omega), A₃, m₃, scheduleAt_scratch E.sep,
        show u₁.mem = u.mem by rw [O.upd], I.sched, ksIter_step key (by omega)]
      rfl
    · rw [xv, xmm₈, k₅ _ (by decide), x₄, x₃, m₂, readW_scratch0, h1, ksIter_step key (by omega)]
    · have b := B₅
      rw [a₅, setWidth_setWidth_32] at b
      rw [xv, xmm₈, x₅, b, ksIter_step key (by omega)]
    · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hg
      rw [gv g h3 h2, G₈ g h3 h7, g₁ g h1 h4 h5 h6 h7]; exact I.gpr g ⟨h1, h2, h3, h4, h5, h6, h7⟩
    · have n0 : d ≠ xL := fun e => hd (by rw [e]; decide)
      have n1 : d ≠ xR := fun e => hd (by rw [e]; decide)
      rw [xv, xmm₈, k₅ _ n1, x₄, k₃ _ n0, x₂, O.xmm d hd, I.xmm d hd]
    · rw [mv, mem₈, m₆]
      have mS : (⟨S, 4168⟩ : Region) ∈ [⟨S, 4168⟩, ⟨B, 32⟩] := List.mem_cons_self
      have mB : (⟨B, 32⟩ : Region) ∈ [⟨S, 4168⟩, ⟨B, 32⟩] := List.mem_cons_of_mem _ List.mem_cons_self
      refine frame_bytes ?_ mS (by omega) _
      rw [m₅, m₄, m₃]
      refine frame_bytes ?_ mS (by omega) _
      refine ((I.frame.trans ?_).writeW mB _ (Offset.contains_base B (by omega) (by omega))).writeW mB _
        (Offset.contains_base B (by omega) (by omega))
      rw [show u₁.mem = u.mem by rw [O.upd]]; exact Frame.refl _ _
  have so' := sOff_succ h9 (j := j)
  apply WP.seq
  refine WP.of_runBlock ⟨u₈, ?_, ?_⟩
  · rw [storeS, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc]
    refine cat_run r₂ (cat_run r₃ (cat_run r₄ (cat_run r₅ (cat_run r₆ ?_))))
    rw [runBlock_cons, e₇, runStep_some, runBlock_cons, e₈, runStep_some, runBlock_nil]
  have zf₈ : isa.eval .e u₈ = some ((sOff j + 2) % 256 == 0) := by
    show u₈.zf = _
    rw [z₈, show u₇.gpr .rdi = u₈.gpr .rdi by rw [gp₈], rdi₈,
      show BitVec.signExtend 64 (255 : BitVec 32) = BitVec.ofNat 64 255 from rfl]
    congr 1
    by_cases h : (sOff j + 2) % 256 = 0
    · rw [beq_iff_eq.mpr h]; apply beq_iff_eq.mpr; apply BitVec.eq_of_toNat_eq; rw [and_255 (by omega), h]; rfl
    · rw [beq_eq_false_iff_ne.mpr h]; apply beq_eq_false_iff_ne.mpr; intro e
      have := congrArg BitVec.toNat e; rw [and_255 (by omega)] at this; exact h this
  apply WP.seq
  -- the next S-box, after its last entry
  have fin : ∀ v : State, UpdM u₈ v → v.mem = u₈.mem → v.xmm = u₈.xmm →
      (∀ g, g ≠ .rdi → v.gpr g = u₈.gpr g) → v.gpr .rdi = BitVec.ofNat 64 (sOff (j + 1)) →
      WP isa (.block [.alu .sub .rsi (.imm 1)]) v (fun u' => EncInv key S B s₀ (j + 1) u' ∧
        u'.gpr .rdi = BitVec.ofNat 64 (sOff (j + 1)) ∧ u'.gpr .rsi = BitVec.ofNat 64 (521 - (j + 1)) ∧
        u'.zf = some (BitVec.ofNat 64 (521 - (j + 1)) == 0)) := by
    intro v uv mv xv gv rv
    obtain ⟨w, e, a, z, k, x, up⟩ := sub_imm_run v .rsi 1
    have rsi₈ : v.gpr .rsi = BitVec.ofNat 64 (521 - j) := by
      rw [gv _ (by decide), G₈ _ (by decide) (by decide),
        g₁ _ (by decide) (by decide) (by decide) (by decide) (by decide), hrsi]
    have r : BitVec.ofNat 64 (521 - j) - BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 (521 - (j + 1)) := by
      apply BitVec.eq_of_toNat_eq; simp; omega
    refine WP.of_runBlock ⟨w, by rw [runBlock_cons, e, runStep_some, runBlock_nil],
      I₈ w ((UpdM.of_upd up).trans uv) (by rw [up]; exact mv) (by rw [x]; exact xv)
        (fun g h1 h2 => by rw [k _ h2]; exact gv g h1), by rw [k _ (by decide)]; exact rv,
      by rw [a, rsi₈, r], by rw [z, rsi₈, r]⟩
  apply WP.ite _ zf₈
  · intro h
    have h' : (sOff j + 2) % 256 = 0 := by simpa using h
    obtain ⟨v, e, a, k, x, up⟩ := add_imm_run u₈ .rdi 768
    refine WP.of_runBlock ⟨v, by rw [runBlock_cons, e, runStep_some, runBlock_nil],
      fin v (UpdM.of_upd up) (by rw [up]) x (fun g h1 => k g h1) ?_⟩
    rw [a, rdi₈, so', itT _ _ h']
    apply BitVec.eq_of_toNat_eq; simp
  · intro h
    have h' : ¬ (sOff j + 2) % 256 = 0 := by simpa using h
    refine WP.block_nil (fin u₈ (by unfold UpdM; rfl) rfl rfl (fun _ _ => rfl) ?_)
    rw [rdi₈, so', itF _ _ h']

end VG.Proof.Blowfish.X86_64

import VerifiedGarbage.Proof.Argon2.X86.Derive.FillPtr
import VerifiedGarbage.Proof.Framework.Omega

section

/-!
# Argon2 on x86 (32-bit): the new block

`fillCompress_ok`: G of the previous and reference blocks, to
`scratch + 4096`. `writeWords_ok`: its words to the current block, XORed
into the old ones after the first pass; `fillWrite_ok`: the current block
after the step, as `FillStep.update` has it.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd Fupd wp_movi wp_mov wp_add wp_addi wp_subi wp_sub wp_addm wp_cmpi wp_ldm wp_stm wp_andi
  wp_sbb_self wp_and wp_xor wp_xorm)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState compress xorBlock)
open VG.Proof.Argon2.X86 (blk ofWords blk_of_words)
open VG.Impl.Sha512.X86 (at_)
open VG.Impl.Argon2.X86.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  j1Off j2Off refLaneOff startOff countOff tmpOff curOff writeWord)

/-- Words of the memory matrix. -/
abbrev mw (s₀ : State) (m : Mem) (o : Nat) : BitVec 32 := m.readW (addr (memP s₀) o) 32

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem blocks22 : blocksN s₀ < 2 ^ 22 := by
  have hb := hp.blocks_lt
  omega

theorem mem_addr' {o : Nat} (ho : o < blocksN s₀ * 1024) : addr (memP s₀) o = memB s₀ + BitVec.ofNat 64 o :=
  addr_eq (by have := hp.mem_fits; omega)

/-- A word of the matrix after a store to another, or the same. -/
theorem mw_store (m : Mem) {a b : Nat} (ha : a + 4 ≤ blocksN s₀ * 1024) (hb : b + 4 ≤ blocksN s₀ * 1024)
    (h : a = b ∨ a + 4 ≤ b ∨ b + 4 ≤ a) (v : BitVec 32) :
    mw s₀ (m.writeW (addr (memP s₀) a) v) b = if a = b then v else mw s₀ m b := by
  have := blocks22 hp
  by_cases e : a = b
  · subst e; rw [ite_eq_left rfl]; exact Mem.readW_writeW_self32 _ _ _
  · rw [ite_eq_right e, mw, mw, mem_addr' hp (by omega), mem_addr' hp (by omega)]
    exact Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)

/-- The words of the current block, `n` of them written. -/
theorem writeWords_ok {s : State} (h : Inv s₀ s) {cur : Nat} (hc : cur < blocksN s₀) (xo : Bool)
    {P : BitVec 32} (hsi : s.gpr .esi = P) (hPfit : P.toNat + 1024 ≤ 2 ^ 32)
    (hPw : ∃ R ∈ [scrR s₀, memR s₀], ∃ off, P.setWidth 64 = R.base + BitVec.ofNat 64 off ∧ off + 1024 ≤ R.len)
    (hPC : Region.Disjoint ⟨P.setWidth 64, 1024⟩ ⟨matrixCell (memB s₀) cur, 1024⟩)
    (hdi : s.gpr .edi = memP s₀ + BitVec.ofNat 32 (cur * 1024)) :
    ∀ n ≤ 256, WP isa (.block ((List.range n).flatMap (writeWord xo))) s fun t =>
      Inv s₀ t ∧ (∀ r, r ≠ .eax → t.gpr r = s.gpr r) ∧
      Frame [⟨matrixCell (memB s₀) cur, 1024⟩] s.mem t.mem ∧
      ∀ i < 256, mw s₀ t.mem (cur * 1024 + 4 * i) = if i < n then
        (if xo then s.mem.readW (addr P (4 * i)) 32 ^^^ mw s₀ s.mem (cur * 1024 + 4 * i) else s.mem.readW (addr P (4 * i)) 32)
        else mw s₀ s.mem (cur * 1024 + 4 * i)
  | 0, _ => WP.block_nil ⟨h, fun _ _ => rfl, Frame.refl _ _, fun i _ => by rw [ite_eq_right (by omega)]⟩
  | n + 1, hn => by
    have hs := hp.scr_fits
    have hm := hp.mem_fits
    have hb := blocks22 hp
    have hc' : cur * 1024 + 1024 ≤ blocksN s₀ * 1024 := by omega
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append ((writeWords_ok h hc xo hsi hPfit hPw hPC hdi n (by omega)).mono
      fun t ⟨it, gt, ft, wt⟩ => ?_)
    have cell : matrixCell (memB s₀) cur = memB s₀ + BitVec.ofNat 64 (cur * 1024) := rfl
    -- The source word is kept: only the current block has been written.
    have eP : addr P (4 * n) = P.setWidth 64 + BitVec.ofNat 64 (4 * n) := addr_eq (by omega_using [hPfit, hn])
    have sw_t : t.mem.readW (addr P (4 * n)) 32 = s.mem.readW (addr P (4 * n)) 32 := by
      rw [eP]
      refine ft.readW (r := ⟨P.setWidth 64 + BitVec.ofNat 64 (4 * n), 4⟩) (Region.contains_self _ _)
        (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact hPC.sub_left (Offset.sub_base _ (by omega_using [hn]))
    have ea : addr (t.gpr .esi) (4 * n) = addr P (4 * n) := by
      rw [gt _ (by decide), hsi]
    have eb : addr (t.gpr .edi) (4 * n) = addr (memP s₀) (cur * 1024 + 4 * n) := by
      rw [gt _ (by decide), hdi, addr_shift]
    have b1 : cur * 1024 + 4 * n + 4 ≤ blocksN s₀ * 1024 := by omega_using [hc', hn]
    have b2 : cur * 1024 + 1024 < 2 ^ 64 := by omega_using [hc', hb]
    have inS : InRegions (t.rd ++ t.wr) (addr (t.gpr .esi) (4 * n)) 4 := by
      obtain ⟨R, hR, off, bR, lR⟩ := hPw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      have RW : R ∈ t.wr ∧ R.len ≤ 2 ^ 32 := by
        rw [it.wr]
        rcases hR with rfl | rfl
        · exact ⟨scr_mem hp, by show 16384 ≤ 2 ^ 32; decide⟩
        · exact ⟨mem_mem hp, by show blocksN s₀ * 1024 ≤ 2 ^ 32; omega_using [hm]⟩
      rw [ea, eP, bR, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact ⟨R, List.mem_append_right _ RW.1, Offset.contains_base _ (by omega_using [lR, hn])
        (by have := RW.2; omega_using [lR, hn, this])⟩
    have inMc : (memR s₀).Contains (addr (t.gpr .edi) (4 * n)) 4 := by
      rw [eb, mem_addr' hp (by omega_using [b1])]
      exact Offset.contains_base _ b1 (by omega_using [b1, hb])
    have inC : (⟨matrixCell (memB s₀) cur, 1024⟩ : Region).Contains (addr (t.gpr .edi) (4 * n)) 4 := by
      rw [eb, mem_addr' hp (by omega_using [b1]), cell]
      exact Offset.contains _ (by omega_using []) (by omega_using [hn]) b2
    have inM : InRegions t.wr (addr (t.gpr .edi) (4 * n)) 4 := ⟨memR s₀, by rw [it.wr]; exact mem_mem hp, inMc⟩
    -- The word.
    have fin : ∀ (v : BitVec 32) (u : State), u.mem = t.mem.writeW (addr (t.gpr .edi) (4 * n)) v →
        u.rd = t.rd → u.wr = t.wr → (∀ r, r ≠ .eax → u.gpr r = s.gpr r) →
        v = (if xo then s.mem.readW (addr P (4 * n)) 32 ^^^ mw s₀ s.mem (cur * 1024 + 4 * n)
          else s.mem.readW (addr P (4 * n)) 32) →
        Inv s₀ u ∧ (∀ r, r ≠ .eax → u.gpr r = s.gpr r) ∧
        Frame [⟨matrixCell (memB s₀) cur, 1024⟩] s.mem u.mem ∧
        ∀ i < 256, mw s₀ u.mem (cur * 1024 + 4 * i) = if i < n + 1 then
          (if xo then s.mem.readW (addr P (4 * i)) 32 ^^^ mw s₀ s.mem (cur * 1024 + 4 * i)
            else s.mem.readW (addr P (4 * i)) 32)
          else mw s₀ s.mem (cur * 1024 + 4 * i) := fun v u hm hrd hwr gu ev => by
      have fu : Frame [⟨matrixCell (memB s₀) cur, 1024⟩] s.mem u.mem := by
        rw [hm]; exact ft.writeW (List.mem_singleton_self _) v inC
      have iu : Inv s₀ u := it.step (by rw [gu _ (by decide), gt _ (by decide)])
        (by rw [gu _ (by decide), gt _ (by decide)]) hrd hwr
        (by rw [hm]; exact (Frame.refl _ _).writeW (r := memR s₀) (by simp) v inMc)
      refine ⟨iu, gu, fu, fun i hi => ?_⟩
      rw [hm, eb, mw_store hp _ b1 (by omega_using [hi, hc', hb]) (by omega_using []), wt i hi]
      by_cases e : i = n
      · subst e
        rw [ite_eq_left rfl, ite_eq_left (show i < i + 1 by omega_using []), ev]
      · rw [ite_eq_right (show ¬cur * 1024 + 4 * n = cur * 1024 + 4 * i by omega_using [e])]
        by_cases c : i < n
        · rw [ite_eq_left c, ite_eq_left (show i < n + 1 by omega_using [c])]
        · rw [ite_eq_right c, ite_eq_right (show ¬i < n + 1 by omega_using [c, e])]
    cases xo
    · simp only [writeWord, Bool.false_eq_true, ite_false, List.nil_append]
      refine wp_ldm rfl inS fun u₁ v₁ => ?_
      refine wp_stm (b := .edi) (v₁.other .edi (by decide)) (by rw [v₁.wr]; exact inM) fun u mu => WP.block_nil ?_
      refine fin _ u (by rw [mu.mem, v₁.mem]) (by rw [mu.rd, v₁.rd]) (by rw [mu.wr, v₁.wr])
        (fun r hr => by rw [mu.gpr, v₁.other r hr, gt r hr]) ?_
      simp only [Bool.false_eq_true, ite_false]
      rw [v₁.gpr, ea, sw_t]
    · simp only [writeWord, ite_true, List.cons_append, List.nil_append]
      refine wp_ldm rfl inS fun u₁ v₁ => ?_
      refine wp_xorm (b := .edi) (v₁.other .edi (by decide)) (by rw [v₁.rd, v₁.wr]; exact
        ⟨memR s₀, List.mem_append_right _ (by rw [it.wr]; exact mem_mem hp), inMc⟩) fun u₂ v₂ => ?_
      refine wp_stm (b := .edi) (by rw [v₂.other .edi (by decide), v₁.other .edi (by decide)])
        (by rw [v₂.wr, v₁.wr]; exact inM) fun u mu => WP.block_nil ?_
      refine fin _ u (by rw [mu.mem, v₂.mem, v₁.mem]) (by rw [mu.rd, v₂.rd, v₁.rd]) (by rw [mu.wr, v₂.wr, v₁.wr])
        (fun r hr => by rw [mu.gpr, v₂.other r hr, v₁.other r hr, gt r hr]) ?_
      simp only [ite_true]
      rw [v₂.gpr, v₁.gpr, v₁.mem, ea, sw_t, eb, ← mw, wt n (by omega_using [hn]),
        ite_eq_right (show ¬n < n by omega_using [])]

end

end VG.Proof.Argon2.X86.Derive

end

/-!
# Argon2 on x86 (32-bit): one block of the filling loops

`fillCompress_ok`: G of the previous and reference blocks to
`scratch + 4096`; `fillWrite_ok`: the current block, copied or XORed;
`fillBlock_ok`: the filling state after one block (`Spec.Argon2.fillBlock`).
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd Fupd wp_movi wp_mov wp_add wp_addi wp_subi wp_sub wp_addm wp_cmpi wp_ldm wp_stm wp_andi
  wp_sbb_self wp_and wp_xor wp_xorm)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState compress xorBlock)
open VG.Proof.Argon2.X86 (blk ofWords blk_of_words xor_words)
open VG.Impl.Argon2.X86.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  j1Off j2Off refLaneOff startOff countOff tmpOff curOff writeBlock)

theorem FS.of_upd {s₀ s t : State} {pass slice lane index ctr : Nat} {st : FillState} {r : Reg} {v : BitVec 32}
    (h : FS s₀ pass slice lane index ctr st s) (u : Upd s t r v) (h1 : r ≠ .esp) (h2 : r ≠ .ebp) :
    FS s₀ pass slice lane index ctr st t :=
  h.keep (h.inv.upd u h1 h2) (fun d _ => lw_mem u.mem d) (by rw [u.mem]) fun _ _ => by rw [u.mem]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem outside_work : Outside s₀ ⟨scrB s₀, 4096⟩ := by
  have := outside_scr hp (o := 0) (n := 4096) (.inl (by decide))
  simpa using this

/-- The locals are kept by writes outside them. -/
theorem lw_outside {s t : State} {rs : List Region} (f : Frame rs s.mem t.mem) (ho : ∀ r ∈ rs, Outside s₀ r)
    {d : Nat} (hd : d + 4 ≤ 144) : lw s₀ t d = lw s₀ s d :=
  f.readW (r := ⟨addr (E s₀) d, 4⟩) (Region.contains_self _ _)
    (fun r hr => (ho r hr).1.symm.sub_left (loc_word_sub hp hd)) (by decide)

/-- `fillCompress`: G of the previous and reference blocks, to `scratch + 4096`. -/
theorem fillCompress_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) {R : Nat} (hR : R < blocksN s₀)
    (htmp : lw s₀ s tmpOff = memP s₀ + BitVec.ofNat 32 (R * 1024)) :
    WP isa Impl.Argon2.X86.Derive.fillCompress s fun t => FS s₀ pass slice lane index ctr st t ∧
      (∀ d, d + 4 ≤ 144 → lw s₀ t d = lw s₀ s d) ∧
      blk t.mem (scrP s₀) 4096 = compress (blockAt s.mem (matrixCell (memB s₀) (lane * (prm s₀).laneLen +
        (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) % (prm s₀).laneLen)))
        (blockAt s.mem (matrixCell (memB s₀) R)) := by
  have L8 := laneLen_ge hp
  obtain ⟨cl, _⟩ := cell_fits hp hl (col := (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) %
    (prm s₀).laneLen) (Nat.mod_lt _ (by omega))
  unfold Impl.Argon2.X86.Derive.fillCompress Impl.Argon2.X86.Derive.compressCall
  refine WP.seq ((prevPointer_ok hp h.inv h.pr h.pos hl hs hi).mono fun s₁ ⟨a₁, k₁⟩ => ?_)
  generalize (lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index + (prm s₀).laneLen - 1) %
    (prm s₀).laneLen) = P at cl a₁ ⊢
  have h₁ := h.of_keep k₁
  refine WP.seq (wp_ldloc hp h₁.inv (d := tmpOff) (by decide) fun s₂ u₂ => ?_)
  have h₂ := h₁.of_upd u₂ (by decide) (by decide)
  refine wp_ldarg hp h₂.inv (i := 15) (by decide) fun s₃ u₃ => ?_
  have h₃ := h₂.of_upd u₃ (by decide) (by decide)
  refine wp_mov fun s₄ u₄ => ?_
  have h₄ := h₃.of_upd u₄ (by decide) (by decide)
  refine wp_addi fun s₅ u₅ => WP.block_nil ?_
  have h₅ := h₄.of_upd u₅ (by decide) (by decide)
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, k₁.mem]
  have ax : s₅.gpr .eax = memP s₀ + BitVec.ofNat 32 (P * 1024) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), a₁]
  have sx : s₅.gpr .esi = memP s₀ + BitVec.ofNat 32 (R * 1024) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, lw_mem k₁.mem, htmp]
  have dx : s₅.gpr .edx = scrP s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  have cx : s₅.gpr .ecx = scrP s₀ + BitVec.ofNat 32 4096 := by
    rw [u₅.gpr, u₄.gpr, u₃.gpr]; rfl
  refine ccall_ok hp h₅.inv dx (o := 4096) (by decide) (by decide) cx (by rw [ax]; exact .inl ⟨P, cl, rfl⟩)
    (by rw [sx]; exact .inl ⟨R, hR, rfl⟩) fun t it _ f post => ?_
  have ho : ∀ r ∈ [⟨scrB s₀ + BitVec.ofNat 64 4096, 1024⟩, ⟨scrB s₀, 4096⟩, callR s₀], Outside s₀ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact outside_scr hp (.inl (by decide))
    · exact outside_work hp
    · exact outside_call hp
  refine ⟨h₅.frame hp it f ho, fun d hd => by rw [lw_outside hp f ho hd, lw_mem m₅], ?_⟩
  rw [post, ax, sx, cell_addr hp cl, cell_addr hp hR, m₅]

end


section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `fillWrite`: G's output to the current block, XORed into it after the first pass. -/
theorem fillWrite_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hpass : pass < 2 ^ 32) {C : Nat} (hC : C < blocksN s₀)
    (hcur : lw s₀ s curOff = memP s₀ + BitVec.ofNat 32 (C * 1024)) :
    WP isa Impl.Argon2.X86.Derive.fillWrite s fun t => Inv s₀ t ∧
      Frame [⟨matrixCell (memB s₀) C, 1024⟩] s.mem t.mem ∧
      blockAt t.mem (matrixCell (memB s₀) C) = if pass = 0 then blk s.mem (scrP s₀) 4096 else
        xorBlock (blk s.mem (scrP s₀) 4096) (blockAt s.mem (matrixCell (memB s₀) C)) := by
  unfold Impl.Argon2.X86.Derive.fillWrite
  refine WP.seq (wp_ldarg hp h.inv (i := 15) (by decide) fun s₁ u₁ => ?_)
  have h₁ := h.of_upd u₁ (by decide) (by decide)
  refine wp_addi fun s₂ u₂ => ?_
  have h₂ := h₁.of_upd u₂ (by decide) (by decide)
  refine wp_ldloc hp h₂.inv (d := curOff) (by decide) fun s₃ u₃ => ?_
  have h₃ := h₂.of_upd u₃ (by decide) (by decide)
  refine wp_ldloc hp h₃.inv (d := passOff) (by decide) fun s₄ u₄ => wp_cmpi fun s₅ f₅ _ z₅ => WP.block_nil ?_
  have h₅ := (h₃.of_upd u₄ (by decide) (by decide)).of_keep (Divide.Keep.of_fupd f₅)
  have m₅ : s₅.mem = s.mem := by rw [f₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have si : s₅.gpr .esi = scrP s₀ + BitVec.ofNat 32 4096 := by
    rw [f₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr]; rfl
  have di : s₅.gpr .edi = memP s₀ + BitVec.ofNat 32 (C * 1024) := by
    rw [f₅.gpr, u₄.other _ (by decide), u₃.gpr, lw_mem u₂.mem, lw_mem u₁.mem, hcur]
  have z : ∀ y : BitVec 32, y - 0 = y := fun y => by simp
  have hsf := hp.scr_fits
  have eP : (scrP s₀ + BitVec.ofNat 32 4096).setWidth 64 = scrB s₀ + BitVec.ofNat 64 4096 :=
    HPrime.setWidth_add (by omega)
  have Pfit : (scrP s₀ + BitVec.ofNat 32 4096).toNat + 1024 ≤ 2 ^ 32 := by rw [add_nat (by omega)]; omega
  have Pw : ∃ R ∈ [scrR s₀, memR s₀], ∃ off, (scrP s₀ + BitVec.ofNat 32 4096).setWidth 64 =
      R.base + BitVec.ofNat 64 off ∧ off + 1024 ≤ R.len := ⟨scrR s₀, by simp, 4096, eP, by show 4096 + 1024 ≤ 16384; decide⟩
  have PC : Region.Disjoint ⟨(scrP s₀ + BitVec.ofNat 32 4096).setWidth 64, 1024⟩ ⟨matrixCell (memB s₀) C, 1024⟩ := by
    rw [eP]
    exact (hp.mem_scr.symm.sub_left (Offset.sub_base _ (by decide))).sub_right (cell_in_mem hC)
  have nxt : blk s.mem (scrP s₀) 4096 = ofWords fun i => sw s₀ s.mem (4096 + 4 * i) :=
    blk_of_words fun _ _ => rfl
  have old : blockAt s.mem (matrixCell (memB s₀) C) = ofWords fun i => mw s₀ s.mem (C * 1024 + 4 * i) := by
    rw [cell_blk hp _ hC]; exact blk_of_words fun _ _ => rfl
  have done : ∀ (xo : Bool) (t : State), (∀ i < 256, mw s₀ t.mem (C * 1024 + 4 * i) = if i < 256 then
        (if xo then s₅.mem.readW (addr (scrP s₀ + BitVec.ofNat 32 4096) (4 * i)) 32 ^^^ mw s₀ s₅.mem (C * 1024 + 4 * i)
          else s₅.mem.readW (addr (scrP s₀ + BitVec.ofNat 32 4096) (4 * i)) 32)
        else mw s₀ s₅.mem (C * 1024 + 4 * i)) →
      blockAt t.mem (matrixCell (memB s₀) C) = if xo then
        xorBlock (blk s.mem (scrP s₀) 4096) (blockAt s.mem (matrixCell (memB s₀) C)) else blk s.mem (scrP s₀) 4096 :=
    fun xo t wt => by
      have e : blockAt t.mem (matrixCell (memB s₀) C) = ofWords fun i => if xo then
          sw s₀ s.mem (4096 + 4 * i) ^^^ mw s₀ s.mem (C * 1024 + 4 * i) else sw s₀ s.mem (4096 + 4 * i) := by
        rw [cell_blk hp _ hC]
        exact blk_of_words fun i hi => by rw [← mw, wt i hi, ite_eq_left hi, m₅, addr_shift]
      rw [e, nxt, old]
      cases xo
      · rfl
      · simp only [ite_true]; rw [xor_words]
  refine WP.ite (decide (pass = 0)) (by
    show s₅.zf = _
    rw [z₅, u₄.gpr, lw_mem u₃.mem, lw_mem u₂.mem, lw_mem u₁.mem, h.pos.pass, z, Wp.ofNat_beq_zero hpass])
    (fun hb => ?_) fun hb => ?_
  · refine ((writeWords_ok hp h₅.inv hC false si Pfit Pw PC di 256 (Nat.le_refl _)).mono fun t ⟨it, _, ft, wt⟩ =>
      ⟨it, by rw [← m₅]; exact ft, ?_⟩)
    rw [done false t wt, ite_eq_left (of_decide_eq_true hb)]; rfl
  · refine ((writeWords_ok hp h₅.inv hC true si Pfit Pw PC di 256 (Nat.le_refl _)).mono fun t ⟨it, _, ft, wt⟩ =>
      ⟨it, by rw [← m₅]; exact ft, ?_⟩)
    rw [done true t wt, ite_eq_right (of_decide_eq_false hb)]; rfl

end

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `fillBlock`: one block of the filling loops. -/
theorem fillBlock_ok {s : State} {pass slice lane index ctr : Nat} {st : FillState}
    (h : FS s₀ pass slice lane index ctr st s) (hpass : pass < 2 ^ 32) (hl : lane < lanesN s₀) (hs : slice < 4)
    (hi : index < (prm s₀).segmentLen) (active : pass ≠ 0 ∨ slice ≠ 0 ∨ 2 ≤ index) :
    WP isa Impl.Argon2.X86.Derive.fillBlock s fun t =>
      FS s₀ pass slice lane index (ctrNext (prm s₀) pass slice index ctr)
        (Spec.Argon2.fillBlock (prm s₀) pass slice lane index st) t := by
  have hb : blocksN s₀ = (prm s₀).blocks := hp.blocks
  unfold Impl.Argon2.X86.Derive.fillBlock
  refine WP.seq ((randomSource_ok hp h hpass hl hs hi).mono fun t₁ ⟨h₁, w₁⟩ => ?_)
  refine WP.seq ((reference_ok hp ⟨h₁, rfl, rfl⟩ hpass hl hs hi active).mono fun t₂ ⟨h₂, tmp₂, cur₂⟩ => ?_)
  rw [w₁] at tmp₂
  have refLt := Proof.Argon2.reference_cell_lt (prm s₀) hp.lanes_pos hp.memory_ge pass lane slice index
    (Proof.Argon2.FillStep.random (prm s₀) pass lane slice index st.memory) hl
  have curLt := Proof.Argon2.current_cell_lt (prm s₀) hp.lanes_pos hl hs hi
  have prevLt := Proof.Argon2.previous_cell_lt (prm s₀) hp.lanes_pos hp.memory_ge
    (column := slice * (prm s₀).segmentLen + index) hl
  simp only at refLt
  refine WP.seq ((fillCompress_ok hp h₂.fs hl hs hi (by rw [hb]; exact refLt) tmp₂).mono
    fun t₃ ⟨h₃, l₃, c₃⟩ => ?_)
  refine (fillWrite_ok hp h₃ hpass (C := lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index))
    (by rw [hb]; exact curLt) (by rw [l₃ _ (by decide)]; exact cur₂)).mono
    fun t ⟨it, ft, bt⟩ => ?_
  have kept : ∀ j < (prm s₀).blocks, j ≠ lane * (prm s₀).laneLen + (slice * (prm s₀).segmentLen + index) →
      blockAt t.mem (matrixCell (memB s₀) j) = blockAt t₃.mem (matrixCell (memB s₀) j) := fun j hj ne =>
    blockAt_keep ft fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact cell_other hp (by rw [hb]; exact hj) (by rw [hb]; exact curLt) ne
  have lt : ∀ d, d + 4 ≤ 144 → lw s₀ t d = lw s₀ t₃ d := fun d hd =>
    ft.readW (r := ⟨addr (E s₀) d, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (loc_disj hp hd (memR s₀) (by simp)).sub_right (cell_in_mem (by rw [hb]; exact curLt))) (by decide)
  refine ⟨it, Prm.of_lw h₃.pr fun d hd => lt d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide),
    h₃.pos.of_lw fun d hd => lt d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide),
    ?_, ?_⟩
  · obtain ⟨c0, c1, c2 | ⟨c3, c4⟩⟩ := h₃.cache
    · exact ⟨c0, by rw [lt _ (by decide)]; exact c1, .inl c2⟩
    · refine ⟨c0, by rw [lt _ (by decide)]; exact c1, .inr ⟨c3, ?_⟩⟩
      rw [scr_blk hp _ (by decide), blockAt_keep ft (fun r hr => ?_), ← scr_blk hp _ (by decide), c4]
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.mem_scr.symm.sub_left (Offset.sub_base _ (by decide))).sub_right
        (cell_in_mem (by rw [hb]; exact curLt))
  · rw [Proof.Argon2.FillStep.memory _ _ _ _ _ _ active]
    simp only [Proof.Argon2.FillStep.update]
    refine Represents.update h₃.mem _ curLt _ ?_ kept
    rw [bt, c₃, h₂.fs.mem.block _ prevLt, h₂.fs.mem.block _ refLt, h₃.mem.block _ curLt]

end
end VG.Proof.Argon2.X86.Derive

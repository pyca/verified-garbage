import VerifiedGarbage.Proof.AesOcb.X86_64.Hash

/-!
# AES-OCB on x86-64: a pass over the whole blocks (`pass`)

Untrusted: everything here is checked by Lean. `pass body` goes over the
`m` whole blocks of the data at `D`, with the offset and the checksum in
`xmm0` and `xmm1` (`XInv`, OCB's blocks `rv` of the registers): for block
`i` it computes `Offset_{i+1}` (`OfsOk`: from `L_0` in `xmm4` or `L_1` in
`xmm5`, `ofsX_ok`, or from the table, `nextOffset_ok`), loads the block to
`xmm3`, runs `body` on it, which replaces it with `fB` of it and the
offset, and the checksum with `fC` of them (`BodyOk`: `[xorOfs]`,
`[addCk, xorOfs]`, `[xorOfs, addCk]`), and stores it back
(`blockStep_ok`). Four blocks at a time (`quad_ok`, the first three with
`ntz` 0, 1 and 0), then one at a time (`single_ok`); `pass_ok` gives the
blocks, the offset and the checksum in `W` after all `m`.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt)
open VG.Proof.AesCcm.X86_64 (runBlock_append toNat_ofNat_of_lt imm_eq eval_e eval_ne eval_b in_left)

theorem xmm_setXmm (s : State) (r : XReg) (v : BitVec 128) (r' : XReg) :
    (s.setXmm r v).xmm r' = if r' = r then v else s.xmm r' := rfl

theorem eval_ae {s : State} {b : Bool} (h : s.cf = some b) : isa.eval .ae s = some !b := by
  show s.cf.map (!·) = _; rw [h]; rfl

/-- What a body does to the block in `xmm3` and the checksum in `xmm1`, with
the offset in `xmm0`: nothing else. -/
def BodyOk (body : List Instr) (fB : Block → Block → Block) (fC : Block → Block → Block → Block) : Prop :=
  ∀ t : State, ∃ t', runBlock isa body t = some t' ∧
    rv (t'.xmm .xmm3) = fB (rv (t.xmm .xmm3)) (rv (t.xmm .xmm0)) ∧
    rv (t'.xmm .xmm1) = fC (rv (t.xmm .xmm1)) (rv (t.xmm .xmm3)) (rv (t.xmm .xmm0)) ∧
    (∀ x, x ≠ .xmm1 → x ≠ .xmm3 → t'.xmm x = t.xmm x) ∧ t'.gpr = t.gpr ∧ t'.mem = t.mem ∧ t'.rd = t.rd ∧
    t'.wr = t.wr

theorem xorOfs_ok : BodyOk [xorOfs] (fun b o => b ^^^ o) (fun c _ _ => c) := fun t => by
  refine ⟨_, by orun [xorOfs, XOp.exec, XBinOp.eval], ?_, ?_, fun x h1 h3 => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [xmm_setXmm, ite_true, rv_xor]
  · simp only [xmm_setXmm, reduceCtorEq, ite_false]
  · simp only [xmm_setXmm, h3, ite_false]
  all_goals rfl

/-- `seal`'s first pass: the checksum of the block, then the block XORed with the offset. -/
theorem sealPre_ok : BodyOk [addCk, xorOfs] (fun b o => b ^^^ o) (fun c b _ => c ^^^ b) := fun t => by
  refine ⟨_, by orun [addCk, xorOfs, XOp.exec, XBinOp.eval], ?_, ?_, fun x h1 h3 => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [xmm_setXmm, ite_true, reduceCtorEq, ite_false, rv_xor]
  · simp only [xmm_setXmm, reduceCtorEq, ite_true, ite_false, rv_xor]
  · simp only [xmm_setXmm, h1, h3, ite_false]
  all_goals rfl

/-- `open`'s third pass: the block XORed with the offset, then its checksum. -/
theorem openPost_ok : BodyOk [xorOfs, addCk] (fun b o => b ^^^ o) (fun c b o => c ^^^ (b ^^^ o)) := fun t => by
  refine ⟨_, by orun [addCk, xorOfs, XOp.exec, XBinOp.eval], ?_, ?_, fun x h1 h3 => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [xmm_setXmm, ite_true, reduceCtorEq, ite_false, rv_xor]
  · simp only [xmm_setXmm, reduceCtorEq, ite_true, ite_false, rv_xor]
  · simp only [xmm_setXmm, h1, h3, ite_false]
  all_goals rfl

/-- What the code `ofs` does to the offset in `xmm0`, for block `i + 1`:
`⊕ L_{ntz(i+1)}`, using `xmm2`, `rax`, `rcx` and `rdx` at most. -/
def OfsOk (ofs : List Instr) (l : Block) (i : Nat) (t : State) : Prop :=
  ∃ u, runBlock isa ofs t = some u ∧ rv (u.xmm .xmm0) = rv (t.xmm .xmm0) ^^^ lAt l (ntz (i + 1)) ∧
    (∀ x, x ≠ .xmm0 → x ≠ .xmm2 → u.xmm x = t.xmm x) ∧
    (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → u.gpr r = t.gpr r) ∧ u.mem = t.mem ∧ u.rd = t.rd ∧ u.wr = t.wr

/-- `L_{ntz(i+1)}` in the register `x`. -/
theorem ofsX_ok {l : Block} {i : Nat} {t : State} (x : XReg)
    (h : rv (t.xmm x) = lAt l (ntz (i + 1))) : OfsOk (ofsX x) l i t := by
  refine ⟨_, by orun [ofsX, XOp.exec, XBinOp.eval], ?_, fun y h0 _ => ?_, fun _ _ _ _ => ?_, ?_, ?_, ?_⟩
  · simp only [xmm_setXmm, ite_true, rv_xor, h]
  · simp only [xmm_setXmm, h0, ite_false]
  all_goals rfl

/-- `L_{ntz(i+1)}` from the table. -/
theorem nextOffset_ok {K W SP : Addr} {t : State} (E : Env K W SP t) {l : Block} {M i : Nat}
    (T : Tbl W l M t.mem) (hi : i + 1 ≤ M) (hbp : t.gpr .rbp = BitVec.ofNat 64 (i + 1)) :
    OfsOk nextOffset l i t := by
  have hM := T.lt
  obtain ⟨u, run, h1, g, m, x, rd, wr⟩ := lAddr_ok E.r15 (i := i + 1) (by omega) (by omega) hbp
  have hs := slot_lt (ntz (i + 1))
  have ea : u.gpr .rcx + BitVec.ofNat 64 2560 = W + BitVec.ofNat 64 (2560 + 16 * slot (ntz (i + 1))) := by
    rw [h1]; exact slot_addr W _
  have rT : InRegions (u.rd ++ u.wr) (W + BitVec.ofNat 64 (2560 + 16 * slot (ntz (i + 1)))) 16 := by
    rw [rd, wr]; exact E.perm.wR (by omega)
  refine ⟨_, by rw [nextOffset, runBlock_append, run, Option.bind_some]
                orun [XOp.exec, XBinOp.eval, State.load128, ea, rT], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e := T.ntz (by omega) hi
    simp only [tblO] at e
    simp only [xmm_setXmm, ite_true, reduceCtorEq, ite_false, rv_xor, x, ← blockAtMem_eq, m, e]
  · intro y h0 h2; simp only [xmm_setXmm, h0, h2, ite_false, x]
  · intro r h₁ h₂ h₃; simp only [gpr_setXmm, g r h₁ h₂ h₃]
  · simp only [mem_setXmm, m]
  · simp only [rd_setXmm, rd]
  · simp only [wr_setXmm, wr]

/-- A pass over the `m` whole blocks at `D` (`X k` at its start, `t₀`), after
`i` of them, the offset and the checksum in `xmm0` and `xmm1`. -/
structure XInv (K W SP D : Addr) (m : Nat) (O0 l : Block) (X : Nat → Block) (fB : Block → Block → Block)
    (ckF : Nat → Block) (t₀ t : State) (i : Nat) : Prop where
  env : Env K W SP t
  frame : Frame [⟨D, 16 * m⟩] t₀.mem t.mem
  rd : t.rd = t₀.rd
  wr : t.wr = t₀.wr
  rbx : t.gpr .rbx = D + BitVec.ofNat 64 (16 * i)
  rbp : t.gpr .rbp = BitVec.ofNat 64 (i + 1)
  ofs : rv (t.xmm .xmm0) = offAt O0 l i
  ck : rv (t.xmm .xmm1) = ckF i
  blk : ∀ k < m, blockAtMem t.mem (D + BitVec.ofNat 64 (16 * k)) =
    if k < i then fB (X k) (offAt O0 l (k + 1)) else X k
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → t.gpr r = t₀.gpr r

/-- One block, `i + 1`: its offset (`ofs`), the block through `body`. -/
theorem blockStep_ok {K W SP D : Addr} {m : Nat} {O0 l : Block} {X : Nat → Block} {fB : Block → Block → Block}
    {fC : Block → Block → Block → Block} {ckF : Nat → Block} {body ofs : List Instr} (hB : BodyOk body fB fC)
    (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    {t₀ : State} (hD : DBuf K W SP t₀ D (16 * m)) {t : State} {i : Nat} (hi : i < m)
    (P : XInv K W SP D m O0 l X fB ckF t₀ t i) (hofs : OfsOk ofs l i t) :
    ∃ t', runBlock isa (blockStep ofs body) t = some t' ∧ XInv K W SP D m O0 l X fB ckF t₀ t' (i + 1) ∧
      t'.gpr .r12 = t.gpr .r12 ∧ (∀ x, x ≠ .xmm0 → x ≠ .xmm1 → x ≠ .xmm2 → x ≠ .xmm3 → t'.xmm x = t.xmm x) := by
  have hDt : DBuf K W SP t D (16 * m) := hD.of_eq P.rd P.wr
  have hBi := hDt.slice (a := 16 * i) (k := 16) (by omega)
  generalize hB' : D + BitVec.ofNat 64 (16 * i) = B at hBi
  obtain ⟨u₁, run₁, o₁, x₁, g₁, m₁, rd₁, wr₁⟩ := hofs
  have hbx₁ : u₁.gpr .rbx = B := by rw [g₁ _ (by decide) (by decide) (by decide), P.rbx, hB']
  have rB : InRegions (u₁.rd ++ u₁.wr) B 16 := by
    rw [rd₁, wr₁]
    exact hBi.rd _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  -- the load
  have run₂ : runBlock isa [.movdquLoad .xmm3 (at_ .rbx 0)] u₁ = some (u₁.setXmm .xmm3 (u₁.mem.readW B 128)) := by
    orun [State.load128, hbx₁, rB, BitVec.add_zero]
  -- the body
  obtain ⟨u₃, run₃, b₃, c₃, x₃, g₃, m₃, rd₃, wr₃⟩ := hB (u₁.setXmm .xmm3 (u₁.mem.readW B 128))
  have hbx₃ : u₃.gpr .rbx = B := by rw [g₃, gpr_setXmm, hbx₁]
  have hbp₃ : u₃.gpr .rbp = BitVec.ofNat 64 (i + 1) := by
    rw [g₃, gpr_setXmm, g₁ _ (by decide) (by decide) (by decide), P.rbp]
  have wB : InRegions u₃.wr B 16 := by
    rw [wr₃, wr_setXmm, wr₁]
    exact hBi.wr _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  -- the store and the next block
  obtain ⟨u₄, run₄, m₄, bx₄, bp₄, g₄, x₄, rd₄, wr₄⟩ : ∃ u₄, runBlock isa
      ([.movdquStore (at_ .rbx 0) .xmm3] ++ nextBlock) u₃ = some u₄ ∧
      u₄.mem = u₃.mem.writeW B (u₃.xmm .xmm3) ∧ u₄.gpr .rbx = D + BitVec.ofNat 64 (16 * (i + 1)) ∧
      u₄.gpr .rbp = BitVec.ofNat 64 (i + 1 + 1) ∧ (∀ r, r ≠ .rbx → r ≠ .rbp → u₄.gpr r = u₃.gpr r) ∧
      u₄.xmm = u₃.xmm ∧ u₄.rd = u₃.rd ∧ u₄.wr = u₃.wr := by
    refine ⟨_, by orun [nextBlock, State.store128, hbx₃, hbp₃, wB, BitVec.add_zero], ?_, ?_, ?_, fun r h1 h2 => ?_,
      ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_arithFlags, BitVec.add_zero]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbx₃, ← hB', Offset.add_add]
      rw [show 16 * i + 16 = 16 * (i + 1) by omega]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbp₃, ← BitVec.ofNat_add]
    · simp only [gpr_setReg, gpr_arithFlags, h1, h2, ite_false]
    all_goals rfl
  refine ⟨u₄, by rw [blockStep, runBlock_append, runBlock_append, runBlock_append, runBlock_append, run₁,
    Option.bind_some, run₂,
    Option.bind_some, run₃, Option.bind_some, ← runBlock_append, run₄], ?_, ?_, fun x h0 h1 h2 h3 => ?_⟩
  rotate_left
  · rw [g₄ _ (by decide) (by decide), g₃, gpr_setXmm, g₁ _ (by decide) (by decide) (by decide)]
  · rw [x₄, x₃ x h1 h3]; simp only [xmm_setXmm, h3, ite_false]; exact x₁ x h0 h2
  have hBX : blockAtMem t.mem B = X i := by rw [← hB', P.blk i hi]; simp
  have e3 : rv (u₃.xmm .xmm3) = fB (X i) (offAt O0 l (i + 1)) := by
    rw [b₃]; simp only [xmm_setXmm, ite_true, reduceCtorEq, ite_false]
    rw [← blockAtMem_eq, o₁, P.ofs, m₁, hBX]; rfl
  have fB4 : Frame [⟨B, 16⟩] t.mem u₄.mem := by
    rw [m₄, m₃, mem_setXmm, ← m₁]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨?_, ?_, ?_, ?_, ?_, bp₄, ?_, ?_, fun k hk => ?_, fun r h1 h2 h3 h4 h5 h6 => ?_⟩
  · exact P.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        rw [g₄ _ (by decide) (by decide), g₃, gpr_setXmm, g₁ _ (by decide) (by decide) (by decide)])
      (by rw [rd₄, rd₃, rd_setXmm, rd₁]) (by rw [wr₄, wr₃, wr_setXmm, wr₁])
  · exact P.frame.trans (fB4.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨D, 16 * m⟩, List.mem_singleton_self _, by rw [← hB']; exact Offset.sub_base D (by omega)⟩)
  · rw [rd₄, rd₃, rd_setXmm, rd₁, P.rd]
  · rw [wr₄, wr₃, wr_setXmm, wr₁, P.wr]
  · exact bx₄
  · rw [x₄, x₃ .xmm0 (by decide) (by decide)]; simp only [xmm_setXmm, reduceCtorEq, ite_false]
    rw [o₁, P.ofs]; rfl
  · rw [x₄, c₃]; simp only [xmm_setXmm, ite_true, reduceCtorEq, ite_false]
    rw [x₁ .xmm1 (by decide) (by decide), P.ck, ← blockAtMem_eq, m₁, hBX, o₁, P.ofs, hckF i hi]; rfl
  · by_cases hki : k = i
    · subst hki
      rw [hB', m₄, blockAtMem_writeW, e3]; simp
    · have hBk := hDt.slice (a := 16 * k) (k := 16) (by omega)
      rw [blockAtMem_frame fB4 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [← hB']
        exact Offset.disjoint D (by omega) (by have := hD.wrap; omega) (by have := hD.wrap; omega)), P.blk k hk]
      by_cases hk' : k < i
      · simp [hk', show k < i + 1 by omega]
      · simp [hk', show ¬ k < i + 1 by omega]
  · rw [g₄ r h4 h5, g₃, gpr_setXmm, g₁ r h1 h3 h2, P.gpr r h1 h2 h3 h4 h5 h6]

theorem ntz_4k1 (k : Nat) : ntz (4 * k + 1) = 0 := Proof.Ocb.ntz_odd (by omega)
theorem ntz_4k3 (k : Nat) : ntz (4 * k + 3) = 0 := Proof.Ocb.ntz_odd (by omega)
theorem ntz_4k2 (k : Nat) : ntz (4 * k + 2) = 1 := by
  rw [Proof.Ocb.ntz_even (by omega) (by omega), show (4 * k + 2) / 2 = 2 * k + 1 by omega,
    Proof.Ocb.ntz_odd (by omega)]

/-- What the pass needs throughout: the table (for `M ≥ m`), and the block
counter. -/
structure PCtx (K W SP D : Addr) (m : Nat) (l : Block) (t₀ : State) : Prop where
  lay : Lay K W SP
  data : DBuf K W SP t₀ D (16 * m)
  tbl : ∃ M, Tbl W l M t₀.mem ∧ m ≤ M

theorem PCtx.tbl' {K W SP D : Addr} {m : Nat} {l : Block} {t₀ : State} (C : PCtx K W SP D m l t₀) {t : State}
    (h : Frame [⟨D, 16 * m⟩] t₀.mem t.mem) : ∃ M, Tbl W l M t.mem ∧ m ≤ M := by
  obtain ⟨M, T, hM⟩ := C.tbl
  exact ⟨M, T.frame h fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact C.data.w.symm.sub_left (Lay.wSub (by decide)), hM⟩

/-- Four blocks, `4k + 1` to `4k + 4`, with `L_0` and `L_1` in `xmm4` and `xmm5`. -/
theorem quad_ok {K W SP D : Addr} {m : Nat} {O0 l : Block} {X : Nat → Block} {fB : Block → Block → Block}
    {fC : Block → Block → Block → Block} {ckF : Nat → Block} {body : List Instr} (hB : BodyOk body fB fC)
    (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    {t₀ : State} (C : PCtx K W SP D m l t₀) {t : State} {k : Nat} (hk : 4 * k + 4 ≤ m)
    (P : XInv K W SP D m O0 l X fB ckF t₀ t (4 * k)) (h12 : t.gpr .r12 = BitVec.ofNat 64 (m - 4 * k))
    (h4 : rv (t.xmm .xmm4) = lAt l 0) (h5 : rv (t.xmm .xmm5) = lAt l 1) :
    ∃ t', runBlock isa (quad body) t = some t' ∧ XInv K W SP D m O0 l X fB ckF t₀ t' (4 * (k + 1)) ∧
      t'.gpr .r12 = BitVec.ofNat 64 (m - 4 * (k + 1)) ∧ t'.cf = some (decide (m - 4 * (k + 1) < 4)) ∧
      rv (t'.xmm .xmm4) = lAt l 0 ∧ rv (t'.xmm .xmm5) = lAt l 1 := by
  obtain ⟨t₁, run₁, P₁, r₁, x₁⟩ := blockStep_ok hB hckF C.data (by omega) P
    (ofsX_ok .xmm4 (by rw [h4, ntz_4k1]))
  obtain ⟨t₂, run₂, P₂, r₂, x₂⟩ := blockStep_ok hB hckF C.data (by omega) P₁
    (ofsX_ok .xmm5 (by rw [x₁ .xmm5 (by decide) (by decide) (by decide) (by decide), h5,
      show 4 * k + 1 + 1 = 4 * k + 2 by omega, ntz_4k2]))
  obtain ⟨t₃, run₃, P₃, r₃, x₃⟩ := blockStep_ok hB hckF C.data (by omega) P₂
    (ofsX_ok .xmm4 (by rw [x₂ .xmm4 (by decide) (by decide) (by decide) (by decide),
      x₁ .xmm4 (by decide) (by decide) (by decide) (by decide), h4, show 4 * k + 1 + 1 + 1 = 4 * k + 3 by omega,
      ntz_4k3]))
  obtain ⟨M, T, hM⟩ := C.tbl' P₃.frame
  obtain ⟨t₄, run₄, P₄, r₄, x₄⟩ := blockStep_ok hB hckF C.data (by omega) P₃
    (nextOffset_ok P₃.env T (by omega) P₃.rbp)
  have h12₄ : t₄.gpr .r12 = BitVec.ofNat 64 (m - 4 * k) := by rw [r₄, r₃, r₂, r₁, h12]
  obtain ⟨t₅, run₅, h12₅, cf₅, g₅, m₅, x₅, rd₅, wr₅⟩ : ∃ t₅, runBlock isa
      [.alu .sub .r12 (.imm 4), .alu .cmp .r12 (.imm 4)] t₄ = some t₅ ∧
      t₅.gpr .r12 = BitVec.ofNat 64 (m - 4 * (k + 1)) ∧ t₅.cf = some (decide (m - 4 * (k + 1) < 4)) ∧
      (∀ r, r ≠ .r12 → t₅.gpr r = t₄.gpr r) ∧ t₅.mem = t₄.mem ∧ t₅.xmm = t₄.xmm ∧ t₅.rd = t₄.rd ∧
      t₅.wr = t₄.wr := by
    have e4 : BitVec.signExtend 64 (4 : BitVec 32) = BitVec.ofNat 64 4 := by decide
    have hs : BitVec.ofNat 64 (m - 4 * k) - BitVec.ofNat 64 4 = BitVec.ofNat 64 (m - 4 * (k + 1)) := by
      rw [Proof.AesCcm.X86_64.ofNat_sub (by omega) (by have := C.data.lt; omega),
        show m - 4 * k - 4 = m - 4 * (k + 1) by omega]
    refine ⟨_, by orun [h12₄], ?_, ?_, fun r h => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, h12₄, e4, hs]
    · simp only [cf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, h12₄, e4, hs]
      rw [toNat_ofNat_of_lt (by have := C.data.lt; omega), toNat_ofNat_of_lt (by decide)]
    · simp only [gpr_setReg, gpr_arithFlags, h, ite_false]
    all_goals rfl
  refine ⟨t₅, ?_, ?_, h12₅, cf₅, ?_, ?_⟩
  · rw [quad, runBlock_append, runBlock_append, runBlock_append, runBlock_append, run₁, Option.bind_some, run₂,
      Option.bind_some, run₃, Option.bind_some, run₄, Option.bind_some, run₅]
  · rw [show 4 * (k + 1) = 4 * k + 1 + 1 + 1 + 1 by omega]
    exact { P₄ with
      env := P₄.env.keep (fun r hr => g₅ r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl <;> decide))
        rd₅ wr₅
      frame := by rw [m₅]; exact P₄.frame
      rd := by rw [rd₅, P₄.rd]
      wr := by rw [wr₅, P₄.wr]
      rbx := by rw [g₅ _ (by decide), P₄.rbx]
      rbp := by rw [g₅ _ (by decide), P₄.rbp]
      ofs := by rw [x₅, P₄.ofs]
      ck := by rw [x₅, P₄.ck]
      blk := by rw [m₅]; exact P₄.blk
      gpr := fun r h1 h2 h3 h4 h5 h6 => by rw [g₅ r h6, P₄.gpr r h1 h2 h3 h4 h5 h6] }
  · rw [x₅, x₄ .xmm4 (by decide) (by decide) (by decide) (by decide),
      x₃ .xmm4 (by decide) (by decide) (by decide) (by decide), x₂ .xmm4 (by decide) (by decide) (by decide) (by decide),
      x₁ .xmm4 (by decide) (by decide) (by decide) (by decide), h4]
  · rw [x₅, x₄ .xmm5 (by decide) (by decide) (by decide) (by decide),
      x₃ .xmm5 (by decide) (by decide) (by decide) (by decide), x₂ .xmm5 (by decide) (by decide) (by decide) (by decide),
      x₁ .xmm5 (by decide) (by decide) (by decide) (by decide), h5]

/-- One block, `i + 1`, from the table. -/
theorem single_ok {K W SP D : Addr} {m : Nat} {O0 l : Block} {X : Nat → Block} {fB : Block → Block → Block}
    {fC : Block → Block → Block → Block} {ckF : Nat → Block} {body : List Instr} (hB : BodyOk body fB fC)
    (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (X i) (offAt O0 l (i + 1)))
    {t₀ : State} (C : PCtx K W SP D m l t₀) {t : State} {i : Nat} (hi : i < m)
    (P : XInv K W SP D m O0 l X fB ckF t₀ t i) (h12 : t.gpr .r12 = BitVec.ofNat 64 (m - i)) :
    ∃ t', runBlock isa (blockStep nextOffset body ++ ([.alu .sub .r12 (.imm 1)] : List Instr)) t = some t' ∧
      XInv K W SP D m O0 l X fB ckF t₀ t' (i + 1) ∧ t'.gpr .r12 = BitVec.ofNat 64 (m - (i + 1)) ∧
      t'.zf = some (decide (m - (i + 1) = 0)) := by
  obtain ⟨M, T, hM⟩ := C.tbl' P.frame
  obtain ⟨t₁, run₁, P₁, r₁, -⟩ := blockStep_ok hB hckF C.data hi P (nextOffset_ok P.env T (by omega) P.rbp)
  have h12₁ : t₁.gpr .r12 = BitVec.ofNat 64 (m - i) := by rw [r₁, h12]
  have hm := C.data.lt
  refine ⟨_, by rw [runBlock_append, run₁, Option.bind_some]; orun [h12₁], ?_, ?_, ?_⟩
  · exact { P₁ with
      env := P₁.env.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false]) rfl rfl
      rbx := by simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, P₁.rbx]
      rbp := by simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, P₁.rbp]
      gpr := fun r h1 h2 h3 h4 h5 h6 => by
        simp only [gpr_setReg, gpr_arithFlags, h6, ite_false]; exact P₁.gpr r h1 h2 h3 h4 h5 h6 }
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, h12₁, Proof.AesOcb.X86_64.sext1]
    rw [Proof.AesCcm.X86_64.ofNat_sub (by omega) (by omega), show m - i - 1 = m - (i + 1) by omega]
  · simp only [zf_setReg, zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, h12₁, Proof.AesOcb.X86_64.sext1]
    rw [Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
    exact congrArg some (decide_eq_decide.mpr (by omega))

/-- What a pass over the `m` whole blocks at `D` leaves, from `t`: the blocks
through `fB` with their offsets, the offset and the checksum in `W`. -/
structure PassPost (K W SP D : Addr) (m : Nat) (O0 l : Block) (fB : Block → Block → Block) (ckF : Nat → Block)
    (t t' : State) : Prop where
  env : Env K W SP t'
  frame : Frame [⟨W + BitVec.ofNat 64 ofsO, 16⟩, ⟨W + BitVec.ofNat 64 ckO, 16⟩, ⟨D, 16 * m⟩] t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  ofs : blockAtMem t'.mem (W + BitVec.ofNat 64 ofsO) = offAt O0 l m
  ck : blockAtMem t'.mem (W + BitVec.ofNat 64 ckO) = ckF m
  blk : ∀ k < m, blockAtMem t'.mem (D + BitVec.ofNat 64 (16 * k)) =
    fB (blockAtMem t.mem (D + BitVec.ofNat 64 (16 * k))) (offAt O0 l (k + 1))
  gpr : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → t'.gpr r = t.gpr r

theorem pass_ok {K W SP D : Addr} {m : Nat} {O0 l : Block} {fB : Block → Block → Block}
    {fC : Block → Block → Block → Block} {ckF : Nat → Block} {body : List Instr} (hB : BodyOk body fB fC)
    {t : State} (hckF : ∀ i < m, ckF (i + 1) = fC (ckF i) (blockAtMem t.mem (D + BitVec.ofNat 64 (16 * i)))
      (offAt O0 l (i + 1)))
    (C : PCtx K W SP D m l t) (E : Env K W SP t) (hm0 : 0 < m)
    (hbx : t.gpr .rbx = D) (hbp : t.gpr .rbp = BitVec.ofNat 64 1) (h12 : t.gpr .r12 = BitVec.ofNat 64 m)
    (hofs : blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) = O0)
    (hck : blockAtMem t.mem (W + BitVec.ofNat 64 ckO) = ckF 0) :
    WP isa (pass body) t (PassPost K W SP D m O0 l fB ckF t) := by
  have L := C.lay
  have hm := C.data.lt
  let X := fun k => blockAtMem t.mem (D + BitVec.ofNat 64 (16 * k))
  obtain ⟨M, T, hM⟩ := C.tbl
  have hM60 := T.lt
  have r₀ : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 16) 16 := E.perm.wR (by decide)
  have r₁ : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 32) 16 := E.perm.wR (by decide)
  have r₂ : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 2560) 16 := E.perm.wR (by decide)
  have r₃ : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 2576) 16 := E.perm.wR (by decide)
  -- the start
  obtain ⟨t₁, run₁, P₁, h12₁, cf₁, x4₁, x5₁⟩ : ∃ t₁, runBlock isa
      [.movdquLoad .xmm0 (at_ .r15 ofsO), .movdquLoad .xmm1 (at_ .r15 ckO), .movdquLoad .xmm4 (at_ .r15 tblO),
        .movdquLoad .xmm5 (at_ .r15 (tblO + 16)), .alu .cmp .r12 (.imm 4)] t = some t₁ ∧
      XInv K W SP D m O0 l X fB ckF t t₁ (4 * 0) ∧ t₁.gpr .r12 = BitVec.ofNat 64 (m - 4 * 0) ∧
      t₁.cf = some (decide (m < 4)) ∧ rv (t₁.xmm .xmm4) = lAt l 0 ∧
      (2 ≤ m → rv (t₁.xmm .xmm5) = lAt l 1) := by
    have e4 : BitVec.signExtend 64 (4 : BitVec 32) = BitVec.ofNat 64 4 := by decide
    refine ⟨_, by orun [State.load128, E.r15, r₀, r₁, r₂, r₃], ?_, ?_, ?_, ?_, fun h2 => ?_⟩
    · exact {
        env := E.keep (fun _ _ => rfl) rfl rfl
        frame := Frame.refl _ _, rd := rfl, wr := rfl
        rbx := by simp only [gpr_arithFlags, gpr_setXmm, hbx]; simp
        rbp := by simp only [gpr_arithFlags, gpr_setXmm, hbp]
        ofs := by
          simp only [xmm_arithFlags, xmm_setXmm, reduceCtorEq, ite_true, ite_false, ← blockAtMem_eq]
          exact hofs
        ck := by
          simp only [xmm_arithFlags, xmm_setXmm, reduceCtorEq, ite_true, ite_false, ← blockAtMem_eq]
          exact hck
        blk := fun k _ => by simp [X, mem_arithFlags, mem_setXmm]
        gpr := fun _ _ _ _ _ _ _ => rfl }
    · simp only [gpr_arithFlags, gpr_setXmm, h12]; simp
    · simp only [cf_arithFlags, gpr_setXmm, h12, e4]
      rw [toNat_ofNat_of_lt (show m < 2 ^ 64 by omega), toNat_ofNat_of_lt (by decide)]
    · simp only [xmm_arithFlags, xmm_setXmm, reduceCtorEq, ite_true, ite_false, ← blockAtMem_eq]
      have := T.val 0 (by simp; omega)
      rwa [slot_zero, Nat.mul_zero, Nat.add_zero] at this
    · simp only [xmm_arithFlags, xmm_setXmm, reduceCtorEq, ite_true, ite_false, ← blockAtMem_eq]
      have := T.val 1 (by simp; omega)
      rwa [slot_one, Nat.mul_one] at this
  have C₁ : PCtx K W SP D m l t := C
  -- four blocks at a time
  have quads : WP isa (.ite .b (.block []) (.loop (.block (quad body)) .ae)) t₁ fun u =>
      XInv K W SP D m O0 l X fB ckF t u (4 * (m / 4)) ∧ u.gpr .r12 = BitVec.ofNat 64 (m - 4 * (m / 4)) := by
    refine WP.ite (decide (m < 4)) (eval_b cf₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
    · have : m / 4 = 0 := by have := of_decide_eq_true hb; omega
      rw [this]; exact ⟨P₁, h12₁⟩
    have h4m : 4 ≤ m := by have := of_decide_eq_false hb; omega
    refine WP.loop (M := isa) (c := .ae)
      (fun (n : Nat) (u : State) => ∃ k, n = m / 4 - k ∧ 4 * k + 4 ≤ m ∧ XInv K W SP D m O0 l X fB ckF t u (4 * k) ∧
        u.gpr .r12 = BitVec.ofNat 64 (m - 4 * k) ∧ rv (u.xmm .xmm4) = lAt l 0 ∧ rv (u.xmm .xmm5) = lAt l 1)
      ?_ (m / 4 - 0) t₁ ⟨0, rfl, by omega, P₁, h12₁, x4₁, x5₁ (by omega)⟩
    rintro n u ⟨k, rfl, hk, P, h12, h4, h5⟩
    obtain ⟨u', run', P', h12', cf', h4', h5'⟩ := quad_ok hB (fun i hi => hckF i hi) C₁ hk P h12 h4 h5
    refine WP.of_runBlock ⟨u', run', ?_⟩
    by_cases he : m - 4 * (k + 1) < 4
    · left
      have : k + 1 = m / 4 := by omega
      exact ⟨(eval_ae cf').trans (by simp [he]), by rw [← this]; exact ⟨P', h12'⟩⟩
    · right
      exact ⟨(eval_ae cf').trans (by simp [he]), m / 4 - (k + 1), by omega, k + 1, rfl, by omega, P', h12', h4', h5'⟩
  unfold pass
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.seq (WP.mono quads fun u ⟨Pu, h12u⟩ => ?_)
  -- the rest, one at a time
  obtain ⟨u₁, run₂, zf₂, g₂, m₂, x₂, rd₂, wr₂⟩ : ∃ u₁, runBlock isa [.alu .test .r12 (.reg .r12)] u = some u₁ ∧
      u₁.zf = some (decide (m - 4 * (m / 4) = 0)) ∧ u₁.gpr = u.gpr ∧ u₁.mem = u.mem ∧ u₁.xmm = u.xmm ∧
      u₁.rd = u.rd ∧ u₁.wr = u.wr := by
    refine ⟨_, by orun [h12u], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [zf_arithFlags, h12u, Proof.AesCcm.X86_64.and_self_beq (show m - 4 * (m / 4) < 2 ^ 64 by omega)]
    all_goals rfl
  have Pu₁ : XInv K W SP D m O0 l X fB ckF t u₁ (4 * (m / 4)) :=
    { Pu with
      env := Pu.env.keep (fun r _ => by rw [g₂]) rd₂ wr₂
      frame := by rw [m₂]; exact Pu.frame
      rd := by rw [rd₂, Pu.rd]
      wr := by rw [wr₂, Pu.wr]
      rbx := by rw [g₂, Pu.rbx]
      rbp := by rw [g₂, Pu.rbp]
      ofs := by rw [x₂, Pu.ofs]
      ck := by rw [x₂, Pu.ck]
      blk := by rw [m₂]; exact Pu.blk
      gpr := fun r h1 h2 h3 h4 h5 h6 => by rw [g₂, Pu.gpr r h1 h2 h3 h4 h5 h6] }
  have singles : WP isa (.ite .e (.block [])
      (.loop (.block (blockStep nextOffset body ++ [.alu .sub .r12 (.imm 1)])) .ne)) u₁ fun u' =>
      XInv K W SP D m O0 l X fB ckF t u' m := by
    refine WP.ite _ (eval_e zf₂) (fun hb => WP.block_nil ?_) (fun hb => ?_)
    · have : 4 * (m / 4) = m := by have := of_decide_eq_true hb; omega
      rw [this] at Pu₁; exact Pu₁
    have hlt : 4 * (m / 4) < m := by have := of_decide_eq_false hb; omega
    refine WP.loop (M := isa) (c := .ne)
      (fun (n : Nat) (u : State) => ∃ i, n = m - i ∧ i < m ∧ XInv K W SP D m O0 l X fB ckF t u i ∧
        u.gpr .r12 = BitVec.ofNat 64 (m - i)) ?_ (m - 4 * (m / 4)) u₁
      ⟨4 * (m / 4), rfl, hlt, Pu₁, by rw [g₂, h12u]⟩
    rintro n u ⟨i, rfl, hi, P, h12⟩
    obtain ⟨u', run', P', h12', zf'⟩ := single_ok hB (fun i hi => hckF i hi) C₁ hi P h12
    refine WP.of_runBlock ⟨u', run', ?_⟩
    by_cases he : m - (i + 1) = 0
    · left
      exact ⟨(eval_ne zf').trans (by simp [he]), (show i + 1 = m by omega) ▸ P'⟩
    · right
      exact ⟨(eval_ne zf').trans (by simp [he]), m - (i + 1), by omega, i + 1, rfl, by omega, P', h12'⟩
  refine WP.seq (WP.of_runBlock ⟨u₁, run₂, ?_⟩)
  refine WP.seq (WP.mono singles fun v P => ?_)
  -- the end
  have w₀ : InRegions v.wr (W + BitVec.ofNat 64 16) 16 := by rw [P.wr]; exact E.perm.wW (by decide)
  have w₁ : InRegions v.wr (W + BitVec.ofNat 64 32) 16 := by rw [P.wr]; exact E.perm.wW (by decide)
  have h15 := P.env.r15
  refine WP.of_runBlock ⟨_, by orun [State.store128, h15, w₀, w₁], ?_⟩
  have dO : (⟨W + BitVec.ofNat 64 16, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 32, 16⟩ :=
    L.w_w (.inl (by decide)) (by decide) (by decide)
  have c16 : ∀ a : Addr, (⟨a, 16⟩ : Region).Contains a (128 / 8) := fun a => Region.contains_self a 16
  have fw2 : ∀ (M : Mem) (x : BitVec 128), Frame [⟨W + BitVec.ofNat 64 32, 16⟩] M
      (M.writeW (W + BitVec.ofNat 64 32) x) := fun M x =>
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c16 _)
  have fw : Frame [⟨W + BitVec.ofNat 64 16, 16⟩, ⟨W + BitVec.ofNat 64 32, 16⟩] v.mem
      ((v.mem.writeW (W + BitVec.ofNat 64 16) (v.xmm .xmm0)).writeW (W + BitVec.ofNat 64 32) (v.xmm .xmm1)) :=
    ((Frame.refl _ _).writeW (List.mem_cons_self ..) _ (c16 _)).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (c16 _)
  refine ⟨P.env.keep (fun _ _ => rfl) rfl rfl, ?_, P.rd, P.wr, ?_, ?_, fun k hk => ?_, P.gpr⟩
  · exact (P.frame.mono (by simp)).trans (fw.mono (by simp [ofsO, ckO]))
  · show blockAtMem ((v.mem.writeW (W + BitVec.ofNat 64 16) (v.xmm .xmm0)).writeW (W + BitVec.ofNat 64 32)
      (v.xmm .xmm1)) (W + BitVec.ofNat 64 16) = _
    rw [blockAtMem_frame (fw2 _ _) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dO),
      blockAtMem_writeW, P.ofs]
  · show blockAtMem ((v.mem.writeW (W + BitVec.ofNat 64 16) (v.xmm .xmm0)).writeW (W + BitVec.ofNat 64 32)
      (v.xmm .xmm1)) (W + BitVec.ofNat 64 32) = _
    rw [blockAtMem_writeW, P.ck]
  · show blockAtMem ((v.mem.writeW (W + BitVec.ofNat 64 16) (v.xmm .xmm0)).writeW (W + BitVec.ofNat 64 32)
      (v.xmm .xmm1)) _ = _
    have hBk := C.data.slice (a := 16 * k) (k := 16) (by omega)
    rw [blockAtMem_frame fw (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hBk.w.sub_right (Lay.wSub (by decide))
        · exact hBk.w.sub_right (Lay.wSub (by decide))), P.blk k hk]
    simp [hk, X]

end VG.Proof.AesOcb.X86_64
